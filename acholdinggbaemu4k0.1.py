import tkinter as tk
from tkinter import filedialog, messagebox, ttk
from PIL import Image, ImageTk
import time
import sys
import array
import struct
import os

# =================================================================
# REAL GBA HARDWARE EMULATOR (ARM7TDMI CORE + HLE BIOS)
# =================================================================

class ARM7TDMI:
    def __init__(self, memory_bus):
        self.bus = memory_bus
        self.r = array.array('I', [0] * 16)      # R0-R12, SP, LR, PC
        self.cpsr = 0x0000001F                   # System mode
        self.spsr = 0x00000000                   # Saved PSR
        self.halted = False
        self.halt_reason = ""
        self.cycles = 0

    def reset(self, skip_bios=True):
        if not skip_bios and getattr(self.bus, 'bios_loaded', False):
            self.r[15] = 0x00000000
            self.cpsr = 0x000000D3                # Supervisor, IRQ/FIQ disabled
        else:
            self.r[13] = 0x03007F00               # SP_svc
            self.r[15] = 0x08000000
            self.cpsr = 0x0000001F                # System mode
        self.halted = False
        self.halt_reason = ""
        self.cycles = 0

    # ---------- Condition Code Evaluation ----------
    def check_cond(self, cond):
        if cond == 0xE: return True               # AL
        n = (self.cpsr >> 31) & 1
        z = (self.cpsr >> 30) & 1
        c = (self.cpsr >> 29) & 1
        v = (self.cpsr >> 28) & 1
        if cond == 0x0: return z == 1             # EQ
        if cond == 0x1: return z == 0             # NE
        if cond == 0x2: return c == 1             # CS/HS
        if cond == 0x3: return c == 0             # CC/LO
        if cond == 0x4: return n == 1             # MI
        if cond == 0x5: return n == 0             # PL
        if cond == 0x6: return v == 1             # VS
        if cond == 0x7: return v == 0             # VC
        if cond == 0x8: return c == 1 and z == 0  # HI
        if cond == 0x9: return c == 0 or z == 1   # LS
        if cond == 0xA: return n == v             # GE
        if cond == 0xB: return n != v             # LT
        if cond == 0xC: return z == 0 and n == v  # GT
        if cond == 0xD: return z == 1 or n != v   # LE
        return False

    # ---------- Flag Setting Helpers ----------
    def set_nz(self, val):
        self.cpsr &= ~0xC0000000
        if val == 0: self.cpsr |= 0x40000000
        if val & 0x80000000: self.cpsr |= 0x80000000

    def set_add_flags(self, a, b, result, carry_in=0):
        self.set_nz(result)
        self.cpsr &= ~0x30000000
        if result < a: self.cpsr |= 0x20000000
        if ((a ^ b) & 0x80000000) == 0 and ((a ^ result) & 0x80000000) != 0:
            self.cpsr |= 0x10000000

    def set_sub_flags(self, a, b, result, carry_in=0):
        self.set_nz(result)
        self.cpsr &= ~0x30000000
        if a >= b: self.cpsr |= 0x20000000
        if ((a ^ b) & 0x80000000) != 0 and ((a ^ result) & 0x80000000) != 0:
            self.cpsr |= 0x10000000

    # ---------- Shifter Operand ----------
    def shift(self, rm, shift_type, amount):
        if shift_type == 0:               # LSL
            if amount == 0: return rm, (self.cpsr >> 29) & 1
            res = (rm << amount) & 0xFFFFFFFF
            carry = (rm >> (32 - amount)) & 1 if amount <= 32 else 0
            return res, carry
        elif shift_type == 1:             # LSR
            if amount == 0: amount = 32
            res = rm >> amount
            carry = (rm >> (amount - 1)) & 1 if amount <= 32 else 0
            return res, carry
        elif shift_type == 2:             # ASR
            if amount == 0: amount = 32
            if rm & 0x80000000:
                res = ((rm >> amount) | (0xFFFFFFFF << (32 - amount))) & 0xFFFFFFFF
            else:
                res = rm >> amount
            carry = (rm >> (amount - 1)) & 1 if amount <= 32 else (rm >> 31) & 1
            return res, carry
        elif shift_type == 3:             # ROR
            if amount == 0:               # RRX
                carry = rm & 1
                res = ((rm >> 1) | ((self.cpsr & 0x20000000) << 2)) & 0xFFFFFFFF
                return res, carry
            amount %= 32
            res = ((rm >> amount) | (rm << (32 - amount))) & 0xFFFFFFFF
            carry = (res >> 31) & 1
            return res, carry
        return rm, 0

    # ---------- Main Execution ----------
    def step(self):
        if self.halted: return
        try:
            if self.cpsr & 0x20:          # Thumb state
                pc = self.r[15] & 0xFFFFFFFE
                instr = self.bus.read16(pc)
                self.r[15] = pc + 2
                self.execute_thumb(instr)
            else:
                pc = self.r[15] & 0xFFFFFFFC
                instr = self.bus.read32(pc)
                self.r[15] = pc + 4
                self.execute_arm(instr)
            self.cycles += 1
            self.bus.update_timers(1)
        except Exception as e:
            self.halted = True
            self.halt_reason = f"Crash at {self.r[15]:08X}: {str(e)}"

    # ---------- ARM Interpreter ----------
    def execute_arm(self, instr):
        cond = (instr >> 28) & 0xF
        if not self.check_cond(cond): return

        # SWI
        if (instr & 0x0F000000) == 0x0F000000:
            self.execute_swi(instr & 0x00FFFFFF)
            return

        # Branch and Branch with Link
        if (instr & 0x0E000000) == 0x0A000000:
            offset = instr & 0x00FFFFFF
            if offset & 0x00800000: offset |= 0xFF000000
            offset = struct.unpack('<i', struct.pack('<I', offset))[0]
            if instr & 0x01000000:          # Link bit
                self.r[14] = self.r[15] - 4
            self.r[15] = (self.r[15] + (offset << 2)) & 0xFFFFFFFF
            return

        # Data Processing
        if (instr & 0x0C000000) == 0x00000000:
            opcode = (instr >> 21) & 0xF
            set_cc = (instr >> 20) & 1
            rn = (instr >> 16) & 0xF
            rd = (instr >> 12) & 0xF
            shifter_op = instr & 0xFFF

            # Second operand
            if instr & 0x02000000:          # Immediate
                imm = instr & 0xFF
                rot = (instr >> 8) & 0xF
                operand = ((imm >> (rot * 2)) | (imm << (32 - rot * 2))) & 0xFFFFFFFF
                carry = self.cpsr & 0x20000000
            else:                           # Register
                rm = self.r[instr & 0xF]
                shift_type = (instr >> 5) & 3
                if instr & 0x10:            # Shift by register
                    rs = self.r[(instr >> 8) & 0xF] & 0xFF
                    operand, carry = self.shift(rm, shift_type, rs)
                else:
                    shift_imm = (instr >> 7) & 0x1F
                    operand, carry = self.shift(rm, shift_type, shift_imm)

            a = self.r[rn]
            b = operand
            res = 0

            # Execute opcode
            if opcode == 0x0: res = a & b          # AND
            elif opcode == 0x1: res = a ^ b        # EOR
            elif opcode == 0x2:                    # SUB
                res = (a - b) & 0xFFFFFFFF
                if set_cc: self.set_sub_flags(a, b, res)
            elif opcode == 0x3:                    # RSB
                res = (b - a) & 0xFFFFFFFF
                if set_cc: self.set_sub_flags(b, a, res)
            elif opcode == 0x4:                    # ADD
                res = (a + b) & 0xFFFFFFFF
                if set_cc: self.set_add_flags(a, b, res)
            elif opcode == 0x5:                    # ADC
                res = (a + b + ((self.cpsr >> 29) & 1)) & 0xFFFFFFFF
                if set_cc: self.set_add_flags(a, b, res, ((self.cpsr>>29)&1))
            elif opcode == 0x6:                    # SBC
                res = (a - b - (1 - ((self.cpsr>>29)&1))) & 0xFFFFFFFF
                if set_cc: self.set_sub_flags(a, b, res)
            elif opcode == 0x7:                    # RSC
                res = (b - a - (1 - ((self.cpsr>>29)&1))) & 0xFFFFFFFF
                if set_cc: self.set_sub_flags(b, a, res)
            elif opcode == 0x8:                    # TST
                self.set_nz(a & b)
            elif opcode == 0x9:                    # TEQ
                self.set_nz(a ^ b)
            elif opcode == 0xA:                    # CMP
                res = (a - b) & 0xFFFFFFFF
                self.set_sub_flags(a, b, res)
            elif opcode == 0xB:                    # CMN
                res = (a + b) & 0xFFFFFFFF
                self.set_add_flags(a, b, res)
            elif opcode == 0xC: res = a | b        # ORR
            elif opcode == 0xD: res = b            # MOV
            elif opcode == 0xE: res = a & ~b       # BIC
            elif opcode == 0xF: res = ~b & 0xFFFFFFFF # MVN

            if opcode not in (0x8,0x9,0xA,0xB):
                self.r[rd] = res
                if set_cc and opcode not in (0xA,0xB):
                    self.set_nz(res)
                    if opcode in (0x4,0x5,0x6,0x7):
                        pass  # flags already set
                    else:
                        self.cpsr = (self.cpsr & ~0x20000000) | (carry << 29)
            return

        # Multiply (MUL, MLA)
        if (instr & 0x0FC000F0) == 0x00000090:
            rd = (instr >> 16) & 0xF
            rn = (instr >> 12) & 0xF
            rs = (instr >> 8) & 0xF
            rm = instr & 0xF
            set_cc = (instr >> 20) & 1
            res = (self.r[rm] * self.r[rs]) & 0xFFFFFFFF
            if (instr >> 21) & 1:           # MLA
                res = (res + self.r[rn]) & 0xFFFFFFFF
            self.r[rd] = res
            if set_cc:
                self.set_nz(res)
            return

        # Load/Store (LDR/STR, LDRB/STRB)
        if (instr & 0x0C000000) == 0x04000000:
            is_load = (instr >> 20) & 1
            is_byte = (instr >> 22) & 1
            rn = (instr >> 16) & 0xF
            rd = (instr >> 12) & 0xF
            offset = instr & 0xFFF
            if not (instr & 0x00800000): offset = -offset
            addr = self.r[rn] + offset
            if is_load:
                self.r[rd] = self.bus.read8(addr) if is_byte else self.bus.read32(addr)
            else:
                if is_byte: self.bus.write8(addr, self.r[rd] & 0xFF)
                else: self.bus.write32(addr, self.r[rd])
            return

        # Block Data Transfer (LDM/STM)
        if (instr & 0x0E000000) == 0x08000000:
            rn = (instr >> 16) & 0xF
            reg_list = instr & 0xFFFF
            is_load = (instr >> 20) & 1
            up = (instr >> 23) & 1
            pre = (instr >> 24) & 1
            writeback = (instr >> 21) & 1
            usermode = (instr >> 22) & 1

            addr = self.r[rn]
            for i in range(16):
                if (reg_list >> i) & 1:
                    if pre:
                        addr += 4 if up else -4
                        if is_load: self.r[i] = self.bus.read32(addr)
                        else: self.bus.write32(addr, self.r[i])
                    else:
                        if is_load: self.r[i] = self.bus.read32(addr)
                        else: self.bus.write32(addr, self.r[i])
                        addr += 4 if up else -4
            if writeback:
                self.r[rn] = addr
            return

        self.halted = True
        self.halt_reason = f"Unimplemented ARM: 0x{instr:08X}"

    # ---------- THUMB Interpreter ----------
    def execute_thumb(self, instr):
        # Move shifted register
        if (instr & 0xE000) == 0x0000:
            op = (instr >> 11) & 3
            offset5 = (instr >> 6) & 0x1F
            rs = (instr >> 3) & 7
            rd = instr & 7
            val = self.r[rs]
            if op == 0: res, carry = self.shift(val, 0, offset5)  # LSL
            elif op == 1: res, carry = self.shift(val, 1, offset5)  # LSR
            elif op == 2: res, carry = self.shift(val, 2, offset5)  # ASR
            else: return
            self.r[rd] = res
            self.set_nz(res)
            self.cpsr = (self.cpsr & ~0x20000000) | (carry << 29)
            return

        # Add/subtract
        if (instr & 0xF800) == 0x1800:
            op = (instr >> 9) & 3
            rn = (instr >> 6) & 7
            rs = (instr >> 3) & 7
            rd = instr & 7
            if op == 0: self.r[rd] = (self.r[rn] + self.r[rs]) & 0xFFFFFFFF
            elif op == 1: self.r[rd] = (self.r[rn] - self.r[rs]) & 0xFFFFFFFF
            elif op == 2: self.r[rd] = (self.r[rn] + self.r[rs]) & 0xFFFFFFFF
            elif op == 3: self.r[rd] = (self.r[rn] - self.r[rs]) & 0xFFFFFFFF
            self.set_nz(self.r[rd])
            return

        # Immediate operations
        if (instr & 0xE000) == 0x2000:
            op = (instr >> 11) & 3
            rd = (instr >> 8) & 7
            imm = instr & 0xFF
            if op == 0: self.r[rd] = imm; self.set_nz(imm)
            elif op == 1: self.set_nz((self.r[rd] - imm) & 0xFFFFFFFF)
            elif op == 2: self.r[rd] = (self.r[rd] + imm) & 0xFFFFFFFF; self.set_nz(self.r[rd])
            elif op == 3: self.r[rd] = (self.r[rd] - imm) & 0xFFFFFFFF; self.set_nz(self.r[rd])
            return

        # ALU operations
        if (instr & 0xFC00) == 0x4000:
            op = (instr >> 6) & 0xF
            rs = (instr >> 3) & 7
            rd = instr & 7
            a = self.r[rd]
            b = self.r[rs]
            if op == 0x0: res = a & b
            elif op == 0x1: res = a ^ b
            elif op == 0x2: res = (a << (b & 0xFF)) & 0xFFFFFFFF
            elif op == 0x3: res = (a >> (b & 0xFF)) & 0xFFFFFFFF
            elif op == 0x4: res = (struct.unpack('<i', struct.pack('<I', a))[0] >> (b & 0xFF)) & 0xFFFFFFFF
            elif op == 0x5: res = (a + b + ((self.cpsr>>29)&1)) & 0xFFFFFFFF
            elif op == 0x6: res = (a - b - (1-((self.cpsr>>29)&1))) & 0xFFFFFFFF
            elif op == 0x7: res = ((b << 8) | (b >> 24)) & 0xFFFFFFFF
            elif op == 0x8: self.set_nz(a & b); return
            elif op == 0x9: res = ~b & 0xFFFFFFFF
            elif op == 0xA: self.set_nz((a - b) & 0xFFFFFFFF); return
            elif op == 0xB: self.set_nz((a + b) & 0xFFFFFFFF); return
            elif op == 0xC: res = a | b
            elif op == 0xD: res = (a * b) & 0xFFFFFFFF
            elif op == 0xE: res = a & ~b
            elif op == 0xF: res = ~b & 0xFFFFFFFF
            self.r[rd] = res
            self.set_nz(res)
            return

        # Hi register operations / BX
        if (instr & 0xFC00) == 0x4400:
            op = (instr >> 8) & 3
            h1 = (instr >> 7) & 1
            h2 = (instr >> 6) & 1
            rs = ((instr >> 3) & 0xF) | (h1 << 3)
            rd = (instr & 7) | (h2 << 3)
            if op == 0: self.r[rd] = (self.r[rd] + self.r[rs]) & 0xFFFFFFFF
            elif op == 1: self.r[rd] = (self.r[rd] - self.r[rs]) & 0xFFFFFFFF; self.set_nz(self.r[rd])
            elif op == 2: self.r[rd] = self.r[rs]
            elif op == 3:
                target = self.r[rs]
                self.cpsr = (self.cpsr & ~0x20) | (target & 1) << 5
                self.r[15] = target & 0xFFFFFFFE
            return

        # PC-relative load
        if (instr & 0xF800) == 0x4800:
            rd = (instr >> 8) & 7
            offset = (instr & 0xFF) << 2
            addr = (self.r[15] & 0xFFFFFFFC) + offset
            self.r[rd] = self.bus.read32(addr)
            return

        # Load/store with register offset
        if (instr & 0xF200) == 0x5000:
            op = (instr >> 10) & 3
            ro = (instr >> 6) & 7
            rb = (instr >> 3) & 7
            rd = instr & 7
            addr = self.r[rb] + self.r[ro]
            if op == 0: self.r[rd] = self.bus.read32(addr)
            elif op == 1: self.r[rd] = self.bus.read8(addr)
            elif op == 2: self.bus.write32(addr, self.r[rd])
            elif op == 3: self.bus.write8(addr, self.r[rd])
            return

        # Load/store with immediate offset
        if (instr & 0xE000) == 0x6000:
            op = (instr >> 11) & 3
            imm = (instr >> 6) & 0x1F
            rb = (instr >> 3) & 7
            rd = instr & 7
            if op == 0: addr = self.r[rb] + (imm << 2); self.r[rd] = self.bus.read32(addr)
            elif op == 1: addr = self.r[rb] + imm; self.r[rd] = self.bus.read8(addr)
            elif op == 2: addr = self.r[rb] + (imm << 2); self.bus.write32(addr, self.r[rd])
            elif op == 3: addr = self.r[rb] + imm; self.bus.write8(addr, self.r[rd])
            return

        # SP-relative load/store
        if (instr & 0xF000) == 0x9000:
            rd = (instr >> 8) & 7
            offset = (instr & 0xFF) << 2
            addr = self.r[13] + offset
            if instr & 0x0800:
                self.r[rd] = self.bus.read32(addr)
            else:
                self.bus.write32(addr, self.r[rd])
            return

        # Push/Pop
        if (instr & 0xF600) == 0xB400:
            reg_list = instr & 0xFF
            is_push = (instr >> 11) & 1
            if is_push:
                self.r[13] -= 4 * bin(reg_list).count('1')
                addr = self.r[13]
                for i in range(8):
                    if (reg_list >> i) & 1:
                        self.bus.write32(addr, self.r[i])
                        addr += 4
            else:
                addr = self.r[13]
                for i in range(8):
                    if (reg_list >> i) & 1:
                        self.r[i] = self.bus.read32(addr)
                        addr += 4
                self.r[13] = addr
            return

        # Conditional branch
        if (instr & 0xF000) == 0xD000:
            cond = (instr >> 8) & 0xF
            if self.check_cond(cond):
                offset = instr & 0xFF
                if offset & 0x80: offset |= 0xFFFFFF00
                self.r[15] = (self.r[15] + (offset << 1)) & 0xFFFFFFFF
            return

        # SWI
        if (instr & 0xFF00) == 0xDF00:
            self.execute_swi(instr & 0xFF)
            return

        # Unconditional branch
        if (instr & 0xF800) == 0xE000:
            offset = instr & 0x7FF
            if offset & 0x400: offset |= 0xFFFFF800
            self.r[15] = (self.r[15] + (offset << 1)) & 0xFFFFFFFF
            return

        self.halted = True
        self.halt_reason = f"Unimplemented THUMB: 0x{instr:04X}"

    def execute_swi(self, num):
        # Basic HLE BIOS functions
        if num == 0x02: self.cycles += 1000
        elif num == 0x05:   # CpuFastSet
            src, dst, ctrl = self.r[0], self.r[1], self.r[2]
            count = ctrl & 0x1FFFFF
            for i in range(count):
                self.bus.write32(dst + i*4, self.bus.read32(src + i*4))
        elif num == 0x0B:   # CpuSet
            src, dst, ctrl = self.r[0], self.r[1], self.r[2]
            count = ctrl & 0x1FFFFF
            for i in range(count):
                self.bus.write32(dst + i*4, self.bus.read32(src + i*4))
        elif num == 0x06:   # Div
            if self.r[1] == 0: self.r[0], self.r[1], self.r[3] = 0, 0, 0
            else:
                self.r[0] = (self.r[0] // self.r[1]) & 0xFFFFFFFF
                self.r[1] = (self.r[0] % self.r[1]) & 0xFFFFFFFF
                self.r[3] = abs(self.r[0] // self.r[1]) & 0xFFFFFFFF


class GBAMemoryBus:
    def __init__(self, rom_data):
        self.rom = rom_data
        self.ewram = bytearray(256 * 1024)
        self.iwram = bytearray(32 * 1024)
        self.ioregs = bytearray(1024)
        self.vram = bytearray(96 * 1024)
        self.palette = bytearray(1024)
        self.oam = bytearray(1024)
        self.sram = bytearray(64 * 1024)     # 64KB SRAM
        self.scanline = 0
        self.bios_loaded = False
        self.bios = bytearray()

        # Interrupts
        self.irq_enable = 0
        self.irq_flags = 0
        self.irq_master = True

        # Timers (simple)
        self.timer_counter = [0]*4
        self.timer_reload = [0]*4

        # Load BIOS
        if os.path.exists("gba_bios.bin"):
            with open("gba_bios.bin", "rb") as f:
                self.bios = bytearray(f.read())
                self.bios_loaded = True

        # Detect save type (simple heuristic)
        self.save_type = self.detect_save_type()

    def detect_save_type(self):
        # Look for known save type strings in ROM
        rom_str = self.rom.tobytes() if isinstance(self.rom, bytearray) else bytes(self.rom)
        if b"EEPROM_V" in rom_str: return "EEPROM"
        if b"SRAM_V" in rom_str: return "SRAM"
        if b"FLASH_V" in rom_str or b"FLASH512_V" in rom_str: return "FLASH"
        if b"SII" in rom_str[0xA0:0xAC]: return "SRAM"
        return "SRAM"  # default

    def _map(self, addr):
        region = addr >> 24
        if region == 0x00 and self.bios_loaded:
            return self.bios, addr & 0x3FFF
        if region == 0x02:
            return self.ewram, addr & 0x3FFFF
        if region == 0x03:
            return self.iwram, addr & 0x7FFF
        if region == 0x04:
            return self.ioregs, addr & 0x3FF
        if region == 0x05:
            return self.palette, addr & 0x3FF
        if region == 0x06:
            return self.vram, addr & 0x1FFFF
        if region == 0x07:
            return self.oam, addr & 0x3FF
        if 0x08 <= region <= 0x0D:
            return self.rom, addr & 0x1FFFFFF
        if 0x0E <= region <= 0x0F and self.save_type == "SRAM":
            return self.sram, addr & 0xFFFF
        return None, 0

    def read8(self, addr):
        if addr == 0x04000006: return self.scanline & 0xFF
        if addr == 0x04000130: return (self.irq_flags) & 0xFF
        if addr == 0x04000131: return (self.irq_flags >> 8) & 0xFF
        if addr == 0x04000208: return 0  # IME
        buf, off = self._map(addr)
        if buf and off < len(buf): return buf[off]
        return 0

    def write8(self, addr, val):
        if addr == 0x04000208:
            self.irq_master = (val & 1) != 0
            return
        if addr == 0x04000130:
            self.irq_flags &= ~(val & 0xFF)
            return
        if addr == 0x04000131:
            self.irq_flags &= ~((val << 8) & 0xFF00)
            return
        buf, off = self._map(addr)
        if buf and off < len(buf) and addr < 0x08000000:
            buf[off] = val & 0xFF

    def read16(self, addr):
        if addr == 0x04000006: return self.scanline
        buf, off = self._map(addr)
        if buf and off+1 < len(buf): return struct.unpack_from('<H', buf, off)[0]
        return 0

    def write16(self, addr, val):
        if addr == 0x04000004: self.scanline = 0
        if addr == 0x04000200: self.irq_enable = val & 0x3FFF
        if addr == 0x04000202: self.irq_flags &= ~val
        buf, off = self._map(addr)
        if buf and off+1 < len(buf) and addr < 0x08000000:
            struct.pack_into('<H', buf, off, val & 0xFFFF)

    def read32(self, addr):
        buf, off = self._map(addr)
        if buf and off+3 < len(buf): return struct.unpack_from('<I', buf, off)[0]
        return 0

    def write32(self, addr, val):
        buf, off = self._map(addr)
        if buf and off+3 < len(buf) and addr < 0x08000000:
            struct.pack_into('<I', buf, off, val)

    def update_timers(self, cycles):
        # Minimal VBlank IRQ trigger
        self.scanline += cycles // 4
        if self.scanline >= 228:
            self.scanline = 0
            self.irq_flags |= 0x0001  # VBlank IRQ
        if self.irq_master and (self.irq_enable & self.irq_flags):
            # Trigger IRQ (not implemented fully)
            pass


class GGBACore:
    def __init__(self, rom_path):
        with open(rom_path, "rb") as f: self.rom_data = f.read()
        self.bus = GBAMemoryBus(self.rom_data)
        self.cpu = ARM7TDMI(self.bus)
        self.cpu.reset(skip_bios=not self.bus.bios_loaded)
        try:
            self.title = self.rom_data[0xA0:0xAC].decode('ascii', errors='ignore').strip()
            if not self.title: self.title = "UNKNOWN ROM"
        except:
            self.title = "INVALID HEADER"

    def run_frame(self):
        for line in range(228):
            self.bus.scanline = line
            for _ in range(250):
                if self.cpu.halted: break
                self.cpu.step()
        return self._render_vram()

    def _render_vram(self):
        width, height = 240, 160
        buffer = bytearray(width * height * 3)
        vram = self.bus.vram
        for y in range(height):
            for x in range(width):
                idx = (y * width + x) * 2
                if idx+1 < len(vram):
                    pixel = struct.unpack_from('<H', vram, idx)[0]
                    r = (pixel & 0x1F) << 3
                    g = ((pixel >> 5) & 0x1F) << 3
                    b = ((pixel >> 10) & 0x1F) << 3
                    idx_b = (y * width + x) * 3
                    buffer[idx_b:idx_b+3] = [r, g, b]
        if sum(vram[:1000]) == 0:
            for i in range(0, len(buffer), 3): buffer[i:i+3] = [30, 30, 30]
        return bytes(buffer)


# =================================================================
# GUI APPLICATION
# =================================================================

class GBAEmulator:
    def __init__(self, root):
        self.root = root
        self.root.title("AC HOLDING GBAEMU 0.3 - EXPANDED CORE")
        self.root.geometry("600x520")
        self.root.resizable(False, False)
        self.root.configure(bg="#0a0a0a")
        self.is_running = False
        self.gba_core = None
        self.photo = None
        self.boot_frames = 0
        self.setup_ui()

    def setup_ui(self):
        menubar = tk.Menu(self.root)
        file_menu = tk.Menu(menubar, tearoff=0)
        file_menu.add_command(label="Open ROM...", command=self.open_rom)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.root.quit)
        menubar.add_cascade(label="File", menu=file_menu)
        self.root.config(menu=menubar)
        self.canvas_frame = tk.Frame(self.root, bg="black", bd=0)
        self.canvas_frame.place(x=0, y=0, width=600, height=400)
        self.screen = tk.Canvas(self.canvas_frame, bg="#000", highlightthickness=0)
        self.screen.pack(expand=True, fill="both")
        self.screen.create_text(300, 200, text="AC HOLDING GBAEMU\nEXPANDED HARDWARE CORE\n\nLOAD COMMERCIAL ROM",
                                fill="#00FF00", font=("Consolas", 12, "bold"), justify="center", tags="splash")
        self.status_bar = tk.Label(self.root, text="System: Ready", bd=0, relief="flat",
                                   anchor="w", padx=10, bg="#111", fg="#888", font=("Consolas", 9))
        self.status_bar.pack(side="bottom", fill="x")

    def open_rom(self):
        file_path = filedialog.askopenfilename(title="Select ROM", filetypes=(("GBA", "*.gba"), ("All", "*.*")))
        if file_path:
            self.screen.delete("all")
            self.gba_core = GGBACore(file_path)
            self.is_running = True
            self.boot_frames = 0
            if self.gba_core.bus.bios_loaded:
                self.status_bar.config(text=f"Loaded: {self.gba_core.title} [Real BIOS Boot]")
                self.start_emulation_loop()
            else:
                self.status_bar.config(text=f"Loaded: {self.gba_core.title} [HLE Booting]")
                self.play_hle_boot_sequence()

    def play_hle_boot_sequence(self):
        if self.boot_frames == 0:
            self.screen.delete("all")
            self.screen.create_rectangle(0, 0, 600, 400, fill="white", tags="bg")
            self.screen.create_text(300, -50, text="GAME BOY", font=("Arial Black", 32, "italic"), fill="#1a1a1a", tags="logo")
        if self.boot_frames < 60:
            y_pos = -50 + (self.boot_frames * 3.5)
            if y_pos > 160: y_pos = 160
            self.screen.coords("logo", 300, y_pos)
            self.boot_frames += 1
            self.root.after(16, self.play_hle_boot_sequence)
        elif self.boot_frames == 60:
            self.screen.create_text(300, 240, text="Nintendo®", font=("Arial", 16, "bold"), fill="red", tags="nintendo")
            self.boot_frames += 1
            self.root.after(1200, self.play_hle_boot_sequence)
        else:
            self.screen.delete("all")
            self.status_bar.config(text=f"Running: {self.gba_core.title}")
            self.start_emulation_loop()

    def render_frame(self, data):
        img = Image.frombytes('RGB', (240, 160), data)
        img = img.resize((600, 400), Image.NEAREST)
        self.photo = ImageTk.PhotoImage(image=img)
        self.screen.create_image(0, 0, image=self.photo, anchor="nw")

    def start_emulation_loop(self):
        if not self.is_running or not self.gba_core: return
        self.screen.delete("overlay")
        frame_buffer = self.gba_core.run_frame()
        self.render_frame(frame_buffer)
        cpu = self.gba_core.cpu
        self.screen.create_text(10, 10, text=f"PC: 0x{cpu.r[15]:08X} | CPSR: {cpu.cpsr:08X}",
                                fill="#0f0", anchor="nw", font=("Consolas", 10), tags="overlay")
        if cpu.halted:
            self.screen.create_text(300, 380, text=f"HALT: {cpu.halt_reason[:50]}",
                                    fill="red", font=("Consolas", 8), tags="overlay")
        else:
            self.root.after(16, self.start_emulation_loop)


if __name__ == "__main__":
    root = tk.Tk()
    app = GBAEmulator(root)
    root.mainloop()
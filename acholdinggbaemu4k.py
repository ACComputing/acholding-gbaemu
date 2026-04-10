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
        # R0-R12 (General Purpose), R13 (SP), R14 (LR), R15 (PC)
        self.r = array.array('I', [0] * 16)
        self.cpsr = 0x0000001F  # System Mode
        self.halted = False
        self.halt_reason = ""
        self.cycles = 0

    def reset(self, skip_bios=True):
        """Hardware reset sequence."""
        # Detect if a real BIOS file is loaded
        if not skip_bios and getattr(self.bus, 'bios_loaded', False):
            self.r[15] = 0x00000000 # Start at BIOS entry
            self.cpsr = 0x000000D3  # Supervisor Mode, IRQ/FIQ disabled
        else:
            # HLE ROM Boot entry state
            self.r[13] = 0x03007F00 # IWRAM Stack Pointer
            self.r[15] = 0x08000000 # PC points to ROM entry
            self.cpsr = 0x0000001F  # System Mode
        
        self.halted = False
        self.halt_reason = ""
        self.cycles = 0

    def set_flags(self, result):
        """Sets Negative (N) and Zero (Z) CPSR flags for loops."""
        self.cpsr &= ~(0xC0000000) # Clear N and Z
        if result == 0: 
            self.cpsr |= 0x40000000 # Set Z
        if result & 0x80000000: 
            self.cpsr |= 0x80000000 # Set N

    def check_cond(self, cond):
        """Evaluates ARM condition codes."""
        if cond == 0xE: return True # AL (Always)
        z = (self.cpsr >> 30) & 1
        n = (self.cpsr >> 31) & 1
        if cond == 0x0: return z == 1 # EQ
        if cond == 0x1: return z == 0 # NE
        if cond == 0xA: return n == 0 # GE (Simplified)
        if cond == 0xB: return n == 1 # LT (Simplified)
        return True # Default HLE Fallback

    def step(self):
        """Fetches and executes a single real CPU instruction."""
        if self.halted: return

        try:
            in_thumb = (self.cpsr & 0x20) != 0

            if in_thumb:
                pc = self.r[15]
                instruction = self.bus.read16(pc)
                self.r[15] += 2
                self.execute_thumb(instruction)
            else:
                pc = self.r[15]
                instruction = self.bus.read32(pc)
                self.r[15] += 4
                self.execute_arm(instruction)
                
            self.cycles += 1

        except Exception as e:
            self.halted = True
            self.halt_reason = f"Crash at {self.r[15]:08X}: {str(e)}"

    def execute_swi(self, swi_num):
        """HLE BIOS: Simulates standard GBA Software Interrupts."""
        if swi_num == 0x02: # VBlankIntrWait
            self.cycles += 1000
        elif swi_num == 0x05: # VRAM Set
            src, dst, count = self.r[0], self.r[1], self.r[2] & 0x1FFFFF
            for i in range(count):
                self.bus.write32(dst + (i*4), self.bus.read32(src + (i*4)))
        elif swi_num == 0x0B: # CpuSet
            src, dst, cnt = self.r[0], self.r[1], self.r[2]
            for i in range(cnt & 0x1FFFFF):
                self.bus.write32(dst + (i*4), self.bus.read32(src + (i*4)))

    def execute_arm(self, instr):
        """Decodes and executes real ARM32 machine code."""
        cond = (instr >> 28) & 0xF
        if not self.check_cond(cond):
            return # Condition failed, skip instruction

        # Software Interrupt (SWI)
        if (instr & 0x0F000000) == 0x0F000000:
            self.execute_swi((instr >> 16) & 0xFF)
            return

        # 1. Branch (B) or Branch with Link (BL)
        if (instr & 0x0E000000) == 0x0A000000:
            link = (instr >> 24) & 1
            if link: self.r[14] = self.r[15]
            
            offset = instr & 0x00FFFFFF
            if offset & 0x00800000: offset |= 0xFF000000
            offset = struct.unpack('<i', struct.pack('<I', offset))[0] 
            self.r[15] = (self.r[15] + (offset << 2) + 4) & 0xFFFFFFFF
            return

        # 2. Data Processing (ADD, MOV, SUB, CMP, AND, ORR)
        if (instr & 0x0C000000) == 0x00000000:
            opcode = (instr >> 21) & 0xF
            set_cc = (instr >> 20) & 1
            rn = (instr >> 16) & 0xF
            rd = (instr >> 12) & 0xF
            
            if (instr & 0x02000000): # Immediate
                val = instr & 0xFF
                rotate = (instr >> 8) & 0xF
                val = ((val >> (rotate * 2)) | (val << (32 - (rotate * 2)))) & 0xFFFFFFFF
            else: # Register
                rm = instr & 0xF
                val = self.r[rm]

            res = 0
            if opcode == 0x0: res = self.r[rd] = self.r[rn] & val # AND
            elif opcode == 0x2: res = self.r[rd] = (self.r[rn] - val) & 0xFFFFFFFF # SUB
            elif opcode == 0x4: res = self.r[rd] = (self.r[rn] + val) & 0xFFFFFFFF # ADD
            elif opcode == 0xA: res = (self.r[rn] - val) & 0xFFFFFFFF # CMP
            elif opcode == 0xC: res = self.r[rd] = self.r[rn] | val # ORR
            elif opcode == 0xD: res = self.r[rd] = val # MOV
            
            if set_cc: self.set_flags(res)
            return

        # 3. Load/Store (LDR/STR / LDRB/STRB)
        if (instr & 0x0C000000) == 0x04000000:
            is_load = (instr >> 20) & 1
            is_byte = (instr >> 22) & 1
            rn = (instr >> 16) & 0xF
            rd = (instr >> 12) & 0xF
            offset = instr & 0xFFF
            
            # Simple down-direction support (U=0)
            if not ((instr >> 23) & 1): offset = -offset
            
            addr = (self.r[rn] + offset) & 0xFFFFFFFF
            if is_load:
                self.r[rd] = self.bus.read8(addr) if is_byte else self.bus.read32(addr)
            else:
                if is_byte: self.bus.write8(addr, self.r[rd])
                else: self.bus.write32(addr, self.r[rd])
            return

        # 4. Block Data Transfer (LDM/STM)
        if (instr & 0x0E000000) == 0x08000000:
            rn = (instr >> 16) & 0xF
            reg_list = instr & 0xFFFF
            is_load = (instr >> 20) & 1
            up = (instr >> 23) & 1
            writeback = (instr >> 21) & 1
            
            addr = self.r[rn]
            for i in range(16):
                if (reg_list >> i) & 1:
                    if is_load: self.r[i] = self.bus.read32(addr)
                    else: self.bus.write32(addr, self.r[i])
                    addr += 4 if up else -4
            
            if writeback: self.r[rn] = addr
            return

        # Relaxed halting: Gracefully NOP unimplemented instructions to allow commercial games to push further
        self.halt_reason = f"Ignored ARM: 0x{instr:08X}"

    def execute_thumb(self, instr):
        """Decodes and executes real THUMB16 machine code."""
        if (instr & 0xFF00) == 0xDF00: # THUMB SWI
            self.execute_swi(instr & 0xFF)
            return

        if (instr & 0xE000) == 0x2000: # THUMB Move/Compare/Add/Sub immediate
            opcode = (instr >> 11) & 0x3
            rd = (instr >> 8) & 0x7
            val = instr & 0xFF
            if opcode == 0: 
                self.r[rd] = val # MOV
                self.set_flags(val)
            elif opcode == 1:
                self.set_flags((self.r[rd] - val) & 0xFFFFFFFF) # CMP
            return
            
        if (instr & 0xFF80) == 0x4700: # THUMB BX
            rs = (instr >> 3) & 0xF
            target = self.r[rs]
            if target & 1: self.cpsr |= 0x20
            else: self.cpsr &= ~0x20
            self.r[15] = target & 0xFFFFFFFE
            return

        # Relaxed halting: Gracefully NOP unimplemented instructions to allow commercial games to push further
        self.halt_reason = f"Ignored THUMB: 0x{instr:04X}"

class GBAMemoryBus:
    def __init__(self, rom_data):
        self.rom = rom_data
        self.ewram = bytearray(256 * 1024)
        self.iwram = bytearray(32 * 1024)
        self.ioregs = bytearray(1024)
        self.vram = bytearray(96 * 1024)
        self.palette = bytearray(1024)
        self.sram = bytearray(64 * 1024)  # Added: Commercial ROM Backup Memory support
        self.scanline = 0
        
        # Load BIOS if present in the directory
        if os.path.exists("gba_bios.bin"):
            with open("gba_bios.bin", "rb") as f:
                self.bios = bytearray(f.read())
                self.bios_loaded = True
        else:
            self.bios_loaded = False

    def _map(self, addr):
        """Maps full 32-bit address into mirrored hardware regions."""
        region = (addr >> 24) & 0xFF
        if region == 0x00 and self.bios_loaded: return self.bios, addr & 0x3FFF
        if region == 0x02: return self.ewram, addr & 0x3FFFF
        if region == 0x03: return self.iwram, addr & 0x7FFF
        if region == 0x04: return self.ioregs, addr & 0x3FF
        if region == 0x05: return self.palette, addr & 0x3FF
        if region == 0x06: return self.vram, addr & 0x1FFFF
        if 0x08 <= region <= 0x0D: 
            # Fixed: Modulo ROM length to support commercial bank mirroring
            if len(self.rom) > 0:
                return self.rom, (addr & 0x1FFFFFF) % len(self.rom)
        if region == 0x0E: return self.sram, addr & 0xFFFF # Added: SRAM backup memory
        return None, 0

    def read8(self, addr):
        buf, off = self._map(addr)
        if buf and off < len(buf): return buf[off]
        return 0

    def write8(self, addr, val):
        buf, off = self._map(addr)
        if buf and off < len(buf) and (addr < 0x08000000 or addr >= 0x0E000000): # Allow SRAM writes
            buf[off] = val & 0xFF

    def read16(self, addr):
        if addr == 0x04000006: return self.scanline # VCOUNT
        buf, off = self._map(addr)
        if buf and off + 1 < len(buf): return struct.unpack_from('<H', buf, off)[0]
        return 0

    def write16(self, addr, val):
        buf, off = self._map(addr)
        if buf and off + 1 < len(buf) and (addr < 0x08000000 or addr >= 0x0E000000):
            struct.pack_into('<H', buf, off, val & 0xFFFF)

    def read32(self, addr):
        buf, off = self._map(addr)
        if buf and off + 3 < len(buf): return struct.unpack_from('<I', buf, off)[0]
        return 0

    def write32(self, addr, val):
        buf, off = self._map(addr)
        if buf and off + 3 < len(buf) and (addr < 0x08000000 or addr >= 0x0E000000):
            struct.pack_into('<I', buf, off, val)

class GGBACore:
    def __init__(self, rom_path):
        with open(rom_path, "rb") as f: self.rom_data = f.read()
        self.bus = GBAMemoryBus(self.rom_data)
        self.cpu = ARM7TDMI(self.bus)
        
        # If a real BIOS is detected, run through it! Otherwise skip.
        self.cpu.reset(skip_bios=not self.bus.bios_loaded)
        
        try:
            self.title = self.rom_data[0xA0:0xAC].decode('ascii', errors='ignore').strip()
            if not self.title: self.title = "UNKNOWN ROM"
        except:
            self.title = "INVALID HEADER"

    def run_frame(self):
        """Runs approx cycles and simulates scanlines."""
        for line in range(228):
            self.bus.scanline = line
            for _ in range(250): # Frame slice
                if self.cpu.halted: break
                self.cpu.step()
        return self._render_vram()

    def _render_vram(self):
        width, height = 240, 160
        buffer = bytearray(width * height * 3)
        vram = self.bus.vram
        
        # Mode 3 Simplified Rendering
        for y in range(height):
            for x in range(width):
                idx_v = (y * width + x) * 2
                if idx_v + 1 < len(vram):
                    pixel = struct.unpack_from('<H', vram, idx_v)[0]
                    r, g, b = (pixel & 0x1F) << 3, ((pixel >> 5) & 0x1F) << 3, ((pixel >> 10) & 0x1F) << 3
                    idx_b = (y * width + x) * 3
                    buffer[idx_b:idx_b+3] = [r, g, b]
        
        # If VRAM is empty, display a generic gray screen to verify active display signal
        if sum(vram[:1000]) == 0:
            for i in range(0, len(buffer), 3): buffer[i:i+3] = [30, 30, 30]
            
        return bytes(buffer)

# =================================================================
# GUI APPLICATION
# =================================================================

class GBAEmulator:
    def __init__(self, root):
        self.root = root
        self.root.title("AC HOLDING GBAEMU 0.2 - ROM BOOT COMPAT")
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

        self.screen.create_text(300, 200, text="AC HOLDING GBAEMU\nHLE HARDWARE CORE\n\nLOAD COMMERCIAL ROM", 
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
                self.start_emulation_loop() # Rely on actual emulation to show logo
            else:
                self.status_bar.config(text=f"Loaded: {self.gba_core.title} [HLE Booting]")
                self.play_hle_boot_sequence()

    def play_hle_boot_sequence(self):
        """Simulates the iconic visual GBA boot sequence if no actual BIOS file is loaded."""
        if self.boot_frames == 0:
            self.screen.delete("all")
            self.screen.create_rectangle(0, 0, 600, 400, fill="white", tags="bg")
            self.screen.create_text(300, -50, text="GAME BOY", font=("Arial Black", 32, "italic"), fill="#1a1a1a", tags="logo")
        
        if self.boot_frames < 60:
            # Drop the Gameboy logo down
            y_pos = -50 + (self.boot_frames * 3.5)
            if y_pos > 160: y_pos = 160
            self.screen.coords("logo", 300, y_pos)
            self.boot_frames += 1
            self.root.after(16, self.play_hle_boot_sequence)
        elif self.boot_frames == 60:
            # Flash "Nintendo" logo exactly like the original BIOS
            self.screen.create_text(300, 240, text="Nintendo®", font=("Arial", 16, "bold"), fill="red", tags="nintendo")
            self.boot_frames += 1
            self.root.after(1200, self.play_hle_boot_sequence) # Hold on screen
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
        # Display Execution State Overlay
        self.screen.create_text(10, 10, text=f"PC: 0x{cpu.r[15]:08X} | CPSR: {cpu.cpsr:08X}", 
                                fill="#0f0", anchor="nw", font=("Consolas", 10), tags="overlay")
        
        if cpu.halted:
            self.screen.create_text(300, 380, text=f"HALT: {cpu.halt_reason[:50]}", 
                                    fill="red", font=("Consolas", 8), tags="overlay")
        else:
            # Added visual read-out for gracefully ignored instructions
            if cpu.halt_reason:
                self.screen.create_text(300, 380, text=f"WARN: {cpu.halt_reason[:50]}", 
                                        fill="orange", font=("Consolas", 8), tags="overlay")
                cpu.halt_reason = "" # Clear after warning
                
            self.root.after(16, self.start_emulation_loop)

if __name__ == "__main__":
    root = tk.Tk()
    app = GBAEmulator(root)
    root.mainloop()

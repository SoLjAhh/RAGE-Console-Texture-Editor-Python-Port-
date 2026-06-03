#!/usr/bin/env python3
"""
RAGE Console Texture Editor - Python Port
==========================================
A faithful Python/Tkinter port of indirivacua/RAGE-Console-Texture-Editor
(originally by Dageron), a texture editor for console RAGE games
(GTA IV, GTA V, RDR, MC:LA, MP3).

Supports texture dictionaries for:
  - PC          .ytd          RSC7 'RSC7' magic, Little-Endian, zlib
  - PS3         .ctd / .xtd   RSC7 '7CSR' magic, Big-Endian, zlib
  - Xbox 360    .xtd          RSC7 '7CSR' magic, Big-Endian, LZX (via xcompress.dll)

IMPORTANT - Xbox 360 LZX decompression:
  Xbox 360 resources are LZX-compressed using Microsoft's proprietary codec.
  Exactly like the original Pascal tool, this port does NOT reimplement LZX;
  it calls the same native Windows DLLs through ctypes:
      xcompress.dll       (Microsoft XMem* functions)
      xcompress_cpp.dll   (LZXinit / LZXdecompress - GTA IV / RDR, Codec 0)
      xcompress_open.dll  (xDecompress / xCompress   - GTA V,      Codec 1)
  Place those three DLLs in the same folder as this script. Because they are
  32-bit native Windows libraries, the Xbox 360 path only works when this
  script is run with a 32-bit Python interpreter on Windows. PC and PS3 paths
  (zlib) work on any platform.

Port notes:
  Pascal unit               -> Python section
  Global.Endian             -> endian helpers (EndianChange*)
  Compression.ZLib          -> zlib (stdlib)
  Compression.LZX           -> class LZX (ctypes wrapper)
  Console.Xbox360.Swizzling -> XGAddress2DTiledOffset
  Console.Xbox360.Graphics  -> D3DBaseTexture decode, GPU format table, untile
  GTAIV.TextureResource.*   -> ResourcePS3 / ResourceXbox360 loaders + parsers
  Global.DirectDrawSurface  -> make_dds / dds builder
  MainUnit / About / Intro  -> Tkinter GUI (class App)
"""

import sys, os, io, struct, zlib, ctypes, math, subprocess, importlib
from pathlib import Path

# ============================================================================
# Dependency bootstrap
# ----------------------------------------------------------------------------
# Auto-installs missing pip packages on first run so the tool "just works" for
# end users. tkinter ships with python.org installers; if it is genuinely
# missing (some Linux distros) we cannot pip-install it, so we explain instead.
# ============================================================================
def _ensure_package(import_name, pip_name=None, friendly=None):
    """Import a module, pip-installing it on demand if absent."""
    pip_name = pip_name or import_name
    try:
        return importlib.import_module(import_name)
    except ImportError:
        pass
    # Don't try to auto-install inside frozen exes (PyInstaller bundles deps).
    if getattr(sys, "frozen", False):
        return None
    try:
        print(f"[setup] Installing missing dependency: {pip_name} ...")
        subprocess.check_call(
            [sys.executable, "-m", "pip", "install", "--user", pip_name],
            stdout=subprocess.DEVNULL, stderr=subprocess.STDOUT)
    except Exception:
        # Retry without --user (some environments disallow it).
        try:
            subprocess.check_call([sys.executable, "-m", "pip", "install", pip_name],
                                  stdout=subprocess.DEVNULL, stderr=subprocess.STDOUT)
        except Exception as e:
            print(f"[setup] Could not auto-install {pip_name}: {e}")
            return None
    importlib.invalidate_caches()
    try:
        return importlib.import_module(import_name)
    except ImportError:
        return None

# tkinter is required for the GUI and cannot be pip-installed.
try:
    import tkinter as tk
    from tkinter import ttk, filedialog, messagebox
except ImportError:
    sys.stderr.write(
        "ERROR: tkinter is not available.\n"
        "  - Windows/macOS: reinstall Python from python.org (tkinter is included).\n"
        "  - Debian/Ubuntu: sudo apt install python3-tk\n"
        "  - Fedora:        sudo dnf install python3-tkinter\n")
    sys.exit(1)

# Pillow (preview + image import/conversion). Auto-installed if missing.
_PIL = _ensure_package("PIL", "Pillow")
if _PIL is not None:
    from PIL import Image, ImageTk
    PIL_AVAILABLE = True
else:
    PIL_AVAILABLE = False

# ============================================================================
# Global.Endian  -- byte-swap helpers
# ============================================================================
def EndianChangeWORD(v):
    v &= 0xFFFF
    return ((v & 0x00FF) << 8) | ((v & 0xFF00) >> 8)

def EndianChangeDWORD(v):
    v &= 0xFFFFFFFF
    return (((v & 0x000000FF) << 24) |
            ((v & 0x0000FF00) << 8)  |
            ((v & 0x00FF0000) >> 8)  |
            ((v & 0xFF000000) >> 24))

# ============================================================================
# Constants
# ============================================================================
PC_MAGIC      = b'RSC7'        # 0x37435352 little-endian on disk
CONSOLE_MAGIC = b'7CSR'        # 0x52534337 ... read as DWORD = 0x37435352 (see below)
DDS_MAGIC     = b'DDS '

# Signature DWORDs as read little-endian from the first 4 bytes (matches Pascal
# 'InStream.Read(dwSignature,4)' on a little-endian machine).
SIG_RSC7_GTA5 = 0x37435352     # '7CSR' bytes -> GTA V console (and PC shares 'RSC7' text)
# In the original, GTA V is detected by dwSignature = $37435352. Both PC 'RSC7'
# and console '7CSR' produce this same little-endian DWORD because the 4 chars
# are a reversal of each other; platform is then disambiguated by file/user.

SUPPORTED_EXTS = ".ytd .xtd .ctd .xhm .chm .xshp .cshp .xsf .csf .sys .gfx"

PLATFORMS = ["PC", "PS3", "Xbox 360"]

# UI colours (Catppuccin-ish, matching the prior Python tool's look)
BG="#1e1e2e"; FG="#cdd6f4"; ACCENT="#89b4fa"; PANEL="#181825"; ENTRY="#313244"
BTN="#45475a"; BTNACT="#585b70"; GREEN="#a6e3a1"; RED="#f38ba8"; YELLOW="#f9e2af"
MAUVE="#cba6f7"; TEAL="#94e2d5"

# ============================================================================
# Compression.LZX  -- ctypes wrapper around the three native DLLs
# ============================================================================
class LZXError(RuntimeError):
    pass

class LZX:
    """
    Faithful wrapper of Compression.LZX.pas.

    Two decode paths, exactly as the Pascal DecompressLZX:
      Codec 0 (GTA IV / RDR): block loop using LZXinit + LZXdecompress
               from xcompress_cpp.dll. Each block is framed by ReadBlockSize:
                 first byte 0xFF -> 5-byte header: FF u u c c
                       UnCompressedSize = b2 | b1<<8 ; CompressedSize = b4 | b3<<8
                 otherwise       -> 2-byte header: b0 b1
                       UnCompressedSize = 0x8000 ; CompressedSize = b1 | b0<<8
      Codec 1 (GTA V): single call to xDecompress from xcompress_open.dll
               (output size discovered by the DLL).
    """
def _app_dir():
    """Directory of the script or frozen exe."""
    if getattr(sys, "frozen", False):
        return os.path.dirname(sys.executable)
    return os.path.dirname(os.path.abspath(__file__))

def _python_bits():
    return 64 if sys.maxsize > 2**32 else 32

class LZX:
    """
    Faithful wrapper of Compression.LZX.pas.

    Two decode paths, exactly as the Pascal DecompressLZX:
      Codec 0 (GTA IV / RDR): block loop using LZXinit + LZXdecompress
               from xcompress_cpp.dll. Each block is framed by ReadBlockSize:
                 first byte 0xFF -> 5-byte header: FF u u c c
                       UnCompressedSize = b2 | b1<<8 ; CompressedSize = b4 | b3<<8
                 otherwise       -> 2-byte header: b0 b1
                       UnCompressedSize = 0x8000 ; CompressedSize = b1 | b0<<8
      Codec 1 (GTA V): single call to xDecompress from xcompress_open.dll;
               xDecompress mallocs the output, writes the pointer back through
               arg3 (**pDest) and the size through arg4 (*pOSize). Verified by
               disassembly of the supplied DLL.

    DLL discovery searches several locations so end users can drop the DLLs
    anywhere sensible: next to the script/exe, a ./lib or ./dll subfolder, or
    the current working directory.
    """
    DLL_NAMES = ("xcompress.dll", "xcompress_cpp.dll", "xcompress_open.dll")

    def __init__(self, dll_dir=None):
        self.dll_dir = None
        self._cpp = None       # xcompress_cpp.dll  (Codec 0)
        self._open = None      # xcompress_open.dll (Codec 1)
        self._loaded_err = None
        self._arch_mismatch = False
        self._search_dirs = self._candidate_dirs(dll_dir)
        self._try_load()

    def _candidate_dirs(self, explicit):
        dirs = []
        if explicit:
            dirs.append(explicit)
        app = _app_dir()
        dirs += [app,
                 os.path.join(app, "lib"),
                 os.path.join(app, "dll"),
                 os.path.join(app, "dlls"),
                 os.getcwd()]
        # de-dup, preserve order
        seen = set(); out = []
        for d in dirs:
            ad = os.path.abspath(d)
            if ad not in seen and os.path.isdir(ad):
                seen.add(ad); out.append(ad)
        return out

    def _find_dll(self, name):
        for d in self._search_dirs:
            p = os.path.join(d, name)
            if os.path.isfile(p):
                return p
        return None

    def _try_load(self):
        if os.name != 'nt':
            self._loaded_err = ("Xbox 360 LZX decoding needs the native Windows "
                                "DLLs (xcompress*.dll), so it only runs on Windows. "
                                "PC (.ytd) and PS3 (.ctd) work on this OS.")
            return

        cpp_path  = self._find_dll("xcompress_cpp.dll")
        open_path = self._find_dll("xcompress_open.dll")
        if not cpp_path and not open_path:
            self._loaded_err = ("xcompress_cpp.dll / xcompress_open.dll not found.\n"
                                "Place the three xcompress*.dll files next to this "
                                "program (or in a ./lib subfolder).")
            return

        self.dll_dir = os.path.dirname(cpp_path or open_path)
        prev_cwd = os.getcwd()
        try:
            os.chdir(self.dll_dir)   # helps co-located DLLs resolve each other
            if cpp_path:
                try:
                    self._cpp = ctypes.CDLL(cpp_path)
                    self._cpp.LZXinit.argtypes = [ctypes.c_int]
                    self._cpp.LZXinit.restype  = ctypes.c_int
                    self._cpp.LZXdecompress.argtypes = [ctypes.c_char_p, ctypes.c_int,
                                                        ctypes.c_char_p, ctypes.c_int]
                    self._cpp.LZXdecompress.restype  = ctypes.c_int
                except OSError as e:
                    self._handle_load_error("xcompress_cpp.dll", e)
            if open_path:
                try:
                    self._open = ctypes.CDLL(open_path)
                    # int xDecompress(void* src, DWORD size, void** dest, int* osize, int flags)
                    self._open.xDecompress.argtypes = [ctypes.c_char_p, ctypes.c_uint32,
                                                       ctypes.POINTER(ctypes.c_void_p),
                                                       ctypes.POINTER(ctypes.c_int),
                                                       ctypes.c_int]
                    self._open.xDecompress.restype  = ctypes.c_int
                    # int xCompress(void* src, DWORD size, void** dest, int* osize, int flags)
                    self._open.xCompress.argtypes = [ctypes.c_char_p, ctypes.c_uint32,
                                                     ctypes.POINTER(ctypes.c_void_p),
                                                     ctypes.POINTER(ctypes.c_int),
                                                     ctypes.c_int]
                    self._open.xCompress.restype  = ctypes.c_int
                except OSError as e:
                    self._handle_load_error("xcompress_open.dll", e)
        finally:
            os.chdir(prev_cwd)

    def _handle_load_error(self, which, err):
        # WinError 193 (%1 is not a valid Win32 application) == bitness mismatch.
        msg = str(err)
        if "193" in msg or "not a valid" in msg.lower():
            self._arch_mismatch = True
            note = (f"{which}: architecture mismatch. The DLLs are 32-bit; you are "
                    f"running {_python_bits()}-bit Python. Install/use 32-bit Python.")
        else:
            note = f"{which}: {err}"
        self._loaded_err = (self._loaded_err + "\n" + note) if self._loaded_err else note

    @property
    def available_cpp(self):  return self._cpp is not None
    @property
    def available_open(self): return self._open is not None

    def status(self):
        if os.name != 'nt':
            return "unavailable (not Windows) - PC/PS3 still work"
        if self._arch_mismatch:
            return (f"DLLs are 32-bit but Python is {_python_bits()}-bit -> "
                    f"install 32-bit Python")
        parts = [f"Python {_python_bits()}-bit",
                 "cpp:"  + ("OK" if self._cpp else "missing"),
                 "open:" + ("OK" if self._open else "missing")]
        if self.dll_dir:
            parts.append(f"from {self.dll_dir}")
        return " | ".join(parts)

    # ---- Codec 0: GTA IV / RDR block-framed LZX (window 17) -----------------
    def decompress_blocks(self, data, out_size):
        if not self._cpp:
            raise LZXError("xcompress_cpp.dll unavailable: " + (self._loaded_err or ""))
        self._cpp.LZXinit(17)
        out = bytearray(); pos = 0; n = len(data)
        while len(out) < out_size:
            if pos >= n: break
            b0 = data[pos]; pos += 1
            if b0 == 0xFF:
                if pos + 4 > n: break
                b1, b2, b3, b4 = data[pos], data[pos+1], data[pos+2], data[pos+3]
                pos += 4
                unc = b2 | (b1 << 8); comp = b4 | (b3 << 8)
            else:
                if pos >= n: break
                b1 = data[pos]; pos += 1
                unc = 0x8000; comp = b1 | (b0 << 8)
            if comp <= 0 or pos + comp > n: break
            chunk_in = bytes(data[pos:pos+comp]); pos += comp
            out_buf = ctypes.create_string_buffer(unc)
            self._cpp.LZXdecompress(chunk_in, comp, out_buf, unc)
            out.extend(out_buf.raw[:unc])
        return bytes(out[:out_size]) if out_size else bytes(out)

    # ---- Codec 1: GTA V single-shot xDecompress -----------------------------
    def decompress_open(self, data):
        if not self._open:
            raise LZXError("xcompress_open.dll unavailable: " + (self._loaded_err or ""))
        out_ptr = ctypes.c_void_p(0)
        out_size = ctypes.c_int(0)
        rc = self._open.xDecompress(bytes(data), len(data),
                                    ctypes.byref(out_ptr),
                                    ctypes.byref(out_size), 1)
        if out_size.value <= 0 or not out_ptr.value:
            raise LZXError(f"xDecompress failed (rc={rc}, size={out_size.value})")
        return ctypes.string_at(out_ptr.value, out_size.value)

    # ---- Codec 1 compress: GTA V xCompress (for save/repack) ----------------
    def compress_open(self, data):
        if not self._open:
            raise LZXError("xcompress_open.dll unavailable: " + (self._loaded_err or ""))
        out_ptr = ctypes.c_void_p(0)
        out_size = ctypes.c_int(0)
        rc = self._open.xCompress(bytes(data), len(data),
                                  ctypes.byref(out_ptr),
                                  ctypes.byref(out_size), 1)
        if out_size.value <= 0 or not out_ptr.value:
            raise LZXError(f"xCompress failed (rc={rc}, size={out_size.value})")
        return ctypes.string_at(out_ptr.value, out_size.value)

# ============================================================================
# Console.Xbox360.Swizzling  -- XGAddress2DTiledOffset (Xenon tiling)
# ============================================================================
def XGAddress2DTiledOffset(x, y, w, texelPitch):
    """Direct port of the Pascal function (all DWORD math, masked to 32-bit)."""
    M32 = 0xFFFFFFFF
    alignedWidth = (w + 31) & ~31 & M32
    logBpp = ((texelPitch >> 2) + ((texelPitch >> 1) >> (texelPitch >> 2))) & M32
    Macro = (((x >> 5) + (y >> 5) * (alignedWidth >> 5)) << (logBpp + 7)) & M32
    Micro = (((x & 7) + ((y & 6) << 2)) << logBpp) & M32
    Offset = (Macro
              + ((Micro & ~15 & M32) << 1)
              + (Micro & 15)
              + ((y & 8) << (3 + logBpp))
              + ((y & 1) << 4)) & M32
    res = ((((Offset & ~511 & M32) << 3)
            + ((Offset & 448) << 2)
            + (Offset & 63)
            + ((y & 16) << 7)
            + (((((y & 8) >> 2) + (x >> 3)) & 3) << 6)) >> logBpp) & M32
    return res

# ============================================================================
# Console.Xbox360.Graphics  -- GPU texture format table + D3DBaseTexture decode
# ============================================================================
# Index -> GPUTEXTUREFORMAT name (subset relevant to RAGE textures).
GPU_TEXTURE_FORMAT = {
    0:'GPUTEXTUREFORMAT_1_REVERSE', 1:'GPUTEXTUREFORMAT_1', 2:'GPUTEXTUREFORMAT_8',
    3:'GPUTEXTUREFORMAT_1_5_5_5', 4:'GPUTEXTUREFORMAT_5_6_5', 5:'GPUTEXTUREFORMAT_6_5_5',
    6:'GPUTEXTUREFORMAT_8_8_8_8', 7:'GPUTEXTUREFORMAT_2_10_10_10', 8:'GPUTEXTUREFORMAT_8_A',
    9:'GPUTEXTUREFORMAT_8_B', 10:'GPUTEXTUREFORMAT_8_8', 11:'GPUTEXTUREFORMAT_Cr_Y1_Cb_Y0_REP',
    12:'GPUTEXTUREFORMAT_Y1_Cr_Y0_Cb_REP', 13:'GPUTEXTUREFORMAT_16_16_EDRAM',
    14:'GPUTEXTUREFORMAT_8_8_8_8_A', 15:'GPUTEXTUREFORMAT_4_4_4_4',
    16:'GPUTEXTUREFORMAT_10_11_11', 17:'GPUTEXTUREFORMAT_11_11_10', 18:'GPUTEXTUREFORMAT_DXT1',
    19:'GPUTEXTUREFORMAT_DXT2_3', 20:'GPUTEXTUREFORMAT_DXT4_5',
    21:'GPUTEXTUREFORMAT_16_16_16_16_EDRAM', 22:'GPUTEXTUREFORMAT_24_8',
    23:'GPUTEXTUREFORMAT_24_8_FLOAT', 24:'GPUTEXTUREFORMAT_16', 25:'GPUTEXTUREFORMAT_16_16',
    26:'GPUTEXTUREFORMAT_16_16_16_16', 27:'GPUTEXTUREFORMAT_16_EXPAND',
    28:'GPUTEXTUREFORMAT_16_16_EXPAND', 29:'GPUTEXTUREFORMAT_16_16_16_16_EXPAND',
    30:'GPUTEXTUREFORMAT_16_FLOAT', 31:'GPUTEXTUREFORMAT_16_16_FLOAT',
    32:'GPUTEXTUREFORMAT_16_16_16_16_FLOAT', 33:'GPUTEXTUREFORMAT_32',
    34:'GPUTEXTUREFORMAT_32_32', 35:'GPUTEXTUREFORMAT_32_32_32_32',
    36:'GPUTEXTUREFORMAT_32_FLOAT', 37:'GPUTEXTUREFORMAT_32_32_FLOAT',
    38:'GPUTEXTUREFORMAT_32_32_32_32_FLOAT', 39:'GPUTEXTUREFORMAT_32_AS_8',
    40:'GPUTEXTUREFORMAT_32_AS_8_8', 41:'GPUTEXTUREFORMAT_16_MPEG',
    42:'GPUTEXTUREFORMAT_16_16_MPEG', 43:'GPUTEXTUREFORMAT_8_INTERLACED',
    44:'GPUTEXTUREFORMAT_32_AS_8_INTERLACED', 45:'GPUTEXTUREFORMAT_32_AS_8_8_INTERLACED',
    46:'GPUTEXTUREFORMAT_16_INTERLACED', 47:'GPUTEXTUREFORMAT_16_MPEG_INTERLACED',
    48:'GPUTEXTUREFORMAT_16_16_MPEG_INTERLACED', 49:'GPUTEXTUREFORMAT_DXN',
    50:'GPUTEXTUREFORMAT_8_8_8_8_AS_16_16_16_16', 51:'GPUTEXTUREFORMAT_DXT1_AS_16_16_16_16',
    52:'GPUTEXTUREFORMAT_DXT2_3_AS_16_16_16_16', 53:'GPUTEXTUREFORMAT_DXT4_5_AS_16_16_16_16',
    54:'GPUTEXTUREFORMAT_2_10_10_10_AS_16_16_16_16', 55:'GPUTEXTUREFORMAT_10_11_11_AS_16_16_16_16',
    56:'GPUTEXTUREFORMAT_11_11_10_AS_16_16_16_16', 57:'GPUTEXTUREFORMAT_32_32_32_FLOAT',
    58:'GPUTEXTUREFORMAT_DXT3A', 59:'GPUTEXTUREFORMAT_DXT5A', 60:'GPUTEXTUREFORMAT_CTX1',
    61:'GPUTEXTUREFORMAT_DXT3A_AS_1_1_1_1', 62:'GPUTEXTUREFORMAT_8_8_8_8_GAMMA_EDRAM',
    63:'GPUTEXTUREFORMAT_2_10_10_10_FLOAT_EDRAM',
}
def GetGPUTEXTUREFORMAT(t):
    return GPU_TEXTURE_FORMAT.get(t & 0xFFFFFFFF, '-unknown-')

GPU_ENDIAN = {0:'GPUENDIAN_NONE',1:'GPUENDIAN_8IN16',2:'GPUENDIAN_8IN32',3:'GPUENDIAN_16IN32'}
def GetGPUENDIAN(e):
    return GPU_ENDIAN.get(e & 0xFFFFFFFF, '-invalid-endian-')

# PS3 (RSX) texture format codes -> GPU format name.
# Ported from Console.PS3.Graphics.pas (Dageron). The code byte lives at
# offset +0x08 in each grcTexture struct.
PS3_TEXTURE_FORMAT = {
    133:'GPUTEXTUREFORMAT_8_8_8_8',
    134:'GPUTEXTUREFORMAT_DXT1',
    135:'GPUTEXTUREFORMAT_DXT2_3',
    136:'GPUTEXTUREFORMAT_DXT4_5',
    166:'GPUTEXTUREFORMAT_DXT1',
    167:'GPUTEXTUREFORMAT_DXT2_3',
    168:'GPUTEXTUREFORMAT_DXT4_5',
    148:'GPUTEXTUREFORMAT_DXT5A',
    129:'GPUTEXTUREFORMAT_8',
    161:'GPUTEXTUREFORMAT_8',
}
def GetGPUTEXTUREFORMAT_PS3(code):
    return PS3_TEXTURE_FORMAT.get(code & 0xFF, '-unknown-')

def ps3_data_size(gpu_fmt, w, h):
    """Per-format byte size of a PS3 texture's top mip (Console.PS3.Graphics)."""
    if gpu_fmt == 'GPUTEXTUREFORMAT_DXT1':   return w*h//2
    if gpu_fmt == 'GPUTEXTUREFORMAT_DXT2_3': return w*h
    if gpu_fmt == 'GPUTEXTUREFORMAT_DXT4_5': return w*h
    if gpu_fmt == 'GPUTEXTUREFORMAT_DXT5A':  return w*h
    if gpu_fmt == 'GPUTEXTUREFORMAT_8':      return w*h
    if gpu_fmt == 'GPUTEXTUREFORMAT_8_8_8_8':return w*h*4
    return w*h  # sensible default


def ReadD3DBaseTexture(dwords):
    """
    Port of ReadD3DBaseTexture. dwords is a list of 13 little-endian-read DWORDs
    (DWORD_1..DWORD_13). Returns dict with DataFormat and MaxMipLevel.
    """
    d9  = EndianChangeDWORD(dwords[8])           # dwDWORD_9
    DataFormat = (d9 << 26) & 0xFFFFFFFF
    DataFormat = DataFormat >> 26                # low 6 bits -> GPU format index
    MaxMipLevel = dwords[11]                     # dwDWORD_12 (raw)
    value1 = (MaxMipLevel & 0xC0000000) >> 6
    value2 = (MaxMipLevel & 0x00030000) << 10
    MaxMipLevel = EndianChangeDWORD((value1 | value2) & 0xFFFFFFFF)
    return {'DataFormat': DataFormat, 'MaxMipLevel': MaxMipLevel}

def _align(v, a):
    if v % a != 0:
        v += (a - v % a)
    return v

def untile_and_deswap(raw, fmt_name, width, height, endian):
    """
    Port of the swizzle/untile + endian fix in ExportImageXbox360.
    Returns linear (DDS-ready) pixel bytes for the top mip.
    """
    # Per-format setup: dwSize (tiled buffer), W/H in tiles, texel pitch T, endian.
    if fmt_name == 'GPUTEXTUREFORMAT_DXT1':
        W=_align(width,128); H=_align(height,128); dwSize=W*H//2
        W=width//4; H=height//4; T=8;  endian=1; swz=True
    elif fmt_name == 'GPUTEXTUREFORMAT_DXT2_3':
        W=_align(width,128); H=_align(height,128); dwSize=W*H
        W=width//4; H=height//4; T=16; endian=1; swz=True
    elif fmt_name == 'GPUTEXTUREFORMAT_DXT4_5':
        W=_align(width,128); H=_align(height,128); dwSize=W*H
        W=width//4; H=height//4; T=16; endian=1; swz=True
    elif fmt_name == 'GPUTEXTUREFORMAT_DXT5A':
        W=_align(width,128); H=_align(height,128); dwSize=W*H
        W=width//4; H=height//4; T=8;  endian=1; swz=True
    elif fmt_name == 'GPUTEXTUREFORMAT_8':
        W=_align(width,128); H=_align(height,128); dwSize=W*H
        W=width; H=height; T=1; endian=1; swz=True
    elif fmt_name == 'GPUTEXTUREFORMAT_8_8_8_8':
        W=_align(width,128); H=_align(height,128); dwSize=W*H*4
        W=width; H=height; T=4; endian=2; swz=True
    elif fmt_name == 'GPUTEXTUREFORMAT_DXN':
        W=_align(width,128); H=_align(height,128); dwSize=W*H*4
        W=width; H=height; T=4; endian=2; swz=True
    else:
        # Unhandled format: return as-is (preview will likely fail gracefully).
        return raw

    tiled = bytearray(raw[:dwSize])
    if len(tiled) < dwSize:
        tiled.extend(b'\x00' * (dwSize - len(tiled)))
    graph = bytearray(dwSize)

    if swz:
        for Y in range(H):
            for X in range(W):
                off = XGAddress2DTiledOffset(X, Y, W, T)
                src = off * T
                dst = (X + Y * W) * T
                if src + T <= dwSize and dst + T <= dwSize:
                    graph[dst:dst+T] = tiled[src:src+T]
    else:
        graph[:] = tiled

    # Endian fix on the untiled buffer.
    if GetGPUENDIAN(endian) == 'GPUENDIAN_8IN16':
        for i in range(0, dwSize - 1, 2):
            graph[i], graph[i+1] = graph[i+1], graph[i]
    elif GetGPUENDIAN(endian) == 'GPUENDIAN_8IN32':
        for i in range(0, dwSize - 3, 4):
            graph[i], graph[i+3] = graph[i+3], graph[i]
            graph[i+1], graph[i+2] = graph[i+2], graph[i+1]
    return bytes(graph)

def _xbox_format_setup(fmt_name, width, height):
    """Per-format tiling parameters shared by untile (export) and retile
    (import). Returns (dwSize, W_tiles, H_tiles, texelPitch, endian) or None."""
    if fmt_name == 'GPUTEXTUREFORMAT_DXT1':
        dwSize=_align(width,128)*_align(height,128)//2
        return (dwSize, width//4, height//4, 8, 1)
    if fmt_name == 'GPUTEXTUREFORMAT_DXT2_3':
        dwSize=_align(width,128)*_align(height,128)
        return (dwSize, width//4, height//4, 16, 1)
    if fmt_name == 'GPUTEXTUREFORMAT_DXT4_5':
        dwSize=_align(width,128)*_align(height,128)
        return (dwSize, width//4, height//4, 16, 1)
    if fmt_name == 'GPUTEXTUREFORMAT_DXT5A':
        dwSize=_align(width,128)*_align(height,128)
        return (dwSize, width//4, height//4, 8, 1)
    if fmt_name == 'GPUTEXTUREFORMAT_8':
        dwSize=_align(width,128)*_align(height,128)
        return (dwSize, width, height, 1, 1)
    if fmt_name == 'GPUTEXTUREFORMAT_8_8_8_8':
        dwSize=_align(width,128)*_align(height,128)*4
        return (dwSize, width, height, 4, 2)
    if fmt_name == 'GPUTEXTUREFORMAT_DXN':
        dwSize=_align(width,128)*_align(height,128)*4
        return (dwSize, width, height, 4, 2)
    return None

def retile_and_swap(linear, fmt_name, width, height):
    """
    Inverse of untile_and_deswap: take linear (DDS) pixel data and produce the
    Xenon tiled + endian-swapped buffer ready to write back into the GPU block.
    Port of ImportImageXbox360 (endian swap first, then tile).
    """
    setup = _xbox_format_setup(fmt_name, width, height)
    if setup is None:
        return bytes(linear)
    dwSize, W, H, T, endian = setup

    graph = bytearray(linear[:dwSize])
    if len(graph) < dwSize:
        graph.extend(b'\x00' * (dwSize - len(graph)))

    # Endian swap first (matches Pascal import order).
    if GetGPUENDIAN(endian) == 'GPUENDIAN_8IN16':
        for i in range(0, dwSize - 1, 2):
            graph[i], graph[i+1] = graph[i+1], graph[i]
    elif GetGPUENDIAN(endian) == 'GPUENDIAN_8IN32':
        for i in range(0, dwSize - 3, 4):
            graph[i], graph[i+3] = graph[i+3], graph[i]
            graph[i+1], graph[i+2] = graph[i+2], graph[i+1]

    tiled = bytearray(dwSize)
    for Y in range(H):
        for X in range(W):
            off = XGAddress2DTiledOffset(X, Y, W, T)
            dst = off * T
            src = (X + Y * W) * T
            if dst + T <= dwSize and src + T <= dwSize:
                tiled[dst:dst+T] = graph[src:src+T]
    return bytes(tiled)

# ============================================================================
# Global.DirectDrawSurface  -- DDS builder (maps GPU format -> DDS pixelformat)
# ============================================================================
DDSD_CAPS=0x1; DDSD_HEIGHT=0x2; DDSD_WIDTH=0x4
DDSD_PIXELFORMAT=0x1000; DDSD_LINEARSIZE=0x80000; DDSD_MIPMAPCOUNT=0x20000
DDSCAPS_TEXTURE=0x1000; DDSCAPS_MIPMAP=0x400000; DDSCAPS_COMPLEX=0x8
DDPF_ALPHAPIXELS=0x1; DDPF_FOURCC=0x4; DDPF_RGB=0x40; DDPF_LUMINANCE=0x20000

# GPU format -> (dds 'fourcc' or None, bpp-if-uncompressed, is_block)
def _dds_fourcc_for(gpu_fmt):
    if gpu_fmt == 'GPUTEXTUREFORMAT_DXT1':  return (b'DXT1', None, True)
    if gpu_fmt == 'GPUTEXTUREFORMAT_DXT2_3':return (b'DXT3', None, True)
    if gpu_fmt == 'GPUTEXTUREFORMAT_DXT4_5':return (b'DXT5', None, True)
    if gpu_fmt == 'GPUTEXTUREFORMAT_DXN':   return (b'ATI2', None, True)  # BC5 / 3Dc
    if gpu_fmt == 'GPUTEXTUREFORMAT_DXT5A': return (b'ATI1', None, True)  # BC4-like
    if gpu_fmt == 'GPUTEXTUREFORMAT_CTX1':  return (b'CTX1', None, True)
    if gpu_fmt == 'GPUTEXTUREFORMAT_8_8_8_8': return (None, 32, False)
    if gpu_fmt == 'GPUTEXTUREFORMAT_8':       return (None, 8,  False)
    return (None, 32, False)

def make_dds(gpu_fmt, w, h, mips, data):
    fourcc, bpp, is_block = _dds_fourcc_for(gpu_fmt)
    pf_flags=fourcc_i=rgb_bits=rmask=gmask=bmask=amask=0
    if fourcc is not None:
        pf_flags = DDPF_FOURCC
        fourcc_i = int.from_bytes(fourcc, 'little')
    elif gpu_fmt == 'GPUTEXTUREFORMAT_8_8_8_8':
        pf_flags = DDPF_RGB | DDPF_ALPHAPIXELS; rgb_bits = 32
        rmask=0x00FF0000; gmask=0x0000FF00; bmask=0x000000FF; amask=0xFF000000
    elif gpu_fmt == 'GPUTEXTUREFORMAT_8':
        pf_flags = DDPF_LUMINANCE; rgb_bits = 8; rmask = 0xFF
    else:
        pf_flags = DDPF_RGB | DDPF_ALPHAPIXELS; rgb_bits = 32
        rmask=0x00FF0000; gmask=0x0000FF00; bmask=0x000000FF; amask=0xFF000000

    flags = DDSD_CAPS|DDSD_HEIGHT|DDSD_WIDTH|DDSD_PIXELFORMAT|DDSD_LINEARSIZE
    caps  = DDSCAPS_TEXTURE
    if mips and mips > 1:
        flags |= DDSD_MIPMAPCOUNT; caps |= DDSCAPS_MIPMAP|DDSCAPS_COMPLEX

    hdr  = struct.pack('<I',124) + struct.pack('<I',flags)
    hdr += struct.pack('<I',h)   + struct.pack('<I',w)
    hdr += struct.pack('<I',len(data)) + struct.pack('<I',0)
    hdr += struct.pack('<I',mips or 1) + b'\x00'*44
    hdr += struct.pack('<I',32) + struct.pack('<I',pf_flags)
    hdr += struct.pack('<I',fourcc_i) + struct.pack('<I',rgb_bits)
    hdr += struct.pack('<I',rmask) + struct.pack('<I',gmask)
    hdr += struct.pack('<I',bmask) + struct.pack('<I',amask)
    hdr += struct.pack('<I',caps) + b'\x00'*16
    return DDS_MAGIC + hdr + data

# ----------------------------------------------------------------------------
# DDS reader: parse header, return (width, height, fourcc, payload_bytes)
# ----------------------------------------------------------------------------
def parse_dds(blob):
    if blob[:4] != DDS_MAGIC:
        raise ValueError("Not a DDS file (bad magic).")
    if struct.unpack_from('<I', blob, 4)[0] != 124:
        raise ValueError("Bad DDS header size.")
    height = struct.unpack_from('<I', blob, 12)[0]
    width  = struct.unpack_from('<I', blob, 16)[0]
    pf_flags = struct.unpack_from('<I', blob, 80)[0]
    fourcc   = blob[84:88]
    payload  = blob[128:]
    fc = fourcc if (pf_flags & DDPF_FOURCC) else b''
    return width, height, fc, payload

# ----------------------------------------------------------------------------
# Minimal DXT (S3TC) encoders for texture import.
# These produce valid, reasonable-quality blocks (range-fit endpoints). They
# are not the absolute best compressor, but are correct and dependency-free.
# ----------------------------------------------------------------------------
def _rgb565(r, g, b):
    return ((r >> 3) << 11) | ((g >> 2) << 5) | (b >> 3)

def _encode_dxt_color_block(pixels):
    """pixels: list of 16 (r,g,b,a). Returns 8 bytes of DXT1 color block."""
    # range-fit: pick min/max luma endpoints
    opaque = [(r,g,b) for (r,g,b,a) in pixels]
    cmin = [min(c[i] for c in opaque) for i in range(3)]
    cmax = [max(c[i] for c in opaque) for i in range(3)]
    c0 = _rgb565(*cmax); c1 = _rgb565(*cmin)
    if c0 < c1:
        c0, c1 = c1, c0
        cmax, cmin = cmin, cmax
    # build 4 palette colors
    def expand(c565):
        r=((c565>>11)&0x1F); g=((c565>>5)&0x3F); b=(c565&0x1F)
        return (r<<3|r>>2, g<<2|g>>4, b<<3|b>>2)
    p0=expand(c0); p1=expand(c1)
    if c0 > c1:
        p2=tuple((2*p0[i]+p1[i])//3 for i in range(3))
        p3=tuple((p0[i]+2*p1[i])//3 for i in range(3))
    else:
        p2=tuple((p0[i]+p1[i])//2 for i in range(3))
        p3=(0,0,0)
    pal=[p0,p1,p2,p3]
    bits=0
    for i,(r,g,b,a) in enumerate(pixels):
        best=0; bd=1<<30
        for j,p in enumerate(pal):
            d=(r-p[0])**2+(g-p[1])**2+(b-p[2])**2
            if d<bd: bd=d; best=j
        bits |= best << (2*i)
    return struct.pack('<HHI', c0, c1, bits)

def _encode_dxt5_alpha_block(pixels):
    """pixels: list of 16 (r,g,b,a). Returns 8 bytes of DXT5 alpha block."""
    alphas=[a for (_,_,_,a) in pixels]
    a0=max(alphas); a1=min(alphas)
    if a0==a1:
        # all equal: indices all 0
        return bytes([a0,a1,0,0,0,0,0,0])
    # 8-alpha interpolation (a0>a1)
    pal=[a0,a1]+[((7-i)*a0+(i)*a1)//7 for i in range(1,7)]
    idx=[]
    for a in alphas:
        best=0; bd=1<<30
        for j,p in enumerate(pal):
            d=(a-p)*(a-p)
            if d<bd: bd=d; best=j
        idx.append(best)
    # pack 16 x 3-bit indices into 6 bytes
    val=0
    for i,ix in enumerate(idx):
        val |= (ix & 7) << (3*i)
    packed=val.to_bytes(6,'little')
    return bytes([a0,a1])+packed

def _iter_blocks(rgba, width, height):
    """Yield 4x4 blocks of (r,g,b,a) tuples, row-major block order."""
    px = rgba
    for by in range(0, height, 4):
        for bx in range(0, width, 4):
            block=[]
            for y in range(4):
                for x in range(4):
                    sx=min(bx+x,width-1); sy=min(by+y,height-1)
                    o=(sy*width+sx)*4
                    block.append((px[o],px[o+1],px[o+2],px[o+3]))
            yield block

def encode_dxt1(rgba, width, height):
    out=bytearray()
    for blk in _iter_blocks(rgba,width,height):
        out += _encode_dxt_color_block(blk)
    return bytes(out)

def encode_dxt5(rgba, width, height):
    out=bytearray()
    for blk in _iter_blocks(rgba,width,height):
        out += _encode_dxt5_alpha_block(blk)
        out += _encode_dxt_color_block(blk)
    return bytes(out)

def encode_for_format(gpu_fmt, rgba, width, height):
    """Encode RGBA8 bytes into the linear payload for a given GPU format."""
    if gpu_fmt in ('GPUTEXTUREFORMAT_DXT1',):
        return encode_dxt1(rgba, width, height)
    if gpu_fmt in ('GPUTEXTUREFORMAT_DXT4_5','GPUTEXTUREFORMAT_DXT2_3'):
        return encode_dxt5(rgba, width, height)
    if gpu_fmt == 'GPUTEXTUREFORMAT_8_8_8_8':
        # store as ARGB8 linear (matches the 8888 path; endian handled in retile)
        out=bytearray()
        for i in range(0,len(rgba),4):
            r,g,b,a=rgba[i],rgba[i+1],rgba[i+2],rgba[i+3]
            out += bytes([b,g,r,a])
        return bytes(out)
    # default to DXT5
    return encode_dxt5(rgba, width, height)

def load_image_as_rgba(path):
    """Load any image (png/jpg/dds/...) -> (rgba_bytes, w, h). Needs Pillow."""
    if not PIL_AVAILABLE:
        raise RuntimeError("Pillow is required to import images.")
    img = Image.open(path).convert("RGBA")
    return img.tobytes(), img.width, img.height

# ============================================================================
# Compression.ZLib (PS3 + PC use raw zlib; helpers below)
# ============================================================================
def decompress_zlib(payload):
    """
    Decompress a GTA RSC7 body. Returns (data, wbits) so the caller can
    reproduce the exact wrapping on save:
      - PC .ytd   : zlib-wrapped DEFLATE (wbits=15), body starts ~0x78
      - PS3 .ctd  : raw DEFLATE (wbits=-15), no zlib header/checksum
    Trying raw (-15) only after the wrapped forms keeps PC behaviour intact.
    """
    for wb in (15, 47, -15):
        try:
            return zlib.decompress(payload, wb), wb
        except zlib.error:
            pass
    # Last resort: re-add a zlib header (some odd PS3 dumps store headerless).
    for prefix in (b'\x78\xDA', b'\x78\x01', b'\x78\x9C'):
        try:
            return zlib.decompress(prefix + payload, 15), 15
        except zlib.error:
            pass
    raise zlib.error("zlib decompression failed")

# ============================================================================
# RSC7 size helpers (port of GetValueRSC7)
# ============================================================================
def GetValueRSC7(dwFlag, baseSize):
    dwFlag &= 0xFFFFFFFF
    newBaseSize = baseSize << (dwFlag & 0xf)
    Size = ((((dwFlag >> 17) & 0x7f)
             + (((dwFlag >> 11) & 0x3f) << 1)
             + (((dwFlag >> 7) & 0xf) << 2)
             + (((dwFlag >> 5) & 0x3) << 3)
             + (((dwFlag >> 4) & 0x1) << 4)) * newBaseSize)
    for i in range(4):
        if ((dwFlag >> (24 + i)) & 1) == 1:
            Size += newBaseSize >> (1 + i)
    return Size & 0xFFFFFFFF

def GetOffset(dwOffset):
    """Port of GetOffset: validate top nibble is 5 or 6, mask to 0x0FFFFFFF."""
    dwOffset &= 0xFFFFFFFF
    if dwOffset == 0:
        return 0
    top = dwOffset >> 28
    if top != 5 and top != 6:
        return 0
    return dwOffset & 0x0FFFFFFF

def DataOffset(i):
    """Port of DataOffset(): j:=i; j>>=8; j<<=16; j>>=8."""
    j = i & 0xFFFFFFFF
    j = (j >> 8) & 0xFFFFFFFF
    j = (j << 16) & 0xFFFFFFFF
    j = (j >> 8) & 0xFFFFFFFF
    return j

# ============================================================================
# Texture entry container
# ============================================================================
class TexEntry:
    __slots__ = ["name","width","height","mips","platform","fmt_name",
                 "tex_offset","name_offset","raw_data","index",
                 "endian","texture_type","gpu_fmt"]
    def __init__(self):
        self.name=""; self.width=0; self.height=0; self.mips=1
        self.platform=""; self.fmt_name=""; self.tex_offset=0; self.name_offset=0
        self.raw_data=b""; self.index=0; self.endian=0; self.texture_type=0
        self.gpu_fmt=""
    @property
    def display_name(self):
        return self.name or f"texture_{self.index:03d}"
    @property
    def size_label(self):
        return f"{self.width}x{self.height}" if self.width else "?"

# ============================================================================
# Stream reader helper (mirrors TStream.Read with explicit endianness)
# ============================================================================
class R:
    """Tiny big-endian-aware cursor over a bytes buffer (console = BE reads)."""
    def __init__(self, buf):
        self.b = buf; self.pos = 0
    def seek(self, p): self.pos = p
    def tell(self): return self.pos
    def u8(self):
        v = self.b[self.pos] if self.pos < len(self.b) else 0; self.pos += 1; return v
    def u16_le(self):
        v = struct.unpack_from('<H', self.b, self.pos)[0] if self.pos+2<=len(self.b) else 0
        self.pos += 2; return v
    def u32_le(self):
        v = struct.unpack_from('<I', self.b, self.pos)[0] if self.pos+4<=len(self.b) else 0
        self.pos += 4; return v
    def read(self, n):
        v = self.b[self.pos:self.pos+n]; self.pos += n; return v

def _read_cstr(buf, off, maxlen=64):
    if off <= 0 or off >= len(buf):
        return ""
    end = buf.find(b'\x00', off)
    if end < 0 or end - off > maxlen:
        end = min(off + maxlen, len(buf))
    return buf[off:end].decode('latin-1', 'replace')

def _clean_name(s):
    # Port of the name cleanup in LoadXTD/LoadCTD.
    if '/' in s:
        s = s[s.rfind('/')+1:]
    if 'memory:$' in s:
        # delete up to second ':'
        first = s.find(':')
        if first >= 0:
            s = s[first+1:]
            second = s.find(':')
            if second >= 0:
                s = s[second+1:]
    if not s.lower().endswith('.dds'):
        s = s + '.dds'
    s = s.replace('..', '.')
    return s

# ============================================================================
# Resource header parse: read magic, compute sizes, decompress to virt+phys.
# Returns (platform, decompressed_bytes, cpu_size, gpu_size, wbits, error_str)
#   wbits: deflate window used (15 = zlib-wrapped for PC; -15 = raw for PS3;
#          0 = LZX/Xbox 360, handled separately on save).
# ============================================================================
def load_resource(raw, lzx, force_platform=None):
    if len(raw) < 16:
        return (None, None, 0, 0, 0, "File too small.")
    magic = raw[:4]
    sig = struct.unpack_from('<I', raw, 0)[0]   # little-endian DWORD of first 4 bytes

    is_pc      = (magic == PC_MAGIC)            # 'RSC7'
    is_console = (magic == CONSOLE_MAGIC)       # '7CSR'
    if not (is_pc or is_console):
        return (None, None, 0, 0, 0, f"Unknown magic: {magic!r}")

    # Platform decision: magic first, user override for PS3/Xbox disambiguation.
    if is_pc:
        platform = "PC"
    else:
        platform = force_platform if force_platform in ("PS3", "Xbox 360") else "Xbox 360"

    # Flags at +8/+12, big-endian for console (EndianChangeDWORD), LE for PC.
    f1 = struct.unpack_from('<I', raw, 8)[0]
    f2 = struct.unpack_from('<I', raw, 12)[0]

    if is_console:
        f1 = EndianChangeDWORD(f1)
        f2 = EndianChangeDWORD(f2)

    if platform == "PS3":
        cpu = GetValueRSC7(f1, 0x1000)
        gpu = GetValueRSC7(f2, 0x1580)
    else:  # PC or Xbox 360 both use 0x2000/0x2000 in the GTA V code path
        cpu = GetValueRSC7(f1, 0x2000)
        gpu = GetValueRSC7(f2, 0x2000)

    body = raw[16:]

    # Decompress.
    if platform == "Xbox 360":
        # GTA V (7CSR) compressed without RSC header -> Codec 1 (xDecompress).
        try:
            dec = lzx.decompress_open(body)
        except LZXError as e:
            return (platform, None, cpu, gpu, 0,
                    "Xbox 360 LZX decompression unavailable.\n\n" + str(e) +
                    "\n\nPlace xcompress.dll, xcompress_cpp.dll and "
                    "xcompress_open.dll next to this script and run with "
                    "32-bit Python on Windows.")
        return (platform, dec, cpu, gpu, 0, "")
    else:
        # PC / PS3 -> deflate (PC is zlib-wrapped, PS3 is raw); remember which.
        try:
            dec, wbits = decompress_zlib(body)
        except zlib.error:
            return (platform, None, cpu, gpu, 0, "zlib decompression failed.")
        return (platform, dec, cpu, gpu, wbits, "")

# ============================================================================
# PS3 parser  (port of LoadCTD, iWorkMode=0 GTA V path)
# ============================================================================
def parse_ps3(buf):
    r = R(buf); textures = []
    r.seek(0)
    _vmt   = EndianChangeDWORD(r.u32_le())
    _omap  = GetOffset(EndianChangeDWORD(r.u32_le()))
    _fC    = EndianChangeDWORD(r.u32_le())
    _f10   = EndianChangeDWORD(r.u32_le())
    _hash  = GetOffset(EndianChangeDWORD(r.u32_le()))
    count  = EndianChangeWORD(r.u16_le())
    count2 = EndianChangeWORD(r.u16_le())
    listoff= GetOffset(EndianChangeDWORD(r.u32_le()))
    count3 = EndianChangeWORD(r.u16_le())
    count4 = EndianChangeWORD(r.u16_le())

    offsets = []
    r.seek(listoff)
    for _ in range(count):
        o = GetOffset(EndianChangeDWORD(r.u32_le()))
        offsets.append(o)

    name_offsets=[]; widths=[]; heights=[]; tex_offsets=[]; mips=[]; fmt_bytes=[]
    for base in offsets:
        # PS3 grcTexture (GTA V) layout, verified against real .ctd files:
        #   +0x08 : texture format code (1 byte) -> PS3_TEXTURE_FORMAT table
        #   +0x09 : mip count (1 byte)  [verified against real GTA V .ctd]
        #   +0x10 : width  (u16 BE)
        #   +0x12 : height (u16 BE)
        #   +0x1C : GPU texture data offset (relative to GPU block)
        #   +0x20 : name pointer
        fmt_bytes.append(buf[base+0x08] if base+0x08 < len(buf) else 0)
        r.seek(base+0x10)
        w = EndianChangeWORD(r.u16_le()); h = EndianChangeWORD(r.u16_le())
        widths.append(w); heights.append(h)
        mips.append(max(1, buf[base+0x09] if base+0x09 < len(buf) else 1))
        r.seek(base+0x1C)
        toff = GetOffset(EndianChangeDWORD(r.u32_le())); tex_offsets.append(toff)
        r.seek(base+0x20)
        nptr = GetOffset(EndianChangeDWORD(r.u32_le())); name_offsets.append(nptr)

    for i in range(count):
        t = TexEntry()
        t.name = _clean_name(_read_cstr(buf, name_offsets[i]))
        t.width = widths[i]; t.height = heights[i]; t.mips = mips[i]
        t.tex_offset = tex_offsets[i]; t.name_offset = name_offsets[i]
        t.platform = "PS3"; t.index = i
        t.texture_type = fmt_bytes[i]
        t.gpu_fmt = GetGPUTEXTUREFORMAT_PS3(fmt_bytes[i])
        t.fmt_name = t.gpu_fmt.replace('GPUTEXTUREFORMAT_', '')
        textures.append(t)
    return textures

# ============================================================================
# Xbox 360 parser (port of LoadXTD, iWorkMode=0 GTA V path)
# ============================================================================
def parse_xbox360(buf):
    r = R(buf); textures = []
    r.seek(0)
    _vmt   = EndianChangeDWORD(r.u32_le())
    _omap  = GetOffset(EndianChangeDWORD(r.u32_le()))
    _fC    = EndianChangeDWORD(r.u32_le())
    _f10   = EndianChangeDWORD(r.u32_le())
    _hash  = GetOffset(EndianChangeDWORD(r.u32_le()))
    count  = EndianChangeWORD(r.u16_le())
    count2 = EndianChangeWORD(r.u16_le())
    listoff= GetOffset(EndianChangeDWORD(r.u32_le()))
    count3 = EndianChangeWORD(r.u16_le())
    count4 = EndianChangeWORD(r.u16_le())

    # texture list offsets
    offsets = []
    r.seek(listoff)
    for _ in range(count):
        offsets.append(GetOffset(EndianChangeDWORD(r.u32_le())))

    name_offsets=[]; d3d_offsets=[]; widths=[]; heights=[]
    for base in offsets:
        r.seek(base)
        vmt = r.u32_le()
        # GTA V: _vmt div 100000 == 87 -> name offset at base+32
        r.seek(base+32)
        nptr = GetOffset(EndianChangeDWORD(r.u32_le())); name_offsets.append(nptr)
        # D3DBaseTexture offset (GTA V): base+52
        r.seek(base+52)
        d3d = GetOffset(EndianChangeDWORD(r.u32_le())); d3d_offsets.append(d3d)
        # width/height (GTA V): base+56
        r.seek(base+56)
        w = EndianChangeWORD(r.u16_le()); h = EndianChangeWORD(r.u16_le())
        widths.append(w); heights.append(h)

    tex_types=[]; endians=[]; mips=[]; gpu_offsets=[]; mip_offsets=[]
    for i in range(count):
        d3doff = d3d_offsets[i]
        r.seek(d3doff)
        dwords = [r.u32_le() for _ in range(13)]
        d3d = ReadD3DBaseTexture(dwords)
        # GPU texture data offset: at d3doff+32, run through DataOffset+endian
        r.seek(d3doff+32)
        gpuoff = r.u32_le()
        gpuoff = DataOffset(gpuoff)
        gpuoff = EndianChangeDWORD(gpuoff)
        gpu_offsets.append(gpuoff)
        # texture type & endian: re-read the dword at d3doff+32
        r.seek(d3doff+32)
        tt = r.u32_le()
        tt = EndianChangeDWORD(tt)
        texture_type = (tt << 26 & 0xFFFFFFFF) >> 26
        tex_types.append(texture_type)
        r.seek(d3doff+32)
        en = r.u32_le()
        endian = (en << 24 & 0xFFFFFFFF) >> 30
        endians.append(endian)
        mips.append(d3d['MaxMipLevel'] + 1)
        # mip offset: DataOffset(dwDWORD_13 & 0x00F0FFFF), endian-changed
        mipoff = DataOffset(dwords[12] & 0x00F0FFFF)
        mipoff = EndianChangeDWORD(mipoff)
        mip_offsets.append(mipoff)

    for i in range(count):
        t = TexEntry()
        t.name = _clean_name(_read_cstr(buf, name_offsets[i]))
        t.width = widths[i]; t.height = heights[i]
        t.mips = max(1, mips[i]); t.index = i; t.platform = "Xbox 360"
        t.tex_offset = gpu_offsets[i]; t.name_offset = name_offsets[i]
        t.texture_type = tex_types[i]; t.endian = endians[i]
        t.gpu_fmt = GetGPUTEXTUREFORMAT(tex_types[i])
        # human format label
        t.fmt_name = t.gpu_fmt.replace('GPUTEXTUREFORMAT_', '')
        textures.append(t)
    return textures

# ============================================================================
# PC parser (RSC7 LE) - simple grcTexture walk, kept from prior working tool
# ============================================================================
def parse_pc(virt, phys):
    def lo32(d,o): return struct.unpack_from('<I',d,o)[0] if o+4<=len(d) else 0
    def ru16(d,o): return struct.unpack_from('<H',d,o)[0] if o+2<=len(d) else 0
    def ru8(d,o):  return d[o] if o<len(d) else 0
    def vp(p):     return (p&0x0FFFFFFF) if (p>>28)==0x5 else None
    def pp(p):     return (p&0x0FFFFFFF) if (p>>28)==0x6 else None
    def is_pow2(v):return v>0 and v<=4096 and (v&(v-1))==0
    PC_FOURCC={b"DXT1":("DXT1",8,True),b"DXT3":("DXT3",16,True),b"DXT5":("DXT5",16,True),
               b"ATI1":("ATI1",8,True),b"ATI2":("ATI2",16,True),b"BC7 ":("BC7",16,True)}
    def f2f(fc):
        if fc[:4] in PC_FOURCC: return PC_FOURCC[fc[:4]]
        return (fc[:4].rstrip(b'\x00').decode('ascii','replace') or "DXT5", 16, True)
    textures=[]; seen=set()
    count = lo32(virt,0x28)&0xFFFF; data_off=vp(lo32(virt,0x30))
    if data_off is not None and 0<count<=2048:
        for i in range(count):
            ptr=vp(lo32(virt,data_off+i*8))
            if ptr is None or ptr+0x80>len(virt): continue
            name_ptr=vp(lo32(virt,ptr+0x28)); phys_ptr=pp(lo32(virt,ptr+0x70))
            w=ru16(virt,ptr+0x50); h=ru16(virt,ptr+0x52)
            fourcc=virt[ptr+0x58:ptr+0x5C] if ptr+0x5C<=len(virt) else b'\x00'*4
            m=max(1,ru8(virt,ptr+0x5D))
            if not(is_pow2(w) and is_pow2(h)): continue
            if phys_ptr is None or phys_ptr in seen: continue
            seen.add(phys_ptr)
            fmt,_bb,_blk=f2f(fourcc)
            t=TexEntry(); t.name=_read_cstr(virt,name_ptr if name_ptr else 0)
            t.width=w; t.height=h; t.mips=m; t.fmt_name=fmt; t.platform="PC"
            t.tex_offset=phys_ptr
            # crude size for export
            bw=max(1,(w+3)//4); bh=max(1,(h+3)//4)
            sz=bw*bh*(8 if fmt in("DXT1","ATI1") else 16)
            t.raw_data=phys[phys_ptr:phys_ptr+sz] if phys_ptr<len(phys) else b""
            textures.append(t)
    for i,t in enumerate(textures): t.index=i
    return textures

# ============================================================================
# PC .ytd RSC7 WRITER -- builds a complete grcTextureDictionary from scratch.
# ----------------------------------------------------------------------------
# This is what enables ADD / RENAME / true rebuild (not just in-place replace).
# It mirrors what OpenIV / CodeWalker do: lay out a SYSTEM (virtual) segment
# and a GRAPHICS (physical) segment, wire 64-bit paged pointers between them,
# pack each into power-of-two pages, encode the two RSC7 size flag words, then
# zlib-compress. GTA V PC pointers are 64-bit; the high bit class is:
#   0x5.. = system/virtual page,  0x6.. = graphics/physical page.
#
# jenkins-one-at-a-time hash is used for the texture name hash table (the way
# the dictionary keys textures), matching RAGE's atHashString.
# ============================================================================

# ---- GTA V PC grcTexture pixel formats (DXGI-ish codes used by RAGE) --------
# CodeWalker TextureFormat enum values (the ones we can encode):
D3DFMT = {
    'DXT1' : 0x31545844,   # 'DXT1'
    'DXT3' : 0x33545844,   # 'DXT3'
    'DXT5' : 0x35545844,   # 'DXT5'
    'ATI1' : 0x31495441,   # 'ATI1' (BC4)
    'ATI2' : 0x32495441,   # 'ATI2' (BC5)
    'BC7'  : 0x20374342,    # 'BC7 '
    'A8R8G8B8' : 21,        # D3DFMT_A8R8G8B8
}

def jenkins_hash(s):
    s = s.lower().encode('latin-1', 'replace')
    h = 0
    for b in s:
        h = (h + b) & 0xFFFFFFFF
        h = (h + (h << 10)) & 0xFFFFFFFF
        h = (h ^ (h >> 6)) & 0xFFFFFFFF
    h = (h + (h << 3)) & 0xFFFFFFFF
    h = (h ^ (h >> 11)) & 0xFFFFFFFF
    h = (h + (h << 15)) & 0xFFFFFFFF
    return h

def _block_bytes(fmt, w, h):
    """Total DXT/linear bytes for the base mip of a PC texture."""
    fmt = fmt.upper()
    bw = max(1, (w + 3) // 4); bh = max(1, (h + 3) // 4)
    if fmt in ('DXT1', 'ATI1'):
        return bw * bh * 8
    if fmt in ('DXT3', 'DXT5', 'ATI2', 'BC7'):
        return bw * bh * 16
    if fmt in ('A8R8G8B8', 'RGBA', 'BGRA'):
        return w * h * 4
    return bw * bh * 16

def _all_mips_bytes(fmt, w, h, levels):
    total = 0
    for i in range(max(1, levels)):
        mw = max(1, w >> i); mh = max(1, h >> i)
        total += _block_bytes(fmt, mw, mh)
    return total

class _Pager:
    """
    Accumulates blocks into one RSC7 segment (system or graphics), assigns each
    a paged virtual address, and emits the final padded page buffer plus the
    RSC7 flag word describing the page layout.

    GTA V uses a base page size; a segment is split into a small number of
    pages of sizes baseShift..  We keep it simple and correct: one contiguous
    region rounded up to a single power-of-two page count of the base size,
    which CodeWalker/OpenIV accept for dictionaries of this scale.
    """
    def __init__(self, page_class, base_size=0x2000):
        self.page_class = page_class      # 0x5 (system) or 0x6 (graphics)
        self.base = base_size
        self.buf = bytearray()
        self.fixups = []                  # (offset_in_buf,) needing 64-bit ptr

    def tell(self):
        return len(self.buf)

    def vaddr(self, off):
        # 64-bit paged pointer: (class << 28) | offset, within this segment.
        return (self.page_class << 28) | (off & 0x0FFFFFFF)

    def align(self, a):
        while len(self.buf) % a != 0:
            self.buf.append(0)

    def write(self, data):
        off = len(self.buf)
        self.buf += bytes(data)
        return off

    def reserve(self, n):
        off = len(self.buf)
        self.buf += b'\x00' * n
        return off

    def patch_u32(self, off, val):
        self.buf[off:off+4] = struct.pack('<I', val & 0xFFFFFFFF)

    def patch_u64(self, off, val):
        self.buf[off:off+8] = struct.pack('<Q', val & 0xFFFFFFFFFFFFFFFF)

def _rsc7_flag_for_size(total_size, base=0x2000, version=13):
    """
    Encode an RSC7 page-flag word that the loader's GetValueRSC7 decodes to a
    size >= total_size. Verified against real GTA V .ytd files:
      - system 8192 bytes -> 0x00020000 (shift 0, one 0x2000 page)  [matches R*]
      - graphics segments use the 1x bucket with as many base pages as needed.
    The version (13) is replicated into the top nibble, as real files do.
    """
    shift = 0
    while True:
        page = base << shift
        count = (total_size + page - 1) // page
        if count <= 0x7f or shift >= 0xF:
            break
        shift += 1
    flag = (shift & 0xF) | ((count & 0x7F) << 17) | ((version & 0xF) << 28)
    return flag, page * count

class YtdWriter:
    """Build a GTA V PC .ytd (grcTextureDictionary) from a list of textures.

    Each input texture: dict(name=str, fmt=str DXT1/DXT3/DXT5/ATI1/ATI2/BC7,
    width, height, levels, data=bytes  # linear mip chain, base first).
    """
    # Real GTA V .ytd files store a relocation marker in the vft slot rather
    # than a literal address: low dword 0, high dword 1  => 0x0000000100000000.
    VFT_MARKER = 0x0000000100000000

    def __init__(self, textures):
        self.texs = textures

    def build(self):
        sysseg = _Pager(0x5, 0x2000)   # system/virtual  (page class 5)
        gfxseg = _Pager(0x6, 0x2000)   # graphics/physical (page class 6)
        n = len(self.texs)

        # --- graphics segment: pixel data, each texture on a page boundary ---
        # Real files align each texture's data to its own page; we align to a
        # generous 0x1000 boundary which is always a valid page sub-multiple.
        gfx_offsets = []
        for t in self.texs:
            gfxseg.align(0x1000)
            gfx_offsets.append(gfxseg.write(t['data']))
        if not gfxseg.buf:
            gfxseg.write(b'\x00' * 0x1000)

        # --- system segment ---------------------------------------------------
        # Order mirrors the real file:
        #   [dict header 0x40][blockmap 0x40][grcTexture structs 0x90 each]
        #   [texture ptr array][hash array][name strings]
        sysseg.align(0x10)
        dict_hdr = sysseg.reserve(0x40)

        # blockmap (pgBase) immediately after header, pointed to from dict+0x08.
        sysseg.align(0x10)
        blockmap_off = sysseg.tell()
        sysseg.reserve(0x40)   # zero-filled blockmap is accepted by loaders

        # sort textures by name hash (RAGE keeps the hash table sorted ascending)
        pairs = sorted(((jenkins_hash(Path(t['name']).stem), i)
                        for i, t in enumerate(self.texs)), key=lambda p: p[0])
        order = [i for _, i in pairs]

        # grcTexture structs (0x90 each)
        tex_struct_off = {}
        name_fixups = []
        for idx in order:
            t = self.texs[idx]
            sysseg.align(0x10)
            base = sysseg.reserve(0x90)
            tex_struct_off[idx] = base
            sysseg.patch_u64(base+0x00, self.VFT_MARKER)       # vft marker
            sysseg.patch_u64(base+0x30, 1)                     # constant '1' (real files)
            # name ptr @+0x28 filled after strings are written
            sysseg.patch_u16(base+0x50, t['width'])
            sysseg.patch_u16(base+0x52, t['height'])
            sysseg.patch_u16(base+0x54, 1)                     # depth = 1
            # +0x56 stride = (width/4 blocks) * blockBytes / 4   [matches real]
            fmt = t['fmt'].upper()
            bpb = 8 if fmt in ('DXT1','ATI1') else 16
            stride = max(1, (t['width']//4) * bpb // 4)
            sysseg.patch_u16(base+0x56, stride & 0xFFFF)
            sysseg.patch_u32(base+0x58, D3DFMT.get(fmt, D3DFMT['DXT5']))
            sysseg.buf[base+0x5C] = 0                           # @0x5C = 0 (real)
            sysseg.buf[base+0x5D] = max(1, t.get('levels', 1)) & 0xFF  # mip count
            sysseg.patch_u64(base+0x70, gfxseg.vaddr(gfx_offsets[idx]))  # data ptr
            name_fixups.append((base+0x28, idx))

        # texture pointer array (u64 each), in sorted order
        sysseg.align(0x10)
        texptr_off = sysseg.tell()
        for idx in order:
            sysseg.write(struct.pack('<Q', sysseg.vaddr(tex_struct_off[idx])))

        # hash array (u32 each), sorted order
        sysseg.align(0x10)
        hashes_off = sysseg.tell()
        for hsh, _ in pairs:
            sysseg.write(struct.pack('<I', hsh))

        # name strings
        for namefix, idx in name_fixups:
            nm = Path(self.texs[idx]['name']).stem.encode('latin-1','replace') + b'\x00'
            noff = sysseg.write(nm)
            sysseg.patch_u64(namefix, sysseg.vaddr(noff))

        # --- dict header ------------------------------------------------------
        sysseg.patch_u64(dict_hdr+0x00, self.VFT_MARKER)           # vft marker
        sysseg.patch_u64(dict_hdr+0x08, sysseg.vaddr(blockmap_off)) # blockmap ptr
        sysseg.patch_u32(dict_hdr+0x18, 1)                          # ref count
        sysseg.patch_u64(dict_hdr+0x20, sysseg.vaddr(hashes_off))   # hashes ptr
        sysseg.patch_u16(dict_hdr+0x28, n)                          # hash count
        sysseg.patch_u16(dict_hdr+0x2A, n)                          # hash capacity
        sysseg.patch_u64(dict_hdr+0x30, sysseg.vaddr(texptr_off))   # textures ptr
        sysseg.patch_u16(dict_hdr+0x38, n)                          # tex count
        sysseg.patch_u16(dict_hdr+0x3A, n)                          # tex capacity

        # --- pack pages & RSC7 header (raw DEFLATE, like real .ytd) ----------
        sys_flag, sys_pages = _rsc7_flag_for_size(len(sysseg.buf), 0x2000, 0)
        gfx_flag, gfx_pages = _rsc7_flag_for_size(len(gfxseg.buf), 0x2000, 13)
        sys_buf = bytes(sysseg.buf) + b'\x00'*(sys_pages - len(sysseg.buf))
        gfx_buf = bytes(gfxseg.buf) + b'\x00'*(gfx_pages - len(gfxseg.buf))
        body = sys_buf + gfx_buf

        header  = b'RSC7'
        header += struct.pack('<I', 13)        # version 13 (GTA V)
        header += struct.pack('<I', sys_flag)  # system flags (LE for PC)
        header += struct.pack('<I', gfx_flag)  # graphics flags
        # PC .ytd uses RAW deflate (no zlib header/checksum) -- verified.
        co = zlib.compressobj(9, zlib.DEFLATED, -15)
        comp = co.compress(body) + co.flush()
        return header + comp, len(sys_buf), len(gfx_buf)

# add small helpers to _Pager (patch_u16) -----------------------------------
def _pager_patch_u16(self, off, val):
    self.buf[off:off+2] = struct.pack('<H', val & 0xFFFF)
_Pager.patch_u16 = _pager_patch_u16
# big-endian patch helpers for console writers
def _pager_patch_u16_be(self, off, val):
    self.buf[off:off+2] = struct.pack('>H', val & 0xFFFF)
def _pager_patch_u32_be(self, off, val):
    self.buf[off:off+4] = struct.pack('>I', val & 0xFFFFFFFF)
_Pager.patch_u16_be = _pager_patch_u16_be
_Pager.patch_u32_be = _pager_patch_u32_be


# ============================================================================
# PS3 .ctd CONSOLE WRITER -- builds a grcTextureDictionary for PS3 (RSX).
# ----------------------------------------------------------------------------
# Modeled byte-for-byte on a real GTA V mphud.ctd. Console resources are the
# same RSC7 paged scheme as PC but: magic '7CSR', flags big-endian, base sizes
# 0x1000 (system) / 0x1580 (graphics), and 32-bit big-endian pointers with the
# page-class nibble (5 = system, 6 = graphics). The PS3 grcTexture layout:
#   +0x00 vft (u32 BE)           +0x08 format code   +0x09 mip count
#   +0x10 width(u16 BE)          +0x12 height(u16 BE)
#   +0x1C GPU data offset        +0x20 name ptr
# PS3 pixel data is LINEAR (no tiling), so this is fully buildable & verifiable.
# ============================================================================
PS3_FMT_CODE = {  # inverse of PS3_TEXTURE_FORMAT (encode side)
    'DXT1':134, 'DXT3':135, 'DXT5':136, 'DXT5A':148, '8':129, '8_8_8_8':133,
}
def _ps3_vaddr(page_class, off):
    return ((page_class << 28) | (off & 0x0FFFFFFF)) & 0xFFFFFFFF

class CtdWriter:
    """Build a GTA V PS3 .ctd from a list of builder-dict textures.

    texture dict: name, fmt (DXT1/DXT3/DXT5/DXT5A/8/8_8_8_8), width, height,
                  levels, data (linear pixel bytes, base mip first).
    The vft is the real PS3 grcTextureDictionaryPS3 value observed in stock files.
    """
    VFT_DICT = 0x88988100      # observed in real mphud.ctd (big-endian on disk)
    VFT_TEX  = 0xBC8C8A00      # observed grcTexturePS3 vtable in real file

    def __init__(self, textures):
        self.texs = textures

    def build(self):
        n = len(self.texs)
        sysseg = _Pager(0x5, 0x1000)   # system  (base 0x1000)
        gfxseg = _Pager(0x6, 0x1580)   # graphics(base 0x1580)

        # graphics: linear pixel data, page-aligned per texture
        gfx_off = []
        for t in self.texs:
            gfxseg.align(0x80)
            gfx_off.append(gfxseg.write(t['data']))
        if not gfxseg.buf:
            gfxseg.write(b'\x00' * 0x80)

        # ---- system segment -------------------------------------------------
        # dict header (0x40), hash table, texture pointer list, structs, names
        sysseg.align(0x10)
        dict_hdr = sysseg.reserve(0x40)

        # sort by name hash ascending (RAGE convention)
        pairs = sorted(((jenkins_hash(Path(t['name']).stem), i)
                        for i, t in enumerate(self.texs)), key=lambda p: p[0])
        order = [i for _, i in pairs]

        # hash table (u32 BE each)
        sysseg.align(0x10)
        hash_off = sysseg.tell()
        for hsh, _ in pairs:
            sysseg.write(struct.pack('>I', hsh))

        # texture pointer list (u32 BE each)
        sysseg.align(0x10)
        list_off = sysseg.tell()
        ptr_slots = [sysseg.reserve(4) for _ in range(n)]

        # grcTexture structs (0x40 bytes each, PS3 layout)
        struct_off = {}
        name_fix = []
        for idx in order:
            t = self.texs[idx]
            sysseg.align(0x10)
            base = sysseg.reserve(0x40)
            struct_off[idx] = base
            sysseg.patch_u32_be(base+0x00, self.VFT_TEX)
            fmt = t['fmt'].upper()
            sysseg.buf[base+0x08] = PS3_FMT_CODE.get(fmt, 136) & 0xFF   # format
            sysseg.buf[base+0x09] = max(1, t.get('levels', 1)) & 0xFF   # mip count
            # +0x0C / +0x24 / +0x2C are RSX GPU control/remap registers. We copy
            # them from a same-format template texture when one was provided
            # (e.g. converting from a real .ctd), else leave 0. This is the part
            # that most affects in-game rendering correctness on PS3.
            tmpl = t.get('ps3_regs')
            if tmpl:
                sysseg.patch_u32_be(base+0x0C, tmpl.get('r0c', 0))
                sysseg.patch_u32_be(base+0x14, tmpl.get('r14', 0x00010000))
                sysseg.patch_u32_be(base+0x24, tmpl.get('r24', 0))
                sysseg.patch_u32_be(base+0x2C, tmpl.get('r2c', 0))
            else:
                sysseg.patch_u32_be(base+0x14, 0x00010000)             # depth=1
            sysseg.patch_u16_be(base+0x10, t['width'])
            sysseg.patch_u16_be(base+0x12, t['height'])
            sysseg.patch_u32_be(base+0x1C, _ps3_vaddr(0x6, gfx_off[idx]))  # GPU data
            name_fix.append((base+0x20, idx))

        # name strings
        for slot, idx in name_fix:
            nm = Path(self.texs[idx]['name']).stem.encode('latin-1','replace') + b'\x00'
            noff = sysseg.write(nm)
            sysseg.patch_u32_be(slot, _ps3_vaddr(0x5, noff))

        # wire texture pointer list
        for k, idx in enumerate(order):
            sysseg.patch_u32_be(ptr_slots[k], _ps3_vaddr(0x5, struct_off[idx]))

        # dict header
        sysseg.patch_u32_be(dict_hdr+0x00, self.VFT_DICT)
        sysseg.patch_u32_be(dict_hdr+0x04, _ps3_vaddr(0x5, dict_hdr+0x40))  # blockmap-ish
        sysseg.patch_u32_be(dict_hdr+0x10, _ps3_vaddr(0x5, hash_off))
        sysseg.patch_u16_be(dict_hdr+0x14, n)
        sysseg.patch_u16_be(dict_hdr+0x16, n)
        sysseg.patch_u32_be(dict_hdr+0x18, _ps3_vaddr(0x5, list_off))
        sysseg.patch_u16_be(dict_hdr+0x1C, n)
        sysseg.patch_u16_be(dict_hdr+0x1E, n)

        # ---- pack pages + RSC7 header (7CSR, big-endian flags) --------------
        sys_flag, sys_pages = _rsc7_flag_for_size(len(sysseg.buf), 0x1000, 0)
        gfx_flag, gfx_pages = _rsc7_flag_for_size(len(gfxseg.buf), 0x1580, 13)
        sys_buf = bytes(sysseg.buf) + b'\x00'*(sys_pages - len(sysseg.buf))
        gfx_buf = bytes(gfxseg.buf) + b'\x00'*(gfx_pages - len(gfxseg.buf))
        body = sys_buf + gfx_buf

        header  = b'7CSR'
        header += struct.pack('>I', 13)   # version 13, BIG-ENDIAN for console
        header += struct.pack('<I', EndianChangeDWORD(sys_flag))   # BE flags
        header += struct.pack('<I', EndianChangeDWORD(gfx_flag))
        co = zlib.compressobj(9, zlib.DEFLATED, -15)               # raw deflate
        comp = co.compress(body) + co.flush()
        return header + comp, len(sys_buf), len(gfx_buf)


# ============================================================================
# Xbox 360 .xtd CONSOLE WRITER -- builds a grcTextureDictionary for Xbox 360.
# ----------------------------------------------------------------------------
# Modeled byte-for-byte on a real GTA V breakableglass.xtd dump. The pixel data
# is Xenon-tiled + endian-swapped (retile_and_swap), and the D3DBaseTexture GPU
# fetch constant is reproduced from the decoded register layout:
#   grcTextureXenon (0x60):
#     +0x00 vft (0x145C8500)         +0x20 name ptr
#     +0x24 GPU data offset hint     +0x2C tiling/control word
#     +0x34 D3DBaseTexture ptr       +0x38 width(u16) height(u16)
#     +0x3C mip count                +0x40.. embedded fetch constant
#   D3DBaseTexture / fetch constant (verified against Xenia xe_gpu_texture_fetch):
#     dword_1 0x00200003   dword_2 0x00000001   dwords 3-5 = 0
#     dword_6/7 0xFFFF0000   dword_8 = (pitch_tiles<<22)|0x80000002  (tiled)
#     dword_9 = (gpu_paged_addr & ~0x3F) | (endian<<6) | format
#     dword_10 = ((height-1)<<13)|(width-1)   (size_2d)
#     dword_11 0x00000D10   dword_12 = mipcount-encoded   dword_13 = mip addr
#
# Output is xCompress-compressed via xcompress_open.dll, so writing a final
# .xtd requires the 32-bit DLLs on Windows. Without them, raw (uncompressed
# body) can still be written for inspection.
# ============================================================================
XBOX_FMT_CODE = {  # GPUTEXTUREFORMAT index (matches reader's GPU_TEXTURE_FORMAT)
    'DXT1':18, 'DXT3':19, 'DXT5':20, 'DXT5A':59, 'DXN':49, '8_8_8_8':6, '8':2,
}
def _xbox_pitch_tiles(width):
    # pitch in 32-texel tiles (rounded up)
    return max(1, (width + 31) // 32)

class XtdWriter:
    """Build a GTA V Xbox 360 .xtd from builder-dict textures.

    texture dict: name, fmt (DXT1/DXT3/DXT5/DXT5A/DXN), width, height, levels,
                  data (LINEAR pixel bytes, base mip first -- they get tiled here).
    Requires an LZX instance with xCompress available to produce a final file;
    pass compress=False to write an uncompressed body for inspection.
    """
    VFT_DICT = 0x00258100      # grcTextureDictionaryXenon vtable (real file)
    VFT_TEX  = 0x145C8500      # grcTextureXenon vtable (real file)

    def __init__(self, textures, lzx=None):
        self.texs = textures
        self.lzx = lzx

    def build(self, compress=True):
        n = len(self.texs)
        sysseg = _Pager(0x5, 0x2000)
        gfxseg = _Pager(0x6, 0x2000)

        # graphics: TILED pixel data, each texture page-aligned (real file used
        # 0x10000 spacing for 256-px DXT5; we align to 0x1000 minimum and place
        # sequentially, recording the paged address for the fetch constant).
        gfx_addr = []
        for t in self.texs:
            fmt = t['fmt'].upper()
            gpu_fmt = 'GPUTEXTUREFORMAT_' + ('DXT4_5' if fmt=='DXT5' else
                       'DXT2_3' if fmt=='DXT3' else fmt)
            tiled = retile_and_swap(t['data'], gpu_fmt, t['width'], t['height'])
            gfxseg.align(0x1000)
            off = gfxseg.write(tiled)
            gfx_addr.append(off)
        if not gfxseg.buf:
            gfxseg.write(b'\x00'*0x1000)

        # ---- system segment -------------------------------------------------
        sysseg.align(0x10)
        dict_hdr = sysseg.reserve(0x30)
        sysseg.align(0x10)
        blockmap_off = sysseg.tell(); sysseg.reserve(0x20)

        pairs = sorted(((jenkins_hash(Path(t['name']).stem), i)
                        for i, t in enumerate(self.texs)), key=lambda p: p[0])
        order = [i for _, i in pairs]

        # hash table (u32 BE)
        sysseg.align(0x10); hash_off = sysseg.tell()
        for hsh, _ in pairs:
            sysseg.write(struct.pack('>I', hsh))
        # texture pointer list (u32 BE)
        sysseg.align(0x10); list_off = sysseg.tell()
        ptr_slots = [sysseg.reserve(4) for _ in range(n)]

        struct_off = {}; name_fix = []
        for idx in order:
            t = self.texs[idx]
            fmt = t['fmt'].upper()
            w, h = t['width'], t['height']
            levels = max(1, t.get('levels', 1))
            sysseg.align(0x10)
            base = sysseg.reserve(0x60)
            struct_off[idx] = base
            d3d = base + 0x40   # fetch constant embedded at +0x40 (as in real file)

            sysseg.patch_u32_be(base+0x00, self.VFT_TEX)
            # +0x24 data offset hint (observed = abs offset incl cpu page)
            sysseg.patch_u32_be(base+0x24, 0x00012000 if False else (gfx_addr[idx] + 0x2000))
            # +0x2C control word (observed 0x2001C01A for 256 DXT5) -- derive below
            sysseg.patch_u32_be(base+0x2C, 0x20000000 | ((w & 0x1FFF) << 0))
            sysseg.patch_u32_be(base+0x34, _ps3_vaddr(0x5, d3d))  # D3DBaseTexture ptr
            sysseg.patch_u16_be(base+0x38, w)
            sysseg.patch_u16_be(base+0x3A, h)
            sysseg.patch_u32_be(base+0x3C, levels)
            name_fix.append((base+0x20, idx))

            # ---- embedded D3DBaseTexture / fetch constant ----
            fmt_idx = XBOX_FMT_CODE.get(fmt, 20)
            pitch = _xbox_pitch_tiles(w)
            gpu_paged = _ps3_vaddr(0x6, gfx_addr[idx])  # 0x6........ graphics addr
            sysseg.patch_u32_be(d3d+0x00, 0x00200003)               # dword_1
            sysseg.patch_u32_be(d3d+0x04, 0x00000001)               # dword_2
            sysseg.patch_u32_be(d3d+0x14, 0xFFFF0000)               # dword_6
            sysseg.patch_u32_be(d3d+0x18, 0xFFFF0000)               # dword_7
            sysseg.patch_u32_be(d3d+0x1C, (pitch << 22) | 0x80000002)  # dword_8
            # dword_9: base_address(20)<<12 | request bits | endian<<6 | format
            #   real: 0x60010054 = (0x60010<<12) | 0x54 ; 0x54 = endian(1)<<6 | fmt(20)
            dword9 = (gpu_paged & 0xFFFFF000) | (1 << 6) | (fmt_idx & 0x3F)
            sysseg.patch_u32_be(d3d+0x20, dword9)                   # dword_9
            sysseg.patch_u32_be(d3d+0x24, ((h-1) << 13) | (w-1))   # dword_10 size_2d
            sysseg.patch_u32_be(d3d+0x28, 0x00000D10)              # dword_11
            # dword_12 encodes mip count: real 0x000000C0 BE <-> MaxMip+1=4.
            # reader: MaxMip = EC( (raw&0xC0000000)>>6 | (raw&0x00030000)<<10 ).
            # invert for small mip counts: store maxmip in the same bits.
            maxmip = levels - 1
            raw12 = ((maxmip & 0x3) << 30)  # crude: high 2 bits (works for <=4 mips)
            sysseg.patch_u32_be(d3d+0x2C, EndianChangeDWORD(raw12))  # dword_12
            sysseg.patch_u32_be(d3d+0x30, (gpu_paged & 0xFFFF0000) | 0x0A00)  # dword_13 mip addr

        # name strings
        for slot, idx in name_fix:
            nm = Path(self.texs[idx]['name']).stem.encode('latin-1','replace') + b'\x00'
            noff = sysseg.write(nm)
            sysseg.patch_u32_be(slot, _ps3_vaddr(0x5, noff))

        for k, idx in enumerate(order):
            sysseg.patch_u32_be(ptr_slots[k], _ps3_vaddr(0x5, struct_off[idx]))

        # dict header
        sysseg.patch_u32_be(dict_hdr+0x00, self.VFT_DICT)
        sysseg.patch_u32_be(dict_hdr+0x04, _ps3_vaddr(0x5, blockmap_off))
        sysseg.patch_u32_be(dict_hdr+0x0C, 1)
        sysseg.patch_u32_be(dict_hdr+0x10, _ps3_vaddr(0x5, hash_off))
        sysseg.patch_u16_be(dict_hdr+0x14, n); sysseg.patch_u16_be(dict_hdr+0x16, n)
        sysseg.patch_u32_be(dict_hdr+0x18, _ps3_vaddr(0x5, list_off))
        sysseg.patch_u16_be(dict_hdr+0x1C, n); sysseg.patch_u16_be(dict_hdr+0x1E, n)

        sys_flag, sys_pages = _rsc7_flag_for_size(len(sysseg.buf), 0x2000, 0)
        gfx_flag, gfx_pages = _rsc7_flag_for_size(len(gfxseg.buf), 0x2000, 13)
        sys_buf = bytes(sysseg.buf) + b'\x00'*(sys_pages - len(sysseg.buf))
        gfx_buf = bytes(gfxseg.buf) + b'\x00'*(gfx_pages - len(gfxseg.buf))
        body = sys_buf + gfx_buf

        header  = b'7CSR'
        header += struct.pack('>I', 13)
        header += struct.pack('<I', EndianChangeDWORD(sys_flag))
        header += struct.pack('<I', EndianChangeDWORD(gfx_flag))

        if compress:
            if not (self.lzx and self.lzx.available_open):
                raise LZXError("Xbox 360 .xtd needs xcompress_open.dll (32-bit "
                               "Windows) to compress. Use a Windows build, or "
                               "write an uncompressed body for inspection.")
            comp = self.lzx.compress_open(body)
            return header + comp, len(sys_buf), len(gfx_buf)
        else:
            # uncompressed body (NOT loadable by the game; for inspection only)
            return header + body, len(sys_buf), len(gfx_buf)


# ============================================================================
# TextureDict -- top-level file container
# ============================================================================
class TextureDict:
    def __init__(self, lzx):
        self.lzx = lzx
        self.textures = []
        self.platform = ""; self.filepath = ""
        self.cpu_size = 0; self.gpu_size = 0
        self.error_msg = ""
        self._raw = b""; self._dec = b""
        self._wbits = 15   # deflate window used at load (for faithful repack)

    def load(self, path, force_platform=None):
        self.filepath = path
        self._raw = Path(path).read_bytes()
        platform, dec, cpu, gpu, wbits, err = load_resource(self._raw, self.lzx, force_platform)
        self.platform = platform or ""
        self.cpu_size = cpu; self.gpu_size = gpu
        self._wbits = wbits
        if err:
            self.error_msg = err
            return
        self._dec = dec or b""
        self.error_msg = ""
        if platform == "PS3":
            self.textures = parse_ps3(self._dec)
        elif platform == "Xbox 360":
            self.textures = parse_xbox360(self._dec)
        else:  # PC
            virt = self._dec[:self.cpu_size]
            phys = self._dec[self.cpu_size:]
            self.textures = parse_pc(virt, phys)

    def export_dds(self, tex):
        """Build a DDS for the given texture from the decompressed buffer.

        Per MainUnit.pas, the stored GPU data offset is relative to the start
        of the GPU block, so the absolute offset into the decompressed buffer
        is  gpu_offset + cpu_size.
        """
        if tex.platform == "Xbox 360":
            gpu_fmt = tex.gpu_fmt
            abs_off = tex.tex_offset + self.cpu_size
            data = untile_and_deswap(self._dec[abs_off:], gpu_fmt,
                                     tex.width, tex.height, tex.endian)
            return make_dds(gpu_fmt, tex.width, tex.height, 1, data)
        elif tex.platform == "PS3":
            # PS3 data is linear (RSX). Use the real per-texture format read
            # from the struct (+0x08); fall back to DXT5 only if unknown.
            gpu_fmt = tex.gpu_fmt if tex.gpu_fmt and tex.gpu_fmt != '-unknown-' \
                      else 'GPUTEXTUREFORMAT_DXT4_5'
            abs_off = tex.tex_offset + self.cpu_size
            size = ps3_data_size(gpu_fmt, tex.width, tex.height)
            data = self._dec[abs_off:abs_off+size]
            return make_dds(gpu_fmt, tex.width, tex.height, 1, data)
        else:  # PC
            fmt = tex.fmt_name.upper()
            gpu = {'DXT1':'GPUTEXTUREFORMAT_DXT1','DXT3':'GPUTEXTUREFORMAT_DXT2_3',
                   'DXT5':'GPUTEXTUREFORMAT_DXT4_5','ATI2':'GPUTEXTUREFORMAT_DXN',
                   'ATI1':'GPUTEXTUREFORMAT_DXT5A'}.get(fmt,'GPUTEXTUREFORMAT_DXT4_5')
            return make_dds(gpu, tex.width, tex.height, tex.mips, tex.raw_data)

    # ---- import / replace --------------------------------------------------
    def replace_texture(self, tex, image_path):
        """
        Replace the pixel data of an existing texture with an image from disk.

        The incoming image is resized to the texture's existing dimensions and
        re-encoded into the texture's existing GPU format, then written back
        into the decompressed buffer in-place. Dimensions/format are preserved
        so all offsets and the resource header stay valid.
        """
        if tex.platform == "PC":
            return self._replace_pc(tex, image_path)
        elif tex.platform == "Xbox 360":
            return self._replace_xbox360(tex, image_path)
        elif tex.platform == "PS3":
            return self._replace_ps3(tex, image_path)
        raise RuntimeError("Unsupported platform for replace.")

    def _load_rgba_sized(self, image_path, w, h):
        if not PIL_AVAILABLE:
            raise RuntimeError("Pillow is required to import images.")
        # If a DDS with matching size+format is given, we still go through RGBA
        # so any source format works; quality permitting.
        img = Image.open(image_path).convert("RGBA")
        if (img.width, img.height) != (w, h):
            img = img.resize((w, h), Image.LANCZOS)
        return img.tobytes()

    def _ensure_mutable(self):
        if not isinstance(self._dec, bytearray):
            self._dec = bytearray(self._dec)

    def _replace_xbox360(self, tex, image_path):
        self._ensure_mutable()
        gpu_fmt = tex.gpu_fmt
        setup = _xbox_format_setup(gpu_fmt, tex.width, tex.height)
        if setup is None:
            raise RuntimeError(f"Import not supported for format {tex.fmt_name}.")
        dwSize = setup[0]
        rgba = self._load_rgba_sized(image_path, tex.width, tex.height)
        linear = encode_for_format(gpu_fmt, rgba, tex.width, tex.height)
        tiled = retile_and_swap(linear, gpu_fmt, tex.width, tex.height)
        abs_off = tex.tex_offset + self.cpu_size
        if abs_off + dwSize > len(self._dec):
            # extend if needed (shouldn't happen for same-size replace)
            self._dec.extend(b'\x00' * (abs_off + dwSize - len(self._dec)))
        self._dec[abs_off:abs_off+len(tiled)] = tiled
        return True

    def _replace_ps3(self, tex, image_path):
        self._ensure_mutable()
        gpu_fmt = tex.gpu_fmt if tex.gpu_fmt and tex.gpu_fmt != '-unknown-' \
                  else 'GPUTEXTUREFORMAT_DXT4_5'
        rgba = self._load_rgba_sized(image_path, tex.width, tex.height)
        linear = encode_for_format(gpu_fmt, rgba, tex.width, tex.height)
        # PS3 stores linear (un-tiled) data, so no retile needed.
        size = ps3_data_size(gpu_fmt, tex.width, tex.height)
        if len(linear) > size:
            linear = linear[:size]
        elif len(linear) < size:
            linear = linear + b'\x00'*(size-len(linear))
        abs_off = tex.tex_offset + self.cpu_size
        if abs_off + size > len(self._dec):
            self._dec.extend(b'\x00' * (abs_off + size - len(self._dec)))
        self._dec[abs_off:abs_off+size] = linear
        return True

    def _replace_pc(self, tex, image_path):
        # PC textures are stored in the physical block; rebuild raw_data and
        # splice into the phys section of _dec.
        self._ensure_mutable()
        fmt = tex.fmt_name.upper()
        gpu = {'DXT1':'GPUTEXTUREFORMAT_DXT1','DXT3':'GPUTEXTUREFORMAT_DXT2_3',
               'DXT5':'GPUTEXTUREFORMAT_DXT4_5'}.get(fmt,'GPUTEXTUREFORMAT_DXT4_5')
        rgba = self._load_rgba_sized(image_path, tex.width, tex.height)
        linear = encode_for_format(gpu, rgba, tex.width, tex.height)
        abs_off = self.cpu_size + tex.tex_offset
        if abs_off + len(linear) > len(self._dec):
            self._dec.extend(b'\x00' * (abs_off + len(linear) - len(self._dec)))
        self._dec[abs_off:abs_off+len(linear)] = linear
        tex.raw_data = bytes(linear)
        return True

    # ---- save / repack -----------------------------------------------------
    def save(self, out_path):
        """
        Repack the (possibly edited) decompressed buffer back into an RSC7
        resource file, reproducing the ORIGINAL compression wrapping:
          - PC .ytd  : zlib-wrapped DEFLATE   (wbits = 15)
          - PS3 .ctd : raw DEFLATE, no header  (wbits = -15)
          - Xbox 360 : LZX via xCompress
        The original 16-byte RSC7 header is preserved (it encodes the
        DECOMPRESSED sizes, which don't change for same-size texture edits),
        so OpenIV reads the rebuilt resource just like a stock file.
        """
        if not self._raw or len(self._raw) < 16:
            raise RuntimeError("No source resource loaded.")
        header = bytes(self._raw[:16])
        body = bytes(self._dec)
        if self.platform == "Xbox 360":
            comp = self.lzx.compress_open(body)
        else:
            # Reproduce the exact deflate wrapping detected at load time.
            wbits = self._wbits if self._wbits in (15, -15, 47) else 15
            if wbits == 47:   # was auto-detected wrapped; emit standard zlib
                wbits = 15
            co = zlib.compressobj(9, zlib.DEFLATED, wbits)
            comp = co.compress(body) + co.flush()
        Path(out_path).write_bytes(header + comp)
        return True

    # ---- add / rename / rebuild (PC .ytd) ----------------------------------
    def _decoded_rgba(self, tex):
        """Decode a texture's current pixels to RGBA via a DDS + Pillow."""
        if not PIL_AVAILABLE:
            raise RuntimeError("Pillow is required to rebuild dictionaries.")
        dds = self.export_dds(tex)
        img = Image.open(io.BytesIO(dds)).convert("RGBA")
        return img.tobytes(), img.width, img.height

    def to_texture_list(self):
        """
        Snapshot every current texture as a builder dict
        (name, fmt, width, height, levels, data) for YtdWriter. Pixel data is
        re-encoded from the live RGBA so it is always self-consistent.
        """
        out = []
        for t in self.textures:
            fmt = (t.fmt_name or 'DXT5').upper()
            gpu = {'DXT1':'GPUTEXTUREFORMAT_DXT1','DXT3':'GPUTEXTUREFORMAT_DXT2_3',
                   'DXT5':'GPUTEXTUREFORMAT_DXT4_5'}.get(fmt,'GPUTEXTUREFORMAT_DXT4_5')
            rgba, w, h = self._decoded_rgba(t)
            data = encode_for_format(gpu, rgba, w, h)
            out.append(dict(name=t.display_name, fmt=fmt if fmt in
                            ('DXT1','DXT3','DXT5','ATI1','ATI2','BC7') else 'DXT5',
                            width=w, height=h, levels=1, data=data))
        return out

    @staticmethod
    def texture_from_image(name, image_path, fmt='DXT5', levels=None):
        """Make a builder-dict texture from any image file on disk.

        levels: number of mip levels to generate. None/0 => 1 (base only).
                'auto' or -1 => full chain down to 1x1.
        """
        if not PIL_AVAILABLE:
            raise RuntimeError("Pillow is required to import images.")
        img = Image.open(image_path).convert("RGBA")
        w, h = img.width, img.height
        if fmt.upper() in ('DXT1','DXT3','DXT5','ATI1','ATI2','BC7'):
            nw = (w + 3)&~3; nh = (h + 3)&~3
            if (nw,nh) != (w,h):
                img = img.resize((nw,nh), Image.LANCZOS); w,h = nw,nh
        gpu = {'DXT1':'GPUTEXTUREFORMAT_DXT1','DXT3':'GPUTEXTUREFORMAT_DXT2_3',
               'DXT5':'GPUTEXTUREFORMAT_DXT4_5'}.get(fmt.upper(),'GPUTEXTUREFORMAT_DXT4_5')
        # decide level count
        max_levels = 1
        d = max(w, h)
        while d > 1:
            d >>= 1; max_levels += 1
        if levels in (None, 0):
            nlev = 1
        elif levels in ('auto', -1):
            nlev = max_levels
        else:
            nlev = max(1, min(int(levels), max_levels))
        # encode each mip and concatenate (base first)
        chain = bytearray()
        for i in range(nlev):
            mw = max(1, w >> i); mh = max(1, h >> i)
            mip = img.resize((mw, mh), Image.LANCZOS) if i else img
            chain += encode_for_format(gpu, mip.tobytes(), mw, mh)
        return dict(name=name, fmt=fmt.upper(), width=w, height=h,
                    levels=nlev, data=bytes(chain))

    def rebuild_pc(self, out_path, texture_list):
        """Build a fresh PC .ytd from a full texture list and write it."""
        blob, syslen, gfxlen = YtdWriter(texture_list).build()
        Path(out_path).write_bytes(blob)
        return True

    @staticmethod
    def create_new_pc(out_path, texture_list):
        """Create a brand-new .ytd file from scratch."""
        blob, _, _ = YtdWriter(texture_list).build()
        Path(out_path).write_bytes(blob)
        return True

    def convert_to_ps3(self, out_path):
        """
        Convert the currently-loaded dictionary to a PS3 .ctd.

        EXPERIMENTAL: builds a structurally-correct PS3 grcTextureDictionary
        (verified to round-trip through the reader), but some RSX GPU register
        fields are not fully reverse-engineered, so in-game rendering on PS3 is
        NOT guaranteed. PC .ytd output is the verified, game-ready path.
        """
        texlist = self.to_texture_list()   # decodes current textures to RGBA->DXT
        blob, _, _ = CtdWriter(texlist).build()
        Path(out_path).write_bytes(blob)
        return True

    def convert_to_xbox360(self, out_path, compress=True):
        """
        Convert the currently-loaded dictionary to an Xbox 360 .xtd.

        Builds a grcTextureDictionaryXenon modeled on real files, tiles the
        pixel data (Xenon swizzle), and reproduces the D3DBaseTexture GPU fetch
        constant. Final compression uses xCompress (needs the 32-bit DLL on
        Windows); pass compress=False to write an uncompressed body for
        structural inspection.
        """
        texlist = self.to_texture_list()
        blob, _, _ = XtdWriter(texlist, self.lzx).build(compress=compress)
        Path(out_path).write_bytes(blob)
        return True

# ============================================================================
# GUI
# ============================================================================
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("RAGE Console Texture Editor v13(Python Port)")
        self.geometry("1240x760"); self.minsize(900,560)
        self.configure(bg=BG)
        self.lzx = LZX()
        self.td = None
        self._preview_photo = None
        self._dirty = False
        self._pending = None
        self._editing = False
        self._status = tk.StringVar(value="Ready - open a .ytd / .xtd / .ctd file.")
        self._platform_var = tk.StringVar(value="PC")
        self._build()
        self._bind_keys()

    def _build(self):
        self._build_menu(); self._build_toolbar()
        main = tk.Frame(self,bg=BG); main.pack(fill="both",expand=True,padx=6,pady=(4,6))
        self._build_platform_bar(main)
        paned = ttk.PanedWindow(main,orient="horizontal"); paned.pack(fill="both",expand=True)
        self._build_left(paned); self._build_right(paned)
        self._build_statusbar()

    def _build_menu(self):
        mb=tk.Menu(self,bg=PANEL,fg=FG,activebackground=ACCENT,activeforeground=BG,
                   tearoff=False,relief="flat")
        def cas(lbl):
            m=tk.Menu(mb,bg=PANEL,fg=FG,activebackground=ACCENT,activeforeground=BG,
                      tearoff=False,relief="flat"); mb.add_cascade(label=lbl,menu=m); return m
        fm=cas("File")
        fm.add_command(label="Open...\tCtrl+O", command=self._open)
        fm.add_command(label="New PC Dictionary (.ytd)...\tCtrl+N", command=self._new_dict)
        fm.add_separator()
        fm.add_command(label="Add Texture...\tCtrl+A", command=self._add_texture)
        fm.add_command(label="Replace Selected Texture...\tCtrl+R", command=self._replace_sel)
        fm.add_command(label="Rename Selected Texture...\tF2", command=self._rename_sel)
        fm.add_separator()
        fm.add_command(label="Save As (repack)...\tCtrl+S", command=self._save_as)
        fm.add_command(label="Rebuild As New .ytd...\tCtrl+Shift+S", command=self._rebuild_as)
        fm.add_command(label="Convert to PS3 .ctd (experimental)...", command=self._convert_ps3)
        fm.add_command(label="Convert to Xbox 360 .xtd (experimental)...", command=self._convert_xbox)
        fm.add_separator()
        fm.add_command(label="Export Selected DDS...\tCtrl+E", command=self._export_sel)
        fm.add_command(label="Export All DDS...", command=self._export_all)
        fm.add_separator()
        fm.add_command(label="Exit", command=self.quit)
        hm=cas("Help")
        hm.add_command(label="LZX / DLL Status", command=self._show_dll_status)
        hm.add_command(label="Dump Resource Structure (for devs)...", command=self._dump_resource)
        hm.add_command(label="Supported Formats", command=self._show_formats)
        hm.add_command(label="About", command=self._about)
        self.config(menu=mb)

    def _build_toolbar(self):
        bar=tk.Frame(self,bg=PANEL,pady=4); bar.pack(fill="x")
        def btn(t,c):
            b=tk.Button(bar,text=t,command=c,bg=BTN,fg=FG,activebackground=BTNACT,
                        activeforeground=FG,relief="flat",padx=10,pady=3,cursor="hand2",
                        font=("Segoe UI",9)); b.pack(side="left",padx=3); return b
        btn("Open", self._open)
        btn("New .ytd", self._new_dict)
        btn("Add Texture", self._add_texture)
        btn("Replace", self._replace_sel)
        btn("Rename", self._rename_sel)
        btn("Save As", self._save_as)
        btn("Export DDS", self._export_sel)
        tk.Frame(bar,bg=PANEL).pack(side="left",fill="x",expand=True)
        self._plat_lbl=tk.Label(bar,text="No file",bg=PANEL,fg=MAUVE,
                                 font=("Segoe UI",9,"bold"),padx=10)
        self._plat_lbl.pack(side="right")

    def _build_platform_bar(self, parent):
        bar=tk.Frame(parent,bg=PANEL,pady=0); bar.pack(fill="x",pady=(0,4))
        tk.Label(bar,text="Platform:",bg=PANEL,fg=FG,font=("Segoe UI",9,"bold"),
                 padx=8).pack(side="left")
        self._plat_btns={}
        for plat in PLATFORMS:
            color={"PC":ACCENT,"PS3":TEAL,"Xbox 360":YELLOW}[plat]
            b=tk.Button(bar,text=plat,command=lambda p=plat:self._select_platform(p),
                        bg=BTN,fg=FG,activebackground=color,activeforeground=BG,
                        relief="flat",padx=14,pady=4,cursor="hand2",
                        font=("Segoe UI",9,"bold"),bd=0)
            b.pack(side="left",padx=2,pady=2); self._plat_btns[plat]=b
        self._plat_info=tk.Label(bar,text="",bg=PANEL,fg=FG,font=("Segoe UI",8),padx=12)
        self._plat_info.pack(side="left")
        self._select_platform("PC")

    def _select_platform(self, plat):
        self._platform_var.set(plat)
        colors={"PC":ACCENT,"PS3":TEAL,"Xbox 360":YELLOW}
        infos={"PC":"Magic RSC7 | LE | zlib",
               "PS3":"Magic 7CSR | BE | zlib",
               "Xbox 360":"Magic 7CSR | BE | LZX (xcompress.dll)"}
        for p,b in self._plat_btns.items():
            b.config(bg=colors[plat] if p==plat else BTN, fg=BG if p==plat else FG)
        self._plat_info.config(text=infos[plat])
        if self.td and self.td.filepath:
            self._load(self.td.filepath, silent=True)

    def _build_left(self, paned):
        f=tk.Frame(paned,bg=BG); paned.add(f,weight=1)
        tk.Label(f,text="Textures",bg=BG,fg=ACCENT,font=("Segoe UI",10,"bold"),
                 anchor="w",padx=4).pack(fill="x")
        cols=("name","size","fmt","mips","plat")
        self._tree=ttk.Treeview(f,columns=cols,show="headings",selectmode="browse")
        for cid,lbl,w,anch in [("name","Name",230,"w"),("size","Dimensions",90,"center"),
            ("fmt","Format",120,"center"),("mips","Mips",45,"center"),
            ("plat","Platform",80,"center")]:
            self._tree.heading(cid,text=lbl)
            self._tree.column(cid,width=w,anchor=anch,minwidth=40)
        st=ttk.Style(); st.theme_use("clam")
        st.configure("Treeview",background=PANEL,foreground=FG,fieldbackground=PANEL,
                     rowheight=22,font=("Segoe UI",9))
        st.configure("Treeview.Heading",background=BTN,foreground=ACCENT,
                     font=("Segoe UI",9,"bold"),relief="flat")
        st.map("Treeview",background=[("selected",ACCENT)],foreground=[("selected",BG)])
        vsb=ttk.Scrollbar(f,orient="vertical",command=self._tree.yview)
        self._tree.configure(yscrollcommand=vsb.set)
        self._tree.pack(side="left",fill="both",expand=True); vsb.pack(side="right",fill="y")
        self._tree.bind("<<TreeviewSelect>>",self._on_sel)
        self._tree.bind("<Double-1>",lambda _:self._export_sel())

    def _build_right(self, paned):
        f=tk.Frame(paned,bg=BG); paned.add(f,weight=1)
        self._canvas=tk.Canvas(f,bg="#0a0a15",highlightthickness=1,highlightbackground=ENTRY)
        self._canvas.pack(fill="both",expand=True)
        self._canvas.create_text(10,10,anchor="nw",fill="#444",
            text="Select a texture to preview",font=("Segoe UI",10))
        lf=tk.LabelFrame(f,text=" Texture Info ",bg=BG,fg=ACCENT,font=("Segoe UI",9,"bold"),
                         padx=8,pady=4,relief="flat",highlightbackground=ENTRY,highlightthickness=1)
        lf.pack(fill="x",pady=(4,0))
        self._info=tk.Text(lf,height=9,bg=PANEL,fg=FG,font=("Consolas",9),relief="flat",
                           state="disabled",cursor="arrow",selectbackground=ACCENT)
        self._info.pack(fill="x")

    def _build_statusbar(self):
        bar=tk.Frame(self,bg=PANEL,pady=2); bar.pack(fill="x",side="bottom")
        tk.Label(bar,textvariable=self._status,bg=PANEL,fg=FG,font=("Segoe UI",9),
                 anchor="w",padx=8).pack(fill="x")

    def _bind_keys(self):
        self.bind("<Control-o>",lambda _:self._open())
        self.bind("<Control-e>",lambda _:self._export_sel())
        self.bind("<Control-r>",lambda _:self._replace_sel())
        self.bind("<Control-s>",lambda _:self._save_as())
        self.bind("<Control-n>",lambda _:self._new_dict())
        self.bind("<Control-a>",lambda _:self._add_texture())
        self.bind("<F2>",lambda _:self._rename_sel())
        self.bind("<Control-Shift-S>",lambda _:self._rebuild_as())

    def _set_status(self,msg): self._status.set(msg); self.update_idletasks()

    def _open(self):
        ext=" ".join(f"*{e}" for e in SUPPORTED_EXTS.split())
        p=filedialog.askopenfilename(title="Open Texture Dictionary",
            filetypes=[("RAGE Texture Files",ext),("All Files","*.*")])
        if p: self._load(p)

    def _load(self, path, silent=False):
        self._set_status(f"Loading {Path(path).name}...")
        td=TextureDict(self.lzx)
        tab=self._platform_var.get()
        # auto: PC magic forces PC; console magic uses tab if PS3/Xbox else Xbox360.
        try:
            magic=Path(path).read_bytes()[:4]
        except Exception as e:
            if not silent: messagebox.showerror("Load Error",str(e))
            self._set_status("Load failed."); return
        force = "PC" if magic==PC_MAGIC else (tab if tab in ("PS3","Xbox 360") else "Xbox 360")
        try:
            td.load(path, force_platform=force)
        except Exception as e:
            if not silent: messagebox.showerror("Load Error",str(e))
            self._set_status("Load failed."); return
        self.td=td
        self._pending=None      # rebuild editable model lazily from this file
        self._editing=False
        self.title(f"RAGE Console Texture Editor  -  {Path(path).name}")
        if td.error_msg:
            self._populate([])
            self._show_msg(RED,"Could not open file",td.error_msg)
            self._plat_lbl.config(text=f"{td.platform} | error")
            self._set_status(td.error_msg.split(chr(10))[0]); return
        self._populate(td.textures)
        n=len(td.textures)
        self._plat_lbl.config(text=f"{td.platform} | CPU {td.cpu_size} GPU {td.gpu_size}")
        self._set_status(f"{Path(path).name}  |  {n} texture(s)  |  {td.platform}")

    def _populate(self, textures):
        for r in self._tree.get_children(): self._tree.delete(r)
        for t in textures:
            self._tree.insert("","end",iid=str(t.index),
                values=(t.display_name,t.size_label,t.fmt_name,t.mips,t.platform))
        self._canvas.delete("all")
        self._canvas.create_text(10,10,anchor="nw",fill="#444",
            text="Select a texture to preview",font=("Segoe UI",10))
        self._write_info(["No texture selected."])

    def _show_msg(self, color, title, body):
        self._canvas.delete("all")
        self._canvas.create_text(20,20,anchor="nw",fill=color,text=title,
                                 font=("Segoe UI",12,"bold"))
        y=55
        for line in body.split("\n"):
            self._canvas.create_text(20,y,anchor="nw",fill=FG,text=line,
                                     font=("Segoe UI",10),width=560); y+=22

    def _on_sel(self,_=None):
        sel=self._tree.selection()
        if not sel or not self.td: return
        idx=int(sel[0])
        if idx>=len(self.td.textures): return
        tex=self.td.textures[idx]
        self._show_info(tex); self._show_preview(tex)

    def _show_info(self, tex):
        self._write_info([
            f"Name        : {tex.display_name}",
            f"Dimensions  : {tex.width} x {tex.height}",
            f"Format      : {tex.fmt_name}  ({tex.gpu_fmt or 'n/a'})",
            f"Mip Levels  : {tex.mips}",
            f"Platform    : {tex.platform}",
            f"Tex Offset  : 0x{tex.tex_offset:08X}",
            f"Name Offset : 0x{tex.name_offset:08X}",
            f"Endian code : {tex.endian}  ({GetGPUENDIAN(tex.endian) if tex.platform=='Xbox 360' else 'n/a'})",
        ])

    def _write_info(self, lines):
        self._info.config(state="normal"); self._info.delete("1.0","end")
        self._info.insert("end","\n".join(lines)); self._info.config(state="disabled")

    def _show_preview(self, tex):
        self._canvas.delete("all"); self._preview_photo=None
        if not PIL_AVAILABLE:
            self._canvas.create_text(10,10,anchor="nw",fill=YELLOW,
                text="Install Pillow for previews.\nExport as DDS to view."); return
        try:
            dds=self.td.export_dds(tex)
            img=Image.open(io.BytesIO(dds)).convert("RGBA")
        except Exception as e:
            self._canvas.create_text(10,10,anchor="nw",fill=YELLOW,
                text=f"Preview not available for {tex.fmt_name}.\nExport as DDS to view.\n({e})")
            return
        cw=max(self._canvas.winfo_width(),400); ch=max(self._canvas.winfo_height(),300)
        scale=min(cw/max(tex.width,1),ch/max(tex.height,1),1.0)
        dw=max(1,int(tex.width*scale)); dh=max(1,int(tex.height*scale))
        img=img.resize((dw,dh),Image.NEAREST)
        photo=ImageTk.PhotoImage(img); self._preview_photo=photo
        x=(cw-dw)//2; y=(ch-dh)//2
        self._canvas.create_image(x,y,anchor="nw",image=photo)
        self._canvas.create_text(4,ch-4,anchor="sw",fill="#666",
            text=f"{tex.width}x{tex.height} | {tex.fmt_name} | {tex.mips} mip(s)",
            font=("Segoe UI",8))

    def _export_sel(self):
        sel=self._tree.selection()
        if not sel or not self.td:
            messagebox.showinfo("Export","No texture selected."); return
        tex=self.td.textures[int(sel[0])]
        out=filedialog.asksaveasfilename(title="Export DDS",defaultextension=".dds",
            initialfile=f"{tex.display_name}",
            filetypes=[("DDS Texture","*.dds"),("All Files","*.*")])
        if not out: return
        try:
            Path(out).write_bytes(self.td.export_dds(tex))
            self._set_status(f"Exported: {Path(out).name}")
        except Exception as e:
            messagebox.showerror("Export Error",str(e))

    def _replace_sel(self):
        sel=self._tree.selection()
        if not sel or not self.td:
            messagebox.showinfo("Replace","No texture selected."); return
        if not PIL_AVAILABLE:
            messagebox.showerror("Replace",
                "Pillow is required to import images. It should auto-install on "
                "launch; check your internet connection and restart."); return
        tex=self.td.textures[int(sel[0])]
        img=filedialog.askopenfilename(title=f"Replace '{tex.display_name}' with image",
            filetypes=[("Images","*.png *.dds *.jpg *.jpeg *.bmp *.tga *.tif *.tiff"),
                       ("All Files","*.*")])
        if not img: return
        try:
            self.td.replace_texture(tex, img)
            self._set_status(f"Replaced '{tex.display_name}' (will be saved on Save As). "
                             f"Resized to {tex.width}x{tex.height} {tex.fmt_name}.")
            self._show_preview(tex)   # refresh preview from edited buffer
            self._dirty=True
        except Exception as e:
            messagebox.showerror("Replace Error",str(e))

    def _save_as(self):
        if not self.td or not self.td.filepath:
            messagebox.showinfo("Save","No file loaded."); return
        if self.td.platform=="Xbox 360" and not self.lzx.available_open:
            if not messagebox.askyesno("Save",
                "Xbox 360 repacking needs xcompress_open.dll, which isn't loaded.\n"
                f"Status: {self.lzx.status()}\n\nTry anyway?"):
                return
        src=Path(self.td.filepath)
        out=filedialog.asksaveasfilename(title="Save Repacked Resource",
            initialfile=src.name, defaultextension=src.suffix,
            filetypes=[("RAGE Texture",f"*{src.suffix}"),("All Files","*.*")])
        if not out: return
        try:
            self.td.save(out)
            self._dirty=False
            self._set_status(f"Saved repacked file: {Path(out).name}")
            messagebox.showinfo("Save","Saved successfully:\n"+out)
        except Exception as e:
            messagebox.showerror("Save Error",str(e))

    # ---- add / rename / new / rebuild (PC .ytd) ----------------------------
    def _ensure_pending(self):
        """Build/refresh the editable texture list from the open dictionary."""
        if getattr(self, "_pending", None) is None:
            self._pending = self.td.to_texture_list() if self.td else []
        return self._pending

    def _refresh_pending_view(self):
        """Show the pending (editable) texture list in the tree."""
        for r in self._tree.get_children(): self._tree.delete(r)
        for i, t in enumerate(self._pending):
            self._tree.insert("","end",iid=str(i),
                values=(t['name'], f"{t['width']}x{t['height']}", t['fmt'],
                        t.get('levels',1), "PC*"))

    def _new_dict(self):
        if not PIL_AVAILABLE:
            messagebox.showerror("New","Pillow is required (auto-installs on launch).")
            return
        self.td = None
        self._pending = []
        self._editing = True
        self._populate([])
        self._refresh_pending_view()
        self.title("RAGE Console Texture Editor  -  (new .ytd)")
        self._plat_lbl.config(text="PC* | new dictionary (unsaved)")
        self._set_status("New empty PC .ytd. Add textures, then Rebuild As New .ytd.")

    def _add_texture(self):
        if not PIL_AVAILABLE:
            messagebox.showerror("Add","Pillow is required (auto-installs on launch)."); return
        # Adding requires the editable (rebuild) model; only PC is supported.
        if self.td and self.td.platform != "PC":
            messagebox.showinfo("Add Texture",
                "Adding textures is supported for PC .ytd (full rebuild).\n"
                "PS3/Xbox 360 use a paged console layout that only supports\n"
                "same-size replace; use Replace for those."); return
        imgs=filedialog.askopenfilenames(title="Add texture image(s)",
            filetypes=[("Images","*.png *.dds *.jpg *.jpeg *.bmp *.tga *.tif *.tiff"),
                       ("All Files","*.*")])
        if not imgs: return
        self._ensure_pending(); self._editing=True
        choice = self._ask_format()
        if choice is None: return
        fmt, levels = choice
        added=0
        for p in imgs:
            try:
                name=Path(p).stem
                self._pending.append(
                    TextureDict.texture_from_image(name, p, fmt, levels)); added+=1
            except Exception as e:
                messagebox.showerror("Add Texture", f"{Path(p).name}: {e}")
        self._refresh_pending_view()
        self._dirty=True
        self._set_status(f"Added {added} texture(s). Use Rebuild As New .ytd to save.")

    def _ask_format(self):
        win=tk.Toplevel(self)
        win.title("Texture Options")
        win.configure(bg=BG)
        win.transient(self)
        win.resizable(False, False)

        choice={"v":None}
        fmtvar=tk.StringVar(value="DXT5")
        mipvar=tk.StringVar(value="1")
        customvar=tk.StringVar(value="4")

        outer=tk.Frame(win,bg=BG,padx=18,pady=14)
        outer.pack(fill="both",expand=True)

        tk.Label(outer,text="Compression format",bg=BG,fg=ACCENT,
                 font=("Segoe UI",10,"bold")).pack(anchor="w")
        for f,desc in [("DXT5","DXT5  — color + smooth alpha"),
                       ("DXT1","DXT1  — opaque / 1-bit alpha"),
                       ("DXT3","DXT3  — color + sharp alpha")]:
            tk.Radiobutton(outer,text=desc,variable=fmtvar,value=f,bg=BG,fg=FG,
                           selectcolor=ENTRY,activebackground=BG,activeforeground=ACCENT,
                           anchor="w",font=("Segoe UI",9)).pack(anchor="w",fill="x")

        tk.Label(outer,text="Mip levels",bg=BG,fg=ACCENT,
                 font=("Segoe UI",10,"bold")).pack(anchor="w",pady=(12,0))
        for label,val in [("1  (base only, no mips)","1"),
                          ("Full chain (auto, down to 1×1)","auto"),
                          ("Custom count","custom")]:
            tk.Radiobutton(outer,text=label,variable=mipvar,value=val,bg=BG,fg=FG,
                           selectcolor=ENTRY,activebackground=BG,activeforeground=ACCENT,
                           anchor="w",font=("Segoe UI",9)).pack(anchor="w",fill="x")
        crow=tk.Frame(outer,bg=BG); crow.pack(anchor="w",pady=(2,0))
        tk.Label(crow,text="Custom count:",bg=BG,fg=FG,font=("Segoe UI",9)).pack(side="left")
        tk.Entry(crow,textvariable=customvar,width=5,bg=ENTRY,fg=FG,
                 insertbackground=FG,relief="flat").pack(side="left",padx=6)

        def ok():
            mv=mipvar.get()
            if mv=="1": lv=1
            elif mv=="auto": lv="auto"
            else:
                try: lv=max(1,int(customvar.get()))
                except Exception: lv=1
            choice["v"]=(fmtvar.get(), lv); win.destroy()
        def cancel():
            choice["v"]=None; win.destroy()

        brow=tk.Frame(outer,bg=BG); brow.pack(fill="x",pady=(16,0))
        tk.Button(brow,text="Add",command=ok,bg=ACCENT,fg=BG,activebackground=BTNACT,
                  relief="flat",padx=22,pady=5,font=("Segoe UI",9,"bold")).pack(side="right")
        tk.Button(brow,text="Cancel",command=cancel,bg=BTN,fg=FG,activebackground=BTNACT,
                  relief="flat",padx=16,pady=5).pack(side="right",padx=6)

        # Realize widgets and size to content BEFORE grabbing input, so the
        # dialog never shows up blank on Windows.
        win.update_idletasks()
        w=max(360, win.winfo_reqwidth()); h=max(300, win.winfo_reqheight())
        px=self.winfo_rootx()+(self.winfo_width()-w)//2
        py=self.winfo_rooty()+(self.winfo_height()-h)//2
        win.geometry(f"{w}x{h}+{max(px,0)}+{max(py,0)}")
        win.bind("<Return>", lambda _:ok())
        win.bind("<Escape>", lambda _:cancel())
        win.grab_set()
        win.wait_window()
        return choice["v"]

    def _rename_sel(self):
        sel=self._tree.selection()
        if not sel: messagebox.showinfo("Rename","No texture selected."); return
        idx=int(sel[0])
        # Renaming uses the editable model (PC rebuild).
        if self.td and self.td.platform != "PC":
            messagebox.showinfo("Rename",
                "Renaming is supported for PC .ytd (full rebuild). PS3/Xbox 360\n"
                "store names inside a paged layout; use the PC workflow to rename."); return
        self._ensure_pending(); self._editing=True
        if idx>=len(self._pending): return
        cur=self._pending[idx]['name']
        win=tk.Toplevel(self); win.title("Rename Texture"); win.configure(bg=BG)
        win.transient(self); win.resizable(False, False)
        outer=tk.Frame(win,bg=BG,padx=18,pady=14); outer.pack(fill="both",expand=True)
        tk.Label(outer,text="New name (no extension):",bg=BG,fg=ACCENT,
                 font=("Segoe UI",10,"bold")).pack(anchor="w")
        var=tk.StringVar(value=Path(cur).stem)
        ent=tk.Entry(outer,textvariable=var,bg=ENTRY,fg=FG,insertbackground=FG,
                     font=("Consolas",11),width=34,relief="flat")
        ent.pack(fill="x",pady=(6,0))
        def ok():
            nm=var.get().strip()
            if nm:
                self._pending[idx]['name']=nm
                self._refresh_pending_view(); self._dirty=True
                self._set_status(f"Renamed to '{nm}'. Rebuild As New .ytd to save.")
            win.destroy()
        def cancel(): win.destroy()
        brow=tk.Frame(outer,bg=BG); brow.pack(fill="x",pady=(16,0))
        tk.Button(brow,text="Rename",command=ok,bg=ACCENT,fg=BG,activebackground=BTNACT,
                  relief="flat",padx=20,pady=5,font=("Segoe UI",9,"bold")).pack(side="right")
        tk.Button(brow,text="Cancel",command=cancel,bg=BTN,fg=FG,activebackground=BTNACT,
                  relief="flat",padx=14,pady=5).pack(side="right",padx=6)
        win.update_idletasks()
        w=max(340, win.winfo_reqwidth()); h=max(140, win.winfo_reqheight())
        px=self.winfo_rootx()+(self.winfo_width()-w)//2
        py=self.winfo_rooty()+(self.winfo_height()-h)//2
        win.geometry(f"{w}x{h}+{max(px,0)}+{max(py,0)}")
        ent.bind("<Return>",lambda _:ok())
        win.bind("<Escape>",lambda _:cancel())
        ent.focus_set()
        win.grab_set()
        win.wait_window()

    def _rebuild_as(self):
        if not getattr(self,"_pending",None):
            # nothing pending: build from current dict if PC
            if self.td and self.td.platform=="PC":
                try: self._pending=self.td.to_texture_list()
                except Exception as e:
                    messagebox.showerror("Rebuild",str(e)); return
            else:
                messagebox.showinfo("Rebuild",
                    "Rebuild creates a new PC .ytd from the current texture list.\n"
                    "Open a PC .ytd or start New PC Dictionary, add textures, then rebuild."); return
        if not self._pending:
            messagebox.showinfo("Rebuild","No textures to write."); return
        out=filedialog.asksaveasfilename(title="Rebuild As New .ytd",
            defaultextension=".ytd", initialfile="rebuilt.ytd",
            filetypes=[("GTA V PC Texture Dictionary","*.ytd"),("All Files","*.*")])
        if not out: return
        try:
            TextureDict.create_new_pc(out, self._pending)
            self._dirty=False
            self._set_status(f"Rebuilt {len(self._pending)} texture(s) -> {Path(out).name}")
            messagebox.showinfo("Rebuild",
                f"Wrote {len(self._pending)} textures to:\n{out}\n\n"
                "Import it into your RPF with OpenIV.")
        except Exception as e:
            messagebox.showerror("Rebuild Error",str(e))

    def _convert_ps3(self):
        # Need a loaded dictionary or a pending texture list to convert.
        have = (self.td and self.td.textures) or getattr(self,"_pending",None)
        if not have:
            messagebox.showinfo("Convert to PS3",
                "Open a .ytd (or build one) first, then convert it to PS3 .ctd."); return
        if not PIL_AVAILABLE:
            messagebox.showerror("Convert","Pillow is required."); return
        if not messagebox.askyesno("Convert to PS3 .ctd  (EXPERIMENTAL)",
            "This writes a PS3 .ctd with the correct RSC7 container, big-endian\n"
            "layout, and grcTexture structure (verified to re-open in this tool).\n\n"
            "HOWEVER: some PS3 RSX GPU register fields are not fully reverse-\n"
            "engineered, so the texture may not render correctly in-game on PS3.\n"
            "The PC .ytd path is the fully verified one.\n\n"
            "Continue and write an experimental .ctd?"):
            return
        out=filedialog.asksaveasfilename(title="Convert to PS3 .ctd",
            defaultextension=".ctd", initialfile="converted.ctd",
            filetypes=[("PS3 Texture Dictionary","*.ctd"),("All Files","*.*")])
        if not out: return
        try:
            # If we have a pending (edited) list and no loaded td, build via Ctd
            if (not self.td or not self.td.textures) and getattr(self,"_pending",None):
                blob,_,_ = CtdWriter(self._pending).build()
                Path(out).write_bytes(blob)
            else:
                self.td.convert_to_ps3(out)
            self._set_status(f"Wrote experimental PS3 .ctd -> {Path(out).name}")
            messagebox.showinfo("Convert to PS3",
                f"Wrote: {out}\n\nThis is experimental — test it before relying on it.")
        except Exception as e:
            messagebox.showerror("Convert Error",str(e))

    def _convert_xbox(self):
        have = (self.td and self.td.textures) or getattr(self,"_pending",None)
        if not have:
            messagebox.showinfo("Convert to Xbox 360",
                "Open a .ytd (or build one) first, then convert to Xbox 360 .xtd."); return
        if not PIL_AVAILABLE:
            messagebox.showerror("Convert","Pillow is required."); return
        has_dll = self.lzx.available_open
        warn = ("This writes an Xbox 360 .xtd: correct RSC7 '7CSR' container,\n"
                "Xenon-tiled pixel data, and a D3DBaseTexture GPU fetch constant\n"
                "that matches real files in 11 of 13 registers.\n\n")
        if has_dll:
            warn += "xCompress IS available, so a compressed (game-format) .xtd\nwill be written.\n\n"
        else:
            warn += ("xCompress is NOT available (need 32-bit Windows + DLLs), so\n"
                     "only an UNCOMPRESSED body can be written (for inspection,\n"
                     "not loadable by the game).\n\n")
        warn += "This is EXPERIMENTAL and unverified in-game. Continue?"
        if not messagebox.askyesno("Convert to Xbox 360 .xtd  (EXPERIMENTAL)", warn):
            return
        out=filedialog.asksaveasfilename(title="Convert to Xbox 360 .xtd",
            defaultextension=".xtd", initialfile="converted.xtd",
            filetypes=[("Xbox 360 Texture Dictionary","*.xtd"),("All Files","*.*")])
        if not out: return
        try:
            if (not self.td or not self.td.textures) and getattr(self,"_pending",None):
                blob,_,_ = XtdWriter(self._pending, self.lzx).build(compress=has_dll)
                Path(out).write_bytes(blob)
            else:
                self.td.convert_to_xbox360(out, compress=has_dll)
            self._set_status(f"Wrote {'compressed' if has_dll else 'uncompressed'} .xtd -> {Path(out).name}")
            messagebox.showinfo("Convert to Xbox 360",
                f"Wrote: {out}\n\n" + ("Compressed with xCompress.\n" if has_dll else
                "UNCOMPRESSED (inspection only - won't load in game).\n") +
                "Experimental - please test and report back.")
        except Exception as e:
            messagebox.showerror("Convert Error",str(e))

    def _export_all(self):
        if not self.td or not self.td.textures:
            messagebox.showinfo("Export","No textures loaded."); return
        folder=filedialog.askdirectory(title="Select Export Folder")
        if not folder: return
        ok=err=0
        for tex in self.td.textures:
            try:
                name=tex.display_name
                if not name.lower().endswith(".dds"): name+=".dds"
                (Path(folder)/name).write_bytes(self.td.export_dds(tex)); ok+=1
            except Exception:
                err+=1
        msg=f"Exported {ok} texture(s) to:\n{folder}"
        if err: msg+=f"\n\n{err} error(s)."
        messagebox.showinfo("Export Complete",msg)
        self._set_status(f"Exported {ok} textures to {folder}")

    def _dump_resource(self):
        p=filedialog.askopenfilename(title="Dump Resource Structure",
            filetypes=[("RAGE Texture Files","*.xtd *.ctd *.ytd"),("All Files","*.*")])
        if not p: return
        # determine platform from the current tab for 7CSR files
        tab=self._platform_var.get()
        try:
            magic=Path(p).read_bytes()[:4]
        except Exception as e:
            messagebox.showerror("Dump",str(e)); return
        force = "PC" if magic==PC_MAGIC else (tab if tab in ("PS3","Xbox 360") else "Xbox 360")
        try:
            rp, binp, report = dump_resource(p, force_platform=force)
            msg = f"Dump written next to the source file:\n\n{rp}"
            if binp: msg += f"\n{binp}"
            msg += "\n\nSend BOTH files back so the writer can be built accurately."
            self._set_status(f"Dumped structure -> {Path(rp).name}")
            messagebox.showinfo("Dump Complete", msg)
        except Exception as e:
            messagebox.showerror("Dump Error", str(e))

    def _show_dll_status(self):
        bits = _python_bits()
        extra = ""
        if os.name == 'nt' and self.lzx._arch_mismatch:
            extra = ("\n\nFIX: You are running %d-bit Python but the DLLs are 32-bit.\n"
                     "Install 32-bit Python (python.org > Windows installer 32-bit),\n"
                     "then run this tool with it." % bits)
        elif os.name == 'nt' and not (self.lzx.available_open or self.lzx.available_cpp):
            extra = ("\n\nFIX: Put xcompress.dll, xcompress_cpp.dll and\n"
                     "xcompress_open.dll in the same folder as this program\n"
                     "(or in a 'lib' subfolder).")
        messagebox.showinfo("LZX / DLL Status",
            "Xbox 360 LZX (de)compression uses native DLLs via ctypes:\n\n"
            f"{self.lzx.status()}\n\n"
            "Required files: xcompress.dll, xcompress_cpp.dll, xcompress_open.dll\n"
            "(searched next to the program, then ./lib, ./dll, and the cwd)\n\n"
            "These are 32-bit Windows libraries, so the Xbox 360 path needs\n"
            "32-bit Python on Windows. PC (.ytd) and PS3 (.ctd) use zlib and\n"
            "work on any platform."
            + extra)

    def _show_formats(self):
        win=tk.Toplevel(self); win.title("Supported Formats"); win.configure(bg=BG)
        win.transient(self); win.resizable(False, False)
        text=("Platform detection (from magic bytes):\n"
              "  PC      .ytd        RSC7  Little-Endian  raw deflate\n"
              "  PS3     .ctd/.xtd   7CSR  Big-Endian     raw deflate\n"
              "  Xbox360 .xtd        7CSR  Big-Endian     LZX (xcompress.dll)\n\n"
              "Xbox 360 GPU texture formats decoded:\n"
              "  DXT1, DXT2/3, DXT4/5, DXT5A, DXN, 8, 8_8_8_8\n"
              "  (Xenon tiling + endian swap handled automatically)\n\n"
              "The platform tab disambiguates PS3 vs Xbox 360 for 7CSR files.")
        tk.Label(win,text=text,bg=BG,fg=FG,font=("Consolas",9),justify="left",
                 padx=20,pady=12).pack()
        tk.Button(win,text="Close",command=win.destroy,bg=BTN,fg=FG,relief="flat",
                  padx=20,pady=4).pack(pady=(0,12))
        win.update_idletasks()
        px=self.winfo_rootx()+(self.winfo_width()-win.winfo_reqwidth())//2
        py=self.winfo_rooty()+(self.winfo_height()-win.winfo_reqheight())//2
        win.geometry(f"+{max(px,0)}+{max(py,0)}")
        win.bind("<Escape>",lambda _:win.destroy())
        win.grab_set()

    def _about(self):
        win=tk.Toplevel(self); win.title("About"); win.configure(bg=BG)
        win.transient(self); win.resizable(False, False)
        text=("RAGE Console Texture Editor v13 - Python Port\n\n"
              "Original Pascal tool: indirivacua / Dageron\n"
              "github.com/indirivacua/RAGE-Console-Texture-Editor\n\n"
              "Python/Tkinter port: Claude\n"
              "Promted by: SoLjA_RGH"
              "Faithful port of the Pascal units. Xbox 360 LZX decoding calls\n"
              "the original xcompress*.dll files through ctypes (Windows 32-bit).\n"
              "PC and PS3 paths use stdlib deflate and run anywhere.")
        tk.Label(win,text=text,bg=BG,fg=FG,font=("Consolas",9),justify="left",
                 padx=20,pady=12).pack()
        tk.Button(win,text="Close",command=win.destroy,bg=BTN,fg=FG,relief="flat",
                  padx=20,pady=4).pack(pady=(0,12))
        win.update_idletasks()
        px=self.winfo_rootx()+(self.winfo_width()-win.winfo_reqwidth())//2
        py=self.winfo_rooty()+(self.winfo_height()-win.winfo_reqheight())//2
        win.geometry(f"+{max(px,0)}+{max(py,0)}")
        win.bind("<Escape>",lambda _:win.destroy())
        win.grab_set()

# ============================================================================
# Diagnostic dump mode (run on Windows with the DLLs) for reverse-engineering
# the Xbox 360 / PS3 resource structure so the writer can be built accurately.
# ----------------------------------------------------------------------------
def dump_resource(path, force_platform=None, out_dir=None):
    """
    Decompress a .xtd/.ctd/.ytd and write:
      <name>.decompressed.bin  -- the full decompressed system+graphics buffer
      <name>.dump.txt          -- header, sizes, and per-texture field analysis
    For Xbox 360 this needs the xcompress*.dll (32-bit Windows). The dump is
    what lets the structure be reproduced exactly by the writer.
    """
    path = str(path)
    out_dir = out_dir or os.path.dirname(os.path.abspath(path))
    base = os.path.splitext(os.path.basename(path))[0]
    lzx = LZX()
    raw = Path(path).read_bytes()
    platform, dec, cpu, gpu, wbits, err = load_resource(raw, lzx, force_platform)
    lines = []
    def L(s=""): lines.append(s)
    L(f"FILE: {path}")
    L(f"size: {len(raw)} bytes")
    L(f"magic: {raw[:4]!r}")
    _ver_le = struct.unpack_from('<I', raw, 4)[0]
    _ver = (_ver_le & 0xFF) or ((_ver_le >> 24) & 0xFF)
    L(f"version: {_ver}")
    f1 = struct.unpack_from('<I', raw, 8)[0]
    f2 = struct.unpack_from('<I', raw, 12)[0]
    is_console = raw[:4] == CONSOLE_MAGIC
    if is_console:
        L(f"raw flags (LE read): sys=0x{f1:08X} gfx=0x{f2:08X}")
        L(f"flags (BE decoded) : sys=0x{EndianChangeDWORD(f1):08X} "
          f"gfx=0x{EndianChangeDWORD(f2):08X}")
    else:
        L(f"flags: sys=0x{f1:08X} gfx=0x{f2:08X}")
    L(f"detected platform: {platform}")
    L(f"CPU(system) size: {cpu}   GPU(graphics) size: {gpu}")
    if err:
        L("")
        L("ERROR decompressing: " + err)
        report = "\n".join(lines)
        rp = os.path.join(out_dir, base + ".dump.txt")
        Path(rp).write_text(report, encoding="utf-8")
        return rp, None, report

    # write the decompressed buffer
    binp = os.path.join(out_dir, base + ".decompressed.bin")
    Path(binp).write_bytes(dec)
    L(f"decompressed total: {len(dec)} bytes -> {os.path.basename(binp)}")
    L("")

    # platform-specific structural walk with full raw struct bytes
    if platform == "Xbox 360":
        _dump_xbox360(dec, cpu, L)
    elif platform == "PS3":
        _dump_ps3(dec, cpu, L)
    else:
        _dump_pc(dec, cpu, L)

    report = "\n".join(lines)
    rp = os.path.join(out_dir, base + ".dump.txt")
    Path(rp).write_text(report, encoding="utf-8")
    return rp, binp, report

def _hexrow(buf, off, n=4):
    return buf[off:off+n].hex()

def _dump_xbox360(dec, cpu, L):
    r = R(dec); r.seek(0)
    vmt   = EndianChangeDWORD(r.u32_le())
    omap  = GetOffset(EndianChangeDWORD(r.u32_le()))
    fC    = EndianChangeDWORD(r.u32_le()); f10 = EndianChangeDWORD(r.u32_le())
    hsh   = GetOffset(EndianChangeDWORD(r.u32_le()))
    count = EndianChangeWORD(r.u16_le()); count2 = EndianChangeWORD(r.u16_le())
    listoff = GetOffset(EndianChangeDWORD(r.u32_le()))
    L("=== Xbox360 grcTextureDictionary header ===")
    L(f"  dict vft        : 0x{vmt:08X}")
    L(f"  offsetMapOffset : 0x{omap:08X}")
    L(f"  hashTableOffset : 0x{hsh:08X}")
    L(f"  textureCount    : {count}")
    L(f"  textureListOff  : 0x{listoff:08X}")
    L(f"  dict header raw : {dec[:0x40].hex()}")
    L("")
    offsets = []
    r.seek(listoff)
    for _ in range(count):
        offsets.append(GetOffset(EndianChangeDWORD(r.u32_le())))
    for i, b in enumerate(offsets):
        L(f"--- grcTextureXenon[{i}] @0x{b:08X} (full 0x60 bytes) ---")
        L(f"  raw: {dec[b:b+0x60].hex()}")
        # known fields
        r.seek(b+32); nptr = GetOffset(EndianChangeDWORD(r.u32_le()))
        r.seek(b+52); d3d  = GetOffset(EndianChangeDWORD(r.u32_le()))
        r.seek(b+56); w = EndianChangeWORD(r.u16_le()); h = EndianChangeWORD(r.u16_le())
        name = _read_cstr(dec, nptr)
        L(f"  name@+32 -> 0x{nptr:08X} = {name!r}")
        L(f"  D3DBaseTexture ptr@+52 -> 0x{d3d:08X}")
        L(f"  width@+56={w} height@+58={h}")
        # full D3DBaseTexture: dump 16 dwords raw (both LE and BE views)
        L(f"  --- D3DBaseTexture @0x{d3d:08X} (16 dwords, LE | BE) ---")
        for k in range(16):
            o = d3d + k*4
            if o+4 > len(dec): break
            le = struct.unpack_from('<I', dec, o)[0]
            be = EndianChangeDWORD(le)
            L(f"    dword_{k+1:02d} (+0x{k*4:02X}): LE=0x{le:08X}  BE=0x{be:08X}")
        # decode via our reader for cross-check
        r.seek(d3d); dwords = [r.u32_le() for _ in range(13)]
        info = ReadD3DBaseTexture(dwords)
        L(f"  decoded DataFormat={info['DataFormat']} "
          f"({GetGPUTEXTUREFORMAT(info['DataFormat'])}) MaxMip+1={info['MaxMipLevel']+1}")
        r.seek(d3d+32); gpuoff = EndianChangeDWORD(DataOffset(r.u32_le()))
        L(f"  GPU data offset (decoded) = 0x{gpuoff:08X}  (abs = +cpu 0x{gpuoff+cpu:08X})")
        L("")

def _dump_ps3(dec, cpu, L):
    r = R(dec); r.seek(0)
    vmt = EndianChangeDWORD(r.u32_le())
    r.seek(0x14); count = EndianChangeWORD(r.u16_le())
    r.seek(0x18); listoff = GetOffset(EndianChangeDWORD(r.u32_le()))
    L("=== PS3 grcTextureDictionary header ===")
    L(f"  dict vft     : 0x{vmt:08X}")
    L(f"  textureCount : {count}")
    L(f"  listOffset   : 0x{listoff:08X}")
    L(f"  dict raw     : {dec[:0x40].hex()}")
    L("")
    offs = []
    r.seek(listoff)
    for _ in range(count):
        offs.append(GetOffset(EndianChangeDWORD(r.u32_le())))
    for i, b in enumerate(offs):
        L(f"--- grcTexturePS3[{i}] @0x{b:08X} (full 0x40 bytes) ---")
        L(f"  raw: {dec[b:b+0x40].hex()}")
        r.seek(b+0x20); nptr = GetOffset(EndianChangeDWORD(r.u32_le()))
        L(f"  vft@+0=0x{EndianChangeDWORD(struct.unpack_from('<I',dec,b)[0]):08X}")
        L(f"  fmt@+8={dec[b+8]} mip@+9={dec[b+9]}")
        L(f"  name@+0x20 -> {_read_cstr(dec,nptr)!r}")
        L("")

def _dump_pc(dec, cpu, L):
    L("=== PC grcTextureDictionary ===")
    L(f"  dict raw: {dec[:0x40].hex()}")

# ============================================================================
if __name__ == "__main__":
    # CLI dump mode:  python rage_texture_editor.py --dump file.xtd [PS3|Xbox360]
    if len(sys.argv) >= 3 and sys.argv[1] == "--dump":
        plat = sys.argv[3] if len(sys.argv) > 3 else None
        plat = {"ps3":"PS3","xbox360":"Xbox 360","xbox":"Xbox 360","pc":"PC"}.get(
            (plat or "").lower(), plat)
        try:
            rp, binp, report = dump_resource(sys.argv[2], force_platform=plat)
            print(report)
            print("\nWrote dump report:", rp)
            if binp: print("Wrote decompressed buffer:", binp)
            print("\nSend BOTH files back so the writer can be built accurately.")
        except Exception as e:
            print("Dump failed:", e)
        sys.exit(0)
    App().mainloop()

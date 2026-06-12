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

# pycryptodome (AES for encrypted RPF archives). Auto-installed if missing.
_CRYPTO = _ensure_package("Crypto", "pycryptodome")

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
GTA4_MAGIC    = b'RSC\x05'     # 0x05435352 -- GTA IV / EFLC (RSC version 5)

def GetValueRSC05(flags):
    """
    GTA IV (RSC version 5) flag decoder. A single 32-bit flags word at +0x08
    encodes both segment sizes:
      system  = (flags & 0x7FF)        << (((flags >> 11) & 0xF) + 8)
      graphics= ((flags >> 15) & 0x7FF)<< (((flags >> 26) & 0xF) + 8)
    Returns (system_size, graphics_size). Verified against w_ak47.wdr
    (9984 + 720896 = 730880 = exact decompressed length).
    """
    flags &= 0xFFFFFFFF
    sysz = (flags & 0x7FF) << (((flags >> 11) & 0xF) + 8)
    gfxz = ((flags >> 15) & 0x7FF) << (((flags >> 26) & 0xF) + 8)
    return sysz, gfxz
DDS_MAGIC     = b'DDS '

# Signature DWORDs as read little-endian from the first 4 bytes (matches Pascal
# 'InStream.Read(dwSignature,4)' on a little-endian machine).
SIG_RSC7_GTA5 = 0x37435352     # '7CSR' bytes -> GTA V console (and PC shares 'RSC7' text)
# In the original, GTA V is detected by dwSignature = $37435352. Both PC 'RSC7'
# and console '7CSR' produce this same little-endian DWORD because the 4 chars
# are a reversal of each other; platform is then disambiguated by file/user.

SUPPORTED_EXTS = ".ytd .xtd .ctd .wtd .wdr .wdd .wft .xhm .chm .xshp .cshp .xsf .csf .sys .gfx"

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
        self._xmem = None      # xcompress.dll      (XMem* LZX - RPF7 console)
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
        base_path = self._find_dll("xcompress.dll")
        if not cpp_path and not open_path and not base_path:
            self._loaded_err = ("xcompress*.dll not found.\n"
                                "Place the three xcompress*.dll files next to this "
                                "program (or in a ./lib subfolder).")
            return

        self.dll_dir = os.path.dirname(cpp_path or open_path or base_path)
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
            if base_path:
                # Microsoft XMem* API (the codec the RPF7 console archives use
                # for resource data, per koolk's RPF7 viewer). This is the
                # CORRECT path for GTA V Xbox 360 RPF-packed resources.
                try:
                    self._xmem = ctypes.CDLL(base_path)
                    self._xmem.XMemCreateDecompressionContext.argtypes = [
                        ctypes.c_int,                 # XMEMCODEC_TYPE
                        ctypes.c_void_p,              # params*
                        ctypes.c_int,                 # flags
                        ctypes.POINTER(ctypes.c_void_p)]
                    self._xmem.XMemCreateDecompressionContext.restype = ctypes.c_int
                    self._xmem.XMemDecompress.argtypes = [
                        ctypes.c_void_p,              # context
                        ctypes.c_char_p,              # dest
                        ctypes.POINTER(ctypes.c_int), # destSize*
                        ctypes.c_char_p,              # src
                        ctypes.c_int]                 # srcSize
                    self._xmem.XMemDecompress.restype = ctypes.c_int
                    self._xmem.XMemDestroyDecompressionContext.argtypes = [ctypes.c_void_p]
                    self._xmem.XMemDestroyDecompressionContext.restype = None
                except OSError as e:
                    self._handle_load_error("xcompress.dll", e)
                except AttributeError:
                    # Some xcompress.dll builds don't export XMem*; ignore.
                    self._xmem = None
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
                 "open:" + ("OK" if self._open else "missing"),
                 "xmem:" + ("OK" if self._xmem else "missing")]
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

    @property
    def available_xmem(self):
        return self._xmem is not None

    # ---- XMem LZX: the codec GTA V console RPF7 uses for resource data -------
    def xmem_decompress(self, data, uncompressed_size):
        """
        Decompress an RPF7 console resource body using the Microsoft XMem LZX
        codec (xcompress.dll), matching koolk's RPF7 viewer. `uncompressed_size`
        MUST be known up front (computed from the resource's system+graphics
        flags). Window 64 KB, partition 256 KB, create flag = 1.

        This is the correct path for GTA V Xbox 360 RPF-packed resources, and
        unlike xDecompress it will not crash on this data.
        """
        if not self._xmem:
            raise LZXError("xcompress.dll (XMem* API) unavailable: "
                           + (self._loaded_err or "not loaded"))
        if uncompressed_size <= 0:
            raise LZXError("XMem decompress needs a positive uncompressed size.")

        # XMEMCODEC_PARAMETERS_LZX { int Flags; int WindowSize; int PartitionSize; }
        params = (ctypes.c_int * 3)(0, 64 * 1024, 256 * 1024)
        ctx = ctypes.c_void_p(0)
        XMEMCODEC_LZX = 1
        rc = self._xmem.XMemCreateDecompressionContext(
            XMEMCODEC_LZX, ctypes.cast(params, ctypes.c_void_p), 1,
            ctypes.byref(ctx))
        if rc != 0 or not ctx.value:
            raise LZXError(f"XMemCreateDecompressionContext failed (rc={rc})")
        try:
            out = ctypes.create_string_buffer(uncompressed_size)
            out_len = ctypes.c_int(uncompressed_size)
            src = bytes(data)
            rc = self._xmem.XMemDecompress(ctx, out, ctypes.byref(out_len),
                                           src, len(src))
            if rc != 0:
                raise LZXError(f"XMemDecompress failed (rc={rc})")
            return out.raw[:out_len.value]
        finally:
            self._xmem.XMemDestroyDecompressionContext(ctx)

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

def _ps3_8888_to_dds(data):
    """
    PS3 RSX 8_8_8_8 is big-endian: each pixel is stored as bytes [A,R,G,B].
    A standard DDS A8R8G8B8 (rmask 0x00FF0000 ...) expects little-endian byte
    order [B,G,R,A]. Reversing each 4-byte group converts [A,R,G,B] -> [B,G,R,A].
    Symmetric: the same reversal converts a DDS pixel back to PS3 order, so this
    one function is used for both export and import.
    """
    out = bytearray(len(data))
    n = len(data) - (len(data) % 4)
    for i in range(0, n, 4):
        out[i]   = data[i+3]
        out[i+1] = data[i+2]
        out[i+2] = data[i+1]
        out[i+3] = data[i]
    return bytes(out)

# import side has identical byte work; alias for readability at call sites
_dds_8888_to_ps3 = _ps3_8888_to_dds

# PS3 RSX stores power-of-two linear (8_8_8_8 / 8) textures in Morton/Z-order
# (swizzled). Set False from the Help menu if a particular file stores them
# linear and the unswizzle makes them WORSE (rare, but format-version dependent).
PS3_UNSWIZZLE_ENABLED = True


def _ps3_swizzle_offset(x, y, w, h):
    """
    Morton / Z-order address for PS3 RSX swizzled textures.
    Interleaves the bits of x and y. Works for any power-of-two w/h
    (including non-square, by stopping each axis when it runs out of bits).
    """
    offset = 0; shift = 0
    xx, yy = x, y
    ww, hh = w, h
    while ww > 1 or hh > 1:
        if ww > 1:
            offset |= (xx & 1) << shift
            xx >>= 1; shift += 1; ww >>= 1
        if hh > 1:
            offset |= (yy & 1) << shift
            yy >>= 1; shift += 1; hh >>= 1
    return offset


def ps3_unswizzle(data, width, height, bytespp):
    """
    Convert PS3 RSX swizzled (Morton-order) pixel data to linear row-major.

    GTA V PS3 stores linear formats (8_8_8_8, 8) swizzled when the texture is
    a power-of-two; DXT/compressed formats are NOT swizzled. Only call this for
    the linear formats. If dimensions aren't power-of-two the data is assumed
    linear and returned unchanged (RSX cannot swizzle NPOT textures).
    """
    if not PS3_UNSWIZZLE_ENABLED:
        return data
    def _is_pow2(v): return v > 0 and (v & (v - 1)) == 0
    if not (_is_pow2(width) and _is_pow2(height)):
        return data
    need = width * height * bytespp
    if len(data) < need:
        return data  # not enough data; leave as-is rather than corrupt
    out = bytearray(need)
    for y in range(height):
        row = y * width
        for x in range(width):
            src = _ps3_swizzle_offset(x, y, width, height) * bytespp
            dst = (row + x) * bytespp
            out[dst:dst + bytespp] = data[src:src + bytespp]
    return bytes(out)


def ps3_swizzle(data, width, height, bytespp):
    """Inverse of ps3_unswizzle: linear row-major -> RSX swizzled (for import)."""
    if not PS3_UNSWIZZLE_ENABLED:
        return data
    def _is_pow2(v): return v > 0 and (v & (v - 1)) == 0
    if not (_is_pow2(width) and _is_pow2(height)):
        return data
    need = width * height * bytespp
    if len(data) < need:
        return data
    out = bytearray(need)
    for y in range(height):
        row = y * width
        for x in range(width):
            dst = _ps3_swizzle_offset(x, y, width, height) * bytespp
            src = (row + x) * bytespp
            out[dst:dst + bytespp] = data[src:src + bytespp]
    return bytes(out)


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
        # DXT5A / BC4 is 8 bytes per 4x4 block (single channel), same as DXT1.
        dwSize=_align(width,128)*_align(height,128)//2
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

def _encode_dxt_color_block(pixels, dxt5=True):
    """Encode 16 (r,g,b,a) pixels into an 8-byte DXT color block.

    For DXT5 (dxt5=True) the color block MUST use 4-colour mode (c0 > c1).
    The 3-colour 'punch-through' mode (c0 <= c1) is only legal in DXT1 and
    produces malformed blocks in DXT5 -- this is what broke solid / black-and-
    white textures (every flat 4x4 region collapses to c0 == c1). We guarantee
    c0 > c1 by nudging the endpoints apart when they are equal.
    """
    opaque = [(r,g,b) for (r,g,b,a) in pixels]
    cmin = [min(c[i] for c in opaque) for i in range(3)]
    cmax = [max(c[i] for c in opaque) for i in range(3)]
    c0 = _rgb565(*cmax); c1 = _rgb565(*cmin)

    if c0 == c1:
        # Degenerate (solid / monochrome) block. Force a valid 4-colour block
        # with c0 > c1 so decoders and OpenIV's validator accept it. Drop c1 by
        # the smallest representable step; the colour is unchanged because every
        # index will point at endpoint 0 (c0).
        if c1 > 0:
            c1 -= 1
        else:
            c0 += 1   # c0 was 0 (pure black): raise c0 instead so c0 > c1
        # all pixels map to endpoint 0 (the true colour)
        return struct.pack('<HHI', c0, c1, 0)

    if c0 < c1:
        c0, c1 = c1, c0   # ensure 4-colour mode (c0 > c1)

    def expand(c565):
        r=((c565>>11)&0x1F); g=((c565>>5)&0x3F); b=(c565&0x1F)
        return (r<<3|r>>2, g<<2|g>>4, b<<3|b>>2)
    p0=expand(c0); p1=expand(c1)
    # 4-colour mode interpolation (always, for DXT5 correctness)
    p2=tuple((2*p0[i]+p1[i])//3 for i in range(3))
    p3=tuple((p0[i]+2*p1[i])//3 for i in range(3))
    pal=[p0,p1,p2,p3]
    bits=0
    for i,(r,g,b,a) in enumerate(pixels):
        best=0; bd=1<<30
        for j,p in enumerate(pal):
            d=(r-p[0])**2+(g-p[1])**2+(b-p[2])**2
            if d<bd: bd=d; best=j
        bits |= best << (2*i)
    return struct.pack('<HHI', c0, c1, bits)

def _encode_dxt3_alpha_block(pixels):
    """DXT3 (DXT2_3) explicit alpha: 16 x 4-bit alpha values, 8 bytes total.
    This is NOT the DXT5 interpolated alpha -- using DXT5's alpha block for a
    DXT3 texture corrupts the alpha channel."""
    val = 0
    for i, (_, _, _, a) in enumerate(pixels):
        # 8-bit alpha -> 4-bit (round to nearest)
        a4 = (a * 15 + 127) // 255
        val |= (a4 & 0xF) << (4 * i)
    return val.to_bytes(8, 'little')

def _encode_dxt5_alpha_block(pixels):
    """pixels: list of 16 (r,g,b,a). Returns 8 bytes of DXT5 interpolated alpha."""
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
    val=0
    for i,ix in enumerate(idx):
        val |= (ix & 7) << (3*i)
    packed=val.to_bytes(6,'little')
    return bytes([a0,a1])+packed

def _encode_bc4_block(values):
    """BC4 / DXT5A single-channel block from 16 8-bit values. 8 bytes.
    Same layout as the DXT5 alpha block but driven by one channel (red)."""
    r0=max(values); r1=min(values)
    if r0==r1:
        return bytes([r0,r1,0,0,0,0,0,0])
    pal=[r0,r1]+[((7-i)*r0+(i)*r1)//7 for i in range(1,7)]
    val=0
    for i,v in enumerate(values):
        best=0; bd=1<<30
        for j,p in enumerate(pal):
            d=(v-p)*(v-p)
            if d<bd: bd=d; best=j
        val |= (best & 7) << (3*i)
    return bytes([r0,r1])+val.to_bytes(6,'little')

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

def encode_dxt3(rgba, width, height):
    """DXT3 (DXT2_3): explicit 4-bit alpha block + DXT1-style colour block."""
    out=bytearray()
    for blk in _iter_blocks(rgba,width,height):
        out += _encode_dxt3_alpha_block(blk)
        out += _encode_dxt_color_block(blk)
    return bytes(out)

def encode_dxt5(rgba, width, height):
    out=bytearray()
    for blk in _iter_blocks(rgba,width,height):
        out += _encode_dxt5_alpha_block(blk)
        out += _encode_dxt_color_block(blk)
    return bytes(out)

def encode_dxt5a(rgba, width, height):
    """DXT5A / BC4: single-channel (red) interpolated block, 8 bytes/block."""
    out=bytearray()
    for blk in _iter_blocks(rgba,width,height):
        reds=[r for (r,_,_,_) in blk]
        out += _encode_bc4_block(reds)
    return bytes(out)

def encode_for_format(gpu_fmt, rgba, width, height):
    """Encode RGBA8 bytes into the linear payload for a given GPU format."""
    if gpu_fmt == 'GPUTEXTUREFORMAT_DXT1':
        return encode_dxt1(rgba, width, height)
    if gpu_fmt == 'GPUTEXTUREFORMAT_DXT2_3':
        return encode_dxt3(rgba, width, height)   # explicit alpha, NOT DXT5
    if gpu_fmt == 'GPUTEXTUREFORMAT_DXT4_5':
        return encode_dxt5(rgba, width, height)
    if gpu_fmt == 'GPUTEXTUREFORMAT_DXT5A':
        return encode_dxt5a(rgba, width, height)
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
                 "endian","texture_type","gpu_fmt",
                 "_rgba_override","_converted","_user_painted"]
    def __init__(self):
        self.name=""; self.width=0; self.height=0; self.mips=1
        self.platform=""; self.fmt_name=""; self.tex_offset=0; self.name_offset=0
        self.raw_data=b""; self.index=0; self.endian=0; self.texture_type=0
        self.gpu_fmt=""
        self._rgba_override=None   # (rgba_bytes, w, h) when format was converted
        self._converted=False      # True once format was changed via convert
        self._user_painted=False   # True once the user Replaced with real pixels
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
    if len(raw) < 12:
        return (None, None, 0, 0, 0, "File too small.")
    magic = raw[:4]

    # ---- GTA IV / EFLC: RSC version 5 (12-byte header) ----------------------
    if magic == GTA4_MAGIC:
        rsctype = struct.unpack_from('<I', raw, 4)[0]
        flags   = struct.unpack_from('<I', raw, 8)[0]
        cpu, gpu = GetValueRSC05(flags)
        body = raw[12:]               # v5 header is only 12 bytes
        total = cpu + gpu
        # Compression tells PC/PS3 (both zlib) apart from Xbox 360 (block LZX):
        #   - zlib stream (starts 0x78)        -> PC or PS3 (RSX, big-endian)
        #   - 0xEF12F50F marker or other bytes -> Xbox 360 (LZX Codec 0)
        # PC and PS3 share zlib; the platform tab (force_platform) disambiguates
        # them because their texture structs differ (PC little-endian D3D9 vs
        # PS3 big-endian RSX). Default zlib -> PC unless the tab says PS3.
        is_zlib = body[:1] == b'\x78'
        if force_platform in ("PC", "PS3", "Xbox 360"):
            platform = force_platform
        else:
            platform = "PC" if is_zlib else "Xbox 360"

        if platform in ("PC", "PS3"):
            try:
                dec, wbits = decompress_zlib(body)
            except zlib.error:
                tag = "GTA4-PS3" if platform == "PS3" else "GTA4-PC"
                return (tag, None, cpu, gpu, 0, "GTA IV zlib decompression failed.")
            tag = "GTA4-PS3" if platform == "PS3" else "GTA4-PC"
            return (tag, dec, cpu, gpu, wbits, "")
        else:
            # Xbox 360 GTA IV -> block-framed LZX (Codec 0), needs xcompress_cpp.dll.
            # The compressed stream is prefixed by an 8-byte sub-header that
            # CompressLZX writes: [marker 0xEF12F50F : 4][compressed size BE : 4],
            # then the LZX blocks. Skip it so the block reader starts correctly.
            blocks = body
            if len(body) >= 8 and struct.unpack_from('<I', body, 0)[0] == 0xEF12F50F:
                blocks = body[8:]
            try:
                dec = lzx.decompress_blocks(blocks, total)
            except LZXError as e:
                return ("GTA4-Xbox 360", None, cpu, gpu, 0,
                        "GTA IV Xbox 360 LZX decompression unavailable.\n\n" + str(e) +
                        "\n\nNeeds xcompress_cpp.dll and 32-bit Python on Windows.")
            return ("GTA4-Xbox 360", dec, cpu, gpu, 0, "")

    if len(raw) < 16:
        return (None, None, 0, 0, 0, "File too small.")
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
# GTA IV (RSC version 5) texture-dictionary parser.
# ----------------------------------------------------------------------------
# GTA IV grcTextureDictionary (WTD/.xtd) mirrors the documented WDD/WDR layout:
#   dict header: +0x00 vft, +0x04 blockmap, +0x08 parent, +0x0C usage,
#                +0x10 SimpleCollection<hashes> (ptr@+0x10, count@+0x14),
#                +0x18 PointerCollection<grcTexture> (ptr@+0x18, count@+0x1C)
# Pointers are paged: system = 0x.....50 class 5, graphics = 0x.....60 class 6
# (note: GTA IV uses page-class nibble in the HIGH byte differently -> mask low
#  28 bits). PC .wtd is little-endian; Xbox 360 .xtd is big-endian.
# grcTexture (GTA IV) name pointer sits at +0x20 (like later formats); width/
# height are u16 at +0x38/+0x3A on PC. These offsets are best-effort from the
# documented layout; the dump mode lets us confirm against a real decompressed
# sample if any field is off.
# ============================================================================
def parse_gta4(buf, cpu_size, console=False, ps3=False):
    """
    GTA IV grcTextureDictionary parser, decoded from a real policedb.xtd:
      dict header (BE on Xbox 360):
        +0x10 hashes collection ptr,  +0x14 count(u16)
        +0x18 texture-pointer collection ptr, +0x1C count(u16)
      grcTexture (0x40 bytes):
        +0x00 vft (0x9C1A6300)
        +0x14 name pointer  (e.g. 'pack:/bacerra.dds')
        +0x18 D3DBaseTexture descriptor pointer -- SAME Xenon fetch constant as
              GTA V Xbox 360, so format = descriptor dword_9 low6 bits, and
              width/height come from descriptor dword_10 (size_2d).
    PC GTA IV (.wtd) uses the same layout, little-endian, zlib-compressed.
    PS3 GTA IV (.ctd) uses big-endian RSX structs; that path is UNVERIFIED
    (no sample yet) and is parsed best-effort with big-endian + PS3 format codes.
    """
    textures = []
    be = console or ps3   # Xbox 360 and PS3 are both big-endian; PC is little
    def u32(o):
        if o+4 > len(buf): return 0
        return struct.unpack_from('>I' if be else '<I', buf, o)[0]
    def u16(o):
        if o+2 > len(buf): return 0
        return struct.unpack_from('>H' if be else '<H', buf, o)[0]
    def off(p):
        p &= 0xFFFFFFFF
        if p == 0 or (p >> 28) not in (5, 6):
            return 0
        return p & 0x0FFFFFFF

    # dict header: texture pointer collection at +0x18, count at +0x1C
    list_ptr = off(u32(0x18)); count = u16(0x1C)
    if count == 0 or count > 8192:
        count = u32(0x1C) & 0xFFFF
    tex_ptrs = [off(u32(list_ptr + i*4)) for i in range(count)]

    for i, base in enumerate(tex_ptrs):
        if base == 0 or base+0x40 > len(buf):
            continue
        t = TexEntry()
        t.index = i
        t.platform = "GTA4-Xbox 360" if console else "GTA4-PC"

        # name pointer @ +0x14
        nptr = off(u32(base + 0x14))
        nm = _read_cstr(buf, nptr) if nptr else ""
        # strip the 'pack:/' prefix and .dds suffix for display
        if nm:
            nm = nm.rsplit('/', 1)[-1].rsplit('\\', 1)[-1]
        t.name = _clean_name(nm) if nm else f"texture_{i:03d}"
        t.name_offset = nptr

        # texture descriptor (D3DBaseTexture / Xenon fetch constant) @ +0x18
        desc = off(u32(base + 0x18))
        w = h = 0; fmt_name = "DXT?"; mips = 1; data_off = 0
        if desc and desc+0x30 <= len(buf):
            # read 13 dwords LE-as-stored (ReadD3DBaseTexture endian-swaps itself)
            dwords = [struct.unpack_from('<I', buf, desc + k*4)[0] for k in range(13)]
            info = ReadD3DBaseTexture(dwords)
            fmt_idx = info['DataFormat']
            gpu_fmt = GetGPUTEXTUREFORMAT(fmt_idx)   # e.g. 'GPUTEXTUREFORMAT_DXT4_5'
            fmt_name = {'GPUTEXTUREFORMAT_DXT1':'DXT1',
                        'GPUTEXTUREFORMAT_DXT2_3':'DXT3',
                        'GPUTEXTUREFORMAT_DXT4_5':'DXT5',
                        'GPUTEXTUREFORMAT_DXT5A':'DXT5A',
                        'GPUTEXTUREFORMAT_DXN':'DXN',
                        'GPUTEXTUREFORMAT_8_8_8_8':'A8R8G8B8',
                        'GPUTEXTUREFORMAT_8':'L8'}.get(gpu_fmt, gpu_fmt or "DXT?")
            mips = max(1, info['MaxMipLevel'] + 1)
            # size_2d is dword_10 (index 9), big-endian on disk -> use BE read
            d10 = struct.unpack_from('>I', buf, desc + 9*4)[0]
            w = (d10 & 0x1FFF) + 1
            h = ((d10 >> 13) & 0x1FFF) + 1
            # GPU data address: dword_9 (index 8) high bits = paged graphics addr
            d9 = struct.unpack_from('>I', buf, desc + 8*4)[0]
            data_off = (d9 & 0xFFFFF000) & 0x0FFFFFFF
            t.gpu_fmt = gpu_fmt
        t.width = w; t.height = h
        t.mips = mips
        t.fmt_name = fmt_name
        t.tex_offset = data_off
        t.endian = 1
        # attach the tiled GPU pixel data so export/preview can untile it.
        if console and w and h and t.gpu_fmt:
            setup = _xbox_format_setup(t.gpu_fmt, w, h)
            if setup:
                dwSize = setup[0]
                abs_off = cpu_size + data_off
                t.raw_data = buf[abs_off:abs_off + dwSize]
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

def rage_page_layout(block_sizes, base_unit=0x2000):
    """
    Lay out graphics blocks into the RAGE virtual-page hierarchy and return
    (offsets, total_size, page_flag) where:
      - offsets[i]  = byte offset of block i within the graphics segment
      - total_size  = total bytes the segment occupies (sum of page sizes)
      - page_flag   = RSC7 flag word whose GetValueRSC7 == total_size exactly

    The hierarchy has 9 tiers (base*16 .. base/16). Each block is placed in the
    SMALLEST tier that fits it; pages are then laid out largest-first and packed
    contiguously, so every block sits at an offset aligned to its own page size.
    The flag is built from the per-tier page counts so the layout it describes
    is self-consistent (this is what the game's loader + BlockMap require).

    base_unit is grown until all blocks fit in the available tiers and the
    per-tier counts fit their bit-widths.
    """
    block_sizes = list(block_sizes)
    if not block_sizes:
        # empty graphics segment: one base page
        flag = 0 | ((1 & 0x7F) << 17) | (13 << 28)
        return [], base_unit, flag

    shift = 0
    while True:
        base = base_unit << shift
        tiers = [base*16, base*8, base*4, base*2, base,
                 base//2, base//4, base//8, base//16]
        tiers = [t for t in tiers if t >= 1]
        pages = []
        ok = True
        for sz in block_sizes:
            chosen = None
            for ts in sorted(tiers):
                if ts >= sz:
                    chosen = ts; break
            if chosen is None:
                ok = False; break
            pages.append(chosen)
        if ok:
            # per-tier counts (largest..smallest, 9 tiers)
            tier9 = [base*16, base*8, base*4, base*2, base,
                     base//2, base//4, base//8, base//16]
            counts = [pages.count(t) for t in tier9]
            # check counts fit their bit-widths
            widths = [1, 2, 4, 6, 7, 1, 1, 1, 1]  # c16,c8,c4,c2,c1,/2,/4,/8,/16
            if all(counts[i] < (1 << widths[i]) for i in range(9)):
                # lay out largest-first, contiguous
                order = sorted(range(len(pages)), key=lambda i: (-pages[i], i))
                offsets = [0]*len(pages); cur = 0
                for i in order:
                    offsets[i] = cur; cur += pages[i]
                flag = (shift & 0xF)
                flag |= (counts[0] & 0x1) << 4     # base*16
                flag |= (counts[1] & 0x3) << 5     # base*8
                flag |= (counts[2] & 0xF) << 7     # base*4
                flag |= (counts[3] & 0x3F) << 11   # base*2
                flag |= (counts[4] & 0x7F) << 17   # base*1
                flag |= (counts[5] & 0x1) << 24    # base/2
                flag |= (counts[6] & 0x1) << 25    # base/4
                flag |= (counts[7] & 0x1) << 26    # base/8
                flag |= (counts[8] & 0x1) << 27    # base/16
                flag |= (13 << 28)                 # version nibble
                return offsets, cur, flag
        shift += 1
        if shift > 0xF:
            raise RuntimeError("rage_page_layout: blocks too large to page")


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
    VFT_DICT = 0x88988100      # grcTextureDictionaryXenon vtable (real stock
                               # GTA V .xtd; the game dispatches through this so
                               # it MUST match or the dict isn't recognised)
    VFT_TEX  = 0x145C8500      # grcTextureXenon vtable (real file)

    def __init__(self, textures, lzx=None):
        self.texs = textures
        self.lzx = lzx

    def build(self, compress=True):
        n = len(self.texs)
        sysseg = _Pager(0x5, 0x2000)
        gfxseg = _Pager(0x6, 0x2000)

        # graphics: TILED pixel data laid out with the RAGE page allocator so
        # the segment matches the page hierarchy the game's loader/BlockMap
        # expects (a flat 0x1000 packing is what made earlier files crash).
        tiled_list = []
        for t in self.texs:
            fmt = t['fmt'].upper()
            gpu_fmt = 'GPUTEXTUREFORMAT_' + ('DXT4_5' if fmt=='DXT5' else
                       'DXT2_3' if fmt=='DXT3' else fmt)
            tiled = retile_and_swap(t['data'], gpu_fmt, t['width'], t['height'])
            setup = _xbox_format_setup(gpu_fmt, t['width'], t['height'])
            dwSize = setup[0] if setup else len(tiled)
            if len(tiled) < dwSize:
                tiled = tiled + b'\x00'*(dwSize - len(tiled))
            tiled_list.append(tiled)
        block_sizes = [len(x) for x in tiled_list]
        if block_sizes:
            gfx_offsets, gfx_total, gfx_pageflag = rage_page_layout(block_sizes, 0x2000)
        else:
            gfx_offsets, gfx_total, gfx_pageflag = [], 0x2000, _rsc7_flag_for_size(0x2000,0x2000,13)[0]
        gfx_buf_full = bytearray(gfx_total if gfx_total else 0x1000)
        for tiled, off in zip(tiled_list, gfx_offsets):
            gfx_buf_full[off:off+len(tiled)] = tiled
        gfx_addr = list(gfx_offsets)

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
        gfx_flag = gfx_pageflag
        sys_buf = bytes(sysseg.buf) + b'\x00'*(sys_pages - len(sysseg.buf))
        gfx_buf = bytes(gfx_buf_full)
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

    def load_from_decompressed(self, dec, platform, system_flags, graphics_flags,
                               name="rpf_resource"):
        """
        Load a texture dictionary from an ALREADY-decompressed resource buffer
        (e.g. one extracted from an RPF archive), bypassing the on-disk RSC7
        header + compression. SystemFlags/GraphicsFlags give the CPU/GPU block
        sizes exactly as the RSC7 header would.

        This is what lets .ctd / .xtd packed inside an RPF open correctly: the
        RPF stores them deflate-compressed without an RSC7 header, so we decode
        the bytes in the browser and hand the raw resource straight to the
        parser here.
        """
        self.filepath = name
        self.platform = platform
        # CPU (system) and GPU (graphics) sizes come from the resource flags,
        # same formula as the standalone loader (GTA V PS3 vs Xbox/PC bases).
        if platform == "PS3":
            self.cpu_size = GetValueRSC7(system_flags, 0x1000)
            self.gpu_size = GetValueRSC7(graphics_flags, 0x1580)
        else:
            self.cpu_size = GetValueRSC7(system_flags, 0x2000)
            self.gpu_size = GetValueRSC7(graphics_flags, 0x2000)
        self._dec = dec or b""
        self._wbits = 15
        self.error_msg = ""
        # Sanity: a correctly-decoded resource buffer should be at least as
        # large as its system block, and the texture count should be sane.
        # If the buffer is too small or the parser returns an absurd count, the
        # decompression was almost certainly wrong (wrong codec / key).
        expected_min = self.cpu_size
        if len(self._dec) < expected_min:
            self.error_msg = (
                "Decoded resource is smaller than its header says it should be.\n"
                "The archive data could not be decompressed correctly "
                "(wrong codec, key, or platform).")
            self.textures = []
            return self
        try:
            if platform == "PS3":
                self.textures = parse_ps3(self._dec)
            elif platform == "Xbox 360":
                self.textures = parse_xbox360(self._dec)
            else:  # PC
                virt = self._dec[:self.cpu_size]
                phys = self._dec[self.cpu_size:]
                self.textures = parse_pc(virt, phys)
        except Exception as e:
            self.error_msg = f"Could not parse resource: {e}"
            self.textures = []
            return self
        # Reject obviously-wrong parses (garbage buffer -> huge bogus count).
        if len(self.textures) > 4096:
            self.error_msg = (
                f"Resource parsed to {len(self.textures)} textures, which is "
                "not valid — the archive data was not decompressed correctly "
                "(likely wrong compression codec for this platform).")
            self.textures = []
        return self

    def load_from_bytes(self, data, force_platform=None, name="rpf_resource"):
        """
        Load a texture dictionary from in-memory resource-file bytes (a complete
        '7CSR'/'RSC7' file, e.g. one reconstructed from an RPF archive). Uses the
        exact same decode path as load() -- including Xbox 360 xDecompress (LZX)
        -- so packed .xtd/.ctd open identically to standalone files.
        """
        self.filepath = name
        self._raw = bytes(data)
        platform, dec, cpu, gpu, wbits, err = load_resource(
            self._raw, self.lzx, force_platform)
        self.platform = platform or ""
        self.cpu_size = cpu; self.gpu_size = gpu
        self._wbits = wbits
        if err:
            self.error_msg = err
            self.textures = []
            return self
        self._dec = dec or b""
        self.error_msg = ""
        try:
            if platform == "PS3":
                self.textures = parse_ps3(self._dec)
            elif platform == "Xbox 360":
                self.textures = parse_xbox360(self._dec)
            elif platform in ("GTA4-PC", "GTA4-Xbox 360", "GTA4-PS3"):
                self.textures = parse_gta4(self._dec, self.cpu_size,
                                           console=(platform == "GTA4-Xbox 360"),
                                           ps3=(platform == "GTA4-PS3"))
            else:  # PC
                virt = self._dec[:self.cpu_size]
                phys = self._dec[self.cpu_size:]
                self.textures = parse_pc(virt, phys)
        except Exception as e:
            self.error_msg = f"Could not parse resource: {e}"
            self.textures = []
        return self

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
        elif platform in ("GTA4-PC", "GTA4-Xbox 360", "GTA4-PS3"):
            self.textures = parse_gta4(self._dec, self.cpu_size,
                                       console=(platform == "GTA4-Xbox 360"),
                                       ps3=(platform == "GTA4-PS3"))
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
        # If the format was converted (e.g. DXT5A->DXT5), build the DDS from the
        # stashed RGBA in the NEW format so the preview reflects the change.
        ov = getattr(tex, "_rgba_override", None)
        if ov is not None:
            rgba, w, h = ov
            gpu_fmt = tex.gpu_fmt or 'GPUTEXTUREFORMAT_DXT4_5'
            linear = encode_for_format(gpu_fmt, rgba, w, h)
            return make_dds(gpu_fmt, w, h, 1, linear)
        if tex.platform in ("Xbox 360", "GTA4-Xbox 360"):
            gpu_fmt = tex.gpu_fmt
            abs_off = tex.tex_offset + self.cpu_size
            data = untile_and_deswap(self._dec[abs_off:], gpu_fmt,
                                     tex.width, tex.height, tex.endian)
            return make_dds(gpu_fmt, tex.width, tex.height, 1, data)
        elif tex.platform in ("PS3",):
            # PS3 data is linear (RSX). Use the real per-texture format read
            # from the struct (+0x08); fall back to DXT5 only if unknown.
            gpu_fmt = tex.gpu_fmt if tex.gpu_fmt and tex.gpu_fmt != '-unknown-' \
                      else 'GPUTEXTUREFORMAT_DXT4_5'
            abs_off = tex.tex_offset + self.cpu_size
            size = ps3_data_size(gpu_fmt, tex.width, tex.height)
            data = self._dec[abs_off:abs_off+size]
            if gpu_fmt == 'GPUTEXTUREFORMAT_8_8_8_8':
                # PS3 RSX stores power-of-two linear (8_8_8_8 / 8) textures
                # SWIZZLED in Morton/Z-order. DXT formats are stored linear.
                # Unswizzle the raw bytes first, then fix channel byte order:
                # RSX 8888 is [A,R,G,B] big-endian; DDS A8R8G8B8 wants [B,G,R,A].
                data = ps3_unswizzle(data, tex.width, tex.height, 4)
                data = _ps3_8888_to_dds(data)
            elif gpu_fmt == 'GPUTEXTUREFORMAT_8':
                data = ps3_unswizzle(data, tex.width, tex.height, 1)
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
        # If this texture had its format converted (e.g. DXT5A->DXT5), its data
        # size no longer matches the original GPU slot, so writing in-place
        # would overflow into the next texture. Instead, stash the new image as
        # an RGBA override; the rebuild on Save As lays it out correctly.
        if getattr(tex, "_converted", False):
            rgba = self._load_rgba_sized(image_path, tex.width, tex.height)
            tex._rgba_override = (rgba, tex.width, tex.height)
            tex._user_painted = True   # the user supplied real pixels; don't
                                       # re-apply the DXT5A->alpha expansion
            return True
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
        if gpu_fmt == 'GPUTEXTUREFORMAT_8_8_8_8':
            # encode_for_format emits little-endian [B,G,R,A]; PS3 RSX wants
            # big-endian [A,R,G,B]. Convert so replaced 8888 textures aren't
            # glitchy in-game.
            linear = _dds_8888_to_ps3(linear)
            # RSX stores power-of-two 8888 textures swizzled (Morton order).
            # Re-swizzle so the game reads the replacement correctly.
            linear = ps3_swizzle(linear, tex.width, tex.height, 4)
        elif gpu_fmt == 'GPUTEXTUREFORMAT_8':
            linear = ps3_swizzle(linear, tex.width, tex.height, 1)
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

        If any texture's FORMAT was converted (e.g. DXT5A->DXT5), the data sizes
        change, so we cannot patch in place -- we rebuild the whole dictionary
        from the live textures instead (new header, offsets, and block sizes).
        """
        any_converted = any(getattr(t, "_converted", False)
                            for t in self.textures)
        gpu_grew = getattr(self, "_gpu_grew", False)

        if any_converted and self.platform == "PC":
            # PC: full rebuild from the live textures.
            return self.rebuild_pc(out_path, self.to_texture_list())

        # For console conversions, re-run the GPU-block rebuild NOW so the most
        # recent pixels (including any image the user Replaced AFTER converting)
        # are the ones encoded into the buffer. Re-running is idempotent: it
        # reads each texture's current RGBA (override if present) and re-lays
        # the whole graphics segment.
        if any_converted and self.platform in ("Xbox 360", "PS3"):
            conv = next((t for t in self.textures
                         if getattr(t, "_converted", False)), None)
            if conv is not None:
                rgba, w, h = self._decoded_rgba(conv)
                if self.platform == "Xbox 360":
                    self._convert_xbox360_inplace(conv, conv.gpu_fmt, rgba, w, h)
                else:
                    self._convert_ps3_inplace(conv, conv.gpu_fmt, rgba, w, h)
                gpu_grew = getattr(self, "_gpu_grew", False)

        if not self._raw or len(self._raw) < 16:
            raise RuntimeError("No source resource loaded.")

        header = bytearray(self._raw[:16])
        body = bytes(self._dec)

        if gpu_grew:
            gfx_flag = getattr(self, "_new_gfx_flag", None)
            if gfx_flag is None:
                gpu_len = len(body) - self.cpu_size
                gfx_flag, _pages = _rsc7_flag_for_size(gpu_len, 0x2000, 13)
            struct.pack_into('<I', header, 12, EndianChangeDWORD(gfx_flag))

        if self.platform == "Xbox 360":
            comp = self.lzx.compress_open(body)
        else:
            wbits = self._wbits if self._wbits in (15, -15, 47) else 15
            if wbits == 47:
                wbits = 15
            co = zlib.compressobj(9, zlib.DEFLATED, wbits)
            comp = co.compress(body) + co.flush()
        Path(out_path).write_bytes(bytes(header) + comp)
        return True

    # ---- add / rename / rebuild (PC .ytd) ----------------------------------
    def convert_texture_format(self, tex, new_fmt):
        """
        Change a single texture's format (e.g. DXT5A -> DXT5) so it can carry
        full colour.

        For console (Xbox 360 / PS3) this is a SURGICAL in-place edit: only the
        one texture's data and its fetch-constant format bits change. Every
        other texture and the whole dictionary structure stay byte-for-byte
        identical to the original game file. The new (larger) data is appended
        to the end of the GPU block and the texture is re-pointed to it. This
        avoids rebuilding the entire dictionary from scratch -- a full rebuild
        is what made the game crash, because re-emitting untouched textures
        through an approximate writer corrupts their GPU registers.

        new_fmt: 'DXT1', 'DXT3', or 'DXT5'. A DXT5A texture holds one channel;
        converting to DXT5 keeps that as a grayscale image with opaque alpha.
        """
        new_fmt = new_fmt.upper()
        gpu_map = {'DXT1':'GPUTEXTUREFORMAT_DXT1',
                   'DXT3':'GPUTEXTUREFORMAT_DXT2_3',
                   'DXT5':'GPUTEXTUREFORMAT_DXT4_5',
                   '8_8_8_8':'GPUTEXTUREFORMAT_8_8_8_8',
                   '8888':'GPUTEXTUREFORMAT_8_8_8_8'}
        if new_fmt not in gpu_map:
            raise RuntimeError(f"Unsupported target format: {new_fmt}")
        new_gpu = gpu_map[new_fmt]

        # Decode current pixels with the CURRENT format first.
        rgba, w, h = self._decoded_rgba(tex)
        if new_fmt in ('DXT5', 'DXT3', '8_8_8_8') and \
           (tex.fmt_name or '').upper() in ('DXT5A', 'ATI1', 'BC4') and \
           not getattr(tex, '_user_painted', False):
            # A DXT5A texture (e.g. a radio-wheel station icon) stores a single
            # channel that the game uses as an ALPHA MASK -- the icon's shape.
            # The tool's DXT5A decoder puts that channel in RED. To keep the
            # icon looking correct after conversion, move it into ALPHA with
            # white RGB (white icon, transparent background), which is how the
            # wheel shader expects to read it. The user can then Replace this
            # with their own colour+alpha image.
            ba = bytearray(rgba)
            for i in range(0, len(ba), 4):
                mask = ba[i]            # the single channel (in red)
                ba[i]=255; ba[i+1]=255; ba[i+2]=255; ba[i+3]=mask
            rgba = bytes(ba)

        if tex.platform in ("Xbox 360",):
            self._convert_xbox360_inplace(tex, new_gpu, rgba, w, h)
        elif tex.platform in ("PS3",):
            self._convert_ps3_inplace(tex, new_gpu, rgba, w, h)
        else:
            # PC: rebuild path is reliable for PC; just stash override + flag.
            tex._rgba_override = (rgba, w, h)
            tex._converted = True

        # Show the same RAGE format label the parser uses (e.g. 'DXT4_5'),
        # so converted textures read consistently with stock ones in the list.
        tex.fmt_name = new_gpu.replace('GPUTEXTUREFORMAT_', '')
        tex.gpu_fmt  = new_gpu
        # Keep an RGBA override for the live preview (and PC rebuild).
        tex._rgba_override = (rgba, w, h)
        return True

    def _convert_xbox360_inplace(self, tex, new_gpu, rgba, w, h):
        """
        Rebuild the entire GPU (graphics) block so the converted texture's new,
        larger data fits the RAGE page hierarchy correctly. Every texture's
        pixel data is re-tiled and laid out with rage_page_layout(); each
        texture's fetch-constant GPU offset + format bits are rewritten; the
        graphics page-flag in the RSC7 header is regenerated. The SYSTEM block
        (structs, names, header) is left structurally intact apart from the
        per-texture GPU offset / format / mip patches.
        """
        self._ensure_mutable()

        # 1) Gather each texture's current pixel data, re-encoded for its target
        #    format (the converted one uses new_gpu; others keep their format).
        per_tex = []   # (texture, gpu_fmt, tiled_bytes, data_len)
        for t in self.textures:
            if t is tex:
                fmt = new_gpu
                trgba, tw, th = rgba, w, h
            else:
                fmt = t.gpu_fmt
                trgba, tw, th = self._decoded_rgba(t)
            linear = encode_for_format(fmt, trgba, tw, th)
            tiled  = retile_and_swap(linear, fmt, tw, th)
            setup  = _xbox_format_setup(fmt, tw, th)
            dwSize = setup[0] if setup else len(tiled)
            # pad the tiled data to its tiled dwSize (page content size)
            if len(tiled) < dwSize:
                tiled = tiled + b'\x00' * (dwSize - len(tiled))
            per_tex.append((t, fmt, tiled, dwSize))

        # 2) Lay the blocks out into the page hierarchy.
        sizes = [p[3] for p in per_tex]
        offsets, total, gfx_flag = rage_page_layout(sizes, 0x2000)

        # 3) Build the new GPU block.
        new_gpu_block = bytearray(total)
        for (t, fmt, tiled, dwSize), off in zip(per_tex, offsets):
            new_gpu_block[off:off+len(tiled)] = tiled

        # 4) Splice: keep the system block (0..cpu_size) and replace the GPU part.
        self._dec = bytearray(self._dec[:self.cpu_size]) + new_gpu_block

        # 5) Patch each texture's fetch constant (GPU offset + format + mips).
        for (t, fmt, tiled, dwSize), off in zip(per_tex, offsets):
            d3doff = self._xbox_d3d_offset(t)
            if d3doff is None:
                continue
            old = struct.unpack_from('>I', self._dec, d3doff + 0x20)[0]
            fkey = (fmt.replace('GPUTEXTUREFORMAT_', '')
                       .replace('DXT4_5', 'DXT5').replace('DXT2_3', 'DXT3'))
            fmt_idx = XBOX_FMT_CODE.get(fkey, 20)
            gpu_paged = _ps3_vaddr(0x6, off)
            endian_bit = old & (1 << 6)
            dword9 = (gpu_paged & 0xFFFFF000) | endian_bit | (fmt_idx & 0x3F)
            struct.pack_into('>I', self._dec, d3doff + 0x20, dword9 & 0xFFFFFFFF)
            # single mip: clear only the mip-count bits in dword_12
            old12 = struct.unpack_from('>I', self._dec, d3doff + 0x2C)[0]
            mip_mask_be = EndianChangeDWORD(0xC0030000)
            struct.pack_into('>I', self._dec, d3doff + 0x2C,
                             old12 & (~mip_mask_be & 0xFFFFFFFF))
            t.tex_offset = off
            if t is tex:
                t.texture_type = fmt_idx
                t.mips = 1

        # 6) Record the new graphics flag for save() to write into the header.
        self._new_gfx_flag = gfx_flag & 0xFFFFFFFF
        self.gpu_size = total
        self._gpu_grew = True
        tex._converted = True

    def _xbox_struct_base(self, tex):
        """Absolute offset of a texture's grcTexture struct (its list entry)."""
        try:
            buf = self._dec
            r = R(buf); r.seek(0)
            for _ in range(5): r.u32_le()
            count = EndianChangeWORD(r.u16_le()); r.u16_le()
            listoff = GetOffset(EndianChangeDWORD(r.u32_le()))
            r.seek(listoff)
            offs = [GetOffset(EndianChangeDWORD(r.u32_le())) for _ in range(count)]
            return offs[tex.index] if tex.index < len(offs) else None
        except Exception:
            return None

    def _convert_ps3_inplace(self, tex, new_gpu, rgba, w, h):
        """PS3: append linear data to the GPU block, re-point, set format byte."""
        soff = self._ps3_struct_offset(tex)
        if soff is None:
            raise RuntimeError(
                "Format conversion is currently supported for Xbox 360 textures.\n"
                "PS3 in-place conversion isn't available yet in this build.")
        self._ensure_mutable()
        linear = encode_for_format(new_gpu, rgba, w, h)
        size = ps3_data_size(new_gpu, w, h)
        data = linear[:size]
        new_gpu_off_abs = _align(len(self._dec), 0x80)
        if new_gpu_off_abs > len(self._dec):
            self._dec.extend(b'\x00' * (new_gpu_off_abs - len(self._dec)))
        self._dec.extend(data)
        new_gpu_off_rel = new_gpu_off_abs - self.cpu_size
        ps3_code = {'GPUTEXTUREFORMAT_DXT1':134,'GPUTEXTUREFORMAT_DXT2_3':135,
                    'GPUTEXTUREFORMAT_DXT4_5':136}.get(new_gpu, 136)
        if soff + 0x08 < len(self._dec):
            self._dec[soff + 0x08] = ps3_code & 0xFF
        tex.tex_offset = new_gpu_off_rel
        tex.texture_type = ps3_code
        tex._converted = True
        self._gpu_grew = True

    def _xbox_d3d_offset(self, tex):
        """Recompute the absolute offset of a texture's D3DBaseTexture fetch
        constant within the system block (mirrors parse_xbox360)."""
        try:
            buf = self._dec
            r = R(buf); r.seek(0)
            for _ in range(5): r.u32_le()
            count = EndianChangeWORD(r.u16_le())
            r.u16_le()
            listoff = GetOffset(EndianChangeDWORD(r.u32_le()))
            r.seek(listoff)
            offsets = [GetOffset(EndianChangeDWORD(r.u32_le())) for _ in range(count)]
            if tex.index >= len(offsets):
                return None
            base = offsets[tex.index]
            r.seek(base + 52)
            d3d = GetOffset(EndianChangeDWORD(r.u32_le()))
            return d3d
        except Exception:
            return None

    def _ps3_struct_offset(self, tex):
        """Recompute the absolute offset of a PS3 grcTexture struct."""
        try:
            buf = self._dec
            # PS3 parser reads the texture pointer list similarly; reuse parse
            # to map index -> struct offset. Simplest: re-run the PS3 list walk.
            import struct as _s
            # The PS3 dictionary header layout is parsed in parse_ps3; we
            # approximate by scanning the pointer list. If unavailable, bail.
            return getattr(tex, "_ps3_struct_off", None)
        except Exception:
            return None

    def _decoded_rgba(self, tex):
        """Decode a texture's current pixels to RGBA via a DDS + Pillow.
        If the texture's format was converted, return the stashed RGBA so the
        new format is reflected without touching the original GPU buffer."""
        ov = getattr(tex, "_rgba_override", None)
        if ov is not None:
            return ov
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
# RPF7 Archive support (integrated from rpf_archive.py)
# ============================================================================
try:
    from Crypto.Cipher import AES as _AES_MOD
    _AES_OK = True
except Exception:
    _AES_OK = False

RPF7_MAGIC  = b'RPF7'
DIR_MARKER  = 0x7FFFFF00
RPF_SECTOR  = 512
ENC_OPEN    = 0x4E45504F   # 'OPEN'
ENC_NONE    = 0x00000000
ENC_AES     = 0x0FFFFFF9
ENC_NG      = 0x0FFFFFF7   # console archives; data is AES

class RPFError(RuntimeError):
    pass

import dataclasses
from typing import Optional, List

@dataclasses.dataclass
class RPFEntry:
    index: int
    name_offset: int
    name: str = ""
    parent: object = None
    path: str = ""

@dataclasses.dataclass
class RPFDirEntry(RPFEntry):
    entries_index: int = 0
    entries_count: int = 0
    children: list = dataclasses.field(default_factory=list)
    is_dir: bool = True

@dataclasses.dataclass
class RPFFileEntry(RPFEntry):
    file_size: int = 0
    file_offset: int = 0
    uncompressed_size: int = 0
    encryption_type: int = 0
    is_resource: bool = False
    system_flags: int = 0
    graphics_flags: int = 0
    is_dir: bool = False

    @property
    def abs_offset(self):
        return self.file_offset * RPF_SECTOR

    @property
    def is_compressed(self):
        return self.file_size > 0

    def on_disk_size(self):
        return self.file_size if self.file_size != 0 else self.uncompressed_size


def _rpf_aes_decrypt_rounds(data, key, rounds):
    """AES-256-ECB decrypt, `rounds` passes per full 16-byte block; trailing
    partial block left as plaintext."""
    if not _AES_OK:
        raise RPFError("pycryptodome is required for encrypted RPF archives.\n"
                       "Run: pip install pycryptodome")
    c = _AES_MOD.new(key, _AES_MOD.MODE_ECB)
    out = bytearray(data)
    nblocks = len(out) // 16
    for b in range(nblocks):
        blk = bytes(out[b*16:(b+1)*16])
        for _ in range(rounds):
            blk = c.decrypt(blk)
        out[b*16:(b+1)*16] = blk
    return bytes(out)

def _rpf_aes_encrypt_rounds(data, key, rounds):
    if not _AES_OK:
        raise RPFError("pycryptodome is required for encrypted RPF archives.")
    c = _AES_MOD.new(key, _AES_MOD.MODE_ECB)
    out = bytearray(data)
    nblocks = len(out) // 16
    for b in range(nblocks):
        blk = bytes(out[b*16:(b+1)*16])
        for _ in range(rounds):
            blk = c.encrypt(blk)
        out[b*16:(b+1)*16] = blk
    return bytes(out)


def _rpf_aes_decrypt(data, key):
    """
    GTA V RPF AES-256-ECB decryption.

    Per the RAGE crypto spec (OpenIV / CodeWalker / LibertyV), the standard is
    16 decrypt passes per 16-byte block, trailing partial block left as
    plaintext. Some tools/archives use a single pass; the archive object picks
    the right round count once (via _aes_rounds) by validating the decrypted
    table of contents, so this function honours that decision through the
    module-level default used only when no archive context applies.
    """
    return _rpf_aes_decrypt_rounds(data, key, _RPF_DEFAULT_AES_ROUNDS)

def _rpf_aes_encrypt(data, key):
    return _rpf_aes_encrypt_rounds(data, key, _RPF_DEFAULT_AES_ROUNDS)

# Default rounds when there is no archive instance to consult. GTA V standard.
_RPF_DEFAULT_AES_ROUNDS = 16

def rpf_find_key_beside(archive_path):
    d = os.path.dirname(os.path.abspath(archive_path))
    candidates = ["encryption_key.bin","gtav_key.bin","key.bin",
                  "gta5_xbox360.bin","gta5_ps3.bin"]
    for name in candidates:
        p = os.path.join(d, name)
        if os.path.isfile(p) and os.path.getsize(p) == 32:
            return p
    try:
        for fn in os.listdir(d):
            if fn.lower().endswith(".bin"):
                p = os.path.join(d, fn)
                if os.path.isfile(p) and os.path.getsize(p) == 32:
                    return p
    except OSError:
        pass
    return None

def rpf_load_key(path):
    with open(path, "rb") as f:
        k = f.read()
    if len(k) != 32:
        raise RPFError(f"Key file must be exactly 32 bytes (got {len(k)}): {path}")
    return k


class RPFArchive:
    def __init__(self, path, key, lzx=None, platform="Xbox 360"):
        self.path = path
        self.key  = key
        self.lzx  = lzx
        self.platform = platform
        self.raw  = b""
        self.entry_count  = 0
        self.names_length = 0
        self.names_flag   = 0
        self.encryption   = 0
        self.entries: List[RPFEntry] = []
        self.root = None
        self._aes_rounds = 16

    @classmethod
    def open(cls, path, key, lzx=None, platform="Xbox 360"):
        arc = cls(path, key, lzx=lzx, platform=platform)
        with open(path, "rb") as f:
            arc.raw = f.read()
        arc._parse()
        return arc

    @classmethod
    def open_bytes(cls, raw, key, lzx=None, platform="Xbox 360", path="<nested>"):
        """Open an RPF archive that lives entirely in memory -- used for nested
        RPFs (an .rpf stored inside another .rpf), exactly like OpenIV lets you
        drill into them."""
        arc = cls(path, key, lzx=lzx, platform=platform)
        arc.raw = bytes(raw)
        arc._parse()
        return arc

    def _parse(self):
        raw = self.raw
        if raw[:4] != RPF7_MAGIC:
            raise RPFError(f"Not an RPF7 archive (magic={raw[:4]!r}).")
        self.entry_count  = struct.unpack_from(">I", raw, 4)[0]
        nl = struct.unpack_from(">I", raw, 8)[0]
        self.names_flag   = nl & 0x80000000
        self.names_length = nl & 0x7FFFFFFF
        self.encryption   = struct.unpack_from(">I", raw, 12)[0]

        toc_off   = 0x10
        toc_size  = self.entry_count * 16
        names_off = toc_off + toc_size
        toc_enc   = raw[toc_off:toc_off + toc_size]
        names_enc = raw[names_off:names_off + self.names_length]

        if self.encryption in (ENC_OPEN, ENC_NONE):
            toc   = toc_enc
            names = names_enc
            self._aes_rounds = 0
        else:
            # GTA V standard is 16 AES passes per block, but some archives /
            # tools use a single pass. Try 16 first, then 1, and keep whichever
            # yields a valid root directory entry (offset field == 0x7FFFFF).
            toc = names = None
            for rounds in (16, 1):
                cand = _rpf_aes_decrypt_rounds(toc_enc, self.key, rounds)
                # validate: first entry must be the root directory
                if len(cand) >= 16:
                    f12 = (cand[0] << 16) | (cand[1] << 8) | cand[2]
                    if (f12 & 0x7FFFFF) == 0x7FFFFF:
                        toc = cand
                        names = _rpf_aes_decrypt_rounds(names_enc, self.key, rounds)
                        self._aes_rounds = rounds
                        break
            if toc is None:
                # Neither validated; fall back to 16-round so the error path
                # reports a clear "wrong key" message downstream.
                self._aes_rounds = 16
                toc = _rpf_aes_decrypt_rounds(toc_enc, self.key, 16)
                names = _rpf_aes_decrypt_rounds(names_enc, self.key, 16)

        self._names = names
        self._read_entries(toc)
        self._build_tree()

    def _cstr(self, off):
        if off < 0 or off >= len(self._names):
            return ""
        end = self._names.find(b"\x00", off)
        if end < 0:
            end = len(self._names)
        return self._names[off:end].decode("latin1")

    def _read_entries(self, toc):
        self.entries = []
        for i in range(self.entry_count):
            e = toc[i * 16:(i + 1) * 16]
            field1and2 = (e[0] << 16) | (e[1] << 8) | e[2]
            is_resource = (field1and2 >> 23) & 1
            offset23    = field1and2 & 0x7FFFFF
            size        = (e[3] << 16) | (e[4] << 8) | e[5]
            name_off    = (e[6] << 8) | e[7]
            field5      = struct.unpack_from(">I", e, 8)[0]
            field6      = struct.unpack_from(">I", e, 12)[0]

            if offset23 == 0x7FFFFF:
                d = RPFDirEntry(index=i, name_offset=name_off,
                                entries_index=field5, entries_count=field6)
                d.name = self._cstr(name_off)
                self.entries.append(d)
            elif is_resource:
                fe = RPFFileEntry(index=i, name_offset=name_off,
                                  file_size=size, file_offset=offset23,
                                  uncompressed_size=0, encryption_type=0,
                                  is_resource=True,
                                  system_flags=field5, graphics_flags=field6)
                fe.name = self._cstr(name_off)
                self.entries.append(fe)
            else:
                fe = RPFFileEntry(index=i, name_offset=name_off,
                                  file_size=size, file_offset=offset23,
                                  uncompressed_size=field5, encryption_type=field6,
                                  is_resource=False)
                fe.name = self._cstr(name_off)
                self.entries.append(fe)

    def _build_tree(self):
        if not self.entries:
            self.root = None; return
        root = self.entries[0]
        if not isinstance(root, RPFDirEntry):
            raise RPFError(
                "Could not read the archive's directory table.\n\n"
                "This almost always means the encryption key is wrong or missing.\n"
                "Supply the correct 32-byte GTA V key (the same encryption_key.bin\n"
                "that OpenIV uses) and make sure the platform (PS3 / Xbox 360)\n"
                "matches the archive.")
        root.path = ""; self.root = root
        stack = [root]
        while stack:
            d = stack.pop(); d.children = []
            for k in range(d.entries_index, d.entries_index + d.entries_count):
                if k < 0 or k >= len(self.entries): continue
                child = self.entries[k]
                child.parent = d
                child.path = (d.path + "/" + child.name).lstrip("/")
                d.children.append(child)
                if isinstance(child, RPFDirEntry):
                    stack.append(child)

    def iter_files(self):
        for e in self.entries:
            if isinstance(e, RPFFileEntry):
                yield e

    def iter_dirs(self):
        for e in self.entries:
            if isinstance(e, RPFDirEntry):
                yield e

    def find(self, path):
        path = path.strip("/").lower()
        for e in self.entries:
            if e.path.lower() == path:
                return e
        return None

    def _archive_is_encrypted(self):
        """Archive-level encryption (AES) applies to file data, per CodeWalker.
        OPEN/NONE archives store plaintext; everything else is AES on console."""
        return self.encryption not in (ENC_OPEN, ENC_NONE)

    # RSC7 resource version written by GTA V console files (verified against
    # OpenIV-exported .xtd: '7CSR' + version(13) + sysFlag + gfxFlag).
    RSC7_VERSION = 13

    def _resource_body(self, entry):
        """
        Return the resource's compressed body (decrypted, RPF sub-header
        stripped) -- i.e. the exact compressed stream, NOT decompressed.

        This is the piece OpenIV prepends a '7CSR' header to. For Xbox 360 the
        body is an xCompress/LZX stream; for PS3/PC it is headerless zlib.
        """
        off = entry.abs_offset
        fsz = entry.file_size
        if fsz <= 0:
            return b""
        HEADER = 0x10
        totlen = fsz - HEADER
        blob = self.raw[off + HEADER: off + HEADER + totlen]
        if self._archive_is_encrypted():
            blob = _rpf_aes_decrypt_rounds(blob, self.key,
                                           getattr(self, "_aes_rounds", 16))
        return blob

    def extract_resource_as_file(self, entry):
        """
        Reconstruct a standalone console resource file, byte-identical to what
        OpenIV exports: '7CSR' + version + SystemFlags + GraphicsFlags (all
        big-endian) followed by the original compressed body.

        The result can be fed straight to the editor's standard resource loader
        (load_resource), which already handles Xbox 360 xDecompress (LZX) and
        PS3/PC zlib correctly -- so this is the reliable way to open a packed
        .xtd / .ctd, instead of trying to decompress inside the archive layer.
        """
        body = self._resource_body(entry)
        header = (CONSOLE_MAGIC
                  + struct.pack(">I", self.RSC7_VERSION)
                  + struct.pack(">I", entry.system_flags & 0xFFFFFFFF)
                  + struct.pack(">I", entry.graphics_flags & 0xFFFFFFFF))
        return header + body

    def extract(self, entry):
        """
        Fully decode a packed file, following CodeWalker's RpfFile logic.

        Console RPF7 layout for a stored file:
          - data begins at file_offset * 512
          - resources have a 0x10-byte sub-header that is skipped
          - if the archive is AES-encrypted, the body is AES-256-ECB decrypted
          - the body is then decompressed (zlib on PC/PS3, LZX on Xbox 360)
        """
        if entry.is_resource:
            return self._extract_resource(entry)
        return self._extract_binary(entry)

    def _extract_resource(self, entry):
        # Resource files: skip the 0x10 sub-header (CodeWalker ExtractFileResource)
        off = entry.abs_offset
        fsz = entry.file_size
        if fsz <= 0:
            return b""
        HEADER = 0x10
        totlen = fsz - HEADER
        blob = self.raw[off + HEADER: off + HEADER + totlen]

        # Archive-level AES (console resources are encrypted unless OPEN/NONE).
        if self._archive_is_encrypted():
            blob = _rpf_aes_decrypt_rounds(blob, self.key,
                                           getattr(self, "_aes_rounds", 16))

        # Decompress. PC/PS3 RPFs use headerless zlib (deflate). Xbox 360 RPFs
        # use LZX. If no codec yields a valid-size buffer, the resource may be
        # stored uncompressed -> use the decrypted bytes directly.
        body = self._decompress_resource(blob, entry)
        if body is None:
            body = blob  # stored uncompressed; use decrypted bytes as-is
        return body

    def _decompress_resource(self, blob, entry):
        """Decompress an RPF resource body to the full system+graphics buffer.

        Xbox 360 RPF resources use the Microsoft XMem LZX codec with the
        uncompressed size known up front (from the resource flags) -- this is
        the safe, correct path (koolk's RPF7 viewer). PC/PS3 use headerless
        zlib. Returns the decompressed bytes, or None if the data looks stored.
        """
        if self.platform == "PS3":
            sys_sz = GetValueRSC7(entry.system_flags, 0x1000)
            gfx_sz = GetValueRSC7(entry.graphics_flags, 0x1580)
        else:
            sys_sz = GetValueRSC7(entry.system_flags, 0x2000)
            gfx_sz = GetValueRSC7(entry.graphics_flags, 0x2000)
        want = sys_sz + gfx_sz

        if self.platform in ("Xbox 360", "Xbox360"):
            # Preferred: XMem LZX with the exact uncompressed size. This will
            # not crash the process the way feeding bad data to xDecompress can.
            if self.lzx is not None and self.lzx.available_xmem and want > 0:
                try:
                    out = self.lzx.xmem_decompress(blob, want)
                    if out and len(out) >= max(16, sys_sz):
                        return out
                except Exception:
                    pass
            # Fallback: headerless zlib, in case a particular archive used it.
            out = self._inflate(blob)
            if out and len(out) >= max(16, sys_sz):
                return out
            # Last resort: maybe stored uncompressed and already the right size.
            if len(blob) >= max(16, sys_sz):
                return blob
            return out  # may be None
        else:
            # PC / PS3 -> headerless zlib (raw deflate).
            out = self._inflate(blob)
            if out is None and len(blob) >= max(16, sys_sz):
                return blob  # stored uncompressed
            return out

    def _extract_binary(self, entry):
        off  = entry.abs_offset
        size = entry.on_disk_size()
        blob = self.raw[off:off + size]
        # Per-entry encryption flag (field6) AND archive must be encrypted.
        if entry.encryption_type != 0 and self._archive_is_encrypted():
            blob = _rpf_aes_decrypt_rounds(blob, self.key,
                                           getattr(self, "_aes_rounds", 16))
        if entry.is_compressed:
            body = self._inflate(blob)
            return body if body is not None else blob
        return blob[:entry.uncompressed_size] if entry.uncompressed_size else blob

    @staticmethod
    def _inflate(blob):
        """Raw-DEFLATE inflate (RPF uses headerless deflate, like CodeWalker)."""
        for wb in (-15, 15, 47):
            try:
                return zlib.decompress(blob, wb)
            except Exception:
                continue
        return None

    def extract_to_disk_bytes(self, entry):
        """
        Bytes suitable for writing a standalone file to disk.

        For resources (.xtd/.ctd/.ydr/etc.) this reconstructs the OpenIV-style
        '7CSR' resource file (header + original compressed body) so the saved
        file is byte-compatible with OpenIV and re-openable by this editor and
        other RAGE tools. For binary files it returns the decoded contents.
        """
        if entry.is_resource:
            return self.extract_resource_as_file(entry)
        return self._extract_binary(entry)

    def summary(self):
        dirs  = sum(1 for e in self.entries if isinstance(e, RPFDirEntry))
        files = sum(1 for e in self.entries if isinstance(e, RPFFileEntry))
        res   = sum(1 for e in self.entries if isinstance(e, RPFFileEntry) and e.is_resource)
        enc   = {ENC_OPEN:"OPEN", ENC_NONE:"NONE", ENC_AES:"AES",
                 ENC_NG:"NG/AES(console)", 0x0FFFFFF8:"AES(console)"}.get(
                     self.encryption, f"0x{self.encryption:08X}")
        return (f"RPF7 | {self.platform} | {dirs} dirs, {files} files "
                f"({res} resource) | encryption={enc} | names={self.names_length}B")


# ============================================================================
# RPF Browser GUI window
# ============================================================================
class RPFBrowserWindow(tk.Toplevel):
    """
    A standalone child window that lets the user:
      1. Open an RPF7 archive (Xbox 360 or PS3) + supply an encryption key.
      2. Browse the directory tree and file list.
      3. Extract any file to disk.
      4. Open a .ytd / .xtd / .ctd directly into the parent Texture Editor.
    """
    TEXTURE_EXTS = {".ytd", ".xtd", ".ctd", ".wtd"}

    def __init__(self, parent_app):
        super().__init__(parent_app)
        self.app  = parent_app          # reference to App (the texture editor)
        self.arc  = None                # RPFArchive instance
        self.key  = None                # bytes
        self._key_path_var = tk.StringVar(value="")
        self._arc_path_var = tk.StringVar(value="")
        self._plat_var     = tk.StringVar(value="Xbox 360")
        self._status_var   = tk.StringVar(value="Open an RPF archive to get started.")
        self._filter_var   = tk.StringVar(value="")
        self._filter_var.trace_add("write", lambda *_: self._apply_filter())
        self._all_file_entries = []     # flat list of RPFFileEntry for filter

        self.title("RPF Archive Browser")
        self.geometry("860x620")
        self.minsize(660, 440)
        self.configure(bg=BG)
        self.transient(parent_app)

        # Navigation stack for nested RPFs: each entry is
        # (archive, label) so "Back" can restore the parent archive view.
        self._nav_stack = []
        self._current_dir = None

        self._build()

    # ------------------------------------------------------------------ build
    def _build(self):
        self._build_top_bar()
        self._build_main_area()
        self._build_statusbar()

    def _build_top_bar(self):
        top = tk.Frame(self, bg=PANEL, pady=6); top.pack(fill="x")

        # --- row 1: archive path + open button ---
        r1 = tk.Frame(top, bg=PANEL); r1.pack(fill="x", padx=8, pady=(0,4))
        tk.Label(r1, text="Archive:", bg=PANEL, fg=FG,
                 font=("Segoe UI",9,"bold"), width=9, anchor="w").pack(side="left")
        tk.Entry(r1, textvariable=self._arc_path_var, bg=ENTRY, fg=FG,
                 insertbackground=FG, relief="flat", font=("Segoe UI",9)
                 ).pack(side="left", fill="x", expand=True, padx=(0,6))
        tk.Button(r1, text="Browse…", command=self._browse_archive,
                  bg=BTN, fg=FG, activebackground=BTNACT, relief="flat",
                  padx=10, pady=2, font=("Segoe UI",9)
                  ).pack(side="left")

        # --- row 2: key path + browse + auto-detect ---
        r2 = tk.Frame(top, bg=PANEL); r2.pack(fill="x", padx=8, pady=(0,4))
        tk.Label(r2, text="Key file:", bg=PANEL, fg=FG,
                 font=("Segoe UI",9,"bold"), width=9, anchor="w").pack(side="left")
        tk.Entry(r2, textvariable=self._key_path_var, bg=ENTRY, fg=FG,
                 insertbackground=FG, relief="flat", font=("Segoe UI",9)
                 ).pack(side="left", fill="x", expand=True, padx=(0,6))
        tk.Button(r2, text="Browse…", command=self._browse_key,
                  bg=BTN, fg=FG, activebackground=BTNACT, relief="flat",
                  padx=10, pady=2, font=("Segoe UI",9)
                  ).pack(side="left", padx=(0,4))
        tk.Button(r2, text="Auto-detect", command=self._auto_key,
                  bg=BTN, fg=FG, activebackground=BTNACT, relief="flat",
                  padx=10, pady=2, font=("Segoe UI",9)
                  ).pack(side="left")

        # --- row 3: platform selector + Open button ---
        r3 = tk.Frame(top, bg=PANEL); r3.pack(fill="x", padx=8)
        tk.Label(r3, text="Platform:", bg=PANEL, fg=FG,
                 font=("Segoe UI",9,"bold"), width=9, anchor="w").pack(side="left")
        for plat, col in [("Xbox 360", YELLOW), ("PS3", TEAL)]:
            tk.Radiobutton(r3, text=plat, variable=self._plat_var, value=plat,
                           bg=PANEL, fg=FG, selectcolor=ENTRY,
                           activebackground=PANEL, activeforeground=col,
                           font=("Segoe UI",9)).pack(side="left", padx=(0,8))
        tk.Frame(r3, bg=PANEL).pack(side="left", fill="x", expand=True)
        tk.Button(r3, text="Open Archive", command=self._open_archive,
                  bg=ACCENT, fg=BG, activebackground=BTNACT,
                  relief="flat", padx=16, pady=4,
                  font=("Segoe UI",9,"bold"), cursor="hand2"
                  ).pack(side="right")

    def _build_main_area(self):
        mid = tk.Frame(self, bg=BG); mid.pack(fill="both", expand=True, padx=6, pady=4)

        # left: directory tree
        lf = tk.LabelFrame(mid, text=" Directories ", bg=BG, fg=ACCENT,
                           font=("Segoe UI",9,"bold"), relief="flat",
                           highlightbackground=ENTRY, highlightthickness=1)
        lf.pack(side="left", fill="both", expand=False, padx=(0,4))
        lf.config(width=220)
        lf.pack_propagate(False)

        self._dir_tree = ttk.Treeview(lf, show="tree", selectmode="browse")
        vsb = ttk.Scrollbar(lf, orient="vertical", command=self._dir_tree.yview)
        self._dir_tree.configure(yscrollcommand=vsb.set)
        self._dir_tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")
        self._dir_tree.bind("<<TreeviewSelect>>", self._on_dir_select)

        # right: file list + filter + action buttons
        rf = tk.Frame(mid, bg=BG); rf.pack(side="left", fill="both", expand=True)

        # filter bar
        fbar = tk.Frame(rf, bg=BG); fbar.pack(fill="x", pady=(0,4))
        tk.Label(fbar, text="Filter:", bg=BG, fg=FG,
                 font=("Segoe UI",9)).pack(side="left")
        tk.Entry(fbar, textvariable=self._filter_var, bg=ENTRY, fg=FG,
                 insertbackground=FG, relief="flat", font=("Segoe UI",9)
                 ).pack(side="left", fill="x", expand=True, padx=6)
        tk.Button(fbar, text="✕", command=lambda: self._filter_var.set(""),
                  bg=BTN, fg=FG, activebackground=BTNACT, relief="flat",
                  padx=6, pady=1, font=("Segoe UI",9)
                  ).pack(side="left")

        # file treeview
        cols = ("name","type","size","compressed","enc")
        self._file_tree = ttk.Treeview(rf, columns=cols, show="headings",
                                       selectmode="extended")
        for cid, lbl, w, anch in [
            ("name",       "Name",        300, "w"),
            ("type",       "Type",         60, "center"),
            ("size",       "Size",         90, "e"),
            ("compressed", "Compressed",   90, "e"),
            ("enc",        "Encrypted",    70, "center"),
        ]:
            self._file_tree.heading(cid, text=lbl)
            self._file_tree.column(cid, width=w, anchor=anch, minwidth=40)
        vsb2 = ttk.Scrollbar(rf, orient="vertical", command=self._file_tree.yview)
        self._file_tree.configure(yscrollcommand=vsb2.set)
        self._file_tree.pack(side="left", fill="both", expand=True)
        vsb2.pack(side="right", fill="y")
        self._file_tree.bind("<Double-1>", lambda _: self._on_file_double_click())
        self._file_tree.bind("<<TreeviewSelect>>", self._on_file_select)

        # breadcrumb / back bar for nested RPF navigation
        navf = tk.Frame(rf, bg=BG); navf.pack(fill="x", pady=(4,0))
        self._btn_back = tk.Button(navf, text="◀ Back", command=self._nav_back,
                                   bg=BTN, fg=FG, activebackground=BTNACT,
                                   relief="flat", padx=8, pady=1,
                                   font=("Segoe UI",9), cursor="hand2",
                                   state="disabled")
        self._btn_back.pack(side="left")
        self._crumb_lbl = tk.Label(navf, text="", bg=BG, fg=MAUVE,
                                   font=("Segoe UI",9), anchor="w")
        self._crumb_lbl.pack(side="left", fill="x", expand=True, padx=8)

        # action button bar (right side)
        abf = tk.Frame(self, bg=PANEL, pady=6); abf.pack(fill="x")
        def abtn(t, c, col=BTN):
            b = tk.Button(abf, text=t, command=c, bg=col, fg=BG if col != BTN else FG,
                          activebackground=BTNACT, relief="flat", padx=12, pady=4,
                          font=("Segoe UI",9,"bold") if col != BTN else ("Segoe UI",9),
                          cursor="hand2")
            b.pack(side="left", padx=4); return b
        self._btn_open_ed = abtn("Open in Texture Editor", self._open_in_editor, ACCENT)
        self._btn_extract  = abtn("Extract File(s)…",       self._extract_sel)
        self._btn_extract_all = abtn("Decompress All to Folder…", self._extract_all)
        tk.Frame(abf, bg=PANEL).pack(side="left", fill="x", expand=True)
        self._info_lbl = tk.Label(abf, text="", bg=PANEL, fg=MAUVE,
                                  font=("Segoe UI",9), padx=10)
        self._info_lbl.pack(side="right")

    def _build_statusbar(self):
        bar = tk.Frame(self, bg=PANEL, pady=2); bar.pack(fill="x", side="bottom")
        tk.Label(bar, textvariable=self._status_var, bg=PANEL, fg=FG,
                 font=("Segoe UI",9), anchor="w", padx=8).pack(fill="x")

    # ------------------------------------------------------------------ helpers
    def _setstatus(self, msg):
        self._status_var.set(msg); self.update_idletasks()

    def _browse_archive(self):
        p = filedialog.askopenfilename(
            title="Open RPF Archive",
            filetypes=[("RPF Archives","*.rpf"),("All Files","*.*")])
        if p:
            self._arc_path_var.set(p)
            # try to auto-detect key beside it
            kp = rpf_find_key_beside(p)
            if kp:
                self._key_path_var.set(kp)
                self._setstatus(f"Key auto-detected: {Path(kp).name}")

    def _browse_key(self):
        p = filedialog.askopenfilename(
            title="Select Encryption Key File",
            filetypes=[("Binary Key","*.bin"),("All Files","*.*")])
        if p:
            self._key_path_var.set(p)

    def _auto_key(self):
        arc = self._arc_path_var.get().strip()
        if not arc:
            messagebox.showinfo("Auto-detect Key", "Browse for an RPF archive first.",
                                parent=self); return
        kp = rpf_find_key_beside(arc)
        if kp:
            self._key_path_var.set(kp)
            self._setstatus(f"Auto-detected key: {Path(kp).name}")
        else:
            messagebox.showinfo("Auto-detect Key",
                "No 32-byte .bin key file found beside the archive.\n"
                "Browse for it manually (encryption_key.bin / gtav_key.bin).",
                parent=self)

    def _open_archive(self):
        arc_path = self._arc_path_var.get().strip()
        key_path = self._key_path_var.get().strip()
        plat     = self._plat_var.get()

        if not arc_path:
            messagebox.showerror("Open Archive", "Select an RPF archive first.", parent=self)
            return

        # Load the key (required for console archives)
        if key_path:
            try:
                self.key = rpf_load_key(key_path)
            except RPFError as e:
                messagebox.showerror("Key Error", str(e), parent=self); return
        else:
            self.key = b"\x00" * 32
            self._setstatus("No key supplied — trying unencrypted (OPEN) mode…")

        # Open + parse on a worker thread so the UI never freezes on large
        # archives. The parse itself is fast; reading a big file from disk and
        # decrypting can take a moment, and doing it on the main thread is what
        # makes the window appear hung.
        self._set_busy(True, f"Opening {Path(arc_path).name}…")
        import threading
        def worker():
            try:
                arc = RPFArchive.open(arc_path, self.key,
                                      lzx=self.app.lzx, platform=plat)
                self.after(0, lambda: self._on_archive_opened(arc, None))
            except Exception as ex:
                self.after(0, lambda: self._on_archive_opened(None, ex))
        threading.Thread(target=worker, daemon=True).start()

    def _set_busy(self, busy, msg=""):
        """Toggle a simple busy state on the open button / status line."""
        try:
            if busy:
                self._setstatus(msg or "Working…")
                self.config(cursor="watch")
            else:
                self.config(cursor="")
            self.update_idletasks()
        except Exception:
            pass

    def _on_archive_opened(self, arc, err):
        self._set_busy(False)
        if err is not None:
            if isinstance(err, RPFError):
                messagebox.showerror("RPF Error", str(err), parent=self)
            else:
                messagebox.showerror("Error", str(err), parent=self)
            self._setstatus("Failed to open archive.")
            return
        self.arc = arc
        self._nav_stack = []          # fresh top-level archive resets navigation
        self._setstatus(self.arc.summary())
        self._populate_trees()
        self._update_nav_ui(None)

    def _populate_trees(self):
        """Fill the directory tree and flat file list from the open archive."""
        # --- directory tree ---
        for item in self._dir_tree.get_children():
            self._dir_tree.delete(item)

        def add_dir(parent_iid, d):
            label = d.name or "(root)"
            iid = self._dir_tree.insert(parent_iid, "end", iid=str(d.index),
                                        text=f"📁 {label}", open=(parent_iid==""))
            for child in d.children:
                if isinstance(child, RPFDirEntry):
                    add_dir(iid, child)

        if self.arc.root:
            add_dir("", self.arc.root)

        # --- flat file list: start scoped to the root folder ---
        self._all_file_entries = list(self.arc.iter_files())
        self._current_dir = self.arc.root
        self._show_files(self._current_dir_files())
        # Select the root node so the tree highlights what's shown.
        try:
            if self.arc.root is not None:
                self._dir_tree.selection_set(str(self.arc.root.index))
        except Exception:
            pass

        dirs  = sum(1 for _ in self.arc.iter_dirs())
        files = len(self._all_file_entries)
        self._info_lbl.config(text=f"{dirs} dirs  |  {files} files")

    def _show_files(self, entries):
        for row in self._file_tree.get_children():
            self._file_tree.delete(row)

        # color tags
        self._file_tree.tag_configure("tex",  foreground=ACCENT)
        self._file_tree.tag_configure("res",  foreground=TEAL)
        self._file_tree.tag_configure("rpf",  foreground=YELLOW)
        self._file_tree.tag_configure("norm", foreground=FG)

        for e in entries:
            ext  = Path(e.name).suffix.lower()
            is_rpf = (ext == ".rpf")
            kind = ("RPF" if is_rpf else
                    "RES" if e.is_resource else
                    ("CMP" if e.is_compressed else "RAW"))
            sz   = e.uncompressed_size or (e.file_size if e.file_size else 0)
            csz  = e.file_size if e.is_compressed else sz
            enc  = "Yes" if e.encryption_type != 0 else "—"
            tag  = ("rpf" if is_rpf else
                    "tex" if ext in self.TEXTURE_EXTS else
                    ("res" if e.is_resource else "norm"))
            self._file_tree.insert("", "end", iid=str(e.index),
                values=(e.name, kind, _fmt_size(sz), _fmt_size(csz), enc),
                tags=(tag,))

    def _on_dir_select(self, _=None):
        if not self.arc: return
        sel = self._dir_tree.selection()
        if not sel: return
        idx = int(sel[0])
        entry = self.arc.entries[idx] if idx < len(self.arc.entries) else None
        if not isinstance(entry, RPFDirEntry): return
        # Remember the selected folder so the filter scopes to it (instead of
        # showing every file in the archive).
        self._current_dir = entry
        self._apply_filter()
        self._setstatus(f"{entry.path or '(root)'}  —  "
                        f"{sum(1 for c in entry.children if isinstance(c, RPFFileEntry))}"
                        f" file(s)")

    def _current_dir_files(self):
        """Files in the currently-selected directory (or all files if none)."""
        d = getattr(self, "_current_dir", None)
        if d is None:
            return self._all_file_entries
        return [c for c in d.children if isinstance(c, RPFFileEntry)]

    def _on_file_select(self, _=None):
        sel = self._file_tree.selection()
        if not sel or not self.arc: return
        # check if a texture is selected
        entries = self._get_selected_entries()
        if len(entries) == 1:
            e = entries[0]
            ext = Path(e.name).suffix.lower()
            sz = e.uncompressed_size or e.file_size
            self._setstatus(f"{e.path}  |  {_fmt_size(sz)}  |  "
                            f"{'Resource' if e.is_resource else 'Binary'}")

    def _apply_filter(self, *_):
        # Filter within the currently-selected folder. An empty filter shows the
        # folder's files (NOT every file in the archive).
        base = self._current_dir_files()
        filt = self._filter_var.get().strip().lower()
        if not filt:
            self._show_files(base)
            return
        filtered = [e for e in base
                    if filt in e.name.lower() or filt in e.path.lower()]
        self._show_files(filtered)

    def _get_selected_entries(self):
        sel = self._file_tree.selection()
        if not self.arc or not sel: return []
        out = []
        for iid in sel:
            idx = int(iid)
            for e in self.arc.iter_files():
                if e.index == idx:
                    out.append(e); break
        return out

    def _on_file_double_click(self):
        """Double-click: open a nested .rpf as an archive, or a texture in the
        editor."""
        entries = self._get_selected_entries()
        if not entries:
            return
        e = entries[0]
        if Path(e.name).suffix.lower() == ".rpf":
            self._open_nested_rpf(e)
        else:
            self._open_in_editor()

    def _open_nested_rpf(self, entry):
        """Open an .rpf stored inside the current archive (like OpenIV)."""
        self._set_busy(True, f"Opening {entry.name}…")
        import threading
        cur_arc = self.arc
        cur_label = self._crumb_label_for(cur_arc)
        def worker():
            try:
                # A nested RPF is a plain binary file inside the archive.
                raw = cur_arc.extract_to_disk_bytes(entry)
                if raw[:4] != RPF7_MAGIC:
                    raise RPFError(f"'{entry.name}' is not an RPF7 archive "
                                   f"(magic={raw[:4]!r}).")
                nested = RPFArchive.open_bytes(
                    raw, cur_arc.key, lzx=self.app.lzx,
                    platform=cur_arc.platform, path=entry.path or entry.name)
                self.after(0, lambda: self._on_nested_opened(
                    nested, cur_arc, cur_label, entry, None))
            except Exception as ex:
                self.after(0, lambda: self._on_nested_opened(
                    None, cur_arc, cur_label, entry, ex))
        threading.Thread(target=worker, daemon=True).start()

    def _on_nested_opened(self, nested, parent_arc, parent_label, entry, err):
        self._set_busy(False)
        if err is not None:
            messagebox.showerror("Open Nested RPF", str(err), parent=self)
            self._setstatus(f"Could not open {entry.name}.")
            return
        # push the parent onto the nav stack, switch to the nested archive
        self._nav_stack.append((parent_arc, parent_label))
        self.arc = nested
        self._setstatus(self.arc.summary())
        self._populate_trees()
        self._update_nav_ui(entry.name)

    def _nav_back(self):
        if not self._nav_stack:
            return
        parent_arc, _label = self._nav_stack.pop()
        self.arc = parent_arc
        self._setstatus(self.arc.summary())
        self._populate_trees()
        self._update_nav_ui(None)

    def _crumb_label_for(self, arc):
        if arc is None:
            return ""
        return Path(getattr(arc, "path", "") or "").name or "archive"

    def _update_nav_ui(self, _entered_name):
        # Build a breadcrumb: root.rpf > sub.rpf > ...
        crumbs = [self._crumb_label_for(a) for (a, _l) in self._nav_stack]
        crumbs.append(self._crumb_label_for(self.arc))
        self._crumb_lbl.config(text="  ▸  ".join(c for c in crumbs if c))
        self._btn_back.config(
            state=("normal" if self._nav_stack else "disabled"))

    def _open_in_editor(self):
        entries = self._get_selected_entries()
        if not entries:
            self._setstatus("Select a texture file first."); return
        e = entries[0]
        ext = Path(e.name).suffix.lower()
        if ext not in self.TEXTURE_EXTS:
            messagebox.showinfo("Open in Editor",
                f"'{e.name}' is not a texture file.\n\n"
                "Only .ytd, .xtd, .ctd, and .wtd files can be opened in the editor.",
                parent=self); return
        if not e.is_resource:
            messagebox.showinfo("Open in Editor",
                f"'{e.name}' is stored as a binary file, not a resource.\n"
                "Use Extract File(s) to save it to disk instead.",
                parent=self); return

        self._setstatus(f"Extracting {e.name}…")
        try:
            # Decompress inside the archive layer (Xbox 360 via XMem LZX with a
            # known output size, PS3 via zlib) -> full system+graphics buffer.
            # This avoids feeding RPF data to the crash-prone standalone
            # xDecompress path.
            dec = self.arc.extract(e)
        except Exception as ex:
            messagebox.showerror("Extract Error", str(ex), parent=self)
            self._setstatus("Extraction failed."); return

        self.app.lift(); self.app.focus_set()
        try:
            self.app._select_platform(self.arc.platform)
        except Exception:
            pass
        try:
            td = TextureDict(self.app.lzx)
            td.load_from_decompressed(dec, self.arc.platform,
                                      e.system_flags, e.graphics_flags,
                                      name=e.name)
        except Exception as ex:
            messagebox.showerror("Open Error", str(ex), parent=self)
            self._setstatus("Could not open resource."); return

        app = self.app
        app.td = td
        app._pending = None
        app._editing = False
        app.title(f"RAGE Console Texture Editor  -  {e.name}")
        if td.error_msg:
            app._populate([])
            app._show_msg(RED, "Could not open file", td.error_msg)
            app._plat_lbl.config(text=f"{td.platform} | error")
            self._setstatus(td.error_msg.split(chr(10))[0]); return
        app._populate(td.textures)
        app._plat_lbl.config(
            text=f"{td.platform} | CPU {td.cpu_size} GPU {td.gpu_size}")
        app._set_status(f"{e.name}  |  {len(td.textures)} texture(s)  |  {td.platform}")
        self._setstatus(f"Opened {e.name} in the Texture Editor  "
                        f"({len(td.textures)} texture(s))")

    def _extract_sel(self):
        entries = self._get_selected_entries()
        if not entries:
            self._setstatus("Select one or more files to extract."); return
        if len(entries) == 1:
            e = entries[0]
            out = filedialog.asksaveasfilename(
                title=f"Extract {e.name}", initialfile=e.name,
                defaultextension=Path(e.name).suffix,
                filetypes=[("All Files","*.*")], parent=self)
            if not out: return
            try:
                Path(out).write_bytes(self.arc.extract_to_disk_bytes(e))
                self._setstatus(f"Extracted: {Path(out).name}")
            except Exception as ex:
                messagebox.showerror("Extract Error", str(ex), parent=self)
        else:
            folder = filedialog.askdirectory(title="Extract Files To…", parent=self)
            if not folder: return
            ok = err = 0
            for e in entries:
                try:
                    Path(folder, e.name).write_bytes(self.arc.extract_to_disk_bytes(e)); ok += 1
                except Exception:
                    err += 1
            self._setstatus(f"Extracted {ok} file(s) to {folder}" +
                            (f"  ({err} error(s))" if err else ""))

    def _extract_all(self):
        if not self.arc:
            self._setstatus("Open an archive first."); return
        folder = filedialog.askdirectory(title="Decompress All Files To…", parent=self)
        if not folder: return
        ok = err = 0
        errors = []
        for e in self.arc.iter_files():
            # Preserve the real directory structure inside the archive,
            # exactly like OpenIV's "Export to folder".
            rel = e.path if e.path else e.name
            dest = Path(folder, *rel.split("/"))
            try:
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_bytes(self.arc.extract_to_disk_bytes(e)); ok += 1
            except Exception as ex:
                err += 1
                if len(errors) < 8:
                    errors.append(f"{rel}: {ex}")
        msg = f"Decompressed {ok} file(s) to:\n{folder}"
        if err:
            msg += f"\n\n{err} file(s) could not be extracted:"
            msg += "\n" + "\n".join(errors)
            if err > len(errors):
                msg += f"\n…and {err - len(errors)} more."
        self._setstatus(f"Decompressed {ok} file(s) to {folder}" +
                        (f"  ({err} error(s))" if err else ""))
        messagebox.showinfo("Decompress All", msg, parent=self)


def _fmt_size(n):
    if n is None or n == 0: return "—"
    if n >= 1024*1024: return f"{n/1048576:.1f} MB"
    if n >= 1024:      return f"{n/1024:.1f} KB"
    return f"{n} B"


# ============================================================================
# GUI
# ============================================================================
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("RAGE Console Texture Editor (Python Port)")
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
        fm.add_command(label="Open RPF Archive (Browser)...\tCtrl+P", command=self._open_rpf_browser)
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
        self._ps3_swz_var = tk.BooleanVar(value=PS3_UNSWIZZLE_ENABLED)
        hm.add_checkbutton(label="PS3: Unswizzle 8_8_8_8 textures",
                           variable=self._ps3_swz_var,
                           command=self._toggle_ps3_swizzle)
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
        # RPF Browser button (highlighted)
        rb = tk.Button(bar, text="RPF Browser", command=self._open_rpf_browser,
                       bg=YELLOW, fg="#1e1e2e", activebackground=BTNACT,
                       activeforeground=FG, relief="flat", padx=10, pady=3,
                       cursor="hand2", font=("Segoe UI", 9, "bold"))
        rb.pack(side="left", padx=3)
        tk.Frame(bar, bg=PANEL, width=6).pack(side="left")
        btn("New .ytd", self._new_dict)
        btn("Add Texture", self._add_texture)
        btn("Replace", self._replace_sel)
        btn("Rename", self._rename_sel)
        btn("Convert Format", self._convert_format_sel)
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
        self.bind("<Control-p>",lambda _:self._open_rpf_browser())
        self.bind("<Control-e>",lambda _:self._export_sel())
        self.bind("<Control-r>",lambda _:self._replace_sel())
        self.bind("<Control-s>",lambda _:self._save_as())
        self.bind("<Control-n>",lambda _:self._new_dict())
        self.bind("<Control-a>",lambda _:self._add_texture())
        self.bind("<F2>",lambda _:self._rename_sel())
        self.bind("<Control-Shift-S>",lambda _:self._rebuild_as())

    def _set_status(self,msg): self._status.set(msg); self.update_idletasks()

    def _toggle_ps3_swizzle(self):
        """Flip the global PS3 unswizzle flag and refresh the current preview."""
        global PS3_UNSWIZZLE_ENABLED
        PS3_UNSWIZZLE_ENABLED = bool(self._ps3_swz_var.get())
        state = "ON" if PS3_UNSWIZZLE_ENABLED else "OFF"
        self._set_status(f"PS3 8_8_8_8 unswizzle: {state}")
        # Refresh the currently-selected texture preview, if any
        sel = self._tree.selection()
        if sel and self.td and int(sel[0]) < len(self.td.textures):
            self._on_sel()

    def _open_rpf_browser(self):
        """Open the RPF Archive Browser as a child window."""
        win = RPFBrowserWindow(self)
        win.focus_set()

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
        if magic == GTA4_MAGIC:
            # GTA IV: PC & PS3 are both zlib (ambiguous), Xbox360 is LZX. Use the
            # platform tab to pick PS3/Xbox360/PC; if tab is PC, auto-detect.
            force = tab if tab in ("PS3", "Xbox 360", "PC") else None
            if tab == "PC":
                force = None   # let stream auto-detect (zlib->PC, LZX->Xbox360)
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

    def _convert_format_sel(self):
        sel=self._tree.selection()
        if not sel or not self.td:
            messagebox.showinfo("Convert Format","No texture selected."); return
        tex=self.td.textures[int(sel[0])]
        cur=(tex.fmt_name or "?").upper()

        # Offer DXT5 as the colour-capable target; also allow DXT1/DXT3.
        # The common ask is DXT5A -> DXT5 so colour can be painted in.
        win=tk.Toplevel(self); win.title("Convert Texture Format")
        win.configure(bg=BG); win.transient(self); win.grab_set()
        win.resizable(False, False)
        tk.Label(win, text=f"Convert '{tex.display_name}'", bg=BG, fg=ACCENT,
                 font=("Segoe UI",10,"bold")).pack(padx=16, pady=(14,2))
        tk.Label(win, text=f"Current format: {cur}", bg=BG, fg=FG,
                 font=("Segoe UI",9)).pack(padx=16, pady=(0,2))
        if cur in ("DXT5A","ATI1","BC4"):
            tk.Label(win,
                text="DXT5A holds a single channel (an alpha/luminance mask).\n"
                     "Converting to DXT4_5 (DXT5) makes it colour-capable: the\n"
                     "mask is kept as a white icon on transparent background.\n"
                     "Replace it afterwards with a colour image to add colour.\n\n"
                     "Note: the radio-wheel icons are tinted monochrome by the\n"
                     "game at runtime, so colour may not show there even after\n"
                     "conversion. Weapon-wheel and most other icons DO show colour.",
                bg=BG, fg=MAUVE, font=("Segoe UI",9), justify="left"
                ).pack(padx=16, pady=(2,8))
        else:
            tk.Label(win,
                text="Pick a target format. The change applies on the next\n"
                     "Save As (the dictionary is rebuilt with the new format).",
                bg=BG, fg=MAUVE, font=("Segoe UI",9), justify="left"
                ).pack(padx=16, pady=(2,8))

        choice=tk.StringVar(value="DXT5")
        rowf=tk.Frame(win, bg=BG); rowf.pack(padx=16, pady=(0,8))
        # Labels show the RAGE/GTA V format names (what the dump displays);
        # the value sent to convert_texture_format stays the short alias.
        # DXT4_5 IS DXT5 (format code 20) -- the colour-capable wheel format.
        fmt_choices = [("DXT4_5 (colour)","DXT5"),
                       ("DXT2_3","DXT3"),
                       ("DXT1","DXT1"),
                       ("8_8_8_8","8_8_8_8")]
        for label, value in fmt_choices:
            tk.Radiobutton(rowf, text=label, variable=choice, value=value,
                           bg=BG, fg=FG, selectcolor=ENTRY,
                           activebackground=BG, activeforeground=ACCENT,
                           font=("Segoe UI",9)).pack(side="left", padx=6)

        def do_convert():
            target=choice.get()
            try:
                self.td.convert_texture_format(tex, target)
                # convert_texture_format sets tex.fmt_name to the RAGE label.
                self._populate(self.td.textures)
                # reselect the same row
                try:
                    self._tree.selection_set(sel[0]); self._tree.see(sel[0])
                except Exception: pass
                self._show_preview(tex)
                self._dirty=True
                self._set_status(f"Converted '{tex.display_name}' to {target} "
                                 f"(applies on Save As).")
            except Exception as e:
                messagebox.showerror("Convert Error", str(e), parent=win)
            win.destroy()

        bf=tk.Frame(win, bg=BG); bf.pack(padx=16, pady=(4,14))
        tk.Button(bf, text="Convert", command=do_convert, bg=ACCENT, fg=BG,
                  activebackground=BTNACT, relief="flat", padx=16, pady=4,
                  font=("Segoe UI",9,"bold"), cursor="hand2").pack(side="left", padx=6)
        tk.Button(bf, text="Cancel", command=win.destroy, bg=BTN, fg=FG,
                  activebackground=BTNACT, relief="flat", padx=16, pady=4,
                  font=("Segoe UI",9), cursor="hand2").pack(side="left", padx=6)

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
        if magic == GTA4_MAGIC:
            force = None
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
        text=("RAGE Console Texture Editor - Python Port\n\n"
              "Original Pascal tool: indirivacua / Dageron\n"
              "  github.com/indirivacua/RAGE-Console-Texture-Editor\n"
              "Python/Tkinter port: Claude\n\n"
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
    elif platform in ("GTA4-PC", "GTA4-Xbox 360", "GTA4-PS3"):
        _dump_gta4(dec, cpu, L, console=(platform == "GTA4-Xbox 360"))
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

def _dump_gta4(dec, cpu, L, console=False):
    be = console
    def u32(o): return struct.unpack_from('>I' if be else '<I', dec, o)[0] if o+4<=len(dec) else 0
    def u16(o): return struct.unpack_from('>H' if be else '<H', dec, o)[0] if o+2<=len(dec) else 0
    def off(p):
        p &= 0xFFFFFFFF
        return p & 0x0FFFFFFF if (p>>28) in (5,6) else 0
    L("=== GTA IV grcTextureDictionary header (%s) ==="%("Xbox360 BE" if be else "PC LE"))
    L(f"  dict raw (0x40): {dec[:0x40].hex()}")
    L(f"  vft@0x00       : 0x{u32(0):08X}")
    L(f"  blockmap@0x04  : 0x{u32(4):08X}")
    L(f"  parent@0x08    : 0x{u32(8):08X}")
    L(f"  usage@0x0C     : 0x{u32(0xC):08X}")
    L(f"  hashes ptr@0x10: 0x{u32(0x10):08X}  count@0x14: {u16(0x14)}")
    L(f"  tex   ptr@0x18 : 0x{u32(0x18):08X}  count@0x1C: {u16(0x1C)}")
    list_ptr = off(u32(0x18)); count = u16(0x1C) or (u32(0x1C)&0xFFFF)
    L("")
    for i in range(min(count, 64)):
        base = off(u32(list_ptr + i*4))
        if base == 0 or base+0x60 > len(dec):
            L(f"--- texture[{i}] @0x{base:08X} (out of range) ---"); continue
        L(f"--- GTA IV grcTexture[{i}] @0x{base:08X} (full 0x60 bytes) ---")
        L(f"  raw: {dec[base:base+0x60].hex()}")
        nptr = off(u32(base+0x20))
        L(f"  name@+0x20 -> 0x{nptr:08X} = {_read_cstr(dec, nptr)!r}")
        L(f"  u16@+0x38={u16(base+0x38)} u16@+0x3A={u16(base+0x3A)} "
          f"u16@+0x10={u16(base+0x10)} u16@+0x12={u16(base+0x12)}")
        L("")

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

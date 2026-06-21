#!/usr/bin/env python3
"""
RAGE Console Texture Editor - Python Port
==========================================
A faithful Python/Tkinter port of indirivacua/RAGE-Console-Texture-Editor
(originally by Dageron), a texture editor for console RAGE games
(GTA IV, GTA V, RDR, MC:LA, MP3).

Supports texture dictionaries for:
  - PC          .ytd          RSC7 'RSC7' magic, Little-Endian, zlib
  - PS3         .ctd          RSC7 '7CSR' magic, Big-Endian, zlib
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
    from tkinter import ttk, filedialog, messagebox, simpledialog
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


def encode_mip_register(levels):
    """Encode the Xbox 360 GPU fetch-constant DWORD (our dword_12) holding
    MaxMipLevel, in the EXACT format the working Dageron tool and stock GTA IV
    files use. Verified byte-for-byte against a real working pcj.xtd:
        1 mip  -> 0x00000000
        3 mips -> 0x00000080   (maxmip 2)
        4 mips -> 0x000000C0   (maxmip 3)

    Layout: the 4-bit MaxMipLevel is split in the NATIVE (little-endian) value
    as low 2 bits at bits 30-31 and high 2 bits at bits 16-17; the dword is then
    byte-swapped for big-endian on-disk storage. (Net effect for small counts:
    the value lands in the low byte, e.g. 0x80 for maxmip 2.)
    """
    m = max(0, levels - 1) & 0xF
    native = ((m & 0x3) << 30) | (((m >> 2) & 0x3) << 16)
    return EndianChangeDWORD(native)


def decode_mip_register(d12_le):
    """Inverse of encode_mip_register. Takes dword_12 AS READ little-endian by
    the caller (parse_gta4 reads the descriptor dwords with '<I'), which is the
    natural GPU-register order -- so MaxMipLevel's low 2 bits are at bits 30-31
    and high 2 bits at bits 16-17, with NO further byte-swap. Verified against
    the working Dageron pcj.xtd: LE-read 0x80000000 -> maxmip 2 (3 levels),
    0xC0000000 -> 3 (4 levels), 0x00000000 -> 0 (1 level)."""
    return ((d12_le >> 30) & 0x3) | (((d12_le >> 16) & 0x3) << 2)

# ============================================================================
# Constants
# ============================================================================
PC_MAGIC      = b'RSC7'        # 0x37435352 little-endian on disk
CONSOLE_MAGIC = b'7CSR'        # 0x52534337 ... read as DWORD = 0x37435352 (see below)
GTA4_MAGIC    = b'RSC\x05'     # 0x05435352 -- GTA IV / EFLC PC (RSC version 5)
GTA4_MAGIC_CON= b'\x05CSR'     # 0x5243530... GTA IV console (Xbox 360 / PS3),
                               # the PC magic byte-reversed: raw version 0x05 + 'CSR'

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
                    # ---- compression side (GTA IV / RDR Xbox 360, Codec 0) ----
                    # int XMemCreateCompressionContext(type, params*, flags, ctx**)
                    self._xmem.XMemCreateCompressionContext.argtypes = [
                        ctypes.c_int, ctypes.c_void_p, ctypes.c_int,
                        ctypes.POINTER(ctypes.c_void_p)]
                    self._xmem.XMemCreateCompressionContext.restype = ctypes.c_int
                    self._xmem.XMemResetCompressionContext.argtypes = [ctypes.c_void_p]
                    self._xmem.XMemResetCompressionContext.restype = ctypes.c_int
                    # int XMemCompress(ctx, dest, destSize*, src, srcSize)
                    self._xmem.XMemCompress.argtypes = [
                        ctypes.c_void_p, ctypes.c_char_p,
                        ctypes.POINTER(ctypes.c_int),
                        ctypes.c_char_p, ctypes.c_int]
                    self._xmem.XMemCompress.restype = ctypes.c_int
                    self._xmem.XMemDestroyCompressionContext.argtypes = [ctypes.c_void_p]
                    self._xmem.XMemDestroyCompressionContext.restype = None
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

    # ---- Codec 0 compress: GTA IV / RDR Xbox 360 (XMemCompress + marker) -----
    def compress_blocks_xmem(self, data):
        """
        Compress a GTA IV / RDR Xbox 360 resource body the way the original
        Pascal tool's CompressLZX (Codec 0) does, using XMemCompress (stream
        mode) from xcompress.dll. The on-disk body the loader expects is:

            DWORD  0xF112F50F            (little-endian marker, as stored)
            DWORD  compressedSize        (BIG-endian)
            bytes  <XMem LZX stream>

        The loader (load_resource) skips the 8-byte marker+size prefix, then
        feeds the LZX stream to the block-framed decompressor. We mirror the
        reference exactly so a body produced here round-trips through our own
        reader and through the real game loader.

        Window 64 KB, partition 256 KB, stream flag = 1 (XMEMCOMPRESS_STREAM).
        """
        if not self._xmem:
            raise LZXError("xcompress.dll (XMem* API) unavailable: "
                           + (self._loaded_err or "not loaded"))
        if not hasattr(self._xmem, "XMemCompress"):
            raise LZXError("xcompress.dll does not export XMemCompress.")
        src = bytes(data)
        ctx = ctypes.c_void_p(0)
        XMEMCODEC_LZX = 1
        XMEMCOMPRESS_STREAM = 1
        # The reference passes NIL codec params (default 64KB window / stream
        # mode), not the LZX parameter struct used for DEcompression. Matching
        # that exactly is what makes the framed output decode block-for-block.
        rc = self._xmem.XMemCreateCompressionContext(
            XMEMCODEC_LZX, None, XMEMCOMPRESS_STREAM, ctypes.byref(ctx))
        if rc != 0 or not ctx.value:
            raise LZXError(f"XMemCreateCompressionContext failed (rc={rc})")
        try:
            self._xmem.XMemResetCompressionContext(ctx)
            # Output capacity = 2x input (as in the reference). The buffer is
            # zero-initialised; XMemCompress may leave a tail of zeros, so the
            # real length is found by trimming trailing zero DWORDs rather than
            # trusting the returned size (matches CompressLZX Codec 0).
            cap = max(len(src) * 2, 0x1000)
            out = ctypes.create_string_buffer(cap)   # zero-filled
            out_len = ctypes.c_int(cap)
            rc = self._xmem.XMemCompress(ctx, out, ctypes.byref(out_len),
                                         src, len(src))
            if rc != 0:
                raise LZXError(f"XMemCompress failed (rc={rc})")
            raw_out = out.raw[:cap]
        finally:
            self._xmem.XMemDestroyCompressionContext(ctx)

        # Trim trailing zero DWORDs to recover the true compressed length, the
        # way the reference scans backward 4 bytes at a time until non-zero.
        end = len(raw_out)
        while end >= 4 and raw_out[end-4:end] == b'\x00\x00\x00\x00':
            end -= 4
        # The returned size, when valid, is authoritative; prefer the larger of
        # (reported, trimmed) so we never truncate a block the reader needs.
        reported = out_len.value if 0 < out_len.value <= cap else 0
        comp_len = max(end, reported)
        comp = raw_out[:comp_len]
        # Marker: the original Pascal CompressLZX writes DWORD 0xF112F50F (bytes
        # 0F F5 12 F1). Real GTA IV files use both 0xF112F50F and 0xEF12F50F;
        # our loader accepts either. We emit 0xF112F50F to match the reference
        # tool's output exactly. The decompressor only needs the 8-byte prefix
        # skipped, so the precise value doesn't affect decoding.
        marker = struct.pack('<I', 0xF112F50F)
        size_be = struct.pack('>I', len(comp))
        return marker + size_be + comp

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
    # dwDWORD_12: MaxMipLevel. dwords[11] is read little-endian by the caller,
    # which is the natural register order; decode_mip_register extracts the mip
    # count directly (no extra byte-swap). Verified against the working Dageron
    # file (0x80000000 LE -> 3 levels).
    MaxMipLevel = decode_mip_register(dwords[11])
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
                 "_rgba_override","_converted","_user_painted","_mip_levels",
                 "_orig_dword11","_mip_overrides","_tex_vft","_dict_vft",
                 "_full_gpu_data","_orig_mip_off","_orig_levels","_mip_tail_data",
                 "_ps3_regs","_ps3_struct_raw"]
    def __init__(self):
        self.name=""; self.width=0; self.height=0; self.mips=1
        self.platform=""; self.fmt_name=""; self.tex_offset=0; self.name_offset=0
        self.raw_data=b""; self.index=0; self.endian=0; self.texture_type=0
        self.gpu_fmt=""
        self._rgba_override=None   # (rgba_bytes, w, h) when format was converted
        self._converted=False      # True once format was changed via convert
        self._user_painted=False   # True once the user Replaced with real pixels
        self._mip_levels=1         # requested mip-chain length for rebuild
        self._orig_dword11=None     # original dword_11 (tiling reg) if parsed
        self._mip_overrides=None    # {level:(rgba,w,h)} for per-mip replacement
        self._tex_vft=None          # original grcTextureXenon vtable, if parsed
        self._dict_vft=None         # original dictionary vtable, if parsed
        self._full_gpu_data=None    # the COMPLETE original tiled block (base +
                                    # mip tail) exactly as stored in the file, so
                                    # an unedited texture round-trips byte-for-byte
                                    # and its console-correct mip layout survives
        self._orig_mip_off=None     # original dword_13 mip-chain address (raw)
        self._orig_levels=1         # mip count as parsed from the source file
        self._mip_tail_data=None    # original mip-tail region bytes (verbatim)
        self._ps3_regs=None         # captured PS3 RSX GPU registers (dict)
        self._ps3_struct_raw=None   # full original PS3 grcTexture 0x40 struct
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
    if magic == GTA4_MAGIC or magic == GTA4_MAGIC_CON:
        # PC stores the header little-endian ('RSC\x05'); consoles store it
        # big-endian, which makes the magic appear byte-reversed ('\x05CSR').
        con = (magic == GTA4_MAGIC_CON)
        endc = '>I' if con else '<I'
        rsctype = struct.unpack_from(endc, raw, 4)[0]
        flags   = struct.unpack_from(endc, raw, 8)[0]
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
        # The Xbox 360 LZX sub-header marker. Real GTA IV files use BOTH
        # 0xF112F50F and 0xEF12F50F (verified across vehicles.img: 112 vs 144
        # resources, zero using anything else). They differ only in the top
        # byte and both precede an 8-byte [marker][compressed-size BE] prefix
        # that must be skipped before the LZX block reader. Accept either.
        LZX_MARKERS = (0xF112F50F, 0xEF12F50F)
        first_dword = (struct.unpack_from('<I', body, 0)[0]
                       if len(body) >= 4 else 0)
        has_lzx_marker = first_dword in LZX_MARKERS
        if force_platform in ("PC", "PS3", "Xbox 360"):
            platform = force_platform
        elif con:
            # A console RSC5 is Xbox 360 (LZX) or PS3 (zlib). zlib body -> PS3.
            platform = "PS3" if is_zlib else "Xbox 360"
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
            # CompressLZX writes: [marker : 4][compressed size BE : 4], then the
            # LZX blocks. Skip it so the block reader starts correctly.
            blocks = body
            if has_lzx_marker and len(body) >= 8:
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
    elif force_platform in ("PS3", "Xbox 360"):
        platform = force_platform
    else:
        # A 7CSR console resource is either PS3 (raw zlib/deflate body) or
        # Xbox 360 (LZX body). They share the same magic, so sniff the body: try
        # to fully inflate it as raw deflate (PS3). LZX data is not deflate and
        # fails or yields almost nothing, so require a substantial inflate before
        # calling it PS3. This auto-detects PS3 .ctd files that were previously
        # misreported as Xbox 360 (then failing with an LZX error), without
        # false-positiving on real Xbox 360 LZX bodies.
        platform = "Xbox 360"
        def _probe_deflate(wbits):
            try:
                d = zlib.decompressobj(wbits)
                out = d.decompress(raw[16:], 65536)
                # a genuine PS3 body inflates to a large dictionary; LZX won't.
                return len(out) >= 4096
            except Exception:
                return False
        if _probe_deflate(-15) or _probe_deflate(15):
            platform = "PS3"

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
    ps3_regs_list=[]; struct_raw_list=[]
    for base in offsets:
        # PS3 grcTexture (GTA V) layout, verified against real .ctd files:
        #   +0x08 : texture format code (1 byte) -> PS3_TEXTURE_FORMAT table
        #   +0x09 : mip count (1 byte)  [verified against real GTA V .ctd]
        #   +0x0C : RSX texture control register (GcmTexture-style)
        #   +0x10 : width  (u16 BE)
        #   +0x12 : height (u16 BE)
        #   +0x14 : depth / control register (0x00010000 = depth 1)
        #   +0x1C : GPU texture data offset (relative to GPU block)
        #   +0x20 : name pointer
        #   +0x24 / +0x2C : RSX remap / filter control registers
        # The +0x0C/+0x14/+0x24/+0x2C registers configure the RSX texture unit.
        # If they are dropped on a rebuild (written as 0) the PS3 cannot set the
        # texture up and FREEZES at the load screen. Capture them verbatim so a
        # replaced/rebuilt texture keeps its working register set.
        fmt_bytes.append(buf[base+0x08] if base+0x08 < len(buf) else 0)
        r.seek(base+0x10)
        w = EndianChangeWORD(r.u16_le()); h = EndianChangeWORD(r.u16_le())
        widths.append(w); heights.append(h)
        mips.append(max(1, buf[base+0x09] if base+0x09 < len(buf) else 1))
        r.seek(base+0x1C)
        toff = GetOffset(EndianChangeDWORD(r.u32_le())); tex_offsets.append(toff)
        r.seek(base+0x20)
        nptr = GetOffset(EndianChangeDWORD(r.u32_le())); name_offsets.append(nptr)
        def _rd_be(o):
            return struct.unpack_from('>I', buf, base+o)[0] if base+o+4 <= len(buf) else 0
        ps3_regs_list.append({
            'r08': _rd_be(0x08), 'r0c': _rd_be(0x0C), 'r14': _rd_be(0x14),
            'r18': _rd_be(0x18), 'r24': _rd_be(0x24), 'r28': _rd_be(0x28),
            'r2c': _rd_be(0x2C), 'r30': _rd_be(0x30), 'r34': _rd_be(0x34),
            'r38': _rd_be(0x38), 'r3c': _rd_be(0x3C)})
        struct_raw_list.append(bytes(buf[base:base+0x40])
                               if base+0x40 <= len(buf) else b'')

    for i in range(count):
        t = TexEntry()
        t.name = _clean_name(_read_cstr(buf, name_offsets[i]))
        t.width = widths[i]; t.height = heights[i]; t.mips = mips[i]
        t.tex_offset = tex_offsets[i]; t.name_offset = name_offsets[i]
        t.platform = "PS3"; t.index = i
        t.texture_type = fmt_bytes[i]
        t.gpu_fmt = GetGPUTEXTUREFORMAT_PS3(fmt_bytes[i])
        t.fmt_name = t.gpu_fmt.replace('GPUTEXTUREFORMAT_', '')
        t._ps3_regs = ps3_regs_list[i]          # RSX registers for rebuild
        t._ps3_struct_raw = struct_raw_list[i]  # full original 0x40 struct
        t.texture_type = fmt_bytes[i]           # original PS3 format code byte
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

    name_offsets=[]; d3d_offsets=[]; widths=[]; heights=[]; tex_vfts=[]
    for base in offsets:
        r.seek(base)
        vmt = r.u32_le()
        tex_vfts.append(EndianChangeDWORD(vmt) & 0xFFFFFFFF)
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

    tex_types=[]; endians=[]; mips=[]; gpu_offsets=[]; mip_offsets=[]; d11s=[]
    for i in range(count):
        d3doff = d3d_offsets[i]
        r.seek(d3doff)
        dwords = [r.u32_le() for _ in range(13)]
        d3d = ReadD3DBaseTexture(dwords)
        # capture the real dword_11 (tiling/format register) as stored big-endian
        d11s.append(EndianChangeDWORD(dwords[10]) & 0xFFFFFFFF)
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
        t._orig_dword11 = d11s[i]   # preserve for faithful rebuild
        t._tex_vft = tex_vfts[i] if i < len(tex_vfts) else None
        t._dict_vft = _vmt          # dict vtable (same for all in this dict)
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
            # original dword_11 (tiling register) and dword_13 (mip-chain addr),
            # captured so an unedited texture can be written back byte-for-byte.
            t._orig_dword11 = struct.unpack_from('>I', buf, desc + 10*4)[0]
            t._orig_mip_off = struct.unpack_from('>I', buf, desc + 12*4)[0]
            t._orig_levels = mips
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

    # ---- capture each texture's base + mip-tail as SEPARATE contiguous regions
    # On Xbox 360 a texture's base mip (at dword_9) and its mip tail (levels 1..N
    # at dword_13) are two contiguous blocks placed in the graphics segment, often
    # in gaps between other textures. Each region is itself contiguous. Capturing
    # both verbatim lets the writer re-place them and re-point dword_13 while
    # preserving Rockstar's console-correct tiled mip layout, which the tool can't
    # reconstruct. We compute each region's length from the next data-region start.
    if console:
        starts = set()
        for t in textures:
            if t.tex_offset:
                starts.add(t.tex_offset)
            mo = getattr(t, '_orig_mip_off', None)
            if mo is not None and (mo >> 28) in (5, 6):
                starts.add(mo & 0x0FFFFFFF)
        gfx_end = len(buf) - cpu_size
        starts.add(gfx_end)
        starts_sorted = sorted(s for s in starts if s is not None)

        def region(start_off):
            # bytes from start_off to the next region start (exclusive)
            nxt = gfx_end
            for s in starts_sorted:
                if s > start_off:
                    nxt = s
                    break
            a = cpu_size + start_off
            b = cpu_size + nxt
            if 0 <= a < b <= len(buf):
                return bytes(buf[a:b])
            return None

        for t in textures:
            base_reg = region(t.tex_offset) if t.tex_offset is not None else None
            mo = getattr(t, '_orig_mip_off', None)
            mip_reg = None
            if mo is not None and (mo >> 28) in (5, 6):
                mip_start = mo & 0x0FFFFFFF
                # EXACT mip-tail size = sum of the tiled sizes of levels 1..N-1.
                # Measuring to the next region start would include inter-block
                # page padding, which inflates the tail; on a reopen+resave that
                # inflation cascades and corrupts OTHER textures' mips. Compute
                # the precise byte count from the mip dimensions instead.
                tail_sz = 0
                if t.gpu_fmt and (t.mips or 1) > 1:
                    for lvl in range(1, t.mips):
                        mw = max(1, t.width >> lvl); mh = max(1, t.height >> lvl)
                        s2 = _xbox_format_setup(t.gpu_fmt, mw, mh)
                        if s2:
                            tail_sz += s2[0]
                a = cpu_size + mip_start
                if tail_sz and 0 <= a < a + tail_sz <= len(buf):
                    mip_reg = bytes(buf[a:a + tail_sz])
                else:
                    mip_reg = region(mip_start)   # fallback
            # base region: trim to exact base mip size too (avoid trailing pad)
            if base_reg is not None and t.gpu_fmt:
                s0 = _xbox_format_setup(t.gpu_fmt, t.width, t.height)
                if s0 and len(base_reg) >= s0[0]:
                    base_reg = base_reg[:s0[0]]
            if base_reg is not None:
                t._full_gpu_data = base_reg
            t._mip_tail_data = mip_reg
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
    # Numeric D3DFMT / DXGI codes used by RAGE for UNCOMPRESSED textures. These
    # appear as a small integer in the format dword, NOT a 4-char FourCC. The
    # 256x1 gradient/LUT textures in HUD dictionaries are typically A8R8G8B8.
    PC_NUMERIC={
        21: ("A8R8G8B8", 4, False),   # D3DFMT_A8R8G8B8
        20: ("R8G8B8",   3, False),   # D3DFMT_R8G8B8 (rare)
        28: ("A8",       1, False),   # D3DFMT_A8
        50: ("L8",       1, False),   # D3DFMT_L8
        0x57: ("A8R8G8B8", 4, False), # some variants
    }
    def f2f(fc):
        if fc[:4] in PC_FOURCC: return PC_FOURCC[fc[:4]]
        # uncompressed: the format is a small integer in the first dword
        code = int.from_bytes(fc[:4], 'little')
        if code in PC_NUMERIC: return PC_NUMERIC[code]
        if (fc[0] in (0x15,0x14,0x1C,0x32,0x57)) and fc[1]==0 and fc[2]==0 and fc[3]==0:
            return PC_NUMERIC.get(fc[0], ("A8R8G8B8",4,False))
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
            fmt,bpp,is_blk=f2f(fourcc)
            t=TexEntry(); t.name=_read_cstr(virt,name_ptr if name_ptr else 0)
            t.width=w; t.height=h; t.mips=m; t.fmt_name=fmt; t.platform="PC"
            t.tex_offset=phys_ptr
            # data size: block formats are bw*bh*blocksize; uncompressed are w*h*bpp
            if is_blk:
                bw=max(1,(w+3)//4); bh=max(1,(h+3)//4)
                sz=bw*bh*(8 if fmt in("DXT1","ATI1") else 16)
            else:
                sz=w*h*bpp
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

    # Choose the base unit so the LARGEST block fits in the top tier
    # (base*16). Starting too small forces big textures to fail and small ones
    # to overflow the per-tier counts; sizing from the largest block first
    # avoids both. We still try increasing shifts in case the per-tier counts
    # need more headroom.
    largest = max(block_sizes)
    min_shift = 0
    while (base_unit << min_shift) * 16 < largest:
        min_shift += 1

    shift = min_shift
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
                chosen = max(tiers)   # clamp to the top tier
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
        if shift > 0x1F:
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
            # Prefer the EXACT original format code for a same-format edit (the
            # RSX uses distinct codes like 134 vs 166 for the same logical format
            # to signal swizzle/normalisation state; remapping to the canonical
            sysseg.patch_u32_be(base+0x00, self.VFT_TEX)
            fmt = t['fmt'].upper()
            # Format code: prefer the EXACT original code for a same-format edit
            # (the RSX uses distinct codes like 134 vs 166 for one logical format
            # to signal swizzle/normalisation); only use the canonical encode
            # code when the format was actually converted.
            orig_code = t.get('orig_fmt_code')
            if orig_code is not None and GetGPUTEXTUREFORMAT_PS3(orig_code) != '-unknown-':
                sysseg.buf[base+0x08] = orig_code & 0xFF
            else:
                sysseg.buf[base+0x08] = PS3_FMT_CODE.get(fmt, 136) & 0xFF   # format
            sysseg.buf[base+0x09] = max(1, t.get('levels', 1)) & 0xFF   # mip count
            # +0x0C / +0x24 / +0x2C are RSX GPU control/remap registers. Copy
            # them from the captured originals (ps3_regs) when present -- this is
            # the v32 approach that produces .ctd files which do NOT freeze the
            # console. Do NOT clone the whole struct or synthesise a +0x28
            # self-pointer / +0x34 table: doing so froze the PS3 at load.
            regs = t.get('ps3_regs')
            if regs:
                sysseg.patch_u32_be(base+0x0C, regs.get('r0c', 0))
                sysseg.patch_u32_be(base+0x14, regs.get('r14', 0x00010000))
                sysseg.patch_u32_be(base+0x24, regs.get('r24', 0))
                sysseg.patch_u32_be(base+0x2C, regs.get('r2c', 0))
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

# ============================================================================
# GTA IV (RSC version 5) flag ENCODER.
# ----------------------------------------------------------------------------
# This is a direct port of RageLib's ResourceHeader.SetMemSizes (used by both
# SparkIV and OpenIV). The decode side is:
#   system   = (flags & 0x7FF)         << (((flags >> 11) & 0xF) + 8)
#   graphics = ((flags >> 15) & 0x7FF) << (((flags >> 26) & 0xF) + 8)
# but the CANONICAL encode RageLib expects keeps each mantissa <= 0x3F (NOT
# 0x7FF) by maximizing the shift, and it ALWAYS sets the top two bits
# (0xC0000000). Those top bits are the resource marker the IMG TOC reads back
# via `IsResourceFile = ((flags & 0xC0000000) != 0)`. If they're clear -- which
# happens if you naively pack a large mantissa with shift 0 -- SparkIV/OpenIV
# see the entry as a NON-resource and display the flag value as a raw size
# (e.g. 0x03000020 -> "48 MB"), which is exactly the bug this fixes.
# ============================================================================
def _rsc05_mantissa_shift(size):
    """Canonical (mantissa<=0x3F, shift) for a segment size, matching RageLib's
    SetMemSizes loop. size 0 -> (0,0)."""
    a = size >> 8
    b = 0
    while a > 0x3F:
        if (a & 1) != 0:
            a += 2
        a >>= 1
        b += 1
    return a & 0x3F, b & 0xF

def encode_rsc05_flags(system_size, graphics_size, version_bits=0xC0000000):
    """Build the GTA IV RSC v5 flags dword from the two segment sizes, the way
    RageLib (SparkIV/OpenIV) does. The 0xC0000000 marker bits are set so the
    file round-trips through the IMG TOC as a genuine resource. Verified that
    decoding the result with GetValueRSC05 reproduces the input sizes and that
    the top two bits are set."""
    s_mant, s_sh = _rsc05_mantissa_shift(system_size)
    g_mant, g_sh = _rsc05_mantissa_shift(graphics_size)
    flags = ((version_bits & 0xC0000000)
             | (s_mant & 0x7FF)
             | ((s_sh & 0xF) << 11)
             | ((g_mant & 0x7FF) << 15)
             | ((g_sh & 0xF) << 26))
    return flags & 0xFFFFFFFF

# ============================================================================
# GTA IV Xbox 360 .xtd WRITER  --  full grcTextureDictionary rebuild (RSC v5).
# ----------------------------------------------------------------------------
# Models the structure decoded byte-for-byte from a real pcj.xtd:
#   dict header (0x30, BE):
#     +0x00 vft (0x0C836100)   +0x04 blockmap ptr   +0x08 parent(0)
#     +0x0C usage(1)           +0x10 hash ptr  +0x14 hash count(u16)
#     +0x18 tex-list ptr       +0x1C tex count (u16,u16)
#   grcTexture (0x40, BE):
#     +0x00 vft (0x941A6300)   +0x08 usage(1)
#     +0x14 name ptr           +0x18 D3DBaseTexture ptr
#     +0x1C width(u16) height(u16)   +0x20 mip count
#     +0x24..0x2C = three 1.0 floats (0x3F800000)
#   D3DBaseTexture descriptor (0x34, the GPU fetch constant, stored LITTLE-
#   endian dword-by-dword exactly like GTA V Xbox 360):
#     dword_1 0x00200003  dword_2 0x00000001  dwords 3-5 = 0
#     dword_6/7 0xFFFF0000
#     dword_8 = (pitch_tiles<<22) | 0x80000002
#     dword_9 = (gpu_paged_addr & 0xFFFFF000) | (endian<<6) | format
#     dword_10 = ((h-1)<<13) | (w-1)
#     dword_11 = per-format tiling register (preserved if known)
#     dword_12 = mip-count encoded (LE on disk)
#     dword_13 = mip address (single-mip default 0x00000200)
# The whole thing is one RSC5 container: 12-byte header (magic + version + the
# single flags word from encode_rsc05_flags), body = system pages + graphics
# pages, LZX-compressed via XMemCompress (compress_blocks_xmem).
# ============================================================================
class Xtd4Writer:
    """Build a GTA IV Xbox 360 .xtd from builder-dict textures.

    texture dict entries: name, fmt (DXT1/DXT3/DXT5/DXT5A/DXN/8_8_8_8), width,
    height, levels, data (LINEAR mip chain, base first -- tiled here), and the
    optional orig_dword11 / tex_vft / dict_vft carried from the parsed file.
    Requires an LZX instance with xcompress.dll (XMem* API) to produce a final
    file; pass compress=False for an uncompressed body (inspection only).
    """
    VFT_DICT = 0x0C836100      # grcTextureDictionary vtable in real GTA IV .xtd
    VFT_TEX  = 0x941A6300      # grcTextureXenon vtable in real GTA IV .xtd

    def __init__(self, textures, lzx=None):
        self.texs = textures
        self.lzx = lzx

    @staticmethod
    def _gpu_fmt_of(fmt):
        return {'DXT5':'GPUTEXTUREFORMAT_DXT4_5','DXT4_5':'GPUTEXTUREFORMAT_DXT4_5',
                'DXT3':'GPUTEXTUREFORMAT_DXT2_3','DXT2_3':'GPUTEXTUREFORMAT_DXT2_3',
                'DXT1':'GPUTEXTUREFORMAT_DXT1','DXT5A':'GPUTEXTUREFORMAT_DXT5A',
                'DXN':'GPUTEXTUREFORMAT_DXN','8_8_8_8':'GPUTEXTUREFORMAT_8_8_8_8',
                'A8R8G8B8':'GPUTEXTUREFORMAT_8_8_8_8'}.get(fmt.upper(),
                                                           'GPUTEXTUREFORMAT_DXT4_5')

    def build(self, compress=True):
        n = len(self.texs)
        if n == 0:
            raise RuntimeError("GTA IV dictionary needs at least one texture.")

        # ---- graphics segment: base mip + mip tail as SEPARATE blocks --------
        # Each texture contributes a base-mip block and, when it has mips, a
        # separate mip-tail block (levels 1..N). The Xbox 360 stores these as two
        # tiled regions addressed independently by dword_9 (base) and dword_13
        # (tail). Keeping them separate -- rather than concatenated -- reproduces
        # the console-correct layout, so mips load instead of crashing.
        #
        # block_meta[i] = list of (kind, idx) describing what each layout block is
        tiled_list = []
        block_meta = []          # parallel to tiled_list: ('base',i) or ('tail',i)
        base_block_of = {}       # idx -> layout-block index for its base
        tail_block_of = {}       # idx -> layout-block index for its mip tail
        for i, t in enumerate(self.texs):
            fmt = t['fmt'].upper()
            gpu_fmt = self._gpu_fmt_of(fmt)
            levels = max(1, t.get('levels', 1))
            tw, th = t['width'], t['height']

            # 1) BASE mip block
            if t.get('tiled_data') is not None:
                # verbatim base bytes (unedited console texture)
                base_tiled = bytes(t['tiled_data'])
            else:
                lin_fmt = {'DXT4_5':'DXT5','DXT2_3':'DXT3','DXT5A':'DXT1',
                           '8_8_8_8':'A8R8G8B8','DXN':'DXT5'}.get(fmt, fmt)
                src = t['data']
                bw_fmt = lin_fmt if lin_fmt in ('DXT1','DXT3','DXT5','A8R8G8B8') else 'DXT5'
                base_lin_sz = _block_bytes(bw_fmt, tw, th)
                base_tiled = retile_and_swap(src[:base_lin_sz], gpu_fmt, tw, th)
            base_block_of[i] = len(tiled_list)
            tiled_list.append(base_tiled)
            block_meta.append(('base', i))

            # 2) MIP-TAIL block (levels 1..N), only when the texture has mips
            if levels > 1:
                tail = bytes(t['mip_tail_data']) if t.get('mip_tail_data') else None
                if tail is None:
                    # build the tail by tiling each sub-mip at its own dimensions,
                    # matching the reference per-level 128-padded tiling.
                    lin_fmt = {'DXT4_5':'DXT5','DXT2_3':'DXT3','DXT5A':'DXT1',
                               '8_8_8_8':'A8R8G8B8','DXN':'DXT5'}.get(fmt, fmt)
                    bw_fmt = lin_fmt if lin_fmt in ('DXT1','DXT3','DXT5','A8R8G8B8') else 'DXT5'
                    src = t['data']
                    pos = _block_bytes(bw_fmt, tw, th)   # skip base
                    tbuf = bytearray()
                    for lvl in range(1, levels):
                        mw = max(1, tw >> lvl); mh = max(1, th >> lvl)
                        lin_sz = _block_bytes(bw_fmt, mw, mh)
                        tbuf += retile_and_swap(src[pos:pos+lin_sz], gpu_fmt, mw, mh)
                        pos += lin_sz
                    tail = bytes(tbuf)
                if tail:
                    # Xbox 360 packed mip-tail convention: the mip-tail block is
                    # page-aligned, and dword_13 points 0xA00 bytes INTO it. The
                    # first 0xA00 bytes are the tiled mip-tail header region; the
                    # actual mip levels begin at +0xA00. Every stock/Dageron file
                    # follows this (all mip addresses end in 0xA00); pointing at
                    # +0x000 instead -- as the old code did -- makes the GPU read
                    # the tail from the wrong place and hard-crash on fetch.
                    MIPTAIL_OFF = 0xA00
                    tail = (b'\x00' * MIPTAIL_OFF) + tail
                    tail_block_of[i] = len(tiled_list)
                    tiled_list.append(tail)
                    block_meta.append(('tail', i))

        # ---- flat graphics layout (GTA IV uses a FLAT graphics segment) ------
        # The console loader reads a flat graphics blob; the blockmap is empty
        # (verified against stock files) and descriptor dword_9/dword_13 are
        # direct offsets. The old tiered rage_page_layout overflowed its per-tier
        # block counts for large textures ("blocks too large to page"). Instead,
        # pack blocks largest-first on 0x2000-aligned boundaries -- a valid,
        # non-overlapping flat layout. It need not match Rockstar's exact packing
        # byte-for-byte; it only needs each block page-aligned and addressable.
        PAGE_UNIT = 0x2000
        def _algn(v): return (v + PAGE_UNIT - 1) // PAGE_UNIT * PAGE_UNIT
        # order: place all blocks largest-first for tight, deterministic packing
        order = sorted(range(len(tiled_list)), key=lambda k: -len(tiled_list[k]))
        gfx_offsets = [0] * len(tiled_list)
        pos = 0
        for k in order:
            gfx_offsets[k] = pos
            pos += _algn(len(tiled_list[k]))
        gfx_total = pos if pos else PAGE_UNIT
        gfx_buf_full = bytearray(gfx_total)
        for tiled, off in zip(tiled_list, gfx_offsets):
            gfx_buf_full[off:off+len(tiled)] = tiled
        # per-texture base and mip-tail addresses within the graphics segment.
        # The mip-tail block carries a 0xA00 lead-in (see build of tail), so the
        # mip address the GPU fetches is the block offset PLUS 0xA00 -- matching
        # the stock convention where every mip address ends in 0xA00.
        gfx_addr = [gfx_offsets[base_block_of[i]] for i in range(len(self.texs))]
        mip_addr = {i: gfx_offsets[tail_block_of[i]] + 0xA00 for i in tail_block_of}

        # ---- system segment (base 0x2000, page class 0x5) -------------------
        # Layout MUST match the order Rockstar/Dageron use, since that ordering
        # is what loads on real hardware:
        #   0x00   dict header (0x30)
        #   0x30   0x200-byte reserved/blockmap region (filled 0x00)
        #   0x230  grcTexture structs (0x40 each) + D3DBaseTexture descriptors
        #   ...    name strings
        #   end    texture-pointer array, then hash array
        # The earlier layout placed the pointer arrays right after the header and
        # doubled the system segment to 0x2000; a Dageron file that runs on
        # hardware keeps them at the END and fits in 0x1000. Reproduce that.
        sysseg = _Pager(0x5, 0x2000)
        sysseg.align(0x10)
        dict_hdr = sysseg.reserve(0x30)
        # reserved 0x200 region after the header (stock files leave this as a
        # blockmap page-entry area; the loader expects the structs to begin at
        # 0x230, not immediately after the header).
        sysseg.reserve(0x200)

        # Order textures by Jenkins hash of the bare name (as stock files do).
        pairs = sorted(((jenkins_hash(Path(t['name']).stem), i)
                        for i, t in enumerate(self.texs)), key=lambda p: p[0])
        order = [i for _, i in pairs]

        # grcTexture structs (0x40) -- one per texture, in hash order.
        struct_off = {}; desc_off = {}; name_fix = []
        for idx in order:
            t = self.texs[idx]
            w, h = t['width'], t['height']
            levels = max(1, t.get('levels', 1))
            sysseg.align(0x10)
            base = sysseg.reserve(0x40)
            struct_off[idx] = base
            tex_vft = t.get('tex_vft') or self.VFT_TEX
            sysseg.patch_u32_be(base+0x00, tex_vft)
            sysseg.patch_u32_be(base+0x08, 1)                 # usage/refcount
            sysseg.patch_u16_be(base+0x1C, w)
            sysseg.patch_u16_be(base+0x1E, h)
            sysseg.patch_u32_be(base+0x20, max(1, levels))    # mip count
            # three 1.0 floats observed at +0x24/+0x28/+0x2C
            for fo in (0x24, 0x28, 0x2C):
                sysseg.patch_u32_be(base+fo, 0x3F800000)
            name_fix.append((base+0x14, idx))

        # D3DBaseTexture descriptors (0x34) -- separate blocks, pointed to by
        # grcTexture +0x18.
        for idx in order:
            t = self.texs[idx]
            fmt = t['fmt'].upper()
            w, h = t['width'], t['height']
            levels = max(1, t.get('levels', 1))
            sysseg.align(0x10)
            d3d = sysseg.reserve(0x34)
            desc_off[idx] = d3d
            sysseg.patch_u32_be(struct_off[idx]+0x18, _ps3_vaddr(0x5, d3d))

            fmt_idx = XBOX_FMT_CODE.get(fmt, 20)
            pitch = _xbox_pitch_tiles(w)
            gpu_paged = _ps3_vaddr(0x6, gfx_addr[idx])
            # endian: 8_8_8_8/DXN use 8in32 (2); block formats use 8in16 (1)
            endian = 2 if fmt in ('8_8_8_8', 'A8R8G8B8', 'DXN') else 1
            sysseg.patch_u32_be(d3d+0x00, 0x00200003)              # dword_1
            sysseg.patch_u32_be(d3d+0x04, 0x00000001)             # dword_2
            sysseg.patch_u32_be(d3d+0x14, 0xFFFF0000)             # dword_6
            sysseg.patch_u32_be(d3d+0x18, 0xFFFF0000)             # dword_7
            sysseg.patch_u32_be(d3d+0x1C, (pitch << 22) | 0x80000002)  # dword_8
            dword9 = (gpu_paged & 0xFFFFF000) | ((endian & 3) << 6) | (fmt_idx & 0x3F)
            sysseg.patch_u32_be(d3d+0x20, dword9)                 # dword_9
            sysseg.patch_u32_be(d3d+0x24, ((h-1) << 13) | (w-1))  # dword_10 size_2d
            DWORD11 = {18:0x00000D10, 19:0x00000D10, 20:0x00000D10,
                       59:0x000015B6, 6:0x00000C14, 49:0x00000D10}
            d11 = t.get('orig_dword11') or DWORD11.get(fmt_idx, 0x00000D10)
            sysseg.patch_u32_be(d3d+0x28, d11 & 0xFFFFFFFF)       # dword_11
            # dword_12: MaxMipLevel register (stored big-endian).
            sysseg.patch_u32_be(d3d+0x2C, encode_mip_register(levels))
            # dword_13: address of this texture's mip-tail block (block + 0xA00).
            if levels > 1 and idx in mip_addr:
                sysseg.patch_u32_be(d3d+0x30, _ps3_vaddr(0x6, mip_addr[idx]))
            else:
                sysseg.patch_u32_be(d3d+0x30, 0x00000200)         # dword_13

        # name strings (kept as 'pack:/<name>.dds' like stock files)
        for slot, idx in name_fix:
            stem = Path(self.texs[idx]['name']).stem
            nm = ('pack:/' + stem + '.dds').encode('latin-1', 'replace') + b'\x00'
            noff = sysseg.write(nm)
            sysseg.patch_u32_be(slot, _ps3_vaddr(0x5, noff))

        # texture-pointer array and hash array -- at the END (stock ordering).
        sysseg.align(0x10); list_off = sysseg.tell()
        ptr_slots = [sysseg.reserve(4) for _ in range(n)]
        sysseg.align(0x10); hash_off = sysseg.tell()
        for hsh, _ in pairs:
            sysseg.write(struct.pack('>I', hsh))

        for k, idx in enumerate(order):
            sysseg.patch_u32_be(ptr_slots[k], _ps3_vaddr(0x5, struct_off[idx]))

        # dict header
        dict_vft = self.VFT_DICT
        for t in self.texs:
            if t.get('dict_vft'):
                dict_vft = t['dict_vft']; break
        sysseg.patch_u32_be(dict_hdr+0x00, dict_vft)
        sysseg.patch_u32_be(dict_hdr+0x04, _ps3_vaddr(0x5, 0x20))  # blockmap ptr
        sysseg.patch_u32_be(dict_hdr+0x08, 0)                      # parent
        sysseg.patch_u32_be(dict_hdr+0x0C, 1)                      # usage
        sysseg.patch_u32_be(dict_hdr+0x10, _ps3_vaddr(0x5, hash_off))
        sysseg.patch_u16_be(dict_hdr+0x14, n)
        sysseg.patch_u32_be(dict_hdr+0x18, _ps3_vaddr(0x5, list_off))
        sysseg.patch_u16_be(dict_hdr+0x1C, n)
        sysseg.patch_u16_be(dict_hdr+0x1E, n)

        # ---- assemble RSC5 container ----------------------------------------
        # Pad each segment up to a whole number of pages so the flag encoder can
        # describe it and the loader's size math matches. The SYSTEM segment uses
        # 0x1000 pages (a 9-texture dictionary fits in one 0x1000 page, exactly as
        # the working Dageron file does -- padding it to 0x2000 made the segment
        # twice the size the loader expects). Graphics uses 0x2000 pages.
        def _pad_pages(buf, base):
            total = ((len(buf) + base - 1) // base) * base
            return bytes(buf) + b'\x00' * (total - len(buf)), total
        sys_buf, sys_total = _pad_pages(sysseg.buf, 0x1000)
        gfx_buf, gfx_total2 = _pad_pages(gfx_buf_full, 0x2000)
        body = sys_buf + gfx_buf

        # Self-check: the dictionary header MUST sit at offset 0 of the system
        # segment and carry a real vtable + texture count. If it's blank, the
        # build went wrong and we must NOT emit a file the game would reject.
        hdr_vft = struct.unpack_from('>I', sys_buf, 0x00)[0]
        hdr_cnt = struct.unpack_from('>H', sys_buf, 0x1C)[0]
        if hdr_vft == 0 or hdr_cnt != n:
            raise RuntimeError(
                "Internal error building GTA IV dictionary: header not "
                f"populated (vft=0x{hdr_vft:08X}, count={hdr_cnt}, expected "
                f"{n}). Aborting so a corrupt .xtd is not written.")

        flags = encode_rsc05_flags(sys_total, gfx_total2)
        # Console GTA IV header is big-endian: magic '\x05CSR', version 7, flags.
        header  = b'\x05CSR'
        header += struct.pack('>I', 7)
        header += struct.pack('>I', flags)

        if compress:
            if not (self.lzx and getattr(self.lzx, 'available_xmem', False)):
                raise LZXError("GTA IV Xbox 360 .xtd needs xcompress.dll (XMem* "
                               "API, 32-bit Windows) to compress. Use a Windows "
                               "build, or write an uncompressed body to inspect.")
            comp = self.lzx.compress_blocks_xmem(body)
            return header + comp, len(sys_buf), len(gfx_buf)
        else:
            return header + body, len(sys_buf), len(gfx_buf)


class XtdWriter:
    """Build a GTA V Xbox 360 .xtd from builder-dict textures.

    texture dict: name, fmt (DXT1/DXT3/DXT5/DXT5A/DXN), width, height, levels,
                  data (LINEAR pixel bytes, base mip first -- they get tiled here).
    Requires an LZX instance with xCompress available to produce a final file;
    pass compress=False to write an uncompressed body for inspection.
    """
    VFT_DICT = 0xE0678100      # grcTextureDictionary vtable as it appears in
                               # real stock GTA V Xbox 360 .xtd files (verified
                               # against adder.xtd and a known-working police
                               # .xtd). The game dispatches through this, so it
                               # must match a real file or textures won't load.
                               # (Preserved from the source file when available.)
    VFT_TEX  = 0xA47A8500      # grcTextureXenon vtable from real stock files
                               # (verified). Using a wrong value here is what
                               # made rebuilt police textures fail to load.

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
            gpu_fmt = {'DXT5':'GPUTEXTUREFORMAT_DXT4_5',
                       'DXT4_5':'GPUTEXTUREFORMAT_DXT4_5',
                       'DXT3':'GPUTEXTUREFORMAT_DXT2_3',
                       'DXT2_3':'GPUTEXTUREFORMAT_DXT2_3',
                       'DXT1':'GPUTEXTUREFORMAT_DXT1',
                       'DXT5A':'GPUTEXTUREFORMAT_DXT5A',
                       '8_8_8_8':'GPUTEXTUREFORMAT_8_8_8_8'}.get(
                           fmt, 'GPUTEXTUREFORMAT_DXT4_5')
            levels = max(1, t.get('levels', 1))
            tw, th = t['width'], t['height']
            # t['data'] is the FULL linear mip chain (base first). Tile EACH
            # level separately at its own dimensions and concatenate, so the
            # mips survive the rebuild. (Tiling the whole chain as one base-size
            # block silently dropped every level below the base -- the cause of
            # multi-mip textures losing their distant LODs / failing to load.)
            tiled = bytearray()
            src = t['data']; pos = 0
            for lvl in range(levels):
                mw = max(1, tw >> lvl); mh = max(1, th >> lvl)
                lin_sz = _block_bytes(fmt if fmt in ('DXT1','DXT3','DXT5') else
                                      {'DXT4_5':'DXT5','DXT2_3':'DXT3',
                                       'DXT5A':'DXT1','8_8_8_8':'A8R8G8B8'}.get(fmt,'DXT5'),
                                      mw, mh)
                lvl_lin = src[pos:pos+lin_sz]; pos += lin_sz
                lvl_tiled = retile_and_swap(lvl_lin, gpu_fmt, mw, mh)
                tiled += lvl_tiled
            tiled = bytes(tiled)
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

            tex_vft = t.get('tex_vft') or self.VFT_TEX
            sysseg.patch_u32_be(base+0x00, tex_vft)
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
            # dword_11: the Xenon tiling/format register. Its exact value depends
            # on format AND dimensions/tiling mode (verified against real vehicle
            # textures), so when we have the ORIGINAL value from the parsed file
            # we preserve it byte-for-byte. Only for brand-new or format-converted
            # textures (no original) do we fall back to the per-format table,
            # which is correct for the verified HUD-icon cases.
            DWORD11 = {18:0x00000D10, 19:0x00000D10, 20:0x00000D10,
                       59:0x000015B6, 6:0x00000C14}
            orig11 = t.get('orig_dword11')
            d11 = orig11 if orig11 else DWORD11.get(fmt_idx, 0x00000D10)
            sysseg.patch_u32_be(d3d+0x28, d11 & 0xFFFFFFFF)        # dword_11
            # dword_12: MaxMipLevel register (stored big-endian).
            sysseg.patch_u32_be(d3d+0x2C, encode_mip_register(levels))
            # dword_13: mip-chain address = base + size of mip 0. Must be unique
            # per texture; the old (base & 0xFFFF0000) | 0x0A00 collided across
            # textures and crashed the GPU on mip fetch.
            if levels > 1:
                setup0 = _xbox_format_setup(gpu_fmt, w, h)
                mip0_size = setup0[0] if setup0 else 0
                mip_off = gfx_addr[idx] + mip0_size
                sysseg.patch_u32_be(d3d+0x30, _ps3_vaddr(0x6, mip_off))
            else:
                sysseg.patch_u32_be(d3d+0x30, 0x00000200)           # dword_13

        # name strings
        for slot, idx in name_fix:
            nm = Path(self.texs[idx]['name']).stem.encode('latin-1','replace') + b'\x00'
            noff = sysseg.write(nm)
            sysseg.patch_u32_be(slot, _ps3_vaddr(0x5, noff))

        for k, idx in enumerate(order):
            sysseg.patch_u32_be(ptr_slots[k], _ps3_vaddr(0x5, struct_off[idx]))

        # dict header
        dict_vft = self.VFT_DICT
        for t in self.texs:
            if t.get('dict_vft'):
                dict_vft = t['dict_vft']; break
        sysseg.patch_u32_be(dict_hdr+0x00, dict_vft)
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
        self._dict_dirty = False   # True after add/remove (forces full rebuild)

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
        self._wbits = -15 if platform == "PS3" else 15
        self.error_msg = ""
        # Reconstruct the 16-byte RSC7 header so save()/save_to_bytes() can
        # repack this resource into a valid standalone file (the RPF browser's
        # Export relies on this; without _raw, save() would raise "No source
        # resource loaded"). Header = '7CSR' + version + SystemFlags +
        # GraphicsFlags, all big-endian, exactly as a standalone console
        # resource on disk.
        try:
            self._raw = (CONSOLE_MAGIC
                         + struct.pack(">I", 13)
                         + struct.pack(">I", system_flags & 0xFFFFFFFF)
                         + struct.pack(">I", graphics_flags & 0xFFFFFFFF))
        except Exception:
            self._raw = b""
        self._sys_flags = system_flags
        self._gfx_flags = graphics_flags
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

    def mip_dimensions(self, tex):
        """Return [(w,h), ...] for each mip level of a texture (base first)."""
        dims=[]; w,h=tex.width,tex.height
        for _ in range(max(1, tex.mips)):
            dims.append((max(1,w), max(1,h)))
            if w<=1 and h<=1: break
            w=max(1,w>>1); h=max(1,h>>1)
        return dims

    def export_dds_mip(self, tex, mip_level=0):
        """
        Export a single mip level of a texture as its own DDS (at the level's
        own dimensions). mip_level 0 = base. Falls back to base if the level
        isn't available. Used for per-mip viewing.
        """
        dims = self.mip_dimensions(tex)
        if mip_level < 0 or mip_level >= len(dims):
            mip_level = 0
        mw, mh = dims[mip_level]
        gpu_fmt = tex.gpu_fmt or 'GPUTEXTUREFORMAT_DXT4_5'

        # A per-mip override (user replaced this specific level) wins, so the
        # preview shows their edit instead of reverting to the downsampled base.
        movr = getattr(tex, '_mip_overrides', None)
        if movr and mip_level in movr:
            ov_rgba, ow, oh = movr[mip_level]
            img = Image.frombytes("RGBA", (ow, oh), ov_rgba)
            if (mw, mh) != (ow, oh):
                img = img.resize((mw, mh), Image.LANCZOS)
            linear = encode_for_format(gpu_fmt, img.tobytes(), mw, mh)
            return make_dds(gpu_fmt, mw, mh, 1, linear)

        ov = getattr(tex, "_rgba_override", None)
        if ov is not None:
            img = Image.frombytes("RGBA", (ov[1], ov[2]), ov[0])
            if (mw,mh) != (ov[1],ov[2]):
                img = img.resize((mw,mh), Image.LANCZOS)
            linear = encode_for_format(gpu_fmt, img.tobytes(), mw, mh)
            return make_dds(gpu_fmt, mw, mh, 1, linear)

        if tex.platform in ("Xbox 360", "GTA4-Xbox 360"):
            off = tex.tex_offset + self.cpu_size
            if mip_level == 0:
                # base mip lives at dword_9 (tex_offset) and untiles cleanly
                data = untile_and_deswap(self._dec[off:], gpu_fmt, mw, mh, tex.endian)
                return make_dds(gpu_fmt, mw, mh, 1, data)
            # Sub-mip PREVIEW. The Xbox 360 packed mip-tail uses a hardware
            # addressing scheme whose exact per-level byte offsets can't be
            # reconstructed reliably from the descriptor alone, so reading the
            # tail directly previews as scrambled/striped images. For a correct,
            # clean preview we render what the level represents: the base mip
            # downsampled to this level's dimensions. (A user's explicit per-mip
            # replacement is handled above via _mip_overrides and still shows
            # through; the on-disk save path builds the real tail separately and
            # is unaffected by this preview choice.)
            try:
                base_data = untile_and_deswap(self._dec[off:], gpu_fmt,
                                              dims[0][0], dims[0][1], tex.endian)
                base_dds = make_dds(gpu_fmt, dims[0][0], dims[0][1], 1, base_data)
                bimg = Image.open(io.BytesIO(base_dds)).convert("RGBA")
                bimg = bimg.resize((mw, mh), Image.LANCZOS)
                lin = encode_for_format(gpu_fmt, bimg.tobytes(), mw, mh)
                return make_dds(gpu_fmt, mw, mh, 1, lin)
            except Exception:
                # last-resort: show the base itself
                base_data = untile_and_deswap(self._dec[off:], gpu_fmt,
                                              dims[0][0], dims[0][1], tex.endian)
                return make_dds(gpu_fmt, dims[0][0], dims[0][1], 1, base_data)
        elif tex.platform == "PS3":
            # PS3 RSX linear textures need unswizzle + channel byte-order fix for
            # 8_8_8_8 / 8 (this was handled in export_dds but got dropped here
            # when per-mip viewing was added, which is why PS3 8888 textures
            # previewed as yellow/striped swizzled garbage). For mip 0 defer to
            # export_dds, which has the correct per-format decoders. For sub-mips
            # decode the base then downscale to the level's size.
            if mip_level == 0:
                return self.export_dds(tex)
            base_dds = self.export_dds(tex)
            try:
                img = Image.open(io.BytesIO(base_dds)).convert("RGBA")
                if (img.width, img.height) != (mw, mh):
                    img = img.resize((mw, mh), Image.LANCZOS)
                if gpu_fmt in ('GPUTEXTUREFORMAT_8_8_8_8',):
                    # build a BGRA A8R8G8B8 DDS directly from the RGBA preview
                    src = img.tobytes(); bgra = bytearray(mw*mh*4)
                    for i in range(mw*mh):
                        r, g, b, a = src[i*4:i*4+4]
                        bgra[i*4]=b; bgra[i*4+1]=g; bgra[i*4+2]=r; bgra[i*4+3]=a
                    return make_dds('GPUTEXTUREFORMAT_8_8_8_8', mw, mh, 1, bytes(bgra))
                linear = encode_for_format(gpu_fmt, img.tobytes(), mw, mh)
                return make_dds(gpu_fmt, mw, mh, 1, linear)
            except Exception:
                return base_dds
        else:  # PC: raw_data holds the full chain, base first
            fmt = tex.fmt_name.upper()
            # Uncompressed formats (A8R8G8B8 etc.) aren't DXT blocks; for these,
            # and for the base level of any PC texture, defer to export_dds which
            # has the correct per-format decoders. (Using the DXT path here was
            # decoding A8R8G8B8 gradient/icon textures as DXT5 -> garbage/blank.)
            UNCOMPRESSED = ('A8R8G8B8','R8G8B8','A8','L8','A8L8','X8R8G8B8')
            if mip_level == 0 or fmt in UNCOMPRESSED:
                full = self.export_dds(tex)
                if mip_level == 0:
                    return full
                # uncompressed + sub-mip: decode base then downscale
                img = Image.open(io.BytesIO(full)).convert("RGBA")
                if (img.width, img.height) != (mw, mh):
                    img = img.resize((mw, mh), Image.LANCZOS)
                bgra = bytearray(mw*mh*4); src=img.tobytes()
                for i in range(mw*mh):
                    r,g,b,a = src[i*4:i*4+4]
                    bgra[i*4]=b; bgra[i*4+1]=g; bgra[i*4+2]=r; bgra[i*4+3]=a
                return make_dds('GPUTEXTUREFORMAT_8_8_8_8', mw, mh, 1, bytes(bgra))
            skip = 0
            for i in range(mip_level):
                skip += _block_bytes(fmt, dims[i][0], dims[i][1])
            size = _block_bytes(fmt, mw, mh)
            data = (tex.raw_data or b"")[skip:skip+size]
            gpu = {'DXT1':'GPUTEXTUREFORMAT_DXT1','DXT3':'GPUTEXTUREFORMAT_DXT2_3',
                   'DXT5':'GPUTEXTUREFORMAT_DXT4_5','ATI2':'GPUTEXTUREFORMAT_DXN',
                   'ATI1':'GPUTEXTUREFORMAT_DXT5A'}.get(fmt, 'GPUTEXTUREFORMAT_DXT4_5')
            return make_dds(gpu, mw, mh, 1, data)

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
            # Uncompressed formats (gradient/LUT textures) carry raw pixels, not
            # DXT blocks. Build an A8R8G8B8 DDS directly so they preview/export.
            if fmt in ('A8R8G8B8','R8G8B8','A8','L8','A8L8','X8R8G8B8'):
                w, h = tex.width, tex.height
                src = tex.raw_data or b""
                # expand to BGRA (DDS A8R8G8B8 byte order) for any of these.
                bgra = bytearray(w*h*4)
                if fmt in ('A8R8G8B8','X8R8G8B8'):
                    # RAGE PC stores A8R8G8B8 as BGRA bytes already (D3D order).
                    n = min(len(src), len(bgra)); bgra[:n] = src[:n]
                    if fmt == 'X8R8G8B8':
                        for p in range(3, len(bgra), 4): bgra[p] = 0xFF
                elif fmt == 'R8G8B8':
                    for i in range(w*h):
                        if i*3+2 < len(src):
                            bgra[i*4]=src[i*3+2]; bgra[i*4+1]=src[i*3+1]
                            bgra[i*4+2]=src[i*3]; bgra[i*4+3]=0xFF
                elif fmt in ('A8','L8'):
                    for i in range(w*h):
                        v = src[i] if i < len(src) else 0
                        if fmt == 'L8':
                            bgra[i*4]=bgra[i*4+1]=bgra[i*4+2]=v; bgra[i*4+3]=0xFF
                        else:  # A8 -> white with alpha
                            bgra[i*4]=bgra[i*4+1]=bgra[i*4+2]=0xFF; bgra[i*4+3]=v
                elif fmt == 'A8L8':
                    for i in range(w*h):
                        l = src[i*2] if i*2 < len(src) else 0
                        a = src[i*2+1] if i*2+1 < len(src) else 0
                        bgra[i*4]=bgra[i*4+1]=bgra[i*4+2]=l; bgra[i*4+3]=a
                return make_dds('GPUTEXTUREFORMAT_8_8_8_8', w, h, 1, bytes(bgra))
            gpu = {'DXT1':'GPUTEXTUREFORMAT_DXT1','DXT3':'GPUTEXTUREFORMAT_DXT2_3',
                   'DXT5':'GPUTEXTUREFORMAT_DXT4_5','ATI2':'GPUTEXTUREFORMAT_DXN',
                   'ATI1':'GPUTEXTUREFORMAT_DXT5A'}.get(fmt,'GPUTEXTUREFORMAT_DXT4_5')
            return make_dds(gpu, tex.width, tex.height, tex.mips, tex.raw_data)

    # ---- import / replace --------------------------------------------------
    def replace_texture(self, tex, image_path):
        """
        Replace the pixel data of an existing texture with an image from disk.

        For console textures (GTA IV/V Xbox 360, PS3) the new pixels are stashed
        as an RGBA override and applied by the full rebuild on Save As. This is
        the path that now produces hardware-correct files (the in-place splice
        predated the separate base/mip-tail layout and is no longer consistent
        with how the dictionary is written, which is what raised an error on
        replace for GTA IV Xbox 360). PC textures still splice in-place.
        """
        console = (tex.platform in ("Xbox 360", "PS3")
                   or "Xbox 360" in (tex.platform or "")
                   or "PS3" in (tex.platform or ""))
        if getattr(tex, "_converted", False) or console:
            rgba = self._load_rgba_sized(image_path, tex.width, tex.height)
            tex._rgba_override = (rgba, tex.width, tex.height)
            tex._user_painted = True   # real pixels supplied; rebuild lays it out
            self._dict_dirty = True
            return True
        if tex.platform == "PC":
            return self._replace_pc(tex, image_path)
        raise RuntimeError("Unsupported platform for replace.")

    def replace_texture_mip(self, tex, mip_level, image_path):
        """
        Replace a SINGLE mip level of a texture with an image from disk. The
        image is resized to that mip level's dimensions and stored as a per-mip
        override. On Save As the chain is rebuilt using each level's override
        where present (and downsampling the base for any level left untouched).

        This is what lets a user fix a 'snow returns at distance' mismatch: edit
        the base up close AND replace the lower mips that still carry the old
        (snowy) pixels, so the texture is consistent at every LOD.
        """
        if not PIL_AVAILABLE:
            raise RuntimeError("Pillow is required to import images.")
        dims = self.mip_dimensions(tex)
        if mip_level < 0 or mip_level >= len(dims):
            raise RuntimeError(f"Mip level {mip_level} out of range "
                               f"(texture has {len(dims)} levels).")
        mw, mh = dims[mip_level]
        img = Image.open(image_path).convert("RGBA")
        if (img.width, img.height) != (mw, mh):
            img = img.resize((mw, mh), Image.LANCZOS)
        if tex._mip_overrides is None:
            tex._mip_overrides = {}
        tex._mip_overrides[mip_level] = (img.tobytes(), mw, mh)
        # Editing a single mip means we keep the existing chain length and must
        # rebuild so the new level is written. Preserve current mip count.
        tex._mip_levels = max(tex.mips, len(dims))
        tex._converted = True       # routes through the rebuild path
        tex._user_painted = True
        self._dict_dirty = True
        return True

    def clear_mip_override(self, tex, mip_level=None):
        """Drop a per-mip override (or all of them if mip_level is None)."""
        if tex._mip_overrides is None:
            return
        if mip_level is None:
            tex._mip_overrides = None
        else:
            tex._mip_overrides.pop(mip_level, None)

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
    def save_to_bytes(self):
        """Repack via the proven save() path and return the resulting file's
        bytes (used by the RPF browser's Export, so exported resources are
        valid standalone files rather than fragile header+body reconstructions).
        """
        import tempfile
        fd, tmp = tempfile.mkstemp(suffix=Path(self.filepath or "res.xtd").suffix
                                   or ".xtd")
        os.close(fd)
        try:
            self.save(tmp)
            return Path(tmp).read_bytes()
        finally:
            try:
                os.remove(tmp)
            except Exception:
                pass

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
        dict_dirty = getattr(self, "_dict_dirty", False)

        # Normalize GTA IV platform names so save routing matches the writers.
        plat = self.platform
        is_xbox = plat in ("Xbox 360", "GTA4-Xbox 360")
        is_ps3  = plat in ("PS3", "GTA4-PS3")
        is_pc   = plat in ("PC", "GTA4-PC", "")

        # If textures were ADDED or REMOVED, the dictionary's structure changed
        # (count, hash table, offsets), so a full rebuild from the live list is
        # required for every platform.
        if dict_dirty:
            compress = (not is_xbox) or \
                       (self.lzx is not None and self.lzx.available_open)
            return self.save_rebuilt(out_path, compress=compress)

        if any_converted and is_pc:
            # PC: full rebuild from the live textures.
            return self.rebuild_pc(out_path, self.to_texture_list())

        # PS3: a converted dictionary is rebuilt cleanly through CtdWriter -- the
        # SAME path v32 used to produce .ctd files that do NOT freeze the
        # console. The in-place GPU surgery (_convert_ps3_inplace) and struct
        # cloning that were added later are what froze the PS3 at load, so PS3
        # conversion no longer uses them.
        if any_converted and is_ps3:
            return self.convert_to_ps3(out_path)

        # Xbox 360 conversion still uses the verified in-place GPU rebuild.
        if any_converted and is_xbox:
            conv = next((t for t in self.textures
                         if getattr(t, "_converted", False)), None)
            if conv is not None:
                rgba, w, h = self._decoded_rgba(conv)
                self._convert_xbox360_inplace(conv, conv.gpu_fmt, rgba, w, h)
                gpu_grew = getattr(self, "_gpu_grew", False)

        # ---- GTA IV / EFLC (RSC version 5): 12-byte header --------------------
        # Faithful port of the Pascal SaveResource for GTA IV: keep the original
        # 12-byte header (magic + rsctype + flags) verbatim -- the flags encode
        # the decompressed CPU/GPU sizes, which don't change for same-size edits
        # -- then recompress the (possibly edited) body with the platform codec:
        #   GTA4-Xbox 360 : XMem LZX (Codec 0) + 0xF112F50F marker prefix
        #   GTA4-PC/PS3   : zlib (same wbits the source used)
        is_gta4 = plat in ("GTA4-Xbox 360", "GTA4-PC", "GTA4-PS3")
        if is_gta4:
            if not self._raw or len(self._raw) < 12:
                raise RuntimeError("No source GTA IV resource loaded.")
            header = bytes(self._raw[:12])
            body = bytes(self._dec)
            if plat == "GTA4-Xbox 360":
                comp = self.lzx.compress_blocks_xmem(body)
            else:
                wbits = self._wbits if self._wbits in (15, -15, 47) else 15
                if wbits == 47:
                    wbits = 15
                co = zlib.compressobj(9, zlib.DEFLATED, wbits)
                comp = co.compress(body) + co.flush()
            Path(out_path).write_bytes(header + comp)
            return True

        if not self._raw or len(self._raw) < 16:
            raise RuntimeError("No source resource loaded.")
        body = bytes(self._dec)
        header = bytearray(self._raw[:16])   # RSC7 16-byte header (mutable)

        if gpu_grew:
            gfx_flag = getattr(self, "_new_gfx_flag", None)
            if gfx_flag is None:
                gpu_len = len(body) - self.cpu_size
                gfx_flag, _pages = _rsc7_flag_for_size(gpu_len, 0x2000, 13)
            struct.pack_into('<I', header, 12, EndianChangeDWORD(gfx_flag))

        if is_xbox:
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
            # PS3: do NOT do in-place GPU surgery. Just stash the new pixels and
            # mark converted; Save As rebuilds the whole .ctd cleanly through
            # CtdWriter (the v32 path that does not freeze the console). The
            # in-place rebuild + struct manipulation is what caused the freeze.
            tex._rgba_override = (rgba, w, h)
            tex._converted = True
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
        #    dword_11 (the Xenon tiling/format register) is only rewritten for
        #    the texture whose FORMAT actually changed -- every other texture
        #    keeps its original dword_11 from the source file, because that value
        #    also depends on dimensions/tiling, not just format (verified against
        #    real multi-mip vehicle textures). Rewriting the converted texture's
        #    dword_11 to the new format's value is what makes a DXT5A->colour
        #    icon stop rendering monochrome.
        DWORD11_FOR_FMT = {
            18: 0x00000D10,  # DXT1
            19: 0x00000D10,  # DXT2_3 (DXT3)
            20: 0x00000D10,  # DXT4_5 (DXT5)
            59: 0x000015B6,  # DXT5A
            6:  0x00000C14,  # 8_8_8_8
        }
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
            # Only the converted texture's dword_11 changes (its format changed).
            if t is tex:
                d11 = DWORD11_FOR_FMT.get(fmt_idx)
                if d11 is not None:
                    struct.pack_into('>I', self._dec, d3doff + 0x28, d11)
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
        """
        Convert a PS3 texture's format by rebuilding the GPU block (same safe
        approach as Xbox 360). PS3 (RSX) texture structs are simpler than
        Xbox's: the format lives in a single byte at struct+0x08, with no
        separate format-dependent tiling register, so patching that byte plus
        re-laying the GPU data is sufficient.

        NOTE: PS3 GPU layout has not been verified against a real edited .ctd in
        game the way the Xbox 360 path has. The structure here mirrors the
        verified Xbox logic; treat PS3 conversion as functional-but-unverified
        until confirmed on hardware.
        """
        soff = self._ps3_struct_offset(tex)
        if soff is None:
            raise RuntimeError("Could not locate the PS3 texture struct for "
                               "in-place conversion.")
        self._ensure_mutable()

        # Re-encode every texture (converted one in new format, others kept) and
        # lay them out FLAT (PS3 graphics is a flat linear block; the tiered
        # rage_page_layout overflowed its per-tier block counts on larger
        # textures -- 512x256 etc. -- which is the "blocks too large to page"
        # error). A flat largest-first packer is valid and never overflows.
        #
        # CRITICAL: only the texture being converted is re-encoded. Every OTHER
        # texture is carried VERBATIM from its original GPU bytes. Decoding an
        # unedited texture to RGBA and re-encoding is lossy and, for PS3 DXT3/DXT5
        # and 8_8_8_8, risks a swizzle/byte-order mismatch -- which is exactly
        # what corrupted all the OTHER textures when only one was converted.
        per_tex = []
        for t in self.textures:
            if t is tex:
                fmt = new_gpu; trgba, tw, th = rgba, w, h
                linear = encode_for_format(fmt, trgba, tw, th)
                if fmt == 'GPUTEXTUREFORMAT_8_8_8_8':
                    linear = _dds_8888_to_ps3(linear)
                    linear = ps3_swizzle(linear, tw, th, 4)
                elif fmt == 'GPUTEXTUREFORMAT_8':
                    linear = ps3_swizzle(linear, tw, th, 1)
                size = ps3_data_size(fmt, tw, th)
                data = linear[:size] if size else linear
            else:
                # carry the ORIGINAL GPU bytes for this texture verbatim
                fmt = t.gpu_fmt
                size = ps3_data_size(fmt, t.width, t.height)
                src_off = self.cpu_size + (t.tex_offset or 0)
                data = bytes(self._dec[src_off:src_off + size])
                if len(data) < size:                      # safety pad
                    data = data + b'\x00' * (size - len(data))
            per_tex.append((t, fmt, data, len(data)))

        PAGE_UNIT = 0x80   # PS3 textures are 0x80-aligned in the graphics block
        def _algn(v): return (v + PAGE_UNIT - 1) // PAGE_UNIT * PAGE_UNIT
        order = sorted(range(len(per_tex)), key=lambda k: -per_tex[k][3])
        offsets = [0] * len(per_tex)
        pos = 0
        for k in order:
            offsets[k] = pos
            pos += _algn(per_tex[k][3])
        total = pos if pos else PAGE_UNIT
        new_gpu_block = bytearray(total)
        for (t, fmt, data, _sz), off in zip(per_tex, offsets):
            new_gpu_block[off:off+len(data)] = data
        self._dec = bytearray(self._dec[:self.cpu_size]) + new_gpu_block

        # Patch each struct: format byte (+0x08), mip count (+0x09 -> 1),
        # data offset (+0x1C).
        ps3_code = {'GPUTEXTUREFORMAT_DXT1':134, 'GPUTEXTUREFORMAT_DXT2_3':135,
                    'GPUTEXTUREFORMAT_DXT4_5':136,
                    'GPUTEXTUREFORMAT_8_8_8_8':133}.get(new_gpu, 136)
        for (t, fmt, data, _sz), off in zip(per_tex, offsets):
            so = self._ps3_struct_offset(t)
            if so is None:
                continue
            if t is tex and so + 0x08 < len(self._dec):
                self._dec[so + 0x08] = ps3_code & 0xFF
                if so + 0x09 < len(self._dec):
                    self._dec[so + 0x09] = 1   # single mip
            # data offset (+0x1C) as a paged vaddr
            if so + 0x1C + 4 <= len(self._dec):
                struct.pack_into('>I', self._dec, so + 0x1C,
                                 EndianChangeDWORD(_ps3_vaddr(0x6, off)))
            t.tex_offset = off
            if t is tex:
                t.texture_type = ps3_code
                t.mips = 1

        # PS3 graphics flag uses base 0x1580 in the header math.
        gpu_len = total
        gfx_flag, _pages = _rsc7_flag_for_size(gpu_len, 0x1580, 13)
        self._new_gfx_flag = gfx_flag & 0xFFFFFFFF
        self._new_gfx_base = 0x1580
        self.gpu_size = total
        self._gpu_grew = True
        tex._converted = True

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
        """Absolute offset of a PS3 grcTexture struct (mirrors parse_ps3)."""
        try:
            buf = self._dec
            r = R(buf); r.seek(0)
            for _ in range(5): r.u32_le()        # vmt, omap, fC, f10, hash
            count = EndianChangeWORD(r.u16_le())
            r.u16_le()                            # count2
            listoff = GetOffset(EndianChangeDWORD(r.u32_le()))
            r.seek(listoff)
            offs = [GetOffset(EndianChangeDWORD(r.u32_le())) for _ in range(count)]
            return offs[tex.index] if tex.index < len(offs) else None
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

    def add_texture_from_image(self, name, image_path, fmt='DXT5', levels=1):
        """
        Add a new texture (from an image on disk) to the live dictionary. Works
        for every platform: the texture is decoded to RGBA and appended; the
        next Save As rebuilds the dictionary with the new texture laid out
        correctly. Returns the new TexEntry.
        """
        if not PIL_AVAILABLE:
            raise RuntimeError("Pillow is required to import images.")
        img = Image.open(image_path).convert("RGBA")
        w, h = img.width, img.height
        # DXT formats need multiple-of-4 dimensions.
        if fmt.upper() in ('DXT1','DXT3','DXT5','DXT5A'):
            nw=(w+3)&~3; nh=(h+3)&~3
            if (nw,nh)!=(w,h):
                img=img.resize((nw,nh), Image.LANCZOS); w,h=nw,nh
        gpu = {'DXT1':'GPUTEXTUREFORMAT_DXT1','DXT3':'GPUTEXTUREFORMAT_DXT2_3',
               'DXT5':'GPUTEXTUREFORMAT_DXT4_5','DXT5A':'GPUTEXTUREFORMAT_DXT5A',
               '8_8_8_8':'GPUTEXTUREFORMAT_8_8_8_8'}.get(fmt.upper(),
               'GPUTEXTUREFORMAT_DXT4_5')
        t = TexEntry()
        t.name = name if name.lower().endswith('.dds') else name + '.dds'
        t.width=w; t.height=h; t.mips=1
        t.platform=self.platform
        t.gpu_fmt=gpu
        t.fmt_name=gpu.replace('GPUTEXTUREFORMAT_','')
        t.index=len(self.textures)
        t._rgba_override=(img.tobytes(), w, h)
        t._converted=True   # forces the rebuild path on save
        t._user_painted=True
        self.textures.append(t)
        self._dict_dirty=True
        return t

    def remove_textures(self, texs):
        """Remove one or more textures from the live dictionary. The change
        takes effect on the next Save As (full rebuild)."""
        remove_set = set(id(x) for x in texs)
        self.textures = [t for t in self.textures if id(t) not in remove_set]
        for i, t in enumerate(self.textures):
            t.index = i
        self._dict_dirty = True
        # mark dirty so save rebuilds
        if self.textures:
            self.textures[0]._converted = True

    def save_rebuilt(self, out_path, compress=True):
        """
        Rebuild the whole dictionary from the current texture list (after
        add/remove/mip edits) and write it. Routes to the correct platform
        writer.
        """
        texlist = self.to_texture_list()
        if not texlist:
            raise RuntimeError("Dictionary has no textures to save.")
        # Normalize platform: a GTA IV file is detected as "GTA4-Xbox 360" /
        # "GTA4-PS3" / "GTA4-PC", but the writers are keyed on the bare console
        # name. Without this, a GTA IV Xbox 360 (.xtd) source falls through to
        # the PC YtdWriter and is wrongly written as a little-endian 'RSC7' file.
        plat = self.platform
        # GTA IV (RSC v5) uses its own container/dictionary layout, distinct
        # from the GTA V-era RSC7 writers. Route structural rebuilds (add/remove
        # texture) to the dedicated GTA IV writers.
        if plat == "GTA4-Xbox 360":
            if not compress:
                if not (self.lzx is not None and getattr(self.lzx, 'available_xmem', False)):
                    raise RuntimeError(
                        "Cannot write a loadable GTA IV Xbox 360 .xtd without "
                        "LZX compression. xcompress.dll (XMem* API, 32-bit "
                        "Windows) is required.")
            blob, _, _ = Xtd4Writer(texlist, self.lzx).build(compress=compress)
            Path(out_path).write_bytes(blob)
            return True
        if plat in ("GTA4-PC", "GTA4-PS3"):
            raise RuntimeError(
                "Adding or removing textures is currently supported for GTA IV "
                "Xbox 360 (.xtd) only. GTA IV PC (.wtd) and PS3 dictionary "
                "writers are not implemented yet. You can still Replace a "
                "texture's image or Convert its format and Save As.")
        is_xbox = plat in ("Xbox 360", "GTA4-Xbox 360")
        is_ps3  = plat in ("PS3", "GTA4-PS3")
        if is_xbox:
            # An uncompressed Xbox 360 .xtd will NOT load in game. Refuse to
            # write one silently (this produced tiny, unloadable files before).
            if not compress:
                if not (self.lzx is not None and getattr(self.lzx,'available_open',False)):
                    raise RuntimeError(
                        "Cannot write a loadable Xbox 360 .xtd without LZX "
                        "compression. xcompress_open.dll (32-bit Windows) is "
                        "required. Run the 32-bit Windows build to save Xbox 360 "
                        "files.")
            blob,_,_ = XtdWriter(texlist, self.lzx).build(compress=compress)
        elif is_ps3:
            blob,_,_ = CtdWriter(texlist).build()
        else:
            blob,_,_ = YtdWriter(texlist).build()
        Path(out_path).write_bytes(blob)
        return True

    def generate_mips(self, tex, levels='auto'):
        """
        Regenerate a texture with a full (or N-level) mip chain from its current
        base image. The chain is built by downsampling the current top mip and
        re-encoding each level in the texture's existing format. Takes effect on
        the next Save As (full rebuild). Returns the new level count.

        levels: 'auto' = full chain down to 1x1, or an integer level count.
        """
        rgba, w, h = self._decoded_rgba(tex)
        img = Image.frombytes("RGBA", (w, h), rgba)
        # how many levels?
        maxlev = 1; d = max(w, h)
        while d > 1: d >>= 1; maxlev += 1
        if levels in ('auto', -1, None):
            nlev = maxlev
        else:
            nlev = max(1, min(int(levels), maxlev))
        tex.mips = nlev
        # Store the full-resolution RGBA as the override; the rebuild path
        # (XtdWriter / CtdWriter / YtdWriter) regenerates the chain from it via
        # the 'levels' field. Mark dirty so Save As does a full rebuild.
        tex._rgba_override = (img.tobytes(), w, h)
        tex._mip_levels = nlev
        tex._converted = True
        self._dict_dirty = True
        return nlev

    def to_texture_list(self):
        """
        Snapshot every current texture as a builder dict
        (name, fmt, width, height, levels, data) for the dictionary writers.
        Pixel data is re-encoded from the live RGBA so it is always
        self-consistent. The texture's real format is preserved (DXT5A and
        8_8_8_8 included) so a rebuild does not silently downgrade formats.
        """
        out = []
        fmt_to_gpu = {'DXT1':'GPUTEXTUREFORMAT_DXT1',
                      'DXT3':'GPUTEXTUREFORMAT_DXT2_3',
                      'DXT2_3':'GPUTEXTUREFORMAT_DXT2_3',
                      'DXT5':'GPUTEXTUREFORMAT_DXT4_5',
                      'DXT4_5':'GPUTEXTUREFORMAT_DXT4_5',
                      'DXT5A':'GPUTEXTUREFORMAT_DXT5A',
                      '8_8_8_8':'GPUTEXTUREFORMAT_8_8_8_8'}
        for t in self.textures:
            fmt = (t.fmt_name or 'DXT4_5').upper()
            gpu = fmt_to_gpu.get(fmt, 'GPUTEXTUREFORMAT_DXT4_5')
            # Fast, lossless path: an UN-edited console texture (GTA IV/V Xbox360
            # or PS3) still holds its original, correctly-sized GPU bytes in
            # raw_data. Re-decoding it to RGBA and re-encoding can introduce fill
            # bytes if anything about the untile is imperfect, which is what
            # corrupted rebuilt GTA IV dictionaries (0xDC-filled graphics). When
            # the texture wasn't painted/converted and raw_data is the expected
            # tiled size, carry those exact bytes through so the writer can place
            # them verbatim (it skips re-tiling when 'tiled_data' is provided).
            edited = (getattr(t, '_rgba_override', None) is not None or
                      getattr(t, '_user_painted', False) or
                      getattr(t, '_converted', False) or
                      getattr(t, '_mip_overrides', None))
            console_plat = (t.platform or "").replace("GTA4-", "") in ("Xbox 360", "PS3") \
                           or "Xbox 360" in (t.platform or "") or "PS3" in (t.platform or "")
            raw = getattr(t, 'raw_data', None)
            base_blk = getattr(t, '_full_gpu_data', None)
            tail_blk = getattr(t, '_mip_tail_data', None)

            # Lossless MIPPED path: an unedited console texture with a mip chain
            # keeps its base block AND its console-correct mip-tail block verbatim.
            # The writer re-places both and re-points dword_13, so the stock mip
            # layout (which loads on hardware) is preserved exactly.
            #
            # IMPORTANT: this also covers the case where the user "edited" ONLY the
            # mip maps of a console texture (the common GTA IV workflow of trying
            # to fix broken mips). Re-tiling the base from decoded RGBA can shift
            # bytes vs the original and, together with a regenerated mip tail,
            # crashes the console. Since stock mip tails are uninitialised filler
            # that the game tolerates, the safe, hardware-proven behaviour is to
            # keep BOTH the original base and the original mip tail verbatim
            # whenever the base itself was not repainted. We therefore treat a
            # mip-only edit (no _rgba_override / _user_painted / base convert) the
            # same as no edit for console textures that still have their original
            # blocks captured.
            base_repainted = (getattr(t, '_rgba_override', None) is not None or
                              getattr(t, '_user_painted', False) or
                              getattr(t, '_converted', False))
            mip_only_edit = (getattr(t, '_mip_overrides', None) is not None
                             and not base_repainted)
            if (console_plat and base_blk and tail_blk and (t.mips or 1) > 1
                    and (not edited or mip_only_edit)):
                setup = _xbox_format_setup(t.gpu_fmt, t.width, t.height) if t.gpu_fmt else None
                base_sz = setup[0] if setup else len(base_blk)
                out.append(dict(
                    name=t.display_name, fmt=fmt if fmt in fmt_to_gpu else 'DXT5',
                    width=t.width, height=t.height, levels=t.mips,
                    tiled_data=bytes(base_blk[:base_sz]),
                    mip_tail_data=bytes(tail_blk),
                    orig_dword11=getattr(t, '_orig_dword11', None),
                    tex_vft=getattr(t, '_tex_vft', None),
                    dict_vft=getattr(t, '_dict_vft', None)))
                continue

            if (not edited) and console_plat and raw:
                want = None
                if t.gpu_fmt:
                    setup = _xbox_format_setup(t.gpu_fmt, t.width, t.height)
                    # For multi-mip, the tiled chain is larger; only fast-path
                    # single-mip where the size is unambiguous and verified.
                    if setup and (t.mips or 1) == 1:
                        want = setup[0]
                if want is not None and len(raw) >= want:
                    out.append(dict(
                        name=t.display_name, fmt=fmt if fmt in fmt_to_gpu else 'DXT5',
                        width=t.width, height=t.height, levels=1,
                        tiled_data=bytes(raw[:want]),
                        orig_dword11=getattr(t, '_orig_dword11', None),
                        tex_vft=getattr(t, '_tex_vft', None),
                        dict_vft=getattr(t, '_dict_vft', None)))
                    continue
            rgba, w, h = self._decoded_rgba(t)
            # Preserve the texture's existing mip count by default. The user only
            # overrides it via generate_mips, which sets _mip_levels > 1. Since
            # the slot defaults to 1, treat _mip_levels<=1 as "use the texture's
            # real mip count" so add/remove never flattens existing chains.
            req = getattr(t, '_mip_levels', 1) or 1
            nlev = max(1, req if req > 1 else (t.mips or 1))
            if nlev > 1:
                # Build the chain. For each level, use the user's per-mip
                # override image if they replaced that specific level; otherwise
                # downsample the base. This is what lets a user fix lower mips
                # that still carry old data (e.g. snow that returns at distance).
                img = Image.frombytes("RGBA", (w, h), rgba)
                overrides = getattr(t, '_mip_overrides', None) or {}
                chain = bytearray()
                for i in range(nlev):
                    mw = max(1, w >> i); mh = max(1, h >> i)
                    if i in overrides:
                        ov_rgba, ow, oh = overrides[i]
                        if (ow, oh) != (mw, mh):
                            ov_img = Image.frombytes("RGBA", (ow, oh), ov_rgba)
                            ov_img = ov_img.resize((mw, mh), Image.LANCZOS)
                            lvl_bytes = ov_img.tobytes()
                        else:
                            lvl_bytes = ov_rgba
                    elif i == 0:
                        lvl_bytes = img.tobytes()
                    else:
                        lvl_bytes = img.resize((mw, mh), Image.LANCZOS).tobytes()
                    chain += encode_for_format(gpu, lvl_bytes, mw, mh)
                data = bytes(chain)
            else:
                data = encode_for_format(gpu, rgba, w, h)
            # PS3 RSX storage conversion for linear formats. encode_for_format
            # emits little-endian DDS bytes ([B,G,R,A] for 8_8_8_8) in linear
            # order, but the PS3 stores 8_8_8_8 as big-endian [A,R,G,B] and
            # power-of-two linear textures SWIZZLED (Morton order). The in-place
            # _replace_ps3 path applied this, but the full-rebuild path
            # (to_texture_list -> CtdWriter) did not, so a PS3 texture edited and
            # saved came out byte-swapped/unswizzled -> corrupted on reload
            # (the savingspinner 8_8_8_8 case). Apply the same conversion here so
            # both save paths agree.
            is_ps3_plat = (t.platform or "").replace("GTA4-", "") == "PS3" \
                          or "PS3" in (t.platform or "")
            if is_ps3_plat and nlev == 1:
                if gpu == 'GPUTEXTUREFORMAT_8_8_8_8':
                    data = _dds_8888_to_ps3(data)
                    data = ps3_swizzle(data, w, h, 4)
                elif gpu == 'GPUTEXTUREFORMAT_8':
                    data = ps3_swizzle(data, w, h, 1)
            builder_fmt = {'GPUTEXTUREFORMAT_DXT1':'DXT1',
                           'GPUTEXTUREFORMAT_DXT2_3':'DXT3',
                           'GPUTEXTUREFORMAT_DXT4_5':'DXT5',
                           'GPUTEXTUREFORMAT_DXT5A':'DXT5A',
                           'GPUTEXTUREFORMAT_8_8_8_8':'8_8_8_8'}[gpu]
            out.append(dict(name=t.display_name, fmt=builder_fmt,
                            width=w, height=h, levels=nlev, data=data,
                            orig_dword11=getattr(t, '_orig_dword11', None),
                            tex_vft=getattr(t, '_tex_vft', None),
                            dict_vft=getattr(t, '_dict_vft', None),
                            ps3_regs=getattr(t, '_ps3_regs', None),
                            ps3_struct_raw=getattr(t, '_ps3_struct_raw', None),
                            # keep the exact original PS3 format code for a
                            # same-format edit (codes 134 vs 166 etc. encode RSX
                            # state); only drop it when the format was converted.
                            orig_fmt_code=(None if getattr(t, '_converted', False)
                                           else getattr(t, 'texture_type', None))))
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

    def extract_to_disk_bytes(self, entry, lzx=None):
        """
        Bytes suitable for writing a standalone file to disk.

        For TEXTURE resources (.xtd/.ctd/.ytd/.wtd) the previous approach of
        prepending a '7CSR' header to the still-compressed RPF body produced
        files that other tools failed to open (the RPF body framing / sub-header
        skip is not identical to a standalone OpenIV resource, so re-opening saw
        corrupted data). Instead, decompress the resource the SAME way the
        "Open in Editor" path does -- which is known good -- then repack it
        through the editor's proven resource writer so the saved file is a clean,
        valid standalone .xtd/.ctd/.ytd. For non-texture resources we keep the
        header+body reconstruction (the editor can't repack those).
        """
        if entry.is_resource:
            ext = Path(entry.name).suffix.lower()
            if ext in (".xtd", ".ctd", ".ytd", ".wtd") and lzx is not None:
                try:
                    dec = self.extract(entry)        # decompressed full buffer
                    td = TextureDict(lzx)
                    td.load_from_decompressed(dec, self.platform,
                                              entry.system_flags,
                                              entry.graphics_flags,
                                              name=entry.name)
                    if not td.error_msg:
                        return td.save_to_bytes()
                except Exception:
                    pass   # fall back to raw reconstruction below
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
        self._btn_find = abtn("Find Texture in RPFs…", self._find_texture_in_rpfs, YELLOW)
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
                raw = cur_arc.extract_to_disk_bytes(entry, lzx=self.app.lzx)
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
                Path(out).write_bytes(self.arc.extract_to_disk_bytes(e, lzx=self.app.lzx))
                self._setstatus(f"Extracted: {Path(out).name}")
            except Exception as ex:
                messagebox.showerror("Extract Error", str(ex), parent=self)
        else:
            folder = filedialog.askdirectory(title="Extract Files To…", parent=self)
            if not folder: return
            ok = err = 0
            for e in entries:
                try:
                    Path(folder, e.name).write_bytes(self.arc.extract_to_disk_bytes(e, lzx=self.app.lzx)); ok += 1
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
                dest.write_bytes(self.arc.extract_to_disk_bytes(e, lzx=self.app.lzx)); ok += 1
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

    def _find_texture_in_rpfs(self):
        """
        Scan a folder of RPF archives for a texture (or texture-dictionary)
        name. This finds DLC/update archives that contain their OWN copy of a
        texture -- the copy the game actually loads, which silently overrides
        edits made to the base archive. Essential for diagnosing 'my changes
        don't show up in game'.
        """
        name = simpledialog.askstring(
            "Find Texture in RPFs",
            "Texture or file name to search for (e.g. radio_stations,\n"
            "GTAV_Radio_Stations_Texture_256, or hud.xtd).\n"
            "Partial matches are fine.",
            parent=self)
        if not name:
            return
        name_l = name.lower().strip()
        folder = filedialog.askdirectory(
            title="Folder to scan for .rpf archives (searches subfolders)",
            parent=self)
        if not folder:
            return

        self._set_busy(True, f"Scanning for '{name}'…")
        import threading
        key = self.key
        plat = self._plat_var.get()
        lzx = self.app.lzx

        def worker():
            rpfs = []
            for root, _dirs, files in os.walk(folder):
                for fn in files:
                    if fn.lower().endswith(".rpf"):
                        rpfs.append(os.path.join(root, fn))
            hits = []   # (archive_path, matched_file_path)
            scanned = 0
            for rp in rpfs:
                try:
                    with open(rp, "rb") as f:
                        raw = f.read()
                    if raw[:4] != RPF7_MAGIC:
                        continue
                    arc = RPFArchive.open_bytes(raw, key, lzx=lzx,
                                                platform=plat, path=rp)
                    scanned += 1
                    for e in arc.iter_files():
                        if name_l in e.name.lower() or name_l in e.path.lower():
                            hits.append((rp, e.path or e.name))
                    # also descend into nested RPFs one level (DLC mounts)
                    for e in arc.iter_files():
                        if e.name.lower().endswith(".rpf"):
                            try:
                                nraw = arc.extract_to_disk_bytes(e, lzx=self.app.lzx)
                                if nraw[:4] == RPF7_MAGIC:
                                    nested = RPFArchive.open_bytes(
                                        nraw, key, lzx=lzx, platform=plat,
                                        path=rp + "/" + e.name)
                                    for ne in nested.iter_files():
                                        if name_l in ne.name.lower():
                                            hits.append((rp + " > " + e.name,
                                                         ne.path or ne.name))
                            except Exception:
                                pass
                except Exception:
                    continue
            self.after(0, lambda: self._show_scan_results(
                name, scanned, len(rpfs), hits))
        threading.Thread(target=worker, daemon=True).start()

    def _show_scan_results(self, name, scanned, total, hits):
        self._set_busy(False)
        if not hits:
            self._setstatus(f"'{name}' not found in {scanned} archive(s).")
            messagebox.showinfo(
                "Find Texture in RPFs",
                f"Scanned {scanned} of {total} .rpf file(s).\n\n"
                f"No archive contained '{name}'.\n\n"
                "If you expected an override, try a shorter/partial name, or "
                "check that the key/platform match these archives.",
                parent=self)
            return
        # Group by archive
        lines = []
        for arc_path, file_path in hits[:60]:
            lines.append(f"• {Path(arc_path).name}  →  {file_path}")
        extra = "" if len(hits) <= 60 else f"\n…and {len(hits)-60} more."
        msg = (f"Found '{name}' in {len(hits)} location(s) across "
               f"{scanned} archive(s):\n\n" + "\n".join(lines) + extra +
               "\n\nIf more than one archive contains this texture, the one "
               "loaded LAST (usually a DLC/update mount) wins — that's the copy "
               "the game shows, and it overrides edits to the others.")
        self._setstatus(f"'{name}' found in {len(hits)} location(s).")
        messagebox.showinfo("Find Texture in RPFs", msg, parent=self)


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
        self._img_source = None          # set when a resource came from a .img
        self._gtaiv_exe_path = None      # remembered GTAIV.exe (shared key src)
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
        fm.add_command(label="Open IMG Archive (Browser)...\tCtrl+I", command=self._open_img_browser)
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
        ib = tk.Button(bar, text="IMG Browser", command=self._open_img_browser,
                       bg=YELLOW, fg="#1e1e2e", activebackground=BTNACT,
                       activeforeground=FG, relief="flat", padx=10, pady=3,
                       cursor="hand2", font=("Segoe UI", 9, "bold"))
        ib.pack(side="left", padx=3)
        tk.Frame(bar, bg=PANEL, width=6).pack(side="left")
        btn("New .ytd", self._new_dict)
        btn("Add Texture", self._add_texture)
        btn("Remove Texture", self._remove_sel)
        btn("Replace", self._replace_sel)
        btn("Generate Mips", self._generate_mips_sel)
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
        self._tree=ttk.Treeview(f,columns=cols,show="headings",selectmode="extended")
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
        # Mip-level selector (only shown for multi-mip textures).
        self._mipbar=tk.Frame(f,bg=BG)
        self._mipbar.pack(fill="x",pady=(2,0))
        self._mip_level=0
        lf=tk.LabelFrame(f,text=" Texture Info ",bg=BG,fg=ACCENT,font=("Segoe UI",9,"bold"),
                         padx=8,pady=4,relief="flat",highlightbackground=ENTRY,highlightthickness=1)
        lf.pack(fill="x",pady=(4,0))
        self._info=tk.Text(lf,height=9,bg=PANEL,fg=FG,font=("Consolas",9),relief="flat",
                           state="disabled",cursor="arrow",selectbackground=ACCENT)
        self._info.pack(fill="x")

    def _build_mip_selector(self, tex):
        """Show a row of mip-level buttons + per-mip actions for multi-mip
        textures; hide entirely for single-mip textures."""
        for w in self._mipbar.winfo_children():
            w.destroy()
        dims = self.td.mip_dimensions(tex) if self.td else [(tex.width,tex.height)]
        if len(dims) <= 1:
            return
        tk.Label(self._mipbar, text="Mip:", bg=BG, fg=MAUVE,
                 font=("Segoe UI",8,"bold")).pack(side="left", padx=(4,2))
        ovr = getattr(tex, '_mip_overrides', None) or {}
        for lvl,(mw,mh) in enumerate(dims):
            sel = (lvl == self._mip_level)
            edited = lvl in ovr
            label = f"{lvl}: {mw}×{mh}" + (" *" if edited else "")
            b=tk.Button(self._mipbar, text=label,
                        command=lambda l=lvl: self._select_mip(tex, l),
                        bg=(ACCENT if sel else (TEAL if edited else BTN)),
                        fg=(BG if (sel or edited) else FG),
                        activebackground=BTNACT, relief="flat", padx=6, pady=0,
                        font=("Segoe UI",8), cursor="hand2")
            b.pack(side="left", padx=2)
        # per-mip actions for the currently selected level
        tk.Button(self._mipbar, text="Replace Mip…",
                  command=lambda: self._replace_mip_sel(tex),
                  bg=YELLOW, fg=BG, activebackground=BTNACT, relief="flat",
                  padx=6, pady=0, font=("Segoe UI",8,"bold"),
                  cursor="hand2").pack(side="left", padx=(10,2))
        tk.Button(self._mipbar, text="Export Mip…",
                  command=lambda: self._export_mip_sel(tex),
                  bg=BTN, fg=FG, activebackground=BTNACT, relief="flat",
                  padx=6, pady=0, font=("Segoe UI",8),
                  cursor="hand2").pack(side="left", padx=2)
        if (getattr(tex, '_mip_overrides', None) or {}):
            tk.Button(self._mipbar, text="Reset Mips",
                      command=lambda: self._reset_mips_sel(tex),
                      bg=BTN, fg=MAUVE, activebackground=BTNACT, relief="flat",
                      padx=6, pady=0, font=("Segoe UI",8),
                      cursor="hand2").pack(side="left", padx=2)

    def _select_mip(self, tex, level):
        self._mip_level = level
        self._build_mip_selector(tex)
        self._show_preview(tex)

    def _replace_mip_sel(self, tex):
        lvl = getattr(self, '_mip_level', 0)
        dims = self.td.mip_dimensions(tex)
        mw, mh = dims[lvl]
        path = filedialog.askopenfilename(
            title=f"Replace mip {lvl} ({mw}×{mh}) of {tex.display_name}",
            filetypes=[("Images","*.png *.dds *.jpg *.jpeg *.bmp *.tga *.tif *.tiff"),
                       ("All Files","*.*")])
        if not path:
            return
        try:
            self.td.replace_texture_mip(tex, lvl, path)
            self._dirty=True
            self._build_mip_selector(tex)
            self._show_preview(tex)
            self._set_status(
                f"Replaced mip {lvl} ({mw}×{mh}) of '{tex.display_name}'. "
                "Save As to write. Replace the other distant mips too if the "
                "old image still shows at range.")
        except Exception as e:
            messagebox.showerror("Replace Mip", str(e))

    def _export_mip_sel(self, tex):
        lvl = getattr(self, '_mip_level', 0)
        dims = self.td.mip_dimensions(tex)
        mw, mh = dims[lvl]
        path = filedialog.asksaveasfilename(
            title=f"Export mip {lvl} ({mw}×{mh})",
            defaultextension=".dds",
            initialfile=f"{tex.display_name.replace('.dds','')}_mip{lvl}.dds",
            filetypes=[("DDS","*.dds"),("PNG","*.png")])
        if not path:
            return
        try:
            dds=self.td.export_dds_mip(tex, lvl)
            if path.lower().endswith(".png") and PIL_AVAILABLE:
                Image.open(io.BytesIO(dds)).save(path)
            else:
                Path(path).write_bytes(dds)
            self._set_status(f"Exported mip {lvl} to {Path(path).name}")
        except Exception as e:
            messagebox.showerror("Export Mip", str(e))

    def _reset_mips_sel(self, tex):
        self.td.clear_mip_override(tex, None)
        if not (getattr(tex,'_rgba_override',None) and tex._user_painted):
            tex._converted=False
        self._build_mip_selector(tex)
        self._show_preview(tex)
        self._set_status("Cleared per-mip edits for this texture.")

    def _build_statusbar(self):
        bar=tk.Frame(self,bg=PANEL,pady=2); bar.pack(fill="x",side="bottom")
        tk.Label(bar,textvariable=self._status,bg=PANEL,fg=FG,font=("Segoe UI",9),
                 anchor="w",padx=8).pack(fill="x")

    def _bind_keys(self):
        self.bind("<Control-o>",lambda _:self._open())
        self.bind("<Control-p>",lambda _:self._open_rpf_browser())
        self.bind("<Control-i>",lambda _:self._open_img_browser())
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

    def _open_img_browser(self):
        """Open the GTA IV .img Archive Browser as a separate child window.
        Kept entirely separate from the .xtd/.ytd writer code; it only opens
        resources into this editor and writes edited resources back to the .img.
        """
        win = ImgBrowserWindow(self)
        win.focus_set()

    def open_resource_bytes(self, raw, name="resource"):
        """Open a complete RSC resource (bytes) into the editor. Used by the
        archive browsers (RPF / IMG). Returns True on success, False on a
        handled error. Does not alter any writer behaviour."""
        td = TextureDict(self.lzx)
        try:
            td.load_from_bytes(raw, name=name)
        except Exception as ex:
            messagebox.showerror("Open Error", str(ex)); return False
        self.td = td
        self._pending = None
        self._editing = False
        self._img_source = None          # cleared; the caller re-tags if needed
        self.title(f"RAGE Console Texture Editor  -  {name}")
        try:
            self._select_platform(td.platform)
        except Exception:
            pass
        if td.error_msg:
            self._populate([])
            self._show_msg(RED, "Could not open file", td.error_msg)
            try:
                self._plat_lbl.config(text=f"{td.platform} | error")
            except Exception:
                pass
            return False
        self._populate(td.textures)
        try:
            self._plat_lbl.config(
                text=f"{td.platform} | CPU {td.cpu_size} GPU {td.gpu_size}")
        except Exception:
            pass
        self._set_status(f"{name}  |  {len(td.textures)} texture(s)  |  {td.platform}")
        return True

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
        self._mip_level=0
        self._show_info(tex)
        self._build_mip_selector(tex)
        self._show_preview(tex)

    def _show_info(self, tex):
        # Endianness label: both console targets (PS3 RSX and Xbox 360 Xenon)
        # store resources BIG-ENDIAN; PC (RSC7 'RSC7') is little-endian. The
        # 'endian' field on Xbox textures is the per-texture fetch-constant
        # endian swap mode (8in16 / 8in32), shown via GetGPUENDIAN; for PS3 the
        # platform is simply big-endian.
        plat = tex.platform or ""
        if plat == "Xbox 360" or "Xbox 360" in plat:
            endian_str = f"{tex.endian}  (big-endian, {GetGPUENDIAN(tex.endian)})"
        elif plat == "PS3" or "PS3" in plat:
            endian_str = "big-endian (PS3 RSX)"
        elif "PC" in plat:
            endian_str = "little-endian (PC)"
        else:
            endian_str = f"{tex.endian}"
        self._write_info([
            f"Name        : {tex.display_name}",
            f"Dimensions  : {tex.width} x {tex.height}",
            f"Format      : {tex.fmt_name}  ({tex.gpu_fmt or 'n/a'})",
            f"Mip Levels  : {tex.mips}",
            f"Platform    : {tex.platform}",
            f"Tex Offset  : 0x{tex.tex_offset:08X}",
            f"Name Offset : 0x{tex.name_offset:08X}",
            f"Endian      : {endian_str}",
        ])

    def _write_info(self, lines):
        self._info.config(state="normal"); self._info.delete("1.0","end")
        self._info.insert("end","\n".join(lines)); self._info.config(state="disabled")

    def _show_preview(self, tex):
        self._canvas.delete("all"); self._preview_photo=None
        if not PIL_AVAILABLE:
            self._canvas.create_text(10,10,anchor="nw",fill=YELLOW,
                text="Install Pillow for previews.\nExport as DDS to view."); return
        lvl = getattr(self, "_mip_level", 0)
        dims = self.td.mip_dimensions(tex)
        if lvl >= len(dims): lvl = 0
        mw, mh = dims[lvl]
        try:
            dds=self.td.export_dds_mip(tex, lvl)
            img=Image.open(io.BytesIO(dds)).convert("RGBA")
        except Exception as e:
            self._canvas.create_text(10,10,anchor="nw",fill=YELLOW,
                text=f"Preview not available for {tex.fmt_name}.\nExport as DDS to view.\n({e})")
            return
        cw=max(self._canvas.winfo_width(),400); ch=max(self._canvas.winfo_height(),300)
        scale=min(cw/max(mw,1),ch/max(mh,1),1.0)
        dw=max(1,int(mw*scale)); dh=max(1,int(mh*scale))
        img=img.resize((dw,dh),Image.NEAREST)
        # Composite onto a checkerboard so textures with transparency (e.g. white
        # weapon icons on a 0-alpha background) are visible instead of blank.
        bg=self._checker(dw,dh)
        bg.alpha_composite(img)
        photo=ImageTk.PhotoImage(bg); self._preview_photo=photo
        x=(cw-dw)//2; y=(ch-dh)//2
        self._canvas.create_image(x,y,anchor="nw",image=photo)
        miptxt = f" | mip {lvl} of {len(dims)-1}" if len(dims)>1 else ""
        self._canvas.create_text(4,ch-4,anchor="sw",fill="#666",
            text=f"{mw}x{mh} | {tex.fmt_name} | {tex.mips} mip(s){miptxt}",
            font=("Segoe UI",8))

    @staticmethod
    def _checker(w, h, sq=8, c1=(90,90,98,255), c2=(60,60,66,255)):
        """A checkerboard RGBA image to back transparent previews. Built by
        tiling a 2x2-square pattern so it stays fast even at large sizes."""
        tile=Image.new("RGBA",(sq*2,sq*2),c1)
        dark=Image.new("RGBA",(sq,sq),c2)
        tile.paste(dark,(0,0)); tile.paste(dark,(sq,sq))
        bg=Image.new("RGBA",(w,h))
        for y in range(0,h,sq*2):
            for x in range(0,w,sq*2):
                bg.paste(tile,(x,y))
        return bg

    def _generate_mips_sel(self):
        sel=self._tree.selection()
        if not sel or not self.td:
            messagebox.showinfo("Generate Mips","No texture selected."); return
        tex=self.td.textures[int(sel[0])]
        dims=self.td.mip_dimensions(tex)
        maxlev=1; d=max(tex.width,tex.height)
        while d>1: d>>=1; maxlev+=1
        if not messagebox.askyesno("Generate Mips",
            f"Generate a full mip chain for '{tex.display_name}'?\n\n"
            f"{tex.width}x{tex.height} {tex.fmt_name} -> {maxlev} levels "
            f"(down to 1x1).\n\nTakes effect on Save As (full rebuild)."):
            return
        try:
            n=self.td.generate_mips(tex,'auto')
            self._dirty=True
            self._mip_level=0
            self._show_info(tex); self._build_mip_selector(tex); self._show_preview(tex)
            self._set_status(f"Generated {n} mip levels for '{tex.display_name}'. "
                             "Save As to write.")
        except Exception as e:
            messagebox.showerror("Generate Mips", str(e))

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
        plat = self.td.platform
        if plat == "GTA4-Xbox 360" and not getattr(self.lzx, "available_xmem", False):
            if not messagebox.askyesno("Save",
                "GTA IV Xbox 360 repacking needs xcompress.dll (XMem* API), "
                "which isn't loaded.\n"
                f"Status: {self.lzx.status()}\n\nTry anyway?"):
                return
        elif plat == "Xbox 360" and not self.lzx.available_open:
            if not messagebox.askyesno("Save",
                "Xbox 360 repacking needs xcompress_open.dll, which isn't loaded.\n"
                f"Status: {self.lzx.status()}\n\nTry anyway?"):
                return

        # If this resource was opened FROM a .img archive, offer to write the
        # edited resource straight back into that archive (auto write-back), in
        # addition to / instead of saving a loose file.
        img_src = getattr(self, "_img_source", None)
        if img_src and img_src.get("browser") is not None:
            self._save_back_to_img(img_src)
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

    def _save_back_to_img(self, img_src):
        """Repack the open resource and write it back into the source .img."""
        import tempfile
        entry_name = img_src.get("entry_name")
        browser = img_src.get("browser")
        # Repack to a temp file using the exact same proven save path, then read
        # the bytes back and hand them to the archive layer.
        suffix = Path(entry_name).suffix or ".xtd"
        tmp = None
        try:
            fd, tmp = tempfile.mkstemp(suffix=suffix)
            os.close(fd)
            self.td.save(tmp)
            resource_bytes = Path(tmp).read_bytes()
        except Exception as e:
            messagebox.showerror("Save Error",
                                 f"Could not repack the resource:\n{e}")
            return
        finally:
            if tmp and os.path.exists(tmp):
                try:
                    os.remove(tmp)
                except Exception:
                    pass
        try:
            browser.write_back(entry_name, resource_bytes)
        except Exception as e:
            messagebox.showerror("IMG Write-Back",
                                 f"Repacked the resource but could not write it "
                                 f"back into the .img:\n{e}")
            return
        self._dirty = False
        self._set_status(f"Saved {entry_name} back into the .img archive.")
        messagebox.showinfo(
            "Saved to .img",
            f"'{entry_name}' was repacked and written back into\n"
            f"{img_src.get('img_path')}\n\n"
            "The archive on disk is updated and ready for the console.")


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
        if not self.td:
            messagebox.showinfo("Add Texture","Open a texture dictionary first."); return
        imgs=filedialog.askopenfilenames(title="Add texture image(s)",
            filetypes=[("Images","*.png *.dds *.jpg *.jpeg *.bmp *.tga *.tif *.tiff"),
                       ("All Files","*.*")])
        if not imgs: return
        choice = self._ask_format()
        if choice is None: return
        fmt, levels = choice
        added=0; errors=[]
        for p in imgs:
            try:
                name=Path(p).stem
                self.td.add_texture_from_image(name, p, fmt, levels)
                added+=1
            except Exception as e:
                errors.append(f"{Path(p).name}: {e}")
        self._populate(self.td.textures)
        self._dirty=True
        msg=f"Added {added} texture(s). Save As to write the rebuilt dictionary."
        if errors:
            messagebox.showerror("Add Texture", "\n".join(errors))
        self._set_status(msg)

    def _remove_sel(self):
        sel=self._tree.selection()
        if not sel or not self.td:
            messagebox.showinfo("Remove","No texture selected."); return
        texs=[self.td.textures[int(i)] for i in sel]
        names=", ".join(t.display_name for t in texs[:5])
        if len(texs)>5: names+=f" (+{len(texs)-5} more)"
        if len(self.td.textures)-len(texs) < 1:
            messagebox.showwarning("Remove",
                "A texture dictionary must keep at least one texture."); return
        if not messagebox.askyesno("Remove Texture(s)",
            f"Remove {len(texs)} texture(s)?\n\n{names}\n\n"
            "This takes effect when you Save As."):
            return
        self.td.remove_textures(texs)
        self._populate(self.td.textures)
        self._dirty=True
        self._set_status(f"Removed {len(texs)} texture(s). Save As to write the "
                         "rebuilt dictionary.")

    def _OLD_add_texture(self):
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

    # Resource-header validity check, mirroring SparkIV/OpenIV's RageLib exactly:
    #   IsResource  : magic == 0x05435352 (LE) or 0x52534305 (BE-on-disk)
    #   ResourceType: dword at +0x04 (after BE-swap on console), 0x7 = TextureXBOX
    # This is what those tools use to show "Resource [Version: 7]" vs "No". If
    # this prints VALID, the file's header is genuine regardless of whether the
    # IMG TOC entry marks it as a resource (that flag is set on import).
    try:
        m_le = struct.unpack_from('<I', raw, 0)[0]
        rt   = struct.unpack_from('<I', raw, 4)[0]
        if m_le == 0x52534305:          # BE-on-disk console magic -> swap fields
            m_chk = 0x05435352
            rt    = EndianChangeDWORD(rt)
        else:
            m_chk = m_le
        rtype_names = {0x7: "TextureXBOX (.xtd)", 0x8: "Texture (.wtd)",
                       0x6D: "ModelXBOX (.xdr)", 0x6E: "Model (.wdr)",
                       0x70: "ModelFrag (.wft)", 0x6C: "Bounds"}
        is_res = (m_chk == 0x05435352)
        L(f"RageLib IsResource : {'VALID' if is_res else 'NOT A RESOURCE'} "
          f"(magic check)")
        L(f"ResourceType@+0x04 : 0x{rt:X} "
          f"= {rtype_names.get(rt, 'UNKNOWN')}")
        if is_res and rt != 0x7 and is_console and base.endswith(('', '_test')) \
           and path.lower().endswith('.xtd'):
            L("  WARNING: .xtd should have ResourceType 0x7 (TextureXBOX); "
              "SparkIV/OpenIV may not recognize it.")
    except Exception as _e:
        L(f"resource-header check failed: {_e}")

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
# Inlined module: img_archive  (GTA IV .img v3 parser / writer)
# ============================================================================
#!/usr/bin/env python3
"""
img_archive.py -- standalone GTA IV (RAGE) .img version-3 archive reader/writer.

Format (little-endian on PC, the header dwords are plain LE; the resource files
inside keep their own endianness):

  Header (0x10 bytes):
    u32  Identifier   = 0xA94E2A52  ('R*N\xA9')
    i32  Version      = 3
    i32  EntryCount
    i32  TocSize      = EntryCount*0x10 + len(name string blob)
    i16  TocEntrySize = 0x10
    i16  Unknown2

  TOC: EntryCount * 0x10-byte entries, then a flat ASCII name blob (one
  null-terminated string per entry, in order). The header + TOC together are
  padded to a whole number of 0x800 blocks before the first data block.

  TOC entry (0x10 bytes):
    u32  first       -> if (first & 0xC0000000) != 0 it's RSCFlags (resource),
                        else it's the plain file Size in bytes.
    i32  ResourceType (0x7=TextureXBOX/.xtd, 0x6E=Model/.wdr, 0x70=Frag/.wft ...)
    i32  OffsetBlock  (in 0x800 blocks from start of file)
    i16  UsedBlocks   (count of 0x800 blocks the data occupies)
    i16  Flags        -> low 11 bits (0x7FF) = padding byte count in last block

  For a resource entry, Size = UsedBlocks*0x800 - PaddingCount.

GTA IV Xbox 360 AND PC archives encrypt the header+TOC with AES-256-ECB applied
SIXTEEN times (Rockstar's choice; one pass would be equivalent cryptographically
but the data really is enciphered 16x, so it must be deciphered 16x). The data
blocks are stored in the clear. The AES key is NOT a loose encryption_key.bin
(that's GTA V) -- it is a 32-byte blob embedded inside the PC GTAIV.exe,
identified by its SHA-1 hash. Following the OpenIV/SparkIV model this module
never embeds the key: point it at a GTAIV.exe (or pass the 32 raw key bytes) and
it extracts/uses the key. PC and Xbox 360 GTA IV share the same key and scheme.

The header (0x14 bytes) and the TOC (TocSize bytes) are decrypted as TWO
SEPARATE regions, each only over its length rounded down to a 16-byte multiple
(so the header's trailing 4 bytes pass through unencrypted).
"""

import struct
import hashlib
from dataclasses import dataclass, field
from typing import List, Optional

IMG_MAGIC = 0xA94E2A52
IMG_VERSION = 3
BLOCK = 0x800

# The GTA IV AES key inside GTAIV.exe is identified by this SHA-1 (from RageLib).
GTAIV_KEY_SHA1 = "DEA375EF1E6EF2223A1221C2C575C47BF17EFA5E"
# Known key offsets for various GTAIV.exe builds (checked first; full scan after).
GTAIV_KEY_OFFSETS = (
    0xA94204, 0xB607C4, 0xB56BC4, 0xB75C9C, 0xB7AEF4, 0xBE1370, 0xBE6540,
    0xBE7540, 0xC95FD8, 0xC5B33C, 0xC5B73C, 0xB5B65C, 0xB569F4, 0xB76CB4,
    0xB7AEFC, 0xB8813C, 0xB8C38C, 0xBE6510,
)
# EFLC uses the same scheme with a different key in EFLC.exe (different SHA-1).
EFLC_KEY_SHA1 = "53BB1CF67663D5C9B5DDB6924BC2A2C0A24FD0AC"


def extract_gtaiv_key(exe_path):
    """Extract the 32-byte AES key from a PC GTAIV.exe (or EFLC.exe). Tries the
    known build offsets first, then scans every 32-byte boundary, validating by
    SHA-1. Returns the key bytes or raises if not found."""
    with open(exe_path, "rb") as f:
        exe = f.read()

    def at(off):
        if 0 <= off <= len(exe) - 32:
            cand = exe[off:off + 32]
            h = hashlib.sha1(cand).hexdigest().upper()
            if h in (GTAIV_KEY_SHA1, EFLC_KEY_SHA1):
                return cand
        return None

    for off in GTAIV_KEY_OFFSETS:
        k = at(off)
        if k:
            return k
    # Fall back to a full 32-byte-aligned scan.
    for i in range(len(exe) // 32):
        k = at(i * 32)
        if k:
            return k
    raise ValueError(
        f"No GTA IV AES key found in {exe_path} (SHA-1 of any 32-byte block "
        "did not match). Is this a genuine PC GTAIV.exe / EFLC.exe?")


def resolve_key(key=None, exe_path=None):
    """Normalize a caller-supplied key. Accepts raw 32 bytes, or an exe path to
    extract from. Returns 32 key bytes or None."""
    if key is not None:
        if len(key) == 32:
            return bytes(key)
        if len(key) > 32:
            return bytes(key[:32])
        raise ValueError(f"Key must be 32 bytes (got {len(key)}).")
    if exe_path:
        return extract_gtaiv_key(exe_path)
    return None

RESOURCE_TYPE_NAMES = {
    0x01: "Generic", 0x07: "TextureXBOX (.xtd)", 0x08: "Texture (.wtd)",
    0x20: "Bounds", 0x24: "Particles", 0x1B: "Particles2",
    0x6D: "ModelXBOX (.xdr)", 0x6E: "Model (.wdr)", 0x70: "ModelFrag (.wft)",
}


@dataclass
class ImgEntry:
    name: str
    offset_block: int
    used_blocks: int
    is_resource: bool
    rsc_flags: int = 0            # the full dword when is_resource
    resource_type: int = 0
    size: int = 0                 # logical byte size of the file
    padding: int = 0             # bytes of padding in the final block
    entry_flags: int = 0         # the raw 16-bit flags short from the TOC
                                 # (low 11 bits = padding; bit 0x2000 = is RSC)
    _data: Optional[bytes] = field(default=None, repr=False)
    _edited: bool = field(default=False, repr=False)

    @property
    def data_offset(self) -> int:
        return self.offset_block * BLOCK

    @property
    def span_bytes(self) -> int:
        return self.used_blocks * BLOCK

    def type_name(self) -> str:
        if not self.is_resource:
            return "binary"
        return RESOURCE_TYPE_NAMES.get(self.resource_type,
                                       f"Resource 0x{self.resource_type:X}")


def _ceil_blocks(nbytes: int) -> int:
    return (nbytes + BLOCK - 1) // BLOCK


def _rsc05_decode_sizes(flags):
    sysz = (flags & 0x7FF) << (((flags >> 11) & 0xF) + 8)
    gfxz = ((flags >> 15) & 0x7FF) << (((flags >> 26) & 0xF) + 8)
    return sysz, gfxz


def _rsc05_canonical_flags(flags):
    """Re-encode a GTA IV RSC flags dword into the CANONICAL form RageLib and
    the console loader expect: mantissa <= 0x3F with the shift maximized, and
    the 0xC0000000 resource-marker bits set.

    This matters because the console's GPU/page allocator uses the SHIFT field
    to pick page granularity. A flags value that decodes to the right total size
    but uses shift 0 with a large mantissa (e.g. 0x03000020) allocates GPU pages
    at the wrong granularity and HARD-CRASHES the Xbox 360 on texture fetch,
    even though the archive parses fine in OpenIV/SparkIV. Texture-editor output
    produced before the encoder fix can carry such flags; re-canonicalizing them
    here makes injection safe regardless of the source .xtd's flag encoding."""
    sysz, gfxz = _rsc05_decode_sizes(flags)

    def split(size):
        a = size >> 8
        b = 0
        while a > 0x3F:
            if a & 1:
                a += 2
            a >>= 1
            b += 1
        return a & 0x3F, b & 0xF

    sm, ss = split(sysz)
    gm, gs = split(gfxz)
    return (0xC0000000 | (sm & 0x7FF) | ((ss & 0xF) << 11)
            | ((gm & 0x7FF) << 15) | ((gs & 0xF) << 26)) & 0xFFFFFFFF


def rsc_flags_from_xtd(data):
    """Read the canonical IMG-TOC RSC flags from a GTA IV resource file's own
    12-byte header (console big-endian '\\x05CSR' or PC little-endian 'RSC\\x05').
    Returns (rsc_flags, resource_type) or None if not a recognizable resource."""
    if len(data) < 12:
        return None
    magic = data[:4]
    if magic == b"\x05CSR":          # console, big-endian
        rtype = struct.unpack_from(">I", data, 4)[0]
        flags = struct.unpack_from(">I", data, 8)[0]
    elif magic == b"RSC\x05":        # PC, little-endian
        rtype = struct.unpack_from("<I", data, 4)[0]
        flags = struct.unpack_from("<I", data, 8)[0]
    else:
        return None
    return _rsc05_canonical_flags(flags), rtype & 0xFFFFFFFF


def canonicalize_xtd_header(data):
    """Return a copy of a GTA IV resource file with its INTERNAL RSC header
    flags re-canonicalized (correct GPU page-granularity shift), if needed. This
    makes a .xtd self-consistent and safe to load on console even if the texture
    editor that produced it wrote non-canonical flags. No-op for non-resources
    or already-canonical files."""
    if len(data) < 12:
        return data
    magic = data[:4]
    if magic == b"\x05CSR":
        endc = ">I"
    elif magic == b"RSC\x05":
        endc = "<I"
    else:
        return data
    flags = struct.unpack_from(endc, data, 8)[0]
    canon = _rsc05_canonical_flags(flags)
    if canon == flags:
        return data
    out = bytearray(data)
    struct.pack_into(endc, out, 8, canon)
    return bytes(out)


class ImgArchive:
    def __init__(self):
        self.entries: List[ImgEntry] = []
        self.unknown2: int = 0
        self._raw: bytes = b""
        self._toc_blocks: int = 0
        self.encrypted: bool = False
        self.key: Optional[bytes] = None

    # ----------------------------------------------------------------- read
    @classmethod
    def open(cls, path, key: Optional[bytes] = None, exe_path: Optional[str] = None):
        """Open an .img. For encrypted GTA IV archives pass either exe_path (a
        PC GTAIV.exe to extract the key from) or key (32 raw bytes)."""
        with open(path, "rb") as f:
            raw = f.read()
        key = resolve_key(key=key, exe_path=exe_path)
        return cls.from_bytes(raw, key=key)

    @classmethod
    def from_bytes(cls, raw: bytes, key: Optional[bytes] = None):
        self = cls()
        self._raw = raw

        magic = struct.unpack_from("<I", raw, 0)[0]
        self.encrypted = (magic != IMG_MAGIC)

        # ---- header (0x14 bytes; decrypted separately if needed) ------------
        if self.encrypted:
            if key is None:
                raise ValueError(
                    "IMG header is encrypted. Supply the GTA IV key: pass a "
                    "GTAIV.exe (exe_path=) to extract it, or the 32 raw key "
                    "bytes. (GTA IV uses the exe key, not encryption_key.bin.)")
            header = _gta_decrypt(raw[:0x14], key)
        else:
            header = raw[:0x14]

        ident, ver, ecount, tocsize = struct.unpack_from("<IiiI", header, 0)
        if ident != IMG_MAGIC:
            raise ValueError(
                f"Bad IMG magic 0x{ident:08X} after decrypt; wrong key/exe?"
                if self.encrypted else
                f"Not a GTA IV IMG (magic 0x{ident:08X}).")
        if ver != IMG_VERSION:
            raise ValueError(f"Unsupported IMG version {ver} (expected 3).")
        tes, unk = struct.unpack_from("<hh", header, 0x10)
        self.unknown2 = unk
        self.key = key

        # ---- TOC (TocSize bytes immediately after the 0x14 header) ----------
        toc_raw = raw[0x14:0x14 + tocsize]
        toc = _gta_decrypt(toc_raw, key) if self.encrypted else toc_raw

        entries_end = ecount * 0x10
        name_blob = toc[entries_end:tocsize]
        names = name_blob.split(b"\x00")

        self._toc_blocks = _ceil_blocks(0x14 + tocsize)

        for i in range(ecount):
            off = i * 0x10
            first = struct.unpack_from("<I", toc, off)[0]
            rtype = struct.unpack_from("<i", toc, off + 4)[0]
            oblock = struct.unpack_from("<i", toc, off + 8)[0]
            ublocks = struct.unpack_from("<h", toc, off + 12)[0]
            flags = struct.unpack_from("<h", toc, off + 14)[0] & 0xFFFF
            padding = flags & 0x7FF
            is_res = (first & 0xC0000000) != 0
            name = names[i].decode("ascii", "replace") if i < len(names) else f"entry_{i}"
            size = (ublocks * BLOCK - padding) if is_res else first
            self.entries.append(ImgEntry(
                name=name, offset_block=oblock, used_blocks=ublocks,
                is_resource=is_res, rsc_flags=(first if is_res else 0),
                resource_type=rtype, size=size, padding=padding,
                entry_flags=flags))
        return self

    def read_file(self, entry: ImgEntry) -> bytes:
        """Return the raw bytes of an entry's data (resource files include their
        own \\x05CSR header; data blocks are plaintext even in encrypted IMGs)."""
        start = entry.data_offset
        return self._raw[start:start + entry.size]

    # ----------------------------------------------------------------- write
    def to_bytes(self, key: Optional[bytes] = None,
                 exe_path: Optional[str] = None,
                 encrypt: Optional[bool] = None) -> bytes:
        """Rebuild the archive while PRESERVING the original physical layout.

        Real GTA IV archives do not store data in TOC-entry order, and each
        entry's flags short carries a 0x2000 'is-RSC' bit the game loader checks.
        A naive sequential relayout (or dropping that bit) produces a file that
        OpenIV/SparkIV still parse but the console rejects at load (fatal crash
        just after the logos). So:

          * Unedited entries keep their EXACT original offset_block / used_blocks
            and their bytes are copied verbatim from the source archive.
          * Only edited (replace_file) or newly added entries are (re)allocated;
            they're placed at the end of the data region. If an edited file still
            fits in its original block span, it stays in place.
          * The full 16-bit entry flags short (padding | 0x2000 RSC marker) is
            preserved for unchanged entries and synthesized correctly for new
            ones.

        Encryption defaults to the source's state; pass encrypt=True/False to
        force it. Provide the key via exe_path (GTAIV.exe), key (32 bytes), or
        the key captured at open()."""
        key = resolve_key(key=key, exe_path=exe_path) or self.key
        do_encrypt = self.encrypted if encrypt is None else encrypt
        if do_encrypt and key is None:
            raise ValueError(
                "Encrypting a GTA IV archive needs the key. Pass exe_path= "
                "(a PC GTAIV.exe) or key= (32 bytes).")

        ecount = len(self.entries)
        name_blob = b"".join(e.name.encode("ascii", "replace") + b"\x00"
                             for e in self.entries)
        tocsize = ecount * 0x10 + len(name_blob)
        toc_blocks = _ceil_blocks(0x14 + tocsize)

        # ---- decide each entry's final block placement ----------------------
        # An entry is "in place" if it isn't edited AND its original blocks lie
        # entirely after the (possibly grown) TOC region. The TOC region only
        # grows if we added entries/names, which is rare; guard against overlap.
        layout = {}      # id(e) -> (offset_block, used_blocks, padding)
        max_block_used = toc_blocks
        movers = []
        for e in self.entries:
            edited = bool(getattr(e, "_edited", False)) or getattr(e, "_data", None) is not None
            if not edited and e.used_blocks > 0 and e.offset_block >= toc_blocks:
                # untouched: keep exactly where it was
                layout[id(e)] = (e.offset_block, e.used_blocks, e.padding)
                max_block_used = max(max_block_used,
                                     e.offset_block + e.used_blocks)
            elif edited and e.used_blocks > 0 and e.offset_block >= toc_blocks:
                # edited but, if it still fits its original block span, keep it
                # in place so the rest of the archive is untouched.
                payload = self._payload_for(e)
                need = _ceil_blocks(len(payload)) if payload else 0
                if 0 < need <= e.used_blocks:
                    pad = e.used_blocks * BLOCK - len(payload)
                    layout[id(e)] = (e.offset_block, e.used_blocks, pad)
                    max_block_used = max(max_block_used,
                                         e.offset_block + e.used_blocks)
                else:
                    movers.append(e)
            else:
                movers.append(e)

        # place movers (edited / added / would-overlap-TOC) after everything
        next_block = max_block_used
        for e in movers:
            payload = self._payload_for(e)
            ub = _ceil_blocks(len(payload)) if payload else 0
            pad = ub * BLOCK - len(payload)
            layout[id(e)] = (next_block, ub, pad)
            next_block += ub
        total_blocks = next_block

        # ---- assemble the data region ---------------------------------------
        data_region = bytearray((total_blocks - toc_blocks) * BLOCK)
        for e in self.entries:
            ob, ub, pad = layout[id(e)]
            if ub == 0:
                continue
            payload = self._payload_for(e)
            dst = (ob - toc_blocks) * BLOCK
            data_region[dst:dst + len(payload)] = payload
            # remainder of the span stays zero-padded

        # ---- header (0x14 bytes) -------------------------------------------
        header = bytearray()
        header += struct.pack("<IiiI", IMG_MAGIC, IMG_VERSION, ecount, tocsize)
        header += struct.pack("<hh", 0x10, self.unknown2)   # -> exactly 0x14

        # ---- TOC (entries + name blob) -------------------------------------
        toc = bytearray()
        for e in self.entries:
            ob, ub, pad = layout[id(e)]
            first = e.rsc_flags if e.is_resource else (e.size & 0xFFFFFFFF)
            # preserve the original flags short (keeps 0x2000 RSC marker and any
            # other high bits) but refresh the padding count to the real value.
            base_flags = getattr(e, "entry_flags", 0) & ~0x7FF
            if base_flags == 0 and e.is_resource:
                base_flags = 0x2000          # synthesize for new RSC entries
            flags = (base_flags | (pad & 0x7FF)) & 0xFFFF
            toc += struct.pack("<IiihH", first, e.resource_type, ob, ub, flags)
        toc += name_blob

        if do_encrypt:
            header_enc = _gta_encrypt(bytes(header), key)
            toc_enc = _gta_encrypt(bytes(toc), key)
        else:
            header_enc = bytes(header)
            toc_enc = bytes(toc)

        out = bytearray()
        out += header_enc
        out += toc_enc
        out += b"\x00" * (toc_blocks * BLOCK - len(out))   # pad TOC region
        out += data_region
        return bytes(out)

    def _payload_for(self, e: ImgEntry) -> bytes:
        cached = getattr(e, "_data", None)
        if cached is not None:
            return cached
        return self._raw[e.data_offset:e.data_offset + e.size]

    def replace_file(self, name: str, data: bytes,
                     is_resource: Optional[bool] = None,
                     resource_type: Optional[int] = None,
                     rsc_flags: Optional[int] = None):
        e = self.find(name)
        if e is None:
            raise KeyError(name)
        # Make the resource self-consistent: canonicalize its internal RSC
        # header flags so the console allocates GPU pages at the right
        # granularity (prevents the hard-crash-on-spawn from non-canonical .xtd
        # output). No-op for already-correct files and non-resources.
        data = canonicalize_xtd_header(data)
        e._data = data
        e._edited = True
        e.size = len(data)

        # Auto-derive resource identity from the file's own RSC header so the
        # IMG TOC always gets CANONICAL flags (correct GPU page granularity).
        # This is the safety net that prevents a .xtd with non-canonical flags
        # from hard-crashing the console on texture fetch.
        info = rsc_flags_from_xtd(data)
        if info is not None:
            auto_flags, auto_type = info
            e.is_resource = True if is_resource is None else is_resource
            e.resource_type = auto_type if resource_type is None else resource_type
            e.rsc_flags = (rsc_flags if rsc_flags is not None
                           else auto_flags)
            # if a caller passed raw rsc_flags, still canonicalize them
            if rsc_flags is not None:
                e.rsc_flags = _rsc05_canonical_flags(rsc_flags)
        else:
            if is_resource is not None:
                e.is_resource = is_resource
            if resource_type is not None:
                e.resource_type = resource_type
            if rsc_flags is not None:
                e.rsc_flags = _rsc05_canonical_flags(rsc_flags)

        e.entry_flags = (e.entry_flags | 0x2000) if e.is_resource \
            else (e.entry_flags & ~0x2000)
        return e

    def add_file(self, name: str, data: bytes, is_resource: Optional[bool] = None,
                 resource_type: int = 0, rsc_flags: int = 0):
        data = canonicalize_xtd_header(data)
        info = rsc_flags_from_xtd(data)
        if info is not None and (is_resource is None or is_resource):
            rsc_flags, resource_type = info
            is_resource = True
        else:
            is_resource = bool(is_resource)
            if is_resource and rsc_flags:
                rsc_flags = _rsc05_canonical_flags(rsc_flags)
        e = ImgEntry(name=name, offset_block=0, used_blocks=0,
                     is_resource=is_resource, rsc_flags=rsc_flags,
                     resource_type=resource_type, size=len(data),
                     entry_flags=(0x2000 if is_resource else 0))
        e._data = data
        e._edited = True
        self.entries.append(e)
        return e

    def remove_file(self, name: str):
        self.entries = [e for e in self.entries if e.name != name]

    def find(self, name: str) -> Optional[ImgEntry]:
        nl = name.lower()
        for e in self.entries:
            if e.name.lower() == nl:
                return e
        return None


# ----------------------------------------------------------------------------
# GTA IV crypto: AES-256-ECB, no padding, applied SIXTEEN times, over only the
# 16-byte-aligned portion of the region (DataUtil.Decrypt in RageLib). Used for
# both the 0x14-byte header and the TOC, each as its own region. Uses
# pycryptodome if present, otherwise the built-in AES below.
# ----------------------------------------------------------------------------
def _aes_ecb_once(data: bytes, key: bytes, encrypt: bool) -> bytes:
    try:
        from Crypto.Cipher import AES
        c = AES.new(key, AES.MODE_ECB)
        return c.encrypt(data) if encrypt else c.decrypt(data)
    except ImportError:
        return _aes_ecb(key, data, encrypt=encrypt)


def _gta_decrypt(region: bytes, key: bytes, rounds: int = 16) -> bytes:
    n = len(region) & ~0x0F
    if n == 0:
        return bytes(region)
    body = bytes(region[:n])
    for _ in range(rounds):
        body = _aes_ecb_once(body, key, encrypt=False)
    return body + bytes(region[n:])


def _gta_encrypt(region: bytes, key: bytes, rounds: int = 16) -> bytes:
    # Inverse of _gta_decrypt: encrypting 16x is undone by decrypting 16x.
    n = len(region) & ~0x0F
    if n == 0:
        return bytes(region)
    body = bytes(region[:n])
    for _ in range(rounds):
        body = _aes_ecb_once(body, key, encrypt=True)
    return body + bytes(region[n:])


# ----------------------------------------------------------------------------
# Minimal AES-256-ECB fallback (only used when pycryptodome is absent and a key
# is supplied). Correct but not fast; the TOC is small so this is fine.
# ----------------------------------------------------------------------------
_SBOX = []
_INV_SBOX = []
def _init_sbox():
    p = q = 1
    sbox = [0] * 256
    while True:
        p = p ^ ((p << 1) & 0xFF) ^ (0x1B if p & 0x80 else 0)
        q ^= q << 1; q ^= q << 2; q ^= q << 4; q &= 0xFF
        if q & 0x80: q ^= 0x09
        xformed = q ^ ((q << 1) | (q >> 7)) ^ ((q << 2) | (q >> 6)) ^ \
                  ((q << 3) | (q >> 5)) ^ ((q << 4) | (q >> 4))
        sbox[p] = (xformed ^ 0x63) & 0xFF
        if p == 1:
            break
    sbox[0] = 0x63
    inv = [0] * 256
    for i, v in enumerate(sbox):
        inv[v] = i
    return sbox, inv

def _xtime(a):
    return ((a << 1) ^ 0x1B) & 0xFF if a & 0x80 else (a << 1)

def _mul(a, b):
    r = 0
    for _ in range(8):
        if b & 1:
            r ^= a
        b >>= 1
        a = _xtime(a)
    return r & 0xFF

def _key_expansion(key):
    global _SBOX, _INV_SBOX
    if not _SBOX:
        _SBOX, _INV_SBOX = _init_sbox()
    Nk = len(key) // 4
    Nr = {4: 10, 6: 12, 8: 14}[Nk]
    w = [list(key[4 * i:4 * i + 4]) for i in range(Nk)]
    rcon = 1
    for i in range(Nk, 4 * (Nr + 1)):
        temp = list(w[i - 1])
        if i % Nk == 0:
            temp = temp[1:] + temp[:1]
            temp = [_SBOX[b] for b in temp]
            temp[0] ^= rcon
            rcon = _xtime(rcon)
        elif Nk > 6 and i % Nk == 4:
            temp = [_SBOX[b] for b in temp]
        w.append([a ^ b for a, b in zip(w[i - Nk], temp)])
    return w, Nr

def _add_round_key(s, w, rnd):
    for c in range(4):
        for r in range(4):
            s[r][c] ^= w[rnd * 4 + c][r]

def _inv_sub_bytes(s):
    for r in range(4):
        for c in range(4):
            s[r][c] = _INV_SBOX[s[r][c]]

def _sub_bytes(s):
    for r in range(4):
        for c in range(4):
            s[r][c] = _SBOX[s[r][c]]

def _inv_shift_rows(s):
    for r in range(1, 4):
        s[r] = s[r][-r:] + s[r][:-r]

def _shift_rows(s):
    for r in range(1, 4):
        s[r] = s[r][r:] + s[r][:r]

def _inv_mix_columns(s):
    for c in range(4):
        a = [s[r][c] for r in range(4)]
        s[0][c] = _mul(a[0], 14) ^ _mul(a[1], 11) ^ _mul(a[2], 13) ^ _mul(a[3], 9)
        s[1][c] = _mul(a[0], 9) ^ _mul(a[1], 14) ^ _mul(a[2], 11) ^ _mul(a[3], 13)
        s[2][c] = _mul(a[0], 13) ^ _mul(a[1], 9) ^ _mul(a[2], 14) ^ _mul(a[3], 11)
        s[3][c] = _mul(a[0], 11) ^ _mul(a[1], 13) ^ _mul(a[2], 9) ^ _mul(a[3], 14)

def _mix_columns(s):
    for c in range(4):
        a = [s[r][c] for r in range(4)]
        s[0][c] = _mul(a[0], 2) ^ _mul(a[1], 3) ^ a[2] ^ a[3]
        s[1][c] = a[0] ^ _mul(a[1], 2) ^ _mul(a[2], 3) ^ a[3]
        s[2][c] = a[0] ^ a[1] ^ _mul(a[2], 2) ^ _mul(a[3], 3)
        s[3][c] = _mul(a[0], 3) ^ a[1] ^ a[2] ^ _mul(a[3], 2)

def _block_to_state(block):
    return [[block[r + 4 * c] for c in range(4)] for r in range(4)]

def _state_to_block(s):
    return bytes(s[r][c] for c in range(4) for r in range(4))

def _aes_ecb(key, data, encrypt):
    w, Nr = _key_expansion(key)
    out = bytearray()
    for i in range(0, len(data), 16):
        s = _block_to_state(data[i:i + 16])
        if encrypt:
            _add_round_key(s, w, 0)
            for rnd in range(1, Nr):
                _sub_bytes(s); _shift_rows(s); _mix_columns(s)
                _add_round_key(s, w, rnd)
            _sub_bytes(s); _shift_rows(s); _add_round_key(s, w, Nr)
        else:
            _add_round_key(s, w, Nr)
            for rnd in range(Nr - 1, 0, -1):
                _inv_shift_rows(s); _inv_sub_bytes(s)
                _add_round_key(s, w, rnd); _inv_mix_columns(s)
            _inv_shift_rows(s); _inv_sub_bytes(s); _add_round_key(s, w, 0)
        out += _state_to_block(s)
    return bytes(out)


# ============================================================================
# Inlined module: img_browser_integrated  (.img browser window + write-back)
# ============================================================================
# Catppuccin Mocha palette (matches the editor).
MUTED = "#9399b2"
SURFACE1 = "#45475a"
_IMG_TEXTURE_EXTS = {".ytd", ".xtd", ".ctd", ".wtd"}


def _img_fmt_size(n):
    for unit in ("B", "KB", "MB", "GB"):
        if n < 1024:
            return f"{n:.0f} {unit}" if unit == "B" else f"{n:.1f} {unit}"
        n /= 1024
    return f"{n:.1f} TB"


class ImgBrowserWindow(tk.Toplevel):
    """Standalone .img browser; bridges entries into the parent texture editor."""

    def __init__(self, parent_app):
        super().__init__(parent_app)
        self.app = parent_app
        self.arc = None                 # ImgArchive
        self.key = None                 # 32 raw key bytes
        self.img_path = None            # path of the open .img on disk
        self._exe_path = None           # remembered GTAIV.exe for the key

        self.title("GTA IV .img Archive Browser")
        self.configure(bg=BG)
        self.geometry("900x600")
        self.minsize(640, 420)

        self._build_toolbar()
        self._build_table()
        self._build_statusbar()

        # If the editor already knows a GTAIV.exe (e.g. from a prior session),
        # reuse it so the user isn't prompted again.
        self._exe_path = getattr(parent_app, "_gtaiv_exe_path", None)

        self.protocol("WM_DELETE_WINDOW", self._on_close)

    # ---------------------------------------------------------------- UI ----
    def _btn(self, parent, text, cmd, color=SURFACE1):
        b = tk.Button(parent, text=text, command=cmd, bg=color, fg=FG,
                      activebackground=ACCENT, activeforeground=BG,
                      relief="flat", bd=0, padx=10, pady=5,
                      font=("Segoe UI", 9))
        b.pack(side="left", padx=3)
        return b

    def _build_toolbar(self):
        bar = tk.Frame(self, bg=PANEL); bar.pack(fill="x", padx=0, pady=0)
        inner = tk.Frame(bar, bg=PANEL); inner.pack(fill="x", padx=8, pady=6)
        self._btn(inner, "Open .img", self._open_img, ACCENT)
        self._btn(inner, "Open in Editor", self._open_in_editor)
        self._btn(inner, "Extract", self._extract_sel)
        self._btn(inner, "Import/Replace", self._import_replace)
        self._btn(inner, "Save .img", self._save_img, GREEN)
        self._path_lbl = tk.Label(inner, text="(no archive open)", bg=PANEL,
                                  fg=MUTED, font=("Segoe UI", 9))
        self._path_lbl.pack(side="right")

    def _build_table(self):
        wrap = tk.Frame(self, bg=BG); wrap.pack(fill="both", expand=True,
                                               padx=8, pady=(4, 4))
        cols = ("name", "type", "size", "blocks", "offset")
        style = ttk.Style(self)
        try:
            style.theme_use("clam")
        except Exception:
            pass
        style.configure("Img.Treeview", background=PANEL, fieldbackground=PANEL,
                        foreground=FG, rowheight=22, borderwidth=0)
        style.configure("Img.Treeview.Heading", background=ENTRY, foreground=ACCENT,
                        relief="flat", font=("Segoe UI", 9, "bold"))
        style.map("Img.Treeview", background=[("selected", ACCENT)],
                  foreground=[("selected", BG)])
        self.tree = ttk.Treeview(wrap, columns=cols, show="headings",
                                 style="Img.Treeview", selectmode="extended")
        headers = {"name": ("Name", 360), "type": ("Type", 130),
                   "size": ("Size", 90), "blocks": ("Blocks", 70),
                   "offset": ("Offset", 100)}
        for c, (lbl, w) in headers.items():
            self.tree.heading(c, text=lbl, command=lambda cc=c: self._sort_by(cc))
            self.tree.column(c, width=w, anchor=("w" if c == "name" else "center"))
        vs = ttk.Scrollbar(wrap, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=vs.set)
        self.tree.pack(side="left", fill="both", expand=True)
        vs.pack(side="right", fill="y")
        self.tree.bind("<Double-1>", lambda _e: self._open_in_editor())
        self._sort_state = {}

    def _build_statusbar(self):
        sb = tk.Frame(self, bg=PANEL); sb.pack(fill="x")
        self._status = tk.Label(sb, text="Open a GTA IV .img to begin.",
                               bg=PANEL, fg=MUTED, anchor="w",
                               font=("Segoe UI", 9))
        self._status.pack(fill="x", padx=8, pady=3)

    def _setstatus(self, msg):
        self._status.config(text=msg); self.update_idletasks()

    # ------------------------------------------------------------- key ------
    def _ensure_key(self):
        """Return a usable key, prompting for GTAIV.exe if needed."""
        if self.key is not None:
            return self.key
        # try a remembered exe first
        if self._exe_path and os.path.isfile(self._exe_path):
            try:
                self.key = extract_gtaiv_key(self._exe_path)
                return self.key
            except Exception:
                pass
        if not messagebox.askyesno(
                "GTA IV key needed",
                "GTA IV .img archives are encrypted with a key stored inside "
                "GTAIV.exe (not encryption_key.bin).\n\n"
                "Select your GTAIV.exe so the key can be extracted?",
                parent=self):
            return None
        p = filedialog.askopenfilename(
            title="Select GTAIV.exe",
            filetypes=[("GTAIV executable", "*.exe"), ("All files", "*.*")],
            parent=self)
        if not p:
            return None
        try:
            self.key = extract_gtaiv_key(p)
            self._exe_path = p
            # remember on the app for future sessions / the RPF side
            try:
                self.app._gtaiv_exe_path = p
            except Exception:
                pass
            return self.key
        except Exception as ex:
            messagebox.showerror("Key extraction failed",
                                 f"Could not extract the key from that .exe:\n{ex}",
                                 parent=self)
            return None

    # ------------------------------------------------------------ open ------
    def _open_img(self):
        p = filedialog.askopenfilename(
            title="Open GTA IV .img archive",
            filetypes=[("IMG archive", "*.img"), ("All files", "*.*")],
            parent=self)
        if not p:
            return
        key = self._ensure_key()
        # key may be None for an unencrypted archive; ImgArchive handles that.
        self._setstatus(f"Opening {Path(p).name}…")
        try:
            self.arc = ImgArchive.open(p, key=key)
        except Exception as ex:
            messagebox.showerror("Open IMG", str(ex), parent=self)
            self._setstatus("Open failed."); return
        self.img_path = p
        self.key = getattr(self.arc, "key", key)
        self._path_lbl.config(text=Path(p).name)
        self._refresh()
        self._setstatus(f"Opened {Path(p).name}  |  {len(self.arc.entries)} entries")

    def _refresh(self):
        for r in self.tree.get_children():
            self.tree.delete(r)
        if not self.arc:
            return
        for i, e in enumerate(self.arc.entries):
            self.tree.insert("", "end", iid=str(i),
                             values=(e.name, e.type_name(), _img_fmt_size(e.size),
                                     e.used_blocks, f"0x{e.data_offset:X}"))

    def _sort_by(self, col):
        if not self.arc:
            return
        rev = self._sort_state.get(col, False)
        idx = {"name": lambda e: e.name.lower(),
               "type": lambda e: e.type_name(),
               "size": lambda e: e.size,
               "blocks": lambda e: e.used_blocks,
               "offset": lambda e: e.data_offset}[col]
        order = sorted(range(len(self.arc.entries)),
                       key=lambda i: idx(self.arc.entries[i]), reverse=rev)
        self._sort_state[col] = not rev
        # rebuild in that order but keep iid->entry mapping by storing the index
        for r in self.tree.get_children():
            self.tree.delete(r)
        for i in order:
            e = self.arc.entries[i]
            self.tree.insert("", "end", iid=str(i),
                             values=(e.name, e.type_name(), _img_fmt_size(e.size),
                                     e.used_blocks, f"0x{e.data_offset:X}"))

    def _selected(self):
        sel = self.tree.selection()
        out = []
        for iid in sel:
            try:
                out.append(self.arc.entries[int(iid)])
            except Exception:
                pass
        return out

    # -------------------------------------------------- open in editor ------
    def _open_in_editor(self):
        if not self.arc:
            self._setstatus("Open a .img first."); return
        ents = self._selected()
        if not ents:
            self._setstatus("Select a texture entry first."); return
        e = ents[0]
        ext = Path(e.name).suffix.lower()
        if ext not in _IMG_TEXTURE_EXTS:
            messagebox.showinfo("Open in Editor",
                f"'{e.name}' is not a texture resource.\n\n"
                "Only .ytd / .xtd / .ctd / .wtd entries open in the editor.\n"
                "Use Extract for other files.", parent=self)
            return
        try:
            raw = self.arc.read_file(e)      # the resource bytes (with RSC header)
        except Exception as ex:
            messagebox.showerror("Read error", str(ex), parent=self)
            return

        app = self.app
        # Hand the bytes to the editor the same way an on-disk open would, then
        # tag the App so its Save path writes back into THIS archive/entry.
        try:
            ok = app.open_resource_bytes(raw, name=e.name)
        except Exception as ex:
            messagebox.showerror("Open in Editor",
                                 f"Could not open '{e.name}':\n{ex}", parent=self)
            return
        if ok is False:
            return
        # attach the write-back source
        app._img_source = {
            "browser": self,
            "archive": self.arc,
            "img_path": self.img_path,
            "entry_name": e.name,
            "key": self.key,
        }
        app.lift(); app.focus_set()
        self._setstatus(f"Opened {e.name} in the editor. Save writes back to "
                        f"{Path(self.img_path).name}.")

    # ------------------------------------------------ write-back path -------
    def write_back(self, entry_name, resource_bytes):
        """Replace an entry's bytes and re-save the .img in place. Called by the
        editor's Save when the open resource came from this archive."""
        if not self.arc:
            raise RuntimeError("No .img archive is open.")
        self.arc.replace_file(entry_name, resource_bytes)
        blob = self.arc.to_bytes(key=self.key)
        with open(self.img_path, "wb") as f:
            f.write(blob)
        # re-open from the freshly written bytes so offsets/TOC are in sync
        try:
            self.arc = ImgArchive.from_bytes(blob, key=self.key)
            self._refresh()
        except Exception:
            pass
        self._setstatus(f"Wrote {entry_name} back into "
                        f"{Path(self.img_path).name}.")

    # --------------------------------------------------- extract/import -----
    def _extract_sel(self):
        if not self.arc:
            return
        ents = self._selected()
        if not ents:
            self._setstatus("Select file(s) to extract."); return
        if len(ents) == 1:
            e = ents[0]
            out = filedialog.asksaveasfilename(
                title=f"Extract {e.name}", initialfile=e.name,
                defaultextension=Path(e.name).suffix, parent=self)
            if not out:
                return
            try:
                with open(out, "wb") as f:
                    f.write(self.arc.read_file(e))
                self._setstatus(f"Extracted {e.name}")
            except Exception as ex:
                messagebox.showerror("Extract", str(ex), parent=self)
        else:
            d = filedialog.askdirectory(title="Extract selected files to…",
                                        parent=self)
            if not d:
                return
            n = 0
            for e in ents:
                try:
                    with open(os.path.join(d, e.name), "wb") as f:
                        f.write(self.arc.read_file(e))
                    n += 1
                except Exception:
                    pass
            self._setstatus(f"Extracted {n} file(s) to {d}")

    def _import_replace(self):
        if not self.arc:
            return
        ents = self._selected()
        if not ents:
            self._setstatus("Select the entry to replace first."); return
        e = ents[0]
        p = filedialog.askopenfilename(
            title=f"Replace {e.name} with…",
            filetypes=[("Resource / file", "*.*")], parent=self)
        if not p:
            return
        try:
            data = Path(p).read_bytes()
            self.arc.replace_file(e.name, data)
            self._refresh()
            self._setstatus(f"Replaced {e.name} (unsaved — use Save .img).")
        except Exception as ex:
            messagebox.showerror("Replace", str(ex), parent=self)

    def _save_img(self):
        if not self.arc:
            return
        out = filedialog.asksaveasfilename(
            title="Save .img", initialfile=Path(self.img_path).name
            if self.img_path else "archive.img",
            defaultextension=".img", parent=self)
        if not out:
            return
        try:
            blob = self.arc.to_bytes(key=self.key)
            with open(out, "wb") as f:
                f.write(blob)
            self.img_path = out
            self._path_lbl.config(text=Path(out).name)
            self._setstatus(f"Saved {Path(out).name} ({_img_fmt_size(len(blob))})")
        except Exception as ex:
            messagebox.showerror("Save .img", str(ex), parent=self)

    def _on_close(self):
        # detach any write-back source pointing at us
        src = getattr(self.app, "_img_source", None)
        if src and src.get("browser") is self:
            self.app._img_source = None
        self.destroy()

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

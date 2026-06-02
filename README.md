[README.md](https://github.com/user-attachments/files/28528782/README.1.md)
# RAGE Console Texture Editor — Python Port

A Python/Tkinter port of [indirivacua/RAGE-Console-Texture-Editor](https://github.com/indirivacua/RAGE-Console-Texture-Editor)
(originally by Dageron). Opens GTA V (and GTA IV / RDR / MC:LA / MP3) console
texture dictionaries: **view, export, replace, and repack** textures.

## Quick start

1. Keep these four files together in one folder (all included):
   ```
   rage_texture_editor.py
   xcompress.dll
   xcompress_cpp.dll
   xcompress_open.dll
   ```
2. Run it:
   ```
   python rage_texture_editor.py
   ```
   On first launch it **auto-installs Pillow** (previews + image import) if
   it's missing — no manual `pip install` needed.

## Platform support

| Platform | Extension | Container | Works where |
|----------|-----------|-----------|-------------|
| PC | `.ytd` | RSC7, Little-Endian, zlib | Anywhere |
| PS3 | `.ctd` / `.xtd` | 7CSR, Big-Endian, zlib | Anywhere |
| Xbox 360 | `.xtd` | 7CSR, Big-Endian, **LZX** | **32-bit Windows** (needs DLLs) |

Platform is auto-detected from the magic bytes. The Platform tab only
disambiguates PS3 vs Xbox 360 for `7CSR` files.

## Xbox 360: the 32-bit requirement

Xbox 360 LZX (de)compression is not reimplemented — like the original tool it
calls the bundled native DLLs via ctypes (`xcompress.dll`,
`xcompress_cpp.dll` for GTA IV/RDR, `xcompress_open.dll` for GTA V). These are
**32-bit** Windows libraries (verified), so opening/saving Xbox 360 `.xtd`
files needs **32-bit Python on Windows**. Run 64-bit Python and the tool will
detect the mismatch and tell you in `Help → LZX / DLL Status`. PC and PS3
files use zlib and work on any Python/OS.

Get 32-bit Python from python.org → "Windows installer (32-bit)".

## Features

- Open / browse textures with live preview.
- Export DDS — single texture or *Export All* to a folder.
- **Replace Texture** (Ctrl+R): pick any PNG/JPG/DDS/BMP/TGA/TIFF; it's resized
  to the texture's dimensions, re-encoded to its GPU format, Xenon-tiled and
  endian-swapped as needed, and written back into the archive in memory.
- **Save As / repack** (Ctrl+S): rebuilds the resource — PC/PS3 via zlib,
  Xbox 360 via xCompress. The 16-byte RSC7 header is preserved.

## What was verified

Built from the actual Pascal sources. Verified here (no DLL needed): RSC7 size
formula, Xenon tiling and its exact inverse (retile→untile round-trips
byte-for-byte), D3DBaseTexture decode, GPU format table, DDS build/parse
round-trip, DXT1/DXT5 encoders, replace→buffer splice, and PC/PS3 zlib repack.
The `xDecompress`/`xCompress` ctypes signatures were confirmed by
disassembling the supplied DLLs. The live Xbox 360 LZX path needs 32-bit
Windows to exercise.

## Notes / limitations

- Replace keeps original dimensions + format (a different-size image is resized
  to fit), so offsets and the header stay valid.
- The DXT encoder is a correct, dependency-free range-fit compressor.
- PS3 reads the real per-texture format (DXT1/DXT2_3/DXT4_5/DXT5A/8/8888) from
  the struct and repacks with raw DEFLATE so OpenIV accepts the rebuilt .ctd.
- Mip 0 is exported/replaced; per-mip editing isn't wired in yet.
- **Back up your files before saving.**

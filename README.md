[README.md](https://github.com/user-attachments/files/28923994/README.md)
# RAGE Console Texture Editor — Python Port

<img width="1920" height="1080" alt="Screenshot (1080)" src="https://github.com/user-attachments/assets/5df6e097-2952-4718-8444-3c5437ba8d35" />

<img width="1920" height="1080" alt="Screenshot (1077)" src="https://github.com/user-attachments/assets/f7507079-cc64-411c-bb36-ab3c41ab4a14" />


A Python/Tkinter tool for reading, viewing, editing, converting, and repacking
**RAGE engine texture dictionaries** across PC, PlayStation 3, and Xbox 360.

It is a port and extension of the Pascal/Delphi tools by **Dageron**
(`GTA-V-Console-Texture-Editor`) and **indirivacua**
(`RAGE-Console-Texture-Editor`), rebuilt in Python with a number of new
capabilities — most notably **working colour conversion of console texture
formats** and a built-in **RPF archive browser**.

> Primary target is **GTA V** (and **GTA IV**) texture dictionaries, but the
> RSC7/RSC5 structures are shared across several RAGE titles.

---

## Supported files

| Platform   | Extension     | Magic  | Endian | Compression                  |
|------------|---------------|--------|--------|------------------------------|
| PC         | `.ytd`        | `RSC7` | Little | zlib (raw DEFLATE)           |
| PS3        | `.ctd` / `.xtd` | `7CSR` | Big    | zlib                         |
| Xbox 360   | `.xtd`        | `7CSR` | Big    | LZX / XMem (via xcompress)   |

Both **RSC7** (GTA V) and **RSC5** (GTA IV) resource versions are read.

---

## Features

### Viewing
- Open `.ytd` / `.ctd` / `.xtd` directly, or browse them inside RPF archives.
- Preview every texture, decoded from its real GPU format.
- **Per-mip viewing** — for multi-mip textures, a level selector shows each mip
  at its own resolution (verified against real multi-mip vehicle textures).
- Texture info panel: dimensions, format, mip count, platform, offsets, endian.

### Editing
- **Replace** a texture with any image (PNG/DDS/JPG/BMP/TGA/TIFF); it is resized
  and re-encoded to the texture's existing format and written back.
- **Add** new textures from images (all platforms).
- **Remove** textures (multi-select supported).
- **Convert format** — change a texture's compression format, e.g.
  `DXT5A → DXT4_5` to make a single-channel mask into a colour-capable texture.
- **Generate Mips** — build a full mip chain (down to 1×1) for a texture.
- Save/repack back to a game-ready file, reproducing the original compression.

### RPF archive browser
- Open RPF7 archives (Xbox 360 / PS3), with AES decryption when you supply your
  own `encryption_key.bin` (the same key file OpenIV uses — see *Keys* below).
- Folder-scoped listing, nested-RPF navigation with breadcrumbs, background-
  threaded opens so the UI never freezes.
- **Find Texture in RPFs…** — scan a folder of archives (and one level of nested
  DLC mounts) for a texture name. This finds **DLC/update archives that override
  your edits**, a common reason in-game changes don't appear.
- Extract individual files, or decompress an entire archive to a folder.
- Open any texture dictionary found in an archive straight into the editor.

### Format support
DXT1, DXT2_3 (DXT3), DXT4_5 (DXT5), DXT5A, DXN, and 8_8_8_8, with correct
encoders for each (DXT3 explicit alpha, DXT5A/BC4 single channel, etc.).

---

## Notes on the hard-won details

This tool was built by decoding **real game files byte-by-byte**, not from
documentation. A few of the things that matter:

- **`dword_11` (Xenon tiling/format register).** Each Xbox 360 texture's fetch
  constant has a register whose value depends on **both format and dimensions**.
  Getting it wrong makes a texture render monochrome or mis-tiled. The editor
  **preserves each texture's original value** and only recomputes it for a
  texture whose format you actually convert. This is what makes converted
  radio-wheel icons display in colour.
- **RAGE virtual page allocator.** The graphics block is a page hierarchy
  (tiers of `base×16 … base÷16`). When a conversion or rebuild changes data
  sizes, the editor re-lays the whole block and regenerates a self-consistent
  page flag, so the game's loader/BlockMap resolves it.
- **Dictionary vtable.** Xbox 360 `grcTextureDictionary` uses vtable
  `0x88988100`; using the wrong value makes the game reject the file. (This was
  the CTD→XTD "not recognized" fix.)
- **Mip count register (`dword_12`).** Encoded so the reader decodes the correct
  level count for any chain length (not just ≤4).

---

## Requirements

- **Python 3.8+**
- **Pillow** (`pip install pillow`) — for image import/preview/encoding. The app
  attempts to auto-install it on launch.
- **PyCryptodome** (`pip install pycryptodome`) — only needed for AES-encrypted
  RPF archives.
- **Xbox 360 LZX** needs the native Microsoft DLLs (see below).

### Xbox 360 LZX / XMem (Windows only)

Xbox 360 resources use Microsoft's proprietary LZX codec. Like the original
Pascal tool, this port does **not** reimplement it — it calls the native DLLs
through `ctypes`:

```
xcompress.dll        (XMem* functions)
xcompress_cpp.dll    (LZXinit / LZXdecompress — GTA IV / RDR, Codec 0)
xcompress_open.dll   (xDecompress / xCompress — GTA V, Codec 1)
```

Place these three DLLs in the same folder as the script. They are **32-bit**
native Windows libraries, so the Xbox 360 path requires a **32-bit Python
interpreter on Windows**. The PC and PS3 paths (zlib) work on any platform/any
Python.

---

## Keys (encrypted RPF archives)

Following the OpenIV model, **this tool does not ship encryption keys.** To open
encrypted RPF archives, supply your own `encryption_key.bin` (the same key file
OpenIV accepts) in the working folder; the browser auto-detects it. Console
RPF7 archives use single-pass AES-256-ECB; PC "NG" archives use the 16-round
scheme — the tool auto-detects which.

---

## Usage

```bash
# 32-bit Python on Windows for full Xbox 360 support:
python rage_texture_editor.py
```

1. **File → Open** a `.ytd` / `.ctd` / `.xtd`, or **open the RPF browser** to
   pull one out of an archive.
2. Select a texture to preview it. For multi-mip textures, use the mip selector.
3. **Replace / Add / Remove / Convert Format / Generate Mips** as needed.
4. **Save As** to write a repacked, game-ready file.

### Converting a single-channel icon to colour (e.g. radio-wheel icons)
1. Select the `DXT5A` texture.
2. **Convert Format → DXT4_5 (colour)**. The mask is preserved as a white icon
   on a transparent background.
3. **Replace** it with your own colour image.
4. **Save As**, then test in-game.

> The GTA V **radio wheel** specifically requires the **DXT2_3 / DXT4_5** format
> for colour (its stock DLC icon is DXT2_3). Convert the stock `DXT5A` icons to
> a colour format to unlock colour there.

---

## Verification status (honest)

Development followed a **real-sample verification loop**: edits are checked at
the byte level against real game files, and many were confirmed **in-game on
real hardware**.

**Confirmed working in-game (Xbox 360):**
- PC `.ytd` RSC7 writing (verified in OpenIV).
- Reading/exporting textures across PC / PS3 / Xbox 360.
- **Colour radio-wheel icons** via `DXT5A → DXT4_5/DXT2_3` conversion.
- Multi-mip texture **viewing** (verified against real vehicle textures).

**Structurally verified (byte-correct vs real files; in-game test recommended):**
- Add / Remove textures (rebuild preserves all formats, mip counts, and the
  per-texture `dword_11` registers).
- Mip **generation** (mip-count register round-trips for any chain length).
- CTD→XTD conversion (dictionary vtable + page layout corrected).

**Experimental (not yet hardware-verified):**
- **PS3** format conversion and `.ctd` rebuild — implemented and structurally
  consistent, but RSX GPU behaviour has not been confirmed in-game. PS3 dumps
  from real hardware are welcome to lock this down.

The Xbox 360 LZX/XMem paths require the native DLLs and a 32-bit Windows Python;
they cannot run in non-Windows environments.

---

## Credits & references

- **Dageron** — original GTA V Console Texture Editor (Pascal).
- **indirivacua** — RAGE-Console-Texture-Editor.
- Cross-referenced against **OpenIV**, **CodeWalker** (dexyfex), and
  **libertyv** (koolkdev) when reverse-engineering the RSC7/RPF7 structures.

This tool never ships encryption keys or copyrighted game data; users supply
their own, exactly as with OpenIV.

---

## License

See the repository for license details. The bundled `xcompress*.dll` files are
Microsoft components and are **not** covered by this project's license; obtain
them yourself.

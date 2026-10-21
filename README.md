# Tripo3D Model Downloader

A Tampermonkey/Violentmonkey userscript that captures the 3D assets loaded by
`studio.tripo3d.ai` and converts the captured GLB to STL / OBJ / FBX / 3MF / GLTF
locally in your browser, without spending Tripo credits.

## What it does

- Runs on `https://studio.tripo3d.ai/*` at `document-start`.
- Hooks `window.fetch` and `XMLHttpRequest` to capture asset URLs as the studio
  loads them, and parses the JSON bodies of Tripo API responses.
- Falls back to scanning the page state (Nuxt/Vue state), the DOM, and — on an
  explicit deep scan — window properties, for URLs the network hook missed.
- Recognises `glb`, `gltf`, `stl`, `obj`, `fbx`, `3mf`, `usd`/`usda`/`usdc`/`usdz`,
  `ply`, `dae` and `zip` assets, plus URLs on known Tripo/CDN hosts that carry no
  recognisable extension.
- Injects a "⬇ DL Model" button and an in-page dialog with:
  - **⬇ Download** — save the captured model,
  - **🎨 PBR Model** — save the PBR variant,
  - **📋** — copy the source URL,
  - a dropdown of every captured URL,
  - **🔄 Refresh Scan** — run a deep search again,
  - **📄 Copy All URL** — copy the whole capture history.
- Converts the captured GLB in the browser to STL, OBJ, FBX, 3MF or GLTF. The
  conversion runs locally, so nothing is uploaded and no credits are spent.
- Validates downloads with magic-byte checks (for example the glTF binary
  header) and warns you when a saved file does not look like what it should.

## Features

- Multi-format capture, not just GLB: STL, OBJ, FBX, 3MF, USD/USDZ, PLY, DAE and
  ZIP assets are detected and listed with their own MIME type and filename.
- Free client-side conversion (three.js + MeshoptDecoder), including a vendored
  3MF exporter that builds the archive synchronously with `fflate`.
- Resource monitoring through the Performance Observer API, and a background
  poller that re-scans when the page route changes (the studio is a SPA).
- Cycle-safe URL extraction: recursive scanning uses a `WeakSet` guard and a
  type filter so Vue reactive proxies and DOM nodes cannot cause a stack
  overflow or freeze the page.
- Downloads use `arraybuffer` instead of `blob` responses, because large binary
  blobs get truncated on some userscript managers.

## Requirements

- A browser with **Tampermonkey** or **Violentmonkey**.
- **Node.js** and npm only if you want to rebuild the userscript from source.

## Install

Install the pre-built userscript:

1. Download [`dist/tripo3d-model-downloader.user.js`](dist/tripo3d-model-downloader.user.js).
2. Open the file in your browser; the userscript manager picks it up and asks
   you to confirm the installation.

Or build it yourself:

```bash
npm install
npm run build
```

`npm run build` runs `node build.mjs`, which bundles `src/converter.js` with
esbuild into `dist/tripo-converter.js` and inlines that bundle into
`src/userscript.template.js` at the `/*__CONVERTER_BUNDLE__*/` marker, writing
the final `dist/tripo3d-model-downloader.user.js`.

Other scripts:

- `npm run bundle` — only the esbuild step, output in `dist/tripo-converter.js`.
- `node test3mf.mjs <file.glb>` — developer check that exports a GLB to 3MF and
  prints the resulting ZIP entries.

## Usage

1. Open <https://studio.tripo3d.ai> and load a model.
2. Click the **⬇ DL Model** button that the script injects into the page.
3. In the dialog, use **⬇ Download** to save the model as it was captured, or
   **🎨 PBR Model** for the PBR variant. **📋** copies the source URL.
4. Under **Convert locally**, pick STL, OBJ, FBX, 3MF or GLTF. The script
   downloads the captured GLB, converts it in the browser and saves the result;
   the status line shows the download progress and the final file name.

## Configuration

Everything is configured in the `CONFIG` object at the top of
[`src/userscript.template.js`](src/userscript.template.js):

| Key | Meaning |
| --- | --- |
| `POLL_INTERVAL` | Background poll interval in ms (default `2000`). |
| `ROUTE_CHECK_INTERVAL` | SPA route-change check interval in ms (default `1000`). |
| `MAX_SEARCH_DEPTH` | Maximum depth of the recursive state search (default `25`). |
| `MAX_URL_HISTORY` | Number of captured URLs kept in the history (default `20`). |
| `MODEL_KEYWORDS` | Keys in API/state objects that are treated as model references. |
| `GLB_PATTERNS` | URL fragments that identify a model resource. |
| `ASSET_EXTENSIONS` | Asset extensions the downloader recognises. |
| `ASSET_HOSTS` | Hosts whose URLs count as assets even without an extension. |
| `NON_ASSET_EXTENSIONS` | Extensions that are never treated as models. |
| `CONVERT_FORMATS` | Formats offered by the local converter, in priority order. |
| `API_PATTERNS` | URL fragments that mark a request as an API call to inspect. |

Edit the file and rebuild (`npm run build`) to apply changes.

## Repository layout

| Path | Purpose |
| --- | --- |
| `src/userscript.template.js` | Userscript source. The converter bundle is injected here at build time — do not hand-edit the injected code. |
| `src/converter.js` | Converter entry point: three.js GLTF loading plus the STL/OBJ/GLTF/FBX/3MF exporters. |
| `src/vendor/three3mf.mjs` | Vendored 3MF exporter. |
| `src/userscript.v9.1.js` | Older (v9.1) userscript, kept for reference. |
| `dist/tripo3d-model-downloader.user.js` | Built userscript that you install. |
| `dist/tripo-converter.js` | Standalone minified converter bundle. |
| `build.mjs` | Build script (bundle + inline + write `.user.js`). |
| `test3mf.mjs` | Small node script that exports a GLB to 3MF and inspects the archive. |

## Limitations

- The script only runs on `studio.tripo3d.ai` (the `@match` rule in the
  userscript header).
- A URL can only be captured once the asset is requested by the page. If the
  model was already loaded before the script ran, use **🔄 Refresh Scan** to run
  the deep search.
- Local conversion does not reproduce Tripo's paid server-side post-processing
  (quad remesh, face limit, texture bake / UV packing). STL and 3MF output is
  geometry only, FBX embeds the textures that are already on the model, and OBJ
  is written as geometry plus material library.
- Conversion of large meshes happens in the browser tab and takes a few
  seconds; a very large model needs a lot of memory.
- Downloads rely on `GM_xmlhttpRequest`/`GM_download`; on some userscript
  managers large binary responses can still be truncated. The magic-byte check
  warns you when that happens.

## License

MIT — see [LICENSE](LICENSE).

Copyright (c) 2026 thenobody0817.

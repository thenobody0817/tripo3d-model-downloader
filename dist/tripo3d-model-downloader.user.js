// ==UserScript==
// @name         Tripo3D Model Downloader
// @namespace    http://tampermonkey.net/
// @version      10.1
// @description  Extract & download Tripo models, and convert the GLB to STL / OBJ / FBX / 3MF / GLTF locally (no credits spent). Network interception (Fetch+XHR), API parsing, state analysis & resource monitoring.
// @author       TheNobody (V10.0 — multi-format capture + free client-side conversion)
// @match        https://studio.tripo3d.ai/*
// @grant        GM_xmlhttpRequest
// @grant        GM_download
// @grant        GM_setValue
// @grant        GM_getValue
// @grant        GM_addStyle
// @run-at       document-start
// ==/UserScript==

/*
CHANGELOG 9.0 -> 9.1
- Fixed unbounded recursion in extractUrlsFromObject(): it could walk into
  circular structures (Vue 3 reactive proxies, DOM nodes, window/document
  internals) with no cycle detection, which could throw "Maximum call
  stack size exceeded" and cause multi-second page freezes on every 2s
  poll. Added a WeakSet "seen" guard + an isSafeObject() type filter
  (credit: MrArni's feedback comment for the general approach — the
  original URL-matching logic is kept intact so link detection still
  actually works, which the community-suggested patch had dropped).
- comprehensiveSearch()'s full `window`-property walk (step 5) now only
  runs on an explicit deep search (manual "Refresh Scan" / initial button
  click), not on every 2s background poll, since it was the most
  expensive and highest-risk step for a freeze.
- downloadFile() now requests responseType: 'arraybuffer' instead of
  'blob'. GM_xmlhttpRequest's internal message-passing for large binary
  'blob' responses is known to silently truncate/corrupt on some
  Tampermonkey/Violentmonkey builds, which matches the "downloads but
  won't open in any viewer" reports. The ArrayBuffer is converted to a
  Blob locally with an explicit model/gltf-binary MIME type, and the
  first bytes are checked against the glTF binary magic header before
  confirming success — if they don't match, the file still saves but the
  user now gets a clear warning instead of a silently broken .glb.
CHANGELOG 9.1 -> 10.1
- 3MF export builds its ZIP synchronously with fflate (JSZip 3 removed the
  sync generate() and its async generateAsync() stalls inside userscript
  sandboxes). GLTF output is now stringified correctly (was emitting an
  object instead of JSON).
CHANGELOG 9.1 -> 10.0
- Multi-format capture: the script no longer only looks for .glb/.gltf. It now
  recognises STL, OBJ, FBX, 3MF, USD/USDZ, PLY, DAE and ZIP asset URLs too, and
  lists every captured asset in the dialog with a correct MIME type, filename
  and (where applicable) magic-byte check.
- NEW: free client-side conversion. Tripo's own "Export" to non-GLB formats is a
  paid server-side step (~5 credits each). Instead, this script converts the GLB
  you already have, entirely in your browser, using three.js + MeshoptDecoder:
  STL, OBJ, FBX and 3MF (plus GLTF). No Tripo credits are ever spent, no data is
  uploaded anywhere. The converter bundle is inlined below — it is generated
  (see the project build script) and should not be hand-edited.
- Download engine now picks the right MIME type per format and only runs the
  glTF magic check on .glb files, so OBJ/STL/FBX/3MF/ZIP downloads are not
  mis-flagged.
- Note: local conversion skips Tripo's paid post-processing (quad remesh,
  face_limit, texture bake / UV packing). STL and 3MF are geometry-only; FBX
  embeds the existing textures; OBJ is exported as geometry + MTL + textures in
  a ZIP when texture extraction succeeds.
*/

(function() {
    'use strict';

    // ============================================================
    //  CONFIGURATION
    // ============================================================
    const CONFIG = {
        // How often (ms) to poll for URL if network interception fails
        POLL_INTERVAL: 2000,
        // How often (ms) to check for SPA route changes
        ROUTE_CHECK_INTERVAL: 1000,
        // Maximum depth for recursive state search
        MAX_SEARCH_DEPTH: 25,
        // Maximum number of captured URLs to keep in history
        MAX_URL_HISTORY: 20,
        // Keywords that identify model-related keys in state/API responses
        MODEL_KEYWORDS: [
            'model_url', 'glb_url', 'file_url', 'model', 'asset',
            'src', 'url', 'pbr_model', 'base_model', 'rendered_image',
            'rendered_video', 'generated_image', 'download_url', 'export_url',
            'result_url', 'output_url', 'data_url', 'mesh_url'
        ],
        // URL patterns that indicate a GLB/model resource
        GLB_PATTERNS: [
            '.glb', '.gltf', 'model.glb', 'pbr_model.glb', 'base_model.glb',
            '/model?', '/download?', 'cloudfront.net', 'tripo3d.ai/model'
        ],
        // All 3D/archive extensions we can recognise as downloadable assets.
        ASSET_EXTENSIONS: [
            'glb', 'gltf', 'stl', 'obj', 'fbx', '3mf',
            'usd', 'usda', 'usdc', 'usdz', 'ply', 'dae', 'zip'
        ],
        // Known asset hosts — a URL from these counts as an asset even without
        // a recognisable extension (signed CDN URLs often have none).
        ASSET_HOSTS: ['tripo-data.', 'data.tripo3d.', '.cloudfront.net'],
        // Never treat these as downloadable models.
        NON_ASSET_EXTENSIONS: ['png', 'jpg', 'jpeg', 'webp', 'gif', 'mp4', 'webm', 'svg', 'json', 'js', 'css'],
        // Formats the built-in local converter can produce, in priority order.
        CONVERT_FORMATS: ['stl', 'obj', 'fbx', '3mf', 'gltf'],
        // API endpoints to watch for response interception
        API_PATTERNS: [
            'api.tripo3d.ai',
            '/api/',
            '/task/',
            '/model/',
            '/export',
            '/download'
        ]
    };

    // ============================================================
    //  STATE MANAGEMENT
    // ============================================================
    const state = {
        capturedModelUrl: null,         // Best known GLB URL
        capturedPbrUrl: null,           // PBR model URL
        capturedBaseUrl: null,          // Base model URL
        capturedRenderedImage: null,    // Rendered preview image URL
        urlHistory: [],                 // History of all found URLs
        apiResponses: [],               // Captured API response data
        isDialogOpen: false,
        lastRouteUrl: location.href,
        debugLogs: [],
        deepScanRunning: false          // guards against overlapping full-window scans
    };

    function log(tag, msg, data) {
        const prefix = `[Tripo V10.0 ${tag}]`;
        if (data !== undefined) {
            console.log(prefix, msg, data);
        } else {
            console.log(prefix, msg);
        }
        state.debugLogs.push({
            time: Date.now(),
            tag,
            msg,
            data: data ? String(data).substring(0, 200) : undefined
        });
        // Keep log buffer manageable
        if (state.debugLogs.length > 200) {
            state.debugLogs = state.debugLogs.slice(-100);
        }
    }

    function addUrlToHistory(url, source) {
        if (!url || typeof url !== 'string' || !url.startsWith('http')) return;
        // Avoid duplicates
        if (state.urlHistory.some(h => h.url === url)) return;

        state.urlHistory.unshift({
            url,
            source,
            time: Date.now()
        });
        if (state.urlHistory.length > CONFIG.MAX_URL_HISTORY) {
            state.urlHistory = state.urlHistory.slice(0, CONFIG.MAX_URL_HISTORY);
        }
        log('HIST', `Added URL from ${source}: ${url.substring(0, 80)}...`);
    }

    // Set the primary model URL (prioritize PBR > standard > base)
    function setModelUrl(url, source) {
        if (!url || typeof url !== 'string' || !url.startsWith('http')) return;

        // Classify URL
        if (url.includes('pbr_model') || url.includes('pbr')) {
            state.capturedPbrUrl = url;
            if (!state.capturedModelUrl || !state.capturedModelUrl.includes('pbr')) {
                state.capturedModelUrl = url;
            }
        } else if (url.includes('base_model') || url.includes('base')) {
            state.capturedBaseUrl = url;
            if (!state.capturedModelUrl) {
                state.capturedModelUrl = url;
            }
        } else if (url.includes('rendered_image') || url.match(/\.(png|jpg|jpeg|webp)/)) {
            state.capturedRenderedImage = url;
        } else {
            // Only a GLB/GLTF becomes the primary model. A captured OBJ/STL/FBX/
            // 3MF/ZIP export is recorded in history but must NOT replace the GLB
            // we convert from.
            const ext = assetExtension(url);
            const primaryExt = assetExtension(state.capturedModelUrl || '');
            if ((ext === 'glb' || ext === 'gltf') &&
                (!state.capturedModelUrl || !(primaryExt === 'glb' || primaryExt === 'gltf'))) {
                state.capturedModelUrl = url;
            }
        }

        addUrlToHistory(url, source);

        // Live-update dialog if open
        const input = document.getElementById('tripo-url-input');
        if (input) {
            input.value = url;
            input.style.color = '#0f0';
        }
        const statusEl = document.getElementById('tripo-status');
        if (statusEl) {
            statusEl.textContent = `URL captured via ${source}`;
            statusEl.style.color = '#4CAF50';
        }
    }

    // ============================================================
    //  1. NETWORK INTERCEPTION — FETCH HOOK (with response body capture)
    // ============================================================
    const originalFetch = window.fetch;

    window.fetch = function(...args) {
        const url = typeof args[0] === 'string' ? args[0] :
                    args[0] instanceof Request ? args[0].url : String(args[0]);

        // --- Check 1: Direct GLB URL in request ---
        if (isModelUrl(url)) {
            log('FETCH', 'Intercepted GLB request URL:', url);
            setModelUrl(url, 'fetch-request');
        }

        // --- Check 2: API response interception ---
        // If the URL looks like an API call, clone and read the response
        if (isApiUrl(url)) {
            log('FETCH', 'Intercepted API call:', url);

            return originalFetch.apply(this, args).then(response => {
                // Clone so we can read the body without consuming it
                const cloned = response.clone();

                // Read and parse response body asynchronously
                cloned.text().then(bodyText => {
                    try {
                        const json = JSON.parse(bodyText);
                        extractUrlsFromObject(json, 'fetch-api-response');
                    } catch (e) {
                        // Not JSON; check raw text for URLs
                        extractUrlsFromText(bodyText, 'fetch-api-raw');
                    }
                }).catch(err => {
                    log('FETCH', 'Could not read response body:', err.message);
                });

                return response; // Return original, unmodified response
            }).catch(err => {
                log('FETCH', 'Fetch error:', err.message);
                throw err;
            });
        }

        return originalFetch.apply(this, args);
    };

    // ============================================================
    //  2. NETWORK INTERCEPTION — XMLHttpRequest HOOK
    // ============================================================
    const originalXHROpen = XMLHttpRequest.prototype.open;
    const originalXHRSend = XMLHttpRequest.prototype.send;

    XMLHttpRequest.prototype.open = function(method, url, ...rest) {
        this._tripoUrl = url;
        this._tripoMethod = method;

        if (isModelUrl(url)) {
            log('XHR', 'Intercepted GLB request URL:', url);
            setModelUrl(url, 'xhr-request');
        }

        return originalXHROpen.call(this, method, url, ...rest);
    };

    XMLHttpRequest.prototype.send = function(...args) {
        const xhr = this;

        if (isApiUrl(xhr._tripoUrl)) {
            log('XHR', 'Monitoring API response for:', xhr._tripoUrl);

            const originalOnLoad = xhr.onload;
            const originalOnReadyStateChange = xhr.onreadystatechange;

            xhr.onreadystatechange = function(...ev) {
                if (xhr.readyState === 4 && xhr.responseText) {
                    try {
                        const json = JSON.parse(xhr.responseText);
                        extractUrlsFromObject(json, 'xhr-api-response');
                    } catch (e) {
                        extractUrlsFromText(xhr.responseText, 'xhr-api-raw');
                    }
                }
                if (originalOnReadyStateChange) {
                    return originalOnReadyStateChange.apply(this, ev);
                }
            };

            xhr.onload = function(...ev) {
                if (xhr.responseText) {
                    try {
                        const json = JSON.parse(xhr.responseText);
                        extractUrlsFromObject(json, 'xhr-api-response');
                    } catch (e) {
                        extractUrlsFromText(xhr.responseText, 'xhr-api-raw');
                    }
                }
                if (originalOnLoad) {
                    return originalOnLoad.apply(this, ev);
                }
            };
        }

        return originalXHRSend.apply(this, args);
    };

    // ============================================================
    //  3. PERFORMANCE OBSERVER (Resource Timing API)
    // ============================================================
    function initPerformanceObserver() {
        try {
            const observer = new PerformanceObserver((list) => {
                for (const entry of list.getEntries()) {
                    if (isModelUrl(entry.name)) {
                        log('PERF', 'Detected GLB resource load:', entry.name);
                        setModelUrl(entry.name, 'performance-observer');
                    }
                }
            });
            observer.observe({ entryTypes: ['resource'] });
            log('INIT', 'PerformanceObserver active');
        } catch (e) {
            log('INIT', 'PerformanceObserver not supported:', e.message);
        }
    }

    // ============================================================
    //  4. URL DETECTION HELPERS
    // ============================================================
    // Per-format metadata: MIME type, human label and optional magic bytes.
    const FORMAT_INFO = {
        glb:   { mime: 'model/gltf-binary',           label: 'GLB',  magic: [0x67, 0x6C, 0x54, 0x46] },
        gltf:  { mime: 'model/gltf+json',             label: 'GLTF' },
        stl:   { mime: 'model/stl',                   label: 'STL'  },
        obj:   { mime: 'text/plain',                  label: 'OBJ'  },
        fbx:   { mime: 'application/octet-stream',    label: 'FBX',  magicText: 'Kaydara FBX Binary' },
        '3mf': { mime: 'model/3mf',                   label: '3MF',  magic: [0x50, 0x4B, 0x03, 0x04] },
        usdz:  { mime: 'model/vnd.usdz+zip',          label: 'USDZ', magic: [0x50, 0x4B, 0x03, 0x04] },
        usd:   { mime: 'model/vnd.usd',               label: 'USD'  },
        usda:  { mime: 'model/vnd.usd',               label: 'USDA' },
        usdc:  { mime: 'model/vnd.usd',               label: 'USDC' },
        ply:   { mime: 'application/octet-stream',    label: 'PLY'  },
        dae:   { mime: 'model/vnd.collada+xml',       label: 'DAE'  },
        zip:   { mime: 'application/zip',             label: 'ZIP',  magic: [0x50, 0x4B, 0x03, 0x04] }
    };

    // Lower-case file extension from a URL path (query/fragment stripped).
    function assetExtension(url) {
        if (!url || typeof url !== 'string') return '';
        const path = url.split('#')[0].split('?')[0];
        const m = path.match(/\.([A-Za-z0-9]+)$/);
        return m ? m[1].toLowerCase() : '';
    }

    function assetFromHost(url) {
        const lower = String(url).toLowerCase();
        return CONFIG.ASSET_HOSTS.some(h => lower.includes(h));
    }

    // An "asset" is anything we could sensibly offer to download: a recognised
    // 3D/archive extension, or a URL from a known asset CDN host (signed URLs
    // often carry no extension at all).
    function isAssetUrl(url) {
        if (!url || typeof url !== 'string' || !url.startsWith('http')) return false;
        const ext = assetExtension(url);
        if (ext && CONFIG.NON_ASSET_EXTENSIONS.includes(ext)) return false;
        if (ext && CONFIG.ASSET_EXTENSIONS.includes(ext)) return true;
        return assetFromHost(url);
    }

    // Backwards-compatible name used throughout the rest of the script, now
    // widened to cover every asset format (not just GLB).
    function isModelUrl(url) {
        return isAssetUrl(url);
    }

    function formatInfo(url) {
        const ext = assetExtension(url);
        return FORMAT_INFO[ext] || {
            mime: 'application/octet-stream',
            label: ext ? ext.toUpperCase() : 'FILE'
        };
    }

    function isApiUrl(url) {
        if (!url || typeof url !== 'string') return false;
        const lower = url.toLowerCase();
        return CONFIG.API_PATTERNS.some(p => lower.includes(p.toLowerCase()));
    }

    // Only walk into things that are plausibly plain app state — never into
    // live DOM/Window/Document objects. This is what turned unbounded
    // recursion into circular-reference stack overflows before.
    function isSafeObject(value) {
        if (value === null || typeof value !== 'object') return false;
        if (value === window || value === document) return false;
        if (typeof Window !== 'undefined' && value instanceof Window) return false;
        if (typeof Document !== 'undefined' && value instanceof Document) return false;
        if (typeof Node !== 'undefined' && value instanceof Node) return false; // covers HTMLElement, Text, etc.
        return true;
    }

    // Extract URLs from a JSON/state object (recursive search).
    // `seen` guards against circular references — Vue 3 reactive proxies in
    // particular tend to point back at their parent/root, which is what was
    // causing "Maximum call stack size exceeded" / freezes.
    function extractUrlsFromObject(obj, source, depth = 0, seen = new WeakSet()) {
        if (depth > CONFIG.MAX_SEARCH_DEPTH) return;
        if (!isSafeObject(obj)) return;
        if (seen.has(obj)) return;
        seen.add(obj);

        // Handle Vue 3 Refs
        if (obj.__v_isRef && obj.value !== undefined) {
            return extractUrlsFromObject(obj.value, source, depth + 1, seen);
        }

        for (const key in obj) {
            try {
                if (!obj.hasOwnProperty(key)) continue;
                const value = obj[key];

                // If the key matches a model keyword and the value is a URL-like string
                if (typeof value === 'string' && value.startsWith('http')) {
                    const keyLower = key.toLowerCase();
                    const isModelKey = CONFIG.MODEL_KEYWORDS.some(k => keyLower.includes(k.toLowerCase()));

                    if (isModelKey && isModelUrl(value)) {
                        log('EXTRACT', `Found model URL via key "${key}":`, value.substring(0, 80));
                        setModelUrl(value, `${source}[${key}]`);
                    } else if (isModelKey && value.includes('http')) {
                        // Key matches but URL doesn't have .glb — could still be a download API
                        log('EXTRACT', `Found potential model URL via key "${key}":`, value.substring(0, 80));
                        addUrlToHistory(value, `${source}[${key}]`);
                    }
                }

                // Never recurse into these by name, even if they slip past isSafeObject
                if (key === 'document' || key === 'window' ||
                    key === 'parent' || key === 'top' || key === 'frames') {
                    continue;
                }

                // Recurse into nested objects (cycle-safe)
                if (isSafeObject(value)) {
                    extractUrlsFromObject(value, source, depth + 1, seen);
                }
            } catch (e) {
                // Skip inaccessible properties
            }
        }
    }

    // Extract URLs from raw text (regex scan)
    function extractUrlsFromText(text, source) {
        if (!text || typeof text !== 'string') return;
        // Match URLs that look like model URLs
        const urlRegex = /https?:\/\/[^\s"'<>{}]+/g;
        let match;
        while ((match = urlRegex.exec(text)) !== null) {
            const url = match[0];
            if (isModelUrl(url)) {
                log('EXTRACT', 'Found URL in text:', url.substring(0, 80));
                setModelUrl(url, source);
            }
        }
    }

    // ============================================================
    //  5. STATE / RUNTIME ANALYSIS
    // ============================================================
    function searchNuxtState() {
        // Priority 1: __NUXT__ state
        if (window.__NUXT__) {
            extractUrlsFromObject(window.__NUXT__, 'nuxt-state');
            if (state.capturedModelUrl) return true;
        }
        // Priority 2: $nuxt
        if (window.$nuxt) {
            extractUrlsFromObject(window.$nuxt, 'nuxt-instance');
            if (state.capturedModelUrl) return true;
        }
        // Priority 3: Vue app instance
        if (window.__vue_app__) {
            extractUrlsFromObject(window.__vue_app__, 'vue-app');
            if (state.capturedModelUrl) return true;
        }
        // Priority 4: Try Pinia/Vuex stores
        try {
            const nuxtApp = window.__NUXT__ || window.useNuxtApp?.();
            if (nuxtApp && nuxtApp.$pinia) {
                extractUrlsFromObject(nuxtApp.$pinia.state?.value || nuxtApp.$pinia, 'pinia-store');
            }
        } catch (e) {}
        return false;
    }

    // Scan DOM for model source attributes
    function searchDOM() {
        // Check all source/src/data attributes on elements
        const attrs = ['src', 'source', 'data-src', 'data-url', 'data-model', 'data-source', 'href'];
        const selectors = attrs.map(a => `[${a}*=".glb"], [${a}*=".gltf"], [${a}*="model"]`).join(', ');

        try {
            const elements = document.querySelectorAll(selectors);
            elements.forEach(el => {
                attrs.forEach(attr => {
                    const val = el.getAttribute(attr);
                    if (val && isModelUrl(val)) {
                        log('DOM', `Found model URL in ${attr}:`, val);
                        setModelUrl(val, `dom-${attr}`);
                    }
                });
            });
        } catch (e) {}

        // Check canvas elements' parent containers for data attributes
        try {
            const canvases = document.querySelectorAll('canvas');
            canvases.forEach(canvas => {
                let parent = canvas.parentElement;
                let depth = 0;
                while (parent && depth < 5) {
                    const dataset = parent.dataset;
                    for (const key in dataset) {
                        if (typeof dataset[key] === 'string' && isModelUrl(dataset[key])) {
                            log('DOM', `Found model URL in canvas parent data-${key}:`, dataset[key]);
                            setModelUrl(dataset[key], `dom-canvas-data`);
                        }
                    }
                    parent = parent.parentElement;
                    depth++;
                }
            });
        } catch (e) {}
    }

    // Comprehensive search combining all strategies.
    // `deep` gates the expensive full-`window`-property walk (step 5) — that
    // one is only worth the cost on an explicit user-triggered scan, not on
    // every 2s background poll.
    async function comprehensiveSearch(deep = false) {
        log('SEARCH', `Running ${deep ? 'deep' : 'quick'} URL search...`);

        // 1. Already captured via network
        if (state.capturedModelUrl) return state.capturedModelUrl;

        // 2. Search Nuxt/Vue state
        searchNuxtState();
        if (state.capturedModelUrl) return state.capturedModelUrl;

        // 3. Search DOM
        searchDOM();
        if (state.capturedModelUrl) return state.capturedModelUrl;

        // 4. Check Performance entries
        try {
            const entries = performance.getEntriesByType('resource');
            for (const entry of entries) {
                if (isModelUrl(entry.name)) {
                    setModelUrl(entry.name, 'performance-cache');
                    return state.capturedModelUrl;
                }
            }
        } catch (e) {}

        // 5. Scan global window properties for any object containing model URLs.
        // Deep-only: expensive, and the main historical source of freezes.
        if (deep && !state.deepScanRunning) {
            state.deepScanRunning = true;
            try {
                for (const key of Object.keys(window)) {
                    try {
                        const val = window[key];
                        if (isSafeObject(val) && !Array.isArray(val)) {
                            extractUrlsFromObject(val, `window[${key}]`, 0);
                            if (state.capturedModelUrl) break;
                        }
                    } catch (e) {}
                }
            } finally {
                state.deepScanRunning = false;
            }
        }

        return state.capturedModelUrl;
    }

    // ============================================================
    //  6. DOWNLOAD ENGINE
    // ============================================================
    // GLB magic, per the glTF 2.0 spec (ASCII "glTF").
    const GLB_MAGIC = [0x67, 0x6C, 0x54, 0x46];

    function looksLikeValidGlb(arrayBuffer) {
        if (!arrayBuffer || arrayBuffer.byteLength < 12) return false;
        return looksLikeMagic(arrayBuffer, GLB_MAGIC);
    }

    // Does the buffer start with the given byte signature?
    function looksLikeMagic(arrayBuffer, magic) {
        if (!magic) return true;
        if (!arrayBuffer || arrayBuffer.byteLength < magic.length) return false;
        const bytes = new Uint8Array(arrayBuffer, 0, magic.length);
        return magic.every((b, i) => bytes[i] === b);
    }

    function looksLikeText(arrayBuffer, text) {
        if (!arrayBuffer || arrayBuffer.byteLength < text.length) return false;
        const head = new TextDecoder('latin1').decode(new Uint8Array(arrayBuffer, 0, text.length));
        return head === text;
    }

    // Validate a downloaded buffer against the format's known signature.
    function checkFileMagic(buffer, info) {
        if (buffer && buffer.byteLength === 0) return false;
        if (info && info.magic) return looksLikeMagic(buffer, info.magic);
        if (info && info.magicText) return looksLikeText(buffer, info.magicText);
        return true;
    }

    // Signed download links usually return an HTML/XML error page when expired.
    function isProbablyHtml(buffer) {
        if (!buffer || buffer.byteLength < 1) return false;
        const n = Math.min(64, buffer.byteLength);
        const head = new TextDecoder('latin1').decode(new Uint8Array(buffer, 0, n)).trim().toLowerCase();
        return head.startsWith('<!doctype') || head.startsWith('<html') || head.startsWith('<?xml');
    }

    // Save an in-memory Blob to disk (used by both downloadFile and convert).
    function saveBlob(blob, name) {
        const blobUrl = URL.createObjectURL(blob);
        const a = document.createElement('a');
        a.href = blobUrl;
        a.download = name;
        document.body.appendChild(a);
        a.click();
        document.body.removeChild(a);
        setTimeout(() => URL.revokeObjectURL(blobUrl), 10000);
    }

    function downloadFile(url, filename) {
        if (!url || !url.startsWith('http')) {
            alert('No valid URL to download.');
            return;
        }

        const info = formatInfo(url);
        const name = filename || generateFilename(url);

        log('DL', `Starting download [${info.label}]: ${url.substring(0, 80)}... → ${name}`);

        GM_xmlhttpRequest({
            method: 'GET',
            url: url,
            headers: {
                'Referer': window.location.href,
                'Origin': window.location.origin
            },
            // ArrayBuffer transfers far more reliably than 'blob' across the
            // extension's internal message bridge for large binary payloads.
            responseType: 'arraybuffer',
            timeout: 120000, // 2 minute timeout for large files
            onload: function(resp) {
                if (resp.status === 200) {
                    try {
                        const buffer = resp.response;

                        if (isProbablyHtml(buffer)) {
                            log('DL', 'Got an HTML/XML response instead of a file — link likely expired');
                            showToast('That link returned a web page, not a file — it has probably expired. Reload the model page and try again.', 'error');
                            return;
                        }

                        const magicOk = checkFileMagic(buffer, info);
                        const blob = new Blob([buffer], { type: info.mime });
                        saveBlob(blob, name);
                        log('DL', `Download started successfully (${buffer.byteLength} bytes)`);
                        showToast(`Download started (${info.label}, ${(buffer.byteLength / 1048576).toFixed(1)} MB)`, 'success');

                        if (!magicOk) {
                            log('DL', `Content did not match the expected ${info.label} signature`);
                            showToast(`Downloaded, but this doesn't look like a valid ${info.label} file — the model may still be processing. Try again in a bit.`, 'error');
                        }
                    } catch (e) {
                        log('DL', 'Binary download failed, trying window.open:', e.message);
                        fallbackDownload(url, name);
                    }
                } else if (resp.status === 403 || resp.status === 401) {
                    log('DL', `Auth error ${resp.status}, URL may have expired`);
                    showToast('URL expired (403). Try refreshing the model page first.', 'error');
                } else {
                    log('DL', `HTTP error ${resp.status}`);
                    showToast(`Download failed (HTTP ${resp.status}). Try copying the URL.`, 'error');
                }
            },
            onerror: function(err) {
                log('DL', 'Network error:', err);
                showToast('Network error. The link might have expired.', 'error');
            },
            ontimeout: function() {
                log('DL', 'Download timed out');
                showToast('Download timed out. The file may be too large.', 'error');
            }
        });
    }

    function fallbackDownload(url, name) {
        // Fallback: open in new tab (browser will handle download for S3 presigned URLs)
        window.open(url, '_blank');
        showToast('Opened in new tab. Right-click → Save As if needed.', 'info');
    }

    function generateFilename(url) {
        try {
            const pathPart = url.split('?')[0].split('#')[0]; // Remove query/fragment
            const filename = decodeURIComponent(pathPart.split('/').pop() || ''); // last segment
            if (filename && filename.length > 3 && filename.includes('.')) return filename;
        } catch (e) {}
        return `tripo_model_${Date.now()}.${assetExtension(url) || 'bin'}`;
    }

    // ============================================================
    //  6b. LOCAL CONVERSION (free — no Tripo credits spent)
    // ============================================================
    // Find the best GLB/GLTF URL to convert from.
    function capturedGlbUrl() {
        const candidates = [state.capturedPbrUrl, state.capturedBaseUrl, state.capturedModelUrl];
        for (const c of candidates) {
            if (c && /\.(glb|gltf)(\?|#|$)/i.test(c)) return c;
        }
        const hit = state.urlHistory.find(h => /\.(glb|gltf)(\?|#|$)/i.test(h.url));
        return hit ? hit.url : null;
    }

    // Human-friendly base filename for converted output.
    function modelBasename() {
        try {
            const m = location.pathname.match(/\/3d-model\/(.+?)-[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}/i);
            if (m && m[1]) return m[1].slice(0, 60);
        } catch (e) {}
        const glb = capturedGlbUrl();
        if (glb) {
            let base = (glb.split('?')[0].split('#')[0].split('/').pop() || '').replace(/\.(glb|gltf)$/i, '');
            base = base.replace(/[^A-Za-z0-9._-]+/g, '_').replace(/_?meshopt$/i, '').replace(/^_+|_+$/g, '');
            if (base) return base;
        }
        return 'tripo_model';
    }

    function fetchAsArrayBuffer(url, onProgress) {
        return new Promise((resolve, reject) => {
            GM_xmlhttpRequest({
                method: 'GET',
                url: url,
                headers: { 'Referer': window.location.href, 'Origin': window.location.origin },
                responseType: 'arraybuffer',
                timeout: 180000,
                onprogress: function (e) {
                    if (onProgress && e && e.lengthComputable) onProgress(e.loaded, e.total);
                },
                onload: function (resp) {
                    if (resp.status === 200 && resp.response) resolve(resp.response);
                    else reject(new Error(`HTTP ${resp.status}`));
                },
                onerror: function () { reject(new Error('network error')); },
                ontimeout: function () { reject(new Error('timed out')); }
            });
        });
    }

    function setConversionStatus(msg, color) {
        const el = document.getElementById('tripo-conv-status');
        if (el) { el.textContent = msg; el.style.color = color || '#888'; }
    }

    // Convert the captured GLB to `format` entirely in the browser and save it.
    async function convertCaptured(format) {
        if (typeof TripoConverter === 'undefined') {
            showToast('Converter bundle failed to initialise.', 'error');
            return;
        }
        const url = capturedGlbUrl();
        if (!url) {
            showToast('No GLB captured yet — make sure the model is fully loaded, then retry.', 'error');
            return;
        }
        const info = FORMAT_INFO[format] || { label: format.toUpperCase() };
        const label = info.label;
        try {
            setConversionStatus('Downloading the GLB…', '#FF9800');
            const buffer = await fetchAsArrayBuffer(url, (loaded, total) => {
                if (total) setConversionStatus(`Downloading the GLB… ${Math.round(loaded / total * 100)}%`, '#FF9800');
            });
            setConversionStatus(`Converting to ${label}… this can take a few seconds.`, '#FF9800');
            await new Promise(r => setTimeout(r, 30)); // let the UI repaint first
            const result = await TripoConverter.convertGlb(buffer, format, { basename: modelBasename() });
            saveBlob(result.blob, result.filename);
            const mb = (result.blob.size / 1048576).toFixed(1);
            setConversionStatus(`Saved ${result.filename} (${mb} MB).`, '#4CAF50');
            showToast(`${label} ready: ${result.filename} (${mb} MB)`, 'success');
            log('CONV', `Converted to ${format}: ${result.filename} (${result.blob.size} bytes)`);
        } catch (e) {
            log('CONV', `Conversion to ${format} failed: ${e.message}`);
            setConversionStatus(`Conversion failed: ${e.message}`, '#f44336');
            showToast(`Conversion to ${label} failed: ${e.message}`, 'error');
        }
    }

    // ============================================================
    //  7. UI — TOAST NOTIFICATIONS
    // ============================================================
    function showToast(message, type = 'info') {
        const existing = document.getElementById('tripo-toast');
        if (existing) existing.remove();

        const colors = {
            success: { bg: '#1b5e20', border: '#4CAF50' },
            error: { bg: '#b71c1c', border: '#f44336' },
            info: { bg: '#0d47a1', border: '#2196F3' }
        };
        const color = colors[type] || colors.info;

        const toast = document.createElement('div');
        toast.id = 'tripo-toast';
        toast.style.cssText = `
            position: fixed; top: 20px; right: 20px; z-index: 2147483647;
            padding: 12px 20px; border-radius: 8px; color: #fff;
            background: ${color.bg}; border: 1px solid ${color.border};
            font-family: -apple-system, BlinkMacSystemFont, sans-serif;
            font-size: 14px; max-width: 400px;
            box-shadow: 0 4px 12px rgba(0,0,0,0.3);
            transition: opacity 0.3s;
        `;
        toast.textContent = message;
        document.body.appendChild(toast);

        setTimeout(() => {
            toast.style.opacity = '0';
            setTimeout(() => toast.remove(), 300);
        }, 4000);
    }

    // ============================================================
    //  8. UI — MAIN DOWNLOAD BUTTON
    // ============================================================
    function addButton() {
        const oldBtn = document.getElementById('tripo-dl-btn-main');
        if (oldBtn) oldBtn.remove();

        const btn = document.createElement('button');
        btn.id = 'tripo-dl-btn-main';
        btn.innerHTML = '⬇ DL Model';
        btn.style.cssText = `
            position: fixed; bottom: 30px; right: 30px; z-index: 2147483646;
            padding: 14px 24px;
            background: linear-gradient(135deg, #4CAF50, #2E7D32);
            color: white; border: none; border-radius: 30px; cursor: pointer;
            font-weight: bold; font-size: 15px;
            font-family: -apple-system, BlinkMacSystemFont, sans-serif;
            box-shadow: 0 4px 15px rgba(76, 175, 80, 0.4);
            transition: transform 0.2s, box-shadow 0.2s;
            user-select: none;
        `;
        btn.onmouseenter = () => {
            btn.style.transform = 'scale(1.08)';
            btn.style.boxShadow = '0 6px 20px rgba(76, 175, 80, 0.6)';
        };
        btn.onmouseleave = () => {
            btn.style.transform = 'scale(1)';
            btn.style.boxShadow = '0 4px 15px rgba(76, 175, 80, 0.4)';
        };

        // Badge indicator for captured URL
        const badge = document.createElement('span');
        badge.id = 'tripo-badge';
        badge.style.cssText = `
            position: absolute; top: -6px; right: -6px;
            width: 14px; height: 14px; border-radius: 50%;
            background: #f44336; border: 2px solid #1e1e2e;
            display: none;
        `;
        btn.style.position = 'fixed';
        btn.appendChild(badge);

        btn.onclick = async () => {
            await comprehensiveSearch(true);
            showDialog();
        };

        document.body.appendChild(btn);
    }

    // Update badge visibility
    function updateBadge() {
        const badge = document.getElementById('tripo-badge');
        if (badge) {
            badge.style.display = state.capturedModelUrl ? 'block' : 'none';
            badge.style.background = state.capturedModelUrl ? '#4CAF50' : '#f44336';
        }
    }

    // ============================================================
    //  9. UI — DOWNLOAD DIALOG
    // ============================================================
    function showDialog() {
        const existing = document.getElementById('tripo-dialog');
        if (existing) existing.remove();

        state.isDialogOpen = true;

        const dialog = document.createElement('div');
        dialog.id = 'tripo-dialog';
        dialog.style.cssText = `
            position: fixed; top: 50%; left: 50%; transform: translate(-50%, -50%);
            background: #1a1a2e; color: #e0e0e0; padding: 0;
            border-radius: 16px; z-index: 2147483647;
            box-shadow: 0 20px 60px rgba(0,0,0,0.7);
            width: 520px; max-width: 95vw; max-height: 90vh;
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
            border: 1px solid #333; overflow: hidden;
        `;

        const hasUrl = state.capturedModelUrl;
        const statusText = hasUrl ? 'URL captured — ready to download' : 'Scanning network...';

        const urlOptions = state.urlHistory
            .map((h, i) => ({ h, i }))
            .filter(({ h }) => isModelUrl(h.url))
            .slice(0, 12)
            .map(({ h, i }) => {
                const shortUrl = h.url.length > 60 ? h.url.substring(0, 57) + '...' : h.url;
                const info = formatInfo(h.url);
                const type = h.url.includes('pbr_model') ? 'PBR ' + info.label :
                             h.url.includes('base_model') ? 'Base ' + info.label : info.label;
                return `<option value="${i}" title="${h.url}">[${type}] ${shortUrl} (${h.source})</option>`;
            }).join('');

        dialog.innerHTML = `
            <!-- Header -->
            <div style="background: linear-gradient(135deg, #1b5e20, #2E7D32); padding: 18px 24px; display: flex; justify-content: space-between; align-items: center;">
                <div>
                    <h3 style="margin: 0; color: #fff; font-size: 18px;">Download 3D Model</h3>
                    <p id="tripo-status" style="margin: 4px 0 0; font-size: 12px; color: #a5d6a7;">${statusText}</p>
                </div>
                <button id="btn-close" style="background: rgba(255,255,255,0.15); border: none; color: #fff; width: 32px; height: 32px; border-radius: 50%; cursor: pointer; font-size: 18px; display: flex; align-items: center; justify-content: center;">✕</button>
            </div>

            <!-- Body -->
            <div style="padding: 20px 24px;">
                <!-- Primary URL display -->
                <div style="margin-bottom: 16px;">
                    <label style="font-size: 11px; color: #888; text-transform: uppercase; letter-spacing: 1px;">Source URL</label>
                    <input id="tripo-url-input" type="text" readonly
                        value="${hasUrl ? state.capturedModelUrl : 'Scanning network...'}"
                        style="width: 100%; padding: 10px 12px; background: #0d0d1a; border: 1px solid #333;
                               color: ${hasUrl ? '#0f0' : '#fa0'}; border-radius: 8px; font-size: 12px;
                               font-family: 'SF Mono', 'Consolas', monospace; margin-top: 4px; box-sizing: border-box;">
                </div>

                <!-- URL History dropdown (if multiple URLs found) -->
                ${state.urlHistory.filter(h => isModelUrl(h.url)).length > 1 ? `
                <div style="margin-bottom: 16px;">
                    <label style="font-size: 11px; color: #888; text-transform: uppercase; letter-spacing: 1px;">Available URLs</label>
                    <select id="tripo-url-select" style="width: 100%; padding: 8px; background: #0d0d1a; border: 1px solid #333;
                           color: #0f0; border-radius: 8px; font-size: 11px; font-family: monospace; margin-top: 4px;">
                        ${urlOptions}
                    </select>
                </div>
                ` : ''}

                <!-- Action Buttons -->
                <div style="display: flex; gap: 8px; flex-wrap: wrap; margin-bottom: 16px;">
                    <button id="btn-dl" style="flex: 1; min-width: 120px; padding: 12px 16px; background: linear-gradient(135deg, #4CAF50, #2E7D32);
                        border: none; border-radius: 8px; color: white; cursor: pointer; font-weight: 600; font-size: 14px;
                        transition: opacity 0.2s;">
                        ⬇ Download
                    </button>
                    <button id="btn-dl-pbr" style="flex: 1; min-width: 120px; padding: 12px 16px; background: linear-gradient(135deg, #7C4DFF, #651FFF);
                        border: none; border-radius: 8px; color: white; cursor: pointer; font-weight: 600; font-size: 14px;
                        transition: opacity 0.2s; ${state.capturedPbrUrl ? '' : 'opacity: 0.5;'}">
                        🎨 PBR Model
                    </button>
                    <button id="btn-copy" style="padding: 12px 16px; background: #1565C0;
                        border: none; border-radius: 8px; color: white; cursor: pointer; font-size: 14px; min-width: 44px;">
                        📋
                    </button>
                </div>

                <!-- Local conversion (free, no Tripo credits) -->
                <div style="margin-bottom: 16px; border-top: 1px solid #2a2a3e; padding-top: 14px;">
                    <div style="font-size: 11px; color: #888; text-transform: uppercase; letter-spacing: 1px; margin-bottom: 8px;">
                        Convert locally <span style="color:#4CAF50;">free</span>
                        <span style="color:#666; text-transform:none; letter-spacing:0;">— no Tripo credits spent</span>
                    </div>
                    <div id="tripo-conv-buttons" style="display: flex; gap: 8px; flex-wrap: wrap;"></div>
                    <div id="tripo-conv-status" style="margin-top: 10px; font-size: 12px; color: #888; line-height: 1.4;">
                        Converts the captured GLB in your browser. STL &amp; 3MF are geometry-only; FBX embeds textures.
                    </div>
                </div>

                <div style="display: flex; gap: 8px;">
                    <button id="btn-refresh" style="flex: 1; padding: 10px; background: #E65100; border: none; border-radius: 8px;
                        color: white; cursor: pointer; font-size: 13px;">
                        🔄 Refresh Scan
                    </button>
                    <button id="btn-copy-all" style="flex: 1; padding: 10px; background: #333; border: none; border-radius: 8px;
                        color: #aaa; cursor: pointer; font-size: 13px;">
                        📄 Copy All URLs
                    </button>
                </div>

                <!-- Debug info (collapsed) -->
                <details style="margin-top: 16px; font-size: 12px; color: #666;">
                    <summary style="cursor: pointer; color: #555;">Debug Info (${state.debugLogs.length} logs)</summary>
                    <div id="tripo-debug" style="max-height: 150px; overflow-y: auto; background: #0d0d1a; padding: 8px;
                        border-radius: 6px; margin-top: 6px; font-family: monospace; font-size: 10px; color: #888;">
                        ${state.debugLogs.slice(-20).map(l =>
                            `<div>[${new Date(l.time).toLocaleTimeString()}] ${l.tag}: ${l.msg}${l.data ? ' → ' + l.data : ''}</div>`
                        ).join('')}
                    </div>
                </details>
            </div>
        `;

        document.body.appendChild(dialog);

        // --- Event Handlers ---

        // Download primary model
        document.getElementById('btn-dl').onclick = () => {
            const url = getSelectedUrl();
            if (url && url.startsWith('http')) {
                downloadFile(url);
            } else {
                showToast('No valid URL found yet. Wait a moment or click Refresh.', 'error');
            }
        };

        // Download PBR model
        document.getElementById('btn-dl-pbr').onclick = () => {
            const url = state.capturedPbrUrl || state.capturedModelUrl;
            if (url && url.startsWith('http')) {
                downloadFile(url);
            } else {
                showToast('No PBR model URL available.', 'error');
            }
        };

        // --- Local conversion buttons (free) ---
        const convWrap = document.getElementById('tripo-conv-buttons');
        if (convWrap) {
            CONFIG.CONVERT_FORMATS.forEach(fmt => {
                const info = FORMAT_INFO[fmt] || { label: fmt.toUpperCase() };
                const b = document.createElement('button');
                b.textContent = `→ ${info.label}`;
                b.title = `Convert the captured GLB to ${info.label} in your browser (no Tripo credits used)`;
                b.style.cssText = 'flex: 1; min-width: 64px; padding: 10px 12px; background: #263238; border: 1px solid #37474F; border-radius: 8px; color: #B0BEC5; cursor: pointer; font-weight: 600; font-size: 13px;';
                b.onmouseenter = () => { b.style.background = '#37474F'; b.style.color = '#fff'; };
                b.onmouseleave = () => { b.style.background = '#263238'; b.style.color = '#B0BEC5'; };
                b.onclick = () => convertCaptured(fmt);
                convWrap.appendChild(b);
            });
        }

        // Copy URL
        document.getElementById('btn-copy').onclick = () => {
            const url = getSelectedUrl();
            if (url) {
                navigator.clipboard.writeText(url).then(() => {
                    showToast('URL copied to clipboard!', 'success');
                }).catch(() => {
                    // Fallback for insecure contexts
                    const ta = document.createElement('textarea');
                    ta.value = url;
                    document.body.appendChild(ta);
                    ta.select();
                    document.execCommand('copy');
                    ta.remove();
                    showToast('URL copied!', 'success');
                });
            }
        };

        // Refresh / rescan
        document.getElementById('btn-refresh').onclick = async () => {
            const input = document.getElementById('tripo-url-input');
            const statusEl = document.getElementById('tripo-status');
            input.value = 'Scanning...';
            input.style.color = '#fa0';
            statusEl.textContent = 'Running full scan...';
            statusEl.style.color = '#FF9800';

            const url = await comprehensiveSearch(true);
            if (url) {
                input.value = url;
                input.style.color = '#0f0';
                statusEl.textContent = 'URL found!';
                statusEl.style.color = '#4CAF50';
                showToast('Model URL found!', 'success');
            } else {
                input.value = 'No URL found — make sure a model is fully loaded';
                input.style.color = '#f44336';
                statusEl.textContent = 'No URL detected. Try loading the model first.';
                statusEl.style.color = '#f44336';
            }
        };

        // Copy all URLs
        document.getElementById('btn-copy-all').onclick = () => {
            const urls = state.urlHistory.map(h => `[${h.source}] ${h.url}`).join('\n');
            if (urls) {
                navigator.clipboard.writeText(urls).then(() => {
                    showToast('All URLs copied!', 'success');
                }).catch(() => {
                    const ta = document.createElement('textarea');
                    ta.value = urls;
                    document.body.appendChild(ta);
                    ta.select();
                    document.execCommand('copy');
                    ta.remove();
                    showToast('All URLs copied!', 'success');
                });
            } else {
                showToast('No URLs captured yet.', 'info');
            }
        };

        // URL history dropdown
        const selectEl = document.getElementById('tripo-url-select');
        if (selectEl) {
            selectEl.onchange = () => {
                const idx = parseInt(selectEl.value);
                const entry = state.urlHistory[idx];
                if (entry) {
                    const input = document.getElementById('tripo-url-input');
                    input.value = entry.url;
                    input.style.color = '#0f0';
                }
            };
        }

        // Close
        document.getElementById('btn-close').onclick = () => {
            dialog.remove();
            state.isDialogOpen = false;
        };

        // Close on Escape
        const escHandler = (e) => {
            if (e.key === 'Escape') {
                dialog.remove();
                state.isDialogOpen = false;
                document.removeEventListener('keydown', escHandler);
            }
        };
        document.addEventListener('keydown', escHandler);
    }

    function getSelectedUrl() {
        const input = document.getElementById('tripo-url-input');
        return input ? input.value : null;
    }

    // ============================================================
    //  10. ROUTE WATCHER (SPA Navigation Support)
    // ============================================================
    function initRouteWatcher() {
        // Also hook pushState/replaceState for immediate detection
        const origPushState = history.pushState;
        const origReplaceState = history.replaceState;

        history.pushState = function(...args) {
            origPushState.apply(this, args);
            handleRouteChange();
        };

        history.replaceState = function(...args) {
            origReplaceState.apply(this, args);
            handleRouteChange();
        };

        window.addEventListener('popstate', handleRouteChange);

        // Fallback interval check
        setInterval(() => {
            if (location.href !== state.lastRouteUrl) {
                handleRouteChange();
            }
        }, CONFIG.ROUTE_CHECK_INTERVAL);
    }

    function handleRouteChange() {
        const newUrl = location.href;
        if (newUrl !== state.lastRouteUrl) {
            log('ROUTE', `Route changed: ${state.lastRouteUrl} → ${newUrl}`);
            state.lastRouteUrl = newUrl;
            // Don't reset capturedModelUrl on route change —
            // the old URL might still be valid. Let the user refresh manually.
        }
    }

    // ============================================================
    //  11. BACKGROUND POLLER (Fallback)
    // ============================================================
    function initBackgroundPoller() {
        setInterval(async () => {
            if (!state.capturedModelUrl) {
                // Quick pass only — the deep window-property walk is reserved
                // for an explicit user-triggered scan (see comprehensiveSearch).
                await comprehensiveSearch(false);
            }
            updateBadge();
        }, CONFIG.POLL_INTERVAL);

        log('INIT', 'Background poller started');
    }

    // ============================================================
    //  12. MUTATION OBSERVER (DOM Change Detection)
    // ============================================================
    function initMutationObserver() {
        // Wait for body
        const waitForBody = setInterval(() => {
            if (!document.body) return;
            clearInterval(waitForBody);

            const observer = new MutationObserver((mutations) => {
                // Only scan DOM periodically, not on every mutation
                if (!state.capturedModelUrl && Date.now() % 5000 < 100) {
                    searchDOM();
                }
            });

            observer.observe(document.body, {
                childList: true,
                subtree: true,
                attributes: true,
                attributeFilter: ['src', 'data-src', 'data-url', 'data-model']
            });

            log('INIT', 'MutationObserver active');
        }, 500);
    }

    // ============================================================
    //  13. INITIALIZATION
    // ============================================================
    function initScript() {
        log('INIT', 'Tripo3D Model Downloader V10.0 starting...');

        // Add UI button once DOM is ready
        if (document.body) {
            addButton();
        } else {
            document.addEventListener('DOMContentLoaded', addButton);
        }

        // Initialize all monitors
        initPerformanceObserver();
        initRouteWatcher();
        initBackgroundPoller();
        initMutationObserver();

        log('INIT', 'All systems initialized. Waiting for model URL capture...');
    }

    // Start!
    initScript();

    // ============================================================
    //  BUNDLED LOCAL CONVERTER
    //  Generated by build.mjs (esbuild) — do not edit by hand.
    //  Provides `TripoConverter.convertGlb(arrayBuffer, format, opts)`.
    //  Formats: stl, obj, fbx, 3mf, gltf.
    // ============================================================
    var TripoConverter=(()=>{var Vi=Object.defineProperty;var Ju=Object.getOwnPropertyDescriptor;var Zu=Object.getOwnPropertyNames;var $u=Object.prototype.hasOwnProperty;var Qu=(a,e,t)=>e in a?Vi(a,e,{enumerable:!0,configurable:!0,writable:!0,value:t}):a[e]=t;var eh=(a,e)=>{for(var t in e)Vi(a,t,{get:e[t],enumerable:!0})},th=(a,e,t,n)=>{if(e&&typeof e=="object"||typeof e=="function")for(let i of Zu(e))!$u.call(a,i)&&i!==t&&Vi(a,i,{get:()=>e[i],enumerable:!(n=Ju(e,i))||n.enumerable});return a};var nh=a=>th(Vi({},"__esModule",{value:!0}),a);var ue=(a,e,t)=>Qu(a,typeof e!="symbol"?e+"":e,t);var y0={};eh(y0,{FORMATS:()=>_0,convertGlb:()=>b0,parseGlb:()=>ju,sceneStats:()=>Yn});var Kc=1;var Yc=3,Si=0,jc=1,Mi=2;var Jc=1;var Zc=100;var $c=204,Qc=205;var Ir=0,Pr=1,Lr=2,xs=3,Dr=4,Nr=5,Fr=6,Ur=7,Zr=0,el=1,tl=2;var $r=1,Qr=2,ea=3,ta=4,na=5,ia=6,sa=7,Or="attached",nl="detached",ra=300,il=301,aa=302;var sl=306,_t=1e3,xt=1001,nn=1002,zt=1003,Ai=1004;var Ti=1005;var Xt=1006,wi=1007;var hn=1008;var oa=1009;var Ds=1015;var Ei=1023;var rl=1028;var yt=2300,vt=2301,ds=2302,Br=2303,kr=2400,zr=2401,Vr=2402,al=2500;var ca=0,Ri=1,Wn=2;var ol=0;var Ci="",ce="srgb",Be="srgb-linear",Gr="linear",ps="srgb";var ms=7680;var cl=519;var la=35044;var kt=2e3,ai=2001;function ih(a){for(let e=a.length-1;e>=0;--e)if(a[e]>=65535)return!0;return!1}function sh(a){return ArrayBuffer.isView(a)&&!(a instanceof DataView)}function bs(a){return document.createElementNS("http://www.w3.org/1999/xhtml",a)}var uc={},Pn=null;function Hr(...a){let e="THREE."+a.shift();Pn?Pn("log",e,...a):console.log(e,...a)}function ll(a){let e=a[0];if(typeof e=="string"&&e.startsWith("TSL:")){let t=a[1];t&&t.isStackTrace?a[0]+=" "+t.getLocation():a[1]='Stack trace not available. Enable "THREE.Node.captureStackTrace" to capture stack traces.'}return a}function ne(...a){a=ll(a);let e="THREE."+a.shift();if(Pn)Pn("warn",e,...a);else{let t=a[0];t&&t.isStackTrace?console.warn(t.getError(e)):console.warn(e,...a)}}function oe(...a){a=ll(a);let e="THREE."+a.shift();if(Pn)Pn("error",e,...a);else{let t=a[0];t&&t.isStackTrace?console.error(t.getError(e)):console.error(e,...a)}}function Cn(...a){let e=a.join(" ");e in uc||(uc[e]=!0,ne(...a))}var rh={[Ir]:Pr,[Lr]:Fr,[Dr]:Ur,[xs]:Nr,[Pr]:Ir,[Fr]:Lr,[Ur]:Dr,[Nr]:xs},Vt=class{addEventListener(e,t){this._listeners===void 0&&(this._listeners={});let n=this._listeners;n[e]===void 0&&(n[e]=[]),n[e].indexOf(t)===-1&&n[e].push(t)}hasEventListener(e,t){let n=this._listeners;return n===void 0?!1:n[e]!==void 0&&n[e].indexOf(t)!==-1}removeEventListener(e,t){let n=this._listeners;if(n===void 0)return;let i=n[e];if(i!==void 0){let s=i.indexOf(t);s!==-1&&i.splice(s,1)}}dispatchEvent(e){let t=this._listeners;if(t===void 0)return;let n=t[e.type];if(n!==void 0){e.target=this;let i=n.slice(0);for(let s=0,r=i.length;s<r;s++)i[s].call(this,e);e.target=null}}},ve=["00","01","02","03","04","05","06","07","08","09","0a","0b","0c","0d","0e","0f","10","11","12","13","14","15","16","17","18","19","1a","1b","1c","1d","1e","1f","20","21","22","23","24","25","26","27","28","29","2a","2b","2c","2d","2e","2f","30","31","32","33","34","35","36","37","38","39","3a","3b","3c","3d","3e","3f","40","41","42","43","44","45","46","47","48","49","4a","4b","4c","4d","4e","4f","50","51","52","53","54","55","56","57","58","59","5a","5b","5c","5d","5e","5f","60","61","62","63","64","65","66","67","68","69","6a","6b","6c","6d","6e","6f","70","71","72","73","74","75","76","77","78","79","7a","7b","7c","7d","7e","7f","80","81","82","83","84","85","86","87","88","89","8a","8b","8c","8d","8e","8f","90","91","92","93","94","95","96","97","98","99","9a","9b","9c","9d","9e","9f","a0","a1","a2","a3","a4","a5","a6","a7","a8","a9","aa","ab","ac","ad","ae","af","b0","b1","b2","b3","b4","b5","b6","b7","b8","b9","ba","bb","bc","bd","be","bf","c0","c1","c2","c3","c4","c5","c6","c7","c8","c9","ca","cb","cc","cd","ce","cf","d0","d1","d2","d3","d4","d5","d6","d7","d8","d9","da","db","dc","dd","de","df","e0","e1","e2","e3","e4","e5","e6","e7","e8","e9","ea","eb","ec","ed","ee","ef","f0","f1","f2","f3","f4","f5","f6","f7","f8","f9","fa","fb","fc","fd","fe","ff"],hc=1234567,si=Math.PI/180,Ln=180/Math.PI;function Ze(){let a=Math.random()*4294967295|0,e=Math.random()*4294967295|0,t=Math.random()*4294967295|0,n=Math.random()*4294967295|0;return(ve[a&255]+ve[a>>8&255]+ve[a>>16&255]+ve[a>>24&255]+"-"+ve[e&255]+ve[e>>8&255]+"-"+ve[e>>16&15|64]+ve[e>>24&255]+"-"+ve[t&63|128]+ve[t>>8&255]+"-"+ve[t>>16&255]+ve[t>>24&255]+ve[n&255]+ve[n>>8&255]+ve[n>>16&255]+ve[n>>24&255]).toLowerCase()}function q(a,e,t){return Math.max(e,Math.min(t,a))}function ua(a,e){return(a%e+e)%e}function ah(a,e,t,n,i){return n+(a-e)*(i-n)/(t-e)}function oh(a,e,t){return a!==e?(t-a)/(e-a):0}function ri(a,e,t){return(1-t)*a+t*e}function ch(a,e,t,n){return ri(a,e,1-Math.exp(-t*n))}function lh(a,e=1){return e-Math.abs(ua(a,e*2)-e)}function uh(a,e,t){return a<=e?0:a>=t?1:(a=(a-e)/(t-e),a*a*(3-2*a))}function hh(a,e,t){return a<=e?0:a>=t?1:(a=(a-e)/(t-e),a*a*a*(a*(a*6-15)+10))}function fh(a,e){return a+Math.floor(Math.random()*(e-a+1))}function dh(a,e){return a+Math.random()*(e-a)}function ph(a){return a*(.5-Math.random())}function mh(a){a!==void 0&&(hc=a);let e=hc+=1831565813;return e=Math.imul(e^e>>>15,e|1),e^=e+Math.imul(e^e>>>7,e|61),((e^e>>>14)>>>0)/4294967296}function gh(a){return a*si}function xh(a){return a*Ln}function bh(a){return a>0&&Number.isInteger(a)&&2**Math.round(Math.log2(a))===a}function _h(a){return Math.pow(2,Math.ceil(Math.log(a)/Math.LN2))}function yh(a){return Math.pow(2,Math.floor(Math.log(a)/Math.LN2))}function vh(a,e,t,n,i){let s=Math.cos,r=Math.sin,o=s(t/2),c=r(t/2),l=s((e+n)/2),u=r((e+n)/2),h=s((e-n)/2),f=r((e-n)/2),d=s((n-e)/2),p=r((n-e)/2);switch(i){case"XYX":a.set(o*u,c*h,c*f,o*l);break;case"YZY":a.set(c*f,o*u,c*h,o*l);break;case"ZXZ":a.set(c*h,c*f,o*u,o*l);break;case"XZX":a.set(o*u,c*p,c*d,o*l);break;case"YXY":a.set(c*d,o*u,c*p,o*l);break;case"ZYZ":a.set(c*p,c*d,o*u,o*l);break;default:ne("MathUtils: .setQuaternionFromProperEuler() encountered an unknown order: "+i)}}function Je(a,e){switch(e.constructor){case Float32Array:return a;case Uint32Array:return a/4294967295;case Uint16Array:return a/65535;case Uint8Array:case Uint8ClampedArray:return a/255;case Int32Array:return Math.max(a/2147483647,-1);case Int16Array:return Math.max(a/32767,-1);case Int8Array:return Math.max(a/127,-1);default:throw new Error("THREE.MathUtils: Invalid component type.")}}function te(a,e){switch(e.constructor){case Float32Array:return a;case Uint32Array:return Math.round(a*4294967295);case Uint16Array:return Math.round(a*65535);case Uint8Array:case Uint8ClampedArray:return Math.round(a*255);case Int32Array:return Math.round(a*2147483647);case Int16Array:return Math.round(a*32767);case Int8Array:return Math.round(a*127);default:throw new Error("THREE.MathUtils: Invalid component type.")}}var fn={DEG2RAD:si,RAD2DEG:Ln,generateUUID:Ze,clamp:q,euclideanModulo:ua,mapLinear:ah,inverseLerp:oh,lerp:ri,damp:ch,pingpong:lh,smoothstep:uh,smootherstep:hh,randInt:fh,randFloat:dh,randFloatSpread:ph,seededRandom:mh,degToRad:gh,radToDeg:xh,isPowerOfTwo:bh,ceilPowerOfTwo:_h,floorPowerOfTwo:yh,setQuaternionFromProperEuler:vh,normalize:te,denormalize:Je},da=class da{constructor(e=0,t=0){this.x=e,this.y=t}get width(){return this.x}set width(e){this.x=e}get height(){return this.y}set height(e){this.y=e}set(e,t){return this.x=e,this.y=t,this}setScalar(e){return this.x=e,this.y=e,this}setX(e){return this.x=e,this}setY(e){return this.y=e,this}setComponent(e,t){switch(e){case 0:this.x=t;break;case 1:this.y=t;break;default:throw new Error("THREE.Vector2: index is out of range: "+e)}return this}getComponent(e){switch(e){case 0:return this.x;case 1:return this.y;default:throw new Error("THREE.Vector2: index is out of range: "+e)}}clone(){return new this.constructor(this.x,this.y)}copy(e){return this.x=e.x,this.y=e.y,this}add(e){return this.x+=e.x,this.y+=e.y,this}addScalar(e){return this.x+=e,this.y+=e,this}addVectors(e,t){return this.x=e.x+t.x,this.y=e.y+t.y,this}addScaledVector(e,t){return this.x+=e.x*t,this.y+=e.y*t,this}sub(e){return this.x-=e.x,this.y-=e.y,this}subScalar(e){return this.x-=e,this.y-=e,this}subVectors(e,t){return this.x=e.x-t.x,this.y=e.y-t.y,this}multiply(e){return this.x*=e.x,this.y*=e.y,this}multiplyScalar(e){return this.x*=e,this.y*=e,this}divide(e){return this.x/=e.x,this.y/=e.y,this}divideScalar(e){return this.multiplyScalar(1/e)}applyMatrix3(e){let t=this.x,n=this.y,i=e.elements;return this.x=i[0]*t+i[3]*n+i[6],this.y=i[1]*t+i[4]*n+i[7],this}min(e){return this.x=Math.min(this.x,e.x),this.y=Math.min(this.y,e.y),this}max(e){return this.x=Math.max(this.x,e.x),this.y=Math.max(this.y,e.y),this}clamp(e,t){return this.x=q(this.x,e.x,t.x),this.y=q(this.y,e.y,t.y),this}clampScalar(e,t){return this.x=q(this.x,e,t),this.y=q(this.y,e,t),this}clampLength(e,t){let n=this.length();return this.divideScalar(n||1).multiplyScalar(q(n,e,t))}floor(){return this.x=Math.floor(this.x),this.y=Math.floor(this.y),this}ceil(){return this.x=Math.ceil(this.x),this.y=Math.ceil(this.y),this}round(){return this.x=Math.round(this.x),this.y=Math.round(this.y),this}roundToZero(){return this.x=Math.trunc(this.x),this.y=Math.trunc(this.y),this}negate(){return this.x=-this.x,this.y=-this.y,this}dot(e){return this.x*e.x+this.y*e.y}cross(e){return this.x*e.y-this.y*e.x}lengthSq(){return this.x*this.x+this.y*this.y}length(){return Math.sqrt(this.x*this.x+this.y*this.y)}manhattanLength(){return Math.abs(this.x)+Math.abs(this.y)}normalize(){return this.divideScalar(this.length()||1)}angle(){return Math.atan2(-this.y,-this.x)+Math.PI}angleTo(e){let t=Math.sqrt(this.lengthSq()*e.lengthSq());if(t===0)return Math.PI/2;let n=this.dot(e)/t;return Math.acos(q(n,-1,1))}distanceTo(e){return Math.sqrt(this.distanceToSquared(e))}distanceToSquared(e){let t=this.x-e.x,n=this.y-e.y;return t*t+n*n}manhattanDistanceTo(e){return Math.abs(this.x-e.x)+Math.abs(this.y-e.y)}setLength(e){return this.normalize().multiplyScalar(e)}lerp(e,t){return this.x+=(e.x-this.x)*t,this.y+=(e.y-this.y)*t,this}lerpVectors(e,t,n){return this.x=e.x+(t.x-e.x)*n,this.y=e.y+(t.y-e.y)*n,this}equals(e){return e.x===this.x&&e.y===this.y}fromArray(e,t=0){return this.x=e[t],this.y=e[t+1],this}toArray(e=[],t=0){return e[t]=this.x,e[t+1]=this.y,e}fromBufferAttribute(e,t){return this.x=e.getX(t),this.y=e.getY(t),this}rotateAround(e,t){let n=Math.cos(t),i=Math.sin(t),s=this.x-e.x,r=this.y-e.y;return this.x=s*n-r*i+e.x,this.y=s*i+r*n+e.y,this}random(){return this.x=Math.random(),this.y=Math.random(),this}*[Symbol.iterator](){yield this.x,yield this.y}};da.prototype.isVector2=!0;var $=da,pe=class{constructor(e=0,t=0,n=0,i=1){this.isQuaternion=!0,this._x=e,this._y=t,this._z=n,this._w=i}static slerpFlat(e,t,n,i,s,r,o){let c=n[i+0],l=n[i+1],u=n[i+2],h=n[i+3],f=s[r+0],d=s[r+1],p=s[r+2],m=s[r+3];if(h!==m||c!==f||l!==d||u!==p){let b=c*f+l*d+u*p+h*m;b<0&&(f=-f,d=-d,p=-p,m=-m,b=-b);let x=1-o;if(b<.9995){let v=Math.acos(b),S=Math.sin(v);x=Math.sin(x*v)/S,o=Math.sin(o*v)/S,c=c*x+f*o,l=l*x+d*o,u=u*x+p*o,h=h*x+m*o}else{c=c*x+f*o,l=l*x+d*o,u=u*x+p*o,h=h*x+m*o;let v=1/Math.sqrt(c*c+l*l+u*u+h*h);c*=v,l*=v,u*=v,h*=v}}e[t]=c,e[t+1]=l,e[t+2]=u,e[t+3]=h}static multiplyQuaternionsFlat(e,t,n,i,s,r){let o=n[i],c=n[i+1],l=n[i+2],u=n[i+3],h=s[r],f=s[r+1],d=s[r+2],p=s[r+3];return e[t]=o*p+u*h+c*d-l*f,e[t+1]=c*p+u*f+l*h-o*d,e[t+2]=l*p+u*d+o*f-c*h,e[t+3]=u*p-o*h-c*f-l*d,e}get x(){return this._x}set x(e){this._x=e,this._onChangeCallback()}get y(){return this._y}set y(e){this._y=e,this._onChangeCallback()}get z(){return this._z}set z(e){this._z=e,this._onChangeCallback()}get w(){return this._w}set w(e){this._w=e,this._onChangeCallback()}set(e,t,n,i){return this._x=e,this._y=t,this._z=n,this._w=i,this._onChangeCallback(),this}clone(){return new this.constructor(this._x,this._y,this._z,this._w)}copy(e){return this._x=e.x,this._y=e.y,this._z=e.z,this._w=e.w,this._onChangeCallback(),this}setFromEuler(e,t=!0){let n=e._x,i=e._y,s=e._z,r=e._order,o=Math.cos,c=Math.sin,l=o(n/2),u=o(i/2),h=o(s/2),f=c(n/2),d=c(i/2),p=c(s/2);switch(r){case"XYZ":this._x=f*u*h+l*d*p,this._y=l*d*h-f*u*p,this._z=l*u*p+f*d*h,this._w=l*u*h-f*d*p;break;case"YXZ":this._x=f*u*h+l*d*p,this._y=l*d*h-f*u*p,this._z=l*u*p-f*d*h,this._w=l*u*h+f*d*p;break;case"ZXY":this._x=f*u*h-l*d*p,this._y=l*d*h+f*u*p,this._z=l*u*p+f*d*h,this._w=l*u*h-f*d*p;break;case"ZYX":this._x=f*u*h-l*d*p,this._y=l*d*h+f*u*p,this._z=l*u*p-f*d*h,this._w=l*u*h+f*d*p;break;case"YZX":this._x=f*u*h+l*d*p,this._y=l*d*h+f*u*p,this._z=l*u*p-f*d*h,this._w=l*u*h-f*d*p;break;case"XZY":this._x=f*u*h-l*d*p,this._y=l*d*h-f*u*p,this._z=l*u*p+f*d*h,this._w=l*u*h+f*d*p;break;default:ne("Quaternion: .setFromEuler() encountered an unknown order: "+r)}return t===!0&&this._onChangeCallback(),this}setFromAxisAngle(e,t){let n=t/2,i=Math.sin(n);return this._x=e.x*i,this._y=e.y*i,this._z=e.z*i,this._w=Math.cos(n),this._onChangeCallback(),this}setFromRotationMatrix(e){let t=e.elements,n=t[0],i=t[4],s=t[8],r=t[1],o=t[5],c=t[9],l=t[2],u=t[6],h=t[10],f=n+o+h;if(f>0){let d=.5/Math.sqrt(f+1);this._w=.25/d,this._x=(u-c)*d,this._y=(s-l)*d,this._z=(r-i)*d}else if(n>o&&n>h){let d=2*Math.sqrt(1+n-o-h);this._w=(u-c)/d,this._x=.25*d,this._y=(i+r)/d,this._z=(s+l)/d}else if(o>h){let d=2*Math.sqrt(1+o-n-h);this._w=(s-l)/d,this._x=(i+r)/d,this._y=.25*d,this._z=(c+u)/d}else{let d=2*Math.sqrt(1+h-n-o);this._w=(r-i)/d,this._x=(s+l)/d,this._y=(c+u)/d,this._z=.25*d}return this._onChangeCallback(),this}setFromUnitVectors(e,t){let n=e.dot(t)+1;return n<1e-8?(n=0,Math.abs(e.x)>Math.abs(e.z)?(this._x=-e.y,this._y=e.x,this._z=0,this._w=n):(this._x=0,this._y=-e.z,this._z=e.y,this._w=n)):(this._x=e.y*t.z-e.z*t.y,this._y=e.z*t.x-e.x*t.z,this._z=e.x*t.y-e.y*t.x,this._w=n),this.normalize()}angleTo(e){return 2*Math.acos(Math.abs(q(this.dot(e),-1,1)))}rotateTowards(e,t){let n=this.angleTo(e);if(n===0)return this;let i=Math.min(1,t/n);return this.slerp(e,i),this}identity(){return this.set(0,0,0,1)}invert(){return this.conjugate()}conjugate(){return this._x*=-1,this._y*=-1,this._z*=-1,this._onChangeCallback(),this}dot(e){return this._x*e._x+this._y*e._y+this._z*e._z+this._w*e._w}lengthSq(){return this._x*this._x+this._y*this._y+this._z*this._z+this._w*this._w}length(){return Math.sqrt(this._x*this._x+this._y*this._y+this._z*this._z+this._w*this._w)}normalize(){let e=this.length();return e===0?(this._x=0,this._y=0,this._z=0,this._w=1):(e=1/e,this._x=this._x*e,this._y=this._y*e,this._z=this._z*e,this._w=this._w*e),this._onChangeCallback(),this}multiply(e){return this.multiplyQuaternions(this,e)}premultiply(e){return this.multiplyQuaternions(e,this)}multiplyQuaternions(e,t){let n=e._x,i=e._y,s=e._z,r=e._w,o=t._x,c=t._y,l=t._z,u=t._w;return this._x=n*u+r*o+i*l-s*c,this._y=i*u+r*c+s*o-n*l,this._z=s*u+r*l+n*c-i*o,this._w=r*u-n*o-i*c-s*l,this._onChangeCallback(),this}slerp(e,t){let n=e._x,i=e._y,s=e._z,r=e._w,o=this.dot(e);o<0&&(n=-n,i=-i,s=-s,r=-r,o=-o);let c=1-t;if(o<.9995){let l=Math.acos(o),u=Math.sin(l);c=Math.sin(c*l)/u,t=Math.sin(t*l)/u,this._x=this._x*c+n*t,this._y=this._y*c+i*t,this._z=this._z*c+s*t,this._w=this._w*c+r*t,this._onChangeCallback()}else this._x=this._x*c+n*t,this._y=this._y*c+i*t,this._z=this._z*c+s*t,this._w=this._w*c+r*t,this.normalize();return this}slerpQuaternions(e,t,n){return this.copy(e).slerp(t,n)}random(){let e=2*Math.PI*Math.random(),t=2*Math.PI*Math.random(),n=Math.random(),i=Math.sqrt(1-n),s=Math.sqrt(n);return this.set(i*Math.sin(e),i*Math.cos(e),s*Math.sin(t),s*Math.cos(t))}equals(e){return e._x===this._x&&e._y===this._y&&e._z===this._z&&e._w===this._w}fromArray(e,t=0){return this._x=e[t],this._y=e[t+1],this._z=e[t+2],this._w=e[t+3],this._onChangeCallback(),this}toArray(e=[],t=0){return e[t]=this._x,e[t+1]=this._y,e[t+2]=this._z,e[t+3]=this._w,e}fromBufferAttribute(e,t){return this._x=e.getX(t),this._y=e.getY(t),this._z=e.getZ(t),this._w=e.getW(t),this._onChangeCallback(),this}toJSON(){return this.toArray()}_onChange(e){return this._onChangeCallback=e,this}_onChangeCallback(){}*[Symbol.iterator](){yield this._x,yield this._y,yield this._z,yield this._w}},pa=class pa{constructor(e=0,t=0,n=0){this.x=e,this.y=t,this.z=n}set(e,t,n){return n===void 0&&(n=this.z),this.x=e,this.y=t,this.z=n,this}setScalar(e){return this.x=e,this.y=e,this.z=e,this}setX(e){return this.x=e,this}setY(e){return this.y=e,this}setZ(e){return this.z=e,this}setComponent(e,t){switch(e){case 0:this.x=t;break;case 1:this.y=t;break;case 2:this.z=t;break;default:throw new Error("THREE.Vector3: index is out of range: "+e)}return this}getComponent(e){switch(e){case 0:return this.x;case 1:return this.y;case 2:return this.z;default:throw new Error("THREE.Vector3: index is out of range: "+e)}}clone(){return new this.constructor(this.x,this.y,this.z)}copy(e){return this.x=e.x,this.y=e.y,this.z=e.z,this}add(e){return this.x+=e.x,this.y+=e.y,this.z+=e.z,this}addScalar(e){return this.x+=e,this.y+=e,this.z+=e,this}addVectors(e,t){return this.x=e.x+t.x,this.y=e.y+t.y,this.z=e.z+t.z,this}addScaledVector(e,t){return this.x+=e.x*t,this.y+=e.y*t,this.z+=e.z*t,this}sub(e){return this.x-=e.x,this.y-=e.y,this.z-=e.z,this}subScalar(e){return this.x-=e,this.y-=e,this.z-=e,this}subVectors(e,t){return this.x=e.x-t.x,this.y=e.y-t.y,this.z=e.z-t.z,this}multiply(e){return this.x*=e.x,this.y*=e.y,this.z*=e.z,this}multiplyScalar(e){return this.x*=e,this.y*=e,this.z*=e,this}multiplyVectors(e,t){return this.x=e.x*t.x,this.y=e.y*t.y,this.z=e.z*t.z,this}applyEuler(e){return this.applyQuaternion(fc.setFromEuler(e))}applyAxisAngle(e,t){return this.applyQuaternion(fc.setFromAxisAngle(e,t))}applyMatrix3(e){let t=this.x,n=this.y,i=this.z,s=e.elements;return this.x=s[0]*t+s[3]*n+s[6]*i,this.y=s[1]*t+s[4]*n+s[7]*i,this.z=s[2]*t+s[5]*n+s[8]*i,this}applyNormalMatrix(e){return this.applyMatrix3(e).normalize()}applyMatrix4(e){let t=this.x,n=this.y,i=this.z,s=e.elements,r=1/(s[3]*t+s[7]*n+s[11]*i+s[15]);return this.x=(s[0]*t+s[4]*n+s[8]*i+s[12])*r,this.y=(s[1]*t+s[5]*n+s[9]*i+s[13])*r,this.z=(s[2]*t+s[6]*n+s[10]*i+s[14])*r,this}applyQuaternion(e){let t=this.x,n=this.y,i=this.z,s=e.x,r=e.y,o=e.z,c=e.w,l=2*(r*i-o*n),u=2*(o*t-s*i),h=2*(s*n-r*t);return this.x=t+c*l+r*h-o*u,this.y=n+c*u+o*l-s*h,this.z=i+c*h+s*u-r*l,this}project(e){return this.applyMatrix4(e.matrixWorldInverse).applyMatrix4(e.projectionMatrix)}unproject(e){return this.applyMatrix4(e.projectionMatrixInverse).applyMatrix4(e.matrixWorld)}transformDirection(e){let t=this.x,n=this.y,i=this.z,s=e.elements;return this.x=s[0]*t+s[4]*n+s[8]*i,this.y=s[1]*t+s[5]*n+s[9]*i,this.z=s[2]*t+s[6]*n+s[10]*i,this.normalize()}divide(e){return this.x/=e.x,this.y/=e.y,this.z/=e.z,this}divideScalar(e){return this.multiplyScalar(1/e)}min(e){return this.x=Math.min(this.x,e.x),this.y=Math.min(this.y,e.y),this.z=Math.min(this.z,e.z),this}max(e){return this.x=Math.max(this.x,e.x),this.y=Math.max(this.y,e.y),this.z=Math.max(this.z,e.z),this}clamp(e,t){return this.x=q(this.x,e.x,t.x),this.y=q(this.y,e.y,t.y),this.z=q(this.z,e.z,t.z),this}clampScalar(e,t){return this.x=q(this.x,e,t),this.y=q(this.y,e,t),this.z=q(this.z,e,t),this}clampLength(e,t){let n=this.length();return this.divideScalar(n||1).multiplyScalar(q(n,e,t))}floor(){return this.x=Math.floor(this.x),this.y=Math.floor(this.y),this.z=Math.floor(this.z),this}ceil(){return this.x=Math.ceil(this.x),this.y=Math.ceil(this.y),this.z=Math.ceil(this.z),this}round(){return this.x=Math.round(this.x),this.y=Math.round(this.y),this.z=Math.round(this.z),this}roundToZero(){return this.x=Math.trunc(this.x),this.y=Math.trunc(this.y),this.z=Math.trunc(this.z),this}negate(){return this.x=-this.x,this.y=-this.y,this.z=-this.z,this}dot(e){return this.x*e.x+this.y*e.y+this.z*e.z}lengthSq(){return this.x*this.x+this.y*this.y+this.z*this.z}length(){return Math.sqrt(this.x*this.x+this.y*this.y+this.z*this.z)}manhattanLength(){return Math.abs(this.x)+Math.abs(this.y)+Math.abs(this.z)}normalize(){return this.divideScalar(this.length()||1)}setLength(e){return this.normalize().multiplyScalar(e)}lerp(e,t){return this.x+=(e.x-this.x)*t,this.y+=(e.y-this.y)*t,this.z+=(e.z-this.z)*t,this}lerpVectors(e,t,n){return this.x=e.x+(t.x-e.x)*n,this.y=e.y+(t.y-e.y)*n,this.z=e.z+(t.z-e.z)*n,this}cross(e){return this.crossVectors(this,e)}crossVectors(e,t){let n=e.x,i=e.y,s=e.z,r=t.x,o=t.y,c=t.z;return this.x=i*c-s*o,this.y=s*r-n*c,this.z=n*o-i*r,this}projectOnVector(e){let t=e.lengthSq();if(t===0)return this.set(0,0,0);let n=e.dot(this)/t;return this.copy(e).multiplyScalar(n)}projectOnPlane(e){return ar.copy(this).projectOnVector(e),this.sub(ar)}reflect(e){return this.sub(ar.copy(e).multiplyScalar(2*this.dot(e)))}angleTo(e){let t=Math.sqrt(this.lengthSq()*e.lengthSq());if(t===0)return Math.PI/2;let n=this.dot(e)/t;return Math.acos(q(n,-1,1))}distanceTo(e){return Math.sqrt(this.distanceToSquared(e))}distanceToSquared(e){let t=this.x-e.x,n=this.y-e.y,i=this.z-e.z;return t*t+n*n+i*i}manhattanDistanceTo(e){return Math.abs(this.x-e.x)+Math.abs(this.y-e.y)+Math.abs(this.z-e.z)}setFromSpherical(e){return this.setFromSphericalCoords(e.radius,e.phi,e.theta)}setFromSphericalCoords(e,t,n){let i=Math.sin(t)*e;return this.x=i*Math.sin(n),this.y=Math.cos(t)*e,this.z=i*Math.cos(n),this}setFromCylindrical(e){return this.setFromCylindricalCoords(e.radius,e.theta,e.y)}setFromCylindricalCoords(e,t,n){return this.x=e*Math.sin(t),this.y=n,this.z=e*Math.cos(t),this}setFromMatrixPosition(e){let t=e.elements;return this.x=t[12],this.y=t[13],this.z=t[14],this}setFromMatrixScale(e){let t=this.setFromMatrixColumn(e,0).length(),n=this.setFromMatrixColumn(e,1).length(),i=this.setFromMatrixColumn(e,2).length();return this.x=t,this.y=n,this.z=i,this}setFromMatrixColumn(e,t){return this.fromArray(e.elements,t*4)}setFromMatrix3Column(e,t){return this.fromArray(e.elements,t*3)}setFromEuler(e){return this.x=e._x,this.y=e._y,this.z=e._z,this}setFromColor(e){return this.x=e.r,this.y=e.g,this.z=e.b,this}equals(e){return e.x===this.x&&e.y===this.y&&e.z===this.z}fromArray(e,t=0){return this.x=e[t],this.y=e[t+1],this.z=e[t+2],this}toArray(e=[],t=0){return e[t]=this.x,e[t+1]=this.y,e[t+2]=this.z,e}fromBufferAttribute(e,t){return this.x=e.getX(t),this.y=e.getY(t),this.z=e.getZ(t),this}random(){return this.x=Math.random(),this.y=Math.random(),this.z=Math.random(),this}randomDirection(){let e=Math.random()*Math.PI*2,t=Math.random()*2-1,n=Math.sqrt(1-t*t);return this.x=n*Math.cos(e),this.y=t,this.z=n*Math.sin(e),this}*[Symbol.iterator](){yield this.x,yield this.y,yield this.z}};pa.prototype.isVector3=!0;var E=pa,ar=new E,fc=new pe,ma=class ma{constructor(e,t,n,i,s,r,o,c,l){this.elements=[1,0,0,0,1,0,0,0,1],e!==void 0&&this.set(e,t,n,i,s,r,o,c,l)}set(e,t,n,i,s,r,o,c,l){let u=this.elements;return u[0]=e,u[1]=i,u[2]=o,u[3]=t,u[4]=s,u[5]=c,u[6]=n,u[7]=r,u[8]=l,this}identity(){return this.set(1,0,0,0,1,0,0,0,1),this}copy(e){let t=this.elements,n=e.elements;return t[0]=n[0],t[1]=n[1],t[2]=n[2],t[3]=n[3],t[4]=n[4],t[5]=n[5],t[6]=n[6],t[7]=n[7],t[8]=n[8],this}extractBasis(e,t,n){return e.setFromMatrix3Column(this,0),t.setFromMatrix3Column(this,1),n.setFromMatrix3Column(this,2),this}setFromMatrix4(e){let t=e.elements;return this.set(t[0],t[4],t[8],t[1],t[5],t[9],t[2],t[6],t[10]),this}multiply(e){return this.multiplyMatrices(this,e)}premultiply(e){return this.multiplyMatrices(e,this)}multiplyMatrices(e,t){let n=e.elements,i=t.elements,s=this.elements,r=n[0],o=n[3],c=n[6],l=n[1],u=n[4],h=n[7],f=n[2],d=n[5],p=n[8],m=i[0],b=i[3],x=i[6],v=i[1],S=i[4],y=i[7],T=i[2],M=i[5],A=i[8];return s[0]=r*m+o*v+c*T,s[3]=r*b+o*S+c*M,s[6]=r*x+o*y+c*A,s[1]=l*m+u*v+h*T,s[4]=l*b+u*S+h*M,s[7]=l*x+u*y+h*A,s[2]=f*m+d*v+p*T,s[5]=f*b+d*S+p*M,s[8]=f*x+d*y+p*A,this}multiplyScalar(e){let t=this.elements;return t[0]*=e,t[3]*=e,t[6]*=e,t[1]*=e,t[4]*=e,t[7]*=e,t[2]*=e,t[5]*=e,t[8]*=e,this}determinant(){let e=this.elements,t=e[0],n=e[1],i=e[2],s=e[3],r=e[4],o=e[5],c=e[6],l=e[7],u=e[8];return t*r*u-t*o*l-n*s*u+n*o*c+i*s*l-i*r*c}invert(){let e=this.elements,t=e[0],n=e[1],i=e[2],s=e[3],r=e[4],o=e[5],c=e[6],l=e[7],u=e[8],h=u*r-o*l,f=o*c-u*s,d=l*s-r*c,p=t*h+n*f+i*d;if(p===0)return this.set(0,0,0,0,0,0,0,0,0);let m=1/p;return e[0]=h*m,e[1]=(i*l-u*n)*m,e[2]=(o*n-i*r)*m,e[3]=f*m,e[4]=(u*t-i*c)*m,e[5]=(i*s-o*t)*m,e[6]=d*m,e[7]=(n*c-l*t)*m,e[8]=(r*t-n*s)*m,this}transpose(){let e,t=this.elements;return e=t[1],t[1]=t[3],t[3]=e,e=t[2],t[2]=t[6],t[6]=e,e=t[5],t[5]=t[7],t[7]=e,this}getNormalMatrix(e){return this.setFromMatrix4(e).invert().transpose()}transposeIntoArray(e){let t=this.elements;return e[0]=t[0],e[1]=t[3],e[2]=t[6],e[3]=t[1],e[4]=t[4],e[5]=t[7],e[6]=t[2],e[7]=t[5],e[8]=t[8],this}setUvTransform(e,t,n,i,s,r,o){let c=Math.cos(s),l=Math.sin(s);return this.set(n*c,n*l,-n*(c*r+l*o)+r+e,-i*l,i*c,-i*(-l*r+c*o)+o+t,0,0,1),this}scale(e,t){return Cn("Matrix3: .scale() is deprecated. Use .makeScale() instead."),this.premultiply(or.makeScale(e,t)),this}rotate(e){return Cn("Matrix3: .rotate() is deprecated. Use .makeRotation() instead."),this.premultiply(or.makeRotation(-e)),this}translate(e,t){return Cn("Matrix3: .translate() is deprecated. Use .makeTranslation() instead."),this.premultiply(or.makeTranslation(e,t)),this}makeTranslation(e,t){return e.isVector2?this.set(1,0,e.x,0,1,e.y,0,0,1):this.set(1,0,e,0,1,t,0,0,1),this}makeRotation(e){let t=Math.cos(e),n=Math.sin(e);return this.set(t,-n,0,n,t,0,0,0,1),this}makeScale(e,t){return this.set(e,0,0,0,t,0,0,0,1),this}equals(e){let t=this.elements,n=e.elements;for(let i=0;i<9;i++)if(t[i]!==n[i])return!1;return!0}fromArray(e,t=0){for(let n=0;n<9;n++)this.elements[n]=e[n+t];return this}toArray(e=[],t=0){let n=this.elements;return e[t]=n[0],e[t+1]=n[1],e[t+2]=n[2],e[t+3]=n[3],e[t+4]=n[4],e[t+5]=n[5],e[t+6]=n[6],e[t+7]=n[7],e[t+8]=n[8],e}clone(){return new this.constructor().fromArray(this.elements)}};ma.prototype.isMatrix3=!0;var G=ma,or=new G,dc=new G().set(.4123908,.3575843,.1804808,.212639,.7151687,.0721923,.0193308,.1191948,.9505322),pc=new G().set(3.2409699,-1.5373832,-.4986108,-.9692436,1.8759675,.0415551,.0556301,-.203977,1.0569715);function Sh(){let a={enabled:!0,workingColorSpace:Be,spaces:{},convert:function(i,s,r){return this.enabled===!1||s===r||!s||!r||(this.spaces[s].transfer===ps&&(i.r=bt(i.r),i.g=bt(i.g),i.b=bt(i.b)),this.spaces[s].primaries!==this.spaces[r].primaries&&(i.applyMatrix3(this.spaces[s].toXYZ),i.applyMatrix3(this.spaces[r].fromXYZ)),this.spaces[r].transfer===ps&&(i.r=In(i.r),i.g=In(i.g),i.b=In(i.b))),i},workingToColorSpace:function(i,s){return this.convert(i,this.workingColorSpace,s)},colorSpaceToWorking:function(i,s){return this.convert(i,s,this.workingColorSpace)},getPrimaries:function(i){return this.spaces[i].primaries},getTransfer:function(i){return i===Ci?Gr:this.spaces[i].transfer},getToneMappingMode:function(i){return this.spaces[i].outputColorSpaceConfig.toneMappingMode||"standard"},getLuminanceCoefficients:function(i,s=this.workingColorSpace){return i.fromArray(this.spaces[s].luminanceCoefficients)},define:function(i){Object.assign(this.spaces,i)},_getMatrix:function(i,s,r){return i.copy(this.spaces[s].toXYZ).multiply(this.spaces[r].fromXYZ)},_getDrawingBufferColorSpace:function(i){return this.spaces[i].outputColorSpaceConfig.drawingBufferColorSpace},_getUnpackColorSpace:function(i=this.workingColorSpace){return this.spaces[i].workingColorSpaceConfig.unpackColorSpace},fromWorkingColorSpace:function(i,s){return Cn("ColorManagement: .fromWorkingColorSpace() has been renamed to .workingToColorSpace()."),a.workingToColorSpace(i,s)},toWorkingColorSpace:function(i,s){return Cn("ColorManagement: .toWorkingColorSpace() has been renamed to .colorSpaceToWorking()."),a.colorSpaceToWorking(i,s)}},e=[.64,.33,.3,.6,.15,.06],t=[.2126,.7152,.0722],n=[.3127,.329];return a.define({[Be]:{primaries:e,whitePoint:n,transfer:Gr,toXYZ:dc,fromXYZ:pc,luminanceCoefficients:t,workingColorSpaceConfig:{unpackColorSpace:ce},outputColorSpaceConfig:{drawingBufferColorSpace:ce}},[ce]:{primaries:e,whitePoint:n,transfer:ps,toXYZ:dc,fromXYZ:pc,luminanceCoefficients:t,outputColorSpaceConfig:{drawingBufferColorSpace:ce}}}),a}var _e=Sh();function bt(a){return a<.04045?a*.0773993808:Math.pow(a*.9478672986+.0521327014,2.4)}function In(a){return a<.0031308?a*12.92:1.055*Math.pow(a,.41666)-.055}var xn,Dn=class{static getDataURL(e,t="image/png"){if(/^data:/i.test(e.src)||typeof HTMLCanvasElement>"u")return e.src;let n;if(e instanceof HTMLCanvasElement)n=e;else{xn===void 0&&(xn=bs("canvas")),xn.width=e.width,xn.height=e.height;let i=xn.getContext("2d");e instanceof ImageData?i.putImageData(e,0,0):i.drawImage(e,0,0,e.width,e.height),n=xn}return n.toDataURL(t)}static sRGBToLinear(e){if(typeof HTMLImageElement<"u"&&e instanceof HTMLImageElement||typeof HTMLCanvasElement<"u"&&e instanceof HTMLCanvasElement||typeof ImageBitmap<"u"&&e instanceof ImageBitmap){let t=bs("canvas");t.width=e.width,t.height=e.height;let n=t.getContext("2d");n.drawImage(e,0,0,e.width,e.height);let i=n.getImageData(0,0,e.width,e.height),s=i.data;for(let r=0;r<s.length;r++)s[r]=bt(s[r]/255)*255;return n.putImageData(i,0,0),t}else if(e.data){let t=e.data.slice(0);for(let n=0;n<t.length;n++)t instanceof Uint8Array||t instanceof Uint8ClampedArray?t[n]=Math.floor(bt(t[n]/255)*255):t[n]=bt(t[n]);return{data:t,width:e.width,height:e.height}}else return ne("ImageUtils.sRGBToLinear(): Unsupported image type. No color space conversion applied."),e}},Mh=0,sn=class{constructor(e=null){this.isTextureSource=!0,Object.defineProperty(this,"id",{value:Mh++}),this.uuid=Ze(),this.data=e,this.dataReady=!0,this.version=0}getSize(e){let t=this.data;return typeof HTMLVideoElement<"u"&&t instanceof HTMLVideoElement?e.set(t.videoWidth,t.videoHeight,0):typeof VideoFrame<"u"&&t instanceof VideoFrame?e.set(t.displayWidth,t.displayHeight,0):t!==null?e.set(t.width,t.height,t.depth||0):e.set(0,0,0),e}set needsUpdate(e){e===!0&&this.version++}toJSON(e){let t=e===void 0||typeof e=="string";if(!t&&e.images[this.uuid]!==void 0)return e.images[this.uuid];let n={uuid:this.uuid,url:""},i=this.data;if(i!==null){let s;if(Array.isArray(i)){s=[];for(let r=0,o=i.length;r<o;r++)i[r].isDataTexture?s.push(cr(i[r].image)):s.push(cr(i[r]))}else s=cr(i);n.url=s}return t||(e.images[this.uuid]=n),n}};function cr(a){return typeof HTMLImageElement<"u"&&a instanceof HTMLImageElement||typeof HTMLCanvasElement<"u"&&a instanceof HTMLCanvasElement||typeof ImageBitmap<"u"&&a instanceof ImageBitmap?Dn.getDataURL(a):a.data?{data:Array.from(a.data),width:a.width,height:a.height,type:a.data.constructor.name}:(ne("Texture: Unable to serialize Texture."),{})}var Ah=0,lr=new E,We=class a extends Vt{constructor(e=a.DEFAULT_IMAGE,t=a.DEFAULT_MAPPING,n=xt,i=xt,s=Xt,r=hn,o=Ei,c=oa,l=a.DEFAULT_ANISOTROPY,u=Ci){super(),this.isTexture=!0,Object.defineProperty(this,"id",{value:Ah++}),this.uuid=Ze(),this.name="",this.source=new sn(e),this.mipmaps=[],this.mapping=t,this.channel=0,this.wrapS=n,this.wrapT=i,this.magFilter=s,this.minFilter=r,this.anisotropy=l,this.format=o,this.internalFormat=null,this.type=c,this.offset=new $(0,0),this.repeat=new $(1,1),this.center=new $(0,0),this.rotation=0,this.matrixAutoUpdate=!0,this.matrix=new G,this.generateMipmaps=!0,this.premultiplyAlpha=!1,this.flipY=!0,this.unpackAlignment=4,this.colorSpace=u,this.userData={},this.updateRanges=[],this.version=0,this.onUpdate=null,this.renderTarget=null,this.isRenderTargetTexture=!1,this.isArrayTexture=!!(e&&e.depth&&e.depth>1),this.pmremVersion=0,this.normalized=!1}get width(){return this.source.getSize(lr).x}get height(){return this.source.getSize(lr).y}get depth(){return this.source.getSize(lr).z}get image(){return this.source.data}set image(e){this.source.data=e}updateMatrix(){this.matrix.setUvTransform(this.offset.x,this.offset.y,this.repeat.x,this.repeat.y,this.rotation,this.center.x,this.center.y)}addUpdateRange(e,t){this.updateRanges.push({start:e,count:t})}clearUpdateRanges(){this.updateRanges.length=0}clone(){return new this.constructor().copy(this)}copy(e){return this.name=e.name,this.source=e.source,this.mipmaps=e.mipmaps.slice(0),this.mapping=e.mapping,this.channel=e.channel,this.wrapS=e.wrapS,this.wrapT=e.wrapT,this.magFilter=e.magFilter,this.minFilter=e.minFilter,this.anisotropy=e.anisotropy,this.format=e.format,this.internalFormat=e.internalFormat,this.type=e.type,this.normalized=e.normalized,this.offset.copy(e.offset),this.repeat.copy(e.repeat),this.center.copy(e.center),this.rotation=e.rotation,this.matrixAutoUpdate=e.matrixAutoUpdate,this.matrix.copy(e.matrix),this.generateMipmaps=e.generateMipmaps,this.premultiplyAlpha=e.premultiplyAlpha,this.flipY=e.flipY,this.unpackAlignment=e.unpackAlignment,this.colorSpace=e.colorSpace,this.renderTarget=e.renderTarget,this.isRenderTargetTexture=e.isRenderTargetTexture,this.isArrayTexture=e.isArrayTexture,this.userData=JSON.parse(JSON.stringify(e.userData)),this.needsUpdate=!0,this}setValues(e){for(let t in e){let n=e[t];if(n===void 0){ne(`Texture.setValues(): parameter '${t}' has value of undefined.`);continue}let i=this[t];if(i===void 0){ne(`Texture.setValues(): property '${t}' does not exist.`);continue}i&&n&&i.isVector2&&n.isVector2||i&&n&&i.isVector3&&n.isVector3||i&&n&&i.isMatrix3&&n.isMatrix3?i.copy(n):this[t]=n}}toJSON(e){let t=e===void 0||typeof e=="string";if(!t&&e.textures[this.uuid]!==void 0)return e.textures[this.uuid];let n={metadata:{version:4.7,type:"Texture",generator:"Texture.toJSON"},uuid:this.uuid,name:this.name,image:this.source.toJSON(e).uuid,mapping:this.mapping,channel:this.channel,repeat:[this.repeat.x,this.repeat.y],offset:[this.offset.x,this.offset.y],center:[this.center.x,this.center.y],rotation:this.rotation,wrap:[this.wrapS,this.wrapT],format:this.format,internalFormat:this.internalFormat,type:this.type,normalized:this.normalized,colorSpace:this.colorSpace,minFilter:this.minFilter,magFilter:this.magFilter,anisotropy:this.anisotropy,flipY:this.flipY,generateMipmaps:this.generateMipmaps,premultiplyAlpha:this.premultiplyAlpha,unpackAlignment:this.unpackAlignment};return Object.keys(this.userData).length>0&&(n.userData=this.userData),t||(e.textures[this.uuid]=n),n}dispose(){this.dispatchEvent({type:"dispose"})}transformUv(e){if(this.mapping!==ra)return e;if(e.applyMatrix3(this.matrix),e.x<0||e.x>1)switch(this.wrapS){case _t:e.x=e.x-Math.floor(e.x);break;case xt:e.x=e.x<0?0:1;break;case nn:Math.abs(Math.floor(e.x)%2)===1?e.x=Math.ceil(e.x)-e.x:e.x=e.x-Math.floor(e.x);break}if(e.y<0||e.y>1)switch(this.wrapT){case _t:e.y=e.y-Math.floor(e.y);break;case xt:e.y=e.y<0?0:1;break;case nn:Math.abs(Math.floor(e.y)%2)===1?e.y=Math.ceil(e.y)-e.y:e.y=e.y-Math.floor(e.y);break}return this.flipY&&(e.y=1-e.y),e}set needsUpdate(e){e===!0&&(this.version++,this.source.needsUpdate=!0)}set needsPMREMUpdate(e){e===!0&&this.pmremVersion++}};We.DEFAULT_IMAGE=null;We.DEFAULT_MAPPING=ra;We.DEFAULT_ANISOTROPY=1;var ga=class ga{constructor(e=0,t=0,n=0,i=1){this.x=e,this.y=t,this.z=n,this.w=i}get width(){return this.z}set width(e){this.z=e}get height(){return this.w}set height(e){this.w=e}set(e,t,n,i){return this.x=e,this.y=t,this.z=n,this.w=i,this}setScalar(e){return this.x=e,this.y=e,this.z=e,this.w=e,this}setX(e){return this.x=e,this}setY(e){return this.y=e,this}setZ(e){return this.z=e,this}setW(e){return this.w=e,this}setComponent(e,t){switch(e){case 0:this.x=t;break;case 1:this.y=t;break;case 2:this.z=t;break;case 3:this.w=t;break;default:throw new Error("THREE.Vector4: index is out of range: "+e)}return this}getComponent(e){switch(e){case 0:return this.x;case 1:return this.y;case 2:return this.z;case 3:return this.w;default:throw new Error("THREE.Vector4: index is out of range: "+e)}}clone(){return new this.constructor(this.x,this.y,this.z,this.w)}copy(e){return this.x=e.x,this.y=e.y,this.z=e.z,this.w=e.w!==void 0?e.w:1,this}add(e){return this.x+=e.x,this.y+=e.y,this.z+=e.z,this.w+=e.w,this}addScalar(e){return this.x+=e,this.y+=e,this.z+=e,this.w+=e,this}addVectors(e,t){return this.x=e.x+t.x,this.y=e.y+t.y,this.z=e.z+t.z,this.w=e.w+t.w,this}addScaledVector(e,t){return this.x+=e.x*t,this.y+=e.y*t,this.z+=e.z*t,this.w+=e.w*t,this}sub(e){return this.x-=e.x,this.y-=e.y,this.z-=e.z,this.w-=e.w,this}subScalar(e){return this.x-=e,this.y-=e,this.z-=e,this.w-=e,this}subVectors(e,t){return this.x=e.x-t.x,this.y=e.y-t.y,this.z=e.z-t.z,this.w=e.w-t.w,this}multiply(e){return this.x*=e.x,this.y*=e.y,this.z*=e.z,this.w*=e.w,this}multiplyScalar(e){return this.x*=e,this.y*=e,this.z*=e,this.w*=e,this}applyMatrix4(e){let t=this.x,n=this.y,i=this.z,s=this.w,r=e.elements;return this.x=r[0]*t+r[4]*n+r[8]*i+r[12]*s,this.y=r[1]*t+r[5]*n+r[9]*i+r[13]*s,this.z=r[2]*t+r[6]*n+r[10]*i+r[14]*s,this.w=r[3]*t+r[7]*n+r[11]*i+r[15]*s,this}divide(e){return this.x/=e.x,this.y/=e.y,this.z/=e.z,this.w/=e.w,this}divideScalar(e){return this.multiplyScalar(1/e)}setAxisAngleFromQuaternion(e){this.w=2*Math.acos(e.w);let t=Math.sqrt(1-e.w*e.w);return t<1e-4?(this.x=1,this.y=0,this.z=0):(this.x=e.x/t,this.y=e.y/t,this.z=e.z/t),this}setAxisAngleFromRotationMatrix(e){let t,n,i,s,c=e.elements,l=c[0],u=c[4],h=c[8],f=c[1],d=c[5],p=c[9],m=c[2],b=c[6],x=c[10];if(Math.abs(u-f)<.01&&Math.abs(h-m)<.01&&Math.abs(p-b)<.01){if(Math.abs(u+f)<.1&&Math.abs(h+m)<.1&&Math.abs(p+b)<.1&&Math.abs(l+d+x-3)<.1)return this.set(1,0,0,0),this;t=Math.PI;let S=(l+1)/2,y=(d+1)/2,T=(x+1)/2,M=(u+f)/4,A=(h+m)/4,g=(p+b)/4;return S>y&&S>T?S<.01?(n=0,i=.707106781,s=.707106781):(n=Math.sqrt(S),i=M/n,s=A/n):y>T?y<.01?(n=.707106781,i=0,s=.707106781):(i=Math.sqrt(y),n=M/i,s=g/i):T<.01?(n=.707106781,i=.707106781,s=0):(s=Math.sqrt(T),n=A/s,i=g/s),this.set(n,i,s,t),this}let v=Math.sqrt((b-p)*(b-p)+(h-m)*(h-m)+(f-u)*(f-u));return Math.abs(v)<.001&&(v=1),this.x=(b-p)/v,this.y=(h-m)/v,this.z=(f-u)/v,this.w=Math.acos((l+d+x-1)/2),this}setFromMatrixPosition(e){let t=e.elements;return this.x=t[12],this.y=t[13],this.z=t[14],this.w=t[15],this}min(e){return this.x=Math.min(this.x,e.x),this.y=Math.min(this.y,e.y),this.z=Math.min(this.z,e.z),this.w=Math.min(this.w,e.w),this}max(e){return this.x=Math.max(this.x,e.x),this.y=Math.max(this.y,e.y),this.z=Math.max(this.z,e.z),this.w=Math.max(this.w,e.w),this}clamp(e,t){return this.x=q(this.x,e.x,t.x),this.y=q(this.y,e.y,t.y),this.z=q(this.z,e.z,t.z),this.w=q(this.w,e.w,t.w),this}clampScalar(e,t){return this.x=q(this.x,e,t),this.y=q(this.y,e,t),this.z=q(this.z,e,t),this.w=q(this.w,e,t),this}clampLength(e,t){let n=this.length();return this.divideScalar(n||1).multiplyScalar(q(n,e,t))}floor(){return this.x=Math.floor(this.x),this.y=Math.floor(this.y),this.z=Math.floor(this.z),this.w=Math.floor(this.w),this}ceil(){return this.x=Math.ceil(this.x),this.y=Math.ceil(this.y),this.z=Math.ceil(this.z),this.w=Math.ceil(this.w),this}round(){return this.x=Math.round(this.x),this.y=Math.round(this.y),this.z=Math.round(this.z),this.w=Math.round(this.w),this}roundToZero(){return this.x=Math.trunc(this.x),this.y=Math.trunc(this.y),this.z=Math.trunc(this.z),this.w=Math.trunc(this.w),this}negate(){return this.x=-this.x,this.y=-this.y,this.z=-this.z,this.w=-this.w,this}dot(e){return this.x*e.x+this.y*e.y+this.z*e.z+this.w*e.w}lengthSq(){return this.x*this.x+this.y*this.y+this.z*this.z+this.w*this.w}length(){return Math.sqrt(this.x*this.x+this.y*this.y+this.z*this.z+this.w*this.w)}manhattanLength(){return Math.abs(this.x)+Math.abs(this.y)+Math.abs(this.z)+Math.abs(this.w)}normalize(){return this.divideScalar(this.length()||1)}setLength(e){return this.normalize().multiplyScalar(e)}lerp(e,t){return this.x+=(e.x-this.x)*t,this.y+=(e.y-this.y)*t,this.z+=(e.z-this.z)*t,this.w+=(e.w-this.w)*t,this}lerpVectors(e,t,n){return this.x=e.x+(t.x-e.x)*n,this.y=e.y+(t.y-e.y)*n,this.z=e.z+(t.z-e.z)*n,this.w=e.w+(t.w-e.w)*n,this}equals(e){return e.x===this.x&&e.y===this.y&&e.z===this.z&&e.w===this.w}fromArray(e,t=0){return this.x=e[t],this.y=e[t+1],this.z=e[t+2],this.w=e[t+3],this}toArray(e=[],t=0){return e[t]=this.x,e[t+1]=this.y,e[t+2]=this.z,e[t+3]=this.w,e}fromBufferAttribute(e,t){return this.x=e.getX(t),this.y=e.getY(t),this.z=e.getZ(t),this.w=e.getW(t),this}random(){return this.x=Math.random(),this.y=Math.random(),this.z=Math.random(),this.w=Math.random(),this}*[Symbol.iterator](){yield this.x,yield this.y,yield this.z,yield this.w}};ga.prototype.isVector4=!0;var Xe=ga;var Ls=class Ls{constructor(e,t,n,i,s,r,o,c,l,u,h,f,d,p,m,b){this.elements=[1,0,0,0,0,1,0,0,0,0,1,0,0,0,0,1],e!==void 0&&this.set(e,t,n,i,s,r,o,c,l,u,h,f,d,p,m,b)}set(e,t,n,i,s,r,o,c,l,u,h,f,d,p,m,b){let x=this.elements;return x[0]=e,x[4]=t,x[8]=n,x[12]=i,x[1]=s,x[5]=r,x[9]=o,x[13]=c,x[2]=l,x[6]=u,x[10]=h,x[14]=f,x[3]=d,x[7]=p,x[11]=m,x[15]=b,this}identity(){return this.set(1,0,0,0,0,1,0,0,0,0,1,0,0,0,0,1),this}clone(){return new Ls().fromArray(this.elements)}copy(e){let t=this.elements,n=e.elements;return t[0]=n[0],t[1]=n[1],t[2]=n[2],t[3]=n[3],t[4]=n[4],t[5]=n[5],t[6]=n[6],t[7]=n[7],t[8]=n[8],t[9]=n[9],t[10]=n[10],t[11]=n[11],t[12]=n[12],t[13]=n[13],t[14]=n[14],t[15]=n[15],this}copyPosition(e){let t=this.elements,n=e.elements;return t[12]=n[12],t[13]=n[13],t[14]=n[14],this}setFromMatrix3(e){let t=e.elements;return this.set(t[0],t[3],t[6],0,t[1],t[4],t[7],0,t[2],t[5],t[8],0,0,0,0,1),this}extractBasis(e,t,n){return this.determinantAffine()===0?(e.set(1,0,0),t.set(0,1,0),n.set(0,0,1),this):(e.setFromMatrixColumn(this,0),t.setFromMatrixColumn(this,1),n.setFromMatrixColumn(this,2),this)}makeBasis(e,t,n){return this.set(e.x,t.x,n.x,0,e.y,t.y,n.y,0,e.z,t.z,n.z,0,0,0,0,1),this}extractRotation(e){if(e.determinantAffine()===0)return this.identity();let t=this.elements,n=e.elements,i=1/bn.setFromMatrixColumn(e,0).length(),s=1/bn.setFromMatrixColumn(e,1).length(),r=1/bn.setFromMatrixColumn(e,2).length();return t[0]=n[0]*i,t[1]=n[1]*i,t[2]=n[2]*i,t[3]=0,t[4]=n[4]*s,t[5]=n[5]*s,t[6]=n[6]*s,t[7]=0,t[8]=n[8]*r,t[9]=n[9]*r,t[10]=n[10]*r,t[11]=0,t[12]=0,t[13]=0,t[14]=0,t[15]=1,this}makeRotationFromEuler(e){let t=this.elements,n=e.x,i=e.y,s=e.z,r=Math.cos(n),o=Math.sin(n),c=Math.cos(i),l=Math.sin(i),u=Math.cos(s),h=Math.sin(s);if(e.order==="XYZ"){let f=r*u,d=r*h,p=o*u,m=o*h;t[0]=c*u,t[4]=-c*h,t[8]=l,t[1]=d+p*l,t[5]=f-m*l,t[9]=-o*c,t[2]=m-f*l,t[6]=p+d*l,t[10]=r*c}else if(e.order==="YXZ"){let f=c*u,d=c*h,p=l*u,m=l*h;t[0]=f+m*o,t[4]=p*o-d,t[8]=r*l,t[1]=r*h,t[5]=r*u,t[9]=-o,t[2]=d*o-p,t[6]=m+f*o,t[10]=r*c}else if(e.order==="ZXY"){let f=c*u,d=c*h,p=l*u,m=l*h;t[0]=f-m*o,t[4]=-r*h,t[8]=p+d*o,t[1]=d+p*o,t[5]=r*u,t[9]=m-f*o,t[2]=-r*l,t[6]=o,t[10]=r*c}else if(e.order==="ZYX"){let f=r*u,d=r*h,p=o*u,m=o*h;t[0]=c*u,t[4]=p*l-d,t[8]=f*l+m,t[1]=c*h,t[5]=m*l+f,t[9]=d*l-p,t[2]=-l,t[6]=o*c,t[10]=r*c}else if(e.order==="YZX"){let f=r*c,d=r*l,p=o*c,m=o*l;t[0]=c*u,t[4]=m-f*h,t[8]=p*h+d,t[1]=h,t[5]=r*u,t[9]=-o*u,t[2]=-l*u,t[6]=d*h+p,t[10]=f-m*h}else if(e.order==="XZY"){let f=r*c,d=r*l,p=o*c,m=o*l;t[0]=c*u,t[4]=-h,t[8]=l*u,t[1]=f*h+m,t[5]=r*u,t[9]=d*h-p,t[2]=p*h-d,t[6]=o*u,t[10]=m*h+f}return t[3]=0,t[7]=0,t[11]=0,t[12]=0,t[13]=0,t[14]=0,t[15]=1,this}makeRotationFromQuaternion(e){return this.compose(Th,e,wh)}lookAt(e,t,n){let i=this.elements;return Ue.subVectors(e,t),Ue.lengthSq()===0&&(Ue.z=1),Ue.normalize(),Lt.crossVectors(n,Ue),Lt.lengthSq()===0&&(Math.abs(n.z)===1?Ue.x+=1e-4:Ue.z+=1e-4,Ue.normalize(),Lt.crossVectors(n,Ue)),Lt.normalize(),Gi.crossVectors(Ue,Lt),i[0]=Lt.x,i[4]=Gi.x,i[8]=Ue.x,i[1]=Lt.y,i[5]=Gi.y,i[9]=Ue.y,i[2]=Lt.z,i[6]=Gi.z,i[10]=Ue.z,this}multiply(e){return this.multiplyMatrices(this,e)}premultiply(e){return this.multiplyMatrices(e,this)}multiplyMatrices(e,t){let n=e.elements,i=t.elements,s=this.elements,r=n[0],o=n[4],c=n[8],l=n[12],u=n[1],h=n[5],f=n[9],d=n[13],p=n[2],m=n[6],b=n[10],x=n[14],v=n[3],S=n[7],y=n[11],T=n[15],M=i[0],A=i[4],g=i[8],w=i[12],R=i[1],C=i[5],N=i[9],L=i[13],F=i[2],I=i[6],O=i[10],B=i[14],k=i[3],W=i[7],me=i[11],se=i[15];return s[0]=r*M+o*R+c*F+l*k,s[4]=r*A+o*C+c*I+l*W,s[8]=r*g+o*N+c*O+l*me,s[12]=r*w+o*L+c*B+l*se,s[1]=u*M+h*R+f*F+d*k,s[5]=u*A+h*C+f*I+d*W,s[9]=u*g+h*N+f*O+d*me,s[13]=u*w+h*L+f*B+d*se,s[2]=p*M+m*R+b*F+x*k,s[6]=p*A+m*C+b*I+x*W,s[10]=p*g+m*N+b*O+x*me,s[14]=p*w+m*L+b*B+x*se,s[3]=v*M+S*R+y*F+T*k,s[7]=v*A+S*C+y*I+T*W,s[11]=v*g+S*N+y*O+T*me,s[15]=v*w+S*L+y*B+T*se,this}multiplyScalar(e){let t=this.elements;return t[0]*=e,t[4]*=e,t[8]*=e,t[12]*=e,t[1]*=e,t[5]*=e,t[9]*=e,t[13]*=e,t[2]*=e,t[6]*=e,t[10]*=e,t[14]*=e,t[3]*=e,t[7]*=e,t[11]*=e,t[15]*=e,this}determinant(){let e=this.elements,t=e[0],n=e[4],i=e[8],s=e[12],r=e[1],o=e[5],c=e[9],l=e[13],u=e[2],h=e[6],f=e[10],d=e[14],p=e[3],m=e[7],b=e[11],x=e[15],v=c*d-l*f,S=o*d-l*h,y=o*f-c*h,T=r*d-l*u,M=r*f-c*u,A=r*h-o*u;return t*(m*v-b*S+x*y)-n*(p*v-b*T+x*M)+i*(p*S-m*T+x*A)-s*(p*y-m*M+b*A)}determinantAffine(){let e=this.elements,t=e[0],n=e[4],i=e[8],s=e[1],r=e[5],o=e[9],c=e[2],l=e[6],u=e[10];return t*(r*u-o*l)-n*(s*u-o*c)+i*(s*l-r*c)}transpose(){let e=this.elements,t;return t=e[1],e[1]=e[4],e[4]=t,t=e[2],e[2]=e[8],e[8]=t,t=e[6],e[6]=e[9],e[9]=t,t=e[3],e[3]=e[12],e[12]=t,t=e[7],e[7]=e[13],e[13]=t,t=e[11],e[11]=e[14],e[14]=t,this}setPosition(e,t,n){let i=this.elements;return e.isVector3?(i[12]=e.x,i[13]=e.y,i[14]=e.z):(i[12]=e,i[13]=t,i[14]=n),this}invert(){let e=this.elements,t=e[0],n=e[1],i=e[2],s=e[3],r=e[4],o=e[5],c=e[6],l=e[7],u=e[8],h=e[9],f=e[10],d=e[11],p=e[12],m=e[13],b=e[14],x=e[15],v=t*o-n*r,S=t*c-i*r,y=t*l-s*r,T=n*c-i*o,M=n*l-s*o,A=i*l-s*c,g=u*m-h*p,w=u*b-f*p,R=u*x-d*p,C=h*b-f*m,N=h*x-d*m,L=f*x-d*b,F=v*L-S*N+y*C+T*R-M*w+A*g;if(F===0)return this.set(0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);let I=1/F;return e[0]=(o*L-c*N+l*C)*I,e[1]=(i*N-n*L-s*C)*I,e[2]=(m*A-b*M+x*T)*I,e[3]=(f*M-h*A-d*T)*I,e[4]=(c*R-r*L-l*w)*I,e[5]=(t*L-i*R+s*w)*I,e[6]=(b*y-p*A-x*S)*I,e[7]=(u*A-f*y+d*S)*I,e[8]=(r*N-o*R+l*g)*I,e[9]=(n*R-t*N-s*g)*I,e[10]=(p*M-m*y+x*v)*I,e[11]=(h*y-u*M-d*v)*I,e[12]=(o*w-r*C-c*g)*I,e[13]=(t*C-n*w+i*g)*I,e[14]=(m*S-p*T-b*v)*I,e[15]=(u*T-h*S+f*v)*I,this}scale(e){let t=this.elements,n=e.x,i=e.y,s=e.z;return t[0]*=n,t[4]*=i,t[8]*=s,t[1]*=n,t[5]*=i,t[9]*=s,t[2]*=n,t[6]*=i,t[10]*=s,t[3]*=n,t[7]*=i,t[11]*=s,this}getMaxScaleOnAxis(){let e=this.elements,t=e[0]*e[0]+e[1]*e[1]+e[2]*e[2],n=e[4]*e[4]+e[5]*e[5]+e[6]*e[6],i=e[8]*e[8]+e[9]*e[9]+e[10]*e[10];return Math.sqrt(Math.max(t,n,i))}makeTranslation(e,t,n){return e.isVector3?this.set(1,0,0,e.x,0,1,0,e.y,0,0,1,e.z,0,0,0,1):this.set(1,0,0,e,0,1,0,t,0,0,1,n,0,0,0,1),this}makeRotationX(e){let t=Math.cos(e),n=Math.sin(e);return this.set(1,0,0,0,0,t,-n,0,0,n,t,0,0,0,0,1),this}makeRotationY(e){let t=Math.cos(e),n=Math.sin(e);return this.set(t,0,n,0,0,1,0,0,-n,0,t,0,0,0,0,1),this}makeRotationZ(e){let t=Math.cos(e),n=Math.sin(e);return this.set(t,-n,0,0,n,t,0,0,0,0,1,0,0,0,0,1),this}makeRotationAxis(e,t){let n=Math.cos(t),i=Math.sin(t),s=1-n,r=e.x,o=e.y,c=e.z,l=s*r,u=s*o;return this.set(l*r+n,l*o-i*c,l*c+i*o,0,l*o+i*c,u*o+n,u*c-i*r,0,l*c-i*o,u*c+i*r,s*c*c+n,0,0,0,0,1),this}makeScale(e,t,n){return this.set(e,0,0,0,0,t,0,0,0,0,n,0,0,0,0,1),this}makeShear(e,t,n,i,s,r){return this.set(1,n,s,0,e,1,r,0,t,i,1,0,0,0,0,1),this}compose(e,t,n){let i=this.elements,s=t._x,r=t._y,o=t._z,c=t._w,l=s+s,u=r+r,h=o+o,f=s*l,d=s*u,p=s*h,m=r*u,b=r*h,x=o*h,v=c*l,S=c*u,y=c*h,T=n.x,M=n.y,A=n.z;return i[0]=(1-(m+x))*T,i[1]=(d+y)*T,i[2]=(p-S)*T,i[3]=0,i[4]=(d-y)*M,i[5]=(1-(f+x))*M,i[6]=(b+v)*M,i[7]=0,i[8]=(p+S)*A,i[9]=(b-v)*A,i[10]=(1-(f+m))*A,i[11]=0,i[12]=e.x,i[13]=e.y,i[14]=e.z,i[15]=1,this}decompose(e,t,n){let i=this.elements;e.x=i[12],e.y=i[13],e.z=i[14];let s=this.determinantAffine();if(s===0)return n.set(1,1,1),t.identity(),this;let r=bn.set(i[0],i[1],i[2]).length(),o=bn.set(i[4],i[5],i[6]).length(),c=bn.set(i[8],i[9],i[10]).length();s<0&&(r=-r),Ke.copy(this);let l=1/r,u=1/o,h=1/c;return Ke.elements[0]*=l,Ke.elements[1]*=l,Ke.elements[2]*=l,Ke.elements[4]*=u,Ke.elements[5]*=u,Ke.elements[6]*=u,Ke.elements[8]*=h,Ke.elements[9]*=h,Ke.elements[10]*=h,t.setFromRotationMatrix(Ke),n.x=r,n.y=o,n.z=c,this}makePerspective(e,t,n,i,s,r,o=kt,c=!1){let l=this.elements,u=2*s/(t-e),h=2*s/(n-i),f=(t+e)/(t-e),d=(n+i)/(n-i),p,m;if(c)p=s/(r-s),m=r*s/(r-s);else if(o===kt)p=-(r+s)/(r-s),m=-2*r*s/(r-s);else if(o===ai)p=-r/(r-s),m=-r*s/(r-s);else throw new Error("THREE.Matrix4.makePerspective(): Invalid coordinate system: "+o);return l[0]=u,l[4]=0,l[8]=f,l[12]=0,l[1]=0,l[5]=h,l[9]=d,l[13]=0,l[2]=0,l[6]=0,l[10]=p,l[14]=m,l[3]=0,l[7]=0,l[11]=-1,l[15]=0,this}makeOrthographic(e,t,n,i,s,r,o=kt,c=!1){let l=this.elements,u=2/(t-e),h=2/(n-i),f=-(t+e)/(t-e),d=-(n+i)/(n-i),p,m;if(c)p=1/(r-s),m=r/(r-s);else if(o===kt)p=-2/(r-s),m=-(r+s)/(r-s);else if(o===ai)p=-1/(r-s),m=-s/(r-s);else throw new Error("THREE.Matrix4.makeOrthographic(): Invalid coordinate system: "+o);return l[0]=u,l[4]=0,l[8]=0,l[12]=f,l[1]=0,l[5]=h,l[9]=0,l[13]=d,l[2]=0,l[6]=0,l[10]=p,l[14]=m,l[3]=0,l[7]=0,l[11]=0,l[15]=1,this}equals(e){let t=this.elements,n=e.elements;for(let i=0;i<16;i++)if(t[i]!==n[i])return!1;return!0}fromArray(e,t=0){for(let n=0;n<16;n++)this.elements[n]=e[n+t];return this}toArray(e=[],t=0){let n=this.elements;return e[t]=n[0],e[t+1]=n[1],e[t+2]=n[2],e[t+3]=n[3],e[t+4]=n[4],e[t+5]=n[5],e[t+6]=n[6],e[t+7]=n[7],e[t+8]=n[8],e[t+9]=n[9],e[t+10]=n[10],e[t+11]=n[11],e[t+12]=n[12],e[t+13]=n[13],e[t+14]=n[14],e[t+15]=n[15],e}};Ls.prototype.isMatrix4=!0;var z=Ls,bn=new E,Ke=new z,Th=new E(0,0,0),wh=new E(1,1,1),Lt=new E,Gi=new E,Ue=new E,mc=new z,gc=new pe,ke=class a{constructor(e=0,t=0,n=0,i=a.DEFAULT_ORDER){this.isEuler=!0,this._x=e,this._y=t,this._z=n,this._order=i}get x(){return this._x}set x(e){this._x=e,this._onChangeCallback()}get y(){return this._y}set y(e){this._y=e,this._onChangeCallback()}get z(){return this._z}set z(e){this._z=e,this._onChangeCallback()}get order(){return this._order}set order(e){this._order=e,this._onChangeCallback()}set(e,t,n,i=this._order){return this._x=e,this._y=t,this._z=n,this._order=i,this._onChangeCallback(),this}clone(){return new this.constructor(this._x,this._y,this._z,this._order)}copy(e){return this._x=e._x,this._y=e._y,this._z=e._z,this._order=e._order,this._onChangeCallback(),this}setFromRotationMatrix(e,t=this._order,n=!0){let i=e.elements,s=i[0],r=i[4],o=i[8],c=i[1],l=i[5],u=i[9],h=i[2],f=i[6],d=i[10];switch(t){case"XYZ":this._y=Math.asin(q(o,-1,1)),Math.abs(o)<.9999999?(this._x=Math.atan2(-u,d),this._z=Math.atan2(-r,s)):(this._x=Math.atan2(f,l),this._z=0);break;case"YXZ":this._x=Math.asin(-q(u,-1,1)),Math.abs(u)<.9999999?(this._y=Math.atan2(o,d),this._z=Math.atan2(c,l)):(this._y=Math.atan2(-h,s),this._z=0);break;case"ZXY":this._x=Math.asin(q(f,-1,1)),Math.abs(f)<.9999999?(this._y=Math.atan2(-h,d),this._z=Math.atan2(-r,l)):(this._y=0,this._z=Math.atan2(c,s));break;case"ZYX":this._y=Math.asin(-q(h,-1,1)),Math.abs(h)<.9999999?(this._x=Math.atan2(f,d),this._z=Math.atan2(c,s)):(this._x=0,this._z=Math.atan2(-r,l));break;case"YZX":this._z=Math.asin(q(c,-1,1)),Math.abs(c)<.9999999?(this._x=Math.atan2(-u,l),this._y=Math.atan2(-h,s)):(this._x=0,this._y=Math.atan2(o,d));break;case"XZY":this._z=Math.asin(-q(r,-1,1)),Math.abs(r)<.9999999?(this._x=Math.atan2(f,l),this._y=Math.atan2(o,s)):(this._x=Math.atan2(-u,d),this._y=0);break;default:ne("Euler: .setFromRotationMatrix() encountered an unknown order: "+t)}return this._order=t,n===!0&&this._onChangeCallback(),this}setFromQuaternion(e,t,n){return mc.makeRotationFromQuaternion(e),this.setFromRotationMatrix(mc,t,n)}setFromVector3(e,t=this._order){return this.set(e.x,e.y,e.z,t)}reorder(e){return gc.setFromEuler(this),this.setFromQuaternion(gc,e)}equals(e){return e._x===this._x&&e._y===this._y&&e._z===this._z&&e._order===this._order}fromArray(e){return this._x=e[0],this._y=e[1],this._z=e[2],e[3]!==void 0&&(this._order=e[3]),this._onChangeCallback(),this}toArray(e=[],t=0){return e[t]=this._x,e[t+1]=this._y,e[t+2]=this._z,e[t+3]=this._order,e}_onChange(e){return this._onChangeCallback=e,this}_onChangeCallback(){}*[Symbol.iterator](){yield this._x,yield this._y,yield this._z,yield this._order}};ke.DEFAULT_ORDER="XYZ";var _s=class{constructor(){this.mask=1}set(e){this.mask=(1<<e|0)>>>0}enable(e){this.mask|=1<<e|0}enableAll(){this.mask=-1}toggle(e){this.mask^=1<<e|0}disable(e){this.mask&=~(1<<e|0)}disableAll(){this.mask=0}test(e){return(this.mask&e.mask)!==0}isEnabled(e){return(this.mask&(1<<e|0))!==0}},Eh=0,xc=new E,_n=new pe,ht=new z,Hi=new E,Jn=new E,Rh=new E,Ch=new pe,bc=new E(1,0,0),_c=new E(0,1,0),yc=new E(0,0,1),vc={type:"added"},Ih={type:"removed"},yn={type:"childadded",child:null},ur={type:"childremoved",child:null},le=class a extends Vt{constructor(){super(),this.isObject3D=!0,Object.defineProperty(this,"id",{value:Eh++}),this.uuid=Ze(),this.name="",this.type="Object3D",this.parent=null,this.children=[],this.up=a.DEFAULT_UP.clone();let e=new E,t=new ke,n=new pe,i=new E(1,1,1);function s(){n.setFromEuler(t,!1)}function r(){t.setFromQuaternion(n,void 0,!1)}t._onChange(s),n._onChange(r),Object.defineProperties(this,{position:{configurable:!0,enumerable:!0,value:e},rotation:{configurable:!0,enumerable:!0,value:t},quaternion:{configurable:!0,enumerable:!0,value:n},scale:{configurable:!0,enumerable:!0,value:i},modelViewMatrix:{value:new z},normalMatrix:{value:new G}}),this.matrix=new z,this.matrixWorld=new z,this.matrixAutoUpdate=a.DEFAULT_MATRIX_AUTO_UPDATE,this.matrixWorldAutoUpdate=a.DEFAULT_MATRIX_WORLD_AUTO_UPDATE,this.matrixWorldNeedsUpdate=!1,this.layers=new _s,this.visible=!0,this.castShadow=!1,this.receiveShadow=!1,this.frustumCulled=!0,this.renderOrder=0,this.animations=[],this.customDepthMaterial=void 0,this.customDistanceMaterial=void 0,this.static=!1,this.userData={},this.pivot=null}onBeforeShadow(){}onAfterShadow(){}onBeforeRender(){}onAfterRender(){}applyMatrix4(e){this.matrixAutoUpdate&&this.updateMatrix(),this.matrix.premultiply(e),this.matrix.decompose(this.position,this.quaternion,this.scale)}applyQuaternion(e){return this.quaternion.premultiply(e),this}setRotationFromAxisAngle(e,t){this.quaternion.setFromAxisAngle(e,t)}setRotationFromEuler(e){this.quaternion.setFromEuler(e,!0)}setRotationFromMatrix(e){this.quaternion.setFromRotationMatrix(e)}setRotationFromQuaternion(e){this.quaternion.copy(e)}rotateOnAxis(e,t){return _n.setFromAxisAngle(e,t),this.quaternion.multiply(_n),this}rotateOnWorldAxis(e,t){return _n.setFromAxisAngle(e,t),this.quaternion.premultiply(_n),this}rotateX(e){return this.rotateOnAxis(bc,e)}rotateY(e){return this.rotateOnAxis(_c,e)}rotateZ(e){return this.rotateOnAxis(yc,e)}translateOnAxis(e,t){return xc.copy(e).applyQuaternion(this.quaternion),this.position.add(xc.multiplyScalar(t)),this}translateX(e){return this.translateOnAxis(bc,e)}translateY(e){return this.translateOnAxis(_c,e)}translateZ(e){return this.translateOnAxis(yc,e)}localToWorld(e){return this.updateWorldMatrix(!0,!1),e.applyMatrix4(this.matrixWorld)}worldToLocal(e){return this.updateWorldMatrix(!0,!1),e.applyMatrix4(ht.copy(this.matrixWorld).invert())}lookAt(e,t,n){e.isVector3?Hi.copy(e):Hi.set(e,t,n);let i=this.parent;this.updateWorldMatrix(!0,!1),Jn.setFromMatrixPosition(this.matrixWorld),this.isCamera||this.isLight?ht.lookAt(Jn,Hi,this.up):ht.lookAt(Hi,Jn,this.up),this.quaternion.setFromRotationMatrix(ht),i&&(ht.extractRotation(i.matrixWorld),_n.setFromRotationMatrix(ht),this.quaternion.premultiply(_n.invert()))}add(e){if(arguments.length>1){for(let t=0;t<arguments.length;t++)this.add(arguments[t]);return this}return e===this?(oe("Object3D.add: object can't be added as a child of itself.",e),this):(e&&e.isObject3D?(e.removeFromParent(),e.parent=this,this.children.push(e),e.dispatchEvent(vc),yn.child=e,this.dispatchEvent(yn),yn.child=null):oe("Object3D.add: object not an instance of THREE.Object3D.",e),this)}remove(e){if(arguments.length>1){for(let n=0;n<arguments.length;n++)this.remove(arguments[n]);return this}let t=this.children.indexOf(e);return t!==-1&&(e.parent=null,this.children.splice(t,1),e.dispatchEvent(Ih),ur.child=e,this.dispatchEvent(ur),ur.child=null),this}removeFromParent(){let e=this.parent;return e!==null&&e.remove(this),this}clear(){return this.remove(...this.children)}attach(e){return this.updateWorldMatrix(!0,!1),ht.copy(this.matrixWorld).invert(),e.parent!==null&&(e.parent.updateWorldMatrix(!0,!1),ht.multiply(e.parent.matrixWorld)),e.applyMatrix4(ht),e.removeFromParent(),e.parent=this,this.children.push(e),e.updateWorldMatrix(!1,!0),e.dispatchEvent(vc),yn.child=e,this.dispatchEvent(yn),yn.child=null,this}getObjectById(e){return this.getObjectByProperty("id",e)}getObjectByName(e){return this.getObjectByProperty("name",e)}getObjectByProperty(e,t){if(this[e]===t)return this;for(let n=0,i=this.children.length;n<i;n++){let r=this.children[n].getObjectByProperty(e,t);if(r!==void 0)return r}}getObjectsByProperty(e,t,n=[]){this[e]===t&&n.push(this);let i=this.children;for(let s=0,r=i.length;s<r;s++)i[s].getObjectsByProperty(e,t,n);return n}getWorldPosition(e){return this.updateWorldMatrix(!0,!1),e.setFromMatrixPosition(this.matrixWorld)}getWorldQuaternion(e){return this.updateWorldMatrix(!0,!1),this.matrixWorld.decompose(Jn,e,Rh),e}getWorldScale(e){return this.updateWorldMatrix(!0,!1),this.matrixWorld.decompose(Jn,Ch,e),e}getWorldDirection(e){this.updateWorldMatrix(!0,!1);let t=this.matrixWorld.elements;return e.set(t[8],t[9],t[10]).normalize()}raycast(){}intersectsFrustum(){}traverse(e){e(this);let t=this.children;for(let n=0,i=t.length;n<i;n++)t[n].traverse(e)}traverseVisible(e){if(this.visible===!1)return;e(this);let t=this.children;for(let n=0,i=t.length;n<i;n++)t[n].traverseVisible(e)}traverseAncestors(e){let t=this.parent;t!==null&&(e(t),t.traverseAncestors(e))}updateMatrix(){this.matrix.compose(this.position,this.quaternion,this.scale);let e=this.pivot;if(e!==null){let t=e.x,n=e.y,i=e.z,s=this.matrix.elements;s[12]+=t-s[0]*t-s[4]*n-s[8]*i,s[13]+=n-s[1]*t-s[5]*n-s[9]*i,s[14]+=i-s[2]*t-s[6]*n-s[10]*i}this.matrixWorldNeedsUpdate=!0}updateMatrixWorld(e){this.matrixAutoUpdate&&this.updateMatrix(),(this.matrixWorldNeedsUpdate||e)&&(this.matrixWorldAutoUpdate===!0&&(this.parent===null?this.matrixWorld.copy(this.matrix):this.matrixWorld.multiplyMatrices(this.parent.matrixWorld,this.matrix)),this.matrixWorldNeedsUpdate=!1,e=!0);let t=this.children;for(let n=0,i=t.length;n<i;n++)t[n].updateMatrixWorld(e)}updateWorldMatrix(e,t,n=!1){let i=this.parent;if(e===!0&&i!==null&&i.updateWorldMatrix(!0,!1),this.matrixAutoUpdate&&this.updateMatrix(),(this.matrixWorldNeedsUpdate||n)&&(this.matrixWorldAutoUpdate===!0&&(this.parent===null?this.matrixWorld.copy(this.matrix):this.matrixWorld.multiplyMatrices(this.parent.matrixWorld,this.matrix)),this.matrixWorldNeedsUpdate=!1,n=!0),t===!0){let s=this.children;for(let r=0,o=s.length;r<o;r++)s[r].updateWorldMatrix(!1,!0,n)}}toJSON(e){let t=e===void 0||typeof e=="string",n={};t&&(e={geometries:{},materials:{},textures:{},images:{},shapes:{},skeletons:{},animations:{},nodes:{}},n.metadata={version:4.7,type:"Object",generator:"Object3D.toJSON"});let i={};i.uuid=this.uuid,i.type=this.type,i.name=this.name,i.castShadow=this.castShadow,i.receiveShadow=this.receiveShadow,i.visible=this.visible,i.frustumCulled=this.frustumCulled,i.renderOrder=this.renderOrder,i.static=this.static,i.matrixAutoUpdate=this.matrixAutoUpdate,Object.keys(this.userData).length>0&&(i.userData=this.userData),i.layers=this.layers.mask,i.matrix=this.matrix.toArray(),i.up=this.up.toArray(),this.pivot!==null&&(i.pivot=this.pivot.toArray()),this.morphTargetDictionary!==void 0&&(i.morphTargetDictionary=Object.assign({},this.morphTargetDictionary)),this.morphTargetInfluences!==void 0&&(i.morphTargetInfluences=this.morphTargetInfluences.slice()),this.isInstancedMesh&&(i.type="InstancedMesh",i.count=this.count,i.instanceMatrix=this.instanceMatrix.toJSON(),this.instanceColor!==null&&(i.instanceColor=this.instanceColor.toJSON())),this.isBatchedMesh&&(i.type="BatchedMesh",i.perObjectFrustumCulled=this.perObjectFrustumCulled,i.sortObjects=this.sortObjects,i.drawRanges=this._drawRanges,i.reservedRanges=this._reservedRanges,i.geometryInfo=this._geometryInfo.map(o=>({...o,boundingBox:o.boundingBox?o.boundingBox.toJSON():void 0,boundingSphere:o.boundingSphere?o.boundingSphere.toJSON():void 0})),i.instanceInfo=this._instanceInfo.map(o=>({...o})),i.availableInstanceIds=this._availableInstanceIds.slice(),i.availableGeometryIds=this._availableGeometryIds.slice(),i.nextIndexStart=this._nextIndexStart,i.nextVertexStart=this._nextVertexStart,i.geometryCount=this._geometryCount,i.maxInstanceCount=this._maxInstanceCount,i.maxVertexCount=this._maxVertexCount,i.maxIndexCount=this._maxIndexCount,i.geometryInitialized=this._geometryInitialized,i.matricesTexture=this._matricesTexture.toJSON(e),i.indirectTexture=this._indirectTexture.toJSON(e),this._colorsTexture!==null&&(i.colorsTexture=this._colorsTexture.toJSON(e)),this.boundingSphere!==null&&(i.boundingSphere=this.boundingSphere.toJSON()),this.boundingBox!==null&&(i.boundingBox=this.boundingBox.toJSON()));function s(o,c){return o[c.uuid]===void 0&&(o[c.uuid]=c.toJSON(e)),c.uuid}if(this.isScene)this.background&&(this.background.isColor?i.background=this.background.toJSON():this.background.isTexture&&(i.background=this.background.toJSON(e).uuid)),this.environment&&this.environment.isTexture&&this.environment.isRenderTargetTexture!==!0&&(i.environment=this.environment.toJSON(e).uuid);else if(this.isMesh||this.isLine||this.isPoints){i.geometry=s(e.geometries,this.geometry);let o=this.geometry.parameters;if(o!==void 0&&o.shapes!==void 0){let c=o.shapes;if(Array.isArray(c))for(let l=0,u=c.length;l<u;l++){let h=c[l];s(e.shapes,h)}else s(e.shapes,c)}}if(this.isSkinnedMesh&&(i.bindMode=this.bindMode,i.bindMatrix=this.bindMatrix.toArray(),this.skeleton!==void 0&&(s(e.skeletons,this.skeleton),i.skeleton=this.skeleton.uuid)),this.material!==void 0)if(Array.isArray(this.material)){let o=[];for(let c=0,l=this.material.length;c<l;c++)o.push(s(e.materials,this.material[c]));i.material=o}else i.material=s(e.materials,this.material);if(this.children.length>0){i.children=[];for(let o=0;o<this.children.length;o++)i.children.push(this.children[o].toJSON(e).object)}if(this.animations.length>0){i.animations=[];for(let o=0;o<this.animations.length;o++){let c=this.animations[o];i.animations.push(s(e.animations,c))}}if(t){let o=r(e.geometries),c=r(e.materials),l=r(e.textures),u=r(e.images),h=r(e.shapes),f=r(e.skeletons),d=r(e.animations),p=r(e.nodes);o.length>0&&(n.geometries=o),c.length>0&&(n.materials=c),l.length>0&&(n.textures=l),u.length>0&&(n.images=u),h.length>0&&(n.shapes=h),f.length>0&&(n.skeletons=f),d.length>0&&(n.animations=d),p.length>0&&(n.nodes=p)}return n.object=i,n;function r(o){let c=[];for(let l in o){let u=o[l];delete u.metadata,c.push(u)}return c}}clone(e){return new this.constructor().copy(this,e)}copy(e,t=!0){if(this.name=e.name,this.up.copy(e.up),this.position.copy(e.position),this.rotation.order=e.rotation.order,this.quaternion.copy(e.quaternion),this.scale.copy(e.scale),this.pivot=e.pivot!==null?e.pivot.clone():null,this.matrix.copy(e.matrix),this.matrixWorld.copy(e.matrixWorld),this.matrixAutoUpdate=e.matrixAutoUpdate,this.matrixWorldAutoUpdate=e.matrixWorldAutoUpdate,this.matrixWorldNeedsUpdate=e.matrixWorldNeedsUpdate,this.layers.mask=e.layers.mask,this.visible=e.visible,this.castShadow=e.castShadow,this.receiveShadow=e.receiveShadow,this.frustumCulled=e.frustumCulled,this.renderOrder=e.renderOrder,this.static=e.static,this.animations=e.animations.slice(),this.userData=JSON.parse(JSON.stringify(e.userData)),t===!0)for(let n=0;n<e.children.length;n++){let i=e.children[n];this.add(i.clone())}return this}dispose(){this.dispatchEvent({type:"dispose"})}};le.DEFAULT_UP=new E(0,1,0);le.DEFAULT_MATRIX_AUTO_UPDATE=!0;le.DEFAULT_MATRIX_WORLD_AUTO_UPDATE=!0;var rn=class extends le{constructor(){super(),this.isGroup=!0,this.type="Group"}};var ul={aliceblue:15792383,antiquewhite:16444375,aqua:65535,aquamarine:8388564,azure:15794175,beige:16119260,bisque:16770244,black:0,blanchedalmond:16772045,blue:255,blueviolet:9055202,brown:10824234,burlywood:14596231,cadetblue:6266528,chartreuse:8388352,chocolate:13789470,coral:16744272,cornflowerblue:6591981,cornsilk:16775388,crimson:14423100,cyan:65535,darkblue:139,darkcyan:35723,darkgoldenrod:12092939,darkgray:11119017,darkgreen:25600,darkgrey:11119017,darkkhaki:12433259,darkmagenta:9109643,darkolivegreen:5597999,darkorange:16747520,darkorchid:10040012,darkred:9109504,darksalmon:15308410,darkseagreen:9419919,darkslateblue:4734347,darkslategray:3100495,darkslategrey:3100495,darkturquoise:52945,darkviolet:9699539,deeppink:16716947,deepskyblue:49151,dimgray:6908265,dimgrey:6908265,dodgerblue:2003199,firebrick:11674146,floralwhite:16775920,forestgreen:2263842,fuchsia:16711935,gainsboro:14474460,ghostwhite:16316671,gold:16766720,goldenrod:14329120,gray:8421504,green:32768,greenyellow:11403055,grey:8421504,honeydew:15794160,hotpink:16738740,indianred:13458524,indigo:4915330,ivory:16777200,khaki:15787660,lavender:15132410,lavenderblush:16773365,lawngreen:8190976,lemonchiffon:16775885,lightblue:11393254,lightcoral:15761536,lightcyan:14745599,lightgoldenrodyellow:16448210,lightgray:13882323,lightgreen:9498256,lightgrey:13882323,lightpink:16758465,lightsalmon:16752762,lightseagreen:2142890,lightskyblue:8900346,lightslategray:7833753,lightslategrey:7833753,lightsteelblue:11584734,lightyellow:16777184,lime:65280,limegreen:3329330,linen:16445670,magenta:16711935,maroon:8388608,mediumaquamarine:6737322,mediumblue:205,mediumorchid:12211667,mediumpurple:9662683,mediumseagreen:3978097,mediumslateblue:8087790,mediumspringgreen:64154,mediumturquoise:4772300,mediumvioletred:13047173,midnightblue:1644912,mintcream:16121850,mistyrose:16770273,moccasin:16770229,navajowhite:16768685,navy:128,oldlace:16643558,olive:8421376,olivedrab:7048739,orange:16753920,orangered:16729344,orchid:14315734,palegoldenrod:15657130,palegreen:10025880,paleturquoise:11529966,palevioletred:14381203,papayawhip:16773077,peachpuff:16767673,peru:13468991,pink:16761035,plum:14524637,powderblue:11591910,purple:8388736,rebeccapurple:6697881,red:16711680,rosybrown:12357519,royalblue:4286945,saddlebrown:9127187,salmon:16416882,sandybrown:16032864,seagreen:3050327,seashell:16774638,sienna:10506797,silver:12632256,skyblue:8900331,slateblue:6970061,slategray:7372944,slategrey:7372944,snow:16775930,springgreen:65407,steelblue:4620980,tan:13808780,teal:32896,thistle:14204888,tomato:16737095,turquoise:4251856,violet:15631086,wheat:16113331,white:16777215,whitesmoke:16119285,yellow:16776960,yellowgreen:10145074},Dt={h:0,s:0,l:0},Wi={h:0,s:0,l:0};function hr(a,e,t){return t<0&&(t+=1),t>1&&(t-=1),t<1/6?a+(e-a)*6*t:t<1/2?e:t<2/3?a+(e-a)*6*(2/3-t):a}var H=class{constructor(e,t,n){return this.isColor=!0,this.r=1,this.g=1,this.b=1,this.set(e,t,n)}set(e,t,n){if(t===void 0&&n===void 0){let i=e;i&&i.isColor?this.copy(i):typeof i=="number"?this.setHex(i):typeof i=="string"&&this.setStyle(i)}else this.setRGB(e,t,n);return this}setScalar(e){return this.r=e,this.g=e,this.b=e,this}setHex(e,t=ce){return e=Math.floor(e),this.r=(e>>16&255)/255,this.g=(e>>8&255)/255,this.b=(e&255)/255,_e.colorSpaceToWorking(this,t),this}setRGB(e,t,n,i=_e.workingColorSpace){return this.r=e,this.g=t,this.b=n,_e.colorSpaceToWorking(this,i),this}setHSL(e,t,n,i=_e.workingColorSpace){if(e=ua(e,1),t=q(t,0,1),n=q(n,0,1),t===0)this.r=this.g=this.b=n;else{let s=n<=.5?n*(1+t):n+t-n*t,r=2*n-s;this.r=hr(r,s,e+1/3),this.g=hr(r,s,e),this.b=hr(r,s,e-1/3)}return _e.colorSpaceToWorking(this,i),this}setStyle(e,t=ce){function n(s){s!==void 0&&parseFloat(s)<1&&ne("Color: Alpha component of "+e+" will be ignored.")}let i;if(i=/^(\w+)\(([^\)]*)\)/.exec(e)){let s,r=i[1],o=i[2];switch(r){case"rgb":case"rgba":if(s=/^\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)\s*(?:,\s*(\d*\.?\d+)\s*)?$/.exec(o))return n(s[4]),this.setRGB(Math.min(255,parseInt(s[1],10))/255,Math.min(255,parseInt(s[2],10))/255,Math.min(255,parseInt(s[3],10))/255,t);if(s=/^\s*(\d+)\%\s*,\s*(\d+)\%\s*,\s*(\d+)\%\s*(?:,\s*(\d*\.?\d+)\s*)?$/.exec(o))return n(s[4]),this.setRGB(Math.min(100,parseInt(s[1],10))/100,Math.min(100,parseInt(s[2],10))/100,Math.min(100,parseInt(s[3],10))/100,t);break;case"hsl":case"hsla":if(s=/^\s*(\d*\.?\d+)\s*,\s*(\d*\.?\d+)\%\s*,\s*(\d*\.?\d+)\%\s*(?:,\s*(\d*\.?\d+)\s*)?$/.exec(o))return n(s[4]),this.setHSL(parseFloat(s[1])/360,parseFloat(s[2])/100,parseFloat(s[3])/100,t);break;default:ne("Color: Unknown color model "+e)}}else if(i=/^\#([A-Fa-f\d]+)$/.exec(e)){let s=i[1],r=s.length;if(r===3)return this.setRGB(parseInt(s.charAt(0),16)/15,parseInt(s.charAt(1),16)/15,parseInt(s.charAt(2),16)/15,t);if(r===6)return this.setHex(parseInt(s,16),t);ne("Color: Invalid hex color "+e)}else if(e&&e.length>0)return this.setColorName(e,t);return this}setColorName(e,t=ce){let n=ul[e.toLowerCase()];return n!==void 0?this.setHex(n,t):ne("Color: Unknown color "+e),this}clone(){return new this.constructor(this.r,this.g,this.b)}copy(e){return this.r=e.r,this.g=e.g,this.b=e.b,this}copySRGBToLinear(e){return this.r=bt(e.r),this.g=bt(e.g),this.b=bt(e.b),this}copyLinearToSRGB(e){return this.r=In(e.r),this.g=In(e.g),this.b=In(e.b),this}convertSRGBToLinear(){return this.copySRGBToLinear(this),this}convertLinearToSRGB(){return this.copyLinearToSRGB(this),this}getHex(e=ce){return _e.workingToColorSpace(Se.copy(this),e),Math.round(q(Se.r*255,0,255))*65536+Math.round(q(Se.g*255,0,255))*256+Math.round(q(Se.b*255,0,255))}getHexString(e=ce){return("000000"+this.getHex(e).toString(16)).slice(-6)}getHSL(e,t=_e.workingColorSpace){_e.workingToColorSpace(Se.copy(this),t);let n=Se.r,i=Se.g,s=Se.b,r=Math.max(n,i,s),o=Math.min(n,i,s),c,l,u=(o+r)/2;if(o===r)c=0,l=0;else{let h=r-o;switch(l=u<=.5?h/(r+o):h/(2-r-o),r){case n:c=(i-s)/h+(i<s?6:0);break;case i:c=(s-n)/h+2;break;case s:c=(n-i)/h+4;break}c/=6}return e.h=c,e.s=l,e.l=u,e}getRGB(e,t=_e.workingColorSpace){return _e.workingToColorSpace(Se.copy(this),t),e.r=Se.r,e.g=Se.g,e.b=Se.b,e}getStyle(e=ce){_e.workingToColorSpace(Se.copy(this),e);let t=Se.r,n=Se.g,i=Se.b;return e!==ce?`color(${e} ${t.toFixed(3)} ${n.toFixed(3)} ${i.toFixed(3)})`:`rgb(${Math.round(t*255)},${Math.round(n*255)},${Math.round(i*255)})`}offsetHSL(e,t,n){return this.getHSL(Dt),this.setHSL(Dt.h+e,Dt.s+t,Dt.l+n)}add(e){return this.r+=e.r,this.g+=e.g,this.b+=e.b,this}addColors(e,t){return this.r=e.r+t.r,this.g=e.g+t.g,this.b=e.b+t.b,this}addScalar(e){return this.r+=e,this.g+=e,this.b+=e,this}sub(e){return this.r=Math.max(0,this.r-e.r),this.g=Math.max(0,this.g-e.g),this.b=Math.max(0,this.b-e.b),this}multiply(e){return this.r*=e.r,this.g*=e.g,this.b*=e.b,this}multiplyScalar(e){return this.r*=e,this.g*=e,this.b*=e,this}lerp(e,t){return this.r+=(e.r-this.r)*t,this.g+=(e.g-this.g)*t,this.b+=(e.b-this.b)*t,this}lerpColors(e,t,n){return this.r=e.r+(t.r-e.r)*n,this.g=e.g+(t.g-e.g)*n,this.b=e.b+(t.b-e.b)*n,this}lerpHSL(e,t){this.getHSL(Dt),e.getHSL(Wi);let n=ri(Dt.h,Wi.h,t),i=ri(Dt.s,Wi.s,t),s=ri(Dt.l,Wi.l,t);return this.setHSL(n,i,s),this}setFromVector3(e){return this.r=e.x,this.g=e.y,this.b=e.z,this}applyMatrix3(e){let t=this.r,n=this.g,i=this.b,s=e.elements;return this.r=s[0]*t+s[3]*n+s[6]*i,this.g=s[1]*t+s[4]*n+s[7]*i,this.b=s[2]*t+s[5]*n+s[8]*i,this}equals(e){return e.r===this.r&&e.g===this.g&&e.b===this.b}fromArray(e,t=0){return this.r=e[t],this.g=e[t+1],this.b=e[t+2],this}toArray(e=[],t=0){return e[t]=this.r,e[t+1]=this.g,e[t+2]=this.b,e}fromBufferAttribute(e,t){return this.r=e.getX(t),this.g=e.getY(t),this.b=e.getZ(t),this}toJSON(){return this.getHex()}*[Symbol.iterator](){yield this.r,yield this.g,yield this.b}},Se=new H;H.NAMES=ul;var Nn=class extends le{constructor(){super(),this.isScene=!0,this.type="Scene",this.background=null,this.environment=null,this.fog=null,this.backgroundBlurriness=0,this.backgroundIntensity=1,this.backgroundRotation=new ke,this.environmentIntensity=1,this.environmentRotation=new ke,this.overrideMaterial=null,typeof __THREE_DEVTOOLS__<"u"&&__THREE_DEVTOOLS__.dispatchEvent(new CustomEvent("observe",{detail:this}))}copy(e,t){return super.copy(e,t),e.background!==null&&(this.background=e.background.clone()),e.environment!==null&&(this.environment=e.environment.clone()),e.fog!==null&&(this.fog=e.fog.clone()),this.backgroundBlurriness=e.backgroundBlurriness,this.backgroundIntensity=e.backgroundIntensity,this.backgroundRotation.copy(e.backgroundRotation),this.environmentIntensity=e.environmentIntensity,this.environmentRotation.copy(e.environmentRotation),e.overrideMaterial!==null&&(this.overrideMaterial=e.overrideMaterial.clone()),this.matrixAutoUpdate=e.matrixAutoUpdate,this}toJSON(e){let t=super.toJSON(e);return this.fog!==null&&(t.object.fog=this.fog.toJSON()),t.object.backgroundBlurriness=this.backgroundBlurriness,t.object.backgroundIntensity=this.backgroundIntensity,t.object.backgroundRotation=this.backgroundRotation.toArray(),t.object.environmentIntensity=this.environmentIntensity,t.object.environmentRotation=this.environmentRotation.toArray(),t}},Ye=new E,ft=new E,fr=new E,dt=new E,vn=new E,Sn=new E,Sc=new E,dr=new E,pr=new E,mr=new E,gr=new Xe,xr=new Xe,br=new Xe,Bt=class a{constructor(e=new E,t=new E,n=new E){this.a=e,this.b=t,this.c=n}static getNormal(e,t,n,i){i.subVectors(n,t),Ye.subVectors(e,t),i.cross(Ye);let s=i.lengthSq();return s>0?i.multiplyScalar(1/Math.sqrt(s)):i.set(0,0,0)}static getBarycoord(e,t,n,i,s){Ye.subVectors(i,t),ft.subVectors(n,t),fr.subVectors(e,t);let r=Ye.dot(Ye),o=Ye.dot(ft),c=Ye.dot(fr),l=ft.dot(ft),u=ft.dot(fr),h=r*l-o*o;if(h===0)return s.set(0,0,0),null;let f=1/h,d=(l*c-o*u)*f,p=(r*u-o*c)*f;return s.set(1-d-p,p,d)}static containsPoint(e,t,n,i){return this.getBarycoord(e,t,n,i,dt)===null?!1:dt.x>=0&&dt.y>=0&&dt.x+dt.y<=1}static getInterpolation(e,t,n,i,s,r,o,c){return this.getBarycoord(e,t,n,i,dt)===null?(c.x=0,c.y=0,"z"in c&&(c.z=0),"w"in c&&(c.w=0),null):(c.setScalar(0),c.addScaledVector(s,dt.x),c.addScaledVector(r,dt.y),c.addScaledVector(o,dt.z),c)}static getInterpolatedAttribute(e,t,n,i,s,r){return gr.setScalar(0),xr.setScalar(0),br.setScalar(0),gr.fromBufferAttribute(e,t),xr.fromBufferAttribute(e,n),br.fromBufferAttribute(e,i),r.setScalar(0),r.addScaledVector(gr,s.x),r.addScaledVector(xr,s.y),r.addScaledVector(br,s.z),r}static isFrontFacing(e,t,n,i){return Ye.subVectors(n,t),ft.subVectors(e,t),Ye.cross(ft).dot(i)<0}set(e,t,n){return this.a.copy(e),this.b.copy(t),this.c.copy(n),this}setFromPointsAndIndices(e,t,n,i){return this.a.copy(e[t]),this.b.copy(e[n]),this.c.copy(e[i]),this}setFromAttributeAndIndices(e,t,n,i){return this.a.fromBufferAttribute(e,t),this.b.fromBufferAttribute(e,n),this.c.fromBufferAttribute(e,i),this}clone(){return new this.constructor().copy(this)}copy(e){return this.a.copy(e.a),this.b.copy(e.b),this.c.copy(e.c),this}getArea(){return Ye.subVectors(this.c,this.b),ft.subVectors(this.a,this.b),Ye.cross(ft).length()*.5}getMidpoint(e){return e.addVectors(this.a,this.b).add(this.c).multiplyScalar(1/3)}getNormal(e){return a.getNormal(this.a,this.b,this.c,e)}getPlane(e){return e.setFromCoplanarPoints(this.a,this.b,this.c)}getBarycoord(e,t){return a.getBarycoord(e,this.a,this.b,this.c,t)}getInterpolation(e,t,n,i,s){return a.getInterpolation(e,this.a,this.b,this.c,t,n,i,s)}containsPoint(e){return a.containsPoint(e,this.a,this.b,this.c)}isFrontFacing(e){return a.isFrontFacing(this.a,this.b,this.c,e)}intersectsBox(e){return e.intersectsTriangle(this)}closestPointToPoint(e,t){let n=this.a,i=this.b,s=this.c,r,o;vn.subVectors(i,n),Sn.subVectors(s,n),dr.subVectors(e,n);let c=vn.dot(dr),l=Sn.dot(dr);if(c<=0&&l<=0)return t.copy(n);pr.subVectors(e,i);let u=vn.dot(pr),h=Sn.dot(pr);if(u>=0&&h<=u)return t.copy(i);let f=c*h-u*l;if(f<=0&&c>=0&&u<=0)return r=c/(c-u),t.copy(n).addScaledVector(vn,r);mr.subVectors(e,s);let d=vn.dot(mr),p=Sn.dot(mr);if(p>=0&&d<=p)return t.copy(s);let m=d*l-c*p;if(m<=0&&l>=0&&p<=0)return o=l/(l-p),t.copy(n).addScaledVector(Sn,o);let b=u*p-d*h;if(b<=0&&h-u>=0&&d-p>=0)return Sc.subVectors(s,i),o=(h-u)/(h-u+(d-p)),t.copy(i).addScaledVector(Sc,o);let x=1/(b+m+f);return r=m*x,o=f*x,t.copy(n).addScaledVector(vn,r).addScaledVector(Sn,o)}equals(e){return e.a.equals(this.a)&&e.b.equals(this.b)&&e.c.equals(this.c)}},ze=class{constructor(e=new E(1/0,1/0,1/0),t=new E(-1/0,-1/0,-1/0)){this.isBox3=!0,this.min=e,this.max=t}set(e,t){return this.min.copy(e),this.max.copy(t),this}setFromArray(e){this.makeEmpty();for(let t=0,n=e.length;t<n;t+=3)this.expandByPoint(je.fromArray(e,t));return this}setFromBufferAttribute(e){this.makeEmpty();for(let t=0,n=e.count;t<n;t++)this.expandByPoint(je.fromBufferAttribute(e,t));return this}setFromPoints(e){this.makeEmpty();for(let t=0,n=e.length;t<n;t++)this.expandByPoint(e[t]);return this}setFromCenterAndSize(e,t){let n=je.copy(t).multiplyScalar(.5);return this.min.copy(e).sub(n),this.max.copy(e).add(n),this}setFromObject(e,t=!1){return this.makeEmpty(),this.expandByObject(e,t)}clone(){return new this.constructor().copy(this)}copy(e){return this.min.copy(e.min),this.max.copy(e.max),this}makeEmpty(){return this.min.x=this.min.y=this.min.z=1/0,this.max.x=this.max.y=this.max.z=-1/0,this}isEmpty(){return this.max.x<this.min.x||this.max.y<this.min.y||this.max.z<this.min.z}getCenter(e){return this.isEmpty()?e.set(0,0,0):e.addVectors(this.min,this.max).multiplyScalar(.5)}getSize(e){return this.isEmpty()?e.set(0,0,0):e.subVectors(this.max,this.min)}expandByPoint(e){return this.min.min(e),this.max.max(e),this}expandByVector(e){return this.min.sub(e),this.max.add(e),this}expandByScalar(e){return this.min.addScalar(-e),this.max.addScalar(e),this}expandByObject(e,t=!1){e.updateWorldMatrix(!1,!1);let n=e.geometry;if(n!==void 0){let s=n.getAttribute("position");if(t===!0&&s!==void 0&&e.isInstancedMesh!==!0)for(let r=0,o=s.count;r<o;r++)e.isMesh===!0?e.getVertexPosition(r,je):je.fromBufferAttribute(s,r),je.applyMatrix4(e.matrixWorld),this.expandByPoint(je);else e.boundingBox!==void 0?(e.boundingBox===null&&e.computeBoundingBox(),Xi.copy(e.boundingBox)):(n.boundingBox===null&&n.computeBoundingBox(),Xi.copy(n.boundingBox)),Xi.applyMatrix4(e.matrixWorld),this.union(Xi)}let i=e.children;for(let s=0,r=i.length;s<r;s++)this.expandByObject(i[s],t);return this}containsPoint(e){return e.x>=this.min.x&&e.x<=this.max.x&&e.y>=this.min.y&&e.y<=this.max.y&&e.z>=this.min.z&&e.z<=this.max.z}containsBox(e){return this.min.x<=e.min.x&&e.max.x<=this.max.x&&this.min.y<=e.min.y&&e.max.y<=this.max.y&&this.min.z<=e.min.z&&e.max.z<=this.max.z}getParameter(e,t){return t.set((e.x-this.min.x)/(this.max.x-this.min.x),(e.y-this.min.y)/(this.max.y-this.min.y),(e.z-this.min.z)/(this.max.z-this.min.z))}intersectsBox(e){return e.max.x>=this.min.x&&e.min.x<=this.max.x&&e.max.y>=this.min.y&&e.min.y<=this.max.y&&e.max.z>=this.min.z&&e.min.z<=this.max.z}intersectsSphere(e){return this.clampPoint(e.center,je),je.distanceToSquared(e.center)<=e.radius*e.radius}intersectsPlane(e){let t,n;return e.normal.x>0?(t=e.normal.x*this.min.x,n=e.normal.x*this.max.x):(t=e.normal.x*this.max.x,n=e.normal.x*this.min.x),e.normal.y>0?(t+=e.normal.y*this.min.y,n+=e.normal.y*this.max.y):(t+=e.normal.y*this.max.y,n+=e.normal.y*this.min.y),e.normal.z>0?(t+=e.normal.z*this.min.z,n+=e.normal.z*this.max.z):(t+=e.normal.z*this.max.z,n+=e.normal.z*this.min.z),t<=-e.constant&&n>=-e.constant}intersectsTriangle(e){if(this.isEmpty())return!1;this.getCenter(Zn),qi.subVectors(this.max,Zn),Mn.subVectors(e.a,Zn),An.subVectors(e.b,Zn),Tn.subVectors(e.c,Zn),Nt.subVectors(An,Mn),Ft.subVectors(Tn,An),$t.subVectors(Mn,Tn);let t=[0,-Nt.z,Nt.y,0,-Ft.z,Ft.y,0,-$t.z,$t.y,Nt.z,0,-Nt.x,Ft.z,0,-Ft.x,$t.z,0,-$t.x,-Nt.y,Nt.x,0,-Ft.y,Ft.x,0,-$t.y,$t.x,0];return!_r(t,Mn,An,Tn,qi)||(t=[1,0,0,0,1,0,0,0,1],!_r(t,Mn,An,Tn,qi))?!1:(Ki.crossVectors(Nt,Ft),t=[Ki.x,Ki.y,Ki.z],_r(t,Mn,An,Tn,qi))}clampPoint(e,t){return t.copy(e).clamp(this.min,this.max)}distanceToPoint(e){return this.clampPoint(e,je).distanceTo(e)}getBoundingSphere(e){return this.isEmpty()?e.makeEmpty():(this.getCenter(e.center),e.radius=this.getSize(je).length()*.5),e}intersect(e){return this.min.max(e.min),this.max.min(e.max),this.isEmpty()&&this.makeEmpty(),this}union(e){return this.min.min(e.min),this.max.max(e.max),this}applyMatrix4(e){return this.isEmpty()?this:(pt[0].set(this.min.x,this.min.y,this.min.z).applyMatrix4(e),pt[1].set(this.min.x,this.min.y,this.max.z).applyMatrix4(e),pt[2].set(this.min.x,this.max.y,this.min.z).applyMatrix4(e),pt[3].set(this.min.x,this.max.y,this.max.z).applyMatrix4(e),pt[4].set(this.max.x,this.min.y,this.min.z).applyMatrix4(e),pt[5].set(this.max.x,this.min.y,this.max.z).applyMatrix4(e),pt[6].set(this.max.x,this.max.y,this.min.z).applyMatrix4(e),pt[7].set(this.max.x,this.max.y,this.max.z).applyMatrix4(e),this.setFromPoints(pt),this)}translate(e){return this.min.add(e),this.max.add(e),this}equals(e){return e.min.equals(this.min)&&e.max.equals(this.max)}toJSON(){return{min:this.min.toArray(),max:this.max.toArray()}}fromJSON(e){return this.min.fromArray(e.min),this.max.fromArray(e.max),this}},pt=[new E,new E,new E,new E,new E,new E,new E,new E],je=new E,Xi=new ze,Mn=new E,An=new E,Tn=new E,Nt=new E,Ft=new E,$t=new E,Zn=new E,qi=new E,Ki=new E,Qt=new E;function _r(a,e,t,n,i){for(let s=0,r=a.length-3;s<=r;s+=3){Qt.fromArray(a,s);let o=i.x*Math.abs(Qt.x)+i.y*Math.abs(Qt.y)+i.z*Math.abs(Qt.z),c=e.dot(Qt),l=t.dot(Qt),u=n.dot(Qt);if(Math.max(-Math.max(c,l,u),Math.min(c,l,u))>o)return!1}return!0}var de=new E,Yi=new $,Ph=0,ae=class extends Vt{constructor(e,t,n=!1){if(super(),Array.isArray(e))throw new TypeError("THREE.BufferAttribute: array should be a Typed Array.");this.isBufferAttribute=!0,Object.defineProperty(this,"id",{value:Ph++}),this.name="",this.array=e,this.itemSize=t,this.count=e!==void 0?e.length/t:0,this.normalized=n,this.usage=la,this.updateRanges=[],this.gpuType=Ds,this.version=0}onUploadCallback(){}set needsUpdate(e){e===!0&&this.version++}setUsage(e){return this.usage=e,this}addUpdateRange(e,t){this.updateRanges.push({start:e,count:t})}clearUpdateRanges(){this.updateRanges.length=0}copy(e){return this.name=e.name,this.array=new e.array.constructor(e.array),this.itemSize=e.itemSize,this.count=e.count,this.normalized=e.normalized,this.usage=e.usage,this.gpuType=e.gpuType,this}copyAt(e,t,n){e*=this.itemSize,n*=t.itemSize;for(let i=0,s=this.itemSize;i<s;i++)this.array[e+i]=t.array[n+i];return this}copyArray(e){return this.array.set(e),this}applyMatrix3(e){if(this.itemSize===2)for(let t=0,n=this.count;t<n;t++)Yi.fromBufferAttribute(this,t),Yi.applyMatrix3(e),this.setXY(t,Yi.x,Yi.y);else if(this.itemSize===3)for(let t=0,n=this.count;t<n;t++)de.fromBufferAttribute(this,t),de.applyMatrix3(e),this.setXYZ(t,de.x,de.y,de.z);return this}applyMatrix4(e){for(let t=0,n=this.count;t<n;t++)de.fromBufferAttribute(this,t),de.applyMatrix4(e),this.setXYZ(t,de.x,de.y,de.z);return this}applyNormalMatrix(e){for(let t=0,n=this.count;t<n;t++)de.fromBufferAttribute(this,t),de.applyNormalMatrix(e),this.setXYZ(t,de.x,de.y,de.z);return this}transformDirection(e){for(let t=0,n=this.count;t<n;t++)de.fromBufferAttribute(this,t),de.transformDirection(e),this.setXYZ(t,de.x,de.y,de.z);return this}set(e,t=0){return this.array.set(e,t),this}getComponent(e,t){let n=this.array[e*this.itemSize+t];return this.normalized&&(n=Je(n,this.array)),n}setComponent(e,t,n){return this.normalized&&(n=te(n,this.array)),this.array[e*this.itemSize+t]=n,this}getX(e){let t=this.array[e*this.itemSize];return this.normalized&&(t=Je(t,this.array)),t}setX(e,t){return this.normalized&&(t=te(t,this.array)),this.array[e*this.itemSize]=t,this}getY(e){let t=this.array[e*this.itemSize+1];return this.normalized&&(t=Je(t,this.array)),t}setY(e,t){return this.normalized&&(t=te(t,this.array)),this.array[e*this.itemSize+1]=t,this}getZ(e){let t=this.array[e*this.itemSize+2];return this.normalized&&(t=Je(t,this.array)),t}setZ(e,t){return this.normalized&&(t=te(t,this.array)),this.array[e*this.itemSize+2]=t,this}getW(e){let t=this.array[e*this.itemSize+3];return this.normalized&&(t=Je(t,this.array)),t}setW(e,t){return this.normalized&&(t=te(t,this.array)),this.array[e*this.itemSize+3]=t,this}setXY(e,t,n){return e*=this.itemSize,this.normalized&&(t=te(t,this.array),n=te(n,this.array)),this.array[e+0]=t,this.array[e+1]=n,this}setXYZ(e,t,n,i){return e*=this.itemSize,this.normalized&&(t=te(t,this.array),n=te(n,this.array),i=te(i,this.array)),this.array[e+0]=t,this.array[e+1]=n,this.array[e+2]=i,this}setXYZW(e,t,n,i,s){return e*=this.itemSize,this.normalized&&(t=te(t,this.array),n=te(n,this.array),i=te(i,this.array),s=te(s,this.array)),this.array[e+0]=t,this.array[e+1]=n,this.array[e+2]=i,this.array[e+3]=s,this}onUpload(e){return this.onUploadCallback=e,this}clone(){return new this.constructor(this.array,this.itemSize).copy(this)}toJSON(){let e={itemSize:this.itemSize,type:this.array.constructor.name,array:Array.from(this.array),normalized:this.normalized};return e.name=this.name,e.usage=this.usage,e.gpuType=this.gpuType,e}dispose(){this.dispatchEvent({type:"dispose"})}};var ys=class extends ae{constructor(e,t,n){super(new Uint16Array(e),t,n)}};var vs=class extends ae{constructor(e,t,n){super(new Uint32Array(e),t,n)}};var an=class extends ae{constructor(e,t,n){super(new Float32Array(e),t,n)}},Lh=new ze,$n=new E,yr=new E,Le=class{constructor(e=new E,t=-1){this.isSphere=!0,this.center=e,this.radius=t}set(e,t){return this.center.copy(e),this.radius=t,this}setFromPoints(e,t){let n=this.center;t!==void 0?n.copy(t):Lh.setFromPoints(e).getCenter(n);let i=0;for(let s=0,r=e.length;s<r;s++)i=Math.max(i,n.distanceToSquared(e[s]));return this.radius=Math.sqrt(i),this}copy(e){return this.center.copy(e.center),this.radius=e.radius,this}isEmpty(){return this.radius<0}makeEmpty(){return this.center.set(0,0,0),this.radius=-1,this}containsPoint(e){return e.distanceToSquared(this.center)<=this.radius*this.radius}distanceToPoint(e){return e.distanceTo(this.center)-this.radius}intersectsSphere(e){let t=this.radius+e.radius;return e.center.distanceToSquared(this.center)<=t*t}intersectsBox(e){return e.intersectsSphere(this)}intersectsPlane(e){return Math.abs(e.distanceToPoint(this.center))<=this.radius}clampPoint(e,t){let n=this.center.distanceToSquared(e);return t.copy(e),n>this.radius*this.radius&&(t.sub(this.center).normalize(),t.multiplyScalar(this.radius).add(this.center)),t}getBoundingBox(e){return this.isEmpty()?(e.makeEmpty(),e):(e.set(this.center,this.center),e.expandByScalar(this.radius),e)}applyMatrix4(e){return this.center.applyMatrix4(e),this.radius=this.radius*e.getMaxScaleOnAxis(),this}translate(e){return this.center.add(e),this}expandByPoint(e){if(this.isEmpty())return this.center.copy(e),this.radius=0,this;$n.subVectors(e,this.center);let t=$n.lengthSq();if(t>this.radius*this.radius){let n=Math.sqrt(t),i=(n-this.radius)*.5;this.center.addScaledVector($n,i/n),this.radius+=i}return this}union(e){return e.isEmpty()?this:this.isEmpty()?(this.copy(e),this):(this.center.equals(e.center)===!0?this.radius=Math.max(this.radius,e.radius):(yr.subVectors(e.center,this.center).setLength(e.radius),this.expandByPoint($n.copy(e.center).add(yr)),this.expandByPoint($n.copy(e.center).sub(yr))),this)}equals(e){return e.center.equals(this.center)&&e.radius===this.radius}clone(){return new this.constructor().copy(this)}toJSON(){return{radius:this.radius,center:this.center.toArray()}}fromJSON(e){return this.radius=e.radius,this.center.fromArray(e.center),this}},Dh=0,He=new z,vr=new le,wn=new E,Oe=new ze,Qn=new ze,be=new E,nt=class a extends Vt{constructor(){super(),this.isBufferGeometry=!0,Object.defineProperty(this,"id",{value:Dh++}),this.uuid=Ze(),this.name="",this.type="BufferGeometry",this.index=null,this.indirect=null,this.indirectOffset=0,this.attributes={},this.morphAttributes={},this.morphTargetsRelative=!1,this.groups=[],this.boundingBox=null,this.boundingSphere=null,this.drawRange={start:0,count:1/0},this.userData={},this._transformed=!1}getIndex(){return this.index}setIndex(e){return Array.isArray(e)?this.index=new(ih(e)?vs:ys)(e,1):this.index=e,this}setIndirect(e,t=0){return this.indirect=e,this.indirectOffset=t,this}getIndirect(){return this.indirect}getAttribute(e){return this.attributes[e]}setAttribute(e,t){return this.attributes[e]=t,this}deleteAttribute(e){return delete this.attributes[e],this}hasAttribute(e){return this.attributes[e]!==void 0}addGroup(e,t,n=0){this.groups.push({start:e,count:t,materialIndex:n})}clearGroups(){this.groups=[]}setDrawRange(e,t){this.drawRange.start=e,this.drawRange.count=t}applyMatrix4(e){let t=this.attributes.position;t!==void 0&&(t.applyMatrix4(e),t.needsUpdate=!0);let n=this.attributes.normal;if(n!==void 0){let s=new G().getNormalMatrix(e);n.applyNormalMatrix(s),n.needsUpdate=!0}let i=this.attributes.tangent;return i!==void 0&&(i.transformDirection(e),i.needsUpdate=!0),this.boundingBox!==null&&this.computeBoundingBox(),this.boundingSphere!==null&&this.computeBoundingSphere(),this._transformed=!0,this}applyQuaternion(e){return He.makeRotationFromQuaternion(e),this.applyMatrix4(He),this}rotateX(e){return He.makeRotationX(e),this.applyMatrix4(He),this}rotateY(e){return He.makeRotationY(e),this.applyMatrix4(He),this}rotateZ(e){return He.makeRotationZ(e),this.applyMatrix4(He),this}translate(e,t,n){return He.makeTranslation(e,t,n),this.applyMatrix4(He),this}scale(e,t,n){return He.makeScale(e,t,n),this.applyMatrix4(He),this}lookAt(e){return vr.lookAt(e),vr.updateMatrix(),this.applyMatrix4(vr.matrix),this}center(){return this.computeBoundingBox(),this.boundingBox.getCenter(wn).negate(),this.translate(wn.x,wn.y,wn.z),this}setFromPoints(e){let t=this.getAttribute("position");if(t===void 0){let n=[];for(let i=0,s=e.length;i<s;i++){let r=e[i];n.push(r.x,r.y,r.z||0)}this.setAttribute("position",new an(n,3))}else{let n=Math.min(e.length,t.count);for(let i=0;i<n;i++){let s=e[i];t.setXYZ(i,s.x,s.y,s.z||0)}e.length>t.count&&ne("BufferGeometry: Buffer size too small for points data. Use .dispose() and create a new geometry."),t.needsUpdate=!0}return this}computeBoundingBox(){this.boundingBox===null&&(this.boundingBox=new ze);let e=this.attributes.position,t=this.morphAttributes.position;if(e&&e.isGLBufferAttribute){oe("BufferGeometry.computeBoundingBox(): GLBufferAttribute requires a manual bounding box.",this),this.boundingBox.set(new E(-1/0,-1/0,-1/0),new E(1/0,1/0,1/0));return}if(e!==void 0){if(this.boundingBox.setFromBufferAttribute(e),t)for(let n=0,i=t.length;n<i;n++){let s=t[n];Oe.setFromBufferAttribute(s),this.morphTargetsRelative?(be.addVectors(this.boundingBox.min,Oe.min),this.boundingBox.expandByPoint(be),be.addVectors(this.boundingBox.max,Oe.max),this.boundingBox.expandByPoint(be)):(this.boundingBox.expandByPoint(Oe.min),this.boundingBox.expandByPoint(Oe.max))}}else this.boundingBox.makeEmpty();(isNaN(this.boundingBox.min.x)||isNaN(this.boundingBox.min.y)||isNaN(this.boundingBox.min.z))&&oe('BufferGeometry.computeBoundingBox(): Computed min/max have NaN values. The "position" attribute is likely to have NaN values.',this)}computeBoundingSphere(){this.boundingSphere===null&&(this.boundingSphere=new Le);let e=this.attributes.position,t=this.morphAttributes.position;if(e&&e.isGLBufferAttribute){oe("BufferGeometry.computeBoundingSphere(): GLBufferAttribute requires a manual bounding sphere.",this),this.boundingSphere.set(new E,1/0);return}if(e){let n=this.boundingSphere.center;if(Oe.setFromBufferAttribute(e),t)for(let s=0,r=t.length;s<r;s++){let o=t[s];Qn.setFromBufferAttribute(o),this.morphTargetsRelative?(be.addVectors(Oe.min,Qn.min),Oe.expandByPoint(be),be.addVectors(Oe.max,Qn.max),Oe.expandByPoint(be)):(Oe.expandByPoint(Qn.min),Oe.expandByPoint(Qn.max))}Oe.getCenter(n);let i=0;for(let s=0,r=e.count;s<r;s++)be.fromBufferAttribute(e,s),i=Math.max(i,n.distanceToSquared(be));if(t)for(let s=0,r=t.length;s<r;s++){let o=t[s],c=this.morphTargetsRelative;for(let l=0,u=o.count;l<u;l++)be.fromBufferAttribute(o,l),c&&(wn.fromBufferAttribute(e,l),be.add(wn)),i=Math.max(i,n.distanceToSquared(be))}this.boundingSphere.radius=Math.sqrt(i),isNaN(this.boundingSphere.radius)&&oe('BufferGeometry.computeBoundingSphere(): Computed radius is NaN. The "position" attribute is likely to have NaN values.',this)}}computeTangents(){let e=this.index,t=this.attributes;if(e===null||t.position===void 0||t.normal===void 0||t.uv===void 0){oe("BufferGeometry: .computeTangents() failed. Missing required attributes (index, position, normal or uv)");return}let n=t.position,i=t.normal,s=t.uv,r=this.getAttribute("tangent");(r===void 0||r.count!==n.count)&&(r=new ae(new Float32Array(4*n.count),4),this.setAttribute("tangent",r));let o=[],c=[];for(let g=0;g<n.count;g++)o[g]=new E,c[g]=new E;let l=new E,u=new E,h=new E,f=new $,d=new $,p=new $,m=new E,b=new E;function x(g,w,R){l.fromBufferAttribute(n,g),u.fromBufferAttribute(n,w),h.fromBufferAttribute(n,R),f.fromBufferAttribute(s,g),d.fromBufferAttribute(s,w),p.fromBufferAttribute(s,R),u.sub(l),h.sub(l),d.sub(f),p.sub(f);let C=1/(d.x*p.y-p.x*d.y);isFinite(C)&&(m.copy(u).multiplyScalar(p.y).addScaledVector(h,-d.y).multiplyScalar(C),b.copy(h).multiplyScalar(d.x).addScaledVector(u,-p.x).multiplyScalar(C),o[g].add(m),o[w].add(m),o[R].add(m),c[g].add(b),c[w].add(b),c[R].add(b))}let v=this.groups;v.length===0&&(v=[{start:0,count:e.count}]);for(let g=0,w=v.length;g<w;++g){let R=v[g],C=R.start,N=R.count;for(let L=C,F=C+N;L<F;L+=3)x(e.getX(L+0),e.getX(L+1),e.getX(L+2))}let S=new E,y=new E,T=new E,M=new E;function A(g){T.fromBufferAttribute(i,g),M.copy(T);let w=o[g];S.copy(w),S.sub(T.multiplyScalar(T.dot(w))).normalize(),y.crossVectors(M,w);let C=y.dot(c[g])<0?-1:1;r.setXYZW(g,S.x,S.y,S.z,C)}for(let g=0,w=v.length;g<w;++g){let R=v[g],C=R.start,N=R.count;for(let L=C,F=C+N;L<F;L+=3)A(e.getX(L+0)),A(e.getX(L+1)),A(e.getX(L+2))}this._transformed=!0}computeVertexNormals(){let e=this.index,t=this.getAttribute("position");if(t!==void 0){let n=this.getAttribute("normal");if(n===void 0||n.count!==t.count)n=new ae(new Float32Array(t.count*3),3),this.setAttribute("normal",n);else for(let f=0,d=n.count;f<d;f++)n.setXYZ(f,0,0,0);let i=new E,s=new E,r=new E,o=new E,c=new E,l=new E,u=new E,h=new E;if(e)for(let f=0,d=e.count;f<d;f+=3){let p=e.getX(f+0),m=e.getX(f+1),b=e.getX(f+2);i.fromBufferAttribute(t,p),s.fromBufferAttribute(t,m),r.fromBufferAttribute(t,b),u.subVectors(r,s),h.subVectors(i,s),u.cross(h),o.fromBufferAttribute(n,p),c.fromBufferAttribute(n,m),l.fromBufferAttribute(n,b),o.add(u),c.add(u),l.add(u),n.setXYZ(p,o.x,o.y,o.z),n.setXYZ(m,c.x,c.y,c.z),n.setXYZ(b,l.x,l.y,l.z)}else for(let f=0,d=t.count;f<d;f+=3)i.fromBufferAttribute(t,f+0),s.fromBufferAttribute(t,f+1),r.fromBufferAttribute(t,f+2),u.subVectors(r,s),h.subVectors(i,s),u.cross(h),n.setXYZ(f+0,u.x,u.y,u.z),n.setXYZ(f+1,u.x,u.y,u.z),n.setXYZ(f+2,u.x,u.y,u.z);this.normalizeNormals(),n.needsUpdate=!0}}normalizeNormals(){let e=this.attributes.normal;for(let t=0,n=e.count;t<n;t++)be.fromBufferAttribute(e,t),be.normalize(),e.setXYZ(t,be.x,be.y,be.z)}toNonIndexed(){function e(o,c){let l=o.array,u=o.itemSize,h=o.normalized,f=new l.constructor(c.length*u),d=0,p=0;for(let m=0,b=c.length;m<b;m++){o.isInterleavedBufferAttribute?d=c[m]*o.data.stride+o.offset:d=c[m]*u;for(let x=0;x<u;x++)f[p++]=l[d++]}return new ae(f,u,h)}if(this.index===null)return ne("BufferGeometry.toNonIndexed(): BufferGeometry is already non-indexed."),this;let t=new a,n=this.index.array,i=this.attributes;for(let o in i){let c=i[o],l=e(c,n);t.setAttribute(o,l)}let s=this.morphAttributes;for(let o in s){let c=[],l=s[o];for(let u=0,h=l.length;u<h;u++){let f=l[u],d=e(f,n);c.push(d)}t.morphAttributes[o]=c}t.morphTargetsRelative=this.morphTargetsRelative;let r=this.groups;for(let o=0,c=r.length;o<c;o++){let l=r[o];t.addGroup(l.start,l.count,l.materialIndex)}return t}toJSON(){let e={metadata:{version:4.7,type:"BufferGeometry",generator:"BufferGeometry.toJSON"}};if(e.uuid=this.uuid,e.type=this.parameters!==void 0&&this._transformed===!0?"BufferGeometry":this.type,e.name=this.name,Object.keys(this.userData).length>0&&(e.userData=this.userData),this.parameters!==void 0&&this._transformed!==!0){let c=this.parameters;for(let l in c)c[l]!==void 0&&(e[l]=c[l]);return e}e.data={attributes:{}};let t=this.index;t!==null&&(e.data.index={type:t.array.constructor.name,array:Array.prototype.slice.call(t.array)});let n=this.attributes;for(let c in n){let l=n[c];e.data.attributes[c]=l.toJSON(e.data)}let i={},s=!1;for(let c in this.morphAttributes){let l=this.morphAttributes[c],u=[];for(let h=0,f=l.length;h<f;h++){let d=l[h];u.push(d.toJSON(e.data))}u.length>0&&(i[c]=u,s=!0)}s&&(e.data.morphAttributes=i,e.data.morphTargetsRelative=this.morphTargetsRelative);let r=this.groups;r.length>0&&(e.data.groups=JSON.parse(JSON.stringify(r)));let o=this.boundingSphere;return o!==null&&(e.data.boundingSphere=o.toJSON()),e}clone(){return new this.constructor().copy(this)}copy(e){this.index=null,this.attributes={},this.morphAttributes={},this.groups=[],this.boundingBox=null,this.boundingSphere=null;let t={};this.name=e.name;let n=e.index;n!==null&&this.setIndex(n.clone());let i=e.attributes;for(let l in i){let u=i[l];this.setAttribute(l,u.clone(t))}let s=e.morphAttributes;for(let l in s){let u=[],h=s[l];for(let f=0,d=h.length;f<d;f++)u.push(h[f].clone(t));this.morphAttributes[l]=u}this.morphTargetsRelative=e.morphTargetsRelative;let r=e.groups;for(let l=0,u=r.length;l<u;l++){let h=r[l];this.addGroup(h.start,h.count,h.materialIndex)}let o=e.boundingBox;o!==null&&(this.boundingBox=o.clone());let c=e.boundingSphere;return c!==null&&(this.boundingSphere=c.clone()),this.drawRange.start=e.drawRange.start,this.drawRange.count=e.drawRange.count,this.userData=e.userData,this._transformed=e._transformed,this}dispose(){this.dispatchEvent({type:"dispose"})}},Fn=class{constructor(e,t){this.isInterleavedBuffer=!0,this.array=e,this.stride=t,this.count=e!==void 0?e.length/t:0,this.usage=la,this.updateRanges=[],this.version=0,this.uuid=Ze()}onUploadCallback(){}set needsUpdate(e){e===!0&&this.version++}setUsage(e){return this.usage=e,this}addUpdateRange(e,t){this.updateRanges.push({start:e,count:t})}clearUpdateRanges(){this.updateRanges.length=0}copy(e){return this.array=new e.array.constructor(e.array),this.count=e.count,this.stride=e.stride,this.usage=e.usage,this}copyAt(e,t,n){e*=this.stride,n*=t.stride;for(let i=0,s=this.stride;i<s;i++)this.array[e+i]=t.array[n+i];return this}set(e,t=0){return this.array.set(e,t),this}clone(e){e.arrayBuffers===void 0&&(e.arrayBuffers={}),this.array.buffer._uuid===void 0&&(this.array.buffer._uuid=Ze()),e.arrayBuffers[this.array.buffer._uuid]===void 0&&(e.arrayBuffers[this.array.buffer._uuid]=this.array.slice(0).buffer);let t=new this.array.constructor(e.arrayBuffers[this.array.buffer._uuid]),n=new this.constructor(t,this.stride);return n.setUsage(this.usage),n}onUpload(e){return this.onUploadCallback=e,this}toJSON(e){e.arrayBuffers===void 0&&(e.arrayBuffers={}),this.array.buffer._uuid===void 0&&(this.array.buffer._uuid=Ze()),e.arrayBuffers[this.array.buffer._uuid]===void 0&&(e.arrayBuffers[this.array.buffer._uuid]=Array.from(new Uint32Array(this.array.buffer)));let t={uuid:this.uuid,buffer:this.array.buffer._uuid,type:this.array.constructor.name,stride:this.stride};return t.usage=this.usage,t}},Re=new E,Un=class a{constructor(e,t,n,i=!1){this.isInterleavedBufferAttribute=!0,this.name="",this.data=e,this.itemSize=t,this.offset=n,this.normalized=i}get count(){return this.data.count}get array(){return this.data.array}set needsUpdate(e){this.data.needsUpdate=e}applyMatrix4(e){for(let t=0,n=this.data.count;t<n;t++)Re.fromBufferAttribute(this,t),Re.applyMatrix4(e),this.setXYZ(t,Re.x,Re.y,Re.z);return this}applyNormalMatrix(e){for(let t=0,n=this.count;t<n;t++)Re.fromBufferAttribute(this,t),Re.applyNormalMatrix(e),this.setXYZ(t,Re.x,Re.y,Re.z);return this}transformDirection(e){for(let t=0,n=this.count;t<n;t++)Re.fromBufferAttribute(this,t),Re.transformDirection(e),this.setXYZ(t,Re.x,Re.y,Re.z);return this}getComponent(e,t){let n=this.array[e*this.data.stride+this.offset+t];return this.normalized&&(n=Je(n,this.array)),n}setComponent(e,t,n){return this.normalized&&(n=te(n,this.array)),this.data.array[e*this.data.stride+this.offset+t]=n,this}setX(e,t){return this.normalized&&(t=te(t,this.array)),this.data.array[e*this.data.stride+this.offset]=t,this}setY(e,t){return this.normalized&&(t=te(t,this.array)),this.data.array[e*this.data.stride+this.offset+1]=t,this}setZ(e,t){return this.normalized&&(t=te(t,this.array)),this.data.array[e*this.data.stride+this.offset+2]=t,this}setW(e,t){return this.normalized&&(t=te(t,this.array)),this.data.array[e*this.data.stride+this.offset+3]=t,this}getX(e){let t=this.data.array[e*this.data.stride+this.offset];return this.normalized&&(t=Je(t,this.array)),t}getY(e){let t=this.data.array[e*this.data.stride+this.offset+1];return this.normalized&&(t=Je(t,this.array)),t}getZ(e){let t=this.data.array[e*this.data.stride+this.offset+2];return this.normalized&&(t=Je(t,this.array)),t}getW(e){let t=this.data.array[e*this.data.stride+this.offset+3];return this.normalized&&(t=Je(t,this.array)),t}setXY(e,t,n){return e=e*this.data.stride+this.offset,this.normalized&&(t=te(t,this.array),n=te(n,this.array)),this.data.array[e+0]=t,this.data.array[e+1]=n,this}setXYZ(e,t,n,i){return e=e*this.data.stride+this.offset,this.normalized&&(t=te(t,this.array),n=te(n,this.array),i=te(i,this.array)),this.data.array[e+0]=t,this.data.array[e+1]=n,this.data.array[e+2]=i,this}setXYZW(e,t,n,i,s){return e=e*this.data.stride+this.offset,this.normalized&&(t=te(t,this.array),n=te(n,this.array),i=te(i,this.array),s=te(s,this.array)),this.data.array[e+0]=t,this.data.array[e+1]=n,this.data.array[e+2]=i,this.data.array[e+3]=s,this}clone(e){if(e===void 0){Hr("InterleavedBufferAttribute.clone(): Cloning an interleaved buffer attribute will de-interleave buffer data.");let t=[];for(let n=0;n<this.count;n++){let i=n*this.data.stride+this.offset;for(let s=0;s<this.itemSize;s++)t.push(this.data.array[i+s])}return new ae(new this.array.constructor(t),this.itemSize,this.normalized)}else return e.interleavedBuffers===void 0&&(e.interleavedBuffers={}),e.interleavedBuffers[this.data.uuid]===void 0&&(e.interleavedBuffers[this.data.uuid]=this.data.clone(e)),new a(e.interleavedBuffers[this.data.uuid],this.itemSize,this.offset,this.normalized)}toJSON(e){if(e===void 0){Hr("InterleavedBufferAttribute.toJSON(): Serializing an interleaved buffer attribute will de-interleave buffer data.");let t=[];for(let n=0;n<this.count;n++){let i=n*this.data.stride+this.offset;for(let s=0;s<this.itemSize;s++)t.push(this.data.array[i+s])}return{itemSize:this.itemSize,type:this.array.constructor.name,array:t,normalized:this.normalized}}else return e.interleavedBuffers===void 0&&(e.interleavedBuffers={}),e.interleavedBuffers[this.data.uuid]===void 0&&(e.interleavedBuffers[this.data.uuid]=this.data.toJSON(e)),{isInterleavedBufferAttribute:!0,itemSize:this.itemSize,data:this.data.uuid,offset:this.offset,normalized:this.normalized}}},Sr=new E,Nh=new E,Fh=new G,et=class{constructor(e=new E(1,0,0),t=0){this.isPlane=!0,this.normal=e,this.constant=t}set(e,t){return this.normal.copy(e),this.constant=t,this}setComponents(e,t,n,i){return this.normal.set(e,t,n),this.constant=i,this}setFromNormalAndCoplanarPoint(e,t){return this.normal.copy(e),this.constant=-t.dot(this.normal),this}setFromCoplanarPoints(e,t,n){let i=Sr.subVectors(n,t).cross(Nh.subVectors(e,t)).normalize();return this.setFromNormalAndCoplanarPoint(i,e),this}copy(e){return this.normal.copy(e.normal),this.constant=e.constant,this}normalize(){let e=1/this.normal.length();return this.normal.multiplyScalar(e),this.constant*=e,this}negate(){return this.constant*=-1,this.normal.negate(),this}distanceToPoint(e){return this.normal.dot(e)+this.constant}distanceToSphere(e){return this.distanceToPoint(e.center)-e.radius}projectPoint(e,t){return t.copy(e).addScaledVector(this.normal,-this.distanceToPoint(e))}intersectLine(e,t,n=!0){let i=e.delta(Sr),s=this.normal.dot(i);if(s===0)return this.distanceToPoint(e.start)===0?t.copy(e.start):null;let r=-(e.start.dot(this.normal)+this.constant)/s;return n===!0&&(r<0||r>1)?null:t.copy(e.start).addScaledVector(i,r)}intersectsLine(e){let t=this.distanceToPoint(e.start),n=this.distanceToPoint(e.end);return t<0&&n>0||n<0&&t>0}intersectsBox(e){return e.intersectsPlane(this)}intersectsSphere(e){return e.intersectsPlane(this)}coplanarPoint(e){return e.copy(this.normal).multiplyScalar(-this.constant)}applyMatrix4(e,t){let n=t||Fh.getNormalMatrix(e),i=this.coplanarPoint(Sr).applyMatrix4(e),s=this.normal.applyMatrix3(n).normalize();return this.constant=-i.dot(s),this}translate(e){return this.constant-=e.dot(this.normal),this}equals(e){return e.normal.equals(this.normal)&&e.constant===this.constant}clone(){return new this.constructor().copy(this)}toJSON(){return{normal:this.normal.toArray(),constant:this.constant}}fromJSON(e){return this.normal.fromArray(e.normal),this.constant=e.constant,this}},Uh=0,$e=class extends Vt{constructor(){super(),this.isMaterial=!0,Object.defineProperty(this,"id",{value:Uh++}),this.uuid=Ze(),this.name="",this.type="Material",this.blending=Jc,this.side=Si,this.vertexColors=!1,this.opacity=1,this.transparent=!1,this.alphaHash=!1,this.blendSrc=$c,this.blendDst=Qc,this.blendEquation=Zc,this.blendSrcAlpha=null,this.blendDstAlpha=null,this.blendEquationAlpha=null,this.blendColor=new H(0,0,0),this.blendAlpha=0,this.depthFunc=xs,this.depthTest=!0,this.depthWrite=!0,this.stencilWriteMask=255,this.stencilFunc=cl,this.stencilRef=0,this.stencilFuncMask=255,this.stencilFail=ms,this.stencilZFail=ms,this.stencilZPass=ms,this.stencilWrite=!1,this.clippingPlanes=null,this.clipIntersection=!1,this.clipShadows=!1,this.shadowSide=null,this.colorWrite=!0,this.precision=null,this.polygonOffset=!1,this.polygonOffsetFactor=0,this.polygonOffsetUnits=0,this.dithering=!1,this.alphaToCoverage=!1,this.premultipliedAlpha=!1,this.forceSinglePass=!1,this.allowOverride=!0,this.visible=!0,this.toneMapped=!0,this.userData={},this.version=0,this._alphaTest=0}get alphaTest(){return this._alphaTest}set alphaTest(e){this._alphaTest>0!=e>0&&this.version++,this._alphaTest=e}onBeforeRender(){}onBeforeCompile(){}customProgramCacheKey(){return this.onBeforeCompile.toString()}setValues(e){if(e!==void 0)for(let t in e){let n=e[t];if(n===void 0){ne(`Material: parameter '${t}' has value of undefined.`);continue}let i=this[t];if(i===void 0){ne(`Material: '${t}' is not a property of THREE.${this.type}.`);continue}i&&i.isColor?i.set(n):i&&i.isVector2&&n&&n.isVector2||i&&i.isEuler&&n&&n.isEuler||i&&i.isVector3&&n&&n.isVector3?i.copy(n):this[t]=n}}toJSON(e){let t=e===void 0||typeof e=="string";t&&(e={textures:{},images:{}});let n={metadata:{version:4.7,type:"Material",generator:"Material.toJSON"}};n.uuid=this.uuid,n.type=this.type,n.blending=this.blending,n.side=this.side,n.shadowSide=this.shadowSide,n.vertexColors=this.vertexColors,n.opacity=this.opacity,n.transparent=this.transparent,n.blendSrc=this.blendSrc,n.blendDst=this.blendDst,n.blendEquation=this.blendEquation,n.blendSrcAlpha=this.blendSrcAlpha,n.blendDstAlpha=this.blendDstAlpha,n.blendEquationAlpha=this.blendEquationAlpha,n.blendColor=this.blendColor.getHex(),n.blendAlpha=this.blendAlpha,n.depthFunc=this.depthFunc,n.depthTest=this.depthTest,n.depthWrite=this.depthWrite,n.colorWrite=this.colorWrite,n.clipIntersection=this.clipIntersection,n.clipShadows=this.clipShadows,n.stencilWriteMask=this.stencilWriteMask,n.stencilFunc=this.stencilFunc,n.stencilRef=this.stencilRef,n.stencilFuncMask=this.stencilFuncMask,n.stencilFail=this.stencilFail,n.stencilZFail=this.stencilZFail,n.stencilZPass=this.stencilZPass,n.stencilWrite=this.stencilWrite,n.polygonOffset=this.polygonOffset,n.polygonOffsetFactor=this.polygonOffsetFactor,n.polygonOffsetUnits=this.polygonOffsetUnits,n.dithering=this.dithering,n.alphaTest=this.alphaTest,n.alphaHash=this.alphaHash,n.alphaToCoverage=this.alphaToCoverage,n.premultipliedAlpha=this.premultipliedAlpha,n.forceSinglePass=this.forceSinglePass,n.allowOverride=this.allowOverride,n.visible=this.visible,n.toneMapped=this.toneMapped,n.name=this.name,this.color&&this.color.isColor&&(n.color=this.color.getHex()),this.roughness!==void 0&&(n.roughness=this.roughness),this.metalness!==void 0&&(n.metalness=this.metalness),this.sheen!==void 0&&(n.sheen=this.sheen),this.sheenColor&&this.sheenColor.isColor&&(n.sheenColor=this.sheenColor.getHex()),this.sheenRoughness!==void 0&&(n.sheenRoughness=this.sheenRoughness),this.emissive&&this.emissive.isColor&&(n.emissive=this.emissive.getHex()),this.emissiveIntensity!==void 0&&(n.emissiveIntensity=this.emissiveIntensity),this.specular&&this.specular.isColor&&(n.specular=this.specular.getHex()),this.specularIntensity!==void 0&&(n.specularIntensity=this.specularIntensity),this.specularColor&&this.specularColor.isColor&&(n.specularColor=this.specularColor.getHex()),this.shininess!==void 0&&(n.shininess=this.shininess),this.clearcoat!==void 0&&(n.clearcoat=this.clearcoat),this.clearcoatRoughness!==void 0&&(n.clearcoatRoughness=this.clearcoatRoughness),this.clearcoatMap&&this.clearcoatMap.isTexture&&(n.clearcoatMap=this.clearcoatMap.toJSON(e).uuid),this.clearcoatRoughnessMap&&this.clearcoatRoughnessMap.isTexture&&(n.clearcoatRoughnessMap=this.clearcoatRoughnessMap.toJSON(e).uuid),this.clearcoatNormalMap&&this.clearcoatNormalMap.isTexture&&(n.clearcoatNormalMap=this.clearcoatNormalMap.toJSON(e).uuid,n.clearcoatNormalScale=this.clearcoatNormalScale.toArray()),this.sheenColorMap&&this.sheenColorMap.isTexture&&(n.sheenColorMap=this.sheenColorMap.toJSON(e).uuid),this.sheenRoughnessMap&&this.sheenRoughnessMap.isTexture&&(n.sheenRoughnessMap=this.sheenRoughnessMap.toJSON(e).uuid),this.dispersion!==void 0&&(n.dispersion=this.dispersion),this.retroreflectivity!==void 0&&(n.retroreflectivity=this.retroreflectivity),this.iridescence!==void 0&&(n.iridescence=this.iridescence),this.iridescenceIOR!==void 0&&(n.iridescenceIOR=this.iridescenceIOR),this.iridescenceThicknessRange!==void 0&&(n.iridescenceThicknessRange=this.iridescenceThicknessRange),this.iridescenceMap&&this.iridescenceMap.isTexture&&(n.iridescenceMap=this.iridescenceMap.toJSON(e).uuid),this.iridescenceThicknessMap&&this.iridescenceThicknessMap.isTexture&&(n.iridescenceThicknessMap=this.iridescenceThicknessMap.toJSON(e).uuid),this.anisotropy!==void 0&&(n.anisotropy=this.anisotropy),this.anisotropyRotation!==void 0&&(n.anisotropyRotation=this.anisotropyRotation),this.anisotropyMap&&this.anisotropyMap.isTexture&&(n.anisotropyMap=this.anisotropyMap.toJSON(e).uuid),this.map&&this.map.isTexture&&(n.map=this.map.toJSON(e).uuid),this.matcap&&this.matcap.isTexture&&(n.matcap=this.matcap.toJSON(e).uuid),this.alphaMap&&this.alphaMap.isTexture&&(n.alphaMap=this.alphaMap.toJSON(e).uuid),this.lightMap&&this.lightMap.isTexture&&(n.lightMap=this.lightMap.toJSON(e).uuid,n.lightMapIntensity=this.lightMapIntensity),this.aoMap&&this.aoMap.isTexture&&(n.aoMap=this.aoMap.toJSON(e).uuid,n.aoMapIntensity=this.aoMapIntensity),this.bumpMap&&this.bumpMap.isTexture&&(n.bumpMap=this.bumpMap.toJSON(e).uuid,n.bumpScale=this.bumpScale),this.normalMap&&this.normalMap.isTexture&&(n.normalMap=this.normalMap.toJSON(e).uuid,n.normalMapType=this.normalMapType,n.normalScale=this.normalScale.toArray()),this.displacementMap&&this.displacementMap.isTexture&&(n.displacementMap=this.displacementMap.toJSON(e).uuid,n.displacementScale=this.displacementScale,n.displacementBias=this.displacementBias),this.roughnessMap&&this.roughnessMap.isTexture&&(n.roughnessMap=this.roughnessMap.toJSON(e).uuid),this.metalnessMap&&this.metalnessMap.isTexture&&(n.metalnessMap=this.metalnessMap.toJSON(e).uuid),this.emissiveMap&&this.emissiveMap.isTexture&&(n.emissiveMap=this.emissiveMap.toJSON(e).uuid),this.specularMap&&this.specularMap.isTexture&&(n.specularMap=this.specularMap.toJSON(e).uuid),this.specularIntensityMap&&this.specularIntensityMap.isTexture&&(n.specularIntensityMap=this.specularIntensityMap.toJSON(e).uuid),this.specularColorMap&&this.specularColorMap.isTexture&&(n.specularColorMap=this.specularColorMap.toJSON(e).uuid),this.envMap&&this.envMap.isTexture&&(n.envMap=this.envMap.toJSON(e).uuid,this.combine!==void 0&&(n.combine=this.combine)),this.envMapRotation!==void 0&&(n.envMapRotation=this.envMapRotation.toArray()),this.envMapIntensity!==void 0&&(n.envMapIntensity=this.envMapIntensity),this.reflectivity!==void 0&&(n.reflectivity=this.reflectivity),this.refractionRatio!==void 0&&(n.refractionRatio=this.refractionRatio),this.gradientMap&&this.gradientMap.isTexture&&(n.gradientMap=this.gradientMap.toJSON(e).uuid),this.transmission!==void 0&&(n.transmission=this.transmission),this.transmissionMap&&this.transmissionMap.isTexture&&(n.transmissionMap=this.transmissionMap.toJSON(e).uuid),this.thickness!==void 0&&(n.thickness=this.thickness),this.thicknessMap&&this.thicknessMap.isTexture&&(n.thicknessMap=this.thicknessMap.toJSON(e).uuid),this.attenuationDistance!==void 0&&(n.attenuationDistance=this.attenuationDistance),this.attenuationColor!==void 0&&(n.attenuationColor=this.attenuationColor.getHex()),this.size!==void 0&&(n.size=this.size),this.sizeAttenuation!==void 0&&(n.sizeAttenuation=this.sizeAttenuation),Array.isArray(this.clippingPlanes)&&this.clippingPlanes.length>0&&(n.clippingPlanes=this.clippingPlanes.map(s=>s.toJSON())),this.rotation!==void 0&&(n.rotation=this.rotation),this.depthPacking!==void 0&&(n.depthPacking=this.depthPacking),this.linewidth!==void 0&&(n.linewidth=this.linewidth),this.linecap!==void 0&&(n.linecap=this.linecap),this.linejoin!==void 0&&(n.linejoin=this.linejoin),this.dashSize!==void 0&&(n.dashSize=this.dashSize),this.gapSize!==void 0&&(n.gapSize=this.gapSize),this.scale!==void 0&&(n.scale=this.scale),this.wireframe!==void 0&&(n.wireframe=this.wireframe),this.wireframeLinewidth!==void 0&&(n.wireframeLinewidth=this.wireframeLinewidth),this.wireframeLinecap!==void 0&&(n.wireframeLinecap=this.wireframeLinecap),this.wireframeLinejoin!==void 0&&(n.wireframeLinejoin=this.wireframeLinejoin),this.flatShading!==void 0&&(n.flatShading=this.flatShading),this.fog!==void 0&&(n.fog=this.fog),Object.keys(this.userData).length>0&&(n.userData=this.userData);function i(s){let r=[];for(let o in s){let c=s[o];delete c.metadata,r.push(c)}return r}if(t){let s=i(e.textures),r=i(e.images);s.length>0&&(n.textures=s),r.length>0&&(n.images=r)}return n}fromJSON(e,t){if(e.uuid!==void 0&&(this.uuid=e.uuid),e.name!==void 0&&(this.name=e.name),e.color!==void 0&&this.color!==void 0&&this.color.setHex(e.color),e.roughness!==void 0&&(this.roughness=e.roughness),e.metalness!==void 0&&(this.metalness=e.metalness),e.sheen!==void 0&&(this.sheen=e.sheen),e.sheenColor!==void 0&&(this.sheenColor=new H().setHex(e.sheenColor)),e.sheenRoughness!==void 0&&(this.sheenRoughness=e.sheenRoughness),e.emissive!==void 0&&this.emissive!==void 0&&this.emissive.setHex(e.emissive),e.specular!==void 0&&this.specular!==void 0&&this.specular.setHex(e.specular),e.specularIntensity!==void 0&&(this.specularIntensity=e.specularIntensity),e.specularColor!==void 0&&this.specularColor!==void 0&&this.specularColor.setHex(e.specularColor),e.shininess!==void 0&&(this.shininess=e.shininess),e.clearcoat!==void 0&&(this.clearcoat=e.clearcoat),e.clearcoatRoughness!==void 0&&(this.clearcoatRoughness=e.clearcoatRoughness),e.dispersion!==void 0&&(this.dispersion=e.dispersion),e.retroreflectivity!==void 0&&(this.retroreflectivity=e.retroreflectivity),e.iridescence!==void 0&&(this.iridescence=e.iridescence),e.iridescenceIOR!==void 0&&(this.iridescenceIOR=e.iridescenceIOR),e.iridescenceThicknessRange!==void 0&&(this.iridescenceThicknessRange=e.iridescenceThicknessRange),e.transmission!==void 0&&(this.transmission=e.transmission),e.thickness!==void 0&&(this.thickness=e.thickness),e.attenuationDistance!==void 0&&(this.attenuationDistance=e.attenuationDistance),e.attenuationColor!==void 0&&this.attenuationColor!==void 0&&this.attenuationColor.setHex(e.attenuationColor),e.anisotropy!==void 0&&(this.anisotropy=e.anisotropy),e.anisotropyRotation!==void 0&&(this.anisotropyRotation=e.anisotropyRotation),e.fog!==void 0&&(this.fog=e.fog),e.flatShading!==void 0&&(this.flatShading=e.flatShading),e.blending!==void 0&&(this.blending=e.blending),e.combine!==void 0&&(this.combine=e.combine),e.side!==void 0&&(this.side=e.side),e.shadowSide!==void 0&&(this.shadowSide=e.shadowSide),e.opacity!==void 0&&(this.opacity=e.opacity),e.transparent!==void 0&&(this.transparent=e.transparent),e.alphaTest!==void 0&&(this.alphaTest=e.alphaTest),e.alphaHash!==void 0&&(this.alphaHash=e.alphaHash),e.depthFunc!==void 0&&(this.depthFunc=e.depthFunc),e.depthTest!==void 0&&(this.depthTest=e.depthTest),e.depthWrite!==void 0&&(this.depthWrite=e.depthWrite),e.colorWrite!==void 0&&(this.colorWrite=e.colorWrite),e.clippingPlanes!==void 0&&(this.clippingPlanes=e.clippingPlanes.map(n=>new et().fromJSON(n))),e.clipIntersection!==void 0&&(this.clipIntersection=e.clipIntersection),e.clipShadows!==void 0&&(this.clipShadows=e.clipShadows),e.depthPacking!==void 0&&(this.depthPacking=e.depthPacking),e.blendSrc!==void 0&&(this.blendSrc=e.blendSrc),e.blendDst!==void 0&&(this.blendDst=e.blendDst),e.blendEquation!==void 0&&(this.blendEquation=e.blendEquation),e.blendSrcAlpha!==void 0&&(this.blendSrcAlpha=e.blendSrcAlpha),e.blendDstAlpha!==void 0&&(this.blendDstAlpha=e.blendDstAlpha),e.blendEquationAlpha!==void 0&&(this.blendEquationAlpha=e.blendEquationAlpha),e.blendColor!==void 0&&this.blendColor!==void 0&&this.blendColor.setHex(e.blendColor),e.blendAlpha!==void 0&&(this.blendAlpha=e.blendAlpha),e.stencilWriteMask!==void 0&&(this.stencilWriteMask=e.stencilWriteMask),e.stencilFunc!==void 0&&(this.stencilFunc=e.stencilFunc),e.stencilRef!==void 0&&(this.stencilRef=e.stencilRef),e.stencilFuncMask!==void 0&&(this.stencilFuncMask=e.stencilFuncMask),e.stencilFail!==void 0&&(this.stencilFail=e.stencilFail),e.stencilZFail!==void 0&&(this.stencilZFail=e.stencilZFail),e.stencilZPass!==void 0&&(this.stencilZPass=e.stencilZPass),e.stencilWrite!==void 0&&(this.stencilWrite=e.stencilWrite),e.wireframe!==void 0&&(this.wireframe=e.wireframe),e.wireframeLinewidth!==void 0&&(this.wireframeLinewidth=e.wireframeLinewidth),e.wireframeLinecap!==void 0&&(this.wireframeLinecap=e.wireframeLinecap),e.wireframeLinejoin!==void 0&&(this.wireframeLinejoin=e.wireframeLinejoin),e.rotation!==void 0&&(this.rotation=e.rotation),e.linewidth!==void 0&&(this.linewidth=e.linewidth),e.linecap!==void 0&&(this.linecap=e.linecap),e.linejoin!==void 0&&(this.linejoin=e.linejoin),e.dashSize!==void 0&&(this.dashSize=e.dashSize),e.gapSize!==void 0&&(this.gapSize=e.gapSize),e.scale!==void 0&&(this.scale=e.scale),e.polygonOffset!==void 0&&(this.polygonOffset=e.polygonOffset),e.polygonOffsetFactor!==void 0&&(this.polygonOffsetFactor=e.polygonOffsetFactor),e.polygonOffsetUnits!==void 0&&(this.polygonOffsetUnits=e.polygonOffsetUnits),e.dithering!==void 0&&(this.dithering=e.dithering),e.alphaToCoverage!==void 0&&(this.alphaToCoverage=e.alphaToCoverage),e.premultipliedAlpha!==void 0&&(this.premultipliedAlpha=e.premultipliedAlpha),e.forceSinglePass!==void 0&&(this.forceSinglePass=e.forceSinglePass),e.allowOverride!==void 0&&(this.allowOverride=e.allowOverride),e.visible!==void 0&&(this.visible=e.visible),e.toneMapped!==void 0&&(this.toneMapped=e.toneMapped),e.userData!==void 0&&(this.userData=e.userData),e.vertexColors!==void 0&&(typeof e.vertexColors=="number"?this.vertexColors=e.vertexColors>0:this.vertexColors=e.vertexColors),e.size!==void 0&&(this.size=e.size),e.sizeAttenuation!==void 0&&(this.sizeAttenuation=e.sizeAttenuation),e.map!==void 0&&(this.map=t[e.map]||null),e.matcap!==void 0&&(this.matcap=t[e.matcap]||null),e.alphaMap!==void 0&&(this.alphaMap=t[e.alphaMap]||null),e.bumpMap!==void 0&&(this.bumpMap=t[e.bumpMap]||null),e.bumpScale!==void 0&&(this.bumpScale=e.bumpScale),e.normalMap!==void 0&&(this.normalMap=t[e.normalMap]||null),e.normalMapType!==void 0&&(this.normalMapType=e.normalMapType),e.normalScale!==void 0){let n=e.normalScale;Array.isArray(n)===!1&&(n=[n,n]),this.normalScale=new $().fromArray(n)}return e.displacementMap!==void 0&&(this.displacementMap=t[e.displacementMap]||null),e.displacementScale!==void 0&&(this.displacementScale=e.displacementScale),e.displacementBias!==void 0&&(this.displacementBias=e.displacementBias),e.roughnessMap!==void 0&&(this.roughnessMap=t[e.roughnessMap]||null),e.metalnessMap!==void 0&&(this.metalnessMap=t[e.metalnessMap]||null),e.emissiveMap!==void 0&&(this.emissiveMap=t[e.emissiveMap]||null),e.emissiveIntensity!==void 0&&(this.emissiveIntensity=e.emissiveIntensity),e.specularMap!==void 0&&(this.specularMap=t[e.specularMap]||null),e.specularIntensityMap!==void 0&&(this.specularIntensityMap=t[e.specularIntensityMap]||null),e.specularColorMap!==void 0&&(this.specularColorMap=t[e.specularColorMap]||null),e.envMap!==void 0&&(this.envMap=t[e.envMap]||null),e.envMapRotation!==void 0&&this.envMapRotation.fromArray(e.envMapRotation),e.envMapIntensity!==void 0&&(this.envMapIntensity=e.envMapIntensity),e.reflectivity!==void 0&&(this.reflectivity=e.reflectivity),e.refractionRatio!==void 0&&(this.refractionRatio=e.refractionRatio),e.lightMap!==void 0&&(this.lightMap=t[e.lightMap]||null),e.lightMapIntensity!==void 0&&(this.lightMapIntensity=e.lightMapIntensity),e.aoMap!==void 0&&(this.aoMap=t[e.aoMap]||null),e.aoMapIntensity!==void 0&&(this.aoMapIntensity=e.aoMapIntensity),e.gradientMap!==void 0&&(this.gradientMap=t[e.gradientMap]||null),e.clearcoatMap!==void 0&&(this.clearcoatMap=t[e.clearcoatMap]||null),e.clearcoatRoughnessMap!==void 0&&(this.clearcoatRoughnessMap=t[e.clearcoatRoughnessMap]||null),e.clearcoatNormalMap!==void 0&&(this.clearcoatNormalMap=t[e.clearcoatNormalMap]||null),e.clearcoatNormalScale!==void 0&&(this.clearcoatNormalScale=new $().fromArray(e.clearcoatNormalScale)),e.iridescenceMap!==void 0&&(this.iridescenceMap=t[e.iridescenceMap]||null),e.iridescenceThicknessMap!==void 0&&(this.iridescenceThicknessMap=t[e.iridescenceThicknessMap]||null),e.transmissionMap!==void 0&&(this.transmissionMap=t[e.transmissionMap]||null),e.thicknessMap!==void 0&&(this.thicknessMap=t[e.thicknessMap]||null),e.anisotropyMap!==void 0&&(this.anisotropyMap=t[e.anisotropyMap]||null),e.sheenColorMap!==void 0&&(this.sheenColorMap=t[e.sheenColorMap]||null),e.sheenRoughnessMap!==void 0&&(this.sheenRoughnessMap=t[e.sheenRoughnessMap]||null),this}clone(){return new this.constructor().copy(this)}copy(e){this.name=e.name,this.blending=e.blending,this.side=e.side,this.vertexColors=e.vertexColors,this.opacity=e.opacity,this.transparent=e.transparent,this.blendSrc=e.blendSrc,this.blendDst=e.blendDst,this.blendEquation=e.blendEquation,this.blendSrcAlpha=e.blendSrcAlpha,this.blendDstAlpha=e.blendDstAlpha,this.blendEquationAlpha=e.blendEquationAlpha,this.blendColor.copy(e.blendColor),this.blendAlpha=e.blendAlpha,this.depthFunc=e.depthFunc,this.depthTest=e.depthTest,this.depthWrite=e.depthWrite,this.stencilWriteMask=e.stencilWriteMask,this.stencilFunc=e.stencilFunc,this.stencilRef=e.stencilRef,this.stencilFuncMask=e.stencilFuncMask,this.stencilFail=e.stencilFail,this.stencilZFail=e.stencilZFail,this.stencilZPass=e.stencilZPass,this.stencilWrite=e.stencilWrite;let t=e.clippingPlanes,n=null;if(t!==null){let i=t.length;n=new Array(i);for(let s=0;s!==i;++s)n[s]=t[s].clone()}return this.clippingPlanes=n,this.clipIntersection=e.clipIntersection,this.clipShadows=e.clipShadows,this.shadowSide=e.shadowSide,this.colorWrite=e.colorWrite,this.precision=e.precision,this.polygonOffset=e.polygonOffset,this.polygonOffsetFactor=e.polygonOffsetFactor,this.polygonOffsetUnits=e.polygonOffsetUnits,this.dithering=e.dithering,this.alphaTest=e.alphaTest,this.alphaHash=e.alphaHash,this.alphaToCoverage=e.alphaToCoverage,this.premultipliedAlpha=e.premultipliedAlpha,this.forceSinglePass=e.forceSinglePass,this.allowOverride=e.allowOverride,this.visible=e.visible,this.toneMapped=e.toneMapped,this.userData=JSON.parse(JSON.stringify(e.userData)),this}dispose(){this.dispatchEvent({type:"dispose"})}set needsUpdate(e){e===!0&&this.version++}};var mt=new E,Mr=new E,ji=new E,Ji=new E,on=class{constructor(e=new E,t=new E(0,0,-1)){this.origin=e,this.direction=t}set(e,t){return this.origin.copy(e),this.direction.copy(t),this}copy(e){return this.origin.copy(e.origin),this.direction.copy(e.direction),this}at(e,t){return t.copy(this.origin).addScaledVector(this.direction,e)}lookAt(e){return this.direction.copy(e).sub(this.origin).normalize(),this}recast(e){return this.origin.copy(this.at(e,mt)),this}closestPointToPoint(e,t){t.subVectors(e,this.origin);let n=t.dot(this.direction);return n<0?t.copy(this.origin):t.copy(this.origin).addScaledVector(this.direction,n)}distanceToPoint(e){return Math.sqrt(this.distanceSqToPoint(e))}distanceSqToPoint(e){let t=mt.subVectors(e,this.origin).dot(this.direction);return t<0?this.origin.distanceToSquared(e):(mt.copy(this.origin).addScaledVector(this.direction,t),mt.distanceToSquared(e))}distanceSqToSegment(e,t,n,i){Mr.copy(e).add(t).multiplyScalar(.5),ji.copy(t).sub(e).normalize(),Ji.copy(this.origin).sub(Mr);let s=e.distanceTo(t)*.5,r=-this.direction.dot(ji),o=Ji.dot(this.direction),c=-Ji.dot(ji),l=Ji.lengthSq(),u=Math.abs(1-r*r),h,f,d,p;if(u>0)if(h=r*c-o,f=r*o-c,p=s*u,h>=0)if(f>=-p)if(f<=p){let m=1/u;h*=m,f*=m,d=h*(h+r*f+2*o)+f*(r*h+f+2*c)+l}else f=s,h=Math.max(0,-(r*f+o)),d=-h*h+f*(f+2*c)+l;else f=-s,h=Math.max(0,-(r*f+o)),d=-h*h+f*(f+2*c)+l;else f<=-p?(h=Math.max(0,-(-r*s+o)),f=h>0?-s:Math.min(Math.max(-s,-c),s),d=-h*h+f*(f+2*c)+l):f<=p?(h=0,f=Math.min(Math.max(-s,-c),s),d=f*(f+2*c)+l):(h=Math.max(0,-(r*s+o)),f=h>0?s:Math.min(Math.max(-s,-c),s),d=-h*h+f*(f+2*c)+l);else f=r>0?-s:s,h=Math.max(0,-(r*f+o)),d=-h*h+f*(f+2*c)+l;return n&&n.copy(this.origin).addScaledVector(this.direction,h),i&&i.copy(Mr).addScaledVector(ji,f),d}intersectSphere(e,t){if(e.radius<0)return null;mt.subVectors(e.center,this.origin);let n=mt.dot(this.direction),i=mt.dot(mt)-n*n,s=e.radius*e.radius;if(i>s)return null;let r=Math.sqrt(s-i),o=n-r,c=n+r;return c<0?null:o<0?this.at(c,t):this.at(o,t)}intersectsSphere(e){return e.radius<0?!1:this.distanceSqToPoint(e.center)<=e.radius*e.radius}distanceToPlane(e){let t=e.normal.dot(this.direction);if(t===0)return e.distanceToPoint(this.origin)===0?0:null;let n=-(this.origin.dot(e.normal)+e.constant)/t;return n>=0?n:null}intersectPlane(e,t){let n=this.distanceToPlane(e);return n===null?null:this.at(n,t)}intersectsPlane(e){let t=e.distanceToPoint(this.origin);return t===0||e.normal.dot(this.direction)*t<0}intersectBox(e,t){let n,i,s,r,o,c,l=1/this.direction.x,u=1/this.direction.y,h=1/this.direction.z,f=this.origin;return l>=0?(n=(e.min.x-f.x)*l,i=(e.max.x-f.x)*l):(n=(e.max.x-f.x)*l,i=(e.min.x-f.x)*l),u>=0?(s=(e.min.y-f.y)*u,r=(e.max.y-f.y)*u):(s=(e.max.y-f.y)*u,r=(e.min.y-f.y)*u),n>r||s>i||((s>n||isNaN(n))&&(n=s),(r<i||isNaN(i))&&(i=r),h>=0?(o=(e.min.z-f.z)*h,c=(e.max.z-f.z)*h):(o=(e.max.z-f.z)*h,c=(e.min.z-f.z)*h),n>c||o>i)||((o>n||n!==n)&&(n=o),(c<i||i!==i)&&(i=c),i<0)?null:this.at(n>=0?n:i,t)}intersectsBox(e){return this.intersectBox(e,mt)!==null}intersectTriangle(e,t,n,i,s){let r=this.origin,o=this.direction,c=o.x,l=o.y,u=o.z,h=e.x-r.x,f=e.y-r.y,d=e.z-r.z,p=t.x-r.x,m=t.y-r.y,b=t.z-r.z,x=n.x-r.x,v=n.y-r.y,S=n.z-r.z,y=Math.abs(c),T=Math.abs(l),M=Math.abs(u),A,g,w,R,C,N,L,F,I,O,B,k;if(y>=T&&y>=M?(w=c,N=h,I=p,k=x,c>=0?(A=l,g=u,R=f,C=d,L=m,F=b,O=v,B=S):(A=u,g=l,R=d,C=f,L=b,F=m,O=S,B=v)):T>=M?(w=l,N=f,I=m,k=v,l>=0?(A=u,g=c,R=d,C=h,L=b,F=p,O=S,B=x):(A=c,g=u,R=h,C=d,L=p,F=b,O=x,B=S)):(w=u,N=d,I=b,k=S,u>=0?(A=c,g=l,R=h,C=f,L=p,F=m,O=x,B=v):(A=l,g=c,R=f,C=h,L=m,F=p,O=v,B=x)),w===0)return null;let W=A/w,me=g/w,se=1/w,we=R-W*N,Fe=C-me*N,Ee=L-W*I,ge=F-me*I,lt=O-W*k,jn=B-me*k,ut=lt*ge-jn*Ee,Zt=we*jn-Fe*lt,Pt=Ee*Fe-ge*we;if(i){if(ut<0||Zt<0||Pt<0)return null}else if((ut<0||Zt<0||Pt<0)&&(ut>0||Zt>0||Pt>0))return null;let mn=ut+Zt+Pt;if(mn===0)return null;let gn=se*(ut*N+Zt*I+Pt*k);return(mn>0?gn<0:gn>0)?null:this.at(gn/mn,s)}applyMatrix4(e){return this.origin.applyMatrix4(e),this.direction.transformDirection(e),this}equals(e){return e.origin.equals(this.origin)&&e.direction.equals(this.direction)}clone(){return new this.constructor().copy(this)}},it=class extends $e{constructor(e){super(),this.isMeshBasicMaterial=!0,this.type="MeshBasicMaterial",this.color=new H(16777215),this.map=null,this.lightMap=null,this.lightMapIntensity=1,this.aoMap=null,this.aoMapIntensity=1,this.specularMap=null,this.alphaMap=null,this.envMap=null,this.envMapRotation=new ke,this.combine=Zr,this.reflectivity=1,this.refractionRatio=.98,this.wireframe=!1,this.wireframeLinewidth=1,this.wireframeLinecap="round",this.wireframeLinejoin="round",this.fog=!0,this.setValues(e)}copy(e){return super.copy(e),this.color.copy(e.color),this.map=e.map,this.lightMap=e.lightMap,this.lightMapIntensity=e.lightMapIntensity,this.aoMap=e.aoMap,this.aoMapIntensity=e.aoMapIntensity,this.specularMap=e.specularMap,this.alphaMap=e.alphaMap,this.envMap=e.envMap,this.envMapRotation.copy(e.envMapRotation),this.combine=e.combine,this.reflectivity=e.reflectivity,this.refractionRatio=e.refractionRatio,this.wireframe=e.wireframe,this.wireframeLinewidth=e.wireframeLinewidth,this.wireframeLinecap=e.wireframeLinecap,this.wireframeLinejoin=e.wireframeLinejoin,this.fog=e.fog,this}},Mc=new z,en=new on,Zi=new Le,Ac=new E,$i=new E,Qi=new E,es=new E,Ar=new E,ts=new E,Tc=new E,ns=new E,Gt=class extends le{constructor(e=new nt,t=new it){super(),this.isMesh=!0,this.type="Mesh",this.geometry=e,this.material=t,this.morphTargetDictionary=void 0,this.morphTargetInfluences=void 0,this.count=1,this.updateMorphTargets()}copy(e,t){return super.copy(e,t),e.morphTargetInfluences!==void 0&&(this.morphTargetInfluences=e.morphTargetInfluences.slice()),e.morphTargetDictionary!==void 0&&(this.morphTargetDictionary=Object.assign({},e.morphTargetDictionary)),this.material=Array.isArray(e.material)?e.material.slice():e.material,this.geometry=e.geometry,this}updateMorphTargets(){let t=this.geometry.morphAttributes,n=Object.keys(t);if(n.length>0){let i=t[n[0]];if(i!==void 0){this.morphTargetInfluences=[],this.morphTargetDictionary={};for(let s=0,r=i.length;s<r;s++){let o=i[s].name||String(s);this.morphTargetInfluences.push(0),this.morphTargetDictionary[o]=s}}}}getVertexPosition(e,t){let n=this.geometry,i=n.attributes.position,s=n.morphAttributes.position,r=n.morphTargetsRelative;t.fromBufferAttribute(i,e);let o=this.morphTargetInfluences;if(s&&o){ts.set(0,0,0);for(let c=0,l=s.length;c<l;c++){let u=o[c],h=s[c];u!==0&&(Ar.fromBufferAttribute(h,e),r?ts.addScaledVector(Ar,u):ts.addScaledVector(Ar.sub(t),u))}t.add(ts)}return t}intersectsFrustum(e){return e.intersectsObject(this)}raycast(e,t){let n=this.geometry,i=this.material,s=this.matrixWorld;i!==void 0&&(n.boundingSphere===null&&n.computeBoundingSphere(),Zi.copy(n.boundingSphere),Zi.applyMatrix4(s),en.copy(e.ray).recast(e.near),!(Zi.containsPoint(en.origin)===!1&&(en.intersectSphere(Zi,Ac)===null||en.origin.distanceToSquared(Ac)>(e.far-e.near)**2))&&(Mc.copy(s).invert(),en.copy(e.ray).applyMatrix4(Mc),!(n.boundingBox!==null&&en.intersectsBox(n.boundingBox)===!1)&&this._computeIntersections(e,t,en)))}_computeIntersections(e,t,n){let i,s=this.geometry,r=this.material,o=s.index,c=s.attributes.position,l=s.attributes.uv,u=s.attributes.uv1,h=s.attributes.normal,f=s.groups,d=s.drawRange;if(o!==null)if(Array.isArray(r))for(let p=0,m=f.length;p<m;p++){let b=f[p],x=r[b.materialIndex],v=Math.max(b.start,d.start),S=Math.min(o.count,Math.min(b.start+b.count,d.start+d.count));for(let y=v,T=S;y<T;y+=3){let M=o.getX(y),A=o.getX(y+1),g=o.getX(y+2);i=is(this,x,e,n,l,u,h,M,A,g),i&&(i.faceIndex=Math.floor(y/3),i.face.materialIndex=b.materialIndex,t.push(i))}}else{let p=Math.max(0,d.start),m=Math.min(o.count,d.start+d.count);for(let b=p,x=m;b<x;b+=3){let v=o.getX(b),S=o.getX(b+1),y=o.getX(b+2);i=is(this,r,e,n,l,u,h,v,S,y),i&&(i.faceIndex=Math.floor(b/3),t.push(i))}}else if(c!==void 0)if(Array.isArray(r))for(let p=0,m=f.length;p<m;p++){let b=f[p],x=r[b.materialIndex],v=Math.max(b.start,d.start),S=Math.min(c.count,Math.min(b.start+b.count,d.start+d.count));for(let y=v,T=S;y<T;y+=3){let M=y,A=y+1,g=y+2;i=is(this,x,e,n,l,u,h,M,A,g),i&&(i.faceIndex=Math.floor(y/3),i.face.materialIndex=b.materialIndex,t.push(i))}}else{let p=Math.max(0,d.start),m=Math.min(c.count,d.start+d.count);for(let b=p,x=m;b<x;b+=3){let v=b,S=b+1,y=b+2;i=is(this,r,e,n,l,u,h,v,S,y),i&&(i.faceIndex=Math.floor(b/3),t.push(i))}}}};function Oh(a,e,t,n,i,s,r,o){let c;if(e.side===jc?c=n.intersectTriangle(r,s,i,!0,o):c=n.intersectTriangle(i,s,r,e.side===Si,o),c===null)return null;ns.copy(o),ns.applyMatrix4(a.matrixWorld);let l=t.ray.origin.distanceTo(ns);return l<t.near||l>t.far?null:{distance:l,point:ns.clone(),object:a}}function is(a,e,t,n,i,s,r,o,c,l){a.getVertexPosition(o,$i),a.getVertexPosition(c,Qi),a.getVertexPosition(l,es);let u=Oh(a,e,t,n,$i,Qi,es,Tc);if(u){let h=new E;Bt.getBarycoord(Tc,$i,Qi,es,h),i&&(u.uv=Bt.getInterpolatedAttribute(i,o,c,l,h,new $)),s&&(u.uv1=Bt.getInterpolatedAttribute(s,o,c,l,h,new $)),r&&(u.normal=Bt.getInterpolatedAttribute(r,o,c,l,h,new E),u.normal.dot(n.direction)>0&&u.normal.multiplyScalar(-1));let f={a:o,b:c,c:l,normal:new E,materialIndex:0};Bt.getNormal($i,Qi,es,f.normal),u.face=f,u.barycoord=h}return u}var ei=new Xe,wc=new Xe,Ec=new Xe,Bh=new Xe,Rc=new z,ss=new E,Tr=new Le,Cc=new z,wr=new on,oi=class extends Gt{constructor(e,t){super(e,t),this.isSkinnedMesh=!0,this.type="SkinnedMesh",this.bindMode=Or,this.bindMatrix=new z,this.bindMatrixInverse=new z,this.boundingBox=null,this.boundingSphere=null}computeBoundingBox(){let e=this.geometry;this.boundingBox===null&&(this.boundingBox=new ze),this.boundingBox.makeEmpty();let t=e.getAttribute("position");for(let n=0;n<t.count;n++)this.getVertexPosition(n,ss),this.boundingBox.expandByPoint(ss)}computeBoundingSphere(){let e=this.geometry;this.boundingSphere===null&&(this.boundingSphere=new Le),this.boundingSphere.makeEmpty();let t=e.getAttribute("position");for(let n=0;n<t.count;n++)this.getVertexPosition(n,ss),this.boundingSphere.expandByPoint(ss)}copy(e,t){return super.copy(e,t),this.bindMode=e.bindMode,this.bindMatrix.copy(e.bindMatrix),this.bindMatrixInverse.copy(e.bindMatrixInverse),this.skeleton=e.skeleton,e.boundingBox!==null&&(this.boundingBox=e.boundingBox.clone()),e.boundingSphere!==null&&(this.boundingSphere=e.boundingSphere.clone()),this}raycast(e,t){let n=this.material,i=this.matrixWorld;n!==void 0&&(this.boundingSphere===null&&this.computeBoundingSphere(),Tr.copy(this.boundingSphere),Tr.applyMatrix4(i),e.ray.intersectsSphere(Tr)!==!1&&(Cc.copy(i).invert(),wr.copy(e.ray).applyMatrix4(Cc),!(this.boundingBox!==null&&wr.intersectsBox(this.boundingBox)===!1)&&this._computeIntersections(e,t,wr)))}getVertexPosition(e,t){return super.getVertexPosition(e,t),this.applyBoneTransform(e,t),t}bind(e,t){this.skeleton=e,t===void 0&&(this.updateMatrixWorld(!0),this.skeleton.calculateInverses(),t=this.matrixWorld),this.bindMatrix.copy(t),this.bindMatrixInverse.copy(t).invert()}pose(){this.skeleton.pose()}normalizeSkinWeights(){let e=new Xe,t=this.geometry.attributes.skinWeight;for(let n=0,i=t.count;n<i;n++){e.fromBufferAttribute(t,n);let s=1/e.manhattanLength();s!==1/0?e.multiplyScalar(s):e.set(1,0,0,0),t.setXYZW(n,e.x,e.y,e.z,e.w)}}updateMatrixWorld(e){super.updateMatrixWorld(e),this.bindMode===Or?this.bindMatrixInverse.copy(this.matrixWorld).invert():this.bindMode===nl?this.bindMatrixInverse.copy(this.bindMatrix).invert():ne("SkinnedMesh: Unrecognized bindMode: "+this.bindMode)}applyBoneTransform(e,t){let n=this.skeleton,i=this.geometry;wc.fromBufferAttribute(i.attributes.skinIndex,e),Ec.fromBufferAttribute(i.attributes.skinWeight,e),t.isVector4?(ei.copy(t),t.set(0,0,0,0)):(ei.set(...t,1),t.set(0,0,0)),ei.applyMatrix4(this.bindMatrix);for(let s=0;s<4;s++){let r=Ec.getComponent(s);if(r!==0){let o=wc.getComponent(s);Rc.multiplyMatrices(n.bones[o].matrixWorld,n.boneInverses[o]),t.addScaledVector(Bh.copy(ei).applyMatrix4(Rc),r)}}return t.isVector4&&(t.w=ei.w),t.applyMatrix4(this.bindMatrixInverse)}},On=class extends le{constructor(){super(),this.isBone=!0,this.type="Bone"}},ci=class extends We{constructor(e=null,t=1,n=1,i,s,r,o,c,l=zt,u=zt,h,f){super(null,r,o,c,l,u,i,s,h,f),this.isDataTexture=!0,this.image={data:e,width:t,height:n},this.generateMipmaps=!1,this.flipY=!1,this.unpackAlignment=1}},Ic=new z,kh=new z,li=class a{constructor(e=[],t=[]){this.uuid=Ze(),this.bones=e.slice(0),this.boneInverses=t,this.boneMatrices=null,this.boneTexture=null,this.init()}init(){let e=this.bones,t=this.boneInverses;if(this.boneMatrices=new Float32Array(e.length*16),t.length===0)this.calculateInverses();else if(e.length!==t.length){ne("Skeleton: Number of inverse bone matrices does not match amount of bones."),this.boneInverses=[];for(let n=0,i=this.bones.length;n<i;n++)this.boneInverses.push(new z)}}calculateInverses(){this.boneInverses.length=0;for(let e=0,t=this.bones.length;e<t;e++){let n=new z;this.bones[e]&&n.copy(this.bones[e].matrixWorld).invert(),this.boneInverses.push(n)}}pose(){for(let e=0,t=this.bones.length;e<t;e++){let n=this.bones[e];n&&n.matrixWorld.copy(this.boneInverses[e]).invert()}for(let e=0,t=this.bones.length;e<t;e++){let n=this.bones[e];n&&(n.parent&&n.parent.isBone?(n.matrix.copy(n.parent.matrixWorld).invert(),n.matrix.multiply(n.matrixWorld)):n.matrix.copy(n.matrixWorld),n.matrix.decompose(n.position,n.quaternion,n.scale))}}update(){let e=this.bones,t=this.boneInverses,n=this.boneMatrices,i=this.boneTexture;for(let s=0,r=e.length;s<r;s++){let o=e[s]?e[s].matrixWorld:kh;Ic.multiplyMatrices(o,t[s]),Ic.toArray(n,s*16)}i!==null&&(i.needsUpdate=!0)}clone(){return new a(this.bones,this.boneInverses)}computeBoneTexture(){let e=Math.sqrt(this.bones.length*4);e=Math.ceil(e/4)*4,e=Math.max(e,4);let t=new Float32Array(e*e*4);t.set(this.boneMatrices);let n=new ci(t,e,e,Ei,Ds);return n.needsUpdate=!0,this.boneMatrices=t,this.boneTexture=n,this}getBoneByName(e){for(let t=0,n=this.bones.length;t<n;t++){let i=this.bones[t];if(i.name===e)return i}}dispose(){this.boneTexture!==null&&(this.boneTexture.dispose(),this.boneTexture=null)}fromJSON(e,t){this.uuid=e.uuid;for(let n=0,i=e.bones.length;n<i;n++){let s=e.bones[n],r=t[s];r===void 0&&(ne("Skeleton: No bone found with UUID:",s),r=new On),this.bones.push(r),this.boneInverses.push(new z().fromArray(e.boneInverses[n]))}return this.init(),this}toJSON(){let e={metadata:{version:4.7,type:"Skeleton",generator:"Skeleton.toJSON"},bones:[],boneInverses:[]};e.uuid=this.uuid;let t=this.bones,n=this.boneInverses;for(let i=0,s=t.length;i<s;i++){let r=t[i];e.bones.push(r.uuid);let o=n[i];e.boneInverses.push(o.toArray())}return e}},St=class extends ae{constructor(e,t,n,i=1){super(e,t,n),this.isInstancedBufferAttribute=!0,this.meshPerAttribute=i}copy(e){return super.copy(e),this.meshPerAttribute=e.meshPerAttribute,this}toJSON(){let e=super.toJSON();return e.meshPerAttribute=this.meshPerAttribute,e.isInstancedBufferAttribute=!0,e}},En=new z,Pc=new z,rs=[],Lc=new ze,zh=new z,ti=new Gt,ni=new Le,ui=class extends Gt{constructor(e,t,n){super(e,t),this.isInstancedMesh=!0,this.instanceMatrix=new St(new Float32Array(n*16),16),this.instanceColor=null,this.morphTexture=null,this.count=n,this.boundingBox=null,this.boundingSphere=null;for(let i=0;i<n;i++)this.setMatrixAt(i,zh)}computeBoundingBox(){let e=this.geometry,t=this.count;this.boundingBox===null&&(this.boundingBox=new ze),e.boundingBox===null&&e.computeBoundingBox(),this.boundingBox.makeEmpty();for(let n=0;n<t;n++)this.getMatrixAt(n,En),Lc.copy(e.boundingBox).applyMatrix4(En),this.boundingBox.union(Lc)}computeBoundingSphere(){let e=this.geometry,t=this.count;this.boundingSphere===null&&(this.boundingSphere=new Le),e.boundingSphere===null&&e.computeBoundingSphere(),this.boundingSphere.makeEmpty();for(let n=0;n<t;n++)this.getMatrixAt(n,En),ni.copy(e.boundingSphere).applyMatrix4(En),this.boundingSphere.union(ni)}copy(e,t){return super.copy(e,t),this.instanceMatrix.copy(e.instanceMatrix),e.morphTexture!==null&&(this.morphTexture=e.morphTexture.clone()),e.instanceColor!==null&&(this.instanceColor=e.instanceColor.clone()),this.count=e.count,e.boundingBox!==null&&(this.boundingBox=e.boundingBox.clone()),e.boundingSphere!==null&&(this.boundingSphere=e.boundingSphere.clone()),this}getColorAt(e,t){return this.instanceColor===null?t.setRGB(1,1,1):t.fromArray(this.instanceColor.array,e*3)}getMatrixAt(e,t){return t.fromArray(this.instanceMatrix.array,e*16)}getMorphAt(e,t){let n=t.morphTargetInfluences,i=this.morphTexture.source.data.data,s=n.length+1,r=e*s+1;for(let o=0;o<n.length;o++)n[o]=i[r+o]}raycast(e,t){let n=this.matrixWorld,i=this.count;if(ti.geometry=this.geometry,ti.material=this.material,ti.material!==void 0&&(this.boundingSphere===null&&this.computeBoundingSphere(),ni.copy(this.boundingSphere),ni.applyMatrix4(n),e.ray.intersectsSphere(ni)!==!1))for(let s=0;s<i;s++){this.getMatrixAt(s,En),Pc.multiplyMatrices(n,En),ti.matrixWorld=Pc,ti.raycast(e,rs);for(let r=0,o=rs.length;r<o;r++){let c=rs[r];c.instanceId=s,c.object=this,t.push(c)}rs.length=0}}setColorAt(e,t){return this.instanceColor===null&&(this.instanceColor=new St(new Float32Array(this.instanceMatrix.count*3).fill(1),3)),t.toArray(this.instanceColor.array,e*3),this}setMatrixAt(e,t){return t.toArray(this.instanceMatrix.array,e*16),this}setMorphAt(e,t){let n=t.morphTargetInfluences,i=n.length+1;this.morphTexture===null&&(this.morphTexture=new ci(new Float32Array(i*this.count),i,this.count,rl,Ds));let s=this.morphTexture.source.data.data,r=0;for(let l=0;l<n.length;l++)r+=n[l];let o=this.geometry.morphTargetsRelative?1:1-r,c=i*e;return s[c]=o,s.set(n,c+1),this}updateMorphTargets(){}dispose(){super.dispose(),this.morphTexture!==null&&(this.morphTexture.dispose(),this.morphTexture=null)}},tn=new Le,Vh=new $(.5,.5),as=new E,Ss=class{constructor(e=new et,t=new et,n=new et,i=new et,s=new et,r=new et){this.planes=[e,t,n,i,s,r]}set(e,t,n,i,s,r){let o=this.planes;return o[0].copy(e),o[1].copy(t),o[2].copy(n),o[3].copy(i),o[4].copy(s),o[5].copy(r),this}copy(e){let t=this.planes;for(let n=0;n<6;n++)t[n].copy(e.planes[n]);return this}setFromProjectionMatrix(e,t=kt,n=!1){let i=this.planes,s=e.elements,r=s[0],o=s[1],c=s[2],l=s[3],u=s[4],h=s[5],f=s[6],d=s[7],p=s[8],m=s[9],b=s[10],x=s[11],v=s[12],S=s[13],y=s[14],T=s[15];if(i[0].setComponents(l-r,d-u,x-p,T-v).normalize(),i[1].setComponents(l+r,d+u,x+p,T+v).normalize(),i[2].setComponents(l+o,d+h,x+m,T+S).normalize(),i[3].setComponents(l-o,d-h,x-m,T-S).normalize(),n)i[4].setComponents(c,f,b,y).normalize(),i[5].setComponents(l-c,d-f,x-b,T-y).normalize();else if(i[4].setComponents(l-c,d-f,x-b,T-y).normalize(),t===kt)i[5].setComponents(l+c,d+f,x+b,T+y).normalize();else if(t===ai)i[5].setComponents(c,f,b,y).normalize();else throw new Error("THREE.Frustum.setFromProjectionMatrix(): Invalid coordinate system: "+t);return this}intersectsObject(e){if(e.boundingSphere!==void 0)e.boundingSphere===null&&e.computeBoundingSphere(),tn.copy(e.boundingSphere).applyMatrix4(e.matrixWorld);else{let t=e.geometry;t.boundingSphere===null&&t.computeBoundingSphere(),tn.copy(t.boundingSphere).applyMatrix4(e.matrixWorld)}return this.intersectsSphere(tn)}intersectsSprite(e){tn.center.set(0,0,0);let t=Vh.distanceTo(e.center);return tn.radius=.7071067811865476+t,tn.applyMatrix4(e.matrixWorld),this.intersectsSphere(tn)}intersectsSphere(e){let t=this.planes,n=e.center,i=-e.radius;for(let s=0;s<6;s++)if(t[s].distanceToPoint(n)<i)return!1;return!0}intersectsBox(e){let t=this.planes;for(let n=0;n<6;n++){let i=t[n];if(as.x=i.normal.x>0?e.max.x:e.min.x,as.y=i.normal.y>0?e.max.y:e.min.y,as.z=i.normal.z>0?e.max.z:e.min.z,i.distanceToPoint(as)<0)return!1}return!0}containsPoint(e){let t=this.planes;for(let n=0;n<6;n++)if(t[n].distanceToPoint(e)<0)return!1;return!0}clone(){return new this.constructor().copy(this)}};var Bn=class extends $e{constructor(e){super(),this.isLineBasicMaterial=!0,this.type="LineBasicMaterial",this.color=new H(16777215),this.map=null,this.linewidth=1,this.linecap="round",this.linejoin="round",this.fog=!0,this.setValues(e)}copy(e){return super.copy(e),this.color.copy(e.color),this.map=e.map,this.linewidth=e.linewidth,this.linecap=e.linecap,this.linejoin=e.linejoin,this.fog=e.fog,this}},Ms=new E,As=new E,Dc=new z,ii=new on,os=new Le,Er=new E,Nc=new E,cn=class extends le{constructor(e=new nt,t=new Bn){super(),this.isLine=!0,this.type="Line",this.geometry=e,this.material=t,this.morphTargetDictionary=void 0,this.morphTargetInfluences=void 0,this.updateMorphTargets()}copy(e,t){return super.copy(e,t),this.material=Array.isArray(e.material)?e.material.slice():e.material,this.geometry=e.geometry,this}computeLineDistances(){let e=this.geometry;if(e.index===null){let t=e.attributes.position,n=[0];for(let i=1,s=t.count;i<s;i++)Ms.fromBufferAttribute(t,i-1),As.fromBufferAttribute(t,i),n[i]=n[i-1],n[i]+=Ms.distanceTo(As);e.setAttribute("lineDistance",new an(n,1))}else ne("Line.computeLineDistances(): Computation only possible with non-indexed BufferGeometry.");return this}intersectsFrustum(e){return e.intersectsObject(this)}raycast(e,t){let n=this.geometry,i=this.matrixWorld,s=e.params.Line.threshold,r=n.drawRange;if(n.boundingSphere===null&&n.computeBoundingSphere(),os.copy(n.boundingSphere),os.applyMatrix4(i),os.radius+=s,e.ray.intersectsSphere(os)===!1)return;Dc.copy(i).invert(),ii.copy(e.ray).applyMatrix4(Dc);let o=s/((this.scale.x+this.scale.y+this.scale.z)/3),c=o*o,l=this.isLineSegments?2:1,u=n.index,f=n.attributes.position;if(u!==null){let d=Math.max(0,r.start),p=Math.min(u.count,r.start+r.count);for(let m=d,b=p-1;m<b;m+=l){let x=u.getX(m),v=u.getX(m+1),S=cs(this,e,ii,c,x,v,m);S&&t.push(S)}if(this.isLineLoop){let m=u.getX(p-1),b=u.getX(d),x=cs(this,e,ii,c,m,b,p-1);x&&t.push(x)}}else{let d=Math.max(0,r.start),p=Math.min(f.count,r.start+r.count);for(let m=d,b=p-1;m<b;m+=l){let x=cs(this,e,ii,c,m,m+1,m);x&&t.push(x)}if(this.isLineLoop){let m=cs(this,e,ii,c,p-1,d,p-1);m&&t.push(m)}}}updateMorphTargets(){let t=this.geometry.morphAttributes,n=Object.keys(t);if(n.length>0){let i=t[n[0]];if(i!==void 0){this.morphTargetInfluences=[],this.morphTargetDictionary={};for(let s=0,r=i.length;s<r;s++){let o=i[s].name||String(s);this.morphTargetInfluences.push(0),this.morphTargetDictionary[o]=s}}}}};function cs(a,e,t,n,i,s,r){let o=a.geometry.attributes.position;if(Ms.fromBufferAttribute(o,i),As.fromBufferAttribute(o,s),t.distanceSqToSegment(Ms,As,Er,Nc)>n)return;Er.applyMatrix4(a.matrixWorld);let l=e.ray.origin.distanceTo(Er);if(!(l<e.near||l>e.far))return{distance:l,point:Nc.clone().applyMatrix4(a.matrixWorld),index:r,face:null,faceIndex:null,barycoord:null,object:a}}var Fc=new E,Uc=new E,hi=class extends cn{constructor(e,t){super(e,t),this.isLineSegments=!0,this.type="LineSegments"}computeLineDistances(){let e=this.geometry;if(e.index===null){let t=e.attributes.position,n=[];for(let i=0,s=t.count;i<s;i+=2)Fc.fromBufferAttribute(t,i),Uc.fromBufferAttribute(t,i+1),n[i]=i===0?0:n[i-1],n[i+1]=n[i]+Fc.distanceTo(Uc);e.setAttribute("lineDistance",new an(n,1))}else ne("LineSegments.computeLineDistances(): Computation only possible with non-indexed BufferGeometry.");return this}},fi=class extends cn{constructor(e,t){super(e,t),this.isLineLoop=!0,this.type="LineLoop"}},kn=class extends $e{constructor(e){super(),this.isPointsMaterial=!0,this.type="PointsMaterial",this.color=new H(16777215),this.map=null,this.alphaMap=null,this.size=1,this.sizeAttenuation=!0,this.fog=!0,this.setValues(e)}copy(e){return super.copy(e),this.color.copy(e.color),this.map=e.map,this.alphaMap=e.alphaMap,this.size=e.size,this.sizeAttenuation=e.sizeAttenuation,this.fog=e.fog,this}},Oc=new z,Wr=new on,ls=new Le,us=new E,di=class extends le{constructor(e=new nt,t=new kn){super(),this.isPoints=!0,this.type="Points",this.geometry=e,this.material=t,this.morphTargetDictionary=void 0,this.morphTargetInfluences=void 0,this.updateMorphTargets()}copy(e,t){return super.copy(e,t),this.material=Array.isArray(e.material)?e.material.slice():e.material,this.geometry=e.geometry,this}intersectsFrustum(e){return e.intersectsObject(this)}raycast(e,t){let n=this.geometry,i=this.matrixWorld,s=e.params.Points.threshold,r=n.drawRange;if(n.boundingSphere===null&&n.computeBoundingSphere(),ls.copy(n.boundingSphere),ls.applyMatrix4(i),ls.radius+=s,e.ray.intersectsSphere(ls)===!1)return;Oc.copy(i).invert(),Wr.copy(e.ray).applyMatrix4(Oc);let o=s/((this.scale.x+this.scale.y+this.scale.z)/3),c=o*o,l=n.index,h=n.attributes.position;if(l!==null){let f=Math.max(0,r.start),d=Math.min(l.count,r.start+r.count);for(let p=f,m=d;p<m;p++){let b=l.getX(p);us.fromBufferAttribute(h,b),Bc(us,b,c,i,e,t,this)}}else{let f=Math.max(0,r.start),d=Math.min(h.count,r.start+r.count);for(let p=f,m=d;p<m;p++)us.fromBufferAttribute(h,p),Bc(us,p,c,i,e,t,this)}}updateMorphTargets(){let t=this.geometry.morphAttributes,n=Object.keys(t);if(n.length>0){let i=t[n[0]];if(i!==void 0){this.morphTargetInfluences=[],this.morphTargetDictionary={};for(let s=0,r=i.length;s<r;s++){let o=i[s].name||String(s);this.morphTargetInfluences.push(0),this.morphTargetDictionary[o]=s}}}}};function Bc(a,e,t,n,i,s,r){let o=Wr.distanceSqToPoint(a);if(o<t){let c=new E;Wr.closestPointToPoint(a,c),c.applyMatrix4(n);let l=i.ray.origin.distanceTo(c);if(l<i.near||l>i.far)return;s.push({distance:l,distanceToRay:Math.sqrt(o),point:c,index:e,face:null,faceIndex:null,barycoord:null,object:r})}}var Ht=class extends We{constructor(e,t,n,i,s,r,o,c,l,u,h,f){super(null,r,o,c,l,u,i,s,h,f),this.isCompressedTexture=!0,this.image={width:t,height:n},this.mipmaps=e,this.flipY=!1,this.generateMipmaps=!1}};function hl(a){let e={};for(let t in a){e[t]={};for(let n in a[t]){let i=a[t][n];if(kc(i))i.isRenderTargetTexture?(ne("UniformsUtils: Textures of render targets cannot be cloned via cloneUniforms() or mergeUniforms()."),e[t][n]=null):e[t][n]=i.clone();else if(Array.isArray(i))if(kc(i[0])){let s=[];for(let r=0,o=i.length;r<o;r++)s[r]=i[r].clone();e[t][n]=s}else e[t][n]=i.slice();else e[t][n]=i}}return e}function Ce(a){let e={};for(let t=0;t<a.length;t++){let n=hl(a[t]);for(let i in n)e[i]=n[i]}return e}function kc(a){return a&&(a.isColor||a.isMatrix3||a.isMatrix4||a.isVector2||a.isVector3||a.isVector4||a.isTexture||a.isQuaternion)}var ln=class extends $e{constructor(e){super(),this.isMeshStandardMaterial=!0,this.type="MeshStandardMaterial",this.defines={STANDARD:""},this.color=new H(16777215),this.roughness=1,this.metalness=0,this.map=null,this.lightMap=null,this.lightMapIntensity=1,this.aoMap=null,this.aoMapIntensity=1,this.emissive=new H(0),this.emissiveIntensity=1,this.emissiveMap=null,this.bumpMap=null,this.bumpScale=1,this.normalMap=null,this.normalMapType=ol,this.normalScale=new $(1,1),this.displacementMap=null,this.displacementScale=1,this.displacementBias=0,this.roughnessMap=null,this.metalnessMap=null,this.alphaMap=null,this.envMap=null,this.envMapRotation=new ke,this.envMapIntensity=1,this.wireframe=!1,this.wireframeLinewidth=1,this.wireframeLinecap="round",this.wireframeLinejoin="round",this.flatShading=!1,this.fog=!0,this.setValues(e)}copy(e){return super.copy(e),this.defines={STANDARD:""},this.color.copy(e.color),this.roughness=e.roughness,this.metalness=e.metalness,this.map=e.map,this.lightMap=e.lightMap,this.lightMapIntensity=e.lightMapIntensity,this.aoMap=e.aoMap,this.aoMapIntensity=e.aoMapIntensity,this.emissive.copy(e.emissive),this.emissiveMap=e.emissiveMap,this.emissiveIntensity=e.emissiveIntensity,this.bumpMap=e.bumpMap,this.bumpScale=e.bumpScale,this.normalMap=e.normalMap,this.normalMapType=e.normalMapType,this.normalScale.copy(e.normalScale),this.displacementMap=e.displacementMap,this.displacementScale=e.displacementScale,this.displacementBias=e.displacementBias,this.roughnessMap=e.roughnessMap,this.metalnessMap=e.metalnessMap,this.alphaMap=e.alphaMap,this.envMap=e.envMap,this.envMapRotation.copy(e.envMapRotation),this.envMapIntensity=e.envMapIntensity,this.wireframe=e.wireframe,this.wireframeLinewidth=e.wireframeLinewidth,this.wireframeLinecap=e.wireframeLinecap,this.wireframeLinejoin=e.wireframeLinejoin,this.flatShading=e.flatShading,this.fog=e.fog,this}},De=class extends ln{constructor(e){super(),this.isMeshPhysicalMaterial=!0,this.defines={STANDARD:"",PHYSICAL:""},this.type="MeshPhysicalMaterial",this.anisotropyRotation=0,this.anisotropyMap=null,this.clearcoatMap=null,this.clearcoatRoughness=0,this.clearcoatRoughnessMap=null,this.clearcoatNormalScale=new $(1,1),this.clearcoatNormalMap=null,this.ior=1.5,Object.defineProperty(this,"reflectivity",{get:function(){return q(2.5*(this.ior-1)/(this.ior+1),0,1)},set:function(t){this.ior=(1+.4*t)/(1-.4*t)}}),this.iridescenceMap=null,this.iridescenceIOR=1.3,this.iridescenceThicknessRange=[100,400],this.iridescenceThicknessMap=null,this.sheenColor=new H(0),this.sheenColorMap=null,this.sheenRoughness=1,this.sheenRoughnessMap=null,this.transmissionMap=null,this.thickness=0,this.thicknessMap=null,this.attenuationDistance=1/0,this.attenuationColor=new H(1,1,1),this.specularIntensity=1,this.specularIntensityMap=null,this.specularColor=new H(1,1,1),this.specularColorMap=null,this._anisotropy=0,this._clearcoat=0,this._dispersion=0,this._iridescence=0,this._retroreflectivity=0,this._sheen=0,this._transmission=0,this.setValues(e)}get anisotropy(){return this._anisotropy}set anisotropy(e){this._anisotropy>0!=e>0&&this.version++,this._anisotropy=e}get clearcoat(){return this._clearcoat}set clearcoat(e){this._clearcoat>0!=e>0&&this.version++,this._clearcoat=e}get iridescence(){return this._iridescence}set iridescence(e){this._iridescence>0!=e>0&&this.version++,this._iridescence=e}get dispersion(){return this._dispersion}set dispersion(e){this._dispersion>0!=e>0&&this.version++,this._dispersion=e}get retroreflectivity(){return this._retroreflectivity}set retroreflectivity(e){this._retroreflectivity>0!=e>0&&this.version++,this._retroreflectivity=e}get sheen(){return this._sheen}set sheen(e){this._sheen>0!=e>0&&this.version++,this._sheen=e}get transmission(){return this._transmission}set transmission(e){this._transmission>0!=e>0&&this.version++,this._transmission=e}copy(e){return super.copy(e),this.defines={STANDARD:"",PHYSICAL:""},this.anisotropy=e.anisotropy,this.anisotropyRotation=e.anisotropyRotation,this.anisotropyMap=e.anisotropyMap,this.clearcoat=e.clearcoat,this.clearcoatMap=e.clearcoatMap,this.clearcoatRoughness=e.clearcoatRoughness,this.clearcoatRoughnessMap=e.clearcoatRoughnessMap,this.clearcoatNormalMap=e.clearcoatNormalMap,this.clearcoatNormalScale.copy(e.clearcoatNormalScale),this.dispersion=e.dispersion,this.ior=e.ior,this.iridescence=e.iridescence,this.iridescenceMap=e.iridescenceMap,this.iridescenceIOR=e.iridescenceIOR,this.iridescenceThicknessRange=[...e.iridescenceThicknessRange],this.iridescenceThicknessMap=e.iridescenceThicknessMap,this.retroreflectivity=e.retroreflectivity,this.sheen=e.sheen,this.sheenColor.copy(e.sheenColor),this.sheenColorMap=e.sheenColorMap,this.sheenRoughness=e.sheenRoughness,this.sheenRoughnessMap=e.sheenRoughnessMap,this.transmission=e.transmission,this.transmissionMap=e.transmissionMap,this.thickness=e.thickness,this.thicknessMap=e.thicknessMap,this.attenuationDistance=e.attenuationDistance,this.attenuationColor.copy(e.attenuationColor),this.specularIntensity=e.specularIntensity,this.specularIntensityMap=e.specularIntensityMap,this.specularColor.copy(e.specularColor),this.specularColorMap=e.specularColorMap,this}};function Ot(a,e){return!a||a.constructor===e?a:typeof e.BYTES_PER_ELEMENT=="number"?new e(a):Array.prototype.slice.call(a)}function gs(a){return a!==void 0&&a.inTangents!==void 0&&a.outTangents!==void 0}function Gh(a){function e(i,s){return a[i]-a[s]}let t=a.length,n=new Array(t);for(let i=0;i!==t;++i)n[i]=i;return n.sort(e),n}function zc(a,e,t){let n=a.length,i=new a.constructor(n);for(let s=0,r=0;r!==n;++s){let o=t[s]*e;for(let c=0;c!==e;++c)i[r++]=a[o+c]}return i}function Hh(a,e,t,n){let i=1,s=a[0];for(;s!==void 0&&s[n]===void 0;)s=a[i++];if(s===void 0)return;let r=s[n];if(r!==void 0)if(Array.isArray(r))do r=s[n],r!==void 0&&(e.push(s.time),t.push(...r)),s=a[i++];while(s!==void 0);else if(r.toArray!==void 0)do r=s[n],r!==void 0&&(e.push(s.time),r.toArray(t,t.length)),s=a[i++];while(s!==void 0);else do r=s[n],r!==void 0&&(e.push(s.time),t.push(r)),s=a[i++];while(s!==void 0)}var st=class{constructor(e,t,n,i){this.parameterPositions=e,this._cachedIndex=0,this.resultBuffer=i!==void 0?i:new t.constructor(n),this.sampleValues=t,this.valueSize=n,this.settings=null,this.DefaultSettings_={}}evaluate(e){let t=this.parameterPositions,n=this._cachedIndex,i=t[n],s=t[n-1];n:{e:{let r;t:{i:if(!(e<i)){for(let o=n+2;;){if(i===void 0){if(e<s)break i;return n=t.length,this._cachedIndex=n,this.copySampleValue_(n-1)}if(n===o)break;if(s=i,i=t[++n],e<i)break e}r=t.length;break t}if(!(e>=s)){let o=t[1];e<o&&(n=2,s=o);for(let c=n-2;;){if(s===void 0)return this._cachedIndex=0,this.copySampleValue_(0);if(n===c)break;if(i=s,s=t[--n-1],e>=s)break e}r=n,n=0;break t}break n}for(;n<r;){let o=n+r>>>1;e<t[o]?r=o:n=o+1}if(i=t[n],s=t[n-1],s===void 0)return this._cachedIndex=0,this.copySampleValue_(0);if(i===void 0)return n=t.length,this._cachedIndex=n,this.copySampleValue_(n-1)}this._cachedIndex=n,this.intervalChanged_(n,s,i)}return this.interpolate_(n,s,e,i)}getSettings_(){return this.settings||this.DefaultSettings_}copySampleValue_(e){let t=this.resultBuffer,n=this.sampleValues,i=this.valueSize,s=e*i;for(let r=0;r!==i;++r)t[r]=n[s+r];return t}interpolate_(){throw new Error("THREE.Interpolant: Call to abstract method.")}intervalChanged_(){}},Ts=class extends st{constructor(e,t,n,i){super(e,t,n,i),this._weightPrev=-0,this._offsetPrev=-0,this._weightNext=-0,this._offsetNext=-0,this.DefaultSettings_={endingStart:kr,endingEnd:kr}}intervalChanged_(e,t,n){let i=this.parameterPositions,s=e-2,r=e+1,o=i[s],c=i[r];if(o===void 0)switch(this.getSettings_().endingStart){case zr:s=e,o=2*t-n;break;case Vr:s=i.length-2,o=t+i[s]-i[s+1];break;default:s=e,o=n}if(c===void 0)switch(this.getSettings_().endingEnd){case zr:r=e,c=2*n-t;break;case Vr:r=1,c=n+i[1]-i[0];break;default:r=e-1,c=t}let l=(n-t)*.5,u=this.valueSize;this._weightPrev=l/(t-o),this._weightNext=l/(c-n),this._offsetPrev=s*u,this._offsetNext=r*u}interpolate_(e,t,n,i){let s=this.resultBuffer,r=this.sampleValues,o=this.valueSize,c=e*o,l=c-o,u=this._offsetPrev,h=this._offsetNext,f=this._weightPrev,d=this._weightNext,p=(n-t)/(i-t),m=p*p,b=m*p,x=-f*b+2*f*m-f*p,v=(1+f)*b+(-1.5-2*f)*m+(-.5+f)*p+1,S=(-1-d)*b+(1.5+d)*m+.5*p,y=d*b-d*m;for(let T=0;T!==o;++T)s[T]=x*r[u+T]+v*r[l+T]+S*r[c+T]+y*r[h+T];return s}},ws=class extends st{constructor(e,t,n,i){super(e,t,n,i)}interpolate_(e,t,n,i){let s=this.resultBuffer,r=this.sampleValues,o=this.valueSize,c=e*o,l=c-o,u=(n-t)/(i-t),h=1-u;for(let f=0;f!==o;++f)s[f]=r[l+f]*h+r[c+f]*u;return s}},Es=class extends st{constructor(e,t,n,i){super(e,t,n,i)}interpolate_(e){return this.copySampleValue_(e-1)}},Rs=class extends st{interpolate_(e,t,n,i){let s=this.resultBuffer,r=this.sampleValues,o=this.valueSize,c=e*o,l=c-o,u=this.inTangents,h=this.outTangents;if(!u||!h){let p=(n-t)/(i-t),m=1-p;for(let b=0;b!==o;++b)s[b]=r[l+b]*m+r[c+b]*p;return s}let f=o*2,d=e-1;for(let p=0;p!==o;++p){let m=r[l+p],b=r[c+p],x=d*f+p*2,v=h[x],S=h[x+1],y=e*f+p*2,T=u[y],M=u[y+1],A=Xh(n,t,v,T,i);s[p]=fl(A,m,S,M,b)}return s}};function fl(a,e,t,n,i){let s=1-a;return s*s*s*e+3*s*s*a*t+3*s*a*a*n+a*a*a*i}function Wh(a,e,t,n,i){let s=1-a;return 3*s*s*(t-e)+6*s*a*(n-t)+3*a*a*(i-n)}function Xh(a,e,t,n,i){let s=(a-e)/(i-e);for(let r=0;r<8;r++){let o=fl(s,e,t,n,i)-a;if(Math.abs(o)<1e-10)break;let c=Wh(s,e,t,n,i);if(Math.abs(c)<1e-10)break;s=Math.max(0,Math.min(1,s-o/c))}return s}var Ne=class{constructor(e,t,n,i){if(e===void 0)throw new Error("THREE.KeyframeTrack: track name is undefined");if(t===void 0||t.length===0)throw new Error("THREE.KeyframeTrack: no keyframes in track named "+e);this.name=e,this.times=Ot(t,this.TimeBufferType),this.values=Ot(n,this.ValueBufferType),this.setInterpolation(i||this.DefaultInterpolation)}static toJSON(e){let t=e.constructor,n;if(t.toJSON!==this.toJSON)n=t.toJSON(e);else{n={name:e.name,times:Ot(e.times,Array),values:Ot(e.values,Array)};let i=e.getInterpolation();i!==e.DefaultInterpolation&&(n.interpolation=i),gs(e.settings)&&(n.settings={inTangents:Ot(e.settings.inTangents,Array),outTangents:Ot(e.settings.outTangents,Array)})}return n.type=e.ValueTypeName,n}InterpolantFactoryMethodDiscrete(e){return new Es(this.times,this.values,this.getValueSize(),e)}InterpolantFactoryMethodLinear(e){return new ws(this.times,this.values,this.getValueSize(),e)}InterpolantFactoryMethodSmooth(e){return new Ts(this.times,this.values,this.getValueSize(),e)}InterpolantFactoryMethodBezier(e){let t=new Rs(this.times,this.values,this.getValueSize(),e);return this.settings&&(t.inTangents=this.settings.inTangents,t.outTangents=this.settings.outTangents),t}setInterpolation(e){let t;switch(e){case yt:t=this.InterpolantFactoryMethodDiscrete;break;case vt:t=this.InterpolantFactoryMethodLinear;break;case ds:t=this.InterpolantFactoryMethodSmooth;break;case Br:t=this.InterpolantFactoryMethodBezier;break}if(t===void 0){let n="unsupported interpolation for "+this.ValueTypeName+" keyframe track named "+this.name;if(this.createInterpolant===void 0)if(e!==this.DefaultInterpolation)this.setInterpolation(this.DefaultInterpolation);else throw new Error(n);return ne("KeyframeTrack:",n),this}return this.createInterpolant=t,this}getInterpolation(){switch(this.createInterpolant){case this.InterpolantFactoryMethodDiscrete:return yt;case this.InterpolantFactoryMethodLinear:return vt;case this.InterpolantFactoryMethodSmooth:return ds;case this.InterpolantFactoryMethodBezier:return Br}}getValueSize(){return this.values.length/this.times.length}shift(e){if(e!==0){let t=this.times;for(let n=0,i=t.length;n!==i;++n)t[n]+=e}return this}scale(e){if(e!==1){let t=this.times;for(let n=0,i=t.length;n!==i;++n)t[n]*=e;gs(this.settings)&&(Vc(this.settings.inTangents,e),Vc(this.settings.outTangents,e))}return this}trim(e,t){let n=this.times,i=n.length,s=0,r=i-1;for(;s!==i&&n[s]<e;)++s;for(;r!==-1&&n[r]>t;)--r;if(++r,s!==0||r!==i){s>=r&&(r=Math.max(r,1),s=r-1);let o=this.getValueSize();this.times=n.slice(s,r),this.values=this.values.slice(s*o,r*o)}return this}validate(){let e=!0,t=this.getValueSize();t-Math.floor(t)!==0&&(oe("KeyframeTrack: Invalid value size in track.",this),e=!1);let n=this.times,i=this.values,s=n.length;s===0&&(oe("KeyframeTrack: Track is empty.",this),e=!1);let r=null;for(let o=0;o!==s;o++){let c=n[o];if(typeof c=="number"&&isNaN(c)){oe("KeyframeTrack: Time is not a valid number.",this,o,c),e=!1;break}if(r!==null&&r>c){oe("KeyframeTrack: Out of order keys.",this,o,c,r),e=!1;break}r=c}if(i!==void 0&&sh(i))for(let o=0,c=i.length;o!==c;++o){let l=i[o];if(isNaN(l)){oe("KeyframeTrack: Value is not a valid number.",this,o,l),e=!1;break}}return e}optimize(){let e=this.times.slice(),t=this.values.slice(),n=this.getValueSize(),i=this.getInterpolation()===ds,s=e.length-1,r=1;for(let o=1;o<s;++o){let c=!1,l=e[o],u=e[o+1];if(l!==u&&(o!==1||l!==e[0]))if(i)c=!0;else{let h=o*n,f=h-n,d=h+n;for(let p=0;p!==n;++p){let m=t[h+p];if(m!==t[f+p]||m!==t[d+p]){c=!0;break}}}if(c){if(o!==r){e[r]=e[o];let h=o*n,f=r*n;for(let d=0;d!==n;++d)t[f+d]=t[h+d]}++r}}if(s>0){e[r]=e[s];for(let o=s*n,c=r*n,l=0;l!==n;++l)t[c+l]=t[o+l];++r}return r!==e.length?(this.times=e.slice(0,r),this.values=t.slice(0,r*n)):(this.times=e,this.values=t),this}clone(){let e=this.times.slice(),t=this.values.slice(),n=this.constructor,i=new n(this.name,e,t);return i.createInterpolant=this.createInterpolant,gs(this.settings)&&(i.settings={inTangents:this.settings.inTangents.slice(),outTangents:this.settings.outTangents.slice()}),i}};function Vc(a,e){for(let t=0,n=a.length;t!==n;t+=2)a[t]*=e}Ne.prototype.ValueTypeName="";Ne.prototype.TimeBufferType=Float32Array;Ne.prototype.ValueBufferType=Float32Array;Ne.prototype.DefaultInterpolation=vt;var Mt=class extends Ne{constructor(e,t,n){super(e,t,n)}};Mt.prototype.ValueTypeName="bool";Mt.prototype.ValueBufferType=Array;Mt.prototype.DefaultInterpolation=yt;Mt.prototype.InterpolantFactoryMethodLinear=void 0;Mt.prototype.InterpolantFactoryMethodSmooth=void 0;var pi=class extends Ne{constructor(e,t,n,i){super(e,t,n,i)}};pi.prototype.ValueTypeName="color";var At=class extends Ne{constructor(e,t,n,i){super(e,t,n,i)}};At.prototype.ValueTypeName="number";var Cs=class extends st{constructor(e,t,n,i){super(e,t,n,i)}interpolate_(e,t,n,i){let s=this.resultBuffer,r=this.sampleValues,o=this.valueSize,c=(n-t)/(i-t),l=e*o;for(let u=l+o;l!==u;l+=4)pe.slerpFlat(s,0,r,l-o,r,l,c);return s}},Tt=class extends Ne{constructor(e,t,n,i){super(e,t,n,i)}InterpolantFactoryMethodLinear(e){return new Cs(this.times,this.values,this.getValueSize(),e)}};Tt.prototype.ValueTypeName="quaternion";Tt.prototype.InterpolantFactoryMethodSmooth=void 0;var wt=class extends Ne{constructor(e,t,n){super(e,t,n)}};wt.prototype.ValueTypeName="string";wt.prototype.ValueBufferType=Array;wt.prototype.DefaultInterpolation=yt;wt.prototype.InterpolantFactoryMethodLinear=void 0;wt.prototype.InterpolantFactoryMethodSmooth=void 0;var Wt=class extends Ne{constructor(e,t,n,i){super(e,t,n,i)}};Wt.prototype.ValueTypeName="vector";var mi=class{constructor(e="",t=-1,n=[],i=al){this.name=e,this.tracks=n,this.duration=t,this.blendMode=i,this.uuid=Ze(),this.userData={},this.duration<0&&this.resetDuration()}static parse(e){let t=[],n=e.tracks,i=1/(e.fps||1);for(let r=0,o=n.length;r!==o;++r)t.push(Kh(n[r]).scale(i));let s=new this(e.name,e.duration,t,e.blendMode);return s.uuid=e.uuid,s.userData=JSON.parse(e.userData||"{}"),s}static toJSON(e){let t=[],n=e.tracks,i={name:e.name,duration:e.duration,tracks:t,uuid:e.uuid,blendMode:e.blendMode,userData:JSON.stringify(e.userData)};for(let s=0,r=n.length;s!==r;++s)t.push(Ne.toJSON(n[s]));return i}static CreateFromMorphTargetSequence(e,t,n,i){let s=t.length,r=[];for(let o=0;o<s;o++){let c=[],l=[];c.push((o+s-1)%s,o,(o+1)%s),l.push(0,1,0);let u=Gh(c);c=zc(c,1,u),l=zc(l,1,u),!i&&c[0]===0&&(c.push(s),l.push(l[0])),r.push(new At(".morphTargetInfluences["+t[o].name+"]",c,l).scale(1/n))}return new this(e,-1,r)}static findByName(e,t){let n=e;if(!Array.isArray(e)){let i=e;n=i.geometry&&i.geometry.animations||i.animations}for(let i=0;i<n.length;i++)if(n[i].name===t)return n[i];return null}static CreateClipsFromMorphTargetSequences(e,t,n){let i={},s=/^([\w-]*?)([\d]+)$/;for(let o=0,c=e.length;o<c;o++){let l=e[o],u=l.name.match(s);if(u&&u.length>1){let h=u[1],f=i[h];f||(i[h]=f=[]),f.push(l)}}let r=[];for(let o in i)r.push(this.CreateFromMorphTargetSequence(o,i[o],t,n));return r}resetDuration(){let e=this.tracks,t=0;for(let n=0,i=e.length;n!==i;++n){let s=this.tracks[n];t=Math.max(t,s.times[s.times.length-1])}return this.duration=t,this}trim(){for(let e=0;e<this.tracks.length;e++)this.tracks[e].trim(0,this.duration);return this}validate(){let e=!0;for(let t=0;t<this.tracks.length;t++)e=e&&this.tracks[t].validate();return e}optimize(){for(let e=0;e<this.tracks.length;e++)this.tracks[e].optimize();return this}clone(){let e=[];for(let n=0;n<this.tracks.length;n++)e.push(this.tracks[n].clone());let t=new this.constructor(this.name,this.duration,e,this.blendMode);return t.userData=JSON.parse(JSON.stringify(this.userData)),t}toJSON(){return this.constructor.toJSON(this)}};function qh(a){switch(a.toLowerCase()){case"scalar":case"double":case"float":case"number":case"integer":return At;case"vector":case"vector2":case"vector3":case"vector4":return Wt;case"color":return pi;case"quaternion":return Tt;case"bool":case"boolean":return Mt;case"string":return wt}throw new Error("THREE.KeyframeTrack: Unsupported typeName: "+a)}function Kh(a){if(a.type===void 0)throw new Error("THREE.KeyframeTrack: track type undefined, can not parse");let e=qh(a.type);if(a.times===void 0){let n=[],i=[];Hh(a.keys,n,i,"value"),a.times=n,a.values=i}let t;return e.parse!==void 0?t=e.parse(a):t=new e(a.name,a.times,a.values,a.interpolation),gs(a.settings)&&(t.settings={inTangents:Ot(a.settings.inTangents,Float32Array),outTangents:Ot(a.settings.outTangents,Float32Array)}),t}var tt={enabled:!1,files:{},add:function(a,e){this.enabled!==!1&&(Gc(a)||(this.files[a]=e))},get:function(a){if(this.enabled!==!1&&!Gc(a))return this.files[a]},remove:function(a){delete this.files[a]},clear:function(){this.files={}}};function Gc(a){try{let e=a.slice(a.indexOf(":")+1);return new URL(e).protocol==="blob:"}catch{return!1}}var Is=class{constructor(e,t,n){let i=this,s=!1,r=0,o=0,c,l=[];this.onStart=void 0,this.onLoad=e,this.onProgress=t,this.onError=n,this._abortController=null,this.itemStart=function(u){o++,s===!1&&i.onStart!==void 0&&i.onStart(u,r,o),s=!0},this.itemEnd=function(u){r++,i.onProgress!==void 0&&i.onProgress(u,r,o),r===o&&(s=!1,i.onLoad!==void 0&&i.onLoad())},this.itemError=function(u){i.onError!==void 0&&i.onError(u)},this.resolveURL=function(u){return u=u.normalize("NFC"),c?c(u):u},this.setURLModifier=function(u){return c=u,this},this.addHandler=function(u,h){return l.push(u,h),this},this.removeHandler=function(u){let h=l.indexOf(u);return h!==-1&&l.splice(h,2),this},this.getHandler=function(u){for(let h=0,f=l.length;h<f;h+=2){let d=l[h],p=l[h+1];if(d.global&&(d.lastIndex=0),d.test(u))return p}return null},this.abort=function(){return this.abortController.abort(),this._abortController=null,this}}get abortController(){return this._abortController||(this._abortController=new AbortController),this._abortController}},dl=new Is,rt=class{constructor(e){this.manager=e!==void 0?e:dl,this.crossOrigin="anonymous",this.withCredentials=!1,this.path="",this.resourcePath="",this.requestHeader={},typeof __THREE_DEVTOOLS__<"u"&&__THREE_DEVTOOLS__.dispatchEvent(new CustomEvent("observe",{detail:this}))}load(){}loadAsync(e,t){let n=this;return new Promise(function(i,s){n.load(e,i,t,s)})}parse(){}setCrossOrigin(e){return this.crossOrigin=e,this}setWithCredentials(e){return this.withCredentials=e,this}setPath(e){return this.path=e,this}setResourcePath(e){return this.resourcePath=e,this}setRequestHeader(e){return this.requestHeader=e,this}abort(){return this}};rt.DEFAULT_MATERIAL_NAME="__DEFAULT";var gt={},Xr=class extends Error{constructor(e,t){super(e),this.response=t}},zn=class extends rt{constructor(e){super(e),this.mimeType="",this.responseType="",this._abortController=new AbortController}load(e,t,n,i){e===void 0&&(e=""),this.path!==void 0&&(e=this.path+e),e=this.manager.resolveURL(e);let s=tt.get(`file:${e}`);if(s!==void 0){this.manager.itemStart(e),setTimeout(()=>{t&&t(s),this.manager.itemEnd(e)},0);return}if(gt[e]!==void 0){gt[e].push({onLoad:t,onProgress:n,onError:i});return}gt[e]=[],gt[e].push({onLoad:t,onProgress:n,onError:i});let r=new Request(e,{headers:new Headers(this.requestHeader),credentials:this.withCredentials?"include":"same-origin",signal:typeof AbortSignal.any=="function"?AbortSignal.any([this._abortController.signal,this.manager.abortController.signal]):this._abortController.signal}),o=this.mimeType,c=this.responseType;fetch(r).then(l=>{if(l.status===200||l.status===0){if(l.status===0&&ne("FileLoader: HTTP Status 0 received."),typeof ReadableStream>"u"||l.body===void 0||l.body.getReader===void 0)return l;let u=gt[e],h=l.body.getReader(),f=l.headers.get("X-File-Size")||l.headers.get("Content-Length"),d=f?parseInt(f):0,p=d!==0,m=0,b=new ReadableStream({start(x){v();function v(){h.read().then(({done:S,value:y})=>{if(S)x.close();else{m+=y.byteLength;let T=new ProgressEvent("progress",{lengthComputable:p,loaded:m,total:d});for(let M=0,A=u.length;M<A;M++){let g=u[M];g.onProgress&&g.onProgress(T)}x.enqueue(y),v()}},S=>{x.error(S)})}}});return new Response(b)}else throw new Xr(`fetch for "${l.url}" responded with ${l.status}: ${l.statusText}`,l)}).then(l=>{switch(c){case"arraybuffer":return l.arrayBuffer();case"blob":return l.blob();case"document":return l.text().then(u=>new DOMParser().parseFromString(u,o));case"json":return l.json();default:if(o==="")return l.text();{let h=/charset="?([^;"\s]*)"?/i.exec(o),f=h&&h[1]?h[1].toLowerCase():void 0,d=new TextDecoder(f);return l.arrayBuffer().then(p=>d.decode(p))}}}).then(l=>{tt.add(`file:${e}`,l);let u=gt[e];delete gt[e];for(let h=0,f=u.length;h<f;h++){let d=u[h];d.onLoad&&d.onLoad(l)}}).catch(l=>{let u=gt[e];if(u===void 0)throw this.manager.itemError(e),l;delete gt[e];for(let h=0,f=u.length;h<f;h++){let d=u[h];d.onError&&d.onError(l)}this.manager.itemError(e)}).finally(()=>{this.manager.itemEnd(e)}),this.manager.itemStart(e)}setResponseType(e){return this.responseType=e,this}setMimeType(e){return this.mimeType=e,this}abort(){return this._abortController.abort(),this._abortController=new AbortController,this}};var Rn=new WeakMap,Ps=class extends rt{constructor(e){super(e)}load(e,t,n,i){this.path!==void 0&&(e=this.path+e),e=this.manager.resolveURL(e);let s=this,r=tt.get(`image:${e}`);if(r!==void 0){if(r.complete===!0)s.manager.itemStart(e),setTimeout(function(){t&&t(r),s.manager.itemEnd(e)},0);else{let h=Rn.get(r);h===void 0&&(h=[],Rn.set(r,h)),h.push({onLoad:t,onError:i})}return r}let o=bs("img");function c(){u(),t&&t(this);let h=Rn.get(this)||[];for(let f=0;f<h.length;f++){let d=h[f];d.onLoad&&d.onLoad(this)}Rn.delete(this),s.manager.itemEnd(e)}function l(h){u(),i&&i(h),tt.remove(`image:${e}`);let f=Rn.get(this)||[];for(let d=0;d<f.length;d++){let p=f[d];p.onError&&p.onError(h)}Rn.delete(this),s.manager.itemError(e),s.manager.itemEnd(e)}function u(){o.removeEventListener("load",c,!1),o.removeEventListener("error",l,!1)}return o.addEventListener("load",c,!1),o.addEventListener("error",l,!1),e.slice(0,5)!=="data:"&&this.crossOrigin!==void 0&&(o.crossOrigin=this.crossOrigin),tt.add(`image:${e}`,o),s.manager.itemStart(e),o.src=e,o}};var gi=class extends rt{constructor(e){super(e)}load(e,t,n,i){let s=new We,r=new Ps(this.manager);return r.setCrossOrigin(this.crossOrigin),r.setPath(this.path),r.load(e,function(o){s.image=o,s.needsUpdate=!0,t!==void 0&&t(s)},n,i),s}},Vn=class extends le{constructor(e,t=1){super(),this.isLight=!0,this.type="Light",this.color=new H(e),this.intensity=t}copy(e,t){return super.copy(e,t),this.color.copy(e.color),this.intensity=e.intensity,this}toJSON(e){let t=super.toJSON(e);return t.object.color=this.color.getHex(),t.object.intensity=this.intensity,t}};var Rr=new z,Hc=new E,Wc=new E,Gn=class{constructor(e){this.camera=e,this.intensity=1,this.bias=0,this.biasNode=null,this.normalBias=0,this.radius=1,this.blurSamples=8,this.mapSize=new $(512,512),this.mapType=oa,this.map=null,this.mapPass=null,this.matrix=new z,this.autoUpdate=!0,this.needsUpdate=!1,this._frustum=new Ss,this._frameExtents=new $(1,1),this._viewportCount=1,this._viewports=[new Xe(0,0,1,1)]}getViewportCount(){return this._viewportCount}getCamera(){return this.camera}getFrustum(){return this._frustum}updateMatrices(e){let t=this.camera;Hc.setFromMatrixPosition(e.matrixWorld),t.position.copy(Hc),Wc.setFromMatrixPosition(e.target.matrixWorld),t.lookAt(Wc),t.updateMatrixWorld(),this._updateMatrix(t,this.matrix,this._frustum)}_updateMatrix(e,t,n,i){Rr.multiplyMatrices(e.projectionMatrix,e.matrixWorldInverse),n.setFromProjectionMatrix(Rr,e.coordinateSystem,e.reversedDepth);let s=this._frameExtents,r=i?i.z/s.x:1,o=i?i.w/s.y:1,c=i?i.x/s.x:0,l=i?i.y/s.y:0;e.coordinateSystem===ai||e.reversedDepth?t.set(.5*r,0,0,.5*r+c,0,.5*o,0,.5*o+l,0,0,1,0,0,0,0,1):t.set(.5*r,0,0,.5*r+c,0,.5*o,0,.5*o+l,0,0,.5,.5,0,0,0,1),t.multiply(Rr)}getViewport(e){return this._viewports[e]}getFrameExtents(){return this._frameExtents}dispose(){this.map&&this.map.dispose(),this.mapPass&&this.mapPass.dispose()}copy(e){return this.camera=e.camera.clone(),this.intensity=e.intensity,this.bias=e.bias,this.radius=e.radius,this.autoUpdate=e.autoUpdate,this.needsUpdate=e.needsUpdate,this.normalBias=e.normalBias,this.blurSamples=e.blurSamples,this.mapSize.copy(e.mapSize),this.biasNode=e.biasNode,this}clone(){return new this.constructor().copy(this)}toJSON(){let e={};return e.intensity=this.intensity,e.bias=this.bias,e.normalBias=this.normalBias,e.radius=this.radius,e.blurSamples=this.blurSamples,e.mapSize=this.mapSize.toArray(),e.camera=this.camera.toJSON(!1).object,delete e.camera.matrix,e}},hs=new E,fs=new pe,Qe=new E,xi=class extends le{constructor(){super(),this.isCamera=!0,this.type="Camera",this.matrixWorldInverse=new z,this.projectionMatrix=new z,this.projectionMatrixInverse=new z,this.coordinateSystem=kt,this._reversedDepth=!1}get reversedDepth(){return this._reversedDepth}copy(e,t){return super.copy(e,t),this.matrixWorldInverse.copy(e.matrixWorldInverse),this.projectionMatrix.copy(e.projectionMatrix),this.projectionMatrixInverse.copy(e.projectionMatrixInverse),this.coordinateSystem=e.coordinateSystem,this}getWorldDirection(e){return super.getWorldDirection(e).negate()}updateMatrixWorld(e){super.updateMatrixWorld(e),this.matrixWorld.decompose(hs,fs,Qe),Qe.x===1&&Qe.y===1&&Qe.z===1?this.matrixWorldInverse.copy(this.matrixWorld).invert():this.matrixWorldInverse.compose(hs,fs,Qe.set(1,1,1)).invert()}updateWorldMatrix(e,t,n=!1){super.updateWorldMatrix(e,t,n),this.matrixWorld.decompose(hs,fs,Qe),Qe.x===1&&Qe.y===1&&Qe.z===1?this.matrixWorldInverse.copy(this.matrixWorld).invert():this.matrixWorldInverse.compose(hs,fs,Qe.set(1,1,1)).invert()}clone(){return new this.constructor().copy(this)}},Ut=new E,Xc=new $,qc=new $,un=class extends xi{constructor(e=50,t=1,n=.1,i=2e3){super(),this.isPerspectiveCamera=!0,this.type="PerspectiveCamera",this.fov=e,this.zoom=1,this.near=n,this.far=i,this.focus=10,this.aspect=t,this.view=null,this.filmGauge=35,this.filmOffset=0,this.updateProjectionMatrix()}copy(e,t){return super.copy(e,t),this.fov=e.fov,this.zoom=e.zoom,this.near=e.near,this.far=e.far,this.focus=e.focus,this.aspect=e.aspect,this.view=e.view===null?null:Object.assign({},e.view),this.filmGauge=e.filmGauge,this.filmOffset=e.filmOffset,this}setFocalLength(e){let t=.5*this.getFilmHeight()/e;this.fov=Ln*2*Math.atan(t),this.updateProjectionMatrix()}getFocalLength(){let e=Math.tan(si*.5*this.fov);return .5*this.getFilmHeight()/e}getEffectiveFOV(){return Ln*2*Math.atan(Math.tan(si*.5*this.fov)/this.zoom)}getFilmWidth(){return this.filmGauge*Math.min(this.aspect,1)}getFilmHeight(){return this.filmGauge/Math.max(this.aspect,1)}getViewBounds(e,t,n){Ut.set(-1,-1,.5).applyMatrix4(this.projectionMatrixInverse),t.set(Ut.x,Ut.y).multiplyScalar(-e/Ut.z),Ut.set(1,1,.5).applyMatrix4(this.projectionMatrixInverse),n.set(Ut.x,Ut.y).multiplyScalar(-e/Ut.z)}getViewSize(e,t){return this.getViewBounds(e,Xc,qc),t.subVectors(qc,Xc)}setViewOffset(e,t,n,i,s,r){this.aspect=e/t,this.view===null&&(this.view={enabled:!0,fullWidth:1,fullHeight:1,offsetX:0,offsetY:0,width:1,height:1}),this.view.enabled=!0,this.view.fullWidth=e,this.view.fullHeight=t,this.view.offsetX=n,this.view.offsetY=i,this.view.width=s,this.view.height=r,this.updateProjectionMatrix()}clearViewOffset(){this.view!==null&&(this.view.enabled=!1),this.updateProjectionMatrix()}updateProjectionMatrix(){let e=this.near,t=e*Math.tan(si*.5*this.fov)/this.zoom,n=2*t,i=this.aspect*n,s=-.5*i,r=this.view;if(this.view!==null&&this.view.enabled){let c=r.fullWidth,l=r.fullHeight;s+=r.offsetX*i/c,t-=r.offsetY*n/l,i*=r.width/c,n*=r.height/l}let o=this.filmOffset;o!==0&&(s+=e*o/this.getFilmWidth()),this.projectionMatrix.makePerspective(s,s+i,t,t-n,e,this.far,this.coordinateSystem,this.reversedDepth),this.projectionMatrixInverse.copy(this.projectionMatrix).invert()}toJSON(e){let t=super.toJSON(e);return t.object.fov=this.fov,t.object.zoom=this.zoom,t.object.near=this.near,t.object.far=this.far,t.object.focus=this.focus,t.object.aspect=this.aspect,this.view!==null&&(t.object.view=Object.assign({},this.view)),t.object.filmGauge=this.filmGauge,t.object.filmOffset=this.filmOffset,t}},qr=class extends Gn{constructor(){super(new un(50,1,.5,500)),this.isSpotLightShadow=!0,this.focus=1,this.aspect=1}updateMatrices(e){let t=this.camera,n=Ln*2*e.angle*this.focus,i=this.mapSize.width/this.mapSize.height*this.aspect,s=e.distance||t.far;(n!==t.fov||i!==t.aspect||s!==t.far)&&(t.fov=n,t.aspect=i,t.far=s,t.updateProjectionMatrix()),super.updateMatrices(e)}copy(e){return super.copy(e),this.focus=e.focus,this.aspect=e.aspect,this}toJSON(){let e=super.toJSON();return e.focus=this.focus,e.aspect=this.aspect,e}},bi=class extends Vn{constructor(e,t,n=0,i=Math.PI/3,s=0,r=2){super(e,t),this.isSpotLight=!0,this.type="SpotLight",this.position.copy(le.DEFAULT_UP),this.updateMatrix(),this.target=new le,this.distance=n,this.angle=i,this.penumbra=s,this.decay=r,this.map=null,this.shadow=new qr}get power(){return this.intensity*Math.PI}set power(e){this.intensity=e/Math.PI}dispose(){super.dispose(),this.shadow.dispose()}copy(e,t){return super.copy(e,t),this.distance=e.distance,this.angle=e.angle,this.penumbra=e.penumbra,this.decay=e.decay,this.target=e.target.clone(),this.map=e.map,this.shadow=e.shadow.clone(),this}toJSON(e){let t=super.toJSON(e);return t.object.distance=this.distance,t.object.angle=this.angle,t.object.decay=this.decay,t.object.penumbra=this.penumbra,t.object.target=this.target.uuid,this.map&&this.map.isTexture&&(t.object.map=this.map.toJSON(e).uuid),t.object.shadow=this.shadow.toJSON(),t}},Kr=class extends Gn{constructor(){super(new un(90,1,.5,500)),this.isPointLightShadow=!0}},_i=class extends Vn{constructor(e,t,n=0,i=2){super(e,t),this.isPointLight=!0,this.type="PointLight",this.distance=n,this.decay=i,this.shadow=new Kr}get power(){return this.intensity*4*Math.PI}set power(e){this.intensity=e/(4*Math.PI)}dispose(){super.dispose(),this.shadow.dispose()}copy(e,t){return super.copy(e,t),this.distance=e.distance,this.decay=e.decay,this.shadow=e.shadow.clone(),this}toJSON(e){let t=super.toJSON(e);return t.object.distance=this.distance,t.object.decay=this.decay,t.object.shadow=this.shadow.toJSON(),t}},Hn=class extends xi{constructor(e=-1,t=1,n=1,i=-1,s=.1,r=2e3){super(),this.isOrthographicCamera=!0,this.type="OrthographicCamera",this.zoom=1,this.view=null,this.left=e,this.right=t,this.top=n,this.bottom=i,this.near=s,this.far=r,this.updateProjectionMatrix()}copy(e,t){return super.copy(e,t),this.left=e.left,this.right=e.right,this.top=e.top,this.bottom=e.bottom,this.near=e.near,this.far=e.far,this.zoom=e.zoom,this.view=e.view===null?null:Object.assign({},e.view),this}setViewOffset(e,t,n,i,s,r){this.view===null&&(this.view={enabled:!0,fullWidth:1,fullHeight:1,offsetX:0,offsetY:0,width:1,height:1}),this.view.enabled=!0,this.view.fullWidth=e,this.view.fullHeight=t,this.view.offsetX=n,this.view.offsetY=i,this.view.width=s,this.view.height=r,this.updateProjectionMatrix()}clearViewOffset(){this.view!==null&&(this.view.enabled=!1),this.updateProjectionMatrix()}updateProjectionMatrix(){let e=(this.right-this.left)/(2*this.zoom),t=(this.top-this.bottom)/(2*this.zoom),n=(this.right+this.left)/2,i=(this.top+this.bottom)/2,s=n-e,r=n+e,o=i+t,c=i-t;if(this.view!==null&&this.view.enabled){let l=(this.right-this.left)/this.view.fullWidth/this.zoom,u=(this.top-this.bottom)/this.view.fullHeight/this.zoom;s+=l*this.view.offsetX,r=s+l*this.view.width,o-=u*this.view.offsetY,c=o-u*this.view.height}this.projectionMatrix.makeOrthographic(s,r,o,c,this.near,this.far,this.coordinateSystem,this.reversedDepth),this.projectionMatrixInverse.copy(this.projectionMatrix).invert()}toJSON(e){let t=super.toJSON(e);return t.object.zoom=this.zoom,t.object.left=this.left,t.object.right=this.right,t.object.top=this.top,t.object.bottom=this.bottom,t.object.near=this.near,t.object.far=this.far,this.view!==null&&(t.object.view=Object.assign({},this.view)),t}},Yr=class extends Gn{constructor(){super(new Hn(-5,5,5,-5,.5,500)),this.isDirectionalLightShadow=!0}},yi=class extends Vn{constructor(e,t){super(e,t),this.isDirectionalLight=!0,this.type="DirectionalLight",this.position.copy(le.DEFAULT_UP),this.updateMatrix(),this.target=new le,this.shadow=new Yr}dispose(){super.dispose(),this.shadow.dispose()}copy(e){return super.copy(e),this.target=e.target.clone(),this.shadow=e.shadow.clone(),this}toJSON(e){let t=super.toJSON(e);return t.object.shadow=this.shadow.toJSON(),t.object.target=this.target.uuid,t}};var Et=class{static extractUrlBase(e){let t=e.lastIndexOf("/");return t===-1?"./":e.slice(0,t+1)}static resolveURL(e,t){return typeof e!="string"||e===""?"":(/^https?:\/\//i.test(t)&&/^\//.test(e)&&(t=t.replace(/(^https?:\/\/[^\/]+).*/i,"$1")),/^(https?:)?\/\//i.test(e)||/^data:.*,.*$/i.test(e)||/^blob:.*$/i.test(e)?e:t+e)}};var Cr=new WeakMap,vi=class extends rt{constructor(e){super(e),this.isImageBitmapLoader=!0,typeof createImageBitmap>"u"&&ne("ImageBitmapLoader: createImageBitmap() not supported."),typeof fetch>"u"&&ne("ImageBitmapLoader: fetch() not supported."),this.options={premultiplyAlpha:"none"},this._abortController=new AbortController}setOptions(e){return this.options=e,this}load(e,t,n,i){e===void 0&&(e=""),this.path!==void 0&&(e=this.path+e),e=this.manager.resolveURL(e);let s=this,r=tt.get(`image-bitmap:${e}`);if(r!==void 0){if(s.manager.itemStart(e),r.then){r.then(l=>{Cr.has(r)===!0?(i&&i(Cr.get(r)),s.manager.itemError(e),s.manager.itemEnd(e)):(t&&t(l),s.manager.itemEnd(e))});return}setTimeout(function(){t&&t(r),s.manager.itemEnd(e)},0);return}let o={};o.credentials=this.crossOrigin==="anonymous"?"same-origin":"include",o.headers=this.requestHeader,o.signal=typeof AbortSignal.any=="function"?AbortSignal.any([this._abortController.signal,this.manager.abortController.signal]):this._abortController.signal;let c=fetch(e,o).then(function(l){return l.blob()}).then(function(l){return createImageBitmap(l,Object.assign({},s.options,{colorSpaceConversion:"none"}))}).then(function(l){return tt.add(`image-bitmap:${e}`,l),t&&t(l),s.manager.itemEnd(e),l}).catch(function(l){i&&i(l),Cr.set(c,l),tt.remove(`image-bitmap:${e}`),s.manager.itemError(e),s.manager.itemEnd(e)});tt.add(`image-bitmap:${e}`,c),s.manager.itemStart(e)}abort(){return this._abortController.abort(),this._abortController=new AbortController,this}};var ha="\\[\\]\\.:\\/",Yh=new RegExp("["+ha+"]","g"),fa="[^"+ha+"]",jh="[^"+ha.replace("\\.","")+"]",Jh=/((?:WC+[\/:])*)/.source.replace("WC",fa),Zh=/(WCOD+)?/.source.replace("WCOD",jh),$h=/(?:\.(WC+)(?:\[(.+)\])?)?/.source.replace("WC",fa),Qh=/\.(WC+)(?:\[(.+)\])?/.source.replace("WC",fa),ef=new RegExp("^"+Jh+Zh+$h+Qh+"$"),tf=["material","materials","bones","map"],jr=class{constructor(e,t,n){let i=n||j.parseTrackName(t);this._targetGroup=e,this._bindings=e.subscribe_(t,i)}getValue(e,t){this.bind();let n=this._targetGroup.nCachedObjects_,i=this._bindings[n];i!==void 0&&i.getValue(e,t)}setValue(e,t){let n=this._bindings;for(let i=this._targetGroup.nCachedObjects_,s=n.length;i!==s;++i)n[i].setValue(e,t)}bind(){let e=this._bindings;for(let t=this._targetGroup.nCachedObjects_,n=e.length;t!==n;++t)e[t].bind()}unbind(){let e=this._bindings;for(let t=this._targetGroup.nCachedObjects_,n=e.length;t!==n;++t)e[t].unbind()}},j=class a{constructor(e,t,n){this.path=t,this.parsedPath=n||a.parseTrackName(t),this.node=a.findNode(e,this.parsedPath.nodeName),this.rootNode=e,this.getValue=this._getValue_unbound,this.setValue=this._setValue_unbound}static create(e,t,n){return e&&e.isAnimationObjectGroup?new a.Composite(e,t,n):new a(e,t,n)}static sanitizeNodeName(e){return e.replace(/\s/g,"_").replace(Yh,"")}static parseTrackName(e){let t=ef.exec(e);if(t===null)throw new Error("THREE.PropertyBinding: Cannot parse trackName: "+e);let n={nodeName:t[2],objectName:t[3],objectIndex:t[4],propertyName:t[5],propertyIndex:t[6]},i=n.nodeName&&n.nodeName.lastIndexOf(".");if(i!==void 0&&i!==-1){let s=n.nodeName.substring(i+1);tf.indexOf(s)!==-1&&(n.nodeName=n.nodeName.substring(0,i),n.objectName=s)}if(n.propertyName===null||n.propertyName.length===0)throw new Error("THREE.PropertyBinding: can not parse propertyName from trackName: "+e);return n}static findNode(e,t){if(t===void 0||t===""||t==="."||t===-1||t===e.name||t===e.uuid)return e;if(e.skeleton){let n=e.skeleton.getBoneByName(t);if(n!==void 0)return n}if(e.children){let n=function(s){for(let r=0;r<s.length;r++){let o=s[r];if(o.name===t||o.uuid===t)return o;let c=n(o.children);if(c)return c}return null},i=n(e.children);if(i)return i}return null}_getValue_unavailable(){}_setValue_unavailable(){}_getValue_direct(e,t){e[t]=this.targetObject[this.propertyName]}_getValue_array(e,t){let n=this.resolvedProperty;for(let i=0,s=n.length;i!==s;++i)e[t++]=n[i]}_getValue_arrayElement(e,t){e[t]=this.resolvedProperty[this.propertyIndex]}_getValue_toArray(e,t){this.resolvedProperty.toArray(e,t)}_setValue_direct(e,t){this.targetObject[this.propertyName]=e[t]}_setValue_direct_setNeedsUpdate(e,t){this.targetObject[this.propertyName]=e[t],this.targetObject.needsUpdate=!0}_setValue_direct_setMatrixWorldNeedsUpdate(e,t){this.targetObject[this.propertyName]=e[t],this.targetObject.matrixWorldNeedsUpdate=!0}_setValue_array(e,t){let n=this.resolvedProperty;for(let i=0,s=n.length;i!==s;++i)n[i]=e[t++]}_setValue_array_setNeedsUpdate(e,t){let n=this.resolvedProperty;for(let i=0,s=n.length;i!==s;++i)n[i]=e[t++];this.targetObject.needsUpdate=!0}_setValue_array_setMatrixWorldNeedsUpdate(e,t){let n=this.resolvedProperty;for(let i=0,s=n.length;i!==s;++i)n[i]=e[t++];this.targetObject.matrixWorldNeedsUpdate=!0}_setValue_arrayElement(e,t){this.resolvedProperty[this.propertyIndex]=e[t]}_setValue_arrayElement_setNeedsUpdate(e,t){this.resolvedProperty[this.propertyIndex]=e[t],this.targetObject.needsUpdate=!0}_setValue_arrayElement_setMatrixWorldNeedsUpdate(e,t){this.resolvedProperty[this.propertyIndex]=e[t],this.targetObject.matrixWorldNeedsUpdate=!0}_setValue_fromArray(e,t){this.resolvedProperty.fromArray(e,t)}_setValue_fromArray_setNeedsUpdate(e,t){this.resolvedProperty.fromArray(e,t),this.targetObject.needsUpdate=!0}_setValue_fromArray_setMatrixWorldNeedsUpdate(e,t){this.resolvedProperty.fromArray(e,t),this.targetObject.matrixWorldNeedsUpdate=!0}_getValue_unbound(e,t){this.bind(),this.getValue(e,t)}_setValue_unbound(e,t){this.bind(),this.setValue(e,t)}bind(){let e=this.node,t=this.parsedPath,n=t.objectName,i=t.propertyName,s=t.propertyIndex;if(e||(e=a.findNode(this.rootNode,t.nodeName),this.node=e),this.getValue=this._getValue_unavailable,this.setValue=this._setValue_unavailable,!e){ne("PropertyBinding: No target node found for track: "+this.path+".");return}if(n){let l=t.objectIndex;switch(n){case"materials":if(!e.material){oe("PropertyBinding: Can not bind to material as node does not have a material.",this);return}if(!e.material.materials){oe("PropertyBinding: Can not bind to material.materials as node.material does not have a materials array.",this);return}e=e.material.materials;break;case"bones":if(!e.skeleton){oe("PropertyBinding: Can not bind to bones as node does not have a skeleton.",this);return}e=e.skeleton.bones;for(let u=0;u<e.length;u++)if(e[u].name===l){l=u;break}break;case"map":if("map"in e){e=e.map;break}if(!e.material){oe("PropertyBinding: Can not bind to material as node does not have a material.",this);return}if(!e.material.map){oe("PropertyBinding: Can not bind to material.map as node.material does not have a map.",this);return}e=e.material.map;break;default:if(e[n]===void 0){oe("PropertyBinding: Can not bind to objectName of node undefined.",this);return}e=e[n]}if(l!==void 0){if(e[l]===void 0){oe("PropertyBinding: Trying to bind to objectIndex of objectName, but is undefined.",this,e);return}e=e[l]}}let r=e[i];if(r===void 0){let l=t.nodeName;oe("PropertyBinding: Trying to update property for track: "+l+"."+i+" but it wasn't found.",e);return}let o=this.Versioning.None;this.targetObject=e,e.isMaterial===!0?o=this.Versioning.NeedsUpdate:e.isObject3D===!0&&(o=this.Versioning.MatrixWorldNeedsUpdate);let c=this.BindingType.Direct;if(s!==void 0){if(i==="morphTargetInfluences"){if(!e.geometry){oe("PropertyBinding: Can not bind to morphTargetInfluences because node does not have a geometry.",this);return}if(!e.geometry.morphAttributes){oe("PropertyBinding: Can not bind to morphTargetInfluences because node does not have a geometry.morphAttributes.",this);return}e.morphTargetDictionary[s]!==void 0&&(s=e.morphTargetDictionary[s])}c=this.BindingType.ArrayElement,this.resolvedProperty=r,this.propertyIndex=s}else r.fromArray!==void 0&&r.toArray!==void 0?(c=this.BindingType.HasFromToArray,this.resolvedProperty=r):Array.isArray(r)?(c=this.BindingType.EntireArray,this.resolvedProperty=r):this.propertyName=i;this.getValue=this.GetterByBindingType[c],this.setValue=this.SetterByBindingTypeAndVersioning[c][o]}unbind(){this.node=null,this.getValue=this._getValue_unbound,this.setValue=this._setValue_unbound}};j.Composite=jr;j.prototype.BindingType={Direct:0,EntireArray:1,ArrayElement:2,HasFromToArray:3};j.prototype.Versioning={None:0,NeedsUpdate:1,MatrixWorldNeedsUpdate:2};j.prototype.GetterByBindingType=[j.prototype._getValue_direct,j.prototype._getValue_array,j.prototype._getValue_arrayElement,j.prototype._getValue_toArray];j.prototype.SetterByBindingTypeAndVersioning=[[j.prototype._setValue_direct,j.prototype._setValue_direct_setNeedsUpdate,j.prototype._setValue_direct_setMatrixWorldNeedsUpdate],[j.prototype._setValue_array,j.prototype._setValue_array_setNeedsUpdate,j.prototype._setValue_array_setMatrixWorldNeedsUpdate],[j.prototype._setValue_arrayElement,j.prototype._setValue_arrayElement_setNeedsUpdate,j.prototype._setValue_arrayElement_setMatrixWorldNeedsUpdate],[j.prototype._setValue_fromArray,j.prototype._setValue_fromArray_setNeedsUpdate,j.prototype._setValue_fromArray_setMatrixWorldNeedsUpdate]];var S0=new Float32Array(1);var xa=class xa{constructor(e,t,n,i){this.elements=[1,0,0,1],e!==void 0&&this.set(e,t,n,i)}identity(){return this.set(1,0,0,1),this}fromArray(e,t=0){for(let n=0;n<4;n++)this.elements[n]=e[n+t];return this}set(e,t,n,i){let s=this.elements;return s[0]=e,s[2]=t,s[1]=n,s[3]=i,this}};xa.prototype.isMatrix2=!0;var Jr=xa;typeof __THREE_DEVTOOLS__<"u"&&__THREE_DEVTOOLS__.dispatchEvent(new CustomEvent("register",{detail:{revision:"186"}}));typeof window<"u"&&(window.__THREE__?ne("WARNING: Multiple instances of Three.js being imported."):window.__THREE__="186");var nf=`#ifdef USE_ALPHAHASH
	if ( diffuseColor.a < getAlphaHashThreshold( vPosition ) ) discard;
#endif`,sf=`#ifdef USE_ALPHAHASH
	const float ALPHA_HASH_SCALE = 0.05;
	float hash2D( vec2 value ) {
		return fract( 1.0e4 * sin( 17.0 * value.x + 0.1 * value.y ) * ( 0.1 + abs( sin( 13.0 * value.y + value.x ) ) ) );
	}
	float hash3D( vec3 value ) {
		return hash2D( vec2( hash2D( value.xy ), value.z ) );
	}
	float getAlphaHashThreshold( vec3 position ) {
		float maxDeriv = max(
			length( dFdx( position.xyz ) ),
			length( dFdy( position.xyz ) )
		);
		float pixScale = 1.0 / ( ALPHA_HASH_SCALE * maxDeriv );
		vec2 pixScales = vec2(
			exp2( floor( log2( pixScale ) ) ),
			exp2( ceil( log2( pixScale ) ) )
		);
		vec2 alpha = vec2(
			hash3D( floor( pixScales.x * position.xyz ) ),
			hash3D( floor( pixScales.y * position.xyz ) )
		);
		float lerpFactor = fract( log2( pixScale ) );
		float x = ( 1.0 - lerpFactor ) * alpha.x + lerpFactor * alpha.y;
		float a = min( lerpFactor, 1.0 - lerpFactor );
		vec3 cases = vec3(
			x * x / ( 2.0 * a * ( 1.0 - a ) ),
			( x - 0.5 * a ) / ( 1.0 - a ),
			1.0 - ( ( 1.0 - x ) * ( 1.0 - x ) / ( 2.0 * a * ( 1.0 - a ) ) )
		);
		float threshold = ( x < ( 1.0 - a ) )
			? ( ( x < a ) ? cases.x : cases.y )
			: cases.z;
		return clamp( threshold , 1.0e-6, 1.0 );
	}
#endif`,rf=`#ifdef USE_ALPHAMAP
	diffuseColor.a *= texture2D( alphaMap, vAlphaMapUv ).g;
#endif`,af=`#ifdef USE_ALPHAMAP
	uniform sampler2D alphaMap;
#endif`,of=`#ifdef USE_ALPHATEST
	#ifdef ALPHA_TO_COVERAGE
	diffuseColor.a = smoothstep( alphaTest, alphaTest + fwidth( diffuseColor.a ), diffuseColor.a );
	if ( diffuseColor.a == 0.0 ) discard;
	#else
	if ( diffuseColor.a < alphaTest ) discard;
	#endif
#endif`,cf=`#ifdef USE_ALPHATEST
	uniform float alphaTest;
#endif`,lf=`#ifdef USE_AOMAP
	float ambientOcclusion = ( texture2D( aoMap, vAoMapUv ).r - 1.0 ) * aoMapIntensity + 1.0;
	reflectedLight.indirectDiffuse *= ambientOcclusion;
	#if defined( USE_CLEARCOAT ) 
		clearcoatSpecularIndirect *= ambientOcclusion;
	#endif
	#if defined( USE_SHEEN ) 
		sheenSpecularIndirect *= ambientOcclusion;
	#endif
	#if defined( USE_ENVMAP ) && defined( STANDARD )
		float dotNV = saturate( dot( geometryNormal, geometryViewDir ) );
		reflectedLight.indirectSpecular *= computeSpecularOcclusion( dotNV, ambientOcclusion, material.roughness );
	#endif
#endif`,uf=`#ifdef USE_AOMAP
	uniform sampler2D aoMap;
	uniform float aoMapIntensity;
#endif`,hf=`#ifdef USE_BATCHING
	#if ! defined( GL_ANGLE_multi_draw )
	#define gl_DrawID _gl_DrawID
	uniform int _gl_DrawID;
	#endif
	uniform highp sampler2D batchingTexture;
	uniform highp usampler2D batchingIdTexture;
	mat4 getBatchingMatrix( const in float i ) {
		int size = textureSize( batchingTexture, 0 ).x;
		int j = int( i ) * 4;
		int x = j % size;
		int y = j / size;
		vec4 v1 = texelFetch( batchingTexture, ivec2( x, y ), 0 );
		vec4 v2 = texelFetch( batchingTexture, ivec2( x + 1, y ), 0 );
		vec4 v3 = texelFetch( batchingTexture, ivec2( x + 2, y ), 0 );
		vec4 v4 = texelFetch( batchingTexture, ivec2( x + 3, y ), 0 );
		return mat4( v1, v2, v3, v4 );
	}
	float getIndirectIndex( const in int i ) {
		int size = textureSize( batchingIdTexture, 0 ).x;
		int x = i % size;
		int y = i / size;
		return float( texelFetch( batchingIdTexture, ivec2( x, y ), 0 ).r );
	}
#endif
#ifdef USE_BATCHING_COLOR
	uniform sampler2D batchingColorTexture;
	vec4 getBatchingColor( const in float i ) {
		int size = textureSize( batchingColorTexture, 0 ).x;
		int j = int( i );
		int x = j % size;
		int y = j / size;
		return texelFetch( batchingColorTexture, ivec2( x, y ), 0 );
	}
#endif`,ff=`#ifdef USE_BATCHING
	mat4 batchingMatrix = getBatchingMatrix( getIndirectIndex( gl_DrawID ) );
#endif`,df=`vec3 transformed = vec3( position );
#ifdef USE_ALPHAHASH
	vPosition = vec3( position );
#endif`,pf=`vec3 objectNormal = vec3( normal );
#ifdef USE_TANGENT
	vec3 objectTangent = vec3( tangent.xyz );
#endif`,mf=`float G_BlinnPhong_Implicit( ) {
	return 0.25;
}
float D_BlinnPhong( const in float shininess, const in float dotNH ) {
	return RECIPROCAL_PI * ( shininess * 0.5 + 1.0 ) * pow( dotNH, shininess );
}
vec3 BRDF_BlinnPhong( const in vec3 lightDir, const in vec3 viewDir, const in vec3 normal, const in vec3 specularColor, const in float shininess ) {
	vec3 halfDir = normalize( lightDir + viewDir );
	float dotNH = saturate( dot( normal, halfDir ) );
	float dotVH = saturate( dot( viewDir, halfDir ) );
	vec3 F = F_Schlick( specularColor, 1.0, dotVH );
	float G = G_BlinnPhong_Implicit( );
	float D = D_BlinnPhong( shininess, dotNH );
	return F * ( G * D );
} // validated`,gf=`#ifdef USE_IRIDESCENCE
	const mat3 XYZ_TO_REC709 = mat3(
		 3.2404542, -0.9692660,  0.0556434,
		-1.5371385,  1.8760108, -0.2040259,
		-0.4985314,  0.0415560,  1.0572252
	);
	vec3 Fresnel0ToIor( vec3 fresnel0 ) {
		vec3 sqrtF0 = sqrt( fresnel0 );
		return ( vec3( 1.0 ) + sqrtF0 ) / ( vec3( 1.0 ) - sqrtF0 );
	}
	vec3 IorToFresnel0( vec3 transmittedIor, float incidentIor ) {
		return pow2( ( transmittedIor - vec3( incidentIor ) ) / ( transmittedIor + vec3( incidentIor ) ) );
	}
	float IorToFresnel0( float transmittedIor, float incidentIor ) {
		return pow2( ( transmittedIor - incidentIor ) / ( transmittedIor + incidentIor ));
	}
	vec3 evalSensitivity( float OPD, vec3 shift ) {
		float phase = 2.0 * PI * OPD * 1.0e-9;
		vec3 val = vec3( 5.4856e-13, 4.4201e-13, 5.2481e-13 );
		vec3 pos = vec3( 1.6810e+06, 1.7953e+06, 2.2084e+06 );
		vec3 var = vec3( 4.3278e+09, 9.3046e+09, 6.6121e+09 );
		vec3 xyz = val * sqrt( 2.0 * PI * var ) * cos( pos * phase + shift ) * exp( - pow2( phase ) * var );
		xyz.x += 9.7470e-14 * sqrt( 2.0 * PI * 4.5282e+09 ) * cos( 2.2399e+06 * phase + shift[ 0 ] ) * exp( - 4.5282e+09 * pow2( phase ) );
		xyz /= 1.0685e-7;
		vec3 rgb = XYZ_TO_REC709 * xyz;
		return rgb;
	}
	vec3 evalIridescence( float outsideIOR, float eta2, float cosTheta1, float thinFilmThickness, vec3 baseF0 ) {
		vec3 I;
		float iridescenceIOR = mix( outsideIOR, eta2, smoothstep( 0.0, 0.03, thinFilmThickness ) );
		float sinTheta2Sq = pow2( outsideIOR / iridescenceIOR ) * ( 1.0 - pow2( cosTheta1 ) );
		float cosTheta2Sq = 1.0 - sinTheta2Sq;
		if ( cosTheta2Sq < 0.0 ) {
			return vec3( 1.0 );
		}
		float cosTheta2 = sqrt( cosTheta2Sq );
		float R0 = IorToFresnel0( iridescenceIOR, outsideIOR );
		float R12 = F_Schlick( R0, 1.0, cosTheta1 );
		float T121 = 1.0 - R12;
		float phi12 = 0.0;
		if ( iridescenceIOR < outsideIOR ) phi12 = PI;
		float phi21 = PI - phi12;
		vec3 baseIOR = Fresnel0ToIor( clamp( baseF0, 0.0, 0.9999 ) );		vec3 R1 = IorToFresnel0( baseIOR, iridescenceIOR );
		vec3 R23 = F_Schlick( R1, 1.0, cosTheta2 );
		vec3 phi23 = vec3( 0.0 );
		if ( baseIOR[ 0 ] < iridescenceIOR ) phi23[ 0 ] = PI;
		if ( baseIOR[ 1 ] < iridescenceIOR ) phi23[ 1 ] = PI;
		if ( baseIOR[ 2 ] < iridescenceIOR ) phi23[ 2 ] = PI;
		float OPD = 2.0 * iridescenceIOR * thinFilmThickness * cosTheta2;
		vec3 phi = vec3( phi21 ) + phi23;
		vec3 R123 = clamp( R12 * R23, 1e-5, 0.9999 );
		vec3 r123 = sqrt( R123 );
		vec3 Rs = pow2( T121 ) * R23 / ( vec3( 1.0 ) - R123 );
		vec3 C0 = R12 + Rs;
		I = C0;
		vec3 Cm = Rs - T121;
		for ( int m = 1; m <= 2; ++ m ) {
			Cm *= r123;
			vec3 Sm = 2.0 * evalSensitivity( float( m ) * OPD, float( m ) * phi );
			I += Cm * Sm;
		}
		return max( I, vec3( 0.0 ) );
	}
#endif`,xf=`#ifdef USE_BUMPMAP
	uniform sampler2D bumpMap;
	uniform float bumpScale;
	vec2 dHdxy_fwd() {
		vec2 dSTdx = dFdx( vBumpMapUv );
		vec2 dSTdy = dFdy( vBumpMapUv );
		float Hll = bumpScale * texture2D( bumpMap, vBumpMapUv ).x;
		float dBx = bumpScale * texture2D( bumpMap, vBumpMapUv + dSTdx ).x - Hll;
		float dBy = bumpScale * texture2D( bumpMap, vBumpMapUv + dSTdy ).x - Hll;
		return vec2( dBx, dBy );
	}
	vec3 perturbNormalArb( vec3 surf_pos, vec3 surf_norm, vec2 dHdxy, float faceDirection ) {
		vec3 vSigmaX = normalize( dFdx( surf_pos.xyz ) );
		vec3 vSigmaY = normalize( dFdy( surf_pos.xyz ) );
		vec3 vN = surf_norm;
		vec3 R1 = cross( vSigmaY, vN );
		vec3 R2 = cross( vN, vSigmaX );
		float fDet = dot( vSigmaX, R1 ) * faceDirection;
		vec3 vGrad = sign( fDet ) * ( dHdxy.x * R1 + dHdxy.y * R2 );
		return normalize( abs( fDet ) * surf_norm - vGrad );
	}
#endif`,bf=`#if NUM_CLIPPING_PLANES > 0
	vec4 plane;
	#ifdef ALPHA_TO_COVERAGE
		float distanceToPlane, distanceGradient;
		float clipOpacity = 1.0;
		#pragma unroll_loop_start
		for ( int i = 0; i < UNION_CLIPPING_PLANES; i ++ ) {
			plane = clippingPlanes[ i ];
			distanceToPlane = - dot( vClipPosition, plane.xyz ) + plane.w;
			distanceGradient = fwidth( distanceToPlane ) / 2.0;
			clipOpacity *= smoothstep( - distanceGradient, distanceGradient, distanceToPlane );
			if ( clipOpacity == 0.0 ) discard;
		}
		#pragma unroll_loop_end
		#if UNION_CLIPPING_PLANES < NUM_CLIPPING_PLANES
			float unionClipOpacity = 1.0;
			#pragma unroll_loop_start
			for ( int i = UNION_CLIPPING_PLANES; i < NUM_CLIPPING_PLANES; i ++ ) {
				plane = clippingPlanes[ i ];
				distanceToPlane = - dot( vClipPosition, plane.xyz ) + plane.w;
				distanceGradient = fwidth( distanceToPlane ) / 2.0;
				unionClipOpacity *= 1.0 - smoothstep( - distanceGradient, distanceGradient, distanceToPlane );
			}
			#pragma unroll_loop_end
			clipOpacity *= 1.0 - unionClipOpacity;
		#endif
		diffuseColor.a *= clipOpacity;
		if ( diffuseColor.a == 0.0 ) discard;
	#else
		#pragma unroll_loop_start
		for ( int i = 0; i < UNION_CLIPPING_PLANES; i ++ ) {
			plane = clippingPlanes[ i ];
			if ( dot( vClipPosition, plane.xyz ) > plane.w ) discard;
		}
		#pragma unroll_loop_end
		#if UNION_CLIPPING_PLANES < NUM_CLIPPING_PLANES
			bool clipped = true;
			#pragma unroll_loop_start
			for ( int i = UNION_CLIPPING_PLANES; i < NUM_CLIPPING_PLANES; i ++ ) {
				plane = clippingPlanes[ i ];
				clipped = ( dot( vClipPosition, plane.xyz ) > plane.w ) && clipped;
			}
			#pragma unroll_loop_end
			if ( clipped ) discard;
		#endif
	#endif
#endif`,_f=`#if NUM_CLIPPING_PLANES > 0
	varying vec3 vClipPosition;
	uniform vec4 clippingPlanes[ NUM_CLIPPING_PLANES ];
#endif`,yf=`#if NUM_CLIPPING_PLANES > 0
	varying vec3 vClipPosition;
#endif`,vf=`#if NUM_CLIPPING_PLANES > 0
	vClipPosition = - mvPosition.xyz;
#endif`,Sf=`#if defined( USE_COLOR ) || defined( USE_COLOR_ALPHA )
	diffuseColor *= vColor;
#endif`,Mf=`#if defined( USE_COLOR ) || defined( USE_COLOR_ALPHA )
	varying vec4 vColor;
#endif`,Af=`#if defined( USE_COLOR ) || defined( USE_COLOR_ALPHA ) || defined( USE_INSTANCING_COLOR ) || defined( USE_BATCHING_COLOR )
	varying vec4 vColor;
#endif`,Tf=`#if defined( USE_COLOR ) || defined( USE_COLOR_ALPHA ) || defined( USE_INSTANCING_COLOR ) || defined( USE_BATCHING_COLOR )
	vColor = vec4( 1.0 );
#endif
#ifdef USE_COLOR_ALPHA
	vColor *= color;
#elif defined( USE_COLOR )
	vColor.rgb *= color;
#endif
#ifdef USE_INSTANCING_COLOR
	vColor.rgb *= instanceColor.rgb;
#endif
#ifdef USE_BATCHING_COLOR
	vColor *= getBatchingColor( getIndirectIndex( gl_DrawID ) );
#endif`,wf=`#define PI 3.141592653589793
#define PI2 6.283185307179586
#define PI_HALF 1.5707963267948966
#define RECIPROCAL_PI 0.3183098861837907
#define RECIPROCAL_PI2 0.15915494309189535
#define EPSILON 1e-6
#ifndef saturate
#define saturate( a ) clamp( a, 0.0, 1.0 )
#endif
#define whiteComplement( a ) ( 1.0 - saturate( a ) )
float pow2( const in float x ) { return x*x; }
vec3 pow2( const in vec3 x ) { return x*x; }
float pow3( const in float x ) { return x*x*x; }
float pow4( const in float x ) { float x2 = x*x; return x2*x2; }
float max3( const in vec3 v ) { return max( max( v.x, v.y ), v.z ); }
float average( const in vec3 v ) { return dot( v, vec3( 0.3333333 ) ); }
highp float rand( const in vec2 uv ) {
	const highp float a = 12.9898, b = 78.233, c = 43758.5453;
	highp float dt = dot( uv.xy, vec2( a,b ) ), sn = mod( dt, PI );
	return fract( sin( sn ) * c );
}
#ifdef HIGH_PRECISION
	float precisionSafeLength( vec3 v ) { return length( v ); }
#else
	float precisionSafeLength( vec3 v ) {
		float maxComponent = max3( abs( v ) );
		return length( v / maxComponent ) * maxComponent;
	}
#endif
struct IncidentLight {
	vec3 color;
	vec3 direction;
	bool visible;
};
struct ReflectedLight {
	vec3 directDiffuse;
	vec3 directSpecular;
	vec3 indirectDiffuse;
	vec3 indirectSpecular;
};
#ifdef USE_ALPHAHASH
	varying vec3 vPosition;
#endif
vec3 transformDirection( in vec3 dir, in mat4 matrix ) {
	return normalize( ( matrix * vec4( dir, 0.0 ) ).xyz );
}
#define inverseTransformDirection transformDirectionByInverseViewMatrix
vec3 transformNormalByInverseViewMatrix( in vec3 normal, in mat4 viewMatrix ) {
	return normalize( ( vec4( normal, 0.0 ) * viewMatrix ).xyz );
}
vec3 transformDirectionByInverseViewMatrix( in vec3 dir, in mat4 viewMatrix ) {
	return normalize( ( vec4( dir, 0.0 ) * viewMatrix ).xyz );
}
bool isPerspectiveMatrix( mat4 m ) {
	return m[ 2 ][ 3 ] == - 1.0;
}
vec2 equirectUv( in vec3 dir ) {
	float u = atan( dir.z, dir.x ) * RECIPROCAL_PI2 + 0.5;
	float v = asin( clamp( dir.y, - 1.0, 1.0 ) ) * RECIPROCAL_PI + 0.5;
	return vec2( u, v );
}
vec3 BRDF_Lambert( const in vec3 diffuseColor ) {
	return RECIPROCAL_PI * diffuseColor;
}
vec3 F_Schlick( const in vec3 f0, const in float f90, const in float dotVH ) {
	float fresnel = exp2( ( - 5.55473 * dotVH - 6.98316 ) * dotVH );
	return f0 * ( 1.0 - fresnel ) + ( f90 * fresnel );
}
float F_Schlick( const in float f0, const in float f90, const in float dotVH ) {
	float fresnel = exp2( ( - 5.55473 * dotVH - 6.98316 ) * dotVH );
	return f0 * ( 1.0 - fresnel ) + ( f90 * fresnel );
} // validated`,Ef=`#ifdef ENVMAP_TYPE_CUBE_UV
	#define cubeUV_minMipLevel 4.0
	#define cubeUV_minTileSize 16.0
	float getFace( vec3 direction ) {
		vec3 absDirection = abs( direction );
		float face = - 1.0;
		if ( absDirection.x > absDirection.z ) {
			if ( absDirection.x > absDirection.y )
				face = direction.x > 0.0 ? 0.0 : 3.0;
			else
				face = direction.y > 0.0 ? 1.0 : 4.0;
		} else {
			if ( absDirection.z > absDirection.y )
				face = direction.z > 0.0 ? 2.0 : 5.0;
			else
				face = direction.y > 0.0 ? 1.0 : 4.0;
		}
		return face;
	}
	vec2 getUV( vec3 direction, float face ) {
		vec2 uv;
		if ( face == 0.0 ) {
			uv = vec2( direction.z, direction.y ) / abs( direction.x );
		} else if ( face == 1.0 ) {
			uv = vec2( - direction.x, - direction.z ) / abs( direction.y );
		} else if ( face == 2.0 ) {
			uv = vec2( - direction.x, direction.y ) / abs( direction.z );
		} else if ( face == 3.0 ) {
			uv = vec2( - direction.z, direction.y ) / abs( direction.x );
		} else if ( face == 4.0 ) {
			uv = vec2( - direction.x, direction.z ) / abs( direction.y );
		} else {
			uv = vec2( direction.x, direction.y ) / abs( direction.z );
		}
		return 0.5 * ( uv + 1.0 );
	}
	vec3 bilinearCubeUV( sampler2D envMap, vec3 direction, float mipInt ) {
		float face = getFace( direction );
		float filterInt = max( cubeUV_minMipLevel - mipInt, 0.0 );
		mipInt = max( mipInt, cubeUV_minMipLevel );
		float faceSize = exp2( mipInt );
		highp vec2 uv = getUV( direction, face ) * ( faceSize - 2.0 ) + 1.0;
		if ( face > 2.0 ) {
			uv.y += faceSize;
			face -= 3.0;
		}
		uv.x += face * faceSize;
		uv.x += filterInt * 3.0 * cubeUV_minTileSize;
		uv.y += 4.0 * ( exp2( CUBEUV_MAX_MIP ) - faceSize );
		uv.x *= CUBEUV_TEXEL_WIDTH;
		uv.y *= CUBEUV_TEXEL_HEIGHT;
		#ifdef texture2DGradEXT
			return texture2DGradEXT( envMap, uv, vec2( 0.0 ), vec2( 0.0 ) ).rgb;
		#else
			return texture2D( envMap, uv ).rgb;
		#endif
	}
	#define cubeUV_r0 1.0
	#define cubeUV_m0 - 2.0
	#define cubeUV_r1 0.8
	#define cubeUV_m1 - 1.0
	#define cubeUV_r4 0.4
	#define cubeUV_m4 2.0
	#define cubeUV_r5 0.305
	#define cubeUV_m5 3.0
	#define cubeUV_r6 0.21
	#define cubeUV_m6 4.0
	float roughnessToMip( float roughness ) {
		float mip = 0.0;
		if ( roughness >= cubeUV_r1 ) {
			mip = ( cubeUV_r0 - roughness ) * ( cubeUV_m1 - cubeUV_m0 ) / ( cubeUV_r0 - cubeUV_r1 ) + cubeUV_m0;
		} else if ( roughness >= cubeUV_r4 ) {
			mip = ( cubeUV_r1 - roughness ) * ( cubeUV_m4 - cubeUV_m1 ) / ( cubeUV_r1 - cubeUV_r4 ) + cubeUV_m1;
		} else if ( roughness >= cubeUV_r5 ) {
			mip = ( cubeUV_r4 - roughness ) * ( cubeUV_m5 - cubeUV_m4 ) / ( cubeUV_r4 - cubeUV_r5 ) + cubeUV_m4;
		} else if ( roughness >= cubeUV_r6 ) {
			mip = ( cubeUV_r5 - roughness ) * ( cubeUV_m6 - cubeUV_m5 ) / ( cubeUV_r5 - cubeUV_r6 ) + cubeUV_m5;
		} else {
			mip = - 2.0 * log2( 1.16 * roughness );		}
		return mip;
	}
	vec4 textureCubeUV( sampler2D envMap, vec3 sampleDir, float roughness ) {
		float mip = clamp( roughnessToMip( roughness ), cubeUV_m0, CUBEUV_MAX_MIP );
		float mipF = fract( mip );
		float mipInt = floor( mip );
		vec3 color0 = bilinearCubeUV( envMap, sampleDir, mipInt );
		if ( mipF == 0.0 ) {
			return vec4( color0, 1.0 );
		} else {
			vec3 color1 = bilinearCubeUV( envMap, sampleDir, mipInt + 1.0 );
			return vec4( mix( color0, color1, mipF ), 1.0 );
		}
	}
#endif`,Rf=`vec3 transformedNormal = objectNormal;
#ifdef USE_TANGENT
	vec3 transformedTangent = objectTangent;
#endif
#ifdef USE_BATCHING
	mat3 bm = mat3( batchingMatrix );
	transformedNormal /= vec3( dot( bm[ 0 ], bm[ 0 ] ), dot( bm[ 1 ], bm[ 1 ] ), dot( bm[ 2 ], bm[ 2 ] ) );
	transformedNormal = bm * transformedNormal;
	#ifdef USE_TANGENT
		transformedTangent = bm * transformedTangent;
	#endif
#endif
#ifdef USE_INSTANCING
	mat3 im = mat3( instanceMatrix );
	transformedNormal /= vec3( dot( im[ 0 ], im[ 0 ] ), dot( im[ 1 ], im[ 1 ] ), dot( im[ 2 ], im[ 2 ] ) );
	transformedNormal = im * transformedNormal;
	#ifdef USE_TANGENT
		transformedTangent = im * transformedTangent;
	#endif
#endif
transformedNormal = normalMatrix * transformedNormal;
#ifdef FLIP_SIDED
	transformedNormal = - transformedNormal;
#endif
#ifdef USE_TANGENT
	transformedTangent = ( modelViewMatrix * vec4( transformedTangent, 0.0 ) ).xyz;
#endif`,Cf=`#ifdef USE_DISPLACEMENTMAP
	uniform sampler2D displacementMap;
	uniform float displacementScale;
	uniform float displacementBias;
#endif`,If=`#ifdef USE_DISPLACEMENTMAP
	transformed += normalize( objectNormal ) * ( texture2D( displacementMap, vDisplacementMapUv ).x * displacementScale + displacementBias );
#endif`,Pf=`#ifdef USE_EMISSIVEMAP
	vec4 emissiveColor = texture2D( emissiveMap, vEmissiveMapUv );
	#ifdef DECODE_VIDEO_TEXTURE_EMISSIVE
		emissiveColor = sRGBTransferEOTF( emissiveColor );
	#endif
	totalEmissiveRadiance *= emissiveColor.rgb;
#endif`,Lf=`#ifdef USE_EMISSIVEMAP
	uniform sampler2D emissiveMap;
#endif`,Df="gl_FragColor = linearToOutputTexel( gl_FragColor );",Nf=`vec4 LinearTransferOETF( in vec4 value ) {
	return value;
}
vec4 sRGBTransferEOTF( in vec4 value ) {
	return vec4( mix( pow( value.rgb * 0.9478672986 + vec3( 0.0521327014 ), vec3( 2.4 ) ), value.rgb * 0.0773993808, vec3( lessThanEqual( value.rgb, vec3( 0.04045 ) ) ) ), value.a );
}
vec4 sRGBTransferOETF( in vec4 value ) {
	return vec4( mix( pow( value.rgb, vec3( 0.41666 ) ) * 1.055 - vec3( 0.055 ), value.rgb * 12.92, vec3( lessThanEqual( value.rgb, vec3( 0.0031308 ) ) ) ), value.a );
}`,Ff=`#ifdef USE_ENVMAP
	#ifdef ENV_WORLDPOS
		vec3 cameraToFrag;
		if ( isOrthographic ) {
			cameraToFrag = normalize( vec3( - viewMatrix[ 0 ][ 2 ], - viewMatrix[ 1 ][ 2 ], - viewMatrix[ 2 ][ 2 ] ) );
		} else {
			cameraToFrag = normalize( vWorldPosition - cameraPosition );
		}
		vec3 worldNormal = transformNormalByInverseViewMatrix( normal, viewMatrix );
		#ifdef ENVMAP_MODE_REFLECTION
			vec3 reflectVec = reflect( cameraToFrag, worldNormal );
		#else
			vec3 reflectVec = refract( cameraToFrag, worldNormal, refractionRatio );
		#endif
	#else
		vec3 reflectVec = vReflect;
	#endif
	#ifdef ENVMAP_TYPE_CUBE
		vec4 envColor = textureCube( envMap, envMapRotation * reflectVec );
		#ifdef ENVMAP_BLENDING_MULTIPLY
			outgoingLight = mix( outgoingLight, outgoingLight * envColor.xyz, specularStrength * reflectivity );
		#elif defined( ENVMAP_BLENDING_MIX )
			outgoingLight = mix( outgoingLight, envColor.xyz, specularStrength * reflectivity );
		#elif defined( ENVMAP_BLENDING_ADD )
			outgoingLight += envColor.xyz * specularStrength * reflectivity;
		#endif
	#endif
#endif`,Uf=`#ifdef USE_ENVMAP
	uniform float envMapIntensity;
	uniform mat3 envMapRotation;
	#ifdef ENVMAP_TYPE_CUBE
		uniform samplerCube envMap;
	#else
		uniform sampler2D envMap;
	#endif
#endif`,Of=`#ifdef USE_ENVMAP
	uniform float reflectivity;
	#if defined( USE_BUMPMAP ) || defined( USE_NORMALMAP ) || defined( PHONG ) || defined( LAMBERT )
		#define ENV_WORLDPOS
	#endif
	#ifdef ENV_WORLDPOS
		varying vec3 vWorldPosition;
		uniform float refractionRatio;
	#else
		varying vec3 vReflect;
	#endif
#endif`,Bf=`#ifdef USE_ENVMAP
	#if defined( USE_BUMPMAP ) || defined( USE_NORMALMAP ) || defined( PHONG ) || defined( LAMBERT )
		#define ENV_WORLDPOS
	#endif
	#ifdef ENV_WORLDPOS
		
		varying vec3 vWorldPosition;
	#else
		varying vec3 vReflect;
		uniform float refractionRatio;
	#endif
#endif`,kf=`#ifdef USE_ENVMAP
	#ifdef ENV_WORLDPOS
		vWorldPosition = worldPosition.xyz;
	#else
		vec3 cameraToVertex;
		if ( isOrthographic ) {
			cameraToVertex = normalize( vec3( - viewMatrix[ 0 ][ 2 ], - viewMatrix[ 1 ][ 2 ], - viewMatrix[ 2 ][ 2 ] ) );
		} else {
			cameraToVertex = normalize( worldPosition.xyz - cameraPosition );
		}
		vec3 worldNormal = transformNormalByInverseViewMatrix( transformedNormal, viewMatrix );
		#ifdef ENVMAP_MODE_REFLECTION
			vReflect = reflect( cameraToVertex, worldNormal );
		#else
			vReflect = refract( cameraToVertex, worldNormal, refractionRatio );
		#endif
	#endif
#endif`,zf=`#ifdef USE_FOG
	vFogDepth = - mvPosition.z;
#endif`,Vf=`#ifdef USE_FOG
	varying float vFogDepth;
#endif`,Gf=`#ifdef USE_FOG
	#ifdef FOG_EXP2
		float fogFactor = 1.0 - exp( - fogDensity * fogDensity * vFogDepth * vFogDepth );
	#else
		float fogFactor = smoothstep( fogNear, fogFar, vFogDepth );
	#endif
	gl_FragColor.rgb = mix( gl_FragColor.rgb, fogColor, fogFactor );
#endif`,Hf=`#ifdef USE_FOG
	uniform vec3 fogColor;
	varying float vFogDepth;
	#ifdef FOG_EXP2
		uniform float fogDensity;
	#else
		uniform float fogNear;
		uniform float fogFar;
	#endif
#endif`,Wf=`#ifdef USE_GRADIENTMAP
	uniform sampler2D gradientMap;
#endif
vec3 getGradientIrradiance( vec3 normal, vec3 lightDirection ) {
	float dotNL = dot( normal, lightDirection );
	vec2 coord = vec2( dotNL * 0.5 + 0.5, 0.0 );
	#ifdef USE_GRADIENTMAP
		return vec3( texture2D( gradientMap, coord ).r );
	#else
		vec2 fw = fwidth( coord ) * 0.5;
		return mix( vec3( 0.7 ), vec3( 1.0 ), smoothstep( 0.7 - fw.x, 0.7 + fw.x, coord.x ) );
	#endif
}`,Xf=`#ifdef USE_LIGHTMAP
	uniform sampler2D lightMap;
	uniform float lightMapIntensity;
#endif`,qf=`LambertMaterial material;
material.diffuseColor = diffuseColor.rgb;
material.specularStrength = specularStrength;`,Kf=`varying vec3 vViewPosition;
struct LambertMaterial {
	vec3 diffuseColor;
	float specularStrength;
};
void RE_Direct_Lambert( const in IncidentLight directLight, const in vec3 geometryPosition, const in vec3 geometryNormal, const in vec3 geometryViewDir, const in vec3 geometryClearcoatNormal, const in LambertMaterial material, inout ReflectedLight reflectedLight ) {
	float dotNL = saturate( dot( geometryNormal, directLight.direction ) );
	vec3 irradiance = dotNL * directLight.color;
	reflectedLight.directDiffuse += irradiance * BRDF_Lambert( material.diffuseColor );
}
void RE_IndirectDiffuse_Lambert( const in vec3 irradiance, const in vec3 geometryPosition, const in vec3 geometryNormal, const in vec3 geometryViewDir, const in vec3 geometryClearcoatNormal, const in LambertMaterial material, inout ReflectedLight reflectedLight ) {
	reflectedLight.indirectDiffuse += irradiance * BRDF_Lambert( material.diffuseColor );
}
#define RE_Direct				RE_Direct_Lambert
#define RE_IndirectDiffuse		RE_IndirectDiffuse_Lambert`,Yf=`uniform bool receiveShadow;
uniform vec3 ambientLightColor;
#if defined( USE_LIGHT_PROBES )
	uniform vec3 lightProbe[ 9 ];
#endif
vec3 shGetIrradianceAt( in vec3 normal, in vec3 shCoefficients[ 9 ] ) {
	float x = normal.x, y = normal.y, z = normal.z;
	vec3 result = shCoefficients[ 0 ] * 0.886227;
	result += shCoefficients[ 1 ] * 2.0 * 0.511664 * y;
	result += shCoefficients[ 2 ] * 2.0 * 0.511664 * z;
	result += shCoefficients[ 3 ] * 2.0 * 0.511664 * x;
	result += shCoefficients[ 4 ] * 2.0 * 0.429043 * x * y;
	result += shCoefficients[ 5 ] * 2.0 * 0.429043 * y * z;
	result += shCoefficients[ 6 ] * ( 0.743125 * z * z - 0.247708 );
	result += shCoefficients[ 7 ] * 2.0 * 0.429043 * x * z;
	result += shCoefficients[ 8 ] * 0.429043 * ( x * x - y * y );
	return result;
}
vec3 getLightProbeIrradiance( const in vec3 lightProbe[ 9 ], const in vec3 normal ) {
	vec3 worldNormal = transformNormalByInverseViewMatrix( normal, viewMatrix );
	vec3 irradiance = shGetIrradianceAt( worldNormal, lightProbe );
	return irradiance;
}
vec3 getAmbientLightIrradiance( const in vec3 ambientLightColor ) {
	vec3 irradiance = ambientLightColor;
	return irradiance;
}
float getDistanceAttenuation( const in float lightDistance, const in float cutoffDistance, const in float decayExponent ) {
	float distanceFalloff = 1.0 / max( pow( lightDistance, decayExponent ), 0.01 );
	if ( cutoffDistance > 0.0 ) {
		distanceFalloff *= pow2( saturate( 1.0 - pow4( lightDistance / cutoffDistance ) ) );
	}
	return distanceFalloff;
}
float getSpotAttenuation( const in float coneCosine, const in float penumbraCosine, const in float angleCosine ) {
	return smoothstep( coneCosine, penumbraCosine, angleCosine );
}
#if NUM_SUN_LIGHTS > 0
	struct SunLight {
		vec3 direction;
		vec3 color;
	};
	uniform SunLight sunLights[ NUM_SUN_LIGHTS ];
	void getSunLightInfo( const in SunLight sunLight, out IncidentLight light ) {
		light.color = sunLight.color;
		light.direction = sunLight.direction;
		light.visible = true;
	}
#endif
#if NUM_DIR_LIGHTS > 0
	struct DirectionalLight {
		vec3 direction;
		vec3 color;
	};
	uniform DirectionalLight directionalLights[ NUM_DIR_LIGHTS ];
	void getDirectionalLightInfo( const in DirectionalLight directionalLight, out IncidentLight light ) {
		light.color = directionalLight.color;
		light.direction = directionalLight.direction;
		light.visible = true;
	}
#endif
#if NUM_POINT_LIGHTS > 0
	struct PointLight {
		vec3 position;
		vec3 color;
		float distance;
		float decay;
	};
	uniform PointLight pointLights[ NUM_POINT_LIGHTS ];
	void getPointLightInfo( const in PointLight pointLight, const in vec3 geometryPosition, out IncidentLight light ) {
		vec3 lVector = pointLight.position - geometryPosition;
		light.direction = normalize( lVector );
		float lightDistance = length( lVector );
		light.color = pointLight.color;
		light.color *= getDistanceAttenuation( lightDistance, pointLight.distance, pointLight.decay );
		light.visible = ( light.color != vec3( 0.0 ) );
	}
#endif
#if NUM_SPOT_LIGHTS > 0
	struct SpotLight {
		vec3 position;
		vec3 direction;
		vec3 color;
		float distance;
		float decay;
		float coneCos;
		float penumbraCos;
	};
	uniform SpotLight spotLights[ NUM_SPOT_LIGHTS ];
	void getSpotLightInfo( const in SpotLight spotLight, const in vec3 geometryPosition, out IncidentLight light ) {
		vec3 lVector = spotLight.position - geometryPosition;
		light.direction = normalize( lVector );
		float angleCos = dot( light.direction, spotLight.direction );
		float spotAttenuation = getSpotAttenuation( spotLight.coneCos, spotLight.penumbraCos, angleCos );
		if ( spotAttenuation > 0.0 ) {
			float lightDistance = length( lVector );
			light.color = spotLight.color * spotAttenuation;
			light.color *= getDistanceAttenuation( lightDistance, spotLight.distance, spotLight.decay );
			light.visible = ( light.color != vec3( 0.0 ) );
		} else {
			light.color = vec3( 0.0 );
			light.visible = false;
		}
	}
#endif
#if NUM_RECT_AREA_LIGHTS > 0
	struct RectAreaLight {
		vec3 color;
		vec3 position;
		vec3 halfWidth;
		vec3 halfHeight;
	};
	uniform sampler2D ltc_1;	uniform sampler2D ltc_2;
	uniform RectAreaLight rectAreaLights[ NUM_RECT_AREA_LIGHTS ];
#endif
#if NUM_HEMI_LIGHTS > 0
	struct HemisphereLight {
		vec3 direction;
		vec3 skyColor;
		vec3 groundColor;
	};
	uniform HemisphereLight hemisphereLights[ NUM_HEMI_LIGHTS ];
	vec3 getHemisphereLightIrradiance( const in HemisphereLight hemiLight, const in vec3 normal ) {
		float dotNL = dot( normal, hemiLight.direction );
		float hemiDiffuseWeight = 0.5 * dotNL + 0.5;
		vec3 irradiance = mix( hemiLight.groundColor, hemiLight.skyColor, hemiDiffuseWeight );
		return irradiance;
	}
#endif
#include <lightprobes_pars_fragment>`,jf=`#ifdef USE_ENVMAP
	vec3 getIBLIrradiance( const in vec3 normal ) {
		#ifdef ENVMAP_TYPE_CUBE_UV
			vec3 worldNormal = transformNormalByInverseViewMatrix( normal, viewMatrix );
			vec4 envMapColor = textureCubeUV( envMap, envMapRotation * worldNormal, 1.0 );
			return PI * envMapColor.rgb * envMapIntensity;
		#else
			return vec3( 0.0 );
		#endif
	}
	vec3 getIBLRadiance( const in vec3 viewDir, const in vec3 normal, const in float roughness ) {
		#ifdef ENVMAP_TYPE_CUBE_UV
			vec3 reflectVec = reflect( - viewDir, normal );
			reflectVec = normalize( mix( reflectVec, normal, pow4( roughness ) ) );
			reflectVec = transformDirectionByInverseViewMatrix( reflectVec, viewMatrix );
			vec4 envMapColor = textureCubeUV( envMap, envMapRotation * reflectVec, roughness );
			return envMapColor.rgb * envMapIntensity;
		#else
			return vec3( 0.0 );
		#endif
	}
	#ifdef USE_RETROREFLECTION
		vec3 getIBLRetroRadiance( const in vec3 viewDir, const in vec3 normal, const in float roughness ) {
			#ifdef ENVMAP_TYPE_CUBE_UV
				vec3 retroVec = normalize( mix( viewDir, normal, pow4( roughness ) ) );
				retroVec = transformDirectionByInverseViewMatrix( retroVec, viewMatrix );
				vec4 envMapColor = textureCubeUV( envMap, envMapRotation * retroVec, roughness );
				return envMapColor.rgb * envMapIntensity;
			#else
				return vec3( 0.0 );
			#endif
		}
	#endif
	#ifdef USE_ANISOTROPY
		vec3 getIBLAnisotropyRadiance( const in vec3 viewDir, const in vec3 normal, const in float roughness, const in vec3 bitangent, const in float anisotropy ) {
			#ifdef ENVMAP_TYPE_CUBE_UV
				vec3 bentNormal = cross( bitangent, viewDir );
				bentNormal = normalize( cross( bentNormal, bitangent ) );
				bentNormal = normalize( mix( bentNormal, normal, pow2( pow2( 1.0 - anisotropy * ( 1.0 - roughness ) ) ) ) );
				return getIBLRadiance( viewDir, bentNormal, roughness );
			#else
				return vec3( 0.0 );
			#endif
		}
		#ifdef USE_RETROREFLECTION
			vec3 getIBLAnisotropyRetroRadiance( const in vec3 viewDir, const in vec3 normal, const in float roughness, const in vec3 bitangent, const in float anisotropy ) {
				#ifdef ENVMAP_TYPE_CUBE_UV
					vec3 bentNormal = cross( bitangent, viewDir );
					bentNormal = normalize( cross( bentNormal, bitangent ) );
					bentNormal = normalize( mix( bentNormal, normal, pow2( pow2( 1.0 - anisotropy * ( 1.0 - roughness ) ) ) ) );
					return getIBLRetroRadiance( viewDir, bentNormal, roughness );
				#else
					return vec3( 0.0 );
				#endif
			}
		#endif
	#endif
#endif`,Jf=`ToonMaterial material;
material.diffuseColor = diffuseColor.rgb;`,Zf=`varying vec3 vViewPosition;
struct ToonMaterial {
	vec3 diffuseColor;
};
void RE_Direct_Toon( const in IncidentLight directLight, const in vec3 geometryPosition, const in vec3 geometryNormal, const in vec3 geometryViewDir, const in vec3 geometryClearcoatNormal, const in ToonMaterial material, inout ReflectedLight reflectedLight ) {
	vec3 irradiance = getGradientIrradiance( geometryNormal, directLight.direction ) * directLight.color;
	reflectedLight.directDiffuse += irradiance * BRDF_Lambert( material.diffuseColor );
}
void RE_IndirectDiffuse_Toon( const in vec3 irradiance, const in vec3 geometryPosition, const in vec3 geometryNormal, const in vec3 geometryViewDir, const in vec3 geometryClearcoatNormal, const in ToonMaterial material, inout ReflectedLight reflectedLight ) {
	reflectedLight.indirectDiffuse += irradiance * BRDF_Lambert( material.diffuseColor );
}
#define RE_Direct				RE_Direct_Toon
#define RE_IndirectDiffuse		RE_IndirectDiffuse_Toon`,$f=`BlinnPhongMaterial material;
material.diffuseColor = diffuseColor.rgb;
material.specularColor = specular;
material.specularShininess = shininess;
material.specularStrength = specularStrength;`,Qf=`varying vec3 vViewPosition;
struct BlinnPhongMaterial {
	vec3 diffuseColor;
	vec3 specularColor;
	float specularShininess;
	float specularStrength;
};
void RE_Direct_BlinnPhong( const in IncidentLight directLight, const in vec3 geometryPosition, const in vec3 geometryNormal, const in vec3 geometryViewDir, const in vec3 geometryClearcoatNormal, const in BlinnPhongMaterial material, inout ReflectedLight reflectedLight ) {
	float dotNL = saturate( dot( geometryNormal, directLight.direction ) );
	vec3 irradiance = dotNL * directLight.color;
	reflectedLight.directDiffuse += irradiance * BRDF_Lambert( material.diffuseColor );
	reflectedLight.directSpecular += irradiance * BRDF_BlinnPhong( directLight.direction, geometryViewDir, geometryNormal, material.specularColor, material.specularShininess ) * material.specularStrength;
}
void RE_IndirectDiffuse_BlinnPhong( const in vec3 irradiance, const in vec3 geometryPosition, const in vec3 geometryNormal, const in vec3 geometryViewDir, const in vec3 geometryClearcoatNormal, const in BlinnPhongMaterial material, inout ReflectedLight reflectedLight ) {
	reflectedLight.indirectDiffuse += irradiance * BRDF_Lambert( material.diffuseColor );
}
#define RE_Direct				RE_Direct_BlinnPhong
#define RE_IndirectDiffuse		RE_IndirectDiffuse_BlinnPhong`,ed=`PhysicalMaterial material;
material.diffuseColor = diffuseColor.rgb;
material.diffuseContribution = diffuseColor.rgb * ( 1.0 - metalnessFactor );
material.metalness = metalnessFactor;
vec3 dxy = max( abs( dFdx( nonPerturbedNormal ) ), abs( dFdy( nonPerturbedNormal ) ) );
float geometryRoughness = max( max( dxy.x, dxy.y ), dxy.z );
material.roughness = max( roughnessFactor, 0.0525 );material.roughness += geometryRoughness;
material.roughness = min( material.roughness, 1.0 );
#ifdef IOR
	material.ior = ior;
	#ifdef USE_SPECULAR
		float specularIntensityFactor = specularIntensity;
		vec3 specularColorFactor = specularColor;
		#ifdef USE_SPECULAR_COLORMAP
			specularColorFactor *= texture2D( specularColorMap, vSpecularColorMapUv ).rgb;
		#endif
		#ifdef USE_SPECULAR_INTENSITYMAP
			specularIntensityFactor *= texture2D( specularIntensityMap, vSpecularIntensityMapUv ).a;
		#endif
		material.specularF90 = mix( specularIntensityFactor, 1.0, metalnessFactor );
	#else
		float specularIntensityFactor = 1.0;
		vec3 specularColorFactor = vec3( 1.0 );
		material.specularF90 = 1.0;
	#endif
	material.specularColor = min( pow2( ( material.ior - 1.0 ) / ( material.ior + 1.0 ) ) * specularColorFactor, vec3( 1.0 ) ) * specularIntensityFactor;
	material.specularColorBlended = mix( material.specularColor, diffuseColor.rgb, metalnessFactor );
#else
	material.specularColor = vec3( 0.04 );
	material.specularColorBlended = mix( material.specularColor, diffuseColor.rgb, metalnessFactor );
	material.specularF90 = 1.0;
#endif
#ifdef USE_CLEARCOAT
	material.clearcoat = clearcoat;
	material.clearcoatRoughness = clearcoatRoughness;
	material.clearcoatF0 = vec3( 0.04 );
	material.clearcoatF90 = 1.0;
	#ifdef USE_CLEARCOATMAP
		material.clearcoat *= texture2D( clearcoatMap, vClearcoatMapUv ).x;
	#endif
	#ifdef USE_CLEARCOAT_ROUGHNESSMAP
		material.clearcoatRoughness *= texture2D( clearcoatRoughnessMap, vClearcoatRoughnessMapUv ).y;
	#endif
	material.clearcoat = saturate( material.clearcoat );	material.clearcoatRoughness = max( material.clearcoatRoughness, 0.0525 );
	material.clearcoatRoughness += geometryRoughness;
	material.clearcoatRoughness = min( material.clearcoatRoughness, 1.0 );
#endif
#ifdef USE_DISPERSION
	material.dispersion = dispersion;
#endif
#ifdef USE_RETROREFLECTION
	material.retroreflectivity = retroreflectivity;
#endif
#ifdef USE_IRIDESCENCE
	material.iridescence = iridescence;
	material.iridescenceIOR = iridescenceIOR;
	#ifdef USE_IRIDESCENCEMAP
		material.iridescence *= texture2D( iridescenceMap, vIridescenceMapUv ).r;
	#endif
	#ifdef USE_IRIDESCENCE_THICKNESSMAP
		material.iridescenceThickness = (iridescenceThicknessMaximum - iridescenceThicknessMinimum) * texture2D( iridescenceThicknessMap, vIridescenceThicknessMapUv ).g + iridescenceThicknessMinimum;
	#else
		material.iridescenceThickness = iridescenceThicknessMaximum;
	#endif
#endif
#ifdef USE_SHEEN
	material.sheenColor = sheenColor;
	#ifdef USE_SHEEN_COLORMAP
		material.sheenColor *= texture2D( sheenColorMap, vSheenColorMapUv ).rgb;
	#endif
	material.sheenRoughness = clamp( sheenRoughness, 0.0001, 1.0 );
	#ifdef USE_SHEEN_ROUGHNESSMAP
		material.sheenRoughness *= texture2D( sheenRoughnessMap, vSheenRoughnessMapUv ).a;
	#endif
#endif
#ifdef USE_ANISOTROPY
	#ifdef USE_ANISOTROPYMAP
		mat2 anisotropyMat = mat2( anisotropyVector.x, anisotropyVector.y, - anisotropyVector.y, anisotropyVector.x );
		vec3 anisotropyPolar = texture2D( anisotropyMap, vAnisotropyMapUv ).rgb;
		vec2 anisotropyV = anisotropyMat * normalize( 2.0 * anisotropyPolar.rg - vec2( 1.0 ) ) * anisotropyPolar.b;
	#else
		vec2 anisotropyV = anisotropyVector;
	#endif
	material.anisotropy = length( anisotropyV );
	if( material.anisotropy == 0.0 ) {
		anisotropyV = vec2( 1.0, 0.0 );
	} else {
		anisotropyV /= material.anisotropy;
		material.anisotropy = saturate( material.anisotropy );
	}
	material.alphaT = mix( pow2( material.roughness ), 1.0, pow2( material.anisotropy ) );
	material.anisotropyT = tbn[ 0 ] * anisotropyV.x + tbn[ 1 ] * anisotropyV.y;
	material.anisotropyB = tbn[ 1 ] * anisotropyV.x - tbn[ 0 ] * anisotropyV.y;
#endif`,td=`uniform sampler2D dfgLUT;
struct PhysicalMaterial {
	vec3 diffuseColor;
	vec3 diffuseContribution;
	vec3 specularColor;
	vec3 specularColorBlended;
	float roughness;
	float metalness;
	float specularF90;
	float dispersion;
	vec2 dfg;
	vec3 multiScatteringCompensation;
	#ifdef USE_RETROREFLECTION
		float retroreflectivity;
	#endif
	#ifdef USE_CLEARCOAT
		float clearcoat;
		float clearcoatRoughness;
		vec3 clearcoatF0;
		float clearcoatF90;
	#endif
	#ifdef USE_IRIDESCENCE
		float iridescence;
		float iridescenceIOR;
		float iridescenceThickness;
		vec3 iridescenceFresnel;
		vec3 iridescenceF0Dielectric;
		vec3 iridescenceF0Metallic;
	#endif
	#ifdef USE_SHEEN
		vec3 sheenColor;
		float sheenRoughness;
	#endif
	#ifdef IOR
		float ior;
	#endif
	#ifdef USE_TRANSMISSION
		float transmission;
		float transmissionAlpha;
		float thickness;
		float attenuationDistance;
		vec3 attenuationColor;
	#endif
	#ifdef USE_ANISOTROPY
		float anisotropy;
		float alphaT;
		vec3 anisotropyT;
		vec3 anisotropyB;
	#endif
};
vec3 clearcoatSpecularDirect = vec3( 0.0 );
vec3 clearcoatSpecularIndirect = vec3( 0.0 );
vec3 sheenSpecularDirect = vec3( 0.0 );
vec3 sheenSpecularIndirect = vec3(0.0 );
vec3 Schlick_to_F0( const in vec3 f, const in float f90, const in float dotVH ) {
    float x = clamp( 1.0 - dotVH, 0.0, 1.0 );
    float x2 = x * x;
    float x5 = clamp( x * x2 * x2, 0.0, 0.9999 );
    return ( f - vec3( f90 ) * x5 ) / ( 1.0 - x5 );
}
float V_GGX_SmithCorrelated( const in float alpha, const in float dotNL, const in float dotNV ) {
	float a2 = pow2( alpha );
	float gv = dotNL * sqrt( a2 + ( 1.0 - a2 ) * pow2( dotNV ) );
	float gl = dotNV * sqrt( a2 + ( 1.0 - a2 ) * pow2( dotNL ) );
	return 0.5 / max( gv + gl, EPSILON );
}
float D_GGX( const in float alpha, const in float dotNH ) {
	float a2 = pow2( alpha );
	float denom = pow2( dotNH ) * ( a2 - 1.0 ) + 1.0;
	return RECIPROCAL_PI * a2 / pow2( denom );
}
#ifdef USE_ANISOTROPY
	float V_GGX_SmithCorrelated_Anisotropic( const in float alphaT, const in float alphaB, const in float dotTV, const in float dotBV, const in float dotTL, const in float dotBL, const in float dotNV, const in float dotNL ) {
		float gv = dotNL * length( vec3( alphaT * dotTV, alphaB * dotBV, dotNV ) );
		float gl = dotNV * length( vec3( alphaT * dotTL, alphaB * dotBL, dotNL ) );
		return 0.5 / max( gv + gl, EPSILON );
	}
	float D_GGX_Anisotropic( const in float alphaT, const in float alphaB, const in float dotNH, const in float dotTH, const in float dotBH ) {
		float a2 = alphaT * alphaB;
		highp vec3 v = vec3( alphaB * dotTH, alphaT * dotBH, a2 * dotNH );
		highp float v2 = dot( v, v );
		float w2 = a2 / v2;
		return RECIPROCAL_PI * a2 * pow2 ( w2 );
	}
#endif
#ifdef USE_CLEARCOAT
	vec3 BRDF_GGX_Clearcoat( const in vec3 lightDir, const in vec3 viewDir, const in vec3 normal, const in PhysicalMaterial material) {
		vec3 f0 = material.clearcoatF0;
		float f90 = material.clearcoatF90;
		float roughness = material.clearcoatRoughness;
		float alpha = pow2( roughness );
		vec3 halfDir = normalize( lightDir + viewDir );
		float dotNL = saturate( dot( normal, lightDir ) );
		float dotNV = saturate( dot( normal, viewDir ) );
		float dotNH = saturate( dot( normal, halfDir ) );
		float dotVH = saturate( dot( viewDir, halfDir ) );
		vec3 F = F_Schlick( f0, f90, dotVH );
		float V = V_GGX_SmithCorrelated( alpha, dotNL, dotNV );
		float D = D_GGX( alpha, dotNH );
		return F * ( V * D );
	}
#endif
vec3 BRDF_GGX( const in vec3 lightDir, const in vec3 viewDir, const in vec3 normal, const in PhysicalMaterial material ) {
	vec3 f0 = material.specularColorBlended;
	float f90 = material.specularF90;
	float roughness = material.roughness;
	float alpha = pow2( roughness );
	vec3 halfDir = normalize( lightDir + viewDir );
	float dotNL = saturate( dot( normal, lightDir ) );
	float dotNV = saturate( dot( normal, viewDir ) );
	float dotNH = saturate( dot( normal, halfDir ) );
	float dotVH = saturate( dot( viewDir, halfDir ) );
	vec3 F = F_Schlick( f0, f90, dotVH );
	#ifdef USE_IRIDESCENCE
		F = mix( F, material.iridescenceFresnel, material.iridescence );
	#endif
	#ifdef USE_ANISOTROPY
		float dotTL = dot( material.anisotropyT, lightDir );
		float dotTV = dot( material.anisotropyT, viewDir );
		float dotTH = dot( material.anisotropyT, halfDir );
		float dotBL = dot( material.anisotropyB, lightDir );
		float dotBV = dot( material.anisotropyB, viewDir );
		float dotBH = dot( material.anisotropyB, halfDir );
		float V = V_GGX_SmithCorrelated_Anisotropic( material.alphaT, alpha, dotTV, dotBV, dotTL, dotBL, dotNV, dotNL );
		float D = D_GGX_Anisotropic( material.alphaT, alpha, dotNH, dotTH, dotBH );
	#else
		float V = V_GGX_SmithCorrelated( alpha, dotNL, dotNV );
		float D = D_GGX( alpha, dotNH );
	#endif
	return F * ( V * D );
}
vec2 LTC_Uv( const in vec3 N, const in vec3 V, const in float roughness ) {
	const float LUT_SIZE = 64.0;
	const float LUT_SCALE = ( LUT_SIZE - 1.0 ) / LUT_SIZE;
	const float LUT_BIAS = 0.5 / LUT_SIZE;
	float dotNV = saturate( dot( N, V ) );
	vec2 uv = vec2( roughness, sqrt( 1.0 - dotNV ) );
	uv = uv * LUT_SCALE + LUT_BIAS;
	return uv;
}
float LTC_ClippedSphereFormFactor( const in vec3 f ) {
	float l = length( f );
	return max( ( l * l + f.z ) / ( l + 1.0 ), 0.0 );
}
vec3 LTC_EdgeVectorFormFactor( const in vec3 v1, const in vec3 v2 ) {
	float x = dot( v1, v2 );
	float y = abs( x );
	float a = 0.8543985 + ( 0.4965155 + 0.0145206 * y ) * y;
	float b = 3.4175940 + ( 4.1616724 + y ) * y;
	float v = a / b;
	float theta_sintheta = ( x > 0.0 ) ? v : 0.5 * inversesqrt( max( 1.0 - x * x, 1e-7 ) ) - v;
	return cross( v1, v2 ) * theta_sintheta;
}
vec3 LTC_Evaluate( const in vec3 N, const in vec3 V, const in vec3 P, const in mat3 mInv, const in vec3 rectCoords[ 4 ] ) {
	vec3 v1 = rectCoords[ 1 ] - rectCoords[ 0 ];
	vec3 v2 = rectCoords[ 3 ] - rectCoords[ 0 ];
	vec3 lightNormal = cross( v1, v2 );
	if( dot( lightNormal, P - rectCoords[ 0 ] ) < 0.0 ) return vec3( 0.0 );
	vec3 T1, T2;
	T1 = normalize( V - N * dot( V, N ) );
	T2 = - cross( N, T1 );
	mat3 mat = mInv * transpose( mat3( T1, T2, N ) );
	vec3 coords[ 4 ];
	coords[ 0 ] = mat * ( rectCoords[ 0 ] - P );
	coords[ 1 ] = mat * ( rectCoords[ 1 ] - P );
	coords[ 2 ] = mat * ( rectCoords[ 2 ] - P );
	coords[ 3 ] = mat * ( rectCoords[ 3 ] - P );
	coords[ 0 ] = normalize( coords[ 0 ] );
	coords[ 1 ] = normalize( coords[ 1 ] );
	coords[ 2 ] = normalize( coords[ 2 ] );
	coords[ 3 ] = normalize( coords[ 3 ] );
	vec3 vectorFormFactor = vec3( 0.0 );
	vectorFormFactor += LTC_EdgeVectorFormFactor( coords[ 0 ], coords[ 1 ] );
	vectorFormFactor += LTC_EdgeVectorFormFactor( coords[ 1 ], coords[ 2 ] );
	vectorFormFactor += LTC_EdgeVectorFormFactor( coords[ 2 ], coords[ 3 ] );
	vectorFormFactor += LTC_EdgeVectorFormFactor( coords[ 3 ], coords[ 0 ] );
	float result = LTC_ClippedSphereFormFactor( vectorFormFactor );
	return vec3( result );
}
#if defined( USE_SHEEN )
float D_Charlie( float roughness, float dotNH ) {
	float alpha = pow2( roughness );
	float invAlpha = 1.0 / alpha;
	float cos2h = dotNH * dotNH;
	float sin2h = max( 1.0 - cos2h, 0.0078125 );
	return ( 2.0 + invAlpha ) * pow( sin2h, invAlpha * 0.5 ) / ( 2.0 * PI );
}
float V_Neubelt( float dotNV, float dotNL ) {
	return saturate( 1.0 / ( 4.0 * ( dotNL + dotNV - dotNL * dotNV ) ) );
}
vec3 BRDF_Sheen( const in vec3 lightDir, const in vec3 viewDir, const in vec3 normal, vec3 sheenColor, const in float sheenRoughness ) {
	vec3 halfDir = normalize( lightDir + viewDir );
	float dotNL = saturate( dot( normal, lightDir ) );
	float dotNV = saturate( dot( normal, viewDir ) );
	float dotNH = saturate( dot( normal, halfDir ) );
	float D = D_Charlie( sheenRoughness, dotNH );
	float V = V_Neubelt( dotNV, dotNL );
	return sheenColor * ( D * V );
}
#endif
float IBLSheenBRDF( const in vec3 normal, const in vec3 viewDir, const in float roughness ) {
	float dotNV = saturate( dot( normal, viewDir ) );
	float r2 = roughness * roughness;
	float rInv = 1.0 / ( roughness + 0.1 );
	float a = -1.9362 + 1.0678 * roughness + 0.4573 * r2 - 0.8469 * rInv;
	float b = -0.6014 + 0.5538 * roughness - 0.4670 * r2 - 0.1255 * rInv;
	float DG = exp( a * dotNV + b );
	return saturate( DG );
}
vec3 EnvironmentBRDF( const in vec3 normal, const in vec3 viewDir, const in vec3 specularColor, const in float specularF90, const in float roughness ) {
	float dotNV = saturate( dot( normal, viewDir ) );
	vec2 fab = texture2D( dfgLUT, vec2( roughness, dotNV ) ).rg;
	return specularColor * fab.x + specularF90 * fab.y;
}
#ifdef USE_IRIDESCENCE
void computeMultiscatteringIridescence( const in vec2 fab, const in vec3 specularColor, const in float specularF90, const in float iridescence, const in vec3 iridescenceF0, inout vec3 singleScatter, inout vec3 multiScatter ) {
#else
void computeMultiscattering( const in vec2 fab, const in vec3 specularColor, const in float specularF90, inout vec3 singleScatter, inout vec3 multiScatter ) {
#endif
	#ifdef USE_IRIDESCENCE
		vec3 Fr = mix( specularColor, iridescenceF0, iridescence );
	#else
		vec3 Fr = specularColor;
	#endif
	vec3 FssEss = Fr * fab.x + specularF90 * fab.y;
	float Ess = fab.x + fab.y;
	float Ems = 1.0 - Ess;
	vec3 Favg = Fr + ( 1.0 - Fr ) * 0.047619;	vec3 Fms = FssEss * Favg / ( 1.0 - Ems * Favg );
	singleScatter += FssEss;
	multiScatter += Fms * Ems;
}
#if NUM_RECT_AREA_LIGHTS > 0
	void RE_Direct_RectArea_Physical( const in RectAreaLight rectAreaLight, const in vec3 geometryPosition, const in vec3 geometryNormal, const in vec3 geometryViewDir, const in vec3 geometryClearcoatNormal, const in PhysicalMaterial material, inout ReflectedLight reflectedLight ) {
		vec3 normal = geometryNormal;
		vec3 viewDir = geometryViewDir;
		vec3 position = geometryPosition;
		vec3 lightPos = rectAreaLight.position;
		vec3 halfWidth = rectAreaLight.halfWidth;
		vec3 halfHeight = rectAreaLight.halfHeight;
		vec3 lightColor = rectAreaLight.color;
		float roughness = material.roughness;
		vec3 rectCoords[ 4 ];
		rectCoords[ 0 ] = lightPos + halfWidth - halfHeight;		rectCoords[ 1 ] = lightPos - halfWidth - halfHeight;
		rectCoords[ 2 ] = lightPos - halfWidth + halfHeight;
		rectCoords[ 3 ] = lightPos + halfWidth + halfHeight;
		vec2 uv = LTC_Uv( normal, viewDir, roughness );
		vec4 t1 = texture2D( ltc_1, uv );
		vec4 t2 = texture2D( ltc_2, uv );
		mat3 mInv = mat3(
			vec3( t1.x, 0, t1.y ),
			vec3(    0, 1,    0 ),
			vec3( t1.z, 0, t1.w )
		);
		vec3 fresnel = ( material.specularColorBlended * t2.x + ( material.specularF90 - material.specularColorBlended ) * t2.y );
		reflectedLight.directSpecular += lightColor * fresnel * LTC_Evaluate( normal, viewDir, position, mInv, rectCoords );
		reflectedLight.directDiffuse += lightColor * material.diffuseContribution * LTC_Evaluate( normal, viewDir, position, mat3( 1.0 ), rectCoords );
		#ifdef USE_CLEARCOAT
			vec3 Ncc = geometryClearcoatNormal;
			vec2 uvClearcoat = LTC_Uv( Ncc, viewDir, material.clearcoatRoughness );
			vec4 t1Clearcoat = texture2D( ltc_1, uvClearcoat );
			vec4 t2Clearcoat = texture2D( ltc_2, uvClearcoat );
			mat3 mInvClearcoat = mat3(
				vec3( t1Clearcoat.x, 0, t1Clearcoat.y ),
				vec3(             0, 1,             0 ),
				vec3( t1Clearcoat.z, 0, t1Clearcoat.w )
			);
			vec3 fresnelClearcoat = material.clearcoatF0 * t2Clearcoat.x + ( material.clearcoatF90 - material.clearcoatF0 ) * t2Clearcoat.y;
			clearcoatSpecularDirect += lightColor * fresnelClearcoat * LTC_Evaluate( Ncc, viewDir, position, mInvClearcoat, rectCoords );
		#endif
	}
#endif
void RE_Direct_Physical( const in IncidentLight directLight, const in vec3 geometryPosition, const in vec3 geometryNormal, const in vec3 geometryViewDir, const in vec3 geometryClearcoatNormal, const in PhysicalMaterial material, inout ReflectedLight reflectedLight ) {
	float dotNL = saturate( dot( geometryNormal, directLight.direction ) );
	vec3 irradiance = dotNL * directLight.color;
	#ifdef USE_CLEARCOAT
		float dotNLcc = saturate( dot( geometryClearcoatNormal, directLight.direction ) );
		vec3 ccIrradiance = dotNLcc * directLight.color;
		clearcoatSpecularDirect += ccIrradiance * BRDF_GGX_Clearcoat( directLight.direction, geometryViewDir, geometryClearcoatNormal, material );
	#endif
	#ifdef USE_SHEEN
 
 		sheenSpecularDirect += irradiance * BRDF_Sheen( directLight.direction, geometryViewDir, geometryNormal, material.sheenColor, material.sheenRoughness );
 
 		float sheenAlbedoV = IBLSheenBRDF( geometryNormal, geometryViewDir, material.sheenRoughness );
 		float sheenAlbedoL = IBLSheenBRDF( geometryNormal, directLight.direction, material.sheenRoughness );
 
 		float sheenEnergyComp = 1.0 - max3( material.sheenColor ) * max( sheenAlbedoV, sheenAlbedoL );
 
 		irradiance *= sheenEnergyComp;
 
 	#endif
	vec3 specularBRDF = BRDF_GGX( directLight.direction, geometryViewDir, geometryNormal, material );
	#ifdef USE_RETROREFLECTION
		vec3 retroViewDir = reflect( - geometryViewDir, geometryNormal );
		vec3 retroSpecularBRDF = BRDF_GGX( directLight.direction, retroViewDir, geometryNormal, material );
		specularBRDF = mix( specularBRDF, retroSpecularBRDF, saturate( material.retroreflectivity ) );
	#endif
	reflectedLight.directSpecular += irradiance * specularBRDF * material.multiScatteringCompensation;
	vec3 halfDir = normalize( directLight.direction + geometryViewDir );
	float dotVH = saturate( dot( geometryViewDir, halfDir ) );
	vec3 F = F_Schlick( material.specularColor, material.specularF90, dotVH );
	#ifdef USE_RETROREFLECTION
		vec3 retroHalfDir = normalize( directLight.direction + retroViewDir );
		float dotRetroVH = saturate( dot( retroViewDir, retroHalfDir ) );
		vec3 retroF = F_Schlick( material.specularColor, material.specularF90, dotRetroVH );
		F = mix( F, retroF, saturate( material.retroreflectivity ) );
	#endif
	reflectedLight.directDiffuse += irradiance * BRDF_Lambert( material.diffuseContribution ) * ( 1.0 - F );
}
void RE_IndirectDiffuse_Physical( const in vec3 irradiance, const in vec3 geometryPosition, const in vec3 geometryNormal, const in vec3 geometryViewDir, const in vec3 geometryClearcoatNormal, const in PhysicalMaterial material, inout ReflectedLight reflectedLight ) {
	vec3 singleScattering = vec3( 0.0 );
	vec3 multiScattering = vec3( 0.0 );
	#ifdef USE_IRIDESCENCE
		computeMultiscatteringIridescence( material.dfg, material.specularColor, material.specularF90, material.iridescence, material.iridescenceF0Dielectric, singleScattering, multiScattering );
	#else
		computeMultiscattering( material.dfg, material.specularColor, material.specularF90, singleScattering, multiScattering );
	#endif
	vec3 diffuse = irradiance * BRDF_Lambert( material.diffuseContribution ) * ( 1.0 - singleScattering - multiScattering );
	#ifdef USE_SHEEN
		float sheenAlbedo = IBLSheenBRDF( geometryNormal, geometryViewDir, material.sheenRoughness );
		sheenSpecularIndirect += irradiance * material.sheenColor * sheenAlbedo * RECIPROCAL_PI;
		float sheenEnergyComp = 1.0 - max3( material.sheenColor ) * sheenAlbedo;
		diffuse *= sheenEnergyComp;
	#endif
	reflectedLight.indirectDiffuse += diffuse;
}
void RE_IndirectSpecular_Physical( const in vec3 radiance, const in vec3 irradiance, const in vec3 clearcoatRadiance, const in vec3 geometryPosition, const in vec3 geometryNormal, const in vec3 geometryViewDir, const in vec3 geometryClearcoatNormal, const in PhysicalMaterial material, inout ReflectedLight reflectedLight) {
	#ifdef USE_CLEARCOAT
		clearcoatSpecularIndirect += clearcoatRadiance * EnvironmentBRDF( geometryClearcoatNormal, geometryViewDir, material.clearcoatF0, material.clearcoatF90, material.clearcoatRoughness );
	#endif
	#ifdef USE_SHEEN
		sheenSpecularIndirect += irradiance * material.sheenColor * IBLSheenBRDF( geometryNormal, geometryViewDir, material.sheenRoughness ) * RECIPROCAL_PI;
 	#endif
	vec3 singleScatteringDielectric = vec3( 0.0 );
	vec3 multiScatteringDielectric = vec3( 0.0 );
	vec3 singleScatteringMetallic = vec3( 0.0 );
	vec3 multiScatteringMetallic = vec3( 0.0 );
	#ifdef USE_IRIDESCENCE
		computeMultiscatteringIridescence( material.dfg, material.specularColor, material.specularF90, material.iridescence, material.iridescenceF0Dielectric, singleScatteringDielectric, multiScatteringDielectric );
		computeMultiscatteringIridescence( material.dfg, material.diffuseColor, material.specularF90, material.iridescence, material.iridescenceF0Metallic, singleScatteringMetallic, multiScatteringMetallic );
	#else
		computeMultiscattering( material.dfg, material.specularColor, material.specularF90, singleScatteringDielectric, multiScatteringDielectric );
		computeMultiscattering( material.dfg, material.diffuseColor, material.specularF90, singleScatteringMetallic, multiScatteringMetallic );
	#endif
	vec3 singleScattering = mix( singleScatteringDielectric, singleScatteringMetallic, material.metalness );
	vec3 multiScattering = mix( multiScatteringDielectric, multiScatteringMetallic, material.metalness );
	vec3 totalScatteringDielectric = singleScatteringDielectric + multiScatteringDielectric;
	vec3 diffuse = material.diffuseContribution * ( 1.0 - totalScatteringDielectric );
	vec3 cosineWeightedIrradiance = irradiance * RECIPROCAL_PI;
	vec3 indirectSpecular = radiance * singleScattering;
	indirectSpecular += multiScattering * cosineWeightedIrradiance;
	vec3 indirectDiffuse = diffuse * cosineWeightedIrradiance;
	#ifdef USE_SHEEN
		float sheenAlbedo = IBLSheenBRDF( geometryNormal, geometryViewDir, material.sheenRoughness );
		float sheenEnergyComp = 1.0 - max3( material.sheenColor ) * sheenAlbedo;
		indirectSpecular *= sheenEnergyComp;
		indirectDiffuse *= sheenEnergyComp;
	#endif
	reflectedLight.indirectSpecular += indirectSpecular;
	reflectedLight.indirectDiffuse += indirectDiffuse;
}
#define RE_Direct				RE_Direct_Physical
#define RE_Direct_RectArea		RE_Direct_RectArea_Physical
#define RE_IndirectDiffuse		RE_IndirectDiffuse_Physical
#define RE_IndirectSpecular		RE_IndirectSpecular_Physical
float computeSpecularOcclusion( const in float dotNV, const in float ambientOcclusion, const in float roughness ) {
	return saturate( pow( dotNV + ambientOcclusion, exp2( - 16.0 * roughness - 1.0 ) ) - 1.0 + ambientOcclusion );
}`,nd=`
vec3 geometryPosition = - vViewPosition;
vec3 geometryNormal = normal;
vec3 geometryViewDir = ( isOrthographic ) ? vec3( 0, 0, 1 ) : normalize( vViewPosition );
vec3 geometryClearcoatNormal = vec3( 0.0 );
#ifdef USE_CLEARCOAT
	geometryClearcoatNormal = clearcoatNormal;
#endif
#ifdef USE_IRIDESCENCE
	float dotNVi = saturate( dot( normal, geometryViewDir ) );
	if ( material.iridescenceThickness == 0.0 ) {
		material.iridescence = 0.0;
	} else {
		material.iridescence = saturate( material.iridescence );
	}
	if ( material.iridescence > 0.0 ) {
		vec3 iridescenceFresnelDielectric = evalIridescence( 1.0, material.iridescenceIOR, dotNVi, material.iridescenceThickness, material.specularColor );
		vec3 iridescenceFresnelMetallic = evalIridescence( 1.0, material.iridescenceIOR, dotNVi, material.iridescenceThickness, material.diffuseColor );
		material.iridescenceFresnel = mix( iridescenceFresnelDielectric, iridescenceFresnelMetallic, material.metalness );
		material.iridescenceF0Dielectric = Schlick_to_F0( iridescenceFresnelDielectric, 1.0, dotNVi );
		material.iridescenceF0Metallic = Schlick_to_F0( iridescenceFresnelMetallic, 1.0, dotNVi );
	}
#endif
#ifdef STANDARD
	float dotNVms = saturate( dot( geometryNormal, geometryViewDir ) );
	material.dfg = texture2D( dfgLUT, vec2( material.roughness, dotNVms ) ).rg;
	#if ( NUM_SUN_LIGHTS > 0 || NUM_DIR_LIGHTS > 0 || NUM_POINT_LIGHTS > 0 || NUM_SPOT_LIGHTS > 0 )
		float EssMs = material.dfg.x + material.dfg.y;
		material.multiScatteringCompensation = 1.0 + material.specularColorBlended * ( 1.0 / EssMs - 1.0 );
	#endif
#endif
IncidentLight directLight;
#if ( NUM_POINT_LIGHTS > 0 ) && defined( RE_Direct )
	PointLight pointLight;
	#if defined( USE_SHADOWMAP ) && NUM_POINT_LIGHT_SHADOWS > 0
	PointLightShadow pointLightShadow;
	#endif
	#pragma unroll_loop_start
	for ( int i = 0; i < NUM_POINT_LIGHTS; i ++ ) {
		pointLight = pointLights[ i ];
		getPointLightInfo( pointLight, geometryPosition, directLight );
		#if defined( USE_SHADOWMAP ) && ( UNROLLED_LOOP_INDEX < NUM_POINT_LIGHT_SHADOWS ) && ( defined( SHADOWMAP_TYPE_PCF ) || defined( SHADOWMAP_TYPE_BASIC ) )
		pointLightShadow = pointLightShadows[ i ];
		directLight.color *= ( directLight.visible && receiveShadow ) ? getPointShadow( pointShadowMap[ i ], pointLightShadow.shadowMapSize, pointLightShadow.shadowIntensity, pointLightShadow.shadowBias, pointLightShadow.shadowRadius, vPointShadowCoord[ i ], pointLightShadow.shadowCameraNear, pointLightShadow.shadowCameraFar ) : 1.0;
		#endif
		RE_Direct( directLight, geometryPosition, geometryNormal, geometryViewDir, geometryClearcoatNormal, material, reflectedLight );
	}
	#pragma unroll_loop_end
#endif
#if ( NUM_SPOT_LIGHTS > 0 ) && defined( RE_Direct )
	SpotLight spotLight;
	vec4 spotColor;
	vec3 spotLightCoord;
	bool inSpotLightMap;
	#if defined( USE_SHADOWMAP ) && NUM_SPOT_LIGHT_SHADOWS > 0
	SpotLightShadow spotLightShadow;
	#endif
	#pragma unroll_loop_start
	for ( int i = 0; i < NUM_SPOT_LIGHTS; i ++ ) {
		spotLight = spotLights[ i ];
		getSpotLightInfo( spotLight, geometryPosition, directLight );
		#if ( UNROLLED_LOOP_INDEX < NUM_SPOT_LIGHT_SHADOWS_WITH_MAPS )
		#define SPOT_LIGHT_MAP_INDEX UNROLLED_LOOP_INDEX
		#elif ( UNROLLED_LOOP_INDEX < NUM_SPOT_LIGHT_SHADOWS )
		#define SPOT_LIGHT_MAP_INDEX NUM_SPOT_LIGHT_MAPS
		#else
		#define SPOT_LIGHT_MAP_INDEX ( UNROLLED_LOOP_INDEX - NUM_SPOT_LIGHT_SHADOWS + NUM_SPOT_LIGHT_SHADOWS_WITH_MAPS )
		#endif
		#if ( SPOT_LIGHT_MAP_INDEX < NUM_SPOT_LIGHT_MAPS )
			spotLightCoord = vSpotLightCoord[ i ].xyz / vSpotLightCoord[ i ].w;
			inSpotLightMap = all( lessThan( abs( spotLightCoord * 2. - 1. ), vec3( 1.0 ) ) );
			spotColor = texture2D( spotLightMap[ SPOT_LIGHT_MAP_INDEX ], spotLightCoord.xy );
			directLight.color = inSpotLightMap ? directLight.color * spotColor.rgb : directLight.color;
		#endif
		#undef SPOT_LIGHT_MAP_INDEX
		#if defined( USE_SHADOWMAP ) && ( UNROLLED_LOOP_INDEX < NUM_SPOT_LIGHT_SHADOWS )
		spotLightShadow = spotLightShadows[ i ];
		directLight.color *= ( directLight.visible && receiveShadow ) ? getShadow( spotShadowMap[ i ], spotLightShadow.shadowMapSize, spotLightShadow.shadowIntensity, spotLightShadow.shadowBias, spotLightShadow.shadowRadius, vSpotLightCoord[ i ] ) : 1.0;
		#endif
		RE_Direct( directLight, geometryPosition, geometryNormal, geometryViewDir, geometryClearcoatNormal, material, reflectedLight );
	}
	#pragma unroll_loop_end
#endif
#if ( NUM_SUN_LIGHTS > 0 ) && defined( RE_Direct )
	SunLight sunLight;
	#if defined( USE_SHADOWMAP ) && NUM_SUN_LIGHT_SHADOWS > 0
	SunLightShadow sunLightShadow;
	#endif
	#pragma unroll_loop_start
	for ( int i = 0; i < NUM_SUN_LIGHTS; i ++ ) {
		sunLight = sunLights[ i ];
		getSunLightInfo( sunLight, directLight );
		#if defined( USE_SHADOWMAP ) && ( UNROLLED_LOOP_INDEX < NUM_SUN_LIGHT_SHADOWS )
		sunLightShadow = sunLightShadows[ i ];
		directLight.color *= ( directLight.visible && receiveShadow ) ? getSunShadow( sunShadowMap[ i ], sunLightShadow, UNROLLED_LOOP_INDEX ) : 1.0;
		#endif
		RE_Direct( directLight, geometryPosition, geometryNormal, geometryViewDir, geometryClearcoatNormal, material, reflectedLight );
	}
	#pragma unroll_loop_end
#endif
#if ( NUM_DIR_LIGHTS > 0 ) && defined( RE_Direct )
	DirectionalLight directionalLight;
	#if defined( USE_SHADOWMAP ) && NUM_DIR_LIGHT_SHADOWS > 0
	DirectionalLightShadow directionalLightShadow;
	#endif
	#pragma unroll_loop_start
	for ( int i = 0; i < NUM_DIR_LIGHTS; i ++ ) {
		directionalLight = directionalLights[ i ];
		getDirectionalLightInfo( directionalLight, directLight );
		#if defined( USE_SHADOWMAP ) && ( UNROLLED_LOOP_INDEX < NUM_DIR_LIGHT_SHADOWS )
		directionalLightShadow = directionalLightShadows[ i ];
		directLight.color *= ( directLight.visible && receiveShadow ) ? getShadow( directionalShadowMap[ i ], directionalLightShadow.shadowMapSize, directionalLightShadow.shadowIntensity, directionalLightShadow.shadowBias, directionalLightShadow.shadowRadius, vDirectionalShadowCoord[ i ] ) : 1.0;
		#endif
		RE_Direct( directLight, geometryPosition, geometryNormal, geometryViewDir, geometryClearcoatNormal, material, reflectedLight );
	}
	#pragma unroll_loop_end
#endif
#if ( NUM_RECT_AREA_LIGHTS > 0 ) && defined( RE_Direct_RectArea )
	RectAreaLight rectAreaLight;
	#pragma unroll_loop_start
	for ( int i = 0; i < NUM_RECT_AREA_LIGHTS; i ++ ) {
		rectAreaLight = rectAreaLights[ i ];
		RE_Direct_RectArea( rectAreaLight, geometryPosition, geometryNormal, geometryViewDir, geometryClearcoatNormal, material, reflectedLight );
	}
	#pragma unroll_loop_end
#endif
#if defined( RE_IndirectDiffuse )
	vec3 iblIrradiance = vec3( 0.0 );
	vec3 irradiance = getAmbientLightIrradiance( ambientLightColor );
	#if defined( USE_LIGHT_PROBES )
		irradiance += getLightProbeIrradiance( lightProbe, geometryNormal );
	#endif
	#if ( NUM_HEMI_LIGHTS > 0 )
		#pragma unroll_loop_start
		for ( int i = 0; i < NUM_HEMI_LIGHTS; i ++ ) {
			irradiance += getHemisphereLightIrradiance( hemisphereLights[ i ], geometryNormal );
		}
		#pragma unroll_loop_end
	#endif
	#ifdef USE_LIGHT_PROBES_GRID
		vec3 probeWorldPos = ( ( vec4( geometryPosition, 1.0 ) - viewMatrix[ 3 ] ) * viewMatrix ).xyz;
		vec3 probeWorldNormal = transformNormalByInverseViewMatrix( geometryNormal, viewMatrix );
		irradiance += getLightProbeGridIrradiance( probeWorldPos, probeWorldNormal );
	#endif
#endif
#if defined( RE_IndirectSpecular )
	vec3 radiance = vec3( 0.0 );
	vec3 clearcoatRadiance = vec3( 0.0 );
#endif`,id=`#if defined( RE_IndirectDiffuse )
	#ifdef USE_LIGHTMAP
		vec4 lightMapTexel = texture2D( lightMap, vLightMapUv );
		vec3 lightMapIrradiance = lightMapTexel.rgb * lightMapIntensity;
		irradiance += lightMapIrradiance;
	#endif
	#if defined( USE_ENVMAP ) && defined( ENVMAP_TYPE_CUBE_UV )
		#if defined( STANDARD ) || defined( LAMBERT ) || defined( PHONG )
			iblIrradiance += getIBLIrradiance( geometryNormal );
		#endif
	#endif
#endif
#if defined( USE_ENVMAP ) && defined( RE_IndirectSpecular )
	#ifdef USE_ANISOTROPY
		vec3 iblRadiance = getIBLAnisotropyRadiance( geometryViewDir, geometryNormal, material.roughness, material.anisotropyB, material.anisotropy );
	#else
		vec3 iblRadiance = getIBLRadiance( geometryViewDir, geometryNormal, material.roughness );
	#endif
	#ifdef USE_RETROREFLECTION
		#ifdef USE_ANISOTROPY
			vec3 retroIBLRadiance = getIBLAnisotropyRetroRadiance( geometryViewDir, geometryNormal, material.roughness, material.anisotropyB, material.anisotropy );
		#else
			vec3 retroIBLRadiance = getIBLRetroRadiance( geometryViewDir, geometryNormal, material.roughness );
		#endif
		iblRadiance = mix( iblRadiance, retroIBLRadiance, saturate( material.retroreflectivity ) );
	#endif
	radiance += iblRadiance;
	#ifdef USE_CLEARCOAT
		clearcoatRadiance += getIBLRadiance( geometryViewDir, geometryClearcoatNormal, material.clearcoatRoughness );
	#endif
#endif`,sd=`#if defined( RE_IndirectDiffuse )
	#if defined( LAMBERT ) || defined( PHONG )
		irradiance += iblIrradiance;
	#endif
	RE_IndirectDiffuse( irradiance, geometryPosition, geometryNormal, geometryViewDir, geometryClearcoatNormal, material, reflectedLight );
#endif
#if defined( RE_IndirectSpecular )
	RE_IndirectSpecular( radiance, iblIrradiance, clearcoatRadiance, geometryPosition, geometryNormal, geometryViewDir, geometryClearcoatNormal, material, reflectedLight );
#endif`,rd=`#ifdef USE_LIGHT_PROBES_GRID
uniform highp sampler3D probesSH;
uniform vec3 probesMin;
uniform vec3 probesMax;
uniform vec3 probesResolution;
vec3 getLightProbeGridIrradiance( vec3 worldPos, vec3 worldNormal ) {
	vec3 res = probesResolution;
	vec3 gridRange = probesMax - probesMin;
	vec3 resMinusOne = res - 1.0;
	vec3 probeSpacing = gridRange / resMinusOne;
	vec3 samplePos = worldPos + worldNormal * probeSpacing * 0.5;
	vec3 uvw = clamp( ( samplePos - probesMin ) / gridRange, 0.0, 1.0 );
	uvw = uvw * resMinusOne / res + 0.5 / res;
	float nz          = res.z;
	float paddedSlices = nz + 2.0;
	float atlasDepth  = 7.0 * paddedSlices;
	float uvZBase     = uvw.z * nz + 1.0;
	vec4 s0 = texture( probesSH, vec3( uvw.xy, ( uvZBase                       ) / atlasDepth ) );
	vec4 s1 = texture( probesSH, vec3( uvw.xy, ( uvZBase +       paddedSlices   ) / atlasDepth ) );
	vec4 s2 = texture( probesSH, vec3( uvw.xy, ( uvZBase + 2.0 * paddedSlices   ) / atlasDepth ) );
	vec4 s3 = texture( probesSH, vec3( uvw.xy, ( uvZBase + 3.0 * paddedSlices   ) / atlasDepth ) );
	vec4 s4 = texture( probesSH, vec3( uvw.xy, ( uvZBase + 4.0 * paddedSlices   ) / atlasDepth ) );
	vec4 s5 = texture( probesSH, vec3( uvw.xy, ( uvZBase + 5.0 * paddedSlices   ) / atlasDepth ) );
	vec4 s6 = texture( probesSH, vec3( uvw.xy, ( uvZBase + 6.0 * paddedSlices   ) / atlasDepth ) );
	vec3 c0 = s0.xyz;
	vec3 c1 = vec3( s0.w, s1.xy );
	vec3 c2 = vec3( s1.zw, s2.x );
	vec3 c3 = s2.yzw;
	vec3 c4 = s3.xyz;
	vec3 c5 = vec3( s3.w, s4.xy );
	vec3 c6 = vec3( s4.zw, s5.x );
	vec3 c7 = s5.yzw;
	vec3 c8 = s6.xyz;
	float x = worldNormal.x, y = worldNormal.y, z = worldNormal.z;
	vec3 result = c0 * 0.886227;
	result += c1 * 2.0 * 0.511664 * y;
	result += c2 * 2.0 * 0.511664 * z;
	result += c3 * 2.0 * 0.511664 * x;
	result += c4 * 2.0 * 0.429043 * x * y;
	result += c5 * 2.0 * 0.429043 * y * z;
	result += c6 * ( 0.743125 * z * z - 0.247708 );
	result += c7 * 2.0 * 0.429043 * x * z;
	result += c8 * 0.429043 * ( x * x - y * y );
	return max( result, vec3( 0.0 ) );
}
#endif`,ad=`#if defined( USE_LOGARITHMIC_DEPTH_BUFFER )
	gl_FragDepth = vIsPerspective == 0.0 ? gl_FragCoord.z : log2( vFragDepth ) * logDepthBufFC * 0.5;
#endif`,od=`#if defined( USE_LOGARITHMIC_DEPTH_BUFFER )
	uniform float logDepthBufFC;
	varying float vFragDepth;
	varying float vIsPerspective;
#endif`,cd=`#ifdef USE_LOGARITHMIC_DEPTH_BUFFER
	varying float vFragDepth;
	varying float vIsPerspective;
#endif`,ld=`#ifdef USE_LOGARITHMIC_DEPTH_BUFFER
	vFragDepth = 1.0 + gl_Position.w;
	vIsPerspective = float( isPerspectiveMatrix( projectionMatrix ) );
#endif`,ud=`#ifdef USE_MAP
	vec4 sampledDiffuseColor = texture2D( map, vMapUv );
	#ifdef DECODE_VIDEO_TEXTURE
		sampledDiffuseColor = sRGBTransferEOTF( sampledDiffuseColor );
	#endif
	diffuseColor *= sampledDiffuseColor;
#endif`,hd=`#ifdef USE_MAP
	uniform sampler2D map;
#endif`,fd=`#if defined( USE_MAP ) || defined( USE_ALPHAMAP )
	#if defined( USE_POINTS_UV )
		vec2 uv = vUv;
	#else
		vec2 uv = ( uvTransform * vec3( gl_PointCoord.x, 1.0 - gl_PointCoord.y, 1 ) ).xy;
	#endif
#endif
#ifdef USE_MAP
	diffuseColor *= texture2D( map, uv );
#endif
#ifdef USE_ALPHAMAP
	diffuseColor.a *= texture2D( alphaMap, uv ).g;
#endif`,dd=`#if defined( USE_POINTS_UV )
	varying vec2 vUv;
#else
	#if defined( USE_MAP ) || defined( USE_ALPHAMAP )
		uniform mat3 uvTransform;
	#endif
#endif
#ifdef USE_MAP
	uniform sampler2D map;
#endif
#ifdef USE_ALPHAMAP
	uniform sampler2D alphaMap;
#endif`,pd=`float metalnessFactor = metalness;
#ifdef USE_METALNESSMAP
	vec4 texelMetalness = texture2D( metalnessMap, vMetalnessMapUv );
	metalnessFactor *= texelMetalness.b;
#endif`,md=`#ifdef USE_METALNESSMAP
	uniform sampler2D metalnessMap;
#endif`,gd=`#ifdef USE_INSTANCING_MORPH
	float morphTargetInfluences[ MORPHTARGETS_COUNT ];
	float morphTargetBaseInfluence = texelFetch( morphTexture, ivec2( 0, gl_InstanceID ), 0 ).r;
	for ( int i = 0; i < MORPHTARGETS_COUNT; i ++ ) {
		morphTargetInfluences[i] =  texelFetch( morphTexture, ivec2( i + 1, gl_InstanceID ), 0 ).r;
	}
#endif`,xd=`#if defined( USE_MORPHCOLORS )
	vColor *= morphTargetBaseInfluence;
	for ( int i = 0; i < MORPHTARGETS_COUNT; i ++ ) {
		#if defined( USE_COLOR_ALPHA )
			if ( morphTargetInfluences[ i ] != 0.0 ) vColor += getMorph( gl_VertexID, i, 2 ) * morphTargetInfluences[ i ];
		#elif defined( USE_COLOR )
			if ( morphTargetInfluences[ i ] != 0.0 ) vColor += getMorph( gl_VertexID, i, 2 ).rgb * morphTargetInfluences[ i ];
		#endif
	}
#endif`,bd=`#ifdef USE_MORPHNORMALS
	objectNormal *= morphTargetBaseInfluence;
	for ( int i = 0; i < MORPHTARGETS_COUNT; i ++ ) {
		if ( morphTargetInfluences[ i ] != 0.0 ) objectNormal += getMorph( gl_VertexID, i, 1 ).xyz * morphTargetInfluences[ i ];
	}
#endif`,_d=`#ifdef USE_MORPHTARGETS
	#ifndef USE_INSTANCING_MORPH
		uniform float morphTargetBaseInfluence;
		uniform float morphTargetInfluences[ MORPHTARGETS_COUNT ];
	#endif
	uniform sampler2DArray morphTargetsTexture;
	uniform ivec2 morphTargetsTextureSize;
	vec4 getMorph( const in int vertexIndex, const in int morphTargetIndex, const in int offset ) {
		int texelIndex = vertexIndex * MORPHTARGETS_TEXTURE_STRIDE + offset;
		int y = texelIndex / morphTargetsTextureSize.x;
		int x = texelIndex - y * morphTargetsTextureSize.x;
		ivec3 morphUV = ivec3( x, y, morphTargetIndex );
		return texelFetch( morphTargetsTexture, morphUV, 0 );
	}
#endif`,yd=`#ifdef USE_MORPHTARGETS
	transformed *= morphTargetBaseInfluence;
	for ( int i = 0; i < MORPHTARGETS_COUNT; i ++ ) {
		if ( morphTargetInfluences[ i ] != 0.0 ) transformed += getMorph( gl_VertexID, i, 0 ).xyz * morphTargetInfluences[ i ];
	}
#endif`,vd=`float faceDirection = gl_FrontFacing ? 1.0 : - 1.0;
#ifdef FLAT_SHADED
	vec3 fdx = dFdx( vViewPosition );
	vec3 fdy = dFdy( vViewPosition );
	vec3 normal = normalize( cross( fdx, fdy ) );
#else
	vec3 normal = normalize( vNormal );
	#ifdef DOUBLE_SIDED
		normal *= faceDirection;
	#endif
#endif
#if defined( USE_NORMALMAP_TANGENTSPACE ) || defined( USE_CLEARCOAT_NORMALMAP ) || defined( USE_ANISOTROPY )
	#ifdef USE_TANGENT
		mat3 tbn = mat3( normalize( vTangent ), normalize( vBitangent ), normal );
	#else
		mat3 tbn = getTangentFrame( - vViewPosition, normal,
		#if defined( USE_NORMALMAP )
			vNormalMapUv
		#elif defined( USE_CLEARCOAT_NORMALMAP )
			vClearcoatNormalMapUv
		#else
			vUv
		#endif
		);
	#endif
	#ifdef DOUBLE_SIDED
		tbn[0] *= faceDirection;
		tbn[1] *= faceDirection;
	#endif
#endif
#ifdef USE_CLEARCOAT_NORMALMAP
	#ifdef USE_TANGENT
		mat3 tbn2 = mat3( normalize( vTangent ), normalize( vBitangent ), normal );
	#else
		mat3 tbn2 = getTangentFrame( - vViewPosition, normal, vClearcoatNormalMapUv );
	#endif
	#ifdef DOUBLE_SIDED
		tbn2[0] *= faceDirection;
		tbn2[1] *= faceDirection;
	#endif
#endif
vec3 nonPerturbedNormal = normal;`,Sd=`#ifdef USE_NORMALMAP_OBJECTSPACE
	normal = texture2D( normalMap, vNormalMapUv ).xyz * 2.0 - 1.0;
	#ifdef FLIP_SIDED
		normal = - normal;
	#endif
	#ifdef DOUBLE_SIDED
		normal = normal * faceDirection;
	#endif
	normal = normalize( normalMatrix * normal );
#elif defined( USE_NORMALMAP_TANGENTSPACE )
	vec3 mapN = texture2D( normalMap, vNormalMapUv ).xyz * 2.0 - 1.0;
	#if defined( USE_PACKED_NORMALMAP )
		mapN = vec3( mapN.xy, sqrt( saturate( 1.0 - dot( mapN.xy, mapN.xy ) ) ) );
	#endif
	mapN.xy *= normalScale;
	normal = normalize( tbn * mapN );
#elif defined( USE_BUMPMAP )
	normal = perturbNormalArb( - vViewPosition, normal, dHdxy_fwd(), faceDirection );
#endif`,Md=`#ifndef FLAT_SHADED
	varying vec3 vNormal;
	#ifdef USE_TANGENT
		varying vec3 vTangent;
		varying vec3 vBitangent;
	#endif
#endif`,Ad=`#ifndef FLAT_SHADED
	varying vec3 vNormal;
	#ifdef USE_TANGENT
		varying vec3 vTangent;
		varying vec3 vBitangent;
	#endif
#endif`,Td=`#ifndef FLAT_SHADED
	vNormal = normalize( transformedNormal );
	#ifdef USE_TANGENT
		vTangent = normalize( transformedTangent );
		vBitangent = normalize( cross( vNormal, vTangent ) * tangent.w );
		#ifdef FLIP_SIDED
			vBitangent = - vBitangent;
		#endif
	#endif
#endif`,wd=`#ifdef USE_NORMALMAP
	uniform sampler2D normalMap;
	uniform vec2 normalScale;
#endif
#ifdef USE_NORMALMAP_OBJECTSPACE
	uniform mat3 normalMatrix;
#endif
#if ! defined ( USE_TANGENT ) && ( defined ( USE_NORMALMAP_TANGENTSPACE ) || defined ( USE_CLEARCOAT_NORMALMAP ) || defined( USE_ANISOTROPY ) )
	mat3 getTangentFrame( vec3 eye_pos, vec3 surf_norm, vec2 uv ) {
		vec3 q0 = dFdx( eye_pos.xyz );
		vec3 q1 = dFdy( eye_pos.xyz );
		vec2 st0 = dFdx( uv.st );
		vec2 st1 = dFdy( uv.st );
		vec3 N = surf_norm;
		vec3 q1perp = cross( q1, N );
		vec3 q0perp = cross( N, q0 );
		vec3 T = q1perp * st0.x + q0perp * st1.x;
		vec3 B = q1perp * st0.y + q0perp * st1.y;
		float det = max( dot( T, T ), dot( B, B ) );
		float scale = ( det == 0.0 ) ? 0.0 : inversesqrt( det );
		return mat3( T * scale, B * scale, N );
	}
#endif`,Ed=`#ifdef USE_CLEARCOAT
	vec3 clearcoatNormal = nonPerturbedNormal;
#endif`,Rd=`#ifdef USE_CLEARCOAT_NORMALMAP
	vec3 clearcoatMapN = texture2D( clearcoatNormalMap, vClearcoatNormalMapUv ).xyz * 2.0 - 1.0;
	clearcoatMapN.xy *= clearcoatNormalScale;
	clearcoatNormal = normalize( tbn2 * clearcoatMapN );
#endif`,Cd=`#ifdef USE_CLEARCOATMAP
	uniform sampler2D clearcoatMap;
#endif
#ifdef USE_CLEARCOAT_NORMALMAP
	uniform sampler2D clearcoatNormalMap;
	uniform vec2 clearcoatNormalScale;
#endif
#ifdef USE_CLEARCOAT_ROUGHNESSMAP
	uniform sampler2D clearcoatRoughnessMap;
#endif`,Id=`#ifdef USE_IRIDESCENCEMAP
	uniform sampler2D iridescenceMap;
#endif
#ifdef USE_IRIDESCENCE_THICKNESSMAP
	uniform sampler2D iridescenceThicknessMap;
#endif`,Pd=`#ifdef OPAQUE
diffuseColor.a = 1.0;
#endif
#ifdef USE_TRANSMISSION
diffuseColor.a *= material.transmissionAlpha;
#endif
gl_FragColor = vec4( outgoingLight, diffuseColor.a );`,Ld=`vec3 packNormalToRGB( const in vec3 normal ) {
	return normalize( normal ) * 0.5 + 0.5;
}
vec3 unpackRGBToNormal( const in vec3 rgb ) {
	return 2.0 * rgb.xyz - 1.0;
}
const float PackUpscale = 256. / 255.;const float UnpackDownscale = 255. / 256.;const float ShiftRight8 = 1. / 256.;
const float Inv255 = 1. / 255.;
const vec4 PackFactors = vec4( 1.0, 256.0, 256.0 * 256.0, 256.0 * 256.0 * 256.0 );
const vec2 UnpackFactors2 = vec2( UnpackDownscale, 1.0 / PackFactors.g );
const vec3 UnpackFactors3 = vec3( UnpackDownscale / PackFactors.rg, 1.0 / PackFactors.b );
const vec4 UnpackFactors4 = vec4( UnpackDownscale / PackFactors.rgb, 1.0 / PackFactors.a );
vec4 packDepthToRGBA( const in float v ) {
	if( v <= 0.0 )
		return vec4( 0., 0., 0., 0. );
	if( v >= 1.0 )
		return vec4( 1., 1., 1., 1. );
	float vuf;
	float af = modf( v * PackFactors.a, vuf );
	float bf = modf( vuf * ShiftRight8, vuf );
	float gf = modf( vuf * ShiftRight8, vuf );
	return vec4( vuf * Inv255, gf * PackUpscale, bf * PackUpscale, af );
}
vec3 packDepthToRGB( const in float v ) {
	if( v <= 0.0 )
		return vec3( 0., 0., 0. );
	if( v >= 1.0 )
		return vec3( 1., 1., 1. );
	float vuf;
	float bf = modf( v * PackFactors.b, vuf );
	float gf = modf( vuf * ShiftRight8, vuf );
	return vec3( vuf * Inv255, gf * PackUpscale, bf );
}
vec2 packDepthToRG( const in float v ) {
	if( v <= 0.0 )
		return vec2( 0., 0. );
	if( v >= 1.0 )
		return vec2( 1., 1. );
	float vuf;
	float gf = modf( v * 256., vuf );
	return vec2( vuf * Inv255, gf );
}
float unpackRGBAToDepth( const in vec4 v ) {
	return dot( v, UnpackFactors4 );
}
float unpackRGBToDepth( const in vec3 v ) {
	return dot( v, UnpackFactors3 );
}
float unpackRGToDepth( const in vec2 v ) {
	return v.r * UnpackFactors2.r + v.g * UnpackFactors2.g;
}
vec4 pack2HalfToRGBA( const in vec2 v ) {
	vec4 r = vec4( v.x, fract( v.x * 255.0 ), v.y, fract( v.y * 255.0 ) );
	return vec4( r.x - r.y / 255.0, r.y, r.z - r.w / 255.0, r.w );
}
vec2 unpackRGBATo2Half( const in vec4 v ) {
	return vec2( v.x + ( v.y / 255.0 ), v.z + ( v.w / 255.0 ) );
}
float viewZToOrthographicDepth( const in float viewZ, const in float near, const in float far ) {
	return ( viewZ + near ) / ( near - far );
}
float orthographicDepthToViewZ( const in float depth, const in float near, const in float far ) {
	#ifdef USE_REVERSED_DEPTH_BUFFER
	
		return depth * ( far - near ) - far;
	#else
		return depth * ( near - far ) - near;
	#endif
}
float viewZToPerspectiveDepth( const in float viewZ, const in float near, const in float far ) {
	return ( ( near + viewZ ) * far ) / ( ( far - near ) * viewZ );
}
float perspectiveDepthToViewZ( const in float depth, const in float near, const in float far ) {
	
	#ifdef USE_REVERSED_DEPTH_BUFFER
		return ( near * far ) / ( ( near - far ) * depth - near );
	#else
		return ( near * far ) / ( ( far - near ) * depth - far );
	#endif
}`,Dd=`#ifdef PREMULTIPLIED_ALPHA
	gl_FragColor.rgb *= gl_FragColor.a;
#endif`,Nd=`vec4 mvPosition = vec4( transformed, 1.0 );
#ifdef USE_BATCHING
	mvPosition = batchingMatrix * mvPosition;
#endif
#ifdef USE_INSTANCING
	mvPosition = instanceMatrix * mvPosition;
#endif
mvPosition = modelViewMatrix * mvPosition;
gl_Position = projectionMatrix * mvPosition;`,Fd=`#ifdef DITHERING
	gl_FragColor.rgb = dithering( gl_FragColor.rgb );
#endif`,Ud=`#ifdef DITHERING
	vec3 dithering( vec3 color ) {
		float grid_position = rand( gl_FragCoord.xy );
		vec3 dither_shift_RGB = vec3( 0.25 / 255.0, -0.25 / 255.0, 0.25 / 255.0 );
		dither_shift_RGB = mix( 2.0 * dither_shift_RGB, -2.0 * dither_shift_RGB, grid_position );
		return color + dither_shift_RGB;
	}
#endif`,Od=`float roughnessFactor = roughness;
#ifdef USE_ROUGHNESSMAP
	vec4 texelRoughness = texture2D( roughnessMap, vRoughnessMapUv );
	roughnessFactor *= texelRoughness.g;
#endif`,Bd=`#ifdef USE_ROUGHNESSMAP
	uniform sampler2D roughnessMap;
#endif`,kd=`#if NUM_SPOT_LIGHT_COORDS > 0
	varying vec4 vSpotLightCoord[ NUM_SPOT_LIGHT_COORDS ];
#endif
#if NUM_SPOT_LIGHT_MAPS > 0
	uniform sampler2D spotLightMap[ NUM_SPOT_LIGHT_MAPS ];
#endif
#ifdef USE_SHADOWMAP
	#if NUM_SUN_LIGHT_SHADOWS > 0
		#define SUN_LIGHT_CASCADES 2
		#if defined( SHADOWMAP_TYPE_PCF )
			uniform sampler2DShadow sunShadowMap[ NUM_SUN_LIGHT_SHADOWS ];
		#else
			uniform sampler2D sunShadowMap[ NUM_SUN_LIGHT_SHADOWS ];
		#endif
		uniform mat4 sunShadowMatrix[ NUM_SUN_LIGHT_SHADOWS * SUN_LIGHT_CASCADES ];
		uniform vec4 sunShadowCascade[ NUM_SUN_LIGHT_SHADOWS * SUN_LIGHT_CASCADES ];
		varying vec4 vSunShadowWorldPosition;
		varying vec3 vSunShadowWorldNormal;
		struct SunLightShadow {
			float shadowIntensity;
			float shadowBias;
			float shadowNormalBias;
			float shadowRadius;
			vec2 shadowMapSize;
		};
		uniform SunLightShadow sunLightShadows[ NUM_SUN_LIGHT_SHADOWS ];
	#endif
	#if NUM_DIR_LIGHT_SHADOWS > 0
		#if defined( SHADOWMAP_TYPE_PCF )
			uniform sampler2DShadow directionalShadowMap[ NUM_DIR_LIGHT_SHADOWS ];
		#else
			uniform sampler2D directionalShadowMap[ NUM_DIR_LIGHT_SHADOWS ];
		#endif
		varying vec4 vDirectionalShadowCoord[ NUM_DIR_LIGHT_SHADOWS ];
		struct DirectionalLightShadow {
			float shadowIntensity;
			float shadowBias;
			float shadowNormalBias;
			float shadowRadius;
			vec2 shadowMapSize;
		};
		uniform DirectionalLightShadow directionalLightShadows[ NUM_DIR_LIGHT_SHADOWS ];
	#endif
	#if NUM_SPOT_LIGHT_SHADOWS > 0
		#if defined( SHADOWMAP_TYPE_PCF )
			uniform sampler2DShadow spotShadowMap[ NUM_SPOT_LIGHT_SHADOWS ];
		#else
			uniform sampler2D spotShadowMap[ NUM_SPOT_LIGHT_SHADOWS ];
		#endif
		struct SpotLightShadow {
			float shadowIntensity;
			float shadowBias;
			float shadowNormalBias;
			float shadowRadius;
			vec2 shadowMapSize;
		};
		uniform SpotLightShadow spotLightShadows[ NUM_SPOT_LIGHT_SHADOWS ];
	#endif
	#if NUM_POINT_LIGHT_SHADOWS > 0
		#if defined( SHADOWMAP_TYPE_PCF )
			uniform samplerCubeShadow pointShadowMap[ NUM_POINT_LIGHT_SHADOWS ];
		#elif defined( SHADOWMAP_TYPE_BASIC )
			uniform samplerCube pointShadowMap[ NUM_POINT_LIGHT_SHADOWS ];
		#endif
		varying vec4 vPointShadowCoord[ NUM_POINT_LIGHT_SHADOWS ];
		struct PointLightShadow {
			float shadowIntensity;
			float shadowBias;
			float shadowNormalBias;
			float shadowRadius;
			vec2 shadowMapSize;
			float shadowCameraNear;
			float shadowCameraFar;
		};
		uniform PointLightShadow pointLightShadows[ NUM_POINT_LIGHT_SHADOWS ];
	#endif
	#if defined( SHADOWMAP_TYPE_PCF )
		float interleavedGradientNoise( vec2 position ) {
			return fract( 52.9829189 * fract( dot( position, vec2( 0.06711056, 0.00583715 ) ) ) );
		}
		vec2 vogelDiskSample( int sampleIndex, int samplesCount, float phi ) {
			const float goldenAngle = 2.399963229728653;
			float r = sqrt( ( float( sampleIndex ) + 0.5 ) / float( samplesCount ) );
			float theta = float( sampleIndex ) * goldenAngle + phi;
			return vec2( cos( theta ), sin( theta ) ) * r;
		}
	#endif
	#if defined( SHADOWMAP_TYPE_PCF )
		float getShadow( sampler2DShadow shadowMap, vec2 shadowMapSize, float shadowIntensity, float shadowBias, float shadowRadius, vec4 shadowCoord ) {
			float shadow = 1.0;
			shadowCoord.xyz /= shadowCoord.w;
			shadowCoord.z += shadowBias;
			bool inFrustum = shadowCoord.x >= 0.0 && shadowCoord.x <= 1.0 && shadowCoord.y >= 0.0 && shadowCoord.y <= 1.0;
			bool frustumTest = inFrustum && shadowCoord.z <= 1.0;
			if ( frustumTest ) {
				vec2 texelSize = vec2( 1.0 ) / shadowMapSize;
				float radius = shadowRadius * texelSize.x;
				float phi = interleavedGradientNoise( gl_FragCoord.xy ) * PI2;
				shadow = (
					texture( shadowMap, vec3( shadowCoord.xy + vogelDiskSample( 0, 5, phi ) * radius, shadowCoord.z ) ) +
					texture( shadowMap, vec3( shadowCoord.xy + vogelDiskSample( 1, 5, phi ) * radius, shadowCoord.z ) ) +
					texture( shadowMap, vec3( shadowCoord.xy + vogelDiskSample( 2, 5, phi ) * radius, shadowCoord.z ) ) +
					texture( shadowMap, vec3( shadowCoord.xy + vogelDiskSample( 3, 5, phi ) * radius, shadowCoord.z ) ) +
					texture( shadowMap, vec3( shadowCoord.xy + vogelDiskSample( 4, 5, phi ) * radius, shadowCoord.z ) )
				) * 0.2;
			}
			return mix( 1.0, shadow, shadowIntensity );
		}
	#elif defined( SHADOWMAP_TYPE_VSM )
		float getShadow( sampler2D shadowMap, vec2 shadowMapSize, float shadowIntensity, float shadowBias, float shadowRadius, vec4 shadowCoord ) {
			float shadow = 1.0;
			shadowCoord.xyz /= shadowCoord.w;
			#ifdef USE_REVERSED_DEPTH_BUFFER
				shadowCoord.z -= shadowBias;
			#else
				shadowCoord.z += shadowBias;
			#endif
			bool inFrustum = shadowCoord.x >= 0.0 && shadowCoord.x <= 1.0 && shadowCoord.y >= 0.0 && shadowCoord.y <= 1.0;
			bool frustumTest = inFrustum && shadowCoord.z <= 1.0;
			if ( frustumTest ) {
				vec2 distribution = texture2D( shadowMap, shadowCoord.xy ).rg;
				float mean = distribution.x;
				float variance = distribution.y * distribution.y;
				#ifdef USE_REVERSED_DEPTH_BUFFER
					float hard_shadow = step( mean, shadowCoord.z );
				#else
					float hard_shadow = step( shadowCoord.z, mean );
				#endif
				
				if ( hard_shadow == 1.0 ) {
					shadow = 1.0;
				} else {
					variance = max( variance, 0.0000001 );
					float d = shadowCoord.z - mean;
					float p_max = variance / ( variance + d * d );
					p_max = clamp( ( p_max - 0.3 ) / 0.65, 0.0, 1.0 );
					shadow = max( hard_shadow, p_max );
				}
			}
			return mix( 1.0, shadow, shadowIntensity );
		}
	#else
		float getShadow( sampler2D shadowMap, vec2 shadowMapSize, float shadowIntensity, float shadowBias, float shadowRadius, vec4 shadowCoord ) {
			float shadow = 1.0;
			shadowCoord.xyz /= shadowCoord.w;
			#ifdef USE_REVERSED_DEPTH_BUFFER
				shadowCoord.z -= shadowBias;
			#else
				shadowCoord.z += shadowBias;
			#endif
			bool inFrustum = shadowCoord.x >= 0.0 && shadowCoord.x <= 1.0 && shadowCoord.y >= 0.0 && shadowCoord.y <= 1.0;
			bool frustumTest = inFrustum && shadowCoord.z <= 1.0;
			if ( frustumTest ) {
				float depth = texture2D( shadowMap, shadowCoord.xy ).r;
				#ifdef USE_REVERSED_DEPTH_BUFFER
					shadow = step( depth, shadowCoord.z );
				#else
					shadow = step( shadowCoord.z, depth );
				#endif
			}
			return mix( 1.0, shadow, shadowIntensity );
		}
	#endif
	#if NUM_SUN_LIGHT_SHADOWS > 0
		float getSunShadow(
			#if defined( SHADOWMAP_TYPE_PCF )
				sampler2DShadow shadowMap,
			#else
				sampler2D shadowMap,
			#endif
			SunLightShadow sunLightShadow,
			int shadowIndex
		) {
			vec4 shadowWorldPosition = vec4( vSunShadowWorldPosition.xyz + vSunShadowWorldNormal * sunLightShadow.shadowNormalBias, 1.0 );
			float viewDepth = vSunShadowWorldPosition.w;
			int cascadeOffset = shadowIndex * SUN_LIGHT_CASCADES;
			float shadow = 1.0;
			for ( int i = SUN_LIGHT_CASCADES - 1; i >= 0; i -- ) {
				vec4 cascade = sunShadowCascade[ cascadeOffset + i ];
				if ( viewDepth >= cascade.x && viewDepth < cascade.y ) {
					float cascadeShadow = getShadow(
						shadowMap,
						sunLightShadow.shadowMapSize,
						sunLightShadow.shadowIntensity,
						sunLightShadow.shadowBias,
						sunLightShadow.shadowRadius,
						sunShadowMatrix[ cascadeOffset + i ] * shadowWorldPosition
					);
					shadow = mix( cascadeShadow, shadow, smoothstep( cascade.z, cascade.y, viewDepth ) );
				}
			}
			return shadow;
		}
	#endif
	#if NUM_POINT_LIGHT_SHADOWS > 0
	#if defined( SHADOWMAP_TYPE_PCF )
	float getPointShadow( samplerCubeShadow shadowMap, vec2 shadowMapSize, float shadowIntensity, float shadowBias, float shadowRadius, vec4 shadowCoord, float shadowCameraNear, float shadowCameraFar ) {
		float shadow = 1.0;
		vec3 lightToPosition = shadowCoord.xyz;
		vec3 bd3D = normalize( lightToPosition );
		vec3 absVec = abs( lightToPosition );
		float viewSpaceZ = max( max( absVec.x, absVec.y ), absVec.z );
		if ( viewSpaceZ - shadowCameraFar <= 0.0 && viewSpaceZ - shadowCameraNear >= 0.0 ) {
			#ifdef USE_REVERSED_DEPTH_BUFFER
				float dp = ( shadowCameraNear * ( shadowCameraFar - viewSpaceZ ) ) / ( viewSpaceZ * ( shadowCameraFar - shadowCameraNear ) );
				dp -= shadowBias;
			#else
				float dp = ( shadowCameraFar * ( viewSpaceZ - shadowCameraNear ) ) / ( viewSpaceZ * ( shadowCameraFar - shadowCameraNear ) );
				dp += shadowBias;
			#endif
			float texelSize = shadowRadius / shadowMapSize.x;
			vec3 absDir = abs( bd3D );
			vec3 tangent = absDir.x > absDir.z ? vec3( 0.0, 1.0, 0.0 ) : vec3( 1.0, 0.0, 0.0 );
			tangent = normalize( cross( bd3D, tangent ) );
			vec3 bitangent = cross( bd3D, tangent );
			float phi = interleavedGradientNoise( gl_FragCoord.xy ) * PI2;
			vec2 sample0 = vogelDiskSample( 0, 5, phi );
			vec2 sample1 = vogelDiskSample( 1, 5, phi );
			vec2 sample2 = vogelDiskSample( 2, 5, phi );
			vec2 sample3 = vogelDiskSample( 3, 5, phi );
			vec2 sample4 = vogelDiskSample( 4, 5, phi );
			shadow = (
				texture( shadowMap, vec4( bd3D + ( tangent * sample0.x + bitangent * sample0.y ) * texelSize, dp ) ) +
				texture( shadowMap, vec4( bd3D + ( tangent * sample1.x + bitangent * sample1.y ) * texelSize, dp ) ) +
				texture( shadowMap, vec4( bd3D + ( tangent * sample2.x + bitangent * sample2.y ) * texelSize, dp ) ) +
				texture( shadowMap, vec4( bd3D + ( tangent * sample3.x + bitangent * sample3.y ) * texelSize, dp ) ) +
				texture( shadowMap, vec4( bd3D + ( tangent * sample4.x + bitangent * sample4.y ) * texelSize, dp ) )
			) * 0.2;
		}
		return mix( 1.0, shadow, shadowIntensity );
	}
	#elif defined( SHADOWMAP_TYPE_BASIC )
	float getPointShadow( samplerCube shadowMap, vec2 shadowMapSize, float shadowIntensity, float shadowBias, float shadowRadius, vec4 shadowCoord, float shadowCameraNear, float shadowCameraFar ) {
		float shadow = 1.0;
		vec3 lightToPosition = shadowCoord.xyz;
		vec3 absVec = abs( lightToPosition );
		float viewSpaceZ = max( max( absVec.x, absVec.y ), absVec.z );
		if ( viewSpaceZ - shadowCameraFar <= 0.0 && viewSpaceZ - shadowCameraNear >= 0.0 ) {
			float dp = ( shadowCameraFar * ( viewSpaceZ - shadowCameraNear ) ) / ( viewSpaceZ * ( shadowCameraFar - shadowCameraNear ) );
			dp += shadowBias;
			vec3 bd3D = normalize( lightToPosition );
			float depth = textureCube( shadowMap, bd3D ).r;
			#ifdef USE_REVERSED_DEPTH_BUFFER
				depth = 1.0 - depth;
			#endif
			shadow = step( dp, depth );
		}
		return mix( 1.0, shadow, shadowIntensity );
	}
	#endif
	#endif
#endif`,zd=`#if NUM_SPOT_LIGHT_COORDS > 0
	uniform mat4 spotLightMatrix[ NUM_SPOT_LIGHT_COORDS ];
	varying vec4 vSpotLightCoord[ NUM_SPOT_LIGHT_COORDS ];
#endif
#ifdef USE_SHADOWMAP
	#if NUM_SUN_LIGHT_SHADOWS > 0
		varying vec4 vSunShadowWorldPosition;
		varying vec3 vSunShadowWorldNormal;
	#endif
	#if NUM_DIR_LIGHT_SHADOWS > 0
		uniform mat4 directionalShadowMatrix[ NUM_DIR_LIGHT_SHADOWS ];
		varying vec4 vDirectionalShadowCoord[ NUM_DIR_LIGHT_SHADOWS ];
		struct DirectionalLightShadow {
			float shadowIntensity;
			float shadowBias;
			float shadowNormalBias;
			float shadowRadius;
			vec2 shadowMapSize;
		};
		uniform DirectionalLightShadow directionalLightShadows[ NUM_DIR_LIGHT_SHADOWS ];
	#endif
	#if NUM_SPOT_LIGHT_SHADOWS > 0
		struct SpotLightShadow {
			float shadowIntensity;
			float shadowBias;
			float shadowNormalBias;
			float shadowRadius;
			vec2 shadowMapSize;
		};
		uniform SpotLightShadow spotLightShadows[ NUM_SPOT_LIGHT_SHADOWS ];
	#endif
	#if NUM_POINT_LIGHT_SHADOWS > 0
		uniform mat4 pointShadowMatrix[ NUM_POINT_LIGHT_SHADOWS ];
		varying vec4 vPointShadowCoord[ NUM_POINT_LIGHT_SHADOWS ];
		struct PointLightShadow {
			float shadowIntensity;
			float shadowBias;
			float shadowNormalBias;
			float shadowRadius;
			vec2 shadowMapSize;
			float shadowCameraNear;
			float shadowCameraFar;
		};
		uniform PointLightShadow pointLightShadows[ NUM_POINT_LIGHT_SHADOWS ];
	#endif
#endif`,Vd=`#if ( defined( USE_SHADOWMAP ) && ( NUM_DIR_LIGHT_SHADOWS > 0 || NUM_SUN_LIGHT_SHADOWS > 0 || NUM_POINT_LIGHT_SHADOWS > 0 ) ) || ( NUM_SPOT_LIGHT_COORDS > 0 )
	#ifdef HAS_NORMAL
		vec3 shadowWorldNormal = transformNormalByInverseViewMatrix( transformedNormal, viewMatrix );
	#else
		vec3 shadowWorldNormal = vec3( 0.0 );
	#endif
	vec4 shadowWorldPosition;
#endif
#if defined( USE_SHADOWMAP )
	#if NUM_SUN_LIGHT_SHADOWS > 0
		vSunShadowWorldPosition = vec4( worldPosition.xyz, - mvPosition.z );
		vSunShadowWorldNormal = shadowWorldNormal;
	#endif
	#if NUM_DIR_LIGHT_SHADOWS > 0
		#pragma unroll_loop_start
		for ( int i = 0; i < NUM_DIR_LIGHT_SHADOWS; i ++ ) {
			shadowWorldPosition = worldPosition + vec4( shadowWorldNormal * directionalLightShadows[ i ].shadowNormalBias, 0 );
			vDirectionalShadowCoord[ i ] = directionalShadowMatrix[ i ] * shadowWorldPosition;
		}
		#pragma unroll_loop_end
	#endif
	#if NUM_POINT_LIGHT_SHADOWS > 0
		#pragma unroll_loop_start
		for ( int i = 0; i < NUM_POINT_LIGHT_SHADOWS; i ++ ) {
			shadowWorldPosition = worldPosition + vec4( shadowWorldNormal * pointLightShadows[ i ].shadowNormalBias, 0 );
			vPointShadowCoord[ i ] = pointShadowMatrix[ i ] * shadowWorldPosition;
		}
		#pragma unroll_loop_end
	#endif
#endif
#if NUM_SPOT_LIGHT_COORDS > 0
	#pragma unroll_loop_start
	for ( int i = 0; i < NUM_SPOT_LIGHT_COORDS; i ++ ) {
		shadowWorldPosition = worldPosition;
		#if ( defined( USE_SHADOWMAP ) && UNROLLED_LOOP_INDEX < NUM_SPOT_LIGHT_SHADOWS )
			shadowWorldPosition.xyz += shadowWorldNormal * spotLightShadows[ i ].shadowNormalBias;
		#endif
		vSpotLightCoord[ i ] = spotLightMatrix[ i ] * shadowWorldPosition;
	}
	#pragma unroll_loop_end
#endif`,Gd=`float getShadowMask() {
	float shadow = 1.0;
	#ifdef USE_SHADOWMAP
	#if NUM_SUN_LIGHT_SHADOWS > 0
	SunLightShadow sunLight;
	#pragma unroll_loop_start
	for ( int i = 0; i < NUM_SUN_LIGHT_SHADOWS; i ++ ) {
		sunLight = sunLightShadows[ i ];
		shadow *= receiveShadow ? getSunShadow( sunShadowMap[ i ], sunLight, UNROLLED_LOOP_INDEX ) : 1.0;
	}
	#pragma unroll_loop_end
	#endif
	#if NUM_DIR_LIGHT_SHADOWS > 0
	DirectionalLightShadow directionalLight;
	#pragma unroll_loop_start
	for ( int i = 0; i < NUM_DIR_LIGHT_SHADOWS; i ++ ) {
		directionalLight = directionalLightShadows[ i ];
		shadow *= receiveShadow ? getShadow( directionalShadowMap[ i ], directionalLight.shadowMapSize, directionalLight.shadowIntensity, directionalLight.shadowBias, directionalLight.shadowRadius, vDirectionalShadowCoord[ i ] ) : 1.0;
	}
	#pragma unroll_loop_end
	#endif
	#if NUM_SPOT_LIGHT_SHADOWS > 0
	SpotLightShadow spotLight;
	#pragma unroll_loop_start
	for ( int i = 0; i < NUM_SPOT_LIGHT_SHADOWS; i ++ ) {
		spotLight = spotLightShadows[ i ];
		shadow *= receiveShadow ? getShadow( spotShadowMap[ i ], spotLight.shadowMapSize, spotLight.shadowIntensity, spotLight.shadowBias, spotLight.shadowRadius, vSpotLightCoord[ i ] ) : 1.0;
	}
	#pragma unroll_loop_end
	#endif
	#if NUM_POINT_LIGHT_SHADOWS > 0 && ( defined( SHADOWMAP_TYPE_PCF ) || defined( SHADOWMAP_TYPE_BASIC ) )
	PointLightShadow pointLight;
	#pragma unroll_loop_start
	for ( int i = 0; i < NUM_POINT_LIGHT_SHADOWS; i ++ ) {
		pointLight = pointLightShadows[ i ];
		shadow *= receiveShadow ? getPointShadow( pointShadowMap[ i ], pointLight.shadowMapSize, pointLight.shadowIntensity, pointLight.shadowBias, pointLight.shadowRadius, vPointShadowCoord[ i ], pointLight.shadowCameraNear, pointLight.shadowCameraFar ) : 1.0;
	}
	#pragma unroll_loop_end
	#endif
	#endif
	return shadow;
}`,Hd=`#ifdef USE_SKINNING
	mat4 boneMatX = getBoneMatrix( skinIndex.x );
	mat4 boneMatY = getBoneMatrix( skinIndex.y );
	mat4 boneMatZ = getBoneMatrix( skinIndex.z );
	mat4 boneMatW = getBoneMatrix( skinIndex.w );
#endif`,Wd=`#ifdef USE_SKINNING
	uniform mat4 bindMatrix;
	uniform mat4 bindMatrixInverse;
	uniform highp sampler2D boneTexture;
	mat4 getBoneMatrix( const in float i ) {
		int size = textureSize( boneTexture, 0 ).x;
		int j = int( i ) * 4;
		int x = j % size;
		int y = j / size;
		vec4 v1 = texelFetch( boneTexture, ivec2( x, y ), 0 );
		vec4 v2 = texelFetch( boneTexture, ivec2( x + 1, y ), 0 );
		vec4 v3 = texelFetch( boneTexture, ivec2( x + 2, y ), 0 );
		vec4 v4 = texelFetch( boneTexture, ivec2( x + 3, y ), 0 );
		return mat4( v1, v2, v3, v4 );
	}
#endif`,Xd=`#ifdef USE_SKINNING
	vec4 skinVertex = bindMatrix * vec4( transformed, 1.0 );
	vec4 skinned = vec4( 0.0 );
	skinned += boneMatX * skinVertex * skinWeight.x;
	skinned += boneMatY * skinVertex * skinWeight.y;
	skinned += boneMatZ * skinVertex * skinWeight.z;
	skinned += boneMatW * skinVertex * skinWeight.w;
	transformed = ( bindMatrixInverse * skinned ).xyz;
#endif`,qd=`#ifdef USE_SKINNING
	mat4 skinMatrix = mat4( 0.0 );
	skinMatrix += skinWeight.x * boneMatX;
	skinMatrix += skinWeight.y * boneMatY;
	skinMatrix += skinWeight.z * boneMatZ;
	skinMatrix += skinWeight.w * boneMatW;
	skinMatrix = bindMatrixInverse * skinMatrix * bindMatrix;
	objectNormal = vec4( skinMatrix * vec4( objectNormal, 0.0 ) ).xyz;
	#ifdef USE_TANGENT
		objectTangent = vec4( skinMatrix * vec4( objectTangent, 0.0 ) ).xyz;
	#endif
#endif`,Kd=`float specularStrength;
#ifdef USE_SPECULARMAP
	vec4 texelSpecular = texture2D( specularMap, vSpecularMapUv );
	specularStrength = texelSpecular.r;
#else
	specularStrength = 1.0;
#endif`,Yd=`#ifdef USE_SPECULARMAP
	uniform sampler2D specularMap;
#endif`,jd=`#if defined( TONE_MAPPING )
	gl_FragColor.rgb = toneMapping( gl_FragColor.rgb );
#endif`,Jd=`#ifndef saturate
#define saturate( a ) clamp( a, 0.0, 1.0 )
#endif
uniform float toneMappingExposure;
vec3 LinearToneMapping( vec3 color ) {
	return saturate( toneMappingExposure * color );
}
vec3 ReinhardToneMapping( vec3 color ) {
	color *= toneMappingExposure;
	return saturate( color / ( vec3( 1.0 ) + color ) );
}
vec3 CineonToneMapping( vec3 color ) {
	color *= toneMappingExposure;
	color = max( vec3( 0.0 ), color - 0.004 );
	return pow( ( color * ( 6.2 * color + 0.5 ) ) / ( color * ( 6.2 * color + 1.7 ) + 0.06 ), vec3( 2.2 ) );
}
vec3 RRTAndODTFit( vec3 v ) {
	vec3 a = v * ( v + 0.0245786 ) - 0.000090537;
	vec3 b = v * ( 0.983729 * v + 0.4329510 ) + 0.238081;
	return a / b;
}
vec3 ACESFilmicToneMapping( vec3 color ) {
	const mat3 ACESInputMat = mat3(
		vec3( 0.59719, 0.07600, 0.02840 ),		vec3( 0.35458, 0.90834, 0.13383 ),
		vec3( 0.04823, 0.01566, 0.83777 )
	);
	const mat3 ACESOutputMat = mat3(
		vec3(  1.60475, -0.10208, -0.00327 ),		vec3( -0.53108,  1.10813, -0.07276 ),
		vec3( -0.07367, -0.00605,  1.07602 )
	);
	color *= toneMappingExposure / 0.6;
	color = ACESInputMat * color;
	color = RRTAndODTFit( color );
	color = ACESOutputMat * color;
	return saturate( color );
}
const mat3 LINEAR_REC2020_TO_LINEAR_SRGB = mat3(
	vec3( 1.6605, - 0.1246, - 0.0182 ),
	vec3( - 0.5876, 1.1329, - 0.1006 ),
	vec3( - 0.0728, - 0.0083, 1.1187 )
);
const mat3 LINEAR_SRGB_TO_LINEAR_REC2020 = mat3(
	vec3( 0.6274, 0.0691, 0.0164 ),
	vec3( 0.3293, 0.9195, 0.0880 ),
	vec3( 0.0433, 0.0113, 0.8956 )
);
vec3 agxDefaultContrastApprox( vec3 x ) {
	vec3 x2 = x * x;
	vec3 x4 = x2 * x2;
	return + 15.5 * x4 * x2
		- 40.14 * x4 * x
		+ 31.96 * x4
		- 6.868 * x2 * x
		+ 0.4298 * x2
		+ 0.1191 * x
		- 0.00232;
}
vec3 AgXToneMapping( vec3 color ) {
	const mat3 AgXInsetMatrix = mat3(
		vec3( 0.856627153315983, 0.137318972929847, 0.11189821299995 ),
		vec3( 0.0951212405381588, 0.761241990602591, 0.0767994186031903 ),
		vec3( 0.0482516061458583, 0.101439036467562, 0.811302368396859 )
	);
	const mat3 AgXOutsetMatrix = mat3(
		vec3( 1.1271005818144368, - 0.1413297634984383, - 0.14132976349843826 ),
		vec3( - 0.11060664309660323, 1.157823702216272, - 0.11060664309660294 ),
		vec3( - 0.016493938717834573, - 0.016493938717834257, 1.2519364065950405 )
	);
	const float AgxMinEv = - 12.47393;	const float AgxMaxEv = 4.026069;
	color *= toneMappingExposure;
	color = LINEAR_SRGB_TO_LINEAR_REC2020 * color;
	color = AgXInsetMatrix * color;
	color = max( color, 1e-10 );	color = log2( color );
	color = ( color - AgxMinEv ) / ( AgxMaxEv - AgxMinEv );
	color = clamp( color, 0.0, 1.0 );
	color = agxDefaultContrastApprox( color );
	color = AgXOutsetMatrix * color;
	color = pow( max( vec3( 0.0 ), color ), vec3( 2.2 ) );
	color = LINEAR_REC2020_TO_LINEAR_SRGB * color;
	color = clamp( color, 0.0, 1.0 );
	return color;
}
vec3 NeutralToneMapping( vec3 color ) {
	const float StartCompression = 0.8 - 0.04;
	const float Desaturation = 0.15;
	color *= toneMappingExposure;
	float x = min( color.r, min( color.g, color.b ) );
	float offset = x < 0.08 ? x - 6.25 * x * x : 0.04;
	color -= offset;
	float peak = max( color.r, max( color.g, color.b ) );
	if ( peak < StartCompression ) return color;
	float d = 1. - StartCompression;
	float newPeak = 1. - d * d / ( peak + d - StartCompression );
	color *= newPeak / peak;
	float g = 1. - 1. / ( Desaturation * ( peak - newPeak ) + 1. );
	return mix( color, vec3( newPeak ), g );
}
vec3 CustomToneMapping( vec3 color ) { return color; }`,Zd=`#ifdef USE_TRANSMISSION
	material.transmission = transmission;
	material.transmissionAlpha = 1.0;
	material.thickness = thickness;
	material.attenuationDistance = attenuationDistance;
	material.attenuationColor = attenuationColor;
	#ifdef USE_TRANSMISSIONMAP
		material.transmission *= texture2D( transmissionMap, vTransmissionMapUv ).r;
	#endif
	#ifdef USE_THICKNESSMAP
		material.thickness *= texture2D( thicknessMap, vThicknessMapUv ).g;
	#endif
	vec3 pos = vWorldPosition;
	vec3 v = normalize( cameraPosition - pos );
	vec3 n = transformNormalByInverseViewMatrix( normal, viewMatrix );
	vec4 transmitted = getIBLVolumeRefraction(
		n, v, material.roughness, material.diffuseContribution, material.specularColorBlended, material.specularF90,
		pos, modelMatrix, viewMatrix, projectionMatrix, material.dispersion, material.ior, material.thickness,
		material.attenuationColor, material.attenuationDistance );
	material.transmissionAlpha = mix( material.transmissionAlpha, transmitted.a, material.transmission );
	totalDiffuse = mix( totalDiffuse, transmitted.rgb, material.transmission );
#endif`,$d=`#ifdef USE_TRANSMISSION
	uniform float transmission;
	uniform float thickness;
	uniform float attenuationDistance;
	uniform vec3 attenuationColor;
	#ifdef USE_TRANSMISSIONMAP
		uniform sampler2D transmissionMap;
	#endif
	#ifdef USE_THICKNESSMAP
		uniform sampler2D thicknessMap;
	#endif
	uniform vec2 transmissionSamplerSize;
	uniform sampler2D transmissionSamplerMap;
	uniform mat4 modelMatrix;
	uniform mat4 projectionMatrix;
	varying vec3 vWorldPosition;
	float w0( float a ) {
		return ( 1.0 / 6.0 ) * ( a * ( a * ( - a + 3.0 ) - 3.0 ) + 1.0 );
	}
	float w1( float a ) {
		return ( 1.0 / 6.0 ) * ( a *  a * ( 3.0 * a - 6.0 ) + 4.0 );
	}
	float w2( float a ){
		return ( 1.0 / 6.0 ) * ( a * ( a * ( - 3.0 * a + 3.0 ) + 3.0 ) + 1.0 );
	}
	float w3( float a ) {
		return ( 1.0 / 6.0 ) * ( a * a * a );
	}
	float g0( float a ) {
		return w0( a ) + w1( a );
	}
	float g1( float a ) {
		return w2( a ) + w3( a );
	}
	float h0( float a ) {
		return - 1.0 + w1( a ) / ( w0( a ) + w1( a ) );
	}
	float h1( float a ) {
		return 1.0 + w3( a ) / ( w2( a ) + w3( a ) );
	}
	vec4 bicubic( sampler2D tex, vec2 uv, vec4 texelSize, float lod ) {
		uv = uv * texelSize.zw + 0.5;
		vec2 iuv = floor( uv );
		vec2 fuv = fract( uv );
		float g0x = g0( fuv.x );
		float g1x = g1( fuv.x );
		float h0x = h0( fuv.x );
		float h1x = h1( fuv.x );
		float h0y = h0( fuv.y );
		float h1y = h1( fuv.y );
		vec2 p0 = ( vec2( iuv.x + h0x, iuv.y + h0y ) - 0.5 ) * texelSize.xy;
		vec2 p1 = ( vec2( iuv.x + h1x, iuv.y + h0y ) - 0.5 ) * texelSize.xy;
		vec2 p2 = ( vec2( iuv.x + h0x, iuv.y + h1y ) - 0.5 ) * texelSize.xy;
		vec2 p3 = ( vec2( iuv.x + h1x, iuv.y + h1y ) - 0.5 ) * texelSize.xy;
		return g0( fuv.y ) * ( g0x * textureLod( tex, p0, lod ) + g1x * textureLod( tex, p1, lod ) ) +
			g1( fuv.y ) * ( g0x * textureLod( tex, p2, lod ) + g1x * textureLod( tex, p3, lod ) );
	}
	vec4 textureBicubic( sampler2D sampler, vec2 uv, float lod ) {
		vec2 fLodSize = vec2( textureSize( sampler, int( lod ) ) );
		vec2 cLodSize = vec2( textureSize( sampler, int( lod + 1.0 ) ) );
		vec2 fLodSizeInv = 1.0 / fLodSize;
		vec2 cLodSizeInv = 1.0 / cLodSize;
		vec4 fSample = bicubic( sampler, uv, vec4( fLodSizeInv, fLodSize ), floor( lod ) );
		vec4 cSample = bicubic( sampler, uv, vec4( cLodSizeInv, cLodSize ), ceil( lod ) );
		return mix( fSample, cSample, fract( lod ) );
	}
	vec3 getVolumeTransmissionRay( const in vec3 n, const in vec3 v, const in float thickness, const in float ior, const in mat4 modelMatrix ) {
		vec3 refractionVector = refract( - v, normalize( n ), 1.0 / ior );
		vec3 modelScale;
		modelScale.x = length( vec3( modelMatrix[ 0 ].xyz ) );
		modelScale.y = length( vec3( modelMatrix[ 1 ].xyz ) );
		modelScale.z = length( vec3( modelMatrix[ 2 ].xyz ) );
		return normalize( refractionVector ) * thickness * modelScale;
	}
	float applyIorToRoughness( const in float roughness, const in float ior ) {
		return roughness * clamp( ior * 2.0 - 2.0, 0.0, 1.0 );
	}
	vec4 getTransmissionSample( const in vec2 fragCoord, const in float roughness, const in float ior ) {
		float lod = log2( transmissionSamplerSize.x ) * applyIorToRoughness( roughness, ior );
		return textureBicubic( transmissionSamplerMap, fragCoord.xy, lod );
	}
	vec3 volumeAttenuation( const in float transmissionDistance, const in vec3 attenuationColor, const in float attenuationDistance ) {
		if ( isinf( attenuationDistance ) ) {
			return vec3( 1.0 );
		} else {
			vec3 attenuationCoefficient = -log( attenuationColor ) / attenuationDistance;
			vec3 transmittance = exp( - attenuationCoefficient * transmissionDistance );			return transmittance;
		}
	}
	vec4 getIBLVolumeRefraction( const in vec3 n, const in vec3 v, const in float roughness, const in vec3 diffuseColor,
		const in vec3 specularColor, const in float specularF90, const in vec3 position, const in mat4 modelMatrix,
		const in mat4 viewMatrix, const in mat4 projMatrix, const in float dispersion, const in float ior, const in float thickness,
		const in vec3 attenuationColor, const in float attenuationDistance ) {
		vec4 transmittedLight;
		vec3 transmittance;
		#ifdef USE_DISPERSION
			float halfSpread = ( ior - 1.0 ) * 0.025 * dispersion;
			vec3 iors = vec3( ior - halfSpread, ior, ior + halfSpread );
			for ( int i = 0; i < 3; i ++ ) {
				vec3 transmissionRay = getVolumeTransmissionRay( n, v, thickness, iors[ i ], modelMatrix );
				vec3 refractedRayExit = position + transmissionRay;
				vec4 ndcPos = projMatrix * viewMatrix * vec4( refractedRayExit, 1.0 );
				vec2 refractionCoords = ndcPos.xy / ndcPos.w;
				refractionCoords += 1.0;
				refractionCoords /= 2.0;
				vec4 transmissionSample = getTransmissionSample( refractionCoords, roughness, iors[ i ] );
				transmittedLight[ i ] = transmissionSample[ i ];
				transmittedLight.a += transmissionSample.a;
				transmittance[ i ] = diffuseColor[ i ] * volumeAttenuation( length( transmissionRay ), attenuationColor, attenuationDistance )[ i ];
			}
			transmittedLight.a /= 3.0;
		#else
			vec3 transmissionRay = getVolumeTransmissionRay( n, v, thickness, ior, modelMatrix );
			vec3 refractedRayExit = position + transmissionRay;
			vec4 ndcPos = projMatrix * viewMatrix * vec4( refractedRayExit, 1.0 );
			vec2 refractionCoords = ndcPos.xy / ndcPos.w;
			refractionCoords += 1.0;
			refractionCoords /= 2.0;
			transmittedLight = getTransmissionSample( refractionCoords, roughness, ior );
			transmittance = diffuseColor * volumeAttenuation( length( transmissionRay ), attenuationColor, attenuationDistance );
		#endif
		vec3 attenuatedColor = transmittance * transmittedLight.rgb;
		vec3 F = EnvironmentBRDF( n, v, specularColor, specularF90, roughness );
		float transmittanceFactor = ( transmittance.r + transmittance.g + transmittance.b ) / 3.0;
		return vec4( ( 1.0 - F ) * attenuatedColor, 1.0 - ( 1.0 - transmittedLight.a ) * transmittanceFactor );
	}
#endif`,Qd=`#if defined( USE_UV ) || defined( USE_ANISOTROPY )
	varying vec2 vUv;
#endif
#ifdef USE_MAP
	varying vec2 vMapUv;
#endif
#ifdef USE_ALPHAMAP
	varying vec2 vAlphaMapUv;
#endif
#ifdef USE_LIGHTMAP
	varying vec2 vLightMapUv;
#endif
#ifdef USE_AOMAP
	varying vec2 vAoMapUv;
#endif
#ifdef USE_BUMPMAP
	varying vec2 vBumpMapUv;
#endif
#ifdef USE_NORMALMAP
	varying vec2 vNormalMapUv;
#endif
#ifdef USE_EMISSIVEMAP
	varying vec2 vEmissiveMapUv;
#endif
#ifdef USE_METALNESSMAP
	varying vec2 vMetalnessMapUv;
#endif
#ifdef USE_ROUGHNESSMAP
	varying vec2 vRoughnessMapUv;
#endif
#ifdef USE_ANISOTROPYMAP
	varying vec2 vAnisotropyMapUv;
#endif
#ifdef USE_CLEARCOATMAP
	varying vec2 vClearcoatMapUv;
#endif
#ifdef USE_CLEARCOAT_NORMALMAP
	varying vec2 vClearcoatNormalMapUv;
#endif
#ifdef USE_CLEARCOAT_ROUGHNESSMAP
	varying vec2 vClearcoatRoughnessMapUv;
#endif
#ifdef USE_IRIDESCENCEMAP
	varying vec2 vIridescenceMapUv;
#endif
#ifdef USE_IRIDESCENCE_THICKNESSMAP
	varying vec2 vIridescenceThicknessMapUv;
#endif
#ifdef USE_SHEEN_COLORMAP
	varying vec2 vSheenColorMapUv;
#endif
#ifdef USE_SHEEN_ROUGHNESSMAP
	varying vec2 vSheenRoughnessMapUv;
#endif
#ifdef USE_SPECULARMAP
	varying vec2 vSpecularMapUv;
#endif
#ifdef USE_SPECULAR_COLORMAP
	varying vec2 vSpecularColorMapUv;
#endif
#ifdef USE_SPECULAR_INTENSITYMAP
	varying vec2 vSpecularIntensityMapUv;
#endif
#ifdef USE_TRANSMISSIONMAP
	uniform mat3 transmissionMapTransform;
	varying vec2 vTransmissionMapUv;
#endif
#ifdef USE_THICKNESSMAP
	uniform mat3 thicknessMapTransform;
	varying vec2 vThicknessMapUv;
#endif`,ep=`#if defined( USE_UV ) || defined( USE_ANISOTROPY )
	varying vec2 vUv;
#endif
#ifdef USE_MAP
	uniform mat3 mapTransform;
	varying vec2 vMapUv;
#endif
#ifdef USE_ALPHAMAP
	uniform mat3 alphaMapTransform;
	varying vec2 vAlphaMapUv;
#endif
#ifdef USE_LIGHTMAP
	uniform mat3 lightMapTransform;
	varying vec2 vLightMapUv;
#endif
#ifdef USE_AOMAP
	uniform mat3 aoMapTransform;
	varying vec2 vAoMapUv;
#endif
#ifdef USE_BUMPMAP
	uniform mat3 bumpMapTransform;
	varying vec2 vBumpMapUv;
#endif
#ifdef USE_NORMALMAP
	uniform mat3 normalMapTransform;
	varying vec2 vNormalMapUv;
#endif
#ifdef USE_DISPLACEMENTMAP
	uniform mat3 displacementMapTransform;
	varying vec2 vDisplacementMapUv;
#endif
#ifdef USE_EMISSIVEMAP
	uniform mat3 emissiveMapTransform;
	varying vec2 vEmissiveMapUv;
#endif
#ifdef USE_METALNESSMAP
	uniform mat3 metalnessMapTransform;
	varying vec2 vMetalnessMapUv;
#endif
#ifdef USE_ROUGHNESSMAP
	uniform mat3 roughnessMapTransform;
	varying vec2 vRoughnessMapUv;
#endif
#ifdef USE_ANISOTROPYMAP
	uniform mat3 anisotropyMapTransform;
	varying vec2 vAnisotropyMapUv;
#endif
#ifdef USE_CLEARCOATMAP
	uniform mat3 clearcoatMapTransform;
	varying vec2 vClearcoatMapUv;
#endif
#ifdef USE_CLEARCOAT_NORMALMAP
	uniform mat3 clearcoatNormalMapTransform;
	varying vec2 vClearcoatNormalMapUv;
#endif
#ifdef USE_CLEARCOAT_ROUGHNESSMAP
	uniform mat3 clearcoatRoughnessMapTransform;
	varying vec2 vClearcoatRoughnessMapUv;
#endif
#ifdef USE_SHEEN_COLORMAP
	uniform mat3 sheenColorMapTransform;
	varying vec2 vSheenColorMapUv;
#endif
#ifdef USE_SHEEN_ROUGHNESSMAP
	uniform mat3 sheenRoughnessMapTransform;
	varying vec2 vSheenRoughnessMapUv;
#endif
#ifdef USE_IRIDESCENCEMAP
	uniform mat3 iridescenceMapTransform;
	varying vec2 vIridescenceMapUv;
#endif
#ifdef USE_IRIDESCENCE_THICKNESSMAP
	uniform mat3 iridescenceThicknessMapTransform;
	varying vec2 vIridescenceThicknessMapUv;
#endif
#ifdef USE_SPECULARMAP
	uniform mat3 specularMapTransform;
	varying vec2 vSpecularMapUv;
#endif
#ifdef USE_SPECULAR_COLORMAP
	uniform mat3 specularColorMapTransform;
	varying vec2 vSpecularColorMapUv;
#endif
#ifdef USE_SPECULAR_INTENSITYMAP
	uniform mat3 specularIntensityMapTransform;
	varying vec2 vSpecularIntensityMapUv;
#endif
#ifdef USE_TRANSMISSIONMAP
	uniform mat3 transmissionMapTransform;
	varying vec2 vTransmissionMapUv;
#endif
#ifdef USE_THICKNESSMAP
	uniform mat3 thicknessMapTransform;
	varying vec2 vThicknessMapUv;
#endif`,tp=`#if defined( USE_UV ) || defined( USE_ANISOTROPY )
	vUv = vec3( uv, 1 ).xy;
#endif
#ifdef USE_MAP
	vMapUv = ( mapTransform * vec3( MAP_UV, 1 ) ).xy;
#endif
#ifdef USE_ALPHAMAP
	vAlphaMapUv = ( alphaMapTransform * vec3( ALPHAMAP_UV, 1 ) ).xy;
#endif
#ifdef USE_LIGHTMAP
	vLightMapUv = ( lightMapTransform * vec3( LIGHTMAP_UV, 1 ) ).xy;
#endif
#ifdef USE_AOMAP
	vAoMapUv = ( aoMapTransform * vec3( AOMAP_UV, 1 ) ).xy;
#endif
#ifdef USE_BUMPMAP
	vBumpMapUv = ( bumpMapTransform * vec3( BUMPMAP_UV, 1 ) ).xy;
#endif
#ifdef USE_NORMALMAP
	vNormalMapUv = ( normalMapTransform * vec3( NORMALMAP_UV, 1 ) ).xy;
#endif
#ifdef USE_DISPLACEMENTMAP
	vDisplacementMapUv = ( displacementMapTransform * vec3( DISPLACEMENTMAP_UV, 1 ) ).xy;
#endif
#ifdef USE_EMISSIVEMAP
	vEmissiveMapUv = ( emissiveMapTransform * vec3( EMISSIVEMAP_UV, 1 ) ).xy;
#endif
#ifdef USE_METALNESSMAP
	vMetalnessMapUv = ( metalnessMapTransform * vec3( METALNESSMAP_UV, 1 ) ).xy;
#endif
#ifdef USE_ROUGHNESSMAP
	vRoughnessMapUv = ( roughnessMapTransform * vec3( ROUGHNESSMAP_UV, 1 ) ).xy;
#endif
#ifdef USE_ANISOTROPYMAP
	vAnisotropyMapUv = ( anisotropyMapTransform * vec3( ANISOTROPYMAP_UV, 1 ) ).xy;
#endif
#ifdef USE_CLEARCOATMAP
	vClearcoatMapUv = ( clearcoatMapTransform * vec3( CLEARCOATMAP_UV, 1 ) ).xy;
#endif
#ifdef USE_CLEARCOAT_NORMALMAP
	vClearcoatNormalMapUv = ( clearcoatNormalMapTransform * vec3( CLEARCOAT_NORMALMAP_UV, 1 ) ).xy;
#endif
#ifdef USE_CLEARCOAT_ROUGHNESSMAP
	vClearcoatRoughnessMapUv = ( clearcoatRoughnessMapTransform * vec3( CLEARCOAT_ROUGHNESSMAP_UV, 1 ) ).xy;
#endif
#ifdef USE_IRIDESCENCEMAP
	vIridescenceMapUv = ( iridescenceMapTransform * vec3( IRIDESCENCEMAP_UV, 1 ) ).xy;
#endif
#ifdef USE_IRIDESCENCE_THICKNESSMAP
	vIridescenceThicknessMapUv = ( iridescenceThicknessMapTransform * vec3( IRIDESCENCE_THICKNESSMAP_UV, 1 ) ).xy;
#endif
#ifdef USE_SHEEN_COLORMAP
	vSheenColorMapUv = ( sheenColorMapTransform * vec3( SHEEN_COLORMAP_UV, 1 ) ).xy;
#endif
#ifdef USE_SHEEN_ROUGHNESSMAP
	vSheenRoughnessMapUv = ( sheenRoughnessMapTransform * vec3( SHEEN_ROUGHNESSMAP_UV, 1 ) ).xy;
#endif
#ifdef USE_SPECULARMAP
	vSpecularMapUv = ( specularMapTransform * vec3( SPECULARMAP_UV, 1 ) ).xy;
#endif
#ifdef USE_SPECULAR_COLORMAP
	vSpecularColorMapUv = ( specularColorMapTransform * vec3( SPECULAR_COLORMAP_UV, 1 ) ).xy;
#endif
#ifdef USE_SPECULAR_INTENSITYMAP
	vSpecularIntensityMapUv = ( specularIntensityMapTransform * vec3( SPECULAR_INTENSITYMAP_UV, 1 ) ).xy;
#endif
#ifdef USE_TRANSMISSIONMAP
	vTransmissionMapUv = ( transmissionMapTransform * vec3( TRANSMISSIONMAP_UV, 1 ) ).xy;
#endif
#ifdef USE_THICKNESSMAP
	vThicknessMapUv = ( thicknessMapTransform * vec3( THICKNESSMAP_UV, 1 ) ).xy;
#endif`,np=`#if defined( USE_ENVMAP ) || defined( DISTANCE ) || defined ( USE_SHADOWMAP ) || defined ( USE_TRANSMISSION ) || NUM_SPOT_LIGHT_COORDS > 0
	vec4 worldPosition = vec4( transformed, 1.0 );
	#ifdef USE_BATCHING
		worldPosition = batchingMatrix * worldPosition;
	#endif
	#ifdef USE_INSTANCING
		worldPosition = instanceMatrix * worldPosition;
	#endif
	worldPosition = modelMatrix * worldPosition;
#endif`,ip=`varying vec2 vUv;
uniform mat3 uvTransform;
void main() {
	vUv = ( uvTransform * vec3( uv, 1 ) ).xy;
	gl_Position = vec4( position.xy, 1.0, 1.0 );
}`,sp=`uniform sampler2D t2D;
uniform float backgroundIntensity;
varying vec2 vUv;
void main() {
	vec4 texColor = texture2D( t2D, vUv );
	#ifdef DECODE_VIDEO_TEXTURE
		texColor = vec4( mix( pow( texColor.rgb * 0.9478672986 + vec3( 0.0521327014 ), vec3( 2.4 ) ), texColor.rgb * 0.0773993808, vec3( lessThanEqual( texColor.rgb, vec3( 0.04045 ) ) ) ), texColor.w );
	#endif
	texColor.rgb *= backgroundIntensity;
	gl_FragColor = texColor;
	#include <tonemapping_fragment>
	#include <colorspace_fragment>
}`,rp=`varying vec3 vWorldDirection;
#include <common>
void main() {
	vWorldDirection = transformDirection( position, modelMatrix );
	#include <begin_vertex>
	#include <project_vertex>
	gl_Position.z = gl_Position.w;
}`,ap=`#ifdef ENVMAP_TYPE_CUBE
	uniform samplerCube envMap;
#elif defined( ENVMAP_TYPE_CUBE_UV )
	uniform sampler2D envMap;
#endif
uniform float backgroundBlurriness;
uniform float backgroundIntensity;
uniform mat3 backgroundRotation;
varying vec3 vWorldDirection;
#include <cube_uv_reflection_fragment>
void main() {
	#ifdef ENVMAP_TYPE_CUBE
		vec4 texColor = textureCube( envMap, backgroundRotation * vWorldDirection );
	#elif defined( ENVMAP_TYPE_CUBE_UV )
		vec4 texColor = textureCubeUV( envMap, backgroundRotation * vWorldDirection, backgroundBlurriness );
	#else
		vec4 texColor = vec4( 0.0, 0.0, 0.0, 1.0 );
	#endif
	texColor.rgb *= backgroundIntensity;
	gl_FragColor = texColor;
	#include <tonemapping_fragment>
	#include <colorspace_fragment>
}`,op=`varying vec3 vWorldDirection;
#include <common>
void main() {
	vWorldDirection = transformDirection( position, modelMatrix );
	#include <begin_vertex>
	#include <project_vertex>
	gl_Position.z = gl_Position.w;
}`,cp=`uniform samplerCube tCube;
uniform float tFlip;
uniform float opacity;
varying vec3 vWorldDirection;
void main() {
	vec4 texColor = textureCube( tCube, vec3( tFlip * vWorldDirection.x, vWorldDirection.yz ) );
	gl_FragColor = texColor;
	gl_FragColor.a *= opacity;
	#include <tonemapping_fragment>
	#include <colorspace_fragment>
}`,lp=`#include <common>
#include <batching_pars_vertex>
#include <uv_pars_vertex>
#include <displacementmap_pars_vertex>
#include <morphtarget_pars_vertex>
#include <skinning_pars_vertex>
#include <logdepthbuf_pars_vertex>
#include <clipping_planes_pars_vertex>
varying vec2 vHighPrecisionZW;
void main() {
	#include <uv_vertex>
	#include <batching_vertex>
	#include <skinbase_vertex>
	#include <morphinstance_vertex>
	#ifdef USE_DISPLACEMENTMAP
		#include <beginnormal_vertex>
		#include <morphnormal_vertex>
		#include <skinnormal_vertex>
	#endif
	#include <begin_vertex>
	#include <morphtarget_vertex>
	#include <skinning_vertex>
	#include <displacementmap_vertex>
	#include <project_vertex>
	#include <logdepthbuf_vertex>
	#include <clipping_planes_vertex>
	vHighPrecisionZW = gl_Position.zw;
}`,up=`#if DEPTH_PACKING == 3200
	uniform float opacity;
#endif
#include <common>
#include <packing>
#include <uv_pars_fragment>
#include <map_pars_fragment>
#include <alphamap_pars_fragment>
#include <alphatest_pars_fragment>
#include <alphahash_pars_fragment>
#include <logdepthbuf_pars_fragment>
#include <clipping_planes_pars_fragment>
varying vec2 vHighPrecisionZW;
void main() {
	vec4 diffuseColor = vec4( 1.0 );
	#include <clipping_planes_fragment>
	#if DEPTH_PACKING == 3200
		diffuseColor.a = opacity;
	#endif
	#include <map_fragment>
	#include <alphamap_fragment>
	#include <alphatest_fragment>
	#include <alphahash_fragment>
	#include <logdepthbuf_fragment>
	#ifdef USE_REVERSED_DEPTH_BUFFER
		float fragCoordZ = vHighPrecisionZW[ 0 ] / vHighPrecisionZW[ 1 ];
	#else
		float fragCoordZ = 0.5 * vHighPrecisionZW[ 0 ] / vHighPrecisionZW[ 1 ] + 0.5;
	#endif
	#if DEPTH_PACKING == 3200
		gl_FragColor = vec4( vec3( 1.0 - fragCoordZ ), opacity );
	#elif DEPTH_PACKING == 3201
		gl_FragColor = packDepthToRGBA( fragCoordZ );
	#elif DEPTH_PACKING == 3202
		gl_FragColor = vec4( packDepthToRGB( fragCoordZ ), 1.0 );
	#elif DEPTH_PACKING == 3203
		gl_FragColor = vec4( packDepthToRG( fragCoordZ ), 0.0, 1.0 );
	#endif
}`,hp=`#define DISTANCE
varying vec3 vWorldPosition;
#include <common>
#include <batching_pars_vertex>
#include <uv_pars_vertex>
#include <displacementmap_pars_vertex>
#include <morphtarget_pars_vertex>
#include <skinning_pars_vertex>
#include <clipping_planes_pars_vertex>
void main() {
	#include <uv_vertex>
	#include <batching_vertex>
	#include <skinbase_vertex>
	#include <morphinstance_vertex>
	#ifdef USE_DISPLACEMENTMAP
		#include <beginnormal_vertex>
		#include <morphnormal_vertex>
		#include <skinnormal_vertex>
	#endif
	#include <begin_vertex>
	#include <morphtarget_vertex>
	#include <skinning_vertex>
	#include <displacementmap_vertex>
	#include <project_vertex>
	#include <worldpos_vertex>
	#include <clipping_planes_vertex>
	vWorldPosition = worldPosition.xyz;
}`,fp=`#define DISTANCE
uniform vec3 referencePosition;
uniform float nearDistance;
uniform float farDistance;
varying vec3 vWorldPosition;
#include <common>
#include <uv_pars_fragment>
#include <map_pars_fragment>
#include <alphamap_pars_fragment>
#include <alphatest_pars_fragment>
#include <alphahash_pars_fragment>
#include <clipping_planes_pars_fragment>
void main() {
	vec4 diffuseColor = vec4( 1.0 );
	#include <clipping_planes_fragment>
	#include <map_fragment>
	#include <alphamap_fragment>
	#include <alphatest_fragment>
	#include <alphahash_fragment>
	float dist = length( vWorldPosition - referencePosition );
	dist = ( dist - nearDistance ) / ( farDistance - nearDistance );
	dist = saturate( dist );
	gl_FragColor = vec4( dist, 0.0, 0.0, 1.0 );
}`,dp=`varying vec3 vWorldDirection;
#include <common>
void main() {
	vWorldDirection = transformDirection( position, modelMatrix );
	#include <begin_vertex>
	#include <project_vertex>
}`,pp=`uniform sampler2D tEquirect;
varying vec3 vWorldDirection;
#include <common>
void main() {
	vec3 direction = normalize( vWorldDirection );
	vec2 sampleUV = equirectUv( direction );
	gl_FragColor = texture2D( tEquirect, sampleUV );
	#include <tonemapping_fragment>
	#include <colorspace_fragment>
}`,mp=`uniform float scale;
attribute float lineDistance;
varying float vLineDistance;
#include <common>
#include <uv_pars_vertex>
#include <color_pars_vertex>
#include <fog_pars_vertex>
#include <morphtarget_pars_vertex>
#include <logdepthbuf_pars_vertex>
#include <clipping_planes_pars_vertex>
void main() {
	vLineDistance = scale * lineDistance;
	#include <uv_vertex>
	#include <color_vertex>
	#include <morphinstance_vertex>
	#include <morphcolor_vertex>
	#include <begin_vertex>
	#include <morphtarget_vertex>
	#include <project_vertex>
	#include <logdepthbuf_vertex>
	#include <clipping_planes_vertex>
	#include <fog_vertex>
}`,gp=`uniform vec3 diffuse;
uniform float opacity;
uniform float dashSize;
uniform float totalSize;
varying float vLineDistance;
#include <common>
#include <color_pars_fragment>
#include <uv_pars_fragment>
#include <map_pars_fragment>
#include <fog_pars_fragment>
#include <logdepthbuf_pars_fragment>
#include <clipping_planes_pars_fragment>
void main() {
	vec4 diffuseColor = vec4( diffuse, opacity );
	#include <clipping_planes_fragment>
	if ( mod( vLineDistance, totalSize ) > dashSize ) {
		discard;
	}
	vec3 outgoingLight = vec3( 0.0 );
	#include <logdepthbuf_fragment>
	#include <map_fragment>
	#include <color_fragment>
	outgoingLight = diffuseColor.rgb;
	#include <opaque_fragment>
	#include <tonemapping_fragment>
	#include <colorspace_fragment>
	#include <fog_fragment>
	#include <premultiplied_alpha_fragment>
}`,xp=`#include <common>
#include <batching_pars_vertex>
#include <uv_pars_vertex>
#include <envmap_pars_vertex>
#include <color_pars_vertex>
#include <fog_pars_vertex>
#include <morphtarget_pars_vertex>
#include <skinning_pars_vertex>
#include <logdepthbuf_pars_vertex>
#include <clipping_planes_pars_vertex>
void main() {
	#include <uv_vertex>
	#include <color_vertex>
	#include <morphinstance_vertex>
	#include <morphcolor_vertex>
	#include <batching_vertex>
	#if defined ( USE_ENVMAP ) || defined ( USE_SKINNING )
		#include <beginnormal_vertex>
		#include <morphnormal_vertex>
		#include <skinbase_vertex>
		#include <skinnormal_vertex>
		#include <defaultnormal_vertex>
	#endif
	#include <begin_vertex>
	#include <morphtarget_vertex>
	#include <skinning_vertex>
	#include <project_vertex>
	#include <logdepthbuf_vertex>
	#include <clipping_planes_vertex>
	#include <worldpos_vertex>
	#include <envmap_vertex>
	#include <fog_vertex>
}`,bp=`uniform vec3 diffuse;
uniform float opacity;
#ifndef FLAT_SHADED
	varying vec3 vNormal;
#endif
#include <common>
#include <dithering_pars_fragment>
#include <color_pars_fragment>
#include <uv_pars_fragment>
#include <map_pars_fragment>
#include <alphamap_pars_fragment>
#include <alphatest_pars_fragment>
#include <alphahash_pars_fragment>
#include <aomap_pars_fragment>
#include <lightmap_pars_fragment>
#include <envmap_common_pars_fragment>
#include <envmap_pars_fragment>
#include <fog_pars_fragment>
#include <specularmap_pars_fragment>
#include <logdepthbuf_pars_fragment>
#include <clipping_planes_pars_fragment>
void main() {
	vec4 diffuseColor = vec4( diffuse, opacity );
	#include <clipping_planes_fragment>
	#include <logdepthbuf_fragment>
	#include <map_fragment>
	#include <color_fragment>
	#include <alphamap_fragment>
	#include <alphatest_fragment>
	#include <alphahash_fragment>
	#include <specularmap_fragment>
	ReflectedLight reflectedLight = ReflectedLight( vec3( 0.0 ), vec3( 0.0 ), vec3( 0.0 ), vec3( 0.0 ) );
	#ifdef USE_LIGHTMAP
		vec4 lightMapTexel = texture2D( lightMap, vLightMapUv );
		reflectedLight.indirectDiffuse += lightMapTexel.rgb * lightMapIntensity * RECIPROCAL_PI;
	#else
		reflectedLight.indirectDiffuse += vec3( 1.0 );
	#endif
	#include <aomap_fragment>
	reflectedLight.indirectDiffuse *= diffuseColor.rgb;
	vec3 outgoingLight = reflectedLight.indirectDiffuse;
	#include <envmap_fragment>
	#include <opaque_fragment>
	#include <tonemapping_fragment>
	#include <colorspace_fragment>
	#include <fog_fragment>
	#include <premultiplied_alpha_fragment>
	#include <dithering_fragment>
}`,_p=`#define LAMBERT
varying vec3 vViewPosition;
#include <common>
#include <batching_pars_vertex>
#include <uv_pars_vertex>
#include <displacementmap_pars_vertex>
#include <envmap_pars_vertex>
#include <color_pars_vertex>
#include <fog_pars_vertex>
#include <normal_pars_vertex>
#include <morphtarget_pars_vertex>
#include <skinning_pars_vertex>
#include <shadowmap_pars_vertex>
#include <logdepthbuf_pars_vertex>
#include <clipping_planes_pars_vertex>
void main() {
	#include <uv_vertex>
	#include <color_vertex>
	#include <morphinstance_vertex>
	#include <morphcolor_vertex>
	#include <batching_vertex>
	#include <beginnormal_vertex>
	#include <morphnormal_vertex>
	#include <skinbase_vertex>
	#include <skinnormal_vertex>
	#include <defaultnormal_vertex>
	#include <normal_vertex>
	#include <begin_vertex>
	#include <morphtarget_vertex>
	#include <skinning_vertex>
	#include <displacementmap_vertex>
	#include <project_vertex>
	#include <logdepthbuf_vertex>
	#include <clipping_planes_vertex>
	vViewPosition = - mvPosition.xyz;
	#include <worldpos_vertex>
	#include <envmap_vertex>
	#include <shadowmap_vertex>
	#include <fog_vertex>
}`,yp=`#define LAMBERT
uniform vec3 diffuse;
uniform vec3 emissive;
uniform float opacity;
#include <common>
#include <dithering_pars_fragment>
#include <color_pars_fragment>
#include <uv_pars_fragment>
#include <map_pars_fragment>
#include <alphamap_pars_fragment>
#include <alphatest_pars_fragment>
#include <alphahash_pars_fragment>
#include <aomap_pars_fragment>
#include <lightmap_pars_fragment>
#include <emissivemap_pars_fragment>
#include <cube_uv_reflection_fragment>
#include <envmap_common_pars_fragment>
#include <envmap_pars_fragment>
#include <envmap_physical_pars_fragment>
#include <fog_pars_fragment>
#include <bsdfs>
#include <lights_pars_begin>
#include <normal_pars_fragment>
#include <lights_lambert_pars_fragment>
#include <shadowmap_pars_fragment>
#include <bumpmap_pars_fragment>
#include <normalmap_pars_fragment>
#include <specularmap_pars_fragment>
#include <logdepthbuf_pars_fragment>
#include <clipping_planes_pars_fragment>
void main() {
	vec4 diffuseColor = vec4( diffuse, opacity );
	#include <clipping_planes_fragment>
	ReflectedLight reflectedLight = ReflectedLight( vec3( 0.0 ), vec3( 0.0 ), vec3( 0.0 ), vec3( 0.0 ) );
	vec3 totalEmissiveRadiance = emissive;
	#include <logdepthbuf_fragment>
	#include <map_fragment>
	#include <color_fragment>
	#include <alphamap_fragment>
	#include <alphatest_fragment>
	#include <alphahash_fragment>
	#include <specularmap_fragment>
	#include <normal_fragment_begin>
	#include <normal_fragment_maps>
	#include <emissivemap_fragment>
	#include <lights_lambert_fragment>
	#include <lights_fragment_begin>
	#include <lights_fragment_maps>
	#include <lights_fragment_end>
	#include <aomap_fragment>
	vec3 outgoingLight = reflectedLight.directDiffuse + reflectedLight.indirectDiffuse + totalEmissiveRadiance;
	#include <envmap_fragment>
	#include <opaque_fragment>
	#include <tonemapping_fragment>
	#include <colorspace_fragment>
	#include <fog_fragment>
	#include <premultiplied_alpha_fragment>
	#include <dithering_fragment>
}`,vp=`#define MATCAP
varying vec3 vViewPosition;
#include <common>
#include <batching_pars_vertex>
#include <uv_pars_vertex>
#include <color_pars_vertex>
#include <displacementmap_pars_vertex>
#include <fog_pars_vertex>
#include <normal_pars_vertex>
#include <morphtarget_pars_vertex>
#include <skinning_pars_vertex>
#include <logdepthbuf_pars_vertex>
#include <clipping_planes_pars_vertex>
void main() {
	#include <uv_vertex>
	#include <color_vertex>
	#include <morphinstance_vertex>
	#include <morphcolor_vertex>
	#include <batching_vertex>
	#include <beginnormal_vertex>
	#include <morphnormal_vertex>
	#include <skinbase_vertex>
	#include <skinnormal_vertex>
	#include <defaultnormal_vertex>
	#include <normal_vertex>
	#include <begin_vertex>
	#include <morphtarget_vertex>
	#include <skinning_vertex>
	#include <displacementmap_vertex>
	#include <project_vertex>
	#include <logdepthbuf_vertex>
	#include <clipping_planes_vertex>
	#include <fog_vertex>
	vViewPosition = - mvPosition.xyz;
}`,Sp=`#define MATCAP
uniform vec3 diffuse;
uniform float opacity;
uniform sampler2D matcap;
varying vec3 vViewPosition;
#include <common>
#include <dithering_pars_fragment>
#include <color_pars_fragment>
#include <uv_pars_fragment>
#include <map_pars_fragment>
#include <alphamap_pars_fragment>
#include <alphatest_pars_fragment>
#include <alphahash_pars_fragment>
#include <fog_pars_fragment>
#include <normal_pars_fragment>
#include <bumpmap_pars_fragment>
#include <normalmap_pars_fragment>
#include <logdepthbuf_pars_fragment>
#include <clipping_planes_pars_fragment>
void main() {
	vec4 diffuseColor = vec4( diffuse, opacity );
	#include <clipping_planes_fragment>
	#include <logdepthbuf_fragment>
	#include <map_fragment>
	#include <color_fragment>
	#include <alphamap_fragment>
	#include <alphatest_fragment>
	#include <alphahash_fragment>
	#include <normal_fragment_begin>
	#include <normal_fragment_maps>
	vec3 viewDir = normalize( vViewPosition );
	vec3 x = normalize( vec3( viewDir.z, 0.0, - viewDir.x ) );
	vec3 y = cross( viewDir, x );
	vec2 uv = vec2( dot( x, normal ), dot( y, normal ) ) * 0.495 + 0.5;
	#ifdef USE_MATCAP
		vec4 matcapColor = texture2D( matcap, uv );
	#else
		vec4 matcapColor = vec4( vec3( mix( 0.2, 0.8, uv.y ) ), 1.0 );
	#endif
	vec3 outgoingLight = diffuseColor.rgb * matcapColor.rgb;
	#include <opaque_fragment>
	#include <tonemapping_fragment>
	#include <colorspace_fragment>
	#include <fog_fragment>
	#include <premultiplied_alpha_fragment>
	#include <dithering_fragment>
}`,Mp=`#define NORMAL
#if defined( FLAT_SHADED ) || defined( USE_BUMPMAP ) || defined( USE_NORMALMAP_TANGENTSPACE )
	varying vec3 vViewPosition;
#endif
#include <common>
#include <batching_pars_vertex>
#include <uv_pars_vertex>
#include <displacementmap_pars_vertex>
#include <normal_pars_vertex>
#include <morphtarget_pars_vertex>
#include <skinning_pars_vertex>
#include <logdepthbuf_pars_vertex>
#include <clipping_planes_pars_vertex>
void main() {
	#include <uv_vertex>
	#include <batching_vertex>
	#include <beginnormal_vertex>
	#include <morphinstance_vertex>
	#include <morphnormal_vertex>
	#include <skinbase_vertex>
	#include <skinnormal_vertex>
	#include <defaultnormal_vertex>
	#include <normal_vertex>
	#include <begin_vertex>
	#include <morphtarget_vertex>
	#include <skinning_vertex>
	#include <displacementmap_vertex>
	#include <project_vertex>
	#include <logdepthbuf_vertex>
	#include <clipping_planes_vertex>
#if defined( FLAT_SHADED ) || defined( USE_BUMPMAP ) || defined( USE_NORMALMAP_TANGENTSPACE )
	vViewPosition = - mvPosition.xyz;
#endif
}`,Ap=`#define NORMAL
uniform float opacity;
#if defined( FLAT_SHADED ) || defined( USE_BUMPMAP ) || defined( USE_NORMALMAP_TANGENTSPACE )
	varying vec3 vViewPosition;
#endif
#include <uv_pars_fragment>
#include <normal_pars_fragment>
#include <bumpmap_pars_fragment>
#include <normalmap_pars_fragment>
#include <logdepthbuf_pars_fragment>
#include <clipping_planes_pars_fragment>
void main() {
	vec4 diffuseColor = vec4( 0.0, 0.0, 0.0, opacity );
	#include <clipping_planes_fragment>
	#include <logdepthbuf_fragment>
	#include <normal_fragment_begin>
	#include <normal_fragment_maps>
	gl_FragColor = vec4( normalize( normal ) * 0.5 + 0.5, diffuseColor.a );
	#ifdef OPAQUE
		gl_FragColor.a = 1.0;
	#endif
}`,Tp=`#define PHONG
varying vec3 vViewPosition;
#include <common>
#include <batching_pars_vertex>
#include <uv_pars_vertex>
#include <displacementmap_pars_vertex>
#include <envmap_pars_vertex>
#include <color_pars_vertex>
#include <fog_pars_vertex>
#include <normal_pars_vertex>
#include <morphtarget_pars_vertex>
#include <skinning_pars_vertex>
#include <shadowmap_pars_vertex>
#include <logdepthbuf_pars_vertex>
#include <clipping_planes_pars_vertex>
void main() {
	#include <uv_vertex>
	#include <color_vertex>
	#include <morphcolor_vertex>
	#include <batching_vertex>
	#include <beginnormal_vertex>
	#include <morphinstance_vertex>
	#include <morphnormal_vertex>
	#include <skinbase_vertex>
	#include <skinnormal_vertex>
	#include <defaultnormal_vertex>
	#include <normal_vertex>
	#include <begin_vertex>
	#include <morphtarget_vertex>
	#include <skinning_vertex>
	#include <displacementmap_vertex>
	#include <project_vertex>
	#include <logdepthbuf_vertex>
	#include <clipping_planes_vertex>
	vViewPosition = - mvPosition.xyz;
	#include <worldpos_vertex>
	#include <envmap_vertex>
	#include <shadowmap_vertex>
	#include <fog_vertex>
}`,wp=`#define PHONG
uniform vec3 diffuse;
uniform vec3 emissive;
uniform vec3 specular;
uniform float shininess;
uniform float opacity;
#include <common>
#include <dithering_pars_fragment>
#include <color_pars_fragment>
#include <uv_pars_fragment>
#include <map_pars_fragment>
#include <alphamap_pars_fragment>
#include <alphatest_pars_fragment>
#include <alphahash_pars_fragment>
#include <aomap_pars_fragment>
#include <lightmap_pars_fragment>
#include <emissivemap_pars_fragment>
#include <cube_uv_reflection_fragment>
#include <envmap_common_pars_fragment>
#include <envmap_pars_fragment>
#include <envmap_physical_pars_fragment>
#include <fog_pars_fragment>
#include <bsdfs>
#include <lights_pars_begin>
#include <normal_pars_fragment>
#include <lights_phong_pars_fragment>
#include <shadowmap_pars_fragment>
#include <bumpmap_pars_fragment>
#include <normalmap_pars_fragment>
#include <specularmap_pars_fragment>
#include <logdepthbuf_pars_fragment>
#include <clipping_planes_pars_fragment>
void main() {
	vec4 diffuseColor = vec4( diffuse, opacity );
	#include <clipping_planes_fragment>
	ReflectedLight reflectedLight = ReflectedLight( vec3( 0.0 ), vec3( 0.0 ), vec3( 0.0 ), vec3( 0.0 ) );
	vec3 totalEmissiveRadiance = emissive;
	#include <logdepthbuf_fragment>
	#include <map_fragment>
	#include <color_fragment>
	#include <alphamap_fragment>
	#include <alphatest_fragment>
	#include <alphahash_fragment>
	#include <specularmap_fragment>
	#include <normal_fragment_begin>
	#include <normal_fragment_maps>
	#include <emissivemap_fragment>
	#include <lights_phong_fragment>
	#include <lights_fragment_begin>
	#include <lights_fragment_maps>
	#include <lights_fragment_end>
	#include <aomap_fragment>
	vec3 outgoingLight = reflectedLight.directDiffuse + reflectedLight.indirectDiffuse + reflectedLight.directSpecular + reflectedLight.indirectSpecular + totalEmissiveRadiance;
	#include <envmap_fragment>
	#include <opaque_fragment>
	#include <tonemapping_fragment>
	#include <colorspace_fragment>
	#include <fog_fragment>
	#include <premultiplied_alpha_fragment>
	#include <dithering_fragment>
}`,Ep=`#define STANDARD
varying vec3 vViewPosition;
#ifdef USE_TRANSMISSION
	varying vec3 vWorldPosition;
#endif
#include <common>
#include <batching_pars_vertex>
#include <uv_pars_vertex>
#include <displacementmap_pars_vertex>
#include <color_pars_vertex>
#include <fog_pars_vertex>
#include <normal_pars_vertex>
#include <morphtarget_pars_vertex>
#include <skinning_pars_vertex>
#include <shadowmap_pars_vertex>
#include <logdepthbuf_pars_vertex>
#include <clipping_planes_pars_vertex>
void main() {
	#include <uv_vertex>
	#include <color_vertex>
	#include <morphinstance_vertex>
	#include <morphcolor_vertex>
	#include <batching_vertex>
	#include <beginnormal_vertex>
	#include <morphnormal_vertex>
	#include <skinbase_vertex>
	#include <skinnormal_vertex>
	#include <defaultnormal_vertex>
	#include <normal_vertex>
	#include <begin_vertex>
	#include <morphtarget_vertex>
	#include <skinning_vertex>
	#include <displacementmap_vertex>
	#include <project_vertex>
	#include <logdepthbuf_vertex>
	#include <clipping_planes_vertex>
	vViewPosition = - mvPosition.xyz;
	#include <worldpos_vertex>
	#include <shadowmap_vertex>
	#include <fog_vertex>
#ifdef USE_TRANSMISSION
	vWorldPosition = worldPosition.xyz;
#endif
}`,Rp=`#define STANDARD
#ifdef PHYSICAL
	#define IOR
	#define USE_SPECULAR
#endif
uniform vec3 diffuse;
uniform vec3 emissive;
uniform float roughness;
uniform float metalness;
uniform float opacity;
#ifdef IOR
	uniform float ior;
#endif
#ifdef USE_SPECULAR
	uniform float specularIntensity;
	uniform vec3 specularColor;
	#ifdef USE_SPECULAR_COLORMAP
		uniform sampler2D specularColorMap;
	#endif
	#ifdef USE_SPECULAR_INTENSITYMAP
		uniform sampler2D specularIntensityMap;
	#endif
#endif
#ifdef USE_CLEARCOAT
	uniform float clearcoat;
	uniform float clearcoatRoughness;
#endif
#ifdef USE_DISPERSION
	uniform float dispersion;
#endif
#ifdef USE_RETROREFLECTION
	uniform float retroreflectivity;
#endif
#ifdef USE_IRIDESCENCE
	uniform float iridescence;
	uniform float iridescenceIOR;
	uniform float iridescenceThicknessMinimum;
	uniform float iridescenceThicknessMaximum;
#endif
#ifdef USE_SHEEN
	uniform vec3 sheenColor;
	uniform float sheenRoughness;
	#ifdef USE_SHEEN_COLORMAP
		uniform sampler2D sheenColorMap;
	#endif
	#ifdef USE_SHEEN_ROUGHNESSMAP
		uniform sampler2D sheenRoughnessMap;
	#endif
#endif
#ifdef USE_ANISOTROPY
	uniform vec2 anisotropyVector;
	#ifdef USE_ANISOTROPYMAP
		uniform sampler2D anisotropyMap;
	#endif
#endif
varying vec3 vViewPosition;
#include <common>
#include <dithering_pars_fragment>
#include <color_pars_fragment>
#include <uv_pars_fragment>
#include <map_pars_fragment>
#include <alphamap_pars_fragment>
#include <alphatest_pars_fragment>
#include <alphahash_pars_fragment>
#include <aomap_pars_fragment>
#include <lightmap_pars_fragment>
#include <emissivemap_pars_fragment>
#include <iridescence_fragment>
#include <cube_uv_reflection_fragment>
#include <envmap_common_pars_fragment>
#include <envmap_physical_pars_fragment>
#include <fog_pars_fragment>
#include <lights_pars_begin>
#include <normal_pars_fragment>
#include <lights_physical_pars_fragment>
#include <transmission_pars_fragment>
#include <shadowmap_pars_fragment>
#include <bumpmap_pars_fragment>
#include <normalmap_pars_fragment>
#include <clearcoat_pars_fragment>
#include <iridescence_pars_fragment>
#include <roughnessmap_pars_fragment>
#include <metalnessmap_pars_fragment>
#include <logdepthbuf_pars_fragment>
#include <clipping_planes_pars_fragment>
void main() {
	vec4 diffuseColor = vec4( diffuse, opacity );
	#include <clipping_planes_fragment>
	ReflectedLight reflectedLight = ReflectedLight( vec3( 0.0 ), vec3( 0.0 ), vec3( 0.0 ), vec3( 0.0 ) );
	vec3 totalEmissiveRadiance = emissive;
	#include <logdepthbuf_fragment>
	#include <map_fragment>
	#include <color_fragment>
	#include <alphamap_fragment>
	#include <alphatest_fragment>
	#include <alphahash_fragment>
	#include <roughnessmap_fragment>
	#include <metalnessmap_fragment>
	#include <normal_fragment_begin>
	#include <normal_fragment_maps>
	#include <clearcoat_normal_fragment_begin>
	#include <clearcoat_normal_fragment_maps>
	#include <emissivemap_fragment>
	#include <lights_physical_fragment>
	#include <lights_fragment_begin>
	#include <lights_fragment_maps>
	#include <lights_fragment_end>
	#include <aomap_fragment>
	vec3 totalDiffuse = reflectedLight.directDiffuse + reflectedLight.indirectDiffuse;
	vec3 totalSpecular = reflectedLight.directSpecular + reflectedLight.indirectSpecular;
	#include <transmission_fragment>
	vec3 outgoingLight = totalDiffuse + totalSpecular + totalEmissiveRadiance;
	#ifdef USE_SHEEN
 
		outgoingLight = outgoingLight + sheenSpecularDirect + sheenSpecularIndirect;
 
 	#endif
	#ifdef USE_CLEARCOAT
		float dotNVcc = saturate( dot( geometryClearcoatNormal, geometryViewDir ) );
		vec3 Fcc = F_Schlick( material.clearcoatF0, material.clearcoatF90, dotNVcc );
		outgoingLight = outgoingLight * ( 1.0 - material.clearcoat * Fcc ) + ( clearcoatSpecularDirect + clearcoatSpecularIndirect ) * material.clearcoat;
	#endif
	#include <opaque_fragment>
	#include <tonemapping_fragment>
	#include <colorspace_fragment>
	#include <fog_fragment>
	#include <premultiplied_alpha_fragment>
	#include <dithering_fragment>
}`,Cp=`#define TOON
varying vec3 vViewPosition;
#include <common>
#include <batching_pars_vertex>
#include <uv_pars_vertex>
#include <displacementmap_pars_vertex>
#include <color_pars_vertex>
#include <fog_pars_vertex>
#include <normal_pars_vertex>
#include <morphtarget_pars_vertex>
#include <skinning_pars_vertex>
#include <shadowmap_pars_vertex>
#include <logdepthbuf_pars_vertex>
#include <clipping_planes_pars_vertex>
void main() {
	#include <uv_vertex>
	#include <color_vertex>
	#include <morphinstance_vertex>
	#include <morphcolor_vertex>
	#include <batching_vertex>
	#include <beginnormal_vertex>
	#include <morphnormal_vertex>
	#include <skinbase_vertex>
	#include <skinnormal_vertex>
	#include <defaultnormal_vertex>
	#include <normal_vertex>
	#include <begin_vertex>
	#include <morphtarget_vertex>
	#include <skinning_vertex>
	#include <displacementmap_vertex>
	#include <project_vertex>
	#include <logdepthbuf_vertex>
	#include <clipping_planes_vertex>
	vViewPosition = - mvPosition.xyz;
	#include <worldpos_vertex>
	#include <shadowmap_vertex>
	#include <fog_vertex>
}`,Ip=`#define TOON
uniform vec3 diffuse;
uniform vec3 emissive;
uniform float opacity;
#include <common>
#include <dithering_pars_fragment>
#include <color_pars_fragment>
#include <uv_pars_fragment>
#include <map_pars_fragment>
#include <alphamap_pars_fragment>
#include <alphatest_pars_fragment>
#include <alphahash_pars_fragment>
#include <aomap_pars_fragment>
#include <lightmap_pars_fragment>
#include <emissivemap_pars_fragment>
#include <gradientmap_pars_fragment>
#include <fog_pars_fragment>
#include <bsdfs>
#include <lights_pars_begin>
#include <normal_pars_fragment>
#include <lights_toon_pars_fragment>
#include <shadowmap_pars_fragment>
#include <bumpmap_pars_fragment>
#include <normalmap_pars_fragment>
#include <logdepthbuf_pars_fragment>
#include <clipping_planes_pars_fragment>
void main() {
	vec4 diffuseColor = vec4( diffuse, opacity );
	#include <clipping_planes_fragment>
	ReflectedLight reflectedLight = ReflectedLight( vec3( 0.0 ), vec3( 0.0 ), vec3( 0.0 ), vec3( 0.0 ) );
	vec3 totalEmissiveRadiance = emissive;
	#include <logdepthbuf_fragment>
	#include <map_fragment>
	#include <color_fragment>
	#include <alphamap_fragment>
	#include <alphatest_fragment>
	#include <alphahash_fragment>
	#include <normal_fragment_begin>
	#include <normal_fragment_maps>
	#include <emissivemap_fragment>
	#include <lights_toon_fragment>
	#include <lights_fragment_begin>
	#include <lights_fragment_maps>
	#include <lights_fragment_end>
	#include <aomap_fragment>
	vec3 outgoingLight = reflectedLight.directDiffuse + reflectedLight.indirectDiffuse + totalEmissiveRadiance;
	#include <opaque_fragment>
	#include <tonemapping_fragment>
	#include <colorspace_fragment>
	#include <fog_fragment>
	#include <premultiplied_alpha_fragment>
	#include <dithering_fragment>
}`,Pp=`uniform float size;
uniform float scale;
#include <common>
#include <color_pars_vertex>
#include <fog_pars_vertex>
#include <morphtarget_pars_vertex>
#include <logdepthbuf_pars_vertex>
#include <clipping_planes_pars_vertex>
#ifdef USE_POINTS_UV
	varying vec2 vUv;
	uniform mat3 uvTransform;
#endif
void main() {
	#ifdef USE_POINTS_UV
		vUv = ( uvTransform * vec3( uv, 1 ) ).xy;
	#endif
	#include <color_vertex>
	#include <morphinstance_vertex>
	#include <morphcolor_vertex>
	#include <begin_vertex>
	#include <morphtarget_vertex>
	#include <project_vertex>
	gl_PointSize = size;
	#ifdef USE_SIZEATTENUATION
		bool isPerspective = isPerspectiveMatrix( projectionMatrix );
		if ( isPerspective ) gl_PointSize *= ( scale / - mvPosition.z );
	#endif
	#include <logdepthbuf_vertex>
	#include <clipping_planes_vertex>
	#include <worldpos_vertex>
	#include <fog_vertex>
}`,Lp=`uniform vec3 diffuse;
uniform float opacity;
#include <common>
#include <color_pars_fragment>
#include <map_particle_pars_fragment>
#include <alphatest_pars_fragment>
#include <alphahash_pars_fragment>
#include <fog_pars_fragment>
#include <logdepthbuf_pars_fragment>
#include <clipping_planes_pars_fragment>
void main() {
	vec4 diffuseColor = vec4( diffuse, opacity );
	#include <clipping_planes_fragment>
	vec3 outgoingLight = vec3( 0.0 );
	#include <logdepthbuf_fragment>
	#include <map_particle_fragment>
	#include <color_fragment>
	#include <alphatest_fragment>
	#include <alphahash_fragment>
	outgoingLight = diffuseColor.rgb;
	#include <opaque_fragment>
	#include <tonemapping_fragment>
	#include <colorspace_fragment>
	#include <fog_fragment>
	#include <premultiplied_alpha_fragment>
}`,Dp=`#include <common>
#include <batching_pars_vertex>
#include <fog_pars_vertex>
#include <morphtarget_pars_vertex>
#include <skinning_pars_vertex>
#include <logdepthbuf_pars_vertex>
#include <shadowmap_pars_vertex>
void main() {
	#include <batching_vertex>
	#include <beginnormal_vertex>
	#include <morphinstance_vertex>
	#include <morphnormal_vertex>
	#include <skinbase_vertex>
	#include <skinnormal_vertex>
	#include <defaultnormal_vertex>
	#include <begin_vertex>
	#include <morphtarget_vertex>
	#include <skinning_vertex>
	#include <project_vertex>
	#include <logdepthbuf_vertex>
	#include <worldpos_vertex>
	#include <shadowmap_vertex>
	#include <fog_vertex>
}`,Np=`uniform vec3 color;
uniform float opacity;
#include <common>
#include <fog_pars_fragment>
#include <bsdfs>
#include <lights_pars_begin>
#include <logdepthbuf_pars_fragment>
#include <shadowmap_pars_fragment>
#include <shadowmask_pars_fragment>
void main() {
	#include <logdepthbuf_fragment>
	gl_FragColor = vec4( color, opacity * ( 1.0 - getShadowMask() ) );
	#include <tonemapping_fragment>
	#include <colorspace_fragment>
	#include <fog_fragment>
	#include <premultiplied_alpha_fragment>
}`,Fp=`uniform float rotation;
uniform vec2 center;
#include <common>
#include <uv_pars_vertex>
#include <fog_pars_vertex>
#include <logdepthbuf_pars_vertex>
#include <clipping_planes_pars_vertex>
void main() {
	#include <uv_vertex>
	vec4 mvPosition = modelViewMatrix[ 3 ];
	vec2 scale = vec2( length( modelMatrix[ 0 ].xyz ), length( modelMatrix[ 1 ].xyz ) );
	#ifndef USE_SIZEATTENUATION
		bool isPerspective = isPerspectiveMatrix( projectionMatrix );
		if ( isPerspective ) scale *= - mvPosition.z;
	#endif
	vec2 alignedPosition = ( position.xy - ( center - vec2( 0.5 ) ) ) * scale;
	vec2 rotatedPosition;
	rotatedPosition.x = cos( rotation ) * alignedPosition.x - sin( rotation ) * alignedPosition.y;
	rotatedPosition.y = sin( rotation ) * alignedPosition.x + cos( rotation ) * alignedPosition.y;
	mvPosition.xy += rotatedPosition;
	gl_Position = projectionMatrix * mvPosition;
	#include <logdepthbuf_vertex>
	#include <clipping_planes_vertex>
	#include <fog_vertex>
}`,Up=`uniform vec3 diffuse;
uniform float opacity;
#include <common>
#include <uv_pars_fragment>
#include <map_pars_fragment>
#include <alphamap_pars_fragment>
#include <alphatest_pars_fragment>
#include <alphahash_pars_fragment>
#include <fog_pars_fragment>
#include <logdepthbuf_pars_fragment>
#include <clipping_planes_pars_fragment>
void main() {
	vec4 diffuseColor = vec4( diffuse, opacity );
	#include <clipping_planes_fragment>
	vec3 outgoingLight = vec3( 0.0 );
	#include <logdepthbuf_fragment>
	#include <map_fragment>
	#include <alphamap_fragment>
	#include <alphatest_fragment>
	#include <alphahash_fragment>
	outgoingLight = diffuseColor.rgb;
	#include <opaque_fragment>
	#include <tonemapping_fragment>
	#include <colorspace_fragment>
	#include <fog_fragment>
}`,Y={alphahash_fragment:nf,alphahash_pars_fragment:sf,alphamap_fragment:rf,alphamap_pars_fragment:af,alphatest_fragment:of,alphatest_pars_fragment:cf,aomap_fragment:lf,aomap_pars_fragment:uf,batching_pars_vertex:hf,batching_vertex:ff,begin_vertex:df,beginnormal_vertex:pf,bsdfs:mf,iridescence_fragment:gf,bumpmap_pars_fragment:xf,clipping_planes_fragment:bf,clipping_planes_pars_fragment:_f,clipping_planes_pars_vertex:yf,clipping_planes_vertex:vf,color_fragment:Sf,color_pars_fragment:Mf,color_pars_vertex:Af,color_vertex:Tf,common:wf,cube_uv_reflection_fragment:Ef,defaultnormal_vertex:Rf,displacementmap_pars_vertex:Cf,displacementmap_vertex:If,emissivemap_fragment:Pf,emissivemap_pars_fragment:Lf,colorspace_fragment:Df,colorspace_pars_fragment:Nf,envmap_fragment:Ff,envmap_common_pars_fragment:Uf,envmap_pars_fragment:Of,envmap_pars_vertex:Bf,envmap_physical_pars_fragment:jf,envmap_vertex:kf,fog_vertex:zf,fog_pars_vertex:Vf,fog_fragment:Gf,fog_pars_fragment:Hf,gradientmap_pars_fragment:Wf,lightmap_pars_fragment:Xf,lights_lambert_fragment:qf,lights_lambert_pars_fragment:Kf,lights_pars_begin:Yf,lights_toon_fragment:Jf,lights_toon_pars_fragment:Zf,lights_phong_fragment:$f,lights_phong_pars_fragment:Qf,lights_physical_fragment:ed,lights_physical_pars_fragment:td,lights_fragment_begin:nd,lights_fragment_maps:id,lights_fragment_end:sd,lightprobes_pars_fragment:rd,logdepthbuf_fragment:ad,logdepthbuf_pars_fragment:od,logdepthbuf_pars_vertex:cd,logdepthbuf_vertex:ld,map_fragment:ud,map_pars_fragment:hd,map_particle_fragment:fd,map_particle_pars_fragment:dd,metalnessmap_fragment:pd,metalnessmap_pars_fragment:md,morphinstance_vertex:gd,morphcolor_vertex:xd,morphnormal_vertex:bd,morphtarget_pars_vertex:_d,morphtarget_vertex:yd,normal_fragment_begin:vd,normal_fragment_maps:Sd,normal_pars_fragment:Md,normal_pars_vertex:Ad,normal_vertex:Td,normalmap_pars_fragment:wd,clearcoat_normal_fragment_begin:Ed,clearcoat_normal_fragment_maps:Rd,clearcoat_pars_fragment:Cd,iridescence_pars_fragment:Id,opaque_fragment:Pd,packing:Ld,premultiplied_alpha_fragment:Dd,project_vertex:Nd,dithering_fragment:Fd,dithering_pars_fragment:Ud,roughnessmap_fragment:Od,roughnessmap_pars_fragment:Bd,shadowmap_pars_fragment:kd,shadowmap_pars_vertex:zd,shadowmap_vertex:Vd,shadowmask_pars_fragment:Gd,skinbase_vertex:Hd,skinning_pars_vertex:Wd,skinning_vertex:Xd,skinnormal_vertex:qd,specularmap_fragment:Kd,specularmap_pars_fragment:Yd,tonemapping_fragment:jd,tonemapping_pars_fragment:Jd,transmission_fragment:Zd,transmission_pars_fragment:$d,uv_pars_fragment:Qd,uv_pars_vertex:ep,uv_vertex:tp,worldpos_vertex:np,background_vert:ip,background_frag:sp,backgroundCube_vert:rp,backgroundCube_frag:ap,cube_vert:op,cube_frag:cp,depth_vert:lp,depth_frag:up,distance_vert:hp,distance_frag:fp,equirect_vert:dp,equirect_frag:pp,linedashed_vert:mp,linedashed_frag:gp,meshbasic_vert:xp,meshbasic_frag:bp,meshlambert_vert:_p,meshlambert_frag:yp,meshmatcap_vert:vp,meshmatcap_frag:Sp,meshnormal_vert:Mp,meshnormal_frag:Ap,meshphong_vert:Tp,meshphong_frag:wp,meshphysical_vert:Ep,meshphysical_frag:Rp,meshtoon_vert:Cp,meshtoon_frag:Ip,points_vert:Pp,points_frag:Lp,shadow_vert:Dp,shadow_frag:Np,sprite_vert:Fp,sprite_frag:Up},D={common:{diffuse:{value:new H(16777215)},opacity:{value:1},map:{value:null},mapTransform:{value:new G},alphaMap:{value:null},alphaMapTransform:{value:new G},alphaTest:{value:0}},specularmap:{specularMap:{value:null},specularMapTransform:{value:new G}},envmap:{envMap:{value:null},envMapRotation:{value:new G},reflectivity:{value:1},ior:{value:1.5},refractionRatio:{value:.98},dfgLUT:{value:null}},aomap:{aoMap:{value:null},aoMapIntensity:{value:1},aoMapTransform:{value:new G}},lightmap:{lightMap:{value:null},lightMapIntensity:{value:1},lightMapTransform:{value:new G}},bumpmap:{bumpMap:{value:null},bumpMapTransform:{value:new G},bumpScale:{value:1}},normalmap:{normalMap:{value:null},normalMapTransform:{value:new G},normalScale:{value:new $(1,1)}},displacementmap:{displacementMap:{value:null},displacementMapTransform:{value:new G},displacementScale:{value:1},displacementBias:{value:0}},emissivemap:{emissiveMap:{value:null},emissiveMapTransform:{value:new G}},metalnessmap:{metalnessMap:{value:null},metalnessMapTransform:{value:new G}},roughnessmap:{roughnessMap:{value:null},roughnessMapTransform:{value:new G}},gradientmap:{gradientMap:{value:null}},fog:{fogDensity:{value:25e-5},fogNear:{value:1},fogFar:{value:2e3},fogColor:{value:new H(16777215)}},lights:{ambientLightColor:{value:[]},lightProbe:{value:[]},sunLights:{value:[],properties:{direction:{},color:{}}},sunLightShadows:{value:[],properties:{shadowIntensity:1,shadowBias:{},shadowNormalBias:{},shadowRadius:{},shadowMapSize:{}}},sunShadowMatrix:{value:[]},sunShadowCascade:{value:[]},directionalLights:{value:[],properties:{direction:{},color:{}}},directionalLightShadows:{value:[],properties:{shadowIntensity:1,shadowBias:{},shadowNormalBias:{},shadowRadius:{},shadowMapSize:{}}},directionalShadowMatrix:{value:[]},spotLights:{value:[],properties:{color:{},position:{},direction:{},distance:{},coneCos:{},penumbraCos:{},decay:{}}},spotLightShadows:{value:[],properties:{shadowIntensity:1,shadowBias:{},shadowNormalBias:{},shadowRadius:{},shadowMapSize:{}}},spotLightMap:{value:[]},spotLightMatrix:{value:[]},pointLights:{value:[],properties:{color:{},position:{},decay:{},distance:{}}},pointLightShadows:{value:[],properties:{shadowIntensity:1,shadowBias:{},shadowNormalBias:{},shadowRadius:{},shadowMapSize:{},shadowCameraNear:{},shadowCameraFar:{}}},pointShadowMatrix:{value:[]},hemisphereLights:{value:[],properties:{direction:{},skyColor:{},groundColor:{}}},rectAreaLights:{value:[],properties:{color:{},position:{},width:{},height:{}}},ltc_1:{value:null},ltc_2:{value:null},probesSH:{value:null},probesMin:{value:new E},probesMax:{value:new E},probesResolution:{value:new E}},points:{diffuse:{value:new H(16777215)},opacity:{value:1},size:{value:1},scale:{value:1},map:{value:null},alphaMap:{value:null},alphaMapTransform:{value:new G},alphaTest:{value:0},uvTransform:{value:new G}},sprite:{diffuse:{value:new H(16777215)},opacity:{value:1},center:{value:new $(.5,.5)},rotation:{value:0},map:{value:null},mapTransform:{value:new G},alphaMap:{value:null},alphaMapTransform:{value:new G},alphaTest:{value:0}}},pl={basic:{uniforms:Ce([D.common,D.specularmap,D.envmap,D.aomap,D.lightmap,D.fog]),vertexShader:Y.meshbasic_vert,fragmentShader:Y.meshbasic_frag},lambert:{uniforms:Ce([D.common,D.specularmap,D.envmap,D.aomap,D.lightmap,D.emissivemap,D.bumpmap,D.normalmap,D.displacementmap,D.fog,D.lights,{emissive:{value:new H(0)},envMapIntensity:{value:1}}]),vertexShader:Y.meshlambert_vert,fragmentShader:Y.meshlambert_frag},phong:{uniforms:Ce([D.common,D.specularmap,D.envmap,D.aomap,D.lightmap,D.emissivemap,D.bumpmap,D.normalmap,D.displacementmap,D.fog,D.lights,{emissive:{value:new H(0)},specular:{value:new H(1118481)},shininess:{value:30},envMapIntensity:{value:1}}]),vertexShader:Y.meshphong_vert,fragmentShader:Y.meshphong_frag},standard:{uniforms:Ce([D.common,D.envmap,D.aomap,D.lightmap,D.emissivemap,D.bumpmap,D.normalmap,D.displacementmap,D.roughnessmap,D.metalnessmap,D.fog,D.lights,{emissive:{value:new H(0)},roughness:{value:1},metalness:{value:0},envMapIntensity:{value:1}}]),vertexShader:Y.meshphysical_vert,fragmentShader:Y.meshphysical_frag},toon:{uniforms:Ce([D.common,D.aomap,D.lightmap,D.emissivemap,D.bumpmap,D.normalmap,D.displacementmap,D.gradientmap,D.fog,D.lights,{emissive:{value:new H(0)}}]),vertexShader:Y.meshtoon_vert,fragmentShader:Y.meshtoon_frag},matcap:{uniforms:Ce([D.common,D.bumpmap,D.normalmap,D.displacementmap,D.fog,{matcap:{value:null}}]),vertexShader:Y.meshmatcap_vert,fragmentShader:Y.meshmatcap_frag},points:{uniforms:Ce([D.points,D.fog]),vertexShader:Y.points_vert,fragmentShader:Y.points_frag},dashed:{uniforms:Ce([D.common,D.fog,{scale:{value:1},dashSize:{value:1},totalSize:{value:2}}]),vertexShader:Y.linedashed_vert,fragmentShader:Y.linedashed_frag},depth:{uniforms:Ce([D.common,D.displacementmap]),vertexShader:Y.depth_vert,fragmentShader:Y.depth_frag},normal:{uniforms:Ce([D.common,D.bumpmap,D.normalmap,D.displacementmap,{opacity:{value:1}}]),vertexShader:Y.meshnormal_vert,fragmentShader:Y.meshnormal_frag},sprite:{uniforms:Ce([D.sprite,D.fog]),vertexShader:Y.sprite_vert,fragmentShader:Y.sprite_frag},background:{uniforms:{uvTransform:{value:new G},t2D:{value:null},backgroundIntensity:{value:1}},vertexShader:Y.background_vert,fragmentShader:Y.background_frag},backgroundCube:{uniforms:{envMap:{value:null},backgroundBlurriness:{value:0},backgroundIntensity:{value:1},backgroundRotation:{value:new G}},vertexShader:Y.backgroundCube_vert,fragmentShader:Y.backgroundCube_frag},cube:{uniforms:{tCube:{value:null},tFlip:{value:-1},opacity:{value:1}},vertexShader:Y.cube_vert,fragmentShader:Y.cube_frag},equirect:{uniforms:{tEquirect:{value:null}},vertexShader:Y.equirect_vert,fragmentShader:Y.equirect_frag},distance:{uniforms:Ce([D.common,D.displacementmap,{referencePosition:{value:new E},nearDistance:{value:1},farDistance:{value:1e3}}]),vertexShader:Y.distance_vert,fragmentShader:Y.distance_frag},shadow:{uniforms:Ce([D.lights,D.fog,{color:{value:new H(0)},opacity:{value:1}}]),vertexShader:Y.shadow_vert,fragmentShader:Y.shadow_frag}};pl.physical={uniforms:Ce([pl.standard.uniforms,{clearcoat:{value:0},clearcoatMap:{value:null},clearcoatMapTransform:{value:new G},clearcoatNormalMap:{value:null},clearcoatNormalMapTransform:{value:new G},clearcoatNormalScale:{value:new $(1,1)},clearcoatRoughness:{value:0},clearcoatRoughnessMap:{value:null},clearcoatRoughnessMapTransform:{value:new G},dispersion:{value:0},retroreflectivity:{value:0},iridescence:{value:0},iridescenceMap:{value:null},iridescenceMapTransform:{value:new G},iridescenceIOR:{value:1.3},iridescenceThicknessMinimum:{value:100},iridescenceThicknessMaximum:{value:400},iridescenceThicknessMap:{value:null},iridescenceThicknessMapTransform:{value:new G},sheen:{value:0},sheenColor:{value:new H(0)},sheenColorMap:{value:null},sheenColorMapTransform:{value:new G},sheenRoughness:{value:1},sheenRoughnessMap:{value:null},sheenRoughnessMapTransform:{value:new G},transmission:{value:0},transmissionMap:{value:null},transmissionMapTransform:{value:new G},transmissionSamplerSize:{value:new $},transmissionSamplerMap:{value:null},thickness:{value:0},thicknessMap:{value:null},thicknessMapTransform:{value:new G},attenuationDistance:{value:0},attenuationColor:{value:new H(0)},specularColor:{value:new H(1,1,1)},specularColorMap:{value:null},specularColorMapTransform:{value:new G},specularIntensity:{value:1},specularIntensityMap:{value:null},specularIntensityMapTransform:{value:new G},anisotropyVector:{value:new $},anisotropyMap:{value:null},anisotropyMapTransform:{value:new G}}]),vertexShader:Y.meshphysical_vert,fragmentShader:Y.meshphysical_frag};var Op=new G;Op.set(-1,0,0,0,1,0,0,0,1);var zv={[$r]:"LINEAR_TONE_MAPPING",[Qr]:"REINHARD_TONE_MAPPING",[ea]:"CINEON_TONE_MAPPING",[ta]:"ACES_FILMIC_TONE_MAPPING",[ia]:"AGX_TONE_MAPPING",[sa]:"NEUTRAL_TONE_MAPPING",[na]:"CUSTOM_TONE_MAPPING"};var Vv=new Float32Array(16),Gv=new Float32Array(9),Hv=new Float32Array(4);var Wv={[$r]:"Linear",[Qr]:"Reinhard",[ea]:"Cineon",[ta]:"ACESFilmic",[ia]:"AgX",[sa]:"Neutral",[na]:"Custom"};var Xv={[Kc]:"SHADOWMAP_TYPE_PCF",[Yc]:"SHADOWMAP_TYPE_VSM"};var qv={[il]:"ENVMAP_TYPE_CUBE",[aa]:"ENVMAP_TYPE_CUBE",[sl]:"ENVMAP_TYPE_CUBE_UV"};var Kv={[aa]:"ENVMAP_MODE_REFRACTION"};var Yv={[Zr]:"ENVMAP_BLENDING_MULTIPLY",[el]:"ENVMAP_BLENDING_MIX",[tl]:"ENVMAP_BLENDING_ADD"};var Bp=new G;Bp.set(-1,0,0,0,1,0,0,0,1);var jv=new Uint16Array([12469,15057,12620,14925,13266,14620,13807,14376,14323,13990,14545,13625,14713,13328,14840,12882,14931,12528,14996,12233,15039,11829,15066,11525,15080,11295,15085,10976,15082,10705,15073,10495,13880,14564,13898,14542,13977,14430,14158,14124,14393,13732,14556,13410,14702,12996,14814,12596,14891,12291,14937,11834,14957,11489,14958,11194,14943,10803,14921,10506,14893,10278,14858,9960,14484,14039,14487,14025,14499,13941,14524,13740,14574,13468,14654,13106,14743,12678,14818,12344,14867,11893,14889,11509,14893,11180,14881,10751,14852,10428,14812,10128,14765,9754,14712,9466,14764,13480,14764,13475,14766,13440,14766,13347,14769,13070,14786,12713,14816,12387,14844,11957,14860,11549,14868,11215,14855,10751,14825,10403,14782,10044,14729,9651,14666,9352,14599,9029,14967,12835,14966,12831,14963,12804,14954,12723,14936,12564,14917,12347,14900,11958,14886,11569,14878,11247,14859,10765,14828,10401,14784,10011,14727,9600,14660,9289,14586,8893,14508,8533,15111,12234,15110,12234,15104,12216,15092,12156,15067,12010,15028,11776,14981,11500,14942,11205,14902,10752,14861,10393,14812,9991,14752,9570,14682,9252,14603,8808,14519,8445,14431,8145,15209,11449,15208,11451,15202,11451,15190,11438,15163,11384,15117,11274,15055,10979,14994,10648,14932,10343,14871,9936,14803,9532,14729,9218,14645,8742,14556,8381,14461,8020,14365,7603,15273,10603,15272,10607,15267,10619,15256,10631,15231,10614,15182,10535,15118,10389,15042,10167,14963,9787,14883,9447,14800,9115,14710,8665,14615,8318,14514,7911,14411,7507,14279,7198,15314,9675,15313,9683,15309,9712,15298,9759,15277,9797,15229,9773,15166,9668,15084,9487,14995,9274,14898,8910,14800,8539,14697,8234,14590,7790,14479,7409,14367,7067,14178,6621,15337,8619,15337,8631,15333,8677,15325,8769,15305,8871,15264,8940,15202,8909,15119,8775,15022,8565,14916,8328,14804,8009,14688,7614,14569,7287,14448,6888,14321,6483,14088,6171,15350,7402,15350,7419,15347,7480,15340,7613,15322,7804,15287,7973,15229,8057,15148,8012,15046,7846,14933,7611,14810,7357,14682,7069,14552,6656,14421,6316,14251,5948,14007,5528,15356,5942,15356,5977,15353,6119,15348,6294,15332,6551,15302,6824,15249,7044,15171,7122,15070,7050,14949,6861,14818,6611,14679,6349,14538,6067,14398,5651,14189,5311,13935,4958,15359,4123,15359,4153,15356,4296,15353,4646,15338,5160,15311,5508,15263,5829,15188,6042,15088,6094,14966,6001,14826,5796,14678,5543,14527,5287,14377,4985,14133,4586,13869,4257,15360,1563,15360,1642,15358,2076,15354,2636,15341,3350,15317,4019,15273,4429,15203,4732,15105,4911,14981,4932,14836,4818,14679,4621,14517,4386,14359,4156,14083,3795,13808,3437,15360,122,15360,137,15358,285,15355,636,15344,1274,15322,2177,15281,2765,15215,3223,15120,3451,14995,3569,14846,3567,14681,3466,14511,3305,14344,3121,14037,2800,13753,2467,15360,0,15360,1,15359,21,15355,89,15346,253,15325,479,15287,796,15225,1148,15133,1492,15008,1749,14856,1882,14685,1886,14506,1783,14324,1608,13996,1398,13702,1183]);function ba(a,e){if(e===ca)return console.warn("THREE.BufferGeometryUtils.toTrianglesDrawMode(): Geometry already defined as triangles."),a;if(e===Wn||e===Ri){let t=a.getIndex();if(t===null){let s=[],r=a.getAttribute("position");if(r!==void 0){for(let o=0;o<r.count;o++)s.push(o);a.setIndex(s),t=a.getIndex()}else return console.error("THREE.BufferGeometryUtils.toTrianglesDrawMode(): Undefined position attribute. Processing not possible."),a}let n=t.count-2,i=[];if(e===Wn)for(let s=1;s<=n;s++)i.push(t.getX(0)),i.push(t.getX(s)),i.push(t.getX(s+1));else for(let s=0;s<n;s++)s%2===0?(i.push(t.getX(s)),i.push(t.getX(s+1)),i.push(t.getX(s+2))):(i.push(t.getX(s+2)),i.push(t.getX(s+1)),i.push(t.getX(s)));return i.length/3!==n&&console.error("THREE.BufferGeometryUtils.toTrianglesDrawMode(): Unable to generate correct amount of triangles."),a.setIndex(i),a.clearGroups(),a}else return console.error("THREE.BufferGeometryUtils.toTrianglesDrawMode(): Unknown draw mode:",e),a}function gl(a){let e=new Map,t=new Map,n=a.clone();return xl(a,n,function(i,s){e.set(s,i),t.set(i,s)}),n.traverse(function(i){if(!i.isSkinnedMesh)return;let s=i,r=e.get(i),o=r.skeleton.bones;s.skeleton=r.skeleton.clone(),s.bindMatrix.copy(r.bindMatrix),s.skeleton.bones=o.map(function(c){return t.get(c)}),s.bind(s.skeleton,s.bindMatrix)}),n}function xl(a,e,t){t(a,e);for(let n=0;n<a.children.length;n++)xl(a.children[n],e.children[n],t)}var Ns=class extends rt{constructor(e){super(e),this.dracoLoader=null,this.ktx2Loader=null,this.meshoptDecoder=null,this.pluginCallbacks=[],this.register(function(t){return new Ta(t)}),this.register(function(t){return new wa(t)}),this.register(function(t){return new Fa(t)}),this.register(function(t){return new Ua(t)}),this.register(function(t){return new Oa(t)}),this.register(function(t){return new Ra(t)}),this.register(function(t){return new Ca(t)}),this.register(function(t){return new Ia(t)}),this.register(function(t){return new Pa(t)}),this.register(function(t){return new Aa(t)}),this.register(function(t){return new La(t)}),this.register(function(t){return new Ea(t)}),this.register(function(t){return new Na(t)}),this.register(function(t){return new Da(t)}),this.register(function(t){return new Sa(t)}),this.register(function(t){return new Fs(t,X.EXT_MESHOPT_COMPRESSION)}),this.register(function(t){return new Fs(t,X.KHR_MESHOPT_COMPRESSION)}),this.register(function(t){return new Ba(t)})}load(e,t,n,i){let s=this,r;if(this.resourcePath!=="")r=this.resourcePath;else if(this.path!==""){let l=Et.extractUrlBase(e);r=Et.resolveURL(l,this.path)}else r=Et.extractUrlBase(e);this.manager.itemStart(e);let o=function(l){i?i(l):console.error(l),s.manager.itemError(e),s.manager.itemEnd(e)},c=new zn(this.manager);c.setPath(this.path),c.setResponseType("arraybuffer"),c.setRequestHeader(this.requestHeader),c.setWithCredentials(this.withCredentials),c.load(e,function(l){try{s.parse(l,r,function(u){t(u),s.manager.itemEnd(e)},o)}catch(u){o(u)}},n,o)}setDRACOLoader(e){return this.dracoLoader=e,this}setKTX2Loader(e){return this.ktx2Loader=e,this}setMeshoptDecoder(e){return this.meshoptDecoder=e,this}register(e){return this.pluginCallbacks.indexOf(e)===-1&&this.pluginCallbacks.push(e),this}unregister(e){return this.pluginCallbacks.indexOf(e)!==-1&&this.pluginCallbacks.splice(this.pluginCallbacks.indexOf(e),1),this}parse(e,t,n,i){let s,r={},o={},c=new TextDecoder;if(typeof e=="string")s=JSON.parse(e);else if(e instanceof ArrayBuffer)if(c.decode(new Uint8Array(e,0,4))===Sl){try{r[X.KHR_BINARY_GLTF]=new ka(e)}catch(h){i&&i(h);return}s=JSON.parse(r[X.KHR_BINARY_GLTF].content)}else s=JSON.parse(c.decode(e));else s=e;if(s.asset===void 0||s.asset.version[0]<2){i&&i(new Error("THREE.GLTFLoader: Unsupported asset. glTF versions >=2.0 are supported."));return}let l=new qa(s,{path:t||this.resourcePath||"",crossOrigin:this.crossOrigin,requestHeader:this.requestHeader,manager:this.manager,ktx2Loader:this.ktx2Loader,meshoptDecoder:this.meshoptDecoder});l.fileLoader.setRequestHeader(this.requestHeader);for(let u=0;u<this.pluginCallbacks.length;u++){let h=this.pluginCallbacks[u](l);h.name||console.error("THREE.GLTFLoader: Invalid plugin found: missing name"),o[h.name]=h,r[h.name]=!0}if(s.extensionsUsed)for(let u=0;u<s.extensionsUsed.length;++u){let h=s.extensionsUsed[u],f=s.extensionsRequired||[];switch(h){case X.KHR_MATERIALS_UNLIT:r[h]=new Ma;break;case X.KHR_DRACO_MESH_COMPRESSION:r[h]=new za(s,this.dracoLoader);break;case X.KHR_TEXTURE_TRANSFORM:r[h]=new Va;break;case X.KHR_MESH_QUANTIZATION:r[h]=new Ga;break;default:f.indexOf(h)>=0&&o[h]===void 0&&console.warn('THREE.GLTFLoader: Unknown extension "'+h+'".')}}l.setExtensions(r),l.setPlugins(o),l.parse(n,i)}parseAsync(e,t){let n=this;return new Promise(function(i,s){n.parse(e,t,i,s)})}};function kp(){let a={};return{get:function(e){return a[e]},add:function(e,t){a[e]=t},remove:function(e){delete a[e]},removeAll:function(){a={}}}}function he(a,e,t){let n=a.json.materials[e];return n.extensions&&n.extensions[t]?n.extensions[t]:null}var X={KHR_BINARY_GLTF:"KHR_binary_glTF",KHR_DRACO_MESH_COMPRESSION:"KHR_draco_mesh_compression",KHR_LIGHTS_PUNCTUAL:"KHR_lights_punctual",KHR_MATERIALS_CLEARCOAT:"KHR_materials_clearcoat",KHR_MATERIALS_DISPERSION:"KHR_materials_dispersion",KHR_MATERIALS_IOR:"KHR_materials_ior",KHR_MATERIALS_SHEEN:"KHR_materials_sheen",KHR_MATERIALS_SPECULAR:"KHR_materials_specular",KHR_MATERIALS_TRANSMISSION:"KHR_materials_transmission",KHR_MATERIALS_IRIDESCENCE:"KHR_materials_iridescence",KHR_MATERIALS_ANISOTROPY:"KHR_materials_anisotropy",KHR_MATERIALS_UNLIT:"KHR_materials_unlit",KHR_MATERIALS_VOLUME:"KHR_materials_volume",KHR_TEXTURE_BASISU:"KHR_texture_basisu",KHR_TEXTURE_TRANSFORM:"KHR_texture_transform",KHR_MESH_QUANTIZATION:"KHR_mesh_quantization",KHR_MATERIALS_EMISSIVE_STRENGTH:"KHR_materials_emissive_strength",EXT_MATERIALS_BUMP:"EXT_materials_bump",EXT_TEXTURE_WEBP:"EXT_texture_webp",EXT_TEXTURE_AVIF:"EXT_texture_avif",EXT_MESHOPT_COMPRESSION:"EXT_meshopt_compression",KHR_MESHOPT_COMPRESSION:"KHR_meshopt_compression",EXT_MESH_GPU_INSTANCING:"EXT_mesh_gpu_instancing"},Sa=class{constructor(e){this.parser=e,this.name=X.KHR_LIGHTS_PUNCTUAL,this.cache={refs:{},uses:{}}}_markDefs(){let e=this.parser,t=this.parser.json.nodes||[];for(let n=0,i=t.length;n<i;n++){let s=t[n];s.extensions&&s.extensions[this.name]&&s.extensions[this.name].light!==void 0&&e._addNodeRef(this.cache,s.extensions[this.name].light)}}_loadLight(e){let t=this.parser,n="light:"+e,i=t.cache.get(n);if(i)return i;let s=t.json,c=((s.extensions&&s.extensions[this.name]||{}).lights||[])[e],l,u=new H(16777215);c.color!==void 0&&u.setRGB(c.color[0],c.color[1],c.color[2],Be);let h=c.range!==void 0?c.range:0;switch(c.type){case"directional":l=new yi(u),l.target.position.set(0,0,-1),l.add(l.target);break;case"point":l=new _i(u),l.distance=h;break;case"spot":l=new bi(u),l.distance=h,c.spot=c.spot||{},c.spot.innerConeAngle=c.spot.innerConeAngle!==void 0?c.spot.innerConeAngle:0,c.spot.outerConeAngle=c.spot.outerConeAngle!==void 0?c.spot.outerConeAngle:Math.PI/4,l.angle=c.spot.outerConeAngle,l.penumbra=1-c.spot.innerConeAngle/c.spot.outerConeAngle,l.target.position.set(0,0,-1),l.add(l.target);break;default:throw new Error("THREE.GLTFLoader: Unexpected light type: "+c.type)}return l.position.set(0,0,0),at(l,c),c.intensity!==void 0&&(l.intensity=c.intensity),l.name=t.createUniqueName(c.name||"light_"+e),i=Promise.resolve(l),t.cache.add(n,i),i}getDependency(e,t){if(e==="light")return this._loadLight(t)}createNodeAttachment(e){let t=this,n=this.parser,s=n.json.nodes[e],o=(s.extensions&&s.extensions[this.name]||{}).light;return o===void 0?null:this._loadLight(o).then(function(c){return n._getNodeRef(t.cache,o,c)})}},Ma=class{constructor(){this.name=X.KHR_MATERIALS_UNLIT}getMaterialType(){return it}extendParams(e,t,n){let i=[];e.color=new H(1,1,1),e.opacity=1;let s=t.pbrMetallicRoughness;if(s){if(Array.isArray(s.baseColorFactor)){let r=s.baseColorFactor;e.color.setRGB(r[0],r[1],r[2],Be),e.opacity=r[3]}s.baseColorTexture!==void 0&&i.push(n.assignTexture(e,"map",s.baseColorTexture,ce))}return Promise.all(i)}},Aa=class{constructor(e){this.parser=e,this.name=X.KHR_MATERIALS_EMISSIVE_STRENGTH}extendMaterialParams(e,t){let n=he(this.parser,e,this.name);return n===null||n.emissiveStrength!==void 0&&(t.emissiveIntensity=n.emissiveStrength),Promise.resolve()}},Ta=class{constructor(e){this.parser=e,this.name=X.KHR_MATERIALS_CLEARCOAT}getMaterialType(e){return he(this.parser,e,this.name)!==null?De:null}extendMaterialParams(e,t){let n=he(this.parser,e,this.name);if(n===null)return Promise.resolve();let i=[];if(n.clearcoatFactor!==void 0&&(t.clearcoat=n.clearcoatFactor),n.clearcoatTexture!==void 0&&i.push(this.parser.assignTexture(t,"clearcoatMap",n.clearcoatTexture)),n.clearcoatRoughnessFactor!==void 0&&(t.clearcoatRoughness=n.clearcoatRoughnessFactor),n.clearcoatRoughnessTexture!==void 0&&i.push(this.parser.assignTexture(t,"clearcoatRoughnessMap",n.clearcoatRoughnessTexture)),n.clearcoatNormalTexture!==void 0&&(i.push(this.parser.assignTexture(t,"clearcoatNormalMap",n.clearcoatNormalTexture)),n.clearcoatNormalTexture.scale!==void 0)){let s=n.clearcoatNormalTexture.scale;t.clearcoatNormalScale=new $(s,s)}return Promise.all(i)}},wa=class{constructor(e){this.parser=e,this.name=X.KHR_MATERIALS_DISPERSION}getMaterialType(e){return he(this.parser,e,this.name)!==null?De:null}extendMaterialParams(e,t){let n=he(this.parser,e,this.name);return n===null||(t.dispersion=n.dispersion!==void 0?n.dispersion:0),Promise.resolve()}},Ea=class{constructor(e){this.parser=e,this.name=X.KHR_MATERIALS_IRIDESCENCE}getMaterialType(e){return he(this.parser,e,this.name)!==null?De:null}extendMaterialParams(e,t){let n=he(this.parser,e,this.name);if(n===null)return Promise.resolve();let i=[];return n.iridescenceFactor!==void 0&&(t.iridescence=n.iridescenceFactor),n.iridescenceTexture!==void 0&&i.push(this.parser.assignTexture(t,"iridescenceMap",n.iridescenceTexture)),n.iridescenceIor!==void 0&&(t.iridescenceIOR=n.iridescenceIor),t.iridescenceThicknessRange===void 0&&(t.iridescenceThicknessRange=[100,400]),n.iridescenceThicknessMinimum!==void 0&&(t.iridescenceThicknessRange[0]=n.iridescenceThicknessMinimum),n.iridescenceThicknessMaximum!==void 0&&(t.iridescenceThicknessRange[1]=n.iridescenceThicknessMaximum),n.iridescenceThicknessTexture!==void 0&&i.push(this.parser.assignTexture(t,"iridescenceThicknessMap",n.iridescenceThicknessTexture)),Promise.all(i)}},Ra=class{constructor(e){this.parser=e,this.name=X.KHR_MATERIALS_SHEEN}getMaterialType(e){return he(this.parser,e,this.name)!==null?De:null}extendMaterialParams(e,t){let n=he(this.parser,e,this.name);if(n===null)return Promise.resolve();let i=[];if(t.sheenColor=new H(0,0,0),t.sheenRoughness=0,t.sheen=1,n.sheenColorFactor!==void 0){let s=n.sheenColorFactor;t.sheenColor.setRGB(s[0],s[1],s[2],Be)}return n.sheenRoughnessFactor!==void 0&&(t.sheenRoughness=n.sheenRoughnessFactor),n.sheenColorTexture!==void 0&&i.push(this.parser.assignTexture(t,"sheenColorMap",n.sheenColorTexture,ce)),n.sheenRoughnessTexture!==void 0&&i.push(this.parser.assignTexture(t,"sheenRoughnessMap",n.sheenRoughnessTexture)),Promise.all(i)}},Ca=class{constructor(e){this.parser=e,this.name=X.KHR_MATERIALS_TRANSMISSION}getMaterialType(e){return he(this.parser,e,this.name)!==null?De:null}extendMaterialParams(e,t){let n=he(this.parser,e,this.name);if(n===null)return Promise.resolve();let i=[];return n.transmissionFactor!==void 0&&(t.transmission=n.transmissionFactor),n.transmissionTexture!==void 0&&i.push(this.parser.assignTexture(t,"transmissionMap",n.transmissionTexture)),Promise.all(i)}},Ia=class{constructor(e){this.parser=e,this.name=X.KHR_MATERIALS_VOLUME}getMaterialType(e){return he(this.parser,e,this.name)!==null?De:null}extendMaterialParams(e,t){let n=he(this.parser,e,this.name);if(n===null)return Promise.resolve();let i=[];t.thickness=n.thicknessFactor!==void 0?n.thicknessFactor:0,n.thicknessTexture!==void 0&&i.push(this.parser.assignTexture(t,"thicknessMap",n.thicknessTexture)),t.attenuationDistance=n.attenuationDistance||1/0;let s=n.attenuationColor||[1,1,1];return t.attenuationColor=new H().setRGB(s[0],s[1],s[2],Be),Promise.all(i)}},Pa=class{constructor(e){this.parser=e,this.name=X.KHR_MATERIALS_IOR}getMaterialType(e){return he(this.parser,e,this.name)!==null?De:null}extendMaterialParams(e,t){let n=he(this.parser,e,this.name);return n===null||(t.ior=n.ior!==void 0?n.ior:1.5,t.ior===0&&(t.ior=1e3)),Promise.resolve()}},La=class{constructor(e){this.parser=e,this.name=X.KHR_MATERIALS_SPECULAR}getMaterialType(e){return he(this.parser,e,this.name)!==null?De:null}extendMaterialParams(e,t){let n=he(this.parser,e,this.name);if(n===null)return Promise.resolve();let i=[];t.specularIntensity=n.specularFactor!==void 0?n.specularFactor:1,n.specularTexture!==void 0&&i.push(this.parser.assignTexture(t,"specularIntensityMap",n.specularTexture));let s=n.specularColorFactor||[1,1,1];return t.specularColor=new H().setRGB(s[0],s[1],s[2],Be),n.specularColorTexture!==void 0&&i.push(this.parser.assignTexture(t,"specularColorMap",n.specularColorTexture,ce)),Promise.all(i)}},Da=class{constructor(e){this.parser=e,this.name=X.EXT_MATERIALS_BUMP}getMaterialType(e){return he(this.parser,e,this.name)!==null?De:null}extendMaterialParams(e,t){let n=he(this.parser,e,this.name);if(n===null)return Promise.resolve();let i=[];return t.bumpScale=n.bumpFactor!==void 0?n.bumpFactor:1,n.bumpTexture!==void 0&&i.push(this.parser.assignTexture(t,"bumpMap",n.bumpTexture)),Promise.all(i)}},Na=class{constructor(e){this.parser=e,this.name=X.KHR_MATERIALS_ANISOTROPY}getMaterialType(e){return he(this.parser,e,this.name)!==null?De:null}extendMaterialParams(e,t){let n=he(this.parser,e,this.name);if(n===null)return Promise.resolve();let i=[];return n.anisotropyStrength!==void 0&&(t.anisotropy=n.anisotropyStrength),n.anisotropyRotation!==void 0&&(t.anisotropyRotation=n.anisotropyRotation),n.anisotropyTexture!==void 0&&i.push(this.parser.assignTexture(t,"anisotropyMap",n.anisotropyTexture)),Promise.all(i)}},Fa=class{constructor(e){this.parser=e,this.name=X.KHR_TEXTURE_BASISU}loadTexture(e){let t=this.parser,n=t.json,i=n.textures[e];if(!i.extensions||!i.extensions[this.name])return null;let s=i.extensions[this.name],r=t.options.ktx2Loader;if(!r){if(n.extensionsRequired&&n.extensionsRequired.indexOf(this.name)>=0)throw new Error("THREE.GLTFLoader: setKTX2Loader must be called before loading KTX2 textures");return null}return t.loadTextureImage(e,s.source,r)}},Ua=class{constructor(e){this.parser=e,this.name=X.EXT_TEXTURE_WEBP}loadTexture(e){let t=this.name,n=this.parser,i=n.json,s=i.textures[e];if(!s.extensions||!s.extensions[t])return null;let r=s.extensions[t],o=i.images[r.source],c=n.textureLoader;if(o.uri){let l=n.options.manager.getHandler(o.uri);l!==null&&(c=l)}return n.loadTextureImage(e,r.source,c)}},Oa=class{constructor(e){this.parser=e,this.name=X.EXT_TEXTURE_AVIF}loadTexture(e){let t=this.name,n=this.parser,i=n.json,s=i.textures[e];if(!s.extensions||!s.extensions[t])return null;let r=s.extensions[t],o=i.images[r.source],c=n.textureLoader;if(o.uri){let l=n.options.manager.getHandler(o.uri);l!==null&&(c=l)}return n.loadTextureImage(e,r.source,c)}},Fs=class{constructor(e,t){this.name=t,this.parser=e}loadBufferView(e){let t=this.parser.json,n=t.bufferViews[e];if(n.extensions&&n.extensions[this.name]){let i=n.extensions[this.name],s=this.parser.getDependency("buffer",i.buffer),r=this.parser.options.meshoptDecoder;if(!r||!r.supported){if(t.extensionsRequired&&t.extensionsRequired.indexOf(this.name)>=0)throw new Error("THREE.GLTFLoader: setMeshoptDecoder must be called before loading compressed files");return null}return s.then(function(o){let c=i.byteOffset||0,l=i.byteLength||0,u=i.count,h=i.byteStride,f=new Uint8Array(o,c,l);return r.decodeGltfBufferAsync?r.decodeGltfBufferAsync(u,h,f,i.mode,i.filter).then(function(d){return d.buffer}):r.ready.then(function(){let d=new ArrayBuffer(u*h);return r.decodeGltfBuffer(new Uint8Array(d),u,h,f,i.mode,i.filter),d})})}else return null}},Ba=class{constructor(e){this.name=X.EXT_MESH_GPU_INSTANCING,this.parser=e}createNodeMesh(e){let t=this.parser.json,n=t.nodes[e];if(!n.extensions||!n.extensions[this.name]||n.mesh===void 0)return null;let i=t.meshes[n.mesh];for(let l of i.primitives)if(l.mode!==qe.TRIANGLES&&l.mode!==qe.TRIANGLE_STRIP&&l.mode!==qe.TRIANGLE_FAN&&l.mode!==void 0)return null;let r=n.extensions[this.name].attributes,o=[],c={};for(let l in r)o.push(this.parser.getDependency("accessor",r[l]).then(u=>(c[l]=u,c[l])));return o.length<1?null:(o.push(this.parser.createNodeMesh(e)),Promise.all(o).then(l=>{let u=l.pop(),h=u.isGroup?u.children:[u],f=l[0].count,d=[];for(let p of h){let m=new z,b=new E,x=new pe,v=new E(1,1,1),S=new ui(p.geometry,p.material,f);for(let T=0;T<f;T++)c.TRANSLATION&&b.fromBufferAttribute(c.TRANSLATION,T),c.ROTATION&&x.fromBufferAttribute(c.ROTATION,T),c.SCALE&&v.fromBufferAttribute(c.SCALE,T),S.setMatrixAt(T,m.compose(b,x,v));let y=null;for(let T in c)if(T==="_COLOR_0"){let M=c[T];S.instanceColor=new St(M.array,M.itemSize,M.normalized)}else if(T!=="TRANSLATION"&&T!=="ROTATION"&&T!=="SCALE"){if(y===null){let A=S.geometry;y=new nt,y.name=A.name;for(let g in A.attributes)y.setAttribute(g,A.attributes[g]);for(let g in A.morphAttributes)y.morphAttributes[g]=A.morphAttributes[g];A.index!==null&&y.setIndex(A.index),y.morphTargetsRelative=A.morphTargetsRelative;for(let g of A.groups)y.addGroup(g.start,g.count,g.materialIndex);A.boundingBox!==null&&(y.boundingBox=A.boundingBox.clone()),A.boundingSphere!==null&&(y.boundingSphere=A.boundingSphere.clone()),y.drawRange.start=A.drawRange.start,y.drawRange.count=A.drawRange.count,y.userData=Object.assign({},A.userData),S.geometry=y}let M=c[T];y.setAttribute(T,new St(M.array,M.itemSize,M.normalized))}le.prototype.copy.call(S,p),this.parser.assignFinalMaterial(S),d.push(S)}return u.isGroup?(u.clear(),u.add(...d),u):d[0]}))}},Sl="glTF",Ii=12,bl={JSON:1313821514,BIN:5130562},ka=class{constructor(e){this.name=X.KHR_BINARY_GLTF,this.content=null,this.body=null;let t=new DataView(e,0,Ii),n=new TextDecoder;if(this.header={magic:n.decode(new Uint8Array(e.slice(0,4))),version:t.getUint32(4,!0),length:t.getUint32(8,!0)},this.header.magic!==Sl)throw new Error("THREE.GLTFLoader: Unsupported glTF-Binary header.");if(this.header.version<2)throw new Error("THREE.GLTFLoader: Legacy binary file detected.");let i=this.header.length-Ii,s=new DataView(e,Ii),r=0;for(;r<i;){let o=s.getUint32(r,!0);r+=4;let c=s.getUint32(r,!0);if(r+=4,c===bl.JSON){let l=new Uint8Array(e,Ii+r,o);this.content=n.decode(l)}else if(c===bl.BIN){let l=Ii+r;this.body=e.slice(l,l+o)}r+=o}if(this.content===null)throw new Error("THREE.GLTFLoader: JSON content not found.")}},za=class{constructor(e,t){if(!t)throw new Error("THREE.GLTFLoader: No DRACOLoader instance provided.");this.name=X.KHR_DRACO_MESH_COMPRESSION,this.json=e,this.dracoLoader=t,this.dracoLoader.preload()}decodePrimitive(e,t){let n=this.json,i=this.dracoLoader,s=e.extensions[this.name].bufferView,r=e.extensions[this.name].attributes,o={},c={},l={};for(let u in r){let h=Wa[u]||u.toLowerCase();o[h]=r[u]}for(let u in e.attributes){let h=Wa[u]||u.toLowerCase();if(r[u]!==void 0){let f=n.accessors[e.attributes[u]],d=Xn[f.componentType];l[h]=d.name,c[h]=f.normalized===!0}}return t.getDependency("bufferView",s).then(function(u){return new Promise(function(h,f){i.decodeDracoFile(u,function(d){for(let p in d.attributes){let m=d.attributes[p],b=c[p];b!==void 0&&(m.normalized=b)}h(d)},o,l,Be,f)})})}},Va=class{constructor(){this.name=X.KHR_TEXTURE_TRANSFORM}extendTexture(e,t){if((t.texCoord===void 0||t.texCoord===e.channel)&&t.offset===void 0&&t.rotation===void 0&&t.scale===void 0)return e;if(e=e.clone(),t.texCoord!==void 0&&(e.channel=t.texCoord),t.offset!==void 0&&e.offset.fromArray(t.offset),t.rotation!==void 0&&(e.rotation=t.rotation),t.scale!==void 0&&e.repeat.fromArray(t.scale),t.rotation!==void 0){let n=Math.cos(e.rotation),i=Math.sin(e.rotation);e.matrix.set(e.repeat.x*n,e.repeat.y*i,e.offset.x,-e.repeat.x*i,e.repeat.y*n,e.offset.y,0,0,1),e.matrixAutoUpdate=!1}return e.needsUpdate=!0,e}},Ga=class{constructor(){this.name=X.KHR_MESH_QUANTIZATION}},Us=class extends st{constructor(e,t,n,i){super(e,t,n,i)}copySampleValue_(e){let t=this.resultBuffer,n=this.sampleValues,i=this.valueSize,s=e*i*3+i;for(let r=0;r!==i;r++)t[r]=n[s+r];return t}interpolate_(e,t,n,i){let s=this.resultBuffer,r=this.sampleValues,o=this.valueSize,c=o*2,l=o*3,u=i-t,h=(n-t)/u,f=h*h,d=f*h,p=e*l,m=p-l,b=-2*d+3*f,x=d-f,v=1-b,S=x-f+h;for(let y=0;y!==o;y++){let T=r[m+y+o],M=r[m+y+c]*u,A=r[p+y+o],g=r[p+y]*u;s[y]=v*T+S*M+b*A+x*g}return s}},zp=new pe,Ha=class extends Us{interpolate_(e,t,n,i){let s=super.interpolate_(e,t,n,i);return zp.fromArray(s).normalize().toArray(s),s}},qe={FLOAT:5126,FLOAT_MAT3:35675,FLOAT_MAT4:35676,FLOAT_VEC2:35664,FLOAT_VEC3:35665,FLOAT_VEC4:35666,LINEAR:9729,REPEAT:10497,SAMPLER_2D:35678,POINTS:0,LINES:1,LINE_LOOP:2,LINE_STRIP:3,TRIANGLES:4,TRIANGLE_STRIP:5,TRIANGLE_FAN:6,UNSIGNED_BYTE:5121,UNSIGNED_SHORT:5123},Xn={5120:Int8Array,5121:Uint8Array,5122:Int16Array,5123:Uint16Array,5125:Uint32Array,5126:Float32Array},_l={9728:zt,9729:Xt,9984:Ai,9985:wi,9986:Ti,9987:hn},yl={33071:xt,33648:nn,10497:_t},_a={SCALAR:1,VEC2:2,VEC3:3,VEC4:4,MAT2:4,MAT3:9,MAT4:16},Wa={POSITION:"position",NORMAL:"normal",TANGENT:"tangent",TEXCOORD_0:"uv",TEXCOORD_1:"uv1",TEXCOORD_2:"uv2",TEXCOORD_3:"uv3",COLOR_0:"color",WEIGHTS_0:"skinWeight",JOINTS_0:"skinIndex"},qt={scale:"scale",translation:"position",rotation:"quaternion",weights:"morphTargetInfluences"},Vp={CUBICSPLINE:void 0,LINEAR:vt,STEP:yt},ya={OPAQUE:"OPAQUE",MASK:"MASK",BLEND:"BLEND"};function Gp(a){return a.DefaultMaterial===void 0&&(a.DefaultMaterial=new ln({color:16777215,emissive:0,metalness:1,roughness:1,transparent:!1,depthTest:!0,side:Si})),a.DefaultMaterial}function dn(a,e,t){for(let n in t.extensions)a[n]===void 0&&(e.userData.gltfExtensions=e.userData.gltfExtensions||{},e.userData.gltfExtensions[n]=t.extensions[n])}function at(a,e){e.extras!==void 0&&(typeof e.extras=="object"?Object.assign(a.userData,e.extras):console.warn("THREE.GLTFLoader: Ignoring primitive type .extras, "+e.extras))}function Hp(a,e,t){let n=!1,i=!1,s=!1;for(let l=0,u=e.length;l<u;l++){let h=e[l];if(h.POSITION!==void 0&&(n=!0),h.NORMAL!==void 0&&(i=!0),h.COLOR_0!==void 0&&(s=!0),n&&i&&s)break}if(!n&&!i&&!s)return Promise.resolve(a);let r=[],o=[],c=[];for(let l=0,u=e.length;l<u;l++){let h=e[l];if(n){let f=h.POSITION!==void 0?t.getDependency("accessor",h.POSITION):a.attributes.position;r.push(f)}if(i){let f=h.NORMAL!==void 0?t.getDependency("accessor",h.NORMAL):a.attributes.normal;o.push(f)}if(s){let f=h.COLOR_0!==void 0?t.getDependency("accessor",h.COLOR_0):a.attributes.color;c.push(f)}}return Promise.all([Promise.all(r),Promise.all(o),Promise.all(c)]).then(function(l){let u=l[0],h=l[1],f=l[2];return n&&(a.morphAttributes.position=u),i&&(a.morphAttributes.normal=h),s&&(a.morphAttributes.color=f),a.morphTargetsRelative=!0,a})}function Wp(a,e){if(a.updateMorphTargets(),e.weights!==void 0)for(let t=0,n=e.weights.length;t<n;t++)a.morphTargetInfluences[t]=e.weights[t];if(e.extras&&Array.isArray(e.extras.targetNames)){let t=e.extras.targetNames;if(a.morphTargetInfluences.length===t.length){a.morphTargetDictionary={};for(let n=0,i=t.length;n<i;n++)a.morphTargetDictionary[t[n]]=n}else console.warn("THREE.GLTFLoader: Invalid extras.targetNames length. Ignoring names.")}}function Xp(a){let e,t=a.extensions&&a.extensions[X.KHR_DRACO_MESH_COMPRESSION];if(t?e="draco:"+t.bufferView+":"+t.indices+":"+va(t.attributes):e=a.indices+":"+va(a.attributes)+":"+a.mode,a.targets!==void 0)for(let n=0,i=a.targets.length;n<i;n++)e+=":"+va(a.targets[n]);return e}function va(a){let e="",t=Object.keys(a).sort();for(let n=0,i=t.length;n<i;n++)e+=t[n]+":"+a[t[n]]+";";return e}function Xa(a){switch(a){case Int8Array:return 1/127;case Uint8Array:return 1/255;case Int16Array:return 1/32767;case Uint16Array:return 1/65535;default:throw new Error("THREE.GLTFLoader: Unsupported normalized accessor component type.")}}function qp(a){return a.search(/\.jpe?g($|\?)/i)>0||a.search(/^data\:image\/jpeg/)===0?"image/jpeg":a.search(/\.webp($|\?)/i)>0||a.search(/^data\:image\/webp/)===0?"image/webp":a.search(/\.ktx2($|\?)/i)>0||a.search(/^data\:image\/ktx2/)===0?"image/ktx2":"image/png"}var Kp=new z,qa=class{constructor(e={},t={}){this.json=e,this.extensions={},this.plugins={},this.options=t,this.cache=new kp,this.associations=new Map,this.primitiveCache={},this.nodeCache={},this.meshCache={refs:{},uses:{}},this.cameraCache={refs:{},uses:{}},this.lightCache={refs:{},uses:{}},this.sourceCache={},this.textureCache={},this.nodeNamesUsed={};let n=!1,i=-1,s=!1,r=-1;if(typeof navigator<"u"&&typeof navigator.userAgent<"u"){let o=navigator.userAgent;n=/^((?!chrome|android).)*safari/i.test(o)===!0;let c=o.match(/Version\/(\d+)/);i=n&&c?parseInt(c[1],10):-1,s=o.indexOf("Firefox")>-1,r=s?o.match(/Firefox\/([0-9]+)\./)[1]:-1}typeof createImageBitmap>"u"||n&&i<17||s&&r<98?this.textureLoader=new gi(this.options.manager):this.textureLoader=new vi(this.options.manager),this.textureLoader.setCrossOrigin(this.options.crossOrigin),this.textureLoader.setRequestHeader(this.options.requestHeader),this.fileLoader=new zn(this.options.manager),this.fileLoader.setResponseType("arraybuffer"),this.options.crossOrigin==="use-credentials"&&this.fileLoader.setWithCredentials(!0)}setExtensions(e){this.extensions=e}setPlugins(e){this.plugins=e}parse(e,t){let n=this,i=this.json,s=this.extensions;this.cache.removeAll(),this.nodeCache={},this._invokeAll(function(r){return r._markDefs&&r._markDefs()}),Promise.all(this._invokeAll(function(r){return r.beforeRoot&&r.beforeRoot()})).then(function(){return Promise.all([n.getDependencies("scene"),n.getDependencies("animation"),n.getDependencies("camera")])}).then(function(r){let o={scene:r[0][i.scene||0],scenes:r[0],animations:r[1],cameras:r[2],asset:i.asset,parser:n,userData:{}};return dn(s,o,i),at(o,i),Promise.all(n._invokeAll(function(c){return c.afterRoot&&c.afterRoot(o)})).then(function(){for(let c of o.scenes)c.updateMatrixWorld();e(o)})}).catch(t)}_markDefs(){let e=this.json.nodes||[],t=this.json.skins||[],n=this.json.meshes||[];for(let i=0,s=t.length;i<s;i++){let r=t[i].joints;for(let o=0,c=r.length;o<c;o++)e[r[o]].isBone=!0}for(let i=0,s=e.length;i<s;i++){let r=e[i];r.mesh!==void 0&&(this._addNodeRef(this.meshCache,r.mesh),r.skin!==void 0&&(n[r.mesh].isSkinnedMesh=!0)),r.camera!==void 0&&this._addNodeRef(this.cameraCache,r.camera)}}_addNodeRef(e,t){t!==void 0&&(e.refs[t]===void 0&&(e.refs[t]=e.uses[t]=0),e.refs[t]++)}_getNodeRef(e,t,n){if(e.refs[t]<=1)return n;let i=n.clone(),s=(r,o)=>{let c=this.associations.get(r);c!=null&&this.associations.set(o,c);for(let[l,u]of r.children.entries())s(u,o.children[l])};return s(n,i),i.name+="_instance_"+e.uses[t]++,i}_invokeOne(e){let t=Object.values(this.plugins);t.push(this);for(let n=0;n<t.length;n++){let i=e(t[n]);if(i)return i}return null}_invokeAll(e){let t=Object.values(this.plugins);t.unshift(this);let n=[];for(let i=0;i<t.length;i++){let s=e(t[i]);s&&n.push(s)}return n}getDependency(e,t){let n=e+":"+t,i=this.cache.get(n);if(!i){switch(e){case"scene":i=this.loadScene(t);break;case"node":i=this._invokeOne(function(s){return s.loadNode&&s.loadNode(t)});break;case"mesh":i=this._invokeOne(function(s){return s.loadMesh&&s.loadMesh(t)});break;case"accessor":i=this.loadAccessor(t);break;case"bufferView":i=this._invokeOne(function(s){return s.loadBufferView&&s.loadBufferView(t)});break;case"buffer":i=this.loadBuffer(t);break;case"material":i=this._invokeOne(function(s){return s.loadMaterial&&s.loadMaterial(t)});break;case"texture":i=this._invokeOne(function(s){return s.loadTexture&&s.loadTexture(t)});break;case"skin":i=this.loadSkin(t);break;case"animation":i=this._invokeOne(function(s){return s.loadAnimation&&s.loadAnimation(t)});break;case"camera":i=this.loadCamera(t);break;default:if(i=this._invokeOne(function(s){return s!=this&&s.getDependency&&s.getDependency(e,t)}),!i)throw new Error("Unknown type: "+e);break}this.cache.add(n,i)}return i}getDependencies(e){let t=this.cache.get(e);if(!t){let n=this,i=this.json[e+(e==="mesh"?"es":"s")]||[];t=Promise.all(i.map(function(s,r){return n.getDependency(e,r)})),this.cache.add(e,t)}return t}loadBuffer(e){let t=this.json.buffers[e],n=this.fileLoader;if(t.type&&t.type!=="arraybuffer")throw new Error("THREE.GLTFLoader: "+t.type+" buffer type is not supported.");if(t.uri===void 0&&e===0)return Promise.resolve(this.extensions[X.KHR_BINARY_GLTF].body);let i=this.options;return new Promise(function(s,r){n.load(Et.resolveURL(t.uri,i.path),s,void 0,function(){r(new Error('THREE.GLTFLoader: Failed to load buffer "'+t.uri+'".'))})})}loadBufferView(e){let t=this.json.bufferViews[e];return this.getDependency("buffer",t.buffer).then(function(n){let i=t.byteLength||0,s=t.byteOffset||0;return n.slice(s,s+i)})}loadAccessor(e){let t=this,n=this.json,i=this.json.accessors[e];if(i.bufferView===void 0&&i.sparse===void 0){let r=_a[i.type],o=Xn[i.componentType],c=i.normalized===!0,l=new o(i.count*r);return Promise.resolve(new ae(l,r,c))}let s=[];return i.bufferView!==void 0?s.push(this.getDependency("bufferView",i.bufferView)):s.push(null),i.sparse!==void 0&&(s.push(this.getDependency("bufferView",i.sparse.indices.bufferView)),s.push(this.getDependency("bufferView",i.sparse.values.bufferView))),Promise.all(s).then(function(r){let o=r[0],c=_a[i.type],l=Xn[i.componentType],u=l.BYTES_PER_ELEMENT,h=u*c,f=i.byteOffset||0,d=i.bufferView!==void 0?n.bufferViews[i.bufferView].byteStride:void 0,p=i.normalized===!0,m,b;if(d&&d!==h){let x=Math.floor(f/d),v="InterleavedBuffer:"+i.bufferView+":"+i.componentType+":"+x+":"+i.count,S=t.cache.get(v);S||(m=new l(o,x*d,i.count*d/u),S=new Fn(m,d/u),t.cache.add(v,S)),b=new Un(S,c,f%d/u,p)}else o===null?m=new l(i.count*c):m=new l(o,f,i.count*c),b=new ae(m,c,p);if(i.sparse!==void 0){let x=_a.SCALAR,v=Xn[i.sparse.indices.componentType],S=i.sparse.indices.byteOffset||0,y=i.sparse.values.byteOffset||0,T=new v(r[1],S,i.sparse.count*x),M=new l(r[2],y,i.sparse.count*c);o!==null&&(b=new ae(b.array.slice(),b.itemSize,b.normalized)),b.normalized=!1;for(let A=0,g=T.length;A<g;A++){let w=T[A];if(b.setX(w,M[A*c]),c>=2&&b.setY(w,M[A*c+1]),c>=3&&b.setZ(w,M[A*c+2]),c>=4&&b.setW(w,M[A*c+3]),c>=5)throw new Error("THREE.GLTFLoader: Unsupported itemSize in sparse BufferAttribute.")}b.normalized=p}return b})}loadTexture(e){let t=this.json,n=this.options,s=t.textures[e].source,r=t.images[s],o=this.textureLoader;if(r.uri){let c=n.manager.getHandler(r.uri);c!==null&&(o=c)}return this.loadTextureImage(e,s,o)}loadTextureImage(e,t,n){let i=this,s=this.json,r=s.textures[e],o=s.images[t],c=(o.uri||o.bufferView)+":"+r.sampler;if(this.textureCache[c])return this.textureCache[c];let l=this.loadImageSource(t,n).then(function(u){u.flipY=!1,u.name=r.name||o.name||"",u.name===""&&typeof o.uri=="string"&&o.uri.startsWith("data:image/")===!1&&(u.name=o.uri);let f=(s.samplers||{})[r.sampler]||{};return u.magFilter=_l[f.magFilter]||Xt,u.minFilter=_l[f.minFilter]||hn,u.wrapS=yl[f.wrapS]||_t,u.wrapT=yl[f.wrapT]||_t,u.generateMipmaps=!u.isCompressedTexture&&u.minFilter!==zt&&u.minFilter!==Xt,i.associations.set(u,{textures:e}),u}).catch(function(){return null});return this.textureCache[c]=l,l}loadImageSource(e,t){let n=this,i=this.json,s=this.options;if(this.sourceCache[e]!==void 0)return this.sourceCache[e].then(h=>h.clone());let r=i.images[e],o=self.URL||self.webkitURL,c=r.uri||"",l=!1;if(r.bufferView!==void 0)c=n.getDependency("bufferView",r.bufferView).then(function(h){l=!0;let f=new Blob([h],{type:r.mimeType});return c=o.createObjectURL(f),c});else if(r.uri===void 0)throw new Error("THREE.GLTFLoader: Image "+e+" is missing URI and bufferView");let u=Promise.resolve(c).then(function(h){return new Promise(function(f,d){let p=f;t.isImageBitmapLoader===!0&&(p=function(m){let b=new We(m);b.needsUpdate=!0,f(b)}),t.load(Et.resolveURL(h,s.path),p,void 0,d)})}).then(function(h){return l===!0&&o.revokeObjectURL(c),at(h,r),h.userData.mimeType=r.mimeType||qp(r.uri),h}).catch(function(h){throw console.error("THREE.GLTFLoader: Couldn't load texture",c),h});return this.sourceCache[e]=u,u}assignTexture(e,t,n,i){let s=this;return this.getDependency("texture",n.index).then(function(r){if(!r)return null;if(n.texCoord!==void 0&&n.texCoord>0&&(r=r.clone(),r.channel=n.texCoord),s.extensions[X.KHR_TEXTURE_TRANSFORM]){let o=n.extensions!==void 0?n.extensions[X.KHR_TEXTURE_TRANSFORM]:void 0;if(o){let c=s.associations.get(r);r=s.extensions[X.KHR_TEXTURE_TRANSFORM].extendTexture(r,o),s.associations.set(r,c)}}return i!==void 0&&(r.colorSpace=i),e[t]=r,r})}assignFinalMaterial(e){let t=e.geometry,n=e.material,i=t.attributes.tangent===void 0,s=t.attributes.color!==void 0,r=t.attributes.normal===void 0;if(e.isPoints){let o="PointsMaterial:"+n.uuid,c=this.cache.get(o);c||(c=new kn,$e.prototype.copy.call(c,n),c.color.copy(n.color),c.map=n.map,c.sizeAttenuation=!1,this.cache.add(o,c)),n=c}else if(e.isLine){let o="LineBasicMaterial:"+n.uuid,c=this.cache.get(o);c||(c=new Bn,$e.prototype.copy.call(c,n),c.color.copy(n.color),c.map=n.map,this.cache.add(o,c)),n=c}if(i||s||r){let o="ClonedMaterial:"+n.uuid+":";i&&(o+="derivative-tangents:"),s&&(o+="vertex-colors:"),r&&(o+="flat-shading:");let c=this.cache.get(o);c||(c=n.clone(),s&&(c.vertexColors=!0),r&&(c.flatShading=!0),i&&(c.normalScale&&(c.normalScale.y*=-1),c.clearcoatNormalScale&&(c.clearcoatNormalScale.y*=-1)),this.cache.add(o,c),this.associations.set(c,this.associations.get(n))),n=c}e.material=n}getMaterialType(){return ln}loadMaterial(e){let t=this,n=this.json,i=this.extensions,s=n.materials[e],r,o={},c=s.extensions||{},l=[];if(c[X.KHR_MATERIALS_UNLIT]){let h=i[X.KHR_MATERIALS_UNLIT];r=h.getMaterialType(),l.push(h.extendParams(o,s,t))}else{let h=s.pbrMetallicRoughness||{};if(o.color=new H(1,1,1),o.opacity=1,Array.isArray(h.baseColorFactor)){let f=h.baseColorFactor;o.color.setRGB(f[0],f[1],f[2],Be),o.opacity=f[3]}h.baseColorTexture!==void 0&&l.push(t.assignTexture(o,"map",h.baseColorTexture,ce)),o.metalness=h.metallicFactor!==void 0?h.metallicFactor:1,o.roughness=h.roughnessFactor!==void 0?h.roughnessFactor:1,h.metallicRoughnessTexture!==void 0&&(l.push(t.assignTexture(o,"metalnessMap",h.metallicRoughnessTexture)),l.push(t.assignTexture(o,"roughnessMap",h.metallicRoughnessTexture))),r=this._invokeOne(function(f){return f.getMaterialType&&f.getMaterialType(e)}),l.push(Promise.all(this._invokeAll(function(f){return f.extendMaterialParams&&f.extendMaterialParams(e,o)})))}s.doubleSided===!0&&(o.side=Mi);let u=s.alphaMode||ya.OPAQUE;if(u===ya.BLEND?(o.transparent=!0,o.depthWrite=!1):(o.transparent=!1,u===ya.MASK&&(o.alphaTest=s.alphaCutoff!==void 0?s.alphaCutoff:.5)),s.normalTexture!==void 0&&r!==it&&(l.push(t.assignTexture(o,"normalMap",s.normalTexture)),o.normalScale=new $(1,1),s.normalTexture.scale!==void 0)){let h=s.normalTexture.scale;o.normalScale.set(h,h)}if(s.occlusionTexture!==void 0&&r!==it&&(l.push(t.assignTexture(o,"aoMap",s.occlusionTexture)),s.occlusionTexture.strength!==void 0&&(o.aoMapIntensity=s.occlusionTexture.strength)),s.emissiveFactor!==void 0&&r!==it){let h=s.emissiveFactor;o.emissive=new H().setRGB(h[0],h[1],h[2],Be)}return s.emissiveTexture!==void 0&&r!==it&&l.push(t.assignTexture(o,"emissiveMap",s.emissiveTexture,ce)),Promise.all(l).then(function(){let h=new r(o);return s.name&&(h.name=s.name),at(h,s),t.associations.set(h,{materials:e}),s.extensions&&dn(i,h,s),h})}createUniqueName(e){let t=j.sanitizeNodeName(e||"");return t in this.nodeNamesUsed?t+"_"+ ++this.nodeNamesUsed[t]:(this.nodeNamesUsed[t]=0,t)}loadGeometries(e){let t=this,n=this.extensions,i=this.primitiveCache;function s(o){return n[X.KHR_DRACO_MESH_COMPRESSION].decodePrimitive(o,t).then(function(c){return vl(c,o,t)})}let r=[];for(let o=0,c=e.length;o<c;o++){let l=e[o],u=Xp(l),h=i[u];if(h)r.push(h.promise);else{let f;l.extensions&&l.extensions[X.KHR_DRACO_MESH_COMPRESSION]?f=s(l):f=vl(new nt,l,t),l.mode===qe.TRIANGLE_STRIP?f=f.then(d=>ba(d,Ri)):l.mode===qe.TRIANGLE_FAN&&(f=f.then(d=>ba(d,Wn))),i[u]={primitive:l,promise:f},r.push(f)}}return Promise.all(r)}loadMesh(e){let t=this,n=this.json,i=this.extensions,s=n.meshes[e],r=s.primitives,o=[];for(let c=0,l=r.length;c<l;c++){let u=r[c].material===void 0?Gp(this.cache):this.getDependency("material",r[c].material);o.push(u)}return o.push(t.loadGeometries(r)),Promise.all(o).then(async function(c){let l=c.slice(0,c.length-1),u=c[c.length-1],h=[];for(let d=0,p=u.length;d<p;d++){let m=u[d],b=r[d],x,v=l[d];if(b.mode===qe.TRIANGLES||b.mode===qe.TRIANGLE_STRIP||b.mode===qe.TRIANGLE_FAN||b.mode===void 0){let S=s.isSkinnedMesh===!0,y=m.hasAttribute("skinIndex")&&m.hasAttribute("skinWeight");S&&y===!1&&console.warn("THREE.GLTFLoader: Missing skinIndex or skinWeight attributes. Skinning disabled."),x=S&&y?new oi(m,v):new Gt(m,v),x.isSkinnedMesh===!0&&x.normalizeSkinWeights()}else if(b.mode===qe.LINES)x=new hi(m,v);else if(b.mode===qe.LINE_STRIP)x=new cn(m,v);else if(b.mode===qe.LINE_LOOP)x=new fi(m,v);else if(b.mode===qe.POINTS)x=new di(m,v);else throw new Error("THREE.GLTFLoader: Primitive mode unsupported: "+b.mode);Object.keys(x.geometry.morphAttributes).length>0&&Wp(x,s),x.name=t.createUniqueName(s.name||"mesh_"+e),at(x,s),b.extensions&&dn(i,x,b),t.assignFinalMaterial(x),h.push(x)}for(let d=0,p=h.length;d<p;d++)t.associations.set(h[d],{meshes:e,primitives:d});if(h.length===1)return s.extensions&&dn(i,h[0],s),h[0];let f=new rn;s.extensions&&dn(i,f,s),t.associations.set(f,{meshes:e});for(let d=0,p=h.length;d<p;d++)f.add(h[d]);return f})}loadCamera(e){let t,n=this.json.cameras[e],i=n[n.type];if(!i){console.warn("THREE.GLTFLoader: Missing camera parameters.");return}return n.type==="perspective"?t=new un(fn.radToDeg(i.yfov),i.aspectRatio||1,i.znear||1,i.zfar||2e6):n.type==="orthographic"&&(t=new Hn(-i.xmag,i.xmag,i.ymag,-i.ymag,i.znear,i.zfar)),n.name&&(t.name=this.createUniqueName(n.name)),at(t,n),Promise.resolve(t)}loadSkin(e){let t=this.json.skins[e],n=[];for(let i=0,s=t.joints.length;i<s;i++)n.push(this._loadNodeShallow(t.joints[i]));return t.inverseBindMatrices!==void 0?n.push(this.getDependency("accessor",t.inverseBindMatrices)):n.push(null),Promise.all(n).then(function(i){let s=i.pop(),r=i,o=[],c=[];for(let l=0,u=r.length;l<u;l++){let h=r[l];if(h){o.push(h);let f=new z;s!==null&&f.fromArray(s.array,l*16),c.push(f)}else console.warn('THREE.GLTFLoader: Joint "%s" could not be found.',t.joints[l])}return new li(o,c)})}loadAnimation(e){let t=this.json,n=this,i=t.animations[e],s=i.name?i.name:"animation_"+e,r=[],o=[],c=[],l=[],u=[];for(let h=0,f=i.channels.length;h<f;h++){let d=i.channels[h],p=i.samplers[d.sampler],m=d.target,b=m.node,x=i.parameters!==void 0?i.parameters[p.input]:p.input,v=i.parameters!==void 0?i.parameters[p.output]:p.output;m.node!==void 0&&(r.push(this.getDependency("node",b)),o.push(this.getDependency("accessor",x)),c.push(this.getDependency("accessor",v)),l.push(p),u.push(m))}return Promise.all([Promise.all(r),Promise.all(o),Promise.all(c),Promise.all(l),Promise.all(u)]).then(function(h){let f=h[0],d=h[1],p=h[2],m=h[3],b=h[4],x=[];for(let S=0,y=f.length;S<y;S++){let T=f[S],M=d[S],A=p[S],g=m[S],w=b[S];if(T===void 0)continue;T.updateMatrix&&T.updateMatrix();let R=n._createAnimationTracks(T,M,A,g,w);if(R)for(let C=0;C<R.length;C++)x.push(R[C])}let v=new mi(s,void 0,x);return at(v,i),v})}createNodeMesh(e){let t=this.json,n=this,i=t.nodes[e];return i.mesh===void 0?null:n.getDependency("mesh",i.mesh).then(function(s){let r=n._getNodeRef(n.meshCache,i.mesh,s);return i.weights!==void 0&&r.traverse(function(o){if(o.isMesh)for(let c=0,l=i.weights.length;c<l;c++)o.morphTargetInfluences[c]=i.weights[c]}),r})}loadNode(e){let t=this.json,n=this,i=t.nodes[e],s=n._loadNodeShallow(e),r=[],o=i.children||[];for(let l=0,u=o.length;l<u;l++)r.push(n.getDependency("node",o[l]));let c=i.skin===void 0?Promise.resolve(null):n.getDependency("skin",i.skin);return Promise.all([s,Promise.all(r),c]).then(function(l){let u=l[0],h=l[1],f=l[2];f!==null&&u.traverse(function(d){d.isSkinnedMesh&&d.bind(f,Kp)});for(let d=0,p=h.length;d<p;d++)u.add(h[d]);if(u.userData.pivot!==void 0&&h.length>0){let d=u.userData.pivot,p=h[0];u.pivot=new E().fromArray(d),u.position.x-=d[0],u.position.y-=d[1],u.position.z-=d[2],p.position.set(0,0,0),delete u.userData.pivot}return u})}_loadNodeShallow(e){let t=this.json,n=this.extensions,i=this;if(this.nodeCache[e]!==void 0)return this.nodeCache[e];let s=t.nodes[e],r=s.name?i.createUniqueName(s.name):"",o=[],c=i._invokeOne(function(l){return l.createNodeMesh&&l.createNodeMesh(e)});return c&&o.push(c),s.camera!==void 0&&o.push(i.getDependency("camera",s.camera).then(function(l){return i._getNodeRef(i.cameraCache,s.camera,l)})),i._invokeAll(function(l){return l.createNodeAttachment&&l.createNodeAttachment(e)}).forEach(function(l){o.push(l)}),this.nodeCache[e]=Promise.all(o).then(function(l){let u;if(s.isBone===!0?u=new On:l.length>1?u=new rn:l.length===1?u=l[0]:u=new le,u!==l[0])for(let h=0,f=l.length;h<f;h++)u.add(l[h]);if(s.name&&(u.userData.name=s.name,u.name=r),at(u,s),s.extensions&&dn(n,u,s),s.matrix!==void 0){let h=new z;h.fromArray(s.matrix),u.applyMatrix4(h)}else s.translation!==void 0&&u.position.fromArray(s.translation),s.rotation!==void 0&&u.quaternion.fromArray(s.rotation),s.scale!==void 0&&u.scale.fromArray(s.scale);if(!i.associations.has(u))i.associations.set(u,{});else if(s.mesh!==void 0&&i.meshCache.refs[s.mesh]>1){let h=i.associations.get(u);i.associations.set(u,{...h})}return i.associations.get(u).nodes=e,u}),this.nodeCache[e]}loadScene(e){let t=this.extensions,n=this.json.scenes[e],i=this,s=new rn;n.name&&(s.name=i.createUniqueName(n.name)),at(s,n),n.extensions&&dn(t,s,n);let r=n.nodes||[],o=[];for(let c=0,l=r.length;c<l;c++)o.push(i.getDependency("node",r[c]));return Promise.all(o).then(function(c){for(let u=0,h=c.length;u<h;u++){let f=c[u];f.parent!==null?s.add(gl(f)):s.add(f)}let l=u=>{let h=new Map;for(let[f,d]of i.associations)(f instanceof $e||f instanceof We)&&h.set(f,d);return u.traverse(f=>{let d=i.associations.get(f);d!=null&&h.set(f,d)}),h};return i.associations=l(s),s})}_createAnimationTracks(e,t,n,i,s){let r=[],o=e.name?e.name:e.uuid,c=[];function l(d){d.morphTargetInfluences&&c.push(d.name?d.name:d.uuid)}qt[s.path]===qt.weights?(l(e),e.isGroup&&e.children.forEach(l)):c.push(o);let u;switch(qt[s.path]){case qt.weights:u=At;break;case qt.rotation:u=Tt;break;case qt.translation:case qt.scale:u=Wt;break;default:n.itemSize===1?u=At:u=Wt;break}let h=i.interpolation!==void 0?Vp[i.interpolation]:vt,f=this._getArrayFromAccessor(n);for(let d=0,p=c.length;d<p;d++){let m=new u(c[d]+"."+qt[s.path],t.array,f,h);i.interpolation==="CUBICSPLINE"&&this._createCubicSplineTrackInterpolant(m),r.push(m)}return r}_getArrayFromAccessor(e){let t=e.array;if(e.normalized){let n=Xa(t.constructor),i=new Float32Array(t.length);for(let s=0,r=t.length;s<r;s++)i[s]=t[s]*n;t=i}return t}_createCubicSplineTrackInterpolant(e){e.createInterpolant=function(n){let i=this instanceof Tt?Ha:Us;return new i(this.times,this.values,this.getValueSize()/3,n)},e.createInterpolant.isInterpolantFactoryMethodGLTFCubicSpline=!0}};function Yp(a,e,t){let n=e.attributes,i=new ze;if(n.POSITION!==void 0){let o=t.json.accessors[n.POSITION],c=o.min,l=o.max;if(c!==void 0&&l!==void 0){if(i.set(new E(c[0],c[1],c[2]),new E(l[0],l[1],l[2])),o.normalized){let u=Xa(Xn[o.componentType]);i.min.multiplyScalar(u),i.max.multiplyScalar(u)}}else{console.warn("THREE.GLTFLoader: Missing min/max properties for accessor POSITION.");return}}else return;let s=e.targets;if(s!==void 0){let o=new E,c=new E;for(let l=0,u=s.length;l<u;l++){let h=s[l];if(h.POSITION!==void 0){let f=t.json.accessors[h.POSITION],d=f.min,p=f.max;if(d!==void 0&&p!==void 0){if(c.setX(Math.max(Math.abs(d[0]),Math.abs(p[0]))),c.setY(Math.max(Math.abs(d[1]),Math.abs(p[1]))),c.setZ(Math.max(Math.abs(d[2]),Math.abs(p[2]))),f.normalized){let m=Xa(Xn[f.componentType]);c.multiplyScalar(m)}o.max(c)}else console.warn("THREE.GLTFLoader: Missing min/max properties for accessor POSITION.")}}i.expandByVector(o)}a.boundingBox=i;let r=new Le;i.getCenter(r.center),r.radius=i.min.distanceTo(i.max)/2,a.boundingSphere=r}function vl(a,e,t){let n=e.attributes,i=[];function s(r,o){return t.getDependency("accessor",r).then(function(c){a.setAttribute(o,c)})}for(let r in n){let o=Wa[r]||r.toLowerCase();o in a.attributes||i.push(s(n[r],o))}if(e.indices!==void 0&&!a.index){let r=t.getDependency("accessor",e.indices).then(function(o){a.setIndex(o)});i.push(r)}return _e.workingColorSpace!==Be&&"COLOR_0"in n&&console.warn(`THREE.GLTFLoader: Converting vertex colors from "srgb-linear" to "${_e.workingColorSpace}" not supported.`),at(a,e),Yp(a,e,t),Promise.all(i).then(function(){return e.targets!==void 0?Hp(a,e.targets,t):a})}var Ml=(function(){var a="b9H79Tebbbe8Fv9Gbb9Gvuuuuueu9Giuuub9Geueu9Giuuueuixkbeeeddddillviebeoweuecj:Gdkr;Neqo9TW9T9VV95dbH9F9F939H79T9F9J9H229F9Jt9VV7bb8A9TW79O9V9Wt9F9KW9J9V9KW9wWVtW949c919M9MWVbeY9TW79O9V9Wt9F9KW9J9V9KW69U9KW949c919M9MWVbdE9TW79O9V9Wt9F9KW9J9V9KW69U9KW949tWG91W9U9JWbiL9TW79O9V9Wt9F9KW9J9V9KWS9P2tWV9p9JtblK9TW79O9V9Wt9F9KW9J9V9KWS9P2tWV9r919HtbvL9TW79O9V9Wt9F9KW9J9V9KWS9P2tWVT949WboY9TW79O9V9Wt9F9KW9J9V9KWS9P2tWVJ9V29VVbrl79IV9Rbwq:VZkdbk:XYi5ud9:du8Jjjjjbcj;kb9Rgv8Kjjjjbc9:hodnalTmbcuhoaiRbbgrc;WeGc:Ge9hmbarcsGgwce0mbc9:hoalcufadcd4cbawEgDadfgrcKcaawEgqaraq0Egk6mbaicefhxcj;abad9Uc;WFbGcjdadca0EhmaialfgPar9Rgoadfhsavaoadz:jjjjbgzceVhHcbhOdndninaeaO9nmeaPax9RaD6mdamaeaO9RaOamfgoae6EgAcsfglc9WGhCabaOad2fhXaAcethQaxaDfhiaOaeaoaeao6E9RhLalcl4cifcd4hKazcj;cbfaAfhYcbh8AazcjdfhEaHh3incbh5dnawTmbaxa8Acd4fRbbh5kcbh8Eazcj;cbfhqinaih8Fdndndndna5a8Ecet4ciGgoc9:fPdebdkaPa8F9RaA6mrazcj;cbfa8EaA2fa8FaAz:jjjjb8Aa8FaAfhixdkazcj;cbfa8EaA2fcbaAz:kjjjb8Aa8FhixekaPa8F9RaK6mva8FaKfhidnaCTmbaPai9RcK6mbaocdtc:q:G:cjbfcj:G:cjbawEhaczhrcbhlinargoc9Wfghaqfhrdndndndndndnaaa8Fahco4fRbbalcoG4ciGcdtfydbPDbedvivvvlvkar9cb83bwar9cb83bbxlkarcbaiRbdai8Xbb9c:c:qj:bw9:9c:q;c1:I1e:d9c:b:c:e1z9:gg9cjjjjjz:dg8J9qE86bbaqaofgrcGfcbaicdfa8J9c8N1:NfghRbbag9cjjjjjw:dg8J9qE86bbarcVfcbaha8J9c8M1:NfghRbbag9cjjjjjl:dg8J9qE86bbarc7fcbaha8J9c8L1:NfghRbbag9cjjjjjd:dg8J9qE86bbarctfcbaha8J9c8K1:NfghRbbag9cjjjjje:dg8J9qE86bbarc91fcbaha8J9c8J1:NfghRbbag9cjjjj;ab:dg8J9qE86bbarc4fcbaha8J9cg1:NfghRbbag9cjjjja:dg8J9qE86bbarc93fcbaha8J9ch1:NfghRbbag9cjjjjz:dgg9qE86bbarc94fcbahag9ca1:NfghRbbai8Xbe9c:c:qj:bw9:9c:q;c1:I1e:d9c:b:c:e1z9:gg9cjjjjjz:dg8J9qE86bbarc95fcbaha8J9c8N1:NfgiRbbag9cjjjjjw:dg8J9qE86bbarc96fcbaia8J9c8M1:NfgiRbbag9cjjjjjl:dg8J9qE86bbarc97fcbaia8J9c8L1:NfgiRbbag9cjjjjjd:dg8J9qE86bbarc98fcbaia8J9c8K1:NfgiRbbag9cjjjjje:dg8J9qE86bbarc99fcbaia8J9c8J1:NfgiRbbag9cjjjj;ab:dg8J9qE86bbarc9:fcbaia8J9cg1:NfgiRbbag9cjjjja:dg8J9qE86bbarcufcbaia8J9ch1:NfgiRbbag9cjjjjz:dgg9qE86bbaiag9ca1:NfhixikaraiRblaiRbbghco4g8Ka8KciSg8KE86bbaqaofgrcGfaiclfa8Kfg8KRbbahcl4ciGg8La8LciSg8LE86bbarcVfa8Ka8Lfg8KRbbahcd4ciGg8La8LciSg8LE86bbarc7fa8Ka8Lfg8KRbbahciGghahciSghE86bbarctfa8Kahfg8KRbbaiRbeghco4g8La8LciSg8LE86bbarc91fa8Ka8Lfg8KRbbahcl4ciGg8La8LciSg8LE86bbarc4fa8Ka8Lfg8KRbbahcd4ciGg8La8LciSg8LE86bbarc93fa8Ka8Lfg8KRbbahciGghahciSghE86bbarc94fa8Kahfg8KRbbaiRbdghco4g8La8LciSg8LE86bbarc95fa8Ka8Lfg8KRbbahcl4ciGg8La8LciSg8LE86bbarc96fa8Ka8Lfg8KRbbahcd4ciGg8La8LciSg8LE86bbarc97fa8Ka8Lfg8KRbbahciGghahciSghE86bbarc98fa8KahfghRbbaiRbigico4g8Ka8KciSg8KE86bbarc99faha8KfghRbbaicl4ciGg8Ka8KciSg8KE86bbarc9:faha8KfghRbbaicd4ciGg8Ka8KciSg8KE86bbarcufaha8KfgrRbbaiciGgiaiciSgiE86bbaraifhixdkaraiRbwaiRbbghcl4g8Ka8KcsSg8KE86bbaqaofgrcGfaicwfa8Kfg8KRbbahcsGghahcsSghE86bbarcVfa8KahfghRbbaiRbeg8Kcl4g8La8LcsSg8LE86bbarc7faha8LfghRbba8KcsGg8Ka8KcsSg8KE86bbarctfaha8KfghRbbaiRbdg8Kcl4g8La8LcsSg8LE86bbarc91faha8LfghRbba8KcsGg8Ka8KcsSg8KE86bbarc4faha8KfghRbbaiRbig8Kcl4g8La8LcsSg8LE86bbarc93faha8LfghRbba8KcsGg8Ka8KcsSg8KE86bbarc94faha8KfghRbbaiRblg8Kcl4g8La8LcsSg8LE86bbarc95faha8LfghRbba8KcsGg8Ka8KcsSg8KE86bbarc96faha8KfghRbbaiRbvg8Kcl4g8La8LcsSg8LE86bbarc97faha8LfghRbba8KcsGg8Ka8KcsSg8KE86bbarc98faha8KfghRbbaiRbog8Kcl4g8La8LcsSg8LE86bbarc99faha8LfghRbba8KcsGg8Ka8KcsSg8KE86bbarc9:faha8KfghRbbaiRbrgicl4g8Ka8KcsSg8KE86bbarcufaha8KfgrRbbaicsGgiaicsSgiE86bbaraifhixekarai8Pbw83bwarai8Pbb83bbaiczfhikdnaoaC9pmbalcdfhlaoczfhraPai9RcL0mekkaoaC6moaimexokaCmva8FTmvkaqaAfhqa8Ecefg8Ecl9hmbkdndndndnawTmbasa8Acd4fRbbgociGPlbedrbkaATmdaza8Afh8Fazcj;cbfhhcbh8EaEhaina8FRbbhraahocbhlinaoahalfRbbgqce4cbaqceG9R7arfgr86bbaoadfhoaAalcefgl9hmbkaacefhaa8Fcefh8FahaAfhha8Ecefg8Ecl9hmbxikkaATmeaza8Afhaazcj;cbfhhcbhoceh8EaYh8FinaEaofhlaa8Vbbhrcbhoinala8FaofRbbcwtahaofRbbgqVc;:FiGce4cbaqceG9R7arfgr87bbaladfhlaLaocefgofmbka8FaQfh8FcdhoaacdfhaahaQfhha8EceGhlcbh8EalmbxdkkaATmbaocl4h8Eaza8AfRbbhqcwhoa3hlinalRbbaotaqVhqalcefhlaocwfgoca9hmbkcbhhaEh8FaYhainazcj;cbfahfRbbhrcwhoaahlinalRbbaotarVhralaAfhlaocwfgoca9hmbkara8E94aq7hqcbhoa8Fhlinalaqao486bbalcefhlaocwfgoca9hmbka8Fadfh8FaacefhaahcefghaA9hmbkkaEclfhEa3clfh3a8Aclfg8Aad6mbkaXazcjdfaAad2z:jjjjb8AazazcjdfaAcufad2fadz:jjjjb8AaAaOfhOaihxaimbkc9:hoxdkcbc99aPax9RakSEhoxekc9:hokavcj;kbf8Kjjjjbaok:ysezu8Jjjjjbc;ae9Rgv8Kjjjjbc9:hodnalaeci9UgrcHf6mbcuhoaiRbbgwc;WeGc;Ge9hmbawcsGgDce0mbavc;abfcFecjez:kjjjb8Aav9cu83iUav9cu83i8Wav9cu83iyav9cu83iaav9cu83iKav9cu83izav9cu83iwav9cu83ibaialfc9WfhqaicefgwarfhldnaeTmbcmcsaDceSEhkcbhxcbhmcbhrcbhicbhoindnalaq9nmbc9:hoxikdndnawRbbgDc;Ve0mbavc;abfaoaDcu7gPcl4fcsGcitfgsydlhzasydbhHdndnaDcsGgsak9pmbavaiaPfcsGcdtfydbaxasEhDaxasTgOfhxxekdndnascsSmbcehOasc987asamffcefhDxekalcefhDal8SbbgscFeGhPdndnascu9mmbaDhlxekalcvfhlaPcFbGhPcrhsdninaD8SbbgOcFbGastaPVhPaOcu9kmeaDcefhDascrfgsc8J9hmbxdkkaDcefhlkcehOaPce4cbaPceG9R7amfhDkaDhmkavc;abfaocitfgsaDBdbasazBdlavaicdtfaDBdbavc;abfaocefcsGcitfgsaHBdbasaDBdlaocdfhoaOaifhidnadcd9hmbabarcetfgsaH87ebasclfaD87ebascdfaz87ebxdkabarcdtfgsaHBdbascwfaDBdbasclfazBdbxekdnaDcpe0mbavaiaqaDcsGfRbbgscl4gP9RcsGcdtfydbaxcefgOaPEhDavaias9RcsGcdtfydbaOaPTgzfgOascsGgPEhsaPThPdndnadcd9hmbabarcetfgHax87ebaHclfas87ebaHcdfaD87ebxekabarcdtfgHaxBdbaHcwfasBdbaHclfaDBdbkavaicdtfaxBdbavc;abfaocitfgHaDBdbaHaxBdlavaicefgicsGcdtfaDBdbavc;abfaocefcsGcitfgHasBdbaHaDBdlavaiazfgicsGcdtfasBdbavc;abfaocdfcsGcitfgDaxBdbaDasBdlaocifhoaiaPfhiaOaPfhxxekaxcbalRbbgsEgHaDc;:eSgDfhOascsGhAdndnascl4gCmbaOcefhzxekaOhzavaiaC9RcsGcdtfydbhOkdndnaAmbazcefhxxekazhxavaias9RcsGcdtfydbhzkdndnaDTmbalcefhDxekalcdfhDal8SbegPcFeGhsdnaPcu9kmbalcofhHascFbGhscrhldninaD8SbbgPcFbGaltasVhsaPcu9kmeaDcefhDalcrfglc8J9hmbkaHhDxekaDcefhDkasce4cbasceG9R7amfgmhHkdndnaCcsSmbaDhsxekaDcefhsaD8SbbglcFeGhPdnalcu9kmbaDcvfhOaPcFbGhPcrhldninas8SbbgDcFbGaltaPVhPaDcu9kmeascefhsalcrfglc8J9hmbkaOhsxekascefhskaPce4cbaPceG9R7amfgmhOkdndnaAcsSmbashlxekascefhlas8SbbgDcFeGhPdnaDcu9kmbascvfhzaPcFbGhPcrhDdninal8SbbgscFbGaDtaPVhPascu9kmealcefhlaDcrfgDc8J9hmbkazhlxekalcefhlkaPce4cbaPceG9R7amfgmhzkdndnadcd9hmbabarcetfgDaH87ebaDclfaz87ebaDcdfaO87ebxekabarcdtfgDaHBdbaDcwfazBdbaDclfaOBdbkavc;abfaocitfgDaOBdbaDaHBdlavaicdtfaHBdbavc;abfaocefcsGcitfgDazBdbaDaOBdlavaicefgicsGcdtfaOBdbavc;abfaocdfcsGcitfgDaHBdbaDazBdlavaiaCTaCcsSVfgicsGcdtfazBdbaiaATaAcsSVfhiaocifhokawcefhwaocsGhoaicsGhiarcifgrae6mbkkcbc99alaqSEhokavc;aef8Kjjjjbaok:clevu8Jjjjjbcz9Rhvdnalaecvf9pmbc9:skdnaiRbbc;:eGc;qeSmbcuskav9cb83iwaicefhoaialfc98fhrdnaeTmbdnadcdSmbcbhwindnaoar6mbc9:skaocefhlao8SbbgicFeGhddndnaicu9mmbalhoxekaocvfhoadcFbGhdcrhidninal8SbbgDcFbGaitadVhdaDcu9kmealcefhlaicrfgic8J9hmbxdkkalcefhokabawcdtfadc8Etc8F91adcd47avcwfadceGcdtVglydbfgiBdbalaiBdbawcefgwae9hmbxdkkcbhwindnaoar6mbc9:skaocefhlao8SbbgicFeGhddndnaicu9mmbalhoxekaocvfhoadcFbGhdcrhidninal8SbbgDcFbGaitadVhdaDcu9kmealcefhlaicrfgic8J9hmbxdkkalcefhokabawcetfadc8Etc8F91adcd47avcwfadceGcdtVglydbfgi87ebalaiBdbawcefgwae9hmbkkcbc99aoarSEk:Lvoeue99dud99eud99dndnadcl9hmbaeTmeindndnabcdfgd8Sbb:Yab8Sbbgi:Ygl:l:tabcefgv8Sbbgo:Ygr:l:tgwJbb;:9cawawNJbbbbawawJbbbb9GgDEgq:mgkaqaicb9iEalMgwawNakaqaocb9iEarMgqaqNMM:r:vglNJbbbZJbbb:;aDEMgr:lJbbb9p9DTmbar:Ohixekcjjjj94hikadai86bbdndnaqalNJbbbZJbbb:;aqJbbbb9GEMgq:lJbbb9p9DTmbaq:Ohdxekcjjjj94hdkavad86bbdndnawalNJbbbZJbbb:;awJbbbb9GEMgw:lJbbb9p9DTmbaw:Ohdxekcjjjj94hdkabad86bbabclfhbaecufgembxdkkaeTmbindndnabclfgd8Ueb:Yab8Uebgi:Ygl:l:tabcdfgv8Uebgo:Ygr:l:tgwJb;:FSawawNJbbbbawawJbbbb9GgDEgq:mgkaqaicb9iEalMgwawNakaqaocb9iEarMgqaqNMM:r:vglNJbbbZJbbb:;aDEMgr:lJbbb9p9DTmbar:Ohixekcjjjj94hikadai87ebdndnaqalNJbbbZJbbb:;aqJbbbb9GEMgq:lJbbb9p9DTmbaq:Ohdxekcjjjj94hdkavad87ebdndnawalNJbbbZJbbb:;awJbbbb9GEMgw:lJbbb9p9DTmbaw:Ohdxekcjjjj94hdkabad87ebabcwfhbaecufgembkkk:4ioiue99dud99dud99dnaeTmbcbhiabhlindndnal8Uebgv:YgoJ:ji:1Salcof8UebgrciVgw:Y:vgDNJbbbZJbbb:;avcu9kEMgq:lJbbb9p9DTmbaq:Ohkxekcjjjj94hkkalclf8Uebhvalcdf8UebhxalarcefciGcetfak87ebdndnax:YgqaDNJbbbZJbbb:;axcu9kEMgm:lJbbb9p9DTmbam:Ohxxekcjjjj94hxkabaiarciGgkfcd7cetfax87ebdndnav:YgmaDNJbbbZJbbb:;avcu9kEMgP:lJbbb9p9DTmbaP:Ohvxekcjjjj94hvkalarcufciGcetfav87ebdndnawaw2:ZgPaPMaoaoN:taqaqN:tamamN:tgoJbbbbaoJbbbb9GE:raDNJbbbZMgD:lJbbb9p9DTmbaD:Ohrxekcjjjj94hrkalakcetfar87ebalcwfhlaiclfhiaecufgembkkk9mbdnadcd4ae2gdTmbinababydbgecwtcw91:Yaece91cjjj98Gcjjj;8if::NUdbabclfhbadcufgdmbkkk:Tvirud99eudndnadcl9hmbaeTmeindndnabRbbgiabcefgl8Sbbgvabcdfgo8Sbbgrf9R:YJbbuJabcifgwRbbgdce4adVgDcd4aDVgDcl4aDVgD:Z:vgqNJbbbZMgk:lJbbb9p9DTmbak:Ohxxekcjjjj94hxkaoax86bbdndnaraif:YaqNJbbbZMgk:lJbbb9p9DTmbak:Ohoxekcjjjj94hokalao86bbdndnavaifar9R:YaqNJbbbZMgk:lJbbb9p9DTmbak:Ohixekcjjjj94hikabai86bbdndnaDadcetGadceGV:ZaqNJbbbZMgq:lJbbb9p9DTmbaq:Ohdxekcjjjj94hdkawad86bbabclfhbaecufgembxdkkaeTmbindndnab8Vebgiabcdfgl8Uebgvabclfgo8Uebgrf9R:YJbFu9habcofgw8Vebgdce4adVgDcd4aDVgDcl4aDVgDcw4aDVgD:Z:vgqNJbbbZMgk:lJbbb9p9DTmbak:Ohxxekcjjjj94hxkaoax87ebdndnaraif:YaqNJbbbZMgk:lJbbb9p9DTmbak:Ohoxekcjjjj94hokalao87ebdndnavaifar9R:YaqNJbbbZMgk:lJbbb9p9DTmbak:Ohixekcjjjj94hikabai87ebdndnaDadcetGadceGV:ZaqNJbbbZMgq:lJbbb9p9DTmbaq:Ohdxekcjjjj94hdkawad87ebabcwfhbaecufgembkkk9teiucbcbyd:K:G:cjbgeabcifc98GfgbBd:K:G:cjbdndnabZbcztgd9nmbcuhiabad9RcFFifcz4nbcuSmekaehikaik;LeeeudndnaeabVciGTmbabhixekdndnadcz9pmbabhixekabhiinaiaeydbBdbaiclfaeclfydbBdbaicwfaecwfydbBdbaicxfaecxfydbBdbaeczfheaiczfhiadc9Wfgdcs0mbkkadcl6mbinaiaeydbBdbaeclfheaiclfhiadc98fgdci0mbkkdnadTmbinaiaeRbb86bbaicefhiaecefheadcufgdmbkkabk;aeedudndnabciGTmbabhixekaecFeGc:b:c:ew2hldndnadcz9pmbabhixekabhiinaialBdbaicxfalBdbaicwfalBdbaiclfalBdbaiczfhiadc9Wfgdcs0mbkkadcl6mbinaialBdbaiclfhiadc98fgdci0mbkkdnadTmbinaiae86bbaicefhiadcufgdmbkkabkk83dbcj:Gdk8Kbbbbdbbblbbbwbbbbbbbebbbdbbblbbbwbbbbc:K:Gdkl8W:qbb",e="b9H79TebbbeKl9Gbb9Gvuuuuueu9Giuuub9Geueuixkbbebeeddddilve9Weeeviebeoweuecj:Gdkr;Neqo9TW9T9VV95dbH9F9F939H79T9F9J9H229F9Jt9VV7bb8A9TW79O9V9Wt9F9KW9J9V9KW9wWVtW949c919M9MWVbdY9TW79O9V9Wt9F9KW9J9V9KW69U9KW949c919M9MWVblE9TW79O9V9Wt9F9KW9J9V9KW69U9KW949tWG91W9U9JWbvL9TW79O9V9Wt9F9KW9J9V9KWS9P2tWV9p9JtboK9TW79O9V9Wt9F9KW9J9V9KWS9P2tWV9r919HtbrL9TW79O9V9Wt9F9KW9J9V9KWS9P2tWVT949WbwY9TW79O9V9Wt9F9KW9J9V9KWS9P2tWVJ9V29VVbDl79IV9Rbqq:W9Dklbzik94evu8Jjjjjbcz9Rhbcbheincbhdcbhiinabcwfadfaicjuaead4ceGglE86bbaialfhiadcefgdcw9hmbkaeai86b:q:W:cjbaecitab8Piw83i:q:G:cjbaecefgecjd9hmbkk:JBl8Aud97dur978Jjjjjbcj;kb9Rgv8Kjjjjbc9:hodnalTmbcuhoaiRbbgrc;WeGc:Ge9hmbarcsGgwce0mbc9:hoalcufadcd4cbawEgDadfgrcKcaawEgqaraq0Egk6mbaialfgxar9RhodnadTgmmbavaoad;8qbbkaicefhPcj;abad9Uc;WFbGcjdadca0EhsdndndnadTmbaoadfhzcbhHinaeaH9nmdaxaP9RaD6miabaHad2fhOaPaDfhAasaeaH9RaHasfae6EgCcsfgocl4cifcd4hXavcj;cbfaoc9WGgQcetfhLavcj;cbfaQci2fhKavcj;cbfaQfhYcbh8Aaoc;ab6hEincbh3dnawTmbaPa8Acd4fRbbh3kcbh5avcj;cbfh8Eindndndndna3a5cet4ciGgoc9:fPdebdkaxaA9RaQ6mwdnaQTmbavcj;cbfa5aQ2faAaQ;8qbbkaAaCfhAxdkaQTmeavcj;cbfa5aQ2fcbaQ;8kbxekaxaA9RaX6moaoclVcbawEhraAaXfhocbhidnaEmbaxao9Rc;Gb6mbcbhlina8EalfhidndndndndndnaAalco4fRbbgqciGarfPDbedibledibkaipxbbbbbbbbbbbbbbbbpklbxlkaiaopbblaopbbbg8Fclp:mea8FpmbzeHdOiAlCvXoQrLg8Fcdp:mea8FpmbzeHdOiAlCvXoQrLpxiiiiiiiiiiiiiiiip9ogapxiiiiiiiiiiiiiiiip8Jg8Fp5b9cjF;8;4;W;G;ab9:9cU1:Nghcitpbi:q:G:cjbahRb:q:W:cjbghpsa8Fp5e9cjF;8;4;W;G;ab9:9cU1:Nggcitpbi:q:G:cjbp9UpmbedilvorzHOACXQLpPaaa8Fp9spklbahaoclffagRb:q:W:cjbfhoxikaiaopbbwaopbbbg8Fclp:mea8FpmbzeHdOiAlCvXoQrLpxssssssssssssssssp9ogapxssssssssssssssssp8Jg8Fp5b9cjF;8;4;W;G;ab9:9cU1:Nghcitpbi:q:G:cjbahRb:q:W:cjbghpsa8Fp5e9cjF;8;4;W;G;ab9:9cU1:Nggcitpbi:q:G:cjbp9UpmbedilvorzHOACXQLpPaaa8Fp9spklbahaocwffagRb:q:W:cjbfhoxdkaiaopbbbpklbaoczfhoxekaiaopbbdaoRbbghcitpbi:q:G:cjbahRb:q:W:cjbghpsaoRbeggcitpbi:q:G:cjbp9UpmbedilvorzHOACXQLpPpklbahaocdffagRb:q:W:cjbfhokdndndndndndnaqcd4ciGarfPDbedibledibkaiczfpxbbbbbbbbbbbbbbbbpklbxlkaiczfaopbblaopbbbg8Fclp:mea8FpmbzeHdOiAlCvXoQrLg8Fcdp:mea8FpmbzeHdOiAlCvXoQrLpxiiiiiiiiiiiiiiiip9ogapxiiiiiiiiiiiiiiiip8Jg8Fp5b9cjF;8;4;W;G;ab9:9cU1:Nghcitpbi:q:G:cjbahRb:q:W:cjbghpsa8Fp5e9cjF;8;4;W;G;ab9:9cU1:Nggcitpbi:q:G:cjbp9UpmbedilvorzHOACXQLpPaaa8Fp9spklbahaoclffagRb:q:W:cjbfhoxikaiczfaopbbwaopbbbg8Fclp:mea8FpmbzeHdOiAlCvXoQrLpxssssssssssssssssp9ogapxssssssssssssssssp8Jg8Fp5b9cjF;8;4;W;G;ab9:9cU1:Nghcitpbi:q:G:cjbahRb:q:W:cjbghpsa8Fp5e9cjF;8;4;W;G;ab9:9cU1:Nggcitpbi:q:G:cjbp9UpmbedilvorzHOACXQLpPaaa8Fp9spklbahaocwffagRb:q:W:cjbfhoxdkaiczfaopbbbpklbaoczfhoxekaiczfaopbbdaoRbbghcitpbi:q:G:cjbahRb:q:W:cjbghpsaoRbeggcitpbi:q:G:cjbp9UpmbedilvorzHOACXQLpPpklbahaocdffagRb:q:W:cjbfhokdndndndndndnaqcl4ciGarfPDbedibledibkaicafpxbbbbbbbbbbbbbbbbpklbxlkaicafaopbblaopbbbg8Fclp:mea8FpmbzeHdOiAlCvXoQrLg8Fcdp:mea8FpmbzeHdOiAlCvXoQrLpxiiiiiiiiiiiiiiiip9ogapxiiiiiiiiiiiiiiiip8Jg8Fp5b9cjF;8;4;W;G;ab9:9cU1:Nghcitpbi:q:G:cjbahRb:q:W:cjbghpsa8Fp5e9cjF;8;4;W;G;ab9:9cU1:Nggcitpbi:q:G:cjbp9UpmbedilvorzHOACXQLpPaaa8Fp9spklbahaoclffagRb:q:W:cjbfhoxikaicafaopbbwaopbbbg8Fclp:mea8FpmbzeHdOiAlCvXoQrLpxssssssssssssssssp9ogapxssssssssssssssssp8Jg8Fp5b9cjF;8;4;W;G;ab9:9cU1:Nghcitpbi:q:G:cjbahRb:q:W:cjbghpsa8Fp5e9cjF;8;4;W;G;ab9:9cU1:Nggcitpbi:q:G:cjbp9UpmbedilvorzHOACXQLpPaaa8Fp9spklbahaocwffagRb:q:W:cjbfhoxdkaicafaopbbbpklbaoczfhoxekaicafaopbbdaoRbbghcitpbi:q:G:cjbahRb:q:W:cjbghpsaoRbeggcitpbi:q:G:cjbp9UpmbedilvorzHOACXQLpPpklbahaocdffagRb:q:W:cjbfhokdndndndndndnaqco4arfPDbedibledibkaic8Wfpxbbbbbbbbbbbbbbbbpklbxlkaic8Wfaopbblaopbbbg8Fclp:mea8FpmbzeHdOiAlCvXoQrLg8Fcdp:mea8FpmbzeHdOiAlCvXoQrLpxiiiiiiiiiiiiiiiip9ogapxiiiiiiiiiiiiiiiip8Jg8Fp5b9cjF;8;4;W;G;ab9:9cU1:Ngicitpbi:q:G:cjbaiRb:q:W:cjbgipsa8Fp5e9cjF;8;4;W;G;ab9:9cU1:Ngqcitpbi:q:G:cjbp9UpmbedilvorzHOACXQLpPaaa8Fp9spklbaiaoclffaqRb:q:W:cjbfhoxikaic8Wfaopbbwaopbbbg8Fclp:mea8FpmbzeHdOiAlCvXoQrLpxssssssssssssssssp9ogapxssssssssssssssssp8Jg8Fp5b9cjF;8;4;W;G;ab9:9cU1:Ngicitpbi:q:G:cjbaiRb:q:W:cjbgipsa8Fp5e9cjF;8;4;W;G;ab9:9cU1:Ngqcitpbi:q:G:cjbp9UpmbedilvorzHOACXQLpPaaa8Fp9spklbaiaocwffaqRb:q:W:cjbfhoxdkaic8Wfaopbbbpklbaoczfhoxekaic8WfaopbbdaoRbbgicitpbi:q:G:cjbaiRb:q:W:cjbgipsaoRbegqcitpbi:q:G:cjbp9UpmbedilvorzHOACXQLpPpklbaiaocdffaqRb:q:W:cjbfhokalc;abfhialcjefaQ0meaihlaxao9Rc;Fb0mbkkdnaiaQ9pmbaici4hlinaxao9RcK6mwa8EaifhqdndndndndndnaAaico4fRbbalcoG4ciGarfPDbedibledibkaqpxbbbbbbbbbbbbbbbbpkbbxlkaqaopbblaopbbbg8Fclp:mea8FpmbzeHdOiAlCvXoQrLg8Fcdp:mea8FpmbzeHdOiAlCvXoQrLpxiiiiiiiiiiiiiiiip9ogapxiiiiiiiiiiiiiiiip8Jg8Fp5b9cjF;8;4;W;G;ab9:9cU1:Nghcitpbi:q:G:cjbahRb:q:W:cjbghpsa8Fp5e9cjF;8;4;W;G;ab9:9cU1:Nggcitpbi:q:G:cjbp9UpmbedilvorzHOACXQLpPaaa8Fp9spkbbahaoclffagRb:q:W:cjbfhoxikaqaopbbwaopbbbg8Fclp:mea8FpmbzeHdOiAlCvXoQrLpxssssssssssssssssp9ogapxssssssssssssssssp8Jg8Fp5b9cjF;8;4;W;G;ab9:9cU1:Nghcitpbi:q:G:cjbahRb:q:W:cjbghpsa8Fp5e9cjF;8;4;W;G;ab9:9cU1:Nggcitpbi:q:G:cjbp9UpmbedilvorzHOACXQLpPaaa8Fp9spkbbahaocwffagRb:q:W:cjbfhoxdkaqaopbbbpkbbaoczfhoxekaqaopbbdaoRbbghcitpbi:q:G:cjbahRb:q:W:cjbghpsaoRbeggcitpbi:q:G:cjbp9UpmbedilvorzHOACXQLpPpkbbahaocdffagRb:q:W:cjbfhokalcdfhlaiczfgiaQ6mbkkaohAaoTmoka8EaQfh8Ea5cefg5cl9hmbkdndndndnawTmbaza8Acd4fRbbglciGPlbedwbkaQTmdavcjdfa8Afhlava8Afpbdbh8Jcbhoinalavcj;cbfaofpblbg8KaYaofpblbg8LpmbzeHdOiAlCvXoQrLg8MaLaofpblbg8NaKaofpblbgypmbzeHdOiAlCvXoQrLg8PpmbezHdiOAlvCXorQLg8Fcep9Ta8Fpxeeeeeeeeeeeeeeeegap9op9Hp9rg8Fa8Jp9Ug8Jp9Abbbaladfgla8Ja8Fa8Fpmlvorlvorlvorlvorp9Ug8Jp9Abbbaladfgla8Ja8Fa8FpmwDqkwDqkwDqkwDqkp9Ug8Jp9Abbbaladfgla8Ja8Fa8FpmxmPsxmPsxmPsxmPsp9Ug8Jp9Abbbaladfgla8Ja8Ma8PpmwDKYqk8AExm35Ps8E8Fg8Fcep9Ta8Faap9op9Hp9rg8Fp9Ug8Jp9Abbbaladfgla8Ja8Fa8Fpmlvorlvorlvorlvorp9Ug8Jp9Abbbaladfgla8Ja8Fa8FpmwDqkwDqkwDqkwDqkp9Ug8Jp9Abbbaladfgla8Ja8Fa8FpmxmPsxmPsxmPsxmPsp9Ug8Jp9Abbbaladfgla8Ja8Ka8LpmwKDYq8AkEx3m5P8Es8Fg8Ka8NaypmwKDYq8AkEx3m5P8Es8Fg8LpmbezHdiOAlvCXorQLg8Fcep9Ta8Faap9op9Hp9rg8Fp9Ug8Jp9Abbbaladfgla8Ja8Fa8Fpmlvorlvorlvorlvorp9Ug8Jp9Abbbaladfgla8Ja8Fa8FpmwDqkwDqkwDqkwDqkp9Ug8Jp9Abbbaladfgla8Ja8Fa8FpmxmPsxmPsxmPsxmPsp9Ug8Jp9Abbbaladfgla8Ja8Ka8LpmwDKYqk8AExm35Ps8E8Fg8Fcep9Ta8Faap9op9Hp9rg8Fp9Ugap9Abbbaladfglaaa8Fa8Fpmlvorlvorlvorlvorp9Ugap9Abbbaladfglaaa8Fa8FpmwDqkwDqkwDqkwDqkp9Ugap9Abbbaladfglaaa8Fa8FpmxmPsxmPsxmPsxmPsp9Ug8Jp9AbbbaladfhlaoczfgoaQ6mbxikkaQTmeavcjdfa8Afhlava8Afpbdbh8Jcbhoinalavcj;cbfaofpblbg8KaYaofpblbg8LpmbzeHdOiAlCvXoQrLg8MaLaofpblbg8NaKaofpblbgypmbzeHdOiAlCvXoQrLg8PpmbezHdiOAlvCXorQLg8Fcep:nea8Fpxebebebebebebebebgap9op:bep9rg8Fa8Jp:oeg8Jp9Abbbaladfgla8Ja8Fa8Fpmlvorlvorlvorlvorp:oeg8Jp9Abbbaladfgla8Ja8Fa8FpmwDqkwDqkwDqkwDqkp:oeg8Jp9Abbbaladfgla8Ja8Fa8FpmxmPsxmPsxmPsxmPsp:oeg8Jp9Abbbaladfgla8Ja8Ma8PpmwDKYqk8AExm35Ps8E8Fg8Fcep:nea8Faap9op:bep9rg8Fp:oeg8Jp9Abbbaladfgla8Ja8Fa8Fpmlvorlvorlvorlvorp:oeg8Jp9Abbbaladfgla8Ja8Fa8FpmwDqkwDqkwDqkwDqkp:oeg8Jp9Abbbaladfgla8Ja8Fa8FpmxmPsxmPsxmPsxmPsp:oeg8Jp9Abbbaladfgla8Ja8Ka8LpmwKDYq8AkEx3m5P8Es8Fg8Ka8NaypmwKDYq8AkEx3m5P8Es8Fg8LpmbezHdiOAlvCXorQLg8Fcep:nea8Faap9op:bep9rg8Fp:oeg8Jp9Abbbaladfgla8Ja8Fa8Fpmlvorlvorlvorlvorp:oeg8Jp9Abbbaladfgla8Ja8Fa8FpmwDqkwDqkwDqkwDqkp:oeg8Jp9Abbbaladfgla8Ja8Fa8FpmxmPsxmPsxmPsxmPsp:oeg8Jp9Abbbaladfgla8Ja8Ka8LpmwDKYqk8AExm35Ps8E8Fg8Fcep:nea8Faap9op:bep9rg8Fp:oegap9Abbbaladfglaaa8Fa8Fpmlvorlvorlvorlvorp:oegap9Abbbaladfglaaa8Fa8FpmwDqkwDqkwDqkwDqkp:oegap9Abbbaladfglaaa8Fa8FpmxmPsxmPsxmPsxmPsp:oeg8Jp9AbbbaladfhlaoczfgoaQ6mbxdkkaQTmbcbhocbalcl4gl9Rc8FGhiavcjdfa8Afhrava8Afpbdbhainaravcj;cbfaofpblbg8JaYaofpblbg8KpmbzeHdOiAlCvXoQrLg8LaLaofpblbg8MaKaofpblbg8NpmbzeHdOiAlCvXoQrLgypmbezHdiOAlvCXorQLg8Faip:Rea8Falp:Tep9qg8Faap9rgap9Abbbaradfgraaa8Fa8Fpmlvorlvorlvorlvorp9rgap9Abbbaradfgraaa8Fa8FpmwDqkwDqkwDqkwDqkp9rgap9Abbbaradfgraaa8Fa8FpmxmPsxmPsxmPsxmPsp9rgap9Abbbaradfgraaa8LaypmwDKYqk8AExm35Ps8E8Fg8Faip:Rea8Falp:Tep9qg8Fp9rgap9Abbbaradfgraaa8Fa8Fpmlvorlvorlvorlvorp9rgap9Abbbaradfgraaa8Fa8FpmwDqkwDqkwDqkwDqkp9rgap9Abbbaradfgraaa8Fa8FpmxmPsxmPsxmPsxmPsp9rgap9Abbbaradfgraaa8Ja8KpmwKDYq8AkEx3m5P8Es8Fg8Ja8Ma8NpmwKDYq8AkEx3m5P8Es8Fg8KpmbezHdiOAlvCXorQLg8Faip:Rea8Falp:Tep9qg8Fp9rgap9Abbbaradfgraaa8Fa8Fpmlvorlvorlvorlvorp9rgap9Abbbaradfgraaa8Fa8FpmwDqkwDqkwDqkwDqkp9rgap9Abbbaradfgraaa8Fa8FpmxmPsxmPsxmPsxmPsp9rgap9Abbbaradfgraaa8Ja8KpmwDKYqk8AExm35Ps8E8Fg8Faip:Rea8Falp:Tep9qg8Fp9rgap9Abbbaradfgraaa8Fa8Fpmlvorlvorlvorlvorp9rgap9Abbbaradfgraaa8Fa8FpmwDqkwDqkwDqkwDqkp9rgap9Abbbaradfgraaa8Fa8FpmxmPsxmPsxmPsxmPsp9rgap9AbbbaradfhraoczfgoaQ6mbkka8Aclfg8Aad6mbkdnaCad2goTmbaOavcjdfao;8qbbkdnammbavavcjdfaCcufad2fad;8qbbkaCaHfhHc9:hoaAhPaAmbxlkkaeTmbaDalfhrcbhocuhlinaralaD9RglfaD6mdasaeao9Raoasfae6Eaofgoae6mbkaial9RhPkcbc99axaP9RakSEhoxekc9:hokavcj;kbf8Kjjjjbaokwbz:bjjjbkNsezu8Jjjjjbc;ae9Rgv8Kjjjjbc9:hodnalaeci9UgrcHf6mbcuhoaiRbbgwc;WeGc;Ge9hmbawcsGgDce0mbavc;abfcFecje;8kbav9cu83iUav9cu83i8Wav9cu83iyav9cu83iaav9cu83iKav9cu83izav9cu83iwav9cu83ibaialfc9WfhqaicefgwarfhldnaeTmbcmcsaDceSEhkcbhxcbhmcbhrcbhicbhoindnalaq9nmbc9:hoxikdndnawRbbgDc;Ve0mbavc;abfaoaDcu7gPcl4fcsGcitfgsydlhzasydbhHdndnaDcsGgsak9pmbavaiaPfcsGcdtfydbaxasEhDaxasTgOfhxxekdndnascsSmbcehOasc987asamffcefhDxekalcefhDal8SbbgscFeGhPdndnascu9mmbaDhlxekalcvfhlaPcFbGhPcrhsdninaD8SbbgOcFbGastaPVhPaOcu9kmeaDcefhDascrfgsc8J9hmbxdkkaDcefhlkcehOaPce4cbaPceG9R7amfhDkaDhmkavc;abfaocitfgsaDBdbasazBdlavaicdtfaDBdbavc;abfaocefcsGcitfgsaHBdbasaDBdlaocdfhoaOaifhidnadcd9hmbabarcetfgsaH87ebasclfaD87ebascdfaz87ebxdkabarcdtfgsaHBdbascwfaDBdbasclfazBdbxekdnaDcpe0mbavaiaqaDcsGfRbbgscl4gP9RcsGcdtfydbaxcefgOaPEhDavaias9RcsGcdtfydbaOaPTgzfgOascsGgPEhsaPThPdndnadcd9hmbabarcetfgHax87ebaHclfas87ebaHcdfaD87ebxekabarcdtfgHaxBdbaHcwfasBdbaHclfaDBdbkavaicdtfaxBdbavc;abfaocitfgHaDBdbaHaxBdlavaicefgicsGcdtfaDBdbavc;abfaocefcsGcitfgHasBdbaHaDBdlavaiazfgicsGcdtfasBdbavc;abfaocdfcsGcitfgDaxBdbaDasBdlaocifhoaiaPfhiaOaPfhxxekaxcbalRbbgsEgHaDc;:eSgDfhOascsGhAdndnascl4gCmbaOcefhzxekaOhzavaiaC9RcsGcdtfydbhOkdndnaAmbazcefhxxekazhxavaias9RcsGcdtfydbhzkdndnaDTmbalcefhDxekalcdfhDal8SbegPcFeGhsdnaPcu9kmbalcofhHascFbGhscrhldninaD8SbbgPcFbGaltasVhsaPcu9kmeaDcefhDalcrfglc8J9hmbkaHhDxekaDcefhDkasce4cbasceG9R7amfgmhHkdndnaCcsSmbaDhsxekaDcefhsaD8SbbglcFeGhPdnalcu9kmbaDcvfhOaPcFbGhPcrhldninas8SbbgDcFbGaltaPVhPaDcu9kmeascefhsalcrfglc8J9hmbkaOhsxekascefhskaPce4cbaPceG9R7amfgmhOkdndnaAcsSmbashlxekascefhlas8SbbgDcFeGhPdnaDcu9kmbascvfhzaPcFbGhPcrhDdninal8SbbgscFbGaDtaPVhPascu9kmealcefhlaDcrfgDc8J9hmbkazhlxekalcefhlkaPce4cbaPceG9R7amfgmhzkdndnadcd9hmbabarcetfgDaH87ebaDclfaz87ebaDcdfaO87ebxekabarcdtfgDaHBdbaDcwfazBdbaDclfaOBdbkavc;abfaocitfgDaOBdbaDaHBdlavaicdtfaHBdbavc;abfaocefcsGcitfgDazBdbaDaOBdlavaicefgicsGcdtfaOBdbavc;abfaocdfcsGcitfgDaHBdbaDazBdlavaiaCTaCcsSVfgicsGcdtfazBdbaiaATaAcsSVfhiaocifhokawcefhwaocsGhoaicsGhiarcifgrae6mbkkcbc99alaqSEhokavc;aef8Kjjjjbaok:clevu8Jjjjjbcz9Rhvdnalaecvf9pmbc9:skdnaiRbbc;:eGc;qeSmbcuskav9cb83iwaicefhoaialfc98fhrdnaeTmbdnadcdSmbcbhwindnaoar6mbc9:skaocefhlao8SbbgicFeGhddndnaicu9mmbalhoxekaocvfhoadcFbGhdcrhidninal8SbbgDcFbGaitadVhdaDcu9kmealcefhlaicrfgic8J9hmbxdkkalcefhokabawcdtfadc8Etc8F91adcd47avcwfadceGcdtVglydbfgiBdbalaiBdbawcefgwae9hmbxdkkcbhwindnaoar6mbc9:skaocefhlao8SbbgicFeGhddndnaicu9mmbalhoxekaocvfhoadcFbGhdcrhidninal8SbbgDcFbGaitadVhdaDcu9kmealcefhlaicrfgic8J9hmbxdkkalcefhokabawcetfadc8Etc8F91adcd47avcwfadceGcdtVglydbfgi87ebalaiBdbawcefgwae9hmbkkcbc99aoarSEk;Toio97eue97aec98Ghedndnadcl9hmbaeTmecbhdinababpbbbgicKp:RecKp:Sep;6eglaicwp:RecKp:Sep;6ealp;Geaiczp:RecKp:Sep;6egvp;Gep;Kep;Legopxbbbbbbbbbbbbbbbbp:2egralpxbbbjbbbjbbbjbbbjgwp9op9rp;Keglpxbb;:9cbb;:9cbb;:9cbb;:9calalp;Meaoaop;Meavaravawp9op9rp;Keglalp;Mep;Kep;Kep;Jep;Negvp;Mepxbbn0bbn0bbn0bbn0grp;KepxFbbbFbbbFbbbFbbbp9oaipxbbbFbbbFbbbFbbbFp9op9qalavp;Mearp;Kecwp:RepxbFbbbFbbbFbbbFbbp9op9qaoavp;Mearp;Keczp:RepxbbFbbbFbbbFbbbFbp9op9qpkbbabczfhbadclfgdae6mbxdkkaeTmbcbhdinabczfgDaDpbbbgipxbbbbbbFFbbbbbbFFgwp9oabpbbbgoaipmbediwDqkzHOAKY8AEgvczp:Reczp:Sep;6eglaoaipmlvorxmPsCXQL358E8FpxFubbFubbFubbFubbp9op;6eavczp:Sep;6egvp;Gealp;Gep;Kep;Legipxbbbbbbbbbbbbbbbbp:2egralpxbbbjbbbjbbbjbbbjgqp9op9rp;Keglpxb;:FSb;:FSb;:FSb;:FSalalp;Meaiaip;Meavaravaqp9op9rp;Keglalp;Mep;Kep;Kep;Jep;Negvp;Mepxbbn0bbn0bbn0bbn0grp;KepxFFbbFFbbFFbbFFbbp9oaiavp;Mearp;Keczp:Rep9qgialavp;Mearp;KepxFFbbFFbbFFbbFFbbp9oglpmwDKYqk8AExm35Ps8E8Fp9qpkbbabaoawp9oaialpmbezHdiOAlvCXorQLp9qpkbbabcafhbadclfgdae6mbkkk;2ileue97euo97dnaec98GgiTmbcbheinabcKfpx:ji:1S:ji:1S:ji:1S:ji:1SabpbbbglabczfgvpbbbgopmlvorxmPsCXQL358E8Fgrczp:Segwpxibbbibbbibbbibbbp9qp;6egDp;NegqaDaDp;MegDaDp;KealaopmbediwDqkzHOAKY8AEgDczp:Reczp:Sep;6eglalp;MeaDczp:Sep;6egoaop;Mearczp:Reczp:Sep;6egrarp;Mep;Kep;Kep;Lepxbbbbbbbbbbbbbbbbp:4ep;Jep;Mepxbbn0bbn0bbn0bbn0gDp;KepxFFbbFFbbFFbbFFbbgkp9oaqaop;MeaDp;Keczp:Rep9qgoaqalp;MeaDp;Keakp9oaqarp;MeaDp;Keczp:Rep9qgDpmwDKYqk8AExm35Ps8E8Fglp5eawclp:RegqpEi:T:j83ibavalp5baqpEd:T:j83ibabcwfaoaDpmbezHdiOAlvCXorQLgDp5eaqpEe:T:j83ibabaDp5baqpEb:T:j83ibabcafhbaeclfgeai6mbkkkuee97dnadcd4ae2c98GgeTmbcbhdinababpbbbgicwp:Recwp:Sep;6eaicep:SepxbbjFbbjFbbjFbbjFp9opxbbjZbbjZbbjZbbjZp:Uep;Mepkbbabczfhbadclfgdae6mbkkk:Sodw97euaec98Ghedndnadcl9hmbaeTmecbhdinabpxbbuJbbuJbbuJbbuJabpbbbgicKp:TeglaicYp:Tep9qgvcdp:Teavp9qgvclp:Teavp9qgop;6ep;Negvaicwp:RecKp:SegraipxFbbbFbbbFbbbFbbbgwp9ogDp:Uep;6ep;Mepxbbn0bbn0bbn0bbn0gqp;Kecwp:RepxbFbbbFbbbFbbbFbbp9oavaDarp:Xeaiczp:RecKp:Segip:Uep;6ep;Meaqp;Keawp9op9qavaDaraip:Uep:Xep;6ep;Meaqp;Keczp:RepxbbFbbbFbbbFbbbFbp9op9qavaoalcep:Rep9oalpxebbbebbbebbbebbbp9op9qp;6ep;Meaqp;KecKp:Rep9qpkbbabczfhbadclfgdae6mbxdkkaeTmbcbhdinabczfgkpxbFu9hbFu9hbFu9hbFu9habpbbbglakpbbbgrpmlvorxmPsCXQL358E8Fgvczp:TegqavcHp:Tep9qgicdp:Teaip9qgiclp:Teaip9qgicwp:Teaip9qgop;6ep;NegialarpmbediwDqkzHOAKY8AEgDpxFFbbFFbbFFbbFFbbglp9ograDczp:Segwp:Ueavczp:Reczp:SegDp:Xep;6ep;Mepxbbn0bbn0bbn0bbn0gvp;Kealp9oaiarawaDp:Uep:Xep;6ep;Meavp;Keczp:Rep9qgwaiaoaqcep:Rep9oaqpxebbbebbbebbbebbbp9op9qp;6ep;Meavp;Keczp:ReaiaDarp:Uep;6ep;Meavp;Kealp9op9qgipmwDKYqk8AExm35Ps8E8FpkbbabawaipmbezHdiOAlvCXorQLpkbbabcafhbadclfgdae6mbkkk9teiucbcbydj:G:cjbgeabcifc98GfgbBdj:G:cjbdndnabZbcztgd9nmbcuhiabad9RcFFifcz4nbcuSmekaehikaikkxebcj:Gdklz:zbb",t=new Uint8Array([0,97,115,109,1,0,0,0,1,4,1,96,0,0,3,3,2,0,0,5,3,1,0,1,12,1,0,10,22,2,12,0,65,0,65,0,65,0,252,10,0,0,11,7,0,65,0,253,15,26,11]),n=new Uint8Array([32,0,65,2,1,106,34,33,3,128,11,4,13,64,6,253,10,7,15,116,127,5,8,12,40,16,19,54,20,9,27,255,113,17,42,67,24,23,146,148,18,14,22,45,70,69,56,114,101,21,25,63,75,136,108,28,118,29,73,115]);if(typeof WebAssembly!="object")return{supported:!1};var i=WebAssembly.validate(t)?o(e):o(a),s,r=WebAssembly.instantiate(i,{}).then(function(x){s=x.instance,s.exports.__wasm_call_ctors()});function o(x){for(var v=new Uint8Array(x.length),S=0;S<x.length;++S){var y=x.charCodeAt(S);v[S]=y>96?y-97:y>64?y-39:y+4}for(var T=0,S=0;S<x.length;++S)v[T++]=v[S]<60?n[v[S]]:(v[S]-60)*64+v[++S];return v.buffer.slice(0,T)}function c(x,v,S,y,T,M,A){var g=x.exports.sbrk,w=y+3&-4,R=g(w*T),C=g(M.length),N=new Uint8Array(x.exports.memory.buffer);N.set(M,C);var L=v(R,y,T,C,M.length);if(L==0&&A&&A(R,w,T),S.set(N.subarray(R,R+y*T)),g(R-g(0)),L!=0)throw new Error("Malformed buffer data: "+L)}var l={NONE:"",OCTAHEDRAL:"meshopt_decodeFilterOct",QUATERNION:"meshopt_decodeFilterQuat",EXPONENTIAL:"meshopt_decodeFilterExp",COLOR:"meshopt_decodeFilterColor"},u={ATTRIBUTES:"meshopt_decodeVertexBuffer",TRIANGLES:"meshopt_decodeIndexBuffer",INDICES:"meshopt_decodeIndexSequence"},h=[],f=0;function d(x){var v={object:new Worker(x),pending:0,requests:{}};return v.object.onmessage=function(S){var y=S.data;v.pending-=y.count,v.requests[y.id][y.action](y.value),delete v.requests[y.id]},v}function p(x){for(var v="self.ready = WebAssembly.instantiate(new Uint8Array(["+new Uint8Array(i)+"]), {}).then(function(result) { result.instance.exports.__wasm_call_ctors(); return result.instance; });self.onmessage = "+b.name+";"+c.toString()+b.toString(),S=new Blob([v],{type:"text/javascript"}),y=URL.createObjectURL(S),T=h.length;T<x;++T)h[T]=d(y);for(var T=x;T<h.length;++T)h[T].object.postMessage({});h.length=x,URL.revokeObjectURL(y)}function m(x,v,S,y,T){for(var M=h[0],A=1;A<h.length;++A)h[A].pending<M.pending&&(M=h[A]);return new Promise(function(g,w){var R=new Uint8Array(S),C=++f;M.pending+=x,M.requests[C]={resolve:g,reject:w},M.object.postMessage({id:C,count:x,size:v,source:R,mode:y,filter:T},[R.buffer])})}function b(x){var v=x.data;self.ready.then(function(S){if(!v.id)return self.close();try{var y=new Uint8Array(v.count*v.size);c(S,S.exports[v.mode],y,v.count,v.size,v.source,S.exports[v.filter]),self.postMessage({id:v.id,count:v.count,action:"resolve",value:y},[y.buffer])}catch(T){self.postMessage({id:v.id,count:v.count,action:"reject",value:T})}})}return{ready:r,supported:!0,useWorkers:function(x){p(x)},decodeVertexBuffer:function(x,v,S,y,T){c(s,s.exports.meshopt_decodeVertexBuffer,x,v,S,y,s.exports[l[T]])},decodeIndexBuffer:function(x,v,S,y){c(s,s.exports.meshopt_decodeIndexBuffer,x,v,S,y)},decodeIndexSequence:function(x,v,S,y){c(s,s.exports.meshopt_decodeIndexSequence,x,v,S,y)},decodeGltfBuffer:function(x,v,S,y,T,M){c(s,s.exports[u[T]],x,v,S,y,s.exports[l[M]])},decodeGltfBufferAsync:function(x,v,S,y,T){return h.length>0?m(x,v,S,u[y],l[T]):r.then(function(){var M=new Uint8Array(x*v);return c(s,s.exports[u[y]],M,x,v,S,s.exports[l[T]]),M})}}})();var Os=class{parse(e,t={}){t=Object.assign({binary:!1},t);let n=t.binary,i=[],s=0;e.traverse(function(x){if(x.isMesh){let v=x.geometry,S=v.index,y=v.getAttribute("position");s+=S!==null?S.count/3:y.count/3,i.push({object3d:x,geometry:v})}});let r,o=80;if(n===!0){let x=s*2+s*3*4*4+80+4,v=new ArrayBuffer(x);r=new DataView(v),r.setUint32(o,s,!0),o+=4}else r="",r+=`solid exported
`;let c=new E,l=new E,u=new E,h=new E,f=new E,d=new E;for(let x=0,v=i.length;x<v;x++){let S=i[x].object3d,y=i[x].geometry,T=y.index,M=y.getAttribute("position");if(T!==null)for(let A=0;A<T.count;A+=3){let g=T.getX(A+0),w=T.getX(A+1),R=T.getX(A+2);p(g,w,R,M,S)}else for(let A=0;A<M.count;A+=3){let g=A+0,w=A+1,R=A+2;p(g,w,R,M,S)}}return n===!1&&(r+=`endsolid exported
`),r;function p(x,v,S,y,T){c.fromBufferAttribute(y,x),l.fromBufferAttribute(y,v),u.fromBufferAttribute(y,S),T.isSkinnedMesh===!0&&(T.applyBoneTransform(x,c),T.applyBoneTransform(v,l),T.applyBoneTransform(S,u)),c.applyMatrix4(T.matrixWorld),l.applyMatrix4(T.matrixWorld),u.applyMatrix4(T.matrixWorld),m(c,l,u),b(c),b(l),b(u),n===!0?(r.setUint16(o,0,!0),o+=2):(r+=`		endloop
`,r+=`	endfacet
`)}function m(x,v,S){h.subVectors(S,v),f.subVectors(x,v),h.cross(f).normalize(),d.copy(h).normalize(),n===!0?(r.setFloat32(o,d.x,!0),o+=4,r.setFloat32(o,d.y,!0),o+=4,r.setFloat32(o,d.z,!0),o+=4):(r+="	facet normal "+d.x+" "+d.y+" "+d.z+`
`,r+=`		outer loop
`)}function b(x){n===!0?(r.setFloat32(o,x.x,!0),o+=4,r.setFloat32(o,x.y,!0),o+=4,r.setFloat32(o,x.z,!0),o+=4):r+="			vertex "+x.x+" "+x.y+" "+x.z+`
`}}};var Bs=class{parse(e){let t="",n=0,i=0,s=0,r=new E,o=new H,c=new E,l=new $,u=[];function h(p){let m=0,b=0,x=0,v=p.geometry,S=new G,y=v.getAttribute("position"),T=v.getAttribute("normal"),M=v.getAttribute("uv"),A=v.getIndex();if(t+="o "+p.name+`
`,p.material&&p.material.name&&(t+="usemtl "+p.material.name+`
`),y!==void 0)for(let g=0,w=y.count;g<w;g++,m++)r.fromBufferAttribute(y,g),r.applyMatrix4(p.matrixWorld),t+="v "+r.x+" "+r.y+" "+r.z+`
`;if(M!==void 0)for(let g=0,w=M.count;g<w;g++,x++)l.fromBufferAttribute(M,g),t+="vt "+l.x+" "+l.y+`
`;if(T!==void 0){S.getNormalMatrix(p.matrixWorld);for(let g=0,w=T.count;g<w;g++,b++)c.fromBufferAttribute(T,g),c.applyMatrix3(S).normalize(),t+="vn "+c.x+" "+c.y+" "+c.z+`
`}if(A!==null)for(let g=0,w=A.count;g<w;g+=3){for(let R=0;R<3;R++){let C=A.getX(g+R)+1;u[R]=n+C+(T||M?"/"+(M?i+C:"")+(T?"/"+(s+C):""):"")}t+="f "+u.join(" ")+`
`}else for(let g=0,w=y.count;g<w;g+=3){for(let R=0;R<3;R++){let C=g+R+1;u[R]=n+C+(T||M?"/"+(M?i+C:"")+(T?"/"+(s+C):""):"")}t+="f "+u.join(" ")+`
`}n+=m,i+=x,s+=b}function f(p){let m=0,b=p.geometry,x=p.type,v=b.getAttribute("position");if(t+="o "+p.name+`
`,v!==void 0)for(let S=0,y=v.count;S<y;S++,m++)r.fromBufferAttribute(v,S),r.applyMatrix4(p.matrixWorld),t+="v "+r.x+" "+r.y+" "+r.z+`
`;if(x==="Line"){t+="l ";for(let S=1,y=v.count;S<=y;S++)t+=n+S+" ";t+=`
`}if(x==="LineSegments")for(let S=1,y=S+1,T=v.count;S<T;S+=2,y=S+1)t+="l "+(n+S)+" "+(n+y)+`
`;n+=m}function d(p){let m=0,b=p.geometry,x=b.getAttribute("position"),v=b.getAttribute("color");if(t+="o "+p.name+`
`,x!==void 0){for(let S=0,y=x.count;S<y;S++,m++)r.fromBufferAttribute(x,S),r.applyMatrix4(p.matrixWorld),t+="v "+r.x+" "+r.y+" "+r.z,v!==void 0&&(o.fromBufferAttribute(v,S),_e.workingToColorSpace(o,ce),t+=" "+o.r+" "+o.g+" "+o.b),t+=`
`;t+="p ";for(let S=1,y=x.count;S<=y;S++)t+=n+S+" ";t+=`
`}n+=m}return e.traverse(function(p){p.isMesh===!0&&h(p),p.isLine===!0&&f(p),p.isPoints===!0&&d(p)}),t}};var Al={POSITION:["byte","byte normalized","unsigned byte","unsigned byte normalized","short","short normalized","unsigned short","unsigned short normalized"],NORMAL:["byte normalized","short normalized"],TANGENT:["byte normalized","short normalized"],TEXCOORD:["byte","byte normalized","unsigned byte","short","short normalized","unsigned short"]},Kt=class{constructor(){this.textureUtils=null,this.pluginCallbacks=[],this.register(function(e){return new Za(e)}),this.register(function(e){return new $a(e)}),this.register(function(e){return new no(e)}),this.register(function(e){return new io(e)}),this.register(function(e){return new so(e)}),this.register(function(e){return new ro(e)}),this.register(function(e){return new Qa(e)}),this.register(function(e){return new eo(e)}),this.register(function(e){return new to(e)}),this.register(function(e){return new ao(e)}),this.register(function(e){return new oo(e)}),this.register(function(e){return new co(e)}),this.register(function(e){return new lo(e)}),this.register(function(e){return new uo(e)})}register(e){return this.pluginCallbacks.indexOf(e)===-1&&this.pluginCallbacks.push(e),this}unregister(e){return this.pluginCallbacks.indexOf(e)!==-1&&this.pluginCallbacks.splice(this.pluginCallbacks.indexOf(e),1),this}setTextureUtils(e){return this.textureUtils=e,this}parse(e,t,n,i){let s=new Ja,r=[];for(let o=0,c=this.pluginCallbacks.length;o<c;o++)r.push(this.pluginCallbacks[o](s));s.setPlugins(r),s.setTextureUtils(this.textureUtils),s.writeAsync(e,t,i).catch(n)}parseAsync(e,t){let n=this;return new Promise(function(i,s){n.parse(e,i,s,t)})}},K={POINTS:0,LINES:1,LINE_LOOP:2,LINE_STRIP:3,TRIANGLES:4,TRIANGLE_STRIP:5,TRIANGLE_FAN:6,BYTE:5120,UNSIGNED_BYTE:5121,SHORT:5122,UNSIGNED_SHORT:5123,INT:5124,UNSIGNED_INT:5125,FLOAT:5126,ARRAY_BUFFER:34962,ELEMENT_ARRAY_BUFFER:34963,NEAREST:9728,LINEAR:9729,NEAREST_MIPMAP_NEAREST:9984,LINEAR_MIPMAP_NEAREST:9985,NEAREST_MIPMAP_LINEAR:9986,LINEAR_MIPMAP_LINEAR:9987,CLAMP_TO_EDGE:33071,MIRRORED_REPEAT:33648,REPEAT:10497},Ka="KHR_mesh_quantization",Ve={};Ve[zt]=K.NEAREST;Ve[Ai]=K.NEAREST_MIPMAP_NEAREST;Ve[Ti]=K.NEAREST_MIPMAP_LINEAR;Ve[Xt]=K.LINEAR;Ve[wi]=K.LINEAR_MIPMAP_NEAREST;Ve[hn]=K.LINEAR_MIPMAP_LINEAR;Ve[xt]=K.CLAMP_TO_EDGE;Ve[_t]=K.REPEAT;Ve[nn]=K.MIRRORED_REPEAT;var Tl={scale:"scale",position:"translation",quaternion:"rotation",morphTargetInfluences:"weights"},jp=new H,wl=12,Jp=1179937895,Zp=2,El=8,$p=1313821514,Qp=5130562;function Rt(a,e){return a.length===e.length&&a.every(function(t,n){return t===e[n]})}function em(a){return new TextEncoder().encode(a).buffer}function tm(a){return Rt(a.elements,[1,0,0,0,0,1,0,0,0,0,1,0,0,0,0,1])}function nm(a,e,t){let n={min:new Array(a.itemSize).fill(Number.POSITIVE_INFINITY),max:new Array(a.itemSize).fill(Number.NEGATIVE_INFINITY)};for(let i=e;i<e+t;i++)for(let s=0;s<a.itemSize;s++){let r;a.itemSize>4?r=a.array[i*a.itemSize+s]:(s===0?r=a.getX(i):s===1?r=a.getY(i):s===2?r=a.getZ(i):s===3&&(r=a.getW(i)),a.normalized===!0&&(r=fn.normalize(r,a.array))),n.min[s]=Math.min(n.min[s],r),n.max[s]=Math.max(n.max[s],r)}return n}function Rl(a){return Math.ceil(a/4)*4}function Ya(a,e=0){let t=Rl(a.byteLength);if(t!==a.byteLength){let n=new Uint8Array(t);if(n.set(new Uint8Array(a)),e!==0)for(let i=a.byteLength;i<t;i++)n[i]=e;return n.buffer}return a}function ja(){return typeof document>"u"&&typeof OffscreenCanvas<"u"?new OffscreenCanvas(1,1):document.createElement("canvas")}function im(a,e){if(typeof OffscreenCanvas<"u"&&a instanceof OffscreenCanvas){let t;return e==="image/jpeg"?t=.92:e==="image/webp"&&(t=.8),a.convertToBlob({type:e,quality:t})}else return new Promise(t=>a.toBlob(t,e))}var Ja=class{constructor(){this.plugins=[],this.options={},this.pending=[],this.buffers=[],this.byteOffset=0,this.buffers=[],this.nodeMap=new Map,this.skins=[],this.extensionsUsed={},this.extensionsRequired={},this.uids=new Map,this.uid=0,this.json={asset:{version:"2.0",generator:"THREE.GLTFExporter r186"}},this.cache={meshes:new Map,attributes:new Map,attributesNormalized:new Map,materials:new Map,textures:new Map,images:new Map,normalMaps:new Map},this.textureUtils=null}setPlugins(e){this.plugins=e}setTextureUtils(e){this.textureUtils=e}async writeAsync(e,t,n={}){this.options=Object.assign({binary:!1,trs:!1,onlyVisible:!0,maxTextureSize:1/0,animations:[],includeCustomExtensions:!1,copyright:null},n),this.options.animations.length>0&&(this.options.trs=!0),await this.processInputAsync(e),await Promise.all(this.pending);let i=this,s=i.buffers,r=i.json;n=i.options;let o=i.extensionsUsed,c=i.extensionsRequired,l=new Blob(s,{type:"application/octet-stream"}),u=Object.keys(o),h=Object.keys(c);if(u.length>0&&(r.extensionsUsed=u),h.length>0&&(r.extensionsRequired=h),r.buffers&&r.buffers.length>0&&(r.buffers[0].byteLength=l.size),n.copyright&&(r.asset.copyright=n.copyright),n.binary===!0){let f=new FileReader;f.readAsArrayBuffer(l),f.onloadend=function(){let d=Ya(f.result),p=new DataView(new ArrayBuffer(El));p.setUint32(0,d.byteLength,!0),p.setUint32(4,Qp,!0);let m=Ya(em(JSON.stringify(r)),32),b=new DataView(new ArrayBuffer(El));b.setUint32(0,m.byteLength,!0),b.setUint32(4,$p,!0);let x=new ArrayBuffer(wl),v=new DataView(x);v.setUint32(0,Jp,!0),v.setUint32(4,Zp,!0);let S=wl+b.byteLength+m.byteLength+p.byteLength+d.byteLength;v.setUint32(8,S,!0);let y=new Blob([x,b,m,p,d],{type:"application/octet-stream"}),T=new FileReader;T.readAsArrayBuffer(y),T.onloadend=function(){t(T.result)}}}else if(r.buffers&&r.buffers.length>0){let f=new FileReader;f.readAsDataURL(l),f.onloadend=function(){let d=f.result;r.buffers[0].uri=d,t(r)}}else t(r)}serializeUserData(e,t){if(Object.keys(e.userData).length===0)return;let n=this.options,i=this.extensionsUsed;try{let s=JSON.parse(JSON.stringify(e.userData));if(n.includeCustomExtensions&&s.gltfExtensions){t.extensions===void 0&&(t.extensions={});for(let r in s.gltfExtensions)t.extensions[r]=s.gltfExtensions[r],i[r]=!0;delete s.gltfExtensions}Object.keys(s).length>0&&(t.extras=s)}catch(s){console.warn("THREE.GLTFExporter: userData of '"+e.name+"' won't be serialized because of JSON.stringify error - "+s.message)}}getUID(e,t=!1){if(this.uids.has(e)===!1){let i=new Map;i.set(!0,this.uid++),i.set(!1,this.uid++),this.uids.set(e,i)}return this.uids.get(e).get(t)}isNormalizedNormalAttribute(e){if(this.cache.attributesNormalized.has(e))return!1;let n=new E;for(let i=0,s=e.count;i<s;i++)if(Math.abs(n.fromBufferAttribute(e,i).length()-1)>5e-4)return!1;return!0}createNormalizedNormalAttribute(e){let t=this.cache;if(t.attributesNormalized.has(e))return t.attributesNormalized.get(e);let n=e.clone(),i=new E;for(let s=0,r=n.count;s<r;s++)i.fromBufferAttribute(n,s),i.x===0&&i.y===0&&i.z===0?i.setX(1):i.normalize(),n.setXYZ(s,i.x,i.y,i.z);return t.attributesNormalized.set(e,n),n}applyTextureTransform(e,t){let n=!1,i={};(t.offset.x!==0||t.offset.y!==0)&&(i.offset=t.offset.toArray(),n=!0),t.rotation!==0&&(i.rotation=t.rotation,n=!0),(t.repeat.x!==1||t.repeat.y!==1)&&(i.scale=t.repeat.toArray(),n=!0),n&&(e.extensions=e.extensions||{},e.extensions.KHR_texture_transform=i,this.extensionsUsed.KHR_texture_transform=!0)}async buildMetalRoughTextureAsync(e,t){if(e===t)return e;function n(d){return d.colorSpace===ce?function(m){return m<.04045?m*.0773993808:Math.pow(m*.9478672986+.0521327014,2.4)}:function(m){return m}}e instanceof Ht&&(e=await this.decompressTextureAsync(e)),t instanceof Ht&&(t=await this.decompressTextureAsync(t));let i=e?e.image:null,s=t?t.image:null,r=Math.max(i?i.width:0,s?s.width:0),o=Math.max(i?i.height:0,s?s.height:0),c=ja();c.width=r,c.height=o;let l=c.getContext("2d",{willReadFrequently:!0});l.fillStyle="#00ffff",l.fillRect(0,0,r,o);let u=l.getImageData(0,0,r,o);if(i){l.drawImage(i,0,0,r,o);let d=n(e),p=l.getImageData(0,0,r,o).data;for(let m=2;m<p.length;m+=4)u.data[m]=d(p[m]/256)*256}if(s){l.drawImage(s,0,0,r,o);let d=n(t),p=l.getImageData(0,0,r,o).data;for(let m=1;m<p.length;m+=4)u.data[m]=d(p[m]/256)*256}l.putImageData(u,0,0);let f=(e||t).clone();return f.source=new sn(c),f.colorSpace=Ci,f.channel=(e||t).channel,e&&t&&e.channel!==t.channel&&console.warn("THREE.GLTFExporter: UV channels for metalnessMap and roughnessMap textures must match."),console.warn("THREE.GLTFExporter: Merged metalnessMap and roughnessMap textures."),f}async buildNormalMapTextureAsync(e,t,n){e instanceof Ht&&(e=await this.decompressTextureAsync(e));let i=e.image,s=ja();s.width=i.width,s.height=i.height;let r=s.getContext("2d",{willReadFrequently:!0});r.drawImage(i,0,0,s.width,s.height);let o=r.getImageData(0,0,s.width,s.height),c=o.data;for(let u=0;u<c.length;u+=4)t&&(c[u+0]=255-c[u+0]),n&&(c[u+1]=255-c[u+1]);r.putImageData(o,0,0);let l=e.clone();return l.source=new sn(s),l}async decompressTextureAsync(e,t=1/0){if(this.textureUtils===null)throw new Error("THREE.GLTFExporter: setTextureUtils() must be called to process compressed textures.");return await this.textureUtils.decompress(e,t)}processBuffer(e){let t=this.json,n=this.buffers;return t.buffers||(t.buffers=[{byteLength:0}]),n.push(e),0}processBufferView(e,t,n,i,s){let r=this.json;r.bufferViews||(r.bufferViews=[]);let o;switch(t){case K.BYTE:case K.UNSIGNED_BYTE:o=1;break;case K.SHORT:case K.UNSIGNED_SHORT:o=2;break;default:o=4}let c=e.itemSize*o;s===K.ARRAY_BUFFER&&(c=Math.ceil(c/4)*4);let l=Rl(i*c),u=new DataView(new ArrayBuffer(l)),h=0;for(let p=n;p<n+i;p++){for(let m=0;m<e.itemSize;m++){let b;e.itemSize>4?b=e.array[p*e.itemSize+m]:(m===0?b=e.getX(p):m===1?b=e.getY(p):m===2?b=e.getZ(p):m===3&&(b=e.getW(p)),e.normalized===!0&&(b=fn.normalize(b,e.array))),t===K.FLOAT?u.setFloat32(h,b,!0):t===K.INT?u.setInt32(h,b,!0):t===K.UNSIGNED_INT?u.setUint32(h,b,!0):t===K.SHORT?u.setInt16(h,b,!0):t===K.UNSIGNED_SHORT?u.setUint16(h,b,!0):t===K.BYTE?u.setInt8(h,b):t===K.UNSIGNED_BYTE&&u.setUint8(h,b),h+=o}h%c!==0&&(h+=c-h%c)}let f={buffer:this.processBuffer(u.buffer),byteOffset:this.byteOffset,byteLength:l};return s!==void 0&&(f.target=s),s===K.ARRAY_BUFFER&&(f.byteStride=c),this.byteOffset+=l,r.bufferViews.push(f),{id:r.bufferViews.length-1,byteLength:0}}processBufferViewImage(e){let t=this,n=t.json;return n.bufferViews||(n.bufferViews=[]),new Promise(function(i){let s=new FileReader;s.readAsArrayBuffer(e),s.onloadend=function(){let r=Ya(s.result),o={buffer:t.processBuffer(r),byteOffset:t.byteOffset,byteLength:r.byteLength};t.byteOffset+=r.byteLength,i(n.bufferViews.push(o)-1)}})}processAccessor(e,t,n,i){let s=this.json,r={1:"SCALAR",2:"VEC2",3:"VEC3",4:"VEC4",9:"MAT3",16:"MAT4"},o;if(e.array.constructor===Float32Array)o=K.FLOAT;else if(e.array.constructor===Int32Array)o=K.INT;else if(e.array.constructor===Uint32Array)o=K.UNSIGNED_INT;else if(e.array.constructor===Int16Array)o=K.SHORT;else if(e.array.constructor===Uint16Array)o=K.UNSIGNED_SHORT;else if(e.array.constructor===Int8Array)o=K.BYTE;else if(e.array.constructor===Uint8Array)o=K.UNSIGNED_BYTE;else throw new Error("THREE.GLTFExporter: Unsupported bufferAttribute component type: "+e.array.constructor.name);if(n===void 0&&(n=0),(i===void 0||i===1/0)&&(i=e.count),i===0)return null;let c=nm(e,n,i),l;t!==void 0&&(l=e===t.index?K.ELEMENT_ARRAY_BUFFER:K.ARRAY_BUFFER);let u=this.processBufferView(e,o,n,i,l),h={bufferView:u.id,byteOffset:u.byteOffset,componentType:o,count:i,max:c.max,min:c.min,type:r[e.itemSize]};return e.normalized===!0&&(h.normalized=!0),s.accessors||(s.accessors=[]),s.accessors.push(h)-1}processImage(e,t,n,i="image/png"){if(e!==null){let s=this,r=s.cache,o=s.json,c=s.options,l=s.pending;r.images.has(e)||r.images.set(e,{});let u=r.images.get(e),h=i+":flipY/"+n.toString();if(u[h]!==void 0)return u[h];o.images||(o.images=[]);let f={mimeType:i},d=ja();d.width=Math.min(e.width,c.maxTextureSize),d.height=Math.min(e.height,c.maxTextureSize);let p=d.getContext("2d",{willReadFrequently:!0});if(n===!0&&(p.translate(0,d.height),p.scale(1,-1)),e.data!==void 0){t!==Ei&&console.error("GLTFExporter: Only RGBAFormat is supported.",t),(e.width>c.maxTextureSize||e.height>c.maxTextureSize)&&console.warn("GLTFExporter: Image size is bigger than maxTextureSize",e);let b=new Uint8ClampedArray(e.height*e.width*4);for(let x=0;x<b.length;x+=4)b[x+0]=e.data[x+0],b[x+1]=e.data[x+1],b[x+2]=e.data[x+2],b[x+3]=e.data[x+3];p.putImageData(new ImageData(b,e.width,e.height),0,0)}else if(typeof HTMLImageElement<"u"&&e instanceof HTMLImageElement||typeof HTMLCanvasElement<"u"&&e instanceof HTMLCanvasElement||typeof ImageBitmap<"u"&&e instanceof ImageBitmap||typeof OffscreenCanvas<"u"&&e instanceof OffscreenCanvas)p.drawImage(e,0,0,d.width,d.height);else throw new Error("THREE.GLTFExporter: Invalid image type. Use HTMLImageElement, HTMLCanvasElement, ImageBitmap or OffscreenCanvas.");c.binary===!0?l.push(im(d,i).then(b=>s.processBufferViewImage(b)).then(b=>{f.bufferView=b})):f.uri=Dn.getDataURL(d,i);let m=o.images.push(f)-1;return u[h]=m,m}else throw new Error("THREE.GLTFExporter: No valid image data found. Unable to process texture.")}processSampler(e){let t=this.json;t.samplers||(t.samplers=[]);let n={magFilter:Ve[e.magFilter],minFilter:Ve[e.minFilter],wrapS:Ve[e.wrapS],wrapT:Ve[e.wrapT]};return t.samplers.push(n)-1}async processTextureAsync(e){let n=this.options,i=this.cache,s=this.json;if(i.textures.has(e))return i.textures.get(e);s.textures||(s.textures=[]),e instanceof Ht&&(e=await this.decompressTextureAsync(e,n.maxTextureSize));let r=e.userData.mimeType,o=this.processImage(e.image,e.format,e.flipY,r),c={sampler:this.processSampler(e)};r==="image/webp"?(c.extensions=c.extensions||{},c.extensions.EXT_texture_webp={source:o},this.extensionsUsed.EXT_texture_webp=!0,this.extensionsRequired.EXT_texture_webp=!0):c.source=o,e.name&&(c.name=e.name),await this._invokeAllAsync(async function(u){u.writeTexture&&await u.writeTexture(e,c)});let l=s.textures.push(c)-1;return i.textures.set(e,l),l}async processMaterialAsync(e,t){let n=this.cache,i=this.json,s=t!==void 0&&t.hasAttribute("tangent"),r=e.normalMap?e.uuid+":"+s:e.uuid;if(n.materials.has(r))return n.materials.get(r);if(e.isShaderMaterial)return console.warn("GLTFExporter: THREE.ShaderMaterial not supported."),null;i.materials||(i.materials=[]);let o={pbrMetallicRoughness:{}};e.isMeshStandardMaterial!==!0&&e.isMeshBasicMaterial!==!0&&console.warn("GLTFExporter: Use MeshStandardMaterial or MeshBasicMaterial for best results.");let c=e.color.toArray().concat([e.opacity]);if(Rt(c,[1,1,1,1])||(o.pbrMetallicRoughness.baseColorFactor=c),e.isMeshStandardMaterial?(o.pbrMetallicRoughness.metallicFactor=e.metalness,o.pbrMetallicRoughness.roughnessFactor=e.roughness):(o.pbrMetallicRoughness.metallicFactor=0,o.pbrMetallicRoughness.roughnessFactor=1),e.metalnessMap||e.roughnessMap){let u=await this.buildMetalRoughTextureAsync(e.metalnessMap,e.roughnessMap),h={index:await this.processTextureAsync(u),texCoord:u.channel};this.applyTextureTransform(h,u),o.pbrMetallicRoughness.metallicRoughnessTexture=h}if(e.map){let u={index:await this.processTextureAsync(e.map),texCoord:e.map.channel};this.applyTextureTransform(u,e.map),o.pbrMetallicRoughness.baseColorTexture=u}if(e.emissive){let u=e.emissive;if(Math.max(u.r,u.g,u.b)>0&&(o.emissiveFactor=e.emissive.toArray()),e.emissiveMap){let f={index:await this.processTextureAsync(e.emissiveMap),texCoord:e.emissiveMap.channel};this.applyTextureTransform(f,e.emissiveMap),o.emissiveTexture=f}}if(e.normalMap){let u=e.normalScale,h=u.x<0,f=s?u.y<0:u.y>0,d=e.normalMap;if(h||f){n.normalMaps.has(e.normalMap)===!1&&n.normalMaps.set(e.normalMap,{});let m=n.normalMaps.get(e.normalMap),b=`${h}:${f}`;m[b]===void 0&&(m[b]=await this.buildNormalMapTextureAsync(e.normalMap,h,f)),d=m[b]}let p={index:await this.processTextureAsync(d),texCoord:e.normalMap.channel};Math.abs(u.x)!==1&&(p.scale=Math.abs(u.x)),this.applyTextureTransform(p,e.normalMap),o.normalTexture=p}if(e.aoMap){let u={index:await this.processTextureAsync(e.aoMap),texCoord:e.aoMap.channel};e.aoMapIntensity!==1&&(u.strength=e.aoMapIntensity),this.applyTextureTransform(u,e.aoMap),o.occlusionTexture=u}e.transparent?o.alphaMode="BLEND":e.alphaTest>0&&(o.alphaMode="MASK",o.alphaCutoff=e.alphaTest),e.side===Mi&&(o.doubleSided=!0),e.name!==""&&(o.name=e.name),this.serializeUserData(e,o),await this._invokeAllAsync(async function(u){u.writeMaterialAsync&&await u.writeMaterialAsync(e,o)});let l=i.materials.push(o)-1;return n.materials.set(r,l),l}async processMeshAsync(e){let t=this.cache,n=this.json,i=[e.geometry.uuid];if(Array.isArray(e.material))for(let y=0,T=e.material.length;y<T;y++)i.push(e.material[y].uuid);else i.push(e.material.uuid);let s=i.join(":");if(t.meshes.has(s))return t.meshes.get(s);let r=e.geometry,o;e.isLineSegments?o=K.LINES:e.isLineLoop?o=K.LINE_LOOP:e.isLine?o=K.LINE_STRIP:e.isPoints?o=K.POINTS:o=e.material.wireframe?K.LINES:K.TRIANGLES;let c={},l={},u=[],h=[],f={uv:"TEXCOORD_0",uv1:"TEXCOORD_1",uv2:"TEXCOORD_2",uv3:"TEXCOORD_3",color:"COLOR_0",skinWeight:"WEIGHTS_0",skinIndex:"JOINTS_0"},d=r.getAttribute("normal");d!==void 0&&!this.isNormalizedNormalAttribute(d)&&(console.warn("THREE.GLTFExporter: Creating normalized normal attribute from the non-normalized one."),r.setAttribute("normal",this.createNormalizedNormalAttribute(d)));let p=null;for(let y in r.attributes){if(y.slice(0,5)==="morph")continue;let T=r.attributes[y];if(y=f[y]||y.toUpperCase(),!/^(POSITION|NORMAL|TANGENT|TEXCOORD_\d+|COLOR_\d+|JOINTS_\d+|WEIGHTS_\d+)$/.test(y)&&!y.startsWith("_")&&(y="_"+y),t.attributes.has(this.getUID(T))){l[y]=t.attributes.get(this.getUID(T));continue}p=null;let A=T.array;y==="JOINTS_0"&&!(A instanceof Uint16Array)&&!(A instanceof Uint8Array)?(console.warn('GLTFExporter: Attribute "skinIndex" converted to type UNSIGNED_SHORT.'),p=Kt.Utils.toTypedBufferAttribute(T,Uint16Array)):(A instanceof Uint32Array||A instanceof Int32Array)&&!y.startsWith("_")&&(console.warn(`GLTFExporter: Attribute "${y}" converted to type FLOAT.`),p=Kt.Utils.toTypedBufferAttribute(T,Float32Array));let g=this.processAccessor(p||T,r);g!==null&&(y.startsWith("_")||this.detectMeshQuantization(y,T),l[y]=g,t.attributes.set(this.getUID(T),g))}if(d!==void 0&&r.setAttribute("normal",d),Object.keys(l).length===0)return null;if(e.morphTargetInfluences!==void 0&&e.morphTargetInfluences.length>0){let y=[],T=[],M={};if(e.morphTargetDictionary!==void 0)for(let A in e.morphTargetDictionary)M[e.morphTargetDictionary[A]]=A;for(let A=0;A<e.morphTargetInfluences.length;++A){let g={},w=!1;for(let R in r.morphAttributes){if(R!=="position"&&R!=="normal"){w||(console.warn("GLTFExporter: Only POSITION and NORMAL morph are supported."),w=!0);continue}let C=r.morphAttributes[R][A],N=R.toUpperCase(),L=r.attributes[R];if(t.attributes.has(this.getUID(C,!0))){g[N]=t.attributes.get(this.getUID(C,!0));continue}let F=C.clone();if(!r.morphTargetsRelative)for(let I=0,O=C.count;I<O;I++)for(let B=0;B<C.itemSize;B++)B===0&&F.setX(I,C.getX(I)-L.getX(I)),B===1&&F.setY(I,C.getY(I)-L.getY(I)),B===2&&F.setZ(I,C.getZ(I)-L.getZ(I)),B===3&&F.setW(I,C.getW(I)-L.getW(I));g[N]=this.processAccessor(F,r),t.attributes.set(this.getUID(L,!0),g[N])}h.push(g),y.push(e.morphTargetInfluences[A]),e.morphTargetDictionary!==void 0&&T.push(M[A])}c.weights=y,T.length>0&&(c.extras={},c.extras.targetNames=T)}let m=Array.isArray(e.material);if(m&&r.groups.length===0)return null;let b=!1;if(m&&r.index===null){let y=[];for(let T=0,M=r.attributes.position.count;T<M;T++)y[T]=T;r.setIndex(y),b=!0}let x=m?e.material:[e.material],v=m?r.groups:[{materialIndex:0,start:void 0,count:void 0}];for(let y=0,T=v.length;y<T;y++){let M={mode:o,attributes:l};if(this.serializeUserData(r,M),h.length>0&&(M.targets=h),r.index!==null){let g=this.getUID(r.index);(v[y].start!==void 0||v[y].count!==void 0)&&(g+=":"+v[y].start+":"+v[y].count),t.attributes.has(g)?M.indices=t.attributes.get(g):(M.indices=this.processAccessor(r.index,r,v[y].start,v[y].count),t.attributes.set(g,M.indices)),M.indices===null&&delete M.indices}let A=await this.processMaterialAsync(x[v[y].materialIndex],r);A!==null&&(M.material=A),u.push(M)}b===!0&&r.setIndex(null),c.primitives=u,n.meshes||(n.meshes=[]),await this._invokeAllAsync(function(y){y.writeMesh&&y.writeMesh(e,c)});let S=n.meshes.push(c)-1;return t.meshes.set(s,S),S}detectMeshQuantization(e,t){if(this.extensionsUsed[Ka])return;let n;switch(t.array.constructor){case Int8Array:n="byte";break;case Uint8Array:n="unsigned byte";break;case Int16Array:n="short";break;case Uint16Array:n="unsigned short";break;default:return}t.normalized&&(n+=" normalized");let i=e.split("_",1)[0];Al[i]&&Al[i].includes(n)&&(this.extensionsUsed[Ka]=!0,this.extensionsRequired[Ka]=!0)}processCamera(e){let t=this.json;t.cameras||(t.cameras=[]);let n=e.isOrthographicCamera,i={type:n?"orthographic":"perspective"};return n?i.orthographic={xmag:e.right*2,ymag:e.top*2,zfar:e.far<=0?.001:e.far,znear:e.near<0?0:e.near}:i.perspective={aspectRatio:e.aspect,yfov:fn.degToRad(e.fov),zfar:e.far<=0?.001:e.far,znear:e.near<0?0:e.near},e.name!==""&&(i.name=e.type),t.cameras.push(i)-1}processAnimation(e,t){let n=this.json,i=this.nodeMap;n.animations||(n.animations=[]),e=Kt.Utils.mergeMorphTargetTracks(e.clone(),t);let s=e.tracks,r=[],o=[];for(let l=0;l<s.length;++l){let u=s[l],h=j.parseTrackName(u.name),f=j.findNode(t,h.nodeName),d=Tl[h.propertyName];if(h.objectName==="bones"&&(f.isSkinnedMesh===!0?f=f.skeleton.getBoneByName(h.objectIndex):f=void 0),!f||!d){console.warn('THREE.GLTFExporter: Could not export animation track "%s".',u.name);continue}let p=1,m=u.values.length/u.times.length;d===Tl.morphTargetInfluences&&(m/=f.morphTargetInfluences.length);let b;u.createInterpolant.isInterpolantFactoryMethodGLTFCubicSpline===!0?(b="CUBICSPLINE",m/=3):u.getInterpolation()===yt?b="STEP":b="LINEAR",o.push({input:this.processAccessor(new ae(u.times,p)),output:this.processAccessor(new ae(u.values,m)),interpolation:b}),r.push({sampler:o.length-1,target:{node:i.get(f),path:d}})}let c={name:e.name||"clip_"+n.animations.length,samplers:o,channels:r};return this.serializeUserData(e,c),n.animations.push(c),n.animations.length-1}processSkin(e){let t=this.json,n=this.nodeMap,i=t.nodes[n.get(e)],s=e.skeleton;if(s===void 0)return null;let r=e.skeleton.bones[0];if(r===void 0)return null;let o=[],c=new Float32Array(s.bones.length*16),l=new z;for(let h=0;h<s.bones.length;++h)o.push(n.get(s.bones[h])),l.copy(s.boneInverses[h]),l.multiply(e.bindMatrix).toArray(c,h*16);return t.skins===void 0&&(t.skins=[]),t.skins.push({inverseBindMatrices:this.processAccessor(new ae(c,16)),joints:o,skeleton:n.get(r)}),i.skin=t.skins.length-1}async processNodeAsync(e){let t=this.json,n=this.options,i=this.nodeMap;if(t.nodes||(t.nodes=[]),e.pivot!==null)return await this._processNodeWithPivotAsync(e);let s={};if(n.trs){let o=e.quaternion.toArray(),c=e.position.toArray(),l=e.scale.toArray();Rt(o,[0,0,0,1])||(s.rotation=o),Rt(c,[0,0,0])||(s.translation=c),Rt(l,[1,1,1])||(s.scale=l)}else e.matrixAutoUpdate&&e.updateMatrix(),tm(e.matrix)===!1&&(s.matrix=e.matrix.elements);if(e.name!==""&&(s.name=String(e.name)),this.serializeUserData(e,s),e.isMesh||e.isLine||e.isPoints){let o=await this.processMeshAsync(e);o!==null&&(s.mesh=o)}else e.isCamera&&(s.camera=this.processCamera(e));e.isSkinnedMesh&&this.skins.push(e);let r=t.nodes.push(s)-1;if(i.set(e,r),e.children.length>0){let o=[];for(let c=0,l=e.children.length;c<l;c++){let u=e.children[c];if(u.visible||n.onlyVisible===!1){let h=await this.processNodeAsync(u);h!==null&&o.push(h)}}o.length>0&&(s.children=o)}return await this._invokeAllAsync(function(o){o.writeNode&&o.writeNode(e,s)}),r}async _processNodeWithPivotAsync(e){let t=this.json,n=this.options,i=this.nodeMap,s=e.pivot,r={},o=e.quaternion.toArray(),c=[e.position.x+s.x,e.position.y+s.y,e.position.z+s.z],l=e.scale.toArray();Rt(o,[0,0,0,1])||(r.rotation=o),Rt(c,[0,0,0])||(r.translation=c),Rt(l,[1,1,1])||(r.scale=l),r.extras={pivot:s.toArray()},e.name!==""&&(r.name=String(e.name)),this.serializeUserData(e,r);let u=t.nodes.push(r)-1;i.set(e,u);let h={},f=[-s.x,-s.y,-s.z];if(Rt(f,[0,0,0])||(h.translation=f),e.isMesh||e.isLine||e.isPoints){let m=await this.processMeshAsync(e);m!==null&&(h.mesh=m)}else e.isCamera&&(h.camera=this.processCamera(e));e.isSkinnedMesh&&this.skins.push(e);let p=[t.nodes.push(h)-1];if(e.children.length>0){let m=[];for(let b=0,x=e.children.length;b<x;b++){let v=e.children[b];if(v.visible||n.onlyVisible===!1){let S=await this.processNodeAsync(v);S!==null&&m.push(S)}}m.length>0&&(h.children=m)}return r.children=p,await this._invokeAllAsync(function(m){m.writeNode&&m.writeNode(e,r)}),u}async processSceneAsync(e){let t=this.json,n=this.options;t.scenes||(t.scenes=[],t.scene=0);let i={};e.name!==""&&(i.name=e.name),t.scenes.push(i);let s=[];for(let r=0,o=e.children.length;r<o;r++){let c=e.children[r];if(c.visible||n.onlyVisible===!1){let l=await this.processNodeAsync(c);l!==null&&s.push(l)}}s.length>0&&(i.nodes=s),this.serializeUserData(e,i)}async processObjectsAsync(e){let t=new Nn;t.name="AuxScene";for(let n=0;n<e.length;n++)t.children.push(e[n]);await this.processSceneAsync(t)}async processInputAsync(e){let t=this.options;e=e instanceof Array?e:[e],await this._invokeAllAsync(function(i){i.beforeParse&&i.beforeParse(e)});let n=[];for(let i=0;i<e.length;i++)e[i]instanceof Nn?await this.processSceneAsync(e[i]):n.push(e[i]);n.length>0&&await this.processObjectsAsync(n);for(let i=0;i<this.skins.length;++i)this.processSkin(this.skins[i]);if(e.length===1)for(let i=0;i<t.animations.length;++i)this.processAnimation(t.animations[i],e[0]);else for(let i=0;i<e.length;i++){let s=t.animations[i]||[];for(let r=0;r<s.length;++r)this.processAnimation(s[r],e[i])}await this._invokeAllAsync(function(i){i.afterParse&&i.afterParse(e)})}async _invokeAllAsync(e){for(let t=0,n=this.plugins.length;t<n;t++)await e(this.plugins[t])}},Za=class{constructor(e){this.writer=e,this.name="KHR_lights_punctual"}writeNode(e,t){if(!e.isLight)return;if(!e.isDirectionalLight&&!e.isPointLight&&!e.isSpotLight){console.warn("THREE.GLTFExporter: Only directional, point, and spot lights are supported.",e);return}let n=this.writer,i=n.json,s=n.extensionsUsed,r={};e.name&&(r.name=e.name),r.color=e.color.toArray(),r.intensity=e.intensity,e.isDirectionalLight?r.type="directional":e.isPointLight?(r.type="point",e.distance>0&&(r.range=e.distance)):e.isSpotLight&&(r.type="spot",e.distance>0&&(r.range=e.distance),r.spot={},r.spot.innerConeAngle=(1-e.penumbra)*e.angle,r.spot.outerConeAngle=e.angle),e.decay!==void 0&&e.decay!==2&&console.warn("THREE.GLTFExporter: Light decay may be lost. glTF is physically-based, and expects light.decay=2."),e.target&&(e.target.parent!==e||e.target.position.x!==0||e.target.position.y!==0||e.target.position.z!==-1)&&console.warn("THREE.GLTFExporter: Light direction may be lost. For best results, make light.target a child of the light with position 0,0,-1."),s[this.name]||(i.extensions=i.extensions||{},i.extensions[this.name]={lights:[]},s[this.name]=!0);let o=i.extensions[this.name].lights;o.push(r),t.extensions=t.extensions||{},t.extensions[this.name]={light:o.length-1}}},$a=class{constructor(e){this.writer=e,this.name="KHR_materials_unlit"}async writeMaterialAsync(e,t){if(!e.isMeshBasicMaterial)return;let i=this.writer.extensionsUsed;t.extensions=t.extensions||{},t.extensions[this.name]={},i[this.name]=!0,t.pbrMetallicRoughness.metallicFactor=0,t.pbrMetallicRoughness.roughnessFactor=.9}},Qa=class{constructor(e){this.writer=e,this.name="KHR_materials_clearcoat"}async writeMaterialAsync(e,t){if(!e.isMeshPhysicalMaterial||e.clearcoat===0)return;let n=this.writer,i=n.extensionsUsed,s={};if(s.clearcoatFactor=e.clearcoat,e.clearcoatMap){let r={index:await n.processTextureAsync(e.clearcoatMap),texCoord:e.clearcoatMap.channel};n.applyTextureTransform(r,e.clearcoatMap),s.clearcoatTexture=r}if(s.clearcoatRoughnessFactor=e.clearcoatRoughness,e.clearcoatRoughnessMap){let r={index:await n.processTextureAsync(e.clearcoatRoughnessMap),texCoord:e.clearcoatRoughnessMap.channel};n.applyTextureTransform(r,e.clearcoatRoughnessMap),s.clearcoatRoughnessTexture=r}if(e.clearcoatNormalMap){let r={index:await n.processTextureAsync(e.clearcoatNormalMap),texCoord:e.clearcoatNormalMap.channel};e.clearcoatNormalScale.x!==1&&(r.scale=e.clearcoatNormalScale.x),n.applyTextureTransform(r,e.clearcoatNormalMap),s.clearcoatNormalTexture=r}t.extensions=t.extensions||{},t.extensions[this.name]=s,i[this.name]=!0}},eo=class{constructor(e){this.writer=e,this.name="KHR_materials_dispersion"}async writeMaterialAsync(e,t){if(!e.isMeshPhysicalMaterial||e.dispersion===0)return;let i=this.writer.extensionsUsed,s={};s.dispersion=e.dispersion,t.extensions=t.extensions||{},t.extensions[this.name]=s,i[this.name]=!0}},to=class{constructor(e){this.writer=e,this.name="KHR_materials_iridescence"}async writeMaterialAsync(e,t){if(!e.isMeshPhysicalMaterial||e.iridescence===0)return;let n=this.writer,i=n.extensionsUsed,s={};if(s.iridescenceFactor=e.iridescence,e.iridescenceMap){let r={index:await n.processTextureAsync(e.iridescenceMap),texCoord:e.iridescenceMap.channel};n.applyTextureTransform(r,e.iridescenceMap),s.iridescenceTexture=r}if(s.iridescenceIor=e.iridescenceIOR,s.iridescenceThicknessMinimum=e.iridescenceThicknessRange[0],s.iridescenceThicknessMaximum=e.iridescenceThicknessRange[1],e.iridescenceThicknessMap){let r={index:await n.processTextureAsync(e.iridescenceThicknessMap),texCoord:e.iridescenceThicknessMap.channel};n.applyTextureTransform(r,e.iridescenceThicknessMap),s.iridescenceThicknessTexture=r}t.extensions=t.extensions||{},t.extensions[this.name]=s,i[this.name]=!0}},no=class{constructor(e){this.writer=e,this.name="KHR_materials_transmission"}async writeMaterialAsync(e,t){if(!e.isMeshPhysicalMaterial||e.transmission===0)return;let n=this.writer,i=n.extensionsUsed,s={};if(s.transmissionFactor=e.transmission,e.transmissionMap){let r={index:await n.processTextureAsync(e.transmissionMap),texCoord:e.transmissionMap.channel};n.applyTextureTransform(r,e.transmissionMap),s.transmissionTexture=r}t.extensions=t.extensions||{},t.extensions[this.name]=s,i[this.name]=!0}},io=class{constructor(e){this.writer=e,this.name="KHR_materials_volume"}async writeMaterialAsync(e,t){if(!e.isMeshPhysicalMaterial||e.transmission===0)return;let n=this.writer,i=n.extensionsUsed,s={};if(s.thicknessFactor=e.thickness,e.thicknessMap){let r={index:await n.processTextureAsync(e.thicknessMap),texCoord:e.thicknessMap.channel};n.applyTextureTransform(r,e.thicknessMap),s.thicknessTexture=r}e.attenuationDistance!==1/0&&(s.attenuationDistance=e.attenuationDistance),s.attenuationColor=e.attenuationColor.toArray(),t.extensions=t.extensions||{},t.extensions[this.name]=s,i[this.name]=!0}},so=class{constructor(e){this.writer=e,this.name="KHR_materials_ior"}async writeMaterialAsync(e,t){if(!e.isMeshPhysicalMaterial||e.ior===1.5)return;let i=this.writer.extensionsUsed,s={};s.ior=e.ior,t.extensions=t.extensions||{},t.extensions[this.name]=s,i[this.name]=!0}},ro=class{constructor(e){this.writer=e,this.name="KHR_materials_specular"}async writeMaterialAsync(e,t){if(!e.isMeshPhysicalMaterial||e.specularIntensity===1&&e.specularColor.equals(jp)&&!e.specularIntensityMap&&!e.specularColorMap)return;let n=this.writer,i=n.extensionsUsed,s={};if(e.specularIntensityMap){let r={index:await n.processTextureAsync(e.specularIntensityMap),texCoord:e.specularIntensityMap.channel};n.applyTextureTransform(r,e.specularIntensityMap),s.specularTexture=r}if(e.specularColorMap){let r={index:await n.processTextureAsync(e.specularColorMap),texCoord:e.specularColorMap.channel};n.applyTextureTransform(r,e.specularColorMap),s.specularColorTexture=r}s.specularFactor=e.specularIntensity,s.specularColorFactor=e.specularColor.toArray(),t.extensions=t.extensions||{},t.extensions[this.name]=s,i[this.name]=!0}},ao=class{constructor(e){this.writer=e,this.name="KHR_materials_sheen"}async writeMaterialAsync(e,t){if(!e.isMeshPhysicalMaterial||e.sheen==0)return;let n=this.writer,i=n.extensionsUsed,s={};if(e.sheenRoughnessMap){let r={index:await n.processTextureAsync(e.sheenRoughnessMap),texCoord:e.sheenRoughnessMap.channel};n.applyTextureTransform(r,e.sheenRoughnessMap),s.sheenRoughnessTexture=r}if(e.sheenColorMap){let r={index:await n.processTextureAsync(e.sheenColorMap),texCoord:e.sheenColorMap.channel};n.applyTextureTransform(r,e.sheenColorMap),s.sheenColorTexture=r}s.sheenRoughnessFactor=e.sheenRoughness,s.sheenColorFactor=e.sheenColor.toArray(),t.extensions=t.extensions||{},t.extensions[this.name]=s,i[this.name]=!0}},oo=class{constructor(e){this.writer=e,this.name="KHR_materials_anisotropy"}async writeMaterialAsync(e,t){if(!e.isMeshPhysicalMaterial||e.anisotropy==0)return;let n=this.writer,i=n.extensionsUsed,s={};if(e.anisotropyMap){let r={index:await n.processTextureAsync(e.anisotropyMap)};n.applyTextureTransform(r,e.anisotropyMap),s.anisotropyTexture=r}s.anisotropyStrength=e.anisotropy,s.anisotropyRotation=e.anisotropyRotation,t.extensions=t.extensions||{},t.extensions[this.name]=s,i[this.name]=!0}},co=class{constructor(e){this.writer=e,this.name="KHR_materials_emissive_strength"}async writeMaterialAsync(e,t){if(!e.isMeshStandardMaterial||e.emissiveIntensity===1)return;let i=this.writer.extensionsUsed,s={};s.emissiveStrength=e.emissiveIntensity,t.extensions=t.extensions||{},t.extensions[this.name]=s,i[this.name]=!0}},lo=class{constructor(e){this.writer=e,this.name="EXT_materials_bump"}async writeMaterialAsync(e,t){if(!e.isMeshStandardMaterial||e.bumpScale===1&&!e.bumpMap)return;let n=this.writer,i=n.extensionsUsed,s={};if(e.bumpMap){let r={index:await n.processTextureAsync(e.bumpMap),texCoord:e.bumpMap.channel};n.applyTextureTransform(r,e.bumpMap),s.bumpTexture=r}s.bumpFactor=e.bumpScale,t.extensions=t.extensions||{},t.extensions[this.name]=s,i[this.name]=!0}},uo=class{constructor(e){this.writer=e,this.name="EXT_mesh_gpu_instancing"}writeNode(e,t){if(!e.isInstancedMesh)return;let n=this.writer,i=e,s=new Float32Array(i.count*3),r=new Float32Array(i.count*4),o=new Float32Array(i.count*3),c=new z,l=new E,u=new pe,h=new E;for(let d=0;d<i.count;d++)i.getMatrixAt(d,c),c.decompose(l,u,h),l.toArray(s,d*3),u.toArray(r,d*4),h.toArray(o,d*3);let f={TRANSLATION:n.processAccessor(new ae(s,3)),ROTATION:n.processAccessor(new ae(r,4)),SCALE:n.processAccessor(new ae(o,3))};i.instanceColor&&(f._COLOR_0=n.processAccessor(i.instanceColor)),t.extensions=t.extensions||{},t.extensions[this.name]={attributes:f},n.extensionsUsed[this.name]=!0,n.extensionsRequired[this.name]=!0}};Kt.Utils={insertKeyframe:function(a,e){let n=a.getValueSize(),i=new a.TimeBufferType(a.times.length+1),s=new a.ValueBufferType(a.values.length+n),r=a.createInterpolant(new a.ValueBufferType(n)),o;if(a.times.length===0){i[0]=e;for(let c=0;c<n;c++)s[c]=0;o=0}else if(e<a.times[0]){if(Math.abs(a.times[0]-e)<.001)return 0;i[0]=e,i.set(a.times,1),s.set(r.evaluate(e),0),s.set(a.values,n),o=0}else if(e>a.times[a.times.length-1]){if(Math.abs(a.times[a.times.length-1]-e)<.001)return a.times.length-1;i[i.length-1]=e,i.set(a.times,0),s.set(a.values,0),s.set(r.evaluate(e),a.values.length),o=i.length-1}else for(let c=0;c<a.times.length;c++){if(Math.abs(a.times[c]-e)<.001)return c;if(a.times[c]<e&&a.times[c+1]>e){i.set(a.times.slice(0,c+1),0),i[c+1]=e,i.set(a.times.slice(c+1),c+2),s.set(a.values.slice(0,(c+1)*n),0),s.set(r.evaluate(e),(c+1)*n),s.set(a.values.slice((c+1)*n),(c+2)*n),o=c+1;break}}return a.times=i,a.values=s,o},mergeMorphTargetTracks:function(a,e){let t=[],n={},i=a.tracks;for(let s=0;s<i.length;++s){let r=i[s],o=j.parseTrackName(r.name),c=j.findNode(e,o.nodeName);if(o.propertyName!=="morphTargetInfluences"||o.propertyIndex===void 0){t.push(r);continue}if(r.createInterpolant!==r.InterpolantFactoryMethodDiscrete&&r.createInterpolant!==r.InterpolantFactoryMethodLinear){if(r.createInterpolant.isInterpolantFactoryMethodGLTFCubicSpline)throw new Error("THREE.GLTFExporter: Cannot merge tracks with glTF CUBICSPLINE interpolation.");console.warn("THREE.GLTFExporter: Morph target interpolation mode not yet supported. Using LINEAR instead."),r=r.clone(),r.setInterpolation(vt)}let l=c.morphTargetInfluences.length,u=c.morphTargetDictionary[o.propertyIndex];if(u===void 0)throw new Error("THREE.GLTFExporter: Morph target name not found: "+o.propertyIndex);let h;if(n[c.uuid]===void 0){h=r.clone();let d=new h.ValueBufferType(l*h.times.length);for(let p=0;p<h.times.length;p++)d[p*l+u]=h.values[p];h.name=(o.nodeName||"")+".morphTargetInfluences",h.values=d,n[c.uuid]=h,t.push(h);continue}let f=r.createInterpolant(new r.ValueBufferType(1));h=n[c.uuid];for(let d=0;d<h.times.length;d++)h.values[d*l+u]=f.evaluate(h.times[d]);for(let d=0;d<r.times.length;d++){let p=this.insertKeyframe(h,r.times[d]);h.values[p*l+u]=r.values[d]}}return a.tracks=t,a},toTypedBufferAttribute:function(a,e){let t=new ae(new e(a.count*a.itemSize),a.itemSize,!1);if(!a.normalized&&!a.isInterleavedBufferAttribute)return t.array.set(a.array),t;for(let n=0,i=a.count;n<i;n++)for(let s=0;s<a.itemSize;s++)t.setComponent(n,s,a.getComponent(n,s));return t}};var Me=Uint8Array,Ge=Uint16Array,xo=Int32Array,bo=new Me([0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0,0,0,0]),_o=new Me([0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13,0,0]),Cl=new Me([16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15]),Fl=function(a,e){for(var t=new Ge(31),n=0;n<31;++n)t[n]=e+=1<<a[n-1];for(var i=new xo(t[30]),n=1;n<30;++n)for(var s=t[n];s<t[n+1];++s)i[s]=s-t[n]<<5|n;return{b:t,r:i}},Ul=Fl(bo,2),sm=Ul.b,fo=Ul.r;sm[28]=258,fo[258]=28;var Ol=Fl(_o,0),fS=Ol.b,Il=Ol.r,po=new Ge(32768);for(Q=0;Q<32768;++Q)Ct=(Q&43690)>>1|(Q&21845)<<1,Ct=(Ct&52428)>>2|(Ct&13107)<<2,Ct=(Ct&61680)>>4|(Ct&3855)<<4,po[Q]=((Ct&65280)>>8|(Ct&255)<<8)>>1;var Ct,Q,Di=(function(a,e,t){for(var n=a.length,i=0,s=new Ge(e);i<n;++i)a[i]&&++s[a[i]-1];var r=new Ge(e);for(i=1;i<e;++i)r[i]=r[i-1]+s[i-1]<<1;var o;if(t){o=new Ge(1<<e);var c=15-e;for(i=0;i<n;++i)if(a[i])for(var l=i<<4|a[i],u=e-a[i],h=r[a[i]-1]++<<u,f=h|(1<<u)-1;h<=f;++h)o[po[h]>>c]=l}else for(o=new Ge(n),i=0;i<n;++i)a[i]&&(o[i]=po[r[a[i]-1]++]>>15-a[i]);return o}),pn=new Me(288);for(Q=0;Q<144;++Q)pn[Q]=8;var Q;for(Q=144;Q<256;++Q)pn[Q]=9;var Q;for(Q=256;Q<280;++Q)pn[Q]=7;var Q;for(Q=280;Q<288;++Q)pn[Q]=8;var Q,ks=new Me(32);for(Q=0;Q<32;++Q)ks[Q]=5;var Q,rm=Di(pn,9,0);var am=Di(ks,5,0);var Bl=function(a){return(a+7)/8|0},kl=function(a,e,t){return(e==null||e<0)&&(e=0),(t==null||t>a.length)&&(t=a.length),new Me(a.subarray(e,t))};var om=["unexpected EOF","invalid block type","invalid length/literal","invalid distance","stream finished","no stream handler",,"no callback","invalid UTF-8 data","extra field too long","date not in range 1980-2099","filename too long","stream finishing","invalid zip data"],Vs=function(a,e,t){var n=new Error(e||om[a]);if(n.code=a,Error.captureStackTrace&&Error.captureStackTrace(n,Vs),!t)throw n;return n};var It=function(a,e,t){t<<=e&7;var n=e/8|0;a[n]|=t,a[n+1]|=t>>8},Pi=function(a,e,t){t<<=e&7;var n=e/8|0;a[n]|=t,a[n+1]|=t>>8,a[n+2]|=t>>16},ho=function(a,e){for(var t=[],n=0;n<a.length;++n)a[n]&&t.push({s:n,f:a[n]});var i=t.length,s=t.slice();if(!i)return{t:Vl,l:0};if(i==1){var r=new Me(t[0].s+1);return r[t[0].s]=1,{t:r,l:1}}t.sort(function(T,M){return T.f-M.f}),t.push({s:-1,f:25001});var o=t[0],c=t[1],l=0,u=1,h=2;for(t[0]={s:-1,f:o.f+c.f,l:o,r:c};u!=i-1;)o=t[t[l].f<t[h].f?l++:h++],c=t[l!=u&&t[l].f<t[h].f?l++:h++],t[u++]={s:-1,f:o.f+c.f,l:o,r:c};for(var f=s[0].s,n=1;n<i;++n)s[n].s>f&&(f=s[n].s);var d=new Ge(f+1),p=mo(t[u-1],d,0);if(p>e){var n=0,m=0,b=p-e,x=1<<b;for(s.sort(function(M,A){return d[A.s]-d[M.s]||M.f-A.f});n<i;++n){var v=s[n].s;if(d[v]>e)m+=x-(1<<p-d[v]),d[v]=e;else break}for(m>>=b;m>0;){var S=s[n].s;d[S]<e?m-=1<<e-d[S]++-1:++n}for(;n>=0&&m;--n){var y=s[n].s;d[y]==e&&(--d[y],++m)}p=e}return{t:new Me(d),l:p}},mo=function(a,e,t){return a.s==-1?Math.max(mo(a.l,e,t+1),mo(a.r,e,t+1)):e[a.s]=t},Pl=function(a){for(var e=a.length;e&&!a[--e];);for(var t=new Ge(++e),n=0,i=a[0],s=1,r=function(c){t[n++]=c},o=1;o<=e;++o)if(a[o]==i&&o!=e)++s;else{if(!i&&s>2){for(;s>138;s-=138)r(32754);s>2&&(r(s>10?s-11<<5|28690:s-3<<5|12305),s=0)}else if(s>3){for(r(i),--s;s>6;s-=6)r(8304);s>2&&(r(s-3<<5|8208),s=0)}for(;s--;)r(i);s=1,i=a[o]}return{c:t.subarray(0,n),n:e}},Li=function(a,e){for(var t=0,n=0;n<e.length;++n)t+=a[n]*e[n];return t},zl=function(a,e,t){var n=t.length,i=Bl(e+2);a[i]=n&255,a[i+1]=n>>8,a[i+2]=a[i]^255,a[i+3]=a[i+1]^255;for(var s=0;s<n;++s)a[i+s+4]=t[s];return(i+4+n)*8},Ll=function(a,e,t,n,i,s,r,o,c,l,u){It(e,u++,t),++i[256];for(var h=ho(i,15),f=h.t,d=h.l,p=ho(s,15),m=p.t,b=p.l,x=Pl(f),v=x.c,S=x.n,y=Pl(m),T=y.c,M=y.n,A=new Ge(19),g=0;g<v.length;++g)++A[v[g]&31];for(var g=0;g<T.length;++g)++A[T[g]&31];for(var w=ho(A,7),R=w.t,C=w.l,N=19;N>4&&!R[Cl[N-1]];--N);var L=l+5<<3,F=Li(i,pn)+Li(s,ks)+r,I=Li(i,f)+Li(s,m)+r+14+3*N+Li(A,R)+2*A[16]+3*A[17]+7*A[18];if(c>=0&&L<=F&&L<=I)return zl(e,u,a.subarray(c,c+l));var O,B,k,W;if(It(e,u,1+(I<F)),u+=2,I<F){O=Di(f,d,0),B=f,k=Di(m,b,0),W=m;var me=Di(R,C,0);It(e,u,S-257),It(e,u+5,M-1),It(e,u+10,N-4),u+=14;for(var g=0;g<N;++g)It(e,u+3*g,R[Cl[g]]);u+=3*N;for(var se=[v,T],we=0;we<2;++we)for(var Fe=se[we],g=0;g<Fe.length;++g){var Ee=Fe[g]&31;It(e,u,me[Ee]),u+=R[Ee],Ee>15&&(It(e,u,Fe[g]>>5&127),u+=Fe[g]>>12)}}else O=rm,B=pn,k=am,W=ks;for(var g=0;g<o;++g){var ge=n[g];if(ge>255){var Ee=ge>>18&31;Pi(e,u,O[Ee+257]),u+=B[Ee+257],Ee>7&&(It(e,u,ge>>23&31),u+=bo[Ee]);var lt=ge&31;Pi(e,u,k[lt]),u+=W[lt],lt>3&&(Pi(e,u,ge>>5&8191),u+=_o[lt])}else Pi(e,u,O[ge]),u+=B[ge]}return Pi(e,u,O[256]),u+B[256]},cm=new xo([65540,131080,131088,131104,262176,1048704,1048832,2114560,2117632]),Vl=new Me(0),lm=function(a,e,t,n,i,s){var r=s.z||a.length,o=new Me(n+r+5*(1+Math.ceil(r/7e3))+i),c=o.subarray(n,o.length-i),l=s.l,u=(s.r||0)&7;if(e){u&&(c[0]=s.r>>3);for(var h=cm[e-1],f=h>>13,d=h&8191,p=(1<<t)-1,m=s.p||new Ge(32768),b=s.h||new Ge(p+1),x=Math.ceil(t/3),v=2*x,S=function(rr){return(a[rr]^a[rr+1]<<x^a[rr+2]<<v)&p},y=new xo(25e3),T=new Ge(288),M=new Ge(32),A=0,g=0,w=s.i||0,R=0,C=s.w||0,N=0;w+2<r;++w){var L=S(w),F=w&32767,I=b[L];if(m[F]=I,b[L]=F,C<=w){var O=r-w;if((A>7e3||R>24576)&&(O>423||!l)){u=Ll(a,c,0,y,T,M,g,R,N,w-N,u),R=A=g=0,N=w;for(var B=0;B<286;++B)T[B]=0;for(var B=0;B<30;++B)M[B]=0}var k=2,W=0,me=d,se=F-I&32767;if(O>2&&L==S(w-se))for(var we=Math.min(f,O)-1,Fe=Math.min(32767,w),Ee=Math.min(258,O);se<=Fe&&--me&&F!=I;){if(a[w+k]==a[w+k-se]){for(var ge=0;ge<Ee&&a[w+ge]==a[w+ge-se];++ge);if(ge>k){if(k=ge,W=se,ge>we)break;for(var lt=Math.min(se,ge-2),jn=0,B=0;B<lt;++B){var ut=w-se+B&32767,Zt=m[ut],Pt=ut-Zt&32767;Pt>jn&&(jn=Pt,I=ut)}}}F=I,I=m[F],se+=F-I&32767}if(W){y[R++]=268435456|fo[k]<<18|Il[W];var mn=fo[k]&31,gn=Il[W]&31;g+=bo[mn]+_o[gn],++T[257+mn],++M[gn],C=w+k,++A}else y[R++]=a[w],++T[a[w]]}}for(w=Math.max(w,C);w<r;++w)y[R++]=a[w],++T[a[w]];u=Ll(a,c,l,y,T,M,g,R,N,w-N,u),l||(s.r=u&7|c[u/8|0]<<3,u-=7,s.h=b,s.p=m,s.i=w,s.w=C)}else{for(var w=s.w||0;w<r+l;w+=65535){var sr=w+65535;sr>=r&&(c[u/8|0]=l,sr=r),u=zl(c,u+1,a.subarray(w,sr))}s.i=r}return kl(o,0,n+Bl(u)+i)},um=(function(){for(var a=new Int32Array(256),e=0;e<256;++e){for(var t=e,n=9;--n;)t=(t&1&&-306674912)^t>>>1;a[e]=t}return a})(),hm=function(){var a=-1;return{p:function(e){for(var t=a,n=0;n<e.length;++n)t=um[t&255^e[n]]^t>>>8;a=t},d:function(){return~a}}},Gl=function(){var a=1,e=0;return{p:function(t){for(var n=a,i=e,s=t.length|0,r=0;r!=s;){for(var o=Math.min(r+2655,s);r<o;++r)i+=n+=t[r];n=(n&65535)+15*(n>>16),i=(i&65535)+15*(i>>16)}a=n,e=i},d:function(){return a%=65521,e%=65521,(a&255)<<24|(a&65280)<<8|(e&255)<<8|e>>8}}},Hl=function(a,e,t,n,i){if(!i&&(i={l:1},e.dictionary)){var s=e.dictionary.subarray(-32768),r=new Me(s.length+a.length);r.set(s),r.set(a,s.length),a=r,i.w=s.length}return lm(a,e.level==null?6:e.level,e.mem==null?i.l?Math.ceil(Math.max(8,Math.min(13,Math.log(a.length)))*1.5):20:12+e.mem,t,n,i)},Wl=function(a,e){var t={};for(var n in a)t[n]=a[n];for(var n in e)t[n]=e[n];return t};var xe=function(a,e,t){for(;t;++e)a[e]=t,t>>>=8};var fm=function(a,e){var t=e.level,n=t==0?0:t<6?1:t==9?3:2;if(a[0]=120,a[1]=n<<6|(e.dictionary&&32),a[1]|=31-(a[0]<<8|a[1])%31,e.dictionary){var i=Gl();i.p(e.dictionary),xe(a,2,i.d())}};function dm(a,e){return Hl(a,e||{},0,0)}function Gs(a,e){e||(e={});var t=Gl();t.p(a);var n=Hl(a,e,e.dictionary?6:2,4);return fm(n,e),xe(n,n.length-4,t.d()),n}var Xl=function(a,e,t,n){for(var i in a){var s=a[i],r=e+i,o=n;Array.isArray(s)&&(o=Wl(n,s[1]),s=s[0]),ArrayBuffer.isView(s)?t[r]=[s,o]:(t[r+="/"]=[new Me(0),o],Xl(s,r,t,n))}},Dl=typeof TextEncoder<"u"&&new TextEncoder,pm=typeof TextDecoder<"u"&&new TextDecoder,mm=0;try{pm.decode(Vl,{stream:!0}),mm=1}catch{}function zs(a,e){if(e){for(var t=new Me(a.length),n=0;n<a.length;++n)t[n]=a.charCodeAt(n);return t}if(Dl)return Dl.encode(a);for(var i=a.length,s=new Me(a.length+(a.length>>1)),r=0,o=function(u){s[r++]=u},n=0;n<i;++n){if(r+5>s.length){var c=new Me(r+8+(i-n<<1));c.set(s),s=c}var l=a.charCodeAt(n);l<128||e?o(l):l<2048?(o(192|l>>6),o(128|l&63)):l>55295&&l<57344?(l=65536+(l&1047552)|a.charCodeAt(++n)&1023,o(240|l>>18),o(128|l>>12&63),o(128|l>>6&63),o(128|l&63)):(o(224|l>>12),o(128|l>>6&63),o(128|l&63))}return kl(s,0,r)}var go=function(a){var e=0;if(a)for(var t in a){var n=a[t].length;n>65535&&Vs(9),e+=n+4}return e},Nl=function(a,e,t,n,i,s,r,o){var c=n.length,l=t.extra,u=o&&o.length,h=go(l);xe(a,e,r!=null?33639248:67324752),e+=4,r!=null&&(a[e++]=20,a[e++]=t.os),a[e]=20,e+=2,a[e++]=t.flag<<1|(s<0&&8),a[e++]=i&&8,a[e++]=t.compression&255,a[e++]=t.compression>>8;var f=new Date(t.mtime==null?Date.now():t.mtime),d=f.getFullYear()-1980;if((d<0||d>119)&&Vs(10),xe(a,e,d<<25|f.getMonth()+1<<21|f.getDate()<<16|f.getHours()<<11|f.getMinutes()<<5|f.getSeconds()>>1),e+=4,s!=-1&&(xe(a,e,t.crc),xe(a,e+4,s<0?-s-2:s),xe(a,e+8,t.size)),xe(a,e+12,c),xe(a,e+14,h),e+=16,r!=null&&(xe(a,e,u),xe(a,e+6,t.attrs),xe(a,e+10,r),e+=14),a.set(n,e),e+=c,h)for(var p in l){var m=l[p],b=m.length;xe(a,e,+p),xe(a,e+2,b),a.set(m,e+4),e+=4+b}return u&&(a.set(o,e),e+=u),e},gm=function(a,e,t,n,i){xe(a,e,101010256),xe(a,e+8,t),xe(a,e+10,t),xe(a,e+12,n),xe(a,e+16,i)};function ql(a,e){e||(e={});var t={},n=[];Xl(a,"",t,e);var i=0,s=0;for(var r in t){var o=t[r],c=o[0],l=o[1],u=l.level==0?0:8,h=zs(r),f=h.length,d=l.comment,p=d&&zs(d),m=p&&p.length,b=go(l.extra);f>65535&&Vs(11);var x=u?dm(c,l):c,v=x.length,S=hm();S.p(c),n.push(Wl(l,{size:c.length,crc:S.d(),c:x,f:h,m:p,u:f!=r.length||p&&d.length!=m,o:i,compression:u})),i+=30+f+b+v,s+=76+2*(f+b)+(m||0)+v}for(var y=new Me(s+22),T=i,M=s-i,A=0;A<n.length;++A){var h=n[A];Nl(y,h.o,h,h.f,h.u,h.c.length);var g=30+h.f.length+go(h.extra);y.set(h.c,h.o+g),Nl(y,i,h,h.f,h.u,h.c.length,h.o,h.m),i+=16+g+(h.m?h.m.length:0)}return gm(y,i,n.length,M,T),y}var Yl=new TextEncoder,jl=new Set(["AnimationStack","AnimationLayer"]),ot=class a{constructor(e){ue(this,"id");ue(this,"_idBytes");ue(this,"propsType");ue(this,"propsData");ue(this,"elems");ue(this,"_endOffset");ue(this,"_propsLength");if(this.id=e,this._idBytes=Yl.encode(e),this._idBytes.length>255)throw new RangeError(`FBX node id too long: ${this._idBytes.length} UTF-8 bytes (max 255). id=${JSON.stringify(e)}`);this.propsType=[],this.propsData=[],this.elems=[],this._endOffset=-1,this._propsLength=-1}addChild(e){return this.elems.push(e),e}addEmpty(e){return this.addChild(new a(e))}addBool(e){this.propsType.push(66),this.propsData.push(new Uint8Array([e?1:0]))}addChar(e){this.propsType.push(67),this.propsData.push(new Uint8Array([e&255]))}addInt8(e){let t=new ArrayBuffer(1);new DataView(t).setInt8(0,e),this.propsType.push(90),this.propsData.push(new Uint8Array(t))}addInt16(e){let t=new ArrayBuffer(2);new DataView(t).setInt16(0,e,!0),this.propsType.push(89),this.propsData.push(new Uint8Array(t))}addInt32(e){let t=new ArrayBuffer(4);new DataView(t).setInt32(0,e,!0),this.propsType.push(73),this.propsData.push(new Uint8Array(t))}addInt64(e){let t=new ArrayBuffer(8);new DataView(t).setBigInt64(0,typeof e=="bigint"?e:BigInt(e),!0),this.propsType.push(76),this.propsData.push(new Uint8Array(t))}addFloat32(e){let t=new ArrayBuffer(4);new DataView(t).setFloat32(0,e,!0),this.propsType.push(70),this.propsData.push(new Uint8Array(t))}addFloat64(e){let t=new ArrayBuffer(8);new DataView(t).setFloat64(0,e,!0),this.propsType.push(68),this.propsData.push(new Uint8Array(t))}addBytes(e){let t=new Uint8Array(4+e.byteLength);new DataView(t.buffer).setUint32(0,e.byteLength,!0),t.set(e,4),this.propsType.push(82),this.propsData.push(t)}addString(e){let t=typeof e=="string"?Yl.encode(e):e,n=new Uint8Array(4+t.byteLength);new DataView(n.buffer).setUint32(0,t.byteLength,!0),n.set(t,4),this.propsType.push(83),this.propsData.push(n)}_addArray(e,t,n){let i=new Uint8Array(n),s,r;if(i.byteLength>128){let l=Gs(i,{level:1});s=1,r=l}else s=0,r=i;let o=new Uint8Array(12+r.byteLength),c=new DataView(o.buffer);c.setUint32(0,t,!0),c.setUint32(4,s,!0),c.setUint32(8,r.byteLength,!0),o.set(r,12),this.propsType.push(e),this.propsData.push(o)}addBoolArray(e){let t=e instanceof Uint8Array?e:Uint8Array.from(e,n=>n?1:0);this._addArray(98,t.length,t)}addByteArray(e){let t=e instanceof Uint8Array?e:Uint8Array.from(e);this._addArray(99,t.length,t)}addInt32Array(e){let t=e instanceof Int32Array?e:Int32Array.from(e);this._addArray(105,t.length,t.buffer.slice(t.byteOffset,t.byteOffset+t.byteLength))}addInt64Array(e){let t=e instanceof BigInt64Array?e:BigInt64Array.from(e,n=>typeof n=="bigint"?n:BigInt(n));this._addArray(108,t.length,t.buffer.slice(t.byteOffset,t.byteOffset+t.byteLength))}addFloat32Array(e){let t=e instanceof Float32Array?e:Float32Array.from(e);this._addArray(102,t.length,t.buffer.slice(t.byteOffset,t.byteOffset+t.byteLength))}addFloat64Array(e){let t=e instanceof Float64Array?e:Float64Array.from(e);this._addArray(100,t.length,t.buffer.slice(t.byteOffset,t.byteOffset+t.byteLength))}_calcOffsets(e,t,n){e+=n.metaSize,e+=1+this._idBytes.length;let i=0;for(let s=0;s<this.propsData.length;s++)i+=1+this.propsData[s].byteLength;return this._propsLength=i,e+=i,e=this._calcOffsetsChildren(e,t,n),this._endOffset=e,e}_calcOffsetsChildren(e,t,n){if(this.elems.length>0){let i=this.elems.length-1;for(let s=0;s<this.elems.length;s++)e=this.elems[s]._calcOffsets(e,s===i,n);e+=n.sentinelSize}else(this.propsData.length===0&&!t||jl.has(this.id))&&(e+=n.sentinelSize);return e}_write(e,t,n){if(this._endOffset<0||this._propsLength<0)throw new Error("_calcOffsets must run before _write");n.use64?(e.writeU64(BigInt(this._endOffset)),e.writeU64(BigInt(this.propsData.length)),e.writeU64(BigInt(this._propsLength))):(e.writeU32(this._endOffset),e.writeU32(this.propsData.length),e.writeU32(this._propsLength)),e.writeU8(this._idBytes.length),e.writeBytes(this._idBytes);for(let i=0;i<this.propsData.length;i++)e.writeU8(this.propsType[i]),e.writeBytes(this.propsData[i]);if(this._writeChildren(e,t,n),e.tell()!==this._endOffset)throw new Error(`FBXElem ${this.id}: end offset mismatch (expected ${this._endOffset}, got ${e.tell()})`)}_writeChildren(e,t,n){if(this.elems.length>0){let i=this.elems.length-1;for(let s=0;s<this.elems.length;s++)this.elems[s]._write(e,s===i,n);e.writeZeros(n.sentinelSize)}else(this.propsData.length===0&&!t||jl.has(this.id))&&e.writeZeros(n.sentinelSize)}};var Nm=new TextEncoder,Ni=class{constructor(e=4096){ue(this,"_buf");ue(this,"_view");ue(this,"_u8");ue(this,"_offset");this._buf=new ArrayBuffer(e),this._view=new DataView(this._buf),this._u8=new Uint8Array(this._buf),this._offset=0}get length(){return this._offset}tell(){return this._offset}_ensure(e){let t=this._offset+e;if(t<=this._buf.byteLength)return;let n=this._buf.byteLength;for(;n<t;)n*=2;let i=new ArrayBuffer(n);new Uint8Array(i).set(this._u8),this._buf=i,this._view=new DataView(i),this._u8=new Uint8Array(i)}writeU8(e){this._ensure(1),this._view.setUint8(this._offset,e),this._offset+=1}writeI8(e){this._ensure(1),this._view.setInt8(this._offset,e),this._offset+=1}writeU16(e){this._ensure(2),this._view.setUint16(this._offset,e,!0),this._offset+=2}writeI16(e){this._ensure(2),this._view.setInt16(this._offset,e,!0),this._offset+=2}writeU32(e){this._ensure(4),this._view.setUint32(this._offset,e,!0),this._offset+=4}writeI32(e){this._ensure(4),this._view.setInt32(this._offset,e,!0),this._offset+=4}writeF32(e){this._ensure(4),this._view.setFloat32(this._offset,e,!0),this._offset+=4}writeF64(e){this._ensure(8),this._view.setFloat64(this._offset,e,!0),this._offset+=8}writeU64(e){this._ensure(8),this._view.setBigUint64(this._offset,typeof e=="bigint"?e:BigInt(e),!0),this._offset+=8}writeI64(e){this._ensure(8),this._view.setBigInt64(this._offset,typeof e=="bigint"?e:BigInt(e),!0),this._offset+=8}writeBytes(e){this._ensure(e.byteLength),this._u8.set(e,this._offset),this._offset+=e.byteLength}writeUtf8(e){this.writeBytes(Nm.encode(e))}writeZeros(e){this._ensure(e),this._u8.fill(0,this._offset,this._offset+e),this._offset+=e}toUint8Array(){return this._u8.slice(0,this._offset)}toArrayBuffer(){return this.toUint8Array().buffer}};var Fm=new TextEncoder,Um=new Uint8Array([75,97,121,100,97,114,97,32,70,66,88,32,66,105,110,97,114,121,32,32,0,26,0]),Om=Fm.encode("1970-01-01 10:00:00:000"),Bm=new Uint8Array([40,179,42,235,182,36,204,194,191,200,176,42,169,43,252,241]),km=new Uint8Array([250,188,171,9,208,200,212,102,177,118,251,131,28,247,38,126]),zm=new Uint8Array([248,90,140,106,222,245,217,126,236,233,12,227,117,143,41,11]);function Vm(a){return a<7500?{use64:!1,metaSize:12,sentinelSize:13}:{use64:!0,metaSize:24,sentinelSize:25}}function Gm(a){let e=0;for(let t of a.elems)if(t.id==="FileId"?(t.propsType=[],t.propsData=[],t.addBytes(Bm),e++):t.id==="CreationTime"&&(t.propsType=[],t.propsData=[],t.addString(Om),e++),e===2)break}function yo(a,{version:e=7400}={}){if(!(a instanceof ot))throw new TypeError("root must be an FBXElem");if(a.id!=="")throw new Error("root FBXElem must have an empty id");Gm(a);let t=Vm(e),n=new Ni(64*1024);n.writeBytes(Um),n.writeU32(e),a._calcOffsetsChildren(n.tell(),!1,t),a._writeChildren(n,!1,t),n.writeBytes(km),n.writeZeros(4);let i=n.tell(),s=(i+15&-16)-i;return s===0&&(s=16),n.writeZeros(s),n.writeU32(e),n.writeZeros(120),n.writeBytes(zm),n.toUint8Array()}var Hm=0xcbf29ce484222325n,Wm=0x00000100000001b3n,vo=(1n<<63n)-1n,Jl=1000000000n;function Xm(a){let e=Hm,t=new TextEncoder().encode(a);for(let n=0;n<t.length;n++)e^=BigInt(t[n]),e=e*Wm&0xffffffffffffffffn;return e}var Fi=class{constructor(){ue(this,"_keyToUid");ue(this,"_uidToKey");this._keyToUid=new Map,this._uidToKey=new Map}get(e){let t=this._keyToUid.get(e);if(t!==void 0)return t;let n=Xm(e);if(n>vo&&(n&=vo),n>Jl){let i=n%Jl;this._uidToKey.has(i)||(n=i)}for(;this._uidToKey.has(n);)if(n=n>=1n<<62n?n-1n:n+1n,n<0n||n>vo)throw new Error(`Unable to allocate FBX UID for key "${e}"`);return this._keyToUid.set(e,n),this._uidToKey.set(n,e),n}keyOf(e){return this._uidToKey.get(e)}get size(){return this._keyToUid.size}},qm={scene:"Scene",object:"Object",mesh:"Mesh",geometry:"Geometry",material:"Material",texture:"Texture",video:"Video",light:"Light",camera:"Camera",bone:"Bone",armature:"Armature",skeleton:"Skeleton",animstack:"AnimStack",animlayer:"AnimLayer",animcurvenode:"AnimCurveNode",animcurve:"AnimCurve"};function re(a,e){return`B${qm[a]??a}#${e}`}function Zl(a){return`${re("mesh",a)}|Geometry`}function $l(a){return re("material",a)}function Ql(a){return re("texture",a)}function eu(a){return`${re("texture",a)}|Video`}function Yt(a){return re("object",a)}function Km(a,e){return`${re("armature",a)}|${re("bone",e)}`}function tu(a,e){return`${Km(a,e)}|Data`}function nu(a,e){return`${re("armature",a)}|${re("mesh",e)}|DeformerSkin`}function iu(a,e,t){return`${re("armature",a)}|${re("mesh",e)}|${re("bone",t)}|SubDeformerCluster`}function su(a,e){return`${re("object",a)}|${re("mesh",e)}|BindPose`}function ru(a){return`${re("animstack",a)}`}function So(a){return`${re("animstack",a)}|Layer`}function Mo(a,e,t){return`${So(a)}|${re("animcurvenode",e)}|${t}`}function au(a,e,t,n){return`${Mo(a,e,t)}|${n}`}var ou=a=>`__FBX_Document__${a}`,cu=a=>`${re("geometry",a)}|BlendShape`,lu=(a,e,t)=>`${re("geometry",a)}|BlendShapeChannel|${e}|${t}`,uu=(a,e,t)=>`${re("geometry",a)}|Shape|${e}|${t}`;function ct(a,e,t){let n=new ot(e);return t(n),a.addChild(n),n}var ye=(a,e)=>a.addEmpty(e);var fu=(a,e,t)=>ct(a,e,n=>n.addChar(t));var U=(a,e,t)=>ct(a,e,n=>n.addInt32(t)),qn=(a,e,t)=>ct(a,e,n=>n.addInt64(t));var jt=(a,e,t)=>ct(a,e,n=>n.addFloat64(t)),Ws=(a,e,t)=>ct(a,e,n=>n.addBytes(t)),V=(a,e,t)=>ct(a,e,n=>n.addString(t)),Ie=(a,e,t)=>ct(a,e,n=>n.addInt32Array(t)),du=(a,e,t)=>ct(a,e,n=>n.addInt64Array(t)),Eo=(a,e,t)=>ct(a,e,n=>n.addFloat32Array(t)),Pe=(a,e,t)=>ct(a,e,n=>n.addFloat64Array(t));function Z(a,e){return`${a}\0${e}`}var ee="addFloat64",Hs="addInt32",hu="addInt64",Ao="addString",pu={p_bool:["bool","",Hs],p_integer:["int","Integer",Hs],p_ulonglong:["ULongLong","",hu],p_double:["double","Number",ee],p_number:["Number","",ee],p_enum:["enum","",Hs],p_vector_3d:["Vector3D","Vector",ee,ee,ee],p_vector:["Vector","",ee,ee,ee],p_color_rgb:["ColorRGB","Color",ee,ee,ee],p_color:["Color","",ee,ee,ee],p_string:["KString","",Ao],p_string_url:["KString","Url",Ao],p_timestamp:["KTime","Time",hu],p_datetime:["DateTime","",Ao],p_object:["object",""],p_compound:["Compound",""],p_lcl_translation:["Lcl Translation","",ee,ee,ee],p_lcl_rotation:["Lcl Rotation","",ee,ee,ee],p_lcl_scaling:["Lcl Scaling","",ee,ee,ee],p_visibility:["Visibility","",ee],p_visibility_inheritance:["Visibility Inheritance","",Hs],p_roll:["Roll","",ee],p_opticalcenterx:["OpticalCenterX","",ee],p_opticalcentery:["OpticalCenterY","",ee],p_fov:["FieldOfView","",ee],p_fov_x:["FieldOfViewX","",ee],p_fov_y:["FieldOfViewY","",ee]};function To(a,e,t){return a?e?t?"A+U":"A+":t?"A+U":"A":t?"U":""}function wo(a,e,t,n,i){let s=new ot("P");s.addString(t),s.addString(e[0]),s.addString(e[1]),s.addString(i);let r=e.slice(2);if(r.length===1)e[0]==="object"||s[r[0]](n);else if(r.length>1)for(let o=0;o<r.length;o++)s[r[o]](n[o]);return a.addChild(s),s}function ie(a){return a.addEmpty("Properties70")}function J(a,e,t,n,{animatable:i=!1,animated:s=!1,custom:r=!1}={}){let o=pu[e];if(!o)throw new Error(`Unknown ptype: ${e}`);wo(a,o,t,n,To(i,s,r))}function fe(a,e){let t=a&&a.get?a.get(e):null;if(!t)return{};let n={};for(let[i,s]of Object.entries(t.properties))n[i]={...s,written:!1};return n}function P(a,e,t,n,i,{animatable:s=!1,animated:r=!1}={}){let o=pu[t];if(!o)throw new Error(`Unknown ptype: ${t}`);let c=a[n];c?(wo(e,o,n,i,To(c.animatable,r,!1)),c.written=!0):wo(e,o,n,i,To(s,r,!1))}var _=(a,e,t=!1)=>({value:a,ptype:e,animatable:t});function Ae(a,e){return e?{...a,...e}:a}function Te(a,e,t){return{typeName:a,propTypeName:e,properties:t,users:0,_written:!1}}function mu(a,e){return Te("GlobalSettings","",Ae({},e))}function Ro(a,e){let t={QuaternionInterpolate:_(0,"p_enum"),RotationOffset:_([0,0,0],"p_vector_3d"),RotationPivot:_([0,0,0],"p_vector_3d"),ScalingOffset:_([0,0,0],"p_vector_3d"),ScalingPivot:_([0,0,0],"p_vector_3d"),TranslationActive:_(!1,"p_bool"),TranslationMin:_([0,0,0],"p_vector_3d"),TranslationMax:_([0,0,0],"p_vector_3d"),TranslationMinX:_(!1,"p_bool"),TranslationMinY:_(!1,"p_bool"),TranslationMinZ:_(!1,"p_bool"),TranslationMaxX:_(!1,"p_bool"),TranslationMaxY:_(!1,"p_bool"),TranslationMaxZ:_(!1,"p_bool"),RotationOrder:_(0,"p_enum"),RotationSpaceForLimitOnly:_(!1,"p_bool"),RotationStiffnessX:_(0,"p_double"),RotationStiffnessY:_(0,"p_double"),RotationStiffnessZ:_(0,"p_double"),AxisLen:_(10,"p_double"),PreRotation:_([0,0,0],"p_vector_3d"),PostRotation:_([0,0,0],"p_vector_3d"),RotationActive:_(!1,"p_bool"),RotationMin:_([0,0,0],"p_vector_3d"),RotationMax:_([0,0,0],"p_vector_3d"),RotationMinX:_(!1,"p_bool"),RotationMinY:_(!1,"p_bool"),RotationMinZ:_(!1,"p_bool"),RotationMaxX:_(!1,"p_bool"),RotationMaxY:_(!1,"p_bool"),RotationMaxZ:_(!1,"p_bool"),InheritType:_(0,"p_enum"),ScalingActive:_(!1,"p_bool"),ScalingMin:_([0,0,0],"p_vector_3d"),ScalingMax:_([1,1,1],"p_vector_3d"),ScalingMinX:_(!1,"p_bool"),ScalingMinY:_(!1,"p_bool"),ScalingMinZ:_(!1,"p_bool"),ScalingMaxX:_(!1,"p_bool"),ScalingMaxY:_(!1,"p_bool"),ScalingMaxZ:_(!1,"p_bool"),GeometricTranslation:_([0,0,0],"p_vector_3d"),GeometricRotation:_([0,0,0],"p_vector_3d"),GeometricScaling:_([1,1,1],"p_vector_3d"),MinDampRangeX:_(0,"p_double"),MinDampRangeY:_(0,"p_double"),MinDampRangeZ:_(0,"p_double"),MaxDampRangeX:_(0,"p_double"),MaxDampRangeY:_(0,"p_double"),MaxDampRangeZ:_(0,"p_double"),MinDampStrengthX:_(0,"p_double"),MinDampStrengthY:_(0,"p_double"),MinDampStrengthZ:_(0,"p_double"),MaxDampStrengthX:_(0,"p_double"),MaxDampStrengthY:_(0,"p_double"),MaxDampStrengthZ:_(0,"p_double"),PreferedAngleX:_(0,"p_double"),PreferedAngleY:_(0,"p_double"),PreferedAngleZ:_(0,"p_double"),LookAtProperty:_(null,"p_object"),UpVectorProperty:_(null,"p_object"),Show:_(!0,"p_bool"),NegativePercentShapeSupport:_(!0,"p_bool"),DefaultAttributeIndex:_(-1,"p_integer"),Freeze:_(!1,"p_bool"),LODBox:_(!1,"p_bool"),"Lcl Translation":_([0,0,0],"p_lcl_translation",!0),"Lcl Rotation":_([0,0,0],"p_lcl_rotation",!0),"Lcl Scaling":_([1,1,1],"p_lcl_scaling",!0),Visibility:_(1,"p_visibility",!0),"Visibility Inheritance":_(1,"p_visibility_inheritance")};return Te("Model","FbxNode",Ae(t,e))}function Co(a,e){let t={Color:_([.8,.8,.8],"p_color_rgb"),Size:_(100,"p_double"),Look:_(1,"p_enum")};return Te("NodeAttribute","FbxNull",Ae(t,e))}function gu(a,e){let t=a?.globalScale??1,n={LightType:_(0,"p_enum"),CastLight:_(!0,"p_bool"),Color:_([1,1,1],"p_color",!0),Intensity:_(100,"p_number",!0),Exposure:_(0,"p_number",!0),DecayType:_(2,"p_enum"),DecayStart:_(30*t,"p_double"),CastShadows:_(!0,"p_bool"),ShadowColor:_([0,0,0],"p_color",!0),AreaLightShape:_(0,"p_enum")};return Te("NodeAttribute","FbxLight",Ae(n,e))}function xu(a,e){let t={Color:_([.8,.8,.8],"p_color_rgb"),Position:_([0,0,-50],"p_vector",!0),UpVector:_([0,1,0],"p_vector",!0),InterestPosition:_([0,0,0],"p_vector",!0),Roll:_(0,"p_roll",!0),OpticalCenterX:_(0,"p_opticalcenterx",!0),OpticalCenterY:_(0,"p_opticalcentery",!0),BackgroundColor:_([.63,.63,.63],"p_color",!0),TurnTable:_(0,"p_number",!0),DisplayTurnTableIcon:_(!1,"p_bool"),UseMotionBlur:_(!1,"p_bool"),UseRealTimeMotionBlur:_(!0,"p_bool"),"Motion Blur Intensity":_(1,"p_number",!0),AspectRatioMode:_(0,"p_enum"),AspectWidth:_(320,"p_double"),AspectHeight:_(200,"p_double"),PixelAspectRatio:_(1,"p_double"),FilmOffsetX:_(0,"p_number",!0),FilmOffsetY:_(0,"p_number",!0),FilmWidth:_(.816,"p_double"),FilmHeight:_(.612,"p_double"),FilmAspectRatio:_(1.3333333333333333,"p_double"),FilmSqueezeRatio:_(1,"p_double"),FilmFormatIndex:_(0,"p_enum"),PreScale:_(1,"p_number",!0),FilmTranslateX:_(0,"p_number",!0),FilmTranslateY:_(0,"p_number",!0),FilmRollPivotX:_(0,"p_number",!0),FilmRollPivotY:_(0,"p_number",!0),FilmRollValue:_(0,"p_number",!0),FilmRollOrder:_(0,"p_enum"),ApertureMode:_(2,"p_enum"),GateFit:_(0,"p_enum"),FieldOfView:_(25.114999771118164,"p_fov",!0),FieldOfViewX:_(40,"p_fov_x",!0),FieldOfViewY:_(40,"p_fov_y",!0),FocalLength:_(34.89327621672628,"p_number",!0),CameraFormat:_(0,"p_enum"),UseFrameColor:_(!1,"p_bool"),FrameColor:_([.3,.3,.3],"p_color_rgb"),ShowName:_(!0,"p_bool"),ShowInfoOnMoving:_(!0,"p_bool"),ShowGrid:_(!0,"p_bool"),ShowOpticalCenter:_(!1,"p_bool"),ShowAzimut:_(!0,"p_bool"),ShowTimeCode:_(!1,"p_bool"),ShowAudio:_(!1,"p_bool"),AudioColor:_([0,1,0],"p_vector_3d"),NearPlane:_(10,"p_double"),FarPlane:_(4e3,"p_double"),AutoComputeClipPanes:_(!1,"p_bool"),ViewCameraToLookAt:_(!0,"p_bool"),ViewFrustumNearFarPlane:_(!1,"p_bool"),ViewFrustumBackPlaneMode:_(2,"p_enum"),BackPlaneDistance:_(4e3,"p_number",!0),BackPlaneDistanceMode:_(1,"p_enum"),ViewFrustumFrontPlaneMode:_(2,"p_enum"),FrontPlaneDistance:_(10,"p_number",!0),FrontPlaneDistanceMode:_(1,"p_enum"),LockMode:_(!1,"p_bool"),LockInterestNavigation:_(!1,"p_bool"),FitImage:_(!1,"p_bool"),Crop:_(!1,"p_bool"),Center:_(!0,"p_bool"),KeepRatio:_(!0,"p_bool"),BackgroundAlphaTreshold:_(.5,"p_double"),ShowBackplate:_(!0,"p_bool"),BackPlaneOffsetX:_(0,"p_number",!0),BackPlaneOffsetY:_(0,"p_number",!0),BackPlaneRotation:_(0,"p_number",!0),BackPlaneScaleX:_(1,"p_number",!0),BackPlaneScaleY:_(1,"p_number",!0),"Background Texture":_(null,"p_object"),FrontPlateFitImage:_(!0,"p_bool"),FrontPlateCrop:_(!1,"p_bool"),FrontPlateCenter:_(!0,"p_bool"),FrontPlateKeepRatio:_(!0,"p_bool"),"Foreground Opacity":_(1,"p_double"),ShowFrontplate:_(!0,"p_bool"),FrontPlaneOffsetX:_(0,"p_number",!0),FrontPlaneOffsetY:_(0,"p_number",!0),FrontPlaneRotation:_(0,"p_number",!0),FrontPlaneScaleX:_(1,"p_number",!0),FrontPlaneScaleY:_(1,"p_number",!0),"Foreground Texture":_(null,"p_object"),DisplaySafeArea:_(!1,"p_bool"),DisplaySafeAreaOnRender:_(!1,"p_bool"),SafeAreaDisplayStyle:_(1,"p_enum"),SafeAreaAspectRatio:_(1.3333333333333333,"p_double"),Use2DMagnifierZoom:_(!1,"p_bool"),"2D Magnifier Zoom":_(100,"p_number",!0),"2D Magnifier X":_(50,"p_number",!0),"2D Magnifier Y":_(50,"p_number",!0),CameraProjectionType:_(0,"p_enum"),OrthoZoom:_(1,"p_double"),UseRealTimeDOFAndAA:_(!1,"p_bool"),UseDepthOfField:_(!1,"p_bool"),FocusSource:_(0,"p_enum"),FocusAngle:_(3.5,"p_double"),FocusDistance:_(200,"p_double"),UseAntialiasing:_(!1,"p_bool"),AntialiasingIntensity:_(.77777,"p_double"),AntialiasingMethod:_(0,"p_enum"),UseAccumulationBuffer:_(!1,"p_bool"),FrameSamplingCount:_(7,"p_integer"),FrameSamplingType:_(1,"p_enum")};return Te("NodeAttribute","FbxCamera",Ae(t,e))}function bu(a,e){return Te("NodeAttribute","LimbNode",Ae({},e))}function Xs(a,e){let t={Color:_([.8,.8,.8],"p_color_rgb"),BBoxMin:_([0,0,0],"p_vector_3d"),BBoxMax:_([0,0,0],"p_vector_3d"),"Primary Visibility":_(!0,"p_bool"),"Casts Shadows":_(!0,"p_bool"),"Receive Shadows":_(!0,"p_bool")};return Te("Geometry","FbxMesh",Ae(t,e))}function _u(a,e){let t={ShadingModel:_("Phong","p_string"),MultiLayer:_(!1,"p_bool"),EmissiveColor:_([0,0,0],"p_color",!0),EmissiveFactor:_(1,"p_number",!0),AmbientColor:_([.2,.2,.2],"p_color",!0),AmbientFactor:_(1,"p_number",!0),DiffuseColor:_([.8,.8,.8],"p_color",!0),DiffuseFactor:_(1,"p_number",!0),TransparentColor:_([0,0,0],"p_color",!0),TransparencyFactor:_(0,"p_number",!0),Opacity:_(1,"p_number",!0),NormalMap:_([0,0,0],"p_vector_3d"),Bump:_([0,0,0],"p_vector_3d"),BumpFactor:_(1,"p_double"),DisplacementColor:_([0,0,0],"p_color_rgb"),DisplacementFactor:_(1,"p_double"),VectorDisplacementColor:_([0,0,0],"p_color_rgb"),VectorDisplacementFactor:_(1,"p_double"),SpecularColor:_([.2,.2,.2],"p_color",!0),SpecularFactor:_(1,"p_number",!0),Shininess:_(20,"p_number",!0),ShininessExponent:_(20,"p_number",!0),ReflectionColor:_([0,0,0],"p_color",!0),ReflectionFactor:_(1,"p_number",!0)};return Te("Material","FbxSurfacePhong",Ae(t,e))}function yu(a,e){let t={TextureTypeUse:_(0,"p_enum"),AlphaSource:_(2,"p_enum"),"Texture alpha":_(1,"p_double"),PremultiplyAlpha:_(!0,"p_bool"),CurrentTextureBlendMode:_(1,"p_enum"),CurrentMappingType:_(0,"p_enum"),UVSet:_("default","p_string"),WrapModeU:_(0,"p_enum"),WrapModeV:_(0,"p_enum"),UVSwap:_(!1,"p_bool"),Translation:_([0,0,0],"p_vector_3d"),Rotation:_([0,0,0],"p_vector_3d"),Scaling:_([1,1,1],"p_vector_3d"),TextureRotationPivot:_([0,0,0],"p_vector_3d"),TextureScalingPivot:_([0,0,0],"p_vector_3d"),UseMaterial:_(!1,"p_bool"),UseMipMap:_(!1,"p_bool")};return Te("Texture","FbxFileTexture",Ae(t,e))}function vu(a,e){let t={Width:_(0,"p_integer"),Height:_(0,"p_integer"),Path:_("","p_string_url"),AccessMode:_(0,"p_enum"),StartFrame:_(0,"p_integer"),StopFrame:_(0,"p_integer"),Offset:_(0,"p_timestamp"),PlaySpeed:_(0,"p_double"),FreeRunning:_(!1,"p_bool"),Loop:_(!1,"p_bool"),InterlaceMode:_(0,"p_enum"),ImageSequence:_(!1,"p_bool"),ImageSequenceOffset:_(0,"p_integer"),FrameRate:_(0,"p_double"),LastFrame:_(0,"p_integer")};return Te("Video","FbxVideo",Ae(t,e))}function Su(a,e){return Te("Pose","",Ae({},e))}function Kn(a,e){return Te("Deformer","",Ae({},e))}function Mu(a,e){let t={Description:_("","p_string"),LocalStart:_(0,"p_timestamp"),LocalStop:_(0,"p_timestamp"),ReferenceStart:_(0,"p_timestamp"),ReferenceStop:_(0,"p_timestamp")};return Te("AnimationStack","FbxAnimStack",Ae(t,e))}function Au(a,e){let t={Weight:_(100,"p_number",!0),Mute:_(!1,"p_bool"),Solo:_(!1,"p_bool"),Lock:_(!1,"p_bool"),Color:_([.8,.8,.8],"p_color_rgb"),BlendMode:_(0,"p_enum"),RotationAccumulationMode:_(0,"p_enum"),ScaleAccumulationMode:_(0,"p_enum"),BlendModeBypass:_(0,"p_ulonglong")};return Te("AnimationLayer","FbxAnimLayer",Ae(t,e))}function Tu(a,e){let t={d:_(null,"p_compound")};return Te("AnimationCurveNode","FbxAnimCurveNode",Ae(t,e))}function wu(a,e){return Te("AnimationCurve","",Ae({},e))}var Ui=class{constructor(){ue(this,"_byType");ue(this,"_byKey");this._byType=new Map,this._byKey=new Map}register(e){let t=`${e.typeName}|${e.propTypeName}`,n=this._byKey.get(t);if(n)return n;this._byKey.set(t,e);let i=this._byType.get(e.typeName)??[];return i.push(e),this._byType.set(e.typeName,i),e}resolved(){let e=new Map;for(let[t,n]of this._byType){let i=0,s=n[0],r=-1,o=-1;for(let c of n){i+=c.users;let l=Object.keys(c.properties).length;(c.users>r||c.users===r&&l>o)&&(r=c.users,o=l,s=c)}e.set(t,{totalUsers:i,dominant:s})}return e}get(e){let t=this._byType.get(e);if(!t||t.length===0)return null;let n=t[0],i=-1,s=-1;for(let r of t){let o=Object.keys(r.properties).length;(r.users>i||r.users===i&&o>s)&&(i=r.users,s=o,n=r)}return n}totalUsers(){let e=0;for(let t of this._byKey.values())e+=t.users;return e}};var Zm=46186158000n;var qs=Zm,Io={"X|-Y":{up:[0,1],front:[1,1],coord:[2,1]},"X|Y":{up:[0,1],front:[1,-1],coord:[2,-1]},"X|-Z":{up:[0,1],front:[2,1],coord:[1,-1]},"X|Z":{up:[0,1],front:[2,-1],coord:[1,1]},"-X|-Y":{up:[0,-1],front:[1,1],coord:[2,-1]},"-X|Y":{up:[0,-1],front:[1,-1],coord:[2,1]},"-X|-Z":{up:[0,-1],front:[2,1],coord:[1,1]},"-X|Z":{up:[0,-1],front:[2,-1],coord:[1,-1]},"Y|-X":{up:[1,1],front:[0,1],coord:[2,-1]},"Y|X":{up:[1,1],front:[0,-1],coord:[2,1]},"Y|-Z":{up:[1,1],front:[2,1],coord:[0,1]},"Y|Z":{up:[1,1],front:[2,-1],coord:[0,-1]},"-Y|-X":{up:[1,-1],front:[0,1],coord:[2,1]},"-Y|X":{up:[1,-1],front:[0,-1],coord:[2,-1]},"-Y|-Z":{up:[1,-1],front:[2,1],coord:[0,-1]},"-Y|Z":{up:[1,-1],front:[2,-1],coord:[0,1]},"Z|-X":{up:[2,1],front:[0,1],coord:[1,1]},"Z|X":{up:[2,1],front:[0,-1],coord:[1,-1]},"Z|-Y":{up:[2,1],front:[1,1],coord:[0,-1]},"Z|Y":{up:[2,1],front:[1,-1],coord:[0,1]},"-Z|-X":{up:[2,-1],front:[0,1],coord:[1,-1]},"-Z|X":{up:[2,-1],front:[0,-1],coord:[1,1]},"-Z|-Y":{up:[2,-1],front:[1,1],coord:[0,1]},"-Z|Y":{up:[2,-1],front:[1,-1],coord:[0,-1]}},Eu=[{fps:-1,mode:14},{fps:120,mode:1},{fps:100,mode:2},{fps:60,mode:3},{fps:50,mode:4},{fps:48,mode:5},{fps:30,mode:6},{fps:30/1.001,mode:9},{fps:25,mode:10},{fps:24,mode:11},{fps:24/1.001,mode:13},{fps:96,mode:15},{fps:72,mode:16},{fps:60/1.001,mode:17}],Ru="Comfy Org",Po="@comfyorg/fbx-exporter-three",Lo="1.0.0";function Iu(a){return a&&typeof a.creator=="string"&&a.creator?a.creator:`${Po} - ${Lo}`}function eg(a){for(let e of Eu)if(e.fps>0&&Math.abs(e.fps-a)<1e-4)return e.mode;return 14}function No({root:a,settings:e,sceneName:t="Scene"}){let n=ye(a,"FBXHeaderExtension");U(n,"FBXHeaderVersion",1003),U(n,"FBXVersion",e.version??7400),U(n,"EncryptionType",0);let i=ye(n,"CreationTimeStamp");U(i,"Version",1e3),U(i,"Year",1970),U(i,"Month",1),U(i,"Day",1),U(i,"Hour",0),U(i,"Minute",0),U(i,"Second",0),U(i,"Millisecond",0),V(n,"Creator",Iu(e));let s=V(n,"SceneInfo",Z("GlobalInfo","SceneInfo"));s.addString("UserData"),V(s,"Type","UserData"),U(s,"Version",100);let r=ye(s,"MetaData");U(r,"Version",100);for(let c of["Title","Subject","Author","Keywords","Revision","Comment"])V(r,c,"");let o=ie(s);J(o,"p_string_url","DocumentUrl","/foobar.fbx"),J(o,"p_string_url","SrcDocumentUrl","/foobar.fbx");for(let c of["Original","LastSaved"])J(o,"p_compound",c),J(o,"p_string",`${c}|ApplicationVendor`,Ru),J(o,"p_string",`${c}|ApplicationName`,Po),J(o,"p_string",`${c}|ApplicationVersion`,Lo),J(o,"p_datetime",`${c}|DateTime_GMT`,"01/01/1970 00:00:00.000");Ws(a,"FileId",new Uint8Array(16)),V(a,"CreationTime","1970-01-01 10:00:00:000"),V(a,"Creator",Iu(e)),tg(a,e),ng(a,t),ye(a,"References")}function tg(a,e){let t=ye(a,"GlobalSettings");U(t,"Version",1e3);let n=`${e.axisUp??"Y"}|${e.axisForward??"Z"}`,i=Io[n]??Io["Y|Z"],s=e.unitScale??1,r=e.fps??24,o=ie(t);J(o,"p_integer","UpAxis",i.up[0]),J(o,"p_integer","UpAxisSign",i.up[1]),J(o,"p_integer","FrontAxis",i.front[0]),J(o,"p_integer","FrontAxisSign",i.front[1]),J(o,"p_integer","CoordAxis",i.coord[0]),J(o,"p_integer","CoordAxisSign",i.coord[1]),J(o,"p_integer","OriginalUpAxis",-1),J(o,"p_integer","OriginalUpAxisSign",1),J(o,"p_double","UnitScaleFactor",s),J(o,"p_double","OriginalUnitScaleFactor",s),J(o,"p_color_rgb","AmbientColor",[0,0,0]),J(o,"p_string","DefaultCamera","Producer Perspective"),J(o,"p_enum","TimeMode",eg(r)),J(o,"p_timestamp","TimeSpanStart",0n),J(o,"p_timestamp","TimeSpanStop",qs),J(o,"p_double","CustomFrameRate",r)}function ng(a,e){let t=ye(a,"Documents");U(t,"Count",1);let n=ig(ou(e)),i=qn(t,"Document",n);i.addString(e),i.addString(e);let s=ie(i);J(s,"p_object","SourceObject"),J(s,"p_string","ActiveAnimStackName",""),qn(i,"RootNode",0n)}function ig(a){let e=0xcbf29ce484222325n,t=0x00000100000001b3n;for(let n=0;n<a.length;n++)e^=BigInt(a.charCodeAt(n)),e=e*t&0xffffffffffffffffn;return e&(1n<<63n)-1n}function Fo({root:a,templates:e}){let t=ye(a,"Definitions");U(t,"Version",100),U(t,"Count",e.totalUsers());for(let[n,{totalUsers:i,dominant:s}]of e.resolved()){let r=V(t,"ObjectType",n);if(U(r,"Count",i),s._written=!0,!s.propTypeName||Object.keys(s.properties).length===0)continue;let o=V(r,"PropertyTemplate",s.propTypeName),c=ie(o);for(let[l,u]of Object.entries(s.properties))try{J(c,u.ptype,l,u.value,{animatable:u.animatable})}catch(h){console.warn(`Failed to write template prop ${n}.${l}: ${h.message}`)}}}function Uo({root:a,connections:e}){let t=ye(a,"Connections");if(e.length===0){let n=t.addEmpty("C");n.addString("OO"),n.addInt64(0n),n.addInt64(0n);return}for(let[n,i,s,r]of e){let o=t.addEmpty("C");o.addString(n),o.addInt64(i),o.addInt64(s),r!=null&&o.addString(r)}}var Lu={threejs:{axisUp:"Y",axisForward:"Z",unitScale:1,bakeSpaceTransform:!1},unity:{axisUp:"Y",axisForward:"Z",unitScale:1,bakeSpaceTransform:!1},unreal:{axisUp:"Z",axisForward:"X",unitScale:1,bakeSpaceTransform:!1},blender:{axisUp:"Y",axisForward:"Z",unitScale:100,bakeSpaceTransform:!1},maya:{axisUp:"Y",axisForward:"Z",unitScale:100,bakeSpaceTransform:!1}};function Oo(a){a=a||{};let e=a.preset||"threejs",t=Lu[e];if(!t)return console.warn(`fbx-exporter-three: unknown preset "${e}" \u2014 using as-is`),{...a};let n={...t};for(let i of Object.keys(a))a[i]!==void 0&&(n[i]=a[i]);return n}var Pu={X:[1,0,0],"-X":[-1,0,0],Y:[0,1,0],"-Y":[0,-1,0],Z:[0,0,1],"-Z":[0,0,-1]};function Du(a,e){let t=Pu[a],n=Pu[e];if(!t||!n)throw new Error(`buildAxisMatrix: invalid axes axisUp=${a} axisForward=${e}`);let i=[t[1]*n[2]-t[2]*n[1],t[2]*n[0]-t[0]*n[2],t[0]*n[1]-t[1]*n[0]],s=new z;return s.set(i[0],t[0],n[0],0,i[1],t[1],n[1],0,i[2],t[2],n[2],0,0,0,0,1),s}function Bo(a){let e=a.axisUp??"Y",t=a.axisForward??"Z",n=a.unitScale??1,i=a.bakeSpaceTransform===!0,s=Du(e,t);if(i&&n!==1){let c=new z().makeScale(n,n,n);s.premultiply(c)}let r=new z().copy(s).invert(),o=rg(r);return o.elements[12]=o.elements[13]=o.elements[14]=0,{axisUp:e,axisForward:t,unitScale:n,bake:i,globalMatrix:s,globalMatrixInvTransposed:o,isIdentity:i?ag(s):!0}}function rg(a){let e=a.elements,t=new z;return t.set(e[0],e[1],e[2],e[3],e[4],e[5],e[6],e[7],e[8],e[9],e[10],e[11],e[12],e[13],e[14],e[15]),t}function ag(a){let e=a.elements;for(let t=0;t<16;t++){let n=t===0||t===5||t===10||t===15?1:0;if(Math.abs(e[t]-n)>1e-9)return!1}return!0}function ko(a,e){let t=e.elements;for(let n=0;n<a.length;n+=3){let i=a[n],s=a[n+1],r=a[n+2];a[n]=t[0]*i+t[4]*s+t[8]*r+t[12],a[n+1]=t[1]*i+t[5]*s+t[9]*r+t[13],a[n+2]=t[2]*i+t[6]*s+t[10]*r+t[14]}}function zo(a,e){let t=e.elements;for(let n=0;n<a.length;n+=3){let i=a[n],s=a[n+1],r=a[n+2],o=t[0]*i+t[4]*s+t[8]*r,c=t[1]*i+t[5]*s+t[9]*r,l=t[2]*i+t[6]*s+t[10]*r,u=Math.hypot(o,c,l);u>1e-12&&(o/=u,c/=u,l/=u),a[n]=o,a[n+1]=c,a[n+2]=l}}function Fu(a,e=a.itemSize){if(!(a.isInterleavedBufferAttribute||a.normalized===!0))return a.array;let n=a.count,i=new Float32Array(n*e);for(let s=0;s<n;s++){let r=s*e;e>=1&&(i[r]=a.getX(s)),e>=2&&(i[r+1]=a.getY(s)),e>=3&&(i[r+2]=a.getZ(s)),e>=4&&(i[r+3]=a.getW(s))}return i}function hg(a){if(a.index)return Int32Array.from(a.index.array);let e=a.attributes.position.count,t=new Int32Array(e);for(let n=0;n<e;n++)t[n]=n;return t}function fg(a){let e=a/3;if(!Number.isInteger(e))throw new Error(`Loop count ${a} is not a multiple of 3 \u2014 non-triangular geometry not supported`);let t=new Int32Array(e);for(let n=0;n<e;n++)t[n]=n*3;return t}function dg(a,e){for(let t=1;t<e.length;t++)a[e[t]-1]^=-1;a[a.length-1]^=-1}function Vo(a,e,t){let n=a.index?a.index.count:a.attributes.position.count,i=Fu(e,t);if(!a.index)return i;let s=new Float32Array(n*t),r=a.index.array;for(let o=0;o<n;o++){let l=r[o]*t,u=o*t;for(let h=0;h<t;h++)s[u+h]=i[l+h]}return s}function Go(a){let{parent:e,geometry:t,uid:n,name:i,templates:s,materialSlotCount:r=0,groups:o=[],slotRemap:c,transformCtx:l,flipUV:u=!1}=a,h=l&&l.bake&&!l.isIdentity,f=e.addEmpty("Geometry");f.addInt64(n),f.addString(Z(i||"Geometry","Geometry")),f.addString("Mesh");let d=fe(s,"Geometry"),p=ie(f);U(f,"GeometryVersion",124);let m=t.attributes.position;if(!m)throw new Error(`Geometry "${i}" has no position attribute`);let b=Fu(m,3),x=new Float64Array(b.length);for(let R=0;R<b.length;R++)x[R]=b[R];h&&ko(x,l.globalMatrix),Pe(f,"Vertices",x);let v=hg(t),S=fg(v.length),y=new Int32Array(v);dg(y,S),Ie(f,"PolygonVertexIndex",y),Ie(f,"Edges",new Int32Array(0));let T=!1;t.attributes.normal&&(pg(f,t,h?l:null),T=!0);let M=!1;t.attributes.color&&(gg(f,t),M=!0);let A=[];for(let R of["uv","uv1","uv2","uv3"])t.attributes[R]&&A.push(R);A.forEach((R,C)=>mg(f,t,R,C,u));let g=!1;r>0&&(xg(f,t,r,o,c),g=!0);let w=U(f,"Layer",0);U(w,"Version",100),T&&Oi(w,"LayerElementNormal",0),M&&Oi(w,"LayerElementColor",0),A.length&&Oi(w,"LayerElementUV",0),g&&Oi(w,"LayerElementMaterial",0);for(let R=1;R<A.length;R++){let C=U(f,"Layer",R);U(C,"Version",100),Oi(C,"LayerElementUV",R)}}function Oi(a,e,t){let n=ye(a,"LayerElement");V(n,"Type",e),U(n,"TypedIndex",t)}function pg(a,e,t){let n=U(a,"LayerElementNormal",0);U(n,"Version",101),V(n,"Name",""),V(n,"MappingInformationType","ByPolygonVertex"),V(n,"ReferenceInformationType","IndexToDirect");let i=Vo(e,e.attributes.normal,3),s=new Float64Array(i.length);for(let c=0;c<i.length;c++)s[c]=i[c];t&&zo(s,t.globalMatrixInvTransposed),Pe(n,"Normals",s);let r=s.length/3,o=new Int32Array(r);for(let c=0;c<r;c++)o[c]=c;Ie(n,"NormalsIndex",o)}function mg(a,e,t,n,i){let s=U(a,"LayerElementUV",n);U(s,"Version",101),V(s,"Name",t==="uv"?"UVMap":t),V(s,"MappingInformationType","ByPolygonVertex"),V(s,"ReferenceInformationType","IndexToDirect");let r=Vo(e,e.attributes[t],2),o=new Float64Array(r.length);for(let u=0;u<r.length;u++)o[u]=i&&u%2===1?1-r[u]:r[u];Pe(s,"UV",o);let c=o.length/2,l=new Int32Array(c);for(let u=0;u<c;u++)l[u]=u;Ie(s,"UVIndex",l)}function gg(a,e){let t=U(a,"LayerElementColor",0);U(t,"Version",101),V(t,"Name","Col"),V(t,"MappingInformationType","ByPolygonVertex"),V(t,"ReferenceInformationType","IndexToDirect");let n=e.attributes.color,i=n.itemSize,s=Vo(e,n,i),r=s.length/i,o=new Float64Array(r*4);for(let l=0;l<r;l++){let u=l*i,h=l*4;o[h]=s[u],o[h+1]=s[u+1],o[h+2]=s[u+2],o[h+3]=i>=4?s[u+3]:1}Pe(t,"Colors",o);let c=new Int32Array(r);for(let l=0;l<r;l++)c[l]=l;Ie(t,"ColorIndex",c)}function xg(a,e,t,n,i){let s=U(a,"LayerElementMaterial",0);if(U(s,"Version",101),V(s,"Name",""),t<=1||n.length===0){V(s,"MappingInformationType","AllSame"),V(s,"ReferenceInformationType","IndexToDirect"),Ie(s,"Materials",new Int32Array([0]));return}let o=(e.index?e.index.count:e.attributes.position.count)/3,c=new Int32Array(o),l=i||bg(t),u=h=>{if(h<0||h>=l.length)return 0;let f=l[h];return f>=0&&f<t?f:0};for(let h of n){let f=Math.floor(h.start/3),d=Math.floor(h.count/3),p=u(h.materialIndex);for(let m=0;m<d;m++)c[f+m]=p}V(s,"MappingInformationType","ByPolygon"),V(s,"ReferenceInformationType","IndexToDirect"),Ie(s,"Materials",c)}function bg(a){let e=new Array(a);for(let t=0;t<a;t++)e[t]=t;return e}var Ho=180/Math.PI;function yg(a,e){if(!(!e||typeof e!="object"))for(let t of Object.keys(e)){let n=e[t];if(n!=null)if(typeof n=="boolean")J(a,"p_bool",t,n?1:0,{custom:!0});else if(typeof n=="number"&&Number.isFinite(n)){let i=Number.isInteger(n)?"p_integer":"p_double";J(a,i,t,n,{custom:!0})}else if(typeof n=="string")J(a,"p_string",t,n,{custom:!0});else if(Array.isArray(n)&&n.length===3&&n.every(i=>typeof i=="number"&&Number.isFinite(i)))J(a,"p_vector_3d",t,n,{custom:!0});else try{J(a,"p_string",t,JSON.stringify(n),{custom:!0})}catch{}}}var Ks=new ke,Uu=new E,Ou=new pe,Bu=new E;function vg(a){return a.matrix.decompose(Uu,Ou,Bu),{pos:Uu,quat:Ou,scale:Bu}}function Sg(a){return Ks.setFromQuaternion(a,"ZYX"),[Ks.x*Ho,Ks.y*Ho,Ks.z*Ho]}function Mg(a){return a.isMesh?"Mesh":a.isBone?"LimbNode":a.isLight&&!a.isAmbientLight?"Light":a.isCamera?"Camera":"Null"}function ki({parent:a,object:e,uid:t,templates:n,overrideTranslation:i,overrideMatrix:s,hasLookAtTarget:r,customProperties:o}){let c=Mg(e),l=a.addEmpty("Model");l.addInt64(t),l.addString(Z(e.name||c,"Model")),l.addString(c),U(l,"Version",232);let u=fe(n,"Model"),h=ie(l),f,d,p;if(s){let x=new E,v=new pe,S=new E;s.decompose(x,v,S),f=x,d=v,p=S}else({pos:f,quat:d,scale:p}=vg(e));let m=Sg(d),b=i||[f.x,f.y,f.z];P(u,h,"p_lcl_translation","Lcl Translation",b,{animatable:!0}),P(u,h,"p_lcl_rotation","Lcl Rotation",m,{animatable:!0}),P(u,h,"p_lcl_scaling","Lcl Scaling",[p.x,p.y,p.z],{animatable:!0}),P(u,h,"p_visibility","Visibility",e.visible?1:0),P(u,h,"p_integer","DefaultAttributeIndex",0),P(u,h,"p_enum","InheritType",1),r&&P(u,h,"p_object","LookAtProperty",null),o&&yg(h,e.userData),U(l,"MultiLayer",0),U(l,"MultiTake",0),fu(l,"Shading",1),V(l,"Culling","CullingOff")}function Ys({parent:a,name:e,uid:t,templates:n}){let i=a.addEmpty("NodeAttribute");i.addInt64(t),i.addString(Z(e||"Null","NodeAttribute")),i.addString("Null"),V(i,"TypeFlags","Null");let s=fe(n,"NodeAttribute"),r=ie(i);}function Tg(a){let e={baseColor:[.8,.8,.8],emissiveColor:[0,0,0],emissiveStrength:1,metallic:0,roughness:.5,specular:.5,alpha:1,normalmapStrength:1};if(a.color&&(e.baseColor=[a.color.r,a.color.g,a.color.b]),a.emissive&&(e.emissiveColor=[a.emissive.r,a.emissive.g,a.emissive.b]),"emissiveIntensity"in a&&(e.emissiveStrength=a.emissiveIntensity),"metalness"in a&&(e.metallic=a.metalness),"roughness"in a&&(e.roughness=a.roughness),"opacity"in a&&(e.alpha=a.opacity),"normalScale"in a&&a.normalScale&&(e.normalmapStrength=a.normalScale.x),a.isMeshPhongMaterial){let t=typeof a.shininess=="number"?a.shininess:30;e.roughness=Math.max(0,1-Math.sqrt(Math.max(0,t))/10),a.specular&&typeof a.specular.r=="number"&&(e.specular=a.specular.r)}return e}function Wo({parent:a,material:e,uid:t,templates:n}){let i=Tg(e),s=a.addEmpty("Material");s.addInt64(t),s.addString(Z(e.name||"Material","Material")),s.addString(""),U(s,"Version",102),V(s,"ShadingModel","Phong"),U(s,"MultiLayer",0);let r=fe(n,"Material"),o=ie(s);P(r,o,"p_string","ShadingModel","Phong"),P(r,o,"p_color","DiffuseColor",i.baseColor),P(r,o,"p_number","DiffuseFactor",1),P(r,o,"p_color","EmissiveColor",i.emissiveColor),P(r,o,"p_number","EmissiveFactor",i.emissiveStrength),P(r,o,"p_color","AmbientColor",[0,0,0]),P(r,o,"p_number","AmbientFactor",0);let c=1e-5;if(i.alpha<c||i.alpha>1-c){let h=1-i.alpha;P(r,o,"p_color","TransparentColor",[h,h,h])}else P(r,o,"p_color","TransparentColor",i.baseColor);P(r,o,"p_number","TransparencyFactor",1-i.alpha),P(r,o,"p_number","Opacity",i.alpha),P(r,o,"p_vector_3d","NormalMap",[0,0,0]),P(r,o,"p_double","BumpFactor",i.normalmapStrength),P(r,o,"p_color","SpecularColor",i.baseColor),P(r,o,"p_number","SpecularFactor",i.specular/2);let l=(1-i.roughness)*10,u=l*l;P(r,o,"p_number","Shininess",u),P(r,o,"p_number","ShininessExponent",u),P(r,o,"p_color","ReflectionColor",i.baseColor),P(r,o,"p_number","ReflectionFactor",i.metallic)}var wg=33;function Xo({parent:a,bone:e,attrUid:t,templates:n}){let i=a.addEmpty("NodeAttribute");i.addInt64(t),i.addString(Z(e.name||"Bone","NodeAttribute")),i.addString("LimbNode"),V(i,"TypeFlags","Skeleton");let s=fe(n,"NodeAttribute"),r=ie(i);P(s,r,"p_double","Size",wg)}function js(a){let e=new Float64Array(16);for(let t=0;t<16;t++)e[t]=a.elements[t];return e}var Ig=new Float64Array(new z().identity().elements);function qo({parent:a,skin:e,armatureName:t="Armature"}){let n=a.addEmpty("Deformer");n.addInt64(e.deformerUid),n.addString(Z(t,"Deformer")),n.addString("Skin"),U(n,"Version",101),jt(n,"Link_DeformAcuracy",50);for(let i of e.clusters)Pg(a,i,e)}function Pg(a,e,t){let n=a.addEmpty("Deformer");n.addInt64(e.clusterUid),n.addString(Z(e.bone.name||"Bone","SubDeformer")),n.addString("Cluster"),U(n,"Version",100);let i=ye(n,"UserData");i.addString(""),i.addString(""),e.indices.length>0&&(Ie(n,"Indexes",Int32Array.from(e.indices)),Pe(n,"Weights",Float64Array.from(e.weights))),Pe(n,"Transform",js(e.transform)),Pe(n,"TransformLink",js(e.transformLink)),Pe(n,"TransformAssociateModel",Ig)}function Ko({parent:a,skin:e,meshUid:t,meshName:n}){let i=a.addEmpty("Pose");i.addInt64(e.bindPoseUid),i.addString(Z(n||"BindPose","Pose")),i.addString("BindPose"),V(i,"Type","BindPose"),U(i,"Version",100),U(i,"NbPoseNodes",1+e.clusters.length);let s=ye(i,"PoseNode");qn(s,"Node",t),Pe(s,"Matrix",js(e.bindMatrix));for(let r of e.clusters){let o=ye(i,"PoseNode");qn(o,"Node",r.boneEntry.uid),Pe(o,"Matrix",js(r.transformLink))}}var Dg=24836,Ng=[0,0,9419963346924634e-45,0];function Yo({parent:a,stacks:e,templates:t}){for(let n of e)Fg(a,n,t)}function Fg(a,e,t){let n=a.addEmpty("AnimationStack");n.addInt64(e.stackUid),n.addString(Z(e.name,"AnimStack")),n.addString("");let i=fe(t,"AnimationStack"),s=ie(n);P(i,s,"p_timestamp","LocalStart",e.start),P(i,s,"p_timestamp","LocalStop",e.stop),P(i,s,"p_timestamp","ReferenceStart",e.start),P(i,s,"p_timestamp","ReferenceStop",e.stop);let r=a.addEmpty("AnimationLayer");r.addInt64(e.layerUid),r.addString(Z(e.name,"AnimLayer")),r.addString("");for(let o of e.curveNodes)Ug(a,o,t)}function Ug(a,e,t){let n=a.addEmpty("AnimationCurveNode");n.addInt64(e.curveNodeUid),n.addString(Z(e.attrName,"AnimCurveNode")),n.addString("");let i=fe(t,"AnimationCurveNode"),s=ie(n);for(let r of e.curves)P(i,s,"p_number",`d|${r.axis}`,r.defaultValue,{animatable:!0});for(let r of e.curves)Og(a,r)}function Og(a,e){let t=a.addEmpty("AnimationCurve");t.addInt64(e.uid),t.addString(Z("","AnimCurve")),t.addString(""),jt(t,"Default",e.defaultValue),U(t,"KeyVer",4008),du(t,"KeyTime",e.times),Eo(t,"KeyValueFloat",e.values),Ie(t,"KeyAttrFlags",new Int32Array([Dg])),Eo(t,"KeyAttrDataFloat",new Float32Array(Ng)),Ie(t,"KeyAttrRefCount",new Int32Array([e.times.length]))}var jo=180/Math.PI,Js=new ke,ku=new pe;function zu(a){return Number.isFinite(a)?BigInt(Math.round(a*1e6))*qs/1000000n:0n}var Bg={position:{attrName:"T",fbxProp:"Lcl Translation",axes:["X","Y","Z"]},scale:{attrName:"S",fbxProp:"Lcl Scaling",axes:["X","Y","Z"]},quaternion:{attrName:"R",fbxProp:"Lcl Rotation",axes:["X","Y","Z"]},morphTargetInfluences:{attrName:"DeformPercent",fbxProp:"DeformPercent",axes:["DeformPercent"]}};function Jo(a){let e=new Set,t=[];function n(i){if(Array.isArray(i.animations))for(let s of i.animations)s&&!e.has(s)&&(e.add(s),t.push(s))}return n(a),a.traverse(i=>{i!==a&&n(i)}),t}function Zo({root:a,clips:e,uids:t,templates:n,settings:i,meshes:s=[]}){let r=[];if(!e||e.length===0)return r;let o=new Map;a.traverse(c=>{c.name&&o.set(c.name,c)});for(let c of e){let l=kg({clip:c,root:a,nodeMap:o,uids:t,templates:n,meshes:s});l&&r.push(l)}return r}function kg({clip:a,root:e,nodeMap:t,uids:n,templates:i,meshes:s}){let r=ru(a.uuid||a.name),o=n.get(r),c=So(a.uuid||a.name),l=n.get(c),u=new Map;for(let d of a.tracks){let p=j.parseTrackName(d.name);if(!p.nodeName)continue;let m=t.get(p.nodeName)||j.findNode(e,p.nodeName);if(!m)continue;let b=Bg[p.propertyName];if(!b)continue;if(p.propertyName==="morphTargetInfluences"&&p.propertyIndex==null){let y=d.getValueSize(),T=d.values.constructor;for(let M=0;M<y;M++){let A=new T(d.times.length);for(let w=0;w<d.times.length;w++)A[w]=d.values[w*y+M];let g=`${m.uuid}|morphTargetInfluences[${M}]`;u.set(g,{node:m,kind:b,propertyName:"morphTargetInfluences",propertyIndex:String(M),track:{times:d.times,values:A}})}continue}let x=p.propertyIndex!=null?`[${p.propertyIndex}]`:"",v=`${m.uuid}|${p.propertyName}${x}`,S=u.get(v);S||(S={node:m,kind:b,propertyName:p.propertyName,propertyIndex:p.propertyIndex,track:null},u.set(v,S)),S.track=d}if(u.size===0)return null;let h=0;for(let d of u.values()){if(d.track.times.length===0)continue;let p=d.track.times[d.track.times.length-1];p>h&&(h=p)}let f=[];for(let d of u.values()){let p=zg({group:d,clip:a,uids:n,templates:i,meshes:s});p&&f.push(p)}return i.register(Mu({})).users+=1,i.register(Au({})).users+=1,{stackKey:r,stackUid:o,layerKey:c,layerUid:l,name:a.name||"AnimStack",start:0n,stop:zu(h),curveNodes:f}}function zg({group:a,clip:e,uids:t,templates:n,meshes:i}){let{node:s,kind:r,propertyName:o,propertyIndex:c,track:l}=a,u=r.axes,h=c!=null?`[${c}]`:"",f=t.get(Mo(e.uuid||e.name,s.uuid,`${o}${h}`)),d;if(o==="quaternion")d=Vg(l.values);else if(o==="morphTargetInfluences"){d=[[]];for(let x=0;x<l.times.length;x++)d[0].push(l.values[x]*100)}else{d=[[],[],[]];for(let x=0;x<l.times.length;x++)d[0].push(l.values[x*3]),d[1].push(l.values[x*3+1]),d[2].push(l.values[x*3+2])}let p=null;if(o==="morphTargetInfluences"){let x=i.find(S=>S.object===s);if(!x||!x.morph)return null;let v=x.morph.channels[parseInt(c,10)];if(!v)return null;p=v.channelUid}let m=new BigInt64Array(l.times.length);for(let x=0;x<l.times.length;x++)m[x]=zu(l.times[x]);let b=[];for(let x=0;x<u.length;x++){let v=t.get(au(e.uuid||e.name,s.uuid,`${o}${h}`,u[x]));n.register(wu({})).users+=1,b.push({uid:v,axis:u[x],defaultValue:d[x][0]??0,times:m,values:Float32Array.from(d[x])})}return n.register(Tu({})).users+=1,{targetUid:p,targetNode:s,fbxProp:r.fbxProp,attrName:r.attrName,curveNodeUid:f,curves:b}}function Vg(a){let e=a.length/4,t=new Array(e),n=new Array(e),i=new Array(e),s=[0,0,0];for(let r=0;r<e;r++){ku.set(a[r*4],a[r*4+1],a[r*4+2],a[r*4+3]),Js.setFromQuaternion(ku,"ZYX");let o=[Js.x*jo,Js.y*jo,Js.z*jo];r>0&&Gg(s,o),t[r]=o[0],n[r]=o[1],i[r]=o[2],s=o}return[t,n,i]}function Gg(a,e){for(let t=0;t<3;t++){for(;e[t]-a[t]>180;)e[t]-=360;for(;e[t]-a[t]<-180;)e[t]+=360}}function $o({parent:a,morphPlan:e,templates:t}){let n=e.mesh.name||"BlendShape";for(let s of e.channels)qg(a,s,t);let i=a.addEmpty("Deformer");i.addInt64(e.blendShapeUid),i.addString(Z(n,"Deformer")),i.addString("BlendShape"),U(i,"Version",100);for(let s of e.channels)Kg(a,s,t)}function qg(a,e,t){let n=a.addEmpty("Geometry");n.addInt64(e.shapeGeomUid),n.addString(Z(e.name,"Geometry")),n.addString("Shape");let i=fe(t,"Geometry"),s=ie(n);U(n,"Version",100),Ie(n,"Indexes",e.indices),Pe(n,"Vertices",e.deltas)}function Kg(a,e,t){let n=a.addEmpty("Deformer");n.addInt64(e.channelUid),n.addString(Z(e.name,"SubDeformer")),n.addString("BlendShapeChannel"),U(n,"Version",100),jt(n,"DeformPercent",e.deformPercent);let i=new Float64Array(e.indices.length);i.fill(100),Pe(n,"FullWeights",i)}function Qo({mesh:a,uids:e,templates:t}){let n=a.geometry,i=n.morphAttributes&&n.morphAttributes.position;if(!i||i.length===0)return null;let s=n.attributes.position;if(!s)return null;let r=n.morphTargetsRelative===!0,o=e.get(cu(n.uuid));t.register(Kn({})).users+=1;let c=a.morphTargetDictionary,l=new Array(i.length);if(c)for(let[p,m]of Object.entries(c))l[m]=p;for(let p=0;p<i.length;p++)l[p]||(l[p]=`morph_${p}`);let u=[],h=Yg(s),f=s.count,d=a.morphTargetInfluences;for(let p=0;p<i.length;p++){let m=i[p],b=l[p],x=e.get(lu(n.uuid,p,b)),v=e.get(uu(n.uuid,p,b));t.register(Kn({})).users+=1,t.register(Xs({})).users+=1;let S=jg(m,h,f,r),y=new Int32Array(f);for(let A=0;A<f;A++)y[A]=A;let M=(Array.isArray(d)&&p<d.length?d[p]:0)*100;u.push({index:p,name:b,channelUid:x,shapeGeomUid:v,deltas:S,indices:y,deformPercent:M})}return{mesh:a,geometry:n,blendShapeUid:o,channels:u}}function Yg(a){let e=a.count,t=new Float32Array(e*3);if(a.isInterleavedBufferAttribute||a.normalized)for(let n=0;n<e;n++)t[n*3]=a.getX(n),t[n*3+1]=a.getY(n),t[n*3+2]=a.getZ(n);else t.set(a.array.subarray(0,e*3));return t}function jg(a,e,t,n){let i=new Float64Array(t*3),s=a.isInterleavedBufferAttribute||a.normalized;if(n)if(s)for(let r=0;r<t;r++)i[r*3]=a.getX(r),i[r*3+1]=a.getY(r),i[r*3+2]=a.getZ(r);else{let r=a.array;for(let o=0;o<t*3;o++)i[o]=r[o]}else if(s)for(let r=0;r<t;r++)i[r*3]=a.getX(r)-e[r*3],i[r*3+1]=a.getY(r)-e[r*3+1],i[r*3+2]=a.getZ(r)-e[r*3+2];else{let r=a.array;for(let o=0;o<t;o++)i[o*3]=r[o*3]-e[o*3],i[o*3+1]=r[o*3+1]-e[o*3+1],i[o*3+2]=r[o*3+2]-e[o*3+2]}return i}var Jg=180/Math.PI,Vu=0,Gu=1,Zg=2,$g=3;function Qg(a){return a.isDirectionalLight?Gu:a.isSpotLight?Zg:a.isPointLight?Vu:a.isHemisphereLight?Gu:a.isRectAreaLight?$g:Vu}function ec({parent:a,light:e,attrUid:t,templates:n}){let i=a.addEmpty("NodeAttribute");i.addInt64(t),i.addString(Z(e.name||"Light","NodeAttribute")),i.addString("Light"),U(i,"GeometryVersion",124);let s=fe(n,"NodeAttribute"),r=ie(i),o=Qg(e);P(s,r,"p_enum","LightType",o);let c=!e.isAmbientLight;P(s,r,"p_bool","CastLight",c);let l=e.color||{r:1,g:1,b:1};P(s,r,"p_color","Color",[l.r,l.g,l.b],{animatable:!0});let u=(e.intensity??1)*100;if(P(s,r,"p_number","Intensity",u,{animatable:!0}),P(s,r,"p_enum","DecayType",2),P(s,r,"p_double","DecayStart",25*1),P(s,r,"p_bool","CastShadows",e.castShadow===!0),P(s,r,"p_color","ShadowColor",[0,0,0],{animatable:!0}),e.isSpotLight){let f=(e.angle??Math.PI/3)*Jg,d=Math.min(1,Math.max(0,e.penumbra??0)),p=f*(1-d);P(s,r,"p_double","OuterAngle",f),P(s,r,"p_double","InnerAngle",p)}if(e.isPointLight||e.isSpotLight){let f=e.distance??0;P(s,r,"p_double","FarAttenuationEnd",f),P(s,r,"p_bool","EnableFarAttenuation",f>0)}}var yM=180/Math.PI;function tc({parent:a,camera:e,attrUid:t,templates:n,settings:i={}}){let s=a.addEmpty("NodeAttribute");s.addInt64(t),s.addString(Z(e.name||"Camera","NodeAttribute")),s.addString("Camera");let r=fe(n,"NodeAttribute"),o=ie(s),c=e.isOrthographicCamera===!0;P(r,o,"p_enum","CameraProjectionType",c?1:0);let l=e.aspect??16/9,u=i.cameraAspectWidth??1920,h=u/l;P(r,o,"p_enum","AspectRatioMode",2),P(r,o,"p_double","AspectWidth",u),P(r,o,"p_double","AspectHeight",h),P(r,o,"p_double","PixelAspectRatio",1);let f=e.fov??50,d=f*l;P(r,o,"p_fov","FieldOfView",f,{animatable:!0}),P(r,o,"p_fov_x","FieldOfViewX",d,{animatable:!0}),P(r,o,"p_fov_y","FieldOfViewY",f,{animatable:!0});let p=e.getFocalLength?e.getFocalLength():35;P(r,o,"p_double","FocalLength",p,{animatable:!0});let m=i.unitScale??1,b=(e.near??.1)*m,x=(e.far??2e3)*m;if(P(r,o,"p_double","NearPlane",b),P(r,o,"p_double","FarPlane",x),P(r,o,"p_enum","BackPlaneDistanceMode",1),P(r,o,"p_double","BackPlaneDistance",x,{animatable:!0}),c){let v=(e.right??1)-(e.left??-1);P(r,o,"p_double","OrthoZoom",v)}V(s,"TypeFlags","Camera"),U(s,"GeometryVersion",124),Zs(s,"Position",[0,0,0]),Zs(s,"Up",[0,1,0]),Zs(s,"LookAt",[0,0,-1]),U(s,"ShowInfoOnMoving",1),U(s,"ShowAudio",0),Zs(s,"AudioColor",[0,1,0]),jt(s,"CameraOrthoZoom",1)}function Zs(a,e,[t,n,i]){let s=a.addEmpty(e);s.addFloat64(t),s.addFloat64(n),s.addFloat64(i)}var t0=1e3,n0=1002;function Hu(a){return a===t0||a===n0?0:1}function nc({parent:a,textureEntry:e,templates:t}){let n=e.texture,i=e.fileName,s=n.name||`texture_${e.texUid}`,r=a.addEmpty("Texture");r.addInt64(e.texUid),r.addString(Z(s,"Texture")),r.addString(""),V(r,"Type","TextureVideoClip"),U(r,"Version",202),V(r,"TextureName",Z(s,"Texture")),V(r,"Media",Z(s,"Video")),V(r,"FileName",i),V(r,"RelativeFilename",i);let o=fe(t,"Texture"),c=ie(r),l=e.imageBytes!=null;P(o,c,"p_enum","AlphaSource",l?2:0),P(o,c,"p_bool","PremultiplyAlpha",!1),P(o,c,"p_enum","CurrentMappingType",0),P(o,c,"p_enum","WrapModeU",Hu(n.wrapS)),P(o,c,"p_enum","WrapModeV",Hu(n.wrapT));let u=n.offset||{x:0,y:0},h=n.repeat||{x:1,y:1},f=n.rotation??0;P(o,c,"p_vector_3d","Translation",[u.x,u.y,0]),P(o,c,"p_vector_3d","Rotation",[0,0,-f]),P(o,c,"p_vector_3d","Scaling",[h.x,h.y,1]),P(o,c,"p_bool","UseMaterial",!0),P(o,c,"p_bool","UseMipMap",!1)}function ic({parent:a,textureEntry:e,templates:t}){let n=e.fileName,i=e.imageBytes,s=e.texture.name||`texture_${e.vidUid}`,r=a.addEmpty("Video");r.addInt64(e.vidUid),r.addString(Z(s,"Video")),r.addString("Clip"),V(r,"Type","Clip");let o=fe(t,"Video"),c=ie(r);P(o,c,"p_string_url","Path",n),U(r,"UseMipMap",0),V(r,"Filename",n),V(r,"RelativeFilename",n),i!=null&&Ws(r,"Content",i)}var i0=new Uint8Array([137,80,78,71,13,10,26,10]),sc=null;function s0(){if(sc)return sc;let a=new Uint32Array(256);for(let e=0;e<256;e++){let t=e;for(let n=0;n<8;n++)t=t&1?3988292384^t>>>1:t>>>1;a[e]=t>>>0}return sc=a,a}function r0(a){let e=s0(),t=4294967295;for(let n=0;n<a.length;n++)t=(e[(t^a[n])&255]^t>>>8)>>>0;return(t^4294967295)>>>0}function rc(a,e){let t=new TextEncoder().encode(a);if(t.length!==4)throw new Error(`PNG chunk type must be 4 bytes, got ${a}`);let n=new Uint8Array(8+e.length+4),i=new DataView(n.buffer);i.setUint32(0,e.length,!1),n.set(t,4),n.set(e,8);let s=new Uint8Array(4+e.length);return s.set(t,0),s.set(e,4),i.setUint32(8+e.length,r0(s),!1),n}function a0(a){let e=0;for(let i of a)e+=i.length;let t=new Uint8Array(e),n=0;for(let i of a)t.set(i,n),n+=i.length;return t}function $s(a,e,t){if(a.length!==e*t*4)throw new Error(`PNG: expected ${e*t*4} RGBA bytes, got ${a.length}`);let n=e*4,i=new Uint8Array(t*(1+n));for(let c=0;c<t;c++)i[c*(1+n)]=0,i.set(a.subarray(c*n,(c+1)*n),c*(1+n)+1);let s=Gs(i,{level:6}),r=new Uint8Array(13),o=new DataView(r.buffer);return o.setUint32(0,e,!1),o.setUint32(4,t,!1),r[8]=8,r[9]=6,r[10]=0,r[11]=0,r[12]=0,a0([i0,rc("IHDR",r),rc("IDAT",s),rc("IEND",new Uint8Array(0))])}async function ac(a){if(a.isDataTexture||a.image&&a.image.data instanceof Uint8Array){let{data:t,width:n,height:i}=a.image;if(t.length!==n*i*4)throw new Error(`DataTexture must be RGBAFormat / UnsignedByteType for PNG embedding (got data ${t.length} bytes for ${n}\xD7${i}; expected ${n*i*4})`);return{bytes:$s(t,n,i),extension:"png"}}let e=a.image;if(!e)throw new Error("Texture has no image source");if(typeof OffscreenCanvas<"u"){let t=e.width||e.naturalWidth||0,n=e.height||e.naturalHeight||0;if(!t||!n)throw new Error(`Texture image has zero size (${t}\xD7${n})`);let i=new OffscreenCanvas(t,n);i.getContext("2d").drawImage(e,0,0);let r=await i.convertToBlob({type:"image/png"});return{bytes:new Uint8Array(await r.arrayBuffer()),extension:"png"}}if(typeof document<"u"){let t=e.width||e.naturalWidth||0,n=e.height||e.naturalHeight||0;if(!t||!n)throw new Error(`Texture image has zero size (${t}\xD7${n})`);let i=document.createElement("canvas");return i.width=t,i.height=n,i.getContext("2d").drawImage(e,0,0),await new Promise((r,o)=>{i.toBlob(async c=>{if(!c)return o(new Error("canvas.toBlob returned null"));let l=new Uint8Array(await c.arrayBuffer());r({bytes:l,extension:"png"})},"image/png")})}throw new Error("Cannot encode texture: not a DataTexture and no canvas API available. In Node, use THREE.DataTexture; in browser, ensure canvas is supported.")}function Wu(a){let e=Array.isArray(a)?a:[a];for(let t of e)if(t)for(let n of Object.keys(Qs)){let i=t[n];if(i&&i.isTexture)return i.flipY===!1}return!1}var Qs={map:"DiffuseColor",emissiveMap:"EmissiveColor",normalMap:"NormalMap",bumpMap:"Bump",alphaMap:"TransparentColor",specularMap:"SpecularColor",aoMap:"Maya|TEX_ao_map",displacementMap:"DisplacementColor",envMap:"ReflectionColor"};function oc({materials:a,uids:e,templates:t,connections:n}){let i=new Map;for(let[s,r]of a)for(let o of Object.keys(Qs)){let c=s[o];if(!c||!c.isTexture)continue;let l=i.get(c);if(!l){let h=c.name||`texture_${i.size}`;l={texUid:e.get(Ql(c.uuid)),vidUid:e.get(eu(c.uuid)),texture:c,slotName:o,fileName:`${o0(h)}.png`,imageBytes:null,extension:"png"},i.set(c,l),t.register(yu({})).users+=1,t.register(vu({})).users+=1,n.push(["OO",l.vidUid,l.texUid])}let u=Qs[o];n.push(["OP",l.texUid,r.uid,u])}return{textures:i}}async function cc(a){!a||!a.textures||await Promise.all([...a.textures.values()].map(async e=>{try{let t=await ac(e.texture);e.imageBytes=t.bytes,e.extension=t.extension,e.fileName&&!e.fileName.endsWith(`.${e.extension}`)&&(e.fileName=e.fileName.replace(/\.[^.]+$/,"")+"."+e.extension)}catch(t){console.warn(`fbx-exporter-three: failed to embed texture "${e.texture.name||"<unnamed>"}": ${t.message}`),e.imageBytes=null}}))}function o0(a){return String(a).replace(/[^a-zA-Z0-9_\-]/g,"_")}var Xu=new z,BM=new z,qu=new z;function c0(a){return a.isBone?"LimbNode":a.isMesh?"Mesh":a.isLight&&!a.isAmbientLight?"Light":a.isCamera?"Camera":"Null"}function er(a,e){return!(a.isScene||e&&e.onlyVisible&&a.visible===!1||e&&typeof e.objectFilter=="function"&&e.objectFilter(a)===!1)}function tr(a,e={}){e=Oo(e);let t=Bo(e);if(t.bake&&!t.isIdentity&&!e._suppressBakeWarning){let g=!1;a.traverse(w=>{if(!(g||w.isScene)){if(w.isSkinnedMesh||w.isLight||w.isCamera){g=!0;return}w.isMesh&&(w.position.lengthSq()>1e-12||w.quaternion.x**2+w.quaternion.y**2+w.quaternion.z**2>1e-12)&&(g=!0)}}),g&&console.warn("fbx-exporter-three: bakeSpaceTransform=true currently bakes only Vertices+Normals. The scene contains object transforms / skinning / animation / lights / cameras whose matrices will NOT be baked, leaving the output file internally inconsistent. Pass { bakeSpaceTransform: false } unless your scene is a single mesh at the origin.")}let n=new Fi,i=new Ui,s=[],r=[],o=[],c=[],l=[],u=new Map,h=[],f=new Map,d=new Map,p=[];a.updateMatrixWorld(!0),i.register(mu(e)).users=1,a.traverse(g=>{if(!er(g,e))return;let w=c0(g),R=n.get(Yt(g.uuid));if(i.register(Ro(e)).users+=1,w==="Mesh"){let C=S(g.geometry),{entries:N,slotRemap:L}=A(g),F={object:g,uid:R,geometry:g.geometry,geomUid:C.uid,materials:N,slotRemap:L,skin:null,morph:null};s.push(F),g.isSkinnedMesh&&g.skeleton&&g.skeleton.bones.length>0&&(F.skin=M(g)),F.morph=Qo({mesh:g,uids:n,templates:i})}else if(w==="LimbNode")T(g);else if(w==="Light"){let C=n.get(`${re("object",g.uuid)}|NodeAttr|Light`);i.register(gu(e)).users+=1;let N=null;(g.isDirectionalLight||g.isSpotLight)&&g.target&&(N=y(g.target)),o.push({object:g,uid:R,attrUid:C,targetUid:N})}else if(w==="Camera"){let C=n.get(`${re("object",g.uuid)}|NodeAttr|Camera`);i.register(xu(e)).users+=1,c.push({object:g,uid:R,attrUid:C})}else{let C=n.get(`${re("object",g.uuid)}|NodeAttr|Null`);i.register(Co(e)).users+=1,r.push({object:g,uid:R,nodeAttrUid:C})}});let m=new Set;a.traverse(g=>{if(!er(g,e))return;let w=n.get(Yt(g.uuid));m.add(w);let R=0n;g.parent&&er(g.parent,e)&&(R=n.get(Yt(g.parent.uuid))),p.push(["OO",w,R])});for(let[g,w]of u){if(m.has(w.uid))continue;let R=0n;if(g.parent&&er(g.parent,e)){let C=n.get(Yt(g.parent.uuid));(m.has(C)||u.has(g.parent))&&(R=C)}p.push(["OO",w.uid,R])}for(let g of r)p.push(["OO",g.nodeAttrUid,g.uid]);for(let[,g]of u)p.push(["OO",g.attrUid,g.uid]);for(let g of o)p.push(["OO",g.attrUid,g.uid]);for(let g of c)p.push(["OO",g.attrUid,g.uid]);for(let g of l)m.has(g.uid)||(g.auxiliary=!0,g.nodeAttrUid=n.get(`${re("object",g.target.uuid)}|NodeAttr|Null`),i.register(Co(e)).users+=1,i.register(Ro(e)).users+=1,p.push(["OO",g.nodeAttrUid,g.uid]),p.push(["OO",g.uid,0n]));for(let g of o)g.targetUid!=null&&p.push(["OP",g.targetUid,g.uid,"LookAtProperty"]);for(let g of s)p.push(["OO",g.geomUid,g.uid]);for(let g of s)for(let w of g.materials)p.push(["OO",w.uid,g.uid]);for(let g of s)if(g.skin){p.push(["OO",g.skin.deformerUid,g.geomUid]);for(let w of g.skin.clusters)p.push(["OO",w.clusterUid,g.skin.deformerUid]),p.push(["OO",w.boneEntry.uid,w.clusterUid])}for(let g of s)if(g.morph){p.push(["OO",g.morph.blendShapeUid,g.geomUid]);for(let w of g.morph.channels)p.push(["OO",w.channelUid,g.morph.blendShapeUid]),p.push(["OO",w.shapeGeomUid,w.channelUid])}let b=oc({materials:d,uids:n,templates:i,connections:p}),x;e.includeAnimations===!1?x=[]:e.animations?x=e.animations:x=Jo(a);let v=Zo({root:a,clips:x,uids:n,templates:i,settings:e,meshes:s});for(let g of v)for(let w of g.curveNodes)w.targetUid==null&&(w.targetUid=n.get(Yt(w.targetNode.uuid)));for(let g of v){p.push(["OO",g.layerUid,g.stackUid]);for(let w of g.curveNodes){p.push(["OO",w.curveNodeUid,g.layerUid]),p.push(["OP",w.curveNodeUid,w.targetUid,w.fbxProp]);for(let R of w.curves)p.push(["OP",R.uid,w.curveNodeUid,`d|${R.axis}`])}}return{settings:e,uids:n,templates:i,meshes:s,empties:r,bones:u,skins:h,geometries:f,materials:d,lights:o,cameras:c,lightTargets:l,textures:b,animStacks:v,connections:p,rootInput:a,transformCtx:t};function S(g){let w=f.get(g);if(w)return w.refCount++,w;let R=Zl(g.uuid),C=n.get(R);return i.register(Xs(e)).users+=1,w={uid:C,key:R,refCount:1},f.set(g,w),w}function y(g){let w=l.find(C=>C.target===g);if(w)return w.uid;let R=n.get(Yt(g.uuid));return l.push({target:g,uid:R,nodeAttrUid:null,auxiliary:!1}),R}function T(g){let w=u.get(g);if(w)return w;let R=n.get(Yt(g.uuid)),C=n.get(tu(g.uuid,g.uuid));return i.register(bu(e)).users+=1,w={uid:R,attrUid:C},u.set(g,w),w}function M(g){let w=g.skeleton,R=w.bones,C=w.boneInverses,N=g.bindMatrix,L=n.get(nu(g.uuid,g.geometry.uuid)),F=n.get(su(g.uuid,g.geometry.uuid));i.register(Kn(e)).users+=1,i.register(Su(e)).users+=1;let I=new Map;for(let k=0;k<R.length;k++){let W=R[k];W&&!I.has(W)&&I.set(W,new z().copy(C[k]).invert())}for(let k of R){if(!k)continue;let W=T(k);if(W.bindLocalMatrix)continue;let me=I.get(k),se=k.parent,we;se&&I.has(se)?we=I.get(se):se&&(we=se.matrixWorld);let Fe=we?new z().copy(we).invert().multiply(me):me.clone();W.bindLocalMatrix=Fe}let O=[];for(let k=0;k<R.length;k++){let W=R[k];if(!W)continue;let me=T(W),se=iu(g.uuid,g.geometry.uuid,W.uuid),we=n.get(se);i.register(Kn(e)).users+=1;let{indices:Fe,weights:Ee}=l0(g.geometry,k);Xu.copy(C[k]).invert(),qu.copy(C[k]).multiply(N),O.push({boneIdx:k,bone:W,boneEntry:me,clusterUid:we,clusterKey:se,indices:Fe,weights:Ee,transform:qu.clone(),transformLink:Xu.clone()})}let B={skinnedMesh:g,deformerUid:L,bindPoseUid:F,bindMatrix:N.clone(),clusters:O};return h.push(B),B}function A(g){let w=g.material,R=Array.isArray(w)?w:w?[w]:[],C=[],N=new Map,L=new Array(R.length),F=0;for(let I=0;I<R.length;I++){let O=R[I];if(!O){L[I]=0;continue}let B=N.get(O);if(B!==void 0){L[I]=B;continue}let k=d.get(O);if(!k){let W=$l(O.uuid),me=n.get(W);i.register(_u(e)).users+=1,k={uid:me,key:W,refCount:0},d.set(O,k)}k.refCount++,N.set(O,F),L[I]=F,C.push({material:O,uid:k.uid,slot:F}),F++}return{entries:C,slotRemap:L}}}function l0(a,e){let t=a.attributes.skinIndex,n=a.attributes.skinWeight;if(!t||!n)return{indices:[],weights:[]};let i=t.count,s=[],r=[];for(let o=0;o<i;o++)for(let c=0;c<4;c++){if((c===0?t.getX(o):c===1?t.getY(o):c===2?t.getZ(o):t.getW(o))!==e)continue;let u=c===0?n.getX(o):c===1?n.getY(o):c===2?n.getZ(o):n.getW(o);u>0&&(s.push(o),r.push(u))}return{indices:s,weights:r}}var nr=new E;function ir(a){let{settings:e,templates:t,meshes:n,empties:i,bones:s,lights:r,cameras:o,lightTargets:c,materials:l,textures:u,animStacks:h,connections:f,rootInput:d}=a,p=e.version??7400,m=new ot("");No({root:m,settings:{...e,version:p},sceneName:d.name||"Scene"}),Fo({root:m,templates:t});let b=m.addEmpty("Objects");for(let M of i)Ys({parent:b,name:M.object.name,uid:M.nodeAttrUid,templates:t});for(let[M,A]of s)Xo({parent:b,bone:M,attrUid:A.attrUid,templates:t});for(let M of r)ec({parent:b,light:M.object,attrUid:M.attrUid,templates:t});for(let M of o)tc({parent:b,camera:M.object,attrUid:M.attrUid,templates:t,settings:e});if(c)for(let M of c)M.auxiliary&&Ys({parent:b,name:M.target.name||"Light Target",uid:M.nodeAttrUid,templates:t});let x=new Set;for(let M of n)x.has(M.geomUid)||(x.add(M.geomUid),Go({parent:b,geometry:M.geometry,uid:M.geomUid,name:M.geometry.name||M.object.name,templates:t,materialSlotCount:M.materials.length,groups:M.geometry.groups||[],slotRemap:M.slotRemap,transformCtx:a.transformCtx,flipUV:e.flipUV==="auto"||e.flipUV===void 0?Wu(M.object.material):!!e.flipUV}));let v=new Set,S=new Set;for(let M of r)M.targetUid!=null&&S.add(M.object);let y=!!e.customProperties;if(d.traverse(M=>{if(M.isScene)return;let A=n.find(F=>F.object===M),g=i.find(F=>F.object===M),w=r.find(F=>F.object===M),R=o.find(F=>F.object===M),C=s.get(M),N=A?.uid??g?.uid??w?.uid??R?.uid??C?.uid;if(N==null)return;let L=C?.bindLocalMatrix||void 0;ki({parent:b,object:M,uid:N,templates:t,hasLookAtTarget:S.has(M),overrideMatrix:L,customProperties:y}),v.add(N)}),c)for(let M of c)M.auxiliary&&(M.target.updateMatrixWorld(!0),M.target.getWorldPosition(nr),ki({parent:b,object:M.target,uid:M.uid,templates:t,overrideTranslation:[nr.x,nr.y,nr.z]}),v.add(M.uid));for(let[M,A]of s)v.has(A.uid)||ki({parent:b,object:M,uid:A.uid,templates:t});for(let[M,A]of l)Wo({parent:b,material:M,uid:A.uid,templates:t});if(u&&u.textures){for(let[,M]of u.textures)nc({parent:b,textureEntry:M,templates:t});for(let[,M]of u.textures)ic({parent:b,textureEntry:M,templates:t})}Yo({parent:b,stacks:h,templates:t});for(let M of n)M.morph&&$o({parent:b,morphPlan:M.morph,templates:t});for(let M of n)M.skin&&(Ko({parent:b,skin:M.skin,meshUid:M.uid,meshName:M.object.name}),qo({parent:b,skin:M.skin,armatureName:M.object.name||"Armature"}));return Uo({root:m,connections:f}),m.addEmpty("Takes").addEmpty("Current").addString(""),yo(m,{version:p})}var Ku={version:7400,fps:24,embedTextures:!0},zi=class{constructor(){ue(this,"pluginCallbacks",[])}register(e){return this.pluginCallbacks.includes(e)||this.pluginCallbacks.push(e),this}unregister(e){let t=this.pluginCallbacks.indexOf(e);return t!==-1&&this.pluginCallbacks.splice(t,1),this}parseSync(e,t={}){let n={...Ku,...t},i=tr(e,n);n.embedTextures!==!1&&u0(i);for(let s of this.pluginCallbacks)s(i);return ir(i)}parse(e,t,n,i){this.parseAsync(e,i).then(t,n??(s=>{throw s}))}async parseAsync(e,t={}){let n={...Ku,...t},i=tr(e,n);n.embedTextures!==!1&&i.textures&&await cc(i.textures);for(let s of this.pluginCallbacks)s(i);return ir(i)}};function u0(a){if(!(!a.textures||!a.textures.textures))for(let[,e]of a.textures.textures){let t=e.texture;if(t.isDataTexture||t.image&&t.image.data instanceof Uint8Array)try{let{data:n,width:i,height:s}=t.image;e.imageBytes=$s(n,i,s),e.extension="png"}catch(n){console.warn(`fbx-exporter-three: failed to encode DataTexture "${t.name||"<unnamed>"}": ${n.message}`)}else console.warn(`fbx-exporter-three: skipping embed of texture "${t.name||"<unnamed>"}" \u2014 parseSync only handles DataTextures. Use parseAsync to embed HTMLImage / canvas-backed textures.`)}}var h0={printer_name:"Bambu Lab A1",filament:"Bambu PLA Basic @BBL A1",printableWidth:256,printableDepth:256,printableHeight:256,printableArea:["0x0","256x0","256x256","0x256"],printerSettingsId:"Bambu Lab A1 0.4 nozzle",printSettingsId:"0.20mm Standard @BBL A1",compression:"standard",metadata:{Application:"BambuStudio-02.04.00.70",ApplicationTitle:"Exported 3D Model"}},f0={standard:"DEFLATE",none:"STORE"};async function Yu(a,e){let t={},n={file:(A,g)=>{t[A]=g}},i=Object.assign({},h0,e),s=f0[i.compression],r=[],o=[],c=[],l=A=>{A.updateMatrixWorld(!0);let g=A.geometry,w=g.attributes.position,R=g.index,C=null;if(A.material){let O=new H,B=Array.isArray(A.material)?A.material[0]:A.material;B&&"color"in B&&B.color?O.copy(B.color):O.set(8421504);let k=o.find(W=>W.color.r===O.r&&W.color.g===O.g&&W.color.b===O.b);if(k)C=k;else{let W=o.length+1;C={id:o.length+1,color:O,name:A.name?`${A.name}_material`:`material_${o.length}`,extruder:W},o.push(C)}}let N=r.length+1,L={id:N,type:"mesh",vertices:[],triangles:[],material:C,name:A.name||`Mesh-${N}`,subComponents:[],uuid:lc()},F=new Map,I=O=>{let B=new E;B.fromBufferAttribute(w,O);let k=`${B.x},${B.y},${B.z}`;return F.has(k)||(F.set(k,L.vertices.length),L.vertices.push({x:B.x,y:B.y,z:B.z})),F.get(k)};if(R)for(let O=0;O<R.count;O+=3)L.triangles.push({v1:I(R.getX(O)),v2:I(R.getX(O+1)),v3:I(R.getX(O+2))});else for(let O=0;O<w.count;O+=3)L.triangles.push({v1:I(O),v2:I(O+1),v3:I(O+2)});return r.push(L),N},u=A=>{if(A.type==="Mesh")return l(A);if(A.type==="Group"||A.type==="Object3D"||A.type==="Scene"){let g=[];if(A.updateMatrixWorld(!0),A.children.forEach(w=>{let R=u(w);if(R!==-1){let C=w.matrixWorld.clone().premultiply(A.matrixWorld.clone().invert());g.push({objectId:R,transform:C})}}),g.length>0){let w=r.length+1;return r.push({id:w,type:"assembly",subComponents:g,name:A.name||`Group-${w}`,vertices:[],triangles:[],material:null,uuid:lc()}),w}}return-1},h=a.type==="Scene"?a.children:[a],f=[];h.forEach(A=>{let g=u(A);if(g!==-1){A.updateMatrix();let w=A.matrix.clone(),R=r.find(N=>N.id===g),C=N=>N.type==="assembly"?N.subComponents.flatMap(L=>{let F=r.find(I=>I.id===L.objectId);return C(F).map(I=>I.clone().applyMatrix4(L.transform))}):N.vertices.map(L=>new E(L.x,L.y,L.z));C(R).forEach(N=>{N.applyMatrix4(w),f.push(N)}),c.push({objectId:g,transformMatrix:w,uuid:lc()})}});let d={x:1/0,y:1/0,z:1/0},p={x:-1/0,y:-1/0,z:-1/0};f.length>0?f.forEach(A=>{d.x=Math.min(d.x,A.x),d.y=Math.min(d.y,A.y),d.z=Math.min(d.z,A.z),p.x=Math.max(p.x,A.x),p.y=Math.max(p.y,A.y),p.z=Math.max(p.z,A.z)}):(d={x:0,y:0,z:0},p={x:0,y:0,z:0});let m={x:(d.x+p.x)/2,y:(d.y+p.y)/2,z:(d.z+p.z)/2},b={x:i.printableWidth/2,y:i.printableDepth/2,z:0},x={x:b.x-m.x,y:b.y-m.y,z:b.z-d.z},v=d0(r,c,x,i),S=p0(r,c),y=m0(o,i);n.file("_rels/.rels",g0()),n.file("3D/3dmodel.model",v),n.file("Metadata/model_settings.config",S),n.file("Metadata/project_settings.config",y),n.file("[Content_Types].xml",x0());let T={};for(let[A,g]of Object.entries(t))T[A]=typeof g=="string"?zs(g):g;let M=ql(T,{level:s==="STORE"?0:6});return new Blob([M],{type:"application/vnd.ms-package.3dmanufacturing-3dmodel+xml"})}function d0(a,e,t,n){let i=[],s=n.metadata;i.push(`<metadata name="CreationDate">${new Date().toISOString()}</metadata>`);for(let c in s)i.push(`<metadata name="${c}">${s[c]}</metadata>`);let r=a.map(c=>{if(c.type==="assembly"){let l=c.subComponents.map(u=>{let h=u.transform.elements,f=`${h[0].toFixed(5)} ${h[1].toFixed(5)} ${h[2].toFixed(5)} ${h[4].toFixed(5)} ${h[5].toFixed(5)} ${h[6].toFixed(5)} ${h[8].toFixed(5)} ${h[9].toFixed(5)} ${h[10].toFixed(5)} ${h[12].toFixed(5)} ${h[13].toFixed(5)} ${h[14].toFixed(5)}`;return`<component objectid="${u.objectId}" transform="${f}" />`}).join("");return`<object id="${c.id}" type="model" name="${c.name}"><components>${l}</components></object>`}else{let l=c.vertices.map(h=>`<vertex x="${h.x.toFixed(5)}" y="${h.y.toFixed(5)}" z="${h.z.toFixed(5)}" />`).join(" "),u=c.triangles.map(h=>`<triangle v1="${h.v1}" v2="${h.v2}" v3="${h.v3}" />`).join(" ");return`<object id="${c.id}" type="model" name="${c.name}"><mesh><vertices>${l}</vertices><triangles>${u}</triangles></mesh></object>`}}).join(`
`),o=e.map(c=>{let l=c.transformMatrix.elements,u=l[12]+t.x,h=l[13]+t.y,f=l[14]+t.z,d=`${l[0].toFixed(5)} ${l[1].toFixed(5)} ${l[2].toFixed(5)} ${l[4].toFixed(5)} ${l[5].toFixed(5)} ${l[6].toFixed(5)} ${l[8].toFixed(5)} ${l[9].toFixed(5)} ${l[10].toFixed(5)} ${u.toFixed(5)} ${h.toFixed(5)} ${f.toFixed(5)}`;return`<item objectid="${c.objectId}" transform="${d}" printable="1" />`}).join(`
`);return`<?xml version="1.0" encoding="UTF-8"?>
<model unit="millimeter" xml:lang="en-US" xmlns="http://schemas.microsoft.com/3dmanufacturing/core/2015/02" xmlns:slic3rpe="http://schemas.slic3r.org/3mf/2017/06" xmlns:p="http://schemas.microsoft.com/3dmanufacturing/production/2015/06" requiredextensions="p">
    ${i.join(`
    `)}
    <resources>
${r}
    </resources>
    <build>
${o}
    </build>
</model>`}function p0(a,e){let t="",n="",i="";return e.forEach((s,r)=>{let o=s.objectId,c=a.find(f=>f.id===o),l=[],u=f=>{f.type==="mesh"?l.push(f):f.subComponents.forEach(d=>u(a.find(p=>p.id===d.objectId)))};u(c);let h=l.map(f=>{let d=f.material?f.material.extruder:1;return`    <part id="${f.id}" subtype="normal_part">
      <metadata key="name" value="${f.name}"/>
      <metadata key="extruder" value="${d}"/>
      <mesh_stat edges_fixed="0" degenerate_facets="0" facets_removed="0" facets_reversed="0" backwards_edges="0"/>
    </part>`}).join(`
`);t+=`  <object id="${o}">
    <metadata key="name" value="${c.name}"/>
    <metadata key="extruder" value="1"/>
    <metadata key="thumbnail_file" value=""/>
${h}
  </object>
`,n+=`    <model_instance>
      <metadata key="object_id" value="${o}"/>
      <metadata key="instance_id" value="0"/>
      <metadata key="identify_id" value="${r+1}"/>
    </model_instance>
`,i+=`    <assemble_item object_id="${o}" instance_id="0" offset="0 0 0"/>
`}),`<?xml version="1.0" encoding="UTF-8"?>
<config>
${t}
  <plate>
    <metadata key="plater_id" value="1"/>
    <metadata key="plater_name" value="plate-1"/>
${n}
  </plate>
  <assemble>
${i}
  </assemble>
</config>`}function m0(a,e){let t=a.map(s=>`#${s.color.getHexString()}`);for(;t.length<2;)t.push("#FFFFFF");let n=new Set(e.different_settings_to_system||[]),i={printable_area:e.printableArea,printable_height:e.printableHeight.toString(),bed_exclude_area:[],filament_colour:t,filament_settings_id:Array.from({length:t.length}).fill(e.filament),filament_diameter:Array.from({length:t.length}).fill("1.75"),filament_is_support:Array.from({length:t.length}).fill("0"),printer_model:e.printer_name,layer_height:"0.2",wall_loops:"2",sparse_infill_density:"15%",printer_settings_id:e.printerSettingsId,printer_variant:"0.4",nozzle_diameter:["0.4"],enable_support:"0",support_type:"normal(auto)",print_settings_id:e.printSettingsId};return e.seam_position&&(i.seam_position=e.seam_position,n.add("seam_position")),n.size>0&&(i.different_settings_to_system=Array.from(n)),JSON.stringify(i)}function g0(){return`<?xml version="1.0" encoding="UTF-8"?>
<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">
  <Relationship Id="rel-1" Target="/3D/3dmodel.model" Type="http://schemas.microsoft.com/3dmanufacturing/2013/01/3dmodel"/>
  <Relationship Id="rel-2" Target="/Metadata/model_settings.config" Type="http://schemas.microsoft.com/3dmanufacturing/2013/01/3dmodel"/>
  <Relationship Id="rel-3" Target="/Metadata/project_settings.config" Type="http://schemas.microsoft.com/3dmanufacturing/2013/01/3dmodel"/>
</Relationships>`}function x0(){return`<?xml version="1.0" encoding="UTF-8"?>
<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">
  <Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml" />
  <Default Extension="model" ContentType="application/vnd.ms-package.3dmanufacturing-3dmodel+xml" />
  <Default Extension="config" ContentType="application/vnd.ms-package.3dmanufacturing-3dmodel+xml" />
  <Default Extension="png" ContentType="image/png" />
  <Default Extension="gcode" ContentType="text/x.gcode"/>
</Types>`}function lc(){return"xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx".replace(/[xy]/g,a=>{let e=Math.random()*16|0;return(a==="x"?e:e&3|8).toString(16)})}async function ju(a){let e=new Ns;return e.setMeshoptDecoder(Ml),await new Promise((t,n)=>e.parse(a,"",t,n))}function Yn(a){let e=0,t=0;return a.traverse(n=>{if(n.isMesh){e++;let i=n.geometry;t+=(i.index?i.index.count:i.attributes.position.count)/3}}),{meshes:e,triangles:Math.round(t)}}async function b0(a,e,t={}){let i=(await ju(a)).scene,s=String(e||"").toLowerCase(),r=t.basename||"model";if(s==="stl"){let o=new Os().parse(i,{binary:!0});return{blob:new Blob([o],{type:"model/stl"}),filename:`${r}.stl`,stats:Yn(i)}}if(s==="obj"){let o=new Bs().parse(i);return{blob:new Blob([o],{type:"text/plain"}),filename:`${r}.obj`,stats:Yn(i)}}if(s==="gltf"){let o=await new Kt().parseAsync(i,{binary:!1}),c=JSON.stringify(o);return{blob:new Blob([c],{type:"model/gltf+json"}),filename:`${r}.gltf`,stats:Yn(i)}}if(s==="fbx"){let o=new zi,c=o.parseAsync?await o.parseAsync(i,t.fbxOptions||{}):o.parseSync(i,t.fbxOptions||{});return{blob:new Blob([c],{type:"application/octet-stream"}),filename:`${r}.fbx`,stats:Yn(i)}}if(s==="3mf")return{blob:await Yu(i,t.printConfig||{}),filename:`${r}.3mf`,stats:Yn(i)};throw new Error(`Unsupported format: ${e}`)}var _0=["stl","obj","fbx","3mf","gltf","glb"];return nh(y0);})();


})();

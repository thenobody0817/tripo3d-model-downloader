// ==UserScript==
// @name         Tripo3D Model Downloader
// @namespace    http://tampermonkey.net/
// @version      9.1
// @description  Extract and download GLB models via Network Interception (Fetch+XHR), API Response Parsing, State Analysis & Resource Monitoring
// @author       TheNobody (V9.1 fix — safe recursion + reliable binary download)
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
        const prefix = `[Tripo V9.1 ${tag}]`;
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
        } else if (url.includes('rendered_image') || url.match(/\.(png|jpg|jpeg)/)) {
            state.capturedRenderedImage = url;
        } else {
            // Default: treat as primary model
            state.capturedModelUrl = url;
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
    function isModelUrl(url) {
        if (!url || typeof url !== 'string') return false;
        const lower = url.toLowerCase();
        return CONFIG.GLB_PATTERNS.some(p => lower.includes(p.toLowerCase()));
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
    // First 4 bytes of a valid binary .glb file, per the glTF 2.0 spec
    // (ASCII "glTF").
    const GLB_MAGIC = [0x67, 0x6C, 0x54, 0x46];

    function looksLikeValidGlb(arrayBuffer) {
        if (!arrayBuffer || arrayBuffer.byteLength < 12) return false;
        const bytes = new Uint8Array(arrayBuffer, 0, 4);
        return GLB_MAGIC.every((b, i) => bytes[i] === b);
    }

    function downloadFile(url, filename) {
        if (!url || !url.startsWith('http')) {
            alert('No valid URL to download.');
            return;
        }

        const name = filename || generateFilename(url);
        const expectsGlb = url.toLowerCase().includes('.glb');

        log('DL', `Starting download: ${url.substring(0, 80)}... → ${name}`);

        // Method 1: Use GM_xmlhttpRequest (cross-origin capable)
        GM_xmlhttpRequest({
            method: 'GET',
            url: url,
            headers: {
                'Referer': window.location.href,
                'Origin': window.location.origin
            },
            // ArrayBuffer transfers far more reliably than 'blob' across the
            // extension's internal message bridge for large binary payloads —
            // 'blob' responses are known to silently truncate/corrupt on some
            // Tampermonkey/Violentmonkey builds, which is what caused the
            // "downloads but won't open in any viewer" reports.
            responseType: 'arraybuffer',
            timeout: 120000, // 2 minute timeout for large files
            onload: function(resp) {
                if (resp.status === 200) {
                    try {
                        const buffer = resp.response;
                        const validGlb = looksLikeValidGlb(buffer);

                        if (expectsGlb && !validGlb) {
                            log('DL', 'Downloaded content failed GLB magic-byte check — likely not finalized yet');
                            showToast('Downloaded, but this doesn\'t look like a finished .glb file yet — the model may still be processing on Tripo3D\'s side. Try again in a bit.', 'error');
                        }

                        const blob = new Blob([buffer], { type: 'model/gltf-binary' });
                        const blobUrl = URL.createObjectURL(blob);
                        const a = document.createElement('a');
                        a.href = blobUrl;
                        a.download = name;
                        document.body.appendChild(a);
                        a.click();
                        document.body.removeChild(a);
                        setTimeout(() => URL.revokeObjectURL(blobUrl), 5000);
                        log('DL', `Download started successfully (${buffer.byteLength} bytes)`);

                        if (!expectsGlb || validGlb) {
                            showToast('Download started!', 'success');
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
            const pathPart = url.split('?')[0]; // Remove query string
            const filename = pathPart.split('/').pop(); // Get last path segment
            if (filename && filename.length > 3) return filename;
        } catch (e) {}
        return `tripo_model_${Date.now()}.glb`;
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
            .filter(h => isModelUrl(h.url))
            .slice(0, 10)
            .map((h, i) => {
                const shortUrl = h.url.length > 60 ? h.url.substring(0, 57) + '...' : h.url;
                const type = h.url.includes('pbr_model') ? 'PBR' :
                             h.url.includes('base_model') ? 'Base' :
                             h.url.includes('rendered_image') ? 'Image' : 'GLB';
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
                        ⬇ Download GLB
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
        log('INIT', 'Tripo3D Model Downloader V9.1 starting...');

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

})();

// Build the Tripo3D Model Downloader userscript.
//
// 1. Bundles src/converter.js (three.js + MeshoptDecoder + exporters) into a
//    single minified IIFE exposing the global `TripoConverter`.
// 2. Inlines that bundle into src/userscript.template.js at the
//    /*__CONVERTER_BUNDLE__*/ marker and writes the final .user.js.

import fs from 'node:fs';
import path from 'node:path';
import { execFileSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const root = path.dirname(fileURLToPath(import.meta.url));
process.chdir(root);

console.log('1/2  bundling converter…');
execFileSync(
  path.resolve('node_modules/esbuild/bin/esbuild'),
  [
    'src/converter.js',
    '--bundle',
    '--format=iife',
    '--global-name=TripoConverter',
    '--minify',
    '--legal-comments=none',
    '--platform=browser',
    '--target=es2020',
    '--outfile=dist/tripo-converter.js',
  ],
  { stdio: 'inherit' }
);

console.log('2/2  assembling userscript…');
const tpl = fs.readFileSync('src/userscript.template.js', 'utf8');
const bundle = fs.readFileSync('dist/tripo-converter.js', 'utf8');

const MARKER = '/*__CONVERTER_BUNDLE__*/';
if (!tpl.includes(MARKER)) {
  throw new Error(`marker ${MARKER} not found in template`);
}

// Function replacer avoids `$&`-style expansion in the (minified) bundle.
const out = tpl.replace(MARKER, () => bundle);

const outPath = 'dist/tripo3d-model-downloader.user.js';
fs.writeFileSync(outPath, out);
console.log(`done → ${outPath} (${(out.length / 1024).toFixed(0)} KB)`);

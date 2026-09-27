import fs from 'node:fs';
import { GLTFLoader } from 'three/addons/loaders/GLTFLoader.js';
import { MeshoptDecoder } from 'three/addons/libs/meshopt_decoder.module.js';
import { unzipSync, strFromU8 } from 'fflate';
import { exportTo3MF } from './src/vendor/three3mf.mjs';

globalThis.self = globalThis;
if (typeof globalThis.createImageBitmap === 'undefined') {
  globalThis.createImageBitmap = async () => ({ width: 1, height: 1, close() {} });
}

const buf = fs.readFileSync(process.argv[2]);
const ab = buf.buffer.slice(buf.byteOffset, buf.byteOffset + buf.byteLength);
const loader = new GLTFLoader();
loader.setMeshoptDecoder(MeshoptDecoder);
const gltf = await new Promise((res, rej) => loader.parse(ab, '', res, rej));

const blob = await exportTo3MF(gltf.scene);
const bytes = new Uint8Array(await blob.arrayBuffer());
fs.writeFileSync('/tmp/opencode/vendored.3mf', bytes);
console.log('3mf bytes', bytes.length);

const files = unzipSync(bytes);
console.log('zip entries:', Object.keys(files));
for (const [name, data] of Object.entries(files)) {
  console.log(' -', name, data.length, 'bytes');
}
const model = strFromU8(files['3D/3dmodel.model']);
console.log('model xml head:', model.slice(0, 200).replace(/\s+/g, ' '));
console.log('has vertex tags:', (model.match(/<vertex /g) || []).length);
console.log('has triangle tags:', (model.match(/<triangle /g) || []).length);

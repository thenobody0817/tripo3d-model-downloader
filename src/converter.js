import * as THREE from 'three';
import { GLTFLoader } from 'three/addons/loaders/GLTFLoader.js';
import { MeshoptDecoder } from 'three/addons/libs/meshopt_decoder.module.js';
import { STLExporter } from 'three/addons/exporters/STLExporter.js';
import { OBJExporter } from 'three/addons/exporters/OBJExporter.js';
import { GLTFExporter } from 'three/addons/exporters/GLTFExporter.js';
import { FBXExporter } from '@comfyorg/fbx-exporter-three';
import { exportTo3MF } from './vendor/three3mf.mjs';

async function parseGlb(arrayBuffer) {
  const loader = new GLTFLoader();
  loader.setMeshoptDecoder(MeshoptDecoder);
  return await new Promise((resolve, reject) => loader.parse(arrayBuffer, '', resolve, reject));
}

function sceneStats(scene) {
  let meshes = 0, triangles = 0;
  scene.traverse((o) => {
    if (o.isMesh) {
      meshes++;
      const g = o.geometry;
      triangles += (g.index ? g.index.count : g.attributes.position.count) / 3;
    }
  });
  return { meshes, triangles: Math.round(triangles) };
}

// formats: stl, obj, fbx, 3mf, gltf
export async function convertGlb(arrayBuffer, format, opts = {}) {
  const gltf = await parseGlb(arrayBuffer);
  const scene = gltf.scene;
  const fmt = String(format || '').toLowerCase();
  const base = opts.basename || 'model';

  if (fmt === 'stl') {
    const data = new STLExporter().parse(scene, { binary: true });
    return { blob: new Blob([data], { type: 'model/stl' }), filename: `${base}.stl`, stats: sceneStats(scene) };
  }

  if (fmt === 'obj') {
    const text = new OBJExporter().parse(scene);
    return { blob: new Blob([text], { type: 'text/plain' }), filename: `${base}.obj`, stats: sceneStats(scene) };
  }

  if (fmt === 'gltf') {
    // binary:false resolves to a plain JS object, not a string — stringify it.
    const data = await new GLTFExporter().parseAsync(scene, { binary: false });
    const text = JSON.stringify(data);
    return { blob: new Blob([text], { type: 'model/gltf+json' }), filename: `${base}.gltf`, stats: sceneStats(scene) };
  }

  if (fmt === 'fbx') {
    const exporter = new FBXExporter();
    const bytes = exporter.parseAsync
      ? await exporter.parseAsync(scene, opts.fbxOptions || {})
      : exporter.parseSync(scene, opts.fbxOptions || {});
    return { blob: new Blob([bytes], { type: 'application/octet-stream' }), filename: `${base}.fbx`, stats: sceneStats(scene) };
  }

  if (fmt === '3mf') {
    const blob = await exportTo3MF(scene, opts.printConfig || {});
    return { blob, filename: `${base}.3mf`, stats: sceneStats(scene) };
  }

  throw new Error(`Unsupported format: ${format}`);
}

export const FORMATS = ['stl', 'obj', 'fbx', '3mf', 'gltf', 'glb'];
export { parseGlb, sceneStats };

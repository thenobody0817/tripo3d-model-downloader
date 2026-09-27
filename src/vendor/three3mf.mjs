import { zipSync, strToU8 } from 'fflate';
import { Vector3, Color } from 'three';

const defaultPrintConfig = {
  printer_name: "Bambu Lab A1",
  filament: "Bambu PLA Basic @BBL A1",
  printableWidth: 256,
  printableDepth: 256,
  printableHeight: 256,
  printableArea: ["0x0", "256x0", "256x256", "0x256"],
  printerSettingsId: "Bambu Lab A1 0.4 nozzle",
  printSettingsId: "0.20mm Standard @BBL A1",
  compression: "standard",
  metadata: {
    Application: "BambuStudio-02.04.00.70",
    ApplicationTitle: "Exported 3D Model"
  }
};
const JSZipCompressionMap = { standard: "DEFLATE", none: "STORE" };
async function exportTo3MF(object, printJobConfig) {
  // Collect entries ourselves and zip with fflate at the end. JSZip 3 removed
  // the synchronous generate(), and its async generateAsync() relies on
  // setImmediate/MessageChannel which stalls inside a userscript sandbox.
  const files = {};
  const zip = { file: (name, content) => { files[name] = content; } };
  const printConfig = Object.assign({}, defaultPrintConfig, printJobConfig);
  const compression = JSZipCompressionMap[printConfig.compression];
  const components = [];
  const materials = [];
  const buildItems = [];
  const processMesh = (mesh) => {
    mesh.updateMatrixWorld(true);
    const geometry = mesh.geometry;
    const positionAttr = geometry.attributes.position;
    const indexAttr = geometry.index;
    let materialInfo = null;
    if (mesh.material) {
      const color = new Color();
      const mat = Array.isArray(mesh.material) ? mesh.material[0] : mesh.material;
      if (mat && "color" in mat && mat.color) {
        color.copy(mat.color);
      } else {
        color.set(8421504);
      }
      const existingMaterial = materials.find(
        (m) => m.color.r === color.r && m.color.g === color.g && m.color.b === color.b
      );
      if (existingMaterial) {
        materialInfo = existingMaterial;
      } else {
        const extruder = materials.length + 1;
        materialInfo = {
          id: materials.length + 1,
          color,
          name: mesh.name ? `${mesh.name}_material` : `material_${materials.length}`,
          extruder
        };
        materials.push(materialInfo);
      }
    }
    const componentId = components.length + 1;
    const component = {
      id: componentId,
      type: "mesh",
      vertices: [],
      triangles: [],
      material: materialInfo,
      name: mesh.name || `Mesh-${componentId}`,
      subComponents: [],
      uuid: generateUUID()
    };
    const vertexMap = /* @__PURE__ */ new Map();
    const processVertex = (vertexIndex) => {
      const vertex = new Vector3();
      vertex.fromBufferAttribute(positionAttr, vertexIndex);
      const vertexKey = `${vertex.x},${vertex.y},${vertex.z}`;
      if (!vertexMap.has(vertexKey)) {
        vertexMap.set(vertexKey, component.vertices.length);
        component.vertices.push({ x: vertex.x, y: vertex.y, z: vertex.z });
      }
      return vertexMap.get(vertexKey);
    };
    if (indexAttr) {
      for (let i = 0; i < indexAttr.count; i += 3) {
        component.triangles.push({
          v1: processVertex(indexAttr.getX(i)),
          v2: processVertex(indexAttr.getX(i + 1)),
          v3: processVertex(indexAttr.getX(i + 2))
        });
      }
    } else {
      for (let i = 0; i < positionAttr.count; i += 3) {
        component.triangles.push({
          v1: processVertex(i),
          v2: processVertex(i + 1),
          v3: processVertex(i + 2)
        });
      }
    }
    components.push(component);
    return componentId;
  };
  const processNode = (node) => {
    if (node.type === "Mesh") {
      return processMesh(node);
    } else if (node.type === "Group" || node.type === "Object3D" || node.type === "Scene") {
      const subComponents = [];
      node.updateMatrixWorld(true);
      node.children.forEach((child) => {
        const subId = processNode(child);
        if (subId !== -1) {
          const relMatrix = child.matrixWorld.clone().premultiply(node.matrixWorld.clone().invert());
          subComponents.push({ objectId: subId, transform: relMatrix });
        }
      });
      if (subComponents.length > 0) {
        const assemblyId = components.length + 1;
        components.push({
          id: assemblyId,
          type: "assembly",
          subComponents,
          name: node.name || `Group-${assemblyId}`,
          vertices: [],
          triangles: [],
          material: null,
          uuid: generateUUID()
        });
        return assemblyId;
      }
    }
    return -1;
  };
  const rootChildren = object.type === "Scene" ? object.children : [object];
  const allVerticesWorld = [];
  rootChildren.forEach((child) => {
    const childId = processNode(child);
    if (childId !== -1) {
      child.updateMatrix();
      const itemMatrix = child.matrix.clone();
      const targetComp = components.find((c) => c.id === childId);
      const getVerts = (c) => {
        if (c.type === "assembly") {
          return c.subComponents.flatMap((sc) => {
            const subComp = components.find((x) => x.id === sc.objectId);
            return getVerts(subComp).map((v) => v.clone().applyMatrix4(sc.transform));
          });
        }
        return c.vertices.map((v) => new Vector3(v.x, v.y, v.z));
      };
      getVerts(targetComp).forEach((vec) => {
        vec.applyMatrix4(itemMatrix);
        allVerticesWorld.push(vec);
      });
      buildItems.push({
        objectId: childId,
        transformMatrix: itemMatrix,
        uuid: generateUUID()
      });
    }
  });
  let min = { x: Infinity, y: Infinity, z: Infinity };
  let max = { x: -Infinity, y: -Infinity, z: -Infinity };
  if (allVerticesWorld.length > 0) {
    allVerticesWorld.forEach((v) => {
      min.x = Math.min(min.x, v.x);
      min.y = Math.min(min.y, v.y);
      min.z = Math.min(min.z, v.z);
      max.x = Math.max(max.x, v.x);
      max.y = Math.max(max.y, v.y);
      max.z = Math.max(max.z, v.z);
    });
  } else {
    min = { x: 0, y: 0, z: 0 };
    max = { x: 0, y: 0, z: 0 };
  }
  const modelCenter = { x: (min.x + max.x) / 2, y: (min.y + max.y) / 2, z: (min.z + max.z) / 2 };
  const bedCenter = { x: printConfig.printableWidth / 2, y: printConfig.printableDepth / 2, z: 0 };
  const shift = { x: bedCenter.x - modelCenter.x, y: bedCenter.y - modelCenter.y, z: bedCenter.z - min.z };
  const mainModelXml = createMainModelXML(components, buildItems, shift, printConfig);
  const modelSettingsXml = createModelSettingsXML(components, buildItems);
  const projectSettingsConfig = createProjectSettingsConfig(materials, printConfig);
  zip.file("_rels/.rels", relationshipsXML());
  zip.file("3D/3dmodel.model", mainModelXml);
  zip.file("Metadata/model_settings.config", modelSettingsXml);
  zip.file("Metadata/project_settings.config", projectSettingsConfig);
  zip.file("[Content_Types].xml", contentTypesXML());
  const entries = {};
  for (const [name, content] of Object.entries(files)) {
    entries[name] = typeof content === 'string' ? strToU8(content) : content;
  }
  const bytes = zipSync(entries, { level: compression === 'STORE' ? 0 : 6 });
  return new Blob([bytes], { type: "application/vnd.ms-package.3dmanufacturing-3dmodel+xml" });
}
function createMainModelXML(components, buildItems, shift, printConfig) {
  const metadata = [];
  const metadataConfig = printConfig.metadata;
  metadata.push(`<metadata name="CreationDate">${( new Date()).toISOString()}</metadata>`);
  for (const key in metadataConfig) {
    metadata.push(`<metadata name="${key}">${metadataConfig[key]}</metadata>`);
  }
  const resources = components.map((c) => {
    if (c.type === "assembly") {
      const comps = c.subComponents.map((sc) => {
        const e = sc.transform.elements;
        const tStr = `${e[0].toFixed(5)} ${e[1].toFixed(5)} ${e[2].toFixed(5)} ${e[4].toFixed(5)} ${e[5].toFixed(5)} ${e[6].toFixed(5)} ${e[8].toFixed(5)} ${e[9].toFixed(5)} ${e[10].toFixed(5)} ${e[12].toFixed(5)} ${e[13].toFixed(5)} ${e[14].toFixed(5)}`;
        return `<component objectid="${sc.objectId}" transform="${tStr}" />`;
      }).join("");
      return `<object id="${c.id}" type="model" name="${c.name}"><components>${comps}</components></object>`;
    } else {
      const vXml = c.vertices.map((v) => `<vertex x="${v.x.toFixed(5)}" y="${v.y.toFixed(5)}" z="${v.z.toFixed(5)}" />`).join(" ");
      const tXml = c.triangles.map((t) => `<triangle v1="${t.v1}" v2="${t.v2}" v3="${t.v3}" />`).join(" ");
      return `<object id="${c.id}" type="model" name="${c.name}"><mesh><vertices>${vXml}</vertices><triangles>${tXml}</triangles></mesh></object>`;
    }
  }).join("\n");
  const build = buildItems.map((item) => {
    const e = item.transformMatrix.elements;
    const tx = e[12] + shift.x;
    const ty = e[13] + shift.y;
    const tz = e[14] + shift.z;
    const tStr = `${e[0].toFixed(5)} ${e[1].toFixed(5)} ${e[2].toFixed(5)} ${e[4].toFixed(5)} ${e[5].toFixed(5)} ${e[6].toFixed(5)} ${e[8].toFixed(5)} ${e[9].toFixed(5)} ${e[10].toFixed(5)} ${tx.toFixed(5)} ${ty.toFixed(5)} ${tz.toFixed(5)}`;
    return `<item objectid="${item.objectId}" transform="${tStr}" printable="1" />`;
  }).join("\n");
  return `<?xml version="1.0" encoding="UTF-8"?>
<model unit="millimeter" xml:lang="en-US" xmlns="http://schemas.microsoft.com/3dmanufacturing/core/2015/02" xmlns:slic3rpe="http://schemas.slic3r.org/3mf/2017/06" xmlns:p="http://schemas.microsoft.com/3dmanufacturing/production/2015/06" requiredextensions="p">
    ${metadata.join("\n    ")}
    <resources>
${resources}
    </resources>
    <build>
${build}
    </build>
</model>`;
}
function createModelSettingsXML(components, buildItems) {
  let objectsXml = "";
  let instancesXml = "";
  let assembleXml = "";
  buildItems.forEach((item, index) => {
    const objId = item.objectId;
    const comp = components.find((c) => c.id === objId);
    const parts = [];
    const collect = (c) => {
      if (c.type === "mesh")
        parts.push(c);
      else
        c.subComponents.forEach((sc) => collect(components.find((x) => x.id === sc.objectId)));
    };
    collect(comp);
    const partsXml = parts.map((p) => {
      const extruder = p.material ? p.material.extruder : 1;
      return `    <part id="${p.id}" subtype="normal_part">
      <metadata key="name" value="${p.name}"/>
      <metadata key="extruder" value="${extruder}"/>
      <mesh_stat edges_fixed="0" degenerate_facets="0" facets_removed="0" facets_reversed="0" backwards_edges="0"/>
    </part>`;
    }).join("\n");
    objectsXml += `  <object id="${objId}">
    <metadata key="name" value="${comp.name}"/>
    <metadata key="extruder" value="1"/>
    <metadata key="thumbnail_file" value=""/>
${partsXml}
  </object>
`;
    instancesXml += `    <model_instance>
      <metadata key="object_id" value="${objId}"/>
      <metadata key="instance_id" value="0"/>
      <metadata key="identify_id" value="${index + 1}"/>
    </model_instance>
`;
    assembleXml += `    <assemble_item object_id="${objId}" instance_id="0" offset="0 0 0"/>
`;
  });
  return `<?xml version="1.0" encoding="UTF-8"?>
<config>
${objectsXml}
  <plate>
    <metadata key="plater_id" value="1"/>
    <metadata key="plater_name" value="plate-1"/>
${instancesXml}
  </plate>
  <assemble>
${assembleXml}
  </assemble>
</config>`;
}
function createProjectSettingsConfig(materials, printConfig) {
  const colors = materials.map((m) => {
    const hex = `#${m.color.getHexString()}`;
    return hex;
  });
  while (colors.length < 2) {
    colors.push("#FFFFFF");
  }
  const different_settings_to_system = new Set(printConfig.different_settings_to_system || []);
  const projectSettings = {
    printable_area: printConfig.printableArea,
    printable_height: printConfig.printableHeight.toString(),
    bed_exclude_area: [],
    filament_colour: colors,
    filament_settings_id: Array.from({ length: colors.length }).fill(printConfig.filament),
    filament_diameter: Array.from({ length: colors.length }).fill("1.75"),
    filament_is_support: Array.from({ length: colors.length }).fill("0"),
    printer_model: printConfig.printer_name,
    layer_height: "0.2",
    wall_loops: "2",
    sparse_infill_density: "15%",
    printer_settings_id: printConfig.printerSettingsId,
    printer_variant: "0.4",
    nozzle_diameter: ["0.4"],
    enable_support: "0",
    support_type: "normal(auto)",
    print_settings_id: printConfig.printSettingsId
  };
  if (printConfig.seam_position) {
    projectSettings.seam_position = printConfig.seam_position;
    different_settings_to_system.add("seam_position");
  }
  if (different_settings_to_system.size > 0) {
    projectSettings.different_settings_to_system = Array.from(different_settings_to_system);
  }
  return JSON.stringify(projectSettings);
}
function relationshipsXML() {
  return `<?xml version="1.0" encoding="UTF-8"?>
<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">
  <Relationship Id="rel-1" Target="/3D/3dmodel.model" Type="http://schemas.microsoft.com/3dmanufacturing/2013/01/3dmodel"/>
  <Relationship Id="rel-2" Target="/Metadata/model_settings.config" Type="http://schemas.microsoft.com/3dmanufacturing/2013/01/3dmodel"/>
  <Relationship Id="rel-3" Target="/Metadata/project_settings.config" Type="http://schemas.microsoft.com/3dmanufacturing/2013/01/3dmodel"/>
</Relationships>`;
}
function contentTypesXML() {
  return `<?xml version="1.0" encoding="UTF-8"?>
<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">
  <Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml" />
  <Default Extension="model" ContentType="application/vnd.ms-package.3dmanufacturing-3dmodel+xml" />
  <Default Extension="config" ContentType="application/vnd.ms-package.3dmanufacturing-3dmodel+xml" />
  <Default Extension="png" ContentType="image/png" />
  <Default Extension="gcode" ContentType="text/x.gcode"/>
</Types>`;
}
function generateUUID() {
  return "xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx".replace(/[xy]/g, (c) => {
    const r = Math.random() * 16 | 0;
    const v = c === "x" ? r : r & 3 | 8;
    return v.toString(16);
  });
}

export { defaultPrintConfig, exportTo3MF };

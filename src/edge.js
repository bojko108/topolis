/** @module */

import SpatialError from './SpatialError';
import { isSimple, relate, equals, azimuth, split, distance, intersects } from './utils';
import { insertNode, insertEdge, deleteEdge, insertFace, updateFaceTree, deleteFace, trigger } from './topo';
import { addFaceSplit } from './face';

/**
 * Edge definition
 *
 * @typedef {Object} Edge
 * @property {number} id Edge ID
 * @property {module:node~Node} start
 * @property {module:node~Node} end
 * @property {module:coordinate~Coordinate[]} coordinates Coordinates
 * @property {module:edge~Edge} nextLeft
 * @property {module:edge~Edge} nextRight
 * @property {module:face~Face} leftFace
 * @property {module:face~Face} rightFace
 * @property {number} minX Minimum X of bounds
 * @property {number} maxY Maximum Y of bounds
 * @property {number} minX Minimum X of bounds
 * @property {number} maxY Maximum Y of bounds
 */

console.debug = console.log;
console.debug = function() {};

/**
 * @param {module:edge~Edge} e
 * @param {boolean} d
 * @return {number}
 * @private
 */
export function sid(e, d) {
  return d ? e.id : -e.id;
}

/**
 * @param {module:edge~Edge} e
 * @return {string}
 * @private
 */
export function e2s(e) {
  const nl = sid(e.nextLeft, e.nextLeftDir);
  const nr = sid(e.nextRight, e.nextRightDir);
  return `${e.id}|${e.start.id}|${e.end.id}|${nl}|${nr}|${e.leftFace.id}|${e.rightFace.id}`;
}

export function getEdgeByPoint(topo, c, tol) {
  const result = topo.edgesTree.search({
    minX: c[0] - tol,
    minY: c[1] - tol,
    maxX: c[0] + tol,
    maxY: c[1] + tol
  });

  const candidates = result.filter(e => distance(c, e.coordinates) <= tol);

  // TODO: throw exception on more than one candidate?

  return candidates;
}

export function getEdgesByLine(topo, cs) {
  const xs = cs.map(c => c[0]);
  const ys = cs.map(c => c[1]);

  const bounds = {
    minX: Math.min(...xs),
    minY: Math.min(...ys),
    maxX: Math.max(...xs),
    maxY: Math.max(...ys)
  };

  const edges = topo.edgesTree.search(bounds).filter(e => intersects(cs, e.coordinates));

  return edges;
}

/**
 * Adds an isolated edge defined by geometry alinestring to a topology connecting two existing isolated nodes anode and anothernode and returns the edge id of the new edge.
 *
 * @param {module:topo~Topo} topo
 * @param {module:node~Node} start
 * @param {module:node~Node} end
 * @param {module:coordinate~Coordinate[]} coordinates
 * @return {module:edge~Edge}
 */
export function addIsoEdge(topo, start, end, coordinates) {
  const xs = coordinates.map(c => c[0]);
  const ys = coordinates.map(c => c[1]);

  const edge = {
    id: topo.edgesSeq,
    start,
    end,
    coordinates,
    nextLeft: { id: 0 },
    nextRight: { id: 0 },
    leftFace: { id: -1 },
    rightFace: { id: -1 },
    minX: Math.min(...xs),
    minY: Math.min(...ys),
    maxX: Math.max(...xs),
    maxY: Math.max(...ys)
  };

  if (start === end) {
    throw new SpatialError('start and end node cannot be the same as it would not construct an isolated edge');
  }

  if (!start.face || !end.face) {
    throw new SpatialError('not isolated node');
  }

  if (start.face !== end.face) {
    throw new SpatialError('nodes in different faces');
  }

  if (!equals(start.coordinate, coordinates[0])) {
    throw new SpatialError('start node not geometry start point');
  }

  if (!equals(end.coordinate, coordinates[coordinates.length - 1])) {
    throw new SpatialError('end node not geometry end point');
  }

  if (!isSimple(coordinates)) {
    throw new SpatialError('curve not simple');
  }

  checkEdgeCrossing(topo, start, end, edge);

  edge.leftFace = end.face;
  edge.nextLeft = edge;
  edge.nextLeftDir = false;
  edge.nextRight = edge;
  edge.nextRightDir = true;

  delete start.face;
  delete end.face;

  insertEdge(topo, edge);
  trigger(topo, 'addedge', edge);

  return edge;
}

function checkEdgeCrossing(topo, start, end, edge) {
  const check = (e1, e2) => {
    if (e1 === e2) {
      return;
    }
    const im = relate(e1.coordinates, e2.coordinates);
    if (im.matches('1FFF*FFF2')) {
      throw new SpatialError('coincident edge ' + e1.id);
    }
    if (im.matches('1********')) {
      throw new SpatialError('geometry intersects edge ' + e1.id);
    }
    if (im.matches('T********')) {
      throw new SpatialError('geometry crosses edge ' + e1.id);
    }
  };
  topo.edgesTree.search(edge).forEach(e => check(e, edge));
}

function getEdgeByNode(topo, node) {
  if (node.length) {
    return topo.edges.filter(e => node.some(n => n === e.start) || node.some(n => n === e.end));
  } else {
    return topo.edges.filter(e => e.start === node || e.end === node);
  }
}

function findAdjacentEdges(topo, node, data, other, edge) {
  data.nextCW = data.nextCCW = { id: 0 };
  data.cwFace = data.ccwFace = { id: -1 };

  let minaz, maxaz, azdif;

  if (other) {
    azdif = other.az - data.az;
    if (azdif < 0) azdif += 2 * Math.PI;
    minaz = maxaz = azdif;
    console.debug(`Other edge end has cwFace=${other.cwFace.id} and ccwFace=${other.ccwFace.id}`);
  } else {
    minaz = maxaz = -1;
  }

  console.debug(`Looking for edges incident to node ${node.id} and adjacent to azimuth ${data.az}`);

  const edges = getEdgeByNode(topo, node);

  console.debug(`getEdgeByNode returned ${edges.length} edges, minaz=${minaz}, maxaz=${maxaz}`);

  edges.forEach(e => {
    if (e === edge) {
      return;
    }

    if (e.coordinates.length < 2) {
      throw new Error(`corrupted topo: edge ${e.id} does not have two distinct points`);
    }

    if (e.start === node) {
      const p1 = e.coordinates[0];
      const p2 = e.coordinates[1];
      console.debug(`edge ${e.id} starts on node ${node.id}, edgeend is ${p1[0]},${p1[1]}-${p2[0]},${p2[1]}`);
      const az = azimuth(p1, p2);
      azdif = az - data.az;
      console.debug(`azimuth of edge ${e.id}: ${az} (diff: ${azdif})`);
      if (azdif < 0) azdif += 2 * Math.PI;
      if (minaz === -1) {
        minaz = maxaz = azdif;
        data.nextCW = data.nextCCW = e;
        data.nextCWDir = data.nextCCWDir = true;
        data.cwFace = e.leftFace;
        data.ccwFace = e.rightFace;
        console.debug(
          `new nextCW and nextCCW edge is ${e.id}, outgoing, with face_left ${e.leftFace.id} and face_right ${
            e.rightFace.id
          } (face_right is new ccwFace, face_left is new cwFace)`
        );
      } else {
        if (azdif < minaz) {
          data.nextCW = e;
          data.nextCWDir = true;
          data.cwFace = e.leftFace;
          console.debug(
            `new nextCW edge is ${e.id}, outgoing, with face_left ${e.leftFace.id} and face_right ${
              e.rightFace.id
            } (previous had minaz=${minaz}, face_left is new cwFace)`
          );
          minaz = azdif;
        } else if (azdif > maxaz) {
          data.nextCCW = e;
          data.nextCCWDir = true;
          data.ccwFace = e.rightFace;
          console.debug(
            `new nextCCW edge is ${e.id}, outgoing, with face_left ${e.leftFace.id} and face_right ${
              e.rightFace.id
            } (previous had maxaz=${maxaz}, face_right is new ccwFace)`
          );
          maxaz = azdif;
        }
      }
    }

    if (e.end === node) {
      const p1 = e.coordinates[e.coordinates.length - 1];
      const p2 = e.coordinates[e.coordinates.length - 2];
      console.debug(`edge ${e.id} ends on node ${node.id}, edgeend is ${p1[0]},${p1[1]}-${p2[0]},${p2[1]}`);
      const az = azimuth(p1, p2);
      azdif = az - data.az;
      console.debug(`azimuth of edge ${e.id}: ${az} (diff: ${azdif})`);
      if (azdif < 0) azdif += 2 * Math.PI;
      if (minaz === -1) {
        minaz = maxaz = azdif;
        data.nextCW = data.nextCCW = e;
        data.nextCWDir = data.nextCCWDir = false;
        data.cwFace = e.rightFace;
        data.ccwFace = e.leftFace;
        console.debug(
          `new nextCW and nextCCW edge is ${e.id}, incoming, with face_left ${e.leftFace.id} and face_right ${
            e.rightFace.id
          } (face_right is new cwFace, face_left is new ccwFace)`
        );
      } else {
        if (azdif < minaz) {
          data.nextCW = e;
          data.nextCWDir = false;
          data.cwFace = e.rightFace;
          console.debug(
            `new nextCW edge is ${e.id}, incoming, with face_left ${e.leftFace.id} and face_right ${
              e.rightFace.id
            } (previous had minaz=${minaz}, face_right is new cwFace)`
          );
          minaz = azdif;
        } else if (azdif > maxaz) {
          data.nextCCW = e;
          data.nextCCWDir = false;
          data.ccwFace = e.leftFace;
          console.debug(
            `new nextCCW edge is ${e.id}, outgoing, from start point, with face_left ${e.leftFace.id} and face_right ${
              e.rightFace.id
            } (previous had maxaz=${maxaz}, face_left is new ccwFace)`
          );
          maxaz = azdif;
        }
      }
    }
  });

  console.debug(
    `edges adjacent to azimuth ${data.az} (incident to node ${node.id}): CW:${sid(data.nextCW, data.nextCWDir)}(${minaz}) CCW:${sid(
      data.nextCCW,
      data.nextCCWDir
    )}(${maxaz})`
  );

  if (!edge && edges.length > 0 && data.cwFace !== data.ccwFace) {
    if (data.cwFace.id !== -1 && data.ccwFace.id !== -1) {
      throw new Error(
        `Corrupted topo: adjacent edges ${sid(data.nextCW, data.nextCWDir)} and ${sid(data.nextCCW, data.nextCCWDir)} bind different face (${
          data.cwFace.id
        } and ${data.ccwFace.id})`
      );
    }
  }

  return edges;
}

function addEdge(topo, start, end, coordinates, modFace) {
  console.debug('addEdge called');

  if (!isSimple(coordinates)) {
    throw new SpatialError('curve not simple');
  }

  const xs = coordinates.map(c => c[0]);
  const ys = coordinates.map(c => c[1]);

  const edge = {
    id: topo.edgesSeq,
    start,
    end,
    coordinates,
    nextLeft: { id: 0 },
    nextRight: { id: 0 },
    leftFace: { id: -1 },
    rightFace: { id: -1 },
    minX: Math.min(...xs),
    minY: Math.min(...ys),
    maxX: Math.max(...xs),
    maxY: Math.max(...ys)
  };

  // TODO: remove repeated points
  // TODO: check that we haave at least two points left

  const span = {
    cwFace: { id: -1 },
    ccwFace: { id: -1 },
    az: azimuth(coordinates[0], coordinates[1])
  };

  const epan = {
    cwFace: { id: -1 },
    ccwFace: { id: -1 },
    az: azimuth(coordinates[coordinates.length - 1], coordinates[coordinates.length - 2])
  };

  const nodes = start !== end ? [start, end] : [start];

  nodes.forEach(node => {
    if (node.face) {
      if (edge.leftFace.id === -1) {
        edge.leftFace = edge.rightFace = node.face;
      } else if (edge.leftFace !== node.face) {
        throw new SpatialError(`geometry crosses an edge (endnodes in faces ${edge.leftFace.id} and ${node.face.id})`);
      }
    }
  });

  if (!equals(start.coordinate, coordinates[0])) {
    throw new SpatialError('start node not geometry start point');
  }

  if (!equals(end.coordinate, coordinates[coordinates.length - 1])) {
    throw new SpatialError('end node not geometry end point');
  }

  checkEdgeCrossing(topo, start, end, edge);

  const isClosed = start === end;
  const foundStart = findAdjacentEdges(topo, start, span, isClosed ? epan : undefined);

  let prevLeft;
  let prevLeftDir;

  if (foundStart.length > 0) {
    span.wasIsolated = false;
    if (span.nextCW.id) {
      edge.nextRight = span.nextCW;
      edge.nextRightDir = span.nextCWDir;
    } else {
      edge.nextRight = edge;
      edge.nextRightDir = false;
    }
    if (span.nextCCW.id) {
      prevLeft = span.nextCCW;
      prevLeftDir = !span.nextCCWDir;
    } else {
      prevLeft = edge;
      prevLeftDir = true;
    }
    console.debug(
      `New edge ${edge.id} is connected on start node, next_right is ${sid(edge.nextRight, edge.nextRightDir)}, prev_left is ${sid(
        prevLeft,
        prevLeftDir
      )}`
    );
    if (edge.rightFace.id === -1) {
      edge.rightFace = span.cwFace;
    }
    if (edge.leftFace.id === -1) {
      edge.leftFace = span.ccwFace;
    }
  } else {
    span.wasIsolated = true;
    edge.nextRight = edge;
    edge.nextRightDir = !isClosed;
    prevLeft = edge;
    prevLeftDir = isClosed;
    console.debug(
      `New edge ${edge.id} is isolated on start node, next_right is ${sid(edge.nextRight, edge.nextRightDir)}, prev_left is ${sid(
        prevLeft,
        prevLeftDir
      )}`
    );
  }

  const foundEnd = findAdjacentEdges(topo, end, epan, isClosed ? span : undefined);

  let prevRight;
  let prevRightDir;

  if (foundEnd.length > 0) {
    epan.wasIsolated = false;
    if (epan.nextCW.id) {
      edge.nextLeft = epan.nextCW;
      edge.nextLeftDir = epan.nextCWDir;
    } else {
      edge.nextLeft = edge;
      edge.nextLeftDir = true;
    }
    if (epan.nextCCW.id) {
      prevRight = epan.nextCCW;
      prevRightDir = !epan.nextCCWDir;
    } else {
      prevRight = edge;
      prevRightDir = false;
    }
    console.debug(
      `New edge ${edge.id} is connected on end node, next_left is ${sid(edge.nextLeft, edge.nextLeftDir)}, prev_right is ${sid(
        prevRight,
        prevRightDir
      )}`
    );
    if (edge.rightFace.id === -1) {
      edge.rightFace = span.ccwFace;
    } else if (edge.rightFace !== epan.ccwFace) {
      throw new Error(`Side-location conflict: new edge starts in face ${edge.rightFace.id} and ends in face ${epan.ccwFace.id}`);
    }
    if (edge.leftFace.id === -1) {
      edge.leftFace = span.cwFace;
    } else if (edge.leftFace !== epan.cwFace) {
      throw new Error(`Side-location conflict: new edge starts in face ${edge.leftFace.id} and ends in face ${epan.cwFace.id}`);
    }
  } else {
    epan.wasIsolated = true;
    edge.nextLeft = edge;
    edge.nextLeftDir = isClosed;
    prevRight = edge;
    prevRightDir = !isClosed;
    console.debug(
      `New edge ${edge.id} is isolated on end node, next_left is ${sid(edge.nextLeft, edge.nextLeftDir)}, prev_right is ${sid(
        prevRight,
        prevRightDir
      )}`
    );
  }

  if (edge.leftFace !== edge.rightFace) {
    throw new Error(`Left(${edge.leftFace.id})/right(${edge.rightFace.id}) faces mismatch: invalid topology ?`);
  } else if (edge.leftFace.id === -1) {
    throw new Error('Could not derive edge face from linked primitives: invalid topo ?');
  }

  insertEdge(topo, edge);

  if (prevLeft !== edge) {
    if (prevLeftDir) {
      prevLeft.nextLeft = edge;
      prevLeft.nextLeftDir = true;
    } else {
      prevLeft.nextRight = edge;
      prevLeft.nextRightDir = true;
    }
  }

  if (prevRight !== edge) {
    if (prevRightDir) {
      prevRight.nextLeft = edge;
      prevRight.nextLeftDir = false;
    } else {
      prevRight.nextRight = edge;
      prevRight.nextRightDir = false;
    }
  }

  if (span.wasIsolated) {
    delete start.face;
  }
  if (epan.wasIsolated) {
    delete end.face;
  }

  if (!isClosed && (epan.wasIsolated || span.wasIsolated)) {
    trigger(topo, 'addedge', edge);
    return edge;
  }

  const oldFace = edge.leftFace;

  let newface1;

  if (!modFace) {
    newface1 = addFaceSplit(topo, edge, false, edge.leftFace, false);
    if (newface1 === 0) {
      console.debug('New edge does not split any face');
      trigger(topo, 'addedge', edge);
      return edge;
    }
  }

  let newface = addFaceSplit(topo, edge, true, edge.leftFace, false);

  if (modFace) {
    if (newface === 0) {
      console.debug('New edge does not split any face');
      trigger(topo, 'addedge', edge);
      return edge;
    }

    if (newface < 0) {
      newface = addFaceSplit(topo, edge, false, edge.leftFace, false);
      if (newface < 0) {
        trigger(topo, 'addedge', edge);
        return edge;
      }
    } else {
      addFaceSplit(topo, edge, false, edge.leftFace, true);
    }
  }

  trigger(topo, 'addedge', edge);

  if (oldFace !== topo.universe && !modFace) {
    deleteFace(topo, oldFace);
    trigger(topo, 'removeface', oldFace);
  }

  return edge;
}

/**
 * Add a new edge and, if in doing so it splits a face, delete the original face and replace it with two new faces.
 *
 * @param {module:topo~Topo} topo
 * @param {module:node~Node} start
 * @param {module:node~Node} end
 * @param {module:coordinate~Coordinate[]} coordinates
 * @return {module:edge~Edge}
 */
export function addEdgeNewFaces(topo, start, end, coordinates) {
  return addEdge(topo, start, end, coordinates, false);
}

/**
 * Add a new edge and, if in doing so it splits a face, modify the original face and add a new face.
 *
 * @param {module:topo~Topo} topo
 * @param {module:node~Node} start
 * @param {module:node~Node} end
 * @param {module:coordinate~Coordinate[]} coordinates
 * @return {module:edge~Edge}
 */
export function addEdgeModFace(topo, start, end, coordinates) {
  return addEdge(topo, start, end, coordinates, true);
}

function remEdge(topo, edge, modFace) {
  console.debug('Updating next_{right,left}_face of ring edges...');

  const { universe, edges, nodes, facesTree } = topo;

  const oldLeftFace = edge.leftFace;
  const oldRightFace = edge.rightFace;

  const edgeNodes = [];
  edgeNodes.push(edge.start);
  if (edge.end !== edge.start) {
    edgeNodes.push(edge.end);
  }
  const updEdge = getEdgeByNode(topo, edgeNodes);
  const updEdgeLeft = [];
  const updEdgeRight = [];
  let fnodeEdges = 0;
  let lnodeEdges = 0;

  updEdge.forEach(e => {
    if (e === edge) return;
    if (e.start === edge.start || e.end === edge.start) fnodeEdges++;
    if (e.start === edge.end || e.end === edge.end) lnodeEdges++;
    if (e.nextLeft === edge && !e.nextLeftDir) {
      updEdgeLeft.push({
        edge: e,
        nextLeft: edge.nextLeft !== edge || !edge.nextLeftDir ? edge.nextLeft : edge.nextRight,
        nextLeftDir: edge.nextLeft !== edge || !edge.nextLeftDir ? edge.nextLeftDir : edge.nextRightDir
      });
    } else if (e.nextLeft === edge && e.nextLeftDir) {
      updEdgeLeft.push({
        edge: e,
        nextLeft: edge.nextRight !== edge || edge.nextRightDir ? edge.nextRight : edge.nextLeft,
        nextLeftDir: edge.nextRight !== edge || edge.nextRightDir ? edge.nextRightDir : edge.nextLeftDir
      });
    }

    if (e.nextRight === edge && !e.nextRightDir) {
      updEdgeRight.push({
        edge: e,
        nextRight: edge.nextLeft !== edge || !edge.nextLeftDir ? edge.nextLeft : edge.nextRight,
        nextRightDir: edge.nextLeft !== edge || !edge.nextLeftDir ? edge.nextLefttDir : edge.nextRightDir
      });
    } else if (e.nextRight === edge && e.nextRightDir) {
      updEdgeRight.push({
        edge: e,
        nextRight: edge.nextRight !== edge || edge.nextRightDir ? edge.nextRight : edge.nextLeft,
        nextRightDir: edge.nextRight !== edge || edge.nextRightDir ? edge.nextRightDir : edge.nextLeftDir
      });
    }
  });

  updEdgeLeft.forEach(ue => {
    ue.edge.nextLeft = ue.nextLeft;
    ue.edge.nextLeftDir = ue.nextLeftDir;
  });

  updEdgeRight.forEach(ue => {
    ue.edge.nextRight = ue.nextRight;
    ue.edge.nextRightDir = ue.nextRightDir;
  });

  let floodface;
  let newface = { id: -1 };

  if (oldLeftFace === oldRightFace) {
    floodface = oldRightFace;
  } else {
    if (oldLeftFace === universe || oldRightFace === universe) {
      floodface = universe;
      console.debug('floodface is universe');
    } else {
      floodface = oldRightFace;
      console.debug('floodface is ' + floodface.id);
      // TODO: merge bboxes
      if (modFace) {
        newface = floodface;
      } else {
        insertFace(topo, newface);
        floodface = newface;
      }
    }

    if (oldLeftFace !== floodface) {
      console.debug(`Updating edges leftFace to ${floodface.id} where it was ${oldLeftFace.id}`);
      edges.filter(e => e.leftFace === oldLeftFace).forEach(e => (e.leftFace = floodface));
      edges.filter(e => e.rightFace === oldLeftFace).forEach(e => (e.rightFace = floodface));
      nodes.filter(n => n.face === oldLeftFace).forEach(n => (n.face = floodface));
    }

    if (oldRightFace !== floodface) {
      console.debug(`Updating edges rightFace to ${floodface.id} where it was ${oldRightFace.id}`);
      edges.filter(e => e.leftFace === oldRightFace).forEach(e => (e.leftFace = floodface));
      edges.filter(e => e.rightFace === oldRightFace).forEach(e => (e.rightFace = floodface));
      nodes.filter(n => n.face === oldRightFace).forEach(n => (n.face = floodface));
    }
  }

  deleteEdge(topo, edge);

  if (!fnodeEdges) edge.start.face = floodface;

  if (edge.end !== edge.start && !lnodeEdges) edge.end.face = floodface;

  const deletedFaces = [];
  if (oldLeftFace !== oldRightFace) {
    if (oldRightFace !== floodface) deletedFaces.push(oldRightFace);
    if (oldLeftFace !== floodface) deletedFaces.push(oldLeftFace);
  }

  newface = modFace ? floodface : newface;

  deletedFaces.forEach(f => {
    deleteFace(topo, f);
    trigger(topo, 'removeface', f);
  });

  trigger(topo, 'removeedge', edge);
  if (newface.id !== -1) {
    facesTree.remove(newface);
    updateFaceTree(topo, newface);
  }
  trigger(topo, 'addface', newface);

  return modFace ? floodface : newface;
}

export function remEdgeNewFace(topo, edge) {
  return remEdge(topo, edge, false);
}

export function remEdgeModFace(topo, edge) {
  return remEdge(topo, edge, true);
}

function healEdges(topo, e1, e2, modEdge) {
  return undefined;
}

export function modEdgeHeal(topo, e1, e2) {
  return healEdges(topo, e1, e2, true);
}

export function newEdgeHeal(topo, e1, e2) {
  return healEdges(topo, e1, e2, false);
}

export function modEdgeSplit(topo, edge, coordinate) {
  const { edges, edgesTree } = topo;

  const parts = split(edge.coordinates, coordinate);

  const splitCoordinate = parts[0][parts[0].length - 1];

  const node = {
    coordinate: splitCoordinate
  };

  insertNode(topo, node);

  const newedge1 = {
    start: node,
    end: edge.end,
    leftFace: edge.leftFace,
    rightFace: edge.rightFace
  };
  newedge1.nextLeft = edge.nextLeft === edge && !edge.nextLeftDir ? newedge1 : edge.nextLeft;
  newedge1.nextLeftDir = edge.nextLeft === edge && !edge.nextLeftDir ? false : edge.nextLeftDir;
  newedge1.nextRight = edge;
  newedge1.nextRightDir = false;
  newedge1.coordinates = parts[1];

  insertEdge(topo, newedge1);

  const oldEnd = edge.end;

  edge.coordinates = parts[0];
  edge.nextLeft = newedge1;
  edge.nextLeftDir = true;
  edge.end = node;
  edgesTree.remove(edge);
  const xs = edge.coordinates.map(c => c[0]);
  const ys = edge.coordinates.map(c => c[1]);
  edge.minX = Math.min(...xs);
  edge.minY = Math.min(...ys);
  edge.maxX = Math.max(...xs);
  edge.maxY = Math.max(...ys);
  edgesTree.insert(edge);

  edges
    .filter(e => e.nextRight === edge && !e.nextRightDir && e.start === oldEnd && e !== newedge1)
    .forEach(e => {
      e.nextRight = newedge1;
      e.nextRightDir = false;
    });

  edges
    .filter(e => e.nextLeft === edge && !e.nextLeftDir && e.end === oldEnd && e !== newedge1)
    .forEach(e => {
      e.nextLeft = newedge1;
      e.nextLeftDir = false;
    });

  trigger(topo, 'addnode', node);
  trigger(topo, 'addedge', newedge1);
  trigger(topo, 'modedge', edge);
  trigger(topo, 'splitedge', { origEdge: edge, newEdge: newedge1 });

  return node;
}

export function newEdgesSplit(topo, edge, coordinate, skipISOChecks) {
  return undefined;
}

SVG_SIZE = 400
SVG_STROKE = 0.5
R_INC = Math.PI / 8

###############################################################################

loadObject =  (url, store, cb, cbErr) ->
  req = new XMLHttpRequest()
  req.open('GET', url, true)

  req.onreadystatechange = () ->
    if req.readyState == 4
      if req.status == 200
        cb(store, req.responseText)
      else
        cbErr(url)

  req.send(null)

###############################################################################

parseVertex = (vertexString) ->
  split = vertexString.split(' ')
  [x, y, z] = split[1..3]
  {
    x: parseFloat(x)
    y: parseFloat(y)
    z: parseFloat(z)
  }

###############################################################################

parseFace = (faceString) ->
  split = faceString.split(' ')
  parseInt(i) - 1 for i in split[1..]

###############################################################################

Array::max = () -> 
  Math.max.apply(null, @)

Array::min = () -> 
  Math.min.apply(null, @)

getVertexRanges = (vertices) ->
  xs = for v in vertices
    v.x
  ys = for v in vertices
    v.y
  zs = for v in vertices
    v.z

  {
    x1: xs.min()
    x2: xs.max()

    y1: ys.min()
    y2: ys.max()

    z1: zs.min()
    z2: zs.max()
  }

###############################################################################

rescaleVertices = (vertices, size) ->
  r = getVertexRanges(vertices)

  rx = r.x2 - r.x1
  ry = r.y2 - r.y1
  rz = r.z2 - r.z1

  rm = Math.max(rx, ry, rz)

  for v in vertices
    {
      x: .05*size + .90*size * (rm - rx - 2*r.x1 + 2*v.x)/(2*rm)
      y: .05*size + .90*size * (rm - ry - 2*r.y1 + 2*v.y)/(2*rm)
      z: .95*size - .90*size * (rm - rz - 2*r.z1 + 2*v.z)/(2*rm)
    }

###############################################################################

orthoProj = (vertices) ->
  {
    xy: {x: v.x, y: v.y} for v in vertices
    xz: {x: v.x, y: v.z} for v in vertices
    yz: {x: v.y, y: v.z} for v in vertices
  }

###############################################################################

union = (a) ->
  seen = Object.create(null)
  out = []
  len = a.length
  j = 0
  for i in [0...len]
    item = a[i]
    if seen[item] isnt 1 then [seen[item], out[j++]] = [1, item]
  out

###############################################################################

class Line 
  p1: 0
  p2: 0

  constructor: (p1 = @p1, p2 = @p2) ->
    @p1 = p1
    @p2 = p2

  toString: () ->
    "(#{@p1.toString()}, #{@p2.toString()})"

###############################################################################

createMeshLines = (faces) ->
  lines = []

  for face in faces
    len = face.length
    for i in [0...len]
      v1 = Math.min(face[i], face[(i+1)%len])
      v2 = Math.max(face[i], face[(i+1)%len])
      lines.push(new Line(v1, v2))

  union(lines)

###############################################################################

createSVGLine = (p1, p2, stroke) ->
  line = document.createElementNS('http://www.w3.org/2000/svg', 'line')
  line.setAttribute('x1', p1.x)
  line.setAttribute('y1', p1.y)
  line.setAttribute('x2', p2.x)
  line.setAttribute('y2', p2.y)
  line.setAttribute('stroke-width', stroke)
  line.setAttribute('stroke', 'black')
  line

###############################################################################

callback = (obj, txt) -> 
  lines = txt.split('\n')
  for line in lines
    if line[0] == 'v'
      obj.vertices.push(parseVertex(line))
    if line[0] == 'f'
      obj.faces.push(parseFace(line))

  obj.vertices = rescaleVertices(obj.vertices, SVG_SIZE)
  op = orthoProj(obj.vertices)

  [svgXY, svgXZ, svgYZ, svgIP] = 
    for i in [1..4]
      svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg')
      svg.setAttribute('width', SVG_SIZE)
      svg.setAttribute('height', SVG_SIZE)
      svg.setAttribute('style', "border: 1px solid black;")
      svg
  
  obj.meshLines = createMeshLines(obj.faces)

  for line in obj.meshLines
    lineXY = createSVGLine(op.xy[line.p1], op.xy[line.p2], SVG_STROKE)
    lineXZ = createSVGLine(op.xz[line.p1], op.xz[line.p2], SVG_STROKE)
    lineYZ = createSVGLine(op.yz[line.p1], op.yz[line.p2], SVG_STROKE)
    ip1 = isometricProjection(obj.vertices[line.p1])
    ip2 = isometricProjection(obj.vertices[line.p2])
    ips1 = {x: ip1.x + SVG_SIZE/2, y: ip1.y - SVG_SIZE/3}
    ips2 = {x: ip2.x + SVG_SIZE/2, y: ip2.y - SVG_SIZE/3}
    lineIP = createSVGLine(ips1, ips2, SVG_STROKE)
    svgXY.appendChild(lineXY)
    svgXZ.appendChild(lineXZ)
    svgYZ.appendChild(lineYZ)
    svgIP.appendChild(lineIP)
    obj.svgLinesXY.push(lineXY)
    obj.svgLinesXZ.push(lineXZ)
    obj.svgLinesYZ.push(lineYZ)
    obj.svgLinesIP.push(lineIP)

  createLabel = (text) ->
    label = document.createElementNS('http://www.w3.org/2000/svg', 'text')
    label.setAttribute('x', 10)
    label.setAttribute('y', 38)
    label.setAttribute('fill', 'red')
    label.setAttribute('font-size', '28px')
    label.setAttribute('font-family', 'helvetica')
    label.innerHTML = text
    label

  svgXY.appendChild(createLabel('xy'))
  svgXZ.appendChild(createLabel('xz'))
  svgYZ.appendChild(createLabel('yz'))
  svgIP.appendChild(createLabel('isometric'))

  containerXY = document.getElementById('containerXY')
  containerXZ = document.getElementById('containerXZ')
  containerYZ = document.getElementById('containerYZ')
  containerIP = document.getElementById('containerIP')

  clear()
  containerXY.appendChild(svgXY)
  containerXZ.appendChild(svgXZ)
  containerYZ.appendChild(svgYZ)
  containerIP.appendChild(svgIP)

###############################################################################

rotate = (object3D, txy, txz, tyz) ->
  ctxy = Math.cos(txy)
  ctxz = Math.cos(txz)
  ctyz = Math.cos(tyz)
  stxy = Math.sin(txy)
  stxz = Math.sin(txz)
  styz = Math.sin(tyz)

  size = SVG_SIZE

  rotatedVertices = for v in object3D.vertices
    [x, y, z] = [v.x, v.y, v.z]
    s2x = size - 2*x
    s2y = size - 2*y
    s2z = size - 2*z
    {
      x: (-(ctxy*ctxz*s2x) + size + ctxz*s2y*stxy - s2z*stxz)/2.0
      y: (size - ctyz*s2x*stxy + ctxz*s2z*styz + s2y*stxy*stxz*styz - ctxy*(ctyz*s2y + s2x*stxz*styz))/2.0
      z: (-(ctxz*ctyz*s2z) + size + ctyz*(ctxy*s2x - s2y*stxy)*stxz - (ctxy*s2y + s2x*stxy)*styz)/2.0
    }

  for i in [0...object3D.meshLines.length]
    meshLine = object3D.meshLines[i]

    p1 = rotatedVertices[meshLine.p1]
    p2 = rotatedVertices[meshLine.p2]

    object3D.svgLinesXY[i].setAttribute('x1', p1.x)
    object3D.svgLinesXY[i].setAttribute('y1', p1.y)
    object3D.svgLinesXY[i].setAttribute('x2', p2.x)
    object3D.svgLinesXY[i].setAttribute('y2', p2.y)

    object3D.svgLinesXZ[i].setAttribute('x1', p1.x)
    object3D.svgLinesXZ[i].setAttribute('y1', p1.z)
    object3D.svgLinesXZ[i].setAttribute('x2', p2.x)
    object3D.svgLinesXZ[i].setAttribute('y2', p2.z)

    object3D.svgLinesYZ[i].setAttribute('x1', p1.y)
    object3D.svgLinesYZ[i].setAttribute('y1', p1.z)
    object3D.svgLinesYZ[i].setAttribute('x2', p2.y)
    object3D.svgLinesYZ[i].setAttribute('y2', p2.z)

    ip1 = isometricProjection(p1)
    ip2 = isometricProjection(p2)
    ips1 = {x: ip1.x + SVG_SIZE/2, y: ip1.y - SVG_SIZE/3}
    ips2 = {x: ip2.x + SVG_SIZE/2, y: ip2.y - SVG_SIZE/3}
    lineIP = createSVGLine(ips1, ips2, SVG_STROKE)

    object3D.svgLinesIP[i].setAttribute('x1', ips1.x)
    object3D.svgLinesIP[i].setAttribute('y1', ips1.y)
    object3D.svgLinesIP[i].setAttribute('x2', ips2.x)
    object3D.svgLinesIP[i].setAttribute('y2', ips2.y)

  object3D.vertices = rotatedVertices

###############################################################################

isometricProjection = (v) ->
  {
    x: (v.x - v.y) / Math.sqrt(2.0)
    y: (v.x + v.y + 2.0*v.z) / Math.sqrt(6.0)
  }

###############################################################################

transformationMatrix = (scale, translation, shear, rotation, perspective) ->
  [  sx,  sy,  sz ] = [       scale.x,       scale.y,       scale.z ]
  [  tx,  ty,  tz ] = [ translation.x, translation.y, translation.z ]
  [ syz, sxz, sxy ] = [       shear.x,       shear.y,       shear.z ]
  [  rx,  ry,  rz ] = [    rotation.x,    rotation.y,    rotation.z ]
  [  px,  py,  pz ] = [ perspective.x, perspective.y, perspective.z ]

  v1  = Math.cos(rx)
  v2  = Math.sin(rx)
  v3  = Math.cos(rz)
  v4  = Math.sin(ry)
  v5  = Math.sin(rz)
  v6  = Math.tan(sxy)
  v7  = Math.tan(syz)
  v8  = Math.cos(ry)
  v9  = -v4
  v10 = px * v6
  v11 = py + v10
  v12 = Math.tan(sxz)
  v13 = v1 * v3
  v14 = v2 * v3
  v15 = v1 * v5
  v16 = v2 * v5
  v17 = -v8
  v18 = px * v12
  v19 = v11 * v7
  v20 = pz + v18 + v19
  v21 = v6 * v7
  v22 = v12 + v21
  v23 = v13 * v4
  v24 = v1 * v8
  v25 = v15 * v9
  v26 = rx - syz
  v27 = v17 * v2
  v28 = v16 * v4
  v29 = v17 * v5
  v30 = v2 * v7
  v31 = v1 + v30
  v32 = v3 * v8
  v33 = v14 * v9
  v34 = 1 / Math.cos(syz)
  v35 = Math.sin(v26)
  v36 = v34 * v35

  m11 = sx*(v16*v22 + v22*v23 + v32 + v15*v6 + v33*v6)
  m12 = sy*(v14*v22 + v22*v25 + v29 + v13*v6 + v28*v6)
  m13 = sz*(v22*v24 + v27*v6 + v9)
  m14 = tx + tz*v22 + ty*v6

  m21 = sx*(v31*v5 + v3*v36*v9)
  m22 = sy*(v3*v31 + v4*v5*(v2 - v1*v7))
  m23 = sz*v17*v36
  m24 = ty + tz*v7

  m31 = sx*(v16 + v23)
  m32 = sy*(v14 + v25)
  m33 = sz*v24
  m34 = tz

  m41 = sx*(v16*v20 + v20*v23 + px*v32 + v11*(v15 + v33))
  m42 = sy*(v14*v20 + v20*v25 + v11*(v13 + v28) + px*v29)
  m43 = sz*(v20*v24 + v11*v27 + px*v9)
  m44 = 1 + px*tx + ty*v11 + tz*v20

  [[m11, m12, m13, m14]
   [m21, m22, m23, m24]
   [m31, m32, m33, m34]
   [m41, m42, m43, m44]]

###############################################################################

transformVertices = (object3D, scale, translation, shear, rotation, perspective) ->

  size = SVG_SIZE
  m = transformationMatrix(scale, translation, shear, rotation, perspective)

  transformed = for v in object3D.vertices
    {
      x: m[1][4] + m[1][1] * v.x + m[1][2] * v.y + m[1][3] * v.z
      y: m[2][4] + m[2][1] * v.x + m[2][2] * v.y + m[2][3] * v.z
    }

  for i in [0...object3D.meshLines.length]
    meshLine = object3D.meshLines[i]

    proj1 = transformed[meshLine.p1]
    proj2 = transformed[meshLine.p2]

    console.log proj1

    object3D.svgLinesIP[i].setAttribute('x1', proj1.x)
    object3D.svgLinesIP[i].setAttribute('y1', proj1.y)
    object3D.svgLinesIP[i].setAttribute('x2', proj2.x)
    object3D.svgLinesIP[i].setAttribute('y2', proj2.y)

###############################################################################

generalizedTransformation = (scale, translation, shear, rotation, perspective, point) ->
  [  sx,  sy,  sz ] = [       scale.x,       scale.y,       scale.z ]
  [  tx,  ty,  tz ] = [ translation.x, translation.y, translation.z ]
  [ syz, sxz, sxy ] = [       shear.x,       shear.y,       shear.z ]
  [  rx,  ry,  rz ] = [    rotation.x,    rotation.y,    rotation.z ]
  [  px,  py,  pz ] = [ perspective.x, perspective.y, perspective.z ]
  [   x,   y,   z ] = [       point.x,       point.y,       point.z ]

  v1  = Math.tan(sxy)
  v2  = Math.cos(rz)
  v3  = Math.sin(rz)
  v4  = px * v1
  v5  = py + v4
  v6  = Math.sin(ry)
  v7  = Math.cos(rx)
  v8  = Math.sin(rx)
  v9  = Math.tan(syz)
  v10 = Math.tan(sxz)
  v11 = -v6
  v12 = Math.cos(ry)
  v13 = px * v10
  v14 = v5 * v9
  v15 = pz + v13 + v14
  v16 = v15 * v7
  v17 = v2 * v8
  v18 = v3 * v8
  v19 = sx * x
  v20 = sy * y
  v21 = sz * z
  v22 = px * v12
  v23 = v11 * v3
  v24 = v2 * v6
  v25 = v5 * v7
  v26 = v11 * v17
  v27 = -v3
  v28 = v18 * v6
  v29 = -v8
  v30 = px * tx
  v31 = px * v11
  v32 = tz * v15
  v33 = v15 * v17
  v34 = v15 * v18
  v35 = v2 * v22
  v36 = v16 * v23
  v37 = v16 * v24
  v38 = v2 * v25
  v39 = v22 * v27
  v40 = v25 * v3
  v41 = ty * v5
  v42 = v26 * v5
  v43 = v34 + v35 + v37 + v40 + v42
  v44 = v19 * v43
  v45 = v28 * v5
  v46 = v33 + v36 + v38 + v39 + v45
  v47 = v12 * v21
  v48 = v21 * v31
  v49 = v20 * v46
  v50 = v16 * v47
  v51 = v29 * v47
  v52 = v5 * v51
  v53 = 1 / (1 + v30 + v32 + v41 + v44 + v48 + v49 + v50 + v52)
  v54 = v1 * v9
  v55 = v10 + v54
  v56 = v20 * v23
  v57 = v19 * v24
  xo  = v53*(tx + ty*v1 + tz*v55 + v20*(v12*v27 + v1*(v28 + v2*v7) + v55*(v17 + v23*v7)) + v19*(v12*v2 + v55*(v18 + v24*v7) + v1*(v26 + v3*v7)) + v21*(v11 + v12*(v10*v7 + v1*(v29 + v7*v9))))
  yo  = v53*(ty + tz*v9 + (v2*v20 + v19*v3)*(v7 + v8*v9) - (v47 + v56 + v57)*(1/Math.cos(syz)))*Math.sin(rx - syz)
  zo  = v53*(tz + v18*v19 + v17*v20 + v47*v7 + v56*v7 + v57*v7)
  {x: xo, y: yo, z: zo}

###############################################################################

clear = () ->
  cc = (cname) ->
    container = document.getElementById(cname)
    while container.hasChildNodes()
      container.removeChild(container.firstChild)

  cc('containerXY')
  cc('containerXZ')
  cc('containerYZ')
  cc('containerIP')
  

###############################################################################

err = (url) ->
  alert "failed to load #{url}"

###############################################################################

load = (object) ->
  object3D = 
    {
      vertices: []
      faces: []
      meshLines: []
      svgLinesXY: []
      svgLinesXZ: []
      svgLinesYZ: []
      svgLinesIP: []
    }
  loadObject("objects/#{object}.obj", object3D, callback, err)
  object3D

###############################################################################

class Viewer

  objectName = 'Cube'
  object3D   = null

  scale:       {x: 1, y: 1, z: 1}
  translation: {x: 0, y: 0, z: 0}
  shear:       {x: 0, y: 0, z: 0}
  rotation:    {x: 0, y: 0, z: 0}
  perspective: {x: 0, y: 0, z: 0}

  constructor: () ->
    @init()

  init: () =>
    SVG_SIZE = Math.min(window.innerWidth - 30, window.innerHeight - 175) / 2
    document.getElementById('imgTbl').width = 2 * SVG_SIZE
    console.log objectName
    object3D = load(objectName)
    transformVertices(object3D, @scale, @translation, @shear, @rotation, @perspective)

  reset: (preset) =>
    @scale       = {x: 1, y: 1, z: 1}
    @translation = {x: 0, y: 0, z: 0}
    @shear       = {x: 0, y: 0, z: 0}
    @rotation    = {x: 0, y: 0, z: 0}
    @perspective = {x: 0, y: 0, z: 0}
    
    if preset?

      switch preset

        when 'Isometric'
          @rotation.x = Math.asin(1 / Math.sqrt(3))
          @rotation.y = Math.PI / 4

        when 'Dimetric'
          @rotation.x = Math.PI / 16
          @rotation.y = Math.PI / 4

        when 'Trimetric'
          @rotation.x = Math.PI / 16
          @rotation.y = Math.PI / 5

        when 'Oblique'
          @shear.x = @shear.y = 0.5

        when 'Perspective1'
          @rotation.x = Math.PI / 16
          @rotation.y = Math.PI / 5
          @perspective.z = -0.25

        when 'Perspective2'
          @rotation.x = Math.PI / 16
          @rotation.y = Math.PI / 5
          @perspective.y = -0.125
          @perspective.z = -0.25

        when 'Perspective3'
          @rotation.x = Math.PI / 16
          @rotation.y = Math.PI / 5
          @perspective.z = -0.0625
          @perspective.y = -0.125
          @perspective.z = -0.25

    console.log object3D
    transformVertices(object3D, @scale, @translation, @shear, @rotation, @perspective)

###############################################################################

main = () ->
  # SVG_SIZE = Math.min(window.innerWidth - 30, window.innerHeight - 175)/2
  # document.getElementById('imgTbl').width = 2*SVG_SIZE
  # object3D = load('Cube')

  viewer = new Viewer()

  gui = new dat.GUI()

  document.getElementById('selector').addEventListener "change", (e) => 
      object3D = load(selector.value)

  document.getElementById('Isometric').addEventListener "click", (e) => 
      viewer.reset('Isometric')

  document.getElementById('rotateXY+').addEventListener "click", (e) => 
      rotate(object3D, -R_INC, 0, 0)
  
  document.getElementById('rotateXZ+').addEventListener "click", (e) => 
      rotate(object3D, 0, R_INC, 0)

  document.getElementById('rotateYZ+').addEventListener "click", (e) => 
      rotate(object3D, 0, 0, -R_INC)

  document.getElementById('rotateXY-').addEventListener "click", (e) => 
      rotate(object3D, R_INC, 0, 0)
  
  document.getElementById('rotateXZ-').addEventListener "click", (e) => 
      rotate(object3D, 0, -R_INC, 0)

  document.getElementById('rotateYZ-').addEventListener "click", (e) => 
      rotate(object3D, 0, 0, R_INC)
  # object3D = {vertices: [], faces: []}
  # loadObject('objects/Beethoven.obj', object3D, callback, err)

main()


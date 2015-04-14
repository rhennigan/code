SVG_SIZE = 400
SVG_STROKE = 0.0025
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

rescaleVertices = (vertices, size) ->
  r = getVertexRanges(vertices)
  m = {x: (r.x1+r.x2)/2, y: (r.y1+r.y2)/2, z: (r.z1+r.z2)/2}
  shifted = for v in vertices
    {x: v.x - m.x, y: v.y - m.y, z: v.z - m.z}
  
  rm = 0
  for v in vertices
    x = Math.abs(v.x)
    y = Math.abs(v.y)
    z = Math.abs(v.z)
    rm = Math.max(rm, x, y, z)

  for v in vertices
    {
      x: size * v.x / rm
      y: size * v.y / rm
      z: size * v.z / rm
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

svgShift = (p) ->
  0.3 * p + 0.5

###############################################################################

createSVGLine = (p1, p2, stroke) ->
  line = document.createElementNS('http://www.w3.org/2000/svg', 'line')
  line.setAttribute('x1', svgShift(p1.x))
  line.setAttribute('y1', 1-svgShift(p1.y))
  line.setAttribute('x2', svgShift(p2.x))
  line.setAttribute('y2', 1-svgShift(p2.y))
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

  obj.vertices = rescaleVertices(obj.vertices, 1)
  # console.log getVertexRanges(obj.vertices)
  op = orthoProj(obj.vertices)

  [svgXY, svgXZ, svgYZ, svgIP] = 
    for i in [1..4]
      svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg')
      svg.setAttribute('width', SVG_SIZE)
      svg.setAttribute('height', SVG_SIZE)
      svg.setAttribute('style', "border: 1px solid black;")
      svg.setAttribute('viewBox', "0 0 1 1")
      svg
  
  obj.meshLines = createMeshLines(obj.faces)

  for line in obj.meshLines
    lineXY = createSVGLine(op.xy[line.p1], op.xy[line.p2], SVG_STROKE)
    lineXZ = createSVGLine(op.xz[line.p1], op.xz[line.p2], SVG_STROKE)
    lineYZ = createSVGLine(op.yz[line.p1], op.yz[line.p2], SVG_STROKE)
    ip1 = isometricProjection(obj.vertices[line.p1])
    ip2 = isometricProjection(obj.vertices[line.p2])
    lineIP = createSVGLine(ip1, ip2, SVG_STROKE)
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
    label.setAttribute('x', 0.05)
    label.setAttribute('y', 0.075)
    label.setAttribute('fill', 'red')
    label.setAttribute('font-size', 0.05)
    label.setAttribute('font-family', 'helvetica')
    label.innerHTML = text
    label

  svgXY.appendChild(createLabel('xy'))
  svgXZ.appendChild(createLabel('xz'))
  svgYZ.appendChild(createLabel('yz'))
  svgIP.appendChild(createLabel('projection'))

  containerXY = document.getElementById('containerXY')
  containerXZ = document.getElementById('containerXZ')
  containerYZ = document.getElementById('containerYZ')
  containerIP = document.getElementById('containerIP')

  clear()
  containerXY.appendChild(svgXY)
  containerXZ.appendChild(svgXZ)
  containerYZ.appendChild(svgYZ)
  containerIP.appendChild(svgIP)

  x = -Math.PI + Math.atan(Math.sqrt(2))
  y = 0
  z = Math.PI / 4
  transformVertices(obj, {x:1, y:1, z:1}, 
                         {x:0, y:0, z:0},
                         {x:0, y:0, z:0},
                         {x:x, y:y, z:z},
                         {x:0, y:0, z:0})


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

  start = new Date().getTime();
  transformedVertices = 
    for v in object3D.vertices
      generalizedTransformation(scale, translation, shear, rotation, perspective, v)
  end = new Date().getTime();
  time = end - start;

  for i in [0...object3D.meshLines.length]
    meshLine = object3D.meshLines[i]

    ip1 = transformedVertices[meshLine.p1]
    ip2 = transformedVertices[meshLine.p2]

    object3D.svgLinesIP[i].setAttribute('x1', svgShift(ip1.x))
    object3D.svgLinesIP[i].setAttribute('y1', svgShift(ip1.y))
    object3D.svgLinesIP[i].setAttribute('x2', svgShift(ip2.x))
    object3D.svgLinesIP[i].setAttribute('y2', svgShift(ip2.y))

###############################################################################

generalizedTransformation = (scale, translation, shear, rotation, perspective, point) ->
  [  sx,  sy,  sz ] = [       scale.x,       scale.y,       scale.z ]
  [  tx,  ty,  tz ] = [ translation.x, translation.y, translation.z ]
  [ syz, sxz, sxy ] = [       shear.x,       shear.y,       shear.z ]
  [  rx,  ry,  rz ] = [    rotation.x,    rotation.y,    rotation.z ]
  [  px,  py,  pz ] = [ perspective.x, perspective.y, perspective.z ]
  [   x,   y,   z ] = [       point.x,       point.y,      -point.z ]

  v1  = Math.tan(sxy)
  v2  = Math.cos(rz)
  v3  = Math.sin(ry)
  v4  = Math.sin(rz)
  v5  = px * v1
  v6  = py + v5
  v7  = Math.cos(rx)
  v8  = Math.sin(rx)
  v9  = Math.tan(syz)
  v10 = Math.tan(sxz)
  v11 = -v3
  v12 = Math.cos(ry)
  v13 = px * v10
  v14 = v6 * v9
  v15 = pz + v13 + v14
  v16 = v15 * v7
  v17 = v2 * v8
  v18 = v4 * v8
  v19 = sx * x
  v20 = sy * y
  v21 = px * v12
  v22 = v2 * v3
  v23 = v11 * v4
  v24 = v6 * v7
  v25 = v1 * v9
  v26 = sz * z
  v27 = v11 * v17
  v28 = v10 + v25
  v29 = v18 * v3
  v30 = -v4
  v31 = -v8
  v32 = px * tx
  v33 = px * v11
  v34 = tz * v15
  v35 = v15 * v17
  v36 = v15 * v18
  v37 = v2 * v21
  v38 = v16 * v22
  v39 = v16 * v23
  v40 = v2 * v24
  v41 = v21 * v30
  v42 = v24 * v4
  v43 = ty * v6
  v44 = v27 * v6
  v45 = v36 + v37 + v38 + v42 + v44
  v46 = v19 * v45
  v47 = v29 * v6
  v48 = v35 + v39 + v40 + v41 + v47
  v49 = v12 * v26
  v50 = v26 * v33
  v51 = v20 * v48
  v52 = v16 * v49
  v53 = v31 * v49
  v54 = v53 * v6
  v55 = 1 / (1 + v32 + v34 + v43 + v46 + v50 + v51 + v52 + v54)

  xo  = v55*(tx + ty*v1 + tz*v28 + v20*(v17*v28 + v12*v30 + v23*v28*v7 + v1*(v29 + v2*v7)) + v26*(v11 + v12*(v1*v31 + (v10 + v25)*v7)) + v19*(v12*v2 + v28*(v18 + v22*v7) + v1*(v27 + v4*v7)))
  yo  = v55*(ty + tz*v9 + (v2*v20 + v19*v4)*(v7 + v8*v9) - (v19*v22 + v20*v23 + v49)*(1/Math.cos(syz))*Math.sin(rx - syz))
  {x: xo, y: yo}

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
    object3D = load(objectName)
    console.log object3D.vertices
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
          @rotation.x = -Math.PI + Math.atan(Math.sqrt(2))
          @rotation.z = Math.PI / 4

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

class Main

  gui: null
  objectName: 'Cube'
  object3D: null

  sx:  1.0,  sy:  1.0,  sz:  1.0,
  tx:  0.0,  ty:  0.0,  tz:  0.0,
  sxy: 0.0,  sxz: 0.0,  syz: 0.0,
  rx:  0.0,  ry:  0.0,  rz:  0.0,
  px:  0.0,  py:  0.0,  pz:  0.0,

  clearParameters: () ->
    @sx  = @sy  = @sz  = 1
    @tx  = @ty  = @tz  = 0
    @sxy = @sxz = @syz = 0
    @rx  = @ry  = @rz  = 0
    @px  = @py  = @pz  = 0

  straight: () -> 
    @clearParameters()
    @reset()

  isometric: () -> @reset('Isometric')
  dimetric: () -> @reset('Dimetric')
  trimetric: () -> @reset('Trimetric')
  oblique: () -> @reset('Oblique')
  perspective1: () -> @reset('Perspective1')
  perspective2: () -> @reset('Perspective2')
  perspective3: () -> @reset('Perspective3')

  constructor: () ->
    @initSVG()
    @initGUI()

  initSVG: =>
    SVG_SIZE = Math.min(window.innerWidth - 30, window.innerHeight - 175)/2
    document.getElementById('imgTbl').width = 2*SVG_SIZE
    console.log @objectName
    @object3D = load(@objectName)
    @reset('Isometric')

    #@t.isometric = () -> @reset('Isometric')

    # attachHandler = (name) =>
    #   document.getElementById(name).addEventListener "click", (e) =>
    #     @reset(name)

    # attachHandler('Isometric')
    # attachHandler('Dimetric')
    # attachHandler('Trimetric')
    # attachHandler('Oblique')
    # attachHandler('Perspective1')
    # attachHandler('Perspective2')
    # attachHandler('Perspective3')

    document.getElementById('selector').addEventListener "change", (e) => 
      @object3D = load(selector.value)
      @reset('Isometric')

  initGUI: ->
    @gui = new dat.GUI()

    slider = (f, name, low, high) =>
      control = f.add(@, name, low, high).step(0.001)
      control.listen()
      control.onChange((value) => @reset())

    ftr = @gui.addFolder('transformations')

    fs = ftr.addFolder('scale')
    slider(fs, 'sx', -5.0, 5.0)
    slider(fs, 'sy', -5.0, 5.0)
    slider(fs, 'sz', -5.0, 5.0)
    # fs.open()

    ft = ftr.addFolder('translation')
    slider(ft, 'tx', -2.0, 2.0)
    slider(ft, 'ty', -2.0, 2.0)
    slider(ft, 'tz', -2.0, 2.0)
    # ft.open()

    fsh = ftr.addFolder('shear')
    slider(fsh, 'sxy', -1.0, 1.0)
    slider(fsh, 'sxz', -1.0, 1.0)
    slider(fsh, 'syz', -1.0, 1.0)
    # fsh.open()

    fr = ftr.addFolder('rotation')
    slider(fr, 'rx', -2*Math.PI, 2*Math.PI)
    slider(fr, 'ry', -2*Math.PI, 2*Math.PI)
    slider(fr, 'rz', -2*Math.PI, 2*Math.PI)
    # fr.open()

    fp = ftr.addFolder('perspective')
    slider(fp, 'px', -0.3, 0.3)
    slider(fp, 'py', -0.3, 0.3)
    slider(fp, 'pz', -0.3, 0.3)
    # fp.open()

    ftr.open()

    fpr = @gui.addFolder('presets')
    fpr.add(@, 'straight')
    fpr.add(@, 'isometric')
    fpr.add(@, 'dimetric')
    fpr.add(@, 'trimetric')
    fpr.add(@, 'oblique')
    fpr.add(@, 'perspective1')
    fpr.add(@, 'perspective2')
    fpr.add(@, 'perspective3')

    fpr.open()

  reset: (preset) ->

    if preset?

      @clearParameters()

      switch preset

        when 'Isometric'
          @rx = -Math.PI + Math.atan(Math.sqrt(2))
          @rz = Math.PI / 4

        when 'Dimetric'
          @rx = -Math.PI + Math.atan(Math.sqrt(2)) + 0.4
          @rz = Math.PI / 4

        when 'Trimetric'
          @rx = -Math.PI + Math.atan(Math.sqrt(2)) + 0.4
          @rz = Math.PI / 4 + 0.2

        when 'Oblique'
          @syz = @sxz = 0.5

        when 'Perspective1'
          @rx = Math.PI / 16
          @ry = Math.PI / 5
          @pz = 0.25

        when 'Perspective2'
          @rx = Math.PI / 16
          @ry = Math.PI / 5
          @py = 0.125
          @pz = 0.25

        when 'Perspective3'
          @rx = Math.PI / 16
          @ry = Math.PI / 5
          @px = 0.0625
          @py = 0.125
          @pz = 0.25
    
    transformVertices(@object3D, {x:@sx , y:@sy , z:@sz }, 
                                 {x:@tx , y:@ty , z:@tz },
                                 {x:@syz, y:@sxz, z:@sxy},
                                 {x:@rx , y:@ry , z:@rz },
                                 {x:@px , y:@py , z:@pz })

prog = new Main()
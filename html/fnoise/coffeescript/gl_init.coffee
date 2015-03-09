PhiloGL.unpack()

class Viewer
  canvas = document.getElementById('fnCanvas')
  canvas.width = window.innerWidth
  canvas.height = window.innerHeight-5
  aspect = canvas.width / canvas.height
  frameTimes = [0, 0, 0, 0, 0]
  frameLast = 0
  frameIndex = 0
  p = Date.now() / 1000000000

  turbulence: 0.02
  tfrequency: 1.0
  persistence: 2.0
  lacunarity: 2.0
  speed: 1.0
  flip: false
  hint: 'click and drag to move'

  center = {x: 0.0, y: 0.0}
  mouseDragging = false
  dragStart = {x: 0, y: 0}
  dragCurrent = {x: 0, y: 0}

  constructor: () ->
  
  if PhiloGL.hasWebGL() is not yes
    alert("Your browser does not support WebGL")

  load: () =>
    PhiloGL('fnCanvas', 
      program: [{
        id: 'fnoise',
        from: 'uris',
        path: './'
        vs: 'vertex.glsl',
        fs: 'fragment.glsl'
      }]

      onError: (e) => 
        console.log(e)

      onLoad: (app) => 
        time = Date.now()
        # document.getElementById('turbulenceTxt').value = @turbulence
        # document.getElementById('tfrequencyTxt').value = @tfrequency
        # document.getElementById('persistenceTxt').value = @persistence
        # document.getElementById('lacunarityTxt').value = @lacunarity
        # document.getElementById('speedTxt').value = @speed
        # document.getElementById('flip').value = @flip
        
        draw = () =>
          canvas.width = window.innerWidth-5
          canvas.height = window.innerHeight-5
          aspect = canvas.width / canvas.height
          # p = speed * ((Date.now()-1425166257376) / 100000)
          p += @speed * 0.0002
          # tmp = Date.now()
          # frameTimes[++frameIndex % 5] = 1000 / (tmp - frameLast)
          # frameLast = tmp
          # avgFPS = 0
          # avgFPS += ft for ft in frameTimes
          # avgFPS /= 5.0
          # document.getElementById('fpsTxt').value = Math.round(avgFPS) if frameIndex % 5 is 0

          Media.Image.postProcess(
            width: canvas.width,
            height: canvas.height,
            toScreen: true,
            aspectRatio: 1,
            program: 'fnoise',
            uniforms: {
              p: p
              aspect: aspect
              turbulence: @turbulence
              tfrequency: @tfrequency
              persistence: @persistence
              lacunarity: @lacunarity
              dX: aspect * (center.x + dragStart.x - dragCurrent.x) / canvas.width
              dY: (center.y + dragCurrent.y - dragStart.y) / canvas.height
              flip: @flip
            }
          )

          Fx.requestAnimationFrame(draw)
          # setTimeout((() -> Fx.requestAnimationFrame(draw)), 1000/60)

        draw()
    )

    # btnPlusTurb = document.getElementById('turbulence+')
    # btnPlusTurb.addEventListener "click", (e) => 
    #     @turbulence *= 1.1
    #     document.getElementById('turbulenceTxt').value = @turbulence
    #     console.log @turbulence

    # btnSubTurb = document.getElementById('turbulence-')
    # btnSubTurb.addEventListener "click", (e) => 
    #     @turbulence /= 1.1
    #     document.getElementById('turbulenceTxt').value = @turbulence
    #     console.log @turbulence

    # btnPlusTF = document.getElementById('tfrequency+')
    # btnPlusTF.addEventListener "click", (e) => 
    #     @tfrequency *= 1.1
    #     document.getElementById('tfrequencyTxt').value = @tfrequency
    #     console.log @tfrequency

    # btnSubTF = document.getElementById('tfrequency-')
    # btnSubTF.addEventListener "click", (e) => 
    #     @tfrequency /= 1.1
    #     document.getElementById('tfrequencyTxt').value = @tfrequency
    #     console.log @tfrequency

    # btnPlusPers = document.getElementById('persistence+')
    # btnPlusPers.addEventListener "click", (e) => 
    #     persistence = if persistence >= 5.0 then 5.0 else persistence + 0.1
    #     document.getElementById('persistenceTxt').value = persistence
    #     console.log persistence

    # btnSubPers = document.getElementById('persistence-')
    # btnSubPers.addEventListener "click", (e) => 
    #     persistence = if persistence <= 0.0 then 0.0 else persistence - 0.1
    #     document.getElementById('persistenceTxt').value = persistence
    #     console.log persistence

    # btnPlusLac = document.getElementById('lacunarity+')
    # btnPlusLac.addEventListener "click", (e) => 
    #     lacunarity = if lacunarity >= 5.0 then 5.0 else lacunarity + 0.1
    #     document.getElementById('lacunarityTxt').value = lacunarity
    #     console.log lacunarity

    # btnPlusLac = document.getElementById('lacunarity-')
    # btnPlusLac.addEventListener "click", (e) => 
    #     lacunarity = if lacunarity <= 0.0 then 0.0 else lacunarity - 0.1
    #     document.getElementById('lacunarityTxt').value = lacunarity
    #     console.log lacunarity

    # btnPlusSpd = document.getElementById('speed+')
    # btnPlusSpd.addEventListener "click", (e) => 
    #     speed *= 1.1
    #     document.getElementById('speedTxt').value = speed
    #     console.log speed
    #     console.log p

    # btnPlusSpd = document.getElementById('speed-')
    # btnPlusSpd.addEventListener "click", (e) => 
    #     speed /= 1.1
    #     document.getElementById('speedTxt').value = speed
    #     console.log speed
    #     console.log p

    # document.getElementById('flip').addEventListener "click", (e) =>
    #     flip = $("#flip").is(':checked')

    getMousePos = (event) => 
      rect = canvas.getBoundingClientRect()
      x: event.clientX - rect.left
      y: event.clientY - rect.top

    canvas.addEventListener "mousedown", (e) =>
      dragStart = dragCurrent = getMousePos(e)
      mouseDragging = true

    canvas.addEventListener "mousemove", (e) =>
      if mouseDragging
        dragCurrent = getMousePos(e)

    canvas.addEventListener "mouseup", (e) =>
      mouseDragging = false
      center.x = center.x + dragStart.x - dragCurrent.x
      center.y = center.y + dragCurrent.y - dragStart.y
      dragStart = dragCurrent = {x: 0.0, y: 0.0}

viewer = new Viewer()
viewer.load()

gui = new dat.GUI({autoPlace: false})
document.getElementById('container').appendChild(gui.domElement)

gui.add(viewer, 'turbulence', 0.0, 0.2)
gui.add(viewer, 'tfrequency', 0.0, 4.0)
gui.add(viewer, 'persistence', 1.0, 5.0)
gui.add(viewer, 'lacunarity', 0.0, 5.0)
gui.add(viewer, 'speed').min(0)
gui.add(viewer, 'flip')

gui.close()
gui.width = 300

console.log gui
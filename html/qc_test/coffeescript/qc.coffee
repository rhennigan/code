PhiloGL.unpack()

load = () ->
  canvas = document.getElementById('qcCanvas')
  order = 5
  phaseS = 1.0
  aspect = canvas.width / canvas.height
  frameTimes = [0, 0, 0, 0, 0]
  frameLast = 0
  frameIndex = 0
  
  if PhiloGL.hasWebGL() is not yes
    alert("Your browser does not support WebGL")

  PhiloGL('qcCanvas', 
    program: [{
      id: 'quasicrystals',
      from: 'ids',
      vs: 'shader-vs',
      fs: 'shader-fs'
    }]

    onError: (e) => 
      console.log(e)

    onLoad: (app) -> 
      time = Date.now()
      
      draw = () ->
        p = phaseS * ((Date.now() - time) / 80000)
        tmp = Date.now()
        frameTimes[++frameIndex % 5] = 1000 / (tmp - frameLast)
        frameLast = tmp
        avgFPS = 0
        avgFPS += ft for ft in frameTimes
        avgFPS /= 5.0
        document.getElementById('fpsTxt').value = Math.round(avgFPS) if frameIndex % 5 is 0

        Media.Image.postProcess(
          width: canvas.width,
          height: canvas.height,
          toScreen: true,
          aspectRatio: 1,
          program: 'quasicrystals',
          uniforms: {
            p: p
            order: order
            aspect: aspect
          }
        )

        Fx.requestAnimationFrame(draw)
        # setTimeout((() -> Fx.requestAnimationFrame(draw)), 1000/60)

      draw()
  )

  btnPlus = document.getElementById('order+')
  btnPlus.addEventListener "click", (e) => 
      order = if order >= 30 then 30 else order + 1
      document.getElementById('orderTxt').value = order
      console.log order

  btnSub = document.getElementById('order-')
  btnSub.addEventListener "click", (e) => 
      order = if order <=  1 then  0 else order - 1
      document.getElementById('orderTxt').value = order
      console.log order

  btnPlus = document.getElementById('phase+')
  btnPlus.addEventListener "click", (e) => 
      phaseS *= 1.2
      document.getElementById('phaseTxt').value = phaseS
      console.log phaseS

  btnSub = document.getElementById('phase-')
  btnSub.addEventListener "click", (e) => 
      phaseS /= 1.2
      document.getElementById('phaseTxt').value = phaseS
      console.log phaseS

load()
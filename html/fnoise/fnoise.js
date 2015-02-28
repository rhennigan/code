// Generated by CoffeeScript 1.9.1
(function() {
  var IO, cb, err, fragmentShader, load, vertexShader;

  IO = (function() {
    function IO() {}

    return IO;

  })();

  IO.prototype.load = function(url, store, cb, cbErr) {
    var req;
    req = new XMLHttpRequest();
    req.open('GET', url, true);
    req.onreadystatechange = function() {
      if (req.readyState === 4) {
        if (req.status === 200) {
          return cb(store, req.responseText);
        } else {
          return cbErr(url);
        }
      }
    };
    return req.send(null);
  };

  cb = function(sh, txt) {
    sh.text(txt);
    return console.log(sh);
  };

  err = function(url) {
    return alert("failed to load " + url);
  };

  vertexShader = {
    text: null
  };

  fragmentShader = {
    text: null
  };

  IO.prototype.load('vertex.glsl', $("#shader-vs"), cb, err);

  IO.prototype.load('fragment.glsl', $("#shader-fs"), cb, err);

  PhiloGL.unpack();

  load = function() {
    var aspect, btnPlusLac, btnPlusPers, btnPlusTurb, btnSubPers, btnSubTurb, canvas, frameIndex, frameLast, frameTimes, lacunarity, persistence, turbulence;
    canvas = document.getElementById('fnCanvas');
    aspect = canvas.width / canvas.height;
    frameTimes = [0, 0, 0, 0, 0];
    frameLast = 0;
    frameIndex = 0;
    turbulence = 0.03;
    persistence = 2.4;
    lacunarity = 1.8;
    if (PhiloGL.hasWebGL() === !true) {
      alert("Your browser does not support WebGL");
    }
    PhiloGL('fnCanvas', {
      program: [
        {
          id: 'fnoise',
          from: 'uris',
          path: './',
          vs: 'vertex.glsl',
          fs: 'fragment.glsl'
        }
      ],
      onError: (function(_this) {
        return function(e) {
          return console.log(e);
        };
      })(this),
      onLoad: function(app) {
        var draw, time;
        time = Date.now();
        console.log(time);
        draw = function() {
          var avgFPS, ft, i, len, p, tmp;
          p = (Date.now() - 1425166257376) / 20000;
          tmp = Date.now();
          frameTimes[++frameIndex % 5] = 1000 / (tmp - frameLast);
          frameLast = tmp;
          avgFPS = 0;
          for (i = 0, len = frameTimes.length; i < len; i++) {
            ft = frameTimes[i];
            avgFPS += ft;
          }
          avgFPS /= 5.0;
          if (frameIndex % 5 === 0) {
            document.getElementById('fpsTxt').value = Math.round(avgFPS);
          }
          Media.Image.postProcess({
            width: canvas.width,
            height: canvas.height,
            toScreen: true,
            aspectRatio: 1,
            program: 'fnoise',
            uniforms: {
              p: p,
              aspect: aspect,
              turbulence: turbulence,
              persistence: persistence,
              lacunarity: lacunarity
            }
          });
          return Fx.requestAnimationFrame(draw);
        };
        return draw();
      }
    });
    btnPlusTurb = document.getElementById('turbulence+');
    btnPlusTurb.addEventListener("click", (function(_this) {
      return function(e) {
        turbulence = turbulence >= 1.0 ? 1.0 : turbulence + 0.001;
        document.getElementById('turbulenceTxt').value = turbulence;
        return console.log(turbulence);
      };
    })(this));
    btnSubTurb = document.getElementById('turbulence-');
    btnSubTurb.addEventListener("click", (function(_this) {
      return function(e) {
        turbulence = turbulence <= 0.0 ? 0.0 : turbulence - 0.001;
        document.getElementById('turbulenceTxt').value = turbulence;
        return console.log(turbulence);
      };
    })(this));
    btnPlusPers = document.getElementById('persistence+');
    btnPlusPers.addEventListener("click", (function(_this) {
      return function(e) {
        persistence = persistence >= 5.0 ? 5.0 : persistence + 0.1;
        document.getElementById('persistenceTxt').value = persistence;
        return console.log(persistence);
      };
    })(this));
    btnSubPers = document.getElementById('persistence-');
    btnSubPers.addEventListener("click", (function(_this) {
      return function(e) {
        persistence = persistence <= 0.0 ? 0.0 : persistence - 0.1;
        document.getElementById('persistenceTxt').value = persistence;
        return console.log(persistence);
      };
    })(this));
    btnPlusLac = document.getElementById('lacunarity+');
    btnPlusLac.addEventListener("click", (function(_this) {
      return function(e) {
        lacunarity = lacunarity >= 5.0 ? 5.0 : lacunarity + 0.1;
        document.getElementById('lacunarityTxt').value = lacunarity;
        return console.log(lacunarity);
      };
    })(this));
    btnPlusLac = document.getElementById('lacunarity-');
    return btnPlusLac.addEventListener("click", (function(_this) {
      return function(e) {
        lacunarity = lacunarity <= 0.0 ? 0.0 : lacunarity - 0.1;
        document.getElementById('lacunarityTxt').value = lacunarity;
        return console.log(lacunarity);
      };
    })(this));
  };

  load();

}).call(this);

//# sourceMappingURL=fnoise.js.map

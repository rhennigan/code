class IO

  load: (url, store, cb, cbErr) ->
    req = new XMLHttpRequest()
    req.open('GET', url, true)

    req.onreadystatechange = () ->
      if req.readyState == 4
        if req.status == 200
          cb(store, req.responseText)
        else
          cbErr(url)

    req.send(null)

callback = (obj, txt) -> 
  lines = txt.split('\n')
  console.log obj
  console.log objectText

err = (url) ->
  alert "failed to load #{url}"

objectText = {text: null}

IO::load('objects/SpaceShuttle.obj', objectText, callback, err)

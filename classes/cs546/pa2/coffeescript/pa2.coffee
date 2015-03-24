class IO

  load: (url, dest, callback, callbackError) ->
    req = new XMLHttpRequest()
    req.open('GET', url, true)

    req.onreadystatechange = () ->
      if req.readyState == 4
        if req.status == 200
          cb(store, req.responseText)
        else
          cbErr(url)

    req.send(null)
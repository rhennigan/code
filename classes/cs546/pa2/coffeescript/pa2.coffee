class IO
  container: null

  load: (url, callback, callbackError) ->
    req = new XMLHttpRequest()
    req.open('GET', url, true)

    req.onreadystatechange = () ->
      if req.readyState == 4
        if req.status == 200
          callback(req.responseText)
        else
          callbackError(url)

    req.send(null)
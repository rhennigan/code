module Terrain.TerrainEngine

open UnityEngine
open TerrainTypes
open OpenCL
open System.Collections.Generic

////////////////////////////////////////////////////////////////////////////////
// Terrain Node Construction
////////////////////////////////////////////////////////////////////////////////

//Requires: Vertices, Normals, Tangents
//Async: No
//Ready: EditMeshReadyQ
let NewMesh(gameObject:GameObject, key:Key) =
    let mf = gameObject.AddComponent<MeshFilter>()
    let _ = gameObject.AddComponent<MeshRenderer>()
    gameObject.renderer.material <- new Material(Shader.Find("Unpacked Bumped Diffuse"))
    let mesh = mf.mesh
    mesh.vertices <- Cache.Vertices.[key]
    mesh.normals <- Cache.Normals.[key]
    mesh.tangents <- Cache.Tangents.[key]
    mesh.triangles <- TerrainTypes.FullTriangles
    mesh.uv <- TerrainTypes.FullUV
    mesh.RecalculateBounds()
    ()

//Requires: Vertices, Normals, Tangents
//Async: No
//Ready: EditMeshReadyQ
let ModifyMesh(gameObject:GameObject, key:Key) =
    let mesh = gameObject.GetComponent<MeshFilter>().mesh
    mesh.vertices <- Cache.Vertices.[key]
    mesh.normals <- Cache.Normals.[key]
    mesh.tangents <- Cache.Tangents.[key]
    mesh.RecalculateBounds()
    ()

//Requires: TextureData, NormalMapData
//Enables: Texture, NormalMap
//Async: No
//Ready: EditTexturesReadyQ
let NewTextures(gameObject:GameObject, key:Key) =
    let texture = new Texture2D(Config.TextureRes, Config.TextureRes)
    let normalMap = new Texture2D(Config.TextureRes, Config.TextureRes)

    let color (b:byte4) = Color32(b.x, b.y, b.z, 255uy)

    let fhm = Cache.TextureData.[key]
    let fnm = Cache.NormalMapData.[key]

    texture.SetPixels32([| for i in 0 .. Config.TextureRes * Config.TextureRes - 1 -> color(fhm.[i]) |])
    normalMap.SetPixels32([| for i in 0 .. Config.TextureRes * Config.TextureRes - 1 -> color(fnm.[i]) |])

    texture.wrapMode <- TextureWrapMode.Clamp
    normalMap.wrapMode <- TextureWrapMode.Clamp

    texture.Apply()
    normalMap.Apply()

    Cache.Texture.[key] <- texture
    Cache.NormalMap.[key] <- normalMap

    gameObject.renderer.material.SetTexture("_BumpMap", normalMap)
    gameObject.renderer.material.SetTexture("_MainTex", texture)

    let offset = 1.5f / (float32 Config.TextureRes)
    let tiling = 1.0f - 2.0f * offset

    gameObject.renderer.material.SetTextureOffset("_MainTex", Vector2(offset, offset))
    gameObject.renderer.material.SetTextureScale("_MainTex", Vector2(tiling, tiling))
    gameObject.renderer.material.SetTextureOffset("_BumpMap", Vector2(offset, offset))
    gameObject.renderer.material.SetTextureScale("_BumpMap", Vector2(tiling, tiling))

    ()

//Requires: TextureData, NormalMapData
//Enables: Texture, NormalMap
//Async: No
//Ready: EditTexturesReadyQ
let ModifyTextures(gameObject:GameObject, key:Key) =
    
    let texture = gameObject.renderer.material.GetTexture("_MainTex") :?> Texture2D
    let normalMap = gameObject.renderer.material.GetTexture("_BumpMap") :?> Texture2D

    let color (b:byte4) = Color32(b.x, b.y, b.z, 255uy)

    let fhm = Cache.TextureData.[key]
    let fnm = Cache.NormalMapData.[key]

    texture.SetPixels32([| for i in 0 .. Config.TextureRes * Config.TextureRes - 1 -> color(fhm.[i]) |])
    normalMap.SetPixels32([| for i in 0 .. Config.TextureRes * Config.TextureRes - 1 -> color(fnm.[i]) |])
    
    texture.Apply()
    normalMap.Apply()

    Cache.Texture.[key] <- texture
    Cache.NormalMap.[key] <- normalMap

    ()

//Requires: Nothing
//Async: No
//Ready: True
let BuildNewGameObject (key:Key) =
    
    UpdateMeshData(key)
    UpdateTextureData(key)

    let pID = key.planetID
    let face = key.face
    let cID = key.cellID

    let name = "p" + (string pID) + "_" 
                   + (string face) + "_" 
                   + (string cID)

    let gameObject = new GameObject(name)

    while not (Cache.EditMeshReadyQ(key)) do System.Threading.Thread.Sleep(10)
    NewMesh(gameObject, key)
    
    while not (Cache.EditTexturesReadyQ(key)) do System.Threading.Thread.Sleep(10)
    NewTextures(gameObject, key)

    Cache.Ready.[key] <- true
    Cache.GameObjectRefs.[key] <- ref gameObject

    ()


////////////////////////////////////////////////////////////////////////////////
// Queuing Operations
////////////////////////////////////////////////////////////////////////////////

let TIME_LIMIT = 5L
let QUEUE_LIMIT = 4

type Evaluator(sequence: seq<unit>) = 
    let cacheSeq = Seq.cache sequence
    let mutable n = -1
    member this.Evaluate() = 
        let t() = System.DateTime.Now.Ticks
        let t0 = t()
        let s0 = Seq.takeWhile (fun _ -> (t() - t0)/10000L < TIME_LIMIT) cacheSeq
        match Seq.length s0 with
        | l when l = n -> false
        | l -> n <- l
               true

type EvaluationClass() = 
    let queue = Queue<Evaluator>()
    let emptyEvaluator = Evaluator(seq { yield () })
    let mutable currentEvaluator = emptyEvaluator
    
    member this.Evaluate() = 
        match currentEvaluator.Evaluate() with
        | true -> ()
        | false -> if queue.Count > 0 then currentEvaluator <- queue.Dequeue()
    
    member this.Enqueue(eval: Evaluator) = if queue.Count <= QUEUE_LIMIT then queue.Enqueue eval
    member this.Count = queue.Count
    member this.Cap() = this.Enqueue(emptyEvaluator)

let EvaluationQueue = EvaluationClass()

let BuildRecycledGameObject2 (key:Key) =
    Evaluator(seq {
        
        yield ()

        let gameObject = Cache.ObjectPool.Pop()

        yield ()

        let pID = key.planetID
        let face = key.face
        let cID = key.cellID

        let name = "p" + (string pID) + "_" 
                       + (string face) + "_" 
                       + (string cID)

        gameObject.name <- name

        let rad, amp = Cache.PlanetData.[pID]
        yield ()

        let BL, BR, TL = Corners(key)

        yield ()
        let vertRef = ref (Array.zeroCreate<Vector3> (Config.VertexArraySize |> int))
        let normRef = ref (Array.zeroCreate<Vector3> (Config.VertexArraySize |> int))
        let tangRef = ref (Array.zeroCreate<Vector4> (Config.VertexArraySize |> int))
        
        yield ()
        let hmDataRef = ref (Array.zeroCreate<byte4> (Config.TextureArraySize |> int))
        let nmDataRef = ref (Array.zeroCreate<byte4> (Config.TextureArraySize |> int))

        yield ()

        yield (OpenCL.UpdateRefs(vertRef, normRef, tangRef, hmDataRef, nmDataRef, BL, BR, TL, rad, amp))
        
        //Debug.Log("Should be waiting here...")
        // Wait here until OpenCL queue is ready!
        yield ()

        //Debug.Log("Data should be ready by now")
        let mesh = gameObject.GetComponent<MeshFilter>().mesh

        yield ()

        let v0, n0, t0 = OpenCL.AppendFlange rad amp (vertRef.contents) (normRef.contents) (tangRef.contents)

        mesh.vertices <- v0
        mesh.normals <- n0
        mesh.tangents <- t0

        yield ()
        mesh.RecalculateBounds()

        yield ()

        let normalcolor (b:byte4) = Color32(b.x, b.y, b.z, 255uy)
        let texture = new Texture2D(Config.TextureRes, Config.TextureRes)
        let normalMap = new Texture2D(Config.TextureRes, Config.TextureRes)
    
        yield ()
        texture.SetPixels32(Array.map normalcolor (hmDataRef.contents))
        texture.Apply()
        texture.wrapMode <- TextureWrapMode.Clamp

        yield ()
        normalMap.SetPixels32(Array.map normalcolor (nmDataRef.contents))
        normalMap.Apply()
        normalMap.wrapMode <- TextureWrapMode.Clamp

        yield ()
        gameObject.renderer.material.SetTexture("_BumpMap", normalMap)
        gameObject.renderer.material.SetTexture("_MainTex", texture)

        let offset = 1.5f / (float32 Config.TextureRes)
        let tiling = 1.0f - 2.0f * offset

        yield ()
        gameObject.renderer.material.SetTextureOffset("_MainTex", Vector2(offset, offset))
        gameObject.renderer.material.SetTextureScale("_MainTex", Vector2(tiling, tiling))
        gameObject.renderer.material.SetTextureOffset("_BumpMap", Vector2(offset, offset))
        gameObject.renderer.material.SetTextureScale("_BumpMap", Vector2(tiling, tiling))

        Cache.Ready.[key] <- true
        //Debug.Log(key.ToString() + " is now marked as ready.")
        Cache.GameObjectRefs.[key] <- ref gameObject
        
        // Make sure sequence is evaluated all the way to end
        yield ()
    })

let Split2 (key: Key) =
    let ch = Children(key)
    match List.forall (Cache.ReadyQ) ch with
    | true  -> List.iter (Cache.Enable) ch
               Cache.Disable key
               ch
    | false -> List.iter (fun k -> EvaluationQueue.Enqueue(BuildRecycledGameObject2 k)) ch
               [ key ]

let Merge(key: Key) = 
    match key.cellID > 3L with
    | false -> key
    | true -> 
        Neighbors(key) |> List.iter (Cache.Disable)
        let p = Parent(key)
        (Cache.Enable p)
        p


////////////////////////////////////////////////////////////////////////////////
// Terrain Node Processing
////////////////////////////////////////////////////////////////////////////////

let DistanceToNode(key:Key) =
    let boundingBox = Cache.GameObjectRefs.[key].Value.GetComponent<MeshFilter>().mesh.bounds
    let minV, maxV = boundingBox.min, boundingBox.max
    let cameraPos = Camera.main.transform.position
    let closestPoint = Vector3(Mathf.Clamp(cameraPos.x, minV.x, maxV.x),
                               Mathf.Clamp(cameraPos.y, minV.y, maxV.y),
                               Mathf.Clamp(cameraPos.z, minV.z, maxV.z))
    Mathf.Max(0.0001f, Vector3.Distance(cameraPos, closestPoint))

let DistanceError(key:Key) =
    let rad, _ = Cache.PlanetData.[key.planetID]
    let (BL, BR, _) = Corners(key)
    let d = (rad / 2.0f) * Vector3.Distance(BL, BR)
    let D = DistanceToNode(key)
    d / D

let ClosestNode(currentKeys : Key list) = List.minBy DistanceToNode currentKeys

let rec ProcessKeys2 (t:float32) =
    function
    | [] -> EvaluationQueue.Cap()
            []
    | (k::ks) ->
        let pk = ProcessKeys2 t
        let d = DistanceError
        match (Cache.ActiveQ k) with
        | false -> pk ks
        | true ->
            match (d k, d (Parent k)) with
            | (d, _) when d > t -> let split = (Split2 k)
                                   split @ (pk ks)
            | (_, p) when p < t -> (Merge k) :: (pk ks)
            | _ -> k :: (pk ks)


let ProcessFrame2 (baseGameObject:GameObject) (rootObject: GameObject) (t:float32) (keyList: Key list) =
    match (OpenCL.QueueBusy(), EvaluationQueue.Count) with
    | (true, _) -> keyList
    | (false, 0) -> 
        if Cache.ObjectPool.Count < Config.ObjectPoolSize / 2 then
            Cache.FillObjectPool(baseGameObject, rootObject)
        ProcessKeys2 t keyList
    | (false, _) ->
        OpenCL.Reset()
        EvaluationQueue.Evaluate()
        keyList
        

let InitializeKeys (rad:float32) (amp:float32) (baseGameObject:GameObject) (rootObject: GameObject)=
    Cache.PlanetData.[0] <- (rad, amp)
    
    let keys = [ MakeKey(0, CubeFace.Front,  -1L)
                 MakeKey(0, CubeFace.Top,    -1L)
                 MakeKey(0, CubeFace.Bottom, -1L)
                 MakeKey(0, CubeFace.Left,   -1L)
                 MakeKey(0, CubeFace.Right,  -1L)
                 MakeKey(0, CubeFace.Back,   -1L) ]
    List.iter (fun k -> BuildNewGameObject k) keys

    let tempObj = Cache.GameObjectRefs.[MakeKey(0, CubeFace.Front,  -1L)].Value

    Cache.FillObjectPool(tempObj, rootObject)
    keys

let KeyStringArray (keys: Key list) = 
    keys 
    |> Array.ofList 
    |> Array.map (fun k -> k.ToString() + ": " + DistanceError(k).ToString())

let FlushCache (rad:float32) (amp:float32) (baseGameObject:GameObject) (rootObject: GameObject) =
    let c = rootObject.transform.childCount
    for i in 0 .. c-1 do
        let t = rootObject.transform.GetChild(i)
        Object.Destroy(t.gameObject)

    for obj in Cache.ObjectPool do
        Object.Destroy(obj)

    Cache.ObjectPool.Clear()
    Cache.PlanetData.Clear()
    Cache.Ready.Clear()
    Cache.Vertices.Clear()
    Cache.Normals.Clear()
    Cache.Tangents.Clear()
    Cache.TextureData.Clear()
    Cache.NormalMapData.Clear()
    Cache.Texture.Clear()
    Cache.NormalMap.Clear()
    Cache.GameObjectRefs.Clear()

    System.GC.Collect()

    InitializeKeys rad amp baseGameObject rootObject
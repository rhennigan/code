module OpenCLCubeMap

open Cloo
open UnityEngine

[<Literal>]
let VERTEX_GRID_SIZE = 16
let VERTEX_ARRAY_SIZE = int64(VERTEX_GRID_SIZE * VERTEX_GRID_SIZE * 4)

type CubeFace =
    | Front  = 0
    | Back   = 1
    | Left   = 2
    | Right  = 3
    | Top    = 4
    | Bottom = 5

type TerrainNode =
    {
        planetID : int
        face : CubeFace
        cellID : int64
        BL : Vector3
        BR : Vector3
        TL : Vector3
        gameObject : GameObject
        bounds : Bounds
    }

type Key = {planetID:int; face:CubeFace; cellID:int64}

let makeKey(pID:int, f:CubeFace, cID:int64) =
    {planetID = pID; face = f; cellID = cID}

let TerrainNodeCache = System.Collections.Generic.Dictionary<Key, TerrainNode>()

let Triangles =
  
  let vs = VERTEX_GRID_SIZE
  let tl = vs * i + j
  let tr = vs * i + j + 1
  let bl = vs * (i + 1) + j
  let br = vs * (i + 1) + j + 1

  seq {
    for i in 0 .. (vs - 2) do
      for j in 0 .. (vs - 2) do

        if i + j % 2 = 0 then
          yield tl
          yield bl
          yield tr

          yield bl
          yield br
          yield tr

        else
          yield tl
          yield bl
          yield br

          yield tr
          yield tl
          yield br
                
    } |> Array.ofSeq

let UV =
    let w = float32 VERTEX_GRID_SIZE - 1.0f
    let h = float32 VERTEX_GRID_SIZE - 1.0f
    seq {
            for i in 0.0f .. h do
                    for j in 0.0f .. w do
                        let r = j / w
                        let u = i / h
                        yield Vector2(r, u)
        }
    |> Array.ofSeq

let OpenCLComputePlatform = 
    new ComputeContextPropertyList(ComputePlatform.Platforms.[0])

let OpenCLContext = 
    new ComputeContext(ComputeDeviceTypes.Default, 
                       OpenCLComputePlatform, 
                       null, 
                       System.IntPtr.Zero)

let VertexDisplacementKernel =
    let path = @"E:\GDrive\PlanetTesting\Assets\Code\F#\Terrain.cl"
    let kernelSource = System.IO.File.ReadAllText(path)
    let program = new ComputeProgram(OpenCLContext, [|kernelSource|])
    program.Build(null, null, null, System.IntPtr.Zero)
    let k = program.CreateKernel("VertexDisplacement")
    program.Dispose()
    k

let VertexBuffer = 
    new ComputeBuffer<float32>(OpenCLContext, 
                               ComputeMemoryFlags.WriteOnly, 
                               VERTEX_ARRAY_SIZE)

VertexDisplacementKernel.SetMemoryArgument(0, VertexBuffer)

let VertexDisplacement (BL:Vector3, BR:Vector3, TL:Vector3) =

    VertexDisplacementKernel.SetValueArgument(1, BL.x)
    VertexDisplacementKernel.SetValueArgument(2, BL.y)
    VertexDisplacementKernel.SetValueArgument(3, BL.z)

    VertexDisplacementKernel.SetValueArgument(4, BR.x)
    VertexDisplacementKernel.SetValueArgument(5, BR.y)
    VertexDisplacementKernel.SetValueArgument(6, BR.z)

    VertexDisplacementKernel.SetValueArgument(7, TL.x)
    VertexDisplacementKernel.SetValueArgument(8, TL.y)
    VertexDisplacementKernel.SetValueArgument(9, TL.z)

    VertexDisplacementKernel.SetValueArgument(10, VERTEX_GRID_SIZE)

    let commands = new ComputeCommandQueue(OpenCLContext, 
                                           OpenCLContext.Devices.[0], 
                                           ComputeCommandQueueFlags.None)
    let events = new ComputeEventList()
    commands.Execute(VertexDisplacementKernel, 
                     null, 
                     [| VERTEX_ARRAY_SIZE |], 
                     null, 
                     events)

    let get = ref (Array.create (int VERTEX_ARRAY_SIZE) 0.0f)
    commands.ReadFromBuffer(VertexBuffer, get, true, events)

    let data = get.contents

    // cleanup commands
    commands.Dispose()

    [|for i in 0..4..(int VERTEX_ARRAY_SIZE)-1 -> 
        Vector3(data.[i], data.[i+1], data.[i+2])|]

let Cleanup() =
    VertexDisplacementKernel.Dispose()
    VertexBuffer.Dispose()

let Activate(node : TerrainNode) =
    node.gameObject.SetActive(true)
    node

let Deactivate(node : TerrainNode) =
    node.gameObject.SetActive(false)
    node

let BuildMesh(vertices : Vector3[]) =
    let mesh = new Mesh()
    mesh.vertices <- vertices
    mesh.triangles <- Triangles
    mesh.uv <- UV
    mesh.RecalculateNormals()
    mesh.RecalculateBounds()
    mesh

let BuildGameObject(name : string, mesh : Mesh, material : Material) =
    let gameObject = new GameObject(name)
    let meshFilter = gameObject.AddComponent<MeshFilter>()
    meshFilter.mesh <- mesh
    let meshRenderer = gameObject.AddComponent<MeshRenderer>()
    let meshCollider = gameObject.AddComponent<MeshCollider>()
    meshCollider.sharedMesh <- mesh
    gameObject.renderer.material <- new Material(material)
    gameObject

let CreateTerrainNode(planetID : int, face : CubeFace, cellID : int64,
                      bl : Vector3, br : Vector3, tl : Vector3, 
                      material : Material) =

    let name = "p" + (string planetID) + "_" 
                   + (string face) + "_" 
                   + (string cellID)

    let vertices = VertexDisplacement(bl, br, tl)
    let mesh = BuildMesh(vertices)
    let bounds = mesh.bounds
    let gameObject = BuildGameObject(name, mesh, material)

    let node =
        {
            planetID = planetID
            face = face
            cellID = cellID
            BL = bl
            BR = br
            TL = tl
            gameObject = gameObject
            bounds = bounds
        }

    let key = {planetID = planetID
               face = face
               cellID = cellID}

    TerrainNodeCache.[key] <- node

    node

let GetTerrainNode(planetID:int, face:CubeFace, cellID:int64,
                   bl:Vector3, br:Vector3, tl:Vector3, 
                   material:Material) =

    let key = {planetID=planetID; face=face; cellID=cellID}
    if TerrainNodeCache.ContainsKey(key) then 
        TerrainNodeCache.[key]
    else
        CreateTerrainNode(planetID, face, cellID, bl, br, tl, material)

let NextKeys(node:TerrainNode) =
    let i = node.cellID + 1L
    let bi = 4L * i
    let TLi = bi + 0L
    let TRi = bi + 1L
    let BLi = bi + 2L
    let BRi = bi + 3L
    let pID = node.planetID
    let face = node.face
    (makeKey(pID, face, TLi),
     makeKey(pID, face, TRi),
     makeKey(pID, face, BLi),
     makeKey(pID, face, BRi))

let SplitNode(node:TerrainNode) =
    
    let BL, BR, TL = node.BL, node.BR, node.TL
    let dX = 0.5f * (BR - BL)
    let dY = 0.5f * (TL - BL)
    let left = BL + dY
    let bottom = BL + dX
    let mid = left + dX
    let top = mid + dY
    let right = mid + dX

    let i = node.cellID + 1L
    let bi = 4L * i
    let TLi = bi + 0L
    let TRi = bi + 1L
    let BLi = bi + 2L
    let BRi = bi + 3L

    let pID = node.planetID
    let face = node.face
    let mat = node.gameObject.renderer.material

    let TLnode = GetTerrainNode(pID, face, TLi, left,   mid,    TL,   mat)
    let TRnode = GetTerrainNode(pID, face, TRi, mid,    right,  top,  mat)
    let BLnode = GetTerrainNode(pID, face, BLi, BL,     bottom, left, mat)
    let BRnode = GetTerrainNode(pID, face, BRi, bottom, BR,     mid,  mat)

    //Deactivate(node);

    [|TLnode; TRnode; BLnode; BRnode|]

let DistanceError(node:TerrainNode) =
    let boundingBox = node.bounds
    let d = boundingBox.SqrDistance(Camera.main.transform.position)
    let b = boundingBox.size
    let s = max b.x (max b.y b.z)
    (2.0f * atan(s / (2.0f * d))) / Mathf.PI

let ViewportError(node:TerrainNode) =
    let boundingBox = node.bounds
    let bMax, bMin = boundingBox.max, boundingBox.min
    let sMax = Camera.main.WorldToViewportPoint(bMax)
    let sMin = Camera.main.WorldToViewportPoint(bMin)
    let xMin, xMax = Mathf.Clamp01(sMin.x), Mathf.Clamp01(sMax.x)
    let yMin, yMax = Mathf.Clamp01(sMin.y), Mathf.Clamp01(sMax.y)
    let w, h = abs(xMax - xMin), abs(yMax - yMin)
    if w < 0.0001f || h < 0.0001f then
        0.0f
    else
        max w h

//let rec ResetSubNodes(node:TerrainNode) =
//
//    let k1, k2, k3, k4 = NextKeys(node)
//
//    let reset(k) = 
//        if TerrainNodeCache.ContainsKey(k) then
//            let n = TerrainNodeCache.[k]
//            Deactivate(n)
//            ResetSubNodes(n)
//    
//    reset(k1)
//    reset(k2)
//    reset(k3)
//    reset(k4)

let RefineNode (threshold:float32) (node:TerrainNode) =
    let error = ViewportError(node)
    if error > threshold then
        SplitNode(node)
    else
        [|node|]

let RootNodes(planetID:int, material:Material) =

    let makeSide(BL, BR, TL, side) =
        CreateTerrainNode(planetID, side, 0L, BL, BR, TL, material)

    let front  = makeSide(Vector3(-1.0f, -1.0f,  1.0f), 
                          Vector3( 1.0f, -1.0f,  1.0f), 
                          Vector3(-1.0f,  1.0f,  1.0f),
                          CubeFace.Front)

    let top    = makeSide(Vector3(-1.0f,  1.0f,  1.0f), 
                          Vector3( 1.0f,  1.0f,  1.0f), 
                          Vector3(-1.0f,  1.0f, -1.0f),
                          CubeFace.Top)

    let bottom = makeSide(Vector3(-1.0f, -1.0f, -1.0f), 
                          Vector3( 1.0f, -1.0f, -1.0f), 
                          Vector3(-1.0f, -1.0f,  1.0f),
                          CubeFace.Bottom)

    let left   = makeSide(Vector3(-1.0f, -1.0f, -1.0f), 
                          Vector3(-1.0f, -1.0f,  1.0f), 
                          Vector3(-1.0f,  1.0f, -1.0f),
                          CubeFace.Left)

    let right  = makeSide(Vector3( 1.0f, -1.0f,  1.0f), 
                          Vector3( 1.0f, -1.0f, -1.0f), 
                          Vector3( 1.0f,  1.0f,  1.0f),
                          CubeFace.Right)

    let back   = makeSide(Vector3( 1.0f, -1.0f, -1.0f), 
                          Vector3(-1.0f, -1.0f, -1.0f), 
                          Vector3( 1.0f,  1.0f, -1.0f),
                          CubeFace.Back)

    [|front; top; bottom; left; right; back|]

let UpdateNodes(threshold:float32, nodes:TerrainNode[]) =
    Array.collect (RefineNode threshold) nodes


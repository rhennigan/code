module OpenCLCubeMap

open Cloo
open UnityEngine

[<Literal>]
let OBJECT_POOL_SIZE = 4

[<Literal>]
let VERTEX_GRID_SIZE = 32
let VERTEX_ARRAY_SIZE = VERTEX_GRID_SIZE * VERTEX_GRID_SIZE |> int64

[<Literal>]
let PLANET_RADIUS = 100.0f

[<Literal>]
let NOISE_AMPLITUDE = 0.2f

[<Literal>]
let NORMAL_INTENSITY = 1.0f

[<Literal>]
let NORMAL_SIZE = 256
let NORMAL_ARRAY_SIZE = NORMAL_SIZE * NORMAL_SIZE |> int64

type CubeFace =
    | Front  = 0
    | Back   = 1
    | Left   = 2
    | Right  = 3
    | Top    = 4
    | Bottom = 5

type TerrainNode =
    {
        planetID:int
        face:CubeFace
        cellID:int64
        BL:Vector3
        BR:Vector3
        TL:Vector3
        gameObject:GameObject
        bounds:Bounds
    }

type Key = {planetID:int; face:CubeFace; cellID:int64}

let makeKey(pID:int, f:CubeFace, cID:int64) =
    {planetID = pID; face = f; cellID = cID}

let TerrainNodeCache = System.Collections.Generic.Dictionary<Key, TerrainNode>()
let ObjectPool = System.Collections.Generic.Stack<GameObject>(OBJECT_POOL_SIZE)

let FillObjectPool(baseGameObject:GameObject) =
    ObjectPool.Clear()
    Debug.Log("Filling Object Pool!")
    for i in 0 .. OBJECT_POOL_SIZE do
        let gameObject = GameObject.Instantiate(baseGameObject) :?> GameObject
        ObjectPool.Push(gameObject)

//let Triangles =
//    seq {
//        for i in 0 .. (VERTEX_GRID_SIZE-2) do
//            for j in 0 .. (VERTEX_GRID_SIZE-2) do
//                
//                yield VERTEX_GRID_SIZE * i + j
//                yield VERTEX_GRID_SIZE * (i + 1) + j
//                yield VERTEX_GRID_SIZE * i + j + 1
//                        
//                yield VERTEX_GRID_SIZE * (i + 1) + j
//                yield VERTEX_GRID_SIZE * (i + 1) + j + 1
//                yield VERTEX_GRID_SIZE * i + j + 1
//                
//    } |> Array.ofSeq

let Triangles =
  
    let vs = VERTEX_GRID_SIZE

    seq {
        for i in 0 .. (vs - 2) do
            for j in 0 .. (vs - 2) do

                let tl = vs * i + j
                let tr = vs * i + j + 1
                let bl = vs * (i + 1) + j
                let br = vs * (i + 1) + j + 1

                if (i + j) % 2 = 0 then
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
    let vs = VERTEX_GRID_SIZE
    let w = float32 vs - 1.0f
    let h = float32 vs - 1.0f
    seq {
            for i in 0.0f .. h do
                    for j in 0.0f .. w do
                        let r = j / w
                        let u = i / h
                        yield Vector2(r, u)
        }
    |> Array.ofSeq

////////////////////////////////////////////////////////////////////////////////
// Open CL Host Code: Normal Mapping
////////////////////////////////////////////////////////////////////////////////

let OpenCLComputePlatform = 
    new ComputeContextPropertyList(ComputePlatform.Platforms.[0])

let OpenCLContext = 
    new ComputeContext(ComputeDeviceTypes.Default, 
                       OpenCLComputePlatform, 
                       null, 
                       System.IntPtr.Zero)

let NormalMapKernel =
    let path = @"E:\GDrive\PlanetTesting\Assets\Code\F#\Terrain.cl"
    let kernelSource = System.IO.File.ReadAllText(path)
    let program = new ComputeProgram(OpenCLContext, [|kernelSource|])
    program.Build(null, null, null, System.IntPtr.Zero)
    let k = program.CreateKernel("NormalMap")
    program.Dispose()
    k

let NormalBuffer =
    new ComputeBuffer<Vector4>(OpenCLContext,
                               ComputeMemoryFlags.WriteOnly,
                               NORMAL_ARRAY_SIZE)

NormalMapKernel.SetMemoryArgument(0, NormalBuffer)

let NormalMap (BL:Vector3, BR:Vector3, TL:Vector3, intensity:float32) =

    NormalMapKernel.SetValueArgument(1, BL.x)
    NormalMapKernel.SetValueArgument(2, BL.y)
    NormalMapKernel.SetValueArgument(3, BL.z)

    NormalMapKernel.SetValueArgument(4, BR.x)
    NormalMapKernel.SetValueArgument(5, BR.y)
    NormalMapKernel.SetValueArgument(6, BR.z)

    NormalMapKernel.SetValueArgument(7, TL.x)
    NormalMapKernel.SetValueArgument(8, TL.y)
    NormalMapKernel.SetValueArgument(9, TL.z)

    NormalMapKernel.SetValueArgument(10, VERTEX_GRID_SIZE)
    NormalMapKernel.SetValueArgument(11, PLANET_RADIUS)
    NormalMapKernel.SetValueArgument(12, NOISE_AMPLITUDE)
    NormalMapKernel.SetValueArgument(13, intensity)

    let commands = new ComputeCommandQueue(OpenCLContext,
                                           OpenCLContext.Devices.[0],
                                           ComputeCommandQueueFlags.None)
    
    let events = new ComputeEventList()
    commands.Execute(NormalMapKernel,
                     null,
                     [| NORMAL_ARRAY_SIZE |],
                     null,
                     null)
    
    let get = ref (Array.zeroCreate<Vector4> (int NORMAL_ARRAY_SIZE))
    //let get = ref (Array.create (int NORMAL_ARRAY_SIZE * 4) 0.0f)
    commands.ReadFromBuffer(NormalBuffer, get, true, events)
    commands.Finish()

    let data = get.contents

    commands.Dispose()

    let normalMap = new Texture2D(NORMAL_SIZE, NORMAL_SIZE)
    
    for i in 0..(int NORMAL_ARRAY_SIZE)-1 do
        normalMap.SetPixel(i/NORMAL_SIZE, i % NORMAL_SIZE, 
                           Color(data.[i].x, data.[i].y, 1.0f))

//    let bmp = new System.Drawing.Bitmap(NORMAL_SIZE, NORMAL_SIZE)
//    for i in 0..(int NORMAL_SIZE)-1 do
//        for j in 0..(int NORMAL_SIZE)-1 do
//            bmp.SetPixel(i, j, System.Drawing.Color.FromArgb(255.0f * data.[i].x |> int,
//                                                             255.0f * data.[i].y |> int,
//                                                             255.0f * 0.5f |> int))
////            bmp.SetPixel(i, j, System.Drawing.Color.FromArgb(255.0f * normalMap.GetPixel(i,j).r |> int,
////                                                             255.0f * normalMap.GetPixel(i,j).g |> int,
////                                                             255.0f * normalMap.GetPixel(i,j).b |> int))
//
//    let name = (string BL) + (string BR) + (string TL) + ".bmp"
//    bmp.Save(@"E:\GDrive\PlanetTesting\" + name)

    normalMap

////////////////////////////////////////////////////////////////////////////////
// Open CL Host Code: Cube to Sphere Vertex Mapping
////////////////////////////////////////////////////////////////////////////////

let VertexDisplacementKernel =
    let path = @"E:\GDrive\PlanetTesting\Assets\Code\F#\Terrain.cl"
    let kernelSource = System.IO.File.ReadAllText(path)
    let program = new ComputeProgram(OpenCLContext, [|kernelSource|])
    program.Build(null, null, null, System.IntPtr.Zero)
    let k = program.CreateKernel("VertexDisplacement")
    program.Dispose()
    k

let VertexBuffer = 
    new ComputeBuffer<Vector4>(OpenCLContext, 
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
    VertexDisplacementKernel.SetValueArgument(11, PLANET_RADIUS)
    VertexDisplacementKernel.SetValueArgument(12, NOISE_AMPLITUDE)

    let commands = new ComputeCommandQueue(OpenCLContext, 
                                           OpenCLContext.Devices.[0], 
                                           ComputeCommandQueueFlags.None)
    let events = new ComputeEventList()
    commands.Execute(VertexDisplacementKernel, 
                     null, 
                     [| VERTEX_ARRAY_SIZE |], 
                     null, 
                     null)

    let get = ref (Array.zeroCreate<Vector4> (int VERTEX_ARRAY_SIZE))
    //let get = ref (Array.create (int VERTEX_ARRAY_SIZE * 4) 0.0f)
    commands.ReadFromBuffer(VertexBuffer, get, true, events)
    commands.Finish();
    let data = get.contents

    // cleanup commands
    commands.Dispose()

    [|for i in 0..(int VERTEX_ARRAY_SIZE)-1 -> 
        Vector3(data.[i].x, data.[i].y, data.[i].z)|]

let Cleanup() =
    VertexDisplacementKernel.Dispose()
    VertexBuffer.Dispose()

let Activate(node:TerrainNode) =
    node.gameObject.SetActive(true)
    node

let Deactivate(node:TerrainNode) =
    node.gameObject.SetActive(false)

//let BuildMesh(vertices:Vector3[]) =
//    let mesh = new Mesh()
//    mesh.vertices <- vertices
//    mesh.triangles <- Triangles
//    mesh.uv <- UV
//    mesh.RecalculateNormals()
//    mesh.RecalculateBounds()
//    mesh

//let BuildGameObject(name:string, mesh:Mesh, material:Material) =
//    let gameObject = new GameObject(name)
//    let meshFilter = gameObject.AddComponent<MeshFilter>()
//    meshFilter.mesh <- mesh
//    let meshRenderer = gameObject.AddComponent<MeshRenderer>()
//    let meshCollider = gameObject.AddComponent<MeshCollider>()
//    meshCollider.sharedMesh <- mesh
//    gameObject.renderer.material <- new Material(material)
//    gameObject

let CalculateMeshTangents(mesh:Mesh) =
    let triangles = mesh.triangles
    let vertices = mesh.vertices
    let uv = mesh.uv
    let normals = mesh.normals

    let triangleCount = triangles.Length
    let vertexCount = vertices.Length

    let tan1 = Array.zeroCreate<Vector3> vertexCount
    let tan2 = Array.zeroCreate<Vector3> vertexCount

    let tangents = Array.zeroCreate<Vector4> vertexCount

    for a in 0..3..(triangleCount-1) do

        let i1 = triangles.[a + 0]
        let i2 = triangles.[a + 1]
        let i3 = triangles.[a + 2]

        let v1 = vertices.[i1]
        let v2 = vertices.[i2]
        let v3 = vertices.[i3]

        let w1 = uv.[i1]
        let w2 = uv.[i2]
        let w3 = uv.[i3]

        let x1 = v2.x - v1.x
        let x2 = v3.x - v1.x
        let y1 = v2.y - v1.y
        let y2 = v3.y - v1.y
        let z1 = v2.z - v1.z
        let z2 = v3.z - v1.z

        let s1 = w2.x - w1.x
        let s2 = w3.x - w1.x
        let t1 = w2.y - w1.y
        let t2 = w3.y - w1.y

        let r = 1.0f / (s1 * t2 - s2 * t1)

        let sdir = Vector3((t2 * x1 - t1 * x2) * r, (t2 * y1 - t1 * y2) * r, (t2 * z1 - t1 * z2) * r)
        let tdir = Vector3((s1 * x2 - s2 * x1) * r, (s1 * y2 - s2 * y1) * r, (s1 * z2 - s2 * z1) * r)

        tan1.[i1] <- tan1.[i1] + sdir
        tan1.[i2] <- tan1.[i2] + sdir
        tan1.[i3] <- tan1.[i3] + sdir

        tan2.[i1] <- tan2.[i1] + tdir
        tan2.[i2] <- tan2.[i2] + tdir
        tan2.[i3] <- tan2.[i3] + tdir

    for a in 0..(vertexCount-1) do
        let nR = ref normals.[a]
        let tR = ref tan1.[a]

        Vector3.OrthoNormalize(nR, tR)
        let n, t = nR.Value, tR.Value

        tangents.[a].x <- t.x
        tangents.[a].y <- t.y
        tangents.[a].z <- t.z

        tangents.[a].w <- if (Vector3.Dot(Vector3.Cross(n, t), tan2.[a]) < 0.0f) then -1.0f else 1.0f

    mesh.tangents <- tangents

let BuildGameObject(name:string, vertices:Vector3[], baseGameObject:GameObject) =

    if ObjectPool.Count < 1 then
        FillObjectPool(baseGameObject)

    let gameObject = ObjectPool.Pop()
    
    let mesh = gameObject.GetComponent<MeshFilter>().mesh
    mesh.vertices <- vertices
    mesh.triangles <- Triangles
    mesh.uv <- UV
    mesh.RecalculateNormals()
    mesh.RecalculateBounds()
    CalculateMeshTangents(mesh)
//    let meshCollider = gameObject.GetComponent<MeshCollider>()
//    meshCollider.sharedMesh <- mesh

    (gameObject, mesh.bounds)

let CreateTerrainNode(planetID:int,
                      face:CubeFace,
                      cellID:int64,
                      bl:Vector3, 
                      br:Vector3, 
                      tl:Vector3,
                      baseGameObject:GameObject) =

    let name = "p" + (string planetID) + "_" 
                   + (string face) + "_" 
                   + (string cellID)

    let vertices = VertexDisplacement(bl, br, tl)
    let gameObject, bounds = BuildGameObject(name, vertices, baseGameObject)
    gameObject.name <- name

    let normalMap = NormalMap(bl, br, tl, NORMAL_INTENSITY)

    //let png = normalMap.EncodeToPNG()

    gameObject.renderer.material.SetTexture("_BumpMap", normalMap)

    //gameObject.renderer.material.shader <- Shader.Find("Unpacked Bumped Diffuse");

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
                   baseGameObject:GameObject) =

    let key = {planetID=planetID; face=face; cellID=cellID}
    let node =
        if TerrainNodeCache.ContainsKey(key) then 
            TerrainNodeCache.[key]
        else
            CreateTerrainNode(planetID, face, cellID, bl, br, tl, baseGameObject)
    node

//let CreateTerrainNode(planetID:int,
//                      face:CubeFace,
//                      cellID:int64,
//                      bl:Vector3, 
//                      br:Vector3, 
//                      tl:Vector3, 
//                      material:Material) =
//
//    let name = "p" + (string planetID) + "_" 
//                   + (string face) + "_" 
//                   + (string cellID)
//
//    let vertices = VertexDisplacement(bl, br, tl)
//    let mesh = BuildMesh(vertices)
//    let bounds = mesh.bounds
//    let gameObject = BuildGameObject(name, mesh, material)
//
//    let node =
//        {
//            planetID = planetID
//            face = face
//            cellID = cellID
//            BL = bl
//            BR = br
//            TL = tl
//            gameObject = gameObject
//            bounds = bounds
//        }
//
//    let key = {planetID = planetID
//               face = face
//               cellID = cellID}
//
//    TerrainNodeCache.[key] <- node
//
//    node

//let GetTerrainNode(planetID:int, face:CubeFace, cellID:int64,
//                   bl:Vector3, br:Vector3, tl:Vector3, 
//                   material:Material) =
//
//    let key = {planetID=planetID; face=face; cellID=cellID}
//    if TerrainNodeCache.ContainsKey(key) then 
//        TerrainNodeCache.[key]
//    else
//        CreateTerrainNode(planetID, face, cellID, bl, br, tl, material)

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
    let gameObject = node.gameObject

    let TLnode = GetTerrainNode(pID, face, TLi, left,   mid,    TL,   gameObject)
    let TRnode = GetTerrainNode(pID, face, TRi, mid,    right,  top,  gameObject)
    let BLnode = GetTerrainNode(pID, face, BLi, BL,     bottom, left, gameObject)
    let BRnode = GetTerrainNode(pID, face, BRi, bottom, BR,     mid,  gameObject)
    
    [|TLnode; TRnode; BLnode; BRnode|]

let InactiveSplit(node:TerrainNode) =
    let next = SplitNode(node)
    Array.iter Deactivate next
    next

let DistanceError(node:TerrainNode) =
    let boundingBox = node.bounds
    let d = boundingBox.SqrDistance(Camera.main.transform.position) |> sqrt
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
//            if n.gameObject.activeSelf then
//                Deactivate(n)
//                ResetSubNodes(n)
//    
//    reset(k1)
//    reset(k2)
//    reset(k3)
//    reset(k4)

let rec RefineNode (threshold:float32) (node:TerrainNode) =
    let error = DistanceError(node)
    if error > threshold then
        Array.collect (RefineNode threshold) (SplitNode(node))
    else
        [|node|]

let RootNodes(planetID:int, baseGameObject:GameObject) =

    let makeSide(BL, BR, TL, side) =
        CreateTerrainNode(planetID, side, 0L, BL, BR, TL, baseGameObject)

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

let rec InitializeNodes (count:int) (rootNodes:TerrainNode[]) =
    if rootNodes.Length < count then
        Array.collect InactiveSplit rootNodes
        |> InitializeNodes count
    else
        rootNodes

let UpdateNodes(threshold:float32, nodes:TerrainNode[]) =
    nodes
    |> Array.collect (RefineNode threshold)
    |> Array.map Activate

//let cubeMap (v : Vector3) = 
//    let (xm, ym, zm) = (abs (v.x), abs (v.y), abs (v.z))
//    match (max xm (max ym zm)) with
//    | m when m = xm -> v / xm
//    | m when m = ym -> v / ym
//    | m when m = zm -> v / zm
//    | _ -> failwith "CubeMapping broke: This should never happen..."
//
//let EmptyNodeObject(material:Material) =
//    let name = "Empty Terrain Grid"
//    let gameObject0 = RootNodes(0, material).[1].gameObject
//    let meshFilter0 = gameObject0.AddComponent<MeshFilter>()
//    let mesh0 = gameObject0.GetComponent<MeshFilter>().mesh
//    let vertices = Array.map cubeMap (mesh0.vertices)
//    let mesh = new Mesh()
//    mesh.vertices <- vertices
//    mesh.triangles <- Triangles
//    mesh.uv <- UV
//    mesh.RecalculateNormals()
//    mesh.RecalculateBounds()
//    BuildGameObject(name, mesh, material)


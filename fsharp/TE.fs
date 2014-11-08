module TE

open Cloo
open UnityEngine

let ElapsedTime(startTime: int64, task: string) = 
    let endTime = System.DateTime.Now.Ticks
    let elapsed = endTime - startTime
#if COMPILED
    Debug.Log("Time to " + task + ": " + (elapsed / 10000L
                                          |> string) + " ms")
#else
    printfn "%s" ("Time to " + task + ": " + (elapsed/10000L |> string) + " ms")
#endif
    

let Now() = System.DateTime.Now.Ticks

////////////////////////////////////////////////////////////////////////////////
//#region Configuration Constants
////////////////////////////////////////////////////////////////////////////////

[<Literal>]
let ARRAY_SIZE = 17L

[<Literal>]
let TEXTURE_SIZE = 512L

[<Literal>]
let OBJECT_POOL_SIZE = 1024

//#endregion

////////////////////////////////////////////////////////////////////////////////
//#region Fixed Mesh Components
////////////////////////////////////////////////////////////////////////////////

let Triangles = 
    let vs = ARRAY_SIZE |> int
    seq { 
        for i in 0..(vs - 2) do
            for j in 0..(vs - 2) do
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
    }
    |> Array.ofSeq

let EdgeFill = 
    let vs = ARRAY_SIZE |> int
    let b = vs * vs - vs
    seq { 
        for i in 0..2..(vs - 3) do
            yield! seq [ vs * i
                         vs * (i + 2)
                         vs * (i + 1)
                         vs * i
                         vs * (i + 1)
                         vs * (i + 2)
                         vs * (i + 3) - 1
                         vs * (i + 1) - 1
                         vs * (i + 2) - 1
                         vs * (i + 3) - 1
                         vs * (i + 2) - 1
                         vs * (i + 1) - 1
                         i + 1
                         i + 2
                         i
                         i + 1
                         i
                         i + 2
                         b + i + 1
                         b + i
                         b + i + 2
                         b + i + 1
                         b + i + 2
                         b + i ]
    }
    |> Array.ofSeq

let FullTriangles = Array.append Triangles EdgeFill

let UV = 
    let vs = ARRAY_SIZE |> int
    let w = float32 vs - 1.0f
    let h = float32 vs - 1.0f
    seq { 
        for i in 0.0f..h do
            for j in 0.0f..w do
                let r = j / w
                let u = i / h
                yield Vector2(r, u)
    }
    |> Array.ofSeq

//#endregion

////////////////////////////////////////////////////////////////////////////////
//#region Type Definitions
////////////////////////////////////////////////////////////////////////////////

type CubeFace = 
    | Front  = 0
    | Back   = 1
    | Left   = 2
    | Right  = 3
    | Top    = 4
    | Bottom = 5

type byte2 = 
    struct
        val x: byte
        val y: byte
        new(X, Y) = 
            { x = X
              y = Y }
    end

type Key = 
    { planetID: int
      face: CubeFace
      cellID: int64 }

let MakeKey(pID: int, f: CubeFace, cID: int64) = 
    { planetID = pID
      face = f
      cellID = cID }

//#endregion

#if INTERACTIVE
fsi.AddPrintTransformer(fun (b:byte2) -> (b.x, b.y) |> box)
fsi.AddPrintTransformer(fun (k:Key) -> (k.planetID, k.face, k.cellID) |> box)
#endif

////////////////////////////////////////////////////////////////////////////////
//#region State Persistence
////////////////////////////////////////////////////////////////////////////////

open System.Collections.Generic

let PlanetData = Dictionary<int, float32 * float32>()
let ReadyCache = Dictionary<Key, bool>()
let CornerCache = Dictionary<Key, Vector3 * Vector3 * Vector3>()
let VertexCache = Dictionary<Key, Vector3 []>()
let NormalCache = Dictionary<Key, Vector3 []>()
let TangentCache = Dictionary<Key, Vector4 []>()
let TextureCache = Dictionary<Key, Texture2D>()
let NormalMapCache = Dictionary<Key, Texture2D>()
let GameObjectRefs = Dictionary<Key, GameObject ref>()
let ObjectPool = Stack<GameObject>(OBJECT_POOL_SIZE)

let FillObjectPool(baseGameObject: GameObject) = 
    ObjectPool.Clear()
    Debug.Log("Filling Object Pool!")
    for i in 0..OBJECT_POOL_SIZE do
        let gameObject = GameObject.Instantiate(baseGameObject) :?> GameObject
        gameObject.SetActive(false)
        ObjectPool.Push(gameObject)

let ReadyQ(key: Key) = ReadyCache.TryGetValue(key) |> fst
let ActiveQ(key: Key) = GameObjectRefs.[key].Value.activeSelf
let Disable(key: Key) = GameObjectRefs.[key].Value.SetActive(false)
let Enable(key: Key) = GameObjectRefs.[key].Value.SetActive(true)

//#endregion

////////////////////////////////////////////////////////////////////////////////
//#region What have I done?
////////////////////////////////////////////////////////////////////////////////

type Evaluator(sequence: seq<unit>) = 
    let cacheSeq = Seq.cache sequence
    let mutable n = 1
    member this.Evaluate() = 
        try 
            Seq.nth n cacheSeq
            n <- n + 1
            true
        with :? System.ArgumentException -> false

type EvaluationClass() = 
    let queue = Queue<Evaluator>()
    let mutable currentEvaluator = Evaluator(seq { yield () })
    
    member this.Evaluate() = 
        let sw = System.Diagnostics.Stopwatch.StartNew()
        match currentEvaluator.Evaluate() with
        | true -> ()
        | false -> 
            if queue.Count > 0 then 
                currentEvaluator <- queue.Dequeue()
                printfn "Next evaluator"
            else printfn "Queue empty"
    
    member this.Enqueue(eval: Evaluator) = queue.Enqueue eval
    member this.Count = queue.Count

let EvaluationQueue = EvaluationClass()

//#endregion

////////////////////////////////////////////////////////////////////////////////
//#region OpenCL Host Code Initialization
////////////////////////////////////////////////////////////////////////////////

let OpenCLComputePlatform = 
    new ComputeContextPropertyList(ComputePlatform.Platforms.[0])
let OpenCLContext = 
    new ComputeContext(ComputeDeviceTypes.Default, OpenCLComputePlatform, null, 
                       System.IntPtr.Zero)
let path = @"E:\GDrive\PlanetTesting\Assets\Code\F#\Terrain.cl"
let kernelSource = System.IO.File.ReadAllText(path)
let OpenCLProgram = new ComputeProgram(OpenCLContext, [| kernelSource |])

OpenCLProgram.Build(null, null, null, System.IntPtr.Zero)

let OpenCLCommandQueue = 
    new ComputeCommandQueue(OpenCLContext, OpenCLContext.Devices.[0], 
                            ComputeCommandQueueFlags.None)
let OpenCLEvents = new ComputeEventList()
let CommandQueueBusy() = 
    Seq.forall 
        (fun (event: ComputeEventBase) -> 
        (event.Status = ComputeCommandExecutionStatus.Complete)) OpenCLEvents 
    |> not
let VertexValuesSplitKernel = OpenCLProgram.CreateKernel("VertexValuesSplit")
let VertexNormalsSplitKernel = OpenCLProgram.CreateKernel("VertexNormalsSplit")
let HeightMapSplitKernel = OpenCLProgram.CreateKernel("HeightMapSplit")
let NormalMapSplitKernel = OpenCLProgram.CreateKernel("NormalMapSplit")
let VertexValuesOutput = ref (Array.zeroCreate<Vector4> (4L * ARRAY_SIZE 
                                                         * ARRAY_SIZE
                                                         |> int))
let VertexNormalsOutput = ref (Array.zeroCreate<Vector4> (4L * ARRAY_SIZE 
                                                          * ARRAY_SIZE
                                                          |> int))
let HeightMapOutput = ref (Array.zeroCreate<byte> (4L * TEXTURE_SIZE 
                                                   * TEXTURE_SIZE
                                                   |> int))
let NormalMapOutput = ref (Array.zeroCreate<byte2> (4L * TEXTURE_SIZE 
                                                    * TEXTURE_SIZE
                                                    |> int))
let VertexValuesBuffer = 
    new ComputeBuffer<Vector4>(OpenCLContext, ComputeMemoryFlags.WriteOnly, 
                               4L * ARRAY_SIZE * ARRAY_SIZE)
let VertexNormalsBuffer = 
    new ComputeBuffer<Vector4>(OpenCLContext, ComputeMemoryFlags.WriteOnly, 
                               4L * ARRAY_SIZE * ARRAY_SIZE)
let HeightMapBuffer = 
    new ComputeBuffer<byte>(OpenCLContext, ComputeMemoryFlags.WriteOnly, 
                            4L * TEXTURE_SIZE * TEXTURE_SIZE)
let NormalMapBuffer = 
    new ComputeBuffer<byte2>(OpenCLContext, ComputeMemoryFlags.WriteOnly, 
                             4L * TEXTURE_SIZE * TEXTURE_SIZE)

//#endregion

////////////////////////////////////////////////////////////////////////////////
//#region Recursive Terrain Node Subdivision
////////////////////////////////////////////////////////////////////////////////
let CalculateMeshTangents(mesh: Mesh) = 
    let triangles = mesh.triangles
    let vertices = mesh.vertices
    let uv = mesh.uv
    let normals = mesh.normals
    let triangleCount = triangles.Length
    let vertexCount = vertices.Length
    let tan1 = Array.zeroCreate<Vector3> vertexCount
    let tan2 = Array.zeroCreate<Vector3> vertexCount
    let tangents = Array.zeroCreate<Vector4> vertexCount
    for a in 0..3..(triangleCount - 1) do
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
        let div = s1 * t2 - s2 * t1
        
        let r = match div with
                | 0.0f -> 0.0f
                | _    -> 1.0f / div
        
        let sdir = 
            Vector3
                ((t2 * x1 - t1 * x2) * r, (t2 * y1 - t1 * y2) * r, 
                 (t2 * z1 - t1 * z2) * r)
        let tdir = 
            Vector3
                ((s1 * x2 - s2 * x1) * r, (s1 * y2 - s2 * y1) * r, 
                 (s1 * z2 - s2 * z1) * r)
        tan1.[i1] <- tan1.[i1] + sdir
        tan1.[i2] <- tan1.[i2] + sdir
        tan1.[i3] <- tan1.[i3] + sdir
        tan2.[i1] <- tan2.[i1] + tdir
        tan2.[i2] <- tan2.[i2] + tdir
        tan2.[i3] <- tan2.[i3] + tdir
    for a in 0..(vertexCount - 1) do
        let nR = ref normals.[a]
        let tR = ref tan1.[a]
        Vector3.OrthoNormalize(nR, tR)
        let n, t = nR.Value, tR.Value
        tangents.[a].x <- t.x
        tangents.[a].y <- t.y
        tangents.[a].z <- t.z
        tangents.[a].w <- if (Vector3.Dot(Vector3.Cross(n, t), tan2.[a]) < 0.0f) then 
                              -1.0f
                          else 1.0f
    mesh.tangents <- tangents

let NewCorners(BL:Vector3, BR:Vector3, TL:Vector3) =
    let dX = 0.5f * (BR - BL)
    let dY = 0.5f * (TL - BL)
    let left = BL + dY
    let bottom = BL + dX
    let mid = left + dX
    let top = mid + dY
    let right = mid + dX

    ((left,   mid,    TL   ),
     (mid,    right,  top  ),
     (BL,     bottom, left ),
     (bottom, BR,     mid  ))

let Children(key:Key) =
    let i = key.cellID + 1L
    let bi = 4L * i
//    let TLi = bi + 0L
//    let TRi = bi + 1L
//    let BLi = bi + 2L
//    let BRi = bi + 3L
    let pID = key.planetID
    let face = key.face
    List.map (fun x -> MakeKey(pID, face, bi + x)) [0L..3L]
//    [MakeKey(pID, face, TLi);
//     MakeKey(pID, face, TRi);
//     MakeKey(pID, face, BLi);
//     MakeKey(pID, face, BRi)]

let Neighbors(key:Key) =
    let pID = key.planetID
    let face = key.face
    let cID = key.cellID
    let b = cID / 4L * 4L
    [MakeKey(pID, face, b + 0L);
     MakeKey(pID, face, b + 1L);
     MakeKey(pID, face, b + 2L);
     MakeKey(pID, face, b + 3L)]

let TopLevelQ(key:Key) = key.cellID < 4L

let Parent(key:Key) =
    if TopLevelQ(key) then key
    else let pID = key.planetID
         let face = key.face
         let cID = key.cellID
         let b = cID / 4L * 4L
         MakeKey(pID, face, b / 4L - 1L)

let SplitData(key:Key, BL:Vector3, BR:Vector3, TL:Vector3, rad:float32, amp:float32) =
        
        let start = Now()

        let pID = key.planetID
        let face = key.face
        let cID = key.cellID

        let i = cID + 1L
        let bi = 4L * i
        let TLi = bi + 0L
        let TRi = bi + 1L
        let BLi = bi + 2L
        let BRi = bi + 3L

        let TLKey = MakeKey(pID, face, TLi)
        let TRKey = MakeKey(pID, face, TRi)
        let BLKey = MakeKey(pID, face, BLi)
        let BRKey = MakeKey(pID, face, BRi)

        // The keys are immediately marked as not ready while the splitting computations are in progress
        ReadyCache.[TLKey] <- false
        ReadyCache.[TRKey] <- false
        ReadyCache.[BLKey] <- false
        ReadyCache.[BRKey] <- false

        // Send arguments to the GPU
        HeightMapSplitKernel.SetMemoryArgument(0, HeightMapBuffer)
        HeightMapSplitKernel.SetValueArgument(1, Vector4(BL.x, BL.y, BL.z))
        HeightMapSplitKernel.SetValueArgument(2, Vector4(BR.x, BR.y, BR.z))
        HeightMapSplitKernel.SetValueArgument(3, Vector4(TL.x, TL.y, TL.z))
        HeightMapSplitKernel.SetValueArgument(4, rad)

        NormalMapSplitKernel.SetMemoryArgument(0, HeightMapBuffer)
        NormalMapSplitKernel.SetMemoryArgument(1, NormalMapBuffer)

        VertexValuesSplitKernel.SetMemoryArgument(0, VertexValuesBuffer)
        VertexValuesSplitKernel.SetValueArgument(1, Vector4(BL.x, BL.y, BL.z))
        VertexValuesSplitKernel.SetValueArgument(2, Vector4(BR.x, BR.y, BR.z))
        VertexValuesSplitKernel.SetValueArgument(3, Vector4(TL.x, TL.y, TL.z))
        VertexValuesSplitKernel.SetValueArgument(4, rad)
        VertexValuesSplitKernel.SetValueArgument(5, amp)

        VertexNormalsSplitKernel.SetMemoryArgument(0, VertexNormalsBuffer)
        VertexNormalsSplitKernel.SetValueArgument(1, Vector4(BL.x, BL.y, BL.z))
        VertexNormalsSplitKernel.SetValueArgument(2, Vector4(BR.x, BR.y, BR.z))
        VertexNormalsSplitKernel.SetValueArgument(3, Vector4(TL.x, TL.y, TL.z))
        VertexNormalsSplitKernel.SetValueArgument(4, rad)
        VertexNormalsSplitKernel.SetValueArgument(5, amp)
        
        // Submit commands to the OpenCL command queues
        OpenCLCommandQueue.Execute(HeightMapSplitKernel,
                                   null,
                                   [|4L; TEXTURE_SIZE; TEXTURE_SIZE|],
                                   null,
                                   OpenCLEvents)

        OpenCLCommandQueue.ReadFromBuffer(HeightMapBuffer, HeightMapOutput, true, OpenCLEvents)
        OpenCLCommandQueue.Finish()

        OpenCLCommandQueue.Execute(NormalMapSplitKernel,
                                   null, 
                                   [|4L; TEXTURE_SIZE; TEXTURE_SIZE|],
                                   null, 
                                   OpenCLEvents)

        OpenCLCommandQueue.Execute(VertexValuesSplitKernel,
                                   null,
                                   [|4L; ARRAY_SIZE; ARRAY_SIZE|],
                                   null,
                                   OpenCLEvents)

        OpenCLCommandQueue.Execute(VertexNormalsSplitKernel,
                                   null,
                                   [|4L; ARRAY_SIZE; ARRAY_SIZE|],
                                   null,
                                   OpenCLEvents)

        // Read data back from the GPU
        OpenCLCommandQueue.ReadFromBuffer(NormalMapBuffer, NormalMapOutput, true, OpenCLEvents)
        OpenCLCommandQueue.ReadFromBuffer(VertexValuesBuffer, VertexValuesOutput, true, OpenCLEvents)
        OpenCLCommandQueue.ReadFromBuffer(VertexNormalsBuffer, VertexNormalsOutput, true, OpenCLEvents)
        OpenCLCommandQueue.Finish()

        let flattenedHeightMaps = HeightMapOutput.contents
        let flattenedNormalMaps = NormalMapOutput.contents
        let flattenedVertexValues = VertexValuesOutput.contents
        let flattenedVertexNormals = VertexNormalsOutput.contents

        
        
        let len1 = TEXTURE_SIZE * TEXTURE_SIZE |> int
        let len2 = ARRAY_SIZE   * ARRAY_SIZE   |> int
        let n = int TEXTURE_SIZE

        #if COMPILED

        // Heightmaps
        let hmTex = Array.map (fun (b:byte) -> Color32(b, b, b, 255uy))
    
        let hmBL = new Texture2D(n, n)
        let hmBR = new Texture2D(n, n)
        let hmTL = new Texture2D(n, n)
        let hmTR = new Texture2D(n, n)

        hmBL.SetPixels32(flattenedHeightMaps.[0      ..   len1 - 1] |> hmTex)
        hmBR.SetPixels32(flattenedHeightMaps.[len1   .. 2*len1 - 1] |> hmTex)
        hmTL.SetPixels32(flattenedHeightMaps.[2*len1 .. 3*len1 - 1] |> hmTex)
        hmTR.SetPixels32(flattenedHeightMaps.[3*len1 .. 4*len1 - 1] |> hmTex)

        hmBL.Apply()
        hmBR.Apply()
        hmTL.Apply()
        hmTR.Apply()

        hmBL.wrapMode <- TextureWrapMode.Clamp
        hmBR.wrapMode <- TextureWrapMode.Clamp
        hmTL.wrapMode <- TextureWrapMode.Clamp
        hmTR.wrapMode <- TextureWrapMode.Clamp

        TextureCache.[BLKey] <- hmBL
        TextureCache.[BRKey] <- hmBR
        TextureCache.[TLKey] <- hmTL
        TextureCache.[TRKey] <- hmTR

        //Normal maps
        let nmTex = Array.map (fun (b:byte2) -> Color32(b.x, b.y, 255uy, 255uy))

        let nmBL = new Texture2D(n, n)
        let nmBR = new Texture2D(n, n)
        let nmTL = new Texture2D(n, n)
        let nmTR = new Texture2D(n, n)

        nmBL.SetPixels32(flattenedNormalMaps.[0      ..   len1 - 1] |> nmTex)
        nmBR.SetPixels32(flattenedNormalMaps.[len1   .. 2*len1 - 1] |> nmTex)
        nmTL.SetPixels32(flattenedNormalMaps.[2*len1 .. 3*len1 - 1] |> nmTex)
        nmTR.SetPixels32(flattenedNormalMaps.[3*len1 .. 4*len1 - 1] |> nmTex)

//        //let dNorm = Color(0.5f, 0.5f, 1.0f, 1.0f)
//        let trim (nm:Texture2D) =
//            for i in 0 .. n do
//                nm.SetPixel(0, i, nm.GetPixel(1, i))
//                nm.SetPixel(i, 0, nm.GetPixel(i, 1))
//                nm.SetPixel(n-1, i, nm.GetPixel(n-2, i))
//                nm.SetPixel(i, n-1, nm.GetPixel(i, n-2))
//
//        trim nmBL
//        trim nmBR
//        trim nmTL
//        trim nmTR

        nmBL.Apply()
        nmBR.Apply()
        nmTL.Apply()
        nmTR.Apply()

        nmBL.wrapMode <- TextureWrapMode.Clamp
        nmBR.wrapMode <- TextureWrapMode.Clamp
        nmTL.wrapMode <- TextureWrapMode.Clamp
        nmTR.wrapMode <- TextureWrapMode.Clamp

        NormalMapCache.[BLKey] <- nmBL
        NormalMapCache.[BRKey] <- nmBR
        NormalMapCache.[TLKey] <- nmTL
        NormalMapCache.[TRKey] <- nmTR

        #endif

        //Vertex values
        let v4tov3 = Array.map (fun (v:Vector4) -> Vector3(v.x, v.y, v.z))

        let vvBL = flattenedVertexValues.[0      ..   len2 - 1] |> v4tov3
        let vvBR = flattenedVertexValues.[len2   .. 2*len2 - 1] |> v4tov3
        let vvTL = flattenedVertexValues.[2*len2 .. 3*len2 - 1] |> v4tov3
        let vvTR = flattenedVertexValues.[3*len2 .. 4*len2 - 1] |> v4tov3

        VertexCache.[TLKey] <- vvTL
        VertexCache.[TRKey] <- vvTR
        VertexCache.[BLKey] <- vvBL
        VertexCache.[BRKey] <- vvBR

        //Vertex normals
        let vnBL = flattenedVertexNormals.[0      ..   len2 - 1] |> v4tov3
        let vnBR = flattenedVertexNormals.[len2   .. 2*len2 - 1] |> v4tov3
        let vnTL = flattenedVertexNormals.[2*len2 .. 3*len2 - 1] |> v4tov3
        let vnTR = flattenedVertexNormals.[3*len2 .. 4*len2 - 1] |> v4tov3

        NormalCache.[TLKey] <- vnTL
        NormalCache.[TRKey] <- vnTR
        NormalCache.[BLKey] <- vnBL
        NormalCache.[BRKey] <- vnBR

        //New corners

        let (TLc, TRc, BLc, BRc) = NewCorners(BL, BR, TL)
//        let dX = 0.5f * (BR - BL)
//        let dY = 0.5f * (TL - BL)
//        let left = BL + dY
//        let bottom = BL + dX
//        let mid = left + dX
//        let top = mid + dY
//        let right = mid + dX

        CornerCache.[TLKey] <- TLc
        CornerCache.[TRKey] <- TRc
        CornerCache.[BLKey] <- BLc
        CornerCache.[BRKey] <- BRc

        //Subnodes are now ready for use
        ReadyCache.[TLKey] <- true
        ReadyCache.[TRKey] <- true
        ReadyCache.[BLKey] <- true
        ReadyCache.[BRKey] <- true

        ElapsedTime(start, "openCL")

        ()

let SplitEvaluator(key:Key, BL:Vector3, BR:Vector3, TL:Vector3, rad:float32, amp:float32) =
        let eval = Evaluator(seq{

            let pID = key.planetID
            let face = key.face
            let cID = key.cellID

            let i = cID + 1L
            let bi = 4L * i
            let TLi = bi + 0L
            let TRi = bi + 1L
            let BLi = bi + 2L
            let BRi = bi + 3L

            let TLKey = MakeKey(pID, face, TLi)
            let TRKey = MakeKey(pID, face, TRi)
            let BLKey = MakeKey(pID, face, BLi)
            let BRKey = MakeKey(pID, face, BRi)

            // The keys are immediately marked as not ready while the splitting computations are in progress
            printfn "Marking as not ready"
            ReadyCache.[TLKey] <- false
            ReadyCache.[TRKey] <- false
            ReadyCache.[BLKey] <- false
            ReadyCache.[BRKey] <- false

            // Send arguments to the GPU
            HeightMapSplitKernel.SetMemoryArgument(0, HeightMapBuffer)
            HeightMapSplitKernel.SetValueArgument(1, Vector4(BL.x, BL.y, BL.z))
            HeightMapSplitKernel.SetValueArgument(2, Vector4(BR.x, BR.y, BR.z))
            HeightMapSplitKernel.SetValueArgument(3, Vector4(TL.x, TL.y, TL.z))
            HeightMapSplitKernel.SetValueArgument(4, rad)

            NormalMapSplitKernel.SetMemoryArgument(0, HeightMapBuffer)
            NormalMapSplitKernel.SetMemoryArgument(1, NormalMapBuffer)

            VertexValuesSplitKernel.SetMemoryArgument(0, VertexValuesBuffer)
            VertexValuesSplitKernel.SetValueArgument(1, Vector4(BL.x, BL.y, BL.z))
            VertexValuesSplitKernel.SetValueArgument(2, Vector4(BR.x, BR.y, BR.z))
            VertexValuesSplitKernel.SetValueArgument(3, Vector4(TL.x, TL.y, TL.z))
            VertexValuesSplitKernel.SetValueArgument(4, rad)
            VertexValuesSplitKernel.SetValueArgument(5, amp)

            VertexNormalsSplitKernel.SetMemoryArgument(0, VertexNormalsBuffer)
            VertexNormalsSplitKernel.SetValueArgument(1, Vector4(BL.x, BL.y, BL.z))
            VertexNormalsSplitKernel.SetValueArgument(2, Vector4(BR.x, BR.y, BR.z))
            VertexNormalsSplitKernel.SetValueArgument(3, Vector4(TL.x, TL.y, TL.z))
            VertexNormalsSplitKernel.SetValueArgument(4, rad)
            VertexNormalsSplitKernel.SetValueArgument(5, amp)
            
            yield ()
            // Submit commands to the OpenCL command queues
            OpenCLCommandQueue.Execute(HeightMapSplitKernel,
                                       null,
                                       [|4L; TEXTURE_SIZE; TEXTURE_SIZE|],
                                       null,
                                       OpenCLEvents)

            yield ()

            OpenCLCommandQueue.ReadFromBuffer(HeightMapBuffer, HeightMapOutput, true, OpenCLEvents)

            yield ()

            OpenCLCommandQueue.Finish()
            
            yield ()

            OpenCLCommandQueue.Execute(NormalMapSplitKernel,
                                       null, 
                                       [|4L; TEXTURE_SIZE; TEXTURE_SIZE|],
                                       null, 
                                       OpenCLEvents)
            
            yield ()

            OpenCLCommandQueue.Execute(VertexValuesSplitKernel,
                                       null,
                                       [|4L; ARRAY_SIZE; ARRAY_SIZE|],
                                       null,
                                       OpenCLEvents)
            
            yield ()

            OpenCLCommandQueue.Execute(VertexNormalsSplitKernel,
                                       null,
                                       [|4L; ARRAY_SIZE; ARRAY_SIZE|],
                                       null,
                                       OpenCLEvents)

            yield ()
            // Read data back from the GPU
            OpenCLCommandQueue.ReadFromBuffer(NormalMapBuffer, NormalMapOutput, true, OpenCLEvents)

            yield ()

            OpenCLCommandQueue.ReadFromBuffer(VertexValuesBuffer, VertexValuesOutput, true, OpenCLEvents)

            yield ()

            OpenCLCommandQueue.ReadFromBuffer(VertexNormalsBuffer, VertexNormalsOutput, true, OpenCLEvents)

            yield ()

            OpenCLCommandQueue.Finish()

            yield ()

            printfn "OpenCL stuff done!"

            let flattenedHeightMaps = HeightMapOutput.contents
            let flattenedNormalMaps = NormalMapOutput.contents
            let flattenedVertexValues = VertexValuesOutput.contents
            let flattenedVertexNormals = VertexNormalsOutput.contents
        
            let len1 = TEXTURE_SIZE * TEXTURE_SIZE |> int
            let len2 = ARRAY_SIZE   * ARRAY_SIZE   |> int
            let n = int TEXTURE_SIZE

            #if COMPILED

            // Heightmaps
            let hmTex = Array.map (fun (b:byte) -> Color32(b, b, b, 255uy))
            
            let hmBL = new Texture2D(n, n)
            let hmBR = new Texture2D(n, n)
            let hmTL = new Texture2D(n, n)
            let hmTR = new Texture2D(n, n)

            hmBL.SetPixels32(flattenedHeightMaps.[0      ..   len1 - 1] |> hmTex)
            hmBR.SetPixels32(flattenedHeightMaps.[len1   .. 2*len1 - 1] |> hmTex)
            hmTL.SetPixels32(flattenedHeightMaps.[2*len1 .. 3*len1 - 1] |> hmTex)
            hmTR.SetPixels32(flattenedHeightMaps.[3*len1 .. 4*len1 - 1] |> hmTex)

            yield ()

            hmBL.Apply()
            hmBR.Apply()
            hmTL.Apply()
            hmTR.Apply()

            hmBL.wrapMode <- TextureWrapMode.Clamp
            hmBR.wrapMode <- TextureWrapMode.Clamp
            hmTL.wrapMode <- TextureWrapMode.Clamp
            hmTR.wrapMode <- TextureWrapMode.Clamp

            TextureCache.[BLKey] <- hmBL
            TextureCache.[BRKey] <- hmBR
            TextureCache.[TLKey] <- hmTL
            TextureCache.[TRKey] <- hmTR
            yield ()


            //Normal maps
            let nmTex = Array.map (fun (b:byte2) -> Color32(b.x, b.y, 255uy, 255uy))

            let nmBL = new Texture2D(n, n)
            let nmBR = new Texture2D(n, n)
            let nmTL = new Texture2D(n, n)
            let nmTR = new Texture2D(n, n)

            nmBL.SetPixels32(flattenedNormalMaps.[0      ..   len1 - 1] |> nmTex)
            nmBR.SetPixels32(flattenedNormalMaps.[len1   .. 2*len1 - 1] |> nmTex)
            nmTL.SetPixels32(flattenedNormalMaps.[2*len1 .. 3*len1 - 1] |> nmTex)
            nmTR.SetPixels32(flattenedNormalMaps.[3*len1 .. 4*len1 - 1] |> nmTex)

            yield ()
    //        //let dNorm = Color(0.5f, 0.5f, 1.0f, 1.0f)
    //        let trim (nm:Texture2D) =
    //            for i in 0 .. n do
    //                nm.SetPixel(0, i, nm.GetPixel(1, i))
    //                nm.SetPixel(i, 0, nm.GetPixel(i, 1))
    //                nm.SetPixel(n-1, i, nm.GetPixel(n-2, i))
    //                nm.SetPixel(i, n-1, nm.GetPixel(i, n-2))
    //
    //        trim nmBL
    //        trim nmBR
    //        trim nmTL
    //        trim nmTR

            nmBL.Apply()
            nmBR.Apply()
            nmTL.Apply()
            nmTR.Apply()

            nmBL.wrapMode <- TextureWrapMode.Clamp
            nmBR.wrapMode <- TextureWrapMode.Clamp
            nmTL.wrapMode <- TextureWrapMode.Clamp
            nmTR.wrapMode <- TextureWrapMode.Clamp
            
            NormalMapCache.[BLKey] <- nmBL
            NormalMapCache.[BRKey] <- nmBR
            NormalMapCache.[TLKey] <- nmTL
            NormalMapCache.[TRKey] <- nmTR

            yield ()
            #endif
            
            //Vertex values

            let v4tov3 = Array.map (fun (v:Vector4) -> Vector3(v.x, v.y, v.z))

            let vvBL = flattenedVertexValues.[0      ..   len2 - 1] |> v4tov3
            let vvBR = flattenedVertexValues.[len2   .. 2*len2 - 1] |> v4tov3
            let vvTL = flattenedVertexValues.[2*len2 .. 3*len2 - 1] |> v4tov3
            let vvTR = flattenedVertexValues.[3*len2 .. 4*len2 - 1] |> v4tov3


            VertexCache.[TLKey] <- vvTL
            VertexCache.[TRKey] <- vvTR
            VertexCache.[BLKey] <- vvBL
            VertexCache.[BRKey] <- vvBR
            
            yield ()
            //Vertex normals

            let vnBL = flattenedVertexNormals.[0      ..   len2 - 1] |> v4tov3
            let vnBR = flattenedVertexNormals.[len2   .. 2*len2 - 1] |> v4tov3
            let vnTL = flattenedVertexNormals.[2*len2 .. 3*len2 - 1] |> v4tov3
            let vnTR = flattenedVertexNormals.[3*len2 .. 4*len2 - 1] |> v4tov3

            NormalCache.[TLKey] <- vnTL
            NormalCache.[TRKey] <- vnTR
            NormalCache.[BLKey] <- vnBL
            NormalCache.[BRKey] <- vnBR
            
            //New corners

            let (TLc, TRc, BLc, BRc) = NewCorners(BL, BR, TL)
    //        let dX = 0.5f * (BR - BL)
    //        let dY = 0.5f * (TL - BL)
    //        let left = BL + dY
    //        let bottom = BL + dX
    //        let mid = left + dX
    //        let top = mid + dY
    //        let right = mid + dX

            CornerCache.[TLKey] <- TLc
            CornerCache.[TRKey] <- TRc
            CornerCache.[BLKey] <- BLc
            CornerCache.[BRKey] <- BRc

            //Subnodes are now ready for use
            printfn "Marking as ready"
            ReadyCache.[TLKey] <- true
            ReadyCache.[TRKey] <- true
            ReadyCache.[BLKey] <- true
            ReadyCache.[BRKey] <- true
            
            printfn "Other stuff done!"

            })
        EvaluationQueue.Enqueue(eval)


let NewGameObject(key:Key) =
    let pID = key.planetID
    let face = key.face
    let cID = key.cellID

    let name = "p" + (string pID) + "_" 
                   + (string face) + "_" 
                   + (string cID)

    let vertices = VertexCache.[key]
    let normals = NormalCache.[key]
    let texture = TextureCache.[key]
    let normalMap = NormalMapCache.[key]

    let gameObject = new GameObject(name)

    let mf = gameObject.AddComponent<MeshFilter>()
    let mr = gameObject.AddComponent<MeshRenderer>()
    let material = new Material(Shader.Find("Unpacked Bumped Diffuse"))

    gameObject.renderer.material <- material

    let mesh = mf.mesh
    mesh.vertices <- vertices
    mesh.triangles <- Triangles
    mesh.uv <- UV
    mesh.normals <- normals

    CalculateMeshTangents(mesh)
    mesh.RecalculateBounds()
    mesh.triangles <- FullTriangles

    gameObject.renderer.material.SetTexture("_BumpMap", normalMap)
    gameObject.renderer.material.SetTexture("_MainTex", texture)

    let offset = 1.5f / (float32 TEXTURE_SIZE)
    let tiling = 1.0f - 2.0f * offset

    gameObject.renderer.material.SetTextureOffset("_MainTex", Vector2(offset, offset))
    gameObject.renderer.material.SetTextureScale("_MainTex", Vector2(tiling, tiling))
    gameObject.renderer.material.SetTextureOffset("_BumpMap", Vector2(offset, offset))
    gameObject.renderer.material.SetTextureScale("_BumpMap", Vector2(tiling, tiling))

    gameObject.SetActive(true)

    let refObj = ref gameObject
    GameObjectRefs.[key] <- refObj

    ()

let BuildGameObject(key:Key) =
    let pID = key.planetID
    let face = key.face
    let cID = key.cellID

    let name = "p" + (string pID) + "_" 
                   + (string face) + "_" 
                   + (string cID)

    let vertices = VertexCache.[key]
    let normals = NormalCache.[key]
    let texture = TextureCache.[key]
    let normalMap = NormalMapCache.[key]

    #if COMPILED

    let gameObject = ObjectPool.Pop()

    gameObject.name <- name

    let mesh = gameObject.GetComponent<MeshFilter>().mesh
    //mesh.Clear()

    mesh.vertices <- vertices
    mesh.triangles <- Triangles
    mesh.normals <- normals

    CalculateMeshTangents(mesh)
    mesh.RecalculateBounds()
    mesh.triangles <- FullTriangles

    gameObject.renderer.material.SetTexture("_BumpMap", normalMap)
    gameObject.renderer.material.SetTexture("_MainTex", texture)

    let offset = 1.5f / (float32 TEXTURE_SIZE)
    let tiling = 1.0f - 2.0f * offset

    gameObject.renderer.material.SetTextureOffset("_MainTex", Vector2(offset, offset))
    gameObject.renderer.material.SetTextureScale("_MainTex", Vector2(tiling, tiling))
    gameObject.renderer.material.SetTextureOffset("_BumpMap", Vector2(offset, offset))
    gameObject.renderer.material.SetTextureScale("_BumpMap", Vector2(tiling, tiling))

    //gameObject.renderer.material.mainTexture.wrapMode <- TextureWrapMode.Clamp

    gameObject.SetActive(true)

    let refObj = ref gameObject
    GameObjectRefs.[key] <- refObj

    #endif

    ()


let DistanceToNode(key:Key) =
    #if COMPILED
    let boundingBox = GameObjectRefs.[key].Value.GetComponent<MeshFilter>().mesh.bounds
    let minV, maxV = boundingBox.min, boundingBox.max
    let cameraPos = Camera.main.transform.position
    let closestPoint = Vector3(Mathf.Clamp(cameraPos.x, minV.x, maxV.x),
                               Mathf.Clamp(cameraPos.y, minV.y, maxV.y),
                               Mathf.Clamp(cameraPos.z, minV.z, maxV.z))
    Mathf.Max(0.0001f, Vector3.Distance(cameraPos, closestPoint))
    #else
    1.0f
    #endif

let PrintKey(key:Key) =
    let pID = (string key.planetID)
    let f = (string key.face)
    let cID = (string key.cellID)
    #if COMPILED
    Debug.Log("Key: " + pID + "_" + f + "_" + cID)
    #else
    printfn "%s" ("Key: " + pID + "_" + f + "_" + cID)
    #endif

let DistanceError(key:Key) =
    let (BL, BR, _) = CornerCache.[key]
    //TODO: Remove 50.0 as constant radius and use argument instead
    let d = 50.0f * Vector3.Distance(BL, BR)
    let D = DistanceToNode(key)
    d / D


let ClosestNode(currentKeys : Key list) = List.minBy DistanceToNode currentKeys

//let DistanceError(key:Key) =
//    let (BL, BR, _) = CornerCache.[key]
//    let delta = Vector3.Distance(BL, BR)
//    let boundingBox = GameObjectRefs.[key].Value.GetComponent<MeshFilter>().mesh.bounds
//    let d = boundingBox.SqrDistance(Camera.main.transform.position) |> sqrt
//    let b = boundingBox.size
//    let s = max b.x (max b.y b.z)
//    (2.0f * atan(s / (2.0f * d))) / Mathf.PI


let Subdivide(key: Key, rad: float32, amp: float32) = 
    let ch = Children(key)
    match List.forall ReadyQ ch with
    | true ->
        #if COMPILED 
        List.iter BuildGameObject ch
        Disable(key)
        #endif
        
        ch
    | false -> 
        let bl, br, tl = CornerCache.[key]
        SplitData(key, bl, br, tl, rad, amp)
        [ key ]

let SubdivideQueued(key: Key, rad: float32, amp: float32) = 
    let ch = Children(key)
    match List.forall ReadyQ ch with
    | true ->
        #if COMPILED 
        List.iter BuildGameObject ch
        Disable(key)
        #endif
        
        ch
    | false -> 
        let bl, br, tl = CornerCache.[key]
        SplitEvaluator(key, bl, br, tl, rad, amp)
        [ key ]

let Merge(key: Key) = 
    match key.cellID > 3L with
    | false -> key
    | true -> 
        Neighbors(key) |> List.iter Disable
        let p = Parent(key)
        Enable(p)
        p
    
//#endregion

let CurrentKeys(initialKeys: Key list) =
    let rec findActive =
        function
        | [] -> []
        | (k :: ks) ->
            match ActiveQ k with
            | true -> k :: (findActive ks)
            | false ->
                match Children k with
                | a :: b :: c :: d :: [] -> findActive (a :: b :: c :: d :: ks)
                | _ -> failwith "YOU DUN GOOFED!"
    findActive initialKeys

//TODO: Remove rad=100.0 and amp=1.0 as constants and use arguments instead
//let rec ProcessKeys (t:float32) =
//    function
//    | []      -> []
//    | (k::ks) -> match ActiveQ(k) with
//                 | false -> ProcessKeys t ks
//                 | true  -> match DistanceError k with
//                            | e when e < t/4.0f -> (Merge k)::(ProcessKeys t ks)
//                            | e when e > t -> (sd k) @ (ProcessKeys t ks)
//                            | _ -> k::(ProcessKeys t ks)

//TODO: Remove rad=100.0 and amp=1.0 as fixed parameters in Subdivide
let rec ProcessKeys(t: float32) = 
    function 
    | [] -> []
    | (k :: ks) -> 
        #if COMPILED 
        let x = ActiveQ(k)
        #else
        let x = ReadyQ(k)
        #endif
        match x with
        | false -> ProcessKeys t ks
        | true -> 
            match (DistanceError k, DistanceError(Parent(k))) with
            | (d, _) when d > t -> Subdivide(k, 100.0f, 1.0f) @ (ProcessKeys t ks)
            | (_, p) when p < t -> (Merge k) :: (ProcessKeys t ks)
            | _ -> k :: (ProcessKeys t ks)

let rec ProcessKeysQueued(t: float32) = 
    function 
    | [] -> []
    | (k :: ks) -> 
        match ActiveQ(k) with
        | false -> ProcessKeysQueued t ks
        | true -> 
            let pk = ProcessKeysQueued t ks
            match (DistanceError k, DistanceError(Parent(k))) with
            | (d, _) when d > t -> SubdivideQueued(k, 100.0f, 1.0f) @ pk
            | (_, p) when p < t -> (Merge k) :: pk
            | _ -> k :: pk

let mutable processed = false

let InitializeStepFrame (threshold: float32) (keyList: Key list) = 
    let proc = 
        Evaluator(seq { 
                      let _ = ProcessKeysQueued threshold keyList
                      processed <- true
                      yield ()
                  })
    EvaluationQueue.Enqueue(proc)

let StepFrame2 (threshold: float32) (keyList: Key list) = 
    match CommandQueueBusy() with
    | true -> ()
    | false -> 
        OpenCLEvents.Clear()
        EvaluationQueue.Evaluate()
    if processed then 
        let keyList0 = ProcessKeysQueued threshold keyList
        processed <- false
        let proc = 
            Evaluator(seq { 
                          let _ = ProcessKeysQueued threshold keyList0
                          processed <- true
                          yield ()
                      })
        EvaluationQueue.Enqueue(proc)
        keyList0
    else keyList

let StepFrame (t:float32) (keyList:Key list) =
    let keyList0 = ProcessKeysQueued t keyList
    match CommandQueueBusy() with
        | true  -> keyList0
        | false -> OpenCLEvents.Clear()
                   EvaluationQueue.Evaluate()
                   keyList0

let ProcessOnce(keyList:Key list) =
    let newKeys = List.collect (fun (k:Key) -> Subdivide(k, 100.0f, 1.0f)) keyList
                  |> Seq.distinct
                  |> List.ofSeq
    List.iter PrintKey newKeys
    newKeys

let KeysReady(keyList: Key list) = List.forall ReadyQ keyList

let WriteMeshData(gameObject:GameObject) =
    let mesh = gameObject.GetComponent<MeshFilter>().mesh
    let vertices = mesh.vertices
    let normals = mesh.normals
    let tangents = mesh.tangents
    let triangles = mesh.triangles
    let uv = mesh.uv
    let format2 (v:Vector2) = (string v.x) + ", " + (string v.y)
    let format3 (v:Vector3) = (string v.x) + ", " + (string v.y) + ", " + (string v.z)
    let format4 (v:Vector4) = (string v.x) + ", " + (string v.y) + ", " + (string v.z) + ", " + (string v.w)
    let path = @"E:\GDrive\PlanetTesting\Extra Stuff\data\" + (string System.DateTime.Now.Ticks) + "_"
    System.IO.File.WriteAllLines(path + "vertices.csv", Array.map format3 vertices)
    System.IO.File.WriteAllLines(path + "normals.csv", Array.map format3 normals)
    System.IO.File.WriteAllLines(path + "tangents.csv", Array.map format4 tangents)
    System.IO.File.WriteAllLines(path + "triangles.csv", Array.map string triangles)
    System.IO.File.WriteAllLines(path + "uv.csv", Array.map format2 uv)


////////////////////////////////////////////////////////////////////////////////
//#region Testing
////////////////////////////////////////////////////////////////////////////////

let InitializePlanetCache(pID:int, rad:float32, amp:float32) = 
    let init(key:Key, BL, BR, TL, rad, amp) =
        SplitData(key, BL, BR, TL, rad, amp)

    init({planetID = pID; face = CubeFace.Front; cellID = -1L},
            Vector3(-1.0f, -1.0f,  1.0f), 
            Vector3( 1.0f, -1.0f,  1.0f), 
            Vector3(-1.0f,  1.0f,  1.0f),
            rad, amp)

    init({planetID = pID; face = CubeFace.Top; cellID = -1L},
            Vector3(-1.0f,  1.0f,  1.0f), 
            Vector3( 1.0f,  1.0f,  1.0f), 
            Vector3(-1.0f,  1.0f, -1.0f),
            rad, amp)

    init({planetID = pID; face = CubeFace.Bottom; cellID = -1L},
            Vector3(-1.0f, -1.0f, -1.0f), 
            Vector3( 1.0f, -1.0f, -1.0f), 
            Vector3(-1.0f, -1.0f,  1.0f),
            rad, amp)

    init({planetID = pID; face = CubeFace.Left; cellID = -1L},
            Vector3(-1.0f, -1.0f, -1.0f), 
            Vector3(-1.0f, -1.0f,  1.0f), 
            Vector3(-1.0f,  1.0f, -1.0f),
            rad, amp)

    init({planetID = pID; face = CubeFace.Right; cellID = -1L},
            Vector3( 1.0f, -1.0f,  1.0f), 
            Vector3( 1.0f, -1.0f, -1.0f), 
            Vector3( 1.0f,  1.0f,  1.0f),
            rad, amp)

    init({planetID = pID; face = CubeFace.Back; cellID = -1L},
            Vector3( 1.0f, -1.0f, -1.0f), 
            Vector3(-1.0f, -1.0f, -1.0f), 
            Vector3( 1.0f,  1.0f, -1.0f),
            rad, amp)

    [
        MakeKey(0, CubeFace.Front, 0L)
        MakeKey(0, CubeFace.Front, 1L)
        MakeKey(0, CubeFace.Front, 2L)
        MakeKey(0, CubeFace.Front, 3L)

        MakeKey(0, CubeFace.Top, 0L)
        MakeKey(0, CubeFace.Top, 1L)
        MakeKey(0, CubeFace.Top, 2L)
        MakeKey(0, CubeFace.Top, 3L)

        MakeKey(0, CubeFace.Bottom, 0L)
        MakeKey(0, CubeFace.Bottom, 1L)
        MakeKey(0, CubeFace.Bottom, 2L)
        MakeKey(0, CubeFace.Bottom, 3L)

        MakeKey(0, CubeFace.Left, 0L)
        MakeKey(0, CubeFace.Left, 1L)
        MakeKey(0, CubeFace.Left, 2L)
        MakeKey(0, CubeFace.Left, 3L)

        MakeKey(0, CubeFace.Right, 0L)
        MakeKey(0, CubeFace.Right, 1L)
        MakeKey(0, CubeFace.Right, 2L)
        MakeKey(0, CubeFace.Right, 3L)

        MakeKey(0, CubeFace.Back, 0L)
        MakeKey(0, CubeFace.Back, 1L)
        MakeKey(0, CubeFace.Back, 2L)
        MakeKey(0, CubeFace.Back, 3L)
    ]


let KeyArray (keys : Key list) = Array.ofList keys

let SaveTextures(keys:Key[]) =
    for key in keys do
        let pID = key.planetID |> string
        let face = key.face |> string
        let cID = key.cellID |> string

        let hm = TextureCache.[key]
        System.IO.File.WriteAllBytes(Application.dataPath + "/../" + pID + face + cID + "hm.png", hm.EncodeToPNG())

        let nm = NormalMapCache.[key]
        System.IO.File.WriteAllBytes(Application.dataPath + "/../" + pID + face + cID + "nm.png", nm.EncodeToPNG())

//#endregion
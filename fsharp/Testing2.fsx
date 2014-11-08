#r @"E:\GDrive\PlanetTesting\FSharp Project Folder\UnityPlanetGenerator\Cloo.dll"
#r @"E:\GDrive\PlanetTesting\FSharp Project Folder\UnityPlanetGenerator\UnityEngine.dll"
#load "Terrain/Config.fs"
#load "Terrain/TerrainTypes.fs"
#load "Terrain/Cache.fs"
#load "Terrain/OpenCL.fs"
#load "Terrain/TerrainEngine.fs"
//
//open UnityEngine
//open TerrainTypes
//open OpenCL
//
//
//
//let key = MakeKey(0, CubeFace.Front,  1L)
//let BL, BR, TL = Corners(key)
//let rad, amp = 100.0f, 1.0f
//
//let vertices = Array.zeroCreate<Vector3> (Config.VertexArraySize |> int)
//let normals = Array.zeroCreate<Vector3> (Config.VertexArraySize |> int)
//let tangents = Array.zeroCreate<Vector4> (Config.VertexArraySize |> int)
//let texData = Array.zeroCreate<byte4> (Config.TextureArraySize |> int)
//let nrmData = Array.zeroCreate<byte4> (Config.TextureArraySize |> int)
//
//let vertRef = ref vertices
//let normRef = ref normals
//let tangRef = ref tangents
//let hmDataRef = ref texData
//let nmDataRef = ref nrmData
//
//OpenCL.UpdateRefs(vertRef, normRef, tangRef, hmDataRef, nmDataRef, BL, BR, TL, rad, amp)
//
//hmDataRef.contents


//
//let key = MakeKey(0, CubeFace.Front, 0L)
//let rad, amp = 100.0f, 1.0f
//
//let NewGameObject(key:Key) =
//
//    let pID = key.planetID
//    let face = key.face
//    let cID = key.cellID
//
//    let name = "p" + (string pID) + "_" 
//                   + (string face) + "_" 
//                   + (string cID)
//
//    let gameObject = new GameObject(name)
//
//    let mf = gameObject.AddComponent<MeshFilter>()
//    let mr = gameObject.AddComponent<MeshRenderer>()
//    gameObject.renderer.material <- new Material(Shader.Find("Unpacked Bumped Diffuse"))
//    let mesh = mf.mesh
//
//    mesh.vertices <- Array.zeroCreate<Vector3> (Config.VertexArraySize |> int)
//    mesh.normals <- Array.zeroCreate<Vector3> (Config.VertexArraySize |> int)
//    mesh.tangents <- Array.zeroCreate<Vector4> (Config.VertexArraySize |> int)
//    mesh.triangles <- TerrainTypes.Triangles
//    mesh.uv <- TerrainTypes.UV
//
//    let (BL, BR, TL) = Corners(key)
//    let mTask, mCont = UpdateMesh(ref mesh.vertices, ref mesh.normals, ref mesh.tangents, BL, BR, TL, rad, amp)
//    mCont.Publish.Add(mesh.RecalculateBounds)
//    Async.Start(mTask)
//
//    let normalMap = new Texture2D(Config.TextureRes, Config.TextureRes)
//    let texture = new Texture2D(Config.TextureRes, Config.TextureRes)
//
//    let onCompletion() =
//        gameObject.renderer.material.SetTexture("_BumpMap", normalMap)
//        gameObject.renderer.material.SetTexture("_MainTex", texture)
//
//        let offset = 1.5f / (float32 Config.TextureRes)
//        let tiling = 1.0f - 2.0f * offset
//
//        gameObject.renderer.material.SetTextureOffset("_MainTex", Vector2(offset, offset))
//        gameObject.renderer.material.SetTextureScale("_MainTex", Vector2(tiling, tiling))
//        gameObject.renderer.material.SetTextureOffset("_BumpMap", Vector2(offset, offset))
//        gameObject.renderer.material.SetTextureScale("_BumpMap", Vector2(tiling, tiling))
//
//        gameObject.SetActive(true)
//
//        Cache.GameObjectRefs.[key] <- ref gameObject
//
//    let tTask, tCont = UpdateTextures(ref texture, ref normalMap, BL, BR, TL, rad)
//    tCont.Publish.Add(onCompletion)
//    Async.Start(tTask)
//
//    ()
//
//
//
//
//#time "on"
//
//let key = MakeKey(0, CubeFace.Front, 654564687460051L)
//
//Corners(key)
//
//open UnityEngine
//open OpenCL
//
//////////////////////////////////////////////////////////////////////////////////
//// Inputs
//////////////////////////////////////////////////////////////////////////////////
//
//let BL, BR, TL = Vector3(-1.0f, -1.0f,  1.0f), 
//                 Vector3( 1.0f, -1.0f,  1.0f), 
//                 Vector3(-1.0f,  1.0f,  1.0f)
//let rad = 100.0f
//let amp = 1.0f
//
//let vertices = Array.zeroCreate<Vector3> (OpenCL.vertexArraySize |> int)
//let normals = Array.zeroCreate<Vector3> (OpenCL.vertexArraySize |> int)
//let tangents = Array.zeroCreate<Vector4> (OpenCL.vertexArraySize |> int)
//
//////////////////////////////////////////////////////////////////////////////////
//// Testing
//////////////////////////////////////////////////////////////////////////////////
//
//#time "on"
//
//
//let (task, completionEvent) = OpenCL.UpdateMesh(ref vertices, ref normals, ref tangents, BL, BR, TL, rad, amp)
//let continuation = fun () -> printfn "it worked!"
//
//completionEvent.Publish.Add(continuation)
//Async.Start(task)
//
//let WriteVector3Array(vertices:Vector3[], name:string) =
//    let format (v:Vector3) =
//        (string v.x) + ", " + (string v.y) + ", " + (string v.z)
//    let exportPath = @"E:\GDrive\PlanetTesting\Extra Stuff\data\"
//    System.IO.File.WriteAllLines(exportPath + name + ".csv", Array.map format vertices)
//
//let WriteVector4Array(vertices:Vector4[], name:string) =
//    let format (v:Vector4) =
//        (string v.x) + ", " + (string v.y) + ", " + (string v.z) + ", " + (string v.w)
//    let exportPath = @"E:\GDrive\PlanetTesting\Extra Stuff\data\"
//    System.IO.File.WriteAllLines(exportPath + name + ".csv", Array.map format vertices)
//
//WriteVector3Array(vertices, "vertices")
//WriteVector3Array(normals, "normals")
//WriteVector4Array(tangents, "tangents")
//
//let WriteBMP(imgArray:byte[], name:string) = 
//    let color(r:byte, g:byte, b:byte) = System.Drawing.Color.FromArgb(int r, int g, int b)
//    let bmp = new System.Drawing.Bitmap(OpenCL.textureRes, OpenCL.textureRes)
//    for i in 0 .. OpenCL.textureRes - 1 do
//        for j in 0 .. OpenCL.textureRes - 1 do
//            let k = OpenCL.textureRes * i + j
//            let c = color(imgArray.[3 * k], imgArray.[3 * k + 1], imgArray.[3 * k + 2])
//            bmp.SetPixel(i, j, c)
//    bmp.Save(@"E:\GDrive\PlanetTesting\Extra Stuff\data\" + name + ".bmp")
//
//WriteBMP(heightMap, "heightMap")
//WriteBMP(normalMap, "normalMap")


////open TE
//open UnityEngine
//open Cloo
//
//let ARRAY_SIZE = 256L
//
//#if INTERACTIVE
//fsi.AddPrintTransformer(fun (v:Vector3) -> (v.x, v.y, v.z) |> box)
//fsi.AddPrintTransformer(fun (v:Vector4) -> (v.x, v.y, v.z, v.w) |> box)
//#endif
//
////type OpenCL =
////    static member Platform = new ComputeContextPropertyList(ComputePlatform.Platforms.[0])
////    static member Context = new ComputeContext(ComputeDeviceTypes.Default, OpenCL.Platform, null, System.IntPtr.Zero)
////
////    static member Program = 
////        let path = @"E:\GDrive\PlanetTesting\FSharp Project Folder\UnityPlanetGenerator\UnityPlanetGenerator\Terrain.cl"
////        let kernelSource = System.IO.File.ReadAllText(path)
////        let program = new ComputeProgram(OpenCL.Context, [| kernelSource |])
////        program.Build(null, null, null, System.IntPtr.Zero)
////        program
////
////    static member CommandQueue = 
////        new ComputeCommandQueue(OpenCL.Context, OpenCL.Context.Devices.[0], ComputeCommandQueueFlags.None)
////
////    static member Events = new ComputeEventList()
////    static member VertexKernel = OpenCL.Program.CreateKernel("VertexKernel")
////    static member TextureKernel = OpenCL.Program.CreateKernel("TextureKernel")
////
////    static member VertexBuffer() = 
////        new ComputeBuffer<Vector4>(OpenCL.Context, ComputeMemoryFlags.WriteOnly, ARRAY_SIZE * ARRAY_SIZE)
//
//
//let OpenCLComputePlatform = 
//    new ComputeContextPropertyList(ComputePlatform.Platforms.[0])
//let OpenCLContext = 
//    new ComputeContext(ComputeDeviceTypes.Default, OpenCLComputePlatform, null, 
//                       System.IntPtr.Zero)
//let path = @"E:\GDrive\PlanetTesting\FSharp Project Folder\UnityPlanetGenerator\UnityPlanetGenerator\Terrain.cl"
//let kernelSource = System.IO.File.ReadAllText(path)
//let OpenCLProgram = new ComputeProgram(OpenCLContext, [| kernelSource |])
//
//OpenCLProgram.Build(null, null, null, System.IntPtr.Zero)
//
//let OpenCLCommandQueue = 
//    new ComputeCommandQueue(OpenCLContext, OpenCLContext.Devices.[0], 
//                            ComputeCommandQueueFlags.None)
//let OpenCLEvents = new ComputeEventList()
//
//let VertexKernel = OpenCLProgram.CreateKernel("VertexKernel")
//let TextureKernel = OpenCLProgram.CreateKernel("TextureKernel")
//
//let Vector3Buffer() = new ComputeBuffer<Vector3>(OpenCLContext, ComputeMemoryFlags.WriteOnly, ARRAY_SIZE * ARRAY_SIZE)
//let Vector4Buffer() = new ComputeBuffer<Vector4>(OpenCLContext, ComputeMemoryFlags.WriteOnly, ARRAY_SIZE * ARRAY_SIZE)

//let OpenCL = OpenCLInitialization



////////////////////////////////////////////////////////////////////////////////
// Def
////////////////////////////////////////////////////////////////////////////////

//#time "on"
//
//let verticesBuffer = Vector3Buffer()
//let normalsBuffer = Vector3Buffer()
//let tangentsBuffer = Vector4Buffer()
//
//VertexKernel.SetMemoryArgument(0, verticesBuffer)
//VertexKernel.SetMemoryArgument(1, normalsBuffer)
//VertexKernel.SetMemoryArgument(2, tangentsBuffer)
//VertexKernel.SetValueArgument(3, Vector4(BL.x, BL.y, BL.z))
//VertexKernel.SetValueArgument(4, Vector4(BR.x, BR.y, BR.z))
//VertexKernel.SetValueArgument(5, Vector4(TL.x, TL.y, TL.z))
//VertexKernel.SetValueArgument(6, rad)
//VertexKernel.SetValueArgument(7, amp)
//
//OpenCLCommandQueue.Execute(VertexKernel, null, [|ARRAY_SIZE; ARRAY_SIZE|], null, OpenCLEvents)
//
//OpenCLCommandQueue.ReadFromBuffer(verticesBuffer, vertRef, true, OpenCLEvents)
//OpenCLCommandQueue.ReadFromBuffer(normalsBuffer, normRef, true, OpenCLEvents)
//OpenCLCommandQueue.ReadFromBuffer(tangentsBuffer, tangRef, true, OpenCLEvents)
//
//OpenCLCommandQueue.Finish()



//
//Cloo.
//
//let event = new Event<_>()
//
//[<CLIEvent>]
//let trigger() = event.Publish
//let ready() = event.Trigger()
//
//trigger()
//
//event.
//
//let keyList = InitializePlanetCache(0, 100.0f, 1.0f)
//
//let mutable processed = false
//let proc =
//        Evaluator(
//            seq {
//                let _ = ProcessKeysQueued 1.0f keyList
//                processed <- true
//                yield ()
//                })
//EvaluationQueue.Enqueue(proc)
//
//#time "on"
//
//let StepFrame2 (threshold:float32) (keyList: Key list) = 
//    printfn "Keys: %d" (keyList.Length)
//    printfn "Queue: %d" (EvaluationQueue.Count)
//
//    match CommandQueueBusy() with
//        | true  -> System.Threading.Thread.Sleep(15)
//        | false -> OpenCLEvents.Clear()
//                   EvaluationQueue.Evaluate()
//
//    if processed then
//        let keyList0 = ProcessKeysQueued threshold keyList
//        processed <- false
//        let proc =
//            Evaluator(
//                seq {
//                    let _ = ProcessKeysQueued threshold keyList0
//                    processed <- true
//                    yield ()
//                    })
//        EvaluationQueue.Enqueue(proc)
//        keyList0
//    else
//        keyList
//
//let keyList = StepFrame2 1.0f keyList
//
//
//let timer = System.Diagnostics.Stopwatch.StartNew()
//let mutable t = 0L
//for i in 1..100 do
//    printfn "Total time: %d ms" (timer.ElapsedMilliseconds)
//    printfn "Current computation time: %d ms" (t)
//    t <- timer.ElapsedMilliseconds
//    match CommandQueueBusy() with
//        | true  -> System.Threading.Thread.Sleep(15)
//        | false -> OpenCLEvents.Clear()
//                   EvaluationQueue.Evaluate()
//    t <- timer.ElapsedMilliseconds - t
//
//
//
//OpenCLEvents
//
//let event = OpenCLEvents.[0]
//
//OpenCLEvents
//OpenCLEvents.Count
//
//CommandQueueBusy()
//
//
//let key = MakeKey(0, CubeFace.Front, -1L)
//let BL, BR, TL = Vector3(-1.0f, -1.0f,  1.0f), 
//                 Vector3( 1.0f, -1.0f,  1.0f), 
//                 Vector3(-1.0f,  1.0f,  1.0f)
//let rad = 100.0f
//let amp = 1.0f
//
//let pID = key.planetID
//let face = key.face
//let cID = key.cellID
//
//let i = cID + 1L
//let bi = 4L * i
//let TLi = bi + 0L
//let TRi = bi + 1L
//let BLi = bi + 2L
//let BRi = bi + 3L
//
//let TLKey = MakeKey(pID, face, TLi)
//let TRKey = MakeKey(pID, face, TRi)
//let BLKey = MakeKey(pID, face, BLi)
//let BRKey = MakeKey(pID, face, BRi)
//
//HeightMapSplitKernel.SetMemoryArgument(0, HeightMapBuffer)
//HeightMapSplitKernel.SetValueArgument(1, Vector4(BL.x, BL.y, BL.z))
//HeightMapSplitKernel.SetValueArgument(2, Vector4(BR.x, BR.y, BR.z))
//HeightMapSplitKernel.SetValueArgument(3, Vector4(TL.x, TL.y, TL.z))
//HeightMapSplitKernel.SetValueArgument(4, rad)
//
//NormalMapSplitKernel.SetMemoryArgument(0, HeightMapBuffer)
//NormalMapSplitKernel.SetMemoryArgument(1, NormalMapBuffer)
//
//VertexValuesSplitKernel.SetMemoryArgument(0, VertexValuesBuffer)
//VertexValuesSplitKernel.SetValueArgument(1, Vector4(BL.x, BL.y, BL.z))
//VertexValuesSplitKernel.SetValueArgument(2, Vector4(BR.x, BR.y, BR.z))
//VertexValuesSplitKernel.SetValueArgument(3, Vector4(TL.x, TL.y, TL.z))
//VertexValuesSplitKernel.SetValueArgument(4, rad)
//VertexValuesSplitKernel.SetValueArgument(5, amp)
//
//VertexNormalsSplitKernel.SetMemoryArgument(0, VertexNormalsBuffer)
//VertexNormalsSplitKernel.SetValueArgument(1, Vector4(BL.x, BL.y, BL.z))
//VertexNormalsSplitKernel.SetValueArgument(2, Vector4(BR.x, BR.y, BR.z))
//VertexNormalsSplitKernel.SetValueArgument(3, Vector4(TL.x, TL.y, TL.z))
//VertexNormalsSplitKernel.SetValueArgument(4, rad)
//VertexNormalsSplitKernel.SetValueArgument(5, amp)
//
//OpenCLCommandQueue.Execute(HeightMapSplitKernel,
//                            null,
//                            [|4L; TEXTURE_SIZE; TEXTURE_SIZE|],
//                            null,
//                            OpenCLEvents)
//
//OpenCLCommandQueue.ReadFromBuffer(HeightMapBuffer, HeightMapOutput, true, OpenCLEvents)
//OpenCLCommandQueue.Finish()

//let starterKeys = InitializePlanetCache(0, 100.0f, 1.0f)
//let key = starterKeys.[0]
//
//let vertices = VertexCache.[key]
//let normals = NormalCache.[key]
//
//let format (v:Vector3) =
//    (string v.x) + ", " + (string v.y) + ", " + (string v.z)
//
//let vertex = vertices.[0]
//format vertex
//
//let strVertices = Array.map format vertices
//let strNormals = Array.map format normals
//
//let path = @"E:\GDrive\PlanetTesting\Extra Stuff\data\"
//System.IO.File.WriteAllLines(path + "vertices.csv", strVertices)
//System.IO.File.WriteAllLines(path + "normals.csv", strNormals)
//
//let WriteVector3Array(vertices:Vector3[]) =
//    let path = @"E:\GDrive\PlanetTesting\Extra Stuff\data\" + (string System.DateTime.Now.Ticks) + "_"
//    System.IO.File.WriteAllLines(path + "vertices.csv", Array.map format vertices)
//
//
//
//
//
//let minV = Vector3(
//            (Array.minBy (fun (v:Vector3) -> v.x) vertices).x,
//            (Array.minBy (fun (v:Vector3) -> v.y) vertices).y,
//            (Array.minBy (fun (v:Vector3) -> v.z) vertices).z
//            )
//
//let maxV = Vector3(
//            (Array.maxBy (fun (v:Vector3) -> v.x) vertices).x,
//            (Array.maxBy (fun (v:Vector3) -> v.y) vertices).y,
//            (Array.maxBy (fun (v:Vector3) -> v.z) vertices).z
//            )
//
//let center = (minV + maxV) / 2.0f
//let size = maxV - minV
//
//
//
//let (BL, BR, _) = CornerCache.[key]
//let d = 50.0f * Vector3.Distance(BL, BR)
//
//let cameraPos = 1.75f * Vector3(-70.4f, 0.0f, 70.4f)
//
//let closestPoint = Vector3(
//                    Mathf.Clamp(cameraPos.x, minV.x, maxV.x),
//                    Mathf.Clamp(cameraPos.y, minV.y, maxV.y),
//                    Mathf.Clamp(cameraPos.z, minV.z, maxV.z)
//                    )
//
//let D = Mathf.Max(0.0001f, Vector3.Distance(cameraPos, closestPoint))
//
//d / D
//
//
//
//
//let DistanceError(key:Key) =
//    let (BL, BR, _) = CornerCache.[key]
//    //TODO: Remove 50.0 as constant radius and use argument instead
//    let d = 50.0f * Vector3.Distance(BL, BR)
//    let boundingBox = GameObjectRefs.[key].Value.GetComponent<MeshFilter>().mesh.bounds
//    let minV, maxV = boundingBox.min, boundingBox.max
//    let cameraPos = Camera.main.transform.position
//    let closestPoint = Vector3(Mathf.Clamp(cameraPos.x, minV.x, maxV.x),
//                               Mathf.Clamp(cameraPos.y, minV.y, maxV.y),
//                               Mathf.Clamp(cameraPos.z, minV.z, maxV.z))
//    let D = Mathf.Max(0.0001f, Vector3.Distance(cameraPos, closestPoint))
//    d / D
//
//let format (v:Vector3) =
//    (string v.x) + ", " + (string v.y) + ", " + (string v.z)
//
//
//Array.map format vertices.[0..9]
//Array.map format normals.[0..9]

//let ReadyCache     = Dictionary<Key, bool>()
//let CornerCache    = Dictionary<Key, Vector3 * Vector3 * Vector3>()
//let VertexCache    = Dictionary<Key, Vector3[]>()
//let NormalCache    = Dictionary<Key, Vector3[]>()
//let TangentCache   = Dictionary<Key, Vector4[]>()
//let TextureCache   = Dictionary<Key, Texture2D>()
//let NormalMapCache = Dictionary<Key, Texture2D>()
//let GameObjectRefs = Dictionary<Key, GameObject ref>()


//let top    = makeSide(Vector3(-1.0f,  1.0f,  1.0f), 
//                        Vector3( 1.0f,  1.0f,  1.0f), 
//                        Vector3(-1.0f,  1.0f, -1.0f),
//                        CubeFace.Top)
//
//let bottom = makeSide(Vector3(-1.0f, -1.0f, -1.0f), 
//                        Vector3( 1.0f, -1.0f, -1.0f), 
//                        Vector3(-1.0f, -1.0f,  1.0f),
//                        CubeFace.Bottom)
//
//let left   = makeSide(Vector3(-1.0f, -1.0f, -1.0f), 
//                        Vector3(-1.0f, -1.0f,  1.0f), 
//                        Vector3(-1.0f,  1.0f, -1.0f),
//                        CubeFace.Left)
//
//let right  = makeSide(Vector3( 1.0f, -1.0f,  1.0f), 
//                        Vector3( 1.0f, -1.0f, -1.0f), 
//                        Vector3( 1.0f,  1.0f,  1.0f),
//                        CubeFace.Right)
//
//let back   = makeSide(Vector3( 1.0f, -1.0f, -1.0f), 
//                        Vector3(-1.0f, -1.0f, -1.0f), 
//                        Vector3( 1.0f,  1.0f, -1.0f),
//                        CubeFace.Back)

//open Cloo
//open UnityEngine
//open System.Drawing
//open System.Drawing.Imaging
//open System.Collections
//
//type byte2 =
//    struct
//        val x: byte
//        val y: byte
//        new(X, Y) = {x = X; y = Y}
//    end
//
//#if INTERACTIVE
//fsi.AddPrintTransformer(fun (b:byte2) -> (b.x, b.y) |> box)
//#endif
//
//let OpenCLComputePlatform = 
//    new ComputeContextPropertyList(ComputePlatform.Platforms.[0])
//
//let OpenCLContext = 
//    new ComputeContext(ComputeDeviceTypes.Default, 
//                       OpenCLComputePlatform, 
//                       null, 
//                       System.IntPtr.Zero)
//
//let path = @"E:\GDrive\PlanetTesting\Assets\Code\F#\Terrain.cl"
//let kernelSource = System.IO.File.ReadAllText(path)
//let OpenCLProgram = new ComputeProgram(OpenCLContext, [|kernelSource|])
//OpenCLProgram.Build(null, null, null, System.IntPtr.Zero)
//
//let OpenCLCommandQueue = 
//    new ComputeCommandQueue(OpenCLContext, 
//                            OpenCLContext.Devices.[0], 
//                            ComputeCommandQueueFlags.None)
//
//let OpenCLEvents = new ComputeEventList()
//
//let VertexValuesSplitKernel  = OpenCLProgram.CreateKernel("VertexValuesSplit")
//let VertexNormalsSplitKernel = OpenCLProgram.CreateKernel("VertexNormalsSplit")
//let HeightMapSplitKernel     = OpenCLProgram.CreateKernel("HeightMapSplit")
//let NormalMapSplitKernel     = OpenCLProgram.CreateKernel("NormalMapSplit")
//
//let ARRAY_SIZE   =  16L
//let TEXTURE_SIZE = 256L
//
////let BL = Vector3(-1.0f, -1.0f, 1.0f)
////let BR = Vector3(-0.9f, -1.0f, 1.0f)
////let TL = Vector3(-1.0f, -0.9f, 1.0f)
//let BL = Vector3(-1.0f, -1.0f, 1.0f)
//let BR = Vector3( 1.0f, -1.0f, 1.0f)
//let TL = Vector3(-1.0f,  1.0f, 1.0f)
//
//let rad = 100.0f
//let amp = 0.1f
//
//let VertexValuesOutput  = ref (Array.zeroCreate<Vector4> (4L*ARRAY_SIZE*ARRAY_SIZE|>int))
//let VertexNormalsOutput = ref (Array.zeroCreate<Vector4> (4L*ARRAY_SIZE*ARRAY_SIZE|>int))
//let HeightMapOutput     = ref (Array.zeroCreate<byte>    (4L*TEXTURE_SIZE*TEXTURE_SIZE|>int))
//let NormalMapOutput     = ref (Array.zeroCreate<byte2>   (4L*TEXTURE_SIZE*TEXTURE_SIZE|>int))
//
//let VertexValuesBuffer  = new ComputeBuffer<Vector4> (OpenCLContext, ComputeMemoryFlags.WriteOnly, 4L*ARRAY_SIZE*ARRAY_SIZE)
//let VertexNormalsBuffer = new ComputeBuffer<Vector4> (OpenCLContext, ComputeMemoryFlags.WriteOnly, 4L*ARRAY_SIZE*ARRAY_SIZE)
//let HeightMapBuffer     = new ComputeBuffer<byte>    (OpenCLContext, ComputeMemoryFlags.WriteOnly, 4L*TEXTURE_SIZE*TEXTURE_SIZE)
//let NormalMapBuffer     = new ComputeBuffer<byte2>   (OpenCLContext, ComputeMemoryFlags.WriteOnly, 4L*TEXTURE_SIZE*TEXTURE_SIZE)
//
//#time "on"
//
//HeightMapSplitKernel.SetMemoryArgument(0, HeightMapBuffer)
//HeightMapSplitKernel.SetValueArgument(1, Vector4(BL.x, BL.y, BL.z))
//HeightMapSplitKernel.SetValueArgument(2, Vector4(BR.x, BR.y, BR.z))
//HeightMapSplitKernel.SetValueArgument(3, Vector4(TL.x, TL.y, TL.z))
//HeightMapSplitKernel.SetValueArgument(4, rad)
//
//NormalMapSplitKernel.SetMemoryArgument(0, HeightMapBuffer)
//NormalMapSplitKernel.SetMemoryArgument(1, NormalMapBuffer)
//
//VertexValuesSplitKernel.SetMemoryArgument(0, VertexValuesBuffer)
//VertexValuesSplitKernel.SetValueArgument(1, Vector4(BL.x, BL.y, BL.z))
//VertexValuesSplitKernel.SetValueArgument(2, Vector4(BR.x, BR.y, BR.z))
//VertexValuesSplitKernel.SetValueArgument(3, Vector4(TL.x, TL.y, TL.z))
//VertexValuesSplitKernel.SetValueArgument(4, rad)
//VertexValuesSplitKernel.SetValueArgument(5, amp)
//
//VertexNormalsSplitKernel.SetMemoryArgument(0, VertexNormalsBuffer)
//VertexNormalsSplitKernel.SetValueArgument(1, Vector4(BL.x, BL.y, BL.z))
//VertexNormalsSplitKernel.SetValueArgument(2, Vector4(BR.x, BR.y, BR.z))
//VertexNormalsSplitKernel.SetValueArgument(3, Vector4(TL.x, TL.y, TL.z))
//VertexNormalsSplitKernel.SetValueArgument(4, rad)
//VertexNormalsSplitKernel.SetValueArgument(5, amp)
//
//OpenCLCommandQueue.Execute(HeightMapSplitKernel,
//                           null,
//                           [|4L; TEXTURE_SIZE; TEXTURE_SIZE|],
//                           null,
//                           OpenCLEvents)
//
//OpenCLCommandQueue.ReadFromBuffer(HeightMapBuffer, HeightMapOutput, true, OpenCLEvents)
//OpenCLCommandQueue.Finish()
//
//OpenCLCommandQueue.Execute(NormalMapSplitKernel,
//                           null, 
//                           [|4L; TEXTURE_SIZE; TEXTURE_SIZE|],
//                           null, 
//                           OpenCLEvents)
//
//OpenCLCommandQueue.Execute(VertexValuesSplitKernel,
//                           null,
//                           [|4L; ARRAY_SIZE; ARRAY_SIZE|],
//                           null,
//                           OpenCLEvents)
//
//OpenCLCommandQueue.Execute(VertexNormalsSplitKernel,
//                           null,
//                           [|4L; ARRAY_SIZE; ARRAY_SIZE|],
//                           null,
//                           OpenCLEvents)
//
//OpenCLCommandQueue.ReadFromBuffer(NormalMapBuffer, NormalMapOutput, true, OpenCLEvents)
//OpenCLCommandQueue.ReadFromBuffer(VertexValuesBuffer, VertexValuesOutput, true, OpenCLEvents)
//OpenCLCommandQueue.ReadFromBuffer(VertexNormalsBuffer, VertexNormalsOutput, true, OpenCLEvents)
//OpenCLCommandQueue.Finish()
//
//let flattenedHeightMaps = HeightMapOutput.contents
//let flattenedNormalMaps = NormalMapOutput.contents
//let flattenedVertexValues = VertexValuesOutput.contents
//let flattenedVertexNormals = VertexNormalsOutput.contents
//
//let len1 = TEXTURE_SIZE * TEXTURE_SIZE |> int
//let len2 = ARRAY_SIZE   * ARRAY_SIZE   |> int
//
//let hmTL = flattenedHeightMaps.[0      ..   len1 - 1]
//let hmTR = flattenedHeightMaps.[len1   .. 2*len1 - 1]
//let hmBL = flattenedHeightMaps.[2*len1 .. 3*len1 - 1]
//let hmBR = flattenedHeightMaps.[3*len1 .. 4*len1 - 1]
//
//let nmTL = flattenedNormalMaps.[0      ..   len1 - 1]
//let nmTR = flattenedNormalMaps.[len1   .. 2*len1 - 1]
//let nmBL = flattenedNormalMaps.[2*len1 .. 3*len1 - 1]
//let nmBR = flattenedNormalMaps.[3*len1 .. 4*len1 - 1]
//
//let vvTL = flattenedVertexValues.[0      ..   len2 - 1]
//let vvTR = flattenedVertexValues.[len2   .. 2*len2 - 1]
//let vvBL = flattenedVertexValues.[2*len2 .. 3*len2 - 1]
//let vvBR = flattenedVertexValues.[3*len2 .. 4*len2 - 1]
//
//let vnTL = flattenedVertexNormals.[0      ..   len2 - 1]
//let vnTR = flattenedVertexNormals.[len2   .. 2*len2 - 1]
//let vnBL = flattenedVertexNormals.[2*len2 .. 3*len2 - 1]
//let vnBR = flattenedVertexNormals.[3*len2 .. 4*len2 - 1]
//
//
//
//
//let byteToColor = fun (b:byte) -> System.Drawing.Color.FromArgb(255, int(b), int(b), int(b))
//let byte2ToColor = fun (b:byte2) -> System.Drawing.Color.FromArgb(255, int(b.x), int(b.y), 255)
//let showImg(img, title) =
//    let form = new System.Windows.Forms.Form()
//    form.AutoSize <- true
//    let pb = new System.Windows.Forms.PictureBox()
//    pb.Image <- img
//    pb.SizeMode <- System.Windows.Forms.PictureBoxSizeMode.AutoSize
//    form.Controls.Add(pb)
//    form.Text <- title
//    form.Show()
//
//let DrawHeightMap(hm:byte[], title) =
//    let n = int TEXTURE_SIZE
//    let bmp = new System.Drawing.Bitmap(n, n)
//    for i in 0..(n-1) do
//        for j in 0..(n-1) do
//            bmp.SetPixel(i, n-j-1, byteToColor(hm.[n*i+j]))
//    showImg(bmp, title)
//
//let DrawNormalMap(nm:byte2[], title) =
//    let n = int TEXTURE_SIZE
//    let bmp = new System.Drawing.Bitmap(n, n)
//    for i in 0..(n-1) do
//        for j in 0..(n-1) do
//            bmp.SetPixel(i, n-j-1, byte2ToColor(nm.[n*i+j]))
//    showImg(bmp, title)
//
//DrawHeightMap(hmTL, "Top Left")
//DrawHeightMap(hmTR, "Top Right")
//DrawHeightMap(hmBL, "Bottom Left")
//DrawHeightMap(hmBR, "Bottom Right")
//
//type CubeFace =
//    | Front  = 0
//    | Back   = 1
//    | Left   = 2
//    | Right  = 3
//    | Top    = 4
//    | Bottom = 5
//
//type Key = {planetID:int; face:CubeFace; cellID:int64}
//
//let cacheSize = pown 2 22
//
//let ReadyCache = System.Collections.Generic.Dictionary<Key, bool>(cacheSize)
//
//#time "on"
//for i in 0..cacheSize-1 do
//    ReadyCache.[{planetID=0; face=CubeFace.Front; cellID=(int64 i)}] <- false

//
//let heightMapData = Array.map byteToColor data
//let normalMapData = Array.map byte2ToColor normals
//let len = data.Length/4 |> float |> sqrt |> int
//
//let hm1 = new System.Drawing.Bitmap(len, len)
//for i in 0..(len)-1 do
//    for j in 0..(len)-1 do
//        hm1.SetPixel(i, len-j-1, heightMapData.[len*i+j])
//
//let nm1 = new System.Drawing.Bitmap(len, len)
//for i in 0..(len)-1 do
//    for j in 0..(len)-1 do
//        nm1.SetPixel(i, len-j-1, normalMapData.[len*i+j])
//

//
//showImg(hm1, "Heightmap")
//showImg(nm1, "Normalmap")
//
//hm1.Save(@"E:\GDrive\PlanetTesting\Extra Stuff\hm2.png", System.Drawing.Imaging.ImageFormat.Png)
//nm1.Save(@"E:\GDrive\PlanetTesting\Extra Stuff\nm2.png", System.Drawing.Imaging.ImageFormat.Png)
//let Rescale32 (array : float32 []) =
//    let xMax = Array.max array
//    let xMin = Array.min array
//    Array.map (fun x -> (x - xMin) / (xMax - xMin)) array

//let rescaled = Array.map (fun i -> System.Drawing.Color.FromArgb(255, int(i), int(i), int(i))) data
//
////let rescaled = 
////    Rescale32(data)
////    |> Array.map (fun (x:float32) -> x*255.0f |> int |> (fun i -> System.Drawing.Color.FromArgb(255, i, i, i)))
//
//let len = data.Length/4 |> float |> sqrt |> int
//
//let img1 = new System.Drawing.Bitmap(len, len)
//let img2 = new System.Drawing.Bitmap(len, len)
//let img3 = new System.Drawing.Bitmap(len, len)
//let img4 = new System.Drawing.Bitmap(len, len)
//
//for i in 0..(len)-1 do
//    for j in 0..(len)-1 do
//        img1.SetPixel(i, len-j-1, rescaled.[len*i+j])
//
//for i in 0..(len)-1 do
//    for j in 0..(len)-1 do
//        img2.SetPixel(i, len-j-1, rescaled.[len*len + len*i+j])
//
//for i in 0..(len)-1 do
//    for j in 0..(len)-1 do
//        img3.SetPixel(i, len-j-1, rescaled.[2*len*len + len*i+j])
//
//for i in 0..(len)-1 do
//    for j in 0..(len)-1 do
//        img4.SetPixel(i, len-j-1, rescaled.[3*len*len + len*i+j])
//
//
//
//showImg(img1, "img1")
//showImg(img2, "img2")
//showImg(img3, "img3")
//showImg(img4, "img4")
//
////let len = data.Length |> float |> sqrt |> int
////
////let rescaled = 
////    Utils.Data.Array.Rescale32(data)
////    |> Array.map (fun (x:float32) -> x*255.0f |> int |> (fun i -> System.Drawing.Color.FromArgb(255, i, i, i)))
////
////let img = new System.Drawing.Bitmap(len, len)
////for i in 0..(len)-1 do
////    for j in 0..(len)-1 do
////        img.SetPixel(i, len-j-1, rescaled.[len*i+j])
////
////let form = new System.Windows.Forms.Form()
////form.AutoSize <- true
////let pb = new System.Windows.Forms.PictureBox()
////
////pb.Image <- img
////pb.SizeMode <- System.Windows.Forms.PictureBoxSizeMode.AutoSize
////form.Controls.Add(pb)
////form.Show()
//
//
////let Output = ref (System.Array.CreateInstance(typeof<float32>, [|size; size|]))
//
////OpenCLCommandQueue.Read(NoiseValuesBuffer, true, 0L, 0L, System.IntPtr.Zero, OpenCLEvents)
//
//OpenCLCommandQueue.ReadFromBuffer(NoiseValuesBuffer, Output1, true, OpenCLEvents)
//OpenCLCommandQueue.ReadFromBuffer(NoiseValuesBuffer, Output2, true, OpenCLEvents)
//
//let data1 = Output.contents
//let data2 = Output2.contents
//
//
//let format = ComputeImageFormat(ComputeImageChannelOrder.Rgba, ComputeImageChannelType.Float)
//let firstBitmap = new Bitmap(int size, int size, PixelFormat.Format32bppRgb)
//
//let img = Array.zeroCreate<float32> (int size) 
//let imgPtr = nativeint img
//
//let clImage = 
//    new ComputeImage2D
//        (OpenCLContext, 
//        ComputeMemoryFlags.ReadWrite ||| ComputeMemoryFlags.CopyHostPointer, 
//        format, int size, int size, size * 4L * (int64 sizeof<float32>), imgPtr)

//let clImage = new ComputeImage2D(context, ComputeMemoryFlags.ReadWrite ||| ComputeMemoryFlags.CopyHostPointer, firstBitmap)

//let s = seq { for i in 0 .. 4095 do yield i } :?> IEnumerator
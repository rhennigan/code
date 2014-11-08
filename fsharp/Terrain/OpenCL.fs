module Terrain.OpenCL

open Cloo
open Config
open UnityEngine
open TerrainTypes

let private Platform = 
    new ComputeContextPropertyList(ComputePlatform.Platforms.[0])
let private Context = 
    new ComputeContext(ComputeDeviceTypes.Default, Platform, null, 
                       System.IntPtr.Zero)

let private Program = new ComputeProgram(Context, [| KernelSource.kernelSource |])

Program.Build(null, null, null, System.IntPtr.Zero)

let private Queue = 
    new ComputeCommandQueue(Context, Context.Devices.[0], 
                            ComputeCommandQueueFlags.Profiling)
let private Events = new ComputeEventList()

let QueueBusy() = 
    Seq.forall 
        (fun (event: ComputeEventBase) -> 
        (event.Status = ComputeCommandExecutionStatus.Complete)) Events 
    |> not

let Reset() = Events.Clear()

let private VertexKernel = Program.CreateKernel("VertexKernel")
let private HeightMapKernel = Program.CreateKernel("HeightMapKernel")
let private NormalMapKernel = Program.CreateKernel("NormalMapKernel")
let private ColorizeKernel = Program.CreateKernel("ColorizeKernel")

let private Vector3Buffer() = 
    new ComputeBuffer<Vector3>(Context, ComputeMemoryFlags.WriteOnly, 
                               VertexArraySize)
let private Vector4Buffer() = 
    new ComputeBuffer<Vector4>(Context, ComputeMemoryFlags.WriteOnly, 
                               VertexArraySize)
let private ByteBuffer() = 
    new ComputeBuffer<byte>(Context, ComputeMemoryFlags.ReadWrite, 
                            TextureArraySize)

let private Byte4Buffer() = 
    new ComputeBuffer<byte4>(Context, ComputeMemoryFlags.ReadWrite, 
                             TextureArraySize)

let AppendFlange (rad:float32) (amp:float32) (vertices:Vector3[]) (normals:Vector3[]) (tangents:Vector4[]) =
    let s = Config.VertexCount

    let i00 = 0
    let i01 = s - 1
    let i10 = s*s - s
    let i11 = s*s - 1

    let c = (rad - 2.0f * amp) / rad

    let newVertices =
        [|
            c * vertices.[i00]
            c * vertices.[i01]
            c * vertices.[i10]
            c * vertices.[i11]
        |]
    
    let newNormals =
        [|
            normals.[i00]
            normals.[i01]
            normals.[i10]
            normals.[i11]
        |]

    let newTangents =
        [|
            tangents.[i00]
            tangents.[i01]
            tangents.[i10]
            tangents.[i11]
        |]

    (Array.append vertices newVertices,
     Array.append normals newNormals,
     Array.append tangents newTangents)

let UpdateRefs(vertRef:Vector3[] ref, normRef:Vector3[] ref, tangRef:Vector4[] ref,
               hmDataRef:byte4[] ref, nmDataRef:byte4[] ref,
               BL:Vector3, BR:Vector3, TL:Vector3,
               rad:float32, amp:float32) = 
    
    //Debug.Log("Updating refs")

    let event = new Event<unit>()
    
    let verticesBuffer = Vector3Buffer()
    let normalsBuffer = Vector3Buffer()
    let tangentsBuffer = Vector4Buffer()

    VertexKernel.SetMemoryArgument(0, verticesBuffer)
    VertexKernel.SetMemoryArgument(1, normalsBuffer)
    VertexKernel.SetMemoryArgument(2, tangentsBuffer)
    VertexKernel.SetValueArgument(3, Vector4(BL.x, BL.y, BL.z))
    VertexKernel.SetValueArgument(4, Vector4(BR.x, BR.y, BR.z))
    VertexKernel.SetValueArgument(5, Vector4(TL.x, TL.y, TL.z))
    VertexKernel.SetValueArgument(6, rad)
    VertexKernel.SetValueArgument(7, amp)
    Queue.Execute(VertexKernel, null, [| int64 VertexCount; int64 VertexCount |], null, Events)
    Queue.ReadFromBuffer(verticesBuffer, vertRef, true, Events)
    Queue.ReadFromBuffer(normalsBuffer, normRef, true, Events)
    Queue.ReadFromBuffer(tangentsBuffer, tangRef, true, Events)

    let heightMapBuffer = Byte4Buffer()
    let normalMapBuffer = Byte4Buffer()
    //let textureBuffer = Byte4Buffer()

    HeightMapKernel.SetMemoryArgument(0, heightMapBuffer)
    HeightMapKernel.SetValueArgument(1, Vector4(BL.x, BL.y, BL.z))
    HeightMapKernel.SetValueArgument(2, Vector4(BR.x, BR.y, BR.z))
    HeightMapKernel.SetValueArgument(3, Vector4(TL.x, TL.y, TL.z))
    HeightMapKernel.SetValueArgument(4, rad)

    Queue.Execute(HeightMapKernel, null, [| int64 TextureRes; int64 TextureRes |], null, Events)
    Queue.ReadFromBuffer(heightMapBuffer, hmDataRef, true, Events)
    Queue.AddBarrier()

    NormalMapKernel.SetMemoryArgument(0, heightMapBuffer)
    NormalMapKernel.SetMemoryArgument(1, normalMapBuffer)

    Queue.Execute(NormalMapKernel, null, [| int64 TextureRes; int64 TextureRes |], null, Events)
    Queue.ReadFromBuffer(normalMapBuffer, nmDataRef, true, Events)

//    ColorizeKernel.SetMemoryArgument(0, heightMapBuffer)
//    ColorizeKernel.SetMemoryArgument(1, textureBuffer)
//    Queue.Execute(ColorizeKernel, null, [| int64 TextureRes; int64 TextureRes |], null, Events)
//    Queue.AddBarrier()
//    Queue.ReadFromBuffer(textureBuffer, hmDataRef, true, Events)

    let marker = Queue.AddMarker()
    event.Publish.Add(fun () -> 
        verticesBuffer.Dispose()
        normalsBuffer.Dispose()
        tangentsBuffer.Dispose()
        heightMapBuffer.Dispose()
        normalMapBuffer.Dispose()
        //Debug.Log("Disposing buffers")
        )

    marker.Completed.Add(fun _ -> event.Trigger())

    ()



let UpdateMeshData(key: Key) = 
    
    let rad, amp = Cache.PlanetData.[key.planetID]
    let BL, BR, TL = Corners(key)

    let vertices = Array.zeroCreate<Vector3> (Config.VertexArraySize |> int)
    let normals = Array.zeroCreate<Vector3> (Config.VertexArraySize |> int)
    let tangents = Array.zeroCreate<Vector4> (Config.VertexArraySize |> int)

    let event = new Event<unit>()
    
    let verticesBuffer = Vector3Buffer()
    let normalsBuffer = Vector3Buffer()
    let tangentsBuffer = Vector4Buffer()
    VertexKernel.SetMemoryArgument(0, verticesBuffer)
    VertexKernel.SetMemoryArgument(1, normalsBuffer)
    VertexKernel.SetMemoryArgument(2, tangentsBuffer)
    VertexKernel.SetValueArgument(3, Vector4(BL.x, BL.y, BL.z))
    VertexKernel.SetValueArgument(4, Vector4(BR.x, BR.y, BR.z))
    VertexKernel.SetValueArgument(5, Vector4(TL.x, TL.y, TL.z))
    VertexKernel.SetValueArgument(6, rad)
    VertexKernel.SetValueArgument(7, amp)
    Queue.Execute(VertexKernel, null, [| int64 VertexCount; int64 VertexCount |], null, Events)
    Queue.ReadFromBuffer(verticesBuffer, ref vertices, true, Events)
    Queue.ReadFromBuffer(normalsBuffer, ref normals, true, Events)
    Queue.ReadFromBuffer(tangentsBuffer, ref tangents, true, Events)
    let marker = Queue.AddMarker()
    event.Publish.Add(fun () -> 
        verticesBuffer.Dispose()
        normalsBuffer.Dispose()
        tangentsBuffer.Dispose()

        let v0, n0, t0 = AppendFlange rad amp vertices normals tangents

        Cache.Vertices.[key] <- v0
        Cache.Normals.[key] <- n0
        Cache.Tangents.[key] <- t0
        )

    marker.Completed.Add(fun _ -> event.Trigger())

    ()


let UpdateTextureData(key:Key) =

    let rad, _ = Cache.PlanetData.[key.planetID]

    let BL, BR, TL = Corners(key)

    let fhm = Array.zeroCreate<byte4> (TextureArraySize |> int)
    let fnm = Array.zeroCreate<byte4> (TextureArraySize |> int)

    let event = new Event<unit>()

    let heightMapBuffer = Byte4Buffer()
    let normalMapBuffer = Byte4Buffer()

    HeightMapKernel.SetMemoryArgument(0, heightMapBuffer)
    HeightMapKernel.SetValueArgument(1, Vector4(BL.x, BL.y, BL.z))
    HeightMapKernel.SetValueArgument(2, Vector4(BR.x, BR.y, BR.z))
    HeightMapKernel.SetValueArgument(3, Vector4(TL.x, TL.y, TL.z))
    HeightMapKernel.SetValueArgument(4, rad)

    Queue.Execute(HeightMapKernel, null, [| int64 TextureRes; int64 TextureRes |], null, Events)
    Queue.ReadFromBuffer(heightMapBuffer, ref fhm, true, Events)
    Queue.AddBarrier()

    NormalMapKernel.SetMemoryArgument(0, heightMapBuffer)
    NormalMapKernel.SetMemoryArgument(1, normalMapBuffer)

    Queue.Execute(NormalMapKernel, null, [| int64 TextureRes; int64 TextureRes |], null, Events)
    Queue.ReadFromBuffer(normalMapBuffer, ref fnm, true, Events)
    let marker = Queue.AddMarker()

    let onCompletion() =
        
        heightMapBuffer.Dispose()
        normalMapBuffer.Dispose()
        Cache.TextureData.[key] <- fhm
        Cache.NormalMapData.[key] <- fnm

    event.Publish.Add(fun () -> onCompletion())
    marker.Completed.Add(fun _ -> event.Trigger())

    ()

//let UpdateTextureData(rad: float32, amp: float32, key: Key) = 
//
//    let BL, BR, TL = Corners(key)
//
//    let fhm = Array.zeroCreate<byte4> (TextureArraySize |> int)
//    let fnm = Array.zeroCreate<byte4> (TextureArraySize |> int)
//
//    let event = new Event<unit>()
//    
//    let heightMapBuffer = Byte4Buffer()
//    let normalMapBuffer = Byte4Buffer()
//
//    TextureKernel.SetMemoryArgument(0, heightMapBuffer)
//    TextureKernel.SetMemoryArgument(1, normalMapBuffer)
//    TextureKernel.SetValueArgument(2, Vector4(BL.x, BL.y, BL.z))
//    TextureKernel.SetValueArgument(3, Vector4(BR.x, BR.y, BR.z))
//    TextureKernel.SetValueArgument(4, Vector4(TL.x, TL.y, TL.z))
//    TextureKernel.SetValueArgument(5, rad)
//    Queue.Execute(TextureKernel, null, [| int64 TextureRes; int64 TextureRes |], null, Events)
//    Queue.ReadFromBuffer(heightMapBuffer, ref fhm, false, Events)
//    Queue.ReadFromBuffer(normalMapBuffer, ref fnm, false, Events)
//    let marker = Queue.AddMarker()
//            
//    let onCompletion() = 
//        heightMapBuffer.Dispose()
//        normalMapBuffer.Dispose()
//
//        Cache.TextureData.[key] <- fhm
//        Cache.NormalMapData.[key] <- fnm
//                
//    event.Publish.Add(fun () -> onCompletion())
//    marker.Completed.Add(fun _ -> event.Trigger())
//    
//    ()
    

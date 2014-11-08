module Terrain.TerrainTypes

open UnityEngine

type CubeFace = 
    | Front  = 0
    | Back   = 1
    | Left   = 2
    | Right  = 3
    | Top    = 4
    | Bottom = 5

type byte4 = 
    struct
        val x: byte
        val y: byte
        val z: byte
        val w: byte
        new(X, Y, Z, W) = { x = X; y = Y; z = Z; w = W }
    end

type Key = 
    { planetID: int
      face: CubeFace
      cellID: int64 }

    override this.ToString() = 
        "p" + (string this.planetID) + "_" 
        + (string this.face) + "_" 
        + (string this.cellID)

let MakeKey(pID: int, f: CubeFace, cID: int64) = 
    { planetID = pID
      face = f
      cellID = cID }

let Children(key:Key) =
    let i = key.cellID + 1L
    let bi = 4L * i
    let pID = key.planetID
    let face = key.face
    List.map (fun x -> MakeKey(pID, face, bi + x)) [0L..3L]

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

let RootCorners =
    function
    | CubeFace.Front -> Vector3(-1.0f, -1.0f,  1.0f), 
                        Vector3( 1.0f, -1.0f,  1.0f), 
                        Vector3(-1.0f,  1.0f,  1.0f)
    | CubeFace.Top   -> Vector3(-1.0f,  1.0f,  1.0f), 
                        Vector3( 1.0f,  1.0f,  1.0f), 
                        Vector3(-1.0f,  1.0f, -1.0f)
    | CubeFace.Bottom ->Vector3( 1.0f, -1.0f,  1.0f), 
                        Vector3(-1.0f, -1.0f,  1.0f),
                        Vector3( 1.0f, -1.0f, -1.0f)
    | CubeFace.Left  -> Vector3(-1.0f, -1.0f, -1.0f), 
                        Vector3(-1.0f, -1.0f,  1.0f), 
                        Vector3(-1.0f,  1.0f, -1.0f)
    | CubeFace.Right -> Vector3( 1.0f, -1.0f,  1.0f), 
                        Vector3( 1.0f, -1.0f, -1.0f), 
                        Vector3( 1.0f,  1.0f,  1.0f)
    | CubeFace.Back  -> Vector3( 1.0f, -1.0f, -1.0f), 
                        Vector3(-1.0f, -1.0f, -1.0f), 
                        Vector3( 1.0f,  1.0f, -1.0f)
    | _              -> failwith "there are only six sides to a cube!"

let private path n =
    let rec convert n = if n < 4L then [n] else (n % 4L) :: (convert (n / 4L - 1L))
    convert n |> List.rev

let rec private cut (BL:Vector3, BR:Vector3, TL:Vector3) =
    function
    | [] -> (BL, BR, TL)
    | (n::ns) ->
        let dX = (BR - BL)/2.0f
        let dY = (TL - BL)/2.0f
        let newBL = BL + (float32 (n % 2L) * dX) + (float32 (n / 2L) * dY)
        cut (newBL, newBL + dX, newBL + dY) ns

let Corners(key:Key) = 
    match key.cellID with
    | -1L -> RootCorners key.face
    | _   -> cut (RootCorners key.face) (path key.cellID)

let Triangles = 
    let vs = Config.VertexCount |> int
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
    let vs = Config.VertexCount |> int
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

let FlangeFill =
    let s = Config.VertexCount |> int
    
    let i00 = 0
    let i01 = s - 1
    let i10 = s*s - s
    let i11 = s*s - 1

    let v00 = i11 + 1
    let v01 = i11 + 2
    let v10 = i11 + 3
    let v11 = i11 + 4

    let mt = s / 2
    let ml = s * mt
    let mr = ml + s - 1
    let mb = i10 + mt

    seq {
        for i in i00 .. mt - 1 do yield! [i; i+1; v00]
        for i in mt .. i01 - 1 do yield! [i; i+1; v01]
        yield! [mt; v01; v00]

        for i in i00 .. s .. (ml - s) do yield! [i; v00; i+s]
        for i in ml .. s .. (i10 - s) do yield! [i; v10; i+s]
        yield! [v00; v10; ml]

        for i in i01 .. s .. (mr - s) do yield! [i; i+s; v01]
        for i in mr .. s .. (i11 - s) do yield! [i; i+s; v11]
        yield! [v01; mr; v11]

        for i in i10 .. mb - 1 do yield! [i; v10; i+1]
        for i in mb .. i11 - 1 do yield! [i; v11; i+1]
        yield! [mb; v10; v11]
    } |> Array.ofSeq

let FullTriangles = Array.append Triangles FlangeFill

let UV = 
    let vs = Config.VertexCount |> int
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

let FullUV = 
    let s = Config.VertexCount
    let w = float32 s - 1.0f
    let h = float32 s - 1.0f

    let uv =
        seq { 
            for i in 0.0f..h do
                for j in 0.0f..w do
                    let r = j / w
                    let u = i / h
                    yield Vector2(r, u)
        }
        |> Array.ofSeq

    let i00 = 0
    let i01 = s - 1
    let i10 = s*s - s
    let i11 = s*s - 1

    let newUV = [| uv.[i00]; uv.[i01]; uv.[i10]; uv.[i11]; |]

    Array.append uv newUV

#if INTERACTIVE
fsi.AddPrintTransformer(fun (b:byte4) -> (b.x, b.y, b.z, b.w) |> box)
fsi.AddPrintTransformer(fun (k:Key) -> (k.planetID, k.face, k.cellID) |> box)
#endif
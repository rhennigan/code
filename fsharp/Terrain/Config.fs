module Terrain.Config

open UnityEngine

let VertexCount = 64
let VertexArraySize = VertexCount * VertexCount |> int64

let TextureRes = 256
let TextureArraySize = TextureRes * TextureRes |> int64

let ObjectPoolSize = 512

let DebugMessage(message:string) =
    #if COMPILED
    Debug.Log(message)
    #else
    printfn "%A" message
    #endif

let WriteVector3Array(vertices:Vector3[], name:string) =
    let format (v:Vector3) =
        (string v.x) + ", " + (string v.y) + ", " + (string v.z)
    let exportPath = @"E:\GDrive\PlanetTesting\Extra Stuff\data\"
    System.IO.File.WriteAllLines(exportPath + name + ".csv", Array.map format vertices)

let WriteVector4Array(vertices:Vector4[], name:string) =
    let format (v:Vector4) =
        (string v.x) + ", " + (string v.y) + ", " + (string v.z) + ", " + (string v.w)
    let exportPath = @"E:\GDrive\PlanetTesting\Extra Stuff\data\"
    System.IO.File.WriteAllLines(exportPath + name + ".csv", Array.map format vertices)

let WriteBMP(imgArray:byte[], name:string) = 
    let color(r:byte, g:byte, b:byte) = System.Drawing.Color.FromArgb(int r, int g, int b)
    let imgSize = imgArray.Length / 3 |> float |> sqrt |> int
    let bmp = new System.Drawing.Bitmap(imgSize, imgSize)
    for i in 0 .. imgSize - 1 do
        for j in 0 .. imgSize - 1 do
            let k = imgSize * i + j
            let c = color(imgArray.[3 * k], imgArray.[3 * k + 1], imgArray.[3 * k + 2])
            bmp.SetPixel(i, j, c)
    bmp.Save(@"E:\GDrive\PlanetTesting\Extra Stuff\data\" + name + ".bmp")

open System.Drawing

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

    let tex = gameObject.renderer.material.GetTexture("_MainTex") :?> Texture2D
    let nrm = gameObject.renderer.material.GetTexture("_BumpMap") :?> Texture2D
    
    System.IO.File.WriteAllBytes(path + "texture.png", tex.EncodeToPNG())
    System.IO.File.WriteAllBytes(path + "normalMap.png", nrm.EncodeToPNG())

    Debug.Log("Export Complete")

#if INTERACTIVE
fsi.AddPrintTransformer(fun (v:Vector3) -> (v.x, v.y, v.z) |> box)
fsi.AddPrintTransformer(fun (v:Vector4) -> (v.x, v.y, v.z, v.w) |> box)
#endif
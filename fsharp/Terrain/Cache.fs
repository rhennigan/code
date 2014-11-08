module Terrain.Cache

open Terrain.Config
open Terrain.TerrainTypes
open UnityEngine
open System.Collections.Generic

let PlanetData = Dictionary<int, float32 * float32>()
let Ready = Dictionary<Key, bool>()
let Vertices = Dictionary<Key, Vector3 []>()
let Normals = Dictionary<Key, Vector3 []>()
let Tangents = Dictionary<Key, Vector4 []>()
let TextureData = Dictionary<Key, byte4 []>()
let NormalMapData = Dictionary<Key, byte4 []>()
let Texture = Dictionary<Key, Texture2D>()
let NormalMap = Dictionary<Key, Texture2D>()
let GameObjectRefs = Dictionary<Key, GameObject ref>()
let ObjectPool = Stack<GameObject>(ObjectPoolSize)

let FillObjectPool(baseGameObject: GameObject, rootObject: GameObject) = 
    ObjectPool.Clear()
    Debug.Log("Filling Object Pool!")
    for i in 0..ObjectPoolSize do
        let gameObject = GameObject.Instantiate(baseGameObject) :?> GameObject
        gameObject.transform.parent <- rootObject.transform
        gameObject.SetActive(false)
        ObjectPool.Push(gameObject)

let VerticesReadyQ key = Vertices.TryGetValue(key) |> fst
let NormalsReadyQ key = Normals.TryGetValue(key) |> fst
let TangentsReadyQ key = Tangents.TryGetValue(key) |> fst
let TextureDataReadyQ key = TextureData.TryGetValue(key) |> fst
let NormalMapDataReadyQ key = NormalMapData.TryGetValue(key) |> fst
let TextureReadyQ key = Texture.TryGetValue(key) |> fst
let NormalMapReadyQ key = NormalMap.TryGetValue(key) |> fst

let EditMeshReadyQ(key: Key) = 
    List.forall (fun f -> f key) 
        [ VerticesReadyQ; NormalsReadyQ; TangentsReadyQ ]

let EditTexturesReadyQ(key: Key) = 
    List.forall (fun f -> f key) 
        [ TextureDataReadyQ; NormalMapDataReadyQ ]

let BuildObjectReadyQ(key:Key) =
    List.forall (fun f -> f key) 
        [ VerticesReadyQ; NormalsReadyQ; TangentsReadyQ; TextureDataReadyQ; NormalMapDataReadyQ ]

let ReadyQ(key: Key) = Ready.TryGetValue(key) |> fst

let ActiveQ(key: Key) = GameObjectRefs.[key].Value.activeSelf
let Disable(key: Key) = GameObjectRefs.[key].Value.SetActive(false)
let Enable(key: Key) = GameObjectRefs.[key].Value.SetActive(true)
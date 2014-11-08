let s = 5

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

let top =
    seq {
        for i in i00 .. mt - 1 do yield! [i; i+1; v00]
        for i in mt .. i01 - 1 do yield! [i; i+1; v01]
        yield! [mt; v01; v00]
    }

let left =
    seq {
        for i in i00 .. s .. (ml - s) do yield! [i; v00; i+s]
        for i in ml .. s .. (i10 - s) do yield! [i; v10; i+s]
        yield! [v00; v10; ml]
    }

let right =
    seq {
        for i in i01 .. s .. (mr - s) do yield! [i; i+s; v01]
        for i in mr .. s .. (i11 - s) do yield! [i; i+s; v11]
        yield! [v01; mr; v11]
    }

let bottom =
    seq {
        for i in i10 .. mb - 1 do yield! [i; v10; i+1]
        for i in mb .. i11 - 1 do yield! [i; v11; i+1]
        yield! [mb; v10; v11]
    }

Array.ofSeq top
Array.ofSeq left
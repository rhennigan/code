(* for readability *)
let identity = fun x -> x

(* natural numbers *)
type nat = 
  | Zero
  | Successor of nat

(* addition of two natural numbers *)
let rec add: nat -> nat -> nat = 
    function 
    | Zero -> identity
    | Successor n -> fun b -> add n (Successor b)

let rec iterate: (nat -> nat) -> nat -> nat = 
    fun f -> function 
          | Zero -> f (Successor Zero)
          | Successor n -> f (iterate f n)

let rec ackermann: nat -> nat -> nat = 
    function 
    | Zero -> fun n -> Successor n
    | Successor n -> iterate (ackermann n)

(* convenience functions *)
let rec display: nat -> int = 
    function 
    | Zero -> 0
    | Successor n -> 1 + (display n)

let rec tonat : int -> nat =
    function 
    | 0 -> Zero
    | n -> Successor(tonat (n - 1))

		   
let (>>) f g x = g(f(x))
let (<|) f g x = f(g(x))
		  

let (/@) f x = List.map f x


let test x = x
			  
let rec quick_sort : 'a list -> 'a list = 
  function 
  | [ ] -> []
  | head :: tail -> 
     let less = fun x -> x < head in
     let left, right = List.partition less tail in
     quick_sort left @ [ head ] @ quick_sort right
		       
let merge_sort : 'a list -> 'a list = 
  let rec merge left right = 
    match left, right with
    | tail, [] -> tail
    | [] , ys -> ys
    | head :: tail, y :: ys -> 
       if head <= y then head :: merge tail right
       else y :: merge left ys in
  let rec aux = 
    function 
    | [] -> []
    | [ head ] -> [ head ]
    | head :: y :: zs -> aux (merge head y :: (aux zs)) in
  List.map (fun head -> [ head ]) >> aux >> function [ head ] -> head | _ -> []

let lst = [5;12;5;61;126;2;1;2;56;61;23;136]
let f = fun x -> x + x
let test = f /@ lst
		 

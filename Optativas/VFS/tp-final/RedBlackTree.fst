module RedBlackTree

// Color type
type color = 
  | Red 
  | Black

// Red-black tree type. Ver si lo hacemos polimórfico con un tipo que tenga orden definido
type rbt = 
  | E
  | N of color & rbt & int & rbt

// Balance function
let balance (c : color) (t : rbt) (x : int) (b : rbt) : rbt =
  match c, t, x, b with
  | Black, N (Red, N (Red, a, x, b), y, c), z, d
  | Black, N (Red, a, x, N (Red, b, y, c)), z, d
  | Black, a, x, N (Red, N (Red, b, y, c), z, d)
  | Black, a, x, N (Red, b, y, N (Red, c, z, d)) ->
    N (Red, N (Black, a, x, b), y, N (Black, c, z, d))
  | c, a, x, b -> N (c, a, x, b)

exception MinNotFound

// Insert function
let rec insert (x : int) (t : rbt) : rbt = 
  match t with
  | E -> N (Red, E, x, E)
  | N (c, l, y, r) ->
    if x < y then balance c (insert x l) y r
    else if x > y then balance c l y (insert x r)
    else t

// Función para encontrar el mínimo valor en un árbol
let rec min (t : rbt) : option int =
  match t with
  | N (_, E, x, _) -> Some x
  | N (_, l, _, _) -> min l
  | _ -> None

// Delete function
let rec delete (x : int) (t : rbt) : Tot rbt (decreases t) =
  match t with
  | E -> E
  | N (c, l, y, r) ->
    if x < y then balance c (delete x l) y r
    else if x > y then balance c l y (delete x r)
    else match l, r with
      | E, _ -> r
      | _, E -> l
      | _, _ -> 
        match min r with
        | None -> l
        | Some m -> balance c l m (delete m r)

// Member function
let rec member (x : int) (t : rbt) : bool = 
  match t with
  | E -> false
  | N (_, l, y, r) ->
    if x < y then member x l
    else if x > y then member x r
    else true

// Size function
let rec size (t : rbt) : int =
  match t with
  | E -> 0
  | N (_, l, _, r) -> 1 + size l + size r

// Balanced function
// let rec balanced (t : rbt) : bool =
//   match t with
//   | E -> true
//   | N (Red, N (Red, _, _, _), _, _) -> false
//   | N (Red, _, _, N (Red, _, _, _)) -> false
//   | N (_, l, _, r) -> balanced l && balanced r
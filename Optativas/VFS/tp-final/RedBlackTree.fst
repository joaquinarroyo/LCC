module RedBlackTree

////////////////////////////// Structure //////////////////////////////

// Color type
type color = 
  | Red 
  | Black

// Red-black tree type. Ver si lo hacemos polimórfico con un tipo que tenga orden definido
type rbt (a : Type) = 
  | E
  | N of color & rbt a & a & rbt a

////////////////////////////// Aux Functions //////////////////////////////

// Balance function
let _balance (#a : Type) (c : color) (t : rbt a) (x : a) (b : rbt a) : rbt a =
  match c, t, x, b with
  | Black, N (Red, N (Red, a, x, b), y, c), z, d
  | Black, N (Red, a, x, N (Red, b, y, c)), z, d
  | Black, a, x, N (Red, N (Red, b, y, c), z, d)
  | Black, a, x, N (Red, b, y, N (Red, c, z, d)) ->
    N (Red, N (Black, a, x, b), y, N (Black, c, z, d))
  | c, a, x, b -> N (c, a, x, b)

// Min function
let rec _min (#a : Type) (t : rbt a) : option a =
  match t with
  | N (_, E, x, _) -> Some x
  | N (_, l, _, _) -> _min l
  | _ -> None

////////////////////////////// Main Functions //////////////////////////////

// Insert function
let rec insert (#a : Type) (x : a) (t : rbt a) : rbt a = 
  match t with
  | E -> N (Red, E, x, E)
  | N (c, l, y, r) ->
    if x < y then _balance c (insert x l) y r
    else if x > y then _balance c l y (insert x r)
    else t

// Delete function
let rec delete (#a : Type) (x : a) (t : rbt a) : Tot (rbt a) (decreases t) =
  match t with
  | E -> E
  | N (c, l, y, r) ->
    if x < y then _balance c (delete x l) y r
    else if x > y then _balance c l y (delete x r)
    else match l, r with
      | E, _ -> r
      | _, E -> l
      | _, _ -> 
        match _min r with
        | None -> l
        | Some m -> _balance c l m (delete m r)

// Member function
let rec member (#a : Type) (x : a) (t : rbt a) : bool = 
  match t with
  | E -> false
  | N (_, l, y, r) ->
    if x < y then member x l
    else if x > y then member x r
    else true

// Size function
let rec size (#a : Type) (t : rbt a) : a =
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

////////////////////////////// Proofs //////////////////////////////
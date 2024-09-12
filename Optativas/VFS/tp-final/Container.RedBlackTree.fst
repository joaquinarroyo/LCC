(*
  Librería de RBTs verificada.
  Se proveen las operaciones básicas de un RBT (insert, delete, member, size, min, empty, is_empty) 
  y se demuestra que modelan conjuntos y que las operaciones que alteran la estructura mantienen el invariante de los RBTs.

  Autores:
    - Arroyo Joaquin
    - Bolzan Francisco
  
  Verificacion en F* - 2024
*)

module Container.RedBlackTree
open RedBlackTree
open Container

(* Balance function *)
let balance (t:rbt int) : rbt int =
  match t with
  | E -> E 
  | N (Black, N (Red, N (Red, a, x, b), y, c), z, d)
  | N (Black, N (Red, a, x, N (Red, b, y, c)), z, d)
  | N (Black, a, x, N (Red, N (Red, b, y, c), z, d))
  | N (Black, a, x, N (Red, b, y, N (Red, c, z, d))) ->
    N (Red, N (Black, a, x, b), y, N (Black, c, z, d))  // Rotaciones y recoloreado para balancear
  | _ -> t 

(* Min function *)
let rec min (t:rbt int) : option int =
  match t with
  | N (_, E, x, _) -> Some x
  | N (_, l, _, _) -> min l
  | _ -> None

(* Empty function *)
let empty : rbt int = E

(* Is empty function *)
let is_empty (t:rbt int) : bool =
  match t with
  | E -> true
  | _ -> false

(* Make black function *)
let make_black (t:rbt int) : rbt int =
  match t with
  | E -> E
  | N (_, l, x, r) -> N (Black, l, x, r)

(* Insert function *)
let rec ins' (x:int) (t:rbt int) : rbt int = 
  match t with
  | E -> N (Red, E, x, E)
  | N (c, l, y, r) ->
    if x < y then balance (N (c, (ins' x l), y, r))
    else if x > y then balance (N (c, l, y, (ins' x r)))
    else t // No se permiten elementos repetidos

let ins (x:int) (t:rbt int) : rbt int =
  make_black (ins' x t)

(* Delete function *)
let rec del' (x:int) (t:rbt int) : Tot (rbt int) (decreases t) =
  match t with
  | E -> E
  | N (c, l, y, r) ->
    if x < y then balance (N (c, del' x l, y, r)) 
    else if x > y then balance (N (c, l, y, del' x r))
    else match l, r with 
      | E, _ -> r
      | _, E -> l
      | _, _ -> 
        match min r with
        | None -> l
        | Some m -> balance (N (c, l, m, del' m r))

let del (x:int) (t:rbt int) : rbt int =
  make_black (del' x t)

(* Member function *)
let rec mem (x:int) (t:rbt int) : bool = 
  match t with
  | E -> false
  | N (_, l, y, r) ->
    if x < y then mem x l
    else if x > y then mem x r
    else true

(* Size function *)
let rec size (t:rbt int) : int =
  match t with
  | E -> 0
  | N (_, l, _, r) -> 1 + size l + size r

(* Demostración que los RBTs modelan conjuntos *)

instance rbts_son_container0
  : container0 int (rbt int) = {
    empty = E;
    is_empty = E?;
    mem = mem;
    ins = ins;
    del = del;
}

let models
  (t : rbt int)
  (ss : TSet.set int)
  : GTot prop =
  forall (x:int).
    mem x t <==> TSet.mem x ss

let empty_ok () : Lemma (models E TSet.empty)
  = ()

let is_empty_ok_back (t:rbt int)
  : Lemma (models t TSet.empty ==> E? t)
  = ()

let mem_ok (x:int) (t:rbt int) (ss:TSet.set int)
  : Lemma (requires t `models` ss)
          (ensures  mem x t <==> TSet.mem x ss)
  = ()

let rec is_bst (t: rbt int) (min_val: option int) (max_val: option int) : bool =
  match t with
  | E -> true
  | N (_, l, x, r) ->
    let within_limits = 
      (match min_val with
       | Some min -> x > min
       | None -> true) &&
      (match max_val with
       | Some max -> x < max
       | None -> true) in
    within_limits &&
    is_bst l min_val (Some x) && 
    is_bst r (Some x) max_val

// TODO: Definir
let rec ins_ok_lem (x:int) (t:rbt int) (ss:TSet.set int)
  : Lemma (requires t `models` ss)
          (ensures  ins x t
                    `models`
                    TSet.union ss (TSet.singleton x))
  = match t with
    | E -> ()
    | N (c, l, y, r) ->
      if x < y then (
        admit();
        ins_ok_lem x l (TSet.filter (fun z -> z < y) ss)
      )
      else if x > y then (
        admit();
        ins_ok_lem x r (TSet.filter (fun z -> z > y) ss)
      )
      else ()

// TODO: Definir
let rec del_ok_aux (y:int) (t:rbt int) (z:int)
  : Lemma (mem z (del y t) <==> mem z t /\ y <> z)
  = match t with
    | E -> ()
    | N (c, l, x, r) ->
      if y < x then (
        admit();
        del_ok_aux y l z
      )
      else if y > x then (
        admit();
        del_ok_aux y r z
      )
      else admit()

let del_ok_lem (y:int) (t:rbt int) (ss:TSet.set int)
  : Lemma (requires t `models` ss)
          (ensures del y t
                   `models`
                   TSet.intersect ss (TSet.complement <| TSet.singleton y))
  =
  Classical.forall_intro (del_ok_aux y t)

instance rbts_son_container_laws
  : container_laws int (rbt int) rbts_son_container0 = {
    models = models;
    empty_ok = empty_ok;
    is_empty_ok = is_empty_ok_back;
    mem_ok = mem_ok;
    ins_ok = ins_ok_lem;
    del_ok = del_ok_lem;
}

instance rbts_son_container
  : container int (rbt int) = {
    ops = rbts_son_container0;
    laws = rbts_son_container_laws;
}

(* Demostración que las operaciones que alteran la estructura mantienen el invariante de los RBTs *)
let root_is_black (t:rbt int) : bool
  = match t with
    | E -> true
    | N (c, _, _, _) -> c = Black

let rec leaves_are_black (t:rbt int) : bool =
  match t with
  | E -> true
  | N (c, E, _, E) -> c = Black
  | N (_, l, _, r) -> leaves_are_black l && leaves_are_black r

let rec red_children_are_black (t:rbt int) : bool =
  match t with
  | E -> true
  | N (Red, N (Red, _, _, _), _, _) -> false
  | N (Red, _, _, N (Red, _, _, _)) -> false
  | N (_, l, _, r) -> red_children_are_black l && red_children_are_black r

let rec black_height (t:rbt int) : int =
  match t with
  | E -> 1
  | N (c, l, _, _) -> 
    let hl = black_height l in
    if c = Black then hl + 1 else hl

let rbt_invariant (t:rbt int) : bool =
  root_is_black t && leaves_are_black t && red_children_are_black t

// TODO: Definir
let rec ins_preserves_rbt_invariant (x:int) (t:rbt int) 
  : Lemma (rbt_invariant t ==> rbt_invariant (ins x t))
  = match t with
    | E -> ()
    | N (c, l, y, r) ->
      if x < y then (
        admit();
        ins_preserves_rbt_invariant x l
      )
      else if x > y then (
        admit();
        ins_preserves_rbt_invariant x r
      )
      else ()

// TODO: Definir
let rec del_preserves_rbt_invariant (x:int) (t:rbt int) 
  : Lemma (rbt_invariant t ==> rbt_invariant (del x t))
  = match t with
    | E -> ()
    | N (c, l, y, r) ->
      if x < y then (
        admit();
        del_preserves_rbt_invariant x l
      )
      else if x > y then (
        admit();
        del_preserves_rbt_invariant x r
      )
      else admit()
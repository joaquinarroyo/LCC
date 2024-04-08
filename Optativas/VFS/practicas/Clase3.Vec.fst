module Clase3.Vec

type vec (a:Type) : nat -> Type =
  | VNil : vec a 0
  | VCons : #n:nat -> hd:a -> tl:vec a n -> vec a (n+1)

(* safehead :: forall a. vec a -> a *)
let vhd (#a:Type) (#n:pos) (xs : vec a n) : a =
  match xs with
  | VCons hd tl -> hd

(* indice :: forall a. vec a -> nat -> a *)
let rec vidx (#a:Type) (#n:pos) (xs : vec a n) (i : nat{i < n}) : a =
  match xs with
  | VCons hd tl ->
    if i = 0
    then hd
    else vidx tl (i-1)

(* append :: forall a. vec a -> vec a -> vec a *)
let rec vappend (#a:Type) (#n1 #n2 : nat) (xs : vec a n1) (ys : vec a n2) : vec a (n1 + n2) =
  match xs with
  | VNil -> ys
  | VCons xhd xtl ->
    match ys with
    | VNil -> xs
    | VCons yhd ytl -> VCons xhd (vappend xtl ys)

(* update :: forall a. vec a -> nat -> a -> vec a *)
let rec vupd (#a:Type) (#n:pos) (xs : vec a n) (i : nat{i < n}) (x : a) : vec a n =
  match i with
  | 0 -> 
    (match xs with
      | VCons hd tl ->  VCons x tl)
  | j ->
    (match xs with
      | VCons hd tl -> VCons hd (vupd tl (j-1) x))

(* 
  Definir funciones similares para matrices.
  Se pueden usar las definiciones anteriores.
*)

(* 
  Tipo Matriz 

  [
    [0 ... 0] <- Vector 
    [0 ... 0] <- Vector
    Nil       <- MNil terminación
  ]

*)
type mat (a:Type) : nat -> nat -> Type =
  | MNil : mat a 0 0
  | MCons : #row:nat -> #column:nat -> hd : vec a column -> tl : mat a row column -> mat a (row+1) column
  
(* indice :: forall a. mat a -> nat -> nat -> a *)
let rec matidx (#a:Type) (#m #n : nat) (ma : mat a m n) (i : nat{i < m}) (j : nat{j < n}) : a =
  match ma with
  | MCons hd tl -> 
    if i = 0
    then vidx hd j
    else matidx tl (i-1) j

(* remove :: forall a. mat a -> nat -> nat -> a -> mat a *)
let rec matupd (#a:Type) (#m #n : pos) (ma : mat a m n) (i : nat{i < m}) (j : nat{j < n}) (x : a) : mat a m n =
  match ma with
  | MCons hd tl ->
    match i with
    | 0 -> MCons (vupd hd j x) tl
    | n -> MCons hd (matupd tl (i-1) j x)
 

module Clase5.MiniLang

type l_ty =
  | Int
  | Bool

type var = nat

(* Pequeño lenguaje de expresiones, indexado por el tipo de su resultado *)
type expr : l_ty -> Type =
  | EInt : int -> expr Int
  | EBool : bool -> expr Bool
  | EAdd : expr Int -> expr Int -> expr Int
  | EEq : expr Int -> expr Int -> expr Bool
  | EIf :
    #ty:_ ->
    expr Bool -> expr ty -> expr ty -> expr ty

(* Traducción de tipos de MiniLang a tipos de F* *)
let lift (ty : l_ty) : Type =
  match ty with
  | Int -> int
  | Bool -> bool
  
(* El evaluador intrínsecamente-tipado de MiniLang *)
val eval (#ty:l_ty) (e : expr ty) : Tot (lift ty)
let rec eval (#ty:l_ty) (e : expr ty) : Tot (lift ty) (decreases e) =
  match e with
  | EInt i -> i
  | EBool b -> b
  | EAdd m n -> eval m + eval n
  | EEq m n -> eval m = eval n
  | EIf c t e ->
    if eval c then eval t else eval e

(* Optimización sobre expresiones MiniLang: constant folding *)
let rec constant_fold (#ty:l_ty) (e : expr ty) : Tot (expr ty) (decreases e) =
  match e with
  | EAdd l r ->
    let l' = constant_fold l in
    let r' = constant_fold r in
    (match (l', r') with
      | EInt x, EInt y -> EInt (x + y)
      | _ -> EAdd l' r')

  | EEq l raise ->
    let l' = constant_fold l in
    let raise' = constant_fold raise in
    (match (l', raise') with
      | EInt x, EInt y -> EBool (x = y)
      | _ -> EEq l' raise')

  | EIf c t e ->
    let c' = constant_fold c in
    let t' = constant_fold t in
    let e' = constant_fold e in
    (match c' with
      | EBool true -> t'
      | EBool false -> e'
      | _ -> EIf c' t' e')

  | _ -> e

(* Correctitud de la optimización de constant folding *)
let rec constant_fold_ok (#ty:l_ty) (e : expr ty)
  : Lemma (ensures eval e == eval (constant_fold e)) (decreases e)
  = match e with
  | EAdd l r ->
    constant_fold_ok l;
    constant_fold_ok r

  | EEq l r ->
    constant_fold_ok l;
    constant_fold_ok r

  | EIf c t e ->
    constant_fold_ok c;
    constant_fold_ok t;
    constant_fold_ok e

  | _ -> ()

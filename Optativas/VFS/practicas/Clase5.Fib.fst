module Clase5.Fib

(* Hace que '*' sea la multiplicación de enteros, en vez del constructor de tuplas. *)
open FStar.Mul

let abs (x:int) : nat = if x >= 0 then x else -x
let max (x y : int) : int = if x > y then x else y

let rec fac (x:int) : int =
  if x <= 0 then 1 else x * fac (x - 1)

let rec fac_is_pos (x:int) : Lemma (requires True) (ensures fac x > 0) =
  if x <= 0
  then ()
  else fac_is_pos (x-1)

let suma_fac (x y : int) : pos =
  fac_is_pos x;
  fac_is_pos y;
  fac x + fac y

let rec fac_is_gt (x:int) : Lemma (requires x >= 3) (ensures fac x > x) =
  if x = 3
  then ()
  else fac_is_gt (x-1)

(* N-ésimo número triangular. *)
let rec triang (n:nat) : int =
  if n = 0 then 0 else triang (n - 1) + n

// 1   + 2  + ... + 100
// 100 + 99 + ... + 1
// 101 + 101 + ... + 101 = 101 * 100
// suma = 101 * 100 / 2 = 5050
(* https://en.wikipedia.org/wiki/Arithmetic_progression#History *)
let rec gauss (n:nat) : Lemma (triang n == n * (1 + n) / 2) =
  if n = 0 then () else gauss (n - 1)

let rec fib (x:nat) : nat =
  if x = 0 then 1
  else if x = 1 then 1
  else fib (x - 1) + fib (x - 2)

(* Fibonacci en tiempo lineal *)
let rec fib_lin' (x:nat) : (int & int) =
  if x = 0 then (1, 1)
   else
      let (a, b) = fib_lin' (x - 1) in
      (b, a + b)
let fib_lin (n:nat) : int = fst (fib_lin' n)

let rec fib_lin'_ok (n:nat) : Lemma (fib_lin' n == (fib n, fib (n + 1))) =
  if n = 0 then ()
  else if n = 1 then ()
  else fib_lin'_ok (n - 1)

(* Demuestre que es correcta. *)
let fib_lin_ok (n:nat) : Lemma (fib_lin n == fib n) =
  fib_lin'_ok n

(* Fibonacci en tiempo lineal con recursión de cola (esencialmente
un bucle while). *)
let rec fib_tail' (a b : nat) (n : nat) : Tot nat (decreases n) =
  if n = 0 then a
  else fib_tail' b (a + b) (n - 1)
let fib_tail (n:nat) : nat = fib_tail' 1 1 n

let rec fib_tail'_advances_fib (n:nat) (m:nat): Lemma (fib_tail' (fib m) (fib (m + 1)) n == fib (m + n)) =
  if n = 0 then ()
  else
    fib_tail'_advances_fib (n - 1) (m + 1)

(* Demuestre que es correcta. Va a necesitar un lema auxiliar para fib_tail'. *)
let fib_tail_ok (n:nat) : Lemma (fib_tail n == fib n) =
  fib_tail'_advances_fib n 0


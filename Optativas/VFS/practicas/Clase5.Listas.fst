module Clase5.Listas

open FStar.List.Tot

val sum_int : list int -> int
let rec sum_int xs =
  match xs with
 | [] -> 0
 | x::xs' -> x + sum_int xs'

(* Demuestre que sum_int "distribuye" sobre la concatenación de listas. *)
let rec sum_append (l1 l2 : list int)
  : Lemma (sum_int (l1 @ l2) == sum_int l1 + sum_int l2)
  (*
    l1 = []
    sum ([] ++ l2) = sum l2 = 0 + sum l2 = sum [] + sum l2

    l1 = x:xs
    sum x:xs + sum l2 = x + sum xs + sum l2
    sum (x:xs ++ l2) = sum (x:(xs ++ l2)) = x + sum (xs ++ l2) 
   *)
  = match l1 with
    | [] -> ()
    | x::xs -> 
      assert (sum_int l1 + sum_int l2 == x + sum_int xs + sum_int l2);
      assert (sum_int (l1 @ l2) = sum_int(x::(xs @ l2)));
      assert (sum_int (l1 @ l2) = x + sum_int (xs @ l2));
      sum_append xs l2; // H.I (revisar, si se sacan los assert y se pone la HI funciona)
      ()


(* Idem para length, definida en la librería de F*. *)
let rec len_append (l1 l2 : list int)
  : Lemma (length (l1 @ l2) == length l1 + length l2)
  (*
    l1 = x:xs
    length (x:xs ++ l2) = length (x::(xs ++ l2)) = 1 + length (xs ++ l2)
    length x:xs + length l2 = 1 + length xs + length l2 
   *)
  = match l1 with
    | [] -> ()
    | x::xs -> 
      assert (length l1 + length l2 == 1 + length xs + length l2);
      assert (length (l1 @ l2) == length (x::(xs @ l2)));
      assert (length (l1 @ l2) == 1 + length (xs @ l2));
      len_append xs l2;
      ()

let rec snoc (xs : list int) (x : int) : list int =
  match xs with
  | [] -> [x]
  | y::ys -> y :: snoc ys x

(* unit-tests *)
let _ = assert (snoc [1;2;3] 4 == [1;2;3;4])
let _ = assert (snoc [1;2;3] 5 == [1;2;3;5])

let rec rev_int (xs : list int) : list int =
  match xs with
  | [] -> []
  | x::xs' -> snoc (rev_int xs') x

let rev_append_int (xs ys : list int)
  : Lemma (rev_int (xs @ ys) == rev_int ys @ rev_int xs)
= admit()

let rev_rev (xs : list int)
  : Lemma (rev_int (rev_int xs) == xs)
= admit()

let rev_injective (xs ys : list int)
  : Lemma (requires rev_int xs == rev_int ys) (ensures xs == ys)
= admit()

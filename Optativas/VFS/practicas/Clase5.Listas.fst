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
      sum_append xs l2;
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

(* unit-tests *)
let _ = assert (snoc (rev_int [1;2;3]) 4 == [3;2;1;4])

// Lema para "rev_append_int"
let rec snoc_append (l1 l2 : list int) (x : int)
  : Lemma (snoc (l1 @ l2) x == l1 @ snoc l2 x)
  = match l1 with
  | [] -> ()
  | _::xs -> snoc_append xs l2 x

// rev_int "distribuye" sobre append
let rec rev_append_int (l1 l2 : list int)
  : Lemma (rev_int (l1 @ l2) == rev_int l2 @ rev_int l1)
= match l1 with
  | [] -> ()
  | x::xs ->
    rev_append_int xs l2;
    snoc_append (rev_int l2) (rev_int xs) x;
    ()

// Doble reverse es identidad
let rec rev_rev (l : list int)
  : Lemma (rev_int (rev_int l) == l)
  (*
  l = x:xs

  rev (rev l) = rev (rev x:xs);
  rev (rev x:xs) = rev (snoc (rev xs) x);
  rev (snoc (rev xs) x) = rev (rev xs @ [x]);
  rev (rev xs @ [x]) = rev [x] @ rev (rev xs)
  [x] @ xs = l

  xs = [1, 2, 3] x = 4
  rev (rev [1, 2, 3] @ [4]) = rev [3, 2, 1, 4] = [4, 1, 2, 3]
  rev (rev [1, 2, 3]) @ rev [4] = rev [3, 2, 1] @ [4] = [1, 2, 3, 4]

  Lema 1: snoc (rev l) x = rev l @ [x]
  Lema 2: rev (rev l1 @ l2) = rev l2 @ rev (rev l1)
  *)
= match l with
  | [] -> ()
  | x::xs ->
    assume (rev (rev l) = rev (rev xs @ [x]));
    assume (rev (rev xs @ [x]) = rev [x] @ rev (rev xs));
    assume (rev [x] = [x]);
    rev_rev xs;
    admit();
    ()

let rec rev_injective (l1 l2 : list int)
  : Lemma (requires rev_int l1 == rev_int l2) (ensures l1 == l2)
  (*
  l1 = x:xs
  l2 = y:ys

  rev x:xs = rev y:ys => snoc (rev xs) x = snoc (rev ys) y => 
  => rev xs @ [x] = rev ys @ [y] => H.I =>
  => sx @ [x] = sx @ [y] => (assume sx = sy)
  => [x] = [y] =>
  *)
= match l1 with
  | [] -> ()
  | x::xs -> 
    match l2 with
    | [] -> ()
    | y::ys ->
      assert (rev (x::xs) = rev (y::ys));
      ()


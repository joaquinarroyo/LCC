module Proofs

open RedBlackTree

// A proof that a tree is a valid red-black tree

let rec is_balanced (t : rbt) : bool =
  match t with
  | E -> true
  | T (B, a, x, b) -> is_balanced a && is_balanced b
  | T (R, a, x, b) -> is_balanced a && is_balanced b
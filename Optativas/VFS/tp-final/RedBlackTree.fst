(*
  Estructura RBTree

  Autores:
    - Arroyo Joaquin
    - Bolzan Francisco
  
  Verificacion en F* - 2024
*)

module RedBlackTree

(* Color type *)
type color =
  | Red
  | Black

(* Red-black tree type *)
type rbt a = 
  | E
  | N of color & rbt a & a & rbt a
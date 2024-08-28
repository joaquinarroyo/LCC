(*
  Interfaz

  Autores:
    - Arroyo Joaquin
    - Bolzan Francisco
  
  Verificacion en F* - 2024
*)

module Container.RedBlackTree

open RedBlackTree
open Container

instance val rbts_son_container0
  : container0 int (rbt int)

instance val rbts_son_container_laws
  : container_laws int (rbt int) rbts_son_container0

instance val rbts_son_container
  : container int (rbt int)

(* Los siguientes tests fallan sin conocer las implementaciones
(funciona dentro del módulo, porque mem/ins/del son visibles.
Se puede _demostrar_ (si tenemos la instancia de _laws)
pero no es automático. *)

// let test0 () =
//   let l : list int = empty in
//   let l = ins 2 l in
//   let l = del 3 l in
//   assert (mem 2 l);
//   l

// let test1 (t:eqtype) (x:t) =
//   let l : list t = empty in
//   let l = ins x l in
//   assert (mem x l);
//   l
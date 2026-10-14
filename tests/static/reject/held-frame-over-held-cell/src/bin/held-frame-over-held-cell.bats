#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* setting a cell the held bytes reach (i < n) changes them: the frame lemma
   needs n <= i *)
prfn claim {base,cells,cells_after,message:$A.cells}{n,i:nat | i < n}{value:int}
  (held: $SHA.HELD(base, cells, n, message), set: $A.SETC(cells, i, value, cells_after)): $SHA.HELD(base, cells_after, n, message) =
  $SHA.held_frame(held, set)

implement main0 () = ()

#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* after a frame the bytes are held from the array that was set, cs2, not cs *)
prfn claim {base,cells,cells_after,message:$A.cells}{n,i:nat | n <= i}{value:int}
  (held: $SHA.HELD(base, cells, n, message), set: $A.SETC(cells, i, value, cells_after)): $SHA.HELD(base, cells, n, message) =
  $SHA.held_frame(held, set)

implement main0 () = ()

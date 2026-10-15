#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* the byte put after n are held is cell n, not cell n + 1 *)
prfn claim {base,cells,message,message_after:$A.cells}{n:nat}{value:int}
  (held: $SHA.HELD(base, cells, n, message), cell: $A.NTH(cells, n + 1, value), snoc: $SHA.SNOC(message, value, message_after))
  : $SHA.HELD(base, cells, n + 1, message_after) =
  $SHA.HELD_next(held, cell, snoc)

implement main0 () = ()

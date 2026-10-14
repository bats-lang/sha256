#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* a byte is counted into a block under 64: not into a full one *)
prfn claim {message,message_after:$A.cells}{value:int}
  (counted: $SHA.COUNTED(message, 0, 0, 0, 64), snoc: $SHA.SNOC(message, value, message_after)): $SHA.COUNTED(message_after, 0, 0, 0, 65) =
  $SHA.COUNTED_byte(counted, snoc)

implement main0 () = ()

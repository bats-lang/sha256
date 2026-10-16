#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* the byte counted is put after the message that was counted *)
prfn claim {message,other,message_after:$A.cells}{value:int}
  (counted: $SHA.COUNTED(message, 0, 0, 0, 5), snoc: $SHA.SNOC(other, value, message_after)): $SHA.COUNTED(message_after, 0, 0, 0, 6) =
  $SHA.COUNTED_byte(counted, snoc)

implement main0 () = ()

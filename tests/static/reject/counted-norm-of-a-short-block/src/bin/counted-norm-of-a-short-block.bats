#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* hashing a block carries only a full block's count *)
prfn claim {message:$A.cells} (counted: $SHA.COUNTED(message, 0, 0, 0, 63)): $SHA.COUNTED(message, 0, 0, 1, 0) =
  $SHA.COUNTED_norm(counted, $SHA.NORM_block())

implement main0 () = ()

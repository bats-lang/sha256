#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* finish gives the digest of the message that was fed, not of another *)
fn claim {message,other:$A.cells}{out_loc:agz}{out_cells:$A.cells} (context: $SHA.ctx256(message), out: $A.barr(out_loc, 64, out_cells))
  : [out_cells_after:$A.cells][chaining:$SHA.eight_words] ($SHA.DIGEST256(other, chaining) | $A.barr(out_loc, 64, out_cells_after)) = let
  val (digest, _ | out) = $SHA.finish256_proved(context, out)
in (digest | out) end

implement main0 () = ()

#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* finish1_proved gives the digest of the message that was fed, not of another *)
fn claim {message,other:$A.cells}{out_loc:agz}{out_cells:$A.cells} (context: $SHA.ctx1(message), out: $A.barr(out_loc, 20, out_cells))
  : [out_cells_after:$A.cells][chaining:$SHA.five_words] ($SHA.DIGEST1(other, chaining) | $A.barr(out_loc, 20, out_cells_after)) = let
  val (digest, _ | out) = $SHA.finish1_proved(context, out)
in (digest | out) end

implement main0 () = ()

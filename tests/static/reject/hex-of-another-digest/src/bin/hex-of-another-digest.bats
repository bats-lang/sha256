#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* the hex digits written are the digest's: of the chaining value h, not of another *)
fn claim {message:$A.cells}{out_loc:agz}{out_cells:$A.cells}{other:$SHA.eight_words} (context: $SHA.ctx256(message), out: $A.barr(out_loc, 64, out_cells))
  : [out_cells_after:$A.cells][chaining:$SHA.eight_words] ($SHA.DIGEST256(message, chaining), $SHA.EIGHT_HEX(out_cells_after, other) | $A.barr(out_loc, 64, out_cells_after)) =
  $SHA.finish256_proved(context, out)

implement main0 () = ()

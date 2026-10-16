#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* the message is the first len cells of the data, put after nothing *)
fn claim {loc:agz}{n:nat}{data_cells:$A.cells}{length:nat | length <= n; length <= 65535}{out_loc:agz}{out_cells:$A.cells}
  (data: !$A.barr(loc, n, data_cells), length_given: int length, out: $A.barr(out_loc, 64, out_cells))
  : [message,out_cells_after:$A.cells][chaining:$SHA.eight_words] ($SHA.HELD($A.ccons(0, $A.cnil()), data_cells, length, message) | $A.barr(out_loc, 64, out_cells_after)) = let
  val (held, _, _ | out) = $SHA.sha256_digest_proved(data, length_given, out)
in (held | out) end

implement main0 () = ()

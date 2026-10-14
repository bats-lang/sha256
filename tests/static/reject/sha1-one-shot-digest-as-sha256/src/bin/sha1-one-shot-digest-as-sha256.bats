#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* the SHA-1 of the data is a DIGEST1, not a DIGEST256 *)
fn claim {loc:agz}{n:nat}{data_cells:$A.cells}{length:nat | length <= n; length <= 65535}{out_loc:agz}{out_cells:$A.cells}
  (data: !$A.barr(loc, n, data_cells), length_given: int length, out: $A.barr(out_loc, 20, out_cells))
  : [message,out_cells_after:$A.cells][chaining:$SHA.eight_words] ($SHA.DIGEST256(message, chaining) | $A.barr(out_loc, 20, out_cells_after)) = let
  val (_, digest, _ | out) = $SHA.sha1_digest_proved(data, length_given, out)
in (digest | out) end

implement main0 () = ()

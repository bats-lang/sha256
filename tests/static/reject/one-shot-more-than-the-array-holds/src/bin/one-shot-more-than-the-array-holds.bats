#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* len is at most the array's size *)
fn claim {loc:agz}{n:nat}{data_cells:$A.cells}{length:nat | n < length; length <= 65535}{out_loc:agz}{out_cells:$A.cells}
  (data: !$A.barr(loc, n, data_cells), length_given: int length, out: $A.barr(out_loc, 64, out_cells)): void = let
  val (_, _, _ | out) = $SHA.sha256_digest_proved(data, length_given, out)
in $A.barr_free(out) end

implement main0 () = ()

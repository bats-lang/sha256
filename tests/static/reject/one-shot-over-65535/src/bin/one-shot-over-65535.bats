#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* the one-shot digest is for under 2 to the 16 bytes: longer messages go in pieces *)
fn claim {loc:agz}{n:nat}{data_cells:$A.cells}{out_loc:agz}{out_cells:$A.cells} (data: !$A.barr(loc, n, data_cells), out: $A.barr(out_loc, 64, out_cells)): void = let
  val (_, _, _ | out) = $SHA.sha256_digest_proved(data, 65536, out)
in $A.barr_free(out) end

implement main0 () = ()

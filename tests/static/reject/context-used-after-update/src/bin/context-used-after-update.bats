#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* a context is used once: update gives the next one *)
fn claim {message,data_cells:$A.cells}{loc:agz}{n:nat}{length:nat | length <= n}{out_loc:agz}{out_cells:$A.cells}
  (context: $SHA.ctx256(message), data: !$A.barr(loc, n, data_cells), length_given: int length, out: $A.barr(out_loc, 64, out_cells)): void = let
  val r = $SHA.update256_proved(context, data, length_given)
  val (_, _ | out) = $SHA.finish256_proved(context, out)
  val () = $A.barr_free(out)
in case+ r of
   | ~$SHA.Updated256(_ | carry_mid) => let val+ ~$SHA.ctx256_mk(_, _, _, _, _ | chain_array, fill, block_array, _, _, _, _) = carry_mid in $A.barr_free(chain_array); $A.barr_free(fill); $A.barr_free(block_array) end
   | ~$SHA.Stopped256(_ | carry_mid) => let val+ ~$SHA.ctx256_mk(_, _, _, _, _ | chain_array, fill, block_array, _, _, _, _) = carry_mid in $A.barr_free(chain_array); $A.barr_free(fill); $A.barr_free(block_array) end
end

implement main0 () = ()

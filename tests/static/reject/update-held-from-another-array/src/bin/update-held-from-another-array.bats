#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* what update held is the message put after the old one from the array it was
   given, dc: not from another *)
fn consume {message,other:$A.cells}{length:nat} (r: $SHA.update256_result(message, other, length)): void =
  case+ r of
  | ~$SHA.Updated256(_ | carry_mid) => let val+ ~$SHA.ctx256_mk(_, _, _, _, _ | chain_array, fill, block_array, _, _, _, _) = carry_mid in $A.barr_free(chain_array); $A.barr_free(fill); $A.barr_free(block_array) end
  | ~$SHA.Stopped256(_ | carry_mid) => let val+ ~$SHA.ctx256_mk(_, _, _, _, _ | chain_array, fill, block_array, _, _, _, _) = carry_mid in $A.barr_free(chain_array); $A.barr_free(fill); $A.barr_free(block_array) end

fn claim {message,data_cells,other:$A.cells}{loc:agz}{n:nat}{length:nat | length <= n} (context: $SHA.ctx256(message), data: !$A.barr(loc, n, data_cells), length_given: int length): void =
  consume{message,other}{length}($SHA.update256_proved(context, data, length_given))

implement main0 () = ()

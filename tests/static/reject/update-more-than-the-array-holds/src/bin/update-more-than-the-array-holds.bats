#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* update reads the first len cells of the data: len is at most the array's size *)
fn claim {message,data_cells:$A.cells}{loc:agz}{n:nat}{length:nat | n < length} (context: $SHA.ctx256(message), data: !$A.barr(loc, n, data_cells), length_given: int length): void =
  case+ $SHA.update256_proved(context, data, length_given) of
  | ~$SHA.Updated256(_ | carry_mid) => let val+ ~$SHA.ctx256_mk(_, _, _, _, _ | chain_array, fill, block_array, _, _, _, _) = carry_mid in $A.barr_free(chain_array); $A.barr_free(fill); $A.barr_free(block_array) end
  | ~$SHA.Stopped256(_ | carry_mid) => let val+ ~$SHA.ctx256_mk(_, _, _, _, _ | chain_array, fill, block_array, _, _, _, _) = carry_mid in $A.barr_free(chain_array); $A.barr_free(fill); $A.barr_free(block_array) end

implement main0 () = ()

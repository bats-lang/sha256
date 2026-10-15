#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* The SHA-1 incremental proved API as a caller reads it: two pieces fed one
   after the other make the message of the first piece's first k1 cells and
   then the second piece's first k2, and the digest is that message's. *)

fn free1 {message:$A.cells} (context: $SHA.ctx1(message)): void = let
  val+ ~$SHA.ctx1_mk(_, _, _, _, _ | chain_array, schedule_array, block_array, _, _, _, _) = context
in $A.barr_free(chain_array); $A.barr_free(schedule_array); $A.barr_free(block_array) end

fn two_pieces {first_cells,second_cells:$A.cells}{first_loc,second_loc:agz}{first_size,second_size:nat}{first_length:nat | first_length <= first_size}{second_length:nat | second_length <= second_size}{out_loc:agz}{out_cells:$A.cells}
  (first: !$A.barr(first_loc, first_size, first_cells), first_given: int first_length, second: !$A.barr(second_loc, second_size, second_cells), second_given: int second_length, out: $A.barr(out_loc, 20, out_cells)): void = let
  val first_context = $SHA.init1_proved()
in
  case+ $SHA.update1_proved(first_context, first, first_given) of
  | ~$SHA.Updated1(held1 | context1) =>
    (case+ $SHA.update1_proved(context1, second, second_given) of
     | ~$SHA.Updated1(held2 | context2) => let
         val (digest, placed | out) = $SHA.finish1_proved(context2, out)
       in $A.barr_free(out) end
     | ~$SHA.Stopped1(_ | context2) => let val () = free1(context2) in $A.barr_free(out) end)
  | ~$SHA.Stopped1(_ | context1) => let val () = free1(context1) in $A.barr_free(out) end
end

implement main0 () = ()

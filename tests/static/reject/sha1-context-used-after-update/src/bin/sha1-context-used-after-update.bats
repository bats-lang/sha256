#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* a SHA-1 context is used once: update gives the next one *)

fn free1 {message:$A.cells} (context: $SHA.ctx1(message)): void = let
  val+ ~$SHA.ctx1_mk(_, _, _, _, _ | chain_array, schedule_array, block_array, _, _, _, _) = context
in $A.barr_free(chain_array); $A.barr_free(schedule_array); $A.barr_free(block_array) end

fn claim {message,data_cells:$A.cells}{loc:agz}{n:nat}{length:nat | length <= n}{out_loc:agz}{out_cells:$A.cells}
  (context: $SHA.ctx1(message), data: !$A.barr(loc, n, data_cells), length_given: int length, out: $A.barr(out_loc, 20, out_cells)): void = let
  val r = $SHA.update1_proved(context, data, length_given)
  val (_, _ | out) = $SHA.finish1_proved(context, out)
  val () = $A.barr_free(out)
in case+ r of
   | ~$SHA.Updated1(_ | c) => free1(c)
   | ~$SHA.Stopped1(_ | c) => free1(c)
end

implement main0 () = ()

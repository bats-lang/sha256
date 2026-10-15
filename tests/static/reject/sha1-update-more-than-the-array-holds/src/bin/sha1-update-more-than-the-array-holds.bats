#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* update1_proved takes at most the cells the array holds *)

fn free1 {message:$A.cells} (context: $SHA.ctx1(message)): void = let
  val+ ~$SHA.ctx1_mk(_, _, _, _, _ | chain_array, schedule_array, block_array, _, _, _, _) = context
in $A.barr_free(chain_array); $A.barr_free(schedule_array); $A.barr_free(block_array) end

fn claim {message,data_cells:$A.cells}{loc:agz}{n:nat} (context: $SHA.ctx1(message), data: !$A.barr(loc, n, data_cells), size: int n): void =
  case+ $SHA.update1_proved(context, data, size + 1) of
  | ~$SHA.Updated1(_ | c) => free1(c)
  | ~$SHA.Stopped1(_ | c) => free1(c)

implement main0 () = ()

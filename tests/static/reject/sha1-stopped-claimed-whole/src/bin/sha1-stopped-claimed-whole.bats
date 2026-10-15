#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* a Stopped1 held only the first i of the bytes: all `length` of them are not in the message *)

fn free1 {message:$A.cells} (context: $SHA.ctx1(message)): void = let
  val+ ~$SHA.ctx1_mk(_, _, _, _, _ | chain_array, schedule_array, block_array, _, _, _, _) = context
in $A.barr_free(chain_array); $A.barr_free(schedule_array); $A.barr_free(block_array) end

fn claim {message,data_cells:$A.cells}{loc:agz}{n:nat}{length:nat | length <= n}
  (context: $SHA.ctx1(message), data: !$A.barr(loc, n, data_cells), length_given: int length)
  : [message_after:$A.cells] ($SHA.HELD(message, data_cells, length, message_after) | $SHA.ctx1(message_after)) =
  case+ $SHA.update1_proved(context, data, length_given) of
  | ~$SHA.Updated1(held | c) => (held | c)
  | ~$SHA.Stopped1(held | c) => (held | c)

implement main0 () = ()

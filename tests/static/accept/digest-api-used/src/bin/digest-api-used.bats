#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* The proved API as a caller reads it: two pieces fed one after the other
   make the message of the first piece's first k1 cells and then the second
   piece's first k2, and the digest and its hex digits are those of that
   message. Also the one-shot digests of SHA-256 and SHA-1. *)
fn free_ctx {message:$A.cells} (context: $SHA.ctx256(message)): void = let
  val+ ~$SHA.ctx256_mk(_, _, _, _, _ | chain_array, schedule_array, block_array, _, _, _, _) = context
in $A.barr_free(chain_array); $A.barr_free(schedule_array); $A.barr_free(block_array) end

(* the first piece after nothing, the second after that: one message *)
prfn chained {first_cells,second_cells,ms1,ms2:$A.cells}{first_length,second_length:nat}
  (first: $SHA.HELD($A.cnil(), first_cells, first_length, ms1), second: $SHA.HELD(ms1, second_cells, second_length, ms2)): $SHA.HELD(ms1, second_cells, second_length, ms2) = second

fn two_pieces {first_cells,second_cells:$A.cells}{first_loc,second_loc:agz}{first_size,second_size:nat}{first_length:nat | first_length <= first_size}{second_length:nat | second_length <= second_size}{out_loc:agz}{out_cells:$A.cells}
  (first: !$A.barr(first_loc, first_size, first_cells), first_given: int first_length, second: !$A.barr(second_loc, second_size, second_cells), second_given: int second_length, out: $A.barr(out_loc, 64, out_cells)): void = let
  val first_context = $SHA.init256_proved()
in
  case+ $SHA.update256_proved(first_context, first, first_given) of
  | ~$SHA.Updated256(held1 | context1) =>
    (case+ $SHA.update256_proved(context1, second, second_given) of
     | ~$SHA.Updated256(held2 | context2) => let
         prval _ = chained(held1, held2)
         val (digest, hex | out) = $SHA.finish256_proved(context2, out)
       in $A.barr_free(out) end
     | ~$SHA.Stopped256(_ | context2) => let val () = free_ctx(context2) in $A.barr_free(out) end)
  | ~$SHA.Stopped256(_ | context1) => let val () = free_ctx(context1) in $A.barr_free(out) end
end

fn once {loc:agz}{size:nat}{data_cells:$A.cells}{length:nat | length <= size; length <= 65535}{out_loc:agz}{out_cells:$A.cells}
  (data: !$A.barr(loc, size, data_cells), length_given: int length, out: $A.barr(out_loc, 64, out_cells), out_sha1: $A.barr(out_loc, 20, out_cells)): void = let
  val (held, digest, hex | out) = $SHA.sha256_digest_proved(data, length_given, out)
  val (held1, digest1, five | out_sha1) = $SHA.sha1_digest_proved(data, length_given, out_sha1)
in $A.barr_free(out); $A.barr_free(out_sha1) end

implement main0 () = ()

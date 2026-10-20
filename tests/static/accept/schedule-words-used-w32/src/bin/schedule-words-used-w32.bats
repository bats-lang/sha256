#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use sha256 as SHA

(* The schedule of a block, and what its proofs say: W_20 is in the array
   at 80 and is what the standard says it is (the same sigmas and sums of
   the words it names), and a word set afterwards beyond the schedule
   leaves it. *)
fn schedule_twenty {lm:agz}{nm:nat}{msg:$A.cells}{at:nat | at + 64 <= nm}{lw:agz}{words:$A.cells}
  (message: !$A.barr(lm, nm, msg), at: int at, array: $A.barr(lw, 256, words)): int = let
  val [words2:$A.cells] (listed | array) = $SHA.schedule_sha256(message, at, array)
  prval @(stored, specified) = $SHA.schedule_array_get{$SHA.sha256_kind()}{words2,msg}{at,64,20}(listed)
  val (read | word_value) = $SHA.word_get_w32(array, 80)
  prval () = $SHA.word_at_functional(read, stored)
  prval $SHA.SCHEDULE_sha256(back2, back7, back15, back16, sigma1, sigma0, add1, add2, add3) = specified
  val (_ | high_byte) = $AR.word32_byte(word_value, 0)
  val () = $A.barr_free(array)
in high_byte end

implement main0 () = ()

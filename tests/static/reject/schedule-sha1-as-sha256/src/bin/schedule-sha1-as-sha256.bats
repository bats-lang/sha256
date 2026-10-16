#include "share/atspre_staload.hats"
#use array as A
#use sha256 as SHA

(* The schedule of SHA-1 is not SHA-256's, though both are the block's
   words and others from them: the kinds are different *)
fn claim {lm:agz}{nm:nat}{msg:$A.cells}{at:nat | at + 64 <= nm}{lw:agz}{words:$A.cells}
  (message: !$A.barr(lm, nm, msg), at: int at, array: $A.barr(lw, 320, words)): void = let
  val (listed | array) = $SHA.schedule_sha1(message, at, array)
  prval wrong: $SHA.SCHEDULE_ARRAY($SHA.sha256_kind(), words, msg, at, 80) = listed
  val () = $A.barr_free(array)
in end

implement main0 () = ()

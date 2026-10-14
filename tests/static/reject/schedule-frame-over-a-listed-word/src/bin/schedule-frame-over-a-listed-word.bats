#include "share/atspre_staload.hats"
#use array as A
#use sha256 as SHA

(* Setting the word at 12 (word 3) is not beyond the first 4 words: they
   are kept only if it is at 16 or later *)
prfn claim {kind:$SHA.schedule_kind}{words,words2,msg:$A.cells}{at,high,low:nat}
  (set: $SHA.WORD_SET(words, 12, high, low, words2), listed: $SHA.SCHEDULE_ARRAY(kind, words, msg, at, 4))
  : $SHA.SCHEDULE_ARRAY(kind, words2, msg, at, 4) = $SHA.schedule_array_frame(set, listed)

implement main0 () = ()

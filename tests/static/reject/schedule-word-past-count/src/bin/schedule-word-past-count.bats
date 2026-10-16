#include "share/atspre_staload.hats"
#use array as A
#use sha256 as SHA

(* Of the first 16 words, there is no word 16 to get *)
prfn claim {kind:$SHA.schedule_kind}{words,msg:$A.cells}{at:nat}
  (listed: $SHA.SCHEDULE_ARRAY(kind, words, msg, at, 16))
  : [high,low:nat] ($SHA.WORD_AT(words, 64, high, low), $SHA.SCHEDULE(kind, msg, at, 16, high, low)) =
  $SHA.schedule_array_get{kind}{words,msg}{at,16,16}(listed)

implement main0 () = ()

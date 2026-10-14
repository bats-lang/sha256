#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* a word's halves are under 65536, not under 65535 *)
prfn claim {cells:$A.cells}{at,high,low:nat} (word: $SHA.WORD_AT(cells, at, high, low)): [high < 65535] void =
  $SHA.word_at_bound(word)

implement main0 () = ()

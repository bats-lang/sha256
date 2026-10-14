#include "share/atspre_staload.hats"
#use array as A
#use sha256 as SHA

(* Setting the word at 4 leaves the word at 6 as it was only if the two
   share no cell: they share cells 6 and 7 *)
prfn claim {cs,cs2:$A.cells}{high,low,other_high,other_low:nat}
  (set: $SHA.WORD_SET(cs, 4, high, low, cs2), word: $SHA.WORD_AT(cs, 6, other_high, other_low))
  : $SHA.WORD_AT(cs2, 6, other_high, other_low) = $SHA.word_set_other(set, word)

implement main0 () = ()

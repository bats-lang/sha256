#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* Setting the word 1:2 puts the word 1:2 in the four cells, not the word
   2:1: the type of a word32 is its halves, so the proof cannot be claimed
   for the swapped ones *)
fn claim {l:agz}{n,at:nat | at + 3 < n}{cs:$A.cells}
  (cells: $A.barr(l, n, cs), at: int at, x: $AR.word32(1, 2))
  : [cs2:$A.cells] ($SHA.WORD_SET(cs, at, 2, 1, cs2) | $A.barr(l, n, cs2)) =
  $SHA.word_set_w32(cells, at, x)

implement main0 () = ()

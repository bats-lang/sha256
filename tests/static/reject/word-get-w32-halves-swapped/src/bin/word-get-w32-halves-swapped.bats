#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* The word read from the cells at `at` is the word the proof says they
   hold: 1:2 here, so it cannot be given the type of the word 2:1 *)
fn claim {l:agz}{n,at:nat | at + 3 < n}{cs:$A.cells}
  (cells: !$A.barr(l, n, cs), at: int at, have: $SHA.WORD_AT(cs, at, 1, 2))
  : $AR.word32(2, 1) = let
  val (read | x) = $SHA.word_get_w32(cells, at)
  prval () = $SHA.word_at_functional(read, have)
in x end

implement main0 () = ()

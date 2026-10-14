#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* the byte's high digit is written first *)
prfn claim {out_cells,chain_cells:$A.cells}{n:nat}{value,high_nibble,low_nibble,first_char,second_char:nat | value < 256; high_nibble < 16; low_nibble < 16; value == 16*high_nibble + low_nibble}
  (before: $SHA.HEXOF(out_cells, chain_cells, n), nth: $A.NTH(chain_cells, n, value), first: $SHA.HEX_DIGIT(high_nibble, first_char), second: $SHA.HEX_DIGIT(low_nibble, second_char),
   at_even: $A.NTH(out_cells, 2*n, first_char), at_odd: $A.NTH(out_cells, 2*n + 1, second_char)): $SHA.HEXOF(out_cells, chain_cells, n + 1) =
  $SHA.HEXOF_next(before, nth, second, first, at_even, at_odd)

implement main0 () = ()

#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* The count of a one-byte message, and the sequence of its padding's first
   byte, built from the definitions. *)
prfn one_byte (): $SHA.COUNTED($A.ccons(97, $A.cnil()), 0, 0, 0, 1) =
  $SHA.COUNTED_byte($SHA.COUNTED_nil(), $SHA.SNOC_nil())

prfn first_block_of_the_next (): $SHA.COUNTED($A.ccons(97, $A.cnil()), 0, 0, 0, 1) = one_byte()

prfn full_block_hashed {message:$A.cells} (counted: $SHA.COUNTED(message, 0, 0, 1022, 64)): $SHA.COUNTED(message, 0, 0, 1023, 0) =
  $SHA.COUNTED_norm(counted, $SHA.NORM_block())

prfn carry_into_the_next_digit {message:$A.cells} (counted: $SHA.COUNTED(message, 5, 65535, 1023, 64)): $SHA.COUNTED(message, 5, 65535, 1023, 64) =
  counted

prfn carry_into_nh {message:$A.cells} (counted: $SHA.COUNTED(message, 0, 7, 1023, 64)): $SHA.COUNTED(message, 0, 8, 0, 0) =
  $SHA.COUNTED_norm(counted, $SHA.NORM_carry())

prfn carry_into_n2 {message:$A.cells} (counted: $SHA.COUNTED(message, 0, 65535, 1023, 64)): $SHA.COUNTED(message, 1, 0, 0, 0) =
  $SHA.COUNTED_norm(counted, $SHA.NORM_carry2())

prfn zeros_short (): $SHA.ZCOUNT(55, 0) = $SHA.ZCOUNT_short()
prfn zeros_short_none (): $SHA.ZCOUNT(0, 55) = $SHA.ZCOUNT_short()
prfn zeros_long (): $SHA.ZCOUNT(56, 63) = $SHA.ZCOUNT_long()
prfn zeros_long_last (): $SHA.ZCOUNT(63, 56) = $SHA.ZCOUNT_long()

implement main0 () = ()

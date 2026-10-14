#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* the first padding block took 63 - b zeros: the second continues from there *)
fn claim {block_loc:agz}{block_cells,message,marked,first_padded:$A.cells}
  (block_array: $A.barr(block_loc, 64, block_cells), list: $SHA.LIST(first_padded), counted: $SHA.COUNTED(message, 0, 0, 0, 60),
   marking: $SHA.SNOC(message, 128, marked), zeroing: $SHA.ZSNOC(marked, 62, first_padded)): void = let
  val (_, _ | block_array) = $SHA.pad_long_second(block_array, 0, 0, 0, 60, list, counted, marking, zeroing)
in $A.barr_free(block_array) end

implement main0 () = ()

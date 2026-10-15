#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* pad_long_first is for 56 bytes or more: 55 fit the length in the same block *)
fn claim {block_loc:agz}{block_cells,hashed_bytes,message:$A.cells}
  (block_array: $A.barr(block_loc, 64, block_cells), held: $SHA.HELD(hashed_bytes, block_cells, 55, message), list: $SHA.LIST(message)): void = let
  val (_, _, _, _ | block_array) = $SHA.pad_long_first(block_array, 55, held, list)
in $A.barr_free(block_array) end

implement main0 () = ()

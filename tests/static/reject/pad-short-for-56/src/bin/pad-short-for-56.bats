#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* pad_short is for 55 bytes or fewer in the block: 56 have no room for the length *)
fn claim {block_loc:agz}{block_cells,hashed_bytes,message:$A.cells}
  (block_array: $A.barr(block_loc, 64, block_cells), held: $SHA.HELD(hashed_bytes, block_cells, 56, message), list: $SHA.LIST(message),
   counted: $SHA.COUNTED(message, 0, 0, 0, 56)): void = let
  val (_, _ | block_array) = $SHA.pad_short(block_array, 0, 0, 0, 56, held, list, counted)
in $A.barr_free(block_array) end

implement main0 () = ()

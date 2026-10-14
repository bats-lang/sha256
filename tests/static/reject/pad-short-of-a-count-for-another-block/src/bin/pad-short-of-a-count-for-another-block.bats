#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* the padding of the message counted for 10 bytes in the block is not the
   padding of a message of 11 *)
fn claim {block_loc:agz}{block_cells,hashed_bytes,message:$A.cells}
  (block_array: $A.barr(block_loc, 64, block_cells), held: $SHA.HELD(hashed_bytes, block_cells, 10, message), list: $SHA.LIST(message),
   counted: $SHA.COUNTED(message, 0, 0, 0, 11)): void = let
  val (_, _ | block_array) = $SHA.pad_short(block_array, 0, 0, 0, 10, held, list, counted)
in $A.barr_free(block_array) end

implement main0 () = ()

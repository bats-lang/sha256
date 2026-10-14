#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* a block is the 64 bytes from cell 0 of the array it is compressed from *)
prfn claim {hashed_bytes,hashed_after,cells:$A.cells}{chaining,chaining_after:$SHA.eight_words}
  (hashed: $SHA.HASHED256(hashed_bytes, chaining), block: $SHA.SHA256_BLOCK(cells, 64, chaining, chaining_after), held: $SHA.HELD(hashed_bytes, cells, 64, hashed_after))
  : $SHA.HASHED256(hashed_after, chaining_after) =
  $SHA.HASHED256_block(hashed, block, held)

implement main0 () = ()

#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* the block compressed is the block put after the bytes: the same cells *)
prfn claim {hashed_bytes,hashed_after,cells,other:$A.cells}{chaining,chaining_after:$SHA.eight_words}
  (hashed: $SHA.HASHED256(hashed_bytes, chaining), block: $SHA.SHA256_BLOCK(other, 0, chaining, chaining_after), held: $SHA.HELD(hashed_bytes, cells, 64, hashed_after))
  : $SHA.HASHED256(hashed_after, chaining_after) =
  $SHA.HASHED256_block(hashed, block, held)

implement main0 () = ()

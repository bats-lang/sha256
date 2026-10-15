#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* the block is compressed onto the value the bytes before it made *)
prfn claim {hashed_bytes,hashed_after,cells:$A.cells}{chaining,chaining_after,other:$SHA.eight_words}
  (hashed: $SHA.HASHED256(hashed_bytes, chaining), block: $SHA.SHA256_BLOCK(cells, 0, other, chaining_after), held: $SHA.HELD(hashed_bytes, cells, 64, hashed_after))
  : $SHA.HASHED256(hashed_after, chaining_after) =
  $SHA.HASHED256_block(hashed, block, held)

implement main0 () = ()

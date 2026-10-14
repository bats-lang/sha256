#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* the digest hashes the padded message, not the message *)
prfn claim {message,padded:$A.cells}{count_top,count_high,count_blocks,fill:nat}{chaining:$SHA.eight_words}
  (pad: $SHA.PAD(message, count_top, count_high, count_blocks, fill, padded), hashed: $SHA.HASHED256(message, chaining)): $SHA.DIGEST256(message, chaining) =
  $SHA.DIGEST256_mk(pad, hashed)

implement main0 () = ()

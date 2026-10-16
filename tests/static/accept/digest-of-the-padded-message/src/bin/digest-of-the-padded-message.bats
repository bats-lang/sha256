#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* the digest of m is what hashing the padded message makes *)
prfn claim {message,padded:$A.cells}{count_top,count_high,count_blocks,fill:nat}{chaining:$SHA.eight_words}
  (pad: $SHA.PAD(message, count_top, count_high, count_blocks, fill, padded), hashed: $SHA.HASHED256(padded, chaining)): $SHA.DIGEST256(message, chaining) =
  $SHA.DIGEST256_mk(pad, hashed)

prfn claim1 {message,padded:$A.cells}{count_top,count_high,count_blocks,fill:nat}{chaining:$SHA.five_words}
  (pad: $SHA.PAD(message, count_top, count_high, count_blocks, fill, padded), hashed: $SHA.HASHED1(padded, chaining)): $SHA.DIGEST1(message, chaining) =
  $SHA.DIGEST1_mk(pad, hashed)

implement main0 () = ()

#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* SHA-1's chaining value is five words, SHA-256's eight: a SHA-1 digest is no SHA-256 one *)
prfn claim {message,padded:$A.cells}{count_top,count_high,count_blocks,fill:nat}{chaining:$SHA.five_words}
  (pad: $SHA.PAD(message, count_top, count_high, count_blocks, fill, padded), hashed: $SHA.HASHED1(padded, chaining)): $SHA.DIGEST256(message, chaining) =
  $SHA.DIGEST256_mk(pad, hashed)

implement main0 () = ()

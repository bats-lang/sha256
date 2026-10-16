#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* the initial value is the hash of no bytes only *)
prfn claim {message:$A.cells}{chaining:$SHA.eight_words} (iv: $SHA.SHA256_IV(chaining)): $SHA.HASHED256($A.ccons(1, message), chaining) =
  $SHA.HASHED256_start(iv)

implement main0 () = ()

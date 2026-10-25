#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* H(0)_0 one over: x^2 <= p * 2^64 fails, with x = floor(sqrt(p) * 2^32) (sha256#77) *)
prfn claim (): $SHA.SHA256_IV($SHA.eight($SHA.w32(0x6a09, 0xe668), $SHA.w32(0xbb67, 0xae85), $SHA.w32(0x3c6e, 0xf372), $SHA.w32(0xa54f, 0xf53a),
  $SHA.w32(0x510e, 0x527f), $SHA.w32(0x9b05, 0x688c), $SHA.w32(0x1f83, 0xd9ab), $SHA.w32(0x5be0, 0xcd19))) =
  $SHA.SHA256_IV_mk()

implement main0 () = ()

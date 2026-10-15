#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* SHA-1's initial value has five words: it is no SHA-256 initial value *)
prfn claim (): $SHA.HASHED1($A.cnil(), $SHA.five($SHA.w32(0x6745, 0x2301), $SHA.w32(0xefcd, 0xab89), $SHA.w32(0x98ba, 0xdcfe), $SHA.w32(0x1032, 0x5476), $SHA.w32(0xc3d2, 0xe1f1))) =
  $SHA.HASHED1_start($SHA.SHA1_IV_mk())

implement main0 () = ()

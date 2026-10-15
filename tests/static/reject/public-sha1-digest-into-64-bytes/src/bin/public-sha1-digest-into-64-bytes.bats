#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* the SHA-1 is 20 bytes *)
fn claim {l:agz}{n:pos}{lo:agz} (data: !$A.borrow(byte, l, n), size: int n, out: !$A.arr(byte, lo, 64)): void =
  $SHA.sha1_digest(data, size, out)

implement main0 () = ()

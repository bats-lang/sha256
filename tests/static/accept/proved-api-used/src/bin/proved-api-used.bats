#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* The proved API as a caller reads it: the hash of an array, the same in
   pieces, and the SHA-1 of a borrowed one. *)
fn all {l:agz}{n:pos}{lo,ls:agz} (data: $A.arr(byte, l, n), size: int n, out: !$A.arr(byte, lo, 64), sum: !$A.arr(byte, ls, 20)): void = let
  val () = $SHA.proved_hash(data, size, out)
  val c = $SHA.proved_init()
  val () = $SHA.proved_update(c, data, size)
  val () = $SHA.proved_update(c, data, 0)
  val () = $SHA.proved_finish(c, out)
  val @(frozen, borrowed) = $A.freeze<byte>(data)
  val () = $SHA.sha1_digest(borrowed, size, sum)
  val () = $A.drop<byte>(frozen, borrowed)
  val () = $A.free<byte>($A.thaw<byte>(frozen))
in end

implement main0 () = ()

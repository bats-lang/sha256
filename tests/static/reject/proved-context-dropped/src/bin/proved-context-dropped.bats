#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use sha256 as SHA

(* a context that is never finished is a leak the types see *)
fn claim (): void = let
  val c = $SHA.proved_init()
in end

implement main0 () = ()

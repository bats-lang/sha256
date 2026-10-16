#include "share/atspre_staload.hats"
#use array as A
#use sha256 as SHA

(* Time of hashing 1 MiB: SHA-256 by hash (the fast code), by proved_hash
   (the proved code) and SHA-1 by sha1_digest (proved), each against a
   budget (sha256#29, #34). The fast budget is a few times what the fast
   code takes in a debug build and well under what the proved code takes
   (hash took 0.3 s and proved_hash 2.8 s on the machine of the measurement),
   so that hash running the proved code by mistake fails it. The proved
   budgets are a multiple of the proved time, so that a rotation done a bit
   at a time (a million operations a block, 9 s) fails them and a slow runner
   does not. It prints nothing but "ok" and exits 1 over budget. The times go
   to stderr. *)

$UNSAFE begin
%{
#include <time.h>
#include <stdio.h>
#include <stdlib.h>
static double perf_now_ms (void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec * 1000.0 + t.tv_nsec / 1000000.0;
}
static void perf_report (const char *name, double ms) {
  fprintf(stderr, "%s: %.1f ms\n", name, ms);
}
static void perf_fail (void) { exit(1); }
static int perf_over (double ms, double budget_ms) { return ms > budget_ms; }
%}

extern fun perf_now_ms (): double = "mac#"
extern fun perf_report (name: string, ms: double): void = "mac#"
extern fun perf_fail (): void = "mac#"
extern fun perf_over (ms: double, budget: double): int = "mac#"
end


fun fill {l:agz}{n:pos}{i:nat | i <= n} .<n - i>.
  (d: !$A.arr(byte, l, n), n: int n, i: int i): void =
  if i >= n then ()
  else let
    val () = $A.set<byte>(d, i, $A.int2byte(97 + nmod(i, 26)))
  in fill(d, n, i + 1) end

implement main0 () = let
  val d = $A.alloc<byte>(1048576)
  val () = fill(d, 1048576, 0)
  val o = $A.alloc<byte>(64)
  val t0 = perf_now_ms()
  val () = $SHA.hash(d, 1048576, o)
  val t1 = perf_now_ms()
  val () = $SHA.proved_hash(d, 1048576, o)
  val t2 = perf_now_ms()
  val s1 = $A.alloc<byte>(20)
  val @(frozen, borrowed) = $A.freeze<byte>(d)
  val () = $SHA.sha1_digest(borrowed, 1048576, s1)
  val () = $A.drop<byte>(frozen, borrowed)
  val t3 = perf_now_ms()
  val () = perf_report("hash (fast) 1 MiB", t1 - t0)
  val () = perf_report("proved_hash 1 MiB", t2 - t1)
  val () = perf_report("sha1_digest (proved) 1 MiB", t3 - t2)
  val () = $A.free<byte>(s1)
  val () = $A.free<byte>(o)
  val () = $A.free<byte>($A.thaw<byte>(frozen))
in
  if perf_over(t1 - t0, 1500.0) + perf_over(t2 - t1, 6000.0) + perf_over(t3 - t2, 3000.0) > 0 then (println! ("over budget"); perf_fail())
  else println! ("ok")
end

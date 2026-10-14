#include "share/atspre_staload.hats"
#use array as A
#use sha256 as SHA

(* Time of hashing 1 MiB, SHA-256 (hash) and SHA-1 (sha1_digest), against a
   budget (sha256#29, stage E). The budget is a multiple of what the unproved
   code took on the same machine before the public functions ran the proved
   code, so that a rotation done a bit at a time (a million operations a
   block) fails it, and a slow runner does not: it prints nothing but "ok"
   and exits 1 over budget. The times go to stderr. *)

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
  val s1 = $A.alloc<byte>(20)
  val @(frozen, borrowed) = $A.freeze<byte>(d)
  val () = $SHA.sha1_digest(borrowed, 1048576, s1)
  val () = $A.drop<byte>(frozen, borrowed)
  val t2 = perf_now_ms()
  val () = perf_report("sha256 1 MiB", t1 - t0)
  val () = perf_report("sha1 1 MiB", t2 - t1)
  val () = $A.free<byte>(s1)
  val () = $A.free<byte>(o)
  val () = $A.free<byte>($A.thaw<byte>(frozen))
in
  if perf_over(t1 - t0, 6000.0) + perf_over(t2 - t1, 3000.0) > 0 then (println! ("over budget"); perf_fail())
  else println! ("ok")
end

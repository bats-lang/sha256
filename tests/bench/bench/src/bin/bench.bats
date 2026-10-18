#include "share/atspre_staload.hats"
#use array as A
#use sha256 as SHA

(* A microbenchmark of the fast SHA-256 (sha256#40): hashes 1 MiB
   BENCH_ITERATIONS times (default 20) with hash, and with BENCH_API=
   incremental in pieces of 4096 bytes through init, update and finish
   (what bats does). It prints the first digest and, on stderr, the
   milliseconds a MiB and the bytes a second. tests/bench/run.sh runs it
   natively, in debug and release, and under callgrind for instructions a
   byte. *)

$UNSAFE begin
%{
#include <time.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static double bench_now_ms (void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec * 1000.0 + t.tv_nsec / 1000000.0;
}
static int bench_iterations (void) {
  const char *s = getenv("BENCH_ITERATIONS");
  int n = s ? atoi(s) : 20;
  return n < 1 ? 1 : n;
}
static int bench_incremental (void) {
  const char *s = getenv("BENCH_API");
  return s != NULL && strcmp(s, "incremental") == 0;
}
static void bench_report (int iterations, double ms) {
  fprintf(stderr, "%d x 1 MiB: %.2f ms a MiB, %.1f MB/s\n", iterations,
          ms / iterations, iterations * 1.048576 / ms * 1000.0);
}
%}

extern fun bench_now_ms (): double = "mac#"
extern fun bench_iterations (): [k:nat] int k = "mac#"
extern fun bench_incremental (): int = "mac#"
extern fun bench_report (iterations: int, ms: double): void = "mac#"
end

fun fill {l:agz}{n:pos}{i:nat | i <= n} .<n - i>.
  (d: !$A.arr(byte, l, n), n: int n, i: int i): void =
  if i >= n then ()
  else let
    val () = $A.set<byte>(d, i, $A.int2byte(97 + nmod(i, 26)))
  in fill(d, n, i + 1) end

fn once_hash {l:agz}{lo:agz}(d: !$A.arr(byte, l, 1048576), o: !$A.arr(byte, lo, 64)): void =
  $SHA.hash(d, 1048576, o)

fn once_incremental {l:agz}{lo:agz}(d: !$A.arr(byte, l, 1048576), o: !$A.arr(byte, lo, 64)): void = let
  val c = $SHA.init()
  fun go {l:agz}{i:nat | i <= 256} .<256 - i>.
    (c: !$SHA.ctx, d: !$A.arr(byte, l, 1048576), i: int i): void =
    if i >= 256 then ()
    else let
      (* the same bytes each time: hashing, not the content, is measured *)
      val () = $SHA.update(c, d, 4096)
    in go(c, d, i + 1) end
  val () = go(c, d, 0)
in $SHA.finish(c, o) end

fun loop {l:agz}{lo:agz}{k:nat} .<k>.
  (d: !$A.arr(byte, l, 1048576), o: !$A.arr(byte, lo, 64), inc: bool, k: int k): void =
  if k <= 0 then ()
  else let
    val () = if inc then once_incremental(d, o) else once_hash(d, o)
  in loop(d, o, inc, k - 1) end

implement main0 () = let
  val d = $A.alloc<byte>(1048576)
  val () = fill(d, 1048576, 0)
  val o = $A.alloc<byte>(64)
  val n = bench_iterations()
  val inc = (bench_incremental() > 0)
  val t0 = bench_now_ms()
  val () = loop(d, o, inc, n)
  val t1 = bench_now_ms()
  val () = bench_report(n, t1 - t0)
  fun show {lo:agz}{i:nat | i <= 64} .<64 - i>.
    (o: !$A.arr(byte, lo, 64), i: int i): void =
    if i >= 64 then println! ()
    else let
      val () = print_char(int2char0(byte2int0($A.get<byte>(o, i))))
    in show(o, i + 1) end
  val () = show(o, 0)
  val () = $A.free<byte>(o)
  val () = $A.free<byte>(d)
in end

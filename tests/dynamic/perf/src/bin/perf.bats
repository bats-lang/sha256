#include "share/atspre_staload.hats"
#use array as A
#use sha256 as SHA

(* Instructions of hashing 1 MiB (perf-instructions, sha256#65, sha256#29,
   #34): the test runs itself three times under `valgrind --tool=callgrind`,
   once for SHA-256 by hash (the fast code), by proved_hash (the proved code)
   and SHA-1 by sha1_digest (proved), and decides by the instructions
   callgrind collects, which load does not change. It reads no clock. The
   budgets (in millions of instructions, with their reasons in sha256's
   CLAUDE.md, "The perf test counts instructions") are what the counts of
   the code give. It prints "ok" and exits 1 over a budget, or when a count
   cannot be read; the counts go to stderr. *)

$UNSAFE begin
%{
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static const char *perf_self = "";
static int perf_argc = 0;
static char *perf_argv1 = "";
__attribute__((constructor)) static void perf_capture (int argc, char **argv) {
  perf_argc = argc;
  if (argc > 0) perf_self = argv[0];
  if (argc > 1) perf_argv1 = argv[1];
}
/* the mode this process was started with: 0 is the parent, 1 to 3 a child */
static int perf_mode (void) { return perf_argc > 1 ? atoi(perf_argv1) : 0; }
/* run this binary as a child of the mode under callgrind; its collected
   instructions in millions, or -1 when valgrind does not give a count */
static int perf_millions (int mode) {
  char command[1024];
  char line[1024];
  long long collected = -1;
  FILE *pipe;
  snprintf(command, sizeof command,
    "valgrind --tool=callgrind --callgrind-out-file=perf-callgrind.out '%s' %d 2>&1",
    perf_self, mode);
  pipe = popen(command, "r");
  if (pipe == NULL) return -1;
  while (fgets(line, sizeof line, pipe) != NULL) {
    char *at = strstr(line, "Collected : ");
    if (at != NULL) collected = atoll(at + 12);
  }
  if (pclose(pipe) != 0) return -1;
  remove("perf-callgrind.out");
  return collected < 0 ? -1 : (int)(collected / 1000000);
}
static void perf_report (const char *name, int millions) {
  fprintf(stderr, "%s: %d million instructions\n", name, millions);
}
static void perf_fail (void) { exit(1); }
static int perf_over (int millions, int budget) { return millions < 0 || millions > budget; }
%}

extern fun perf_mode (): int = "mac#"
extern fun perf_millions (mode: int): int = "mac#"
extern fun perf_report (name: string, millions: int): void = "mac#"
extern fun perf_fail (): void = "mac#"
extern fun perf_over (millions: int, budget: int): int = "mac#"
end


fun fill {l:agz}{n:pos}{i:nat | i <= n} .<n - i>.
  (d: !$A.arr(byte, l, n), n: int n, i: int i): void =
  if i >= n then ()
  else let
    val () = $A.set<byte>(d, i, $A.int2byte(97 + nmod(i, 26)))
  in fill(d, n, i + 1) end

(* a child hashes 1 MiB the way its mode names, so callgrind counts only that *)
fn child_fast (): void = let
  val d = $A.alloc<byte>(1048576)
  val () = fill(d, 1048576, 0)
  val o = $A.alloc<byte>(64)
  val () = $SHA.hash(d, 1048576, o)
  val () = $A.free<byte>(o)
  val () = $A.free<byte>(d)
in end

fn child_proved (): void = let
  val d = $A.alloc<byte>(1048576)
  val () = fill(d, 1048576, 0)
  val o = $A.alloc<byte>(64)
  val () = $SHA.proved_hash(d, 1048576, o)
  val () = $A.free<byte>(o)
  val () = $A.free<byte>(d)
in end

fn child_sha1 (): void = let
  val d = $A.alloc<byte>(1048576)
  val () = fill(d, 1048576, 0)
  val o = $A.alloc<byte>(20)
  val @(frozen, borrowed) = $A.freeze<byte>(d)
  val () = $SHA.sha1_digest(borrowed, 1048576, o)
  val () = $A.drop<byte>(frozen, borrowed)
  val () = $A.free<byte>(o)
  val () = $A.free<byte>($A.thaw<byte>(frozen))
in end

implement main0 () = let
  val mode = perf_mode()
in
  if mode = 1 then child_fast()
  else if mode = 2 then child_proved()
  else if mode = 3 then child_sha1()
  else let
    val fast = perf_millions(1)
    val proved = perf_millions(2)
    val sha1 = perf_millions(3)
    val () = perf_report("hash (fast) 1 MiB", fast)
    val () = perf_report("proved_hash 1 MiB", proved)
    val () = perf_report("sha1_digest (proved) 1 MiB", sha1)
  in
    if perf_over(fast, 2000) + perf_over(proved, 9000) + perf_over(sha1, 9000) > 0 then (println! ("over budget"); perf_fail())
    else println! ("ok")
  end
end

#include "share/atspre_staload.hats"
#use array as A
#use sha256 as SHA

(* The proved SHA-256 (proved_hash, proved_init, proved_update,
   proved_finish) and SHA-1 (sha1_digest) against the fast SHA-256 (hash,
   init, update, finish) and against known answers (sha256#29, stage E).

   The proofs say the proved code computes FIPS 180-4's digest; the copies
   of the caller's array into the proved code's, and the digits back, are
   glue the types do not check, and the fast code is not proved at all.
   So this checks, on bytes:

   - SHA-256 of every prefix length 0 to 200 of a pattern, the proved one
     printed (the harness compares it with Python's hashlib in `expected`)
     and compared here with the fast one;
   - the same for 40 pseudo-random lengths (201 to 5000) of pseudo-random
     bytes (a fixed generator, written again in make-expected.py);
   - the NIST test vectors: "abc", the 448-bit and 896-bit messages and one
     million "a", with the proved and the fast SHA-256 side by side;
   - 1 MiB of a pattern and of pseudo-random bytes, both ways;
   - SHA-1 of every prefix length 1 to 200, the empty message (through the
     incremental proved SHA-1) and the same vectors.

   It prints the digests and the number of times the fast and the proved
   SHA-256 differ, which `expected` has as 0. It does not run under
   valgrind (the proved code under it takes a quarter of an hour for the
   3 MiB): the leak check of the proved functions is `sizes` and `digest`. *)
fn hex_digit (d: int): int = let
  val e = g1ofg0(d)
in if e >= 0 then (if e < 10 then 48 + e else if e < 16 then 87 + e else 63) else 63 end

fun pr_text64 {l:agz}{i:nat | i <= 64} .<64 - i>. (o: !$A.arr(byte, l, 64), i: int i): void =
  if i >= 64 then ()
  else let val () = print_char(int2char0(byte2int0($A.get<byte>(o, i)))) in pr_text64(o, i + 1) end

fun pr_hex20 {l:agz}{i:nat | i <= 20} .<20 - i>. (o: !$A.arr(byte, l, 20), i: int i): void =
  if i >= 20 then ()
  else let
    val b = byte2int0($A.get<byte>(o, i))
    val high = b / 16
    val low = b - 16 * high
    val () = print_char(int2char0(hex_digit(high)))
    val () = print_char(int2char0(hex_digit(low)))
  in pr_hex20(o, i + 1) end

fun same64 {la,lb:agz}{i:nat | i <= 64} .<64 - i>.
  (a: !$A.arr(byte, la, 64), b: !$A.arr(byte, lb, 64), i: int i): bool =
  if i >= 64 then true
  else if byte2int0($A.get<byte>(a, i)) = byte2int0($A.get<byte>(b, i)) then same64(a, b, i + 1)
  else false

(* the fast SHA-256 of d[0, k), as init, update and finish *)
fn fast {l:agz}{n:pos}{k:nat | k <= n}{lo:agz}
  (d: !$A.arr(byte, l, n), k: int k, out: !$A.arr(byte, lo, 64)): void = let
  val c = $SHA.init()
  val () = $SHA.update(c, d, k)
in $SHA.finish(c, out) end

(* the proved SHA-256 of d[0, k) *)
fn proved {l:agz}{n:pos}{k:nat | k <= n}{lo:agz}
  (d: !$A.arr(byte, l, n), k: int k, out: !$A.arr(byte, lo, 64)): void = let
  val c = $SHA.proved_init()
  val () = $SHA.proved_update(c, d, k)
in $SHA.proved_finish(c, out) end

(* Prints "name length proved-digest" and answers 1 when the fast digest
   differs from the proved one, else 0. *)
fn compare_prefix {l:agz}{n:pos}{k:nat | k <= n}
  (name: string, d: !$A.arr(byte, l, n), k: int k): int = let
  val a = $A.alloc<byte>(64)
  val b = $A.alloc<byte>(64)
  val () = fast(d, k, a)
  val () = proved(d, k, b)
  val () = print!(name, " ", k, " ")
  val () = pr_text64(b, 0)
  val () = print_newline()
  val r = (if same64(a, b, 0) then 0 else 1): int
  val () = $A.free<byte>(a)
  val () = $A.free<byte>(b)
in r end

fun fill_pattern {l:agz}{n:pos}{i:nat | i <= n} .<n - i>.
  (d: !$A.arr(byte, l, n), n: int n, i: int i): void =
  if i >= n then ()
  else let
    val () = $A.set<byte>(d, i, $A.int2byte(97 + nmod(i, 26)))
  in fill_pattern(d, n, i + 1) end

(* x(i+1) = (75 * x(i) + 74) mod 65537, the ZX81's generator: byte i is x(i) mod 256 *)
fun fill_pseudo {l:agz}{n:pos}{i:nat | i <= n}{x:nat | x < 65537} .<n - i>.
  (d: !$A.arr(byte, l, n), n: int n, i: int i, x: int x): void =
  if i >= n then ()
  else let
    val () = $A.set<byte>(d, i, $A.int2byte(nmod(x, 256)))
  in fill_pseudo(d, n, i + 1, nmod(75 * x + 74, 65537)) end

fun fill_char {l:agz}{n:pos}{i:nat | i <= n}{c:nat | c < 256} .<n - i>.
  (d: !$A.arr(byte, l, n), n: int n, i: int i, c: int c): void =
  if i >= n then ()
  else let val () = $A.set<byte>(d, i, $A.int2byte(c)) in fill_char(d, n, i + 1, c) end

fn octet (b: int): [v:nat | v < 256] int v = let
  val x = g1ofg0(b)
in if x >= 0 then (if x < 256 then x else 0) else 0 end

fun fill_text {l:agz}{n:pos}{i:nat | i <= n} .<n - i>.
  (d: !$A.arr(byte, l, n), s: string(n), n: int n, i: int i): void =
  if i >= n then ()
  else let
    val () = $A.set<byte>(d, i, $A.int2byte(octet(char2int0(string_get_at_gint(s, i)))))
  in fill_text(d, s, n, i + 1) end

(* every length 0 to 200 of the 201 bytes of d *)
fun sweep256 {l:agz}{k:nat | k <= 200} .<200 - k>.
  (d: !$A.arr(byte, l, 201), k: int k): int =
  if k >= 200 then compare_prefix("sha256", d, 200)
  else compare_prefix("sha256", d, k) + sweep256(d, k + 1)

(* 40 pseudo-random lengths, 201 to 5000, of the pseudo-random bytes of d *)
fun random_lengths {l:agz}{t:nat | t <= 40}{y:nat | y < 65537} .<t>.
  (d: !$A.arr(byte, l, 5001), t: int t, y: int y): int =
  if t <= 0 then 0
  else let
    val y2 = nmod(75 * y + 74, 65537)
    val length = 201 + nmod(y2, 4800)
  in compare_prefix("random", d, length) + random_lengths(d, t - 1, y2) end

fn run_sweeps (): void = let
  val d = $A.alloc<byte>(201)
  val () = fill_pattern(d, 201, 0)
  val different = sweep256(d, 0)
  val () = print!("sha256 prefixes 0 to 200, fast and proved differ ", different, " times\n")
  val () = $A.free<byte>(d)
  val r = $A.alloc<byte>(5001)
  val () = fill_pseudo(r, 5001, 0, 12345)
  val different2 = random_lengths(r, 40, 777)
  val () = print!("sha256 random lengths, fast and proved differ ", different2, " times\n")
  val () = $A.free<byte>(r)
in end

(* the SHA-1 of d[0, k) *)
fn sha1_print {l:agz}{n:pos}{k:pos | k <= n}
  (name: string, d: !$A.borrow(byte, l, n), k: int k): void = let
  val o = $A.alloc<byte>(20)
  val () = $SHA.sha1_digest(d, k, o)
  val () = print!(name, " ", k, " ")
  val () = pr_hex20(o, 0)
  val () = print_newline()
  val () = $A.free<byte>(o)
in end

fun sha1_sweep {l:agz}{k:pos | k <= 201} .<201 - k>.
  (d: !$A.borrow(byte, l, 201), k: int k): void =
  if k > 200 then ()
  else let val () = sha1_print("sha1", d, k) in sha1_sweep(d, k + 1) end

(* the SHA-1 of nothing, by the incremental proved SHA-1 *)
fn sha1_empty (): void = let
  val c = $SHA.init1_proved()
  val (_ | digits) = $A.barr_alloc(20)
  val (_, _ | digits) = $SHA.finish1_proved(c, digits)
  fun loop {lb:agz}{cs:$A.cells}{i:nat | i <= 20} .<20 - i>.
    (digits: !$A.barr(lb, 20, cs), i: int i): void =
    if i >= 20 then ()
    else let
      val (_ | v) = $A.barr_get(digits, i)
      val high = v / 16
      val low = v - 16 * high
      val () = print_char(int2char0(hex_digit(high)))
      val () = print_char(int2char0(hex_digit(low)))
    in loop(digits, i + 1) end
  val () = print!("sha1 empty ")
  val () = loop(digits, 0)
  val () = print_newline()
  val () = $A.barr_free(digits)
in end

fn run_sha1_sweep (): void = let
  val d = $A.alloc<byte>(201)
  val () = fill_pattern(d, 201, 0)
  val @(frozen, borrowed) = $A.freeze<byte>(d)
  val () = sha1_sweep(borrowed, 1)
  val () = $A.drop<byte>(frozen, borrowed)
  val () = $A.free<byte>($A.thaw<byte>(frozen))
in end

(* d is filled; prints the SHA-256 both ways and the SHA-1, then frees d *)
fn whole {l:agz}{n:pos}
  (name: string, d: $A.arr(byte, l, n), n: int n): int = let
  val a = $A.alloc<byte>(64)
  val () = $SHA.hash(d, n, a)
  val () = print!(name, " ", n, " fast ")
  val () = pr_text64(a, 0)
  val () = print_newline()
  val b = $A.alloc<byte>(64)
  val () = $SHA.proved_hash(d, n, b)
  val () = print!(name, " ", n, " proved ")
  val () = pr_text64(b, 0)
  val () = print_newline()
  val r = (if same64(a, b, 0) then 0 else 1): int
  val () = $A.free<byte>(a)
  val () = $A.free<byte>(b)
  val @(frozen, borrowed) = $A.freeze<byte>(d)
  val () = sha1_print(name, borrowed, n)
  val () = $A.drop<byte>(frozen, borrowed)
  val () = $A.free<byte>($A.thaw<byte>(frozen))
in r end

fn named {n:pos | n <= 1048576} (name: string, text: string(n), n: int n): int = let
  val d = $A.alloc<byte>(n)
  val () = fill_text(d, text, n, 0)
in whole(name, d, n) end

fn million (): int = let
  val d = $A.alloc<byte>(1000000)
  val () = fill_char(d, 1000000, 0, 97)
in whole("million-a", d, 1000000) end

fn one_mebibyte_pattern (): int = let
  val d = $A.alloc<byte>(1048576)
  val () = fill_pattern(d, 1048576, 0)
in whole("mebibyte-pattern", d, 1048576) end

fn one_mebibyte_pseudo (): int = let
  val d = $A.alloc<byte>(1048576)
  val () = fill_pseudo(d, 1048576, 0, 4242)
in whole("mebibyte-pseudo", d, 1048576) end

implement main0 () = let
  val () = run_sweeps()
  val () = sha1_empty()
  val () = run_sha1_sweep()
  val v1 = named("abc", "abc", 3)
  val v2 = named("nist-448", "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq", 56)
  val v3 = named("nist-896", "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu", 112)
  val v4 = million()
  val v5 = one_mebibyte_pattern()
  val v6 = one_mebibyte_pseudo()
  val () = print!("whole messages, fast and proved differ ", v1 + v2 + v3 + v4 + v5 + v6, " times\n")
in end

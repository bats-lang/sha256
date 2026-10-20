# sha256

## CI is pinned

Every input to CI is pinned in the source (bats-lang/repository-prototype#269),
so a commit that passes keeps passing:

* `bats.lock` is committed: CI never runs `bats lock` for the package, so
  `bats check` and `bats build` fetch exactly the locked versions, and fail
  when the lock is missing or does not match `bats.toml`. A library's lock
  pins only its own CI and tests; its dependents still resolve their own.
* The compiler is the commit in `.github/bats-version`, read by every
  workflow that builds bats (and by the publish workflow).
* The package repository is fetched at the commit in
  `.github/repository-version`, so what the test packages under `tests/`
  lock (`bats lock --dev`) is pinned too.
* `publish.yml` and `relock-pins.yml` in bats-lang/repository-prototype are
  called by commit, never `@main`.

Pins move only through a reviewed pull request that runs the same CI. The
daily `relock.yml` (the shared `relock-pins.yml`) relocks against the
newest, moves the compiler and repository pins, pushes `relock/<date>`,
opens a pull request listing the old and new versions and dispatches
`check.yml` on it, so a breaking publish shows as a red relock pull
request and main stays green. GITHUB_TOKEN cannot change workflow files,
so without a `RELOCK_TOKEN` secret that pull request lists a workflow pin
that would move instead of moving it: move it in a pull request of its
own. A pull request that needs newer packages runs `bats lock
--repository <dir>` and commits `bats.lock` (and
`.github/repository-version`) with the change.

## The word functions are proved (bats-lang/sha256#29, stage A)

`word_ch`, `word_maj`, `big_sigma_0`, `big_sigma_1`, `small_sigma_0` and
`small_sigma_1` take and give a word as its two 16-bit halves in the
published forms (deprecated, sha256#48: one published version holds both,
then they are removed). The `_w32` forms (`word_ch_w32`, `big_sigma_0_w32`,
...) take and give one `word32(h, l)` (arith's C unsigned int, the halves in
its type), so no proof names 2 to the 32 (the solver is 32-bit). Both return
the proof of the relation `CH`, `MAJ`,
`BIG_SIGMA_0`, ... that is the standard's definition (FIPS 180-4, section
4.1.2) composed from arith's bit specifications. `tests/dynamic/word_functions`
runs them on the published trace of SHA-256 over "abc". The digest
functions are stages B to D of the plan in the issue (done): the proved ones
are `proved_hash`, `proved_init`, `proved_update`, `proved_finish` and
`sha1_digest` (stage E, below), and `hash`, `init`, `update`, `finish` are the
fast unproved code, unchanged.

## Words in an array and the message schedules are proved (bats-lang/sha256#29, stage B)

`WORD_AT(cells, at, high, low)` says the four cells of an array's contents
(array's `barr`, whose cells are in its type) from `at` are the word
high:low, big endian; `WORD_SET(cells, at, high, low, cells2)` says four
cells were set to it. A word needs no array of its own and no change to the
array package: `word_get_w32` reads its four bytes with one call to array's
`barr_get_be32` (sha256#53; its four `NTH` proofs go straight to `WORD_AT`),
and the halves `word_get` is four `barr_get`s; `barr_set`s write, and `word_set_at`, `word_set_other` (a word that shares no cell
with the one set is as it was) and `word_at_functional` are proved from
array's `setc_nth_same`, `setc_nth_other` and `nth_functional`. A message
block's words are the bytes it is, read in place at `at`, so loading a
block needs no copy that the proof would have to follow.

`SCHEDULE(kind, msg, at, t, high, low)` is the standard's definition of
W_t for the block of 64 bytes from `at` of the cells `msg`, with no array in
it: the t-th word of the block for t < 16 and for SHA-256 (FIPS 180-4, section
6.2.2) sigma1(W_t-2) + W_t-7 + sigma0(W_t-15) + W_t-16 by `SMALL_SIGMA_1`,
`SMALL_SIGMA_0` and three `ADD32`, in that order; for SHA-1 (section 6.1.2)
ROTL 1 of W_t-3 xor W_t-8 xor W_t-14 xor W_t-16, the rotation left by one
being `ROTR(31, ...)` (arith has no left rotation; ROTL n = ROTR (32 - n) by the
standard's definition of the two). `SCHEDULE_ARRAY(kind, words, msg, at,
count)` says the first count words of an array, at 4 * t, are W_0 to
W_count-1; `schedule_array_get` and `schedule_array_frame` (setting a word
beyond the first count leaves them) are its lemmas. `schedule_sha256` (64
words, a 256-byte array) and `schedule_sha1` (80 words, 320 bytes) fill the
array from the message block and return `SCHEDULE_ARRAY(..., 64)` or
`(..., 80)`: every word of the array is the standard's. The proofs are
about the halves-based functions, and `proved_hash` and `sha1_digest` run
them (below).

`tests/dynamic/schedule` runs both schedules on the standard's padded
blocks ("abc", the 448-bit message in two blocks) and 64 other bytes against
an independent implementation in C unsigned arithmetic, and prints the
words of "abc" the standard's trace shows (W16 = 61626380, W17 = 000f0000,
...), compared with `expected` made by Python. `tests/static` rejects a
word set over a cell of another, sigma 0 for sigma 1, a SHA-1 schedule
claimed SHA-256's, a word past the count and a frame over a listed word.

## The rounds and the chaining add are proved (bats-lang/sha256#29, stage C)

A state of the rounds is a static `eight_words` (SHA-1: `five_words`) of
`word`s, `w32(high, low)`, so a relation between states names every word of
both and the register shifts of a round are in the indices. `SHA256_ROUND`
is one round of FIPS 180-4, section 6.2.2 step 3: T1 = h + BIG_SIGMA_1(e) +
Ch(e, f, g) + K_t + W_t, T2 = BIG_SIGMA_0(a) + Maj(a, b, c), the new a is
T1 + T2 and the new e is d + T1, each sum an `ADD32` in the standard's order,
the sigmas, Ch and Maj the stage A relations. `SHA256_ROUNDS(msg, at, t, init,
state)` says that `state` is the working variables after t rounds of the block
of 64 bytes from `at` of the cells msg, begun with `init`: round t uses
`SHA256_K(t, ...)` and the `SCHEDULE` word W_t of that block (stage B's
relation, not the array's contents), and ends in
`eight(new a, a, b, c, new e, e, f, g)`, so a round that does not shift is
rejected (`rounds-registers-not-shifted`). `SHA256_BLOCK(msg, at, before,
after)` is a whole block (step 4 included): 64 rounds from the chaining value
`before` and each working variable at the end added to the same word of
`before` (`ADD32`), which is `after`. `sha256_round` is one round with its
proof (the test runs it round by round), `sha256_compress` the block: it
computes the schedule (`schedule_sha256`), reads the chaining value from an
array of 32 bytes (`EIGHT_AT(cells, 0, state)`: `eight_get`, `eight_set`, the
words at 4 * i, proved with stage B's `WORD_AT` and `WORD_SET`), runs the 64
rounds, adds and writes the new chaining value there, and returns
`SHA256_BLOCK` and `EIGHT_AT` of the new value, so a block's result is the
next block's `have` (stage D's fold) and a caller never relates two values
read from an array by hand.

SHA-1 is the same in `SHA1_F` (Ch for t 0 to 19, Parity 20 to 39, Maj 40 to 59,
Parity 60 to 79, one constructor per range, so `f_t` of another range does not
type-check: `sha1-choose-in-the-parity-rounds`), `SHA1_K`, `SHA1_ROUND` (T =
ROTL 5(a) + f_t(b, c, d) + e + K_t + W_t, new c = ROTL 30(b); a left rotation
is ROTR (32 - n), so `ROTR(27, ...)` and `ROTR(2, ...)`:
`sha1-rotation-by-five-right`), `SHA1_ROUNDS`, `SHA1_BLOCK`, `sha1_f`,
`sha1_round`, `sha1_compress` (a chaining value of 20 bytes, `FIVE_AT`).

**Tested, not proved: the round constants.** `SHA256_K` is the standard's table
(the first 32 bits of the fractional parts of the cube roots of the first 64
primes) and `SHA1_K` the four constants (the integer parts of 2 to the 30 times
the square roots of 2, 3, 5 and 10), each stated once in a dataprop whose
constructors the lookups (`sha256_k`, `sha1_k`) return, so the compiler checks
the rounds use the table's word for round t and nothing else, and that
the lookup returns the word the table states. That each word is what the
definition says is not proved: it needs integers of 2 to the 100 (2 to the 61
for SHA-1), and the solver is 32-bit. A proof is owed (sha256 issue, p2: a
relation on 16-bit limbs, `x^3 <= p * 2^96 < (x + 1)^3` for a multi-limb x, or
a bounded integer-root relation); until then they are said to be tested:
`tests/dynamic/rounds` prints every constant and compares them with integer
cube and square roots computed in Python from the definitions
(`make-test.py`), not copied from the standard.

`tests/dynamic/rounds` runs both hashes on "abc", the 448-bit message (two
blocks) and 64 other bytes: each round of the first two (`sha256_round` and
`sha1_round`, constants from the lookups, W_t from the proved schedule) against
the trace of an independent implementation in Python integers (its first rounds
are asserted to be the published traces of FIPS 180-2 B.1 and A.1, and its
digests hashlib's), and the digest `sha256_compress` and `sha1_compress` chain
the blocks into against an independent C-unsigned-arithmetic implementation
written in the test with a constants table of its own. `tests/static` rejects a
round with the constant or the schedule word of another round, a registers
shift that is not the standard's, a round 64, BIG_SIGMA_0 for BIG_SIGMA_1, a
chaining add of another word, and for SHA-1 Ch in a Parity round, the constant
of another range, ROTR 5 for ROTL 5 and SHA-256's schedule in SHA-1's rounds;
`accept/rounds-used` takes a round and a block's proofs.
The padding, the fold over blocks and the digest are stage D, and the
functions that take an array and run them stage E (below).

## The padding, the fold and the digest are proved (bats-lang/sha256#29, stage D)

A message is a sequence of cells (array's `cells`; the cell values are its
bytes), and the proofs about it never name an array. `SNOC(message, value,
message_after)` puts a byte after a message; `HELD(base, cells, n, message)`
says `message` is `base` followed, byte by byte, by the first n cells of
`cells` (`HELD_zero`, `HELD_next` reads cell n with array's `NTH`): it is how
bytes reach a message from the array a piece is given in and from the block
being filled, so a piece's message is its cells and nothing else.
`LIST(message)` (a finite sequence, with a size index for the lemmas' metric)
is what lets a byte be put after a message; `snoc_list` and `held_frame`
(setting a cell the held bytes do not reach leaves them) are the lemmas, each
a private recursive `prfun` with a termination metric and a public wrapper.

**The length is digits.** The solver is 32-bit, so a length is not an integer:
`COUNTED(message, count_top, count_high, count_blocks, fill)` is n = 2^32 *
count_top + 2^16 * count_high + 64 * count_blocks + fill, counted a byte at a
time (`COUNTED_byte`, fill under 64) and a full block at a time (`COUNTED_norm`
by `NORM`: the carry into the next digit). count_top is under 8192, so a message
is under 2^45 bytes and the bit length is under 2^48 (the top two of the
padding's eight length bytes are 0). `BITLEN` is that length times 8 as its
eight bytes, three limbs each of its own small relation (`BITLEN_LOW`, `_MID`,
`_HIGH`: a limb is two bytes and hands a carry under 8 to the next) with
`bitlen_low`, `bitlen_mid`, `bitlen_high` (divisions by 128, 8192 and 256 of a
number under 65536 each) and `bitlen_bytes` composing them.

**The padding** (`PAD(message, ..., padded)`, FIPS 180-4 5.1.1, SHA-256 and
SHA-1 alike) is the message, the byte 128 (`SNOC(message, 128, marked)`),
`zeros` zero bytes (`ZSNOC`) with `ZCOUNT(fill, zeros)` the smallest number
that makes the length a multiple of 64 bytes (fill <= 55: 55 - fill; else 119 -
fill, so a second block), and the eight length bytes (`LENSNOC`), each a
`SNOC`. It is written in place in the block being filled (`pad_short`, or
`pad_long_first` and, once that block is hashed, `pad_long_second`, which
writes the rest into the same array), so no copy has to be followed: each byte
written is a `SNOC` of the message and a `HELD` of the cells set
(`held_frame` and array's `setc_nth_same`).

**The fold and the digest.** `HASHED256(hashed_bytes, chaining)` is the
initial value (`SHA256_IV`, `HASHED256_start`) and then each block: 64 bytes put
after the ones before (`HELD(hashed_bytes, cells, 64, hashed_after)`) and
compressed (stage C's `SHA256_BLOCK(cells, 0, chaining, chaining_after)`).
`DIGEST256(message, chaining)` is `PAD` of the message and `HASHED256` of the
padded message (the very `padded`), so a digest of a message is the hash of
the padded message and of nothing else; `HASHED1` and `DIGEST1` are SHA-1's.
`SHA256_IV` is the standard's table, stated and tested (`tests/dynamic/
initial_value` derives it by integer square roots), not proved against its
definition, as the round constants (sha256 issue 31); SHA-1's five words are
the standard's own.

**The incremental API** (`ctx256(message)`, linear and indexed by the message
fed so far): `init256_proved` (the empty message), `update256_proved(context,
data, len)` (the first len cells of `data` put after the message one byte at a
time into the block being filled, a full block hashed; it returns `Updated256`
with `HELD(message, data_cells, len, message_after)` and the next context, or
`Stopped256` when the message reaches its largest length, about 2^45 bytes,
and only the first i bytes were taken, as HACL*'s streaming API answers a length
over its maximum with an error code) and `finish256_proved(context, out)` (the
padding written in the block, the last block or two hashed, the chaining value
written as 64 lowercase hex digits; it returns `DIGEST256(message, chaining)`
and `EIGHT_HEX(out_cells, chaining)`: `HEXOF` says digit pair i of the output is
the hex of byte i of the 32 bytes that hold the chaining value, `EIGHT_AT`).
The context's invariant is the one the issue states: `HASHED256(hashed_bytes,
chaining)` for the blocks hashed, `HELD(hashed_bytes, block_cells, fill,
message)` for the bytes in the block, so the message is the blocks hashed
followed by the buffer, `COUNTED` for its length (fill the same index), `LIST`
for its shape. `sha256_digest_proved(data, len, out)` and `sha1_digest_proved`
are the one-shot proved versions (`proved_hash` and `sha1_digest` run the
incremental ones, stage E): `HELD(cnil, data_cells, len, message)`,
`DIGEST256(message, chaining)` (`DIGEST1`) and the output's proof. They take
len under 2^16: see the solver note. Larger inputs go through the incremental
API in pieces of any size.

**The solver note (found by mutation, kept as the method).** The 32-bit solver
accepted a false claim in the first version of the one-shot loop, whose context
held `1024 * count_high + count_blocks = j` and `64 * j + fill = i` together
(65536 * count_high once j is gone, times a bound near 2^20). No error showed
and the context was not contradictory at the points probed: the false claim was
`nh := 7` in a recursive call, found only by changing code and checking it was
rejected. So the digit lengths of the one-shot loop are `count_blocks` only
(`64 * count_blocks + fill = i`, `i <= 65535`: coefficients 64 and bounds 2^16)
and `bitlen` is three small relations. The method that found it, which a
change to this stage repeats: a probe (`prfn t (): [1 == 2] void = ()` after
each `val`, which must be rejected) in every function of the stage, and a
mutation of every arithmetic expression (an off-by-one constant, a missing
carry, a wrong bound) which must be rejected; each public lemma and relation
has its false variant in `tests/static/reject`. At the head of the pull request (quire's `mutation_check.py`, the GMP solver, on
`src/lib.bats`): 61 mutants of the lemmas were rejected and 1 accepted, with no
control failed. The accepted one is `_snoc_list` with its `SNOC` value argument
plus one: `_snoc_list` is stated for every `value:int` (`{value:int}`), so the
statement at `value + 1` is the same lemma at another value, true, not a
vacuous proof. None of the probes (after every `val` of the stage) was accepted.

`tests/dynamic/digest` prints SHA-256 of the proved incremental API in pieces
(1, 7, 13, 64, 1000, 4097 bytes) and in one call, and SHA-1 in one call, for
"abc", the empty message, the 448-bit message of FIPS 180-2 B.2 and lengths
55, 56, 63, 64, 65, 119, 120, 128, 1000 and 10000 (the edges of one and of
two padding blocks, and many blocks), against `hashlib` (`make-expected.py`,
which asserts the published digests first); valgrind finds no leak.
`tests/dynamic/bitlen` prints the eight length bytes at the corners of every
digit against Python integers. `tests/static` rejects (54 fixtures) a byte
other than the cell's put after a message, a frame over a held cell, a block
not full or not 64 bytes hashed, a count carried at the wrong place or past
the top, a length limb without its carry, a padding that starts with a zero,
has a zero too few or too many, or is for the wrong message, a block hashed
from other cells or onto another chaining value or at an offset, an initial
value with a word changed, a digest of the unpadded message, SHA-1's taken
for SHA-256's, a digest or hex digits of another message or chaining value,
an update of more cells than the array holds, an update's result not matched
completely, a context used twice, a one-shot over 2^16 bytes, and the three
bound lemmas stated one too small; it accepts the API as a caller reads it
(two pieces make one message, the one-shots), the length corners, and the
count and zero-count constructors.

## The proved SHA-256 and SHA-1 beside the fast SHA-256 (bats-lang/sha256#29, stage E; #34)

Two SHA-256 implementations are in the package, and which one a caller gets is
its choice by name:

* **`hash`, `init`, `update`, `finish`** (and `ctx`): the fast code,
  unproved, 32-bit words as C `unsigned`, unchanged by #29 (same types; its
  block function was rewritten for speed in #40, below). It is what dependents use and what quire hashes whole EPUBs with (a
  book's id is the SHA-256 of its file, megabytes): about 170 MB/s in a release
  build. Tested, not proved (`tests/dynamic/vectors`, `sizes`, `proved`).
* **`proved_hash`, `proved_init`, `proved_update`, `proved_finish`** (and
  `proved_ctx`): the same types, running the proved code (stages A to D) through
  `init256_proved`, `update256_proved`, `finish256_proved`. About 7.5 times slower
  than `hash` (452 instructions a byte before sha256#53, 394 after; `hash` 52),
  so nothing switches to it until it is fast enough (#34). A message
  that reaches its largest length (about 2^45 bytes) takes no more bytes.
* **`sha1_digest`**: the proved SHA-1 (`init1_proved`, `update1_proved`,
  `finish1_proved` over the same `HELD`, `COUNTED` and padding proofs). SHA-1 had
  only an unproved version, never published (it was added to main for quire#562
  and is replaced here, same type), and its inputs are tiny (the font key of
  EPUB's IDPF obfuscation: an identifier), so the proved one costs nothing that
  matters (about 110 ms a MiB in release). Quire calls it for the font key.

The decision (written on #34): correctness before speed, so the proved code is
exposed as new API and the existing SHA-256 API keeps running the existing code.
The measurement that led to it (callgrind, release, 1 MiB: rotations 36% of 1.48G
instructions against 114M for the fast code, `sha256_round` 15%, the schedule
11%, `add32` 9%) is on #34; `rotr_fast` is used here (O(1) rotations proved
against `ROTR`; the single-bit `rotr` takes 31 steps).

* **How an array reaches the proved code.** A caller's array is array's `arr` (or
  `borrow`), whose cells the types know nothing of, and the proved functions
  read a `barr`, whose cells they know. So a call copies its bytes, 4096 at a
  time, into a `barr` of the package's own (`_copy_arr`, `_copy_borrow`), feeds
  them to `update256_proved` (`update1_proved`), and after `finish256_proved`
  (`finish1_proved`) copies the digits or the 20 bytes into the caller's array
  (`_copy_out`). That glue is not proved: it is tested (`tests/dynamic/sizes`,
  `sha1`, `proved`). Everything between (padding, blocks, schedule, rounds,
  chaining value, hex digits) is the code `DIGEST256` and `DIGEST1` describe. An
  array-package function giving a `barr` view of a borrowed `arr` would remove the
  copy (and the glue): not made, the copy costs a byte-wise loop against 64 rounds
  a block.
* **Sizes.** `proved_update` and `sha1_digest` feed the proved incremental API in
  pieces of any total size: a message is not limited to the 2^16 bytes the
  one-shot `sha256_digest_proved` and `sha1_digest_proved` take (those stay,
  proved, and the array functions do not use them: one code path).
* **Measured** (release build, 1 MiB, 4 cores, `/tmp/bench`-style loop of 40 and 10
  hashes; the main branch's `hash` and this branch's `hash` measured the same way):
  `hash` 5.9 ms (about 175 MB/s) on main and 5.9 to 6.9 ms here (nothing slowed);
  `proved_hash` 211 to 239 ms (4.4 to 5.0 MB/s); `sha1_digest` 108 to 138 ms
  (7.6 to 9.7 MB/s). In a debug build `hash` took 296 ms and `proved_hash` 2790 ms.
  `tests/dynamic/perf` fails a debug build over 1.5 s for `hash` (so `hash` running
  the proved code by mistake fails it), over 6 s for `proved_hash` and over 3 s for
  `sha1_digest` (the single-bit rotations would take 9.4 and 4.8 s).

**What is proved, tested and trusted.** Proved (by the compiler, no `praxi`, no
`assume`, no `$UNSAFE`): the word functions, the schedules, the rounds and the
chaining add, the padding and the length, the fold over the blocks, the digest
and its hex digits, the incremental contexts of both hashes, each against the
FIPS 180-4 definitions, in terms of arith's relations on 16-bit halves. Tested
only: the round constants and the initial values (`SHA256_K`, `SHA1_K`,
`SHA256_IV`, `SHA1_IV` are the standard's tables stated once; that each word is
what the definition says needs integers of 2^100 and the solver is 32-bit: issue
#31), the copy glue above, and the fast `hash`/`init`/`update`/`finish` (not
proved at all). Trusted, where it lives: array's `barr` primitives (`barr_get`,
`barr_set`, ...: array's CLAUDE.md), arith's C operators and the equivalence of its
halves-based functions to 32-bit arithmetic wherever arith states it (`and_proved`,
the shifts: arith's tests).

`tests/dynamic/proved` is the check that the two are the same function: the
proved and the fast SHA-256 of every prefix length 0 to 200 of a pattern, of 40
pseudo-random lengths (201 to 4999) of pseudo-random bytes, of the NIST vectors
("abc", the 448-bit and 896-bit messages, one million "a") and of 1 MiB of a
pattern and of pseudo-random bytes, each digest compared with `hashlib`'s
(`make-expected.py`, which asserts the published NIST digests first) and the
fast and the proved compared with each other in the test (the count of
differences is in `expected`, 0); and the SHA-1 of lengths 0 (through the
incremental proved SHA-1) to 200 and the same vectors. It does not run under
valgrind (the proved code under it takes a quarter of an hour for the 3 MiB);
`sizes` and `digest` do, and cover the leaks of the glue. `tests/dynamic/sizes`
hashes 4095, 4096, 4097, 8191, 8192, 8193, 65535, 65536 and 65537 bytes with
`hash`, `proved_hash` and `sha1_digest`, and an `update` and a `proved_update` of a
prefix (0, 4100 of 5000, all) against `hashlib` (the edges of the 4096-byte piece
and of the one-shot limit); `vectors` is the fast code's; `sha1` and the stage D
tests run unchanged. A test may name its valgrind limit in seconds in a `timeout`
file (`tests/dynamic/run.sh`; `sizes` 900).

`tests/static` rejects (stage E) a context finished twice or dropped, an update or
a SHA-1 digest of more bytes than the array holds, a hash of no bytes, a finish
into 20 bytes, a SHA-1 into 64, a SHA-256 context given to the SHA-1 update, a
SHA-1 digest of another message or claimed as SHA-256's, a SHA-1 context used twice,
a SHA-1 update's result not matched completely, more cells than the array holds,
and a Stopped1 claimed to hold all the bytes, each for the fast API
(`public-*`) and the proved one (`proved-*`); it accepts both as a caller reads
them and the SHA-1 incremental API. The reject fixtures are exact (quire#585,
as arith's and array's): `expect` names the function, the line and patsopt's
error, and `tests/static/expect.py` fails a fixture rejected for another reason
(`expect_test.py` tests it). Stage E adds no lemma.

Issue #29's "done when" (the digest's own code is the proved code) is met by the
proved API; the fast API keeps the unproved code until the proved one is fast
enough (#34), and the round constants are #31.

## The fast SHA-256 is written for a build without optimisation (bats-lang/sha256#40)

bats hashes with `init`, `update` and `finish`, the fast unproved code, and
in an unchanged `bats check` hashing each module's C was 35% of the time. Its
bootstrap compiler is a debug build (`-O0`), where every `uint` operation is a
call (`atspre_g0uint_lxor_uint`, ...), so the cost is the number of operations
and calls, not the instructions of the algorithm. What the profile
(callgrind, `tests/bench`) found in the code of #29: a chain of up to nine
tests for each round constant (`_k`), a call and a subtraction for each
rotation (`_rotr` with a variable amount, three of them in each sigma), the
rounds and the schedule read and written through an array (about seven calls
for each `get`), an eight-word tuple through each round, the 64 rounds and
the two schedule loops as loops, and the data copied a byte at a time into
the block buffer before it was hashed, even when a whole block was there.

What it is now (all in `src/lib.bats`, types and `#pub` unchanged):

* **The 64 rounds are written one after another** (`_compress`, generated by
  `scripts/gen-fast-compress.py`, between the two `generated` marker lines;
  `--check` fails when the region is not what the script writes). The round
  constants are literals, the message schedule is 64 named words
  (`w0` ... `w63`, no array, so the context's schedule array is not used and
  stays only because the public `ctx` has it), and the eight working variables
  are not moved: a round gives the new e and the new a and the next round
  names its arguments in the new order. `_round` and `_schedule` write each
  sigma out with its rotations by their amounts, Ch as `g xor (e and (f xor
  g))` and Maj as `(a and b) or (c and (a or b))` (the same functions with one
  operation fewer each). A rotation is `(x >> n) lor (x << (32 - n))`, in the
  form GCC and clang turn into a rotate: the first version of this wrote the
  six shifts of a sigma as one `lxor` chain and GCC did not find the rotates
  (80.7 instructions a byte; with the rotations in parentheses, 62.2).
* **`_fill` hashes a whole block where it lies** when the buffer is empty
  and 64 bytes remain, without the byte-wise copy; a partly filled buffer is
  filled byte by byte as before, so the digest of any split of the input
  is the same.
* **Only operations the wasm prelude has.** quire hashes books in wasm, where
  bats' prelude defines a fixed list of `atspre_` functions (bats' CLAUDE.md,
  "The wasm prelude"). A byte is read with `byte2int0` and
  `g0int2uint_int_uint` (the first version used `byte2uint0`, which the wasm
  prelude lacks), no `ullint`, and the set of `atspre_` names in the C of
  this module is a subset of the set before this change.

Not proved, as before: the fast code has no proof. What ties it to the proved
code is `tests/dynamic/proved` (the fast and the proved SHA-256 of every
prefix 0 to 200, 40 random lengths, the NIST vectors and 1 MiB, the count of
differences in `expected`), `vectors`, `sizes` and `digest` (valgrind). The
proved code (`proved_hash`, `sha1_digest`, stages A to E) is untouched, so what
it proves, `DIGEST256(message, chaining)` against FIPS 180-4, is the same
statement; the constants in the fast code's rounds are the same as `SHA256_K`
and are not related to it by the compiler, only by those tests.

**Measured** (`tests/bench/run.sh <repository> [debug|release]`, native, 1 MiB
hashed 20 times, the least of 5 runs; instructions a byte from callgrind as
the difference of a 3 MiB and a 1 MiB run, so the buffer fill is not
counted; one machine of 4 cores, shared, GCC 13.3 at `-O2` and `-O0` as
bats builds a release and a debug binary):

| build | before | after | factor |
|---|---|---|---|
| release, instructions a byte | 93.0 | 52.4 | 1.77 |
| release, ms a MiB | 6.12 | 4.65 | 1.32 |
| debug, instructions a byte | 2286.9 | 842.2 | 2.72 |
| debug, ms a MiB | 355.6 | 143.4 | 2.48 |

The digest of the benchmark's data is the same before and after (and the
incremental API in pieces of 4096 bytes gives the same numbers as `hash`).
What is left in a debug build is the call of each `uint` operation (about
3,000 a block, some 17 instructions each, 65% of the time): that is the
build's, not this code's (compiling the dependencies of a debug build with
`-O1`, or the operations as `always_inline`, is bats').

**The proved SHA-256 was not made faster by this** (`proved_hash`: about 7.5
times slower than the fast code, #34). It is not what bats and quire call. The
`_w32` words (sha256#52) and the `barr_get_be32` read (sha256#53) took it from
452 to 394 instructions a byte (callgrind, release, 1 MiB; the fast `hash`
about 52): the rest is the proof's own work, and the way to its speed is
#34's last comment, not these changes.


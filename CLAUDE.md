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

**The round constants are proved against their definitions: SHA-256's against
the cube roots (sha256#31, piece #75), SHA-1's against the square roots (piece
#76).** `SHA256_K` is
the standard's table (the first 32 bits of the fractional parts of the cube
roots of the first 64 primes) and `SHA1_K` the four constants (the integer
parts of 2 to the 30 times the square roots of 2, 3, 5 and 10), each stated
once in a dataprop whose constructors the lookups (`sha256_k`, `sha1_k`)
return, so the compiler checks the rounds use the table's word for round t and
nothing else, and that the lookup returns the word the table states.

Each constructor `SHA256_K_t(t, high, low)` carries the definition as its
guard: `cube_fraction_le(i, high, low, p)` and `cube_fraction_gt(i, high, low,
p)` say that x = i * 2^32 + 65536 * high + low has `x^3 <= p * 2^96 < (x +
1)^3`, with p the literal prime and i the integer part of its root, so
`SHA256_K_t` at a word that is not floor(cbrt(p) * 2^32) mod 2^32 does not
type-check. No limb arithmetic is needed: the gmp build of the solver
(infinite precision; arith's CLAUDE.md, "The proofs are checked by the
infinite-precision solver") takes the integers of 2^105 as literals and
multiplies them. The int build would not be a check at all (#594). No type of
a published constructor or function changes (each guard holds at its
constructor's own indices, and `sha256_k`, `sha256_k_w32` stay and are called
by the rounds and the digests), so this is not a breaking change.
Research: HACL* (`specs/Spec.SHA2.Constants.fst`) states `k224_256` as a
literal list of 64 words, checked only for its length; Appel's VST
(`sha/SHA256.v`) states `K256` as 64 hard-coded constants with the comment
"hardcoding the constants, first 32 bits of the fractional parts of the cube
roots of the first 64 prime numbers". Neither proves the table against the
definition; this does.
`tests/static/accept/sha256-k-used` builds all 64 constructors at the word the
definition gives. `tests/static/reject/sha256-k-<t>-one-over` and
`sha256-k-<t>-one-under` (t = 0 to 63: 128 fixtures) claim word t one bit too
high (`cube_fraction_le` fails) and one too low (`cube_fraction_gt` fails),
each with an exact `expect` (function `claim`, line 7, the unsolved
constraint with the prime, the integer part and the halves claimed), so a
guard of any word weakened in either clause is caught. patsopt reports one
unsolved constraint for a function, so a fixture holds one word and one
direction. All 129 fixtures are written by
`tests/static/make-sha256-k-fixtures.py` from the definition alone (the first
64 primes and integer cube roots of p * 2^96, no table copied), and
`tests/static/run.sh` runs its `--check`, which fails when a committed fixture
differs from what the generator writes or one is missing or extra. Python is
the avenue: the package's tests already generate theirs with it
(`make-expected.py`, `scripts/gen-fast-compress.py`). The guards also state
`high < 65536` and `low < 65536`, so the statement is for halves in range and
a word out of range does not type-check either. That p is the (t+1)-th prime is
proved beside it, in the section "The primes are the first 64 and the first 8"
below (sha256#78).

**SHA1_K (piece #76).** Each constructor `SHA1_K_0_to_19`, `_20_to_39`,
`_40_to_59` and `_60_to_79` is `{t,high,low:nat | <its range of t>; high <
65536; low < 65536; sqrt_fraction_le(high, low, n); sqrt_fraction_gt(high,
low, n)}` with n the literal 2, 3, 5 and 10: `sqrt_fraction_le` and
`sqrt_fraction_gt` say that x = 65536 * high + low has `x^2 <= n * 2^60 < (x +
1)^2`, that is x = floor(sqrt(n) * 2^30), the definition of FIPS 180-4, section
4.2.1 (integers of 2^64, held by the gmp solver as above). The word is free in
the constructor's type, as SHA256_K's is, so `SHA1_K(t, high, low)` at a word
that is not the definition's does not type-check. The type of `sha1_k` and
`sha1_k_w32` is unchanged in shape:
both lookups still return `SHA1_K(t, high, low)` for halves under 65536, and
`sha1_k` stays, deprecated, and `tests/dynamic/rounds` still calls it.
`tests/static/accept/sha1-k-used` builds the four constructors at the
definition's word, and `tests/static/reject/sha1-k-<range>-one-over` and
`-one-under` (ranges `0-to-19`, `20-to-39`, `40-to-59`, `60-to-79`: 8
fixtures, all committed) claim a word one bit too high (`sqrt_fraction_le`
fails) and one too low (`sqrt_fraction_gt` fails), each with an exact `expect`.
The same generator, `tests/static/make-sha256-k-fixtures.py`, writes them from
the definition alone (`floor(sqrt(n) * 2^30)` as an integer square root of n *
2^60, no copied table), so its `--check` in `tests/static/run.sh` covers the
138 fixtures of both (sha256#77 adds the 16 of `SHA256_IV`, above). The design is #75's, whose research (HACL* and VST state
their tables as literals, none proves them against the definition) applies
unchanged. Not proved: nothing of SHA1_K remains owed.
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
`SHA256_IV` is proved against its definition (FIPS 180-4, section 5.3.3, sha256#31
piece #77), as the round constants are (above): the constructor `SHA256_IV_mk` is
`{h0_high,h0_low,...,h7_high,h7_low:nat | every half < 65536; sqrt_fraction32_le(i,
h_high, h_low, p); sqrt_fraction32_gt(i, h_high, h_low, p) for each word}` with p the
literal prime (2, 3, 5, 7, 11, 13, 17, 19) and i the literal integer part of its
square root (1, 1, 2, 2, 3, 3, 4, 4), and the type `SHA256_IV(eight(w32(h0_high,
h0_low), ...))`. `sqrt_fraction32_le` and `sqrt_fraction32_gt` say that x = i * 2^32
+ 65536 * high + low has `x^2 <= p * 2^64 < (x + 1)^2`, that is x = floor(sqrt(p) *
2^32), so the word is the first 32 bits of the fractional part (integers of 2^67,
held by the gmp solver as for SHA256_K; the int build would not be a check, #594).
The word is free in the constructor's type, so `SHA256_IV` at a word that is not the
definition's does not type-check. No published type changes: `sha256_iv_w32` and
the deprecated `sha256_iv` keep their types and each is called (`tests/dynamic/
initial_value`, `initial_value_w32`), because each guard holds at the constructor's
own indices; this is not a breaking change. `tests/static/accept/sha256-iv-used`
builds the constructor at the eight words the definition gives, and
`tests/static/reject/sha256-iv-<j>-one-over` and `-one-under` (j = 0 to 7: 16
fixtures) claim word j one bit too high (`sqrt_fraction32_le` fails) and one too low
(`sqrt_fraction32_gt` fails), each with an exact `expect`;
`tests/static/make-sha256-k-fixtures.py` writes them from the definition alone (the
first eight primes and integer square roots of p * 2^64, no table copied) and its
`--check` covers them with the K fixtures. `reject/iv-of-another-word` (word 0 low
half 0xe668) is the hand-written case. That p is the (j+1)-th prime is proved
beside it, in the section "The primes are the first 64 and the first 8" below
(sha256#78). SHA-1's five words are the standard's own, constants with no
definition to prove.

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
  `init256_proved`, `update256_proved`, `finish256_proved`. Before sha256#59 about 7.5
  times slower than `hash` (393.9 instructions a byte against 52.4, 38.71 ms a MiB
  against 3.29, `tests/bench`, release, the raw output is on PR #60); since it
  94.0 against 52.4 (1.79 times) and 5.89 ms against 3.39 (section "within 2x", below).
  Nothing switches to it until it is fast enough (#34). A message
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
* **Measured** (release build, 1 MiB; `hash` and `proved_hash` by `tests/bench`, least
  of 5 runs of 20 hashes, figures in the section "within 2x" below: `hash` 3.29 ms
  a MiB, `proved_hash` 38.71 ms before sha256#59 and 5.89 ms after; `sha1_digest` and
  the debug figures from an earlier `/tmp/bench`-style loop of 40 and 10 hashes on
  another machine state, not measured again): `sha1_digest` 108 to 138 ms
  (7.6 to 9.7 MB/s). In a debug build `hash` took 296 ms and `proved_hash` 2790 ms.
  `tests/dynamic/perf` decides by instruction counts, not time (below, sha256#65).

**What is proved, tested and trusted.** Proved (by the compiler, no `praxi`, no
`assume`, no `$UNSAFE`): the word functions, the schedules, the rounds and the
chaining add, the padding and the length, the fold over the blocks, the digest
and its hex digits, the incremental contexts of both hashes, each against the
FIPS 180-4 definitions, in terms of arith's relations on 16-bit halves. Tested
only: the initial value of SHA-1 (`SHA1_IV` is the standard's table stated
once; `SHA256_K`, `SHA1_K` and `SHA256_IV` are proved against their definitions, sha256#75,
#76 and #77, and their primes by #78; nothing of sha256#31 remains owed), the copy glue above, and the fast `hash`/`init`/`update`/`finish` (not
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
times slower than the fast code then, #34; sha256#59, below, made it 1.79 times).
It is not what bats and quire call. The
`_w32` words (sha256#52) and the `barr_get_be32` read (sha256#53) took it from
452 to 394 instructions a byte (callgrind, release, 1 MiB; the fast `hash`
about 52): the rest is the proof's own work, and the way to its speed is
#34's last comment, not these changes.

## The proved SHA-256 within 2x of the fast one (bats-lang/sha256#59)

**Measured.** `tests/bench/run.sh <repository> release` (native, 1 MiB; the time is
the least of 5 runs of 20 hashes, the instructions a byte are callgrind's
(3 MiB - 1 MiB) / 2 MiB), run on main (c09d33c) and on this branch with the same
compiler (bats dbb8914 release, from its bootstrap/c), the same GMP ATS2, the same
scratch copy of the pinned repository (d256b6e) and one machine state, one after the
other. The raw output of both runs is in the comment on PR #60 that names the head
that was measured. This is the one place the figures are stated:

| | instructions a byte | ms a MiB |
|---|---|---|
| `proved_hash`, main (before) | 393.9 | 38.71 |
| `proved_hash`, this branch (after) | **94.0** | **5.89** |
| `hash` (main) / `hash` (this branch) | 52.4 / 52.4 | 3.29 / 3.39 |
| incremental API (main) / (this branch) | 52.4 / 52.4 | 3.26 / 3.42 |

The proved code is 7.5 times `hash` in instructions before and **1.79** after (94.0 /
52.4), 11.8 times in time before and 1.74 after (5.89 / 3.39): within the 2x of the
ticket. The digest of the bench is `8816f31b...` in all four runs of `hash` and `proved`
(the incremental API's is `99c35f42...` in both). The earlier sections' figures for `proved_hash` (7.5 times, 452 and
394 instructions a byte, 211 to 239 ms) are the code before this change, and the 211
to 239 ms are replaced by the 38.71 ms above (same code, measured by `tests/bench`).

What it was: the proved code's words were one `uint` already (the `word32` of
sha256#52), and its cost was calls.
Each `#pub fun` of arith and array is an external symbol compiled alone at `-O2`,
so `barr_get_be32`, `barr_set`, `word32_pack`, `word32_rotr` and `word32_byte`
(175.8 of 394.0 instructions a byte, #55's profile) were calls. What is done:

1. **The five as templates.** arith's `word32_rotr_inline`, `word32_pack_inline`,
   `word32_byte_inline` and array's `barr_get_inline`, `barr_get_be32_inline`,
   `barr_set_inline` are `#pub fun{}` templates with the types and bodies of the
   old names: a dependent instantiates them in its own translation unit (it loads
   the package's `lib.dats`), so the C compiler inlines them. This package calls
   them everywhere (the old names are not called here any more; they stay in
   arith and array). Nothing new is trusted (arith's and array's CLAUDE.md), no
   `$UNSAFE` is added here, the package is `unsafe = false`.
2. **The round constants as a chain of equalities** (`sha256_k_w32`). It was a
   binary search of six comparisons for each round (about 15 instructions a byte, a
   call that was not inlined, from the profile of the earlier work on this change);
   `if t = 0 ... else if t = 1 ...` with `$AR.eq_g1` is the same function with
   the same proof of `SHA256_K(t, ...)` in each leaf, and about 6 instructions a byte.
   The last leaf (t = 63) is proved by the solver from the signature's `0 <= t` and
   `t < 64` and the 63 disequalities `t != 0` to `t != 62` that the 63 false
   branches of the chain give.

The steps' own figures (277.5 after arith's templates, 113.0 after array's, 103.0 with
`word32_pack_inline` in the constants) and the by-function profile below (58, 28)
are from the earlier work on this change; only the before and after are in the posted
raw output.

What is left (94.0): `sha256_compress` 58 a byte (the rounds, the sigmas, the
reads of the schedule words), `schedule_sha256` 28 (the 48 expanded words, about
37 instructions each: the word written by the previous step is read back from the
array byte by byte, which the C compiler does not forward), and the bench's own
fill. Reaching the fast code's 52 needs the schedule out of the array (the
proofs follow the array's cells, `SCHEDULE_ARRAY`) or unrolled rounds; not done.

**Override exposure (the review of PR #60; arith's and array's CLAUDE.md, same
section name).** Before this change the six functions were external symbols, and a
second definition of one was a link error. A template body is compiled into each
translation unit that instantiates it, so a package in this package's dependency
graph that implements the same template (`implement{} $AR.word32_rotr_inline ...`,
which needs an unsafe package, since it casts) replaces the body at this package's
call sites, silently, and sha256 (`unsafe = false`) would run it: the proved code's
six template call sites (`word32_rotr_inline`, `word32_pack_inline`,
`word32_byte_inline`, `barr_get_inline`, `barr_get_be32_inline`, `barr_set_inline`)
are exposed, though the types still hold (the replacement has the same type, and
the proofs are about the type). Nothing in this package's build detects it today.
The tracker is bats-lang/bats#421 (open): reject an `implement` of a template or
function that another package declares. Until it lands the exposure is
the one arith's and array's CLAUDE.md state for their templates; this package adds no override and its lock names only arith and
array.

Proved, tested, trusted: unchanged. Every proof is the same term (the
templates have the types of the functions they replace), checked by the gmp
solver; `tests/dynamic` (15 tests, `proved` and `sizes` included) and
`tests/static` (105 fixtures) pass.

## The primes are the first 64 and the first 8 (bats-lang/sha256#78; keyword: nth-prime)

The guards of `SHA256_K` and `SHA256_IV` name p as a literal. `NTH_PRIME(t, p)` says p is the
(t+1)-th prime, t from 0, as a relation made of witnesses and nothing else:

* `PRIME(p)`: `PRIME_mk{r}` over `NO_DIVISOR(p, 2, r)` with `2 <= p` and `r*r <= p < (r+1)*(r+1)`,
  r the integer root. `NO_DIVISOR(n, d, r)` is built by `NO_DIVISOR_none` (d > r) and
  `NO_DIVISOR_step{q, m}` (n = d*q + m with `0 < m < d`, then the same for d + 1): a division with a
  remainder that is not 0 for each e from 2 to the root, so a composite has no `PRIME` (the divisor
  up to its root, by the usual argument, is where its remainder would have to be 0).
* `COMPOSITE(n)`: `COMPOSITE_mk{d, q}`, n = d*q with d and q at least 2 (a factorisation).
* `NONPRIMES(a, b)`: every number from a + 1 to b - 1 is `COMPOSITE` (`NONPRIMES_none` when b <= a + 1,
  `NONPRIMES_next` for a + 1 < b), so the next prime cannot skip one.
* `NTH_PRIME_first` is `PRIME(2)` at (0, 2); `NTH_PRIME_next` takes `NTH_PRIME(t, p)`, `NONPRIMES(p, q)` with
  `p < q` and `PRIME(q)` to `NTH_PRIME(t + 1, q)`.

The witnesses are given at each use (the gmp solver evaluates the products of literals), and are written
by `scripts/gen-primes.py` between the two `generated` marker lines of `src/lib.bats`: 64 private proofs
`_nth_prime_<t>`, each from the one before it, from the definition (trial division, integer roots); the
compiler checks every witness, so a wrong one is a type error and the generator is not trusted. `--check`
(run by `tests/static/run.sh`) fails when the region is not what it writes. Python is the avenue: the
package's tests and its `gen-fast-compress.py` already generate theirs with it, and the bats test tooling
has no generator to build on. A relation is a specification, so there is nothing to run for it; no
`praxi`, no `assume`, no `$UNSAFE`, no runtime check.

**How the primes reach the constants.** `SHA256_K_PRIMED(t, p, high, low)` is `SHA256_K` again, constructor for
constructor (`SHA256_K_PRIMED_<t>`), with the same guard (the prime p and the integer part of its cube root as
literals) and, as an argument, the proof `NTH_PRIME(t, p)` of that very p, which is an index of the new proof; so
one proof carries both facts, that the word is floor(cbrt(p) * 2^32) mod 2^32 and that p is the (t+1)-th prime.
`SHA256_IV_PRIMED` is the same for `SHA256_IV_mk`, holding `NTH_PRIME(0, 2)` to `NTH_PRIME(7, 19)`. The two are
written by `scripts/gen-primes.py` from the old constructors of `src/lib.bats`, and its `--check` fails when an old
constructor is not the definition's (so the guard copied is the table's). `sha256_k_nth_w32(t)` and
`sha256_iv_nth_w32()` are beside `sha256_k_w32` and `sha256_iv_w32` (additive: no published type or constructor
changed, so nothing is deprecated and no removal ticket is filed; `tests/dynamic/nth_prime` calls both): they
return the proof of the table and the primed proof at the same indices, with the word.

Routes tried for the tie between the published `SHA256_K_t` and the new proof, recorded: (1) a lemma over every
`SHA256_K` proof giving `SHA256_K_PRIMED`: `case+ k of SHA256_K_0() => ...` leaves `cube_fraction_le(1, high, low,
2)` unsolved, since the guard is a cube of the constructor's variables and the solver proves a cube only of
literals (a linear guard such as `high < 65536` does carry); naming the constructor's variables in the pattern
(`SHA256_K_0{h,l}()`) makes the pattern itself demand the guard. (2) A lemma that a cube-root word determines its
prime (`cube_fraction_le/gt` at one `i,h,l` for `p1` and `p2` gives `p1 == p2`, with `i <= 6`): the solver leaves
`p1 == p2` unsolved (non-linear), so it is not provable here. (3) The family above, which is the route taken: the
primed proof is the table, not derived from the old proof.

**Rejected** (`tests/static/reject`, each with its exact `expect`; `accept/nth-prime-used` is the control):
a composite given a `PRIME` by a remainder of 0 (`nth-prime-composite-is-prime`), by a remainder not below the
divisor (`nth-prime-remainder-not-below-divisor`), by a witness that is not a division
(`nth-prime-composite-wrong-witness`) and by a root too small to reach its divisor
(`nth-prime-composite-root-too-small`); 1 as a prime (`nth-prime-one-is-prime`); a prime that skips one, with no
factorisation for it (`nth-prime-skips-a-prime`), with a wrong product (`nth-prime-skips-a-prime-wrong-product`) and
with no numbers listed (`nth-prime-gap-without-factorisations`); a prime repeated (`nth-prime-repeats-a-prime`);
the first prime as 3 (`nth-prime-first-is-three`); a factor of 1 (`nth-prime-composite-by-one`); a composite
listed past the end (`nth-prime-nonprimes-past-the-end`); and a constant or an initial word given another
prime or another round (`k-primed-other-prime`, `k-primed-wrong-round`, `iv-primed-other-prime`).

**Mutation check** (the method of gestures' and array's CLAUDE.md, quire's `mutation_check.py`, the gmp solver as
`--ats-home`): the `prfn`s of the section, `_nth_prime_<t>`, are the statements it mutates (the index t plus one, the
prime plus one), and the compiler must reject each; the run, its sample and its seed are in the pull request.
The relations' own guards are the constructors', checked by the reject fixtures above, one for each guard.

## The perf test counts instructions (bats-lang/sha256#65)

`tests/dynamic/perf` read the clock around three hashes and failed over fixed
times (1.5, 6 and 3 s), which a loaded runner can exceed with correct code: a
red that says nothing about the code, and a retry is no fix. What it guards is
not a time: `hash` must not run the proved code, and the proved code must not
rotate a bit at a time (a million operations a block). Both are how many
instructions run, which `valgrind --tool=callgrind` counts exactly and load
does not change. So the test runs itself three times under callgrind (one hash
of 1 MiB each, `popen`, the child chosen by its argument), reads the line
`Collected : N` of valgrind's summary, and compares N in millions with a
budget. It reads no clock, runs each hash once, and fails when valgrind gives
no count. Its C (a few lines in an `unsafe = true` test, as before) is
`popen` and `atoll`: the process package would need an argument array and
a pipe for the same, and the budgets themselves are in Bats.

**Counted** (debug build, as `run.sh` builds it, GMP ATS2, the whole child
including the 1 MiB fill and the allocations, so about 200 million are not the
hash): `hash` 1097 million, `proved_hash` 6325 million, `sha1_digest` 6133
million.

**Budgets, and why each number:**

* `hash`: 2000 million. 1.8 times what it takes, so a small change to the
  fast code does not fail it, and 3.2 times below what `proved_hash` takes, so
  `hash` running the proved code (6325) fails it. The fast code is some 840
  instructions a byte in a debug build (above), 880 million for 1 MiB.
* `proved_hash` and `sha1_digest`: 9000 million each. 1.4 times what they take
  (6325, 6133), and well under what the single-bit `rotr` costs. Measured
  (review of #66): in a scratch copy of arith, `word32_rotr_inline` split the
  word into halves, called arith's single-bit `rotr` (n steps of one bit, the
  specification) and packed the result back; published into a scratch package
  repository with this sha256 and the unchanged test, built as `run.sh` builds
  it (debug, native), the counts were `hash` 1097 million (unchanged),
  `proved_hash` 40747 million (6.4 times its count) and `sha1_digest` 24569
  million (4.0 times), and the test printed `over budget` and exited 1. Both
  9000 budgets catch it (40747 and 24569 are over 9000).

A count is the same on every run of the same binary, so there is no margin for
load; the margins are for the code and for the valgrind and libc versions. A
change that moves a count past its budget moves the budget in the same pull
request, with its reason here. The test names `timeout` 900 for `run.sh`
(valgrind runs the hashes much slower than the machine); that limit is a hang
guard of `run.sh`, not a budget.

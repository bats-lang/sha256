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
`small_sigma_1` take and give a word as its two 16-bit halves (arith's
`rotr`, `shr`, `add32`, `xor32`, `and32`; the solver is 32-bit, so no
proof names 2 to the 32) and return the proof of the relation `CH`, `MAJ`,
`BIG_SIGMA_0`, ... that is the standard's definition (FIPS 180-4, section
4.1.2) composed from arith's bit specifications. `tests/dynamic/word_functions`
runs them on the published trace of SHA-256 over "abc". The digest
functions (`hash`, `update`, `finish`, `sha1_digest`) are still written
and tested, not proved: the schedule, the rounds, the padding and the
digest are stages B to D of the plan in the issue.

## Words in an array and the message schedules are proved (bats-lang/sha256#29, stage B)

`WORD_AT(cells, at, high, low)` says the four cells of an array's contents
(array's `barr`, whose cells are in its type) from `at` are the word
high:low, big endian; `WORD_SET(cells, at, high, low, cells2)` says four
cells were set to it. A word needs no array of its own and no change to the
array package: `word_get` and `word_set` are four `barr_get`s and
`barr_set`s, and `word_set_at`, `word_set_other` (a word that shares no cell
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
about the halves-based functions (single-bit rotations, arith); the digest
does not run them yet (stage E of the plan, which needs the fast rotations
first), so `hash` and `sha1_digest` still compute their schedules with `uint`
and are tested, not proved.

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
Digest functions are still the old unproved ones (stage E switches them to the
halves), and padding and the fold over blocks are stage D.

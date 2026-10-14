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

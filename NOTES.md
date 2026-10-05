# Notes: proving Lighthouse epoch processing, and a Python-to-Lean path for the spec

Raw material for a blog post. In order of events. Dates are 2026-10-02 to 2026-10-04.

## Part 1: Lighthouse epoch processing, proved against the spec

### The goal

Prove that Lighthouse's epoch processing (`single_pass.rs`) gives the same result as the
consensus spec. Target fork: Gloas.

Prior art: `sigp/verified-consensus` proved things about an Isabelle model of the spec. It never
touched the Rust. We wanted the Rust.

### Tools

- Aeneas (with Charon) turns Rust into Lean.
- The spec side is a hand-written Lean transcription of the pyspec functions.
- Proofs are in Lean 4. Each PR runs an axiom audit: only `propext`, `Classical.choice` and
  `Quot.sound` are allowed.

Why Lean for the spec, not a Rust reference: Lighthouse passes the EF vectors, so a proof that
Lighthouse equals the Lean spec also says the Lean spec passes them. And Lean reads close to
pyspec.

### Getting Aeneas to accept the code

Aeneas does not take production Rust as is. What broke it:

- `?` inside a loop (early return) and iterator chains.
- `milhouse` trees with `Arc::make_mut`, `HashMap`, `BTreeSet`, and the `superstruct` `BeaconState`.
- Types like `Epoch`, `Slot` and `PublicKey`, plus `Option::map` and `slice::first`. Aeneas turns
  each into an axiom.
- Branches. Aeneas copies the rest of a function into each branch, so code size grows
  exponentially with the number of `if`s. We split one function into three to stop this.

The fix every time: move the logic into a small pure module on plain `u64`s, and leave the glue
(the milhouse loop, the caches) in `single_pass.rs`. The glue is trusted, not proved.

### One step at a time

Each spec step got its own pure Rust function, its own Lean transcription, and an equality
proof. One PR per step, stacked:

1. Builder pending payments
2. Effective balance updates
3. Inactivity updates
4. Slashings
5. Rewards and penalties
6. Registry updates
7. Pending deposits (first loop proof with a `break`)
8. Pending consolidations

### What the proofs found

None of these is a live bug. Each is a place where Lighthouse and the spec do different things,
and the proof forced us to say why they still agree.

- **Rewards order.** The spec applies rewards and penalties in four rounds, and each round
  saturates at zero. Lighthouse (and Prysm) add all rewards and subtract all penalties at once.
  These differ when a balance is smaller than one flag penalty. Example: balance 3, source penalty
  5, target reward 10. The spec gives 10. Lighthouse gives 8. The proof shows they agree when the
  balance covers the three flag penalties. Real balances are far above that.
- **Registry `if`/`elif`.** The spec uses `if` / `elif` / `elif` for queue, ejection and
  activation. Lighthouse uses three independent `if`s. They agree because the ejection balance is
  below the activation minimum.
- **Lazy leak flag.** The spec reads the inactivity leak flag only for eligible rows. A single pass
  has to handle that read order.
- **Genesis guard.** The inactivity step needs an explicit guard for the genesis epoch.

### Many passes into one

The spec runs each step as its own pass over all validators. Lighthouse runs one loop and does
every step per validator. We proved that the separate passes equal one pass of a combined row
step, first in pure Lean over lists, then against a new pure Rust function
(`single_pass_step.rs`) that Aeneas translates.

Naming lesson: the first names were "fusion" and "kernel". Both were vague. Now it is "single
pass" and plain function names.

### Invariants, and a flaw found after the PR was open

The equality needs hypotheses, such as "the balance covers the flag penalties". A proof with
false hypotheses proves nothing, so we proved them as invariants.

The first version required `effective_balance <= 256 * balance` for every validator. That is
false on mainnet. A fully withdrawn validator has balance 0, and its effective balance only drops
at the next update. So the theorem was vacuous on real states. The fix: require the floor only for
eligible validators. Other rows only need a balance below `2^64`.

Lesson: check that a hypothesis holds on real data before you build on it.

### The whole state transition (option A)

The invariants have to hold on every state that the chain can reach, so we needed block
processing too. We wrote it in Lean as a stack of PRs: withdrawals, requests, slashings,
attestations, sync aggregate and finality, then `state_transition`.

The capstone theorem: on mainnet, from every reachable state, the state transition with the
Lighthouse epoch has the same results as the spec state transition.

Finding: sync committee seat multiplicity. One validator with a 1 ETH effective balance can hold
nearly all 512 seats. If it misses every slot, it can lose about 0.76 ETH per epoch when the total
stake is near `2^57` Gwei. That breaks the balance floor. So the final theorem needs a supply
bound: at most 139 million ETH active. That bound is an explicit hypothesis.

### The tail of the epoch

The first capstone covered the four steps of the single pass. The rest of the epoch (deposit
top-up, effective balance update, new deposits, consolidations, builder payments) still ran on the
spec path. We moved those into the Rust row step too, and modeled the order of the remaining
glue. EF tests pass (104/104 and 166/166). 113 theorems are audited.

Also checked by hand: Lighthouse's Gloas churn limit equals the spec's.

### What we still trust

- The milhouse loop and the order of the glue after it (modeled by hand, not by Aeneas).
- The caches: base reward, total active balance, the pubkey map.
- The oracle (hashing, BLS).
- Supply hypotheses (139M ETH, sums below `2^62` and `2^60`).
- **The hand-written Lean spec.** This is the big one, and the rest of these notes are about it.

The PRs now live on `eserilev/lighthouse-aeneas`.

## Part 2: trusting the spec

### The problem

Our Lean spec is a manual transcription of pyspec. A mistake there makes every proof about the
wrong thing. Every fork needs a manual update.

### Research: why is there no pyspec-to-formal translator?

There have been many formal models of the consensus spec. All were hand-written, and most are
dormant:

- ConsenSys: Dafny.
- Runtime Verification: K and Coq.
- sigp `verified-consensus`: Isabelle.
- `coq-of-python`: paused.
- ericsson49's transpiler: stalled.

The one active project is Etheorem, a hand-written Lean 4 spec (Fulu, Gloas, Heze) that passes the
vectors. Still hand-written.

Why nobody built a translator: Python is dynamic, and the spec relies on it. Objects are shared
by reference. SSZ types have their own arithmetic rules. Loops over lists see appends. A
faithful translator has to model all of that.

### Layers of trust

- Layer 1: tests. Run the vectors and fuzz.
- Layer 2: hand-written models with proofs. Dropped. It breaks on every spec change.
- Layer 3: a Lean interpreter for the Python subset that the spec uses. The interpreter defines
  what the spec means. A translator emits readable Lean, plus a proof per function that it equals
  the interpreter (translation validation).
- Layer 4 (an idea for later): prove the translator itself correct once.

With layer 3, a spec change means a rerun, not a rewrite. The trust moves to one interpreter,
which we can test hard against CPython.

### Does the spec use a "safe" subset of Python?

Mostly. The exception: writes through a local name.

```python
validator = state.validators[index]
validator.exit_epoch = exit_queue_epoch
```

In Python this changes the state. In a value-based language, it changes a copy.

### Experiment: rewrite the spec into a strict subset

We rewrote every such write to use a full path from `state`, and replaced the `for_ops` callbacks
with plain loops. The size: +239 / −183 lines over about 26 functions. All 2048 spec tests passed.

Then the question: why do we need this? `state.validators[index].withdrawal_credentials = ...`
is not more readable than the alias. It asks the spec authors to change their style for one tool.

Decision: revert all rewrites. The translator reads the spec as written.

### The lint

We kept a lint (`scripts/check_safe_python.py`, PR #3 on `eserilev/consensus-specs`). It accepts
the alias patterns that the spec already uses and flags writes a translator cannot follow:

- through a helper's return value, a comprehension element, a conditional expression or a tuple
  unpack;
- through an alias whose index changes before the write;
- inside other nested functions;
- to a parameter that is not a root.

The unchanged spec passes. The final PR is the lint plus one line in the Makefile.

The lint is a guide, not part of the trust story. It cannot see every form of sharing. The
interpreter and the proofs handle that.

### The translator spec, four drafts

Each draft went to a subagent for review. Each review found real errors.

**Draft 1 to draft 2.**

- Pyspec no longer uses remerkleable. It uses `eth-ssz-specs`.
- uint types are nominal. `Slot + Epoch` raises `TypeError`. `Gwei + Uint64` gives `Gwei`.
- Sets iterate in hash order, which depends on `PYTHONHASHSEED`. No fixed order matches pyspec.
- Plain assignment evaluates the right side first. Augmented assignment evaluates it last.
- `bls_setting: 1` vectors need real BLS, not a stub.
- Gloas `Balances` and `Validators` are progressive lists with no limit.

Lesson: probe the real library. Do not trust what you remember about it.

**Draft 3.** The spec is read as written. The translator resolves five alias patterns. The memory
model was V1: references are paths from a root.

**Draft 4.** The review showed V1 is unsound. Three memory models:

- V0, value semantics. Each name holds a copy. It disagrees with Python, and the readable Lean
  disagrees in the same way, so the proof passes on a wrong answer. Unsound.
- V1, path references. Fails on three cases:
  - Rebound prefix: `v = state.validators[0]`, then the element is replaced, then a write through
    `v`. Python changes the old object. V1 changes the new one.
  - Real sharing: Altair sets `previous_epoch_participation = current_epoch_participation`.
    Phase0 rotates checkpoints the same way. Two fields point to one object.
  - Objects a function creates, like `post = BeaconState(...)`. They have no root path.
- V2, a full heap. Chosen. It models Python exactly, so it is easy to test against CPython.

The cost of V2 moves into the proofs. Each validation theorem gets a side condition,
`UniqueWrites`: every object that the function changes in place is reachable by exactly one path.
Sharing is fine if nobody writes to the shared object. A separate invariant proof shows that real
states meet this condition.

Also from the draft 4 review:

- `for` over an SSZ list is live: an append inside the loop extends it.
- A fixed fuel bound cannot cover input-dependent `while` loops. The theorem says "for every input
  there is enough fuel".

Lesson: "how hard is modeling Python's heap?" turned out to be the right question. The heap
itself is easy. The hard part is proving that a value-based Lean function matches it, and that is
one clean side condition.

**Draft 5.** The heap model held up. The proof rule around it did not.

- The aliasing condition counted paths only from the arguments. `upgrade_to_electra` builds
  `post = BeaconState(balances=pre.balances, ...)` and writes through `post`. Python changes `pre`
  too. The condition passed, and a translator that treated `post` as new would prove something
  false about `pre`.
- The fix: the theorem compares every argument after the call, not only the ones the translator
  expects to change. A wrong guess now makes the proof fail.
- The condition is now one rule on the input heap (`WTree`): each object that the function writes
  in place has exactly one path from the arguments. Each theorem gives the rule back on its result,
  so calls compose. The rule then holds on every reachable state by induction.
- A `while` loop with fuel in the readable Lean breaks the theorem. One loop
  (`compute_balance_weighted_selection`) ends only because of sha256 outputs. Readable loops now
  use recursion on an explicit bound.
- Errors: compare only "error" against "ok". The EF vectors check nothing more.
- A dynamic check in the interpreter counts paths at each write, on all EF vectors. It finds the
  `upgrade_to_electra` case at once.

Lesson: a correct model of Python is not enough. The contract between the model and the readable
code is where the bugs hide.

**Draft 6.** The draft 5 fix was false in a simple case.

- `get_current_epoch` writes nothing, so its write condition was empty. But its result had to meet
  the condition for everything the state transition writes. Give it a state whose two
  participation lists are one object, and the theorem promises something false.
- The fix: one global write condition, the same before and after every function.
- The frame was too weak. A callee could replace an object with an equal copy, and the decoded
  values would still match. Python code that holds the old object then writes to the wrong one.
  `process_attestation` does exactly this with a builder payment. The frame now says that every
  object outside the function's footprint keeps its contents.
- The upgrades are not called by any spec function. The test harness calls them. So they get
  their own theorem form, with the write condition only on the result.
- Errors split into two classes. `invalid` is an assert or index error, which is all the EF
  vectors use. `bug` is anything else, such as an overflow or a type error. Now "the spec never
  has a bug error" is a theorem we can try to prove.

Lesson: a condition that is not the same at entry and exit does not compose. We found it with a
function that does nothing.

### Spike

Step 1 of the plan: a Lean `Value` type, a heap, a minimal interpreter, and hand validation of
three functions in their original form.

The first version worked, under the draft 4 rule:

- Three functions proved: `decrease_balance`, `process_effective_balance_updates` (it writes
  through the loop variable `validator`) and `integer_squareroot` (a `while` loop).
- No `sorry`, no extra axioms. A clean build takes 11 seconds.
- A differential test ran 18 cases through the interpreter, the readable Lean and pyspec. It found
  0 differences, including overflow, index errors and a `TypeError`.
- 596 value-rule probes against `eth-ssz-specs` pass.

What the spike taught the spec:

- The library resolves uint result types with one rule, not a table: the derived class wins.
- Once `for` loops are live, each iteration must cost fuel. So the fuel a run needs depends on
  the input.
- The input condition only needs to be about the input heap. The function's own aliases need no
  extra condition: the proof covers them, or it fails. This was the first sign that the design
  works.

The spike also showed where it was behind the spec: plain `Nat` for every uint, error kinds
compared, `for` loops that took a snapshot, and no augmented assignment.

### Where we are now (2026-10-05)

- SPEC.md is at draft 6.
- We stopped the paper reviews. Each review found a real hole, but each one only checked the
  design on paper. A Lean proof that fails to go through tells us more.
- The spike is moving its three proofs to the draft 6 rule: one global write footprint, the
  stronger frame, and `invalid` against `bug` errors. It makes the smallest change that works.
- Next, the same agent builds step 2: the interpreter for the full version 1 scope (the state
  transition and the upgrades), with a test per construct. No new proofs in step 2.
- After that, step 3: run the interpreter on the Gloas EF vectors, with the dynamic sharing check
  on.

Decision: write no new spec drafts unless code shows a problem.

Update: the spike moved its three proofs to the new rule in one pass. All three still go through,
with no `sorry`. A clean build takes 13 s.

- Resolving the alias `validator = state.validators[index]` cost one line in the readable Lean.
  The real cost was the loop: proving that it ends.
- `process_effective_balance_updates` took about 430 lines of proof. About 90 lines are lemmas
  that other functions can reuse.
- The code found two holes that the paper reviews missed. Frames do not chain without one more
  fact: the function reaches no old object that it did not reach before. And the clause "new
  addresses were free" was always true, so it said nothing.

This is the point of stopping the reviews. The prototype found these holes in one pass.

Update: the spike now follows the draft 6 rule (global footprint, stronger frame, `invalid` against
`bug`). All proofs go through, with no `sorry`. A clean build takes 12.8 s. Step 1 is done. Step 2,
the full interpreter, has started.

## Running list of lessons

- Pure functions on plain integers are what make Rust provable. Leave the glue small and obvious.
- A proof finds every place where two implementations differ, including the harmless ones. Each
  one needs a written reason.
- Check every hypothesis against a real state.
- Hand-written models are the weakest link, and the hardest to keep current.
- Do not change the source to fit the tool if the tool can handle the source.
- Probe the library. Memory is wrong about library behavior.
- Name things for what they do.
- An independent reviewer found real errors in every draft.
- Paper reviews give less each round. When a working prototype exists, let it find the holes.

### Step 2: the interpreter (2026-10-05)

The interpreter now covers the version 1 scope.

- The serializer reads the pinned spec and writes 163 functions, 769 names and 31 containers,
  starting from `state_transition`, `process_slots`, `process_block`, `process_epoch` and
  `upgrade_to_gloas`. The generated file compiles in 3.6 s.
- 56 construct tests compare CPython and the Lean interpreter. 0 differences.
- The value-rule probes grew to 1264 rows. All pass.
- The three proofs moved to the new interpreter without trouble. A clean build takes 23 s.
- The serializer rejects any node it does not know, so it is also the constructs scan.

Steps 1 and 2 are committed (`7442c57`). Next: step 3, the EF vectors.

### The name: Pythia

The project is now called Pythia. The Pythia was the oracle at Delphi, named after the serpent
Python. It fits next to Aeneas and Charon. The repo is `eserilev/pythia` (private for now).

### Step 4 came early: the fuzzer (2026-10-05)

We built the differential fuzzer while step 3 ran. It generates random small Python programs,
runs each one in CPython and in the Lean interpreter, and compares the results, including which
objects are shared.

- About 43,000 programs, at about 450 per second for the two runs.
- 11 distinct differences, each shrunk to a small repro in `tools/fuzz/corpus/`.
- Three of them were rules in our own spec:
  - List comprehensions iterate live, like `for` loops. We said they took a snapshot.
  - Generator expressions are lazy. `any` and `all` stop early, so later items never run.
  - `.copy()` of a plain Python list is shallow. We said every copy was deep.
- The other eight were interpreter bugs. Examples: a `Slot` stored in a `Uint64` field stays a
  `Slot`. `True + Uint64(1)` is the int `2`. A dict literal evaluates all keys before any value.

Lesson: the spec rules that "everyone knows" were the ones we never probed. The fuzzer found
them in minutes.

### Step 3: the EF vectors (in progress, 2026-10-05)

The Lean interpreter runs the Gloas EF vectors on the minimal preset.

- 545 cases pass, 36 fail, and 137 are skipped (mostly cases that need real BLS).
- 20 failures are timeouts at 600 s, all in finality and multi-epoch sanity blocks. The
  interpreter is too slow for runs over several epochs. Profiling is under way.
- 15 failures are a `TypeError`, most of them in `process_attestation`. This is likely one
  value-rule bug.
- 1 failure is an invalid-signature case. The BLS stub accepts every signature, so this case
  belongs with the skipped ones.
- The dynamic sharing check (`WTree`) and the mainnet preset have no results yet.

So far: simple operations and epoch processing match pyspec. The open problems are speed and
one type bug.

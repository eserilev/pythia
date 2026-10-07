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
  `Slot`. `True + Uint64(1)` is the int `2`. A dict literal evaluates each key, then its value.

Lesson: the spec rules that "everyone knows" were the ones we never probed. The fuzzer found
them in minutes.

### Step 3: the EF vectors (in progress, 2026-10-05)

The Lean interpreter runs the Gloas EF vectors on the minimal preset.

First run: 545 pass, 36 fail, 137 skipped (mostly cases that need real BLS). The failures were 20
timeouts on multi-epoch runs and 15 `TypeError`s, most in `process_attestation`.

Latest run without the sharing check: 646 pass, 1 fails. The speed problem and the type bug are
fixed. The one failure is an invalid-signature case: the BLS stub accepts every signature, so the
case belongs with the skipped ones. So the interpreter matches pyspec on every minimal vector it
can run.

With the sharing check (`WTree`) on, the first runs reported many hits. All were false alarms:

- `is_eligible_for_activation(state, validator)` gets the state and one of its validators, so that
  validator has two paths at call entry.
- `set_or_append_list` returns with the new validator both in the list and in its argument.
- `upgrade_to_gloas` returns a `post` that shares fields with `pre`. That is expected: the upgrades
  are entry points.

None of these functions writes the shared object. The rule counted sharing among a call's
arguments, which is too strict, because many spec helpers take `state` plus a part of it.

The new rule:

- At each write: the written object has exactly one path from all live names. This is the real
  hazard check, and it did not change.
- At call entry: only the objects that the callee writes must have one path.
- At call exit: the callee creates no new path to an old object, and writes nothing outside its
  footprint.
- At the top level: the whole state meets the rule at entry and exit.

Result on the minimal preset, with the check on: 0 hits. 678 of 681 cases pass, including the
fork tests. The other 3 test invalid signatures and need real BLS. A full run takes about 4
minutes on 16 cores with the check, and about 1 minute without it.

The serializer now computes each function's write footprint. 63 functions write in place. No
function wrote outside its footprint.

Blind spot: no minimal vector writes to a shared object, so the real hazard check never fired.
The pass shows that the hazard does not occur. It does not yet show that the check catches it.
The fuzzer needs to run with the check on, plus one program that must trigger it.

For the proofs, the new rule makes the per-function theorems simpler. The cost moves to one new
lemma: a write to an object with one path, with no new paths created, keeps the whole state free
of unsafe sharing.

Final result (committed as `4ebc9c3`):

- Minimal: all 678 runnable cases pass. With the sharing check on: 0 hits, 4 minutes on 16 cores.
- Mainnet: 598 of 605 pass, with 0 wrong results. 7 multi-epoch cases time out at 30 minutes.
- Skipped: about 100 cases per preset that need real BLS, and 9 mainnet cases that change the
  blob schedule in the config.

The big speed fix: heap and local-name lookups walked a growing chain of closures. A persistent
trie behind each one cut one sanity case from 355 s to 5 s. The definitions that proofs read did
not change, so the proofs did not change either.

The vectors found more interpreter bugs: list `+`, `*` and `+=`, `Uint64(Boolean)`, a missing
BLS constant, and a BLS helper that pyspec routes through the oracle.

The fuzzer had one diagnosis wrong. It said a dict literal evaluates all keys first. CPython
evaluates key 1, value 1, key 2, value 2. The fuzzer's own repro shows this order.

### Next: split core and library (approved)

The interpreter mixes Python rules (loops, assignment, `int + int`) with SSZ library rules
(`Slot + Epoch` is an error, uint coercion, `hash_tree_root`). After step 3, the SSZ rules move
into a plugin. The core asks the plugin first and falls back to plain Python. A new target, such
as the execution specs (EELS) or leanSpec, then needs only a new plugin.

Why now: the split changes the `Value` type. Step 5 adds many proofs that depend on it, so the
split is cheaper before step 5.

Decision (2026-10-05): do the split in two parts.

1. Now: move every SSZ behavior into a plugin (`LibModel`, with `sszModel` as the first one). The
   core asks the plugin first and falls back to Python rules. The serializer splits the same way.
2. Later: the data types. Heap objects still carry SSZ tags (list kind, element type, limit). About
   60 places in the proofs match on them. Making them generic now means guessing the interface
   for a second target that we have not started. So we only measure the cost now, on a scratch
   copy, and decide when work on EELS or leanSpec starts.

### Step 5: the translator (started 2026-10-05, autonomous)

Item 1, the proof contract, is done (`87dbb47`, `eebf58e`). The theorems now use the narrow
sharing rule that the EF runs use:

- Each theorem asks only that the objects the function writes have one path.
- The result no longer has to meet the global rule. One lemma, `wtree_compose`, gives that back
  for any footprint: the function reaches no old object it did not reach before, and each new
  object has one path.
- One surprise: "reaches no new old object" was not enough. A function can build a new list that
  holds one new object twice. So the lemma also needs "each new object has one path".
- The three proofs got shorter: the parts that kept the global rule on the result are gone.

Item 2, the translator, is done (`d9aebf4`). It turns all 162 scope functions and 73 types into
readable Lean, about 7,000 lines. The file builds in 14 s with no `sorry`. The EF runner can now
run every case through the readable Lean too. Result: 678 of 678 minimal cases pass on the
readable Lean, as on the interpreter.

The vectors found five translator bugs, all fixed. The most interesting one: a local name bound
to a field that a later line replaces. `old_previous_justified_checkpoint` must keep the old
object, not follow the path to the new one. That is the V1 "rebound prefix" failure from the
draft 3 review, found again in real spec code.

Two places where the readable Lean differs from the spec text, open for now:

- Early returns are `return` inside `do`, not if-then-else. Item 3 shows whether this hurts the
  proofs.
- When a uint goes to a parameter of another class with the same width, the readable Lean
  converts it. Python keeps the argument's class. The vectors cannot see this. The proofs will:
  a theorem fails wherever the difference changes a result.

Status at 11:40: the tactic proves 21 of 41 leaf functions alone (`5cf104e`), up from 12 an hour
earlier. The work now is on functions with local variables. Calls, `for` loops and `while` loops
come after. This is the slow part: each new statement shape is a new way for the tactic to get
stuck, and each try means a Lean compile.

The fuzzer's second campaign (21,000 programs, merged as `092d4db`):

- All 10 hand-written hazard tests trigger the sharing check: shared fields, callees, returned
  refs, shared elements, appends, loops and deep call chains.
- A new oracle: each program also runs in CPython with every stored value deep-copied. Where the
  two runs differ, a value-based translation would be wrong, so the check must fire.
- That oracle found a gap in the check: `v1 = Box(p=a0); a0.a = 1; return v1`. The write
  through `a0` counted only one path, because the check did not count the path through the
  local `v1`. The proofs still catch this case, because the theorem compares the returned value.
  But the check is meant to catch it first. Fixed at 11:50 (`2a850bf`, branch `fuzzer`): paths
  through locals now count.
- 3 more interpreter bugs (writes into `Bitlist`, `Bitvector` and `Boolean` fields that CPython
  accepts) and a few missing builtins.
- The early `IndexError` rate fell from 30% to 22%.

Status at 11:50: the tactic count is still 21 of 41 leaf functions. The work on functions with
local variables is not committed yet. The fuzzer is fixing the interpreter on its own branch,
because the spike is busy with the tactic. Done so far: the check gap, the `Boolean` coercions,
`bit_length`, set `difference` and dict views. Still to do: the bitlist and bitvector writes,
`ssz_serialize` of an int, the `ByteList` model, an EF rerun with the check, and a new campaign.

Status at 12:15: no new commits since 11:50. The spike is running the full leaf tier through the
generator and the proof check, which gives the next count. The fuzzer is rerunning the EF
vectors with the sharing check, to confirm its interpreter fixes broke nothing.

Status at 14:00:

- The tactic proves 25 of 41 leaf functions (`9df8f29`), including leaves that write.
- The proofs found their first bug that no test had found. In `a < b <= c + d`, the readable Lean
  computed `c + d` even when `a < b` was false. Python stops early. So an overflow there gave a
  "bug" error in Lean where Python gives "invalid". The vectors never reach this case.
- The code was wrong and the spec was right once: `Frame` also covered free addresses, so any new
  object broke it (`555d58a`).
- A hole in the contract. `Reach` kept every object on a fixed path. That is false when a function
  slices a list or pops from it, because the elements move. Two Gloas epoch functions do this. The
  new rule counts paths instead: no old object may gain a path. Moved elements keep one path, and
  dropped ones go to zero.

The crash. At 13:44 the machine ran out of memory. The kernel killed one `lean` process at
12.9 GB, during a proof build with the new path-count rule. The crash took down the session and
both agents. Nothing committed was lost, and the uncommitted work stayed on disk. New agents
picked up the work from the files. From now on, every Lean build runs under a hard memory cap.
If the cap kills a proof, the proof gets fixed, not the cap raised.

Lesson: an agent's progress lives in the files it commits, not in the agent. Commit often.

### The fuzzer after the crash (2026-10-05)

A new agent finished the fuzzer work from the files on disk.

- The bitlist and bitvector writes and `ssz_serialize` of an int were already fixed in `2a850bf`.
- The `ByteList` model. The heap keeps a byte list as a `List` of `Uint8`, as the readable Lean
  and `hash_tree_root` need. Python reads it as a `bytearray`: an element is an `int`, a slice
  and `+` give `bytes`, `==` with any other type raises `TypeError`, and a `for` loop takes a
  snapshot. The serializer now rejects any other list of `Uint8`, so the two never mix.
- The byte list checks live in their own match arms. An `if` on the list kind broke the
  leaf proofs, because their list kinds were unknown before `decListT`.
- A campaign of 10,000 programs with every `--avoid` family on found three more: the byte list
  snapshot, the order of byte strings (`sorted` of `Root`s), and `AttributeError` on an
  attribute of a byte string.
- After the fixes: a second campaign of 10,000 programs found no difference and no hazard miss.
  EF minimal with the sharing check: 678 of 678 pass, 0 hits.

Status at 15:30:

- The cause of the crash: two tactic loops that never ended. One frame lemma unified a heap write
  with a heap allocation, at default transparency. One `apply` also matched its own output, so it
  made new goals forever. Each loop ate memory until the kernel killed it. The fixes: try the
  allocation lemmas first under `with_reducible`, and use `refine` in place of `apply`. One proof
  went from 4+ GB to 550 MB. Every proof check now runs in its own capped scope.
- The path-count rule (`NoNewPaths`) replaces `Reach` (`144bb97`). It is a one-to-one map from
  new paths to old paths that keeps the footprint patterns. Still 25 of 41 leaves.
- Next blockers: the uint decoders do not check the range, so range checks in constructors cannot
  be proved. And `process_eth1_data` shares `eth1_data` between the block and the state, so the
  path count must cover only footprint objects.
- The fuzzer branch is merged (`7dae481`). ByteList now behaves as bytes, as in CPython. The last
  campaign of 10,000 programs found 0 differences and 0 hazard misses.

Lesson: a proof tactic can loop like any program. Under no memory cap, one bad `apply` took down
the machine.

Status at 23:00: the tactic proves 49 of 162 functions alone: 29 leaves, 17 calls and 3 loops.

- The call rule worked at once (0 to 15 calls). After that, progress came about one function per
  commit, which is the pattern we wanted to avoid.
- The general loop lemmas are on master (`944f700`), built by a second agent in parallel:
  `for_sim` for every `for` loop with the contract chained over each pass, variants for live
  lists, `enumerate` and `zip`, and `while_sim`.
- The tactic proves its first loops (`e6c4e43`, `a3d6a6a`): two `for` loops and
  `integer_squareroot`. So far only simple loops: they write nothing to the heap and carry only
  uint locals.
- Not covered yet, and where most of the remaining functions are: loops that write the heap (all
  the `process_*` epoch functions), callers of loop functions (their fuel depends on the input),
  and comprehensions.

Honest read: the machinery is in place, but the count is rising slowly. The next rule, loops that
write the heap, is the test. It covers the functions that the Lighthouse proofs need most.

### Overnight (2026-10-06)

- Mainnet with the sharing check on: 593 of 605 pass, 12 long multi-epoch cases time out at 40
  minutes, 0 wrong results and 0 sharing hits. The run took about 3 hours on 8 runners.
- The tactic proves 50 of 162. The new one is the important one: `process_effective_balance_updates`
  is the first heap-writing epoch loop proved with no hand help. The loop rule sits on the generic
  `for_sim` lemma that a second agent built in parallel. Most other loop functions now wait on
  helpers that return lists.
- The second agent also built the general rules for comprehensions (`comp_sim`), snapshot
  sources like `range(n)`, and new objects (`alloc_contract`: one lemma gives the whole contract
  for a new list).
- Two more memory traps in proofs: Lean computing a heap store at default transparency, and
  `omega` on `max x 0` facts. Both fixed. The memory caps caught them before the machine did.

### The layer 4 spike

We tried the other road in parallel: prove the translator correct once, as Aeneas does, instead
of proving each generated function.

- The result, for a fragment (expressions, writes, `if`, `return`, `assert`, no loops or calls):
  one theorem, `denote_sound`, proves the Lean translation matches the heap interpreter for every
  program in the fragment, under the sharing rule. No `sorry`, standard axioms only.
- Size: about 2,400 lines. It builds in 7.5 s. Two real spec functions go through it, and for
  `is_active_validator` the translation equals the generated readable Lean by `simp`.
- A twist: inside the translator, a local holds a "place", a path from an argument. That is the
  path model we rejected in draft 4 as the meaning of Python. As a translation target it is fine,
  because the theorem proves it matches the real heap whenever the sharing rule holds.
- Same traps as the tactic: `simp` unfolding value rules into a `2^64` range check, and runs that
  "passed" because the memory cap had killed them silently. Always check exit codes.

The spike's verdict: full layer 4 is realistic, and more robust than proving each function.

### Proving all 162: general rules, not one function at a time (2026-10-06)

The count over the day: 25 → 45 → 49 → 50 → 55 of 162.

- After the call rule, progress slowed to about one function per commit. Each commit fixed one
  shape. We asked the tactic agent to stop and sort every unproved function by its first
  blocking cause. The answer was good news: four causes blocked 79 of the 113 open functions.
  The biggest: a result that is a list (33), a result that is a container (17), a loop that
  writes the heap (16), an `Option` argument (13).
- So the work became: one general rule per cause, then regenerate all 162. Rules added since:
  - for loops that write the heap (`process_effective_balance_updates`, the first epoch loop
    proved with no hand help);
  - comprehensions, live and over `range(n)`;
  - new objects (`alloc_contract`: one lemma for the whole contract of a new list);
  - callers of loop functions, with a fuel bound per function that the caller adds up;
  - `sum` over a generator, next to unlock `get_total_balance` and its many callers.
- Two agents split the rules: one builds the generic lemma in new files, the other wires it into
  the tactic. That kept them out of each other's files.
- A case explosion stalled the first loop proof: 2.8 MB of open goals. Each step that can fail
  split into ok and error on both sides, so ten steps gave about 4^10 cases. The fix is a joint
  step: both sides ok with matching values, or both error with the same class.
- Container `==` changes in the readable Lean: from derived `BEq` (field by field, not usable as
  equality in proofs) to `decide (x = y)`. The vectors still have to pass.

### What Aeneas taught us

Aeneas turns Rust into pure Lean, the same job for a different language.

- Aeneas does not prove each function. It trusts the translator, whose method is proved sound
  once on paper. Rust's borrow checker rules out shared writes, so the translation can use plain
  values.
- Python has no borrow checker. Nothing in the language stops two names from writing one object.
  That is the whole reason for Pythia's heap model and the `WTree` rule.
- Two kinds of sharing look alike. A local name for a part of the state
  (`validator = state.validators[i]`) is everywhere in the spec, and the translator maps it to a
  path. One object at two places in the state, then written, is the dangerous kind. The spec
  creates that sharing (checkpoints, the payload bid, `eth1_data`) but never writes to it in place.
  The vectors, the fuzzer and the proofs all agree.
- Aeneas's `progress` tactic applies each callee's lemma at a call, found by an attribute. Our call
  rule does the same.
- Aeneas does not automate loop proofs either. Its users write the loop invariants. That made it
  fair for us to allow an invariant annotation where the tactic cannot find one.

### Layer 4 takes the lead

The layer 4 spike proved one theorem for a fragment of the spec (no loops or calls): the Lean
translation matches the heap interpreter for every program in the fragment. It took about 2,400
lines and builds in 7.5 s.

- It is Aeneas's approach with one upgrade: the soundness proof is in Lean and checked by
  machine, not on paper.
- Python's missing borrow checker shows up as `WTree` inside that one theorem, instead of in
  every function's proof.
- The decision (2026-10-06): build the layer 4 call rule now, proved once by induction on call
  depth, while the per-function tactic keeps going as the fallback. If layer 4 gets calls and
  loops, it becomes the main path. Every lemma from the tactic work carries over.

### Is this viable?

An honest check after a full day and night of agents:

- Solid: the interpreter (678/678 minimal and 593/605 mainnet with the sharing check, 0 wrong
  results, about 80,000 fuzzed programs) and the translator (all 162 functions, 678/678).
  Together they are already a readable Lean spec, generated from pyspec and tested against it.
- Not yet shown: proving all 162. The per-function tactic is at 55. Layer 4 is the better bet
  for the rest.
- The goal stays all 162, through general rules.

### Two ways to prove a translator: the tactic and layer 4

By the morning of 2026-10-06 we had two proof strategies running side by side. They prove the
same fact: the generated readable Lean does what the Python spec does. They differ in where the
work happens.

#### The question both answer

The interpreter defines what the spec means. It models Python exactly: a heap of objects, refs,
shared objects, live loops. The readable Lean is what people will write proofs against. It uses
plain values: a `BeaconState` is a Lean structure, not a heap address. A proof has to connect the
two. For each spec function, it must show that running the Python code on the heap gives the same
result as running the readable Lean on the decoded values. And it must show that this holds only
because the code never writes to a shared object (`WTree`), and that the function leaves alone
everything it does not own (`Frame`, `Fresh`, `NoNewPaths`).

#### Strategy 1: the per-function tactic (translation validation)

How it works:

- The Python translator writes the readable Lean. A second script writes one theorem per
  function: "this function's readable Lean matches the interpreter".
- A custom Lean tactic proves each theorem. It steps through both programs at once, statement by
  statement: one step of the interpreter on the heap, one step of the readable Lean on values.
  At each step it shows that the values still match and that the heap facts still hold.
- A call uses the callee's own theorem as a black box. A loop uses a loop lemma (`for_sim`) plus a
  proof of one pass of the loop body.

Example. For `decrease_balance`, the tactic runs the interpreter's
`state.balances[index] = saturating_sub(state.balances[index], delta)` through a heap read, a call
and a heap write. It runs the readable `lset … (saturating_sub …)` beside it. After each step it
checks the decoded balance list, the frame and the path counts.

Pros:

- The translator can be anything. It is a Python script, and nobody has to prove it correct. If
  it makes a mistake, the proof for that function fails and points at the line.
- It handles everything the interpreter can do, including writes of whole objects and the
  sharing in the upgrades. The heap is right there in every proof.
- It is the standard method ("translation validation"), used by verified compilers for passes
  that are hard to prove in general.

Cons:

- Every function needs its own proof, and every proof does heap reasoning. A new spec shape is a
  new way for the tactic to get stuck.
- Progress came one function at a time for long stretches. After a day and a night: 55 of 162.
- The proofs are big and slow to check. The leaf file alone takes 79 s. Tactic bugs can loop until
  the machine runs out of memory, which happened once.
- Each step that can fail splits into "ok" and "error" on both sides. Without care, ten such steps
  give about a million cases.

#### Strategy 2: layer 4 (a verified translator)

How it works:

- The translation is written in Lean, as a function `den` from the syntax tree to Lean semantics.
- One theorem, `denote_sound_calls`, proves once that `den` matches the interpreter, for every
  program, under the sharing rule. The proof is one induction on fuel.
- Per function, only two small facts remain: a summary of what `den` gives for it, and a `simp`
  proof that this equals the generated readable Lean. Neither touches the heap.
- Inside `den`, a local name holds a value or a "place": an argument plus a path, such as
  `state.balances[index]`. A write through a place updates the decoded tree at that path. A call
  that writes passes a place, and the callee's result is written back there, the same idea as
  Aeneas's backward functions.

Example. For `get_previous_epoch`, layer 4 needs no heap proof at all. `den` gives
`saturating_sub(get_current_epoch(state), 1)` on decoded values, using the summary of
`get_current_epoch`. `simp` shows that equals the readable function. The general theorem does the
rest.

Pros:

- The hard part is proved once. The fragment theorem took about 2,400 lines. Adding calls took
  2,700 more. Loops went in as one more case of the same induction.
- Per function, the work is small and has no heap reasoning: about 30 to 60 lines and 1.3 s.
- It is robust to new code. A new function made of known constructs needs no new proof idea.
- It is the same idea as Aeneas, with one upgrade: Aeneas proves its translation sound on paper,
  and this proof is in Lean, checked by machine.
- Progress came in whole language features per commit: calls in one go, then loops.

Cons:

- The translator must be written in Lean and proved. Every construct needs a case in the theorem.
- The path model has a hard limit. Code that stores whole objects into the state or shares them
  (`state.x = obj`, building `post = BeaconState(...)` from `pre` in the upgrades) does not fit.
  A model that handles it turns back into a heap, which is just the interpreter again. The
  layer 4 agent estimates 120 to 140 of the 162 functions are in reach.
- It needs its own generator for the per-function summaries before it scales past a handful.
- Lean's `simp` falls into the same traps as the tactic: unfolding a value rule down to a check
  against `2^64` in unary, which blows up the kernel. Each operation needs a small step lemma.

#### Side by side

| | Per-function tactic | Layer 4 |
|---|---|---|
| What is proved | each generated function, separately | the translator, once |
| Where the heap reasoning lives | in every function's proof | in the one general theorem |
| Who writes the readable Lean | a Python script, untrusted | a Lean function, proved |
| Per-function work | a generated heap proof, often stuck on new shapes | a summary and a `simp` equality |
| Build cost | about 2.7 s per function, 79 s for the leaf file | about 1.3 s per function, 14 s for all of layer 4 |
| Covers shared objects and whole-object writes | yes | no (path model) |
| How progress came | function by function, with general rules in bursts | language feature by language feature |
| Closest prior art | translation validation in verified compilers | Aeneas, with the soundness proof in Lean |

#### The decision: a hybrid

Neither alone covers everything well. Layer 4 is cheaper and more robust for the bulk of the spec.
The tactic covers the sharing-heavy remainder that the path model cannot express: the upgrades and
the functions that store whole objects. So both stay: layer 4 for most functions, the tactic for
the rest. Every lemma built for one also serves the other: the decoders, the frame and path rules,
the loop and comprehension lemmas.

How we got here, in short. We started with the tactic because translation validation is the safe
choice: it needs no trust in the translator. When the tactic slowed to one function at a time, a
small parallel spike tried layer 4 on a fragment. The spike went better than expected, and calls
and loops followed within hours. The lesson: when one road slows down, a cheap parallel spike on
the other road is worth more than another day on the first.

### Layer 4 grows: loops, new objects, a generator (2026-10-06)

- Loops went into layer 4 as one more case of the same fuel induction (`fb98416`). Two loops now
  go end to end: `process_effective_balance_updates` (a live loop that writes through the loop
  variable) and `apply_withdrawals`, whose loop body calls `decrease_balance`. That call is the
  first real test of write-back through a call.
- New objects (`2be057c` to `3b6eff3`). The core rule changed from "the heap does not grow" to
  "old objects keep their shape, and new objects appear at free addresses". A new object is an
  immutable tree that shares nothing with the arguments. So writes through the arguments can
  never reach it, and no aliasing check is needed. `get_active_validator_indices`, which builds a
  new list, goes end to end.
- The generator (`tools/gen_l4.py`) is the decisive piece now. The general theorem covers whole
  language features, but each function still needs a generated summary. One big `simp` per
  function does not scale: unfolding the denotation all the way makes Lean's kernel recurse too
  deeply. So the generator writes structured proofs: a rewrite per statement, `simp` with small
  step lemmas per expression, and the callee's summary per call.
- More kernel traps, all the same shape: Lean evaluating a big number in unary. A sum with a
  literal under `decide`, a bit mask like `x &&& 1099511627776` closed by `simp`, and
  `rw [if_pos …]` closing a goal by heavy unfolding. Each has a workaround.

### Drawing the line: what we prove and what we trust (2026-10-06)

The tactic's frontier showed which functions block the most others. Three of them were not spec
logic at all: `hash_tree_root` (about 30 functions behind it), `set(list)` (31) and
`uint_to_bytes` (24). That raised the question: do we need to prove these at all?

We looked at Aeneas again. Aeneas proves nothing about Rust's standard library. `Vec`, `HashMap`
and integer operations get hand-written Lean models in `Aeneas.Std`, and those models are trusted.
Aeneas only translates your code. We took the same line:

- Spec functions, the code written in the consensus specs, are proved. That is the point.
- `hash_tree_root`, `sha256`, BLS and KZG are oracles on both sides: the interpreter and the
  readable Lean call the same oracle. The only assumption is that `hash_tree_root` depends only on
  the content of its argument. The EF runs still check the real roots.
- Library and builtin operations (`set`, `sorted`, `sum`, `min`, `max`, `len`, `ssz_serialize`,
  bytes slicing, the uint table, and a few more) are trusted primitives.
- The fork upgrades are tested, not proved. They run once per fork, and they share objects between
  `pre` and `post`, which is the hardest case for both proof strategies.

One condition makes the primitives rule sound: one model per primitive, not two. If the
interpreter had its own `set` and the readable Lean had its own `dedup`, we would trust two models
and an unproved link between them. So each primitive is defined once, in Lean, on decoded values.
The interpreter's builtin decodes, calls that model and encodes. Then the two sides agree by
definition. Our trusted models also have more evidence behind them than Aeneas's: the fuzzer
tests them against CPython and the real SSZ library.

A primitive that already has a proof keeps it. `set(list)` was almost proved when the rule came
in, so we kept the proof.

The claim is now: every spec function of the state transition, except the upgrades, is proved
equal to the interpreter. Hashing and signatures are oracles, and library operations are trusted
primitives with one shared model.

#### `hash_tree_root` in detail

The gap. The tactic agent found it: the interpreter calls an abstract oracle,
`sha.hashTreeRoot h v`. The readable Lean computes the root itself, with `Htr.root`, our Merkle
code in Lean. Nothing linked the two, so about 30 functions could not be proved as stated:
`compute_fork_data_root`, `compute_signing_root` and everything that calls them.

The expensive route, built first by a second agent:

- One assumption on the oracle, `OracleHtr`: the oracle equals `Htr.root`, the oracle's `sha256`
  is the spec's, and every root is 32 bytes. The last one was needed because the readable `Root`
  type checks the length and the interpreter does not.
- A generic lemma, `root_bis`: two values with the same content, to a given depth, have the same
  root, even in two different heaps.
- A bridge per SSZ type: the root of a heap value equals the root of its readable encoding. Done
  for `ForkData` and `SigningData`. `compute_fork_data_root` went end to end.
- The cost: one lemma for each of the 73 types, a stability lemma for nested containers and lists
  (not written), and a new "shape" condition on every argument: each container has the field
  count of its class. Without that, extra fields would change the root, and the decoders do not
  check the count.
- One trap: unfolding `Htr.root` inside a proof made a single `simp` take 523 seconds. A lemma that
  the root never runs out of fuel closed those cases without unfolding.

The cheap route, which we chose: both sides call the same oracle. The readable Lean's
`hash_tree_root` calls `sha.hashTreeRoot` on the value's encoding. The proof then needs only
"same content, same root", which is `root_bis`. No per-type bridges, no shape condition, no Merkle
reasoning. `Htr.root` stays as the executable implementation, so the EF runs still check real
roots against the vectors.

Why it is fine to trust the oracle: the Lighthouse epoch proofs already treat `hash_tree_root` as
an oracle, and Aeneas never proves hash functions either. What we want to prove is the spec's
logic, not SHA-256 or Merkle trees.

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
- When the work stalls, sort the failures by cause. A few causes usually block most of them.
- A general rule is worth more than any number of one-function fixes.
- A proof tactic can loop like any program. Cap its memory, and check exit codes: a killed run
  can look like a pass.
- Proving the translator once beats proving every output, if the soundness proof is affordable.
  The spike showed it is.
- When one approach slows to a crawl, run a small, bounded spike on the alternative in parallel.
  Its result changes the plan faster than another day of pushing.
- Decide what you trust before you decide what you prove. Proving library code is the most
  expensive way to gain the least.
- If you trust a model, trust one model. Two models with an unproved link are worse than either.

### First layer 4 counts (2026-10-06 afternoon)

- The layer 4 generator (`tools/gen_l4.py`) now runs over all 162 functions. The design that
  worked: one rewrite lemma per syntax node of the denotation, so the kernel never unfolds it, and
  the same three-line proof for every function.
- Each function gets three theorems: the denotation equals the readable Lean, a rewrite lemma for
  its callers, and the end-to-end theorem against the interpreter through the one general
  soundness theorem.
- Count: 14, then 23, then 28 "denotation = readable", then 37 end to end. The tactic is at 56.
- The ceiling is the fragment, not the generator. Only about 51 functions use nothing outside it.
  The rest use method calls such as `append` (41 functions), list or tuple literals (33), keyword
  constructors (15), `+=` on a local name (14), `while`, `break` or `continue`. Each of those is a
  new case in the general theorem.
- Decision: grow the fragment next, ordered by how many functions each feature unlocks.

Status at 14:00:

- Layer 4: 37 of 161 functions proved end to end (the upgrade is out of scope). Each has the full
  theorem against the interpreter. Writers carry the `WTree` assumption on their footprint.
- `+=` on a local name is now in the denotation, with its soundness proof.
- The key measurement: how many functions stay inside the denotation, callees included. Today 54.
  Each missing feature raises that ceiling by a known amount: tuples +17, keyword constructors +10,
  methods such as `append` +7, set and generator comprehensions +2, `while` +1, `break` and
  `continue` +1. With all of them, the ceiling covers essentially the whole target. So layer 4 has
  no hard wall, only a list of features with known payoffs.
- The gap between 37 and 54: loops that need a per-loop induction in the generator, list
  arguments, the hash oracle, and byte-length invariants.
- Plan: loop induction in the generator, then tuples, then keyword constructors.
- Tactic: 56, with the `set(list)` commit waiting on its EF readable check. The `hash_tree_root`
  oracle and the shared primitives are done on their branches and wait for merge.

### Day three (2026-10-06 evening to 2026-10-07)

Counts. Tactic: 57 → 58 → 62 → 64 → 65 → 66 → 67 → 69 → 70 → 71. Layer 4: 37 → 43 → 44 → 46 → 48
→ 49 → 52 → 53 → 54 → 56 → 57. The number that matters is the union: a function counts if either
road proves it. For most of the day layer 4 proved nothing the tactic lacked. Its first new ones
were `compute_signing_root` and `update_next_withdrawal_index`, then the two deposit-signature
checks. The union is about 73 of 161. Rule since then: layer 4 prefers functions the tactic lacks.

What we trust, sharpened:

- sha256 joined `hash_tree_root` as an oracle on both sides, with one more fact: every digest is
  32 bytes.
- The plumbing cost is not hashing. The interpreter hands the oracle a heap value, the readable Lean
  a plain value. A generated "same content" lemma for all 71 SSZ classes connects the two. The
  first version took 20 minutes on `BeaconState`. Rewritten as one nested term, it takes 15 s.
- BLS got the same treatment: `OracleBls`, with a lemma that the runner's BLS satisfies it.
- `uint_to_bytes` became a trusted primitive, a one-line spec wrapper around `ssz_serialize`.
- `==` on containers and hashing assume `Shaped`: every container has its class's field count. The
  readable decoders do not check the count. Cleanup later: make them check it and drop the
  assumption.

A flaw in our own contract. `NoNewPaths` said that no old object may gain a path, whatever its
class. The spec appends existing objects to lists:
`state.eth1_data_votes.append(body.eth1_data)`, and two more like it. Python shares the object, so
it gains a path, and these functions were unprovable on both roads, though safe. SPEC 9.4 had
always meant "no object that a function writes may gain a path". The fix scopes the rule to
footprint paths. A check of all 162 footprints showed that no function writes into those shared
classes. So the spec has no sharing hazard. Our rule was just too strict.

A second translator bug that only the proofs found. Python reads
`proposer = state.validators[i]` first, then calls `get_domain`. The translator resolved the alias
lazily and read the validator only at the `return`. If the index is out of range and a callee also
fails, the error class differs from Python. 25 places in 24 functions had this. No EF vector hits
the case. A new hand-built test now does, and it fails on the old code.

Housekeeping that turned out to matter:

- The translator was not deterministic: Python set iteration order changed the output between runs.
  Sorted now; six hash seeds give byte-identical files.
- Hand-written proofs refer to functions by raw numeric ids, so the generated scope file could not
  be regenerated without breaking them. Being replaced by stable symbolic handles.
- A one-command regression script, `tools/regress.sh`.

Agents and the machine:

- The tactic agent stopped receiving messages. It asked the same questions six times, and it never
  saw merges from hours before. It was restarted as a new agent, with every decision and the state
  of master in its first prompt. Nothing committed was lost.
- Agents lost hours waiting for "done" notices that never came. One cause: a `pgrep` wait loop whose
  pattern matched its own command line, so it never ended. Rule now: poll the process and its exit
  code yourself.
- `/home` hit 100% full once: something wrote about 300 GB and deleted it within minutes. The cause
  is unknown. Every background command now caps its output.
- Memory warnings came back several times. The real cause was a full 4 GB swap, plus
  `rust-analyzer` from other Claude sessions (about 10 GB) and Firefox tabs (about 19 GB), not the
  proofs. The Lean jobs stay under hard caps.

Lessons:

- Count the union, not each road. Two roads that prove the same functions are one road.
- A contract can be wrong in the strict direction too. Too strict is as blocking as too weak.
- Order of evaluation is part of the semantics. Lazy translation changed which error came out.
- Generated output must be deterministic, or "regenerate and diff" is not a check.
- An agent that does not read its inbox is worse than no agent. Restart it early.

Why the agents "stopped reading messages" (found 2026-10-07). An agent receives messages only when
it ends its turn. Two agents in long turns, hours of builds and proof runs, got none of the lead's
messages until they went idle, then all at once. One of them was restarted for this, wrongly: it
was not broken, just busy. Rule now: every agent ends its turn after each step, at least every
30 to 45 minutes, and starts long runs in the background.

Strategy change (2026-10-07): progress was as slow as the hardest function, because a caller's
proof uses its callee's theorem, and 22 functions waited on one shuffle function, 31 on one
balance function. Both roads now generate conditional theorems: a caller is proved now, with each
unproved callee's statement as a hypothesis. When the callee is proved later, the caller becomes
fully proved automatically. Two counts from now on, conditional and full, and a ranked list of
the functions that fail even conditionally: the real hard core.

Step 6 groundwork: the Lighthouse proofs use 122 hand-written spec functions. 113 map to
generated ones. Field names and order match exactly. The differences are mechanical: types, an
error-class map, and 29 functions with different parameters. A prototype bridge proves
"hand = readable" for two functions. A generator for the rest is under way.

Lessons:
- An agent can only hear you between turns. Long turns make it deaf.
- If callers wait on callees, you are as slow as your hardest function. Prove callers modulo
  callees.

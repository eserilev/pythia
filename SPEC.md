# consensus-specs-lean: technical spec

Status: draft 6. Nothing is implemented except the step 1 spike. Section 14 lists the changes from
each earlier draft.

## 1. Goal

Turn the Ethereum consensus specs into Lean 4 automatically, with no hand-written Lean model of
the spec. A spec change then needs a regeneration, not a manual Lean edit.

The output has two forms:

- An executable model: a Lean interpreter runs each spec function from its syntax tree, with a
  heap, exactly as Python does.
- Readable Lean definitions that proofs use, with a generated proof per function that the readable
  form equals the interpreter.

Example. The spec function

```python
def decrease_balance(state: BeaconState, index: ValidatorIndex, delta: Gwei) -> None:
    state.balances[index] = 0 if delta > state.balances[index] else state.balances[index] - delta
```

becomes three artifacts: its syntax tree as Lean data, a readable function
`decrease_balance (state : BeaconState) (index : ValidatorIndex) (delta : Gwei) : SpecM BeaconState`,
and a theorem that the readable function equals the interpreter on that syntax tree.

## 2. Trust model

| Layer | What it adds | What we still trust |
|---|---|---|
| 1. Testing | The interpreter and the readable Lean run the EF vectors and match pyspec under differential fuzzing | The translator, on inputs that the tests do not reach |
| 3. Semantics and translation validation | The interpreter defines the meaning of the spec, with a heap (section 7.3). Each readable function is proved equal to the interpreter, on every input heap that meets the write condition | The interpreter and its value rules, the serializer, the oracle, the Lean kernel |
| 4. Verified translator (optional) | One proof about the translator replaces most per-function proofs | The same as layer 3 |

Layer 2 (proofs against hand-written Lean models) is not part of the design, because it needs
manual work at each fork. Step 6 of the plan (section 13) uses it once, to move existing proofs
onto the generated Lean.

The interpreter is the one model of Python that we trust. Section 11 tests it against CPython.

A proof about the readable Lean applies to Python on every run whose input heap meets the write
condition `WTree` of section 9.2. Each validation theorem also proves `NoNewPaths`, and the
composition lemma turns it back into `WTree`. So the condition holds on every state that the state transition reaches from a decoded
state (section 9.4).

## 3. Pinned inputs

- Spec: version 1.7.0b3, upstream commit `889a389f9`. The spec text is used unchanged. The existing
  hand-written model is at v1.7.0-beta.2. Step 6 pins one version for both.
- SSZ library: `eth-ssz-specs` (`pyproject.toml`, `from ssz.uint import …`). Pyspec no longer uses
  remerkleable. Every value rule in section 6 comes from probes against `eth-ssz-specs`.

## 4. Input: the spec as written

### 4.1 Input options

| Option | What the translator reads | Status |
|---|---|---|
| I1, strict subset | A spec rewritten so that every state write uses a full path from a root, with no `for_ops` callbacks | Measured, then dropped. The rewrite is +239 / −183 lines over about 26 functions, and it asks the spec team for a style change that serves one tool. |
| I2, spec as written | The unchanged spec. The translator resolves the alias patterns of section 4.2. | Chosen |

### 4.2 Alias patterns the translator resolves

The readable Lean uses plain values, so the translator maps each read and each write through a
local name to the place it refers to.

1. A local name bound to a path from an argument, then used:
   `validator = state.validators[index]` then `validator.exit_epoch = epoch`. The write goes to
   `state.validators[index]`, with the value that `index` had when `validator` was bound. A read
   through `validator` is a read of that path.
2. A local name bound to one of several paths in different branches:
   `epoch_participation = state.current_epoch_participation` or the previous one. The write
   becomes a conditional write to the chosen path.
3. A loop variable over a list from an argument, directly or through `enumerate`, `zip` or
   `sorted`: `for index, validator in enumerate(state.validators)`. The write goes to the element.
4. The `for_ops` helper: a nested function that only loops over a list and calls a function on
   each element. The translator expands it into plain loops. Gloas `process_operations` uses plain
   loops, so this pattern only matters for earlier forks.
5. A local object that the function creates, by a constructor, `.copy()`, a literal or a
   comprehension. If no argument object is inside it, it is a local value in the readable Lean.
   If a constructor argument comes from an argument path, Python shares objects, in one of two
   ways:
   - A direct field reference shares the field object. `upgrade_to_electra` builds
     `post = BeaconState(balances=pre.balances, ...)`, then writes `post.balances[index]`. That
     write changes `pre.balances`. The translator maps `post.balances` to `pre.balances`.
   - A `data=` argument makes a new list that shares each element. `Validators(data=pre.validators)`
     is a new list, so an append to it does not reach `pre`. A write to one of its elements does.
     The translator maps each element of the new list to the matching element of `pre.validators`.

The translator rejects one more shape: a local object stored into an argument and then written
through the local. No function in Electra, Fulu or Gloas does this.

The validation proof (section 9) checks each resolution. A wrong resolution makes the proof fail,
because the theorem compares every argument, not only the ones the translator expects to change.

### 4.3 The lint

`scripts/check_safe_python.py` (PR #3 on `eserilev/consensus-specs`) accepts the patterns of
section 4.2 and reports these writes: through a helper's return value, a comprehension element
taken from an argument, a conditional expression or a tuple unpack; through an alias whose path
index changes before the write; inside any other nested function; and to a parameter that is not
a root. The unchanged spec passes it.

The lint is a guide for spec authors, not part of the trust story. It matches roots by parameter
name (`state`, `store`, `fcr_store`, `seen`, `block`). It does not see sharing through
constructor arguments or between two places, such as `state.a = c` followed by a write through
`c`. The validation proofs see all of these (section 9.2).

### 4.4 Constructs and scope

The constructs list is generated, not written by hand. A CI script scans every function of the
`SpecObject` with CPython's `ast` module and fails on a node type that the serializer does not
support. The Gloas `SpecObject` has 421 functions. The rendered module has two more, `ceillog2`
and `floorlog2` from `pysetup/constants.py` (section 5.1).

Constructs in use include `raise` (171, mostly gossip validation), `is`/`is not`, `.copy()`,
slices, slice assignment, negative indices, list literals, string constants, f-strings in `raise`
messages, generator expressions, set and dict comprehensions, dict literals, annotated assignment,
starred arguments, `**`, `~` and the other bit operators, `.index`, `.get`, `.items`, `.values`,
`.union`, `.intersection`, `.difference`, `.insert`, `.count`, `bit_length`, `int.from_bytes`,
`any`, `all`, `sum`, `min`, `max`, `filter`, `list`, `tuple`, `ssz_serialize`, `ssz_deserialize` and
`get_generalized_index`. No spec function catches an exception. Section 9.2 depends on this, and
the scan fails on a `try` node.

Scope of version 1: the state transition (`state_transition`, `process_slots`, `process_block`,
`process_epoch` and their callees) and the fork upgrades. In this scope:

- No function calls `.copy()`. All `.copy()` calls are in fork choice, the validator guide, the
  light client and gossip.
- No function raises. The only `raise` is in the built-ins `ceillog2` and `floorlog2`.
- `process_attestation` iterates a set (section 6.3).

Fork choice and gossip validation come later. They need dicts, `.copy()` and `raise` with the
gossip exceptions.

## 5. Pipeline

```
consensus-specs markdown
  -> pyspec build: SpecObject after combine_spec_objects (fork overrides resolved), per preset
  -> CPython ast module
  -> serializer     -> Gen/<fork>/<preset>/Ast.lean         (syntax trees as Lean data)
  -> translator     -> Gen/<fork>/<preset>/Readable.lean    (readable Lean)
                    -> Gen/<fork>/<preset>/Validation.lean  (one theorem per function)
Value.lean, Heap.lean and Interp.lean define the meaning of Ast.lean.
```

All generated files carry a header with the spec commit and the tool version. CI regenerates them
and fails on any difference.

Types cross forks. A class that a fork does not change is the same Python class in both forks:
the Gloas `Validator` is the phase0 `Validator`. After an upgrade, `post` holds objects of
older-fork classes. So:

- The interpreter identifies a nominal type by the class that defines it, not by the build.
- Each Lean type is generated once, in the fork that defines it. Later forks import it.
- The readable Lean of an upgrade imports the types of the previous fork.

### 5.1 Serializer (Python)

Reads the `SpecObject` after `combine_spec_objects` (`pysetup/helpers.py`), not the rendered
module. The rendered module adds code that is not in the markdown: the `cache_this` decorator with
a nested `wrapper`, `get_eth1_data`, `NoopExecutionEngine`, top-level `assert`s, and `ceillog2` and
`floorlog2` from `pysetup/constants.py`. The interpreter implements `ceillog2` and `floorlog2` as
built-ins, including their `ValueError`. The rest become oracle fields or are left out.

- Functions, SSZ container definitions and constants come from the `SpecObject`.
- Presets produce one build each (minimal, mainnet).
- `config` is a runtime value. Tests change it with `with_config_overrides`. So `config` is a
  parameter of the interpreter, not a constant.

Each CPython `ast` node maps to one constructor. Any other node stops the serializer with its
source line. Names are interned to `Nat` indices, so proofs never compare strings.

```lean
inductive Expr where
  | name (id : Nat) | int (n : Int) | bool (b : Bool) | str (s : String) | bytes (b : ByteArray)
  | noneLit
  | fstring (parts : List FPart)                   -- only in raise messages
  | attr (e : Expr) (field : Nat) | index (e : Expr) (i : Expr) | slice (e lo hi step : Option Expr)
  | binop (op : BinOp) (a b : Expr) | unop (op : UnOp) (e : Expr)   -- UnOp includes ~
  | compare (left : Expr) (rest : List (CmpOp × Expr))  -- includes is / is not / in / not in
  | boolop (op : BoolOp) (args : List Expr)
  | call (fn : Expr) (args : List Arg)
  | ifExp (c a b : Expr) | comp (kind : CompKind) (elt : Expr) (gens : List Comprehension)
  | lambda (params : List Nat) (body : Expr)
  | list (es : List Expr) | tuple (es : List Expr) | dict (kvs : List (Expr × Expr))

inductive Arg where
  | pos (e : Expr) | starred (e : Expr) | kw (name : Nat) (e : Expr)

inductive Target where
  | name (id : Nat) | attr (e : Expr) (field : Nat) | index (e : Expr) (i : Expr)
  | slice (e : Expr) (lo hi step : Option Expr) | tuple (ts : List Target)

inductive Stmt where
  | assign (targets : List Target) (value : Expr) | annAssign (t : Target) (value : Expr)
  | augAssign (t : Target) (op : BinOp) (v : Expr) | exprStmt (e : Expr)
  | ifStmt (c : Expr) (thn els : List Stmt) | forStmt (t : Target) (iter : Expr) (body : List Stmt)
  | whileStmt (c : Expr) (body : List Stmt) | ret (e : Option Expr) | assert (e : Expr)
  | raise (e : Option Expr) | brk | cont | pass
  | funDef (name : Nat) (params : List Nat) (body : List Stmt)    -- nested, for for_ops
```

Every node keeps its source line, so errors and proofs point at the spec.

## 6. Values

### 6.1 The value type

```lean
inductive Value where
  | int (n : Int)                                  -- Python int, unbounded, can be negative
  | bool (b : Bool)                                -- Python bool
  | float (x : Float)                              -- only from `/`; see 6.2
  | str (s : String)                               -- ENDIANNESS, raise messages
  | uint (ty : UintType) (n : Nat)                 -- nominal: Slot, Epoch, Gwei, Uint64, Uint8 ...
  | boolean (b : Bool)                             -- SSZ Boolean, nominal
  | bytes (ty : Option BytesType) (b : ByteArray)  -- Bytes32, Root, BLSPubkey ...; none = Python bytes
  | none
  | ref (addr : Addr)                              -- a list, container, dict or set in the heap
  | tuple (xs : Array Value)

structure UintType where
  name : String      -- the defining class: "Slot", "Epoch", "Gwei", "Uint64" ...
  bits : Nat

inductive HeapObject where
  | list (kind : ListKind) (xs : Array Value)
  | container (ty : ContainerType) (fields : Array Value)
  | dict (entries : Array (Value × Value))          -- insertion order
  | set (elems : Array Value)                       -- an order fixed by the interpreter; see 6.3
```

Integers, booleans, strings, bytes and tuples are immutable values. Lists, containers, dicts and
sets live in the heap, and a `Value.ref` points to them, as in Python. A constructor call,
`.copy()`, a literal or a comprehension allocates a new heap object. `.copy()` is deep: the copy
shares no object with the original. `.copy()` of a Python list is shallow: the new list shares
its elements.

`ListKind` covers the SSZ kinds `List`, `Vector`, `Bitlist`, `Bitvector`, `ProgressiveList` and
`ProgressiveBitList`, each with its element type and limit, and the plain Python list `pyList`,
with no element type and no limit. `selected: list[ValidatorIndex] = []`, list literals and
comprehensions give a `pyList`. A `ProgressiveList` has no limit: in Gloas, `Balances` and
`Validators` are progressive, so `append` never raises for them. `ContainerType` covers plain and
progressive containers (`active_fields`).

A `ByteList[N]` is a `List` of `Uint8` with limit `N`, so `hash_tree_root` and the readable Lean
see the same object. Python stores its data in a `bytearray`, so the interpreter reads each element
as an `int` and gives `bytes` for a slice (see 6.2). The spec has no other list of `Uint8`, and
the serializer rejects one.

### 6.2 Value rules

Each row comes from a probe against `eth-ssz-specs` in the pyspec environment. CI keeps these
probes as tests, so a library change shows up as a failing test.

| Operation | Result |
|---|---|
| `Slot + Epoch`, `Slot == Epoch`, `Uint8 + Uint64`, `max(Slot, Epoch)` | `TypeError` (nominal types) |
| `Gwei + Uint64`, `Uint64 + Gwei` | `Gwei` |
| `Slot == int` | compares the numbers |
| `Uint64 == None`, `Uint64 == True`, `Uint64 == "a"`, `Uint64 + True` | `TypeError`: a Python `bool` is not accepted as an `int`, and `==` with another type does not return `False` |
| `Slot(1) in [Epoch(1)]` | `TypeError`: `in` uses `==` |
| `Slot(1) in {Epoch(1)}` | `TypeError` only when the hashes are equal; see 6.3 |
| `Uint64(2) + (-1)` | `Uint64(1)`: a negative `int` operand is legal |
| uint result outside `[0, 2^bits)` | raises `SSZValueError` |
| `-Uint64(1)` | `int` `-1` |
| `Uint64(5) / Uint64(2)` | `float` `2.5` |
| `sum([])`, `len`, `range`, `enumerate` index | `int` |
| `min(Uint64(5), 3)` | `int` `3`: the result keeps the type of the chosen argument |
| `min(Uint64(3), 3)` | `Uint64(3)`: on a tie, the first argument |
| `max([])` | `ValueError` |
| `//` or `%` by zero | `ZeroDivisionError` |
| `validator.slashed == True`, `Boolean + 1` | `TypeError` |
| `Bytes32[0:4]`, `Bytes32 + bytes` | Python `bytes` |
| `Bytes32[0]` | `int` |
| `Root == Bytes32`, `Root == b'…'` | compares the bytes |
| `Root == BLSPubkey` | `False`, no error |
| Container field write of an `int` or a base `Uint64` into a uint field | coerced to the field type; out of range raises `ValidationError` |
| Container field write of a subclass of the field type (`Slot` into a `Uint64` field) | keeps the subclass |
| Container field write of a Python `list` or `tuple` into an SSZ list field | pydantic `ValidationError` |
| `Vector(data=…)` or `List(data=…)` with the wrong length or over the limit | pydantic `ValidationError` |
| `True == Gwei(0)`, `True + Uint64(1)` (Python `bool` on the left) | int rules: `False`, `int` `2` |
| Container field write of `True` into a uint field | pydantic `ValidationError` |
| Container field write of `True` or `False` into a `Boolean` field | coerced to `Boolean` |
| Container field write of `0`, `1` or a float into a `Boolean` field | pydantic `ValidationError` |
| Container field write of bytes of the wrong length or type | pydantic `ValidationError` |
| Container constructor with positional arguments | `TypeError` (keyword arguments only) |
| List element write of an `int` or a base `Uint64` | coerced to the element type |
| List element write of a sibling nominal type (`Slot` into `Balances`) | `SSZTypeError` |
| `append` on a full `List[T, N]` | raises `SSZValueError` |
| Index out of range, including negative indices past the start | `IndexError` |
| `.index(x)` with `x` absent | `ValueError` |
| `ByteList[0]`, `for x in ByteList` | `int` |
| `ByteList[0:2]`, `ByteList + x`, `x + ByteList` | Python `bytes`: the data plus `bytes(x)` |
| `ByteList == x` where `x` is not a `ByteList` | `TypeError`; an SSZ object on the left gives `False` |
| Element write of a number, `bool` or `Boolean` into a `ByteList` | kept when in `range(256)`, else `ValueError` |

The `uint` arithmetic rule depends on both operand types. The library resolves the result type
with one rule (`_resolve_type`): if one operand type derives from the other, the derived type
wins, and otherwise the operation raises `TypeError`. The interpreter implements that rule. The
spike checks it against 596 probe rows.

### 6.3 Sets and dicts

CPython iterates a set in hash order, not in insertion order. For `Root` values the order depends
on `PYTHONHASHSEED`. So no fixed order matches pyspec. The interpreter uses an order of its own.
The rule: a set is only iterated through `sorted`, or in a place where the result does not depend
on the order. For the second form, the validation theorem carries an order-independence
obligation. The obligation also covers the error class of section 6.4.

This is in the version 1 scope: Gloas `process_attestation` iterates the set from
`get_attesting_indices` directly. Dicts keep insertion order, as Python does.

### 6.4 Errors

The interpreter has two error results and a separate `outOfFuel`:

- `invalid`: `AssertionError` or `IndexError`. The EF test harness (`expect_assertion_error` in
  `test/context.py`) accepts only these two classes for an invalid case. So every invalid EF
  vector ends in `invalid`.
- `bug`: every other exception. A `bug` result means that the spec itself has an error, for example
  an overflow or a `TypeError`. Pyspec treats it like an invalid block.

The readable Lean uses `SpecM := Except Fail`, with `Fail := invalid | bug`. The validation theorem
compares the class. So "no reachable input gives `bug`" becomes a theorem that can be proved about
the readable Lean. For the EF vectors and for the `SameOk` theorems of the Lighthouse proofs,
"error against ok" is enough.

The interpreter also records the Python exception class next to each error, for diagnostics in
fuzzing (section 11):

| Python exception | Class | Diagnostic |
|---|---|---|
| `AssertionError` | `invalid` | `assertionFailed` |
| `IndexError` | `invalid` | `indexError` |
| `SSZValueError` | `bug` | `sszValue` |
| pydantic `ValidationError` | `bug` | `validation` |
| `ValueError` | `bug` | `valueError` |
| `ZeroDivisionError` | `bug` | `divisionByZero` |
| `TypeError`, including its subclass `SSZTypeError` | `bug` | `typeError` |
| `KeyError` | `bug` | `keyError` |
| `GossipIgnore`, `GossipReject` (later scope) | later | `gossipIgnore`, `gossipReject` |

## 7. Interpreter

### 7.1 State and calls

```lean
def interp (fuel : Nat) (env : Env) (fn : FnId) (args : List Value) (heap : Heap) :
    Result (Value × Heap)        -- ok, invalid, bug (with a diagnostic), or outOfFuel
```

- The heap maps addresses to `HeapObject`s. A local name holds a `Value`, which can be a `ref`.
- `Env` holds constants and presets of one build, `config`, the other functions, and the oracle.
- A call passes its arguments as values. A `ref` argument lets the callee change the object, as in
  Python. The result heap carries every change.
- A new object gets an address that is not in the heap.

### 7.2 Evaluation order

Probes against CPython fixed these rules:

- Expressions evaluate left to right. A dict literal evaluates key 1, value 1, key 2, value 2, and
  so on.
- `and` and `or` short-circuit. A chained comparison stops at the first false comparison.
- Plain assignment `obj[idx] = rhs` evaluates `rhs`, then `obj`, then `idx`, then writes.
- Augmented assignment `obj[idx] += rhs` evaluates `obj`, then `idx`, then reads `obj[idx]`, then
  evaluates `rhs`, then writes.

### 7.3 Memory model

Python names refer to objects. A write through one name is visible through every other name that
refers to the same object. The readable Lean uses plain values, as proofs need. Three models were
considered.

| Version | References | Faithful to Python | Status |
|---|---|---|---|
| V0, value semantics | Every name holds a copy | No | Rejected |
| V1, path references | A path from a root, such as `state.validators[3]` | No | Rejected |
| V2, full heap | An address in a heap | Yes | Chosen |

**V0** silently disagrees with Python. Python returns `True` here, and V0 returns `False`:

```python
v = state.validators[0]
state.validators[0].slashed = True
return v.slashed
```

A readable Lean that also copies returns `False` too. The two agree on the wrong answer, so a
validation proof passes. V0 is unsound.

**V1** stores a path instead of an address. Review of draft 3 found three failures:

- A rebound path prefix. `v = state.validators[0]`, then `state.validators[0] = Validator()`, then
  `v.slashed = True`. Python changes the old object. V1 follows the path again and changes the new
  one. No object is shared, so no sharing check can catch this.
- Sharing that real code creates (section 9.4 lists it). `upgrade_to_electra` shares `balances`
  and `validators` between `pre` and `post`, then writes through `post`. V1 has to either copy,
  which is wrong when something changes the shared object, or stop, which stops correct code.
- Objects that a function creates. `post = BeaconState(...)` and `a = Checkpoint(); b = a;
  b.epoch = 5` have no root path.

Each fix to V1 (invalidating references, tracking shared pairs across calls, dynamic roots) brings
back the reasoning of V2 in a less direct form.

**V2** models Python exactly. The heap maps addresses to objects. Assignment copies a `ref`, not
the object, so sharing works as in Python. The interpreter never stops on correct code, and
differential fuzzing compares it with CPython directly.

The cost moves into the proofs: the readable Lean uses values, so each validation theorem needs a
write condition (section 9.2). Paths are still useful, as a proof technique: inside a proof,
"the local `validator` refers to the object at `state.validators[i]`" is a lemma about the heap.

### 7.4 Loops and fuel

- `for` over a list iterates live, as Python does for SSZ lists: appending inside the loop extends
  the iteration. At loop entry, the interpreter evaluates the iterable once and keeps the `ref`.
  At each step it reads the length of that object again. If the body replaces the field that the
  iterable came from, the loop continues over the old object, as Python does. The loop variable
  gets the element value. For a list of objects, that value is a `ref`, so a write through the
  loop variable changes the element.
- `for` over `enumerate` and `zip` is live in the same way. `sorted` and slices take a snapshot.
- A list comprehension iterates live, like a `for` loop.
- A generator expression is lazy. `any` and `all` stop at the first result that decides them, so
  later items are never evaluated. A snapshot is wrong when an item has a side effect.
- Each call, each `while` iteration and each `for` iteration costs one unit of fuel. Running out
  of fuel gives `outOfFuel`, never a silent stop. So the fuel that a run needs grows with the
  length of the lists it loops over, and `N` in section 9.2 depends on the input.

## 8. Oracle

- `sha256` and BLS (`Verify`, `FastAggregateVerify`, `AggregateVerify`, `AggregatePKs`,
  `KeyValidate`, and the G1 operations of the sync aggregate) are oracle fields.
- `EXECUTION_ENGINE` calls, KZG calls and builder stubs such as `NoopExecutionEngine` are oracle
  fields.
- SSZ `hash_tree_root` is implemented in Lean on top of `sha256`, including progressive lists,
  progressive containers and progressive bitlists (EIP-7916, EIP-7495).

`hash_tree_root` needs a hash cache, or state roots on mainnet-preset vectors are too slow. The
cache is not part of the semantic heap. With sharing, one object can have two parents, so a cache
that invalidates upward through one parent is wrong. Writes to a cache in the heap also break the
frame lemmas. The proofs see a plain recursive `hash_tree_root`. The executable version is a
separate memoized function, linked with `@[implemented_by]` and tested against the plain one.

For EF vectors, BLS follows `meta.yaml`:

- `bls_setting: 1` needs real BLS. The oracle calls `blst` through FFI.
- `bls_setting: 0` or `2` uses a stub that accepts every signature, as pyspec does with
  `bls.bls_active = False` and `only_with_bls(alt_return=True)`.

## 9. Translator and translation validation

### 9.1 Translator (Python)

Emits readable Lean in the style of the existing hand-written model:

- Typed structures for SSZ containers. Each nominal uint type and `Boolean` is its own Lean type.
- `SpecM := Except Fail` (section 6.4), with state passing: a function returns every argument it
  can change.
- Each read and write through a local name is mapped to the argument path it refers to, by the
  patterns of section 4.2.
- Early returns become `if … then pure … else`, not `return` inside `do`. This avoids the
  do-notation shape that copies the rest of a function into each branch.
- Each `for` loop becomes a named local function that loops by index, as well-founded recursion on
  `len - i`.
- Simp lemmas proved by `rfl` over checked operations caused kernel timeouts in the spike. Checked
  operations are `@[irreducible]`, with `*_eq` lemmas.
- Each `while` loop becomes well-founded recursion on an explicit measure, never on fuel. The
  measures in the version 1 scope:
  - `integer_squareroot`: `x`, which gets smaller at each step.
  - `process_slots`: `slot - state.slot`. This needs the frame of section 9.2 for the callees.
  - `compute_balance_weighted_selection`, and in Electra and Fulu `compute_proposer_index` and
    `get_next_sync_committee_indices`: `2^64 - i` for the `Uint64` counter `i`. The interpreter
    raises an overflow at `2^64`. Only `sha256` outputs end these loops otherwise. The measure is
    valid only if `i += 1` is reached on every path through the body, with no `continue` before
    it. The translator checks this.

  When the translator cannot find a measure, it reads one from a checked-in annotation file.
- Python doc comments are kept, with the source quoted.

### 9.2 Encoding, the write condition and the validation theorem

`decode (heap : Heap) (v : Value) : Option α` reads the typed Lean value of `v` out of the heap,
following `ref`s. The translator generates `decode` for each SSZ type. Two refs to one object
decode to equal values, so sharing is invisible to `decode`. A decoder checks that each uint is in
the range of its class and each byte vector has the length of its class. Python's types
guarantee this, and the proofs need it: a container that Python builds checks the range of
each field, and the readable Lean does not. `DecodesArgs` includes `HeapWF`:
every `ref` reachable from the arguments points to an address in the heap.

**Footprints.** A footprint is a set of path patterns rooted at SSZ types, such as
`BeaconState.validators[*]` or `BeaconState.balances`. A pattern applies to every root of its type.
A footprint names objects that are changed in place:

- a container whose field is set (`validator.exit_epoch = e` puts `BeaconState.validators[*]` in
  it);
- a list whose element is set, that gets an append, or that gets a slice assignment.

Rebinding a field puts the container that holds the field in the footprint, not the old or new
object in the field. So `state.previous_justified_checkpoint = …` puts `BeaconState` in the
footprint, not `Checkpoint`.

There are two footprints:

- `Footprint f`: what `f` changes in place, directly or through its callees.
- `FP`: one global footprint, the union of `Footprint f` over the whole version 1 scope. The
  translator computes it once.

A checked lemma states which types are outside `FP`: no function in scope changes a `Checkpoint`,
an `ExecutionPayloadBid`, an `Eth1Data` or a `SyncCommittee` in place, or the inner vectors of
`ptc_window`. This lemma is what makes the sharing of section 9.4 safe.

**Write condition.** `WTree heap roots FP` is a condition on a heap: every object at an `FP`
path from `roots` is reachable from `roots` by exactly one heap path. Paths count through every
root and every field. Sharing of objects outside `FP` is free. Aliases that `f` creates through
locals while it runs (section 4.2) are the job of the proof itself.

**Theorem.** For each function `f`, the translator emits:

```lean
theorem f_valid : ∀ heap vs args, DecodesArgs heap vs args → WTree heap vs (Footprint f) →
    ∃ N, ∀ fuel ≥ N, ResultMatches f heap vs (interp fuel env f vs heap) (f' args)
```

`ResultMatches f heap vs r r'` holds when one of these is true:

- `r` is `ok (v, heap')`, `r'` is `ok (v', args')`, and:
  - `v` decodes to `v'` in `heap'`, and each argument in `vs` decodes to its value in `args'` in
    `heap'`. This compares every argument, not only those in the footprint. So a translator that
    treats `post` in `upgrade_to_electra` as a new object fails the proof, because `pre` changes
    too.
  - Frame: every object in `heap` that is not at a `Footprint f` path from `vs` has the same
    contents in `heap'`. So a container outside the footprint keeps its pointers, and a callee
    cannot swap an object for an equal copy.
  - Fresh addresses: `heap.next ≤ heap'.next`, and `HeapWF heap → HeapWF heap'`, where `HeapWF`
    says that every address at or above `next` is free. ("Every new address was free" is always
    true, so it says nothing.)
  - NoNewPaths over the global footprint `FP`: no old object gains a path. For each argument,
    a map `φ` sends each path of `heap'` to an old object (below `heap.next`) to a path of
    `heap` to the same object. The map is one to one, and a path that matches a pattern of `FP`
    goes to a path that matches the same pattern. So an old object has at most as many paths
    after the run as before. New objects are free here: `FreshOnce` covers them.

    An earlier rule, `Reach`, kept each path fixed: every `ref` at a path of `heap'` was at the
    same path in `heap`, or was fresh. That is false for a list slice or a pop, which moves old
    items to new positions: `state.pending_partial_withdrawals = ...[n:]` in
    `update_pending_partial_withdrawals`, and the same in `update_builder_pending_withdrawals`.
    `NoNewPaths` allows a move, because the map sends position `j` to position `j + n`. It needs
    the patterns of `FP` to address list items only by `*`. `Reach` implies `NoNewPaths` with `φ`
    the identity (`noNewPaths_of_reach`), so a function that moves nothing still proves `Reach`.
    `NoNewPaths_trans` chains it over loop steps and calls.

`f_valid` takes `WTree` over `Footprint f` only, and promises no `WTree` on its result. The
composition lemma `wtree_compose` (`SpecLean/Compose.lean`) gives `WTree` back over any
footprint: `WTree` before, `NoNewPaths`, each new object reached by one path (`FreshOnce`) and the
roots keeping their class give `WTree` after. So `WTree` over `FP` at the entry of
`state_transition` gives it at the exit.
- `r` is `invalid` and `r'` is `error invalid`, or `r` is `bug _` and `r'` is `error bug`.

`outOfFuel` never matches. On an error, the readable Lean drops every argument, and Python's
partial writes to the heap are lost with them. This is sound because no spec function catches an
exception (section 4.4): an error always ends the whole state transition. The fork-choice runner
continues after an invalid step with the store as Python left it, so the later fork-choice scope
needs a different error rule.

Why the frame matters, with three cases from the spec:

- `process_attestation` binds `payment = state.builder_pending_payments[payment_index]`, calls
  `set_epoch_participation_flags` and `increase_balance`, writes `.weight` through the path, then
  stores `payment` back. The proof needs the callees to leave that element as the same object.
- `upgrade_to_electra` calls `queue_excess_active_balance(post, i)`, and `post` shares objects with
  `pre`. The proof needs the frame to derive the new value of `pre`.
- `process_block`, after `process_execution_payload_bid`, shares the bid between `state` and
  `block`. The later calls get `state`. The proof needs the frame to show that `block` decodes
  unchanged.

**Entry points.** An upgrade breaks `WTree` over `[pre, post]`: `upgrade_to_electra` writes into
`balances`, which `pre` and `post` share, and `upgrade_to_gloas` shares validators and
`latest_block_header`. No spec function calls an upgrade. The test harness calls them, with a copy
of the pre-state (`test/helpers/fork_transition.py`, `test/helpers/<fork>/fork.py`). So upgrades
are entry points, with a second theorem form: `WTree heap' [v] FP` over the result only, from
`wtree_compose` with `post` as the only root. The entry points are the upgrade functions.

**Fuel.** `N` depends on the input, because `while` loops have no fixed bound and `for` loops
cost fuel per iteration (section 7.4). A general lemma, `interp_fuel_mono`, states that more fuel
does not change a result that is not `outOfFuel`. It needs the premise that no construct catches
an error, which the serializer enforces.

**Calls.** A call to `g` inside `f` uses `g_valid`. The caller needs `WTree heap vs_g
(Footprint g)` at the call. It gets it from its own `WTree` at entry, from the frame and `NoNewPaths`
of earlier calls through `wtree_compose`, and from a lemma that the statements between them
create no second path to any object that `g` writes. The tactic proves that lemma per call site. Some sharing exists at a call site, but
only of objects outside `FP`: `compute_ptc` runs while inner `ptc_window` vectors are shared, and
`get_next_sync_committee` runs while the sync committees are shared.

### 9.3 Proof method

Unfolding `interp` naively does not scale. The proofs use generic lemmas, proved once:

- `interp_seq`: a statement list is the composition of its statements.
- `interp_for`: a `for` loop over a list is an index loop over the `ref` from loop entry, which
  reads the length at each step.
- `interp_while`: a `while` loop that ends within the fuel equals the well-founded recursion of
  the readable Lean.
- Frame lemmas: a write to an object with one path changes the decoded value only at that path.
- Allocation lemmas: a new object has no path from any earlier value.
- `WTree` lemmas: dropping a root keeps `WTree`, and adding a root that was just decoded and shares
  nothing keeps `WTree`. `WTree_skel`: a write that keeps the shape of the object keeps `WTree`.
  Loop invariants carry `WTree` on the current heap, and each step proves it again with this lemma.
- Loop termination: each readable index loop is well-founded recursion on `len - i`. It needs a
  lemma that the body keeps the length. One generic tactic proves it for bodies that do not append.
  A loop whose body appends needs a measure from the annotation file.
- Calls: as in section 9.2. A function without loops has a fixed fuel bound `N`, so the generator
  states a `f_run` theorem at fuel `k + N` for every `k`, and `f_valid` follows from it. The
  tactic does not unfold a call of a spec function: it stops at the call (`callStop`) and
  applies the `_run` theorem of the callee. A caller's bound is 64 more than the largest bound
  of its callees.

A custom tactic applies these lemmas in the order of the function's statements. Names are `Nat`
indices, and the heap is a finite map with decidable lookups, so the kernel does not reduce
strings or large arrays.

### 9.4 Real states meet the write condition

Each `f_valid` proves `NoNewPaths` on its result heap, and `wtree_compose` turns it into `WTree`. So
by induction over the state transition, every reachable state meets `WTree` if the start state
does:

- The start state. A state decoded from SSZ bytes shares nothing, so it meets `WTree`.
- Each new block. A block decoded from SSZ bytes shares nothing, so adding it as a root keeps
  `WTree` (section 9.3).
- The upgrades. The entry-point theorem gives `WTree` for `post`. The old state is dropped as a
  root, which keeps `WTree`.

Sharing that lasts across calls, and that `WTree` allows because the objects are outside `FP`:

- After an epoch that is not justified, `previous_justified_checkpoint` and
  `current_justified_checkpoint` are one object. `finalized_checkpoint` can also share with them.
- `latest_execution_payload_bid` is shared with the block.
- `eth1_data` and the entries of `eth1_data_votes` are shared with the block body.

Sharing inside one function, also outside `FP`:

- the participation lists, during the rotation;
- the sync committees, during the rotation;
- elements of `builder_pending_payments`, between the two slice assignments;
- the inner vectors of `ptc_window`, which `get_ptc` also returns as a `ref`;
- withdrawal objects in `builder_pending_withdrawals` and `builder_pending_payments`.

Step 3 adds a dynamic check to the interpreter. It uses `FP`, so `FP` is computed in step 3:

- At each in-place write, it counts the heap paths to the written object from all live roots: the
  arguments and the locals of every frame on the stack.
- At each call entry, it checks `WTree` only over the objects at `Footprint g` paths from the
  call's arguments: the objects that the callee writes.
- At each call exit, it checks `Reach`: every object that the arguments or the return value reach
  was reachable from the arguments before the call, or is fresh.
- At entry and exit of each top-level call, it checks `WTree` over `FP` from the top-level
  arguments.

The first EF run checked `WTree` over all of `FP` from each call's arguments. It reported 36 false
hits. Many spec helpers take `state` and a part of it, such as `is_eligible_for_activation(state,
validator)`, and `set_or_append_list` returns with the new validator in the list and in its
argument. Neither callee writes the shared object. With the narrower rule, the minimal preset gives 0 hits
(678 of 681 cases pass; the other 3 need real BLS). No vector writes to a shared object, so the
per-write check is still untested on a real hazard. The fuzzer covers that case.

The proof contract in section 9.2 now has the same rule: `f_valid` takes `WTree` over
`Footprint f`, `ResultMatches` keeps Frame, Fresh and NoNewPaths, and `wtree_compose` gives `WTree`
over `FP` at the exit of `state_transition`.

Run on all EF vectors, it shows whether `WTree` holds in practice, before any proof exists. The
`upgrade_to_electra` case shows up at the write through `post.balances`, because `post` is a live
root.

## 10. Layer 4 (optional): a verified translator

An idea for later.

Write the translator in Lean, as a function from `FunctionDef` to a shallow Lean term (a
denotation), and prove once that the denotation equals `interp` under `WTree`. Generating Lean
syntax and reasoning about the elaborator is not realistic, so the translator builds terms
directly.

What it gains: the semantic part of each per-function proof goes away. Each named readable
definition still needs a short proof that it equals the denotation of its syntax tree. That proof
is mostly by `rfl`, but it can still be slow on large functions.

Translation validation (section 9) already gives the same guarantee for each function that we
translate. So layer 4 matters only if the per-function proofs become slow or fragile.

## 11. Validation of the interpreter

The interpreter defines the meaning of the spec, so it gets the heaviest tests.

1. EF vectors. A Python harness decodes the vectors into a simple binary format. The compiled
   interpreter runs them per fork and preset, with the dynamic `WTree` check on:
   - operations, epoch processing, sanity, finality and fork: `pre.ssz_snappy`, the input
     object, and `post.ssz_snappy` (no `post` for an invalid case); sanity blocks are
     `blocks_N.ssz_snappy`, with `blocks_count` in `meta.yaml`.
   - `ssz_static`: `serialized.ssz_snappy`, `value.yaml` and `roots.yaml`. These test the decoder
     and `hash_tree_root`, not the interpreter.
2. Differential fuzzing against CPython. Hypothesis generates random programs inside the
   supported constructs, with random typed inputs and with deliberate aliasing: shared objects,
   rebound path prefixes, constructor arguments taken from other objects, references passed to
   callees, and appends inside loops. CPython with `eth-ssz-specs` and the Lean interpreter run
   them. Results, the changed objects and the exception class must match. The generator also
   focuses on `2^64 - 1`, negative `int` operands, Python `bool` mixed with uints, mixed nominal
   types, bytes slices, empty lists, lists at their limit, exceptions in nested calls, and
   evaluation order. It does not compare programs whose result depends on set order.
3. Spec-level fuzzing. Random states and blocks, built with pyspec's test helpers, go through
   pyspec and through the interpreter. Post-state roots must match.
4. Mutation testing. Small deliberate changes to the interpreter, such as dropping an overflow
   check, swapping evaluation order, or copying on assignment, must each make a test in steps 1 to
   3 fail.

## 12. Risks and open questions

- Proof performance. Symbolic execution of `interp` on large functions, such as
  `process_epoch` callees, can be slow. Calls through `g_valid` keep each proof local.
- The per-call `WTree` lemma (section 9.2). If the dynamic check finds in-place writes to shared
  objects outside the upgrades, the write condition has to change.
- Sets. `process_attestation` needs an order-independence proof in version 1.
- Interpreter speed on mainnet. With a 30-minute limit per case, 7 mainnet cases time out:
  `finality` (all 5), `sanity/blocks/builder_payment_after_missed_epochs` and
  `sanity/slots/historical_accumulator`. Heap lists are
  Lean `List`s, so an index into `randao_mixes` (65536 entries) walks the list. Every uint
  operation also computes `2 ^ bits` again. Minimal runs in about 1 minute on 16 cores.
- Fork choice. `store` holds dicts keyed by roots, and `store.blocks` and `store.block_states`
  share objects. The runner also continues after an invalid step. The first version covers the
  state transition only.

## 13. Plan

| Step | Content |
|---|---|
| 1 | Spike: `Value`, the V2 heap and a minimal interpreter. Validate three functions by hand, in their original alias form: `decrease_balance`, `process_effective_balance_updates` (`for` with an alias write), and `integer_squareroot` or `compute_balance_weighted_selection` (`while`). Fix the syntax tree, value, heap, `decode`, `WTree`, the `FP` pattern form, `ResultMatches` and the entry-point theorem form. |
| 2 | Full interpreter for the version 1 scope, value-rule probe tests, and the constructs scan in CI |
| 3 | Serializer from the `SpecObject`, and `FP` computed from it. The interpreter runs the Gloas EF vectors, with `hash_tree_root`, the BLS oracle and the dynamic `WTree` check |
| 4 | Differential fuzzing, spec-level fuzzing and mutation testing of the interpreter |
| 5 | Translator to readable Lean, `decode` instances, loop measures, generic lemmas, the validation tactic, the entry-point theorems for the upgrades and the `WTree` induction of section 9.4 |
| 6 | One-time migration: pin one spec version, prove the existing hand-written epoch `Spec/` equal to the generated Lean, instantiate its `hash_tree_root_*` oracle fields with the Lean implementation, then move the Lighthouse proofs onto the generated Lean |
| 7 | Layer 4, if steps 1 to 6 show a need |

## 14. Changes

### Draft 2 (review of draft 1)

| Finding | Change |
|---|---|
| Pyspec uses `eth-ssz-specs`, not remerkleable; nominal uint types | Sections 3, 6.1, 6.2 |
| Set iteration is hash order | Section 6.3 |
| Constructs list incomplete | Generated by a CI scan (4.4) |
| Value rule errors (negatives, float, `min`, coercion, progressive lists, exceptions) | Sections 6.2, 6.4 |
| Serializer read the rendered module | Reads the `SpecObject`; per-preset builds; `config` as a parameter (5.1) |
| BLS stub wrong for `bls_setting: 1` | Real BLS through FFI (8) |
| Progressive `hash_tree_root` and caching | Section 8 |
| Augmented assignment order | Section 7.2 |
| Layer 4 overstated | Section 10 |
| Vector formats | Section 11 |

### Draft 3

The spec is read as written (I2); the translator resolves alias patterns; the lint only flags
patterns outside them. Draft 3 chose V1, path references.

### Draft 4 (review of draft 3)

| Finding | Change |
|---|---|
| V1 is unsound: rebound path prefixes, real sharing, objects a function creates | V2 chosen; V0 and V1 recorded with their failures (7.3) |
| `for` over SSZ lists iterates live | Index loop that reads the length at each step (7.4) |
| A single fuel bound cannot cover input-dependent `while` loops | `∀ inputs, ∃ N, ∀ fuel ≥ N` (9.2) |
| `ref` arguments make the validation theorem false | Aliasing condition; `ResultMatches` covers changed and returned refs (9.2) |
| Real states share objects | Sharing allowed if never written in place; invariant in 9.4 |
| The lint accepts a fifth pattern and loop variables over `zip` and `sorted` | Section 4.2 pattern 5 and pattern 3; section 4.3 corrected |
| pydantic `ValidationError`, `SSZTypeError` | Section 6.4 |
| Path steps hold index values, not expressions | Section 4.2 pattern 1 |
| Stale cross-references and changelog rows | Sections 2 and 14 |

### Draft 5 (review of draft 4)

| Finding | Change |
|---|---|
| The aliasing condition counted paths only from the arguments, so `upgrade_to_electra` (`post` shares `pre.balances`) passed it while the readable Lean left `pre` unchanged | `ResultMatches` compares every argument; pattern 5 maps constructor arguments to argument paths (4.2, 9.2) |
| `ResultMatches` was too weak to compose calls | Frame, fresh addresses and `WTree` on the result (9.2) |
| The aliasing condition had three different definitions | One static condition `WTree` on the input heap, plus a per-call lemma (9.2) |
| Fuel in the readable `while` loops breaks the theorem | Well-founded recursion on an explicit measure (9.1); `interp_fuel_mono` premise (9.2) |
| Wrong sharing examples; sharing that lasts across states | Checkpoints, payload bid, upgrades (7.3, 9.4); dynamic `WTree` check in step 3 |
| Missing values: `Boolean`, `str`, Python `bytes`, Python lists | Section 6.1 |
| Error mapping incomplete (`ValueError`, `ValidationError` causes) | Only error against ok; kinds are diagnostics (6.4) |
| Missing syntax: list, `str` and `bool` literals, f-strings, starred, `~`, slice assignment, nested `def`; `Target` and `Arg` undefined | Section 5.1 |
| A hash cache in the heap is wrong with sharing | Cache outside the semantic heap (8) |
| Augmented assignment reads `obj[idx]` before `rhs`; which object a live loop holds | Sections 7.2, 7.4 |
| Missing value and coercion rows | Section 6.2 |
| The count of 423 functions comes from the rendered module; `.copy()` is in the version 1 scope; partial writes on error | Sections 4.4, 5.1, 9.2 |
| Spike: the uint result type follows one library rule, not a table | Section 6.2 |
| Spike: `for` iterations must cost fuel once loops are live | Sections 7.4, 9.2 |

### Draft 6 (review of draft 5)

| Finding | Change |
|---|---|
| `WTree` on the result over "the union of footprints" was false: `get_current_epoch` has an empty footprint, so it accepts a heap with shared participation lists, which the union forbids. Per-function footprints indexed by argument position cannot be joined | One global `FP` of type-rooted path patterns, both before and after every function (9.2) |
| The frame was too weak: a callee could swap an object for an equal copy, so `process_attestation`, `upgrade_to_electra` and `process_block` could not be proved | Frame: every object not at a `Footprint f` path keeps its contents (9.2) |
| Upgrades break `WTree` over `[pre, post]`, and no spec function calls them | Entry-point theorem form; `WTree` lemmas for dropping and adding roots (9.2, 9.3, 9.4) |
| The dynamic check counted paths from the top-level arguments only, so it missed `upgrade_to_electra`; it ran only at writes | Count from all live roots; also check at call entry, call exit and returned values (9.4) |
| Footprint granularity undefined; a rebound field in the footprint breaks the induction on shared checkpoints | A footprint names objects changed in place; a checked lemma lists the types outside `FP` (9.2) |
| `X(data=…)` shares elements, not the list | Pattern 5 split into field-level and element-wise sharing; one shape rejected (4.2) |
| `Boolean` coercion row wrong | Section 6.2 |
| `.copy()` is not in the version 1 scope; the counts 423 and 173 include the built-ins | Section 4.4 |
| More lasting and transient sharing; `get_ptc` returns a shared `ref` | Section 9.4 |
| Unchanged classes are shared between forks | Type identity follows the defining class (5, 6.1) |
| Spec bugs and invalid blocks were both "error" | `invalid` against `bug` (6.4) |
| The `Uint64` counter measure needs `i += 1` on every path | Section 9.1; all in-scope `while` measures listed |
| Gloas `compute_proposer_indices` has no `while` loop | Plan step 1 names `compute_balance_weighted_selection` |
| Plan order: the dynamic check needs `FP` before step 5; the upgrade form is needed by step 5 | `FP` form fixed in step 1, computed in step 3; old step 7 folded into step 5 |
| `DecodesArgs` lacked `HeapWF`; set iteration is in version 1 scope; fuzzer and set order | Sections 9.2, 6.3, 11 |
| Spike: frames do not chain without a reach fact; the fresh-address clause was always true | Section 9.2 |
| Spike: loops carry `WTree`; index loops need a termination lemma; `rfl` simp lemmas time out | Sections 9.1, 9.3 |
| Fuzzer: live comprehensions, lazy generators, shallow list `.copy()`, subclass field values, `bool` on the left, dict literal order (key, then value) | Sections 6.1, 6.2, 7.2, 7.4 |

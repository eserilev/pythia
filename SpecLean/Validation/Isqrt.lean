import SpecLean.Validation.Common

/-!
# Validation: `integer_squareroot`

The readable loop is well-founded recursion on `x`. The interpreter loop runs at most `x` times,
and `x < 2 ^ 64`, so fuel `2 ^ 64 + 20` is enough for every input.
-/

namespace SpecLean.Validation

open SpecLean SpecLean.Gen SpecLean.Encode

variable (sha : Oracle)

/-- One step of the loop on numbers: `x = y; y = (x + n // x) // 2`. -/
def isqrtStep (N : Nat) (s : Nat × Nat) : Res (Nat × Nat) := do
  let q ← chkDiv N s.2
  let t ← chkAdd s.2 q
  let y' ← chkDiv t 2
  pure (s.2, y')

/-- One unfolding of the readable loop, with the step on numbers. -/
theorem isqrt_loop_eq (N x y : Nat) :
    Readable.integer_squareroot.loop ⟨N⟩ ⟨x⟩ ⟨y⟩ =
      if y < x then
        Readable.erase (isqrtStep N (x, y)) >>= fun s =>
          Readable.integer_squareroot.loop ⟨N⟩ ⟨s.1⟩ ⟨s.2⟩
      else pure ⟨x⟩ := by
  rw [Readable.integer_squareroot.loop]
  by_cases hyx : y < x
  · rw [dif_pos hyx, if_pos hyx]
    simp only [uDiv_eq, uAdd_eq, isqrtStep]
    cases chkDiv N y with
    | error e => rfl
    | ok q =>
      simp only [Except.map_ok', erase_ok, Except.bind_ok']
      cases chkAdd y q with
      | error e => rfl
      | ok t =>
        simp only [Except.map_ok', erase_ok, Except.bind_ok']
        cases chkDiv t 2 with
        | error e => rfl
        | ok y' => rfl
  · rw [dif_neg hyx, if_neg hyx]

/-- The `while` loop invariant: `n`, `x` and `y` hold uint64 values and the heap is `h0`. -/
def IsqrtInv (h0 : Heap) (N : Nat) (s : Nat × Nat) (L : Locals) (h : Heap) : Prop :=
  h = h0 ∧ L Id.n = some (.uint u64Ty N) ∧ L Id.x = some (.uint u64Ty s.1) ∧
    L Id.y = some (.uint u64Ty s.2) ∧ s.1 < 2 ^ 64 ∧ s.2 < 2 ^ 64

/-- The `while` loop of `integer_squareroot` simulates the readable loop. -/
theorem isqrt_while (h0 : Heap) (N : Nat) (s1 s2 s3 s5 : Stmt) (l : Line) (c : Expr)
    (body : List Stmt)
    (hfn : fn_integer_squareroot.body = [s1, s2, s3, .whileStmt l c body, s5]) :
    ∀ n s L h, IsqrtInv h0 N s L h → s.1 ≤ n →
      StepRel (fun r L' h' => ∃ s, IsqrtInv h0 N s L' h' ∧ decide (s.2 < s.1) = false ∧
          (⟨s.1⟩ : Readable.Uint64) = r)
        (execWhile (env sha) (n + 6 + 1) L h c body)
        (Readable.integer_squareroot.loop ⟨N⟩ ⟨s.1⟩ ⟨s.2⟩) := by
  simp only [fn_integer_squareroot, List.cons.injEq, Stmt.whileStmt.injEq, and_true] at hfn
  obtain ⟨-, -, -, ⟨-, rfl, rfl⟩, -⟩ := hfn
  intro n s L h hR hμ
  refine interp_while (env sha) _ _ 6 (IsqrtInv h0 N) Prod.fst (fun s => decide (s.2 < s.1))
    (fun s => Readable.erase (isqrtStep N s)) (fun s => (⟨s.1⟩ : Readable.Uint64))
    (fun s => Readable.integer_squareroot.loop ⟨N⟩ ⟨s.1⟩ ⟨s.2⟩)
    (fun s => by rw [isqrt_loop_eq]; simp)
    ?hcond ?hbody ?hdec n s L h hR hμ
  case hcond =>
    intro n s L h hR
    obtain ⟨rfl, hn, hx, hy, -⟩ := hR
    simp [evalExpr, evalCmp, lookupName, compareOp, hx, hy,
      cmp_uint (hr := (rfl : resolveUint u64Ty u64Ty = .ok u64Ty)), cmpInt]
    by_cases hlt : s.2 < s.1 <;> simp [hlt]
  case hdec =>
    intro s s' hc hs
    simp only [decide_eq_true_eq] at hc
    revert hs
    simp only [isqrtStep]
    cases chkDiv N s.2 with
    | error e => simp
    | ok q =>
      simp only [Except.bind_ok']
      cases chkAdd s.2 q with
      | error e => simp
      | ok t =>
        simp only [Except.bind_ok']
        cases chkDiv t 2 with
        | error e => simp
        | ok y' =>
          simp only [Except.bind_ok', Except.pure_ok', erase_ok, Except.ok.injEq]
          intro e; subst e; exact hc
  case hbody =>
    intro n s L h hR hcs
    obtain ⟨rfl, hn, hx, hy, hx64, hy64⟩ := hR
    have ru : resolveUint u64Ty u64Ty = .ok u64Ty := rfl
    simp [execBlock, execStmt, evalExpr, assignTarget, lookupName, hn, hy,
      binop_floorDiv (hr := ru) (hb := rfl), binop_add (hr := ru) (hb := rfl), div2_int u64Ty rfl,
      isqrtStep]
    cases hq : chkDiv N s.2 with
    | error e => simp [StepRel, chkDiv_ne_oof hq]
    | ok q =>
      simp only [Except.bind_ok']
      cases ht : chkAdd s.2 q with
      | error e => simp [StepRel, chkAdd_ne_oof ht]
      | ok t =>
        simp only [Except.bind_ok']
        cases hy' : chkDiv t 2 with
        | error e => simp [StepRel, chkDiv_ne_oof hy']
        | ok y' =>
          simp only [Except.bind_ok', erase_ok, StepRel]
          refine ⟨rfl, ?_, ?_, ?_, hy64, chkDiv_lt hy'⟩ <;>
            simp (config := { decide := true }) [hn]

/-- `integer_squareroot` returns a uint64 and changes nothing. -/
def IsqrtExpect (N : Nat) (h : Heap) : Readable.Uint64 → Heap → Value → Prop :=
  fun r h' v => decU64 v = some r ∧ h' = h ∧ decU64 (.uint u64Ty N) = some ⟨N⟩

theorem integer_squareroot_run (k B : Nat) (h : Heap) (N : Nat) (hN : N < 2 ^ 64)
    (hNB : N ≤ B) :
    ResultMatches [] h [.uint u64Ty N] (IsqrtExpect N h)
      (callName (env sha) (k + B + 20) Id.integer_squareroot [.uint u64Ty N] h)
      (Readable.integer_squareroot ⟨N⟩) := by
  have hdecN : decU64 (.uint u64Ty N) = some ⟨N⟩ := by
    simp [decU64, decUint, u64Ty, UintTy.bits, hN]
  obtain ⟨s1, s2, s3, s5, l, c, body, hfn⟩ : ∃ s1 s2 s3 s5 l c body,
      fn_integer_squareroot.body = [s1, s2, s3, .whileStmt l c body, s5] :=
    ⟨_, _, _, _, _, _, _, rfl⟩
  have hw := isqrt_while sha h N s1 s2 s3 s5 l c body hfn
  simp only [fn_integer_squareroot, List.cons.injEq, Stmt.whileStmt.injEq, and_true] at hfn
  obtain ⟨rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, rfl⟩ := hfn
  rw [callName, callValue_fn _ _ _ (g_isqrt sha)]
  have ru : resolveUint u64Ty u64Ty = .ok u64Ty := rfl
  simp [callFn, fn_integer_squareroot, execBlock, execStmt, evalExpr, evalCmp, lookupName,
    evalList, bindArgs, bindArgs.go, compareOp, deepEq_uint, truthyH, g_UINT64_MAX, cmp_uint (hr := ru), cmpInt, Readable.integer_squareroot,
    Readable.UINT64_MAX]
  by_cases hmax : N = 18446744073709551615
  · subst hmax
    simp [truthy, LibValues.truthy, Ssz.truthy, pyTruthy, g_UINT64_MAX_SQRT, Readable.UINT64_MAX_SQRT, ResultMatches, IsqrtExpect,
      decU64, decUint, u64Ty, UintTy.bits]
    exact pure_result (by rintro k ⟨a, fs, hk, -⟩; match k with | 0 | 1 => simp at hk | _ + 2 => simp at hk)
  have hmax' : ¬ ((N : Int) = 18446744073709551615) := by omega
  simp [hmax, hmax', truthy, LibValues.truthy, Ssz.truthy, pyTruthy, assignTarget, add1_int u64Ty rfl, uAdd_eq, uDiv_eq]
  cases hA : chkAdd N 1 with
  | error e => simp [ResultMatches, chkAdd_ne_oof hA]
  | ok a =>
  simp [div2_int u64Ty rfl]
  cases hD : chkDiv a 2 with
  | error e => simp [ResultMatches, chkDiv_ne_oof hD]
  | ok y =>
  simp only [Except.map_ok', Except.bind_ok', erase_ok]
  have hR : IsqrtInv h N (N, y)
      (((Locals.empty.set Id.n (.uint u64Ty N)).set Id.x (.uint u64Ty N)).set Id.y
        (.uint u64Ty y)) h :=
    ⟨rfl, by simp (config := { decide := true }), by simp (config := { decide := true }),
      by simp, hN, chkDiv_lt hD⟩
  have hW := hw (k + B + 11) (N, y) _ h hR (by simp; omega)
  rw [show k + B + 18 = k + B + 11 + 6 + 1 by omega]
  revert hW
  generalize Readable.integer_squareroot.loop ⟨N⟩ ⟨(N, y).1⟩ ⟨(N, y).2⟩ = R
  generalize execWhile _ _ _ _ _ _ = E
  intro hW
  rcases E with e | ⟨o, L', h'⟩ <;> rcases R with e' | r
  · simp only [StepRel] at hW; simp [ResultMatches, hW]
  · simp only [StepRel] at hW
  · cases o <;> simp only [StepRel] at hW
  · cases o <;> simp only [StepRel] at hW
    obtain ⟨s', ⟨rfl, -, hx, -, hx64, -⟩, -, rfl⟩ := hW
    simp [hx, ResultMatches, IsqrtExpect, decU64, decUint, u64Ty, UintTy.bits, hx64]
    exact ⟨hN, pure_result (by rintro k ⟨a, fs, hk, -⟩; match k with | 0 | 1 => simp at hk | _ + 2 => simp at hk)⟩

/-- SPEC 9.2: `integer_squareroot` validated against the interpreter. The bound does not
depend on the input here, which is stronger than SPEC 9.2 asks. -/
theorem integer_squareroot_valid (h : Heap) (N : Nat) (hN : N < 2 ^ 64) :
    ∃ F, ∀ fuel ≥ F,
      ResultMatches [] h [.uint u64Ty N] (IsqrtExpect N h)
        (interp (env sha) fuel Id.integer_squareroot [.uint u64Ty N] h)
        (Readable.integer_squareroot ⟨N⟩) :=
  ⟨2 ^ 64 + 20, fun fuel hf => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hf
    rw [← Nat.add_assoc]
    exact integer_squareroot_run sha k (2 ^ 64) h N hN (Nat.le_of_lt hN)⟩

end SpecLean.Validation

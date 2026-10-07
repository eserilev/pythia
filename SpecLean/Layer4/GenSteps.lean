import SpecLean.Layer4.GenLemmas
import SpecLean.Layer4.GenAttr
import SpecLean.PrimRel

/-!
# Layer 4: one step of `den` per syntax node, as a rewrite

`den_expr` and its siblings are `rfl` lemmas. `simp` uses an `rfl` lemma as a definitional
step, and the kernel then checks it by unfolding `den` at a fuel such as `m + 9`, which recurses
too deep. The lemmas here say the same thing one syntax node at a time, and each is a rewrite,
so a generated proof can run `simp` over a whole function body.
-/

namespace SpecLean.Layer4.GenSteps

open SpecLean SpecLean.Encode SpecLean.Layer4

variable [LibModel]

attribute [local instance high] LibModel.toLibValues

set_option maxRecDepth 4096

variable (env : Env) (fps : Name → Footprint) (n : Nat) (fp : Footprint) (s : DSt)

section expr

theorem s_name (l : Line) (x : Name) :
    (den env fps (n + 1)).expr fp s (.name l x) =
      match s.loc x with
      | some r => .ok r
      | none => dGlobal env x := by rw [den_expr]; rfl

theorem s_int (l : Line) (k : Int) :
    (den env fps (n + 1)).expr fp s (.int l k) = some (.ok (.val (.int k))) := by rw [den_expr]; rfl

theorem s_bool (l : Line) (b : Bool) :
    (den env fps (n + 1)).expr fp s (.bool l b) = some (.ok (.val (.bool b))) := by rw [den_expr]; rfl

theorem s_noneLit (l : Line) :
    (den env fps (n + 1)).expr fp s (.noneLit l) = some (.ok (.val .none)) := by rw [den_expr]; rfl

theorem s_attr (l : Line) (o : Expr) (f : Name) :
    (den env fps (n + 1)).expr fp s (.attr l o f) =
      DM.bind ((den env fps n).expr fp s o) fun ro => dAttr env s ro f := by rw [den_expr]; rfl

theorem s_index (l : Line) (o i : Expr) :
    (den env fps (n + 1)).expr fp s (.index l o i) =
      DM.bind ((den env fps n).expr fp s o) fun ro =>
        DM.bind ((den env fps n).expr fp s i) fun ri => dIndex s ro ri := by rw [den_expr]; rfl

theorem s_binop (l : Line) (op : BinOp) (a b : Expr) :
    (den env fps (n + 1)).expr fp s (.binop l op a b) =
      DM.bind ((den env fps n).expr fp s a) fun ra =>
        DM.bind ((den env fps n).expr fp s b) fun rb => dBinop op ra rb := by rw [den_expr]; rfl

theorem s_compare (l : Line) (a : Expr) (rest : List (CmpOp × Expr)) :
    (den env fps (n + 1)).expr fp s (.compare l a rest) =
      DM.bind ((den env fps n).expr fp s a) fun ra =>
        match ra with
        | .val x => cmpOf ((den env fps n).expr fp s) x rest
        | _ => none := by rw [den_expr]; rfl

theorem s_boolop (l : Line) (op : BoolOp) (es : List Expr) :
    (den env fps (n + 1)).expr fp s (.boolop l op es) = boolOf ((den env fps n).expr fp s) op es := by
  rw [den_expr]; rfl

theorem s_not (l : Line) (a : Expr) :
    (den env fps (n + 1)).expr fp s (.unop l .not a) =
      DM.bind ((den env fps n).expr fp s a) fun r =>
        match r with
        | .val v => DM.bind (lift (truthy v)) fun b => .ok (.val (.bool !b))
        | _ => none := by rw [den_expr]; rfl

theorem s_unop (l : Line) (op : UnOp) (hop : op ≠ .not) (a : Expr) :
    (den env fps (n + 1)).expr fp s (.unop l op a) =
      DM.bind ((den env fps n).expr fp s a) fun r =>
        match r with
        | .val v => DM.bind (lift (unopVal op v)) fun w => if Flat w then .ok (.val w) else none
        | _ => none := by
  cases op
  · exact absurd rfl hop
  all_goals (rw [den_expr]; rfl)

theorem s_slice (l : Line) (o : Expr) (lo hi : Option Expr) :
    (den env fps (n + 1)).expr fp s (.slice l o lo hi none) =
      DM.bind ((den env fps n).expr fp s o) fun ro =>
        match ro with
        | .val (.bytes c bs) =>
          DM.bind (optOf ((den env fps n).expr fp s) lo) fun lov =>
            DM.bind (optOf ((den env fps n).expr fp s) hi) fun hiv =>
              DM.bind (lift (getSlice env.bytesName Heap.empty (.bytes c bs) lov hiv)) fun x =>
                if Flat x.1 then .ok (.val x.1) else none
        | _ => none := by rw [den_expr]; rfl

theorem s_ifExp (l : Line) (c a b : Expr) :
    (den env fps (n + 1)).expr fp s (.ifExp l c a b) =
      DM.bind ((den env fps n).expr fp s c) fun rc =>
        match rc with
        | .val v => DM.bind (lift (truthy v)) fun t =>
            if t then (den env fps n).expr fp s a else (den env fps n).expr fp s b
        | _ => none := by rw [den_expr]; rfl

theorem s_comp (l : Line) (elt : Expr) (t : Target) (it : Expr) (ifs : List Expr) :
    (den env fps (n + 1)).expr fp s (.comp l .list elt [.mk t it ifs]) =
      DM.bind ((den env fps n).iter fp s it) fun ls =>
        DM.bind ((den env fps n).items fp s t ifs elt ls 0) fun ds =>
          .ok (.tree (.list .pyList .any none ds)) := by rw [den_expr]; rfl

theorem s_call (l : Line) (f : Expr) (args : List Arg)
    (hfb : fromBytesOf env s (.call l f args) = none) (hbl : blsOf env s (.call l f args) = none) :
    (den env fps (n + 2)).expr fp s (.call l f args) =
      match callHead env s (.call l f args) with
      | some (g, args) =>
        if allKw args then DM.bind (kwsOf ((den env fps (n + 1)).expr fp s) args) fun kvs => kwCtor env g kvs
        else DM.bind (argsOf ((den env fps (n + 1)).expr fp s) args) fun rs =>
          dCallRO env fps (den env fps (n + 1)).fn s g rs
      | none => none := by
  rw [den_expr]
  cases hc : callHead env s (.call l f args) with
  | some ga => simp only [exprStep, hc]
  | none => cases n <;> simp [exprStep, hc, hfb, hbl]

/-- `bls.f(args)`. -/
theorem s_bls (l la ln : Line) (g f : Name) (args : List Arg)
    (hc : callHead env s (.call l (.attr la (.name ln g) f) args) = none)
    (hfb : fromBytesOf env s (.call l (.attr la (.name ln g) f) args) = none)
    (hbl : blsOf env s (.call l (.attr la (.name ln g) f) args) = some (f, args)) :
    (den env fps (n + 3)).expr fp s (.call l (.attr la (.name ln g) f) args) =
      DM.bind (argsOf ((den env fps (n + 2)).expr fp s) args) fun rs => dBls env f rs := by
  rw [den_expr]; simp only [exprStep, hc, hfb, hbl]

/-- `int.from_bytes(args)`. -/
theorem s_fromBytes (l la ln : Line) (g fb : Name) (args : List Arg)
    (hc : callHead env s (.call l (.attr la (.name ln g) fb) args) = none)
    (hfb : fromBytesOf env s (.call l (.attr la (.name ln g) fb) args) = some args) :
    (den env fps (n + 3)).expr fp s (.call l (.attr la (.name ln g) fb) args) =
      DM.bind (argsOf ((den env fps (n + 2)).expr fp s) args) fun rs => dFromBytes env rs := by
  rw [den_expr]; simp only [exprStep, hc, hfb]

end expr

section call

theorem s_callStep (e : Expr) (hap : appendOf env e = none) :
    (den env fps (n + 2)).call fp s e =
      match callHead env s e with
      | some (g, args) =>
        if allKw args then
          DM.bind (DM.bind (kwsOf ((den env fps (n + 1)).expr fp s) args) fun kvs => kwCtor env g kvs)
            fun r => .ok (r, s.roots)
        else DM.bind (argsOf ((den env fps (n + 1)).expr fp s) args) fun rs =>
          dCallW env fps (den env fps (n + 1)).fn fp s g rs
      | none => DM.bind ((den env fps (n + 2)).expr fp s e) fun r => .ok (r, s.roots) := by
  rw [den_call]; unfold callStep; simp only [hap]; show (match n + 1, callHead env s e with
    | _ + 1, some (g, args) => _
    | _, _ => _) = _
  cases callHead env s e with
  | some _ => rfl
  | none =>
    show Option.map _ (exprStep env fps (n + 1) (den env fps (n + 1)) fp s e) = _
    rw [← den_expr]
    rcases (den env fps (n + 2)).expr fp s e with _ | ⟨_ | _⟩ <;> rfl

/-- `o.append(a)`: the receiver at the fuel below, the item at this fuel. -/
theorem s_append (l l' : Line) (o a : Expr) (m : Name) (hm : m = env.nm.append) :
    (den env fps (n + 2)).call fp s (.call l (.attr l' o m) [.pos a]) =
      DM.bind ((den env fps n).expr fp s o) fun ro =>
        match ro with
        | .place k p =>
          match s.deref k p, s.roots[k]? with
          | some (.list kd el lm ds), some dk =>
            if appendable kd el && fpOk fp s.roots k p then
              DM.bind ((den env fps (n + 1)).expr fp s a) fun ra =>
                DM.bind (appendItemD env s el a ra) fun d =>
                  DM.bind (lift (Ssz.checkLength kd lm (ds.length + 1))) fun _ =>
                    .ok (.val .none, s.roots.set k (setAt p dk (.list kd el lm (ds ++ [d]))))
            else none
          | _, _ => none
        | _ => none := by
  subst hm; rw [den_call]; unfold callStep; simp only [appendOf, if_true]; rfl

theorem appendable_list_cont (ty : Name) : appendable .list (.container ty) = true := rfl
theorem appendable_plist_cont (ty : Name) : appendable .progressiveList (.container ty) = true := rfl
theorem appendable_list_nom (c : Name) (b : Nat) : appendable .list (.uint (.nominal c b)) = true := rfl
theorem appendable_plist_nom (c : Name) (b : Nat) :
    appendable .progressiveList (.uint (.nominal c b)) = true := rfl
theorem appendable_list_bytes (c : Name) (b : Nat) : appendable .list (.bytes c b) = true := rfl
theorem appendable_plist_bytes (c : Name) (b : Nat) :
    appendable .progressiveList (.bytes c b) = true := rfl

end call

section stmt

theorem s_assign (l : Line) (t : Target) (e : Expr) :
    (den env fps (n + 1)).stmt fp s (.assign l [t] e) =
      DM.bind ((den env fps n).call fp s e) fun (r, rs) =>
        (den env fps n).target fp { s with roots := rs } t r := by rw [den_stmt]; rfl

theorem s_annAssign (l : Line) (t : Target) (e : Expr) :
    (den env fps (n + 1)).stmt fp s (.annAssign l t e) =
      DM.bind ((den env fps n).call fp s e) fun (r, rs) =>
        (den env fps n).target fp { s with roots := rs } t r := by rw [den_stmt]; rfl

theorem s_exprStmt (l : Line) (e : Expr) :
    (den env fps (n + 1)).stmt fp s (.exprStmt l e) =
      DM.bind ((den env fps n).call fp s e) fun (_, rs) => .ok (.normal, { s with roots := rs }) := by
  rw [den_stmt]; rfl

theorem s_augAssign (l l' : Line) (o ie : Expr) (op : BinOp) (e : Expr) :
    (den env fps (n + 1)).stmt fp s (.augAssign l (.index l' o ie) op e) =
      augStep env (den env fps n) fp s o ie op e := by rw [den_stmt]; rfl

theorem s_augName (l l' : Line) (x : Name) (op : BinOp) (e : Expr) :
    (den env fps (n + 1)).stmt fp s (.augAssign l (.name l' x) op e) =
      augName (den env fps n) fp s x op e := by rw [den_stmt]; rfl

theorem s_ifStmt (l : Line) (c : Expr) (thn els : List Stmt) :
    (den env fps (n + 1)).stmt fp s (.ifStmt l c thn els) =
      DM.bind ((den env fps n).expr fp s c) fun r =>
        match r with
        | .val v => DM.bind (lift (truthy v)) fun b =>
            if b then blockOf ((den env fps n).stmt fp) s thn else blockOf ((den env fps n).stmt fp) s els
        | _ => none := by rw [den_stmt]; rfl

theorem s_ret (l : Line) (e : Expr) :
    (den env fps (n + 1)).stmt fp s (.ret l (some e)) =
      DM.bind ((den env fps n).expr fp s e) fun r =>
        match r with
        | .val v => .ok (.ret (.val v), s)
        | .tree d => .ok (.ret (.tree d), s)
        | .place _ _ => none := by rw [den_stmt]; rfl

theorem s_retNone (l : Line) :
    (den env fps (n + 1)).stmt fp s (.ret l none) = .ok (.ret (.val .none), s) := by rw [den_stmt]; rfl

theorem s_assert (l : Line) (e : Expr) :
    (den env fps (n + 1)).stmt fp s (.assert l e) =
      DM.bind ((den env fps n).expr fp s e) fun r =>
        match r with
        | .val v => DM.bind (lift (truthy v)) fun b =>
            if b then .ok (.normal, s) else some (.error .assertionFailed)
        | _ => none := by rw [den_stmt]; rfl

theorem s_pass (l : Line) : (den env fps (n + 1)).stmt fp s (.pass l) = .ok (.normal, s) := by
  rw [den_stmt]; rfl

theorem s_forStmt (l : Line) (t : Target) (it : Expr) (body : List Stmt) :
    (den env fps (n + 1)).stmt fp s (.forStmt l t it body) =
      DM.bind ((den env fps n).iter fp s it) fun ls => (den env fps n).loop fp s t ls 0 body := by
  rw [den_stmt]; rfl

end stmt

section target

theorem s_tname (l : Line) (x : Name) (r : DRes) :
    (den env fps (n + 1)).target fp s (.name l x) r = .ok (.normal, { s with loc := setLoc s.loc x r }) := by
  rw [den_target]; rfl

theorem s_tattr (l : Line) (o : Expr) (f : Name) (v : Value) :
    (den env fps (n + 1)).target fp s (.attr l o f) (.val v) =
      DM.bind ((den env fps n).expr fp s o) fun ro =>
        match ro with
        | .place k p =>
          match s.deref k p with
          | some (.cont ty _) =>
            match fieldIndex env ty f with
            | some (i, t) => DM.bind (dCoerce env true t v) fun v' => dWriteD fp s k p i v'
            | none => none
          | _ => none
        | _ => none := by rw [den_target]; rfl

theorem s_tindex (l : Line) (o ie : Expr) (v : Value) :
    (den env fps (n + 1)).target fp s (.index l o ie) (.val v) =
      DM.bind ((den env fps n).expr fp s o) fun ro => DM.bind ((den env fps n).expr fp s ie) fun ri =>
        match ro, ri with
        | .place k p, .val iv =>
          match s.deref k p with
          | some (.list kd e _ ds) =>
            if isByteList kd e then none else
            DM.bind (lift (toIndex iv)) fun j =>
            DM.bind (dCoerce env false e v) fun v' =>
              match normIndex ds.length j with
              | some m => dWriteD fp s k p m v'
              | none => some (.error .indexError)
          | _ => none
        | _, _ => none := by rw [den_target]; rfl

end target

section fn

theorem s_fn (d : FunctionDef) (roots : List DV) :
    (den env fps (n + 1)).fn fp d roots =
      if noneDefaults d = true ∧ d.params.vararg = none ∧ d.params.names.length = roots.length then
        DM.bind (blockOf ((den env fps n).stmt fp)
            { roots, loc := initLoc roots (fun _ => none) d.params.names.zipIdx } d.body) fun (o, s1) =>
          match o with
          | .ret r => .ok (r, s1.roots)
          | _ => .ok (.val .none, s1.roots)
      else none := by rw [den_fn]; rfl

theorem s_iter (e : Expr) :
    (den env fps (n + 1)).iter fp s e = iterStep env fps n (den env fps n) fp s e := by rw [den_iter]

/-- A loop over a list at a place given by an attribute or a name. -/
theorem s_iter_attr (l : Line) (o : Expr) (f : Name) :
    (den env fps (n + 1)).iter fp s (.attr l o f) =
      DM.bind ((den env fps (n + 1)).expr fp s (.attr l o f)) fun r =>
        match r with
        | .place k p => if listPlace s k p then .ok ⟨k, p, false⟩ else none
        | _ => none := by rw [den_iter, den_expr]; rfl

theorem s_iter_name (l : Line) (x : Name) :
    (den env fps (n + 1)).iter fp s (.name l x) =
      DM.bind ((den env fps (n + 1)).expr fp s (.name l x)) fun r =>
        match r with
        | .place k p => if listPlace s k p then .ok ⟨k, p, false⟩ else none
        | _ => none := by rw [den_iter, den_expr]; rfl

/-- A loop or a comprehension over `enumerate` of a list at a place. -/
theorem s_iter_enum (l l' : Line) (g : Name) (e : Expr) :
    (den env fps (n + 2)).iter fp s (.call l (.name l' g) [.pos e]) =
      if (s.loc g).isNone && isEnumerate env g then
        DM.bind ((den env fps (n + 1)).expr fp s e) fun r =>
          match r with
          | .place k p => if listPlace s k p then .ok ⟨k, p, true⟩ else none
          | _ => none
      else none := by rw [den_iter]; rfl

theorem s_loop (t : Target) (ls : LSrc) (i : Nat) (body : List Stmt) :
    (den env fps (n + 1)).loop fp s t ls i body = loopStep n (den env fps n) fp s t ls i body := by
  rw [den_loop]

theorem s_items (t : Target) (ifs : List Expr) (elt : Expr) (ls : LSrc) (i : Nat) :
    (den env fps (n + 1)).items fp s t ifs elt ls i = itemsStep n (den env fps n) fp s t ifs elt ls i := by
  rw [den_items]

end fn

section block
variable (st : DSt → Stmt → DM (DOut × DSt))

theorem b_nil : blockOf st s [] = some (.ok (.normal, s)) := Eq.trans rfl rfl

theorem b_cons (x : Stmt) (xs : List Stmt) :
    blockOf st s (x :: xs) =
      DM.bind (st s x) fun (o, s1) =>
        match o with
        | .normal => blockOf st s1 xs
        | _ => .ok (o, s1) := Eq.trans rfl rfl

end block

section push

theorem dm_ite {α β : Type} (c : Prop) [Decidable c] (x y : DM α) (f : α → DM β) :
    DM.bind (if c then x else y) f = if c then DM.bind x f else DM.bind y f := by
  by_cases h : c
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

theorem eb_ite {ε α β : Type} (c : Prop) [Decidable c] (x y : Except ε α) (f : α → Except ε β) :
    (if c then x else y) >>= f = if c then x >>= f else y >>= f := by
  by_cases h : c
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

theorem lift_ite {α : Type} (c : Prop) [Decidable c] (x y : Res α) :
    lift (if c then x else y) = if c then lift x else lift y := by
  by_cases h : c
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

theorem lift_okp {α : Type} (a : α) : lift (.ok a : Res α) = some (.ok a) := Eq.trans rfl rfl

theorem lift_errp {α : Type} (e : SpecError) (h : e ≠ .outOfFuel) :
    lift (.error e : Res α) = some (.error e) := lift_err e h

theorem eb_okp {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := Eq.trans rfl rfl

theorem eb_errp {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = (Except.error e : Except ε β) := Eq.trans rfl rfl

theorem map_ite {α β : Type} (c : Prop) [Decidable c] (x y : Option α) (f : α → β) :
    Option.map f (if c then x else y) = if c then Option.map f x else Option.map f y := by
  by_cases h : c
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

theorem emap_ite {ε α β : Type} (c : Prop) [Decidable c] (x y : Except ε α) (f : α → β) :
    f <$> (if c then x else y) = if c then f <$> x else f <$> y := by
  by_cases h : c
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

theorem emap_ok {ε α β : Type} (a : α) (f : α → β) : f <$> (Except.ok a : Except ε α) = .ok (f a) := Eq.trans rfl rfl
theorem emap_err {ε α β : Type} (e : ε) (f : α → β) : f <$> (Except.error e : Except ε α) = .error e := Eq.trans rfl rfl
theorem merr_ok {ε ε' α : Type} (a : α) (f : ε → ε') : Except.mapError f (.ok a : Except ε α) = .ok a := Eq.trans rfl rfl
theorem merr_err {ε ε' α : Type} (e : ε) (f : ε → ε') :
    Except.mapError f (.error e : Except ε α) = .error (f e) := Eq.trans rfl rfl
theorem epure {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := Eq.trans rfl rfl
theorem ethrow {ε α : Type} (e : ε) : (throw e : Except ε α) = .error e := Eq.trans rfl rfl
theorem ebind_pure {ε α : Type} (x : Except ε α) : (x >>= fun a => pure a) = x := by cases x <;> rfl

theorem some_ite {α : Type} (c : Prop) [Decidable c] (x y : α) :
    some (if c then x else y) = if c then some x else some y := by
  by_cases h : c
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

theorem uv_ofNat {α : Type} [Rd.UintC α] (n : Nat) : Rd.UintC.val (Rd.UintC.ofNat n : α) = n :=
  Rd.UintC.val_ofNat n

theorem merr_ite {ε ε' α : Type} (c : Prop) [Decidable c] (x y : Except ε α) (f : ε → ε') :
    Except.mapError f (if c then x else y) = if c then Except.mapError f x else Except.mapError f y := by
  by_cases h : c
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

theorem eb_assoc {ε α β γ : Type} (x : Except ε α) (f : α → Except ε β) (g : β → Except ε γ) :
    (x >>= f) >>= g = x >>= fun a => f a >>= g := by cases x <;> rfl

theorem dm_assoc {α β γ : Type} (x : DM α) (f : α → DM β) (g : β → DM γ) :
    DM.bind (DM.bind x f) g = DM.bind x fun a => DM.bind (f a) g := by
  rcases x with _ | _ | _ <;> rfl

theorem getD_ite {α : Type} (c : Prop) [Decidable c] (x y : Option α) (d : α) :
    (if c then x else y).getD d = if c then x.getD d else y.getD d := by
  by_cases h : c
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-- The rest of a run after a call: the callee result decides it. -/
def callK {β γ : Type} (y : Except Fail β) (g : β → Option (Except Fail γ)) : Option (Except Fail γ) :=
  match y with
  | .ok b => g b
  | .error e => some (.error e)

theorem callK_ok {β γ : Type} (b : β) (g : β → Option (Except Fail γ)) : callK (.ok b) g = g b := Eq.trans rfl rfl

theorem callK_err {β γ : Type} (e : Fail) (g : β → Option (Except Fail γ)) :
    callK (.error e) g = some (.error e) := Eq.trans rfl rfl

theorem callK_ite {β γ : Type} (c : Prop) [Decidable c] (x y : Except Fail β)
    (g : β → Option (Except Fail γ)) :
    callK (if c then x else y) g = if c then callK x g else callK y g := by
  by_cases h : c
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

theorem callK_bind {β δ γ : Type} (y : Except Fail β) (h : β → Except Fail δ)
    (g : δ → Option (Except Fail γ)) : callK (y >>= h) g = callK y fun b => callK (h b) g := by
  cases y <;> rfl

theorem callK_pure {β γ : Type} (b : β) (g : β → Option (Except Fail γ)) :
    callK (pure b) g = g b := Eq.trans rfl rfl

theorem callK_congr {β γ : Type} (y : Except Fail β) {g g' : β → Option (Except Fail γ)}
    (h : ∀ b, g b = g' b) : callK y g = callK y g' := by
  cases y
  · rfl
  · exact h _

/-- `callK_congr` with the result of the call in context. -/
theorem bytesOf_ok_len' {β : Type} [Rd.BytesC β] {b : Rd.Bytes} {x : β} (h : Rd.bytesOf β b = .ok x) :
    (Rd.BytesC.data x).length = Rd.BytesC.len β := by
  unfold Rd.bytesOf at h
  split at h
  · next hl => cases h; rw [Rd.BytesC.data_ofBytes]; exact hl
  · cases h

theorem lget_mem {α : Type} {xs : List α} {i : Int} {x : α} (h : Rd.lget xs i = .ok x) : x ∈ xs := by
  unfold Rd.lget at h
  split at h
  · next y hy =>
    cases h; simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hy
    obtain ⟨j, -, hj⟩ := hy; exact List.mem_of_getElem? hj
  · cases h

theorem callK_congr' {β γ : Type} (y : Except Fail β) {g g' : β → Option (Except Fail γ)}
    (h : ∀ b, y = .ok b → g b = g' b) : callK y g = callK y g' := by
  cases y
  · rfl
  · exact h _ rfl

/-- A call of a proved callee: the readable result decides the rest. -/
theorem bind_call {α β γ : Type} {x : DM α} {y : Except Fail β} {enc : β → α}
    (hx : Option.map (Except.mapError SpecError.fail) x = some (enc <$> y)) (k : α → DM γ) :
    Option.map (Except.mapError SpecError.fail) (DM.bind x k) =
      callK y fun b => Option.map (Except.mapError SpecError.fail) (k (enc b)) := by
  rcases x with _ | ⟨e | a⟩
  · cases hx
  · cases y with
    | ok b => cases hx
    | error e' => simp only [Option.map_some, Except.mapError, Option.some.injEq] at hx; cases hx; rfl
  · cases y with
    | ok b =>
      simp only [Option.map_some, Except.mapError, Option.some.injEq] at hx
      cases hx; rfl
    | error e' => cases hx

/-- The readable side of a call: the same split on the callee result. -/
theorem rd_bind {β δ ε : Type} (f : δ → ε) (y : Except Fail β) (h : β → Except Fail δ) :
    some (f <$> (y >>= h)) = callK y fun b => some (f <$> h b) := by
  cases y <;> rfl

theorem ob_some {α β : Type} (a : α) (f : α → Option β) : (some a >>= f) = f a := Eq.trans rfl rfl
theorem ob_none {α β : Type} (f : α → Option β) : ((none : Option α) >>= f) = none := Eq.trans rfl rfl
theorem ob_ite {α β : Type} (c : Prop) [Decidable c] (x y : Option α) (f : α → Option β) :
    ((if c then x else y) >>= f) = if c then x >>= f else y >>= f := by
  by_cases h : c
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

theorem opure {α : Type} (a : α) : (pure a : Option α) = some a := Eq.trans rfl rfl

theorem natCast_lt_zero (n : Nat) : ((n : Int) < 0) = False := by
  apply propext; constructor
  · intro h; omega
  · intro h; exact h.elim

theorem exm_ok {ε α β : Type} (a : α) (f : α → β) : Except.map f (.ok a : Except ε α) = .ok (f a) :=
  Eq.trans rfl rfl
theorem exm_err {ε α β : Type} (e : ε) (f : α → β) : Except.map f (.error e : Except ε α) = .error e :=
  Eq.trans rfl rfl

/-- A call inside an expression at statement level: the pairing with the trees moves inside. -/
theorem omap_bind {α β γ : Type} (g : β → γ) (x : DM α) (k : α → DM β) :
    Option.map (Except.map g) (DM.bind x k) = DM.bind x fun a => Option.map (Except.map g) (k a) := by
  rcases x with _ | ⟨e | a⟩ <;> rfl

theorem setLoc_same (L : Name → Option DRes) (x : Name) (a b : DRes) :
    setLoc (setLoc L x a) x b = setLoc L x b := by
  funext y; simp only [setLoc]; split <;> rfl

theorem fite_app {α β : Type} (c : Prop) [Decidable c] (f g : α → β) (a : α) :
    (if c then f else g) a = if c then f a else g a := by
  by_cases h : c
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

theorem dst_loc_ite (c : Prop) [Decidable c] (R : List DV) (L1 L2 : Name → Option DRes) :
    (DSt.mk R (if c then L1 else L2)).loc = if c then L1 else L2 := Eq.trans rfl rfl

theorem flat_int (n : Int) : Flat (.int n) = true := Eq.trans rfl rfl
theorem flat_bool (b : Bool) : Flat (.bool b) = true := Eq.trans rfl rfl
theorem flat_lib (v : LibVal) : Flat (.lib v) = true := Eq.trans rfl rfl
theorem flat_none : Flat .none = true := Eq.trans rfl rfl
theorem flat_bytes (c : Name) (b : List UInt8) : Flat (.bytes c b) = true := Eq.trans rfl rfl
theorem flat_str (x : String) : Flat (.str x) = true := Eq.trans rfl rfl

theorem flat_ite (c : Prop) [Decidable c] (a b : Value) :
    Flat (if c then a else b) = if c then Flat a else Flat b := by
  by_cases h : c
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

theorem val_ite (c : Prop) [Decidable c] (a b : Value) :
    DRes.val (if c then a else b) = if c then DRes.val a else DRes.val b := by
  by_cases h : c
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

theorem bmin_max : (Builtin.min == Builtin.max) = false := Eq.trans rfl rfl
theorem bmax_max : (Builtin.max == Builtin.max) = true := Eq.trans rfl rfl

theorem allKw_kw (k : Name) (e : Expr) (as : List Arg) :
    allKw (.kw k e :: as) = as.all fun a => match a with | .kw _ _ => true | _ => false :=
  Eq.trans rfl rfl

theorem dmb_none {α β : Type} (f : α → DM β) : DM.bind none f = none := Eq.trans rfl rfl

end push

section model

/-- The value rules of the SSZ model, as one `match` each: `simp` then reduces the `match` on the
constructors of the operands. -/
theorem bv_eq (op : BinOp) (x y : Value) :
    @binopVal (@LibModel.toLibValues Ssz.model) op x y =
      (Ssz.binop op x y).getD (pyBinop op x y) := by
  show (match Ssz.binop op x y with | some r => r | none => pyBinop op x y) = _
  cases Ssz.binop op x y <;> rfl

theorem cv_eq (op : CmpOp) (x y : Value) :
    @cmpVal (@LibModel.toLibValues Ssz.model) op x y =
      (Ssz.compare op x y).getD (pyCmp op x y) := by
  show (match Ssz.compare op x y with | some r => r | none => pyCmp op x y) = _
  cases Ssz.compare op x y <;> rfl

theorem uv_eq (op : UnOp) (x : Value) :
    @unopVal (@LibModel.toLibValues Ssz.model) op x = (Ssz.unop op x).getD (pyUnop op x) := by
  show (match Ssz.unop op x with | some r => r | none => pyUnop op x) = _
  cases Ssz.unop op x <;> rfl

theorem iv_eq (x : Value) :
    @toIndex (@LibModel.toLibValues Ssz.model) x = (Ssz.index x).getD (pyIndex x) := by
  show (match Ssz.index x with | some r => r | none => pyIndex x) = _
  cases Ssz.index x <;> rfl

theorem tv_eq (x : Value) :
    @truthy (@LibModel.toLibValues Ssz.model) x =
      (Ssz.truthy x).getD (pyTruthy x) := by
  show (match Ssz.truthy x with | some r => r | none => pyTruthy x) = _
  cases Ssz.truthy x <;> rfl

/-! The value rules on operands of known constructors. `simp` never unfolds a rule on an
operand it does not know, which would give a `match` over every constructor. -/

theorem bv_uu (op : BinOp) (t t' : UintTy) (a b : Nat) :
    @binopVal (@LibModel.toLibValues Ssz.model) op (.uint t a) (.uint t' b) =
      (resolveUint t t' >>= fun r => intArith op a b >>= wrapUint r) := Eq.trans rfl rfl
theorem bv_ui (op : BinOp) (t : UintTy) (a : Nat) (b : Int) :
    @binopVal (@LibModel.toLibValues Ssz.model) op (.uint t a) (.int b) =
      (intArith op a b >>= wrapUint t) := Eq.trans rfl rfl
theorem bv_iu (op : BinOp) (t : UintTy) (a : Int) (b : Nat) :
    @binopVal (@LibModel.toLibValues Ssz.model) op (.int a) (.uint t b) =
      (intArith op a b >>= wrapUint t) := Eq.trans rfl rfl
theorem bv_ii (op : BinOp) (a b : Int) :
    @binopVal (@LibModel.toLibValues Ssz.model) op (.int a) (.int b) = (.int <$> intArith op a b) := Eq.trans rfl rfl
theorem cv_uu (op : CmpOp) (t t' : UintTy) (a b : Nat) :
    @cmpVal (@LibModel.toLibValues Ssz.model) op (.uint t a) (.uint t' b) =
      (resolveUint t t' >>= fun _ => pure (cmpInt op a b)) := Eq.trans rfl rfl
theorem cv_ui (op : CmpOp) (t : UintTy) (a : Nat) (b : Int) :
    @cmpVal (@LibModel.toLibValues Ssz.model) op (.uint t a) (.int b) = .ok (cmpInt op a b) := Eq.trans rfl rfl
theorem cv_iu (op : CmpOp) (t : UintTy) (a : Int) (b : Nat) :
    @cmpVal (@LibModel.toLibValues Ssz.model) op (.int a) (.uint t b) = .ok (cmpInt op a b) := Eq.trans rfl rfl
theorem cv_ii (op : CmpOp) (a b : Int) :
    @cmpVal (@LibModel.toLibValues Ssz.model) op (.int a) (.int b) = .ok (cmpInt op a b) := Eq.trans rfl rfl
theorem bv_bytes (op : BinOp) (c c' : Name) (a b : List UInt8) :
    @binopVal (@LibModel.toLibValues Ssz.model) op (.bytes c a) (.bytes c' b) =
      (match op with
       | .add => .ok (.bytes 0 (a ++ b))
       | _ => .error .typeError) := Eq.trans rfl rfl
theorem cv_bytes (op : CmpOp) (c c' : Name) (a b : List UInt8) :
    @cmpVal (@LibModel.toLibValues Ssz.model) op (.bytes c a) (.bytes c' b) = pyCmp op (.bytes c a) (.bytes c' b) := Eq.trans rfl rfl
theorem cv_boolean (op : CmpOp) (a b : Bool) :
    @cmpVal (@LibModel.toLibValues Ssz.model) op (.boolean a) (.boolean b) =
      (match op with
      | .eq => .ok (a == b)
      | .notEq => .ok (a != b)
      | _ => .error .unsupported) := Eq.trans rfl rfl
theorem tv_bool (b : Bool) : @truthy (@LibModel.toLibValues Ssz.model) (.bool b) = .ok b := Eq.trans rfl rfl
theorem tv_boolean (b : Bool) : @truthy (@LibModel.toLibValues Ssz.model) (.boolean b) = .ok b := Eq.trans rfl rfl
theorem tv_uint (t : UintTy) (n : Nat) :
    @truthy (@LibModel.toLibValues Ssz.model) (.uint t n) = .ok (n != 0) := Eq.trans rfl rfl
theorem tv_int (n : Int) : @truthy (@LibModel.toLibValues Ssz.model) (.int n) = .ok (n != 0) := Eq.trans rfl rfl
theorem tv_none : @truthy (@LibModel.toLibValues Ssz.model) .none = .ok false := Eq.trans rfl rfl
theorem tv_bytes (c : Name) (b : List UInt8) :
    @truthy (@LibModel.toLibValues Ssz.model) (.bytes c b) = .ok (!b.isEmpty) := Eq.trans rfl rfl
theorem uv_neg (t : UintTy) (n : Nat) :
    @unopVal (@LibModel.toLibValues Ssz.model) .neg (.uint t n) = .ok (.int (-(n : Int))) := Eq.trans rfl rfl
theorem uv_inv (t : UintTy) (n : Nat) :
    @unopVal (@LibModel.toLibValues Ssz.model) .invert (.uint t n) = .ok (.int (Int.not n)) := Eq.trans rfl rfl
theorem uv_negi (n : Int) : @unopVal (@LibModel.toLibValues Ssz.model) .neg (.int n) = .ok (.int (-n)) := Eq.trans rfl rfl
theorem iv_uint (t : UintTy) (n : Nat) : @toIndex (@LibModel.toLibValues Ssz.model) (.uint t n) = .ok n := Eq.trans rfl rfl
theorem iv_int (n : Int) : @toIndex (@LibModel.toLibValues Ssz.model) (.int n) = .ok n := Eq.trans rfl rfl

theorem cons_bool (env : Env) (h : Heap) (b : Bool) :
    @LibModel.construct Ssz.model env h .boolean [.bool b] [] = .ok (.boolean b, h) := Eq.trans rfl rfl
theorem cons_bytes_nil (env : Env) (h : Heap) (ty : Name) (len : Nat) :
    @LibModel.construct Ssz.model env h (.bytes ty len) [] [] = .ok (.bytes ty (List.replicate len 0), h) :=
  Eq.trans rfl rfl
theorem cons_bytes (env : Env) (h : Heap) (ty : Name) (len : Nat) (c : Name) (bs : List UInt8) :
    @LibModel.construct Ssz.model env h (.bytes ty len) [.bytes c bs] [] =
      if bs.length = len then .ok (.bytes ty bs, h) else .error .sszValue := Eq.trans rfl rfl
theorem cons_boolean (env : Env) (h : Heap) (b : Bool) :
    @LibModel.construct Ssz.model env h .boolean [.boolean b] [] = .ok (.boolean b, h) := Eq.trans rfl rfl

/-- A written flat value, into a uint field or element: the coercion of the field or of the
list element. -/
theorem dco_uint (env : Env) (b : Bool) (u : UintTy) (v : Value) (hv : ∀ a, v ≠ .ref a) :
    @dCoerce Ssz.model env b (.uint u) v =
      lift (if b then coerceField (.uint u) v else coerceElem (.uint u) v) := by
  simp only [dCoerce, coerceWith_uint env b _ u v hv]
  generalize (if b = true then coerceField (.uint u) v else coerceElem (.uint u) v) = r
  cases r <;> rfl

theorem coerceH_flat (env : Env) (b : Bool) (d : Nat) (h : Heap) (t : SszTy) (v : Value)
    (ht : ∀ ty, t ≠ .container ty) (hl : ∀ k e l, t ≠ .list k e l) (ha : t ≠ .any)
    (hv : ∀ a, v ≠ .ref a) (hv' : ∀ xs, v ≠ .tuple xs) :
    Ssz.coerceH env b (d + 1) h t v =
      (fun x => (x, h)) <$> (if b then coerceField t v else coerceElem t v) := by
  rw [Ssz.coerceH.eq_def]
  cases t <;> first
    | exact absurd rfl (ht _) | exact absurd rfl (hl _ _ _) | exact absurd rfl ha
    | (cases v <;> first | exact absurd rfl (hv _) | exact absurd rfl (hv' _) |
        (cases b <;> simp <;> rfl))

/-- A written flat value into a flat field or element. -/
theorem dco_flat (env : Env) (b : Bool) (t : SszTy) (v : Value)
    (ht : ∀ ty, t ≠ .container ty) (hl : ∀ k e l, t ≠ .list k e l) (ha : t ≠ .any)
    (hv : ∀ a, v ≠ .ref a) (hv' : ∀ xs, v ≠ .tuple xs) :
    @dCoerce Ssz.model env b t v = lift (if b then coerceField t v else coerceElem t v) := by
  have hc : @coerceWith Ssz.model env b Heap.empty t v =
      (fun x => (x, Heap.empty)) <$> (if b then coerceField t v else coerceElem t v) := by
    cases t <;> first | exact absurd rfl ha | exact absurd rfl (ht _) | exact absurd rfl (hl _ _ _) |
      simp only [coerceWith, LibModel.coerce, Ssz.coerce, depthBound,
        coerceH_flat env b 63 Heap.empty _ v ht hl ha hv hv']
  simp only [dCoerce, hc]
  generalize (if b = true then coerceField t v else coerceElem t v) = r
  cases r <;> rfl

section sumden
open SpecLean.Rd

theorem leafVals_map {α : Type} (f : α → Value) :
    ∀ (xs : List α), leafVals (xs.map fun y => DV.leaf (f y)) = some (xs.map f)
  | [] => rfl
  | x :: xs => by simp [leafVals, leafVals_map f xs]

theorem resolveUint_self (t : UintTy) : resolveUint t t = .ok t := by
  cases t <;> simp [resolveUint]

/-- One checked addition of uints: the interpreter and the readable Lean agree. -/
theorem add_uint_rel {α : Type} [UintC α] (t : UintTy) (ht : t.bits = UintC.bits α) (a : Value) (acc y : α)
    (ha : a = .uint t (UintC.val acc) ∨ (a = .int 0 ∧ UintC.val acc = 0)) :
    PrimRel.ResRel (fun (v : Value) (r : α) => v = .uint t (UintC.val r))
      (@binopVal (@LibModel.toLibValues Ssz.model) .add a (.uint t (UintC.val y)))
      (uOp .add (uv acc) (uv y)) := by
  have hb : @binopVal (@LibModel.toLibValues Ssz.model) .add a (.uint t (UintC.val y)) =
      wrapUint t ((UintC.val acc : Int) + UintC.val y) := by
    rcases ha with rfl | ⟨rfl, h0⟩
    · rw [bv_uu, resolveUint_self]; rfl
    · rw [bv_iu, h0]; simp [intArith]
  rw [hb]
  unfold wrapUint uOp uOf
  by_cases hc : (0 : Int) ≤ ↑(UintC.val acc) + ↑(UintC.val y) ∧ ↑(UintC.val acc) + ↑(UintC.val y) < (2 : Int) ^ UintC.bits α
  · have hc' : (0 : Int) ≤ ↑(UintC.val acc) + ↑(UintC.val y) ∧ ↑(UintC.val acc) + ↑(UintC.val y) < (2 : Int) ^ t.bits := by
      rw [ht]; exact hc
    simp [erase, intArith, uv, Except.mapError, hc, hc', PrimRel.ResRel, UintC.val_ofNat, pure, Except.pure]
  · have hc' : ¬ ((0 : Int) ≤ ↑(UintC.val acc) + ↑(UintC.val y) ∧ ↑(UintC.val acc) + ↑(UintC.val y) < (2 : Int) ^ t.bits) := by
      rw [ht]; exact hc
    simp [erase, intArith, uv, Except.mapError, hc, hc', PrimRel.ResRel, SpecError.fail]

theorem resRel_mono {α β : Type} {R S : α → β → Prop} {x : Res α} {y : SpecM β} (h : PrimRel.ResRel R x y)
    (hs : ∀ a b, R a b → S a b) : PrimRel.ResRel S x y := by
  rcases x with e | a <;> rcases y with e' | b
  · exact h
  · exact h.elim
  · exact h.elim
  · exact hs a b h

theorem fold_rel {α : Type} [UintC α] (t : UintTy) (ht : t.bits = UintC.bits α) :
    ∀ (ys : List α) (a : Value) (acc : α), (a = .uint t (UintC.val acc) ∨ (a = .int 0 ∧ UintC.val acc = 0)) →
      PrimRel.ResRel (fun (v : Value) (r : α) => v = .uint t (UintC.val r) ∨ (ys = [] ∧ v = a ∧ r = acc))
        ((ys.map fun y => Value.uint t (UintC.val y)).foldlM (@binopVal (@LibModel.toLibValues Ssz.model) .add) a)
        (sumU acc ys)
  | [], a, acc, ha => by
    simp only [List.map_nil, List.foldlM_nil, sumU, Prim.sum]
    show PrimRel.ResRel _ (.ok a) (.ok acc)
    exact .inr ⟨trivial, rfl, rfl⟩
  | y :: ys, a, acc, ha => by
    simp only [List.map_cons, List.foldlM_cons, sumU, Prim.sum, List.foldlM_cons]
    refine PrimRel.ResRel.bind (add_uint_rel t ht a acc y ha) fun v r hvr => ?_
    have := fold_rel t ht ys v r (.inl hvr)
    unfold sumU Prim.sum at this
    refine resRel_mono this fun v' r' h => ?_
    rcases h with h | ⟨-, rfl, rfl⟩
    · exact .inl h
    · exact .inl hvr

/-- `sum` of the uints of a list: the readable checked sum. An empty sum is the `int` 0. -/
theorem sum_den {α : Type} [UintC α] (t : UintTy) (ht : t.bits = UintC.bits α) (ys : List α)
    {γ : Type} (K : DRes → DM γ) :
    Option.map (Except.mapError SpecError.fail)
        (DM.bind (@dSum Ssz.model .pyList .any (ys.map fun y => DV.leaf (.uint t (UintC.val y)))) K) =
      callK (sumU (UintC.ofNat 0) ys) fun r =>
        Option.map (Except.mapError SpecError.fail)
          (K (.val (if ys = [] then .int 0 else .uint t (UintC.val r)))) := by
  have hr := fold_rel t ht ys (.int 0) (UintC.ofNat 0) (.inr ⟨rfl, UintC.val_ofNat 0⟩)
  unfold dSum
  simp only [isByteList, decide_eq_true_eq]
  rw [if_neg (by simp), leafVals_map]
  show Option.map _ (DM.bind (DM.bind (lift _) _) K) = _
  revert hr
  have hf : ((fun y => Value.uint t (UintC.val y)) : α → Value) = (fun y => Value.uint t (UintC.val y)) := rfl
  cases hx : (ys.map fun y => Value.uint t (UintC.val y)).foldlM (@binopVal (@LibModel.toLibValues Ssz.model) .add) (.int 0) <;>
    cases hs : sumU (UintC.ofNat 0 : α) ys <;> simp only [PrimRel.ResRel] <;> intro h
  · obtain ⟨hne, rfl⟩ := h
    simp [lift, hne, DM.bind, callK, Except.mapError]
  · exact h.elim
  · exact h.elim
  · rename_i w r
    have hfl : Flat w = true := by rcases h with rfl | ⟨-, rfl, -⟩ <;> rfl
    have hw : w = (if ys = [] then .int 0 else .uint t (UintC.val r)) := by
      rcases h with rfl | ⟨rfl, rfl, rfl⟩
      · by_cases hy : ys = []
        · subst hy; simp [sumU, Prim.sum] at hx
        · simp [hy]
      · simp
    simp [Function.comp_def, hx, lift, DM.bind, DM.ok, callK, hfl, ← hw]

theorem sumU_nil {α : Type} [UintC α] (a : α) : sumU a [] = .ok a := Eq.trans rfl rfl

theorem sum_den_v {α : Type} [UintC α] (t : UintTy) (ht : t.bits = UintC.bits α) (v : α → Nat)
    (hv : ∀ y, v y = UintC.val y) (ys : List α) {γ : Type} (K : DRes → DM γ) :
    Option.map (Except.mapError SpecError.fail)
        (DM.bind (@dSum Ssz.model .pyList .any (ys.map fun y => DV.leaf (.uint t (v y)))) K) =
      if ys = [] then Option.map (Except.mapError SpecError.fail) (K (.val (.int 0)))
      else callK (sumU (UintC.ofNat 0) ys) fun r =>
        Option.map (Except.mapError SpecError.fail) (K (.val (.uint t (UintC.val r)))) := by
  have : v = UintC.val := funext hv
  subst this
  rw [sum_den t ht ys K]
  by_cases hy : ys = []
  · subst hy; simp [sumU, Prim.sum, callK]
  · simp only [hy, if_false]

end sumden

end model

section env

/-- The parts of `Scope.env` that the rules read. `Scope.env` itself stays folded, so the
callee lemmas, which name it, still match. -/
theorem env_globals (o : Oracle) : (Scope.env o).globals = Scope.globals := Eq.trans rfl rfl
theorem env_containers (o : Oracle) : (Scope.env o).containers = Scope.containers := Eq.trans rfl rfl
theorem env_config (o : Oracle) : (Scope.env o).config = Scope.config := Eq.trans rfl rfl
theorem env_bytesName (o : Oracle) : (Scope.env o).bytesName = 0 := Eq.trans rfl rfl
/-- `xs[-1]`: the index after `normIndex` or `pyIndex`. -/
theorem fmod_natCast (a b : Nat) : (a : Int).fmod (b : Int) = ((a % b : Nat) : Int) := by
  rw [Int.fmod_eq_emod_of_nonneg _ (by omega)]; omega
theorem fdiv_natCast (a b : Nat) : (a : Int).fdiv (b : Int) = ((a / b : Nat) : Int) := by
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega)]; omega
theorem toNat_neg1_add (n : Nat) : (-1 + (n : Int)).toNat = n - 1 := by omega
theorem getElem?_len_sub_one {α : Type} (xs : List α) (h : xs.length ≠ 0) :
    xs[xs.length - 1]? = some (xs[xs.length - 1]'(by omega)) :=
  List.getElem?_eq_getElem _

theorem env_root (o : Oracle) : (Scope.env o).nm.root = Scope.Id.«Root» := Eq.trans rfl rfl
theorem env_bls (o : Oracle) : (Scope.env o).bls = o.bls := Eq.trans rfl rfl
theorem env_fromBytes (o : Oracle) : (Scope.env o).nm.fromBytes = 94 := Eq.trans rfl rfl
theorem env_little (o : Oracle) : (Scope.env o).nm.little = "little" := Eq.trans rfl rfl
theorem env_bytes32 (o : Oracle) : (Scope.env o).nm.bytes32 = 505 := Eq.trans rfl rfl
theorem env_sha256 (o : Oracle) : (Scope.env o).sha256 = o.sha256 := Eq.trans rfl rfl
theorem env_append (o : Oracle) : (Scope.env o).nm.append = Scope.Id.«append» := Eq.trans rfl rfl

end env

/-- One pass of the generated proofs: the `den` steps, the locals, the globals, the value rules,
the readable rules, and the pushes of `bind` and `map` into an `if`. `l4_simp` holds the rewrites of
the classes and of the proved callees. -/
syntax "l4_eval" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
/-- `l4_eval` that also rewrites with the hypotheses. -/
syntax "l4_eval_star" : tactic

macro_rules
  | `(tactic| l4_eval $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| simp only [l4_simp, s_name, s_int, s_bool, s_noneLit, s_attr, s_index, s_binop, s_compare,
      s_boolop, s_not, s_unop, s_slice, optOf, getSlice, sliceRange, sliceBound,
      Rd.sliceBound', List.extract_eq_take_drop, s_ifExp, s_comp, s_call, s_callStep, appendOf, Expr.call.injEq, s_append, env_append, appendItemD, appendable_list_cont, appendable_plist_cont, appendable_list_nom, appendable_plist_nom, appendable_list_bytes, appendable_plist_bytes, Ssz.checkLength, Rd.lappend, s_assign, s_annAssign, s_exprStmt,
      s_augAssign, s_augName, augName, s_iter_attr, s_iter_name, s_iter_enum, isEnumerate, listPlace, s_ifStmt, s_ret, s_retNone, s_assert, s_pass, s_forStmt, s_tname, s_tattr,
      s_tindex, b_nil, b_cons, initLoc, List.zipIdx_cons, List.zipIdx_nil, slot,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.length_cons, List.length_nil, setLoc,
      dGlobal, env_globals, env_containers, env_config, env_bytesName,
      Validation.Tactic.lookup_lit, Validation.Tactic.fieldIndex_lit, ↓reduceIte,
      DM.ok, flat_int, flat_bool, flat_lib, flat_none, flat_bytes, flat_str, Nat.reduceEqDiff, dBinop, resolveUint,
      intArith, wrapUint, UintTy.bits, eb_ite, eb_okp, eb_errp, lift_ite, lift_okp, lift_errp, dm_ite,
      GenLemmas.dmb_okp, GenLemmas.dmb_errp, GenLemmas.dmb_okd, map_ite, Option.map_some, if_true,
      if_false, and_self, and_true, true_and, ne_eq, reduceCtorEq, not_false_eq_true, some_ite,
      uv_ofNat, Rd.uOp, Rd.uOf, Rd.erase, Rd.uv, emap_ite, emap_ok, emap_err,
      merr_ok, merr_err, epure, ethrow, ebind_pure, SpecError.fail, callHead, callable, Option.isNone,
      Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.not_true, Bool.not_false,
      argsOf, dCallRO, dCallW, allKw_nil, allKw_pos, allKw_starred, allKw_kw, kwsOf, kwCtor,
      kwFields, flatTy, Bool.and_self, List.all_cons, List.all_nil, List.contains_cons, List.contains_nil,
      List.lookup_cons, List.lookup_nil, List.map_cons, List.map_nil, Bool.or_self, Bool.true_or, dmb_none, Int.reduceAbs, Nat.reduceLeDiff, Int.reduceEq,
      Int.reduceLT, Int.reduceLE, Int.reducePow, Nat.reducePow, Int.reduceToNat, dCtor, ctorFlat, allVals, argRoot, merr_ite, eb_assoc, dm_assoc, Int.natCast_eq_zero, List.mapM_cons, List.mapM_nil,
      Validation.Steps.construct_uint_int, Validation.Steps.construct_uint_uint,
      Validation.Steps.construct_uint_boolean, cons_bool, cons_boolean, cons_bytes, cons_bytes_nil, exm_ok, exm_err, omap_bind, bv_uu, bv_ui, bv_iu, bv_ii, cv_uu, cv_ui, cv_iu, cv_ii, cv_bytes, bv_bytes, cv_boolean, tv_bool,
      tv_boolean, tv_uint, tv_int, tv_none, tv_bytes, uv_neg, uv_inv, uv_negi, iv_uint, iv_int,
      pyCmp, cmpF, cmpOf, cmpInt, boolOf, List.isEmpty_cons,
      List.isEmpty_nil, dAttr, DSt.deref, subAt, DV.kids, ofChild, List.nil_append,
      List.cons_append, dIndex, isByteList, normIndex, List.getElem?_map, List.getElem_map,
      List.length_map, Option.bind_some, dBuiltin, dco_flat, implies_true, coerceField, coerceElem,
      UintTy.subOf, dWriteD, dWrite, fpOk, rootIs, matchesB, leafAt, updAt, setAt, List.any_cons,
      List.any_nil, Bool.or_false, Bool.or_true, Bool.false_or, Bool.true_or, beq_self_eq_true, Nat.reduceBEq, List.set_cons_zero, List.set_cons_succ,
      coversAll, coversB, genB, List.all_cons, List.all_nil, onePlace, decide_false, decide_true, Bool.false_eq_true,
      false_and, and_false, natCast_lt_zero, Int.toNat_natCast, Int.ofNat_lt, Rd.lget, Rd.lset, Rd.assert, Rd.assertBug, Rd.pyIndex, augStep,
      Rd.lslice, Rd.bd, Option.map_none, ob_some, ob_none, ob_ite, opure, setLoc_same, fite_app, dst_loc_ite, rd_bind, callK_ok, callK_err, callK_ite, callK_bind, callK_pure, Nat.zero_add, bmin_max, bmax_max, pickBest, flat_ite, val_ite,
      Rd.pyMin, Rd.pyMax, Rd.toLE, env_bytes32, env_sha256, fmod_natCast, fdiv_natCast, sum_den_v, sumU_nil, padNone, Nat.reduceAdd, Nat.reduceSub, Nat.le_refl, Nat.reduceLeDiff, List.replicate_zero, List.replicate_succ, List.append_nil, Rd.bytesOf, isVal, noneDefaults, isNoneLit, List.isEmpty_cons, List.isEmpty_nil, env_root, fromBytesOf, s_fromBytes, blsOf, s_bls, dBls, env_bls, dFromBytes, fromBytes, env_fromBytes, env_little, PrimRel.fromLE_eq_prim, bne_iff_ne, Bool.not_eq_true', beq_eq_false_iff_ne, Int.natCast_eq_zero, toNat_neg1_add, getElem?_len_sub_one, Option.map_none, Prim.pick, Id.run_bind, Id.run_pure, ite_self, List.foldl_cons, List.foldl_nil, Int.ofNat_eq_natCast, getD_ite, Option.getD_some, Option.getD_none, Rd.uCast, Rd.iOp, $extra,*])
  | `(tactic| l4_eval_star) => `(tactic| simp only [*, List.getElem?_eq_getElem, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq, DRes.val.injEq, DV.leaf.injEq, l4_simp, s_name, s_int, s_bool, s_noneLit, s_attr, s_index, s_binop, s_compare,
      s_boolop, s_not, s_unop, s_slice, optOf, getSlice, sliceRange, sliceBound,
      Rd.sliceBound', List.extract_eq_take_drop, s_ifExp, s_comp, s_call, s_callStep, appendOf, Expr.call.injEq, s_append, env_append, appendItemD, appendable_list_cont, appendable_plist_cont, appendable_list_nom, appendable_plist_nom, appendable_list_bytes, appendable_plist_bytes, Ssz.checkLength, Rd.lappend, s_assign, s_annAssign, s_exprStmt,
      s_augAssign, s_augName, augName, s_iter_attr, s_iter_name, s_iter_enum, isEnumerate, listPlace, s_ifStmt, s_ret, s_retNone, s_assert, s_pass, s_forStmt, s_tname, s_tattr,
      s_tindex, b_nil, b_cons, initLoc, List.zipIdx_cons, List.zipIdx_nil, slot,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.length_cons, List.length_nil, setLoc,
      dGlobal, env_globals, env_containers, env_config, env_bytesName,
      Validation.Tactic.lookup_lit, Validation.Tactic.fieldIndex_lit, ↓reduceIte,
      DM.ok, flat_int, flat_bool, flat_lib, flat_none, flat_bytes, flat_str, Nat.reduceEqDiff, dBinop, resolveUint,
      intArith, wrapUint, UintTy.bits, eb_ite, eb_okp, eb_errp, lift_ite, lift_okp, lift_errp, dm_ite,
      GenLemmas.dmb_okp, GenLemmas.dmb_errp, GenLemmas.dmb_okd, map_ite, Option.map_some, if_true,
      if_false, and_self, and_true, true_and, ne_eq, reduceCtorEq, not_false_eq_true, some_ite,
      uv_ofNat, Rd.uOp, Rd.uOf, Rd.erase, Rd.uv, emap_ite, emap_ok, emap_err,
      merr_ok, merr_err, epure, ethrow, ebind_pure, SpecError.fail, callHead, callable, Option.isNone,
      Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.not_true, Bool.not_false,
      argsOf, dCallRO, dCallW, allKw_nil, allKw_pos, allKw_starred, allKw_kw, kwsOf, kwCtor,
      kwFields, flatTy, Bool.and_self, List.all_cons, List.all_nil, List.contains_cons, List.contains_nil,
      List.lookup_cons, List.lookup_nil, List.map_cons, List.map_nil, Bool.or_self, Bool.true_or, dmb_none, Int.reduceAbs, Nat.reduceLeDiff, Int.reduceEq,
      Int.reduceLT, Int.reduceLE, Int.reducePow, Nat.reducePow, Int.reduceToNat, dCtor, ctorFlat, allVals, argRoot, merr_ite, eb_assoc, dm_assoc, Int.natCast_eq_zero, List.mapM_cons, List.mapM_nil,
      Validation.Steps.construct_uint_int, Validation.Steps.construct_uint_uint,
      Validation.Steps.construct_uint_boolean, cons_bool, cons_boolean, cons_bytes, cons_bytes_nil, exm_ok, exm_err, omap_bind, bv_uu, bv_ui, bv_iu, bv_ii, cv_uu, cv_ui, cv_iu, cv_ii, cv_bytes, bv_bytes, cv_boolean, tv_bool,
      tv_boolean, tv_uint, tv_int, tv_none, tv_bytes, uv_neg, uv_inv, uv_negi, iv_uint, iv_int,
      pyCmp, cmpF, cmpOf, cmpInt, boolOf, List.isEmpty_cons,
      List.isEmpty_nil, dAttr, DSt.deref, subAt, DV.kids, ofChild, List.nil_append,
      List.cons_append, dIndex, isByteList, normIndex, List.getElem?_map, List.getElem_map,
      List.length_map, Option.bind_some, dBuiltin, dco_flat, implies_true, coerceField, coerceElem,
      UintTy.subOf, dWriteD, dWrite, fpOk, rootIs, matchesB, leafAt, updAt, setAt, List.any_cons,
      List.any_nil, Bool.or_false, Bool.or_true, Bool.false_or, Bool.true_or, beq_self_eq_true, Nat.reduceBEq, List.set_cons_zero, List.set_cons_succ,
      coversAll, coversB, genB, List.all_cons, List.all_nil, onePlace, decide_false, decide_true, Bool.false_eq_true,
      false_and, and_false, natCast_lt_zero, Int.toNat_natCast, Int.ofNat_lt, Rd.lget, Rd.lset, Rd.assert, Rd.assertBug, Rd.pyIndex, augStep,
      Rd.lslice, Rd.bd, Option.map_none, ob_some, ob_none, ob_ite, opure, setLoc_same, fite_app, dst_loc_ite, rd_bind, callK_ok, callK_err, callK_ite, callK_bind, callK_pure, Nat.zero_add, bmin_max, bmax_max, pickBest, flat_ite, val_ite,
      Rd.pyMin, Rd.pyMax, Rd.toLE, env_bytes32, env_sha256, fmod_natCast, fdiv_natCast, sum_den_v, sumU_nil, padNone, Nat.reduceAdd, Nat.reduceSub, Nat.le_refl, Nat.reduceLeDiff, List.replicate_zero, List.replicate_succ, List.append_nil, Rd.bytesOf, isVal, noneDefaults, isNoneLit, List.isEmpty_cons, List.isEmpty_nil, env_root, fromBytesOf, s_fromBytes, blsOf, s_bls, dBls, env_bls, dFromBytes, fromBytes, env_fromBytes, env_little, PrimRel.fromLE_eq_prim, bne_iff_ne, Bool.not_eq_true', beq_eq_false_iff_ne, Int.natCast_eq_zero, toNat_neg1_add, getElem?_len_sub_one, Option.map_none, Prim.pick, Id.run_bind, Id.run_pure, ite_self, List.foldl_cons, List.foldl_nil, Int.ofNat_eq_natCast, getD_ite, Option.getD_some, Option.getD_none, Rd.uCast, Rd.iOp] at *)

/-- The side conditions of a loop lemma: fuel, and the locals of the parameters. -/
macro "l4_disch" : tactic => `(tactic| first
  | omega
  | (simp only [setLoc, ↓reduceIte, Nat.reduceEqDiff]; done)
  | (simp only [setLoc, ↓reduceIte, Nat.reduceEqDiff]; assumption)
  | assumption
  | (simp only [List.length_cons, List.length_nil, List.length_replicate, Nat.reduceAdd]; done))

open Lean Meta Elab Tactic in
/-- `by_cases` on the condition of the first `if` in the goal whose condition does not depend
on a bound variable. -/
elab "l4_bycases" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let some e := tgt.find? (fun e => (e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5) &&
      !(e.getArg! 1).hasLooseBVars && !(e.getArg! 1).hasMVar)
    | throwError "l4_bycases: no condition"
  let c ← Term.exprToSyntax (e.getArg! 1)
  evalTactic (← `(tactic| by_cases $(mkIdent `hc) : $c))

/-- The end of a generated proof: case split on the next condition (or the next `match`, or
the next callee result), evaluate again with the new hypothesis, and close each case by `rfl`,
`simp_all` or `omega`. -/
syntax "l4_close" : tactic

macro_rules
  | `(tactic| l4_close) => `(tactic| first
    | with_reducible rfl
    | ((l4_bycases <;> (try l4_eval_star) <;> (try subst_vars) <;> (try l4_eval_star)) <;> l4_close)
    | ((split <;> (try l4_eval_star) <;> (try subst_vars) <;> (try l4_eval_star)) <;> l4_close)
    | ((refine callK_congr _ fun _ => ?_) <;> (try l4_eval_star) <;> l4_close)
    | (simp_all [-den_expr, -den_stmt, -den_call, -den_fn, -den_target, -den_iter, -den_loop,
        -den_items]; done)
    | (simp_all [-den_expr, -den_stmt, -den_call, -den_fn, -den_target, -den_iter, -den_loop,
        -den_items] <;> omega)
    | omega)

/-- `l4_close` that leaves the cases it cannot close: case split on the next condition (or the next `match`, or
the next callee result), evaluate again with the new hypothesis, and close each case by `rfl`,
`simp_all` or `omega`. -/
syntax "l4_dbg" : tactic

macro_rules
  | `(tactic| l4_dbg) => `(tactic| first
    | with_reducible rfl
    | ((l4_bycases <;> (try l4_eval_star) <;> (try subst_vars) <;> (try l4_eval_star)) <;> l4_dbg)
    | ((split <;> (try l4_eval_star) <;> (try subst_vars) <;> (try l4_eval_star)) <;> l4_dbg)
    | ((refine callK_congr _ fun _ => ?_) <;> (try l4_eval_star) <;> l4_dbg)
    | (simp_all [-den_expr, -den_stmt, -den_call, -den_fn, -den_target, -den_iter, -den_loop,
        -den_items]; done)
    | (simp_all [-den_expr, -den_stmt, -den_call, -den_fn, -den_target, -den_iter, -den_loop,
        -den_items] <;> omega)
    | omega
    | skip)

end SpecLean.Layer4.GenSteps

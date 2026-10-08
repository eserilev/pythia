import Lean

/-- Definitions that the bridge proofs unfold: the `abs_T` maps, the `IR_T` predicates and the
constants of both models. -/
register_simp_attr bridge_simp

/-- The `IR_T` predicates, for range side goals. -/
register_simp_attr bridge_ir

/-- The checks that a readable constant equals the hand constant. -/
register_simp_attr bridge_const

/-- Casts between `Int` and `Nat` in the pure goals. -/
register_simp_attr bridge_cast

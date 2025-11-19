import extraction.Gcd
open Std.Do
open Std.Tactic

@[spec]
theorem Rust_primitives.Hax.while_loop.spec {State: Type}
  (cond: State → Result Bool)
  (inv: State → Result Bool)
  (termination : State -> Result Int)
  (init : State)
  (body : State -> Result State) :
  -- inv init = pure true →
  -- (∀ state,
  --   inv state = pure true →
  --   cond state = pure true →
  --   ⦃ ⌜ True ⌝ ⦄
  --   do
  --     let state ← body state
  --     inv state
  --   ⦃ ⇓ isInvTrue => ⌜ isInvTrue ⌝ ⦄) →
  (∀ state,
    ⦃ ⌜ True ⌝ ⦄
    do
      if ← cond state then
        let state' ← body state
        let m ← termination state
        let m' ← termination state'
        pure (some (m, m'))
      else
        pure none
    ⦃ ⇓ r => ⌜ match r with
      | none => True
      | some (m, m') => (0 ≤ m' ∧ m' < m) ⌝ ⦄) →
  ⦃ ⌜ True ⌝ ⦄
  Rust_primitives.Hax.while_loop cond inv termination init body
  ⦃ ⇓ r => ⌜ True ⌝ ⦄ := by sorry


@[spec]
theorem Hax.rem (a:u8) (b:u8) (hb :b ≠ 0) :
  ⦃ ⌜ True ⌝ ⦄
  (a %? b)
  ⦃ ⇓ r => ⌜ r < b ⌝ ⦄
  := sorry


theorem Gcd.euclid_u8.spec (a:u8) (b:u8) :
  ⦃ ⌜ True ⌝ ⦄
  (euclid_u8 a b)
  ⦃ ⇓ r => ⌜ True ⌝ ⦄
  := by
  mvcgen (stepLimit := none) [euclid_u8]
  · grind
  · constructor
    apply Int.zero_le_ofNat
    exact Int.lt_of_toNat_lt (by assumption)
  · grind
  · constructor
    apply Int.zero_le_ofNat
    exact Int.lt_of_toNat_lt (by assumption)

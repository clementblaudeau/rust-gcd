import extraction.Gcd
open Std.Do
open Std.Tactic

@[spec]
theorem Rust_primitives.Hax.while_loop.spec {State: Type}
  (cond: State → Result Bool)
  (cond' : State → Bool)
  (inv: State → Result Bool)
  (inv': State → Bool)
  (termination : State -> Result Int)
  (init : State)
  (body : State -> Result State)
  (inv_inv' : ∀ state,
    ⦃ ⌜ True ⌝ ⦄
    inv state
    ⦃ ⇓? r => ⌜ r = inv' state ⌝ ⦄)
  (cond_cond' : ∀ state,
    ⦃ ⌜ True ⌝ ⦄
    cond state
    ⦃ ⇓? r => ⌜ r = cond' state ⌝ ⦄)
  (inv_init :
    ⦃ ⌜ True ⌝ ⦄
    inv init
    ⦃ ⇓ r => ⌜ r = true ⌝ ⦄)
  (cond_init :
    ⦃ ⌜ True ⌝ ⦄
    cond init
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄)
  (step : ∀ state,
    inv' state →
    cond' state →
    ⦃ ⌜ True ⌝ ⦄
    do
      let state ← body state
      let _ ← cond state
      inv state
    ⦃ ⇓ isInvTrue => ⌜ isInvTrue ⌝ ⦄)
  (decreases : ∀ state,
    inv' state →
    cond' state →
    ⦃ ⌜ True ⌝ ⦄
    do
      let state' ← body state
      let m ← termination state
      let m' ← termination state'
      pure (m, m')
    ⦃ ⇓ (m, m') => ⌜ 0 ≤ m' ∧ m' < m ⌝ ⦄) :
  ⦃ ⌜ True ⌝ ⦄
  Rust_primitives.Hax.while_loop cond inv termination init body
  ⦃ ⇓ state' => ⌜ inv' state' = true ∧ cond' state' = false ⌝ ⦄ := by sorry


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
  · grind
  · constructor
    apply Int.zero_le_ofNat
    exact Int.lt_of_toNat_lt (by assumption)
  · grind
  · grind
  · constructor
    apply Int.zero_le_ofNat
    exact Int.lt_of_toNat_lt (by assumption)

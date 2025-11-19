import extraction.Gcd
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

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


abbrev panic_free {α : Type} (f : Result α) := ⦃ ⌜ True ⌝ ⦄ f ⦃ ⇓ _ => ⌜ True ⌝ ⦄

theorem Rust_primitives.Hax.while_loop.spec2 {State: Type}
  (cond: State → Result Bool)
  (inv: State → Result Bool)
  (termination : State -> Result Int)
  (init : State)
  (body : State -> Result State)
  (inv_init_true :
    ⊢ₛ wp⟦ inv init ⟧ (⇓ r => ⌜ ↑r ⌝ ))
  (inv_implies_cond_pf : ∀ state,
    ⊢ₛ wp⟦ inv state ⟧ ( ⇓ r => ⌜ r → panic_free (cond state) ⌝ ))
  (step : ∀ state,
    ⊢ₛ wp⟦ inv state ⟧ post⟨
      fun r => ⌜ r → ⊢ₛ wp⟦
        do
          if (← cond state) then
            let state' ← (body state)
            let m ← (termination state)
            let m' ← (termination state')
            pure ((← inv state') ∧ 0 ≤ m' ∧ m' < m)
          else
            pure true
        ⟧ ( ⇓ r => ⌜ ↑r ⌝) ⌝ ,
      fun _ => ⌜ True ⌝ -- if the invariant panics, nothing to do
      ⟩) :
  ⦃ ⌜ True ⌝ ⦄
  Rust_primitives.Hax.while_loop cond inv termination init body
  ⦃ ⇓ state' => ⌜
    (⊢ₛ wp⟦inv state'⟧ (⇓ r => ⌜ r ⌝)) ∧
    (⊢ₛ wp⟦cond state'⟧ ( ⇓ r => ⌜ ¬r ⌝))⌝ ⦄ := by sorry



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
  mvcgen [euclid_u8, Rust_primitives.Hax.while_loop.spec2, panic_free]
  <;> try mvcgen
  <;> simp
  <;> try grind
  . apply UInt8.lt_iff_toNat_lt.mp
    omega
  . apply UInt8.lt_iff_toNat_lt.mp
    omega

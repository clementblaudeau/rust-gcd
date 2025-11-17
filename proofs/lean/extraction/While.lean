
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic
open Lean

section
/- The following instances are required to use `partial_fixpoint` in the `Result` monad. -/

open Order
instance : PartialOrder (Result α) := inferInstanceAs (PartialOrder (FlatOrder Result.div))
noncomputable instance : CCPO (Result α) := inferInstanceAs (CCPO (FlatOrder Result.div))
noncomputable instance : MonoBind Result where
  bind_mono_left h := by
    cases h
    · exact FlatOrder.rel.bot
    · exact FlatOrder.rel.refl
  bind_mono_right h := by
    cases ‹Result _›
    · exact h _
    · exact FlatOrder.rel.refl
    · exact FlatOrder.rel.refl

end section

/-- Our own copy of `Loop.forIn` because the original one is `partial` and thus we cannot reason
about it. -/
@[inline]
def Loop.forIn {β : Type} (_ : Loop) (init : β) (f : Unit → β → Result (ForInStep β)) : Result β :=
  let rec @[specialize] loop (b : β) : Result β := do
    match ← f () b with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop b
  partial_fixpoint
  loop init

@[spec]
theorem Spec.ForInStep.casesOn_spec {α β: Type} (x y : α → Result β) (s : ForInStep α)
  (P : Assertion (PostShape.except Error PostShape.pure))
  (Q : PostCond β (PostShape.except Error PostShape.pure))
  (hP : ∀ a, ForInStep.casesOn s (fun _ => Triple (x a) P Q) (fun _ => Triple (y a) P Q)) :
  Triple
    (ForInStep.casesOn s x y : Result β)
    P
    Q := by
cases s <;> simp [hP]

theorem SPred.entails_and (P Q : α → SPred ps.args) (m : Type u → Type v) [WP m ps] (x : m α)
  (hP : I ⊢ₛ wp⟦x⟧ (fun a => P a, R))
  (hQ : I ⊢ₛ wp⟦x⟧ (fun a => Q a, R))
  :
  I ⊢ₛ wp⟦x⟧ (fun a => spred(P a ∧ Q a), R) := sorry

#reduce    Assertion (PostShape.except Error PostShape.pure)

def inv2 : ExceptConds (.except Error .pure) :=  (fun (e : Error) => ULift.up True, ())


theorem pull_precondition (m : Type u → Type v) [WP m ps] (x : m α):
(P → ⦃⌜ True ⌝⦄ x ⦃ Q ⦄) → ⦃⌜ P ⌝⦄ x ⦃ Q ⦄
 := sorry

 #check SPred.and

@[spec]
theorem Spec.forIn_loop {β : Type}
    (init: β) (f : Unit → β → Result (ForInStep β))
    (termination : β → Nat)
    (decreases : ∀ a b, f () b = .ok (.yield a) → termination a < termination b)
    (hdiv : ∀ b, f () b ≠ .div)
    (inv : β → Prop)
    (inv_init : inv init)
    (step: ∀ b (hb : inv b),
      Triple
        (f () b)
        (⌜ True ⌝)
        (fun r => ULift.up (inv r.value), inv2)) :
    Triple (Loop.forIn.loop f init) (⌜ True ⌝) (fun b => ⌜ inv b ⌝, inv2) := by
have hf : Triple (f () init) (⌜ True ⌝) (fun a => spred((ULift.up (f () init = .ok a)) ∧ (⌜ inv a.value ⌝)), inv2) := by
  apply SPred.entails_and
  · have := hdiv init
    revert this
    cases (f () init) <;> simp [inv2]
  · apply step
    apply inv_init
unfold Loop.forIn.loop
apply SPred.entails.trans hf
simp only [WP.bind]
apply (wp (f () init)).mono _ _
simp only [PostCond.entails, Assertion, ExceptConds.entails.refl, and_true]
intro b
unfold Loop.forIn.loop.match_1
cases b
case done a =>
  simp
case yield a =>
  refine pull_precondition Result (ForInStep.casesOn (ForInStep.yield a) (fun a => (fun b => pure b) a) fun a => (fun b => Loop.forIn.loop f b) a) ?_
  intro h
  exact Spec.forIn_loop a f termination decreases hdiv inv h.2 step
-- apply Spec.ForInStep.casesOn_spec
-- intro a
-- cases b
termination_by termination init
decreasing_by
  apply decreases
  apply h.1

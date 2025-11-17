
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic
open Lean

-- This is needed to use `partial_fixpoint`.
-- check https://github.com/leanprover/lean4/blob/cdd38ac5115bdeec5f609e9126cce00f51ae88b3/src/Init/Internal/Order/Basic.lean#L33-L50
open Order
instance : PartialOrder (Result α) := inferInstanceAs (PartialOrder (FlatOrder Result.div))
noncomputable instance : CCPO (Result α) := inferInstanceAs (CCPO (FlatOrder Result.div))
noncomputable instance : MonoBind Result where
  bind_mono_left h := by
    cases h
    · exact FlatOrder.rel.bot
    · exact FlatOrder.rel.refl
  bind_mono_right h := by
    -- cases ‹Result _›
    -- · exact FlatOrder.rel.refl
    -- · exact h _
    sorry

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

@[spec]
theorem Spec.forIn_loop {β : Type}
    (init: β) (f : Unit → β → Result (ForInStep β))
    (termination : β → Nat)
    (decreases : ∀ a b, f () b = .ok (.yield a) → termination b < termination a)
    {inv : PostCond β (.except Error .pure)}
    (step: ∀ b,
      Triple
        (f () b)
        (inv.1 b)
        (fun r => match r with
          | .yield b' => inv.1 b'
          | .done b' => inv.1 b', inv.2)) :
    Triple (Loop.forIn.loop f init) (inv.1 init) inv := by
unfold Loop.forIn.loop
apply Triple.bind
· apply step
· intro b
  unfold Loop.forIn.loop.match_1
  cases b
  case done a =>
    simp
    sorry

  case yield a =>
    apply Spec.forIn_loop a f termination decreases step
-- apply Spec.ForInStep.casesOn_spec
-- intro a
-- cases b
termination_by termination init
decreasing_by sorry

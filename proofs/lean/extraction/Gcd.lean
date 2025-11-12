
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

class Gcd.Gcd (Self : Type) where
  gcd : (Self -> Self -> Result Self)
  gcd_binary : (Self -> Self -> Result Self)
  gcd_euclid : (Self -> Self -> Result Self)

def Rust_primitives.Hax.Machine_int.bitor {α β γ} [HOr α β γ] (x:α) (y:β) : Result γ := pure (HOr.hOr x y)

def Core.Num.Impl_6.trailing_zeros : u8 -> Result u32 := sorry
instance : HaxShiftRight u8 u32 := sorry
open Rust_primitives

def Hax_lib.Int.Int : Type := _root_.Int
def Hax.Int.from_machine : u32 → Hax_lib.Int.Int := sorry
def Hax.while_loop_cf {State: Type}
  (inv: State → Result Bool)
  (cond: State → Result Bool)
  (termination : State -> Result Hax_lib.Int.Int)
  (init : State)
  (body : State -> Result (Core.Ops.Control_flow.ControlFlow (Hax.Tuple2 Hax.Tuple0 State) State))
  : Result State := sorry

def Hax.while_loop {State: Type}
  (inv: State → Result Bool)
  (cond: State → Result Bool)
  (termination : State -> Result Hax_lib.Int.Int)
  (init : State)
  (body : State -> Result State)
  : Result State := sorry
def Hax.Machine_int.shl : u8 -> u32 -> Result u8 := sorry

-- Const euclid GCD implementation for `u8`.
def Gcd.euclid_u8 (a : u8) (b : u8) : Result u8 := do
  let ⟨a, b⟩ ←
    if (← (Hax.Machine_int.gt a b)) then
      (pure (Hax.Tuple2.mk a b))
    else
      (pure (Hax.Tuple2.mk b a));
  let ⟨a, b⟩ ←
    (Hax.while_loop
      (fun ⟨a, b⟩ => (do
        (Hax.Machine_int.ne b (0 : u8)) : Result Bool))
      (fun ⟨a, b⟩ => (do (pure true) : Result Bool))
      (fun ⟨a, b⟩ => (do
        (Hax.Int.from_machine (0 : u32)) : Result
        Hax_lib.Int.Int))
      (Hax.Tuple2.mk a b)
      (fun ⟨a, b⟩ => (do
        let temp : u8 := a;
        let a : u8 := b;
        let b : u8 := temp;
        let b : u8 ← (b %? a);
        (pure (Hax.Tuple2.mk a b)) : Result
        (Hax.Tuple2 u8 u8))));
  (pure a)

theorem Gcd.euclid_u8.spec (a:u8) (b:u8) :
  ⦃ ⌜ True ⌝ ⦄
  (euclid_u8 a b)
  ⦃ ⇓ r => ⌜ True ⌝ ⦄
  := by
  mvcgen [euclid_u8]

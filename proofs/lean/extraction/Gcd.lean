
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

def Hax_lib.Int.Int : Type := _root_.Int
def Rust_primitives.Hax.while_loop {State: Type}
  (cond: State → Result Bool)
  (inv: State → Result Bool)
  (termination : State -> Result Hax_lib.Int.Int)
  (init : State)
  (body : State -> Result State)
  : Result State := sorry

@[spec, simp]
def Rust_primitives.Hax.Int.from_machine (x : u8) : Hax_lib.Int.Int := Int.ofNat x.toNat

-- Const euclid GCD implementation for `u8`.
def Gcd.euclid_u8 (a : u8) (b : u8) : Result u8 := do
  let ⟨a, b⟩ ←
    if (← (Rust_primitives.Hax.Machine_int.gt a b)) then
      (pure (Rust_primitives.Hax.Tuple2.mk a b))
    else
      (pure (Rust_primitives.Hax.Tuple2.mk b a));
  let ⟨a, b⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨a, b⟩ => (do
        (Rust_primitives.Hax.Machine_int.ne b (0 : u8)) : Result Bool))
      (fun ⟨a, b⟩ => (do (pure true) : Result Bool))
      (fun ⟨a, b⟩ => (do
        (Rust_primitives.Hax.Int.from_machine b) : Result Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk a b)
      (fun ⟨a, b⟩ => (do
        let temp : u8 := a;
        let a : u8 := b;
        let b : u8 := temp;
        let b : u8 ← (b %? a);
        (pure (Rust_primitives.Hax.Tuple2.mk a b)) : Result
        (Rust_primitives.Hax.Tuple2 u8 u8))));
  (pure a)

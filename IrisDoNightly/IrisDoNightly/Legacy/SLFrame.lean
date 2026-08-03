module

public import IrisDoNightly.Legacy.HeapAxioms
import Lean
import Std.Internal
import Std.Tactic.Do
public meta import Lean.Elab.Tactic.Do.Internal.VCGen.FrameProc
public meta import Lean.Meta.Sym.Pattern

set_option mvcgen.warning false
set_option grind.warning false

open Lean Meta Sym Std Std.Internal.Do Lean.Order
open Iris.HeapLang Iris.HeapLang.SL

@[expose] public section

namespace Iris.HeapLang.SL

/-! ## Separation-logic structural lemmas for the frame split -/

theorem sepConj_mono_r {a b b' : HProp} (h : b ⊑ b') : (sepConj a b) ⊑ (sepConj a b') := by
  rintro σ ⟨σ₁, σ₂, hd, rfl, ha, hb⟩; exact ⟨σ₁, σ₂, hd, rfl, ha, h _ hb⟩

theorem sepConj_frame_r {pre₀ F R : HProp} (h : pre₀ ⊑ R) : (sepConj pre₀ F) ⊑ (sepConj F R) :=
  PartialOrder.rel_trans (PartialOrder.rel_of_eq (sepConj_comm pre₀ F)) (sepConj_mono_r h)

@[grind ←] theorem sepConj_comm_le (a b : HProp) : (sepConj a b) ⊑ (sepConj b a) :=
  PartialOrder.rel_of_eq (sepConj_comm a b)

/-! ## The registered frame procedure for `∗` -/

open Lean.Elab.Tactic.Do.Internal Lean.Elab.Tactic.Do.Internal.VCGen

public meta partial def sepAtoms (e : Expr) : Array Expr :=
  if e.isAppOf ``sepConj then sepAtoms e.appFn!.appArg! ++ sepAtoms e.appArg!
  else #[e]

public meta def sepConjFrameProc : FrameInferenceProc := fun i => do
  let frame ← match i.providedFrame? with
    | some f => pure f
    | none => do
        let mut rest := sepAtoms (← i.pre)
        let some specPre ← i.specPre? | return none
        for atom in sepAtoms specPre do
          let some j ← rest.findIdxM? (isDefEqS atom ·) | return none
          rest := rest.eraseIdxIfInBounds j
        if rest.isEmpty then return none
        pure (rest.pop.foldr (fun a acc => mkApp2 (mkConst ``sepConj) a acc) rest.back!)
  return some (← FrameSplit.withDeferredSplitVC i frame)

@[frameproc] public meta def heapFP : FrameProc where
  prog := ``Iris.HeapLang.Exp
  opHead := ``sepConj
  mkOpAppM := fun _ => pure (mkConst ``sepConj)
  mkResourceTy := fun _ => pure (mkConst ``HProp)
  proc := sepConjFrameProc

theorem le_hexists {α : Sort _} {P : HProp} (Q : α → HProp) (a : α) (h : P ⊑ Q a) :
    P ⊑ hexists Q := fun σ hσ => ⟨a, h σ hσ⟩

theorem le_hand_pure {P R : HProp} {φ : Prop} (hφ : φ) (h : P ⊑ R) :
    P ⊑ hand (hpure φ) R := fun σ hσ => ⟨hφ, h σ hσ⟩

-- LEGACY / DISABLED (toolchain nightly-2026-08-02): the `@[frameproc]` API dropped custom
-- lattice-operator registration (the old `FrameProc.op = { head, terminal? }`). `vcgen`'s
-- auto-framing therefore no longer decomposes the `sepConj` split VC, so these demos' `with finish`
-- no longer closes. The `heapFP` procedure and SL lemmas above still compile; restoring auto-framing
-- would need sepConj footprint inference reimplemented as a discharged split-VC proof.
/-
section demos
variable {wp} [HeapLangAxioms wp]

example (l1 l2 : Loc) (a b x : Val) :
    (l1 ↦ a ∗ l2 ↦ b)
      ⊑ wp⟦Exp.store (Exp.ofVal (Val.lit (.loc l1))) (Exp.ofVal x)⟧
        (fun _ => l1 ↦ x ∗ l2 ↦ b) := by
  vcgen [spec_store] with finish

/-- The same goal with the frame supplied explicitly via the `frames` clause. -/
example (l1 l2 : Loc) (a b x : Val) :
    (l1 ↦ a ∗ l2 ↦ b)
      ⊑ wp⟦Exp.store (Exp.ofVal (Val.lit (.loc l1))) (Exp.ofVal x)⟧
        (fun _ => l1 ↦ x ∗ l2 ↦ b) := by
  vcgen [spec_store]
    frames | Exp.store _ _ => (pointsTo l2 b)
    with finish

/-- `alloc` yields a fresh cell holding `v`. -/
example (v : Val) :
    emp ⊑ wp⟦Exp.allocN (Exp.ofVal (Val.lit (.int 1))) (Exp.ofVal v)⟧
      (fun r => hexists fun l => hand (hpure (r = Val.lit (.loc l))) (pointsTo l v)) := by
  vcgen [spec_alloc] with finish

/-- `load` returns the stored value and keeps the cell. -/
example (l : Loc) (w : Val) :
    (l ↦ w) ⊑ wp⟦Exp.load (Exp.ofVal (Val.lit (.loc l)))⟧
      (fun v => hand (hpure (v = w)) (l ↦ w)) := by
  vcgen [spec_load] with finish

/-- A mixed program that `vcgen` drives end to end: `(λ_. ()) (l := b)` — store `b` into `l`, then
return unit — carrying the disjoint cell `k ↦ c` untouched across the (framed) store, then a pure
step. The heap spec is sequenced with a pure value through the application rule; `vcgen` applies the
frame for the store and reduces the pure tail, leaving only a `∗`-commutativity residual that
`finish` closes. -/
example (l k : Loc) (a b c : Val) :
    ((l ↦ a) ∗ (k ↦ c))
      ⊑ wp⟦Exp.app (Exp.rec_ .anon .anon (Exp.ofVal (Val.lit .unit)))
            (Exp.store (Exp.ofVal (Val.lit (.loc l))) (Exp.ofVal b))⟧
        (fun _ => (l ↦ b) ∗ (k ↦ c)) := by
  vcgen [spec_store]
  case vc1 =>
    refine le_hexists _ .anon (le_hexists _ .anon
      (le_hexists _ (Exp.ofVal (Val.lit .unit)) (le_hand_pure rfl ?_)))
    simp only [Exp.subst]
    vcgen with finish
  all_goals grind

end demos
-/

end Iris.HeapLang.SL

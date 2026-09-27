/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.Instances.Lib.WSat
public import Iris.Instances.UPred.Transfinite

/-! # Initial resources (Transfinite Iris)

This file ports the `initial` part of `theories/base_logic/lib/own.v` of Transfinite Iris and
`initial_wsat` of `theories/base_logic/lib/wsat.v`: `initial G P` says that `P` holds for a valid
resource that only uses the ghost names in `G`. Initial propositions are satisfiable, and
initial propositions over disjoint names can be combined. This gives an alternative to allocating
world satisfaction with a basic update (`wsat_alloc`).
-/

@[expose] public noncomputable section

variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris

open OFE CMRA BI

variable {GF : BundledGFunctors}

/-- `P` holds for a valid resource with ghost names in `G` (Rocq: `initial`). -/
def initial (G : GName → Prop) (P : IProp GF) : Prop :=
  ∃ m : IResUR GF, ✓ m ∧ (∀ τ γ, (m τ).car γ ≠ none → G γ) ∧ (UPred.ownM m ⊢ P)

/-- Rocq: `initial_mono`. -/
theorem initial_mono {G : GName → Prop} {P Q : IProp GF} (hPQ : P ⊢ Q) (h : initial G P) :
    initial G Q :=
  let ⟨m, hv, hdom, hP⟩ := h
  ⟨m, hv, hdom, hP.trans hPQ⟩

/-- Rocq: `initial_weaken`. -/
theorem initial_weaken {G₁ G₂ : GName → Prop} {P : IProp GF} (h : initial G₁ P)
    (hG : ∀ γ, G₁ γ → G₂ γ) : initial G₂ P :=
  let ⟨m, hv, hdom, hP⟩ := h
  ⟨m, hv, fun τ γ hγ => hG γ (hdom τ γ hγ), hP⟩

/-- Rocq: `initial_satisfiable`. -/
theorem initial_satisfiable {G : GName → Prop} {P : IProp GF} (h : initial G P) :
    UPred.satisfiable P :=
  let ⟨m, hv, _, hP⟩ := h
  fun _ => ⟨m, hv.validN, hP _ _ (incN_refl m)⟩

/-- Rocq: `initial_alloc`. -/
theorem initial_alloc {F} [RFunctorContractive F] [E : ElemG GF F] (γ : GName)
    (a : F.ap (IProp GF)) (ha : ✓ a) : initial (· = γ) (iOwn γ a) := by
  refine ⟨iSingleton F γ a, valid_iff_validN.mpr fun n τ => ?_, fun τ γ' hne => ?_, .rfl⟩
  · by_cases hτ : τ = E.τ
    · subst hτ
      exact iSingleton_validN_at_E_τ ha.validN
    · exact iSingleton_validN_at_ne hτ
  · by_cases hτ : τ = E.τ
    · subst hτ
      exact Classical.byContradiction fun hγ => hne (iSingleton_free_at_ne hγ)
    · exact absurd (by rw [iSingleton_ne_eq_unit hτ]; rfl) hne

/-- Rocq: `initial_combine`. -/
theorem initial_combine {G₁ G₂ : GName → Prop} {P Q : IProp GF} (h₁ : initial G₁ P)
    (h₂ : initial G₂ Q) (hdisj : ∀ γ, G₁ γ → G₂ γ → False) :
    initial (fun γ => G₁ γ ∨ G₂ γ) iprop(P ∗ Q) := by
  obtain ⟨m₁, hv₁, hd₁, hP⟩ := h₁
  obtain ⟨m₂, hv₂, hd₂, hQ⟩ := h₂
  refine ⟨m₁ • m₂, valid_iff_validN.mpr fun n τ γ => ?_, fun τ γ hne => ?_,
    (UPred.ownM_op m₁ m₂).1.trans (sep_mono hP hQ)⟩
  · have v₁ : ✓{n} ((m₁ τ).car γ) := (hv₁.validN (n := n)) τ γ
    have v₂ : ✓{n} ((m₂ τ).car γ) := (hv₂.validN (n := n)) τ γ
    show ✓{n} ((m₁ • m₂) τ).car γ
    rw [iResUR_op_eval]
    cases e₁ : (m₁ τ).car γ with
    | none => simpa [e₁, CMRA.op, optionOp] using v₂
    | some x₁ =>
      cases e₂ : (m₂ τ).car γ with
      | none => simpa [e₂, CMRA.op, optionOp] using e₁ ▸ v₁
      | some x₂ =>
        exact (hdisj γ (hd₁ τ γ (by simp [e₁])) (hd₂ τ γ (by simp [e₂]))).elim
  · rw [iResUR_op_eval] at hne
    cases e₁ : (m₁ τ).car γ with
    | some => exact .inl (hd₁ τ γ (by simp [e₁]))
    | none =>
      refine .inr (hd₂ τ γ fun e₂ => hne ?_)
      simp [e₁, e₂, CMRA.op, optionOp]

section wsat

open Iris.Std HeapView PartialMap DisjointLeibnizSet DFrac LawfulPartialMap BigSepM

/-- The initial world satisfaction (Rocq: `initial_wsat`). -/
theorem initial_wsat [instWp : WsatGpreS GF] {γ γe γd : GName} (h₁ : γ ≠ γe) (h₂ : γ ≠ γd)
    (h₃ : γe ≠ γd) :
    initial (fun x => (x = γ ∨ x = γe) ∨ x = γd)
      iprop(wsat (W := WsatGS.ofNames (GF := GF) γ γe γd) ∗
        ownE (W := WsatGS.ofNames (GF := GF) γ γe γd) ⊤) := by
  have hI := initial_alloc (E := instWp.inv) γ (Auth (.own 1) ∅) auth_one_valid
  have hE := initial_alloc (E := instWp.enabled) γe (valid ⊤) ⟨⟩
  have hD := initial_alloc (E := instWp.disabled) γd (valid ∅) ⟨⟩
  have h12 := initial_combine hI hE fun x hx hx' => h₁ (hx.symm.trans hx')
  have h123 := initial_combine h12 hD fun x hx hx' => by
    rcases hx with hx | hx
    · exact h₂ (hx.symm.trans hx')
    · exact h₃ (hx.symm.trans hx')
  refine initial_mono ?_ h123
  iintro ⟨⟨H, He⟩, Hd⟩
  isplitr [He]
  · unfold wsat
    iexists ∅
    isplitl
    · iclear Hd
      have H : liftInv (∅ : InvMap (IProp GF)) = ∅ := by
        simp only [liftInv, map_empty]
      rw [invMap, H]
      iassumption
    · iapply bigSepM_empty
      itrivial
  · unfold ownE
    iexact He

end wsat

end Iris

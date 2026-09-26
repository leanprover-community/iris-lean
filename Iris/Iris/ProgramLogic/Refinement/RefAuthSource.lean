/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.ProgramLogic.Refinement.RefSource
public import Iris.Algebra.Auth
public import Iris.Algebra.LocalUpdates

/-! # Authoritative sources (Transfinite Iris)

This file ports the `auth_source` part of `theories/program_logic/refinement/ref_source.v` of
Transfinite Iris: a source whose states live in a discrete unital camera `M` with a transition
relation that is compatible with framing. Its interpretation is the authoritative element
`● a`; fragments `◯ b` (`srcF`) can be used to take source steps locally (`auth_src_update`).
The instances for natural numbers and ordinals (time credits) are not ported yet.
-/

@[expose] public noncomputable section

variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris.Transfinite

open Iris Iris.Std Iris.BI OFE CMRA Relation

/-- An authoritative source with its ghost state (Rocq: `auth_source` and `auth_sourceG`): a
transition relation on a discrete unital camera that is compatible with framing and cancellative,
and the ghost name of the authoritative element. -/
class AuthSourceG (GF : BundledGFunctors) (M : Type) [UCMRA M] where
  elem : ElemG GF (constOF (Auth M))
  name : GName
  trans : M → M → Prop
  step_frame {a a' f : M} : trans a a' → ✓ (a • f) → ✓ (a' • f) ∧ trans (a • f) (a' • f)
  op_cancel {a f f' : M} : ✓ (a • f) → a • f = a • f' → f = f'

attribute [reducible, instance] AuthSourceG.elem

section AuthSource

variable {GF : BundledGFunctors} {M : Type} [UCMRA M] [CMRA.Discrete M]
variable [G : AuthSourceG GF M]

/-- The authoritative source state (Rocq: `srcA`). -/
def srcA (a : M) : IProp GF := iOwn (E := G.elem) G.name (● a)

/-- A fragment of the source state (Rocq: `srcF`). -/
def srcF (b : M) : IProp GF := iOwn (E := G.elem) G.name (◯ b)

/-- Rocq: `source_auth_source`. -/
instance authSource_source : Source GF M where
  rel := G.trans
  interp := srcA

/-- Rocq: `source_step_update`. -/
theorem source_step_update {Es es es' : M} (hv : ✓ Es) (hinc : es ≼ Es)
    (hstep : G.trans es es') :
    ∃ Es', (Es, es) ~l~> (Es', es') ∧ G.trans Es Es' := by
  obtain ⟨f, hf⟩ := hinc
  subst hf
  obtain ⟨hv', hstep'⟩ := G.step_frame hstep hv
  refine ⟨es' • f, (local_update_unital_discrete _ _ _ _).mpr fun z _ hz => ⟨hv', ?_⟩, hstep'⟩
  rw [G.op_cancel hv hz]

variable [W : WsatGS GF]

/-- Taking a source step with a fragment (Rocq: `auth_src_update`). -/
theorem auth_src_update (E : CoPset) {s s' : M} (hstep : G.trans s s') :
    srcF (GF := GF) s ⊢ srcUpdate (src := authSource_source (GF := GF) (M := M)) E (srcF s') := by
  unfold srcUpdate
  delta authSource_source
  dsimp only
  unfold srcA srcF
  iintro HF %Es HA
  ihave H := (iOwn_op (E := G.elem) (γ := G.name) (a1 := ● Es) (a2 := ◯ s)).mpr $$ [HA HF]
  · iframe
  ihave ⟨Hv, H⟩ := iOwn_valid_l $$ H
  icases internalCmraValid_discrete.mp $$ Hv with %Hv
  obtain ⟨hinc, hv⟩ := Auth.auth_both_valid_discrete.mp Hv
  obtain ⟨Es', hlu, hstep'⟩ := source_step_update hv hinc hstep
  imod iOwn_update (Auth.auth_update hlu) $$ H with H
  icases (iOwn_op (E := G.elem)).mp $$ H with ⟨HA, HF⟩
  iapply fupd_intro
  iexists Es'
  iframe
  ipureintro
  exact .single hstep'

omit [CMRA.Discrete M] W in
/-- Rocq: `srcF_split`. -/
theorem srcF_split {s t : M} : srcF (GF := GF) (s • t) ⊣⊢ srcF s ∗ srcF t := by
  unfold srcF
  rw [Auth.frag_op]
  exact iOwn_op

end AuthSource

end Iris.Transfinite

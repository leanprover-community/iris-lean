/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.Lib.SetBij
public import Iris.BI.BigOp.BigSepSet
public import Iris.BI.Lib.Fractional
public import Iris.Instances.IProp
public import Iris.ProofMode
meta import Iris.Std.RocqPorting

@[expose] public section

/-!
# Propositions for reasoning about monotone partial bijections
-/

namespace Iris

open Std CMRA BI ProofMode BigSepS LawfulSet SetBij

@[rocq_alias gset_bijG]
class SetBijG (GF : BundledGFunctors) (A B : Type _) (S : outParam (Type _))
    [LawfulSet S (A × B)] where
  elem : ElemG GF (constOF (SetBij S))

attribute [reducible, instance] SetBijG.elem

#rocq_ignore «gset_bijΣ» "Subsumed by BundledGFunctors typeclass synthesis"
#rocq_ignore «subG_gset_bijΣ» "Subsumed by BundledGFunctors typeclass synthesis"

section definitions

variable {A B S : Type _} [LawfulSet S (A × B)] [SetBijG GF A B S]

@[rocq_alias gset_bij_own_auth]
def set_bij_own_auth (γ : GName) (dq : DFrac) (L : S) : IProp GF :=
  iOwn (E := SetBijG.elem) γ (auth dq L)

@[rocq_alias gset_bij_own_elem]
def set_bij_own_elem (γ : GName) (a : A) (b : B) : IProp GF :=
  iOwn (E := SetBijG.elem) γ (elem (S := S) a b)

#rocq_ignore gset_bij_own_auth_def "Not needed"
#rocq_ignore gset_bij_own_auth_aux "Not needed"
#rocq_ignore gset_bij_own_auth_eq "Not needed"
#rocq_ignore gset_bij_own_elem_def "Not needed"
#rocq_ignore gset_bij_own_elem_aux "Not needed"
#rocq_ignore gset_bij_own_elem_eq "Not needed"

end definitions

notation γ " ↪●BIJ{" dq "} " L => set_bij_own_auth γ dq L
notation γ " ↪●BIJ " L => set_bij_own_auth γ (DFrac.own 1) L
notation γ " ↪◯BIJ⟨" a ", " b "⟩" => set_bij_own_elem γ a b

section lemmas

variable {A B S : Type _} [LawfulSet S (A × B)] [SetBijG GF A B S]
variable {γ : GName} {dq dq₁ dq₂ : DFrac} {L L₁ L₂ : S}

@[rocq_alias gset_bij_own_auth_timeless]
instance : Timeless (PROP := IProp GF) (γ ↪●BIJ{dq} L) := by
  unfold set_bij_own_auth; infer_instance

@[rocq_alias gset_bij_own_auth_persistent]
instance : Persistent (PROP := IProp GF) (γ ↪●BIJ{.discard} L) := by
  unfold set_bij_own_auth auth; infer_instance

@[rocq_alias gset_bij_own_elem_timeless]
instance (a : A) (b : B) : Timeless (PROP := IProp GF) (γ ↪◯BIJ⟨a, b⟩) := by
  unfold set_bij_own_elem; infer_instance

@[rocq_alias gset_bij_own_elem_persistent]
instance (a : A) (b : B) : Persistent (PROP := IProp GF) (γ ↪◯BIJ⟨a, b⟩) := by
  unfold set_bij_own_elem; infer_instance

@[rocq_alias gset_bij_own_auth_fractional]
instance : Fractional (PROP := IProp GF) fun q => γ ↪●BIJ{.own q} L where
  fractional p q :=
    .trans (.of_eq (congrArg (iOwn γ) (auth_op_auth (dq₁ := .own p) (dq₂ := .own q)).symm)) iOwn_op

@[rocq_alias gset_bij_own_auth_as_fractional]
instance (q : Qp) : AsFractional (PROP := IProp GF) (γ ↪●BIJ{.own q} L)
    ioΦ (fun q => γ ↪●BIJ{.own q} L) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := inferInstance

/-- Turn the internal validity of a composite `SetBij` resource into a pure fact. -/
private theorem cmraValid_op_pure {a₁ a₂ : SetBij S} {φ : Prop} (h : ✓ (a₁ • a₂) → φ) :
    iOwn (E := SetBijG.elem) γ a₁ ∗ iOwn (E := SetBijG.elem) γ a₂ ⊢@{IProp GF} ⌜φ⌝ := by
  iintro H
  icases iOwn_cmraValid_op $$ H with %Hv
  ipureintro; exact (h Hv)

@[rocq_alias gset_bij_own_auth_agree]
theorem set_bij_own_auth_agree :
    (γ ↪●BIJ{dq₁} L₁) ∗ (γ ↪●BIJ{dq₂} L₂) ⊢@{IProp GF} ⌜✓ (dq₁ • dq₂) ∧ L₁ = L₂ ∧ SetBijective L₁⌝ :=
  cmraValid_op_pure auth_op_auth_valid_iff.mp

@[rocq_alias gset_bij_own_auth_exclusive]
theorem set_bij_own_auth_exclusive : (γ ↪●BIJ L₁) ∗ (γ ↪●BIJ L₂) ⊢@{IProp GF} False :=
  (cmraValid_op_pure (φ := False) auth_one_op_auth_one_valid_iff.mp).trans (pure_elim' False.elim)

@[rocq_alias gset_bij_own_valid]
theorem set_bij_own_valid : (γ ↪●BIJ{dq} L) ⊢@{IProp GF} ⌜✓ dq ∧ SetBijective L⌝ :=
  iOwn_cmraValid.trans <| internalCmraValid_discrete.mp.trans <| pure_mono auth_valid_iff.mp

@[rocq_alias gset_bij_own_elem_agree]
theorem set_bij_own_elem_agree {a a' : A} {b b' : B} :
    (γ ↪◯BIJ⟨a, b⟩) ∗ (γ ↪◯BIJ⟨a', b'⟩) ⊢@{IProp GF} ⌜a = a' ↔ b = b'⌝ :=
  cmraValid_op_pure elem_agree

@[rocq_alias gset_bij_own_elem_get]
theorem set_bij_own_elem_get (a : A) (b : B) (h : (a, b) ∈ L) :
    (γ ↪●BIJ{dq} L) ⊢@{IProp GF} γ ↪◯BIJ⟨a, b⟩ :=
  iOwn_mono (elem_inc_auth h)

@[rocq_alias gset_bij_elem_of]
theorem set_bij_elem_of (a : A) (b : B) :
    (γ ↪●BIJ{dq} L) ∗ (γ ↪◯BIJ⟨a, b⟩) ⊢@{IProp GF} ⌜(a, b) ∈ L⌝ :=
  cmraValid_op_pure fun h => (auth_op_elem_valid_iff.mp h).2.2

end lemmas

section finiteLemmas

variable {A B S : Type _} [LawfulFiniteSet S (A × B)] [SetBijG GF A B S]
variable {γ : GName} {dq : DFrac} {L : S}

@[rocq_alias gset_bij_own_elem_get_big]
theorem set_bij_own_elem_get_big :
    (γ ↪●BIJ{dq} L) ⊢@{IProp GF} [∗set] ab ∈ L, γ ↪◯BIJ⟨ab.1, ab.2⟩ := by
  iintro H
  iapply bigSepS_forall
  iintro %⟨a, b⟩ %hab
  iapply set_bij_own_elem_get _ _ hab $$ H

@[rocq_alias gset_bij_own_alloc]
theorem set_bij_own_alloc (L : S) (h : SetBijective L) :
    ⊢@{IProp GF} |==> ∃ γ, (γ ↪●BIJ L) ∗ [∗set] ab ∈ L, γ ↪◯BIJ⟨ab.1, ab.2⟩ := by
  imod (iOwn_alloc (E := SetBijG.elem) (auth (.own 1) L) (auth_one_valid_iff.mpr h)) with ⟨%γ, G⟩
  imodintro; iexists γ
  iapply persistent_entails_left set_bij_own_elem_get_big
  iunfold set_bij_own_auth; iexact G

@[rocq_alias gset_bij_own_alloc_empty]
theorem set_bij_own_alloc_empty : ⊢@{IProp GF} |==> ∃ γ, γ ↪●BIJ (∅ : S) := by
  imod (set_bij_own_alloc ∅ SetBijective.empty) with ⟨%γ, H, -⟩
  imodintro; iexists γ; iexact H

end finiteLemmas

section updates

variable {A B S : Type _} [LawfulSet S (A × B)] [SetBijG GF A B S]
variable {γ : GName} {L : S}

@[rocq_alias gset_bij_own_extend]
theorem set_bij_own_extend (a : A) (b : B) (ha : ∀ b', (a, b') ∉ L) (hb : ∀ a', (a', b) ∉ L) :
    ⊢@{IProp GF} (γ ↪●BIJ L) ==∗ ((γ ↪●BIJ ({(a, b)} ∪ L)) ∗ γ ↪◯BIJ⟨a, b⟩) := by
  iintro Hauth
  ihave Hauth : (γ ↪●BIJ {(a, b)} ∪ L) $$ [> Hauth]
  · unfold set_bij_own_auth
    iapply (iOwn_update (auth_extend ha hb)) $$ Hauth
  imodintro
  isplit
  · itrivial
  iapply set_bij_own_elem_get _ _ (mem_union.mpr (.inl (mem_singleton.mpr rfl))) $$ Hauth

@[rocq_alias gset_bij_own_extend_internal]
theorem set_bij_own_extend_internal (a : A) (b : B) :
    ⊢@{IProp GF} (∀ b' : B, (γ ↪◯BIJ⟨a, b'⟩) -∗ False) ∗ (∀ a' : A, (γ ↪◯BIJ⟨a', b⟩) -∗ False) ∗
      (γ ↪●BIJ L) ==∗ ((γ ↪●BIJ ({(a, b)} ∪ L)) ∗ γ ↪◯BIJ⟨a, b⟩) := by
  iintro ⟨Ha, Hb, HL⟩
  ihave %h₁ : ⌜∀ b', (a, b') ∉ L⌝ $$ [Ha HL]
  · iintro %b' %hmem
    iapply Ha $$ %b' [HL]
    iapply set_bij_own_elem_get _ _ hmem $$ HL
  ihave %h₂ : ⌜∀ a', (a', b) ∉ L⌝ $$ [Hb HL]
  · iintro %a' %hmem
    iapply Hb $$ %a' [HL]
    iapply set_bij_own_elem_get _ _ hmem $$ HL
  iapply set_bij_own_extend _ _ h₁ h₂ $$ HL

end updates

end Iris

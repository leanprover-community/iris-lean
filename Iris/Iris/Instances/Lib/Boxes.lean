/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Algebra
public import Iris.Algebra.Lib.ExclAuth
public import Iris.ProofMode
public import Iris.Instances.IProp
public import Iris.Instances.Lib.Invariants
public import Iris.Std.PartialMap
public import Iris.Std.Namespaces

@[expose] public section

namespace Iris

open BI CMRA Agree OFE UPred IProp Std ProofMode COFE Auth ExclAuth Excl PartialMap

abbrev BoolO := LeibnizO Bool

variable (GF : BundledGFunctors)

abbrev BoxF : OFunctorPre :=
  ProdOF ((AuthURF (F := PNat) (OptionOF (ExclOF (constOF BoolO)))))
    (OptionOF (AgreeRF (LaterOF (constOF (IProp GF)))))

@[rocq_alias boxG]
class BoxG where
  [elemG : ElemG GF (BoxF GF)]

attribute [reducible, instance] BoxG.elemG

variable {GF : BundledGFunctors} [InvGS_gen hlc GF] [BoxG GF]

@[rocq_alias slice_name]
abbrev SliceName := GName

@[rocq_alias box_own_auth]
def box_own_auth (γ : SliceName) (a : Auth PNat (Option (Excl BoolO))) : IProp GF :=
  iOwn (F := BoxF GF) γ (a, none)

@[rocq_alias box_own_prop]
def box_own_prop (γ : SliceName) (P : IProp GF) : IProp GF :=
  iOwn (F := BoxF GF) γ (UCMRA.unit, some (toAgree (Later.next P)))

instance box_own_prop_persistent (γ : SliceName) (P : IProp GF) :
    Persistent (box_own_prop γ P) := by
  unfold box_own_prop
  infer_instance

@[rocq_alias box_own_prop_ne]
instance box_own_prop_ne (γ : SliceName) : NonExpansive (box_own_prop (GF := GF) γ) := by
  constructor
  intro n P Q h
  unfold box_own_prop
  apply iOwn_ne.ne
  apply dist_prod_ext
  · exact Dist.rfl
  · exact toAgree.ne.ne (NextContractive.distLater_dist h.distLater)

@[rocq_alias box_own_prop_contractive]
instance box_own_prop_contractive (γ : SliceName) : Contractive (box_own_prop (GF := GF) γ) := by
  constructor
  intro n P Q h
  unfold box_own_prop
  apply iOwn_ne.ne
  apply dist_prod_ext
  · exact Dist.rfl
  · exact toAgree.ne.ne (NextContractive.distLater_dist h)

@[rocq_alias slice_inv]
def slice_inv (γ : SliceName) (P : IProp GF) : IProp GF :=
  iprop(∃ b : Bool, box_own_auth γ (●E (⟨b⟩ : BoolO)) ∗ if b then P else True)

@[rocq_alias slice]
def slice (N : Namespace) (γ : SliceName) (P : IProp GF) : IProp GF :=
  iprop(box_own_prop γ P ∗ inv N (slice_inv γ P))

@[rocq_alias box]
def box {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (N : Namespace) (f : M Bool) (P : IProp GF) : IProp GF :=
  iprop(∃ Φ : SliceName → IProp GF,
    ▷ internalEq P ([∗map] γ ↦ _x ∈ f, Φ γ) ∗
    [∗map] γ ↦ b ∈ f, box_own_auth γ (◯E (⟨b⟩ : BoolO)) ∗ box_own_prop γ (Φ γ) ∗
                       inv N (slice_inv γ (Φ γ)))

@[rocq_alias box_inv_ne]
instance slice_inv_ne (γ : SliceName) : NonExpansive (slice_inv (GF := GF) γ) := by
  constructor
  intro n P Q h
  unfold slice_inv
  apply exists_ne
  intro b
  apply sep_ne.ne Dist.rfl
  cases b
  · exact Dist.rfl
  · exact h

@[rocq_alias slice_ne]
instance slice_ne (N : Namespace) (γ : SliceName) : NonExpansive (slice (GF := GF) N γ) := by
  constructor
  intro n P Q h
  unfold slice
  apply sep_ne.ne
  · exact (box_own_prop_ne γ).ne h
  · exact (inv_ne N).ne ((slice_inv_ne γ).ne h)

@[rocq_alias slice_contractive]
instance slice_contractive (N : Namespace) (γ : SliceName) : Contractive (slice (GF := GF) N γ) where
  distLater_dist {n P Q} h := by
    unfold slice
    apply sep_ne.ne
    · exact (box_own_prop_contractive γ).distLater_dist h
    · exact (inv_contractive N).distLater_dist (fun m hm => (slice_inv_ne γ).ne (h m hm))

@[rocq_alias slice_persistent]
instance slice_persistent (N : Namespace) (γ : SliceName) (P : IProp GF) :
    Persistent (slice N γ P) := by
  unfold slice
  infer_instance

@[rocq_alias box_contractive]
instance box_contractive {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (N : Namespace) (f : M Bool) : Contractive (box (GF := GF) N f) where
  distLater_dist {n P Q} h := by
    unfold box
    apply exists_ne
    intro Φ
    apply sep_ne.ne _ Dist.rfl
    apply Contractive.distLater_dist
    intro m hm
    exact (internalEq.ne_l _).ne (h m hm)

@[rocq_alias box_ne]
instance box_ne {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (N : Namespace) (f : M Bool) : NonExpansive (box (GF := GF) N f) :=
  ne_of_contractive _

@[rocq_alias box_own_auth_agree]
theorem box_own_auth_agree (γ : SliceName) (b1 b2 : Bool) :
    box_own_auth (GF := GF) γ (●E (⟨b1⟩ : BoolO)) ∗ box_own_auth γ (◯E ⟨b2⟩) ⊢ ⌜b1 = b2⌝ := by
  unfold box_own_auth
  iintro ⟨H1, H2⟩
  icases iOwn_op $$ [$H1 $H2] with H
  icases iOwn_cmraValid $$ H with H
  icases (internalCmraValid_entails.mpr fun n h => Prod.validN_fst h) $$ H with %H
  ipureintro
  exact LeibnizO.eqv_inj $ Iris.ExclAuth.agree_L H

@[rocq_alias box_own_auth_update]
theorem box_own_auth_update (γ : SliceName) (b1 b2 b3 : Bool) :
    box_own_auth (GF := GF) γ (●E (⟨b1⟩ : BoolO)) ∗ box_own_auth γ (◯E ⟨b2⟩) ⊢
    |==> (box_own_auth γ (●E ⟨b3⟩) ∗ box_own_auth γ (◯E ⟨b3⟩)) := by
  unfold box_own_auth
  iintro ⟨H1, H2⟩
  icases iOwn_op $$ [$H1 $H2] with H
  iapply bupd_mono iOwn_op.mp
  iapply iOwn_update (Update.prod _ ExclAuth.update (Update.id (x := none))) $$ H

@[rocq_alias box_own_agree]
theorem box_own_agree (γ : SliceName) (Q1 Q2 : IProp GF) :
    box_own_prop γ Q1 ∗ box_own_prop γ Q2 ⊢ ▷ internalEq Q1 Q2 := by
  unfold box_own_prop
  iintro ⟨H1, H2⟩
  icases iOwn_op $$ [$H1 $H2] with H
  icases iOwn_cmraValid $$ H with H
  icases (internalCmraValid_entails.mpr fun n h => Prod.validN_snd h) $$ H with H
  icases option_validI.mp $$ H with H
  dsimp only [CMRA.op, optionOp, Option.elim_some]
  icases agree_op_invI $$ H with H
  icases (agree_equivI _ _).mp $$ H with H
  inext
  itrivial

@[rocq_alias box_alloc]
theorem box_alloc {M : Type _ → Type _} [LawfulFiniteMap M SliceName] (N : Namespace) :
    ⊢ box (GF := GF) N (∅ : M Bool) iprop(emp) := by
  simp only [box]
  iexists (fun _ => iprop(True))
  isplit
  · inext; simp only [Algebra.BigOpM.bigOpM_empty]; itrivial
  · simp

@[rocq_alias slice_insert_empty]
theorem slice_insert_empty {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (E : CoPset) (q : Bool) (f : M Bool) (Q P : IProp GF) (N : Namespace) :
    (▷?b box N f P) ⊢
    |={E}=> ∃ γ, ⌜get? f γ = none⌝ ∗
      slice N γ Q ∗ ▷?q box N (insert f γ false) iprop(Q ∗ P) := by
  unfold box
  iintro ⟨%Φ, #Heq, H⟩

  sorry

@[rocq_alias slice_delete_empty]
theorem slice_delete_empty {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (E : CoPset) (q : Bool) (f : M Bool) (P Q : IProp GF)
    (γ : SliceName) (N : Namespace) :
    ↑N ⊆ E →
    get? f γ = some false →
    slice N γ Q ∗ ▷?q box N f P ⊢
    |={E}=> ∃ P', ▷?q (▷ internalEq P iprop(Q ∗ P')) ∗ (box N (delete f γ) P') := by
  sorry

@[rocq_alias slice_fill]
theorem slice_fill {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (E : CoPset) (q : Bool) (f : M Bool) (γ : SliceName)
    (P Q : IProp GF) (N : Namespace) :
    ↑N ⊆ E →
    get? f γ = some false →
    slice N γ Q ∗ ▷ Q ∗ ▷?q box N f P ⊢
    |={E}=> ▷?q box N (insert f γ true) P :=
  sorry

@[rocq_alias slice_empty]
theorem slice_empty {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (E : CoPset) (q : Bool) (f : M Bool) (P Q : IProp GF)
    (γ : SliceName) (N : Namespace) :
    ↑N ⊆ E →
    get? f γ = some true →
    slice N γ Q ∗ ▷?q box N f P ⊢
    |={E}=> ▷ Q ∗ (▷?q box N (insert f γ false) P) := by
  sorry

@[rocq_alias slice_insert_full]
theorem slice_insert_full {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (E : CoPset) (q : Bool) (f : M Bool) (P Q : IProp GF) (N : Namespace) :
    ↑N ⊆ E →
    ▷ Q ∗ (if q then box N f P else ▷ box N f P) ⊢
    |={E}=> ∃ γ, ⌜get? f γ = none⌝ ∗
      slice N γ Q ∗ (▷?q box N (insert f γ true) iprop(Q ∗ P)) :=
  sorry

@[rocq_alias slice_delete_full]
theorem slice_delete_full {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (E : CoPset) (q : Bool) (f : M Bool) (P Q : IProp GF)
    (γ : SliceName) (N : Namespace) :
    ↑N ⊆ E →
    PartialMap.get? f γ = some true →
    slice N γ Q ∗ (if q then box N f P else ▷ box N f P) ⊢
    |={E}=> ∃ P', ▷ Q ∗
      (▷?q ▷ internalEq P iprop(Q ∗ P')) ∗ (▷?q box N (delete f γ) P') :=
  sorry

@[rocq_alias box_fill]
theorem box_fill {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (E : CoPset) (f : M Bool) (P : IProp GF) (N : Namespace) :
    ↑N ⊆ E →
    box N f P ∗ ▷ P ⊢ |={E}=> box N (map _ (fun _ => true) f) P :=
  sorry

@[rocq_alias box_empty]
theorem box_empty {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (E : CoPset) (f : M Bool) (P : IProp GF) (N : Namespace) :
    ↑N ⊆ E →
    all (fun _ b => b = true) f →
    box N f P ⊢ |={E}=> ▷ P ∗ box N (map _ (fun _ => false) f) P :=
  sorry

@[rocq_alias slice_iff]
theorem slice_iff {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (E : CoPset) (q : Bool) (f : M Bool) (P Q Q' : IProp GF)
    (γ : SliceName) (b : Bool) (N : Namespace) :
    ↑N ⊆ E →
    get? f γ = some b →
    □ (▷ (Q ↔ Q')) ∗ slice N γ Q ∗ (▷?q box N f P) ⊢
    |={E}=> ∃ γ' P', ⌜get? (delete f γ) γ' = none⌝ ∗
      (▷?q ▷ □ (P ↔ P')) ∗
      slice N γ' Q' ∗
      (▷?q box N (insert (delete f γ) γ' b) P') :=
  sorry

@[rocq_alias slice_split]
theorem slice_split {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    [DecidableEq SliceName] (E : CoPset) (q : Bool) (f : M Bool) (P Q1 Q2 : IProp GF)
    (γ : SliceName) (b : Bool) (N : Namespace) :
    ↑N ⊆ E →
    get? f γ = some b →
    slice N γ iprop(Q1 ∗ Q2) ∗ (▷?q box N f P) ⊢
    |={E}=> ∃ γ1 γ2, ⌜get? (delete f γ) γ1 = none⌝ ∗
      ⌜get? (delete f γ) γ2 = none⌝ ∗ ⌜γ1 ≠ γ2⌝ ∗
      slice N γ1 Q1 ∗ slice N γ2 Q2 ∗
      (▷?q box N (insert (insert (delete f γ) γ1 b) γ2 b) P) :=
  sorry

@[rocq_alias slice_combine]
theorem slice_combine {M : Type _ → Type _} [LawfulFiniteMap M SliceName]
    (E : CoPset) (q : Bool) (f : M Bool) (P Q1 Q2 : IProp GF)
    (γ1 γ2 : SliceName) (b : Bool) (N : Namespace) :
    ↑N ⊆ E →
    γ1 ≠ γ2 →
    get? f γ1 = some b →
    get? f γ2 = some b →
    slice N γ1 Q1 ∗ slice N γ2 Q2 ∗ (if q then box N f P else ▷ box N f P) ⊢
    |={E}=> ∃ γ, ⌜get? (delete (delete f γ1) γ2) γ = none⌝ ∗
      slice N γ iprop(Q1 ∗ Q2) ∗
      (▷?q box N (insert (delete (delete f γ1) γ2) γ b) P) :=
  sorry

end Iris

end

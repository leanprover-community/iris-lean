/-
Copyright (c) 2026 Сухарик. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Сухарик (@suhr)
-/

module

public import Iris.BI
public import Iris.ProofMode

@[expose] public section

namespace Iris
open Iris.Std BI OFE ProofMode

@[rocq_alias Fractional]
class Fractional [BI PROP] (Φ : Qp → PROP) where
  fractional p q : Φ (p + q) ⊣⊢ Φ p ∗ Φ q

#rocq_ignore Fractional_proper "OFE equivalence is Lean equality; use `congrArg`."

@[ipm_class, rocq_alias AsFractional]
class AsFractional {PROP : Type u} [BI PROP] (P : PROP) (ioΦ : InOut)
    (Φ : semiOutParamIPM ioΦ (Qp → PROP)) (ioq : InOut)
    (q : semiOutParamIPM ioq Qp) where
  as_fractional : P ⊣⊢ Φ q
  as_fractional_fractional : Fractional Φ

/-- `FrameFractionalQp` is used for fractional framing: it subtracts the fraction of the
hypothesis from the fraction of the goal, computing `r := qP - qR`. See `frame_fractional`. -/
@[rocq_alias FrameFractionalQp]
class FrameFractionalQp (qR qP : Qp) (r : outParam Qp) : Prop where
  frame_fractional_qp : qP = qR + r

section Lemmas
variable {PROP : Type _} [BI PROP] {P P1 P2 : PROP} {Φ : Qp → PROP} {q q1 q2 : Qp}

/-- ## AsFractional manipulation lemmas

The Rocq versions are stated using fewer AsFractional instances, and have postconditions
stated in terms of `Φ`. This version adds more typeclass instances, but has postconditons that
unify against any `IProp`.  -/

@[rocq_alias fractional_as_fractional]
instance (priority := low) fractional_as_fractional [h : Fractional Φ] (q : Qp) :
    AsFractional (Φ q) ioΦ Φ ioq q where
  as_fractional := .rfl
  as_fractional_fractional := h

@[rocq_alias fractional_split]
theorem fractional_split [hP : AsFractional P ioΦ Φ ioq (q1 + q2)]
    [hP1 : AsFractional P1 ioΦ Φ ioq q1] [hP2 : AsFractional P2 ioΦ Φ ioq q2] : P ⊣⊢ P1 ∗ P2 :=
  hP.as_fractional.trans <|
  (hP.as_fractional_fractional.fractional q1 q2).trans <|
  sep_congr hP1.as_fractional.symm hP2.as_fractional.symm

@[rocq_alias fractional_half]
theorem fractional_half [hP : AsFractional P ioΦ Φ ioq q] [hP12 : AsFractional P1 ioΦ Φ ioq q.half] :
    P ⊣⊢ P1 ∗ P1 :=
  hP.as_fractional.trans <|
  (Qp.half_add_half q ▸ hP.as_fractional_fractional.fractional q.half q.half).trans <|
  sep_congr hP12.as_fractional.symm hP12.as_fractional.symm

@[rocq_alias fractional_merge]
theorem fractional_merge [Fractional Φ] [hP1 : AsFractional P1 ioΦ Φ ioq q1] [hP2 : AsFractional P2 ioΦ Φ ioq q2] :
    P1 ∗ P2 ⊢ Φ (q1 + q2) :=
  (sep_mono hP1.as_fractional.1 hP2.as_fractional.1).trans (Fractional.fractional q1 q2).2

@[ipm_backtrack, rocq_alias from_sep_fractional]
instance (priority := default - 10) fromSepFractional [hP : AsFractional P .out Φ .in (q1 + q2)] :
    FromSep P (Φ q1) (Φ q2) where
  from_sep := (hP.as_fractional_fractional.fractional q1 q2).2.trans hP.as_fractional.2

@[ipm_backtrack, rocq_alias into_sep_fractional]
instance (priority := default - 10) intoSepFractional [hP : AsFractional P .out Φ .in (q1 + q2)] :
    IntoSep P (Φ q1) (Φ q2) where
  into_sep := hP.as_fractional.1.trans (hP.as_fractional_fractional.fractional q1 q2).1

@[rocq_alias from_sep_fractional_half]
instance (priority := default - 30) fromSepFractionalHalf [hP : AsFractional P .out Φ .out q] :
    FromSep P (Φ q.half) (Φ q.half) where
  from_sep :=
    (Qp.half_add_half q ▸ hP.as_fractional_fractional.fractional q.half q.half).2.trans
    hP.as_fractional.2

@[rocq_alias into_sep_fractional_half]
instance (priority := default - 30) intoSepFractionalHalf [hP : AsFractional P .out Φ .out q] :
    IntoSep P (Φ q.half) (Φ q.half) where
  into_sep :=
    hP.as_fractional.1.trans
    (Qp.half_add_half q ▸ hP.as_fractional_fractional.fractional q.half q.half).1

@[ipm_backtrack, rocq_alias combine_sep_as_fractional]
instance (priority := default - 10) combineSepAsFractional
    [hP1 : AsFractional P1 .out Φ .out q1] [hP2 : AsFractional P2 .in Φ .out q2] :
    CombineSepAs P1 P2 (Φ (q1 + q2)) where
  combine_sep_as :=
    (sep_mono hP1.as_fractional.mp hP2.as_fractional.mp).trans
    (hP1.as_fractional_fractional.fractional q1 q2).mpr

@[ipm_backtrack, rocq_alias combine_sep_as_fractional_half]
instance (priority := default - 10) combineSepAsFractionalHalf
    [hP : AsFractional P .out Φ .in q.half] :
    CombineSepAs P P (Φ q) where
  combine_sep_as := calc
    _ ⊢ Φ q.half ∗ Φ q.half := sep_mono hP.as_fractional.mp hP.as_fractional.mp
    _ ⊢ Φ (q.half + q.half) := (hP.as_fractional_fractional.fractional q.half q.half).mpr
    _ ⊢ Φ q                 := Qp.half_add_half _ ▸ .rfl

/-! ## Fractional and logical connectives -/

@[rocq_alias persistent_fractional]
instance (priority := default - 10) persistent_fractional
    [Persistent P] [TCOr (Affine P) (Absorbing P)] :
    Fractional (fun _ => P) where
  fractional _ _ := persistent_sep_dup

@[rocq_alias fractional_sep]
instance fractional_sep {Ψ : Qp → PROP} [hΦ : Fractional Φ] [hΨ : Fractional Ψ] :
    Fractional (fun q => iprop(Φ q ∗ Ψ q)) where
  fractional p q := (sep_congr (hΦ.fractional p q) (hΨ.fractional p q)).trans sep_sep_sep_comm

@[rocq_alias fractional_embed]
instance fractional_embed {PROP' : Type _} [BI PROP'] [BiEmbed PROP PROP'] [hΦ : Fractional Φ] :
    Fractional (fun q => (iprop(⎡Φ q⎤) : PROP')) where
  fractional p q := calc
    (iprop(⎡Φ (p + q)⎤) : PROP')
    _ ⊣⊢ ⎡Φ p ∗ Φ q⎤   := .ofMono embed_mono (hΦ.fractional p q)
    _ ⊣⊢ ⎡Φ p⎤ ∗ ⎡Φ q⎤ := embed_sep ..

@[rocq_alias as_fractional_embed]
instance as_fractional_embed {PROP' : Type _} [BI PROP'] [BiEmbed PROP PROP']
    [h : AsFractional P ioΦ Φ ioq q] :
    AsFractional (iprop(⎡P⎤) : PROP') ioΦ (fun q => iprop(⎡Φ q⎤)) ioq q where
  as_fractional := .ofMono embed_mono h.as_fractional
  as_fractional_fractional := fractional_embed (hΦ := h.as_fractional_fractional)

@[rocq_alias fractional_big_sepL]
instance fractional_bigSepL {A : Type _} {l : List A} {Ψ : Nat → A → Qp → PROP}
    [∀ k x, Fractional (Ψ k x)] : Fractional (fun q => iprop([∗list] k ↦ x ∈ l, Ψ k x q)) where
  fractional p q :=
    ⟨(BigSepL.bigSepL_mono_of_forall fun {_ _} => (Fractional.fractional p q).1).trans
      BigSepL.bigSepL_sep_eqv.1,
     BigSepL.bigSepL_sep_eqv.2.trans
      (BigSepL.bigSepL_mono_of_forall fun {_ _} => (Fractional.fractional p q).2)⟩

@[rocq_alias fractional_big_sepL2]
instance fractional_bigSepL2 {A B : Type _} {l1 : List A} {l2 : List B}
    {Ψ : Nat → A → B → Qp → PROP} [∀ k x1 x2, Fractional (Ψ k x1 x2)] :
    Fractional (fun q => iprop([∗list] k ↦ x1;x2 ∈ l1;l2, Ψ k x1 x2 q)) where
  fractional p q :=
    (BigSepL2.bigSepL2_eqv_of_forall_eqv fun {_ _ _} => Fractional.fractional p q).trans
      BigSepL2.bigSepL2_sep_eqv

@[rocq_alias fractional_big_sepM]
instance fractional_bigSepM {K V : Type _} {M : Type _ → Type _} [LawfulFiniteMap M K] {m : M V}
    {Ψ : K → V → Qp → PROP} [∀ k x, Fractional (Ψ k x)] :
    Fractional (fun q => iprop([∗map] k ↦ x ∈ m, Ψ k x q)) where
  fractional p q := .of_eq <|
    (BigSepM.bigSepM_eq_of_forall_eq fun {_ _} => (Fractional.fractional p q).to_eq).trans
      BigSepM.bigSepM_sep_eq

@[rocq_alias fractional_big_sepS]
instance fractional_bigSepS {S A : Type _} [LawfulFiniteSet S A] {X : S} {Ψ : A → Qp → PROP}
    [∀ x, Fractional (Ψ x)] : Fractional (fun q => iprop([∗set] x ∈ X, Ψ x q)) where
  fractional p q :=
    (BigSepS.bigSepS_eqv fun _ => Fractional.fractional p q).trans BigSepS.bigSepS_sep

@[rocq_alias fractional_big_sepMS]
instance fractional_bigSepMS {MS A : Type _} [LawfulFiniteMultiSet MS A] {X : MS}
    {Ψ : A → Qp → PROP} [∀ x, Fractional (Ψ x)] :
    Fractional (fun q => iprop([∗mset] x ∈ X, Ψ x q)) where
  fractional p q :=
    (BigSepMS.bigSepMS_eqv fun _ => Fractional.fractional p q).trans BigSepMS.bigSepMS_sep

@[rocq_alias frame_fractional_qp_add_l]
instance frameFractionalQpAddLeft (q q' : Qp) : FrameFractionalQp q (q + q') q' := ⟨rfl⟩

@[rocq_alias frame_fractional_qp_add_r]
instance frameFractionalQpAddRight (q q' : Qp) : FrameFractionalQp q' (q + q') q :=
  ⟨Subtype.ext (Rat.add_comm ..)⟩

@[rocq_alias frame_fractional_qp_half]
instance frameFractionalQpHalf (q : Qp) : FrameFractionalQp q.half q q.half :=
  ⟨(Qp.half_add_half q).symm⟩

/-- Not an instance because of performance; concrete fractional assertions provide their own
`Frame` instances by applying this lemma. `Φ` is explicit because it is rarely inferrable. -/
@[rocq_alias frame_fractional]
theorem frame_fractional (Φ : Qp → PROP) (qR qP r : Qp) {p : Bool} {R : PROP}
    [hR : AsFractional R .in Φ .in qR] [hP : AsFractional P .in Φ .in qP]
    [hq : FrameFractionalQp qR qP r] : Frame p R P (Φ r) where
  frame := calc
    _ ⊢ R ∗ Φ r    := sep_mono_left intuitionisticallyIf_elim
    _ ⊢ Φ qR ∗ Φ r := sep_mono_left hR.as_fractional.mp
    _ ⊢ Φ (qR + r) := (hR.as_fractional_fractional.fractional qR r).mpr
    _ ⊢ Φ qP       := (BIBase.BiEntails.of_eq (congrArg Φ hq.frame_fractional_qp)).mpr
    _ ⊢ P          := hP.as_fractional.mpr

end Lemmas

section Divide
variable {PROP : Type _} [BI PROP]
open BI.BigSepL

theorem fractional_bigSepL_replicate {Φ : Qp → PROP} [Fractional Φ] (r : Qp) (k : Nat) :
    ∀ (q : Qp), q.val = ((k : Rat) + 1) * r.val →
      Φ q ⊢ [∗list] _x ∈ List.replicate (k + 1) r, Φ r := by
  induction k with
  | zero =>
    intro q hq
    refine .trans ?_ (bigSepL_singleton (Φ := fun _ _ => Φ r)).2
    exact .of_eq (by grind)
  | succ k ih =>
    rintro ⟨q, hq⟩ _
    obtain ⟨r, hr⟩ := r
    have hval : q - r = ((k : Rat) + 1) * r := by grind
    have hpos : (0 : Rat) < q - r := hval ▸ Rat.mul_pos (by grind) hr
    have hsum : ⟨r, hr⟩ + (⟨q - r, hpos⟩ : Qp) = ⟨q, hq⟩ := Subtype.ext (by grind)
    rw [← hsum, List.replicate_succ]
    exact ((Fractional.fractional ⟨r, hr⟩ _).1.trans (sep_mono_right (ih _ hval))).trans
      (bigSepL_cons (Φ := fun _ _ => Φ _)).2

theorem fractional_divide_equal {Φ : Qp → PROP} [Fractional Φ] (q : Qp) (n : Nat) :
    Φ q ⊢ [∗list] _x ∈ List.replicate (n + 1) (q.divide_even (n + 1) (Nat.succ_pos n)),
      Φ (q.divide_even (n + 1) (Nat.succ_pos n)) := by
  refine fractional_bigSepL_replicate _ n q ?_
  have hcast : ((n + 1 : Nat) : Rat) = (n : Rat) + 1 := by grind
  rw [Qp.val_divide_even, hcast, Rat.mul_div_cancel_left _]
  have : (0 : Rat) ≤ (n : Rat) := by exact_mod_cast Nat.zero_le n
  grind

end Divide

/-! ## Internal fractional

`internalFractional Φ` internalises `Fractional Φ` into the logic, so that it can be kept in an
invariant and transported along an internal `∗-∗`. -/

section InternalFractional
variable {PROP : Type _} [BI PROP] {Φ Ψ : Qp → PROP}

@[rocq_alias internal_fractional]
def internalFractional (Φ : Qp → PROP) : PROP := iprop(□ ∀ p q, Φ (p + q) ∗-∗ Φ p ∗ Φ q)

@[rocq_alias internal_fractional_ne]
instance internalFractional_ne : NonExpansive (internalFractional (PROP := PROP)) where
  ne _ _ _ h := intuitionistically_ne.ne <|
    forall_ne fun p => forall_ne fun q => wandIff_ne.ne (h _) (sep_ne.ne (h p) (h q))

#rocq_ignore internal_fractional_proper "OFE equivalence is Lean equality; use `congrArg`."

@[rocq_alias internal_fractional_affine]
instance internalFractional_affine : Affine (internalFractional Φ) := by
  unfold internalFractional; infer_instance

@[rocq_alias internal_fractional_persistent]
instance internalFractional_persistent : Persistent (internalFractional Φ) := by
  unfold internalFractional; infer_instance

@[rocq_alias fractional_internal_fractional]
theorem fractional_internalFractional (h : Fractional Φ) : ⊢ internalFractional Φ := by
  unfold internalFractional
  iintro !> %p %q
  iapply equiv_wandIff (h.fractional p q)

@[rocq_alias internal_fractional_iff]
theorem internalFractional_iff :
    □ (∀ q, Φ q ∗-∗ Ψ q) ⊢ internalFractional Φ -∗ internalFractional Ψ := by
  unfold internalFractional
  iintro #Hiff #Hdup !> %p %q
  isplit
  · iintro HΨ
    icases Hdup $$ %p %q (Hiff $$ %(p + q) HΨ) with ⟨H1, H2⟩
    isplitl [H1]
    · iapply Hiff $$ H1
    · iapply Hiff $$ H2
  · iintro ⟨H1, H2⟩
    iapply Hiff
    iapply Hdup
    isplitl [H1]
    · iapply Hiff $$ H1
    · iapply Hiff $$ H2

end InternalFractional

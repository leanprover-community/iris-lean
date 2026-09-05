/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Puming Liu, Janine Lohse
-/
module

public import Iris.Algebra.CMRA
public import Iris.Algebra.OFE
public import Iris.Algebra.Frac
public import Iris.Algebra.DFrac
public import Iris.Algebra.Agree
public import Iris.Algebra.BigOp
public import Iris.Algebra.Updates
public import Iris.Algebra.LocalUpdates

@[expose] public section

open Iris

abbrev ViewRel (A B : Type _) := Nat → A → B → Prop

@[rocq_alias view_rel]
class IsViewRel [OFE A] [UCMRA B] (R : ViewRel A B) where
  /-- The relation only shrinks when a summand of the fragment is dropped. -/
  mono : R n1 a1 b1 → a1 ≡{n2}≡ a2 → b2 ≼ₑ{n2} b1 → n2 ≤ n1 → R n2 a2 b2
  /-- The relation is down-closed for the fragment order. Independent of `mono` in general;
  for an affine fragment algebra `mono` follows from it. -/
  mono_ord : R n1 a1 b1 → a1 ≡{n2}≡ a2 → b2 ≼{n2} b1 → n2 ≤ n1 → R n2 a2 b2
  rel_validN n a b : R n a b → ✓{n} b
  rel_unit n : ∃ a, R n a UCMRA.unit

/-- Build an `IsViewRel` from order-closure alone: over an affine fragment algebra the
`≼ₑ`-closure `mono` follows from `mono_ord`. -/
theorem IsViewRel.ofMonoOrd [OFE A] [UCMRA B] [CMRA.Affine B] {R : ViewRel A B}
    (mono_ord : ∀ {n1 a1 b1 n2 a2 b2},
      R n1 a1 b1 → a1 ≡{n2}≡ a2 → b2 ≼{n2} b1 → n2 ≤ n1 → R n2 a2 b2)
    (rel_validN : ∀ n a b, R n a b → ✓{n} b)
    (rel_unit : ∀ n, ∃ a, R n a UCMRA.unit) : IsViewRel R where
  mono h ha hb hn := mono_ord h ha (CMRA.incN_of_incExtN hb) hn
  mono_ord := mono_ord
  rel_validN := rel_validN
  rel_unit := rel_unit

@[rocq_alias ViewRelDiscrete]
class IsViewRelDiscrete [OFE A] [UCMRA B] (R : ViewRel A B) extends IsViewRel R where
  discrete n a b : R 0 a b → R n a b

namespace ViewRel
open IsViewRel DFrac

variable [OFE A] [UCMRA B] {R : ViewRel A B} [IsViewRel R]

@[rocq_alias view_rel_ne]
theorem iff_of_dist (Ha : a1 ≡{n}≡ a2) (Hb : b1 ≡{n}≡ b2) : R n a1 b1 ↔ R n a2 b2 :=
  ⟨(mono · Ha Hb.symm.to_incExtN n.le_refl), (mono · Ha.symm Hb.to_incExtN n.le_refl)⟩

#rocq_ignore view_rel_proper "OFE is Leibniz; use equality"

end ViewRel

@[rocq_alias view]
structure View {A B : Type _} (R : ViewRel A B) where
  auth : Option ((DFrac) × Agree A)
  frag : B

@[rocq_alias view_auth]
abbrev View.Auth [UCMRA B] {R : ViewRel A B} (dq : DFrac) (a : A) : View R :=
  ⟨some (dq, toAgree a), UCMRA.unit⟩

@[rocq_alias view_frag]
abbrev View.Frag {R : ViewRel A B} (b : B) : View R := ⟨none, b⟩

notation "●V{" dq "} " a => View.Auth dq a
notation "●V " a => View.Auth (DFrac.own 1) a
notation "◯V " b => View.Frag b

namespace View
section OFE
open OFE UCMRA
variable [OFE A] [OFE B] {R : ViewRel A B}

#rocq_ignore view_equiv "OFE is Leibniz; use equality"

@[rocq_alias view_dist]
def dist (n : Nat) (x y : View R) : Prop := x.auth ≡{n}≡ y.auth ∧ x.frag ≡{n}≡ y.frag

@[rocq_alias view_ofe_mixin]
instance instOFE : OFE (View R) where
  Dist := dist
  dist_eqv := {
    refl _ := ⟨.of_eq rfl, .of_eq rfl⟩
    symm H := ⟨H.1.symm, H.2.symm⟩
    trans H1 H2 := ⟨H1.1.trans H2.1, H1.2.trans H2.2⟩
  }
  eq_dist' {x y} := by
    refine ⟨fun H _ => H ▸ ⟨.rfl, .rfl⟩, fun H => ?_⟩
    obtain ⟨xa, xf⟩ := x; obtain ⟨ya, yf⟩ := y
    simp only [View.mk.injEq]
    exact ⟨eq_dist_2 fun n => (H n).1, eq_dist_2 fun n => (H n).2⟩
  dist_lt H Hn := ⟨dist_lt H.1 Hn, dist_lt H.2 Hn⟩

#rocq_ignore viewO "Use the plain View type and typeclass inference"

@[rocq_alias View_ne]
instance mk.ne : NonExpansive₂ (mk : _ → _ → View R) := ⟨fun _ _ _ Ha _ _ Hb => ⟨Ha, Hb⟩⟩
#rocq_ignore View_proper "Derived from View.mk.ne"

@[rocq_alias view_auth_proj_ne]
instance auth.ne : NonExpansive (auth : View R → _) := ⟨fun _ _ _ H => H.1⟩
#rocq_ignore view_auth_proj_proper "Derived from View.auth.ne"

@[rocq_alias view_frag_proj_ne]
instance frag.ne : NonExpansive (frag : View R → _) := ⟨fun _ _ _ H => H.2⟩
#rocq_ignore view_frag_proj_proper "Derived from View.frag.ne"

@[rocq_alias View_discrete]
theorem discrete {ag : Option ((DFrac) × Agree A)} (Ha : DiscreteE ag) (Hb : DiscreteE b) :
  DiscreteE (α := View R) (mk ag b) := ⟨fun H => by rw [Ha.discrete H.1, Hb.discrete H.2]⟩

@[rocq_alias view_ofe_discrete]
instance [Discrete A] [Discrete B] : Discrete (View R) where
  discrete_0 {x y} H := by
    obtain ⟨xa, xf⟩ := x; obtain ⟨ya, yf⟩ := y
    simp only [mk.injEq]
    exact ⟨discrete_0 H.1, discrete_0 H.2⟩

-- view_auth_dist_inj
theorem auth_inj_frac [UCMRA B] {q1 q2 : DFrac} {a1 a2 : A} {n} (H : (●V{q1} a1 : View R) ≡{n}≡ ●V{q2} a2) :
    q1 = q2 := H.1.1

-- view_auth_dist_inj
theorem dist_of_auth_dist [UCMRA B] {q1 q2 : DFrac} {a1 a2 : A} {n} (H : (●V{q1} a1 : View R) ≡{n}≡ ●V{q2} a2) :
    a1 ≡{n}≡ a2 := toAgree.inj H.1.2

@[rocq_alias view_auth_dist_inj]
theorem auth_dist_inj [UCMRA B] {q1 q2 : DFrac} {a1 a2 : A} {n}
    (H : (●V{q1} a1 : View R) ≡{n}≡ ●V{q2} a2) : q1 = q2 ∧ a1 ≡{n}≡ a2 :=
  ⟨auth_inj_frac H, dist_of_auth_dist H⟩

@[rocq_alias view_auth_inj]
theorem auth_eqv_inj [UCMRA B] {q1 q2 : DFrac} {a1 a2 : A}
    (H : (●V{q1} a1 : View R) = ●V{q2} a2) : q1 = q2 ∧ a1 = a2 := by
  refine ⟨(auth_dist_inj (n := 0) H.dist).1, OFE.eq_dist_2 fun n => ?_⟩
  exact (auth_dist_inj H.dist).2

@[rocq_alias view_frag_inj]
theorem frag_eqv_inj [UCMRA B] {b1 b2 : B}
    (H : (◯V b1 : View R) = ◯V b2) : b1 = b2 := OFE.eq_dist_2 fun _ => H.dist.2

@[rocq_alias view_frag_dist_inj]
theorem dist_of_frag_dist [UCMRA B] {b1 b2 : B} {n} (H : (◯V b1 : View R) ≡{n}≡ ◯V b2) :
    b1 ≡{n}≡ b2 := H.2

@[rocq_alias view_auth_discrete]
instance auth_discrete [UCMRA B] {dq a} [Ha : DiscreteE a] [He : DiscreteE (unit : B)] :
    DiscreteE (●V{dq} a : View R) := by
  refine discrete ?_ He
  infer_instance

@[rocq_alias view_frag_discrete]
instance frag_discrete [UCMRA B] [Hb : DiscreteE b] : DiscreteE (◯V b : View R) :=
  discrete Option.none_is_discrete Hb

end OFE

section CMRA
open IsViewRel toAgree OFE DFrac

variable [OFE A] [UCMRA B] {R : ViewRel A B} [IsViewRel R]

theorem IsViewRel.of_agree_dist_iff (Hb : b' ≡{n}≡ b) :
    (∃ a', toAgree a ≡{n}≡ toAgree a' ∧ R n a' b') ↔ R n a b := by
  refine ⟨fun H => ?_, fun H => ?_⟩
  · rcases H with ⟨_, HA, HR⟩
    exact mono HR (inj HA.symm) Hb.symm.to_incExtN n.le_refl
  · exact ⟨a, .rfl, mono H .rfl Hb.to_incExtN n.le_refl⟩

@[rocq_alias view_auth_ne]
instance auth_ne {dq : DFrac} : NonExpansive (Auth dq : A → View R) where
  ne _ _ _ H := by
    refine mk.ne.ne ?_ .rfl
    refine some_dist_some.mpr ⟨.rfl, ?_⟩
    simp only
    exact OFE.NonExpansive.ne H

#rocq_ignore view_auth_proper "Derivable from auth_ne with NonExpansive.eqv"

instance auth_ne₂ : NonExpansive₂ (Auth : DFrac → A → View R) where
  ne _ _ _ Hq _ _ Hf := by
    unfold Auth
    refine (NonExpansive₂.ne ?_ .rfl)
    refine NonExpansive.ne ?_
    exact dist_prod_ext Hq (NonExpansive.ne Hf)

@[rocq_alias view_frag_ne]
instance frag_ne : NonExpansive (Frag : B → View R) where
  ne _ _ _ H := mk.ne.ne .rfl H

#rocq_ignore view_frag_proper "Derivable from frag_ne with NonExpansive.eqv"

@[simp]
def Valid (v : View R) : Prop :=
  match v.auth with
  | some (dq, ag) => ✓ dq ∧ (∀ n, ∃ a, ag ≡{n}≡ toAgree a ∧ R n a (frag v))
  | none => ∀ n, ∃ a, R n a (frag v)

@[simp]
def ValidN (n : Nat) (v : View R) : Prop :=
  match v.auth with
  | some (dq, ag) => ✓{n} dq ∧ (∃ a, ag ≡{n}≡ toAgree a ∧ R n a (frag v))
  | none => ∃ a, R n a (frag v)

@[simp]
def Pcore (v : View R) : Option (View R) :=
  some <| mk (CMRA.core v.auth) (CMRA.core v.frag)

@[simp]
def Op (v1 v2 : View R) : View R :=
  mk (v1.auth • v2.auth) (v1.frag • v2.frag)

/-- A valid view has a valid authority part and a valid fragment. -/
theorem ValidN.pair {n} {x : View R} (Hv : ValidN n x) :
    ✓{n} ((x.auth, x.frag) : Option ((DFrac) × Agree A) × B) := by
  rcases x with ⟨_|⟨q, ag⟩, b⟩
  · obtain ⟨a, Ha⟩ := Hv
    exact ⟨trivial, IsViewRel.rel_validN _ _ _ Ha⟩
  · obtain ⟨Hq, a, Ha1, Ha2⟩ := Hv
    exact ⟨⟨Hq, Agree.validN_ne Ha1.symm trivial⟩, IsViewRel.rel_validN _ _ _ Ha2⟩

@[rocq_alias view_cmra_mixin]
instance instRABase : RABase (View R) where
  pcore := Pcore
  op := Op
  ValidN := ValidN
  Valid := Valid
  op_ne.ne n x1 x2 H := by
    refine mk.ne.ne ?_ ?_
    · exact cmraOption.op_ne.ne <| NonExpansive.ne H
    · exact CMRA.op_ne.ne  <| NonExpansive.ne H
  pcore_ne {n x y} cx H := by
    simp only [Pcore, Option.some.injEq]
    rintro ⟨rfl⟩
    exists ⟨CMRA.core y.auth, CMRA.core y.frag⟩
    exact ⟨rfl, OFE.Dist.core H.1, OFE.Dist.core H.2⟩
  validN_ne {n x1 x2} := by
    rintro ⟨Hl, Hr⟩
    rcases x1 with ⟨_|⟨q1, ag1⟩, b1⟩ <;>
    rcases x2 with ⟨_|⟨q2, ag2⟩, b2⟩ <;>
    simp_all
    · exact fun x H => ⟨x, mono H .rfl Hr.symm.to_incExtN n.le_refl⟩
    intro Hq a Hag HR
    refine ⟨CMRA.validN_ne Hl.1 Hq, ?_⟩
    refine ⟨a, ?_⟩
    refine ⟨Hl.2.symm.trans Hag, ?_⟩
    exact mono HR .rfl Hr.symm.to_incExtN n.le_refl
  valid_iff_validN {x} := by
    simp only [Valid, ValidN]; split
    · exact ⟨fun H n => ⟨H.1, H.2 n⟩, fun H => ⟨(H 0).1, fun n => (H n).2⟩⟩
    · exact Eq.to_iff rfl
  validN_succ {x n} := by
    simp only [ValidN]
    split
    · refine fun H => ⟨H.1, ?_⟩
      rcases H.2 with ⟨ag, Ha⟩; exists ag
      refine ⟨Dist.le Ha.1 n.le_succ, ?_⟩
      exact mono Ha.2 .rfl (RABase.incExtN_refl x.frag) n.le_succ
    · exact fun ⟨z, HR⟩ => ⟨z, mono HR .rfl (RABase.incExtN_refl _) n.le_succ⟩
  validN_op_left {n x y} := by
    rcases x with ⟨_|⟨q1, ag1⟩, b1⟩ <;>
    rcases y with ⟨_|⟨q2, ag2⟩, b2⟩ <;>
    simp [CMRA.op, optionOp]
    · exact fun a Hr => ⟨a, mono Hr .rfl (RABase.incExtN_op_left n b1 b2) n.le_refl⟩
    · exact fun _ a _ Hr => ⟨a, mono Hr .rfl (RABase.incExtN_op_left n b1 b2) n.le_refl⟩
    · exact fun Hq a H Hr => ⟨Hq, ⟨a, ⟨H, mono Hr .rfl (RABase.incExtN_op_left n b1 b2) n.le_refl⟩⟩⟩
    · refine fun Hq a H Hr => ⟨CMRA.validN_op_left Hq, ⟨a, ?_, ?_⟩⟩
      · refine .trans ?_ H
        refine .trans Agree.idemp.symm.dist ?_
        exact CMRA.op_ne.ne <| Agree.op_invN (Agree.validN_ne H.symm trivial)
      · exact mono Hr .rfl (RABase.incExtN_op_left n b1 b2) n.le_refl
  assoc := by simp only [Op, View.mk.injEq]; exact ⟨CMRA.assoc', CMRA.assoc'⟩
  comm := by simp only [Op, View.mk.injEq]; exact ⟨CMRA.comm', CMRA.comm'⟩
  pcore_op_left {x _} := by
    simp only [Pcore, Option.some.injEq]
    rintro rfl
    rcases x with ⟨xa, xf⟩
    simp only [Op, View.mk.injEq]
    exact ⟨CMRA.core_op xa, CMRA.core_op xf⟩
  pcore_idem {_ cx} := by
    simp only [Pcore, Option.some.injEq]
    rcases cx
    simp only [mk.injEq, and_imp]
    rintro rfl rfl
    exact ⟨CMRA.core_idem _, CMRA.core_idem _⟩
  extend {n x y1 y2} Hv He := by
    rcases @CMRA.extend _ _ _ _ ((y1.auth, y1.frag) : _ × B) (y2.auth, y2.frag) Hv.pair He
      with ⟨z1, z2, Hze, Hz1, Hz2⟩
    refine ⟨⟨z1.1, z1.2⟩, ⟨z2.1, z2.2⟩, ?_, Hz1, Hz2⟩
    exact congrArg (fun p => (⟨p.1, p.2⟩ : View R)) Hze

/-- The order on `View R`, inherited componentwise from the authority and fragment parts. -/
@[reducible] def orderN : OrderN (View R) where
  IncludedN n x y := x.auth ≼{n} y.auth ∧ x.frag ≼{n} y.frag
  Included x y := x.auth ≼ y.auth ∧ x.frag ≼ y.frag
  incN_ne ex ey h := ⟨CMRA.incN_ne ex.1 ey.1 h.1, CMRA.incN_ne ex.2 ey.2 h.2⟩
  incN_succ h := ⟨CMRA.incN_succ h.1, CMRA.incN_succ h.2⟩
  incN_trans h1 h2 := ⟨CMRA.incN_trans h1.1 h2.1, CMRA.incN_trans h1.2 h2.2⟩
  inc_trans h1 h2 := ⟨CMRA.inc_trans h1.1 h2.1, CMRA.inc_trans h1.2 h2.2⟩
  incN_of_inc n h := ⟨CMRA.incN_of_inc n h.1, CMRA.incN_of_inc n h.2⟩

section
attribute [local instance] View.orderN

theorem increasing_auth {v : View R} (h : CMRA.Increasing v) : CMRA.Increasing v.auth where
  increasing w := (h.increasing ⟨w, UCMRA.unit⟩).1

theorem increasing_frag {v : View R} (h : CMRA.Increasing v) : CMRA.Increasing v.frag where
  increasing w := (h.increasing ⟨none, w⟩).2

theorem increasing_mk {v : View R} (ha : CMRA.Increasing v.auth) (hb : CMRA.Increasing v.frag) :
    CMRA.Increasing v where
  increasing w := ⟨ha.increasing w.auth, hb.increasing w.frag⟩

instance instCMRA : CMRA (View R) where
  toRABase := instRABase
  toOrderN := View.orderN
  op_monoN_left z h := ⟨CMRA.op_monoN_left z.auth h.1, CMRA.op_monoN_left z.frag h.2⟩
  op_mono_left z h := ⟨CMRA.op_mono_left z.auth h.1, CMRA.op_mono_left z.frag h.2⟩
  validN_of_incN {n x y} h v := by
    rcases x with ⟨_|⟨q1, ag1⟩, b1⟩ <;> rcases y with ⟨_|⟨q2, ag2⟩, b2⟩
    · obtain ⟨a, Ha⟩ := v
      exact ⟨a, mono_ord Ha .rfl h.2 n.le_refl⟩
    · obtain ⟨_, a, _, Ha⟩ := v
      exact ⟨a, mono_ord Ha .rfl h.2 n.le_refl⟩
    · exact h.1.elim
    · obtain ⟨Hq, a, Hag, Ha⟩ := v
      rcases h.1 with e | i
      · exact ⟨CMRA.validN_ne e.1.symm Hq, a, e.2.trans Hag, mono_ord Ha .rfl h.2 n.le_refl⟩
      · refine ⟨CMRA.validN_of_incN i.1 Hq, a, ?_, mono_ord Ha .rfl h.2 n.le_refl⟩
        exact (Agree.valid_includedN (Agree.validN_ne Hag.symm trivial) i.2).trans Hag
  pcore_monoN {_ x y _} h e := by
    obtain rfl := Option.some.inj e
    exact ⟨_, rfl, CMRA.core_incN_core h.1, CMRA.core_incN_core h.2⟩
  pcore_mono {x y _} h e := by
    obtain rfl := Option.some.inj e
    exact ⟨_, rfl, CMRA.core_mono h.1, CMRA.core_mono h.2⟩
  pcore_order_op {x _} e y := by
    obtain rfl := Option.some.inj e
    exact ⟨_, rfl, CMRA.core_op_mono x.auth y.auth, CMRA.core_op_mono x.frag y.frag⟩
  pcore_increasing {x _} e := by
    obtain rfl := Option.some.inj e
    exact increasing_mk inferInstance inferInstance
  increasing_closed {n x y} h h' :=
    increasing_mk
      (CMRA.increasing_closed (increasing_auth h) (Or.imp (·.1) (·.1) h'))
      (CMRA.increasing_closed (increasing_frag h) (Or.imp (·.2) (·.2) h'))
  incN_extend {n x y} v h := by
    obtain ⟨za, hza, ea⟩ := CMRA.incN_extend v.pair.1 h.1
    obtain ⟨zf, hzf, ef⟩ := CMRA.incN_extend v.pair.2 h.2
    exact ⟨⟨za, zf⟩, ⟨hza, hzf⟩, ea, ef⟩

end

@[rocq_alias viewUR]
instance instUCMRA : UCMRA (View R) where
  toCMRA := instCMRA
  unit := ⟨UCMRA.unit, UCMRA.unit⟩
  unit_valid := IsViewRel.rel_unit
  unit_left_id := by
    rintro ⟨xa, xf⟩
    show (⟨UCMRA.unit • xa, UCMRA.unit • xf⟩ : View R) = ⟨xa, xf⟩
    rw [CMRA.ucmra_unit_left_id, CMRA.ucmra_unit_left_id]
  pcore_unit := congrArg some (congrArg (View.mk _) (CMRA.core_eqv_self UCMRA.unit))
  inc_refl x := ⟨CMRA.inc_refl x.auth, CMRA.inc_refl x.frag⟩

/-- A view over an affine fragment algebra is affine. -/
instance [CMRA.Affine B] : CMRA.Affine (View R) where
  increasing v :=
    increasing_mk (CMRA.Affine.increasing v.auth) (CMRA.Affine.increasing v.frag)

#rocq_ignore viewR "Use the plain View type"
#rocq_ignore view_valid_instance "In the CMRA instance"
#rocq_ignore view_validN_instance "In the CMRA instance"
#rocq_ignore view_pcore_instance "In the CMRA instance"
#rocq_ignore view_op_instance "In the CMRA instance"
#rocq_ignore view_valid_eq "Defeq from the CMRA instance"
#rocq_ignore view_validN_eq "Defeq from the CMRA instance"
#rocq_ignore view_pcore_eq "Defeq from the CMRA instance"
#rocq_ignore view_op_eq "Defeq from the CMRA instance"

@[rocq_alias view_cmra_discrete]
instance [Discrete A] [CMRA.Discrete B] [IsViewRelDiscrete R] : CMRA.Discrete (View R) where
  discrete_inc h := ⟨CMRA.discrete_inc h.1, CMRA.discrete_inc h.2⟩
  discrete_valid {x} := by
    simp only [CMRA.ValidN, ValidN, CMRA.Valid, Valid]
    split
    · rintro ⟨H1, ⟨a, H2, H3⟩⟩
      refine ⟨H1, fun n => ⟨a, ⟨?_, ?_⟩⟩⟩
      · exact (OFE.Discrete.discrete_0 H2).dist
      · exact IsViewRelDiscrete.discrete _ _ _ H3
    · exact fun ⟨a, H⟩ _ => ⟨a, IsViewRelDiscrete.discrete _ _ _ H⟩

#rocq_ignore view_empty_instance "Inlined in the UCMRA instance"
#rocq_ignore view_ucmra_mixin "Not needed"

@[rocq_alias view_auth_dfrac_op]
theorem auth_op_auth_eqv : (●V{dq1 • dq2} a : View R) = ((●V{dq1} a) • ●V{dq2} a : View R) :=
  by simp only [View.Auth, Op, CMRA.op, optionOp, Prod.op, View.mk.injEq, CMRA.ucmra_unit_left_id]
     exact ⟨congrArg some (congrArg (Prod.mk _) Agree.idemp.symm), trivial⟩

set_option synthInstance.checkSynthOrder false in
@[rocq_alias view_auth_dfrac_is_op]
instance isOp_view_auth_dfrac {dq dq1 dq2 : DFrac} {a : A}
    [h : IsOp d dq dq1 dq2] :
    IsOp d (●V{dq} a : View R) (●V{dq1} a) (●V{dq2} a) where
  is_op := by
    rw [h.is_op]
    apply auth_op_auth_eqv

@[rocq_alias view_frag_op]
theorem frag_op_eq : (◯V (b1 • b2) : View R) = ((◯V b1) • ◯V b2 : View R) := rfl

@[rocq_alias view_frag_mono]
theorem frag_incExt_of_incExt (H : b1 ≼ₑ b2) : (◯V b1 : View R) ≼ₑ ◯V b2 := by
  rcases H with ⟨c, H⟩
  rw [H, frag_op_eq]
  exact RABase.incExt_op_left _ _

@[rocq_alias view_frag_core]
theorem frag_core : CMRA.core (◯V b : View R) = ◯V (CMRA.core b) := rfl

@[rocq_alias view_both_core_discarded]
theorem auth_discard_op_frag_core : CMRA.core ((●V{.discard} a) • ◯V b : View R) = ((●V{.discard} a) • ◯V (CMRA.core b) : View R) :=
  congrArg (View.mk _) ((congrArg CMRA.core CMRA.ucmra_unit_left_id).trans CMRA.ucmra_unit_left_id.symm)

@[rocq_alias view_both_core_frac]
theorem auth_own_op_frag_core : CMRA.core ((●V{.own q} a) • ◯V b : View R) = (◯V (CMRA.core b) : View R) :=
  congrArg (View.mk _) (congrArg CMRA.core CMRA.ucmra_unit_left_id)

@[rocq_alias view_auth_core_id]
instance : CMRA.CoreId (●V{.discard} a : View R) where
  core_id := congrArg some (congrArg (View.mk _) (CMRA.core_eqv_self UCMRA.unit))

@[rocq_alias view_frag_core_id]
instance [CMRA.CoreId b] : CMRA.CoreId (◯V b : View R) where
  core_id :=
    congrArg some (congrArg (View.mk _) (CMRA.coreId_iff_core_eqv_self.mp (by trivial)))

@[rocq_alias view_both_core_id]
instance [CMRA.CoreId b] : CMRA.CoreId ((●V{.discard} a : View R) • ◯V b) where
  core_id :=
    congrArg some (congrArg (View.mk _)
      (((congrArg CMRA.core CMRA.ucmra_unit_left_id).trans
        (CMRA.coreId_iff_core_eqv_self.mp (by trivial))).trans CMRA.ucmra_unit_left_id.symm))

@[rocq_alias view_frag_is_op]
instance {b b1 b2 : B} [h : IsOp d b b1 b2] :
    IsOp d (◯V b : View R) (◯V b1) (◯V b2) where
  is_op := by rw [h.is_op]; exact frag_op_eq

section BigOp
open Algebra Std

@[rocq_alias view_frag_sep_homomorphism]
instance : MonoidHomomorphism CMRA.op CMRA.op UCMRA.unit UCMRA.unit (· = ·)
    (Frag : B → View R) where
  rel_refl := rfl
  rel_trans := Eq.trans
  op_proper h₁ h₂ := h₁ ▸ h₂ ▸ rfl
  map_ne := frag_ne
  map_op := frag_op_eq
  map_unit := rfl

@[rocq_alias big_opL_view_frag]
theorem bigOpL_frag (g : Nat → C → B) (l : List C) :
    (◯V ([^ CMRA.op list] k ↦ x ∈ l, g k x) : View R) = [^ CMRA.op list] k ↦ x ∈ l, ◯V (g k x) :=
  BigOpL.bigOpL_hom _ _

@[rocq_alias big_opM_view_frag]
theorem bigOpM_frag [LawfulFiniteMap M' K] (g : K → C → B) (m : M' C) :
    (◯V ([^ CMRA.op map] k ↦ x ∈ m, g k x) : View R) = [^ CMRA.op map] k ↦ x ∈ m, ◯V (g k x) :=
  BigOpM.bigOpM_hom _ _

@[rocq_alias big_opS_view_frag]
theorem bigOpS_frag [LawfulFiniteSet S' C] (g : C → B) (X : S') :
    (◯V ([^ CMRA.op set] x ∈ X, g x) : View R) = [^ CMRA.op set] x ∈ X, ◯V (g x) :=
  BigOpS.hom inferInstance _ _

@[rocq_alias big_opMS_view_frag]
theorem bigOpMS_frag [LawfulFiniteMultiSet MS' C] (g : C → B) (X : MS') :
    (◯V ([^ CMRA.op mset] x ∈ X, g x) : View R) = [^ CMRA.op mset] x ∈ X, ◯V (g x) :=
  BigOpMS.hom inferInstance _ _

end BigOp

@[rocq_alias view_auth_dfrac_op_invN]
theorem dist_of_validN_auth (H : ✓{n} ((●V{dq1} a1 : View R) • ●V{dq2} a2)) : a1 ≡{n}≡ a2 := by
  rcases H with ⟨_, _, H, _⟩
  refine toAgree.inj (Agree.op_invN ?_)
  exact Agree.validN_ne H.symm trivial

#rocq_ignore view_auth_dfrac_op_inv "Use eq_of_valid_auth"

@[rocq_alias view_auth_dfrac_op_inv_L]
theorem eq_of_valid_auth
    (H : ✓ ((●V{dq1} a1 : View R) • ●V{dq2} a2)) : a1 = a2 :=
  OFE.eq_dist_2 fun _ => dist_of_validN_auth H.validN

@[rocq_alias view_auth_dfrac_validN]
theorem auth_validN_iff : ✓{n} (●V{dq} a : View R) ↔ ✓{n}dq ∧ R n a UCMRA.unit :=
  and_congr_right fun _ => IsViewRel.of_agree_dist_iff .rfl

@[rocq_alias view_auth_validN]
theorem auth_one_validN_iff n a : ✓{n} (●V a : View R) ↔ R n a UCMRA.unit :=
  ⟨(auth_validN_iff.mp · |>.2), (auth_validN_iff.mpr ⟨valid_own_one, ·⟩)⟩

@[rocq_alias view_auth_dfrac_op_validN]
theorem auth_op_auth_validN_iff :
    ✓{n} ((●V{dq1} a1 : View R) • ●V{dq2} a2) ↔ ✓(dq1 • dq2) ∧ a1 ≡{n}≡ a2 ∧ R n a1 UCMRA.unit := by
  refine ⟨fun H => ?_, fun H => ?_⟩
  · let Ha' : a1 ≡{n}≡ a2 := dist_of_validN_auth H
    rcases H with ⟨Hq, _, Ha, HR⟩
    refine ⟨Hq, Ha', mono HR ?_ RABase.incExtN_unit n.le_refl⟩
    refine .trans ?_ Ha'.symm
    refine toAgree.inj (Ha.symm.trans ?_)
    apply CMRA.op_commN.trans
    apply (CMRA.op_ne.ne (toAgree.ne.ne Ha')).trans
    exact Agree.idemp.dist
  · simp [CMRA.op, CMRA.ValidN, ValidN, optionOp, Prod.op]
    refine ⟨H.1, a1, ?_, ?_⟩
    · exact (CMRA.op_ne.ne <| toAgree.ne.ne H.2.1.symm).trans Agree.idemp.dist
    · refine mono H.2.2 .rfl ?_ n.le_refl
      exact OFE.Dist.to_incExtN <| CMRA.unit_left_id_dist UCMRA.unit

@[rocq_alias view_auth_op_validN]
theorem auth_one_op_auth_one_validN_iff : ✓{n} ((●V a1 : View R) • ●V a2) ↔ False := by
  refine auth_op_auth_validN_iff.trans ?_
  simp only [iff_false, not_and]
  intro h
  simp only [CMRA.Valid, CMRA.op, op, valid] at h
  grind

@[rocq_alias view_frag_validN]
theorem frag_validN_iff : ✓{n} (◯V b : View R) ↔ ∃ a, R n a b := by rfl

@[rocq_alias view_both_dfrac_validN]
theorem auth_op_frag_validN_iff : ✓{n} ((●V{dq} a : View R) • ◯V b) ↔ ✓dq ∧ R n a b :=
  and_congr_right (fun _ => IsViewRel.of_agree_dist_iff <| CMRA.unit_left_id_dist b)

@[rocq_alias view_both_validN]
theorem auth_one_op_frag_validN_iff : ✓{n} ((●V a : View R) • ◯V b) ↔ R n a b :=
  auth_op_frag_validN_iff.trans <| and_iff_right_iff_imp.mpr (fun _ => valid_own_one)

@[rocq_alias view_auth_dfrac_valid]
theorem auth_valid_iff : ✓ (●V{dq} a : View R) ↔ ✓dq ∧ ∀ n, R n a UCMRA.unit :=
  and_congr_right (fun _=> forall_congr' fun _ => IsViewRel.of_agree_dist_iff .rfl)

@[rocq_alias view_auth_valid]
theorem auth_one_valid_iff : ✓ (●V a : View R) ↔ ∀ n, R n a UCMRA.unit :=
  auth_valid_iff.trans <| and_iff_right_iff_imp.mpr (fun _ => valid_own_one)

@[rocq_alias view_auth_dfrac_op_valid]
theorem auth_op_auth_valid_iff : ✓ ((●V{dq1} a1 : View R) • ●V{dq2} a2) ↔ ✓(dq1 • dq2) ∧ a1 = a2 ∧ ∀ n, R n a1 UCMRA.unit := by
  refine CMRA.valid_iff_validN.trans ?_
  refine ⟨fun H => ?_, fun H n => ?_⟩
  · simp [valid, CMRA.op, op, optionOp, CMRA.ValidN, ValidN] at H
    let Hn n := dist_of_validN_auth <| H n
    refine ⟨(H 0).1, OFE.eq_dist_2 Hn, fun n => ?_⟩
    · rcases (H n) with ⟨_, _, Hl, H⟩
      apply mono H ?_ RABase.incExtN_unit n.le_refl
      apply toAgree.inj (Hl.symm.trans ?_)
      exact (CMRA.op_ne.ne <| toAgree.ne.ne (Hn _).symm).trans Agree.idemp.dist
  · exact auth_op_auth_validN_iff.mpr ⟨H.1, H.2.1.dist, H.2.2 n⟩

@[rocq_alias view_auth_op_valid]
theorem auth_one_op_auth_one_valid_iff : ✓ ((●V a1 : View R) • ●V a2) ↔ False := by
  refine auth_op_auth_valid_iff.trans ?_
  simp [CMRA.op, op, CMRA.Valid, op, valid]
  grind

@[rocq_alias view_frag_valid]
theorem frag_valid_iff : ✓ (◯V b : View R) ↔ ∀ n, ∃ a, R n a b := by rfl

@[rocq_alias view_both_dfrac_valid]
theorem auth_op_frag_valid_iff : ✓ ((●V{dq} a : View R) • ◯V b) ↔ ✓dq ∧ ∀ n, R n a b :=
  and_congr_right (fun _ => forall_congr' fun _ => IsViewRel.of_agree_dist_iff <| CMRA.unit_left_id_dist b)

@[rocq_alias view_both_valid]
theorem auth_one_op_frag_valid_iff : ✓ ((●V a : View R) • ◯V b) ↔ ∀ n, R n a b :=
  auth_op_frag_valid_iff.trans <| and_iff_right_iff_imp.mpr (fun _ => valid_own_one)

open CMRA in
@[rocq_alias view_auth_dfrac_includedN]
theorem auth_incExtN_auth_op_frag_iff :
    (●V{dq1} a1 : View R) ≼ₑ{n} ((●V{dq2} a2) • ◯V b) ↔
      (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡{n}≡ a2 := by
  refine ⟨?_, fun H => ?_⟩
  · simp only [Auth, Frag, RABase.IncExtN, CMRA.op]
    rintro ⟨(_|⟨dqf, af⟩),⟨⟨x1, x2⟩, y⟩⟩
    · exact ⟨.inr x1.symm, toAgree.inj x2.symm⟩
    · exact ⟨.inl ⟨dqf, x1⟩, Agree.toAgree_includedN.mp ⟨af, x2⟩⟩
  · rcases H with ⟨(⟨z, HRz⟩| HRa2), HRb⟩
    · calc (●V{dq1} a1 : View R)
             ≼ₑ{n} ((●V{dq1} a1) • ((◯V b) • ●V{z} a1)) := by exists ((◯V b) • ●V{z} a1)
           _ ≡{n}≡ ((◯V b) • ●V{z} a1) • ●V{dq1} a1 := op_commN
           _ ≡{n}≡ (◯V b) • ((●V{z} a1) • ●V{dq1} a1) := op_assocN.symm
           _ ≡{n}≡ (◯V b) • ((●V{dq1} a1) • ●V{z} a1) := op_ne.ne op_commN
           _ ≡{n}≡ (◯V b) • ●V{dq1 • z} a1 := op_ne.ne auth_op_auth_eqv.symm.dist
           _ ≡{n}≡ (◯V b) • ●V{dq2} a2 := op_ne.ne (NonExpansive₂.ne HRz.symm.dist HRb)
           _ ≡{n}≡ ((●V{dq2} a2) • ◯V b) := op_commN
    · exists (◯V b)
      refine comm'.dist.trans ?_
      refine (.trans ?_ comm'.dist)
      apply CMRA.op_ne.ne
      exact HRa2 ▸NonExpansive₂.ne rfl HRb.symm

open CMRA in
@[rocq_alias view_auth_dfrac_included]
theorem auth_incExt_auth_op_frag_iff :
    ((●V{dq1} a1 : View R) ≼ₑ (●V{dq2} a2 : View R) • ◯V b) ↔
      (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 = a2 := by
  refine ⟨fun H => ⟨?_, ?_⟩, fun H => ?_⟩
  · exact auth_incExtN_auth_op_frag_iff (n := 0) |>.mp (RABase.incExtN_of_incExt _ H) |>.1
  · refine OFE.eq_dist_2 (fun n => ?_)
    exact auth_incExtN_auth_op_frag_iff |>.mp (RABase.incExtN_of_incExt _ H) |>.2
  · rcases H with ⟨(⟨q, Hq⟩|Hq), Ha⟩
    · calc (●V{dq1} a1 : View R)
           _ ≼ₑ (●V{dq1} a1) • ((●V{q} a1) • ◯V b) := by exists ((●V{q} a1) • ◯V b)
           _ ≼ₑ ((●V{dq1} a1) • ●V{q} a1) • ◯V b := by rw [CMRA.assoc']
           _ ≼ₑ (◯V b) • ((●V{dq1} a1) • ●V{q} a1) := by rw [CMRA.comm']
           _ ≼ₑ (◯V b) • ●V{dq1 • q} a1 := by rw [View.auth_op_auth_eqv]
           _ ≼ₑ (●V{dq2} a2) • ◯V b := by rw [Hq, Ha, comm', View.auth_op_auth_eqv]
    · exists (◯V b)
      rw [Hq, Ha]

@[rocq_alias view_auth_includedN]
theorem auth_one_incExtN_auth_one_op_frag_iff :
    (●V a1 : View R) ≼ₑ{n} ((●V a2) • ◯V b) ↔ a1 ≡{n}≡ a2 :=
  auth_incExtN_auth_op_frag_iff.trans <| and_iff_right_iff_imp.mpr <| fun _ => .inr rfl

@[rocq_alias view_auth_included]
theorem auth_one_incExt_auth_one_op_frag_iff :
    (●V a1 : View R) ≼ₑ ((●V a2) • ◯V b) ↔ a1 = a2 :=
  auth_incExt_auth_op_frag_iff.trans <| and_iff_right_iff_imp.mpr <| fun _ => .inr rfl

open CMRA in
@[rocq_alias view_frag_includedN]
theorem frag_incExtN_auth_op_frag_iff :
    (◯V b1 : View R) ≼ₑ{n} ((●V{p} a) • ◯V b2) ↔ b1 ≼ₑ{n} b2 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨xf, ⟨_, Hb⟩⟩
    have Hb' : b2 ≡{n}≡ b1 • xf.frag := CMRA.ucmra_unit_left_id.dist.symm.trans Hb
    refine (RABase.incExtN_iff_right <| Hb'.symm).mp ?_
    exists xf.frag
  · rintro ⟨bf, Hbf⟩
    calc (◯V b1 : View R)
         _ ≼ₑ{n} (◯V b1) • ((◯V bf) • ●V{p} a) := by exists ((◯V bf) • ●V{p} a)
         _ ≡{n}≡ ((◯V b1) • ◯V bf) • ●V{p} a := op_assocN
         _ ≡{n}≡ (●V{p} a) • ((◯V b1) • ◯V bf) := op_commN
         _ ≼ₑ{n} (●V{p} a) • ◯V b1 • bf := by rw [frag_op_eq]
         _ ≡{n}≡ (●V{p} a) • ◯V b2 := op_ne.ne (NonExpansive.ne Hbf.symm)

open CMRA in
@[rocq_alias view_frag_included]
theorem frag_incExt_auth_op_frag_iff :
    (◯V b1 : View R) ≼ₑ ((●V{p} a) • ◯V b2) ↔ b1 ≼ₑ b2 := by
  constructor
  · rintro ⟨xf, HH⟩
    have Hb' : b2 = b1 • xf.frag :=
      (UCMRA.unit_left_id).symm.trans (congrArg View.frag HH)
    rw [Hb']
    exists xf.frag
  · rintro ⟨bf, Hbf⟩
    calc (◯V b1 : View R)
         _ ≼ₑ (◯V b1) • ((◯V bf) • ●V{p} a) := by exists ((◯V bf) • ●V{p} a)
         _ ≼ₑ ((◯V b1) • ◯V bf) • ●V{p} a := by rw [CMRA.assoc']
         _ ≼ₑ (●V{p} a) • ((◯V b1) • ◯V bf) := by rw [CMRA.comm']
         _ ≼ₑ (●V{p} a) • ◯V b1 • bf := by rw [frag_op_eq]
         _ ≼ₑ (●V{p} a) • ◯V b2 := by rw [Hbf]

open CMRA in
@[rocq_alias view_both_dfrac_includedN]
theorem auth_op_frag_incExtN_auth_op_frag_iff :
    ((●V{dq1} a1 : View R) • ◯V b1) ≼ₑ{n} ((●V{dq2} a2) • ◯V b2) ↔
      (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡{n}≡ a2 ∧ b1 ≼ₑ{n} b2 := by
  refine ⟨fun H => ?_, fun ⟨H0, H1, ⟨bf, H2⟩⟩ => ?_⟩
  · rw [← and_assoc]
    refine ⟨?_, ?_⟩
    · apply (auth_incExtN_auth_op_frag_iff (R := R)).mp
      exact (RABase.incExtN_op_left _ _ _).trans H
    · apply (frag_incExtN_auth_op_frag_iff (R := R)).mp
      exact (RABase.incExtN_op_right _ _ _).trans H
  · calc ((●V{dq1} a1) • ◯V b1 : View R)
         _ ≼ₑ{n} ((●V{dq2} a2) • ◯V bf) • ◯V b1 :=
           RABase.op_monoN_left_ext _ <| auth_incExtN_auth_op_frag_iff.mpr ⟨H0, H1⟩
         _ ≡{n}≡ (●V{dq2} a2) • ((◯V bf) • ◯V b1) := op_assocN.symm
         _ ≼ₑ{n} (●V{dq2} a2) • ◯V bf • b1 := by rw [frag_op_eq]
         _ ≡{n}≡ (●V{dq2} a2) • ◯V b2 :=
           CMRA.op_ne.ne (NonExpansive.ne (H2.trans comm'.dist |>.symm))

open CMRA in
@[rocq_alias view_both_dfrac_included]
theorem auth_op_frag_incExt_auth_op_frag_iff :
    ((●V{dq1} a1 : View R) • ◯V b1) ≼ₑ ((●V{dq2} a2) • ◯V b2) ↔
      (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 = a2 ∧ b1 ≼ₑ b2 := by
  refine ⟨fun H => ?_, fun ⟨H0, H1, ⟨bf, H2⟩⟩ => ?_⟩
  · rw [← and_assoc]
    refine ⟨?_, ?_⟩
    · apply (auth_incExt_auth_op_frag_iff (R := R)).mp
      exact (RABase.incExt_op_left (●V{dq1} a1) (◯V b1)).trans H
    · apply (frag_incExt_auth_op_frag_iff (R := R)).mp
      exact (RABase.incExt_op_right _ _).trans H
  · calc ((●V{dq1} a1) • ◯V b1 : View R)
         _ ≼ₑ ((●V{dq2} a2) • ◯V bf) • ◯V b1 :=
           RABase.op_mono_left_ext _ <| auth_incExt_auth_op_frag_iff.mpr ⟨H0, H1⟩
         _ ≼ₑ (●V{dq2} a2) • ((◯V bf) • ◯V b1) := by rw [← CMRA.assoc']
         _ ≼ₑ (●V{dq2} a2) • ◯V bf • b1 := .rfl
         _ ≼ₑ (●V{dq2} a2) • ◯V b2 := by rw [← H2.trans comm]

@[rocq_alias view_both_includedN]
theorem auth_one_op_frag_incExtN_auth_one_op_frag_iff :
    ((●V a1 : View R) • ◯V b1) ≼ₑ{n} ((●V a2) • ◯V b2) ↔ (a1 ≡{n}≡ a2 ∧ b1 ≼ₑ{n} b2) :=
  auth_op_frag_incExtN_auth_op_frag_iff.trans <|
    and_iff_right_iff_imp.mpr <| fun _ => .inr rfl

@[rocq_alias view_both_included]
theorem auth_one_op_frag_incExt_auth_one_op_frag_iff :
    ((●V a1 : View R) • ◯V b1) ≼ₑ ((●V a2) • ◯V b2) ↔ a1 = a2 ∧ b1 ≼ₑ b2 :=
  auth_op_frag_incExt_auth_op_frag_iff.trans <|
    and_iff_right_iff_imp.mpr <| fun _ => .inr rfl

#rocq_ignore view_core_eq "Not needed"
#rocq_ignore view_valid_eq "Not needed"
#rocq_ignore view_validN_eq "Not needed"
#rocq_ignore view_pcore_eq "Not needed"
#rocq_ignore view_core_eq "Not needed"
#rocq_ignore view_op_eq "Not needed"

end CMRA

section Updates

variable [OFE A] [IB : UCMRA B] {R : ViewRel A B} [IsViewRel R]

open CMRA DFrac

@[rocq_alias view_updateP]
theorem auth_one_op_frag_updateP {Pab : A → B → Prop}
    (Hup : ∀ n bf, R n a (b • bf) → ∃ a' b', Pab a' b' ∧ R n a' (b' • bf)) :
    ((●V a) • ◯V b : View R) ~~>: fun k => ∃ a' b', k = ((●V a') • ◯V b' : View R) ∧ Pab a' b' := by
  refine UpdateP.total.mpr (fun n ⟨ag, bf⟩ => ?_)
  rcases ag with (_|⟨dq, ag⟩)
  · intro H
    obtain ⟨_, a0, He', Hrel'⟩ := H
    have Hrel : R n a (b • bf) := by
      apply IsViewRel.mono Hrel' (toAgree.inj He').symm _ n.le_refl
      apply Iris.OFE.Dist.to_incExtN
      refine CMRA.comm.dist.trans (.trans ?_ CMRA.comm.dist)
      refine CMRA.op_ne.ne ?_
      exact (CMRA.unit_left_id_dist b).symm
    obtain ⟨a', b', Hab', Hrel''⟩ := Hup _ _ Hrel
    refine ⟨((●V a') • ◯V b'), ?_, ⟨by trivial, ?_⟩⟩
    · exists a'; exists b'
    · refine ⟨a', .rfl, ?_⟩
      apply IsViewRel.mono Hrel'' .rfl _ n.le_refl
      apply Iris.OFE.Dist.to_incExtN
      refine comm.dist.trans (.trans ?_ CMRA.comm.dist)
      refine op_ne.ne <| unit_left_id_dist b'
  · letI _ := own_whole_exclusive
    exact (not_valid_exclN_op_left ·.1 |>.elim)

@[rocq_alias view_update]
theorem auth_one_op_frag_update (Hup : ∀ n bf, R n a (b • bf) → R n a' (b' • bf)) :
    ((●V a) • ◯V b : View R) ~~> (●V a') • ◯V b' := by
  apply Update.of_updateP
  apply UpdateP.weaken
  · apply auth_one_op_frag_updateP (Pab := fun a b => a = a' ∧ b = b')
    exact fun _ _ H => ⟨a', b', ⟨rfl, rfl⟩, Hup _ _ H⟩
  · rintro y ⟨a', b', H, rfl, rfl⟩
    exact H.symm

@[rocq_alias view_update_alloc]
theorem auth_one_alloc (Hup : ∀ n bf, R n a bf → R n a' (b' • bf)) :
    ((●V a) ~~> ((●V a' : View R) • ◯V b')) := by
  rw [← CMRA.unit_right_id (x := (●V{own 1} a))]
  refine auth_one_op_frag_update (fun n bf H => Hup n bf <| IsViewRel.mono H .rfl ?_ n.le_refl)
  exact RABase.incExtN_op_right n unit bf

@[rocq_alias view_update_dealloc]
theorem auth_one_op_frag_dealloc (Hup : (∀ n bf, R n a (b • bf) → R n a' bf)) :
    ((●V a : View R) • ◯V b) ~~> ●V a' := by
  rw [← CMRA.unit_right_id (x := (●V{own 1} a'))]
  refine auth_one_op_frag_update (fun n bf H => ?_)
  refine IsViewRel.mono (Hup n bf H) .rfl ?_ n.le_refl
  exact (unit_left_id_dist bf).to_incExtN

@[rocq_alias view_update_auth]
theorem auth_one_update (Hup : ∀ n bf, R n a bf → R n a' bf) :
    (●V a : View R) ~~> ●V a' := by
  rw [← CMRA.unit_right_id (x := (●V{own 1} a'))]
  rw [← CMRA.unit_right_id (x := (●V{own 1} a))]
  refine auth_one_op_frag_update (fun n bf H => ?_)
  exact IsViewRel.mono (Hup n _ H) .rfl .rfl n.le_refl

@[rocq_alias view_updateP_auth_dfrac]
theorem auth_updateP (Hupd : dq ~~>: P) :
    (●V{dq} a : View R) ~~>: (fun k => ∃ dq', (k = ●V{dq'} a) ∧ P dq') := by
  refine UpdateP.total.mpr (fun n ⟨ag, bf⟩ => ?_)
  rcases ag with (_|⟨dq', ag⟩) <;> rintro ⟨Hv, a', _, _⟩
  · obtain ⟨dr, Hdr, Heq⟩ := Hupd n none Hv
    refine ⟨●V{dr} a, (by exists dr), ⟨Heq, (by exists a')⟩⟩
  · obtain ⟨dr, Hdr, Heq⟩ := Hupd n (some dq') Hv
    refine ⟨●V{dr} a, (by exists dr), ⟨Heq, (by exists a')⟩⟩

@[rocq_alias view_update_auth_persist]
theorem auth_discard : (●V{dq} a : View R) ~~> ●V{.discard} a := by
  apply Update.lift_updateP (g := fun dq => ●V{dq} a)
  · exact fun _ => auth_updateP
  · exact DFrac.update_discard

@[rocq_alias view_updateP_auth_unpersist]
theorem auth_acquire :
    (●V{.discard} a : View R) ~~>: fun k => ∃ q, k = ●V{.own q} a := by
  apply UpdateP.weaken
  · apply auth_updateP
    exact DFrac.update_acquire
  · rintro y ⟨dq, rfl, q', rfl⟩
    exists q'

@[rocq_alias view_updateP_both_unpersist]
theorem auth_op_frag_acquire :
    ((●V{.discard} a : View R) • ◯V b) ~~>: fun k => ∃ q, k = ((●V{.own q} a : View R) • ◯V b ):= by
  apply UpdateP.op
  apply auth_acquire
  apply UpdateP.id rfl
  rintro z1 z2 ⟨q, rfl⟩ rfl; exists q

@[rocq_alias view_updateP_frag]
theorem frag_updateP {P : B → Prop} (Hupd : ∀ a n bf, R n a (b • bf) → ∃ b', P b' ∧ R n a (b' • bf)) :
    (◯V b : View R) ~~>: (fun k => ∃ b', (k = (◯V b' : View R)) ∧ P b') := by
  refine UpdateP.total.mpr (fun n ⟨ag, bf⟩ => ?_)
  rcases ag with (_|⟨dq,af⟩)
  · rintro ⟨a, Ha⟩
    obtain ⟨b', HP, Hb'⟩ := Hupd a n bf Ha
    exists (◯V b')
    simp only [mk.injEq, true_and, exists_eq_left']
    exact ⟨HP, ⟨a, Hb'⟩⟩
  · rintro ⟨Hq, a, Hae, Hr⟩
    obtain ⟨b', Hb', Hp⟩ := Hupd a n bf Hr
    exists (◯V b')
    simp only [mk.injEq, true_and, exists_eq_left']
    refine ⟨Hb', ?_⟩
    simp [CMRA.ValidN, ValidN, CMRA.op, optionOp]
    exact ⟨Hq, ⟨a, Hae, Hp⟩⟩

@[rocq_alias view_update_frag]
theorem frag_update (Hupd : ∀ a n bf, R n a (b • bf) → R n a (b' • bf)) :
    (◯V b : View R) ~~> (◯V b' : View R) := by
  refine Update.total.mpr (fun n ⟨ag, bf⟩ => ?_)
  rcases ag with (_|⟨dq,af⟩)
  simp only [CMRA.ValidN]
  · simp_all [CMRA.op, optionOp]
    intro a HR
    exists a
    exact Hupd _ _ _ HR
  · simp_all [CMRA.op, CMRA.ValidN]
    intro Hq a He Hr
    exists a
    exact ⟨He, Hupd _ _ _ Hr⟩

@[rocq_alias view_update_dfrac_alloc]
theorem auth_alloc (Hup : ∀ n bf, R n a bf → R n a (b • bf)) :
    (●V{dq} a : View R) ~~> ((●V{dq} a) • ◯V b) := by
  refine Update.total.mpr (fun n ⟨ag', bf⟩ => ?_)
  obtain (_|⟨p, ag⟩) := ag'
  · simp [CMRA.op, optionOp, CMRA.ValidN, ValidN]
    intro Hq a' Hag HR
    refine ⟨Hq, a', Hag, ?_⟩
    have HR' := IsViewRel.mono HR (toAgree.inj Hag).symm (RABase.incExtN_op_right n UCMRA.unit bf) n.le_refl
    apply IsViewRel.mono (Hup n bf HR') (toAgree.inj Hag) ?_ n.le_refl
    apply Iris.OFE.Dist.to_incExtN
    refine CMRA.comm.dist.trans (.trans ?_ CMRA.comm.dist)
    refine CMRA.op_ne.ne ?_
    exact (CMRA.unit_left_id_dist _)
  · rintro ⟨Hv, a0, Hag, Hrel⟩
    refine ⟨Hv, ?_⟩
    exists a0
    refine ⟨Hag, ?_⟩
    have Heq  := Agree.toAgree_includedN.mp ⟨ag, Hag.symm⟩
    have HR' := IsViewRel.mono Hrel Heq.symm (RABase.incExtN_op_right n UCMRA.unit bf) n.le_refl
    apply IsViewRel.mono (Hup _ _ HR') Heq ?_ n.le_refl
    apply Iris.OFE.Dist.to_incExtN
    refine CMRA.comm.dist.trans (.trans ?_ CMRA.comm.dist)
    refine CMRA.op_ne.ne ?_
    exact (CMRA.unit_left_id_dist _)

@[rocq_alias view_local_update]
theorem view_local_update {a a' : A} {b0 b1 b0' b1' : B}
    (Hup : (b0, b1) ~l~> (b0', b1'))
    (Hrel : ∀ n, R n a b0 → R n a' b0') :
    ((●V a : View R) • ◯V b0, (●V a) • ◯V b1) ~l~> ((●V a') • ◯V b0', (●V a') • ◯V b1') := by
  rw [local_update_unital]
  rintro n ⟨(_ | ⟨dq, ag'⟩), bf⟩ Hv Heq <;> rw [auth_one_op_frag_validN_iff] at Hv
  · refine ⟨auth_one_op_frag_validN_iff.mpr (Hrel n Hv), ⟨.rfl, ?_⟩⟩
    refine .trans ?_ (unit_left_id_dist b1').symm.op_l
    refine unit_left_id_dist b0' |>.trans ?_
    refine (local_update_unital.mp Hup _ _ (IsViewRel.rel_validN _ _ _ Hv) ?_).2
    exact (unit_left_id_dist b0).symm.trans Heq.2 |>.trans (unit_left_id_dist b1).op_l
  · refine absurd (DFrac.valid_own_op (validN_ne Heq ?_).1)
      (by have : (1 : Qp).val = 1 := rfl; grind)
    exact auth_one_op_frag_validN_iff.mpr Hv

end Updates

section ViewMap

@[rocq_alias view_map]
def map {R : ViewRel A B} (R' : ViewRel A' B') (f : A → A')
    (g : B → B') (v : View R) : View R' where
  auth := match v.auth with | none => none | some (fr, a) => (fr, a.map' f)
  frag := g v.frag

@[rocq_alias view_map_id]
theorem map_id {R : ViewRel A B} (v : View R) : View.map R id id v = v := by
  rcases v with ⟨a, b⟩
  cases a <;> simp [View.map, Agree.map'_id]

@[rocq_alias view_map_compose]
theorem map_compose {R : ViewRel A B} {R' : ViewRel A' B'} {R'' : ViewRel A'' B''}
    f g (f' : A' → A'') (g' : B' → B'') (v : View R) :
    View.map R'' (f' ∘ f) (g' ∘ g) v = View.map R'' f' g' (View.map R' f g v) := by
  rcases v with ⟨a, b⟩
  cases a <;> simp [View.map, Agree.map'_compose]

section mapO

variable [OFE A] [OFE B] [OFE A'] [OFE B'] {R : ViewRel A B} {R' : ViewRel A' B'}

theorem map_compose' [OFE A''] [OFE B''] {R'' : ViewRel A'' B''}
    f g (f' : A' -n> A'') (g' : B' -n> B'') (v : View R) :
    View.map R'' (f'.comp f) (g'.comp g) v = View.map R'' f' g' (View.map R' f g v) :=
    map_compose f.f g.f f'.f g'.f v

#rocq_ignore view_map_ext "OFE is Leibniz; use equality"

omit [OFE B] in
theorem map_ne {f1 f2 : A → A'} {g1 g2 : B → B'} [OFE.NonExpansive f1] [OFE.NonExpansive f2]
    (v : View R) (h1 : ∀ a, f1 a ≡{n}≡ f2 a) (h2 : ∀ b, g1 b ≡{n}≡ g2 b) :
    View.map R' f1 g1 v ≡{n}≡ View.map R' f2 g2 v := by
  refine ⟨?_, h2 _⟩
  simp only [View.map]
  split
  · rfl
  · exact ⟨rfl, Agree.map_ne h1⟩

@[rocq_alias view_map_ne]
instance (f : A → A') (g : B → B') [OFE.NonExpansive f] [hne : OFE.NonExpansive g] :
    OFE.NonExpansive (View.map R' f g : (View R → _)) where
  ne := by
    rintro n _ _ ⟨h1, h2⟩
    refine ⟨?_, hne.ne h2⟩
    simp only [map]
    split <;> split <;> simp_all
    exact ⟨h1.1, Agree.map f |>.ne.ne h1.2⟩

@[rocq_alias viewO_map]
def mapO (f : A -n> A') (g : B -n> B') : View R -n> View R' where
  f := View.map R' f g
  ne := inferInstance

@[rocq_alias viewO_map_ne]
instance mapO_ne : OFE.NonExpansive₂ (mapO (R := R) (R' := R')) where
  ne _ _ _ hf _ _ hg v := map_ne v (hf ·) (hg ·)

end mapO

/-- The action of `View.map` on the authority part, as a morphism. -/
def mapAuthC [OFE A] [OFE A'] (f : A -n> A') :
    Option ((DFrac) × Agree A) -C> Option ((DFrac) × Agree A') :=
  Option.mapC (Prod.mapC CMRA.Hom.id (Agree.map f.f))

theorem map_auth_eq [OFE A] [OFE B] [OFE A'] {R : ViewRel A B} {R' : ViewRel A' B'}
    (f : A -n> A') (g : B → B') (v : View R) :
    (map R' f.f g v).auth = (mapAuthC f).f v.auth := by
  rcases v with ⟨_|⟨fr, a⟩, b⟩ <;> rfl

@[rocq_alias view_map_cmra_morphism]
def mapC [OFE A] [UCMRA B] [OFE A'] [UCMRA B']
    {R : ViewRel A B} [IsViewRel R] {R' : ViewRel A' B'} [IsViewRel R']
    (f : A -n> A') (g : B -C> B') (H : ∀ n a b, R n a b → R' n (f a) (g b)) :
    View R -C> View R' where
  f := View.map R' f g
  ne := inferInstance
  validN {n x} hval := by
    simp [CMRA.ValidN, map] at *
    rcases x with ⟨_ | ⟨fr,a⟩, b⟩ <;> simp_all
    · obtain ⟨a, hr⟩ := hval
      exists f a
      exact (H n a b hr)
    · rcases hval with ⟨hfr, a1, ha, hr⟩
      exact ⟨f a1, ⟨OFE.NonExpansive.ne ha, H n a1 b hr⟩⟩
  pcore x := by
    simp [CMRA.pcore, map, CMRA.core, Option.getD]
    refine ⟨?_, ?_⟩
    · rcases x.auth with _|⟨fr, a⟩ <;> simp [Prod.pcore]
      rcases (CMRA.pcore fr) <;> simp
      rcases h : (CMRA.pcore a) <;> cases h <;> simp [CMRA.pcore]
    · have _ := CMRA.Hom.pcore g x.frag
      rcases _ : (CMRA.pcore x.frag) <;>
      rcases _ : (CMRA.pcore (g.f x.frag)) <;> simp_all
  op x y := by
    rcases x with ⟨xa, xf⟩; rcases y with ⟨ya, yf⟩
    simp only [CMRA.op, map]
    simp only [Op, View.mk.injEq]
    refine ⟨?_, ?_⟩
    · cases xa <;> cases ya <;> simp [CMRA.op, optionOp, Prod.op]
      exact (Agree.map f.f).op _ _
    · exact CMRA.Hom.op g xf yf
  monoN {n x y} h := by
    refine ⟨?_, g.monoN h.2⟩
    rw [map_auth_eq, map_auth_eq]
    exact (mapAuthC f).monoN h.1
  mono {x y} h := by
    refine ⟨?_, g.mono h.2⟩
    rw [map_auth_eq, map_auth_eq]
    exact (mapAuthC f).mono h.1
  increasing {v} h := by
    refine increasing_mk ?_ (g.increasing (increasing_frag h))
    rw [map_auth_eq]
    exact (mapAuthC f).increasing (increasing_auth h)

end ViewMap

end View

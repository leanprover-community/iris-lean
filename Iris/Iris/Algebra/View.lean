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

variable {SI : Type _} [instSI : Iris.SIdx SI]

open Iris

@[nolint unusedArguments]
abbrev ViewRel (SI A B : Type _) [SIdx SI] := SI → A → B → Prop

@[rocq_alias view_rel]
class IsViewRel [OFE SI A] [URA B] [UORA SI B] (R : ViewRel SI A B) where
  mono : R n1 a1 b1 → a1 ≡{n2}≡ a2 → b2 ≼ₒ{n2} b1 → n2 ≤ n1 → R n2 a2 b2
  op_left : R n a (b • c) → R n a b
  rel_validN n a b : R n a b → ✓{n} b
  rel_unit n : ∃ a, R n a UnitOp.unit

theorem IsViewRel.ofMonoOrd [OFE SI A] [URA B] [UORA SI B] [IncOrd SI B] {R : ViewRel SI A B}
    (mono : ∀ {n1 : SI} {a1 b1 n2 a2 b2}, R n1 a1 b1 → a1 ≡{n2}≡ a2 → b2 ≼ₒ{n2} b1 → n2 ≤ n1 → R n2 a2 b2)
    (rel_validN : ∀ (n : SI) a b, R n a b → ✓{n} b)
    (rel_unit : ∀ n, ∃ a, R n a UnitOp.unit) : IsViewRel R where
  mono := mono
  op_left h := mono h .rfl (IncOrd.incN_ordN (ORA.incN_op_left _ _ _)) SIdx.le_refl
  rel_validN := rel_validN
  rel_unit := rel_unit

theorem IsViewRel.mono_inc [OFE SI A] [URA B] [UORA SI B] {R : ViewRel SI A B} [IsViewRel R]
    (H : R n1 a1 b1) (Ha : a1 ≡{n2}≡ a2) (Hb : b2 ≼{n2} b1) (Hn : n2 ≤ n1) : R n2 a2 b2 :=
  let ⟨_, hd⟩ := Hb
  op_left (mono H Ha (ORA.ordN_of_dist hd.symm) Hn)

@[rocq_alias ViewRelDiscrete]
class IsViewRelDiscrete [OFE SI A] [URA B] [UORA SI B] (R : ViewRel SI A B) extends IsViewRel R where
  discrete n a b : R 0 a b → R n a b

namespace ViewRel
open IsViewRel DFrac

variable [OFE SI A] [URA B] [UORA SI B] {R : ViewRel SI A B} [IsViewRel R]

@[rocq_alias view_rel_ne]
theorem iff_of_dist (Ha : a1 ≡{n}≡ a2) (Hb : b1 ≡{n}≡ b2) : R n a1 b1 ↔ R n a2 b2 :=
  ⟨(mono_inc · Ha Hb.symm.to_incN SIdx.le_refl), (mono_inc · Ha.symm Hb.to_incN SIdx.le_refl)⟩

#rocq_ignore view_rel_proper "OFE is Leibniz; use equality"

end ViewRel

@[rocq_alias view]
structure View {A B : Type _} (R : ViewRel SI A B) where
  auth : Option ((DFrac) × Agree A)
  frag : B

@[rocq_alias view_auth]
abbrev View.Auth [URA B] {R : ViewRel SI A B} (dq : DFrac) (a : A) : View R :=
  ⟨some (dq, toAgree a), UnitOp.unit⟩

@[rocq_alias view_frag]
abbrev View.Frag {R : ViewRel SI A B} (b : B) : View R := ⟨none, b⟩

notation "●V{" dq "} " a => View.Auth dq a
notation "●V " a => View.Auth (DFrac.own 1) a
notation "◯V " b => View.Frag b

namespace View
section OFE
open OFE UORA
variable [OFE SI A] [OFE SI B] {R : ViewRel SI A B}

#rocq_ignore view_equiv "OFE is Leibniz; use equality"

@[rocq_alias view_dist]
def dist (n : SI) (x y : View R) : Prop := x.auth ≡{n}≡ y.auth ∧ x.frag ≡{n}≡ y.frag

@[rocq_alias view_ofe_mixin]
instance instOFE : OFE SI (View R) where
  dist := dist
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
instance mk.ne : NonExpansive₂ SI (mk : _ → _ → View R) := ⟨fun _ _ _ Ha _ _ Hb => ⟨Ha, Hb⟩⟩
#rocq_ignore View_proper "Derived from View.mk.ne"

@[rocq_alias view_auth_proj_ne]
instance auth.ne : NonExpansive SI (auth : View R → _) := ⟨fun _ _ _ H => H.1⟩
#rocq_ignore view_auth_proj_proper "Derived from View.auth.ne"

@[rocq_alias view_frag_proj_ne]
instance frag.ne : NonExpansive SI (frag : View R → _) := ⟨fun _ _ _ H => H.2⟩
#rocq_ignore view_frag_proj_proper "Derived from View.frag.ne"

@[rocq_alias View_discrete]
theorem discrete {ag : Option ((DFrac) × Agree A)} (Ha : DiscreteE SI ag) (Hb : DiscreteE SI b) :
  DiscreteE SI (α := View R) (mk ag b) := ⟨fun H => by rw [Ha.discrete H.1, Hb.discrete H.2]⟩

@[rocq_alias view_ofe_discrete]
instance [Discrete SI A] [Discrete SI B] : Discrete SI (View R) where
  discrete_0 {x y} H := by
    obtain ⟨xa, xf⟩ := x; obtain ⟨ya, yf⟩ := y
    simp only [mk.injEq]
    exact ⟨discrete_0 H.1, discrete_0 H.2⟩

-- view_auth_dist_inj
theorem auth_inj_frac [URA B] {q1 q2 : DFrac} {a1 a2 : A} {n : SI} (H : (●V{q1} a1 : View R) ≡{n}≡ ●V{q2} a2) :
    q1 = q2 := H.1.1

-- view_auth_dist_inj
theorem dist_of_auth_dist [URA B] {q1 q2 : DFrac} {a1 a2 : A} {n : SI} (H : (●V{q1} a1 : View R) ≡{n}≡ ●V{q2} a2) :
    a1 ≡{n}≡ a2 := toAgree.inj H.1.2

@[rocq_alias view_auth_dist_inj]
theorem auth_dist_inj [URA B] {q1 q2 : DFrac} {a1 a2 : A} {n : SI}
    (H : (●V{q1} a1 : View R) ≡{n}≡ ●V{q2} a2) : q1 = q2 ∧ a1 ≡{n}≡ a2 :=
  ⟨auth_inj_frac H, dist_of_auth_dist H⟩

@[rocq_alias view_auth_inj]
theorem auth_eqv_inj [URA B] [UORA SI B] {q1 q2 : DFrac} {a1 a2 : A}
    (H : (●V{q1} a1 : View R) = ●V{q2} a2) : q1 = q2 ∧ a1 = a2 := by
  refine ⟨(auth_dist_inj (n := 0) H.dist).1, OFE.eq_dist_2 (SI := SI) fun n => ?_⟩
  exact (auth_dist_inj H.dist).2

@[rocq_alias view_frag_inj]
theorem frag_eqv_inj {b1 b2 : B}
    (H : (◯V b1 : View R) = ◯V b2) : b1 = b2 := OFE.eq_dist_2 fun _ => H.dist (SI := SI).2

@[rocq_alias view_frag_dist_inj]
theorem dist_of_frag_dist {b1 b2 : B} {n : SI} (H : (◯V b1 : View R) ≡{n}≡ ◯V b2) :
    b1 ≡{n}≡ b2 := H.2

@[rocq_alias view_auth_discrete]
instance auth_discrete [URA B] {dq a} [Ha : DiscreteE SI a] [He : DiscreteE SI (unit : B)] :
    DiscreteE SI (●V{dq} a : View R) := by
  refine discrete ?_ He
  infer_instance

@[rocq_alias view_frag_discrete]
instance frag_discrete [Hb : DiscreteE SI b] : DiscreteE SI (◯V b : View R) :=
  discrete Option.none_is_discrete Hb

end OFE

section Data
open ORA
variable {R : ViewRel SI A B}

@[simp]
def Pcore [PCore B] (v : View R) : Option (View R) :=
  some <| mk (core v.auth) (core v.frag)

@[simp]
def Op [_root_.Iris.Op B] (v1 v2 : View R) : View R :=
  mk (v1.auth • v2.auth) (v1.frag • v2.frag)

private theorem core_idem_of_pcore {α : Type _} [PCore α] (x : α) : core (core x) = core x := by
  unfold core; rcases h : PCore.pcore x with _ | c
  · simp [h]
  · simp [PCore.pcore_idem h]

@[reducible] instance raOp [_root_.Iris.Op B] : _root_.Iris.Op (View R) where
  op := Op
  assoc := by simp only [Op, View.mk.injEq]; exact ⟨assoc', assoc'⟩
  comm := by simp only [Op, View.mk.injEq]; exact ⟨comm', comm'⟩

@[reducible] instance raPCore [PCore B] : PCore (View R) where
  pcore := Pcore
  pcore_idem {_ cx} := by
    simp only [Pcore, Option.some.injEq]
    rcases cx
    simp only [mk.injEq, and_imp]
    rintro rfl rfl
    exact ⟨core_idem_of_pcore _, core_idem_of_pcore _⟩

instance raRA [URA B] : RA (View R) where
  pcore_op_left {x _} := by
    simp only [PCore.pcore, Pcore, Option.some.injEq]
    rintro rfl
    rcases x with ⟨xa, xf⟩
    simp only [_root_.Iris.Op.op, Op, View.mk.injEq]
    exact ⟨core_op xa, core_op xf⟩

instance raURA [URA B] : URA (View R) where
  unit := ⟨unit, unit⟩
  unit_left_id := by
    rintro ⟨xa, xf⟩
    change (⟨unit • xa, unit • xf⟩ : View R) = ⟨xa, xf⟩
    rw [ucmra_unit_left_id, ucmra_unit_left_id]
  pcore_unit := congrArg some (congrArg (View.mk _) (core_eqv_self unit))
  total _ := ⟨_, rfl⟩

end Data

section ORA
open IsViewRel toAgree OFE DFrac ORA

variable [OFE SI A] [URA B] [UORA SI B] {R : ViewRel SI A B} [IsViewRel R]

theorem IsViewRel.of_agree_dist_iff (Hb : b' ≡{n}≡ b) :
    (∃ a', toAgree a ≡{n}≡ toAgree a' ∧ R n a' b') ↔ R n a b := by
  refine ⟨fun H => ?_, fun H => ?_⟩
  · rcases H with ⟨_, HA, HR⟩
    exact mono_inc HR (inj HA.symm) Hb.symm.to_incN SIdx.le_refl
  · exact ⟨a, .rfl, mono_inc H .rfl Hb.to_incN SIdx.le_refl⟩

@[rocq_alias view_auth_ne]
instance auth_ne {dq : DFrac} : NonExpansive SI (Auth dq : A → View R) where
  ne _ _ _ H := by
    refine mk.ne.ne ?_ .rfl
    refine some_dist_some.mpr ⟨.rfl, ?_⟩
    simp only
    exact OFE.NonExpansive.ne H

#rocq_ignore view_auth_proper "Derivable from auth_ne with NonExpansive.eqv"

instance auth_ne₂ : NonExpansive₂ SI (Auth : DFrac → A → View R) where
  ne _ _ _ Hq _ _ Hf := by
    unfold Auth
    refine (NonExpansive₂.ne ?_ .rfl)
    refine NonExpansive.ne ?_
    exact dist_prod_ext Hq (NonExpansive.ne Hf)

@[rocq_alias view_frag_ne]
instance frag_ne : NonExpansive SI (Frag : B → View R) where
  ne _ _ _ H := mk.ne.ne .rfl H

#rocq_ignore view_frag_proper "Derivable from frag_ne with NonExpansive.eqv"

@[simp]
def Valid (v : View R) : Prop :=
  match v.auth with
  | some (dq, ag) => ✓[SI] dq ∧ (∀ (n : SI), ∃ a, ag ≡{n}≡ toAgree a ∧ R n a (frag v))
  | none => ∀ n, ∃ a, R n a (frag v)

@[simp]
def ValidN (n : SI) (v : View R) : Prop :=
  match v.auth with
  | some (dq, ag) => ✓{n} dq ∧ (∃ a, ag ≡{n}≡ toAgree a ∧ R n a (frag v))
  | none => ∃ a, R n a (frag v)

theorem ValidN.pair {n : SI} {x : View R} (Hv : ValidN n x) :
    ✓{n} ((x.auth, x.frag) : Option ((DFrac) × Agree A) × B) := by
  rcases x with ⟨_|⟨q, ag⟩, b⟩
  · obtain ⟨a, Ha⟩ := Hv
    exact ⟨trivial, IsViewRel.rel_validN _ _ _ Ha⟩
  · obtain ⟨Hq, a, Ha1, Ha2⟩ := Hv
    exact ⟨⟨Hq, Agree.validN_ne Ha1.symm trivial⟩, IsViewRel.rel_validN _ _ _ Ha2⟩

@[reducible] def raValid : _root_.Iris.Valid SI (View R) where
  ValidN := ValidN
  Valid := Valid
  valid_iff_validN {x} := by
    simp only [Valid, ValidN]; split
    · exact ⟨fun H n => ⟨H.1, H.2 n⟩, fun H => ⟨(H 0).1, fun n => (H n).2⟩⟩
    · exact Eq.to_iff rfl

@[reducible] def raOrdered : Ordered SI (View R) where
  OrderN n x y := x.auth ≼ₒ{n} y.auth ∧ x.frag ≼ₒ{n} y.frag
  Order x y := x.auth ≼ₒ[SI] y.auth ∧ x.frag ≼ₒ[SI] y.frag
  ordN_trans h1 h2 := ⟨ordN_trans h1.1 h2.1, ordN_trans h1.2 h2.2⟩
  ord_trans h1 h2 := ⟨ord_trans h1.1 h2.1, ord_trans h1.2 h2.2⟩
  ordN_of_ord n h := ⟨ordN_of_ord n h.1, ordN_of_ord n h.2⟩

omit [IsViewRel R] in
attribute [local instance] raOrdered in
theorem raOrderedNE : OrderedNE SI (View R) where
  ordN_ne ex ey h := ⟨ordN_ne ex.1 ey.1 h.1, ordN_ne ex.2 ey.2 h.2⟩
  ordN_le h le := ⟨ordN_le h.1 le, ordN_le h.2 le⟩

section
attribute [local instance] View.raOrdered raOp raPCore raValid raOrderedNE

omit [IsViewRel R] in
theorem increasing_auth {v : View R} (h : Increasing SI v) : Increasing SI v.auth where
  increasing w := (h.increasing ⟨w, unit⟩).1

omit [IsViewRel R] in
theorem increasing_frag {v : View R} (h : Increasing SI v) : Increasing SI v.frag where
  increasing w := (h.increasing ⟨none, w⟩).2

omit [IsViewRel R] in
theorem increasing_mk {v : View R} (ha : Increasing SI v.auth) (hb : Increasing SI v.frag) :
    Increasing SI v where
  increasing w := ⟨ha.increasing w.auth, hb.increasing w.frag⟩

@[rocq_alias view_cmra_mixin]
instance instORA : ORA SI (View R) where
  toValid := raValid
  op_ne.ne n x1 x2 H := by
    refine mk.ne.ne ?_ ?_
    · exact cmraOption.op_ne.ne <| NonExpansive.ne H
    · exact op_ne.ne  <| NonExpansive.ne H
  pcore_ne {n : SI} {x y cx} H := by
    simp only [PCore.pcore, Pcore, Option.some.injEq]
    rintro ⟨rfl⟩
    exists ⟨core y.auth, core y.frag⟩
    exact ⟨rfl, OFE.Dist.core H.1, OFE.Dist.core H.2⟩
  validN_ne {n : SI} {x1 x2} := by
    rintro ⟨Hl, Hr⟩
    rcases x1 with ⟨_|⟨q1, ag1⟩, b1⟩ <;>
    rcases x2 with ⟨_|⟨q2, ag2⟩, b2⟩ <;>
    simp_all [Valid.ValidN]
    · exact fun x H => ⟨x, mono_inc H .rfl Hr.symm.to_incN SIdx.le_refl⟩
    intro Hq a Hag HR
    refine ⟨validN_ne Hl.1 Hq, ?_⟩
    refine ⟨a, ?_⟩
    refine ⟨Hl.2.symm.trans Hag, ?_⟩
    exact mono_inc HR .rfl Hr.symm.to_incN SIdx.le_refl
  validN_le {n n' : SI} {x} := by
    simp only [Valid.ValidN, ValidN]
    split
    · refine fun H hle => ⟨H.1, ?_⟩
      rcases H.2 with ⟨ag, Ha⟩; exists ag
      refine ⟨Dist.le Ha.1 hle, ?_⟩
      exact mono_inc Ha.2 .rfl (incN_refl x.frag) hle
    · exact fun ⟨z, HR⟩ hle => ⟨z, mono_inc HR .rfl (incN_refl _) hle⟩
  toOrderedNE := raOrderedNE
  validN_op_left {n : SI} {x y} := by
    rcases x with ⟨_|⟨q1, ag1⟩, b1⟩ <;>
    rcases y with ⟨_|⟨q2, ag2⟩, b2⟩ <;>
    simp [ORA.op, ORA.ValidN, View.Op, View.ValidN, optionOp]
    · exact fun a Hr => ⟨a, mono_inc Hr .rfl (incN_op_left n b1 b2) SIdx.le_refl⟩
    · exact fun _ a _ Hr => ⟨a, mono_inc Hr .rfl (incN_op_left n b1 b2) SIdx.le_refl⟩
    · exact fun Hq a H Hr => ⟨Hq, ⟨a, ⟨H, mono_inc Hr .rfl (incN_op_left n b1 b2) SIdx.le_refl⟩⟩⟩
    · refine fun Hq a H Hr => ⟨valid_op_left (SI := SI) (x := q1) (y := q2) Hq, ⟨a, ?_, ?_⟩⟩
      · refine .trans ?_ H
        refine .trans Agree.idemp.symm.dist ?_
        exact op_ne.ne <| Agree.op_invN (Agree.validN_ne H.symm trivial)
      · exact mono_inc Hr .rfl (incN_op_left n b1 b2) SIdx.le_refl
  extend {n : SI} {x y1 y2} Hv He := by
    rcases extend (y₁ := ((y1.auth, y1.frag) : _ × B)) (y₂ := (y2.auth, y2.frag)) Hv.pair He
      with ⟨z1, z2, Hze, Hz1, Hz2⟩
    refine ⟨⟨z1.1, z1.2⟩, ⟨z2.1, z2.2⟩, ?_, Hz1, Hz2⟩
    exact congrArg (fun p => (⟨p.1, p.2⟩ : View R)) Hze
  toOrdered := View.raOrdered
  op_monoN_left_ord z h := ⟨op_monoN_left_ord z.auth h.1, op_monoN_left_ord z.frag h.2⟩
  op_mono_left_ord z h := ⟨op_mono_left_ord z.auth h.1, op_mono_left_ord z.frag h.2⟩
  validN_of_ordN {n : SI} {x y} h v := by
    rcases x with ⟨_|⟨q1, ag1⟩, b1⟩ <;> rcases y with ⟨_|⟨q2, ag2⟩, b2⟩
    · obtain ⟨a, Ha⟩ := v
      exact ⟨a, mono Ha .rfl h.2 SIdx.le_refl⟩
    · obtain ⟨_, a, _, Ha⟩ := v
      exact ⟨a, mono Ha .rfl h.2 SIdx.le_refl⟩
    · exact h.1.elim
    · obtain ⟨Hq, a, Hag, Ha⟩ := v
      rcases h.1 with e | i
      · exact ⟨validN_ne e.1.symm Hq, a, e.2.trans Hag, mono Ha .rfl h.2 SIdx.le_refl⟩
      · refine ⟨validN_of_ordN i.1 Hq, a, ?_, mono Ha .rfl h.2 SIdx.le_refl⟩
        exact (Agree.valid_ordN (Agree.validN_ne Hag.symm trivial) i.2).trans Hag
  pcore_monoN_ord {_ x y _} h e := by
    obtain rfl := Option.some.inj e
    exact ⟨_, rfl, core_ordN_core h.1, core_ordN_core h.2⟩
  pcore_mono_ord {x y _} h e := by
    obtain rfl := Option.some.inj e
    exact ⟨_, rfl, core_mono_ord h.1, core_mono_ord h.2⟩
  pcore_order_op {x _} e y := by
    obtain rfl := Option.some.inj e
    exact ⟨_, rfl, core_op_mono_ord x.auth y.auth, core_op_mono_ord x.frag y.frag⟩
  pcore_increasing {x _} e := by
    obtain rfl := Option.some.inj e
    exact increasing_mk inferInstance inferInstance
  increasing_closed {n : SI} {x y} h h' :=
    increasing_mk
      (increasing_closed (increasing_auth h) (Or.imp (·.1) (·.1) h'))
      (increasing_closed (increasing_frag h) (Or.imp (·.2) (·.2) h'))
  ordN_extend {n : SI} {sn} {x y} hs v h := by
    obtain ⟨za, hza, ea⟩ := ordN_extend hs v.pair.1 h.1
    obtain ⟨zf, hzf, ef⟩ := ordN_extend hs v.pair.2 h.2
    exact ⟨⟨za, zf⟩, ⟨hza, hzf⟩, ea, ef⟩

end

@[rocq_alias viewUR]
instance instUCMRA : UORA SI (View R) where
  toORA := instORA
  unit_valid := by exact IsViewRel.rel_unit (R := R)
  ord_refl x := ⟨ord_refl x.auth, ord_refl x.frag⟩

instance instIncOrd [IncOrd SI B] : IncOrd SI (View R) := IncOrd.of_increasing fun v =>
    increasing_mk (IncOrd.increasing v.auth) (IncOrd.increasing v.frag)

instance instOrdInc [OrdInc SI B] : OrdInc SI (View R) where
  ord_inc {x y} h := by
    have : OrdInc SI (Option (DFrac × Agree A)) := inferInstance
    obtain ⟨za, ha⟩ := OrdInc.ord_inc h.1
    obtain ⟨zf, hf⟩ := OrdInc.ord_inc h.2
    obtain ⟨ya, yf⟩ := y
    subst ha hf
    exact ⟨⟨za, zf⟩, rfl⟩
  ordN_incN h :=
    have : OrdInc SI (Option (DFrac × Agree A)) := inferInstance
    let ⟨za, ha⟩ := OrdInc.ordN_incN h.1
    let ⟨zf, hf⟩ := OrdInc.ordN_incN h.2
    ⟨⟨za, zf⟩, ha, hf⟩

instance instIsInc [IsInc SI B] : IsInc SI (View R) := {}

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
instance [OFE.Discrete SI A] [ORA.Discrete SI B] [IsViewRelDiscrete R] : ORA.Discrete SI (View R) where
  discrete_ord h := ⟨discrete_ord h.1, discrete_ord h.2⟩
  discrete_valid {x} := by
    simp only [ORA.ValidN, ValidN, ORA.Valid, Valid]
    split
    · rintro ⟨H1, ⟨a, H2, H3⟩⟩
      refine ⟨H1, fun n => ⟨a, ⟨?_, ?_⟩⟩⟩
      · exact (OFE.Discrete.discrete_0 H2).dist
      · exact IsViewRelDiscrete.discrete _ _ _ H3
    · exact fun ⟨a, H⟩ _ => ⟨a, IsViewRelDiscrete.discrete _ _ _ H⟩

#rocq_ignore view_empty_instance "Inlined in the UCMRA instance"
#rocq_ignore view_ucmra_mixin "Not needed"

omit [OFE SI A] [IsViewRel R] [UORA SI B] in
@[rocq_alias view_auth_dfrac_op]
theorem auth_op_auth_eqv : (●V{dq1 • dq2} a : View R) = ((●V{dq1} a) • ●V{dq2} a : View R) :=
  by simp only [View.Auth, Op, ORA.op, optionOp, Prod.op, View.mk.injEq, ucmra_unit_left_id]
     exact ⟨congrArg some (congrArg (Prod.mk _) Agree.idemp.symm), trivial⟩

set_option synthInstance.checkSynthOrder false in
@[rocq_alias view_auth_dfrac_is_op]
instance isOp_view_auth_dfrac {dq dq1 dq2 : DFrac} {a : A}
    [h : IsOp d dq dq1 dq2] :
    IsOp d (●V{dq} a : View R) (●V{dq1} a) (●V{dq2} a) where
  is_op := by
    rw [h.is_op]
    apply auth_op_auth_eqv

omit [OFE SI A] [IsViewRel R] [UORA SI B] in
@[rocq_alias view_frag_op]
theorem frag_op_eq : (◯V (b1 • b2) : View R) = ((◯V b1) • ◯V b2 : View R) := rfl

theorem frag_ord_of_ord (H : b1 ≼ₒ[SI] b2) : (◯V b1 : View R) ≼ₒ[SI] ◯V b2 := ⟨trivial, H⟩

omit [OFE SI A] [IsViewRel R] [UORA SI B] in
@[rocq_alias view_frag_mono]
theorem frag_inc_of_inc (H : b1 ≼ b2) : (◯V b1 : View R) ≼ ◯V b2 := by
  rcases H with ⟨c, H⟩
  rw [H, frag_op_eq]
  exact inc_op_left _ _

omit [OFE SI A] [IsViewRel R] [UORA SI B] in
@[rocq_alias view_frag_core]
theorem frag_core : ORA.core (◯V b : View R) = ◯V (ORA.core b) := rfl

omit [OFE SI A] [IsViewRel R] [UORA SI B] in
@[rocq_alias view_both_core_discarded]
theorem auth_discard_op_frag_core : ORA.core ((●V{.discard} a) • ◯V b : View R) = ((●V{.discard} a) • ◯V (ORA.core b) : View R) :=
  congrArg (View.mk _) ((congrArg ORA.core ucmra_unit_left_id).trans ucmra_unit_left_id.symm)

omit [OFE SI A] [IsViewRel R] [UORA SI B] in
@[rocq_alias view_both_core_frac]
theorem auth_own_op_frag_core : ORA.core ((●V{.own q} a) • ◯V b : View R) = (◯V (ORA.core b) : View R) :=
  congrArg (View.mk _) (congrArg ORA.core ucmra_unit_left_id)

@[rocq_alias view_auth_core_id]
instance : CoreId (●V{.discard} a : View R) where
  core_id := congrArg some (congrArg (View.mk _) (core_eqv_self unit))

@[rocq_alias view_frag_core_id]
instance [ORA.CoreId b] : CoreId (◯V b : View R) where
  core_id := congrArg some (congrArg (View.mk _) (coreId_iff_core_eqv_self.mp (by trivial)))

@[rocq_alias view_both_core_id]
instance [ORA.CoreId b] : CoreId ((●V{.discard} a : View R) • ◯V b) where
  core_id :=
    congrArg some (congrArg (View.mk _)
      (((congrArg ORA.core ucmra_unit_left_id).trans
        (coreId_iff_core_eqv_self.mp (by trivial))).trans ucmra_unit_left_id.symm))

@[rocq_alias view_frag_is_op]
instance {b b1 b2 : B} [h : IsOp d b b1 b2] :
    IsOp d (◯V b : View R) (◯V b1) (◯V b2) where
  is_op := by rw [h.is_op]; exact frag_op_eq

section BigOp
open Algebra Std

instance instMonoidOps : MonoidOps (ORA.op (α := View R)) unit := ucmraMonoidOps

@[rocq_alias view_frag_sep_homomorphism]
instance : MonoidHomomorphism ORA.op ORA.op unit unit (· = ·) (Frag : B → View R) where
  rel_refl := rfl
  rel_trans := Eq.trans
  op_proper h₁ h₂ := h₁ ▸ h₂ ▸ rfl
  map_op := frag_op_eq
  map_unit := rfl

omit [OFE SI A] [IsViewRel R] [UORA SI B] in
@[rocq_alias big_opL_view_frag]
theorem bigOpL_frag (g : Nat → C → B) (l : List C) :
    (◯V ([^ ORA.op list] k ↦ x ∈ l, g k x) : View R) = [^ ORA.op list] k ↦ x ∈ l, ◯V (g k x) :=
  BigOpL.bigOpL_hom _ _

omit [OFE SI A] [IsViewRel R] [UORA SI B] in
@[rocq_alias big_opM_view_frag]
theorem bigOpM_frag [LawfulFiniteMap M' K] (g : K → C → B) (m : M' C) :
    (◯V ([^ ORA.op map] k ↦ x ∈ m, g k x) : View R) = [^ ORA.op map] k ↦ x ∈ m, ◯V (g k x) :=
  BigOpM.bigOpM_hom _ _

omit [OFE SI A] [IsViewRel R] [UORA SI B] in
@[rocq_alias big_opS_view_frag]
theorem bigOpS_frag [LawfulFiniteSet S' C] (g : C → B) (X : S') :
    (◯V ([^ ORA.op set] x ∈ X, g x) : View R) = [^ ORA.op set] x ∈ X, ◯V (g x) :=
  BigOpS.hom inferInstance _ _

omit [OFE SI A] [IsViewRel R] [UORA SI B] in
@[rocq_alias big_opMS_view_frag]
theorem bigOpMS_frag [LawfulFiniteMultiSet MS' C] (g : C → B) (X : MS') :
    (◯V ([^ ORA.op mset] x ∈ X, g x) : View R) = [^ ORA.op mset] x ∈ X, ◯V (g x) :=
  BigOpMS.hom inferInstance _ _

end BigOp

@[rocq_alias view_auth_dfrac_op_invN]
theorem dist_of_validN_auth {n : SI} (H : ✓{n} ((●V{dq1} a1 : View R) • ●V{dq2} a2)) : a1 ≡{n}≡ a2 := by
  rcases H with ⟨_, _, H, _⟩
  refine toAgree.inj (Agree.op_invN ?_)
  exact Agree.validN_ne H.symm trivial

#rocq_ignore view_auth_dfrac_op_inv "Use eq_of_valid_auth"

@[rocq_alias view_auth_dfrac_op_inv_L]
theorem eq_of_valid_auth
    (H : ✓[SI] ((●V{dq1} a1 : View R) • ●V{dq2} a2)) : a1 = a2 :=
  OFE.eq_dist_2 fun _ => dist_of_validN_auth H.validN

@[rocq_alias view_auth_dfrac_validN]
theorem auth_validN_iff {n : SI} : ✓{n} (●V{dq} a : View R) ↔ ✓{n} dq ∧ R n a unit :=
  and_congr_right fun _ => IsViewRel.of_agree_dist_iff .rfl

@[rocq_alias view_auth_validN]
theorem auth_one_validN_iff (n : SI) a : ✓{n} (●V a : View R) ↔ R n a unit :=
  ⟨(auth_validN_iff.mp · |>.2), (auth_validN_iff.mpr ⟨valid_own_one (SI := SI), ·⟩)⟩

@[rocq_alias view_auth_dfrac_op_validN]
theorem auth_op_auth_validN_iff {n : SI} :
    ✓{n} ((●V{dq1} a1 : View R) • ●V{dq2} a2) ↔ ✓[SI] (dq1 • dq2) ∧ a1 ≡{n}≡ a2 ∧ R n a1 unit := by
  refine ⟨fun H => ?_, fun H => ?_⟩
  · let Ha' : a1 ≡{n}≡ a2 := dist_of_validN_auth H
    rcases H with ⟨Hq, _, Ha, HR⟩
    refine ⟨Hq, Ha', mono_inc HR ?_ incN_unit SIdx.le_refl⟩
    refine .trans ?_ Ha'.symm
    refine toAgree.inj (Ha.symm.trans ?_)
    apply op_commN.trans
    apply (op_ne.ne (toAgree.ne.ne Ha')).trans
    exact Agree.idemp.dist
  · simp [ORA.op, ORA.ValidN, ValidN, optionOp, Prod.op]
    refine ⟨H.1, a1, ?_, ?_⟩
    · exact (op_ne.ne <| toAgree.ne.ne H.2.1.symm).trans Agree.idemp.dist
    · refine mono_inc H.2.2 .rfl ?_ SIdx.le_refl
      exact OFE.Dist.to_incN <| unit_left_id_dist unit

@[rocq_alias view_auth_op_validN]
theorem auth_one_op_auth_one_validN_iff {n : SI} : ✓{n} ((●V a1 : View R) • ●V a2) ↔ False := by
  refine auth_op_auth_validN_iff.trans ?_
  simp only [iff_false, not_and]
  intro h
  simp only [ORA.Valid, ORA.op, DFrac.op, valid] at h
  grind

@[rocq_alias view_frag_validN]
theorem frag_validN_iff {n : SI} : ✓{n} (◯V b : View R) ↔ ∃ a, R n a b := by rfl

@[rocq_alias view_both_dfrac_validN]
theorem auth_op_frag_validN_iff {n : SI} : ✓{n} ((●V{dq} a : View R) • ◯V b) ↔ ✓[SI] dq ∧ R n a b :=
  and_congr_right (fun _ => IsViewRel.of_agree_dist_iff <| unit_left_id_dist b)

@[rocq_alias view_both_validN]
theorem auth_one_op_frag_validN_iff {n : SI} : ✓{n} ((●V a : View R) • ◯V b) ↔ R n a b :=
  auth_op_frag_validN_iff.trans <| and_iff_right_iff_imp.mpr (fun _ => valid_own_one)

@[rocq_alias view_auth_dfrac_valid]
theorem auth_valid_iff : ✓[SI] (●V{dq} a : View R) ↔ ✓[SI] dq ∧ ∀ n, R n a unit :=
  and_congr_right (fun _=> forall_congr' fun _ => IsViewRel.of_agree_dist_iff .rfl)

@[rocq_alias view_auth_valid]
theorem auth_one_valid_iff : ✓[SI] (●V a : View R) ↔ ∀ n, R n a unit :=
  auth_valid_iff.trans <| and_iff_right_iff_imp.mpr (fun _ => valid_own_one)

@[rocq_alias view_auth_dfrac_op_valid]
theorem auth_op_auth_valid_iff : ✓[SI] ((●V{dq1} a1 : View R) • ●V{dq2} a2) ↔ ✓[SI] (dq1 • dq2) ∧ a1 = a2 ∧ ∀ n, R n a1 unit := by
  refine valid_iff_validN.trans ?_
  refine ⟨fun H => ?_, fun H n => ?_⟩
  · simp [valid, ORA.op, DFrac.op, optionOp, ORA.ValidN, ValidN] at H
    let Hn n := dist_of_validN_auth <| H n
    refine ⟨(H 0).1, OFE.eq_dist_2 Hn, fun n => ?_⟩
    · rcases (H n) with ⟨_, _, Hl, H⟩
      apply mono_inc H ?_ incN_unit SIdx.le_refl
      apply toAgree.inj (Hl.symm.trans ?_)
      exact (op_ne.ne <| toAgree.ne.ne (Hn _).symm).trans Agree.idemp.dist
  · exact auth_op_auth_validN_iff.mpr ⟨H.1, H.2.1.dist, H.2.2 n⟩

@[rocq_alias view_auth_op_valid]
theorem auth_one_op_auth_one_valid_iff : ✓[SI] ((●V a1 : View R) • ●V a2) ↔ False := by
  refine auth_op_auth_valid_iff.trans ?_
  simp [ORA.op, DFrac.op, ORA.Valid, valid]
  grind

@[rocq_alias view_frag_valid]
theorem frag_valid_iff : ✓[SI] (◯V b : View R) ↔ ∀ n, ∃ a, R n a b := by rfl

@[rocq_alias view_both_dfrac_valid]
theorem auth_op_frag_valid_iff : ✓[SI] ((●V{dq} a : View R) • ◯V b) ↔ ✓[SI] dq ∧ ∀ n, R n a b :=
  and_congr_right (fun _ => forall_congr' fun _ => IsViewRel.of_agree_dist_iff <| unit_left_id_dist b)

@[rocq_alias view_both_valid]
theorem auth_one_op_frag_valid_iff : ✓[SI] ((●V a : View R) • ◯V b) ↔ ∀ n, R n a b :=
  auth_op_frag_valid_iff.trans <| and_iff_right_iff_imp.mpr (fun _ => valid_own_one)

open ORA in
@[rocq_alias view_auth_dfrac_includedN]
theorem auth_incN_auth_op_frag_iff {n : SI} :
    (●V{dq1} a1 : View R) ≼{n} ((●V{dq2} a2) • ◯V b) ↔
      (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡{n}≡ a2 := by
  refine ⟨?_, fun H => ?_⟩
  · simp only [Auth, Frag, IncludedN, ORA.op]
    rintro ⟨(_|⟨dqf, af⟩),⟨⟨x1, x2⟩, y⟩⟩
    · exact ⟨.inr x1.symm, toAgree.inj x2.symm⟩
    · exact ⟨.inl ⟨dqf, x1⟩, Agree.toAgree_includedN.mp ⟨af, x2⟩⟩
  · rcases H with ⟨(⟨z, HRz⟩| HRa2), HRb⟩
    · calc (●V{dq1} a1 : View R)
             ≼{n} ((●V{dq1} a1) • ((◯V b) • ●V{z} a1)) := by exists ((◯V b) • ●V{z} a1)
           _ ≡{n}≡ ((◯V b) • ●V{z} a1) • ●V{dq1} a1 := op_commN
           _ ≡{n}≡ (◯V b) • ((●V{z} a1) • ●V{dq1} a1) := op_assocN.symm
           _ ≡{n}≡ (◯V b) • ((●V{dq1} a1) • ●V{z} a1) := op_ne.ne op_commN
           _ ≡{n}≡ (◯V b) • ●V{dq1 • z} a1 := op_ne.ne auth_op_auth_eqv.symm.dist
           _ ≡{n}≡ (◯V b) • ●V{dq2} a2 := op_ne.ne (NonExpansive₂.ne HRz.symm.dist HRb)
           _ ≡{n}≡ ((●V{dq2} a2) • ◯V b) := op_commN
    · exists (◯V b)
      refine comm'.dist.trans ?_
      refine (.trans ?_ comm'.dist)
      apply op_ne.ne
      exact HRa2 ▸NonExpansive₂.ne rfl HRb.symm

open ORA in
@[rocq_alias view_auth_dfrac_included]
theorem auth_inc_auth_op_frag_iff :
    ((●V{dq1} a1 : View R) ≼ (●V{dq2} a2 : View R) • ◯V b) ↔
      (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 = a2 := by
  refine ⟨fun H => ⟨?_, ?_⟩, fun H => ?_⟩
  · exact auth_incN_auth_op_frag_iff (n := (0 : SI)) |>.mp (incN_of_inc _ H) |>.1
  · refine OFE.eq_dist_2 (SI := SI) (fun n => ?_)
    exact auth_incN_auth_op_frag_iff |>.mp (incN_of_inc _ H) |>.2
  · rcases H with ⟨(⟨q, Hq⟩|Hq), Ha⟩
    · calc (●V{dq1} a1 : View R)
           _ ≼ (●V{dq1} a1) • ((●V{q} a1) • ◯V b) := by exists ((●V{q} a1) • ◯V b)
           _ ≼ ((●V{dq1} a1) • ●V{q} a1) • ◯V b := by rw [assoc']
           _ ≼ (◯V b) • ((●V{dq1} a1) • ●V{q} a1) := by rw [comm']
           _ ≼ (◯V b) • ●V{dq1 • q} a1 := by rw [View.auth_op_auth_eqv]
           _ ≼ (●V{dq2} a2) • ◯V b := by rw [Hq, Ha, comm', View.auth_op_auth_eqv]
    · exists (◯V b)
      rw [Hq, Ha]

@[rocq_alias view_auth_includedN]
theorem auth_one_incN_auth_one_op_frag_iff {n : SI} :
    (●V a1 : View R) ≼{n} ((●V a2) • ◯V b) ↔ a1 ≡{n}≡ a2 :=
  auth_incN_auth_op_frag_iff.trans <| and_iff_right_iff_imp.mpr <| fun _ => .inr rfl

@[rocq_alias view_auth_included]
theorem auth_one_inc_auth_one_op_frag_iff :
    (●V a1 : View R) ≼ ((●V a2) • ◯V b) ↔ a1 = a2 :=
  auth_inc_auth_op_frag_iff.trans <| and_iff_right_iff_imp.mpr <| fun _ => .inr rfl

open ORA in
@[rocq_alias view_frag_includedN]
theorem frag_incN_auth_op_frag_iff {n : SI} :
    (◯V b1 : View R) ≼{n} ((●V{p} a) • ◯V b2) ↔ b1 ≼{n} b2 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨xf, ⟨_, Hb⟩⟩
    have Hb' : b2 ≡{n}≡ b1 • xf.frag := ucmra_unit_left_id.dist.symm.trans Hb
    refine (incN_iff_right <| Hb'.symm).mp ?_
    exists xf.frag
  · rintro ⟨bf, Hbf⟩
    calc (◯V b1 : View R)
         _ ≼{n} (◯V b1) • ((◯V bf) • ●V{p} a) := by exists ((◯V bf) • ●V{p} a)
         _ ≡{n}≡ ((◯V b1) • ◯V bf) • ●V{p} a := op_assocN
         _ ≡{n}≡ (●V{p} a) • ((◯V b1) • ◯V bf) := op_commN
         _ ≼{n} (●V{p} a) • ◯V b1 • bf := by rw [frag_op_eq]
         _ ≡{n}≡ (●V{p} a) • ◯V b2 := op_ne.ne (NonExpansive.ne Hbf.symm)

omit [OFE SI A] [IsViewRel R] in
open ORA in
omit [UORA SI B] in
@[rocq_alias view_frag_included]
theorem frag_inc_auth_op_frag_iff :
    (◯V b1 : View R) ≼ ((●V{p} a) • ◯V b2) ↔ b1 ≼ b2 := by
  constructor
  · rintro ⟨xf, HH⟩
    have Hb' : b2 = b1 • xf.frag := (unit_left_id).symm.trans (congrArg View.frag HH)
    rw [Hb']
    exists xf.frag
  · rintro ⟨bf, Hbf⟩
    calc (◯V b1 : View R)
         _ ≼ (◯V b1) • ((◯V bf) • ●V{p} a) := by exists ((◯V bf) • ●V{p} a)
         _ ≼ ((◯V b1) • ◯V bf) • ●V{p} a := by rw [assoc']
         _ ≼ (●V{p} a) • ((◯V b1) • ◯V bf) := by rw [comm']
         _ ≼ (●V{p} a) • ◯V b1 • bf := by rw [frag_op_eq]
         _ ≼ (●V{p} a) • ◯V b2 := by rw [Hbf]

open ORA in
@[rocq_alias view_both_dfrac_includedN]
theorem auth_op_frag_incN_auth_op_frag_iff {n : SI} :
    ((●V{dq1} a1 : View R) • ◯V b1) ≼{n} ((●V{dq2} a2) • ◯V b2) ↔
      (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡{n}≡ a2 ∧ b1 ≼{n} b2 := by
  refine ⟨fun H => ?_, fun ⟨H0, H1, ⟨bf, H2⟩⟩ => ?_⟩
  · rw [← and_assoc]
    refine ⟨?_, ?_⟩
    · apply (auth_incN_auth_op_frag_iff (R := R)).mp
      exact (incN_op_left _ _ _).trans H
    · apply (frag_incN_auth_op_frag_iff (R := R)).mp
      exact (incN_op_right _ _ _).trans H
  · calc ((●V{dq1} a1) • ◯V b1 : View R)
         _ ≼{n} ((●V{dq2} a2) • ◯V bf) • ◯V b1 :=
           op_monoN_left _ <| auth_incN_auth_op_frag_iff.mpr ⟨H0, H1⟩
         _ ≡{n}≡ (●V{dq2} a2) • ((◯V bf) • ◯V b1) := op_assocN.symm
         _ ≼{n} (●V{dq2} a2) • ◯V bf • b1 := by rw [frag_op_eq]
         _ ≡{n}≡ (●V{dq2} a2) • ◯V b2 := op_ne.ne (NonExpansive.ne (H2.trans comm'.dist |>.symm))

open ORA in
@[rocq_alias view_both_dfrac_included]
theorem auth_op_frag_inc_auth_op_frag_iff :
    ((●V{dq1} a1 : View R) • ◯V b1) ≼ ((●V{dq2} a2) • ◯V b2) ↔
      (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 = a2 ∧ b1 ≼ b2 := by
  refine ⟨fun H => ?_, fun ⟨H0, H1, ⟨bf, H2⟩⟩ => ?_⟩
  · rw [← and_assoc]
    refine ⟨?_, ?_⟩
    · apply (auth_inc_auth_op_frag_iff (R := R)).mp
      exact (inc_op_left (●V{dq1} a1 : View R) (◯V b1)).trans H
    · apply (frag_inc_auth_op_frag_iff (R := R)).mp
      exact (inc_op_right _ _).trans H
  · calc ((●V{dq1} a1) • ◯V b1 : View R)
         _ ≼ (((●V{dq2} a2) • ◯V bf) • ◯V b1 : View R) :=
           op_mono_left _ <| auth_inc_auth_op_frag_iff.mpr ⟨H0, H1⟩
         _ ≼ ((●V{dq2} a2) • ((◯V bf) • ◯V b1) : View R) := by rw [← assoc']
         _ ≼ ((●V{dq2} a2) • ◯V bf • b1 : View R) := inc_refl _
         _ ≼ ((●V{dq2} a2) • ◯V b2 : View R) := by rw [← H2.trans comm]

@[rocq_alias view_both_includedN]
theorem auth_one_op_frag_incN_auth_one_op_frag_iff {n : SI} :
    ((●V a1 : View R) • ◯V b1) ≼{n} ((●V a2) • ◯V b2) ↔ (a1 ≡{n}≡ a2 ∧ b1 ≼{n} b2) :=
  auth_op_frag_incN_auth_op_frag_iff.trans <| and_iff_right_iff_imp.mpr <| fun _ => .inr rfl

@[rocq_alias view_both_included]
theorem auth_one_op_frag_inc_auth_one_op_frag_iff :
    ((●V a1 : View R) • ◯V b1) ≼ ((●V a2) • ◯V b2) ↔ a1 = a2 ∧ b1 ≼ b2 :=
  auth_op_frag_inc_auth_op_frag_iff.trans <| and_iff_right_iff_imp.mpr <| fun _ => .inr rfl

open ORA in
theorem auth_ordN_auth_op_frag_iff {n : SI} [Increasing SI b] :
    (●V{dq1} a1 : View R) ≼ₒ{n} ((●V{dq2} a2) • ◯V b) ↔
      (dq1 ≼ₒ[SI] dq2 ∨ dq1 = dq2) ∧ a1 ≡{n}≡ a2 := by
  refine ⟨fun ⟨ha, _⟩ => ?_, fun ⟨hd, ha⟩ => ⟨?_, ordN_op_left _ _ b⟩⟩
  · rcases ha with ⟨e₁, e₂⟩ | ⟨o₁, o₂⟩
    · exact ⟨.inr (OFE.Discrete.discrete e₁), Agree.toAgree_injN e₂⟩
    · exact ⟨.inl ((ord_iff_ordN (α := DFrac) n).mpr o₁), Agree.toAgree_ordN.mp o₂⟩
  · rcases hd with o | rfl
    · exact .inr ⟨o.ordN, Agree.toAgree_ordN.mpr ha⟩
    · exact .inl ⟨.rfl, toAgree.ne.ne ha⟩

open ORA in
theorem auth_ord_auth_op_frag_iff [Increasing SI b] :
    (●V{dq1} a1 : View R) ≼ₒ[SI] ((●V{dq2} a2) • ◯V b) ↔
      (dq1 ≼ₒ[SI] dq2 ∨ dq1 = dq2) ∧ a1 = a2 := by
  refine ⟨fun ⟨ha, _⟩ => ?_, fun ⟨hd, ha⟩ => ⟨?_, ord_op_left _ b⟩⟩
  · rcases ha with e | ⟨o₁, o₂⟩
    · exact ⟨.inr (congrArg Prod.fst e), Agree.toAgree_inj (congrArg Prod.snd e)⟩
    · exact ⟨.inl o₁, Agree.toAgree_ord.mp o₂⟩
  · subst ha
    rcases hd with o | rfl
    · exact .inr ⟨o, Agree.toAgree_ord.mpr rfl⟩
    · exact .inl rfl

theorem auth_one_ordN_auth_one_op_frag_iff {n : SI} [Increasing SI b] :
    (●V a1 : View R) ≼ₒ{n} ((●V a2) • ◯V b) ↔ a1 ≡{n}≡ a2 :=
  auth_ordN_auth_op_frag_iff.trans <| and_iff_right_iff_imp.mpr <| fun _ => .inr rfl

theorem auth_one_ord_auth_one_op_frag_iff [Increasing SI b] :
    (●V a1 : View R) ≼ₒ[SI] ((●V a2) • ◯V b) ↔ a1 = a2 :=
  auth_ord_auth_op_frag_iff.trans <| and_iff_right_iff_imp.mpr <| fun _ => .inr rfl

open ORA in
theorem frag_ordN_auth_op_frag_iff {n : SI} :
    (◯V b1 : View R) ≼ₒ{n} ((●V{p} a) • ◯V b2) ↔ b1 ≼ₒ{n} b2 :=
  ⟨fun ⟨_, h⟩ => ordN_ne .rfl ucmra_unit_left_id.dist h,
   fun h => ⟨IncOrd.increasing _, ordN_ne .rfl ucmra_unit_left_id.dist.symm h⟩⟩

open ORA in
theorem frag_ord_auth_op_frag_iff :
    (◯V b1 : View R) ≼ₒ[SI] ((●V{p} a) • ◯V b2) ↔ b1 ≼ₒ[SI] b2 :=
  ⟨fun ⟨_, h⟩ => ucmra_unit_left_id (x := b2) ▸ h, fun h => ⟨IncOrd.increasing _, by
     change b1 ≼ₒ[SI] (unit • b2); rw [ucmra_unit_left_id]; exact h⟩⟩

open ORA in
theorem auth_op_frag_ordN_auth_op_frag_iff {n : SI} :
    ((●V{dq1} a1 : View R) • ◯V b1) ≼ₒ{n} ((●V{dq2} a2) • ◯V b2) ↔
      (dq1 ≼ₒ[SI] dq2 ∨ dq1 = dq2) ∧ a1 ≡{n}≡ a2 ∧ b1 ≼ₒ{n} b2 := by
  refine ⟨fun ⟨ha, hb⟩ => ?_, fun ⟨hd, ha, hb⟩ => ⟨?_, ?_⟩⟩
  · refine ⟨?_, ?_, ordN_ne ucmra_unit_left_id.dist ucmra_unit_left_id.dist hb⟩ <;>
      rcases ha with ⟨e₁, e₂⟩ | ⟨o₁, o₂⟩
    · exact .inr (OFE.Discrete.discrete e₁)
    · exact .inl ((ord_iff_ordN (α := DFrac) n).mpr o₁)
    · exact Agree.toAgree_injN e₂
    · exact Agree.toAgree_ordN.mp o₂
  · rcases hd with o | rfl
    · exact .inr ⟨o.ordN, Agree.toAgree_ordN.mpr ha⟩
    · exact .inl ⟨.rfl, toAgree.ne.ne ha⟩
  · exact ordN_ne ucmra_unit_left_id.dist.symm ucmra_unit_left_id.dist.symm hb

open ORA in
theorem auth_op_frag_ord_auth_op_frag_iff :
    ((●V{dq1} a1 : View R) • ◯V b1) ≼ₒ[SI] ((●V{dq2} a2) • ◯V b2) ↔
      (dq1 ≼ₒ[SI] dq2 ∨ dq1 = dq2) ∧ a1 = a2 ∧ b1 ≼ₒ[SI] b2 := by
  have hb : ((●V{dq1} a1 : View R) • ◯V b1).frag ≼ₒ[SI] ((●V{dq2} a2 : View R) • ◯V b2).frag ↔
      b1 ≼ₒ[SI] b2 := by
    change ((unit : B) • b1) ≼ₒ[SI] ((unit : B) • b2) ↔ _
    rw [ucmra_unit_left_id, ucmra_unit_left_id]
  refine ⟨fun ⟨ha, h⟩ => ?_, fun ⟨hd, ha, h⟩ => ⟨?_, hb.mpr h⟩⟩
  · refine ⟨?_, ?_, hb.mp h⟩ <;> rcases ha with e | ⟨o₁, o₂⟩
    · exact .inr (congrArg Prod.fst e)
    · exact .inl o₁
    · exact Agree.toAgree_inj (congrArg Prod.snd e)
    · exact Agree.toAgree_ord.mp o₂
  · subst ha
    rcases hd with o | rfl
    · exact .inr ⟨o, Agree.toAgree_ord.mpr rfl⟩
    · exact .inl rfl

theorem auth_one_op_frag_ord_auth_one_op_frag_iff :
    ((●V a1 : View R) • ◯V b1) ≼ₒ[SI] ((●V a2) • ◯V b2) ↔ a1 = a2 ∧ b1 ≼ₒ[SI] b2 :=
  auth_op_frag_ord_auth_op_frag_iff.trans <| and_iff_right_iff_imp.mpr <| fun _ => .inr rfl

theorem auth_one_op_frag_ordN_auth_one_op_frag_iff {n : SI} :
    ((●V a1 : View R) • ◯V b1) ≼ₒ{n} ((●V a2) • ◯V b2) ↔ (a1 ≡{n}≡ a2 ∧ b1 ≼ₒ{n} b2) :=
  auth_op_frag_ordN_auth_op_frag_iff.trans <| and_iff_right_iff_imp.mpr <| fun _ => .inr rfl

#rocq_ignore view_core_eq "Not needed"
#rocq_ignore view_valid_eq "Not needed"
#rocq_ignore view_validN_eq "Not needed"
#rocq_ignore view_pcore_eq "Not needed"
#rocq_ignore view_core_eq "Not needed"
#rocq_ignore view_op_eq "Not needed"

end ORA

section Updates

variable [OFE SI A] [URA B] [IB : UORA SI B] {R : ViewRel SI A B} [IsViewRel R]

open ORA DFrac

@[rocq_alias view_updateP]
theorem auth_one_op_frag_updateP {Pab : A → B → Prop}
    (Hup : ∀ n bf, R n a (b • bf) → ∃ a' b', Pab a' b' ∧ R n a' (b' • bf)) :
    ((●V a : View R) • ◯V b) ~~>:[SI] fun k => ∃ a' b', k = ((●V a' : View R) • ◯V b') ∧ Pab a' b' := by
  refine UpdateP.total.mpr (fun n ⟨ag, bf⟩ => ?_)
  rcases ag with (_|⟨dq, ag⟩)
  · intro H
    obtain ⟨_, a0, He', Hrel'⟩ := H
    have Hrel : R n a (b • bf) := by
      apply IsViewRel.mono_inc Hrel' (toAgree.inj He').symm _ SIdx.le_refl
      apply Iris.OFE.Dist.to_incN
      refine comm.dist.trans (.trans ?_ comm.dist)
      refine op_ne.ne ?_
      exact (unit_left_id_dist b).symm
    obtain ⟨a', b', Hab', Hrel''⟩ := Hup _ _ Hrel
    refine ⟨((●V a') • ◯V b'), ?_, ?_⟩
    · exists a'; exists b'
    · change Valid.ValidN _ _ ∧ _
      refine ⟨by trivial, a', .rfl, ?_⟩
      apply IsViewRel.mono_inc Hrel'' .rfl _ SIdx.le_refl
      apply Iris.OFE.Dist.to_incN
      refine comm.dist.trans (.trans ?_ comm.dist)
      refine op_ne.ne <| unit_left_id_dist b'
  · letI _ := own_whole_exclusive (SI := SI)
    exact (not_valid_exclN_op_left ·.1 |>.elim)

@[rocq_alias view_update]
theorem auth_one_op_frag_update (Hup : ∀ n bf, R n a (b • bf) → R n a' (b' • bf)) :
    ((●V a : View R) • ◯V b) ~~>[SI] (●V a') • ◯V b' := by
  apply Update.of_updateP
  apply UpdateP.weaken
  · apply auth_one_op_frag_updateP (Pab := fun a b => a = a' ∧ b = b')
    exact fun _ _ H => ⟨a', b', ⟨rfl, rfl⟩, Hup _ _ H⟩
  · rintro y ⟨a', b', H, rfl, rfl⟩
    exact H.symm

@[rocq_alias view_update_alloc]
theorem auth_one_alloc (Hup : ∀ n bf, R n a bf → R n a' (b' • bf)) :
    ((●V a) ~~>[SI] ((●V a' : View R) • ◯V b')) := by
  rw [← unit_right_id (x := (●V{own 1} a))]
  refine auth_one_op_frag_update (fun n bf H => Hup n bf <| IsViewRel.mono_inc H .rfl ?_ SIdx.le_refl)
  exact incN_op_right n unit bf

@[rocq_alias view_update_dealloc]
theorem auth_one_op_frag_dealloc (Hup : (∀ n bf, R n a (b • bf) → R n a' bf)) :
    ((●V a : View R) • ◯V b) ~~>[SI] ●V a' := by
  rw [← unit_right_id (x := (●V{own 1} a'))]
  refine auth_one_op_frag_update (fun n bf H => ?_)
  refine IsViewRel.mono_inc (Hup n bf H) .rfl ?_ SIdx.le_refl
  exact (unit_left_id_dist bf).to_incN

@[rocq_alias view_update_auth]
theorem auth_one_update (Hup : ∀ n bf, R n a bf → R n a' bf) :
    (●V a : View R) ~~>[SI] ●V a' := by
  rw [← unit_right_id (x := (●V{own 1} a'))]
  rw [← unit_right_id (x := (●V{own 1} a))]
  refine auth_one_op_frag_update (fun n bf H => ?_)
  exact IsViewRel.mono_inc (Hup n _ H) .rfl .rfl SIdx.le_refl

@[rocq_alias view_updateP_auth_dfrac]
theorem auth_updateP (Hupd : dq ~~>:[SI] P) :
    (●V{dq} a : View R) ~~>:[SI] (fun k => ∃ dq', (k = ●V{dq'} a) ∧ P dq') := by
  refine UpdateP.total.mpr (fun n ⟨ag, bf⟩ => ?_)
  rcases ag with (_|⟨dq', ag⟩) <;> rintro ⟨Hv, a', _, _⟩
  · obtain ⟨dr, Hdr, Heq⟩ := Hupd n none Hv
    refine ⟨●V{dr} a, (by exists dr), ⟨Heq, (by exists a')⟩⟩
  · obtain ⟨dr, Hdr, Heq⟩ := Hupd n (some dq') Hv
    refine ⟨●V{dr} a, (by exists dr), ⟨Heq, (by exists a')⟩⟩

@[rocq_alias view_update_auth_persist]
theorem auth_discard : (●V{dq} a : View R) ~~>[SI] ●V{.discard} a := by
  apply Update.lift_updateP (g := fun dq => ●V{dq} a)
  · exact fun _ => auth_updateP
  · exact DFrac.update_discard

@[rocq_alias view_updateP_auth_unpersist]
theorem auth_acquire :
    (●V{.discard} a : View R) ~~>:[SI] fun k => ∃ q, k = ●V{.own q} a := by
  apply UpdateP.weaken
  · apply auth_updateP
    exact DFrac.update_acquire
  · rintro y ⟨dq, rfl, q', rfl⟩
    exists q'

@[rocq_alias view_updateP_both_unpersist]
theorem auth_op_frag_acquire :
    ((●V{.discard} a : View R) • ◯V b) ~~>:[SI] fun k => ∃ q, k = ((●V{.own q} a : View R) • ◯V b ):= by
  apply UpdateP.op
  apply auth_acquire
  apply UpdateP.id rfl
  rintro z1 z2 ⟨q, rfl⟩ rfl; exists q

@[rocq_alias view_updateP_frag]
theorem frag_updateP {P : B → Prop} (Hupd : ∀ a n bf, R n a (b • bf) → ∃ b', P b' ∧ R n a (b' • bf)) :
    (◯V b : View R) ~~>:[SI] (fun k => ∃ b', (k = (◯V b' : View R)) ∧ P b') := by
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
    simp [ORA.ValidN, ValidN, ORA.op, optionOp]
    exact ⟨Hq, ⟨a, Hae, Hp⟩⟩

@[rocq_alias view_update_frag]
theorem frag_update (Hupd : ∀ a n bf, R n a (b • bf) → R n a (b' • bf)) :
    (◯V b : View R) ~~>[SI] (◯V b' : View R) := by
  refine Update.total.mpr (fun n ⟨ag, bf⟩ => ?_)
  rcases ag with (_|⟨dq,af⟩)
  simp only [ORA.ValidN]
  · simp_all [ORA.op, optionOp]
    intro a HR
    exists a
    exact Hupd _ _ _ HR
  · simp_all [ORA.op, ORA.ValidN]
    intro Hq a He Hr
    exists a
    exact ⟨He, Hupd _ _ _ Hr⟩

@[rocq_alias view_update_dfrac_alloc]
theorem auth_alloc (Hup : ∀ n bf, R n a bf → R n a (b • bf)) :
    (●V{dq} a : View R) ~~>[SI] ((●V{dq} a) • ◯V b) := by
  refine Update.total.mpr (fun n ⟨ag', bf⟩ => ?_)
  obtain (_|⟨p, ag⟩) := ag'
  · simp [ORA.op, optionOp, ORA.ValidN, ValidN]
    intro Hq a' Hag HR
    refine ⟨Hq, a', Hag, ?_⟩
    have HR' := IsViewRel.mono_inc HR (toAgree.inj Hag).symm (incN_op_right n unit bf) SIdx.le_refl
    apply IsViewRel.mono_inc (Hup n bf HR') (toAgree.inj Hag) ?_ SIdx.le_refl
    apply Iris.OFE.Dist.to_incN
    refine comm.dist.trans (.trans ?_ comm.dist)
    refine op_ne.ne ?_
    exact (unit_left_id_dist _)
  · rintro ⟨Hv, a0, Hag, Hrel⟩
    refine ⟨Hv, ?_⟩
    exists a0
    refine ⟨Hag, ?_⟩
    have Heq  := Agree.toAgree_includedN.mp ⟨ag, Hag.symm⟩
    have HR' := IsViewRel.mono_inc Hrel Heq.symm (incN_op_right n unit bf) SIdx.le_refl
    apply IsViewRel.mono_inc (Hup _ _ HR') Heq ?_ SIdx.le_refl
    apply Iris.OFE.Dist.to_incN
    refine comm.dist.trans (.trans ?_ comm.dist)
    refine op_ne.ne ?_
    exact (unit_left_id_dist _)

@[rocq_alias view_local_update]
theorem view_local_update {a a' : A} {b0 b1 b0' b1' : B}
    (Hup : (b0, b1) ~l~>[SI] (b0', b1'))
    (Hrel : ∀ n, R n a b0 → R n a' b0') :
    ((●V a : View R) • ◯V b0, (●V a) • ◯V b1) ~l~>[SI] ((●V a') • ◯V b0', (●V a') • ◯V b1') := by
  rw [local_update_unital]
  rintro n ⟨(_ | ⟨dq, ag'⟩), bf⟩ Hv Heq <;> rw [auth_one_op_frag_validN_iff] at Hv
  · refine ⟨auth_one_op_frag_validN_iff.mpr (Hrel n Hv), ⟨.rfl, ?_⟩⟩
    refine .trans ?_ (unit_left_id_dist b1').symm.op_l
    refine unit_left_id_dist b0' |>.trans ?_
    refine (local_update_unital.mp Hup _ _ (IsViewRel.rel_validN _ _ _ Hv) ?_).2
    exact (unit_left_id_dist b0).symm.trans Heq.2 |>.trans (unit_left_id_dist b1).op_l
  · refine absurd (DFrac.valid_own_op (SI := SI) (validN_ne Heq ?_).1)
      (by have : (1 : Qp).val = 1 := rfl; grind)
    exact auth_one_op_frag_validN_iff.mpr Hv

end Updates

section ViewMap
open ORA

@[rocq_alias view_map]
def map {R : ViewRel SI A B} (R' : ViewRel SI A' B') (f : A → A')
    (g : B → B') (v : View R) : View R' where
  auth := match v.auth with | none => none | some (fr, a) => (fr, a.map' f)
  frag := g v.frag

@[rocq_alias view_map_id]
theorem map_id {R : ViewRel SI A B} (v : View R) : View.map R id id v = v := by
  rcases v with ⟨a, b⟩
  cases a <;> simp [View.map, Agree.map'_id]

@[rocq_alias view_map_compose]
theorem map_compose {R : ViewRel SI A B} {R' : ViewRel SI A' B'} {R'' : ViewRel SI A'' B''}
    f g (f' : A' → A'') (g' : B' → B'') (v : View R) :
    View.map R'' (f' ∘ f) (g' ∘ g) v = View.map R'' f' g' (View.map R' f g v) := by
  rcases v with ⟨a, b⟩
  cases a <;> simp [View.map, Agree.map'_compose]

section mapO

variable [OFE SI A] [OFE SI B] [OFE SI A'] [OFE SI B'] {R : ViewRel SI A B} {R' : ViewRel SI A' B'}

theorem map_compose' [OFE SI A''] [OFE SI B''] {R'' : ViewRel SI A'' B''}
    f g (f' : A' -n>[SI] A'') (g' : B' -n>[SI] B'') (v : View R) :
    View.map R'' (f'.comp f) (g'.comp g) v = View.map R'' f' g' (View.map R' f g v) :=
    map_compose f.f g.f f'.f g'.f v

#rocq_ignore view_map_ext "OFE is Leibniz; use equality"

omit [OFE SI B] in
theorem map_ne {n : SI} {f1 f2 : A → A'} {g1 g2 : B → B'} [OFE.NonExpansive SI f1] [OFE.NonExpansive SI f2]
    (v : View R) (h1 : ∀ a, f1 a ≡{n}≡ f2 a) (h2 : ∀ b, g1 b ≡{n}≡ g2 b) :
    View.map R' f1 g1 v ≡{n}≡ View.map R' f2 g2 v := by
  refine ⟨?_, h2 _⟩
  simp only [View.map]
  split
  · rfl
  · exact ⟨rfl, Agree.map_ne h1⟩

@[rocq_alias view_map_ne]
instance (f : A → A') (g : B → B') [OFE.NonExpansive SI f] [hne : OFE.NonExpansive SI g] :
    OFE.NonExpansive SI (View.map R' f g : (View R → _)) where
  ne := by
    rintro n _ _ ⟨h1, h2⟩
    refine ⟨?_, hne.ne h2⟩
    simp only [map]
    split <;> split <;> simp_all
    exact ⟨h1.1, Agree.map f |>.ne.ne h1.2⟩

@[rocq_alias viewO_map]
def mapO (f : A -n>[SI] A') (g : B -n>[SI] B') : View R -n>[SI] View R' where
  f := View.map R' f g
  ne := inferInstance

@[rocq_alias viewO_map_ne]
instance mapO_ne : OFE.NonExpansive₂ SI (mapO (R := R) (R' := R')) where
  ne _ _ _ hf _ _ hg v := map_ne v (hf ·) (hg ·)

end mapO

def mapAuthC [OFE SI A] [OFE SI A'] (f : A -n>[SI] A') :
    Option ((DFrac) × Agree A) -C>[SI] Option ((DFrac) × Agree A') :=
  Option.mapC (Prod.mapC Hom.id (Agree.map f.f))

theorem map_auth_eq [OFE SI A] [OFE SI A'] {R : ViewRel SI A B} {R' : ViewRel SI A' B'}
    (f : A -n>[SI] A') (g : B → B') (v : View R) :
    (map R' f.f g v).auth = (mapAuthC f).f v.auth := by
  rcases v with ⟨_|⟨fr, a⟩, b⟩ <;> rfl

@[rocq_alias view_map_cmra_morphism]
def mapC [OFE SI A] [URA B] [UORA SI B] [OFE SI A'] [URA B'] [UORA SI B']
    {R : ViewRel SI A B} [IsViewRel R] {R' : ViewRel SI A' B'} [IsViewRel R']
    (f : A -n>[SI] A') (g : B -C>[SI] B') (H : ∀ n a b, R n a b → R' n (f a) (g b)) :
    View R -C>[SI] View R' where
  f := View.map R' f g
  ne := inferInstance
  validN {n : SI} {x} hval := by
    simp [ORA.ValidN, map] at *
    rcases x with ⟨_ | ⟨fr,a⟩, b⟩ <;> simp_all
    · obtain ⟨a, hr⟩ := hval
      exists f a
      exact (H n a b hr)
    · rcases hval with ⟨hfr, a1, ha, hr⟩
      exact ⟨f a1, ⟨OFE.NonExpansive.ne ha, H n a1 b hr⟩⟩
  pcore x := by
    simp [ORA.pcore, map, ORA.core, Option.getD]
    refine ⟨?_, ?_⟩
    · rcases x.auth with _|⟨fr, a⟩ <;> simp [Prod.pcore]
      rcases (ORA.pcore fr) <;> simp
      rcases h : (ORA.pcore a) <;> cases h; simp [ORA.pcore]
    · have _ := g.pcore x.frag
      rcases _ : (ORA.pcore x.frag) <;>
      rcases _ : (ORA.pcore (g.f x.frag)) <;> simp_all
  op x y := by
    rcases x with ⟨xa, xf⟩; rcases y with ⟨ya, yf⟩
    simp only [ORA.op, map]
    simp only [Op, View.mk.injEq]
    refine ⟨?_, ?_⟩
    · cases xa <;> cases ya <;> simp [ORA.op, optionOp, Prod.op]
      exact (Agree.map (SI := SI) f.f).op _ _
    · exact g.op xf yf
  monoN_ord {n : SI} {x y} h := by
    refine ⟨?_, g.monoN_ord h.2⟩
    rw [map_auth_eq, map_auth_eq]
    exact (mapAuthC f).monoN_ord h.1
  mono_ord {x y} h := by
    refine ⟨?_, g.mono_ord h.2⟩
    rw [map_auth_eq, map_auth_eq]
    exact (mapAuthC f).mono_ord h.1
  increasing {v} h := by
    refine increasing_mk ?_ (g.increasing (increasing_frag h))
    rw [map_auth_eq]
    exact (mapAuthC f).increasing (increasing_auth h)

end ViewMap

end View

/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Janine Lohse
-/
module

public import Iris.Algebra.CMRA
public import Iris.Algebra.Updates
public import Iris.Algebra.LocalUpdates

@[expose] public section

namespace Iris

variable {SI : Type _} [instSI : SIdx SI]

@[rocq_alias csum]
inductive Csum (α β : Type _) where
  | inl : α → Csum α β
  | inr : β → Csum α β
  | invalid : Csum α β

#rocq_ignore maybe_Cinl "std++ `Maybe` class; pattern match instead"
#rocq_ignore maybe_Cinr "std++ `Maybe` class; pattern match instead"

open Csum OFE ORA

namespace Csum

/-! ## OFE -/

#rocq_ignore csum_equiv "OFE is Leibniz; use equality"

@[simp, rocq_alias csum_dist] def Dist [OFE SI α] [OFE SI β] (n : SI) : Csum α β → Csum α β → Prop
  | inl a, inl a' => a ≡{n}≡ a'
  | inr b, inr b' => b ≡{n}≡ b'
  | invalid, invalid => True
  | _, _ => False

theorem dist_eqv [OFE SI α] [OFE SI β] {n : SI} : Equivalence (Csum.Dist (α := α) (β := β) n) where
  refl {x} := by cases x with
    | inl => exact Dist.rfl
    | inr => exact Dist.rfl
    | invalid => trivial
  symm {x y} h := by cases x <;> cases y <;> first | trivial | exact h.symm
  trans {x y z} h₁ h₂ := by
    cases x <;> cases y <;> cases z <;>
      first | trivial | exact h₁.trans h₂

@[rocq_alias csumO]
instance [OFE SI α] [OFE SI β] : OFE SI (Csum α β) where
  dist := Csum.Dist
  dist_eqv := dist_eqv
  eq_dist' {x y} := by
    cases x <;> cases y <;> simp [Csum.Dist, eq_dist (SI := SI)]
  dist_lt {n : SI} {x y m} hn hlt := by
    cases x <;> cases y <;> first | exact OFE.Dist.lt hn hlt | exact hn.elim | trivial

#rocq_ignore csum_ofe_mixin "Not needed"

@[rocq_alias Cinl_ne]
instance [OFE SI α] [OFE SI β] : NonExpansive SI (inl (α := α) (β := β)) where
  ne _ _ _ := id

#rocq_ignore Cinl_proper "Derivable using NonExpansive.eqv"

@[rocq_alias Cinr_ne]
instance [OFE SI α] [OFE SI β] : NonExpansive SI (inr (α := α) (β := β)) where
  ne _ _ _ := id

#rocq_ignore Cinr_proper "Derivable using NonExpansive.eqv"

@[rocq_alias Cinl_inj]
theorem inl_inj {a a' : α} (h : (inl (β := β) a) = inl a') : a = a' :=
  Csum.inl.inj h

@[rocq_alias Cinl_inj_dist]
theorem inl_injN [OFE SI α] [OFE SI β] {n : SI} {a a' : α} (h : inl (β := β) a ≡{n}≡ inl a') : a ≡{n}≡ a' := h

@[rocq_alias Cinr_inj]
theorem inr_inj {b b' : β} (h : (inr (α := α) b) = inr b') : b = b' :=
  Csum.inr.inj h

@[rocq_alias Cinr_inj_dist]
theorem inr_injN [OFE SI α] [OFE SI β] {n : SI} {b b' : β} (h : inr (α := α) b ≡{n}≡ inr b') : b ≡{n}≡ b' := h

@[rocq_alias csum_ofe_discrete]
instance [OFE SI α] [OFE SI β] [OFE.Discrete SI α] [OFE.Discrete SI β] : OFE.Discrete SI (Csum α β) where
  discrete_0 {x y} h := by cases x <;> cases y <;>
    first
      | exact congrArg inl (discrete_0 (α := α) h)
      | exact congrArg inr (discrete_0 (α := β) h)
      | exact h.elim | trivial

#rocq_ignore csum_leibniz "Not needed"

@[rocq_alias Cinl_discrete]
instance [OFE SI α] [OFE SI β] {a : α} [DiscreteE SI a] : DiscreteE SI (inl (β := β) a) where
  discrete {x} h := by
    cases x with
    | inl => exact congrArg inl (DiscreteE.discrete (x := a) h)
    | inr => exact h.elim
    | invalid => exact h.elim

@[rocq_alias Cinr_discrete]
instance [OFE SI α] [OFE SI β] {b : β} [DiscreteE SI b] : DiscreteE SI (inr (α := α) b) where
  discrete {x} h := by
    cases x with
    | inl => exact h.elim
    | inr => exact congrArg inr (DiscreteE.discrete (x := b) h)
    | invalid => exact h.elim

instance [OFE SI α] [OFE SI β] : DiscreteE SI (@invalid α β) where
  discrete {x} h := by
    cases x with
    | inl => exact h.elim
    | inr => exact h.elim
    | invalid => exact rfl

/-! ## COFE -/

@[simp] def getInlD (x : Csum α β) (d : α) : α :=
  match x with | inl a => a | _ => d

@[simp] def getInrD (x : Csum α β) (d : β) : β :=
  match x with | inr b => b | _ => d

@[rocq_alias csum_chain_l]
def chainL [OFE SI α] [OFE SI β] (c : Chain SI (Csum α β)) (a : α) : Chain SI α where
  chain n := (c n).getInlD a
  cauchy {n : SI} {i} h := by
    have hc := c.cauchy h; revert hc
    cases c.chain i <;> cases c.chain n <;> simp [OFE.Dist, HasDist.dist]

@[rocq_alias csum_chain_r]
def chainR [OFE SI α] [OFE SI β] (c : Chain SI (Csum α β)) (b : β) : Chain SI β where
  chain n := (c n).getInrD b
  cauchy {n : SI} {i} h := by
    have hc := c.cauchy h; revert hc
    cases c.chain i <;> cases c.chain n <;> simp [OFE.Dist, HasDist.dist]

@[rocq_alias csum_cofe]
instance [SIdxFinite SI] [OFE SI α] [OFE SI β] [IsCOFE SI α] [IsCOFE SI β] : IsCOFE SI (Csum α β) where
  compl c :=
    match c 0 with
    | inl a => inl (IsCOFE.compl (chainL c a))
    | inr b => inr (IsCOFE.compl (chainR c b))
    | invalid => invalid
  conv_compl {n : SI} {c} := by
    have h0n := c.cauchy (i := n) SIdx.le_0_l
    revert h0n
    rcases e0 : c.chain 0 with a|b|_ <;> rcases en : c.chain n with a'|b'|_ <;> try (· exact id)
    · intro _
      change IsCOFE.compl (chainL c a) ≡{n}≡ a'
      refine OFE.Dist.trans COFE.conv_compl ?_
      simp [chainL, en]
    · intro _
      change IsCOFE.compl (chainR c b) ≡{n}≡ b'
      refine OFE.Dist.trans COFE.conv_compl ?_
      simp [chainR, en]
  lbcompl := (·.elim)
  conv_lbcompl := (·.elim)
  lbcompl_ne := (·.elim)

#rocq_ignore csum_compl "Included in IsCOFE instance"

/-! ## ORA -/

@[simp] abbrev valid [ORA SI α] [ORA SI β] : Csum α β → Prop
  | inl a => ✓[SI] a
  | inr b => ✓[SI] b
  | invalid => False

@[simp] abbrev validN [ORA SI α] [ORA SI β] (n : SI) : Csum α β → Prop
  | inl a => ✓{n} a
  | inr b => ✓{n} b
  | invalid => False

abbrev pcore [PCore α] [PCore β] : Csum α β → Option (Csum α β)
  | inl a => (PCore.pcore a).map inl
  | inr b => (PCore.pcore b).map inr
  | invalid => some invalid

abbrev op [Op α] [Op β] : Csum α β → Csum α β → Csum α β
  | inl a, inl a' => inl (a • a')
  | inr b, inr b' => inr (b • b')
  | _, _ => invalid

@[rocq_alias Cinl_op]
theorem inl_op [ORA SI α] [ORA SI β] (a a' : α) :
    inl (β := β) (a • a') = Csum.op (inl a) (inl a') := rfl

@[rocq_alias Cinr_op]
theorem inr_op [ORA SI α] [ORA SI β] (b b' : β) :
    inr (α := α) (b • b') = Csum.op (inr b) (inr b') := rfl

private theorem pcore_map_inl_eq [PCore α] {a : α} {cx : Csum α β}
    (h : (PCore.pcore a).map inl = some cx) :
    ∃ ca, PCore.pcore a = some ca ∧ cx = inl ca := by
  cases _ : PCore.pcore a <;> simp_all

private theorem pcore_map_inr_eq [PCore β] {b : β} {cx : Csum α β}
    (h : (PCore.pcore b).map inr = some cx) :
    ∃ cb, PCore.pcore b = some cb ∧ cx = inr cb := by
  cases _ : PCore.pcore b <;> simp_all

abbrev OrderN [ORA SI α] [ORA SI β] (n : SI) : Csum α β → Csum α β → Prop
  | _, invalid => True
  | inl a, inl a' => a ≼ₒ{n} a'
  | inr b, inr b' => b ≼ₒ{n} b'
  | _, _ => False

abbrev Order [ORA SI α] [ORA SI β] : Csum α β → Csum α β → Prop
  | _, invalid => True
  | inl a, inl a' => a ≼ₒ[SI] a'
  | inr b, inr b' => b ≼ₒ[SI] b'
  | _, _ => False

@[reducible, rocq_alias csum_cmra_mixin]
instance raOp [Op α] [Op β] : Op (Csum α β) where
  op := Csum.op
  assoc {x y z} := by grind [Op.assoc]
  comm {x y} := by grind [Op.comm]

@[reducible] instance raPCore [PCore α] [PCore β] : PCore (Csum α β) where
  pcore := Csum.pcore
  pcore_idem {x cx} hpx := by cases x with
    | inl a =>
      obtain ⟨ca, hpa, rfl⟩ := pcore_map_inl_eq hpx
      simp [pcore_idem hpa]
    | inr b =>
      obtain ⟨cb, hpb, rfl⟩ := pcore_map_inr_eq hpx
      simp [pcore_idem hpb]
    | invalid => simp only [Csum.pcore, Option.some.injEq] at hpx; exact hpx ▸ rfl

@[reducible] def raValid [ORA SI α] [ORA SI β] : _root_.Iris.Valid SI (Csum α β) where
  Valid := Csum.valid (SI := SI)
  ValidN := Csum.validN
  valid_iff_validN {x} := by cases x <;> simp [valid_iff_validN (SI := SI)]

@[reducible] def raOrdered [ORA SI α] [ORA SI β] : Ordered SI (Csum α β) where
  OrderN := OrderN
  Order := Order (SI := SI)
  ordN_trans {n : SI} {x y z} h₁ h₂ := by grind [Ordered.ordN_trans]
  ord_trans {x y z} h₁ h₂ := by grind [Ordered.ord_trans]
  ordN_of_ord {x y} n h := by grind [Ordered.ordN_of_ord]

attribute [local instance] raOrdered in
theorem raOrderedNE [ORA SI α] [ORA SI β] : OrderedNE SI (Csum α β) where
  ordN_ne {n : SI} {x x' y y'} ex ey h := by
    cases x <;> cases x' <;> cases y <;> cases y' <;>
      first
        | trivial | exact ex.elim | exact ey.elim | exact h.elim
        | exact ordN_ne (α := α) ex ey h | exact ordN_ne (α := β) ex ey h
  ordN_le {n n' : SI} {x y} h le := by
    cases x <;> cases y <;> first | trivial | exact ordN_le (α := α) h le | exact ordN_le (α := β) h le | exact h

section
variable [ORA SI α] [ORA SI β]
attribute [local instance] raValid raOrdered raOrderedNE

theorem increasing_inl_iff {a : α} : Increasing SI (inl (β := β) a) ↔ Increasing SI a where
  mp h := ⟨fun a' => h.increasing (inl a')⟩
  mpr h := ⟨fun | inl a' => h.increasing a' | inr _ | invalid => trivial⟩

theorem increasing_inr_iff {b : β} : Increasing SI (inr (α := α) b) ↔ Increasing SI b where
  mp h := ⟨fun b' => h.increasing (inr b')⟩
  mpr h := ⟨fun | inr b' => h.increasing b' | inl _ | invalid => trivial⟩

instance instIncreasingInvalid : Increasing SI (invalid : Csum α β) := ⟨fun _ => trivial⟩

theorem ordNR_inl {n : SI} {a a' : α} (h : inl (β := β) a ≼ₒ*{n} inl a') : a ≼ₒ*{n} a' := h.imp id id
theorem ordNR_inr {n : SI} {b b' : β} (h : inr (α := α) b ≼ₒ*{n} inr b') : b ≼ₒ*{n} b' := h.imp id id

instance instORA : ORA SI (Csum α β) where
  toOp := raOp
  toPCore := raPCore
  toValid := raValid
  op_ne {x} := ⟨fun {n : SI} {y₁ y₂} hy => by cases x <;> cases y₁ <;> cases y₂ <;>
    first | exact OFE.Dist.op_r (α := α) hy | exact OFE.Dist.op_r (α := β) hy | exact hy | trivial⟩
  pcore_ne {n : SI} {x y cx} hxy hpx := by
    cases x <;> cases y <;> try exact hxy.elim
    · obtain ⟨ca, hpa, rfl⟩ := pcore_map_inl_eq hpx
      obtain ⟨cy, hcy, ecy⟩ := pcore_ne (cx := ca) hxy hpa
      exact ⟨inl cy, by simp [PCore.pcore, Csum.pcore, hcy], ecy⟩
    · obtain ⟨cb, hpb, rfl⟩ := pcore_map_inr_eq hpx
      obtain ⟨cy, hcy, ecy⟩ := pcore_ne (cx := cb) hxy hpb
      exact ⟨inr cy, by simp [PCore.pcore, Csum.pcore, hcy], ecy⟩
    · simp only [PCore.pcore, Csum.pcore, Option.some.injEq] at hpx
      exact ⟨invalid, rfl, hpx ▸ .rfl⟩
  validN_ne {n : SI} {x y} h hv := by
    cases x <;> cases y <;> first
      | exact h.elim | exact hv.elim
      | exact validN_ne (α := α) h hv | exact validN_ne (α := β) h hv
  validN_le {n n' : SI} {x} h le := by
    cases x with
    | inl => exact validN_le (α := α) h le
    | inr => exact validN_le (α := β) h le
    | invalid => exact h
  toOrderedNE := raOrderedNE
  pcore_op_left {x cx} hpx := by cases x with
    | inl a => obtain ⟨ca, hpa, rfl⟩ := pcore_map_inl_eq hpx; exact congrArg _ (pcore_op_left hpa)
    | inr b => obtain ⟨cb, hpb, rfl⟩ := pcore_map_inr_eq hpx; exact congrArg _ (pcore_op_left hpb)
    | invalid => exact (Option.some.inj hpx) ▸ rfl
  validN_op_left {n : SI} {x y} h := by
    cases x <;> cases y <;> first | exact validN_op_left h | exact h.elim
  extend {n : SI} {x y₁ y₂} hv he := by
    cases x <;> cases y₁ <;> cases y₂ <;> first
      | exact he.elim
      | exact hv.elim
      | (obtain ⟨z₁, z₂, hz, hz₁, hz₂⟩ := extend hv he
         exact ⟨inl z₁, inl z₂, congrArg _ hz, hz₁, hz₂⟩)
      | (obtain ⟨z₁, z₂, hz, hz₁, hz₂⟩ := extend hv he
         exact ⟨inr z₁, inr z₂, congrArg _ hz, hz₁, hz₂⟩)
  toOrdered := raOrdered
  op_monoN_left_ord {n : SI} {x y} z h := by
    cases x <;> cases y <;> cases z <;> first | trivial | exact h.elim | exact op_monoN_left_ord _ h
  op_mono_left_ord {x y} z h := by
    cases x <;> cases y <;> cases z <;> first | trivial | exact h.elim | exact op_mono_left_ord _ h
  validN_of_ordN {n : SI} {x y} h v := by
    cases x <;> cases y <;> first | trivial | exact h.elim | exact v.elim | exact validN_of_ordN h v
  pcore_monoN_ord {n : SI} {x y cx} h e := by
    match x, y, h with
    | inl _, inl _, h =>
      obtain ⟨ca, hpa, rfl⟩ := pcore_map_inl_eq e
      let ⟨c, hc, hi⟩ := pcore_monoN_ord h hpa
      exact ⟨inl c, Option.map_forall₂ inl hc, hi⟩
    | inr _, inr _, h =>
      obtain ⟨cb, hpb, rfl⟩ := pcore_map_inr_eq e
      let ⟨c, hc, hi⟩ := pcore_monoN_ord h hpb
      exact ⟨inr c, Option.map_forall₂ inr hc, hi⟩
    | _, invalid, _ => exact ⟨invalid, rfl, trivial⟩
    | inl _, inr _, h | inr _, inl _, h | invalid, inl _, h | invalid, inr _, h => exact h.elim
  pcore_mono_ord {x y cx} h e := by
    match x, y, h with
    | inl _, inl _, h =>
      obtain ⟨ca, hpa, rfl⟩ := pcore_map_inl_eq e
      let ⟨c, hc, hi⟩ := pcore_mono_ord h hpa
      exact ⟨inl c, Option.map_forall₂ inl hc, hi⟩
    | inr _, inr _, h =>
      obtain ⟨cb, hpb, rfl⟩ := pcore_map_inr_eq e
      let ⟨c, hc, hi⟩ := pcore_mono_ord h hpb
      exact ⟨inr c, Option.map_forall₂ inr hc, hi⟩
    | _, invalid, _ => exact ⟨invalid, rfl, trivial⟩
    | inl _, inr _, h | inr _, inl _, h | invalid, inl _, h | invalid, inr _, h => exact h.elim
  pcore_order_op {x cx} e y := by
    match x, y with
    | inl _, inl a' =>
      obtain ⟨ca, hpa, rfl⟩ := pcore_map_inl_eq e
      let ⟨c, hc, hi⟩ := pcore_order_op hpa a'
      exact ⟨inl c, Option.map_forall₂ inl hc, hi⟩
    | inr _, inr b' =>
      obtain ⟨cb, hpb, rfl⟩ := pcore_map_inr_eq e
      let ⟨c, hc, hi⟩ := pcore_order_op hpb b'
      exact ⟨inr c, Option.map_forall₂ inr hc, hi⟩
    | inl _, inr _ | inl _, invalid | inr _, inl _ | inr _, invalid
    | invalid, inl _ | invalid, inr _ | invalid, invalid => exact ⟨invalid, rfl, trivial⟩
  pcore_increasing {x cx} e := by
    match x with
    | inl a =>
      obtain ⟨ca, hpa, rfl⟩ := pcore_map_inl_eq e
      exact increasing_inl_iff.mpr (pcore_increasing hpa)
    | inr b =>
      obtain ⟨cb, hpb, rfl⟩ := pcore_map_inr_eq e
      exact increasing_inr_iff.mpr (pcore_increasing hpb)
    | invalid => cases e; exact inferInstance
  increasing_closed {n : SI} {x y} h h' := by
    match x, y, h' with
    | _, invalid, _ => exact inferInstance
    | inl _, inl _, h' =>
      exact increasing_inl_iff.mpr ((increasing_inl_iff.mp h).of_ordNR (ordNR_inl h'))
    | inr _, inr _, h' =>
      exact increasing_inr_iff.mpr ((increasing_inr_iff.mp h).of_ordNR (ordNR_inr h'))
    | inl _, inr _, h' | inr _, inl _, h' | invalid, inl _, h' | invalid, inr _, h' =>
      exact h'.elim (·.elim) (·.elim)
  ordN_extend {n : SI} {x y} v h := by
    match x, y, h with
    | inl _, inl _, h =>
      obtain ⟨z, hz, ez⟩ := ordN_extend v h
      exact ⟨inl z, hz, ez⟩
    | inr _, inr _, h =>
      obtain ⟨z, hz, ez⟩ := ordN_extend v h
      exact ⟨inr z, hz, ez⟩
    | _, invalid, _ => exact v.elim
    | inl _, inr _, h | inr _, inl _, h | invalid, inl _, h | invalid, inr _, h => exact h.elim

end

instance instOrderRefl [ORA SI α] [ORA SI β] [OrderRefl SI α] [OrderRefl SI β] : OrderRefl SI (Csum α β) where
  ord_refl | inl a => ord_refl a | inr b => ord_refl b | invalid => trivial

instance instIncOrd [ORA SI α] [ORA SI β] [IncOrd SI α] [IncOrd SI β] : IncOrd SI (Csum α β) :=
  IncOrd.of_increasing fun
    | inl a => increasing_inl_iff.mpr (IncOrd.increasing a)
    | inr b => increasing_inr_iff.mpr (IncOrd.increasing b)
    | invalid => inferInstance

#rocq_ignore csumR "Use Csum type with typeclass inference"
#rocq_ignore csum_op_instance "Use ORA instance"
#rocq_ignore csum_pcore_instance "Use ORA instance"
#rocq_ignore csum_validN_instance "Use ORA instance"
#rocq_ignore csum_valid_instance "Use ORA instance"

@[rocq_alias Cinl_valid]
theorem inl_valid [ORA SI α] [ORA SI β] {a : α} : ✓[SI] (inl (β := β) a) ↔ ✓[SI] a := .rfl

@[rocq_alias Cinr_valid]
theorem inr_valid [ORA SI α] [ORA SI β] {b : β} : ✓[SI] (inr (α := α) b) ↔ ✓[SI] b := .rfl

/-! ## ORA Discrete -/

@[rocq_alias csum_cmra_discrete]
instance [ORA SI α] [ORA SI β] [ORA.Discrete SI α] [ORA.Discrete SI β] : ORA.Discrete SI (Csum α β) where
  discrete_valid {x} hv :=
    match x with
    | inl a => discrete_valid (x := a) hv
    | inr b => discrete_valid (x := b) hv
    | invalid => hv
  discrete_ord {x y} h := by
    change Csum.OrderN 0 x y at h; change Csum.Order x y; grind [discrete_ord]

/-! ## CoreId -/

@[rocq_alias Cinl_core_id]
instance [ORA SI α] [ORA SI β] {a : α} [CoreId a] : CoreId (inl (β := β) a) where
  core_id := Option.map_forall₂ inl core_id

@[rocq_alias Cinr_core_id]
instance [ORA SI α] [ORA SI β] {b : β} [CoreId b] : CoreId (inr (α := α) b) where
  core_id := Option.map_forall₂ inr core_id

/-! ## Exclusive -/

@[rocq_alias Cinl_exclusive]
instance [ORA SI α] [ORA SI β] {a : α} [Exclusive SI a] : Exclusive SI (inl (β := β) a) where
  exclusive0_l | inl a' => Exclusive.exclusive0_l a' | inr _ | invalid => id

@[rocq_alias Cinr_exclusive]
instance [ORA SI α] [ORA SI β] {b : β} [Exclusive SI b] : Exclusive SI (inr (α := α) b) where
  exclusive0_l | inr b' => Exclusive.exclusive0_l b' | inl _ | invalid => id

/-! ## Cancelable -/

@[rocq_alias Cinl_cancelable]
instance [ORA SI α] [ORA SI β] {a : α} [Cancelable SI a] : Cancelable SI (inl (β := β) a) where
  cancelableN {n : SI} {y z} hv he := by
    cases y with
    | inl => cases z with | inl => exact cancelableN (x := a) hv he | _ => exact he
    | _ => trivial

@[rocq_alias Cinr_cancelable]
instance [ORA SI α] [ORA SI β] {b : β} [Cancelable SI b] : Cancelable SI (inr (α := α) b) where
  cancelableN {n : SI} {y z} hv he := by
    cases y with
    | inr => cases z with | inr => exact cancelableN (x := b) hv he | _ => exact he
    | _ => trivial

/-! ## IdFree -/

@[rocq_alias Cinl_id_free]
instance [ORA SI α] [ORA SI β] {a : α} [IdFree SI a] : IdFree SI (inl (β := β) a) where
  id_free0_r y hv he := by cases y with | inl a' => exact id_free0_r (x := a) _ hv he | _ => trivial

@[rocq_alias Cinr_id_free]
instance [ORA SI α] [ORA SI β] {b : β} [IdFree SI b] : IdFree SI (inr (α := α) b) where
  id_free0_r y hv he := by cases y with | inr b' => exact id_free0_r (x := b) _ hv he | _ => trivial

/-! ## Order -/

theorem ord [ORA SI α] [ORA SI β] {x y : Csum α β} :
    x ≼ₒ[SI] y ↔ y = invalid ∨
      (∃ a a', x = inl a ∧ y = inl a' ∧ a ≼ₒ[SI] a') ∨
      (∃ b b', x = inr b ∧ y = inr b' ∧ b ≼ₒ[SI] b') := by
  change Csum.Order x y ↔ _
  cases x <;> cases y <;> simp [Csum.Order]

theorem inl_ord [ORA SI α] [ORA SI β] {a a' : α} : (inl (β := β) a) ≼ₒ[SI] inl a' ↔ a ≼ₒ[SI] a' := .rfl

theorem inr_ord [ORA SI α] [ORA SI β] {b b' : β} : (inr (α := α) b) ≼ₒ[SI] inr b' ↔ b ≼ₒ[SI] b' := .rfl

theorem invalid_ord [ORA SI α] [ORA SI β] (x : Csum α β) : x ≼ₒ[SI] invalid := by cases x <;> trivial

theorem ordN [ORA SI α] [ORA SI β] {n : SI} {x y : Csum α β} :
    x ≼ₒ{n} y ↔ y = invalid ∨
      (∃ a a', x = inl a ∧ y = inl a' ∧ a ≼ₒ{n} a') ∨
      (∃ b b', x = inr b ∧ y = inr b' ∧ b ≼ₒ{n} b') := by
  change Csum.OrderN n x y ↔ _
  cases x <;> cases y <;> simp [Csum.OrderN]

theorem some_ord [ORA SI α] [ORA SI β] {x y : Csum α β} :
    some x ≼ₒ[SI] some y ↔ y = invalid ∨
      (∃ a a', x = inl a ∧ y = inl a' ∧ some a ≼ₒ[SI] some a') ∨
      (∃ b b', x = inr b ∧ y = inr b' ∧ some b ≼ₒ[SI] some b') := by
  rw [Option.some_ord_some_iff]
  change _ ∨ Csum.Order x y ↔ _
  cases x <;> cases y <;> simp [Csum.Order, Option.some_ord_some_iff]

theorem some_ordN [ORA SI α] [ORA SI β] {n : SI} {x y : Csum α β} :
    some x ≼ₒ{n} some y ↔ y = invalid ∨
      (∃ a a', x = inl a ∧ y = inl a' ∧ some a ≼ₒ{n} some a') ∨
      (∃ b b', x = inr b ∧ y = inr b' ∧ some b ≼ₒ{n} some b') := by
  rw [Option.some_ordN_some_iff]
  change Csum.Dist n x y ∨ Csum.OrderN n x y ↔ _
  cases x <;> cases y <;> simp [Csum.OrderN, Option.some_ordN_some_iff]

/-! ## Included -/

@[rocq_alias csum_included]
theorem included [ORA SI α] [ORA SI β] {x y : Csum α β} :
    x ≼ y ↔ y = invalid ∨
      (∃ a a', x = inl a ∧ y = inl a' ∧ a ≼ a') ∨
      (∃ b b', x = inr b ∧ y = inr b' ∧ b ≼ b') := by
  refine ⟨fun ⟨z, hz⟩ => ?_, ?_⟩
  · subst hz; cases x <;> cases z <;> first | exact .inl rfl | simp [ORA.op, inc_op_left]
  · rintro (rfl | ⟨a, a', rfl, rfl, c, rfl⟩ | ⟨b, b', rfl, rfl, c, rfl⟩) <;>
      first | exact ⟨invalid, by cases x <;> rfl⟩ | exact ⟨inl c, rfl⟩ | exact ⟨inr c, rfl⟩

@[rocq_alias Cinl_included]
theorem inl_included [ORA SI α] [ORA SI β] {a a' : α} :
    (inl (β := β) a) ≼ inl a' ↔ a ≼ a' :=
  ⟨fun ⟨z, hz⟩ => (by cases z <;> first | exact ⟨_, Csum.inl.inj hz⟩ | cases hz),
   fun ⟨c, hc⟩ => ⟨inl c, congrArg inl hc⟩⟩

@[rocq_alias Cinr_included]
theorem inr_included [ORA SI α] [ORA SI β] {b b' : β} :
    (inr (α := α) b) ≼ inr b' ↔ b ≼ b' :=
  ⟨fun ⟨z, hz⟩ => (by cases z <;> first | exact ⟨_, Csum.inr.inj hz⟩ | cases hz),
   fun ⟨c, hc⟩ => ⟨inr c, congrArg inr hc⟩⟩

@[rocq_alias CsumInvalid_included]
theorem invalid_included [ORA SI α] [ORA SI β] (x : Csum α β) : x ≼ invalid :=
  ⟨invalid, by cases x <;> rfl⟩

@[rocq_alias csum_includedN]
theorem includedN [ORA SI α] [ORA SI β] {n : SI} {x y : Csum α β} :
    x ≼{n} y ↔ y = invalid ∨
      (∃ a a', x = inl a ∧ y = inl a' ∧ a ≼{n} a') ∨
      (∃ b b', x = inr b ∧ y = inr b' ∧ b ≼{n} b') := by
  refine ⟨fun ⟨z, hz⟩ => ?_, ?_⟩
  · change Csum.Dist n y (Csum.op x z) at hz
    cases x <;> cases z <;> cases y <;> simp_all <;> exact ⟨_, hz⟩
  · rintro (rfl | ⟨a, a', rfl, rfl, c, hc⟩ | ⟨b, b', rfl, rfl, c, hc⟩) <;>
      first | exact ⟨invalid, by cases x <;> exact Dist.rfl⟩ | exact ⟨inl c, hc⟩ | exact ⟨inr c, hc⟩

@[rocq_alias Some_csum_included]
theorem some_included [ORA SI α] [ORA SI β] {x y : Csum α β} :
    some x ≼ some y ↔ y = invalid ∨
      (∃ a a', x = inl a ∧ y = inl a' ∧ some a ≼ some a') ∨
      (∃ b b', x = inr b ∧ y = inr b' ∧ some b ≼ some b') := by
  rw [Option.some_inc_some_iff (SI := SI), included]
  cases x <;> cases y <;> simp [Option.some_inc_some_iff]

@[rocq_alias Some_csum_includedN]
theorem some_includedN [ORA SI α] [ORA SI β] {n : SI} {x y : Csum α β} :
    some x ≼{n} some y ↔ y = invalid ∨
      (∃ a a', x = inl a ∧ y = inl a' ∧ some a ≼{n} some a') ∨
      (∃ b b', x = inr b ∧ y = inr b' ∧ some b ≼{n} some b') := by
  rw [Option.some_incN_some_iff, includedN]
  change Csum.Dist n x y ∨ _ ↔ _
  cases x <;> cases y <;> simp [Option.some_incN_some_iff]

/-! ## Updates -/

instance instOrdInc [ORA SI α] [ORA SI β] [OrdInc SI α] [OrdInc SI β] : OrdInc SI (Csum α β) where
  ord_inc h := included.mpr <| (ord.mp h).imp id fun h => h.imp
    (fun ⟨a, a', e₁, e₂, h⟩ => ⟨a, a', e₁, e₂, OrdInc.ord_inc h⟩)
    (fun ⟨b, b', e₁, e₂, h⟩ => ⟨b, b', e₁, e₂, OrdInc.ord_inc h⟩)
  ordN_incN h := includedN.mpr <| (ordN.mp h).imp id fun h => h.imp
    (fun ⟨a, a', e₁, e₂, h⟩ => ⟨a, a', e₁, e₂, OrdInc.ordN_incN h⟩)
    (fun ⟨b, b', e₁, e₂, h⟩ => ⟨b, b', e₁, e₂, OrdInc.ordN_incN h⟩)

instance instIsInc [ORA SI α] [ORA SI β] [IsInc SI α] [IsInc SI β] : IsInc SI (Csum α β) := {}

@[rocq_alias csum_update_l]
theorem update_l [ORA SI α] [ORA SI β] {a₁ a₂ : α}
    (h : a₁ ~~>[SI] a₂) : (inl (β := β) a₁) ~~>[SI] inl a₂ := by
  intro n mz hv; cases mz with
  | none => exact h n none hv
  | some z => cases z with | inl a' => exact h n (some a') hv | _ => exact hv.elim

@[rocq_alias csum_update_r]
theorem update_r [ORA SI α] [ORA SI β] {b₁ b₂ : β}
    (h : b₁ ~~>[SI] b₂) : (inr (α := α) b₁) ~~>[SI] inr b₂ := by
  intro n mz hv; cases mz with
  | none => exact h n none hv
  | some z => cases z with | inr b' => exact h n (some b') hv | _ => exact hv.elim

@[rocq_alias csum_updateP_l]
theorem updateP_l [ORA SI α] [ORA SI β] {P : α → Prop} {Q : Csum α β → Prop} {a : α}
    (h : a ~~>:[SI] P) (hPQ : ∀ a', P a' → Q (inl a')) : (inl (β := β) a) ~~>:[SI] Q := by
  intro n mz hv; cases mz with
  | none => obtain ⟨c, hc, hvc⟩ := h n none hv; exact ⟨inl c, hPQ c hc, hvc⟩
  | some z => cases z with
    | inl a' => obtain ⟨c, hc, hvc⟩ := h n (some a') hv; exact ⟨inl c, hPQ c hc, hvc⟩
    | _ => exact hv.elim

@[rocq_alias csum_updateP_r]
theorem updateP_r [ORA SI α] [ORA SI β] {P : β → Prop} {Q : Csum α β → Prop} {b : β}
    (h : b ~~>:[SI] P) (hPQ : ∀ b', P b' → Q (inr b')) : (inr (α := α) b) ~~>:[SI] Q := by
  intro n mz hv; cases mz with
  | none => obtain ⟨c, hc, hvc⟩ := h n none hv; exact ⟨inr c, hPQ c hc, hvc⟩
  | some z => cases z with
    | inr b' => obtain ⟨c, hc, hvc⟩ := h n (some b') hv; exact ⟨inr c, hPQ c hc, hvc⟩
    | _ => exact hv.elim

@[rocq_alias csum_updateP'_l]
theorem updateP'_l [ORA SI α] [ORA SI β] {P : α → Prop} {a : α}
    (h : a ~~>:[SI] P) : (inl (β := β) a) ~~>:[SI] fun m' => ∃ a', m' = inl a' ∧ P a' :=
  updateP_l h fun a' ha' => ⟨a', rfl, ha'⟩

@[rocq_alias csum_updateP'_r]
theorem updateP'_r [ORA SI α] [ORA SI β] {P : β → Prop} {b : β}
    (h : b ~~>:[SI] P) : (inr (α := α) b) ~~>:[SI] fun m' => ∃ b', m' = inr b' ∧ P b' :=
  updateP_r h fun b' hb' => ⟨b', rfl, hb'⟩

/-! ## Local Updates -/

@[rocq_alias csum_local_update_l]
theorem local_update_l [ORA SI α] [ORA SI β] {a₁ a₂ a₁' a₂' : α}
    (h : (a₁, a₂) ~l~>[SI] (a₁', a₂')) :
    ((inl (β := β) a₁, inl a₂) ~l~>[SI] (inl a₁', inl a₂')) := by
  intro n mf hv he; cases mf with
  | none => exact h n none hv he
  | some z => cases z with | inl a' => exact h n (some a') hv he | _ => exact he.elim

@[rocq_alias csum_local_update_r]
theorem local_update_r [ORA SI α] [ORA SI β] {b₁ b₂ b₁' b₂' : β}
    (h : (b₁, b₂) ~l~>[SI] (b₁', b₂')) :
    ((inr (α := α) b₁, inr b₂) ~l~>[SI] (inr b₁', inr b₂')) := by
  intro n mf hv he; cases mf with
  | none => exact h n none hv he
  | some z => cases z with | inr b' => exact h n (some b') hv he | _ => exact he.elim

/-! ## Functor -/

@[simp, rocq_alias csum_map]
def map (f : α → α') (g : β → β') : Csum α β → Csum α' β'
  | inl a => inl (f a)
  | inr b => inr (g b)
  | invalid => invalid

@[rocq_alias csum_map_id]
theorem map_id {x : Csum α β} : map id id x = x := by cases x <;> simp

@[rocq_alias csum_map_compose]
theorem map_compose (f : α → α') (f' : α' → α'') (g : β → β') (g' : β' → β'')
    (x : Csum α β) : map (f' ∘ f) (g' ∘ g) x = map f' g' (map f g x) := by
  cases x <;> simp

@[rocq_alias csum_map_ext]
theorem map_ext (f f' : α → α') (g g' : β → β')
    (hf : ∀ x, f x = f' x) (hg : ∀ x, g x = g' x) (x : Csum α β) :
    map f g x = map f' g' x := by
  cases x <;> simp [hf, hg]

@[rocq_alias csum_map_cmra_ne]
theorem map_ne [OFE SI α] [OFE SI α'] [OFE SI β] [OFE SI β'] {n : SI}
    {f f' : α → α'} (hf : ∀ ⦃x₁ x₂⦄, x₁ ≡{n}≡ x₂ → f x₁ ≡{n}≡ f' x₂)
    {g g' : β → β'} (hg : ∀ ⦃x₁ x₂⦄, x₁ ≡{n}≡ x₂ → g x₁ ≡{n}≡ g' x₂)
    {x y : Csum α β} (hxy : x ≡{n}≡ y) :
    map f g x ≡{n}≡ map f' g' y := by
  cases x with
  | inl => cases y with | inl => simp [map]; exact hf hxy | _ => exact hxy
  | inr => cases y with | inr => simp [map]; exact hg hxy | _ => exact hxy
  | invalid => cases y with | invalid => trivial | _ => exact hxy

@[rocq_alias csumO_map]
def oMap [OFE SI α] [OFE SI α'] [OFE SI β] [OFE SI β'] (f : α -n>[SI] α') (g : β -n>[SI] β') :
    Csum α β -n>[SI] Csum α' β' where
  f := map f g
  ne := ⟨fun {_n} {_x₁} {_x₂} hxy =>
    map_ne (fun _ _ h => f.ne.1 h) (fun _ _ h => g.ne.1 h) hxy⟩

@[rocq_alias csumO_map_ne]
theorem oMap_ne [OFE SI α] [OFE SI α'] [OFE SI β] [OFE SI β'] :
    NonExpansive₂ SI (oMap (SI := SI) (α := α) (α' := α') (β := β) (β' := β')) where
  ne _ _ _ hf _ _ hg x := by
    cases x with
    | inl => simp [oMap, map]; exact hf _
    | inr => simp [oMap, map]; exact hg _
    | invalid => trivial

@[rocq_alias csumRF]
abbrev OF (Fa Fb : COFE.OFunctorPre SI) : COFE.OFunctorPre SI :=
  fun A B _ _ => Csum (Fa A B) (Fb A B)

@[rocq_alias csum_map_cmra_morphism]
def cMap [ORA SI α] [ORA SI α'] [ORA SI β] [ORA SI β']
    (fa : α -C>[SI] α') (fb : β -C>[SI] β') : Csum α β -C>[SI] Csum α' β' where
  f := map fa fb
  ne := (oMap fa.toHom fb.toHom).ne
  validN {n : SI} {x} hv := by cases x with
    | inl a => exact fa.validN hv
    | inr b => exact fb.validN hv
    | invalid => exact hv
  pcore x := by
    cases x with
    | inl a =>
      change ((PCore.pcore a).map inl).map (map fa fb) = (PCore.pcore (fa a)).map inl
      rw [Option.map_map]
      change (PCore.pcore a).map (inl ∘ ⇑fa) = _
      rw [show (PCore.pcore a).map (inl ∘ ⇑fa) = ((PCore.pcore a).map fa).map inl from
        (Option.map_map ..).symm]
      exact Option.map_forall₂ inl (fa.pcore a)
    | inr b =>
      change ((PCore.pcore b).map inr).map (map fa fb) = (PCore.pcore (fb b)).map inr
      rw [Option.map_map]
      change (PCore.pcore b).map (inr ∘ ⇑fb) = _
      rw [show (PCore.pcore b).map (inr ∘ ⇑fb) = ((PCore.pcore b).map fb).map inr from
        (Option.map_map ..).symm]
      exact Option.map_forall₂ inr (fb.pcore b)
    | invalid => trivial
  op x y := by cases x <;> cases y <;>
    first | exact congrArg _ (fa.op _ _) | exact congrArg _ (fb.op _ _) | trivial
  monoN_ord {n : SI} {x y} h := by
    cases x <;> cases y <;> first | trivial | exact h.elim | exact fa.monoN_ord h | exact fb.monoN_ord h
  mono_ord {x y} h := by
    cases x <;> cases y <;> first | trivial | exact h.elim | exact fa.mono_ord h | exact fb.mono_ord h
  increasing {x} h := by
    cases x with
    | inl a => exact increasing_inl_iff.mpr (fa.increasing (increasing_inl_iff.mp h))
    | inr b => exact increasing_inr_iff.mpr (fb.increasing (increasing_inr_iff.mp h))
    | invalid => exact (inferInstance : Increasing SI (invalid : Csum α' β'))

instance {Fa Fb} [RFunctor SI Fa] [RFunctor SI Fb] : RFunctor SI (OF Fa Fb) where
  map f g := cMap (RFunctor.map f g) (RFunctor.map f g)
  map_ne.ne _ _ _ hf _ _ hg x := by
    cases x <;> simp [cMap, map] <;> exact RFunctor.map_ne.ne hf hg _
  map_id x := by cases x <;> simp [cMap, map] <;> exact RFunctor.map_id _
  map_comp f g f' g' x := by
    cases x <;> simp [cMap, map] <;> exact RFunctor.map_comp f g f' g' _

instance instRFunctorAffine {Fa Fb} [RFunctor SI Fa] [RFunctor SI Fb] [RFunctorAffine SI Fa] [RFunctorAffine SI Fb] :
    RFunctorAffine SI (OF Fa Fb) where
  affine := inferInstance

@[rocq_alias csumRF_contractive]
instance {Fa Fb} [RFunctorContractive SI Fa] [RFunctorContractive SI Fb] :
    RFunctorContractive SI (OF Fa Fb) where
  map_contractive.1 {n : SI} {x y} hKL z := by
    cases z <;> first | exact RFunctorContractive.map_contractive.1 hKL _ | trivial

end Csum

end Iris

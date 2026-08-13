/-
Copyright (c) 2026 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
module

public import Iris.Algebra.LocalUpdates
public import Iris.Std.Classes

/-!
# Monotone resource algebras

Given a relation `R` on `α`, the monotone resource algebra records finite collections of
elements up to agreement on the elements lying below them. The principal element `toMra a`
embeds `a`; for preorders, the resource-algebra inclusion order between principal elements
coincides with `R`.
-/

@[expose] public section
local stepindex Nat

namespace Iris

open CMRA Iris.Std OFE

namespace Mra

def belowList (R : α → α → Prop) (a : α) (xs : List α) : Prop :=
  ∃ b, b ∈ xs ∧ R a b

def listEquiv (R : α → α → Prop) (xs ys : List α) : Prop :=
  ∀ a, belowList R a xs ↔ belowList R a ys

theorem listEquiv_equivalence (R : α → α → Prop) : Equivalence (listEquiv R) where
  refl _ _ := Iff.rfl
  symm h a := (h a).symm
  trans h₁ h₂ a := (h₁ a).trans (h₂ a)

def setoid (R : α → α → Prop) : Setoid (List α) where
  r := listEquiv R
  iseqv := listEquiv_equivalence R

end Mra

@[rocq_alias mra]
def Mra {α : Type _} (R : α → α → Prop) := Quotient (Mra.setoid R)

namespace Mra

variable {α : Type _} {R : α → α → Prop}

def mk (xs : List α) : Mra R := Quotient.mk _ xs

theorem sound {xs ys : List α} (h : listEquiv R xs ys) : mk (R := R) xs = mk ys :=
  Quotient.sound h

@[elab_as_elim]
theorem ind {motive : Mra R → Prop} (mk : ∀ xs, motive (mk xs)) (x : Mra R) : motive x :=
  Quotient.ind mk x

@[elab_as_elim]
theorem ind₂ {motive : Mra R → Mra R → Prop}
    (mk : ∀ xs ys, motive (mk xs) (mk ys)) (x y : Mra R) : motive x y :=
  Quotient.ind₂ mk x y

@[elab_as_elim]
theorem ind₃ {motive : Mra R → Mra R → Mra R → Prop}
    (mk : ∀ xs ys zs, motive (mk xs) (mk ys) (mk zs)) (x y z : Mra R) : motive x y z :=
  ind₂ (fun xs ys ↦ Quotient.ind (mk xs ys)) x y z

/-- The principal element of `Mra R` associated with `a`. -/
@[rocq_alias to_mra]
def toMra (a : α) : Mra R := mk [a]

@[rocq_alias mra_below]
def below (a : α) (x : Mra R) : Prop :=
  Quotient.lift (belowList R a) (fun _ _ h ↦ propext ((h : listEquiv R _ _) a)) x

@[rocq_alias mra_below_to_mra]
theorem below_toMra (a b : α) : below a (toMra (R := R) b) ↔ R a b :=
  ⟨fun ⟨_, hc, hac⟩ ↦ List.mem_singleton.mp hc ▸ hac,
    fun hab ↦ ⟨b, List.mem_singleton_self b, hab⟩⟩

#rocq_ignore mra_equiv "Use equality."
#rocq_ignore mra_equiv_equiv "Use equality."

@[rocq_alias mraO]
instance (R : α → α → Prop) : COFE (Mra R) := COFE.ofDiscrete _

theorem belowList_append (a : α) (xs ys : List α) :
    belowList R a (xs ++ ys) ↔ belowList R a xs ∨ belowList R a ys := by
  constructor
  · rintro ⟨b, hb, hab⟩
    exact (List.mem_append.mp hb).elim (fun h ↦ .inl ⟨b, h, hab⟩) (fun h ↦ .inr ⟨b, h, hab⟩)
  · rintro (⟨b, hb, hab⟩ | ⟨b, hb, hab⟩)
    · exact ⟨b, List.mem_append.mpr (.inl hb), hab⟩
    · exact ⟨b, List.mem_append.mpr (.inr hb), hab⟩

def append (x y : Mra R) : Mra R :=
  Quotient.lift₂ (fun xs ys ↦ mk (xs ++ ys))
    (fun _ _ _ _ hx hy ↦ sound fun a ↦ by
      rw [belowList_append, belowList_append, (hx : listEquiv R _ _) a, (hy : listEquiv R _ _) a])
    x y

theorem append_idem (x : Mra R) : append x x = x := by
  induction x using ind with
  | mk xs => exact sound fun a ↦ by rw [belowList_append, or_self]

#rocq_ignore mra_valid "Replaced by the `Valid` field of the CMRA instance."
#rocq_ignore mra_validN "Replaced by the `ValidN` field of the CMRA instance."
#rocq_ignore mra_op "Replaced by the `op` field of the CMRA instance."
#rocq_ignore mra_pcore "Replaced by the `pcore` field of the CMRA instance."

@[rocq_alias mra_cmra_mixin]
instance (R : α → α → Prop) : CMRA (Mra R) where
  pcore := some
  op := append
  ValidN _ _ := True
  Valid _ := True
  op_ne.ne _ _ _ h := by rw [h]
  pcore_ne hxy h := ⟨_, (congrArg some hxy.symm).trans h, .rfl⟩
  validN_ne _ := id
  valid_iff_validN := by simp
  validN_succ := id
  validN_op_left _ := trivial
  assoc {x y z} := by
    induction x, y, z using ind₃ with
    | mk xs ys zs => exact congrArg mk (List.append_assoc xs ys zs).symm
  comm {x y} := by
    induction x, y using ind₂ with
    | mk xs ys => exact sound fun a ↦ by rw [belowList_append, belowList_append, or_comm]
  pcore_op_left h :=
    (congrArg (append · _) (Option.some.inj h).symm).trans (append_idem _)
  pcore_idem _ := rfl
  pcore_op_mono h y :=
    ⟨y, congrArg (fun z ↦ some (append z y)) (Option.some.inj h)⟩
  extend _ h := ⟨_, _, h, .rfl, .rfl⟩

#rocq_ignore mraR "Use Mra."

@[rocq_alias mra_cmra_total]
instance : CMRA.IsTotal (Mra R) where
  total x := ⟨x, rfl⟩

@[rocq_alias mra_core_id]
instance (x : Mra R) : CMRA.CoreId x where
  core_id := rfl

@[rocq_alias mra_cmra_discrete]
instance : CMRA.Discrete (Mra R) where
  discrete_0 := id
  discrete_valid := id

#rocq_ignore mra_unit "Replaced by the `unit` field of UCMRA instance."
#rocq_ignore mraUR "Use Mra."

-- FIXME: upstream name `auth_ucmra_mixin` should be `mra_ucmra_mixin`
@[rocq_alias auth_ucmra_mixin]
instance (R : α → α → Prop) : UCMRA (Mra R) where
  unit := mk []
  unit_valid := trivial
  unit_left_id {x} := by
    induction x using ind with
    | mk xs => rfl
  pcore_unit := rfl

theorem eq_of_below_iff {x y : Mra R} (h : ∀ a, below a x ↔ below a y) : x = y := by
  induction x, y using ind₂ with
  | mk xs ys => exact sound h

theorem below_op (a : α) (x y : Mra R) : below a (x • y) ↔ below a x ∨ below a y := by
  induction x, y using ind₂ with
  | mk xs ys => exact belowList_append a xs ys

@[rocq_alias mra_idemp]
theorem idem (x : Mra R) : x • x = x := append_idem x

@[rocq_alias mra_included]
theorem inc_iff (x y : Mra R) : x ≼ y ↔ y = x • y :=
  ⟨fun h ↦ (CMRA.op_core_right_of_inc h).symm, fun h ↦ ⟨y, h⟩⟩

@[rocq_alias to_mra_R_op]
theorem toMra_op_of_rel [hR : Trans R R R] (a b : α) (h : R a b) :
    toMra (R := R) a • toMra b = toMra b :=
  eq_of_below_iff fun c ↦ by
    rw [below_op, below_toMra, below_toMra]
    exact ⟨fun hc ↦ hc.elim (fun hca ↦ hR.trans hca h) id, .inr⟩

@[rocq_alias to_mra_included]
theorem toMra_inc_iff [Std.Refl R] [Trans R R R] (a b : α) :
    toMra (R := R) a ≼ toMra b ↔ R a b := by
  constructor
  · rintro ⟨z, hz⟩
    rw [← below_toMra (R := R) a b, hz, below_op]
    exact .inl ((below_toMra a a).mpr (Std.Refl.refl a))
  · exact fun h ↦ ⟨toMra b, (toMra_op_of_rel a b h).symm⟩

@[rocq_alias mra_local_update_grow]
theorem local_update_grow [hR : Trans R R R] (a : α) (x : Mra R) (b : α) (h : R a b) :
    (toMra (R := R) a, x) ~l~> (toMra b, toMra b) := by
  refine (local_update_unital_discrete ..).mpr fun z _ haz ↦ ⟨trivial, ?_⟩
  refine eq_of_below_iff fun c ↦ ?_
  rw [below_toMra, below_op, below_toMra]
  constructor
  · exact .inl
  · rintro (hcb | hcz)
    · exact hcb
    · refine hR.trans ?_ h
      rw [← below_toMra (R := R) c a, haz, below_op]
      exact .inr hcz

@[rocq_alias mra_local_update_get_frag]
theorem local_update_get_frag [Std.Refl R] [Trans R R R] (a b : α) (h : R b a) :
    (toMra (R := R) a, UCMRA.unit) ~l~> (toMra a, toMra b) := by
  refine (local_update_unital_discrete ..).mpr fun z _ haz ↦ ⟨trivial, ?_⟩
  calc
    toMra a = toMra b • toMra a := (toMra_op_of_rel b a h).symm
    _ = toMra b • z := congrArg (toMra b • ·) (haz.trans CMRA.unit_left_id)

private theorem rel_iff_of_toMra_eq (hab : toMra (R := R) a = toMra b) (c : α) :
    R c a ↔ R c b := by
  calc
    R c a ↔ below c (toMra a) := (below_toMra c a).symm
    _ ↔ below c (toMra b) := iff_of_eq (congrArg (below c) hab)
    _ ↔ R c b := below_toMra c b

@[rocq_alias to_mra_rel_proper]
theorem toMra_rel_proper (S : α → α → Prop) (hS : ∀ {a}, S a a)
    (hrel : ∀ {a a' b b'}, S a a' → S b b' → (R a b ↔ R a' b')) :
    ∀ {a b}, S a b → toMra (R := R) a = toMra b :=
  fun {a b} hab ↦ eq_of_below_iff fun c ↦ by
    calc
      below c (toMra a) ↔ R c a := below_toMra c a
      _ ↔ R c b := hrel hS hab
      _ ↔ below c (toMra b) := (below_toMra c b).symm

@[rocq_alias to_mra_rel_inj]
theorem toMra_rel_injective (S : α → α → Prop) (hR : ∀ {a}, R a a)
    (hanti : ∀ {a b}, R a b → R b a → S a b) :
    ∀ {a b}, toMra (R := R) a = toMra b → S a b :=
  fun hab ↦ hanti
    ((rel_iff_of_toMra_eq hab _).mp hR) ((rel_iff_of_toMra_eq hab _).mpr hR)

@[rocq_alias to_mra_inj]
theorem toMra_injective [hR : Std.Refl R] [hanti : Antisymmetric (· = ·) R] :
    Function.Injective (toMra (R := R)) :=
  fun {_ _} hab ↦
    toMra_rel_injective (R := R) (fun a b : α ↦ a = b) (hR.refl _) hanti.antisymm hab

@[rocq_alias to_mra_proper]
theorem toMra_proper [HasEquiv α] [hS : Std.Refl (α := α) (· ≈ ·)]
    (hrel : ∀ {a a' b b'}, a ≈ a' → b ≈ b' → ((R a b) ↔ (R a' b'))) {a b : α} :
    a ≈ b → ((toMra a) : Mra R) = (toMra b) :=
  toMra_rel_proper (· ≈ ·) (hS.refl _) hrel

@[rocq_alias to_mra_equiv_inj]
theorem toMra_equiv_injective [HasEquiv α] [hR : Std.Refl R]
    [hanti : Antisymmetric (· ≈ ·) R] :
    ∀ {a b}, toMra (R := R) a = toMra b → a ≈ b :=
  toMra_rel_injective (R := R) (· ≈ ·) (hR.refl _) hanti.antisymm

end Mra
end Iris

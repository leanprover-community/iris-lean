/-
Copyright (c) 2026 Zongyuan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/
module

public import Iris.Algebra.LocalUpdates
public import Iris.Std.Classes
meta import Iris.Std.RocqPorting

/-!
# Monotone resource algebras

Given a relation `R` on `α`, the monotone resource algebra records finite collections of
elements up to agreement on the elements lying below them. The principal element `toMra a`
embeds `a`; for preorders, the resource-algebra inclusion order between principal elements
coincides with `R`.
-/

@[expose] public section

namespace Iris

open CMRA Iris.Std OFE

def mraBelowList (R : α → α → Prop) (a : α) (xs : List α) : Prop :=
  ∃ b, b ∈ xs ∧ R a b

def mraListEquiv (R : α → α → Prop) (xs ys : List α) : Prop :=
  ∀ a, mraBelowList R a xs ↔ mraBelowList R a ys

theorem mra_list_equiv_equivalence (R : α → α → Prop) :
    Equivalence (mraListEquiv R) where
  refl _ _ := Iff.rfl
  symm h a := (h a).symm
  trans h₁ h₂ a := (h₁ a).trans (h₂ a)

def mraSetoid (R : α → α → Prop) : Setoid (List α) where
  r := mraListEquiv R
  iseqv := mra_list_equiv_equivalence R

@[rocq_alias mra]
def Mra {α : Type _} (R : α → α → Prop) := Quotient (mraSetoid R)

namespace Mra

variable {α : Type _} {R : α → α → Prop}

@[rocq_alias to_mra]
def toMra (a : α) : Mra R := Quotient.mk _ [a]

@[rocq_alias mra_below]
def below (a : α) (x : Mra R) : Prop :=
  Quotient.lift (mraBelowList R a) (by
    intro xs ys h
    change mraListEquiv R xs ys at h
    exact propext (h a)) x

@[rocq_alias mra_below_to_mra]
theorem below_to_mra (a b : α) : below a (toMra (R := R) b) ↔ R a b :=
  ⟨fun ⟨_, hc, hac⟩ ↦ List.mem_singleton.mp hc ▸ hac,
    fun hab ↦ ⟨b, List.mem_singleton_self b, hab⟩⟩

#rocq_ignore mra_equiv "Use equality."
#rocq_ignore mra_equiv_equiv "Use equality."

@[rocq_alias mraO]
instance (R : α → α → Prop) : COFE (Mra R) := COFE.ofDiscrete _

theorem below_list_append (a : α) (xs ys : List α) :
    mraBelowList R a (xs ++ ys) ↔ mraBelowList R a xs ∨ mraBelowList R a ys := by
  constructor
  · rintro ⟨b, hb, hab⟩
    exact (List.mem_append.mp hb).elim (fun h ↦ .inl ⟨b, h, hab⟩) (fun h ↦ .inr ⟨b, h, hab⟩)
  · rintro (⟨b, hb, hab⟩ | ⟨b, hb, hab⟩)
    · exact ⟨b, List.mem_append.mpr (.inl hb), hab⟩
    · exact ⟨b, List.mem_append.mpr (.inr hb), hab⟩

def append (x y : Mra R) : Mra R :=
  Quotient.lift₂ (fun xs ys ↦ Quotient.mk _ (xs ++ ys))
    (by
      intro xs ys xs' ys' hx hy
      change mraListEquiv R xs xs' at hx
      change mraListEquiv R ys ys' at hy
      refine Quotient.sound (fun a => ?_)
      rw [below_list_append, below_list_append, hx a, hy a]) x y

@[elab_as_elim]
private theorem quotient_induction_on {motive : Mra R → Prop} (x : Mra R)
    (h : ∀ xs, motive (Quotient.mk _ xs)) : motive x :=
  Quotient.inductionOn x h

private theorem eq_of_below_iff {x y : Mra R}
    (h : ∀ a, below a x ↔ below a y) : x = y := by
  revert h
  refine quotient_induction_on x fun xs ↦ ?_
  refine quotient_induction_on y fun ys ↦ ?_
  intro h
  apply Quotient.sound
  exact h

private theorem below_append (a : α) (x y : Mra R) :
    below a (append x y) ↔ below a x ∨ below a y := by
  refine quotient_induction_on x fun xs ↦ ?_
  refine quotient_induction_on y fun ys ↦ ?_
  exact below_list_append a xs ys


theorem append_idem (x : Mra R) : append x x = x := by
  refine quotient_induction_on x fun _ ↦ ?_
  refine Quotient.sound fun _ => ?_
  rw [below_list_append, or_self]

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
    refine quotient_induction_on x fun xs ↦ ?_
    refine quotient_induction_on y fun ys ↦ ?_
    refine quotient_induction_on z fun zs ↦ ?_
    exact congrArg (Quotient.mk (mraSetoid R)) (List.append_assoc xs ys zs).symm
  comm {x y} := by
    refine quotient_induction_on x fun _ ↦ ?_
    refine quotient_induction_on y fun _ ↦ ?_
    apply Quotient.sound
    intro a
    rw [below_list_append, below_list_append, or_comm]
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

@[rocq_alias auth_ucmra_mixin]
instance (R : α → α → Prop) : UCMRA (Mra R) where
  unit := Quotient.mk _ []
  unit_valid := trivial
  unit_left_id := by
    intro x
    refine quotient_induction_on (R := R) x fun _ ↦ ?_
    rfl
  pcore_unit := rfl

@[rocq_alias mra_idemp]
theorem idem (x : Mra R) : x • x = x := append_idem x

@[rocq_alias mra_included]
theorem inc_iff (x y : Mra R) : x ≼ y ↔ y = x • y :=
  ⟨fun h ↦ (CMRA.op_core_right_of_inc h).symm, fun h ↦ ⟨y, h⟩⟩

@[rocq_alias to_mra_R_op]
theorem to_mra_op_of_rel [hR : Trans R R R] (a b : α) (h : R a b) :
    toMra (R := R) a • toMra b = toMra b := by
  change append (toMra a) (toMra b) = toMra b
  refine eq_of_below_iff fun c ↦ ?_
  rw [below_append, below_to_mra, below_to_mra]
  constructor
  · exact fun hca_or_hcb ↦ hca_or_hcb.elim (fun hca ↦ hR.trans hca h) id
  · exact .inr

@[rocq_alias to_mra_included]
theorem to_mra_inc_iff [Std.Refl R] [Trans R R R] (a b : α) :
    toMra (R := R) a ≼ toMra b ↔ R a b := by
  constructor
  · rintro ⟨z, hz⟩
    rw [← below_to_mra (R := R) a b, hz]
    exact (below_append a (toMra a) z).mpr <|
      .inl ((below_to_mra a a).mpr (Std.Refl.refl a))
  · exact fun h ↦ ⟨toMra b, (to_mra_op_of_rel a b h).symm⟩

@[rocq_alias mra_local_update_grow]
theorem local_update_grow [hR : Trans R R R] (a : α) (x : Mra R) (b : α) (h : R a b) :
    (toMra (R := R) a, x) ~l~> (toMra b, toMra b) := by
  refine (local_update_unital_discrete ..).mpr fun z _ haz ↦ ⟨trivial, ?_⟩
  change toMra b = append (toMra b) z
  change toMra a = append x z at haz
  refine eq_of_below_iff fun c ↦ ?_
  rw [below_to_mra, below_append, below_to_mra]
  constructor
  · exact .inl
  · rintro (hcb | hcz)
    · exact hcb
    · refine hR.trans ?_ h
      rw [← below_to_mra (R := R) c a, haz, below_append]
      exact .inr hcz

@[rocq_alias mra_local_update_get_frag]
theorem local_update_get_frag [Std.Refl R] [Trans R R R] (a b : α) (h : R b a) :
    (toMra (R := R) a, UCMRA.unit) ~l~> (toMra a, toMra b) := by
  refine (local_update_unital_discrete ..).mpr fun z _ haz ↦ ⟨trivial, ?_⟩
  calc
    toMra a = toMra b • toMra a := (to_mra_op_of_rel b a h).symm
    _ = toMra b • z := congrArg (toMra b • ·) (haz.trans CMRA.unit_left_id)

private theorem rel_iff_of_to_mra_eq (hab : toMra (R := R) a = toMra b) (c : α) :
    R c a ↔ R c b := by
  calc
    R c a ↔ below c (toMra a) := (below_to_mra c a).symm
    _ ↔ below c (toMra b) := iff_of_eq (congrArg (below c) hab)
    _ ↔ R c b := below_to_mra c b

@[rocq_alias to_mra_rel_proper]
theorem to_mra_rel_proper (S : α → α → Prop) (hS : ∀ {a}, S a a)
    (hrel : ∀ {a a' b b'}, S a a' → S b b' → (R a b ↔ R a' b')) :
    ∀ {a b}, S a b → toMra (R := R) a = toMra b :=
  fun {a b} hab ↦ eq_of_below_iff fun c ↦ by
    calc
      below c (toMra a) ↔ R c a := below_to_mra c a
      _ ↔ R c b := hrel hS hab
      _ ↔ below c (toMra b) := (below_to_mra c b).symm

@[rocq_alias to_mra_rel_inj]
theorem to_mra_rel_injective (S : α → α → Prop) (hR : ∀ {a}, R a a)
    (hanti : ∀ {a b}, R a b → R b a → S a b) :
    ∀ {a b}, toMra (R := R) a = toMra b → S a b :=
  fun hab ↦ hanti
    ((rel_iff_of_to_mra_eq hab _).mp hR) ((rel_iff_of_to_mra_eq hab _).mpr hR)

@[rocq_alias to_mra_inj]
theorem to_mra_injective [hR : Std.Refl R] [hanti : Antisymmetric (· = ·) R] :
    Function.Injective (toMra (R := R)) :=
  fun {_ _} hab ↦
    to_mra_rel_injective (R := R) (fun a b : α ↦ a = b) (hR.refl _) hanti.antisymm hab

@[rocq_alias to_mra_proper]
theorem to_mra_proper [HasEquiv α] [hS : Std.Refl (α := α) (· ≈ ·)]
    (hrel : ∀ {a a' b b'}, a ≈ a' → b ≈ b' → ((R a b) ↔ (R a' b'))) {a b : α} :
    a ≈ b → ((toMra a) : Mra R) = (toMra b) :=
  to_mra_rel_proper (· ≈ ·) (hS.refl _) hrel

@[rocq_alias to_mra_equiv_inj]
theorem to_mra_equiv_injective [HasEquiv α] [hR : Std.Refl R]
    [hanti : Antisymmetric (· ≈ ·) R] :
    ∀ {a b}, toMra (R := R) a = toMra b → a ≈ b :=
  to_mra_rel_injective (R := R) (· ≈ ·) (hR.refl _) hanti.antisymm

end Mra
end Iris

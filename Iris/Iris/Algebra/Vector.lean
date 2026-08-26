/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.List
public import Iris.Std.Vector

@[expose] public section

namespace Iris

open OFE COFE

/-! ## The vector OFE

`Vector α n` carries the OFE structure of `List α`, transported along `Vector.toList`. -/

section ofe
variable [OFE α]

@[rocq_alias vec_ofe_mixin]
instance : OFE (Vector α n) where
  Dist k u v := u.toList ≡{k}≡ v.toList
  dist_eqv := InvImage.equivalence dist_eqv
  eq_dist' := ⟨fun h _ => h ▸ .rfl, fun h => Vector.toList_inj.mp (eq_dist_2 h)⟩
  dist_lt h hlt := h.lt hlt
#rocq_ignore vecO "Use Vector"
#rocq_ignore vec_equiv "OFE is Leibniz; use equality"
#rocq_ignore vec_dist "Local Dist instance; folded into Lean's OFE (Vector α n) instance."

theorem vec_dist_toList {k} {u v : Vector α n} : u ≡{k}≡ v ↔ u.toList ≡{k}≡ v.toList := .rfl

@[rocq_alias vec_ofe_discrete]
instance vec_ofe_discrete [Discrete α] : Discrete (Vector α n) where
  discrete_0 h := Vector.toList_inj.mp (discrete_0 (vec_dist_toList.mp h))

@[rocq_alias vnil_discrete]
instance vec_nil_discrete : DiscreteE (#v[] : Vector α 0) where
  discrete h := Vector.toList_inj.mp (DiscreteE.discrete (x := []) (vec_dist_toList.mp h))

/-- Discreteness of a vector transfers to its underlying list. -/
instance vec_toList_discrete (v : Vector α n) [DiscreteE v] : DiscreteE v.toList where
  discrete {l} h := by
    have hl : l.length = n := by rw [← h.length_eq, Vector.length_toList]
    have hv : v = Vector.ofList l hl :=
      ‹DiscreteE v›.discrete (vec_dist_toList.mpr (by simpa using h))
    rw [hv, Vector.toList_ofList]

@[rocq_alias vcons_discrete]
instance vec_cons_discrete (x : α) (v : Vector α n) [DiscreteE x] [DiscreteE v] :
    DiscreteE (v.cons x) where
  discrete h := Vector.toList_inj.mp <| by
    rw [Vector.toList_cons]
    exact DiscreteE.discrete (by simpa using vec_dist_toList.mp h)

end ofe

/-! ## COFE structure -/

section cofe
variable [COFE α]

def vecToListHom : Vector α n -n> List α where
  f := Vector.toList
  ne := ⟨fun _ _ _ h => h⟩

@[simp] theorem vecToListHom_apply {v : Vector α n} : vecToListHom v = v.toList := rfl

theorem length_compl_vecToListHom (c : Chain (Vector α n)) :
    (compl (c.map vecToListHom)).length = n :=
  (length_dist (n := 0) conv_compl).trans Vector.length_toList

@[rocq_alias vector.list_cofe]
instance : IsCOFE (Vector α n) where
  compl c := .ofList (compl (c.map vecToListHom)) (length_compl_vecToListHom c)
  conv_compl {k c} := vec_dist_toList.mpr <| by
    rw [Vector.toList_ofList]
    exact conv_compl

end cofe

/-! ## Nonexpansiveness of the vector operations -/

section proper
variable [OFE α]

@[rocq_alias vcons_ne]
instance vec_cons_ne : NonExpansive₂ (Vector.cons (α := α) (n := n)) where
  ne _ _ _ hx _ _ hv := by
    simp only [vec_dist_toList, Vector.toList_cons]
    exact .cons hx (vec_dist_toList.mp hv)
#rocq_ignore vcons_proper "OFE is Leibniz; use equality"

@[rocq_alias vlookup_ne]
instance vec_getElem_ne (i : Nat) (h : i < n) :
    NonExpansive (fun v : Vector α n => v[i]) where
  ne _ _ _ hv := by
    have hd := (vec_dist_toList.mp hv).getElem? i
    simp only [Vector.getElem?_toList, Vector.getElem?_eq_getElem h] at hd
    exact hd
#rocq_ignore vlookup_proper "OFE is Leibniz; use equality"

@[rocq_alias vec_to_list_ne]
instance vec_toList_ne : NonExpansive (Vector.toList (α := α) (n := n)) where
  ne _ _ _ h := vec_dist_toList.mp h
#rocq_ignore vec_to_list_proper "OFE is Leibniz; use equality"

end proper

/-! ## The vector functor -/

section functor

#rocq_ignore vec_map "Use Vector.map"

@[rocq_alias vec_map_ext_ne]
theorem vec_map_ext_ne [OFE α] [OFE β] {k} {f g : α → β} {v : Vector α n}
    (Hf : ∀ x, f x ≡{k}≡ g x) : v.map f ≡{k}≡ v.map g := by
  simp only [vec_dist_toList, Vector.toList_map]
  exact list_fmap_ext_ne Hf

@[rocq_alias vec_map_ne]
theorem vec_map_ne [OFE α] [OFE β] {k} {f g : α → β}
    (Hf : ∀ {a b}, a ≡{k}≡ b → f a ≡{k}≡ g b) {u v : Vector α n} (h : u ≡{k}≡ v) :
    u.map f ≡{k}≡ v.map g := by
  simp only [vec_dist_toList, Vector.toList_map]
  exact list_fmap_ne Hf (vec_dist_toList.mp h)

/-- The vector functor's action on morphisms: postcompose with `Vector.map`. -/
@[rocq_alias vecO_map]
def vecMap [OFE α] [OFE β] (f : α -n> β) : Vector α n -n> Vector β n where
  f := Vector.map f
  ne := ⟨fun _ _ _ h => vec_map_ne (fun hab => f.ne.ne hab) h⟩

@[simp] theorem vecMap_apply [OFE α] [OFE β] {f : α -n> β} {v : Vector α n} :
    vecMap f v = v.map f := rfl

@[rocq_alias vecO_map_ne]
instance vecMap_ne [OFE α] [OFE β] : NonExpansive (vecMap (α := α) (β := β) (n := n)) where
  ne _ _ _ h _ := vec_map_ext_ne fun x => h x

abbrev VecOF (F : OFunctorPre) (n : Nat) : OFunctorPre := fun A B _ _ => Vector (F A B) n

variable (F : OFunctorPre) (n : Nat)

@[rocq_alias vecOF]
instance oFunctorVec [OFunctor F] : OFunctor (VecOF F n) where
  ofe := _
  map f g := vecMap (OFunctor.map f g)
  map_ne.ne _ _ _ Hx _ _ Hy z :=
    vec_map_ext_ne (v := z) fun x => OFunctor.map_ne.ne Hx Hy x
  map_id z := Vector.toList_inj.mp <| by
    simp only [vecMap_apply, Vector.toList_map]
    exact OFunctor.map_id (F := ListOF F) z.toList
  map_comp f g f' g' z := Vector.toList_inj.mp <| by
    simp only [vecMap_apply, Vector.toList_map]
    exact OFunctor.map_comp (F := ListOF F) f g f' g' z.toList

@[rocq_alias vecOF_contractive]
instance [OFunctorContractive F] : OFunctorContractive (VecOF F n) where
  map_contractive.1 H z :=
    vec_map_ext_ne (v := z) fun x =>
      (OFunctorContractive.map_contractive (F := F)).distLater_dist H x

end functor

end Iris

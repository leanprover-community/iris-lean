/-
Copyright (c) 2025 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
import Iris.Algebra.OFE
import Iris.Algebra.CMRA
import Iris.Algebra.Updates

namespace Iris
open OFE

section GenMap

/- The OFE over gmaps is eqivalent to a non-depdenent discrete function to an `Option` type with a
`Leibniz` OFE of keys, and an infinite number of unallocated elements.

In this setting, the CMRA is always unital, and as a consquence the oFunctors do not require
unitality in order to act as a `URFunctor(Contractive)`.

GenMap is only intended to be used in the construction of the core IProp model. It is a stripped-down
version of the generic heap constructions, which you should use instead. -/

def alter [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun a' => if a = a' then b else f a'

structure Enum (P : α → Prop) (enum : Nat → α) : Prop where
  inc {n} : P (enum n)
  inj {n m} : enum n = enum m → n = m

def Poke [DecidableEq α] (enum : Nat → α) (n : Nat) : Nat → α :=
  fun n' => if n' < n then enum n' else enum (n' + 1)

def Infinite (P : α → Prop) : Prop := ∃ e, Enum P e

def IsFree {β : α → Type _} (f : (a : α) → Option (β a)) : α → Prop := fun a => f a = none

set_option grind.warning false
theorem alter_isFree_infinite [DecidableEq α] {f : α → Option β} (H : Infinite (IsFree f)) :
    Infinite (IsFree (alter f a b)) := by
  rcases H with ⟨enum, Henum_inc, Henum_inj⟩
  rcases Classical.em (∃ n₀, enum n₀ = a) with (⟨n₀, Hin⟩|Hout)
  · refine ⟨Poke enum n₀, @fun n => ?_, @fun n m => ?_⟩
    · simp [alter, IsFree]; split <;> rename_i h <;> revert h <;> simp [Poke]
      · split <;> intro H <;> specialize Henum_inj (Hin ▸ H) <;> omega
      · split <;> refine fun _ => Henum_inc
    · simp [Poke]
      split <;> split
      all_goals intro H <;> specialize Henum_inj H <;> grind
  · refine ⟨enum, @fun n => ?_, @fun n m Heq => ?_⟩
    · simp only [not_exists] at Hout; specialize Hout n
      simp only [IsFree, alter] at ⊢
      split
      · rename_i h; exact (Hout h.symm).elim
      · exact Henum_inc
    · exact Henum_inj Heq

theorem Infinite.mono {P Q : α → Prop} (H : Infinite P) (Hmono : ∀ a, P a → Q a) : Infinite Q := by
  rcases H with ⟨enum, Henum_inc, Henum_inj⟩
  exact ⟨enum, Hmono (enum _) Henum_inc, Henum_inj⟩

section GenMapImpl

-- abbrev GenMap := { f : α → Option β // Infinite (IsFree f) }
structure GenMap (α β : Type _) where
  car : α → Option β

nonrec def GenMap.alter [DecidableEq α] (g : GenMap α β) (a : α) (b : Option β) : GenMap α β where
  car := alter g.car a b

section OFE
variable (α β : Type _) [OFE β]

instance GenMap_instOFE : OFE (GenMap α β) where
  Equiv := (·.car ≡ ·.car)
  Dist n := (·.car ≡{n}≡ ·.car)
  dist_eqv.refl _ := Dist.of_eq rfl
  dist_eqv.symm := Dist.symm
  dist_eqv.trans := Dist.trans
  equiv_dist := equiv_dist
  dist_lt := Dist.lt
end OFE

section CMRA

variable (α β : Type _) [CMRA β]

-- NB. Could use actual subtypes, but I will first attempt to do the subtyping on validity alone
-- May make the OFunctors simpler because I just need to point them to GenMap instead
-- of writing something new.
-- Seems that the alter and alloc updates are still provable?
instance instCMRA_GenMap : CMRA (GenMap α β) where
  pcore x := Option.map GenMap.mk <| CMRA.pcore x.car
  op x y := GenMap.mk (x.car • y.car)
  ValidN n x := ✓{n} x.car ∧ (Infinite (IsFree x.car))
  Valid x := ✓ x.car ∧ (Infinite (IsFree x.car))
  op_ne.ne {_ _ _} H := CMRA.op_ne (α := α → Option β) |>.ne H
  pcore_ne {n x y cx} H Hm := by
    have Hm' : (CMRA.pcore x.car) = some cx.car := by
      rcases h : (CMRA.pcore x.car)
      · simp_all [h]
      · simp_all [h]
        rw [← Hm]
    have H' : x.car ≡{n}≡ y.car := by exact H
    rcases CMRA.pcore_ne H' Hm' with ⟨cy', Hcy'1, Hcy'2⟩
    exact ⟨⟨cy'⟩, by simp [Hcy'1], Hcy'2⟩
  validN_ne {n x y H} := by
    refine fun ⟨Hv, ⟨e, Hf, Hi⟩⟩ => ⟨Dist.validN H |>.mp Hv, ?_⟩
    refine ⟨e, @fun n => ?_, Hi⟩
    specialize H (e n); specialize @Hf n; revert H Hf
    cases _ : x.car (e n) <;> cases _ : y.car (e n) <;>
    simp_all [IsFree, OFE.Dist, Option.Forall₂]
  valid_iff_validN {x} := by
    refine ⟨fun ⟨Hv, Hi⟩ n => ⟨Hv.validN, Hi⟩, fun H => ⟨?_, H 0 |>.2⟩⟩
    exact CMRA.valid_iff_validN.mpr (H · |>.1)
  validN_succ {x n} := fun ⟨Hv, Hi⟩ => ⟨CMRA.validN_succ Hv, Hi⟩
  validN_op_left {n x y} := by
    simp; rintro Hv Hf
    refine ⟨CMRA.validN_op_left Hv, ?_⟩
    refine Infinite.mono Hf (fun a => ?_)
    simp [IsFree, CMRA.op, optionOp]
    cases _ : x.car a <;> cases _ : y.car a  <;> simp
  assoc {x y z} a := by
    cases _ : x.car a <;> cases _ : y.car a <;> cases _ : z.car a <;>
      simp_all [CMRA.op, OFE.Equiv, Option.Forall₂, optionOp]
    exact CMRA.assoc
  comm {x y} a := by
    cases _ : x.car a <;> cases _ : y.car a <;>
      simp_all [CMRA.op, OFE.Equiv, Option.Forall₂, optionOp]
    exact CMRA.comm
  pcore_op_left {x cx} H := by
    rcases x with ⟨x⟩; rcases cx with ⟨cx⟩
    have _ := CMRA.pcore_op_left (x := x) (cx := cx)
    simp_all [OFE.Equiv]
  pcore_idem {x cx} H := by
    rcases x with ⟨x⟩; rcases cx with ⟨cx⟩
    simp_all [OFE.Equiv, Option.Forall₂, Option.map]
    apply CMRA.pcore_idem (x := x) (cx := cx)
    simp [CMRA.pcore, H]
  pcore_op_mono {x cx} := by
    rcases x with ⟨x⟩; rcases cx with ⟨cx⟩; simp
    refine fun H ⟨y⟩ => ?_
    rcases CMRA.pcore_op_mono (x := x) (cx := cx) H y with ⟨cy, Hcy⟩
    refine ⟨.mk cy, Hcy⟩
  extend {n x y1 y2} := by
    rintro ⟨Hv, _⟩ H
    rcases CMRA.extend Hv H with ⟨z1, z2, _, _, _⟩
    exists .mk z1
    exists .mk z2

instance instUCMRA_GenMap : UCMRA (GenMap Nat β) where
  unit := GenMap.mk <| UCMRA.unit
  unit_valid := ⟨fun _ => trivial, ⟨id, rfl, id⟩⟩
  unit_left_id := by simp [CMRA.op, UCMRA.unit, optionOp]
  pcore_unit := by simp [CMRA.pcore, UCMRA.unit, CMRA.core, optionCore]

theorem GenMap.alter_valid [DecidableEq α] {g : GenMap α β} (Hb : ✓{n} b) (Hg : ✓{n} g) :
    ✓{n} g.alter a b := by
  rcases g with ⟨g⟩ <;> simp [GenMap.alter]
  rcases Hg with ⟨Hv, Hi⟩
  refine ⟨fun _ => ?_, alter_isFree_infinite Hi⟩
  simp [Iris.alter] <;> split
  · exact Hb
  · exact Hv _

theorem GenMap.valid_exists_fresh {g : GenMap α β} (Hv : ✓{n} g) : ∃ a : α, g.car a = none := by
  rcases Hv with ⟨_, e, He_inc, _⟩
  exact ⟨e 0, He_inc⟩

end CMRA

section OFunctors
open COFE

abbrev GenMapOF (C : Type _) (F : OFunctorPre) : OFunctorPre :=
  fun A B _ _ => GenMap C (F A B)

abbrev GenMap.lift [OFE α] [OFE β] (f : α -n> β) : GenMap T α -n> GenMap T β where
  f g := .mk fun t => Option.map f (g.car t)
  ne.ne {n x1 x2} H γ := by
    specialize H γ
    simp [Option.map]
    split <;> split <;> simp_all
    exact NonExpansive.ne H

instance GenMapOF_instOFunctor (F : OFunctorPre) [OFunctor F] :
    OFunctor (GenMapOF Nat F) where
  cofe {A B _ _} := GenMap_instOFE Nat (F A B)
  map f₁ f₂ := GenMap.lift <| OFunctor.map (F := F) f₁ f₂
  map_ne.ne {n x1 x2} Hx {y1 y2} Hy k γ := by
    simp only [OFE.Dist, Option.Forall₂, Option.map]
    cases _ : k.car γ <;> simp
    exact OFunctor.map_ne.ne Hx Hy _
  map_id {α β _ _} x γ := by
    simp only [Option.map]
    cases _ : x.car γ <;> simp
    exact OFunctor.map_id _
  map_comp _ _ _ _ x γ := by
    simp only [Option.map]
    cases _ : x.car γ <;> simp
    exact OFunctor.map_comp _ _ _ _ _

-- TODO: Cleanup
instance GenMapOF_instURFunctor (F : COFE.OFunctorPre) [RFunctor F] :
    URFunctor (GenMapOF Nat F) where
  map f g := {
    toHom := GenMap.lift <| COFE.OFunctor.map f g
    validN {n x} hv := by
      rcases hv with ⟨hv, ⟨e, Hf, Hi⟩⟩
      refine ⟨fun z => ?_, ⟨e, @fun n => ?_, Hi⟩⟩
      · cases h : x.car z <;> simp [Option.map, CMRA.ValidN, optionValidN, h]
        rename_i _ α₁ α₂ β₁ β₂ _ _ _ _ v
        let Hvalid := @(URFunctor.map (F := OptionOF F) f g).validN n v
        simp [CMRA.ValidN, optionValidN, h, URFunctor.map] at Hvalid
        specialize Hvalid ?_
        · specialize hv z
          simp [CMRA.ValidN, optionValidN] at hv
          simp [h] at hv
          exact hv
        exact Hvalid
      · specialize @Hf n
        simp [IsFree, Option.map] at Hf ⊢
        simp [Hf]
    pcore x γ := by
      let Hcore := @(URFunctor.map (F := OptionOF F) f g).pcore (x.car γ)
      simp [Option.map] at Hcore ⊢
      cases h : (x.car γ) <;> simp [CMRA.core, Option.getD, optionCore] at Hcore ⊢
      rename_i v
      simp [OFE.Equiv, Option.Forall₂, URFunctor.map, Option.bind, h, optionCore, OFunctor.map, optionMap, Option.map] at Hcore
      cases h' : CMRA.pcore v
      · simp_all [h']
        cases h'' : CMRA.pcore ((OFunctor.map f g).f v) <;> simp_all
        simp_all [RFunctor.toOFunctor]
      · simp_all [h']
        cases h'' : CMRA.pcore ((OFunctor.map f g).f v) <;> simp_all [RFunctor.toOFunctor]
    op z x γ := by
      let Hop := @(URFunctor.map (F := OptionOF F) f g).op (z.car γ) (x.car γ)
      simp [Option.map, RFunctor.toOFunctor, optionCore, CMRA.op, optionOp, Option.bind,
           URFunctor.map] at Hop ⊢
      cases h : z.car γ <;> cases h' : x.car γ <;> simp
      simp [h, h'] at Hop
      simp_all [OFunctor.map, optionMap, RFunctor.toOFunctor]
  }
  map_ne.ne := COFE.OFunctor.map_ne.ne
  map_id := COFE.OFunctor.map_id
  map_comp := COFE.OFunctor.map_comp

instance GenMapOF_instURFC (F : COFE.OFunctorPre) [HURF : RFunctorContractive F] :
    URFunctorContractive (GenMapOF Nat F) where
  map_contractive.1 h x n := by
    rename_i n x' y'
    let Heqv := @(URFunctorContractive.map_contractive (F := OptionOF F)).1 _ x' y' h (x.car n)
    simp [Function.uncurry, URFunctor.map, Option.map] at Heqv ⊢
    cases h : x.car n <;> simp
    rw [h] at Heqv
    exact Heqv

end OFunctors

section updates

-- Which gmap updates do we need?

end updates


/-
Lemma insert_updateP (P : A → Prop) (Q : gmap K A → Prop) m i x :
  x ~~>: P →
  (∀ y, P y → Q (<[i:=y]>m)) →
  <[i:=x]>m ~~>: Q.
Proof.
  intros Hx%option_updateP' HP; apply cmra_total_updateP=> n mf Hm.
  destruct (Hx n (Some (mf !! i))) as ([y|]&?&?); try done.
  { by generalize (Hm i); rewrite lookup_op; simplify_map_eq. }
  exists (<[i:=y]> m); split; first by auto.
  intros j; move: (Hm j)=>{Hm}; rewrite !lookup_op=>Hm.
  destruct (decide (i = j)); simplify_map_eq/=; auto.
Qed.
Lemma insert_updateP' (P : A → Prop) m i x :
  x ~~>: P → <[i:=x]>m ~~>: λ m', ∃ y, m' = <[i:=y]>m ∧ P y.
Proof. eauto using insert_updateP. Qed.
Lemma insert_update m i x y : x ~~> y → <[i:=x]>m ~~> <[i:=y]>m.
Proof. rewrite !cmra_update_updateP; eauto using insert_updateP with subst. Qed.

Lemma singleton_updateP (P : A → Prop) (Q : gmap K A → Prop) i x :
  x ~~>: P → (∀ y, P y → Q {[ i := y ]}) → {[ i := x ]} ~~>: Q.
Proof. apply insert_updateP. Qed.
Lemma singleton_updateP' (P : A → Prop) i x :
  x ~~>: P → {[ i := x ]} ~~>: λ m, ∃ y, m = {[ i := y ]} ∧ P y.
Proof. apply insert_updateP'. Qed.
Lemma singleton_update i (x y : A) : x ~~> y → {[ i := x ]} ~~> {[ i := y ]}.
Proof. apply insert_update. Qed.

Lemma delete_update m i : m ~~> delete i m.
Proof.
  apply cmra_total_update=> n mf Hm j; destruct (decide (i = j)); subst.
  - move: (Hm j). rewrite !lookup_op lookup_delete_eq left_id.
    apply cmra_validN_op_r.
  - move: (Hm j). by rewrite !lookup_op lookup_delete_ne.
Qed.





Section freshness.
  Local Set Default Proof Using "Type*".
  Context `{!Infinite K}.
  Lemma alloc_updateP_strong_dep (Q : gmap K A → Prop) (I : K → Prop) m (f : K → A) :
    pred_infinite I →
    (∀ i, m !! i = None → I i → ✓ (f i)) →
    (∀ i, m !! i = None → I i → Q (<[i:=f i]>m)) → m ~~>: Q.
  Proof.
    move=> /(pred_infinite_set I (C:=gset K)) HP ? HQ.
    apply cmra_total_updateP. intros n mf Hm.
    destruct (HP (dom (m ⋅ mf))) as [i [Hi1 Hi2]].
    assert (m !! i = None).
    { eapply not_elem_of_dom. revert Hi2.
      rewrite dom_op not_elem_of_union. naive_solver. }
    exists (<[i:=f i]>m); split.
    - by apply HQ.
    - rewrite insert_singleton_op //.
      rewrite -assoc -insert_singleton_op; last by eapply not_elem_of_dom.
    apply insert_validN; [apply cmra_valid_validN|]; auto.
  Qed.
  Lemma alloc_updateP_strong (Q : gmap K A → Prop) (I : K → Prop) m x :
    pred_infinite I →
    ✓ x → (∀ i, m !! i = None → I i → Q (<[i:=x]>m)) → m ~~>: Q.
  Proof.
    move=> HP ? HQ. eapply (alloc_updateP_strong_dep _ _ _ (λ _, x)); eauto.
  Qed.
  Lemma alloc_updateP (Q : gmap K A → Prop) m x :
    ✓ x → (∀ i, m !! i = None → Q (<[i:=x]>m)) → m ~~>: Q.
  Proof.
    move=>??.
    eapply (alloc_updateP_strong _ (λ _, True));
    eauto using pred_infinite_True.
  Qed.
  Lemma alloc_updateP_cofinite (Q : gmap K A → Prop) (J : gset K) m x :
    ✓ x → (∀ i, m !! i = None → i ∉ J → Q (<[i:=x]>m)) → m ~~>: Q.
  Proof.
    eapply alloc_updateP_strong.
    apply (pred_infinite_set (C:=gset K)).
    intros E. exists (fresh (J ∪ E)).
    apply not_elem_of_union, is_fresh.
  Qed.

  (* Variants without the universally quantified Q, for use in case that is an evar. *)
  Lemma alloc_updateP_strong_dep' m (f : K → A) (I : K → Prop) :
    pred_infinite I →
    (∀ i, m !! i = None → I i → ✓ (f i)) →
    m ~~>: λ m', ∃ i, I i ∧ m' = <[i:=f i]>m ∧ m !! i = None.
  Proof. eauto using alloc_updateP_strong_dep. Qed.
  Lemma alloc_updateP_strong' m x (I : K → Prop) :
    pred_infinite I →
    ✓ x → m ~~>: λ m', ∃ i, I i ∧ m' = <[i:=x]>m ∧ m !! i = None.
  Proof. eauto using alloc_updateP_strong. Qed.
  Lemma alloc_updateP' m x :
    ✓ x → m ~~>: λ m', ∃ i, m' = <[i:=x]>m ∧ m !! i = None.
  Proof. eauto using alloc_updateP. Qed.
  Lemma alloc_updateP_cofinite' m x (J : gset K) :
    ✓ x → m ~~>: λ m', ∃ i, i ∉ J ∧ m' = <[i:=x]>m ∧ m !! i = None.
  Proof. eauto using alloc_updateP_cofinite. Qed.
End freshness.

Lemma alloc_unit_singleton_updateP (P : A → Prop) (Q : gmap K A → Prop) u i :
  ✓ u → LeftId (≡) u (⋅) →
  u ~~>: P → (∀ y, P y → Q {[ i := y ]}) → ∅ ~~>: Q.
Proof.
  intros ?? Hx HQ. apply cmra_total_updateP=> n gf Hg.
  destruct (Hx n (gf !! i)) as (y&?&Hy).
  { move:(Hg i). rewrite !left_id.
    case: (gf !! i)=>[x|]; rewrite /= ?left_id //.
    intros; by apply cmra_valid_validN. }
  exists {[ i := y ]}; split; first by auto.
  intros i'; destruct (decide (i' = i)) as [->|].
  - rewrite lookup_op lookup_singleton_eq.
    move:Hy; case: (gf !! i)=>[x|]; rewrite /= ?right_id //.
  - move:(Hg i'). by rewrite !lookup_op lookup_singleton_ne // !left_id.
Qed.
Lemma alloc_unit_singleton_updateP' (P: A → Prop) u i :
  ✓ u → LeftId (≡) u (⋅) →
  u ~~>: P → ∅ ~~>: λ m, ∃ y, m = {[ i := y ]} ∧ P y.
Proof. eauto using alloc_unit_singleton_updateP. Qed.
Lemma alloc_unit_singleton_update (u : A) i (y : A) :
  ✓ u → LeftId (≡) u (⋅) → u ~~> y → (∅:gmap K A) ~~> {[ i := y ]}.
Proof.
  rewrite !cmra_update_updateP;
    eauto using alloc_unit_singleton_updateP with subst.
Qed.
-/

-- def GenMapOF (C : Type _) (F : C → COFE.OFunctorPre) : COFE.OFunctorPre :=
--   fun A B => { f : (c : C) → OptionOF (F c) A B // Infinite (IsFree f) }

-- TODO: CMRA instances, updates for alloc + modify, urFunctor instance for when F is always an rFunctor
-- Functor merges
--    urFunctorOptionOF [RFunctor F] : URFunctor (OptionOF F) where
-- instance urFunctorContractiveOptionOF [RFunctorContractive F] : URFunctorContractive (OptionOF F) where
--    DiscreteFunOF_URFC {C} (F : C → COFE.OFunctorPre) [HURF : ∀ c, URFunctorContractive (F c)] :
-- So it should expect ∀ c, (RFunctorContractive c)

-- instance instURFunctor_GenMapOF {F : C → COFE.OFunctorPre} [∀ c, RFunctorContractive (F c)] :
--     URFunctor (GenMapOF C F) :=
--   sorry

end GenMapImpl

end GenMap

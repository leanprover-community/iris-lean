module

public import Iris

@[expose] public section

open Iris OFE

namespace IrisMath

/-! # Inverse limits of OFEs

This module exposes the projective (inverse) limit of a `Nat`-indexed tower of OFEs.
A **tower** consists of:

* a family `carrier : Nat → Type _` of carriers,
* an OFE structure on each `carrier n`,
* non-expansive *transition* (or *projection*) maps `proj n : carrier (n+1) -n> carrier n`.

The *inverse limit* of a tower is the OFE of *compatible families*: functions
`x : (n : Nat) → carrier n` such that `proj n (x (n+1)) ≡ x n`. We equip it with the
pointwise OFE structure inherited level-wise from the tower. When each level is
already complete (a `COFE`), the inverse limit itself becomes a `COFE` by taking
the completion at each level — completion commutes with the non-expansive
transition maps, so the limit family remains compatible.

This is the structural core that subsumes many concrete step-indexed constructions,
e.g. formal power series (every truncation level is a finite-dimensional vector space),
`p`-adic integers, or profinite groups. The pointwise dist plays well with OFE-valued
levels — the alternative "truncation" dist (agree on levels strictly below the step)
only makes sense when each level is discrete.
-/

/-- A `Nat`-indexed tower of OFEs with non-expansive transition maps. The data is a
family of carriers, their OFE instances, and transition maps `proj n : carrier (n+1) -n>
carrier n`. -/
structure Tower where
  /-- The carrier type at each tower level. -/
  carrier : Nat → Type _
  /-- The OFE instance at each tower level. -/
  ofe : ∀ n, OFE (carrier n)
  /-- The non-expansive transition map from level `n+1` down to level `n`. -/
  proj : ∀ n, @Hom (carrier (n + 1)) (carrier n) (ofe (n + 1)) (ofe n)

attribute [instance] Tower.ofe

/-- A *compatible family* over a tower: a section `x : (n : Nat) → carrier n` satisfying
the projective compatibility condition `proj n (x (n+1)) ≡ x n` at every level. -/
def InverseLimit (T : Tower) : Type _ :=
  { x : (n : Nat) → T.carrier n // ∀ n, T.proj n (x (n + 1)) ≡ x n }

namespace InverseLimit

variable {T : Tower}

/-- The underlying section of a compatible family. -/
def val (x : InverseLimit T) : (n : Nat) → T.carrier n := x.1

/-- The compatibility witness of a compatible family. -/
theorem compat (x : InverseLimit T) (n : Nat) : T.proj n (x.val (n + 1)) ≡ x.val n :=
  x.2 n

/-- Smart constructor: package a section and its compatibility proof as an element of the
inverse limit. -/
@[simp] def mk (x : (n : Nat) → T.carrier n) (h : ∀ n, T.proj n (x (n + 1)) ≡ x n) :
    InverseLimit T := ⟨x, h⟩

@[simp] theorem val_mk (x : (n : Nat) → T.carrier n)
    (h : ∀ n, T.proj n (x (n + 1)) ≡ x n) (n : Nat) :
    (mk x h).val n = x n := rfl

/-- Two elements of the inverse limit are equal iff their underlying sections agree at
every level. -/
@[ext] theorem ext {x y : InverseLimit T} (h : ∀ n, x.val n = y.val n) : x = y :=
  Subtype.ext (funext h)

/-! ## Pointwise OFE -/

/-- The pointwise OFE on the inverse limit: equivalence and `n`-equivalence are taken
level-wise in the underlying tower. -/
instance instOFE : OFE (InverseLimit T) where
  Equiv x y := ∀ n, x.val n ≡ y.val n
  Dist k x y := ∀ n, x.val n ≡{k}≡ y.val n
  dist_eqv := {
    refl _ _ := Dist.rfl
    symm h n := (h n).symm
    trans h₁ h₂ n := (h₁ n).trans (h₂ n)
  }
  equiv_dist := by
    refine ⟨fun h k n ↦ (h n).dist, fun h n ↦ ?_⟩
    exact equiv_dist.mpr fun k ↦ h k n
  dist_lt h hmn n := (h n).lt hmn

/-- Unfolding lemma for `Dist` on `InverseLimit`. -/
theorem dist_iff {k : Nat} {x y : InverseLimit T} :
    (x ≡{k}≡ y) ↔ ∀ n, x.val n ≡{k}≡ y.val n := Iff.rfl

/-- Unfolding lemma for `Equiv` on `InverseLimit`. -/
theorem equiv_iff {x y : InverseLimit T} : (x ≡ y) ↔ ∀ n, x.val n ≡ y.val n := Iff.rfl

/-- Level-`n` projection out of the inverse limit, packaged as a non-expansive map. -/
def levelHom (n : Nat) : InverseLimit T -n> T.carrier n where
  f x := x.val n
  ne.ne _ _ _ h := h n

@[simp] theorem levelHom_apply (n : Nat) (x : InverseLimit T) : levelHom n x = x.val n := rfl

/-- Compatibility of the level projections: composing `levelHom (n+1)` with the tower
transition `T.proj n` is equivalent to `levelHom n`. This is exactly the inverse-limit
compatibility condition, packaged as a functional equation. -/
theorem proj_levelHom (n : Nat) (x : InverseLimit T) :
    T.proj n (levelHom (n + 1) x) ≡ levelHom n x :=
  x.compat n

/-! ### Smart constructor for non-expansive maps *into* the inverse limit

Given a family `f : ∀ n, β -n> T.carrier n` whose components are compatible with the
tower transitions — i.e. `T.proj n (f (n+1) b) ≡ f n b` for every `b : β` — we get a
non-expansive map `β -n> InverseLimit T`. The universal property of the projective
limit, dressed in concrete OFE clothing. -/

/-- Non-expansive smart constructor: assemble a non-expansive map into the inverse limit
from a compatible family of non-expansive maps into the levels. -/
def mkHom {β : Type _} [OFE β] (f : ∀ n, β -n> T.carrier n)
    (h : ∀ n b, T.proj n (f (n + 1) b) ≡ f n b) : β -n> InverseLimit T where
  f b := ⟨fun n ↦ f n b, fun n ↦ h n b⟩
  ne.ne _ _ _ hxy n := (f n).ne.ne hxy

@[simp] theorem mkHom_apply_val {β : Type _} [OFE β] (f : ∀ n, β -n> T.carrier n)
    (h : ∀ n b, T.proj n (f (n + 1) b) ≡ f n b) (b : β) (n : Nat) :
    (mkHom f h b).val n = f n b := rfl

@[simp] theorem levelHom_comp_mkHom {β : Type _} [OFE β] (f : ∀ n, β -n> T.carrier n)
    (h : ∀ n b, T.proj n (f (n + 1) b) ≡ f n b) (n : Nat) (b : β) :
    levelHom n (mkHom f h b) = f n b := rfl

/-! ## COFE structure when each level is complete

If every `T.carrier n` is already a `COFE`, the inverse limit completes a chain
level-wise. The level-`n` completion is the `IsCOFE.compl` of the chain
`fun k ↦ (c k).val n`, which is Cauchy because `c` is. Compatibility of the resulting
section follows from the fact that `T.proj n` is non-expansive, hence commutes with
completion (`COFE.compl_map`).
-/

variable [hcofe : ∀ n, IsCOFE (T.carrier n)]

/-- For a chain `c` of compatible families and a tower level `n`, the level-`n`
slice `fun k ↦ (c k).val n` forms a chain in `T.carrier n`. -/
def levelChain (c : Chain (InverseLimit T)) (n : Nat) : Chain (T.carrier n) where
  chain k := (c.chain k).val n
  cauchy h := c.cauchy h n

omit hcofe in
@[simp] theorem levelChain_apply (c : Chain (InverseLimit T)) (n k : Nat) :
    (levelChain c n).chain k = (c.chain k).val n := rfl

/-- The level-`n` completion of a chain `c` of compatible families. -/
def levelCompl (c : Chain (InverseLimit T)) (n : Nat) : T.carrier n :=
  IsCOFE.compl (levelChain c n)

/-- The candidate section of the chain completion of `c`, taken level-wise. -/
def chainSection (c : Chain (InverseLimit T)) : (n : Nat) → T.carrier n :=
  fun n ↦ levelCompl c n

/-- Compatibility of `chainSection`: applying `T.proj n` to the level-`(n+1)`
completion gives the level-`n` completion, up to equivalence. This follows from
`COFE.compl_map` plus level-wise compatibility of each `c.chain k`. -/
theorem chainSection_compat (c : Chain (InverseLimit T)) (n : Nat) :
    T.proj n (chainSection c (n + 1)) ≡ chainSection c n := by
  -- We use that `compl` commutes with non-expansive maps, plus pointwise compatibility:
  -- `T.proj n ∘ (levelChain c (n+1))` agrees pointwise (under `≡`) with `levelChain c n`.
  refine Equiv.trans (COFE.compl_map (T.proj n) (levelChain c (n + 1))).symm ?_
  -- Now: `IsCOFE.compl (Chain.map (T.proj n) (levelChain c (n+1))) ≡ levelCompl c n`.
  -- We prove this from the `equiv_dist` characterisation, level by chain-step.
  refine equiv_dist.mpr fun k ↦ ?_
  -- Use that both completions are `k`-equivalent to the `k`-th chain entry, and the
  -- `k`-th entries are level-wise compatible.
  refine Dist.trans IsCOFE.conv_compl ?_
  refine Dist.trans ?_ IsCOFE.conv_compl.symm
  -- Goal: `T.proj n ((levelChain c (n+1)).chain k) ≡{k}≡ (levelChain c n).chain k`
  -- which is `T.proj n ((c.chain k).val (n+1)) ≡{k}≡ (c.chain k).val n`. This is the
  -- compatibility of `c.chain k` at level `n`, distilled to `Dist k`.
  exact ((c.chain k).compat n).dist

/-- The completion of a chain `c` of compatible families, taken level-wise. -/
def chainCompl (c : Chain (InverseLimit T)) : InverseLimit T :=
  ⟨chainSection c, chainSection_compat c⟩

@[simp] theorem chainCompl_val (c : Chain (InverseLimit T)) (n : Nat) :
    (chainCompl c).val n = IsCOFE.compl (levelChain c n) := rfl

/-- The inverse limit of a tower of COFEs is itself a COFE, with completion taken
level-wise. -/
instance instIsCOFE : IsCOFE (InverseLimit T) where
  compl := chainCompl
  conv_compl {_ c} k := IsCOFE.conv_compl (c := levelChain c k)

end InverseLimit

/-! ## Concrete examples -/

/-- The trivial tower: every level is `Unit`, with the unique transition map. -/
def unitTower : Tower where
  carrier _ := Unit
  ofe _ := inferInstance
  proj _ := ⟨fun _ ↦ (), ⟨fun _ _ _ _ ↦ trivial⟩⟩

/-- The inverse limit of the trivial tower is (equivalent to) `Unit`. We exhibit the
canonical compatible family: the constantly-`()` section. -/
def unitInverseLimit : InverseLimit unitTower :=
  ⟨fun _ ↦ (), fun _ ↦ Equiv.rfl⟩

/-- Any two elements of the trivial inverse limit are equivalent. -/
theorem unitInverseLimit_subsingleton (x y : InverseLimit unitTower) : x ≡ y :=
  fun _ ↦ Equiv.rfl

/-- The *constant* tower at a single OFE `α`: every level is `α` and every transition
is the identity. Compatible families are then sequences `x : Nat → α` with `x (n+1) ≡ x n`,
i.e. eventually-equivalent sequences. -/
def constTower (α : Type _) [OFE α] : Tower where
  carrier _ := α
  ofe _ := inferInstance
  proj _ := Hom.id

/-- Any element `a : α` gives rise to a constantly-`a` compatible family in the constant
tower. -/
def constInverseLimit {α : Type _} [OFE α] (a : α) : InverseLimit (constTower α) :=
  ⟨fun _ ↦ a, fun _ ↦ Equiv.rfl⟩

/-- The *product* of two towers, level by level. The transition at level `n` is the
pairwise transition of the components. This exhibits the category of towers as closed
under finite products, and shows `InverseLimit` interacts well with products. -/
def prodTower (S T : Tower) : Tower where
  carrier n := S.carrier n × T.carrier n
  ofe _ := inferInstance
  proj n :=
    { f := fun p ↦ (S.proj n p.1, T.proj n p.2)
      ne.ne _ _ _ h := ⟨(S.proj n).ne.ne h.1, (T.proj n).ne.ne h.2⟩ }

/-- A compatible family in the product tower is canonically built from a pair of
compatible families, one in each factor. -/
def prodInverseLimit {S T : Tower} (x : InverseLimit S) (y : InverseLimit T) :
    InverseLimit (prodTower S T) :=
  ⟨fun n ↦ (x.val n, y.val n), fun n ↦ ⟨x.compat n, y.compat n⟩⟩

end IrisMath

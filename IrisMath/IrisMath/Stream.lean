module

public import Iris

@[expose] public section

open Iris OFE

namespace IrisMath.Stream

/-! # Infinite streams as OFEs / COFEs

This module exposes infinite streams `Nat → α` (the Cantor / Baire style spaces) as Iris
`OFE`s and `COFE`s with respect to the canonical truncation metric: two streams are
`n`-equivalent iff their first `n` entries are `n`-equivalent in `α`.

We give the construction for an arbitrary base OFE `α` (`StreamO α`), and then specialise
to the Cantor space `Nat → Bool` and the Baire space `Nat → Nat` (each via a `LeibnizO`
wrapper so the entries form a discrete OFE).
-/

/-- The type of infinite streams `Nat → α`, viewed as the underlying type of the truncation
OFE described in the module docstring. -/
abbrev StreamO (α : Type _) [OFE α] : Type _ := Nat → α

namespace StreamO

variable {α : Type _} [OFE α]

/-- Truncation OFE on streams: `n`-equivalence requires the first `n` entries to agree
up to `n`-equivalence in the base OFE. -/
instance instOFE : OFE (StreamO α) where
  Equiv x y := ∀ k, x k ≡ y k
  Dist n x y := ∀ k, k < n → x k ≡{n}≡ y k
  dist_eqv := {
    refl _ _ _ := Dist.rfl
    symm h k hk := (h k hk).symm
    trans h₁ h₂ k hk := (h₁ k hk).trans (h₂ k hk)
  }
  equiv_dist := by
    refine ⟨fun h _ k _ ↦ (h k).dist, fun h k ↦ ?_⟩
    refine equiv_dist.mpr fun n ↦ ?_
    rcases Nat.lt_or_ge k n with hk | hk
    · exact h n k hk
    · exact (h (k + 1) k (Nat.lt_succ_self k)).le (Nat.le_succ_of_le hk)
  dist_lt h hmn k hk := (h k (Nat.lt_trans hk hmn)).lt hmn

/-- Unfolding lemma for `Dist` on `StreamO`. -/
theorem dist_iff {n : Nat} {x y : StreamO α} :
    (x ≡{n}≡ y) ↔ ∀ k, k < n → x k ≡{n}≡ y k := Iff.rfl

/-- Unfolding lemma for `Equiv` on `StreamO`. -/
theorem equiv_iff {x y : StreamO α} : (x ≡ y) ↔ ∀ k, x k ≡ y k := Iff.rfl

section COFE
variable [IsCOFE α]

/-- The chain of entries at coordinate `k`, shifted so that the chain Cauchy property
holds at every level: the `i`-th element is the `k`-th entry of `c (i + k + 1)`. The
shift by `k + 1` ensures `k < i + k + 1`, so the chain Cauchy property of `c` at level
`i + k + 1` constrains the `k`-th entry. -/
def levelChain (c : Chain (StreamO α)) (k : Nat) : Chain α where
  chain i := c.chain (i + k + 1) k
  cauchy {n i} h := by
    -- `n ≤ i`, hence `n + k + 1 ≤ i + k + 1`, so `c.chain (i+k+1) ≡{n+k+1}≡ c.chain (n+k+1)`.
    have hle : n + k + 1 ≤ i + k + 1 := by
      have : n + k ≤ i + k := Nat.add_le_add_right h k
      exact Nat.succ_le_succ this
    have hcauchy : c.chain (i + k + 1) ≡{n + k + 1}≡ c.chain (n + k + 1) := c.cauchy hle
    have hk : k < n + k + 1 := Nat.lt_succ_of_le (Nat.le_add_left k n)
    exact (hcauchy k hk).le (Nat.le_succ_of_le (Nat.le_add_right n k))

omit [IsCOFE α] in
/-- Unfolding lemma for the chain entries of `levelChain`. -/
@[simp] theorem levelChain_chain (c : Chain (StreamO α)) (k i : Nat) :
    (levelChain (α := α) c k).chain i = c.chain (i + k + 1) k := rfl

/-- The diagonal completion of a chain of streams: the `k`-th entry of the limit is the
completion (in the base COFE) of the chain of `k`-th entries. -/
def chainCompl (c : Chain (StreamO α)) : StreamO α := fun k ↦ IsCOFE.compl (levelChain c k)

/-- Evaluation of the diagonal completion at a coordinate. -/
theorem chainCompl_apply (c : Chain (StreamO α)) (k : Nat) :
    chainCompl c k = IsCOFE.compl (levelChain c k) := rfl

/-- The truncation OFE on streams over a COFE is itself a COFE. -/
instance instIsCOFE : IsCOFE (StreamO α) where
  compl := chainCompl
  conv_compl {n c} k hk := by
    -- `chainCompl c k = compl (levelChain c k)`; want this `≡{n}≡ c.chain n k`.
    show IsCOFE.compl (levelChain c k) ≡{n}≡ c.chain n k
    -- Use `conv_compl` of the base COFE at level `n`, then collapse to coordinate `k`.
    refine (IsCOFE.conv_compl (n := n) (c := levelChain c k)).trans ?_
    -- `levelChain c k n = c.chain (n + k + 1) k`; compare with `c.chain n k`.
    show c.chain (n + k + 1) k ≡{n}≡ c.chain n k
    have hle : n ≤ n + k + 1 := Nat.le_succ_of_le (Nat.le_add_right n k)
    have hcauchy : c.chain (n + k + 1) ≡{n}≡ c.chain n := c.cauchy hle
    exact hcauchy k hk

end COFE

/-! ### Stream constructors and projections -/

/-- Prepend an element to the front of a stream, shifting the original entries up by one. -/
def cons (a : α) (s : StreamO α) : StreamO α
  | 0 => a
  | k + 1 => s k

@[simp] theorem cons_zero (a : α) (s : StreamO α) : cons a s 0 = a := rfl

@[simp] theorem cons_succ (a : α) (s : StreamO α) (k : Nat) : cons a s (k + 1) = s k := rfl

/-- Prepending a fixed head is non-expansive in the tail: agreement of the tails at level
`n` propagates to agreement of the prepended streams at level `n`. -/
instance cons_nonExpansive (a : α) : NonExpansive (cons a) where
  ne {n x y} h k hk := by
    cases k with
    | zero => exact Dist.rfl
    | succ k => exact h k (Nat.lt_of_succ_lt hk)

/-- Over a discrete base OFE, `cons a` is contractive: agreement of the tails at every
strictly smaller level suffices for agreement of the prepended streams at level `n`. This
mirrors the canonical contractive prepend operation on processes. -/
instance cons_contractive [Discrete α] (a : α) : Contractive (cons a) where
  distLater_dist {n x y} h k hk := by
    cases k with
    | zero => exact Dist.rfl
    | succ k =>
      have hxy : x ≡{k + 1}≡ y := h (k + 1) hk
      exact Discrete.discrete_n ((hxy k (Nat.lt_succ_self _)).le (Nat.zero_le _))

/-- The tail of a stream, shifting every entry down by one. -/
def tail (s : StreamO α) : StreamO α := fun k ↦ s (k + 1)

@[simp] theorem tail_apply (s : StreamO α) (k : Nat) : tail s k = s (k + 1) := rfl

/-- Shifting decreases the available step-index by one: from agreement at level `n + 1`
of the original streams one obtains agreement at level `n` of the tails. -/
theorem tail_dist_of_dist_succ {n : Nat} {x y : StreamO α} (h : x ≡{n + 1}≡ y) :
    tail x ≡{n}≡ tail y :=
  fun k hk ↦ (h (k + 1) (Nat.succ_lt_succ hk)).lt (Nat.lt_succ_self _)

/-- The constant stream with every entry equal to `a`. -/
def const (a : α) : StreamO α := fun _ ↦ a

@[simp] theorem const_apply (a : α) (k : Nat) : const a k = a := rfl

/-- The constant-stream constructor is non-expansive in its argument. -/
instance const_nonExpansive : NonExpansive (const (α := α)) where
  ne _ _ _ h _ _ := h

end StreamO

/-! ## Cantor space `Nat → Bool` -/

/-- The Cantor space `Nat → Bool`, viewed as the underlying type of the truncation OFE on
infinite bit-streams. Entries are wrapped in `LeibnizO` so they form a discrete OFE. -/
abbrev Cantor : Type := StreamO (LeibnizO Bool)

namespace Cantor

/-- Cantor `n`-equivalence is plain equality of the first `n` bits. -/
theorem dist_iff {n : Nat} {x y : Cantor} :
    (x ≡{n}≡ y) ↔ ∀ k, k < n → (x k).car = (y k).car := by
  refine ⟨fun h k hk ↦ LeibnizO.dist_inj (h k hk), fun h k hk ↦ ?_⟩
  have : x k = y k := LeibnizO.ext (h k hk)
  exact Dist.of_eq this

/-- The constant Cantor stream of `true`. -/
def constTrue : Cantor := fun _ ↦ ⟨true⟩

/-- The constant Cantor stream of `false`. -/
def constFalse : Cantor := fun _ ↦ ⟨false⟩

/-- The alternating Cantor stream `true, false, true, false, …`. -/
def alternating : Cantor := fun k ↦ ⟨decide (k % 2 = 0)⟩

/-- The constant-`true` and constant-`false` Cantor streams are distinguishable at level 1. -/
theorem constTrue_ne_constFalse : ¬ (constTrue ≡{1}≡ constFalse) := by
  intro h
  have h0 : (constTrue 0).car = (constFalse 0).car :=
    (dist_iff (x := constTrue) (y := constFalse)).mp h 0 Nat.zero_lt_one
  simp [constTrue, constFalse] at h0

end Cantor

/-! ## Baire space `Nat → Nat` -/

/-- The Baire space `Nat → Nat`, viewed as the underlying type of the truncation OFE on
streams of natural numbers (entries wrapped in `LeibnizO` so they form a discrete OFE). -/
abbrev Baire : Type := StreamO (LeibnizO Nat)

namespace Baire

/-- Baire `n`-equivalence is plain equality of the first `n` entries. -/
theorem dist_iff {n : Nat} {x y : Baire} :
    (x ≡{n}≡ y) ↔ ∀ k, k < n → (x k).car = (y k).car := by
  refine ⟨fun h k hk ↦ LeibnizO.dist_inj (h k hk), fun h k hk ↦ ?_⟩
  have : x k = y k := LeibnizO.ext (h k hk)
  exact Dist.of_eq this

/-- The identity Baire stream `k ↦ k`. -/
def idStream : Baire := fun k ↦ ⟨k⟩

/-- The constant zero Baire stream. -/
def constZero : Baire := fun _ ↦ ⟨0⟩

end Baire

end IrisMath.Stream

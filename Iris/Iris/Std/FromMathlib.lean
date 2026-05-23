/-
Copyright (c) 2026 Zongyuan Liu, Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Batteries.Data.List.Basic
public import Batteries.Data.Int
public import Batteries.Data.Nat.Bitwise
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Int.Bitwise.Basic
import all Init.Data.Int.Basic


@[expose] public section

namespace FromMathlib

/-- NB. Copied from Mathlib -/
theorem List.Nodup.of_map (f : α → β) {l : List α} : List.Nodup (List.map f l) → List.Nodup l := by
  refine (List.Pairwise.of_map f) fun _ _ => mt <| fun a => (congrArg f ∘ fun _ => a) α

/-- NB. Copied from Mathlib -/
theorem Pairwise.forall {l : List α} {R : α → α → Prop} (hR : ∀ {a b}, R a b ↔ a ≠ b)
    (hl : l.Pairwise (· ≠ ·)) : ∀ ⦃a⦄, a ∈ l → ∀ ⦃b⦄, b ∈ l → a ≠ b → R a b := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.mem_cons]
    rintro x (rfl | hx) y (rfl | hy)
    · simp
    · exact fun a => hR.mpr a
    · exact fun a => hR.mpr a
    · refine ih (List.Pairwise.of_cons hl) hx hy

/-- NB. Copied from Mathlib -/
theorem inj_on_of_nodup_map {f : α → β} {l : List α} (d : List.Nodup (List.map f l)) :
    ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → f x = f y → x = y := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map, List.nodup_cons, List.mem_map, not_exists, not_and, ← Ne.eq_def] at d
    simp only [List.mem_cons]
    rintro _ (rfl | h₁) _ (rfl | h₂) h₃
    · rfl
    · apply (d.1 _ h₂ h₃.symm).elim
    · apply (d.1 _ h₁ h₃).elim
    · apply ih d.2 h₁ h₂ h₃

/-- NB. Copied from Mathlib -/
theorem Nodup.map_on {f : α → β} (H : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) (d : List.Nodup l) :
    (List.map f l).Nodup :=
  List.Pairwise.map _ (fun a b ⟨ma, mb, n⟩ e => n (H a ma b mb e)) (List.Pairwise.and_mem.1 d)

/-- NB. Copied from Mathlib -/
 theorem Nodup.filterMap {f : α → Option β} (h : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a') :
    List.Nodup l → List.Nodup (List.filterMap f l) :=
  (List.Pairwise.filterMap f) @fun a a' n b bm b' bm' e => n <| h a a' b' (by rw [← e]; exact bm) bm'

/-- NB. Copied from Mathlib -/
theorem Nodup.filter (p : α → Bool) {l} : List.Nodup l → List.Nodup (List.filter p l) := by
  simpa using List.Pairwise.filter p

inductive Relation.ReflTransGen (r : α → α → Prop) (a : α) : α → Prop
  | refl : ReflTransGen r a a
  | tail {b c : α} : ReflTransGen r a b → r b c → ReflTransGen r a c

namespace Relation.ReflTransGen

theorem head (hab : r a b) (hbc : ReflTransGen r b c) : ReflTransGen r a c := by
  induction hbc with
  | refl => exact refl.tail hab
  | tail _ hcd hac => exact hac.tail hcd

@[elab_as_elim]
theorem head_induction_on {motive : ∀ a : α, ReflTransGen r a b → Prop} {a : α}
    (h : ReflTransGen r a b) (refl : motive b refl)
    (head : ∀ {a c} (h' : r a c) (h : ReflTransGen r c b), motive c h → motive a (h.head h')) :
    motive a h := by
  induction h with
  | refl => exact refl
  | @tail b c _ hbc ih =>
  apply ih
  · exact head hbc _ refl
  · exact fun h1 h2 ↦ head h1 (h2.tail hbc)

theorem cases_head (h : ReflTransGen r a b) : a = b ∨ ∃ c, r a c ∧ ReflTransGen r c b := by
  induction h using ReflTransGen.head_induction_on <;> grind

end Relation.ReflTransGen

namespace List

@[grind .]
theorem forall₂_zip : ∀ {l₁ l₂}, List.Forall₂ R l₁ l₂ → ∀ {a b}, (a, b) ∈ l₁.zip l₂ → R a b
  | _, _, List.Forall₂.cons h₁ h₂, x, y, hx => by
    rw [List.zip, List.zipWith, List.mem_cons] at hx
    match hx with
    | Or.inl rfl => exact h₁
    | Or.inr h₃ => exact forall₂_zip h₂ h₃


@[elab_as_elim]
def reverseCases {motive : List α → Sort _} (nil : motive [])
    (append_singleton : ∀ (l : List α) (a : α), motive (l ++ [a])) : ∀ l, motive l
  | [] => nil
  | a :: l => (List.dropLast_concat_getLast (List.cons_ne_nil a l)) ▸
    append_singleton _ _

@[elab_as_elim]
def reverseRec {motive : List α → Sort _} (nil : motive [])
    (append_singleton : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) : ∀ l, motive l
  | [] => nil
  | a :: l => (List.dropLast_concat_getLast (List.cons_ne_nil a l)) ▸
    append_singleton _ _ (List.reverseRec nil append_singleton (a :: l).dropLast)
  termination_by l => l.length

end List

namespace Nat

/-- NB. Copied from Mathlib -/
def ldiff : Nat → Nat → Nat :=
  Nat.bitwise fun a b => a && not b

/-- NB. Copied from Mathlib
`bit b` appends the digit `b` to the little end of the binary representation of
its natural number input. -/
def bit (b : Bool) (n : Nat) : Nat :=
  cond b (2 * n + 1) (2 * n)

/-- NB. Copied from Mathlib -/
theorem bit_val (b n) : bit b n = 2 * n + b.toNat := by
  cases b <;> rfl

/-- NB. Copied from Mathlib
`shiftLeft' b m n` performs a left shift of `m` `n` times
and adds the bit `b` as the least significant bit each time.
Returns the corresponding natural number -/
def shiftLeft' (b : Bool) (m : Nat) : Nat → Nat
  | 0 => m
  | n + 1 => bit b (shiftLeft' b m n)

/-- NB. Copied from Mathlib -/
@[simp]
theorem shiftLeft'_false : ∀ n, shiftLeft' false m n = m <<< n
  | 0 => rfl
  | n + 1 => by
    have : 2 * (m * 2 ^ n) = 2 ^ (n + 1) * m := by
      rw [Nat.mul_comm, Nat.mul_assoc, ← Nat.pow_succ]; grind only
    simp [Nat.shiftLeft_eq, shiftLeft', bit_val, shiftLeft'_false, this]
    grind only

/-- NB. Copied from Mathlib -/
@[simp] theorem shiftRight_eq (m n : Nat) : Nat.shiftRight m n = m >>> n := rfl

end Nat

namespace Int

open Nat _root_.Int

/-- NB. Copied from Mathlib
`lor` takes two integers and returns their bitwise `or` -/
def lor : Int → Int → Int
  | (m : Nat), (n : Nat) => m ||| n
  | (m : Nat), -[n+1] => -[ldiff n m+1]
  | -[m+1], (n : Nat) => -[ldiff m n+1]
  | -[m+1], -[n+1] => -[m &&& n+1]

instance : HOr Int Int Int := ⟨lor⟩

/-- NB. Copied from Mathlib
`land` takes two integers and returns their bitwise `and` -/
def land : Int → Int → Int
  | (m : Nat), (n : Nat) => m &&& n
  | (m : Nat), -[n+1] => ldiff m n
  | -[m+1], (n : Nat) => ldiff n m
  | -[m+1], -[n+1] => -[m ||| n+1]

instance : HAnd Int Int Int := ⟨land⟩

/-- NB. Copied from Mathlib
`xor` computes the bitwise `xor` of two natural numbers -/
def xor : Int → Int → Int
  | (m : Nat), (n : Nat) => (m ^^^ n)
  | (m : Nat), -[n+1] => -[(m ^^^ n)+1]
  | -[m+1], (n : Nat) => -[(m ^^^ n)+1]
  | -[m+1], -[n+1] => (m ^^^ n)

instance : HXor Int Int Int := ⟨xor⟩

/-- NB. Copied from Mathlib
`m <<< n` produces an integer whose binary representation
is obtained by left-shifting the binary representation of `m` by `n` places -/
instance : ShiftLeft Int where
  shiftLeft
  | (m : Nat), (n : Nat) => Nat.shiftLeft' false m n
  | (m : Nat), -[n+1] => m >>> (Nat.succ n)
  | -[m+1], (n : Nat) => -[shiftLeft' true m n+1]
  | -[m+1], -[n+1] => -[m >>> (Nat.succ n)+1]

instance : HShiftLeft Int Int Int := ⟨ShiftLeft.shiftLeft⟩

/-- NB. Copied from Mathlib
`m >>> n` produces an integer whose binary representation
is obtained by right-shifting the binary representation of `m` by `n` places -/
instance : ShiftRight Int where
  shiftRight m n := m <<< (-n)

instance : HShiftRight Int Int Int := ⟨ShiftRight.shiftRight⟩

end Int

end FromMathlib

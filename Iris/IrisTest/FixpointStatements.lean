/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Instances.IProp
public import Iris.ProofMode.Lib

@[expose] public section

open Iris BI OFE

/-! # The statements `ifix`, `icofix` and `iguarded` generate

The generator moves every lemma across currying and back, and restores binder names; this pins
down the result. A change here should be deliberate: tuples, or names such as `x_1`, must not
appear. -/

namespace IrisTest.FixpointStatements

abbrev P := IProp BundledGFunctors.default

/-- Print the statements of the declarations `name.suffix`, in order. -/
meta def printGenerated (name : Lean.Name) (suffixes : List Lean.Name) :
    Lean.Elab.Command.CommandElabM Unit :=
  Lean.Elab.Command.liftTermElabM do
    for s in suffixes do
      let n := `IrisTest.FixpointStatements ++ name ++ s
      let some ci := (← Lean.getEnv).find? n | Lean.logInfo m!"{name ++ s}: missing"; continue
      Lean.logInfo m!"{name ++ s} : {ci.type}"

ifix lf (b : Bool) (n : Nat) : P := iprop(⌜n = 0⌝ ∨ lf (!b) (n - 1))

/--
info: lf.pre : (Bool → Nat → P) → Bool → Nat → P
---
info: lf.unfold : ∀ (b : Bool) (n : Nat), lf b n = lf.pre lf b n
---
info: lf.pre_mono : ∀ (Φ Ψ : Bool → Nat → P), ⊢ (□ ∀ b n, Φ b n -∗ Ψ b n) -∗ ∀ b n, lf.pre Φ b n -∗ lf.pre Ψ b n
---
info: lf.unfold_mp : ∀ (b : Bool) (n : Nat), lf b n ⊢ lf.pre lf b n
---
info: lf.unfold_mpr : ∀ (b : Bool) (n : Nat), lf.pre lf b n ⊢ lf b n
---
info: lf.iter : ∀ (Φ : Bool → Nat → P), ⊢ (□ ∀ b n, lf.pre Φ b n -∗ Φ b n) -∗ ∀ b n, lf b n -∗ Φ b n
---
info: lf.ind : ∀ (Φ : Bool → Nat → P),
  ⊢ (□ ∀ b n, lf.pre (fun b n => iprop(Φ b n ∧ lf b n)) b n -∗ Φ b n) -∗ ∀ b n, lf b n -∗ Φ b n
---
info: lf.ind_wf : ∀ (Φ W : Bool → Nat → P),
  (∀ (b : Bool) (n : Nat), Φ b n ∧ lf.pre W b n ⊢ W b n) → ⊢ (□ ∀ b n, lf.pre W b n -∗ Φ b n) -∗ ∀ b n, lf b n -∗ Φ b n
---
info: lf.strong_mono : ∀ (G : (Bool → Nat → P) → Bool → Nat → P) (g : Bool → Nat → P),
  (∀ (b : Bool) (n : Nat), G g b n ⊢ g b n) → ⊢ (□ ∀ Φ b n, lf.pre Φ b n -∗ G Φ b n) -∗ ∀ b n, lf b n -∗ g b n
---
info: lf.affine : ∀ [∀ (b : Bool) (n : Nat), Affine (lf.pre (fun b n => iprop(emp)) b n)] (b : Bool) (n : Nat),
  Affine (lf b n)
---
info: lf.absorbing : ∀ [∀ (b : Bool) (n : Nat), Absorbing (lf.pre (fun b n => iprop(True -∗ lf b n)) b n)] (b : Bool)
  (n : Nat), Absorbing (lf b n)
---
info: lf.persistent_affine : ∀ [∀ (b : Bool) (n : Nat), Affine (lf.pre (fun b n => iprop(□ lf b n)) b n)]
  [∀ (b : Bool) (n : Nat), Persistent (lf.pre (fun b n => iprop(□ lf b n)) b n)] (b : Bool) (n : Nat),
  Persistent (lf b n)
---
info: lf.persistent_absorbing : ∀ [∀ (b : Bool) (n : Nat), Absorbing (lf b n)]
  [∀ (b : Bool) (n : Nat), Persistent (lf.pre (fun b n => iprop(<pers> lf b n)) b n)] (b : Bool) (n : Nat),
  Persistent (lf b n)
-/
#guard_msgs in
run_cmd printGenerated `lf [`pre, `unfold, `pre_mono, `unfold_mp, `unfold_mpr, `iter, `ind,
  `ind_wf, `strong_mono, `affine, `absorbing, `persistent_affine, `persistent_absorbing]

icofix gf (b : Bool) (n : Nat) : P := iprop(▷ gf (!b) (n + 1))

/--
info: gf.pre : (Bool → Nat → P) → Bool → Nat → P
---
info: gf.unfold : ∀ (b : Bool) (n : Nat), gf b n = gf.pre gf b n
---
info: gf.pre_mono : ∀ (Φ Ψ : Bool → Nat → P), ⊢ (□ ∀ b n, Φ b n -∗ Ψ b n) -∗ ∀ b n, gf.pre Φ b n -∗ gf.pre Ψ b n
---
info: gf.unfold_mp : ∀ (b : Bool) (n : Nat), gf b n ⊢ gf.pre gf b n
---
info: gf.unfold_mpr : ∀ (b : Bool) (n : Nat), gf.pre gf b n ⊢ gf b n
---
info: gf.coiter : ∀ (Φ : Bool → Nat → P), ⊢ (□ ∀ b n, Φ b n -∗ gf.pre Φ b n) -∗ ∀ b n, Φ b n -∗ gf b n
---
info: gf.coind : ∀ (Φ : Bool → Nat → P),
  ⊢ (□ ∀ b n, Φ b n -∗ gf.pre (fun b n => iprop(Φ b n ∨ gf b n)) b n) -∗ ∀ b n, Φ b n -∗ gf b n
---
info: gf.paco : ∀ (Φ W : Bool → Nat → P),
  (∀ (b : Bool) (n : Nat), W b n ⊢ Φ b n ∨ gf.pre W b n) → ⊢ (□ ∀ b n, Φ b n -∗ gf.pre W b n) -∗ ∀ b n, Φ b n -∗ gf b n
---
info: gf.strong_mono : ∀ (G : (Bool → Nat → P) → Bool → Nat → P) (g : Bool → Nat → P),
  (∀ (b : Bool) (n : Nat), g b n ⊢ G g b n) → ⊢ (□ ∀ Φ b n, G Φ b n -∗ gf.pre Φ b n) -∗ ∀ b n, g b n -∗ gf b n
---
info: gf.absorbing : ∀ [∀ (b : Bool) (n : Nat), Absorbing (gf.pre (fun b n => iprop(<absorb> gf b n)) b n)] (b : Bool)
  (n : Nat), Absorbing (gf b n)
-/
#guard_msgs in
run_cmd printGenerated `gf [`pre, `unfold, `pre_mono, `unfold_mp, `unfold_mpr, `coiter,
  `coind, `paco, `strong_mono, `absorbing]

ifix none0 : P := iprop(▷ none0)

/--
info: none0.unfold : none0 = none0.pre none0
---
info: none0.pre_mono : ∀ (Φ Ψ : P), ⊢ □ (Φ -∗ Ψ) -∗ none0.pre Φ -∗ none0.pre Ψ
---
info: none0.iter : ∀ (Φ : P), ⊢ □ (none0.pre Φ -∗ Φ) -∗ none0 -∗ Φ
-/
#guard_msgs in
run_cmd printGenerated `none0 [`unfold, `pre_mono, `iter]

ifix one1 (n : Nat) : P := iprop(▷ one1 (n + 1))

/--
info: one1.eq_lfp : one1 = MonotoneFixpoint.lfp one1.pre ⋯
---
info: one1.iter : ∀ (Φ : Nat → P), ⊢ (□ ∀ n, one1.pre Φ n -∗ Φ n) -∗ ∀ n, one1 n -∗ Φ n
-/
#guard_msgs in
run_cmd printGenerated `one1 [`eq_lfp, `iter]

-- Dependent arguments: the second argument's type depends on the first.
ifix dep (n : Nat) (i : Fin n) : P := iprop(⌜i.val < n⌝ ∗ ▷ ∃ (m : Nat) (j : Fin m), dep m j)

/--
info: dep.unfold : ∀ (n : Nat) (i : Fin n), dep n i = dep.pre dep n i
---
info: dep.pre_mono : ∀ (Φ Ψ : (n : Nat) → Fin n → P), ⊢ (□ ∀ n i, Φ n i -∗ Ψ n i) -∗ ∀ n i, dep.pre Φ n i -∗ dep.pre Ψ n i
---
info: dep.iter : ∀ (Φ : (n : Nat) → Fin n → P), ⊢ (□ ∀ n i, dep.pre Φ n i -∗ Φ n i) -∗ ∀ n i, dep n i -∗ Φ n i
---
info: dep.strong_mono : ∀ (G : ((n : Nat) → Fin n → P) → (n : Nat) → Fin n → P) (g : (n : Nat) → Fin n → P),
  (∀ (n : Nat) (i : Fin n), G g n i ⊢ g n i) → ⊢ (□ ∀ Φ n i, dep.pre Φ n i -∗ G Φ n i) -∗ ∀ n i, dep n i -∗ g n i
-/
#guard_msgs in
run_cmd printGenerated `dep [`unfold, `pre_mono, `iter, `strong_mono]

ifix swapNe [OFE α] (x y : α) : P := iprop(▷ swapNe y x)

/--
info: swapNe.iter : ∀ {α : Type u_1} [inst : OFE α] (Φ : α → α → P),
  ⊢ (□ ∀ x y, swapNe.pre Φ x y -∗ Φ x y) -∗ ∀ x y, swapNe x y -∗ Φ x y
---
info: swapNe.ne : ∀ {α : Type u_1} [inst : OFE α],
  (∀ (Φ : α → α → P),
      (∀ (n : Nat) (x y x' y' : α), x ≡{n}≡ x' ∧ y ≡{n}≡ y' → Φ x y ≡{n}≡ Φ x' y') →
        ∀ (n : Nat) (x y x' y' : α), x ≡{n}≡ x' ∧ y ≡{n}≡ y' → swapNe.pre Φ x y ≡{n}≡ swapNe.pre Φ x' y') →
    ∀ (n : Nat) (x y x' y' : α), x ≡{n}≡ x' ∧ y ≡{n}≡ y' → swapNe x y ≡{n}≡ swapNe x' y'
-/
#guard_msgs in
run_cmd printGenerated `swapNe [`iter, `ne]

iguarded gd (b : Bool) (n : Nat) : P := iprop(▷ gd (!b) (n + 1))
contractive_by
  intros k Φ Ψ h b n; unfold gd.pre; exact Contractive.distLater_dist (fun m hm => h m hm _ _)

/--
info: gd.pre : (Bool → Nat → P) → Bool → Nat → P
---
info: gd.unfold : ∀ (b : Bool) (n : Nat), gd b n = gd.pre gd b n
---
info: gd.eq_fixpoint : ∀ {inhabited : Inhabited (Bool → Nat → P)} (b : Bool) (n : Nat), gd b n = fixpoint gd.pre b n
---
info: gd.persistent : (∀ (Φ : Bool → Nat → P),
    (∀ (b : Bool) (n : Nat), Persistent (Φ b n)) → ∀ (b : Bool) (n : Nat), Persistent (gd.pre Φ b n)) →
  ∀ (b : Bool) (n : Nat), Persistent (gd b n)
---
info: gd.affine : (∀ (Φ : Bool → Nat → P),
    (∀ (b : Bool) (n : Nat), Affine (Φ b n)) → ∀ (b : Bool) (n : Nat), Affine (gd.pre Φ b n)) →
  ∀ (b : Bool) (n : Nat), Affine (gd b n)
---
info: gd.absorbing : (∀ (Φ : Bool → Nat → P),
    (∀ (b : Bool) (n : Nat), Absorbing (Φ b n)) → ∀ (b : Bool) (n : Nat), Absorbing (gd.pre Φ b n)) →
  ∀ (b : Bool) (n : Nat), Absorbing (gd b n)
---
info: gd.persistent_absorbing : (∀ (Φ : Bool → Nat → P),
    (∀ (b : Bool) (n : Nat), Persistent (Φ b n)) →
      (∀ (b : Bool) (n : Nat), Absorbing (Φ b n)) →
        ∀ (b : Bool) (n : Nat), Persistent (gd.pre Φ b n) ∧ Absorbing (gd.pre Φ b n)) →
  ∀ (b : Bool) (n : Nat), Persistent (gd b n) ∧ Absorbing (gd b n)
---
info: gd.persistent_affine : (∀ (Φ : Bool → Nat → P),
    (∀ (b : Bool) (n : Nat), Persistent (Φ b n)) →
      (∀ (b : Bool) (n : Nat), Affine (Φ b n)) →
        ∀ (b : Bool) (n : Nat), Persistent (gd.pre Φ b n) ∧ Affine (gd.pre Φ b n)) →
  ∀ (b : Bool) (n : Nat), Persistent (gd b n) ∧ Affine (gd b n)
---
info: gd.plain : (∀ (Φ : Bool → Nat → P),
    (∀ (b : Bool) (n : Nat), Plain (Φ b n)) → ∀ (b : Bool) (n : Nat), Plain (gd.pre Φ b n)) →
  ∀ (b : Bool) (n : Nat), Plain (gd b n)
---
info: gd.plain_absorbing : (∀ (Φ : Bool → Nat → P),
    (∀ (b : Bool) (n : Nat), Plain (Φ b n)) →
      (∀ (b : Bool) (n : Nat), Absorbing (Φ b n)) →
        ∀ (b : Bool) (n : Nat), Plain (gd.pre Φ b n) ∧ Absorbing (gd.pre Φ b n)) →
  ∀ (b : Bool) (n : Nat), Plain (gd b n) ∧ Absorbing (gd b n)
---
info: gd.plain_affine : (∀ (Φ : Bool → Nat → P),
    (∀ (b : Bool) (n : Nat), Plain (Φ b n)) →
      (∀ (b : Bool) (n : Nat), Affine (Φ b n)) → ∀ (b : Bool) (n : Nat), Plain (gd.pre Φ b n) ∧ Affine (gd.pre Φ b n)) →
  ∀ (b : Bool) (n : Nat), Plain (gd b n) ∧ Affine (gd b n)
-/
#guard_msgs in
run_cmd printGenerated `gd [`pre, `unfold, `eq_fixpoint, `persistent, `affine, `absorbing,
  `persistent_absorbing, `persistent_affine, `plain, `plain_absorbing, `plain_affine]

/-! ## Names and shapes that the currying must leave alone -/

-- A parameter whose own type is a `PSigma` stays one parameter.
ifix psig (s : (n : Nat) ×' Fin (n + 1)) (b : Bool) : P := iprop(▷ psig ⟨s.1 + 1, 0⟩ (!b))

/--
info: psig.iter : ∀ (Φ : (n : Nat) ×' Fin (n + 1) → Bool → P),
  ⊢ (□ ∀ s b, psig.pre Φ s b -∗ Φ s b) -∗ ∀ s b, psig s b -∗ Φ s b
-/
#guard_msgs in
run_cmd printGenerated `psig [`iter]

-- Binders inside a parameter's type keep their names.
ifix inner (f : (x : Nat) → Fin (x + 1)) (b : Bool) (c : Bool) : P := iprop(▷ inner f c b)

/--
info: inner.iter : ∀ (f : (x : Nat) → Fin (x + 1)) (Φ : Bool → Bool → P),
  ⊢ (□ ∀ b c, inner.pre f Φ b c -∗ Φ b c) -∗ ∀ b c, inner f b c -∗ Φ b c
-/
#guard_msgs in
run_cmd printGenerated `inner [`iter]

-- Parameters named like the library's binders keep their names; the library's are primed.
ifix clash (Φ : Nat) (Ψ : Nat) : P := iprop(▷ clash Ψ Φ)

/--
info: clash.pre_mono : ∀ (Φ'' Ψ'' : Nat → Nat → P),
  ⊢ (□ ∀ Φ Ψ, Φ'' Φ Ψ -∗ Ψ'' Φ Ψ) -∗ ∀ Φ Ψ, clash.pre Φ'' Φ Ψ -∗ clash.pre Ψ'' Φ Ψ
---
info: clash.iter : ∀ (Φ'' : Nat → Nat → P), ⊢ (□ ∀ Φ Ψ, clash.pre Φ'' Φ Ψ -∗ Φ'' Φ Ψ) -∗ ∀ Φ Ψ, clash Φ Ψ -∗ Φ'' Φ Ψ
-/
#guard_msgs in
run_cmd printGenerated `clash [`pre_mono, `iter]

ifix clashG (G g : Nat) : P := iprop(▷ clashG g G)

/--
info: clashG.strong_mono : ∀ (G'' : (Nat → Nat → P) → Nat → Nat → P) (g'' : Nat → Nat → P),
  (∀ (G g : Nat), G'' g'' G g ⊢ g'' G g) → ⊢ (□ ∀ Φ G g, clashG.pre Φ G g -∗ G'' Φ G g) -∗ ∀ G g, clashG G g -∗ g'' G g
-/
#guard_msgs in
run_cmd printGenerated `clashG [`strong_mono]

-- `ne` with one parameter, and with parameters named `n` and `x'`.
ifix ne1 {α : Type} [OFE α] (a : α) : P := iprop(▷ ∀ b : α, ⌜a = a⌝ ∗ ne1 b)

/--
info: ne1.ne : ∀ {α : Type} [inst : OFE α],
  (∀ (Φ : α → P),
      (∀ (n : Nat) (a a' : α), a ≡{n}≡ a' → Φ a ≡{n}≡ Φ a') →
        ∀ (n : Nat) (a a' : α), a ≡{n}≡ a' → ne1.pre Φ a ≡{n}≡ ne1.pre Φ a') →
    ∀ (n : Nat) (a a' : α), a ≡{n}≡ a' → ne1 a ≡{n}≡ ne1 a'
-/
#guard_msgs in
run_cmd printGenerated `ne1 [`ne]

ifix ne2 [OFE α] (x n : α) : P := iprop(▷ ne2 n x)

/--
info: ne2.ne : ∀ {α : Type u_1} [inst : OFE α],
  (∀ (Φ : α → α → P),
      (∀ (n'' : Nat) (x n x' n' : α), x ≡{n''}≡ x' ∧ n ≡{n''}≡ n' → Φ x n ≡{n''}≡ Φ x' n') →
        ∀ (n'' : Nat) (x n x' n' : α), x ≡{n''}≡ x' ∧ n ≡{n''}≡ n' → ne2.pre Φ x n ≡{n''}≡ ne2.pre Φ x' n') →
    ∀ (n'' : Nat) (x n x' n' : α), x ≡{n''}≡ x' ∧ n ≡{n''}≡ n' → ne2 x n ≡{n''}≡ ne2 x' n'
-/
#guard_msgs in
run_cmd printGenerated `ne2 [`ne]

-- A fixed parameter between varying ones.
ifix mixed (a : Nat) (k : Bool) (c : Nat) : P := iprop(▷ mixed (a + 1) k (c + 1))

/--
info: mixed.iter : ∀ (k : Bool) (Φ : Nat → Nat → P), ⊢ (□ ∀ a c, mixed.pre k Φ a c -∗ Φ a c) -∗ ∀ a c, mixed a k c -∗ Φ a c
-/
#guard_msgs in
run_cmd printGenerated `mixed [`iter]

-- A body that quantifies over the predicate's own type: only the library's binders are renamed.
ifix predBody (a b : Nat) : P := iprop(∀ R : Nat → Nat → P, R a b -∗ ▷ predBody b a)

/--
info: predBody.pre : (Nat → Nat → P) → Nat → Nat → P
---
info: predBody.pre_mono : ∀ (Φ Ψ : Nat → Nat → P),
  ⊢ (□ ∀ a b, Φ a b -∗ Ψ a b) -∗ ∀ a b, predBody.pre Φ a b -∗ predBody.pre Ψ a b
---
info: predBody.iter : ∀ (Φ : Nat → Nat → P), ⊢ (□ ∀ a b, predBody.pre Φ a b -∗ Φ a b) -∗ ∀ a b, predBody a b -∗ Φ a b
---
info: predBody.strong_mono : ∀ (G : (Nat → Nat → P) → Nat → Nat → P) (g : Nat → Nat → P),
  (∀ (a b : Nat), G g a b ⊢ g a b) → ⊢ (□ ∀ Φ a b, predBody.pre Φ a b -∗ G Φ a b) -∗ ∀ a b, predBody a b -∗ g a b
-/
#guard_msgs in
run_cmd printGenerated `predBody [`pre, `pre_mono, `iter, `strong_mono]

-- A non-recursive body whose type is a function: its parameters vary.
def base (n : Nat) (b : Bool) : P := iprop(⌜n = 0 ∧ b⌝)

ifix nonRecFn (n : Nat) : Bool → P := base n

/--
info: nonRecFn.unfold : ∀ (n : Nat) (b : Bool), nonRecFn n b = nonRecFn.pre n (nonRecFn n) b
---
info: nonRecFn.iter : ∀ (n : Nat) (Φ : Bool → P), ⊢ (□ ∀ b, nonRecFn.pre n Φ b -∗ Φ b) -∗ ∀ b, nonRecFn n b -∗ Φ b
-/
#guard_msgs in
run_cmd printGenerated `nonRecFn [`unfold, `iter]

-- A non-recursive body: `partial_fixpoint`'s warning about it is dropped.
#guard_msgs in
ifix constBody (p : P) : P := p

/--
info: constBody.pre : P → P → P
---
info: constBody.unfold : ∀ (p : P), constBody p = constBody.pre p (constBody p)
-/
#guard_msgs in
run_cmd printGenerated `constBody [`pre, `unfold]

end IrisTest.FixpointStatements

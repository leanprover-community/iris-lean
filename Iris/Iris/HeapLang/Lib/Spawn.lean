/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu, Klaus Kraßnitzer
-/
module

public import Iris.Instances.Lib.Token
public import Iris.Instances.Lib.Invariants
public import Iris.Std.Namespaces
public import Iris.HeapLang.PrimitiveLaws
public import Iris.HeapLang.ProofMode

namespace Iris.HeapLang

open BI Iris ProgramLogic

@[expose] public section

namespace Spawn

def spawn : Val := hl_val%
  λ f,
    let c := ref(none());
    fork(c ← some(f #()));
    c

def join : Val := hl_val%
  rec join c :=
    match !c with
    | some(x) => x
    | none() => join c

abbrev SpawnG (GF : BundledGFunctors) := TokenG GF

section Predicates

variable [HeapLangGS hlc GF] [SpawnG GF] (N : Namespace)

def spawnInv (γ : GName) (l : Loc) (Ψ : Val → IProp GF) : IProp GF := iprop%
  ∃ lv : Val, (l ↦ some lv) ∗
    (⌜lv = hl_val(none())⌝ ∨
     ∃ w : Val, ⌜lv = hl_val(some(&w))⌝ ∗ (Ψ w ∨ token γ))

def joinHandle (l : Loc) (Ψ : Val → IProp GF) : IProp GF := iprop%
  ∃ γ : GName, token γ ∗ inv N (spawnInv γ l Ψ)

instance spawnInv_ne (γ : GName) (l : Loc) :
    OFE.NonExpansive (spawnInv γ l : (Val → IProp GF) → _) where
  ne _ _ _ HΨ :=
    exists_ne fun _ =>
      sep_ne.ne .rfl <|
        or_ne.ne .rfl <| exists_ne fun w =>
          sep_ne.ne .rfl <| or_ne.ne (HΨ w) .rfl

instance joinHandle_ne (l : Loc) :
    OFE.NonExpansive (joinHandle N l : (Val → IProp GF) → _) where
  ne _ _ _ HΨ :=
    exists_ne fun γ =>
      sep_ne.ne .rfl <| (inv_ne N).ne <| (spawnInv_ne γ l).ne HΨ

end Predicates

-- TODO: redo with texan triples
section Specs

variable [HeapLangGS hlc GF] [SpawnG GF] (N : Namespace)

theorem spawn_spec (Ψ : Val → IProp GF) (f : Val) :
    ⊢ □ ∀ (Φ : Val → IProp GF),
      WP hl(&f #()) {{ Ψ }} -∗
      (∀ l : Loc, joinHandle N l Ψ -∗ Φ hl_val(#(.loc l))) -∗
      WP hl(&spawn &f) {{ Φ }} := by
  iintro !> %Φ Hf HΦ
  wp_rec
  wp_alloc l as Hl
  imod token_alloc with ⟨%γ, Hγ⟩
  iapply fupd_wp
  imod inv_alloc N ⊤ (spawnInv γ l Ψ) $$ [Hl] with #Hinv
  · inext
    unfold spawnInv
    iexists _
    iframe
    ileft; itrivial
  imodintro
  wp_pures
  wp_bind fork(_)
  iapply wp_fork $$ [- Hf] [Hf]
  · inext
    wp_pures
    imodintro
    iapply HΦ $$ %l
    unfold joinHandle
    iexists γ
    iframe Hγ Hinv
  inext
  wp_bind &f _
  iapply wp_wand $$ Hf
  iintro %v HΨ
  wp_pures
  iapply wp_atomic
  imod inv_acc (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hpt, Hclose⟩
  unfold spawnInv
  icases Hpt with ⟨%_, Hl, _⟩
  imodintro
  wp_store
  iapply Hclose
  inext
  iexists _; iframe Hl
  iright; iexists v; isplit
  · itrivial
  · iframe

theorem join_spec (Ψ : Val → IProp GF) (l : Loc) :
    ⊢ □ ∀ (Φ : Val → IProp GF),
      joinHandle N l Ψ -∗
      (∀ v : Val, Ψ v -∗ Φ v) -∗
      WP hl(&join v(#(.loc l))) {{ Φ }} := by
  iintro !> %Φ H HΦ
  unfold joinHandle
  icases H with ⟨%γ, Hγ, #Hinv⟩
  iloeb as IH
  wp_rec
  wp_bind !_
  iapply wp_atomic
  imod inv_acc (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hpt, Hclose⟩
  unfold spawnInv
  icases Hpt with ⟨%lv, Hl, Hcond⟩
  imodintro
  wp_load
  icases Hcond with (%Heq | ⟨%w, %Heq, (HΨw | Hγ')⟩) <;> subst Heq
  · imod Hclose $$ [Hl]
    · inext
      iexists _
      iframe Hl
      ileft; itrivial
    imodintro
    wp_pures
    iapply IH $$ HΦ Hγ
  · imod Hclose $$ [Hl Hγ]
    · inext
      iexists _; iframe Hl
      iright; iexists w; isplit
      · itrivial
      · iframe
    imodintro
    wp_pures
    iapply HΦ $$ HΨw
  · iexfalso
    iapply token_exclusive
    iframe

end Specs

end Spawn
end

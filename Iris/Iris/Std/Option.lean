/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

module

public import Iris.Init -- shake: keep
import Iris.Std.RocqPorting

@[expose] public section

namespace Option

def Forall₂ (R : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some a, some b => R a b
  | _, _ => False

theorem Forall₂.getD {R : α → β → Prop} {a : α} {b : β} (hab : R a b) :
    ∀ {o : Option α} {o' : Option β}, Forall₂ R o o' → R (o.getD a) (o'.getD b)
  | none, none, _ => hab
  | some _, some _, h => h
  | none, some _, h => h.elim
  | some _, none, h => h.elim

theorem Forall₂.equivalence {R : α → α → Prop}
    (H : Equivalence R) : Equivalence (Option.Forall₂ R) where
  refl | none => trivial | some _ => H.1 _
  symm {x y} := by cases x <;> cases y <;> simp [Option.Forall₂]; apply H.2
  trans {x y z} := by cases x <;> cases y <;> cases z <;> simp [Option.Forall₂]; apply H.3

end Option

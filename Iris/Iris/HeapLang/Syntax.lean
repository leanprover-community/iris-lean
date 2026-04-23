/-
Copyright (c) 2026 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
module

@[expose] public section
namespace Iris.HeapLang

@[ext]
structure Loc where
  mk ::
  n : Int
deriving Inhabited, Repr, DecidableEq

instance : Ord Loc where
  compare l₁ l₂ := compare l₁.n l₂.n

instance : Std.TransOrd Loc where
  eq_swap := by
    intros l₁ l₂; unfold compare; unfold instOrdLoc; simp;
    apply Int.instTransOrd.eq_swap
  isLE_trans := by
    intros l₁ l₂ l₃; unfold compare; unfold instOrdLoc; simp;
    apply Int.instTransOrd.isLE_trans

instance : Std.LawfulEqOrd Loc where
  eq_of_compare := by
    intros l₁ l₂; unfold compare; unfold instOrdLoc; simp;
    intros h; ext; assumption

instance : HAdd Loc Int Loc where
  hAdd l i := ⟨l.n + i⟩

instance : Zero Loc where
  zero := ⟨0⟩

@[simp]
theorem loc_add_n (l : Loc) n :
  (l + n).n = l.n + n := by simp [HAdd.hAdd]

@[ext]
structure ProphId where
  mk ::
  n : Nat
deriving Inhabited, Repr, DecidableEq

inductive Binder where
  | anon
  | named (name : String)
deriving Inhabited, Repr, DecidableEq

inductive BaseLit where
  | int (n : Int)
  | bool (b : Bool)
  | unit
  | poison
  | loc (l : Loc)
  | prophecy (p : ProphId)
deriving Inhabited, Repr, DecidableEq

inductive UnOp where
  | neg
  | minus
deriving Inhabited, Repr, DecidableEq

inductive BinOp where
  /- We use "tdiv" and "tmod" instead of "div" and "mod" to
      better match the behavior of 'real' languages:
      e.g., in Rust, -30 / -4 == 7. ("div" would return 8.) -/
  | plus | minus | mult | tdiv | tmod /- arithmetic -/
  | and | or | xor /- bitwise -/
  | shiftl | shiftr /- shifts -/
  | le | lt | eq /- relations -/
  | offset /- pointer offset -/
deriving Inhabited, Repr, DecidableEq

mutual
  inductive Exp : Type where
    /- values -/
    | val (v : Val)
    /- Base lambda calculus -/
    | var (x : String)
    | rec_ (f x : Binder) (e : Exp)
    | app (e₁ e₂ : Exp)
    /- Base types and their operations -/
    | unop (op : UnOp) (e : Exp)
    | binop (op : BinOp) (e₁ e₂ : Exp)
    | if (e₀ e₁ e₂ : Exp)
    /- Products -/
    | pair (e₁ e₂ : Exp)
    | fst (e : Exp)
    | snd (e : Exp)
    /- Sums -/
    | injL (e : Exp)
    | injR (e : Exp)
    | case (e₀ e₁ e₂ : Exp)
    /- Heap -/
    | allocN (e₁ e₂ : Exp) /- array length, initial value -/
    | free (e : Exp)
    | load (e : Exp)
    | store (e₁ e₂ : Exp)
    | cmpXchg (e₀ e₁ e₂ : Exp) /- compare exchange -/
    | xchg (e₁ e₂ : Exp) /- exchange -/
    | faa (e₁ e₂ : Exp) /- fetch and add -/
    /- Concurrency -/
    | fork (e : Exp)
    /- Prophecy -/
    | newProph
    | resolve (e₀ e₁ e₂ : Exp)
  deriving Inhabited, Repr, DecidableEq
  inductive Val : Type where
    | lit (l : BaseLit)
    | rec_ (f x : Binder) (e : Exp)
    | pair (v₁ v₂ : Val)
    | injL (v : Val)
    | injR (v : Val)
  deriving Inhabited, Repr, DecidableEq
end

def Exp.isVal : Exp → Bool
  | .val _ => true
  | _ => false

instance : Coe Nat BaseLit where
  coe n := .int n

instance : Coe Int BaseLit where
  coe n := .int n

instance : Coe Bool BaseLit where
  coe b := .bool b

instance : Coe Unit BaseLit where
  coe _ := .unit

/- TODO: this instance is sometimes not reduced away. What can we do about this? -/
@[reducible]
instance {n} : OfNat BaseLit n where
  ofNat := .int n

def Exp.substStr (x : String) (v : Val) (e : Exp) : Exp :=
  match e with
  | .val _ => e
  | .var x' => if x == x' then .val v else e
  | .rec_ f x' e => .rec_ f x' $ if .named x != f && .named x != x' then e.substStr x v else e
  | .app e₁ e₂ => .app (e₁.substStr x v) (e₂.substStr x v)
  | .unop op e' => .unop op (e'.substStr x v)
  | .binop op e₁ e₂ => .binop op (e₁.substStr x v) (e₂.substStr x v)
  | .if e₀ e₁ e₂ => .if (e₀.substStr x v) (e₁.substStr x v) (e₂.substStr x v)
  | .pair e₁ e₂ => .pair (e₁.substStr x v) (e₂.substStr x v)
  | .fst e' => .fst (e'.substStr x v)
  | .snd e' => .snd (e'.substStr x v)
  | .injL e' => .injL (e'.substStr x v)
  | .injR e' => .injR (e'.substStr x v)
  | .case e₀ e₁ e₂ => .case (e₀.substStr x v) (e₁.substStr x v) (e₂.substStr x v)
  | .allocN e₁ e₂ => .allocN (e₁.substStr x v) (e₂.substStr x v)
  | .free e' => .free (e'.substStr x v)
  | .load e' => .load (e'.substStr x v)
  | .store e₁ e₂ => .store (e₁.substStr x v) (e₂.substStr x v)
  | .cmpXchg e₀ e₁ e₂ => .cmpXchg (e₀.substStr x v) (e₁.substStr x v) (e₂.substStr x v)
  | .xchg e₁ e₂ => .xchg (e₁.substStr x v) (e₂.substStr x v)
  | .faa e₁ e₂ => .faa (e₁.substStr x v) (e₂.substStr x v)
  | .fork e' => .fork (e'.substStr x v)
  | .newProph => .newProph
  | .resolve e₀ e₁ e₂ => .resolve (e₀.substStr x v) (e₁.substStr x v) (e₂.substStr x v)

def Exp.subst (x : Binder) (v : Val) (e : Exp) : Exp :=
  if let .named x := x then Exp.substStr x v e else e

def BaseLit.isUnboxed : BaseLit → Bool
  | .prophecy _ | .poison => false
  | _ => true

def Val.isUnboxed : Val → Bool
  | .lit l => l.isUnboxed
  | .injL (.lit l) => l.isUnboxed
  | .injR (.lit l) => l.isUnboxed
  | _ => false

def Val.compareSafe (v1 v2 : Val) : Bool :=
  v1.isUnboxed || v2.isUnboxed

section Derived
def Exp.stuck : Exp := Exp.app (.val $ .lit $ .int 0) (.val $ .lit $ .int 0)

@[simp]
theorem Exp.stuck_subst x v:
  Exp.substStr x v Exp.stuck = Exp.stuck := by
  simp [Exp.stuck, Exp.substStr]

def Exp.assert (e : Exp) := Exp.if e (.val $ .lit .unit) Exp.stuck

@[simp]
theorem Exp.assert_subst x v e:
  Exp.substStr x v (Exp.assert e) = Exp.assert (Exp.substStr x v e) := by
  simp [Exp.assert, Exp.substStr]
end Derived

/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/
module

public meta import Iris.ProofMode.SynthInstance

@[expose] public section

namespace Iris.ProofMode
open Qq Iris.BI Iris.Std

/--
  Type class for natural number cancellation. Given a number `n` and a
  number `m` that should be cancelled (subtracted) from `n`, compute a new `n'`
  and a remainder `m'` that could not be cancelled.
-/
@[ipm_class]
class NatCancel (n m : Nat) (n' m' : outParam Nat) : Prop where
  nat_cancel : n' + m = n + m'
export NatCancel (nat_cancel)

theorem natCancel_succ (n m n' m' : Nat) (_ : n' + m = n + m') :
    n' + (m + 1) = (n + 1) + m' := by omega

theorem natCancel_plus_left (n1 n2 m n1' n2' n' m' m'' : Nat)
    (h1 : n1' + m = n1 + m') (h2 : n2' + m' = n2 + m'') (_ : n' = n1' + n2') :
    n' + m = (n1 + n2) + m'' := by omega

theorem natCancel_plus_right (n m1 m2 n' n'' m1' m2' m' : Nat)
    (_ : n' + m1 = n + m1') (_ : n'' + m2 = n' + m2') (_ : m' = m1' + m2') :
    n'' + (m1 + m2) = n + m' := by omega

meta section
open Lean Meta Qq

def evalNatExpr (e : Q(Nat)) : MetaM (Option Nat) := (evalNat e).run

/--
  Given `a` and `b`, return their sum and a proof that `a + b` equals the sum.
  Special cases apply when either `a` or `b` is `0`, in which case the zero
  is dropped.
-/
def mkNatAdd (a b : Q(Nat)) : MetaM (Q(Nat) × Expr) := do
  let ka? ← evalNatExpr a
  let kb? ← evalNatExpr b
  -- Get rid of `0` in `a + 0`
  if ka? == some 0 then return (b, q((Nat.zero_add $b).symm))
  -- Get rid of `0` in `0 + b`
  if kb? == some 0 then return (a, q((Nat.add_zero $a).symm))
  if let ⟨some ka, some kb⟩ := (ka?, kb?) then
    let s : Q(Nat) := mkNatLit (ka + kb)
    return (s, ← mkEqRefl s)
  else
    let s : Q(Nat) := q($a + $b)
    return (s, ← mkEqRefl s)

/-- Given `e`, return `e'` such that `e = e' + 1`, if possible. -/
def tryParseSucc (e : Q(Nat)) : MetaM (Option Q(Nat)) := do
  match ← evalNatExpr e with
  | some 0 => return none
  | some (k + 1) => return some <| mkNatLit k
  | none =>
    match_expr e with
    | HAdd.hAdd _ _ _ _ a b =>
      let bNat ← evalNatExpr b
      return if bNat == some 1 then some a else none
    | Nat.add a b =>
      let bNat ← evalNatExpr b
      return if bNat == some 1 then some a else none
    | Nat.succ a => return some a
    | _ => return none

/-- Given `e`, return `e1` and `e2` such that `e = e1 + e2`, if possible. -/
def tryParseAdd (e : Q(Nat)) : Option (Q(Nat) × Q(Nat)) :=
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b => some (a, b)
  | Nat.add a b => some (a, b)
  | _ => none

/-- Cancel the leaf `n` out of `m`. Return `n'`, `m'` and a proof of `n' + m = n + m'`. -/
partial def natCancelR (n m : Q(Nat)) : MetaM (Q(Nat) × Q(Nat) × Expr) := do
  if ← withNewMCtxDepth <| withConfig ({ · with isDefEqStuckEx := false }) <| isDefEq n m then
    let pf : Q(0 + «$m» = «$m» + 0) := q(by omega)
    return (q((0 : Nat)), q((0 : Nat)), pf)
  -- Cancel on both sides: both sides are natural numbers
  if let some kn := n.nat? then
    if let some km := m.nat? then
      let k := min kn km
      let n' : Q(Nat) := mkNatLit (kn - k)
      let m' : Q(Nat) := mkNatLit (km - k)
      let pf ← mkEqRefl q($n' + $m)
      return (n', m', pf)
  -- Cancel on both sides: both sides are successors of another number
  if let some n0 ← tryParseSucc n then
    if let some m0 ← tryParseSucc m then
      let (n', m', h) ← natCancelR n0 m0
      let h : Q($n' + $m0 = $n0 + $m') := h
      return (n', m', q(natCancel_succ $n0 $m0 $n' $m' $h))
  -- Split `m` into two parts and perform cancellation recursively
  if let some (m1, m2) := tryParseAdd m then
    let (n', m1', h1) ← natCancelR n m1
    let (n'', m2', h2) ← natCancelR n' m2
    let (m', hm) ← mkNatAdd m1' m2'
    let h1 : Q($n' + $m1 = $n + $m1') := h1
    let h2 : Q($n'' + $m2 = $n' + $m2') := h2
    let hm : Q($m' = $m1' + $m2') := hm
    return (n'', m', q(natCancel_plus_right $n $m1 $m2 $n' $n'' $m1' $m2' $m' $h1 $h2 $hm))
  -- Nothing else can be cancelled
  return (n, m, (q(rfl) : Q($n + $m = $n + $m)))

/--
  Cancel `m` out of `n`, recursing on the structure of `n`.
  Returns `n'`, `m'` and a proof of `n' + m = n + m'`.
-/
partial def natCancelL (n m : Q(Nat)) : MetaM (Q(Nat) × Q(Nat) × Expr) := do
  -- Nothing to cancel, stop iteration
  if m.nat? == some 0 then
    return (n, m, (q(rfl) : Q($n + $m = $n + $m)))
  -- Cancel on both sides: both sides are natural numbers
  if let some kn := n.nat? then
    if let some km := m.nat? then
      let k := min kn km
      let n' : Q(Nat) := mkNatLit (kn - k)
      let m' : Q(Nat) := mkNatLit (km - k)
      return (n', m', ← mkEqRefl q($n' + $m))
  -- Cancel on both sides: both sides are successors of another number
  if let some n0 ← tryParseSucc n then
    if let some m0 ← tryParseSucc m then
      let (n', m', h) ← natCancelL n0 m0
      let h : Q($n' + $m0 = $n0 + $m') := h
      return (n', m', q(natCancel_succ $n0 $m0 $n' $m' $h))
  -- Split `n` into two parts and perform cancellation recursively
  if let some (n1, n2) := tryParseAdd n then
    let (n1', m', h1) ← natCancelL n1 m
    let (n2', m'', h2) ← natCancelL n2 m'
    let (n', hn) ← mkNatAdd n1' n2'
    let h1 : Q($n1' + $m = $n1 + $m') := h1
    let h2 : Q($n2' + $m' = $n2 + $m'') := h2
    let hn : Q($n' = $n1' + $n2') := hn
    return (n', m'', q(natCancel_plus_left $n1 $n2 $m $n1' $n2' $n' $m' $m'' $h1 $h2 $hn))
  else natCancelR n m

@[ipm_tactic_instance NatCancel _ _ _ _]
def natCancel : SynthTactic := λ e => do
  let_expr NatCancel n m _ _ := e | return .continue
  have n : Q(Nat) := n
  have m : Q(Nat) := m
  let ⟨n', m', pf⟩ ← natCancelL n m
  let pf : Q($n' + $m = $n + $m') := pf
  let inst : Q(NatCancel $n $m $n' $m') := q(⟨$pf⟩)
  return .success inst

end

end Iris.ProofMode

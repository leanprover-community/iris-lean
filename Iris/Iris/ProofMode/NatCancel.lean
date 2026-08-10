/-
Copyright (c) 2026 Alvin Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Tang
-/
module

public meta import Iris.ProofMode.SynthInstance

@[expose] public section

namespace Iris.ProofMode

/--
  Type class for natural number cancellation. Given a number `n` and a
  number `m` that should be cancelled (subtracted) from `n`, compute a new `n'`
  and a remainder `m'` that could not be cancelled.
-/
@[ipm_class]
class NatCancel (n m : Nat) (n' m' : outParam Nat) : Prop where
  nat_cancel : n' + m = n + m'
export NatCancel (nat_cancel)

public meta section
open Lean Meta Qq

namespace NatCancel

/-- Cases where cancellation happens without recursing -/
def natCancelLeaf (n m : Q(Nat)) : MetaM <| Option <| Q(Nat) × Q(Nat) × Expr := do
  -- Syntactically equal operands cancel completely
  if ← withNewMCtxDepth <| isDefEq n m then
    return some (q((0 : Nat)), q((0 : Nat)), q(Nat.add_comm 0 $m))
  match ← evalNat n, ← evalNat m with
  -- One side evaluates to zero: nothing to do
  | some 0, _ | _, some 0 => return some (n, m, ← mkEqRefl q($n + $m))
  -- Subtract `k` on both sides, where `k` is the minimum of `natN` and `natM`
  | some natN, some natM =>
    let k := min natN natM
    let ⟨n', m'⟩ : Q(Nat) × Q(Nat) := (mkNatLit (natN - k), mkNatLit (natM - k))
    unless ← isDefEq q($n' + $m) q($n + $m') do return none
    return some (n', m', ← mkEqRefl q($n' + $m))
  | _, _ => return none

mutual

/-- Given `n = n1 + n2`, cancel `m` against each of `n1` and `n2`. -/
partial def natCancelAdd (n m : Q(Nat)) : MetaM <| Option <| Q(Nat) × Q(Nat) × Expr := do
  match n with
  | ~q($n1 + $n2) =>
    let ⟨n1', m', (h1 : Q($n1' + $m = $n1 + $m'))⟩ ← natCancel n1 m
    let ⟨n2', m'', (h2 : Q($n2' + $m' = $n2 + $m''))⟩ ← natCancel n2 m'
    let ⟨n', (hn : Q($n' = $n1' + $n2'))⟩ ← do
      match ← evalNat n1', ← evalNat n2' with
      -- Discard `n1'` when `n1' = 0`: `n1' + n2'` equals `n2'`
      | some 0, _ => pure (n2', q((Nat.zero_add $n2').symm))
      -- Discard `n2'` when `n1' = 0`: `n1' + n2'` equals `n1'`
      | _, some 0 => pure (n1', q((Nat.add_zero $n1').symm))
      | some natA, some natB => let s : Q(Nat) := mkNatLit (natA + natB); pure (s, ← mkEqRefl s)
      | _, _ => let s : Q(Nat) := q($n1' + $n2'); pure (s, ← mkEqRefl s)
    return some (n', m'', (q(by omega) : Q($n' + $m = $n1 + $n2 + $m'')))
  | _ => return none

partial def natCancel (n m : Q(Nat)) : MetaM <| Q(Nat) × Q(Nat) × Expr := do
  if let some result ← natCancelLeaf n m then return result
  -- Cancel `m` out of `n`, recursing on the structure of `m`
  if let some result ← natCancelAdd n m then return result
  -- Cancel `m` out of `n`, recursing on the structure of `n`
  if let some (m', n', (pf : Q($m' + $n = $m + $n'))) ← natCancelAdd m n then
    return (n', m', (q(by omega) : Q($n' + $m = $n + $m')))
  return (n, m, ← mkEqRefl q($n + $m))

end

@[ipm_tactic_instance NatCancel _ _ _ _]
def instNatCancel : SynthTactic := λ e => do
  let_expr NatCancel n m _ _ := e | return .continue
  let ⟨m, n⟩ : Q(Nat) × Q(Nat) := (m, n)
  let ⟨n', m', (pf : Q($n' + $m = $n + $m'))⟩ ← natCancel n m
  return .success (q(⟨$pf⟩) : Q(NatCancel $n $m $n' $m'))

end NatCancel

end

end Iris.ProofMode

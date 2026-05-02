/-
Copyright (c) 2026 Sergei Stepanenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.HeapLang

@[expose] public section
namespace Iris.Examples.HeapLang

open Iris.HeapLang

/-! ## Basic functions -/

def identity : Exp := hl(λ x, x)

def increment : Exp := hl(λ n, n + #1)

def abs : Exp := hl(λ n, if #0 ≤ n then n else -n)

/-! ## Recursive functions -/

def factorial : Exp :=
  hl(rec fact n :=
    if n ≤ #0 then #1 else n * fact (n - #1))

def sumToN : Exp :=
  hl(rec sum n :=
    if n ≤ #0 then #0 else n + sum (n - #1))

def power : Exp :=
  hl(rec pow base :=
    λ exp,
      if exp ≤ #0 then #1 else base * pow base (exp - #1))

/-! ## Pairs and products -/

def swapPair : Exp := hl(λ p, (snd(p), fst(p)))

def mapPair : Exp := hl(λ f p, (f (fst(p)), f (snd(p))))

def minMax : Exp :=
  hl(λ x y,
    if x ≤ y then (x, y) else (y, x))

/-! ## Sum types -/

def optionMap : Exp :=
  hl(λ f opt,
    match opt with
    | none() => none()
    | some(x) => some(f x))

def optionGetOrElse : Exp :=
  hl(λ opt default,
    match opt with
    | none() => default
    | some(x) => x)

def listLength : Exp :=
  hl(rec len xs :=
    match xs with
    | injl(_) => #0
    | injr(p) => #1 + (len (snd(p))))

def listSum : Exp :=
  hl(rec lsum xs :=
    match xs with
    | injl(_) => #0
    | injr(p) => fst(p) + (lsum (snd(p))))

/-! ## Heap operations -/

def counter : Exp :=
  hl(let c := ref(#0);
     c ← !c + #1;
     !c)

def swap : Exp :=
  hl(λ l1 l2,
    let tmp := !l1;
    l1 ← !l2;
    l2 ← tmp)

def allocArray : Exp := hl(λ n, allocn(n, #0))

def copy : Exp := hl(λ src dst, dst ← !src)

def fibonacci : Exp :=
  hl(λ n,
    let a := ref(#0);
    let b := ref(#1);
    let i := ref(#0);
    (rec loop _ :=
      if !i < n then
        let tmp := !b;
        b ← !a + !b;
        a ← tmp;
        i ← !i + #1;
        loop #()
      else
        !a) #())

/-! ## Concurrency -/

def parallelIncrement : Exp :=
  hl(let c := ref(#0);
     fork(faa(c, #1));
     faa(c, #1);
     c)

def casIncrement : Exp :=
  hl(λ l,
    (rec loop _ :=
      let v := !l;
      let res := cmpXchg(l, v, v + #1);
      if snd(res) then #() else loop #()) #())

def exchangeAndAssert : Exp :=
  hl(λ l newVal expectedOld,
    let old := xchg(l, newVal);
    assert(old = expectedOld))

/-! ## Composing functions -/

def incrementBy2 : Exp := hl(λ n, {increment} ({increment} n))

def powerOf2 : Exp := hl(λ n, {power} #2 n)

def factorialSum : Exp := hl(λ m n, {factorial} m + {factorial} n)

def incrementPair : Exp := hl(λ p, {mapPair} {increment} p)

def absPair : Exp := hl(λ p, {mapPair} {abs} p)

def sortedSum : Exp :=
  hl(λ x y,
    let p := {minMax} x y;
    fst(p) + snd(p))

def listIsEmpty : Exp := hl(λ xs, {listLength} xs ≤ #0)

def listSumIncremented : Exp :=
  hl(rec go xs :=
    match xs with
    | injl(_) => #0
    | injr(p) => {increment} (fst(p)) + (go (snd(p))))

def casIncrementTwice : Exp :=
  hl(λ l,
    {casIncrement} l;
    {casIncrement} l)

def factorialOfCounter : Exp :=
  hl(let c := ref(#0);
     c ← !c + #1;
     {factorial} (!c))

def parallelFactorials : Exp :=
  hl(λ m n,
    let rm := ref(#0);
    let rn := ref(#0);
    fork(rm ← {factorial} m);
    rn ← {factorial} n;
    (!rm, !rn))

/-! ## Counter -/

def newCounter : Exp := hl(λ _, ref(#0))

def counterIncr : Exp :=
  hl(rec incr l :=
    let n := !l;
    if snd(cmpXchg(l, n, #1 + n)) then #() else incr l)

def counterRead : Exp := hl(λ l, !l)

/-! ## Spin lock -/

def spinLockNew : Exp := hl(λ _, ref(#false))

def spinLockTryAcquire : Exp :=
  hl(λ l, snd(cmpXchg(l, #false, #true)))

def spinLockAcquire : Exp :=
  hl(rec acquire l :=
    if {spinLockTryAcquire} l then #() else acquire l)

def spinLockRelease : Exp := hl(λ l, l ← #false)

/-! ## RW spin lock -/

def rwLockNew : Exp := hl(λ _, ref(#0))

def rwLockTryAcquireReader : Exp :=
  hl(λ l,
    let n := !l;
    if #0 ≤ n
      then snd(cmpXchg(l, n, n + #1))
      else #false)

def rwLockAcquireReader : Exp :=
  hl(rec acquire l :=
    if {rwLockTryAcquireReader} l then #() else acquire l)

def rwLockReleaseReader : Exp := hl(λ l, faa(l, #(.int (-1))); #())

def rwLockTryAcquireWriter : Exp :=
  hl(λ l, snd(cmpXchg(l, #0, #(.int (-1)))))

def rwLockAcquireWriter : Exp :=
  hl(rec acquire l :=
    if {rwLockTryAcquireWriter} l then #() else acquire l)

def rwLockReleaseWriter : Exp := hl(λ l, l ← #0)

def lockedCounter : Exp :=
  hl(let lk := {spinLockNew} #();
     let c := {newCounter} #();
     {spinLockAcquire} lk;
     {counterIncr} c;
     {spinLockRelease} lk;
     {counterRead} c)

/-! ## Prophecy variables -/

def nondetBool : Exp :=
  hl(λ _, let l := ref #true; fork (l ← #false); !l)

def newCoin : Exp :=
  hl(λ _, (ref(injl(#())), {Exp.newProph}))

def readCoin : Exp :=
  hl(λ cp,
    let c := fst(cp);
    let p := snd(cp);
    match !c with
    | injl(_) => {hl(let r := {nondetBool} #();
               c ← injr(r);
               {Exp.resolve hl(injl(#())) hl(p) hl(r)};
               r)}
    | injr(b) => b)

end Iris.Examples.HeapLang

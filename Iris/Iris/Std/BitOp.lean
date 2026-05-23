module

public import Batteries.Data.Int
public import Batteries.Data.Nat.Bitwise
import all Init.Data.Nat.Bitwise.Basic

@[expose] public section

namespace FromMathlib

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

namespace Nat

-- Helper lemmas for commutativity of Nat bitwise operations
theorem or_comm (a b : Nat) : a ||| b = b ||| a := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_or]
  cases a.testBit i <;> cases b.testBit i <;> rfl

theorem and_comm (a b : Nat) : a &&& b = b &&& a := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and]
  cases a.testBit i <;> cases b.testBit i <;> rfl

theorem xor_comm (a b : Nat) : a ^^^ b = b ^^^ a := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> rfl

theorem or_assoc (a b c : Nat) : (a ||| b) ||| c = a ||| (b ||| c) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_or]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> rfl

theorem and_assoc (a b c : Nat) : (a &&& b) &&& c = a &&& (b &&& c) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> rfl

theorem xor_assoc (a b c : Nat) : (a ^^^ b) ^^^ c = a ^^^ (b ^^^ c) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> rfl

theorem ldiff_zero (a : Nat) : ldiff a 0 = a := by
  apply Nat.eq_of_testBit_eq; intro i
  simp [ldiff, Nat.testBit_bitwise]

theorem zero_ldiff (a : Nat) : ldiff 0 a = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp [ldiff, Nat.testBit_bitwise]

theorem ldiff_ldiff_or (a b c : Nat) : ldiff (ldiff a b) c = ldiff a (b ||| c) := by
  unfold ldiff
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_bitwise, Nat.testBit_bitwise, Nat.testBit_bitwise, Nat.testBit_or]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i
  all_goals decide

theorem ldiff_comm_and (a b c : Nat) : ldiff (ldiff a b) c = ldiff (ldiff a c) b := by
  unfold ldiff
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_bitwise, Nat.testBit_bitwise, Nat.testBit_bitwise, Nat.testBit_bitwise]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i
  all_goals decide

theorem and_ldiff_left (a b c : Nat) : ldiff (a &&& b) c = (a &&& ldiff b c) := by
  unfold ldiff
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_bitwise, Nat.testBit_and, Nat.testBit_and, Nat.testBit_bitwise]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i
  all_goals decide

theorem and_ldiff_right (a b c : Nat) : ldiff a b &&& c = (a &&& ldiff c b) := by
  unfold ldiff
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_bitwise, Nat.testBit_and, Nat.testBit_bitwise]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i
  all_goals decide

theorem ldiff_and_self (a b c : Nat) : ldiff b a &&& c = ldiff (b &&& c) a := by
  unfold ldiff
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_bitwise, Nat.testBit_bitwise, Nat.testBit_and]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i
  all_goals decide

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

@[simp]
theorem lor_comm (m n : Int) : m ||| n = n ||| m := by
  match m, n with
  | (a : Nat), (b : Nat) =>
    show (lor a b) = (lor b a)
    simp only [lor, Nat.or_comm]
  | (a : Nat), -[b+1] => rfl
  | -[a+1], (b : Nat) => rfl
  | -[a+1], -[b+1] =>
    show (lor (-[a+1]) (-[b+1])) = (lor (-[b+1]) (-[a+1]))
    simp only [lor, Nat.and_comm]

@[simp]
theorem land_comm (m n : Int) : m &&& n = n &&& m := by
  match m, n with
  | (a : Nat), (b : Nat) =>
    show (land a b) = (land b a)
    simp only [land, Nat.and_comm]
  | (a : Nat), -[b+1] => rfl
  | -[a+1], (b : Nat) => rfl
  | -[a+1], -[b+1] =>
    show (land (-[a+1]) (-[b+1])) = (land (-[b+1]) (-[a+1]))
    simp only [land, Nat.or_comm]

@[simp]
theorem xor_comm (m n : Int) : m ^^^ n = n ^^^ m := by
  match m, n with
  | (a : Nat), (b : Nat) =>
    show (xor a b) = (xor b a)
    simp only [xor, Nat.xor_comm]
  | (a : Nat), -[b+1] =>
    show (xor a (-[b+1])) = (xor (-[b+1]) a)
    simp only [xor, Nat.xor_comm]
  | -[a+1], (b : Nat) =>
    show (xor (-[a+1]) b) = (xor b (-[a+1]))
    simp only [xor, Nat.xor_comm]
  | -[a+1], -[b+1] =>
    show (xor (-[a+1]) (-[b+1])) = (xor (-[b+1]) (-[a+1]))
    simp only [xor, Nat.xor_comm]

theorem lor_assoc (m n k : Int) : (m ||| n) ||| k = m ||| (n ||| k) := by
  match m, n, k with
  | (a : Nat), (b : Nat), (c : Nat) =>
    show lor (lor a b) c = lor a (lor b c)
    simp only [lor, Nat.or_assoc]
  | (a : Nat), (b : Nat), -[c+1] =>
    show lor (lor a b) (-[c+1]) = lor a (lor b (-[c+1]))
    simp only [lor]
    congr 1
    rw [← ldiff_ldiff_or, ldiff_comm_and]
  | (a : Nat), -[b+1], (c : Nat) =>
    show lor (lor a (-[b+1])) c = lor a (lor (-[b+1]) c)
    simp only [lor]
    congr 1
    exact ldiff_comm_and b a c
  | (a : Nat), -[b+1], -[c+1] =>
    show lor (lor a (-[b+1])) (-[c+1]) = lor a (lor (-[b+1]) (-[c+1]))
    simp only [lor]
    congr 1
    exact ldiff_and_self a b c
  | -[a+1], (b : Nat), (c : Nat) =>
    show lor (lor (-[a+1]) b) c = lor (-[a+1]) (lor b c)
    simp only [lor]
    congr 1
    exact ldiff_ldiff_or a b c
  | -[a+1], (b : Nat), -[c+1] =>
    show lor (lor (-[a+1]) b) (-[c+1]) = lor (-[a+1]) (lor b (-[c+1]))
    simp only [lor]
    congr 1
    exact and_ldiff_right a b c
  | -[a+1], -[b+1], (c : Nat) =>
    show lor (lor (-[a+1]) (-[b+1])) c = lor (-[a+1]) (lor (-[b+1]) c)
    simp only [lor]
    congr 1
    exact and_ldiff_left a b c
  | -[a+1], -[b+1], -[c+1] =>
    show lor (lor (-[a+1]) (-[b+1])) (-[c+1]) = lor (-[a+1]) (lor (-[b+1]) (-[c+1]))
    simp only [lor]
    congr 1
    exact Nat.and_assoc a b c

theorem land_assoc (m n k : Int) : (m &&& n) &&& k = m &&& (n &&& k) := by
  match m, n, k with
  | (a : Nat), (b : Nat), (c : Nat) =>
    show land (land a b) c = land a (land b c)
    simp only [land, Nat.and_assoc]
  | (a : Nat), (b : Nat), -[c+1] =>
    show land (land a b) (-[c+1]) = land a (land b (-[c+1]))
    simp only [land]
    exact congrArg Nat.cast (and_ldiff_left a b c)
  | (a : Nat), -[b+1], (c : Nat) =>
    show land (land a (-[b+1])) c = land a (land (-[b+1]) c)
    simp only [land]
    exact congrArg Nat.cast (and_ldiff_right a b c)
  | (a : Nat), -[b+1], -[c+1] =>
    show land (land a (-[b+1])) (-[c+1]) = land a (land (-[b+1]) (-[c+1]))
    simp only [land]
    rw [ldiff_comm_and, ldiff_ldiff_or, Nat.or_comm]
  | -[a+1], (b : Nat), (c : Nat) =>
    show land (land (-[a+1]) b) c = land (-[a+1]) (land b c)
    simp only [land]
    exact congrArg Nat.cast (ldiff_and_self a b c)
  | -[a+1], (b : Nat), -[c+1] =>
    show land (land (-[a+1]) b) (-[c+1]) = land (-[a+1]) (land b (-[c+1]))
    simp only [land]
    rw [ldiff_comm_and]
  | -[a+1], -[b+1], (c : Nat) =>
    show land (land (-[a+1]) (-[b+1])) c = land (-[a+1]) (land (-[b+1]) c)
    simp only [land]
    rw [ldiff_ldiff_or, Nat.or_comm]
  | -[a+1], -[b+1], -[c+1] =>
    show land (land (-[a+1]) (-[b+1])) (-[c+1]) = land (-[a+1]) (land (-[b+1]) (-[c+1]))
    simp only [land, Nat.or_assoc]

theorem xor_assoc (m n k : Int) : (m ^^^ n) ^^^ k = m ^^^ (n ^^^ k) := by
  match m, n, k with
  | (a : Nat), (b : Nat), (c : Nat) =>
    show xor (xor a b) c = xor a (xor b c)
    simp only [xor, Nat.xor_assoc]
  | (a : Nat), (b : Nat), -[c+1] =>
    show xor (xor a b) (-[c+1]) = xor a (xor b (-[c+1]))
    simp only [xor, Nat.xor_assoc]
  | (a : Nat), -[b+1], (c : Nat) =>
    show xor (xor a (-[b+1])) c = xor a (xor (-[b+1]) c)
    simp only [xor, Nat.xor_assoc]
  | (a : Nat), -[b+1], -[c+1] =>
    show xor (xor a (-[b+1])) (-[c+1]) = xor a (xor (-[b+1]) (-[c+1]))
    simp only [xor, Nat.xor_assoc]
  | -[a+1], (b : Nat), (c : Nat) =>
    show xor (xor (-[a+1]) b) c = xor (-[a+1]) (xor b c)
    simp only [xor, Nat.xor_assoc]
  | -[a+1], (b : Nat), -[c+1] =>
    show xor (xor (-[a+1]) b) (-[c+1]) = xor (-[a+1]) (xor b (-[c+1]))
    simp only [xor, Nat.xor_assoc]
  | -[a+1], -[b+1], (c : Nat) =>
    show xor (xor (-[a+1]) (-[b+1])) c = xor (-[a+1]) (xor (-[b+1]) c)
    simp only [xor, Nat.xor_assoc]
  | -[a+1], -[b+1], -[c+1] =>
    show xor (xor (-[a+1]) (-[b+1])) (-[c+1]) = xor (-[a+1]) (xor (-[b+1]) (-[c+1]))
    simp only [xor, Nat.xor_assoc]

@[simp]
theorem lor_zero (m : Int) : m ||| 0 = m := by
  match m with
  | (a : Nat) =>
    show lor a 0 = a
    simp only [lor, Nat.or_zero]
  | -[a+1] =>
    show lor (-[a+1]) 0 = -[a+1]
    simp only [lor, Nat.ldiff_zero]

@[simp]
theorem zero_lor (m : Int) : 0 ||| m = m := by
  rw [lor_comm, lor_zero]

@[simp]
theorem land_neg_one (m : Int) : m &&& (-1) = m := by
  match m with
  | (a : Nat) =>
    show land a (-[0+1]) = a
    simp only [land]
    rw [Nat.ldiff_zero]
  | -[a+1] =>
    show land (-[a+1]) (-[0+1]) = -[a+1]
    simp only [land]
    simp [Nat.or_zero]

@[simp]
theorem neg_one_land (m : Int) : (-1) &&& m = m := by
  rw [land_comm, land_neg_one]

@[simp]
theorem xor_zero (m : Int) : m ^^^ 0 = m := by
  match m with
  | (a : Nat) =>
    show xor a 0 = a
    simp only [xor, Nat.xor_zero]
  | -[a+1] =>
    show xor (-[a+1]) 0 = -[a+1]
    simp only [xor, Nat.xor_zero]

@[simp]
theorem zero_xor (m : Int) : 0 ^^^ m = m := by
  rw [xor_comm, xor_zero]

@[simp]
theorem xor_self (m : Int) : m ^^^ m = 0 := by
  match m with
  | (a : Nat) =>
    show xor a a = 0
    simp only [xor, Nat.xor_self]; rfl
  | -[a+1] =>
    show xor (-[a+1]) (-[a+1]) = 0
    simp only [xor, Nat.xor_self]; rfl

@[simp]
theorem land_zero (m : Int) : m &&& 0 = 0 := by
  match m with
  | (a : Nat) =>
    show land a 0 = 0
    simp only [land, Nat.and_zero]; rfl
  | -[a+1] =>
    show land (-[a+1]) 0 = 0
    simp [land, ldiff, Nat.bitwise]

@[simp]
theorem zero_land (m : Int) : 0 &&& m = 0 := by
  rw [land_comm, land_zero]

@[simp]
theorem lor_neg_one (m : Int) : m ||| (-1) = -1 := by
  match m with
  | (a : Nat) =>
    show lor a (-[0+1]) = -1
    simp only [lor]
    simp [ldiff, Nat.bitwise]
  | -[a+1] =>
    show lor (-[a+1]) (-[0+1]) = -1
    simp [lor, Nat.and_zero]

@[simp]
theorem neg_one_lor (m : Int) : (-1) ||| m = -1 := by
  rw [lor_comm, lor_neg_one]

@[simp]
theorem shiftLeft_zero (m : Int) : m <<< 0 = m := by
  cases m <;> simp [HShiftLeft.hShiftLeft, ShiftLeft.shiftLeft, Nat.shiftLeft']

@[simp]
theorem shiftRight_zero (m : Int) : m >>> 0 = m := by
  simp [HShiftRight.hShiftRight, ShiftRight.shiftRight, shiftLeft_zero]

theorem shiftLeft_neg (m : Int) (n : Int) : m <<< (-n) = m >>> n := by
  simp [HShiftRight.hShiftRight, ShiftRight.shiftRight]

theorem shiftRight_neg (m : Int) (n : Int) : m >>> (-n) = m <<< n := by
  simp [HShiftRight.hShiftRight, ShiftRight.shiftRight]

theorem shiftLeft_natCast (m n : Nat) : (m : Int) <<< (n : Int) = ((m <<< n) : Nat) := by
  simp [HShiftLeft.hShiftLeft, ShiftLeft.shiftLeft, shiftLeft'_false]

theorem natCast_lor (m n : Nat) : ((m ||| n : Nat) : Int) = (m : Int) ||| (n : Int) := by
  simp [HOr.hOr, lor]

theorem natCast_land (m n : Nat) : ((m &&& n : Nat) : Int) = (m : Int) &&& (n : Int) := by
  simp [HAnd.hAnd, land]

theorem natCast_xor (m n : Nat) : ((m ^^^ n : Nat) : Int) = (m : Int) ^^^ (n : Int) := by
  simp [HXor.hXor, xor]

theorem lor_negSucc_negSucc (m n : Nat) : -[m+1] ||| -[n+1] = -[m &&& n+1] := rfl

theorem lor_natCast_negSucc (m n : Nat) : (m : Int) ||| -[n+1] = -[ldiff n m+1] := rfl

theorem lor_negSucc_natCast (m n : Nat) : -[m+1] ||| (n : Int) = -[ldiff m n+1] := rfl

theorem land_negSucc_negSucc (m n : Nat) : -[m+1] &&& -[n+1] = -[m ||| n+1] := rfl

theorem land_natCast_negSucc (m n : Nat) : (m : Int) &&& -[n+1] = ldiff m n := rfl

theorem land_negSucc_natCast (m n : Nat) : -[m+1] &&& (n : Int) = ldiff n m := rfl

theorem xor_negSucc_negSucc (m n : Nat) : -[m+1] ^^^ -[n+1] = (m ^^^ n : Nat) := rfl

theorem xor_natCast_negSucc (m n : Nat) : (m : Int) ^^^ -[n+1] = -[(m ^^^ n)+1] := rfl

theorem xor_negSucc_natCast (m n : Nat) : -[m+1] ^^^ (n : Int) = -[(m ^^^ n)+1] := rfl

theorem lor_of_nonneg_of_nonneg {m n : Int} (hm : 0 ≤ m) (hn : 0 ≤ n) :
    m ||| n = ((m.natAbs ||| n.natAbs) : Nat) := by
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  rfl

theorem land_of_nonneg_of_nonneg {m n : Int} (hm : 0 ≤ m) (hn : 0 ≤ n) :
    m &&& n = ((m.natAbs &&& n.natAbs) : Nat) := by
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  rfl

theorem xor_of_nonneg_of_nonneg {m n : Int} (hm : 0 ≤ m) (hn : 0 ≤ n) :
    m ^^^ n = ((m.natAbs ^^^ n.natAbs) : Nat) := by
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  rfl

end Int

end FromMathlib

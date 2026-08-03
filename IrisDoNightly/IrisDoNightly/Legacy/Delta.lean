module

public import IrisDoNightly.Legacy.Array
public import IrisDoNightly.Legacy.Loop
public import IrisDoNightly.Legacy.SLFrame
public import IrisDoNightly.Notation
import Std.Tactic.Do
import Std.Internal.Do

set_option mvcgen.warning false

/-!
# The `delta` codec (from `Reference/codec.ml`)

A byte-wise differencing transform: `compress` stores each byte as its difference from the previous
one (mod 256); `decompress` is the inverse prefix-sum.  Length-preserving, so both directions are a
single pass over same-sized arrays — no growable buffer needed.

A `bytes` value is modelled as a pair `(ptr, len)` where `ptr` is the base location of a contiguous
block of `len` cells.  The OCaml `(c - prev) land 0xff` on a possibly-negative difference is rendered
as `(c - prev + 256) % 256`: behaviourally identical on byte inputs (`c, prev ∈ [0,256)`), and the
`+ 256` keeps the dividend positive so truncated and Euclidean `mod` agree.
-/

open Lean.Order Std.Internal.Do
open Iris.HeapLang

@[expose] public section

namespace Iris.HeapLang.Codec

/-! ## Byte-array model -/

/-- A byte value: an integer literal (invariantly in `[0, 256)`). -/
def byteVal (n : Int) : Val := .lit (.int n)

/-- `bytesArr l ns` owns a `bytes` buffer at base `l` holding the byte values `ns`. -/
def bytesArr (l : Loc) (ns : List Int) : HProp := arrayPointsTo l (ns.map byteVal)

/-- A `bytes` value: the pair `(base, length)`. -/
def bytesVal (l : Loc) (len : Nat) : Val := .pair (.lit (.loc l)) (.lit (.int len))

/-! ## Pure specification and round-trip -/

/-- Pure model of `delta` encoding: difference each byte against the running previous value,
reduced mod 256. -/
def deltaEnc : Int → List Int → List Int
  | _, [] => []
  | prev, c :: cs => (c - prev + 256) % 256 :: deltaEnc c cs

/-- Pure model of `delta` decoding: the inverse prefix-sum. -/
def deltaDec : Int → List Int → List Int
  | _, [] => []
  | prev, d :: ds => (prev + d) % 256 :: deltaDec ((prev + d) % 256) ds

/-- The round-trip identity on the pure models: decoding the encoding is the identity on any list of
bytes (values in `[0, 256)`), for any starting `prev`. -/
theorem deltaDec_deltaEnc (cs : List Int) (h : ∀ x ∈ cs, 0 ≤ x ∧ x < 256) :
    ∀ prev, deltaDec prev (deltaEnc prev cs) = cs := by
  induction cs with
  | nil => intro prev; rfl
  | cons c cs ih =>
    intro prev
    have hc := h c (by simp)
    have key : (prev + (c - prev + 256) % 256) % 256 = c := by omega
    simp only [deltaEnc, deltaDec, key]
    exact congrArg (c :: ·) (ih (fun x hx => h x (by simp [hx])) c)

@[simp] theorem deltaEnc_length (prev : Int) (cs : List Int) :
    (deltaEnc prev cs).length = cs.length := by
  induction cs generalizing prev with
  | nil => rfl
  | cons c cs ih => simp [deltaEnc, ih]

@[simp] theorem deltaDec_length (prev : Int) (ds : List Int) :
    (deltaDec prev ds).length = ds.length := by
  induction ds generalizing prev with
  | nil => rfl
  | cons d ds ih => simp [deltaDec, ih]

/-- Encoding one more byte appends one output element differenced against the running last byte. -/
theorem deltaEnc_snoc (prev : Int) (xs : List Int) (y : Int) :
    deltaEnc prev (xs ++ [y]) = deltaEnc prev xs ++ [(y - xs.getLastD prev + 256) % 256] := by
  induction xs generalizing prev with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, deltaEnc, ih, List.getLastD_cons]

/-- Every encoded delta lies in `[0, 256)`. -/
theorem deltaEnc_mem_range (prev : Int) (l : List Int) :
    ∀ x ∈ deltaEnc prev l, 0 ≤ x ∧ x < 256 := by
  induction l generalizing prev with
  | nil => intro x hx; simp [deltaEnc] at hx
  | cons a as ih =>
    intro x hx
    simp only [deltaEnc, List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · exact ih _ x hx

/-- Decoding one more byte appends one output element: the prefix-sum against the running last decoded
byte. -/
theorem deltaDec_snoc (prev : Int) (xs : List Int) (y : Int) :
    deltaDec prev (xs ++ [y]) =
      deltaDec prev xs ++ [((deltaDec prev xs).getLastD prev + y) % 256] := by
  induction xs generalizing prev with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, deltaDec, ih, List.getLastD_cons]

/-- Every decoded byte lies in `[0, 256)` (each is a `% 256`). -/
theorem deltaDec_mem_range (prev : Int) (l : List Int) :
    ∀ x ∈ deltaDec prev l, 0 ≤ x ∧ x < 256 := by
  induction l generalizing prev with
  | nil => intro x hx; simp [deltaDec] at hx
  | cons a as ih =>
    intro x hx
    simp only [deltaDec, List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · exact ih _ x hx

/-- `delta` compression.  Mirrors `Codec.Delta.compress`:
```ocaml
let compress b =
  let n = Bytes.length b in
  let out = Bytes.create n in
  let prev = ref 0 in
  for i = 0 to n - 1 do
    let c = Char.code (Bytes.get b i) in
    Bytes.set out i (Char.unsafe_chr ((c - !prev) land 0xff));
    prev := c
  done;
  out
```
-/
def deltaCompress : Val := hl_val%
  λ b,
    let n := snd(b);
    let src := fst(b);
    let out := allocn(n, #0);
    let prev := ref(#0);
    let loop := (rec go i :=
      if i < n then
        let c := !(src +ₗ i);
        (out +ₗ i) ← (c - !prev + #256) % #256;
        prev ← c;
        let i' := i + #1;
        go i'
      else #());
    loop #0;
    (out, n)

/-- `delta` decompression.  Mirrors `Codec.Delta.decompress`:
```ocaml
let decompress b =
  let n = Bytes.length b in
  let out = Bytes.create n in
  let prev = ref 0 in
  for i = 0 to n - 1 do
    let d = Char.code (Bytes.get b i) in
    let c = (!prev + d) land 0xff in
    Bytes.set out i (Char.unsafe_chr c);
    prev := c
  done;
  out
```
-/
def deltaDecompress : Val := hl_val%
  λ b,
    let n := snd(b);
    let src := fst(b);
    let out := allocn(n, #0);
    let prev := ref(#0);
    let loop := (rec go i :=
      if i < n then
        let d := !(src +ₗ i);
        let c := (!prev + d) % #256;
        (out +ₗ i) ← c;
        prev ← c;
        let i' := i + #1;
        go i'
      else #());
    loop #0;
    (out, n)

end Iris.HeapLang.Codec

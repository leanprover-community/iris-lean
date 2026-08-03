module

public import IrisDoNightly.Codec.Basic
import Std.Tactic.Do
import Std.Internal.Do

/-! # The `lzss` codec — pure model (LZ77 token language + decoder) -/

open Lean.Order Std.Internal.Do
open Iris.HeapLang

namespace Iris.HeapLang.Ax

/-- An LZSS token: a literal run, or a back-reference `copy off len` copying `len` bytes starting
`off` positions from the current end of the output (so `off < len` overlaps, à la RLE). -/
public inductive Tok where
  | lit  (bytes : List Int)
  | copy (off len : Nat)

@[expose] public section

/-- Overlapping back-copy: append, `len` times, the byte sitting `off` positions from the end of the
growing buffer.  The read index `acc.length - off` is recomputed each step, so once `acc` has grown
the copy can read bytes it just wrote — exactly the LZ77/RLE overlap. -/
def copyBack (off : Nat) : Nat → List Int → List Int
  | 0,     acc => acc
  | k + 1, acc => copyBack off k (acc ++ [acc.getD (acc.length - off) 0])

/-- The pure `lzss` decoder core: fold the token stream over an output accumulator. -/
def lzssDecodeAux : List Tok → List Int → List Int
  | [],                 acc => acc
  | Tok.lit bs :: ts,   acc => lzssDecodeAux ts (acc ++ bs)
  | Tok.copy o l :: ts, acc => lzssDecodeAux ts (copyBack o l acc)

def lzssDecode (ts : List Tok) : List Int := lzssDecodeAux ts []

/-- Encode an `lzss` token as a `Val`: a literal run is `injL` of the byte-list, a back-reference is
`injR (offset, length)`. -/
def tokVal : Tok → Val
  | Tok.lit bs => .injL (vList bs)
  | Tok.copy off len => .injR (.pair (byteVal off) (byteVal len))

/-- Encode a token stream as a `Val` cons-list. -/
def tokList : List Tok → Val
  | [] => .injL (.lit .unit)
  | t :: ts => .injR (.pair (tokVal t) (tokList ts))

/-- Well-formedness of a token stream against a starting buffer: every back-reference stays in range
(`off ≤ length` of the buffer decoded so far).  This is the `Factors` safety invariant the untrusted
compressor must maintain — and *all* it must maintain for the decoder to match its pure model. -/
def WF : List Tok → List Int → Prop
  | [], _ => True
  | Tok.lit bs :: ts, acc => WF ts (acc ++ bs)
  | Tok.copy off len :: ts, acc => off ≤ acc.length ∧ WF ts (copyBack off len acc)

end

end Iris.HeapLang.Ax

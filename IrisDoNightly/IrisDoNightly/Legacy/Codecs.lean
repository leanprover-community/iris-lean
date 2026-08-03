module

public import IrisDoNightly.Legacy.CodecPrelude
public import IrisDoNightly.Legacy.Delta

@[expose] public section

namespace Iris.HeapLang.Codec

open Iris.HeapLang

/-!
# HeapLang transcriptions of `Reference/codec.ml`

Each codec below mirrors its OCaml counterpart, using the stdlib models from `CodecPrelude`.  Since
our mutable arrays are unsized, helpers that OCaml calls with an inferred `Array.length` take the
length as an explicit argument.  `raise (Malformed _)` on malformed input becomes `assert(#false)`
(a stuck expression); it is never reached on well-formed / round-tripped input.
-/

/-! ## Shared primitives -/

/-- `run_length b i cap`: length (`1..cap`) of the run of `b.(i)` starting at `i`. -/
def runLength : Val := hl_val%
  λ b i cap,
    let n := &blen b;
    let c := &bget b i;
    (rec go r :=
      if ((i + r < n) && (r < cap)) && (&bget b (i + r) = c) then go (r + #1) else r) #1

/-- `common_prefix_length b p q cap`. -/
def commonPrefixLength : Val := hl_val%
  λ b p q cap,
    let n := &blen b;
    (rec go l :=
      if (((l < cap) && (p + l < n)) && (q + l < n)) && (&bget b (p + l) = &bget b (q + l))
      then go (l + #1) else l) #0

/-- `byte_histogram b`: a fresh 256-cell array of byte counts. -/
def byteHistogram : Val := hl_val%
  λ b,
    let counts := allocn(#256, #0);
    let n := &blen b;
    (rec go i :=
      if i < n then
        (let c := &bget b i;
         (counts +ₗ c) ← (!(counts +ₗ c) + #1);
         go (i + #1))
      else #()) #0;
    counts

/-- `exclusive_prefix_sums a` for an array `a` of length `n`. -/
def exclusivePrefixSums : Val := hl_val%
  λ a n,
    let out := allocn(n, #0);
    let acc := ref(#0);
    (rec go i :=
      if i < n then
        ((out +ₗ i) ← !acc;
         acc ← (!acc + !(a +ₗ i));
         go (i + #1))
      else #()) #0;
    out

/-- `bit_at b pos`: the `pos`-th bit of `b`, MSB-first within each byte. -/
def bitAt : Val := hl_val%
  λ b pos, (&bget b (pos >>> #3) >>> (#7 - (pos &&& #7))) &&& #1

/-- `index_of table c`: least `r < n` with `table.(r) = c`, else `n`. -/
def indexOf : Val := hl_val%
  λ table n c,
    (rec go r := if (r < n) && (~(!(table +ₗ r) = c)) then go (r + #1) else r) #0

/-- `move_to_front table r`: move `table.(r)` to index 0, shifting `table.(0..r)` up; return it. -/
def moveToFront : Val := hl_val%
  λ table r,
    let c := !(table +ₗ r);
    (rec go j := if #1 ≤ j then ((table +ₗ j) ← !(table +ₗ (j - #1)); go (j - #1)) else #()) r;
    (table +ₗ #0) ← c;
    c

/-- `add_u16 buf v`. -/
def addU16 : Val := hl_val%
  λ buf v, &bufAddByte buf ((v >>> #8) &&& #255); &bufAddByte buf (v &&& #255)

/-- `get_u16 b off`. -/
def getU16 : Val := hl_val%
  λ b off, (&bget b off <<< #8) ||| &bget b (off + #1)

/-- `add_u32 buf v`. -/
def addU32 : Val := hl_val%
  λ buf v,
    &bufAddByte buf ((v >>> #24) &&& #255);
    &bufAddByte buf ((v >>> #16) &&& #255);
    &bufAddByte buf ((v >>> #8) &&& #255);
    &bufAddByte buf (v &&& #255)

/-- `get_u32 b off`. -/
def getU32 : Val := hl_val%
  λ b off,
    (((&bget b off <<< #24) ||| (&bget b (off + #1) <<< #16))
      ||| (&bget b (off + #2) <<< #8)) ||| &bget b (off + #3)

/-! ## `mtf` — move-to-front -/

/-- `Mtf.fresh_table ()` = `Array.init 256 (fun i -> i)`. -/
def mtfFreshTable : Val := hl_val%
  λ u,
    let t := allocn(#256, #0);
    (rec go i := if i < #256 then ((t +ₗ i) ← i; go (i + #1)) else #()) #0;
    t

/-- `Mtf.compress`. -/
def mtfCompress : Val := hl_val%
  λ b,
    let n := &blen b;
    let out := &bcreate n;
    let table := &mtfFreshTable #();
    (rec go k :=
      if k < n then
        (let c := &bget b k;
         let r := &indexOf table #256 c;
         &bset out k r;
         &moveToFront table r;
         go (k + #1))
      else #()) #0;
    out

/-- `Mtf.decompress`. -/
def mtfDecompress : Val := hl_val%
  λ b,
    let n := &blen b;
    let out := &bcreate n;
    let table := &mtfFreshTable #();
    (rec go k :=
      if k < n then
        (let r := &bget b k;
         &bset out k (&moveToFront table r);
         go (k + #1))
      else #()) #0;
    out

/-! ## `rle` — run-length (PackBits-style) -/

/-- `Rle.compress`. -/
def rleCompress : Val := hl_val%
  λ b,
    let n := &blen b;
    let out := &bufCreate ((n + (n / #128)) + #1);
    let emitLiterals := (λ lo hi,
      (rec go p :=
        if p < hi then
          (let count := &minV #128 (hi - p);
           &bufAddByte out (count - #1);
           &bufAddSubbytes out b p count;
           go (p + count))
        else #()) lo);
    let i := ref(#0);
    let litStart := ref(#0);
    (rec loop u :=
      if !i < n then
        (let run := &runLength b (!i) #128;
         (if #2 ≤ run then
            (emitLiterals (!litStart) (!i);
             &bufAddByte out (#128 ||| (run - #1));
             &bufAddByte out (&bget b (!i));
             i ← (!i + run);
             litStart ← (!i))
          else i ← (!i + #1));
         loop #())
      else #()) #();
    emitLiterals (!litStart) (!i);
    &bufToBytes out

/-- `Rle.decompress`. -/
def rleDecompress : Val := hl_val%
  λ b,
    let n := &blen b;
    let out := &bufCreate (n * #2);
    let i := ref(#0);
    (rec loop u :=
      if !i < n then
        (let ctrl := &bget b (!i);
         i ← (!i + #1);
         (if #128 ≤ ctrl then
            (let count := (ctrl - #128) + #1;
             let c := &bget b (!i);
             i ← (!i + #1);
             (rec rep j := if j < count then (&bufAddByte out c; rep (j + #1)) else #()) #0)
          else
            (let count := ctrl + #1;
             &bufAddSubbytes out b (!i) count;
             i ← (!i + count)));
         loop #())
      else #()) #();
    &bufToBytes out

/-! ## `lzss` — Storer–Szymanski LZ with a bounded hash chain

Constants: `min_match = 3`, `max_match = 258`, `max_offset = 65535`, `literal_run_max = 256`,
`hash_size = 2¹⁵ = 32768`, `hash_mask = 32767`, `max_chain = 128`. -/

/-- `Lzss.compress`. -/
def lzssCompress : Val := hl_val%
  λ b,
    let n := &blen b;
    let out := &bufCreate ((n + (n / #8)) + #16);
    let head := allocn(#32768, #(-1 : Int));
    let prev := allocn(&maxV #1 n, #(-1 : Int));
    let hash := (λ p,
      (((&bget b p * #506832829) + (&bget b (p + #1) * #65599)) + &bget b (p + #2)) &&& #32767);
    let insert := (λ p, let h := hash p; (prev +ₗ p) ← !(head +ₗ h); (head +ₗ h) ← p);
    let litStart := ref(#0);
    let flushLiterals := (λ hi,
      (rec go p :=
        if p < hi then
          (let count := &minV #256 (hi - p);
           &bufAddByte out #0;
           &bufAddByte out (count - #1);
           &bufAddSubbytes out b p count;
           go (p + count))
        else #()) (!litStart);
      litStart ← hi);
    let i := ref(#0);
    (rec loop u :=
      if !i < n then
        ((if n < (!i + #3) then i ← (!i + #1)
          else
            (let cand := ref(!(head +ₗ hash (!i)));
             let bestLen := ref(#0);
             let bestPos := ref(#(-1 : Int));
             let chain := ref(#128);
             let limit := &minV #258 (n - !i);
             (rec inner u :=
               if (#0 ≤ !cand) && (#0 < !chain) then
                 ((if (!i - !cand) ≤ #65535 then
                     (let l := &commonPrefixLength b (!cand) (!i) limit;
                      (if !bestLen < l then (bestLen ← l; bestPos ← (!cand)) else #()))
                   else #());
                  cand ← !(prev +ₗ !cand);
                  chain ← (!chain - #1);
                  inner #())
               else #()) #();
             (if #3 ≤ !bestLen then
                (flushLiterals (!i);
                 let offset := !i - !bestPos;
                 &bufAddByte out #1;
                 &addU16 out offset;
                 &bufAddByte out (!bestLen - #3);
                 let stop := !i + !bestLen;
                 (rec ins u :=
                   if !i < stop then
                     ((if (!i + #3) ≤ n then insert (!i) else #()); i ← (!i + #1); ins #())
                   else #()) #();
                 litStart ← (!i))
              else (insert (!i); i ← (!i + #1)))));
         loop #())
      else #()) #();
    flushLiterals n;
    &bufToBytes out

/-- `Lzss.decompress`. -/
def lzssDecompress : Val := hl_val%
  λ b,
    let n := &blen b;
    let out := &bufCreate (n * #3);
    let i := ref(#0);
    (rec loop u :=
      if !i < n then
        (let tag := &bget b (!i);
         i ← (!i + #1);
         (if tag = #0 then
            (let count := &bget b (!i) + #1;
             i ← (!i + #1);
             &bufAddSubbytes out b (!i) count;
             i ← (!i + count))
          else
            (let offset := &getU16 b (!i);
             let len := &bget b (!i + #2) + #3;
             i ← (!i + #3);
             let src := &bufLength out - offset;
             (rec cp k := if k < len then (&bufAddByte out (&bufNth out (src + k)); cp (k + #1)) else #()) #0));
         loop #())
      else #()) #();
    &bufToBytes out

/-! ## `bwt` — blocked Burrows–Wheeler transform

`block_size = 8192`.  OCaml's `Array.sort` (with the rank comparator) becomes an insertion sort
`sortBy` parameterised by a comparator returning `-1/0/1`. -/

/-- Three-way integer comparison, like OCaml `compare` on ints. -/
def cmpInt : Val := hl_val% λ x y, if x < y then #(-1 : Int) else (if y < x then #1 else #0)

/-- In-place insertion sort of the length-`n` array `arr` by comparator `cmp` (`cmp x y > 0` ⇒ `x`
after `y`). -/
def sortBy : Val := hl_val%
  λ cmp arr n,
    (rec outer i :=
      if i < n then
        (let key := !(arr +ₗ i);
         (rec inner j :=
           if (#0 ≤ j) && (#0 < cmp (!(arr +ₗ j)) key) then
             ((arr +ₗ (j + #1)) ← !(arr +ₗ j); inner (j - #1))
           else (arr +ₗ (j + #1)) ← key) (i - #1);
         outer (i + #1))
      else #()) #1

/-- `suffix_array_cyclic s` for a length-`n` block, by prefix doubling. -/
def suffixArrayCyclic : Val := hl_val%
  λ s n,
    let sa := allocn(n, #0);
    let rank := allocn(n, #0);
    let tmp := allocn(n, #0);
    (rec ini i := if i < n then ((sa +ₗ i) ← i; (rank +ₗ i) ← &bget s i; ini (i + #1)) else #()) #0;
    let k := ref(#1);
    let running := ref(#0 < n - #1);
    (rec loop u :=
      if !running then
        (let cmp := (λ x y,
           if ~(!(rank +ₗ x) = !(rank +ₗ y)) then &cmpInt (!(rank +ₗ x)) (!(rank +ₗ y))
           else &cmpInt (!(rank +ₗ ((x + !k) % n))) (!(rank +ₗ ((y + !k) % n))));
         &sortBy cmp sa n;
         (tmp +ₗ !(sa +ₗ #0)) ← #0;
         (rec fill i :=
           if i < n then
             ((tmp +ₗ !(sa +ₗ i)) ←
                (!(tmp +ₗ !(sa +ₗ (i - #1))) + (if cmp (!(sa +ₗ (i - #1))) (!(sa +ₗ i)) < #0 then #1 else #0));
              fill (i + #1))
           else #()) #1;
         &arrCopy tmp rank n;
         (if !(rank +ₗ !(sa +ₗ (n - #1))) = (n - #1) then running ← #false
          else (k ← (!k * #2); (if n ≤ !k then running ← #false else #())));
         loop #())
      else #()) #();
    sa

/-- `Bwt.compress`. -/
def bwtCompress : Val := hl_val%
  λ b,
    let n := &blen b;
    let out := &bufCreate ((n + (n / #512)) + #16);
    let off := ref(#0);
    (rec loop u :=
      if !off < n then
        (let len := &minV #8192 (n - !off);
         let s := &bsub b (!off) len;
         let sa := &suffixArrayCyclic s len;
         let last := &bcreate len;
         let idx := ref(#0);
         (rec go i :=
           if i < len then
             ((if !(sa +ₗ i) = #0 then idx ← i else #());
              &bset last i (&bget s (((!(sa +ₗ i) + len) - #1) % len));
              go (i + #1))
           else #()) #0;
         &addU32 out len;
         &addU32 out (!idx);
         &bufAddBytes out last;
         off ← (!off + len);
         loop #())
      else #()) #();
    &bufToBytes out

/-- `Bwt.decompress`. -/
def bwtDecompress : Val := hl_val%
  λ b,
    let n := &blen b;
    let out := &bufCreate (n * #2);
    let i := ref(#0);
    (rec loop u :=
      if !i < n then
        (let len := &getU32 b (!i);
         let idx := &getU32 b (!i + #4);
         i ← (!i + #8);
         let last := &bsub b (!i) len;
         i ← (!i + len);
         (if #0 < len then
            (let base := &exclusivePrefixSums (&byteHistogram last) #256;
             let lf := allocn(len, #0);
             let seen := allocn(#256, #0);
             (rec go j :=
               if j < len then
                 (let c := &bget last j;
                  (lf +ₗ j) ← (!(base +ₗ c) + !(seen +ₗ c));
                  (seen +ₗ c) ← (!(seen +ₗ c) + #1);
                  go (j + #1))
               else #()) #0;
             let res := &bcreate len;
             let p := ref(idx);
             (rec go2 kk :=
               if #0 ≤ kk then (&bset res kk (&bget last (!p)); p ← !(lf +ₗ !p); go2 (kk - #1)) else #())
               (len - #1);
             &bufAddBytes out res)
          else #());
         loop #())
      else #()) #();
    &bufToBytes out

/-! ## `huffman` — canonical Huffman with a stored fallback

Trees are `injl(sym)` (leaf) / `injr((left, right))` (node); the priority queue is a list
(`injl(#())` nil / `injr((hd, tl))` cons).  `max_code_len = 15`.  The decode step replaces OCaml's
`Hashtbl` with a linear scan over the ≤256 symbols. -/

/-- Append every live byte of buffer `src` to buffer `dst`. -/
def bufAddBuffer : Val := hl_val%
  λ dst src,
    let m := &bufLength src;
    (rec go j := if j < m then (&bufAddByte dst (&bufNth src j); go (j + #1)) else #()) #0

/-- `extract_min` on a nonempty `(freq, tree)` list: returns `(min, rest)`. -/
def huffExtractMin : Val := hl_val%
  λ lst,
    match lst with
    | injl(u) => (#0, injl(#()))
    | injr(p) =>
      (rec go best acc l :=
        match l with
        | injl(u2) => (best, acc)
        | injr(q) =>
          let x := fst(q);
          (if fst(x) < fst(best) then go x (injr((best, acc))) (snd(q))
           else go best (injr((x, acc))) (snd(q)))) (fst(p)) (injl(#())) (snd(p))

/-- Assign code lengths by tree depth (`max 1 depth` at each leaf). -/
def huffAssign : Val := hl_val%
  rec asg lens depth t :=
    match t with
    | injl(s) => (lens +ₗ s) ← &maxV #1 depth
    | injr(p) => (asg lens (depth + #1) (fst(p)); asg lens (depth + #1) (snd(p)))

/-- `Huffman.code_lengths freqs` (a 256-array of byte frequencies). -/
def huffCodeLengths : Val := hl_val%
  λ freqs,
    let lens := allocn(#256, #0);
    let pool := ref(injl(#()));
    (rec go s :=
      if #0 ≤ s then
        ((if #0 < !(freqs +ₗ s) then pool ← injr(((!(freqs +ₗ s), injl(s)), !pool)) else #());
         go (s - #1))
      else #()) #255;
    (match !pool with
     | injl(u) => #()
     | injr(p) =>
       (match snd(p) with
        | injl(u2) =>
          (match snd(fst(p)) with
           | injl(s) => (lens +ₗ s) ← #1
           | injr(pp) => #())
        | injr(p2) =>
          (let q := ref(!pool);
           (rec loop u :=
             match !q with
             | injl(u3) => #()
             | injr(qp) =>
               (match snd(qp) with
                | injl(u4) => #()
                | injr(qp2) =>
                  (let r1 := &huffExtractMin (!q);
                   let r2 := &huffExtractMin (snd(r1));
                   q ← injr(
                     (((fst(fst(r1)) + fst(fst(r2))), injr((snd(fst(r1)), snd(fst(r2))))), snd(r2)));
                   loop #()))) #();
           (match !q with
            | injl(u5) => #()
            | injr(rp) => &huffAssign lens #0 (snd(fst(rp)))))));
    lens

/-- `Huffman.canonical_codes lens`. -/
def huffCanonicalCodes : Val := hl_val%
  λ lens,
    let maxlen := ref(#0);
    (rec go s :=
      if s < #256 then ((if !maxlen < !(lens +ₗ s) then maxlen ← !(lens +ₗ s) else #()); go (s + #1))
      else #()) #0;
    let blCount := allocn((!maxlen + #1), #0);
    (rec go s :=
      if s < #256 then
        (let l := !(lens +ₗ s); (if #0 < l then (blCount +ₗ l) ← (!(blCount +ₗ l) + #1) else #());
         go (s + #1))
      else #()) #0;
    let nextCode := allocn((!maxlen + #1), #0);
    let code := ref(#0);
    (rec go bits :=
      if bits ≤ !maxlen then
        (code ← ((!code + !(blCount +ₗ (bits - #1))) <<< #1); (nextCode +ₗ bits) ← !code;
         go (bits + #1))
      else #()) #1;
    let codes := allocn(#256, #0);
    (rec go s :=
      if s < #256 then
        (let l := !(lens +ₗ s);
         (if #0 < l then ((codes +ₗ s) ← !(nextCode +ₗ l); (nextCode +ₗ l) ← (!(nextCode +ₗ l) + #1))
          else #());
         go (s + #1))
      else #()) #0;
    codes

/-- The stored (uncompressed) block form. -/
def huffStored : Val := hl_val%
  λ b,
    let out := &bufCreate (&blen b + #5);
    &bufAddByte out #0;
    &addU32 out (&blen b);
    &bufAddBytes out b;
    &bufToBytes out

/-- `Huffman.compress`. -/
def huffCompress : Val := hl_val%
  λ b,
    let n := &blen b;
    if n = #0 then &huffStored b
    else
      (let lens := &huffCodeLengths (&byteHistogram b);
       let maxlen := ref(#0);
       (rec go s :=
         if s < #256 then ((if !maxlen < !(lens +ₗ s) then maxlen ← !(lens +ₗ s) else #()); go (s + #1))
         else #()) #0;
       if #15 < !maxlen then &huffStored b
       else
         (let codes := &huffCanonicalCodes lens;
          let bits := &bufCreate (n + #16);
          let acc := ref(#0);
          let nbits := ref(#0);
          let put := (λ code len,
            (rec go k :=
              if #0 ≤ k then
                (acc ← ((!acc <<< #1) ||| ((code >>> k) &&& #1));
                 nbits ← (!nbits + #1);
                 (if !nbits = #8 then (&bufAddByte bits (!acc); acc ← #0; nbits ← #0) else #());
                 go (k - #1))
              else #()) (len - #1));
          (rec go i :=
            if i < n then (let c := &bget b i; put (!(codes +ₗ c)) (!(lens +ₗ c)); go (i + #1))
            else #()) #0;
          (if #0 < !nbits then &bufAddByte bits (!acc <<< (#8 - !nbits)) else #());
          let out := &bufCreate (&bufLength bits + #261);
          &bufAddByte out #1;
          &addU32 out n;
          (rec go s := if s < #256 then (&bufAddByte out (!(lens +ₗ s)); go (s + #1)) else #()) #0;
          &bufAddBuffer out bits;
          let result := &bufToBytes out;
          if (n + #5) ≤ &blen result then &huffStored b else result))

/-- Linear-scan reverse code lookup: least `s < n` with `lens.(s) = len ∧ codes.(s) = code`, else
`-1`.  (Replaces OCaml's `Hashtbl`.) -/
def huffFindSym : Val := hl_val%
  λ lens codes n len code,
    (rec go s :=
      if s < n then (if (!(lens +ₗ s) = len) && (!(codes +ₗ s) = code) then s else go (s + #1))
      else #(-1 : Int)) #0

/-- `Huffman.decompress`. -/
def huffDecompress : Val := hl_val%
  λ b,
    let n := &blen b;
    let flag := &bget b #0;
    if flag = #0 then
      (let len := &getU32 b #1; &bsub b #5 len)
    else
      (let count := &getU32 b #1;
       let lens := allocn(#256, #0);
       (rec go s := if s < #256 then ((lens +ₗ s) ← &bget b (#5 + s); go (s + #1)) else #()) #0;
       let codes := &huffCanonicalCodes lens;
       let dataOff := #5 + #256;
       let out := &bcreate count;
       let bitpos := ref(#0);
       let nextSymbol := (λ u,
         let code := ref(#0);
         let len := ref(#0);
         let found := ref(#(-1 : Int));
         (rec go u2 :=
           if !found < #0 then
             (let ab := (dataOff <<< #3) + !bitpos;
              bitpos ← (!bitpos + #1);
              code ← ((!code <<< #1) ||| &bitAt b ab);
              len ← (!len + #1);
              found ← &huffFindSym lens codes #256 (!len) (!code);
              go u2)
           else #()) #();
         !found);
       (rec go k := if k < count then (&bset out k (nextSymbol #()); go (k + #1)) else #()) #0;
       out)

/-! ## Combinators, codec records, and the composite stacks

A codec is a pair `(compress, decompress)` (the OCaml `name` field is dropped).  `chain` / `best_of`
build new codecs from a list of codecs; unlike OCaml's eager `let`, the composites are HeapLang
*expressions* that evaluate to a codec value. -/

/-- `chain codecs`: pipe the codecs; `decompress` runs them in reverse. -/
def chainCodec : Val := hl_val%
  λ codecs,
    ((λ x, &listFoldl (λ acc c, fst(c) acc) x codecs),
     (λ y, &listFoldl (λ acc c, snd(c) acc) y (&listRev codecs)))

/-- `best_of candidates`: try each, keep the smallest output, prepend a 1-byte winner tag;
`decompress` dispatches on the tag. -/
def bestOfCodec : Val := hl_val%
  λ candidates,
    ((λ x,
       let bestIdx := ref(#(-1 : Int));
       let bestOut := ref(&bcreate #0);
       let idx := ref(#0);
       (rec go l :=
         match l with
         | injl(u) => #()
         | injr(p) =>
           (let out := fst(fst(p)) x;
            (if (!bestIdx < #0) || (&blen out < &blen (!bestOut)) then (bestIdx ← !idx; bestOut ← out)
             else #());
            idx ← (!idx + #1);
            go (snd(p)))) candidates;
       let res := &bufCreate (&blen (!bestOut) + #1);
       &bufAddByte res (!bestIdx);
       &bufAddBytes res (!bestOut);
       &bufToBytes res),
     (λ y,
       let c := &listNth candidates (&bget y #0);
       snd(c) (&bsub y #1 (&blen y - #1))))

/-- Build a HeapLang codec-list expression from a Lean list of codec records. -/
def codecListExp : List Val → Exp
  | [] => hl% injl(#())
  | c :: cs => hl% injr((&c, &(codecListExp cs)))

/-- The base codec records. -/
def rle : Val := hl_val% (&rleCompress, &rleDecompress)
def lzss : Val := hl_val% (&lzssCompress, &lzssDecompress)
def mtf : Val := hl_val% (&mtfCompress, &mtfDecompress)
def huffman : Val := hl_val% (&huffCompress, &huffDecompress)
def delta : Val := hl_val% (&deltaCompress, &deltaDecompress)
def bwt : Val := hl_val% (&bwtCompress, &bwtDecompress)

/-- The composite stacks. -/
def mtfRle : Exp := hl% &chainCodec &(codecListExp [mtf, rle])
def bwtMtfRle : Exp := hl% &chainCodec &(codecListExp [bwt, mtf, rle])
def bzip : Exp := hl% &chainCodec &(codecListExp [bwt, mtf, rle, huffman])
def deltaRle : Exp := hl% &chainCodec &(codecListExp [delta, rle])

/-- `auto = best_of [rle; lzss; huffman; bzip]`.  `bzip` is bound by a `let` so it is a value when it
enters the candidate list. -/
def auto : Exp := hl%
  let bzipC := &chainCodec &(codecListExp [bwt, mtf, rle, huffman]);
  &bestOfCodec (injr((&rle, injr((&lzss, injr((&huffman, injr((bzipC, injl(#()))))))))))

end Iris.HeapLang.Codec

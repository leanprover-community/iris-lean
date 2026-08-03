exception Malformed of string

type t = {
  name : string;
  compress : bytes -> bytes;
  decompress : bytes -> bytes;
}

let add_u32 buf v =
  Buffer.add_char buf (Char.unsafe_chr ((v lsr 24) land 0xff));
  Buffer.add_char buf (Char.unsafe_chr ((v lsr 16) land 0xff));
  Buffer.add_char buf (Char.unsafe_chr ((v lsr 8) land 0xff));
  Buffer.add_char buf (Char.unsafe_chr (v land 0xff))

let get_u32 b off =
  if off + 4 > Bytes.length b then raise (Malformed "u32: out of bounds");
  (Char.code (Bytes.get b off) lsl 24)
  lor (Char.code (Bytes.get b (off + 1)) lsl 16)
  lor (Char.code (Bytes.get b (off + 2)) lsl 8)
  lor Char.code (Bytes.get b (off + 3))

let add_u16 buf v =
  Buffer.add_char buf (Char.unsafe_chr ((v lsr 8) land 0xff));
  Buffer.add_char buf (Char.unsafe_chr (v land 0xff))

let get_u16 b off =
  if off + 2 > Bytes.length b then raise (Malformed "u16: out of bounds");
  (Char.code (Bytes.get b off) lsl 8) lor Char.code (Bytes.get b (off + 1))

let byte_histogram b =
  let counts = Array.make 256 0 in
  Bytes.iter (fun c -> let s = Char.code c in counts.(s) <- counts.(s) + 1) b;
  counts

let exclusive_prefix_sums a =
  let out = Array.make (Array.length a) 0 in
  let acc = ref 0 in
  for i = 0 to Array.length a - 1 do
    out.(i) <- !acc;
    acc := !acc + a.(i)
  done;
  out

let bit_at b pos =
  (Char.code (Bytes.get b (pos lsr 3)) lsr (7 - (pos land 7))) land 1

let index_of table c =
  let n = Array.length table in
  let r = ref 0 in
  while !r < n && table.(!r) <> c do incr r done;
  !r

let move_to_front table r =
  let c = table.(r) in
  for j = r downto 1 do table.(j) <- table.(j - 1) done;
  table.(0) <- c;
  c

let run_length b i cap =
  let n = Bytes.length b in
  let c = Bytes.get b i in
  let r = ref 1 in
  while i + !r < n && !r < cap && Bytes.get b (i + !r) = c do incr r done;
  !r

let common_prefix_length b p q cap =
  let n = Bytes.length b in
  let l = ref 0 in
  while !l < cap && p + !l < n && q + !l < n && Bytes.get b (p + !l) = Bytes.get b (q + !l) do
    incr l
  done;
  !l

module Rle = struct
  let literal_tag_max = 128
  let repeat_max = 128

  let compress b =
    let n = Bytes.length b in
    let out = Buffer.create (n + (n / 128) + 1) in
    let emit_literals lo hi =
      let p = ref lo in
      while !p < hi do
        let count = min literal_tag_max (hi - !p) in
        Buffer.add_char out (Char.unsafe_chr (count - 1));
        Buffer.add_subbytes out b !p count;
        p := !p + count
      done
    in
    let i = ref 0 in
    let lit_start = ref 0 in
    while !i < n do
      let run = run_length b !i repeat_max in
      if run >= 2 then begin
        emit_literals !lit_start !i;
        Buffer.add_char out (Char.unsafe_chr (0x80 lor (run - 1)));
        Buffer.add_char out (Bytes.get b !i);
        i := !i + run;
        lit_start := !i
      end else
        incr i
    done;
    emit_literals !lit_start !i;
    Buffer.to_bytes out

  let decompress b =
    let n = Bytes.length b in
    let out = Buffer.create (n * 2) in
    let i = ref 0 in
    while !i < n do
      let ctrl = Char.code (Bytes.get b !i) in
      incr i;
      if ctrl >= 0x80 then begin
        let count = (ctrl - 0x80) + 1 in
        if !i >= n then raise (Malformed "rle: truncated repeat");
        let c = Bytes.get b !i in
        incr i;
        for _ = 1 to count do Buffer.add_char out c done
      end else begin
        let count = ctrl + 1 in
        if !i + count > n then raise (Malformed "rle: truncated literal");
        Buffer.add_subbytes out b !i count;
        i := !i + count
      end
    done;
    Buffer.to_bytes out
end

module Mtf = struct
  let fresh_table () = Array.init 256 (fun i -> i)

  let compress b =
    let n = Bytes.length b in
    let out = Bytes.create n in
    let table = fresh_table () in
    for k = 0 to n - 1 do
      let c = Char.code (Bytes.get b k) in
      let r = index_of table c in
      Bytes.set out k (Char.unsafe_chr r);
      ignore (move_to_front table r)
    done;
    out

  let decompress b =
    let n = Bytes.length b in
    let out = Bytes.create n in
    let table = fresh_table () in
    for k = 0 to n - 1 do
      let r = Char.code (Bytes.get b k) in
      Bytes.set out k (Char.unsafe_chr (move_to_front table r))
    done;
    out
end

module Lzss = struct
  let min_match = 3
  let max_match = min_match + 255
  let max_offset = 65535
  let literal_run_max = 256
  let hash_bits = 15
  let hash_size = 1 lsl hash_bits
  let hash_mask = hash_size - 1
  let max_chain = 128

  let compress b =
    let n = Bytes.length b in
    let out = Buffer.create (n + (n / 8) + 16) in
    let head = Array.make hash_size (-1) in
    let prev = Array.make (max 1 n) (-1) in
    let hash p =
      ((Char.code (Bytes.get b p) * 506832829)
       + (Char.code (Bytes.get b (p + 1)) * 65599)
       + Char.code (Bytes.get b (p + 2)))
      land hash_mask
    in
    let insert p =
      let h = hash p in
      prev.(p) <- head.(h);
      head.(h) <- p
    in
    let lit_start = ref 0 in
    let flush_literals hi =
      let p = ref !lit_start in
      while !p < hi do
        let count = min literal_run_max (hi - !p) in
        Buffer.add_char out '\000';
        Buffer.add_char out (Char.unsafe_chr (count - 1));
        Buffer.add_subbytes out b !p count;
        p := !p + count
      done;
      lit_start := hi
    in
    let i = ref 0 in
    while !i < n do
      if !i + min_match > n then incr i
      else begin
        let cand = ref head.(hash !i) in
        let best_len = ref 0 and best_pos = ref (-1) in
        let chain = ref max_chain in
        let limit = min max_match (n - !i) in
        while !cand >= 0 && !chain > 0 do
          if !i - !cand <= max_offset then begin
            let l = common_prefix_length b !cand !i limit in
            if l > !best_len then begin
              best_len := l;
              best_pos := !cand
            end
          end;
          cand := prev.(!cand);
          decr chain
        done;
        if !best_len >= min_match then begin
          flush_literals !i;
          let offset = !i - !best_pos in
          Buffer.add_char out '\001';
          add_u16 out offset;
          Buffer.add_char out (Char.unsafe_chr (!best_len - min_match));
          let stop = !i + !best_len in
          while !i < stop do
            if !i + min_match <= n then insert !i;
            incr i
          done;
          lit_start := !i
        end else begin
          insert !i;
          incr i
        end
      end
    done;
    flush_literals n;
    Buffer.to_bytes out

  let decompress b =
    let n = Bytes.length b in
    let out = Buffer.create (n * 3) in
    let i = ref 0 in
    while !i < n do
      let tag = Char.code (Bytes.get b !i) in
      incr i;
      if tag = 0 then begin
        if !i >= n then raise (Malformed "lzss: truncated literal header");
        let count = Char.code (Bytes.get b !i) + 1 in
        incr i;
        if !i + count > n then raise (Malformed "lzss: truncated literals");
        Buffer.add_subbytes out b !i count;
        i := !i + count
      end else if tag = 1 then begin
        if !i + 3 > n then raise (Malformed "lzss: truncated match");
        let offset = get_u16 b !i in
        let len = Char.code (Bytes.get b (!i + 2)) + min_match in
        i := !i + 3;
        let src = Buffer.length out - offset in
        if offset = 0 || src < 0 then raise (Malformed "lzss: bad back-reference");
        for k = 0 to len - 1 do
          Buffer.add_char out (Buffer.nth out (src + k))
        done
      end else
        raise (Malformed "lzss: bad tag")
    done;
    Buffer.to_bytes out
end

module Huffman = struct
  let max_code_len = 15

  type tree = Leaf of int | Node of tree * tree

  let code_lengths freqs =
    let lens = Array.make 256 0 in
    let pool = ref [] in
    for s = 0 to 255 do
      if freqs.(s) > 0 then pool := (freqs.(s), Leaf s) :: !pool
    done;
    (match !pool with
     | [] -> ()
     | [ (_, Leaf s) ] -> lens.(s) <- 1
     | _ ->
       let extract_min lst =
         let rec go ((bf, _) as best) acc = function
           | [] -> best, acc
           | ((f, _) as x) :: tl ->
             if f < bf then go x (best :: acc) tl else go best (x :: acc) tl
         in
         match lst with x :: tl -> go x [] tl | [] -> assert false
       in
       let q = ref !pool in
       while (match !q with _ :: _ :: _ -> true | _ -> false) do
         let (f1, t1), rest = extract_min !q in
         let (f2, t2), rest2 = extract_min rest in
         q := (f1 + f2, Node (t1, t2)) :: rest2
       done;
       let _, root = List.hd !q in
       let rec assign depth = function
         | Leaf s -> lens.(s) <- max 1 depth
         | Node (l, r) -> assign (depth + 1) l; assign (depth + 1) r
       in
       assign 0 root);
    lens

  let canonical_codes lens =
    let maxlen = Array.fold_left max 0 lens in
    let bl_count = Array.make (maxlen + 1) 0 in
    Array.iter (fun l -> if l > 0 then bl_count.(l) <- bl_count.(l) + 1) lens;
    let next_code = Array.make (maxlen + 1) 0 in
    let code = ref 0 in
    for bits = 1 to maxlen do
      code := (!code + bl_count.(bits - 1)) lsl 1;
      next_code.(bits) <- !code
    done;
    let codes = Array.make 256 0 in
    for s = 0 to 255 do
      if lens.(s) > 0 then begin
        codes.(s) <- next_code.(lens.(s));
        next_code.(lens.(s)) <- next_code.(lens.(s)) + 1
      end
    done;
    codes

  let stored b =
    let out = Buffer.create (Bytes.length b + 5) in
    Buffer.add_char out '\000';
    add_u32 out (Bytes.length b);
    Buffer.add_bytes out b;
    Buffer.to_bytes out

  let compress b =
    let n = Bytes.length b in
    if n = 0 then stored b
    else begin
      let lens = code_lengths (byte_histogram b) in
      if Array.fold_left max 0 lens > max_code_len then stored b
      else begin
        let codes = canonical_codes lens in
        let bits = Buffer.create (n + 16) in
        let acc = ref 0 and nbits = ref 0 in
        let put code len =
          for k = len - 1 downto 0 do
            acc := (!acc lsl 1) lor ((code lsr k) land 1);
            incr nbits;
            if !nbits = 8 then begin
              Buffer.add_char bits (Char.unsafe_chr !acc);
              acc := 0;
              nbits := 0
            end
          done
        in
        Bytes.iter (fun c -> let s = Char.code c in put codes.(s) lens.(s)) b;
        if !nbits > 0 then Buffer.add_char bits (Char.unsafe_chr (!acc lsl (8 - !nbits)));
        let out = Buffer.create (Buffer.length bits + 261) in
        Buffer.add_char out '\001';
        add_u32 out n;
        for s = 0 to 255 do Buffer.add_char out (Char.unsafe_chr lens.(s)) done;
        Buffer.add_buffer out bits;
        let result = Buffer.to_bytes out in
        if Bytes.length result >= n + 5 then stored b else result
      end
    end

  let decompress b =
    let n = Bytes.length b in
    if n < 1 then raise (Malformed "huffman: empty");
    match Char.code (Bytes.get b 0) with
    | 0 ->
      let len = get_u32 b 1 in
      if 5 + len > n then raise (Malformed "huffman: truncated stored data");
      Bytes.sub b 5 len
    | 1 ->
      if n < 5 + 256 then raise (Malformed "huffman: truncated header");
      let count = get_u32 b 1 in
      let lens = Array.init 256 (fun s -> Char.code (Bytes.get b (5 + s))) in
      let codes = canonical_codes lens in
      let maxlen = Array.fold_left max 0 lens in
      let tbl = Hashtbl.create 512 in
      for s = 0 to 255 do
        if lens.(s) > 0 then Hashtbl.replace tbl (lens.(s), codes.(s)) s
      done;
      let data_off = 5 + 256 in
      let out = Bytes.create count in
      let bitpos = ref 0 in
      let next_symbol () =
        let code = ref 0 and len = ref 0 and found = ref (-1) in
        while !found < 0 do
          let abs = (data_off lsl 3) + !bitpos in
          if abs lsr 3 >= n then raise (Malformed "huffman: truncated data");
          incr bitpos;
          code := (!code lsl 1) lor bit_at b abs;
          incr len;
          if !len > maxlen then raise (Malformed "huffman: invalid code");
          match Hashtbl.find_opt tbl (!len, !code) with
          | Some s -> found := s
          | None -> ()
        done;
        !found
      in
      for k = 0 to count - 1 do
        Bytes.set out k (Char.unsafe_chr (next_symbol ()))
      done;
      out
    | _ -> raise (Malformed "huffman: bad flag")
end

module Delta = struct
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
end

module Bwt = struct
  let block_size = 8192

  let suffix_array_cyclic s =
    let n = Bytes.length s in
    let sa = Array.init n (fun i -> i) in
    let rank = Array.init n (fun i -> Char.code (Bytes.get s i)) in
    let tmp = Array.make n 0 in
    let k = ref 1 in
    let running = ref (n > 1) in
    while !running do
      let cmp a b =
        if rank.(a) <> rank.(b) then compare rank.(a) rank.(b)
        else compare rank.((a + !k) mod n) rank.((b + !k) mod n)
      in
      Array.sort cmp sa;
      tmp.(sa.(0)) <- 0;
      for i = 1 to n - 1 do
        tmp.(sa.(i)) <- tmp.(sa.(i - 1)) + (if cmp sa.(i - 1) sa.(i) < 0 then 1 else 0)
      done;
      Array.blit tmp 0 rank 0 n;
      if rank.(sa.(n - 1)) = n - 1 then running := false
      else begin
        k := !k * 2;
        if !k >= n then running := false
      end
    done;
    sa

  let compress b =
    let n = Bytes.length b in
    let out = Buffer.create (n + (n / 512) + 16) in
    let off = ref 0 in
    while !off < n do
      let len = min block_size (n - !off) in
      let s = Bytes.sub b !off len in
      let sa = suffix_array_cyclic s in
      let last = Bytes.create len in
      let idx = ref 0 in
      for i = 0 to len - 1 do
        if sa.(i) = 0 then idx := i;
        Bytes.set last i (Bytes.get s ((sa.(i) + len - 1) mod len))
      done;
      add_u32 out len;
      add_u32 out !idx;
      Buffer.add_bytes out last;
      off := !off + len
    done;
    Buffer.to_bytes out

  let decompress b =
    let n = Bytes.length b in
    let out = Buffer.create (n * 2) in
    let i = ref 0 in
    while !i < n do
      let len = get_u32 b !i in
      let idx = get_u32 b (!i + 4) in
      i := !i + 8;
      if !i + len > n then raise (Malformed "bwt: truncated block");
      let last = Bytes.sub b !i len in
      i := !i + len;
      if len > 0 then begin
        if idx >= len then raise (Malformed "bwt: bad index");
        let base = exclusive_prefix_sums (byte_histogram last) in
        let lf = Array.make len 0 in
        let seen = Array.make 256 0 in
        for j = 0 to len - 1 do
          let c = Char.code (Bytes.get last j) in
          lf.(j) <- base.(c) + seen.(c);
          seen.(c) <- seen.(c) + 1
        done;
        let res = Bytes.create len in
        let p = ref idx in
        for k = len - 1 downto 0 do
          Bytes.set res k (Bytes.get last !p);
          p := lf.(!p)
        done;
        Buffer.add_bytes out res
      end
    done;
    Buffer.to_bytes out
end

let rle = { name = "rle"; compress = Rle.compress; decompress = Rle.decompress }
let lzss = { name = "lzss"; compress = Lzss.compress; decompress = Lzss.decompress }
let mtf = { name = "mtf"; compress = Mtf.compress; decompress = Mtf.decompress }
let huffman = { name = "huffman"; compress = Huffman.compress; decompress = Huffman.decompress }
let delta = { name = "delta"; compress = Delta.compress; decompress = Delta.decompress }
let bwt = { name = "bwt"; compress = Bwt.compress; decompress = Bwt.decompress }

let chain codecs =
  let name = String.concat "+" (List.map (fun c -> c.name) codecs) in
  let compress x = List.fold_left (fun acc c -> c.compress acc) x codecs in
  let decompress y =
    List.fold_left (fun acc c -> c.decompress acc) y (List.rev codecs)
  in
  { name; compress; decompress }

let best_of ~name candidates =
  let arr = Array.of_list candidates in
  if Array.length arr < 1 || Array.length arr > 256 then invalid_arg "best_of";
  let compress x =
    let best = ref (-1, Bytes.empty) in
    Array.iteri
      (fun i c ->
        let out = c.compress x in
        let chosen, prev = !best in
        if chosen < 0 || Bytes.length out < Bytes.length prev then best := (i, out))
      arr;
    let i, out = !best in
    let res = Bytes.create (Bytes.length out + 1) in
    Bytes.set res 0 (Char.unsafe_chr i);
    Bytes.blit out 0 res 1 (Bytes.length out);
    res
  in
  let decompress y =
    if Bytes.length y < 1 then raise (Malformed (name ^ ": empty"));
    let i = Char.code (Bytes.get y 0) in
    if i >= Array.length arr then raise (Malformed (name ^ ": bad tag"));
    arr.(i).decompress (Bytes.sub y 1 (Bytes.length y - 1))
  in
  { name; compress; decompress }

let mtf_rle = chain [ mtf; rle ]
let bwt_mtf_rle = chain [ bwt; mtf; rle ]
let bzip = { (chain [ bwt; mtf; rle; huffman ]) with name = "bzip" }
let delta_rle = chain [ delta; rle ]
let auto = best_of ~name:"auto" [ rle; lzss; huffman; bzip ]

let all =
  [ rle; lzss; mtf; huffman; delta; bwt; mtf_rle; bwt_mtf_rle; bzip; delta_rle; auto ]

let find name =
  match List.find_opt (fun c -> c.name = name) all with
  | Some c -> c
  | None -> invalid_arg ("unknown codec: " ^ name)

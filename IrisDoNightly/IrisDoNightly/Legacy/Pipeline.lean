module

public import IrisDoNightly.Legacy.Codecs

@[expose] public section

namespace Iris.HeapLang.Codec

open Iris.HeapLang

/-!
# HeapLang transcription of `Reference/pipeline.ml` (the concurrent core)

HeapLang provides `fork`, `cmpXchg` (CAS), and mutable references — enough to model OCaml's
`Domain`, `Mutex`, `Condition`, and `Atomic`:

* **`Domain.spawn` / `Domain.join`** → `spawn` forks a thread that writes its result into a cell;
  `join` busy-waits for it (the standard Iris spawn/join idiom).
* **`Mutex`** → a CAS spinlock (`false` = free).
* **`Atomic`** → a reference; `get` is a load, `compare_and_set` is `cmpXchg`.
* **`Condition.wait`** inside a `while guard do wait done` loop → a lock / recheck / release
  busy-wait: acquire, test the guard, and if it still holds, release and retry.  This preserves
  mutual exclusion and progress (the behavioural contract) without a native condition variable.

`msg` is `injl(#())` for `Stop` and `injr((seq, data))` for `Chunk {seq; data}`.
-/

/-! ## Concurrency primitives -/

/-- A fresh CAS spinlock (`false` = unlocked). -/
def newLock : Val := hl_val% λ u, ref(#false)
/-- Acquire a spinlock. -/
def acquire : Val := hl_val% rec acq lk := if cas(lk, #false, #true) then #() else acq lk
/-- Release a spinlock. -/
def release : Val := hl_val% λ lk, lk ← #false

/-- `Domain.spawn f`: fork `f ()` into a result cell, returned as a join handle. -/
def spawn : Val := hl_val%
  λ f, let c := ref(none()); fork(c ← some(f #())); c
/-- `Domain.join`: busy-wait for the handle's result. -/
def join : Val := hl_val%
  rec jn c := match !c with | some(x) => x | none() => jn c

/-! ## `Bqueue` — bounded blocking FIFO

`q = ((slots, capacity, lock), state)` where `state ↦ (head, tail, size)`. -/

/-- `Bqueue.create capacity`. -/
def bqueueCreate : Val := hl_val%
  λ capacity,
    let slots := allocn(capacity, injl(#()));
    let lock := &newLock #();
    let state := ref((#0, (#0, #0)));
    ((slots, (capacity, lock)), state)

/-- `Bqueue.push q v` (blocks while full). -/
def bqueuePush : Val := hl_val%
  λ q v,
    let slots := fst(fst(q));
    let capacity := fst(snd(fst(q)));
    let lock := snd(snd(fst(q)));
    let state := snd(q);
    (rec loop u :=
      (&acquire lock;
       let s := !state;
       let head := fst(s);
       let tail := fst(snd(s));
       let size := snd(snd(s));
       if size = capacity then (&release lock; loop #())
       else
         ((slots +ₗ tail) ← v;
          state ← (head, (((tail + #1) % capacity), (size + #1)));
          &release lock))) #()

/-- `Bqueue.pop q` (blocks while empty). -/
def bqueuePop : Val := hl_val%
  λ q,
    let slots := fst(fst(q));
    let capacity := fst(snd(fst(q)));
    let lock := snd(snd(fst(q)));
    let state := snd(q);
    (rec loop u :=
      (&acquire lock;
       let s := !state;
       let head := fst(s);
       let tail := fst(snd(s));
       let size := snd(snd(s));
       if size = #0 then (&release lock; loop #())
       else
         (let v := !(slots +ₗ head);
          state ← (((head + #1) % capacity), (tail, (size - #1)));
          &release lock;
          v))) #()

/-! ## `Stager` — order-preserving reassembly

`s = (slots, window, total, lock, out, next, order)` (7-tuple); `next` is the atomic next-to-emit
reference, `order` a reference to the emitted-sequence list, `out` the output `Buffer`. -/

/-- `Stager.create window total`. -/
def stagerCreate : Val := hl_val%
  λ window total,
    let window := &maxV #1 window;
    let slots := allocn(window, none());
    let lock := &newLock #();
    let out := &bufCreate ((total * #8) + #16);
    let next := ref(#0);
    let order := ref(injl(#()));
    (slots, (window, (total, (lock, (out, (next, order))))))

/-- `Stager.deposit s seq data` (blocks until the reorder window has room). -/
def stagerDeposit : Val := hl_val%
  λ s seq data,
    let slots := fst(s);
    let window := fst(snd(s));
    let lock := fst(snd(snd(snd(s))));
    let next := fst(snd(snd(snd(snd(snd(s))))));
    (rec loop u :=
      (&acquire lock;
       if window ≤ (seq - !next) then (&release lock; loop #())
       else ((slots +ₗ (seq % window)) ← some(data); &release lock))) #()

/-- `add_frame buf data`: a length-prefixed frame. -/
def addFrame : Val := hl_val%
  λ buf data, &addU32 buf (&blen data); &bufAddBytes buf data

/-- `Stager.collect s`: emit slots in ascending order until `total` are done. -/
def stagerCollect : Val := hl_val%
  λ s,
    let slots := fst(s);
    let window := fst(snd(s));
    let total := fst(snd(snd(s)));
    let lock := fst(snd(snd(snd(s))));
    let out := fst(snd(snd(snd(snd(s)))));
    let next := fst(snd(snd(snd(snd(snd(s))))));
    let order := snd(snd(snd(snd(snd(snd(s))))));
    (rec loop u :=
      let cur := !next;
      if total ≤ cur then #()
      else
        (let idx := cur % window;
         &acquire lock;
         (rec waitFilled v :=
           match !(slots +ₗ idx) with
           | none() => (&release lock; &acquire lock; waitFilled v)
           | some(d) =>
             (&addFrame out d;
              (slots +ₗ idx) ← none();
              order ← injr((cur, !order));
              next ← (cur + #1);
              &release lock)) #();
         loop #())) #()

/-- `Stager.output s`. -/
def stagerOutput : Val := hl_val% λ s, &bufToBytes (fst(snd(snd(snd(snd(s))))))
/-- `Stager.emitted_order s`. -/
def stagerEmittedOrder : Val := hl_val%
  λ s, &listRev (!(snd(snd(snd(snd(snd(snd(s))))))))

/-! ## Top level -/

/-- `compress ~workers ~capacity ~chunk_size ~window codec input`. -/
def pipelineCompress : Val := hl_val%
  λ workers capacity chunkSize window codec input,
    let n := &blen input;
    let total := ((n + chunkSize) - #1) / chunkSize;
    let q := &bqueueCreate capacity;
    let stager := &stagerCreate window total;
    let collector := &spawn (λ u, &stagerCollect stager);
    let worker := (λ u,
      (rec loop v :=
        match &bqueuePop q with
        | injl(stop) => #()
        | injr(ch) => (&stagerDeposit stager (fst(ch)) (fst(codec) (snd(ch))); loop v)) #());
    let pool := allocn(workers, none());
    (rec sp i := if i < workers then ((pool +ₗ i) ← &spawn worker; sp (i + #1)) else #()) #0;
    let off := ref(#0);
    let seq := ref(#0);
    (rec loop u :=
      if !off < n then
        (let len := &minV chunkSize (n - !off);
         &bqueuePush q (injr((!seq, &bsub input (!off) len)));
         seq ← (!seq + #1);
         off ← (!off + len);
         loop #())
      else #()) #();
    (rec stops i := if i < workers then (&bqueuePush q (injl(#())); stops (i + #1)) else #()) #0;
    (rec jn i := if i < workers then (&join (!(pool +ₗ i)); jn (i + #1)) else #()) #0;
    &join collector;
    (&stagerOutput stager, &stagerEmittedOrder stager)

/-- `decompress_stream codec stream`: decode a framed stream, single-threaded. -/
def pipelineDecompressStream : Val := hl_val%
  λ codec stream,
    let n := &blen stream;
    let out := &bufCreate (n * #2);
    let i := ref(#0);
    (rec loop u :=
      if !i < n then
        (let len := &getU32 stream (!i);
         i ← (!i + #4);
         &bufAddBytes out (snd(codec) (&bsub stream (!i) len));
         i ← (!i + len);
         loop #())
      else #()) #();
    &bufToBytes out

end Iris.HeapLang.Codec

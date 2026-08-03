type chunk = { seq : int; data : bytes }
type msg = Chunk of chunk | Stop

module Bqueue = struct
  type t = {
    capacity : int;
    slots : msg array;
    mutable head : int;
    mutable tail : int;
    mutable size : int;
    lock : Mutex.t;
    not_full : Condition.t;
    not_empty : Condition.t;
  }

  let create capacity =
    if capacity < 1 then invalid_arg "Bqueue.create: capacity < 1";
    {
      capacity;
      slots = Array.make capacity Stop;
      head = 0;
      tail = 0;
      size = 0;
      lock = Mutex.create ();
      not_full = Condition.create ();
      not_empty = Condition.create ();
    }

  let push q v =
    Mutex.lock q.lock;
    while q.size = q.capacity do Condition.wait q.not_full q.lock done;
    assert (q.size < q.capacity);
    q.slots.(q.tail) <- v;
    q.tail <- (q.tail + 1) mod q.capacity;
    q.size <- q.size + 1;
    assert (q.size <= q.capacity);
    Condition.signal q.not_empty;
    Mutex.unlock q.lock

  let pop q =
    Mutex.lock q.lock;
    while q.size = 0 do Condition.wait q.not_empty q.lock done;
    assert (q.size > 0);
    let v = q.slots.(q.head) in
    q.slots.(q.head) <- Stop;
    q.head <- (q.head + 1) mod q.capacity;
    q.size <- q.size - 1;
    Condition.signal q.not_full;
    Mutex.unlock q.lock;
    v
end

module Stager = struct
  type t = {
    window : int;
    slots : bytes option array;
    next_to_emit : int Atomic.t;
    total : int;
    lock : Mutex.t;
    slot_filled : Condition.t;
    slot_freed : Condition.t;
    out : Buffer.t;
    mutable order : int list;
  }

  let create window total =
    let window = max 1 window in
    {
      window;
      slots = Array.make window None;
      next_to_emit = Atomic.make 0;
      total;
      lock = Mutex.create ();
      slot_filled = Condition.create ();
      slot_freed = Condition.create ();
      out = Buffer.create ((total * 8) + 16);
      order = [];
    }

  let deposit s seq data =
    Mutex.lock s.lock;
    while seq - Atomic.get s.next_to_emit >= s.window do
      Condition.wait s.slot_freed s.lock
    done;
    let idx = seq mod s.window in
    assert (s.slots.(idx) = None);
    s.slots.(idx) <- Some data;
    Condition.signal s.slot_filled;
    Mutex.unlock s.lock

  let add_frame buf data =
    Codec.add_u32 buf (Bytes.length data);
    Buffer.add_bytes buf data

  let collect s =
    let running = ref true in
    while !running do
      let next = Atomic.get s.next_to_emit in
      if next >= s.total then running := false
      else begin
        let idx = next mod s.window in
        Mutex.lock s.lock;
        while s.slots.(idx) = None do Condition.wait s.slot_filled s.lock done;
        let data = match s.slots.(idx) with Some d -> d | None -> assert false in
        s.slots.(idx) <- None;
        add_frame s.out data;
        s.order <- next :: s.order;
        let advanced = Atomic.compare_and_set s.next_to_emit next (next + 1) in
        assert advanced;
        Condition.broadcast s.slot_freed;
        Mutex.unlock s.lock
      end
    done

  let output s = Buffer.to_bytes s.out
  let emitted_order s = List.rev s.order
end

let default_workers = 4
let default_capacity = 16
let default_chunk_size = 4096
let default_window = 64

let compress ?(workers = default_workers) ?(capacity = default_capacity)
    ?(chunk_size = default_chunk_size) ?(window = default_window)
    (codec : Codec.t) (input : bytes) =
  let n = Bytes.length input in
  let total = if chunk_size < 1 then invalid_arg "chunk_size < 1"
    else (n + chunk_size - 1) / chunk_size in
  let q = Bqueue.create capacity in
  let stager = Stager.create window total in
  let collector = Domain.spawn (fun () -> Stager.collect stager) in
  let worker () =
    let rec loop () =
      match Bqueue.pop q with
      | Stop -> ()
      | Chunk { seq; data } ->
        Stager.deposit stager seq (codec.Codec.compress data);
        loop ()
    in
    loop ()
  in
  let pool = Array.init workers (fun _ -> Domain.spawn worker) in
  let off = ref 0 and seq = ref 0 in
  while !off < n do
    let len = min chunk_size (n - !off) in
    Bqueue.push q (Chunk { seq = !seq; data = Bytes.sub input !off len });
    incr seq;
    off := !off + len
  done;
  for _ = 1 to workers do Bqueue.push q Stop done;
  Array.iter Domain.join pool;
  Domain.join collector;
  (Stager.output stager, Stager.emitted_order stager)

let decompress_stream (codec : Codec.t) (stream : bytes) =
  let n = Bytes.length stream in
  let out = Buffer.create (n * 2) in
  let i = ref 0 in
  while !i < n do
    if !i + 4 > n then failwith "decompress_stream: truncated frame header";
    let len = Codec.get_u32 stream !i in
    i := !i + 4;
    if !i + len > n then failwith "decompress_stream: truncated frame";
    Buffer.add_bytes out (codec.Codec.decompress (Bytes.sub stream !i len));
    i := !i + len
  done;
  Buffer.to_bytes out

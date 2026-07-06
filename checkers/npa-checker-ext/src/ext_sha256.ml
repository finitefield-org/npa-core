let source_identity = "vendored-sha256-source:v1"

type digest = bytes

type t = {
  h : int32 array;
  buffer : bytes;
  mutable buffer_len : int;
  mutable length : int64;
}

let initial_h =
  [|
    0x6a09e667l;
    0xbb67ae85l;
    0x3c6ef372l;
    0xa54ff53al;
    0x510e527fl;
    0x9b05688cl;
    0x1f83d9abl;
    0x5be0cd19l;
  |]

let k =
  [|
    0x428a2f98l;
    0x71374491l;
    0xb5c0fbcfl;
    0xe9b5dba5l;
    0x3956c25bl;
    0x59f111f1l;
    0x923f82a4l;
    0xab1c5ed5l;
    0xd807aa98l;
    0x12835b01l;
    0x243185bel;
    0x550c7dc3l;
    0x72be5d74l;
    0x80deb1fel;
    0x9bdc06a7l;
    0xc19bf174l;
    0xe49b69c1l;
    0xefbe4786l;
    0x0fc19dc6l;
    0x240ca1ccl;
    0x2de92c6fl;
    0x4a7484aal;
    0x5cb0a9dcl;
    0x76f988dal;
    0x983e5152l;
    0xa831c66dl;
    0xb00327c8l;
    0xbf597fc7l;
    0xc6e00bf3l;
    0xd5a79147l;
    0x06ca6351l;
    0x14292967l;
    0x27b70a85l;
    0x2e1b2138l;
    0x4d2c6dfcl;
    0x53380d13l;
    0x650a7354l;
    0x766a0abbl;
    0x81c2c92el;
    0x92722c85l;
    0xa2bfe8a1l;
    0xa81a664bl;
    0xc24b8b70l;
    0xc76c51a3l;
    0xd192e819l;
    0xd6990624l;
    0xf40e3585l;
    0x106aa070l;
    0x19a4c116l;
    0x1e376c08l;
    0x2748774cl;
    0x34b0bcb5l;
    0x391c0cb3l;
    0x4ed8aa4al;
    0x5b9cca4fl;
    0x682e6ff3l;
    0x748f82eel;
    0x78a5636fl;
    0x84c87814l;
    0x8cc70208l;
    0x90befffal;
    0xa4506cebl;
    0xbef9a3f7l;
    0xc67178f2l;
  |]

let create () =
  { h = Array.copy initial_h; buffer = Bytes.create 64; buffer_len = 0; length = 0L }

let copy state =
  {
    h = Array.copy state.h;
    buffer = Bytes.copy state.buffer;
    buffer_len = state.buffer_len;
    length = state.length;
  }

let rotr value bits =
  Int32.logor (Int32.shift_right_logical value bits) (Int32.shift_left value (32 - bits))

let logxor3 a b c = Int32.logxor a (Int32.logxor b c)

let ch x y z = Int32.logxor (Int32.logand x y) (Int32.logand (Int32.lognot x) z)

let maj x y z =
  logxor3 (Int32.logand x y) (Int32.logand x z) (Int32.logand y z)

let big_sigma0 x = logxor3 (rotr x 2) (rotr x 13) (rotr x 22)

let big_sigma1 x = logxor3 (rotr x 6) (rotr x 11) (rotr x 25)

let small_sigma0 x =
  logxor3 (rotr x 7) (rotr x 18) (Int32.shift_right_logical x 3)

let small_sigma1 x =
  logxor3 (rotr x 17) (rotr x 19) (Int32.shift_right_logical x 10)

let byte32 block offset = Int32.of_int (Char.code (Bytes.get block offset))

let get_be32 block offset =
  Int32.logor
    (Int32.shift_left (byte32 block offset) 24)
    (Int32.logor
       (Int32.shift_left (byte32 block (offset + 1)) 16)
       (Int32.logor
          (Int32.shift_left (byte32 block (offset + 2)) 8)
          (byte32 block (offset + 3))))

let set_be32 output offset word =
  Bytes.set output offset
    (Char.chr (Int32.to_int (Int32.logand (Int32.shift_right_logical word 24) 0xffl)));
  Bytes.set output (offset + 1)
    (Char.chr (Int32.to_int (Int32.logand (Int32.shift_right_logical word 16) 0xffl)));
  Bytes.set output (offset + 2)
    (Char.chr (Int32.to_int (Int32.logand (Int32.shift_right_logical word 8) 0xffl)));
  Bytes.set output (offset + 3) (Char.chr (Int32.to_int (Int32.logand word 0xffl)))

let set_be64 output offset word =
  for index = 0 to 7 do
    let shift = (7 - index) * 8 in
    let byte =
      Int64.to_int (Int64.logand (Int64.shift_right_logical word shift) 0xffL)
    in
    Bytes.set output (offset + index) (Char.chr byte)
  done

let process_block state block offset =
  let w = Array.make 64 0l in
  for index = 0 to 15 do
    w.(index) <- get_be32 block (offset + (index * 4))
  done;
  for index = 16 to 63 do
    w.(index) <-
      Int32.add
        (Int32.add (small_sigma1 w.(index - 2)) w.(index - 7))
        (Int32.add (small_sigma0 w.(index - 15)) w.(index - 16))
  done;
  let a = ref state.h.(0) in
  let b = ref state.h.(1) in
  let c = ref state.h.(2) in
  let d = ref state.h.(3) in
  let e = ref state.h.(4) in
  let f = ref state.h.(5) in
  let g = ref state.h.(6) in
  let h = ref state.h.(7) in
  for index = 0 to 63 do
    let t1 =
      Int32.add
        (Int32.add (Int32.add !h (big_sigma1 !e)) (ch !e !f !g))
        (Int32.add k.(index) w.(index))
    in
    let t2 = Int32.add (big_sigma0 !a) (maj !a !b !c) in
    h := !g;
    g := !f;
    f := !e;
    e := Int32.add !d t1;
    d := !c;
    c := !b;
    b := !a;
    a := Int32.add t1 t2
  done;
  state.h.(0) <- Int32.add state.h.(0) !a;
  state.h.(1) <- Int32.add state.h.(1) !b;
  state.h.(2) <- Int32.add state.h.(2) !c;
  state.h.(3) <- Int32.add state.h.(3) !d;
  state.h.(4) <- Int32.add state.h.(4) !e;
  state.h.(5) <- Int32.add state.h.(5) !f;
  state.h.(6) <- Int32.add state.h.(6) !g;
  state.h.(7) <- Int32.add state.h.(7) !h

let update_subbytes state input offset length =
  if offset < 0 || length < 0 || offset + length > Bytes.length input then
    invalid_arg "Ext_sha256.update_subbytes";
  state.length <- Int64.add state.length (Int64.of_int length);
  let input_offset = ref offset in
  let remaining = ref length in
  if state.buffer_len > 0 then (
    let take = min (64 - state.buffer_len) !remaining in
    Bytes.blit input !input_offset state.buffer state.buffer_len take;
    state.buffer_len <- state.buffer_len + take;
    input_offset := !input_offset + take;
    remaining := !remaining - take;
    if state.buffer_len = 64 then (
      process_block state state.buffer 0;
      state.buffer_len <- 0));
  while !remaining >= 64 do
    process_block state input !input_offset;
    input_offset := !input_offset + 64;
    remaining := !remaining - 64
  done;
  if !remaining > 0 then (
    Bytes.blit input !input_offset state.buffer 0 !remaining;
    state.buffer_len <- !remaining)

let update_bytes state input = update_subbytes state input 0 (Bytes.length input)

let update_string state input = update_bytes state (Bytes.of_string input)

let finalize state =
  let final_state = copy state in
  let bit_length = Int64.mul final_state.length 8L in
  let padding_len =
    if final_state.buffer_len < 56 then 56 - final_state.buffer_len
    else 120 - final_state.buffer_len
  in
  let padding = Bytes.make (padding_len + 8) '\000' in
  Bytes.set padding 0 '\128';
  set_be64 padding padding_len bit_length;
  update_bytes final_state padding;
  let output = Bytes.create 32 in
  for index = 0 to 7 do
    set_be32 output (index * 4) final_state.h.(index)
  done;
  output

let digest_bytes input =
  let state = create () in
  update_bytes state input;
  finalize state

let digest_string input =
  let state = create () in
  update_string state input;
  finalize state

let hex_char value =
  Char.unsafe_chr
    (if value < 10 then Char.code '0' + value else Char.code 'a' + value - 10)

let to_hex digest =
  let output = Bytes.create (Bytes.length digest * 2) in
  for index = 0 to Bytes.length digest - 1 do
    let value = Char.code (Bytes.get digest index) in
    Bytes.set output (index * 2) (hex_char (value lsr 4));
    Bytes.set output ((index * 2) + 1) (hex_char (value land 0x0f))
  done;
  Bytes.unsafe_to_string output

let hex_of_bytes input = to_hex (digest_bytes input)

let hex_of_string input = to_hex (digest_string input)

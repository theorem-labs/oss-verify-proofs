(** * Spec.PngModel.Deflate — transcription of zlib-1.3.1's [deflate.c].

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.  Depends on
    [Spec.PngModel.{Base, ZBitsOut, Checksum, Chunk, Trees}] and Stdlib.

    Source: [materials/zlib-1.3.1/deflate.c] (in-container
    [/harness/problem/materials/zlib-1.3.1/deflate.c]) plus the macros in
    [deflate.h] it uses.  BUG-FOR-BUG against the build the delivered
    binary came from (plain [gcc -O2], stock [./configure --static]):
    [FASTEST], [LIT_MEM], [ZLIB_DEBUG], [MAXSEG_64K] and [UNALIGNED_OK] are
    all OFF, [GZIP] and [STDC] are ON.  Consequences pinned here:

    - [longest_match] is the BYTE-AT-A-TIME version ([deflate.c:1439-1471]),
      not the [UNALIGNED_OK] two-bytes-at-a-time one: [zconf.h:200-202]
      defines [UNALIGNED_OK] only under [MSDOS].
    - [INSERT_STRING] maintains [prev[]] ([deflate.c:160-163]).
    - [fill_window]'s [if (sizeof(int) <= 2)] block ([deflate.c:262-272])
      is DEAD on riscv64 LP64 and is transcribed as such.
    - [s->block_start] is a [long] and legitimately goes NEGATIVE
      ([deflate.h:158-160]); it is modelled as a plain [Z], never as a [u32].
    - [more], [len], [left], [have] and the hash values are [unsigned]
      (32-bit); [window_size], [opt_len], [static_len], [high_water] and
      [stored_len] are [ulg] (64-bit on LP64).

    SCOPE CUT, revised 2026-08-19 (zlib-rt gzip extension; original cut
    2026-08 libpng-era, kept below for the record).  The [wrap == 2] WRITE
    path is now transcribed for the [gzhead == Z_NULL] driver: [GZIP_STATE]
    emits the fixed ten-byte header ([deflate.c:1031-1055]) and
    [deflate_trailer] the CRC32+ISIZE trailer ([:1233-1242]).  Still NOT
    transcribed: the [deflateSetHeader] machinery
    ([EXTRA_STATE]/[NAME_STATE]/[COMMENT_STATE]/[HCRC_STATE], [:1056-1173])
    — no driver in this campaign calls [deflateSetHeader], the model
    carries no [gzhead] field, and those states are unreachable from
    [defl_new].  [defl_wf] below still records [wrap <= 1]: that is the
    libpng-era THEORY's obligation (its consumers rely on the zlib trailer
    arm), not the model's; a gzip-side wf is the Q3 theory follow-up.
    (Original libpng-era rationale: [png_deflate_claim] asks for
    [windowBits] in 9..15, so [wrap] was 1 on every call and the gzip
    states were unreachable — [deflate_drv] answered [DfUnmodelled].)

    Window and hash arithmetic is kept LINEAR, never [mod]: every wrap is
    written [if x < wsize then x else x - wsize], matching the machine code
    and keeping the trusted spec's euclidean [lia] stage out of this family
    (the campaign's §3.6 note).

    Arrays.  [window], [prev] and [head] are [zarr]s.  The bulk operations
    ([zmemcpy] of the sliding window, [slide_hash], [CLEAR_HASH], the
    [WIN_INIT] zero-fill) are written as POINTWISE REDEFINITIONS over an
    index range rather than as fuelled write loops: that is both the exact
    postcondition and the shape §3.6 asks the machine-level invariant to
    state ("prefix pointwise [p >= wsize ? p - wsize : 0] applied").

    QUARANTINE (c5-invariants.md §2.2).  [longest_match] is a HEURISTIC.
    The fold below IS its specification; no optimality claim is made or
    needed anywhere.  Likewise [deflate_slow]'s lazy-match policy and
    [Z_FILTERED]'s acceptance gate are pure transcription.  What the
    round-trip lane consumes is the three token contracts at the end of
    this file ([cEnc], [cEmpty], [cRes]).

    Validated against the delivered binary: see [a working folder]
    (R1 boundary records for [longest_match], [fill_window], [deflate_slow],
    [deflate_stored] from [/harness/reference_binary] under qemu GDB-RSP). *)

From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel
  Require Import Base ZBitsOut Checksum Chunk Trees.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

(** ** 1. Constants *)

(** [deflate.c:85-90]. *)
Definition NIL     : Z := 0.
Definition TOO_FAR : Z := 4096.

(** [deflate.h:300]: [WIN_INIT = MAX_MATCH]. *)
Definition WIN_INIT : Z := MAX_MATCH.

(** [deflate.c:1607]. *)
Definition MAX_STORED : Z := 65535.

(** [deflate.h:58-67]: stream status. *)
Definition INIT_STATE   : Z := 42.
Definition GZIP_STATE   : Z := 57.
Definition BUSY_STATE   : Z := 113.

(** [zutil.h:181] ("assume Unix"). *)
Definition OS_CODE      : Z := 3.
Definition FINISH_STATE : Z := 666.

(** [zlib.h:168-184].  [Z_NO_FLUSH], [Z_SYNC_FLUSH], [Z_FINISH],
    [Z_BLOCK], [Z_OK], [Z_STREAM_END], [Z_STREAM_ERROR], [Z_BUF_ERROR] and
    [Z_DEFLATED] are the nine [Inflate.v] also needs, so they live in
    [Base.v] (see the integration note there); only the deflate-specific
    ones are declared here. *)
Definition Z_PARTIAL_FLUSH : Z := 1.
Definition Z_FULL_FLUSH    : Z := 3.
Definition Z_HUFFMAN_ONLY  : Z := 2.
Definition Z_RLE           : Z := 3.
Definition PRESET_DICT     : Z := 32.

(** [deflate.c:133]: [RANK(f) = f*2 - (f > 4 ? 9 : 0)]. *)
Definition RANK (f : Z) : Z := f * 2 - (if Z.ltb 4 f then 9 else 0).

(** [deflate.c:63-68]. *)
Inductive BlockState : Set :=
| NeedMore | BlockDone | FinishStarted | FinishDone.

(** ** 2. The state

    [deflate_state] ([deflate.h:104-282]) as field clusters.  The immutable
    geometry is [Chunk.v]'s [DeflGeom] — the same record [deflateInit2_]
    fills in, already validated against the binary (613 corpus + 94 injected
    [deflateInit2_] records).  [trees.c]'s own fields live in [Trees.v]'s
    [TSt], which also carries [bi_buf]/[bi_valid] and the [pending_buf]
    queue. *)

Record LSt : Type := mkLSt {
  ls_window     : zarr;  (** [window[0 .. window_size)] *)
  ls_prev       : zarr;  (** [prev[]]; NEVER initialised by zlib *)
  ls_head       : zarr;  (** [head[]]; zeroed by [CLEAR_HASH] *)
  ls_insh       : Z;     (** [ins_h] *)
  ls_blockstart : Z;     (** [block_start], a signed [long] *)
  ls_matchlen   : Z;
  ls_prevmatch  : Z;
  ls_matchavail : Z;
  ls_strstart   : Z;
  ls_matchstart : Z;
  ls_lookahead  : Z;
  ls_prevlen    : Z;
  ls_insert     : Z;
  ls_highwater  : Z;     (** [ulg] *)
  ls_windowsize : Z      (** [ulg]; [lm_init] sets it to [2 * w_size] *)
}.

(** The [z_stream] fields [deflate.c] reads or writes.  [zs_in] is the
    unconsumed input ([avail_in = length zs_in]) and [zs_done] the already
    consumed prefix in order, because [deflate_stored] copies backwards
    from [next_in] ([deflate.c:1724], [:1738]). *)
Record ZStrm : Type := mkZStrm {
  zs_in       : list Z;
  zs_done     : list Z;
  zs_out      : list Z;   (** bytes handed to [next_out] so far *)
  zs_availout : Z;
  zs_totalin  : Z;
  zs_totalout : Z;
  zs_adler    : Z;
  zs_datatype : Z
}.

Record DSt : Type := mkDSt {
  d_cfg       : DeflGeom;
  d_status    : Z;
  d_lastflush : Z;
  d_wrap      : Z;   (** mutable: negated once the trailer is written *)
  d_ts        : TSt;
  d_ls        : LSt;
  d_strm      : ZStrm
}.
Definition setL_window (v : zarr) (s : LSt) : LSt :=
  mkLSt (v) (ls_prev s) (ls_head s) (ls_insh s) (ls_blockstart s) (ls_matchlen s) (ls_prevmatch s) (ls_matchavail s) (ls_strstart s) (ls_matchstart s) (ls_lookahead s) (ls_prevlen s) (ls_insert s) (ls_highwater s) (ls_windowsize s).
Definition setL_prev (v : zarr) (s : LSt) : LSt :=
  mkLSt (ls_window s) (v) (ls_head s) (ls_insh s) (ls_blockstart s) (ls_matchlen s) (ls_prevmatch s) (ls_matchavail s) (ls_strstart s) (ls_matchstart s) (ls_lookahead s) (ls_prevlen s) (ls_insert s) (ls_highwater s) (ls_windowsize s).
Definition setL_head (v : zarr) (s : LSt) : LSt :=
  mkLSt (ls_window s) (ls_prev s) (v) (ls_insh s) (ls_blockstart s) (ls_matchlen s) (ls_prevmatch s) (ls_matchavail s) (ls_strstart s) (ls_matchstart s) (ls_lookahead s) (ls_prevlen s) (ls_insert s) (ls_highwater s) (ls_windowsize s).
Definition setL_insh (v : Z) (s : LSt) : LSt :=
  mkLSt (ls_window s) (ls_prev s) (ls_head s) (v) (ls_blockstart s) (ls_matchlen s) (ls_prevmatch s) (ls_matchavail s) (ls_strstart s) (ls_matchstart s) (ls_lookahead s) (ls_prevlen s) (ls_insert s) (ls_highwater s) (ls_windowsize s).
Definition setL_blockstart (v : Z) (s : LSt) : LSt :=
  mkLSt (ls_window s) (ls_prev s) (ls_head s) (ls_insh s) (v) (ls_matchlen s) (ls_prevmatch s) (ls_matchavail s) (ls_strstart s) (ls_matchstart s) (ls_lookahead s) (ls_prevlen s) (ls_insert s) (ls_highwater s) (ls_windowsize s).
Definition setL_matchlen (v : Z) (s : LSt) : LSt :=
  mkLSt (ls_window s) (ls_prev s) (ls_head s) (ls_insh s) (ls_blockstart s) (v) (ls_prevmatch s) (ls_matchavail s) (ls_strstart s) (ls_matchstart s) (ls_lookahead s) (ls_prevlen s) (ls_insert s) (ls_highwater s) (ls_windowsize s).
Definition setL_prevmatch (v : Z) (s : LSt) : LSt :=
  mkLSt (ls_window s) (ls_prev s) (ls_head s) (ls_insh s) (ls_blockstart s) (ls_matchlen s) (v) (ls_matchavail s) (ls_strstart s) (ls_matchstart s) (ls_lookahead s) (ls_prevlen s) (ls_insert s) (ls_highwater s) (ls_windowsize s).
Definition setL_matchavail (v : Z) (s : LSt) : LSt :=
  mkLSt (ls_window s) (ls_prev s) (ls_head s) (ls_insh s) (ls_blockstart s) (ls_matchlen s) (ls_prevmatch s) (v) (ls_strstart s) (ls_matchstart s) (ls_lookahead s) (ls_prevlen s) (ls_insert s) (ls_highwater s) (ls_windowsize s).
Definition setL_strstart (v : Z) (s : LSt) : LSt :=
  mkLSt (ls_window s) (ls_prev s) (ls_head s) (ls_insh s) (ls_blockstart s) (ls_matchlen s) (ls_prevmatch s) (ls_matchavail s) (v) (ls_matchstart s) (ls_lookahead s) (ls_prevlen s) (ls_insert s) (ls_highwater s) (ls_windowsize s).
Definition setL_matchstart (v : Z) (s : LSt) : LSt :=
  mkLSt (ls_window s) (ls_prev s) (ls_head s) (ls_insh s) (ls_blockstart s) (ls_matchlen s) (ls_prevmatch s) (ls_matchavail s) (ls_strstart s) (v) (ls_lookahead s) (ls_prevlen s) (ls_insert s) (ls_highwater s) (ls_windowsize s).
Definition setL_lookahead (v : Z) (s : LSt) : LSt :=
  mkLSt (ls_window s) (ls_prev s) (ls_head s) (ls_insh s) (ls_blockstart s) (ls_matchlen s) (ls_prevmatch s) (ls_matchavail s) (ls_strstart s) (ls_matchstart s) (v) (ls_prevlen s) (ls_insert s) (ls_highwater s) (ls_windowsize s).
Definition setL_prevlen (v : Z) (s : LSt) : LSt :=
  mkLSt (ls_window s) (ls_prev s) (ls_head s) (ls_insh s) (ls_blockstart s) (ls_matchlen s) (ls_prevmatch s) (ls_matchavail s) (ls_strstart s) (ls_matchstart s) (ls_lookahead s) (v) (ls_insert s) (ls_highwater s) (ls_windowsize s).
Definition setL_insert (v : Z) (s : LSt) : LSt :=
  mkLSt (ls_window s) (ls_prev s) (ls_head s) (ls_insh s) (ls_blockstart s) (ls_matchlen s) (ls_prevmatch s) (ls_matchavail s) (ls_strstart s) (ls_matchstart s) (ls_lookahead s) (ls_prevlen s) (v) (ls_highwater s) (ls_windowsize s).
Definition setL_highwater (v : Z) (s : LSt) : LSt :=
  mkLSt (ls_window s) (ls_prev s) (ls_head s) (ls_insh s) (ls_blockstart s) (ls_matchlen s) (ls_prevmatch s) (ls_matchavail s) (ls_strstart s) (ls_matchstart s) (ls_lookahead s) (ls_prevlen s) (ls_insert s) (v) (ls_windowsize s).
Definition setL_windowsize (v : Z) (s : LSt) : LSt :=
  mkLSt (ls_window s) (ls_prev s) (ls_head s) (ls_insh s) (ls_blockstart s) (ls_matchlen s) (ls_prevmatch s) (ls_matchavail s) (ls_strstart s) (ls_matchstart s) (ls_lookahead s) (ls_prevlen s) (ls_insert s) (ls_highwater s) (v).

Definition setZ_in (v : list Z) (s : ZStrm) : ZStrm :=
  mkZStrm (v) (zs_done s) (zs_out s) (zs_availout s) (zs_totalin s) (zs_totalout s) (zs_adler s) (zs_datatype s).
Definition setZ_done (v : list Z) (s : ZStrm) : ZStrm :=
  mkZStrm (zs_in s) (v) (zs_out s) (zs_availout s) (zs_totalin s) (zs_totalout s) (zs_adler s) (zs_datatype s).
Definition setZ_out (v : list Z) (s : ZStrm) : ZStrm :=
  mkZStrm (zs_in s) (zs_done s) (v) (zs_availout s) (zs_totalin s) (zs_totalout s) (zs_adler s) (zs_datatype s).
Definition setZ_availout (v : Z) (s : ZStrm) : ZStrm :=
  mkZStrm (zs_in s) (zs_done s) (zs_out s) (v) (zs_totalin s) (zs_totalout s) (zs_adler s) (zs_datatype s).
Definition setZ_totalin (v : Z) (s : ZStrm) : ZStrm :=
  mkZStrm (zs_in s) (zs_done s) (zs_out s) (zs_availout s) (v) (zs_totalout s) (zs_adler s) (zs_datatype s).
Definition setZ_totalout (v : Z) (s : ZStrm) : ZStrm :=
  mkZStrm (zs_in s) (zs_done s) (zs_out s) (zs_availout s) (zs_totalin s) (v) (zs_adler s) (zs_datatype s).
Definition setZ_adler (v : Z) (s : ZStrm) : ZStrm :=
  mkZStrm (zs_in s) (zs_done s) (zs_out s) (zs_availout s) (zs_totalin s) (zs_totalout s) (v) (zs_datatype s).
Definition setZ_datatype (v : Z) (s : ZStrm) : ZStrm :=
  mkZStrm (zs_in s) (zs_done s) (zs_out s) (zs_availout s) (zs_totalin s) (zs_totalout s) (zs_adler s) (v).

Definition setD_cfg (v : DeflGeom) (s : DSt) : DSt :=
  mkDSt (v) (d_status s) (d_lastflush s) (d_wrap s) (d_ts s) (d_ls s) (d_strm s).
Definition setD_status (v : Z) (s : DSt) : DSt :=
  mkDSt (d_cfg s) (v) (d_lastflush s) (d_wrap s) (d_ts s) (d_ls s) (d_strm s).
Definition setD_lastflush (v : Z) (s : DSt) : DSt :=
  mkDSt (d_cfg s) (d_status s) (v) (d_wrap s) (d_ts s) (d_ls s) (d_strm s).
Definition setD_wrap (v : Z) (s : DSt) : DSt :=
  mkDSt (d_cfg s) (d_status s) (d_lastflush s) (v) (d_ts s) (d_ls s) (d_strm s).
Definition setD_ts (v : TSt) (s : DSt) : DSt :=
  mkDSt (d_cfg s) (d_status s) (d_lastflush s) (d_wrap s) (v) (d_ls s) (d_strm s).
Definition setD_ls (v : LSt) (s : DSt) : DSt :=
  mkDSt (d_cfg s) (d_status s) (d_lastflush s) (d_wrap s) (d_ts s) (v) (d_strm s).
Definition setD_strm (v : ZStrm) (s : DSt) : DSt :=
  mkDSt (d_cfg s) (d_status s) (d_lastflush s) (d_wrap s) (d_ts s) (d_ls s) (v).

(** ** 3. Array primitives

    Every [zmemcpy]/[zmemzero]/[slide_hash] in [deflate.c] is a bulk
    operation on a contiguous range.  Writing them as pointwise
    redefinitions rather than fuelled write loops keeps them O(1) to apply
    AND states the exact postcondition a walk needs. *)

(** [w'] agrees with [w] outside [[base, base+|dat|)] and holds [dat] there.
    Built through [zlist] so that a reader is one array index. *)
Definition win_blit (dat : list Z) (base : Z) (w : zarr) : zarr :=
  let a := zlist dat in
  let n := zlen dat in
  fun i => if (Z.leb base i) && (Z.ltb i (base + n)) then a (i - base) else w i.

Definition win_zero (base cnt : Z) (w : zarr) : zarr :=
  fun i => if (Z.leb base i) && (Z.ltb i (base + cnt)) then 0 else w i.

(** [zmemcpy(dst, src, cnt)] within one array, [dst] and [src] both indices,
    with [dst < src] (the only direction [deflate.c] ever uses). *)
Definition win_move (dst src cnt : Z) (w : zarr) : zarr :=
  fun i => if (Z.leb dst i) && (Z.ltb i (dst + cnt)) then w (i - dst + src) else w i.

Definition win_take (w : zarr) (base n : Z) : list Z :=
  map (fun k => w (base + Z.of_nat k)) (seq 0 (Z.to_nat n)).

(** ** 4. Hashing ([deflate.c:141-175]) *)

(** [deflate.c:141]: [h = ((h << hash_shift) ^ c) & hash_mask]. *)
Definition update_hash (g : DeflGeom) (h c : Z) : Z :=
  Z.land (Z.lxor (Z.shiftl h (dg_hash_shift g)) c) (dg_hash_mask g).

(** [deflate.c:160-163] [INSERT_STRING].  Returns [match_head] and the
    updated [ins_h] / [prev] / [head].  [(Pos)str] is a [ush]. *)
Definition insert_string (g : DeflGeom) (str : Z) (l : LSt) : Z * LSt :=
  let h  := update_hash g (ls_insh l) (ls_window l (str + MIN_MATCH - 1)) in
  let mh := ls_head l h in
  let l1 := setL_insh h l in
  let l2 := setL_prev (zset (ls_prev l1) (Z.land str (dg_w_mask g)) mh) l1 in
  (mh, setL_head (zset (ls_head l2) h (u16 str)) l2).

(** [deflate.c:170-175] [CLEAR_HASH]: the whole [head] array becomes NIL. *)
Definition clear_hash (g : DeflGeom) (l : LSt) : LSt :=
  setL_head (fun i => if (Z.leb 0 i) && (Z.ltb i (dg_hash_size g))
                      then NIL else ls_head l i) l.

(** [deflate.c:187-209] [slide_hash], both loops.  Pointwise
    [p >= wsize ? p - wsize : NIL] over [head[0..hash_size)] and
    [prev[0..wsize)]. *)
Definition slide_one (wsize v : Z) : Z := if Z.leb wsize v then v - wsize else NIL.

Definition slide_range (n wsize : Z) (a : zarr) : zarr :=
  fun i => if (Z.leb 0 i) && (Z.ltb i n) then u16 (slide_one wsize (a i)) else a i.

Definition slide_hash (g : DeflGeom) (l : LSt) : LSt :=
  let ws := dg_w_size g in
  setL_prev (slide_range ws ws (ls_prev l))
            (setL_head (slide_range (dg_hash_size g) ws (ls_head l)) l).

(** ** 5. [read_buf] ([deflate.c:218-239])

    Returns the bytes copied out (already [u8]-normalised, since they come
    from a byte buffer) and the updated stream. *)
Definition read_buf (wrap size : Z) (st : ZStrm) : list Z * ZStrm :=
  let avail := zlen (zs_in st) in
  let len := if Z.ltb size avail then size else avail in
  if Z.eqb len 0 then ([], st)
  else
    let dat := map u8 (firstn (Z.to_nat len) (zs_in st)) in
    let ad  := if Z.eqb wrap 1 then adler32_z (zs_adler st) false dat
               else if Z.eqb wrap 2 then crc32_z_at (zs_adler st) 0 dat
               else zs_adler st in
    (dat, setZ_totalin (zs_totalin st + len)
            (setZ_adler ad
              (setZ_done (zs_done st ++ dat)
                (setZ_in (skipn (Z.to_nat len) (zs_in st)) st)))).

(** ** 6. [fill_window] ([deflate.c:251-368]) *)

(** [deflate.c:307-325]: seed [ins_h] and drain [insert].  The [while
    (s->insert)] loop with its mid-body [break]. *)
Fixpoint fw_insert (fuel : nat) (g : DeflGeom) (str : Z) (l : LSt) : LSt :=
  match fuel with
  | O => l
  | S f =>
      if Z.eqb (ls_insert l) 0 then l
      else
        let h  := update_hash g (ls_insh l) (ls_window l (str + MIN_MATCH - 1)) in
        let l1 := setL_insh h l in
        let l2 := setL_prev (zset (ls_prev l1) (Z.land str (dg_w_mask g))
                                  (ls_head l1 h)) l1 in
        let l3 := setL_head (zset (ls_head l2) h (u16 str)) l2 in
        let l4 := setL_insert (ls_insert l3 - 1) l3 in
        if Z.ltb (ls_lookahead l4 + ls_insert l4) MIN_MATCH then l4
        else fw_insert f g (str + 1) l4
  end.

Definition fw_seed (g : DeflGeom) (l : LSt) : LSt :=
  if Z.leb MIN_MATCH (ls_lookahead l + ls_insert l) then
    let str := ls_strstart l - ls_insert l in
    let h0  := ls_window l str in
    let h1  := update_hash g h0 (ls_window l (str + 1)) in
    fw_insert (Z.to_nat (ls_insert l) + 1) g str (setL_insh h1 l)
  else l.

(** One trip of the [do .. while] at [deflate.c:258-330].  [true] means
    "the [break] at :288 fired". *)
Definition fw_step (g : DeflGeom) (wrap : Z) (l : LSt) (st : ZStrm)
  : bool * LSt * ZStrm :=
  let wsize := dg_w_size g in
  let more0 := u32 (ls_windowsize l - ls_lookahead l - ls_strstart l) in
  (* :277-287; [deflate.c:262-272] is dead on LP64 (sizeof(int) == 4) *)
  let p :=
    if Z.leb (wsize + dg_max_dist g) (ls_strstart l) then
      let l1 := setL_window (win_move 0 wsize (wsize - more0) (ls_window l)) l in
      let l2 := setL_matchstart (ls_matchstart l1 - wsize) l1 in
      let l3 := setL_strstart (ls_strstart l2 - wsize) l2 in
      let l4 := setL_blockstart (ls_blockstart l3 - wsize) l3 in
      let l5 := if Z.ltb (ls_strstart l4) (ls_insert l4)
                then setL_insert (ls_strstart l4) l4 else l4 in
      (slide_hash g l5, more0 + wsize)
    else (l, more0) in
  let l' := fst p in let more := snd p in
  if Z.eqb (zlen (zs_in st)) 0 then (true, l', st)
  else
    (* :303-304 *)
    let r := read_buf wrap more st in
    let dat := fst r in let st' := snd r in
    let l6 := setL_window (win_blit dat (ls_strstart l' + ls_lookahead l')
                                    (ls_window l')) l' in
    let l7 := setL_lookahead (ls_lookahead l6 + zlen dat) l6 in
    (false, fw_seed g l7, st').

Fixpoint fw_loop (fuel : nat) (g : DeflGeom) (wrap : Z) (l : LSt) (st : ZStrm)
  : LSt * ZStrm :=
  match fuel with
  | O => (l, st)
  | S f =>
      match fw_step g wrap l st with
      | (true, l', st') => (l', st')
      | (false, l', st') =>
          if (Z.ltb (ls_lookahead l') MIN_LOOKAHEAD)
             && negb (Z.eqb (zlen (zs_in st')) 0)
          then fw_loop f g wrap l' st'
          else (l', st')
      end
  end.

(** [deflate.c:339-364]: the [WIN_INIT] zero-fill and the high-water bump. *)
Definition fw_highwater (l : LSt) : LSt :=
  if Z.ltb (ls_highwater l) (ls_windowsize l) then
    let curr := ls_strstart l + ls_lookahead l in
    if Z.ltb (ls_highwater l) curr then
      let init0 := ls_windowsize l - curr in
      let init  := if Z.ltb WIN_INIT init0 then WIN_INIT else init0 in
      setL_highwater (curr + init) (setL_window (win_zero curr init (ls_window l)) l)
    else if Z.ltb (ls_highwater l) (curr + WIN_INIT) then
      let init0 := curr + WIN_INIT - ls_highwater l in
      let init  := if Z.ltb (ls_windowsize l - ls_highwater l) init0
                   then ls_windowsize l - ls_highwater l else init0 in
      setL_highwater (ls_highwater l + init)
        (setL_window (win_zero (ls_highwater l) init (ls_window l)) l)
    else l
  else l.

(** [fill_window] is [void]: it updates the state only.  FUEL: each trip
    that does not [break] consumes at least one input byte (the C's
    [Assert(more >= 2)]), so [avail_in + 2] is a static bound. *)
Definition fill_window (g : DeflGeom) (wrap : Z) (l : LSt) (st : ZStrm)
  : LSt * ZStrm :=
  let r := fw_loop (Z.to_nat (zlen (zs_in st)) + 2) g wrap l st in
  (fw_highwater (fst r), snd r).

(** ** 7. [lm_init] ([deflate.c:673-692]) *)

Definition lm_init (g : DeflGeom) (l : LSt) : LSt :=
  let l0 := clear_hash g (setL_windowsize (2 * dg_w_size g) l) in
  setL_insh 0
    (setL_matchavail 0
      (setL_prevlen (MIN_MATCH - 1)
        (setL_matchlen (MIN_MATCH - 1)
          (setL_insert 0
            (setL_lookahead 0
              (setL_blockstart 0 (setL_strstart 0 l0))))))).

(** ** 8. [longest_match] ([deflate.c:1348-1489], the non-[UNALIGNED_OK] arm)

    QUARANTINED HEURISTIC.  The fold below IS the specification.

    [lm_cpl] is the unrolled compare loop at [:1458-1463].  It starts at
    offset 3 — offsets 0 and 1 were checked at [:1443-1444] and offset 2 is
    ASSUMED equal ([:1446-1450]: "not necessary to compare scan[2] and
    match[2] ... given that the hash keys are equal and that
    HASH_BITS >= 8").  That assumption is discharged at model level by
    [hash3_det] below, and it is a genuine bug-for-bug item: a model that
    compares offset 2 would disagree with the binary whenever the
    assumption failed.

    The loop checks [scan < strend] only every 8th comparison, and
    [MAX_MATCH - 2 = 256] is a multiple of 8, so [scan] lands EXACTLY on
    [strend]; the result is therefore [min (first mismatch >= 3) MAX_MATCH]
    with no overrun. *)
Fixpoint lm_cpl (fuel : nat) (w : zarr) (a b j : Z) : Z :=
  match fuel with
  | O => j
  | S f =>
      if Z.leb MAX_MATCH j then MAX_MATCH
      else if Z.eqb (w (a + j)) (w (b + j)) then lm_cpl f w a b (j + 1)
      else j
  end.

Record LmSt : Type := mkLmSt {
  m_cur   : Z;   (** [cur_match] *)
  m_best  : Z;   (** [best_len] *)
  m_start : Z;   (** [s->match_start] *)
  m_end1  : Z;   (** [scan_end1] *)
  m_end   : Z;   (** [scan_end] *)
  m_chain : Z    (** [chain_length] *)
}.

Inductive LmStep : Type := LmCont (st : LmSt) | LmDone (st : LmSt).

(** Everything the loop reads and does not change. *)
Record LmCtx : Type := mkLmCtx {
  x_win   : zarr;
  x_prev  : zarr;
  x_scan  : Z;   (** [s->strstart] *)
  x_nice  : Z;   (** [nice_match], already clamped to [lookahead] *)
  x_limit : Z;
  x_wmask : Z
}.

(** The four byte checks at [deflate.c:1441-1444] that let a candidate
    into the compare loop. *)
Definition lm_ok (c : LmCtx) (st : LmSt) : bool :=
  let w := x_win c in let cm := m_cur st in
  let bl := m_best st in let sc := x_scan c in
  (Z.eqb (w (cm + bl)) (m_end st))
  && (Z.eqb (w (cm + bl - 1)) (m_end1 st))
  && (Z.eqb (w cm) (w sc))
  && (Z.eqb (w (cm + 1)) (w (sc + 1))).

(** [deflate.c:1468]: [len = MAX_MATCH - (strend - scan)], i.e. the offset
    [scan] stopped at, which is the first mismatch at or after 3, capped. *)
Definition lm_len (c : LmCtx) (st : LmSt) : Z :=
  if lm_ok c st
  then lm_cpl (Z.to_nat MAX_MATCH) (x_win c) (x_scan c) (m_cur st) 3
  else 0.

(** [deflate.c:1473]: [if (len > best_len)]. *)
Definition lm_hit (c : LmCtx) (st : LmSt) : bool :=
  lm_ok c st && Z.ltb (m_best st) (lm_len c st).

(** [deflate.c:1474-1482].  The [scan_end1]/[scan_end] refresh is skipped by
    the C on the [break] path; the values are locals, so the difference is
    not observable and the model refreshes unconditionally. *)
Definition lm_next (c : LmCtx) (st : LmSt) : LmSt :=
  if lm_hit c st then
    let len := lm_len c st in
    {| m_cur := m_cur st; m_best := len; m_start := m_cur st;
       m_end1 := x_win c (x_scan c + len - 1);
       m_end  := x_win c (x_scan c + len);
       m_chain := m_chain st |}
  else st.

(** ONE trip of [deflate.c:1393-1485]. *)
Definition lm_step (c : LmCtx) (st : LmSt) : LmStep :=
  let st1 := lm_next c st in
  if lm_hit c st && Z.leb (x_nice c) (lm_len c st) then LmDone st1
  else
    (* :1484-1485 *)
    let cm' := x_prev c (Z.land (m_cur st) (x_wmask c)) in
    let ch' := m_chain st1 - 1 in
    let st2 := {| m_cur := cm'; m_best := m_best st1; m_start := m_start st1;
                  m_end1 := m_end1 st1; m_end := m_end st1; m_chain := ch' |} in
    if (Z.ltb (x_limit c) cm') && negb (Z.eqb ch' 0) then LmCont st2 else LmDone st2.

Fixpoint lm_iter (k : nat) (c : LmCtx) (st : LmSt) : option LmSt :=
  match k with
  | O => Some st
  | S k' => match lm_step c st with
            | LmCont st' => lm_iter k' c st'
            | LmDone _ => None
            end
  end.

Fixpoint lm_loop (fuel : nat) (c : LmCtx) (st : LmSt) : LmSt :=
  match fuel with
  | O => st
  | S f => match lm_step c st with
           | LmCont st' => lm_loop f c st'
           | LmDone st' => st'
           end
  end.

(** [longest_match] returns the match length and sets [s->match_start].
    The returned [match_start] is the C's [s->match_start] AFTER the call:
    unchanged when no candidate beat [prev_length] ("in which case the
    result is equal to prev_length and match_start is garbage", [:1341]). *)
Definition longest_match (g : DeflGeom) (l : LSt) (cur_match : Z) : Z * Z :=
  let w      := ls_window l in
  let sc     := ls_strstart l in
  let bl0    := ls_prevlen l in
  let chain0 := if Z.leb (dg_good_match g) (ls_prevlen l)
                then Z.shiftr (dg_max_chain_length g) 2
                else dg_max_chain_length g in
  let nice   := if Z.ltb (ls_lookahead l) (dg_nice_match g)
                then ls_lookahead l else dg_nice_match g in
  let limit  := if Z.ltb (dg_max_dist g) sc then sc - dg_max_dist g else NIL in
  let c := {| x_win := w; x_prev := ls_prev l; x_scan := sc; x_nice := nice;
              x_limit := limit; x_wmask := dg_w_mask g |} in
  let st0 := {| m_cur := cur_match; m_best := bl0; m_start := ls_matchstart l;
                m_end1 := w (sc + bl0 - 1); m_end := w (sc + bl0);
                m_chain := chain0 |} in
  let stf := lm_loop (Z.to_nat (dg_max_chain_length g) + 2) c st0 in
  (if Z.leb (m_best stf) (ls_lookahead l) then m_best stf else ls_lookahead l,
   m_start stf).

(** ** 9. [flush_pending] / [putShortMSB] ([deflate.c:904-933]) *)

Definition flush_pending (s : DSt) : DSt :=
  let ts := tr_flush_bits (d_ts s) in           (* :919 [_tr_flush_bits] *)
  let pd := bw_out (ts_bw ts) in
  let len0 := zlen pd in
  let len := if Z.ltb (zs_availout (d_strm s)) len0 then zs_availout (d_strm s) else len0 in
  if Z.eqb len 0 then setD_ts ts s
  else
    let moved := firstn (Z.to_nat len) pd in
    let ts' := set_bw {| bw_out := skipn (Z.to_nat len) pd;
                         bw_buf := bw_buf (ts_bw ts);
                         bw_valid := bw_valid (ts_bw ts) |} ts in
    let st := d_strm s in
    let st' := setZ_out (zs_out st ++ moved)
                 (setZ_availout (zs_availout st - len)
                   (setZ_totalout (zs_totalout st + len) st)) in
    setD_strm st' (setD_ts ts' s).

Definition putShortMSB (b : Z) (ts : TSt) : TSt :=
  set_bw (bw_put_byte (Z.land b 255) (bw_put_byte (Z.shiftr b 8) (ts_bw ts))) ts.

(** ** 10. [FLUSH_BLOCK_ONLY] / [FLUSH_BLOCK] ([deflate.c:1588-1604]) *)

Definition flush_block_only (last : Z) (s : DSt) : DSt :=
  let l  := d_ls s in
  let bs := ls_blockstart l in
  let stored_len := ls_strstart l - bs in
  let buf := if Z.leb 0 bs then Some (win_take (ls_window l) bs stored_len)
             else None in
  let r  := tr_flush_block buf stored_len last (dg_level (d_cfg s))
                           (dg_strategy (d_cfg s)) (zs_datatype (d_strm s))
                           (d_ts s) in
  let s1 := setD_ts (snd r)
              (setD_strm (setZ_datatype (fst r) (d_strm s)) s) in
  let s2 := setD_ls (setL_blockstart (ls_strstart l) l) s1 in
  flush_pending s2.

(** [None] = fell through; [Some bs] = the macro's early [return]. *)
Definition flush_block (last : Z) (s : DSt) : option BlockState * DSt :=
  let s' := flush_block_only last s in
  if Z.eqb (zs_availout (d_strm s')) 0
  then (Some (if Z.eqb last 0 then NeedMore else FinishStarted), s')
  else (None, s').

(** ** 11. [deflate_slow] ([deflate.c:1910-2030]) — the level-6 path *)

Inductive DsStep : Type :=
| DsCont  (s : DSt)                    (** go round the [for(;;)] again *)
| DsRet   (bs : BlockState) (s : DSt)  (** an early [return] from the body *)
| DsBreak (s : DSt).                   (** [break] at :1926, run the tail *)

(** [deflate.c:1983-1987]: insert every string up to the end of the match.

    BUG-FOR-BUG: the loop counter IS [s->prev_length] ([while (--s->prev_length
    != 0)]), so the field is left at 0 on return.  A model that used a local
    counter and left [prev_length] alone disagrees with the binary at the very
    next [deflate_slow] boundary — caught by the [deflate_slow] R1 records
    ([ds.prev_length]: model 29 vs reference 0). *)
Fixpoint ds_insert (fuel : nat) (g : DeflGeom) (max_insert : Z) (l : LSt) : LSt :=
  match fuel with
  | O => l
  | S f =>
      let l1 := setL_strstart (ls_strstart l + 1) l in
      let l2 := if Z.leb (ls_strstart l1) max_insert
                then snd (insert_string g (ls_strstart l1) l1) else l1 in
      let l3 := setL_prevlen (ls_prevlen l2 - 1) l2 in
      if Z.eqb (ls_prevlen l3) 0 then l3 else ds_insert f g max_insert l3
  end.

(** [deflate.c:1921-1927], [:1821-1827], [:2048-2054], [:2114-2121]: the
    top-of-loop [fill_window] call, factored out so the three guards below
    are one-line tests and so a proof about them does not have to unfold the
    whole trip.  [b] is the per-function "not enough lookahead" test. *)
Definition fill_if (b : bool) (s : DSt) : DSt :=
  if b then let r := fill_window (d_cfg s) (d_wrap s) (d_ls s) (d_strm s) in
            setD_strm (snd r) (setD_ls (fst r) s)
       else s.

Definition ds_need (s : DSt) : bool := Z.ltb (ls_lookahead (d_ls s)) MIN_LOOKAHEAD.
Definition ds_fill (s : DSt) : DSt := fill_if (ds_need s) s.

(** The body of one trip, from [:1932] on, applied to the POST-fill state. *)
Definition ds_body (flush : Z) (p0 : DSt) : DsStep :=
  let g := d_cfg p0 in
    (* :1932-1935 *)
    let ph := if Z.leb MIN_MATCH (ls_lookahead (d_ls p0))
              then insert_string g (ls_strstart (d_ls p0)) (d_ls p0)
              else (NIL, d_ls p0) in
    let hash_head := fst ph in
    let l0 := snd ph in
    (* :1939-1940 *)
    let l1 := setL_matchlen (MIN_MATCH - 1)
                (setL_prevmatch (ls_matchstart l0) (setL_prevlen (ls_matchlen l0) l0)) in
    (* :1942-1962 *)
    let l2 :=
      if negb (Z.eqb hash_head NIL)
         && (Z.ltb (ls_prevlen l1) (dg_max_lazy_match g))
         && (Z.leb (ls_strstart l1 - hash_head) (dg_max_dist g)) then
        let r := longest_match g l1 hash_head in
        let l1a := setL_matchstart (snd r) (setL_matchlen (fst r) l1) in
        if (Z.leb (ls_matchlen l1a) 5)
           && ((Z.eqb (dg_strategy g) Z_FILTERED)
               || ((Z.eqb (ls_matchlen l1a) MIN_MATCH)
                   && (Z.ltb TOO_FAR (ls_strstart l1a - ls_matchstart l1a))))
        then setL_matchlen (MIN_MATCH - 1) l1a else l1a
      else l1 in
    let s2 := setD_ls l2 p0 in
    (* :1967 *)
    if (Z.leb MIN_MATCH (ls_prevlen l2)) && (Z.leb (ls_matchlen l2) (ls_prevlen l2)) then
      let max_insert := ls_strstart l2 + ls_lookahead l2 - MIN_MATCH in
      let tt := tr_tally_dist (ls_strstart l2 - 1 - ls_prevmatch l2)
                              (ls_prevlen l2 - MIN_MATCH)
                              (dg_sym_end g) (d_ts s2) in
      let bflush := fst tt in
      let l3 := setL_prevlen (ls_prevlen l2 - 2)
                  (setL_lookahead (ls_lookahead l2 - (ls_prevlen l2 - 1)) l2) in
      let l4 := ds_insert (Z.to_nat (ls_prevlen l3) + 1) g max_insert l3 in
      let l5 := setL_strstart (ls_strstart l4 + 1)
                  (setL_matchlen (MIN_MATCH - 1) (setL_matchavail 0 l4)) in
      let s3 := setD_ls l5 (setD_ts (snd tt) s2) in
      if bflush then
        match flush_block 0 s3 with
        | (Some bs, s4) => DsRet bs s4
        | (None, s4) => DsCont s4
        end
      else DsCont s3
    else if negb (Z.eqb (ls_matchavail l2) 0) then
      (* :1994-2006 *)
      let tt := tr_tally_lit (ls_window l2 (ls_strstart l2 - 1)) (dg_sym_end g) (d_ts s2) in
      let s3 := setD_ts (snd tt) s2 in
      let s4 := if fst tt then flush_block_only 0 s3 else s3 in
      let s5 := setD_ls (setL_lookahead (ls_lookahead (d_ls s4) - 1)
                          (setL_strstart (ls_strstart (d_ls s4) + 1) (d_ls s4))) s4 in
      if Z.eqb (zs_availout (d_strm s5)) 0 then DsRet NeedMore s5 else DsCont s5
    else
      (* :2007-2014 *)
      DsCont (setD_ls (setL_lookahead (ls_lookahead l2 - 1)
                        (setL_strstart (ls_strstart l2 + 1)
                          (setL_matchavail 1 l2))) s2).

(** ONE trip of [deflate.c:1915-2015]. *)
Definition ds_step (flush : Z) (s : DSt) : DsStep :=
  if (ds_need s) && (ds_need (ds_fill s)) && (Z.eqb flush Z_NO_FLUSH)
  then DsRet NeedMore (ds_fill s)
  else if (ds_need s) && (Z.eqb (ls_lookahead (d_ls (ds_fill s))) 0)
  then DsBreak (ds_fill s)
  else ds_body flush (ds_fill s).

Fixpoint ds_loop (fuel : nat) (flush : Z) (s : DSt) : option BlockState * DSt :=
  match fuel with
  | O => (Some NeedMore, s)  (* unreachable: the fuel is a static bound *)
  | S f =>
      match ds_step flush s with
      | DsCont s' => ds_loop f flush s'
      | DsRet bs s' => (Some bs, s')
      | DsBreak s' => (None, s')
      end
  end.

(** The common tail of every [deflate_*]: [:2016-2029]. *)
Definition ds_tail (flush : Z) (emit_pending_lit : bool) (set_insert : bool)
                   (s : DSt) : BlockState * DSt :=
  let g := d_cfg s in
  let s1 :=
    if emit_pending_lit && negb (Z.eqb (ls_matchavail (d_ls s)) 0) then
      let tt := tr_tally_lit (ls_window (d_ls s) (ls_strstart (d_ls s) - 1))
                             (dg_sym_end g) (d_ts s) in
      setD_ls (setL_matchavail 0 (d_ls s)) (setD_ts (snd tt) s)
    else s in
  let l  := d_ls s1 in
  let s2 := setD_ls (setL_insert (if set_insert
                                  then (if Z.ltb (ls_strstart l) (MIN_MATCH - 1)
                                        then ls_strstart l else MIN_MATCH - 1)
                                  else 0) l) s1 in
  if Z.eqb flush Z_FINISH then
    match flush_block 1 s2 with
    | (Some bs, s3) => (bs, s3)
    | (None, s3) => (FinishDone, s3)
    end
  else if negb (Z.eqb (ts_symnext (d_ts s2)) 0) then
    match flush_block 0 s2 with
    | (Some bs, s3) => (bs, s3)
    | (None, s3) => (BlockDone, s3)
    end
  else (BlockDone, s2).

(** FUEL: every trip advances [strstart] by at least 1 and never increases
    [avail_in + lookahead], so [avail_in + lookahead + 2] bounds the loop. *)
Definition ds_fuel (s : DSt) : nat :=
  Z.to_nat (zlen (zs_in (d_strm s)) + ls_lookahead (d_ls s)) + 2.

Definition deflate_slow (flush : Z) (s : DSt) : BlockState * DSt :=
  match ds_loop (ds_fuel s) flush s with
  | (Some bs, s') => (bs, s')
  | (None, s') => ds_tail flush true true s'
  end.

(** ** 12. [deflate_fast] ([deflate.c:1811-1902]) *)

Fixpoint df_insert (fuel : nat) (g : DeflGeom) (n : Z) (l : LSt) : LSt :=
  match fuel with
  | O => l
  | S f =>
      let l1 := setL_strstart (ls_strstart l + 1) l in
      let l2 := snd (insert_string g (ls_strstart l1) l1) in
      if Z.eqb (n - 1) 0 then l2 else df_insert f g (n - 1) l2
  end.

Definition df_body (flush : Z) (p0 : DSt) : DsStep :=
  let g := d_cfg p0 in
    let ph := if Z.leb MIN_MATCH (ls_lookahead (d_ls p0))
              then insert_string g (ls_strstart (d_ls p0)) (d_ls p0)
              else (NIL, d_ls p0) in
    let hash_head := fst ph in
    let l0 := snd ph in
    let l1 := if negb (Z.eqb hash_head NIL)
                 && (Z.leb (ls_strstart l0 - hash_head) (dg_max_dist g))
              then let r := longest_match g l0 hash_head in
                   setL_matchstart (snd r) (setL_matchlen (fst r) l0)
              else l0 in
    let s2 := setD_ls l1 p0 in
    if Z.leb MIN_MATCH (ls_matchlen l1) then
      let tt := tr_tally_dist (ls_strstart l1 - ls_matchstart l1)
                              (ls_matchlen l1 - MIN_MATCH)
                              (dg_sym_end g) (d_ts s2) in
      let l2 := setL_lookahead (ls_lookahead l1 - ls_matchlen l1) l1 in
      let l4 :=
        if (Z.leb (ls_matchlen l2) (dg_max_lazy_match g))
           && (Z.leb MIN_MATCH (ls_lookahead l2)) then
          (* :1860-1870: insert every string covered by the match, then the
             one past it.  [s->match_length] is left at 0 by the [do..while]. *)
          let l3 := setL_matchlen (ls_matchlen l2 - 1) l2 in
          let l3b := df_insert (Z.to_nat (ls_matchlen l3) + 1) g (ls_matchlen l3) l3 in
          setL_strstart (ls_strstart l3b + 1) (setL_matchlen 0 l3b)
        else
          let l3 := setL_matchlen 0 (setL_strstart (ls_strstart l2 + ls_matchlen l2) l2) in
          let h0 := ls_window l3 (ls_strstart l3) in
          setL_insh (update_hash g h0 (ls_window l3 (ls_strstart l3 + 1))) l3 in
      let s3 := setD_ls l4 (setD_ts (snd tt) s2) in
      if fst tt then
        match flush_block 0 s3 with
        | (Some bs, s4) => DsRet bs s4
        | (None, s4) => DsCont s4
        end
      else DsCont s3
    else
      let tt := tr_tally_lit (ls_window l1 (ls_strstart l1)) (dg_sym_end g) (d_ts s2) in
      let s3 := setD_ls (setL_strstart (ls_strstart l1 + 1)
                          (setL_lookahead (ls_lookahead l1 - 1) l1))
                        (setD_ts (snd tt) s2) in
      if fst tt then
        match flush_block 0 s3 with
        | (Some bs, s4) => DsRet bs s4
        | (None, s4) => DsCont s4
        end
      else DsCont s3.

Definition df_step (flush : Z) (s : DSt) : DsStep :=
  if (ds_need s) && (ds_need (ds_fill s)) && (Z.eqb flush Z_NO_FLUSH)
  then DsRet NeedMore (ds_fill s)
  else if (ds_need s) && (Z.eqb (ls_lookahead (d_ls (ds_fill s))) 0)
  then DsBreak (ds_fill s)
  else df_body flush (ds_fill s).

Fixpoint df_loop (fuel : nat) (flush : Z) (s : DSt) : option BlockState * DSt :=
  match fuel with
  | O => (Some NeedMore, s)
  | S f => match df_step flush s with
           | DsCont s' => df_loop f flush s'
           | DsRet bs s' => (Some bs, s')
           | DsBreak s' => (None, s')
           end
  end.

Definition deflate_fast (flush : Z) (s : DSt) : BlockState * DSt :=
  match df_loop (ds_fuel s) flush s with
  | (Some bs, s') => (bs, s')
  | (None, s') => ds_tail flush false true s'
  end.

(** ** 13. [deflate_rle] ([deflate.c:2038-2103]) and [deflate_huff] ([:2109-2139]) *)

(** [:2059-2069]: the run length.  [scan] starts at [strstart - 1], the
    three checks at [:2061] cover offsets 0, 1 and 2 OF [strstart], and the
    unrolled loop then compares from offset 3 on with the same 8-fold
    unroll and the same [MAX_MATCH - 2] multiple-of-8 landing as
    [longest_match].  [base] is therefore [strstart], not [strstart - 1] —
    getting that wrong shifts every RLE match by one byte and produces a
    stream that does not inflate (caught by the CPython-zlib cross-check on
    [Z_RLE]). *)
Fixpoint rle_run (fuel : nat) (w : zarr) (base prev j : Z) : Z :=
  match fuel with
  | O => j
  | S f =>
      if Z.leb MAX_MATCH j then MAX_MATCH
      else if Z.eqb (w (base + j)) prev then rle_run f w base prev (j + 1)
      else j
  end.

Definition dr_need (s : DSt) : bool := Z.leb (ls_lookahead (d_ls s)) MAX_MATCH.
Definition dr_fill (s : DSt) : DSt := fill_if (dr_need s) s.

Definition dr_body (flush : Z) (p0 : DSt) : DsStep :=
  let g := d_cfg p0 in
    let l0 := setL_matchlen 0 (d_ls p0) in
    let w  := ls_window l0 in
    let ss := ls_strstart l0 in
    let l1 :=
      if (Z.leb MIN_MATCH (ls_lookahead l0)) && (Z.ltb 0 ss) then
        let pv := w (ss - 1) in
        if (Z.eqb (w ss) pv) && (Z.eqb (w (ss + 1)) pv) && (Z.eqb (w (ss + 2)) pv)
        then let ml := rle_run (Z.to_nat MAX_MATCH) w ss pv 3 in
             setL_matchlen (if Z.ltb (ls_lookahead l0) ml then ls_lookahead l0 else ml) l0
        else l0
      else l0 in
    let s2 := setD_ls l1 p0 in
    if Z.leb MIN_MATCH (ls_matchlen l1) then
      let tt := tr_tally_dist 1 (ls_matchlen l1 - MIN_MATCH) (dg_sym_end g) (d_ts s2) in
      let l2 := setL_matchlen 0
                  (setL_strstart (ls_strstart l1 + ls_matchlen l1)
                    (setL_lookahead (ls_lookahead l1 - ls_matchlen l1) l1)) in
      let s3 := setD_ls l2 (setD_ts (snd tt) s2) in
      if fst tt then match flush_block 0 s3 with
                     | (Some bs, s4) => DsRet bs s4 | (None, s4) => DsCont s4 end
      else DsCont s3
    else
      let tt := tr_tally_lit (w ss) (dg_sym_end g) (d_ts s2) in
      let s3 := setD_ls (setL_strstart (ss + 1) (setL_lookahead (ls_lookahead l1 - 1) l1))
                        (setD_ts (snd tt) s2) in
      if fst tt then match flush_block 0 s3 with
                     | (Some bs, s4) => DsRet bs s4 | (None, s4) => DsCont s4 end
      else DsCont s3.

Definition dr_step (flush : Z) (s : DSt) : DsStep :=
  if (dr_need s) && (dr_need (dr_fill s)) && (Z.eqb flush Z_NO_FLUSH)
  then DsRet NeedMore (dr_fill s)
  else if (dr_need s) && (Z.eqb (ls_lookahead (d_ls (dr_fill s))) 0)
  then DsBreak (dr_fill s)
  else dr_body flush (dr_fill s).

Fixpoint dr_loop (fuel : nat) (flush : Z) (s : DSt) : option BlockState * DSt :=
  match fuel with
  | O => (Some NeedMore, s)
  | S f => match dr_step flush s with
           | DsCont s' => dr_loop f flush s'
           | DsRet bs s' => (Some bs, s')
           | DsBreak s' => (None, s')
           end
  end.

Definition deflate_rle (flush : Z) (s : DSt) : BlockState * DSt :=
  match dr_loop (ds_fuel s) flush s with
  | (Some bs, s') => (bs, s')
  | (None, s') => ds_tail flush false false s'
  end.

Definition dh_need (s : DSt) : bool := Z.eqb (ls_lookahead (d_ls s)) 0.
Definition dh_fill (s : DSt) : DSt := fill_if (dh_need s) s.

Definition dh_body (flush : Z) (p0 : DSt) : DsStep :=
  let g := d_cfg p0 in
    let l0 := setL_matchlen 0 (d_ls p0) in
    let tt := tr_tally_lit (ls_window l0 (ls_strstart l0)) (dg_sym_end g) (d_ts p0) in
    let s3 := setD_ls (setL_strstart (ls_strstart l0 + 1)
                        (setL_lookahead (ls_lookahead l0 - 1) l0))
                      (setD_ts (snd tt) p0) in
    if fst tt then match flush_block 0 s3 with
                   | (Some bs, s4) => DsRet bs s4 | (None, s4) => DsCont s4 end
    else DsCont s3.

Definition dh_step (flush : Z) (s : DSt) : DsStep :=
  if (dh_need s) && (dh_need (dh_fill s)) then
    (if Z.eqb flush Z_NO_FLUSH then DsRet NeedMore (dh_fill s)
     else DsBreak (dh_fill s))
  else dh_body flush (dh_fill s).

Fixpoint dh_loop (fuel : nat) (flush : Z) (s : DSt) : option BlockState * DSt :=
  match fuel with
  | O => (Some NeedMore, s)
  | S f => match dh_step flush s with
           | DsCont s' => dh_loop f flush s'
           | DsRet bs s' => (Some bs, s')
           | DsBreak s' => (None, s')
           end
  end.

Definition deflate_huff (flush : Z) (s : DSt) : BlockState * DSt :=
  match dh_loop (ds_fuel s) flush s with
  | (Some bs, s') => (bs, s')
  | (None, s') => ds_tail flush false false s'
  end.

(** ** 14. [deflate_stored] ([deflate.c:1627-1802]) *)

Definition zmin (a b : Z) : Z := if Z.ltb b a then b else a.

(** The last [k] bytes already consumed from [next_in], i.e. what the C
    reaches as [s->strm->next_in - k]. *)
Definition lastn (k : Z) (l : list Z) : list Z :=
  skipn (Z.to_nat (zlen l - k)) l.

(** [deflate.c:1674-1677]: overwrite the four length bytes the dummy stored
    block just put at the tail of [pending].  [~len] is a 32-bit
    complement, then truncated to a byte at each store. *)
Definition patch_len4 (len : Z) (pd : list Z) : list Z :=
  let n := length pd in
  firstn (n - 4) pd
  ++ [u8 len; u8 (Z.shiftr len 8);
      u8 (Z.lnot len); u8 (Z.shiftr (u32 (Z.lnot len)) 8)].

(** ONE trip of the [do .. while (last == 0)] at [:1640-1709].  The [bool]
    is the [break] at :1648 / :1665; [last] is threaded out. *)
Definition dst_step (flush min_block : Z) (s : DSt) : bool * Z * DSt :=
  let g  := d_cfg s in
  let l  := d_ls s in
  let st := d_strm s in
  let have0 := Z.shiftr (bw_valid (ts_bw (d_ts s)) + 42) 3 in
  if Z.ltb (zs_availout st) have0 then (true, 0, s)
  else
    let have := zs_availout st - have0 in
    let left0 := ls_strstart l - ls_blockstart l in
    let avail := zlen (zs_in st) in
    let len0 := zmin MAX_STORED (zmin (left0 + avail) have) in
    if (Z.ltb len0 min_block)
       && (((Z.eqb len0 0) && negb (Z.eqb flush Z_FINISH))
           || (Z.eqb flush Z_NO_FLUSH)
           || negb (Z.eqb len0 (left0 + avail)))
    then (true, 0, s)
    else
      let last := if (Z.eqb flush Z_FINISH) && (Z.eqb len0 (left0 + avail))
                  then 1 else 0 in
      (* :1671-1677 *)
      let ts1 := tr_stored_block [] 0 last (d_ts s) in
      let ts2 := set_bw {| bw_out := patch_len4 len0 (bw_out (ts_bw ts1));
                           bw_buf := bw_buf (ts_bw ts1);
                           bw_valid := bw_valid (ts_bw ts1) |} ts1 in
      let s1 := flush_pending (setD_ts ts2 s) in
      (* :1689-1698 *)
      let left := zmin left0 len0 in
      let s2 :=
        if Z.eqb left0 0 then s1
        else
          let dat := win_take (ls_window (d_ls s1)) (ls_blockstart (d_ls s1)) left in
          let st1 := d_strm s1 in
          setD_ls (setL_blockstart (ls_blockstart (d_ls s1) + left) (d_ls s1))
            (setD_strm (setZ_out (zs_out st1 ++ dat)
                         (setZ_availout (zs_availout st1 - left)
                           (setZ_totalout (zs_totalout st1 + left) st1))) s1) in
      let len := if Z.eqb left0 0 then len0 else len0 - left in
      (* :1703-1708 *)
      let s3 :=
        if Z.eqb len 0 then s2
        else
          let r := read_buf (d_wrap s2) len (d_strm s2) in
          let dat := fst r in let st2 := snd r in
          setD_strm (setZ_out (zs_out st2 ++ dat)
                      (setZ_availout (zs_availout st2 - len)
                        (setZ_totalout (zs_totalout st2 + len) st2))) s2 in
      (false, last, s3).

Fixpoint dst_loop (fuel : nat) (flush min_block : Z) (s : DSt) : Z * DSt :=
  match fuel with
  | O => (0, s)
  | S f =>
      match dst_step flush min_block s with
      | (true, _, s') => (0, s')
      | (false, last, s') => if Z.eqb last 0 then dst_loop f flush min_block s' else (last, s')
      end
  end.

(** The post-loop window bookkeeping ([deflate.c:1718-1743]), NAMED.

    FACTORED 2026-08-19 (model-rt lane): [deflate_stored] was a single
    ~90-line let-tower, and Coq's conversion zeta-expands let-towers
    eagerly, so the tower's let-multiplicities made ANY
    [deflate_stored ... = ...] statement kernel-intractable (cbv zeta
    alone OOMs 50 GB; kernel conversion against a verbatim alpha-copy
    diverges).  The body is now the same code split at its three seams —
    behaviour-identical by construction ([dispatch] is the only consumer,
    and the ZRepro level-0 vm_compute controls pin exact output bytes
    through this path).  [deflate_slow] was already factored
    ([ds_step]/[ds_loop]); [deflate_stored] was the anomaly. *)
Definition dst_win_update (g : DeflGeom) (used : Z) (s1 : DSt) : DSt :=
if Z.eqb used 0 then s1
    else
      let l := d_ls s1 in
      let ws := dg_w_size g in
      let l' :=
        if Z.leb ws used then
          setL_insert ws (setL_strstart ws
            (setL_window (win_blit (lastn ws (zs_done (d_strm s1))) 0 (ls_window l)) l))
        else
          let la :=
            if Z.leb (ls_windowsize l - ls_strstart l) used then
              let ss := ls_strstart l - ws in
              let l1 := setL_strstart ss (setL_window (win_move 0 ws ss (ls_window l)) l) in
              if Z.ltb ss (ls_insert l1) then setL_insert ss l1 else l1
            else l in
          let lb := setL_window (win_blit (lastn used (zs_done (d_strm s1)))
                                          (ls_strstart la) (ls_window la)) la in
          setL_insert (ls_insert lb + zmin used (ws - ls_insert lb))
            (setL_strstart (ls_strstart lb + used) lb) in
      let ts' := if Z.leb ws used then set_matches 2 (d_ts s1)
                 else if (Z.leb (ls_windowsize (d_ls s1) - ls_strstart (d_ls s1)) used)
                         && (Z.ltb (ts_matches (d_ts s1)) 2)
                      then set_matches (ts_matches (d_ts s1) + 1) (d_ts s1)
                      else d_ts s1 in
      setD_ts ts' (setD_ls (setL_blockstart (ls_strstart l') l') s1).

Definition dst_highwater (s2 : DSt) : DSt :=
  if Z.ltb (ls_highwater (d_ls s2)) (ls_strstart (d_ls s2))
  then setD_ls (setL_highwater (ls_strstart (d_ls s2)) (d_ls s2)) s2 else s2.

Definition dst_tail (flush : Z) (g : DeflGeom) (s3 : DSt) : BlockState * DSt :=
  if negb (Z.eqb flush Z_NO_FLUSH) && negb (Z.eqb flush Z_FINISH)
          && (Z.eqb (zlen (zs_in (d_strm s3))) 0)
          && (Z.eqb (ls_strstart (d_ls s3)) (ls_blockstart (d_ls s3)))
  then (BlockDone, s3)
  else
    (* :1757-1777 *)
    let ws := dg_w_size g in
    let l3 := d_ls s3 in
    let havea := ls_windowsize l3 - ls_strstart l3 in
    let p := if (Z.ltb havea (zlen (zs_in (d_strm s3)))) && (Z.leb ws (ls_blockstart l3))
             then let ss := ls_strstart l3 - ws in
                  let l4 := setL_strstart ss
                              (setL_blockstart (ls_blockstart l3 - ws)
                                (setL_window (win_move 0 ws ss (ls_window l3)) l3)) in
                  let l5 := if Z.ltb ss (ls_insert l4) then setL_insert ss l4 else l4 in
                  (l5, havea + ws, true)
             else (l3, havea, false) in
    let l6 := fst (fst p) in
    let haveb := snd (fst p) in
    let bumped := snd p in
    let ts6 := if bumped && Z.ltb (ts_matches (d_ts s3)) 2
               then set_matches (ts_matches (d_ts s3) + 1) (d_ts s3) else d_ts s3 in
    let have := zmin haveb (zlen (zs_in (d_strm s3))) in
    let s4 := setD_ts ts6 (setD_ls l6 s3) in
    let s5 :=
      if Z.eqb have 0 then s4
      else
        let r2 := read_buf (d_wrap s4) have (d_strm s4) in
        let dat := fst r2 in
        let l7 := setL_window (win_blit dat (ls_strstart l6) (ls_window l6)) l6 in
        let l8 := setL_insert (ls_insert l7 + zmin have (ws - ls_insert l7))
                    (setL_strstart (ls_strstart l7 + have) l7) in
        setD_ls l8 (setD_strm (snd r2) s4) in
    let s6 := if Z.ltb (ls_highwater (d_ls s5)) (ls_strstart (d_ls s5))
              then setD_ls (setL_highwater (ls_strstart (d_ls s5)) (d_ls s5)) s5 else s5 in
    (* :1784-1798 *)
    let have2a := Z.shiftr (bw_valid (ts_bw (d_ts s6)) + 42) 3 in
    let have2 := zmin (dg_pending_buf_size g - have2a) MAX_STORED in
    let mb2 := zmin have2 ws in
    let left := ls_strstart (d_ls s6) - ls_blockstart (d_ls s6) in
    if (Z.leb mb2 left)
       || ((negb (Z.eqb left 0) || Z.eqb flush Z_FINISH)
           && negb (Z.eqb flush Z_NO_FLUSH)
           && (Z.eqb (zlen (zs_in (d_strm s6))) 0)
           && (Z.leb left have2))
    then
      let len := zmin left have2 in
      let last := if (Z.eqb flush Z_FINISH) && (Z.eqb (zlen (zs_in (d_strm s6))) 0)
                     && (Z.eqb len left) then 1 else 0 in
      let dat := win_take (ls_window (d_ls s6)) (ls_blockstart (d_ls s6)) len in
      let s7 := setD_ts (tr_stored_block dat len last (d_ts s6))
                  (setD_ls (setL_blockstart (ls_blockstart (d_ls s6) + len) (d_ls s6)) s6) in
      let s8 := flush_pending s7 in
      (if Z.eqb last 0 then NeedMore else FinishStarted, s8)
    else (NeedMore, s6).

Definition deflate_stored (flush : Z) (s : DSt) : BlockState * DSt :=
  let g := d_cfg s in
  (* :1632 *)
  let min_block := zmin (dg_pending_buf_size g - 5) (dg_w_size g) in
  let used0 := zlen (zs_in (d_strm s)) in
  let r := dst_loop (Z.to_nat (zs_availout (d_strm s) / 5) + 3) flush min_block s in
  let last0 := fst r in let s1 := snd r in
  let used := used0 - zlen (zs_in (d_strm s1)) in
  let s3 := dst_highwater (dst_win_update g used s1) in
  if negb (Z.eqb last0 0) then (FinishDone, s3)
  else dst_tail flush g s3.

(** ** 15. [deflate] ([deflate.c:946-1255])

    [DfUnmodelled] is RETAINED for interface stability (consumers match
    on it: [Codec.v:247], [CodecThy.v:107], [ZRepro.v]) but is no longer
    produced anywhere: the [wrap == 2] write path is transcribed as of
    2026-08-19 ([gzhead == Z_NULL] arm; see the file header). *)
Inductive DfOut : Type :=
| DfRet (code : Z) (s : DSt)
| DfUnmodelled.

(** [:1182-1185]: the compression-function dispatch. *)
Definition dispatch (flush : Z) (s : DSt) : BlockState * DSt :=
  let g := d_cfg s in
  if Z.eqb (dg_level g) 0 then deflate_stored flush s
  else if Z.eqb (dg_strategy g) Z_HUFFMAN_ONLY then deflate_huff flush s
  else if Z.eqb (dg_strategy g) Z_RLE then deflate_rle flush s
  else match cfg_func (dg_level g) with
       | DfStored => deflate_stored flush s
       | DfFast   => deflate_fast flush s
       | DfSlow   => deflate_slow flush s
       end.

(** [:996-1029]: the two-byte zlib header (the [PRESET_DICT] arm included,
    though [deflateSetDictionary] is never called here). *)
Definition zlib_header (s : DSt) : DSt :=
  let g := d_cfg s in
  let hdr0 := Z.shiftl (Z_DEFLATED + Z.shiftl (dg_w_bits g - 8) 4) 8 in
  let lf := if (Z.leb Z_HUFFMAN_ONLY (dg_strategy g)) || (Z.ltb (dg_level g) 2) then 0
            else if Z.ltb (dg_level g) 6 then 1
            else if Z.eqb (dg_level g) 6 then 2 else 3 in
  let hdr1 := Z.lor hdr0 (Z.shiftl lf 6) in
  let hdr2 := if negb (Z.eqb (ls_strstart (d_ls s)) 0)
              then Z.lor hdr1 PRESET_DICT else hdr1 in
  let hdr := hdr2 + 31 - (hdr2 mod 31) in
  let ts0 := putShortMSB hdr (d_ts s) in
  let ts1 := if negb (Z.eqb (ls_strstart (d_ls s)) 0)
             then putShortMSB (Z.land (zs_adler (d_strm s)) 65535)
                    (putShortMSB (Z.shiftr (zs_adler (d_strm s)) 16) ts0)
             else ts0 in
  setD_status BUSY_STATE
    (setD_strm (setZ_adler (adler32_z 0 true []) (d_strm s)) (setD_ts ts1 s)).

(** [deflate.h:287] [put_byte], on the [TSt] the header/trailer code
    works through ([bw_put_byte] applies the [(Bytef)] cast). *)
Definition put_byte (v : Z) (ts : TSt) : TSt :=
  set_bw (bw_put_byte v (ts_bw ts)) ts.

(** [:1031-1055]: the ten-byte gzip header, [gzhead == Z_NULL] arm only
    (see the file header).  Statement order mirrors the C:
    [strm->adler = crc32(0,Z_NULL,0)] first, then ten [put_byte]s
    (magic 31 139, CM 8, FLG 0, MTIME 0x4, XFL by level, OS), then
    [status = BUSY_STATE].  The caller ([deflate_body]) does the
    "Compression must start with an empty pending buffer" flush. *)
Definition gzip_header (s : DSt) : DSt :=
  let g := d_cfg s in
  let s0 := setD_strm (setZ_adler (crc32_z 0 true 0 []) (d_strm s)) s in
  let xfl := if Z.eqb (dg_level g) 9 then 2
             else if (Z.leb Z_HUFFMAN_ONLY (dg_strategy g))
                     || (Z.ltb (dg_level g) 2) then 4 else 0 in
  let ts := put_byte OS_CODE (put_byte xfl (put_byte 0 (put_byte 0
              (put_byte 0 (put_byte 0 (put_byte 0 (put_byte 8
                (put_byte 139 (put_byte 31 (d_ts s0))))))))))  in
  setD_status BUSY_STATE (setD_ts ts s0).

(** [:1231-1254]: the zlib (or gzip) trailer. *)
Definition deflate_trailer (s : DSt) : DfOut :=
  let ts :=
    if Z.eqb (d_wrap s) 2 then
      (* :1233-1242 gzip: CRC32 then ISIZE ([total_in]), both LE;
         [put_byte]'s [u8] is the C's [(Byte)(... & 0xff)] *)
      let ad := zs_adler (d_strm s) in
      let ti := zs_totalin (d_strm s) in
      put_byte (Z.shiftr ti 24) (put_byte (Z.shiftr ti 16)
        (put_byte (Z.shiftr ti 8) (put_byte ti
          (put_byte (Z.shiftr ad 24) (put_byte (Z.shiftr ad 16)
            (put_byte (Z.shiftr ad 8) (put_byte ad (d_ts s))))))))
    else
      (* :1245-1248 zlib: adler, MSB *)
      let ad := zs_adler (d_strm s) in
      putShortMSB (Z.land ad 65535) (putShortMSB (Z.shiftr ad 16) (d_ts s)) in
  let s1 := flush_pending (setD_ts ts s) in
  let s2 := if Z.ltb 0 (d_wrap s1) then setD_wrap (- d_wrap s1) s1 else s1 in
  DfRet (if negb (Z.eqb (zlen (bw_out (ts_bw (d_ts s2)))) 0) then Z_OK else Z_STREAM_END) s2.

(** [:1176-1254], after the header states. *)
Definition deflate_run (flush : Z) (s : DSt) : DfOut :=
  let s1 :=
    if (negb (Z.eqb (zlen (zs_in (d_strm s))) 0))
       || (negb (Z.eqb (ls_lookahead (d_ls s)) 0))
       || (negb (Z.eqb flush Z_NO_FLUSH) && negb (Z.eqb (d_status s) FINISH_STATE))
    then Some (dispatch flush s) else None in
  match s1 with
  | Some (bs, sa) =>
      let sb := match bs with
                | FinishStarted | FinishDone => setD_status FINISH_STATE sa
                | _ => sa
                end in
      match bs with
      | NeedMore | FinishStarted =>
          DfRet Z_OK (if Z.eqb (zs_availout (d_strm sb)) 0
                      then setD_lastflush (-1) sb else sb)
      | BlockDone =>
          let sc :=
            if Z.eqb flush Z_PARTIAL_FLUSH then setD_ts (tr_align (d_ts sb)) sb
            else if negb (Z.eqb flush Z_BLOCK) then
              let sd := setD_ts (tr_stored_block [] 0 0 (d_ts sb)) sb in
              if Z.eqb flush Z_FULL_FLUSH then
                let le := clear_hash (d_cfg sd) (d_ls sd) in
                setD_ls (if Z.eqb (ls_lookahead le) 0
                         then setL_insert 0 (setL_blockstart 0 (setL_strstart 0 le))
                         else le) sd
              else sd
            else sb in
          let se := flush_pending sc in
          if Z.eqb (zs_availout (d_strm se)) 0
          then DfRet Z_OK (setD_lastflush (-1) se)
          else if negb (Z.eqb flush Z_FINISH) then DfRet Z_OK se
          else if Z.leb (d_wrap se) 0 then DfRet Z_STREAM_END se
          else deflate_trailer se
      | FinishDone =>
          if negb (Z.eqb flush Z_FINISH) then DfRet Z_OK sb
          else if Z.leb (d_wrap sb) 0 then DfRet Z_STREAM_END sb
          else deflate_trailer sb
      end
  | None =>
      if negb (Z.eqb flush Z_FINISH) then DfRet Z_OK s
      else if Z.leb (d_wrap s) 0 then DfRet Z_STREAM_END s
      else deflate_trailer s
  end.

(** [:989-1029] plus the gzip cut. *)
Definition deflate_body (flush : Z) (s : DSt) : DfOut :=
  if (Z.eqb (d_status s) FINISH_STATE) && negb (Z.eqb (zlen (zs_in (d_strm s))) 0)
  then DfRet Z_BUF_ERROR s
  else
    let s0 := if (Z.eqb (d_status s) INIT_STATE) && (Z.eqb (d_wrap s) 0)
              then setD_status BUSY_STATE s else s in
    if Z.eqb (d_status s0) INIT_STATE then
      let s1 := zlib_header s0 in
      let s2 := flush_pending s1 in
      if negb (Z.eqb (zlen (bw_out (ts_bw (d_ts s2)))) 0)
      then DfRet Z_OK (setD_lastflush (-1) s2)
      else deflate_run flush s2
    else if Z.eqb (d_status s0) GZIP_STATE then
      (* :1031-1055, gzhead == Z_NULL: the ten header bytes, then
         "Compression must start with an empty pending buffer" *)
      let s1 := gzip_header s0 in
      let s2 := flush_pending s1 in
      if negb (Z.eqb (zlen (bw_out (ts_bw (d_ts s2)))) 0)
      then DfRet Z_OK (setD_lastflush (-1) s2)
      else deflate_run flush s2
    else deflate_run flush s0.

(** ** 16. [deflateResetKeep] / [deflateReset] / [deflateInit2_]
    ([deflate.c:635-702] and [:379-524])

    The geometry itself is [Chunk.v]'s [defl_init2], already validated on
    707 [deflateInit2_] records; this is the state it is wrapped in.  The
    window is [ZALLOC]ed and NOT zeroed, so its initial contents are
    arbitrary; [high_water] exists precisely to bound the defined region,
    and the model's zeros are as good as any other choice for indices the C
    never reads (recorded in [defl_wf]). *)
Definition deflate_reset (g : DeflGeom) (wrap : Z) : DSt :=
  let l0 := {| ls_window := zzero; ls_prev := zzero; ls_head := zzero;
               ls_insh := 0; ls_blockstart := 0; ls_matchlen := 0;
               ls_prevmatch := 0; ls_matchavail := 0; ls_strstart := 0;
               ls_matchstart := 0; ls_lookahead := 0; ls_prevlen := 0;
               ls_insert := 0; ls_highwater := 0; ls_windowsize := 0 |} in
  {| d_cfg := g;
     d_status := if Z.eqb wrap 2 then GZIP_STATE else INIT_STATE;
     d_lastflush := -2;
     d_wrap := wrap;
     d_ts := tr_init ts_new;
     d_ls := lm_init g l0;
     d_strm := {| zs_in := []; zs_done := []; zs_out := [];
                  zs_availout := 0; zs_totalin := 0; zs_totalout := 0;
                  zs_adler := if Z.eqb wrap 2 then crc32_z 0 true 0 []
                              else adler32_z 0 true [];  (* :658-663 *)
                  zs_datatype := Z_UNKNOWN |} |}.

Definition defl_new (level0 method windowBits memLevel strategy : Z) : option DSt :=
  match defl_init2 level0 method windowBits memLevel strategy with
  | None => None
  | Some g => Some (deflate_reset g (dg_wrap g))
  end.

(** [:946-991]. *)
Definition deflate (flush : Z) (s : DSt) : DfOut :=
  if (Z.ltb Z_BLOCK flush) || (Z.ltb flush 0) then DfRet Z_STREAM_ERROR s
  else if (Z.eqb (d_status s) FINISH_STATE) && negb (Z.eqb flush Z_FINISH)
  then DfRet Z_STREAM_ERROR s
  else if Z.eqb (zs_availout (d_strm s)) 0 then DfRet Z_BUF_ERROR s
  else
    let old_flush := d_lastflush s in
    let s0 := setD_lastflush flush s in
    if negb (Z.eqb (zlen (bw_out (ts_bw (d_ts s0)))) 0) then
      let s1 := flush_pending s0 in
      if Z.eqb (zs_availout (d_strm s1)) 0 then DfRet Z_OK (setD_lastflush (-1) s1)
      else deflate_body flush s1
    else if (Z.eqb (zlen (zs_in (d_strm s0))) 0)
            && (Z.leb (RANK flush) (RANK old_flush))
            && negb (Z.eqb flush Z_FINISH)
    then DfRet Z_BUF_ERROR s0
    else deflate_body flush s0.

(** ** 16. Well-formedness of a [deflate.c] call *)

Record defl_wf (s : DSt) : Prop := mkDeflWf {
  (** libpng-era theory obligation — its consumers rely on the zlib
      trailer arm.  The gzip WRITE path itself is modeled as of
      2026-08-19; a gzip-side wf record is the Q3 theory follow-up. *)
  wf_wrap      : 0 <= d_wrap s <= 1;
  (** [deflateInit2_]'s geometry, as [Chunk.v] computes it *)
  wf_geom      : d_cfg s = defl_geom_wrap (d_wrap s) (dg_level (d_cfg s))
                             (dg_w_bits (d_cfg s))
                             (dg_hash_bits (d_cfg s) - 7) (dg_strategy (d_cfg s));
  (** [deflate.c:366]: the loop invariant [fill_window] promises *)
  wf_room      : ls_strstart (d_ls s) + ls_lookahead (d_ls s)
                 <= ls_windowsize (d_ls s);
  wf_windowsize: ls_windowsize (d_ls s) = 2 * dg_w_size (d_cfg s);
  (** match lengths never exceed [MAX_MATCH] *)
  wf_matchlen  : ls_matchlen (d_ls s) <= MAX_MATCH
                 /\ ls_prevlen (d_ls s) <= MAX_MATCH;
  (** [trees.c]'s own obligations *)
  wf_trees     : tr_wf (d_ts s) (dg_sym_end (d_cfg s))
}.

(** ** 17. The three token contracts on this transcription

    c5-invariants.md §2.2.  [cEnc] / [cEmpty] / [cRes] (defined in
    [Trees.v]) are the ONLY facts the round-trip core may use about
    anything in this file.  Everything below is proved; nothing is
    asserted. *)

(** *** The bound behind [cEnc]'s [len <= MAX_MATCH]

    [lm_cpl] can never report more than [MAX_MATCH], whatever the window
    holds — which is why zlib's 8-fold unrolled compare loop, whose
    [scan < strend] test only fires every 8th byte, cannot overrun
    ([MAX_MATCH - 2 = 256] is a multiple of 8). *)
Lemma lm_cpl_le : forall f w a b j, j <= MAX_MATCH -> lm_cpl f w a b j <= MAX_MATCH.
Proof.
  induction f as [|f IH]; intros w a b j Hj; cbn [lm_cpl]; [assumption|].
  destruct (Z.leb MAX_MATCH j) eqn:E; [lia|].
  apply Z.leb_gt in E.
  destruct (Z.eqb (w (a + j)) (w (b + j))); [apply IH; lia | lia].
Qed.

Lemma lm_cpl_ge : forall f w a b j, j <= MAX_MATCH -> j <= lm_cpl f w a b j.
Proof.
  induction f as [|f IH]; intros w a b j Hj; cbn [lm_cpl]; [lia|].
  destruct (Z.leb MAX_MATCH j) eqn:E; [lia|].
  apply Z.leb_gt in E.
  destruct (Z.eqb (w (a + j)) (w (b + j))); [|lia].
  specialize (IH w a b (j + 1) ltac:(lia)). lia.
Qed.

Lemma lm_len_le : forall c st, lm_len c st <= MAX_MATCH.
Proof.
  intros c st. unfold lm_len. destruct (lm_ok c st).
  - apply lm_cpl_le. unfold MAX_MATCH; lia.
  - unfold MAX_MATCH; lia.
Qed.

Lemma lm_next_best_le :
  forall c st, m_best st <= MAX_MATCH -> m_best (lm_next c st) <= MAX_MATCH.
Proof.
  intros c st H. unfold lm_next. destruct (lm_hit c st); cbn [m_best].
  - apply lm_len_le.
  - assumption.
Qed.

Lemma lm_step_best_le :
  forall c st st', m_best st <= MAX_MATCH ->
    (lm_step c st = LmCont st' \/ lm_step c st = LmDone st') ->
    m_best st' <= MAX_MATCH.
Proof.
  intros c st st' Hb H.
  pose proof (lm_next_best_le c st Hb) as Hn.
  unfold lm_step in H.
  destruct (lm_hit c st && Z.leb (x_nice c) (lm_len c st)).
  - destruct H as [H|H]; [discriminate|]. inversion H; subst. assumption.
  - destruct ((Z.ltb (x_limit c) (x_prev c (Z.land (m_cur st) (x_wmask c))))
              && negb (Z.eqb (m_chain (lm_next c st) - 1) 0));
      destruct H as [H|H]; try discriminate; inversion H; subst;
      cbn [m_best]; assumption.
Qed.

Lemma lm_loop_best_le :
  forall f c st, m_best st <= MAX_MATCH -> m_best (lm_loop f c st) <= MAX_MATCH.
Proof.
  induction f as [|f IH]; intros c st H; cbn [lm_loop]; [assumption|].
  destruct (lm_step c st) as [st'|st'] eqn:E.
  - apply IH. eapply lm_step_best_le; eauto.
  - eapply lm_step_best_le; eauto.
Qed.

(** The [len <= MAX_MATCH] half of [cEnc], for any window and any chain. *)
Lemma longest_match_le_MAX :
  forall g l cm, ls_prevlen l <= MAX_MATCH -> fst (longest_match g l cm) <= MAX_MATCH.
Proof.
  intros g l cm H. unfold longest_match; cbn [fst].
  set (stf := lm_loop _ _ _).
  assert (Hb : m_best stf <= MAX_MATCH) by (apply lm_loop_best_le; cbn [m_best]; lia).
  destruct (Z.leb (m_best stf) (ls_lookahead l)) eqn:E; [assumption|].
  apply Z.leb_gt in E. lia.
Qed.

(** *** [hash3_det] — why zlib may skip the [scan[2]] comparison

    [longest_match] does not compare offset 2 ([deflate.c:1446-1450]).  It is
    entitled to because a candidate only reaches the compare loop if it is on
    the hash chain for [window[strstart..strstart+2]] AND offsets 0 and 1
    were byte-checked, and the 3-byte hash is [UPDATE_HASH] applied to the
    third byte on top of a value determined by the first two — an operation
    that is INJECTIVE in that third byte, because the byte contributes only
    bits below [hash_bits].  That is this lemma, and it is the load-bearing
    step of [cRes]: without it the emitted match could disagree with the
    history at offset 2 and the round trip would be false. *)
Lemma land_lxor_distr :
  forall a b m, Z.land (Z.lxor a b) m = Z.lxor (Z.land a m) (Z.land b m).
Proof.
  intros a b m. apply Z.bits_inj'; intros n Hn.
  rewrite Z.land_spec, !Z.lxor_spec, !Z.land_spec.
  now destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit m n).
Qed.

Lemma hash3_det :
  forall g h b b' k,
    0 <= k -> dg_hash_mask g = 2 ^ k - 1 ->
    0 <= b < 2 ^ k -> 0 <= b' < 2 ^ k ->
    update_hash g h b = update_hash g h b' -> b = b'.
Proof.
  intros g h b b' k Hk Hm Hb Hb' H.
  unfold update_hash in H. rewrite Hm in H.
  replace (2 ^ k - 1) with (Z.ones k) in H by (rewrite Z.ones_equiv; lia).
  rewrite !land_lxor_distr in H.
  rewrite !Z.land_ones in H by lia.
  rewrite (Z.mod_small b (2 ^ k)) in H by lia.
  rewrite (Z.mod_small b' (2 ^ k)) in H by lia.
  set (A := Z.shiftl h (dg_hash_shift g) mod 2 ^ k) in H.
  assert (Hxor : Z.lxor A (Z.lxor A b) = Z.lxor A (Z.lxor A b'))
    by (now rewrite H).
  rewrite <- !Z.lxor_assoc, Z.lxor_nilpotent, !Z.lxor_0_l in Hxor.
  exact Hxor.
Qed.

(** The instance this build actually runs: [memLevel 8] gives
    [hash_bits = 15] and [hash_mask = 32767], and every window byte is a
    [u8], so the third byte of the 3-byte key is determined by the hash. *)
Corollary hash3_det_l8 :
  forall g h b b',
    dg_hash_mask g = 32767 -> 0 <= b < 256 -> 0 <= b' < 256 ->
    update_hash g h b = update_hash g h b' -> b = b'.
Proof.
  intros g h b b' Hm Hb Hb' H.
  apply (hash3_det g h b b' 15); try lia; assumption.
Qed.

(** *** [cEmpty] — empty input tallies nothing

    With no input left and no lookahead, [deflate_slow]'s body cannot reach
    a [_tr_tally_*]: [fill_window] adds nothing, and the C either returns
    [need_more] ([Z_NO_FLUSH]) or breaks out to the tail.  The
    [trees.c]-owned cluster is therefore returned untouched. *)
Lemma fw_highwater_lookahead :
  forall l, ls_lookahead (fw_highwater l) = ls_lookahead l.
Proof.
  intros l. unfold fw_highwater.
  destruct (Z.ltb (ls_highwater l) (ls_windowsize l)); [|reflexivity].
  destruct (Z.ltb (ls_highwater l) (ls_strstart l + ls_lookahead l));
    [reflexivity|].
  destruct (Z.ltb (ls_highwater l)
                  (ls_strstart l + ls_lookahead l + WIN_INIT)); reflexivity.
Qed.

Lemma fw_step_empty :
  forall g wrap l st, zs_in st = [] ->
    exists l', fw_step g wrap l st = (true, l', st)
               /\ ls_lookahead l' = ls_lookahead l.
Proof.
  intros g wrap l st Hin. unfold fw_step.
  replace (Z.eqb (zlen (zs_in st)) 0) with true
    by (rewrite Hin; reflexivity).
  destruct (Z.leb (dg_w_size g + dg_max_dist g) (ls_strstart l));
    cbn [fst snd]; eexists; split; try reflexivity.
  match goal with |- context [if ?b then _ else _] => destruct b end;
    reflexivity.
Qed.

Lemma fw_loop_empty :
  forall f g wrap l st, zs_in st = [] ->
    ls_lookahead (fst (fw_loop (S f) g wrap l st)) = ls_lookahead l.
Proof.
  intros f g wrap l st Hin. cbn [fw_loop].
  destruct (fw_step_empty g wrap l st Hin) as [l' [E Hla]].
  rewrite E. cbn [fst]. assumption.
Qed.

(** [fill_window] adds no lookahead once the input is exhausted — the
    termination fact [deflate_slow]'s loop and [cEmpty] both rest on. *)
Lemma fw_lookahead_empty :
  forall g wrap l st,
    zs_in st = [] ->
    ls_lookahead (fst (fill_window g wrap l st)) = ls_lookahead l.
Proof.
  intros g wrap l st Hin. unfold fill_window. cbn [fst].
  rewrite fw_highwater_lookahead.
  replace (Z.to_nat (zlen (zs_in st)) + 2)%nat
    with (S (S (Z.to_nat (zlen (zs_in st))))) by lia.
  apply fw_loop_empty. assumption.
Qed.

Lemma ds_fill_ts : forall s, d_ts (ds_fill s) = d_ts s.
Proof.
  intros s. unfold ds_fill, fill_if.
  destruct (ds_need s); reflexivity.
Qed.

Lemma ds_fill_lookahead_empty :
  forall s, zs_in (d_strm s) = [] ->
    ls_lookahead (d_ls (ds_fill s)) = ls_lookahead (d_ls s).
Proof.
  intros s Hin. unfold ds_fill, fill_if.
  destruct (ds_need s); [|reflexivity].
  cbn [d_ls setD_strm setD_ls]. now apply fw_lookahead_empty.
Qed.

Lemma ds_step_empty_no_tally :
  forall flush s,
    zs_in (d_strm s) = [] -> ls_lookahead (d_ls s) = 0 ->
    exists s', (ds_step flush s = DsBreak s'
                \/ ds_step flush s = DsRet NeedMore s')
               /\ d_ts s' = d_ts s.
Proof.
  intros flush s Hin Hla. unfold ds_step, ds_need.
  rewrite (ds_fill_lookahead_empty s Hin), Hla.
  replace (Z.ltb 0 MIN_LOOKAHEAD) with true by reflexivity.
  cbn [andb].
  destruct (Z.eqb flush Z_NO_FLUSH).
  - exists (ds_fill s). split; [right; reflexivity | apply ds_fill_ts].
  - cbn [andb]. replace (Z.eqb 0 0) with true by reflexivity.
    exists (ds_fill s). split; [left; reflexivity | apply ds_fill_ts].
Qed.

Lemma deflate_slow_empty_no_tokens :
  forall flush s,
    zs_in (d_strm s) = [] -> ls_lookahead (d_ls s) = 0 ->
    ts_symnext (d_ts s) = 0 ->
    sym_tokens (d_ts (snd (ds_loop (ds_fuel s) flush s))) = [].
Proof.
  intros flush s Hin Hla Hsn.
  unfold ds_fuel. rewrite Hin, Hla. cbn [zlen length Z.of_nat].
  replace (Z.to_nat (0 + 0) + 2)%nat with (S (S O)) by reflexivity.
  cbn [ds_loop].
  destruct (ds_step_empty_no_tally flush s Hin Hla) as [s' [[H|H] Hts]];
    rewrite H; cbn [snd];
    apply sym_tokens_empty; rewrite Hts; assumption.
Qed.

(** [cEmpty] itself: an exhausted input contributes no tokens. *)
Corollary cEmpty_deflate_slow :
  forall flush s,
    zs_in (d_strm s) = [] -> ls_lookahead (d_ls s) = 0 ->
    ts_symnext (d_ts s) = 0 ->
    cEmpty [] (sym_tokens (d_ts (snd (ds_loop (ds_fuel s) flush s)))).
Proof.
  intros flush s H1 H2 H3 _. now apply deflate_slow_empty_no_tokens.
Qed.

(** ** Fuel monotonicity and the two loop measures

    Neither [lm_loop] nor [ds_loop] returns an [option]: [lm_loop 0] gives
    back the state unchanged and [ds_loop 0] gives [(Some NeedMore, s)],
    which is also a legitimate answer.  So "more fuel does not change the
    answer" cannot be conditioned on a sentinel; it has to be conditioned
    on the loop actually REACHING a terminating step, and the [_iter]
    functions say exactly that: [_iter f = Some _] means all [f] trips fell
    through, so [_iter f = None] means the loop stopped within [f]. *)

Lemma lm_loop_fuel_mono :
  forall f f' c st,
    (f <= f')%nat -> lm_iter f c st = None ->
    lm_loop f' c st = lm_loop f c st.
Proof.
  induction f as [|f IH]; intros f' c st Hle H;
    [cbn [lm_iter] in H; discriminate H|].
  destruct f' as [|f']; [lia|].
  cbn [lm_iter] in H. cbn [lm_loop].
  destruct (lm_step c st) as [st1|st1].
  - apply IH; [lia | exact H].
  - reflexivity.
Qed.

(** [deflate.c:1484-1485]: [longest_match]'s [while] runs [chain_length]
    down and stops at zero, so [chain_length] IS the measure and
    [max_chain_length + 2] is the fuel [longest_match] passes.  Read
    through a projection rather than [injection]: [LmCont]'s argument is a
    record of six [x_win]/[x_prev] applications, and [injection] on that
    is the shape that does not terminate (see [Inftrees.it_sym_of]). *)
Definition lm_measure (st : LmSt) : Z := m_chain st.

Lemma lm_next_chain : forall c st, m_chain (lm_next c st) = m_chain st.
Proof. intros c st; unfold lm_next; destruct (lm_hit c st); reflexivity. Qed.

Definition lm_cont_chain (r : LmStep) (d : Z) : Z :=
  match r with LmCont s => m_chain s | LmDone _ => d end.

Lemma lm_step_chain_all :
  forall c st, lm_cont_chain (lm_step c st) (m_chain st - 1) = m_chain st - 1.
Proof.
  intros c st. unfold lm_step. cbv zeta.
  repeat (match goal with
          | |- context [if ?b then _ else _] => destruct b eqn:?; cbv iota
          end);
    cbn [lm_cont_chain m_chain]; rewrite ?lm_next_chain; reflexivity.
Qed.

Lemma lm_step_decreases :
  forall c st st',
    lm_step c st = LmCont st' -> lm_measure st' = lm_measure st - 1.
Proof.
  intros c st st' H. unfold lm_measure.
  pose proof (lm_step_chain_all c st) as Hc. rewrite H in Hc.
  cbn [lm_cont_chain] in Hc. exact Hc.
Qed.

(** [deflate_slow]'s [for(;;)] has no counter of its own, so it needs the
    [_iter] form.  [ds_iter k] is "the first [k] trips were all
    [DsCont]". *)
Fixpoint ds_iter (k : nat) (flush : Z) (s : DSt) : option DSt :=
  match k with
  | O => Some s
  | S k' => match ds_step flush s with
            | DsCont s' => ds_iter k' flush s'
            | _ => None
            end
  end.

Lemma ds_loop_fuel_mono :
  forall f f' flush s,
    (f <= f')%nat -> ds_iter f flush s = None ->
    ds_loop f' flush s = ds_loop f flush s.
Proof.
  induction f as [|f IH]; intros f' flush s Hle H;
    [cbn [ds_iter] in H; discriminate H|].
  destruct f' as [|f']; [lia|].
  cbn [ds_iter] in H. cbn [ds_loop].
  destruct (ds_step flush s) as [s1|bs s1|s1].
  - apply IH; [lia | exact H].
  - reflexivity.
  - reflexivity.
Qed.

Lemma ds_iter_loop :
  forall k f flush s s',
    ds_iter k flush s = Some s' ->
    ds_loop (k + f) flush s = ds_loop f flush s'.
Proof.
  induction k as [|k IH]; intros f flush s s' H; cbn [ds_iter] in H.
  - injection H as H; subst s'. reflexivity.
  - cbn [Nat.add]. cbn [ds_loop].
    destruct (ds_step flush s) as [s1|bs s1|s1]; try discriminate H.
    now apply IH.
Qed.

(** NO [ds_measure] IS SHIPPED, and that is deliberate.  [deflate_slow]'s
    trip count is bounded by the lookahead the window can supply, which is
    a fact about [fill_window] and [strstart] rather than about any field
    the loop itself decrements; writing down a plausible-looking
    [Definition] here would fix the wrong shape for the round-trip lane and
    cost more than it saves.  [ds_iter] / [ds_loop_fuel_mono] /
    [ds_iter_loop] give the lane what it actually needs to reason about the
    loop without one. *)

(** ** 18. gzip-wrapper controls (2026-08-19 extension)

    Differentially validated against zlib-1.3.1 ITSELF: the shipped source
    ([/harness/problem/materials/zlib-1.3.1]) compiled host-side and run on
    the same inputs — one-shot [deflate(Z_FINISH)] after
    [deflateInit2(level, Z_DEFLATED, 31, 8, Z_DEFAULT_STRATEGY)] with
    [avail_out >= deflateBound].  Byte-identical streams, return code
    [Z_STREAM_END] (harness: [a working folder]).
    Fixed-table t0: the ten header bytes, XFL by level ([:1043-1045]:
    9 -> 2, < 2 or HUFFMAN -> 4, else 0), OS = 3. *)

Example gzip_header_bytes_by_level :
  match defl_new 9 8 31 8 0, defl_new 1 8 31 8 0, defl_new 6 8 31 8 0 with
  | Some s9, Some s1, Some s6 =>
      (bw_out (ts_bw (d_ts (gzip_header s9))),
       bw_out (ts_bw (d_ts (gzip_header s1))),
       bw_out (ts_bw (d_ts (gzip_header s6))))
      = ([31;139;8;0;0;0;0;0;2;3],
         [31;139;8;0;0;0;0;0;4;3],
         [31;139;8;0;0;0;0;0;0;3])
  | _, _, _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** zlib-1.3.1: [rc=1 out=]
    on input "H" (0x48) at level 9 — CRC32("H") = 0xaa05262f LE, ISIZE 1. *)
Example gzip_stream_level9_H :
  match defl_new 9 8 31 8 0 with
  | Some s0 =>
      match deflate Z_FINISH
              (setD_strm (setZ_availout 100 (setZ_in [72] (d_strm s0))) s0) with
      | DfRet code s2 =>
          (code, zs_out (d_strm s2))
          = (Z_STREAM_END,
             [31;139;8;0;0;0;0;0;2;3; 243;0;0; 47;38;5;170; 1;0;0;0])
      | DfUnmodelled => False
      end
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** zlib-1.3.1: [rc=1 out=] on the
    empty input at level 9 — CRC32 and ISIZE both 0. *)
Example gzip_stream_level9_empty :
  match defl_new 9 8 31 8 0 with
  | Some s0 =>
      match deflate Z_FINISH
              (setD_strm (setZ_availout 100 (setZ_in [] (d_strm s0))) s0) with
      | DfRet code s2 =>
          (code, zs_out (d_strm s2))
          = (Z_STREAM_END,
             [31;139;8;0;0;0;0;0;2;3; 3;0; 0;0;0;0; 0;0;0;0])
      | DfUnmodelled => False
      end
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** zlib-1.3.1: [rc=1 out=] on
    input 01 02 03 at level 1 — the fast path under the gzip wrapper,
    XFL = 4, CRC32 = 0x55bc801d LE, ISIZE 3. *)
Example gzip_stream_level1_bytes :
  match defl_new 1 8 31 8 0 with
  | Some s0 =>
      match deflate Z_FINISH
              (setD_strm (setZ_availout 100 (setZ_in [1;2;3] (d_strm s0))) s0) with
      | DfRet code s2 =>
          (code, zs_out (d_strm s2))
          = (Z_STREAM_END,
             [31;139;8;0;0;0;0;0;4;3; 99;100;98;6;0; 29;128;188;85; 3;0;0;0])
      | DfUnmodelled => False
      end
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

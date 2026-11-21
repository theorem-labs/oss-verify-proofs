(** * Spec.PngModel.InflateFast — transcription of zlib-1.3.1's [inflate_fast].

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.  Depends only on
    [Spec.PngModel.Base], [Spec.PngModel.ZBitsIn] and Stdlib.

    Source: [materials/zlib-1.3.1/inffast.c] (in-container
    [/harness/problem/materials/zlib-1.3.1/inffast.c]), the whole file.
    [ASMINF] is not defined, so the C body at [:11-320] is what was
    compiled (691 instructions, skeleton-identical on both binaries —
    c5-invariants.md §3.4).

    BUG-FOR-BUG.  This is a transcription of the SHIPPED loop, not of RFC
    1951.  In particular:

    - [INFLATE_STRICT] is NOT defined in this build
      ([materials/Makefile:18] has only [-O2 -static -no-pie], and
      [RT_DEFS] adds no zlib defines), so the [dist > dmax] rejection at
      [inffast.c:152-157] is compiled out.  A distance larger than the
      window the zlib header advertised is NOT rejected here; only
      [op > whave] is.  Modelled by its absence, deliberately.
    - [INFLATE_ALLOW_INVALID_DISTANCE_TOOFAR_ARRR] is not defined either
      (note the spelling — this vendored copy uses the [_ARRR] suffix), so
      the zero-fill arm at [inffast.c:171-186] is compiled out.  What
      survives is
      [[if (op > whave) { if (state->sane) { BAD; break; } }]] — with an
      EMPTY else, so a hypothetical [sane == 0] falls through into the
      window copy and reads window bytes past [whave].  [state->sane] is
      set to 1 by [inflateResetKeep] ([inflate.c:120]) and only
      [inflateUndermine] ever clears it, which libpng never calls, so that
      fall-through is dead; it is transcribed anyway because its absence
      would be an unstated assumption.
    - The direct-from-output copy at [inffast.c:238-244] is a DO-while, so
      it copies three bytes before testing [len > 2].  That is only safe
      because every length code carries [len >= 3]; see [if_wf].  The
      window-side copy at [:225-230] is a plain [while].
    - [len -= 3] and friends are [unsigned] subtractions; the model writes
      the [u32] truncation at each one.

    Structure, chosen so a machine-level walk can cut where the C cuts
    (c5-invariants.md §3.4):

    - [if_body]  — ONE trip of the [do { ... }] body, as a total function
      [IfCtx -> IfSt -> IfBody].  [IfCtx] is exactly the block of locals
      the C copies out of [strm]/[state] at [inffast.c:76-95] and never
      writes; [IfSt] is exactly the five it does write ([in], [out],
      [hold], [bits], and the output bytes).  So "one trip of the body"
      really is a function of the loop-carried state, which is what lets
      the loop invariant be indexed by trip count.
    - [if_guard] — the [while (in < last && out < end)] test, separately,
      because the compiled code tests it at the bottom.
    - [if_step] = body then guard; [if_iter k] = [k] fall-through trips;
      [if_loop] runs to the exit; [if_iter_loop] composes them.
    - [if_finish] — the return epilogue at [inffast.c:271-284] (the
      [bits >> 3] input give-back and the two [avail] recomputations).
    - [if_model] — entry ([:78-95]) + loop + epilogue, i.e. the whole
      function as the differential harness observes it.

    INTENDED TERMINATION MEASURE (not proved here; stated for the walk).
    Every body that returns [BodyOk] writes at least one output byte — a
    literal writes exactly 1 ([inffast.c:114]) and a match writes
    [len >= 3] — so [f_out] strictly increases on every continuing trip
    and the guard [out < end] bounds the trip count by [f_end - f_out].
    That is the fuel [if_model] passes.  [c5-invariants.md] §3.4's
    "abstract bit position strictly increases" is the dual statement on
    the input side and bounds the same loop by [8 * avail_in].

    WINDOW ARITHMETIC IS LINEAR, never [mod]: every wrap in [if_winphase]
    is written as the C writes it, [wsize + wnext - op] / [wnext - op] /
    [wsize - op], so the euclidean stage of the trusted spec's [lia] never
    has to fire on this family (c5-invariants.md §3.3).  [wsize] is a
    SYMBOLIC power of two throughout: libpng shrinks [windowBits] for
    small images, and the decode side asks for [inflateInit2(strm, 0)]
    ([pngrutil.c:415]), which takes the window size from the stream's own
    header byte — see [Spec/PngModel/Chunk.v]'s [window_bits_bands] and
    [emitted_window_is_ceil_pow2] for the reachable band (256 .. 32768).

    Validated against the delivered binary: see
    [a working folder] (R1 boundary records from
    [/harness/reference_binary] under qemu GDB-RSP, plus an injected
    stress set). *)

From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base.
(* THE ONE LINE TO REPOINT when the lane lead's [ZBits.v] carries the
   inflate-side bit reader too.  [ZBitsIn] implements exactly the frozen
   [BR] interface. *)
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import ZBitsIn.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

(** ** [strm->msg] as a code

    [strm->msg] is a [char *] into [.rodata]; the model gives each of the
    eighteen distinct literals zlib's inflate side can store a small code,
    with 0 for [Z_NULL].  A machine-level walk maps a code to the address
    of the corresponding string constant.  Shared with
    [Spec/PngModel/Inflate.v], which is why they live in this (lower)
    file. *)

Definition MSG_NONE            : Z := 0.
Definition MSG_HEADER_CHECK    : Z := 1.   (** "incorrect header check"      [inflate.c:625] *)
Definition MSG_UNKNOWN_METHOD  : Z := 2.   (** "unknown compression method"  [inflate.c:630], [:657] *)
Definition MSG_WINDOW_SIZE     : Z := 3.   (** "invalid window size"         [inflate.c:638] *)
Definition MSG_HEADER_FLAGS    : Z := 4.   (** "unknown header flags set"    [inflate.c:662] *)
Definition MSG_HEADER_CRC      : Z := 5.   (** "header crc mismatch"         [inflate.c:796] *)
Definition MSG_BLOCK_TYPE      : Z := 6.   (** "invalid block type"          [inflate.c:854] *)
Definition MSG_STORED_LEN      : Z := 7.   (** "invalid stored block lengths" [inflate.c:864] *)
Definition MSG_TOO_MANY        : Z := 8.   (** "too many length or distance symbols" [inflate.c:903] *)
Definition MSG_CODE_LENGTHS    : Z := 9.   (** "invalid code lengths set"    [inflate.c:924] *)
Definition MSG_BL_REPEAT       : Z := 10.  (** "invalid bit length repeat"   [inflate.c:947], [:981] *)
Definition MSG_NO_EOB          : Z := 11.  (** "invalid code -- missing end-of-block" [inflate.c:992] *)
Definition MSG_LIT_LEN_SET     : Z := 12.  (** "invalid literal/lengths set" [inflate.c:1006] *)
Definition MSG_DIST_SET        : Z := 13.  (** "invalid distances set"       [inflate.c:1015] *)
Definition MSG_LIT_LEN_CODE    : Z := 14.  (** "invalid literal/length code" [inflate.c:1069], [inffast.c:265] *)
Definition MSG_DIST_CODE       : Z := 15.  (** "invalid distance code"       [inflate.c:1103], [inffast.c:253] *)
Definition MSG_DIST_FAR        : Z := 16.  (** "invalid distance too far back" [inflate.c:1132], [inffast.c:168] *)
Definition MSG_DATA_CHECK      : Z := 17.  (** "incorrect data check"        [inflate.c:1203] *)
Definition MSG_LENGTH_CHECK    : Z := 18.  (** "incorrect length check"      [inflate.c:1215] *)

(** ** Static fuel bounds

    Both fuelled [Fixpoint]s below take their bound from the C, and both
    are given a NAME rather than a literal for a concrete reason:

    REDUCTION HAZARD (learned the hard way; the machine-level lane will hit
    it too).  [if_dolen] / [if_dodist] branch five ways per level, so a
    tactic that normalises the whole goal -- [cbn] with no delta list,
    [simpl], [compute] -- unfolds a LITERAL fuel through every level and
    every branch, which is exponential and does not terminate in practice
    (measured: the obvious [cbn [Nat.add if_loop]] proof of [if_iter_loop]
    below did not finish in 15 minutes).  With the fuel behind a constant,
    a [cbn] restricted by a delta list leaves the call stuck, and the
    unfolding lemmas [if_iter_S] / [if_loop_S] below -- each proved by
    [reflexivity], which is whnf-driven and therefore cheap -- are the
    intended way to step the loop in a proof.  [vm_compute],
    [native_compute] and [Extraction] are unaffected: they reduce
    call-by-value and never explore a dead branch, which is why the
    differential harness uses extraction. *)

(** Two levels is all [inflate_table] ever builds ([inftrees.h:33-47]: a
    root table of [2^root] entries plus sub-tables reached by one [goto]),
    so a [goto dolen] / [goto dodist] chain is at most two deep.  16 >
    MAXBITS is a safe over-approximation, and running out means the caller
    supplied a table [it_model] did not produce. *)
Definition tbl_fuel : nat := 16.

(** [inffast.c:225-230] copies three bytes per trip and [len <= 258]
    ([inftrees.c:60], [lbase[28] = 258]), so 87 > 258/3 trips suffice. *)
Definition copy_fuel : nat := 87.

(** ** The loop context: the locals [inflate_fast] copies out and never writes

    [inffast.c:77-95].  [f_last], [f_beg] and [f_end] are the three derived
    pointers, expressed as indices into [f_inbuf] / the output array. *)

Record IfCtx : Type := mkIfCtx {
  f_inbuf  : zarr;  (** the array [strm->next_in] points into, indexed absolutely *)
  f_last   : Z;     (** [last  = in + (avail_in - 5)]      [inffast.c:78] *)
  f_beg    : Z;     (** [beg   = out - (start - avail_out)] [inffast.c:80] *)
  f_end    : Z;     (** [end   = out + (avail_out - 257)]   [inffast.c:81] *)
  f_wsize  : Z;     (** [state->wsize] *)
  f_whave  : Z;     (** [state->whave] *)
  f_wnext  : Z;     (** [state->wnext] *)
  f_window : zarr;  (** [state->window]; read-only here, [updatewindow] writes it *)
  f_lcode  : ztbl;  (** [state->lencode],  indexed from its own base *)
  f_dcode  : ztbl;  (** [state->distcode], indexed from its own base *)
  f_lmask  : Z;     (** [(1U << state->lenbits)  - 1]      [inffast.c:93] *)
  f_dmask  : Z;     (** [(1U << state->distbits) - 1]      [inffast.c:94] *)
  f_sane   : Z      (** [state->sane]; always 1 in this build *)
}.

(** The loop-carried state: exactly what the body writes. *)
Record IfSt : Type := mkIfSt {
  f_in   : Z;     (** index of the next input byte  ([in]) *)
  f_out  : Z;     (** index of the next output byte ([out]) *)
  f_hold : Z;     (** [hold] *)
  f_bits : Z;     (** [bits] *)
  f_buf  : zarr   (** the output array, indexed absolutely *)
}.

(** ** The three primitive state moves *)

(** [inffast.c:106-109]: one unconditional byte load.  Unlike [PULLBYTE]
    there is NO [have == 0] test: [in < last] guarantees five spare bytes. *)
Definition if_load1 (c : IfCtx) (s : IfSt) : IfSt :=
  {| f_in   := f_in s + 1;
     f_out  := f_out s;
     f_hold := f_hold s + Z.shiftl (f_inbuf c (f_in s)) (f_bits s);
     f_bits := f_bits s + 8;
     f_buf  := f_buf s |}.

(** [inffast.c:105-110] / [:128-133]: [if (bits < 15) { load; load; }]. *)
Definition if_refill15 (c : IfCtx) (s : IfSt) : IfSt :=
  if Z.ltb (f_bits s) 15 then if_load1 c (if_load1 c s) else s.

(** [hold >>= n; bits -= n].  [bits] is [unsigned]. *)
Definition if_drop (n : Z) (s : IfSt) : IfSt :=
  {| f_in   := f_in s;
     f_out  := f_out s;
     f_hold := Z.shiftr (f_hold s) n;
     f_bits := u32 (f_bits s - n);
     f_buf  := f_buf s |}.

(** [hold & ((1U << n) - 1)]. *)
Definition if_low (n : Z) (s : IfSt) : Z :=
  Z.land (f_hold s) (Z.shiftl 1 n - 1).

(** [*out++ = v]. *)
Definition if_put (v : Z) (s : IfSt) : IfSt :=
  {| f_in   := f_in s;
     f_out  := f_out s + 1;
     f_hold := f_hold s;
     f_bits := f_bits s;
     f_buf  := zset (f_buf s) (f_out s) v |}.

(** ** Copies

    [from] alternates between [state->window] and the output buffer within
    a single match ([inffast.c:189-224]), so the model tags it.  Reads from
    the output buffer must see earlier writes of the SAME copy — that is
    how a match with [dist < len] performs its run-length expansion — so
    [if_copyn] re-reads [f_buf] from the current state at every byte. *)

Inductive IfSrc : Type :=
| SrcWin (i : Z)   (** [from] points into [state->window] *)
| SrcOut (i : Z).  (** [from] points into the output buffer *)

Definition if_read (c : IfCtx) (s : IfSt) (r : IfSrc) : Z :=
  match r with
  | SrcWin i => f_window c i
  | SrcOut i => f_buf s i
  end.

Definition if_bump (r : IfSrc) : IfSrc :=
  match r with SrcWin i => SrcWin (i + 1) | SrcOut i => SrcOut (i + 1) end.

(** [n] iterations of [*out++ = *from++]. *)
Fixpoint if_copyn (n : nat) (c : IfCtx) (s : IfSt) (r : IfSrc) {struct n}
  : IfSt * IfSrc :=
  match n with
  | O => (s, r)
  | S k => if_copyn k c (if_put (if_read c s r) s) (if_bump r)
  end.

(** [inffast.c:225-230]: [while (len > 2) { 3 copies; len -= 3; }].
    Fuel 87 > 258/3: [len] is a length-code base plus extra bits, at most
    258 ([inftrees.c:60] [lbase[28] = 258]).  Exhausting the fuel needs the
    [u32] underflow that [if_wf]'s [len >= 3] rules out. *)
Fixpoint if_copy3w (fuel : nat) (c : IfCtx) (s : IfSt) (r : IfSrc) (len : Z)
  {struct fuel} : option (IfSt * IfSrc * Z) :=
  match fuel with
  | O => None
  | S k =>
      if Z.ltb 2 len
      then let '(s1, r1) := if_copyn 3 c s r in
           if_copy3w k c s1 r1 (u32 (len - 3))
      else Some (s, r, len)
  end.

(** [inffast.c:231-235] / [:245-249]:
    [if (len) { *out++ = *from++; if (len > 1) *out++ = *from++; }]. *)
Definition if_copytail (c : IfCtx) (s : IfSt) (r : IfSrc) (len : Z) : IfSt :=
  if Z.eqb len 0 then s
  else let '(s1, r1) := if_copyn 1 c s r in
       if Z.ltb 1 len then fst (if_copyn 1 c s1 r1) else s1.

(** [inffast.c:237-249]: the direct-from-output branch.  A DO-while: three
    bytes are copied before [len > 2] is tested. *)
Definition if_copydirect (c : IfCtx) (s : IfSt) (r : IfSrc) (len : Z)
  : option IfSt :=
  let '(s1, r1) := if_copyn 3 c s r in
  match if_copy3w copy_fuel c s1 r1 (u32 (len - 3)) with
  | None => None
  | Some (s2, r2, l2) => Some (if_copytail c s2 r2 l2)
  end.

(** [inffast.c:188-224]: the three [from]-selection cases.

    Returns the state after whatever window-side copying the branch did,
    the [from] the shared tail loop continues at, and the remaining [len].
    Every [do { *out++ = *from++; } while (--op);] here runs with
    [op >= 1] — in the [wnext == 0] and [wnext >= op] branches because
    [op = dist - (out - beg) >= 1] (the branch was entered on
    [dist > out - beg]), and in the [wnext < op] branch because
    [op - wnext >= 1] there and the inner one uses [op = wnext >= 1]
    (that branch requires [wnext != 0]) — so it copies exactly [op] bytes
    and [if_copyn (Z.to_nat op)] is faithful. *)
Definition if_winphase (c : IfCtx) (s : IfSt) (dist op len : Z)
  : IfSt * IfSrc * Z :=
  if Z.eqb (f_wnext c) 0 then
    (* :190-197, "very common case" *)
    let r := SrcWin (f_wsize c - op) in
    if Z.ltb op len then
      let '(s1, _) := if_copyn (Z.to_nat op) c s r in
      (s1, SrcOut (f_out s1 - dist), u32 (len - op))
    else (s, r, len)
  else if Z.ltb (f_wnext c) op then
    (* :198-214, wrap around the window *)
    let r   := SrcWin (f_wsize c + f_wnext c - op) in
    let op1 := u32 (op - f_wnext c) in
    if Z.ltb op1 len then
      let len1 := u32 (len - op1) in
      let '(s1, _) := if_copyn (Z.to_nat op1) c s r in
      if Z.ltb (f_wnext c) len1 then
        let '(s2, _) := if_copyn (Z.to_nat (f_wnext c)) c s1 (SrcWin 0) in
        (s2, SrcOut (f_out s2 - dist), u32 (len1 - f_wnext c))
      else (s1, SrcWin 0, len1)
    else (s, r, len)
  else
    (* :215-223, contiguous in the window *)
    let r := SrcWin (f_wnext c - op) in
    if Z.ltb op len then
      let '(s1, _) := if_copyn (Z.to_nat op) c s r in
      (s1, SrcOut (f_out s1 - dist), u32 (len - op))
    else (s, r, len).

(** ** One trip of the body *)

Inductive IfBody : Type :=
| BodyOk   (s : IfSt)          (** reached the bottom of the body *)
| BodyEob  (s : IfSt)          (** [break] with [state->mode = TYPE]  [inffast.c:261] *)
| BodyBad  (s : IfSt) (m : Z)  (** [break] with [state->mode = BAD] *)
| BodyFuel.                    (** fuel exhausted; unreachable under [if_wf] *)

(** [inffast.c:136-250], entered at the [dodist:] label with the length
    already decoded.  The [goto dodist] at [:252] is a second-level
    distance-table lookup; two levels is all [inflate_table] ever builds
    ([inftrees.h:33-47]), so fuel 16 (> MAXBITS) can only run out on a
    table the caller did not get from [it_model]. *)
Fixpoint if_dodist (fuel : nat) (c : IfCtx) (len : Z) (s : IfSt) (h : Code)
  {struct fuel} : IfBody :=
  match fuel with
  | O => BodyFuel
  | S k =>
      (* :138-141 *)
      let s1 := if_drop (c_bits h) s in
      let op := c_op h in
      if negb (Z.eqb (Z.land op 16) 0) then
        (* :142-236 distance base *)
        let e  := Z.land op 15 in
        let s2 := if Z.ltb (f_bits s1) e
                  then let sa := if_load1 c s1 in
                       if Z.ltb (f_bits sa) e then if_load1 c sa else sa
                  else s1 in
        let dist := c_val h + if_low e s2 in
        (* :158-159 (the INFLATE_STRICT dmax test at :152-157 is compiled out) *)
        let s3 := if_drop e s2 in
        (* :161-162 *)
        let od := u32 (f_out s3 - f_beg c) in
        if Z.ltb od dist then
          (* :163-187 copy from the window *)
          let ow := u32 (dist - od) in
          if Z.ltb (f_whave c) ow && negb (Z.eqb (f_sane c) 0) then
            BodyBad s3 MSG_DIST_FAR
          else
            let '(s4, r4, len4) := if_winphase c s3 dist ow len in
            match if_copy3w copy_fuel c s4 r4 len4 with
            | None => BodyFuel
            | Some (s5, r5, l5) => BodyOk (if_copytail c s5 r5 l5)
            end
        else
          (* :237-249 copy direct from the output *)
          match if_copydirect c s3 (SrcOut (f_out s3 - dist)) len with
          | None => BodyFuel
          | Some s5 => BodyOk s5
          end
      else if Z.eqb (Z.land op 64) 0 then
        (* :251-253 second-level distance code *)
        if_dodist k c len s1 (f_dcode c (c_val h + if_low op s1))
      else
        (* :255-258 *)
        BodyBad s1 MSG_DIST_CODE
  end.

(** [inffast.c:112-268], entered at the [dolen:] label.  Same fuel
    argument as [if_dodist]. *)
Fixpoint if_dolen (fuel : nat) (c : IfCtx) (s : IfSt) (h : Code)
  {struct fuel} : IfBody :=
  match fuel with
  | O => BodyFuel
  | S k =>
      (* :113-116 *)
      let s1 := if_drop (c_bits h) s in
      let op := c_op h in
      if Z.eqb op 0 then
        (* :117-121 literal *)
        BodyOk (if_put (u8 (c_val h)) s1)
      else if negb (Z.eqb (Z.land op 16) 0) then
        (* :122-135 length base *)
        let e := Z.land op 15 in
        let '(len, s2) :=
          if Z.eqb e 0 then (c_val h, s1)
          else let sa := if Z.ltb (f_bits s1) e then if_load1 c s1 else s1 in
               (c_val h + if_low e sa, if_drop e sa) in
        (* :128-134 *)
        let s3 := if_refill15 c s2 in
        if_dodist tbl_fuel c len s3 (f_dcode c (Z.land (f_hold s3) (f_dmask c)))
      else if Z.eqb (Z.land op 64) 0 then
        (* :259-262 second-level length code *)
        if_dolen k c s1 (f_lcode c (c_val h + if_low op s1))
      else if negb (Z.eqb (Z.land op 32) 0) then
        (* :263-266 end of block *)
        BodyEob s1
      else
        (* :267-271 *)
        BodyBad s1 MSG_LIT_LEN_CODE
  end.

(** [inffast.c:103-112]: the top of the body. *)
Definition if_body (c : IfCtx) (s : IfSt) : IfBody :=
  let s0 := if_refill15 c s in
  if_dolen tbl_fuel c s0 (f_lcode c (Z.land (f_hold s0) (f_lmask c))).

(** [inffast.c:269]: [while (in < last && out < end)]. *)
Definition if_guard (c : IfCtx) (s : IfSt) : bool :=
  Z.ltb (f_in s) (f_last c) && Z.ltb (f_out s) (f_end c).

Inductive IfStep : Type :=
| IfCont (s : IfSt)          (** body fell through and the guard holds *)
| IfStop (s : IfSt)          (** guard failed: leave with [mode] unchanged (LEN) *)
| IfEob  (s : IfSt)          (** [break] with [mode := TYPE] *)
| IfBad  (s : IfSt) (m : Z)  (** [break] with [mode := BAD] *)
| IfFuel.

Definition if_step (c : IfCtx) (s : IfSt) : IfStep :=
  match if_body c s with
  | BodyOk s'    => if if_guard c s' then IfCont s' else IfStop s'
  | BodyEob s'   => IfEob s'
  | BodyBad s' m => IfBad s' m
  | BodyFuel     => IfFuel
  end.

(** The state after [k] fall-through trips — the term a machine-level loop
    invariant is indexed by. *)
Fixpoint if_iter (k : nat) (c : IfCtx) (s : IfSt) {struct k} : option IfSt :=
  match k with
  | O => Some s
  | S k' => match if_step c s with
            | IfCont s' => if_iter k' c s'
            | _ => None
            end
  end.

Fixpoint if_loop (n : nat) (c : IfCtx) (s : IfSt) {struct n} : option IfStep :=
  match n with
  | O => None
  | S k => match if_step c s with
           | IfCont s' => if_loop k c s'
           | r => Some r
           end
  end.

(** ** Entry and exit *)

(** How [state->mode] is left ([inffast.c:29-33]): LEN if the loop simply
    ran out of input or output space, TYPE on end-of-block, BAD on a data
    error. *)
Inductive IfExit : Type :=
| ExLen
| ExType
| ExBad (m : Z).

(** Everything the epilogue writes back to [strm]/[state]
    ([inffast.c:276-283]), plus the output array. *)
Record IfOut : Type := mkIfOut {
  y_in        : Z;     (** [strm->next_in],  as an index into [f_inbuf] *)
  y_out       : Z;     (** [strm->next_out], as an index into the output array *)
  y_avail_in  : Z;
  y_avail_out : Z;
  y_hold      : Z;
  y_bits      : Z;
  y_exit      : IfExit;
  y_buf       : zarr
}.

(** [inffast.c:271-283].
<<
    len = bits >> 3;  in -= len;  bits -= len << 3;  hold &= (1U << bits) - 1;
    strm->avail_in  = (unsigned)(in  < last ? 5   + (last - in) : 5   - (in  - last));
    strm->avail_out = (unsigned)(out < end  ? 257 + (end - out) : 257 - (out - end));
>> *)
Definition if_finish (c : IfCtx) (s : IfSt) (e : IfExit) : IfOut :=
  let l := Z.shiftr (f_bits s) 3 in
  let i := f_in s - l in
  let b := u32 (f_bits s - Z.shiftl l 3) in
  {| y_in        := i;
     y_out       := f_out s;
     y_avail_in  := u32 (if Z.ltb i (f_last c)
                         then 5 + (f_last c - i) else 5 - (i - f_last c));
     y_avail_out := u32 (if Z.ltb (f_out s) (f_end c)
                         then 257 + (f_end c - f_out s)
                         else 257 - (f_out s - f_end c));
     y_hold      := Z.land (f_hold s) (Z.shiftl 1 b - 1);
     y_bits      := b;
     y_exit      := e;
     y_buf       := f_buf s |}.

(** The arguments as the differential harness records them at the entry
    breakpoint: the two real parameters plus every [strm]/[state] field
    [inffast.c:78-95] reads. *)
Record IfArgs : Type := mkIfArgs {
  a_inbuf     : zarr;
  a_next_in   : Z;
  a_avail_in  : Z;
  a_buf       : zarr;
  a_next_out  : Z;
  a_avail_out : Z;
  a_start     : Z;   (** the second parameter *)
  a_wsize     : Z;
  a_whave     : Z;
  a_wnext     : Z;
  a_window    : zarr;
  a_lcode     : ztbl;
  a_dcode     : ztbl;
  a_lenbits   : Z;
  a_distbits  : Z;
  a_sane      : Z;
  a_hold      : Z;
  a_bits      : Z
}.

Definition if_ctx (a : IfArgs) : IfCtx :=
  {| f_inbuf  := a_inbuf a;
     f_last   := a_next_in a + (a_avail_in a - 5);
     f_beg    := a_next_out a - (a_start a - a_avail_out a);
     f_end    := a_next_out a + (a_avail_out a - 257);
     f_wsize  := a_wsize a;
     f_whave  := a_whave a;
     f_wnext  := a_wnext a;
     f_window := a_window a;
     f_lcode  := a_lcode a;
     f_dcode  := a_dcode a;
     f_lmask  := Z.shiftl 1 (a_lenbits a) - 1;
     f_dmask  := Z.shiftl 1 (a_distbits a) - 1;
     f_sane   := a_sane a |}.

Definition if_st0 (a : IfArgs) : IfSt :=
  {| f_in := a_next_in a; f_out := a_next_out a;
     f_hold := a_hold a; f_bits := a_bits a; f_buf := a_buf a |}.

(** [None] means a fuel bound was hit, which never happens under [if_wf];
    see the termination note in the header for the [f_end - f_out] bound. *)
Definition if_model (a : IfArgs) : option IfOut :=
  let c := if_ctx a in
  let s := if_st0 a in
  match if_loop (S (Z.to_nat (f_end c - f_out s))) c s with
  | Some (IfStop s')  => Some (if_finish c s' ExLen)
  | Some (IfEob s')   => Some (if_finish c s' ExType)
  | Some (IfBad s' m) => Some (if_finish c s' (ExBad m))
  | Some (IfCont _)   => None
  | Some IfFuel       => None
  | None              => None
  end.

(** [inffast.c:259-262]: a length entry takes the [goto dolen] exactly when
    it is neither a literal ([op == 0]) nor a length base ([op & 16]) nor
    an end-of-block / invalid marker ([op & 64]). *)
Definition lc_chains (op : Z) : bool :=
  negb (Z.eqb op 0) && Z.eqb (Z.land op 16) 0 && Z.eqb (Z.land op 64) 0.

(** [inffast.c:251-253]: the distance side has no literal case. *)
Definition dc_chains (op : Z) : bool :=
  Z.eqb (Z.land op 16) 0 && Z.eqb (Z.land op 64) 0.

(** RETIRED 2026-08-19 (chain repair; retention convention): the original
    table-wide spellings, kept as named targets for farm-ported consumers
    and for the refutation witnesses.  FALSE at reachable states — stale
    entries from a previous block's larger table survive [set_codes], and
    the installed LEN view reads the DIST table beyond [used1] (an earlier development run's
    counterexample classes (a)-(c)).  Consumed by NOTHING in this tree. *)
Definition lcode_two_level_all (c : IfCtx) : Prop :=
  forall v s,
    lc_chains (c_op (f_lcode c v)) = true ->
    lc_chains (c_op (f_lcode c (c_val (f_lcode c v)
                                + if_low (c_op (f_lcode c v)) s))) = false.

Definition dcode_two_level_all (c : IfCtx) : Prop :=
  forall v s,
    dc_chains (c_op (f_dcode c v)) = true ->
    dc_chains (c_op (f_dcode c (c_val (f_dcode c v)
                                + if_low (c_op (f_dcode c v)) s))) = false.

(** RELATIVIZED 2026-08-19 (chain repair, an earlier development run/an earlier development run): the
    quantifier carries the masked-image equation guard — the code's only
    first-level reads are [Z.land hold (f_lmask c)] ([:414]), and the
    table-wide form above is FALSE at reachable states.  Guard as an
    equation, not a range: the abstract-IfCtx lemma family has no
    mask/hold nonnegativity to discharge a range.

    MEASUREMENT-BIAS WARNING (the 560-entry census blind spot, second
    confirmed victim after [if_wf]'s [bits < 8]): every recorded entry
    state sat immediately after inflate_fast's own exit — fresh
    single-block tables, so table-wide claims held on every witness.
    Agreeing witnesses are a region, not a sample: stale-table states
    need multi-block streams with a SHRINKING second table, which the
    census never contained.  Do not re-widen these quantifiers on
    census evidence. *)
Definition lcode_two_level (c : IfCtx) : Prop :=
  forall v x s,
    v = Z.land x (f_lmask c) ->
    lc_chains (c_op (f_lcode c v)) = true ->
    lc_chains (c_op (f_lcode c (c_val (f_lcode c v)
                                + if_low (c_op (f_lcode c v)) s))) = false.

Definition dcode_two_level (c : IfCtx) : Prop :=
  forall v x s,
    v = Z.land x (f_dmask c) ->
    dc_chains (c_op (f_dcode c v)) = true ->
    dc_chains (c_op (f_dcode c (c_val (f_dcode c v)
                                + if_low (c_op (f_dcode c v)) s))) = false.

(** [inffast.c:105-141]: a length-base entry's [val] is the match length
    and [op & 15] its extra-bit count, both read out of [lbase]/[lext].
    [3 <= len] is what stops [if_copydirect]'s [u32 (len - 3)] from
    underflowing (which would exhaust [copy_fuel] and hand back
    [BodyFuel]), and [len <= 258] is what makes [copy_fuel = 87] enough.

    VERIFIED, not argued (2026-08-16): a [vm_compute] over all 31 entries
    of [Inftrees.lbase]/[Inftrees.lext] confirms that every index the C can
    select as a length base (i.e. with bit 4 of [op] set) satisfies both
    bounds, and that the two garbage slots [lext 29 = 203] and
    [lext 30 = 77] have bit 6 set -- so they are marked invalid and are
    never selected as a length base in the first place. *)
Definition lc_len_ok (h : Code) : Prop :=
  Z.land (c_op h) 16 <> 0 ->
  3 <= c_val h /\ c_val h + Z.shiftl 1 (Z.land (c_op h) 15) - 1 <= 258.

(** ** The length-table bound, RELATIVISED — ported repair, 2026-08-19
       (z-repro port of the libpng-w8 approved package; source of truth:
       distilled/zlib-port-repairs.md §2).

    THE UNRELATIVISED FORM IS FALSE AT DYNAMIC BLOCKS, proved on the
    libpng side: [lc_len_ok]'s 258 is a MAX_MATCH LENGTH bound applied
    over ALL table indices, but the distance table shares the array above
    [nx] and a distance [c_val] reaches 32768 — 16 of 32 entries violate
    at a measured dynamic block, up to 127x.  A unit mismatch, not an
    off-by-one.  Until this repair, every [if_wf]-conditioned theorem was
    VACUOUS at dynamic blocks.  The mechanism is exhibited IN THIS TREE at
    [Spec/PngModel/LcodeRelCheck.v] ([mech_old_form_refuted]), together
    with the escape ([mech_new_form_holds]).

    The two [lcode_index_range] clauses are read off the consuming proof
    ([InflateThy.if_dolen_two_ok], the two [Hlb] application sites):
    clause 1 is the caller's masked root index ([if_body]'s
    [Z.land (f_hold s0) (f_lmask c)]), clause 2 the second-level chain
    index (character-identical to [lcode_two_level]'s).

    PORT NOTE (deviation from the drafted package, flagged to the TL):
    clause 1 here carries BOTH bounds ([0 <= ... < n]); the drafted form
    carried only [< n].  The consuming site needs the lower half too —
    [lcode_len_bounded_upto] cannot be applied at the root index without
    it, and nothing ties [f_hold]/[f_lmask] to non-negative values for an
    arbitrary state.  At every witness the mask has the shape
    [Z.ones k], where both halves are one [Z.land_ones]/[Z.mod_pos_bound]
    step, so the strengthening costs witnesses nothing.

    TRAP, carried from the source doc: at [n = 2 ^ o_bits] the pointer
    clause is FALSE BY DESIGN — sub-table pointers point ABOVE the root
    block.  At a dynamic table the witness bound is [o_used], never the
    root size; inhabiting that needs the named residual
    [SubTblPointersBelowUsed] (stated as a port-draft in
    [LcodeRelCheck.v], unproved, a third clause of the fill-loop
    invariant). *)
Definition lcode_len_bounded_upto (c : IfCtx) (n : Z) : Prop :=
  forall v, 0 <= v < n -> lc_len_ok (f_lcode c v).

Definition lcode_index_range (n : Z) (c : IfCtx) : Prop :=
  (forall s, 0 <= Z.land (f_hold s) (f_lmask c) < n)
  /\ (forall v s, 0 <= v < n ->
        lc_chains (c_op (f_lcode c v)) = true ->
        0 <= c_val (f_lcode c v) + if_low (c_op (f_lcode c v)) s < n).

(** Keeps the OLD NAME bundled, so [if_wf] / [if_ctx_wf] / consumers need
    no textual edit and [n] stays hidden. *)
Definition lcode_len_bounded (c : IfCtx) : Prop :=
  exists n, lcode_len_bounded_upto c n /\ lcode_index_range n c.

(** RETENTION of the refuted form under a name, so the refutation stays
    compilable (fleet-standard clause; the refuting exhibit is
    [LcodeRelCheck.mech_old_form_refuted]). *)
Definition lcode_len_bounded_all (c : IfCtx) : Prop := forall v, lc_len_ok (f_lcode c v).

(** ** Well-formedness of a call

    The entry assumptions [inffast.c:23-28] states, plus the facts that
    keep the model's total functions equal to the C's loops.  [inflate]
    establishes all of them before the call at [inflate.c:1027-1030].

    HISTORY (2026-08-16).  An earlier version of this docstring claimed
    the table-provenance fact -- "length/distance tables that came from
    [inflate_table], so the [goto dolen]/[goto dodist] chains are at most
    two deep" -- while the conjuncts below said nothing about
    [a_lcode]/[a_dcode].  A consumer who discharged [if_wf] had therefore
    NOT established the fact the comment said they had.  That gap is now
    closed by the last two conjuncts; the predicate states what the
    docstring claims.

    Three families were added at the same time, all of them standing zlib
    invariants that were simply missing:

    - [0 <= a_hold < 2^a_bits] -- [hold] carries exactly [bits] valid bits
      and nothing above them ([DROPBITS] only ever shifts right), so at
      [a_bits = 0] the accumulator is empty.  Without it, a step reasoning
      about what a table index can be has to re-derive the bound.
    - [a_whave <= a_wsize] and [a_wnext <= a_wsize] -- the window-copy
      path indexes [window] from [wnext]; unconstrained, nothing here
      stopped a read past the window.
    - [lcode_two_level] / [dcode_two_level] -- the chain-depth fact above.
    - [lcode_len_bounded] -- added 2026-08-16 by the LT (fuel-sufficiency)
      lane, which found the SAME defect a second time in this file: the
      header at [:34] and [:250] both cite "[if_wf]'s [len >= 3]" and no
      conjunct said it.  Without [3 <= len] the copy underflows and
      exhausts [copy_fuel]; without [len <= 258] the fuel 87 is not
      enough.  [if_model] provably never returns [None] once this is
      assumed ([InflateThy.if_model_total]).

    These are PRECONDITIONS, so making them too strong would be
    unprovable at establish time rather than merely useless.  They were
    therefore MEASURED, not assumed: all three hold on 560 recorded
    [inflate_fast] entry states from the delivered binary, spanning every
    [in_bits] in [0..7] and both observed [in_wsize] values (0, i.e. the
    window not yet allocated, and 32768), with zero violations.  Nothing
    in the tree established [if_wf] when they were added, so the
    strengthening cost no existing proof. *)
Definition if_wf (a : IfArgs) : Prop :=
  6 <= a_avail_in a
  /\ 258 <= a_avail_out a
  /\ a_avail_out a <= a_start a
  /\ 0 <= a_bits a < 8
  /\ 0 <= a_hold a < 2 ^ a_bits a
  /\ 1 <= a_lenbits a <= 15
  /\ 1 <= a_distbits a <= 15
  /\ a_sane a = 1
  /\ 0 <= a_whave a <= a_wsize a
  /\ 0 <= a_wnext a <= a_wsize a
  /\ (forall i, 0 <= a_inbuf a i < 256)
  /\ (forall i, 0 <= a_window a i < 256)
  /\ lcode_two_level (if_ctx a)
  /\ dcode_two_level (if_ctx a)
  /\ lcode_len_bounded (if_ctx a).

(** ** Elementary facts

    Small and cheap, and each one is used by the walk.  The substantial
    obligations (termination, and "the table decode agrees with the
    canonical code") belong to [Spec/PngModel/InflateThy.v] and to the
    machine-level lane. *)

(** [if_copyn] never touches the input side or the bit accumulator, and it
    advances [out] by exactly [n]. *)
Lemma if_copyn_out :
  forall n c s r, f_out (fst (if_copyn n c s r)) = f_out s + Z.of_nat n.
Proof.
  induction n as [|n IH]; intros c s r; cbn [if_copyn].
  - cbn. lia.
  - rewrite IH. cbn [if_put f_out]. lia.
Qed.

Lemma if_copyn_in :
  forall n c s r, f_in (fst (if_copyn n c s r)) = f_in s.
Proof.
  induction n as [|n IH]; intros c s r; cbn [if_copyn]; [reflexivity|].
  now rewrite IH.
Qed.

Lemma if_copyn_bits :
  forall n c s r, f_bits (fst (if_copyn n c s r)) = f_bits s
               /\ f_hold (fst (if_copyn n c s r)) = f_hold s.
Proof.
  induction n as [|n IH]; intros c s r; cbn [if_copyn]; [now split|].
  now destruct (IH c (if_put (if_read c s r) s) (if_bump r)) as [H1 H2].
Qed.

(** [if_copyn] writes only at indices [f_out s ..]: everything strictly
    below the write cursor is untouched.  The fact that lets a walk keep
    the "output written so far" representation predicate across a copy. *)
Lemma if_copyn_below :
  forall n c s r j, j < f_out s -> f_buf (fst (if_copyn n c s r)) j = f_buf s j.
Proof.
  induction n as [|n IH]; intros c s r j Hj; cbn [if_copyn]; [reflexivity|].
  rewrite IH by (cbn [if_put f_out]; lia).
  cbn [if_put f_buf]. apply zset_other. lia.
Qed.

(** A single trip of the unrolled window-tail loop, as the walk sees it. *)
Lemma if_copy3w_unfold :
  forall fuel c s r len,
    2 < len ->
    if_copy3w (S fuel) c s r len
    = let '(s1, r1) := if_copyn 3 c s r in
      if_copy3w fuel c s1 r1 (u32 (len - 3)).
Proof.
  intros fuel c s r len H. cbn [if_copy3w].
  now apply Z.ltb_lt in H as ->.
Qed.

Lemma if_copy3w_done :
  forall fuel c s r len,
    len <= 2 -> if_copy3w (S fuel) c s r len = Some (s, r, len).
Proof.
  intros fuel c s r len H. cbn [if_copy3w].
  destruct (Z.ltb 2 len) eqn:E; [apply Z.ltb_lt in E; lia|reflexivity].
Qed.

(** The three unfolding lemmas that every proof in this file, and the
    machine-level walk, step the loop with.  Each is [reflexivity], i.e.
    one whnf unfolding of a fixpoint whose guard argument is already a
    constructor -- cheap, and immune to the reduction hazard noted above. *)

Lemma if_iter_O : forall c s, if_iter 0 c s = Some s.
Proof. reflexivity. Qed.

Lemma if_iter_S :
  forall k c s,
    if_iter (S k) c s
    = match if_step c s with IfCont s' => if_iter k c s' | _ => None end.
Proof. reflexivity. Qed.

Lemma if_loop_S :
  forall k c s,
    if_loop (S k) c s
    = match if_step c s with IfCont s' => if_loop k c s' | r => Some r end.
Proof. reflexivity. Qed.

(** [if_iter] composes with [if_loop]: running [k] trips and then the rest
    is running the whole loop.  The bridge a walk uses to hand its
    trip-indexed loop invariant to the exit lemma (the [inflate_table]
    lane's [it_iter_loop], same shape). *)
Lemma if_iter_loop :
  forall k n c s s',
    if_iter k c s = Some s' -> if_loop (k + n) c s = if_loop n c s'.
Proof.
  induction k as [|k IH]; intros n c s s' H.
  - rewrite if_iter_O in H. inversion H; subst. reflexivity.
  - rewrite if_iter_S in H.
    replace (S k + n)%nat with (S (k + n)) by reflexivity.
    rewrite if_loop_S.
    destruct (if_step c s); try discriminate H.
    now apply IH.
Qed.

(** The guard is exactly the conjunction the C tests, so a walk can split
    on the two comparisons independently. *)
Lemma if_guard_true :
  forall c s, if_guard c s = true <-> f_in s < f_last c /\ f_out s < f_end c.
Proof.
  intros c s; unfold if_guard; split.
  - intros H. apply andb_prop in H as [H1 H2].
    now apply Z.ltb_lt in H1, H2.
  - intros [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
    now rewrite H1, H2.
Qed.

(** ** Fuel monotonicity, fuel irrelevance, and the loop measure

    Three fuels appear in this file ([if_loop]'s, [tbl_fuel], [copy_fuel])
    and every [None] / [BodyFuel] / [IfFuel] the model can produce is one
    of them running out.  The facts below are what let a downstream proof
    stop carrying the fuel around.

    REDUCTION DISCIPLINE, and it is not optional here.  Every [cbn] below
    is delta-restricted AND is applied only where the fuel is [S k] for a
    VARIABLE [k], so it unfolds exactly one level.  The moment a literal
    fuel is in scope the header's warning bites: [cbn [if_dolen]] on
    [if_dolen 2] unfolds both levels through all five branches, and the
    resulting term is expensive to convert against.  That is why
    [if_dolen_depth2] goes through [if_dolen_chain_step] (a one-level
    rewrite) instead of normalising [if_dolen 2] — the first draft of that
    proof did the obvious thing and did not finish in 180 s.

    FUEL MONOTONICITY for the outer loop. *)
Lemma if_loop_fuel_mono :
  forall n n' c s r,
    (n <= n')%nat -> if_loop n c s = Some r -> if_loop n' c s = Some r.
Proof.
  induction n as [|n IH]; intros n' c s r Hle H.
  - cbn [if_loop] in H. discriminate H.
  - destruct n' as [|n']; [lia|].
    rewrite if_loop_S. rewrite if_loop_S in H.
    destruct (if_step c s) eqn:E.
    + apply IH; [lia | exact H].
    + exact H.
    + exact H.
    + exact H.
    + exact H.
Qed.

(** FUEL IRRELEVANCE for the two table-walk fixpoints.  These do not
    return an [option]: [BodyFuel] is the sentinel, and it is also what an
    exhausted [if_copy3w] / [if_copydirect] produces, so "the answer was
    not [BodyFuel]" is exactly "no fuel anywhere under this call ran
    out". *)
Lemma if_dodist_fuel_irrel :
  forall f f' c len s h,
    (f <= f')%nat -> if_dodist f c len s h <> BodyFuel ->
    if_dodist f' c len s h = if_dodist f c len s h.
Proof.
  induction f as [|f IH]; intros f' c len s h Hle Hne;
    [cbn [if_dodist] in Hne; congruence|].
  destruct f' as [|f']; [lia|].
  cbn [if_dodist] in Hne |- *.
  destruct (Z.eqb (Z.land (c_op h) 16) 0) eqn:E16; cbn [negb] in Hne |- *;
    [|reflexivity].
  destruct (Z.eqb (Z.land (c_op h) 64) 0) eqn:E64; [|reflexivity].
  apply IH; [lia | exact Hne].
Qed.

Lemma if_dolen_fuel_irrel :
  forall f f' c s h,
    (f <= f')%nat -> if_dolen f c s h <> BodyFuel ->
    if_dolen f' c s h = if_dolen f c s h.
Proof.
  induction f as [|f IH]; intros f' c s h Hle Hne;
    [cbn [if_dolen] in Hne; congruence|].
  destruct f' as [|f']; [lia|].
  cbn [if_dolen] in Hne |- *.
  destruct (Z.eqb (c_op h) 0) eqn:E0; [reflexivity|].
  destruct (Z.eqb (Z.land (c_op h) 16) 0) eqn:E16; cbn [negb] in Hne |- *;
    [|reflexivity].
  destruct (Z.eqb (Z.land (c_op h) 64) 0) eqn:E64; [|reflexivity].
  apply IH; [lia | exact Hne].
Qed.

(** *** The two-level table invariant, and why [tbl_fuel] may be read as 2

    [inflate_table] builds a root table of [2^root] entries plus sub-tables
    reached by ONE [goto] ([inftrees.h:33-47]), so a [goto dolen] /
    [goto dodist] chain is at most two deep.  [tbl_fuel = 16] is a safe
    over-approximation of that, but a lemma stated at 16 makes every
    caller do a sixteen-deep induction over a five-way case split where a
    two-way split suffices.  The predicates below say "an entry reached by
    a chain does not itself chain", and the corollaries turn 16 into 2. *)

(** A non-chaining entry is decided at the first level, so the fuel is
    invisible beyond one. *)
Lemma if_dolen_S_nochain :
  forall k k' c s h,
    lc_chains (c_op h) = false -> if_dolen (S k) c s h = if_dolen (S k') c s h.
Proof.
  intros k k' c s h H. unfold lc_chains in H. cbn [if_dolen].
  destruct (Z.eqb (c_op h) 0) eqn:E0,
           (Z.eqb (Z.land (c_op h) 16) 0) eqn:E16,
           (Z.eqb (Z.land (c_op h) 64) 0) eqn:E64;
    cbn [negb andb] in H |- *; try discriminate H; reflexivity.
Qed.

Lemma if_dodist_S_nochain :
  forall k k' c len s h,
    dc_chains (c_op h) = false ->
    if_dodist (S k) c len s h = if_dodist (S k') c len s h.
Proof.
  intros k k' c len s h H. unfold dc_chains in H. cbn [if_dodist].
  destruct (Z.eqb (Z.land (c_op h) 16) 0) eqn:E16,
           (Z.eqb (Z.land (c_op h) 64) 0) eqn:E64;
    cbn [negb andb] in H |- *; try discriminate H; reflexivity.
Qed.

(** …and a chaining entry consumes exactly one level.  Stated as a
    ONE-LEVEL rewrite so that no proof ever has to normalise a literal
    fuel. *)
Lemma if_dolen_chain_step :
  forall k c s h,
    lc_chains (c_op h) = true ->
    if_dolen (S k) c s h
    = if_dolen k c (if_drop (c_bits h) s)
        (f_lcode c (c_val h + if_low (c_op h) (if_drop (c_bits h) s))).
Proof.
  intros k c s h H. unfold lc_chains in H. cbn [if_dolen].
  destruct (Z.eqb (c_op h) 0) eqn:E0,
           (Z.eqb (Z.land (c_op h) 16) 0) eqn:E16,
           (Z.eqb (Z.land (c_op h) 64) 0) eqn:E64;
    cbn [negb andb] in H |- *; try discriminate H; reflexivity.
Qed.

Lemma if_dodist_chain_step :
  forall k c len s h,
    dc_chains (c_op h) = true ->
    if_dodist (S k) c len s h
    = if_dodist k c len (if_drop (c_bits h) s)
        (f_dcode c (c_val h + if_low (c_op h) (if_drop (c_bits h) s))).
Proof.
  intros k c len s h H. unfold dc_chains in H. cbn [if_dodist].
  destruct (Z.eqb (Z.land (c_op h) 16) 0) eqn:E16,
           (Z.eqb (Z.land (c_op h) 64) 0) eqn:E64;
    cbn [negb andb] in H |- *; try discriminate H; reflexivity.
Qed.

Lemma if_dolen_depth2 :
  forall k c v s,
    lcode_two_level c ->
    (lc_chains (c_op (f_lcode c v)) = true ->
       exists x, v = Z.land x (f_lmask c)) ->
    if_dolen (S (S k)) c s (f_lcode c v) = if_dolen 2 c s (f_lcode c v).
Proof.
  intros k c v s Hinv Hw.
  destruct (lc_chains (c_op (f_lcode c v))) eqn:Hch.
  - destruct (Hw eq_refl) as (x & Hx).
    pose proof (Hinv v x (if_drop (c_bits (f_lcode c v)) s) Hx Hch) as Hnext.
    rewrite (if_dolen_chain_step (S k) c s _ Hch).
    rewrite (if_dolen_chain_step 1 c s _ Hch).
    exact (if_dolen_S_nochain k 0 c _ _ Hnext).
  - exact (if_dolen_S_nochain (S k) 1 c s _ Hch).
Qed.

Lemma if_dodist_depth2 :
  forall k c len v s,
    dcode_two_level c ->
    (dc_chains (c_op (f_dcode c v)) = true ->
       exists x, v = Z.land x (f_dmask c)) ->
    if_dodist (S (S k)) c len s (f_dcode c v) = if_dodist 2 c len s (f_dcode c v).
Proof.
  intros k c len v s Hinv Hw.
  destruct (dc_chains (c_op (f_dcode c v))) eqn:Hch.
  - destruct (Hw eq_refl) as (x & Hx).
    pose proof (Hinv v x (if_drop (c_bits (f_dcode c v)) s) Hx Hch) as Hnext.
    rewrite (if_dodist_chain_step (S k) c len s _ Hch).
    rewrite (if_dodist_chain_step 1 c len s _ Hch).
    exact (if_dodist_S_nochain k 0 c len _ _ Hnext).
  - exact (if_dodist_S_nochain (S k) 1 c len s _ Hch).
Qed.

(** The headline corollaries: under the invariant [inflate_table]
    establishes, the sixteen levels ARE two. *)
Corollary if_dolen_tbl_fuel_is_2 :
  forall c v s,
    lcode_two_level c ->
    (lc_chains (c_op (f_lcode c v)) = true ->
       exists x, v = Z.land x (f_lmask c)) ->
    if_dolen tbl_fuel c s (f_lcode c v) = if_dolen 2 c s (f_lcode c v).
Proof.
  intros c v s H Hw. unfold tbl_fuel. apply (if_dolen_depth2 14 c v s H Hw).
Qed.

Corollary if_dodist_tbl_fuel_is_2 :
  forall c len v s,
    dcode_two_level c ->
    (dc_chains (c_op (f_dcode c v)) = true ->
       exists x, v = Z.land x (f_dmask c)) ->
    if_dodist tbl_fuel c len s (f_dcode c v)
    = if_dodist 2 c len s (f_dcode c v).
Proof.
  intros c len v s H Hw. unfold tbl_fuel.
  apply (if_dodist_depth2 14 c len v s H Hw).
Qed.

(** THE MEASURE for [if_loop].  [inffast.c:269]'s
    [while (in < last && out < end)] is [if_guard], so [f_end - f_out] is
    the quantity the loop runs down, and [if_model] picks
    [S (f_end - f_out)] at entry.

    NOT PROVED HERE, and deliberately not claimed: the other half,
    [if_body c s = BodyOk s' -> f_out s < f_out s'].  It needs the [f_out]
    behaviour of [if_copy3w], [if_copytail], [if_copydirect] and
    [if_winphase] threaded through both table fixpoints; that is
    machine-level-lane work, not a hygiene item.  What is fixed here is
    the name, the shape, and the one half that is free. *)
Definition if_measure (c : IfCtx) (s : IfSt) : Z := f_end c - f_out s.

(** THE [Qed] HAZARD, and the route around it — read this before adding
    any lemma that case-splits on [if_step] or [if_body].

    [unfold if_step in H] followed by a [destruct] on [if_body c s] makes
    the KERNEL, at [Qed], convert a type containing
    [match if_body c s with ...].  That does not terminate in practice
    (measured: > 150 s, on a goal whose tactic script runs in 0 s — the
    interactive proof looks finished and then [Qed] hangs, which is the
    nastiest shape this failure can take).  [remember]/[generalize] do NOT
    help; the fix is to never hand the kernel the composite term:

      - [if_step_unfold] is a [reflexivity]-proved rewrite (whnf-driven,
        instant), and
      - [if_step_body_cont] does the case analysis over an ABSTRACT
        [IfBody], so [if_body] never appears in its proof term.

    Same discipline as [if_iter_S] / [if_loop_S]: rewrite with a
    reflexivity lemma, never [unfold] into the kernel. *)
Lemma if_step_unfold :
  forall c s,
    if_step c s = match if_body c s with
                  | BodyOk s1 => if if_guard c s1 then IfCont s1 else IfStop s1
                  | BodyEob s1 => IfEob s1
                  | BodyBad s1 m => IfBad s1 m
                  | BodyFuel => IfFuel
                  end.
Proof. reflexivity. Qed.

Lemma if_step_body_cont :
  forall c (b : IfBody) s',
    match b with
    | BodyOk s1 => if if_guard c s1 then IfCont s1 else IfStop s1
    | BodyEob s1 => IfEob s1
    | BodyBad s1 m => IfBad s1 m
    | BodyFuel => IfFuel
    end = IfCont s' -> if_guard c s' = true.
Proof.
  intros c b s' H. destruct b as [s1|s1|s1 m|]; try discriminate H.
  destruct (if_guard c s1) eqn:Hg; [|discriminate H].
  injection H as H; subst s'. exact Hg.
Qed.

Lemma if_step_cont_guard :
  forall c s s', if_step c s = IfCont s' -> if_guard c s' = true.
Proof.
  intros c s s' H. rewrite if_step_unfold in H.
  exact (if_step_body_cont c (if_body c s) s' H).
Qed.

Lemma if_measure_pos_on_cont :
  forall c s s', if_step c s = IfCont s' -> 0 < if_measure c s'.
Proof.
  intros c s s' H. apply if_step_cont_guard in H.
  unfold if_guard in H. apply andb_prop in H as [_ H].
  apply Z.ltb_lt in H. unfold if_measure. lia.
Qed.

(** * Spec.PngModel.Checksum — transcription of zlib-1.3.1's [crc32_z] and
    [adler32_z].

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.  Depends only on
    [Spec.PngModel.Base] and Stdlib.

    Sources: [materials/zlib-1.3.1/crc32.c] and [.../adler32.c]
    (in-container [/harness/problem/materials/zlib-1.3.1/]).  This is a
    BUG-FOR-BUG transcription of the code path the DELIVERED riscv64 binary
    actually contains, not of RFC 1950/1952 or of the other paths crc32.c
    can be configured into.

    ** Which crc32.c path is compiled (established by disassembly, not by
       reading the macros)

    crc32.c selects among four shapes: byte-at-a-time, the ARM [crc32x]
    intrinsic path ([ARMCRC32]), and the braided word-at-a-time path in
    little- and big-endian flavours.  For the delivered binary:

    - [N = 5] ([crc32.c:57], unconditional — [Z_TESTN] is not defined);
    - [W = 4]: [crc32.c:80-84] picks [W 8] only for [__x86_64__] /
      [__aarch64__]; riscv64 takes the [#else] arm, [W 4], and
      [crc32.c:87-96] keeps it at 4 with [z_word_t = Z_U4].
      CONFIRMED: [crc_braid_table] in the binary is 0x1000 = 4*256*4 bytes
      (four rows, not eight), and the braid loop uses [lw] (32-bit) loads.
    - [ARMCRC32] is off (not aarch64), so [crc32.c:693-1029] is the body.
    - [DYNAMIC_CRC_TABLE] is off, so the tables are the static [crc32.h]
      copies; [get_crc_table] is a 3-instruction stub at 0x365dc.
    - The run-time endian test [crc32.c:723-726] is constant-folded by gcc:
      the delivered binary has NO [crc_big_table] / [crc_braid_big_table]
      symbol and no [crc_word_big] code.  Only the LITTLE-ENDIAN braid is
      transcribed below; the big-endian arm is unreachable object code that
      was not even emitted.

    Disassembly evidence (container, [riscv64-linux-gnu-objdump]):
<<
      crc32_z          .text 0x365e8 size 0x8dc
        364b8  beqz a1,36d78          <- if (buf == Z_NULL) return 0
        364bc  not a0,a0 / slli 32 / srli 32  <- crc = (~crc) & 0xffffffff
        364c4  li a5,22 ; bgeu a5,a2  <- if (len >= 23) braid   (23 = N*W+W-1)
        364ec  andi a5,a1,3           <- (buf & (W-1)), W = 4
        3655c  lw t4,0(a1) ...        <- 32-bit words
        36580  addi s2,s2,768         <- crc_braid_table[3][..]  (768 = 3*256)
      crc_table        .rodata 0x580b8 size 0x400   (256 x 4)
      crc_braid_table  .rodata 0x58538 size 0x1000  (4 x 256 x 4)
      x2n_table        .rodata 0x584b8 size 0x80    (32 x 4)
>>

    ** Tables

    The tables are NOT typed in as literals.  They are defined here by the
    same recursive polynomial computation [make_crc_table] /
    [braid] use ([crc32.c:310-333] and [:528-540]), so the definition is
    checkable against the binary's [.rodata] copy by evaluation, and so that
    the machine-level [TBL_rep] has a closed form to abstract to.  All 1024
    [crc_braid_table] entries and all 256 [crc_table] entries were compared
    byte-for-byte against the delivered binary's [.rodata]; see
    [a working folder].

    ** Alignment

    [crc32_z]'s pre-loop ([crc32.c:713-717]) consumes bytes until the
    POINTER is 4-aligned, so the execution path — though not the returned
    value — depends on [buf mod 4].  The model therefore takes the
    alignment as an explicit parameter, exactly as [Run] takes the stack
    top: it is a kernel/allocator-chosen quantity, not part of the input.

    Structure, chosen so a machine-level walk can cut where the C cuts:
    [crc_byte] (one trip of the byte loop), [crc_tail] (the 8-unrolled tail,
    [crc32.c:1000-1014]), [BrSt]/[br_step]/[br_iter] (the braid loop-carried
    state and ONE trip of [while (--blks)], so the invariant can be indexed
    by trip count), [br_final] (the last-block combine, [:826-844]).  Same
    for adler: [ad_do1]/[ad_do16] are the C's macros, [ad_inner] the
    347-trip [do {} while (--n)], [ad_nmax] the NMAX outer blocking. *)

From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** * Part 1 — CRC-32 ([crc32.c]) *)

(** [crc32.c:149] [#define POLY 0xedb88320]. *)
Definition POLY : Z := 3988292384.

(** [crc32.c:167] / [:316]: multiply the reflected register by [x] mod [p]:
<<
    b = b & 1 ? (b >> 1) ^ POLY : b >> 1
>> *)
Definition xtime (v : Z) : Z :=
  if Z.odd v then Z.lxor (Z.shiftr v 1) POLY else Z.shiftr v 1.

Fixpoint xtimes (n : nat) (v : Z) {struct n} : Z :=
  match n with O => v | S k => xtimes k (xtime v) end.

(** [crc32.c:313-318]: [crc_table[i]] is the CRC of the single byte [i]. *)
Definition crc_e (i : Z) : Z := xtimes 8 i.

(** The byte-wise table as a total array ([Base.zarr]); every index the C
    forms is [... & 0xff], so indices outside [0..255] are unreachable. *)
Definition crc_table : zarr := crc_e.

(** [crc32.c:155-168] [multmodp].  The [for(;;)] walks [m] from [1<<31]
    down, so 32 trips suffice; the C's early [break] at the lowest set bit
    of [a] is reproduced.  ([a = 0] makes the C loop forever — zlib never
    calls it with [a = 0], and [braid] special-cases [i = 0]; the fuelled
    version returns 0, which is what the special case stores anyway.) *)
Fixpoint multmodp_go (n : nat) (a b m p : Z) {struct n} : Z :=
  match n with
  | O => p
  | S k =>
      if Z.eqb (Z.land a m) 0
      then multmodp_go k a (xtime b) (Z.shiftr m 1) p
      else
        let p' := Z.lxor p b in
        if Z.eqb (Z.land a (m - 1)) 0
        then p'
        else multmodp_go k a (xtime b) (Z.shiftr m 1) p'
  end.

Definition multmodp (a b : Z) : Z := multmodp_go 32%nat a b 2147483648 0.

(** [crc32.c:326-329]: [x2n_table[0] = 1<<30] ([x^1]),
    [x2n_table[n] = multmodp(x2n_table[n-1], x2n_table[n-1])]. *)
Fixpoint x2n_nat (n : nat) {struct n} : Z :=
  match n with
  | O => 1073741824
  | S k => let p := x2n_nat k in multmodp p p
  end.

Definition x2n_table (k : Z) : Z := x2n_nat (Z.to_nat (Z.land k 31)).

(** [crc32.c:174-184] [x2nmodp]: [x^(n * 2^k) mod p]. *)
Fixpoint x2nmodp_go (f : nat) (n k p : Z) {struct f} : Z :=
  match f with
  | O => p
  | S j =>
      if Z.eqb n 0 then p
      else
        let p' := if Z.eqb (Z.land n 1) 1 then multmodp (x2n_table k) p else p in
        x2nmodp_go j (Z.shiftr n 1) (k + 1) p'
  end.

Definition x2nmodp (n k : Z) : Z := x2nmodp_go 64%nat n k 2147483648.

(** [crc32.c:57] [#define N 5]; [crc32.c:83] [W 4] on riscv64. *)
Definition NBRAID : Z := 5.
Definition WBYTES : Z := 4.

(** [crc32.c:528-540] [braid]: the four per-byte-position multipliers
    [p_k = x^((N*W + 3 - k) * 8)].  Kept as a closed list so that a
    lookup costs one [multmodp] rather than re-deriving [x2nmodp]. *)
Definition braid_ps : list Z :=
  map (fun k => x2nmodp (Z.shiftl (NBRAID * WBYTES + 3 - Z.of_nat k) 3) 0)
      (List.seq 0 4).

(** [crc32.c:533-537]: [ltl[k][0] = 0]; [ltl[k][i] = multmodp(i << 24, p_k)]. *)
Definition crc_braid (k i : Z) : Z :=
  if Z.eqb i 0 then 0 else multmodp (Z.shiftl i 24) (nth (Z.to_nat k) braid_ps 0).

(** ** The byte loop *)

(** [crc32.c:1002] etc.: [crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff]]. *)
Definition crc_byte (c b : Z) : Z :=
  Z.lxor (Z.shiftr c 8) (crc_table (Z.land (Z.lxor c b) 255)).

Definition crc_bytes (c : Z) (l : list Z) : Z := fold_left crc_byte l c.

(** [crc32.c:1000-1014]: [while (len >= 8) { 8 x DO1 }] then
    [while (len) { DO1 }].  Written with the 8-wide body explicit because
    the walk's loop invariant is stated at the 8-byte trip. *)
Fixpoint crc_tail (c : Z) (l : list Z) {struct l} : Z :=
  match l with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: r =>
      crc_tail (crc_byte (crc_byte (crc_byte (crc_byte
               (crc_byte (crc_byte (crc_byte (crc_byte c b0) b1) b2) b3)
                b4) b5) b6) b7) r
  | _ => crc_bytes c l
  end.

(** ** The braid *)

(** [crc32.c:672-678] [crc_word]: [for (k = 0; k < W; k++)
      data = (data >> 8) ^ crc_table[data & 0xff]]. *)
Definition crc_word_step (d : Z) : Z :=
  Z.lxor (Z.shiftr d 8) (crc_table (Z.land d 255)).

Fixpoint advz (n : nat) (d : Z) {struct n} : Z :=
  match n with O => d | S k => advz k (crc_word_step d) end.

Definition crc_word (d : Z) : Z := advz 4%nat d.   (* W = 4 *)

(** A little-endian 32-bit load, i.e. one [z_word_t] of the braid. *)
Definition le32 (b0 b1 b2 b3 : Z) : Z :=
  b0 + 256 * b1 + 65536 * b2 + 16777216 * b3.

Fixpoint le_words (l : list Z) {struct l} : list Z :=
  match l with
  | b0 :: b1 :: b2 :: b3 :: r => le32 b0 b1 b2 b3 :: le_words r
  | _ => []
  end.

(** [crc32.c:800-820]: the per-braid update
<<
      crc_j = crc_braid_table[0][word_j & 0xff];
      for (k = 1; k < W; k++)
          crc_j ^= crc_braid_table[k][(word_j >> (k << 3)) & 0xff];
>>
    with [word_j = crc_j ^ words[j]] ([:774-786]). *)
Definition br_one (c w : Z) : Z :=
  let x := Z.lxor c w in
  Z.lxor (Z.lxor (Z.lxor
      (crc_braid 0 (Z.land x 255))
      (crc_braid 1 (Z.land (Z.shiftr x 8) 255)))
      (crc_braid 2 (Z.land (Z.shiftr x 16) 255)))
      (crc_braid 3 (Z.land (Z.shiftr x 24) 255)).

(** Loop-carried state of [while (--blks)] ([crc32.c:772-822]): the five
    braid accumulators and the [words] cursor. *)
Record BrSt : Type := mkBrSt {
  b_c0 : Z;
  b_c1 : Z;
  b_c2 : Z;
  b_c3 : Z;
  b_c4 : Z;
  b_ws : list Z
}.

(** ONE trip of [while (--blks)]. *)
Definition br_step (s : BrSt) : BrSt :=
  match b_ws s with
  | w0 :: w1 :: w2 :: w3 :: w4 :: r =>
      {| b_c0 := br_one (b_c0 s) w0;
         b_c1 := br_one (b_c1 s) w1;
         b_c2 := br_one (b_c2 s) w2;
         b_c3 := br_one (b_c3 s) w3;
         b_c4 := br_one (b_c4 s) w4;
         b_ws := r |}
  | _ => s   (* unreachable: the cursor always holds a multiple of N words *)
  end.

(** The state after [k] trips — the term the machine-level braid invariant
    is indexed by. *)
Fixpoint br_iter (k : nat) (s : BrSt) {struct k} : BrSt :=
  match k with O => s | S k' => br_iter k' (br_step s) end.

(** [crc32.c:826-844]: the last block, combining the five braids. *)
Definition br_final (s : BrSt) : Z :=
  match b_ws s with
  | w0 :: w1 :: w2 :: w3 :: w4 :: _ =>
      let c := crc_word (Z.lxor (b_c0 s) w0) in
      let c := crc_word (Z.lxor (Z.lxor (b_c1 s) w1) c) in
      let c := crc_word (Z.lxor (Z.lxor (b_c2 s) w2) c) in
      let c := crc_word (Z.lxor (Z.lxor (b_c3 s) w3) c) in
      let c := crc_word (Z.lxor (Z.lxor (b_c4 s) w4) c) in
      c
  | _ => b_c0 s   (* unreachable *)
  end.

(** ** The model

    [align] is [(z_size_t)buf & (W-1)] on entry ([crc32.c:714]).  [bs] are
    the [len] bytes at [buf]. *)
Definition crc32_z_at (crc align : Z) (bs : list Z) : Z :=
  (* :709 [crc = (~crc) & 0xffffffff]; [crc] is a 64-bit [unsigned long]. *)
  let c0  := u32 (Z.lnot crc) in
  let len := Z.of_nat (length bs) in
  if Z.leb (NBRAID * WBYTES + WBYTES - 1) len then
    (* :713-717 advance to a z_word_t boundary *)
    let npre := (- align) mod WBYTES in
    let c1   := crc_bytes c0 (firstn (Z.to_nat npre) bs) in
    let rst  := skipn (Z.to_nat npre) bs in
    (* :720-722 [blks = len / (N*W); len -= blks * N*W] *)
    let blks := (len - npre) / (NBRAID * WBYTES) in
    let nmid := Z.to_nat (blks * NBRAID * WBYTES) in
    let ws   := le_words (firstn nmid rst) in
    let tl   := skipn nmid rst in
    (* :772-822 [while (--blks)], then :826-844 the combine *)
    let s    := br_iter (Z.to_nat (blks - 1)) {| b_c0 := c1; b_c1 := 0; b_c2 := 0;
                                                b_c3 := 0;  b_c4 := 0; b_ws := ws |} in
    (* :1000-1014 the tail, :1017 post-conditioning *)
    Z.lxor (crc_tail (br_final s) tl) 4294967295
  else
    Z.lxor (crc_tail c0 bs) 4294967295.

(** [crc32.c:695]: [if (buf == Z_NULL) return 0].  Note this is BEFORE the
    pre-conditioning, so [crc32_z(c, NULL, n) = 0] for every [c] and [n] —
    it does NOT return [c]. *)
Definition crc32_z (crc : Z) (isnull : bool) (align : Z) (bs : list Z) : Z :=
  if isnull then 0 else crc32_z_at crc align bs.

(** The byte-at-a-time reference: the same function computed without the
    braid.  [crc32_z_short] below relates the two on the path that does not
    braid; [Spec/PngModel/ChecksumThy.v]'s [crc32_braid_eq] relates them on
    the braid path too, for EVERY alignment, and derives the two facts the
    round-trip DAG consumes: [crc32_z_at_align] (the answer does not depend
    on [buf mod 4]) and [crc32_ref_app] ([crc32(crc32(c,a),b) =
    crc32(c,a++b)], zlib's incremental usage). *)
Definition crc32_ref (crc : Z) (bs : list Z) : Z :=
  Z.lxor (crc_bytes (u32 (Z.lnot crc)) bs) 4294967295.

(** ** Elementary facts *)

(** The 8-unrolled tail is the byte loop.  Stated with a length bound
    because the 8-deep pattern match needs strong induction. *)
Lemma crc_tail_bytes : forall n l c, (length l <= n)%nat -> crc_tail c l = crc_bytes c l.
Proof.
  induction n as [|n IH]; intros l c Hl.
  - destruct l; [reflexivity | cbn in Hl; lia].
  - destruct l as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 r]]]]]]]];
      try reflexivity.
    cbn [crc_tail]. rewrite IH by (cbn in Hl; lia).
    reflexivity.
Qed.

Corollary crc_tail_eq : forall l c, crc_tail c l = crc_bytes c l.
Proof. intros l c; apply (crc_tail_bytes (length l)); lia. Qed.

(** Short buffers (fewer than [N*W + W - 1 = 23] bytes) never braid, so the
    model is exactly the byte-at-a-time reference there.  Every PNG chunk
    header CRC ([png_write_chunk_header] feeds the 4 type bytes) takes this
    path. *)
Lemma crc32_z_short :
  forall crc align bs,
    (length bs < 23)%nat ->
    crc32_z_at crc align bs = crc32_ref crc bs.
Proof.
  intros crc align bs Hlen. unfold crc32_z_at, crc32_ref.
  replace (Z.leb (NBRAID * WBYTES + WBYTES - 1) (Z.of_nat (length bs))) with false.
  - now rewrite crc_tail_eq.
  - symmetry. apply Z.leb_gt. unfold NBRAID, WBYTES. lia.
Qed.

(** [crc_word] is four trips of the byte loop on zero bytes, which is how
    the last-block combine folds into the byte-wise picture. *)
Lemma crc_word_step_byte : forall c, crc_word_step c = crc_byte c 0.
Proof. intro c; unfold crc_word_step, crc_byte; now rewrite Z.lxor_0_r. Qed.

(** ** Convenience wrappers for the differential harness *)

Definition crc32_check (crc align : Z) (bs : list Z) : Z := crc32_z_at crc align bs.

(** * Part 2 — Adler-32 ([adler32.c])

    [NO_DIVIDE] is NOT defined (zlib's [configure] does not set it and the
    build passes no [-DNO_DIVIDE]), so [MOD]/[MOD28] are plain [%= BASE]
    ([adler32.c:55-58]).  Both [adler] and [sum2] are C [unsigned long],
    i.e. 64 bits on riscv64: the NMAX blocking keeps them below [2^32] so
    no truncation is observable, and none is written here. *)

(** [adler32.c:10-11]. *)
Definition ADLER_BASE : Z := 65521.
Definition NMAX : Z := 5552.

Record AdSt : Type := mkAdSt { a_adler : Z ; a_sum2 : Z }.

(** [adler32.c:14] [DO1(buf,i) {adler += (buf)[i]; sum2 += adler;}]. *)
Definition ad_do1 (s : AdSt) (b : Z) : AdSt :=
  let a := a_adler s + b in {| a_adler := a ; a_sum2 := a_sum2 s + a |}.

Definition ad_run (s : AdSt) (l : list Z) : AdSt := fold_left ad_do1 l s.

(** [adler32.c:15-19] [DO2/DO4/DO8/DO16]: sixteen [DO1]s in index order. *)
Fixpoint ad_don (n : nat) (s : AdSt) (l : list Z) {struct n} : AdSt * list Z :=
  match n, l with
  | O, _ => (s, l)
  | S _, [] => (s, l)
  | S k, b :: r => ad_don k (ad_do1 s b) r
  end.

Definition ad_do16 (s : AdSt) (l : list Z) : AdSt * list Z := ad_don 16%nat s l.

Definition ad_mod (s : AdSt) : AdSt :=
  {| a_adler := a_adler s mod ADLER_BASE ; a_sum2 := a_sum2 s mod ADLER_BASE |}.

(** [adler32.c:95-98]: [n = NMAX / 16; do { DO16(buf); buf += 16; } while (--n)].
    [NMAX / 16 = 347] exactly. *)
Fixpoint ad_inner (n : nat) (s : AdSt) (l : list Z) {struct n} : AdSt * list Z :=
  match n with
  | O => (s, l)
  | S k => let '(s', l') := ad_do16 s l in ad_inner k s' l'
  end.

(** [adler32.c:92-101]: [while (len >= NMAX) { len -= NMAX; <347 x DO16>;
    MOD(adler); MOD(sum2); }].  [f] is a fuel bound; callers pass
    [S (len / NMAX)], which is always enough. *)
Fixpoint ad_nmax (f : nat) (s : AdSt) (l : list Z) {struct f} : AdSt * list Z :=
  match f with
  | O => (s, l)
  | S k =>
      if Z.leb NMAX (Z.of_nat (length l))
      then let '(s', l') := ad_inner 347%nat s l in ad_nmax k (ad_mod s') l'
      else (s, l)
  end.

(** [adler32.c:105-109]: [while (len >= 16) { len -= 16; DO16(buf); buf += 16; }]. *)
Fixpoint ad_blk16 (f : nat) (s : AdSt) (l : list Z) {struct f} : AdSt * list Z :=
  match f with
  | O => (s, l)
  | S k =>
      if Z.leb 16 (Z.of_nat (length l))
      then let '(s', l') := ad_do16 s l in ad_blk16 k s' l'
      else (s, l)
  end.

(** [adler32.c:61-119].

    Two corners the differential harness pins and a transcription is likely
    to miss:

    - [adler32_z(x, NULL, 0) = 1], not [x] ([:80-81]).  The [buf == Z_NULL]
      test is DEFERRED past the [len == 1] fast path, so [isnull] with
      [len = 1] dereferences NULL — see [ad_wf].
    - the [len == 1] path ([:69-77]) normalises with a single conditional
      subtraction, not a [%]; for a well-formed [adler] argument (both
      halves [< BASE]) that is exact, but for [(adler >> 16) & 0xffff]
      in [BASE .. 65535] the returned [sum2] can come back [>= BASE].
      Transcribed as written. *)
Definition adler32_z (adler : Z) (isnull : bool) (bs : list Z) : Z :=
  (* :64-65 split into component sums *)
  let sum2_0 := Z.land (Z.shiftr adler 16) 65535 in
  let adl0   := Z.land adler 65535 in
  let len    := Z.of_nat (length bs) in
  if Z.eqb len 1 then
    (* :68-77 *)
    let a0 := adl0 + nth 0 bs 0 in
    let a  := if Z.leb ADLER_BASE a0 then a0 - ADLER_BASE else a0 in
    let s0 := sum2_0 + a in
    let s  := if Z.leb ADLER_BASE s0 then s0 - ADLER_BASE else s0 in
    Z.lor a (Z.shiftl s 16)
  else if isnull then 1   (* :80-81 *)
  else if Z.ltb len 16 then
    (* :84-92 *)
    let st := ad_run {| a_adler := adl0 ; a_sum2 := sum2_0 |} bs in
    let a  := if Z.leb ADLER_BASE (a_adler st) then a_adler st - ADLER_BASE
              else a_adler st in
    Z.lor a (Z.shiftl (a_sum2 st mod ADLER_BASE) 16)
  else
    (* :95-115 *)
    let '(st1, l1) := ad_nmax (S (Z.to_nat (len / NMAX)))
                              {| a_adler := adl0 ; a_sum2 := sum2_0 |} bs in
    let st2 :=
      if Nat.eqb (length l1) 0 then st1
      else let '(sa, l2) := ad_blk16 (S (Z.to_nat (len / 16))) st1 l1 in
           ad_mod (ad_run sa l2) in
    (* :118 *)
    Z.lor (a_adler st2) (Z.shiftl (a_sum2 st2) 16).

(** The caller obligations that keep the model total and faithful. *)
Definition ad_wf (isnull : bool) (bs : list Z) : Prop :=
  (forall b, In b bs -> 0 <= b < 256)
  /\ (isnull = true -> bs = []).

(** ** Facts *)

(** [ad_do16] on at least 16 bytes is 16 [DO1]s, i.e. [ad_run] on the
    16-byte prefix, and it consumes exactly those 16 bytes. *)
Lemma ad_don_split :
  forall n s l,
    (n <= length l)%nat ->
    ad_don n s l = (ad_run s (firstn n l), skipn n l).
Proof.
  induction n as [|n IH]; intros s l Hl; cbn [ad_don].
  - reflexivity.
  - destruct l as [|b r]; [cbn in Hl; lia|].
    cbn [firstn skipn]. rewrite IH by (cbn in Hl; lia).
    reflexivity.
Qed.

Lemma ad_do16_split :
  forall s l, (16 <= length l)%nat ->
    ad_do16 s l = (ad_run s (firstn 16 l), skipn 16 l).
Proof. intros; now apply ad_don_split. Qed.

(** [ad_run] is affine in the state, so reducing the state mod BASE before
    a block does not change the answer mod BASE.  This is the single fact
    that makes the NMAX blocking sound; it is what a walk hands to the
    model-level "same function on both ends" argument. *)
Lemma add_cong :
  forall n x y u v, x mod n = y mod n -> u mod n = v mod n ->
                    (x + u) mod n = (y + v) mod n.
Proof.
  intros n x y u v Hx Hu.
  rewrite (Zplus_mod x u), Hx, Hu. symmetry. apply Zplus_mod.
Qed.

Lemma ad_run_cong :
  forall l s s',
    a_adler s mod ADLER_BASE = a_adler s' mod ADLER_BASE ->
    a_sum2 s mod ADLER_BASE = a_sum2 s' mod ADLER_BASE ->
    a_adler (ad_run s l) mod ADLER_BASE = a_adler (ad_run s' l) mod ADLER_BASE
    /\ a_sum2 (ad_run s l) mod ADLER_BASE = a_sum2 (ad_run s' l) mod ADLER_BASE.
Proof.
  induction l as [|b r IH]; intros s s' Ha Hs; [split; assumption|].
  cbn [ad_run fold_left]. apply IH; cbn [ad_do1 a_adler a_sum2].
  - apply add_cong; [exact Ha | reflexivity].
  - apply add_cong; [exact Hs | apply add_cong; [exact Ha | reflexivity]].
Qed.

Lemma ad_mod_cong :
  forall s, a_adler (ad_mod s) mod ADLER_BASE = a_adler s mod ADLER_BASE
         /\ a_sum2 (ad_mod s) mod ADLER_BASE = a_sum2 s mod ADLER_BASE.
Proof.
  intro s; cbn [ad_mod a_adler a_sum2]; unfold ADLER_BASE.
  split; apply Z.mod_mod; lia.
Qed.

(** * Where the one open item is

    [adler32_z] vs "[ad_run] then one [mod]".  [ad_run_cong] is the
    inductive core; the remaining work is the case split over the four
    return paths and the range facts that turn the conditional subtractions
    into [mod].  It is not on the round-trip DAG's critical path — the
    decode-side adler check passes by function equality, the same
    [adler32_z] on both ends — so it is left for whoever needs a closed
    form.  The braid identity for [crc32_z], which IS on the critical path
    (the two ends CRC the same bytes at different addresses and in
    different splits), is discharged in [Spec/PngModel/ChecksumThy.v]. *)

(** * Spec.PngModel.Chunk — the PNG container layer and the zlib-parameter cluster.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.  Depends only on
    [Spec.PngModel.Base] and Stdlib.

    Sources (in-container [/harness/problem/materials/], host
    [data/libpng4--aug14/materials/]):

      - [libpng-1.6.43/pngwutil.c]   — signature, chunk framing, [png_image_size],
                                       [optimize_cmf], [png_deflate_claim],
                                       [png_write_IHDR], [png_compress_IDAT],
                                       [png_write_IEND], [png_write_finish_row]
      - [libpng-1.6.43/pngwrite.c]   — [png_create_write_struct_2] defaults,
                                       [png_write_info_before_PLTE],
                                       [png_write_info], [png_write_end]
      - [libpng-1.6.43/pngset.c]     — [png_set_IHDR]
      - [libpng-1.6.43/pngrutil.c]   — [png_read_sig], [png_read_chunk_header],
                                       [png_crc_read/finish/error],
                                       [png_check_chunk_name/length],
                                       [png_read_IDAT_data]
      - [libpng-1.6.43/png.h], [pngpriv.h], [pngstruct.h] — the macros
      - the GENERATED [pnglibconf.h] this build used (identical in all four
        build roots under [a working folder]; md5 …)
      - [zlib-1.3.1/deflate.c], [deflate.h] — [deflateInit2_], the zlib header
        byte pair, [configuration_table], the pending_buf/sym_buf geometry
      - [harness/src/png_harness.c] — [encode_raw], [assert_roundtrip],
                                      [roundtrip_encode_decode], [run_write]

    BUG-FOR-BUG.  This file reproduces what the SHIPPED code does, not what a
    clean-room PNG encoder would do.  The five deviations it exists to pin
    (campaign decision D8) are:

    1. [png_deflate_claim] shrinks [windowBits] below 15 for small images,
       using [png_image_size]'s ESTIMATE and zlib's [MIN_LOOKAHEAD] slop of
       262 ([pngwutil.c:369-380]).  This changes the zlib header byte, [wsize],
       and hence every match distance the compressor can emit.
    2. [optimize_cmf] then REWRITES the two header bytes already produced by
       deflate, with a loop that has NO 262 slop ([pngwutil.c:249-284]).  The
       emitted CMF therefore advertises a window that is normally ONE STEP
       SMALLER than the one deflate actually used, and can reach [cinfo = 0]
       (a 256-byte window) which [deflateInit2_] itself can never produce
       ([deflate.c:430]: [if (windowBits == 8) windowBits = 9]).  See
       [emitted_window_is_ceil_pow2] below for the closed form.
    3. The FCHECK fixup writes 31, not 0, when the remainder is already 0
       ([pngwutil.c:279-281]).
    4. IDAT is cut at exactly [PNG_ZBUF_SIZE = 8192] output bytes with no
       regard to deflate block boundaries, and a trailing 0-length IDAT is
       suppressed ([pngwutil.c:993-1010, 1041-1051]).
    5. [png_write_IHDR] silently rewrites an out-of-range interlace type to
       ADAM7, and an out-of-range compression/filter type to 0
       ([pngwutil.c:751-790]).

    Style follows [Spec/PngModel/Inftrees.v]: C line-number citations at every
    phase; [nat]-fuelled [Fixpoint]s whose fuel is a static bound read off the
    C loop; records for loop-carried / derived state; [_wf] predicates
    collecting caller obligations.  There are no [Admitted]s, [Axiom]s or
    [Parameter]s.

    WHAT IS DELIBERATELY *NOT* MODELLED HERE, and why:

    - The CRC-32 IMPLEMENTATION.  [crc32_bytes] below is the bit-at-a-time
      reflected CRC-32 that zlib's [crc32.c] computes; the shipped code uses
      the braided/table-driven loop.  Transcribing [crc32.c] (and proving it
      equal to [crc32_bytes]) is a separate lane's deliverable; the container
      layer only needs the FUNCTION, and the decode-side check passes by
      function equality (the same function is computed on both ends).
    - Deflate itself.  §8 records only the GEOMETRY [deflateInit2_] derives
      (window, hash, [pending_buf]/[sym_buf] overlap) and the level-6
      configuration row, because those constants decide when
      [_tr_flush_block] fires; the algorithm is the deflate lane's.
    - The read side's chunk DISPATCH ([png_handle_*], the
      [png_read_info]/[png_push_*] state machines, [png_read_update_info]'s
      transformation stack) and the read-side error policy
      ([png_benign_error], [PNG_CRC_QUIET_USE]).  The round-trip theorem
      quantifies over streams THIS ENCODER produced, and for those the
      reachable container shapes are exactly sig · IHDR · IDAT+ · IEND with
      every chunk length ≤ 8192 < [PNG_USER_CHUNK_MALLOC_MAX = 8000000], so
      [png_check_chunk_length]'s limit arithmetic, the ancillary-chunk
      branches, the [png_read_buffer] regrow path and the truncated-IDAT
      recovery in [png_read_IDAT_data] are all unreachable.  §10 models the
      container parse only and states that restriction as [read_wf].
    - Adam7 output geometry beyond [png_image_size]'s use of it.
      [encode_raw] always passes [PNG_INTERLACE_NONE]
      ([png_harness.c:256]); the interlaced arm of [png_image_size] is
      nonetheless transcribed because [run_write] ([png_harness.c:119]) can
      set ADAM7 and does reach it.

    DEAD-BRANCH FINDING (load-bearing for the proof's size, requested
    explicitly).  [encode_raw] ([png_harness.c:246-268]) calls exactly
    [png_set_IHDR], [png_write_info], [png_write_image], [png_write_end].
    [png_set_IHDR] ([pngset.c:246-283]) sets NO bit of [info_ptr->valid]
    (unlike [png_set_oFFs] &c., which all end in [info_ptr->valid |= …]), and
    [png_create_info_struct] zeroes the struct.  Therefore [info_ptr->valid]
    is 0 at [png_write_info] time and EVERY [valid &]-gated branch in
    [png_write_info_before_PLTE] ([pngwrite.c:130-180]: gAMA, iCCP, sRGB,
    sBIT, cHRM) and in [png_write_info] ([pngwrite.c:205-352]: PLTE, tRNS,
    bKGD, eXIf, hIST, oFFs, pCAL, sCAL, pHYs, tIME, sPLT) is dead, as is the
    [num_text] loop ([info_ptr->num_text = 0]) and both
    [write_unknown_chunks] calls ([info_ptr->unknown_chunks_num = 0]).  The
    [else if (color_type == PNG_COLOR_TYPE_PALETTE) png_error] arm
    ([pngwrite.c:214]) is likewise unreachable: the four colour types
    [assert_roundtrip] is ever called with ([png_harness.c:341-342, 396]) are
    GRAY(0), RGB(2), RGBA(6), GRAY_ALPHA(4).  Same for [png_write_end]
    ([pngwrite.c:361-465]): tIME, the text loop, eXIf and the unknown chunks
    are all gated the same way.  So the write side emits exactly

        signature · IHDR · IDAT+ · IEND

    and nothing else.  CONFIRMED on the delivered binary: over 653 inputs
    (the 252-file corpus plus a 401-file synthesised shape family), the
    2485 [png_write_complete_chunk] records carry exactly two tags, IHDR
    (1409) and IDAT (1076) — no ancillary chunk ever appears — and the 6745
    [png_write_data] records reassemble into 598 complete streams every one
    of which parses as signature · IHDR · IDAT+ · IEND with valid CRCs.
    (IEND does not appear as a [png_write_complete_chunk] record because
    [png_write_IEND] inlines that call; it is visible in the
    [png_write_data] byte stream.)

    VALIDATION.  [a working folder]: [harness/chunkextra.py] +
    [harness/chunk_run.py] add [optimize_cmf] and [png_write_data] to the
    lane's shared tracer; [models/build_chunk.sh] extracts THIS FILE to
    OCaml ([models/{ChunkModel,ExtractChunk}.v], [models/chunkq.ml]) and
    [harness/chunkcheck.py] diffs it against the R1 records in
    [logs/chunk/].  19102 checks over 1435 [png_deflate_claim], 1503
    [deflateInit2_], 2437 [png_image_size], 898 [optimize_cmf], 2485
    [png_write_complete_chunk] and 6745 [png_write_data] records:
    0 disagreements.  Ten deliberate model mutations
    ([chunkcheck.py --mutate]) are all caught.  Coverage in
    [reports/chunk_stats.json]. *)

From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel
  Require Import Base Checksum ChecksumThy Filter.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

(** ** 1. Build configuration

    Read off the GENERATED [pnglibconf.h] that produced the delivered
    binary, not off upstream defaults.  All four copies under
    [a working folder] (the cross, native, e2/nat and build roots) are
    byte-identical, which is what makes the native oracle a legitimate
    stand-in. *)

(** [pnglibconf.h:216]. *)
Definition PNG_ZBUF_SIZE : Z := 8192.
(** [pnglibconf.h:200]: [#define PNG_IDAT_READ_SIZE PNG_ZBUF_SIZE]. *)
Definition PNG_IDAT_READ_SIZE : Z := 8192.
(** [pnglibconf.h:201]. *)
Definition PNG_INFLATE_BUF_SIZE : Z := 1024.
(** [pnglibconf.h:218] — note this is [-1] ([Z_DEFAULT_COMPRESSION]), NOT 6.
    The 6 appears only inside [deflateInit2_]; see [zdefl_level]. *)
Definition PNG_Z_DEFAULT_COMPRESSION : Z := -1.
(** [pnglibconf.h:220] — [Z_FILTERED]. *)
Definition PNG_Z_DEFAULT_STRATEGY : Z := 1.
(** [pnglibconf.h:219] — [Z_DEFAULT_STRATEGY]. *)
Definition PNG_Z_DEFAULT_NOFILTER_STRATEGY : Z := 0.
(** [pnglibconf.h:213-215]. *)
Definition PNG_USER_CHUNK_MALLOC_MAX : Z := 8000000.
Definition PNG_USER_WIDTH_MAX : Z := 1000000.
Definition PNG_USER_HEIGHT_MAX : Z := 1000000.

(** Feature flags this transcription depends on, all present in the generated
    header: [PNG_WRITE_OPTIMIZE_CMF_SUPPORTED] (:147),
    [PNG_WRITE_FILTER_SUPPORTED] (:140),
    [PNG_WRITE_INTERLACING_SUPPORTED] (:143),
    [PNG_WRITE_CUSTOMIZE_COMPRESSION_SUPPORTED] (:137),
    [PNG_WRITE_CUSTOMIZE_ZTXT_COMPRESSION_SUPPORTED] (:138),
    [PNG_READ_INTERLACING_SUPPORTED] (:68).  [PNG_WRITE_16BIT_SUPPORTED] is
    on, which is why bit depth 16 is accepted in [ihdr_channels].
    [PNG_MNG_FEATURES_SUPPORTED] is ABSENT, which kills the
    intrapixel-differencing arm of [png_write_IHDR]'s filter-type check. *)

(** [png.h:662-674]. *)
Definition CT_GRAY : Z := 0.
Definition CT_RGB : Z := 2.
Definition CT_PALETTE : Z := 3.
Definition CT_GRAY_ALPHA : Z := 4.
Definition CT_RGB_ALPHA : Z := 6.

(** [png.h:677-687]. *)
Definition PNG_COMPRESSION_TYPE_BASE : Z := 0.
Definition PNG_FILTER_TYPE_BASE : Z := 0.
Definition PNG_INTERLACE_NONE : Z := 0.
Definition PNG_INTERLACE_ADAM7 : Z := 1.

(** [png.h:1463-1470].  [PNG_ALL_FILTERS = PNG_FAST_FILTERS | AVG | PAETH =
    0x38 | 0x40 | 0x80].

    INTEGRATION NOTE (WP-4 seam).  The full five-bit set lives in
    [Spec/PngModel/Filter.v] as [FB_NONE]/[FB_SUB]/[FB_UP]/[FB_AVG]/
    [FB_PAETH]/[FB_ALL] — that is the filter lane's file, and it is the one
    that has all five.  This file kept only the two it needs, under png.h's
    own names; they are now aliases, so there is one definition of each
    number in the tree. *)
Definition PNG_NO_FILTERS : Z := 0.
Definition PNG_FILTER_NONE : Z := FB_NONE.
Definition PNG_ALL_FILTERS : Z := FB_ALL.

(** [pngpriv.h:847-876]: [PNG_U32(b1,b2,b3,b4)]. *)
Definition png_IHDR : Z := 1229472850.   (* 0x49484452 *)
Definition png_IDAT : Z := 1229209940.   (* 0x49444154 *)
Definition png_IEND : Z := 1229278788.   (* 0x49454E44 *)

Definition PNG_UINT_31_MAX : Z := 2147483647.
Definition PNG_UINT_32_MAX : Z := 4294967295.

(** ** 2. PNG byte order

    [pngwutil.c:23-41] ([png_save_uint_32], [png_save_uint_16]) and
    [pngrutil.c:29-115] ([png_get_uint_32], [png_get_uint_16],
    [png_get_uint_31]).  The C writes [(i >> 24) & 0xff]; for the
    [png_uint_32] argument that is division, so the transcription uses
    division and a [u8] for the mask, which keeps the round-trip lemma
    arithmetic. *)

Definition be32 (v : Z) : list Z :=
  [ u8 (v / 16777216) ; u8 (v / 65536) ; u8 (v / 256) ; u8 v ].

Definition be16 (v : Z) : list Z := [ u8 (v / 256) ; u8 v ].

Definition be32_of (b0 b1 b2 b3 : Z) : Z :=
  b0 * 16777216 + b1 * 65536 + b2 * 256 + b3.

Definition be32_at (l : list Z) : Z :=
  be32_of (nth 0 l 0) (nth 1 l 0) (nth 2 l 0) (nth 3 l 0).

Definition be16_at (l : list Z) : Z :=
  (nth 0 l 0) * 256 + (nth 1 l 0).

Lemma be32_of_be32 : forall v, 0 <= v < 4294967296 -> be32_at (be32 v) = v.
Proof.
  intros v Hv. unfold be32, be32_at, be32_of, u8; cbn [nth].
  pose proof (Z.div_mod v 256 ltac:(lia)) as H1.
  pose proof (Z.div_mod (v / 256) 256 ltac:(lia)) as H2.
  pose proof (Z.div_mod (v / 65536) 256 ltac:(lia)) as H3.
  assert (E1 : v / 256 / 256 = v / 65536) by (rewrite Z.div_div by lia; reflexivity).
  assert (E2 : v / 65536 / 256 = v / 16777216) by (rewrite Z.div_div by lia; reflexivity).
  assert (Hlt : v / 16777216 < 256) by (apply Z.div_lt_upper_bound; lia).
  assert (Hge : 0 <= v / 16777216) by (apply Z.div_pos; lia).
  rewrite (Z.mod_small (v / 16777216) 256) by lia.
  rewrite E1 in H2. rewrite E2 in H3. lia.
Qed.

(** [pngrutil.c:96-107]: [png_get_uint_31] is [png_get_uint_32] plus a
    [png_error] when the value has the top bit set.  [None] is that error. *)
Definition get_uint_31 (l : list Z) : option Z :=
  let v := be32_at l in if Z.ltb PNG_UINT_31_MAX v then None else Some v.

(** ** 3. CRC-32

    [png.c]'s [png_calculate_crc] calls zlib's [crc32], and
    [png_reset_crc] seeds it with [crc32(0, NULL, 0) = 0]
    ([pngwutil.c:102-105] resets then runs the type over it).  This is the
    reflected CRC-32 of RFC 1952 / the PNG spec, written bit-at-a-time; the
    shipped [zlib-1.3.1/crc32.c] computes the same function with braided
    tables, and proving THAT equal to THIS is another lane's obligation. *)

(** 0xEDB88320, the reflected polynomial.  [Checksum.POLY] is the same
    number read off the same [crc32.c] line; they are proved equal below. *)
Definition CRC32_POLY : Z := 3988292384.

Fixpoint crc_bits (n : nat) (c : Z) : Z :=
  match n with
  | O => c
  | S k => crc_bits k (if Z.odd c then Z.lxor (Z.shiftr c 1) CRC32_POLY
                       else Z.shiftr c 1)
  end.

(** zlib's [DO1]: [c = crc_table[(c ^ *buf++) & 0xff] ^ (c >> 8)], unrolled
    to the eight bit steps that build [crc_table]. *)
Definition crc32_step (c b : Z) : Z := crc_bits 8%nat (Z.lxor c (u8 b)).

(** [crc32(init, buf, len)] computed bit-at-a-time: pre- and
    post-complement around the fold.  THIS IS NOT THE CANONICAL
    DEFINITION — see [crc32_bytes] below. *)
Definition crc32_bits_bytes (init : Z) (l : list Z) : Z :=
  u32 (Z.lxor (fold_left crc32_step l (Z.lxor (u32 init) 4294967295))
              4294967295).

(** *** The canonical CRC-32, and the bridge to the bit-at-a-time form

    INTEGRATION NOTE (WP-4 seam).  This file was written against its own
    bit-at-a-time CRC while [Spec/PngModel/Checksum.v] was transcribing
    zlib's actual braided table-driven [crc32_z] and its byte-at-a-time
    reference [crc32_ref].  Two definitions of one function is one too
    many, so [crc32_bytes] — the name the container layer and the whole
    read side use — is now DEFINED as [Checksum.crc32_ref].  That closes
    the chain the round-trip DAG needs in one hop:

      what the binary runs       [Checksum.crc32_z_at]
        = [ChecksumThy.crc32_braid_eq]
      byte-at-a-time reference   [Checksum.crc32_ref]
        = definitionally
      what the container uses    [crc32_bytes]

    The bit-at-a-time function is KEPT (as [crc32_bits_bytes]) and proved
    equal, because the [.rodata] table comparison and the emitted-CRC
    validation in [a working folder] were run against it. *)
Definition crc32_bytes (init : Z) (l : list Z) : Z := crc32_ref init l.

(** The eight-step bit loop IS [Checksum]'s shift register. *)
Lemma crc_bits_xtimes : forall n c, crc_bits n c = xtimes n c.
Proof.
  induction n as [|n IH]; intro c; [reflexivity|].
  cbn [crc_bits xtimes]. unfold xtime, CRC32_POLY, POLY. apply IH.
Qed.

(** Eight shifts of a value whose low eight bits are clear is a plain
    shift: the feedback never fires. *)
Lemma xtimes_low0 : forall n v, 0 <= v ->
  (forall i, 0 <= i < Z.of_nat n -> Z.testbit v i = false) ->
  xtimes n v = Z.shiftr v (Z.of_nat n).
Proof.
  induction n as [|n IH]; intros v Hv H.
  - cbn [xtimes]. now rewrite Z.shiftr_0_r.
  - cbn [xtimes]. unfold xtime.
    rewrite <- Z.bit0_odd, (H 0) by lia.
    rewrite IH.
    + rewrite Z.shiftr_shiftr by lia. f_equal. lia.
    + apply Z.shiftr_nonneg; exact Hv.
    + intros i Hi. rewrite Z.shiftr_spec by lia. apply H. lia.
Qed.

(** Split a non-negative integer into its low byte and the rest. *)
Lemma z_split8 : forall z, 0 <= z ->
  Z.lxor (Z.land z 255) (Z.shiftl (Z.shiftr z 8) 8) = z.
Proof.
  intros z Hz. apply Z.bits_inj'; intros i Hi.
  rewrite Z.lxor_spec, Z.land_spec.
  change 255 with (Z.ones 8). rewrite Z.testbit_ones by lia.
  destruct (Z.ltb_spec i 8) as [Hlt|Hge].
  - rewrite Z.shiftl_spec_low by lia.
    rewrite (proj2 (Z.leb_le 0 i)) by lia.
    now destruct (Z.testbit z i).
  - rewrite Z.shiftl_spec by lia. rewrite Z.shiftr_spec by lia.
    replace (i - 8 + 8) with i by lia.
    now destruct (0 <=? i), (Z.testbit z i).
Qed.

(** Hence the byte-wise shift register and [crc32.c]'s word step agree. *)
Lemma crc_e_word_step : forall z, 0 <= z -> crc_e z = crc_word_step z.
Proof.
  intros z Hz.
  assert (Hq : 0 <= Z.shiftr z 8) by (apply Z.shiftr_nonneg; exact Hz).
  assert (Hhi : crc_e (Z.shiftl (Z.shiftr z 8) 8) = Z.shiftr z 8).
  { unfold crc_e. rewrite (xtimes_low0 8).
    - rewrite Z.shiftr_shiftl_l by lia. now rewrite Z.shiftl_0_r.
    - apply Z.shiftl_nonneg; exact Hq.
    - intros i Hi. apply Z.shiftl_spec_low. cbn in Hi. lia. }
  transitivity (crc_e (Z.lxor (Z.land z 255) (Z.shiftl (Z.shiftr z 8) 8))).
  { now rewrite z_split8. }
  rewrite crc_e_lxor, Hhi. unfold crc_word_step, crc_table. apply Z.lxor_comm.
Qed.

Lemma crc32_step_byte : forall c b, 0 <= c -> 0 <= b < 256 ->
  crc32_step c b = crc_byte c b.
Proof.
  intros c b Hc Hb. unfold crc32_step. rewrite u8_id by lia.
  rewrite crc_bits_xtimes.
  change (xtimes 8 (Z.lxor c b)) with (crc_e (Z.lxor c b)).
  rewrite crc_e_word_step by (apply Z.lxor_nonneg; split; lia).
  symmetry. now apply crc_byte_step.
Qed.

Lemma crc32_fold : forall l c, bytes l -> w32 c ->
  fold_left crc32_step l c = crc_bytes c l.
Proof.
  induction l as [|b r IH]; intros c Hl Hc; [reflexivity|].
  cbn [fold_left]. unfold crc_bytes; cbn [fold_left]. fold crc_bytes.
  assert (Hb : 0 <= b < 256) by (apply Hl; now left).
  rewrite crc32_step_byte by (first [apply (w32_bound c Hc) | exact Hb]).
  apply IH; [intros x Hx; apply Hl; now right | now apply w32_crc_byte].
Qed.

(** The complement zlib writes as [~crc] and this file wrote as
    [crc ^ 0xffffffff]. *)
Lemma lnot_as_lxor : forall c, 0 <= c < 4294967296 ->
  Z.lxor (u32 c) 4294967295 = u32 (Z.lnot c).
Proof.
  intros c Hc.
  assert (Hhi : forall i, 32 <= i -> Z.testbit c i = false).
  { intros i Hi. replace i with ((i - 32) + 32) by lia.
    rewrite <- Z.shiftr_spec by lia.
    rewrite (w32_small c Hc). apply Z.bits_0. }
  rewrite u32_id by exact Hc.
  unfold u32. change 4294967296 with (2 ^ 32).
  rewrite <- Z.land_ones by lia.
  apply Z.bits_inj'; intros i Hi.
  rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
  change 4294967295 with (Z.ones 32). rewrite Z.testbit_ones by lia.
  destruct (Z.ltb_spec i 32) as [Hlt|Hge].
  - rewrite (proj2 (Z.leb_le 0 i)) by lia.
    now destruct (Z.testbit c i).
  - rewrite (Hhi i) by lia.
    now destruct (0 <=? i), (Z.testbit (Z.lnot c) i).
Qed.

(** THE BRIDGE.  The bit-at-a-time CRC this file used to define is the
    byte-at-a-time CRC [Checksum.v] defines, which [ChecksumThy.v] proves
    the delivered binary's braided loop computes. *)
Theorem crc32_bits_eq_ref : forall init l,
  0 <= init < 4294967296 -> bytes l -> crc32_bits_bytes init l = crc32_bytes init l.
Proof.
  intros init l Hi Hl. unfold crc32_bits_bytes, crc32_bytes, crc32_ref.
  rewrite lnot_as_lxor by exact Hi.
  rewrite crc32_fold by
    (first [exact Hl
           | apply w32_small; unfold u32; apply Z.mod_pos_bound; lia]).
  apply u32_id.
  pose proof (w32_bound _ (w32_lxor _ _
                (w32_crc_bytes l (u32 (Z.lnot init))
                   (w32_small _ (Z.mod_pos_bound (Z.lnot init) 4294967296
                                   ltac:(lia))))
                (w32_small 4294967295 ltac:(lia)))).
  lia.
Qed.

Lemma crc32_nil : forall init, 0 <= init < 4294967296 -> crc32_bytes init [] = init.
Proof.
  intros init H. unfold crc32_bytes, crc32_ref, crc_bytes; cbn [fold_left].
  rewrite <- (lnot_as_lxor init H).
  rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r.
  now apply u32_id.
Qed.

(** ** 4. Chunk framing

    [pngwutil.c:73-190].  [png_write_chunk_header] writes
    [length(4 BE) || type(4)], then [png_reset_crc] + [png_calculate_crc]
    over the FOUR TYPE BYTES ONLY ([pngwutil.c:102-105]);
    [png_write_chunk_data] adds the payload to the CRC
    ([pngwutil.c:137-142]); [png_write_chunk_end] appends the CRC
    ([pngwutil.c:157-161]).  So the CRC covers type ++ data and NOT the
    length field. *)

Definition ty_IHDR : list Z := [73; 72; 68; 82].
Definition ty_IDAT : list Z := [73; 68; 65; 84].
Definition ty_IEND : list Z := [73; 69; 78; 68].

Definition zlen (l : list Z) : Z := Z.of_nat (length l).

Definition chunk_crc (ty dat : list Z) : Z := crc32_bytes 0 (ty ++ dat).

Definition chunk_bytes (ty dat : list Z) : list Z :=
  be32 (zlen dat) ++ ty ++ dat ++ be32 (chunk_crc ty dat).

(** Pins the CRC transcription against a value everyone knows: the empty
    IEND chunk's CRC is 0xAE426082. *)
Lemma crc_IEND : chunk_crc ty_IEND [] = 2923585666.
Proof. vm_compute. reflexivity. Qed.

(** [pngwutil.c:51-66].  [png_ptr->sig_bytes] is 0 for a fresh write
    struct, so all eight bytes go out in one [png_write_data]. *)
Definition png_signature : list Z := [137; 80; 78; 71; 13; 10; 26; 10].

(** ** 5. [png_write_IHDR] — [pngwutil.c:671-833]

    The validation is a [png_error] (a [longjmp] out of [encode_raw], which
    then returns 0 and the round-trip is skipped), so it is [option]. *)

(** [pngwutil.c:681-750]: the colour-type × bit-depth table, with
    [PNG_WRITE_16BIT_SUPPORTED] on.  Returns [png_ptr->channels]. *)
Definition ihdr_channels (color_type bit_depth : Z) : option Z :=
  if Z.eqb color_type CT_GRAY then
    (if (Z.eqb bit_depth 1) || (Z.eqb bit_depth 2) || (Z.eqb bit_depth 4)
        || (Z.eqb bit_depth 8) || (Z.eqb bit_depth 16)
     then Some 1 else None)
  else if Z.eqb color_type CT_RGB then
    (if (Z.eqb bit_depth 8) || (Z.eqb bit_depth 16) then Some 3 else None)
  else if Z.eqb color_type CT_PALETTE then
    (if (Z.eqb bit_depth 1) || (Z.eqb bit_depth 2) || (Z.eqb bit_depth 4)
        || (Z.eqb bit_depth 8)
     then Some 1 else None)
  else if Z.eqb color_type CT_GRAY_ALPHA then
    (if (Z.eqb bit_depth 8) || (Z.eqb bit_depth 16) then Some 2 else None)
  else if Z.eqb color_type CT_RGB_ALPHA then
    (if (Z.eqb bit_depth 8) || (Z.eqb bit_depth 16) then Some 4 else None)
  else None.

(** [pngwutil.c:751-756]: an invalid compression type is WARNED about and
    replaced by 0, not rejected.  Same for the filter type
    ([pngwutil.c:766-781]) — with [PNG_MNG_FEATURES_SUPPORTED] absent the
    condition collapses to [filter_type != PNG_FILTER_TYPE_BASE]. *)
Definition ihdr_norm_compression (ct : Z) : Z := 0.
Definition ihdr_norm_filter (ft : Z) : Z := 0.

(** [pngwutil.c:783-790].  BUG-FOR-BUG: the fallback is ADAM7, not NONE. *)
Definition ihdr_norm_interlace (it : Z) : Z :=
  if (Z.eqb it PNG_INTERLACE_NONE) || (Z.eqb it PNG_INTERLACE_ADAM7)
  then it else PNG_INTERLACE_ADAM7.

(** [pngpriv.h:763-766]:
<<
    #define PNG_ROWBYTES(pixel_bits, width) \
        ((pixel_bits) >= 8 ? \
        ((size_t)(width) * (((size_t)(pixel_bits)) >> 3)) : \
        (( ((size_t)(width) * ((size_t)(pixel_bits))) + 7) >> 3) )
>> *)
Definition png_rowbytes (pixel_bits width : Z) : Z :=
  if Z.leb 8 pixel_bits then width * (pixel_bits / 8)
  else (width * pixel_bits + 7) / 8.

(** [pngwutil.c:817-827].  On entry [png_ptr->do_filter] is
    [PNG_NO_FILTERS] (the struct is zeroed by [png_create_png_struct] and
    [encode_raw] never calls [png_set_filter]), so this is the value it
    lands on.  It is the input to [png_deflate_claim]'s strategy choice.

    INTEGRATION NOTE (WP-4 seam).  [Spec/PngModel/Filter.v] transcribes
    the same [pngwutil.c:824-831] as [png_ihdr_do_filter]; that is the
    canonical copy and this is an alias.  [ihdr_do_filter_alias] below
    records that the two lanes really did read the C the same way. *)
Definition ihdr_do_filter (color_type bit_depth : Z) : Z :=
  png_ihdr_do_filter color_type bit_depth.

Lemma ihdr_do_filter_alias : forall ct bd,
  ihdr_do_filter ct bd
  = (if (Z.eqb ct CT_PALETTE) || (Z.ltb bd 8)
     then PNG_FILTER_NONE else PNG_ALL_FILTERS).
Proof. reflexivity. Qed.

(** The write-side [png_struct] fields [png_write_IHDR] establishes and the
    rest of the encoder reads ([pngwutil.c:793-815]). *)
Record WrHdr : Type := mkWrHdr {
  wh_width       : Z;
  wh_height      : Z;
  wh_bit_depth   : Z;
  wh_color_type  : Z;
  wh_interlaced  : Z;
  wh_channels    : Z;
  wh_pixel_depth : Z;
  wh_rowbytes    : Z;
  wh_do_filter   : Z
}.

Definition png_write_IHDR (width height bit_depth color_type
                           compression_type filter_type interlace_type : Z)
  : option (WrHdr * list Z) :=
  match ihdr_channels color_type bit_depth with
  | None => None
  | Some ch =>
      let it := ihdr_norm_interlace interlace_type in
      let ct := ihdr_norm_compression compression_type in
      let ft := ihdr_norm_filter filter_type in
      let pd := bit_depth * ch in
      let payload :=
        be32 width ++ be32 height
        ++ [ u8 bit_depth ; u8 color_type ; u8 ct ; u8 ft ; u8 it ] in
      Some ({| wh_width := width; wh_height := height;
               wh_bit_depth := bit_depth; wh_color_type := color_type;
               wh_interlaced := it; wh_channels := ch;
               wh_pixel_depth := pd;
               wh_rowbytes := png_rowbytes pd width;
               wh_do_filter := ihdr_do_filter color_type bit_depth |},
            chunk_bytes ty_IHDR payload)
  end.

Lemma ihdr_payload_is_13 :
  forall w h bd ct comp filt il s bytes,
    png_write_IHDR w h bd ct comp filt il = Some (s, bytes) ->
    length bytes = 25%nat.
Proof.
  intros w h bd ct comp filt il s bytes H.
  unfold png_write_IHDR in H.
  destruct (ihdr_channels ct bd) as [ch|]; [|discriminate].
  injection H as _ <-. reflexivity.
Qed.

(** [pngwutil.c:1072-1080]. *)
Definition png_write_IEND_bytes : list Z := chunk_bytes ty_IEND [].

(** ** 6. Adam7 pass geometry — [png.h:2439-2465] *)

Definition pass_row_shift (p : Z) : Z := if Z.ltb 2 p then (8 - p) / 2 else 3.
Definition pass_col_shift (p : Z) : Z := if Z.ltb 1 p then (7 - p) / 2 else 3.

Definition pass_start_row (p : Z) : Z :=
  Z.land (Z.shiftl (Z.land 1 (Z.lnot p)) (3 - p / 2)) 7.
Definition pass_start_col (p : Z) : Z :=
  Z.land (Z.shiftl (Z.land 1 p) (3 - (p + 1) / 2)) 7.

Definition pass_rows (height p : Z) : Z :=
  (height + (Z.shiftl 1 (pass_row_shift p) - 1) - pass_start_row p)
    / Z.shiftl 1 (pass_row_shift p).
Definition pass_cols (width p : Z) : Z :=
  (width + (Z.shiftl 1 (pass_col_shift p) - 1) - pass_start_col p)
    / Z.shiftl 1 (pass_col_shift p).

(** The classic Adam7 tables, pinned so a reader can check the macro
    transcription without evaluating shifts by hand. *)
Lemma adam7_tables :
  map pass_row_shift  [0;1;2;3;4;5;6] = [3;3;3;2;2;1;1] /\
  map pass_col_shift  [0;1;2;3;4;5;6] = [3;3;2;2;1;1;0] /\
  map pass_start_row  [0;1;2;3;4;5;6] = [0;0;4;0;2;0;1] /\
  map pass_start_col  [0;1;2;3;4;5;6] = [0;4;0;2;0;1;0].
Proof. repeat split; vm_compute; reflexivity. Qed.

(** ** 7. [png_image_size] — [pngwutil.c:203-239]

    "This is used below to find the size of an image to pass to
    png_deflate_claim, so it only needs to be accurate if the size is less
    than 16384 bytes."  It is nonetheless the EXACT input to the windowBits
    loop, so it is transcribed exactly, including the [0xffffffff] fallback
    and the interlaced arm (reachable through [run_write],
    [png_harness.c:119]). *)

(** [pngwutil.c:224-229], one trip per pass; fuel 7 is the C's [pass<=6]. *)
Fixpoint image_size_passes (n : nat) (p : Z) (w h pd acc : Z) : Z :=
  match n with
  | O => acc
  | S k =>
      let pw := pass_cols w p in
      let acc' := if Z.ltb 0 pw
                  then acc + (png_rowbytes pd pw + 1) * pass_rows h p
                  else acc in
      image_size_passes k (p + 1) w h pd acc'
  end.

(** Arguments are the [png_struct] fields the C reads: [rowbytes], [height],
    [width], [pixel_depth], [interlaced]. *)
Definition png_image_size (rowbytes height width pixel_depth interlaced : Z) : Z :=
  if (Z.ltb rowbytes 32768) && (Z.ltb height 32768) then
    (if negb (Z.eqb interlaced 0)
     then image_size_passes 7%nat 0 width height pixel_depth 0
     else (rowbytes + 1) * height)
  else 4294967295.

(** The form the encoder actually uses: [png_image_size] applied to the
    [WrHdr] that [png_write_IHDR] just built. *)
Definition wr_image_size (s : WrHdr) : Z :=
  png_image_size (wh_rowbytes s) (wh_height s) (wh_width s)
                 (wh_pixel_depth s) (wh_interlaced s).

(** ** 8. [png_deflate_claim] — [pngwutil.c:290-436]

    Only the [owner == png_IDAT] path is reachable in this driver (no text
    chunks are ever written; see the dead-branch finding in the header), and
    only with a freshly created write struct, so
    [PNG_FLAG_ZSTREAM_INITIALIZED] is clear and the call is always
    [deflateInit2], never [deflateReset] ([pngwutil.c:405-415]).  The
    [zowner != 0] preamble ([pngwutil.c:294-321]) is likewise unreachable:
    [png_compress_IDAT] claims once and releases at [Z_STREAM_END]. *)

(** [pngwutil.c:1929-1943]:
<<
      filters = png_ptr->do_filter;
      if (png_ptr->height == 1) filters &= 0xff & ~(UP|AVG|PAETH);   /* 0x1f */
      if (png_ptr->width  == 1) filters &= 0xff & ~(SUB|AVG|PAETH);  /* 0x2f */
      if (filters == 0) filters = PNG_FILTER_NONE;
      png_ptr->do_filter = filters;
>>
    BUG-FOR-BUG, and easy to miss: [png_write_start_row] runs on the FIRST
    [png_write_row], i.e. before the first [png_compress_IDAT] and therefore
    before [png_deflate_claim] reads [do_filter].  The strategy the IDAT
    stream is compressed with is decided by this NARROWED value, not by the
    [PNG_ALL_FILTERS] that [png_write_IHDR] installed.  For a 1x1 image both
    reductions fire, [do_filter] becomes [PNG_FILTER_NONE], and the whole
    stream is compressed with [Z_DEFAULT_STRATEGY] instead of [Z_FILTERED].
    Found by the differential harness (58 disagreements on the first run),
    not by reading the code.

    The [filters == 0] arm is dead for this driver: bit 0x08
    ([PNG_FILTER_NONE]) is in both masks, so it survives every narrowing of
    [PNG_ALL_FILTERS].

    INTEGRATION NOTE (WP-4 seam).  [Spec/PngModel/Filter.v]'s
    [png_start_row_filters] is the same transcription of the same
    [pngwutil.c:1929-1943]; it is canonical and this is an alias. *)
Definition start_row_do_filter (do_filter width height : Z) : Z :=
  png_start_row_filters do_filter width height.

Lemma start_row_do_filter_alias : forall df w h,
  start_row_do_filter df w h
  = (let f0 := if Z.eqb h 1 then Z.land df 31 else df in
     let f1 := if Z.eqb w 1 then Z.land f0 47 else f0 in
     if Z.eqb f1 0 then PNG_FILTER_NONE else f1).
Proof. reflexivity. Qed.

(** [pngwutil.c:334-344].  [PNG_FLAG_ZLIB_CUSTOM_STRATEGY] is only set by
    [png_set_compression_strategy], which the harness never calls, so the
    live arm is the [do_filter] test.  BUG-FOR-BUG: the test is
    [!= PNG_FILTER_NONE], and [PNG_FILTER_NONE] is 0x08, NOT 0 — a
    [do_filter] of [PNG_NO_FILTERS = 0] would take the FILTERED branch. *)
Definition idat_strategy (custom : bool) (zlib_strategy do_filter : Z) : Z :=
  if custom then zlib_strategy
  else if negb (Z.eqb do_filter PNG_FILTER_NONE)
       then PNG_Z_DEFAULT_STRATEGY
       else PNG_Z_DEFAULT_NOFILTER_STRATEGY.

(** [pngwutil.c:369-380]:
<<
      if (data_size <= 16384)
      {
         unsigned int half_window_size = 1U << (windowBits-1);
         while (data_size + 262 <= half_window_size)
         {
            half_window_size >>= 1;
            --windowBits;
         }
      }
>>
    The 262 is zlib's [MIN_LOOKAHEAD = MAX_MATCH + MIN_MATCH + 1]
    ([deflate.h:290]) — deflate needs that much window beyond the data,
    inflate does not.  Fuel 16 > [windowBits]: [half_window_size] halves
    every trip and the guard fails once it drops below 262, so with
    [data_size >= 0] the loop stops at [windowBits = 9] at the latest
    (262 > 256), which is why [deflateInit2_]'s
    [if (windowBits == 8) windowBits = 9] ([deflate.c:430]) is DEAD here. *)
Fixpoint dc_shrink (n : nat) (data_size half wb : Z) : Z * Z :=
  match n with
  | O => (half, wb)
  | S k => if Z.leb (data_size + 262) half
           then dc_shrink k data_size (Z.shiftr half 1) (wb - 1)
           else (half, wb)
  end.

Definition deflate_claim_window_bits (windowBits data_size : Z) : Z :=
  if Z.leb data_size 16384
  then snd (dc_shrink 16%nat data_size (Z.shiftl 1 (windowBits - 1)) windowBits)
  else windowBits.

(** The tuple actually handed to [deflateInit2] for IDAT.  The defaults come
    from [png_create_write_struct_2] ([pngwrite.c:538-548]): [zbuffer_size =
    PNG_ZBUF_SIZE], [zlib_level = PNG_Z_DEFAULT_COMPRESSION = -1],
    [zlib_mem_level = 8], [zlib_window_bits = 15], [zlib_method = 8]. *)
Record ZParams : Type := mkZParams {
  zp_level        : Z;
  zp_method       : Z;
  zp_window_bits  : Z;
  zp_mem_level    : Z;
  zp_strategy     : Z
}.

Definition idat_zparams (do_filter data_size : Z) : ZParams :=
  {| zp_level := PNG_Z_DEFAULT_COMPRESSION;
     zp_method := 8;
     zp_window_bits := deflate_claim_window_bits 15 data_size;
     zp_mem_level := 8;
     zp_strategy := idat_strategy false PNG_Z_DEFAULT_STRATEGY do_filter |}.

(** The strategy the IDAT stream is ACTUALLY compressed with, as a function
    of the harness's own IHDR parameters: [png_write_IHDR] sets
    [PNG_ALL_FILTERS], [png_write_start_row] narrows it, and
    [png_deflate_claim] reads the narrowed value. *)
Definition encode_do_filter (color_type bit_depth width height : Z) : Z :=
  start_row_do_filter (ihdr_do_filter color_type bit_depth) width height.

Definition encode_strategy (color_type bit_depth width height : Z) : Z :=
  idat_strategy false PNG_Z_DEFAULT_STRATEGY
                (encode_do_filter color_type bit_depth width height).

(** Over the whole shape family the harness synthesises the strategy is
    [Z_FILTERED = 1] except for the 1x1 images, where it is
    [Z_DEFAULT_STRATEGY = 0]. *)
Lemma encode_strategy_1x1 :
  map (fun p => encode_strategy (fst (fst p)) (snd (fst p))
                                (fst (snd p)) (snd (snd p)))
      [ (0,8,(1,1)) ; (0,8,(1,2)) ; (0,8,(2,1)) ; (0,8,(2,2))
      ; (6,16,(1,1)) ; (6,16,(1,64)) ; (6,16,(64,1)) ; (6,16,(64,64))
      ; (4,8,(1,1)) ; (2,16,(1,1)) ]
  = [0; 1; 1; 1; 0; 1; 1; 1; 0; 0].
Proof. vm_compute. reflexivity. Qed.

(** The seven reachable windowBits bands, pinned.  [data_size] is at least 2
    for any image this harness encodes ([w,h >= 1]), and at most
    [64 * (64*4*2) + 64 = 32832]. *)
Lemma window_bits_bands :
  map (deflate_claim_window_bits 15)
      [0; 250; 251; 762; 763; 1786; 1787; 3834; 3835; 7930; 7931; 16122;
       16123; 16384; 16385; 32832]
  = [9; 9; 10; 10; 11; 11; 12; 12; 13; 13; 14; 14; 15; 15; 15; 15].
Proof. vm_compute. reflexivity. Qed.

(** ** 9. [optimize_cmf] — [pngwutil.c:241-284]

    Fires on the FIRST IDAT emission only ([pngwutil.c:998-1002] and
    [:1043-1047], both gated on [(png_ptr->mode & PNG_HAVE_IDAT) == 0] and
    [compression_type == PNG_COMPRESSION_TYPE_BASE]), and rewrites the two
    bytes of the zlib header that [deflate] has already placed in the
    zbuffer, BEFORE the chunk (and therefore its CRC) is written.  Its
    second argument is [png_image_size(png_ptr)] again — the same estimate
    the windowBits loop used, recomputed.

    The loop here has NO [+262] slop, so it typically shrinks ONE STEP
    FURTHER than [png_deflate_claim] did, and its [do]/[while] runs at least
    once, so it can reach [z_cinfo = 0] — a 256-byte window that deflate
    itself never uses.  This is legal (the loop exits with
    [data_size <= 1 << (z_cinfo + 8)], i.e. the whole uncompressed image
    fits in the advertised window, so no distance can exceed it) but it is
    exactly the sort of thing a clean-room encoder would not do. *)

(** [pngwutil.c:270-275]:
<<
      do { half_z_window_size >>= 1; --z_cinfo; }
      while (z_cinfo > 0 && data_size <= half_z_window_size);
>>
    [z_cinfo] and [half_z_window_size] are [unsigned int], and the loop is a
    [do]/[while], so on entry with [z_cinfo == 0] the decrement UNDERFLOWS to
    [0xFFFFFFFF] and the loop keeps going.  That is transcribed with [u32],
    not with a negative [Z] — the differential harness caught the difference
    (the [z_cmf << 8] in the FCHECK fixup then sees [0xFFFFFFF8], not [-8],
    and the two disagree mod 31).

    TERMINATION.  With [z_cinfo >= 1] on entry the loop stops within 7 trips
    ([z_cinfo] reaches 0).  With [z_cinfo == 0] it stops once
    [half_z_window_size] (which starts at 128) halves below [data_size], i.e.
    within 8 trips — UNLESS [data_size == 0], in which case
    [data_size <= half] holds forever at [half = 0] and the loop runs until
    [z_cinfo] wraps back to 0, i.e. 2^32 trips.  CONFIRMED on the delivered
    binary: injecting [(cmf = 0x08, data_size = 0)] at [optimize_cmf.part.0]
    is the ONE stress case out of 330 that never returns
    ([logs/chunk/ocmf_inj.log]: "TimeoutError").  Neither corner is reachable
    from this encoder ([deflate] writes [z_cinfo = w_bits - 8 >= 1] because
    [png_deflate_claim] never goes below [windowBits = 9], and
    [png_image_size] is at least 2 for any [w, h >= 1]); [optimize_cmf_wf]
    records that.  Fuel 40 covers every terminating input. *)
Fixpoint ocmf_shrink (n : nat) (data_size half cinfo : Z) : Z * Z :=
  match n with
  | O => (half, cinfo)
  | S k =>
      let half' := Z.shiftr half 1 in
      let ci' := u32 (cinfo - 1) in
      if negb (Z.eqb ci' 0) && (Z.leb data_size half')
      then ocmf_shrink k data_size half' ci'
      else (half', ci')
  end.

(** The two corners of [ocmf_shrink] a caller must avoid to match the C: the
    [z_cinfo == 0] entry (an unsigned underflow) and, within it,
    [data_size == 0] (2^32 trips).  Every call this driver makes satisfies
    [1 <= z_cinfo <= 7] and [2 <= data_size]. *)
Definition optimize_cmf_wf (b0 data_size : Z) : Prop :=
  1 <= Z.shiftr (u8 b0) 4 <= 7 /\ 1 <= data_size.

(** [pngwutil.c:279-281]:
<<
      tmp = data[1] & 0xe0;
      tmp += 0x1f - ((z_cmf << 8) + tmp) % 0x1f;
      data[1] = (png_byte)tmp;
>>
    BUG-FOR-BUG: when the remainder is already 0 this adds 0x1f, so FCHECK
    is written as 31 rather than 0.  Both satisfy the RFC-1950 constraint
    [(CMF*256 + FLG) mod 31 == 0]; only one of them is what a naive
    implementation writes.  [z_cmf] here is the FULL [unsigned int], not the
    byte that was stored: after an underflow it is [0xFFFFFFF8] while
    [data[0]] is [0xF8], and the two give different remainders. *)
Definition cmf_fcheck (cmf flg_hi : Z) : Z :=
  flg_hi + (31 - (u32 (u32 (Z.shiftl cmf 8) + flg_hi)) mod 31).

Definition optimize_cmf (b0 b1 data_size : Z) : Z * Z :=
  if Z.leb data_size 16384 then
    let z_cmf := u8 b0 in
    if (Z.eqb (Z.land z_cmf 15) 8) && (Z.leb (Z.land z_cmf 240) 112) then
      let z_cinfo := Z.shiftr z_cmf 4 in
      let half := Z.shiftl 1 (z_cinfo + 7) in
      if Z.leb data_size half then
        let ci := snd (ocmf_shrink 40%nat data_size half z_cinfo) in
        let cmf' := u32 (Z.lor (Z.land z_cmf 15) (u32 (Z.shiftl ci 4))) in
        (u8 cmf', u8 (cmf_fcheck cmf' (Z.land (u8 b1) 224)))
      else (u8 b0, u8 b1)
    else (u8 b0, u8 b1)
  else (u8 b0, u8 b1).

(** The rewrite as seen on the byte stream: the first two bytes of the whole
    deflate output.  ([data] is [zbuffer_list->output], and the zlib header
    is the first thing [deflate] emits, so [data[0]]/[data[1]] are always
    the stream's first two bytes; the buffer is 8192 long and the first
    emission always carries at least the header.) *)
Definition apply_optimize_cmf (data_size : Z) (zout : list Z) : list Z :=
  match zout with
  | b0 :: b1 :: rest =>
      let p := optimize_cmf b0 b1 data_size in fst p :: snd p :: rest
  | _ => zout
  end.

(** [deflate.c:996-1012]: the header [deflate] writes before
    [optimize_cmf] gets at it.  [level_flags] is 2 because the effective
    level is 6 and the strategy ([Z_FILTERED = 1]) is below
    [Z_HUFFMAN_ONLY = 2]; [PRESET_DICT] is never set ([strstart = 0] at
    [INIT_STATE]). *)
Definition deflate_level_flags (level strategy : Z) : Z :=
  if (Z.leb 2 strategy) || (Z.ltb level 2) then 0
  else if Z.ltb level 6 then 1
  else if Z.eqb level 6 then 2
  else 3.

Definition deflate_zlib_header (w_bits level strategy : Z) : Z * Z :=
  let h0 := Z.shiftl (8 + Z.shiftl (w_bits - 8) 4) 8 in
  let h1 := Z.lor h0 (Z.shiftl (deflate_level_flags level strategy) 6) in
  let h := h1 + (31 - h1 mod 31) in
  (u8 (h / 256), u8 h).

(** [deflate.c:411]: [deflate_zlib_header]'s [level] argument is the value
    [deflateInit2_] STORED, i.e. after the [Z_DEFAULT_COMPRESSION -> 6]
    substitution.  libpng passes [-1], so every call site must map it
    first. *)
Definition zdefl_level (level : Z) : Z := if Z.eqb level (-1) then 6 else level.

(** The two header bytes the delivered binary actually emits for a stream of
    [data_size] uncompressed bytes, end to end: [png_deflate_claim] picks
    [windowBits], [deflate] writes the header, [optimize_cmf] rewrites it.
    (For the strategy-aware form keyed on the IHDR parameters — the
    1x1 images compress with [Z_DEFAULT_STRATEGY], see
    [start_row_do_filter] — use [encode_zlib_header] in §12.) *)
Definition emitted_zlib_header_effective (data_size : Z) : Z * Z :=
  let wb := deflate_claim_window_bits 15 data_size in
  let p := deflate_zlib_header wb (zdefl_level PNG_Z_DEFAULT_COMPRESSION)
                               PNG_Z_DEFAULT_STRATEGY in
  optimize_cmf (fst p) (snd p) data_size.

(** The closed form of the D8 item: the window the EMITTED header
    advertises is the smallest power of two that is at least [data_size],
    clamped into [256 .. 32768] — while the window deflate really used is
    [2^(deflate_claim_window_bits 15 data_size)], which is larger whenever
    [data_size + 262] crossed a boundary the un-slopped loop did not.  Pinned
    over the band boundaries. *)
Definition emitted_window (data_size : Z) : Z :=
  Z.shiftl 1 (Z.shiftr (fst (emitted_zlib_header_effective data_size)) 4 + 8).

Lemma emitted_window_is_ceil_pow2 :
  map emitted_window
      [1; 250; 251; 300; 512; 513; 762; 763; 1786; 1787; 3834; 3835;
       7930; 7931; 16122; 16123; 16384]
  = [256; 256; 256; 512; 512; 1024; 1024; 1024; 2048; 2048; 4096; 4096;
     8192; 8192; 16384; 16384; 16384].
Proof. vm_compute. reflexivity. Qed.

(** …and it is strictly smaller than the window deflate used on most of the
    band, which is the observable deviation. *)
Lemma emitted_window_below_deflate_window :
  map (fun d => (emitted_window d,
                 Z.shiftl 1 (deflate_claim_window_bits 15 d)))
      [1; 250; 763; 3835; 16123]
  = [(256, 512); (256, 512); (1024, 2048); (4096, 8192); (16384, 32768)].
Proof. vm_compute. reflexivity. Qed.

(** The two bytes themselves, for the whole reachable band. *)
Lemma emitted_header_bytes :
  map emitted_zlib_header_effective
      [1; 250; 251; 300; 762; 763; 1786; 1787; 3834; 3835; 7930; 7931;
       16122; 16123; 16384; 16385; 32832]
  = [(8, 153); (8, 153); (8, 153); (24, 149); (40, 145); (40, 145);
     (56, 141); (56, 141); (72, 137); (72, 137); (88, 133); (88, 133);
     (104, 129); (104, 129); (104, 129); (120, 156); (120, 156)].
Proof. vm_compute. reflexivity. Qed.
(** ** 9b. [emitted_window_ge] — the advertised window is never too small

    PREMISE OF THE WHOLE DECODER-WINDOW ARGUMENT.  [optimize_cmf]
    advertises a window one step SMALLER than the one deflate actually used
    ([emitted_window_below_deflate_window] above), so the round trip is
    sound only because the uncompressed data still FITS in the advertised
    window: the decoder's [wsize] is [emitted_window data_size], and every
    LZ77 distance the encoder emitted is at most the amount of data already
    produced, which is at most [data_size].  This lemma is that fact.

    The statement is CLAMPED at 32768, and the clamp is not cosmetic:
    the naive [d <= emitted_window d] is FALSE.  It first fails at exactly
    [d = 32769], where [data_size > 16384] short-circuits [optimize_cmf]
    (and [png_deflate_claim]) and the header simply keeps deflate's own
    [windowBits = 15]; see [emitted_window_clamp_is_tight] below.  32768 is
    also the largest window zlib has, so a distance can never exceed it.

    Structure of the proof, which is by the exit invariants of the two
    [do]/[while] loops rather than by enumeration:

      - [dc_shrink_bound]: [png_deflate_claim]'s loop keeps
        [half = 2^(wb-1)] and [data_size + 262 <= 2^wb], and never goes
        below [wb = 9] (its guard needs [half >= 262 > 256]).
      - [ocmf_shrink_window_ge]: [optimize_cmf]'s loop keeps
        [data_size <= half = 2^(cinfo+7)] across every trip, so at exit
        [data_size <= 2^(cinfo_out + 8)] — the advertised window.  Note
        this holds for EVERY fuel, including exhaustion, so it does not
        depend on the 40 being enough.
      - the header bytes in between are pinned per band (seven cases). *)

Local Lemma pow2_le_mono : forall a b, a <= b -> 2 ^ a <= 2 ^ b.
Proof. intros a b H. apply Z.pow_le_mono_r; lia. Qed.

Local Lemma pow2_gt_256_bit : forall k, 256 < 2 ^ k -> 9 <= k.
Proof.
  intros k H. destruct (Z_le_gt_dec 9 k) as [Hk|Hk]; [exact Hk|].
  exfalso. assert (H8 : 2 ^ k <= 2 ^ 8) by (apply pow2_le_mono; lia).
  assert (2 ^ 8 = 256) by reflexivity. lia.
Qed.

Local Lemma shiftr_pow2_succ : forall k, 0 <= k -> Z.shiftr (2 ^ (k + 1)) 1 = 2 ^ k.
Proof.
  intros k Hk. rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.pow_add_r by lia. rewrite Z.pow_1_r.
  apply Z.div_mul. lia.
Qed.

(** [optimize_cmf]'s loop, as a range fact rather than a trip count: it can
    only ever shrink the window down to one that still holds the data. *)
Lemma ocmf_shrink_cinfo_range :
  forall n d half cinfo,
    1 <= cinfo <= 7 -> 0 <= snd (ocmf_shrink n d half cinfo) <= cinfo.
Proof.
  induction n as [|n IH]; intros d half cinfo Hc; cbn [ocmf_shrink].
  - cbn [snd]. lia.
  - assert (Hu : u32 (cinfo - 1) = cinfo - 1) by (apply u32_id; lia).
    rewrite Hu.
    destruct (negb (Z.eqb (cinfo - 1) 0) && Z.leb d (Z.shiftr half 1)) eqn:Hg.
    + apply andb_prop in Hg as [H1 _].
      assert (H1n : cinfo - 1 <> 0)
        by (destruct (Z.eqb (cinfo - 1) 0) eqn:E1;
            [discriminate H1 | now apply Z.eqb_neq in E1]).
      clear H1; rename H1n into H1.
      specialize (IH d (Z.shiftr half 1) (cinfo - 1) ltac:(lia)). lia.
    + cbn [snd]. lia.
Qed.

Lemma ocmf_shrink_window_ge :
  forall n cinfo half d,
    1 <= cinfo <= 7 -> 0 <= d -> half = 2 ^ (cinfo + 7) -> d <= half ->
    d <= 2 ^ (snd (ocmf_shrink n d half cinfo) + 8).
Proof.
  induction n as [|n IH]; intros cinfo half d Hc Hd Hhalf Hle; cbn [ocmf_shrink].
  - cbn [snd]. apply Z.le_trans with half; [exact Hle|].
    subst half. apply pow2_le_mono. lia.
  - assert (Hu : u32 (cinfo - 1) = cinfo - 1) by (apply u32_id; lia).
    assert (Hh : Z.shiftr half 1 = 2 ^ (cinfo - 1 + 7)).
    { subst half. replace (cinfo + 7) with (cinfo - 1 + 7 + 1) by lia.
      apply shiftr_pow2_succ. lia. }
    rewrite Hu.
    destruct (negb (Z.eqb (cinfo - 1) 0) && Z.leb d (Z.shiftr half 1)) eqn:Hg.
    + apply andb_prop in Hg as [H1 H2].
      assert (H1n : cinfo - 1 <> 0)
        by (destruct (Z.eqb (cinfo - 1) 0) eqn:E1;
            [discriminate H1 | now apply Z.eqb_neq in E1]).
      clear H1; rename H1n into H1.
      apply Z.leb_le in H2.
      apply IH; [lia | lia | exact Hh | exact H2].
    + cbn [snd]. replace (cinfo - 1 + 8) with (cinfo + 7) by lia.
      rewrite <- Hhalf. exact Hle.
Qed.

(** [png_deflate_claim]'s loop.  The [+262] slop is what stops it at
    [windowBits = 9]: the guard needs [half >= data_size + 262 >= 262], and
    [262 > 256 = 2^8], so [half = 2^(wb-1)] forces [wb >= 9]. *)
Lemma dc_shrink_bound :
  forall n d half wb,
    0 <= d -> 9 <= wb -> half = 2 ^ (wb - 1) -> d + 262 <= 2 ^ wb ->
    9 <= snd (dc_shrink n d half wb) <= wb
    /\ fst (dc_shrink n d half wb) = 2 ^ (snd (dc_shrink n d half wb) - 1)
    /\ d + 262 <= 2 ^ snd (dc_shrink n d half wb).
Proof.
  induction n as [|n IH]; intros d half wb Hd Hwb Hhalf Hfit; cbn [dc_shrink].
  - cbn [fst snd]. repeat split; try lia; assumption.
  - destruct (Z.leb (d + 262) half) eqn:Hg.
    + apply Z.leb_le in Hg.
      assert (H262 : 256 < 2 ^ (wb - 1)) by (subst half; lia).
      assert (Hwb' : 9 <= wb - 1) by (apply pow2_gt_256_bit in H262; lia).
      assert (Hh : Z.shiftr half 1 = 2 ^ (wb - 1 - 1)).
      { subst half.
        assert (Hp : 2 ^ (wb - 1) = 2 ^ (wb - 1 - 1 + 1)) by (f_equal; lia).
        rewrite Hp. apply shiftr_pow2_succ. lia. }
      specialize (IH d (Z.shiftr half 1) (wb - 1) Hd Hwb' Hh
                     ltac:(rewrite <- Hhalf; exact Hg)).
      destruct IH as [A [B C]]. repeat split; try lia; assumption.
    + cbn [fst snd]. repeat split; try lia; assumption.
Qed.

Lemma dcwb_bound :
  forall d, 0 <= d <= 16384 ->
    9 <= deflate_claim_window_bits 15 d <= 15
    /\ d + 262 <= 2 ^ deflate_claim_window_bits 15 d.
Proof.
  intros d Hd. unfold deflate_claim_window_bits.
  replace (Z.leb d 16384) with true by (symmetry; apply Z.leb_le; lia).
  cbv iota.
  assert (Hs : Z.shiftl 1 (15 - 1) = 2 ^ (15 - 1)) by apply Z.shiftl_1_l.
  assert (Hf : d + 262 <= 2 ^ 15)
    by (assert (H32 : 2 ^ 15 = 32768) by reflexivity; lia).
  pose proof (dc_shrink_bound 16 d (Z.shiftl 1 (15 - 1)) 15
                ltac:(lia) ltac:(lia) Hs Hf) as [A [_ C]].
  split; [lia | exact C].
Qed.

(** The three byte-level facts about the header [deflate] wrote, pinned per
    band.  [1 <= ci0 <= 7] is [9 <= windowBits <= 15]. *)
Local Lemma dzh_cmf :
  forall wb, 9 <= wb <= 15 -> fst (deflate_zlib_header wb 6 1) = 8 + 16 * (wb - 8).
Proof.
  intros wb H.
  assert (Hc : wb = 9 \/ wb = 10 \/ wb = 11 \/ wb = 12 \/ wb = 13 \/ wb = 14 \/ wb = 15)
    by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->| ->]]]]]]; vm_compute; reflexivity.
Qed.

Local Lemma cmf_ok :
  forall ci0, 1 <= ci0 <= 7 ->
    Z.land (u8 (8 + 16 * ci0)) 15 = 8
    /\ Z.land (u8 (8 + 16 * ci0)) 240 = 16 * ci0
    /\ Z.shiftr (u8 (8 + 16 * ci0)) 4 = ci0.
Proof.
  intros ci0 H.
  assert (Hc : ci0 = 1 \/ ci0 = 2 \/ ci0 = 3 \/ ci0 = 4 \/ ci0 = 5 \/ ci0 = 6 \/ ci0 = 7)
    by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->| ->]]]]]];
    (repeat split; vm_compute; reflexivity).
Qed.

(** The high nibble of the byte [optimize_cmf] stores IS the [z_cinfo] its
    loop ended on — the step where the [u32] underflow would have shown up
    if the loop had reached it. *)
Local Lemma cmf_hi_nibble :
  forall ci, 0 <= ci <= 7 ->
    Z.shiftr (u8 (u32 (Z.lor 8 (u32 (Z.shiftl ci 4))))) 4 = ci.
Proof.
  intros ci H.
  assert (Hc : ci = 0 \/ ci = 1 \/ ci = 2 \/ ci = 3 \/ ci = 4 \/ ci = 5
               \/ ci = 6 \/ ci = 7) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
Qed.

(** The rewrite, for a header byte in the reachable band. *)
Lemma optimize_cmf_window_ge :
  forall ci0 b1 d,
    1 <= ci0 <= 7 -> 1 <= d <= 16384 -> d + 262 <= 2 ^ (ci0 + 8) ->
    d <= 2 ^ (Z.shiftr (fst (optimize_cmf (8 + 16 * ci0) b1 d)) 4 + 8).
Proof.
  intros ci0 b1 d Hci Hd Hfit.
  destruct (cmf_ok ci0 Hci) as [E15 [E240 Ehi]].
  assert (G1 : Z.leb d 16384 = true) by (apply Z.leb_le; lia).
  assert (G2 : (Z.eqb (Z.land (u8 (8 + 16 * ci0)) 15) 8)
               && (Z.leb (Z.land (u8 (8 + 16 * ci0)) 240) 112) = true).
  { rewrite E15, E240. apply andb_true_intro. split.
    - apply Z.eqb_eq; reflexivity.
    - apply Z.leb_le; lia. }
  unfold optimize_cmf. cbv zeta. rewrite G1, G2. cbv iota.
  rewrite Ehi, E15.
  assert (Hsh : Z.shiftl 1 (ci0 + 7) = 2 ^ (ci0 + 7)) by apply Z.shiftl_1_l.
  rewrite Hsh.
  destruct (Z.leb d (2 ^ (ci0 + 7))) eqn:Hg; cbn [fst].
  - apply Z.leb_le in Hg.
    pose proof (ocmf_shrink_cinfo_range 40 d (2 ^ (ci0 + 7)) ci0 Hci) as Hr.
    rewrite cmf_hi_nibble by lia.
    apply ocmf_shrink_window_ge; [lia | lia | reflexivity | exact Hg].
  - rewrite Ehi. lia.
Qed.

(** The theorem. *)
Lemma emitted_window_ge :
  forall d, 1 <= d -> Z.min d 32768 <= emitted_window d.
Proof.
  intros d Hd.
  unfold emitted_window, emitted_zlib_header_effective. cbv zeta.
  rewrite Z.shiftl_1_l.
  replace (zdefl_level PNG_Z_DEFAULT_COMPRESSION) with 6 by reflexivity.
  replace PNG_Z_DEFAULT_STRATEGY with 1 by reflexivity.
  destruct (Z_le_gt_dec d 16384) as [Hle | Hgt].
  - (* the band [optimize_cmf] actually rewrites *)
    replace (Z.min d 32768) with d by (symmetry; apply Z.min_l; lia).
    destruct (dcwb_bound d ltac:(lia)) as [Hwb Hfit].
    set (wb := deflate_claim_window_bits 15 d) in *.
    rewrite (dzh_cmf wb Hwb).
    apply (optimize_cmf_window_ge (wb - 8) (snd (deflate_zlib_header wb 6 1)) d);
      [lia | lia | replace (wb - 8 + 8) with wb by lia; exact Hfit].
  - (* [data_size > 16384]: both loops give up, the header keeps the
       encoder own [windowBits = 15] and the window is the full 32768 *)
    assert (Hf : Z.leb d 16384 = false)
      by (destruct (Z.leb d 16384) eqn:E; [apply Z.leb_le in E; lia | reflexivity]).
    assert (Hw : deflate_claim_window_bits 15 d = 15)
      by (unfold deflate_claim_window_bits; rewrite Hf; reflexivity).
    rewrite Hw.
    replace (deflate_zlib_header 15 6 1) with (120, 156) by reflexivity.
    cbn [fst snd]. unfold optimize_cmf. cbv zeta. rewrite Hf. cbv iota. cbn [fst].
    replace (Z.shiftr (u8 120) 4 + 8) with 15 by reflexivity.
    replace (2 ^ 15) with 32768 by reflexivity.
    apply Z.le_min_r.
Qed.

(** The clamp is TIGHT: [d <= emitted_window d] holds up to 32768 and
    fails immediately after, because [png_deflate_claim] and
    [optimize_cmf] both give up above 16384 and leave [windowBits = 15]. *)
Lemma emitted_window_clamp_is_tight :
  emitted_window 32768 = 32768
  /\ emitted_window 32769 = 32768
  /\ emitted_window 40000 = 32768.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** …and a sampled confirmation of the theorem across every band boundary
    the encoder can reach, including the two [optimize_cmf] corners. *)
Lemma emitted_window_ge_sample :
  forallb (fun d => Z.leb (Z.min d 32768) (emitted_window d))
          [1; 2; 250; 251; 256; 257; 300; 512; 513; 762; 763; 1024; 1025;
           1786; 1787; 2048; 2049; 3834; 3835; 4096; 4097; 7930; 7931;
           8192; 8193; 16122; 16123; 16384; 16385; 32768; 32769; 32832;
           40000] = true.
Proof. vm_compute. reflexivity. Qed.

(** ** 10. zlib level-6 configuration and [deflateInit2_] geometry

    Recorded here because the container layer decides them; the deflate lane
    consumes them.  [deflate.c:112-124]:
<<
    local const config configuration_table[10] = {
    /*      good lazy nice chain */
    ...
    /* 6 */ {8,   16, 128, 128, deflate_slow},
>> *)

Inductive DeflateFn : Set := DfStored | DfFast | DfSlow.

Definition cfg_good_length_l : list Z :=
  [0;4;4;4;4;8;8;8;32;32].
Definition cfg_good_length : zarr := zlist cfg_good_length_l.
Definition cfg_max_lazy_l : list Z :=
  [0;4;5;6;4;16;16;32;128;258].
Definition cfg_max_lazy : zarr := zlist cfg_max_lazy_l.
Definition cfg_nice_length_l : list Z :=
  [0;8;16;32;16;32;128;128;258;258].
Definition cfg_nice_length : zarr := zlist cfg_nice_length_l.
Definition cfg_max_chain_l : list Z :=
  [0;4;8;32;16;32;128;256;1024;4096].
Definition cfg_max_chain : zarr := zlist cfg_max_chain_l.
Definition cfg_func (level : Z) : DeflateFn :=
  if Z.eqb level 0 then DfStored
  else if Z.leb level 3 then DfFast
  else DfSlow.

(** The level-6 row, as named constants for the deflate lane. *)
Definition L6_GOOD_LENGTH : Z := 8.
Definition L6_MAX_LAZY    : Z := 16.
Definition L6_NICE_LENGTH : Z := 128.
Definition L6_MAX_CHAIN   : Z := 128.
Definition L6_FUNC        : DeflateFn := DfSlow.

Lemma level6_row :
  (cfg_good_length 6, cfg_max_lazy 6, cfg_nice_length 6, cfg_max_chain 6,
   cfg_func 6)
  = (L6_GOOD_LENGTH, L6_MAX_LAZY, L6_NICE_LENGTH, L6_MAX_CHAIN, L6_FUNC).
Proof. vm_compute. reflexivity. Qed.

(** [deflate.h:290-295]. *)
Definition MIN_MATCH : Z := 3.
Definition MAX_MATCH : Z := 258.
Definition MIN_LOOKAHEAD : Z := 262.   (* MAX_MATCH + MIN_MATCH + 1 *)

(** [deflate.h:224-229].  [LIT_MEM] is COMMENTED OUT at [deflate.h:28] and
    the build adds no [-DLIT_MEM] (see [harness/build.sh]'s
    [build_provable]: plain [gcc -O2], stock [./configure --static]), so
    [LIT_BUFS = 4] and the [sym_buf] layout — not the [d_buf]/[l_buf] one —
    is the live one. *)
Definition LIT_BUFS : Z := 4.

(** Everything [deflateInit2_] derives ([deflate.c:437-513]). *)
Record DeflGeom : Type := mkDeflGeom {
  dg_level            : Z;
  dg_strategy         : Z;
  dg_wrap             : Z;
  dg_w_bits           : Z;
  dg_w_size           : Z;
  dg_w_mask           : Z;
  dg_window_size      : Z;   (** [deflate.c:674]: [2 * w_size] *)
  dg_hash_bits        : Z;
  dg_hash_size        : Z;
  dg_hash_mask        : Z;
  dg_hash_shift       : Z;
  dg_lit_bufsize      : Z;
  dg_pending_buf_bytes: Z;   (** the ZALLOC size: [lit_bufsize * LIT_BUFS] *)
  dg_pending_buf_size : Z;   (** [deflate.c:497]: [lit_bufsize * 4] *)
  dg_sym_buf_off      : Z;   (** [deflate.c:507]: [pending_buf + lit_bufsize] *)
  dg_sym_end          : Z;   (** [deflate.c:508]: [(lit_bufsize - 1) * 3] *)
  dg_max_dist         : Z;   (** [deflate.h:295]: [w_size - MIN_LOOKAHEAD] *)
  dg_good_match       : Z;
  dg_max_lazy_match   : Z;
  dg_nice_match       : Z;
  dg_max_chain_length : Z
}.

(** [deflate.c:413-431]: the wrapper selection and the argument validation,
    ahead of the geometry.  [wrap] is 1 for the zlib wrapper, 0 for a raw
    stream ([windowBits < 0]) and 2 for gzip ([windowBits > 15]); the
    normalised [windowBits] is what [w_bits] becomes.  Only [wrap = 1] with
    [windowBits] in 9..15 is reachable from [png_deflate_claim], but the
    injected stress set drives the others. *)
Definition defl_wrap (windowBits : Z) : option (Z * Z) :=
  if Z.ltb windowBits 0 then
    (if Z.ltb windowBits (-15) then None else Some (0, - windowBits))
  else if Z.ltb 15 windowBits then Some (2, windowBits - 16)
  else Some (1, windowBits).

(** [deflate.c:426-431], including the "until 256-byte window bug fixed"
    bump.  [MAX_MEM_LEVEL] is 9 and [Z_DEFLATED] is 8; [Z_FIXED] is 4. *)
Definition defl_args_ok (level method windowBits memLevel strategy wrap : Z) : bool :=
  (Z.leb 1 memLevel) && (Z.leb memLevel 9) && (Z.eqb method 8)
  && (Z.leb 8 windowBits) && (Z.leb windowBits 15)
  && (Z.leb 0 level) && (Z.leb level 9)
  && (Z.leb 0 strategy) && (Z.leb strategy 4)
  && negb ((Z.eqb windowBits 8) && negb (Z.eqb wrap 1)).

Definition defl_geom_wrap (wrap level0 windowBits memLevel strategy : Z) : DeflGeom :=
  let level := zdefl_level level0 in
  let w_size := Z.shiftl 1 windowBits in
  let hash_bits := memLevel + 7 in
  let hash_size := Z.shiftl 1 hash_bits in
  let lit_bufsize := Z.shiftl 1 (memLevel + 6) in
  {| dg_level := level; dg_strategy := strategy; dg_wrap := wrap;
     dg_w_bits := windowBits; dg_w_size := w_size; dg_w_mask := w_size - 1;
     dg_window_size := 2 * w_size;
     dg_hash_bits := hash_bits; dg_hash_size := hash_size;
     dg_hash_mask := hash_size - 1;
     dg_hash_shift := (hash_bits + MIN_MATCH - 1) / MIN_MATCH;
     dg_lit_bufsize := lit_bufsize;
     dg_pending_buf_bytes := lit_bufsize * LIT_BUFS;
     dg_pending_buf_size := lit_bufsize * 4;
     dg_sym_buf_off := lit_bufsize;
     dg_sym_end := (lit_bufsize - 1) * 3;
     dg_max_dist := w_size - MIN_LOOKAHEAD;
     dg_good_match := cfg_good_length level;
     dg_max_lazy_match := cfg_max_lazy level;
     dg_nice_match := cfg_nice_length level;
     dg_max_chain_length := cfg_max_chain level |}.

(** The zlib-wrapper case, which is the only one [png_deflate_claim] ever
    asks for. *)
Definition defl_geom (level0 windowBits memLevel strategy : Z) : DeflGeom :=
  defl_geom_wrap 1 level0 windowBits memLevel strategy.

(** [deflateInit2_] end to end: [None] is [Z_STREAM_ERROR].

    ORDER MATTERS, and the differential harness caught it: [deflate.c:411]
    maps [Z_DEFAULT_COMPRESSION] to 6 BEFORE the [level < 0 || level > 9]
    range test at [:427].  A model that validates the raw [-1] rejects every
    call libpng makes. *)
Definition defl_init2 (level0 method windowBits memLevel strategy : Z)
  : option DeflGeom :=
  let level := zdefl_level level0 in
  match defl_wrap windowBits with
  | None => None
  | Some (wrap, wb) =>
      if defl_args_ok level method wb memLevel strategy wrap then
        let wb' := if Z.eqb wb 8 then 9 else wb in
        Some (defl_geom_wrap wrap level wb' memLevel strategy)
      else None
  end.

(** The geometry every IDAT stream in this driver is compressed with, apart
    from [windowBits], which the image size picks. *)
Definition idat_geom (data_size : Z) : DeflGeom :=
  defl_geom PNG_Z_DEFAULT_COMPRESSION
            (deflate_claim_window_bits 15 data_size)
            8 PNG_Z_DEFAULT_STRATEGY.

(** When [_tr_flush_block] fires.  [trees.c]'s [_tr_tally] returns
    [s->sym_next == s->sym_end] and [deflate_slow]/[deflate_fast] flush the
    block on that ([deflate.c]'s [FLUSH_BLOCK] macro), so a block is emitted
    every [sym_end / 3 = lit_bufsize - 1] symbols.  With [memLevel = 8] that
    is 16383 — reachable for this driver, whose largest image is
    [64 * (64*4*2) + 64 = 32832] filtered bytes.  The deflate lane owns the
    algorithm; these are the constants it keys off. *)
Definition SYM_BUF_SYMBOLS (lit_bufsize : Z) : Z := lit_bufsize - 1.
Definition L8_LIT_BUFSIZE : Z := 16384.
Definition L8_SYM_END     : Z := 49149.     (* (16384 - 1) * 3 *)
Definition L8_SYM_BUF_OFF : Z := 16384.     (* pending_buf + lit_bufsize *)
Definition L8_PENDING_BUF : Z := 65536.     (* lit_bufsize * LIT_BUFS *)
Definition L8_FLUSH_AFTER : Z := 16383.     (* symbols per block *)

(** [pngstruct.h:67]: [PNG_COMPRESSION_BUFFER_SIZE(pp) =
    offsetof(png_compression_buffer, output) + pp->zbuffer_size].  The struct
    is [{ struct png_compression_buffer *next; png_byte output[1]; }], so on
    riscv64 the offset is 8 and the allocation is 8200 bytes. *)
Definition PNG_COMPRESSION_BUFFER_SIZE : Z := 8 + PNG_ZBUF_SIZE.

(** The [memLevel = 8] constants, pinned: [lit_bufsize = 16384], so
    [_tr_flush_block] fires after [sym_end / 3 = 16383] symbols, the symbol
    area starts 16384 bytes into a 65536-byte [pending_buf], and the hash is
    15 bits with a shift of 5. *)
Lemma memlevel8_geometry :
  forall ds,
    (dg_hash_bits (idat_geom ds), dg_hash_size (idat_geom ds),
     dg_hash_shift (idat_geom ds), dg_lit_bufsize (idat_geom ds),
     dg_pending_buf_bytes (idat_geom ds), dg_sym_buf_off (idat_geom ds),
     dg_sym_end (idat_geom ds))
    = (15, 32768, 5, L8_LIT_BUFSIZE, L8_PENDING_BUF, L8_SYM_BUF_OFF,
       L8_SYM_END)
    /\ SYM_BUF_SYMBOLS (dg_lit_bufsize (idat_geom ds)) = L8_FLUSH_AFTER.
Proof. intros ds. split; vm_compute; reflexivity. Qed.

Lemma level6_geometry :
  forall ds,
    (dg_level (idat_geom ds), dg_strategy (idat_geom ds),
     dg_good_match (idat_geom ds), dg_max_lazy_match (idat_geom ds),
     dg_nice_match (idat_geom ds), dg_max_chain_length (idat_geom ds))
    = (6, 1, 8, 16, 128, 128).
Proof. intros ds. vm_compute. reflexivity. Qed.

(** ** 11. IDAT chunking — [png_compress_IDAT], [pngwutil.c:930-1066]

    The output side is a single 8192-byte buffer
    ([png_ptr->zbuffer_size = PNG_ZBUF_SIZE], [pngwrite.c:538]; the
    allocation is [PNG_COMPRESSION_BUFFER_SIZE(pp) = offsetof(…, output) +
    zbuffer_size = 8 + 8192] on riscv64, [pngstruct.h:67]).  Whenever
    [avail_out] hits 0 an IDAT of EXACTLY [zbuffer_size] bytes is emitted
    ([pngwutil.c:993-1006]); at [Z_STREAM_END] the residue
    [zbuffer_size - avail_out] is emitted IF NONZERO ([pngwutil.c:1041-1051],
    both sites guarded by [if (size > 0)]).  The cut therefore ignores
    deflate block boundaries entirely — it is a pure length split of the
    zlib stream, the analogue of lean-zip's [splitIdat]. *)

(** [chunks n fuel l] cuts [l] into [n]-byte pieces.  Fuel is [length l],
    which is always enough because every trip consumes at least one element
    when [n >= 1]. *)
Fixpoint chunks (n : nat) (fuel : nat) (l : list Z) : list (list Z) :=
  match fuel with
  | O => match l with [] => [] | _ => [l] end
  | S f => match l with
           | [] => []
           | _ :: _ => firstn n l :: chunks n f (skipn n l)
           end
  end.

(** The cut width as a [nat], written through [Z.to_nat] of the [Z] constant
    so that arithmetic side conditions stay in binary. *)
Definition ZBUF_N : nat := Z.to_nat PNG_ZBUF_SIZE.

Lemma ZBUF_N_pos : (0 < ZBUF_N)%nat.
Proof. unfold ZBUF_N, PNG_ZBUF_SIZE. lia. Qed.

Lemma ZBUF_N_Z : Z.of_nat ZBUF_N = PNG_ZBUF_SIZE.
Proof. unfold ZBUF_N, PNG_ZBUF_SIZE. now rewrite Z2Nat.id by lia. Qed.

Definition split_idat (l : list Z) : list (list Z) := chunks ZBUF_N (length l) l.

Lemma chunks_irrel :
  forall f1 n l f2, (0 < n)%nat -> (length l <= f1)%nat -> (length l <= f2)%nat ->
    chunks n f1 l = chunks n f2 l.
Proof.
  induction f1 as [|f1 IH]; intros n l f2 Hn H1 H2.
  - destruct l as [|x xs]; [destruct f2; reflexivity|].
    cbn [length] in H1. lia.
  - destruct l as [|x xs]; [destruct f2; reflexivity|].
    destruct f2 as [|f2]; [cbn [length] in H2; lia|].
    cbn [chunks]. f_equal. apply IH; auto.
    + rewrite length_skipn; cbn [length] in *; lia.
    + rewrite length_skipn; cbn [length] in *; lia.
Qed.

Lemma chunks_concat :
  forall fuel n l, (0 < n)%nat -> (length l <= fuel)%nat ->
    concat (chunks n fuel l) = l.
Proof.
  induction fuel as [|f IH]; intros n l Hn Hl.
  - destruct l as [|x xs]; [reflexivity|]. cbn [length] in Hl. lia.
  - destruct l as [|x xs]; [reflexivity|].
    cbn [chunks concat]. rewrite IH.
    + apply firstn_skipn.
    + exact Hn.
    + rewrite length_skipn; cbn [length] in *; lia.
Qed.

(** The concatenation law the round-trip proof needs: reassembling the IDAT
    payloads recovers the zlib stream exactly. *)
Lemma split_idat_concat : forall l, concat (split_idat l) = l.
Proof.
  intro l. apply chunks_concat; [apply ZBUF_N_pos | reflexivity].
Qed.

(** The unfolding law, in the shape a machine-level walk wants. *)
Lemma split_idat_step :
  forall l, l <> [] ->
    split_idat l = firstn ZBUF_N l :: split_idat (skipn ZBUF_N l).
Proof.
  intros l Hl. unfold split_idat.
  destruct l as [|x xs]; [contradiction|].
  cbn [length chunks].
  f_equal. apply chunks_irrel; [apply ZBUF_N_pos| |reflexivity].
  pose proof ZBUF_N_pos. rewrite length_skipn; cbn [length]; lia.
Qed.

(** No empty IDAT is ever emitted, and none exceeds [PNG_ZBUF_SIZE]. *)
Lemma chunks_bounds :
  forall fuel n l, (0 < n)%nat -> (length l <= fuel)%nat ->
    Forall (fun c => (0 < length c)%nat /\ (length c <= n)%nat) (chunks n fuel l).
Proof.
  induction fuel as [|f IH]; intros n l Hn Hl.
  - destruct l as [|x xs]; [constructor|]. cbn [length] in Hl. lia.
  - destruct l as [|x xs]; [constructor|].
    cbn [chunks]. constructor.
    + rewrite length_firstn. cbn [length]. lia.
    + apply IH; [exact Hn|]. rewrite length_skipn; cbn [length] in *; lia.
Qed.

Lemma split_idat_bounds :
  forall l, Forall (fun c => (0 < length c)%nat /\ (length c <= ZBUF_N)%nat)
                   (split_idat l).
Proof. intro l. apply chunks_bounds; [apply ZBUF_N_pos | reflexivity]. Qed.

(** The IDAT chunk-LENGTH sequence in closed form: [floor(m / 8192)] chunks
    of 8192 followed by [m mod 8192] if that is nonzero.  This is the
    quantity the binary trace reports, so the equation below is the bridge
    between the byte-level split and the observable. *)
Fixpoint lens_aux (n : Z) (fuel : nat) (m : Z) : list Z :=
  match fuel with
  | O => if Z.ltb 0 m then [m] else []
  | S f => if Z.leb m n then (if Z.ltb 0 m then [m] else [])
           else n :: lens_aux n f (m - n)
  end.

Definition idat_lengths (m : Z) : list Z :=
  lens_aux PNG_ZBUF_SIZE (Z.to_nat m) m.

Lemma lens_aux_nil : forall n f, 0 <= n -> lens_aux n f 0 = [].
Proof.
  intros n f Hn. destruct f; cbn [lens_aux].
  - reflexivity.
  - replace (Z.leb 0 n) with true by (symmetry; apply Z.leb_le; lia).
    reflexivity.
Qed.

Lemma chunks_lens :
  forall n fuel l, (0 < n)%nat -> (length l <= fuel)%nat ->
    map (fun c => Z.of_nat (length c)) (chunks n fuel l)
    = lens_aux (Z.of_nat n) fuel (Z.of_nat (length l)).
Proof.
  intros n fuel. revert n.
  induction fuel as [|f IH]; intros n l Hn Hl.
  - destruct l as [|x xs]; [cbn; reflexivity|]. cbn [length] in Hl. lia.
  - destruct l as [|x xs].
    + replace (Z.of_nat (length (@nil Z))) with 0 by reflexivity.
      cbn [chunks map]. rewrite lens_aux_nil by lia. reflexivity.
    + cbn [chunks map]. cbn [lens_aux].
      destruct (Z.leb (Z.of_nat (length (x :: xs))) (Z.of_nat n)) eqn:Hle.
      * apply Z.leb_le in Hle.
        rewrite firstn_all2 by lia.
        rewrite skipn_all2 by lia.
        replace (Z.ltb 0 (Z.of_nat (length (x :: xs)))) with true
          by (symmetry; apply Z.ltb_lt; cbn [length]; lia).
        destruct f; reflexivity.
      * apply Z.leb_gt in Hle.
        rewrite length_firstn.
        replace (Nat.min n (length (x :: xs))) with n by lia.
        cbn [map]. f_equal.
        rewrite IH; [| exact Hn | rewrite length_skipn; cbn [length] in *; lia].
        rewrite length_skipn. f_equal. cbn [length] in *. lia.
Qed.

Lemma split_idat_lengths :
  forall l, map (fun c => Z.of_nat (length c)) (split_idat l)
            = idat_lengths (Z.of_nat (length l)).
Proof.
  intro l. unfold split_idat, idat_lengths.
  rewrite chunks_lens by (first [apply ZBUF_N_pos | reflexivity]).
  now rewrite ZBUF_N_Z, Nat2Z.id.
Qed.

(** ** 12. The stream [encode_raw] produces — [png_harness.c:246-268]

    [png_write_info] emits signature ++ IHDR and nothing else (see the
    dead-branch finding in the header); [png_write_image] +
    [png_write_finish_row] ([pngwutil.c:2085-2088]) drive
    [png_compress_IDAT] to [Z_FINISH], emitting the IDAT run;
    [png_write_end] emits IEND ([pngwrite.c:457-459]).

    [zout] is the raw deflate output BEFORE [optimize_cmf]; the model
    applies the rewrite here, because that is where the C applies it (to the
    buffer, before the chunk goes out and before its CRC is taken). *)

Definition encode_chunks (s : WrHdr) (ihdr : list Z) (zout : list Z)
  : list (list Z) :=
  let ds := wr_image_size s in
  let z := apply_optimize_cmf ds zout in
  ihdr :: map (chunk_bytes ty_IDAT) (split_idat z) ++ [png_write_IEND_bytes].

Definition encode_stream (width height bit_depth color_type interlace_type : Z)
                         (zout : list Z) : option (list Z) :=
  match png_write_IHDR width height bit_depth color_type
                       PNG_COMPRESSION_TYPE_BASE PNG_FILTER_TYPE_BASE
                       interlace_type with
  | None => None
  | Some (s, ihdr) => Some (png_signature ++ concat (encode_chunks s ihdr zout))
  end.

(** The two zlib header bytes the encoder actually emits, as a function of
    the harness's own IHDR parameters.  This is the composition of the whole
    D8 cluster — [png_image_size] -> [png_deflate_claim]'s windowBits ->
    [deflate]'s header -> [optimize_cmf]'s rewrite — and it is what the first
    two bytes of the first IDAT payload are.  [None] where
    [png_write_IHDR] would [png_error]. *)
Definition encode_zlib_header (width height bit_depth color_type
                               interlace_type : Z) : option (Z * Z * Z) :=
  match png_write_IHDR width height bit_depth color_type
                       PNG_COMPRESSION_TYPE_BASE PNG_FILTER_TYPE_BASE
                       interlace_type with
  | None => None
  | Some (s, _) =>
      let ds := wr_image_size s in
      let strat := idat_strategy false PNG_Z_DEFAULT_STRATEGY
                     (start_row_do_filter (wh_do_filter s) width height) in
      let wb := deflate_claim_window_bits 15 ds in
      let p := deflate_zlib_header wb (zdefl_level PNG_Z_DEFAULT_COMPRESSION)
                                   strat in
      let q := optimize_cmf (fst p) (snd p) ds in
      Some (ds, fst q, snd q)
  end.

(** The image size the encoder feeds to [png_deflate_claim] and
    [optimize_cmf], as a function of the harness's own parameters.  This is
    the single number the whole D8 cluster keys off. *)
Definition encode_data_size (width height bit_depth color_type interlace_type : Z)
  : option Z :=
  match png_write_IHDR width height bit_depth color_type
                       PNG_COMPRESSION_TYPE_BASE PNG_FILTER_TYPE_BASE
                       interlace_type with
  | None => None
  | Some (s, _) => Some (wr_image_size s)
  end.

(** ** 13. The read side — container only

    [png_read_sig] ([pngrutil.c:119-150]), [png_read_chunk_header]
    ([pngrutil.c:153-192]), [png_crc_read]/[png_crc_error]
    ([pngrutil.c:194-283]).  [decode_raw] ([png_harness.c:273-304]) does NOT
    call [png_set_crc_action], so [png_ptr->flags] is 0, [need_crc] is 1 for
    critical chunks, and a CRC mismatch on IHDR/IDAT/IEND is a hard
    [png_chunk_error].  ([run_read] and [roundtrip_decode_encode] DO set
    [PNG_CRC_QUIET_USE], but those are the safety-only phases, not the
    round-trip one.)

    Modelled: the byte-level parse.  Not modelled: chunk dispatch, the
    ancillary-chunk policy, [png_check_chunk_length]'s IDAT limit
    arithmetic, [png_read_buffer] regrowth, and the truncated-IDAT recovery
    — all unreachable for encoder-produced input; see [read_wf]. *)

Record PChunk : Type := mkPChunk {
  pc_type : list Z;
  pc_data : list Z;
  pc_crc  : Z
}.

Fixpoint zlist_beq (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: xs, y :: ys => Z.eqb x y && zlist_beq xs ys
  | _, _ => false
  end.

Lemma zlist_beq_refl : forall l, zlist_beq l l = true.
Proof.
  induction l as [|x xs IH]; [reflexivity|].
  cbn. now rewrite Z.eqb_refl, IH.
Qed.

(** [pngrutil.c:119-150] + [png.c]'s [png_sig_cmp].  [decode_raw] leaves
    [sig_bytes] at 0, so all eight bytes are checked. *)
Definition png_read_sig_ok (l : list Z) : bool :=
  zlist_beq (firstn 8 l) png_signature.

(** [pngrutil.c:3134-3150]: each of the four type bytes must be an ASCII
    letter. *)
Definition chunk_name_byte_ok (c : Z) : bool :=
  (Z.leb 65 c) && (Z.leb c 122) && negb ((Z.ltb 90 c) && (Z.ltb c 97)).

Definition chunk_name_ok (ty : list Z) : bool :=
  forallb chunk_name_byte_ok ty.

(** One chunk: header (length + type), payload, CRC.  [None] is any of the
    C's exits — a short read (which [png_read_data] turns into
    "Read Error"), [png_get_uint_31]'s range error, or an invalid type. *)
Definition read_chunk (l : list Z) : option (PChunk * list Z) :=
  if Nat.ltb (length l) 8 then None
  else match get_uint_31 l with
       | None => None
       | Some len =>
           let ty := firstn 4 (skipn 4 l) in
           if negb (chunk_name_ok ty) then None
           else
             let r := skipn 8 l in
             if Nat.ltb (length r) (Z.to_nat len + 4) then None
             else Some (mkPChunk ty (firstn (Z.to_nat len) r)
                                 (be32_at (skipn (Z.to_nat len) r)),
                        skipn (Z.to_nat len + 4) r)
       end.

Definition chunk_crc_ok (c : PChunk) : bool :=
  Z.eqb (pc_crc c) (crc32_bytes 0 (pc_type c ++ pc_data c)).

(** The chunk list, stopping after IEND.  Fuel is the byte length, and every
    trip consumes at least 12 bytes, so it never binds. *)
Fixpoint read_chunks (fuel : nat) (l : list Z) : option (list PChunk) :=
  match fuel with
  | O => None
  | S f =>
      match read_chunk l with
      | None => None
      | Some (c, rest) =>
          if zlist_beq (pc_type c) ty_IEND then Some [c]
          else match read_chunks f rest with
               | None => None
               | Some cs => Some (c :: cs)
               end
      end
  end.

Definition parse_png (l : list Z) : option (list PChunk) :=
  if png_read_sig_ok l then read_chunks (length l) (skipn 8 l) else None.

(** [png_read_IDAT_data] ([pngrutil.c:4147-4271]) hands zlib the
    concatenation of the IDAT payloads, cut at [IDAT_read_size = 8192] input
    bytes per [inflate] call but otherwise contiguous: the cut is invisible
    to the decompressed result, so at the model level the compressed stream
    is just the concatenation. *)
Definition idat_stream (cs : list PChunk) : list Z :=
  concat (map pc_data (filter (fun c => zlist_beq (pc_type c) ty_IDAT) cs)).

(** The container round-trip fact the pixel-level proof rests on: whatever
    the encoder split, the decoder rejoins. *)
Lemma idat_stream_all :
  forall ds, idat_stream (map (fun d => mkPChunk ty_IDAT d 0) ds) = concat ds.
Proof.
  induction ds as [|d ds IH]; [reflexivity|].
  unfold idat_stream in *. cbn [map filter pc_type pc_data].
  rewrite zlist_beq_refl. cbn [map concat]. now rewrite IH.
Qed.

Lemma idat_stream_of_split :
  forall z, idat_stream (map (fun d => mkPChunk ty_IDAT d 0) (split_idat z)) = z.
Proof. intro z. rewrite idat_stream_all. apply split_idat_concat. Qed.

(** ** 14. Well-formedness

    The hypotheses under which the transcription above is exact for THIS
    driver.  A machine-level walk discharges them from the caller's
    invariant; they are stated rather than enforced so that every function
    here stays total. *)

(** The shape family [assert_roundtrip] is ever called with
    ([png_harness.c:337-352] for [roundtrip_encode_decode],
    [:396] for [roundtrip_decode_encode]).  [w] and [h] are
    [1 + (byte & 63)], the colour type is one of four, the bit depth is 8 or
    16, and the interlace type is always [PNG_INTERLACE_NONE]. *)
Definition encode_wf (width height bit_depth color_type interlace_type : Z)
  : Prop :=
  1 <= width <= 64
  /\ 1 <= height <= 64
  /\ (bit_depth = 8 \/ bit_depth = 16)
  /\ (color_type = CT_GRAY \/ color_type = CT_GRAY_ALPHA
      \/ color_type = CT_RGB \/ color_type = CT_RGB_ALPHA)
  /\ interlace_type = PNG_INTERLACE_NONE.

(** Exactness of [png_deflate_claim] / [optimize_cmf] for a [data_size]
    that fits the estimate's own assumptions.

    DOCSTRING CORRECTED 2026-08-16 (iface-fixer's sweep, and the correction
    is sharper than the finding).  This comment used to add "and for the
    default parameter block ([windowBits = 15], [memLevel = 8],
    [level = -1], no custom strategy).  Both hold for every encode this
    driver performs."  On the natural reading that is FALSE, and this file
    contains its own refutation: [window_bits_bands] proves SEVEN reachable
    windowBits values (9..15), because shrinking them is the entire point
    of [png_deflate_claim].  15 is the value libpng REQUESTS; what reaches
    [deflateInit2] is the shrunk one.  Anyone reading the old comment would
    have concluded the emitted window is always 15, which is exactly the D8
    item this file exists to pin.

    What the predicate below actually asserts is the [data_size] range and
    the [do_filter] alternative, and that is all it can assert:
    [windowBits] / [memLevel] / [level] are not arguments of it.  The
    request-side parameter block is a fact about the CALLER
    ([Codec.enc_raw] passes [deflate_claim_window_bits 15 ds], memLevel 8,
    level -1), stated there and not discharged here. *)
Definition zparams_wf (do_filter data_size : Z) : Prop :=
  0 <= data_size <= 4294967295
  /\ (do_filter = PNG_ALL_FILTERS \/ do_filter = PNG_FILTER_NONE).

(** The read side is only modelled for streams this encoder produced: the
    chunk sequence is IHDR · IDAT+ · IEND, every length is at most
    [PNG_ZBUF_SIZE], and therefore [png_check_chunk_length]'s limit
    ([min(PNG_UINT_31_MAX, PNG_USER_CHUNK_MALLOC_MAX) = 8000000], widened
    for IDAT) is never approached and [png_benign_error] is never called. *)
Definition idat_run (cs : list PChunk) : Prop :=
  cs <> [] /\ Forall (fun c => pc_type c = ty_IDAT) cs.

(** The sequence clause, which the docstring above always claimed and the
    conjuncts below did not state until 2026-08-16.  Without it, [read_wf]
    was satisfied by (for instance) a list of nothing but IENDs, while two
    other sites in this file pointed AT it for exactly this restriction.

    THE 13-BYTE IHDR CONJUNCT IS NOT DECORATION (wp5-pf, 2026-08-16, the
    first real consumer of this predicate).  [Codec.dec_raw] is the only
    consumer of a parsed chunk list in the tree, and its FIRST content gate
    is [read_ihdr], which demands [length (pc_data ihdr) = 13].  Without
    this conjunct a stream satisfying [read_wf] can carry an EMPTY IHDR
    payload and [read_ihdr] returns [None] — so a consumer handed [read_wf]
    could not conclude the decode gets past its own first gate, and would
    have had to assume the IHDR fact separately, at which point [read_wf]
    is not doing the work.  A predicate called [read_wf] that does not imply
    the read succeeds is misnamed.  Scoping IHDR contents OUT was a
    deliberate decision recorded in this lane's interface contract, and it
    was the wrong one; the consumer is what showed that. *)
Definition seq_wf (cs : list PChunk) : Prop :=
  exists ihdr mid iend,
    cs = ihdr :: (mid ++ [iend])
    /\ pc_type ihdr = ty_IHDR
    /\ zlen (pc_data ihdr) = 13
    /\ pc_type iend = ty_IEND
    /\ idat_run mid.

(** [cs <> []] was dropped 2026-08-16: [seq_wf] implies it (the list is
    [ihdr :: _]), so it was a conjunct that could never fail and could only
    mislead a reader into thinking it carried weight. *)
Definition read_wf (cs : list PChunk) : Prop :=
  seq_wf cs
  /\ Forall (fun c => zlen (pc_data c) <= PNG_ZBUF_SIZE) cs
  /\ Forall (fun c => chunk_crc_ok c = true) cs.

(** Non-vacuity: [read_wf] is satisfiable, and by a stream of the shape the
    encoder actually emits.

    THIS LEMMA USED TO BE A LIE OF SCOPE, and it is worth leaving the note.
    It carried this same docstring while STATING only [seq_wf] — one of the
    conjuncts — over a witness whose CRC fields were all 0.  Since
    crc32("IHDR") is 0xa8a1ae0a, that witness does NOT satisfy [read_wf]:
    wp5-pf's probe [~ read_wf sat_witness] is Qed.  The lemma was true and
    the sentence above it was not established by it.  Note the CRC conjunct
    closes by [Z.eqb_refl] with no computation, because [chunk_crc] IS the
    value [chunk_crc_ok] compares against — a correct witness was always
    cheaper to write than the broken one. *)
Lemma read_wf_sat :
  read_wf
    [mkPChunk ty_IHDR [0;0;0;1; 0;0;0;1; 8; 0; 0; 0; 0]
              (chunk_crc ty_IHDR [0;0;0;1; 0;0;0;1; 8; 0; 0; 0; 0]);
     mkPChunk ty_IDAT [8; 29; 99; 96; 0; 0; 0; 2; 0; 1]
              (chunk_crc ty_IDAT [8; 29; 99; 96; 0; 0; 0; 2; 0; 1]);
     mkPChunk ty_IEND [] (chunk_crc ty_IEND [])].
Proof.
  unfold read_wf. split.
  - exists (mkPChunk ty_IHDR [0;0;0;1; 0;0;0;1; 8; 0; 0; 0; 0]
                     (chunk_crc ty_IHDR [0;0;0;1; 0;0;0;1; 8; 0; 0; 0; 0])),
           [mkPChunk ty_IDAT [8; 29; 99; 96; 0; 0; 0; 2; 0; 1]
                     (chunk_crc ty_IDAT [8; 29; 99; 96; 0; 0; 0; 2; 0; 1])],
           (mkPChunk ty_IEND [] (chunk_crc ty_IEND [])).
    (* NO [cbn] HERE — wp5-pf's finding, and I walked into it once by lifting
       the tactic from their abbreviated probe instead of their inlined one.
       With the CRCs inlined, [cbn] delta-unfolds [chunk_crc] into the
       bit-at-a-time CRC-32 and reduces it symbolically over 17 bytes; the
       build runs for minutes. [reflexivity]'s own conversion closes the
       projection goals and [vm_compute] below computes the same CRCs
       instantly. The deadly reducer is the one that unfolds and rewrites,
       not the one that evaluates. *)
    repeat split; try reflexivity; try discriminate.
    repeat constructor.
  - split.
    + repeat constructor; vm_compute; intro Hx; discriminate Hx.
    + repeat constructor; unfold chunk_crc_ok, chunk_crc; cbn;
        apply Z.eqb_refl.
Qed.

(** And it really does exclude what it was meant to exclude. *)
Lemma read_wf_rejects_iend_only :
  ~ seq_wf [mkPChunk ty_IEND [] 0].
Proof.
  intros [ihdr [mid [iend [Heq _]]]].
  destruct mid as [|m mid2]; cbn in Heq; inversion Heq.
Qed.

(** ** 15. Wrappers for the differential harness

    [zarr]/[ztbl] never appear on this interface; everything is lists and
    integers, so the extracted OCaml is a direct match for the record
    formats in [a working folder]. *)

(** CR1 record: given the IHDR parameters, everything the container layer
    determines.  Matches the tuple [chunkdump_rsp.py] reports. *)
Record ChunkOut : Type := mkChunkOut {
  co_channels    : Z;
  co_pixel_depth : Z;
  co_rowbytes    : Z;
  co_do_filter   : Z;
  co_image_size  : Z;
  co_window_bits : Z;
  co_strategy    : Z;
  co_level       : Z;
  co_mem_level   : Z;
  co_method      : Z;
  co_cmf_in      : Z;
  co_flg_in      : Z;
  co_cmf_out     : Z;
  co_flg_out     : Z;
  co_ihdr        : list Z
}.

Definition chunk_model (width height bit_depth color_type interlace_type : Z)
  : option ChunkOut :=
  match png_write_IHDR width height bit_depth color_type
                       PNG_COMPRESSION_TYPE_BASE PNG_FILTER_TYPE_BASE
                       interlace_type with
  | None => None
  | Some (s, ihdr) =>
      let ds := wr_image_size s in
      let zp := idat_zparams (wh_do_filter s) ds in
      let hin := deflate_zlib_header (zp_window_bits zp)
                                     (zdefl_level (zp_level zp))
                                     (zp_strategy zp) in
      let hout := optimize_cmf (fst hin) (snd hin) ds in
      Some {| co_channels := wh_channels s;
              co_pixel_depth := wh_pixel_depth s;
              co_rowbytes := wh_rowbytes s;
              co_do_filter := wh_do_filter s;
              co_image_size := ds;
              co_window_bits := zp_window_bits zp;
              co_strategy := zp_strategy zp;
              co_level := zp_level zp;
              co_mem_level := zp_mem_level zp;
              co_method := zp_method zp;
              co_cmf_in := fst hin; co_flg_in := snd hin;
              co_cmf_out := fst hout; co_flg_out := snd hout;
              co_ihdr := ihdr |}
  end.

(** The IDAT-length sequence for a deflate output of [m] bytes. *)
Definition chunk_idat_lengths (m : Z) : list Z := idat_lengths m.

(** [optimize_cmf] as the harness observes it: two bytes in, two bytes out. *)
Definition chunk_optimize_cmf (b0 b1 data_size : Z) : Z * Z :=
  optimize_cmf b0 b1 data_size.

(** [png_image_size] straight from the [png_struct] fields the tracer
    reads out of memory at the breakpoint. *)
Definition chunk_image_size (rowbytes height width pixel_depth interlaced : Z) : Z :=
  png_image_size rowbytes height width pixel_depth interlaced.

(** [png_deflate_claim]'s windowBits, from the two values the tracer
    captures at its entry. *)
Definition chunk_window_bits (windowBits data_size : Z) : Z :=
  deflate_claim_window_bits windowBits data_size.

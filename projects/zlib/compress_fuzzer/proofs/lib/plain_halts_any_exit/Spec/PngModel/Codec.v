(** * Spec.PngModel.Codec — the seam: [encode_raw] / [decode_raw] as a [Codec].

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.  This is the only file
    in [Spec/PngModel] that [Require Import]s the whole tree; everything
    below is composition, not new transcription.  Every C function it needs
    was transcribed by one of the five lanes and is called here by name.

    WHAT THIS FILE IS FOR.  [Spec/PngModel/Harness.v] transcribes the fuzz
    driver down to a three-field record

<<
      Record Codec := mkCodec { cd_enc; cd_dec; cd_front }
>>

    and proves everything the round-trip arm needs ([rt_viol_false],
    [rt_arm_collapses]) FROM that record plus [codec_wf] and
    [codec_ed_id].  What it does not have is an instance.  This file builds
    one — [PngCodec] — out of the real transcriptions, and discharges
    [codec_body] and [codec_front_wf] for it.  [codec_ed_id] is the
    round-trip research core and is deliberately NOT attempted here.

    THE ENCODE PIPELINE, and which lane owns each step
    ([png_harness.c:246-268] [encode_raw]):

      pixels
        -> [rows_of]                       (this file: [pix + y*rb])
        -> [Filter.png_write_find_filter]  (filter lane, [pngwutil.c:2548])
        -> [Deflate.deflate] via [defl_pump] at the geometry
           [Chunk.idat_zparams] pins        (deflate lane + container lane)
        -> [Chunk.encode_stream]            (container lane: sig, IHDR,
           which applies [Chunk.optimize_cmf] and cuts IDAT at 8192)
        -> PNG bytes

    THE DECODE PIPELINE ([png_harness.c:273-304] [decode_raw]):

      PNG bytes
        -> [Chunk.parse_png]                (container lane)
        -> IHDR match + [Chunk.idat_stream] (container lane)
        -> [Inflate.inflate_model] via [inf_pump]  (decoder lane)
        -> [Filter.png_read_filter_row]     (filter lane)
        -> pixels

    CHECKSUMS.  Both ends go through [Checksum.crc32_ref] (which
    [Chunk.crc32_bytes] is now defined as) and [Checksum.adler32_z]; the
    braid identity [ChecksumThy.crc32_braid_eq] connects those to the
    braided loop the delivered binary actually runs.

    [cd_front] — the P3 front end — is §6: [png_check_IHDR], the
    pre-IHDR chunk scan, and [png_read_transform_info]'s
    post-transformation rowbytes arithmetic.  What §6 deliberately
    does NOT transcribe, and why that is sound, is stated there.

    NOTHING in this file is [Admitted]; there are no [Axiom]s,
    [Parameter]s or [Hypothesis]es. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel
  Require Import Base Checksum ChecksumThy Filter Chunk Inftrees ZBitsIn
                 ZBitsOut InflateFast Inflate Trees Deflate Harness.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

(** * §0  Cross-lane consistency

    Five lanes wrote thirteen files without seeing each other's.  Where two
    of them transcribed the same C fact under different names, the fact is
    pinned here rather than assumed.  Each of these is the integrator's
    receipt for one audit finding; all are [reflexivity] or a four-way case
    split, so they cost nothing and they fail loudly if a lane's file
    drifts. *)

(** [Harness.v] names the PNG colour types after png.h's
    [PNG_COLOR_TYPE_*]; [Chunk.v] names them [CT_*] after its own §1.  Same
    five numbers.  (Note that [Inftrees.v]'s [CT_CODES]/[CT_LENS]/
    [CT_DISTS] are a DIFFERENT [CT_]: zlib's [codetype] enum.  No name
    collides, but the prefix is overloaded — read the qualifier.) *)
Lemma colour_type_names_agree :
  PNG_CT_GRAY = CT_GRAY /\ PNG_CT_RGB = CT_RGB /\ PNG_CT_PALETTE = CT_PALETTE
  /\ PNG_CT_GRAY_ALPHA = CT_GRAY_ALPHA /\ PNG_CT_RGB_ALPHA = CT_RGB_ALPHA.
Proof. repeat split; reflexivity. Qed.

(** [Harness.v]'s [channels_of] is [png_harness.c:230-238]'s own switch;
    [Chunk.v]'s [ihdr_channels] is [pngwutil.c:681-750]'s validation table.
    Different C functions, and they must agree or [sh_total] and
    [wh_rowbytes] describe different buffers.  They do, on every shape the
    driver reaches. *)
Lemma channels_agree :
  forall ct bd, In ct ed_cts -> (bd = 8 \/ bd = 16) ->
    ihdr_channels ct bd = Some (channels_of ct).
Proof.
  intros ct bd Hct Hbd.
  unfold ed_cts, PNG_CT_GRAY, PNG_CT_RGB, PNG_CT_RGB_ALPHA,
         PNG_CT_GRAY_ALPHA in Hct; cbn [In] in Hct.
  destruct Hct as [<-|[<-|[<-|[<-|[]]]]]; destruct Hbd as [-> | ->]; reflexivity.
Qed.

(** [Chunk.v]'s [encode_do_filter] is the composition of the two functions
    [Filter.v] independently transcribed from the same [pngwutil.c] lines.
    Since the audit made [Chunk]'s copies aliases, this is [reflexivity] —
    which is exactly the point: there is now one definition. *)
Lemma encode_do_filter_is_filter_lane : forall ct bd w h,
  encode_do_filter ct bd w h = png_start_row_filters (png_ihdr_do_filter ct bd) w h.
Proof. reflexivity. Qed.

(** The container's CRC is the checksum lane's CRC is the braided loop the
    delivered binary runs, at every buffer alignment. *)
Lemma container_crc_is_binary_crc : forall crc align bs,
  bytes bs -> crc32_z_at crc align bs = crc32_bytes crc bs.
Proof. intros crc align bs H. now apply crc32_braid_eq. Qed.

(** The one place where [Filter.v]'s [smax] parameter earns its keep.

    [png_write_find_filter] instantiates [png_write_find_filter_at] at
    [PNG_SIZE_MAX = 2^64 - 1], the target's [(size_t)-1].  A differential
    checker extracted to OCaml cannot represent that (native [int] is 63
    bits) and must substitute a smaller sentinel; the lemma below says the
    substitution is EXACT, not an approximation, for every row this driver
    can form.

    [smax] is read at exactly two places ([pngwutil.c:2600-2604] and
    [:2570]): the overflow guard [smax / 128 <= row_bytes], and the initial
    [mins = smax - 256] used when the NONE candidate is not evaluated.  The
    guard agrees for any two sentinels above [128 * row_bytes], and the
    initial [mins] is not consulted at all when [PNG_FILTER_NONE] is in the
    filter set — which it always is here: bit 0x08 survives BOTH of
    [png_write_start_row]'s narrowing masks (0x1f and 0x2f), so
    [Z.land do_filter FB_NONE <> 0] on every encode. *)
Definition SMAX63 : Z := 4611686018427387903.   (* (1 lsl 62) - 1 *)

Lemma find_filter_smax_irrelevant :
  forall s1 s2 df bpp prev row,
    Z.of_nat (length row) < s1 / 128 -> Z.of_nat (length row) < s2 / 128 ->
    Z.land df FB_NONE <> 0 -> df <> FB_NONE ->
    png_write_find_filter_at s1 df bpp prev row
    = png_write_find_filter_at s2 df bpp prev row.
Proof.
  intros s1 s2 df bpp prev row H1 H2 Hn Hne.
  unfold png_write_find_filter_at; cbv zeta.
  rewrite (proj2 (Z.leb_gt _ _) H1), (proj2 (Z.leb_gt _ _) H2).
  cbn [negb].
  rewrite (proj2 (Z.eqb_neq _ _) Hn), (proj2 (Z.eqb_neq _ _) Hne).
  reflexivity.
Qed.

(** Hence, at the row sizes [encode_raw] reaches (at most
    [64 * 4 * 2 = 512] bytes), the 63-bit sentinel is the 64-bit one. *)
(* NB: the length bound is stated over [Z].  A [nat] literal this large is
   parsed as [Init.Nat.of_num_uint ...] (the abstract-large-number
   mechanism) and [lia] cannot see through it. *)
Corollary find_filter_smax63 : forall df bpp prev row,
  Z.of_nat (length row) <= 65536 -> Z.land df FB_NONE <> 0 -> df <> FB_NONE ->
  png_write_find_filter_at SMAX63 df bpp prev row
  = png_write_find_filter df bpp prev row.
Proof.
  intros df bpp prev row Hz Hn Hne.
  unfold png_write_find_filter.
  apply find_filter_smax_irrelevant; try assumption.
  - unfold SMAX63.
    change (4611686018427387903 / 128) with 36028797018963967. lia.
  - unfold PNG_SIZE_MAX.
    change (18446744073709551615 / 128) with 144115188075855871. lia.
Qed.

(** And the side condition really does hold on every encode: bit 0x08 is in
    both of [png_write_start_row]'s masks, so no narrowing can remove it. *)
Lemma start_row_keeps_none : forall ct bd w h,
  Z.land (start_row_do_filter (ihdr_do_filter ct bd) w h) FB_NONE <> 0.
Proof.
  intros ct bd w h.
  unfold start_row_do_filter, png_start_row_filters, ihdr_do_filter,
         png_ihdr_do_filter, FB_NONE, FB_ALL.
  destruct ((ct =? 3) || (bd <? 8)); cbn;
    destruct (h =? 1); destruct (w =? 1); cbn; discriminate.
Qed.

(** * §1  Rows

    [encode_raw] ([png_harness.c:264]) hands libpng
    [rows[y] = pix + y * rb], so the pixel buffer is exactly [h]
    consecutive [rb]-byte rows.  [rows_of] is that view; it is total, and a
    short [pix] simply yields short rows (which the length guards below
    reject before anything depends on it). *)

Fixpoint rows_of (n : nat) (rb : nat) (l : list Z) : list (list Z) :=
  match n with
  | O => []
  | S k => firstn rb l :: rows_of k rb (skipn rb l)
  end.

Lemma rows_of_length : forall n rb l, length (rows_of n rb l) = n.
Proof. induction n as [|n IH]; intros rb l; cbn; [reflexivity|now rewrite IH]. Qed.

(** * §2  The filter pass

    [png_write_row] ([pngwutil.c:2700-2770] via [png_write_find_filter]):
    for each row, pick a filter against the previous RAW row, emit the
    filter byte and the filtered bytes, then SWAP [row_buf] and [prev_row]
    ([pngwutil.c:2757-2765]) — so the next row's [prev] is this row's
    UNFILTERED bytes, not its filtered ones.  Row 0's [prev] is the
    [png_calloc]ed buffer, modelled by [[]] ([Filter.nthz_nil]). *)

Fixpoint filt_go (df bpp : Z) (prev : list Z) (rows : list (list Z)) : list Z :=
  match rows with
  | [] => []
  | r :: rs =>
      let fo := png_write_find_filter df bpp prev r in
      fst fo :: snd fo ++ filt_go df bpp r rs
  end.

(** The unfilter pass, [png_read_row] ([pngrutil.c:4130-4145]).  Same
    discipline in reverse: the decoded row becomes the next row's [prev].
    Fuel is the row count, read off [png_read_image]'s loop. *)
Fixpoint unfilt_go (n : nat) (bpp : Z) (rb : nat) (prev : list Z) (l : list Z)
  : list Z :=
  match n with
  | O => []
  | S k =>
      match l with
      | [] => []
      | f :: r =>
          let row := png_read_filter_row bpp f prev (firstn rb r) in
          row ++ unfilt_go k bpp rb row (skipn rb r)
      end
  end.

(** * §3  The deflate driver

    [png_compress_IDAT] ([pngwutil.c:930-1066]) is a refill loop: set
    [avail_out] to [PNG_ZBUF_SIZE], call [deflate], emit an IDAT and go
    round whenever the buffer filled exactly.  [Chunk.split_idat] already
    models the emission side (the cut is a pure length split), so what is
    left here is the pump.

    This is the loop [wp4d/streamcheck.py] validated: 434 reconstructed
    zlib streams from the delivered binary, byte-identical from byte 2
    onwards (bytes 0-1 are [optimize_cmf]'s, applied by
    [Chunk.encode_stream]). *)

Fixpoint defl_pump (fuel : nat) (chunk flush : Z) (s : DSt) : Z * DSt :=
  match fuel with
  | O => (-98, s)
  | S f =>
      let s0 := setD_strm (setZ_availout chunk (d_strm s)) s in
      match deflate flush s0 with
      | DfUnmodelled => (-99, s)
      | DfRet code s1 =>
          if Z.eqb (zs_availout (d_strm s1)) 0 then defl_pump f chunk flush s1
          else (code, s1)
      end
  end.

(** Every continuing trip emits [chunk] output bytes, and deflate's output
    for [n] input bytes is bounded by [n] plus five bytes per stored block
    plus the header and trailer, so [n + 64] trips of an 8192-byte buffer
    is an over-approximation by three orders of magnitude.  [None] rather
    than a wrong answer if it ever binds. *)
Definition defl_fuel (input : list Z) : nat := (Z.to_nat (zlen input) + 64)%nat.

(** [png_deflate_claim] + the pump + [Z_FINISH], i.e. the whole zlib stream
    the encoder produces BEFORE [optimize_cmf] rewrites its first two
    bytes.  [memLevel] is 8 and [method] is 8 on every call this driver
    makes ([pngwrite.c:538-548]); [level] is passed raw as
    [PNG_Z_DEFAULT_COMPRESSION] because [Chunk.defl_init2] performs the
    [-1 -> 6] substitution itself ([deflate.c:400]). *)
Definition png_zlib_stream (windowBits level strategy : Z) (input : list Z)
  : option (list Z) :=
  match defl_new level 8 windowBits 8 strategy with
  | None => None
  | Some s0 =>
      let s1 := setD_strm (setZ_in input (d_strm s0)) s0 in
      let r  := defl_pump (defl_fuel input) PNG_ZBUF_SIZE Z_FINISH s1 in
      if Z.eqb (fst r) Z_STREAM_END
      then Some (zs_out (d_strm (snd r)))
      else None
  end.

(** * §4  The inflate driver

    [png_read_IDAT_data] / [png_inflate] ([pngrutil.c:544-586]) is the
    mirror image: a fresh [avail_out] window per call, until
    [Z_STREAM_END], an error, or no progress.

    [inflateInit2(strm, 0)] is what libpng asks for ([pngrutil.c:415]), so
    [wrap = 5] and the window size comes from the stream's own CINFO
    nibble — exactly the byte [Chunk.optimize_cmf] rewrote on the way out.
    That round trip through the header byte is the reason the two lanes
    have to meet here and not earlier. *)

(** A fresh [z_stream].  [inflateReset2] overwrites every field the model
    reads. *)
Definition z_fresh : Strm :=
  {| z_tin := 0; z_tout := 0; z_adler := 0; z_dtype := 0; z_msg := 0 |}.

(** The bytes [ZALLOC] leaves in a fresh [inflate_state] are unspecified
    ([inflate.c:190]; [Inflate.v]'s deviation 8).  Zeros are as good as any
    other choice because [inflateReset2]/[inflateResetKeep] and the mode
    machine write every field the model reads before it is read — the
    empirical form of that claim is the 28 716 boundary records
    [harness/infcheck.py] agreed on. *)
Definition state_fresh : IState :=
  {| s_hdr := {| h_mode := M_HEAD; h_last := 0; h_wrap := 0; h_havedict := 0;
                 h_flags := 0; h_dmax := 0; h_check := 0; h_total := 0;
                 h_head := 0 |};
     s_win := {| w_wbits := 0; w_wsize := 0; w_whave := 0; w_wnext := 0;
                 w_alloc := false; w_win := zzero |};
     s_cur := {| u_length := 0; u_offset := 0; u_extra := 0; u_back := 0;
                 u_was := 0 |};
     s_tab := {| t_lencode := TRcodes 0; t_distcode := TRcodes 0;
                 t_lenbits := 0; t_distbits := 0; t_next := 0;
                 t_codes := tnone; t_sane := 0 |};
     s_bld := {| b_ncode := 0; b_nlen := 0; b_ndist := 0; b_have := 0;
                 b_lens := zzero; b_work := zzero |};
     s_hold := 0; s_bits := 0 |}.

(** One [inflate] call over a list-shaped input and a fresh output window.
    Returns the code, how many input bytes were consumed, the two updated
    states, and the produced bytes. *)
Definition inf_call (s : IState) (z : Strm) (inb : list Z) (avail_out : Z)
  : option (Z * Z * IState * Strm * list Z) :=
  match inflate_model {| g_st := s; g_state_null := false; g_z := z;
                         g_inbuf := zlist inb; g_next_in := 0;
                         g_avail_in := zlen inb; g_in_null := false;
                         g_outbuf := zzero; g_next_out := 0;
                         g_avail_out := avail_out; g_out_null := false;
                         g_flush := Z_NO_FLUSH; g_walloc := true;
                         g_wfresh := zzero |} with
  | None => None
  | Some r =>
      let q := r_q r in
      Some (r_ret r, zlen inb - br_have (q_br q),
            q_st q, q_z q, ob_slice (q_ob q) 0 (o_put (q_ob q)))
  end.

Fixpoint inf_pump (f : nat) (s : IState) (z : Strm) (inp : list Z)
                  (chunk : Z) (acc : list Z) : option (Z * list Z) :=
  match f with
  | O => None
  | S k =>
      match inf_call s z inp chunk with
      | None => None
      | Some (ret, used, s', z', out) =>
          let acc' := acc ++ out in
          if Z.eqb ret Z_STREAM_END || Z.ltb ret 0 then Some (ret, acc')
          else if Z.eqb used 0 && Nat.eqb (length out) 0 then Some (ret, acc')
          else inf_pump k s' z' (skipn (Z.to_nat used) inp) chunk acc'
      end
  end.

(** Every continuing trip either consumes an input byte or produces an
    output byte, so [8 * |input| + 64] trips is an over-approximation. *)
Definition inf_fuel (inp : list Z) : nat := (8 * Z.to_nat (zlen inp) + 64)%nat.

(** The whole decompression, as [png_read_IDAT_data] performs it.  [None]
    unless the stream ends cleanly at [Z_STREAM_END] — which is what the
    read side requires, since [decode_raw] does not set
    [png_set_crc_action] and a zlib error is a [png_error]
    ([pngrutil.c:576-583]).

    [chunk] is [PNG_INFLATE_BUF_SIZE]; the produced bytes do not depend on
    it (it only splits the calls), but it is the value libpng uses. *)
Definition png_inflate_stream (inp : list Z) : option (list Z) :=
  match inflateInit2 z_fresh state_fresh 0 with
  | None => None
  | Some (z, s) =>
      match inf_pump (inf_fuel inp) s z inp PNG_INFLATE_BUF_SIZE [] with
      | None => None
      | Some (ret, out) => if Z.eqb ret Z_STREAM_END then Some out else None
      end
  end.

(** * §5  [encode_raw] and [decode_raw] *)

(** [png_harness.c:246-268].  [None] is the C's [return 0]: a
    [png_create_*] failure or a [png_error] caught by [:253]'s [setjmp]
    (the only reachable one on this path is [png_write_IHDR]'s
    colour-type/bit-depth rejection — "rows oom" and "sink oom" are
    allocation refusals, which E2 puts outside this function). *)
Definition enc_raw (pix : list Z) (s : Shape) : option (list Z) :=
  match png_write_IHDR (sh_w s) (sh_h s) (sh_bd s) (sh_ct s)
                       PNG_COMPRESSION_TYPE_BASE PNG_FILTER_TYPE_BASE
                       PNG_INTERLACE_NONE with
  | None => None
  | Some (hdr, _) =>
      (* [png_write_start_row] ([pngwutil.c:1929-1943]) narrows the filter
         set BEFORE [png_deflate_claim] reads it. *)
      let df   := start_row_do_filter (wh_do_filter hdr) (sh_w s) (sh_h s) in
      (* [pngwutil.c:1919] [png_ptr->bpp = (pixel_depth + 7) >> 3]. *)
      let bpp  := (wh_pixel_depth hdr + 7) / 8 in
      let rows := rows_of (Z.to_nat (sh_h s)) (Z.to_nat (wh_rowbytes hdr)) pix in
      let ds   := wr_image_size hdr in
      let wb   := deflate_claim_window_bits 15 ds in
      let st   := idat_strategy false PNG_Z_DEFAULT_STRATEGY df in
      match png_zlib_stream wb PNG_Z_DEFAULT_COMPRESSION st
                            (filt_go df bpp [] rows) with
      | None => None
      | Some zout =>
          encode_stream (sh_w s) (sh_h s) (sh_bd s) (sh_ct s)
                        PNG_INTERLACE_NONE zout
      end
  end.

(** The IHDR payload of a parsed chunk list, as [png_get_IHDR] would report
    it: [(w, h, bd, ct, comp, filt, interlace)].  [None] unless the first
    chunk really is a 13-byte IHDR. *)
Definition read_ihdr (cs : list PChunk) : option (Z * Z * Z * Z * Z * Z * Z) :=
  match cs with
  | [] => None
  | c :: _ =>
      if negb (zlist_beq (pc_type c) ty_IHDR) then None
      else if negb (Nat.eqb (length (pc_data c)) 13) then None
      else
        let d := pc_data c in
        Some (be32_at d, be32_at (skipn 4 d),
              nthz d 8, nthz d 9, nthz d 10, nthz d 11, nthz d 12)
  end.

(** Every chunk's CRC checks out.  [decode_raw] does NOT call
    [png_set_crc_action], so [png_ptr->flags] is 0, [need_crc] is 1 for
    every critical chunk, and a mismatch is a hard [png_chunk_error]
    ([pngrutil.c:230-283]) — i.e. a [longjmp] out, i.e. [return 0]. *)
Definition all_crcs_ok (cs : list PChunk) : bool := forallb chunk_crc_ok cs.

(** [png_harness.c:273-304].  [Some pix] is [return 1]; [None] is the clean
    [return 0] — the IHDR/rowbytes mismatch at [:288-292], or a
    [png_error] that is not an allocation failure. *)
Definition dec_raw (enc : list Z) (s : Shape) : option (list Z) :=
  match parse_png enc with
  | None => None
  | Some cs =>
      if negb (all_crcs_ok cs) then None else
      match read_ihdr cs with
      | None => None
      | Some (w, h, bd, ct, comp, filt, il) =>
          (* [:289] [png_get_IHDR] fails for an out-of-range IHDR; [:290]
             is the four-way shape test. *)
          if negb ((w =? sh_w s) && (h =? sh_h s)
                   && (bd =? sh_bd s) && (ct =? sh_ct s)
                   && (comp =? 0) && (filt =? 0)
                   && (il =? PNG_INTERLACE_NONE)) then None
          else match ihdr_channels ct bd with
          | None => None
          | Some ch =>
              let pd  := bd * ch in
              let rb  := png_rowbytes pd w in
              let bpp := (pd + 7) / 8 in
              (* [:292] [if (rb * h != outsz) goto done]. *)
              if negb (rb * h =? sh_total s) then None
              else match png_inflate_stream (idat_stream cs) with
              | None => None
              | Some raw =>
                  (* every row is one filter byte plus [rb] data bytes *)
                  if negb (zlen raw =? h * (1 + rb)) then None
                  else Some (unfilt_go (Z.to_nat h) bpp (Z.to_nat rb) [] raw)
              end
          end
      end
  end.

(** * §6  [cd_front] — [roundtrip_decode_encode]'s front end

    [png_harness.c:360-400].  P3 decodes an ARBITRARY input PNG to
    canonical RGBA8 and round-trips those pixels.  Between [png_read_info]
    ([:373]) and [png_read_image] ([:393]) it installs five
    transformations and then asks libpng what shape the rows now have:

<<
      png_read_info(p, info);                            /* :373 */
      if (!png_get_IHDR(p, info, &w, &h, ...)) goto done;/* :375 */
      if (!w || !h || h > 100000000u / w) goto done;     /* :376 */
      png_set_expand(p);                    /* :378   pngrtran.c: 868 */
      png_set_scale_16(p);                  /* :379   pngrtran.c: 183 */
      png_set_gray_to_rgb(p);               /* :380   pngrtran.c: 951 */
      png_set_add_alpha(p, 0xffff, PNG_FILLER_AFTER);
                                            /* :381   pngtrans.c: 205 */
      png_set_interlace_handling(p);        /* :382   pngtrans.c:  99 */
      png_read_update_info(p, info);        /* :383   pngread.c:1116  */
      size_t rb = png_get_rowbytes(p, info);             /* :385 */
      if (rb != (size_t)w * 4) goto done;                /* :386 */
      ... png_read_image(p, rows);                       /* :393 */
      assert_roundtrip(p1, w, h, 8, PNG_COLOR_TYPE_RGB_ALPHA, 0, 1);  /* :395 */
>>

    WHAT THIS SECTION IS, AND WHAT IT DELIBERATELY IS NOT.  It is NOT a
    transcription of [pngrtran.c]'s PIXEL transforms ([png_do_expand],
    [png_do_scale_16_to_8], [png_do_gray_to_rgb], [png_do_read_filler]),
    nor of read-side Adam7 de-interlacing, and it does not need to be.
    [Harness.codec_ed_id] — the one obligation the round-trip arm leaves
    open — is universally quantified over the pixel buffer, and
    [Harness.codec_front_wf] — the one obligation [cd_front] owes — asks
    only for [RS_de s] and [length pix = sh_total s].  So the only thing
    [cd_front] has to get right is the SHAPE and the BUFFER LENGTH that
    [png_read_update_info] reports.  That is [png_read_transform_info]
    ([pngrtran.c:1936-2130]): pure arithmetic on the IHDR fields plus
    [num_trans], transcribed in full in §6.4.

    THE RESULT, in one line: for every IHDR that [png_check_IHDR] accepts,
    the post-transformation row is 8-bit RGBA — [color_type = 6],
    [bit_depth = 8], [channels = 4], [pixel_depth = 32],
    [rowbytes = 4 * width] — INDEPENDENT of the input colour type, bit
    depth, tRNS presence and interlace method ([p3_post_is_rgba8]).  Three
    consequences, all recorded below: [:386]'s [rb != 4*w] guard is DEAD
    ([front_rowbytes_guard_dead]); the shape [cd_front] must report is
    always [mkShape w h 8 6] at the IHDR's OWN [w] and [h]; and only Adam7
    GEOMETRY can matter, never Adam7 round-trip, because
    [png_set_interlace_handling] makes [png_read_image] hand back the full
    de-interlaced [w * h] image ([adam7_partitions_image]).  That is scope
    decision D9, discharged rather than assumed.

    WHAT THIS REPLACED.  The previous [front_raw] returned [Some] only on
    the sub-domain where all five transformations are provably the
    identity — non-interlaced 8-bit RGBA — and [None] everywhere else.
    That was an UNDER-approximation of [rt_viol], the opposite direction
    from the allocation-refusal argument in [Harness.v]'s header: on a real
    PNG the binary ran a comparison where the model declined, so a
    machine-level walk met an unprovable obligation.  The domain below is
    an OVER-approximation, which is the direction both routes need
    ([Harness.rt_viol_false] holds for any [codec_wf] codec, so a [Some]
    the binary would not have produced still collapses the arm).

    WHERE THE OVER-APPROXIMATION LIES, exactly.  [front_shape] returns
    [Some] as soon as the signature, the IHDR chunk and [:376]'s area
    guard are satisfied.  It therefore ALSO accepts inputs the binary
    rejects LATER, in four places this file does not model:

      - a colour-type-3 image with no PLTE before the first IDAT
        ([pngread.c] [png_read_info]'s IDAT arm, "Missing PLTE before
        IDAT");
      - [png_read_update_info] -> [png_read_start_row]'s two big-row-buffer
        allocations, which [limited_malloc] refuses above
        [PNG_USER_CHUNK_MALLOC_MAX = 8000000] bytes (reachable only at
        [max_pixel_depth = 64] and [width >= 999993]);
      - anything [png_read_image] rejects: a broken zlib stream, too few
        or too many decompressed bytes, a bad adaptive filter byte;
      - a truncated or malformed chunk AFTER the IHDR.

    All four are the safe direction.  Nothing below declines an input the
    binary accepts: measured, 357/357 (see the validation note at the end
    of the section).

    WHAT IS FAITHFULLY MODELLED AND WAS NOT BEFORE: [png_check_IHDR]'s
    twelve rejections including libpng's [PNG_USER_WIDTH_MAX] /
    [PNG_USER_HEIGHT_MAX] of 1000000 (which fire long before [:376]'s area
    guard); the fact that P3 never calls [png_read_end], so a file with NO
    IEND AT ALL still decodes (which is why this section does NOT go
    through [Chunk.parse_png], whose [read_chunks] stops at IEND and fails
    without one); [png_set_crc_action(PNG_CRC_QUIET_USE)], so a wrong CRC
    on any chunk is ignored (which is why there is no [all_crcs_ok] here
    either); and leading UNKNOWN ANCILLARY chunks before the IHDR, which
    [png_handle_unknown] skips silently while all nineteen of libpng's own
    pre-IDAT handlers [png_chunk_error] with "missing IHDR". *)

(** ** §6.1  Reading the IHDR the way [png_read_info] does

    [decode_raw] can afford [Chunk.parse_png]: it only ever sees streams
    this encoder produced, which are signature + IHDR + IDAT* + IEND with
    correct CRCs.  P3 cannot: its input is arbitrary fuzz bytes, it sets
    [PNG_CRC_QUIET_USE], and it never calls [png_read_end].  So the front
    end gets its own reader, which stops the moment it has the IHDR. *)

(** [pngrutil.c:96-107].  [png_get_uint_31] is [png_get_uint_32] plus a
    [png_error] when the top bit is set.  The four bytes are a [png_byte
    buf[4]] in the C; the model's [list Z] carries no byte hypothesis, so
    the transcription applies [Base.u8] at the cast — the tree's rule for
    every C cast.  On a genuine byte list this is [Chunk.get_uint_31]
    ([rd_uint_31_bytes]). *)
Definition rd_uint_31 (l : list Z) : option Z :=
  let v := be32_of (u8 (nthz l 0)) (u8 (nthz l 1))
                   (u8 (nthz l 2)) (u8 (nthz l 3)) in
  if PNG_UINT_31_MAX <? v then None else Some v.

Lemma u8_range : forall x, 0 <= u8 x <= 255.
Proof. intro x. unfold u8. pose proof (Z.mod_pos_bound x 256). lia. Qed.

Lemma rd_uint_31_range :
  forall l v, rd_uint_31 l = Some v -> 0 <= v <= PNG_UINT_31_MAX.
Proof.
  intros l v H. unfold rd_uint_31 in H.
  destruct (PNG_UINT_31_MAX <? _) eqn:E; [discriminate|].
  injection H as <-. rewrite Z.ltb_ge in E. split; [|exact E].
  unfold be32_of.
  pose proof (u8_range (nthz l 0)); pose proof (u8_range (nthz l 1));
  pose proof (u8_range (nthz l 2)); pose proof (u8_range (nthz l 3)).
  lia.
Qed.

Lemma rd_uint_31_bytes : forall l,
  (forall i, (i < 4)%nat -> 0 <= nth i l 0 < 256) ->
  rd_uint_31 l = get_uint_31 l.
Proof.
  intros l H. unfold rd_uint_31, get_uint_31, be32_at, be32_of, nthz, u8.
  cbn [Z.ltb Z.to_nat].
  rewrite !Zmod_small by (apply H; lia). reflexivity.
Qed.

(** [pngpriv.h:626-627].  [PNG_CHUNK_ANCILLARY] is bit 5 of the first type
    byte, i.e. "the first letter is lower case". *)
Definition chunk_ancillary (ty : list Z) : bool :=
  negb (Z.land (u8 (nthz ty 0)) 32 =? 0).

(** The eighteen ancillary chunk types [png_read_info] dispatches by name
    ([pngread.c:790-880]).  Every one of their handlers opens with
    [if ((png_ptr->mode & PNG_HAVE_IHDR) == 0) png_chunk_error(png_ptr,
    "missing IHDR")] — nineteen occurrences in [pngrutil.c] counting
    [png_handle_PLTE] — so none of them can appear BEFORE the IHDR.  Only
    a chunk that falls through to [png_handle_unknown] can, and only if it
    is ancillary ([pngrutil.c]'s closing "unhandled critical chunk"). *)
Definition known_ancillary : list (list Z) :=
  [ [98;75;71;68]   (* bKGD *) ; [99;72;82;77]   (* cHRM *)
  ; [101;88;73;102] (* eXIf *) ; [103;65;77;65]  (* gAMA *)
  ; [104;73;83;84]  (* hIST *) ; [111;70;70;115] (* oFFs *)
  ; [112;67;65;76]  (* pCAL *) ; [115;67;65;76]  (* sCAL *)
  ; [112;72;89;115] (* pHYs *) ; [115;66;73;84]  (* sBIT *)
  ; [115;82;71;66]  (* sRGB *) ; [105;67;67;80]  (* iCCP *)
  ; [115;80;76;84]  (* sPLT *) ; [116;69;88;116] (* tEXt *)
  ; [116;73;77;69]  (* tIME *) ; [116;82;78;83]  (* tRNS *)
  ; [122;84;88;116] (* zTXt *) ; [105;84;88;116] (* iTXt *) ].

Definition is_known_ancillary (ty : list Z) : bool :=
  existsb (zlist_beq ty) known_ancillary.

(** NOT a guard, and this cost a differential round to establish.
    [png_read_chunk_header] ends with [png_check_chunk_length]
    ([pngrutil.c:3152-3189]), which for every chunk but IDAT compares the
    length against [png_ptr->user_chunk_malloc_max] — seeded from
    [PNG_USER_CHUNK_MALLOC_MAX = 8000000] in [pnglibconf.h] — and, when it
    is exceeded, calls **[png_benign_error]**, not [png_chunk_error]
    ([pngrutil.c:3188]).  [png_create_read_struct_2] sets
    [PNG_FLAG_BENIGN_ERRORS_WARN] ([pngread.c:61]), so on a READ struct a
    benign error is a [png_chunk_warning] and the parse CONTINUES
    ([pngerror.c:362-375]).  The delivered binary confirms it: a leading
    unknown ancillary chunk declaring 8000001 bytes of payload, with the
    payload actually present, decodes to completion and only warns
    ("chunk data is too large").  A guard here would have DECLINED an input
    the binary accepts — the one direction that is not allowed. *)

(** One leading chunk that [png_handle_unknown] skips: header (8 bytes) +
    payload + CRC (4 bytes), all of which [png_crc_finish] reads, so a
    truncation anywhere in them is a "read past end" [png_error].  [None]
    means "this chunk is not skippable" — either it is the IHDR, or it is
    something that errors, and either way the scan stops here. *)
Definition skip_unknown (l : list Z) : option (list Z) :=
  if Nat.ltb (length l) 8 then None
  else match rd_uint_31 l with
       | None => None
       | Some len =>
           let ty := firstn 4 (skipn 4 l) in
           if negb (chunk_name_ok ty) then None
           else if negb (chunk_ancillary ty) then None
           else if is_known_ancillary ty then None
           else
             let r := skipn 8 l in
             if Nat.ltb (length r) (Z.to_nat len + 4) then None
             else Some (skipn (Z.to_nat len + 4) r)
       end.

(** Fuel is the byte length; every trip consumes at least 12 bytes, so it
    never binds — the same discipline as [Chunk.read_chunks]. *)
Fixpoint pre_ihdr (fuel : nat) (l : list Z) : list Z :=
  match fuel with
  | O => l
  | S f => match skip_unknown l with
           | None => l
           | Some r => pre_ihdr f r
           end
  end.

(** [pngrutil.c:837-908] [png_handle_IHDR], reached from [pngread.c]'s
    [png_read_info] loop.  [png_read_chunk_header] reads eight bytes and
    runs [png_get_uint_31] over the length and [png_check_chunk_name] over
    the type; [png_handle_IHDR] then demands [length == 13]
    ([pngrutil.c:849]), [png_crc_read]s the thirteen payload bytes and
    [png_crc_finish]es over the four CRC bytes.  So 17 bytes must follow
    the header or the read is short.  P3 hands libpng [data + 8]
    ([png_harness.c:370]) with [png_set_sig_bytes(p, 8)] ([:372]), so the
    chunk stream starts at offset 8 of the fuzz input. *)
Definition rd_ihdr (d : list Z) : option (Z * Z * Z * Z * Z * Z * Z) :=
  let l := pre_ihdr (length d) (skipn 8 d) in
  if Nat.ltb (length l) 8 then None
  else match rd_uint_31 l with
       | None => None
       | Some len =>
           if negb (zlist_beq (firstn 4 (skipn 4 l)) ty_IHDR) then None
           else if negb (len =? 13) then None
           else
             let p := skipn 8 l in
             if Nat.ltb (length p) 17 then None
             else match rd_uint_31 p, rd_uint_31 (skipn 4 p) with
                  | Some w, Some h =>
                      Some (w, h, u8 (nthz p 8), u8 (nthz p 9),
                            u8 (nthz p 10), u8 (nthz p 11), u8 (nthz p 12))
                  | _, _ => None
                  end
       end.

Lemma rd_ihdr_range : forall d w h bd ct comp filt il,
  rd_ihdr d = Some (w, h, bd, ct, comp, filt, il) ->
  0 <= w <= PNG_UINT_31_MAX /\ 0 <= h <= PNG_UINT_31_MAX.
Proof.
  intros d w h bd ct comp filt il H. unfold rd_ihdr in H.
  destruct (Nat.ltb _ 8); [discriminate|].
  destruct (rd_uint_31 _) as [len|]; [|discriminate].
  destruct (negb (zlist_beq _ _)); [discriminate|].
  destruct (negb (len =? 13)); [discriminate|].
  destruct (Nat.ltb _ 17); [discriminate|].
  destruct (rd_uint_31 (skipn 8 _)) as [w0|] eqn:Ew; [|discriminate].
  destruct (rd_uint_31 (skipn 4 _)) as [h0|] eqn:Eh; [|discriminate].
  injection H as <- <- _ _ _ _ _.
  split; [eapply rd_uint_31_range, Ew | eapply rd_uint_31_range, Eh].
Qed.

(** ** §6.2  [png_check_IHDR] — [png.c:2515-2668]

    Called twice on this path: from [png_set_IHDR] ([pngset.c:264], at the
    end of [png_handle_IHDR]) and again from [png_get_IHDR]
    ([pngget.c:872], i.e. [png_harness.c:375]).  Each failing test raises a
    [png_warning] and sets [error]; a single [png_error "Invalid IHDR
    data"] at the end turns any of them into a [longjmp].  The harness's
    warning hook does not longjmp, so only [error] matters. *)

Definition PNG_COLOR_MASK_PALETTE : Z := 1.   (* png.h:662 *)
Definition PNG_COLOR_MASK_COLOR   : Z := 2.   (* png.h:663 *)
Definition PNG_COLOR_MASK_ALPHA   : Z := 4.   (* png.h:664 *)
Definition PNG_INTERLACE_LAST     : Z := 2.   (* png.h:688 *)

(** [png.c:2540-2547].  The C is
<<
      if (((width + 7) & ~(png_alloc_size_t)7) >
          ((((PNG_SIZE_MAX - 48) - 1) / 8) - 1))
>>
    [& ~(png_alloc_size_t)7] clears the low three bits of a nonnegative
    value, i.e. it is [8 * ((width + 7) / 8)]; the transcription uses the
    division form for the same reason [Chunk.be32] uses division for [>>]
    — it keeps the arithmetic inside [lia]'s fragment.  [width] here is
    [png_get_uint_31]'s output, so [0 <= width < 2^31] and the rewriting is
    exact. *)
Definition png_row_size_limit : Z := (PNG_SIZE_MAX - 48 - 1) / 8 - 1.

Definition width_arch_ok (w : Z) : bool :=
  negb (png_row_size_limit <? 8 * ((w + 7) / 8)).

(** On a 64-bit target the limit is 2305843009213693944, so this test can
    never fire below [PNG_USER_WIDTH_MAX]: it is DEAD. *)
Lemma width_arch_ok_dead :
  forall w, 0 <= w <= PNG_USER_WIDTH_MAX -> width_arch_ok w = true.
Proof.
  intros w Hw. unfold PNG_USER_WIDTH_MAX in Hw.
  unfold width_arch_ok. apply negb_true_iff, Z.ltb_ge.
  assert (Hlim : png_row_size_limit = 2305843009213693944)
    by (vm_compute; reflexivity).
  rewrite Hlim.
  pose proof (Z.mul_div_le (w + 7) 8 ltac:(lia)) as Hle. lia.
Qed.

(** The colour-type x bit-depth part, kept separate because §6.4's theorem
    is exactly a case analysis over it ([png.c:2595-2615]). *)
Definition ihdr_ct_bd_ok (ct bd : Z) : bool :=
  (* :2595 invalid bit depth *)
  ((bd =? 1) || (bd =? 2) || (bd =? 4) || (bd =? 8) || (bd =? 16))
  (* :2602 invalid colour type *)
  && negb ((ct <? 0) || (ct =? 1) || (ct =? 5) || (6 <? ct))
  (* :2609 invalid colour-type/bit-depth combination *)
  && negb (((ct =? CT_PALETTE) && (8 <? bd))
           || (((ct =? CT_RGB) || (ct =? CT_GRAY_ALPHA) || (ct =? CT_RGB_ALPHA))
               && (bd <? 8))).

Definition png_check_IHDR_ok (w h bd ct il comp filt : Z) : bool :=
  (* :2521 / :2527 / :2540 / :2565 — the four width tests *)
  negb (w =? 0)
  && negb (PNG_UINT_31_MAX <? w)
  && width_arch_ok w
  && negb (PNG_USER_WIDTH_MAX <? w)
  (* :2573 / :2579 / :2589 — the three height tests *)
  && negb (h =? 0)
  && negb (PNG_UINT_31_MAX <? h)
  && negb (PNG_USER_HEIGHT_MAX <? h)
  (* :2595-2615 *)
  && ihdr_ct_bd_ok ct bd
  (* :2616 unknown interlace method *)
  && (il <? PNG_INTERLACE_LAST)
  (* :2622 unknown compression method *)
  && (comp =? PNG_COMPRESSION_TYPE_BASE)
  (* :2643-2661.  [PNG_MNG_FEATURES_SUPPORTED] IS defined in this build's
     [pnglibconf.h], so the MNG arm is the live one; but
     [mng_features_permitted] is 0 (the harness never calls
     [png_permit_mng_features]), so its inner condition is false and any
     [filter_type != 0] still sets [error].  Same outcome as the non-MNG
     arm at :2665. *)
  && (filt =? PNG_FILTER_TYPE_BASE).

Lemma png_check_IHDR_ct_bd :
  forall w h bd ct il comp filt,
    png_check_IHDR_ok w h bd ct il comp filt = true -> ihdr_ct_bd_ok ct bd = true.
Proof.
  intros w h bd ct il comp filt H. unfold png_check_IHDR_ok in H.
  now repeat (apply andb_prop in H as [H ?]).
Qed.

Lemma png_check_IHDR_wh :
  forall w h bd ct il comp filt,
    png_check_IHDR_ok w h bd ct il comp filt = true -> w <> 0 /\ h <> 0.
Proof.
  intros w h bd ct il comp filt H. unfold png_check_IHDR_ok in H.
  repeat (apply andb_prop in H as [H ?]).
  repeat match goal with
         | X : negb (_ =? 0) = true |- _ =>
             apply negb_true_iff, Z.eqb_neq in X
         end.
  split; assumption.
Qed.

(** ** §6.3  What the five setters put in [png_ptr->transformations]

    [pngpriv.h:660-700].  Every one of the five is called before any row
    is initialised, so [png_rtran_ok] ([pngrtran.c:41-60]) lets them all
    through. *)
Definition PNG_TR_INTERLACE     : Z := 2.          (* pngpriv.h:668 0x0002 *)
Definition PNG_TR_EXPAND        : Z := 4096.       (* pngpriv.h:679 0x1000 *)
Definition PNG_TR_GRAY_TO_RGB   : Z := 16384.      (* pngpriv.h:681 0x4000 *)
Definition PNG_TR_FILLER        : Z := 32768.      (* pngpriv.h:682 0x8000 *)
Definition PNG_TR_ADD_ALPHA     : Z := 16777216.   (* pngpriv.h:692 0x1000000 *)
Definition PNG_TR_EXPAND_tRNS   : Z := 33554432.   (* pngpriv.h:693 0x2000000 *)
Definition PNG_TR_SCALE_16_TO_8 : Z := 67108864.   (* pngpriv.h:694 0x4000000 *)

(** [pngrtran.c:868-878] sets [EXPAND | EXPAND_tRNS]; [:183-192] sets
    [SCALE_16_TO_8]; [:951-963] calls [png_set_expand_gray_1_2_4_to_8]
    (another [EXPAND]) and sets [GRAY_TO_RGB]; [pngtrans.c:120-200]
    [png_set_filler] sets [FILLER] (and [PNG_FLAG_FILLER_AFTER], a
    [flags] bit, not a transformation) and [:205-218] [png_set_add_alpha]
    then adds [ADD_ALPHA]; [pngtrans.c:99-110]
    [png_set_interlace_handling] sets [INTERLACE] only when
    [png_ptr->interlaced != 0], and returns the number of passes. *)
Definition p3_transformations (interlaced : Z) : Z :=
  Z.lor (if interlaced =? 0 then 0 else PNG_TR_INTERLACE)
    (Z.lor PNG_TR_EXPAND (Z.lor PNG_TR_EXPAND_tRNS
      (Z.lor PNG_TR_SCALE_16_TO_8 (Z.lor PNG_TR_GRAY_TO_RGB
        (Z.lor PNG_TR_FILLER PNG_TR_ADD_ALPHA))))).

(** [pngtrans.c:99-110]. *)
Definition png_set_interlace_handling_ret (interlaced : Z) : Z :=
  if interlaced =? 0 then 1 else 7.

(** Pinned against the DELIVERED binary: [png_ptr->transformations] read
    out of the live [png_struct] at the return of [png_read_update_info]
    is 0x700D000 on all 327 non-interlaced records that got that far and
    0x700D002 on all 127 interlaced ones — no other value occurs.  See the
    validation note at the end of this section. *)
Example p3_transformations_pinned :
  (p3_transformations 0, p3_transformations 1) = (117493760, 117493762).
Proof. vm_compute. reflexivity. Qed.

(** ** §6.4  [png_read_transform_info] — [pngrtran.c:1936-2130]

    [png_read_update_info] ([pngread.c:1116-1140]) calls
    [png_read_start_row] and then this, which is the function that
    computes the [info_ptr] fields [png_get_rowbytes] reports.  Only the
    arms whose transformation bit P3 actually sets can fire; the others
    are transcribed as the identity with their C line and the reason.

    Order matters and is preserved: EXPAND, then the [bit_depth == 16]
    scale, then GRAY_TO_RGB, then the channel count, then the alpha bump,
    then FILLER. *)

Record PostInfo : Set := mkPostInfo {
  pi_width       : Z;
  pi_height      : Z;
  pi_bit_depth   : Z;
  pi_color_type  : Z;
  pi_channels    : Z;
  pi_pixel_depth : Z;
  pi_rowbytes    : Z
}.

(** [pngrtran.c:1940-1972], the [PNG_EXPAND] arm.  Returns the new
    [(color_type, bit_depth)]; [num_trans] is zeroed in both branches.
    The palette branch also [png_error]s when [png_ptr->palette == NULL]
    ([:1957]) — that is the "Missing PLTE before IDAT" case, which
    [png_read_info] has already rejected before this runs. *)
Definition rti_expand (ct bd nt : Z) : Z * Z :=
  if ct =? CT_PALETTE
  then ((if 0 <? nt then CT_RGB_ALPHA else CT_RGB), 8)
  else ((if negb (nt =? 0) then Z.lor ct PNG_COLOR_MASK_ALPHA else ct),
        (if bd <? 8 then 8 else bd)).

(** [pngrtran.c:1996-2000].  [PNG_READ_16BIT_SUPPORTED] and
    [PNG_READ_SCALE_16_TO_8_SUPPORTED] are both on in this build, and
    [PNG_SCALE_16_TO_8] is set, so the scale arm fires first and the
    [PNG_16_TO_8] "strip" arm at [:2003-2006] is never reached.  For the
    SHAPE the two are indistinguishable anyway — they differ only in the
    sample arithmetic — but the distinction is real and is recorded here
    because [png_set_strip_16] is NOT what the harness calls. *)
Definition rti_scale16 (bd : Z) : Z := if bd =? 16 then 8 else bd.

(** [pngrtran.c:2033-2036]. *)
Definition rti_gray_to_rgb (ct : Z) : Z := Z.lor ct PNG_COLOR_MASK_COLOR.

(** [pngrtran.c:2070-2077].  NB the palette test comes FIRST: colour type
    3 is [PALETTE|COLOR], so testing [& PNG_COLOR_MASK_COLOR] first would
    give it 3 channels. *)
Definition rti_base_channels (ct : Z) : Z :=
  if ct =? CT_PALETTE then 1
  else if negb (Z.land ct PNG_COLOR_MASK_COLOR =? 0) then 3
  else 1.

(** [pngrtran.c:2087]. *)
Definition rti_alpha_bump (ct ch : Z) : Z :=
  if negb (Z.land ct PNG_COLOR_MASK_ALPHA =? 0) then ch + 1 else ch.

(** [pngrtran.c:2092-2101].  [PNG_FILLER] is set and [PNG_ADD_ALPHA] with
    it, so the colour type gains its alpha bit as well as a channel. *)
Definition rti_filler (ct ch : Z) : Z * Z :=
  if (ct =? CT_RGB) || (ct =? CT_GRAY)
  then (Z.lor ct PNG_COLOR_MASK_ALPHA, ch + 1)
  else (ct, ch).

(** BUG-FOR-BUG NOTE, and a dead disjunct.  [pngrtran.c:2093-2095] tests
    [color_type == PNG_COLOR_TYPE_RGB || color_type == PNG_COLOR_TYPE_GRAY],
    but [PNG_GRAY_TO_RGB] has already set the COLOR bit two arms earlier, so
    on THIS path the GRAY disjunct can never fire.  It is transcribed
    because it is what the C says, and its deadness is recorded rather than
    assumed -- a differential run cannot see the difference, so only a proof
    can. *)
Lemma rti_gray_to_rgb_not_gray : forall ct, rti_gray_to_rgb ct <> CT_GRAY.
Proof.
  intros ct H. unfold rti_gray_to_rgb, CT_GRAY, PNG_COLOR_MASK_COLOR in H.
  pose proof (Z.lor_spec ct 2 1) as B. rewrite H in B.
  change (Z.testbit 0 1) with false in B.
  change (Z.testbit 2 1) with true in B.
  rewrite orb_true_r in B. discriminate.
Qed.

Lemma rti_filler_gray_dead : forall ct ch,
  rti_filler (rti_gray_to_rgb ct) ch
  = (if rti_gray_to_rgb ct =? CT_RGB
     then (Z.lor (rti_gray_to_rgb ct) PNG_COLOR_MASK_ALPHA, ch + 1)
     else (rti_gray_to_rgb ct, ch)).
Proof.
  intros ct ch. unfold rti_filler.
  rewrite (proj2 (Z.eqb_neq _ _) (rti_gray_to_rgb_not_gray ct)), orb_false_r.
  reflexivity.
Qed.

(** The composition, [pngrtran.c:2117-2121] for the last two lines.
    NOT modelled because their transformation bit is never set on this
    path: COMPOSE ([:1980]), the gamma copy ([:1994], not a shape),
    RGB_TO_GRAY ([:2040]), QUANTIZE ([:2047]), EXPAND_16 ([:2059]),
    PACK ([:2065]), STRIP_ALPHA ([:2080]) and USER_TRANSFORM ([:2104]). *)
Definition png_read_transform_info (w h bd ct nt : Z) : PostInfo :=
  let ce := rti_expand ct bd nt in
  let ct1 := fst ce in
  let bd2 := rti_scale16 (snd ce) in
  let ct2 := rti_gray_to_rgb ct1 in
  let ch1 := rti_alpha_bump ct2 (rti_base_channels ct2) in
  let cf := rti_filler ct2 ch1 in
  let pd := snd cf * bd2 in
  mkPostInfo w h bd2 (fst cf) (snd cf) pd (png_rowbytes pd w).

(** THE THEOREM.  For every IHDR [png_check_IHDR] accepts, and for every
    [num_trans] whatsoever, the post-transformation row is 8-bit RGBA with
    [rowbytes = 4 * width].  Interlacing does not appear: it is not an
    input to [png_read_transform_info] at all. *)
Lemma png_rowbytes_32 : forall w, png_rowbytes 32 w = 4 * w.
Proof.
  intro w. unfold png_rowbytes.
  replace (8 <=? 32) with true by reflexivity.
  replace (32 / 8) with 4 by reflexivity. lia.
Qed.

Theorem p3_post_is_rgba8 : forall w h bd ct nt,
  ihdr_ct_bd_ok ct bd = true ->
  png_read_transform_info w h bd ct nt
  = mkPostInfo w h 8 CT_RGB_ALPHA 4 32 (png_rowbytes 32 w).
Proof.
  intros w h bd ct nt H.
  assert (Hbd : bd = 1 \/ bd = 2 \/ bd = 4 \/ bd = 8 \/ bd = 16).
  { unfold ihdr_ct_bd_ok in H.
    apply andb_prop in H as [H _]; apply andb_prop in H as [H _].
    rewrite !orb_true_iff, !Z.eqb_eq in H. tauto. }
  assert (Hct : ct = 0 \/ ct = 2 \/ ct = 3 \/ ct = 4 \/ ct = 6).
  { unfold ihdr_ct_bd_ok in H.
    apply andb_prop in H as [H _]; apply andb_prop in H as [_ H].
    apply negb_true_iff in H.
    rewrite !orb_false_iff, Z.ltb_ge, Z.ltb_ge, !Z.eqb_neq in H. lia. }
  (* the combination test kills (3,16), (2,<8), (4,<8), (6,<8) *)
  destruct Hct as [-> | [-> | [-> | [-> | ->]]]];
    destruct Hbd as [-> | [-> | [-> | [-> | ->]]]];
    try (cbn in H; discriminate H);
    unfold png_read_transform_info, rti_expand, rti_scale16,
           rti_gray_to_rgb, rti_base_channels, rti_alpha_bump, rti_filler,
           png_rowbytes, CT_PALETTE, CT_RGB, CT_GRAY, CT_GRAY_ALPHA,
           CT_RGB_ALPHA, PNG_COLOR_MASK_COLOR, PNG_COLOR_MASK_ALPHA;
    destruct (0 <? nt); destruct (negb (nt =? 0));
    cbn; reflexivity.
Qed.

(** [:386]'s [rb != (size_t)w * 4] can never send control to [done]. *)
Corollary front_rowbytes_guard_dead : forall w h bd ct nt,
  ihdr_ct_bd_ok ct bd = true ->
  pi_rowbytes (png_read_transform_info w h bd ct nt) = 4 * w.
Proof.
  intros. rewrite p3_post_is_rgba8 by assumption. cbn [pi_rowbytes].
  apply png_rowbytes_32.
Qed.

(** And the two the harness reads back at [:395]. *)
Corollary front_post_bd_ct : forall w h bd ct nt,
  ihdr_ct_bd_ok ct bd = true ->
  pi_bit_depth (png_read_transform_info w h bd ct nt) = 8
  /\ pi_color_type (png_read_transform_info w h bd ct nt) = PNG_CT_RGB_ALPHA
  /\ pi_channels (png_read_transform_info w h bd ct nt) = 4.
Proof. intros. rewrite p3_post_is_rgba8 by assumption. now cbn. Qed.

(** ** §6.5  Adam7, geometry only — scope decision D9

    [png_set_interlace_handling] makes [png_read_image] ([pngread.c:695])
    run all seven passes into the caller's row pointers, so what comes back
    is the FULL de-interlaced image at the IHDR's [w] x [h] — not a pass.
    The only thing about Adam7 that can therefore reach [cd_front] is the
    pass GEOMETRY, and the only fact about the geometry that is load
    bearing is that the seven passes PARTITION the image.  That is proved
    here; the pass CONTENTS, i.e. the read-side de-interlace round-trip,
    are out of scope by D9 and are not needed by anything below.

    [Chunk.pass_rows] / [Chunk.pass_cols] are the transcription of
    [png.h:2439-2465]'s [PNG_PASS_ROWS] / [PNG_PASS_COLS]; the classic
    tables are pinned by [Chunk.adam7_tables]. *)

Definition adam7_pixels (w h : Z) : Z :=
  fold_right Z.add 0
    (map (fun p => pass_rows h p * pass_cols w p) [0;1;2;3;4;5;6]).

Lemma half_split : forall n, 0 <= n -> (n + 1) / 2 + n / 2 = n.
Proof.
  intros n Hn.
  pose proof (Z_div_mod_eq_full n 2) as Hm.
  pose proof (Z.mod_pos_bound n 2 ltac:(lia)) as Hb.
  assert (Hr : n mod 2 = 0 \/ n mod 2 = 1) by lia.
  destruct Hr as [E|E].
  - replace (n + 1) with (1 + (n / 2) * 2) by lia.
    rewrite Z.div_add by lia. change (1 / 2) with 0. lia.
  - replace (n + 1) with (0 + (n / 2 + 1) * 2) by lia.
    rewrite Z.div_add by lia. change (0 / 2) with 0. lia.
Qed.

(** [ceil(x/2k) + ceil((x-k)/2k) = ceil(x/k)]: halving a pass in the slow
    direction splits its rows (or columns) exactly. *)
Lemma div_split : forall k x, 0 < k -> 0 <= x ->
  (x + 2 * k - 1) / (2 * k) + (x + k - 1) / (2 * k) = (x + k - 1) / k.
Proof.
  intros k x Hk Hx.
  replace (2 * k) with (k * 2) by ring.
  rewrite <- !(Z.div_div _ k 2) by lia.
  replace (x + k * 2 - 1) with ((x + k - 1) + 1 * k) by ring.
  rewrite Z.div_add by lia.
  apply half_split. apply Z.div_pos; lia.
Qed.

(** The three instances the seven passes need, with the literals the
    Adam7 tables actually produce. *)
Lemma div_split_8 : forall x, 0 <= x -> (x + 7) / 8 + (x + 3) / 8 = (x + 3) / 4.
Proof.
  intros x Hx. pose proof (div_split 4 x ltac:(lia) Hx) as X.
  replace (x + 2 * 4 - 1) with (x + 7) in X by lia.
  replace (x + 4 - 1) with (x + 3) in X by lia.
  replace (2 * 4) with 8 in X by lia. exact X.
Qed.

Lemma div_split_4 : forall x, 0 <= x -> (x + 3) / 4 + (x + 1) / 4 = (x + 1) / 2.
Proof.
  intros x Hx. pose proof (div_split 2 x ltac:(lia) Hx) as X.
  replace (x + 2 * 2 - 1) with (x + 3) in X by lia.
  replace (x + 2 - 1) with (x + 1) in X by lia.
  replace (2 * 2) with 4 in X by lia. exact X.
Qed.

Lemma div_split_2 : forall x, 0 <= x -> (x + 1) / 2 + x / 2 = x.
Proof.
  intros x Hx. pose proof (div_split 1 x ltac:(lia) Hx) as X.
  replace (x + 2 * 1 - 1) with (x + 1) in X by lia.
  replace (x + 1 - 1) with x in X by lia.
  replace (2 * 1) with 2 in X by lia.
  now rewrite Z.div_1_r in X.
Qed.

Lemma adam7_pass_rows : forall h,
  map (pass_rows h) [0;1;2;3;4;5;6]
  = [(h + 7) / 8; (h + 7) / 8; (h + 3) / 8;
     (h + 3) / 4; (h + 1) / 4; (h + 1) / 2; h / 2].
Proof.
  intro h. cbn [map]. unfold pass_rows.
  change (Z.shiftl 1 (pass_row_shift 0)) with 8;
  change (Z.shiftl 1 (pass_row_shift 1)) with 8;
  change (Z.shiftl 1 (pass_row_shift 2)) with 8;
  change (Z.shiftl 1 (pass_row_shift 3)) with 4;
  change (Z.shiftl 1 (pass_row_shift 4)) with 4;
  change (Z.shiftl 1 (pass_row_shift 5)) with 2;
  change (Z.shiftl 1 (pass_row_shift 6)) with 2;
  change (pass_start_row 0) with 0;
  change (pass_start_row 1) with 0;
  change (pass_start_row 2) with 4;
  change (pass_start_row 3) with 0;
  change (pass_start_row 4) with 2;
  change (pass_start_row 5) with 0;
  change (pass_start_row 6) with 1.
  replace (h + (8 - 1) - 0) with (h + 7) by lia;
  replace (h + (8 - 1) - 4) with (h + 3) by lia;
  replace (h + (4 - 1) - 0) with (h + 3) by lia;
  replace (h + (4 - 1) - 2) with (h + 1) by lia;
  replace (h + (2 - 1) - 0) with (h + 1) by lia;
  replace (h + (2 - 1) - 1) with h by lia.
  reflexivity.
Qed.

Lemma adam7_pass_cols : forall w,
  map (pass_cols w) [0;1;2;3;4;5;6]
  = [(w + 7) / 8; (w + 3) / 8; (w + 3) / 4;
     (w + 1) / 4; (w + 1) / 2; w / 2; w].
Proof.
  intro w. cbn [map]. unfold pass_cols.
  change (Z.shiftl 1 (pass_col_shift 0)) with 8;
  change (Z.shiftl 1 (pass_col_shift 1)) with 8;
  change (Z.shiftl 1 (pass_col_shift 2)) with 4;
  change (Z.shiftl 1 (pass_col_shift 3)) with 4;
  change (Z.shiftl 1 (pass_col_shift 4)) with 2;
  change (Z.shiftl 1 (pass_col_shift 5)) with 2;
  change (Z.shiftl 1 (pass_col_shift 6)) with 1;
  change (pass_start_col 0) with 0;
  change (pass_start_col 1) with 4;
  change (pass_start_col 2) with 0;
  change (pass_start_col 3) with 2;
  change (pass_start_col 4) with 0;
  change (pass_start_col 5) with 1;
  change (pass_start_col 6) with 0.
  replace (w + (8 - 1) - 0) with (w + 7) by lia;
  replace (w + (8 - 1) - 4) with (w + 3) by lia;
  replace (w + (4 - 1) - 0) with (w + 3) by lia;
  replace (w + (4 - 1) - 2) with (w + 1) by lia;
  replace (w + (2 - 1) - 0) with (w + 1) by lia;
  replace (w + (2 - 1) - 1) with w by lia;
  replace (w + (1 - 1) - 0) with w by lia.
  rewrite Z.div_1_r. reflexivity.
Qed.

Theorem adam7_partitions_image : forall w h,
  0 <= w -> 0 <= h -> adam7_pixels w h = w * h.
Proof.
  intros w h Hw Hh.
  pose proof (div_split_8 w Hw) as Hw8. pose proof (div_split_4 w Hw) as Hw4.
  pose proof (div_split_2 w Hw) as Hw2. pose proof (div_split_8 h Hh) as Hh8.
  pose proof (div_split_4 h Hh) as Hh4. pose proof (div_split_2 h Hh) as Hh2.
  pose proof (adam7_pass_rows h) as Hr. pose proof (adam7_pass_cols w) as Hc.
  unfold adam7_pixels. cbn [map fold_right] in *.
  injection Hr as R0 R1 R2 R3 R4 R5 R6.
  injection Hc as C0 C1 C2 C3 C4 C5 C6.
  rewrite R0, R1, R2, R3, R4, R5, R6, C0, C1, C2, C3, C4, C5, C6.
  set (a0 := (h + 7) / 8) in *; set (a1 := (h + 3) / 8) in *;
  set (a2 := (h + 3) / 4) in *; set (a3 := (h + 1) / 4) in *;
  set (a4 := (h + 1) / 2) in *; set (a5 := h / 2) in *;
  set (b0 := (w + 7) / 8) in *; set (b1 := (w + 3) / 8) in *;
  set (b2 := (w + 3) / 4) in *; set (b3 := (w + 1) / 4) in *;
  set (b4 := (w + 1) / 2) in *; set (b5 := w / 2) in *.
  replace a2 with (a0 + a1) by lia.
  replace a4 with (a0 + a1 + a3) by lia.
  replace b2 with (b0 + b1) by lia.
  replace b4 with (b0 + b1 + b3) by lia.
  replace h with (a0 + a1 + a3 + a5) by lia.
  replace w with (b0 + b1 + b3 + b5) by lia.
  ring.
Qed.

(** ** §6.6  [cd_front]

    Everything above lands here.  The shape is [mkShape w h 8 6] at the
    IHDR's own dimensions, by [p3_post_is_rgba8]; the buffer is
    [rb * h = 4 * w * h] bytes, which is [Harness.sh_total] of that
    shape. *)

(** [png_harness.c:376], verbatim: [!w || !h || h > 100000000u / w].  All
    three operands are [png_uint_32] and [w != 0] on the third, so the
    division is the target's [divuw] and matches [Z.div] exactly. *)
Definition front_area_ok (w h : Z) : bool :=
  negb (w =? 0) && negb (h =? 0) && negb (100000000 / w <? h).

Definition front_shape (d : list Z) : option Shape :=
  (* [:361] [size < kHdr || png_sig_cmp(data, 0, kHdr)] *)
  if Z.of_nat (length d) <? kHdr then None
  else if negb (png_read_sig_ok d) then None
  else match rd_ihdr d with
       | None => None
       | Some (w, h, bd, ct, comp, filt, il) =>
           (* [png.c:2666] [png_error "Invalid IHDR data"] *)
           if negb (png_check_IHDR_ok w h bd ct il comp filt) then None
           (* [:376] *)
           else if negb (front_area_ok w h) then None
           (* [:383] [png_read_update_info] -> [p3_post_is_rgba8] *)
           else Some (mkShape w h 8 PNG_CT_RGB_ALPHA)
       end.

Lemma front_shape_RS_de : forall d s, front_shape d = Some s -> RS_de s.
Proof.
  intros d s H. unfold front_shape in H.
  destruct (Z.of_nat (length d) <? kHdr); [discriminate|].
  destruct (negb (png_read_sig_ok d)); [discriminate|].
  destruct (rd_ihdr d) as [[[[[[[w h] bd] ct] comp] filt] il]|] eqn:Hi;
    [|discriminate].
  destruct (png_check_IHDR_ok w h bd ct il comp filt) eqn:Hc;
    cbn [negb] in H; [|discriminate].
  destruct (front_area_ok w h) eqn:Ha; cbn [negb] in H; [|discriminate].
  injection H as <-.
  pose proof (rd_ihdr_range _ _ _ _ _ _ _ _ Hi) as [Hw Hh].
  unfold front_area_ok in Ha.
  apply andb_prop in Ha as [Ha Hd]; apply andb_prop in Ha as [Ha0 Ha1].
  apply negb_true_iff, Z.eqb_neq in Ha0.
  apply negb_true_iff, Z.eqb_neq in Ha1.
  apply negb_true_iff, Z.ltb_ge in Hd.
  unfold RS_de, PNG_CT_RGB_ALPHA; cbn [sh_w sh_h sh_bd sh_ct].
  repeat split; lia.
Qed.

(** The buffer the C then allocates at [:387]:
    [total = rb * h = 4 * w * h], which is [Harness.sh_total] of the shape
    [front_shape] reports.  This is the equation [codec_front_wf] is about. *)
Lemma front_total : forall w h,
  sh_total (mkShape w h 8 PNG_CT_RGB_ALPHA) = 4 * w * h.
Proof.
  intros w h. unfold sh_total. cbn [sh_w sh_h sh_bd sh_ct].
  replace (channels_of PNG_CT_RGB_ALPHA) with 4 by reflexivity.
  replace (8 / 8) with 1 by reflexivity. ring.
Qed.

(** Four post-transformation tuples pinned against records the DELIVERED
    binary produced, one per interesting input class.  Each is
    [(w, h, bit_depth, color_type, channels, pixel_depth, rowbytes)] read
    out of [info_ptr] at the return of [png_read_update_info]. *)
Example post_pin_pngtest :          (* pngtest.png: 91x69 RGBA8, ADAM7    *)
  png_read_transform_info 91 69 8 CT_RGB_ALPHA 0
  = mkPostInfo 91 69 8 6 4 32 364.
Proof. vm_compute. reflexivity. Qed.

Example post_pin_palette_trns :     (* suite_iftbbn3p08.png: 32x32 P8+tRNS *)
  png_read_transform_info 32 32 8 CT_PALETTE 1
  = mkPostInfo 32 32 8 6 4 32 128.
Proof. vm_compute. reflexivity. Qed.

Example post_pin_gray16 :           (* suite_ibasn0g16.png: 32x32 G16, ADAM7 *)
  png_read_transform_info 32 32 16 CT_GRAY 0
  = mkPostInfo 32 32 8 6 4 32 128.
Proof. vm_compute. reflexivity. Qed.

Example post_pin_gray1 :            (* g1_ct0_bd01_*: 9x9 G1              *)
  png_read_transform_info 9 9 1 CT_GRAY 0 = mkPostInfo 9 9 8 6 4 32 36.
Proof. vm_compute. reflexivity. Qed.

(** The PIXELS.  [Harness.codec_front_wf] constrains their LENGTH and
    nothing else, and [Harness.codec_ed_id] is universally quantified over
    them, so no downstream obligation depends on their values.  On the
    sub-domain where all five transformations are provably the identity —
    a non-interlaced 8-bit RGBA input with correct CRCs and an IEND, which
    is exactly what P2's encoder produces and what the previous
    [front_raw] covered — the canonical pixels really are [dec_raw]'s, and
    that is what is returned; elsewhere the model supplies a length-correct
    buffer rather than inventing [pngrtran.c]'s sample arithmetic.  Both
    branches satisfy the length obligation, which is the whole contract. *)
Definition front_exact (d : list Z) (s : Shape) : option (list Z) :=
  match dec_raw d s with
  | None => None
  | Some pix => if Z.of_nat (length pix) =? sh_total s then Some pix else None
  end.

(** COST NOTE: this is a [repeat], i.e. a term, not a computation.  At the
    top of [RS_de] it stands for 4 x 10^8 bytes, so [cd_front] is NOT
    something to put under [vm_compute] on a large input; every downstream
    obligation goes through [front_pixels_length] instead, which never
    looks inside it. *)
Definition front_fill (s : Shape) : list Z := repeat 0 (Z.to_nat (sh_total s)).

Definition front_pixels (d : list Z) (s : Shape) : list Z :=
  match front_exact d s with
  | Some pix => pix
  | None => front_fill s
  end.

Lemma front_pixels_length : forall d s,
  0 <= sh_total s -> Z.of_nat (length (front_pixels d s)) = sh_total s.
Proof.
  intros d s Hs. unfold front_pixels, front_exact.
  destruct (dec_raw d s) as [pix|].
  - destruct (Z.of_nat (length pix) =? sh_total s) eqn:E.
    + now apply Z.eqb_eq.
    + unfold front_fill. rewrite repeat_length. lia.
  - unfold front_fill. rewrite repeat_length. lia.
Qed.

Definition front_raw (d : list Z) : option (Shape * list Z) :=
  match front_shape d with
  | None => None
  | Some s => Some (s, front_pixels d s)
  end.

(** On the old sub-domain nothing changed: the pixels are still exactly
    [dec_raw]'s at the input's own shape. *)
Lemma front_raw_exact : forall d s pix,
  front_shape d = Some s -> front_exact d s = Some pix ->
  front_raw d = Some (s, pix).
Proof.
  intros d s pix Hs He. unfold front_raw, front_pixels.
  now rewrite Hs, He.
Qed.

(** VALIDATION against the DELIVERED binary, not against a reading of the
    C.  [a working folder] drives
    [/harness/reference_binary] under qemu GDB-RSP with only P3 live,
    breakpointing every guard in [roundtrip_decode_encode] by ADDRESS
    (the harness translation unit carries no DWARF; libpng does) and
    reading [info_ptr] / [png_ptr] through the DWARF offsets, over 672
    inputs: 243 from the real corpus ([a working folder]
    plus [contrib/pngsuite]) and 429 injected — all fifteen legal
    colour-type x bit-depth pairs, each with and without tRNS and each
    non-interlaced and Adam7; Adam7 edge geometry down to 1x1, 1x8, 8x1
    and shapes whose early passes are empty; ancillary chunks before IDAT;
    54 chunk-before-IHDR cases; and the negative battery (zero and
    out-of-range dimensions, both user limits, illegal bit depths and
    colour types, bad compression/filter/interlace bytes, short IHDRs, no
    IHDR, missing PLTE, truncations at every boundary, no IEND at all,
    garbage after IEND, corrupt CRCs everywhere, empty and split IDATs,
    broken zlib).  The model that answers is [Extraction]-compiled from
    THIS file (front/models/frontq); no [vm_compute] is involved.

    Results, all zero-mismatch:

      - DOMAIN SOUNDNESS, the bar: 389 records carried all the way to
        [assert_roundtrip], and [front_shape] returns [Some (w, h, 8, 6)]
        at the binary's own [w], [h] on 389/389.  There is no input in the
        corpus or the stress set that the binary decodes and this model
        declines.  (Restricting [front_shape] back to its old sub-domain
        breaks 329 of those 389, which is the size of the gap closed.)
      - [png_read_transform_info]: 478 records reached the return of
        [png_read_update_info]; the model's [(w,h,bd,ct,channels,
        pixel_depth,rowbytes)] equals [info_ptr]'s on 478/478, and the
        only post-tuple that occurs over the whole set is
        [(8, 6, 4, 32)] with [rowbytes = 4 * width].  [:386]'s guard
        fired 0 times, and [png_get_IHDR] returned 0 zero times.
      - [p3_transformations]: [png_ptr->transformations] equals the
        model's on 478/478 (0x700D000 non-interlaced, 0x700D002 Adam7).
      - [rd_ihdr]: equals the binary's parsed IHDR on 493/493, including
        all 54 chunk-before-IHDR cases (66/67 of that group agree exactly;
        the one exception is a DUPLICATE IHDR, where libpng says "out of
        place" and this model reads the first one — an over-approximation).
      - Adam7: [pass_cols] equals [png_ptr->iwidth] and the full height
        equals [png_ptr->num_rows] at every one of the seven passes of
        every interlaced [png_read_image], 1434/1434 samples; and
        [adam7_pixels]/[pass_rows]/[pass_cols] agree with two independent
        transcriptions of the PNG spec's Adam7 tables over 2116 (w,h)
        pairs including the degenerate ones.
      - [front_raw]'s buffer length is [4*w*h] on 381/381 of the reachable
        records small enough to materialise.

    The 117 remaining over-approximations are itemised by the binary's own
    [png_error] text: 82 are [png_read_image] rejecting the IDAT payload,
    10 a truncation after the IHDR, 8 [png_read_start_row]'s "Out of
    memory", and the rest single container faults (missing PLTE, an
    unhandled critical chunk after the IHDR, IEND before IDAT, a duplicate
    IHDR, a bad PLTE).  Every one is the SAFE direction.

    Negative controls.  Perturbing the captured ground truth fires the
    matching check on every record offered (389/389, 478/478, 478/478,
    493/493).  Perturbing the MODEL is stronger: dropping
    [rti_scale16]'s 16->8, swapping two Adam7 pass columns, dropping
    [rti_filler]'s RGB arm and dropping [:376]'s [!w] guard are all
    rejected by [coqc] — the proofs in this section, not the differential
    run, are what catch them.  Dropping libpng's [PNG_USER_WIDTH_MAX] /
    [PNG_USER_HEIGHT_MAX] compiles and mismatches nothing, and correctly
    so: it only widens the over-approximation, from 117 records to 125. *)

(** * §7  The instance *)

Definition PngCodec : Codec := mkCodec enc_raw dec_raw front_raw.

(** * §8  [codec_wf]

    Both halves.  [codec_ed_id] — the round-trip identity — is NOT proved
    here; it is the research core and belongs to another worker. *)

(** The encoder emits at least the 8-byte signature and a 25-byte IHDR
    chunk, so [assert_roundtrip]'s [enc.len <= kHdr] arm ([:315]) is dead.
    (It emits at least 45: IEND is another 12, and there is always at least
    one IDAT.  33 is all the arm needs.) *)
Lemma encode_stream_ge_33 : forall w h bd ct il zout out,
  encode_stream w h bd ct il zout = Some out -> (33 <= length out)%nat.
Proof.
  intros w h bd ct il zout out H. unfold encode_stream in H.
  destruct (png_write_IHDR w h bd ct PNG_COMPRESSION_TYPE_BASE
                           PNG_FILTER_TYPE_BASE il) as [[hdr ihdr]|] eqn:E;
    [|discriminate].
  injection H as <-.
  pose proof (ihdr_payload_is_13 _ _ _ _ _ _ _ _ _ E) as Hi.
  (* [cbn] iota-reduces [png_signature ++ _] into its eight literal conses *)
  unfold encode_chunks; cbv zeta; cbn [concat length].
  rewrite length_app, Hi. lia.
Qed.

Theorem PngCodec_body : codec_body PngCodec.
Proof.
  intros pix s enc H. cbn [cd_enc PngCodec] in H.
  unfold enc_raw in H.
  destruct (png_write_IHDR (sh_w s) (sh_h s) (sh_bd s) (sh_ct s)
              PNG_COMPRESSION_TYPE_BASE PNG_FILTER_TYPE_BASE
              PNG_INTERLACE_NONE) as [[hdr ihdr]|]; [|discriminate].
  cbv zeta in H.
  destruct (png_zlib_stream _ _ _ _) as [zout|]; [|discriminate].
  pose proof (encode_stream_ge_33 _ _ _ _ _ _ _ H).
  unfold kHdr. lia.
Qed.

Theorem PngCodec_front_wf : codec_front_wf PngCodec.
Proof.
  intros d s pix H. cbn [cd_front PngCodec] in H.
  unfold front_raw in H.
  destruct (front_shape d) as [s0|] eqn:Hs; [|discriminate].
  injection H as <- <-.
  pose proof (front_shape_RS_de _ _ Hs) as Hrs.
  split; [exact Hrs|].
  apply front_pixels_length.
  apply Z.lt_le_incl, RS_de_total_pos, Hrs.
Qed.

Theorem PngCodec_wf : codec_wf PngCodec.
Proof. split; [exact PngCodec_body | exact PngCodec_front_wf]. Qed.

(** The Route-A hooks, instantiated.  [rt_viol_false] and
    [rt_arm_collapses] are already [Qed]'d in [Harness.v]; all they were
    waiting for is a [codec_wf] witness, which is now supplied.  What
    remains open is exactly one hypothesis. *)
Corollary PngCodec_rt_viol_false :
  codec_ed_id PngCodec -> forall d, rt_viol PngCodec d = false.
Proof. intro Hid. apply rt_viol_false; [exact PngCodec_wf | exact Hid]. Qed.

Corollary PngCodec_rt_arm_collapses :
  forall (A : Type) (fail cont : A),
    codec_ed_id PngCodec ->
    forall d, (if rt_viol PngCodec d then fail else cont) = cont.
Proof.
  intros A fail cont Hid d. now rewrite (PngCodec_rt_viol_false Hid).
Qed.

(** * §9  Geometry facts the round-trip lane will need

    Stated here because they are the ones that cross a lane boundary: they
    relate [Harness.v]'s [sh_total] (the driver's own [w * ch * (bd/8) * h])
    to [Chunk.v]'s [wh_rowbytes] (libpng's [PNG_ROWBYTES]).  If these two
    ever disagreed, [enc_raw] would slice the pixel buffer into rows of the
    wrong width and every downstream byte would be wrong. *)

Lemma rowbytes_total : forall s hdr ihdr,
  In (sh_ct s) ed_cts -> (sh_bd s = 8 \/ sh_bd s = 16) ->
  png_write_IHDR (sh_w s) (sh_h s) (sh_bd s) (sh_ct s)
                 PNG_COMPRESSION_TYPE_BASE PNG_FILTER_TYPE_BASE
                 PNG_INTERLACE_NONE = Some (hdr, ihdr) ->
  wh_rowbytes hdr * sh_h s = sh_total s.
Proof.
  intros s hdr ihdr Hct Hbd H.
  unfold png_write_IHDR in H.
  rewrite (channels_agree _ _ Hct Hbd) in H.
  injection H as <- _. cbn [wh_rowbytes].
  unfold sh_total, png_rowbytes.
  unfold ed_cts, PNG_CT_GRAY, PNG_CT_RGB, PNG_CT_RGB_ALPHA,
         PNG_CT_GRAY_ALPHA in Hct; cbn [In] in Hct.
  unfold channels_of, PNG_CT_GRAY, PNG_CT_GRAY_ALPHA, PNG_CT_RGB,
         PNG_CT_RGB_ALPHA.
  destruct Hct as [E|[E|[E|[E|[]]]]]; rewrite <- E;
    destruct Hbd as [Eb|Eb]; rewrite Eb; cbn; lia.
Qed.

(** The pixel buffer the driver synthesises really does split into [h] rows
    of [wh_rowbytes] bytes with nothing left over — the precondition
    [rows_of] is used under. *)
Lemma rows_of_exact : forall s hdr ihdr pix,
  In (sh_ct s) ed_cts -> (sh_bd s = 8 \/ sh_bd s = 16) -> 0 <= sh_h s ->
  png_write_IHDR (sh_w s) (sh_h s) (sh_bd s) (sh_ct s)
                 PNG_COMPRESSION_TYPE_BASE PNG_FILTER_TYPE_BASE
                 PNG_INTERLACE_NONE = Some (hdr, ihdr) ->
  Z.of_nat (length pix) = sh_total s ->
  Z.of_nat (length (rows_of (Z.to_nat (sh_h s))
                            (Z.to_nat (wh_rowbytes hdr)) pix)) = sh_h s.
Proof.
  intros s hdr ihdr pix Hct Hbd Hh H Hlen.
  rewrite rows_of_length. lia.
Qed.

(** * §10  A closed-form pin on the container end of the composition

    Cheap, and it fails loudly if any of [png_write_IHDR], [chunk_bytes],
    [crc32_bytes], [split_idat], [optimize_cmf] or [png_write_IEND_bytes]
    drifts.  (The end-to-end pin on the FULL pipeline is done by
    differential testing against [/harness/reference_binary], not by
    [vm_compute] — see [a working folder].) *)

(** A 1x1 8-bit greyscale image: 8 signature + 25 IHDR + (12 + n) IDAT +
    12 IEND bytes. *)
Example encode_stream_1x1_gray_len :
  option_map (fun l => Z.of_nat (length l))
             (encode_stream 1 1 8 CT_GRAY PNG_INTERLACE_NONE
                            [120; 156; 99; 96; 0; 0; 0; 2; 0; 1])
  = Some 67.
Proof. vm_compute. reflexivity. Qed.

(** [optimize_cmf] really does rewrite the first two zlib bytes on the way
    into the IDAT: for a two-byte image 0x78 0x9C (CINFO 7, a 32768-byte
    window) becomes 0x08 0x99 — CINFO 0, i.e. a 256-byte window, which
    [deflateInit2_] itself can never produce ([deflate.c:430] forces
    [windowBits] 8 up to 9).  The FLG byte keeps its FLEVEL/FDICT bits
    (0x9C & 0xE0 = 0x80) and gets a fresh FCHECK: 0x0899 = 2201 = 71 * 31. *)
Example optimize_cmf_1x1 : optimize_cmf 120 156 2 = (8, 153).
Proof. vm_compute. reflexivity. Qed.

Example optimize_cmf_1x1_fcheck : (8 * 256 + 153) mod 31 = 0.
Proof. reflexivity. Qed.

(** And the whole D8 cluster, keyed on the IHDR parameters alone: a 1x1
    grey image is claimed at windowBits 9 with [Z_DEFAULT_STRATEGY]
    (because [png_write_start_row] cleared every filter bit but NONE),
    while a 64x64 RGBA16 image is claimed at 15 with [Z_FILTERED]. *)
Example d8_cluster_1x1_gray :
  (encode_data_size 1 1 8 CT_GRAY PNG_INTERLACE_NONE,
   encode_strategy CT_GRAY 8 1 1,
   option_map (fun p => deflate_claim_window_bits 15 p)
              (encode_data_size 1 1 8 CT_GRAY PNG_INTERLACE_NONE))
  = (Some 2, 0, Some 9).
Proof. vm_compute. reflexivity. Qed.

Example d8_cluster_64x64_rgba16 :
  (encode_data_size 64 64 16 CT_RGB_ALPHA PNG_INTERLACE_NONE,
   encode_strategy CT_RGB_ALPHA 16 64 64,
   option_map (fun p => deflate_claim_window_bits 15 p)
              (encode_data_size 64 64 16 CT_RGB_ALPHA PNG_INTERLACE_NONE))
  = (Some 32832, 1, Some 15).
Proof. vm_compute. reflexivity. Qed.

(** ** Fuel monotonicity for the two stream pumps

    [defl_pump] and [inf_pump] are the last two fuelled drivers in the
    tree, and they are the ones a whole-stream theorem trips over first:
    [png_zlib_stream] and [png_inflate_stream] both fail closed when the
    fuel binds, so every end-to-end statement carries "the fuel was
    enough" as a hypothesis.  Monotonicity is what lets that hypothesis be
    discharged at a convenient bound and then transported to
    [defl_fuel] / [inf_fuel].

    [defl_pump] has no [option]: its exhaustion sentinel is the return
    code [-98] (and [-99] is [DfUnmodelled], which is NOT a fuel
    artefact — it is fuel-independent and must stay reachable), so the
    hypothesis is stated on the code. *)
Lemma defl_pump_fuel_mono :
  forall f f' chunk flush s,
    (f <= f')%nat -> fst (defl_pump f chunk flush s) <> -98 ->
    defl_pump f' chunk flush s = defl_pump f chunk flush s.
Proof.
  induction f as [|f IH]; intros f' chunk flush s Hle Hne.
  - cbn [defl_pump fst] in Hne. congruence.
  - destruct f' as [|f']; [lia|].
    cbn [defl_pump] in Hne |- *.
    destruct (deflate flush (setD_strm (setZ_availout chunk (d_strm s)) s))
      as [code s1|]; [|reflexivity].
    destruct (Z.eqb (zs_availout (d_strm s1)) 0); [|reflexivity].
    apply IH; [lia | exact Hne].
Qed.

Lemma inf_pump_fuel_mono :
  forall f f' s z inp chunk acc r,
    (f <= f')%nat -> inf_pump f s z inp chunk acc = Some r ->
    inf_pump f' s z inp chunk acc = Some r.
Proof.
  induction f as [|f IH]; intros f' s z inp chunk acc r Hle H.
  - cbn [inf_pump] in H. discriminate H.
  - destruct f' as [|f']; [lia|].
    cbn [inf_pump] in H |- *.
    destruct (inf_call s z inp chunk) as [[[[[ret used] s1] z1] out]|];
      [|exact H].
    destruct (Z.eqb ret Z_STREAM_END || Z.ltb ret 0); [exact H|].
    destruct (Z.eqb used 0 && Nat.eqb (length out) 0); [exact H|].
    apply IH; [lia | exact H].
Qed.

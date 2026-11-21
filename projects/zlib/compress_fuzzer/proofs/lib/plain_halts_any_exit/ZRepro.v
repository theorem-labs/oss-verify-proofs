(** * ZRepro — the z-repro campaign statement, at the model level.

    OWNER: model-rt lane (z-repro campaign, 2026-08-19).  Statements plus
    composition; the faces are OPEN obligations stated as [Definition]s.

    THE TARGET.  zlib_harness.c's [LLVMFuzzerTestOneInput] drives every
    input < 64 MiB through four paths ([zlib_harness.c:188-225]):

      1. decode_stream(x, 15+32) and decode_stream(x, -15): arbitrary bytes
         into inflate, 137-byte input chunks, 4096-byte fresh output windows,
         output discarded.  Obligation: the loop TERMINATES with an answer
         (any documented code) — [ZRepro_Decode_auto] / [ZRepro_Decode_raw].
      2/4. round_trip at (level, windowBits) in
         {(-1,15), (1,-15), (9,31), (0,15)}, all memLevel 8,
         Z_DEFAULT_STRATEGY: one deflate(Z_FINISH) call with
         avail_out = deflateBound must return Z_STREAM_END (the BOUND check
         is that very return: [zlib_harness.c:133-142]), then one
         inflate call with avail_out = len+1 must reproduce x byte-exactly.
      3. compress/uncompress at (-1, 15): same identity, avail_out =
         compressBound on the way out and exactly len on the way back,
         inflate at Z_NO_FLUSH ([uncompr.c]).

    FACTORING adopts DeclIface's landed sandwich verbatim (emitter publishes
    a byte-level frame; a success face says the pump answers; the inflater
    consumes the frame): what (a) concludes is LITERALLY what (b) consumes,
    both stated against one named frame per wrapper family, and the
    composition is PROVED here ([ZRepro_composes]) so the interface is a
    check rather than a guess.

    WHAT THIS FILE DOES NOT INHERIT FROM DeclIface, deliberately:
      * [PayloadFitsWindow] — REFUTED there at a reached input (see the
        banner at [DeclIface.PayloadFitsWindow]), and UNNECESSARY here: the
        harness's round-trip inflate is ONE call with the whole output
        resident ([avail_out = len + 1 >= |X|]), so the implementation's
        distance test [dist > out - beg] compares against output-so-far,
        never against the window, and [BodyDecodesTo]'s own [resolve_lz]
        guard already caps every distance by output-so-far.  The
        window-CONTENT invariant (the libpng campaign's unowned wall) is
        therefore NOT an obligation of any face in this file.
      * the [wr_image_size] / [apply_optimize_cmf] derivation — libpng's
        CMF rewrite does not exist in this driver; windowBits is a driver
        CONSTANT per config, not derived from a header record.

    VOCABULARY IS BORROWED, NOT COINED: the zlib frame's clauses are
    DeclIface's ([ZlibFramed] / [ZlibHeaderOk] (repaired [0 <=] form) /
    [BodyDecodesTo] / [TrailerMatchesPayload]); the entry points below are
    assembled from the tree's own [defl_new] / [deflate] / [inflateInit2] /
    [inflate_model], with call shapes transcribed from zlib_harness.c rather
    than from libpng's drivers ([Codec.png_zlib_stream] pumps 8192-byte
    output windows; the harness gives deflate its WHOLE buffer in one call,
    so this file states the one-call form and owes no chunk-independence
    lemma on the emit side).

    STATEMENT-HARDENING RULES APPLIED:
      * No face hypothesises deflate's success — the emitter face CONCLUDES
        [zr_deflate ... = Some enc] (an existence conjunct, which is exactly
        the deflateBound-fit obligation), so a model that refuses to emit
        cannot satisfy the sandwich vacuously.
      * Every face has a consumer: [ZRepro_composes] consumes all thirteen.
      * The gzip faces are stated against the entry points.  When this
        file was first written they were UNINHABITABLE (the model answered
        [DfUnmodelled] / [InfDead] on the gzip states) and two [= None]
        controls pinned that as a value; the Q3 gzip extension landed the
        same day (2026-08-19), the pins flipped as designed, and the
        controls are now the positive round-trip pins below
        ([zr_control_l9_gzip], [zr_decode_gzip_magic]).  The face
        STATEMENTS never moved — they name only the entry points.
      * Config arithmetic ([-1 -> 6], wrapper families, windowBits
        normalisation, the deflateBound branch selector [hash_bits = 15])
        is pinned by [vm_compute] rather than asserted in prose
        ([zr_cfg_all_four]).
      * Positive controls run BOTH entry points end-to-end at three of the
        four configs, so a face attempt that fails on them has a bug rather
        than a hard case. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel
  Require Import Base Checksum Chunk ZBitsIn ZBitsOut InflateFast Inflate
                 Deflate Codec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import DeclIface.
Import ListNotations.
Import SymbolIdDeclIface.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  Driver constants — zlib_harness.c and the replay driver's cap.
   ========================================================================== *)

(** [Z_DEFAULT_STRATEGY].  NOT [Chunk.PNG_Z_DEFAULT_STRATEGY], which is
    libpng's IDAT default [Z_FILTERED] = 1 ([pngwrite.c]); this driver
    passes zlib's own default, 0 ([zlib_harness.c:115]).  The two differ
    inside [deflate_slow]'s tally decisions, so a proof ported from the
    libpng campaign's level-6 walks must re-check its strategy premise. *)
Definition ZR_STRATEGY : Z := 0.

(** [Z_DEFAULT_COMPRESSION].  [defl_init2] performs the [-1 -> 6]
    substitution itself ([deflate.c:400], pinned by [zr_cfg_all_four]). *)
Definition ZR_DEFAULT_LEVEL : Z := -1.

(** The replay driver refuses [len >= 64 MiB] before the harness runs, so
    every input reaching the four paths is strictly below it. *)
Definition ZR_MAX_INPUT : Z := 67108864.

(** The input universe: byte lists under the cap.  Both conjuncts are
    facts of the DRIVER (bytes come from a file read), not escape
    hatches; inhabitation is witnessed below. *)
Definition ZR_Input (x : list Z) : Prop :=
  Forall (fun b => 0 <= b < 256) x /\ zlen x < ZR_MAX_INPUT.

Example zr_input_inhabited_empty : ZR_Input [].
Proof. split; [constructor | vm_compute; reflexivity]. Qed.

Example zr_input_inhabited : ZR_Input [72; 105].
Proof.
  split; [repeat constructor; lia | vm_compute; reflexivity].
Qed.

(* ==========================================================================
   2.  deflateBound — deflate.c:696-771, at THIS driver's parameters.
   ========================================================================== *)

(** All four configs take deflateBound's TIGHT branch: memLevel 8 gives
    [hash_bits = 8 + 7 = 15] and every config's [w_bits] normalises to 15
    ([-15 -> 15] raw, [31 - 16 = 15] gzip; pinned by [zr_cfg_all_four]),
    so the [w_bits != 15 || hash_bits != 15] conservative branch is dead
    here.  [wraplen] is keyed on the RAW windowBits argument exactly as
    [defl_wrap] keys the wrapper: 0 raw, 6 zlib ([strstart = 0] at the
    harness's bound call, which happens straight after init), 18 gzip
    ([gzhead = Z_NULL] — the driver never sets one). *)
Definition zr_wraplen (windowBits : Z) : Z :=
  if Z.ltb windowBits 0 then 0
  else if Z.ltb 15 windowBits then 18
  else 6.

Definition zr_deflate_bound (windowBits len : Z) : Z :=
  len + Z.shiftr len 12 + Z.shiftr len 14 + Z.shiftr len 25 + 13 - 6
  + zr_wraplen windowBits.

(** [compressBound] ([compress.c]) equals this bound at the zlib wrapper —
    the [13 - 6 + 6] cancellation, pinned so path 3 needs no bound of its
    own. *)
Lemma zr_compress_bound_agrees : forall len,
  zr_deflate_bound 15 len
  = len + Z.shiftr len 12 + Z.shiftr len 14 + Z.shiftr len 25 + 13.
Proof. intros len. unfold zr_deflate_bound, zr_wraplen. cbn. lia. Qed.

Example zr_wraplen_per_config :
  (zr_wraplen 15, zr_wraplen (-15), zr_wraplen 31) = (6, 0, 18).
Proof. vm_compute. reflexivity. Qed.

(* ==========================================================================
   3.  The entry points, at the harness's own call shapes.
   ========================================================================== *)

(** round_trip's emit half ([zlib_harness.c:106-142]): one
    [deflate(Z_FINISH)] call with [avail_out = deflateBound].  [Some] is
    the harness's happy path — [rc = Z_STREAM_END] with exactly the bound
    of room IS the bound check ([:133-142]: any other return means the
    bound under-reported, and [total_out <= avail_out] by construction).
    [None] covers both the model's honest refusals ([DfUnmodelled] — the
    gzip cut) and a bound violation; the emitter faces oblige [Some]. *)
Definition zr_deflate (level windowBits : Z) (x : list Z) : option (list Z) :=
  match defl_new level 8 windowBits 8 ZR_STRATEGY with
  | None => None
  | Some s0 =>
      let s1 := setD_strm (setZ_availout (zr_deflate_bound windowBits (zlen x))
                             (setZ_in x (d_strm s0))) s0 in
      match deflate Z_FINISH s1 with
      | DfUnmodelled => None
      | DfRet code s2 =>
          if Z.eqb code Z_STREAM_END then Some (zs_out (d_strm s2)) else None
      end
  end.

(** [Codec.inf_call] with the flush as a parameter — the harness's two
    inflate call shapes differ there ([Z_FINISH] in round_trip and
    decode_stream's [Z_NO_FLUSH]; [uncompr.c] also uses [Z_NO_FLUSH]).
    Returns (code, consumed, state', strm', produced bytes). *)
Definition zr_inf_call (flush : Z) (s : IState) (z : Strm) (inb : list Z)
                       (avail_out : Z)
  : option (Z * Z * IState * Strm * list Z) :=
  match inflate_model {| g_st := s; g_state_null := false; g_z := z;
                         g_inbuf := zlist inb; g_next_in := 0;
                         g_avail_in := zlen inb; g_in_null := false;
                         g_outbuf := zzero; g_next_out := 0;
                         g_avail_out := avail_out; g_out_null := false;
                         g_flush := flush; g_walloc := true;
                         g_wfresh := zzero |} with
  | None => None
  | Some r =>
      let q := r_q r in
      Some (r_ret r, zlen inb - br_have (q_br q),
            q_st q, q_z q, ob_slice (q_ob q) 0 (o_put (q_ob q)))
  end.

(** round_trip's read half ([zlib_harness.c:150-170]) and [uncompress]'s:
    one inflate call over the whole stream, [Some] only at
    [Z_STREAM_END].  The harness's [total_out = len] and byte-compare are
    both carried by the [= Some x] conclusions below. *)
Definition zr_inflate (flush windowBits cap : Z) (enc : list Z)
  : option (list Z) :=
  match inflateInit2 z_fresh state_fresh windowBits with
  | None => None
  | Some (z, s) =>
      match zr_inf_call flush s z enc cap with
      | None => None
      | Some (ret, _, _, _, out) =>
          if Z.eqb ret Z_STREAM_END then Some out else None
      end
  end.

(** decode_stream's loop ([zlib_harness.c:69-99]): 137-byte input chunks
    ("so calls land mid-symbol"), a fresh 4096-byte output window per
    call, output discarded.  Loop exits: [rc <> Z_OK] (Z_STREAM_END or a
    clean rejection), or input exhausted with output room to spare.
    [Some code] is the C's break; [None] is the model declining (fuel, or
    an unmodelled gzip arm) — the decode faces oblige [Some]. *)
Fixpoint zr_decode_pump (f : nat) (s : IState) (z : Strm) (inp : list Z)
  : option Z :=
  match f with
  | O => None
  | S k =>
      let chunk := Z.min (zlen inp) 137 in
      match zr_inf_call Z_NO_FLUSH s z (firstn (Z.to_nat chunk) inp) 4096 with
      | None => None
      | Some (ret, used, s', z', out) =>
          if negb (Z.eqb ret Z_OK) then Some ret
          else
            let rem := skipn (Z.to_nat used) inp in
            if (Z.eqb (zlen rem) 0) && (Z.ltb (zlen out) 4096)
            then Some ret
            else zr_decode_pump k s' z' rem
      end
  end.

(** Every continuing trip consumes an input byte or fills the whole 4096
    window, and total output is bounded by 258 bytes per consumed bit, so
    [size + (258 * 8 * size) / 4096 + c ~ 1.6 * size] trips over-bounds
    the loop; 4x is the safety margin.  A too-small fuel makes the decode
    faces FALSE, not merely hard, so the margin is deliberate. *)
Definition zr_decode_fuel (x : list Z) : nat := (4 * Z.to_nat (zlen x) + 64)%nat.

Definition zr_decode (windowBits : Z) (x : list Z) : option Z :=
  match inflateInit2 z_fresh state_fresh windowBits with
  | None => None
  | Some (z, s) => zr_decode_pump (zr_decode_fuel x) s z x
  end.

(* ==========================================================================
   4.  Config arithmetic, pinned as values.
   ========================================================================== *)

Definition zr_cfg_probe (level windowBits : Z) : option (Z * Z * Z * Z * Z) :=
  match defl_init2 level 8 windowBits 8 ZR_STRATEGY with
  | None => None
  | Some g => Some (dg_level g, dg_wrap g, dg_w_bits g, dg_strategy g,
                    dg_hash_bits g)
  end.

(** The four (level, windowBits) pairs, through the tree's own
    [defl_init2]: the [-1 -> 6] map, the three wrapper families, the
    windowBits normalisation, strategy 0 accepted, and [hash_bits = 15]
    (the deflateBound tight-branch selector) at every config. *)
Example zr_cfg_all_four :
  (zr_cfg_probe ZR_DEFAULT_LEVEL 15, zr_cfg_probe 1 (-15),
   zr_cfg_probe 9 31, zr_cfg_probe 0 15)
  = (Some (6, 1, 15, 0, 15), Some (1, 0, 15, 0, 15),
     Some (9, 2, 15, 0, 15), Some (0, 1, 15, 0, 15)).
Proof. vm_compute. reflexivity. Qed.

(** The inflate side's wrap arithmetic ([inflate.c:141-171]) at the four
    windowBits values the harness passes to [inflateInit2]: 15 -> zlib
    (wrap 5), -15 -> raw (wrap 0), 31 -> gzip (wrap 6, gzip bit SET —
    which is why the unmodelled gzip arms are LIVE there), 47 -> auto
    (wrap 7).  The [(-99, -99)] fallback cannot false-pass: no expected
    row equals it. *)
Definition zr_iwrap_probe (windowBits : Z) : Z * Z :=
  match inflateInit2 z_fresh state_fresh windowBits with
  | None => (-99, -99)
  | Some (_, s) => (h_wrap (s_hdr s), w_wbits (s_win s))
  end.

Example zr_iwrap_all :
  (zr_iwrap_probe 15, zr_iwrap_probe (-15), zr_iwrap_probe 31,
   zr_iwrap_probe 47)
  = ((5, 15), (0, 15), (6, 15), (7, 15)).
Proof. vm_compute. reflexivity. Qed.

(* ==========================================================================
   5.  The frames — one named byte-level Prop per wrapper family.
   ========================================================================== *)

(** zlib (windowBits 15; configs (-1,15) and (0,15), and path 3).
    DeclIface's clauses verbatim, MINUS the refuted [PayloadFitsWindow]
    (see the header).  At windowBits 15 the emitted CINFO is always 7 —
    there is no [optimize_cmf] in this driver — so even the pre-repair
    header clause would hold; the repaired [0 <=] form is used because it
    is the landed vocabulary. *)
Definition ZR_FramedZlib (enc X : list Z) : Prop :=
  exists b0 b1 body ad,
    ZlibFramed enc b0 b1 body ad
    /\ ZlibHeaderOk b0 b1
    /\ BodyDecodesTo body X
    /\ TrailerMatchesPayload ad X.

(** raw (windowBits -15; config (1,-15)): no header, no trailer — the
    stream IS the deflate body.  The wrapper clauses are trivially
    discharged by this equation; that is the whole content of the raw
    family's framing. *)
Definition ZR_FramedRaw (enc X : list Z) : Prop := BodyDecodesTo enc X.

(** gzip (windowBits 31; config (9,31)).  Header bytes from
    [deflate.c:889-906] at [gzhead = Z_NULL]: magic 31 139, CM 8, FLG 0,
    MTIME 0 0 0 0, XFL ([level = 9 -> 2]; else 4 below level 2 or at
    strategies >= Z_HUFFMAN_ONLY; else 0), OS 3 ([zutil.h:181], the Unix
    fallback this build takes).  Trailer: CRC-32 then ISIZE, both
    little-endian ([deflate.c:1240-1249]); [zr_le32] masks each byte, so
    the mod-2^32 ISIZE truncation is built in (and vacuous under the 64
    MiB cap).  The checksum is spelled as the DECODER recomputes it
    ([Inflate.v:408] [upd_check] with [flags <> 0]), mirroring
    DeclIface's adler clause; the emitter side owes the
    [crc32_z_at]/[crc32_z] bridge, which [ChecksumThy] already carries. *)
Definition zr_le32 (v : Z) : list Z :=
  [Z.land v 255; Z.land (Z.shiftr v 8) 255;
   Z.land (Z.shiftr v 16) 255; Z.land (Z.shiftr v 24) 255].

Definition zr_gzip_xfl (level : Z) : Z :=
  if Z.eqb (zdefl_level level) 9 then 2
  else if (Z.leb 2 ZR_STRATEGY) || (Z.ltb (zdefl_level level) 2) then 4
  else 0.

Definition ZR_GZIP_OS : Z := 3.

Definition zr_gzip_header (level : Z) : list Z :=
  [31; 139; 8; 0; 0; 0; 0; 0; zr_gzip_xfl level; ZR_GZIP_OS].

Definition zr_crc_init : Z := crc32_z 0 true 0 [].

Definition ZR_FramedGzip (level : Z) (enc X : list Z) : Prop :=
  exists body,
    enc = zr_gzip_header level ++ body
          ++ zr_le32 (crc32_z zr_crc_init false 0 X)
          ++ zr_le32 (zlen X)
    /\ BodyDecodesTo body X.

(* ==========================================================================
   6.  The faces — DeclIface's sandwich, per config.
   ========================================================================== *)

(** (a) The emitter publishes the frame AND succeeds within the bound.
    The success conjunct is the deflateBound-fit obligation: [zr_deflate]
    returns [Some] exactly when one [Z_FINISH] call at
    [avail_out = deflateBound] ends the stream. *)
Definition ZR_EmitterPublishes (level windowBits : Z)
           (Frame : list Z -> list Z -> Prop) : Prop :=
  forall x, ZR_Input x ->
    exists enc, zr_deflate level windowBits x = Some enc
             /\ zlen enc <= zr_deflate_bound windowBits (zlen x)
             /\ Forall (fun b => 0 <= b < 256) enc
             /\ Frame enc x.

(** The two flush values the harness's whole-stream reads use.  Both are
    consumed below ([Z_FINISH] by round_trip, [Z_NO_FLUSH] by
    uncompress); the disjunction keeps [Z_BLOCK]/[Z_TREES] semantics —
    under which a whole-stream read legitimately stops early and these
    faces would be FALSE — out of the obligations. *)
Definition ZR_Flush1 (flush : Z) : Prop :=
  flush = Z_NO_FLUSH \/ flush = Z_FINISH.

(** (c) The pump SUCCEEDS on encoder output — [Some]-ness of [zr_inflate],
    which gates on [Z_STREAM_END], so this is a success claim and not
    mere termination (the distinction DeclIface's register documents at
    its (c) entry: totality lemmas that answer WITH AN ERROR do not
    supply this face). *)
(** CAP CEILINGS (repair 2026-08-19, TL-approved; spellings checked by
    an earlier development run): the C interface's [avail_in]/[avail_out] are [uInt], so
    a single call cannot receive more -- and the MODEL's own u32 unwrap
    ([if_finish]) genuinely wraps beyond them, reachably (a 64 MiB input
    can decompress past 2^32 at zlib's 1032:1 ceiling), so the unbounded
    forms were falsifiable, not merely unprovable.  Tight ceilings:
    [avail_out <= 2^32-1]; [avail_in <= 2^32-6] (the -6 absorbs the
    fast-path give-back epilogue).  The input-side bound holds along a
    run by CONSERVATION of the bit budget [8*br_have + br_bits] from a
    bits-0 reset state -- NOT by pointwise decrease ([br_have] can grow
    by up to 4 at a give-back). *)
Definition ZR_PumpSucceeds (level windowBits : Z) : Prop :=
  forall x enc flush cap,
    ZR_Input x -> zr_deflate level windowBits x = Some enc ->
    ZR_Flush1 flush -> zlen x <= cap -> cap <= 4294967295 ->
    exists y, zr_inflate flush windowBits cap enc = Some y.

(** (b) If the pump answers on a framed stream, the answer is X.  Premised
    on the frame and on success, exactly as DeclIface splits (b) from
    (c); [cap] is quantified above [zlen x] so one face serves both the
    [len + 1] (round_trip) and [len] (uncompress) call shapes. *)
(** BYTE FIDELITY (repair 2026-08-20; machine-checked falsifier by
    q6-fixedtbl, ProbeFalsify.v: witness enc entry 321 reads masked as 65
    through [bytes_bits] on the declarative side but is copied RAW by
    [inf_COPY], so without this premise a framed stream pumps to a
    non-byte output and the face is FALSE — all other premises hold).
    [next_in] is [unsigned char*]: bytes by TYPE, the same fidelity class
    as the uInt caps above.  [br_wf]'s in-range clause is the walk-side
    guard; this premise is what lets the entry leg establish it from
    [zlist enc]. *)
Definition ZR_InflaterConsumes (windowBits : Z)
           (Frame : list Z -> list Z -> Prop) : Prop :=
  forall x enc flush cap,
    ZR_Input x -> Frame enc x -> ZR_Flush1 flush -> zlen x <= cap ->
    cap <= 4294967295 -> zlen enc <= 4294967290 ->
    Forall (fun b => 0 <= b < 256) enc ->
    (exists y, zr_inflate flush windowBits cap enc = Some y) ->
    zr_inflate flush windowBits cap enc = Some x.

(** RETIRED SPELLING, retained per the retention convention as the
    standing target of the machine-checked falsifier (the guard lemma
    proving its NEGATION lives in the falsifier-guard leaf and must keep
    compiling forever; a /tmp probe rots).  Do NOT consume: FALSE at
    non-byte [enc] — witness class [1;1;0;254;255;321] / x = [65], see
    the BYTE FIDELITY comment above. *)
Definition ZR_InflaterConsumes_noenc (windowBits : Z)
           (Frame : list Z -> list Z -> Prop) : Prop :=
  forall x enc flush cap,
    ZR_Input x -> Frame enc x -> ZR_Flush1 flush -> zlen x <= cap ->
    cap <= 4294967295 -> zlen enc <= 4294967290 ->
    (exists y, zr_inflate flush windowBits cap enc = Some y) ->
    zr_inflate flush windowBits cap enc = Some x.

Definition ZRepro_Inflater_raw_noenc : Prop :=
  ZR_InflaterConsumes_noenc (-15) ZR_FramedRaw.

(** The decode faces: the chunked pump ANSWERS on arbitrary bytes.  Any
    documented code is a pass (the C treats non-Z_OK as a clean break);
    what is obliged is that the model does not decline — no fuel-out, no
    unmodelled arm. *)
Definition ZR_DecodeTerminates (windowBits : Z) : Prop :=
  forall x, ZR_Input x -> exists r, zr_decode windowBits x = Some r.

(* --------------------------------------------------------------------------
   The named faces — the census surface.  One Definition per obligation;
   ZRepro_Inflater_zlib is shared by both zlib-wrapper configs and path 3
   (same windowBits, same frame — level is an emitter-only parameter).
   -------------------------------------------------------------------------- *)

Definition ZRepro_Emitter_default_zlib : Prop :=
  ZR_EmitterPublishes ZR_DEFAULT_LEVEL 15 ZR_FramedZlib.
Definition ZRepro_Emitter_l1_raw : Prop :=
  ZR_EmitterPublishes 1 (-15) ZR_FramedRaw.
Definition ZRepro_Emitter_l9_gzip : Prop :=
  ZR_EmitterPublishes 9 31 (ZR_FramedGzip 9).
Definition ZRepro_Emitter_l0_zlib : Prop :=
  ZR_EmitterPublishes 0 15 ZR_FramedZlib.

Definition ZRepro_Pump_default_zlib : Prop := ZR_PumpSucceeds ZR_DEFAULT_LEVEL 15.
Definition ZRepro_Pump_l1_raw : Prop := ZR_PumpSucceeds 1 (-15).
Definition ZRepro_Pump_l9_gzip : Prop := ZR_PumpSucceeds 9 31.
Definition ZRepro_Pump_l0_zlib : Prop := ZR_PumpSucceeds 0 15.

Definition ZRepro_Inflater_zlib : Prop := ZR_InflaterConsumes 15 ZR_FramedZlib.
Definition ZRepro_Inflater_raw : Prop := ZR_InflaterConsumes (-15) ZR_FramedRaw.
Definition ZRepro_Inflater_gzip : Prop := ZR_InflaterConsumes 31 (ZR_FramedGzip 9).

Definition ZRepro_Decode_auto : Prop := ZR_DecodeTerminates 47.
Definition ZRepro_Decode_raw : Prop := ZR_DecodeTerminates (-15).

(* ==========================================================================
   7.  The targets, and the composition — the one proof that matters here.
   ========================================================================== *)

(** One round trip, at the harness's exact call shape: [Z_FINISH] both
    ways, [avail_out = len + 1] on the way back
    ([zlib_harness.c:144-170]). *)
Definition ZR_RoundTrip (level windowBits : Z) : Prop :=
  forall x, ZR_Input x ->
    exists enc, zr_deflate level windowBits x = Some enc
             /\ zr_inflate Z_FINISH windowBits (zlen x + 1) enc = Some x.

Definition ZRepro_RoundTrip_default_zlib : Prop := ZR_RoundTrip ZR_DEFAULT_LEVEL 15.
Definition ZRepro_RoundTrip_l1_raw : Prop := ZR_RoundTrip 1 (-15).
Definition ZRepro_RoundTrip_l9_gzip : Prop := ZR_RoundTrip 9 31.
Definition ZRepro_RoundTrip_l0_zlib : Prop := ZR_RoundTrip 0 15.

(** Path 3: [compress]/[uncompress] one-call at (-1, 15).  [compress2]
    feeds everything in one [Z_FINISH] deflate call at
    [avail_out = compressBound] — which IS [zr_deflate ZR_DEFAULT_LEVEL 15]
    by [zr_compress_bound_agrees] — and [uncompress2] reads back with
    [Z_NO_FLUSH] at [avail_out = len] exactly. *)
Definition ZRepro_CompressPath : Prop :=
  forall x, ZR_Input x ->
    exists enc, zr_deflate ZR_DEFAULT_LEVEL 15 x = Some enc
             /\ zr_inflate Z_NO_FLUSH 15 (zlen x) enc = Some x.

(** Everything the A5 arm owes the walk layer, as one Prop. *)
Definition ZRepro_HarnessObligation : Prop :=
  ZRepro_Decode_auto /\ ZRepro_Decode_raw
  /\ ZRepro_RoundTrip_default_zlib /\ ZRepro_RoundTrip_l1_raw
  /\ ZRepro_RoundTrip_l9_gzip /\ ZRepro_RoundTrip_l0_zlib
  /\ ZRepro_CompressPath.

(** The published bound sits far inside the input-side ceiling at every
    admissible input -- the composition discharges the inflater face's
    [zlen enc] premise through it. *)
Lemma zr_bound_small : forall windowBits len,
  0 <= len < ZR_MAX_INPUT ->
  zr_deflate_bound windowBits len <= 4294967290.
Proof.
  intros wb len Hlen.
  unfold zr_deflate_bound, zr_wraplen, ZR_MAX_INPUT in *.
  rewrite !Z.shiftr_div_pow2 by lia.
  assert (H12 : len / 2 ^ 12 < 16384)
    by (apply Z.div_lt_upper_bound; lia).
  assert (H14 : len / 2 ^ 14 < 4096)
    by (apply Z.div_lt_upper_bound; lia).
  assert (H25 : len / 2 ^ 25 < 2)
    by (apply Z.div_lt_upper_bound; lia).
  assert (Hp12 : 0 <= len / 2 ^ 12) by (apply Z.div_pos; lia).
  assert (Hp14 : 0 <= len / 2 ^ 14) by (apply Z.div_pos; lia).
  assert (Hp25 : 0 <= len / 2 ^ 25) by (apply Z.div_pos; lia).
  destruct (Z.ltb wb 0); [lia|].
  destruct (Z.ltb 15 wb); lia.
Qed.

(** The sandwich closes, per config. *)
Lemma ZR_composes : forall level windowBits Frame,
  ZR_EmitterPublishes level windowBits Frame ->
  ZR_PumpSucceeds level windowBits ->
  ZR_InflaterConsumes windowBits Frame ->
  ZR_RoundTrip level windowBits.
Proof.
  intros level wb Frame HA HC HB x Hx.
  pose proof (proj2 Hx) as Hxlen.
  assert (Hxnn : 0 <= zlen x) by (unfold zlen; lia).
  destruct (HA x Hx) as [enc [Henc [Hlen [Hbytes Hframe]]]].
  assert (Hcap : zlen x + 1 <= 4294967295)
    by (unfold ZR_MAX_INPUT in Hxlen; lia).
  assert (Hin : zlen enc <= 4294967290)
    by (pose proof (zr_bound_small wb (zlen x) (conj Hxnn Hxlen)); lia).
  exists enc. split; [exact Henc|].
  apply (HB x enc Z_FINISH (zlen x + 1) Hx Hframe (or_intror eq_refl)
            ltac:(lia) Hcap Hin Hbytes).
  exact (HC x enc Z_FINISH (zlen x + 1) Hx Henc (or_intror eq_refl)
            ltac:(lia) Hcap).
Qed.

(** ...and path 3 rides the SAME three zlib faces at the other flush and
    the tighter cap — the reason those faces quantify both. *)
Lemma ZR_composes_compress :
  ZRepro_Emitter_default_zlib -> ZRepro_Pump_default_zlib ->
  ZRepro_Inflater_zlib -> ZRepro_CompressPath.
Proof.
  intros HA HC HB x Hx.
  pose proof (proj2 Hx) as Hxlen.
  assert (Hxnn : 0 <= zlen x) by (unfold zlen; lia).
  destruct (HA x Hx) as [enc [Henc [Hlen [Hbytes Hframe]]]].
  assert (Hcap : zlen x <= 4294967295)
    by (unfold ZR_MAX_INPUT in Hxlen; lia).
  assert (Hin : zlen enc <= 4294967290)
    by (pose proof (zr_bound_small 15 (zlen x) (conj Hxnn Hxlen)); lia).
  exists enc. split; [exact Henc|].
  apply (HB x enc Z_NO_FLUSH (zlen x) Hx Hframe (or_introl eq_refl)
            ltac:(lia) Hcap Hin Hbytes).
  exact (HC x enc Z_NO_FLUSH (zlen x) Hx Henc (or_introl eq_refl)
            ltac:(lia) Hcap).
Qed.

(** The whole obligation from the thirteen faces.  Every face is consumed
    here; a face without a consumer would be a guess. *)
Theorem ZRepro_composes :
  ZRepro_Emitter_default_zlib -> ZRepro_Emitter_l1_raw ->
  ZRepro_Emitter_l9_gzip -> ZRepro_Emitter_l0_zlib ->
  ZRepro_Pump_default_zlib -> ZRepro_Pump_l1_raw ->
  ZRepro_Pump_l9_gzip -> ZRepro_Pump_l0_zlib ->
  ZRepro_Inflater_zlib -> ZRepro_Inflater_raw -> ZRepro_Inflater_gzip ->
  ZRepro_Decode_auto -> ZRepro_Decode_raw ->
  ZRepro_HarnessObligation.
Proof.
  intros HAd HA1 HA9 HA0 HCd HC1 HC9 HC0 HBz HBr HBg HD47 HDr.
  repeat split.
  - exact HD47.
  - exact HDr.
  - exact (ZR_composes _ _ _ HAd HCd HBz).
  - exact (ZR_composes _ _ _ HA1 HC1 HBr).
  - exact (ZR_composes _ _ _ HA9 HC9 HBg).
  - exact (ZR_composes _ _ _ HA0 HC0 HBz).
  - exact (ZR_composes_compress HAd HCd HBz).
Qed.

(* ==========================================================================
   8.  Controls — the definitions exercised end-to-end, as values.
   ========================================================================== *)

(** Positive control, config (0, 15): stored path emit, zlib wrapper,
    inflate back at the round_trip call shape.  The [match] form keeps
    [vm_compute] evar-free; [None => False] cannot false-pass. *)
Example zr_control_l0_zlib :
  match zr_deflate 0 15 [72; 73] with
  | Some enc => zr_inflate Z_FINISH 15 3 enc = Some [72; 73]
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** Positive control, config (1, -15): fast-path emit on a repetitive
    input (so the match machinery runs), raw wrapper, inflate back. *)
Example zr_control_l1_raw :
  match zr_deflate 1 (-15) [65; 66; 65; 66; 65; 66; 65; 66] with
  | Some enc => zr_inflate Z_FINISH (-15) 9 enc = Some [65; 66; 65; 66; 65; 66; 65; 66]
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** Positive control, config (-1, 15): the default level's slow path,
    and the compress-path call shape ([Z_NO_FLUSH], cap = len) on the
    same stream — both flush values of [ZR_Flush1] exercised against a
    real encoder output. *)
Example zr_control_default_zlib :
  match zr_deflate ZR_DEFAULT_LEVEL 15 [104; 101; 108; 108; 111] with
  | Some enc =>
      zr_inflate Z_FINISH 15 6 enc = Some [104; 101; 108; 108; 111]
      /\ zr_inflate Z_NO_FLUSH 15 5 enc = Some [104; 101; 108; 108; 111]
  | None => False
  end.
Proof. vm_compute. split; reflexivity. Qed.

(** Cross-validation of the DECLARATIVE side against a real encoder
    output: the raw frame is [dec_stream] on the bytes themselves, so
    this control runs the spec decoder over the implementation
    emitter's stream. *)
Example zr_frame_raw_control :
  match zr_deflate 1 (-15) [65; 66; 65; 66; 65; 66; 65; 66] with
  | Some enc => ZR_FramedRaw enc [65; 66; 65; 66; 65; 66; 65; 66]
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** THE GZIP CUT IS CLOSED — updated 2026-08-19 (same day), after the
    zlib-rt Q3 gzip extension landed: [Deflate.v]'s GZIP_STATE header +
    wrap-2 trailer arms and [Inflate.v]'s eight gzip header arms are now
    transcribed.  The two [= None] gap-pins this file originally carried
    here FLIPPED, which is exactly what they were for: the model gap they
    pinned no longer exists.  Config (9, 31) therefore gets the same
    end-to-end positive control as the other three configs.  The FACES
    stay open — these are point witnesses, not proofs. *)
Example zr_control_l9_gzip :
  match zr_deflate 9 31 [72; 73; 72; 73] with
  | Some enc => zr_inflate Z_FINISH 31 5 enc = Some [72; 73; 72; 73]
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** Bare gzip magic at auto-detect: the header arms consume both bytes
    and ask for more input — a clean [Z_OK] break of the decode loop, no
    longer a model decline. *)
Example zr_decode_gzip_magic : zr_decode 47 [31; 139] = Some 0.
Proof. vm_compute. reflexivity. Qed.

(** Decode controls on the modeled families: empty input answers
    [Z_BUF_ERROR] (-5) in one trip at both windowBits; a two-byte valid
    raw stream (final static block, EOB only) answers [Z_STREAM_END];
    junk at auto-detect answers a clean [Z_DATA_ERROR] (-3). *)
Example zr_decode_controls :
  (zr_decode 47 [], zr_decode (-15) [], zr_decode (-15) [3; 0],
   zr_decode 47 [0; 1; 2])
  = (Some (-5), Some (-5), Some 1, Some (-3)).
Proof. vm_compute. reflexivity. Qed.

(** ** [GB] garbage-init entries.

    [inflateInit2] already takes the freshly-allocated state as an
    explicit parameter (ZALLOC does not zero; Inflate.v deviation 8);
    the plain entries instantiate it at [Codec.state_fresh] and the
    user's [z_stream] at [Codec.z_fresh].  The [_g] forms quantify BOTH
    allocations, making the malloc/stack-garbage dependence explicit at
    the entry; the plain entries are their definitional instances
    (reflexivity ties below), so nothing landed moves. *)

Definition zr_inflate_g (gz : Strm) (gs : IState)
           (flush windowBits cap : Z) (enc : list Z) : option (list Z) :=
  match inflateInit2 gz gs windowBits with
  | None => None
  | Some (z, s) =>
      match zr_inf_call flush s z enc cap with
      | None => None
      | Some (ret, _, _, _, out) =>
          if Z.eqb ret Z_STREAM_END then Some out else None
      end
  end.

Definition zr_decode_g (gz : Strm) (gs : IState)
           (windowBits : Z) (x : list Z) : option Z :=
  match inflateInit2 gz gs windowBits with
  | None => None
  | Some (z, s) => zr_decode_pump (zr_decode_fuel x) s z x
  end.

Lemma zr_inflate_g_fresh : forall flush windowBits cap enc,
  zr_inflate_g z_fresh state_fresh flush windowBits cap enc
  = zr_inflate flush windowBits cap enc.
Proof. reflexivity. Qed.

Lemma zr_decode_g_fresh : forall windowBits x,
  zr_decode_g z_fresh state_fresh windowBits x = zr_decode windowBits x.
Proof. reflexivity. Qed.

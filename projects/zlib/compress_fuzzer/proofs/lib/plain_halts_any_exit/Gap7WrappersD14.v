(* the zlib 1.4 twin of Gap7WrappersD, RT's inflate at 1.4. Cut: untainted top-level declarations (imported from Gap7WrappersD), 1.3.1-only declarations no 1.4 consumer needs. *)
(** * Gap7Wrappers — GAP7 FINALE: the three pump-face config wrappers,
    CLOSED.

    OWNER: q7-decode worker fork (zlib z-repro campaign, 2026-08-21;
    finale 2026-08-22).

    The three targets ZRepro_Pump_{default_zlib,l1_raw,l9_gzip} are
    proven OUTRIGHT.  The last supply — an earlier development run's selection heads —
    LANDED with the g1-gap7 train (closed, 48 pure
    ADDs): the frozen head Props live in-tree as
    GtBodySelect.{ZrBodySelect, ZrBodySelectHead0} (the STRICT round-3
    texts, lineage GtBodySelect.v md5
    , — the
    ONE-premise swap vs the re-freeze: the declarative decode
    premise is the STRICT decoder Gap7Strict.dec_stream_from_strict
    (landed ); h_check/h_total conjuncts as adopted at ;
    Head0 deliberately conjunct-free, raw wrap-0 has no trailer gates),
    and the head PROOFS in
    BsAsm.{zr_body_select_holds, zr_body_select_head0_holds} (+ the
    fueled zr_body_select_fuel_holds ladder), each posed at its
    wrapper's use site.  The former Section-Variable rows
    (Hsel/Hsel0/HselC, the Hroot pattern) and their local Prop copies
    are RETIRED — the landed texts were verified TOKEN-IDENTICAL to the
    local copies at this edit (verbcheck_final.py, PASS both pairs).
    The ONE shared MODULO residue row [Henough] (EnoughFits_STMT) was
    already RETIRED — DISCHARGED by g6's landed
    EnoughFitsB14.enough_fits_capped_final (window g6-enoughfits, gate
    , FULLLOAD 1239).

    FINAL CENSUS — SUPPLY AND HEADS COMPLETE: ZERO hypotheses, ZERO
    axioms (all proofs Qed; Print Assumptions closed):
      ZRepro_Pump_l1_raw_holds       : ZRepro_Pump_l1_raw
      ZRepro_Pump_default_zlib_holds : ZRepro_Pump_default_zlib
      ZRepro_Pump_l9_gzip_holds      : ZRepro_Pump_l9_gzip
    (naming per the campaign's zero-premise _holds convention, matching
    ZReproL0E.ZRepro_Pump_l0_zlib_holds).  Each completes its config
    end-to-end with the landed rt legs (RtL1Model / RtN1Model /
    RtL9Gz{Model,Stream,Final} consume exactly these Props).
    Retired rows: Hrawstrict/Hzlstrict/Hgzstrict — the three INTERIM
    strict-supply rows, RETIRED: q5 stage-2 LANDED
    (ZREmitDecode.{raw,zlib,gzip}_body_strict, , each of shape
    build_accepts_of_kraft_STMT -> EnoughFits_STMT -> <row>, the row
    texts VERBATIM the retired rows' — token-checked at this edit) and
    the bridge LANDED (Gap7Bridge.build_accepts_of_kraft_holds,
    , closes the first premise); each row is DERIVED IN-PROOF
    at its use site from landed names alone;
    Henough — the LAST residue row, RETIRED: g6's commission LANDED as
    EnoughFitsB14.enough_fits_capped_final (window g6-enoughfits, gate
    , 18 pure ADDs, B14 pin ; the
    r4 addendum is the commission record), consumed BY TREE NAME at the
    three derivation sites;
    Hdecapp — supplied by
    DecappStrict.dec_stream_from_strict_app (LANDED strict twin; the
    mod-8 premise carries over unchanged);
    Hzltail/Hgztail — CONSUMED from the LANDED
    Q6TailPos.{zr_zl_tail_pos,zr_gz_tail_pos} (q6 F5, ): the
    ratified spellings PLUS one nil-fixed-point premise each (q6's
    o_put = 0 corner), discharged in-proof at the entry-pinned h_check
    via Q6TailPos.{adler32_z_nil_fix,crc32_z_nil_fix};
    Hzlpad/Hgzpad — folded into the interim strict rows (the strict
    body_valid mirrors subsume decode success AND pad exactly as the
    lax ZREmitDecode.{zlib,gzip}_body_valid did at F4).
    Hzlfdict: DISCHARGED, F2 landed DeclIface 4th clause.
    Hrawlen: DISCHARGED, g6's ZReproG6RawLen landed in window
    q7-amend11 at the pin (theorem [hrawlen], statement
    verbatim); consumed in-proof at the use site.
    The PRE-re-freeze M_TYPE head (ZrBodySelect) kept below for
    provenance only; NO wrapper consumes it (the check/total gap).
    The positive zlib header step (was a residue) is DISCHARGED in this
    file: zr_zl_entry_pos.

    Composition per config (EVERY name LANDED in-tree):
      supply   : ZRRawShell.zr_emitter_l1_raw_frame /
                 ZREmitClose.ZRepro_Emitter_{default_zlib,l9_gzip}_holds
                 + the LANDED strict rows
                 ZREmitDecode.{raw,zlib,gzip}_body_strict (),
                 each derived in-proof from
                 Gap7Bridge.build_accepts_of_kraft_holds ()
                 + the landed EnoughFitsB14.enough_fits_capped_final
      pad      : folded into the landed strict rows (strict
                 body_valid shape — decode success + sub-byte leftover)
      init     : ZrRawAsm.zr_init_m15 / L0C.zr_init_15 / (gzip: local vm)
      entry    : (raw: none — Head0) / Q6ZlibEntry / Q6GzipEntry
      body     : GtBodySelect.{ZrBodySelect, ZrBodySelectHead0} via
                 BsAsm.{zr_body_select_holds, zr_body_select_head0_holds}
      tail     : Q6RawTail.zr_raw_tail / Q6TailPos.zr_zl_tail_pos /
                 Q6TailPos.zr_gz_tail_pos (zlib+gzip tails LANDED, q6 F5)
      fuel gap : GtInfTotal.inflate_model_total_reach (DynTblOk_holds)
                 + Q6AsmSupport.zr_loop_uniq — the driver runs inf_loop
                 at its OWN fuel while the heads' k is unbounded; the
                 landed totality theorem + loop uniqueness close the gap
                 with NO head re-freeze.
      leave    : Q6AsmSupport.zr_leave_done_fin
      flush    : ZReproL0E.zr_inflate_transfer (Z_NO_FLUSH leg)

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

(* ===== fast-shadow insert (fastshadow bed, Gap7WrappersD, batch JG6) =====
   Context-shed Zify pre-hook: revert every arithmetic hypothesis into the
   goal, then clear every remaining clearable hypothesis, so each [lia]/[nia]
   pays zify preprocessing only for the arithmetic facts instead of the full
   context.
   The hook is restored to the Zify default at the END of this file, so
   importers see no net redefinition. *)
Ltac gap7wrappersd_fs_shed :=
  repeat match goal with
  | H : (_ <= _)%Z |- _ => revert H
  | H : (_ < _)%Z |- _ => revert H
  | H : (_ >= _)%Z |- _ => revert H
  | H : (_ > _)%Z |- _ => revert H
  | H : @eq Z _ _ |- _ => revert H
  | H : not _ |- _ => revert H
  | H : @eq bool _ _ |- _ => revert H
  | H : @eq nat _ _ |- _ => revert H
  | H : (_ <= _)%nat |- _ => revert H
  | H : (_ < _)%nat |- _ => revert H
  | H : (_ >= _)%nat |- _ => revert H
  | H : (_ > _)%nat |- _ => revert H
  | H : @eq N _ _ |- _ => revert H
  | H : (_ <= _)%N |- _ => revert H
  | H : (_ < _)%N |- _ => revert H
  | H : _ /\ _ |- _ => revert H
  | H : _ \/ _ |- _ => revert H
  | H : _ <-> _ |- _ => revert H
  end;
  repeat match goal with H : _ |- _ => clear H end.
Ltac Zify.zify_pre_hook ::= gap7wrappersd_fs_shed.
(* ===== end fast-shadow insert ===== *)
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Checksum Chunk Bits ZBitsIn Inflate DeflateSpec StepReach
  DynTblOkHolds.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  DeclIface ZRepro ZReproL0E ZReproL0C ZReproQ6A ZReproQ6I ZReproQ6W
  W2Stream Q6AsmSupport Q6RawTail Q6ZlibEntry Q6GzipEntry GtInfTotal
  GtAdlerChunk GtCrcChunk GtDecPump ZRRawShell ZrRawAsm ZREmitClose
  Gap7Strict.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Decapp DecappStrict
  Q6TailPos ZREmitDecode ZReproG6RawLen GtBodySelect BsAsm.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7WrappersD.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Spec.PngModel.Inflate14.

Import SymbolIdDeclIface.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   0.  Supply arithmetic: the deflateBound ceiling fits the u32 budget at
       the 64 MiB input cap, at every config.
   ========================================================================== *)


(** The raw-pump length reduction at q5's OPEN face — kept for
    provenance only: the bound landed first by the g6 route
    (ZReproG6RawLen.hrawlen, consumed at the wrapper's use site),
    so no proof consumes this lemma. *)

(* ==========================================================================
   0b. The POSITIVE zlib header step (was the Hzlentry residue; DISCHARGED
       here).  FDICT-clear now rides ZlibHeaderOk clause 4 (F2 landed).
   ========================================================================== *)

(** Single-bit tests through division: both directions of
    [Z.land v (2^p) = 0  <->  (v / 2^p) mod 2 = 0] at [0 <= v]. *)


(** The 2-byte LE hold, normalised. *)




(** [hold >> 4] decomposed: quotient/remainder form for the CINFO and
    FDICT reads. *)



(** THE POSITIVE ENTRY. *)
Lemma zr_zl_entry_pos14 : forall z b0 b1 rest obuf put cap,
  0 <= b0 < 256 -> 0 <= b1 < 256 ->
  ZlibHeaderOk b0 b1 ->
  Z.land (u8 b1) 32 = 0 ->
  exists z' dm,
    inf_step14 zr_ic (zrq zr_zi0 z ([b0; b1] ++ rest) 0 obuf put cap)
    = InfCont (zrq (zr_zist_t M_TYPE dm) z' ([b0; b1] ++ rest) 2 obuf put cap).
Proof.
  intros z b0 b1 rest obuf put cap Hb0 Hb1 HOK HFD.
  destruct HOK as (HCM & HCINFO & HCHK & _). (* 4th clause (FDICT, F2) discarded: the HFD premise carries it here *)
  unfold u8 in HCM, HCINFO, HCHK.
  rewrite (Z.mod_small b0 256) in HCM, HCINFO, HCHK by lia.
  rewrite (Z.mod_small b1 256) in HCHK by lia.
  assert (Hr : 0 <= zlen rest) by (unfold zlen; lia).
  assert (Hlen : zlen ([b0; b1] ++ rest) = 2 + zlen rest).
  { rewrite zlen_app. unfold zlen. cbn [length]. lia. }
  unfold inf_step14.
  replace (q_mode (zrq zr_zi0 z ([b0; b1] ++ rest) 0 obuf put cap))
    with M_HEAD by reflexivity.
  cbv iota.
  unfold inf_HEAD14. cbv zeta.
  replace (h_wrap (s_hdr (q_st (zrq zr_zi0 z ([b0; b1] ++ rest) 0 obuf put cap))))
    with 5 by reflexivity.
  change (5 =? 0) with false. cbv beta iota.
  match goal with |- context [inf_nb 16 ?br] =>
    replace br with {| br_in := zlist ([b0; b1] ++ rest);
                       br_have := zlen ([b0; b1] ++ rest) - 0;
                       br_next := 0; br_hold := 0; br_bits := 0 |}
      by reflexivity end.
  rewrite inf_nb_pull2 by lia.
  replace (zlist ([b0; b1] ++ rest) 0) with b0 by reflexivity.
  replace (zlist ([b0; b1] ++ rest) (0 + 1)) with b1 by reflexivity.
  cbn [br_hold br_bits br_in br_next br_have].
  rewrite (zr_hold2_val b0 b1).
  replace (Z.land 5 2) with 0 by reflexivity.
  change (0 =? 0) with true. cbn [negb andb].
  replace (Z.land 5 1) with 1 by reflexivity.
  change (1 =? 0) with false. cbn [orb].
  (* FCHECK: passes by clause 3 *)
  match goal with |- context [if negb (?T =? 0) then _ else _] =>
    destruct (Z.eqb_spec T 0) as [EF|EF] end.
  2:{ exfalso. apply EF.
      unfold br_bits_of. cbn [br_hold].
      rewrite (zr_hold2_land255 b0 b1 Hb0 Hb1).
      rewrite (zr_hold2_shr8 b0 b1 Hb0 Hb1).
      rewrite Z.shiftl_mul_pow2 by lia.
      change (2 ^ 8) with 256.
      exact HCHK. }
  cbn [negb].
  (* CM: passes by clause 1 *)
  match goal with |- context [if negb (?C =? Z_DEFLATED) then _ else _] =>
    destruct (Z.eqb_spec C Z_DEFLATED) as [EC|EC] end.
  2:{ exfalso. apply EC.
      unfold br_bits_of. cbn [br_hold].
      rewrite (zr_hold2_land15 b0 b1 Hb0 Hb1).
      unfold Z_DEFLATED.
      rewrite <- HCM.
      change 15 with (Z.ones 4).
      rewrite Z.land_ones by lia.
      change (2 ^ 4) with 16. reflexivity. }
  cbn [negb]. cbv zeta.
  replace (w_wbits (s_win (q_st (zrq zr_zi0 z ([b0; b1] ++ rest) 0 obuf put cap))))
    with 15 by reflexivity.
  change (15 =? 0) with false. cbv beta iota.
  (* the window test: CINFO <= 7 makes len <= 15 *)
  unfold br_dropbits. cbn [br_hold br_bits].
  rewrite (zr_hold2_shr4 b0 b1 Hb0 Hb1).
  unfold br_bits_of. cbn [br_hold].
  rewrite (zr_hold2_cinfo b0 b1 Hb0 Hb1).
  assert (HCsh : b0 / 16 = Z.shiftr b0 4)
    by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  replace (w_wbits (s_win (q_st (zrq zr_zi0 z ([b0; b1] ++ rest) 0 obuf put cap))))
    with 15 by reflexivity.
  match goal with |- context [if ?T1 || ?T2 then _ else _] =>
    replace T1 with false; [replace T2 with false|] end.
  2:{ symmetry. apply Z.ltb_ge. lia. }
  2:{ symmetry. apply Z.ltb_ge. lia. }
  cbn [orb]. cbv beta iota.
  (* FDICT: clear by the premise *)
  match goal with |- context [if Z.land ?H 512 =? 0 then M_TYPE else M_DICTID] =>
    replace (Z.land H 512) with 0 end.
  2:{ symmetry.
      apply (zr_hold2_fdict b0 b1 Hb0 Hb1).
      exact HFD. }
  change (0 =? 0) with true. cbv beta iota.
  (* the pass arm: assemble the explicit post-header state *)
  do 2 eexists.
  f_equal.
  lazy [qmode qcheck qset_br qset_st qset_z set_mode set_flags
        set_dmax set_wbits br_initbits zrq zr_zist_t zr_zi0
        q_st q_z q_br q_ob q_in q_out q_ret
        br_in br_have br_next br_hold br_bits
        s_hdr s_win s_cur s_tab s_bld s_hold s_bits
        h_mode h_last h_wrap h_havedict h_flags h_dmax h_check h_total
        h_head].
  f_equal; first [reflexivity | lia | f_equal; first [reflexivity | lia]].
Qed.

(* ==========================================================================
   1.  The selection heads — LANDED (train g1-gap7, closed 2026-08-22
).  The frozen Props live in-tree as
       GtBodySelect.{ZrBodySelect, ZrBodySelectHead0} (STRICT round-3
       texts, freeze lineage /
       ; ZrBodySelect carries the h_check/h_total
       conjuncts adopted at — it is the former local
       ZrBodySelectC copy VERBATIM, and ZrBodySelectHead0 the former
       local Head0 copy VERBATIM, both token-checked against the landed
       file at this edit) and the head proofs in
       BsAsm.{zr_body_select_holds, zr_body_select_head0_holds}.  The
       local provenance copies (incl. the PRE-re-freeze LAX
       ZrBodySelect) and the Section-Variable rows are DELETED — each
       wrapper poses the landed proof at its use site.
   ========================================================================== *)

(* ==========================================================================
   2.  The wrappers.
   ========================================================================== *)

(* Henough Hypothesis REMOVED — DISCHARGED: the freeze's ENOUGH residue
   (EnoughFits_STMT, the r4 lens_capped text, tree pin ) LANDED
   as EnoughFitsB14.enough_fits_capped_final in window g6-enoughfits
   (18 pure ADDs, FULLLOAD 1239; B14 pin —
   UNCONDITIONAL, Qed, PA closed, zero axioms), completing the g6
   commission recorded in the r4 addendum.  The
   three derivation sites consume the theorem BY TREE NAME. *)

(* Hrawlen Hypothesis REMOVED — DISCHARGED: g6's ZReproG6RawLen.hrawlen
   (landed in window q7-amend11 at the pin) proves the verbatim
   statement, and the wrapper consumes it in-proof at the use site.  The
   pump needs [zlen enc <= 4294967290] twice (ReachSt's avail_in
   ceiling; the entry band's budget) — both flow from the one [Hlen]. *)

(** STRICT-SUPPLY ROWS — RETIRED (were the three F-family interim
    Hypotheses Hrawstrict/Hzlstrict/Hgzstrict, freeze
): q5's stage-2 LANDED
    ZREmitDecode.{raw,zlib,gzip}_body_strict (), each of shape
      build_accepts_of_kraft_STMT -> EnoughFits_STMT -> <row text>
    with <row text> VERBATIM the retired rows' statements (verified
    token-identical at this edit), and
    Gap7Bridge.build_accepts_of_kraft_holds () closes the
    first premise.  Each wrapper now DERIVES its row in-proof from the
    landed pair applied to the landed
    EnoughFitsB14.enough_fits_capped_final — same in-context names,
    same consumption shapes. *)


(* --------------------------------------------------------------------------
   The zlib wrapper — CLOSED composition against the landed strict
   head (h_check/h_total conjuncts + the round-3 STRICT decode premise,
   lineage); the supply side is FULLY LANDED:
     [HselC]     — the selection head, posed in-proof from the LANDED
                   BsAsm.zr_body_select_holds : GtBodySelect.ZrBodySelect
                   (== the former local ZrBodySelectC, verbatim);
     [Hzlstrict] — DERIVED in-proof (was INTERIM): the landed
                   ZREmitDecode.zlib_body_strict () applied to
                   the landed bridge () + the landed
                   EnoughFitsB14.enough_fits_capped_final; subsumes
                   the lax ZREmitDecode.zlib_body_valid consumption
                   whole.
   Retired: [Hzltail] — CONSUMED from the LANDED Q6TailPos.zr_zl_tail_pos
   (q6 F5: ratified spelling + ONE nil-fixed-point premise, discharged
   at the entry-pinned h_check = adler32_z 0 true [] via
   Q6TailPos.adler32_z_nil_fix + adval_init);
   [Hzlfdict] — DISCHARGED, F2 landed DeclIface 4th clause
   (projected in-proof from the face's ZlibHeaderOk conjunct);
   [Hdecapp] — supplied by DecappStrict.dec_stream_from_strict_app;
   [Hzlpad] — folded into [Hzlstrict].
   -------------------------------------------------------------------------- *)

(* Variable HselC REMOVED (GAP7 finale): the head landed with the
   g1-gap7 train; the zlib and gzip wrappers pose
   BsAsm.zr_body_select_holds as [HselC] at their use sites. *)

(* Hdecapp Hypothesis REMOVED: supplied by the LANDED strict twin
   DecappStrict.dec_stream_from_strict_app (+ the same forced mod-8
   premise, discharged per call site by Decapp.bytes_bits_mod8 -- both
   T instances are bytes_bits of a trailer; the strict counterexample
   twin is machine-checked in DecappStrict). *)

(* Hzlfdict Hypothesis REMOVED — F2 ANSWERED the statement-level finding
   (ZlibHeaderOk carried no FDICT-clear clause; an FDICT-set header passed
   all three while the machine forked to M_DICTID/Z_NEED_DICT): DeclIface's
   ZlibHeaderOk now carries the 4th clause [Z.land (u8 b1) 32 = 0]
   (q5-emitter, landed 2026-08-21), and the wrapper projects it from the
   face's ZlibHeaderOk conjunct at the entry-step call site. *)

(* INTERIM STRICT-SUPPLY ROW (zlib) — RETIRED: landed as
   ZREmitDecode.zlib_body_strict (row text VERBATIM); derived in-proof
   below. *)


(* --------------------------------------------------------------------------
   The gzip wrapper.  The ENTRY is landed and positive
   (Q6GzipEntry.zr_gz_entry — the harness frame's header is the concrete
   [31;139;8;0;0;0;0;0;2;3], two composite steps to M_TYPE), so gzip
   carries exactly zlib's premise shape (supply FULLY LANDED):
     [Hgzstrict] — DERIVED in-proof (was INTERIM): the landed
                   ZREmitDecode.gzip_body_strict () applied to
                   the landed bridge () + the landed
                   EnoughFitsB14.enough_fits_capped_final; subsumes
                   the lax ZREmitDecode.gzip_body_valid consumption
                   whole.
   Retired: [Hgztail] — CONSUMED from the LANDED Q6TailPos.zr_gz_tail_pos
   (q6 F5: ratified spelling + ONE nil-fixed-point premise, discharged
   at the entry-pinned h_check = crc32_z 0 true 0 [] — a closed term in
   the crc word range — via Q6TailPos.crc32_z_nil_fix);
   [Hgzpad] — folded into [Hgzstrict].
   -------------------------------------------------------------------------- *)

(* INTERIM STRICT-SUPPLY ROW (gzip) — RETIRED: landed as
   ZREmitDecode.gzip_body_strict (row text VERBATIM); derived in-proof
   below. *)


(* fast-shadow: pure query elided (76.6s of the base lap; no proof-state or .vo effect): Set Printing Width 2000 *)
(* fast-shadow: pure query elided (76.6s of the base lap; no proof-state or .vo effect): Print Assumptions ZRepro_Pump_l1_raw_holds *)
(* fast-shadow: pure query elided (76.6s of the base lap; no proof-state or .vo effect): Print Assumptions ZRepro_Pump_default_zlib_holds *)
(* fast-shadow: pure query elided (76.6s of the base lap; no proof-state or .vo effect): Print Assumptions ZRepro_Pump_l9_gzip_holds *)

(* fast-shadow restore: importers of this file see the Zify default hook. *)
Ltac Zify.zify_pre_hook ::= idtac.

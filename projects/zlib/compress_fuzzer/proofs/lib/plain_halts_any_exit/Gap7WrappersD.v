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
Import SymbolIdDeclIface.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   0.  Supply arithmetic: the deflateBound ceiling fits the u32 budget at
       the 64 MiB input cap, at every config.
   ========================================================================== *)

Lemma zr_bound_fits : forall wb n,
  0 <= n < 67108864 ->
  zr_deflate_bound wb n <= 4294967290.
Proof.
  intros wb n [Hn0 Hn].
  unfold zr_deflate_bound, zr_wraplen.
  rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ 12) with 4096.
  change (2 ^ 14) with 16384.
  change (2 ^ 25) with 33554432.
  assert (H12 : n / 4096 <= n) by (apply Z.div_le_upper_bound; lia).
  assert (H14 : n / 16384 <= n) by (apply Z.div_le_upper_bound; lia).
  assert (H25 : n / 33554432 <= n) by (apply Z.div_le_upper_bound; lia).
  destruct (wb <? 0); [lia | destruct (15 <? wb); lia].
Qed.

(** The raw-pump length reduction at q5's OPEN face — kept for
    provenance only: the bound landed first by the g6 route
    (ZReproG6RawLen.hrawlen, consumed at the wrapper's use site),
    so no proof consumes this lemma. *)
Lemma rawlen_from_face : ZRepro_Emitter_l1_raw ->
  forall x enc, ZR_Input x -> zr_deflate 1 (-15) x = Some enc ->
  zlen enc <= 4294967290.
Proof.
  intros HFace x enc Hx Hdef.
  destruct (HFace x Hx) as (enc' & Hdef' & Hbound & _ & _).
  rewrite Hdef in Hdef'. injection Hdef' as <-.
  assert (Hxr : 0 <= zlen x < 67108864)
    by (split; [unfold zlen; lia | exact (proj2 Hx)]).
  pose proof (zr_bound_fits (-15) (zlen x) Hxr). lia.
Qed.

(* ==========================================================================
   0b. The POSITIVE zlib header step (was the Hzlentry residue; DISCHARGED
       here).  FDICT-clear now rides ZlibHeaderOk clause 4 (F2 landed).
   ========================================================================== *)

(** Single-bit tests through division: both directions of
    [Z.land v (2^p) = 0  <->  (v / 2^p) mod 2 = 0] at [0 <= v]. *)
Lemma zr_land_pow2_of_div : forall v p,
  0 <= v -> 0 <= p ->
  (v / 2 ^ p) mod 2 = 0 ->
  Z.land v (2 ^ p) = 0.
Proof.
  intros v p Hv Hp Hb.
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.eqb_spec n p) as [->|Hne].
  - rewrite Z.pow2_bits_true by lia.
    rewrite andb_true_r.
    destruct (Z.testbit v p) eqn:E; [|reflexivity].
    apply Z.testbit_true in E; [|lia]. lia.
  - rewrite Z.pow2_bits_false by lia.
    apply andb_false_r.
Qed.

Lemma zr_div_of_land_pow2 : forall v p,
  0 <= v -> 0 <= p ->
  Z.land v (2 ^ p) = 0 ->
  (v / 2 ^ p) mod 2 = 0.
Proof.
  intros v p Hv Hp HL.
  pose proof (Z.mod_pos_bound (v / 2 ^ p) 2 ltac:(lia)) as HM.
  destruct (Z.eqb_spec ((v / 2 ^ p) mod 2) 1) as [E1|E1]; [|lia].
  exfalso.
  assert (ET : Z.testbit v p = true)
    by (apply Z.testbit_true; [lia | exact E1]).
  assert (EB : Z.testbit (Z.land v (2 ^ p)) p = true)
    by (rewrite Z.land_spec, ET, Z.pow2_bits_true by lia; reflexivity).
  rewrite HL, Z.bits_0 in EB. discriminate.
Qed.

(** The 2-byte LE hold, normalised. *)
Lemma zr_hold2_val : forall b0 b1,
  Z.shiftl b0 0 + Z.shiftl b1 8 = b0 + b1 * 256.
Proof.
  intros b0 b1.
  rewrite Z.shiftl_0_r, Z.shiftl_mul_pow2 by lia.
  change (2 ^ 8) with 256. lia.
Qed.

Lemma zr_hold2_land255 : forall b0 b1,
  0 <= b0 < 256 -> 0 <= b1 < 256 ->
  Z.land (b0 + b1 * 256) (Z.shiftl 1 8 - 1) = b0.
Proof.
  intros b0 b1 H0 H1.
  change (Z.shiftl 1 8 - 1) with (Z.ones 8).
  rewrite Z.land_ones by lia.
  change (2 ^ 8) with 256.
  rewrite Z.mod_add by lia.
  apply Z.mod_small. lia.
Qed.

Lemma zr_hold2_shr8 : forall b0 b1,
  0 <= b0 < 256 -> 0 <= b1 < 256 ->
  Z.shiftr (b0 + b1 * 256) 8 = b1.
Proof.
  intros b0 b1 H0 H1.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 8) with 256.
  rewrite Z.div_add by lia.
  rewrite Z.div_small by lia. lia.
Qed.

Lemma zr_hold2_land15 : forall b0 b1,
  0 <= b0 < 256 -> 0 <= b1 < 256 ->
  Z.land (b0 + b1 * 256) (Z.shiftl 1 4 - 1) = b0 mod 16.
Proof.
  intros b0 b1 H0 H1.
  change (Z.shiftl 1 4 - 1) with (Z.ones 4).
  rewrite Z.land_ones by lia.
  change (2 ^ 4) with 16.
  replace (b0 + b1 * 256) with (b0 + (b1 * 16) * 16) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

(** [hold >> 4] decomposed: quotient/remainder form for the CINFO and
    FDICT reads. *)
Lemma zr_hold2_shr4 : forall b0 b1,
  0 <= b0 < 256 -> 0 <= b1 < 256 ->
  Z.shiftr (b0 + b1 * 256) 4 = b0 / 16 + b1 * 16.
Proof.
  intros b0 b1 H0 H1.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 4) with 16.
  replace (b0 + b1 * 256) with (b0 + (b1 * 16) * 16) by lia.
  rewrite Z.div_add by lia. lia.
Qed.

Lemma zr_hold2_cinfo : forall b0 b1,
  0 <= b0 < 256 -> 0 <= b1 < 256 ->
  Z.land (b0 / 16 + b1 * 16) (Z.shiftl 1 4 - 1) = b0 / 16.
Proof.
  intros b0 b1 H0 H1.
  change (Z.shiftl 1 4 - 1) with (Z.ones 4).
  rewrite Z.land_ones by lia.
  change (2 ^ 4) with 16.
  rewrite Z.mod_add by lia.
  apply Z.mod_small.
  split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma zr_hold2_fdict : forall b0 b1,
  0 <= b0 < 256 -> 0 <= b1 < 256 ->
  Z.land (u8 b1) 32 = 0 ->
  Z.land (b0 / 16 + b1 * 16) 512 = 0.
Proof.
  intros b0 b1 H0 H1 HFD.
  assert (Hq : 0 <= b0 / 16 < 16)
    by (split; [apply Z.div_le_lower_bound; lia
               | apply Z.div_lt_upper_bound; lia]).
  unfold u8 in HFD.
  rewrite (Z.mod_small b1 256) in HFD by lia.
  change 32 with (2 ^ 5) in HFD.
  apply (zr_div_of_land_pow2 b1 5 ltac:(lia) ltac:(lia)) in HFD.
  change (2 ^ 5) with 32 in HFD.
  change 512 with (2 ^ 9).
  apply zr_land_pow2_of_div; [lia | lia |].
  change (2 ^ 9) with 512.
  replace (b0 / 16 + b1 * 16) with
    (b0 / 16 + (b1 mod 32) * 16 + (b1 / 32) * 512) by (rewrite (Z.div_mod b1 32) at 2 by lia; lia).
  rewrite Z.div_add by lia.
  rewrite (Z.div_small (b0 / 16 + b1 mod 32 * 16) 512)
    by (pose proof (Z.mod_pos_bound b1 32 ltac:(lia)); lia).
  rewrite Z.add_0_l. exact HFD.
Qed.

(** THE POSITIVE ENTRY. *)
Lemma zr_zl_entry_pos : forall z b0 b1 rest obuf put cap,
  0 <= b0 < 256 -> 0 <= b1 < 256 ->
  ZlibHeaderOk b0 b1 ->
  Z.land (u8 b1) 32 = 0 ->
  exists z' dm,
    inf_step zr_ic (zrq zr_zi0 z ([b0; b1] ++ rest) 0 obuf put cap)
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
  unfold inf_step.
  replace (q_mode (zrq zr_zi0 z ([b0; b1] ++ rest) 0 obuf put cap))
    with M_HEAD by reflexivity.
  cbv iota.
  unfold inf_HEAD. cbv zeta.
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

Theorem ZRepro_Pump_l1_raw_holds : ZRepro_Pump_l1_raw.
Proof.
  unfold ZRepro_Pump_l1_raw, ZR_PumpSucceeds.
  intros x enc flush cap Hx Hdef HF Hcap Hcap32.
  assert (Hxn : 0 <= zlen x) by (unfold zlen; lia).
  destruct (zr_emitter_l1_raw_frame x enc Hx Hdef) as [HBy _].
  pose proof (ZReproG6RawLen.hrawlen x enc Hx Hdef) as Hlen.
  assert (Hln : 0 <= zlen enc) by (unfold zlen; lia).
  (* reduce to the Z_FINISH run *)
  assert (HFIN : exists y, zr_inflate Z_FINISH (-15) cap enc = Some y).
  2:{ destruct HFIN as [y Hy]. exists y.
      destruct HF as [-> | ->].
      - apply zr_inflate_transfer;
          [ unfold Z_NO_FLUSH, Z_BLOCK; lia
          | unfold Z_NO_FLUSH, Z_TREES; lia
          | exact Hy ].
      - exact Hy. }
  (* the STRICT decode success — q5's landed ZERO-PREMISE final
     (ZREmitDecode.raw_body_strict_holds; the former in-proof
     derivation via Gap7Bridge + EnoughFitsB14 is folded there) *)
  pose proof ZREmitDecode.raw_body_strict_holds as Hrawstrict.
  destruct (Hrawstrict x enc Hx Hdef) as (rem & EDS).
  (* open the driver *)
  unfold zr_inflate.
  rewrite zr_init_m15.
  unfold zr_inf_call.
  match goal with |- context [inflate_model ?a] => set (A := a) end.
  set (Q0 := inf_st0 A).
  set (C0 := inf_ctx A).
  assert (HC0 : zr_cflush_ok C0).
  { unfold zr_cflush_ok, C0, A, inf_ctx. cbn [n_flush g_flush].
    unfold Z_FINISH, Z_BLOCK, Z_TREES. split; lia. }
  (* totality at the entry record *)
  assert (HR : ReachSt Q0).
  { apply (reach_entry_fresh zr_rz0 zr_ri0 (-15) A zr_init_m15).
    - reflexivity.
    - exact (zlist_bytes enc HBy).
    - unfold A. cbn [g_avail_in]. lia.
    - unfold A. cbn [g_avail_out]. lia.
    - intros j. unfold A. cbn [g_outbuf]. cbv [zzero zconst]. lia. }
  destruct (inflate_model_total_reach DynTblOk_holds A
              eq_refl eq_refl eq_refl HR) as (r & Hrun & _).
  (* the entry band at Q0 *)
  assert (Hentry : zr_body_entry Q0).
  { unfold zr_body_entry.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
             (conj _ (conj _ (conj _ _)))))))))).
    - exact (zr_init_brwf enc HBy).
    - unfold Q0, A. cbn. lia.
    - unfold Q0, A. cbn. lia.
    - reflexivity.
    - exact Hcap32.
    - reflexivity.
    - unfold Q0, A. cbn. lia.
    - reflexivity.
    - reflexivity.
    - apply zr_haligned_bits0. reflexivity.
    - exact (zr_init_budget enc Hlen). }
  (* the dec premise at Q0 *)
  assert (Hdec : dec_stream_from_strict (br_stream (q_br Q0))
                   (ob_slice (q_ob Q0) 0 (o_put (q_ob Q0)))
                 = Some (x, rem)).
  { replace (br_stream (q_br Q0)) with (bytes_bits enc)
      by (symmetry; exact (zr_br_stream_at [] enc 0)).
    replace (ob_slice (q_ob Q0) 0 (o_put (q_ob Q0))) with (@nil Z)
      by reflexivity.
    exact EDS. }
  (* THE SELECTION — the LANDED raw-lane head proof, posed here *)
  pose proof BsAsm.zr_body_select_head0_holds as Hsel0.
  destruct (Hsel0 C0 Q0 x rem HC0 Hentry
              ltac:(reflexivity) ltac:(reflexivity)
              Hdec ltac:(exact Hcap))
    as (k & q' & HI & Hrem & HS & Hwf' & Hop' & Hol' & Hsum & Hm' & Hl'
        & Hr' & Hin' & Hout' & Hwr' & Hfl' & Hws' & Hwh' & Hsn' & Hha'
        & Hbud').
  (* the raw tail *)
  destruct (zr_raw_tail C0 q' HC0
              ltac:(rewrite Hwr'; reflexivity) Hm' Hl')
    as (q2 & HT & Hret2 & Hob2 & Hmd2 & Hwsz2).
  pose proof (zr_iterloop_compose k C0 Q0 q' 2 _ HI HT) as HC.
  (* the driver's own loop, resolved by totality + uniqueness *)
  pose proof Hrun as HrunG.
  unfold inflate_model in Hrun.
  cbv beta zeta in Hrun.
  replace (g_state_null A || g_out_null A
           || g_in_null A && negb (g_avail_in A =? 0))%bool
    with false in Hrun by reflexivity.
  cbv beta iota in Hrun.
  change (inf_st0 A) with Q0 in Hrun.
  change (inf_ctx A) with C0 in Hrun.
  destruct (inf_loop (inf_fuel Q0) C0 Q0) as [s|] eqn:ELOOP;
    [| discriminate Hrun].
  assert (Es : s = InfLeave q2)
    by (exact (zr_loop_uniq _ _ _ _ _ _ ELOOP HC)).
  subst s.
  cbv beta iota in Hrun.
  destruct (inf_leave C0 q2) as [q3 r0] eqn:ELV.
  cbv beta iota in Hrun.
  injection Hrun as Hr. subst r.
  destruct (zr_leave_done_fin C0 q2 ltac:(reflexivity) Hret2 Hmd2
              ltac:(rewrite Hwsz2, Hws'; reflexivity))
    as (Hr3 & _).
  rewrite ELV in Hr3. cbn [snd] in Hr3. subst r0.
  rewrite HrunG.
  cbn [r_ret r_q].
  rewrite Z.eqb_refl.
  eexists. reflexivity.
Qed.

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

Theorem ZRepro_Pump_default_zlib_holds : ZRepro_Pump_default_zlib.
Proof.
  unfold ZRepro_Pump_default_zlib, ZR_PumpSucceeds.
  intros x enc flush cap Hx Hdef HF Hcap Hcap32.
  assert (Hxn : 0 <= zlen x) by (unfold zlen; lia).
  (* supply: the landed emitter face + Some-injection *)
  destruct (ZRepro_Emitter_default_zlib_holds x Hx)
    as (enc' & Hdef' & Hbound & HBy & HFr).
  rewrite Hdef in Hdef'. injection Hdef' as <-.
  destruct HFr as (b0 & b1 & body & ad & Hfr & Hhok & HBD & Htm).
  unfold ZlibFramed in Hfr.
  clear HBD.
  (* Strict supply (Hzlstrict = the strict body_valid mirror) — q5's
     landed ZERO-PREMISE final ZREmitDecode.zlib_body_strict_holds
     (the Gap7Bridge + EnoughFitsB14 derivation folded there): ONE row
     supplies the decode success (now STRICT, feeding the round-3
     head) and the sub-byte pad.  Its existential body is
     identified with the face's by framing injectivity (zr_app_inj
     twice: equal-length [b0;b1] prefixes, then equal-length be32
     tails) — the F4 consumption shape, unchanged. *)
  pose proof ZREmitDecode.zlib_body_strict_holds as Hzlstrict.
  destruct (Hzlstrict x Hx)
    as (encV & b0V & b1V & bodyV & adV & HdefV & HfrV & _ & HvalV).
  rewrite Hdef in HdefV. injection HdefV as <-.
  unfold ZlibFramed in HfrV.
  rewrite Hfr in HfrV.
  destruct (zr_app_inj [b0; b1] [b0V; b1V] _ _ eq_refl HfrV) as [_ Htl].
  assert (HLb : length body = length bodyV).
  { pose proof (f_equal (@length Z) Htl) as HLL.
    rewrite !length_app in HLL.
    change (length (be32 ad)) with 4%nat in HLL.
    change (length (be32 adV)) with 4%nat in HLL.
    lia. }
  destruct (zr_app_inj body bodyV (be32 ad) (be32 adV) HLb Htl)
    as [HbodyE _].
  subst bodyV.
  destruct HvalV as (remb & EDS & Hpadb).
  set (REST := body ++ be32 ad) in *.
  assert (Hlen : zlen enc <= 4294967290).
  { assert (Hxr : 0 <= zlen x < 67108864)
      by (split; [lia | exact (proj2 Hx)]).
    pose proof (zr_bound_fits 15 (zlen x) Hxr). lia. }
  assert (Hln : 0 <= zlen enc) by (unfold zlen; lia).
  (* byte facts through the frame split *)
  pose proof HBy as HBy2.
  rewrite Hfr in HBy2.
  apply Forall_app in HBy2. destruct HBy2 as [Hhd _].
  assert (Hb0 : 0 <= b0 < 256) by (exact (Forall_inv Hhd)).
  assert (Hb1 : 0 <= b1 < 256)
    by (exact (Forall_inv (Forall_inv_tail Hhd))).
  (* the trailer value's range *)
  assert (HAD : 0 <= ad < 4294967296).
  { rewrite Htm. unfold adler_init.
    assert (HV : AdVal (adler32_z (adler32_z 0 true []) false x)).
    { apply adval_step; [exact adval_init|].
      split; [| intro K; discriminate K].
      intros b Hb. destruct Hx as [HxF _].
      rewrite Forall_forall in HxF. exact (HxF b Hb). }
    exact (proj2 HV). }
  (* reduce to the Z_FINISH run *)
  assert (HFIN : exists y, zr_inflate Z_FINISH 15 cap enc = Some y).
  2:{ destruct HFIN as [y Hy]. exists y.
      destruct HF as [-> | ->].
      - apply zr_inflate_transfer;
          [ unfold Z_NO_FLUSH, Z_BLOCK; lia
          | unfold Z_NO_FLUSH, Z_TREES; lia
          | exact Hy ].
      - exact Hy. }
  (* open the driver *)
  unfold zr_inflate.
  rewrite zr_init_15'.
  unfold zr_inf_call.
  match goal with |- context [inflate_model ?a] => set (A := a) end.
  assert (HR : ReachSt (inf_st0 A)).
  { apply (reach_entry_fresh zr_zz0 zr_zi0 15 A zr_init_15').
    - reflexivity.
    - exact (zlist_bytes enc HBy).
    - unfold A. cbn [g_avail_in]. lia.
    - unfold A. cbn [g_avail_out]. lia.
    - intros j. unfold A. cbn [g_outbuf]. cbv [zzero zconst]. lia. }
  destruct (inflate_model_total_reach DynTblOk_holds A
              eq_refl eq_refl eq_refl HR) as (r & Hrun & _).
  (* the driver's entry state, in the walk's zrq spelling *)
  assert (E0 : inf_st0 A = zrq zr_zi0 zr_zz0 ([b0; b1] ++ REST) 0 zzero 0 cap).
  { rewrite <- Hfr.
    unfold A, inf_st0, zrq.
    cbn [g_st g_z g_inbuf g_avail_in g_next_in g_outbuf g_next_out
         g_avail_out g_flush].
    replace (h_mode (s_hdr zr_zi0)) with M_HEAD by reflexivity.
    cbn [s_hold s_bits].
    f_equal; f_equal; first [reflexivity | lia
                            | f_equal; first [reflexivity | lia]]. }
  assert (EC : inf_ctx A = zr_ic) by reflexivity.
  assert (HCfl : zr_cflush_ok zr_ic).
  { unfold zr_cflush_ok, zr_ic. cbn [n_flush].
    unfold Z_FINISH, Z_BLOCK, Z_TREES. split; lia. }
  (* the header step (FDICT-clear projected from Hhok's 4th clause, F2) *)
  destruct (zr_zl_entry_pos zr_zz0 b0 b1 REST zzero 0 cap Hb0 Hb1 Hhok
              (proj2 (proj2 (proj2 Hhok))))
    as (z1 & dm & Hstep).
  set (q1 := zrq (zr_zist_t M_TYPE dm) z1 ([b0; b1] ++ REST) 2 zzero 0 cap).
  pose proof (inf_iter_one zr_ic _ q1 Hstep) as HI1.
  (* length bookkeeping *)
  assert (HLE : zlen ([b0; b1] ++ REST) = zlen enc) by (rewrite Hfr; reflexivity).
  assert (HL2 : zlen ([b0; b1] ++ REST) = 2 + zlen REST).
  { rewrite zlen_app. replace (zlen [b0; b1]) with 2 by reflexivity. lia. }
  assert (HRn : 0 <= zlen REST) by (unfold zlen; lia).
  (* the entry band at the post-header state *)
  assert (Hwf1 : br_wf (q_br q1)).
  { unfold q1, zrq, br_wf. cbn [q_br br_bits br_hold br_have br_in].
    refine (conj _ (conj _ (conj _ _))).
    - lia.
    - change (Z.shiftl 1 0) with 1. lia.
    - lia.
    - intros i. apply zlist_bytes. rewrite <- Hfr. exact HBy. }
  assert (Hentry1 : zr_body_entry q1).
  { unfold zr_body_entry.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
             (conj _ (conj _ (conj _ _)))))))))).
    - exact Hwf1.
    - unfold q1, zrq. cbn. lia.
    - unfold q1, zrq. cbn. lia.
    - unfold q1, zrq. cbn. lia.
    - exact Hcap32.
    - reflexivity.
    - unfold q1, zrq. cbn. lia.
    - reflexivity.
    - reflexivity.
    - apply zr_haligned_bits0. reflexivity.
    - unfold q1, zrq. cbn [q_br br_have br_bits].
      change (0 / 8) with 0. lia. }
  (* the stream view at the post-header state *)
  assert (EBR : q_br q1 = {| br_in := zlist ([b0; b1] ++ REST);
                             br_have := zlen REST;
                             br_next := zlen [b0; b1];
                             br_hold := 0; br_bits := 0 |}).
  { unfold q1, zrq. cbn [q_br].
    f_equal; first [reflexivity | lia]. }
  assert (EST : br_stream (q_br q1) = bytes_bits REST)
    by (rewrite EBR; exact (zr_br_stream_at [b0; b1] REST 0)).
  assert (Hdec1 : dec_stream_from_strict (br_stream (q_br q1))
                    (ob_slice (q_ob q1) 0 (o_put (q_ob q1)))
                  = Some (x, remb ++ bytes_bits (be32 ad))).
  { rewrite EST. unfold REST.
    rewrite w2_bytes_bits_app.
    replace (ob_slice (q_ob q1) 0 (o_put (q_ob q1))) with (@nil Z)
      by reflexivity.
    exact (DecappStrict.dec_stream_from_strict_app _ _ _ _ _
             (Decapp.bytes_bits_mod8 _) EDS). }
  (* THE SELECTION — the LANDED amended head proof, posed here *)
  pose proof BsAsm.zr_body_select_holds as HselC.
  destruct (HselC zr_ic q1 x (remb ++ bytes_bits (be32 ad))
              HCfl Hentry1 ltac:(reflexivity) Hdec1 ltac:(exact Hcap))
    as (k & q' & HI & Hrem & HS & Hwf' & Hop' & Hol' & Hsum & Hm' & Hl'
        & Hr' & Hin' & Hout' & Hwr' & Hfl' & Hws' & Hwh' & Hsn' & Hha'
        & Hbud' & Hck' & Htot').
  (* the check tail — CONSUMED from the LANDED Q6TailPos.zr_zl_tail_pos
     (q6 F5, the ratified Hzltail spelling + ONE nil-fixed-point
     premise).
     q6 ratification (INBOX-1141, F5; folded here from the retired
     Hypothesis site — the analysis is retained, not deleted): the TIE
     premise [q_out q = o_put + o_left] is the LOAD-BEARING piece — do
     not simplify away.  The machine's M_CHECK update span is
     [q_out - o_left] ([q_out] being the SAVED call-entry avail_out,
     frame-preserved through the walk by q6's frame lemmas), and the
     tie pins that span to exactly [o_put] = THE WHOLE SLICE.  That
     makes the value equations STATE-GENERAL over arbitrary [h_check]:
     the machine compares [upd_check h_check (whole slice)] —
     byte-for-byte the premise's LHS — at ANY premise-satisfying [q],
     honest [h_check] or garbage, so no honesty premise on [h_check]
     is needed (the premise carrier contains the fact it seems to
     omit).  DROP THE TIE AND THE STATEMENT IS FALSE at partial-span
     states (the machine would compare a span-update while the premise
     speaks about the slice-update).  Vocabulary ratified (q6 pt 2):
     [be32] for the zlib adler trailer and [zr_le32 ++ zr_le32] for
     gzip crc/isize match the face constructors exactly; [crc32_z]'s
     (false, 0) flags match the model's call shape; the ISIZE mask
     [Z.land (h_total + o_put) 4294967295] is the machine's own
     spelling with the tie again pinning [o_put] as the this-call
     span; the pad decomposition (remb ++ trailer bits, |remb| < 8)
     is the right shape, its suppliers emitter-side (now the interim
     strict rows / q5's stage-2 siblings).  Minimal conclusions
     correct for the (c)-face (q6 pt 3): no [ob_slice] export (the
     pump concludes EXISTENCE, not identity); ret/mode/wsize are
     exactly [zr_leave_done_fin]'s demand; the [zr_ic] pinning is by
     design (pump wrappers run at the one-shot ctx).
     THE AMENDMENT (q6's own o_put = 0 falsification, INBOX-1730,
     option A ratified): inf_CHECK skips the update at wrote = 0 and
     compares the RAW [h_check], so each landed tail carries ONE added
     premise — the running check is a fixed point of the empty update.
     Discharged HERE from the entry pin: zlib's post-entry h_check is
     adler32_z 0 true [] (Q6ZlibEntry:49 canonical form, threaded to
     q' by the head's h_check-preservation conjunct), a canonical
     AdVal, so Q6TailPos.adler32_z_nil_fix + adval_init close it. *)
  destruct (Q6TailPos.zr_zl_tail_pos q' remb ad
              ltac:(rewrite Hwr'; reflexivity)
              ltac:(rewrite Hfl'; reflexivity)
              Hm' Hl' Hwf' Hha'
              ltac:(rewrite Hout', Hsum; unfold q1, zrq; cbn; lia)
              Hrem
              Hpadb
              HAD
              ltac:(rewrite Hfl', Hck', HS;
                    replace (h_flags (s_hdr (q_st q1))) with 0
                      by reflexivity;
                    replace (h_check (s_hdr (q_st q1)))
                      with (adler32_z 0 true []) by reflexivity;
                    unfold upd_check;
                    change (0 =? 0) with true; cbv iota;
                    rewrite Htm; unfold adler_init; reflexivity)
              ltac:(rewrite Hfl', Hck';
                    replace (h_flags (s_hdr (q_st q1))) with 0
                      by reflexivity;
                    replace (h_check (s_hdr (q_st q1)))
                      with (adler32_z 0 true []) by reflexivity;
                    unfold upd_check;
                    change (0 =? 0) with true; cbv iota;
                    exact (Q6TailPos.adler32_z_nil_fix _ adval_init)))
    as (n & q2 & HL & Hret2 & Hmd2 & Hwsz2).
  (* compose the run *)
  assert (HIall : inf_iter (1 + k) zr_ic
                    (zrq zr_zi0 zr_zz0 ([b0; b1] ++ REST) 0 zzero 0 cap)
                  = Some q').
  { rewrite (inf_iter_add 1 k zr_ic _ q1 HI1). exact HI. }
  pose proof (zr_iterloop_compose (1 + k) zr_ic _ q' n _ HIall HL) as HC.
  (* resolve the driver's loop *)
  pose proof Hrun as HrunG.
  unfold inflate_model in Hrun.
  cbv beta zeta in Hrun.
  replace (g_state_null A || g_out_null A
           || g_in_null A && negb (g_avail_in A =? 0))%bool
    with false in Hrun by reflexivity.
  cbv beta iota in Hrun.
  rewrite E0, EC in Hrun.
  destruct (inf_loop
              (inf_fuel (zrq zr_zi0 zr_zz0 ([b0; b1] ++ REST) 0 zzero 0 cap))
              zr_ic (zrq zr_zi0 zr_zz0 ([b0; b1] ++ REST) 0 zzero 0 cap))
    as [s|] eqn:ELOOP;
    [| discriminate Hrun].
  assert (Es : s = InfLeave q2)
    by (exact (zr_loop_uniq _ _ _ _ _ _ ELOOP HC)).
  subst s.
  cbv beta iota in Hrun.
  destruct (inf_leave zr_ic q2) as [q3 r0] eqn:ELV.
  cbv beta iota in Hrun.
  injection Hrun as Hr. subst r.
  destruct (zr_leave_done_fin zr_ic q2 ltac:(reflexivity) Hret2 Hmd2
              ltac:(rewrite Hwsz2, Hws'; reflexivity))
    as (Hr3 & _).
  rewrite ELV in Hr3. cbn [snd] in Hr3. subst r0.
  rewrite HrunG.
  cbn [r_ret r_q].
  rewrite Z.eqb_refl.
  eexists. reflexivity.
Qed.

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

Theorem ZRepro_Pump_l9_gzip_holds : ZRepro_Pump_l9_gzip.
Proof.
  unfold ZRepro_Pump_l9_gzip, ZR_PumpSucceeds.
  intros x enc flush cap Hx Hdef HF Hcap Hcap32.
  assert (Hxn : 0 <= zlen x) by (unfold zlen; lia).
  (* supply: the landed emitter face + Some-injection *)
  destruct (ZRepro_Emitter_l9_gzip_holds x Hx)
    as (enc' & Hdef' & Hbound & HBy & HFr).
  rewrite Hdef in Hdef'. injection Hdef' as <-.
  destruct HFr as (body & Heq & HBD).
  clear HBD.
  (* Strict supply (Hgzstrict = the strict body_valid mirror) — q5's
     landed ZERO-PREMISE final ZREmitDecode.gzip_body_strict_holds
     (the Gap7Bridge + EnoughFitsB14 derivation folded there): ONE row
     supplies the decode success (now STRICT, feeding the round-3
     head) and the sub-byte pad.  Its existential body is
     identified with the face's: the two frame equations share the
     header AND the trailer (both determined by x), so zr_app_inj
     strips the header and the equal-length-tail step closes it. *)
  pose proof ZREmitDecode.gzip_body_strict_holds as Hgzstrict.
  destruct (Hgzstrict x Hx)
    as (encV & bodyV & HdefV & HeqV & _ & HvalV).
  rewrite Hdef in HdefV. injection HdefV as <-.
  rewrite Heq in HeqV.
  destruct (zr_app_inj (zr_gzip_header 9) (zr_gzip_header 9) _ _
              eq_refl HeqV) as [_ HeqT].
  assert (HLb : length body = length bodyV).
  { pose proof (f_equal (@length Z) HeqT) as HLL.
    rewrite !length_app in HLL. lia. }
  destruct (zr_app_inj body bodyV _ _ HLb HeqT) as [HbodyE _].
  subst bodyV.
  destruct HvalV as (remb & EDS & Hpadb).
  set (CRCV := crc32_z zr_crc_init false 0 x) in *.
  set (TRL := zr_le32 CRCV ++ zr_le32 (zlen x)) in *.
  set (REST := body ++ TRL) in *.
  assert (Hlen : zlen enc <= 4294967290).
  { assert (Hxr : 0 <= zlen x < 67108864)
      by (split; [lia | exact (proj2 Hx)]).
    pose proof (zr_bound_fits 31 (zlen x) Hxr). lia. }
  assert (Hln : 0 <= zlen enc) by (unfold zlen; lia).
  (* trailer value facts *)
  assert (HCRCv : 0 <= CRCV < 4294967296).
  { unfold CRCV, zr_crc_init.
    change (crc32_z (crc32_z 0 true 0 []) false 0 x)
      with (crc32_z_at (crc32_z 0 true 0 []) 0 x).
    apply crc32_z_at_val.
    intros b Hb. destruct Hx as [HxF _].
    rewrite Forall_forall in HxF. exact (HxF b Hb). }
  assert (HISZ : 0 <= zlen x < 4294967296) by lia.
  (* reduce to the Z_FINISH run *)
  assert (HFIN : exists y, zr_inflate Z_FINISH 31 cap enc = Some y).
  2:{ destruct HFIN as [y Hy]. exists y.
      destruct HF as [-> | ->].
      - apply zr_inflate_transfer;
          [ unfold Z_NO_FLUSH, Z_BLOCK; lia
          | unfold Z_NO_FLUSH, Z_TREES; lia
          | exact Hy ].
      - exact Hy. }
  (* open the driver *)
  unfold zr_inflate.
  rewrite zr_init_31.
  unfold zr_inf_call.
  match goal with |- context [inflate_model ?a] => set (A := a) end.
  assert (HR : ReachSt (inf_st0 A)).
  { apply (reach_entry_fresh zr_gz0 (zr_gist M_HEAD 0 (-1) 0 0) 31 A
             zr_init_31).
    - reflexivity.
    - exact (zlist_bytes enc HBy).
    - unfold A. cbn [g_avail_in]. lia.
    - unfold A. cbn [g_avail_out]. lia.
    - intros j. unfold A. cbn [g_outbuf]. cbv [zzero zconst]. lia. }
  destruct (inflate_model_total_reach DynTblOk_holds A
              eq_refl eq_refl eq_refl HR) as (r & Hrun & _).
  (* the driver's entry state, in the walk's zrq spelling *)
  assert (E0 : inf_st0 A
               = zrq (zr_gist M_HEAD 0 (-1) 0 0) zr_gz0
                     (zr_gzip_header 9 ++ REST) 0 zzero 0 cap).
  { rewrite <- Heq.
    unfold A, inf_st0, zrq.
    cbn [g_st g_z g_inbuf g_avail_in g_next_in g_outbuf g_next_out
         g_avail_out g_flush].
    replace (h_mode (s_hdr (zr_gist M_HEAD 0 (-1) 0 0))) with M_HEAD
      by reflexivity.
    cbn [s_hold s_bits].
    f_equal; f_equal; first [reflexivity | lia
                            | f_equal; first [reflexivity | lia]]. }
  assert (EC : inf_ctx A = zr_ic) by reflexivity.
  assert (HCfl : zr_cflush_ok zr_ic).
  { unfold zr_cflush_ok, zr_ic. cbn [n_flush].
    unfold Z_FINISH, Z_BLOCK, Z_TREES. split; lia. }
  (* the landed positive header walk *)
  destruct (zr_gz_entry zr_gz0 REST zzero 0 cap) as (z2 & HI2).
  set (q1 := zrq (zr_gist M_TYPE 0 8 (crc32_z 0 true 0 []) 0) z2
                 (zr_gzip_header 9 ++ REST) 10 zzero 0 cap).
  (* length bookkeeping *)
  pose proof zr_gz_hdr_len as HL10.
  assert (HLE : zlen (zr_gzip_header 9 ++ REST) = zlen enc)
    by (rewrite Heq; reflexivity).
  assert (HL2 : zlen (zr_gzip_header 9 ++ REST) = 10 + zlen REST).
  { rewrite zlen_app. lia. }
  assert (HRn : 0 <= zlen REST) by (unfold zlen; lia).
  (* the entry band at the post-header state *)
  assert (Hwf1 : br_wf (q_br q1)).
  { unfold q1, zrq, br_wf. cbn [q_br br_bits br_hold br_have br_in].
    refine (conj _ (conj _ (conj _ _))).
    - lia.
    - change (Z.shiftl 1 0) with 1. lia.
    - lia.
    - intros i. apply zlist_bytes. rewrite <- Heq. exact HBy. }
  assert (Hentry1 : zr_body_entry q1).
  { unfold zr_body_entry.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
             (conj _ (conj _ (conj _ _)))))))))).
    - exact Hwf1.
    - unfold q1, zrq. cbn. lia.
    - unfold q1, zrq. cbn. lia.
    - unfold q1, zrq. cbn. lia.
    - exact Hcap32.
    - reflexivity.
    - unfold q1, zrq. cbn. lia.
    - reflexivity.
    - reflexivity.
    - apply zr_haligned_bits0. reflexivity.
    - unfold q1, zrq. cbn [q_br br_have br_bits].
      change (0 / 8) with 0. lia. }
  (* the stream view at the post-header state *)
  assert (EBR : q_br q1 = {| br_in := zlist (zr_gzip_header 9 ++ REST);
                             br_have := zlen REST;
                             br_next := zlen (zr_gzip_header 9);
                             br_hold := 0; br_bits := 0 |}).
  { unfold q1, zrq. cbn [q_br].
    f_equal; first [reflexivity | lia]. }
  assert (EST : br_stream (q_br q1) = bytes_bits REST)
    by (rewrite EBR; exact (zr_br_stream_at (zr_gzip_header 9) REST 0)).
  assert (Hdec1 : dec_stream_from_strict (br_stream (q_br q1))
                    (ob_slice (q_ob q1) 0 (o_put (q_ob q1)))
                  = Some (x, remb ++ bytes_bits TRL)).
  { rewrite EST. unfold REST.
    rewrite w2_bytes_bits_app.
    replace (ob_slice (q_ob q1) 0 (o_put (q_ob q1))) with (@nil Z)
      by reflexivity.
    exact (DecappStrict.dec_stream_from_strict_app _ _ _ _ _
             (Decapp.bytes_bits_mod8 _) EDS). }
  (* THE SELECTION — the LANDED amended head proof, posed here *)
  pose proof BsAsm.zr_body_select_holds as HselC.
  destruct (HselC zr_ic q1 x (remb ++ bytes_bits TRL)
              HCfl Hentry1 ltac:(reflexivity) Hdec1 ltac:(exact Hcap))
    as (k & q' & HI & Hrem & HS & Hwf' & Hop' & Hol' & Hsum & Hm' & Hl'
        & Hr' & Hin' & Hout' & Hwr' & Hfl' & Hws' & Hwh' & Hsn' & Hha'
        & Hbud' & Hck' & Htot').
  (* output length *)
  assert (Hput : o_put (q_ob q') = zlen x).
  { rewrite <- HS. rewrite zlen_ob_slice; [reflexivity | exact Hop']. }
  (* the crc + isize tail — CONSUMED from the LANDED
     Q6TailPos.zr_gz_tail_pos (q6 F5, the ratified Hgztail spelling +
     ONE nil-fixed-point premise, inserted between the crc value
     equation and the ISIZE mask).  q6's ratification analysis applies
     verbatim here too — see the folded block at the zlib tail
     consumption above (the TIE premise pins the update span to the
     whole slice; the ISIZE mask and [zr_le32 ++ zr_le32] vocabulary
     are ratified as spelled).  The fixed-point premise discharges at
     the entry pin: post-entry h_check = crc32_z 0 true 0 []
     (Q6GzipEntry's concrete header-walk state, threaded to q' by the
     head's h_check-preservation conjunct), a closed term that reduces
     to 0 (crc32_z's isnull arm), inside crc32_z_nil_fix's word
     range. *)
  destruct (Q6TailPos.zr_gz_tail_pos q' remb CRCV (zlen x)
              ltac:(rewrite Hwr'; reflexivity)
              ltac:(rewrite Hfl'; reflexivity)
              Hm' Hl' Hwf' Hha'
              ltac:(rewrite Hout', Hsum; unfold q1, zrq; cbn; lia)
              Hrem
              Hpadb
              HCRCv HISZ
              ltac:(rewrite Hck', HS;
                    replace (h_check (s_hdr (q_st q1)))
                      with (crc32_z 0 true 0 []) by reflexivity;
                    unfold CRCV, zr_crc_init; reflexivity)
              ltac:(rewrite Hck';
                    replace (h_check (s_hdr (q_st q1)))
                      with (crc32_z 0 true 0 []) by reflexivity;
                    apply Q6TailPos.crc32_z_nil_fix;
                    change (crc32_z 0 true 0 []) with 0; lia)
              ltac:(rewrite Htot', Hput;
                    replace (h_total (s_hdr (q_st q1))) with 0
                      by reflexivity;
                    replace (0 + zlen x) with (zlen x) by lia;
                    change 4294967295 with (Z.ones 32);
                    rewrite Z.land_ones by lia;
                    apply Z.mod_small;
                    split; [lia | change (2 ^ 32) with 4294967296; lia]))
    as (n & q2 & HL & Hret2 & Hmd2 & Hwsz2).
  (* compose the run *)
  assert (HIall : inf_iter (2 + k) zr_ic
                    (zrq (zr_gist M_HEAD 0 (-1) 0 0) zr_gz0
                         (zr_gzip_header 9 ++ REST) 0 zzero 0 cap)
                  = Some q').
  { rewrite (inf_iter_add 2 k zr_ic _ q1 HI2). exact HI. }
  pose proof (zr_iterloop_compose (2 + k) zr_ic _ q' n _ HIall HL) as HC.
  (* resolve the driver's loop *)
  pose proof Hrun as HrunG.
  unfold inflate_model in Hrun.
  cbv beta zeta in Hrun.
  replace (g_state_null A || g_out_null A
           || g_in_null A && negb (g_avail_in A =? 0))%bool
    with false in Hrun by reflexivity.
  cbv beta iota in Hrun.
  rewrite E0, EC in Hrun.
  destruct (inf_loop
              (inf_fuel (zrq (zr_gist M_HEAD 0 (-1) 0 0) zr_gz0
                             (zr_gzip_header 9 ++ REST) 0 zzero 0 cap))
              zr_ic (zrq (zr_gist M_HEAD 0 (-1) 0 0) zr_gz0
                         (zr_gzip_header 9 ++ REST) 0 zzero 0 cap))
    as [s|] eqn:ELOOP;
    [| discriminate Hrun].
  assert (Es : s = InfLeave q2)
    by (exact (zr_loop_uniq _ _ _ _ _ _ ELOOP HC)).
  subst s.
  cbv beta iota in Hrun.
  destruct (inf_leave zr_ic q2) as [q3 r0] eqn:ELV.
  cbv beta iota in Hrun.
  injection Hrun as Hr. subst r.
  destruct (zr_leave_done_fin zr_ic q2 ltac:(reflexivity) Hret2 Hmd2
              ltac:(rewrite Hwsz2, Hws'; reflexivity))
    as (Hr3 & _).
  rewrite ELV in Hr3. cbn [snd] in Hr3. subst r0.
  rewrite HrunG.
  cbn [r_ret r_q].
  rewrite Z.eqb_refl.
  eexists. reflexivity.
Qed.

(* fast-shadow: pure query elided (76.6s of the base lap; no proof-state or .vo effect): Set Printing Width 2000 *)
(* fast-shadow: pure query elided (76.6s of the base lap; no proof-state or .vo effect): Print Assumptions ZRepro_Pump_l1_raw_holds *)
(* fast-shadow: pure query elided (76.6s of the base lap; no proof-state or .vo effect): Print Assumptions ZRepro_Pump_default_zlib_holds *)
(* fast-shadow: pure query elided (76.6s of the base lap; no proof-state or .vo effect): Print Assumptions ZRepro_Pump_l9_gzip_holds *)

(* fast-shadow restore: importers of this file see the Zify default hook. *)
Ltac Zify.zify_pre_hook ::= idtac.

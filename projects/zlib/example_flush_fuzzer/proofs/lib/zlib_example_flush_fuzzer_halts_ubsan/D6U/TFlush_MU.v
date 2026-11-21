(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflSlowModel DeflateInvKeep DeflateInv DeflInvCore DeflInvMain
  BoundArith BoundInv BoundCore BoundCall HarnessKit HarnessFacts HarnessSmallStages HarnessSmallFacts HarnessSmallBound HarnessFlush HarnessFlushFacts.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import DeflSlow6_1 DeflSlow6_M DeflSlow6_Bridge Defl6_M DeflInst6 TFlush_M.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Defl6u_5 DeflInst6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import ExFlushIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec Require Import FlushStages FlushM BoundFlush FlushBound.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma HSS6u : forall IN OCAP TOT f X, 0 < OCAP < 2 ^ 31 -> 0 <= f <= 5 ->
  drun 32768 32768 65536 IN OCAP TOT X -> 4 <= ds_level X <= 9 -> lz_strat X -> ds_wrap X = 1 ->
  ds_w_size X = 32768 -> ds_hash_size X = 32768 -> SSAFE6u X f.
Proof.
  intros IN OCAP TOT f X HO Hf DR Hlv LZ W1 Ews Ehs. unfold SSAFE6u. split.
  - exact (proj1 (HSS6 IN OCAP TOT f X HO Hf DR Hlv LZ W1 Ews Ehs)).
  - exact (slow_safe6u_of_drun 32768 32768 65536 IN OCAP TOT HPBL6 f Hf X DR (proj1 Hlv) LZ W1 Ews Ehs).
Qed.

Section FL.
  Variable d : list Z.
  Hypothesis Hn : 4 <= zlength d <= 2 ^ 20.
  Hypothesis Hb : Forall (fun b => 0 <= b < 256) d.

  Theorem dfl1_safeU : DSAFE6u (fl_ds1 d) 3.
  Proof.
    destruct (fl_ds1_dcore d Hn Hb) as (D0 & L3 & AO & CFG). pose proof (fl_clen_range (zlength d) ltac:(lia)) as CR.
    pose proof (fl_ds1_scalars d) as (ST & P0 & LF & WR & LV & SG & AI & AOe & NI & OUT).
    destruct CFG as (CL & CS & CW & CI).
    pose proof (gen_dsafe6 (zlength (zc_input (fl_zc1 d))) (zc_avail_out (fl_zc1 d)) (zs_total_out (zc_strm (fl_zc1 d))) (fl_ds1 d) 3 D0
                  ltac:(left; reflexivity) ltac:(rewrite L3; lia) ltac:(rewrite AO; lia)
                  ltac:(rewrite L3; exact AI) ltac:(rewrite AO, <- (wrap32_fl_clen (zlength d)) by lia; exact AOe) NI
                  ltac:(left; exact ST) ltac:(intros E; split; [exact P0 | exact (proj1 (CI E))]) WR LV SG
                  (w_bits_of_dcfg _ (co_cfg _ _ _ _ _ _ _ D0) (co_ws _ _ _ _ _ _ _ D0))
                  SSAFE6u (fun X DR Hlv LZ W1 Ews Ehs => HSS6u (zlength (zc_input (fl_zc1 d))) (zc_avail_out (fl_zc1 d)) (zs_total_out (zc_strm (fl_zc1 d))) 3 X ltac:(rewrite AO; lia) ltac:(lia) DR Hlv LZ W1 Ews Ehs)) as [HS _].
    split; [| split; [exact HS | rewrite LF; lia]]. apply DWF_of_dcfg; [exact (co_cfg _ _ _ _ _ _ _ D0)|]. rewrite AOe, (wrap32_fl_clen (zlength d)) by lia. lia.
  Qed.

  Theorem dfl2_safeU : DSAFE6u (fl_ds2 d) 4.
  Proof.
    destruct (flush2_dcore d Hn Hb) as (D2 & B2 & C2 & SB2 & AO2 & ZC2 & P2 & AI2 & OUT2).
    destruct (flush2_entry d Hn Hb) as (_ & _ & _ & EAO2 & LO1). destruct (flush1_post d Hn Hb) as (DI1 & _).
    pose proof (fl_clen_range (zlength d) ltac:(lia)) as CR. pose proof (zlength_nonneg (cs_out_rev (ds_strm (fl_s1 d)))) as OL.
    destruct C2 as (CL & CS & CW & CI). destruct (dfl1_facts d Hn Hb) as [_ LV1].
    pose proof (dcore_basics _ _ _ _ _ _ HPBL6 _ D2) as BB2.
    assert (LIN : zlength (zc_input (fl_zc2 d)) = zlength d - 3).
    { rewrite fl_zc2_eq. cbn [zc_input]. rewrite arr_slice_length. rewrite (wrap32_id (zlength d)) by lia. rewrite (wrap32_id (zlength d - 3)) by lia. lia. }
    assert (EAI : cs_avail_in (ds_strm (fl_ds2 d)) = zlength (zc_input (fl_zc2 d))) by (unfold fl_ds2; destruct (fl_s1 d); reflexivity).
    assert (EAO : cs_avail_out (ds_strm (fl_ds2 d)) = zc_avail_out (fl_zc2 d)) by (unfold fl_ds2; destruct (fl_s1 d); reflexivity).
    assert (ENI : cs_next_in (ds_strm (fl_ds2 d)) = 0) by (unfold fl_ds2; destruct (fl_s1 d); reflexivity).
    assert (WR2 : ds_wrap (fl_ds2 d) = 1).
    { destruct CW as [W|W]; [exact W|]. exfalso.
      assert (WR1 : ds_wrap (fl_s1 d) = -1) by (revert W; unfold fl_ds2; destruct (fl_s1 d); intros W; exact W).
      destruct DI1 as [_ I1]. pose proof (di_negwrap _ _ _ _ I1) as NW.
      assert (E1 : ds_wrap (zin (fl_s1 d)) = ds_wrap (fl_s1 d) /\ ds_status (zin (fl_s1 d)) = ds_status (fl_s1 d)) by (destruct (fl_s1 d); split; reflexivity).
      destruct E1 as [Ew Es]. rewrite Ew, Es, WR1 in NW. destruct (NW eq_refl) as [S6 _].
      assert (SB1 : ds_status (fl_s1 d) = BUSY_STATE) by (revert SB2; unfold fl_ds2; destruct (fl_s1 d); intros X; exact X).
      rewrite SB1 in S6. discriminate S6. }
    assert (LV2 : ds_level (fl_ds2 d) = 6) by (revert LV1; unfold fl_ds2; destruct (fl_s1 d); intros X; exact X).
    pose proof (gen_dsafe6 (zlength (zc_input (fl_zc2 d))) (zc_avail_out (fl_zc2 d)) (zs_total_out (zc_strm (fl_zc2 d))) (fl_ds2 d) 4 D2
                  ltac:(right; reflexivity) ltac:(rewrite LIN; lia) ltac:(rewrite <- EAO, EAO2; lia)
                  EAI EAO ENI
                  ltac:(right; exact SB2) ltac:(intros E; rewrite SB2 in E; discriminate E) WR2 LV2 CS
                  (w_bits_of_dcfg _ (co_cfg _ _ _ _ _ _ _ D2) (co_ws _ _ _ _ _ _ _ D2))
                  SSAFE6u (fun X DR Hlv LZ W1 Ews Ehs => HSS6u (zlength (zc_input (fl_zc2 d))) (zc_avail_out (fl_zc2 d)) (zs_total_out (zc_strm (fl_zc2 d))) 4 X ltac:(rewrite <- EAO, EAO2; lia) ltac:(lia) DR Hlv LZ W1 Ews Ehs)) as [HS _].
    split; [| split; [exact HS | lia]]. apply DWF_of_dcfg; [exact (co_cfg _ _ _ _ _ _ _ D2)|]. rewrite EAO2. lia.
  Qed.
End FL.

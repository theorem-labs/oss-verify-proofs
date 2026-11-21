(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import ExFlushIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate
  DeflateInvKeep RefDeflateRel RefDeflatePost RefDeflateHdr4 RefDeflateHdr5 DeflateInv DeflInvTally DeflInvFbo DeflInvCore DeflInvMain
  BoundArith BoundTfb BoundInv BoundSlow BoundCore BoundCall
  HarnessKit HarnessFacts HarnessSmallStages HarnessSmallFacts HarnessSmallBound HarnessFlush HarnessFlushFacts.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec Require Import FlushStages FlushM BoundFlush.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Theorem flush1_post : forall d, 4 <= zlength d <= 2 ^ 20 -> Forall (fun b => 0 <= b < 256) d ->
  let s1 := fl_s1 d in
  DI s1 /\ BI s1 /\ CFGX s1 /\ ds_status s1 = BUSY_STATE /\ SZX s1
  /\ Mloc s1 <= 19
  /\ 0 <= cs_avail_out (ds_strm s1) /\ cs_avail_out (ds_strm s1) + zlength (cs_out_rev (ds_strm s1)) = fl_clen (zlength d)
  /\ 0 <= cs_next_in (ds_strm s1) <= 3
  /\ zs_ok (zr_strm (fl_r1 d)) /\ DADLER2 (ds_wrap s1) (zs_adler (zr_strm (fl_r1 d))) /\ Forall (fun b => 0 <= b < 256) (cs_out_rev (ds_strm s1))
  /\ ds_hash_size s1 = 32768
  /\ (ds_pending s1 = 0 /\ ds_pending_out s1 = 0) /\ cs_total_out (ds_strm s1) = zlength (cs_out_rev (ds_strm s1)).
Proof.
  intros d Hn Hb.
  pose proof DB_ds0 as [DI0 AD ZS B C SZ T0 I0 TIN TOUT PHI].
  pose proof (fl_ds1_scalars d) as (ST & P0 & LF & WR & LV & SG & AI & AO & NI & OUT).
  assert (HCL : wrap32 (fl_clen (zlength d)) = fl_clen (zlength d)) by (apply wrap32_fl_clen; lia).
  pose proof (fl_clen_range (zlength d) ltac:(lia)) as CR.
  set (zc := fl_zc1 d).
  assert (ZC : zcall_ok zc).
  { subst zc. rewrite fl_zc1_eq. unfold zcall_ok, zs_ok in *. cbn [zc_strm zc_avail_out zc_input]. rewrite HCL, arr_slice_length.
    repeat split; try lia; try (cbn; lia).
    apply Forall_arr_slice_of_list. exact Hb. }
  assert (HPBL : 2048 <= ds_lit_bufsize ds0 * 4) by (destruct SZ as [_ E]; rewrite E; lia).
  assert (HF16 : 0 <= Z_FULL_FLUSH < 16) by (unfold Z_FULL_FLUSH; lia).
  pose proof (deflate_DI ds0 zc Z_FULL_FLUSH HPBL (DI_dwf ds0 DI0) DI0 ZC HF16 AD) as (OK & DI1 & AD1).
  destruct OK as (_ & WF1 & _ & DK & ZP). cbv zeta in DI1, AD1, WF1, DK, ZP.
  pose proof (dcore_entry (ds_w_size ds0) (ds_hash_size ds0) (ds_lit_bufsize ds0 * 4) (zlength (zc_input zc)) (zc_avail_out zc) (zs_total_out (zc_strm zc))
                ds0 zc DI0 ZC AD eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as DC.
  change (set_strm ds0 (cstrm_of_call zc)) with (fl_ds1 d) in DC, DI1, AD1, WF1, DK, ZP.
  pose proof (core3 (ds_w_size ds0) (ds_hash_size ds0) (ds_lit_bufsize ds0 * 4) (zlength (zc_input zc)) (zc_avail_out zc) (zs_total_out (zc_strm zc))
                tfb_safe_holds tfb_room_holds HPBL (proj1 SZ) (proj2 SZ) 0 (fl_ds1 d) DC (BI_set_strm _ _ B) (CFGX_set_strm _ _ C)
                ST P0 eq_refl ltac:(rewrite AI; lia) ltac:(rewrite AO, HCL; lia)) as [K SB1].
  cbv zeta in K, SB1.
  assert (ES1 : fst (deflate_core (fl_ds1 d) Z_FULL_FLUSH) = fl_s1 d).
  { unfold fl_s1. rewrite fl_call1_core. destruct (deflate_core (fl_ds1 d) Z_FULL_FLUSH); reflexivity. }
  rewrite ES1 in *. cbv zeta.
  destruct K as (B1 & C1 & MK).
  unfold zpost_ok in ZP. subst zc. rewrite fl_zc1_eq in ZP. cbn [zc_input zc_avail_out zc_strm] in ZP. rewrite HCL, arr_slice_length in ZP.
  destruct ZP as ((N1 & A1 & NA1) & (O1 & OA1) & TO1 & (TI1 & TO2 & AD2 & DT1) & OB1 & RC1).
  assert (ER1 : zr_strm (fl_r1 d) = zstrm_of_cs (ds_strm (fl_s1 d))).
  { unfold fl_r1, fl_s1. rewrite fl_call1_core. destruct (deflate_core (fl_ds1 d) Z_FULL_FLUSH) as [s' rc']. reflexivity. }
  assert (M0 : Mloc (fl_ds1 d) = 0) by reflexivity.
  assert (PH0 : Phi 0 (fl_ds1 d) = 0) by reflexivity.
  pose proof DI1 as [Cf1 I1]. pose proof (di_look _ _ _ _ I1) as LK1. pose proof (di_bs _ _ _ _ I1) as BS1.
  assert (EZ : ds_lookahead (zin (fl_s1 d)) = ds_lookahead (fl_s1 d) /\ ds_strstart (zin (fl_s1 d)) = ds_strstart (fl_s1 d) /\ ds_block_start (zin (fl_s1 d)) = ds_block_start (fl_s1 d))
    by (destruct (fl_s1 d); repeat split; reflexivity).
  destruct EZ as (EZ1 & EZ2 & EZ3). rewrite EZ1 in LK1. rewrite EZ2, EZ3 in BS1.
  assert (PH1 : Phi 0 (fl_s1 d) <= 9).
  { unfold Phi, Aof. rewrite SB1. replace (BUSY_STATE =? INIT_STATE) with false by reflexivity. replace (BUSY_STATE =? FINISH_STATE) with false by reflexivity.
    assert (AB : 0 + cs_next_in (ds_strm (fl_s1 d)) - ds_lookahead (fl_s1 d) - (ds_strstart (fl_s1 d) - ds_block_start (fl_s1 d)) <= 3) by lia.
    assert (DV : (0 + cs_next_in (ds_strm (fl_s1 d)) - ds_lookahead (fl_s1 d) - (ds_strstart (fl_s1 d) - ds_block_start (fl_s1 d))) / KBLK <= 0).
    { assert (X : (0 + cs_next_in (ds_strm (fl_s1 d)) - ds_lookahead (fl_s1 d) - (ds_strstart (fl_s1 d) - ds_block_start (fl_s1 d))) / KBLK < 1) by (apply Z.div_lt_upper_bound; unfold KBLK; lia). lia. }
    destruct (ds_wrap (fl_s1 d) <=? 0); lia. }
  split; [exact DI1|]. split; [exact B1|]. split; [exact C1|]. split; [exact SB1|].
  split. { unfold SZX in *. destruct DK as (_ & _ & _ & _ & _ & W & _ & L). rewrite W, L. exact SZ. }
  split; [lia|]. split; [exact O1|]. split; [exact OA1|]. split; [lia|].
  rewrite ER1. split; [unfold zs_ok; cbn; lia|]. split; [cbn; exact AD1|]. split; [exact OB1|].
  destruct DK as (_ & _ & _ & _ & _ & _ & HS & _). rewrite HS. split; [reflexivity|].
  pose proof (di_pend _ _ _ _ I1) as PD1. pose proof (di_bv _ _ _ _ I1) as BVv1.
  assert (EZ4 : ds_pending (zin (fl_s1 d)) = ds_pending (fl_s1 d) /\ ds_bi_valid (zin (fl_s1 d)) = ds_bi_valid (fl_s1 d)) by (destruct (fl_s1 d); split; reflexivity).
  destruct EZ4 as [EZ4 EZ5]. rewrite EZ4 in PD1. rewrite EZ5 in BVv1. pose proof (cdiv8_le (ds_bi_valid (fl_s1 d)) ltac:(lia)) as C81.
  assert (OUT19 : zlength (cs_out_rev (ds_strm (fl_s1 d))) <= 19) by (unfold Mloc in MK, M0; lia).
  split.
  { pose proof (core3_pend (ds_w_size ds0) (ds_hash_size ds0) (ds_lit_bufsize ds0 * 4) (zlength (zc_input (fl_zc1 d))) (zc_avail_out (fl_zc1 d)) (zs_total_out (zc_strm (fl_zc1 d)))
                tfb_safe_holds tfb_room_holds HPBL 0 (fl_ds1 d) DC (BI_set_strm _ _ B) (CFGX_set_strm _ _ C)
                ST P0 eq_refl ltac:(rewrite AI; lia) ltac:(rewrite AO, HCL; lia)) as PP. cbv zeta in PP. rewrite ES1 in PP. apply PP. lia. }
  rewrite TO1. change (zs_total_out (zc_strm (fl_zc1 d))) with 0. rewrite Z.add_0_l. apply wrap64_id. pose proof (zlength_nonneg (cs_out_rev (ds_strm (fl_s1 d)))). lia.
Qed.

Lemma zr_output_fl_r1 : forall d, zlength (zr_output (fl_r1 d)) = zlength (cs_out_rev (ds_strm (fl_s1 d))).
Proof.
  intros d. unfold fl_r1, fl_s1. rewrite fl_call1_core. destruct (deflate_core (fl_ds1 d) Z_FULL_FLUSH) as [s rc]. cbn [fst snd].
  unfold zret_of_cs. cbn [zr_output]. apply zlength_cs_output.
Qed.

Theorem flush2_entry : forall d, 4 <= zlength d <= 2 ^ 20 -> Forall (fun b => 0 <= b < 256) d ->
  deflateStateCheck (fl_ds2 d) = false /\ ds_status (fl_ds2 d) <> FINISH_STATE /\ cs_avail_out (ds_strm (fl_ds2 d)) <> 0
  /\ cs_avail_out (ds_strm (fl_ds2 d)) = fl_clen (zlength d) - zlength (cs_out_rev (ds_strm (fl_s1 d))) /\ zlength (cs_out_rev (ds_strm (fl_s1 d))) <= 19.
Proof.
  intros d Hn Hb. destruct (flush1_post d Hn Hb) as (DI1 & B1 & C1 & SB1 & SZ1 & M1 & O1 & OA1 & NI1 & _).
  assert (ST2 : ds_status (fl_ds2 d) = BUSY_STATE) by (unfold fl_ds2; destruct (fl_s1 d); exact SB1).
  assert (AO2 : cs_avail_out (ds_strm (fl_ds2 d)) = fl_clen (zlength d) - zlength (cs_out_rev (ds_strm (fl_s1 d)))).
  { change (cs_avail_out (ds_strm (fl_ds2 d))) with (zc_avail_out (fl_zc2 d)).
    change (zc_avail_out (fl_zc2 d)) with (wrap32 (fl_clen (zlength d)) - zlength (zr_output (fl_r1 d))).
    rewrite wrap32_fl_clen by lia. rewrite zr_output_fl_r1. reflexivity. }
  pose proof DI1 as [_ I1]. pose proof (di_pend _ _ _ _ I1) as P1. pose proof (di_bv _ _ _ _ I1) as BV1.
  assert (EZ : ds_pending (zin (fl_s1 d)) = ds_pending (fl_s1 d) /\ ds_bi_valid (zin (fl_s1 d)) = ds_bi_valid (fl_s1 d)) by (destruct (fl_s1 d); split; reflexivity).
  destruct EZ as [EZ1 EZ2]. rewrite EZ1 in P1. rewrite EZ2 in BV1.
  pose proof (cdiv8_le (ds_bi_valid (fl_s1 d)) ltac:(lia)) as C8. unfold Mloc in M1.
  pose proof (fl_clen_range (zlength d) ltac:(lia)) as CR.
  split; [unfold deflateStateCheck; rewrite ST2; reflexivity|]. split; [rewrite ST2; discriminate|]. rewrite AO2. split; [lia|]. split; [reflexivity | lia].
Qed.

Theorem flush2_entry_holds : flush2_entry_stmt.
Proof. intros d Hn Hb. destruct (flush2_entry d Hn Hb) as (A & B & C & _). split; [exact A | split; [exact B | exact C]]. Qed.

Corollary flush2_zr_rc : forall d, 4 <= zlength d <= 2 ^ 20 -> Forall (fun b => 0 <= b < 256) d ->
  zr_rc (fl_r2 d) = Z_OK \/ zr_rc (fl_r2 d) = Z_STREAM_END.
Proof. exact (flush2_zr_rc_of flush2_entry_holds). Qed.

Theorem flush2_dcore : forall d, 4 <= zlength d <= 2 ^ 20 -> Forall (fun b => 0 <= b < 256) d ->
  dcore 32768 32768 65536 (zlength (zc_input (fl_zc2 d))) (zc_avail_out (fl_zc2 d)) (zs_total_out (zc_strm (fl_zc2 d))) (fl_ds2 d)
  /\ BI (fl_ds2 d) /\ CFGX (fl_ds2 d) /\ ds_status (fl_ds2 d) = BUSY_STATE /\ cs_avail_out (ds_strm (fl_ds2 d)) <> 0
  /\ zcall_ok (fl_zc2 d) /\ ds_pending (fl_ds2 d) = 0 /\ cs_avail_in (ds_strm (fl_ds2 d)) <> 0 /\ cs_out_rev (ds_strm (fl_ds2 d)) = [].
Proof.
  intros d Hn Hb. destruct (flush1_post d Hn Hb) as (DI1 & B1 & C1 & SB1 & SZ1 & M1 & O1 & OA1 & NI1 & ZS1 & AD1 & OB1 & HS1 & [P1 PO1] & TO1').
  destruct (flush2_entry d Hn Hb) as (CK2 & NF2 & AO2 & EAO2 & LO1). pose proof (zlength_nonneg (cs_out_rev (ds_strm (fl_s1 d)))) as LO0.
  pose proof (fl_clen_range (zlength d) ltac:(lia)) as CR.
  assert (ZC : zcall_ok (fl_zc2 d)).
  { rewrite fl_zc2_eq. unfold zcall_ok. cbn [zc_strm zc_avail_out zc_input]. rewrite arr_slice_length, zr_output_fl_r1, wrap32_fl_clen by lia.
    rewrite (wrap32_id (zlength d)) by lia. rewrite (wrap32_id (zlength d - 3)) by lia.
    unfold zs_ok in ZS1. repeat split; try lia. apply Forall_arr_slice_of_list. exact Hb. }
  destruct SZ1 as [W1 L1]. pose proof DI1 as [Cf1 _].
  split.
  { unfold fl_ds2. apply (dcore_entry 32768 32768 65536 _ _ _ (fl_s1 d) (fl_zc2 d) DI1 ZC); try reflexivity.
    - rewrite fl_zc2_eq. cbn [zc_strm]. exact AD1.
    - exact W1.
    - exact HS1.
    - rewrite L1. reflexivity. }
  split; [exact (BI_set_strm _ _ B1)|]. split; [exact (CFGX_set_strm _ _ C1)|].
  split; [unfold fl_ds2; destruct (fl_s1 d); exact SB1|]. split; [exact AO2|]. split; [exact ZC|].
  split; [unfold fl_ds2; destruct (fl_s1 d); exact P1|].
  split; [| reflexivity].
  change (cs_avail_in (ds_strm (fl_ds2 d))) with (zlength (zc_input (fl_zc2 d))). rewrite fl_zc2_eq. cbn [zc_input]. rewrite arr_slice_length.
  rewrite (wrap32_id (zlength d)) by lia. rewrite (wrap32_id (zlength d - 3)) by lia. lia.
Qed.

Theorem status2_range : forall d, 4 <= zlength d <= 2 ^ 20 -> Forall (fun b => 0 <= b < 256) d ->
  ds_status (fl_s2 d) = BUSY_STATE \/ ds_status (fl_s2 d) = FINISH_STATE.
Proof.
  intros d Hn Hb. destruct (flush2_dcore d Hn Hb) as (D2 & _ & _ & SB2 & AO2 & _).
  pose proof (core4_status 32768 32768 65536 (zlength (zc_input (fl_zc2 d))) (zc_avail_out (fl_zc2 d)) (zs_total_out (zc_strm (fl_zc2 d))) tfb_safe_holds tfb_room_holds ltac:(lia) (fl_ds2 d) D2 SB2 AO2) as X. cbv zeta in X.
  replace (fl_s2 d) with (fst (deflate_core (fl_ds2 d) Z_FINISH)); [exact X|].
  unfold fl_s2. rewrite fl_call2_core. destruct (deflate_core (fl_ds2 d) Z_FINISH); reflexivity.
Qed.

Theorem fl_busy_status : forall d, 4 <= zlength d <= 2 ^ 20 -> Forall (fun b => 0 <= b < 256) d ->
  fl_busy d = (ds_status (fl_s2 d) =? BUSY_STATE).
Proof.
  intros d Hn Hb. unfold fl_busy, fl_dend, dend_p.
  assert (CK : deflateStateCheck (fl_s2 d) = false).
  { unfold deflateStateCheck. destruct (status2_range d Hn Hb) as [E|E]; rewrite E; reflexivity. }
  rewrite CK. destruct (status2_range d Hn Hb) as [E|E]; rewrite E; reflexivity.
Qed.

Lemma fl_tot_eq : forall d, fl_tot d = cs_total_out (ds_strm (fl_s2 d)).
Proof.
  intros d. unfold fl_tot, fl_c2, fl_ret2, fl_r2, fl_s2. rewrite fl_call2_core.
  destruct (deflate_core (fl_ds2 d) Z_FINISH) as [s rc]. reflexivity.
Qed.

Theorem tot_range : forall d, 4 <= zlength d <= 2 ^ 20 -> Forall (fun b => 0 <= b < 256) d ->
  fl_tot d <= fl_clen (zlength d) /\ (fl_busy d = false -> 2 <= fl_tot d).
Proof.
  intros d Hn Hb.
  destruct (flush1_post d Hn Hb) as (DI1 & B1 & C1 & SB1 & SZ1 & M1 & O1 & OA1 & NI1 & ZS1 & AD1 & OB1 & HS1 & [P1 PO1] & TO1).
  destruct (flush2_dcore d Hn Hb) as (D2 & B2 & C2 & SB2 & AO2 & ZC2 & P2 & AI2 & OUT2).
  destruct (flush2_entry d Hn Hb) as (_ & _ & _ & EAO2 & LO1).
  assert (HPBL : 2048 <= ds_lit_bufsize (fl_s1 d) * 4) by (destruct SZ1 as [_ E]; rewrite E; lia).
  assert (HF16 : 0 <= Z_FINISH < 16) by (unfold Z_FINISH; lia).
  assert (AD1' : DADLER2 (ds_wrap (fl_s1 d)) (zs_adler (zc_strm (fl_zc2 d)))) by (rewrite fl_zc2_eq; cbn [zc_strm]; exact AD1).
  pose proof (deflate_DI (fl_s1 d) (fl_zc2 d) Z_FINISH HPBL (DI_dwf _ DI1) DI1 ZC2 HF16 AD1') as (OK & DI2 & AD2).
  destruct OK as (_ & _ & _ & _ & ZP). cbv zeta in ZP.
  change (set_strm (fl_s1 d) (cstrm_of_call (fl_zc2 d))) with (fl_ds2 d) in ZP.
  assert (ES2 : fst (deflate_core (fl_ds2 d) Z_FINISH) = fl_s2 d).
  { unfold fl_s2. rewrite fl_call2_core. destruct (deflate_core (fl_ds2 d) Z_FINISH); reflexivity. }
  rewrite ES2 in ZP. unfold zpost_ok in ZP. destruct ZP as (_ & (O2 & OA2') & TO2 & _).
  assert (ETO : zs_total_out (zc_strm (fl_zc2 d)) = zlength (cs_out_rev (ds_strm (fl_s1 d)))).
  { rewrite fl_zc2_eq. cbn [zc_strm]. unfold fl_r1, fl_s1 in *. rewrite fl_call1_core in *. destruct (deflate_core (fl_ds1 d) Z_FULL_FLUSH) as [s1 rc1]. cbn [fst snd] in *. exact TO1. }
  assert (EAVO : zc_avail_out (fl_zc2 d) = cs_avail_out (ds_strm (fl_ds2 d))) by reflexivity.
  pose proof (zlength_nonneg (cs_out_rev (ds_strm (fl_s2 d)))) as L2. pose proof (zlength_nonneg (cs_out_rev (ds_strm (fl_s1 d)))) as L1.
  pose proof (fl_clen_range (zlength d) ltac:(lia)) as CR.
  assert (ET : fl_tot d = zlength (cs_out_rev (ds_strm (fl_s1 d))) + zlength (cs_out_rev (ds_strm (fl_s2 d)))).
  { rewrite fl_tot_eq, TO2, ETO. apply wrap64_id. rewrite EAVO, EAO2 in OA2'. lia. }
  split; [rewrite ET; rewrite EAVO, EAO2 in OA2'; lia|].
  intros NB. rewrite (fl_busy_status d Hn Hb) in NB.
  assert (SF : ds_status (fl_s2 d) = FINISH_STATE).
  { destruct (status2_range d Hn Hb) as [E|E]; [rewrite E in NB; discriminate NB | exact E]. }
  pose proof (core4_fin_out 32768 32768 65536 (zlength (zc_input (fl_zc2 d))) (zc_avail_out (fl_zc2 d)) (zs_total_out (zc_strm (fl_zc2 d)))
                tfb_safe_holds tfb_room_holds ltac:(lia) eq_refl eq_refl (fl_ds2 d) D2 B2 C2 SB2 P2 AI2 AO2 OUT2) as X. cbv zeta in X. rewrite ES2 in X.
  destruct (X SF) as [A0|GE3]; rewrite ET; [| lia].
  rewrite EAVO, EAO2 in OA2'. rewrite A0 in OA2'. lia.
Qed.


Theorem flush1_dpost : forall d, 4 <= zlength d <= 2 ^ 20 -> Forall (fun b => 0 <= b < 256) d ->
  let ds := fl_ds1 d in let X := fst (deflate_core ds 3) in let rc := snd (deflate_core ds 3) in
  0 <= rc <= 1 /\ 0 <= cs_next_in (ds_strm X) /\ 0 <= cs_avail_in (ds_strm X)
  /\ cs_next_in (ds_strm X) + cs_avail_in (ds_strm X) = cs_next_in (ds_strm ds) + cs_avail_in (ds_strm ds).
Proof.
  intros d Hn Hb. cbv zeta. change 3 with Z_FULL_FLUSH.
  pose proof DB_ds0 as [DI0 AD ZS B C SZ T0 I0 TIN TOUT PHI].
  assert (HCL : wrap32 (fl_clen (zlength d)) = fl_clen (zlength d)) by (apply wrap32_fl_clen; lia).
  pose proof (fl_clen_range (zlength d) ltac:(lia)) as CR.
  set (zc := fl_zc1 d).
  assert (ZC : zcall_ok zc).
  { subst zc. rewrite fl_zc1_eq. unfold zcall_ok, zs_ok in *. cbn [zc_strm zc_avail_out zc_input]. rewrite HCL, arr_slice_length.
    repeat split; try lia; try (cbn; lia).
    apply Forall_arr_slice_of_list. exact Hb. }
  assert (HPBL : 2048 <= ds_lit_bufsize ds0 * 4) by (destruct SZ as [_ E]; rewrite E; lia).
  assert (HF16 : 0 <= Z_FULL_FLUSH < 16) by (unfold Z_FULL_FLUSH; lia).
  pose proof (deflate_DI ds0 zc Z_FULL_FLUSH HPBL (DI_dwf ds0 DI0) DI0 ZC HF16 AD) as (OK & _ & _).
  destruct OK as (_ & _ & _ & _ & ZP). cbv zeta in ZP.
  change (set_strm ds0 (cstrm_of_call zc)) with (fl_ds1 d) in ZP.
  unfold zpost_ok in ZP. destruct ZP as ((N1 & A1 & NA1) & _).
  split; [rewrite (flush1_rc d) by lia; unfold Z_OK; lia|].
  split; [exact N1|]. split; [exact A1|]. rewrite NA1. subst zc. reflexivity.
Qed.

Theorem flush2_dpost : forall d, 4 <= zlength d <= 2 ^ 20 -> Forall (fun b => 0 <= b < 256) d ->
  let ds := fl_ds2 d in let X := fst (deflate_core ds 4) in let rc := snd (deflate_core ds 4) in
  0 <= rc <= 1 /\ 0 <= cs_next_in (ds_strm X) /\ 0 <= cs_avail_in (ds_strm X)
  /\ cs_next_in (ds_strm X) + cs_avail_in (ds_strm X) = cs_next_in (ds_strm ds) + cs_avail_in (ds_strm ds).
Proof.
  intros d Hn Hb. cbv zeta. change 4 with Z_FINISH.
  destruct (flush1_post d Hn Hb) as (DI1 & B1 & C1 & SB1 & SZ1 & M1 & O1 & OA1 & NI1 & ZS1 & AD1 & OB1 & HS1 & [P1 PO1] & TO1).
  destruct (flush2_dcore d Hn Hb) as (D2 & B2 & C2 & SB2 & AO2 & ZC2 & P2 & AI2 & OUT2).
  assert (HPBL : 2048 <= ds_lit_bufsize (fl_s1 d) * 4) by (destruct SZ1 as [_ E]; rewrite E; lia).
  assert (HF16 : 0 <= Z_FINISH < 16) by (unfold Z_FINISH; lia).
  assert (AD1' : DADLER2 (ds_wrap (fl_s1 d)) (zs_adler (zc_strm (fl_zc2 d)))) by (rewrite fl_zc2_eq; cbn [zc_strm]; exact AD1).
  pose proof (deflate_DI (fl_s1 d) (fl_zc2 d) Z_FINISH HPBL (DI_dwf _ DI1) DI1 ZC2 HF16 AD1') as (OK & _ & _).
  destruct OK as (_ & _ & _ & _ & ZP). cbv zeta in ZP.
  change (set_strm (fl_s1 d) (cstrm_of_call (fl_zc2 d))) with (fl_ds2 d) in ZP.
  unfold zpost_ok in ZP. destruct ZP as ((N1 & A1 & NA1) & _).
  split; [destruct (flush2_rc_of flush2_entry_holds d Hn Hb) as [R|R]; rewrite R; unfold Z_OK, Z_STREAM_END; lia|].
  split; [exact N1|]. split; [exact A1|]. rewrite NA1. reflexivity.
Qed.

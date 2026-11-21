(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prog.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Prelim ZApi ZInst ZApiC ZHarnessC.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Rnd Zlib_iface Z_kit Z_dview Z_drep Z_zrd Zg_defl_path2 Zg_defl_pathi2 Z_irep Zg_zlib_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Deflate DeflateSafe RefDeflateRel RefDeflSafeI1 RefDeflSafeI2 RefDeflSafeI4 BoundFw BoundCall.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintRel ZApiInst ZTaint HarnessSmall HarnessCompress ZApiInstC ZTaintC.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState Inflate RefZApi RefInflateRel RefInflateSafeD RefInflateSafeS2 RefInflateEqS RefInflateEqB RefInflateEqU InflateCall ZTaintI InflateCallsC.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Export ZLoopFactsC.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling}.

Definition zr_dC (m : mem) (S : Z) (LBz : list block) (x : dstream) : Prop :=
  exists (L : dlay) (sa : deflate_state) (b : bptr * bptr * bptr * bptr * bptr),
    LBz = zd_blocks b L /\ dl_S L = S /\ DREPq m L sa (dz_z x) /\ DREL sa x /\ PATG2 sa /\ dlay_ceil L /\ zstrm_okP (dz_z x).

Lemma zr_dC_intro : forall m L sa b x, DREPq m L sa (dz_z x) -> DREL sa x -> PATG2 sa -> dlay_ceil L -> zstrm_okP (dz_z x) ->
  zr_dC m (dl_S L) (zd_blocks b L) x.
Proof.
  intros m L sa b x H1 H2 H3 H4 H5. exists L, sa, b. split; [reflexivity|]. split; [reflexivity|]. split; [exact H1|]. split; [exact H2|].
  split; [exact H3|]. split; [exact H4| exact H5].
Qed.

Lemma zr_dC_frame : forall m m' S LBz x, zr_dC m S LBz x ->
  (forall a, 0 <= a < 2^64 -> (S + 48 <= a < S + 112 \/ in_block LBz a) ->
     m' (wa a) = m (wa a) /\ (wview psegs m (wa a) <> None -> wview psegs m' (wa a) <> None)) ->
  zr_dC m' S LBz x.
Proof.
  intros m m' S LBz x (L & sa & b & -> & <- & DQ & DR & PT & DC & ZO) FR. exists L, sa, b.
  split; [reflexivity|]. split; [reflexivity|]. split; [|split; [exact DR| split; [exact PT| split; [exact DC| exact ZO]]]].
  pose proof (st_lay _ _ _ _ (proj2 DQ)) as LAY.
  destruct (lo_s L LAY) as (s1 & _ & s2 & _). destruct (lo_w L LAY) as (w1 & _ & w2 & _). destruct (lo_p L LAY) as (p1 & _ & p2 & _).
  destruct (lo_h L LAY) as (h1 & _ & h2 & _). destruct (lo_b L LAY) as (b1 & _ & b2 & _). destruct (lo_S L LAY) as (S1 & _ & S2).
  apply (DREPq_agree m m' L sa (dz_z x) DQ).
  - unfold ag_blocks. split; [|split; [|split; [|split]]]; intros a0 Ha; (apply FR; [lia| right; apply in_zd_blocks; lia]).
  - intros a0 Ha. apply FR; [lia| left; lia].
Qed.

Lemma zr_dC_stream : forall m S LBz x, zr_dC m S LBz x -> exists j : list byte, rw_cells psegs m (S + 48) [CB 64 j].
Proof.
  intros m S LBz x (L & sa & b & _ & <- & ((p3 & resv & DZ) & _) & _).
  destruct (rw_cells_forget psegs m _ _ DZ) as (j & H). exists j. exact H.
Qed.

Lemma DREL_sizes : forall sa x, DREL sa x ->
  DD sa /\ dreach sa /\ DeflateTaintRel.INV sa /\ ds_w_size sa = 32768 /\ ds_hash_size sa = 32768 /\ ds_lit_bufsize sa = 16384.
Proof.
  intros sa x DR. destruct (DREL_facts sa x DR) as (R & D & I & _).
  split; [exact D|]. split; [exact R|]. split; [exact I|]. split; [exact (iv_wsize _ I)|]. split; [exact (iv_hsize _ I)| exact (iv_lbs _ I)].
Qed.

Lemma dzC_init_scalars : forall lv, 0 <= lv <= 9 -> dz_z (zdc_init lv) = mkZS 0 0 1 2 MSG_NULL.
Proof. intros lv Hl. unfold zdc_init. cbn [dz_z]. rewrite (dzC_of lv Hl). reflexivity. Qed.

Lemma zsC_init_okP : zstrm_okP (mkZS 0 0 1 2 MSG_NULL).
Proof. unfold zstrm_okP. cbn [zs_total_in zs_total_out zs_adler zs_data_type]. lia. Qed.

Theorem zr_dC_init : forall m L b (G : N -> Z -> Z) lv, 0 <= lv <= 9 ->
  DREPq m L (dinitC_of G lv) (mkZS 0 0 1 2 MSG_NULL) -> dlay_ceil L ->
  zr_dC m (dl_S L) (zd_blocks b L) (zdc_init lv).
Proof.
  intros m L b G lv Hl DQ DC. apply (zr_dC_intro m L (dinitC_of G lv) b (zdc_init lv)).
  - rewrite (dzC_init_scalars lv Hl). exact DQ.
  - exact (DREL_initC G lv Hl).
  - exact (PATG2_dinitC G lv Hl).
  - exact DC.
  - rewrite (dzC_init_scalars lv Hl). exact zsC_init_okP.
Qed.

Lemma zr_dC_dend_rc : forall sa x, DREL sa x -> dend_rc sa = ZApiC.dc_end zinstC x.
Proof. intros sa x DR. cbn [ZApiC.dc_end zinstC]. exact (DREL_dend_rc sa x DR). Qed.

Lemma zr_dC_check : forall sa, PATG2 sa -> deflateStateCheck sa = false.
Proof.
  intros sa PT. unfold deflateStateCheck. destruct (pg2_st sa PT) as [E|[E|E]]; rewrite E; reflexivity.
Qed.

Lemma zr_dC_dend2 : forall sa x, DREL sa x -> PATG2 sa ->
  (if ds_status sa =? BUSY_STATE then Z_DATA_ERROR else Z_OK) = ZApiC.dc_end zinstC x.
Proof.
  intros sa x DR PT. rewrite <- (zr_dC_dend_rc sa x DR). unfold dend_rc. rewrite (zr_dC_check sa PT). reflexivity.
Qed.

End WithCeiling0.

Section PURE_D.
  Variables (sa : deflate_state) (inp : list Z) (x : dstream) (ao flush : Z).
  Hypothesis DR : DREL sa x.
  Hypothesis PT : PATG2 sa.
  Hypothesis ZOK : zstrm_okP (dz_z x).
  Hypothesis HIL : zlength inp < 2 ^ 31.
  Hypothesis HTIN : zs_total_in (dz_z x) + zlength inp < 2 ^ 63.
  Hypothesis HAO : 0 <= ao < 2 ^ 31.
  Hypothesis HD : Forall (fun c => 0 <= c < 256) inp.
  Hypothesis HFL : flush = Z_NO_FLUSH \/ flush = Z_FINISH.

  Definition czcC : ZCall := mkZCall inp ao (dz_z x).
  Definition cd0C : deflate_state := set_strm sa (cstrm_of_call czcC).

  Lemma czcC_wf : dcall_wf czcC.
  Proof.
    unfold dcall_wf, czcC. cbn [zc_strm zc_avail_out zc_input]. split; [exact ZOK|]. split; [lia|]. split; [lia|]. exact HD.
  Qed.

  Lemma HFL3C : flush = Z_NO_FLUSH \/ flush = Z_FINISH \/ flush = Z_BLOCK.
  Proof. destruct HFL as [F|F]; [left| right; left]; exact F. Qed.

  Lemma czcC_path : defl_pathg2 inp flush (deflate_core cd0C flush) cd0C.
  Proof.
    destruct (DREL_sizes sa x DR) as (HDD & _ & _ & WS & HS & LBS).
    exact (defl_pathg2_intro sa czcC flush HDD czcC_wf PT WS HS LBS HFL3C HIL (proj2 HAO)).
  Qed.

  Lemma czcC_SV : SV (cstrm_of_call czcC) (fst (deflate_core cd0C flush)) /\ PATG2 (fst (deflate_core cd0C flush))
                  /\ fwT (fst (deflate_core cd0C flush)) = zs_total_in (dz_z x).
  Proof.
    destruct (DREL_sizes sa x DR) as (HDD & _ & _ & WS & HS & LBS).
    destruct (deflate_core_P2g2 sa czcC flush HDD czcC_wf PT WS HS LBS HFL3C HIL (proj2 HAO)) as [PF [DCF _]].
    split; [exact (proj2 DCF)|]. split; [exact PF|].
    destruct czcC_path as [[_ E] _]. rewrite E. unfold fwT, cd0C. cbn [ds_strm set_strm cstrm_of_call cs_total_in cs_next_in].
    unfold czcC. cbn [zc_strm]. rewrite Z.sub_0_r. rewrite wrap64_mod. apply Z.mod_small. destruct ZOK as ((T0 & T1) & _). lia.
  Qed.

  Lemma zdc_call_facts :
    let sF := fst (deflate_core cd0C flush) in let cF := ds_strm sF in
    let '(x', consumed, bs, rc) := zdc_deflate inp x ao flush in
    DREL sF x' /\ PATG2 sF /\ zstrm_okP (dz_z x')
    /\ rc = snd (deflate_core cd0C flush) /\ bs = rev (cs_out_rev cF)
    /\ zs_total_in (dz_z x') = cs_total_in cF /\ zs_total_out (dz_z x') = cs_total_out cF
    /\ zs_msg (dz_z x') = cs_msg cF /\ zs_data_type (dz_z x') = cs_data_type cF /\ zs_adler (dz_z x') = cs_adler cF
    /\ cs_total_in cF = zs_total_in (dz_z x) + cs_next_in cF
    /\ 0 <= cs_next_in cF <= zlength inp /\ cs_avail_in cF = zlength inp - cs_next_in cF /\ consumed = cs_next_in cF
    /\ cs_total_out cF = wrap64 (zs_total_out (dz_z x) + Z.of_nat (length (cs_out_rev cF)))
    /\ cs_avail_out cF = ao - Z.of_nat (length (cs_out_rev cF))
    /\ zlength bs = Z.of_nat (length (cs_out_rev cF)) /\ Z.of_nat (length (cs_out_rev cF)) <= ao
    /\ Forall (fun c => 0 <= c < 256) bs.
  Proof.
    cbv zeta. pose proof czcC_wf as Hzc.
    pose proof (DREL_zdc sa inp x ao flush DR Hzc HFL) as ZD. cbv zeta in ZD. fold czcC in ZD.
    destruct (zdc_deflate inp x ao flush) as [[[x' consumed] bs] rc].
    destruct czcC_SV as (SVF & PATF & FT).
    unfold deflate_m in ZD. fold cd0C in ZD.
    destruct (deflate_core cd0C flush) as [sF rcF] eqn:EC. cbn [fst snd] in *.
    destruct ZD as (DR' & EZ & ECO & EBS & ERC).
    unfold zret_of_cs in EZ, ECO, EBS, ERC. cbn [zr_strm zr_consumed zr_output zr_rc] in EZ, ECO, EBS, ERC.
    pose proof (sv_inlen _ _ SVF) as I1. pose proof (sv_nin _ _ SVF) as I2. pose proof (sv_ain _ _ SVF) as I3.
    pose proof (sv_out _ _ SVF) as O1. pose proof (sv_aout _ _ SVF) as O2. pose proof (sv_tout _ _ SVF) as O3.
    pose proof (sv_tin _ _ SVF) as T1. pose proof (sv_outb _ _ SVF) as OB.
    assert (IL : arr_len (cs_input (cstrm_of_call czcC)) = zlength inp) by (cbn [cstrm_of_call cs_input]; rewrite arr_len_of_list; reflexivity).
    rewrite IL in I1.
    assert (EO0 : cs_out_rev (cstrm_of_call czcC) = [] /\ cs_avail_out (cstrm_of_call czcC) = ao /\ cs_total_out (cstrm_of_call czcC) = zs_total_out (dz_z x))
      by (unfold czcC; cbn; repeat split; reflexivity).
    destruct EO0 as (EO1 & EO2 & EO3). rewrite EO1, EO2 in O1. rewrite EO1, EO3 in O3. cbn [zlen length Z.of_nat] in O1, O3. rewrite Z.sub_0_r in O3.
    assert (LBS : zlength bs = Z.of_nat (length (cs_out_rev (ds_strm sF)))).
    { rewrite EBS. unfold cs_output. rewrite rev_append_rev, app_nil_r. unfold zlength. rewrite length_rev. reflexivity. }
    unfold zlen in O1, O3. cbn [length Z.of_nat] in O1.
    unfold fwT in FT.
    assert (TI : cs_total_in (ds_strm sF) = zs_total_in (dz_z x) + cs_next_in (ds_strm sF)).
    { apply (BoundCall.wrap64_sub_inj _ _ _ ltac:(rewrite FT; symmetry; apply wrap64_id; destruct ZOK as ((A0 & A1) & _); lia) T1).
      destruct ZOK as ((A0 & A1) & _). unfold zlength in HIL, HTIN, I1. lia. }
    split; [exact DR'|]. split; [exact PATF|].
    split. { rewrite <- EZ. unfold zstrm_okP, zstrm_of_cs. cbn [zs_total_in zs_total_out zs_adler zs_data_type].
             split; [exact T1|]. split; [rewrite O3; apply wrap64_range|]. split; [exact (sv_adler _ _ SVF)| exact (sv_dt _ _ SVF)]. }
    split; [exact ERC|].
    split; [rewrite EBS; unfold cs_output; rewrite rev_append_rev, app_nil_r; reflexivity|].
    rewrite <- EZ. unfold zstrm_of_cs. cbn [zs_total_in zs_total_out zs_msg zs_data_type zs_adler].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact TI|]. split; [lia|]. split; [lia|]. split; [exact ECO|]. split; [exact O3|]. split; [lia|]. split; [exact LBS|]. split; [lia|].
    rewrite EBS. unfold cs_output. rewrite rev_append_rev, app_nil_r. apply Forall_rev. exact OB.
  Qed.
End PURE_D.

Section RecordC. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition zdF (m : mem) (S : Z) (LBz : list block) (x : ZApi.DS ZInst.the_zapi) : Prop := False.
Lemma zdF_frame : forall m m' S LBz ds, zdF m S LBz ds ->
  (forall a, 0 <= a < 2^64 -> (S + ZS_PUB <= a < S + ZS_SIZEOF \/ in_block LBz a) ->
     m' (wa a) = m (wa a) /\ (wview psegs m (wa a) <> None -> wview psegs m' (wa a) <> None)) ->
  zdF m' S LBz ds.
Proof. intros m m' S LBz ds []. Qed.
Lemma zdF_stream : forall m S LBz ds, zdF m S LBz ds -> exists j : list byte, rw_cells psegs m (S + ZS_PUB) [CB 64 j].
Proof. intros m S LBz ds []. Qed.

Definition RsC : zreps := mkZreps zdF zr_i_def zdF_frame zr_i_def_frame zdF_stream zr_i_def_stream.

End RecordC.

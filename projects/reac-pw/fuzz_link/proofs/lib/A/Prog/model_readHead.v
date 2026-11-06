(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths and module names changed; 303 of its 358 lines of code are new or changed and 1252 lines of the source are left out. *)
(* model_read on image A: the head of its walk, from the entry (lib/A/Prog/model_read_c.v
   `model_read_acontract`) to the branch on kind at +0x120 (model_readDefs.v MR_AT120):
     +0x000 .. +0x07c  tok    -> the call of frame_alloc_1 at +0x080 (a0 = 0x60), LinkWalkSide.v aj_gx_stack_malloc_at
     +0x084 .. +0x11c  plain  -> the branch `beqz s5` at +0x120 (the frame header and its sixteen shadow bytes)
   with the kept clause from the call (link_amem.v akept) built from the two runs' frames and the call's acall_kept.
   Proves no function (kind: segment lemma of model_read's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi LinkWalkSide LinkWalkCall.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_read_c index_of_c talk_c model_readDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TL : PALib B.
Hypothesis LV : LinkVals.
(* frame_alloc_1 (0x3da88): lib/A/AF0s.v stack_malloc1_contract *)
Hypothesis ASM1 : astack_malloc_realizes pa_segs B 1.
Hypothesis HSM1 : pc_stack_malloc (as_code B) 1 = pa_sigma LS___asan_stack_malloc_1.

Let errno_low := pal_env B TL.

Lemma mr_head : forall rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs,
  MR_ENTRY SK B rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
  (forall E ms md1 S1 pos, MR_AT120 SK B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs E ms md1 S1 pos ->
     SRr pa_segs W (mkCfg ms md1) (MR_POST SK B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs)) ->
  SRr pa_segs W (cfg_at pa_segs MODEL_READ_A regs memc mdc)
    (MR_POST SK B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs).
Proof.
intros rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (HPRE & HRD & HP) CONT.
set (POST := MR_POST SK B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs) in *.
pose proof HPRE as HPRE0.
destruct HPRE as (HJ & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hside & Hajw & Hnro).
pose proof HJ as HJ0.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (pa_base_lo (PL := PL_link) (PI := PI)) as HBLO.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HK : MODEL_READ_AK = 8416) by reflexivity.
pose proof (aj_gx_unpack SK pa_segs B LAWS Hsegs G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  regs 0 HJ ltac:(lia) Hal16 ltac:(lia) Hwhi) as (memS & HJi & HSTK & HXO & Hpresw & Hceil47).
pose proof (ajournal_gx_AR pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ) as HAR.
destruct Hceil47 as (Hceil & H47).
assert (Hspc : alloc_ceiling + MODEL_READ_AK <= spZ regs) by lia.
(* the entry *)
pose proof (mr_entry SK B LAWS TL LV G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ Hal16 Hwlo Hwhi) as HS.
remember (Eimg (Ereg regs MR_extra)) as E eqn:HEdef.
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs MR_extra) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (EREG : forall r : nat, (r < 32)%nat -> ew E r = getr regs (Z_to_bv 5 (Z.of_nat r))).
{ intros r Hr. rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 5) with 32.
  symmetry. apply Z.mod_small. lia. }
assert (E1 : ew E 1 = getr regs 1) by exact (EREG 1%nat ltac:(lia)).
assert (E2 : ew E 2 = getr regs 2) by exact (EREG 2%nat ltac:(lia)).
assert (E3 : ew E 3 = getr regs 3) by exact (EREG 3%nat ltac:(lia)).
assert (E4 : ew E 4 = getr regs 4) by exact (EREG 4%nat ltac:(lia)).
assert (E32 : ew E 32 = Z_to_bv 64 MR_SB)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs MR_extra 0)).
assert (HAE : env_agree 32 (Ereg regs MR_extra) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HEdef EL.
assert (SHOK : sh_ok pa_segs MRBx (@nil shent) E (mrestrict (w_H W) memc)) by (apply Forall_nil).
assert (HCFG : cfg_at pa_segs MODEL_READ_A regs memc mdc
             = mkCfg (mkst regs (Z_to_bv 64 (pa_val A_TEXT + AF_model_read)) memc (seg_rom pa_segs)) mdc).
{ unfold cfg_at. rewrite (lv_text LV). reflexivity. }
rewrite HCFG.
pose (RUN := paj_run_x SK B LAWS G HGok XO OUT).
pose (RUNP := paj_run_plain_x SK B LAWS G HGok XO OUT).
pose (BR := paj_branch (PI := PI)).
pose (RET := paj_ret_at (PL := PL_link) (PI := PI)).
(* ---- the prologue, the two GOT loads and the switch test, up to frame_alloc_1 (+0x80) ---- *)
paj_run_tok RUN HS HJ SHOK MRspan;
  [ unfold mr_ss, mr_regions, mr_stack, mr_got, mr_cell, mr_ugot, mr_ucell;
    apply awr_ok_x_cons;
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite Usp in Ha;
      left; split; [left; lia | lia]
    | repeat (apply awr_ok_x_cons; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; lia|]);
      apply awr_ok_x_nil ] |].
rename HF into HF0, HFr into HFr0, HG into HG0.
(* ---- the state at the frame_alloc_1 call: the realigned sp is the atom 60 of the next phase ---- *)
pmkst HS.
sreg HS (1%bv : bv 5) R1. sreg HS (2%bv : bv 5) R2.
sreg HS (3%bv : bv 5) R3. sreg HS (4%bv : bv 5) R4.
cbn [ms_regs restrict mkst] in R1, R2, R3, R4.
assert (Hsp64 : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply getr_rng).
assert (E2' : ew E 2 = Z_to_bv 64 (spZ regs))
  by (rewrite E2; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
set (sp1 := 32 * ((spZ regs - 128) / 32)) in *.
assert (Hsp1e : 32 * ((spZ regs + -128) / 32) = sp1) by (unfold sp1; f_equal; f_equal; lia).
destruct (sp1_facts (spZ regs - 128) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity))
  as (Hsp1r & Hsp1al32 & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al32, Hsp1al16.
rewrite (denot_and_m32 E 2 (spZ regs) (-128) E2' ltac:(lia) ltac:(lia) ltac:(lia)), Hsp1e in R2.
change (SOff 240 17124) with (SOff A_TEXT 17124) in R1.
rewrite (codeptr_val E 17124 HEI) in R1.
assert (R3' : getr (ms_regs ms) 3 = w64 (as_gp B))
  by (rewrite R3; cbn [sv_denot]; rewrite E3, Hgp, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (R4' : getr (ms_regs ms) 4 = w64 (as_tp B))
  by (rewrite R4; cbn [sv_denot]; rewrite E4, Htp, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (Rsp : spZ (ms_regs ms) = sp1)
  by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
assert (HES : ESTACK = 4096) by reflexivity.
assert (Hcnt : count_cid 1 (frames Sc) < fs_frames 1).
{ apply (aside_room_take Sc MODEL_READ_ASIDE 1 1 Hside);
  [ unfold MODEL_READ_ASIDE; cbn [In]; left; reflexivity | lia ]. }
eapply SRr_bind.
{ eapply (aj_gx_stack_malloc_at SK pa_segs B LAWS Hsegs errno_low 1 ASM1 ltac:(lia)
    (pa_sigma LS___asan_stack_malloc_1) G XO OUT W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 own
    lyc Sc _ k _ HSM1 HJ).
  - rewrite Rsp. exact Hsp1al16.
  - rewrite Rsp. lia.
  - rewrite Rsp. lia.
  - exact R3'.
  - exact R4'.
  - reflexivity.
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact Hcnt. }
cbv beta. intros W2 c2 _ (-> & S1 & regs1 & mem1 & md1 & pos & -> & HJ1 & HP1 & Ha01 & Eab1 & Hfrs1 & Hnin1
  & Hnev1 & Hbb1 & Hfs1 & HF4096 & HFceil & Hz & Hflagw & HKEPT & Hsame1).
pose proof (ajournal_gx_AR pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) lyc S1 W mem1 md1 k
  HJ1) as HAR1.
assert (Hin1 : In (1, pos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
destruct (frame_al64 pa_segs B lyc S1 W mem1 md1 1 pos HAR1 Hin1) as (HFa64 & HFb64 & HFb).
destruct (al_frames _ _ LAWS lyc S1 W mem1 md1 1 pos HAR1 Hin1) as (HFal32 & HFapp & HFpres & HFSpres).
pose proof (aj_gx_present SK pa_segs B LAWS Hsegs G XO OUT STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own)
  lyc S1 W mem1 md1 k HJ1) as Hpres1.
destruct (frames_bounds pa_segs B LAWS lyc S1 W mem1 md1 1 pos HAR1 Hin1) as (HF4 & HFc & HFapp2).
pose proof (frm_off_imgP B lyc S1 W mem1 md1 1 pos HAR1 Hin1) as HFimg.
destruct (al_flag _ _ LAWS lyc S1 W mem1 md1 1 pos HAR1 Hin1) as (HFLpres & HFLown & HFLapp & HFLc).
set (F := frame_addr lyc 1 pos) in *.
set (FL := flag_addr lyc 1 pos) in *.
change (fs_frame_bytes 1) with 128 in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp2.
unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HFimg.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFLapp.
assert (HFL64 : 0 <= FL < 2 ^ 64)
  by (destruct HFLapp as (Hq1 & _); revert Hq1 HFLc C1a C1b; clear; intros; lia).
pose proof (Z.mul_div_le F 8 ltac:(lia)) as HF8m.
assert (HF8u : F < 8 * (F / 8) + 8)
  by (pose proof (Z.mod_pos_bound F 8 ltac:(lia)); pose proof (Z_div_mod_eq_full F 8); lia).
assert (HF8b : 0 <= F / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HF8al : (MR_SB + F / 8) mod 8 = 0).
{ unfold MR_SB. destruct (div8_of_mul64 F HFa64) as [E8 _]. rewrite E8.
  rewrite Z.add_mod by lia. rewrite (Z.mul_comm 8), Z.mod_mul by lia. reflexivity. }
(* the state after the call: keep only the machine frame; its bytes are above the call's window *)
jafter_call_keep_hi HS 40%nat regs1 (mrestrict (w_H W) mem1) HP1 [0]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
  - apply (mbyte_of_aview pa_segs). pose proof HKEPT as (K1 & _).
    first [ apply K1; [lia | rewrite Rsp; lia] | apply K1; [lia | rewrite Rsp; lia | intros []] ].
  - intros _. apply (apresent_writable pa_segs). apply Hpres1. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 40 (map (getr regs1) CLOB)) as Ev1 eqn:HE1 in HS.
assert (HEI1 : img_env pa_val A_LIM Ev1) by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD1 : forall nn, (nn < 40)%nat -> ew Ev1 nn = ew E nn)
  by (intros nn Hnn; rewrite HE1; apply YN3v.ew_havoc_old; exact Hnn).
assert (HAE1 : env_agree 32 (Ereg regs MR_extra) Ev1)
  by (rewrite HE1; apply env_agree_havoc_ge; [lia | exact HAE]).
clear HE1.
prreg HS (10%bv : bv 5) R10.
assert (E44 : ew Ev1 44 = Z_to_bv 64 F) by (rewrite <- R10; cbn [ms_regs mkst]; exact Ha01).
clear R10.
assert (E1_2 : ew Ev1 2 = Z_to_bv 64 (spZ regs)) by (rewrite OLD1 by lia; exact E2').
assert (E1_32 : ew Ev1 32 = Z_to_bv 64 MR_SB) by (rewrite OLD1 by lia; exact E32).
assert (E1_1 : ew Ev1 1 = getr regs 1) by (rewrite OLD1 by lia; exact E1).
(* atom 60 = the realigned sp, 61 = the frame's flag, 62 = SB + F / 8 *)
prreg_raw HS (2%bv : bv 5) Rsp2. prreg_raw HS (9%bv : bv 5) Rs12.
rewrite (denot_and_m32 Ev1 2 (spZ regs) (-128) E1_2 ltac:(lia) ltac:(lia) ltac:(lia)), Hsp1e in Rsp2.
rewrite (denot_and_m32_add0 Ev1 2 (spZ regs) (-128) E1_2 ltac:(lia) ltac:(lia) ltac:(lia)), Hsp1e in Rs12.
pose proof (st_ok_pi_havoc_hi 60 Ev1 _ _ [Z_to_bv 64 sp1] HS ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
remember (havoc Ev1 60 [Z_to_bv 64 sp1]) as E2v eqn:HE2 in HS.
assert (OLD2 : forall nn, (nn < 60)%nat -> ew E2v nn = ew Ev1 nn)
  by (intros nn Hnn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hnn).
assert (E60 : ew E2v 60 = Z_to_bv 64 sp1)
  by (rewrite HE2; exact (ew_havoc_new Ev1 60 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HEI2 : img_env pa_val A_LIM E2v) by (rewrite HE2; apply img_env_havoc; [exact HEI1 | cbv; lia]).
assert (HAE2 : env_agree 32 (Ereg regs MR_extra) E2v) by (rewrite HE2; apply env_agree_havoc_ge; [lia | exact HAE1]).
clear HE2.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (2%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, Z_to_bv_bv_unsigned;
          symmetry; exact Rsp2)) as HS3 end.
clear HS; rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (9%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, Z_to_bv_bv_unsigned;
          symmetry; exact Rs12)) as HS3 end.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_havoc_hi 61 E2v _ _ [Z_to_bv 64 FL; Z_to_bv 64 (MR_SB + F / 8)] HS
  ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
remember (havoc E2v 61 [Z_to_bv 64 FL; Z_to_bv 64 (MR_SB + F / 8)]) as E3v eqn:HE3 in HS.
assert (OLD3 : forall nn, (nn < 61)%nat -> ew E3v nn = ew E2v nn)
  by (intros nn Hnn; rewrite HE3; apply YN3v.ew_havoc_old; exact Hnn).
assert (E61 : ew E3v 61 = Z_to_bv 64 FL)
  by (rewrite HE3; exact (ew_havoc_new E2v 61 [Z_to_bv 64 FL; Z_to_bv 64 (MR_SB + F / 8)] 0 (Z_to_bv 64 0)
        ltac:(cbn; lia))).
assert (E62 : ew E3v 62 = Z_to_bv 64 (MR_SB + F / 8))
  by (rewrite HE3; exact (ew_havoc_new E2v 61 [Z_to_bv 64 FL; Z_to_bv 64 (MR_SB + F / 8)] 1 (Z_to_bv 64 0)
        ltac:(cbn; lia))).
assert (HEI3 : img_env pa_val A_LIM E3v) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
assert (HAE3 : env_agree 32 (Ereg regs MR_extra) E3v) by (rewrite HE3; apply env_agree_havoc_ge; [lia | exact HAE2]).
clear HE3.
assert (E3_2 : ew E3v 2 = Z_to_bv 64 (spZ regs)) by (rewrite OLD3, OLD2 by lia; exact E1_2).
assert (E3_32 : ew E3v 32 = Z_to_bv 64 MR_SB) by (rewrite OLD3, OLD2 by lia; exact E1_32).
assert (E3_44 : ew E3v 44 = Z_to_bv 64 F) by (rewrite OLD3, OLD2 by lia; exact E44).
assert (E3_60 : ew E3v 60 = Z_to_bv 64 sp1) by (rewrite OLD3 by lia; exact E60).
assert (E3_1 : ew E3v 1 = getr regs 1) by (rewrite OLD3, OLD2 by lia; exact E1_1).
assert (U60 : bv_unsigned (ew E3v 60) = sp1) by (rewrite E3_60; apply unsigned_lit_small; lia).
assert (U44 : bv_unsigned (ew E3v 44) = F) by (rewrite E3_44; apply unsigned_lit_small; lia).
assert (U62 : bv_unsigned (ew E3v 62) = MR_SB + F / 8)
  by (rewrite E62; apply unsigned_lit_small; unfold MR_SB; lia).
assert (U3_2 : bv_unsigned (ew E3v 2) = spZ regs) by (rewrite E3_2; apply unsigned_lit_small; lia).
(* the facts of the three new atoms and the shadow alias: the engine reads (F >> 3) + SB as atom 62 *)
add_fact HS 60%nat (mkAF (2 ^ 46) (2 ^ 47) 5)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E3_60, unsigned_lit_small by lia;
        change (2 ^ 5) with 32; repeat split; lia).
add_fact HS 44%nat (mkAF 4096 (2 ^ 47) 6)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E3_44, unsigned_lit_small by lia;
        change (2 ^ 6) with 64; repeat split; lia).
add_fact HS 62%nat (mkAF MR_SB (MR_SB + 2 ^ 44) 3)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E62, unsigned_lit_small by (unfold MR_SB; lia);
        change (2 ^ 3) with 8; repeat split; [unfold MR_SB; lia | unfold MR_SB; lia | exact HF8al | lia | lia]).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_alias Ev ssx msx _ _ HS
    (shadow_decl_ok Ev 44 32 62 F MR_SB E3_44 ltac:(lia) E3_32 E62)) as HS3 end.
clear HS; rename HS3 into HS; norm_pi HS.
(* the machine frame trimmed to the thirteen saved words *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  let rs := eval vm_compute in (trim_stack (ss_mem ssx) (-104) 0) in
  pose proof (st_ok_pi_submem Ev ssx msx rs HS ltac:(cbn [ss_mem]; submem_to)
    ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS; rename HS3 into HS; norm_pi HS.
assert (HdFS : F + 128 <= MR_SB + F / 8 \/ MR_SB + F / 8 + 16 <= F).
{ assert (HSBv : MR_SB = 2147450880) by reflexivity.
  destruct HFapp2 as (Hf4x & [Hlowx | (Hhighx & Hhcx)]).
  - left. clear - Hf4x Hlowx HSBv HF8m HF8u. lia.
  - right. clear - Hf4x Hhighx HSBv HF8m HF8u. lia. }
(* the slot of s1 (+0xb4 `sd s11, 0x10(s1)`; 24 bytes, below the saved words), the frame (its flag word at 120)
   and the frame's shadow (zero, frame_alloc_1's zero_shadow) *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 60%nat) 0 24 0 24 []) HS eq_refl
  ltac:(unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite U60; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
        intros o Ho; apply (apresent_writable pa_segs); apply Hpres1; lia)
  ltac:(mr_disj; rewrite ?U60, ?U3_2; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS; norm_pi HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (fframe_region 44 61 1 []) HS eq_refl
  ltac:(unfold region_ok, fframe_region;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
        change (fs_frame_bytes 1) with 128; rewrite U44; split; [lia|]; split; [lia|]; split;
        [ intros o Ho; apply (apresent_writable pa_segs); apply (proj1 (HFpres (F + o) ltac:(lia)))
        | apply Forall_cons; [|apply Forall_nil];
          apply (chunk_ok_val pa_segs _ _ F 120 8 _ FL);
          [ cbn [sv_denot]; rewrite E61, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside
          | replace (F + 120) with (F + 128 - 8) by lia;
            exact (val_mem_of_rdword pa_segs _ _ _ _ Hflagw) ] ])
  ltac:(mr_disj; rewrite ?U60, ?U44, ?U3_2; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS; norm_pi HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (fshadow_region 62 1 0 16 [YP09.mkChunk 0 (CZero 16)]) HS eq_refl
  ltac:(unfold region_ok, fshadow_region;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        change (fs_frame_bytes 1 / 8) with 16; rewrite U62; split; [unfold MR_SB; lia|];
        split; [unfold MR_SB; lia|]; split;
        [ intros o Ho; apply (apresent_writable pa_segs);
          replace (MR_SB + F / 8 + o) with (shadow_addr F + o) by (unfold shadow_addr, MR_SB, SHADOW_OFF; lia);
          apply (proj1 (HFSpres o ltac:(change (128 / 8) with 16; lia)))
        | apply Forall_cons; [|apply Forall_nil]; apply chunk_ok_zero; intros i Hi;
          pose proof (Hz i ltac:(change (128 / 8) with 16; lia)) as Hzi;
          unfold shadow_of_addr in Hzi; destruct (aview_byte pa_segs _ _ _ _ Hzi) as (bb & Hbb & Hv & _);
          replace (MR_SB + F / 8 + 0 + i) with (SHADOW_OFF + F / 8 + i) by (unfold MR_SB, SHADOW_OFF; lia);
          rewrite Hbb; f_equal; apply bv_eq; rewrite <- Hv; reflexivity ])
  ltac:(mr_disj; rewrite ?U60, ?U44, ?U62, ?U3_2; unfold MR_SB in *; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS; norm_pi HS.
rewrite R1.
(* ---- +0x84 .. +0x11c (plain): the frame's magic, descriptor and pc, and its sixteen shadow bytes,
   up to the branch `beqz s5` at +0x120 ---- *)
mr_run_plain RUNP HS HJ1.
{ apply awr_ok_x_cons;
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val fshadow_region]; intros a Ha;
    change (fs_frame_bytes 1 / 8) with 16 in Ha; rewrite U62 in Ha;
    left; apply (aj_gx_awr_frame SK pa_segs B LAWS Hsegs G XO OUT STK sp0 FP ly S W0 mem0 md0
      ((1, pos) :: own) lyc S1 W mem1 md1 k 1 pos a HJ1 ltac:(left; reflexivity));
    right; unfold in_zr, shadow_addr; cbn [fst snd];
    change (fs_frame_bytes 1 / 8) with 16; unfold MR_SB, SHADOW_OFF in *; lia
  | apply awr_ok_x_cons;
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val fframe_region]; intros a Ha;
    change (fs_frame_bytes 1) with 128 in Ha; rewrite U44 in Ha;
    left; apply (aj_gx_awr_frame SK pa_segs B LAWS Hsegs G XO OUT STK sp0 FP ly S W0 mem0 md0
      ((1, pos) :: own) lyc S1 W mem1 md1 k 1 pos a HJ1 ltac:(left; reflexivity));
    left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 1) with 128; lia
  | apply awr_ok_x_cons;
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite U60 in Ha;
    left; split; [left; lia | lia]
  | apply awr_ok_x_cons;
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite U3_2 in Ha;
    left; split; [left; lia | lia]
  | apply awr_ok_x_nil ]]]]. }
(* ---- +0x120: the state MR_AT120 ---- *)
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms120 end.
destruct Hsame1 as [Hsm1 _].
set (EW := aside_rng lyc 1 pos).
assert (Hsk : alloc_ceiling <= spZ regs - MODEL_READ_AK) by lia.
assert (PRE0 : forall a, spZ regs - MODEL_READ_AK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply (aj_gx_present SK pa_segs B LAWS Hsegs G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc
        W memc mdc k HJ0); lia).
pose proof (akept_refl SK pa_segs B LAWS Hsegs lyc Sc W memc (spZ regs - MODEL_READ_AK) (spZ regs) EW PRE0) as K0.
(* the first run writes the 128-byte machine frame only *)
pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ (fun a => spZ regs - 128 <= a < spZ regs) HFr0
  ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr;
                                              lia |]);
        destruct Hin)) as UN0.
pose proof (akept_step SK pa_segs B LAWS Hsegs lyc Sc W memc mdc W memc W _ (spZ regs - MODEL_READ_AK) (spZ regs)
  EW EW (fun a => spZ regs - 128 <= a < spZ regs) HAR Hsk ltac:(lia) K0 UN0
  (fun a _ Hp => apresent_grows _ _ _ _ HG0 Hp) (fun a H => H) ltac:(intros a Ha; cbv beta in Ha |- *; right; lia)) as K1.
(* frame_alloc_1 keeps everything outside its window *)
rewrite Rsp in HKEPT.
pose proof (akept_of_acall_kept SK pa_segs B LAWS Hsegs lyc Sc W _ W mem1 (sp1 - ESTACK) sp1 (fun _ => False) EW
  HKEPT (fun a H => False_ind _ H)) as KC.
pose proof (akept_trans SK pa_segs B LAWS Hsegs lyc Sc W memc Sc W _ W mem1 (spZ regs - MODEL_READ_AK) (spZ regs)
  (sp1 - ESTACK) sp1 EW EW EW Hsk ltac:(lia) K1 KC ltac:(lia) ltac:(lia) (fun b m H => H) (fun f H => H)
  (fun a H => H) (fun a H => H)) as K2.
(* the plain run writes the frame, its shadow, s1's slot and the machine frame *)
pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _
  (fun a => aside_rng lyc 1 pos a \/ spZ regs - MODEL_READ_AK <= a < spZ regs) HFr
  ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin];
                [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U60, ?U44, ?U62, ?U3_2 in Hrr;
                 unfold aside_rng, in_zr, frame_rng, shadow_addr; cbn [fst snd]; fold F;
                 change (fs_frame_bytes 1) with 128; change (128 / 8) with 16;
                 unfold MR_SB, SHADOW_OFF in *; lia |]);
        destruct Hin)) as UN3.
pose proof (akept_step SK pa_segs B LAWS Hsegs lyc Sc W memc mdc W mem1 W _ (spZ regs - MODEL_READ_AK) (spZ regs)
  EW EW (fun a => aside_rng lyc 1 pos a \/ spZ regs - MODEL_READ_AK <= a < spZ regs) HAR Hsk ltac:(lia) K2 UN3
  (fun a _ Hp => apresent_grows _ _ _ _ HG Hp) (fun a H => H)
  ltac:(intros a Ha; cbv beta in Ha |- *; destruct Ha as [Ha | Ha]; [left; exact Ha | right; exact Ha])) as K3.
apply (CONT E3v ms120 _ S1 pos).
unfold MR_AT120.
refine (conj HEI3 (conj HAE3 (conj E3_32 (conj E3_44 (conj E3_60 (conj E61 (conj E62 (conj HS (conj HJ1
  (conj Hfrs1 (conj Eab1 (conj Hnin1 (conj Hfs1 (conj K3 _)))))))))))))).
exact (same_but_materialized_trans _ _ _ Hsm1 (same_but_materialized_wvb_any _ _)).
Qed.
End b.
End a.

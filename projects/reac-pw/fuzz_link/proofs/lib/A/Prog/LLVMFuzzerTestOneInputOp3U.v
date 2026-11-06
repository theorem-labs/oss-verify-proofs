(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module names changed; 322 of its 371 lines of code are new or changed and 1283 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...), the op_unmark
   arm: the cut across a callee whose write set lies in g_nl's head [0, NK_N_SENT + 4) and the marks block
   (reac_served_unmark_all at 0x8310c), the shape of lib/A/Prog/LLVMFuzzerTestOneInputMqPost.v lf_mq_post_common
   with the callee's frame bound K as a parameter and no FILE bytes.
   `ux_after`: from the cut's pieces at the call and the callee's akept / ashadow_kept (lf_call), the pieces at
   the return, lf_jbk included (the FILE and its block are not written), and lf_data at the callee's new g_nl,
   marks block and a model block the caller has already rewritten (its bytes the callee does not write).
   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YI00 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase LinkWalkPi.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs
  LLVMFuzzerTestOneInputKeep LLVMFuzzerTestOneInputKpre LLVMFuzzerTestOneInputArmW LLVMFuzzerTestOneInputLp
  LLVMFuzzerTestOneInputDec LLVMFuzzerTestOneInputArmR LLVMFuzzerTestOneInputOp3Lib LLVMFuzzerTestOneInputOp3Cut
  LLVMFuzzerTestOneInputKpost LLVMFuzzerTestOneInputMb LLVMFuzzerTestOneInputMdl
  LLVMFuzzerTestOneInputArmK
  LLVMFuzzerTestOneInputMq LLVMFuzzerTestOneInputMqPost.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_served_unmark_all_c reac_served_mark_c
  mark_quietly_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_read_c model_write_c LinkWalkBcmp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the model with n_mark zeroed (+0x92c sw zero, 0(s5)) *)
Definition u_mbs_um (mbs : list byte) : list byte := lf_upd mbs (Z.to_nat MD_N_MARK) lf_z4.

Section um.
Variable mbs : list byte.
Hypothesis ML : Z.of_nat (length mbs) = MD_SIZE.

Lemma u_um_k : (Z.to_nat MD_N_MARK + length lf_z4 <= length mbs)%nat.
Proof. rewrite lf_z4_len. unfold MD_N_MARK, MD_SIZE in *. lia. Qed.

Lemma u_um_len : Z.of_nat (length (u_mbs_um mbs)) = MD_SIZE.
Proof. unfold u_mbs_um. rewrite lf_upd_length by exact u_um_k. exact ML. Qed.

Lemma u_um_rdn : forall off n, 0 <= off -> 0 <= n -> off + n <= MD_N_MARK ->
  rdn (u_mbs_um mbs) off n = rdn mbs off n.
Proof.
  intros off n H0 H1 H2. unfold u_mbs_um. apply lf_rdn_upd_other; [lia | lia | exact u_um_k |].
  left. unfold MD_N_MARK in *. lia.
Qed.

Lemma u_um_slice : forall off n, 0 <= off -> 0 <= n -> off + n <= MD_N_MARK ->
  slice (u_mbs_um mbs) off n = slice mbs off n.
Proof.
  intros off n H0 H1 H2. unfold u_mbs_um. apply lf_slice_upd_other; [lia | lia | exact u_um_k |].
  left. unfold MD_N_MARK in *. lia.
Qed.

Lemma u_um_n_mark : md_n_mark (u_mbs_um mbs) = 0.
Proof.
  unfold md_n_mark, fld_u32, u_mbs_um. rewrite lf_rdn_upd_same4; [exact lf_z4_val | unfold MD_N_MARK; lia | reflexivity |].
  pose proof u_um_k. rewrite lf_z4_len in H. exact H.
Qed.

Lemma u_um_marks : md_marks (u_mbs_um mbs) = [].
Proof. unfold md_marks. rewrite u_um_n_mark. reflexivity. Qed.

Lemma u_um_fields : md_n_req (u_mbs_um mbs) = md_n_req mbs /\ md_next (u_mbs_um mbs) = md_next mbs /\
  md_socket_errno (u_mbs_um mbs) = md_socket_errno mbs /\ md_send_errno (u_mbs_um mbs) = md_send_errno mbs.
Proof.
  unfold md_n_req, md_next, md_socket_errno, md_send_errno, fld_u32, MD_N_REQ, MD_NEXT, MD_SOCKET_ERRNO,
    MD_SEND_ERRNO. repeat split; apply u_um_rdn; unfold MD_N_MARK; lia.
Qed.

Lemma u_um_kstate : forall kbs, md_kstate (u_mbs_um mbs) kbs = md_kstate mbs kbs.
Proof.
  intros kbs. destruct u_um_fields as (_ & E2 & E3 & E4). unfold md_kstate. rewrite E2, E3, E4. reflexivity.
Qed.

Lemma u_um_reqs : model_wf mbs -> md_reqs (u_mbs_um mbs) = md_reqs mbs.
Proof.
  intros (W1 & _ & _ & _ & W5 & _). destruct u_um_fields as (E1 & _). unfold md_reqs. rewrite E1.
  apply map_ext_in. intros k Hk. apply in_seq in Hk. unfold NL_SENT_MAX in W1.
  specialize (W5 (Z.of_nat k) ltac:(lia)). unfold NL_SENT_LEN in W5.
  unfold md_req_one, fld_u64 in *. unfold NL_SENT_LEN, MD_REQ, MD_REQ_LEN in *.
  rewrite (u_um_rdn (8208 + 8 * Z.of_nat k) 8) by (unfold MD_N_MARK; lia).
  apply u_um_slice; [lia | lia | unfold MD_N_MARK; lia].
Qed.

Lemma u_um_wf : model_wf mbs -> model_wf (u_mbs_um mbs).
Proof.
  intros MW. pose proof MW as (W1 & W2 & W3 & W4 & W5 & _). destruct u_um_fields as (E1 & E2 & E3 & E4).
  split; [rewrite E1; exact W1|]. split; [rewrite E2; exact W2|]. split; [rewrite E3; exact W3|].
  split; [rewrite E4; exact W4|].
  split.
  { intros k Hk. rewrite E1 in Hk. specialize (W5 k Hk). unfold NL_SENT_MAX in W1. unfold fld_u64 in *.
    unfold MD_REQ_LEN in *. rewrite (u_um_rdn (8208 + 8 * k) 8) by (unfold MD_N_MARK; lia). exact W5. }
  unfold model_marks_wf. rewrite u_um_n_mark. split; [unfold MARKS_MAX; lia|]. intros k Hk. lia.
Qed.

End um.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.

#[local] Abbreviation BASEF cx := (@lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Abbreviation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).

(* the cut's data pieces across the store of n_mark := 0 (+0x92c): every byte the store changes lies in
   [md + MD_N_MARK, md + MD_N_MARK + 4), which now reads 0 *)
Lemma ux_store : forall (X : Z -> Prop) m m' cx md mk kbs mbs gbs,
  kagree SEGS X m m' -> wcarry_on m m' (lf_data_fp_w md mk) ->
  (forall a, 0 <= a < 2 ^ 64 -> X a -> md + MD_N_MARK <= a < md + MD_N_MARK + 4) ->
  YCbq.off_img md MD_SIZE -> apart md MD_SIZE mk MK_SIZE -> 0 <= md -> md + MD_SIZE <= 2 ^ 64 ->
  0 <= mk -> mk + MK_SIZE <= 2 ^ 64 ->
  lf_odd_at m' -> lf_la_slack m' ->
  abytes SEGS m' (md + MD_N_MARK) lf_z4 ->
  lf_data cx md mk kbs mbs gbs m ->
  anlk_at SEGS m' LA_G_NL kbs /\ aiftab_at SEGS m' LA_G_NL kbs lf_tab /\ amodel_at SEGS m' md (u_mbs_um mbs) /\
  amarks_at SEGS m' mk gbs /\ lf_ifp m' 64 /\ lf_gnames_at 64 m' /\ lf_gnames_w m' /\ lf_la_at m'.
Proof.
  intros X m m' cx md mk kbs mbs gbs HK HW HXr Hmdt Hap Hm0 Hm1 Hk0 Hk1 Hodd' Hsl' HZ
    (Hnl & Hwf & Hif & Ho & Hmi & Hoc & Hmd & Hmwf & Hmk & Hkwf & Hare & Hifp & Hgn & Hgw & Hodd & Htx & Hla).
  unfold YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hmdt. unfold apart in Hap.
  assert (XI : forall a, 0x10000 <= a < 0x654000 -> ~ X a).
  { intros a Ha HX. pose proof (HXr a ltac:(lia) HX). unfold MD_N_MARK, MD_SIZE in *. lia. }
  assert (XG : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> ~ X a)
    by (intros a Ha; apply XI; unfold LA_G_NL, NK_SIZE in Ha; lia).
  assert (XN : forall a, LA_G_NAMES <= a < LA_G_NAMES + G_NAMES_SIZE -> ~ X a)
    by (intros a Ha; apply XI; unfold LA_G_NAMES, G_NAMES_SIZE in Ha; lia).
  assert (XL : forall a, LA_LONG_ALIAS <= a < LA_LONG_ALIAS + 301 -> ~ X a)
    by (intros a Ha; apply XI; unfold LA_LONG_ALIAS in Ha; lia).
  assert (XO : forall a, LA_ODD <= a < LA_ODD + 48 -> ~ X a)
    by (intros a Ha; apply XI; unfold LA_ODD in Ha; lia).
  assert (XK : forall a, mk <= a < mk + MK_SIZE -> ~ X a).
  { intros a Ha HX. pose proof (HXr a ltac:(lia) HX). unfold MD_N_MARK, MD_SIZE, MK_SIZE in *. lia. }
  assert (WS : forall a n, (forall i, 0 <= i < n -> lf_data_fp_w md mk (a + i)) -> wcarry SEGS m m' a n)
    by (intros a n Ha; exact (wcarry_on_sub m m' _ a n HW Ha)).
  assert (Hifp' : lf_ifp m' 64) by exact (lf_ifp_keep_ro X m m' 64 HK ltac:(lia) XG XO Hifp).
  assert (Hnl' : anlk_at SEGS m' LA_G_NL kbs).
  { apply (anlk_keep SEGS X m m' _ kbs HK); [|intros i Hi; apply XG; lia | exact Hnl].
    apply WS. intros i Hi. unfold lf_data_fp_w. left. lia. }
  assert (Hif' : aiftab_at SEGS m' LA_G_NL kbs lf_tab)
    by exact (lf_aiftab_keep_ro X m m' kbs HK XG XN Hifp Hifp' Hodd' Hif).
  assert (Hmk' : amarks_at SEGS m' mk gbs).
  { apply (amarks_keep SEGS X m m' _ gbs HK); [|intros i Hi; apply XK; lia | exact Hmk].
    apply WS. intros i Hi. unfold lf_data_fp_w. right; right; right; right. lia. }
  assert (Hgw' : lf_gnames_w m').
  { apply (lf_gnames_w_keep X m m' HK); [|exact XN | exact Hgw].
    apply WS. intros i Hi. unfold lf_data_fp_w. right; left. unfold G_NAMES_SIZE in *. lia. }
  assert (Hla' : lf_la_at m').
  { apply (lf_la_at_keep_ns X m m' HK); [|exact XL | exact Hsl' | exact Hla].
    apply WS. intros i Hi. unfold lf_data_fp_w. right; right; left. lia. }
  pose proof Hmd as (Hau & ML).
  assert (Hmd' : amodel_at SEGS m' md (u_mbs_um mbs)).
  { split; [|exact (u_um_len mbs ML)].
    unfold u_mbs_um. apply (au8arr_upd X m m' md mbs (Z.to_nat MD_N_MARK) lf_z4 HK).
    - apply WS. intros i Hi. unfold lf_data_fp_w. right; right; right; left. rewrite ML in Hi. lia.
    - exact (u_um_k mbs ML).
    - intros i Hi HX. rewrite lf_z4_len. pose proof (HXr (md + Z.of_nat i) ltac:(unfold MD_SIZE in *; lia) HX).
      unfold MD_N_MARK, MD_SIZE in *. lia.
    - exact Hau.
    - rewrite Z2Nat.id by (unfold MD_N_MARK; lia). exact HZ. }
  refine (conj Hnl' (conj Hif' (conj Hmd' (conj Hmk' (conj Hifp' (conj (lf_gnames_at_keep X m m' 64 HK ltac:(lia) XN Hgn)
    (conj Hgw' Hla'))))))).
Qed.

Lemma ux_after : forall cx fp k2 ev mo wl lv md mk mbs' T3 own P N
    ly3 S3 (W3 : world SEGS) ms3 md3 ly2 S2 (W2 : world SEGS) ms2 md2 K (E : Z -> Prop) kbs' gbs',
  BASEF cx -> frames S3 = [(LF_CID, fp)] ->
  JRN cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  JRN cx fp ly2 S2 W2 (ms_mem ms2) md2 k2 ->
  0 <= K -> alloc_ceiling <= lf_sp1 cx - K ->
  akept SEGS B ly3 S3 W3 (ms_mem ms3) W2 (ms_mem ms2) (lf_sp1 cx - K) (lf_sp1 cx) E ->
  ashadow_kept SEGS B ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) ->
  In (md, MD_SIZE) (ablocks B ly2 S2) -> In (mk, MK_SIZE) (ablocks B ly2 S2) ->
  m_fds md2 = m_fds md3 -> m_fs md2 = m_fs md3 ->
  (forall a, E a -> (LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4) \/ (mk <= a < mk + MK_SIZE)) ->
  lf_saved cx W3 ms3 -> lf_header cx fp W3 ms3 -> lf_fshadow cx fp W3 ms3 LF_SH0 ->
  lf_slots cx md mk fp W3 ms3 -> lf_cur cx W3 ms3 P N ->
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own ->
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) ->
  amodel_at SEGS (rdW W3 (ms_mem ms3)) md mbs' ->
  lf_ifp (rdW W3 (ms_mem ms3)) 64 -> lf_gnames_at 64 (rdW W3 (ms_mem ms3)) ->
  lf_gnames_w (rdW W3 (ms_mem ms3)) -> lf_la_at (rdW W3 (ms_mem ms3)) ->
  anlk_at SEGS (rdW W2 (ms_mem ms2)) LA_G_NL kbs' -> nlk_wf kbs' ->
  aiftab_at SEGS (rdW W2 (ms_mem ms2)) LA_G_NL kbs' lf_tab ->
  nk_open kbs' = 0 -> nk_misuse kbs' = 0 -> nk_opened kbs' = nk_closed kbs' ->
  model_wf mbs' -> amarks_at SEGS (rdW W2 (ms_mem ms2)) mk gbs' -> marks_wf gbs' -> marks_are gbs' mbs' ->
  lf_saved cx W2 ms2 /\ lf_header cx fp W2 ms2 /\ lf_fshadow cx fp W2 ms2 LF_SH0 /\
  lf_slots cx md mk fp W2 ms2 /\ lf_cur cx W2 ms2 P N /\
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W2 ms2 md2 T3 own /\
  lf_blocks B cx md mk T3 ly3 S3 (rdW W2 (ms_mem ms2)) /\
  lf_data cx md mk kbs' mbs' gbs' (rdW W2 (ms_mem ms2)) /\
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) (ms_mem ms2)).
Proof.
  intros cx fp k2 ev mo wl lv md mk mbs' T3 own P N ly3 S3 W3 ms3 md3 ly2 S2 W2 ms2 md2 K E kbs' gbs'
    HB Hfr HJ3 HJ2 HK0 HKc Hkp Hsk Pmd Pmk Fd Fs HEc Hsv Hhd Hfsh Hsl Hcur Hjbk Hblk Hmd Difp Dgn Dgw Dla
    Dk2 Dwf2 Dtab2 Dop2 Dmis2 Doc2 Dmwf Dmk2 Dkwf2 Dare2.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as (HPRE & _ & HGX & HLN & HMS & _).
  destruct (lf_img_facts B MS la_nul HSEGS TB HMS HLN) as (IMG & RIMG).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ3) as (Hs1 & H16 & Hlo & H47).
  pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (HAR3 & _).
  pose proof HJ2 as (_ & _ & (memS2 & HJi2 & _) & _). pose proof HJi2 as (HAR2 & _).
  pose proof Hjbk as (_ & _ & Hfa & _ & _ & _ & _ & _ & Hgi & Henv & _ & Hinc & HLA & HRO & HPL & HPV).
  pose proof Hblk as (Bmd & Bmk & Bmc & Bkc & BmT & BkT & _ & _ & Hmdt & Hmkt & Hapmm & _ & Bpk & _).
  assert (Hin : In (LF_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
  assert (LC : lf_call B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E).
  { split; [exact HK0|]. split; [exact HKc|]. split; [exact Hkp | exact Hsk]. }
  unfold YCbq.off_img in Hmdt, Hmkt.
  assert (EH : forall a, LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4 -> in_img SEGS a /\ a < LA_G_NL + NK_IF_NAME).
  { intros a Ha. split; [apply (mqp_gnl_img HSEGS); unfold NK_N_SENT, NK_SIZE in *; lia
                         | unfold NK_N_SENT, NK_IF_NAME in *; lia]. }
  assert (EK : forall a, mk <= a < mk + MK_SIZE -> ~ in_img SEGS a /\ a < alloc_ceiling).
  { intros a Ha. exact (kp_blk_place B LAWS ly3 S3 W3 (ms_mem ms3) md3 mk MK_SIZE a HAR3 Bmk
      ltac:(unfold req_size, MK_SIZE in *; cbn; lia)). }
  assert (FR : forall a, (lf_F cx fp <= a < lf_F cx fp + 1024 \/ lf_SH cx fp <= a < lf_SH cx fp + 128) -> ~ E a).
  { intros a Ha HEa. destruct (kp_frame_place B LAWS cx fp ly3 S3 W3 (ms_mem ms3) md3 a HAR3 Hin Hfa Ha) as (Hni & Hc).
    destruct (HEc a HEa) as [H | H].
    - exact (Hni (proj1 (EH a H))).
    - destruct (EK a H) as (_ & Hc2).
      destruct (al_sep _ _ LAWS _ _ _ _ _ HAR3) as (Hsep & _).
      apply YG0s.pairwise_app_inv in Hsep as (_ & _ & Hcr).
      pose proof (Hcr (mk, req_size MK_SIZE) (frame_addr ly3 LF_CID fp, fs_frame_bytes LF_CID)
        ltac:(apply in_map_iff; exists (mk, MK_SIZE); split; [reflexivity | exact Bmk])
        ltac:(apply in_map_iff; exists (LF_CID, fp); split; [reflexivity | exact Hin])) as D.
      unfold zdisjoint in D. cbn [fst snd] in D. change (req_size MK_SIZE) with 516 in D.
      change (fs_frame_bytes LF_CID) with 1024 in D. rewrite (Hfa LF_CID fp) in D.
      unfold lf_SH, lf_F, shadow_of_addr, MK_SIZE in *. destruct Ha as [Ha | Ha]; [lia|].
      destruct (al_blocks _ _ LAWS _ _ _ _ _ mk MK_SIZE HAR3 Bmk) as (_ & _ & _ & Hmkapp & _).
      change (req_size MK_SIZE) with 516 in Hmkapp.
      pose proof (al_sep _ _ LAWS _ _ _ _ _ HAR3) as (_ & HFS). rewrite Forall_forall in HFS.
      pose proof (HFS (LF_CID, fp) Hin) as (HF1 & HF2). cbn [fst snd] in HF1, HF2.
      change (fs_frame_bytes LF_CID) with 1024 in HF1, HF2. rewrite (Hfa LF_CID fp) in HF1, HF2.
      pose proof (ASAN_CEIL_range) as (CR1 & CR2).
      unfold in_app, kLowShadowBeg, kHighMemBeg, MK_SIZE in Hmkapp, H. clear - Hmkapp HF1 HF2 Ha H CR1.
      unfold SHADOW_OFF in Ha. unfold ASAN_CEIL in *. lia. }
  assert (EST : forall a, E a -> a < alloc_ceiling).
  { intros a HEa. destruct (HEc a HEa) as [H | H].
    - unfold LA_G_NL, NK_N_SENT in H. lia.
    - exact (proj2 (EK a H)). }
  assert (Hsv2 : lf_saved cx W2 ms2).
  { apply (lf_saved_callee B cx K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E LC); [|exact Hsv].
    intros a Ha HEa. unfold lf_saved_fp in Ha. pose proof (EST a HEa); unfold LLVMF_STK in *; lia. }
  assert (Hsl2 : lf_slots cx md mk fp W2 ms2).
  { apply (lf_slots_callee B cx K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E md mk fp LC); [|exact Hsl].
    intros a Ha HEa. unfold lf_slots_fp in Ha. pose proof (EST a HEa); unfold LLVMF_STK in *; lia. }
  assert (Hcur2 : lf_cur cx W2 ms2 P N).
  { apply (lf_cur_callee B cx K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E P N LC); [|exact Hcur].
    intros a Ha HEa. unfold lf_cur_fp in Ha. pose proof (EST a HEa); unfold LLVMF_STK in *; lia. }
  assert (Hhd2 : lf_header cx fp W2 ms2).
  { apply (lf_header_callee B cx fp K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E LC Hin Hfa); [|exact Hhd].
    intros a Ha. apply FR. left. unfold lf_header_fp in Ha. change (fs_frame_bytes LF_CID) with 1024 in Ha. lia. }
  assert (Hfsh2 : lf_fshadow cx fp W2 ms2 LF_SH0).
  { apply (lf_fshadow_callee B cx fp K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E LC Hin Hfa); [|exact Hfsh].
    intros a Ha. apply FR. right. unfold lf_fshadow_fp in Ha. lia. }
  assert (Hblk2 : lf_blocks B cx md mk T3 ly3 S3 (rdW W2 (ms_mem ms2)))
    by exact (lf_blocks_callee B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E md mk T3 LC Pmd Pmk Hblk).
  pose proof (lf_call_kagree B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E LC) as KG.
  set (X := lf_X B ly3 S3 ly2 S2 (lf_sp1 cx - K) (lf_sp1 cx) E) in KG.
  assert (IMX : forall a, lf_img_fp MS la_nul a -> ~ E a -> ~ X a)
    by (intros a Ha HEa; exact (lfx_imgfp B MS la_nul ly3 S3 ly2 S2 _ _ E a IMG Ha HEa)).
  assert (ENRO : forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> ~ E a).
  { intros a Ha HEa. destruct (HEc a HEa) as [H | H].
    - apply (ar_not_ro_G HSEGS a); [|exact Ha]. unfold inG, G_HARNESS. apply Exists_cons_hd.
      unfold in_zr. cbn [fst snd]. unfold NK_N_SENT in H. lia.
    - destruct (EK a H) as (Hni & _).
      destruct Ha as [(s & Hs & _ & Hr) | Hr].
      + apply Hni. exists s. split; [exact Hs | exact Hr].
      + apply Hni. exact (ar_relro_img HSEGS a Hr). }
  assert (HRO2 : arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) (ms_mem ms2)))
    by exact (lf_aro_callee B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E RIMG LC ENRO HRO).
  destruct (lf_odd_texts_of_ro B TB HSEGS W2 (ms_mem ms2) HRO2) as (Hodd2 & Htx2).
  assert (ELA : ~ E la_nul).
  { intros HEa. destruct (HEc _ HEa) as [H | H].
    - rewrite HLN in H. unfold LA_NUL, LA_G_NL, LA_LONG_ALIAS, NK_N_SENT in H. lia.
    - destruct (EK _ H) as (Hni & _). apply Hni. apply (kp_img_ok_in B MS la_nul _ IMG). unfold lf_img_fp.
      right; right; right; right; right; left. lia. }
  assert (HNUL : val_mem SEGS (rdW W2 (ms_mem ms2)) la_nul 1 0)
    by exact (lf_la_nul_callee B MS la_nul cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E IMG LC ELA HLA).
  assert (HPB : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by (intros Hn; exact (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
          cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ3 Hn)).
  assert (Hjbk2 : lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W2 ms2 md2 T3 own).
  { apply (lf_jbk_callee B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own K ly2 S2 W2 ms2 md2 E
      IMG RIMG LC); [| exact ENRO | exact HPB | exact Fd | exact Fs | exact HNUL | exact Hjbk].
    intros a Ha HEa. destruct Ha as [Ha | Ha].
    - destruct Ha as [Ha | [Ha | (f & n & Hfn & Ha)]].
      + assert (Ii : in_img SEGS a) by exact (proj1 (IMG a ltac:(right; right; right; left; exact Ha))).
        destruct (HEc a HEa) as [H | H]; [|exact (proj1 (EK a H) Ii)].
        rewrite HMS in Ha. unfold amf_head_addr, amf_ofl_head in Ha.
        cbn [amf_sink_addr amf_say_addr amf_ofl_lock link_amf] in Ha. unfold LA_G_NL, NK_N_SENT in H. lia.
      + assert (Ii : in_img SEGS a) by exact (proj1 (IMG a ltac:(right; right; right; right; left; exact Ha))).
        destruct (HEc a HEa) as [H | H]; [|exact (proj1 (EK a H) Ii)].
        rewrite HMS in Ha. unfold amf_env_addr in Ha.
        cbn [amf_threaded amf_need_locks amf_ofl_lock link_amf] in Ha. unfold LA_G_NL, NK_N_SENT in H. lia.
      + assert (HfnT : In (f, n) (ablocks B ly3 S3)) by exact (Hinc _ Hfn).
        assert (Hn : n = AMF_BLOCK).
        { destruct Hgi as [(_ & HT) | (f' & _ & HT & _)]; rewrite HT in Hfn; [destruct Hfn|].
          destruct Hfn as [Hq | []]. injection Hq as _ <-. reflexivity. }
        subst n.
        destruct (kp_blk_place B LAWS ly3 S3 W3 (ms_mem ms3) md3 f AMF_BLOCK a HAR3 HfnT
          ltac:(unfold req_size, AMF_BLOCK in *; cbn; lia)) as (Hni & _).
        destruct (HEc a HEa) as [H | H]; [exact (Hni (proj1 (EH a H)))|].
        assert (Hne : (f, AMF_BLOCK) <> (mk, MK_SIZE)) by (intros Hq; rewrite Hq in Hfn; exact (BkT Hfn)).
        pose proof (sep_blocks _ _ LAWS _ _ _ _ _ f AMF_BLOCK mk MK_SIZE HAR3 HfnT Bmk Hne) as D.
        unfold zdisjoint in D. cbn [fst snd] in D. change (req_size MK_SIZE) with 516 in D.
        change (req_size AMF_BLOCK) with 1304 in D. unfold AMF_BLOCK, MK_SIZE in *. lia.
    - assert (Hn : 0 < c_n cx) by lia.
      destruct (kp_blk_place B LAWS ly3 S3 W3 (ms_mem ms3) md3 (c_p cx) (c_n cx) a HAR3 (HPB Hn)
        ltac:(unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia)) as (Hni & _).
      destruct (HEc a HEa) as [H | H]; [exact (Hni (proj1 (EH a H)))|].
      destruct (Bpk Hn) as [D | D]; unfold MK_SIZE in *; lia. }
  pose proof (ak_wcarry_callee B LAWS HSEGS ly2 S2 W2 (ms_mem ms2) md2 (rdW W3 (ms_mem ms3)) md mk HAR2 Pmd Pmk) as WC.
  assert (WB : forall a n, (forall i, 0 <= i < n -> lf_data_fp_w md mk (a + i)) ->
    wcarry SEGS (rdW W3 (ms_mem ms3)) (rdW W2 (ms_mem ms2)) a n)
    by (intros a n Hf; exact (wcarry_on_sub _ _ _ a n WC Hf)).
  assert (MDX : forall a, md <= a < md + MD_SIZE -> ~ X a).
  { intros a Ha. apply (lfx_blk B ly3 S3 ly2 S2 _ _ E md MD_SIZE a Bmd Ha). intros HEa.
    destruct (HEc a HEa) as [H | H].
    - destruct (EH a H) as (Hi & _). destruct (kp_blk_place B LAWS ly3 S3 W3 (ms_mem ms3) md3 md MD_SIZE a HAR3 Bmd
        ltac:(unfold req_size, MD_SIZE in *; cbn; lia)) as (Hni & _). exact (Hni Hi).
    - unfold apart, MD_SIZE, MK_SIZE in *. lia. }
  assert (GX : forall a, (LA_G_NL + NK_IF_NAME <= a < LA_G_NL + NK_SIZE \/ LA_G_NAMES <= a < LA_G_NAMES + G_NAMES_SIZE \/
                 LA_LONG_ALIAS <= a < LA_LONG_ALIAS + 301 \/ LA_ODD <= a < LA_ODD + 48) -> ~ X a).
  { intros a Ha. apply IMX.
    - unfold lf_img_fp. destruct Ha as [Ha | [Ha | [Ha | Ha]]].
      + left. unfold NK_IF_NAME in Ha. lia.
      + right; left. exact Ha.
      + right; right; left. exact Ha.
      + right; right; right; right; right; right. exact Ha.
    - intros HEa. destruct (HEc a HEa) as [H | H].
      + unfold NK_IF_NAME, NK_N_SENT, LA_G_NAMES, G_NAMES_SIZE, LA_G_NL, LA_LONG_ALIAS, LA_ODD in *. lia.
      + destruct (EK a H) as (Hni & _). apply Hni. apply (kp_img_ok_in B MS la_nul _ IMG). unfold lf_img_fp.
        destruct Ha as [Ha | [Ha | [Ha | Ha]]]; [left; unfold NK_IF_NAME in Ha; lia | tauto | tauto | tauto]. }
  assert (Hifp2 : lf_ifp (rdW W2 (ms_mem ms2)) 64).
  { intros e He. destruct (Difp e He) as (qq & Hq1 & Hq2 & Hq3). exists qq.
    split; [|split; [exact Hq2|]].
    - apply (au64_keep SEGS _ _ _ _ _ KG); [|exact Hq1]. intros kk Hkk. apply GX. left.
      unfold NK_IF_NAME, NK_SIZE in *. lia.
    - intros H60. apply (au64_keep SEGS _ _ _ _ _ KG); [|exact (Hq3 H60)]. intros kk Hkk. apply GX.
      right; right; right. lia. }
  assert (Hgn2 : lf_gnames_at 64 (rdW W2 (ms_mem ms2))).
  { apply (lf_gnames_at_keep _ _ _ 64 KG ltac:(lia)); [|exact Dgn]. intros a Ha. apply GX. right; left. exact Ha. }
  assert (Hgw2 : lf_gnames_w (rdW W2 (ms_mem ms2))).
  { apply (lf_gnames_w_keep _ _ _ KG); [| |exact Dgw].
    - apply WB. intros i Hi. right; left. unfold G_NAMES_SIZE in *. lia.
    - intros a Ha. apply GX. right; left. exact Ha. }
  assert (Hla2 : lf_la_at (rdW W2 (ms_mem ms2))).
  { apply (lf_la_at_keep_ns _ _ _ KG); [| | exact (lf_la_slack_any HSEGS _) | exact Dla].
    - apply WB. intros i Hi. right; right; left. lia.
    - intros a Ha. apply GX. right; right; left. exact Ha. }
  assert (Hmd2 : amodel_at SEGS (rdW W2 (ms_mem ms2)) md mbs').
  { apply (amodel_keep SEGS _ _ _ md mbs' KG); [| |exact Hmd].
    - apply WB. intros i Hi. right; right; right; left. lia.
    - intros ii Hii. apply MDX. lia. }
  split; [exact Hsv2|]. split; [exact Hhd2|]. split; [exact Hfsh2|]. split; [exact Hsl2|]. split; [exact Hcur2|].
  split; [exact Hjbk2|]. split; [exact Hblk2|]. split; [|exact HRO2].
  exact (conj Dk2 (conj Dwf2 (conj Dtab2 (conj Dop2 (conj Dmis2 (conj Doc2 (conj Hmd2 (conj Dmwf (conj Dmk2
    (conj Dkwf2 (conj Dare2 (conj Hifp2 (conj Hgn2 (conj Hgw2 (conj Hodd2 (conj Htx2 Hla2)))))))))))))))).
Qed.

End a.

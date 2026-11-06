(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module paths and module names changed; 419 of its 471 lines of code are new or changed and 352 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...): the cut AFTER
   mark_quietly (0x883d4), at its two call sites (0x831f8 op_refused, 0x8347c op_mark), shared by both arms.

   `lf_mq_post_common`: from the cut's pieces at the call and the callee's apost (akept with a write set E of
   g_nl's head [0, NK_N_SENT + 4), the marks block when a0 is it, and FILE bytes F the caller places), the pieces
   that do not depend on the FILE: the stack, the frame, the slots, the cursor and the blocks kept (Keep.v's
   *_callee lemmas), the journal's non-FILE memory clauses, and lf_data at the callee's new g_nl and marks bytes
   (amq_rc), given the arm's marks_are after the call (the hypothesis is Mq.v's lf_data_nm: lf_data but
   marks_are, which op_mark's model breaks before the call).
   `lf_mq_post_open` / `lf_mq_post_again`: the FILE part, for the opening call (the kept set grows from [] to the
   new FILE block) and a later one (the FILE block stays).

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro PcapRelroA YC4b link_aro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase LinkWalkPi
  LinkWalkCall.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs
  LLVMFuzzerTestOneInputKeep LLVMFuzzerTestOneInputKpre LLVMFuzzerTestOneInputDec LLVMFuzzerTestOneInputArmR
  LLVMFuzzerTestOneInputArmK LLVMFuzzerTestOneInputKpost LLVMFuzzerTestOneInputMq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
  model_decide_c remember_c reac_code_emit_c reac_served_mark_c mark_quietly_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the image segment that holds g_nl, and the one that holds the FILE globals g_sink .. ofl_head *)
Definition mqp_cov (lo hi : Z) : bool :=
  existsb (fun s => (Z.of_N (seg_base s) <=? lo) && (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs.
Lemma mqp_cov_gnl : mqp_cov LA_G_NL (LA_G_NL + NK_SIZE) = true. Proof. vm_compute. reflexivity. Qed.
Lemma mqp_cov_file : mqp_cov LA_G_SINK (LA_OFL_HEAD + 8) = true. Proof. vm_compute. reflexivity. Qed.
Lemma mqp_in_img : forall lo hi, mqp_cov lo hi = true -> forall a, lo <= a < hi -> in_img tfibsegs a.
Proof.
  intros lo hi H a Ha. unfold mqp_cov in H. apply existsb_exists in H as (s & Hs & Hc).
  apply andb_prop in Hc as (H1 & H2). apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists s. split; [exact Hs | lia].
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
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
Hypothesis MT_LE : forall S S' m, mo_le MT S S' m.

#[local] Abbreviation BASEF cx := (@lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Abbreviation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).

Lemma mqp_gnl_img : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> in_img SEGS a.
Proof. intros a Ha. rewrite HSEGS. exact (mqp_in_img _ _ mqp_cov_gnl a Ha). Qed.
Lemma mqp_file_img : forall a, LA_G_SINK <= a < LA_OFL_HEAD + 8 -> in_img SEGS a.
Proof. intros a Ha. rewrite HSEGS. exact (mqp_in_img _ _ mqp_cov_file a Ha). Qed.

(* the facts of the name and the marks list mark_lib returns, by the arm *)
Definition mqp_rc (regs regs2 : bvmap 5 word) (mk : Z) (kbs kbs' gbs gbs' : list byte) (nm : option (list byte))
    : Prop :=
  (aarg regs 0 = 0 -> kbs' = kbs /\ gbs' = gbs /\ getr regs2 10 = w64 (- E_INVAL)) /\
  (aarg regs 0 <> 0 ->
     let M := mark_lib lf_tab nm (mk_names gbs) (nk_sent kbs) (nk_kstate kbs) in
     getr regs2 10 = w64 (m_rc M) /\
     mk_names gbs' = m_marks M /\ mk_n gbs' = Z.of_nat (length (m_marks M)) /\
     nk_chunks kbs' = nk_chunks kbs /\ nk_end_errno kbs' = nk_end_errno kbs /\ nk_n_if kbs' = nk_n_if kbs /\
     nk_next kbs' = Z.of_nat (k_next (m_state M)) /\
     nk_sent kbs' = m_reqs M /\ nk_n_sent kbs' = Z.of_nat (length (m_reqs M)) /\
     nk_opened kbs <= nk_opened kbs' <= nk_opened kbs + 2).

(* ==========================================================================
   1. The pieces that do not depend on the FILE
   ========================================================================== *)

Lemma lf_mq_post_common : forall cx fp k2 ev mo wl lv md mk kbs mbs gbs T3 own P N
    ly3 S3 (W3 : world SEGS) ms3 md3 ly2 S2 (W2 : world SEGS) ms2 md2 k' (regs regs2 : bvmap 5 word)
    (E F : Z -> Prop) nm,
  BASEF cx -> frames S3 = [(LF_CID, fp)] ->
  JRN cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  JRN cx fp ly2 S2 W2 (ms_mem ms2) md2 k' ->
  spZ regs = lf_sp1 cx ->
  akept SEGS B ly3 S3 W3 (ms_mem ms3) W2 (ms_mem ms2) (lf_sp1 cx - MARK_QUIETLY_AK) (lf_sp1 cx) E ->
  ashadow_kept SEGS B ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) ->
  In (md, MD_SIZE) (ablocks B ly2 S2) -> In (mk, MK_SIZE) (ablocks B ly2 S2) ->
  (aarg regs 0 = 0 \/ aarg regs 0 = mk) ->
  (forall a, E a -> (LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4) \/ (aarg regs 0 = mk /\ mk <= a < mk + MK_SIZE) \/ F a) ->
  (forall a, F a -> ~ lf_saved_fp cx a /\ ~ lf_slots_fp cx a /\ ~ lf_cur_fp cx a /\
     ~ (lf_F cx fp <= a < lf_F cx fp + 1024 \/ lf_SH cx fp <= a < lf_SH cx fp + 128) /\
     ~ lf_data_fp_ro md mk a /\ ~ in_roP SEGS PCAP_RLO PCAP_RHI a /\ ~ (la_nul <= a < la_nul + 1) /\
     ~ amf_env_addr MS a /\ ~ (c_p cx <= a < c_p cx + c_n cx) /\
     ~ (exists x, (md <= x < md + MD_SIZE \/ mk <= x < mk + MK_SIZE) /\ a = shadow_of_addr SHADOW_OFF x)) ->
  astr_arg SEGS (rdW W3 (ms_mem ms3)) (aarg regs 1) nm ->
  amq_rc SEGS regs (rdW W3 (ms_mem ms3)) regs2 (rdW W2 (ms_mem ms2)) ->
  lf_saved cx W3 ms3 -> lf_header cx fp W3 ms3 -> lf_fshadow cx fp W3 ms3 LF_SH0 ->
  lf_slots cx md mk fp W3 ms3 -> lf_cur cx W3 ms3 P N ->
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own ->
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) ->
  lf_data_nm cx md mk kbs mbs gbs (rdW W3 (ms_mem ms3)) ->
  lf_saved cx W2 ms2 /\ lf_header cx fp W2 ms2 /\ lf_fshadow cx fp W2 ms2 LF_SH0 /\
  lf_slots cx md mk fp W2 ms2 /\ lf_cur cx W2 ms2 P N /\
  lf_blocks B cx md mk T3 ly3 S3 (rdW W2 (ms_mem ms2)) /\
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) (ms_mem ms2)) /\
  val_mem SEGS (rdW W2 (ms_mem ms2)) la_nul 1 0 /\ amf_env SEGS MS (rdW W2 (ms_mem ms2)) /\
  abytes SEGS (rdW W2 (ms_mem ms2)) (c_p cx) (c_pl cx) /\
  (forall a, 0 <= a < c_n cx ->
     aview SEGS (w_H W2) (ms_mem ms2) (c_p cx + a) = aview SEGS (w_H (c_W cx)) (c_mem cx) (c_p cx + a)) /\
  (forall a, amf_head_addr MS a -> ~ E a -> mbyte SEGS (rdW W2 (ms_mem ms2)) a = mbyte SEGS (rdW W3 (ms_mem ms3)) a) /\
  (forall f x, In (f, AMF_BLOCK) T3 -> f <= x < f + AMF_BLOCK -> ~ E x ->
     mbyte SEGS (rdW W2 (ms_mem ms2)) x = mbyte SEGS (rdW W3 (ms_mem ms3)) x) /\
  exists kbs' gbs',
    mqp_rc regs regs2 mk kbs kbs' gbs gbs' nm /\
    marks_wf gbs' /\
    (marks_are gbs' mbs -> lf_data cx md mk kbs' mbs gbs' (rdW W2 (ms_mem ms2))).
Proof.
  intros cx fp k2 ev mo wl lv md mk kbs mbs gbs T3 own P N ly3 S3 W3 ms3 md3 ly2 S2 W2 ms2 md2 k' regs regs2 E F nm
    HB Hfr HJ3 HJ2 Hsp Hkp Hsk Pmd Pmk Ha0 HEc HFn Hnm Hrc Hsv Hhd Hfsh Hsl Hcur Hjbk Hblk Hdat.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as (HPRE & _ & HGX & HLN & HMS & _).
  destruct (lf_img_facts B MS la_nul HSEGS TB HMS HLN) as (IMG & RIMG).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ3) as (Hs1 & H16 & Hlo & H47).
  assert (HK : MARK_QUIETLY_AK = 24608) by reflexivity.
  pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (HAR3 & _).
  pose proof HJ2 as (_ & _ & (memS2 & HJi2 & _) & _). pose proof HJi2 as (HAR2 & _).
  pose proof Hjbk as (_ & _ & Hfa & _ & _ & _ & _ & _ & Hgi & Henv & _ & Hinc & HLA & HRO & HPL & HPV).
  pose proof Hblk as (Bmd & Bmk & _ & _ & _ & _ & _ & _ & Hmdt & Hmkt & Hapmm & _).
  assert (Hin : In (LF_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
  assert (LC : lf_call B cx MARK_QUIETLY_AK ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E).
  { split; [rewrite HK; lia|]. split; [rewrite HK; unfold LLVMF_STK in *; lia|]. split; [exact Hkp | exact Hsk]. }
  assert (Hmdb : md + MD_SIZE <= alloc_ceiling /\ 4096 <= md).
  { destruct (al_blocks _ _ LAWS _ _ _ _ _ md MD_SIZE HAR3 Bmd) as (_ & H4 & Hc & _). unfold req_size, MD_SIZE in *. cbn in Hc.
    lia. }
  assert (Hmkb : mk + MK_SIZE <= alloc_ceiling /\ 4096 <= mk).
  { destruct (al_blocks _ _ LAWS _ _ _ _ _ mk MK_SIZE HAR3 Bmk) as (_ & H4 & Hc & _). unfold req_size, MK_SIZE in *. cbn in Hc.
    lia. }
  unfold YCbq.off_img in Hmdt, Hmkt.
  (* the g_nl head and the marks block, against the frame and the stack *)
  assert (EH : forall a, LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4 -> in_img SEGS a /\ a < LA_G_NL + NK_IF_NAME).
  { intros a Ha. split; [apply mqp_gnl_img; unfold NK_N_SENT, NK_SIZE in *; lia | unfold NK_N_SENT, NK_IF_NAME in *; lia]. }
  assert (EK : forall a, mk <= a < mk + MK_SIZE -> ~ in_img SEGS a /\ a < alloc_ceiling).
  { intros a Ha. exact (kp_blk_place B LAWS ly3 S3 W3 (ms_mem ms3) md3 mk MK_SIZE a HAR3 Bmk
      ltac:(unfold req_size, MK_SIZE in *; cbn; lia)). }
  assert (FR : forall a, (lf_F cx fp <= a < lf_F cx fp + 1024 \/ lf_SH cx fp <= a < lf_SH cx fp + 128) -> ~ E a).
  { intros a Ha HEa. destruct (kp_frame_place B LAWS cx fp ly3 S3 W3 (ms_mem ms3) md3 a HAR3 Hin Hfa Ha) as (Hni & Hc).
    destruct (HEc a HEa) as [H | [(_ & H) | H]].
    - exact (Hni (proj1 (EH a H))).
    - destruct (EK a H) as (_ & Hc2).
      (* the marks block and the side frame are apart by AR's separation law *)
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
      unfold SHADOW_OFF in Ha. unfold ASAN_CEIL in *. lia.
    - exact (proj1 (proj2 (proj2 (proj2 (HFn a H)))) Ha). }
  (* the memory clauses kept *)
  assert (Hsv2 : lf_saved cx W2 ms2).
  { apply (lf_saved_callee B cx MARK_QUIETLY_AK ly3 S3 ly2 S2 W3 ms3 W2 ms2 E LC); [|exact Hsv].
    intros a Ha HEa. unfold lf_saved_fp in Ha. destruct (HEc a HEa) as [H | [(_ & H) | H]].
    - destruct (EH a H) as (Hi & _). pose proof (pa_segs_low a Hi). unfold LLVMF_STK in *. lia.
    - destruct (EK a H) as (_ & Hc). unfold LLVMF_STK in *. lia.
    - exact (proj1 (HFn a H) Ha). }
  assert (Hsl2 : lf_slots cx md mk fp W2 ms2).
  { apply (lf_slots_callee B cx MARK_QUIETLY_AK ly3 S3 ly2 S2 W3 ms3 W2 ms2 E md mk fp LC); [|exact Hsl].
    intros a Ha HEa. destruct (HEc a HEa) as [H | [(_ & H) | H]].
    - destruct (EH a H) as (Hi & _). pose proof (pa_segs_low a Hi). unfold lf_slots_fp, LLVMF_STK in *. lia.
    - destruct (EK a H) as (_ & Hc). unfold lf_slots_fp, LLVMF_STK in *. lia.
    - exact (proj1 (proj2 (HFn a H)) Ha). }
  assert (Hcur2 : lf_cur cx W2 ms2 P N).
  { apply (lf_cur_callee B cx MARK_QUIETLY_AK ly3 S3 ly2 S2 W3 ms3 W2 ms2 E P N LC); [|exact Hcur].
    intros a Ha HEa. destruct (HEc a HEa) as [H | [(_ & H) | H]].
    - destruct (EH a H) as (Hi & _). pose proof (pa_segs_low a Hi). unfold lf_cur_fp, LLVMF_STK in *. lia.
    - destruct (EK a H) as (_ & Hc). unfold lf_cur_fp, LLVMF_STK in *. lia.
    - exact (proj1 (proj2 (proj2 (HFn a H))) Ha). }
  assert (Hhd2 : lf_header cx fp W2 ms2).
  { apply (lf_header_callee B cx fp MARK_QUIETLY_AK ly3 S3 ly2 S2 W3 ms3 W2 ms2 E LC Hin Hfa); [|exact Hhd].
    intros a Ha. apply FR. left. unfold lf_header_fp in Ha. change (fs_frame_bytes LF_CID) with 1024 in Ha. lia. }
  assert (Hfsh2 : lf_fshadow cx fp W2 ms2 LF_SH0).
  { apply (lf_fshadow_callee B cx fp MARK_QUIETLY_AK ly3 S3 ly2 S2 W3 ms3 W2 ms2 E LC Hin Hfa); [|exact Hfsh].
    intros a Ha. apply FR. right. unfold lf_fshadow_fp in Ha. lia. }
  assert (Hblk2 : lf_blocks B cx md mk T3 ly3 S3 (rdW W2 (ms_mem ms2)))
    by exact (lf_blocks_callee B cx MARK_QUIETLY_AK ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E md mk T3 LC
      Pmd Pmk Hblk).
  (* the exception set of the call's kagree *)
  pose proof (lf_call_kagree B cx MARK_QUIETLY_AK ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E LC) as KG.
  set (X := lf_X B ly3 S3 ly2 S2 (lf_sp1 cx - MARK_QUIETLY_AK) (lf_sp1 cx) E) in KG.
  assert (IMX : forall a, lf_img_fp MS la_nul a -> ~ E a -> ~ X a)
    by (intros a Ha HEa; exact (lfx_imgfp B MS la_nul ly3 S3 ly2 S2 _ _ E a IMG Ha HEa)).
  (* the read-only image *)
  assert (ENRO : forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> ~ E a).
  { intros a Ha HEa. destruct (HEc a HEa) as [H | [(_ & H) | H]].
    - apply (ar_not_ro_G HSEGS a); [|exact Ha]. unfold inG, G_HARNESS. apply Exists_cons_hd.
      unfold in_zr. cbn [fst snd]. unfold NK_N_SENT in H. lia.
    - destruct (EK a H) as (Hni & _).
      destruct Ha as [(s & Hs & _ & Hr) | Hr].
      + apply Hni. exists s. split; [exact Hs | exact Hr].
      + apply Hni. exact (ar_relro_img HSEGS a Hr).
    - exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (HFn a H)))))) Ha). }
  assert (HRO2 : arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) (ms_mem ms2)))
    by exact (lf_aro_callee B cx MARK_QUIETLY_AK ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E RIMG LC ENRO HRO).
  destruct (lf_odd_texts_of_ro B TB HSEGS W2 (ms_mem ms2) HRO2) as (Hodd2 & Htx2).
  (* long_alias's NUL *)
  assert (ELA : ~ E la_nul).
  { intros HEa. destruct (HEc _ HEa) as [H | [(_ & H) | H]].
    - rewrite HLN in H. unfold LA_NUL, LA_G_NL, LA_LONG_ALIAS, NK_N_SENT in H. lia.
    - destruct (EK _ H) as (Hni & _). apply Hni. apply (kp_img_ok_in B MS la_nul _ IMG). unfold lf_img_fp.
      right; right; right; right; right; left. lia.
    - exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (HFn _ H))))))) ltac:(lia)). }
  assert (HNUL : val_mem SEGS (rdW W2 (ms_mem ms2)) la_nul 1 0)
    by exact (lf_la_nul_callee B MS la_nul cx MARK_QUIETLY_AK ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E IMG LC
      ELA HLA).
  (* the FILE's environment words *)
  assert (HENV : amf_env SEGS MS (rdW W2 (ms_mem ms2))).
  { apply (amf_env_keep SEGS MS X _ _ KG); [|exact Henv]. intros a Ha. apply IMX; [unfold lf_img_fp; tauto|].
    intros HEa. rewrite HMS in Ha. cbv [amf_env_addr link_amf amf_threaded amf_need_locks amf_ofl_lock] in Ha.
    destruct (HEc a HEa) as [H | [(_ & H) | H]].
    - unfold LA_G_NL, NK_N_SENT in H. lia.
    - destruct (EK a H) as (Hni & _). apply Hni. apply (kp_img_ok_in B MS la_nul _ IMG). unfold lf_img_fp.
      right; right; right; right; left. rewrite HMS. cbv [amf_env_addr link_amf amf_threaded amf_need_locks amf_ofl_lock].
      exact Ha.
    - apply (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (HFn a H))))))))). rewrite HMS.
      cbv [amf_env_addr link_amf amf_threaded amf_need_locks amf_ofl_lock]. exact Ha. }
  (* the payload *)
  assert (HPB : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by (intros Hn; exact (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
          cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ3 Hn)).
  assert (XP : forall a, c_p cx <= a < c_p cx + c_n cx -> ~ X a).
  { intros a Ha. apply (lfx_blk B ly3 S3 ly2 S2 _ _ E (c_p cx) (c_n cx) a); [apply HPB; lia | exact Ha |].
    intros HEa. destruct (kp_blk_place B LAWS ly3 S3 W3 (ms_mem ms3) md3 (c_p cx) (c_n cx) a HAR3 (HPB ltac:(lia))
      ltac:(unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia)) as (Hni & Hc).
    destruct (HEc a HEa) as [H | [(_ & H) | H]].
    - exact (Hni (proj1 (EH a H))).
    - (* the input block and the marks block are apart (lf_blocks) *)
      pose proof Hblk as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hapi & _).
      destruct (Hapi ltac:(lia)) as [D | D]; unfold MK_SIZE in *; lia.
    - exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (HFn a H))))))))) Ha). }
  assert (HPL2 : abytes SEGS (rdW W2 (ms_mem ms2)) (c_p cx) (c_pl cx)).
  { apply (abytes_keep SEGS X _ _ (c_p cx) (c_pl cx) KG); [|exact HPL]. intros i Hi. apply XP. unfold c_n. lia. }
  assert (HPV2 : forall a, 0 <= a < c_n cx ->
     aview SEGS (w_H W2) (ms_mem ms2) (c_p cx + a) = aview SEGS (w_H (c_W cx)) (c_mem cx) (c_p cx + a)).
  { intros a Ha. rewrite <- (HPV a Ha). apply (aview_of_kagree SEGS X _ _ _ _ _ KG). apply XP. lia. }
  (* the FILE's heads and kept block, where E misses them *)
  assert (HHD : forall a, amf_head_addr MS a -> ~ E a ->
     mbyte SEGS (rdW W2 (ms_mem ms2)) a = mbyte SEGS (rdW W3 (ms_mem ms3)) a).
  { intros a Ha HEa. apply KG. apply IMX; [unfold lf_img_fp; tauto | exact HEa]. }
  assert (HFB : forall f x, In (f, AMF_BLOCK) T3 -> f <= x < f + AMF_BLOCK -> ~ E x ->
     mbyte SEGS (rdW W2 (ms_mem ms2)) x = mbyte SEGS (rdW W3 (ms_mem ms3)) x).
  { intros f x Hf Hx HEx. apply KG.
    exact (lfx_blk B ly3 S3 ly2 S2 _ _ E f AMF_BLOCK x (Hinc _ Hf) Hx HEx). }
  (* lf_data at the callee's new g_nl and marks bytes *)
  destruct Hdat as (Dk & Dwf & Dtab & Dop & Dmis & Doc & Dmd & Dmwf & Dmk & Dkwf & Difp & Dgn & Dgw & Dodd
    & Dtx & Dla).
  assert (WB : forall b n, In (b, n) (ablocks B ly2 S2) -> wcarry SEGS (rdW W3 (ms_mem ms3)) (rdW W2 (ms_mem ms2)) b n).
  { intros b n Hbn i Hi _. destruct (al_blocks _ _ LAWS ly2 S2 W2 (ms_mem ms2) md2 b n HAR2 Hbn) as (_ & _ & _ & _ & Hp & _).
    apply (apresent_writable SEGS). apply (proj1 (Hp (b + i) ltac:(unfold req_size; destruct (Z.eqb_spec n 0); lia))). }
  assert (MDX : forall a, md <= a < md + MD_SIZE -> ~ X a).
  { intros a Ha. apply (lfx_blk B ly3 S3 ly2 S2 _ _ E md MD_SIZE a Bmd Ha). intros HEa.
    destruct (HEc a HEa) as [H | [(_ & H) | H]].
    - destruct (EH a H) as (Hi & _). destruct (kp_blk_place B LAWS ly3 S3 W3 (ms_mem ms3) md3 md MD_SIZE a HAR3 Bmd
        ltac:(unfold req_size, MD_SIZE in *; cbn; lia)) as (Hni & _). exact (Hni Hi).
    - unfold apart, MD_SIZE, MK_SIZE in *. lia.
    - exact (proj1 (proj2 (proj2 (proj2 (proj2 (HFn a H))))) ltac:(unfold lf_data_fp_ro; tauto)). }
  assert (GX : forall a, (LA_G_NL + NK_IF_NAME <= a < LA_G_NL + NK_SIZE \/ LA_G_NAMES <= a < LA_G_NAMES + G_NAMES_SIZE \/
                 LA_LONG_ALIAS <= a < LA_LONG_ALIAS + 301 \/ LA_ODD <= a < LA_ODD + 48) -> ~ X a).
  { intros a Ha. apply IMX.
    - unfold lf_img_fp. destruct Ha as [Ha | [Ha | [Ha | Ha]]].
      + left. unfold NK_IF_NAME in Ha. lia.
      + right; left. exact Ha.
      + right; right; left. exact Ha.
      + right; right; right; right; right; right. exact Ha.
    - intros HEa. destruct (HEc a HEa) as [H | [(_ & H) | H]].
      + unfold NK_IF_NAME, NK_N_SENT, LA_G_NAMES, G_NAMES_SIZE, LA_G_NL, LA_LONG_ALIAS, LA_ODD in *. lia.
      + destruct (EK a H) as (Hni & _). apply Hni. apply (kp_img_ok_in B MS la_nul _ IMG). unfold lf_img_fp.
        destruct Ha as [Ha | [Ha | [Ha | Ha]]]; [left; unfold NK_IF_NAME in Ha; lia | tauto | tauto | tauto].
      + apply (proj1 (proj2 (proj2 (proj2 (proj2 (HFn a H)))))). unfold lf_data_fp_ro.
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
    - assert (Hw : forall (m' : word -> option byte) a, LA_G_NAMES <= a < LA_G_NAMES + 512 -> writable_at SEGS m' a)
        by (rewrite HSEGS; exact LA_G_NAMES_writable).
      intros ii Hii _. apply Hw. unfold G_NAMES_SIZE in Hii. lia.
    - intros a Ha. apply GX. right; left. exact Ha. }
  assert (Hla2 : lf_la_at (rdW W2 (ms_mem ms2))).
  { apply (lf_la_at_keep_ns _ _ _ KG); [| | exact (lf_la_slack_any HSEGS _) | exact Dla].
    - generalize (rdW W3 (ms_mem ms3)) (rdW W2 (ms_mem ms2)). rewrite HSEGS. intros m3 m2 ii Hii _.
      revert ii Hii. replace (fun ii => writable_at tfibsegs m2 (LA_LONG_ALIAS + ii)) with
        (fun ii => writable_at tfibsegs m2 (LA_LONG_ALIAS + ii)) by reflexivity.
      intros ii Hii. apply (writable_at_of_wseg tfibsegs m2 LA_LONG_ALIAS 304);
        [unfold LA_LONG_ALIAS; lia | unfold LA_LONG_ALIAS; lia | exact wseg_LA_LONG_ALIAS304 | lia].
    - intros a Ha. apply GX. right; right; left. exact Ha. }
  assert (Hmd2 : amodel_at SEGS (rdW W2 (ms_mem ms2)) md mbs).
  { apply (amodel_keep SEGS _ _ _ md mbs KG (WB md MD_SIZE Pmd)); [|exact Dmd]. intros ii Hii. apply MDX. lia. }
  (* the g_nl table, whose bytes the callee does not write *)
  assert (TABX : forall i, 0 <= i < 80 -> forall kk, 0 <= kk < 8 -> ~ X (LA_G_NL + NK_IF_NAME + 8 * i + kk)).
  { intros i Hi kk Hkk. apply GX. left. unfold NK_IF_NAME, NK_SIZE. lia. }
  assert (TIX : forall i, 0 <= i < 80 -> forall kk, 0 <= kk < 4 -> ~ X (LA_G_NL + NK_IF_INDEX + 4 * i + kk)).
  { intros i Hi kk Hkk. apply GX. left. unfold NK_IF_NAME, NK_IF_INDEX, NK_SIZE. lia. }
  split; [exact Hsv2|]. split; [exact Hhd2|]. split; [exact Hfsh2|]. split; [exact Hsl2|]. split; [exact Hcur2|].
  split; [exact Hblk2|]. split; [exact HRO2|]. split; [exact HNUL|]. split; [exact HENV|]. split; [exact HPL2|].
  split; [exact HPV2|]. split; [exact HHD|]. split; [exact HFB|].
  (* amq_rc at this call *)
  destruct Hrc as (Rnull & Rmk).
  destruct (Z.eq_dec (aarg regs 0) 0) as [A0 | A0].
  - (* a0 = NULL: g_nl and the marks are not written *)
    destruct (Rnull A0) as (Rrc & Rk). pose proof (Rk kbs Dk) as Dk2.
    assert (EMK : forall a, mk <= a < mk + MK_SIZE -> ~ X a).
    { intros a Ha. apply (lfx_blk B ly3 S3 ly2 S2 _ _ E mk MK_SIZE a Bmk Ha). intros HEa.
      destruct (HEc a HEa) as [H | [(H0 & H) | H]].
      - destruct (EK a Ha) as (Hni & _). exact (Hni (proj1 (EH a H))).
      - rewrite A0 in H0. unfold MK_SIZE in *. lia.
      - exact (proj1 (proj2 (proj2 (proj2 (proj2 (HFn a H))))) ltac:(unfold lf_data_fp_ro; tauto)). }
    assert (Hmk2 : amarks_at SEGS (rdW W2 (ms_mem ms2)) mk gbs).
    { apply (amarks_keep SEGS _ _ _ mk gbs KG (WB mk MK_SIZE Pmk)); [|exact Dmk]. intros ii Hii. apply EMK. lia. }
    (* the table read through the kept g_nl bytes *)
    set (X' := fun a => X a /\ ~ (LA_G_NL <= a < LA_G_NL + NK_SIZE)).
    assert (KG' : kagree SEGS X' (rdW W3 (ms_mem ms3)) (rdW W2 (ms_mem ms2))).
    { intros a Ha. destruct (Z_lt_le_dec a LA_G_NL) as [Hl | Hl];
        [apply KG; intros HX; apply Ha; split; [exact HX | lia]|].
      destruct (Z_lt_le_dec a (LA_G_NL + NK_SIZE)) as [Hh | Hh];
        [|apply KG; intros HX; apply Ha; split; [exact HX | lia]].
      destruct Dk as (((_ & _ & D1) & _) & DL). destruct Dk2 as (((_ & _ & D2) & _) & _).
      replace a with (LA_G_NL + Z.of_nat (Z.to_nat (a - LA_G_NL))) by lia.
      rewrite (D1 (Z.to_nat (a - LA_G_NL)) ltac:(lia)), (D2 (Z.to_nat (a - LA_G_NL)) ltac:(lia)). reflexivity. }
    assert (Htab2 : aiftab_at SEGS (rdW W2 (ms_mem ms2)) LA_G_NL kbs lf_tab).
    { destruct Dtab as (Hn & H80 & Ht). split; [exact Hn|]. split; [exact H80|].
      intros i nm0 ix Hi. destruct (Ht i nm0 ix Hi) as (Hix & p & Hp & Hp0 & Hs & Hx).
      destruct (lf_tab_entry i nm0 ix Hi) as (H64 & Hlt & Hge).
      assert (Hp' : au64_at SEGS (rdW W2 (ms_mem ms2)) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p).
      { apply (au64_keep SEGS X' _ _ _ p KG'); [|exact Hp]. intros k Hk (_ & HG). apply HG. unfold NK_IF_NAME, NK_SIZE. lia. }
      split; [exact Hix|]. exists p. split; [exact Hp'|]. split; [exact Hp0|].
      split; [|apply (au32_keep SEGS X' _ _ _ ix KG'); [|exact Hx]; intros k Hk (_ & HG); apply HG;
               unfold NK_IF_INDEX, NK_SIZE; lia].
      pose proof Hs as ((Hpa & Hpb & _) & _). rewrite length_app in Hpb. cbn [length] in Hpb.
      destruct (Nat.lt_ge_cases i 60) as [Hi60 | Hi60].
      - destruct (Difp (Z.of_nat i) ltac:(lia)) as (q & Hq & Hq1 & _).
        pose proof (val_mem8_mod SEGS _ _ p q Hp Hq) as Epq. rewrite (Hq1 ltac:(lia)) in Epq.
        pose proof (Hlt Hi60) as Hlen. assert (Hd : 0 <= Z.of_nat i / 15 <= 3) by lia.
        rewrite (Z.mod_small p) in Epq by lia. rewrite Z.mod_small in Epq by (unfold LA_G_NAMES; lia).
        apply (acstr_keep SEGS X' _ _ p nm0 KG'); [|exact Hs]. intros j Hj (HX & _).
        apply (GX (p + Z.of_nat 0 + j - Z.of_nat 0)); [right; left; unfold LA_G_NAMES, G_NAMES_SIZE in *; lia|].
        replace (p + Z.of_nat 0 + j - Z.of_nat 0) with (p + j) by lia. exact HX.
      - pose proof (Hge Hi60) as Hnm0.
        destruct (Hodd2 (i - 59)%nat ltac:(lia)) as (q' & Hq' & _ & Hs' & _).
        destruct (Hifp2 (Z.of_nat i) ltac:(lia)) as (q & Hq & _ & Hq2).
        pose proof (val_mem8_mod SEGS _ _ p q Hp' Hq) as Epq.
        assert (Eq : q mod 2 ^ 64 = q' mod 2 ^ 64).
        { apply (val_mem8_mod SEGS (rdW W2 (ms_mem ms2)) (LA_ODD + 8 * Z.of_nat (i - 59))); [|exact Hq'].
          replace (Z.of_nat (i - 59)) with (Z.of_nat i - 59) by lia. exact (Hq2 ltac:(lia)). }
        pose proof Hs' as ((Hqa & Hqb & _) & _). rewrite length_app in Hqb. cbn [length] in Hqb.
        rewrite (Z.mod_small p) in Epq by lia. rewrite (Z.mod_small q') in Eq by lia.
        assert (Ep : p = q') by (rewrite Epq; exact Eq).
        rewrite Ep, Hnm0. exact Hs'. }
    exists kbs, gbs. split; [split; [intros _; split; [reflexivity | split; [reflexivity | exact Rrc]] | intros H; contradiction]|].
    split; [exact Dkwf|]. intros HAre.
    refine (conj Dk2 (conj Dwf (conj Htab2 (conj Dop (conj Dmis (conj Doc (conj Hmd2 (conj Dmwf (conj Hmk2
      (conj Dkwf (conj HAre (conj Hifp2 (conj Hgn2 (conj Hgw2 (conj Hodd2 (conj Htx2 Hla2)))))))))))))))).
  - (* a0 = the marks block *)
    assert (A0m : aarg regs 0 = mk) by (destruct Ha0; [contradiction | assumption]).
    pose proof (Rmk A0 kbs lf_tab nm gbs Dk Dtab Hnm ltac:(rewrite A0m; exact Dmk)) as RM. cbv zeta in RM.
    destruct RM as (Rrc & (gbs' & Hmk2 & Hkwf2 & Hnames & Hn)
      & (kbs' & Dk2 & Dwf2 & Hch & Hend & Hnif & Htab2 & Hnx & Hsent & Hns & Hop2 & Hmis2 & Hoc2 & Hopd)).
    rewrite A0m in Hmk2.
    exists kbs', gbs'. split.
    { split; [intros H; contradiction|]. intros _. cbv zeta.
      split; [exact Rrc|]. split; [exact Hnames|]. split; [exact Hn|]. split; [exact Hch|]. split; [exact Hend|].
      split; [exact Hnif|]. split; [exact Hnx|]. split; [exact Hsent|]. split; [exact Hns | exact Hopd]. }
    split; [exact Hkwf2|]. intros HAre.
    refine (conj Dk2 (conj Dwf2 (conj Htab2 (conj Hop2 (conj _ (conj _ (conj Hmd2 (conj Dmwf (conj Hmk2
      (conj Hkwf2 (conj HAre (conj Hifp2 (conj Hgn2 (conj Hgw2 (conj Hodd2 (conj Htx2 Hla2)))))))))))))))).
    + rewrite Hmis2. exact Dmis.
    + lia.
Qed.


(* ==========================================================================
   2. The FILE: the opening call and a later one
   ========================================================================== *)

Lemma mqp_heads_of_au64 : forall (m : word -> option byte) v, MS = link_amf ->
  au64_at SEGS m LA_G_SINK v -> au64_at SEGS m LA_G_SAY v -> au64_at SEGS m LA_OFL_HEAD v ->
  amf_heads SEGS MS m v.
Proof.
  intros m v HMS H1 H2 H3. rewrite HMS. unfold amf_heads. cbn [amf_sink_addr amf_say_addr link_amf].
  split; [exact H1|]. split; [exact H2|]. unfold amf_ofl_head. cbn [amf_ofl_lock link_amf]. exact H3.
Qed.

(* lf_blocks across the opening call: the block list grows by the FILE block, the kept set from [] to it *)
Lemma lf_blocks_open : forall cx md mk ly3 S3 ly2 S2 sink m,
  Permutation (ablocks B ly2 S2) (ablocks B ly3 S3 ++ [(sink, AMF_BLOCK)]) ->
  lf_blocks B cx md mk [] ly3 S3 m -> lf_blocks B cx md mk [(sink, AMF_BLOCK)] ly2 S2 m.
Proof.
  intros cx md mk ly3 S3 ly2 S2 sink m HP (B1 & B2 & B3 & B4 & _ & _ & Brest).
  split; [apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact B1|].
  split; [apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact B2|].
  split; [exact B3|]. split; [exact B4|].
  split; [intros [E | []]; injection E as _ E; unfold MD_SIZE, AMF_BLOCK in E; lia|].
  split; [intros [E | []]; injection E as _ E; unfold MK_SIZE, AMF_BLOCK in E; lia|].
  exact Brest.
Qed.

(* lf_jbk across the opening call *)
Lemma lf_jbk_open : forall cx fp k2 ev mo wl ly3 S3 W3 ms3 md3 ly2 S2 (W2 : world SEGS) ms2 md2 md mk sink k' ev' mo' wl',
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl LF_LIVE_HELD ly3 S3 W3 ms3 md3 [] [(md, MD_SIZE); (mk, MK_SIZE)] ->
  (forall c q, frame_addr ly2 c q = frame_addr (c_ly cx) c q) ->
  k' <= ev' -> (wl <= wl')%nat ->
  (length (wild_part (as_universe B) (st_depot S2)) <= length (wild_part (as_universe B) (st_depot S3)))%nat ->
  Permutation (ablocks B ly2 S2) (ablocks B ly3 S3 ++ [(sink, AMF_BLOCK)]) ->
  m_fds md2 = m_fds md3 -> m_fs md2 = m_fs md3 ->
  amf_heads SEGS MS (rdW W2 (ms_mem ms2)) sink -> amemfile_at SEGS MS (rdW W2 (ms_mem ms2)) sink ->
  amf_env SEGS MS (rdW W2 (ms_mem ms2)) -> val_mem SEGS (rdW W2 (ms_mem ms2)) la_nul 1 0 ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) (ms_mem ms2)) ->
  abytes SEGS (rdW W2 (ms_mem ms2)) (c_p cx) (c_pl cx) ->
  (forall a, 0 <= a < c_n cx ->
     aview SEGS (w_H W2) (ms_mem ms2) (c_p cx + a) = aview SEGS (w_H (c_W cx)) (c_mem cx) (c_p cx + a)) ->
  lf_jbk B MT MS la_nul cx fp k' ev' mo' wl' LF_LIVE_HELD ly2 S2 W2 ms2 md2 [(sink, AMF_BLOCK)]
    [(md, MD_SIZE); (mk, MK_SIZE)].
Proof.
  intros cx fp k2 ev mo wl ly3 S3 W3 ms3 md3 ly2 S2 W2 ms2 md2 md mk sink k' ev' mo' wl'
    (J1 & JL & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & (D & HT & HP) & J12 & J13 & J14 & J15 & J16)
    Hfa Hk Hwl Hw2 HP2 Hfd Hfs Hh Hf Henv Hla Hro Hpl Hpv.
  assert (HcT : c_T cx = [] /\ D = []) by (destruct (c_T cx), D; try discriminate; split; reflexivity).
  destruct HcT as (HcT & HD). subst D.
  assert (HP3 : Permutation (ablocks B ly2 S2)
                  ([(md, MD_SIZE); (mk, MK_SIZE)] ++ [(sink, AMF_BLOCK)] ++ ablocks B (c_ly cx) (c_S cx))).
  { apply (perm_trans HP2). cbn [app] in HP |- *.
    apply (perm_trans (Permutation_app_tail [(sink, AMF_BLOCK)] HP)). cbn [app].
    apply perm_skip, perm_skip. apply Permutation_sym, Permutation_cons_append. }
  split; [exact Hk|].
  split.
  { rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ HP3), !bsum_app, <- (blocks_bytes_bsum B (c_ly cx) (c_S cx)).
    cbn [bsum fold_right snd]. unfold LF_LIVE_HELD. lia. }
  split; [exact Hfa|]. split; [exact J3|]. split; [rewrite Hfd; exact J4|]. split; [rewrite Hfs; exact J5|].
  split; [apply MT_LE|]. split; [lia|].
  split; [right; exists sink; split; [exact Hh|]; split; [reflexivity | exact Hf]|].
  split; [exact Henv|].
  split; [exists [(sink, AMF_BLOCK)]; split; [rewrite HcT; reflexivity | exact HP3]|].
  split; [intros x [<- | []]; apply (Permutation_in _ (Permutation_sym HP2)); apply in_or_app; right; left; reflexivity|].
  split; [exact Hla|]. split; [exact Hro|]. split; [exact Hpl | exact Hpv].
Qed.

(* lf_jbk across a later call: the kept FILE stays, its bytes are the callee's *)
Lemma lf_jbk_again : forall cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 ly2 S2 (W2 : world SEGS) ms2 md2 own sink k',
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 [(sink, AMF_BLOCK)] own ->
  (forall c q, frame_addr ly2 c q = frame_addr (c_ly cx) c q) -> k' <= ev ->
  S2 = set_fs (st_fs S2) S3 -> Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) ->
  m_fds md2 = m_fds md3 -> m_fs md2 = m_fs md3 ->
  amf_heads SEGS MS (rdW W2 (ms_mem ms2)) sink -> amemfile_at SEGS MS (rdW W2 (ms_mem ms2)) sink ->
  amf_env SEGS MS (rdW W2 (ms_mem ms2)) -> val_mem SEGS (rdW W2 (ms_mem ms2)) la_nul 1 0 ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) (ms_mem ms2)) ->
  abytes SEGS (rdW W2 (ms_mem ms2)) (c_p cx) (c_pl cx) ->
  (forall a, 0 <= a < c_n cx ->
     aview SEGS (w_H W2) (ms_mem ms2) (c_p cx + a) = aview SEGS (w_H (c_W cx)) (c_mem cx) (c_p cx + a)) ->
  lf_jbk B MT MS la_nul cx fp k' ev mo wl lv ly2 S2 W2 ms2 md2 [(sink, AMF_BLOCK)] own.
Proof.
  intros cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 ly2 S2 W2 ms2 md2 own sink k'
    (J1 & JL & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & (D & HT & HP) & J12 & J13 & J14 & J15 & J16)
    Hfa Hk Hs2 Hperm Hfd Hfs Hh Hf Henv Hla Hro Hpl Hpv.
  split; [exact Hk|].
  split; [rewrite Hs2; exact JL|]. split; [exact Hfa|]. split; [exact J3|].
  split; [rewrite Hfd; exact J4|]. split; [rewrite Hfs; exact J5|]. split; [apply MT_LE|].
  split; [rewrite Hs2; exact J7|].
  split; [right; exists sink; split; [exact Hh|]; split; [reflexivity | exact Hf]|].
  split; [exact Henv|].
  split; [exists D; split; [exact HT | exact (perm_trans Hperm HP)]|].
  split; [intros x Hx; apply (Permutation_in x (Permutation_sym Hperm)); exact (J12 x Hx)|].
  split; [exact Hla|]. split; [exact Hro|]. split; [exact Hpl | exact Hpv].
Qed.

End b.
End a.

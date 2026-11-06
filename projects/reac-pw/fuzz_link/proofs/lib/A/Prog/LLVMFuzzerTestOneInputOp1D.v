(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module paths and module names changed; 506 of its 559 lines of code are new or changed and 1279 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A: op_write's reac_link_alias_write (0x83868). From the cut at
   model_write's return (+0x1088, w_m_inv): `mv s2, a0; mv a0, s5; mv a1, s6; jal reac_link_alias_write`, the call
   under reac_link_alias_write_c.v's contract (the Section hypothesis ALIAS_WRITE,
   reac_link_alias_write_aproof), to the cut at its return (+0x1098, w_a_inv).
   - lf_alias_post: the cut's pieces across a callee whose writes are g_nl's bytes [0, NK_N_SENT + 4) (the library's
     write set), at the new g_nl bytes the callee's post gives (the pattern of Kpost.v lf_kernel_post).
   - w_ma : forall POST i, FROM POST (w_a_inv i) -> FROM POST (w_m_inv i).

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase LinkWalkPi LinkWalkCall.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA LinkWalkZsh.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import text_of_c kernel_c model_write_c index_of_c reac_link_alias_write_c nl_talk_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpre.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKeep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputLp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputMb.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputArmR.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp3Lib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp3K.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputArmK.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputTxa.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputArmH.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputSel.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputMdl.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputNm.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpost.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp1Lib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp1C.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition LW_aret : Z := AF_LLVMFuzzerTestOneInput + 0x1098.   (* 0x8386c, reac_link_alias_write's return *)

(* the paths +0x10a0 .. +0x10d4 take to check_refused: the cases reac_link_alias_write refuses without a socket *)
Definition w_refused (nm : option (list byte)) (t : list byte) : Prop :=
  nm = None \/ nm = Some [] \/ ALIAS_MAX <= Z.of_nat (length t) \/ (forall x, nm = Some x -> index_of lf_tab x = 0).

(* two disjoint ranges, from their bytes *)
Lemma w_apart_gnl_of : forall s n, 0 < n ->
  (forall x, s <= x < s + n -> ~ (LA_G_NL <= x < LA_G_NL + NK_SIZE)) -> apart_gnl LA_G_NL s n.
Proof.
  intros s n Hn H. unfold apart_gnl.
  destruct (Z_le_gt_dec (s + n) LA_G_NL) as [H1 | H1]; [left; exact H1|].
  destruct (Z_le_gt_dec (LA_G_NL + NK_SIZE) s) as [H2 | H2]; [right; exact H2|].
  exfalso. apply (H (Z.max s LA_G_NL)); unfold NK_SIZE in *; lia.
Qed.
Lemma w_apart_of : forall a n b k, 0 < n -> 0 < k ->
  (forall x, a <= x < a + n -> ~ (b <= x < b + k)) -> apart a n b k.
Proof.
  intros a n b k Hn Hk H. unfold apart.
  destruct (Z_le_gt_dec (a + n) b) as [H1 | H1]; [left; exact H1|].
  destruct (Z_le_gt_dec (b + k) a) as [H2 | H2]; [right; exact H2|].
  exfalso. apply (H (Z.max a b)); lia.
Qed.

(* the selector's name lies apart from g_nl *)
Lemma w_name_gnl : forall s x, w_name s (Some x) -> (length x <= 11)%nat -> apart_gnl LA_G_NL s (Z.of_nat (length x) + 1).
Proof.
  intros s x [(_ & Hn) | [(k & Hk & -> & _) | (j & Hj & -> & _)]] Hl; [discriminate| |].
  - right. unfold LA_G_NAMES, LA_G_NL, NK_SIZE. lia.
  - left. rewrite w_odd_ptrs. unfold LA_G_NL. do 6 (destruct j as [|j]; [cbn; lia|]). lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.
Hypothesis LV : LinkVals (L := link_listing).
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
Hypothesis MT_LE : forall S S' m, mo_le MT S S' m.
(* reac_link_alias_write, as proved (reac_link_alias_write_aproof) *)
Hypothesis ALIAS_WRITE : forall fy : YK11.FPState,
  @reac_link_alias_write_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.

#[local] Abbreviation BASEF cx := (@lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Abbreviation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).
Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

(* the cut at reac_link_alias_write's return (+0x1098): a0 is the library's code, s2 the model's; g_nl is the
   library's new bytes; o0 is g_nl.opened before the call (in s4) *)
Definition w_a_inv (i : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N s s6v own1 o0 : Z) (nm : option (list byte)) (t : list byte) (K0 : kstate)
    (kbs mbs gbs : list byte) (T3 nb : list (Z * Z)),
  0 <= i <= 47 /\ lf_shape fy LW_aret ms3 /\ lf_core cx ms3 /\ w_regs cx fp i s s6v ms3 /\ w_name s nm /\
  getr (ms_regs ms3) 20 = w64 o0 /\ 0 <= o0 <= 64 * i /\
  getr (ms_regs ms3) 18 = w64 (w_rc (write_model lf_tab nm (Some t) [] K0)) /\
  getr (ms_regs ms3) 10 = w64 (w_rc (write_lib lf_tab nm (Some t) [] K0)) /\
  ak_cut SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 (nb ++ [(md, MD_SIZE); (mk, MK_SIZE)])
    (lf_ev i + 1) (lf_mo LF_MO_SET LF_MO_OP i) (S (lf_wl i)) (LF_LIVE_HELD + TEXT_OF_LIVE) k2 ly3 S3 W3 ms3 md3 /\
  lf_cur cx W3 ms3 P N /\
  o0 <= nk_opened kbs <= o0 + 1 /\ (w_refused nm t -> nk_opened kbs = o0) /\
  dec_ans B ly3 S3 (rdW W3 (ms_mem ms3)) s6v t /\ tx_ans B SEGS own1 nb ly3 S3 (rdW W3 (ms_mem ms3)) s6v t /\
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (lf_sp1 cx + LS_T130) = Some own1 /\ tx_nb own1 nb /\
  (own1 <> 0 -> own1 = s6v) /\ w_fresh B cx md mk T3 ly3 S3 nb /\
  nk_sent kbs = md_reqs mbs /\ - 2 ^ 31 <= w_rc (write_lib lf_tab nm (Some t) [] K0) < 2 ^ 31.

(* the cut's pieces across a callee that writes g_nl's bytes [0, NK_N_SENT + 4) only, at the callee's new g_nl *)
Lemma lf_alias_post : forall cx fp k2 ev mo wl lv md mk kbs mbs gbs T3 own P N K E
    ly3 S3 (W3 : world SEGS) ms3 md3 ly2 S2 (W2 : world SEGS) ms2 md2 kbs',
  BASEF cx ->
  ak_cut SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 own ev mo wl lv k2 ly3 S3 W3 ms3 md3 ->
  JRN cx fp ly2 S2 W2 (ms_mem ms2) md2 k2 -> frames S2 = frames S3 ->
  lf_call B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E ->
  (forall a, E a -> LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4) ->
  S2 = set_fs (st_fs S2) S3 -> Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) ->
  m_fds md2 = m_fds md3 -> m_fs md2 = m_fs md3 ->
  lf_cur cx W3 ms3 P N ->
  anlk_at SEGS (rdW W2 (ms_mem ms2)) LA_G_NL kbs' -> nlk_wf kbs' ->
  aiftab_at SEGS (rdW W2 (ms_mem ms2)) LA_G_NL kbs' lf_tab ->
  nk_open kbs' = 0 -> nk_misuse kbs' = 0 -> nk_opened kbs' = nk_closed kbs' ->
  ak_cut SK B MT MS la_nul cx fp md mk kbs' mbs gbs T3 own ev mo wl lv k2 ly2 S2 W2 ms2 md2 /\
  lf_cur cx W2 ms2 P N /\
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) (ms_mem ms2)).
Proof.
  intros cx fp k2 ev mo wl lv md mk kbs mbs gbs T3 own P N K E ly3 S3 W3 ms3 md3 ly2 S2 W2 ms2 md2 kbs'
    HB HC HJ2 Hfr2 LC EE Hs2 Hperm Hfd Hfs Hcur Hk' Hwf' Htab' Hop' Hmis' Hoc'.
  destruct HC as (HJ3 & Hfr & Hsv & Hhd & Hfsh & Hsl & Hjbk & Hblk & Hdat).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as (HPRE & _ & HGX & HLN & HMS & _).
  destruct (lf_img_facts B MS la_nul HSEGS TB HMS HLN) as (IMG & RIMG).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ3) as (Hs1 & H16 & Hlo & H47).
  pose proof LC as (HK0 & HKc & _).
  pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (HAR3 & _).
  pose proof HJ2 as (_ & _ & (memS2 & HJi2 & _) & _). pose proof HJi2 as (HAR2 & _).
  pose proof Hjbk as (_ & _ & Hfa & _ & _ & _ & _ & _ & Hgi & _ & _ & Hinc & Hla0 & HRO & _).
  pose proof Hblk as (Bmd & Bmk & _).
  assert (Hin : In (LF_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
  assert (EI : forall a, E a -> in_img SEGS a).
  { intros a Ha. apply (kp_img_ok_in B MS la_nul a IMG). left. pose proof (EE a Ha). unfold NK_N_SENT, NK_SIZE in *. clia. }
  assert (ELOW : forall a, E a -> a < alloc_ceiling) by (intros a Ha; pose proof (pa_segs_low a (EI a Ha)); clia).
  assert (Hsv2 : lf_saved cx W2 ms2).
  { apply (lf_saved_callee B cx K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E LC); [|exact Hsv].
    intros a Ha HEa. pose proof (ELOW a HEa). unfold lf_saved_fp in Ha. unfold LLVMF_STK in *. clia. }
  assert (Hsl2 : lf_slots cx md mk fp W2 ms2).
  { apply (lf_slots_callee B cx K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E md mk fp LC); [|exact Hsl].
    intros a Ha HEa. pose proof (ELOW a HEa). unfold lf_slots_fp in Ha. unfold LLVMF_STK in *. clia. }
  assert (Hcur2 : lf_cur cx W2 ms2 P N).
  { apply (lf_cur_callee B cx K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E P N LC); [|exact Hcur].
    intros a Ha HEa. pose proof (ELOW a HEa). unfold lf_cur_fp in Ha. unfold LS_P, LS_N, LLVMF_STK in *. clia. }
  assert (FNE : forall a, (lf_F cx fp <= a < lf_F cx fp + 1024 \/ lf_SH cx fp <= a < lf_SH cx fp + 128) -> ~ E a).
  { intros a Ha HEa. destruct (kp_frame_place B LAWS cx fp ly3 S3 W3 (ms_mem ms3) md3 a HAR3 Hin Hfa Ha) as (Hni & _).
    exact (Hni (EI a HEa)). }
  assert (Hhd2 : lf_header cx fp W2 ms2).
  { apply (lf_header_callee B cx fp K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E LC Hin Hfa); [|exact Hhd].
    intros a Ha. apply FNE. left. unfold lf_header_fp in Ha. change (fs_frame_bytes LF_CID) with 1024 in Ha. clia. }
  assert (Hfsh2 : lf_fshadow cx fp W2 ms2 LF_SH0).
  { apply (lf_fshadow_callee B cx fp K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E LC Hin Hfa); [|exact Hfsh].
    intros a Ha. apply FNE. right. unfold lf_fshadow_fp in Ha. clia. }
  assert (Pmd : In (md, MD_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Bmd).
  assert (Pmk : In (mk, MK_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Bmk).
  assert (Hblk2 : lf_blocks B cx md mk T3 ly2 S2 (rdW W2 (ms_mem ms2))).
  { apply (ar_blocks_leaf B cx md mk T3 ly3 S3 ly2 S2 _ Hperm).
    exact (lf_blocks_callee B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E md mk T3 LC Pmd Pmk Hblk). }
  assert (HPB : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by (intros Hn; exact (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
          cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ3 Hn)).
  assert (NRO : forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> ~ E a).
  { intros a Ha HEa. apply (ar_not_ro_G HSEGS a); [|exact Ha]. unfold inG, G_HARNESS. apply Exists_cons_hd.
    unfold in_zr. cbn [fst snd]. pose proof (EE a HEa). unfold NK_N_SENT in *. clia. }
  assert (HNUL : val_mem SEGS (rdW W2 (ms_mem ms2)) la_nul 1 0).
  { apply (lf_la_nul_callee B MS la_nul cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E IMG LC); [|exact Hla0].
    intros HEa. pose proof (EE _ HEa). rewrite HLN in *. unfold LA_NUL, LA_LONG_ALIAS, LA_G_NL, NK_N_SENT in *. clia. }
  assert (Hjbk2 : lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly2 S2 W2 ms2 md2 T3 own).
  { apply (ar_jbk_leaf SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp k2 ev mo wl lv
      ly3 S3 ly2 S2 W2 ms2 md2 T3 own k2 HB HJ2 Hs2 Hperm).
    apply (lf_jbk_callee B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own K ly2 S2 W2 ms2 md2 E
      IMG RIMG LC); [| exact NRO | exact HPB | exact Hfd | exact Hfs | exact HNUL | exact Hjbk].
    intros a Ha HEa. pose proof (EE a HEa) as Hr. destruct Ha as [Ha | Ha].
    - destruct Ha as [Ha | [Ha | (f & n & Hfn & Ha)]].
      + rewrite HMS in Ha. cbv [amf_head_addr link_amf amf_sink_addr amf_say_addr amf_ofl_head amf_ofl_lock] in Ha.
        unfold LA_G_NL, NK_N_SENT in *; clia.
      + rewrite HMS in Ha. cbv [amf_env_addr link_amf amf_threaded amf_need_locks amf_ofl_lock] in Ha.
        unfold LA_G_NL, NK_N_SENT in *; clia.
      + assert (HfnT : In (f, n) (ablocks B ly3 S3)) by exact (Hinc _ Hfn).
        assert (Hn : n = AMF_BLOCK).
        { destruct Hgi as [(_ & HT) | (f' & _ & HT & _)]; rewrite HT in Hfn; [destruct Hfn|].
          destruct Hfn as [Hq | []]. injection Hq as _ <-. reflexivity. }
        subst n.
        destruct (kp_blk_place B LAWS ly3 S3 W3 (ms_mem ms3) md3 f AMF_BLOCK a HAR3 HfnT
          ltac:(unfold req_size, AMF_BLOCK in *; cbn; clia)) as (Hni & _).
        exact (Hni (EI a HEa)).
    - assert (Hn : 0 < c_n cx) by clia.
      destruct (kp_blk_place B LAWS ly3 S3 W3 (ms_mem ms3) md3 (c_p cx) (c_n cx) a HAR3 (HPB Hn)
        ltac:(unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); clia)) as (Hni & _).
      exact (Hni (EI a HEa)). }
  assert (HRO2 : arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) (ms_mem ms2)))
    by exact (lf_aro_callee B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E RIMG LC NRO HRO).
  destruct (lf_odd_texts_of_ro B TB HSEGS W2 (ms_mem ms2) HRO2) as (Hodd2 & Htx2).
  pose proof (lf_call_kagree B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E LC) as KG.
  destruct Hdat as (Dk & Dwf & Dtab & Dop & Dmis & Doc & Dmd & Dmwf & Dmk & Dkwf & Dare & Difp & Dgn & Dgw & Dodd
    & Dtx & Dla).
  assert (WB : forall b n, In (b, n) (ablocks B ly2 S2) -> wcarry SEGS (rdW W3 (ms_mem ms3)) (rdW W2 (ms_mem ms2)) b n).
  { intros b n Hbn ii Hii _. destruct (al_blocks _ _ LAWS ly2 S2 W2 (ms_mem ms2) md2 b n HAR2 Hbn) as (_ & _ & _ & _ & Hp & _).
    apply (apresent_writable SEGS). apply (proj1 (Hp (b + ii) ltac:(unfold req_size; destruct (Z.eqb_spec n 0); clia))). }
  assert (BX : forall b n a, In (b, n) (ablocks B ly3 S3) -> b <= a < b + n ->
    ~ lf_X B ly3 S3 ly2 S2 (lf_sp1 cx - K) (lf_sp1 cx) E a).
  { intros b n a Hbn Ha. apply (lfx_blk B ly3 S3 ly2 S2 _ _ E b n a Hbn Ha). intros HEa.
    destruct (kp_blk_place B LAWS ly3 S3 W3 (ms_mem ms3) md3 b n a HAR3 Hbn
      ltac:(unfold req_size; destruct (Z.eqb_spec n 0); clia)) as (Hni & _).
    exact (Hni (EI a HEa)). }
  assert (IMX : forall a, lf_img_fp MS la_nul a -> ~ E a ->
    ~ lf_X B ly3 S3 ly2 S2 (lf_sp1 cx - K) (lf_sp1 cx) E a)
    by (intros a Ha HEa; exact (lfx_imgfp B MS la_nul ly3 S3 ly2 S2 _ _ E a IMG Ha HEa)).
  assert (NEo : forall a, ~ (LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4) -> ~ E a)
    by (intros a Ha HEa; exact (Ha (EE a HEa))).
  assert (Hdat2 : lf_data cx md mk kbs' mbs gbs (rdW W2 (ms_mem ms2))).
  { refine (conj Hk' (conj Hwf' (conj Htab' (conj Hop' (conj Hmis' (conj Hoc' (conj _ (conj Dmwf (conj _
      (conj Dkwf (conj Dare (conj _ (conj _ (conj _ (conj Hodd2 (conj Htx2 _)))))))))))))))).
    - apply (amodel_keep SEGS _ _ _ md mbs KG (WB md MD_SIZE Pmd)); [|exact Dmd].
      intros ii Hii. apply (BX md MD_SIZE); [exact Bmd | clia].
    - apply (amarks_keep SEGS _ _ _ mk gbs KG (WB mk MK_SIZE Pmk)); [|exact Dmk].
      intros ii Hii. apply (BX mk MK_SIZE); [exact Bmk | clia].
    - intros e He. destruct (Difp e He) as (qq & Hq1 & Hq2 & Hq3). exists qq.
      split; [|split; [exact Hq2|]].
      + apply (au64_keep SEGS _ _ _ _ _ KG); [|exact Hq1]. intros kk Hkk. apply IMX.
        * left. unfold NK_IF_NAME, NK_SIZE in *. clia.
        * apply NEo. unfold NK_IF_NAME, NK_N_SENT in *. clia.
      + intros H60. apply (au64_keep SEGS _ _ _ _ _ KG); [|exact (Hq3 H60)]. intros kk Hkk. apply IMX.
        * right; right; right; right; right; right. clia.
        * apply NEo. unfold LA_ODD, LA_G_NL in *. clia.
    - apply (lf_gnames_at_keep _ _ _ 64 KG ltac:(clia)); [|exact Dgn]. intros a Ha. apply IMX.
      + right; left. exact Ha.
      + apply NEo. unfold LA_G_NAMES, G_NAMES_SIZE, LA_G_NL, NK_N_SENT in *. clia.
    - apply (lf_gnames_w_keep _ _ _ KG); [| |exact Dgw].
      + assert (Hw : forall (m' : word -> option byte) a, LA_G_NAMES <= a < LA_G_NAMES + 512 -> writable_at SEGS m' a)
          by (rewrite HSEGS; exact LA_G_NAMES_writable).
        intros ii Hii _. apply Hw. unfold G_NAMES_SIZE in Hii. clia.
      + intros a Ha. apply IMX.
        * right; left. exact Ha.
        * apply NEo. unfold LA_G_NAMES, G_NAMES_SIZE, LA_G_NL, NK_N_SENT in *. clia.
    - destruct Dla as ((la & Hla & Hlal) & Hnul0 & _).
      split; [exists la; split; [|exact Hlal] | split].
      + apply (au8arr_keep SEGS _ _ _ LA_LONG_ALIAS la KG); [| |exact Hla].
        * intros ii Hii _. generalize (rdW W2 (ms_mem ms2)). rewrite HSEGS. intros m2.
          apply (writable_at_of_wseg tfibsegs m2 LA_LONG_ALIAS 304);
            [unfold LA_LONG_ALIAS; lia | unfold LA_LONG_ALIAS; lia | exact wseg_LA_LONG_ALIAS304 | lia].
        * intros ii Hii. apply IMX; [right; right; left; clia | apply NEo; unfold LA_LONG_ALIAS, LA_G_NL, NK_N_SENT in *; clia].
      + apply (val_mem_keep SEGS _ _ _ (LA_LONG_ALIAS + 300) 1 0 KG); [|exact Hnul0].
        intros kk Hkk. apply IMX; [right; right; left; clia | apply NEo; unfold LA_LONG_ALIAS, LA_G_NL, NK_N_SENT in *; clia].
      + exact (lf_la_slack_any HSEGS _). }
  split; [|split; [exact Hcur2 | exact HRO2]].
  split; [exact HJ2|]. split; [rewrite Hfr2; exact Hfr|]. split; [exact Hsv2|]. split; [exact Hhd2|].
  split; [exact Hfsh2|]. split; [exact Hsl2|]. split; [exact Hjbk2|]. split; [exact Hblk2 | exact Hdat2].
Qed.

(* an interface-table string lies in g_names or below g_nl *)
Lemma w_tab_place : forall cx md mk kbs mbs gbs (W : world SEGS) mem i n2 ix p,
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  lf_data cx md mk kbs mbs gbs (rdW W mem) -> nth_error lf_tab i = Some (n2, ix) ->
  au64_at SEGS (rdW W mem) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
  (LA_G_NAMES <= p /\ p + Z.of_nat (length n2) + 1 <= LA_G_NAMES + 512) \/
  p + Z.of_nat (length n2) + 8 <= LA_G_NL.
Proof.
  intros cx md mk kbs mbs gbs W mem i n2 ix p HRO HD Hn Hp Rp.
  destruct HD as (_ & _ & Htab & _ & _ & _ & _ & _ & _ & _ & _ & Difp & _).
  pose proof Htab as (_ & _ & Htent).
  destruct (Htent i n2 ix Hn) as (_ & p0 & Hp0 & _ & Hs0 & _).
  assert (Hi64 : (i < 64)%nat).
  { assert (Hl : (i < length lf_tab)%nat) by (apply nth_error_Some; rewrite Hn; discriminate).
    pose proof lf_tab_len as LL. lia. }
  destruct (Difp (Z.of_nat i) ltac:(lia)) as (qq & Hqq & Hqlo & Hqhi).
  pose proof (kp_vm8_mod _ _ _ _ _ Hp Hqq) as Ep. pose proof (kp_vm8_mod _ _ _ _ _ Hp0 Hqq) as E0.
  rewrite (Z.mod_small p) in Ep by exact Rp.
  assert (R0 : 0 <= p0 < 2 ^ 64) by (destruct Hs0 as ((A1 & A2 & _) & _); rewrite length_app in A2; cbn [length] in A2; lia).
  rewrite (Z.mod_small p0) in E0 by exact R0.
  assert (Epp : p = p0) by congruence. rewrite <- Epp in Hs0. clear E0.
  pose proof (eq_refl (as_owned_static B)) as Ho. pose proof (eq_refl (as_errno B)) as He.
  pose proof (kp_img_here B TB HSEGS) as KI. unfold kp_img_b in KI.
  repeat match type of KI with (_ && _)%bool = true => apply andb_prop in KI as [KI ?] end.
  match goal with Hh : forallb _ (seq 1 4) = true |- _ => rename Hh into KOdd end.
  destruct (Z_lt_le_dec (Z.of_nat i) 60) as [Hlt | Hge].
  - left. rewrite (Hqlo Hlt) in Ep. rewrite Z.mod_small in Ep by (unfold LA_G_NAMES; lia).
    assert (Hlen : (length n2 <= 4)%nat).
    { pose proof lf_tab_gnames_short as Hg. rewrite forallb_forall in Hg.
      specialize (Hg (n2, ix)). apply Nat.leb_le. apply Hg.
      apply (nth_error_In _ i). rewrite nth_error_firstn. destruct (Nat.ltb_spec i 60); [exact Hn | lia]. }
    unfold LA_G_NAMES in *. lia.
  - right. specialize (Hqhi Hge). set (j := (i - 59)%nat).
    assert (Hj : (1 <= j < 5)%nat) by (unfold j; lia).
    pose proof (proj1 (forallb_forall _ _) KOdd j ltac:(apply in_seq; lia)) as Hx. cbv beta zeta in Hx.
    apply andb_prop in Hx as [Hw Hks].
    pose proof (kp_val_mem8 SEGS _ _ B (w_H W) mem _ _ Ho He HRO Hw) as Hv.
    replace (LA_ODD + 8 * (Z.of_nat i - 59)) with (LA_ODD + 8 * Z.of_nat j) in Hqhi by (unfold j; lia).
    pose proof (kp_vm8_mod _ _ _ _ _ Hqhi Hv) as Eq.
    destruct (kp_kstr_acstr B (w_H W) mem _ _ HRO Hks) as (Hst & Hpt0 & Hptl).
    assert (Hpq : p = fst (nth j KP_ODD (0, []))).
    { rewrite <- (Z.mod_small p (2 ^ 64)) by exact Rp. rewrite <- (Z.mod_small (fst (nth j KP_ODD (0, []))) (2 ^ 64))
        by (unfold LA_G_NL in Hptl; lia).
      pose proof (kp_vm8_mod _ _ _ _ _ Hp Hqq) as E1. rewrite E1, Eq. reflexivity. }
    rewrite Hpq in Hs0.
    pose proof (kp_acstr_unique _ _ _ _ _ Hs0 Hst) as En. subst n2. rewrite Hpq. rewrite length_map. exact Hptl.
Qed.

(* the text_of answer lies apart from g_nl *)
Lemma w_ans_gnl : forall ly S (W : world SEGS) mem mdl s t,
  lf_img_ok B MS la_nul -> AR SEGS B ly S W mem mdl -> arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  dec_ans B ly S (rdW W mem) s t -> apart_gnl LA_G_NL s (Z.of_nat (length t) + 1).
Proof.
  intros ly S W mem mdl s t IMG HAR HRO [(i & Hi & -> & ->) | (k & Hin & Hk & Hcs)].
  - pose proof (kp_img_here B TB HSEGS) as KI. unfold kp_img_b in KI.
    repeat match type of KI with (_ && _)%bool = true => apply andb_prop in KI as [KI ?] end.
    match goal with H : forallb _ (seq 0 11) = true |- _ => rename H into KTx end.
    pose proof (kp_forallb_seq _ _ KTx i Hi) as Hx. cbv beta zeta in Hx. apply andb_prop in Hx as [_ Hks].
    destruct (kp_kstr_acstr B (w_H W) mem _ _ HRO Hks) as (_ & _ & Hptl).
    left. rewrite length_map. lia.
  - apply w_apart_gnl_of; [lia|]. intros x Hx Hg.
    destruct (kp_blk_place B LAWS ly S W mem mdl s k x HAR Hin
      ltac:(unfold req_size; destruct (Z.eqb_spec k 0); lia)) as (Hni & _).
    apply Hni. apply (kp_img_ok_in B MS la_nul x IMG). left. exact Hg.
Qed.

Lemma w_ma : forall POST i,
  FROM POST (w_a_inv i) ->
  FROM POST (w_m_inv SK B MT MS la_nul LF_MO_SET LF_MO_OP i).
Proof.
  intros POST i HL cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HMI.
  destruct HMI as (md & mk & P & N & s & s6v & own1 & nm & t & kbs & mbs & gbs & T3 & nb & Hi & Hsh & Hcore & Hreg &
    Hnm & R20 & R10 & HC & Hcur & Hop & HD & HTX & HSL & Hnb & Hown & Hfresh & SENT0 & Hrqm & Hrng).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof (lv_text LV) as HBASE.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof alloc_ceiling_value as (CV & _).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof Hreg as (R19 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
  destruct (lf_img_facts B MS la_nul HSEGS TB HMS HLN) as (IMG & RIMG).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & Hs16 & Hlo & H47').
  rewrite (lf_shape_eta fy LW_mret ms3 Hsh).
  pose proof (d4_entry fy W3 (ms_regs ms3) (ms_mem ms3) LW_mret) as HS.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg (ms_regs ms3) []))
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LW_mret)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) []))) by apply Eimg_env.
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) []) n)
    by (intros n Hn; rewrite HEdef; apply Eimg_low; exact Hn).
  clear HEdef.
  paj_run_tok RUN HS HJ SHOK (0, 0); [apply awr_ok_x_nil|].
  rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
  pose proof (d4_keep_run fy W3 _ _ msA (ms_regs ms3) _ W_R HS EL W_R_low ltac:(d4chk)) as KR.
  pose proof (kagree_frame_nil _ _ _ HFrA) as KA.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdA := mdx) in * end.
  assert (FdA : m_fds mdA = m_fds md3) by (subst mdA; rewrite !lf_wvb_fds; reflexivity).
  assert (FsA : m_fs mdA = m_fs md3) by (subst mdA; rewrite !lf_wvb_fs; reflexivity).
  pose proof (ak_cut_run SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 _ _ _ _ _ k2 ly3 S3 W3 ms3 msA md3 mdA HC HJ KA
    (fun x Hx => HGA x Hx) FdA FsA) as HCA.
  pose proof (lf_cur_keep (fun _ => False) cx W3 ms3 W3 msA P N KA (fun a _ H => H) Hcur) as HcurA.
  pose proof (d4_dec_run B ly3 S3 _ _ s6v t KA HD) as HDA.
  pose proof (tx_ans_keep B own1 nb ly3 S3 ly3 S3 _ _ _ s6v t HTX (fun c H => H) KA (fun _ _ _ _ H => H)) as HTXA.
  pose proof (d4_slot_run W3 (ms_mem ms3) (ms_mem msA) _ _ KA HSL) as HSLA.
  clear HD HTX HSL Hcur HC.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (18%bv : bv 5) Q18.
  ew_reg EL 21%nat (21%bv : bv 5) Q10. ew_reg EL 22%nat (22%bv : bv 5) Q11. ew_reg EL 10%nat (10%bv : bv 5) Q18.
  rewrite R21 in Q10. rewrite R22 in Q11. rewrite R10 in Q18. rewrite HBASE in Q1.
  pose proof HCA as (HJA & HfrA & HsvA & HhdA & HfsA & HslA & HjbkA & HblkA & HdatA).
  pose proof HjbkA as (Hkev & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
  pose proof HJA as (_ & _ & (memSA & HJiA & _) & _). pose proof HJiA as (HARA & _).
  kreg KR 2 (2%bv : bv 5) K2. kreg KR 3 (3%bv : bv 5) K3. kreg KR 4 (4%bv : bv 5) K4.
  destruct (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB) as (Gp & Tp).
  assert (Rsp : spZ (ms_regs msA) = lf_sp1 cx).
  { unfold spZ. rewrite K2, R2. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
  assert (HKAK : REAC_LINK_ALIAS_WRITE_AK = 8560) by reflexivity.
  assert (HK8 : 0 <= REAC_LINK_ALIAS_WRITE_AK <= LLVMF_STK - 448) by (rewrite HKAK; unfold LLVMF_STK; lia).
  assert (HKc : alloc_ceiling <= spZ (ms_regs msA) - REAC_LINK_ALIAS_WRITE_AK)
    by (rewrite Rsp, HKAK; unfold LLVMF_STK in *; lia).
  destruct (dec_rt_ok B LAWS TB HSEGS ly3 S3 W3 (ms_mem msA) mdA (ms_regs msA) REAC_LINK_ALIAS_WRITE_AK s6v t HARA HRO
    HKc HDA) as (Tcs & Trt & Tlen & Tnz).
  pose proof Trt as (T0 & T31 & Tam & Tra & Thv & Ttail & Tfr).
  pose proof (w_name_range s nm Hnm) as Rs.
  assert (Ra0 : aarg (ms_regs msA) 0 = s) by (rewrite ar_aarg0, Q10; unfold w64; apply unsigned_lit_small; lia).
  assert (Ra1 : aarg (ms_regs msA) 1 = s6v).
  { rewrite ar_aarg1, Q11. unfold w64. apply unsigned_lit_small. unfold amem_range, kLowMemEnd, kHighMemEnd in Tam. lia. }
  pose proof (fun x (Hx : nm = Some x) => lf_name_core SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END
    TB HSEGS cx fp ly3 S3 W3 (ms_mem msA) mdA k2 md mk kbs mbs gbs s x HB HJA HRO HdatA
    ltac:(rewrite <- Hx; exact Hnm)) as NM.
  assert (NMA : astr_arg SEGS (rdW W3 (ms_mem msA)) s nm)
    by (apply (w_name_arg _ _ s nm Hnm); intros x Hx; exact (proj1 (NM x Hx))).
  assert (TA : astr_arg SEGS (rdW W3 (ms_mem msA)) s6v (Some t)) by (split; [exact Tnz | exact Tcs]).
  pose proof HdatA as (Dk & Dwf & Dtab & Dop & Dmis & Doc & Dmd & Dmwf & _).
  pose proof (u_rdn4_range kbs NK_OPENED) as Ro.
  pose proof HblkA as (BmdA & BmkA & _).
  replace (pa_sigma LS_reac_link_alias_write) with REAC_LINK_ALIAS_WRITE_A by (rewrite (lv_sigma LV); reflexivity).
  change (mkCfg (mkst (ms_regs msA) (Z_to_bv 64 REAC_LINK_ALIAS_WRITE_A) (ms_mem msA) (seg_rom SEGS)) mdA)
    with (@cfg_at fy SEGS REAC_LINK_ALIAS_WRITE_A (ms_regs msA) (ms_mem msA) mdA).
  eapply (@ar_leaf_call fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END fy).
  - exact (ALIAS_WRITE fy).
  - exact HB.
  - exact HJA.
  - exact HRO.
  - rewrite Q1, <- HBASE. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1. rewrite unsigned_lit_small by (unfold link_text; lia). unfold link_text. lia.
  - rewrite K3, R3. exact Gp.
  - rewrite K4, R4. exact Tp.
  - exact Rsp.
  - exact HK8.
  - lia.
  - unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *. clia.
  - apply (ar_side_room S3 fp _ HfrA). vm_compute. reflexivity.
  - intros a (r & Hin & Hr). unfold reac_link_alias_write_awr in Hin.
    destruct Hin as [<- | []]; cbn [fst snd] in Hr.
    apply (ar_ajw_G B cx fp ly3 S3 a). unfold inG, G_HARNESS. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
    unfold NK_N_SENT in *. clia.
  - intros a (r & Hin & Hr). unfold reac_link_alias_write_awr in Hin.
    destruct Hin as [<- | []]; cbn [fst snd] in Hr.
    apply (ar_not_ro_G HSEGS a). unfold inG, G_HARNESS. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
    unfold NK_N_SENT in *. clia.
  - (* the read set *)
    intros a [(Hz1 & u & Hu & Ha) | [(Hz1 & u & Hu & Ha) | (bs & tab & i0 & n2 & ix & p & Hbs & Htb & Hn & Hp & Hu & Ha)]].
    + rewrite Ra0 in Hz1, Hu, Ha. destruct nm as [x|].
      * pose proof (kp_acstr_unique _ _ _ _ _ Hu (proj1 (NM x eq_refl))) as Eu. subst u.
        exact (lf_name_akb SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
          cx fp ly3 S3 W3 (ms_mem msA) mdA k2 md mk kbs mbs gbs s x ly3 S3 _ _ a HB HJA HRO HdatA Hnm Ha).
      * exfalso. apply Hz1. exact NMA.
    + rewrite Ra1 in Hu, Ha.
      exact (dec_ans_akb B TB HSEGS ly3 S3 W3 (ms_mem msA) mdA s6v t _ _ a HARA HRO HDA (ex_intro _ u (conj Hu Ha))).
    + pose proof Htb as (Hnif & _ & _).
      assert (Hi0 : 0 <= Z.of_nat i0 < nk_n_if bs).
      { rewrite Hnif. assert (Hl : (i0 < length tab)%nat) by (apply nth_error_Some; rewrite Hn; discriminate). lia. }
      exact (lf_tab_akb SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
        cx fp ly3 S3 W3 (ms_mem msA) mdA k2 md mk kbs mbs gbs _ _ HB HJA HRO HdatA bs (Z.of_nat i0) p n2 a Hbs Hi0 Hp Hu Ha).
  - (* the Pre *)
    exists kbs, lf_tab, nm, (Some t).
    rewrite Ra0, Ra1.
    destruct (zsh_gnl_ard B TB SEGS ly3 S3 W3 (ms_mem msA) mdA HARA) as (Gra & Ghv).
    destruct (zsh_errno_ard B TB SEGS ly3 S3 W3 (ms_mem msA) mdA HARA) as (Era & _).
    pose proof (ts_errno B TB) as HEr. pose proof (ts_tp B TB) as HTP.
    split; [exact Dk|]. split; [exact Dwf|]. split; [exact Dop|].
    split; [unfold nk_opened, fld_u32 in *; lia|]. split; [rewrite <- Doc; unfold nk_opened, fld_u32 in *; lia|].
    split; [exact Dtab|]. split; [exact Gra|]. split; [exact Ghv|].
    split.
    { unfold aerrno_ok. rewrite HEr, HTP. split; [reflexivity|].
      split.
      { intros ii Hii. generalize (rdW W3 (ms_mem msA)). rewrite HSEGS. intros m2.
        apply (writable_at_of_wseg tfibsegs m2 TFIB_ERRNO 4);
          [unfold TFIB_ERRNO; lia | unfold TFIB_ERRNO; lia | vm_compute; reflexivity | lia]. }
      split; [rewrite <- HEr; exact Era|].
      split; [unfold apart_frame; left; rewrite Rsp, HKAK; unfold TFIB_ERRNO, LLVMF_STK in *; lia|].
      unfold apart_gnl, LA_G_NL, NK_SIZE, TFIB_ERRNO; right; lia. }
    split; [exact NMA|]. split; [exact TA|].
    split.
    { intros i0 n2 ix p Hn Hp.
      pose proof (lf_tab_names_short) as Hshort. rewrite forallb_forall in Hshort.
      specialize (Hshort (n2, ix) (nth_error_In _ _ Hn)). apply Nat.leb_le in Hshort. cbn [fst] in Hshort.
      destruct (Z_lt_le_dec p 0) as [Hneg | Hp0]; [|destruct (Z_lt_le_dec p (2 ^ 64)) as [Hp64 | Hbig]].
      - split; [unfold apart_frame; left; rewrite Rsp; lia|].
        split; [unfold apart_gnl; left; unfold LA_G_NL; lia|].
        split; [unfold apart; right; rewrite HEr; unfold TFIB_ERRNO; lia|].
        intros Hr. lia.
      - destruct (lf_tab_core SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
          cx fp ly3 S3 W3 (ms_mem msA) mdA k2 md mk kbs mbs gbs HB HJA HRO HdatA i0 n2 ix p Hn Hp ltac:(lia))
          as (TC1 & TC2 & TC3 & TC4 & TC5 & TCT & TC6 & TC7).
        split; [unfold apart_frame; left; rewrite Rsp, HKAK; unfold YImgTop.IMG_TOP, LLVMF_STK in *; lia|].
        split; [destruct (w_tab_place cx md mk kbs mbs gbs W3 (ms_mem msA) i0 n2 ix p HRO HdatA Hn Hp ltac:(lia))
                  as [Hl | Hl]; unfold apart_gnl, LA_G_NAMES, LA_G_NL, NK_SIZE in *; [right | left]; lia|].
        split; [apply w_apart_of; [lia | lia|]; intros x Hx Hx'; exact (proj2 (proj2 (TC7 x ltac:(lia))) Hx)|].
        intros _. split; [exact TC1|]. split; [exact TC2|]. split; [split; [exact TC3|]; split; [exact TC4 | exact TC5]|].
        exact TCT.
      - split; [unfold apart_frame; right; rewrite Rsp; unfold LLVMF_STK in *; lia|].
        split; [unfold apart_gnl; right; unfold LA_G_NL, NK_SIZE; lia|].
        split; [unfold apart; left; rewrite HEr; unfold TFIB_ERRNO; lia|].
        intros Hr. lia. }
    split.
    { intros x Hx. destruct (NM x Hx) as (_ & Hl & NC1 & NC3 & NC4 & NC5 & NCT & NC6 & _).
      split; [unfold apart_frame; left; rewrite Rsp, HKAK; unfold YImgTop.IMG_TOP, LLVMF_STK in *; lia|].
      split; [rewrite Hx in Hnm; exact (w_name_gnl s x Hnm Hl)|].
      split; [lia|]. split; [split; [exact NC3|]; split; [exact NC4 | exact NC5]|]. exact NCT. }
    split.
    { intros u Hu. injection Hu as Hu. subst u.
      split; [exact Tfr|].
      split; [exact (w_ans_gnl ly3 S3 W3 (ms_mem msA) mdA s6v t IMG HARA HRO HDA)|].
      split; [lia|]. split; [apply (w_amem_sub _ _ _ Tam); lia|]. split; [exact Tra | exact Thv]. }
    intros u Hu. injection Hu as Hu. subst u.
    apply (w_slack_of_tail _ s6v (Z.of_nat (length t))); [lia | lia | unfold amem_range, kLowMemEnd, kHighMemEnd in Tam; lia |].
    exact Ttail.
  - (* the return, +0x1098 *)
    intros W2 ly2 S2 regs2 mem2 md2 Hle HJ2 Hpr Hfr2 Hfd2 Hfs2 Hkp Hsk Hs2 Hperm Hpost.
    rewrite Z.add_0_r in HJ2.
    set (ms2 := @mkst fy regs2 (getr (ms_regs msA) 1) mem2 (seg_rom SEGS)).
    change mem2 with (ms_mem ms2) in HJ2, Hkp, Hsk, Hpost.
    set (Er := fun a => inFP (reac_link_alias_write_awr (ms_regs msA) (rdW W3 (ms_mem msA))) a) in *.
    assert (LC : lf_call B cx REAC_LINK_ALIAS_WRITE_AK ly3 S3 ly2 S2 W3 (ms_mem msA) W2 (ms_mem ms2) Er).
    { split; [lia|]. split; [rewrite HKAK; unfold LLVMF_STK in *; clia|]. split; [exact Hkp | exact Hsk]. }
    assert (EE : forall a, Er a -> LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4).
    { intros a (r & Hin & Hr). unfold reac_link_alias_write_awr in Hin.
      destruct Hin as [<- | []]; cbn [fst snd] in Hr. exact Hr. }
    assert (Psub : forall c, In c (ablocks B ly3 S3) -> In c (ablocks B ly2 S2))
      by (intros c Hc; exact (Permutation_in _ (Permutation_sym Hperm) Hc)).
    (* reac_link_alias_write's post *)
    specialize (Hpost kbs lf_tab nm (Some t)). rewrite Ra0, Ra1 in Hpost.
    destruct (Hpost Dk Dtab NMA TA) as (Hrc & (kbs' & Hk' & Hwf' & _ & _ & _ & Htab' & _ & _ & _ & Hsent' & _ & Hop'
      & Hmis' & Hoc' & Hob' & Href')).
    clear Hpost.
    destruct (lf_alias_post cx fp k2 _ _ _ _ md mk kbs mbs gbs T3 _ P N REAC_LINK_ALIAS_WRITE_AK Er ly3 S3 W3 msA mdA
      ly2 S2 W2 ms2 md2 kbs' HB HCA HJ2 Hfr2 LC EE Hs2 Hperm Hfd2 Hfs2 HcurA Hk' Hwf' Htab' Hop'
      ltac:(rewrite Hmis'; exact Dmis) ltac:(rewrite Doc in Hoc'; lia)) as (HC2 & Hcur2 & HRO2).
    pose proof (ar_pres _ _ Hpr) as (P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27).
    pose proof (lf_call_kagree B cx REAC_LINK_ALIAS_WRITE_AK ly3 S3 ly2 S2 W3 (ms_mem msA) W2 (ms_mem ms2) Er LC) as KG.
    assert (XB : forall k a, In (own1, k) (ablocks B ly3 S3) -> own1 <= a < own1 + k ->
      ~ lf_X B ly3 S3 ly2 S2 (lf_sp1 cx - REAC_LINK_ALIAS_WRITE_AK) (lf_sp1 cx) Er a).
    { intros k a Hb Ha. apply (lfx_blk B ly3 S3 ly2 S2 _ _ Er own1 k a Hb Ha). intros HEa.
      destruct (kp_blk_place B LAWS ly3 S3 W3 (ms_mem msA) mdA own1 k a HARA Hb
        ltac:(unfold req_size; destruct (Z.eqb_spec k 0); lia)) as (Hni & _).
      apply Hni. apply (kp_img_ok_in B MS la_nul a IMG). left. pose proof (EE a HEa). unfold NK_N_SENT, NK_SIZE in *. lia. }
    pose proof (tx_ans_keep B own1 nb ly3 S3 ly2 S2 _ _ _ s6v t HTXA Psub KG XB) as HTX2.
    assert (HSL2 : rdword (aview SEGS (w_H W2) (ms_mem ms2)) (lf_sp1 cx + LS_T130) = Some own1).
    { apply (d4_slot_callee B cx REAC_LINK_ALIAS_WRITE_AK ly3 S3 ly2 S2 W3 (ms_mem msA) W2 (ms_mem ms2) Er _ own1 LC);
        [unfold LS_T130; lia | unfold LS_T130, LLVMF_STK in *; lia | | exact HSLA].
      intros j Hj HEa. pose proof (EE _ HEa). unfold LS_T130, LLVMF_STK, LA_G_NL, NK_N_SENT in *. lia. }
    apply (HL cx fy fp k2 ly2 S2 W2 ms2 md2 HB Hfx HJ2 ltac:(rewrite Hfr2; exact Hfr)).
    exists md, mk, P, N, s, s6v, own1, (nk_opened kbs), nm, t, (nk_kstate kbs), kbs', mbs, gbs, T3, nb.
    split; [exact Hi|].
    split.
    { unfold lf_shape, ms2. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
      rewrite Q1, <- HBASE. unfold LW_aret, AF_LLVMFuzzerTestOneInput. repeat split; reflexivity. }
    kreg KR 8 (8%bv : bv 5) K8. kreg KR 9 (9%bv : bv 5) K9. kreg KR 19 (19%bv : bv 5) K19. kreg KR 20 (20%bv : bv 5) K20.
    kreg KR 21 (21%bv : bv 5) K21. kreg KR 22 (22%bv : bv 5) K22. kreg KR 23 (23%bv : bv 5) K23.
    kreg KR 24 (24%bv : bv 5) K24. kreg KR 25 (25%bv : bv 5) K25. kreg KR 26 (26%bv : bv 5) K26.
    kreg KR 27 (27%bv : bv 5) K27.
    split; [unfold lf_core; cbn [ms_regs ms2 mkst]; rewrite P2, P8, P9, P3, P4, K2, K8, K9, K3, K4; repeat split; assumption|].
    split; [unfold w_regs; cbn [ms_regs ms2 mkst]; rewrite P19, P21, P22, P23, P24, P25, P26, P27, K19, K21, K22, K23, K24,
            K25, K26, K27; repeat split; assumption|].
    split; [exact Hnm|].
    cbn [ms_regs ms2 mkst].
    split; [rewrite P20, K20; exact R20|].
    split; [unfold nk_opened, fld_u32 in *; lia|].
    split; [rewrite P18; exact Q18|].
    split; [rewrite SENT0 in Hrc; exact Hrc|].
    split; [exact HC2|]. split; [exact Hcur2|].
    split; [exact Hob'|].
    split.
    { intros [Hr | [Hr | [Hr | Hr]]]; apply Href'.
      - left. exact Hr.
      - right; right; left. exact Hr.
      - right; right; right; left. intros u Hu. injection Hu as <-. exact Hr.
      - right; right; right; right. exact Hr. }
    split; [exact (tx_ans_dec B own1 nb ly2 S2 _ s6v t HTX2)|].
    split; [exact HTX2|]. split; [exact HSL2|]. split; [exact Hnb|]. split; [exact Hown|].
    split; [exact (w_fresh_sub B cx md mk T3 ly3 S3 ly2 S2 nb Psub Hfresh)|].
    split; [|exact Hrng].
    rewrite Hsent', Hrqm, SENT0.
    destruct (write_agree lf_tab nm (Some t) [] (nk_kstate kbs)) as (_ & Hrq & _). exact Hrq.
Qed.

End a.

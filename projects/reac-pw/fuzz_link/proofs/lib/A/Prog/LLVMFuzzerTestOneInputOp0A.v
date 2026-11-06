(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module paths and module names changed; 684 of its 739 lines of code are new or changed and 1277 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A, the op_read arm: reac_link_alias_read (0x836a8), +0xebc .. +0xed4,
   from the cut r_m_inv at model_read's return to the cut r_a_inv at alias_read's return (+0xed8).
   `mv s4, a0; mv a0, s6; mv a1, s7; mv a2, s5; mv a3, s10; mv a4, s11; jal reac_link_alias_read`: the name, the two
   text_buf buffers (NULL for a zero cap) and their caps. The call is made under reac_link_alias_read_c.v's contract
   (the Section hypothesis ALIAS_READ) as op_write makes its reac_link_alias_write call (Op1D.v w_ma),
   and the cut after it is restated by r_alias_post: Op1D.v's lf_alias_post with the frame's shadow a
   parameter and the library's write set g_nl's bytes plus the arm's own buffer blocks.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require reac_served_mark_aux.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import index_of_c reac_link_alias_read_c nl_talk_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs
  LLVMFuzzerTestOneInputKeep LLVMFuzzerTestOneInputKpre LLVMFuzzerTestOneInputLp LLVMFuzzerTestOneInputMb
  LLVMFuzzerTestOneInputDec LLVMFuzzerTestOneInputArmR LLVMFuzzerTestOneInputArmK LLVMFuzzerTestOneInputMdl
  LLVMFuzzerTestOneInputSel LLVMFuzzerTestOneInputNm LLVMFuzzerTestOneInputArmH LLVMFuzzerTestOneInputKpost
  LLVMFuzzerTestOneInputOp3Lib LLVMFuzzerTestOneInputOp3K LLVMFuzzerTestOneInputOp3B LLVMFuzzerTestOneInputOp1C
  LLVMFuzzerTestOneInputOp1D LLVMFuzzerTestOneInputChk LLVMFuzzerTestOneInputOp0Cut LLVMFuzzerTestOneInputOp0T
  LLVMFuzzerTestOneInputOp0Z.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Lemma r_sent_nil : forall kbs, nk_n_sent kbs = 0 -> nk_sent kbs = [].
Proof. intros kbs H. unfold nk_sent. rewrite H. reflexivity. Qed.

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
(* reac_link_alias_read, as proved (reac_link_alias_read.v) *)
Hypothesis ALIAS_READ : forall fy : YK11.FPState,
  @reac_link_alias_read_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.

#[local] Abbreviation BASEF cx :=
  (@lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Abbreviation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).
Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

(* the cut across a callee whose writes are g_nl's bytes [0, NK_N_SENT + 4) and bytes of the arm's own fresh blocks
   nbs, at any frame shadow, at the new g_nl bytes the callee's post gives (Op1D.v lf_alias_post, generalised) *)
Lemma r_alias_post : forall cx fp k2 ev mo wl lv md mk kbs mbs gbs T3 own P N K E sh
    ly3 S3 (W3 : world SEGS) ms3 md3 ly2 S2 (W2 : world SEGS) ms2 md2 kbs' (nbs : list (Z * Z)),
  BASEF cx -> (length sh = 112)%nat ->
  chk_cut SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 own ev mo wl lv k2 sh ly3 S3 W3 ms3 md3 ->
  JRN cx fp ly2 S2 W2 (ms_mem ms2) md2 k2 -> frames S2 = frames S3 ->
  lf_call B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E ->
  (forall a, E a -> LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4 \/ exists b, In b nbs /\ fst b <= a < fst b + snd b) ->
  (forall b, In b nbs -> In b (ablocks B ly3 S3) /\
     (forall c, c = (md, MD_SIZE) \/ c = (mk, MK_SIZE) \/ In c T3 \/ (0 < c_n cx /\ c = (c_p cx, c_n cx)) ->
        zdisjoint (fst c, req_size (snd c)) (fst b, req_size (snd b)))) ->
  S2 = set_fs (st_fs S2) S3 -> Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) ->
  m_fds md2 = m_fds md3 -> m_fs md2 = m_fs md3 ->
  lf_cur cx W3 ms3 P N ->
  anlk_at SEGS (rdW W2 (ms_mem ms2)) LA_G_NL kbs' -> nlk_wf kbs' ->
  aiftab_at SEGS (rdW W2 (ms_mem ms2)) LA_G_NL kbs' lf_tab ->
  nk_open kbs' = 0 -> nk_misuse kbs' = 0 -> nk_opened kbs' = nk_closed kbs' ->
  chk_cut SK B MT MS la_nul cx fp md mk kbs' mbs gbs T3 own ev mo wl lv k2 sh ly2 S2 W2 ms2 md2 /\
  lf_cur cx W2 ms2 P N /\
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) (ms_mem ms2)).
Proof.
  intros cx fp k2 ev mo wl lv md mk kbs mbs gbs T3 own P N K E sh ly3 S3 W3 ms3 md3 ly2 S2 W2 ms2 md2 kbs' nbs
    HB Hl HC HJ2 Hfr2 LC EE NB Hs2 Hperm Hfd Hfs Hcur Hk' Hwf' Htab' Hop' Hmis' Hoc'.
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
  assert (RQ : forall n, n <= req_size n) by (intros n; unfold req_size; destruct (Z.eqb_spec n 0); lia).
  (* a byte E writes: a g_nl byte (an image byte) or a byte of a fresh block (not an image byte) *)
  assert (EB : forall a, E a -> ~ (LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4) ->
      exists b, In b nbs /\ In b (ablocks B ly3 S3) /\ fst b <= a < fst b + req_size (snd b) /\
        ~ in_img SEGS a /\ a < alloc_ceiling).
  { intros a HEa Hng. destruct (EE a HEa) as [Hg | (b & Hb & Ha)]; [contradiction|].
    destruct (NB b Hb) as (Hb3 & _). destruct b as [b n]. cbn [fst snd] in *.
    pose proof (RQ n). destruct (kp_blk_place B LAWS ly3 S3 W3 (ms_mem ms3) md3 b n a HAR3 Hb3 ltac:(lia))
      as (Hni & Hc). exists (b, n). cbn [fst snd]. repeat split; try assumption; lia. }
  assert (EI : forall a, E a -> (LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4) -> in_img SEGS a).
  { intros a _ Ha. apply (kp_img_ok_in B MS la_nul a IMG). left. unfold NK_N_SENT, NK_SIZE in *. clia. }
  assert (ELOW : forall a, E a -> a < alloc_ceiling).
  { intros a Ha. destruct (Z_le_gt_dec LA_G_NL a) as [H1 | H1];
      [destruct (Z_lt_le_dec a (LA_G_NL + NK_N_SENT + 4)) as [H2 | H2]|].
    - pose proof (pa_segs_low a (EI a Ha (conj H1 H2))). clia.
    - destruct (EB a Ha ltac:(lia)) as (b & _ & _ & _ & _ & Hc). exact Hc.
    - destruct (EB a Ha ltac:(lia)) as (b & _ & _ & _ & _ & Hc). exact Hc. }
  (* an image byte E writes is a g_nl byte *)
  assert (NEI : forall a, in_img SEGS a -> ~ (LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4) -> ~ E a).
  { intros a Hi Hng HEa. destruct (EB a HEa Hng) as (b & _ & _ & _ & Hni & _). exact (Hni Hi). }
  assert (Hsv2 : lf_saved cx W2 ms2).
  { apply (lf_saved_callee B cx K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E LC); [|exact Hsv].
    intros a Ha HEa. pose proof (ELOW a HEa). unfold lf_saved_fp in Ha. unfold LLVMF_STK in *. clia. }
  assert (Hsl2 : lf_slots cx md mk fp W2 ms2).
  { apply (lf_slots_callee B cx K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E md mk fp LC); [|exact Hsl].
    intros a Ha HEa. pose proof (ELOW a HEa). unfold lf_slots_fp in Ha. unfold LLVMF_STK in *. clia. }
  assert (Hcur2 : lf_cur cx W2 ms2 P N).
  { apply (lf_cur_callee B cx K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E P N LC); [|exact Hcur].
    intros a Ha HEa. pose proof (ELOW a HEa). unfold lf_cur_fp in Ha. unfold LS_P, LS_N, LLVMF_STK in *. clia. }
  destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
    cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ3 Hfr) as (_ & _ & _ & _ & _ & _ & _ & Fsep).
  assert (FNE : forall a, (lf_F cx fp <= a < lf_F cx fp + 1024 \/ lf_SH cx fp <= a < lf_SH cx fp + 128) -> ~ E a).
  { intros a Ha HEa. destruct (kp_frame_place B LAWS cx fp ly3 S3 W3 (ms_mem ms3) md3 a HAR3 Hin Hfa Ha) as (Hni & _).
    destruct (Z_le_gt_dec LA_G_NL a) as [H1 | H1];
      [destruct (Z_lt_le_dec a (LA_G_NL + NK_N_SENT + 4)) as [H2 | H2]|];
      [exact (Hni (EI a HEa (conj H1 H2)))| |];
      (destruct (EB a HEa ltac:(lia)) as ((b & n) & _ & Hb3 & Hab & _ & _); cbn [fst snd] in Hab;
       destruct Ha as [Ha | Ha];
       [pose proof (Fsep b n Hb3) as D; unfold zdisjoint in D; cbn [fst snd] in D; lia
       | destruct (r_blk_not_sh SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
           cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 b n a HB HJ3 Hfr Hb3 Hab) as (_ & NS); exact (NS Ha)]). }
  assert (Hhd2 : lf_header cx fp W2 ms2).
  { apply (lf_header_callee B cx fp K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E LC Hin Hfa); [|exact Hhd].
    intros a Ha. apply FNE. left. unfold lf_header_fp in Ha. change (fs_frame_bytes LF_CID) with 1024 in Ha. clia. }
  assert (Hfsh2 : lf_fshadow cx fp W2 ms2 sh).
  { apply (lf_fshadow_callee_sh B cx fp K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E sh LC Hin Hfa Hl); [|exact Hfsh].
    intros a Ha. apply FNE. right. unfold lf_fshadow_fp in Ha. clia. }
  assert (Pmd : In (md, MD_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Bmd).
  assert (Pmk : In (mk, MK_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Bmk).
  assert (Hblk2 : lf_blocks B cx md mk T3 ly2 S2 (rdW W2 (ms_mem ms2))).
  { apply (ar_blocks_leaf B cx md mk T3 ly3 S3 ly2 S2 _ Hperm).
    exact (lf_blocks_callee B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E md mk T3 LC Pmd Pmk Hblk). }
  assert (HPB : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by (intros Hn; exact (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
          cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ3 Hn)).
  (* a byte of a block the cut names is not a byte E writes in a fresh block *)
  assert (NBX : forall c a, c = (md, MD_SIZE) \/ c = (mk, MK_SIZE) \/ In c T3 \/ (0 < c_n cx /\ c = (c_p cx, c_n cx)) ->
      fst c <= a < fst c + req_size (snd c) -> E a -> LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4).
  { intros c a Hc Ha HEa. destruct (Z_le_gt_dec LA_G_NL a) as [H1 | H1];
      [destruct (Z_lt_le_dec a (LA_G_NL + NK_N_SENT + 4)) as [H2 | H2]|]; [lia| |];
      (exfalso; destruct (EE a HEa) as [Hg | (b & Hb & Hab)]; [lia|];
       destruct (NB b Hb) as (_ & Hd); pose proof (Hd c Hc) as D; pose proof (RQ (snd b)); unfold zdisjoint in D;
       destruct b as [b1 b2], c as [c1 c2]; cbn [fst snd] in *; lia). }
  assert (NRO : forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> ~ E a).
  { intros a Ha HEa.
    assert (Hi : in_img SEGS a).
    { destruct Ha as [(s0 & Hs0 & _ & Hsr) | Hr2]; [exists s0; split; [exact Hs0 | exact Hsr]|].
      exact (ar_relro_img HSEGS a Hr2). }
    destruct (Z_le_gt_dec LA_G_NL a) as [H1 | H1];
      [destruct (Z_lt_le_dec a (LA_G_NL + NK_N_SENT + 4)) as [H2 | H2]|].
    - apply (ar_not_ro_G HSEGS a); [|exact Ha]. unfold inG, G_HARNESS. apply Exists_cons_hd.
      unfold in_zr. cbn [fst snd]. unfold NK_N_SENT in *. clia.
    - exact (NEI a Hi ltac:(lia) HEa).
    - exact (NEI a Hi ltac:(lia) HEa). }
  assert (HNUL : val_mem SEGS (rdW W2 (ms_mem ms2)) la_nul 1 0).
  { apply (lf_la_nul_callee B MS la_nul cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E IMG LC); [|exact Hla0].
    apply NEI; [apply (kp_img_ok_in B MS la_nul la_nul IMG); right; right; right; right; right; left; lia|].
    rewrite HLN in *. unfold LA_NUL, LA_LONG_ALIAS, LA_G_NL, NK_N_SENT in *. clia. }
  assert (Hjbk2 : lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly2 S2 W2 ms2 md2 T3 own).
  { apply (ar_jbk_leaf SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp k2 ev mo wl lv
      ly3 S3 ly2 S2 W2 ms2 md2 T3 own k2 HB HJ2 Hs2 Hperm).
    apply (lf_jbk_callee B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own K ly2 S2 W2 ms2 md2 E
      IMG RIMG LC); [| exact NRO | exact HPB | exact Hfd | exact Hfs | exact HNUL | exact Hjbk].
    intros a Ha HEa. destruct Ha as [Ha | Ha].
    - destruct Ha as [Ha | [Ha | (f & n & Hfn & Ha)]].
      + apply (NEI a); [apply (kp_img_ok_in B MS la_nul a IMG); right; right; right; left; exact Ha| |exact HEa].
        rewrite HMS in Ha. cbv [amf_head_addr link_amf amf_sink_addr amf_say_addr amf_ofl_head amf_ofl_lock] in Ha.
        unfold LA_G_NL, NK_N_SENT in *; clia.
      + apply (NEI a); [apply (kp_img_ok_in B MS la_nul a IMG); right; right; right; right; left; exact Ha| |exact HEa].
        rewrite HMS in Ha. cbv [amf_env_addr link_amf amf_threaded amf_need_locks amf_ofl_lock] in Ha.
        unfold LA_G_NL, NK_N_SENT in *; clia.
      + assert (HfnT : In (f, n) (ablocks B ly3 S3)) by exact (Hinc _ Hfn).
        assert (Hn : n = AMF_BLOCK).
        { destruct Hgi as [(_ & HT) | (f' & _ & HT & _)]; rewrite HT in Hfn; [destruct Hfn|].
          destruct Hfn as [Hq | []]. injection Hq as _ <-. reflexivity. }
        subst n.
        destruct (kp_blk_place B LAWS ly3 S3 W3 (ms_mem ms3) md3 f AMF_BLOCK a HAR3 HfnT
          ltac:(unfold req_size, AMF_BLOCK in *; cbn; clia)) as (Hni & _).
        pose proof (NBX (f, AMF_BLOCK) a (or_intror (or_intror (or_introl Hfn)))
          ltac:(cbn [fst snd]; unfold req_size, AMF_BLOCK in *; cbn; clia) HEa) as Hg.
        exact (Hni (EI a HEa Hg)).
    - assert (Hn : 0 < c_n cx) by clia.
      destruct (kp_blk_place B LAWS ly3 S3 W3 (ms_mem ms3) md3 (c_p cx) (c_n cx) a HAR3 (HPB Hn)
        ltac:(unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); clia)) as (Hni & _).
      pose proof (NBX (c_p cx, c_n cx) a (or_intror (or_intror (or_intror (conj Hn eq_refl))))
        ltac:(cbn [fst snd]; pose proof (RQ (c_n cx)); lia) HEa) as Hg.
      exact (Hni (EI a HEa Hg)). }
  assert (HRO2 : arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) (ms_mem ms2)))
    by exact (lf_aro_callee B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E RIMG LC NRO HRO).
  destruct (lf_odd_texts_of_ro B TB HSEGS W2 (ms_mem ms2) HRO2) as (Hodd2 & Htx2).
  pose proof (lf_call_kagree B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E LC) as KG.
  destruct Hdat as (Dk & Dwf & Dtab & Dop & Dmis & Doc & Dmd & Dmwf & Dmk & Dkwf & Dare & Difp & Dgn & Dgw & Dodd
    & Dtx & Dla).
  assert (WB : forall b n, In (b, n) (ablocks B ly2 S2) -> wcarry SEGS (rdW W3 (ms_mem ms3)) (rdW W2 (ms_mem ms2)) b n).
  { intros b n Hbn ii Hii _. destruct (al_blocks _ _ LAWS ly2 S2 W2 (ms_mem ms2) md2 b n HAR2 Hbn) as (_ & _ & _ & _ & Hp & _).
    apply (apresent_writable SEGS). apply (proj1 (Hp (b + ii) ltac:(unfold req_size; destruct (Z.eqb_spec n 0); clia))). }
  assert (BX : forall c a, (c = (md, MD_SIZE) \/ c = (mk, MK_SIZE)) -> In c (ablocks B ly3 S3) ->
      fst c <= a < fst c + snd c -> ~ lf_X B ly3 S3 ly2 S2 (lf_sp1 cx - K) (lf_sp1 cx) E a).
  { intros (b & n) a Hc Hbn Ha. cbn [fst snd] in Ha. apply (lfx_blk B ly3 S3 ly2 S2 _ _ E b n a Hbn Ha). intros HEa.
    destruct (kp_blk_place B LAWS ly3 S3 W3 (ms_mem ms3) md3 b n a HAR3 Hbn
      ltac:(pose proof (RQ n); lia)) as (Hni & _).
    pose proof (NBX (b, n) a ltac:(destruct Hc as [Hc | Hc]; [left; exact Hc | right; left; exact Hc])
      ltac:(cbn [fst snd]; pose proof (RQ n); lia) HEa) as Hg.
    exact (Hni (EI a HEa Hg)). }
  assert (IMX : forall a, lf_img_fp MS la_nul a -> ~ (LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4) ->
    ~ lf_X B ly3 S3 ly2 S2 (lf_sp1 cx - K) (lf_sp1 cx) E a)
    by (intros a Ha Hng; exact (lfx_imgfp B MS la_nul ly3 S3 ly2 S2 _ _ E a IMG Ha
          (NEI a (kp_img_ok_in B MS la_nul a IMG Ha) Hng))).
  assert (Hdat2 : lf_data cx md mk kbs' mbs gbs (rdW W2 (ms_mem ms2))).
  { refine (conj Hk' (conj Hwf' (conj Htab' (conj Hop' (conj Hmis' (conj Hoc' (conj _ (conj Dmwf (conj _
      (conj Dkwf (conj Dare (conj _ (conj _ (conj _ (conj Hodd2 (conj Htx2 _)))))))))))))))).
    - apply (amodel_keep SEGS _ _ _ md mbs KG (WB md MD_SIZE Pmd)); [|exact Dmd].
      intros ii Hii. apply (BX (md, MD_SIZE)); [left; reflexivity | exact Bmd | cbn [fst snd]; clia].
    - apply (amarks_keep SEGS _ _ _ mk gbs KG (WB mk MK_SIZE Pmk)); [|exact Dmk].
      intros ii Hii. apply (BX (mk, MK_SIZE)); [right; reflexivity | exact Bmk | cbn [fst snd]; clia].
    - intros e He. destruct (Difp e He) as (qq & Hq1 & Hq2 & Hq3). exists qq.
      split; [|split; [exact Hq2|]].
      + apply (au64_keep SEGS _ _ _ _ _ KG); [|exact Hq1]. intros kk Hkk. apply IMX.
        * left. unfold NK_IF_NAME, NK_SIZE in *. clia.
        * unfold NK_IF_NAME, NK_N_SENT in *. clia.
      + intros H60. apply (au64_keep SEGS _ _ _ _ _ KG); [|exact (Hq3 H60)]. intros kk Hkk. apply IMX.
        * right; right; right; right; right; right. clia.
        * unfold LA_ODD, LA_G_NL in *. clia.
    - apply (lf_gnames_at_keep _ _ _ 64 KG ltac:(clia)); [|exact Dgn]. intros a Ha. apply IMX.
      + right; left. exact Ha.
      + unfold LA_G_NAMES, G_NAMES_SIZE, LA_G_NL, NK_N_SENT in *. clia.
    - apply (lf_gnames_w_keep _ _ _ KG); [| |exact Dgw].
      + assert (Hw : forall (m' : word -> option byte) a, LA_G_NAMES <= a < LA_G_NAMES + 512 -> writable_at SEGS m' a)
          by (rewrite HSEGS; exact LA_G_NAMES_writable).
        intros ii Hii _. apply Hw. unfold G_NAMES_SIZE in Hii. clia.
      + intros a Ha. apply IMX.
        * right; left. exact Ha.
        * unfold LA_G_NAMES, G_NAMES_SIZE, LA_G_NL, NK_N_SENT in *. clia.
    - destruct Dla as ((la & Hla & Hlal) & Hnul0 & _).
      split; [exists la; split; [|exact Hlal] | split].
      + apply (au8arr_keep SEGS _ _ _ LA_LONG_ALIAS la KG); [| |exact Hla].
        * intros ii Hii _. generalize (rdW W2 (ms_mem ms2)). rewrite HSEGS. intros m2.
          apply (writable_at_of_wseg tfibsegs m2 LA_LONG_ALIAS 304);
            [unfold LA_LONG_ALIAS; lia | unfold LA_LONG_ALIAS; lia | exact wseg_LA_LONG_ALIAS304 | lia].
        * intros ii Hii. apply IMX; [right; right; left; clia | unfold LA_LONG_ALIAS, LA_G_NL, NK_N_SENT in *; clia].
      + apply (val_mem_keep SEGS _ _ _ (LA_LONG_ALIAS + 300) 1 0 KG); [|exact Hnul0].
        intros kk Hkk. apply IMX; [right; right; left; clia | unfold LA_LONG_ALIAS, LA_G_NL, NK_N_SENT in *; clia].
      + exact (lf_la_slack_any HSEGS _). }
  split; [|split; [exact Hcur2 | exact HRO2]].
  split; [exact HJ2|]. split; [rewrite Hfr2; exact Hfr|]. split; [exact Hsv2|]. split; [exact Hhd2|].
  split; [exact Hfsh2|]. split; [exact Hsl2|]. split; [exact Hjbk2|]. split; [exact Hblk2 | exact Hdat2].
Qed.

(* the kernel state of g_nl from its five fields *)
Lemma r_nk_kstate_of : forall kbs' K',
  nk_chunks kbs' = k_chunks K' -> nk_next kbs' = Z.of_nat (k_next K') -> nk_end_errno kbs' = k_end K' ->
  nk_socket_errno kbs' = k_sock K' -> nk_send_errno kbs' = k_send K' -> nk_kstate kbs' = K'.
Proof.
  intros kbs' [c n e so se] H1 H2 H3 H4 H5. cbn [k_chunks k_next k_end k_sock k_send] in *. unfold nk_kstate.
  rewrite H1, H2, H3, H4, H5, Nat2Z.id. reflexivity.
Qed.

(* the read's two strings fit their buffers *)
Lemma r_kind_len : forall tab nm kc ac reqs K, 1 <= kc ->
  Z.of_nat (length (r_kind (read_core tab nm kc ac reqs K))) <= kc - 1.
Proof.
  intros tab nm kc ac reqs K Hk. unfold read_core. destruct nm as [s|]; [|cbn; lia].
  destruct (Nat.eqb (length s) 0); [cbn; lia|]. destruct (index_of tab s =? 0); [cbn; lia|]. cbn [r_kind].
  replace (kc <? 1) with false by (symmetry; apply Z.ltb_ge; lia). apply reac_served_mark_aux.text_of_attr_len. exact Hk.
Qed.
Lemma r_alias_len : forall tab nm kc ac reqs K, 1 <= ac ->
  Z.of_nat (length (r_alias (read_core tab nm kc ac reqs K))) <= ac - 1.
Proof.
  intros tab nm kc ac reqs K Hk. unfold read_core. destruct nm as [s|]; [|cbn; lia].
  destruct (Nat.eqb (length s) 0); [cbn; lia|]. destruct (index_of tab s =? 0); [cbn; lia|]. cbn [r_alias].
  replace (ac <? 1) with false by (symmetry; apply Z.ltb_ge; lia). apply reac_served_mark_aux.text_of_attr_len. exact Hk.
Qed.
(* the same at any cap below 40 *)
Lemma r_kind_fit : forall tab nm kc ac reqs K, 0 <= kc < 40 ->
  Z.of_nat (length (r_kind (read_core tab nm kc ac reqs K))) <= 39 /\
  (1 <= kc -> Z.of_nat (length (r_kind (read_core tab nm kc ac reqs K))) <= kc - 1).
Proof.
  intros tab nm kc ac reqs K Hk. destruct (Z_lt_le_dec kc 1) as [K0 | K1].
  - rewrite r_kind_nil by lia. cbn. lia.
  - pose proof (r_kind_len tab nm kc ac reqs K K1). lia.
Qed.
Lemma r_alias_fit : forall tab nm kc ac reqs K, 0 <= ac < 40 ->
  Z.of_nat (length (r_alias (read_core tab nm kc ac reqs K))) <= 39 /\
  (1 <= ac -> Z.of_nat (length (r_alias (read_core tab nm kc ac reqs K))) <= ac - 1).
Proof.
  intros tab nm kc ac reqs K Hk. destruct (Z_lt_le_dec ac 1) as [K0 | K1].
  - rewrite r_alias_nil by lia. cbn. lia.
  - pose proof (r_alias_len tab nm kc ac reqs K K1). lia.
Qed.

Lemma r_aread : forall POST i,
  FROM POST (r_a_inv SK B MT MS la_nul LF_MO_SET LF_MO_OP i) ->
  FROM POST (r_m_inv SK B MT MS la_nul LF_MO_SET LF_MO_OP i).
Proof.
  intros POST i HA cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HM.
  destruct HM as (md & mk & P & N & kbs & mbs & gbs & T3 & s & nm & kc & ac & t1 & t2 & nb1 & nb2 & Hsh & Hreg & R10 &
    Hnm & Hkc & Hac & Hi & Hcore & HC & Hcur & Hop & Hns & Hrq & Hks & Hbufs & Hb1 & Hb2 & HWK & HWA & NIF).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof (lv_text LV) as HBASE.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof alloc_ceiling_value as (CV & _).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof Hreg as (R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
  destruct (lf_img_facts B MS la_nul HSEGS TB HMS HLN) as (IMG & RIMG).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & Hs16 & Hlo & H47').
  rewrite (lf_shape_eta fy LR_m ms3 Hsh).
  pose proof (d4_entry fy W3 (ms_regs ms3) (ms_mem ms3) LR_m) as HS.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg (ms_regs ms3) []))
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LR_m)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) []))) by apply Eimg_env.
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) []) n)
    by (intros n Hn; rewrite HEdef; apply Eimg_low; exact Hn).
  clear HEdef.
  paj_run_tok RUN HS HJ SHOK (0, 0); [apply awr_ok_x_nil|].
  rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
  pose proof (d4_keep_run fy W3 _ _ msA (ms_regs ms3) _ [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27] HS EL
    ltac:(intros r Hr; cbn in Hr; repeat (destruct Hr as [<- | Hr]; [reflexivity|]); destruct Hr) ltac:(d4chk)) as KR.
  pose proof (kagree_frame_nil _ _ _ HFrA) as KA.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdA := mdx) in * end.
  assert (FdA : m_fds mdA = m_fds md3) by (subst mdA; rewrite !lf_wvb_fds; reflexivity).
  assert (FsA : m_fs mdA = m_fs md3) by (subst mdA; rewrite !lf_wvb_fs; reflexivity).
  pose proof (chk_cut_run SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 _ _ _ _ _ k2 SH_R ly3 S3 W3 ms3 msA md3 mdA
    SH_R_len HC HJ KA (fun x Hx => HGA x Hx) FdA FsA) as HCA.
  pose proof (lf_cur_keep (fun _ => False) cx W3 ms3 W3 msA P N KA (fun a _ H => H) Hcur) as HcurA.
  assert (G0 : mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msA))) by exact HGA.
  pose proof (fun H1 => r_atbuf_run W3 _ _ t1 kc _ KA G0 (Hb1 H1)) as Hb1A.
  pose proof (fun H1 => r_atbuf_run W3 _ _ t2 ac _ KA G0 (Hb2 H1)) as Hb2A.
  assert (NIFA : lf_slot cx W3 msA LS_NIF (nk_opened kbs))
    by exact (lf_slot_keep (fun _ => False) cx W3 ms3 W3 msA LS_NIF _ KA (fun j _ H => H) NIF).
  assert (HWKA : acstr_at SEGS (rdW W3 (ms_mem msA)) (lf_F cx fp + LO_B2E0) (r_kind (r_RR nm kc ac kbs)) /\
     (1 <= kc -> abuf SEGS (rdW W3 (ms_mem msA)) (lf_F cx fp + LO_B2E0) kc)).
  { destruct HWK as (W1 & W2'). split.
    - exact (acstr_keep SEGS _ _ _ _ _ KA (fun j _ H => H) W1).
    - intros H1. exact (abuf_keep SEGS _ _ _ _ _ KA (wcarry_of_grows SEGS _ _ _ _ G0) (fun j _ H => H) (W2' H1)). }
  assert (HWAA : acstr_at SEGS (rdW W3 (ms_mem msA)) (lf_F cx fp + LO_B330) (r_alias (r_RR nm kc ac kbs)) /\
     (1 <= ac -> abuf SEGS (rdW W3 (ms_mem msA)) (lf_F cx fp + LO_B330) ac)).
  { destruct HWA as (W1 & W2'). split.
    - exact (acstr_keep SEGS _ _ _ _ _ KA (fun j _ H => H) W1).
    - intros H1. exact (abuf_keep SEGS _ _ _ _ _ KA (wcarry_of_grows SEGS _ _ _ _ G0) (fun j _ H => H) (W2' H1)). }
  clear HC Hcur Hb1 Hb2 NIF HWK HWA.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14. prreg HS (20%bv : bv 5) Q20.
  ew_reg EL 22%nat (22%bv : bv 5) Q10. ew_reg EL 23%nat (23%bv : bv 5) Q11. ew_reg EL 21%nat (21%bv : bv 5) Q12.
  ew_reg EL 26%nat (26%bv : bv 5) Q13. ew_reg EL 27%nat (27%bv : bv 5) Q14. ew_reg EL 10%nat (10%bv : bv 5) Q20.
  rewrite R22 in Q10. rewrite R23 in Q11. rewrite R21 in Q12. rewrite R26 in Q13. rewrite R27 in Q14.
  rewrite R10 in Q20. rewrite HBASE in Q1.
  pose proof HCA as (HJA & HfrA & HsvA & HhdA & HfsA & HslA & HjbkA & HblkA & HdatA).
  pose proof HjbkA as (Hkev & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
  pose proof HJA as (_ & _ & (memSA & HJiA & _) & _). pose proof HJiA as (HARA & _).
  kreg KR 2 (2%bv : bv 5) K2. kreg KR 3 (3%bv : bv 5) K3. kreg KR 4 (4%bv : bv 5) K4.
  destruct (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB) as (Gp & Tp).
  assert (Rsp : spZ (ms_regs msA) = lf_sp1 cx).
  { unfold spZ. rewrite K2, R2. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
  assert (HKAK : REAC_LINK_ALIAS_READ_AK = 8592) by reflexivity.
  assert (HK8 : 0 <= REAC_LINK_ALIAS_READ_AK <= LLVMF_STK - 448) by (rewrite HKAK; unfold LLVMF_STK; lia).
  pose proof (w_name_range s nm Hnm) as Rs.
  pose proof Hbufs as (Hnb1 & Hnb2 & Hbin & Hbap).
  assert (RQ : forall c, 0 <= c -> req_size (c + 1) = c + 1)
    by (intros c Hc; unfold req_size; destruct (c + 1 =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | lia]).
  (* a text buffer t of cap c (t = 0 iff c = 0): its block, below the ceiling, off the image *)
  assert (TB1 : forall t c nb, tb_nb c t nb -> incl nb (nb1 ++ nb2) -> t <> 0 ->
      1 <= c /\ nb = [(t, c + 1)] /\ In (t, c + 1) (ablocks B ly3 S3) /\ ~ In (t, c + 1) (ablocks B (c_ly cx) (c_S cx)) /\
      (forall x, t <= x < t + c + 1 -> ~ in_img SEGS x /\ x < alloc_ceiling /\ apresent (w_H W3) (ms_mem msA) x) /\
      4096 <= t /\ t + c + 1 <= alloc_ceiling /\ in_app t (c + 1)).
  { intros t c nb Hnb Hinc Ht. destruct Hnb as [(_ & E0 & _) | (H1 & H4 & ->)]; [contradiction|].
    destruct (Hbin (t, c + 1) (Hinc _ (or_introl eq_refl))) as (Hin3 & Hnold & _).
    destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem msA) mdA t (c + 1) HARA Hin3) as (_ & Bb4 & Bceil & Bapp & Bp & _).
    rewrite RQ in Bceil, Bapp, Bp by lia.
    split; [lia|]. split; [reflexivity|]. split; [exact Hin3|]. split; [exact Hnold|].
    split; [|split; [lia | split; [lia | exact Bapp]]].
    intros x Hx. destruct (kp_blk_place B LAWS ly3 S3 W3 (ms_mem msA) mdA t (c + 1) x HARA Hin3
      ltac:(rewrite RQ by lia; lia)) as (Hni & Hc).
    split; [exact Hni|]. split; [exact Hc|]. exact (proj1 (Bp x ltac:(lia))). }
  assert (In1 : incl nb1 (nb1 ++ nb2)) by (intros x Hx; apply in_or_app; left; exact Hx).
  assert (In2 : incl nb2 (nb1 ++ nb2)) by (intros x Hx; apply in_or_app; right; exact Hx).
  assert (T1z : t1 = 0 <-> kc = 0) by (destruct Hnb1 as [(-> & -> & _) | (H1 & H4 & _)]; lia).
  assert (T2z : t2 = 0 <-> ac = 0) by (destruct Hnb2 as [(-> & -> & _) | (H1 & H4 & _)]; lia).
  assert (Rt1 : 0 <= t1 < 2 ^ 64).
  { destruct (Z.eq_dec t1 0) as [-> | Ht]; [lia|].
    destruct (TB1 t1 kc nb1 Hnb1 In1 Ht) as (_ & _ & _ & _ & _ & H4 & Hc & _). lia. }
  assert (Rt2 : 0 <= t2 < 2 ^ 64).
  { destruct (Z.eq_dec t2 0) as [-> | Ht]; [lia|].
    destruct (TB1 t2 ac nb2 Hnb2 In2 Ht) as (_ & _ & _ & _ & _ & H4 & Hc & _). lia. }
  assert (Ra0 : aarg (ms_regs msA) 0 = s) by (rewrite ar_aarg0, Q10; unfold w64; apply unsigned_lit_small; lia).
  assert (Ra1 : aarg (ms_regs msA) 1 = t1) by (rewrite ar_aarg1, Q11; unfold w64; apply unsigned_lit_small; lia).
  assert (Ra2 : aarg (ms_regs msA) 2 = kc) by (rewrite ar_aarg2, Q12; unfold w64; apply unsigned_lit_small; lia).
  assert (Ra3 : aarg (ms_regs msA) 3 = t2) by (rewrite ar_aarg3, Q13; unfold w64; apply unsigned_lit_small; lia).
  assert (Ra4 : aarg (ms_regs msA) 4 = ac) by (rewrite ar_aarg4, Q14; unfold w64; apply unsigned_lit_small; lia).
  pose proof (fun x (Hx : nm = Some x) => lf_name_core SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END
    TB HSEGS cx fp ly3 S3 W3 (ms_mem msA) mdA k2 md mk kbs mbs gbs s x HB HJA HRO HdatA
    ltac:(rewrite <- Hx; exact Hnm)) as NM.
  assert (NMA : astr_arg SEGS (rdW W3 (ms_mem msA)) s nm)
    by (apply (w_name_arg _ _ s nm Hnm); intros x Hx; exact (proj1 (NM x Hx))).
  pose proof HdatA as (Dk & Dwf & Dtab & Dop & Dmis & Doc & Dmd & Dmwf & _).
  assert (RRC : - 2 ^ 32 < r_rc (r_LR nm kc ac kbs) < 2 ^ 32).
  { pose proof Dwf as (_ & _ & _ & _ & _ & _ & _ & _ & He & Hso & Hse & _).
    unfold r_LR, read_lib. apply u_read_rc_range; unfold nk_kstate; cbn [k_sock k_send k_end]; lia. }
  pose proof (u_rdn4_range kbs NK_OPENED) as Ro.
  (* a buffer argument's facts *)
  assert (BUF : forall t c nb, tb_nb c t nb -> incl nb (nb1 ++ nb2) -> t <> 0 -> 1 <= c ->
      abuf SEGS (rdW W3 (ms_mem msA)) t c /\ achk SEGS (rdW W3 (ms_mem msA)) t c /\
      apart_frame (ms_regs msA) REAC_LINK_ALIAS_READ_AK t c /\ apart_gnl LA_G_NL t c /\
      apart (as_errno B) 4 t c /\ (forall x, t <= x < t + c -> ~ in_img SEGS x)).
  { intros t c nb Hnb Hinc Ht H1.
    destruct (TB1 t c nb Hnb Hinc Ht) as (_ & _ & Hin3 & _ & Hx & H4 & Hc & Happ).
    assert (NI : forall x, t <= x < t + c -> ~ in_img SEGS x) by (intros x Hx'; exact (proj1 (Hx x ltac:(lia)))).
    split; [apply u_abuf; [lia | lia | lia | intros x Hx'; exact (proj2 (proj2 (Hx x ltac:(lia))))]|].
    split.
    { split; [unfold amem_range, in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *; lia|].
      rewrite ard_aview. split.
      - eapply range_addressable_of_block; [eassumption | eassumption | exact Hin3 | lia | rewrite RQ by lia; lia].
      - eapply shadow_hull_vis_of_block; [eassumption | eassumption | exact Hin3 | lia | rewrite RQ by lia; lia | lia]. }
    split; [unfold apart_frame; left; rewrite Rsp, HKAK; unfold LLVMF_STK in *; lia|].
    split.
    { apply w_apart_gnl_of; [lia|]. intros x Hx' Hg. apply (NI x Hx').
      apply (kp_img_ok_in B MS la_nul x IMG). left. exact Hg. }
    split; [apply w_apart_of; [lia | lia|]; intros x Hx' Hx''; exact (NI x Hx'' (md_errno_img B TB HSEGS x Hx'))|].
    exact NI. }
  replace (pa_sigma LS_reac_link_alias_read) with REAC_LINK_ALIAS_READ_A by (rewrite (lv_sigma LV); reflexivity).
  change (mkCfg (mkst (ms_regs msA) (Z_to_bv 64 REAC_LINK_ALIAS_READ_A) (ms_mem msA) (seg_rom SEGS)) mdA)
    with (@cfg_at fy SEGS REAC_LINK_ALIAS_READ_A (ms_regs msA) (ms_mem msA) mdA).
  eapply (@ar_leaf_call fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END fy).
  - exact (ALIAS_READ fy).
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
  - intros a (r & Hin & Hr). unfold reac_link_alias_read_awr in Hin. rewrite Ra1, Ra2, Ra3, Ra4 in Hin.
    unfold aivl in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
    + apply (ar_ajw_G B cx fp ly3 S3 a). unfold inG, G_HARNESS. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
      unfold NK_N_SENT in *. clia.
    + destruct (Z.eqb_spec t1 0) as [E0 | E0]; [lia|].
      destruct (TB1 t1 kc nb1 Hnb1 In1 E0) as (_ & _ & Hin3 & Hnold & _).
      apply (ar_ajw_blk B cx fp ly3 S3 t1 (kc + 1) a Hin3 Hnold). lia.
    + destruct (Z.eqb_spec t2 0) as [E0 | E0]; [lia|].
      destruct (TB1 t2 ac nb2 Hnb2 In2 E0) as (_ & _ & Hin3 & Hnold & _).
      apply (ar_ajw_blk B cx fp ly3 S3 t2 (ac + 1) a Hin3 Hnold). lia.
  - intros a (r & Hin & Hr). unfold reac_link_alias_read_awr in Hin. rewrite Ra1, Ra2, Ra3, Ra4 in Hin.
    unfold aivl in Hin. intros Hro.
    assert (Him : in_img SEGS a).
    { destruct Hro as [(s0 & Hs0 & _ & Hsr) | Hr2]; [exists s0; split; [exact Hs0 | exact Hsr]|].
      exact (ar_relro_img HSEGS a Hr2). }
    destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
    + apply (ar_not_ro_G HSEGS a); [|exact Hro]. unfold inG, G_HARNESS. apply Exists_cons_hd. unfold in_zr.
      cbn [fst snd]. unfold NK_N_SENT in *. clia.
    + destruct (Z.eqb_spec t1 0) as [E0 | E0]; [lia|].
      destruct (TB1 t1 kc nb1 Hnb1 In1 E0) as (_ & _ & _ & _ & Hx & _). exact (proj1 (Hx a ltac:(lia)) Him).
    + destruct (Z.eqb_spec t2 0) as [E0 | E0]; [lia|].
      destruct (TB1 t2 ac nb2 Hnb2 In2 E0) as (_ & _ & _ & _ & Hx & _). exact (proj1 (Hx a ltac:(lia)) Him).
  - (* the read set *)
    intros a [(Hz1 & u & Hu & Ha) | (bs & tab & i0 & n2 & ix & p & Hbs & Htb & Hn & Hp & Hu & Ha)].
    + rewrite Ra0 in Hz1, Hu, Ha. destruct nm as [x|].
      * pose proof (kp_acstr_unique _ _ _ _ _ Hu (proj1 (NM x eq_refl))) as Eu. subst u.
        exact (lf_name_akb SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
          cx fp ly3 S3 W3 (ms_mem msA) mdA k2 md mk kbs mbs gbs s x ly3 S3 _ _ a HB HJA HRO HdatA Hnm Ha).
      * exfalso. apply Hz1. exact NMA.
    + pose proof Htb as (Hnif & _ & _).
      assert (Hi0 : 0 <= Z.of_nat i0 < nk_n_if bs).
      { rewrite Hnif. assert (Hl : (i0 < length tab)%nat) by (apply nth_error_Some; rewrite Hn; discriminate). lia. }
      exact (lf_tab_akb SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
        cx fp ly3 S3 W3 (ms_mem msA) mdA k2 md mk kbs mbs gbs _ _ HB HJA HRO HdatA bs (Z.of_nat i0) p n2 a Hbs Hi0 Hp Hu Ha).
  - (* the Pre *)
    exists kbs, lf_tab, nm.
    rewrite Ra0, Ra1, Ra2, Ra3, Ra4.
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
    split; [exact NMA|].
    split; [intros Ht H1; exact (proj1 (BUF t1 kc nb1 Hnb1 In1 Ht H1))|].
    split; [intros Ht H1; exact (proj1 (BUF t2 ac nb2 Hnb2 In2 Ht H1))|].
    split.
    { intros i0 n2 ix p Hn Hp.
      pose proof (lf_tab_names_short) as Hshort. rewrite forallb_forall in Hshort.
      specialize (Hshort (n2, ix) (nth_error_In _ _ Hn)). apply Nat.leb_le in Hshort. cbn [fst] in Hshort.
      destruct (Z_lt_le_dec p 0) as [Hneg | Hp0]; [|destruct (Z_lt_le_dec p (2 ^ 64)) as [Hp64 | Hbig]].
      - split; [unfold apart_frame; left; rewrite Rsp; lia|].
        split; [unfold apart_gnl; left; unfold LA_G_NL; lia|].
        split; [unfold apart; right; rewrite HEr; unfold TFIB_ERRNO; lia|].
        split; [intros Ht _; destruct (TB1 t1 kc nb1 Hnb1 In1 Ht) as (_ & _ & _ & _ & _ & H4 & _); unfold apart; left; lia|].
        split; [intros Ht _; destruct (TB1 t2 ac nb2 Hnb2 In2 Ht) as (_ & _ & _ & _ & _ & H4 & _); unfold apart; left; lia|].
        intros Hr. lia.
      - destruct (lf_tab_core SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
          cx fp ly3 S3 W3 (ms_mem msA) mdA k2 md mk kbs mbs gbs HB HJA HRO HdatA i0 n2 ix p Hn Hp ltac:(lia))
          as (TC1 & TC2 & TC3 & TC4 & TC5 & TCT & TC6 & TC7).
        split; [unfold apart_frame; left; rewrite Rsp, HKAK; unfold YImgTop.IMG_TOP, LLVMF_STK in *; lia|].
        split; [destruct (w_tab_place B TB HSEGS cx md mk kbs mbs gbs W3 (ms_mem msA) i0 n2 ix p HRO HdatA Hn Hp ltac:(lia))
                  as [Hl | Hl]; unfold apart_gnl, LA_G_NAMES, LA_G_NL, NK_SIZE in *; [right | left]; lia|].
        split; [apply w_apart_of; [lia | lia|]; intros x Hx Hx'; exact (proj2 (proj2 (TC7 x ltac:(lia))) Hx)|].
        split.
        { intros Ht H1. destruct (BUF t1 kc nb1 Hnb1 In1 Ht H1) as (_ & _ & _ & _ & _ & NI).
          apply w_apart_of; [lia | lia|]. intros x Hx Hx'. exact (NI x Hx' (proj1 (TC7 x ltac:(lia)))). }
        split.
        { intros Ht H1. destruct (BUF t2 ac nb2 Hnb2 In2 Ht H1) as (_ & _ & _ & _ & _ & NI).
          apply w_apart_of; [lia | lia|]. intros x Hx Hx'. exact (NI x Hx' (proj1 (TC7 x ltac:(lia)))). }
        intros _. split; [exact TC1|]. split; [exact TC2|]. split; [split; [exact TC3|]; split; [exact TC4 | exact TC5]|].
        exact TCT.
      - split; [unfold apart_frame; right; rewrite Rsp; unfold LLVMF_STK in *; lia|].
        split; [unfold apart_gnl; right; unfold LA_G_NL, NK_SIZE; lia|].
        split; [unfold apart; left; rewrite HEr; unfold TFIB_ERRNO; lia|].
        split; [intros Ht _; destruct (TB1 t1 kc nb1 Hnb1 In1 Ht) as (_ & _ & _ & _ & _ & _ & Hc & _); unfold apart; right;
                pose proof alloc_ceiling_value as ((Cmn & Cmx) & _); lia|].
        split; [intros Ht _; destruct (TB1 t2 ac nb2 Hnb2 In2 Ht) as (_ & _ & _ & _ & _ & _ & Hc & _); unfold apart; right;
                pose proof alloc_ceiling_value as ((Cmn & Cmx) & _); lia|].
        intros Hr. lia. }
    split.
    { intros x Hx. destruct (NM x Hx) as (_ & Hl & NC1 & NC3 & NC4 & NC5 & NCT & NC6 & NCI).
      split.
      - intros Ht H1. destruct (BUF t1 kc nb1 Hnb1 In1 Ht H1) as (_ & _ & _ & _ & _ & NI).
        apply w_apart_of; [lia | lia|]. intros y Hy Hy'. exact (NI y Hy' (proj1 (NCI y ltac:(lia)))).
      - intros Ht H1. destruct (BUF t2 ac nb2 Hnb2 In2 Ht H1) as (_ & _ & _ & _ & _ & NI).
        apply w_apart_of; [lia | lia|]. intros y Hy Hy'. exact (NI y Hy' (proj1 (NCI y ltac:(lia)))). }
    split.
    { intros Ht1 H1 Ht2 H2.
      destruct (TB1 t1 kc nb1 Hnb1 In1 Ht1) as (_ & E1 & _). destruct (TB1 t2 ac nb2 Hnb2 In2 Ht2) as (_ & E2 & _).
      pose proof (Hbap (t1, kc + 1) (t2, ac + 1) ltac:(rewrite E1; left; reflexivity)
        ltac:(rewrite E2; left; reflexivity)) as D.
      unfold zdisjoint in D. cbn [fst snd] in D. rewrite !RQ in D by lia. unfold apart. lia. }
    split.
    { intros Ht. destruct (Z_lt_le_dec kc 1) as [H0 | H1]; [exfalso; apply Ht; apply T1z; lia|].
      exact (proj1 (proj2 (proj2 (proj2 (proj2 (BUF t1 kc nb1 Hnb1 In1 Ht H1)))))). }
    split.
    { intros Ht. destruct (Z_lt_le_dec ac 1) as [H0 | H1]; [exfalso; apply Ht; apply T2z; lia|].
      exact (proj1 (proj2 (proj2 (proj2 (proj2 (BUF t2 ac nb2 Hnb2 In2 Ht H1)))))). }
    split.
    { intros x Hx. destruct (NM x Hx) as (_ & Hl & NC1 & NC3 & NC4 & NC5 & NCT & NC6 & _).
      split; [unfold apart_frame; left; rewrite Rsp, HKAK; unfold YImgTop.IMG_TOP, LLVMF_STK in *; lia|].
      split; [rewrite Hx in Hnm; exact (w_name_gnl s x Hnm Hl)|].
      split; [lia|]. split; [split; [exact NC3|]; split; [exact NC4 | exact NC5]|]. exact NCT. }
    split.
    { intros Ht. destruct (Z_lt_le_dec kc 1) as [H0 | H1]; [exfalso; apply Ht; apply T1z; lia|].
      destruct (BUF t1 kc nb1 Hnb1 In1 Ht H1) as (_ & _ & G1 & G2 & _). exact (conj G1 G2). }
    split.
    { intros Ht. destruct (Z_lt_le_dec ac 1) as [H0 | H1]; [exfalso; apply Ht; apply T2z; lia|].
      destruct (BUF t2 ac nb2 Hnb2 In2 Ht H1) as (_ & _ & G1 & G2 & _). exact (conj G1 G2). }
    split; [intros Ht H1; exact (proj1 (proj2 (BUF t1 kc nb1 Hnb1 In1 Ht H1)))|].
    intros Ht H1; exact (proj1 (proj2 (BUF t2 ac nb2 Hnb2 In2 Ht H1))).
  - (* the return, +0xed8 *)
    intros W2 ly2 S2 regs2 mem2 md2 Hle HJ2 Hpr Hfr2 Hfd2 Hfs2 Hkp Hsk Hs2 Hperm Hpost.
    rewrite Z.add_0_r in HJ2.
    set (ms2 := @mkst fy regs2 (getr (ms_regs msA) 1) mem2 (seg_rom SEGS)).
    change mem2 with (ms_mem ms2) in HJ2, Hkp, Hsk, Hpost.
    set (Er := fun a => inFP (reac_link_alias_read_awr (ms_regs msA) (rdW W3 (ms_mem msA))) a) in *.
    assert (LC : lf_call B cx REAC_LINK_ALIAS_READ_AK ly3 S3 ly2 S2 W3 (ms_mem msA) W2 (ms_mem ms2) Er).
    { split; [lia|]. split; [rewrite HKAK; unfold LLVMF_STK in *; clia|]. split; [exact Hkp | exact Hsk]. }
    assert (EE : forall a, Er a -> LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4 \/
        exists b, In b (nb1 ++ nb2) /\ fst b <= a < fst b + snd b).
    { intros a (r & Hin & Hr). unfold reac_link_alias_read_awr in Hin. rewrite Ra1, Ra2, Ra3, Ra4 in Hin.
      unfold aivl in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; [left; exact Hr| |].
      - destruct (Z.eqb_spec t1 0) as [E0 | E0]; [lia|]. destruct (TB1 t1 kc nb1 Hnb1 In1 E0) as (_ & E1 & _).
        right. exists (t1, kc + 1). split; [apply In1; rewrite E1; left; reflexivity | cbn [fst snd]; lia].
      - destruct (Z.eqb_spec t2 0) as [E0 | E0]; [lia|]. destruct (TB1 t2 ac nb2 Hnb2 In2 E0) as (_ & E2 & _).
        right. exists (t2, ac + 1). split; [apply In2; rewrite E2; left; reflexivity | cbn [fst snd]; lia]. }
    assert (NB : forall b, In b (nb1 ++ nb2) -> In b (ablocks B ly3 S3) /\
       (forall c, c = (md, MD_SIZE) \/ c = (mk, MK_SIZE) \/ In c T3 \/ (0 < c_n cx /\ c = (c_p cx, c_n cx)) ->
          zdisjoint (fst c, req_size (snd c)) (fst b, req_size (snd b)))).
    { intros b Hb. destruct (Hbin b Hb) as (H1 & _ & H3). exact (conj H1 H3). }
    assert (Psub : forall c, In c (ablocks B ly3 S3) -> In c (ablocks B ly2 S2))
      by (intros c Hc; exact (Permutation_in _ (Permutation_sym Hperm) Hc)).
    (* reac_link_alias_read's post *)
    specialize (Hpost kbs lf_tab nm). rewrite Ra0, Ra1, Ra2, Ra3, Ra4 in Hpost.
    destruct (Hpost Dk Dtab NMA) as (Hrc & (kbs' & Hk' & Hwf' & Hch' & Hen' & _ & Htab' & Hnx' & Hso' & Hse' & Hsent'
      & Hnsent' & Hop' & Hmis' & Hoc' & Hob' & Href') & Hkd & Hal & Hkb & Hab).
    clear Hpost.
    rewrite (r_sent_nil kbs Hns) in Hrc, Hnx', Hso', Hse', Hsent', Hnsent', Hkd, Hal.
    fold (r_LR nm kc ac kbs) in Hrc, Hnx', Hso', Hse', Hsent', Hnsent', Hkd, Hal.
    destruct (r_alias_post cx fp k2 _ _ _ _ md mk kbs mbs gbs T3 _ P N REAC_LINK_ALIAS_READ_AK Er SH_R ly3 S3 W3 msA mdA
      ly2 S2 W2 ms2 md2 kbs' (nb1 ++ nb2) HB SH_R_len HCA HJ2 Hfr2 LC EE NB Hs2 Hperm Hfd2 Hfs2 HcurA Hk' Hwf' Htab'
      Hop' ltac:(rewrite Hmis'; exact Dmis) ltac:(rewrite Doc in Hoc'; lia)) as (HC2 & Hcur2 & HRO2).
    pose proof (ar_pres _ _ Hpr) as (P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27).
    pose proof (lf_call_kagree B cx REAC_LINK_ALIAS_READ_AK ly3 S3 ly2 S2 W3 (ms_mem msA) W2 (ms_mem ms2) Er LC) as KG.
    pose proof HJ2 as (_ & _ & (memS2 & HJi2 & _) & _). pose proof HJi2 as (HAR2 & _).
    destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
      cx fp ly3 S3 W3 (ms_mem msA) mdA k2 HB HJA HfrA) as (HFa & F32 & F4 & Fc & Fapp & Fpres & Fshp & Fsep).
    (* the frame's bytes are not the call's *)
    assert (FX : forall x, lf_F cx fp <= x < lf_F cx fp + 1024 ->
        ~ lf_X B ly3 S3 ly2 S2 (lf_sp1 cx - REAC_LINK_ALIAS_READ_AK) (lf_sp1 cx) Er x).
    { intros x Hx. apply (lfx_frm B ly3 S3 ly2 S2 _ _ Er LF_CID fp x ltac:(rewrite HfrA; left; reflexivity));
        [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite HFa; change (fs_frame_bytes LF_CID) with 1024; lia|].
      intros HEa. destruct (EE x HEa) as [Hg | (b & Hb & Hbx)].
      - destruct (Fpres x Hx) as (_ & NI). apply NI. apply (kp_img_ok_in B MS la_nul x IMG). left.
        unfold NK_N_SENT, NK_SIZE in *. lia.
      - destruct (NB b Hb) as (Hb3 & _). destruct b as [b n]. cbn [fst snd] in Hbx.
        pose proof (Fsep b n Hb3) as D. unfold zdisjoint in D. cbn [fst snd] in D.
        assert (n <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia). lia. }
    assert (NIF2 : lf_slot cx W2 ms2 LS_NIF (nk_opened kbs)).
    { unfold lf_slot, lf_at in *.
      apply (d4_slot_callee B cx REAC_LINK_ALIAS_READ_AK ly3 S3 ly2 S2 W3 (ms_mem msA) W2 (ms_mem ms2) Er _ _ LC);
        [unfold LS_NIF; lia | unfold LS_NIF, LLVMF_STK in *; lia | | exact NIFA].
      intros j Hj HEa. destruct (EE _ HEa) as [Hg | (b & Hb & Hbx)].
      - unfold LS_NIF, LLVMF_STK, LA_G_NL, NK_N_SENT in *. lia.
      - destruct (NB b Hb) as (Hb3 & _). destruct b as [b n]. cbn [fst snd] in Hbx.
        destruct (kp_blk_place B LAWS ly3 S3 W3 (ms_mem msA) mdA b n (lf_sp1 cx + LS_NIF + j) HARA Hb3
          ltac:(unfold req_size; destruct (Z.eqb_spec n 0); lia)) as (_ & Hc). unfold LS_NIF, LLVMF_STK in *. lia. }
    assert (WCF : forall x n, lf_F cx fp <= x -> x + n <= lf_F cx fp + 1024 ->
        wcarry SEGS (rdW W3 (ms_mem msA)) (rdW W2 (ms_mem ms2)) x n).
    { intros x n Hx1 Hx2 ii Hii _.
      apply (apresent_writable SEGS). destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP
        LF_MO_END LAWS cx fp ly2 S2 W2 (ms_mem ms2) md2 k2 HB HJ2 ltac:(rewrite Hfr2; exact HfrA))
        as (_ & _ & _ & _ & _ & Fp2 & _). exact (proj1 (Fp2 (x + ii) ltac:(lia))). }
    apply (HA cx fy fp k2 ly2 S2 W2 ms2 md2 HB Hfx HJ2 ltac:(rewrite Hfr2; exact Hfr)).
    exists md, mk, P, N, kbs, kbs', mbs, gbs, T3, s, nm, kc, ac, t1, t2, nb1, nb2.
    split.
    { unfold lf_shape, ms2. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
      rewrite Q1, <- HBASE. unfold LR_a, AF_LLVMFuzzerTestOneInput. repeat split; reflexivity. }
    kreg KR 8 (8%bv : bv 5) K8. kreg KR 9 (9%bv : bv 5) K9. kreg KR 18 (18%bv : bv 5) K18.
    kreg KR 19 (19%bv : bv 5) K19.
    kreg KR 21 (21%bv : bv 5) K21. kreg KR 22 (22%bv : bv 5) K22. kreg KR 23 (23%bv : bv 5) K23.
    kreg KR 24 (24%bv : bv 5) K24. kreg KR 25 (25%bv : bv 5) K25. kreg KR 26 (26%bv : bv 5) K26.
    kreg KR 27 (27%bv : bv 5) K27.
    split.
    { unfold r_regs5, ms2. cbn [ms_regs mkst].
      rewrite P18, P19, P20, P21, P22, P23, P24, P25, P26, P27, K18, K19, Q20, K21, K22, K23, K24, K25, K26, K27.
      repeat split; assumption. }
    split; [exact Hrc|].
    split; [exact Hnm|]. split; [exact Hkc|]. split; [exact Hac|]. split; [exact Hi|].
    split; [unfold lf_core, ms2; cbn [ms_regs mkst]; rewrite P2, P8, P9, P3, P4, K2, K8, K9, K3, K4;
            repeat split; assumption|].
    split; [exact HC2|]. split; [exact Hcur2|]. split; [exact Hop|].
    split; [exact Hob'|].
    split.
    { intros Hr. apply Href'. destruct Hr as [Hr | [Hr | Hr]]; [left; exact Hr | right; left; exact Hr | right; right; exact Hr]. }
    split; [exact Hsent'|]. split; [exact Hnsent'|].
    split.
    { destruct (u_read_ce lf_tab nm kc ac [] (nk_kstate kbs)) as (Ce & Ee).
      apply r_nk_kstate_of; [ | exact Hnx' | | exact Hso' | exact Hse'];
        unfold r_LR, read_lib; [rewrite Ce, Hch' | rewrite Ee, Hen']; reflexivity. }
    split; [exact Hrq|].
    split; [unfold md_kstate in *; rewrite Hch', Hen'; exact Hks|].
    split.
    { split; [exact Hnb1|]. split; [exact Hnb2|]. split; [|exact Hbap].
      intros b Hb. destruct (Hbin b Hb) as (H1 & H2 & H3). exact (conj (Psub _ H1) (conj H2 H3)). }
    (* the write set of the call, byte by byte *)
    assert (ER : forall a, Er a ->
        LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4 \/ (t1 <> 0 /\ t1 <= a < t1 + kc) \/ (t2 <> 0 /\ t2 <= a < t2 + ac)).
    { intros a (r & Hin & Hr). unfold reac_link_alias_read_awr in Hin. rewrite Ra1, Ra2, Ra3, Ra4 in Hin.
      unfold aivl in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; [left; exact Hr| |].
      - destruct (Z.eqb_spec t1 0) as [E0 | E0]; [lia|]. right; left. lia.
      - destruct (Z.eqb_spec t2 0) as [E0 | E0]; [lia|]. right; right. lia. }
    (* a text buffer's guard byte, not written by the call *)
    assert (GD : forall t c nb, tb_nb c t nb -> incl nb (nb1 ++ nb2) -> 1 <= c ->
        (forall a, Er a -> ~ (a = t + c)) ->
        atbuf_at SEGS (rdW W3 (ms_mem msA)) t c (repeat (zb GUARD_BYTE) (Z.to_nat c)) ->
        au8arr SEGS (rdW W2 (ms_mem ms2)) (t + c) [zb GUARD_BYTE]).
    { intros t c nb Hnb Hinc H1 HNE HT.
      destruct (TB1 t c nb Hnb Hinc ltac:(destruct Hnb as [(E0 & _) | (_ & H4 & _)]; lia))
        as (_ & _ & Hin3 & _ & _ & _ & _ & _).
      apply (au8arr_keep SEGS _ _ _ _ _ KG); [ | | exact (r_au8arr_guard SEGS _ _ _ _ HT)].
      - intros ii Hii _. replace ii with 0 by (cbn [length] in Hii; lia). rewrite Z.add_0_r.
        apply (apresent_writable SEGS).
        destruct (al_blocks _ _ LAWS ly2 S2 W2 (ms_mem ms2) md2 t (c + 1) HAR2 (Psub _ Hin3))
          as (_ & _ & _ & _ & Hp & _).
        apply (proj1 (Hp (t + c) ltac:(unfold req_size; destruct (Z.eqb_spec (c + 1) 0); lia))).
      - intros j Hj. cbn [length] in Hj. replace j with 0 by lia. rewrite Z.add_0_r.
        apply (lfx_blk B ly3 S3 ly2 S2 _ _ Er t (c + 1) (t + c) Hin3 ltac:(lia)).
        intros HEa. exact (HNE _ HEa eq_refl). }
    assert (FB : forall x, LA_G_NL <= x < LA_G_NL + NK_N_SENT + 4 -> forall t c nb, tb_nb c t nb ->
        incl nb (nb1 ++ nb2) -> 1 <= c -> t <= x < t + c + 1 -> False).
    { intros x Hx t c nb Hnb Hinc H1 Ht.
      destruct (TB1 t c nb Hnb Hinc ltac:(destruct Hnb as [(E0 & _) | (_ & H4 & _)]; lia))
        as (_ & _ & _ & _ & HX & _).
      destruct (HX x ltac:(lia)) as (NI & _). apply NI. apply (kp_img_ok_in B MS la_nul x IMG). left.
      unfold NK_N_SENT, NK_SIZE in *. lia. }
    split.
    { intros H1. assert (Ht : t1 <> 0) by (intros E0; apply T1z in E0; lia).
      split; [exact (Hkd Ht H1)|]. split; [exact (Hkb Ht H1)|].
      apply (GD t1 kc nb1 Hnb1 In1 H1); [|exact (Hb1A H1)].
      intros a HEa Ha. subst a. destruct (ER _ HEa) as [Hg | [(_ & Hr) | (Ht2 & Hr)]].
      - exact (FB _ Hg t1 kc nb1 Hnb1 In1 H1 ltac:(lia)).
      - lia.
      - assert (H2 : 1 <= ac) by (destruct (Z_lt_le_dec ac 1); [exfalso; apply Ht2; apply T2z; lia | lia]).
        destruct (TB1 t1 kc nb1 Hnb1 In1 Ht) as (_ & E1 & _). destruct (TB1 t2 ac nb2 Hnb2 In2 Ht2) as (_ & E2 & _).
        pose proof (Hbap (t1, kc + 1) (t2, ac + 1) ltac:(rewrite E1; left; reflexivity)
          ltac:(rewrite E2; left; reflexivity)) as D.
        unfold zdisjoint in D. cbn [fst snd] in D. rewrite !RQ in D by lia. lia. }
    split.
    { intros H1. assert (Ht : t2 <> 0) by (intros E0; apply T2z in E0; lia).
      split; [exact (Hal Ht H1)|]. split; [exact (Hab Ht H1)|].
      apply (GD t2 ac nb2 Hnb2 In2 H1); [|exact (Hb2A H1)].
      intros a HEa Ha. subst a. destruct (ER _ HEa) as [Hg | [(Ht1 & Hr) | (_ & Hr)]].
      - exact (FB _ Hg t2 ac nb2 Hnb2 In2 H1 ltac:(lia)).
      - assert (H2 : 1 <= kc) by (destruct (Z_lt_le_dec kc 1); [exfalso; apply Ht1; apply T1z; lia | lia]).
        destruct (TB1 t1 kc nb1 Hnb1 In1 Ht1) as (_ & E1 & _). destruct (TB1 t2 ac nb2 Hnb2 In2 Ht) as (_ & E2 & _).
        pose proof (Hbap (t1, kc + 1) (t2, ac + 1) ltac:(rewrite E1; left; reflexivity)
          ltac:(rewrite E2; left; reflexivity)) as D.
        unfold zdisjoint in D. cbn [fst snd] in D. rewrite !RQ in D by lia. lia.
      - lia. }
    split.
    { destruct HWKA as (W1 & W2').
      pose proof (r_kind_fit lf_tab nm kc ac [] (nk_kstate kbs) ltac:(lia)) as Lk.
      split.
      - apply (acstr_keep SEGS _ _ _ _ _ KG); [|exact W1]. intros j Hj. apply FX.
        unfold r_RR, read_model in *; cbn [r_kind] in *. unfold LO_B2E0 in *. lia.
      - intros H1. apply (abuf_keep SEGS _ _ _ _ _ KG); [ | | exact (W2' H1)].
        + apply WCF; unfold LO_B2E0; lia.
        + intros j Hj. apply FX. unfold LO_B2E0. lia. }
    split.
    { destruct HWAA as (W1 & W2').
      pose proof (r_alias_fit lf_tab nm kc ac [] (nk_kstate kbs) ltac:(lia)) as Lk.
      split.
      - apply (acstr_keep SEGS _ _ _ _ _ KG); [|exact W1]. intros j Hj. apply FX.
        unfold r_RR, read_model in *; cbn [r_alias] in *. unfold LO_B330 in *. lia.
      - intros H1. apply (abuf_keep SEGS _ _ _ _ _ KG); [ | | exact (W2' H1)].
        + apply WCF; unfold LO_B330; lia.
        + intros j Hj. apply FX. unfold LO_B330. lia. }
    split; [exact NIF2 | exact RRC].
Qed.

End a.

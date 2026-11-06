(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module paths and module names changed; 407 of its 463 lines of code are new or changed and 1276 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...), the op_mark arm at
   +0xc9c (Op2Cut.v o2_q_inv): `ld s5, 0x90(s1)` (the marks block), `mv a0, s5; mv a1, s4; jal mark_quietly`
   (0x8347c, ra 0x83480 = +0xcac), the opening call (the kept set is empty) or a later one (it holds the FILE); at
   its return the library's answer and marks list agree with the model's (Op2Lib.v o2_agree), so the data hold
   marks_are and requests_are again: Op2Y.v's o2_y_inv at +0xcac.
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
  LinkWalkCall LinkWalkZsh.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs
  LLVMFuzzerTestOneInputKeep LLVMFuzzerTestOneInputKpre LLVMFuzzerTestOneInputDec LLVMFuzzerTestOneInputArmR
  LLVMFuzzerTestOneInputArmK LLVMFuzzerTestOneInputKpost LLVMFuzzerTestOneInputLp
  LLVMFuzzerTestOneInputMq LLVMFuzzerTestOneInputMqCall LLVMFuzzerTestOneInputMqPost LLVMFuzzerTestOneInputOp5C.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
  model_decide_c remember_c reac_code_emit_c reac_served_mark_c mark_quietly_c check_write_c check_mark_c
  check_requests_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputSel
  LLVMFuzzerTestOneInputOp3Lib LLVMFuzzerTestOneInputOp5 LLVMFuzzerTestOneInputOp5M LLVMFuzzerTestOneInputOp2Lib
  LLVMFuzzerTestOneInputOp2K LLVMFuzzerTestOneInputOp2Cut LLVMFuzzerTestOneInputOp2Nm LLVMFuzzerTestOneInputOp2Y
  LLVMFuzzerTestOneInputOp3K.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Local Notation AFL := AF_LLVMFuzzerTestOneInput.

(* the name op_mark passes is NULL or an image string *)
Lemma o2q_s_range : forall s nm, w_name s nm -> 0 <= s < 0x654000.
Proof.
  intros s nm [(-> & _) | [(k & Hk & -> & _) | (j & Hj & -> & _)]]; [lia | unfold LA_G_NAMES; lia |].
  unfold ODD_PTRS. do 6 (destruct j as [|j]; [cbn; lia|]). lia.
Qed.

(* the runner's entry state at +0xc9c: the slot 0x90(s1) holding the marks block *)
Definition o2q_rg : YP09.region := YP09.mkRegion (Some 9%nat) 0x90 0x98 0x90 0x90 [YP09.mkChunk 0x90 (CVal 8 (SOff 32 0))].
Definition o2q_ss : sstate := mkSS LO2_q sr_atoms [o2q_rg] None (mkFacts [] [] []).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation BASE := (pa_val A_TEXT).
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
Hypothesis MT_OK : forall S m, mo_ok MT S m.
(* mark_quietly's two arms, as proved (lib/A/Prog/mark_quietly_c.v) *)
Hypothesis MQO : forall fx0 : YK11.FPState,
  @mark_quietly_acontract_open fx0 rc SK pa_segs PCAP_RLO PCAP_RHI B MT (mo_malloc MT AMF_BLOCK) LF_CTX
    (fun _ => True) (mq_ledpost B).
Hypothesis MQA : forall fx0 : YK11.FPState,
  @mark_quietly_acontract_again fx0 rc SK pa_segs PCAP_RLO PCAP_RHI B.

#[local] Abbreviation BASEF cx := (@lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Abbreviation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).
#[local] Abbreviation FROM POST GI :=
  (@lf_from fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END POST GI).
#[local] Abbreviation YCAC i := (o2_y_inv B MT MS la_nul LF_MO_SET LF_MO_OP (AFL + 0xcac) 10%bv i).

Ltac o2q_sv := unfold acallee_saved; first [ (vm_compute; lia) | (cbn; lia) | (simpl; lia) |
    (vm_compute; right; right; right; right; right; split; discriminate) ].

(* the name op_mark passes: NULL or the selector's image string *)
Lemma o2q_names : forall ly S (W : world SEGS) mem mdl (regs : bvmap 5 word) s nm mk fb fn,
  la_nul = LA_NUL -> MS = link_amf ->
  AR SEGS B ly S W mem mdl -> arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  lf_gnames_at 64 (rdW W mem) -> alloc_ceiling <= spZ regs - MARK_QUIETLY_AK -> YCbq.off_img mk MK_SIZE ->
  aarg regs 0 = mk -> aarg regs 1 = s -> w_name s nm ->
  (fb + fn <= 0x10000 \/ YImgTop.IMG_TOP <= fb) -> 0 <= fn ->
  astr_arg SEGS (rdW W mem) (aarg regs 1) nm /\
  amk_name_ok SEGS B regs MARK_QUIETLY_AK fb fn (rdW W mem) nm /\
  (forall t, nm = Some t -> aarg regs 1 + Z.of_nat (length t) + 8 <= LA_G_SINK) /\
  aarg regs 1 < alloc_ceiling /\
  (forall a, aarg regs 1 <> 0 -> forall t, acstr_at SEGS (rdW W mem) (aarg regs 1) t ->
     aarg regs 1 <= a <= aarg regs 1 + Z.of_nat (length t) -> akb SEGS B ly S (spZ regs - MARK_QUIETLY_AK) (spZ regs) a).
Proof.
  intros ly S W mem mdl regs s nm mk fb fn HLN HMS HAR HRO Hgn HK Hmk Ha0 Ha1 Hw Hfb Hfn.
  pose proof asan_consts as ((C1a & C1b) & _).
  pose proof (ts_errno B TB) as HE.
  unfold amk_name_ok. rewrite Ha0, Ha1.
  destruct nm as [t|].
  2: { assert (Hs0 : s = 0)
         by (destruct Hw as [(H0 & _) | [(k & _ & _ & En) | (j & _ & _ & En)]]; [exact H0 | discriminate En | discriminate En]).
       rewrite Hs0 in *. split; [reflexivity|]. split; [intros t Ht; discriminate|]. split; [intros t Ht; discriminate|].
       split; [lia|]. intros a Hz; contradiction. }
  destruct (o2_name_rt B TB HSEGS ly S W mem mdl regs MARK_QUIETLY_AK s t HAR HRO Hgn HK Hw)
    as (Hac & Hrt & Hs16 & Hl11 & Hloc).
  assert (Hrt' : astr_rt_ok SEGS regs MARK_QUIETLY_AK (rdW W mem) s t) by exact Hrt.
  split; [split; [lia | exact Hac]|].
  split.
  { intros t' Ht'. injection Ht' as <-.
    split; [lia|]. split; [exact Hrt'|].
    split; [unfold apart_gnl; unfold LA_G_NL, NK_SIZE, LA_G_NAMES, G_NAMES_SIZE in *; lia|].
    split; [unfold apart; unfold YImgTop.IMG_TOP, LA_G_NL, LA_G_NAMES, G_NAMES_SIZE in *; lia|].
    split; [unfold apart; rewrite HE; unfold TFIB_ERRNO, LA_G_NL, LA_G_NAMES, G_NAMES_SIZE in *; lia|].
    intros _. unfold apart.
    unfold YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, MK_SIZE, LA_G_NL, LA_G_NAMES, G_NAMES_SIZE in *; lia. }
  split; [intros t' Ht'; injection Ht' as <-; unfold LA_G_SINK, LA_G_NL, LA_G_NAMES, G_NAMES_SIZE in *; lia|].
  split; [unfold LA_G_NL, LA_G_NAMES, G_NAMES_SIZE in *; lia|].
  intros a _ t' Ht' Ha. pose proof (kp_acstr_unique _ _ _ _ _ Ht' Hac) as Et. subst t'.
  right; right; left. exact (o2_name_img B TB HSEGS MS la_nul s t HMS HLN Hw a ltac:(lia)).
Qed.

(* the cut at mark_quietly's return (+0xcac): its answer agrees with the model's, the data hold marks_are and
   requests_are again; then Op2Y.v's o2_y_inv *)
Lemma o2q_after : forall POST i cx (fx' : YK11.FPState) fp k' ly2 S2 (W2 : world SEGS) (regs regs2 : bvmap 5 word)
    mem2 md2 md mk P N kbs kbs' mbs gbs gbs' T3' nm (ms3 : machine_state),
  0 <= i <= 47 -> FROM POST (YCAC i) ->
  BASEF cx -> @BoxBase.fxr fx fx' -> JRN cx fp ly2 S2 W2 mem2 md2 k' -> frames S2 = [(LF_CID, fp)] ->
  ms_regs ms3 = regs -> lf_core cx ms3 -> o2_yregs cx md mk fp i ms3 ->
  getr regs 23 = w64 (m_rc (o2_MM nm kbs gbs)) ->
  getr regs 1 = Z_to_bv 64 (BASE + (AFL + 0xcac)) ->
  aregs_preserved regs regs2 -> aarg regs 0 = mk -> 0 < mk ->
  mqp_rc regs regs2 mk kbs kbs' gbs gbs' nm -> marks_wf gbs' ->
  (marks_are gbs' mbs -> lf_data cx md mk kbs' mbs gbs' (rdW W2 mem2)) ->
  md_reqs mbs = m_reqs (o2_MM nm kbs gbs) -> md_marks mbs = m_marks (o2_MM nm kbs gbs) ->
  nlk_wf kbs -> model_wf mbs -> nk_n_sent kbs = 0 -> nk_opened kbs <= 64 * i ->
  lf_saved cx W2 (@mkst fx' regs2 (getr regs 1) mem2 (seg_rom SEGS)) ->
  lf_header cx fp W2 (@mkst fx' regs2 (getr regs 1) mem2 (seg_rom SEGS)) ->
  lf_fshadow cx fp W2 (@mkst fx' regs2 (getr regs 1) mem2 (seg_rom SEGS)) LF_SH0 ->
  lf_slots cx md mk fp W2 (@mkst fx' regs2 (getr regs 1) mem2 (seg_rom SEGS)) ->
  lf_cur cx W2 (@mkst fx' regs2 (getr regs 1) mem2 (seg_rom SEGS)) P N ->
  lf_jbk B MT MS la_nul cx fp k' (lf_ev (i + 1)) (lf_mo LF_MO_SET LF_MO_OP (i + 1)) (lf_wl (i + 1)) LF_LIVE_HELD
    ly2 S2 W2 (@mkst fx' regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 T3' [(md, MD_SIZE); (mk, MK_SIZE)] ->
  lf_blocks B cx md mk T3' ly2 S2 (rdW W2 mem2) ->
  SRr SEGS W2 (mkCfg (@mkst fx' regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2) (POST cx).
Proof.
  intros POST i cx fx' fp k' ly2 S2 W2 regs regs2 mem2 md2 md mk P N kbs kbs' mbs gbs gbs' T3' nm ms3
    Hi NEXT HB Hfx HJ2 Hfr2 Hrg Hcore Hyr R23 R1 Hpr Ha0 Hmk0 (Rnull & Rmk) Hkwf2 Hdat2f Hrq Hmm Hnwf Hmwf Hns Hop
    Hsv2 Hhd2 Hfsh2 Hsl2 Hcur2 Hjbk2 Hblk2.
  set (ms2 := @mkst fx' regs2 (getr regs 1) mem2 (seg_rom SEGS)) in *.
  assert (KR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr (ms_regs ms2) r = getr (ms_regs ms3) r).
  { intros r Hr. cbn [ms2 ms_regs mkst]. rewrite Hrg. exact (o5c_pres _ _ Hpr r Hr). }
  assert (S0 : nk_sent kbs = []) by (unfold nk_sent; rewrite Hns; reflexivity).
  pose proof (Rmk ltac:(lia)) as RM. cbv zeta in RM. rewrite S0 in RM.
  destruct RM as (Rrc & Hnames & Hn & _ & _ & _ & _ & Hsent & _ & Hopd).
  destruct (o2_agree lf_tab nm (mk_names gbs) [] (nk_kstate kbs)) as (Asr & Amk & Arq).
  change (o2_mm lf_tab nm (mk_names gbs) [] (nk_kstate kbs)) with (o2_MM nm kbs gbs) in Asr, Amk, Arq.
  set (M := mark_lib lf_tab nm (mk_names gbs) [] (nk_kstate kbs)) in *.
  assert (Hgr : - 2 ^ 63 <= m_rc M < 2 ^ 63).
  { assert (HK3 : o2_kb3 (nk_kstate kbs))
      by (unfold o2_kb3, nk_kstate; cbn [k_sock k_send k_end]; unfold nlk_wf in Hnwf; lia).
    pose proof (o2_lib_rc_range lf_tab nm (mk_names gbs) [] (nk_kstate kbs) HK3) as RG. fold M in RG. lia. }
  assert (Hare2 : marks_are gbs' mbs).
  { split.
    - rewrite Hn, Amk, <- Hmm. unfold md_marks. rewrite length_map, length_seq.
      pose proof Hmwf as (_ & _ & _ & _ & _ & (Hn0 & _)). lia.
    - rewrite Hnames, Amk, Hmm. reflexivity. }
  pose proof (Hdat2f Hare2) as Hdat2.
  assert (Hreq2 : requests_are kbs' mbs).
  { pose proof Hdat2 as (Dk2 & Dwf2 & _ & _ & _ & _ & Dmd2 & Dmwf2 & _).
    apply u_requests_are; [exact (proj2 Dk2) | exact (proj2 Dmd2) | exact Dwf2 | exact Dmwf2 |].
    rewrite Hsent, Arq, Hrq. reflexivity. }
  apply (NEXT cx fx' fp k' ly2 S2 W2 ms2 md2 HB Hfx HJ2 Hfr2).
  exists md, mk, P, N, (m_rc M), (m_rc (o2_MM nm kbs gbs)), kbs', mbs, gbs', T3'.
  split; [exact Hi|].
  split.
  { unfold lf_shape. cbn [ms2 mkst ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr].
    split; [rewrite R1; reflexivity|]. repeat split; reflexivity. }
  split; [unfold lf_core in *; repeat split; rewrite KR by o2q_sv; tauto|].
  split; [unfold o2_yregs in *; repeat split; rewrite KR by o2q_sv; tauto|].
  split; [exact Rrc|].
  split; [rewrite KR by o2q_sv; rewrite Hrg; exact R23|].
  split; [exact Hgr|]. split; [exact Asr|].
  split; [exact Hsv2|]. split; [exact Hhd2|]. split; [exact Hfsh2|]. split; [exact Hsl2|]. split; [exact Hcur2|].
  split; [exact Hjbk2|]. split; [exact Hblk2|]. split; [exact Hdat2|].
  split; [lia | exact Hreq2].
Qed.

(* op_mark at its call of mark_quietly (0x8347c): a0 = the marks block, a1 = the name *)
Lemma o2q_call : forall POST i cx (fy : YK11.FPState) fp k2 ly3 S3 W3 ms3 md3 md mk P N kbs mbs gbs T3 s nm,
  0 <= i <= 47 -> FROM POST (YCAC i) ->
  BASEF cx -> @BoxBase.fxr fx fy -> JRN cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 -> frames S3 = [(LF_CID, fp)] ->
  ms3 = @mkst fy (ms_regs ms3) (w64 MARK_QUIETLY_A) (ms_mem ms3) (seg_rom SEGS) ->
  lf_core cx ms3 -> o2_yregs cx md mk fp i ms3 ->
  getr (ms_regs ms3) 23 = w64 (m_rc (o2_MM nm kbs gbs)) ->
  getr (ms_regs ms3) 1 = Z_to_bv 64 (BASE + (AFL + 0xcac)) ->
  aarg (ms_regs ms3) 0 = mk -> aarg (ms_regs ms3) 1 = s -> w_name s nm ->
  lf_saved cx W3 ms3 -> lf_header cx fp W3 ms3 -> lf_fshadow cx fp W3 ms3 LF_SH0 ->
  lf_slots cx md mk fp W3 ms3 -> lf_cur cx W3 ms3 P N ->
  lf_jbk B MT MS la_nul cx fp k2 (lf_ev i) (lf_mo LF_MO_SET LF_MO_OP i) (lf_wl i) LF_LIVE_HELD ly3 S3 W3 ms3 md3 T3
    [(md, MD_SIZE); (mk, MK_SIZE)] ->
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) ->
  lf_data_nm cx md mk kbs mbs gbs (rdW W3 (ms_mem ms3)) ->
  md_reqs mbs = m_reqs (o2_MM nm kbs gbs) -> md_marks mbs = m_marks (o2_MM nm kbs gbs) ->
  nk_n_sent kbs = 0 -> nk_opened kbs <= 64 * i ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST i cx fy fp k2 ly3 S3 W3 ms3 md3 md mk P N kbs mbs gbs T3 s nm Hi NEXT HB Hfx HJ Hfr Hms Hcore Hyr
    R23 R1 Ha0 Ha1 Hw Hsv Hhd Hfsh Hsl Hcur Hjbk Hblk Hdatn Hrq Hmm Hns Hop.
  pose proof asan_consts as ((C1a & C1b) & _).
  pose proof HB as (HPRE & Hfz & HGX & HLN & HMS & _).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR3).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & Hs16 & Hlo & H47').
  pose proof Hcore as (C2 & C8 & C9 & C3 & C4).
  pose proof Hjbk as (J1 & JL & Jfa & J3 & J4 & J5 & J6 & J7 & Jgi & Jenv & Jbl & Jinc & Jla & HRO & Jpl & Jpv).
  pose proof Hblk as (Bmd & Bmk & _ & _ & _ & _ & _ & _ & Bmdt & Bmkt & _).
  pose proof Hdatn as (_ & Hnwf & _ & _ & _ & _ & _ & Hmwf & _ & Dkwf & _ & Hgn & _).
  assert (Bmd4 : 4096 <= md) by (destruct (al_blocks _ _ LAWS _ _ _ _ _ md MD_SIZE HAR3 Bmd) as (_ & H4 & _); lia).
  assert (Bmk4 : 4096 <= mk) by (destruct (al_blocks _ _ LAWS _ _ _ _ _ mk MK_SIZE HAR3 Bmk) as (_ & H4 & _); lia).
  assert (Bmk0 : 0 < mk) by lia.
  assert (Hin : In (LF_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
  assert (HAK : MARK_QUIETLY_AK = 24608) by reflexivity.
  assert (Hsp : spZ (ms_regs ms3) = lf_sp1 cx).
  { unfold spZ. rewrite C2. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in Hlo. clia. }
  assert (Hs0 : s0Z (ms_regs ms3) = spZ (c_regs cx)).
  { unfold s0Z, spZ. rewrite C8. unfold w64. apply unsigned_lit_small.
    pose proof (bv_unsigned_in_range _ (getr (c_regs cx) 2)) as R. change (bv_modulus 64) with (2 ^ 64) in R. unfold spZ in *. lia. }
  assert (H8 : rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)))
    by exact (proj1 Hsv).
  assert (H16' : rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx))).
  { pose proof (proj2 Hsv 0 ltac:(lia)) as H. cbn in H. replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16)
      in H by lia. exact H. }
  assert (R1' : getr (ms_regs ms3) 1 = Z_to_bv 64 (link_text + (AFL + 0xcac))) by (rewrite R1, (lv_text LV); reflexivity).
  assert (Hsite : In (AFL + 0xcac) LF_MARK_SITES) by (right; left; reflexivity).
  assert (Hop2 : nk_opened kbs + 2 < 2 ^ 31) by lia.
  assert (Hfrm : YK0o.frm_zero (@YK11.fp_csr fy)) by exact (fxr_frm0 fx fy Hfz Hfx).
  assert (HKc : alloc_ceiling <= spZ (ms_regs ms3) - MARK_QUIETLY_AK)
    by (rewrite Hsp, HAK; unfold LLVMF_STK in *; clia).
  assert (Hev : k2 + 1 <= EV_LIB) by (pose proof lf_ev_bound as EB; unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *; lia).
  assert (Ha0' : aarg (ms_regs ms3) 0 = 0 \/ aarg (ms_regs ms3) 0 = mk) by (right; exact Ha0).
  assert (HPB : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by (intros Hn; exact (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
          cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ Hn)).
  rewrite Hms. change (mkCfg (mkst (ms_regs ms3) (w64 MARK_QUIETLY_A) (ms_mem ms3) (seg_rom SEGS)) md3)
    with (cfg_at SEGS MARK_QUIETLY_A (ms_regs ms3) (ms_mem ms3) md3).
  destruct (amf_gi_shape SEGS MS T3 _ Jgi) as [ET | (f & ET)]; subst T3.
  - (* the opening call *)
    destruct Jgi as [(Hh0 & _) | (f & _ & HT & _)]; [|discriminate HT].
    destruct (o2q_names ly3 S3 W3 (ms_mem ms3) md3 (ms_regs ms3) s nm mk 0 0 HLN HMS HAR3 HRO Hgn HKc Bmkt Ha0 Ha1 Hw
      ltac:(left; lia) ltac:(lia)) as (Hnm & Hnok & Hnlo & Ha1c & Hnakb).
    eapply apostF_continue.
    { rewrite HMS in Hh0, Jenv.
      exact (lf_mq_open_call SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS MT_OK MQO
        fy cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 (ms_regs ms3) md mk kbs mbs gbs (AFL + 0xcac) nm HB HJ Hfr Hfrm Hev Jbl
        HRO Hblk Hdatn Hh0 Jenv Hop2 H8 H16' Hsp Hs0 C3 C4 (lv_text LV) R1' Hsite Ha0' Ha1c Hnm Hnok Hnlo
        ltac:(rewrite Hsp in Hnakb; rewrite Hsp; exact Hnakb)). }
    intros fx' W2 c2 Hle Hfxr Hpost.
    destruct Hpost as (ly2 & S2 & regs2 & mem2 & md2 & Hc2 & HJ2 & Hpr & Hfr2 & Hfd & Hfs & Hkp & Hsk & (Hmo & Hled & Hpa)).
    subst c2.
    destruct Hpa as (sink & Hsnz & Hgs & Hgy & Hgo & Hperm & (kq & Hkq & Hmf) & Hrc).
    set (ms2 := @mkst fx' regs2 (getr (ms_regs ms3) 1) mem2 (seg_rom SEGS)).
    change (SRr SEGS W2 (mkCfg ms2 md2) (POST cx)).
    assert (Pmd2 : In (md, MD_SIZE) (ablocks B ly2 S2))
      by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; left; exact Bmd).
    assert (Pmk2 : In (mk, MK_SIZE) (ablocks B ly2 S2))
      by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; left; exact Bmk).
    rewrite Hsp in Hkp.
    destruct (lf_mq_post_common SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS
      cx fp k2 _ _ _ _ md mk kbs mbs gbs ([] : list (Z * Z)) _ P N ly3 S3 W3 ms3 md3 ly2 S2 W2 ms2 md2 (k2 + 1) (ms_regs ms3) regs2
      _ (fun a => LA_G_SINK <= a < LA_G_SINK + 8 \/ LA_G_SAID <= a < LA_G_SAID + SAID_SIZE \/
                  LA_G_SAY <= a < LA_G_SAY + 8 \/ LA_OFL_HEAD <= a < LA_OFL_HEAD + 8) nm
      HB Hfr HJ HJ2 Hsp Hkp Hsk Pmd2 Pmk2 Ha0'
      (fun a Ha => o5m_E_open (ms_regs ms3) _ mk a Bmk0 Ha0' Ha)
      (fun a Ha => o5m_Fopen_miss B MS la_nul LAWS HSEGS cx fp md mk ly3 S3 W3 (ms_mem ms3) md3 a HLN HMS HAR3 Hin Jfa
                     Bmdt Bmkt Bmd4 Bmk4 HPB Hlo ltac:(clia) Ha)
      Hnm Hrc Hsv Hhd Hfsh Hsl Hcur Hjbk Hblk Hdatn)
      as (Hsv2 & Hhd2 & Hfsh2 & Hsl2 & Hcur2 & Hblk2 & HRO2 & HNUL & HENV & HPL2 & HPV2 & _ & _ & kbs' & gbs' & Hmrc
          & Hkwf2 & Hdat2f).
    assert (Hfa2 : forall c q, frame_addr ly2 c q = frame_addr (c_ly cx) c q)
      by (intros c q; exact (proj1 (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c q HJ2))).
    assert (Hjbk2 : lf_jbk B MT MS la_nul cx fp (k2 + 1) (lf_ev (i + 1)) (lf_mo LF_MO_SET LF_MO_OP (i + 1))
                      (lf_wl (i + 1)) LF_LIVE_HELD ly2 S2 W2 ms2 md2 [(sink, AMF_BLOCK)] [(md, MD_SIZE); (mk, MK_SIZE)]).
    { apply (lf_jbk_open B MT MS la_nul MT_LE cx fp k2 _ _ _ ly3 S3 W3 ms3 md3 ly2 S2 W2 ms2 md2 md mk sink (k2 + 1)
        _ _ _ Hjbk Hfa2).
      - unfold lf_ev, LF_EV_OP in *. lia.
      - unfold lf_wl, LF_WILD_OP. lia.
      - exact Hled.
      - exact Hperm.
      - exact Hfd.
      - exact Hfs.
      - exact (mqp_heads_of_au64 MS _ sink HMS Hgs Hgy Hgo).
      - rewrite HMS. exact (proj1 Hmf).
      - exact HENV.
      - exact HNUL.
      - exact HRO2.
      - exact HPL2.
      - exact HPV2. }
    apply (o2q_after POST i cx fx' fp (k2 + 1) ly2 S2 W2 (ms_regs ms3) regs2 mem2 md2 md mk P N kbs kbs' mbs gbs gbs'
      [(sink, AMF_BLOCK)] nm ms3 Hi NEXT HB (fxr_trans fx fy fx' Hfx Hfxr) HJ2 ltac:(rewrite Hfr2; exact Hfr) eq_refl
      Hcore Hyr R23 R1 Hpr Ha0 Bmk0 Hmrc Hkwf2 Hdat2f Hrq Hmm Hnwf Hmwf Hns Hop Hsv2 Hhd2 Hfsh2 Hsl2 Hcur2 Hjbk2
      (lf_blocks_open B cx md mk ly3 S3 ly2 S2 sink _ Hperm Hblk2)).
  - (* a later call *)
    destruct Jgi as [(_ & HT) | (f' & Hhf & HT & Hamf)]; [discriminate HT|]. injection HT as <-.
    assert (Hfin : In (f, AMF_BLOCK) (ablocks B ly3 S3)) by (apply Jinc; left; reflexivity).
    destruct (blk_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 f AMF_BLOCK HAR3 Hfin) as [Hoff | Hoff];
      change (req_size AMF_BLOCK) with AMF_BLOCK in Hoff; unfold YImgTop.IMG_LO in Hoff.
    all: assert (Hfoff : f + AMF_BLOCK <= 0x10000 \/ YImgTop.IMG_TOP <= f) by lia.
    all: destruct (al_blocks _ _ LAWS _ _ _ _ _ f AMF_BLOCK HAR3 Hfin) as (_ & Hf4 & _).
    all: destruct (o2q_names ly3 S3 W3 (ms_mem ms3) md3 (ms_regs ms3) s nm mk f AMF_BLOCK HLN HMS HAR3 HRO Hgn HKc Bmkt
      Ha0 Ha1 Hw Hfoff ltac:(unfold AMF_BLOCK; lia)) as (Hnm & Hnok & Hnlo & _ & Hnakb).
    all: eapply apostF_continue;
      [ rewrite HMS in Hhf, Hamf;
        exact (lf_mq_again_call SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS MQA
          fy cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 (ms_regs ms3) md mk kbs mbs gbs (AFL + 0xcac) nm f HB HJ Hfr Hfrm
          ltac:(lia) Jbl Jinc HRO Hblk Hdatn Hhf Hamf Hop2 H8 H16' Hsp Hs0 C3 C4 (lv_text LV) R1' Hsite Ha0' Hnm Hnok Hnlo
          ltac:(rewrite Hsp in Hnakb; rewrite Hsp; exact Hnakb)) |].
    all: intros fx' W2 c2 Hle Hfxr Hpost.
    all: destruct Hpost as (ly2 & S2 & regs2 & mem2 & md2 & Hc2 & HJ2 & Hpr & Hfr2 & Hfd & Hfs & Hkp & Hsk & (Hs2 & Hperm & Hpa)).
    all: subst c2.
    all: destruct Hpa as (Hgs & Hgy & Hgo & (kq & Hkq & Hmf) & Hrc).
    all: set (ms2 := @mkst fx' regs2 (getr (ms_regs ms3) 1) mem2 (seg_rom SEGS)).
    all: change (SRr SEGS W2 (mkCfg ms2 md2) (POST cx)).
    all: assert (Pmd2 : In (md, MD_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Bmd).
    all: assert (Pmk2 : In (mk, MK_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Bmk).
    all: rewrite Hsp in Hkp.
    all: assert (Hfnz : f <> 0) by lia.
    all: assert (HPBf : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3) /\ (c_p cx, c_n cx) <> (f, AMF_BLOCK))
      by (intros Hn; split; [exact (HPB Hn) | exact (o5m_input_ne_file SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET
            LF_MO_OP LF_MO_END LAWS cx _ f ly3 S3 W3 (ms_mem ms3) md3 HB HAR3 Jbl Hn)]).
    all: destruct (lf_mq_post_common SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS
      cx fp k2 _ _ _ _ md mk kbs mbs gbs [(f, AMF_BLOCK)] _ P N ly3 S3 W3 ms3 md3 ly2 S2 W2 ms2 md2 (k2 + 0) (ms_regs ms3)
      regs2 _ (fun a => LA_G_SAID <= a < LA_G_SAID + SAID_SIZE \/ f <= a < f + AMF_BLOCK) nm
      HB Hfr HJ HJ2 Hsp Hkp Hsk Pmd2 Pmk2 Ha0'
      (fun a Ha => o5m_E_again (ms_regs ms3) _ mk f a Bmk0 Hfnz Ha0' Ha)
      (fun a Ha => match Ha with
                   | or_introl Hs => o5m_Fopen_miss B MS la_nul LAWS HSEGS cx fp md mk ly3 S3 W3 (ms_mem ms3) md3 a HLN
                                       HMS HAR3 Hin Jfa Bmdt Bmkt Bmd4 Bmk4 HPB Hlo ltac:(clia) (or_intror (or_introl Hs))
                   | or_intror Hb => o5m_Fblk_miss B MS la_nul LAWS TB HSEGS cx fp md mk f ly3 S3 W3 (ms_mem ms3) md3 a
                                       HLN HMS HAR3 Hin Jfa Bmd Bmk Hfin HPBf Hlo Hb
                   end)
      Hnm Hrc Hsv Hhd Hfsh Hsl Hcur Hjbk Hblk Hdatn)
      as (Hsv2 & Hhd2 & Hfsh2 & Hsl2 & Hcur2 & Hblk2 & HRO2 & HNUL & HENV & HPL2 & HPV2 & _ & _ & kbs' & gbs' & Hmrc
          & Hkwf2 & Hdat2f).
    all: assert (Hfa2 : forall c q, frame_addr ly2 c q = frame_addr (c_ly cx) c q)
      by (intros c q; exact (proj1 (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c q HJ2))).
    all: assert (Hjbk2 : lf_jbk B MT MS la_nul cx fp (k2 + 0) (lf_ev (i + 1)) (lf_mo LF_MO_SET LF_MO_OP (i + 1))
                      (lf_wl (i + 1)) LF_LIVE_HELD ly2 S2 W2 ms2 md2 [(f, AMF_BLOCK)] [(md, MD_SIZE); (mk, MK_SIZE)]).
    all: try (apply (lf_jbk_again B MT MS la_nul MT_LE cx fp k2 (lf_ev (i + 1)) (lf_mo LF_MO_SET LF_MO_OP (i + 1))
        (lf_wl (i + 1)) LF_LIVE_HELD ly3 S3 W3 ms3 md3 ly2 S2 W2 ms2 md2 _ f (k2 + 0));
        [ exact (o5m_jbk_next B MT MS la_nul LF_MO_SET LF_MO_OP MT_LE cx fp k2 i ly3 S3 W3 ms3 md3 _ _ ltac:(lia) Hjbk)
        | exact Hfa2 | unfold lf_ev, LF_EV_OP in *; lia | exact Hs2 | exact Hperm | exact Hfd | exact Hfs
        | exact (mqp_heads_of_au64 MS _ f HMS Hgs Hgy Hgo) | rewrite HMS; exact (proj1 Hmf) | exact HENV | exact HNUL
        | exact HRO2 | exact HPL2 | exact HPV2 ]).
    all: apply (o2q_after POST i cx fx' fp (k2 + 0) ly2 S2 W2 (ms_regs ms3) regs2 mem2 md2 md mk P N kbs kbs' mbs gbs gbs'
      [(f, AMF_BLOCK)] nm ms3 Hi NEXT HB (fxr_trans fx fy fx' Hfx Hfxr) HJ2 ltac:(rewrite Hfr2; exact Hfr) eq_refl
      Hcore Hyr R23 R1 Hpr Ha0 Bmk0 Hmrc Hkwf2 Hdat2f Hrq Hmm Hnwf Hmwf Hns Hop Hsv2 Hhd2 Hfsh2 Hsl2 Hcur2 Hjbk2
      (ar_blocks_leaf B cx md mk _ ly3 S3 ly2 S2 _ Hperm Hblk2)).
Qed.

(* +0xc9c `ld s5, 0x90(s1)`, `mv a0, s5`, `mv a1, s4`, `jal mark_quietly` (0x8347c), then o2q_call *)
Lemma o2_qm : forall POST i,
  FROM POST (YCAC i) -> FROM POST (o2_q_inv B MT MS la_nul LF_MO_SET LF_MO_OP i).
Proof.
  intros POST i NEXT cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HQ.
  destruct HQ as (md & mk & P & N & s & nm & kbs & mbs & gbs & T3 & Hsh & R20 & Hw & R22 & R26 & HM & R23 & Hrq & Hmm).
  pose proof HM as (Hi & Hcore & Hkr & Hsv & Hhd & Hfs & Hsl & Hcur & Hjbk & Hblk & Hdatn & Hop & Hns).
  pose proof Hkr as (R19 & R24 & R25 & R27).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof HB as (_ & _ & HGX & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof alloc_ceiling_lt as CL.
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & H16 & Hlo & H47).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (_ & _ & _ & _ & _ & _ & HAR3).
  pose proof Hblk as (Bmd & Bmk & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ mk MK_SIZE HAR3 Bmk) as (_ & Hk4 & Hkc & _).
  change (req_size MK_SIZE) with 516 in Hkc.
  pose proof Hsl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SMK & _).
  pose proof (o2q_s_range s nm Hw) as Hsr.
  set (E := Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 mk])) in *.
  assert (EL : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
  { intros n r Hn Hr. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat _ _ n r Hr). }
  assert (E32 : ew E 32 = Z_to_bv 64 mk).
  { unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra _ [Z_to_bv 64 mk] 0). }
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_sp1 cx)) by (rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl); exact R9).
  assert (HS : st_ok_pi (fx := fy) SEGS pa_val E o2q_ss
    (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LO2_q)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold o2q_ss. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold o2q_rg. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E9, unsigned_lit_small by (unfold LLVMF_STK in *; clia).
      split; [unfold LLVMF_STK in *; clia|]. split; [unfold LLVMF_STK in *; clia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (u_slot_chunk E cx W3 ms3 0x90 _ mk); [|exact SMK].
      rewrite (lf_sv_off E 32 mk 0 E32) by clia. rewrite Z.add_0_r. reflexivity.
    - apply pairwise_disjoint_of_extents. unfold o2q_rg, extent_of_region. cbn [map].
      cbn [zpairwise_disjoint zall_disjoint]. tauto.
    - split; [|split; exact I]. exact I. }
  rewrite (lf_shape_eta fy LO2_q ms3 Hsh).
  assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] E
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LO2_q)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  paj_run_tok RUN HS HJ SHOK (0, 0); [apply ar_awr_nowin; vm_compute; reflexivity|].
  rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
  pose proof (ar_kagree_nowin _ _ _ _ HFrB ltac:(vm_compute; reflexivity)) as KB.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
  assert (Fd : m_fds md4 = m_fds md3) by (subst md4; rewrite !lf_wvb_fds; reflexivity).
  assert (Fs : m_fs md4 = m_fs md3) by (subst md4; rewrite !lf_wvb_fs; reflexivity).
  lazymatch type of HS with st_ok _ _ (setpc ?ssx _) _ => set (ssB := ssx) in HS end.
  assert (KR : forall r : bv 5, sr_get (ss_regs ssB) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
    getr (ms_regs msB) r = getr (ms_regs ms3) r).
  { intros r Hr. rewrite (st_ok_restrict_reg SEGS (w_H W3) _ _ msB r HS). cbn [setpc ss_regs].
    rewrite Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
    pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
    apply EL; [lia | rewrite Z2Nat.id by lia; reflexivity]. }
  assert (R1 : getr (ms_regs msB) 1 = Z_to_bv 64 (BASE + (AFL + 0xcac))).
  { rewrite (st_ok_restrict_reg SEGS (w_H W3) _ _ msB 1%bv HS). cbn [setpc ss_regs]. subst ssB.
    change (sr_get _ 1%bv) with (SOff A_TEXT 4788). rewrite (codeptr_val _ 4788 HEI). reflexivity. }
  assert (R10 : getr (ms_regs msB) 10 = w64 mk).
  { rewrite (st_ok_restrict_reg SEGS (w_H W3) _ _ msB 10%bv HS). cbn [setpc ss_regs]. subst ssB.
    change (sr_get _ 10%bv) with (SOff 32 0). rewrite (lf_sv_off E 32 mk 0 E32) by clia. rewrite Z.add_0_r.
    reflexivity. }
  assert (R21 : getr (ms_regs msB) 21 = w64 mk).
  { rewrite (st_ok_restrict_reg SEGS (w_H W3) _ _ msB 21%bv HS). cbn [setpc ss_regs]. subst ssB.
    change (sr_get _ 21%bv) with (SOff 32 0). rewrite (lf_sv_off E 32 mk 0 E32) by clia. rewrite Z.add_0_r.
    reflexivity. }
  assert (R11 : getr (ms_regs msB) 11 = getr (ms_regs ms3) 20).
  { rewrite (st_ok_restrict_reg SEGS (w_H W3) _ _ msB 11%bv HS). cbn [setpc ss_regs]. subst ssB.
    change (sr_get _ 11%bv) with (SOff 20 0). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
    exact (EL 20%nat 20%bv ltac:(lia) eq_refl). }
  pose proof (st_ok_restrict_mkst SEGS (w_H W3) _ _ msB HS eq_refl) as Hms. cbn [setpc ss_pc] in Hms.
  rewrite pa_sigma_mark_quietly, (lv_text LV) in Hms.
  assert (EA : link_text + AF_mark_quietly = MARK_QUIETLY_A) by reflexivity. rewrite EA in Hms.
  apply (o2q_call POST i cx fy fp k2 ly3 S3 W3 msB md4 md mk P N kbs mbs gbs T3 s nm Hi NEXT HB Hfx HJ Hfr Hms).
  - unfold lf_core. rewrite (KR 2%bv eq_refl), (KR 8%bv eq_refl), (KR 9%bv eq_refl), (KR 3%bv eq_refl),
      (KR 4%bv eq_refl). exact Hcore.
  - unfold o2_yregs. rewrite (KR 19%bv eq_refl), R21, (KR 22%bv eq_refl), (KR 24%bv eq_refl), (KR 25%bv eq_refl),
      (KR 26%bv eq_refl), (KR 27%bv eq_refl).
    repeat split; assumption.
  - rewrite (KR 23%bv eq_refl). exact R23.
  - exact R1.
  - rewrite ar_aarg0, R10. unfold w64. apply unsigned_lit_small. clia.
  - rewrite ar_aarg1, R11, R20. unfold w64. apply unsigned_lit_small. clia.
  - exact Hw.
  - exact (lf_saved_keep _ cx W3 ms3 W3 msB KB (fun a _ H => H) Hsv).
  - exact (lf_header_keep _ cx fp W3 ms3 W3 msB KB (fun a _ H => H) Hhd).
  - exact (lf_fshadow_keep _ cx fp W3 ms3 W3 msB LF_SH0 KB (fun a _ H => H) Hfs).
  - exact (lf_slots_keep _ cx md mk fp W3 ms3 W3 msB KB (fun a _ H => H) Hsl).
  - exact (lf_cur_keep _ cx W3 ms3 W3 msB P N KB (fun a _ H => H) Hcur).
  - exact (lf_jbk_keep B MT MS la_nul _ cx fp k2 _ _ _ _ ly3 S3 W3 ms3 md3 T3 _ W3 msB md4 KB Fd Fs
      (fun a _ H => H) Hjbk).
  - exact (lf_blocks_keep B _ _ _ cx md mk T3 ly3 S3 KB (fun a _ H => H) Hblk).
  - exact (lf_data_nm_keep _ _ _ cx md mk kbs mbs gbs KB (wcarry_on_grows _ _ _ HGB) (fun a _ H => H) Hdatn).
  - exact Hrq.
  - exact Hmm.
  - exact Hns.
  - lia.
Qed.

End b.
End a.

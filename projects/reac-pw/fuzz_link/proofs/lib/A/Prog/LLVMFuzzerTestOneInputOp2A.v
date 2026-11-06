(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module names changed; 703 of its 756 lines of code are new or changed and 1279 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...), the op_mark arm:
   the append of the inlined `remember` (+0x11c0 .. +0x11fc; listing image-A
   (internal path) (internal record, sha256 e84d6f0c6974)).

     +0x11c0 .. +0x11c4  the instrumented check of m->n_mark (s6 = its shadow byte; the SH entry of the model block)
     +0x11c8 .. +0x11d4  m->n_mark := n + 1
     +0x11d8 .. +0x11f0  snprintf(m + MD_MARK + 16 n, 16, .str.21 "%s", name) (the wrapper at 0x839c4: lib/A/Rt/
                         LinkSnpDef.v asnprintf_link_realizes, the Section hypothesis SNP in its exact shape, applied
                         by LLVMFuzzerTestOneInputSnp.v lf_snp_step; the post is apostF, the arm goes on at its fx')
     +0x11f4 .. +0x11fc  s10 := F + 0x20, s6 := m (the spill slots), -> +0xc0c (o2_u_inv)

   The model after it is Op2Ml.v o2l_mbs2 mbs n t: the count n + 1 and slot n holding t; its marks are
   remember (md_marks mbs) t = md_marks mbs ++ [t] (Op2Ml.v o2l_rem_new, o2l_marks2).

   o2_ap : forall POST i, FROM POST (o2_u_inv i) -> FROM POST (o2_a_inv i).

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
  LLVMFuzzerTestOneInputKpost LLVMFuzzerTestOneInputMb LLVMFuzzerTestOneInputMdl LLVMFuzzerTestOneInputOp3K
  LLVMFuzzerTestOneInputArmK.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_read_c model_write_c model_decide_c index_of_c LinkWalkBcmp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputSel LLVMFuzzerTestOneInputMq
  LLVMFuzzerTestOneInputOp2Lib LLVMFuzzerTestOneInputOp2Cut LLVMFuzzerTestOneInputOp2Nm LLVMFuzzerTestOneInputOp5
  LLVMFuzzerTestOneInputOp3B LLVMFuzzerTestOneInputOp3C LLVMFuzzerTestOneInputOp2R LLVMFuzzerTestOneInputDec
  LLVMFuzzerTestOneInputOp3Lib LLVMFuzzerTestOneInputOp3W LLVMFuzzerTestOneInputOp2D LLVMFuzzerTestOneInputOp2Nm
  LLVMFuzzerTestOneInputOp2V LLVMFuzzerTestOneInputOp2Ml.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import PfFacts SnShared SnFF.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkPfPiece LinkSnpDef LinkSnpJ.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputSnp rememberPost
  LLVMFuzzerTestOneInputOp2M LLVMFuzzerTestOneInputOp2X LinkWalkStrArg rememberCalls LLVMFuzzerTestOneInputOp2L
  LLVMFuzzerTestOneInputOp3K LLVMFuzzerTestOneInputOp3X.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Mem.
Import ListNotations.
(* the closure redefines lia with a hypothesis pruning that misses chains through a variable not in the goal *)
Ltac olia := Zify.zify; xlia zchecker.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Definition LO2_f : Z := AF_LLVMFuzzerTestOneInput + 0x11f4.   (* 0x839c8, snprintf's return *)
(* the runner's state at +0x11c0: s6 is the shadow byte of m->n_mark (atom 32 = m), the two spill slots the append
   reads, and the count word it writes *)
Definition o2a_shx : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 8852) (SLit 3)) (SOff 27 0).
Definition o2a_fr : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x58 0xa0 0x58 0x58 [o2m_c8 0x58 (SOff 32 8340); o2m_c8 0x98 (SOff 32 8852)].
Definition o2a_cnt : YP09.region := YP09.mkRegion (Some 32%nat) 8852 8856 8852 8856 [].
Definition o2a_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF 4096 (2 ^ 47 - 8856) 4);
           (27%nat, mkAF o5_RSB o5_RSB 0); (21%nat, mkAF 0 31 0)] [] [].
Definition o2a_ss : sstate := mkSS LO2_a (sr_set sr_atoms 22%bv o2a_shx) [o2a_fr; o2a_cnt] None o2a_facts.
Definition o2a_SH : list shent := [mkSHE 32 0 8856].


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
Hypothesis SNP : forall fy : YK11.FPState,
  @asnprintf_link_realizes fy rc pa_segs B PCAP_RLO PCAP_RHI LA_W_SNPRINTF.

Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).
#[local] Abbreviation BASEF cx := (@lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Abbreviation JRN cx fp ly S W mem md k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
     (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem md k).

Lemma o2a_model_after : forall cx fp K ly3 S3 ly2 S2 (W3 : world SEGS) ms3 md3 (W2 : world SEGS) ms2 md2 (E : Z -> Prop)
    k2 ev mo wl lv md mk kbs mbs gbs mbs' T3 own P N sh,
  BASEF cx -> JRN cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 -> frames S3 = [(LF_CID, fp)] ->
  lf_call B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E ->
  (forall a, E a -> (md <= a < md + MD_SIZE) \/ (lf_F cx fp + 24 <= a < lf_F cx fp + 1016)) ->
  m_fds md2 = m_fds md3 -> m_fs md2 = m_fs md3 ->
  In (md, MD_SIZE) (ablocks B ly2 S2) -> In (mk, MK_SIZE) (ablocks B ly2 S2) ->
  wcarry_on (rdW W3 (ms_mem ms3)) (rdW W2 (ms_mem ms2)) (lf_data_fp_w md mk) ->
  (length sh <= 128)%nat ->
  lf_saved cx W3 ms3 -> lf_header cx fp W3 ms3 -> lf_fshadow cx fp W3 ms3 sh -> lf_slots cx md mk fp W3 ms3 ->
  lf_cur cx W3 ms3 P N ->
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own ->
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) ->
  lf_data cx md mk kbs mbs gbs (rdW W3 (ms_mem ms3)) ->
  amodel_at SEGS (rdW W2 (ms_mem ms2)) md mbs' -> model_wf mbs' ->
  lf_saved cx W2 ms2 /\ lf_header cx fp W2 ms2 /\ lf_fshadow cx fp W2 ms2 sh /\ lf_slots cx md mk fp W2 ms2 /\
  lf_cur cx W2 ms2 P N /\
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W2 ms2 md2 T3 own /\
  lf_blocks B cx md mk T3 ly3 S3 (rdW W2 (ms_mem ms2)) /\
  lf_data_nm cx md mk kbs mbs' gbs (rdW W2 (ms_mem ms2)) /\
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) (ms_mem ms2)).
Proof.
  intros cx fp K ly3 S3 ly2 S2 W3 ms3 md3 W2 ms2 md2 E k2 ev mo wl lv md mk kbs mbs gbs mbs' T3 own P N sh
    HB HJ Hfr LC HE Fd Fs Pmd Pmk WC Hshl Hsv Hhd Hfsh Hsl Hcur Hjbk Hblk Hdat Hmd' Hmwf'.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as (HPRE & _ & HGX & HLN & HMS & _).
  destruct (lf_img_facts B MS la_nul HSEGS TB HMS HLN) as (IMG & RIMG).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & H16 & Hlo & H47).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (_ & _ & _ & _ & _ & _ & HAR3).
  destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
    cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ Hfr)
    as (HFa & F32 & F4 & Fc & Fapp & Fpres & Fshp & Fsep).
  pose proof Hjbk as (_ & _ & Hfa & _ & _ & _ & _ & _ & Hgi & _ & _ & Hinc & Hnul & HRO & _).
  pose proof Hblk as (Bmd & Bmk & Bmc & Bkc & BmT & BkT & Bm16 & Bk16 & Bmt & Bkt & Bap & Bpl & Bpk & _).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 md MD_SIZE HAR3 Bmd) as (_ & Bm4 & Bmceil & _).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 mk MK_SIZE HAR3 Bmk) as (_ & Bk4 & Bkceil & _).
  change (req_size MD_SIZE) with 8856 in Bmceil. change (req_size MK_SIZE) with 516 in Bkceil.
  assert (Hin : In (LF_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
  pose proof (Fsep md MD_SIZE Bmd) as DmF. pose proof (Fsep mk MK_SIZE Bmk) as DkF.
  unfold zdisjoint in DmF, DkF. cbn [fst snd] in DmF, DkF. change (req_size MD_SIZE) with 8856 in DmF.
  change (req_size MK_SIZE) with 516 in DkF.
  pose proof (lf_call_kagree B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E LC) as KG.
  pose proof LC as (HK0 & HKc & _).
  assert (HFS : lf_SH cx fp = SHADOW_OFF + lf_F cx fp / 8) by reflexivity.
  assert (SHB : kLowMemEnd + 512 <= lf_SH cx fp /\ lf_SH cx fp + 128 <= kHighMemBeg).
  { rewrite HFS. assert (D1 : 4096 / 8 <= lf_F cx fp / 8) by (apply Z.div_le_mono; lia).
    assert (D2 : lf_F cx fp / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
    change (4096 / 8) with 512 in D1. change (0x7fffff800000 / 8) with 0xffffff00000 in D2.
    unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg. lia. }
  (* E misses everything but the model block and the frame's body *)
  assert (EImg : forall a, E a -> ~ in_img SEGS a).
  { intros a Ha Hi. destruct (HE a Ha) as [H | H].
    - apply (al_client_img _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 a HAR3); [|exact Hi]. left. exists md, MD_SIZE.
      split; [exact Bmd|]. change (req_size MD_SIZE) with 8856. unfold MD_SIZE in H. lia.
    - exact (proj2 (Fpres a ltac:(lia)) Hi). }
  assert (ERo : forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> ~ E a).
  { intros a Hro Ha. apply (EImg a Ha). destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr]|].
    exact (RIMG a Hr). }
  assert (EHi : forall a, E a -> a < alloc_ceiling) by (intros a Ha; destruct (HE a Ha); unfold MD_SIZE in *; lia).
  assert (ESh : forall a, lf_SH cx fp <= a < lf_SH cx fp + 128 -> ~ E a).
  { intros a Ha HEa. destruct (HE a HEa) as [H | H].
    - unfold amem_range in *. pose proof Hblk as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Bamm & _).
      unfold amem_range, MD_SIZE, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
    - unfold in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, ASAN_CEIL in *. lia. }
  assert (EImgfp : forall a, lf_img_fp MS la_nul a -> ~ E a) by (intros a Ha HEa; exact (EImg a HEa (proj1 (IMG a Ha)))).
  set (LXE := lf_X B ly3 S3 ly2 S2 (lf_sp1 cx - K) (lf_sp1 cx) E) in *.
  assert (NImg : forall a, lf_img_fp MS la_nul a -> ~ LXE a)
    by (intros a Ha; exact (lfx_imgfp B MS la_nul ly3 S3 ly2 S2 _ _ E a IMG Ha (EImgfp a Ha))).
  assert (NSide : forall a, (lf_F cx fp <= a < lf_F cx fp + 24 \/ lf_F cx fp + 1016 <= a < lf_F cx fp + 1024 \/
     lf_SH cx fp <= a < lf_SH cx fp + 128) -> ~ LXE a).
  { intros a Ha. apply (lfx_side B cx fp K ly3 S3 ly2 S2 E a Hin Hfa).
    - destruct Ha as [Ha | [Ha | Ha]]; [left; lia | left; lia | right; exact Ha].
    - intros HEa. destruct Ha as [Ha | [Ha | Ha]].
      + destruct (HE a HEa) as [H | H]; [unfold MD_SIZE in *; lia | lia].
      + destruct (HE a HEa) as [H | H]; [unfold MD_SIZE in *; lia | lia].
      + exact (ESh a Ha HEa). }
  assert (NBlkE : forall b m a, In (b, m) (ablocks B ly3 S3) -> b <= a < b + m -> (b, m) <> (md, MD_SIZE) -> ~ E a).
  { intros b m a Hbm Ha Hne HEa.
    destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 b m HAR3 Hbm) as (_ & _ & _ & _ & _ & _ & Hm).
    assert (Rm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
    destruct (HE a HEa) as [H | H].
    - pose proof (sep_blocks _ _ LAWS _ _ _ _ _ b m md MD_SIZE HAR3 Hbm Bmd Hne) as D. unfold zdisjoint in D.
      cbn [fst snd] in D. change (req_size MD_SIZE) with 8856 in D. unfold MD_SIZE in H. lia.
    - pose proof (Fsep b m Hbm) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia. }
  assert (NBlk : forall b m a, In (b, m) (ablocks B ly3 S3) -> b <= a < b + m -> (b, m) <> (md, MD_SIZE) -> ~ LXE a)
    by (intros b m a Hbm Ha Hne; exact (lfx_blk B ly3 S3 ly2 S2 _ _ E b m a Hbm Ha (NBlkE b m a Hbm Ha Hne))).
  assert (Hmkmd : (mk, MK_SIZE) <> (md, MD_SIZE)) by (intros Hq; injection Hq as _ Hq; discriminate).
  (* the pieces (Mdl.v lf_model_after, but the marks: the model may have remembered a name) *)
  assert (Hsv2 : lf_saved cx W2 ms2).
  { apply (lf_saved_callee B cx K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E LC); [|exact Hsv].
    intros a Ha HEa. unfold lf_saved_fp in Ha. pose proof (EHi a HEa). unfold LLVMF_STK in *. lia. }
  assert (Hsl2 : lf_slots cx md mk fp W2 ms2).
  { apply (lf_slots_callee B cx K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E md mk fp LC); [|exact Hsl].
    intros a Ha HEa. unfold lf_slots_fp in Ha. pose proof (EHi a HEa). unfold LLVMF_STK in *. lia. }
  assert (Hcur2 : lf_cur cx W2 ms2 P N).
  { apply (lf_cur_callee B cx K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E P N LC); [|exact Hcur].
    intros a Ha HEa. unfold lf_cur_fp in Ha. pose proof (EHi a HEa). unfold LLVMF_STK in *. lia. }
  assert (Hhd2 : lf_header cx fp W2 ms2).
  { apply (lf_header_callee B cx fp K ly3 S3 ly2 S2 W3 ms3 W2 ms2 E LC Hin Hfa); [|exact Hhd].
    intros a Ha HEa. unfold lf_header_fp in Ha. change (fs_frame_bytes LF_CID) with 1024 in Ha.
    destruct (HE a HEa) as [H | H]; [unfold MD_SIZE in *; lia | lia]. }
  assert (Hfsh2 : lf_fshadow cx fp W2 ms2 sh).
  { apply (lf_fshadow_keep LXE cx fp W3 ms3 W2 ms2 sh KG); [|exact Hfsh].
    intros a Ha. apply NSide. right; right. unfold lf_fshadow_fp in Ha. lia. }
  assert (Hblk2 : lf_blocks B cx md mk T3 ly3 S3 (rdW W2 (ms_mem ms2)))
    by exact (lf_blocks_callee B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E md mk T3 LC Pmd Pmk Hblk).
  assert (HRO2 : arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) (ms_mem ms2)))
    by exact (lf_aro_callee B cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E RIMG LC ERo HRO).
  assert (HNUL2 : val_mem SEGS (rdW W2 (ms_mem ms2)) la_nul 1 0).
  { apply (lf_la_nul_callee B MS la_nul cx K ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2) E IMG LC); [|exact Hnul].
    apply EImgfp. right; right; right; right; right; left. lia. }
  assert (HPB : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by (intros Hn; exact (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
          cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ Hn)).
  assert (Hjbk2 : lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W2 ms2 md2 T3 own).
  { apply (lf_jbk_callee B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own K ly2 S2 W2 ms2 md2 E
      IMG RIMG LC); [| exact ERo | exact HPB | exact Fd | exact Fs | exact HNUL2 | exact Hjbk].
    intros a Ha HEa. destruct Ha as [Ha | Ha].
    - destruct Ha as [Ha | [Ha | (f & n & Hfn & Ha)]].
      + exact (EImgfp a ltac:(right; right; right; left; exact Ha) HEa).
      + exact (EImgfp a ltac:(right; right; right; right; left; exact Ha) HEa).
      + assert (HfnT : In (f, n) (ablocks B ly3 S3)) by exact (Hinc _ Hfn).
        assert (Hn : n = AMF_BLOCK).
        { destruct Hgi as [(_ & HT) | (f' & _ & HT & _)]; rewrite HT in Hfn; [destruct Hfn|].
          destruct Hfn as [Hq | []]. injection Hq as _ <-. reflexivity. }
        subst n.
        assert (Hne : (f, AMF_BLOCK) <> (md, MD_SIZE)) by (intros Hq; rewrite Hq in Hfn; exact (BmT Hfn)).
        exact (NBlkE f AMF_BLOCK a HfnT ltac:(unfold AMF_BLOCK in *; lia) Hne HEa).
    - assert (Hn : 0 < c_n cx) by lia.
      assert (Hne : (c_p cx, c_n cx) <> (md, MD_SIZE)) by (intros Hq; apply Bmc; rewrite <- Hq; destruct HPRE as (_ & _ & _ & _ & Hpn & _); destruct Hpn as [(Hn0 & _) | (_ & Hin0)]; [lia | exact Hin0]).
      exact (NBlkE _ _ a (HPB Hn) Ha Hne HEa). }
  (* lf_data at the model the callee left *)
  pose proof Hdat as Hdat0.
  destruct Hdat as (Dk & Dwf & Dtab & Dop & Dmis & Doc & Dmd & Dmwf & Dmk & Dkwf & (Dmn & Dmm) & Difp & Dgn & Dgw & Dodd
    & Dtx & Dla).
  assert (WB : forall a n, (forall i, 0 <= i < n -> lf_data_fp_w md mk (a + i)) ->
    wcarry SEGS (rdW W3 (ms_mem ms3)) (rdW W2 (ms_mem ms2)) a n)
    by (intros a n Hf; exact (wcarry_on_sub _ _ _ a n WC Hf)).
  assert (NImgR : forall a lo n, lo <= a < lo + n -> (forall x, lo <= x < lo + n -> lf_img_fp MS la_nul x) -> ~ LXE a)
    by (intros a lo n Ha Hf; exact (NImg a (Hf a Ha))).
  destruct (lf_odd_texts_of_ro B TB HSEGS W2 (ms_mem ms2) HRO2) as (Hodd2 & Htx2).
  assert (Hdat2 : lf_data_nm cx md mk kbs mbs' gbs (rdW W2 (ms_mem ms2))).
  { refine (conj _ (conj Dwf (conj _ (conj Dop (conj Dmis (conj Doc (conj Hmd' (conj Hmwf' (conj _ (conj Dkwf
      (conj _ (conj _ (conj _ (conj Hodd2 (conj Htx2 _))))))))))))))).
    - apply (anlk_keep _ LXE _ _ LA_G_NL kbs KG); [| |exact Dk].
      + apply WB. intros i Hi. left. lia.
      + intros i Hi. apply NImg. left. lia.
    - apply (aiftab_keep _ LXE _ _ LA_G_NL kbs lf_tab KG); [| | |exact Dtab].
      + intros i Hi kk Hk. apply NImg. left. unfold NK_IF_NAME, NK_SIZE. lia.
      + intros i Hi kk Hk. apply NImg. left. unfold NK_IF_INDEX, NK_SIZE. lia.
      + intros i nm ix p Hn Hp Hs jj Hjj.
        assert (Rp : 0 <= p < 2 ^ 64) by (destruct Hs as ((A1 & A2 & _) & _); rewrite length_app in A2;
          cbn [length] in A2; lia).
        destruct (lf_tab_core SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
          cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 md mk kbs mbs gbs HB HJ HRO Hdat0 i nm ix p Hn Hp Rp)
          as (_ & _ & _ & _ & _ & _ & _ & C7).
        destruct (C7 (p + jj) ltac:(lia)) as (I1 & I2 & I3).
        exact (lfx_img B ly3 S3 ly2 S2 _ _ E (p + jj) I1 I2 I3 (fun HEa => EImg _ HEa I1)).
    - apply (amarks_keep _ LXE _ _ mk gbs KG); [| |exact Dmk].
      + apply WB. intros i Hi. right; right; right; right. unfold MK_SIZE in *. lia.
      + intros i Hi. apply (NBlk mk MK_SIZE (mk + i) Bmk); [lia | exact Hmkmd].
    - apply (lf_ifp_keep_ro LXE _ _ 64 KG); [lia | | |exact Difp].
      + intros a Ha. apply NImg. left. exact Ha.
      + intros a Ha. apply NImg. right; right; right; right; right; right. exact Ha.
    - apply (lf_gnames_at_keep LXE _ _ 64 KG); [lia | |exact Dgn].
      intros a Ha. apply NImg. right; left. exact Ha.
    - apply (lf_gnames_w_keep LXE _ _ KG); [| |exact Dgw].
      + apply WB. intros i Hi. right; left. unfold G_NAMES_SIZE in *. lia.
      + intros a Ha. apply NImg. right; left. exact Ha.
    - apply (lf_la_at_keep_ns LXE _ _ KG); [| | exact (lf_la_slack_any HSEGS _) | exact Dla].
      + apply WB. intros i Hi. right; right; left. lia.
      + intros a Ha. apply NImg. right; right; left. exact Ha. }
  refine (conj Hsv2 (conj Hhd2 (conj Hfsh2 (conj Hsl2 (conj Hcur2 (conj Hjbk2 (conj Hblk2 (conj Hdat2 HRO2)))))))).
Qed.

(* the entry registers: s6 the shadow address of m->n_mark *)
Lemma o2a_regs_ok : forall (E : env) (regs : bvmap 5 word), regs_ok E sr_atoms regs ->
  sv_denot E o2a_shx = getr regs 22%bv -> regs_ok E (sr_set sr_atoms 22%bv o2a_shx) regs.
Proof.
  intros E regs HR H22 r. destruct (Z.eq_dec (bv_unsigned r) 22) as [Hq | Hne].
  - assert (Hr : r = 22%bv) by (apply bv_eq; rewrite Hq; reflexivity). subst r.
    rewrite sr_get_set_same by reflexivity. symmetry. exact H22.
  - rewrite sr_get_set_other by (intros Hr; apply Hne; rewrite Hr; reflexivity). apply HR.
Qed.

(* the destination the append computes: m + MD_MARK + 16 n *)
Lemma o2a_dst_val : forall E n md, bv_unsigned (ew E 21) = n -> bv_unsigned (ew E 32) = md ->
  0 <= n <= 31 -> 0 <= md -> md + 8856 < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SOff 21 0) (SLit 4)) (SLit 8340)) (SOff 32 0)) =
    Z_to_bv 64 (md + MD_MARK + MARK_LEN * n).
Proof.
  intros E n md U21 U32 Hn Hmd H47. apply o5_sv_of_U; [|unfold MD_MARK, MARK_LEN; lia].
  rewrite !U_SAlu, !U_SOff, !U_SLit, U21, U32. cbn [zalu_raw].
  unfold zcanon, M64, MD_MARK, MARK_LEN.
  replace (Z.land (4 mod 2 ^ 64) 63) with 4 by reflexivity.
  rewrite !Z.add_0_r. rewrite (Z.mod_small n (2 ^ 64)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 4) with 16.
  rewrite (Z.mod_small (n * 16) (2 ^ 64)) by lia. rewrite (Z.mod_small 8340 (2 ^ 64)) by lia.
  rewrite (Z.mod_small (n * 16 + 8340) (2 ^ 64)) by lia. rewrite (Z.mod_small md (2 ^ 64)) by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

(* the model block after the append: the count n + 1 and slot n holding t, the rest as it was *)
Lemma o2a_model_at : forall (m m2 : word -> option byte) md mbs n t,
  amodel_at SEGS m md mbs -> 0 <= n <= 31 -> (length t <= 11)%nat ->
  abytes SEGS m2 (md + MD_N_MARK) (o2l_cnt n) ->
  (forall j, (j <= length t)%nat -> mbyte SEGS m2 (md + o2l_D n + Z.of_nat j) = nth_error (t ++ [zb 0]) j) ->
  (forall i, Z.of_nat i < MD_SIZE -> ~ (MD_N_MARK <= Z.of_nat i < MD_N_MARK + 4) ->
     ~ (o2l_D n <= Z.of_nat i <= o2l_D n + Z.of_nat (length t)) ->
     mbyte SEGS m2 (md + Z.of_nat i) = mbyte SEGS m (md + Z.of_nat i)) ->
  (forall i, 0 <= i < MD_SIZE -> writable_at SEGS m2 (md + i)) ->
  amodel_at SEGS m2 md (o2l_mbs2 mbs n t).
Proof.
  intros m m2 md mbs n t ((HAB & _) & HL) Hn Ht HC HS HO HW.
  destruct HAB as (Hp & Hpl & Hnth). destruct HC as (_ & _ & Hc).
  assert (HL2 : length (o2l_mbs2 mbs n t) = length mbs) by (apply o2l_len2; [exact HL | lia | exact Ht]).
  assert (HL1 : length (o2l_mbs1 mbs n) = length mbs) by (apply o2l_len1; exact HL).
  assert (HDz : Z.of_nat (Z.to_nat (o2l_D n)) = 8340 + 16 * n)
    by (rewrite Z2Nat.id by (unfold o2l_D, MD_MARK, MARK_LEN; lia); unfold o2l_D, MD_MARK, MARK_LEN; lia).
  assert (HCz : Z.of_nat (Z.to_nat MD_N_MARK) = 8852) by reflexivity.
  assert (HT : Z.of_nat (length (t ++ [zb 0])) = Z.of_nat (length t) + 1) by (rewrite o2l_lenT; lia).
  unfold MD_SIZE in HL.
  split; [|rewrite HL2; exact HL].
  split.
  - split; [exact Hp|]. split; [rewrite HL2; exact Hpl|].
    intros i Hi. rewrite HL2 in Hi.
    unfold o2l_mbs2. rewrite o2l_nth_upd by (apply Nat2Z.inj_le; rewrite Nat2Z.inj_add, HDz, HT, HL1, HL; lia).
    destruct (Nat.leb_spec (Z.to_nat (o2l_D n)) i) as [Hi1 | Hi1];
      [destruct (Nat.ltb_spec i (Z.to_nat (o2l_D n) + length (t ++ [zb 0]))) as [Hi2 | Hi2] |]; cbn [andb].
    + apply Nat2Z.inj_le in Hi1. apply Nat2Z.inj_lt in Hi2. rewrite Nat2Z.inj_add, HDz, HT in Hi2. rewrite HDz in Hi1.
      replace (md + Z.of_nat i) with (md + o2l_D n + Z.of_nat (i - Z.to_nat (o2l_D n)))
        by (rewrite Nat2Z.inj_sub by (apply Nat2Z.inj_le; rewrite HDz; lia); rewrite HDz;
            unfold o2l_D, MD_MARK, MARK_LEN; lia).
      apply HS. apply Nat2Z.inj_le. rewrite Nat2Z.inj_sub by (apply Nat2Z.inj_le; rewrite HDz; lia). rewrite HDz. lia.
    + apply Nat2Z.inj_le in Hi1. apply Nat2Z.inj_le in Hi2. rewrite Nat2Z.inj_add, HDz, HT in Hi2. rewrite HDz in Hi1.
      rewrite o2l_mbs1_cnt, o2l_nth_upd by (apply Nat2Z.inj_le; rewrite Nat2Z.inj_add, HCz, o2l_cnt_len, HL; cbn; lia).
      rewrite o2l_cnt_len.
      destruct (Nat.leb_spec (Z.to_nat MD_N_MARK) i) as [Hj1 | Hj1];
        [destruct (Nat.ltb_spec i (Z.to_nat MD_N_MARK + 4)) as [Hj2 | Hj2] |]; cbn [andb].
      * apply Nat2Z.inj_le in Hj1. apply Nat2Z.inj_lt in Hj2. rewrite Nat2Z.inj_add, HCz in Hj2. rewrite HCz in Hj1.
        replace (md + Z.of_nat i) with (md + MD_N_MARK + Z.of_nat (i - Z.to_nat MD_N_MARK))
          by (rewrite Nat2Z.inj_sub by (apply Nat2Z.inj_le; rewrite HCz; lia); rewrite HCz; unfold MD_N_MARK; lia).
        apply Hc. rewrite o2l_cnt_len. apply Nat2Z.inj_lt. rewrite Nat2Z.inj_sub by (apply Nat2Z.inj_le; rewrite HCz; lia).
        rewrite HCz. cbn. lia.
      * apply Nat2Z.inj_le in Hj1. apply Nat2Z.inj_le in Hj2. rewrite Nat2Z.inj_add, HCz in Hj2.
        apply Nat2Z.inj_lt in Hi. rewrite HL in Hi.
        rewrite HO by (unfold MD_N_MARK, MD_SIZE; lia). apply Hnth. apply Nat2Z.inj_lt. rewrite HL. lia.
      * apply Nat2Z.inj_lt in Hj1. rewrite HCz in Hj1. apply Nat2Z.inj_lt in Hi. rewrite HL in Hi.
        rewrite HO by (unfold MD_N_MARK, MD_SIZE; lia). apply Hnth. apply Nat2Z.inj_lt. rewrite HL. lia.
    + apply Nat2Z.inj_lt in Hi1. rewrite HDz in Hi1.
      rewrite o2l_mbs1_cnt, o2l_nth_upd by (apply Nat2Z.inj_le; rewrite Nat2Z.inj_add, HCz, o2l_cnt_len, HL; cbn; lia).
      rewrite o2l_cnt_len.
      destruct (Nat.leb_spec (Z.to_nat MD_N_MARK) i) as [Hj1 | Hj1];
        [destruct (Nat.ltb_spec i (Z.to_nat MD_N_MARK + 4)) as [Hj2 | Hj2] |]; cbn [andb].
      * apply Nat2Z.inj_le in Hj1. rewrite HCz in Hj1. lia.
      * apply Nat2Z.inj_le in Hj1. rewrite HCz in Hj1. lia.
      * apply Nat2Z.inj_lt in Hj1. rewrite HCz in Hj1. apply Nat2Z.inj_lt in Hi. rewrite HL in Hi.
        rewrite HO by (unfold MD_N_MARK, MD_SIZE; lia). apply Hnth. apply Nat2Z.inj_lt. rewrite HL. lia.
  - intros i Hi. apply HW. rewrite HL2, HL in Hi. unfold MD_SIZE. lia.
Qed.

(* a byte the A view shows, as the byte of the restricted memory *)
Lemma o2a_mbyte_eq : forall H H' (m m' : word -> option byte) a,
  aview SEGS H' m' a = aview SEGS H m a -> mbyte SEGS (mrestrict H' m') a = mbyte SEGS (mrestrict H m) a.
Proof.
  intros H H' m m' a E. unfold aview in E.
  destruct (mbyte SEGS (mrestrict H' m') a) as [b|], (mbyte SEGS (mrestrict H m) a) as [b'|];
    cbn [option_map] in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma o2_ap : forall POST i,
  FROM POST (o2_u_inv B MT MS la_nul LF_MO_SET LF_MO_OP i) -> FROM POST (o2_a_inv B MT MS la_nul LF_MO_SET LF_MO_OP i).
Proof.
  intros POST i HU cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HA0.
  destruct HA0 as (md & mk & P & N & s & t & kbs & mbs & gbs & T3 & Hsh & RM & Hn31 & Hne).
  pose proof RM as (R20 & Hw & Hlt & R21 & R22 & HM & Hare & R23 & Hrq & Hmm).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof HM as (Hi & Hcore & Hkr & Hsv & Hhd & Hfs & Hsl & Hcur & Hjbk & Hblk & Hdatn & Hop & Hns).
  pose proof Hkr as (R19 & R24 & R25 & R27).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof Hdatn as (_ & _ & _ & _ & _ & _ & Dmd & Dmwf & _).
  set (n := md_n_mark mbs) in *.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof alloc_ceiling_lt as CL.
  destruct (o5_geo SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB)
    as (Hal0 & Hceil0 & H470 & Hsp1r & Hsp132 & Hsp146).
  pose proof (o5_aj_AR SK B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR3.
  pose proof Hblk as (Hmdin & Hmkin & Hmdc & Hmkc & HmdT & HmkT & Hmd16 & Hmk16 & Hmdoff & Hmkoff & Hapmm & Hapmi & Hapki
    & Hramd & Hramk & Hammd & Hammk).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ md MD_SIZE HAR3 Hmdin) as (_ & Hmd4096 & Hmdceil & _).
  change (req_size MD_SIZE) with 8856 in Hmdceil.
  pose proof Hsl as (_ & _ & _ & _ & _ & _ & _ & _ & SMARK0 & _ & _ & _ & _ & _ & _ & SNMARK & _).
  unfold lf_slot, lf_at in SMARK0, SNMARK. apply o5_vm_of_rd in SMARK0, SNMARK.
  unfold LS_MARK0, LS_NMARK in SMARK0, SNMARK.
  set (E := Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 md])) in *.
  assert (EL : forall n0 (r : bv 5), (n0 < 32)%nat -> Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr (ms_regs ms3) r).
  { intros n0 r Hn Hr. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat _ _ n0 r Hr). }
  assert (E32 : ew E 32 = Z_to_bv 64 md) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
  assert (U9 : bv_unsigned (ew E 9) = lf_sp1 cx)
    by (rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl), R9; unfold w64; apply unsigned_lit_small; clear - Hsp146 Hsp1r H470; lia).
  assert (U27 : bv_unsigned (ew E 27) = o5_RSB)
    by (rewrite (EL 27%nat 27%bv ltac:(lia) eq_refl), R27; unfold w64, o5_RSB, SHADOW_OFF; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = md) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (U21 : bv_unsigned (ew E 21) = n)
    by (rewrite (EL 21%nat 21%bv ltac:(lia) eq_refl), R21; unfold w64; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi (fx := fy) SEGS pa_val E o2a_ss
    (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LO2_a)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold o2a_ss. apply pa_entry_st_ok_full.
    - apply o2a_regs_ok; [apply regs_ok_Eimg_Ereg|].
      unfold o2a_shx. rewrite (o2m_shx_val E 32 8852 md U32 U27 ltac:(lia) ltac:(lia)
        ltac:(clear - Hmdceil CL; unfold MD_SIZE in *; lia)). rewrite R22. reflexivity.
    - vm_compute. reflexivity.
    - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, o2a_fr, o2a_cnt, o2m_c8;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite U9. split; [clear - Hsp146; lia|]. split; [clear - Hsp146 Hsp1r H470; lia|].
        split; [intros o Ho; clear - Ho; lia|].
        repeat apply Forall_cons; try apply Forall_nil.
        * apply (chunk_ok_val SEGS E _ (lf_sp1 cx) 0x58 8 (SOff 32 8340) (md + MD_MARK));
            [ cbn [sv_denot]; rewrite U32; unfold MD_MARK; reflexivity | unfold MD_MARK; cbn; lia | cbn; lia | exact SMARK0 ].
        * apply (chunk_ok_val SEGS E _ (lf_sp1 cx) 0x98 8 (SOff 32 8852) (md + MD_N_MARK));
            [ cbn [sv_denot]; rewrite U32; unfold MD_N_MARK; reflexivity | unfold MD_N_MARK; cbn; lia | cbn; lia | exact SNMARK ].
      + rewrite U32. split; [lia|]. split; [lia|].
        split; [|apply Forall_nil]. intros o Ho. destruct Dmd as ((_ & Hmw) & Hml). apply Hmw. unfold MD_SIZE in *. lia.
    - apply pairwise_disjoint_of_extents. unfold o2a_fr, o2a_cnt, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      clear - Hmdceil Hsp1r Hceil0 CL. unfold LLVMF_STK in *. lia.
    - split; [|split; exact I]. cbn [o2a_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U9, U32, U27, U21. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I;
        clear - Hsp146 Hsp1r H470 Hsp132 Hmd4096 Hmdceil Hmd16 Hn31 CL Hceil0; unfold o5_RSB, LLVMF_STK in *; try lia. }
  rewrite (lf_shape_eta fy LO2_a ms3 Hsh).
  assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  assert (SHOK : sh_ok SEGS o5_Bx o2a_SH E (rdW W3 (ms_mem ms3))).
  { unfold sh_ok, o2a_SH. apply Forall_cons; [|apply Forall_nil]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
    unfold o5_Bx. rewrite !U_SOff, U32, U27. unfold zcanon, M64.
    rewrite !Z.add_0_r, !Z.mod_small by (unfold o5_RSB; lia). replace (8856 - 0) with MD_SIZE by reflexivity.
    split; [exact Hramd|]. intros a Ha. cbn [Z.min Z.max] in Ha. rewrite Z.max_r in Ha by (unfold MD_SIZE; lia).
    unfold amem_range, o5_RSB, MD_SIZE in *. lia. }
  pose proof HJ as HJ0.
  paj_run_tok RUN HS HJ SHOK o5_span.
  { cbn [ss_mem o2a_ss]. apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]].
    - intros a Ha. cbn [YP09.r_wlo YP09.r_whi o2a_fr] in Ha. lia.
    - intros a Ha. cbn [YP09.r_wlo YP09.r_whi YP09.r_base o2a_cnt base_val] in Ha. rewrite U32 in Ha.
      apply (ar_ajw_blk B cx fp ly3 S3 md MD_SIZE a Hmdin Hmdc). unfold MD_SIZE in *. lia. }
  rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
  assert (Fd : m_fds md4 = m_fds md3) by (subst md4; rewrite !lf_wvb_fds; reflexivity).
  assert (Fs : m_fs md4 = m_fs md3) by (subst md4; rewrite !lf_wvb_fs; reflexivity).
  set (X := fun a => md + MD_N_MARK <= a mod 2 ^ 64 < md + MD_N_MARK + 4).
  assert (KA : kagree SEGS X (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msA))).
  { apply (u_kagree_frame E (ss_mem o2a_ss) _ _ X HFrA). intros a (r & Hr & Hw0). unfold X.
    rewrite Z_to_bv_unsigned in Hw0. unfold bv_wrap in Hw0. change (bv_modulus 64) with (2 ^ 64) in Hw0.
    cbn [ss_mem o2a_ss In] in Hr. destruct Hr as [<- | [<- | []]];
      cbn [YP09.r_wlo YP09.r_whi YP09.r_base o2a_fr o2a_cnt base_val] in Hw0; rewrite ?U32 in Hw0;
      unfold MD_N_MARK; clia. }
  assert (XB : forall a, X a -> 0 <= a < 2 ^ 64 -> md <= a < md + MD_SIZE)
    by (intros a Ha R; unfold X in Ha; rewrite Z.mod_small in Ha by exact R; unfold MD_N_MARK, MD_SIZE in *; clia).
  assert (NX : forall a, (lf_saved_fp cx a \/ lf_header_fp cx fp a \/ lf_fshadow_fp cx fp 112 a \/ lf_slots_fp cx a \/
     lf_cur_fp cx a \/ lf_jbk_fp MS la_nul cx T3 a \/ lf_blocks_fp md mk a) -> ~ X a).
  { intros a Hf HXa.
    pose proof (u_fp_range SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
      cx fp k2 _ _ _ _ md mk T3 _ ly3 S3 W3 ms3 md3 a HB HJ0 Hfr Hjbk Hblk ltac:(tauto)) as (R & _).
    destruct (u_blk_out SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS
      cx fp k2 _ _ _ _ md mk T3 _ ly3 S3 W3 ms3 md3 md MD_SIZE a HB HJ0 Hfr Hjbk Hblk
      (or_introl eq_refl) (XB a HXa R)) as (_ & N1 & N2 & N3 & N4 & N5 & N6 & N7 & _). tauto. }
  pose proof (lf_jbk_keep B MT MS la_nul X cx fp k2 _ _ _ _ ly3 S3 W3 ms3 md3 T3 _ W3 msA md4 KA Fd Fs
    (fun a Ha => NX a ltac:(tauto)) Hjbk) as HjbkA.
  pose proof (lf_blocks_keep B X _ _ cx md mk T3 ly3 S3 KA (fun a Ha => NX a ltac:(tauto)) Hblk) as HblkA.
  pose proof HjbkA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROA & _).
  pose proof Hdatn as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Dgn & _).
  assert (XN : forall a, LA_G_NAMES <= a < LA_G_NAMES + G_NAMES_SIZE -> ~ X a).
  { intros a Ha HXa. pose proof (XB a HXa ltac:(unfold LA_G_NAMES, G_NAMES_SIZE in *; lia)) as Hb.
    unfold YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, LA_G_NAMES, G_NAMES_SIZE, MD_SIZE in *. lia. }
  pose proof (lf_gnames_at_keep X _ _ 64 KA ltac:(lia) XN Dgn) as DgnA.
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem msA) md4 k2 HB HJ) as (H16 & Hceil & _ & Hshi & Hs47 & Hpres & HARA).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem msA) md4 k2 HB HJ) as (Hs1 & H16' & Hlo & H47).
  lazymatch type of HS with st_ok _ ?Ex ?ssx _ => set (EA := Ex) in HS; set (ssA := ssx) in HS end.
  assert (EWA : forall n0, (n0 < 512)%nat -> ew EA n0 = ew E n0)
    by (intros n0 Hn0; unfold EA; repeat (rewrite ew_ewset_other by lia); reflexivity).
  assert (UA21 : bv_unsigned (ew EA 21) = n) by (rewrite EWA by lia; exact U21).
  assert (UA32 : bv_unsigned (ew EA 32) = md) by (rewrite EWA by lia; exact U32).
  assert (RGc : region_ok SEGS EA (rdW W3 (ms_mem msA)) (nth 1 (ss_mem ssA) o2a_fr))
    by exact (st_ok_region_nth EA ssA (restrict (w_H W3) msA) 1 _ HS eq_refl).
  assert (ACA : abytes SEGS (rdW W3 (ms_mem msA)) (md + MD_N_MARK) (o2l_cnt n)).
  { replace (md + MD_N_MARK) with (md + 8852) by (unfold MD_N_MARK; lia).
    apply (o5_word4 EA _ _ md 8852 (SOff 21 1) _ RGc).
    - cbn [nth ss_mem ssA YP09.r_base base_val]. exact UA32.
    - cbn. left. reflexivity.
    - apply o2l_cnt_len.
    - unfold o2l_cnt. rewrite Mem.bytes_le_to_Z_le4, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      cbn [sv_denot]. rewrite UA21. rewrite (Z.mod_small (n + 1) (2 ^ 64)) by lia. rewrite (Z.mod_small (n + 1)) by lia.
      reflexivity.
    - lia.
    - clear - Hmdceil CL. lia. }
  pmkst HS.
  assert (Hpc : ss_pc ssA = pa_sigma LS___interceptor_trampoline_snprintf) by reflexivity.
  rewrite Hpc, (lv_sigma LV LS___interceptor_trampoline_snprintf).
  change (link_sigma LS___interceptor_trampoline_snprintf) with LA_W_SNPRINTF.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (11%bv : bv 5) Q11. prreg HS (13%bv : bv 5) Q13.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
  prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (27%bv : bv 5) Q27.
  rewrite ?EWA in Q1, Q2, Q3, Q4, Q13, Q8, Q9, Q19, Q20, Q23, Q24, Q25, Q27 by lia.
  rewrite (EL 8%nat 8%bv ltac:(lia) eq_refl) in Q8. rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl) in Q9.
  rewrite (EL 19%nat 19%bv ltac:(lia) eq_refl) in Q19. rewrite (EL 20%nat 20%bv ltac:(lia) eq_refl) in Q20.
  rewrite (EL 23%nat 23%bv ltac:(lia) eq_refl) in Q23. rewrite (EL 24%nat 24%bv ltac:(lia) eq_refl) in Q24.
  rewrite (EL 25%nat 25%bv ltac:(lia) eq_refl) in Q25. rewrite (EL 27%nat 27%bv ltac:(lia) eq_refl) in Q27.
  try rewrite (img_env_codeptr E HEI) in Q1.
  rewrite (EL 2%nat 2%bv ltac:(lia) eq_refl) in Q2. rewrite (EL 3%nat 3%bv ltac:(lia) eq_refl) in Q3.
  rewrite (EL 4%nat 4%bv ltac:(lia) eq_refl) in Q4. rewrite (EL 20%nat 20%bv ltac:(lia) eq_refl) in Q13.
  set (d := md + MD_MARK + MARK_LEN * n).
  assert (Q10 : getr (ms_regs msA) 10 = w64 d).
  { rewrite (st_ok_restrict_reg SEGS (w_H W3) EA _ msA 10%bv HS). cbn [setpc ss_regs].
    replace (sr_get (ss_regs ssA) 10%bv)
      with (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SOff 21 0) (SLit 4)) (SLit 8340)) (SOff 32 0))
      by (vm_compute; reflexivity).
    exact (o2a_dst_val EA n md UA21 UA32 ltac:(lia) ltac:(lia) ltac:(clear - Hmdceil CL; unfold MD_SIZE in *; lia)). }
  assert (Q12 : getr (ms_regs msA) 12 = w64 LA_STR21).
  { rewrite (st_ok_restrict_reg SEGS (w_H W3) EA _ msA 12%bv HS). cbn [setpc ss_regs].
    replace (sr_get (ss_regs ssA) 12%bv) with (SOff 253 0) by (vm_compute; reflexivity).
    cbn [sv_denot]. rewrite EWA by lia. unfold E. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia). change 253%nat with (A_OBJ 12).
    rewrite (lv_obj LV 12 ltac:(unfold link_nobj; lia)). rewrite Z.add_0_r. reflexivity. }
  assert (Rsp : spZ (ms_regs msA) = lf_sp1 cx).
  { unfold spZ. rewrite Q2, R2. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. clia. }
  assert (HK : alloc_ceiling <= spZ (ms_regs msA) - 8192) by (rewrite Rsp; unfold LLVMF_STK in *; clia).
  destruct (o2_name_rt B TB HSEGS ly3 S3 W3 (ms_mem msA) md4 (ms_regs msA) 8192 s t HARA HROA DgnA HK Hw)
    as (Hac & Hrt & Hs16 & Hl11 & Hloc).
  pose proof Hrt as (Hs0 & Hsl32 & Hsam & Hsra & Hshv & Hstl & Hsap).
  assert (Hsb : 0x10000 <= s < 0x654000) by (clear - Hs16 Hloc; unfold LA_G_NL, LA_G_NAMES, G_NAMES_SIZE in *; lia).
  set (T := map (fun b : byte => bv_unsigned b) t).
  set (wd := Z.of_nat (length t) + 1).
  assert (Hw15 : (length t <= 15)%nat) by lia.
  assert (Ew : sn_len (16 - 1) T = wd) by exact (rem_sn_len t Hw15).
  assert (Hdw : md <= d /\ d + wd + 8 <= md + MD_SIZE) by (unfold d, wd, MD_MARK, MARK_LEN, MD_SIZE in *; clia).
  destruct (lf_md_sub SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS cx fp ly3 S3 W3
    (ms_mem msA) md4 k2 md mk T3 (ms_regs msA) 8192 d wd HB HJ HblkA Rsp
    ltac:(unfold LLVMF_STK; lia) ltac:(lia) ltac:(lia) ltac:(unfold wd; lia)) as (Dra & Dhv & Dam & Dap).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem msA) md4 md MD_SIZE HARA Hmdin) as (_ & _ & _ & _ & BPres & _).
  change (req_size MD_SIZE) with 8856 in BPres.
  assert (HD : lf_snp_dest W3 (ms_mem msA) d (sn_len (16 - 1) T)).
  { rewrite Ew. apply lf_snp_dest_heap.
    - unfold d, MD_MARK in *. clia.
    - unfold YCbq.off_img in *. unfold MD_SIZE in *. lia.
    - unfold MD_SIZE in *. clear - Hdw Hmdceil. lia.
    - intros a Ha. apply (apresent_writable SEGS). apply BPres. unfold MD_SIZE in *. lia.
    - apply (rem_amem_sub md MD_SIZE); [exact Hammd | lia | unfold wd; lia | lia].
    - rewrite <- ard_aview. exact Dra.
    - rewrite <- ard_aview. exact Dhv. }
  assert (Hwin1 : s + Z.of_nat (length t) + 8 <= spZ (ms_regs msA) - LINK_SNP_STK).
  { pose proof alloc_ceiling_value as CV. assert (HSV : LINK_SNP_STK = 8192) by reflexivity. rewrite HSV.
    (* bridge through the ceiling: the pruning lia keeps only hypotheses that share a variable with the goal *)
    assert (A11 : 6635540 <= spZ (ms_regs msA) - 8192) by lia.
    assert (A8 : s + Z.of_nat (length t) + 8 <= 6635540) by lia.
    lia. }
  assert (Hdap : s + Z.of_nat (length t) + 8 <= d \/ d + wd <= s).
  { unfold YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, MD_SIZE in Hmdoff.
    assert (Hlt11 : Z.of_nat (length t) <= 11) by lia.
    unfold d, wd, MD_MARK, MARK_LEN. destruct Hmdoff as [Hm | Hm]; [right | left]; lia. }
  destruct (lf_snp_arg_str W3 (ms_mem msA) (ms_regs msA) s t d wd (spZ (ms_regs msA)) ltac:(rewrite Q13; exact R20)
    ltac:(clear - Hsb; lia) Hac ltac:(clear - Hl11; lia)
    ltac:(intros x Hx; rewrite <- ard_aview; apply Hstl; unfold str_end in Hx; rewrite length_map in Hx; exact Hx)
    ltac:(exact Hsam) ltac:(rewrite <- ard_aview; exact Hsra) ltac:(rewrite <- ard_aview; exact Hshv)
    (or_introl Hwin1)
    Hdap)
    as (HA & HSL & HAM & HTX).
  fold T in HA, HSL, HAM, HTX.
  rewrite <- Ew in HA.
  destruct (@lf_snp_pre rc SK PI B TB HSEGS G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly3 S3 W3 (ms_mem msA) md4 k2 (ms_regs msA)
    d 16 LA_STR21 LF_FMT_S [Ps] [APtr T] T HJ
    ltac:(rewrite Rsp; change LINK_SNP_STK with 8192; unfold LLVMF_STK; clear - Hsp1r; lia)
    ltac:(rewrite Rsp; clear - Hsp1r; lia)
    HROA Q10 Q11 Q12 (or_intror (conj eq_refl (conj eq_refl eq_refl))) HA HSL HAM HTX ltac:(lia)
    ltac:(unfold T; rewrite length_map; clear - Hl11; lia) HD) as (cval & HFP).
  assert (HAJW : forall a, d <= a < d + sn_len (16 - 1) T ->
    ajw B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx) ly3 S3
      [(LF_CID, fp)] a).
  { intros a Ha. rewrite Ew in Ha. apply (ar_ajw_blk B cx fp ly3 S3 md MD_SIZE a Hmdin Hmdc). lia. }
  assert (HFRM : YK0o.frm_zero (@YK11.fp_csr fy)).
  { destruct Hfx as (_ & [Hc0 | Hc0]); [rewrite Hc0; exact Hfrm | exact Hc0]. }
  eapply (@lf_snp_step fy rc SK PI B LAWS (SNP fy) G_HARNESS 0 [] W3 (ms_regs msA) (ms_mem msA)
    LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(LF_CID, fp)] ly3 S3 md4 k2 d 16 LA_STR21 _ T cval).
  - exact HGX.
  - exact HJ.
  - rewrite Rsp. change LINK_SNP_STK with 8192. unfold LLVMF_STK. clear - Hsp1r. lia.
  - rewrite Rsp. clear - Hsp1r. lia.
  - rewrite Rsp. exact H16'.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Q3, R3. exact (proj1 (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB)).
  - rewrite Q4, R4. exact (proj2 (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB)).
  - exact HROA.
  - exact HFP.
  - exact HAJW.
  - exact HFRM.
  - intros fx' W2 c2 Hle Hfxr HPOST.
    destruct HPOST as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & Hpr & Hfr2 & Hfd2 & Hfs2 & Hkp & Hsk & HQ).
    destruct HQ as (-> & -> & -> & Hsbm & Ha0 & Hby & Hkept & Hpres2).
    rewrite Z.add_0_r in HJ2. rewrite Ew in Hby, Hkept, Hpres2. change LINK_SNP_STK with 8192 in Hkept, Hkp.
    unfold T in Hby. rewrite (rem_sn_bytes t Hw15) in Hby.
    set (ms2 := @mkst fx' regs2 (getr (ms_regs msA) 1) mem2 (seg_rom SEGS)).
    change mem2 with (ms_mem ms2) in HJ2, Hkept, Hpres2, Hby, Hkp, Hsk.
    pose proof HJ2 as (_ & _ & (memS2 & HJi2 & _) & _). pose proof HJi2 as (HAR2 & _).
    assert (Hdd : d = md + o2l_D n) by (unfold d, o2l_D; lia).
    assert (Hcl : d + wd <= alloc_ceiling) by (unfold MD_SIZE in *; clear - Hdw Hmdceil; lia).
    set (slo := lf_sp1 cx - 8192). set (shi := lf_sp1 cx).
    assert (Hslo2 : alloc_ceiling <= slo) by (unfold slo; rewrite <- Rsp; exact HK).
    assert (Hshi2 : shi <= 2 ^ 64) by (unfold shi; clear - Hsp1r Hsp146 H470; lia).
    (* every byte of the block: kept, or the count, or the slot *)
    assert (KEEP : forall a, md <= a < md + MD_SIZE -> ~ (md + MD_N_MARK <= a < md + MD_N_MARK + 4) ->
      ~ (d <= a < d + wd) -> mbyte SEGS (rdW W3 (ms_mem ms2)) a = mbyte SEGS (rdW W3 (ms_mem ms3)) a).
    { intros a Ha Hc1 Hc2.
      assert (Ra : 0 <= a < 2 ^ 64) by (unfold MD_SIZE in *; clear - Ha Hmd4096 Hmdceil CL; lia).
      rewrite (o2a_mbyte_eq (w_H W3) (w_H W3) (ms_mem msA) (ms_mem ms2) a
        (Hkept a Ra Hc2 ltac:(rewrite Rsp; unfold MD_SIZE in *; clear - Ha Hslo2 Hmdceil; unfold slo in Hslo2; lia))).
      apply KA. unfold X. rewrite Z.mod_small by exact Ra. exact Hc1. }
    assert (AC2 : abytes SEGS (rdW W3 (ms_mem ms2)) (md + MD_N_MARK) (o2l_cnt n)).
    { destruct ACA as (A1 & A2 & A3). split; [exact A1|]. split; [exact A2|].
      intros k Hk. rewrite <- (A3 k Hk). rewrite o2l_cnt_len in Hk.
      assert (Ra : 0 <= md + MD_N_MARK + Z.of_nat k < 2 ^ 64) by (unfold MD_N_MARK; clear - Hk Hmd4096 Hmdceil CL; lia).
      apply (o2a_mbyte_eq (w_H W3) (w_H W3) (ms_mem msA) (ms_mem ms2)).
      apply Hkept; [exact Ra | | rewrite Rsp].
      - unfold d, MD_N_MARK, MD_MARK, MARK_LEN, wd in *. clear - Hk Hn31 Hl11. lia.
      - unfold MD_N_MARK, MD_SIZE in *. clear - Hk Hslo2 Hmdceil. unfold slo in Hslo2. lia. }
    assert (SL2 : forall j, (j <= length t)%nat ->
      mbyte SEGS (rdW W3 (ms_mem ms2)) (md + o2l_D n + Z.of_nat j) = nth_error (t ++ [zb 0]) j).
    { intros j Hj. rewrite <- Hdd.
      pose proof (Hby (Z.of_nat j) ltac:(unfold wd; lia)) as Hb. rewrite Nat2Z.id in Hb.
      rewrite (rem_nth_error_nth (t ++ [zb 0]) j (zb 0)) by (rewrite o2l_lenT; lia).
      replace (nth j (map (fun b : byte => bv_unsigned b) t ++ [0]) 0)
        with (bv_unsigned (nth j (t ++ [zb 0]) (zb 0))) in Hb.
      2: { rewrite <- (map_nth (fun b : byte => bv_unsigned b) (t ++ [zb 0]) (zb 0) j). rewrite map_app. reflexivity. }
      rewrite (ambyte_of_aview SEGS W3 (ms_mem ms2) _ _ ltac:(pose proof (bv_unsigned_in_range _ (nth j (t ++ [zb 0]) (zb 0))) as Rb;
        change (bv_modulus 8) with 256 in Rb; exact Rb) Hb).
      f_equal. apply Z_to_bv_bv_unsigned. }
    assert (WR2 : forall i0, 0 <= i0 < MD_SIZE -> writable_at SEGS (rdW W3 (ms_mem ms2)) (md + i0)).
    { intros i0 Hi0.
      destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms2) md2 md MD_SIZE HAR2 Hmdin) as (_ & _ & _ & _ & BP2 & _).
      change (req_size MD_SIZE) with 8856 in BP2. apply (apresent_writable SEGS). apply BP2. unfold MD_SIZE in *. lia. }
    pose proof Dmd as (_ & HLm).
    assert (Hmd2 : amodel_at SEGS (rdW W3 (ms_mem ms2)) md (o2l_mbs2 mbs n t)).
    { apply (o2a_model_at (rdW W3 (ms_mem ms3)) _ md mbs n t Dmd ltac:(lia) Hl11 AC2 SL2); [|exact WR2].
      intros i0 Hi0 H1 H2. apply KEEP; [unfold MD_SIZE in *; lia | intros H3; apply H1; lia |].
      rewrite Hdd. unfold wd. lia. }
    assert (Hnz : ~ In (zb 0) t) by exact (proj2 Hac).
    assert (Hmwf2 : model_wf (o2l_mbs2 mbs n t)) by exact (o2l_wf2 mbs n t HLm eq_refl ltac:(lia) Hl11 Hnz Dmwf).
    (* the call's frame, from the arm's state *)
    destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
      (ms_mem ms3) md3 k2 HB HJ0) as (_ & _ & _ & _ & _ & Hpres0 & _).
    set (Ecnt := fun a => md + MD_N_MARK <= a < md + MD_N_MARK + 4).
    set (Ew2 := fun a => Ecnt a \/ (d <= a < d + wd)).
    assert (AK0 : akept SEGS B ly3 S3 W3 (ms_mem ms3) W3 (ms_mem ms3) slo shi (fun _ => False)).
    { apply (akept_refl SK SEGS B LAWS pa_segs_low). intros a Ha. apply Hpres0. unfold slo, shi in Ha.
      clear - Ha Hsp1r. unfold LLVMF_STK. lia. }
    assert (AK1 : akept SEGS B ly3 S3 W3 (ms_mem ms3) W3 (ms_mem msA) slo shi Ecnt).
    { apply (akept_step SK SEGS B LAWS pa_segs_low ly3 S3 W3 (ms_mem ms3) md3 W3 (ms_mem ms3) W3 (ms_mem msA)
        slo shi (fun _ => False) Ecnt Ecnt HAR3 Hslo2 Hshi2 AK0).
      - intros a Ra Hn0. apply (aview_of_kagree SEGS X (w_H W3) (w_H W3) (ms_mem ms3) (ms_mem msA) a KA).
        unfold X. rewrite Z.mod_small by exact Ra. exact Hn0.
      - intros a Ra Hp0. exact (YCbq.apresent_grows (w_H W3) _ _ a HGA Hp0).
      - intros a [].
      - intros a Ha. left. exact Ha. }
    assert (AK2 : akept SEGS B ly3 S3 W3 (ms_mem ms3) W3 (ms_mem ms2) slo shi Ew2).
    { apply (akept_step SK SEGS B LAWS pa_segs_low ly3 S3 W3 (ms_mem ms3) md3 W3 (ms_mem msA) W3 (ms_mem ms2)
        slo shi Ecnt Ew2 (fun a => (d <= a < d + wd) \/ (slo <= a < shi)) HAR3 Hslo2 Hshi2 AK1).
      - intros a Ra Hn0. apply Hkept; [exact Ra | intros H; apply Hn0; left; exact H |].
        rewrite Rsp. intros H; apply Hn0; right; exact H.
      - intros a Ra Hp0. apply Hpres2; [pose proof alloc_ceiling_value as CV0; clear - Ra CV0; lia | exact Hp0 |].
        intros (H1 & _). clear - H1 Ra Hcl. lia.
      - intros a Ha. left. exact Ha.
      - intros a [Ha | Ha]; [left; right; exact Ha | right; exact Ha]. }
    assert (LC : lf_call B cx 8192 ly3 S3 ly3 S3 W3 (ms_mem ms3) W3 (ms_mem ms2) Ew2).
    { split; [lia|]. split; [exact Hslo2|]. split; [exact AK2|].
      exact (ashadow_kept_AR SK SEGS B LAWS pa_segs_low ly3 S3 ly3 S3 W3 (ms_mem ms3) md3 W3 (ms_mem ms2) md2 HAR3 HAR2). }
    assert (HE : forall a, Ew2 a -> (md <= a < md + MD_SIZE) \/ (lf_F cx fp + 24 <= a < lf_F cx fp + 1016)).
    { intros a [Ha | Ha]; left; unfold Ecnt, MD_N_MARK, MD_SIZE in *; clear - Ha Hdw; lia. }
    assert (Fd2 : m_fds md2 = m_fds md3) by (rewrite Hfd2; exact Fd).
    assert (Fs2 : m_fs md2 = m_fs md3) by (rewrite Hfs2; exact Fs).
    pose proof (ak_wcarry_callee B LAWS HSEGS ly3 S3 W3 (ms_mem ms2) md2 (rdW W3 (ms_mem ms3)) md mk HAR2 Hmdin Hmkin)
      as WC.
    pose proof (lf_data_of_nm _ _ _ _ _ _ _ Hdatn Hare) as Hdat.
    destruct (o2a_model_after cx fp 8192 ly3 S3 ly3 S3 W3 ms3 md3 W3 ms2 md2 Ew2 k2 _ _ _ _ md mk kbs mbs gbs
      (o2l_mbs2 mbs n t) T3 _ P N SH_M HB HJ0 Hfr LC HE Fd2 Fs2 Hmdin Hmkin WC ltac:(rewrite SH_M_len; lia)
      Hsv Hhd Hfs Hsl Hcur Hjbk Hblk Hdat Hmd2 Hmwf2)
      as (Hsv2 & Hhd2 & Hfs2' & Hsl2 & Hcur2 & Hjbk2 & Hblk2 & Hdatn2 & HRO2).
    pose proof (ar_pres _ _ Hpr) as (P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27).
    (* +0x11f4 .. +0x11fc: s10 := F + 0x20, s6 := m, j +0xc0c *)
    assert (HFX2 : @BoxBase.fxr fx fx') by exact (fxr_trans fx fy fx' Hfx Hfxr).
    assert (R2' : getr regs2 2 = w64 (lf_sp1 cx)) by (rewrite P2, Q2; exact R2).
    assert (R9' : getr regs2 9 = w64 (lf_sp1 cx)) by (rewrite P9, Q9; exact R9).
    pose proof Hsl2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SWA & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
      & _ & SM & _).
    unfold lf_slot, lf_at in SWA, SM. apply o5_vm_of_rd in SWA, SM. unfold LS_WA, LS_M in SWA, SM.
    destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
      cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ0 Hfr) as (HFa & F32 & F4 & Fc & _).
    set (E3 := Eimg (Ereg regs2 [Z_to_bv 64 (lf_F cx fp + LO_WA); Z_to_bv 64 md])).
    assert (EL3 : forall n0 (r : bv 5), (n0 < 32)%nat -> Z.of_nat n0 = bv_unsigned r -> ew E3 n0 = getr regs2 r).
    { intros n0 r Hn0 Hr. unfold E3. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat _ _ n0 r Hr). }
    assert (E332 : ew E3 32 = Z_to_bv 64 (lf_F cx fp + LO_WA))
      by (unfold E3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
    assert (E333 : ew E3 33 = Z_to_bv 64 md) by (unfold E3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
    assert (U39 : bv_unsigned (ew E3 9) = lf_sp1 cx)
      by (rewrite (EL3 9%nat 9%bv ltac:(lia) eq_refl), R9'; unfold w64; apply unsigned_lit_small; clear - Hsp146 Hsp1r H470; lia).
    set (ssF := mkSS LO2_f sr_atoms [o2l_fr] None (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] [])).
    assert (HS3 : st_ok_pi (fx := fx') SEGS pa_val E3 ssF
      (restrict (w_H W3) (@mkst fx' regs2 (Z_to_bv 64 (BASE + LO2_f)) (ms_mem ms2) (seg_rom SEGS)))).
    { rewrite restrict_mkst_fx. unfold ssF. apply pa_entry_st_ok_full.
      - apply regs_ok_Eimg_Ereg.
      - vm_compute. reflexivity.
      - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, o2l_fr, o2m_c8.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U39. split; [clear - Hsp146; lia|]. split; [clear - Hsp146 Hsp1r H470; lia|].
        split; [intros o Ho; clear - Ho; lia|].
        repeat apply Forall_cons; try apply Forall_nil.
        + apply (chunk_ok_val SEGS E3 _ (lf_sp1 cx) 0x78 8 (SOff 32 0) (lf_F cx fp + LO_WA));
            [ cbn [sv_denot]; rewrite E332, unsigned_lit_small by (unfold LO_WA; clear - F4 Fc CL; lia);
              rewrite Z.add_0_r; reflexivity
            | unfold LO_WA; cbn; clear - F4 Fc CL; lia | cbn; lia | exact SWA ].
        + apply (chunk_ok_val SEGS E3 _ (lf_sp1 cx) 0xe8 8 (SOff 33 0) md);
            [ cbn [sv_denot]; rewrite E333, unsigned_lit_small by (clear - Hmd4096 Hmdceil CL; lia);
              rewrite Z.add_0_r; reflexivity
            | cbn; clear - Hmd4096 Hmdceil CL; lia | cbn; lia | exact SM ].
      - cbn. tauto.
      - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U39.
        split; [|exact I]. clear - Hsp146 Hsp1r H470 Hsp132. change (2 ^ 5) with 32. lia. }
    assert (Hms2 : ms2 = @mkst fx' regs2 (Z_to_bv 64 (BASE + LO2_f)) (ms_mem ms2) (seg_rom SEGS))
      by (unfold ms2; rewrite Q1; reflexivity).
    rewrite Hms2.
    assert (HEI3 : img_env pa_val A_LIM E3) by apply Eimg_env.
    assert (HGX3 := HGX).
    pose proof (@paj_run_to_x fx' rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO3.
    assert (SHOK3 : sh_ok pa_segs (SLit 0) [] E3
      (mrestrict (w_H W3) (ms_mem (@mkst fx' regs2 (Z_to_bv 64 (BASE + LO2_f)) (ms_mem ms2) (seg_rom SEGS)))))
      by (unfold sh_ok; apply Forall_nil).
    assert (HA3 : env_agree 32 (Ereg regs2 []) E3)
      by (split; [intros n0 Hn0; unfold E3; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite !ew_Ereg_lt by lia;
                  reflexivity | unfold E3; reflexivity]).
    paj_run_to_tok RUNTO3 HS3 HJ2 SHOK3 (0, 0) LO2_u; [apply ar_awr_nowin; vm_compute; reflexivity|].
    rename ms into msC, HF into HFC, HFr into HFrC, HG into HGC.
    pose proof (ar_kagree_nowin _ _ _ _ HFrC ltac:(vm_compute; reflexivity)) as KC.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md5 := mdB) in * end.
    assert (Fd5 : m_fds md5 = m_fds md2) by (subst md5; rewrite !lf_wvb_fds; reflexivity).
    assert (Fs5 : m_fs md5 = m_fs md2) by (subst md5; rewrite !lf_wvb_fs; reflexivity).
    lazymatch type of HS3 with st_ok_pi _ _ _ ?ssx _ => set (ssC := ssx) in HS3 end.
    assert (KR : forall r : bv 5, sr_get (ss_regs ssC) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
      getr (ms_regs msC) r = getr regs2 r)
      by (intros r Hr; exact (lf_reg_atom fx' W3 _ ssC msC _ r HS3 HA3 Hr)).
    assert (HM2 : o2_mem2 B MT MS la_nul LF_MO_SET LF_MO_OP i md mk P N kbs (o2l_mbs2 mbs n t) gbs T3 SH_M cx fp k2 ly3 S3
      W3 ms2 md2).
    { split; [exact Hi|]. split.
      { unfold lf_core in *. cbn [ms_regs ms2 mkst]. rewrite P2, P8, P9, P3, P4, Q2, Q8, Q9, Q3, Q4.
        rewrite R8, R9. repeat split; assumption. }
      split.
      { unfold o2_kregs in *. cbn [ms_regs ms2 mkst]. rewrite P19, P24, P25, P27, Q19, Q24, Q25, Q27.
        repeat split; assumption. }
      split; [exact Hsv2|]. split; [exact Hhd2|]. split; [exact Hfs2'|]. split; [exact Hsl2|].
      split; [exact Hcur2|]. split; [exact Hjbk2|]. split; [exact Hblk2|]. split; [exact Hdatn2|].
      split; [exact Hop | exact Hns]. }
    apply (HU cx fx' fp k2 ly3 S3 W3 msC md5 HB HFX2 HJ2 Hfr).
    exists md, mk, P, N, s, t, kbs, (o2l_mbs2 mbs n t), gbs, T3.
    split; [exact (lf_shape_of_st_ok fx' W3 _ ssC msC HS3 eq_refl)|].
    split; [rewrite KR by (vm_compute; reflexivity); cbn [ms_regs ms2 mkst]; rewrite P20, Q20; exact R20|].
    split; [exact Hw|]. split; [exact Hlt|].
    split; [rewrite (st_ok_pi_restrict_reg (fx := fx') (w_H W3) _ _ msC 22%bv HS3);
            replace (sr_get (ss_regs ssC) 22%bv) with (SOff 33 0) by (vm_compute; reflexivity); cbn [sv_denot];
            rewrite E333, unsigned_lit_small by (clear - Hmd4096 Hmdceil CL; lia); rewrite Z.add_0_r; reflexivity|].
    split; [rewrite (st_ok_pi_restrict_reg (fx := fx') (w_H W3) _ _ msC 26%bv HS3);
            replace (sr_get (ss_regs ssC) 26%bv) with (SOff 32 0) by (vm_compute; reflexivity); cbn [sv_denot];
            rewrite E332, unsigned_lit_small by (unfold LO_WA; clear - F4 Fc CL; lia); rewrite Z.add_0_r; reflexivity|].
    split.
    { apply (o2_mem2_carry B MT XM_LIB XN_LIB MS la_nul LF_MO_SET LF_MO_OP (fun _ => False) i md mk P N kbs
        (o2l_mbs2 mbs n t) gbs T3 SH_M cx fp k2 ly3 S3 W3 ms2 md2 msC md5 HM2 SH_M_len KC (fun a _ H => H) HGC Fd5 Fs5);
        rewrite KR by (vm_compute; reflexivity); reflexivity. }
    split; [rewrite KR by (vm_compute; reflexivity); cbn [ms_regs ms2 mkst]; rewrite P23, Q23; exact R23|].
    split; [rewrite (o2l_reqs2 mbs n t HLm ltac:(lia) Hl11 Dmwf); exact Hrq|].
    rewrite (o2l_marks2 mbs n t HLm eq_refl ltac:(lia) Hl11 Hnz), Hmm.
    destruct Hare as (_ & Hmn). rewrite Hmn. symmetry.
    apply o2l_rem_new; [lia | lia | exact Hne].
Qed.

End a.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module paths and module names changed; 493 of its 545 lines of code are new or changed and 352 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...): op_refused
   (+0x958) at its call of mark_quietly (0x831f8, ra 0x831fc = +0xa28), a0 = the marks block or NULL and a1 =
   .str.1 or NULL: the opening call (the kept set is empty) or a later one (it holds the FILE), mark_quietly's
   answer -22 = -EINVAL (link_spec.v mark_core on a NULL or empty name), the cut at its return, then
   LLVMFuzzerTestOneInputOp5C.v's o5c_after_mq.

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
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Local Notation AFL := AF_LLVMFuzzerTestOneInput.

(* mark_lib on a NULL or empty name: -EINVAL, nothing kept, nothing sent (link_spec.v mark_core) *)
Lemma o5m_lib_refused : forall tab nm marks reqs K, (nm = None \/ nm = Some []) ->
  mark_lib tab nm marks reqs K = Mres (- E_INVAL) marks reqs K.
Proof. intros tab nm marks reqs K [-> | ->]; reflexivity. Qed.

Lemma o5m_mk_names_len : forall gbs, 0 <= mk_n gbs -> Z.of_nat (length (mk_names gbs)) = mk_n gbs.
Proof. intros gbs H. unfold mk_names. rewrite length_map, length_seq. lia. Qed.

Lemma o5m_nk_sent_len : forall kbs, 0 <= nk_n_sent kbs -> Z.of_nat (length (nk_sent kbs)) = nk_n_sent kbs.
Proof. intros kbs H. unfold nk_sent. rewrite length_map, length_seq. lia. Qed.

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
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
Hypothesis HV : LinkVals (L := link_listing).
Hypothesis MT_LE : forall S S' m, mo_le MT S S' m.
Hypothesis MT_OK : forall S m, mo_ok MT S m.
Hypothesis MQO : forall fx0 : YK11.FPState,
  @mark_quietly_acontract_open fx0 rc SK pa_segs PCAP_RLO PCAP_RHI B MT (mo_malloc MT AMF_BLOCK) LF_CTX
    (fun _ => True) (mq_ledpost B).
Hypothesis MQA : forall fx0 : YK11.FPState,
  @mark_quietly_acontract_again fx0 rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CM : forall fx0 : YK11.FPState, @check_mark_acontract fx0 rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CR : forall fx0 : YK11.FPState, @check_requests_acontract fx0 rc SK pa_segs PCAP_RLO PCAP_RHI B.

#[local] Abbreviation BASEF cx := (@lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Abbreviation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).
#[local] Abbreviation FROM POST GI :=
  (@lf_from fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END POST GI).
#[local] Abbreviation TAIL i := (lf_tail_inv B MT MS la_nul LF_MO_SET LF_MO_OP i).

(* the FILE globals mark_quietly's opening arm writes miss every footprint of the cut but the FILE's *)
Lemma o5m_Fopen_miss : forall cx fp md mk ly3 S3 (W3 : world SEGS) mem3 md3 a,
  la_nul = LA_NUL -> MS = link_amf ->
  AR SEGS B ly3 S3 W3 mem3 md3 -> In (LF_CID, fp) (frames S3) ->
  (forall c q, frame_addr ly3 c q = frame_addr (c_ly cx) c q) ->
  YCbq.off_img md MD_SIZE -> YCbq.off_img mk MK_SIZE -> 4096 <= md -> 4096 <= mk ->
  (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3)) ->
  alloc_ceiling + LLVMF_STK - 432 <= lf_sp1 cx -> lf_sp1 cx <= spZ (c_regs cx) - 416 ->
  (LA_G_SINK <= a < LA_G_SINK + 8 \/ LA_G_SAID <= a < LA_G_SAID + SAID_SIZE \/ LA_G_SAY <= a < LA_G_SAY + 8 \/
   LA_OFL_HEAD <= a < LA_OFL_HEAD + 8) ->
  ~ lf_saved_fp cx a /\ ~ lf_slots_fp cx a /\ ~ lf_cur_fp cx a /\
  ~ (lf_F cx fp <= a < lf_F cx fp + 1024 \/ lf_SH cx fp <= a < lf_SH cx fp + 128) /\
  ~ lf_data_fp_ro md mk a /\ ~ in_roP SEGS PCAP_RLO PCAP_RHI a /\ ~ (la_nul <= a < la_nul + 1) /\
  ~ amf_env_addr MS a /\ ~ (c_p cx <= a < c_p cx + c_n cx) /\
  ~ (exists x, (md <= x < md + MD_SIZE \/ mk <= x < mk + MK_SIZE) /\ a = shadow_of_addr SHADOW_OFF x).
Proof.
  intros cx fp md mk ly3 S3 W3 mem3 md3 a HLN HMS HAR Hin Hfa Hmdt Hmkt Hmd4 Hmk4 HPB Hlo Hhi Ha.
  unfold YCbq.off_img in Hmdt, Hmkt.
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (Ha' : LA_G_SINK <= a < LA_OFL_HEAD + 8)
    by (unfold LA_G_SINK, LA_G_SAID, SAID_SIZE, LA_G_SAY, LA_OFL_HEAD in *; lia).
  assert (Hi : in_img SEGS a) by exact (mqp_file_img HSEGS a Ha').
  assert (HG : inG G_HARNESS a).
  { unfold inG, G_HARNESS. unfold LA_G_SINK, LA_G_SAID, SAID_SIZE, LA_G_SAY, LA_OFL_HEAD in Ha.
    destruct Ha as [Ha | [Ha | [Ha | Ha]]];
      repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd];
                     unfold LA_G_NL, LA_G_NAMES, LA_LONG_ALIAS, LA_G_SINK, LA_G_SAID, LA_G_SAY, LA_OFL_HEAD; lia
                   | apply Exists_cons_tl ]. }
  pose proof (lf_sp1_le cx) as (P1 & P2).
  unfold LA_G_SINK, LA_OFL_HEAD in Ha'.
  split; [unfold lf_saved_fp, LF_MFRAME, LLVMF_STK in *; lia|].
  split; [unfold lf_slots_fp, LLVMF_STK in *; lia|].
  split; [unfold lf_cur_fp, LLVMF_STK in *; lia|].
  split; [intros Hf; destruct (kp_frame_place B LAWS cx fp ly3 S3 W3 mem3 md3 a HAR Hin Hfa Hf) as (Hni & _);
          exact (Hni Hi)|].
  split; [unfold lf_data_fp_ro, LA_G_NL, NK_SIZE, LA_G_NAMES, G_NAMES_SIZE, LA_LONG_ALIAS, LA_ODD, MD_SIZE, MK_SIZE,
            YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia|].
  split; [exact (ar_not_ro_G HSEGS a HG)|].
  split; [rewrite HLN; unfold LA_NUL, LA_LONG_ALIAS; lia|].
  split; [rewrite HMS; cbv [amf_env_addr link_amf amf_threaded amf_need_locks amf_ofl_lock];
          unfold LA_G_SINK, LA_G_SAID, SAID_SIZE, LA_G_SAY, LA_OFL_HEAD in Ha; lia|].
  split; [intros Hp; destruct (kp_blk_place B LAWS ly3 S3 W3 mem3 md3 (c_p cx) (c_n cx) a HAR (HPB ltac:(lia))
            ltac:(unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia)) as (Hni & _); exact (Hni Hi)|].
  intros (x & Hx & ->). unfold shadow_of_addr, SHADOW_OFF in Ha'.
  assert (0 <= x) by lia. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). lia.
Qed.


(* the kept FILE block's bytes miss every footprint of the cut but the FILE's *)
Lemma o5m_Fblk_miss : forall cx fp md mk f ly3 S3 (W3 : world SEGS) mem3 md3 a,
  la_nul = LA_NUL -> MS = link_amf ->
  AR SEGS B ly3 S3 W3 mem3 md3 -> In (LF_CID, fp) (frames S3) ->
  (forall c q, frame_addr ly3 c q = frame_addr (c_ly cx) c q) ->
  In (md, MD_SIZE) (ablocks B ly3 S3) -> In (mk, MK_SIZE) (ablocks B ly3 S3) -> In (f, AMF_BLOCK) (ablocks B ly3 S3) ->
  (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3) /\ (c_p cx, c_n cx) <> (f, AMF_BLOCK)) ->
  alloc_ceiling + LLVMF_STK - 432 <= lf_sp1 cx ->
  f <= a < f + AMF_BLOCK ->
  ~ lf_saved_fp cx a /\ ~ lf_slots_fp cx a /\ ~ lf_cur_fp cx a /\
  ~ (lf_F cx fp <= a < lf_F cx fp + 1024 \/ lf_SH cx fp <= a < lf_SH cx fp + 128) /\
  ~ lf_data_fp_ro md mk a /\ ~ in_roP SEGS PCAP_RLO PCAP_RHI a /\ ~ (la_nul <= a < la_nul + 1) /\
  ~ amf_env_addr MS a /\ ~ (c_p cx <= a < c_p cx + c_n cx) /\
  ~ (exists x, (md <= x < md + MD_SIZE \/ mk <= x < mk + MK_SIZE) /\ a = shadow_of_addr SHADOW_OFF x).
Proof.
  intros cx fp md mk f ly3 S3 W3 mem3 md3 a HLN HMS HAR Hin Hfa Bmd Bmk Bf HPB Hlo Ha.
  pose proof asan_consts as ((C1a & C1b) & _).
  destruct (lf_img_facts B MS la_nul HSEGS TB HMS HLN) as (IMG & RIMG).
  destruct (kp_blk_place B LAWS ly3 S3 W3 mem3 md3 f AMF_BLOCK a HAR Bf
    ltac:(change (req_size AMF_BLOCK) with 1304; unfold AMF_BLOCK in Ha; lia)) as (Hni & Hc).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ f AMF_BLOCK HAR Bf) as (_ & Hf4 & _ & Hfapp & _).
  change (req_size AMF_BLOCK) with 1304 in Hfapp.
  assert (SEP : forall b n, In (b, n) (ablocks B ly3 S3) -> (b, n) <> (f, AMF_BLOCK) ->
                  b + req_size n <= f \/ f + 1304 <= b).
  { intros b n Hb Hne. pose proof (sep_blocks _ _ LAWS _ _ _ _ _ b n f AMF_BLOCK HAR Hb Bf Hne) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. change (req_size AMF_BLOCK) with 1304 in D. exact D. }
  assert (IMGX : forall x, lf_img_fp MS la_nul x -> x <> a).
  { intros x Hx E. subst x. exact (Hni (proj1 (IMG a Hx))). }
  pose proof (lf_sp1_le cx) as (P1 & P2).
  split; [unfold lf_saved_fp, LF_MFRAME, LLVMF_STK in *; lia|].
  split; [unfold lf_slots_fp, LLVMF_STK in *; lia|].
  split; [unfold lf_cur_fp, LLVMF_STK in *; lia|].
  split.
  { intros [Hf | Hf].
    - destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as (Hsep & _).
      apply YG0s.pairwise_app_inv in Hsep as (_ & _ & Hcr).
      pose proof (Hcr (f, req_size AMF_BLOCK) (frame_addr ly3 LF_CID fp, fs_frame_bytes LF_CID)
        ltac:(apply in_map_iff; exists (f, AMF_BLOCK); split; [reflexivity | exact Bf])
        ltac:(apply in_map_iff; exists (LF_CID, fp); split; [reflexivity | exact Hin])) as D.
      unfold zdisjoint in D. cbn [fst snd] in D. change (req_size AMF_BLOCK) with 1304 in D.
      change (fs_frame_bytes LF_CID) with 1024 in D. rewrite (Hfa LF_CID fp) in D. unfold lf_F in Hf.
      unfold AMF_BLOCK in Ha. lia.
    - pose proof (al_sep _ _ LAWS _ _ _ _ _ HAR) as (_ & HFS). rewrite Forall_forall in HFS.
      pose proof (HFS (LF_CID, fp) Hin) as (HF1 & HF2). cbn [fst snd] in HF1, HF2.
      change (fs_frame_bytes LF_CID) with 1024 in HF1, HF2. rewrite (Hfa LF_CID fp) in HF1, HF2.
      unfold lf_SH, lf_F, shadow_of_addr in Hf. pose proof (ASAN_CEIL_range) as (CR1 & _).
      unfold in_app, kLowShadowBeg, kHighMemBeg, AMF_BLOCK in Hfapp, Ha. unfold ASAN_CEIL in *.
      unfold SHADOW_OFF in Hf. clear - Hfapp Ha HF1 HF2 Hf CR1. lia. }
  split.
  { unfold lf_data_fp_ro. intros [H | [H | [H | [H | [H | H]]]]].
    - apply (IMGX a); [left; unfold NK_SIZE in *; lia | reflexivity].
    - apply (IMGX a); [right; left; exact H | reflexivity].
    - apply (IMGX a); [right; right; left; exact H | reflexivity].
    - destruct (SEP md MD_SIZE Bmd ltac:(intros E; injection E as _ E; unfold MD_SIZE, AMF_BLOCK in E; lia)) as [D | D];
        change (req_size MD_SIZE) with 8856 in D; unfold MD_SIZE, AMF_BLOCK in *; lia.
    - destruct (SEP mk MK_SIZE Bmk ltac:(intros E; injection E as _ E; unfold MK_SIZE, AMF_BLOCK in E; lia)) as [D | D];
        change (req_size MK_SIZE) with 516 in D; unfold MK_SIZE, AMF_BLOCK in *; lia.
    - apply (IMGX a); [right; right; right; right; right; right; exact H | reflexivity]. }
  split; [intros [(s & Hs & _ & Hr) | Hr]; apply Hni; [exists s; split; [exact Hs | exact Hr] | exact (RIMG a Hr)]|].
  split; [intros H; apply (IMGX a); [right; right; right; right; right; left; exact H | reflexivity]|].
  split; [intros H; apply (IMGX a); [right; right; right; right; left; exact H | reflexivity]|].
  split.
  { intros Hp. destruct (HPB ltac:(lia)) as (Hpin & Hne).
    destruct (SEP _ _ Hpin Hne) as [D | D]; unfold req_size in D; destruct (Z.eqb_spec (c_n cx) 0); unfold AMF_BLOCK in *; lia. }
  intros (x & Hx & ->).
  pose proof (ASAN_CEIL_range) as (CR1 & _).
  assert (Hx0 : 0 <= x < alloc_ceiling).
  { destruct Hx as [Hx | Hx].
    - destruct (al_blocks _ _ LAWS _ _ _ _ _ md MD_SIZE HAR Bmd) as (_ & H4 & Hcx & _).
      change (req_size MD_SIZE) with 8856 in Hcx. unfold MD_SIZE in Hx. lia.
    - destruct (al_blocks _ _ LAWS _ _ _ _ _ mk MK_SIZE HAR Bmk) as (_ & H4 & Hcx & _).
      change (req_size MK_SIZE) with 516 in Hcx. unfold MK_SIZE in Hx. lia. }
  unfold shadow_of_addr in Ha. unfold in_app, kLowShadowBeg, kHighMemBeg, AMF_BLOCK in Hfapp, Ha.
  unfold ASAN_CEIL in *. unfold SHADOW_OFF in Ha. clear - Hfapp Ha Hx0 CR1.
  pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
  lia.
Qed.

(* the payload block is not the kept FILE block *)
Lemma o5m_input_ne_file : forall cx own f ly3 S3 (W3 : world SEGS) mem3 md3,
  BASEF cx -> AR SEGS B ly3 S3 W3 mem3 md3 -> lf_bl B cx own [(f, AMF_BLOCK)] ly3 S3 ->
  0 < c_n cx -> (c_p cx, c_n cx) <> (f, AMF_BLOCK).
Proof.
  intros cx own f ly3 S3 W3 mem3 md3 HB HAR (D & HT & HP) Hn E.
  pose proof HB as (HPRE & _).
  pose proof HPRE as (_ & _ & _ & _ & Hinp & _ & _ & _ & _ & _ & _ & _ & _ & Hnot & _).
  destruct Hinp as [(Hn0 & _) | (_ & Hinp)]; [lia|].
  destruct (c_T cx) as [|t0 [|t1 tr]] eqn:EcT.
  - cbn [app] in HT. subst D.
    destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as (Hsep & _).
    apply YG0s.pairwise_app_inv in Hsep as (Hsep & _ & _).
    assert (ND : List.NoDup (ablocks B ly3 S3)).
    { apply (mq_pw_nodup (fun b => (fst b, req_size (snd b))) _ Hsep).
      intros x Hx. cbn [snd]. unfold req_size. destruct (Z.eqb_spec (snd x) 0); [lia|].
      destruct (al_blocks _ _ LAWS _ _ _ _ _ (fst x) (snd x) HAR ltac:(destruct x; exact Hx)) as (_ & _ & _ & _ & _ & _ & Hn').
      lia. }
    pose proof (Permutation_NoDup HP ND) as ND'.
    apply NoDup_app_remove_l in ND'. cbn [app] in ND'. apply List.NoDup_cons_iff in ND' as (Hn' & _).
    apply Hn'. rewrite <- E. exact Hinp.
  - apply (Hnot Hn). rewrite E. left. cbn [app] in HT. injection HT as -> _. reflexivity.
  - cbn [app] in HT. discriminate HT.
Qed.

(* the write sets of mark_quietly's two arms, by range *)
Lemma o5m_E_open : forall (regs : bvmap 5 word) m mk a, 0 < mk ->
  (aarg regs 0 = 0 \/ aarg regs 0 = mk) -> inFP (mark_quietly_awr_open regs m) a ->
  (LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4) \/ (aarg regs 0 = mk /\ mk <= a < mk + MK_SIZE) \/
  (LA_G_SINK <= a < LA_G_SINK + 8 \/ LA_G_SAID <= a < LA_G_SAID + SAID_SIZE \/ LA_G_SAY <= a < LA_G_SAY + 8 \/
   LA_OFL_HEAD <= a < LA_OFL_HEAD + 8).
Proof.
  intros regs m mk a Hmk Ha0 (r & Hr & Ha). unfold mark_quietly_awr_open in Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; cbn [fst snd] in Ha.
  - left. exact Ha.
  - unfold aivl in Ha. cbn [fst snd] in Ha. destruct Ha0 as [E | E]; rewrite E in Ha.
    + cbn in Ha. lia.
    + right; left. split; [exact E|]. destruct (Z.eqb_spec mk 0); lia.
  - right; right; left. exact Ha.
  - right; right; right; left. exact Ha.
  - right; right; right; right; left. exact Ha.
  - right; right; right; right; right. exact Ha.
Qed.

Lemma o5m_E_again : forall (regs : bvmap 5 word) m mk f a, 0 < mk -> f <> 0 ->
  (aarg regs 0 = 0 \/ aarg regs 0 = mk) -> inFP (mark_quietly_awr_again f regs m) a ->
  (LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4) \/ (aarg regs 0 = mk /\ mk <= a < mk + MK_SIZE) \/
  (LA_G_SAID <= a < LA_G_SAID + SAID_SIZE \/ f <= a < f + AMF_BLOCK).
Proof.
  intros regs m mk f a Hmk Hf Ha0 (r & Hr & Ha). unfold mark_quietly_awr_again in Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Ha.
  - left. exact Ha.
  - unfold aivl in Ha. cbn [fst snd] in Ha. destruct Ha0 as [E | E]; rewrite E in Ha.
    + cbn in Ha. lia.
    + right; left. split; [exact E|]. destruct (Z.eqb_spec mk 0); lia.
  - right; right; left. exact Ha.
  - right; right; right. unfold aivl in Ha. cbn [fst snd] in Ha. destruct (Z.eqb_spec f 0); [contradiction | lia].
Qed.

(* the name op_refused passes: NULL or .str.1 = "" *)
Lemma o5m_names : forall ly S (W : world SEGS) mem mdl (regs : bvmap 5 word) nm mk fb fn,
  AR SEGS B ly S W mem mdl -> arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  LA_G_NL <= spZ regs - MARK_QUIETLY_AK -> YCbq.off_img mk MK_SIZE ->
  (aarg regs 0 = 0 \/ aarg regs 0 = mk) ->
  ((aarg regs 1 = 0 /\ nm = None) \/ (aarg regs 1 = LA_STR1 /\ nm = Some [])) ->
  (fb + fn <= 0x10000 \/ YImgTop.IMG_TOP <= fb) -> 0 <= fn ->
  astr_arg SEGS (rdW W mem) (aarg regs 1) nm /\
  amk_name_ok SEGS B regs MARK_QUIETLY_AK fb fn (rdW W mem) nm /\
  (forall s, nm = Some s -> aarg regs 1 + Z.of_nat (length s) + 8 <= LA_G_SINK) /\
  aarg regs 1 < alloc_ceiling /\
  (forall a, aarg regs 1 <> 0 -> forall s, acstr_at SEGS (rdW W mem) (aarg regs 1) s ->
     aarg regs 1 <= a <= aarg regs 1 + Z.of_nat (length s) -> akb SEGS B ly S (spZ regs - MARK_QUIETLY_AK) (spZ regs) a).
Proof.
  intros ly S W mem mdl regs nm mk fb fn HAR HRO HK Hmk Ha0 Ha1 Hfb Hfn.
  pose proof asan_consts as ((C1a & C1b) & _).
  pose proof (mq_img_here B TB HSEGS) as KI. unfold mq_img_b in KI.
  repeat match type of KI with (_ && _)%bool = true => apply andb_prop in KI as [KI ?] end.
  match goal with H : kp_akbs_b _ _ _ LA_STR1 1 = true |- _ => rename H into KA end.
  rewrite forallb_forall in KI.
  pose proof (KI (LA_STR1, []) ltac:(cbn [mq_pol In]; repeat (first [left; reflexivity | right]))) as Hk.
  cbn [fst snd map] in Hk.
  destruct (mq_rt_kstr B TB ly S W mem mdl regs MARK_QUIETLY_AK LA_STR1 [] HAR HRO Hk HK) as (Hs1 & Hrt).
  cbn [map] in Hs1, Hrt.
  pose proof (ts_errno B TB) as HE.
  destruct Ha1 as [(A1 & ->) | (A1 & ->)].
  - split; [cbn; exact A1|]. split; [intros s Hs; discriminate|]. split; [intros s Hs; discriminate|].
    split; [rewrite A1; lia|]. intros a Ha; contradiction.
  - split; [cbn; rewrite A1; split; [unfold LA_STR1; lia | exact Hs1]|].
    split.
    { intros s Hs. injection Hs as <-. cbn [length Z.of_nat]. rewrite A1.
      split; [lia|]. split; [exact Hrt|].
      split; [unfold apart_gnl, LA_STR1, LA_G_NL; left; lia|].
      split; [unfold apart, LA_STR1, YImgTop.IMG_TOP in *; lia|].
      split; [unfold apart; rewrite HE; unfold TFIB_ERRNO, LA_STR1; right; lia|].
      intros Hnz. unfold apart, LA_STR1, MK_SIZE, YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in *.
      destruct Ha0 as [E | E]; [contradiction | rewrite E; lia]. }
    split; [intros s Hs; injection Hs as <-; cbn; rewrite A1; unfold LA_STR1, LA_G_SINK; lia|].
    split; [rewrite A1; unfold LA_STR1; lia|].
    intros a _ s Hs Ha. rewrite A1 in Hs, Ha.
    pose proof (kp_acstr_unique _ _ _ _ _ Hs Hs1) as Es. subst s. cbn [length Z.of_nat] in Ha.
    exact (kp_akbs_of_b B ly S _ _ LA_STR1 1 a KA ltac:(cbn; lia)).
Qed.

(* the cut at mark_quietly's return (+0xa28): its answer is -22 and the data keep their relations; then
   o5c_after_mq *)
Lemma o5m_after : forall POST i cx (fx' : YK11.FPState) fp k' ly2 S2 (W2 : world SEGS) (regs regs2 : bvmap 5 word)
    mem2 md2 md mk P N kbs kbs' mbs gbs gbs' T3' nm (ms3 : machine_state),
  0 <= i <= 47 -> FROM POST (TAIL i) ->
  BASEF cx -> @BoxBase.fxr fx fx' -> JRN cx fp ly2 S2 W2 mem2 md2 k' -> frames S2 = [(LF_CID, fp)] ->
  ms_regs ms3 = regs -> lf_core cx ms3 -> lf_lregs cx md fp i ms3 ->
  getr regs 1 = Z_to_bv 64 (BASE + (AFL + 0xa28)) ->
  aregs_preserved regs regs2 ->
  (nm = None \/ nm = Some []) ->
  mqp_rc regs regs2 mk kbs kbs' gbs gbs' nm -> marks_wf gbs' ->
  (marks_are gbs' mbs -> lf_data cx md mk kbs' mbs gbs' (rdW W2 mem2)) ->
  marks_are gbs mbs -> marks_wf gbs -> requests_are kbs mbs -> nk_n_sent kbs = 0 -> nk_opened kbs <= 64 * i ->
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
    Hi NEXT HB Hfx HJ2 Hfr2 Hrg Hcore Hlr R1 Hpr Hnm (Rnull & Rmk) Hkwf2 Hdat2f Hare Hkwf Hreq Hns Hop
    Hsv2 Hhd2 Hfsh2 Hsl2 Hcur2 Hjbk2 Hblk2.
  set (ms2 := @mkst fx' regs2 (getr regs 1) mem2 (seg_rom SEGS)) in *.
  assert (KR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr (ms_regs ms2) r = getr (ms_regs ms3) r).
  { intros r Hr. cbn [ms2 ms_regs mkst]. rewrite Hrg. exact (o5c_pres _ _ Hpr r Hr). }
  (* the answer and the data *)
  assert (HD : getr regs2 10 = w64 (- E_INVAL) /\ marks_are gbs' mbs /\ requests_are kbs' mbs /\
               nk_opened kbs' <= 64 * (i + 1)).
  { destruct (Z.eq_dec (aarg regs 0) 0) as [A0 | A0].
    - destruct (Rnull A0) as (-> & -> & Rrc). split; [exact Rrc|]. split; [exact Hare|]. split; [exact Hreq | lia].
    - pose proof (Rmk A0) as RM. cbv zeta in RM. rewrite (o5m_lib_refused _ _ _ _ _ Hnm) in RM.
      cbn [m_rc m_marks m_reqs m_state] in RM.
      destruct RM as (Rrc & Hnames & Hn & _ & _ & _ & _ & Hsent & Hns' & Hopd).
      split; [exact Rrc|].
      split.
      { destruct Hare as (E1 & E2). split; [|rewrite Hnames; exact E2].
        rewrite Hn. destruct Hkwf as (Hk0 & _). rewrite (o5m_mk_names_len gbs ltac:(lia)). exact E1. }
      split; [|lia].
      { destruct Hreq as (E1 & _). unfold requests_are.
        assert (Z0 : nk_n_sent kbs' = 0) by (rewrite Hns', (o5m_nk_sent_len kbs ltac:(lia)); exact Hns).
        rewrite Z0. split; [lia | intros j Hj; lia]. } }
  destruct HD as (Hrc & Hare2 & Hreq2 & Hop2).
  pose proof Hcore as (C2 & C8 & C9 & C3 & C4).
  pose proof Hlr as (L19 & L21 & L22 & L23 & L24 & L25 & L26 & L27).
  apply (o5c_after_mq SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS HV CM CR
    POST i cx fx' fp k' ly2 S2 W2 ms2 md2 md mk P N kbs' mbs gbs' T3' Hi NEXT HB Hfx HJ2 Hfr2).
  - unfold lf_shape. cbn [ms2 mkst ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr].
    split; [rewrite R1; reflexivity|]. repeat split; reflexivity.
  - repeat split; rewrite KR by (unfold acallee_saved; first [ (vm_compute; lia) | (cbn; lia) | (simpl; lia)
      | (vm_compute; right; right; right; right; right; split; discriminate) ]); assumption.
  - repeat split; rewrite KR by (unfold acallee_saved; first [ (vm_compute; lia) | (cbn; lia) | (simpl; lia)
      | (vm_compute; right; right; right; right; right; split; discriminate) ]); assumption.
  - exact Hrc.
  - exact Hsv2.
  - exact Hhd2.
  - exact Hfsh2.
  - exact Hsl2.
  - exact Hcur2.
  - exact Hjbk2.
  - exact Hblk2.
  - exact (Hdat2f Hare2).
  - exact Hreq2.
  - exact Hop2.
Qed.

(* the journal counters of operation i are within those of operation i + 1 *)
Lemma o5m_jbk_next : forall cx fp k2 i ly S W ms mdl T3 own,
  0 <= i -> 
  lf_jbk B MT MS la_nul cx fp k2 (lf_ev i) (lf_mo LF_MO_SET LF_MO_OP i) (lf_wl i) LF_LIVE_HELD ly S W ms mdl T3 own ->
  lf_jbk B MT MS la_nul cx fp k2 (lf_ev (i + 1)) (lf_mo LF_MO_SET LF_MO_OP (i + 1)) (lf_wl (i + 1)) LF_LIVE_HELD
    ly S W ms mdl T3 own.
Proof.
  intros cx fp k2 i ly S W ms mdl T3 own Hi (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & Jrest).
  split; [unfold lf_ev, LF_EV_OP in *; lia|]. split; [exact J2|]. split; [exact J3|]. split; [exact J4|].
  split; [exact J5|]. split; [exact J6|]. split; [apply MT_LE|].
  split; [unfold lf_wl, LF_WILD_OP in *; rewrite Z2Nat.inj_add by lia; lia | exact Jrest].
Qed.

(* op_refused at its call of mark_quietly *)
Lemma o5m_call : forall POST i cx (fy : YK11.FPState) fp k2 ly3 S3 W3 ms3 md3 md mk P N kbs mbs gbs T3
    (nm : option (list byte)),
  0 <= i <= 47 -> FROM POST (TAIL i) ->
  BASEF cx -> @BoxBase.fxr fx fy -> JRN cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 -> frames S3 = [(LF_CID, fp)] ->
  ms3 = @mkst fy (ms_regs ms3) (w64 MARK_QUIETLY_A) (ms_mem ms3) (seg_rom SEGS) ->
  lf_core cx ms3 -> lf_lregs cx md fp i ms3 ->
  getr (ms_regs ms3) 1 = Z_to_bv 64 (BASE + (AFL + 0xa28)) ->
  (aarg (ms_regs ms3) 0 = 0 \/ aarg (ms_regs ms3) 0 = mk) ->
  ((aarg (ms_regs ms3) 1 = 0 /\ nm = None) \/ (aarg (ms_regs ms3) 1 = LA_STR1 /\ nm = Some [])) ->
  lf_saved cx W3 ms3 -> lf_header cx fp W3 ms3 -> lf_fshadow cx fp W3 ms3 LF_SH0 ->
  lf_slots cx md mk fp W3 ms3 -> lf_cur cx W3 ms3 P N ->
  lf_jbk B MT MS la_nul cx fp k2 (lf_ev i) (lf_mo LF_MO_SET LF_MO_OP i) (lf_wl i) LF_LIVE_HELD ly3 S3 W3 ms3 md3 T3
    [(md, MD_SIZE); (mk, MK_SIZE)] ->
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) ->
  lf_data cx md mk kbs mbs gbs (rdW W3 (ms_mem ms3)) ->
  requests_are kbs mbs -> nk_n_sent kbs = 0 -> nk_opened kbs <= 64 * i ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros POST i cx fy fp k2 ly3 S3 W3 ms3 md3 md mk P N kbs mbs gbs T3 nm Hi NEXT HB Hfx HJ Hfr Hms Hcore Hlr R1
    Ha0 Ha1 Hsv Hhd Hfsh Hsl Hcur Hjbk Hblk Hdat Hreq Hns Hop.
  pose proof asan_consts as ((C1a & C1b) & _).
  pose proof HB as (HPRE & Hfz & HGX & HLN & HMS & _).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR3).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & Hs16 & Hlo & H47').
  pose proof Hcore as (C2 & C8 & C9 & C3 & C4).
  pose proof Hjbk as (J1 & JL & Jfa & J3 & J4 & J5 & J6 & J7 & Jgi & Jenv & Jbl & Jinc & Jla & HRO & Jpl & Jpv).
  pose proof Hblk as (Bmd & Bmk & _ & _ & _ & _ & _ & _ & Bmdt & Bmkt & _).
  pose proof Hdat as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Dkwf & Dare & _).
  pose proof (lf_data_nm_of _ _ _ _ _ _ _ Hdat) as Hdatn.
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
  assert (R1' : getr (ms_regs ms3) 1 = Z_to_bv 64 (link_text + (AFL + 0xa28))) by (rewrite R1, (lv_text HV); reflexivity).
  assert (Hsite : In (AFL + 0xa28) LF_MARK_SITES) by (left; reflexivity).
  assert (Hop2 : nk_opened kbs + 2 < 2 ^ 31) by lia.
  assert (Hfrm : YK0o.frm_zero (@YK11.fp_csr fy)) by exact (fxr_frm0 fx fy Hfz Hfx).
  assert (HK : LA_G_NL <= spZ (ms_regs ms3) - MARK_QUIETLY_AK)
    by (rewrite Hsp, HAK; unfold LLVMF_STK, LA_G_NL in *; clia).
  assert (Hev : k2 + 1 <= EV_LIB) by (pose proof lf_ev_bound as EB; unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *; lia).
  assert (Hnmr : nm = None \/ nm = Some []) by (destruct Ha1 as [(_ & ->) | (_ & ->)]; [left | right]; reflexivity).
  assert (HPB : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by (intros Hn; exact (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
          cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ Hn)).
  rewrite Hms. change (mkCfg (mkst (ms_regs ms3) (w64 MARK_QUIETLY_A) (ms_mem ms3) (seg_rom SEGS)) md3)
    with (cfg_at SEGS MARK_QUIETLY_A (ms_regs ms3) (ms_mem ms3) md3).
  destruct (amf_gi_shape SEGS MS T3 _ Jgi) as [ET | (f & ET)]; subst T3.
  - (* the opening call *)
    destruct Jgi as [(Hh0 & _) | (f & _ & HT & _)]; [|discriminate HT].
    destruct (o5m_names ly3 S3 W3 (ms_mem ms3) md3 (ms_regs ms3) nm mk 0 0 HAR3 HRO HK Bmkt Ha0 Ha1
      ltac:(left; lia) ltac:(lia)) as (Hnm & Hnok & Hnlo & Ha1c & Hnakb).
    eapply apostF_continue.
    { rewrite HMS in Hh0, Jenv.
      exact (lf_mq_open_call SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS MT_OK MQO
        fy cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 (ms_regs ms3) md mk kbs mbs gbs (AFL + 0xa28) nm HB HJ Hfr Hfrm Hev Jbl
        HRO Hblk Hdatn Hh0 Jenv Hop2 H8 H16' Hsp Hs0 C3 C4 (lv_text HV) R1' Hsite Ha0 Ha1c Hnm Hnok Hnlo
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
      HB Hfr HJ HJ2 Hsp Hkp Hsk Pmd2 Pmk2 Ha0
      (fun a Ha => o5m_E_open (ms_regs ms3) _ mk a Bmk0 Ha0 Ha)
      (fun a Ha => o5m_Fopen_miss cx fp md mk ly3 S3 W3 (ms_mem ms3) md3 a HLN HMS HAR3 Hin Jfa Bmdt Bmkt Bmd4 Bmk4 HPB Hlo
                     ltac:(clia) Ha)
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
    apply (o5m_after POST i cx fx' fp (k2 + 1) ly2 S2 W2 (ms_regs ms3) regs2 mem2 md2 md mk P N kbs kbs' mbs gbs gbs'
      [(sink, AMF_BLOCK)] nm ms3 Hi NEXT HB (fxr_trans fx fy fx' Hfx Hfxr) HJ2 ltac:(rewrite Hfr2; exact Hfr) eq_refl
      Hcore Hlr R1 Hpr Hnmr Hmrc Hkwf2 Hdat2f Dare Dkwf Hreq Hns Hop Hsv2 Hhd2 Hfsh2 Hsl2 Hcur2 Hjbk2
      (lf_blocks_open B cx md mk ly3 S3 ly2 S2 sink _ Hperm Hblk2)).
  - (* a later call *)
    destruct Jgi as [(_ & HT) | (f' & Hhf & HT & Hamf)]; [discriminate HT|]. injection HT as <-.
    assert (Hfin : In (f, AMF_BLOCK) (ablocks B ly3 S3)) by (apply Jinc; left; reflexivity).
    destruct (blk_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 f AMF_BLOCK HAR3 Hfin) as [Hoff | Hoff];
      change (req_size AMF_BLOCK) with AMF_BLOCK in Hoff; unfold YImgTop.IMG_LO in Hoff.
    all: assert (Hfoff : f + AMF_BLOCK <= 0x10000 \/ YImgTop.IMG_TOP <= f) by lia.
    all: destruct (al_blocks _ _ LAWS _ _ _ _ _ f AMF_BLOCK HAR3 Hfin) as (_ & Hf4 & _).
    all: destruct (o5m_names ly3 S3 W3 (ms_mem ms3) md3 (ms_regs ms3) nm mk f AMF_BLOCK HAR3 HRO HK Bmkt Ha0 Ha1
      Hfoff ltac:(unfold AMF_BLOCK; lia)) as (Hnm & Hnok & Hnlo & _ & Hnakb).
    all: eapply apostF_continue;
      [ rewrite HMS in Hhf, Hamf;
        exact (lf_mq_again_call SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS MQA
          fy cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 (ms_regs ms3) md mk kbs mbs gbs (AFL + 0xa28) nm f HB HJ Hfr Hfrm
          ltac:(lia) Jbl Jinc HRO Hblk Hdatn Hhf Hamf Hop2 H8 H16' Hsp Hs0 C3 C4 (lv_text HV) R1' Hsite Ha0 Hnm Hnok Hnlo
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
      by (intros Hn; split; [exact (HPB Hn) | exact (o5m_input_ne_file cx _ f ly3 S3 W3 (ms_mem ms3) md3 HB HAR3 Jbl Hn)]).
    all: destruct (lf_mq_post_common SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS
      cx fp k2 _ _ _ _ md mk kbs mbs gbs [(f, AMF_BLOCK)] _ P N ly3 S3 W3 ms3 md3 ly2 S2 W2 ms2 md2 (k2 + 0) (ms_regs ms3)
      regs2 _ (fun a => LA_G_SAID <= a < LA_G_SAID + SAID_SIZE \/ f <= a < f + AMF_BLOCK) nm
      HB Hfr HJ HJ2 Hsp Hkp Hsk Pmd2 Pmk2 Ha0
      (fun a Ha => o5m_E_again (ms_regs ms3) _ mk f a Bmk0 Hfnz Ha0 Ha)
      (fun a Ha => match Ha with
                   | or_introl Hs => o5m_Fopen_miss cx fp md mk ly3 S3 W3 (ms_mem ms3) md3 a HLN HMS HAR3 Hin Jfa Bmdt
                                       Bmkt Bmd4 Bmk4 HPB Hlo ltac:(clia) (or_intror (or_introl Hs))
                   | or_intror Hb => o5m_Fblk_miss cx fp md mk f ly3 S3 W3 (ms_mem ms3) md3 a HLN HMS HAR3 Hin Jfa Bmd
                                       Bmk Hfin HPBf Hlo Hb
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
        [ exact (o5m_jbk_next cx fp k2 i ly3 S3 W3 ms3 md3 _ _ ltac:(lia) Hjbk) | exact Hfa2 | unfold lf_ev, LF_EV_OP in *; lia | exact Hs2 | exact Hperm | exact Hfd | exact Hfs
        | exact (mqp_heads_of_au64 MS _ f HMS Hgs Hgy Hgo) | rewrite HMS; exact (proj1 Hmf) | exact HENV | exact HNUL
        | exact HRO2 | exact HPL2 | exact HPV2 ]).
    all: apply (o5m_after POST i cx fx' fp (k2 + 0) ly2 S2 W2 (ms_regs ms3) regs2 mem2 md2 md mk P N kbs kbs' mbs gbs gbs'
      [(f, AMF_BLOCK)] nm ms3 Hi NEXT HB (fxr_trans fx fy fx' Hfx Hfxr) HJ2 ltac:(rewrite Hfr2; exact Hfr) eq_refl
      Hcore Hlr R1 Hpr Hnmr Hmrc Hkwf2 Hdat2f Dare Dkwf Hreq Hns Hop Hsv2 Hhd2 Hfsh2 Hsl2 Hcur2 Hjbk2
      (ar_blocks_leaf B cx md mk _ ly3 S3 ly2 S2 _ Hperm Hblk2)).
Qed.
End b.
End a.

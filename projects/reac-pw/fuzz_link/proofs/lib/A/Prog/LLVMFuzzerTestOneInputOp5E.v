(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module paths and module names changed; 295 of its 340 lines of code are new or changed and 359 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...): op_refused
   (+0x958) at its call of mark_quietly (0x831f8), from the arm's entry cut and what the run from +0x958 to the call
   leaves: the cursor and model_begin's five stores (m + 0, + 4, + 8, + MD_N_REQ, g_nl.n_sent) are the only bytes
   written (`kagree X`), the stored words are the counters model_begin copies, and the registers are the entry's
   but for a0 / a1 / ra. `o5_at_call` re-states the cut there (Keep.v's keep lemmas, Mb.v's lf_data_mb) and hands it
   to LLVMFuzzerTestOneInputOp5M.v's o5m_call.

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
  LLVMFuzzerTestOneInputArmK LLVMFuzzerTestOneInputKpost LLVMFuzzerTestOneInputLp LLVMFuzzerTestOneInputMb
  LLVMFuzzerTestOneInputMq LLVMFuzzerTestOneInputMqCall LLVMFuzzerTestOneInputMqPost LLVMFuzzerTestOneInputOp5C
  LLVMFuzzerTestOneInputOp5M.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
  model_decide_c remember_c reac_code_emit_c reac_served_mark_c mark_quietly_c check_write_c check_mark_c
  check_requests_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Local Notation AFL := AF_LLVMFuzzerTestOneInput.

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

(* every footprint of the cut lies in [0, 2 ^ 64) (Op3K.v u_fp_range, restated) *)
Lemma o5e_fp_range : forall cx fp k2 ev mo wl lv md mk T3 own ly3 S3 (W3 : world SEGS) ms3 md3 a,
  @lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx ->
  ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = [(LF_CID, fp)] ->
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own ->
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) ->
  (lf_saved_fp cx a \/ lf_header_fp cx fp a \/ lf_fshadow_fp cx fp 112 a \/ lf_slots_fp cx a \/
   lf_cur_fp cx a \/ lf_jbk_fp MS la_nul cx T3 a \/ lf_blocks_fp md mk a \/ lf_data_fp md mk a) ->
  0 <= a < 2 ^ 64.
Proof.
  intros cx fp k2 ev mo wl lv md mk T3 own ly3 S3 W3 ms3 md3 a HB HJ Hfr Hjbk Hblk Ha.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as (HPRE & _ & HGX & HLN & HMS & _).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & H16 & Hlo & H47).
  pose proof HJ as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (HAR3 & _).
  pose proof Hjbk as (_ & _ & Hfa & _ & _ & _ & _ & _ & Hgi & _ & _ & Hinc & _ & HRO & _).
  pose proof Hblk as (Bmd & Bmk & _).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 md MD_SIZE HAR3 Bmd) as (_ & Bm4096 & Bmceil & _).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 mk MK_SIZE HAR3 Bmk) as (_ & Bk4096 & Bkceil & _).
  change (req_size MD_SIZE) with 8856 in Bmceil. change (req_size MK_SIZE) with 516 in Bkceil.
  assert (Hin : In (LF_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
  pose proof (al_sep _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 HAR3) as (_ & Hfs).
  rewrite Forall_forall in Hfs. specialize (Hfs (LF_CID, fp) Hin). cbn [fst snd] in Hfs.
  change (fs_frame_bytes LF_CID) with 1024 in Hfs.
  assert (HF : lf_F cx fp = frame_addr ly3 LF_CID fp) by (unfold lf_F; rewrite Hfa; reflexivity).
  assert (RO : forall x, in_roP SEGS PCAP_RLO PCAP_RHI x -> 0 <= x < 2 ^ 64).
  { intros x Hx. pose proof (lf_roP_below_top x Hx) as Ht. unfold YImgTop.IMG_TOP in Ht.
    destruct Hx as [(s & _ & _ & Hs) | Hs]; [pose proof (N2Z.is_nonneg (seg_base s)); clia | unfold PCAP_RLO in Hs; clia]. }
  assert (DV : forall x, 0 <= x <= 2 ^ 47 -> 0 <= x / 8 <= 2 ^ 44).
  { intros x Hx. split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; lia. }
  unfold LLVMF_STK in *.
  destruct Ha as [Ha | [Ha | [Ha | [Ha | [Ha | [Ha | [Ha | Ha]]]]]]].
  - unfold lf_saved_fp in Ha. clia.
  - unfold lf_header_fp in Ha. rewrite HF in Ha. change (fs_frame_bytes LF_CID) with 1024 in Ha. clia.
  - unfold lf_fshadow_fp, lf_SH, shadow_of_addr in Ha. rewrite HF in Ha.
    pose proof (DV (frame_addr ly3 LF_CID fp) ltac:(clia)). unfold SHADOW_OFF in Ha. clia.
  - unfold lf_slots_fp in Ha. clia.
  - unfold lf_cur_fp in Ha. clia.
  - destruct Ha as [Hj | [Hj | [Hj | Hj]]].
    + destruct Hj as [Hj | [Hj | (f & n & Hfn & Hj)]].
      * rewrite HMS in Hj. cbv [amf_head_addr link_amf amf_sink_addr amf_say_addr amf_ofl_head amf_ofl_lock] in Hj. clia.
      * rewrite HMS in Hj. cbv [amf_env_addr link_amf amf_threaded amf_need_locks amf_ofl_lock] in Hj. clia.
      * destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 f n HAR3 (Hinc _ Hfn)) as (_ & Hf4 & Hfc & _).
        assert (Hn : n = AMF_BLOCK).
        { destruct Hgi as [(_ & HT) | (f' & _ & HT & _)]; rewrite HT in Hfn; [destruct Hfn|].
          destruct Hfn as [Hq | []]. injection Hq as _ <-. reflexivity. }
        subst n. change (req_size AMF_BLOCK) with 1304 in Hfc. unfold AMF_BLOCK in Hj. clia.
    + rewrite HLN in Hj. unfold LA_NUL, LA_LONG_ALIAS in Hj. clia.
    + exact (RO a Hj).
    + assert (Hn : 0 < c_n cx) by clia.
      pose proof (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
        cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ Hn) as Hpb.
      destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ HAR3 Hpb) as (_ & Hp4 & Hpc & _).
      unfold req_size in Hpc. destruct (Z.eqb_spec (c_n cx) 0); clia.
  - destruct Ha as [(x & Hx & ->) | (x & Hx & ->)]; unfold shadow_of_addr, MD_SIZE, MK_SIZE in *;
      pose proof (DV x ltac:(clia)); unfold SHADOW_OFF; clia.
  - destruct Ha as [Ha | [Ha | [Ha | [Ha | [Ha | Ha]]]]];
      try (unfold LA_G_NL, NK_SIZE, LA_G_NAMES, G_NAMES_SIZE, LA_LONG_ALIAS, MD_SIZE, MK_SIZE in *; clia).
    exact (RO a Ha).
Qed.

Lemma o5_at_call : forall POST i cx (fy : YK11.FPState) fp k2 ly3 S3 W3 ms3 md3 md mk kbs mbs gbs T3
    (ms' : machine_state) md' (X : Z -> Prop) P' N' (nm : option (list byte)),
  0 <= i <= 47 -> FROM POST (TAIL i) ->
  BASEF cx -> @BoxBase.fxr fx fy ->
  JRN cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 -> frames S3 = [(LF_CID, fp)] ->
  lf_core cx ms3 -> lf_lregs cx md fp i ms3 ->
  lf_saved cx W3 ms3 -> lf_header cx fp W3 ms3 -> lf_fshadow cx fp W3 ms3 LF_SH0 ->
  lf_slots cx md mk fp W3 ms3 ->
  lf_jbk B MT MS la_nul cx fp k2 (lf_ev i) (lf_mo LF_MO_SET LF_MO_OP i) (lf_wl i) LF_LIVE_HELD ly3 S3 W3 ms3 md3 T3
    [(md, MD_SIZE); (mk, MK_SIZE)] ->
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) ->
  lf_data cx md mk kbs mbs gbs (rdW W3 (ms_mem ms3)) ->
  nk_opened kbs <= 64 * i ->
  JRN cx fp ly3 S3 W3 (ms_mem ms') md' k2 ->
  ms' = @mkst fy (ms_regs ms') (w64 MARK_QUIETLY_A) (ms_mem ms') (seg_rom SEGS) ->
  (forall r : bv 5, acallee_saved (bv_unsigned r) -> getr (ms_regs ms') r = getr (ms_regs ms3) r) ->
  getr (ms_regs ms') 1 = Z_to_bv 64 (BASE + (AFL + 0xa28)) ->
  (aarg (ms_regs ms') 0 = 0 \/ aarg (ms_regs ms') 0 = mk) ->
  ((aarg (ms_regs ms') 1 = 0 /\ nm = None) \/ (aarg (ms_regs ms') 1 = LA_STR1 /\ nm = Some [])) ->
  kagree SEGS X (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms')) ->
  (forall a, X a -> 0 <= a < 2 ^ 64 -> lf_cur_fp cx a \/ lf_mb_rng md a) ->
  mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms')) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  abytes SEGS (rdW W3 (ms_mem ms')) (md + MD_SOCKET_ERRNO) (slice kbs NK_SOCKET_ERRNO 4) ->
  abytes SEGS (rdW W3 (ms_mem ms')) (md + MD_SEND_ERRNO) (slice kbs NK_SEND_ERRNO 4) ->
  abytes SEGS (rdW W3 (ms_mem ms')) (md + MD_NEXT) lf_z4 ->
  abytes SEGS (rdW W3 (ms_mem ms')) (md + MD_N_REQ) lf_z4 ->
  abytes SEGS (rdW W3 (ms_mem ms')) (LA_G_NL + NK_N_SENT) lf_z4 ->
  lf_cur cx W3 ms' P' N' ->
  SRr SEGS W3 (mkCfg ms' md') (POST cx).
Proof.
  intros POST i cx fy fp k2 ly3 S3 W3 ms3 md3 md mk kbs mbs gbs T3 ms' md' X P' N' nm Hi NEXT HB Hfx HJ3 Hfr
    Hcore Hlr Hsv Hhd Hfsh Hsl Hjbk Hblk Hdat Hop HJ' Hms KR R1 Ha0 Ha1 KX HX HG Hfd Hfs A1 A2 A3 A4 A5 Hcur.
  pose proof asan_consts as ((C1a & C1b) & _).
  pose proof HB as (HPRE & _ & HGX & HLN & HMS & _).
  destruct (lf_img_facts B MS la_nul HSEGS TB HMS HLN) as (IMG & RIMG).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ3) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR3).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ3) as (Hs1 & Hs16 & Hlo & H47').
  pose proof Hjbk as (J1 & JL & Jfa & J3 & J4 & J5 & J6 & J7 & Jgi & Jenv & Jbl & Jinc & Jla & HRO & Jpl & Jpv).
  pose proof Hblk as (Bmd & Bmk & _ & _ & BmdT & BmkT & _ & _ & Bmdt & Bmkt & Bapmm & Bapmi & Bapki & _).
  assert (Hin : In (LF_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ md MD_SIZE HAR3 Bmd) as (_ & Hmd4 & Hmdc & Hmdapp & _).
  change (req_size MD_SIZE) with 8856 in Hmdc, Hmdapp.
  pose proof (lf_sp1_le cx) as (P1 & P2).
  assert (CV : LA_G_NL = 6146752 /\ NK_N_SENT = 271016 /\ NK_SIZE = 271992 /\ MD_SIZE = 8856 /\ MK_SIZE = 516 /\
               MD_N_REQ = 8336 /\ YImgTop.IMG_LO = 65536 /\ YImgTop.IMG_TOP = 6635520 /\ LF_MFRAME = 416 /\
               LLVMF_STK = LLVMF_STK)
    by (repeat split; reflexivity).
  unfold LLVMF_STK in Hlo, Hceil.
  (* where X lies: the cursor (above s1, below the frame's top) or model_begin's five words (the model block and
     g_nl's n_sent, both below the ceiling) *)
  assert (FPR : forall a, (lf_saved_fp cx a \/ lf_header_fp cx fp a \/ lf_fshadow_fp cx fp 112 a \/ lf_slots_fp cx a \/
      lf_cur_fp cx a \/ lf_jbk_fp MS la_nul cx T3 a \/ lf_blocks_fp md mk a \/ lf_data_fp md mk a) -> 0 <= a < 2 ^ 64)
    by (intros a Ha; exact (o5e_fp_range cx fp k2 _ _ _ _ md mk T3 _ ly3 S3 W3 ms3 md3 a HB HJ3 Hfr Hjbk Hblk Ha)).
  assert (XL : forall a, X a -> 0 <= a < 2 ^ 64 -> (lf_sp1 cx + 0x118 <= a < lf_sp1 cx + 0x128) \/
                 (md <= a < md + 12) \/ (md + 8336 <= a < md + 8340) \/ (6146752 + 271016 <= a < 6146752 + 271020)).
  { intros a Ha Hr. destruct (HX a Ha Hr) as [H | [H | [H | H]]]; unfold lf_cur_fp, MD_N_REQ, LA_G_NL, NK_N_SENT in *; lia. }
  assert (XLO : forall a, X a -> 0 <= a < 2 ^ 64 -> lf_sp1 cx + 0x118 <= a < lf_sp1 cx + 0x128 \/ a < alloc_ceiling).
  { intros a Ha Hr. destruct (XL a Ha Hr) as [H | [H | [H | H]]]; [left; exact H | right; lia | right; lia | right; lia]. }
  (* the frame's pieces *)
  assert (Hsv' : lf_saved cx W3 ms').
  { apply (lf_saved_keep X cx W3 ms3 W3 ms' KX); [|exact Hsv]. intros a Ha HXa.
    pose proof (FPR a ltac:(left; exact Ha)) as Hr.
    unfold lf_saved_fp, LF_MFRAME in *. destruct (XLO a HXa Hr); lia. }
  assert (FR : forall a, (lf_F cx fp <= a < lf_F cx fp + 1024 \/ lf_SH cx fp <= a < lf_SH cx fp + 128) ->
                 0 <= a < 2 ^ 64 -> ~ X a).
  { intros a Ha Hr HXa. destruct (kp_frame_place B LAWS cx fp ly3 S3 W3 (ms_mem ms3) md3 a HAR3 Hin Jfa Ha) as (Hni & Hc).
    destruct (XL a HXa Hr) as [H | [H | [H | H]]].
    - lia.
    - (* the model block and the side frame are apart (AR's separation law); its shadow is not app memory *)
      destruct Ha as [Ha | Ha].
      + destruct (al_sep _ _ LAWS _ _ _ _ _ HAR3) as (Hsep & _).
        apply YG0s.pairwise_app_inv in Hsep as (_ & _ & Hcr).
        pose proof (Hcr (md, req_size MD_SIZE) (frame_addr ly3 LF_CID fp, fs_frame_bytes LF_CID)
          ltac:(apply in_map_iff; exists (md, MD_SIZE); split; [reflexivity | exact Bmd])
          ltac:(apply in_map_iff; exists (LF_CID, fp); split; [reflexivity | exact Hin])) as D.
        unfold zdisjoint in D. cbn [fst snd] in D. change (req_size MD_SIZE) with 8856 in D.
        change (fs_frame_bytes LF_CID) with 1024 in D. rewrite (Jfa LF_CID fp) in D. unfold lf_F in Ha. lia.
      + pose proof (al_sep _ _ LAWS _ _ _ _ _ HAR3) as (_ & HFS). rewrite Forall_forall in HFS.
        pose proof (HFS (LF_CID, fp) Hin) as (HF1 & HF2). cbn [fst snd] in HF1, HF2.
        change (fs_frame_bytes LF_CID) with 1024 in HF1, HF2. rewrite (Jfa LF_CID fp) in HF1, HF2.
        unfold lf_SH, lf_F, shadow_of_addr in Ha. pose proof (ASAN_CEIL_range) as (CR1 & _).
        unfold in_app, kLowShadowBeg, kHighMemBeg in Hmdapp. unfold ASAN_CEIL in *. unfold SHADOW_OFF in Ha.
        clear - Hmdapp Ha HF1 HF2 H CR1. lia.
    - destruct Ha as [Ha | Ha].
      + destruct (al_sep _ _ LAWS _ _ _ _ _ HAR3) as (Hsep & _).
        apply YG0s.pairwise_app_inv in Hsep as (_ & _ & Hcr).
        pose proof (Hcr (md, req_size MD_SIZE) (frame_addr ly3 LF_CID fp, fs_frame_bytes LF_CID)
          ltac:(apply in_map_iff; exists (md, MD_SIZE); split; [reflexivity | exact Bmd])
          ltac:(apply in_map_iff; exists (LF_CID, fp); split; [reflexivity | exact Hin])) as D.
        unfold zdisjoint in D. cbn [fst snd] in D. change (req_size MD_SIZE) with 8856 in D.
        change (fs_frame_bytes LF_CID) with 1024 in D. rewrite (Jfa LF_CID fp) in D. unfold lf_F in Ha. lia.
      + pose proof (al_sep _ _ LAWS _ _ _ _ _ HAR3) as (_ & HFS). rewrite Forall_forall in HFS.
        pose proof (HFS (LF_CID, fp) Hin) as (HF1 & HF2). cbn [fst snd] in HF1, HF2.
        change (fs_frame_bytes LF_CID) with 1024 in HF1, HF2. rewrite (Jfa LF_CID fp) in HF1, HF2.
        unfold lf_SH, lf_F, shadow_of_addr in Ha. pose proof (ASAN_CEIL_range) as (CR1 & _).
        unfold in_app, kLowShadowBeg, kHighMemBeg in Hmdapp. unfold ASAN_CEIL in *. unfold SHADOW_OFF in Ha.
        clear - Hmdapp Ha HF1 HF2 H CR1. lia.
    - apply Hni. apply (mqp_gnl_img HSEGS a). lia. }
  assert (Hhd' : lf_header cx fp W3 ms').
  { apply (lf_header_keep X cx fp W3 ms3 W3 ms' KX); [|exact Hhd]. intros a Ha.
    pose proof (FPR a ltac:(right; left; exact Ha)) as Hr. apply FR; [left | exact Hr].
    unfold lf_header_fp in Ha. change (fs_frame_bytes LF_CID) with 1024 in Ha. lia. }
  assert (Hfsh' : lf_fshadow cx fp W3 ms' LF_SH0).
  { apply (lf_fshadow_keep X cx fp W3 ms3 W3 ms' LF_SH0 KX); [|exact Hfsh]. intros a Ha.
    pose proof (FPR a ltac:(right; right; left; exact Ha)) as Hr. apply FR; [right | exact Hr].
    unfold lf_fshadow_fp in Ha. change (Z.of_nat (length LF_SH0)) with 112 in Ha. lia. }
  assert (Hsl' : lf_slots cx md mk fp W3 ms').
  { apply (lf_slots_keep X cx md mk fp W3 ms3 W3 ms' KX); [|exact Hsl]. intros a Ha HXa.
    pose proof (FPR a ltac:(right; right; right; left; exact Ha)) as Hr.
    unfold lf_slots_fp in Ha. destruct (XLO a HXa Hr); lia. }
  (* the journal clauses *)
  assert (HPB : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by (intros Hn; exact (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
          cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ3 Hn)).
  (* the journal's bytes miss the model block and g_nl *)
  assert (MDNI : forall a, md <= a < md + MD_SIZE -> ~ in_img SEGS a)
    by (intros a Ha; exact (proj1 (kp_blk_place B LAWS ly3 S3 W3 (ms_mem ms3) md3 md MD_SIZE a HAR3 Bmd
          ltac:(change (req_size MD_SIZE) with 8856; unfold MD_SIZE in Ha; lia)))).
  assert (JMD : forall a, md <= a < md + MD_SIZE -> lf_jbk_fp MS la_nul cx T3 a -> False).
  { intros a Hm Ha. unfold lf_jbk_fp in Ha. destruct Ha as [[Ha | [Ha | (f & n & Hf & Ha)]] | [Ha | [Ha | Ha]]].
    - exact (MDNI a Hm (proj1 (IMG a ltac:(unfold lf_img_fp; tauto)))).
    - exact (MDNI a Hm (proj1 (IMG a ltac:(unfold lf_img_fp; tauto)))).
    - destruct (amf_gi_shape SEGS MS T3 _ Jgi) as [ET | (f' & ET)]; rewrite ET in Hf; [destruct Hf|].
      destruct Hf as [Hf | []]. injection Hf as Ef1 Ef2. subst f' n.
      assert (Hfin : In (f, AMF_BLOCK) (ablocks B ly3 S3)) by (apply Jinc; rewrite ET; left; reflexivity).
      assert (Hne : (f, AMF_BLOCK) <> (md, MD_SIZE)) by (intros E; injection E as _ E; unfold MD_SIZE, AMF_BLOCK in E; lia).
      pose proof (sep_blocks _ _ LAWS _ _ _ _ _ f AMF_BLOCK md MD_SIZE HAR3 Hfin Bmd Hne) as D.
      unfold zdisjoint in D. cbn [fst snd] in D. change (req_size AMF_BLOCK) with 1304 in D.
      change (req_size MD_SIZE) with 8856 in D. unfold AMF_BLOCK, MD_SIZE in *. lia.
    - exact (MDNI a Hm (proj1 (IMG a ltac:(unfold lf_img_fp; tauto)))).
    - apply (MDNI a Hm). destruct Ha as [(sg & Hs & _ & Hr) | Hr]; [exists sg; split; [exact Hs | exact Hr] | exact (RIMG a Hr)].
    - destruct (Bapmi ltac:(lia)) as [D | D]; unfold MD_SIZE in *; lia. }
  assert (JGN : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> a < LA_G_NL + NK_IF_NAME ->
                  lf_jbk_fp MS la_nul cx T3 a -> False).
  { intros a Hg Hg' Ha. assert (Hgi : in_img SEGS a) by exact (mqp_gnl_img HSEGS a Hg).
    unfold lf_jbk_fp in Ha. destruct Ha as [[Ha | [Ha | (f & n & Hf & Ha)]] | [Ha | [Ha | Ha]]].
    - rewrite HMS in Ha. cbv [amf_head_addr link_amf amf_sink_addr amf_say_addr amf_ofl_head amf_ofl_lock] in Ha.
      unfold LA_G_NL, NK_SIZE in Hg. lia.
    - rewrite HMS in Ha. cbv [amf_env_addr link_amf amf_threaded amf_need_locks amf_ofl_lock] in Ha.
      unfold LA_G_NL, NK_SIZE in Hg. lia.
    - destruct (amf_gi_shape SEGS MS T3 _ Jgi) as [ET | (f' & ET)]; rewrite ET in Hf; [destruct Hf|].
      destruct Hf as [Hf | []]. injection Hf as Ef1 Ef2. subst f' n.
      assert (Hfin : In (f, AMF_BLOCK) (ablocks B ly3 S3)) by (apply Jinc; rewrite ET; left; reflexivity).
      destruct (kp_blk_place B LAWS ly3 S3 W3 (ms_mem ms3) md3 f AMF_BLOCK a HAR3 Hfin
        ltac:(change (req_size AMF_BLOCK) with 1304; unfold AMF_BLOCK in Ha; lia)) as (Hni & _). exact (Hni Hgi).
    - rewrite HLN in Ha. unfold LA_NUL, LA_LONG_ALIAS, LA_G_NL, NK_SIZE in *. lia.
    - apply (ar_not_ro_G HSEGS a); [|exact Ha]. unfold inG, G_HARNESS. apply Exists_cons_hd. unfold in_zr.
      cbn [fst snd]. unfold LA_G_NL, NK_SIZE, NK_IF_NAME in *. lia.
    - destruct (kp_blk_place B LAWS ly3 S3 W3 (ms_mem ms3) md3 (c_p cx) (c_n cx) a HAR3 (HPB ltac:(lia))
        ltac:(unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia)) as (Hni & _). exact (Hni Hgi). }
  assert (Hjbk' : lf_jbk B MT MS la_nul cx fp k2 (lf_ev i) (lf_mo LF_MO_SET LF_MO_OP i) (lf_wl i) LF_LIVE_HELD ly3 S3
                    W3 ms' md' T3 [(md, MD_SIZE); (mk, MK_SIZE)]).
  { apply (lf_jbk_keep B MT MS la_nul X cx fp k2 _ _ _ _ ly3 S3 W3 ms3 md3 T3 _ W3 ms' md' KX Hfd Hfs); [|exact Hjbk].
    intros a Ha HXa. destruct (XL a HXa (FPR a ltac:(do 5 right; left; exact Ha))) as [H | [H | [H | H]]].
    - (* the cursor: every journal byte is below the ceiling *)
      unfold lf_jbk_fp in Ha. destruct Ha as [[Ha | [Ha | (f & n & Hf & Ha)]] | [Ha | [Ha | Ha]]].
      + destruct (IMG a ltac:(unfold lf_img_fp; tauto)) as (Himg & _). pose proof (pa_segs_low a Himg). unfold kLowMemEnd in *. lia.
      + destruct (IMG a ltac:(unfold lf_img_fp; tauto)) as (Himg & _). pose proof (pa_segs_low a Himg). unfold kLowMemEnd in *. lia.
      + destruct (al_blocks _ _ LAWS _ _ _ _ _ f n HAR3 (Jinc _ Hf)) as (_ & _ & Hc & _).
        destruct (amf_gi_shape SEGS MS T3 _ Jgi) as [ET | (f' & ET)]; rewrite ET in Hf; [destruct Hf|].
        destruct Hf as [Hf | []]. injection Hf as <- <-. change (req_size AMF_BLOCK) with 1304 in Hc. unfold AMF_BLOCK in Ha. lia.
      + destruct (IMG a ltac:(unfold lf_img_fp; tauto)) as (Himg & _). pose proof (pa_segs_low a Himg). unfold kLowMemEnd in *. lia.
      + pose proof (lf_roP_bounds a Ha). unfold YImgTop.IMG_TOP in *. lia.
      + destruct (al_blocks _ _ LAWS _ _ _ _ _ (c_p cx) (c_n cx) HAR3 (HPB ltac:(lia))) as (_ & _ & Hc & _).
        unfold req_size in Hc. destruct (Z.eqb_spec (c_n cx) 0); lia.
    - exact (JMD a ltac:(unfold MD_SIZE; lia) Ha).
    - exact (JMD a ltac:(unfold MD_SIZE; lia) Ha).
    - exact (JGN a ltac:(unfold NK_SIZE; lia) ltac:(unfold NK_IF_NAME; lia) Ha). }
  (* the blocks' shadow *)
  assert (Hblk' : lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms'))).
  { apply (lf_blocks_keep B X _ _ cx md mk T3 ly3 S3 KX); [|exact Hblk].
    intros a Ha HXa. pose proof (FPR a ltac:(do 6 right; left; exact Ha)) as Hr. pose proof (ASAN_CEIL_range) as (CR1 & _).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ mk MK_SIZE HAR3 Bmk) as (_ & Hmk4 & Hmkc & Hmkapp & _).
    change (req_size MK_SIZE) with 516 in Hmkc, Hmkapp.
    assert (Hsh : exists x, 0 <= x < alloc_ceiling /\ a = shadow_of_addr SHADOW_OFF x).
    { destruct Ha as [(x & Hx & ->) | (x & Hx & ->)]; exists x; split; [unfold MD_SIZE in *; lia | reflexivity |
        unfold MK_SIZE in *; lia | reflexivity]. }
    destruct Hsh as (x & Hx & ->). unfold shadow_of_addr, SHADOW_OFF in *.
    pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(unfold ASAN_CEIL in *; lia)).
    unfold in_app, kLowShadowBeg, kHighMemBeg in Hmdapp. unfold ASAN_CEIL in *.
    destruct (XL _ HXa Hr) as [Hq | [Hq | [Hq | Hq]]]; lia. }
  (* the data, at model_begin's stores *)
  destruct (lf_data_mb X (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms')) cx md mk kbs mbs gbs HSEGS KX
    (wcarry_on_grows _ _ _ HG)
    ltac:(intros a Hd HXa; destruct (HX a HXa (FPR a ltac:(do 7 right; exact Hd))) as [Hc | Hm]; [|exact Hm]; exfalso;
          unfold lf_cur_fp in Hc; unfold lf_data_fp in Hd;
          destruct Hd as [Hd | [Hd | [Hd | [Hd | [Hd | Hd]]]]];
          [ unfold LA_G_NL, NK_SIZE in Hd; lia | unfold LA_G_NAMES, G_NAMES_SIZE in Hd; lia
          | unfold LA_LONG_ALIAS in Hd; lia | lia
          | destruct (al_blocks _ _ LAWS _ _ _ _ _ mk MK_SIZE HAR3 Bmk) as (_ & _ & Hmkc' & _);
            change (req_size MK_SIZE) with 516 in Hmkc'; unfold MK_SIZE in Hd; lia
          | pose proof (lf_roP_bounds a Hd); unfold YImgTop.IMG_TOP in *; lia ])
    Bmdt Bmkt Bapmm A1 A2 A3 A4 A5 Hdat) as (Hdat' & Hns' & _ & Hopd & Hreq').
  pose proof Hcore as (C2 & C8 & C9 & C3 & C4).
  pose proof Hlr as (L19 & L21 & L22 & L23 & L24 & L25 & L26 & L27).
  assert (Hcore' : lf_core cx ms').
  { repeat split; rewrite KR by (unfold acallee_saved; first [ (vm_compute; lia) | (cbn; lia) | (simpl; lia)
      | (vm_compute; right; right; right; right; right; split; discriminate) ]); assumption. }
  assert (Hlr' : lf_lregs cx md fp i ms').
  { repeat split; rewrite KR by (unfold acallee_saved; first [ (vm_compute; lia) | (cbn; lia) | (simpl; lia)
      | (vm_compute; right; right; right; right; right; split; discriminate) ]); assumption. }
  apply (o5m_call SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS HV MT_LE MT_OK MQO
    MQA CM CR POST i cx fy fp k2 ly3 S3 W3 ms' md' md mk P' N' (lf_kbs_mb kbs) (lf_mbs_mb kbs mbs) gbs T3 nm
    Hi NEXT HB Hfx HJ' Hfr Hms Hcore' Hlr' R1 Ha0 Ha1 Hsv' Hhd' Hfsh' Hsl' Hcur Hjbk' Hblk' Hdat' Hreq' Hns'
    ltac:(rewrite Hopd; exact Hop)).
Qed.

End b.
End a.

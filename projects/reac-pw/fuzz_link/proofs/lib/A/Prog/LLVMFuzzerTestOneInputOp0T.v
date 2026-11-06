(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module names changed; 461 of its 512 lines of code are new or changed and 1281 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A, the op_read arm: the two text_buf calls (0x835f4, 0x83600),
   +0xe1c .. +0xe30, from the cut r_b_inv to the cut r_t_inv at +0xe34. text_buf's contract (text_buf_c.v
   `text_buf_acontract`, an `aleaf_alloc`) is the Section hypothesis TXB_C; its trace clause `text_buf_traces`
   (an obligation of the image instance and of CTX) is TXB_TR. The call is made as Txo.v makes text_of's
   (lf_text_of_call), and the state after it is restated as Txa.v restates text_of's (lf_text_of_after).
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import text_buf_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs
  LLVMFuzzerTestOneInputKeep LLVMFuzzerTestOneInputKpre LLVMFuzzerTestOneInputArmW LLVMFuzzerTestOneInputLp
  LLVMFuzzerTestOneInputDec LLVMFuzzerTestOneInputArmR LLVMFuzzerTestOneInputArmK LLVMFuzzerTestOneInputFree
  LLVMFuzzerTestOneInputTxa LLVMFuzzerTestOneInputSel LLVMFuzzerTestOneInputOp0Cut LLVMFuzzerTestOneInputArmH.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

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
Hypothesis MT_OK : forall S m, mo_ok MT S m.
(* text_buf's contract at the running FP state (the text_buf walk, text_buf_aproof) *)
Hypothesis TXB_C : forall fy : YK11.FPState, text_buf_acontract (fx := fy) SK SEGS PCAP_RLO PCAP_RHI B MT LF_CTX.
(* the malloc trace of each context CTX allows at text_buf's call is a fixed trace of the universe *)
Hypothesis TXB_TR : text_buf_traces B LF_CTX.

#[local] Notation BASEF cx := (lf_base SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Notation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).
Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

(* the whole text_buf call at a site, from what a cut of the body carries: the contract applied *)
Lemma lf_text_buf_call : forall (fy : YK11.FPState) cx fp k2 ev lv ly S (W : world SEGS) mem mdl
    (regs : bvmap 5 word) rao,
  @lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx ->
  JRN cx fp ly S W mem mdl k2 ->
  k2 <= ev -> ev + 1 <= EV_LIB ->
  blocks_bytes S <= blocks_bytes (c_S cx) + lv -> lv + TEXT_BUF_LIVE <= LIVE_LIB ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  rdword (aview SEGS (w_H W) mem) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
  rdword (aview SEGS (w_H W) mem) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
  spZ regs = lf_sp1 cx -> s0Z regs = spZ (c_regs cx) -> aarg regs 0 < 40 ->
  getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
  pa_val A_TEXT = link_text -> getr regs 1 = Z_to_bv 64 (link_text + rao) -> In rao LF_TEXT_BUF_SITES ->
  SRr SEGS W (cfg_at (fx := fy) SEGS TEXT_BUF_A regs mem mdl)
    (apost (fx := fy) SK SEGS B TEXT_BUF_AK 1 (fun a => inFP (text_buf_awr regs (rdW W mem)) a) G_HARNESS 0 []
       LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
       [(LF_CID, fp)] ly S W mem mdl k2 regs
       (fun ly2 S2 W2 regs2 mem2 md2 =>
          mo_le MT S S2 (mo_malloc MT TEXT_BUF_LIVE) /\ text_buf_ledpost B S S2 /\
          text_buf_apostA SEGS regs (rdW W mem) regs2 (rdW W2 mem2) (ablocks B ly S) (ablocks B ly2 S2))).
Proof.
  intros fy cx fp k2 ev lv ly S W mem mdl regs rao HB HJ Hkev Hev Hbb Hlv HRO H8 H16 Hsp Hs0 Ha0 R3 R4 HBASE R1
    Hsite.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as (HPRE & _ & HGX & _).
  pose proof HPRE as (HAFN & _ & _ & _ & _ & _ & _ & _ & _ & Hlive & _).
  pose proof HAFN as (_ & _ & _ & HGP & HTP & _).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly S W mem mdl k2
    HB HJ) as (H16s & Hceil & Hslo & Hshi & H47 & Hwin & HAR).
  assert (Hs1 : spZ (c_regs cx) - 416 - 16 <= lf_sp1 cx <= spZ (c_regs cx) - 416).
  { unfold lf_sp1. pose proof (lf_sp1_range (spZ (c_regs cx)) ltac:(unfold LF_MFRAME, LLVMF_STK in *; lia) H16s)
      as (R & _). unfold LF_MFRAME in R. exact R. }
  assert (Hra : raZ regs = link_text + rao).
  { unfold raZ. rewrite R1. apply unsigned_lit_small.
    unfold LF_TEXT_BUF_SITES, AF_LLVMFuzzerTestOneInput, link_text in *. cbn in Hsite. lia. }
  assert (Hret : YK0s.ret_ok (getr regs 1)).
  { rewrite R1, <- HBASE. apply ret_ok_codeptr_v.
    - unfold LF_TEXT_BUF_SITES, AF_LLVMFuzzerTestOneInput in Hsite. cbn in Hsite. lia.
    - unfold LF_TEXT_BUF_SITES, AF_LLVMFuzzerTestOneInput in Hsite. cbn in Hsite.
      destruct Hsite as [<- | [<- | []]]; reflexivity. }
  assert (Hra4 : 4096 <= raZ regs) by (rewrite Hra; unfold link_text, LF_TEXT_BUF_SITES, AF_LLVMFuzzerTestOneInput in *;
    cbn in Hsite; lia).
  pose proof (lf_apre_at SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END
    cx fp ly S W mem mdl k2 regs TEXT_BUF_AK 1 [] (text_buf_awr regs (rdW W mem)) HB HJ HRO Hsp
    ltac:(rewrite R3; exact HGP) ltac:(rewrite R4; exact HTP) Hret Hra4
    ltac:(rewrite TEXT_BUF_AK_val; unfold LLVMF_STK; lia) ltac:(lia) ltac:(lia) (Forall_nil _)
    ltac:(intros a (r & Hin & _); destruct Hin) ltac:(intros a (r & Hin & _); destruct Hin)) as HAPRE.
  destruct (lf_site_chain SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END
    cx [(LF_CID, fp)] ly S W mem mdl k2 regs HB HJ H8 H16 ltac:(unfold LLVMF_STK in *; lia) Hs0 Hra4)
    as (_ & HCH).
  assert (HCTX : In (raZ regs :: spine (lf_chain cx)) LF_CTX).
  { apply (lf_site_ctx SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx regs HB).
    rewrite Hra, <- HBASE. replace (pa_val A_TEXT + rao - pa_val A_TEXT) with rao by lia.
    unfold LF_ALLOC_SITES. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
    apply in_or_app. left. exact Hsite. }
  apply (TXB_C fy G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k2 regs (lf_chain cx) HAPRE).
  - pose proof LF_LIVE_HELD_room as LR. unfold TEXT_BUF_LIVE, LF_LIVE_HELD in *. lia.
  - apply MT_OK.
  - exact HCH.
  - exact HCTX.
  - exact I.
  - split; [exact Ha0 | exact TXB_TR].
Qed.

(* the state after a text_buf call: the cut kept, the fresh block (if any) added to the arm's own blocks *)
Lemma lf_text_buf_after : forall cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly3 S3 W3 (ms3 : machine_state) md3
    (regs : bvmap 5 word) ly2 S2 W2 regs2 mem2 md2 (ms2 : machine_state) mo',
  BASEF cx -> JRN cx fp ly3 S3 W3 (ms_mem ms3) md3 k ->
  ak_cut SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly3 S3 W3 ms3 md3 ->
  spZ regs = lf_sp1 cx -> 0 <= aarg regs 0 < 40 ->
  ms_mem ms2 = mem2 ->
  JRN cx fp ly2 S2 W2 mem2 md2 (k + 1) -> frames S2 = frames S3 ->
  m_fds md2 = m_fds md3 -> m_fs md2 = m_fs md3 ->
  akept SEGS B ly3 S3 W3 (ms_mem ms3) W2 mem2 (spZ regs - TEXT_BUF_AK) (spZ regs)
    (fun a => inFP (text_buf_awr regs (rdW W3 (ms_mem ms3))) a) ->
  ashadow_kept SEGS B ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 mem2 ->
  text_buf_ledpost B S3 S2 ->
  text_buf_apostA SEGS regs (rdW W3 (ms_mem ms3)) regs2 (rdW W2 mem2) (ablocks B ly3 S3) (ablocks B ly2 S2) ->
  exists t nb,
    getr regs2 10 = w64 t /\ tb_nb (aarg regs 0) t nb /\
    ak_cut SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 (nb ++ own) (ev + 1) mo' wl (lv + TEXT_BUF_LIVE) (k + 1)
      ly2 S2 W2 ms2 md2 /\
    arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) mem2) /\
    (forall c, In c (ablocks B ly3 S3) -> In c (ablocks B ly2 S2)) /\
    (forall b, In b nb -> In b (ablocks B ly2 S2)) /\
    (forall c b, In c (ablocks B ly3 S3) -> In b nb -> zdisjoint (fst c, req_size (snd c)) (fst b, req_size (snd b))) /\
    lf_call B cx TEXT_BUF_AK ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 mem2
      (fun a => inFP (text_buf_awr regs (rdW W3 (ms_mem ms3))) a) /\
    (1 <= aarg regs 0 -> atbuf_at SEGS (rdW W2 mem2) t (aarg regs 0) (repeat (zb GUARD_BYTE) (Z.to_nat (aarg regs 0)))).
Proof.
  intros cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly3 S3 W3 ms3 md3 regs ly2 S2 W2 regs2 mem2 md2 ms2 mo'
    HB HJ HC Hsp Ha0 Hms2 HJ2 Hfr2 Hfd Hfs HK HSH HLED (HP0 & HP1).
  pose proof HB as (HPRE & _ & HGX & HLAN & HMSE & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k HB HJ) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR3).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly2 S2 W2
    mem2 md2 (k + 1) HB HJ2) as (_ & _ & _ & _ & _ & _ & HAR2).
  assert (Hs1 : spZ (c_regs cx) - 416 - 16 <= lf_sp1 cx <= spZ (c_regs cx) - 416).
  { unfold lf_sp1. pose proof (lf_sp1_range (spZ (c_regs cx)) ltac:(unfold LF_MFRAME, LLVMF_STK in *; lia) H16)
      as (R & _). unfold LF_MFRAME in R. exact R. }
  unfold LLVMF_STK in *.
  pose proof HC as (_ & HFR & _ & _ & _ & _ & HJBK & HBLK & _).
  pose proof HJBK as (Hkev & Hbb & Hfa & _ & _ & _ & _ & Hwl & _ & _ & Hbl & Hinc & _ & Hro & _).
  pose proof HBLK as (Hmd & Hmk & _).
  (* the answer and the block list after the call *)
  assert (HT : exists t nb, getr regs2 10 = w64 t /\ tb_nb (aarg regs 0) t nb /\
      (nb = [] -> Permutation (ablocks B ly2 S2) (ablocks B ly3 S3)) /\
      (nb <> [] -> ablocks B ly2 S2 = ablocks B ly3 S3 ++ nb) /\
      (1 <= aarg regs 0 -> atbuf_at SEGS (rdW W2 mem2) t (aarg regs 0) (repeat (zb GUARD_BYTE) (Z.to_nat (aarg regs 0))))).
  { destruct (Z.eq_dec (aarg regs 0) 0) as [E | E].
    - destruct (HP0 E) as (H10 & Hperm). exists 0, [].
      split; [exact H10|]. split; [left; split; [exact E|]; split; reflexivity|].
      split; [intros _; exact Hperm|]. split; [intros Hn; contradiction|]. intros Hl; lia.
    - destruct (HP1 E) as (p & H10 & H4096 & Hbl2 & Hbuf). exists p, [(p, aarg regs 0 + 1)].
      split; [exact H10|]. split; [right; split; [lia|]; split; [exact H4096 | reflexivity]|].
      split; [intros Hn; discriminate|]. split; [intros _; exact Hbl2|]. intros _; exact Hbuf. }
  destruct HT as (t & nb & H10 & Hnb & Hnb0 & Hnb1 & Hbuf).
  assert (Hsub : forall c, In c (ablocks B ly3 S3) -> In c (ablocks B ly2 S2)).
  { intros c Hc. destruct nb as [|b nb'].
    - exact (Permutation_in c (Permutation_sym (Hnb0 eq_refl)) Hc).
    - rewrite (Hnb1 ltac:(discriminate)). apply in_or_app. left. exact Hc. }
  assert (Hnbin : forall b, In b nb -> In b (ablocks B ly2 S2)).
  { intros b Hb. destruct nb as [|b0 nb']; [destruct Hb|].
    rewrite (Hnb1 ltac:(discriminate)). apply in_or_app. right. exact Hb. }
  assert (Hapart : forall c b, In c (ablocks B ly3 S3) -> In b nb ->
            zdisjoint (fst c, req_size (snd c)) (fst b, req_size (snd b))).
  { intros c b Hc Hb. destruct Hnb as [(_ & _ & ->) | (_ & _ & ->)]; [destruct Hb|].
    destruct Hb as [<- | []].
    exact (tx_fresh_apart B LAWS ly2 S2 W2 mem2 md2 (ablocks B ly3 S3) (t, aarg regs 0 + 1) HAR2
      (Hnb1 ltac:(discriminate)) c Hc). }
  assert (HPB : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by exact (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS cx fp ly3 S3 W3
              (ms_mem ms3) md3 k HB HJ).
  assert (HCALL : lf_call B cx TEXT_BUF_AK ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 (ms_mem ms2)
                    (fun a => inFP (text_buf_awr regs (rdW W3 (ms_mem ms3))) a)).
  { rewrite Hms2. unfold lf_call. rewrite Hsp in HK. split; [rewrite TEXT_BUF_AK_val; lia|].
    split; [rewrite TEXT_BUF_AK_val; lia|]. split; [exact HK | exact HSH]. }
  (* the live bytes after the call *)
  assert (Hbb2 : blocks_bytes S2 <= blocks_bytes (c_S cx) + (lv + TEXT_BUF_LIVE)).
  { rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly3 S3) in *.
    destruct Hnb as [(_ & _ & ->) | (Hc1 & _ & ->)].
    - rewrite (bsum_perm _ _ (Hnb0 eq_refl)). unfold TEXT_BUF_LIVE. lia.
    - rewrite (Hnb1 ltac:(discriminate)), bsum_app. cbn [bsum fold_right fst snd]. unfold bsum in *. cbn.
      unfold TEXT_BUF_LIVE in *. lia. }
  assert (Hwl2 : (length (wild_part (as_universe B) (st_depot S2)) <=
                  length (wild_part (as_universe B) (st_depot (c_S cx))) + wl)%nat)
    by (unfold text_buf_ledpost in HLED; lia).
  assert (Hbl2 : lf_bl B cx (nb ++ own) T3 ly2 S2).
  { destruct Hnb as [(_ & _ & ->) | (_ & _ & ->)].
    - cbn [app]. exact (lf_bl_perm B cx own T3 ly3 S3 ly2 S2 Hbl (Hnb0 eq_refl)).
    - cbn [app]. exact (lf_bl_cons B cx own T3 ly3 S3 ly2 S2 _ Hbl (Hnb1 ltac:(discriminate))). }
  destruct (ak_cut_callee SK B MT MS la_nul LAWS MT_LE HSEGS TB cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly3 S3 W3
    ms3 md3 (nb ++ own) (ev + 1) mo' wl (lv + TEXT_BUF_LIVE) (k + 1) ly2 S2 W2 ms2 md2 TEXT_BUF_AK
    (fun a => inFP (text_buf_awr regs (rdW W3 (ms_mem ms3))) a) HMSE HLAN HPB HC
    ltac:(rewrite Hms2; exact HJ2) Hfr2 ltac:(rewrite Hms2; exact HAR2) HCALL)
    as (HC2 & HRO2).
  - intros a (r & Hin & _). destruct Hin.
  - intros a (r & Hin & _). destruct Hin.
  - exact Hfd.
  - exact Hfs.
  - exact (Hsub _ Hmd).
  - exact (Hsub _ Hmk).
  - lia.
  - exact Hbb2.
  - exact Hwl2.
  - exact Hbl2.
  - intros c Hc. exact (Hsub c (Hinc c Hc)).
  - exists t, nb.
    rewrite Hms2 in HRO2.
    split; [exact H10|]. split; [exact Hnb|]. split; [exact HC2|]. split; [exact HRO2|].
    split; [exact Hsub|]. split; [exact Hnbin|]. split; [exact Hapart|].
    split; [rewrite <- Hms2; exact HCALL|]. exact Hbuf.
Qed.
(* a text buffer of the arm's own blocks across a callee that does not write it *)
Lemma r_atbuf_callee : forall cx K ly3 S3 ly2 S2 (W3 : world SEGS) mem3 (W2 : world SEGS) mem2 (E : Z -> Prop) md2
    t cap bs,
  lf_call B cx K ly3 S3 ly2 S2 W3 mem3 W2 mem2 E -> AR SEGS B ly2 S2 W2 mem2 md2 ->
  In (t, cap + 1) (ablocks B ly3 S3) -> In (t, cap + 1) (ablocks B ly2 S2) ->
  (forall a, t <= a < t + cap + 1 -> ~ E a) -> 0 <= cap ->
  atbuf_at SEGS (rdW W3 mem3) t cap bs -> atbuf_at SEGS (rdW W2 mem2) t cap bs.
Proof.
  intros cx K ly3 S3 ly2 S2 W3 mem3 W2 mem2 E md2 t cap bs HC HAR Hin3 Hin2 HE Hc (Hu & Hl).
  split; [|exact Hl].
  assert (Rq : req_size (cap + 1) = cap + 1) by (unfold req_size; destruct (cap + 1 =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | lia]).
  assert (L : Z.of_nat (length (bs ++ [zb GUARD_BYTE])) = cap + 1) by (rewrite length_app; cbn [length]; lia).
  apply (au8arr_keep SEGS _ _ _ _ _ (lf_call_kagree B cx K ly3 S3 ly2 S2 W3 mem3 W2 mem2 E HC)); [| |exact Hu].
  - rewrite L. intros i Hi _.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin2) as (_ & _ & _ & _ & Hp & _).
    destruct (Hp (t + i) ltac:(rewrite Rq; lia)) as (Hpr & _).
    exact (apresent_writable SEGS (w_H W2) mem2 (t + i) Hpr).
  - rewrite L. intros i Hi. apply (lfx_blk B ly3 S3 ly2 S2 _ _ E t (cap + 1) (t + i) Hin3 ltac:(lia)).
    apply HE. lia.
Qed.

(* the same across a run that writes no byte *)
Lemma r_atbuf_run : forall (W : world SEGS) m m' t cap bs,
  kagree SEGS (fun _ => False) (rdW W m) (rdW W m') -> mem_grows (rdW W m) (rdW W m') ->
  atbuf_at SEGS (rdW W m) t cap bs -> atbuf_at SEGS (rdW W m') t cap bs.
Proof.
  intros W m m' t cap bs HK HG (Hu & Hl). split; [|exact Hl].
  apply (au8arr_keep SEGS _ _ _ _ _ HK (wcarry_of_grows SEGS _ _ _ _ HG)); [intros i _ H; exact H | exact Hu].
Qed.

(* the two text_buf calls *)
Lemma r_tbufs : forall POST i,
  FROM POST (r_t_inv SK B MT MS la_nul LF_MO_SET LF_MO_OP i) ->
  FROM POST (r_b_inv B MT MS la_nul LF_MO_SET LF_MO_OP i).
Proof.
  intros POST i HT cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HBI.
  destruct HBI as (md & mk & P & N & kbs & mbs & gbs & T3 & s & nm & kc & ac & Hsh & Hreg & Hnm & Hkc & Hac & HU &
    Hns & Hrq & Hks & Hra).
  destruct HU as (Hi & Hcore & Hsv & Hhd & Hfs & Hsl & Hcur & Hjbk & Hblk & Hdat & Hop).
  assert (HC0 : ak_cut SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 [(md, MD_SIZE); (mk, MK_SIZE)]
    (lf_ev i) (lf_mo LF_MO_SET LF_MO_OP i) (lf_wl i) LF_LIVE_HELD k2 ly3 S3 W3 ms3 md3)
    by (repeat (split; [eassumption|]); exact Hdat).
  clear Hsv Hhd Hfs Hsl Hjbk Hblk Hdat.
  pose proof HB as (HPRE & Hfrm & HGX & _).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof Hreg as (R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
  pose proof (lv_text LV) as HBASE.
  assert (Hs1 : spZ (c_regs cx) - 416 - 16 <= lf_sp1 cx <= spZ (c_regs cx) - 416 /\ lf_sp1 cx mod 16 = 0).
  { unfold lf_sp1. pose proof (lf_sp1_range (spZ (c_regs cx)) ltac:(unfold LF_MFRAME, LLVMF_STK in *; lia) H16)
      as (R & _ & R16). unfold LF_MFRAME in R. split; [exact R | exact R16]. }
  assert (Usp : spZ (ms_regs ms3) = lf_sp1 cx).
  { unfold spZ. rewrite R2. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
  (* ---- +0xe1c .. +0xe20: a0 := kc; text_buf ---- *)
  rewrite (aw_ms_eq fy LR_b ms3 Hsh).
  pose proof (aw_entry0 (fx := fy) W3 (ms_regs ms3) (ms_mem ms3) LR_b ltac:(unfold LLVMF_STK in *; lia)
    ltac:(rewrite Usp; lia)) as HS.
  assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) aw_extra0))) by apply Eimg_env.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  assert (SHOK : sh_ok pa_segs aw_Bx [] (Eimg (Ereg (ms_regs ms3) aw_extra0))
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LR_b)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  paj_run_tok RUN HS HJ SHOK aw_span; [apply awr_ok_x_nil|].
  rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
  pose proof (kagree_frame_nil _ _ _ HFrA) as KA.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (mdA := mdB) in * end.
  assert (FdA : m_fds mdA = m_fds md3) by (subst mdA; rewrite !lf_wvb_fds; reflexivity).
  assert (FsA : m_fs mdA = m_fs md3) by (subst mdA; rewrite !lf_wvb_fs; reflexivity).
  pose proof (ak_cut_run SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 _ _ _ _ _ k2 ly3 S3 W3 ms3 msA md3 mdA HC0 HJ KA
    (fun x Hx => HGA x Hx) FdA FsA) as HCA.
  pose proof (lf_cur_keep (fun _ => False) cx W3 ms3 W3 msA P N KA (fun a _ H => H) Hcur) as HcurA.
  lazymatch type of HS with st_ok _ ?Ex ?ssx _ => set (ssA := ssx) in HS; set (EA := Ex) in HS end.
  pmkst HS.
  assert (EL : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew EA n = getr (ms_regs ms3) r).
  { intros n r Hn Hr. unfold EA. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat _ _ n r Hr). }
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
  prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10.
  prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
  prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
  prreg HS (27%bv : bv 5) Q27.
  rewrite (img_env_codeptr EA HEI) in Q1.
  rewrite (EL 2%nat 2%bv ltac:(lia) eq_refl), R2 in Q2. rewrite (EL 3%nat 3%bv ltac:(lia) eq_refl), R3 in Q3.
  rewrite (EL 4%nat 4%bv ltac:(lia) eq_refl), R4 in Q4. rewrite (EL 8%nat 8%bv ltac:(lia) eq_refl), R8 in Q8.
  rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl), R9 in Q9. rewrite (EL 21%nat 21%bv ltac:(lia) eq_refl), R21 in Q10.
  rewrite (EL 18%nat 18%bv ltac:(lia) eq_refl), R18 in Q18. rewrite (EL 19%nat 19%bv ltac:(lia) eq_refl), R19 in Q19.
  rewrite (EL 20%nat 20%bv ltac:(lia) eq_refl), R20 in Q20. rewrite (EL 21%nat 21%bv ltac:(lia) eq_refl), R21 in Q21.
  rewrite (EL 22%nat 22%bv ltac:(lia) eq_refl), R22 in Q22. rewrite (EL 23%nat 23%bv ltac:(lia) eq_refl), R23 in Q23.
  rewrite (EL 24%nat 24%bv ltac:(lia) eq_refl), R24 in Q24. rewrite (EL 25%nat 25%bv ltac:(lia) eq_refl), R25 in Q25.
  rewrite (EL 26%nat 26%bv ltac:(lia) eq_refl), R26 in Q26. rewrite (EL 27%nat 27%bv ltac:(lia) eq_refl), R27 in Q27.
  rewrite HBASE in Q1.
  assert (HspA : spZ (ms_regs msA) = lf_sp1 cx)
    by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  assert (Hs0A : s0Z (ms_regs msA) = spZ (c_regs cx))
    by (unfold s0Z; rewrite Q8; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  assert (Ha0A : aarg (ms_regs msA) 0 = kc) by (rewrite ar_aarg0, Q10; unfold w64; apply unsigned_lit_small; lia).
  pose proof HCA as (HJA & HFRA & HSAVA & _ & _ & _ & HJBKA & HBLKA & _).
  pose proof HJBKA as (HkA & HbbA & _ & _ & _ & _ & _ & _ & _ & _ & HblA & HincA & _ & HroA & _).
  destruct (lf_saved_ra_s0 cx W3 msA HSAVA) as (HR8 & HR16).
  assert (Hpc : ss_pc ssA = pa_sigma LS_text_buf) by reflexivity.
  rewrite Hpc.
  eapply SRr_bind.
  { replace (pa_sigma LS_text_buf) with TEXT_BUF_A by (rewrite (lv_sigma LV); reflexivity).
    change (mkCfg (mkst (ms_regs msA) (Z_to_bv 64 TEXT_BUF_A) (ms_mem msA) (seg_rom SEGS)) mdA)
      with (cfg_at (fx := fy) SEGS TEXT_BUF_A (ms_regs msA) (ms_mem msA) mdA).
    apply (lf_text_buf_call fy cx fp k2 (lf_ev i) LF_LIVE_HELD ly3 S3 W3 (ms_mem msA) mdA (ms_regs msA) 5164 HB HJA
      HkA ltac:(unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB; lia) HbbA
      ltac:(pose proof LF_LIVE_HELD_room; unfold TEXT_BUF_LIVE; lia) HroA HR8 HR16 HspA Hs0A ltac:(lia) Q3 Q4 HBASE
      Q1 ltac:(unfold LF_TEXT_BUF_SITES, AF_LLVMFuzzerTestOneInput; left; reflexivity)). }
  intros W4 c4 Hle4 HPOST.
  destruct HPOST as (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HPRES4 & HFR4 & HFD4 & HFS4 & HKEPT4 & HSHK4 &
    HMO4 & HLED4 & HPA4).
  set (ms4 := @mkst fy regs4 (getr (ms_regs msA) 1) mem4 (seg_rom SEGS)).
  destruct (lf_text_buf_after cx fp md mk kbs mbs gbs T3 _ _ _ _ _ k2 ly3 S3 W3 msA mdA (ms_regs msA) ly4 S4 W4 regs4
    mem4 md4 ms4 (lf_mo LF_MO_SET LF_MO_OP i) HB HJA HCA HspA ltac:(rewrite Ha0A; lia) eq_refl HJ4 HFR4 HFD4 HFS4
    HKEPT4 HSHK4 HLED4 HPA4)
    as (t1 & nb1 & HT10 & Hnb1 & HC4 & HRO4 & Hsub4 & Hnbin4 & Hap4 & HCALL4 & Hbuf4).
  rewrite Ha0A in Hnb1, Hbuf4.
  pose proof (ar_pres _ _ HPRES4) as (P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26
    & P27).
  pose proof (lf_cur_callee B cx TEXT_BUF_AK ly3 S3 ly4 S4 W3 msA W4 ms4 _ P N HCALL4
    ltac:(intros a _ (r & Hin & _); destruct Hin) HcurA) as Hcur4.
  (* ---- +0xe24 .. +0xe2c: s7 := kind, a0 := ac; text_buf ---- *)
  unfold ms4. rewrite Q1, <- HBASE.
  clear HS SHOK.
  assert (Usp4 : spZ regs4 = lf_sp1 cx) by (unfold spZ in *; rewrite P2; exact HspA).
  pose proof (aw_entry0 (fx := fy) W4 regs4 mem4 5164 ltac:(rewrite Usp4; unfold LLVMF_STK in *; lia)
    ltac:(rewrite Usp4; lia)) as HS.
  assert (HEI4 : img_env pa_val A_LIM (Eimg (Ereg regs4 aw_extra0))) by apply Eimg_env.
  assert (SHOK : sh_ok pa_segs aw_Bx [] (Eimg (Ereg regs4 aw_extra0))
    (mrestrict (w_H W4) (ms_mem (@mkst fy regs4 (Z_to_bv 64 (BASE + 5164)) mem4 (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  pose proof HC4 as (HJ4' & _).
  change (ms_mem ms4) with mem4 in HJ4'.
  paj_run_tok RUN HS HJ4' SHOK aw_span; [apply awr_ok_x_nil|].
  rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
  pose proof (kagree_frame_nil _ _ _ HFrB) as KB.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdB := mdx) in * end.
  assert (FdB : m_fds mdB = m_fds md4) by (subst mdB; rewrite !lf_wvb_fds; reflexivity).
  assert (FsB : m_fs mdB = m_fs md4) by (subst mdB; rewrite !lf_wvb_fs; reflexivity).
  pose proof (ak_cut_run SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 _ _ _ _ _ (k2 + 1) ly4 S4 W4 ms4 msB md4 mdB HC4
    HJ4' KB (fun x Hx => HGB x Hx) FdB FsB) as HCB.
  pose proof (lf_cur_keep (fun _ => False) cx W4 ms4 W4 msB P N KB (fun a _ H => H) Hcur4) as HcurB.
  pose proof (fun H1 => r_atbuf_run W4 mem4 (ms_mem msB) t1 kc _ KB HGB (Hbuf4 H1)) as BUF1B.
  lazymatch type of HS with st_ok _ ?Ex ?ssx _ => set (ssB := ssx) in HS; set (EB := Ex) in HS end.
  pmkst HS.
  assert (ELB : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew EB n = getr regs4 r).
  { intros n r Hn Hr. unfold EB. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat _ _ n r Hr). }
  prreg HS (1%bv : bv 5) B1. prreg HS (2%bv : bv 5) B2. prreg HS (3%bv : bv 5) B3.
  prreg HS (4%bv : bv 5) B4. prreg HS (8%bv : bv 5) B8. prreg HS (9%bv : bv 5) B9. prreg HS (10%bv : bv 5) B10.
  prreg HS (18%bv : bv 5) B18. prreg HS (19%bv : bv 5) B19. prreg HS (20%bv : bv 5) B20.
  prreg HS (21%bv : bv 5) B21. prreg HS (22%bv : bv 5) B22. prreg HS (23%bv : bv 5) B23.
  prreg HS (24%bv : bv 5) B24. prreg HS (25%bv : bv 5) B25. prreg HS (26%bv : bv 5) B26.
  prreg HS (27%bv : bv 5) B27.
  rewrite (img_env_codeptr EB HEI4) in B1.
  rewrite (ELB 2%nat 2%bv ltac:(lia) eq_refl), P2, Q2 in B2. rewrite (ELB 3%nat 3%bv ltac:(lia) eq_refl), P3, Q3 in B3.
  rewrite (ELB 4%nat 4%bv ltac:(lia) eq_refl), P4, Q4 in B4. rewrite (ELB 8%nat 8%bv ltac:(lia) eq_refl), P8, Q8 in B8.
  rewrite (ELB 9%nat 9%bv ltac:(lia) eq_refl), P9, Q9 in B9.
  rewrite (ELB 27%nat 27%bv ltac:(lia) eq_refl), P27, Q27 in B10.
  rewrite (ELB 27%nat 27%bv ltac:(lia) eq_refl), P27, Q27 in B27.
  rewrite (ELB 18%nat 18%bv ltac:(lia) eq_refl), P18, Q18 in B18.
  rewrite (ELB 19%nat 19%bv ltac:(lia) eq_refl), P19, Q19 in B19.
  rewrite (ELB 20%nat 20%bv ltac:(lia) eq_refl), P20, Q20 in B20.
  rewrite (ELB 21%nat 21%bv ltac:(lia) eq_refl), P21, Q21 in B21.
  rewrite (ELB 22%nat 22%bv ltac:(lia) eq_refl), P22, Q22 in B22.
  rewrite (ELB 10%nat 10%bv ltac:(lia) eq_refl), HT10 in B23.
  rewrite (ELB 24%nat 24%bv ltac:(lia) eq_refl), P24, Q24 in B24.
  rewrite (ELB 25%nat 25%bv ltac:(lia) eq_refl), P25, Q25 in B25.
  rewrite (ELB 26%nat 26%bv ltac:(lia) eq_refl), P26, Q26 in B26.
  rewrite HBASE in B1.
  assert (HspB : spZ (ms_regs msB) = lf_sp1 cx)
    by (unfold spZ; rewrite B2; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  assert (Hs0B : s0Z (ms_regs msB) = spZ (c_regs cx))
    by (unfold s0Z; rewrite B8; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
  assert (Ha0B : aarg (ms_regs msB) 0 = ac) by (rewrite ar_aarg0, B10; unfold w64; apply unsigned_lit_small; lia).
  pose proof HCB as (HJB & HFRB & HSAVB & _ & _ & _ & HJBKB & HBLKB & _).
  pose proof HJBKB as (HkB & HbbB & _ & _ & _ & _ & _ & _ & _ & _ & HblB & HincB & _ & HroB & _).
  destruct (lf_saved_ra_s0 cx W4 msB HSAVB) as (HR8B & HR16B).
  assert (HpcB : ss_pc ssB = pa_sigma LS_text_buf) by reflexivity.
  rewrite HpcB.
  eapply SRr_bind.
  { replace (pa_sigma LS_text_buf) with TEXT_BUF_A by (rewrite (lv_sigma LV); reflexivity).
    change (mkCfg (mkst (ms_regs msB) (Z_to_bv 64 TEXT_BUF_A) (ms_mem msB) (seg_rom SEGS)) mdB)
      with (cfg_at (fx := fy) SEGS TEXT_BUF_A (ms_regs msB) (ms_mem msB) mdB).
    apply (lf_text_buf_call fy cx fp (k2 + 1) (lf_ev i + 1) (LF_LIVE_HELD + TEXT_BUF_LIVE) ly4 S4 W4 (ms_mem msB) mdB
      (ms_regs msB) 5176 HB HJB
      HkB ltac:(unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB; lia) HbbB
      ltac:(pose proof LF_LIVE_HELD_room; unfold TEXT_BUF_LIVE; lia) HroB HR8B HR16B HspB Hs0B ltac:(lia) B3 B4 HBASE
      B1 ltac:(unfold LF_TEXT_BUF_SITES, AF_LLVMFuzzerTestOneInput; right; left; reflexivity)). }
  intros W5 c5 Hle5 HPOST.
  destruct HPOST as (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HPRES5 & HFR5 & HFD5 & HFS5 & HKEPT5 & HSHK5 &
    HMO5 & HLED5 & HPA5).
  set (ms5 := @mkst fy regs5 (getr (ms_regs msB) 1) mem5 (seg_rom SEGS)).
  destruct (lf_text_buf_after cx fp md mk kbs mbs gbs T3 _ _ _ _ _ (k2 + 1) ly4 S4 W4 msB mdB (ms_regs msB) ly5 S5 W5
    regs5 mem5 md5 ms5 (lf_mo LF_MO_SET LF_MO_OP i) HB HJB HCB HspB ltac:(rewrite Ha0B; lia) eq_refl HJ5 HFR5 HFD5
    HFS5 HKEPT5 HSHK5 HLED5 HPA5)
    as (t2 & nb2 & HT20 & Hnb2 & HC5 & HRO5 & Hsub5 & Hnbin5 & Hap5 & HCALL5 & Hbuf5).
  rewrite Ha0B in Hnb2, Hbuf5.
  pose proof (ar_pres _ _ HPRES5) as (P2' & P3' & P4' & P8' & P9' & P18' & P19' & P20' & P21' & P22' & P23' & P24'
    & P25' & P26' & P27').
  pose proof (lf_cur_callee B cx TEXT_BUF_AK ly4 S4 ly5 S5 W4 msB W5 ms5 _ P N HCALL5
    ltac:(intros a _ (r & Hin & _); destruct Hin) HcurB) as Hcur5.
  (* ---- +0xe30: s10 := alias, to the cut at +0xe34 ---- *)
  unfold ms5. rewrite B1, <- HBASE.
  clear HS SHOK.
  assert (Usp5 : spZ regs5 = lf_sp1 cx) by (unfold spZ in *; rewrite P2'; exact HspB).
  pose proof (aw_entry0 (fx := fy) W5 regs5 mem5 5176 ltac:(rewrite Usp5; unfold LLVMF_STK in *; lia)
    ltac:(rewrite Usp5; lia)) as HS.
  assert (HEI5 : img_env pa_val A_LIM (Eimg (Ereg regs5 aw_extra0))) by apply Eimg_env.
  assert (SHOK : sh_ok pa_segs aw_Bx [] (Eimg (Ereg regs5 aw_extra0))
    (mrestrict (w_H W5) (ms_mem (@mkst fy regs5 (Z_to_bv 64 (BASE + 5176)) mem5 (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  pose proof HC5 as (HJ5' & _).
  change (ms_mem ms5) with mem5 in HJ5'.
  pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
  paj_run_to_tok RUNTO HS HJ5' SHOK aw_span LR_t; [apply awr_ok_x_nil|].
  rename ms into msC, HF into HFC, HFr into HFrC, HG into HGC.
  pose proof (kagree_frame_nil _ _ _ HFrC) as KC.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdC := mdx) in * end.
  assert (FdC : m_fds mdC = m_fds md5) by (subst mdC; rewrite !lf_wvb_fds; reflexivity).
  assert (FsC : m_fs mdC = m_fs md5) by (subst mdC; rewrite !lf_wvb_fs; reflexivity).
  pose proof (ak_cut_run SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 _ _ _ _ _ (k2 + 1 + 1) ly5 S5 W5 ms5 msC md5 mdC
    HC5 HJ5' KC (fun x Hx => HGC x Hx) FdC FsC) as HCC.
  pose proof (lf_cur_keep (fun _ => False) cx W5 ms5 W5 msC P N KC (fun a _ H => H) Hcur5) as HcurC.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx _ => set (ssC := ssx) in HS; set (EC := Ex) in HS end.
  assert (EL5 : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew EC n = getr regs5 r).
  { intros n r Hn Hr. unfold EC. repeat rewrite ew_ewset_other by lia.
    rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat _ _ n r Hr). }
  prreg HS (2%bv : bv 5) C2'. prreg HS (3%bv : bv 5) C3'. prreg HS (4%bv : bv 5) C4'. prreg HS (8%bv : bv 5) C8'.
  prreg HS (9%bv : bv 5) C9'.
  prreg HS (18%bv : bv 5) C18. prreg HS (19%bv : bv 5) C19. prreg HS (20%bv : bv 5) C20.
  prreg HS (21%bv : bv 5) C21. prreg HS (22%bv : bv 5) C22. prreg HS (23%bv : bv 5) C23.
  prreg HS (24%bv : bv 5) C24. prreg HS (25%bv : bv 5) C25. prreg HS (26%bv : bv 5) C26.
  prreg HS (27%bv : bv 5) C27.
  rewrite (EL5 2%nat 2%bv ltac:(lia) eq_refl), P2', B2 in C2'. rewrite (EL5 3%nat 3%bv ltac:(lia) eq_refl), P3', B3 in C3'.
  rewrite (EL5 4%nat 4%bv ltac:(lia) eq_refl), P4', B4 in C4'. rewrite (EL5 8%nat 8%bv ltac:(lia) eq_refl), P8', B8 in C8'.
  rewrite (EL5 9%nat 9%bv ltac:(lia) eq_refl), P9', B9 in C9'.
  rewrite (EL5 18%nat 18%bv ltac:(lia) eq_refl), P18', B18 in C18.
  rewrite (EL5 19%nat 19%bv ltac:(lia) eq_refl), P19', B19 in C19.
  rewrite (EL5 20%nat 20%bv ltac:(lia) eq_refl), P20', B20 in C20.
  rewrite (EL5 21%nat 21%bv ltac:(lia) eq_refl), P21', B21 in C21.
  rewrite (EL5 22%nat 22%bv ltac:(lia) eq_refl), P22', B22 in C22.
  rewrite (EL5 23%nat 23%bv ltac:(lia) eq_refl), P23', B23 in C23.
  rewrite (EL5 24%nat 24%bv ltac:(lia) eq_refl), P24', B24 in C24.
  rewrite (EL5 25%nat 25%bv ltac:(lia) eq_refl), P25', B25 in C25.
  rewrite (EL5 10%nat 10%bv ltac:(lia) eq_refl), HT20 in C26.
  rewrite (EL5 27%nat 27%bv ltac:(lia) eq_refl), P27', B27 in C27.
  (* the two fresh blocks *)
  assert (HPB3 : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by exact (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS cx fp ly3 S3 W3
              (ms_mem msA) mdA k2 HB HJA).
  pose proof HBLKA as (Bmd3 & Bmk3 & _).
  assert (RQ : forall cap t nb, tb_nb cap t nb -> forall b, In b nb -> 1 <= req_size (snd b)).
  { intros cap t nb [(_ & _ & ->) | (Hc1 & _ & ->)] b Hb; [destruct Hb|]. destruct Hb as [<- | []].
    cbn [snd]. unfold req_size. destruct (cap + 1 =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | lia]. }
  pose proof (d4_fresh_ok B cx md mk T3 _ ly3 S3 nb1 HblA Bmd3 Bmk3 HincA HPB3 Hap4 (RQ _ _ _ Hnb1)) as FR1.
  pose proof (d4_fresh_ok B cx md mk T3 _ ly4 S4 nb2 HblB (Hsub4 _ Bmd3) (Hsub4 _ Bmk3) HincB
    (fun Hn => Hsub4 _ (HPB3 Hn)) Hap5 (RQ _ _ _ Hnb2)) as FR2.
  apply (HT cx fy fp (k2 + 1 + 1) ly5 S5 W5 msC mdC HB Hfx HJ5' ltac:(rewrite HFR5, HFR4; exact Hfr)).
  exists md, mk, P, N, kbs, mbs, gbs, T3, s, nm, kc, ac, t1, t2, nb1, nb2.
  split; [exact (lf_shape_of_st_ok fy W5 _ _ msC HS eq_refl)|].
  split; [unfold r_regs3; repeat split; assumption|].
  split; [exact Hnm|]. split; [exact Hkc|]. split; [exact Hac|]. split; [exact Hi|].
  split; [unfold lf_core; repeat split; assumption|].
  split.
  { replace (lf_ev i + 2) with (lf_ev i + 1 + 1) by lia.
    replace (LF_LIVE_HELD + 2 * 40) with (LF_LIVE_HELD + TEXT_BUF_LIVE + TEXT_BUF_LIVE) by (unfold TEXT_BUF_LIVE; lia).
    exact HCC. }
  split; [exact HcurC|]. split; [exact Hop|].
  split; [exact Hns|]. split; [exact Hrq|]. split; [exact Hks|]. split; [exact Hra|].
  split.
  { split; [exact Hnb1|]. split; [exact Hnb2|]. split.
    - intros b Hb. apply in_app_or in Hb as [Hb | Hb].
      + destruct (FR1 b Hb) as (Hn & Hd). split; [exact (Hsub5 _ (Hnbin4 b Hb))|]. exact (conj Hn Hd).
      + destruct (FR2 b Hb) as (Hn & Hd). split; [exact (Hnbin5 b Hb)|]. exact (conj Hn Hd).
    - intros b1 b2 Hb1 Hb2. exact (Hap5 b1 b2 (Hnbin4 b1 Hb1) Hb2). }
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly5 S5 W5
    mem5 md5 (k2 + 1 + 1) HB HJ5) as (_ & _ & _ & _ & _ & _ & HAR5).
  split.
  { intros H1. apply (r_atbuf_run W5 mem5 (ms_mem msC) t1 kc _ KC HGC).
    destruct Hnb1 as [(E0 & _) | (_ & _ & ->)]; [lia|].
    apply (r_atbuf_callee cx TEXT_BUF_AK ly4 S4 ly5 S5 W4 (ms_mem msB) W5 mem5 _ md5 t1 kc _ HCALL5 HAR5
      (Hnbin4 _ (or_introl eq_refl)) (Hsub5 _ (Hnbin4 _ (or_introl eq_refl)))); [| lia | exact (BUF1B H1)].
    intros a _ (r & Hin & _). destruct Hin. }
  intros H1. exact (r_atbuf_run W5 mem5 (ms_mem msC) t2 ac _ KC HGC (Hbuf5 H1)).
Qed.

End a.

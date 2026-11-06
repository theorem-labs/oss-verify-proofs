(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Image B's exit-end LS row (row G-BLS-exit of FREE-PIECES.md (sha256 0f44f6fd1403; internal record); B-TOPX-OWNERS.md (sha256 705727227472; internal record) row 48 LS_exit_end;
   the B top lib/B/W_LLVMFuzzerTestOneInput_top_x.v at e43cf0c7bef; k3's lib/B/ReplyBTop.v:90 at a6411d87d21).
   proves no function (kind: invariant lemma).

   WHAT THIS FILE PROVES (a Theorem Labs lane 06:42Z, a Theorem Labs lane 06:45Z / 07:06Z): the B exit text BY ITS OWNER'S NAME,
   a Theorem Labs lane's lib/B/ReplyLS3B_inst.v TX_LS_exit_end_e (A's adopted lib/A/ReplyLSI.v:191-221 word for word:
   the top's LS_exit_end with NP dropped and LS_exit_end3e's four premises last - relay_finish's final capacity, the
   loop's t bound, fr_hblks at the return, NoDup), at the B top's parameters (MT := ameter_triv, XN_LIB := XR0,
   fr_live_post := fr_live_post_b, fr_surv := fr_surv_b TfibB, fr_FP := fr_FP_b, ARX := top_x's ARX,
   G := G_fr_c TfibB, the sink head tfib_sink_head), from a Theorem Labs lane's lib/B/ReplyB3LS3e.v LS_exit_end3e.  It
   re-proves neither LS_exit_end3e nor ou_exit_bytes.
   - bx_TX_LS_exit_end_e: at any LSx with LSx -> fr_LS3c TfibB CR, -> ReplyLSBo.fr_OUT OUT_MAX4, -> fr_ENT TfibB;
   - bx_LS_exit_end_lsi: at decbox's instance ReplyLS3B_inst.LSI TfibB OUT_MAX4 fr_CAP (any fr_CAP), projected by
     decbox's lsi_parts.

   NP: the B texts that k3 re-points still conclude NP (ReplyBTop.v:90 RLV; lib/B/W_LLVMFuzzerTestOneInput_exit_x.v:157
   at a6411d87d21; Btop:285 at e43cf0c7bef) and move to TX_LS_exit_end_e's NP-free text, as A's top did
   (lib/A/W_LLVMFuzzerTestOneInput_top_x.v:646-661 at 14fbe276057).

   WHY THE OLD B TEXT CANNOT BE PROVED: (U1) cap is free (btext_cap_breaks_post); (U2) NP := room_live_cf reads
   allocator state (lib/Reusable/YGcfRoomLive.v:1210-1213) that no premise names; (U3) fr_surv_b needs the entry
   conjunct and fr_hblks at the return (btext_surv_needs_ent); and at e43cf0c7bef fr_live_post_b's OUT_MAX was
   33,554,430 (YCfn_cf.v:38 there) below fr_OUT's OUT_MAX4 = 133,953,540; equal at this base (be3d698ebfa,
   YCfn_cf.v:49): ou_live_post_b_om. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT drain_b_c send_line_b_c gestures_end_b_c gesture_end_c relay_remove_b_c relay_instance_gone_b_c
  RelayCap SlotReads SlotInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBArms ReplyLSBTrPeak ReplyRINVB.
(* the arm files after ReplyLSBArms: the wr_* names are B's _write.v's (lib/B/ReplyB3Base.v's ruling) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_write
W_LLVMFuzzerTestOneInput_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSB ReplyLSBo ReplyLSBoRf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
  ReplyB3Base ReplyB3LS3 ReplyB3LSCntL ReplyB3LS3c ReplyB3LS3Arms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_gone_base.

From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3LS3cArms ReplyB3LS3e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_remove.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_G YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
  W_LLVMFuzzerTestOneInput_top_x ReplyTFIBBcf ReplyLS3B_inst.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Existing Instance YE2k.tfib_sink_head.

(* ================================================================== the constants, read from the B files *)
(* fr_live_post_b's bound is fr_OUT's: YCfn_cf.OUT_MAX (lib/B/YCfn_cf.v:49) is ReplyLSBo.OUT_MAX4 (ReplyLSBo.v:69) *)
Lemma ou_live_post_b_om : YCfn_cf.OUT_MAX = ReplyLSBo.OUT_MAX4.
Proof. reflexivity. Qed.

Section bhb.
Context {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs rc fr_prog_listing (@PB_fr rc)).
(* B's cut fr_hblks (the one fr_ENT and fr_surv_e read) is the driver's fr_hblks_b (the one fr_surv_b reads) *)
Lemma ou_hblks_cut_b : forall (W : world segs) (mem : word -> option byte),
  W_LLVMFuzzerTestOneInput_cut.fr_hblks W mem = YCfn_cf.fr_hblks_b W mem.
Proof. reflexivity. Qed.
End bhb.

(* ================================================================== the texts at the B top's parameters *)
Section bx.
Context {rc : YM05.RunCeil}.
Variable CR : Z.
Variable LSx : @lfcx rc -> Z -> lmod -> alayout -> astate -> Prop.
Hypothesis LSx_3c : forall cx t m ly S, LSx cx t m ly S -> fr_LS3c TfibB CR cx t m ly S.
Hypothesis LSx_OUT : forall cx t m ly S, LSx cx t m ly S -> ReplyLSBo.fr_OUT ReplyLSBo.OUT_MAX4 cx t m ly S.
Hypothesis LSx_ENT : forall cx t m ly S, LSx cx t m ly S -> ReplyB3LS3e.fr_ENT TfibB cx m ly S.

(* ---- decbox's TX_LS_exit_end_e, from ReplyB3LS3e.LS_exit_end3e at OM := OUT_MAX4 (its fr_live_post3_e OUT_MAX4 is
   fr_live_post_b's text, ou_live_post_b_om; its fr_surv_e TfibB is fr_surv_b TfibB, ou_hblks_cut_b) ---- *)
Lemma bx_TX_LS_exit_end_e :
  ReplyLS3B_inst.TX_LS_exit_end_e TfibB ameter_triv ReplyTFIBBcf.XR0 YCfn_cf.fr_live_post_b
    (YCfn_cf.fr_surv_b TfibB) YCfn_cf.fr_FP_b LSx (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (G_fr_c TfibB).
Proof.
  unfold ReplyLS3B_inst.TX_LS_exit_end_e.
  intros cx t m ly3 S3 rest ly' S' W' mem' md' fpos k' C cap out HLS HP HP' Hfr Hmo HC HJ Hcap Ht HFH HND.
  pose proof (LSx_3c cx t m ly3 S3 HLS) as H3c.
  pose proof (LSx_OUT cx t m ly3 S3 HLS) as HOU.
  pose proof (LSx_ENT cx t m ly3 S3 HLS) as HEN.
  pose proof (Z.le_refl ReplyLSBo.OUT_MAX4) as HOM.
  (* decbox's KF-COUNT 09be0e8b51b: LS_exit_end3e concludes the first two conjuncts only; the meter conjunct is
     `exact I` at MT := ameter_triv *)
  assert (R : ReplyB3LS3e.fr_live_post3_e ReplyLSBo.OUT_MAX4 (c_S cx) (stack_free_state 1 fpos S') k' /\
              ReplyB3LS3e.fr_surv_e TfibB (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S')
                W' mem')
    by (eapply ReplyB3LS3e.LS_exit_end3e; eassumption).
  destruct R as (R1 & R2).
  split; [| split; [exact R2 | exact I]].
  unfold YCfn_cf.fr_live_post_b. rewrite ou_live_post_b_om. exact R1.
Qed.
End bx.

(* ================================================================== at decbox's LSI *)
(* ReplyLS3B_inst.LSI B OM fr_CAP := fr_LS3cp B YCfn_cf.CALL_ROOM_B /\ fr_OUT OM /\ fr_ENT B /\ fr_CAP (decbox
   8963bbb77ad4, ReplyLS3B_inst.v:228-231), at B := TfibB, OM := OUT_MAX4, fr_CAP its slot (any predicate); its
   projections are decbox's lsi_parts (:234-241). *)
Section bxi.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable fr_CAP : @lfcx rc -> Z -> lmod -> alayout -> astate -> Prop.
Local Notation LSIB := (ReplyLS3B_inst.LSI TfibB ReplyLSBo.OUT_MAX4 fr_CAP).
Lemma lsi_bx_3c : forall cx t m ly S, LSIB cx t m ly S -> fr_LS3c TfibB YCfn_cf.CALL_ROOM_B cx t m ly S.
Proof.
  intros cx t m ly S H.
  destruct (ReplyLS3B_inst.lsi_parts TfibB ReplyLSBo.OUT_MAX4 fr_CAP cx t m ly S H) as (_ & H3c & _). exact H3c.
Qed.
Lemma lsi_bx_OUT : forall cx t m ly S, LSIB cx t m ly S -> ReplyLSBo.fr_OUT ReplyLSBo.OUT_MAX4 cx t m ly S.
Proof.
  intros cx t m ly S H.
  destruct (ReplyLS3B_inst.lsi_parts TfibB ReplyLSBo.OUT_MAX4 fr_CAP cx t m ly S H) as (_ & _ & _ & HO & _). exact HO.
Qed.
Lemma lsi_bx_ENT : forall cx t m ly S, LSIB cx t m ly S -> ReplyB3LS3e.fr_ENT TfibB cx m ly S.
Proof.
  intros cx t m ly S H.
  destruct (ReplyLS3B_inst.lsi_parts TfibB ReplyLSBo.OUT_MAX4 fr_CAP cx t m ly S H) as (_ & _ & _ & _ & HE & _).
  exact HE.
Qed.
(* decbox's TX_LS_exit_end_e at LSI and the B top's parameters: the row's lemma *)
Lemma bx_LS_exit_end_lsi :
  ReplyLS3B_inst.TX_LS_exit_end_e TfibB ameter_triv ReplyTFIBBcf.XR0 YCfn_cf.fr_live_post_b
    (YCfn_cf.fr_surv_b TfibB) YCfn_cf.fr_FP_b LSIB (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (G_fr_c TfibB).
Proof. exact (bx_TX_LS_exit_end_e YCfn_cf.CALL_ROOM_B LSIB lsi_bx_3c lsi_bx_OUT lsi_bx_ENT). Qed.
End bxi.

(* ================================================================== why the B text as stated fails *)
Section bunrestated.
Context {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs rc fr_prog_listing (@PB_fr rc)).
(* (U1) the text's only premise that names cap is the return's block Permutation; with block sizes non-negative
   (BLKN), a kept g_out larger than the entry's live bytes plus OUT_MAX breaks fr_live_post_b whatever LS, the
   journal or the meter say.  LS speaks of S3 and lm_cap m, not of the exit's cap; so fr_live_post_b needs (A1). *)
Lemma btext_cap_breaks_post : forall (cx : @lfcx rc) m rest ly' S' fpos k' cap out,
  Permutation (ablocks TfibB ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  (forall b, In b (input_blks cx ++ rest) -> 0 <= snd b) ->
  0 <= blocks_bytes (c_S cx) -> blocks_bytes (c_S cx) + YCfn_cf.OUT_MAX < cap ->
  ~ YCfn_cf.fr_live_post_b (c_S cx) (stack_free_state 1 fpos S') k'.
Proof.
  intros cx m rest ly' S' fpos k' cap out HP' HN H0 Hbig (HB & _).
  assert (EA : ablocks TfibB ly' (stack_free_state 1 fpos S') = ablocks TfibB ly' S') by reflexivity.
  rewrite (blocks_bytes_bsum TfibB ly' (stack_free_state 1 fpos S')), EA, (bsum_perm _ _ HP') in HB.
  assert (Hnn : forall l, (forall b, In b l -> 0 <= snd b) -> 0 <= bsum l).
  { induction l as [|b l IH]; intros Hl; [cbn; lia|]. rewrite bsum_cons.
    pose proof (Hl b (or_introl eq_refl)).
    assert (0 <= bsum l) by (apply IH; intros b' Hb'; apply Hl; right; exact Hb'). lia. }
  assert (H1 : 0 <= bsum (input_blks cx)) by (apply Hnn; intros b Hb; apply HN, in_app_iff; left; exact Hb).
  assert (H2 : 0 <= bsum rest) by (apply Hnn; intros b Hb; apply HN, in_app_iff; right; exact Hb).
  assert (Hc : 0 <= cap) by (unfold YCfn_cf.OUT_MAX in Hbig; lia).
  repeat progress (rewrite ?bsum_app, ?bsum_cons in HB). cbn [snd] in HB.
  rewrite (ReplyLSBArms.bt_bsum_aout_eq cap out Hc) in HB.
  unfold YCfn_cf.OUT_MAX, ATABLE in *. lia.
Qed.
(* (U3) fr_surv_b's first clause needs every entry block that is not an entry harness block among the return's
   blocks, so among input ++ the kept table and g_out ++ the LS state's rest.  That is a fact about the ENTRY's
   blocks (c_ly cx, c_S cx) and the exit's rest; v2's LSxBO = fr_LS /\ fr_OUT holds only an existential rest of S3
   (lib/B/ReplyLSB.v fr_LS) and nothing of c_S's blocks, so it cannot exclude such a block; the entry conjunct
   fr_ENT (LSx_ENT above) is what gives it. *)
Lemma btext_surv_needs_ent : forall (cx : @lfcx rc) m rest ly' S' (W' : world segs) (mem' : word -> option byte)
  fpos cap out b,
  Permutation (ablocks TfibB ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  In b (ablocks TfibB (c_ly cx) (c_S cx)) -> ~ In b (YCfn_cf.fr_hblks_b (c_W cx) (c_mem cx)) ->
  ~ In b (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  ~ YCfn_cf.fr_surv_b TfibB (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem'.
Proof.
  intros cx m rest ly' S' W' mem' fpos cap out b HP' Hb Hnh Hnot (S1 & _ & _).
  assert (EA : ablocks TfibB ly' (stack_free_state 1 fpos S') = ablocks TfibB ly' S') by reflexivity.
  pose proof (S1 b Hb Hnh) as Hin. rewrite EA in Hin.
  exact (Hnot (Permutation_in b HP' Hin)).
Qed.
End bunrestated.

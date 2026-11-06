(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyLS.v, with its module paths and module names changed; 340 of its 445 lines of code are new or changed and 489 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyB3LS3e.v, with its module names changed; 55 of its 164 lines of code are new or changed and 336 lines of the source are left out. *)
(* Theorem Labs, 2026-10-31 (a Theorem Labs lane, route R): image B's twin of image A's lib/A/ReplyLSI.v lsi_LS_exit_end_xR
   (a working branch a35949e2022, :637-665), the exit-end model rule at a world relation R for
   lib/B/W_LLVMFuzzerTestOneInput_exit_x.v's Section lxxR hypothesis LS_exit_end_R (a working branch 1debddc16d1,
   :1072-1086): the strict LS_exit_end (lib/B/W_LLVMFuzzerTestOneInput_exit_x.v :172) with its journal premise ajournal_gx_x -> ajournal_gx_xR .. R.
   - LS_exit_end3e_xR: lib/B/ReplyB3LS3e.v LS_exit_end3e (:506-568) with its journal premise at R.  Its proof is the
     strict proof; it reads the journal only for `0 <= k'`, the eighth conjunct of ajournal_xR at every R.
   - lsi_LS_exit_end_xR: LS_exit_end_R's text at image B's top parameters (lib/B/ReplyLSBExit.v bx_LS_exit_end_lsi,
     row G-BLS-exit: MT := ameter_triv, fr_live_post := YCfn_cf.fr_live_post_b, fr_surv := YCfn_cf.fr_surv_b TfibB,
     PST := []) at k3's LS instance ReplyLS3B_inst.LSI TfibB OUT_MAX4 fr_CAP, for every fr_FP, ARX, G and R, as A's
     lemma quantifies them, and for every XN_LIB (the B top's is ReplyTFIBBcf.XR0; ameter_triv's mo_le holds at every
     bound, and ReplyTFIBBcf is not Required: on this base its closure reaches the 3c base's own errors at
     B/YGcallcf.v:329, B/YD1icf.v:55, B/YD1mcf.v:56).  fr_live_post3_e OUT_MAX4 is fr_live_post_b's text
     (YCfn_cf.OUT_MAX = ReplyLSBo.OUT_MAX4), and fr_surv_e TfibB is fr_surv_b TfibB (the cut's fr_hblks is fr_hblks_b).
   proves no function (kind: route-R lift of an existing model rule). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_write
W_LLVMFuzzerTestOneInput_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSB ReplyLSBo ReplyLSBoRf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
  ReplyB3Base ReplyB3LS3 ReplyB3LSCntL ReplyB3LS3c ReplyB3LS3Arms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_bx_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyB3LS3e ReplyLS3B_inst.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================================================================== the exit rule at R (lib/B/ReplyB3LS3e.v :444-568) *)
Section oexR.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable CALL_ROOM_B : Z.
Context {MT : ameter_ops}.
Variable OM : Z.
Hypothesis HOM : ReplyLSBo.OUT_MAX4 <= OM.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable R : world segs -> world segs -> Prop.

(* ReplyB3LS3e.v :506 LS_exit_end3e, its journal premise ajournal_gx_x segs B PST ARx -> ajournal_gx_xR segs B PST ARx R *)
Lemma LS_exit_end3e_xR : forall cx t m ly3 S3 rest ly' S' (W' : world segs) mem' md' fpos k' C cap out,
  fr_LS3c B CALL_ROOM_B cx t m ly3 S3 -> ReplyLSBo.fr_OUT OM cx t m ly3 S3 -> ReplyB3LS3e.fr_ENT B cx m ly3 S3 ->
  Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  frames S' = [(1, fpos)] -> mo_le MT S3 S' C -> C <= W_bx_defs.lx_exit_cost MT m ->
  cap = gse_cap (W_bx_defs.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) ->
  0 <= t <= OPS_MAX ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] YCfn.LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' (stack_free_state 1 fpos S') [] W' mem' md' k' ->
  W_LLVMFuzzerTestOneInput_cut.fr_hblks W' mem' = (lm_G m, ATABLE) :: aout_blks cap out ->
  List.NoDup (ablocks B ly' S') ->
  ReplyB3LS3e.fr_live_post3_e OM (c_S cx) (stack_free_state 1 fpos S') k' /\
  ReplyB3LS3e.fr_surv_e B (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem'.
Proof using HOM.
  intros cx t m ly3 S3 rest ly' S' W' mem' md' fpos k' C cap out HLS HOU HENT HP HP' Hfr Hmo HC Hcap Ht HJ HFH HND.
  assert (Hk : 0 <= k').
  { destruct HJ as (_ & _ & (memS & HAJ & _) & _).
    destruct HAJ as (_ & _ & _ & _ & _ & _ & _ & Hk0 & _). exact Hk0. }
  assert (EA : ablocks B ly' (stack_free_state 1 fpos S') = ablocks B ly' S') by reflexivity.
  assert (EB : blocks_bytes (stack_free_state 1 fpos S') = blocks_bytes S').
  { rewrite (blocks_bytes_bsum B ly' (stack_free_state 1 fpos S')), (blocks_bytes_bsum B ly' S'), EA. reflexivity. }
  pose proof (HENT rest HP) as HEnt.
  set (FHe := W_LLVMFuzzerTestOneInput_cut.fr_hblks (c_W cx) (c_mem cx)) in *.
  set (NEW := (lm_G m, ATABLE) :: aout_blks cap out) in *.
  split.
  - unfold ReplyB3LS3e.fr_live_post3_e. rewrite EB. split; [| exact Hk].
    eapply ReplyB3LS3e.ou_exit_bytes_e; eassumption.
  - unfold ReplyB3LS3e.fr_surv_e. rewrite EA, HFH. split; [| split].
    + intros b Hb Hnot.
      pose proof (Permutation_in b HEnt Hb) as Hin.
      apply in_app_iff in Hin as [Hin | Hin]; [| apply in_app_iff in Hin as [Hin | Hin]].
      * apply (Permutation_in b (Permutation_sym HP')). apply in_app_iff. left. exact Hin.
      * contradiction.
      * apply (Permutation_in b (Permutation_sym HP')). apply in_app_iff. right.
        apply in_cons, in_app_iff. right. exact Hin.
    + intros b Hb.
      pose proof (Permutation_in b HP' Hb) as Hin.
      apply in_app_iff in Hin as [Hin | Hin].
      * right. apply (Permutation_in b (Permutation_sym HEnt)). apply in_app_iff. left. exact Hin.
      * destruct Hin as [Hin | Hin]; [left; left; exact Hin|].
        apply in_app_iff in Hin as [Hin | Hin].
        -- left. right. exact Hin.
        -- right. apply (Permutation_in b (Permutation_sym HEnt)). apply in_app_iff. right.
           apply in_app_iff. right. exact Hin.
    + intros b Hb.
      destruct (in_dec zzdec b FHe) as [Hfe | Hfe]; [right; exact Hfe|]. left. intros Hin.
      pose proof (Permutation_in b HEnt Hin) as Hin2.
      assert (Hio : In b (input_blks cx) \/ In b rest).
      { apply in_app_iff in Hin2 as [X | X]; [left; exact X|].
        apply in_app_iff in X as [X | X]; [contradiction | right; exact X]. }
      assert (HP'N : Permutation (ablocks B ly' S') (input_blks cx ++ NEW ++ rest))
        by (unfold NEW; exact HP').
      assert (Hcnt : (count_occ zzdec (input_blks cx ++ NEW ++ rest) b <= 1)%nat).
      { pose proof (proj1 (Permutation_count_occ zzdec _ _) HP'N b) as Hq.
        pose proof (proj1 (NoDup_count_occ zzdec _) HND b) as Hc1. lia. }
      rewrite !count_occ_app in Hcnt.
      pose proof (proj1 (count_occ_In zzdec NEW b) Hb) as HbN.
      destruct Hio as [Hio | Hio];
        [pose proof (proj1 (count_occ_In zzdec (input_blks cx) b) Hio) as Hz
        | pose proof (proj1 (count_occ_In zzdec rest b) Hio) as Hz]; lia.
Qed.
End oexR.

(* ================================================================== at k3's LSI and image B's top parameters *)
Section lsiR.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable fr_CAP : @lfcx rc -> Z -> lmod -> alayout -> astate -> Prop.
Variable XN_LIB : Z -> Z.
Local Notation LSIB := (ReplyLS3B_inst.LSI TfibB ReplyLSBo.OUT_MAX4 fr_CAP).
Local Notation MTB := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YCbp.ameter_triv.

(* lib/B/W_LLVMFuzzerTestOneInput_exit_x.v :1072 LS_exit_end_R at B := TfibB, PST := [], MT := ameter_triv, any XN_LIB,
   fr_live_post := fr_live_post_b, fr_surv := fr_surv_b TfibB, LSx := LSI TfibB OUT_MAX4 fr_CAP *)
Lemma lsi_LS_exit_end_xR : forall fr_FP ARX G (R : world segs -> world segs -> Prop),
  forall cx t m ly3 S3 rest ly' S' (W' : world segs) mem' md' fpos k' C cap out,
  LSIB cx t m ly3 S3 ->
  Permutation (ablocks TfibB ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks TfibB ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  frames S' = [(1, fpos)] -> mo_le MTB S3 S' C -> C <= W_bx_defs.lx_exit_cost MTB m ->
  ajournal_gx_xR segs TfibB [] ARX R G 0 [] YCfn.LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' (stack_free_state 1 fpos S') [] W' mem' md' k' ->
  cap = gse_cap (W_bx_defs.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) ->
  0 <= t <= OPS_MAX ->
  W_LLVMFuzzerTestOneInput_cut.fr_hblks W' mem' = (lm_G m, ATABLE) :: aout_blks cap out ->
  List.NoDup (ablocks TfibB ly' S') ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m) ->
  YCfn_cf.fr_live_post_b (c_S cx) (stack_free_state 1 fpos S') k' /\
  YCfn_cf.fr_surv_b TfibB (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem' /\
  mo_le MTB (c_S cx) (stack_free_state 1 fpos S') (XN_LIB (c_n cx)).
Proof using Type.
  intros fr_FP ARX G R cx t m ly3 S3 rest ly' S' W' mem' md' fpos k' C cap out H HP3 HP' Hfr Hmo HC0 HJ Hcap Ht
    HFH HND _.
  destruct (ReplyLS3B_inst.lsi_parts TfibB ReplyLSBo.OUT_MAX4 fr_CAP cx t m ly3 S3 H)
    as (_ & H3c & _ & HO & HE & _).
  destruct (LS_exit_end3e_xR TfibB YCfn_cf.CALL_ROOM_B ReplyLSBo.OUT_MAX4 (Z.le_refl _) [] ARX G fr_FP R
              cx t m ly3 S3 rest ly' S' W' mem' md' fpos k' C cap out H3c HO HE HP3 HP' Hfr Hmo HC0 Hcap Ht HJ HFH HND)
    as (R1 & R2).
  split; [| split; [exact R2 | exact I]].
  unfold YCfn_cf.fr_live_post_b. unfold ReplyB3LS3e.fr_live_post3_e in R1.
  change YCfn_cf.OUT_MAX with ReplyLSBo.OUT_MAX4. exact R1.
Qed.
End lsiR.

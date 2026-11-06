From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL00 YL01 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import StrFun Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import KindB RecFacts RecModel RecInv RecInvP VerbsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_c verbs_receive_since.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_rel verbs_receive_st verbs_receive_step.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_call verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_br.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require VerbsMem rec_shape_of_c RecKindB reply rec_shape_of.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_disp atoi_c sup_reply_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_tail0.
Import ListNotations.
Local Open Scope Z_scope.

Lemma tlm_digits_len : forall k n acc, (length (digits k n acc) <= k + length acc)%nat.
Proof.
  induction k as [|k IH]; intros n acc; cbn [digits]; [lia|].
  destruct (n <? 10); [cbn [length]; lia|].
  specialize (IH (n / 10) (Z_to_bv 8 (48 + n mod 10) :: acc)). cbn [length] in IH. lia.
Qed.

Lemma tlm_resp : forall c, no0 (resp c) /\ (length (resp c) <= 4096)%nat.
Proof.
  intros c. split; [apply resp_no0|]. unfold resp, dec. rewrite !length_app.
  pose proof (tlm_digits_len 10 (Z.abs c) []) as L. cbn [length] in L.
  match goal with |- context [length (bstr ?s)] =>
    let v := eval vm_compute in (length (bstr s)) in change (length (bstr s)) with v end.
  destruct (c <? 0); cbn [length]; lia.
Qed.

Lemma tlm_inst_go_in : forall s d b, In b (inst_go d s) -> b = Z_to_bv 8 49 \/ In b s.
Proof.
  induction s as [|c s IH]; intros d b H; cbn [inst_go] in H; [destruct H|].
  destruct d as [|d].
  - destruct (bv_unsigned c =? 60); destruct H as [H|H].
    + left. symmetry. exact H.
    + apply IH in H. cbn [In]. tauto.
    + cbn [In]. tauto.
    + apply IH in H. cbn [In]. tauto.
  - destruct (bv_unsigned c =? 60); [|destruct (bv_unsigned c =? 62)]; apply IH in H; cbn [In]; tauto.
Qed.

Lemma tlm_inst_no0 : forall s, no0 s -> no0 (inst s).
Proof.
  intros s Hs H. apply tlm_inst_go_in in H. destruct H as [H|H]; [|exact (Hs H)].
  apply (f_equal bv_unsigned) in H. rewrite !byte_unsigned in H by lia. discriminate.
Qed.

Lemma tlm_shape : forall s, In s shape_set -> no0 (inst s) /\ (length (inst s) <= 4096)%nat.
Proof.
  intros s Hs. destruct (shape_set_facts s Hs) as (_ & L & _ & N).
  split; [apply tlm_inst_no0; exact N | lia].
Qed.

Lemma tlm_mod : In REC_MOD_HOST_SHAPE shape_set.
Proof. unfold shape_set. left. reflexivity. Qed.

Lemma tlm_stub : forall R fn A sh ch, In sh shape_set ->
  no0 (snd (rec_stub R fn A sh ch)) /\ (length (snd (rec_stub R fn A sh ch)) <= 4096)%nat.
Proof.
  intros R fn A sh ch Hs. unfold rec_stub. rewrite rec_answer_text.
  destruct (r_refuse (rec_record R fn A) =? 0); [apply tlm_shape; exact Hs | apply tlm_resp].
Qed.

Lemma tlm_add_text : forall R u i p q,
  no0 (snd (sup_add_m R u i p q)) /\ (length (snd (sup_add_m R u i p q)) <= 4096)%nat.
Proof.
  intros R u i p q. unfold sup_add_m. cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
  unfold hand_back; cbn [snd]; apply tlm_resp.
Qed.

Lemma tlm_call_text : forall R c,
  no0 (snd (VerbsRun.run_call R c)) /\ (length (snd (VerbsRun.run_call R c)) <= 4096)%nat.
Proof.
  intros R c. destruct c; unfold VerbsRun.run_call; [apply tlm_add_text|..];
  unfold descriptors_get_m, descriptors_panel_get_m, sup_remove_m, sup_remove_all_m, sup_worker_list_m,
    sup_instance_info_m, sup_reset_m, sup_quarantine_clear_m, sup_policy_set_m, sup_lv2_worker_set_m,
    sup_pool_config_m, sup_worker_env_m, sup_chain_m, sup_chain_clear_m, sup_pin_accept_m,
    sup_instance_verb_m, sup_call_m, sup_connect_m, daemon_shape;
  apply tlm_stub; first [apply shape_of_in | exact tlm_mod].
Qed.

Lemma tlm_bc_text : forall R ln,
  no0 (snd (sup_broadcast_m R ln)) /\ (length (snd (sup_broadcast_m R ln)) <= 4096)%nat.
Proof. intros R ln. unfold sup_broadcast_m. apply tlm_stub. exact tlm_mod. Qed.

Lemma tl_text : forall R s R1 x qt,
  VerbsRun.run_step sup_reply_code_c.reply_code R s = (R1, x, qt) -> no0 x /\ (length x <= 4096)%nat.
Proof.
  intros R s R1 x qt H.
  assert (E : x = snd (fst (VerbsRun.run_step sup_reply_code_c.reply_code R s))) by (rewrite H; reflexivity).
  subst x. clear H. destruct s as [c|c|u i p q|u f l v|u| |ln tk]; unfold VerbsRun.run_step.
  - cbn [fst snd]. apply tlm_resp.
  - cbn [fst snd]. apply tlm_call_text.
  - pose proof (tlm_add_text R (Some u) i p q) as T. revert T.
    destruct (sup_add_m R (Some u) i p q) as [R2 x2]. intros T. exact T.
  - destruct (pins_set_m R (Some u) (Some f) (Some l) v) as [R2 c2].
    cbn [fst snd VerbsRun.pins_follow]. apply tlm_resp.
  - destruct (pins_clear_m R (Some u)) as [R2 c2].
    cbn [fst snd VerbsRun.pins_follow]. apply tlm_resp.
  - cbn [fst snd]. apply tlm_resp.
  - pose proof (tlm_bc_text R ln) as T. revert T.
    destruct (sup_broadcast_m R ln) as [R2 x2]. intros T. exact T.
Qed.

Lemma tlm_rr : forall R fn A, r_nreplies (rec_record R fn A) = r_nreplies R.
Proof. intros R fn A. unfold rec_record. destruct (Nat.ltb (length (r_calls R)) 16); reflexivity. Qed.

Ltac tlm_rr_tac := match goal with |- context [rec_record ?R ?f ?A] =>
  transitivity (r_nreplies (rec_record R f A)); [reflexivity | apply tlm_rr] end.

Lemma tlm_stub_n : forall R fn A sh ch, r_nreplies (fst (rec_stub R fn A sh ch)) = r_nreplies R.
Proof.
  intros R fn A sh ch. unfold rec_stub, rec_answer.
  destruct (r_refuse (rec_record R fn A) =? 0); [destruct ch|]; tlm_rr_tac.
Qed.

Lemma tlm_code_n : forall R fn A, r_nreplies (fst (rec_stub_code R fn A)) = r_nreplies R.
Proof.
  intros R fn A. unfold rec_stub_code. cbv zeta. destruct (r_refuse (rec_record R fn A) =? 0); tlm_rr_tac.
Qed.

Lemma tlm_mix_n : forall R fn A, r_nreplies (rec_stub_mix R fn A) = r_nreplies R.
Proof. intros R fn A. unfold rec_stub_mix. tlm_rr_tac. Qed.

Lemma tlm_host_n : forall R ln tk, r_nreplies (sup_host_setting_m R ln tk) = r_nreplies R.
Proof. intros R ln tk. unfold sup_host_setting_m. cbv zeta. tlm_rr_tac. Qed.

Lemma tlm_add_n : forall R u i p q, r_nreplies (fst (sup_add_m R u i p q)) = r_nreplies R.
Proof.
  intros R u i p q. unfold sup_add_m. cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; tlm_rr_tac.
Qed.

Lemma tlm_call_n : forall R c, r_nreplies (fst (VerbsRun.run_call R c)) = r_nreplies R.
Proof.
  intros R c. destruct c; unfold VerbsRun.run_call; [apply tlm_add_n|..];
  unfold descriptors_get_m, descriptors_panel_get_m, sup_remove_m, sup_remove_all_m, sup_worker_list_m,
    sup_instance_info_m, sup_reset_m, sup_quarantine_clear_m, sup_policy_set_m, sup_lv2_worker_set_m,
    sup_pool_config_m, sup_worker_env_m, sup_chain_m, sup_chain_clear_m, sup_pin_accept_m,
    sup_instance_verb_m, sup_call_m, sup_connect_m;
  apply tlm_stub_n.
Qed.

Lemma tlm_pset_n : forall R u f l v, r_nreplies (fst (pins_set_m R u f l v)) = r_nreplies R.
Proof. intros R u f l v. unfold pins_set_m. apply tlm_code_n. Qed.

Lemma tlm_pclr_n : forall R u, r_nreplies (fst (pins_clear_m R u)) = r_nreplies R.
Proof. intros R u. unfold pins_clear_m. apply tlm_code_n. Qed.

Lemma tlm_bc_n : forall R ln, r_nreplies (fst (sup_broadcast_m R ln)) = r_nreplies R.
Proof. intros R ln. unfold sup_broadcast_m. apply tlm_stub_n. Qed.

Lemma tl_nrep : forall R s R1 x qt,
  VerbsRun.run_step sup_reply_code_c.reply_code R s = (R1, x, qt) -> r_nreplies R1 = r_nreplies R.
Proof.
  intros R s R1 x qt H.
  assert (E : R1 = fst (fst (VerbsRun.run_step sup_reply_code_c.reply_code R s))) by (rewrite H; reflexivity).
  subst R1. clear H. destruct s as [c|c|u i p q|u f l v|u| |ln tk]; unfold VerbsRun.run_step.
  - reflexivity.
  - cbn [fst snd]. apply tlm_call_n.
  - pose proof (tlm_add_n R (Some u) i p q) as T. revert T.
    destruct (sup_add_m R (Some u) i p q) as [R2 x2]. cbn [fst snd]. intros T.
    destruct (0 <=? sup_reply_code_c.reply_code x2); [|exact T].
    unfold descriptors_add_m. rewrite tlm_mix_n. exact T.
  - pose proof (tlm_pset_n R (Some u) (Some f) (Some l) v) as T. revert T.
    destruct (pins_set_m R (Some u) (Some f) (Some l) v) as [R2 c2].
    cbn [fst snd VerbsRun.pins_follow]. intros T.
    destruct (c2 =? 0); [|exact T]. unfold lv2_refusals_forget_m. rewrite tlm_mix_n. exact T.
  - pose proof (tlm_pclr_n R (Some u)) as T. revert T.
    destruct (pins_clear_m R (Some u)) as [R2 c2].
    cbn [fst snd VerbsRun.pins_follow]. intros T.
    destruct (c2 =? 0); [|exact T]. unfold lv2_refusals_forget_m. rewrite tlm_mix_n. exact T.
  - reflexivity.
  - pose proof (tlm_bc_n R ln) as T. revert T.
    destruct (sup_broadcast_m R ln) as [R2 x2]. cbn [fst snd]. intros T.
    rewrite tlm_host_n. exact T.
Qed.

Lemma tl_run : forall R D R1 x q,
  VerbsRun.run_step sup_reply_code_c.reply_code R (plan_at (route (toks D)) atoi_c.atoi_val (line D) (toks D)) = (R1, x, q) ->
  vr_run R D = (match Verbs.after atoi_c.atoi_val (toks D) with
                | Some (i, v) => sup_after_reply_m (fst (socket_send_m R1 (x ++ [Z_to_bv 8 0]))) i (Some v)
                | None => fst (socket_send_m R1 (x ++ [Z_to_bv 8 0]))
                end, x, q).
Proof.
  intros R D R1 x q. unfold vr_run, VerbsRun.run_receive, Verbs.receive.
  destruct (toks D) as [|t tk]; intros H.
  - cbn [plan_at] in H. unfold reject in H. rewrite H. reflexivity.
  - rewrite plan_route by discriminate. rewrite H. reflexivity.
Qed.

Lemma tl_after_short : forall (atoi : list byte -> Z) tk, (length tk <= 1)%nat -> Verbs.after atoi tk = None.
Proof.
  intros atoi tk H. destruct tk as [|a [|b tk]]; [reflexivity|reflexivity|]. cbn [length] in H. lia.
Qed.

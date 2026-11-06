(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the functional facts the segments S05 (EMPTY) and S30 (JOIN) of the walk of
   verbs_receive (lib/A/Prog/verbs_receive_iface.v) use about the model, with the ASan wrappers' reply code: the
   handler's reply text is at most 4096 bytes and the handler keeps r_nreplies (the plain proof's tl_text / tl_nrep,
   lib/Prog/verbs_receive_tail_m.v:100, :168, for any reply-code function), a handler run from a recorder with no
   call records at most two (the plain proof's step_frame, lib/Prog/HarnessPropsProof.v:1361, for any recorder state
   with no call), the empty message's step, and the call after the reply with one word. No machine state. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_tail_m verbs_receive_pre SlotRec.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRep.
Import ListNotations.
Local Open Scope Z_scope.

Module TM := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_tail_m.

(* lib/Prog/verbs_receive_tail_m.v:100 tl_text, for any reply-code function (the text never depends on it) *)
Lemma vrm_text : forall (rcode : list byte -> Z) R s R1 x qt,
  VerbsRun.run_step rcode R s = (R1, x, qt) -> no0 x /\ (length x <= 4096)%nat.
Proof.
  intros rcode R s R1 x qt H.
  assert (E : x = snd (fst (VerbsRun.run_step rcode R s))) by (rewrite H; reflexivity).
  subst x. clear H. destruct s as [c|c|u i p q|u f l v|u| |ln tk]; unfold VerbsRun.run_step.
  - cbn [fst snd]. apply TM.tlm_resp.
  - cbn [fst snd]. apply TM.tlm_call_text.
  - pose proof (TM.tlm_add_text R (Some u) i p q) as T. revert T.
    destruct (sup_add_m R (Some u) i p q) as [R2 x2]. intros T. exact T.
  - destruct (pins_set_m R (Some u) (Some f) (Some l) v) as [R2 c2].
    cbn [fst snd VerbsRun.pins_follow]. apply TM.tlm_resp.
  - destruct (pins_clear_m R (Some u)) as [R2 c2].
    cbn [fst snd VerbsRun.pins_follow]. apply TM.tlm_resp.
  - cbn [fst snd]. apply TM.tlm_resp.
  - pose proof (TM.tlm_bc_text R ln) as T. revert T.
    destruct (sup_broadcast_m R ln) as [R2 x2]. intros T. exact T.
Qed.

(* lib/Prog/verbs_receive_tail_m.v:168 tl_nrep, for any reply-code function *)
Lemma vrm_nrep : forall (rcode : list byte -> Z) R s R1 x qt,
  VerbsRun.run_step rcode R s = (R1, x, qt) -> r_nreplies R1 = r_nreplies R.
Proof.
  intros rcode R s R1 x qt H.
  assert (E : R1 = fst (fst (VerbsRun.run_step rcode R s))) by (rewrite H; reflexivity).
  subst R1. clear H. destruct s as [c|c|u i p q|u f l v|u| |ln tk]; unfold VerbsRun.run_step.
  - reflexivity.
  - cbn [fst snd]. apply TM.tlm_call_n.
  - pose proof (TM.tlm_add_n R (Some u) i p q) as T. revert T.
    destruct (sup_add_m R (Some u) i p q) as [R2 x2]. cbn [fst snd]. intros T.
    destruct (0 <=? rcode x2); [|exact T].
    unfold descriptors_add_m. rewrite TM.tlm_mix_n. exact T.
  - pose proof (TM.tlm_pset_n R (Some u) (Some f) (Some l) v) as T. revert T.
    destruct (pins_set_m R (Some u) (Some f) (Some l) v) as [R2 c2].
    cbn [fst snd VerbsRun.pins_follow]. intros T.
    destruct (c2 =? 0); [|exact T]. unfold lv2_refusals_forget_m. rewrite TM.tlm_mix_n. exact T.
  - pose proof (TM.tlm_pclr_n R (Some u)) as T. revert T.
    destruct (pins_clear_m R (Some u)) as [R2 c2].
    cbn [fst snd VerbsRun.pins_follow]. intros T.
    destruct (c2 =? 0); [|exact T]. unfold lv2_refusals_forget_m. rewrite TM.tlm_mix_n. exact T.
  - reflexivity.
  - pose proof (TM.tlm_bc_n R ln) as T. revert T.
    destruct (sup_broadcast_m R ln) as [R2 x2]. cbn [fst snd]. intros T.
    rewrite TM.tlm_host_n. exact T.
Qed.

(* lib/Prog/HarnessPropsProof.v:1361 step_frame's call count, from any recorder state that holds no call *)
Lemma vrm_calls : forall (rcode : list byte -> Z) R s, r_calls R = [] ->
  (length (r_calls (fst (fst (VerbsRun.run_step rcode R s)))) <= 2)%nat.
Proof.
  intros rcode [rf cd cl sp an nr rp st hs] s Hc. cbn in Hc. subst cl.
  destruct s as [c0|c|u i p q|u f l v|u| |ln tk]; [|destruct c|..];
    unfold VerbsRun.run_step, VerbsRun.run_call, VerbsRun.pins_follow, sup_add_m, descriptors_get_m,
      descriptors_panel_get_m, sup_remove_m, sup_remove_all_m, sup_worker_list_m, sup_instance_info_m, sup_reset_m,
      sup_quarantine_clear_m, sup_policy_set_m, sup_lv2_worker_set_m, sup_pool_config_m, sup_worker_env_m,
      sup_chain_m, sup_chain_clear_m, sup_pin_accept_m, sup_instance_verb_m, sup_call_m, sup_connect_m,
      sup_broadcast_m, sup_host_setting_m, pins_set_m, pins_clear_m, lv2_refusals_forget_m, descriptors_add_m,
      rec_stub, rec_answer, hand_back, rec_record, rec_mix, rec_mix_host, rec_stub_code, rec_answer_code,
      rec_stub_mix; cbn;
    repeat (match goal with |- context [if ?c then _ else _] => destruct c end; cbn);
    lia.
Qed.

(* the empty message: no word, so the step is sup_resp(-902) and no call follows the reply *)
Lemma vrm_empty : forall (atoi : list byte -> Z) D, Verbs.toks D = [] ->
  Verbs.receive atoi D = (Verbs.SResp (-902), None).
Proof. intros atoi D H. unfold Verbs.receive. rewrite H. reflexivity. Qed.

(* one word: no call after the reply (lib/Prog/verbs_receive_tail_m.v tl_after_short) *)
Lemma vrm_after_one : forall (atoi : list byte -> Z) D, length (Verbs.toks D) = 1%nat ->
  snd (Verbs.receive atoi D) = None.
Proof.
  intros atoi D H. unfold Verbs.receive.
  destruct (Verbs.toks D) as [|t tk] eqn:E; [reflexivity|]. cbn [snd].
  apply TM.tl_after_short. try rewrite E in H. cbn [length] in H |- *. lia.
Qed.

(* the trimmed line is no longer than the bytes strndup copied (lib/Prog/verbs_receive_pre.v:64 strnlen_upto,
   lib/Prog/SlotRec.v:623 line_len) *)
Lemma vrm_line_le : forall D, Z.of_nat (length (Verbs.line D)) <= StrFun.strnlen_res (Z.of_nat (length D)) D.
Proof. intros D. rewrite (proj2 (verbs_receive_pre.strnlen_upto D)). pose proof (SlotRec.line_len D). lia. Qed.
Lemma vrm_l_le : forall n D, 0 <= n -> 0 <= StrFun.strnlen_res n D <= n.
Proof. intros n D Hn. exact (verbs_receive_pre.strnlen_res_le n D Hn). Qed.

(* How many arguments one message records, for any value of atoi and of the reply code.

   The recorder keeps, for each daemon call of a message, the call's arguments (lib/Prog/RecModel.v:38-39
   rec_record); the allocator events of rec_clear, rec_calls_copy, rec_calls_free and check_round_trip are one per
   recorded argument (lib/A/Prog/CmdRep.v:120-121 ev_args). The type caps (16 calls of 6 arguments,
   H/recorder.h:40-41) give 96 arguments; the handlers record far fewer. From a cleared recorder one step records at
   most 2 calls and at most 5 arguments: sup_add then descriptors_add (4 + 1), pins_set then lv2_refusals_forget
   (4 + 1), sup_broadcast then sup_host_setting (1 + 3); every other handler records one call of at most 4
   arguments (a derivation by hand from the source gives the same). The whole run of one message
   (run_receive, lib/Spec/VerbsRun.v:59-64: the step, the reply, and sup_after_reply for preset_load and patch_set)
   keeps both bounds, because the verbs with an after-reply call are instance verbs, whose step is one sup_call of 2
   arguments.

   step_frame_at is the released step_frame (lib/Prog/HarnessPropsProof.v:1363-1376) at any reply code, step_args
   its argument count, and run_args the bound for the whole message. All hold for every atoi and reply code, so for
   the plain image (atoi_val, reply_code) and the ASan image (atoi_a, reply_code_a, lib/A/Prog/sup_reply_code_c.v:47-52)
   alike. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
Import ListNotations.
Open Scope Z_scope.

(* the arguments the recorder holds: the body of lib/A/Prog/CmdRep.v:120-121 ev_args, so the two are equal by
   reflexivity *)
Definition ev_args_m (R : rstate) : Z :=
fold_right (fun c acc => Z.of_nat (length (snd c)) + acc) 0 (r_calls R).

(* the released step_frame (lib/Prog/HarnessPropsProof.v:1363-1364) at any reply code: the proof there reads no
   property of it *)
Lemma step_frame_at : forall rc R0 s, let '(R1, x, q) := VerbsRun.run_step rc (rec_clear R0) s in
  r_refuse R1 = r_refuse R0 /\ r_code R1 = r_code R0 /\ r_spill R1 = r_spill R0 /\ (length (r_calls R1) <= 2)%nat.
Proof.
  intros rc R0 s. destruct s as [c0|c|u i p q|u f l v|u| |ln tk]; [|destruct c|..];
    unfold VerbsRun.run_step, VerbsRun.run_call, VerbsRun.pins_follow, sup_add_m, descriptors_get_m,
      descriptors_panel_get_m, sup_remove_m, sup_remove_all_m, sup_worker_list_m, sup_instance_info_m, sup_reset_m,
      sup_quarantine_clear_m, sup_policy_set_m, sup_lv2_worker_set_m, sup_pool_config_m, sup_worker_env_m,
      sup_chain_m, sup_chain_clear_m, sup_pin_accept_m, sup_instance_verb_m, sup_call_m, sup_connect_m,
      sup_broadcast_m, sup_host_setting_m, pins_set_m, pins_clear_m, lv2_refusals_forget_m, descriptors_add_m,
      rec_stub, rec_answer, hand_back, rec_record, rec_mix, rec_mix_host, rec_stub_code, rec_answer_code,
      rec_stub_mix; cbn;
    repeat (match goal with |- context [if ?c then _ else _] => destruct c end; cbn);
    repeat split; cbn; lia.
Qed.

(* one step of the daemon on a cleared recorder records at most 5 arguments *)
Lemma step_args : forall rc R0 s, let '(R1, x, q) := VerbsRun.run_step rc (rec_clear R0) s in ev_args_m R1 <= 5.
Proof.
  intros rc R0 s. destruct s as [c0|c|u i p q|u f l v|u| |ln tk]; [|destruct c|..];
    unfold VerbsRun.run_step, VerbsRun.run_call, VerbsRun.pins_follow, sup_add_m, descriptors_get_m,
      descriptors_panel_get_m, sup_remove_m, sup_remove_all_m, sup_worker_list_m, sup_instance_info_m, sup_reset_m,
      sup_quarantine_clear_m, sup_policy_set_m, sup_lv2_worker_set_m, sup_pool_config_m, sup_worker_env_m,
      sup_chain_m, sup_chain_clear_m, sup_pin_accept_m, sup_instance_verb_m, sup_call_m, sup_connect_m,
      sup_broadcast_m, sup_host_setting_m, pins_set_m, pins_clear_m, lv2_refusals_forget_m, descriptors_add_m,
      rec_stub, rec_answer, hand_back, rec_record, rec_mix, rec_mix_host, rec_stub_code, rec_answer_code,
      rec_stub_mix, ev_args_m; cbn;
    repeat (match goal with |- context [if ?c then _ else _] => destruct c end; cbn);
    lia.
Qed.

(* a verb with an after-reply call (preset_load, patch_set; Verbs.after, lib/Spec/Verbs.v:309-313) is an instance
   verb: its step is one sup_call *)
Lemma plan_after : forall atoi ln v a rest p, (forall b, In b v -> bv_unsigned b <> 32 /\ bv_unsigned b <> 9) ->
  Verbs.after atoi (v :: a :: rest) = Some p ->
  Verbs.plan atoi ln (v :: a :: rest) = Verbs.SCall (Verbs.sup_call (atoi a) ln).
Proof.
  intros atoi ln v a rest p Tv H. unfold Verbs.after in H.
  destruct Verbs.format_words as (_ & _ & _ & _ & FW5 & FW6).
  destruct (Verbs.verb_is_m v Verbs.Lit.fmt_preset_load) eqn:E1.
  { apply (Verbs.verb_is_m_token v _ Tv) in E1. rewrite FW5 in E1. subst v. vm_compute. reflexivity. }
  destruct (Verbs.verb_is_m v Verbs.Lit.fmt_patch_set) eqn:E2; [|discriminate H].
  apply (Verbs.verb_is_m_token v _ Tv) in E2. rewrite FW6 in E2. subst v. vm_compute. reflexivity.
Qed.

(* one message, from a cleared recorder to the state after its reply and its after-reply call, records at most 2
   calls and at most 5 arguments. With R0 the recorder before send_message's rec_clear (H/fuzz_command.c:188) this
   is the state after the message's send; with R0 := set_host (set_state R sb) hb it is the state after
   check_round_trip's second send (lib/Prog/check_round_trip_c.v:26-30). *)
Theorem run_args : forall atoi rc R0 D,
  let '(R1, x, q) := VerbsRun.run_receive atoi rc (rec_clear R0) D in
  (length (r_calls R1) <= 2)%nat /\ ev_args_m R1 <= 5.
Proof.
  intros atoi rc R0 D. unfold VerbsRun.run_receive, Verbs.receive.
  destruct (Verbs.toks D) as [|v args] eqn:Et.
  { cbn. split; [lia | unfold ev_args_m; cbn; lia]. }
  assert (Tv : forall b, In b v -> bv_unsigned b <> 32 /\ bv_unsigned b <> 9).
  { intros b Hb. assert (Hv : In v (Verbs.toks D)) by (rewrite Et; left; reflexivity).
    destruct (Verbs.toks_word D v Hv) as [_ H]. destruct (H b Hb) as (H1 & H2 & _). split; assumption. }
  cbv beta iota.
  destruct (Verbs.after atoi (v :: args)) as [[i w]|] eqn:Ea.
  - destruct args as [|a rest]; [discriminate Ea|].
    rewrite (plan_after atoi (Verbs.line D) v a rest (i, w) Tv Ea).
    unfold VerbsRun.run_step, VerbsRun.run_call, sup_call_m, rec_stub, rec_answer, hand_back, rec_mix,
      sup_after_reply_m, rec_record, ev_args_m; cbn.
    destruct (r_refuse R0 =? 0); cbn; split; lia.
  - pose proof (step_args rc R0 (Verbs.plan atoi (Verbs.line D) (v :: args))) as S.
    pose proof (step_frame_at rc R0 (Verbs.plan atoi (Verbs.line D) (v :: args))) as F.
    destruct (VerbsRun.run_step rc (rec_clear R0) (Verbs.plan atoi (Verbs.line D) (v :: args))) as [[R1 x] q].
    cbv beta iota zeta. destruct F as (_ & _ & _ & F). split; [exact F | exact S].
Qed.

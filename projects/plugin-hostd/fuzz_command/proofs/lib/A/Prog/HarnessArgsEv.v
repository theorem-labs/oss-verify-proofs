(* The allocator events of one call of LLVMFuzzerTestOneInput on the ASan build are at most EV_LIB.

   EV_LTOI (lib/A/Prog/LLVMFuzzerTestOneInput_c.v:115-141) sums, over the at most 32 messages of a payload, the
   event counts of send_message, words_of / words_free, the five checks and check_round_trip at the recorder state
   each message starts from, with rec_clear at the entry and at the exit. Those counts follow the route of each
   message (verbs_receive's ev_vr, lib/A/Prog/verbs_receive_c.v:105-166) and the arguments the recorder holds
   (CmdRep.v ev_args). The bound is proved in three steps:
   - ev_vr_le: one run of verbs_receive from a cleared recorder spends at most 19 events, whatever the route: the
     deepest route is pin_set (pin_set_words, pins_set, lv2_refusals_forget, sup_resp: 10) and the after-reply
     call adds at most 2. Every recorder entry's spill-arm frees are 0, because the table holds at most 2 calls
     (step_frame_at, lib/A/Prog/HarnessArgs.v);
   - ev_msg_le: one message spends at most 78 = 20 + 5 + 3 * 5 + 2 * 19 events, when the recorder it starts from
     holds at most 5 arguments; the state after its first send holds at most 5 (run_args, HarnessArgs.v);
   - ev_msgs_le, by induction over the passes: the loop spends at most 78 per pass and leaves at most 5 arguments.
   So EV_LTOI pl <= 2 + 32 * 78 + 7 = 2,505 <= EV_LIB = 2,900 (lib/A/ACfn.v:26). The measured worst case is 2,372
   (32 x `pin_set a b c`). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRep HarnessArgs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
chain_words_c descriptors_add_c descriptors_get_c descriptors_panel_get_c lv2_refusals_forget_c
pin_set_words_c pins_clear_c pins_set_c reply_c socket_send_c sup_add_c sup_after_reply_c sup_broadcast_c sup_call_c
sup_chain_c sup_chain_clear_c sup_connect_c sup_host_setting_c sup_instance_info_c sup_instance_verb_c
sup_lv2_worker_set_c sup_pin_accept_c sup_policy_set_c sup_pool_config_c sup_quarantine_clear_c sup_remove_c
sup_remove_all_c sup_reply_code_c sup_reset_c sup_resp_c sup_worker_env_c sup_worker_list_c answer_c answer_code_c
hand_back_c arg_i_c arg_line_c rec_canonical_c xstrdup_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_clear_c send_message_c
  check_reply_c check_arity_c check_words_c check_refusal_c check_round_trip_c joined_c rec_calls_copy_c
  verbs_receive_c LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

(* the event counts of the route's program callees, down to their constants *)
Ltac ev_unfold :=
  unfold ev_route, ev_step, ev_call, ev_after,
    EV_CHAIN_WORDS, EV_PIN_SET_WORDS, EV_SUP_ADD, EV_DESCRIPTORS_ADD, EV_DESCRIPTORS_GET, EV_DESCRIPTORS_PANEL_GET,
    EV_SUP_REMOVE, EV_SUP_REMOVE_ALL, EV_SUP_WORKER_LIST, EV_SUP_INSTANCE_INFO, EV_SUP_RESET, EV_SUP_QUARANTINE_CLEAR,
    EV_SUP_POLICY_SET, EV_SUP_LV2_WORKER_SET, EV_SUP_POOL_CONFIG, EV_SUP_WORKER_ENV, EV_SUP_CHAIN, EV_SUP_CHAIN_CLEAR,
    EV_SUP_PIN_ACCEPT, EV_SUP_INSTANCE_VERB, EV_SUP_CALL, EV_SUP_CONNECT, EV_SUP_REPLY_CODE, EV_PINS_SET,
    EV_PINS_CLEAR, EV_LV2_REFUSALS_FORGET, EV_SUP_BROADCAST, EV_SUP_HOST_SETTING, EV_SUP_AFTER_REPLY, EV_SUP_RESP,
    EV_ANSWER_CODE, EV_ANSWER, EV_HAND_BACK, EV_ARG_I, EV_ARG_LINE, EV_REC_CANONICAL, EV_XSTRDUP, rec_spill_frees.

(* the recorder model's entries, to the recorded calls *)
Ltac rec_unfold :=
  unfold sup_add_m, sup_broadcast_m, pins_set_m, pins_clear_m, rec_stub_code, rec_answer_code, rec_stub,
    rec_answer, hand_back, rec_record, rec_mix.

(* case on the innermost conditions first, so that each recorder state's call count is computed before the
   spill-arm test that reads it *)
Ltac ifs := repeat (match goal with |- context [if ?c then _ else _] =>
  lazymatch c with context [if _ then _ else _] => fail | _ => destruct c end end; cbn).

(* one step of the daemon from a cleared recorder: at most 9 events (sup_broadcast then sup_host_setting) *)
Lemma ev_step_le : forall R s, ev_step (rec_clear R) s <= 9.
Proof.
  intros R s. destruct s as [c0|c|u i p q|u f l v|u| |ln tk]; [|destruct c|..];
    ev_unfold; rec_unfold; cbn; ifs; lia.
Qed.

(* the route a message's words select: at most 10 events (pin_set: pin_set_words, pins_set, lv2_refusals_forget,
   then sup_resp) *)
Lemma ev_route_le : forall R ln tk s, ev_route (rec_clear R) ln tk s <= 10.
Proof.
  intros R ln tk s. pose proof (ev_step_le R s) as Hs. unfold ev_route.
  destruct tk as [|v args]; [ev_unfold; lia|].
  match goal with |- context [if Verbs.list_eqb v ?w then _ else _] => destruct (Verbs.list_eqb v w) end;
    [ev_unfold; cbn; lia|].
  match goal with |- context [if Verbs.list_eqb v ?w then _ else _] => destruct (Verbs.list_eqb v w) end;
    [|lia].
  unfold EV_PIN_SET_WORDS. destruct (Verbs.pin_set_words_m ln args); try (ev_unfold; lia).
  ev_unfold; rec_unfold; cbn; ifs; lia.
Qed.

(* the call after the reply, on a recorder of fewer than 16 calls: at most 2 events *)
Lemma ev_after_le : forall R2 af, (length (r_calls R2) < 16)%nat -> ev_after R2 af <= 2.
Proof.
  intros R2 af L. destruct af as [p|]; ev_unfold; [|lia].
  apply Nat.ltb_lt in L. rewrite L. lia.
Qed.

(* one run of verbs_receive from a cleared recorder: strndup, strdup and their frees (4), the route (<= 10), the
   reply (3) and the call after the reply (<= 2) *)
Lemma ev_vr_le : forall R D, ev_vr (rec_clear R) D <= 19.
Proof.
  intros R D. unfold ev_vr. destruct (Verbs.receive atoi_a D) as [st af].
  pose proof (step_frame_at reply_code_a R st) as F.
  pose proof (ev_route_le R (Verbs.line D) (Verbs.toks D) st) as Hr.
  destruct (VerbsRun.run_step reply_code_a (rec_clear R) st) as [[R1 x] q].
  destruct F as (_ & _ & _ & F).
  assert (Ha : ev_after (fst (socket_send_m R1 (x ++ [Z_to_bv 8 0]))) af <= 2).
  { apply ev_after_le. unfold socket_send_m, rec_socket_send. cbn. lia. }
  unfold EV_REPLY, EV_SOCKET_SEND. lia.
Qed.

(* one message of the top loop, from a recorder of at most 5 arguments: send_message, words_of / words_free, the
   five checks and check_round_trip at the state after the first send, as ev_msgs sums them *)
Lemma ev_msg_le : forall R0 D ws, ev_args R0 <= 5 ->
  EV_SEND_MESSAGE R0 D + (3 + 3) + EV_CHECK_REPLY + EV_CHECK_ARITY + EV_CHECK_WORDS + EV_CHECK_REFUSAL +
  EV_CHECK_ROUND_TRIP (fst (fst (vr_runA (RecModel.rec_clear R0) D))) ws <= 78.
Proof.
  intros R0 D ws H.
  assert (H1 : ev_args (fst (fst (vr_runA (RecModel.rec_clear R0) D))) <= 5).
  { pose proof (run_args atoi_a reply_code_a R0 D) as A. unfold vr_runA.
    destruct (VerbsRun.run_receive atoi_a reply_code_a (RecModel.rec_clear R0) D) as [[Ra x] q].
    exact (proj2 A). }
  pose proof (ev_vr_le R0 D) as V0.
  pose proof (ev_vr_le (fst (fst (vr_runA (RecModel.rec_clear R0) D))) (join_sp ws)) as V1.
  unfold EV_CHECK_ROUND_TRIP, EV_SEND_MESSAGE, EV_REC_CLEAR, EV_CHECK_REPLY, EV_CHECK_ARITY, EV_CHECK_WORDS,
    EV_JOINED, EV_CHECK_REFUSAL, EV_SUP_REPLY_CODE, EV_REC_CALLS_COPY, EV_XSTRDUP.
  lia.
Qed.

(* the top loop: at most 78 events per pass, and the recorder it leaves holds at most 5 arguments *)
Lemma ev_msgs_le : forall fuel R pl, ev_args R <= 5 ->
  fst (ev_msgs fuel R pl) <= 78 * Z.of_nat fuel /\ ev_args (snd (ev_msgs fuel R pl)) <= 5.
Proof.
  induction fuel as [|f IH]; intros R pl H.
  - cbn. split; [lia | exact H].
  - destruct pl as [|b pl']; [cbn; split; [lia | exact H]|].
    cbn [ev_msgs].
    match goal with |- context [ev_msgs f ?R1 ?pl2] =>
      assert (H1 : ev_args R1 <= 5);
      [|destruct (IH R1 pl2 H1) as [Ik Is]; destruct (ev_msgs f R1 pl2) as [k Rf]]
    end.
    + match goal with |- ev_args (fst (fst (vr_runA (RecModel.rec_clear ?R0) ?D))) <= 5 =>
        pose proof (run_args atoi_a reply_code_a R0 D) as A; unfold vr_runA;
        destruct (VerbsRun.run_receive atoi_a reply_code_a (RecModel.rec_clear R0) D) as [[Ra x] q];
        exact (proj2 A)
      end.
    + cbn [fst snd] in *. split; [|exact Is].
      rewrite Nat2Z.inj_succ.
      eapply Z.le_trans; [apply Z.add_le_mono; [apply ev_msg_le; exact H | exact Ik] | lia].
Qed.

(* the allocator events of one call of LLVMFuzzerTestOneInput: at most 2 + 32 * 78 + 7 = 2,505 *)
Theorem ev_ltoi_lib : forall pl, EV_LTOI pl <= EV_LIB.
Proof.
  intros pl. unfold EV_LTOI.
  assert (H0 : ev_args R_ENTRY <= 5) by (unfold ev_args; cbn; lia).
  destruct (ev_msgs_le 32 R_ENTRY pl H0) as [Hk Hs].
  destruct (ev_msgs 32 R_ENTRY pl) as [k Rf]. cbn [fst snd] in Hk, Hs.
  unfold EV_REC_CLEAR, EV_LIB. change (ev_args R_ENTRY) with 0. cbn in Hk. lia.
Qed.

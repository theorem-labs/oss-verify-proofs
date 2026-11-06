From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import Verbs VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel verbs_receive_c.

Definition rc_keep (R R' : rstate) : Prop := r_refuse R' = r_refuse R /\ r_code R' = r_code R.

Lemma rc_refl : forall R, rc_keep R R.
Proof. intros R. split; reflexivity. Qed.

Lemma rc_trans : forall R1 R2 R3, rc_keep R1 R2 -> rc_keep R2 R3 -> rc_keep R1 R3.
Proof. intros R1 R2 R3 [A B] [C D]. split; congruence. Qed.

Ltac rc_pair E :=
  match type of E with
  | ?t = ((?a, _), _) => replace a with (fst (fst t)) by (rewrite E; reflexivity)
  | ?t = (?a, _) => replace a with (fst t) by (rewrite E; reflexivity)
  end.

Lemma rc_record : forall R0 R fn A, rc_keep R0 R -> rc_keep R0 (rec_record R fn A).
Proof.
  intros R0 R fn A H. eapply rc_trans; [exact H|].
  unfold rec_record. destruct (Nat.ltb (length (r_calls R)) 16); split; reflexivity.
Qed.

Lemma rc_mix : forall R0 R c, rc_keep R0 R -> rc_keep R0 (rec_mix R c).
Proof. intros R0 R c H. exact H. Qed.

Lemma rc_mix_host : forall R0 R c, rc_keep R0 R -> rc_keep R0 (rec_mix_host R c).
Proof. intros R0 R c H. exact H. Qed.

Lemma rc_hand_back : forall R0 R t, rc_keep R0 R -> rc_keep R0 (fst (hand_back R t)).
Proof. intros R0 R t H. exact H. Qed.

Lemma rc_answer : forall R0 R c s ch, rc_keep R0 R -> rc_keep R0 (fst (rec_answer R c s ch)).
Proof.
  intros R0 R c s ch H. unfold rec_answer.
  destruct (r_refuse R =? 0); [destruct ch|]; exact H.
Qed.

Lemma rc_answer_code : forall R0 R k, rc_keep R0 R -> rc_keep R0 (fst (rec_answer_code R k)).
Proof. intros R0 R k H. exact H. Qed.

Lemma rc_socket_send : forall R0 R x, rc_keep R0 R -> rc_keep R0 (rec_socket_send R x).
Proof. intros R0 R x H. exact H. Qed.

Lemma rc_stub : forall R0 R fn A s ch, rc_keep R0 R -> rc_keep R0 (fst (rec_stub R fn A s ch)).
Proof. intros R0 R fn A s ch H. unfold rec_stub. apply rc_answer. apply rc_record. exact H. Qed.

Lemma rc_stub_code : forall R0 R fn A, rc_keep R0 R -> rc_keep R0 (fst (rec_stub_code R fn A)).
Proof.
  intros R0 R fn A H. unfold rec_stub_code. cbv zeta.
  destruct (r_refuse (rec_record R fn A) =? 0); apply rc_answer_code; [apply rc_mix|];
    apply rc_record; exact H.
Qed.

Lemma rc_stub_mix : forall R0 R fn A, rc_keep R0 R -> rc_keep R0 (rec_stub_mix R fn A).
Proof. intros R0 R fn A H. unfold rec_stub_mix. apply rc_mix. apply rc_record. exact H. Qed.

Lemma rc_socket_send_m : forall R0 R x, rc_keep R0 R -> rc_keep R0 (fst (socket_send_m R x)).
Proof. intros R0 R x H. exact H. Qed.

Lemma rc_sup_resp_m : forall R0 R k, rc_keep R0 R -> rc_keep R0 (fst (sup_resp_m R k)).
Proof. intros R0 R k H. exact H. Qed.

Lemma rc_pins_set_m : forall R0 R u f l v, rc_keep R0 R -> rc_keep R0 (fst (pins_set_m R u f l v)).
Proof. intros R0 R u f l v H. unfold pins_set_m. apply rc_stub_code. exact H. Qed.

Lemma rc_pins_clear_m : forall R0 R u, rc_keep R0 R -> rc_keep R0 (fst (pins_clear_m R u)).
Proof. intros R0 R u H. unfold pins_clear_m. apply rc_stub_code. exact H. Qed.

Lemma rc_lv2_refusals_forget_m : forall R0 R u, rc_keep R0 R -> rc_keep R0 (lv2_refusals_forget_m R u).
Proof. intros R0 R u H. unfold lv2_refusals_forget_m. apply rc_stub_mix. exact H. Qed.

Lemma rc_descriptors_add_m : forall R0 R u, rc_keep R0 R -> rc_keep R0 (descriptors_add_m R u).
Proof. intros R0 R u H. unfold descriptors_add_m. apply rc_stub_mix. exact H. Qed.

Lemma rc_sup_add_m : forall R0 R u i p q, rc_keep R0 R -> rc_keep R0 (fst (sup_add_m R u i p q)).
Proof.
  intros R0 R u i p q H. unfold sup_add_m. cbv zeta.
  destruct ((i <? 0) || (10000 <=? i)).
  - apply rc_hand_back. apply rc_record. exact H.
  - destruct (negb (r_refuse (rec_record R REC_ADD _) =? 0)).
    + apply rc_hand_back. apply rc_record. exact H.
    + apply rc_hand_back. apply rc_mix. apply rc_record. exact H.
Qed.

Lemma rc_sup_broadcast_m : forall R0 R ln, rc_keep R0 R -> rc_keep R0 (fst (sup_broadcast_m R ln)).
Proof. intros R0 R ln H. unfold sup_broadcast_m. apply rc_stub. exact H. Qed.

Lemma rc_sup_host_setting_m : forall R0 R ln tk, rc_keep R0 R -> rc_keep R0 (sup_host_setting_m R ln tk).
Proof.
  intros R0 R ln tk H. unfold sup_host_setting_m. cbv zeta.
  apply rc_mix_host. apply rc_record. exact H.
Qed.

Lemma rc_sup_after_reply_m : forall R0 R i v, rc_keep R0 R -> rc_keep R0 (sup_after_reply_m R i v).
Proof. intros R0 R i v H. unfold sup_after_reply_m. apply rc_record. exact H. Qed.

Lemma rc_call : forall R0 R c, rc_keep R0 R -> rc_keep R0 (fst (run_call R c)).
Proof.
  intros R0 R c H. destruct c; cbn [run_call];
    first
      [ apply rc_sup_add_m; exact H
      | unfold descriptors_get_m, descriptors_panel_get_m, sup_remove_m, sup_remove_all_m,
          sup_worker_list_m, sup_instance_info_m, sup_reset_m, sup_quarantine_clear_m,
          sup_policy_set_m, sup_lv2_worker_set_m, sup_pool_config_m, sup_worker_env_m,
          sup_chain_m, sup_chain_clear_m, sup_pin_accept_m, sup_instance_verb_m, sup_call_m,
          sup_connect_m;
        apply rc_stub; exact H ].
Qed.

Lemma rc_pins_follow : forall R0 R rc, rc_keep R0 R -> rc_keep R0 (fst (pins_follow R rc)).
Proof.
  intros R0 R rc H. unfold pins_follow. cbn [fst].
  destruct (rc =? 0); [apply rc_lv2_refusals_forget_m|]; exact H.
Qed.

Lemma rc_pin_set_run : forall R0 R ln args, rc_keep R0 R -> rc_keep R0 (fst (pin_set_run R ln args)).
Proof.
  intros R0 R ln args H. unfold pin_set_run.
  destruct (Verbs.pin_set_words_m ln args) eqn:W; try exact H.
  match goal with |- context [pins_set_m R ?u ?f ?l ?v] => destruct (pins_set_m R u f l v) as [R1 r] eqn:E end.
  cbn [fst]. apply rc_pins_follow. rc_pair E. apply rc_pins_set_m. exact H.
Qed.

Lemma rc_chain_run : forall R0 R args, rc_keep R0 R -> rc_keep R0 (fst (chain_run R args)).
Proof.
  intros R0 R args H. unfold chain_run.
  destruct (Verbs.chain_words_m args);
    first [ apply rc_call; exact H | apply rc_sup_resp_m; exact H ].
Qed.

Lemma rc_step : forall rcode R0 R s, rc_keep R0 R -> rc_keep R0 (fst (fst (run_step rcode R s))).
Proof.
  intros rcode R0 R s H. destruct s; cbn [run_step fst].
  - exact H.
  - apply rc_call. exact H.
  - match goal with |- context [sup_add_m R ?u ?i ?p ?q] => destruct (sup_add_m R u i p q) as [R1 x] eqn:E end.
    cbn [fst].
    destruct (0 <=? rcode x); [apply rc_descriptors_add_m|]; rc_pair E; apply rc_sup_add_m; exact H.
  - match goal with |- context [pins_set_m R ?u ?f ?l ?v] => destruct (pins_set_m R u f l v) as [R1 r] eqn:E end.
    cbn [fst]. apply rc_pins_follow. rc_pair E. apply rc_pins_set_m. exact H.
  - match goal with |- context [pins_clear_m R ?u] => destruct (pins_clear_m R u) as [R1 r] eqn:E end.
    cbn [fst]. apply rc_pins_follow. rc_pair E. apply rc_pins_clear_m. exact H.
  - exact H.
  - match goal with |- context [sup_broadcast_m R ?l] => destruct (sup_broadcast_m R l) as [R1 x] eqn:E end.
    cbn [fst]. apply rc_sup_host_setting_m. rc_pair E. apply rc_sup_broadcast_m. exact H.
Qed.

Lemma vr_run_rc : forall (R : rstate) (D : list byte),
  r_refuse (fst (fst (vr_run R D))) = r_refuse R /\ r_code (fst (fst (vr_run R D))) = r_code R.
Proof.
  intros R D. change (rc_keep R (fst (fst (vr_run R D)))).
  unfold vr_run, run_receive.
  match goal with |- context [Verbs.receive ?a D] => destruct (Verbs.receive a D) as [st af] end.
  match goal with |- context [run_step ?c R st] => destruct (run_step c R st) as [[R1 x] q] eqn:E end.
  cbn [fst].
  destruct af as [[i v]|]; cbn [fst]; [apply rc_sup_after_reply_m|]; apply rc_socket_send_m;
    rc_pair E; apply rc_step; apply rc_refl.
Qed.

Definition sp_keep (R0 R : rstate) (k : nat) : Prop := r_spill R = r_spill R0 /\ (length (r_calls R) <= k)%nat.

Lemma sp_refl : forall R, sp_keep R R (length (r_calls R)).
Proof. intros R. split; reflexivity. Qed.

Lemma sp_weak : forall R0 R k k', sp_keep R0 R k -> (k <= k')%nat -> sp_keep R0 R k'.
Proof. intros R0 R k k' [Hs Hl] K. split; [exact Hs | lia]. Qed.

Lemma sp_record : forall R0 R k fn A, sp_keep R0 R k -> (k < 16)%nat -> sp_keep R0 (rec_record R fn A) (S k).
Proof.
  intros R0 R k fn A [Hs Hl] K. rewrite rec_record_calls by lia.
  unfold sp_keep, set_calls. cbn [r_spill r_calls]. split; [exact Hs|].
  rewrite length_app. cbn [length]. lia.
Qed.

Lemma sp_mix : forall R0 R k c, sp_keep R0 R k -> sp_keep R0 (rec_mix R c) k.
Proof. intros R0 R k c H. exact H. Qed.

Lemma sp_mix_host : forall R0 R k c, sp_keep R0 R k -> sp_keep R0 (rec_mix_host R c) k.
Proof. intros R0 R k c H. exact H. Qed.

Lemma sp_hand_back : forall R0 R k t, sp_keep R0 R k -> sp_keep R0 (fst (hand_back R t)) k.
Proof. intros R0 R k t H. exact H. Qed.

Lemma sp_answer : forall R0 R k c s ch, sp_keep R0 R k -> sp_keep R0 (fst (rec_answer R c s ch)) k.
Proof.
  intros R0 R k c s ch H. unfold rec_answer.
  destruct (r_refuse R =? 0); [destruct ch|]; exact H.
Qed.

Lemma sp_answer_code : forall R0 R k n, sp_keep R0 R k -> sp_keep R0 (fst (rec_answer_code R n)) k.
Proof. intros R0 R k n H. exact H. Qed.

Lemma sp_socket_send_m : forall R0 R k x, sp_keep R0 R k -> sp_keep R0 (fst (socket_send_m R x)) k.
Proof. intros R0 R k x H. exact H. Qed.

Lemma sp_stub : forall R0 R k fn A s ch, sp_keep R0 R k -> (k < 16)%nat ->
  sp_keep R0 (fst (rec_stub R fn A s ch)) (S k).
Proof. intros R0 R k fn A s ch H K. unfold rec_stub. apply sp_answer. apply sp_record; assumption. Qed.

Lemma sp_stub_code : forall R0 R k fn A, sp_keep R0 R k -> (k < 16)%nat ->
  sp_keep R0 (fst (rec_stub_code R fn A)) (S k).
Proof.
  intros R0 R k fn A H K. unfold rec_stub_code. cbv zeta.
  destruct (r_refuse (rec_record R fn A) =? 0); apply sp_answer_code; [apply sp_mix|];
    apply sp_record; assumption.
Qed.

Lemma sp_stub_mix : forall R0 R k fn A, sp_keep R0 R k -> (k < 16)%nat ->
  sp_keep R0 (rec_stub_mix R fn A) (S k).
Proof. intros R0 R k fn A H K. unfold rec_stub_mix. apply sp_mix. apply sp_record; assumption. Qed.

Lemma sp_pins_set_m : forall R0 R k u f l v, sp_keep R0 R k -> (k < 16)%nat ->
  sp_keep R0 (fst (pins_set_m R u f l v)) (S k).
Proof. intros R0 R k u f l v H K. unfold pins_set_m. apply sp_stub_code; assumption. Qed.

Lemma sp_pins_clear_m : forall R0 R k u, sp_keep R0 R k -> (k < 16)%nat ->
  sp_keep R0 (fst (pins_clear_m R u)) (S k).
Proof. intros R0 R k u H K. unfold pins_clear_m. apply sp_stub_code; assumption. Qed.

Lemma sp_descriptors_add_m : forall R0 R k u, sp_keep R0 R k -> (k < 16)%nat ->
  sp_keep R0 (descriptors_add_m R u) (S k).
Proof. intros R0 R k u H K. unfold descriptors_add_m. apply sp_stub_mix; assumption. Qed.

Lemma sp_sup_add_m : forall R0 R k u i p q, sp_keep R0 R k -> (k < 16)%nat ->
  sp_keep R0 (fst (sup_add_m R u i p q)) (S k).
Proof.
  intros R0 R k u i p q H K. unfold sup_add_m. cbv zeta.
  destruct ((i <? 0) || (10000 <=? i)).
  - apply sp_hand_back. apply sp_record; assumption.
  - destruct (negb (r_refuse (rec_record R REC_ADD _) =? 0)).
    + apply sp_hand_back. apply sp_record; assumption.
    + apply sp_hand_back. apply sp_mix. apply sp_record; assumption.
Qed.

Lemma sp_sup_broadcast_m : forall R0 R k ln, sp_keep R0 R k -> (k < 16)%nat ->
  sp_keep R0 (fst (sup_broadcast_m R ln)) (S k).
Proof. intros R0 R k ln H K. unfold sup_broadcast_m. apply sp_stub; assumption. Qed.

Lemma sp_sup_host_setting_m : forall R0 R k ln tk, sp_keep R0 R k -> (k < 16)%nat ->
  sp_keep R0 (sup_host_setting_m R ln tk) (S k).
Proof.
  intros R0 R k ln tk H K. unfold sup_host_setting_m. cbv zeta.
  apply sp_mix_host. apply sp_record; assumption.
Qed.

Lemma sp_sup_after_reply_m : forall R0 R k i v, sp_keep R0 R k -> (k < 16)%nat ->
  sp_keep R0 (sup_after_reply_m R i v) (S k).
Proof. intros R0 R k i v H K. unfold sup_after_reply_m. apply sp_record; assumption. Qed.

Lemma sp_lv2_refusals_forget_m : forall R0 R k u, sp_keep R0 R k -> (k < 16)%nat ->
  sp_keep R0 (lv2_refusals_forget_m R u) (S k).
Proof. intros R0 R k u H K. unfold lv2_refusals_forget_m. apply sp_stub_mix; assumption. Qed.

Lemma sp_call : forall R0 R k c, sp_keep R0 R k -> (k < 16)%nat -> sp_keep R0 (fst (run_call R c)) (S k).
Proof.
  intros R0 R k c H K. destruct c; cbn [run_call];
    first
      [ apply sp_sup_add_m; assumption
      | unfold descriptors_get_m, descriptors_panel_get_m, sup_remove_m, sup_remove_all_m,
          sup_worker_list_m, sup_instance_info_m, sup_reset_m, sup_quarantine_clear_m,
          sup_policy_set_m, sup_lv2_worker_set_m, sup_pool_config_m, sup_worker_env_m,
          sup_chain_m, sup_chain_clear_m, sup_pin_accept_m, sup_instance_verb_m, sup_call_m,
          sup_connect_m;
        apply sp_stub; assumption ].
Qed.

Lemma sp_pins_follow : forall R0 R k rc, sp_keep R0 R k -> (k < 16)%nat ->
  sp_keep R0 (fst (pins_follow R rc)) (S k).
Proof.
  intros R0 R k rc H K. unfold pins_follow. cbn [fst].
  destruct (rc =? 0); [apply sp_lv2_refusals_forget_m; assumption | eapply sp_weak; [exact H | lia]].
Qed.

Lemma sp_step : forall rcode R0 R k s, sp_keep R0 R k -> (k < 15)%nat ->
  sp_keep R0 (fst (fst (run_step rcode R s))) (S (S k)).
Proof.
  intros rcode R0 R k s H K. destruct s; cbn [run_step fst].
  - eapply sp_weak; [exact H | lia].
  - eapply sp_weak; [apply sp_call; [exact H | lia] | lia].
  - match goal with |- context [sup_add_m R ?u ?i ?p ?q] => destruct (sup_add_m R u i p q) as [R1 x] eqn:E end.
    cbn [fst].
    assert (H1 : sp_keep R0 R1 (S k)) by (rc_pair E; apply sp_sup_add_m; [exact H | lia]).
    destruct (0 <=? rcode x); [apply sp_descriptors_add_m; [exact H1 | lia] | eapply sp_weak; [exact H1 | lia]].
  - match goal with |- context [pins_set_m R ?u ?f ?l ?v] => destruct (pins_set_m R u f l v) as [R1 r] eqn:E end.
    cbn [fst].
    assert (H1 : sp_keep R0 R1 (S k)) by (rc_pair E; apply sp_pins_set_m; [exact H | lia]).
    apply sp_pins_follow; [exact H1 | lia].
  - match goal with |- context [pins_clear_m R ?u] => destruct (pins_clear_m R u) as [R1 r] eqn:E end.
    cbn [fst].
    assert (H1 : sp_keep R0 R1 (S k)) by (rc_pair E; apply sp_pins_clear_m; [exact H | lia]).
    apply sp_pins_follow; [exact H1 | lia].
  - eapply sp_weak; [exact H | lia].
  - match goal with |- context [sup_broadcast_m R ?l] => destruct (sup_broadcast_m R l) as [R1 x] eqn:E end.
    cbn [fst].
    assert (H1 : sp_keep R0 R1 (S k)) by (rc_pair E; apply sp_sup_broadcast_m; [exact H | lia]).
    apply sp_sup_host_setting_m; [exact H1 | lia].
Qed.

Lemma vr_run_spill : forall (R : rstate) (D : list byte), (length (r_calls R) <= 12)%nat ->
  r_spill (fst (fst (vr_run R D))) = r_spill R.
Proof.
  intros R D Hl.
  assert (H : sp_keep R (fst (fst (vr_run R D))) (S (S (S (length (r_calls R)))))).
  { unfold vr_run, run_receive.
    match goal with |- context [Verbs.receive ?a D] => destruct (Verbs.receive a D) as [st af] end.
    match goal with |- context [run_step ?c R st] => destruct (run_step c R st) as [[R1 x] q] eqn:E end.
    cbn [fst].
    assert (H1 : sp_keep R R1 (S (S (length (r_calls R))))) by (rc_pair E; apply sp_step; [apply sp_refl | lia]).
    destruct af as [[i v]|]; cbn [fst].
    - apply sp_sup_after_reply_m; [apply sp_socket_send_m; exact H1 | lia].
    - eapply sp_weak; [apply sp_socket_send_m; exact H1 | lia]. }
  exact (proj1 H).
Qed.

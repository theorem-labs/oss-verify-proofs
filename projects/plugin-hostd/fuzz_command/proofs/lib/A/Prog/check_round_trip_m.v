(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: pure model lemmas for the ASan walk of check_round_trip (lib/A/Prog/check_round_trip.v): send_message's event and meter budgets (lib/A/Prog/send_message_c.v EV_SEND_MESSAGE, XM_SEND_MESSAGE) do not read the recorder's r_state / r_host, and refuse, code and spill survive the ASan run_receive (lib/Prog/CrtVr.v's vr_run_rc / vr_run_spill with the atoi and reply-code functions generic). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRep
chain_words_c descriptors_add_c descriptors_get_c descriptors_panel_get_c lv2_refusals_forget_c pin_set_words_c
pins_clear_c pins_set_c sup_add_c sup_after_reply_c sup_broadcast_c sup_call_c sup_chain_c sup_chain_clear_c
sup_connect_c sup_host_setting_c sup_instance_info_c sup_instance_verb_c sup_lv2_worker_set_c sup_pin_accept_c
sup_policy_set_c sup_pool_config_c sup_quarantine_clear_c sup_remove_c sup_remove_all_c sup_reset_c
sup_worker_env_c sup_worker_list_c rec_clear_c verbs_receive_c send_message_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import CrtVr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* (M1) the recorder fields the route reads: two recorders that agree on refuse, code, calls and spill (they may differ
   in r_state, r_host and the answer / reply fields) take the same route with the same payloads, and every event count
   of the route (each reads R only through rec_spill_frees R, CmdRep.v) is the same on both. *)
Definition crtm_eq (R R' : rstate) : Prop :=
  r_refuse R' = r_refuse R /\ r_code R' = r_code R /\ r_calls R' = r_calls R /\ r_spill R' = r_spill R.

Definition crtm_pair {A : Type} (p p' : rstate * A) : Prop := crtm_eq (fst p) (fst p') /\ snd p' = snd p.

Lemma crtm_eq_sh : forall R s h, crtm_eq R (set_host (set_state R s) h).
Proof. intros R s h. exact (conj eq_refl (conj eq_refl (conj eq_refl eq_refl))). Qed.

Lemma crtm_spill_frees : forall R R', crtm_eq R R' -> rec_spill_frees R' = rec_spill_frees R.
Proof. intros R R' (_ & _ & C & Sp). unfold rec_spill_frees. rewrite C, Sp. reflexivity. Qed.

Lemma crtm_record : forall R R' fn A, crtm_eq R R' -> crtm_eq (rec_record R fn A) (rec_record R' fn A).
Proof.
  intros R R' fn A (F & K & C & Sp). unfold rec_record. rewrite C.
  destruct (Nat.ltb (length (r_calls R)) 16); unfold crtm_eq, set_calls, set_spill;
    cbn [r_refuse r_code r_calls r_spill]; rewrite ?C; repeat split; congruence.
Qed.

Lemma crtm_mix : forall R R' c, crtm_eq R R' -> crtm_eq (rec_mix R c) (rec_mix R' c).
Proof. intros R R' c H. exact H. Qed.

Lemma crtm_mix_host : forall R R' c, crtm_eq R R' -> crtm_eq (rec_mix_host R c) (rec_mix_host R' c).
Proof. intros R R' c H. exact H. Qed.

Lemma crtm_answer : forall R R' c s ch, crtm_eq R R' -> crtm_pair (rec_answer R c s ch) (rec_answer R' c s ch).
Proof.
  intros R R' c s ch H. pose proof H as (F & K & _ & _). unfold rec_answer. rewrite F.
  destruct (r_refuse R =? 0); [destruct ch|]; split; try exact H; cbn [snd hand_back]; congruence.
Qed.

Lemma crtm_answer_code : forall R R' k, crtm_eq R R' -> crtm_pair (rec_answer_code R k) (rec_answer_code R' k).
Proof. intros R R' k H. split; [exact H | reflexivity]. Qed.

Lemma crtm_stub : forall R R' fn A s ch, crtm_eq R R' -> crtm_pair (rec_stub R fn A s ch) (rec_stub R' fn A s ch).
Proof. intros R R' fn A s ch H. unfold rec_stub. apply crtm_answer. apply crtm_record. exact H. Qed.

Lemma crtm_stub_code : forall R R' fn A, crtm_eq R R' -> crtm_pair (rec_stub_code R fn A) (rec_stub_code R' fn A).
Proof.
  intros R R' fn A H. unfold rec_stub_code. cbv zeta.
  pose proof (crtm_record R R' fn A H) as H1. pose proof H1 as (F & K & _ & _). rewrite F.
  destruct (r_refuse (rec_record R fn A) =? 0).
  - apply crtm_answer_code. apply crtm_mix. exact H1.
  - split; [exact H1 | cbn [snd rec_answer_code]; exact K].
Qed.

Lemma crtm_stub_mix : forall R R' fn A, crtm_eq R R' -> crtm_eq (rec_stub_mix R fn A) (rec_stub_mix R' fn A).
Proof. intros R R' fn A H. unfold rec_stub_mix. apply crtm_mix. apply crtm_record. exact H. Qed.

Lemma crtm_socket_send_m : forall R R' x, crtm_eq R R' -> crtm_pair (socket_send_m R x) (socket_send_m R' x).
Proof. intros R R' x H. split; [exact H | reflexivity]. Qed.

Lemma crtm_pins_set_m : forall R R' u f l v, crtm_eq R R' ->
  crtm_pair (pins_set_m R u f l v) (pins_set_m R' u f l v).
Proof. intros R R' u f l v H. unfold pins_set_m. apply crtm_stub_code. exact H. Qed.

Lemma crtm_pins_clear_m : forall R R' u, crtm_eq R R' -> crtm_pair (pins_clear_m R u) (pins_clear_m R' u).
Proof. intros R R' u H. unfold pins_clear_m. apply crtm_stub_code. exact H. Qed.

Lemma crtm_lv2_refusals_forget_m : forall R R' u, crtm_eq R R' ->
  crtm_eq (lv2_refusals_forget_m R u) (lv2_refusals_forget_m R' u).
Proof. intros R R' u H. unfold lv2_refusals_forget_m. apply crtm_stub_mix. exact H. Qed.

Lemma crtm_descriptors_add_m : forall R R' u, crtm_eq R R' ->
  crtm_eq (descriptors_add_m R u) (descriptors_add_m R' u).
Proof. intros R R' u H. unfold descriptors_add_m. apply crtm_stub_mix. exact H. Qed.

Lemma crtm_sup_add_m : forall R R' u i p q, crtm_eq R R' ->
  crtm_pair (sup_add_m R u i p q) (sup_add_m R' u i p q).
Proof.
  intros R R' u i p q H. unfold sup_add_m. cbv zeta.
  match goal with |- context [rec_record R REC_ADD ?A] => pose proof (crtm_record R R' REC_ADD A H) as H1 end.
  pose proof H1 as (F & K & _ & _).
  destruct ((i <? 0) || (10000 <=? i)).
  - split; [exact H1 | reflexivity].
  - rewrite F. destruct (negb (r_refuse (rec_record R REC_ADD _) =? 0)).
    + split; [exact H1 | cbn [snd hand_back]; congruence].
    + split; [apply crtm_mix; exact H1 | reflexivity].
Qed.

Lemma crtm_sup_broadcast_m : forall R R' ln, crtm_eq R R' ->
  crtm_pair (sup_broadcast_m R ln) (sup_broadcast_m R' ln).
Proof. intros R R' ln H. unfold sup_broadcast_m. apply crtm_stub. exact H. Qed.

Lemma crtm_sup_host_setting_m : forall R R' ln tk, crtm_eq R R' ->
  crtm_eq (sup_host_setting_m R ln tk) (sup_host_setting_m R' ln tk).
Proof.
  intros R R' ln tk H. unfold sup_host_setting_m. cbv zeta.
  apply crtm_mix_host. apply crtm_record. exact H.
Qed.

Lemma crtm_sup_after_reply_m : forall R R' i v, crtm_eq R R' ->
  crtm_eq (sup_after_reply_m R i v) (sup_after_reply_m R' i v).
Proof. intros R R' i v H. unfold sup_after_reply_m. apply crtm_record. exact H. Qed.

Lemma crtm_call : forall R R' c, crtm_eq R R' -> crtm_pair (VerbsRun.run_call R c) (VerbsRun.run_call R' c).
Proof.
  intros R R' c H. destruct c; cbn [VerbsRun.run_call];
    first
      [ apply crtm_sup_add_m; exact H
      | unfold descriptors_get_m, descriptors_panel_get_m, sup_remove_m, sup_remove_all_m,
          sup_worker_list_m, sup_instance_info_m, sup_reset_m, sup_quarantine_clear_m,
          sup_policy_set_m, sup_lv2_worker_set_m, sup_pool_config_m, sup_worker_env_m,
          sup_chain_m, sup_chain_clear_m, sup_pin_accept_m, sup_instance_verb_m, sup_call_m,
          sup_connect_m;
        apply crtm_stub; exact H ].
Qed.

Lemma crtm_pins_follow : forall R R' rc, crtm_eq R R' ->
  crtm_pair (VerbsRun.pins_follow R rc) (VerbsRun.pins_follow R' rc).
Proof.
  intros R R' rc H. unfold VerbsRun.pins_follow. split; [|reflexivity].
  cbn [fst]. destruct (rc =? 0); [apply crtm_lv2_refusals_forget_m|]; exact H.
Qed.

Lemma crtm_step : forall rcode R R' s, crtm_eq R R' ->
  crtm_eq (fst (fst (VerbsRun.run_step rcode R s))) (fst (fst (VerbsRun.run_step rcode R' s))) /\
  snd (fst (VerbsRun.run_step rcode R' s)) = snd (fst (VerbsRun.run_step rcode R s)) /\
  snd (VerbsRun.run_step rcode R' s) = snd (VerbsRun.run_step rcode R s).
Proof.
  intros rcode R R' s H.
  destruct s as [k|c|u i p q|u f l v|u| |ln tk]; cbn [VerbsRun.run_step].
  - exact (conj H (conj eq_refl eq_refl)).
  - destruct (crtm_call R R' c H) as [A1 A2]. exact (conj A1 (conj A2 eq_refl)).
  - generalize (crtm_sup_add_m R R' (Some u) i p q H).
    destruct (sup_add_m R (Some u) i p q) as [R1 x]. destruct (sup_add_m R' (Some u) i p q) as [R1' x'].
    intros [A1 A2]. cbn [fst snd] in A1, A2 |- *. subst x'.
    destruct (0 <=? rcode x).
    + exact (conj (crtm_descriptors_add_m R1 R1' (Some u) A1) (conj eq_refl eq_refl)).
    + exact (conj A1 (conj eq_refl eq_refl)).
  - generalize (crtm_pins_set_m R R' (Some u) (Some f) (Some l) v H).
    destruct (pins_set_m R (Some u) (Some f) (Some l) v) as [R1 r].
    destruct (pins_set_m R' (Some u) (Some f) (Some l) v) as [R1' r'].
    intros [A1 A2]. cbn [fst snd] in A1, A2 |- *. subst r'.
    destruct (crtm_pins_follow R1 R1' r A1) as [B1 B2]. exact (conj B1 (conj B2 eq_refl)).
  - generalize (crtm_pins_clear_m R R' (Some u) H).
    destruct (pins_clear_m R (Some u)) as [R1 r]. destruct (pins_clear_m R' (Some u)) as [R1' r'].
    intros [A1 A2]. cbn [fst snd] in A1, A2 |- *. subst r'.
    destruct (crtm_pins_follow R1 R1' r A1) as [B1 B2]. exact (conj B1 (conj B2 eq_refl)).
  - exact (conj H (conj eq_refl eq_refl)).
  - generalize (crtm_sup_broadcast_m R R' ln H).
    destruct (sup_broadcast_m R ln) as [R1 x]. destruct (sup_broadcast_m R' ln) as [R1' x'].
    intros [A1 A2]. cbn [fst snd] in A1, A2 |- *. subst x'.
    exact (conj (crtm_sup_host_setting_m R1 R1' ln tk A1) (conj eq_refl eq_refl)).
Qed.

Lemma crtm_ev_call : forall R R' c, crtm_eq R R' -> ev_call R' c = ev_call R c.
Proof.
  intros R R' c H. destruct c; cbn [ev_call];
    unfold EV_SUP_ADD, EV_DESCRIPTORS_GET, EV_DESCRIPTORS_PANEL_GET, EV_SUP_REMOVE, EV_SUP_REMOVE_ALL,
      EV_SUP_WORKER_LIST, EV_SUP_INSTANCE_INFO, EV_SUP_RESET, EV_SUP_QUARANTINE_CLEAR, EV_SUP_POLICY_SET,
      EV_SUP_LV2_WORKER_SET, EV_SUP_POOL_CONFIG, EV_SUP_WORKER_ENV, EV_SUP_CHAIN, EV_SUP_CHAIN_CLEAR,
      EV_SUP_PIN_ACCEPT, EV_SUP_INSTANCE_VERB, EV_SUP_CALL, EV_SUP_CONNECT;
    rewrite (crtm_spill_frees R R' H); reflexivity.
Qed.

Lemma crtm_ev_step : forall R R' s, crtm_eq R R' -> ev_step R' s = ev_step R s.
Proof.
  intros R R' s H.
  destruct s as [k|c|u i p q|u f l v|u| |ln tk]; cbn [ev_step].
  - reflexivity.
  - apply crtm_ev_call. exact H.
  - destruct (crtm_sup_add_m R R' (Some u) i p q H) as [A1 _].
    unfold EV_SUP_ADD, EV_DESCRIPTORS_ADD.
    rewrite (crtm_spill_frees R R' H), (crtm_spill_frees _ _ A1). reflexivity.
  - reflexivity.
  - generalize (crtm_pins_clear_m R R' (Some u) H).
    destruct (pins_clear_m R (Some u)) as [R1 r]. destruct (pins_clear_m R' (Some u)) as [R1' r'].
    intros [A1 A2]. cbn [fst snd] in A1, A2 |- *. subst r'.
    unfold EV_PINS_CLEAR, EV_LV2_REFUSALS_FORGET.
    rewrite (crtm_spill_frees R R' H), (crtm_spill_frees R1 R1' A1). reflexivity.
  - reflexivity.
  - destruct (crtm_sup_broadcast_m R R' ln H) as [A1 _].
    unfold EV_SUP_BROADCAST, EV_SUP_HOST_SETTING.
    rewrite (crtm_spill_frees R R' H), (crtm_spill_frees _ _ A1). reflexivity.
Qed.

Lemma crtm_ev_psw : forall R R' ln args, crtm_eq R R' -> EV_PIN_SET_WORDS R' ln args = EV_PIN_SET_WORDS R ln args.
Proof.
  intros R R' ln args H. unfold EV_PIN_SET_WORDS.
  destruct (Verbs.pin_set_words_m ln args) as [k|c|u i p q|u f l v|u| |ln' tk];
    [reflexivity | reflexivity | reflexivity | | reflexivity | reflexivity | reflexivity].
  generalize (crtm_pins_set_m R R' (Some u) (Some f) (Some l) v H).
  destruct (pins_set_m R (Some u) (Some f) (Some l) v) as [R1 r].
  destruct (pins_set_m R' (Some u) (Some f) (Some l) v) as [R1' r'].
  intros [A1 A2]. cbn [fst snd] in A1, A2 |- *. subst r'.
  unfold EV_PINS_SET, EV_LV2_REFUSALS_FORGET.
  rewrite (crtm_spill_frees R R' H), (crtm_spill_frees R1 R1' A1). reflexivity.
Qed.

Lemma crtm_ev_route : forall R R' ln tk s, crtm_eq R R' -> ev_route R' ln tk s = ev_route R ln tk s.
Proof.
  intros R R' ln tk s H. unfold ev_route. destruct tk as [|v args]; [reflexivity|].
  destruct (Verbs.list_eqb v Verbs.Lit.verb_chain).
  { unfold EV_CHAIN_WORDS, EV_SUP_CHAIN. rewrite (crtm_spill_frees R R' H). reflexivity. }
  destruct (Verbs.list_eqb v Verbs.Lit.verb_pin_set).
  { rewrite (crtm_ev_psw R R' ln args H). reflexivity. }
  apply crtm_ev_step. exact H.
Qed.

Lemma crtm_ev_after_ss : forall R R' y af, crtm_eq R R' ->
  ev_after (fst (socket_send_m R' y)) af = ev_after (fst (socket_send_m R y)) af.
Proof.
  intros R R' y af H. destruct af as [a|]; cbn [ev_after]; [|reflexivity].
  unfold EV_SUP_AFTER_REPLY. rewrite (crtm_spill_frees _ _ (proj1 (crtm_socket_send_m R R' y H))). reflexivity.
Qed.

Lemma crtm_ev_vr : forall R R' D, crtm_eq R R' -> ev_vr R' D = ev_vr R D.
Proof.
  intros R R' D H. unfold ev_vr.
  match goal with |- context [Verbs.receive ?a D] => destruct (Verbs.receive a D) as [st af] end.
  cbv beta iota.
  match goal with |- context [VerbsRun.run_step ?c R st] =>
    generalize (crtm_step c R R' st H);
    destruct (VerbsRun.run_step c R st) as [[R1 x] q];
    destruct (VerbsRun.run_step c R' st) as [[R1' x'] q'] end.
  cbn [fst snd]. intros (A1 & A2 & A3). subst x' q'.
  rewrite (crtm_ev_route R R' _ _ st H), (crtm_ev_after_ss R1 R1' _ af A1). reflexivity.
Qed.

Lemma crt_ev_vr_sh : forall R s h D, ev_vr (set_host (set_state R s) h) D = ev_vr R D.
Proof. intros R s h D. apply crtm_ev_vr. apply crtm_eq_sh. Qed.

Lemma crt_ev_send_sh : forall R s h D, EV_SEND_MESSAGE (set_host (set_state R s) h) D = EV_SEND_MESSAGE R D.
Proof.
  intros R s h D. unfold EV_SEND_MESSAGE.
  change (RecModel.rec_clear (set_host (set_state R s) h)) with (set_host (set_state (RecModel.rec_clear R) s) h).
  rewrite crt_ev_vr_sh.
  change (EV_REC_CLEAR (set_host (set_state R s) h)) with (EV_REC_CLEAR R).
  reflexivity.
Qed.

Lemma crt_xm_send_sh : forall MT R s h D, XM_SEND_MESSAGE MT (set_host (set_state R s) h) D = XM_SEND_MESSAGE MT R D.
Proof.
  intros MT R s h D. unfold XM_SEND_MESSAGE, XM_VERBS_RECEIVE.
  change (RecModel.rec_clear (set_host (set_state R s) h)) with (set_host (set_state (RecModel.rec_clear R) s) h).
  rewrite crt_ev_vr_sh.
  change (XM_REC_CLEAR MT (set_host (set_state R s) h)) with (XM_REC_CLEAR MT R).
  reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* (M2) refuse, code and spill survive run_receive for any atoi and reply-code function: lib/Prog/CrtVr.v's
   vr_run_rc / vr_run_spill (there over the plain vr_run) assembled over VerbsRun.run_receive from CrtVr's rc_step /
   sp_step, which are already generic in the reply-code function. *)
Lemma crt_rr_rc : forall atoi rcode (R : rstate) (D : list byte),
  r_refuse (fst (fst (VerbsRun.run_receive atoi rcode R D))) = r_refuse R /\
  r_code (fst (fst (VerbsRun.run_receive atoi rcode R D))) = r_code R.
Proof.
  intros atoi rcode R D. change (rc_keep R (fst (fst (VerbsRun.run_receive atoi rcode R D)))).
  unfold VerbsRun.run_receive.
  destruct (Verbs.receive atoi D) as [st af]. cbv beta iota.
  destruct (VerbsRun.run_step rcode R st) as [[R1 x] q] eqn:E.
  cbn [fst].
  destruct af as [[i v]|]; cbn [fst]; [apply rc_sup_after_reply_m|]; apply rc_socket_send_m;
    rc_pair E; apply rc_step; apply rc_refl.
Qed.

Lemma crt_rr_spill : forall atoi rcode (R : rstate) (D : list byte), (length (r_calls R) <= 12)%nat ->
  r_spill (fst (fst (VerbsRun.run_receive atoi rcode R D))) = r_spill R.
Proof.
  intros atoi rcode R D Hl.
  assert (H : sp_keep R (fst (fst (VerbsRun.run_receive atoi rcode R D))) (S (S (S (length (r_calls R)))))).
  { unfold VerbsRun.run_receive.
    destruct (Verbs.receive atoi D) as [st af]. cbv beta iota.
    destruct (VerbsRun.run_step rcode R st) as [[R1 x] q] eqn:E.
    cbn [fst].
    assert (H1 : sp_keep R R1 (S (S (length (r_calls R))))) by (rc_pair E; apply sp_step; [apply sp_refl | lia]).
    destruct af as [[i v]|]; cbn [fst].
    - apply sp_sup_after_reply_m; [apply sp_socket_send_m; exact H1 | lia].
    - eapply sp_weak; [apply sp_socket_send_m; exact H1 | lia]. }
  exact (proj1 H).
Qed.

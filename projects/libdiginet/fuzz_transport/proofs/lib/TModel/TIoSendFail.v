(* The harness's io_send (fuzz/fuzz_transport.c:823-899, TCb.v io_send_m) leaves g_fail_next at 0. It clears the
   byte first (:829) and nothing after that writes it: every later write of io_send_m and of the checks it calls
   lands in M, GOT, g_cmd, g_q, g_last_counter or g_nq (TWorld.v:26-43), and the byte of g_fail_next (TWorld.v:30,
   :477) is in none of them. The checks other than check_latest_sent return their world unchanged; check_latest_sent
   marks commands SENT in g_cmd and q_remove rewrites g_q below g_nq (indices < CMDS_MAX) and g_nq. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TSess0 TCb.
Import ListNotations.
Open Scope Z_scope.

(* a world of the right length whose g_fail_next byte is 0 *)
Definition isf_fn0 (X : list byte) : Prop := length X = Z.to_nat W_LEN /\ g_fail_next X = 0.

Lemma isf_upd : forall X k v, isf_fn0 X -> 0 <= k -> k + Z.of_nat (length v) <= W_LEN ->
  k + Z.of_nat (length v) <= OFF_g_fail_next \/ OFF_g_fail_next + 1 <= k -> isf_fn0 (upd X k v).
Proof.
  intros X k v [HL HF] Hk Hl Hd. unfold isf_fn0, g_fail_next in *.
  assert (HL' : k + Z.of_nat (length v) <= Z.of_nat (length X)) by (rewrite HL; unfold W_LEN in *; lia).
  split.
  - rewrite length_upd by assumption. exact HL.
  - rewrite u_at_upd_out; [exact HF | exact Hk | unfold OFF_g_fail_next; lia | | exact HL'].
    change (Z.of_nat 1) with 1. lia.
Qed.

Lemma isf_put : forall X k n v, isf_fn0 X -> 0 <= k -> k + Z.of_nat n <= W_LEN ->
  k + Z.of_nat n <= OFF_g_fail_next \/ OFF_g_fail_next + 1 <= k -> isf_fn0 (upd X k (put n v)).
Proof. intros X k n v F Hk Hl Hd. apply isf_upd; rewrite ?length_put; assumption. Qed.

Lemma isf_clear : forall B, length B = Z.to_nat W_LEN -> isf_fn0 (set_g_fail_next B 0).
Proof.
  intros B HL. unfold isf_fn0, set_g_fail_next, g_fail_next.
  split.
  - rewrite length_upd_put; [exact HL | unfold OFF_g_fail_next; lia | rewrite HL; unfold OFF_g_fail_next, W_LEN; lia].
  - rewrite u_at_upd_put; [reflexivity | unfold OFF_g_fail_next; lia | rewrite HL; unfold OFF_g_fail_next, W_LEN; lia].
Qed.

Ltac isf_offs :=
  unfold A_M_fly_on, A_M_fly_cmd, A_M_fly_counter, A_M_fly_retries, A_M_fly_sent, A_M_fly_frame, A_M_fly_len,
    A_M_host_counter, A_M_next_ka, A_M_last_display, A_M_display_sent, A_GOT_acks, A_GOT_e2, A_GOT_e3,
    A_Cmd_st, OFF_M, OFF_GOT, OFF_g_cmd, OFF_g_q, OFF_g_last_counter, OFF_g_nq, OFF_g_fail_next, W_LEN,
    SPEC_MAX_FRAME, CMDS_MAX in *.

(* the length side goal of the write of M.fly.frame (:888-889): firstn of at most SPEC_MAX_FRAME bytes *)
Ltac isf_len :=
  rewrite ?length_firstn;
  repeat match goal with Hb : (_ <? _) = true |- _ => apply Z.ltb_lt in Hb end;
  isf_offs; lia.

(* a world built by TWorld setters on a world the context says isf_fn0 of *)
Ltac isf_tac :=
  unfold set_M_fly_on, set_M_fly_cmd, set_M_fly_counter, set_M_fly_retries, set_M_fly_sent, set_M_fly_frame,
    set_M_fly_len, set_M_host_counter, set_M_next_ka, set_M_last_display, set_M_display_sent, set_GOT_acks,
    set_GOT_e2, set_GOT_e3, set_g_last_counter;
  repeat first
    [ assumption
    | apply isf_put; [ | isf_offs; lia | isf_offs; lia | isf_offs; lia ]
    | apply isf_upd; [ | isf_offs; lia | isf_len | isf_len ] ].

(* ---- the checks that return their world unchanged ---- *)

Ltac isf_ck :=
  cbv zeta;
  repeat (match goal with |- context [if ?c then _ else _] => destruct c; cbv beta iota end);
  let H := fresh "H" in intros H; first [discriminate H | injection H as <- _; reflexivity].

Lemma isf_sent : forall X f Y u, check_sent_frame_m X f = Some (Y, u) -> Y = X.
Proof. intros X f Y u. unfold check_sent_frame_m. isf_ck. Qed.
Lemma isf_ack : forall X f Y u, check_ack_frame_m X f = Some (Y, u) -> Y = X.
Proof. intros X f Y u. unfold check_ack_frame_m. isf_ck. Qed.
Lemma isf_ctl : forall X f Y u, check_latest_control_m X f = Some (Y, u) -> Y = X.
Proof. intros X f Y u. unfold check_latest_control_m. isf_ck. Qed.
Lemma isf_retry : forall X f Y u, check_inflight_retry_m X f = Some (Y, u) -> Y = X.
Proof. intros X f Y u. unfold check_inflight_retry_m. isf_ck. Qed.
Lemma isf_wake : forall X Y u, check_state_wake_m X = Some (Y, u) -> Y = X.
Proof. intros X Y u. unfold check_state_wake_m. isf_ck. Qed.
Lemma isf_new : forall X Y u, check_inflight_new_m X = Some (Y, u) -> Y = X.
Proof. intros X Y u. unfold check_inflight_new_m. isf_ck. Qed.
Lemma isf_frame : forall X f c Y u, check_latest_frame_m X f c = Some (Y, u) -> Y = X.
Proof. intros X f c Y u. unfold check_latest_frame_m. isf_ck. Qed.
Lemma isf_ka : forall X Y u, check_keepalive_due_m X = Some (Y, u) -> Y = X.
Proof. intros X Y u. unfold check_keepalive_due_m. isf_ck. Qed.
Lemma isf_disp : forall X Y u, check_latest_display_m X = Some (Y, u) -> Y = X.
Proof. intros X Y u. unfold check_latest_display_m. isf_ck. Qed.

(* ---- check_latest_sent (:626-644) ---- *)

(* tagged_of answers an index of g_cmd below CMDS_MAX (:613-614) *)
Lemma isf_tagged : forall X b n Y s, tagged_of_m X b n = Some (Y, Some s) -> 0 <= s < CMDS_MAX.
Proof.
  intros X b n Y s. unfold tagged_of_m. cbv zeta.
  repeat (match goal with |- context [if ?c then _ else _] => let E := fresh "Ec" in destruct c eqn:E; cbv beta iota end);
    let H := fresh "H" in intros H; try discriminate H.
  injection H as _ <-.
  match goal with Ec : (CMDS_MAX <=? _) = false |- _ => apply Z.leb_gt in Ec end.
  split; [|assumption].
  apply Z.lor_nonneg. split; [|apply Z.shiftl_nonneg];
    unfold DgnSpec.at8, DgnSpec.bz;
    match goal with |- 0 <= bv_unsigned ?x => pose proof (bv_unsigned_in_range _ x); lia end.
Qed.

(* q_remove's loop (:619-623) writes g_q[k] with k <= i < CMDS_MAX *)
Lemma isf_q_loop : forall fuel X s nq i k Y k', isf_fn0 X -> 0 <= k <= i ->
  q_remove_loop fuel X s nq i k = Some (Y, k') -> isf_fn0 Y.
Proof.
  induction fuel as [|fuel IH]; intros X s nq i k Y k' FX Hk; cbn [q_remove_loop];
    [let H := fresh "H" in intros H; discriminate H|].
  destruct (Z.ltb_spec i nq) as [Hi|Hi]; cbv beta iota;
    [|let H := fresh "H" in intros H; injection H as <- _; exact FX].
  destruct (Z.leb_spec CMDS_MAX i) as [Hc|Hc]; cbv beta iota; [let H := fresh "H" in intros H; discriminate H|].
  destruct (Q_at X i =? s); cbv beta iota.
  - apply (IH X s nq (i + 1) k Y k' FX). lia.
  - apply (IH _ s nq (i + 1) (k + 1) Y k'); [|lia].
    unfold set_Q_at. apply isf_put; [exact FX | isf_offs; lia | isf_offs; lia | isf_offs; lia].
Qed.

Lemma isf_q_remove : forall X s Y u, isf_fn0 X -> q_remove_m X s = Some (Y, u) -> isf_fn0 Y.
Proof.
  intros X s Y u FX. unfold q_remove_m.
  match goal with |- match ?x with _ => _ end = _ -> _ => destruct x as [[X1 k]|] eqn:EL end; cbv beta iota;
    [|let H := fresh "H" in intros H; discriminate H].
  let H := fresh "H" in intros H; injection H as <- _.
  unfold set_g_nq. apply isf_put; [ | isf_offs; lia | isf_offs; lia | isf_offs; lia ].
  exact (isf_q_loop _ X s _ 0 0 X1 k FX ltac:(lia) EL).
Qed.

Lemma isf_ls_loop : forall fuel X body len pos disp Y d, isf_fn0 X ->
  latest_sent_loop fuel X body len pos disp = Some (Y, d) -> isf_fn0 Y.
Proof.
  induction fuel as [|fuel IH]; intros X body len pos disp Y d FX; cbn [latest_sent_loop];
    [let H := fresh "H" in intros H; discriminate H|].
  cbv zeta.
  destruct (pos <? len); cbv beta iota; [|let H := fresh "H" in intros H; injection H as <- _; exact FX].
  match goal with |- match ?x with _ => _ end = _ -> _ => destruct x as [[X0 t]|] eqn:ET end; cbv beta iota;
    [|let H := fresh "H" in intros H; discriminate H].
  destruct t as [s|]; cbv beta iota; [|let H := fresh "H" in intros H; discriminate H].
  pose proof (isf_tagged _ _ _ _ _ ET) as Hs.
  match goal with |- (if ?c then _ else _) = _ -> _ => destruct c end; cbv beta iota;
    [let H := fresh "H" in intros H; discriminate H|].
  match goal with |- match ?x with _ => _ end = _ -> _ => destruct x as [[X2 u2]|] eqn:EQ end; cbv beta iota;
    [|let H := fresh "H" in intros H; discriminate H].
  apply IH. apply (isf_q_remove (set_Cmd_st X s SENT) s X2 u2); [|exact EQ].
  unfold set_Cmd_st. apply isf_put; [exact FX | isf_offs; lia | isf_offs; lia | isf_offs; lia].
Qed.

Lemma isf_ls : forall X body len Y d, isf_fn0 X -> check_latest_sent_m X body len = Some (Y, d) -> isf_fn0 Y.
Proof. intros X body len Y d FX. unfold check_latest_sent_m. apply isf_ls_loop. exact FX. Qed.

(* ---- io_send ---- *)

(* the facts a call's answer E gives: the unchanged world of a check, or isf_fn0 of check_latest_sent's world *)
Ltac isf_fact E Y :=
  lazymatch type of E with
  | check_sent_frame_m _ _ = _ => apply isf_sent in E; subst Y
  | check_ack_frame_m _ _ = _ => apply isf_ack in E; subst Y
  | check_latest_control_m _ _ = _ => apply isf_ctl in E; subst Y
  | check_inflight_retry_m _ _ = _ => apply isf_retry in E; subst Y
  | check_state_wake_m _ = _ => apply isf_wake in E; subst Y
  | check_inflight_new_m _ = _ => apply isf_new in E; subst Y
  | check_latest_frame_m _ _ _ = _ => apply isf_frame in E; subst Y
  | check_keepalive_due_m _ = _ => apply isf_ka in E; subst Y
  | check_latest_display_m _ = _ => apply isf_disp in E; subst Y
  | check_latest_sent_m ?X _ _ = _ =>
      let F := fresh "F" in assert (F : isf_fn0 Y) by (eapply (isf_ls X); [isf_tac | exact E])
  | _ => idtac
  end.

Ltac isf_go :=
  cbv beta iota;
  first
    [ let H := fresh "H" in intros H; discriminate H
    | let H := fresh "H" in intros H; injection H as <- _; isf_tac
    | match goal with |- context [if ?c then _ else _] => let Ec := fresh "Ec" in destruct c eqn:Ec; isf_go end
    | let x := match goal with
               | |- context [match ?x with _ => _ end] =>
                   lazymatch x with context [match _ with _ => _ end] => fail | _ => x end
               end in
      let E := fresh "E" in
      lazymatch type of x with
      | option (prod _ _) =>
          let Y := fresh "Y" in let u := fresh "u" in
          destruct x as [[Y u]|] eqn:E; [isf_fact E Y|]; isf_go
      | _ => destruct x eqn:E; isf_go
      end
    | let H := fresh "H" in intros H;
      lazymatch type of H with _ = Some (?Y, _) => isf_fact H Y; isf_tac end ].

Lemma io_send_m_fail_next : forall I B frame B' r,
  io_send_m I B frame = Some (B', r) -> length B = Z.to_nat W_LEN -> g_fail_next B' = 0.
Proof.
  intros I B frame B' r H HL.
  pose proof (isf_clear B HL) as F0.
  unfold io_send_m in H. cbv zeta in H.
  remember (set_g_fail_next B 0) as B0 eqn:EB0. clear EB0.
  revert H.
  match goal with |- match ?x with _ => _ end = _ -> _ => destruct x as [[B1 u1]|] eqn:E1 end; cbv beta iota;
    [|let H := fresh "H" in intros H; discriminate H].
  apply isf_sent in E1. subst B1.
  match goal with |- match ?x with _ => _ end = _ -> _ => destruct x as [[B2 u2]|] eqn:E2 end; cbv beta iota;
    [|let H := fresh "H" in intros H; discriminate H].
  intros H. injection H as <- _.
  enough (FB : isf_fn0 B2) by exact (proj2 FB).
  revert E2. isf_go.
Qed.

(* io_send returns 0 or -EIO (:898) *)
Lemma io_send_m_ret : forall I B frame B' r, io_send_m I B frame = Some (B', r) -> r = 0 \/ r = - EIO.
Proof.
  intros I B frame B' r H. unfold io_send_m in H. cbv zeta in H. revert H.
  match goal with |- match ?x with _ => _ end = _ -> _ => destruct x as [[B1 u1]|] end; cbv beta iota;
    [|let H := fresh "H" in intros H; discriminate H].
  match goal with |- match ?x with _ => _ end = _ -> _ => destruct x as [[B2 u2]|] end; cbv beta iota;
    [|let H := fresh "H" in intros H; discriminate H].
  intros H. injection H as _ <-. destruct (truth (g_fail_next B)); [right | left]; reflexivity.
Qed.

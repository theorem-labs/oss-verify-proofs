(* What the harness's io_send (fuzz/fuzz_transport.c:823-899, TCb.v io_send_m) and the session's send_raw and
   send_control (transport/src/diginet_session.c:88-109, TSess.v send_raw_m, send_control_m) leave of the world: every
   byte outside tok_wr is the one they were given. tok_wr is M, g_cmd, g_q, g_fail_next, g_last_counter, g_nq,
   GOT.e2 .. GOT.acks (TWorld.v) and g_s.stats.tx_frames: io_send_m writes g_fail_next (:829), GOT.acks / GOT.e2 /
   GOT.e3 (:834, :849, :892), g_last_counter (:850, :868) and M (M.fly, M.host_counter, M.next_ka, M.display_sent,
   M.last_display); the checks it calls return their world unchanged (TIoSendFail.v isf_sent .. isf_disp) except
   check_latest_sent, which marks commands SENT in g_cmd and whose q_remove rewrites g_q below CMDS_MAX and g_nq;
   send_raw_m adds g_s.stats.tx_frames (:91-92). So g_s outside stats.tx_frames, OW, GOT.n, GOT.t[], GOT.desk,
   GOT.foreign, GOT.acked and GOT.ndata are kept: send_control_m_keeps names the fields the G-form walks of
   diginet_session_wake and on_data read after send_control (S_state, GOT.n, GOT.ndata, S_desk_counter,
   S_desk_counter_valid, OW). Build-independent. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import
  TWorld TWorldLemmas TImg TNeed TSess0 TCb TSess TIoSendFail.
Import ListNotations.
Open Scope Z_scope.

(* The world offsets io_send, send_raw and send_control may write. *)
Definition tok_wr (k : Z) : Prop :=
  (OFF_M <= k < OFF_M + SZ_M) \/
  (OFF_g_cmd <= k < OFF_g_q + SZ_g_q) \/
  (OFF_g_fail_next <= k < OFF_g_fail_next + 1) \/
  (OFF_g_last_counter <= k < OFF_g_nq + SZ_g_nq) \/
  (A_GOT_e2 <= k < A_GOT_acks + 4) \/
  (A_S_stats_tx_frames <= k < A_S_stats_tx_frames + 8).

(* X is a whole world whose bytes outside tok_wr are B0's. *)
Definition tok_keep (B0 X : list byte) : Prop :=
  length X = Z.to_nat W_LEN /\ forall i, ~ tok_wr (Z.of_nat i) -> nth_error X i = nth_error B0 i.

Lemma tok_refl : forall B, length B = Z.to_nat W_LEN -> tok_keep B B.
Proof. intros B HL. split; [exact HL | intros i _; reflexivity]. Qed.

(* A write inside the world and inside tok_wr keeps tok_keep. *)
Lemma tok_upd : forall B0 X k v, tok_keep B0 X -> 0 <= k -> k + Z.of_nat (length v) <= W_LEN ->
  (forall j, k <= j < k + Z.of_nat (length v) -> tok_wr j) -> tok_keep B0 (upd X k v).
Proof.
  intros B0 X k v [HL HK] Hk Hl Hw.
  assert (HZ : Z.of_nat (length X) = W_LEN) by (rewrite HL; apply Z2Nat.id; unfold W_LEN; lia).
  split.
  - rewrite length_upd; [exact HL | exact Hk | lia].
  - intros i Hi. rewrite ne_upd; [| exact Hk | lia].
    match goal with |- (if ?c then _ else _) = _ => destruct c eqn:E end.
    + exfalso. apply andb_prop in E as [E1 E2]. apply Nat.leb_le in E1. apply Nat.ltb_lt in E2.
      apply Hi. apply Hw. lia.
    + exact (HK i Hi).
Qed.

(* Equal lists from equal nth_error. *)
Lemma tok_list_ext : forall (l l' : list byte), (forall i, nth_error l i = nth_error l' i) -> l = l'.
Proof.
  induction l as [|x l IH]; intros [|y l'] H.
  - reflexivity.
  - specialize (H 0%nat). discriminate H.
  - specialize (H 0%nat). discriminate H.
  - pose proof (H 0%nat) as H0. cbn in H0. injection H0 as ->. f_equal. apply IH. intros i. exact (H (S i)).
Qed.

(* A read of n bytes at k that misses tok_wr reads B0's bytes. *)
Lemma tok_sub : forall B0 X k n, tok_keep B0 X -> 0 <= k ->
  (forall j, k <= j < k + Z.of_nat n -> ~ tok_wr j) -> sub X k n = sub B0 k n.
Proof.
  intros B0 X k n [_ HK] Hk Hn. apply tok_list_ext. intros i.
  rewrite !ne_sub by exact Hk. destruct (i <? n)%nat eqn:E; [|reflexivity].
  apply Nat.ltb_lt in E. apply HK. intros Hw. apply (Hn (k + Z.of_nat i)); [lia|].
  replace (k + Z.of_nat i) with (Z.of_nat (Z.to_nat k + i)) by lia. exact Hw.
Qed.

Lemma tok_trans : forall B0 X Y, tok_keep B0 X -> tok_keep X Y -> tok_keep B0 Y.
Proof.
  intros B0 X Y [_ H1] [HL H2]. split; [exact HL|]. intros i Hi. rewrite (H2 i Hi). exact (H1 i Hi).
Qed.

Lemma tok_u_at : forall B0 X k n, tok_keep B0 X -> 0 <= k ->
  (forall j, k <= j < k + Z.of_nat n -> ~ tok_wr j) -> u_at X k n = u_at B0 k n.
Proof. intros B0 X k n K Hk Hn. unfold u_at. rewrite (tok_sub B0 X k n K Hk Hn). reflexivity. Qed.

Lemma tok_s32 : forall B0 X k, tok_keep B0 X -> 0 <= k ->
  (forall j, k <= j < k + 4 -> ~ tok_wr j) -> s32_at X k = s32_at B0 k.
Proof.
  intros B0 X k K Hk Hn. unfold s32_at. rewrite (tok_u_at B0 X k 4 K Hk); [reflexivity|].
  intros j Hj. apply Hn. simpl in Hj. lia.
Qed.

Ltac tok_offs :=
  unfold tok_wr, A_M_fly_on, A_M_fly_cmd, A_M_fly_counter, A_M_fly_retries, A_M_fly_sent, A_M_fly_frame,
    A_M_fly_len, A_M_host_counter, A_M_next_ka, A_M_last_display, A_M_display_sent, A_GOT_acks, A_GOT_e2,
    A_GOT_e3, A_Cmd_st, A_S_stats_tx_frames, OFF_M, SZ_M, OFF_GOT, OFF_g_cmd, OFF_g_q, SZ_g_q, OFF_g_last_counter,
    OFF_g_nq, SZ_g_nq, OFF_g_fail_next, OFF_g_s, W_LEN, SPEC_MAX_FRAME, CMDS_MAX in *.

(* the arithmetic side goals of tok_upd: offsets are TWorld constants; the write of M.fly.frame (:888-889) is
   firstn of at most SPEC_MAX_FRAME bytes *)
Ltac tok_arith :=
  rewrite ?length_put, ?length_firstn in *;
  repeat match goal with Hb : (_ <? _) = true |- _ => apply Z.ltb_lt in Hb end;
  tok_offs; lia.

(* a world built by TWorld setters on a world the context says tok_keep of *)
Ltac tok_tac :=
  unfold set_M_fly_on, set_M_fly_cmd, set_M_fly_counter, set_M_fly_retries, set_M_fly_sent, set_M_fly_frame,
    set_M_fly_len, set_M_host_counter, set_M_next_ka, set_M_last_display, set_M_display_sent, set_GOT_acks,
    set_GOT_e2, set_GOT_e3, set_g_last_counter, set_g_fail_next, set_S_stats_tx_frames;
  repeat first
    [ assumption
    | apply tok_upd; [ | tok_arith | tok_arith | let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; tok_arith ] ].

(* ---- check_latest_sent (:626-644): g_cmd and, by q_remove, g_q and g_nq ---- *)

Lemma tok_q_loop : forall fuel B0 X s nq i k Y k', tok_keep B0 X -> 0 <= k <= i ->
  q_remove_loop fuel X s nq i k = Some (Y, k') -> tok_keep B0 Y.
Proof.
  induction fuel as [|fuel IH]; intros B0 X s nq i k Y k' FX Hk; cbn [q_remove_loop];
    [let H := fresh "H" in intros H; discriminate H|].
  destruct (Z.ltb_spec i nq) as [Hi|Hi]; cbv beta iota;
    [|let H := fresh "H" in intros H; injection H as <- _; exact FX].
  destruct (Z.leb_spec CMDS_MAX i) as [Hc|Hc]; cbv beta iota; [let H := fresh "H" in intros H; discriminate H|].
  destruct (Q_at X i =? s); cbv beta iota.
  - apply (IH B0 X s nq (i + 1) k Y k' FX). lia.
  - apply (IH B0 _ s nq (i + 1) (k + 1) Y k'); [|lia].
    unfold set_Q_at. apply tok_upd; [exact FX | tok_arith | tok_arith |].
    intros j Hj. tok_arith.
Qed.

Lemma tok_q_remove : forall B0 X s Y u, tok_keep B0 X -> q_remove_m X s = Some (Y, u) -> tok_keep B0 Y.
Proof.
  intros B0 X s Y u FX. unfold q_remove_m.
  match goal with |- match ?x with _ => _ end = _ -> _ => destruct x as [[X1 k]|] eqn:EL end; cbv beta iota;
    [|let H := fresh "H" in intros H; discriminate H].
  let H := fresh "H" in intros H; injection H as <- _.
  unfold set_g_nq. apply tok_upd; [ | tok_arith | tok_arith | intros j Hj; tok_arith ].
  exact (tok_q_loop _ B0 X s _ 0 0 X1 k FX ltac:(lia) EL).
Qed.

Lemma tok_ls_loop : forall fuel B0 X body len pos disp Y d, tok_keep B0 X ->
  latest_sent_loop fuel X body len pos disp = Some (Y, d) -> tok_keep B0 Y.
Proof.
  induction fuel as [|fuel IH]; intros B0 X body len pos disp Y d FX; cbn [latest_sent_loop];
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
  apply IH. apply (tok_q_remove B0 (set_Cmd_st X s SENT) s X2 u2); [|exact EQ].
  unfold set_Cmd_st. apply tok_upd; [exact FX | tok_arith | tok_arith | intros j Hj; tok_arith].
Qed.

Lemma tok_ls : forall B0 X body len Y d, tok_keep B0 X -> check_latest_sent_m X body len = Some (Y, d) ->
  tok_keep B0 Y.
Proof. intros B0 X body len Y d FX. unfold check_latest_sent_m. apply tok_ls_loop. exact FX. Qed.

(* ---- io_send ---- *)

(* the facts a call's answer E gives: the unchanged world of a check, or tok_keep of check_latest_sent's world *)
Ltac tok_fact E Y :=
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
      let F := fresh "F" in
      lazymatch goal with
      | _ : tok_keep ?B0 _ |- _ => assert (F : tok_keep B0 Y) by (eapply (tok_ls B0 X); [tok_tac | exact E])
      end
  | _ => idtac
  end.

Ltac tok_go :=
  cbv beta iota;
  first
    [ let H := fresh "H" in intros H; discriminate H
    | let H := fresh "H" in intros H; injection H as <- _; tok_tac
    | match goal with |- context [if ?c then _ else _] => let Ec := fresh "Ec" in destruct c eqn:Ec; tok_go end
    | let x := match goal with
               | |- context [match ?x with _ => _ end] =>
                   lazymatch x with context [match _ with _ => _ end] => fail | _ => x end
               end in
      let E := fresh "E" in
      lazymatch type of x with
      | option (prod _ _) =>
          let Y := fresh "Y" in let u := fresh "u" in
          destruct x as [[Y u]|] eqn:E; [tok_fact E Y|]; tok_go
      | _ => destruct x eqn:E; tok_go
      end
    | let H := fresh "H" in intros H;
      lazymatch type of H with _ = Some (?Y, _) => tok_fact H Y; tok_tac end ].

(* io_send writes only bytes of tok_wr *)
Lemma io_send_m_keep : forall I B frame B' r, length B = Z.to_nat W_LEN ->
  io_send_m I B frame = Some (B', r) -> tok_keep B B'.
Proof.
  intros I B frame B' r HL H.
  assert (F0 : tok_keep B (set_g_fail_next B 0)) by (pose proof (tok_refl B HL); tok_tac).
  unfold io_send_m in H. cbv zeta in H.
  remember (set_g_fail_next B 0) as B0 eqn:EB0. clear EB0.
  revert H.
  match goal with |- match ?x with _ => _ end = _ -> _ => destruct x as [[B1 u1]|] eqn:E1 end; cbv beta iota;
    [|let H := fresh "H" in intros H; discriminate H].
  apply isf_sent in E1. subst B1.
  match goal with |- match ?x with _ => _ end = _ -> _ => destruct x as [[B2 u2]|] eqn:E2 end; cbv beta iota;
    [|let H := fresh "H" in intros H; discriminate H].
  intros H. injection H as <- _.
  revert E2. tok_go.
Qed.

(* send_raw: io_send through s->io.send, then g_s.stats.tx_frames *)
Lemma send_raw_m_keep : forall I F B frame B' r, length B = Z.to_nat W_LEN ->
  send_raw_m I F B frame = Some (B', r) -> tok_keep B B'.
Proof.
  intros I F B frame B' r HL H. unfold send_raw_m, call_send in H.
  destruct (S_io_send B =? ti_io_send I); cbv beta iota in H; [|discriminate H].
  destruct (io_send_m I B frame) as [[B1 r1]|] eqn:E; cbv beta iota in H; [|discriminate H].
  pose proof (io_send_m_keep I B frame B1 r1 HL E) as K.
  destruct (r1 =? 0); cbv beta iota in H; injection H as <- _; [tok_tac | exact K].
Qed.

(* send_control: no write on the build's negative code, else send_raw's *)
Lemma send_control_m_keep : forall I F B cmd ack B' R, length B = Z.to_nat W_LEN ->
  send_control_m I F B cmd ack = Some (B', R) -> tok_keep B B'.
Proof.
  intros I F B cmd ack B' R HL H. unfold send_control_m in H. cbv zeta in H.
  match type of H with (if ?c then _ else _) = _ => destruct c end; cbv beta iota in H;
    [injection H as <- _; exact (tok_refl B HL)|].
  match type of H with match ?x with _ => _ end = _ => destruct x as [[B1 r]|] eqn:E end; cbv beta iota in H;
    [|discriminate H].
  injection H as <- _. exact (send_raw_m_keep I F B _ B1 r HL E).
Qed.

(* The fields the G-form walks read after send_control (diginet_session_wake: S_state and GOT.n; on_data: OW, GOT.ndata,
   S_desk_counter, S_desk_counter_valid): each lies outside tok_wr, so it is the one before the call. OW is the last
   global of the world (OFF_OW + SZ_OW = W_LEN), so every read from OFF_OW on is kept. *)
Lemma send_control_m_keeps : forall I F B cmd ack B' R, length B = Z.to_nat W_LEN ->
  send_control_m I F B cmd ack = Some (B', R) ->
  S_state B' = S_state B /\ GOT_n B' = GOT_n B /\ GOT_ndata B' = GOT_ndata B /\
  S_desk_counter B' = S_desk_counter B /\ S_desk_counter_valid B' = S_desk_counter_valid B /\
  (forall k n, OFF_OW <= k -> sub B' k n = sub B k n) /\
  (forall g, 0 <= g -> OW_dn_body B' g = OW_dn_body B g).
Proof.
  intros I F B cmd ack B' R HL H. pose proof (send_control_m_keep I F B cmd ack B' R HL H) as K.
  assert (KW : forall k n, OFF_OW <= k -> sub B' k n = sub B k n).
  { intros k n Hk. apply (tok_sub B B' k n K); [unfold OFF_OW in Hk; lia|]. intros j Hj Hw. tok_offs.
    unfold OFF_OW in Hk. lia. }
  split; [unfold S_state; apply (tok_s32 B B' _ K);
    [unfold A_S_state; tok_offs; lia | intros j Hj Hw; unfold A_S_state in Hj; tok_offs; lia]|].
  split; [unfold GOT_n; apply (tok_s32 B B' _ K);
    [unfold A_GOT_n; tok_offs; lia | intros j Hj Hw; unfold A_GOT_n in Hj; tok_offs; lia]|].
  split; [unfold GOT_ndata; apply (tok_s32 B B' _ K);
    [unfold A_GOT_ndata; tok_offs; lia | intros j Hj Hw; unfold A_GOT_ndata in Hj; tok_offs; lia]|].
  split; [unfold S_desk_counter; apply (tok_u_at B B' _ _ K);
    [unfold A_S_desk_counter; tok_offs; lia
    | intros j Hj Hw; unfold A_S_desk_counter in Hj; simpl Z.of_nat in Hj; tok_offs; lia]|].
  split; [unfold S_desk_counter_valid; apply (tok_s32 B B' _ K);
    [unfold A_S_desk_counter_valid; tok_offs; lia
    | intros j Hj Hw; unfold A_S_desk_counter_valid in Hj; tok_offs; lia]|].
  split; [exact KW|].
  intros g Hg. unfold OW_dn_body, u_at.
  rewrite (KW (A_OW_dn_body g) 8%nat ltac:(unfold A_OW_dn_body; lia)). reflexivity.
Qed.

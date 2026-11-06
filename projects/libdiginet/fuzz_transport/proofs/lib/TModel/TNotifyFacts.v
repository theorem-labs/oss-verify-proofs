(* Model facts the machine walks of the session functions that call s->notify need beyond their callee
   contracts: a STATE or ACKED notice (fuzz_transport.c:941-953) writes GOT only, so it leaves the one-byte
   g_fail_next as it was; and reads / writes of a world of W_LEN bytes. Build-independent. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TSess0 TCb.
Import ListNotations.
Open Scope Z_scope.

(* a write inside the world at or above GOT (which lies above g_fail_next) keeps g_fail_next and the length *)
Lemma gfn_upd : forall (B v : list byte) k, length B = Z.to_nat W_LEN ->
  OFF_GOT <= k -> k + Z.of_nat (length v) <= W_LEN ->
  g_fail_next (upd B k v) = g_fail_next B /\ length (upd B k v) = Z.to_nat W_LEN.
Proof.
  intros B v k L Hk Hl. unfold W_LEN, OFF_GOT in *. split.
  - unfold g_fail_next. apply u_at_upd_out; unfold OFF_g_fail_next; cbn; lia.
  - rewrite length_upd; [exact L | lia | lia].
Qed.

(* ---- reads and writes of a world of W_LEN bytes, for the walks ---- *)

Lemma len_upd_W : forall (B v : list byte) k, length B = Z.to_nat W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= W_LEN -> length (upd B k v) = Z.to_nat W_LEN.
Proof. intros B v k L Hk Hl. rewrite length_upd; [exact L | exact Hk | rewrite L; unfold W_LEN in *; lia]. Qed.

Lemma rd_upd_W : forall (B v : list byte) k k' n, length B = Z.to_nat W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= W_LEN -> 0 <= k' -> (k' + Z.of_nat n <= k \/ k + Z.of_nat (length v) <= k') ->
  u_at (upd B k v) k' n = u_at B k' n.
Proof. intros. apply u_at_upd_out; try assumption. rewrite H. unfold W_LEN in *. lia. Qed.

Lemma rd32_upd_W : forall (B v : list byte) k k', length B = Z.to_nat W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= W_LEN -> 0 <= k' -> (k' + 4 <= k \/ k + Z.of_nat (length v) <= k') ->
  s32_at (upd B k v) k' = s32_at B k'.
Proof. intros. apply s32_at_upd_out; try assumption. rewrite H. unfold W_LEN in *. lia. Qed.

Lemma upd_comm_W : forall (B v w : list byte) k k', length B = Z.to_nat W_LEN -> 0 <= k -> 0 <= k' ->
  k + Z.of_nat (length v) <= W_LEN -> k' + Z.of_nat (length w) <= W_LEN ->
  (k' + Z.of_nat (length w) <= k \/ k + Z.of_nat (length v) <= k') ->
  upd (upd B k v) k' w = upd (upd B k' w) k v.
Proof. intros. apply upd_upd_comm; try assumption; rewrite H; unfold W_LEN in *; lia. Qed.

(* side goals of the lemmas above: a closed numeric comparison (offsets are TWorld constants), or the length of
   a world built by upd from one of W_LEN bytes. vm_compute only ever sees a closed Z or nat comparison. *)
Ltac wnum := rewrite ?length_put;
  first [ lia | (vm_compute; congruence) | (vm_compute; reflexivity)
        | (vm_compute; first [ left; congruence | right; congruence ]) ].
Ltac wlen := first [ assumption | (apply len_upd_W; [ wlen | wnum | wnum ]) ].
Ltac wside := first [ wlen | wnum ].

Lemma notice_state_acked_fail_next : forall I F B n B',
  (n_kind n = N_STATE \/ n_kind n = N_ACKED) -> length B = Z.to_nat W_LEN ->
  notice_m I F B n = Some (B', tt) -> g_fail_next B' = g_fail_next B.
Proof.
  intros I F B n B' K L H.
  unfold notice_m in H. destruct K as [K | K]; rewrite K in H; cbn [Z.eqb N_STATE N_ACKED Pos.eqb] in H.
  - set (g := GOT_n B) in H.
    unfold set_GOT_n, set_GOT_t_reason, set_GOT_t_old, set_GOT_t_state in H.
    destruct (g <? TRANS_MAX) eqn:E1.
    + destruct (g <? 0) eqn:E2; [discriminate H |].
      apply Z.ltb_lt in E1. apply Z.ltb_ge in E2. unfold TRANS_MAX in E1.
      destruct (int_inc g) as [g1 |]; [| discriminate H].
      edestruct (gfn_upd B (put 4 (n_state n)) (A_GOT_t_state g)) as [G1 L1];
        [ exact L | unfold A_GOT_t_state; lia | rewrite length_put; unfold A_GOT_t_state, OFF_GOT, W_LEN; lia |].
      edestruct (gfn_upd _ (put 4 (n_old n)) (A_GOT_t_old g) L1) as [G2 L2];
        [ unfold A_GOT_t_old; lia | rewrite length_put; unfold A_GOT_t_old, OFF_GOT, W_LEN; lia |].
      edestruct (gfn_upd _ (put 4 (n_reason n)) (A_GOT_t_reason g) L2) as [G3 L3];
        [ unfold A_GOT_t_reason; lia | rewrite length_put; unfold A_GOT_t_reason, OFF_GOT, W_LEN; lia |].
      edestruct (gfn_upd _ (put 4 g1) A_GOT_n L3) as [G4 L4];
        [ unfold A_GOT_n; lia | rewrite length_put; unfold A_GOT_n, OFF_GOT, W_LEN; lia |].
      destruct (n_state n =? S_ONLINE).
      * unfold check_state_online_m in H.
        match type of H with (if ?c then _ else _) = _ => destruct c end; [discriminate H |].
        injection H as <-.
        etransitivity; [exact G4 |]. etransitivity; [exact G3 |]. etransitivity; [exact G2 |]. exact G1.
      * injection H as <-.
        etransitivity; [exact G4 |]. etransitivity; [exact G3 |]. etransitivity; [exact G2 |]. exact G1.
    + destruct (int_inc g) as [g1 |]; [| discriminate H].
      edestruct (gfn_upd B (put 4 g1) A_GOT_n L) as [G4 L4];
        [ unfold A_GOT_n; lia | rewrite length_put; unfold A_GOT_n, OFF_GOT, W_LEN; lia |].
      destruct (n_state n =? S_ONLINE).
      * unfold check_state_online_m in H.
        match type of H with (if ?c then _ else _) = _ => destruct c end; [discriminate H |].
        injection H as <-. exact G4.
      * injection H as <-. exact G4.
  - unfold set_GOT_acked in H.
    destruct (int_inc (GOT_acked B)) as [a |]; [| discriminate H].
    unfold check_inflight_acked_m in H.
    match type of H with (if ?c then _ else _) = _ => destruct c end; [discriminate H |].
    injection H as <-.
    edestruct (gfn_upd B (put 4 a) A_GOT_acked L) as [G1 L1];
      [ unfold A_GOT_acked; lia | rewrite length_put; unfold A_GOT_acked, OFF_GOT, W_LEN; lia |].
    exact G1.
Qed.

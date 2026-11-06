(* Model facts the walk of io_send (lib/Prog/T/io_send.v) uses: reads of a concatenation (u_at_app_l / _r), one
   more byte of a checksum span (sum_bytes_sub_succ), and that q_remove_m and check_latest_sent_m (TCb.v) keep the
   world's length and every byte below OFF_g_cmd (q_remove_keep, cls_keep): they write only g_cmd[s].st, g_q[k]
   and g_nq, all at or above OFF_g_cmd. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TSess0 TCb.
Import ListNotations.
Open Scope Z_scope.

(* ---- reads of a concatenation ---- *)

Lemma u_at_app_l : forall (x y : list byte) (k : Z) (n : nat), 0 <= k -> k + Z.of_nat n <= Z.of_nat (length x) ->
  u_at (x ++ y) k n = u_at x k n.
Proof.
  intros x y k n Hk Hn. unfold u_at, sub. f_equal.
  rewrite skipn_app, firstn_app, length_skipn.
  replace (n - (length x - Z.to_nat k))%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r. reflexivity.
Qed.

Lemma u_at_app_r : forall (x y : list byte) (k : Z) (n : nat), Z.of_nat (length x) <= k ->
  u_at (x ++ y) k n = u_at y (k - Z.of_nat (length x)) n.
Proof.
  intros x y k n Hk. unfold u_at, sub. f_equal.
  rewrite skipn_app.
  assert (E : skipn (Z.to_nat k) x = []) by (apply skipn_all2; lia).
  rewrite E, app_nil_l.
  replace (Z.to_nat (k - Z.of_nat (length x))) with (Z.to_nat k - length x)%nat by lia.
  reflexivity.
Qed.

(* ---- one more byte of a summed span ---- *)

Lemma sum_bytes_sub_succ : forall (l : list byte) (k : Z) (j : nat),
  0 <= k -> k + Z.of_nat (S j) <= Z.of_nat (length l) ->
  sum_bytes (sub l k (S j)) = sum_bytes (sub l k j) + at8 l (Z.to_nat k + j).
Proof.
  intros l k j Hk Hj. unfold sub.
  rewrite sum_bytes_firstn_S by (rewrite length_skipn; lia).
  rewrite at8_skipn. reflexivity.
Qed.

(* ---- writes at or above OFF_g_cmd keep the low part of the world ---- *)

(* B' has B's length and B's bytes below OFF_g_cmd. *)
Definition iok_keep (B B' : list byte) : Prop :=
  length B' = length B /\
  (forall (k : Z) (n : nat), 0 <= k -> k + Z.of_nat n <= OFF_g_cmd -> sub B' k n = sub B k n).

Lemma iok_refl : forall B, iok_keep B B.
Proof. intros B. split; [reflexivity | intros; reflexivity]. Qed.

Lemma iok_trans : forall B1 B2 B3, iok_keep B1 B2 -> iok_keep B2 B3 -> iok_keep B1 B3.
Proof.
  unfold iok_keep. intros B1 B2 B3 [L1 S1] [L2 S2]. split; [congruence|].
  intros k n Hk Hn. rewrite S2, S1 by assumption. reflexivity.
Qed.

Lemma iok_upd_hi : forall (B v : list byte) (off : Z), OFF_g_cmd <= off ->
  off + Z.of_nat (length v) <= Z.of_nat (length B) -> iok_keep B (upd B off v).
Proof.
  intros B v off Hoff Hl. assert (H0 : 0 <= off) by (unfold OFF_g_cmd in Hoff; lia).
  split; [apply length_upd; lia|].
  intros k n Hk Hn. apply sub_upd_out; [lia | lia | left; lia | lia].
Qed.

Lemma iok_lenZ : forall B : list byte, length B = Z.to_nat W_LEN -> Z.of_nat (length B) = 65616.
Proof. intros B H. rewrite H, Z2Nat.id; [reflexivity | unfold W_LEN; lia]. Qed.

(* The loop of q_remove: the next free place k stays at or below i < CMDS_MAX, so g_q[k] lies in g_q. *)
Lemma iok_q_remove_loop : forall fuel B serial nq i k B1 k1,
  q_remove_loop fuel B serial nq i k = Some (B1, k1) -> 0 <= k <= i -> length B = Z.to_nat W_LEN ->
  iok_keep B B1.
Proof.
  induction fuel as [|fuel IH]; intros B serial nq i k B1 k1 H Hki HL; cbn [q_remove_loop] in H;
    [discriminate|].
  destruct (i <? nq); [|injection H; intros; subst; apply iok_refl].
  destruct (CMDS_MAX <=? i) eqn:Ec; [discriminate|].
  apply Z.leb_gt in Ec. unfold CMDS_MAX in Ec.
  destruct (Q_at B i =? serial).
  - eapply IH; [exact H | lia | exact HL].
  - assert (K : iok_keep B (set_Q_at B k (Q_at B i))).
    { unfold set_Q_at. apply iok_upd_hi; rewrite ?length_put, ?(iok_lenZ _ HL); unfold OFF_g_q, OFF_g_cmd; lia. }
    apply (iok_trans _ _ _ K). eapply IH; [exact H | lia |].
    destruct K as [K' _]. rewrite K'. exact HL.
Qed.

Lemma iok_q_remove : forall B s B2, q_remove_m B s = Some (B2, tt) -> length B = Z.to_nat W_LEN -> iok_keep B B2.
Proof.
  intros B s B2 H HL. unfold q_remove_m in H.
  destruct (q_remove_loop (S (Z.to_nat CMDS_MAX)) B s (g_nq B) 0 0) as [[B1 k1]|] eqn:E;
    cbv beta iota in H; [|discriminate].
  injection H; intros; subst.
  pose proof (iok_q_remove_loop _ _ _ _ _ _ _ _ E ltac:(lia) HL) as K.
  apply (iok_trans _ _ _ K). unfold set_g_nq. apply iok_upd_hi.
  - unfold OFF_g_nq, OFF_g_cmd; lia.
  - rewrite length_put. destruct K as [K' _]. rewrite K', (iok_lenZ _ HL). unfold OFF_g_nq. lia.
Qed.

(* tagged_of answers Some s only for 0 <= s < CMDS_MAX. *)
Lemma iok_tagged_of_range : forall B b n B0 s, tagged_of_m B b n = Some (B0, Some s) -> 0 <= s < CMDS_MAX.
Proof.
  intros B b n B0 s H. unfold tagged_of_m in H. cbv zeta in H.
  repeat match type of H with
  | (if ?c then _ else _) = _ => destruct c eqn:?; cbv beta iota in H; try discriminate H
  end.
  injection H; intros; subst.
  match goal with E : (CMDS_MAX <=? _) = false |- _ => apply Z.leb_gt in E end.
  split; [|lia].
  pose proof (at8_range b 1). pose proof (at8_range b 2).
  apply Z.lor_nonneg. split; [lia|]. apply Z.shiftl_nonneg. lia.
Qed.

(* The loop of check_latest_sent: each round writes g_cmd[s].st (s < CMDS_MAX) and runs q_remove. *)
Lemma iok_latest_sent_loop : forall fuel B body len pos disp B' disp',
  latest_sent_loop fuel B body len pos disp = Some (B', disp') -> length B = Z.to_nat W_LEN -> iok_keep B B'.
Proof.
  induction fuel as [|fuel IH]; intros B body len pos disp B' disp' H HL; cbn [latest_sent_loop] in H;
    [discriminate|].
  cbv zeta in H.
  destruct (pos <? len); [|injection H; intros; subst; apply iok_refl].
  destruct (tagged_of_m B (skipn (Z.to_nat pos) body) (len - pos)) as [[B0 [s|]]|] eqn:Et;
    cbv beta iota in H; [|discriminate|discriminate].
  pose proof (iok_tagged_of_range _ _ _ _ _ Et) as Hs. unfold CMDS_MAX in Hs.
  match type of H with
  | (if ?c then _ else _) = _ => destruct c; cbv beta iota in H; [discriminate|]
  end.
  destruct (q_remove_m (set_Cmd_st B s SENT) s) as [[B2 []]|] eqn:Eq; cbv beta iota in H; [|discriminate].
  assert (K1 : iok_keep B (set_Cmd_st B s SENT)).
  { unfold set_Cmd_st, A_Cmd_st. apply iok_upd_hi; rewrite ?length_put, ?(iok_lenZ _ HL); unfold OFF_g_cmd; lia. }
  assert (L1 : length (set_Cmd_st B s SENT) = Z.to_nat W_LEN) by (destruct K1 as [L _]; rewrite L; exact HL).
  pose proof (iok_q_remove _ _ _ Eq L1) as K2.
  apply (iok_trans _ _ _ K1). apply (iok_trans _ _ _ K2).
  eapply IH; [exact H|]. destruct K2 as [L2 _]. rewrite L2. exact L1.
Qed.

(* ---- the lemmas the walk applies ---- *)

Lemma q_remove_keep : forall (B : list byte) (s : Z) (B2 : list byte),
  q_remove_m B s = Some (B2, tt) -> length B = Z.to_nat W_LEN ->
  length B2 = length B /\ (forall (k : Z) (n : nat), 0 <= k -> k + Z.of_nat n <= OFF_g_cmd -> sub B2 k n = sub B k n).
Proof. intros B s B2 H HL. exact (iok_q_remove B s B2 H HL). Qed.

Lemma cls_keep : forall (B body : list byte) (len : Z) (B' : list byte) (disp : Z),
  check_latest_sent_m B body len = Some (B', disp) -> length B = Z.to_nat W_LEN ->
  length B' = length B /\ (forall (k : Z) (n : nat), 0 <= k -> k + Z.of_nat n <= OFF_g_cmd -> sub B' k n = sub B k n).
Proof.
  intros B body len B' disp H HL. unfold check_latest_sent_m in H.
  exact (iok_latest_sent_loop _ _ _ _ _ _ _ _ H HL).
Qed.

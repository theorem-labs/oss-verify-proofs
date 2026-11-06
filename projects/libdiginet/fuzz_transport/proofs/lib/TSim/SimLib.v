(* The world B (TWorld.v) is the .bss region as a byte list: every getter reads it with sub / u_at / s32_at at a
   literal offset, every setter writes it with upd (put n v). This file is the algebra the simulation proofs
   (reception, tick, submit, wake and close) share, on top of TModel/TWorldLemmas.v:
   - the base lemmas TWorldLemmas lacks (w_sub_upd_cover, w_s32_put) and the frames wframe;
   - reads through writes (the wr_ lemmas): a read the write misses, the read of the value written, a read
     inside a zeroed range, a read inside a written list; each needs only 0 <= k <= length B of the write;
   - the A2 consequences of agree_cfg (Agree.v): s->cfg is the copy of g_cfg;
   - the tactics wrange, wsimp, wlen; frames over range lists (wsame, wsame_tac, wsame_rw);
   - the frame transfer of agree: the footprints foot_core / foot_q, agree_core_frame, agree_q_frame,
     agree_frame, the monotony in ops, and the named facts of op_begin and op 7 (g_fail_next = 1).
   SAFETY. Two reads of one world at different offsets are equal only by unfolding both to
   skipn (Z.to_nat offset) B, and the unifier then builds unary numbers of up to 65616 (one build died at
   209 GB). No proof or tactic here lets the unifier compare two reads: equations are rewritten as fully
   applied instances found by syntactic matching (`pattern` + eq_ind_r), goals are closed by exact terms or
   by Ltac's syntactic matching (never a metavariable shared by a hypothesis pattern and the conclusion, which
   Ltac compares by conversion), vm_compute runs only on closed goals with no world in them, and offsets are
   decided by lia on the unfolded numbers. Unsafe on a goal with reads: `reflexivity`, `assumption`,
   `congruence`, `auto`, `f_equal`, `contradiction`, `rewrite !H`, `rewrite ?H`, `repeat rewrite H`,
   `rewrite H` when the left side of H is not syntactically in the goal, and `match goal with H : ?P |- ?P`. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import
  TWorld TWorldLemmas TImg TNeed TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------- base algebra (QueueFacts.v's names)
   QueueFacts.v lemmas that TWorldLemmas.v already states are not repeated here:
   w_nth_error_sub = ne_sub, w_nth_error_upd = ne_upd, w_length_upd = length_upd, w_length_sub = length_sub,
   w_length_put = length_put, w_sub_upd_disj = sub_upd_out, w_sub_upd_in = sub_upd_d (or wr_sub_upd_in below),
   w_sub_all = sub_all, w_sub_upd_same = sub_upd_eq, w_sub_sub = sub_sub, w_bytes_put = bytes_le_to_Z_put. *)

(* reading from the start of the range written, on past its end *)
Lemma w_sub_upd_cover : forall B k v n, 0 <= k -> (length v <= n)%nat -> (Z.to_nat k + n <= length B)%nat ->
  sub (upd B k v) k n = v ++ sub B (k + Z.of_nat (length v)) (n - length v).
Proof.
  intros B k v n Hk Hn Hl. apply nth_error_ext. intros t.
  rewrite ne_sub by exact Hk. destruct (Nat.ltb_spec t (length v)) as [Ht|Ht].
  - rewrite nth_error_app1 by exact Ht. destruct (Nat.ltb_spec t n); [|lia].
    rewrite ne_upd by (try assumption; lia).
    destruct (Nat.leb_spec (Z.to_nat k) (Z.to_nat k + t)); [|lia]. cbn [andb].
    destruct (Nat.ltb_spec (Z.to_nat k + t) (Z.to_nat k + length v)); [|lia]. f_equal. lia.
  - rewrite nth_error_app2 by exact Ht. rewrite ne_sub by lia.
    destruct (Nat.ltb_spec t n); destruct (Nat.ltb_spec (t - length v) (n - length v)); try lia;
      [|reflexivity].
    rewrite ne_upd by (try assumption; lia).
    destruct (Nat.leb_spec (Z.to_nat k) (Z.to_nat k + t)); [|lia]. cbn [andb].
    destruct (Nat.ltb_spec (Z.to_nat k + t) (Z.to_nat k + length v)); [lia|]. f_equal. lia.
Qed.

Lemma w_s32_put : forall v, - 2 ^ 31 <= v < 2 ^ 31 -> bv_swrap 32 (bytes_le_to_Z (put 4 v)) = v.
Proof.
  intros v Hv. rewrite bytes_le_to_Z_put. change (8 * Z.of_nat 4) with 32.
  change (v mod 2 ^ 32) with (bv_wrap 32 v). rewrite bv_swrap_wrap. apply bv_swrap_small.
  unfold bv_half_modulus, bv_modulus. cbn. lia.
Qed.

(* ---------------------------------------------------------------- frames: B' is B outside the addresses R names *)

Definition wframe (R : Z -> Prop) (B B' : list byte) : Prop :=
  length B' = length B /\ forall a : nat, ~ R (Z.of_nat a) -> nth_error B' a = nth_error B a.

Lemma wframe_refl : forall R B, wframe R B B.
Proof. intros R B. split; [reflexivity|]. intros; reflexivity. Qed.

Lemma wframe_trans : forall R B1 B2 B3, wframe R B1 B2 -> wframe R B2 B3 -> wframe R B1 B3.
Proof.
  intros R B1 B2 B3 [L1 H1] [L2 H2]. split; [congruence|]. intros a Ha. rewrite H2, H1 by exact Ha. reflexivity.
Qed.

Lemma wframe_weaken : forall (R R' : Z -> Prop) B B', (forall a, R a -> R' a) -> wframe R B B' -> wframe R' B B'.
Proof. intros R R' B B' HR [L H]. split; [exact L|]. intros a Ha. apply H. intros Hr. apply Ha, HR, Hr. Qed.

Lemma wframe_upd : forall (R : Z -> Prop) B k v, 0 <= k -> (Z.to_nat k + length v <= length B)%nat ->
  (forall a, k <= a < k + Z.of_nat (length v) -> R a) -> wframe R B (upd B k v).
Proof.
  intros R B k v Hk Hl HR. split; [apply length_upd; lia|]. intros a Ha.
  rewrite ne_upd by assumption.
  destruct (Nat.leb_spec (Z.to_nat k) a); cbn [andb]; [|reflexivity].
  destruct (Nat.ltb_spec a (Z.to_nat k + length v)); [|reflexivity].
  exfalso. apply Ha, HR. lia.
Qed.

Lemma wframe_sub : forall (R : Z -> Prop) B B' j n, wframe R B B' -> 0 <= j ->
  (forall a, j <= a < j + Z.of_nat n -> ~ R a) -> sub B' j n = sub B j n.
Proof.
  intros R B B' j n [L H] Hj HR. apply nth_error_ext. intros t.
  rewrite (ne_sub B' j n t Hj), (ne_sub B j n t Hj). destruct (Nat.ltb_spec t n); [|reflexivity].
  apply H. apply HR. lia.
Qed.

Lemma wframe_u_at : forall (R : Z -> Prop) B B' j n, wframe R B B' -> 0 <= j ->
  (forall a, j <= a < j + Z.of_nat n -> ~ R a) -> u_at B' j n = u_at B j n.
Proof. intros R B B' j n Hw Hj HR. unfold u_at. rewrite (wframe_sub R B B' j n Hw Hj HR). reflexivity. Qed.

Lemma wframe_s32_at : forall (R : Z -> Prop) B B' j, wframe R B B' -> 0 <= j ->
  (forall a, j <= a < j + 4 -> ~ R a) -> s32_at B' j = s32_at B j.
Proof. intros R B B' j Hw Hj HR. unfold s32_at. rewrite (wframe_u_at R B B' j 4 Hw Hj HR). reflexivity. Qed.


(* ---------------------------------------------------------------- reads through a write: only 0 <= k <= length B *)

Lemma w_length_upd_ge : forall B k v, (length B <= length (upd B k v))%nat.
Proof. intros B k v. unfold upd. rewrite !length_app, length_firstn, length_skipn. lia. Qed.

Lemma w_nth_error_upd_le : forall B k v a, (Z.to_nat k <= length B)%nat ->
  nth_error (upd B k v) a =
  if (a <? Z.to_nat k)%nat then nth_error B a
  else if (a <? Z.to_nat k + length v)%nat then nth_error v (a - Z.to_nat k) else nth_error B a.
Proof.
  intros B k v a Hl. unfold upd.
  assert (Hf : length (firstn (Z.to_nat k) B) = Z.to_nat k) by (rewrite length_firstn; lia).
  destruct (Nat.ltb_spec a (Z.to_nat k)) as [Ha|Ha].
  - rewrite nth_error_app1 by lia. rewrite nth_error_firstn.
    destruct (Nat.ltb_spec a (Z.to_nat k)); [reflexivity|lia].
  - rewrite nth_error_app2 by lia. rewrite Hf.
    destruct (Nat.ltb_spec a (Z.to_nat k + length v)) as [Hb|Hb].
    + rewrite nth_error_app1 by lia. reflexivity.
    + rewrite nth_error_app2 by lia. rewrite nth_error_skipn. f_equal. lia.
Qed.

Lemma w_nth_error_repeat : forall (x : byte) m t,
  nth_error (repeat x m) t = if (t <? m)%nat then Some x else None.
Proof. intros x m. induction m as [|m IH]; intros [|t]; cbn; try reflexivity. apply IH. Qed.

Lemma w_sub_repeat : forall (x : byte) m j n, 0 <= j -> (Z.to_nat j + n <= m)%nat ->
  sub (repeat x m) j n = repeat x n.
Proof.
  intros x m j n Hj Hl. apply nth_error_ext. intros t.
  rewrite (ne_sub (repeat x m) j n t Hj), (w_nth_error_repeat x n t).
  destruct (Nat.ltb_spec t n); [|reflexivity].
  rewrite (w_nth_error_repeat x m (Z.to_nat j + t)).
  destruct (Nat.ltb_spec (Z.to_nat j + t) m); [reflexivity|lia].
Qed.

Lemma w_put_zero : forall m, put m 0 = repeat (b8 0) m.
Proof.
  unfold put. induction m as [|m IH]; [reflexivity|].
  cbn [Z_to_le_bytes repeat]. rewrite Z.shiftr_0_l, IH. reflexivity.
Qed.

Lemma w_bytes_zero : forall n, bytes_le_to_Z (repeat (b8 0) n) = 0.
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [repeat bytes_le_to_Z]. rewrite IH.
  vm_compute. reflexivity.
Qed.

(* a read the write misses *)
Lemma wr_sub_upd_disj : forall B k v j n, 0 <= k -> 0 <= j -> k <= Z.of_nat (length B) ->
  ((j + Z.of_nat n <=? k) || (k + Z.of_nat (length v) <=? j)) = true ->
  sub (upd B k v) j n = sub B j n.
Proof.
  intros B k v j n Hk Hj Hl Hd. apply orb_true_iff in Hd.
  assert (Hd' : j + Z.of_nat n <= k \/ k + Z.of_nat (length v) <= j)
    by (destruct Hd as [H|H]; apply Z.leb_le in H; [left|right]; exact H).
  clear Hd. apply nth_error_ext. intros t.
  rewrite (ne_sub (upd B k v) j n t Hj), (ne_sub B j n t Hj).
  destruct (Nat.ltb_spec t n); [|reflexivity].
  rewrite w_nth_error_upd_le by lia.
  destruct (Nat.ltb_spec (Z.to_nat j + t) (Z.to_nat k)); [reflexivity|].
  destruct (Nat.ltb_spec (Z.to_nat j + t) (Z.to_nat k + length v)); [lia|reflexivity].
Qed.

(* a read inside the list written *)
Lemma wr_sub_upd_in : forall B k v j n, 0 <= k -> k <= Z.of_nat (length B) ->
  ((k <=? j) && (j + Z.of_nat n <=? k + Z.of_nat (length v))) = true ->
  sub (upd B k v) j n = sub v (j - k) n.
Proof.
  intros B k v j n Hk Hl Hb. apply andb_true_iff in Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  apply nth_error_ext. intros t.
  rewrite (ne_sub (upd B k v) j n t ltac:(lia)), (ne_sub v (j - k) n t ltac:(lia)).
  destruct (Nat.ltb_spec t n); [|reflexivity].
  rewrite w_nth_error_upd_le by lia.
  destruct (Nat.ltb_spec (Z.to_nat j + t) (Z.to_nat k)); [lia|].
  destruct (Nat.ltb_spec (Z.to_nat j + t) (Z.to_nat k + length v)); [|lia].
  f_equal. lia.
Qed.

(* the read of the list written *)
Lemma wr_sub_upd_same : forall B k v j n, j = k -> n = length v -> 0 <= k -> k <= Z.of_nat (length B) ->
  sub (upd B k v) j n = v.
Proof.
  intros B k v j n -> -> Hk Hl.
  rewrite (wr_sub_upd_in B k v k (length v) Hk Hl).
  - rewrite Z.sub_diag. exact (sub_all v (length v) eq_refl).
  - apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

(* a read inside a zeroed range (TCb op_begin_m / op 4's memsets, TSess0's memset of g_s) *)
Lemma wr_sub_upd_zero : forall B k m j n, 0 <= k -> k <= Z.of_nat (length B) ->
  ((k <=? j) && (j + Z.of_nat n <=? k + Z.of_nat m)) = true ->
  sub (upd B k (repeat (b8 0) m)) j n = repeat (b8 0) n.
Proof.
  intros B k m j n Hk Hl Hb.
  assert (Hb' : ((k <=? j) && (j + Z.of_nat n <=? k + Z.of_nat (length (repeat (b8 0) m)))) = true)
    by (rewrite repeat_length; exact Hb).
  rewrite (wr_sub_upd_in B k (repeat (b8 0) m) j n Hk Hl Hb').
  apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  apply w_sub_repeat; lia.
Qed.

Lemma wr_sub_upd_zero_put : forall B k m j n, 0 <= k -> k <= Z.of_nat (length B) ->
  ((k <=? j) && (j + Z.of_nat n <=? k + Z.of_nat m)) = true ->
  sub (upd B k (put m 0)) j n = repeat (b8 0) n.
Proof. intros B k m j n Hk Hl Hb. rewrite (w_put_zero m). exact (wr_sub_upd_zero B k m j n Hk Hl Hb). Qed.

Lemma wr_u_upd_disj : forall B k v j n, 0 <= k -> 0 <= j -> k <= Z.of_nat (length B) ->
  ((j + Z.of_nat n <=? k) || (k + Z.of_nat (length v) <=? j)) = true ->
  u_at (upd B k v) j n = u_at B j n.
Proof.
  intros B k v j n Hk Hj Hl Hd. unfold u_at. rewrite (wr_sub_upd_disj B k v j n Hk Hj Hl Hd). reflexivity.
Qed.

Lemma wr_u_upd_in : forall B k v j n, 0 <= k -> k <= Z.of_nat (length B) ->
  ((k <=? j) && (j + Z.of_nat n <=? k + Z.of_nat (length v))) = true ->
  u_at (upd B k v) j n = u_at v (j - k) n.
Proof. intros B k v j n Hk Hl Hb. unfold u_at. rewrite (wr_sub_upd_in B k v j n Hk Hl Hb). reflexivity. Qed.

Lemma wr_u_upd_same : forall B k m w j n, j = k -> n = m -> 0 <= k -> k <= Z.of_nat (length B) ->
  u_at (upd B k (put m w)) j n = w mod 2 ^ (8 * Z.of_nat n).
Proof.
  intros B k m w j n -> -> Hk Hl. unfold u_at.
  rewrite (wr_sub_upd_same B k (put m w) k m eq_refl (eq_sym (length_put m w)) Hk Hl).
  apply bytes_le_to_Z_put.
Qed.

Lemma wr_u_upd_same_id : forall B k m w j n, j = k -> n = m -> 0 <= k -> k <= Z.of_nat (length B) ->
  0 <= w < 2 ^ (8 * Z.of_nat n) -> u_at (upd B k (put m w)) j n = w.
Proof.
  intros B k m w j n Hj Hn Hk Hl Hw. rewrite (wr_u_upd_same B k m w j n Hj Hn Hk Hl).
  apply Z.mod_small. exact Hw.
Qed.

Lemma wr_u_upd_zero : forall B k m j n, 0 <= k -> k <= Z.of_nat (length B) ->
  ((k <=? j) && (j + Z.of_nat n <=? k + Z.of_nat m)) = true ->
  u_at (upd B k (repeat (b8 0) m)) j n = 0.
Proof.
  intros B k m j n Hk Hl Hb. unfold u_at. rewrite (wr_sub_upd_zero B k m j n Hk Hl Hb). apply w_bytes_zero.
Qed.

Lemma wr_u_upd_zero_put : forall B k m j n, 0 <= k -> k <= Z.of_nat (length B) ->
  ((k <=? j) && (j + Z.of_nat n <=? k + Z.of_nat m)) = true ->
  u_at (upd B k (put m 0)) j n = 0.
Proof. intros B k m j n Hk Hl Hb. rewrite (w_put_zero m). exact (wr_u_upd_zero B k m j n Hk Hl Hb). Qed.

Lemma wr_s32_upd_disj : forall B k v j, 0 <= k -> 0 <= j -> k <= Z.of_nat (length B) ->
  ((j + 4 <=? k) || (k + Z.of_nat (length v) <=? j)) = true ->
  s32_at (upd B k v) j = s32_at B j.
Proof.
  intros B k v j Hk Hj Hl Hd. unfold s32_at. rewrite (wr_u_upd_disj B k v j 4 Hk Hj Hl Hd). reflexivity.
Qed.

Lemma wr_s32_upd_in : forall B k v j, 0 <= k -> k <= Z.of_nat (length B) ->
  ((k <=? j) && (j + 4 <=? k + Z.of_nat (length v))) = true ->
  s32_at (upd B k v) j = s32_at v (j - k).
Proof. intros B k v j Hk Hl Hb. unfold s32_at. rewrite (wr_u_upd_in B k v j 4 Hk Hl Hb). reflexivity. Qed.

Lemma wr_s32_upd_same : forall B k w j, j = k -> 0 <= k -> k <= Z.of_nat (length B) ->
  s32_at (upd B k (put 4 w)) j = bv_swrap 32 w.
Proof.
  intros B k w j Hj Hk Hl. unfold s32_at. rewrite (wr_u_upd_same B k 4 w j 4 Hj eq_refl Hk Hl).
  change (8 * Z.of_nat 4) with 32. change (w mod 2 ^ 32) with (bv_wrap 32 w). apply bv_swrap_wrap.
Qed.

Lemma wr_s32_upd_same_id : forall B k w j, j = k -> 0 <= k -> k <= Z.of_nat (length B) ->
  - 2 ^ 31 <= w < 2 ^ 31 -> s32_at (upd B k (put 4 w)) j = w.
Proof.
  intros B k w j Hj Hk Hl Hw. rewrite (wr_s32_upd_same B k w j Hj Hk Hl).
  apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. cbn. lia.
Qed.

Lemma wr_s32_upd_zero : forall B k m j, 0 <= k -> k <= Z.of_nat (length B) ->
  ((k <=? j) && (j + 4 <=? k + Z.of_nat m)) = true ->
  s32_at (upd B k (repeat (b8 0) m)) j = 0.
Proof.
  intros B k m j Hk Hl Hb. unfold s32_at. rewrite (wr_u_upd_zero B k m j 4 Hk Hl Hb). reflexivity.
Qed.

Lemma wr_s32_upd_zero_put : forall B k m j, 0 <= k -> k <= Z.of_nat (length B) ->
  ((k <=? j) && (j + 4 <=? k + Z.of_nat m)) = true ->
  s32_at (upd B k (put m 0)) j = 0.
Proof. intros B k m j Hk Hl Hb. rewrite (w_put_zero m). exact (wr_s32_upd_zero B k m j Hk Hl Hb). Qed.

(* read-after-write of an int at the same offset (u_at: TWorldLemmas.u_at_upd_put; bv_swrap form: s32_at_upd_put) *)

Lemma s32_at_upd_same : forall B k v, 0 <= k -> k <= Z.of_nat (length B) -> - 2 ^ 31 <= v < 2 ^ 31 ->
  s32_at (upd B k (put 4 v)) k = v.
Proof. intros B k v Hk Hl Hv. exact (wr_s32_upd_same_id B k v k eq_refl Hk Hl Hv). Qed.



(* ---------------------------------------------------------------- A2: s->cfg is the copy of g_cfg (DS:64) *)

Lemma a2_sub : forall B o n, agree_cfg B -> 0 <= o -> o + Z.of_nat n <= 60 ->
  sub B (A_S_cfg_host_mac + o) n = sub B (OFF_g_cfg + o) n.
Proof.
  intros B o n H Ho Hn.
  refine (eq_trans (eq_sym (sub_sub B A_S_cfg_host_mac 60 o n _ Ho _)) _);
    [unfold A_S_cfg_host_mac, OFF_g_s; lia | lia |].
  refine (eq_trans (f_equal (fun l => sub l o n) (@a2_cfg B H)) _).
  exact (sub_sub B OFF_g_cfg 60 o n ltac:(unfold OFF_g_cfg; lia) Ho ltac:(lia)).
Qed.

Lemma a2_host_mac : forall B, agree_cfg B -> S_cfg_host_mac B = HOST.
Proof. intros B H. exact (eq_trans (a2_sub B 0 6 H ltac:(lia) ltac:(lia)) (@a1_host_mac B H)). Qed.
Lemma a2_desk_mac : forall B, agree_cfg B -> S_cfg_desk_mac B = Cfg_desk_mac B.
Proof. intros B H. exact (a2_sub B 6 6 H ltac:(lia) ltac:(lia)). Qed.
Lemma a2_desk_mac_set : forall B, agree_cfg B -> S_cfg_desk_mac_set B = Cfg_desk_mac_set B.
Proof. intros B H. exact (f_equal (fun l => bv_swrap 32 (bytes_le_to_Z l)) (a2_sub B 12 4 H ltac:(lia) ltac:(lia))). Qed.
Lemma a2_auto_wake : forall B, agree_cfg B -> S_cfg_auto_wake B = Cfg_auto_wake B.
Proof. intros B H. exact (f_equal (fun l => bv_swrap 32 (bytes_le_to_Z l)) (a2_sub B 16 4 H ltac:(lia) ltac:(lia))). Qed.
Lemma a2_sum_mode : forall B, agree_cfg B -> S_cfg_sum_mode B = Cfg_sum_mode B.
Proof. intros B H. exact (f_equal (fun l => bv_swrap 32 (bytes_le_to_Z l)) (a2_sub B 20 4 H ltac:(lia) ltac:(lia))). Qed.
Lemma a2_keepalive : forall B, agree_cfg B -> S_cfg_keepalive_ms B = Cfg_keepalive_ms B.
Proof. intros B H. exact (f_equal bytes_le_to_Z (a2_sub B 24 4 H ltac:(lia) ltac:(lia))). Qed.
Lemma a2_ack_timeout : forall B, agree_cfg B -> S_cfg_ack_timeout_ms B = Cfg_ack_timeout_ms B.
Proof. intros B H. exact (f_equal bytes_le_to_Z (a2_sub B 28 4 H ltac:(lia) ltac:(lia))). Qed.
Lemma a2_max_retries : forall B, agree_cfg B -> S_cfg_max_retries B = Cfg_max_retries B.
Proof. intros B H. exact (f_equal bytes_le_to_Z (a2_sub B 32 4 H ltac:(lia) ltac:(lia))). Qed.
Lemma a2_backoff : forall B, agree_cfg B -> S_cfg_backoff_ms B = Cfg_backoff_ms B.
Proof. intros B H. exact (f_equal bytes_le_to_Z (a2_sub B 36 4 H ltac:(lia) ltac:(lia))). Qed.
Lemma a2_offline : forall B, agree_cfg B -> S_cfg_offline_ms B = Cfg_offline_ms B.
Proof. intros B H. exact (f_equal bytes_le_to_Z (a2_sub B 40 4 H ltac:(lia) ltac:(lia))). Qed.
Lemma a2_wake_timeout : forall B, agree_cfg B -> S_cfg_wake_timeout_ms B = Cfg_wake_timeout_ms B.
Proof. intros B H. exact (f_equal bytes_le_to_Z (a2_sub B 44 4 H ltac:(lia) ltac:(lia))). Qed.
Lemma a2_display_gap : forall B, agree_cfg B -> S_cfg_display_gap_us B = Cfg_display_gap_us B.
Proof. intros B H. exact (f_equal bytes_le_to_Z (a2_sub B 48 4 H ltac:(lia) ltac:(lia))). Qed.
Lemma a2_max_cmds : forall B, agree_cfg B -> S_cfg_max_cmds B = Cfg_max_cmds B.
Proof. intros B H. exact (f_equal bytes_le_to_Z (a2_sub B 52 4 H ltac:(lia) ltac:(lia))). Qed.
Lemma a2_max_body : forall B, agree_cfg B -> S_cfg_max_body B = Cfg_max_body B.
Proof. intros B H. exact (f_equal bytes_le_to_Z (a2_sub B 56 4 H ltac:(lia) ltac:(lia))). Qed.

(* ---------------------------------------------------------------- wrange *)

(* wrange: for every s32_at / u_at read in the goal (ranges: TWorldLemmas s32_range, u_at_range), and every getter G X / G X i whose body is one (unfolded
   on demand by `red`, so the hypothesis names the folded getter), pose its range once:
   - 2 ^ 31 <= M_state B < 2 ^ 31, 0 <= M_last_rx B < 18446744073709551616, ... (u_at bounds are numerals). *)
Ltac wrange_one t :=
  lazymatch type of t with Z => idtac end;
  let r := lazymatch t with
           | s32_at _ _ => t
           | u_at _ _ _ => t
           | _ => eval red in t
           end in
  lazymatch r with
  | s32_at ?X ?j =>
      lazymatch goal with
      | _ : - 2 ^ 31 <= t < 2 ^ 31 |- _ => fail
      | _ => let H := fresh "Hrng" in pose proof (s32_range X j : - 2 ^ 31 <= t < 2 ^ 31) as H
      end
  | u_at ?X ?j ?n =>
      let p := eval vm_compute in (2 ^ (8 * Z.of_nat n)) in
      lazymatch goal with
      | _ : 0 <= t < p |- _ => fail
      | _ => let H := fresh "Hrng" in pose proof (u_at_range X j n : 0 <= t < p) as H
      end
  end.

Ltac wrange :=
  repeat match goal with
  | |- context [s32_at ?X ?j] => wrange_one (s32_at X j)
  | |- context [u_at ?X ?j ?n] => wrange_one (u_at X j n)
  | |- context [?G ?X ?i] => lazymatch type of X with list byte => wrange_one (G X i) end
  | |- context [?G ?X] => lazymatch type of X with list byte => wrange_one (G X) end
  end.

Example wrange_ex : forall B, - 2 ^ 31 <= M_state B /\ 0 <= M_last_rx B /\ Cmd_key B 3 < 2 ^ 32.
Proof. intros B. wrange. lia. Qed.


(* ================================================================ getter after setter: wsimp, wlen *)

(* every setter of TWorld.v and TCb.v, and every offset / size *)
Ltac wunfold_set :=
  unfold
    set_M_desk_known, set_M_desk, set_M_state, set_M_e2_acked, set_M_e1_us, set_M_foreign, set_M_last_rx,
      set_M_wake_sent, set_M_next_ka, set_M_backoff_until, set_M_last_display, set_M_display_sent,
      set_M_desk_counter_valid, set_M_desk_counter, set_M_host_counter, set_M_fail, set_M_fly_on, set_M_fly_cmd,
      set_M_fly_counter, set_M_fly_retries, set_M_fly_sent, set_M_fly_frame, set_M_fly_len, set_OW_n, set_OW_t_state,
      set_OW_t_old, set_OW_t_reason, set_OW_e2, set_OW_e3, set_OW_acks, set_OW_desk, set_OW_foreign, set_OW_acked,
      set_OW_ndata, set_OW_acked_counter, set_OW_acked_retry, set_OW_desk_off, set_OW_desk_p, set_OW_desk_body,
      set_GOT_n, set_GOT_t_state, set_GOT_t_old, set_GOT_t_reason, set_GOT_e2, set_GOT_e3, set_GOT_acks,
      set_GOT_desk, set_GOT_foreign, set_GOT_acked, set_GOT_ndata, set_S_cfg_host_mac, set_S_cfg_desk_mac,
      set_S_cfg_desk_mac_set, set_S_cfg_auto_wake, set_S_cfg_sum_mode, set_S_cfg_keepalive_ms,
      set_S_cfg_ack_timeout_ms, set_S_cfg_max_retries, set_S_cfg_backoff_ms, set_S_cfg_offline_ms,
      set_S_cfg_wake_timeout_ms, set_S_cfg_display_gap_us, set_S_cfg_max_cmds, set_S_cfg_max_body, set_S_io_ctx,
      set_S_io_send, set_S_io_recv, set_S_io_now_us, set_S_notify, set_S_notify_ctx, set_S_state, set_S_desk_known,
      set_S_desk_mac, set_S_personality, set_S_foreign, set_S_e1_named_us, set_S_wake_acked, set_S_wake_sent_us,
      set_S_host_counter, set_S_desk_counter, set_S_desk_counter_valid, set_S_last_rx_us, set_S_next_keepalive_us,
      set_S_backoff_until_us, set_S_last_display_us, set_S_display_sent, set_S_inflight, set_S_inflight_frame,
      set_S_inflight_len, set_S_inflight_counter, set_S_inflight_retries, set_S_inflight_sent_us, set_S_queue_bytes,
      set_S_queue_len, set_S_queue_display, set_S_queue_key, set_S_queued, set_S_stats_rx_frames,
      set_S_stats_rx_data, set_S_stats_rx_duplicates, set_S_stats_rx_desk_retries, set_S_stats_rx_ignored,
      set_S_stats_tx_frames, set_S_stats_tx_data, set_S_stats_tx_acks, set_S_stats_tx_keepalives,
      set_S_stats_tx_wakes, set_S_stats_tx_retransmits, set_S_stats_ack_lost, set_S_stats_coalesced,
      set_S_stats_refused, set_Cfg_host_mac, set_Cfg_desk_mac, set_Cfg_desk_mac_set, set_Cfg_auto_wake,
      set_Cfg_sum_mode, set_Cfg_keepalive_ms, set_Cfg_ack_timeout_ms, set_Cfg_max_retries, set_Cfg_backoff_ms,
      set_Cfg_offline_ms, set_Cfg_wake_timeout_ms, set_Cfg_display_gap_us, set_Cfg_max_cmds, set_Cfg_max_body,
      set_Cmd_st, set_Cmd_key, set_Cmd_display, set_Cmd_bytes, set_Cmd_len, set_Q_at, set_g_now, set_g_raw,
      set_g_last_counter, set_g_rx_send, set_g_ncmd, set_g_nq, set_g_rx, set_g_rx_len, set_g_rx_fail, set_g_rx_times,
      set_g_fail_next, set_OW_dn_body, set_OW_dn_len, set_OW_dn_counter, set_OW_dn_retry.

Ltac wunfold_addr :=
  cbv beta delta [
    W_LEN OFF_M SZ_M OFF_g_s SZ_g_s OFF_g_cmd SZ_g_cmd OFF_g_q SZ_g_q OFF_g_fail_next SZ_g_fail_next
      OFF_g_raw SZ_g_raw OFF_g_last_counter SZ_g_last_counter OFF_g_nq SZ_g_nq OFF_g_ncmd SZ_g_ncmd
      OFF_g_rx_send SZ_g_rx_send OFF_g_rx_fail SZ_g_rx_fail OFF_g_rx_times SZ_g_rx_times OFF_g_now SZ_g_now
      OFF_g_rx SZ_g_rx OFF_g_rx_len SZ_g_rx_len OFF_g_cfg SZ_g_cfg OFF_GOT SZ_GOT OFF_OW SZ_OW
      A_M_desk_known A_M_desk A_M_state A_M_e2_acked A_M_e1_us A_M_foreign A_M_last_rx A_M_wake_sent
      A_M_next_ka A_M_backoff_until A_M_last_display A_M_display_sent A_M_desk_counter_valid A_M_desk_counter
      A_M_host_counter A_M_fail A_M_fly_on A_M_fly_cmd A_M_fly_counter A_M_fly_retries A_M_fly_sent
      A_M_fly_frame A_M_fly_len A_OW_n A_OW_t_state A_OW_t_old A_OW_t_reason A_OW_e2 A_OW_e3 A_OW_acks
      A_OW_desk A_OW_foreign A_OW_acked A_OW_ndata A_OW_acked_counter A_OW_acked_retry A_OW_desk_off
      A_OW_desk_p A_OW_desk_body A_GOT_n A_GOT_t_state A_GOT_t_old A_GOT_t_reason A_GOT_e2 A_GOT_e3
      A_GOT_acks A_GOT_desk A_GOT_foreign A_GOT_acked A_GOT_ndata A_S_cfg_host_mac A_S_cfg_desk_mac
      A_S_cfg_desk_mac_set A_S_cfg_auto_wake A_S_cfg_sum_mode A_S_cfg_keepalive_ms A_S_cfg_ack_timeout_ms
      A_S_cfg_max_retries A_S_cfg_backoff_ms A_S_cfg_offline_ms A_S_cfg_wake_timeout_ms A_S_cfg_display_gap_us
      A_S_cfg_max_cmds A_S_cfg_max_body A_S_io_ctx A_S_io_send A_S_io_recv A_S_io_now_us A_S_notify
      A_S_notify_ctx A_S_state A_S_desk_known A_S_desk_mac A_S_personality A_S_foreign A_S_e1_named_us
      A_S_wake_acked A_S_wake_sent_us A_S_host_counter A_S_desk_counter A_S_desk_counter_valid A_S_last_rx_us
      A_S_next_keepalive_us A_S_backoff_until_us A_S_last_display_us A_S_display_sent A_S_inflight
      A_S_inflight_frame A_S_inflight_len A_S_inflight_counter A_S_inflight_retries A_S_inflight_sent_us
      A_S_queue_bytes A_S_queue_len A_S_queue_display A_S_queue_key A_S_queued A_S_stats_rx_frames
      A_S_stats_rx_data A_S_stats_rx_duplicates A_S_stats_rx_desk_retries A_S_stats_rx_ignored
      A_S_stats_tx_frames A_S_stats_tx_data A_S_stats_tx_acks A_S_stats_tx_keepalives A_S_stats_tx_wakes
      A_S_stats_tx_retransmits A_S_stats_ack_lost A_S_stats_coalesced A_S_stats_refused A_Cfg_host_mac
      A_Cfg_desk_mac A_Cfg_desk_mac_set A_Cfg_auto_wake A_Cfg_sum_mode A_Cfg_keepalive_ms A_Cfg_ack_timeout_ms
      A_Cfg_max_retries A_Cfg_backoff_ms A_Cfg_offline_ms A_Cfg_wake_timeout_ms A_Cfg_display_gap_us
      A_Cfg_max_cmds A_Cfg_max_body A_Cmd_st A_Cmd_key A_Cmd_display A_Cmd_bytes A_Cmd_len A_OW_dn_body
      A_OW_dn_len A_OW_dn_counter A_OW_dn_retry].

(* the goal is closed: no local variable in it, so vm_compute decides it and no world is in it *)
Ltac wclosed := match goal with |- context [?x] => is_var x; fail 1 | _ => idtac end.

(* lengths of the lists written, by fully applied rewrites of instances found by matching *)
Ltac wlens :=
  repeat match goal with
  | |- context [length (put ?n ?w)] => rewrite (length_put n w)
  | |- context [length (repeat ?x ?m)] => rewrite (repeat_length x m)
  end.

Lemma wb_or : forall a b c d, a <= b \/ c <= d -> ((a <=? b) || (c <=? d)) = true.
Proof. intros a b c d [H|H]; apply orb_true_iff; [left|right]; apply Z.leb_le; exact H. Qed.
Lemma wb_and : forall a b c d, a <= b -> c <= d -> ((a <=? b) && (c <=? d)) = true.
Proof. intros a b c d H1 H2. apply andb_true_iff. split; apply Z.leb_le; assumption. Qed.
Lemma wb_rng32 : forall w, ((- 2 ^ 31 <=? w) && (w <? 2 ^ 31)) = true -> - 2 ^ 31 <= w < 2 ^ 31.
Proof. intros w H. apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia. Qed.
Lemma wb_rngu : forall w p, ((0 <=? w) && (w <? p)) = true -> 0 <= w < p.
Proof. intros w p H. apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia. Qed.

(* 2 ^ (8 * Z.of_nat n) of a literal n as a numeral *)
Ltac wpow_norm :=
  repeat match goal with
  | |- context [2 ^ (8 * Z.of_nat ?n)] =>
      let p := eval vm_compute in (2 ^ (8 * Z.of_nat n)) in
      lazymatch p with Zpos _ => change (2 ^ (8 * Z.of_nat n)) with p end
  end.

(* side conditions (an offset inequality, a boolean of a wr_ lemma, j = k, a nat equality, a value range):
   by computation when closed, else by lia on the unfolded offsets with the context's facts *)
Ltac wle := tryif wclosed then (apply Z.leb_le; vm_compute; reflexivity) else (wunfold_addr; lia).
Ltac wbool :=
  wlens;
  tryif wclosed then (vm_compute; reflexivity)
  else first [ apply wb_or; wunfold_addr; lia | apply wb_and; wunfold_addr; lia ].
Ltac weq :=
  first [ lazymatch goal with |- ?a = ?a => exact eq_refl end
        | tryif wclosed then (apply Z.eqb_eq; vm_compute; reflexivity) else (wunfold_addr; lia) ].
Ltac wneq :=
  wlens;
  first [ lazymatch goal with |- ?a = ?a => exact eq_refl end
        | tryif wclosed then (apply Nat.eqb_eq; vm_compute; reflexivity) else lia ].
Ltac wrng32 := tryif wclosed then (apply wb_rng32; vm_compute; reflexivity) else first [ lia | wrange; lia ].
Ltac wrngu := wpow_norm; tryif wclosed then (apply wb_rngu; vm_compute; reflexivity) else first [ lia | wrange; lia ].

(* Y is syntactically the term W *)
Ltac wis Y W := lazymatch Y with W => idtac end.

(* k <= Z.of_nat (length X), X a chain of writes on a world of length W_LEN *)
Lemma wl_upd : forall B k v x, x <= Z.of_nat (length B) -> x <= Z.of_nat (length (upd B k v)).
Proof. intros B k v x H. pose proof (w_length_upd_ge B k v). lia. Qed.
Lemma wl_base : forall (B : list byte) x, length B = Z.to_nat W_LEN -> x <= W_LEN -> x <= Z.of_nat (length B).
Proof. intros B x H Hx. rewrite H. rewrite Z2Nat.id by (unfold W_LEN; lia). exact Hx. Qed.
Lemma wl_W : forall x, x <= W_LEN -> x <= Z.of_nat (Z.to_nat W_LEN).
Proof. intros x Hx. rewrite Z2Nat.id by (unfold W_LEN; lia). exact Hx. Qed.

Ltac wlen_ge :=
  lazymatch goal with
  | |- _ <= Z.of_nat (length (upd ?X ?k ?v)) => refine (wl_upd X k v _ _); wlen_ge
  | |- _ <= Z.of_nat (Z.to_nat W_LEN) => refine (wl_W _ _); wle
  | |- _ <= Z.of_nat (length ?X) =>
      first
      [ match goal with H : length ?Y = Z.to_nat W_LEN |- _ => wis Y X; refine (wl_base X _ H _); wle end
      | (* X a layer wsimp named: X := upd X' k' v' *)
        match goal with Y := upd ?X' ?k' ?v' |- _ => wis Y X; refine (wl_upd X' k' v' _ _); wlen_ge end ]
  end.

(* rewrite T into R (E : T = R) at every occurrence of T, found syntactically by `pattern`: no unification *)
Ltac wrw E :=
  lazymatch type of E with
  | ?T = ?R =>
      pattern T;
      lazymatch goal with
      | |- ?P _ => refine (@eq_ind_r _ R P _ T E); cbv beta
      end
  end.

(* d = j - k as a numeral when both are literal offsets *)
Ltac wdiff j k :=
  let d := eval vm_compute in (j - k) in
  lazymatch d with
  | Z0 => d
  | Zpos _ => d
  | Zneg _ => d
  | _ => constr:(j - k)
  end.

(* T reads world (upd X k v) (t is T with its getter unfolded by red), Tx is T on X *)
Ltac wread_s32 T Tx t tx X k v j :=
  first
  [ let E := fresh "E" in
    assert (E : T = Tx) by (change (t = tx); refine (wr_s32_upd_disj X k v j _ _ _ _); [wle | wle | wlen_ge | wbool]);
    wrw E; clear E
  | lazymatch v with
    | put _ ?w =>
        first
        [ let E := fresh "E" in
          assert (E : T = w) by (change (t = w); refine (wr_s32_upd_same_id X k w j _ _ _ _); [weq | wle | wlen_ge | wrng32]);
          wrw E; clear E
        | let E := fresh "E" in
          assert (E : T = bv_swrap 32 w) by (change (t = bv_swrap 32 w); refine (wr_s32_upd_same X k w j _ _ _); [weq | wle | wlen_ge]);
          wrw E; clear E ]
    end
  | lazymatch v with
    | repeat (b8 0) ?m =>
        let E := fresh "E" in
        assert (E : T = 0) by (change (t = 0); refine (wr_s32_upd_zero X k m j _ _ _); [wle | wlen_ge | wbool]);
        wrw E; clear E
    | put ?m 0 =>
        let E := fresh "E" in
        assert (E : T = 0) by (change (t = 0); refine (wr_s32_upd_zero_put X k m j _ _ _); [wle | wlen_ge | wbool]);
        wrw E; clear E
    end
  | let d := wdiff j k in
    let E := fresh "E" in
    assert (E : T = s32_at v d) by (change (t = s32_at v d); refine (wr_s32_upd_in X k v j _ _ _); [wle | wlen_ge | wbool]);
    wrw E; clear E ].

Ltac wread_u T Tx t tx X k v j n :=
  first
  [ let E := fresh "E" in
    assert (E : T = Tx) by (change (t = tx); refine (wr_u_upd_disj X k v j n _ _ _ _); [wle | wle | wlen_ge | wbool]);
    wrw E; clear E
  | lazymatch v with
    | put ?m ?w =>
        first
        [ let E := fresh "E" in
          assert (E : T = w) by (change (t = w); refine (wr_u_upd_same_id X k m w j n _ _ _ _ _); [weq | wneq | wle | wlen_ge | wrngu]);
          wrw E; clear E
        | let p := eval vm_compute in (2 ^ (8 * Z.of_nat n)) in
          let E := fresh "E" in
          assert (E : T = w mod p) by (change (t = w mod p); refine (wr_u_upd_same X k m w j n _ _ _ _); [weq | wneq | wle | wlen_ge]);
          wrw E; clear E ]
    end
  | lazymatch v with
    | repeat (b8 0) ?m =>
        let E := fresh "E" in
        assert (E : T = 0) by (change (t = 0); refine (wr_u_upd_zero X k m j n _ _ _); [wle | wlen_ge | wbool]);
        wrw E; clear E
    | put ?m 0 =>
        let E := fresh "E" in
        assert (E : T = 0) by (change (t = 0); refine (wr_u_upd_zero_put X k m j n _ _ _); [wle | wlen_ge | wbool]);
        wrw E; clear E
    end
  | let d := wdiff j k in
    let E := fresh "E" in
    assert (E : T = u_at v d n) by (change (t = u_at v d n); refine (wr_u_upd_in X k v j n _ _ _); [wle | wlen_ge | wbool]);
    wrw E; clear E ].

Ltac wread_sub T Tx t tx X k v j n :=
  first
  [ let E := fresh "E" in
    assert (E : T = Tx) by (change (t = tx); refine (wr_sub_upd_disj X k v j n _ _ _ _); [wle | wle | wlen_ge | wbool]);
    wrw E; clear E
  | let E := fresh "E" in
    assert (E : T = v) by (change (t = v); refine (wr_sub_upd_same X k v j n _ _ _ _); [weq | wneq | wle | wlen_ge]);
    wrw E; clear E
  | lazymatch v with
    | repeat (b8 0) ?m =>
        let E := fresh "E" in
        assert (E : T = repeat (b8 0) n) by (change (t = repeat (b8 0) n); refine (wr_sub_upd_zero X k m j n _ _ _); [wle | wlen_ge | wbool]);
        wrw E; clear E
    | put ?m 0 =>
        let E := fresh "E" in
        assert (E : T = repeat (b8 0) n) by (change (t = repeat (b8 0) n); refine (wr_sub_upd_zero_put X k m j n _ _ _); [wle | wlen_ge | wbool]);
        wrw E; clear E
    end
  | let d := wdiff j k in
    let E := fresh "E" in
    assert (E : T = sub v d n) by (change (t = sub v d n); refine (wr_sub_upd_in X k v j n _ _ _); [wle | wlen_ge | wbool]);
    wrw E; clear E ].

(* the body of a read: T itself when it is a raw read, else its getter unfolded once *)
Ltac wbody T :=
  lazymatch T with
  | s32_at _ _ => T
  | u_at _ _ _ => T
  | sub _ _ _ => T
  | _ => eval red in T
  end.

(* T reads the world W = upd X k v (W that term, or a local definition W := upd X k v); Tx is T on X *)
Ltac wread T Tx W X k v :=
  let t := wbody T in
  let tx := wbody Tx in
  lazymatch t with
  | s32_at W ?j => wread_s32 T Tx t tx X k v j
  | u_at W ?j ?n => wread_u T Tx t tx X k v j n
  | sub W ?j ?n => wread_sub T Tx t tx X k v j n
  end.

Ltac wsimp_once :=
  match goal with
  | |- context [s32_at ?W ?j] =>
      match goal with Y := upd ?X ?k ?v |- _ => wis Y W; wread (s32_at W j) (s32_at X j) W X k v end
  | |- context [u_at ?W ?j ?n] =>
      match goal with Y := upd ?X ?k ?v |- _ => wis Y W; wread (u_at W j n) (u_at X j n) W X k v end
  | |- context [sub ?W ?j ?n] =>
      match goal with Y := upd ?X ?k ?v |- _ => wis Y W; wread (sub W j n) (sub X j n) W X k v end
  | |- context [?G ?W ?i] =>
      match goal with Y := upd ?X ?k ?v |- _ => wis Y W; wread (G W i) (G X i) W X k v end
  | |- context [?G ?W] =>
      match goal with Y := upd ?X ?k ?v |- _ => wis Y W; wread (G W) (G X) W X k v end
  | |- context [s32_at (upd ?X ?k ?v) ?j] => wread (s32_at (upd X k v) j) (s32_at X j) (upd X k v) X k v
  | |- context [u_at (upd ?X ?k ?v) ?j ?n] => wread (u_at (upd X k v) j n) (u_at X j n) (upd X k v) X k v
  | |- context [sub (upd ?X ?k ?v) ?j ?n] => wread (sub (upd X k v) j n) (sub X j n) (upd X k v) X k v
  | |- context [?G (upd ?X ?k ?v) ?i] => wread (G (upd X k v) i) (G X i) (upd X k v) X k v
  | |- context [?G (upd ?X ?k ?v)] => wread (G (upd X k v)) (G X) (upd X k v) X k v
  end.

Ltac wno_upd t := lazymatch t with context [upd _ _ _] => fail | _ => idtac end.

(* name the writes of the goal innermost first (W := upd X k v, X a world without writes or a layer), so each
   read is rewritten on a small term; read through the layers; then unfold the layers left *)
Ltac wsimp_go :=
  first
  [ match goal with
    | |- context [upd ?X ?k ?v] =>
        wno_upd X; wno_upd v;
        let W := fresh "W" in
        set (W := upd X k v);
        wsimp_go;
        try (unfold W; clear W)
    end
  | repeat wsimp_once ].

(* wsimp: unfold the setters (set_X B v = upd B A_X (put n v)), then rewrite every read of a write chain
   through each write, outermost first: a read the write misses becomes the read of the inner world (getters
   stay folded: M_state (set_S_state B 2) -> M_state B); the read of the field written becomes the value (s32:
   v when -2^31 <= v < 2^31, else bv_swrap 32 v; u_at n: v when 0 <= v < 2^(8n), else v mod 2^(8n); a list:
   v); a read inside a zeroed range (repeat (b8 0) m, put m 0) becomes 0 / repeat (b8 0) n; a read inside a
   written list becomes the read of that list. Needs `length B = Z.to_nat W_LEN` in the context for the base
   world B; index side conditions (S_queue_* i, Cmd_* i, Q_at i, OW_t_* i, ...) by lia from the context. A read
   that straddles the end of a write stays. Closes the goal when both sides end up syntactically equal. *)
Ltac wsimp :=
  wunfold_set; wsimp_go;
  try (lazymatch goal with |- ?a = ?a => exact eq_refl end).

(* wlen: length (setter chain on B) = length B (or = Z.to_nat W_LEN), given length B = Z.to_nat W_LEN *)
Lemma wl_eq_upd : forall X k v L, length X = L -> 0 <= k -> k + Z.of_nat (length v) <= Z.of_nat L ->
  length (upd X k v) = L.
Proof. intros X k v L HX Hk Hb. subst L. apply length_upd; assumption. Qed.

Ltac wlen_bnd :=
  lazymatch goal with
  | |- _ <= Z.of_nat (Z.to_nat W_LEN) => refine (wl_W _ _); wlens; wle
  | |- _ <= Z.of_nat (length ?X) =>
      match goal with H : length ?Y = Z.to_nat W_LEN |- _ => wis Y X; refine (wl_base X _ H _); wlens; wle end
  end.

Ltac wlen :=
  wunfold_set;
  let rec go :=
    lazymatch goal with
    | |- length (upd ?X ?k ?v) = ?L => refine (wl_eq_upd X k v L _ _ _); [go | wle | wlen_bnd]
    | |- length ?X = ?L =>
        first [ lazymatch L with length X => exact eq_refl end
              | match goal with H : length ?Y = ?M |- _ => wis Y X; wis M L; exact H end ]
    end in
  go.

(* The examples run with the read primitives opaque, as a proof file may make them (Local Opaque). *)
Section WsimpExamples.
Local Opaque sub upd u_at s32_at put.

Example wsimp_ex_chain3 : forall B, length B = Z.to_nat W_LEN ->
  M_state (set_M_fly_on (set_S_state (set_OW_n B 3) 2) 1) = M_state B.
Proof. intros B HB. wsimp. Qed.

Example wsimp_ex_same : forall B, length B = Z.to_nat W_LEN -> S_state (set_S_state B 2) = 2.
Proof. intros B HB. wsimp. Qed.

Example wsimp_ex_chain12 : forall B, length B = Z.to_nat W_LEN ->
  S_host_counter
    (set_M_state (set_M_fly_on (set_S_state (set_OW_n (set_GOT_n (set_g_now (set_M_last_rx
      (set_S_queued (set_Cmd_st (set_Q_at (set_g_nq (set_S_inflight B 1) 2) 3 4) 5 1) 7) 8) 9) 1) 2) 3) 1) 2)
  = S_host_counter B.
Proof. intros B HB. wsimp. Qed.

Example wsimp_ex_neg : forall B, length B = Z.to_nat W_LEN ->
  M_state (set_M_state (set_S_state B (-1)) (-1)) = -1 /\ S_state (set_M_state (set_S_state B (-1)) (-1)) = -1.
Proof. intros B HB. split; wsimp. Qed.

Example wsimp_ex_u : forall B x, length B = Z.to_nat W_LEN ->
  M_last_rx (set_M_next_ka (set_M_last_rx B x) 5) = x mod 18446744073709551616 /\
  M_next_ka (set_M_next_ka (set_M_last_rx B x) 5) = 5.
Proof. intros B x HB. split; wsimp. Qed.

Example wsimp_ex_index : forall B i j, length B = Z.to_nat W_LEN -> 0 <= i < 1024 -> 0 <= j < 1024 -> i <> j ->
  Cmd_st (set_Cmd_st B i 1) j = Cmd_st B j /\ Cmd_st (set_Cmd_st B i 1) i = 1.
Proof. intros B i j HB Hi Hj Hij. split; wsimp. Qed.

Example wsimp_ex_memset : forall B, length B = Z.to_nat W_LEN ->
  OW_n (upd B OFF_OW (repeat (b8 0) (Z.to_nat SZ_OW))) = 0 /\
  M_state (upd (upd B OFF_OW (repeat (b8 0) (Z.to_nat SZ_OW))) OFF_GOT (repeat (b8 0) (Z.to_nat SZ_GOT)))
    = M_state B /\
  S_state (upd B OFF_g_s (put (Z.to_nat SZ_g_s) 0)) = 0 /\
  S_cfg_host_mac (upd B OFF_g_s (put (Z.to_nat SZ_g_s) 0)) = repeat (b8 0) 6 /\
  M_state (upd B OFF_g_s (put (Z.to_nat SZ_g_s) 0)) = M_state B /\
  M_fly_len (upd B OFF_M (repeat (b8 0) (Z.to_nat SZ_M))) = 0.
Proof. intros B HB. repeat split; wsimp. Qed.

Example wlen_ex : forall B, length B = Z.to_nat W_LEN ->
  length (set_M_fail (set_OW_desk_off (upd B OFF_OW (repeat (b8 0) (Z.to_nat SZ_OW))) (-1)) 0) = length B.
Proof. intros B HB. wlen. Qed.
End WsimpExamples.


(* ================================================================ frames over a list of ranges: wsame *)

Definition in_ranges (rs : list (Z * Z)) (a : Z) : Prop := Exists (fun '(k, n) => k <= a < k + n) rs.

(* B' is B except inside the ranges rs *)
Definition wsame (B B' : list byte) (rs : list (Z * Z)) : Prop := wframe (in_ranges rs) B B'.

(* [j, j + n) misses every range of rs *)
Definition disj (j n : Z) (rs : list (Z * Z)) : bool :=
  forallb (fun '(k, m) => (n <=? 0) || (m <=? 0) || (j + n <=? k) || (k + m <=? j)) rs.
(* [j, j + n) lies inside one range of fp *)
Definition cov (j n : Z) (fp : list (Z * Z)) : bool :=
  (n <=? 0) || existsb (fun '(k, m) => (k <=? j) && (j + n <=? k + m)) fp.
(* every range of rs lies inside one range of fp *)
Definition subr (rs fp : list (Z * Z)) : bool := forallb (fun '(k, n) => cov k n fp) rs.
(* every range of rs misses every range of fp *)
Definition rdisj (rs fp : list (Z * Z)) : bool := forallb (fun '(k, n) => disj k n fp) rs.

Lemma in_ranges_nil : forall a, in_ranges [] a <-> False.
Proof. intros a. unfold in_ranges. split; [intros H; inversion H | intros []]. Qed.

Lemma in_ranges_cons : forall k n rs a, in_ranges ((k, n) :: rs) a <-> (k <= a < k + n) \/ in_ranges rs a.
Proof. intros k n rs a. unfold in_ranges. rewrite Exists_cons. reflexivity. Qed.

Lemma in_ranges_app : forall rs1 rs2 a, in_ranges (rs1 ++ rs2) a <-> in_ranges rs1 a \/ in_ranges rs2 a.
Proof. intros rs1 rs2 a. unfold in_ranges. apply Exists_app. Qed.

Lemma disj_spec : forall j n rs, disj j n rs = true -> forall a, j <= a < j + n -> ~ in_ranges rs a.
Proof.
  intros j n rs. induction rs as [|[k m] rs IH]; intros Hd a Ha Hin.
  - apply in_ranges_nil in Hin. exact Hin.
  - cbn [disj forallb] in Hd. unfold disj in IH. apply andb_true_iff in Hd as [H1 H2].
    apply in_ranges_cons in Hin as [Hin|Hin]; [|exact (IH H2 a Ha Hin)].
    apply orb_true_iff in H1 as [H1|H1]; [apply orb_true_iff in H1 as [H1|H1];
      [apply orb_true_iff in H1 as [H1|H1]|]|]; apply Z.leb_le in H1; lia.
Qed.

Lemma cov_spec : forall j n fp, cov j n fp = true -> forall a, j <= a < j + n -> in_ranges fp a.
Proof.
  intros j n fp Hc a Ha. unfold cov in Hc. apply orb_true_iff in Hc as [Hc|Hc].
  - apply Z.leb_le in Hc. lia.
  - apply existsb_exists in Hc as [[k m] [Hin Hkm]]. apply andb_true_iff in Hkm as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. unfold in_ranges. apply Exists_exists.
    exists (k, m). split; [exact Hin|]. lia.
Qed.

Lemma subr_spec : forall rs fp, subr rs fp = true -> forall a, in_ranges rs a -> in_ranges fp a.
Proof.
  intros rs fp. induction rs as [|[k n] rs IH]; intros Hs a Ha.
  - apply in_ranges_nil in Ha. destruct Ha.
  - cbn [subr forallb] in Hs. unfold subr in IH. apply andb_true_iff in Hs as [H1 H2].
    apply in_ranges_cons in Ha as [Ha|Ha]; [exact (cov_spec k n fp H1 a Ha) | exact (IH H2 a Ha)].
Qed.

(* the footprint form: fp's addresses are not in rs *)
Lemma rdisj_spec : forall rs fp, rdisj rs fp = true -> forall a, in_ranges fp a -> ~ in_ranges rs a.
Proof.
  intros rs fp. induction rs as [|[k n] rs IH]; intros Hr a Hf Ha.
  - apply in_ranges_nil in Ha. exact Ha.
  - cbn [rdisj forallb] in Hr. unfold rdisj in IH. apply andb_true_iff in Hr as [H1 H2].
    apply in_ranges_cons in Ha as [Ha|Ha]; [exact (disj_spec k n fp H1 a Ha Hf) | exact (IH H2 a Hf Ha)].
Qed.

Lemma wsame_refl : forall B, wsame B B [].
Proof. intros B. apply wframe_refl. Qed.

Lemma wsame_len : forall B B' rs, wsame B B' rs -> length B' = length B.
Proof. intros B B' rs [L _]. exact L. Qed.

Lemma wsame_weaken : forall B B' rs rs', (forall a, in_ranges rs a -> in_ranges rs' a) ->
  wsame B B' rs -> wsame B B' rs'.
Proof. intros B B' rs rs' H Hw. exact (wframe_weaken (in_ranges rs) (in_ranges rs') B B' H Hw). Qed.

Lemma wsame_weaken_b : forall B B' rs rs', wsame B B' rs -> subr rs rs' = true -> wsame B B' rs'.
Proof. intros B B' rs rs' Hw Hs. exact (wsame_weaken B B' rs rs' (subr_spec rs rs' Hs) Hw). Qed.

Lemma wsame_upd : forall B k v, 0 <= k -> (Z.to_nat k + length v <= length B)%nat ->
  wsame B (upd B k v) [(k, Z.of_nat (length v))].
Proof.
  intros B k v Hk Hl. apply (wframe_upd (in_ranges [(k, Z.of_nat (length v))]) B k v Hk Hl).
  intros a Ha. apply in_ranges_cons. left. exact Ha.
Qed.

Lemma wsame_trans : forall B1 B2 B3 rs1 rs2, wsame B1 B2 rs1 -> wsame B2 B3 rs2 -> wsame B1 B3 (rs1 ++ rs2).
Proof.
  intros B1 B2 B3 rs1 rs2 H1 H2. apply (wframe_trans (in_ranges (rs1 ++ rs2)) B1 B2 B3).
  - apply (wsame_weaken B1 B2 rs1); [|exact H1]. intros a Ha. apply in_ranges_app. left. exact Ha.
  - apply (wsame_weaken B2 B3 rs2); [|exact H2]. intros a Ha. apply in_ranges_app. right. exact Ha.
Qed.

Lemma wsame_snoc : forall B X rs k v, wsame B X rs -> 0 <= k -> (Z.to_nat k + length v <= length B)%nat ->
  wsame B (upd X k v) (rs ++ [(k, Z.of_nat (length v))]).
Proof.
  intros B X rs k v Hw Hk Hl. apply (wsame_trans B X (upd X k v) rs); [exact Hw|].
  apply wsame_upd; [exact Hk|]. rewrite (wsame_len B X rs Hw). exact Hl.
Qed.

(* transfer of a read [j, j + n) that misses rs *)
Lemma wsame_sub : forall B B' rs j n, wsame B B' rs -> 0 <= j -> disj j (Z.of_nat n) rs = true ->
  sub B' j n = sub B j n.
Proof.
  intros B B' rs j n Hw Hj Hd. apply (wframe_sub (in_ranges rs) B B' j n Hw Hj).
  exact (disj_spec j (Z.of_nat n) rs Hd).
Qed.

Lemma wsame_sub_le : forall B B' rs j n m, wsame B B' rs -> 0 <= j -> (n <= m)%nat ->
  disj j (Z.of_nat m) rs = true -> sub B' j n = sub B j n.
Proof.
  intros B B' rs j n m Hw Hj Hn Hd. apply (wframe_sub (in_ranges rs) B B' j n Hw Hj).
  intros a Ha. apply (disj_spec j (Z.of_nat m) rs Hd a). lia.
Qed.

Lemma wsame_u_at : forall B B' rs j n, wsame B B' rs -> 0 <= j -> disj j (Z.of_nat n) rs = true ->
  u_at B' j n = u_at B j n.
Proof. intros B B' rs j n Hw Hj Hd. unfold u_at. rewrite (wsame_sub B B' rs j n Hw Hj Hd). reflexivity. Qed.

Lemma wsame_s32_at : forall B B' rs j, wsame B B' rs -> 0 <= j -> disj j 4 rs = true ->
  s32_at B' j = s32_at B j.
Proof. intros B B' rs j Hw Hj Hd. unfold s32_at. rewrite (wsame_u_at B B' rs j 4 Hw Hj Hd). reflexivity. Qed.

(* transfer of a read [j, j + n) inside a footprint fp that misses rs *)
Lemma wsame_cov_sub : forall B B' rs fp j n, wsame B B' rs -> (forall a, in_ranges fp a -> ~ in_ranges rs a) ->
  0 <= j -> cov j (Z.of_nat n) fp = true -> sub B' j n = sub B j n.
Proof.
  intros B B' rs fp j n Hw Hd Hj Hc. apply (wframe_sub (in_ranges rs) B B' j n Hw Hj).
  intros a Ha. apply Hd. exact (cov_spec j (Z.of_nat n) fp Hc a Ha).
Qed.

Lemma wsame_cov_sub_le : forall B B' rs fp j n m, wsame B B' rs -> (forall a, in_ranges fp a -> ~ in_ranges rs a) ->
  0 <= j -> (n <= m)%nat -> cov j (Z.of_nat m) fp = true -> sub B' j n = sub B j n.
Proof.
  intros B B' rs fp j n m Hw Hd Hj Hn Hc. apply (wframe_sub (in_ranges rs) B B' j n Hw Hj).
  intros a Ha. apply Hd. apply (cov_spec j (Z.of_nat m) fp Hc a). lia.
Qed.

Lemma wsame_cov_u_at : forall B B' rs fp j n, wsame B B' rs -> (forall a, in_ranges fp a -> ~ in_ranges rs a) ->
  0 <= j -> cov j (Z.of_nat n) fp = true -> u_at B' j n = u_at B j n.
Proof.
  intros B B' rs fp j n Hw Hd Hj Hc. unfold u_at. rewrite (wsame_cov_sub B B' rs fp j n Hw Hd Hj Hc). reflexivity.
Qed.

Lemma wsame_cov_s32_at : forall B B' rs fp j, wsame B B' rs -> (forall a, in_ranges fp a -> ~ in_ranges rs a) ->
  0 <= j -> cov j 4 fp = true -> s32_at B' j = s32_at B j.
Proof.
  intros B B' rs fp j Hw Hd Hj Hc. unfold s32_at. rewrite (wsame_cov_u_at B B' rs fp j 4 Hw Hd Hj Hc). reflexivity.
Qed.

(* ---- tactics *)

(* in_ranges of a literal list as a disjunction of intervals, in a hypothesis or the goal *)
Ltac wranges_in H :=
  repeat match type of H with
  | context [in_ranges (?r1 ++ ?r2) ?a] => rewrite (in_ranges_app r1 r2 a) in H
  | context [in_ranges ((?k, ?n) :: ?r) ?a] => rewrite (in_ranges_cons k n r a) in H
  | context [in_ranges [] ?a] => rewrite (in_ranges_nil a) in H
  end.
Ltac wranges :=
  repeat match goal with
  | |- context [in_ranges (?r1 ++ ?r2) ?a] => rewrite (in_ranges_app r1 r2 a)
  | |- context [in_ranges ((?k, ?n) :: ?r) ?a] => rewrite (in_ranges_cons k n r a)
  | |- context [in_ranges [] ?a] => rewrite (in_ranges_nil a)
  end.

(* (Z.to_nat k + length v <= L)%nat for a write of a chain on a world of length W_LEN *)
Lemma wl_nat : forall k (v : list byte) L, 0 <= k -> k + Z.of_nat (length v) <= Z.of_nat L -> (Z.to_nat k + length v <= L)%nat.
Proof. intros k v L Hk H. lia. Qed.

Ltac wsame_build :=
  lazymatch goal with
  | |- wsame ?B (upd ?X ?k ?v) _ =>
      refine (wsame_snoc B X _ k v _ _ _); [wsame_build | wle | refine (wl_nat k v _ _ _); [wle | wlen_bnd]]
  | |- wsame ?B ?B _ => exact (wsame_refl B)
  end.

(* wsame_tac: wsame B (setter chain on B) rs, given length B = Z.to_nat W_LEN: the ranges of the chain lie
   inside those of rs, by computation when the chain has literal offsets and lengths, else by lia over the
   intervals (index bounds and list lengths from the context) *)
Ltac wsame_tac :=
  wunfold_set;
  lazymatch goal with
  | |- wsame ?B ?X ?rs =>
      eapply (wsame_weaken B X _ rs); [| wsame_build];
      first [ apply subr_spec; wlens; wclosed; vm_compute; reflexivity
            | let a := fresh "a" in let Ha := fresh "Ha" in
              intros a Ha; revert Ha; wranges; wlens; wunfold_addr; intros Ha; lia ]
  end.

(* wsame_rw Hw Hd, Hw : wsame B B' rs, Hd : forall a, in_ranges fp a -> ~ in_ranges rs a: rewrite every read
   of B' in the goal (getters folded, raw sub / u_at / s32_at) whose range lies inside fp (decided by
   computation: literal offsets) into the same read of B *)
Ltac wsame_get Hw Hd T Tx :=
  let t := wbody T in
  let tx := wbody Tx in
  let E := fresh "E" in
  lazymatch t with
  | s32_at _ ?j =>
      assert (E : T = Tx) by (change (t = tx); refine (wsame_cov_s32_at _ _ _ _ j Hw Hd _ _); [wle | wclosed; vm_compute; reflexivity])
  | u_at _ ?j ?n =>
      assert (E : T = Tx) by (change (t = tx); refine (wsame_cov_u_at _ _ _ _ j n Hw Hd _ _); [wle | wclosed; vm_compute; reflexivity])
  | sub _ ?j ?n =>
      assert (E : T = Tx) by (change (t = tx); refine (wsame_cov_sub _ _ _ _ j n Hw Hd _ _); [wle | wclosed; vm_compute; reflexivity])
  end;
  wrw E; clear E.

Ltac wsame_rw Hw Hd :=
  lazymatch type of Hw with
  | wsame ?B ?B' _ =>
      repeat match goal with
      | |- context [s32_at B' ?j] => wsame_get Hw Hd (s32_at B' j) (s32_at B j)
      | |- context [u_at B' ?j ?n] => wsame_get Hw Hd (u_at B' j n) (u_at B j n)
      | |- context [sub B' ?j ?n] => wsame_get Hw Hd (sub B' j n) (sub B j n)
      | |- context [?G B' ?i] => wsame_get Hw Hd (G B' i) (G B i)
      | |- context [?G B'] => wsame_get Hw Hd (G B') (G B)
      end
  end.

(* close the goal by a hypothesis of syntactically the same statement. NOT `match goal with H : ?P |- ?P`:
   Ltac compares a metavariable shared by a hypothesis and the conclusion by conversion, which unfolds two
   different reads of a world (the 31 GB build); wis is a syntactic comparison. *)
Ltac wexact := match goal with H : _ |- ?G => let T := type of H in wis T G; exact H end.

Example wexact_ex : forall B, M_state B = 0 -> S_state B = 1 -> S_state B = 1.
Proof. intros B H1 H2. wexact. Qed.

Section WsameExamples.
Local Opaque sub upd u_at s32_at put.
Example wsame_tac_ex : forall B, length B = Z.to_nat W_LEN ->
  wsame B (set_M_fail (set_OW_desk_off (upd (upd B OFF_OW (repeat (b8 0) (Z.to_nat SZ_OW)))
             OFF_GOT (repeat (b8 0) (Z.to_nat SZ_GOT))) (-1)) 7) [(OFF_OW, SZ_OW); (OFF_GOT, SZ_GOT); (A_M_fail, 4)].
Proof. intros B HB. wsame_tac. Qed.
Example wsame_tac_ex_index : forall B i, length B = Z.to_nat W_LEN -> 0 <= i < 1024 ->
  wsame B (set_Cmd_len (set_Cmd_st B i 1) i 5) [(OFF_g_cmd, SZ_g_cmd)].
Proof. intros B i HB Hi. wsame_tac. Qed.
End WsameExamples.


(* ================================================================ agree: footprints and frame transfer *)

(* what agree_core without agree_q reads, with agree's keepalive clause and g_rx: M but M_fail, the head of g_s
   (cfg, io, state .. inflight_sent_us), g_fail_next, g_raw, g_now, g_rx, g_cfg *)
Definition foot_core : list (Z * Z) :=
  [(OFF_M, 88); (OFF_M + 92, SZ_M - 92); (OFF_g_s, 1760); (OFF_g_fail_next, 1); (OFF_g_raw, 4);
   (OFF_g_now, 8); (OFF_g_rx, 8); (OFF_g_cfg, 60)].
(* foot_core without what agree_misc reads (g_fail_next, S_personality) *)
Definition foot_corem : list (Z * Z) :=
  [(OFF_M, 88); (OFF_M + 92, SZ_M - 92); (OFF_g_s, 128); (OFF_g_s + 136, 1760 - 136); (OFF_g_raw, 4);
   (OFF_g_now, 8); (OFF_g_rx, 8); (OFF_g_cfg, 60)].
(* what agree_q reads: s->queue and S_queued, g_cmd and g_q, g_nq, g_ncmd, g_raw *)
Definition foot_q : list (Z * Z) :=
  [(A_S_queue_bytes 0, A_S_queued + 4 - A_S_queue_bytes 0); (OFF_g_cmd, OFF_g_fail_next - OFF_g_cmd);
   (OFF_g_nq, 4); (OFF_g_ncmd, 4); (OFF_g_raw, 4)].

(* rs misses the footprint (by computation for a literal rs) *)
Definition core_free (rs : list (Z * Z)) : bool := rdisj rs foot_core.
Definition corem_free (rs : list (Z * Z)) : bool := rdisj rs foot_corem.
Definition q_free (rs : list (Z * Z)) : bool := rdisj rs foot_q.

Lemma foot_corem_core : forall rs, (forall a, in_ranges foot_core a -> ~ in_ranges rs a) ->
  forall a, in_ranges foot_corem a -> ~ in_ranges rs a.
Proof.
  intros rs H a Ha. apply H. apply (subr_spec foot_corem foot_core); [vm_compute; reflexivity | exact Ha].
Qed.

(* ---- the sub-records, each under wsame B B' rs with its footprint missing rs *)

Lemma agree_cfg_frame : forall B B' rs, wsame B B' rs -> (forall a, in_ranges foot_corem a -> ~ in_ranges rs a) ->
  agree_cfg B -> agree_cfg B'.
Proof. intros B B' rs Hw Hd H. destruct H. constructor; wsame_rw Hw Hd; wexact. Qed.

Lemma agree_io_frame : forall I B B' rs, wsame B B' rs -> (forall a, in_ranges foot_corem a -> ~ in_ranges rs a) ->
  agree_io I B -> agree_io I B'.
Proof. intros I B B' rs Hw Hd H. destruct H. constructor; wsame_rw Hw Hd; wexact. Qed.

Lemma agree_st_frame : forall B B' rs, wsame B B' rs -> (forall a, in_ranges foot_corem a -> ~ in_ranges rs a) ->
  agree_st B -> agree_st B'.
Proof. intros B B' rs Hw Hd H. destruct H. constructor; wsame_rw Hw Hd; wexact. Qed.

Lemma agree_fly_frame : forall B B' rs, wsame B B' rs -> (forall a, in_ranges foot_corem a -> ~ in_ranges rs a) ->
  agree_fly B -> agree_fly B'.
Proof.
  intros B B' rs Hw Hd H. destruct H as [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11].
  constructor; wsame_rw Hw Hd; try wexact.
  intros Hon. destruct (F11 Hon) as (body & ncmds & H1 & H2 & H3 & H4 & H5 & H6).
  assert (Hn : (Z.to_nat (M_fly_len B) <= 1514)%nat) by (rewrite H4; unfold frame_len; lia).
  assert (E1 : sub B' A_M_fly_frame (Z.to_nat (M_fly_len B)) = sub B A_M_fly_frame (Z.to_nat (M_fly_len B)))
    by (refine (wsame_cov_sub_le B B' rs foot_corem A_M_fly_frame _ 1514 Hw Hd _ Hn _);
        [wle | vm_compute; reflexivity]).
  assert (E2 : sub B' A_S_inflight_frame (Z.to_nat (M_fly_len B)) = sub B A_S_inflight_frame (Z.to_nat (M_fly_len B)))
    by (refine (wsame_cov_sub_le B B' rs foot_corem A_S_inflight_frame _ 1514 Hw Hd _ Hn _);
        [wle | vm_compute; reflexivity]).
  wrw E1. wrw E2. exists body, ncmds. exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 H6))))).
Qed.

Lemma agree_time_frame : forall ops ops' B B' rs, wsame B B' rs ->
  (forall a, in_ranges foot_corem a -> ~ in_ranges rs a) -> 0 <= ops <= ops' -> agree_time ops B -> agree_time ops' B'.
Proof. intros ops ops' B B' rs Hw Hd Ho H. destruct H. constructor; wsame_rw Hw Hd; first [wexact | lia]. Qed.

Lemma c2_keepalive_frame : forall B B' rs, wsame B B' rs -> (forall a, in_ranges foot_corem a -> ~ in_ranges rs a) ->
  c2_keepalive B -> c2_keepalive B'.
Proof. intros B B' rs Hw Hd H. unfold c2_keepalive in *. wsame_rw Hw Hd. exact H. Qed.

Lemma g_rx_frame : forall B B' rs, wsame B B' rs -> (forall a, in_ranges foot_corem a -> ~ in_ranges rs a) ->
  g_rx B = 0 -> g_rx B' = 0.
Proof. intros B B' rs Hw Hd H. wsame_rw Hw Hd. exact H. Qed.

Lemma agree_misc_frame : forall I B B' rs, wsame B B' rs -> (forall a, in_ranges foot_core a -> ~ in_ranges rs a) ->
  agree_misc I B -> agree_misc I B'.
Proof. intros I B B' rs Hw Hd H. destruct H. constructor; wsame_rw Hw Hd; wexact. Qed.

(* ---- agree_q: the indexed reads, inside s->queue (i < 512) and g_cmd / g_q (k < 1024) *)

Section QFrame.
Variables (B B' : list byte) (rs : list (Z * Z)).
Hypothesis Hw : wsame B B' rs.
Hypothesis Hd : forall a, in_ranges foot_q a -> ~ in_ranges rs a.

Lemma wq_queue : forall i j n, 0 <= i < 512 -> A_S_queue_bytes i <= j -> j + Z.of_nat n <= A_S_queue_bytes i + 32 ->
  sub B' j n = sub B j n.
Proof.
  intros i j n Hi Hj1 Hj2. apply (wframe_sub (in_ranges rs) B B' j n Hw); [unfold A_S_queue_bytes, OFF_g_s in *; lia|].
  intros a Ha. apply Hd. unfold foot_q. apply in_ranges_cons. left.
  unfold A_S_queue_bytes, A_S_queued, OFF_g_s in *; lia.
Qed.

Lemma wq_cmdq : forall j n, OFF_g_cmd <= j -> j + Z.of_nat n <= OFF_g_fail_next -> sub B' j n = sub B j n.
Proof.
  intros j n Hj1 Hj2. apply (wframe_sub (in_ranges rs) B B' j n Hw); [unfold OFF_g_cmd in *; lia|].
  intros a Ha. apply Hd. unfold foot_q. apply in_ranges_cons. right. apply in_ranges_cons. left.
  unfold OFF_g_cmd, OFF_g_fail_next in *; lia.
Qed.

Lemma wq_S_queue_bytes : forall i, 0 <= i < 512 -> S_queue_bytes B' i = S_queue_bytes B i.
Proof.
  intros i Hi. exact (wq_queue i (A_S_queue_bytes i) 24 Hi ltac:(unfold A_S_queue_bytes; lia)
    ltac:(unfold A_S_queue_bytes; lia)).
Qed.
Lemma wq_S_queue_len : forall i, 0 <= i < 512 -> S_queue_len B' i = S_queue_len B i.
Proof.
  intros i Hi. exact (f_equal bytes_le_to_Z (wq_queue i (A_S_queue_len i) 1 Hi
    ltac:(unfold A_S_queue_len, A_S_queue_bytes; lia) ltac:(unfold A_S_queue_len, A_S_queue_bytes; lia))).
Qed.
Lemma wq_S_queue_display : forall i, 0 <= i < 512 -> S_queue_display B' i = S_queue_display B i.
Proof.
  intros i Hi. exact (f_equal bytes_le_to_Z (wq_queue i (A_S_queue_display i) 1 Hi
    ltac:(unfold A_S_queue_display, A_S_queue_bytes; lia) ltac:(unfold A_S_queue_display, A_S_queue_bytes; lia))).
Qed.
Lemma wq_S_queue_key : forall i, 0 <= i < 512 -> S_queue_key B' i = S_queue_key B i.
Proof.
  intros i Hi. exact (f_equal bytes_le_to_Z (wq_queue i (A_S_queue_key i) 4 Hi
    ltac:(unfold A_S_queue_key, A_S_queue_bytes; lia) ltac:(unfold A_S_queue_key, A_S_queue_bytes; lia))).
Qed.

Lemma wq_Cmd_st : forall k, 0 <= k < 1024 -> Cmd_st B' k = Cmd_st B k.
Proof.
  intros k Hk. exact (f_equal (fun l => bv_swrap 32 (bytes_le_to_Z l)) (wq_cmdq (A_Cmd_st k) 4
    ltac:(unfold A_Cmd_st; lia) ltac:(unfold A_Cmd_st, OFF_g_cmd, OFF_g_fail_next; lia))).
Qed.
Lemma wq_Cmd_key : forall k, 0 <= k < 1024 -> Cmd_key B' k = Cmd_key B k.
Proof.
  intros k Hk. exact (f_equal bytes_le_to_Z (wq_cmdq (A_Cmd_key k) 4
    ltac:(unfold A_Cmd_key; lia) ltac:(unfold A_Cmd_key, OFF_g_cmd, OFF_g_fail_next; lia))).
Qed.
Lemma wq_Cmd_display : forall k, 0 <= k < 1024 -> Cmd_display B' k = Cmd_display B k.
Proof.
  intros k Hk. exact (f_equal (fun l => bv_swrap 32 (bytes_le_to_Z l)) (wq_cmdq (A_Cmd_display k) 4
    ltac:(unfold A_Cmd_display; lia) ltac:(unfold A_Cmd_display, OFF_g_cmd, OFF_g_fail_next; lia))).
Qed.
Lemma wq_Cmd_bytes : forall k, 0 <= k < 1024 -> Cmd_bytes B' k = Cmd_bytes B k.
Proof.
  intros k Hk. exact (wq_cmdq (A_Cmd_bytes k) 24
    ltac:(unfold A_Cmd_bytes; lia) ltac:(unfold A_Cmd_bytes, OFF_g_cmd, OFF_g_fail_next; lia)).
Qed.
Lemma wq_Cmd_len : forall k, 0 <= k < 1024 -> Cmd_len B' k = Cmd_len B k.
Proof.
  intros k Hk. exact (f_equal bytes_le_to_Z (wq_cmdq (A_Cmd_len k) 1
    ltac:(unfold A_Cmd_len; lia) ltac:(unfold A_Cmd_len, OFF_g_cmd, OFF_g_fail_next; lia))).
Qed.
Lemma wq_Q_at : forall i, 0 <= i < 1024 -> Q_at B' i = Q_at B i.
Proof.
  intros i Hi. exact (f_equal bytes_le_to_Z (wq_cmdq (OFF_g_q + 4 * i) 4
    ltac:(unfold OFF_g_q, OFF_g_cmd; lia) ltac:(unfold OFF_g_q, OFF_g_fail_next; lia))).
Qed.
End QFrame.

(* wq_rw Hw Hd: rewrite each indexed queue read of B' (S_queue_* i, Cmd_* k, Q_at i) into the read of B, the
   index bound (i < 512, k < 1024) by lia from the context *)
Ltac wq_rw Hw Hd :=
  lazymatch type of Hw with
  | wsame ?B ?B' ?rs =>
      repeat match goal with
      | |- context [?G B' ?i] =>
          let E := fresh "E" in
          lazymatch G with
          | S_queue_bytes => assert (E : G B' i = G B i) by (apply (wq_S_queue_bytes B B' rs Hw Hd i); lia)
          | S_queue_len => assert (E : G B' i = G B i) by (apply (wq_S_queue_len B B' rs Hw Hd i); lia)
          | S_queue_display => assert (E : G B' i = G B i) by (apply (wq_S_queue_display B B' rs Hw Hd i); lia)
          | S_queue_key => assert (E : G B' i = G B i) by (apply (wq_S_queue_key B B' rs Hw Hd i); lia)
          | Cmd_st => assert (E : G B' i = G B i) by (apply (wq_Cmd_st B B' rs Hw Hd i); lia)
          | Cmd_key => assert (E : G B' i = G B i) by (apply (wq_Cmd_key B B' rs Hw Hd i); lia)
          | Cmd_display => assert (E : G B' i = G B i) by (apply (wq_Cmd_display B B' rs Hw Hd i); lia)
          | Cmd_bytes => assert (E : G B' i = G B i) by (apply (wq_Cmd_bytes B B' rs Hw Hd i); lia)
          | Cmd_len => assert (E : G B' i = G B i) by (apply (wq_Cmd_len B B' rs Hw Hd i); lia)
          | Q_at => assert (E : G B' i = G B i) by (apply (wq_Q_at B B' rs Hw Hd i); lia)
          end;
          wrw E; clear E
      end
  end.

Lemma agree_q_frame : forall ops ops' B B' rs, agree_q ops B -> ops <= ops' <= OPS_MAX ->
  wsame B B' rs -> q_free rs = true -> agree_q ops' B'.
Proof.
  intros ops ops' B B' rs H Ho Hw Hf.
  pose proof (rdisj_spec rs foot_q Hf) as Hd.
  destruct H as [Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10].
  assert (Hc : g_ncmd B <= 1024) by (unfold OPS_MAX in Ho; lia).
  constructor; wsame_rw Hw Hd.
  - exact Q1.
  - exact Q2.
  - intros Hr i Hi. pose proof (Q2 Hr) as Hnq. unfold QUEUE_MAX in Hnq.
    destruct (Q3 Hr i Hi) as (Hk & Hst & Hb & Hl & Hkey & Hdisp).
    wq_rw Hw Hd. exact (conj Hk (conj Hst (conj Hb (conj Hl (conj Hkey Hdisp))))).
  - intros Hr i j Hi Hj Heq. pose proof (Q2 Hr) as Hnq. unfold QUEUE_MAX in Hnq.
    apply (Q4 Hr i j Hi Hj).
    exact (eq_trans (eq_sym (wq_Q_at B B' rs Hw Hd i ltac:(lia))) (eq_trans Heq (wq_Q_at B B' rs Hw Hd j ltac:(lia)))).
  - intros Hr k Hk. pose proof (Q2 Hr) as Hnq. unfold QUEUE_MAX in Hnq.
    wq_rw Hw Hd. destruct (Q5 Hr k Hk) as [P1 P2]. split.
    + intros Hst. destruct (P1 Hst) as [i [Hi Hq]]. exists i. split; [exact Hi|].
      exact (eq_trans (wq_Q_at B B' rs Hw Hd i ltac:(lia)) Hq).
    + intros [i [Hi Hq]]. apply P2. exists i. split; [exact Hi|].
      exact (eq_trans (eq_sym (wq_Q_at B B' rs Hw Hd i ltac:(lia))) Hq).
  - intros k Hk. wq_rw Hw Hd. exact (Q6 k Hk).
  - lia.
  - lia.
  - exact Q9.
  - intros Hr i Hi. pose proof (Q9 Hr) as Hq9. unfold QUEUE_MAX in Hq9. wq_rw Hw Hd. exact (Q10 Hr i Hi).
Qed.

(* ---- the two layers *)

Lemma agree_core_frame_p : forall I ops ops' B B' rs, agree_core I ops B -> ops <= ops' <= OPS_MAX ->
  wsame B B' rs -> (forall a, in_ranges foot_corem a -> ~ in_ranges rs a) ->
  agree_q ops' B' -> agree_misc I B' -> agree_core I ops' B'.
Proof.
  intros I ops ops' B B' rs H Ho Hw Hd Hq Hm.
  destruct H as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq0 Hmisc].
  assert (Ho0 : 0 <= ops) by (destruct Hq0 as [_ _ _ _ _ _ _ Hops _ _]; lia).
  constructor.
  - exact Himg.
  - exact (eq_trans (wsame_len B B' rs Hw) Hlen).
  - exact (agree_cfg_frame B B' rs Hw Hd Hcfg).
  - exact (agree_io_frame I B B' rs Hw Hd Hio).
  - exact (agree_st_frame B B' rs Hw Hd Hst).
  - exact (agree_fly_frame B B' rs Hw Hd Hfly).
  - exact (agree_time_frame ops ops' B B' rs Hw Hd ltac:(lia) Htime).
  - exact Hq.
  - exact Hm.
Qed.

Lemma agree_core_frame : forall I ops ops' B B' rs, agree_core I ops B -> ops <= ops' <= OPS_MAX ->
  wsame B B' rs -> core_free rs = true -> agree_q ops' B' -> agree_core I ops' B'.
Proof.
  intros I ops ops' B B' rs H Ho Hw Hc Hq.
  pose proof (rdisj_spec rs foot_core Hc) as Hd.
  apply (agree_core_frame_p I ops ops' B B' rs H Ho Hw (foot_corem_core rs Hd) Hq).
  exact (agree_misc_frame I B B' rs Hw Hd (@ac_misc I ops B H)).
Qed.

(* the version for a write of g_fail_next or S_personality: agree_misc of B' is a premise *)
Lemma agree_core_frame_m : forall I ops ops' B B' rs, agree_core I ops B -> ops <= ops' <= OPS_MAX ->
  wsame B B' rs -> corem_free rs = true -> agree_q ops' B' -> agree_misc I B' -> agree_core I ops' B'.
Proof.
  intros I ops ops' B B' rs H Ho Hw Hc.
  exact (agree_core_frame_p I ops ops' B B' rs H Ho Hw (rdisj_spec rs foot_corem Hc)).
Qed.

Lemma agree_frame : forall I ops ops' B B' rs, agree I ops B -> ops <= ops' <= OPS_MAX ->
  wsame B B' rs -> core_free rs = true -> q_free rs = true -> agree I ops' B'.
Proof.
  intros I ops ops' B B' rs H Ho Hw Hc Hq. destruct H as [Hcore Hka Hrx].
  pose proof (foot_corem_core rs (rdisj_spec rs foot_core Hc)) as Hd.
  constructor.
  - exact (agree_core_frame I ops ops' B B' rs Hcore Ho Hw Hc
             (agree_q_frame ops ops' B B' rs (@ac_q I ops B Hcore) Ho Hw Hq)).
  - exact (c2_keepalive_frame B B' rs Hw Hd Hka).
  - exact (g_rx_frame B B' rs Hw Hd Hrx).
Qed.

Lemma agree_core_mono : forall I ops ops' B, agree_core I ops B -> ops <= ops' <= OPS_MAX -> agree_core I ops' B.
Proof.
  intros I ops ops' B H Ho. destruct H as [Himg Hlen Hcfg Hio Hst Hfly Htime Hq Hmisc].
  destruct Hq as [Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10]. destruct Htime as [T1 T2 T3 T4 T5 T6 T7 T8 T9 T10].
  constructor.
  - exact Himg.
  - exact Hlen.
  - exact Hcfg.
  - exact Hio.
  - exact Hst.
  - exact Hfly.
  - constructor; [lia | exact T2 | exact T3 | exact T4 | exact T5 | exact T6 | exact T7 | exact T8 | exact T9
                 | exact T10].
  - constructor; [exact Q1 | exact Q2 | exact Q3 | exact Q4 | exact Q5 | exact Q6 | lia | lia | exact Q9 | exact Q10].
  - exact Hmisc.
Qed.

Lemma agree_mono : forall I ops ops' B, agree I ops B -> ops <= ops' <= OPS_MAX -> agree I ops' B.
Proof.
  intros I ops ops' B H Ho. destruct H as [Hcore Hka Hrx].
  constructor; [exact (agree_core_mono I ops ops' B Hcore Ho) | exact Hka | exact Hrx].
Qed.

(* ================================================================ named operation facts *)

(* op_begin (TCb.v op_begin_m, FT:388-394) writes only OW, GOT and M_fail *)
Lemma op_begin_frame : forall B B1, op_begin_m B = Some (B1, tt) -> length B = Z.to_nat W_LEN ->
  wsame B B1 [(OFF_OW, SZ_OW); (OFF_GOT, SZ_GOT); (A_M_fail, 4)].
Proof. intros B B1 H HB. unfold op_begin_m in H. cbv zeta in H. injection H as E. subst B1. wsame_tac. Qed.

Lemma agree_op_begin : forall I ops B B1, agree I ops B -> op_begin_m B = Some (B1, tt) -> agree I ops B1.
Proof.
  intros I ops B B1 H Hb.
  pose proof (@ac_len I ops B (@ag_core I ops B H)) as HL.
  pose proof (@d3_ops ops B (@ac_q I ops B (@ag_core I ops B H))) as Ho.
  apply (agree_frame I ops ops B B1 _ H ltac:(lia) (op_begin_frame B B1 Hb HL)); vm_compute; reflexivity.
Qed.

Lemma agree_core_op_begin : forall I ops B B1, agree_core I ops B -> op_begin_m B = Some (B1, tt) ->
  agree_core I ops B1.
Proof.
  intros I ops B B1 H Hb.
  pose proof (@ac_len I ops B H) as HL.
  pose proof (@d3_ops ops B (@ac_q I ops B H)) as Ho.
  pose proof (op_begin_frame B B1 Hb HL) as Hw.
  apply (agree_core_frame I ops ops B B1 _ H ltac:(lia) Hw); [vm_compute; reflexivity|].
  apply (agree_q_frame ops ops B B1 _ (@ac_q I ops B H) ltac:(lia) Hw). vm_compute. reflexivity.
Qed.

(* op 7 (FT:1206-1208) sets g_fail_next to 1: e1_fail_next stays bit01 *)
Lemma agree_fail_next : forall I ops B, agree I ops B -> agree I ops (set_g_fail_next B 1).
Proof.
  intros I ops B H. destruct H as [Hc Hka Hrx].
  pose proof (@ac_len I ops B Hc) as HL.
  pose proof (@d3_ops ops B (@ac_q I ops B Hc)) as Ho.
  assert (Hw : wsame B (set_g_fail_next B 1) [(OFF_g_fail_next, 1)]) by wsame_tac.
  assert (Hdm : forall a, in_ranges foot_corem a -> ~ in_ranges [(OFF_g_fail_next, 1)] a)
    by (apply rdisj_spec; vm_compute; reflexivity).
  assert (Hm : agree_misc I (set_g_fail_next B 1)).
  { destruct (@ac_misc I ops B Hc) as [M1 M2]. constructor.
    - unfold bit01. wsimp. right. exact eq_refl.
    - wsimp. exact M2. }
  constructor.
  - refine (agree_core_frame_p I ops ops B _ _ Hc ltac:(lia) Hw Hdm _ Hm).
    refine (agree_q_frame ops ops B _ _ (@ac_q I ops B Hc) ltac:(lia) Hw _). vm_compute. reflexivity.
  - exact (c2_keepalive_frame B _ _ Hw Hdm Hka).
  - exact (g_rx_frame B _ _ Hw Hdm Hrx).
Qed.

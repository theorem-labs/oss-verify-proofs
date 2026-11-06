(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: the doubling potential of a growing block and the count chain of the g_out block, for the
   secondary-request counts (nsec_tr) of the per-trace count files. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyKfChain.v, with its module paths changed; 1 line of the source is left out. *)
(* KF-COUNT: the ONE growth potential and g_out count chain shared by the per-trace count files (ReplyKfTr.v,
   ReplyKfTrRr.v, ReplyKfTrRig.v, ReplyKfTrSm.v).  proves no function (kind: segment lemma).
   - kf_lg x = log2 (x / 32256), the potential of a block of x bytes.  A growth from s to c >= 2 s (send_line's g_out:
     c = 2 (no + n) with s < no + n; a list vector: 16 cap -> 32 cap; drain's buffer: cap -> 2 cap) raises kf_lg by at
     least 1 when c is secondary (64512 < c) and never lowers it, for any s (kf_lg_grow).  kf_lg x >= 0, monotone,
     kf_lg (2 ^ 30) = 15 (kf_lg_2_30, kf_lg_le15).
   - kf_ch c t c': t takes the g_out block from cap c to cap c'; t's count is at most kf_lg c' - kf_lg c, and c' is c
     or at most t's largest request (W_contract.tr_max).  It composes over ++ (kf_ch_app); a free keeps it
     (kf_ch_free_cons); a growth event extends it (kf_ch_malloc, kf_ch_realloc); send_line's rounds, send_line,
     gesture_end and the key run of gestures_end keep it (kf_sl_run, kf_send, kf_gend, kf_ker).
   - kf_ch_bound: a chain whose largest request is at most M counts at most kf_lg M; kf_ch_15: below 2 ^ 30 (a spec's
     pre tr_max tr < MMAX, fr_MMAX = 1,072,693,248 < 2 ^ 30, CfParamsReply.reply_HMMAX) at most 15; kf_keys: a key
     run below 2 ^ 30 counts at most KC_ke = 15.
   - kf_tm_nonneg, kf_tm_app: tr_max over ++. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT RelayRunF send_line_b_c gesture_end_b_c gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyKfNsec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ------------------------------------------------------------------ the largest request of a trace *)
Lemma kf_tm_nonneg : forall (P : Type) (t : list (RelayRunT.rev P)), 0 <= W_contract.tr_max t.
Proof.
  intros P t. induction t as [|[n|k a|k n a] r IH]; unfold W_contract.tr_max in *; cbn [fold_right]; lia.
Qed.

Lemma kf_tm_app : forall (P : Type) (a b : list (RelayRunT.rev P)),
  W_contract.tr_max (a ++ b) = Z.max (W_contract.tr_max a) (W_contract.tr_max b).
Proof.
  intros P a b. pose proof (kf_tm_nonneg P b) as Hb.
  induction a as [|[n|k x|k n x] r IH]; cbn [app]; unfold W_contract.tr_max in *; cbn [fold_right]; lia.
Qed.

(* ------------------------------------------------------------------ the growth potential *)
Definition kf_lg (x : Z) : Z := Z.log2 (x / 32256).

Lemma kf_lg_nonneg : forall x, 0 <= kf_lg x.
Proof. intros x. unfold kf_lg. apply Z.log2_nonneg. Qed.

Lemma kf_lg_mono : forall x y, x <= y -> kf_lg x <= kf_lg y.
Proof. intros x y H. unfold kf_lg. apply Z.log2_le_mono. apply Z.div_le_mono; lia. Qed.

Lemma kf_lg_2_30 : kf_lg (2 ^ 30) = 15.
Proof. vm_compute. reflexivity. Qed.

Lemma kf_lg_le15 : forall x, x <= 2 ^ 30 -> kf_lg x <= 15.
Proof. intros x H. rewrite <- kf_lg_2_30. exact (kf_lg_mono x (2 ^ 30) H). Qed.

(* a growth from s to c >= 2 s: kf_lg rises by 1 when c is secondary, and never falls (any s) *)
Lemma kf_lg_grow : forall s c, 2 * s <= c -> kf_lg s + (if 64512 <? c then 1 else 0) <= kf_lg c.
Proof.
  intros s c H. unfold kf_lg.
  destruct (Z.lt_ge_cases s 32256) as [Hs|Hb].
  - assert (Hq : s / 32256 <= 0).
    { apply Z.lt_succ_r. apply Z.div_lt_upper_bound; lia. }
    rewrite (Z.log2_nonpos _ Hq).
    destruct (Z.ltb_spec 64512 c) as [Hc|Hc].
    + assert (H2 : 2 <= c / 32256) by (apply Z.div_le_lower_bound; lia).
      pose proof (Z.log2_le_mono 2 (c / 32256) H2) as L. change (Z.log2 2) with 1 in L. lia.
    + pose proof (Z.log2_nonneg (c / 32256)). lia.
  - assert (Hq : 1 <= s / 32256) by (apply Z.div_le_lower_bound; lia).
    assert (H2 : 2 * (s / 32256) <= c / 32256).
    { apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le s 32256 ltac:(lia)). lia. }
    pose proof (Z.log2_le_mono _ _ H2) as L. rewrite Z.log2_double in L by lia.
    destruct (Z.ltb_spec 64512 c); lia.
Qed.

(* ------------------------------------------------------------------ the count chain of one block *)
Definition kf_ch {P : Type} (c : Z) (t : list (RelayRunT.rev P)) (c' : Z) : Prop :=
  nsec_tr t + kf_lg c <= kf_lg c' /\ c' <= Z.max c (W_contract.tr_max t).

Lemma kf_ch_nil : forall (P : Type) c, kf_ch c (@nil (RelayRunT.rev P)) c.
Proof. intros P c. unfold kf_ch. rewrite nsec_tr_nil. lia. Qed.

Lemma kf_ch_app : forall (P : Type) c c1 c2 (a b : list (RelayRunT.rev P)),
  kf_ch c a c1 -> kf_ch c1 b c2 -> kf_ch c (a ++ b) c2.
Proof.
  intros P c c1 c2 a b [A1 A2] [B1 B2]. unfold kf_ch. rewrite nsec_tr_app, kf_tm_app. lia.
Qed.

Lemma kf_ch_free_cons : forall (P : Type) c c' k (x : RelayRunT.addr P) (r : list (RelayRunT.rev P)),
  kf_ch c r c' -> kf_ch c (RelayRunT.RFree k x :: r) c'.
Proof.
  intros P c c' k x r [H1 H2]. unfold kf_ch. rewrite nsec_tr_cons. unfold W_contract.tr_max in *.
  cbn [fold_right]. lia.
Qed.

Lemma kf_ch_malloc : forall (P : Type) cap c c'' (r : list (RelayRunT.rev P)),
  2 * cap <= c -> kf_ch c r c'' -> kf_ch cap (RelayRunT.RMalloc c :: r) c''.
Proof.
  intros P cap c c'' r Hc [H1 H2]. pose proof (kf_lg_grow cap c Hc) as G. unfold kf_ch. rewrite nsec_tr_cons.
  unfold W_contract.tr_max in *. cbn [fold_right]. lia.
Qed.

Lemma kf_ch_realloc : forall (P : Type) cap k c c'' (x : RelayRunT.addr P) (r : list (RelayRunT.rev P)),
  2 * cap <= c -> kf_ch c r c'' -> kf_ch cap (RelayRunT.RRealloc k c x :: r) c''.
Proof.
  intros P cap k c c'' x r Hc [H1 H2]. pose proof (kf_lg_grow cap c Hc) as G. unfold kf_ch. rewrite nsec_tr_cons.
  unfold W_contract.tr_max in *. cbn [fold_right]. lia.
Qed.

(* a chain whose requests are at most M counts at most kf_lg M *)
Lemma kf_ch_bound : forall (P : Type) c (t : list (RelayRunT.rev P)) c' M,
  kf_ch c t c' -> W_contract.tr_max t <= M -> nsec_tr t <= kf_lg M.
Proof.
  intros P c t c' M [H1 H2] HM. pose proof (kf_lg_nonneg c) as N0. pose proof (kf_lg_nonneg M) as N1.
  destruct (Z.le_gt_cases c' c) as [Hle|Hgt].
  - pose proof (kf_lg_mono c' c Hle). lia.
  - assert (Hc' : c' <= M) by lia. pose proof (kf_lg_mono c' M Hc'). lia.
Qed.

(* below 2 ^ 30: at most 15 *)
Lemma kf_ch_15 : forall (P : Type) c (t : list (RelayRunT.rev P)) c',
  kf_ch c t c' -> W_contract.tr_max t < 2 ^ 30 -> nsec_tr t <= 15.
Proof.
  intros P c t c' H HM. rewrite <- kf_lg_2_30. exact (kf_ch_bound P c t c' (2 ^ 30) H ltac:(lia)).
Qed.

(* ------------------------------------------------------------------ send_line, gesture_end, gestures_end's key run *)
Lemma kf_sl_run : forall f mx no cap rem j o,
  kf_ch cap (fst (send_line_b_c.sl_run f mx no cap rem j o)) (fst (snd (send_line_b_c.sl_run f mx no cap rem j o))).
Proof.
  intros f. induction f as [|f IH]; intros mx no cap rem j o; cbn [send_line_b_c.sl_run].
  - cbn [fst snd]. apply kf_ch_nil.
  - destruct (rem <=? 0); [cbn [fst snd]; apply kf_ch_nil|].
    match goal with |- context [if ?b then mx else rem] => generalize (if b then mx else rem); intros n end.
    destruct (Z.ltb_spec cap (no + n)) as [Hl|Hl]; cbv beta iota; [|apply IH].
    cbn [fst snd].
    pose proof (IH mx (no + n) ((no + n) * 2) (rem - n) (S j) (RelayRunT.Ret j)) as I.
    destruct (Z.eqb_spec cap 0) as [E|E]; cbv beta iota.
    + apply kf_ch_malloc; [lia | exact I].
    + apply kf_ch_realloc; [lia | exact I].
Qed.

Lemma kf_send : forall live mx no cap len j o,
  kf_ch cap (send_line_b_c.send_line_tr live mx no cap len j o) (send_line_b_c.send_line_cap live mx no cap len).
Proof.
  intros live mx no cap len j o. unfold send_line_b_c.send_line_tr, send_line_b_c.send_line_cap.
  destruct live; [|apply kf_ch_nil].
  pose proof (kf_sl_run (Z.to_nat len) mx no cap len j o) as H.
  rewrite W_contract.sl_run_fin in H. rewrite W_contract.sl_run_fin. exact H.
Qed.

Lemma kf_gend : forall live mx no cap xl j o,
  kf_ch cap (gesture_end_b_c.gesture_end_tr live mx no cap xl j o) (gesture_end_b_c.gesture_end_cap live mx no cap xl).
Proof.
  intros live mx no cap xl j o. unfold gesture_end_b_c.gesture_end_tr, gesture_end_b_c.gesture_end_cap. cbv zeta.
  eapply kf_ch_app; apply kf_send.
Qed.

Lemma kf_ker : forall live mx xks no cap j o,
  kf_ch cap (fst (gestures_end_b_c.keys_end_run live mx no cap xks j o))
    (fst (snd (gestures_end_b_c.keys_end_run live mx no cap xks j o))).
Proof.
  intros live mx xks. induction xks as [|[xl ka] r IH]; intros no cap j o;
    cbn [gestures_end_b_c.keys_end_run fst snd]; [apply kf_ch_nil|].
  eapply kf_ch_app; [apply kf_gend|]. apply kf_ch_free_cons. apply IH.
Qed.

(* the key run's constant *)
Definition KC_ke : Z := 15.

Lemma kf_keys : forall live mx xks no cap j o,
  W_contract.tr_max (fst (gestures_end_b_c.keys_end_run live mx no cap xks j o)) <= 2 ^ 30 ->
  nsec_tr (fst (gestures_end_b_c.keys_end_run live mx no cap xks j o)) <= KC_ke.
Proof.
  intros live mx xks no cap j o HM. unfold KC_ke. rewrite <- kf_lg_2_30.
  exact (kf_ch_bound _ _ _ _ _ (kf_ker live mx xks no cap j o) HM).
Qed.

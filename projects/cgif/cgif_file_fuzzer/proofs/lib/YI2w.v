(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d YO03
YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Lemma rb_acc_00 : forall b, rb_le b (rb_acc b 0 0).
Proof. intros b. unfold rb_le, rb_acc. cbn. lia. Qed.
Lemma res_ok_acc0 : forall s b, res_ok s b -> res_ok s (rb_acc b 0 0).
Proof. intros s b H. eapply res_ok_mono; [apply rb_acc_00 | exact H]. Qed.
Lemma rb_malloc_acc_k : forall b k x n, 0 <= n -> rb_le (rb_malloc (rb_acc b k x) n) (rb_acc b (k + 1) (x + prN n)).
Proof. intros b k x n Hn. rewrite <- rb_acc_acc. apply rb_malloc_acc. exact Hn. Qed.
Lemma res_ok_malloc_acc : forall s b k x n, 0 <= n -> res_ok s (rb_malloc (rb_acc b k x) n) -> res_ok s (rb_acc b (k + 1) (x + prN n)).
Proof. intros s b k x n Hn H. eapply res_ok_mono; [apply rb_malloc_acc_k; exact Hn | exact H]. Qed.
Lemma res_ok_free_acc : forall s b k x n, res_ok s (rb_free (rb_acc b k x) n) -> res_ok s (rb_acc b k (x - prN n)).
Proof. intros s b k x n H. eapply res_ok_mono; [apply rb_free_acc | exact H]. Qed.
Lemma res_ok_malloc_to : forall s b k x n, res_ok s (rb_malloc (rb_acc b k x) n) ->
forall k' x', 0 <= n -> k' = k + 1 -> x' = x + prN n -> res_ok s (rb_acc b k' x').
Proof. intros s b k x n H k' x' Hn -> ->. apply res_ok_malloc_acc; assumption. Qed.
Lemma res_ok_free_to : forall s b k x n, res_ok s (rb_free (rb_acc b k x) n) -> forall x', x' = x - prN n -> res_ok s (rb_acc b k x').
Proof. intros s b k x n H x' ->. apply res_ok_free_acc; assumption. Qed.
Lemma res_ok_acc_le : forall s b k x k' x', 0 <= k <= k' -> x <= x' -> res_ok s (rb_acc b k x) -> res_ok s (rb_acc b k' x').
Proof. intros s b k x k' x' Hk Hx H. eapply res_ok_mono; [| exact H]. apply rb_acc_mono; [apply rb_le_refl | exact Hk | exact Hx]. Qed.
Lemma prN_small : forall n, n <= MMAP_THRESHOLD -> prN n = 0.
Proof. intros n Hn. unfold prN. destruct (Z.ltb_spec MMAP_THRESHOLD n); [lia | reflexivity]. Qed.
Lemma prN_le_lin : forall n, 0 <= n -> 0 <= prN n <= n + 4115.
Proof.
intros n Hn. unfold prN. destruct (MMAP_THRESHOLD <? n); [| lia].
pose proof (page_round_bounds (n + IB + UNIT) ltac:(unfold IB, UNIT; lia)). unfold IB, UNIT in *. lia.
Qed.
Lemma prN_le_pr : forall n m, 0 <= n -> n + 20 <= m -> prN n <= page_round m.
Proof.
intros n m Hn Hm. unfold prN. destruct (MMAP_THRESHOLD <? n).
- apply page_round_mono. unfold IB, UNIT. lia.
- pose proof (page_round_bounds m ltac:(lia)). lia.
Qed.
Lemma site_room_gen : forall b K PK MX k x n,
room (rb_acc b K PK) MX -> 0 <= k <= K -> x <= PK -> 0 <= n <= MX -> room (rb_acc b k x) n.
Proof.
intros b K PK MX k x n HR Hk Hx Hn. eapply room_mono; [| exact Hn | exact HR].
apply rb_acc_mono; [apply rb_le_refl | exact Hk | exact Hx].
Qed.
Definition lzw_x1 : Z := prN 72.
Definition lzw_x2 (idl : Z) : Z := lzw_x1 + prN (2 * idl * idl).
Definition lzw_x3 (idl : Z) : Z := lzw_x2 idl + prN 8192.
Definition lzw_x4 (idl : Z) : Z := lzw_x3 idl + prN 4096.
Definition lzw_x5 (idl : Z) : Z := lzw_x4 idl + prN 8192.
Definition lzw_x6 (idl : Z) : Z := lzw_x5 idl + prN (4098 * idl).
Definition lzw_x7 (idl nP : Z) : Z := lzw_x6 idl + prN (2 * (nP / (4094 - idl) + nP + 2)).
Definition lzw_rooms7 (b : rbound) (idl nP : Z) : Prop :=
room (rb_acc b 0 0) 72 /\
room (rb_acc b 1 lzw_x1) (2 * idl * idl) /\
room (rb_acc b 2 (lzw_x2 idl)) 8192 /\
room (rb_acc b 3 (lzw_x3 idl)) 4096 /\
room (rb_acc b 4 (lzw_x4 idl)) 8192 /\
room (rb_acc b 5 (lzw_x5 idl)) (4098 * idl) /\
room (rb_acc b 6 (lzw_x6 idl)) (2 * (nP / (4094 - idl) + nP + 2)).
Lemma maxres_le : forall idl nP, 2 <= idl <= 256 -> 1 <= nP <= 100000000 -> 0 <= nP / (4094 - idl) <= 26055.
Proof.
intros idl nP Hidl HnP. split; [apply Z.div_pos; lia|].
transitivity (nP / 3838); [apply Z.div_le_compat_l; lia|].
enough (nP / 3838 < 26056) by lia. apply Z.div_lt_upper_bound; lia.
Qed.
Lemma lzw_x6_le : forall idl, 2 <= idl <= 256 -> 0 <= lzw_x6 idl <= 2 ^ 21.
Proof.
intros idl Hidl. unfold lzw_x6, lzw_x5, lzw_x4, lzw_x3, lzw_x2, lzw_x1.
rewrite (prN_small 72), (prN_small 8192), (prN_small 4096) by (unfold MMAP_THRESHOLD; lia).
assert (H1 : 0 <= 2 * idl * idl <= 131072) by nia.
pose proof (prN_le_lin (2 * idl * idl) ltac:(lia)). pose proof (prN_le_lin (4098 * idl) ltac:(lia)). lia.
Qed.
Lemma lzw_x7_le : forall idl nP, 2 <= idl <= 256 -> 1 <= nP <= 100000000 ->
0 <= lzw_x7 idl nP <= 2 ^ 21 + page_round (2 * nP + 2 ^ 16).
Proof.
intros idl nP Hidl HnP. unfold lzw_x7. pose proof (lzw_x6_le idl Hidl). pose proof (maxres_le idl nP Hidl HnP).
pose proof (prN_le_pr (2 * (nP / (4094 - idl) + nP + 2)) (2 * nP + 2 ^ 16) ltac:(lia) ltac:(lia)).
pose proof (prN_nonneg (2 * (nP / (4094 - idl) + nP + 2)) ltac:(lia)). lia.
Qed.
Lemma lzw_rooms7_ok : forall b idl nP, 2 <= idl <= 256 -> 1 <= nP <= 100000000 -> lzw_room b nP -> lzw_rooms7 b idl nP.
Proof.
intros b idl nP Hidl HnP HR. unfold lzw_room, LZW_K, lzw_peak, lzw_maxreq in HR.
pose proof (page_round_bounds (2 * nP + 2 ^ 16) ltac:(lia)) as HPR.
pose proof (maxres_le idl nP Hidl HnP) as HMR.
assert (Hsq : 8 <= 2 * idl * idl <= 131072) by nia.
assert (X1 : lzw_x1 = 0) by (unfold lzw_x1; apply prN_small; unfold MMAP_THRESHOLD; lia).
pose proof (lzw_x6_le idl Hidl) as X6.
assert (XS : lzw_x1 <= lzw_x2 idl <= lzw_x3 idl /\ lzw_x3 idl <= lzw_x4 idl <= lzw_x5 idl /\ lzw_x5 idl <= lzw_x6 idl).
{ unfold lzw_x6, lzw_x5, lzw_x4, lzw_x3, lzw_x2.
pose proof (prN_nonneg (2 * idl * idl) ltac:(lia)). pose proof (prN_nonneg 8192 ltac:(lia)). pose proof (prN_nonneg 4096 ltac:(lia)).
pose proof (prN_nonneg (4098 * idl) ltac:(lia)). lia. }
unfold lzw_rooms7. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))); (eapply site_room_gen; [exact HR | lia | lia | lia]).
Qed.
Lemma lzw_epi_sizes : forall idl nP lp, 2 <= idl <= 256 -> 1 <= nP <= 100000000 -> 0 <= lp -> lp + 1 <= nP + 2 + nP / (4094 - idl) ->
0 <= 12 * (lp + 1) / 8 + 3 /\ 12 * (lp + 1) / 8 + 3 + 20 <= 2 * nP + 2 ^ 16 /\
0 <= 384 * (lp + 1) / 255 + 4 /\ 384 * (lp + 1) / 255 + 4 + 20 <= 2 * nP + 2 ^ 16.
Proof.
intros idl nP lp Hidl HnP Hlp Hcap. pose proof (maxres_le idl nP Hidl HnP) as HMR.
pose proof (Z.div_mod (12 * (lp + 1)) 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound (12 * (lp + 1)) 8 ltac:(lia)) as M8.
pose proof (Z.div_mod (384 * (lp + 1)) 255 ltac:(lia)) as D255. pose proof (Z.mod_pos_bound (384 * (lp + 1)) 255 ltac:(lia)) as M255.
set (q8 := 12 * (lp + 1) / 8) in *. set (q255 := 384 * (lp + 1) / 255) in *. clearbody q8 q255.
set (mr := nP / (4094 - idl)) in *. clearbody mr. lia.
Qed.
Lemma lzw_rooms_epi : forall b idl nP lp, 2 <= idl <= 256 -> 1 <= nP <= 100000000 -> lzw_room b nP ->
0 <= lp -> lp + 1 <= nP + 2 + nP / (4094 - idl) ->
room (rb_acc b 7 (lzw_x7 idl nP)) (12 * (lp + 1) / 8 + 3) /\
room (rb_acc b 8 (lzw_x7 idl nP + prN (12 * (lp + 1) / 8 + 3))) (384 * (lp + 1) / 255 + 4).
Proof.
intros b idl nP lp Hidl HnP HR Hlp Hcap. unfold lzw_room, LZW_K, lzw_peak, lzw_maxreq in HR.
pose proof (page_round_bounds (2 * nP + 2 ^ 16) ltac:(lia)) as HPR.
pose proof (lzw_x7_le idl nP Hidl HnP) as X7.
destruct (lzw_epi_sizes idl nP lp Hidl HnP Hlp Hcap) as (S1 & S2 & S3 & S4).
pose proof (prN_le_pr (12 * (lp + 1) / 8 + 3) (2 * nP + 2 ^ 16) S1 S2) as P1.
set (n1 := 12 * (lp + 1) / 8 + 3) in *. set (n2 := 384 * (lp + 1) / 255 + 4) in *. clearbody n1 n2.
split; (eapply site_room_gen; [exact HR | lia | lia | lia]).
Qed.
Lemma rb_free_acc' : forall X b k x n, rb_le X (rb_acc b k x) -> rb_le (rb_free X n) (rb_acc b k (x - prN n)).
Proof. intros X b k x n H. eapply rb_le_trans; [apply rb_free_mono; exact H | apply rb_free_acc]. Qed.
Lemma res_ok_free_below : forall s X b k x n, rb_le X (rb_acc b k x) -> res_ok s (rb_free X n) -> exists X', rb_le X' (rb_acc b k (x - prN n)) /\ res_ok s X'.
Proof. intros s X b k x n H HR. exists (rb_free X n). split; [apply rb_free_acc'; exact H | exact HR]. Qed.
Definition lzw_frees7 (X : rbound) (nld nti nlm nlc nli ntm : Z) : rbound :=
rb_free (rb_free (rb_free (rb_free (rb_free (rb_free (rb_free X nld) nti) nlm) nlc) nli) ntm) 72.
Lemma lzw_frees7_le : forall X b k x nld nti nlm nlc nli ntm,
rb_le X (rb_acc b k x) ->
rb_le (lzw_frees7 X nld nti nlm nlc nli ntm) (rb_acc b k (x - prN nld - prN nti - prN nlm - prN nlc - prN nli - prN ntm - prN 72)).
Proof.
intros X b k x nld nti nlm nlc nli ntm H. unfold lzw_frees7.
do 7 (apply rb_free_acc'). exact H.
Qed.
Lemma lzw_exit_eidx : forall s b idl nP X,
rb_le X (rb_acc b 7 (lzw_x7 idl nP)) ->
res_ok s (lzw_frees7 X (2 * (nP / (4094 - idl) + nP + 2)) (2 * idl * idl) 8192 4096 8192 (4098 * idl)) ->
res_ok s (lzw_rb b 0).
Proof.
intros s b idl nP X HX HR. unfold lzw_rb, LZW_K. eapply res_ok_mono; [| exact HR].
eapply rb_le_trans; [apply lzw_frees7_le; exact HX|].
apply rb_acc_mono; [apply rb_le_refl | lia |]. unfold lzw_x7, lzw_x6, lzw_x5, lzw_x4, lzw_x3, lzw_x2, lzw_x1. lia.
Qed.
Lemma lzw_exit_ok : forall s b idl nP n1 n2 X,
rb_le X (rb_acc b 9 (lzw_x7 idl nP + prN n1 + prN n2 - prN n1)) ->
res_ok s (lzw_frees7 X (2 * (nP / (4094 - idl) + nP + 2)) (2 * idl * idl) 8192 4096 8192 (4098 * idl)) ->
res_ok s (lzw_rb b (prN n2)).
Proof.
intros s b idl nP n1 n2 X HX HR. unfold lzw_rb, LZW_K. eapply res_ok_mono; [| exact HR].
eapply rb_le_trans; [apply lzw_frees7_le; exact HX|].
apply rb_acc_mono; [apply rb_le_refl | lia |]. unfold lzw_x7, lzw_x6, lzw_x5, lzw_x4, lzw_x3, lzw_x2, lzw_x1. lia.
Qed.
Lemma rawadd_room_il : forall b N, 1 <= N <= 100000000 -> rawadd_room b N -> room b N.
Proof.
intros b N HN HR. unfold rawadd_room, RAWADD_K, LZW_K, rawadd_peak, rawadd_maxreq, lzw_maxreq in HR.
pose proof (lzw_peak_le N ltac:(lia)). pose proof (prN_nonneg N ltac:(lia)).
eapply room_mono; [| | exact HR]; [| lia]. eapply rb_le_trans; [apply rb_acc_00|]. apply rb_acc_mono; [apply rb_le_refl | lia | lia].
Qed.
Lemma rawadd_room_lzw0 : forall b N, 1 <= N <= 100000000 -> rawadd_room b N -> lzw_room b N.
Proof.
intros b N HN HR. unfold rawadd_room, RAWADD_K, rawadd_peak, rawadd_maxreq in HR. unfold lzw_room.
pose proof (lzw_peak_le N ltac:(lia)). pose proof (prN_nonneg N ltac:(lia)).
eapply room_mono; [| | exact HR]; [| unfold lzw_maxreq; lia]. apply rb_acc_mono; [apply rb_le_refl | unfold LZW_K; lia | lia].
Qed.
Lemma rawadd_room_lzw1 : forall b N, 1 <= N <= 100000000 -> rawadd_room b N -> lzw_room (rb_acc b 1 (prN N)) N.
Proof.
intros b N HN HR. unfold rawadd_room, RAWADD_K, rawadd_peak, rawadd_maxreq in HR. unfold lzw_room. rewrite rb_acc_acc.
pose proof (lzw_peak_le N ltac:(lia)). pose proof (prN_nonneg N ltac:(lia)).
eapply room_mono; [| | exact HR]; [| unfold lzw_maxreq; lia]. apply rb_acc_mono; [apply rb_le_refl | unfold LZW_K; lia | lia].
Qed.
Lemma lzw_rb_acc1 : forall b N x, lzw_rb (rb_acc b 1 (prN N)) x = rb_acc b (1 + LZW_K) (prN N + x).
Proof. intros b N x. unfold lzw_rb. apply rb_acc_acc. Qed.
Lemma rawadd_exit : forall s b k x, 0 <= k <= RAWADD_K -> x <= 0 -> res_ok s (rb_acc b k x) -> res_ok s (rawadd_rb b).
Proof. intros s b k x Hk Hx H. unfold rawadd_rb. eapply res_ok_acc_le; [exact Hk | exact Hx | exact H]. Qed.

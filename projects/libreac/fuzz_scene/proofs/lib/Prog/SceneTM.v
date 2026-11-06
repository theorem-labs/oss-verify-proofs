From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneBlock.
Import ListNotations.
Open Scope Z_scope.

Definition scT_off (k : Z) : Z := if k =? 343 then 8904 else scene_off k.
Definition scT_src (k : Z) : Z := if k =? 0 then 9 else 7.

Definition scT_cks (b : list byte) (k : Z) : byte :=
  Z_to_bv 8 ((256 - byte_sum (scene_fields b k) mod 256) mod 256).

Ltac scT_ifs :=
  repeat match goal with |- context [if ?c then _ else _] =>
    let E := fresh "E" in destruct c eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]
  end; lia.

Lemma scT_skip7 : forall b k, skipn 7 (scene_block b k) = scene_payload b k ++ [scT_cks b k].
Proof. intros b k. reflexivity. Qed.

Lemma scT_pay0 : forall b, scene_payload b 0 = [Z_to_bv 8 0x22; Z_to_bv 8 0xc8] ++ firstn 24 b.
Proof. reflexivity. Qed.

Lemma scT_pay342 : forall b, scene_payload b 342 = firstn 14 (skipn (Z.to_nat (scene_off 342)) b) ++ scene_trailer.
Proof. reflexivity. Qed.

Lemma scT_payK : forall b k, k <> 0 -> k <> 342 -> scene_payload b k = firstn 26 (skipn (Z.to_nat (scene_off k)) b).
Proof.
  intros b k H0 H1. unfold scene_payload.
  rewrite (proj2 (Z.eqb_neq _ _) H0), (proj2 (Z.eqb_neq _ _) H1). reflexivity.
Qed.

Lemma scT_lenK : forall k, k <> 0 -> k <> 342 -> scene_len k = 26.
Proof. intros k H0 H1. unfold scene_len. rewrite (proj2 (Z.eqb_neq _ _) H0), (proj2 (Z.eqb_neq _ _) H1). reflexivity. Qed.

Lemma scT_firstn_app : forall (l1 l2 : list byte) n, n = length l1 -> firstn n (l1 ++ l2) = l1.
Proof. intros l1 l2 n ->. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn. apply app_nil_r. Qed.

Lemma scT_firstn_add : forall (l : list byte) n p, firstn n l ++ firstn p (skipn n l) = firstn (n + p) l.
Proof.
  induction l as [|x l IH]; intros n p.
  - rewrite skipn_nil, !firstn_nil. reflexivity.
  - destruct n as [|n]; [reflexivity|]. cbn. rewrite IH. reflexivity.
Qed.

Lemma scT_bnd : forall k, 0 <= k <= 342 ->
  0 <= scT_off k /\ scT_off k + scene_len k <= 8904 /\ 14 <= scene_len k <= 26.
Proof. intros k Hk. unfold scT_off, scene_off, scene_len. scT_ifs. Qed.

Lemma scT_off_step : forall k, 0 <= k <= 342 -> scT_off (k + 1) = scT_off k + scene_len k.
Proof. intros k Hk. unfold scT_off, scene_off, scene_len. scT_ifs. Qed.

Lemma scT_off_0 : scT_off 0 = 0.
Proof. reflexivity. Qed.

Lemma scT_off_343 : scT_off 343 = 8904.
Proof. reflexivity. Qed.

Lemma scT_piece : forall b k, length b = 8904%nat -> 0 <= k <= 342 ->
  firstn (Z.to_nat (scene_len k)) (skipn (Z.to_nat (scT_src k)) (scene_block b k)) =
  firstn (Z.to_nat (scene_len k)) (skipn (Z.to_nat (scT_off k)) b).
Proof.
  intros b k Hb Hk. change 8904%nat with (Z.to_nat 8904) in Hb.
  assert (E343 : (k =? 343) = false) by (apply Z.eqb_neq; lia).
  unfold scT_src, scT_off. rewrite E343.
  destruct (Z.eqb_spec k 0) as [->|H0].
  - change (Z.to_nat 9) with (2 + 7)%nat. rewrite <- skipn_skipn, scT_skip7, scT_pay0.
    change (Z.to_nat (scene_len 0)) with 24%nat. change (Z.to_nat (scene_off 0)) with 0%nat.
    cbn [app skipn]. apply scT_firstn_app. rewrite length_firstn, ?length_skipn. lia.
  - change (Z.to_nat 7) with 7%nat. rewrite scT_skip7.
    destruct (Z.eqb_spec k 342) as [->|H342].
    + rewrite scT_pay342. change (Z.to_nat (scene_len 342)) with 14%nat.
      rewrite <- app_assoc. apply scT_firstn_app.
      rewrite length_firstn, length_skipn. change (scene_off 342) with 8890. lia.
    + rewrite (scT_payK b k H0 H342), (scT_lenK k H0 H342). change (Z.to_nat 26) with 26%nat.
      apply scT_firstn_app. rewrite length_firstn, length_skipn. unfold scene_off.
      rewrite (proj2 (Z.eqb_neq _ _) H0), (proj2 (Z.eqb_neq _ _) H342). lia.
Qed.

Lemma scT_again_step : forall b k, length b = 8904%nat -> 0 <= k <= 342 ->
  firstn (Z.to_nat (scT_off k)) b ++ firstn (Z.to_nat (scene_len k)) (skipn (Z.to_nat (scT_src k)) (scene_block b k))
  = firstn (Z.to_nat (scT_off (k + 1))) b.
Proof.
  intros b k Hb Hk. rewrite (scT_piece b k Hb Hk), scT_firstn_add, (scT_off_step k Hk).
  pose proof (scT_bnd k Hk). f_equal. lia.
Qed.

Lemma scT_again_all : forall b : list byte, length b = 8904%nat -> firstn (Z.to_nat (scT_off 343)) b = b.
Proof. intros b Hb. apply firstn_all2. rewrite Hb, scT_off_343. change 8904%nat with (Z.to_nat 8904). lia. Qed.

Lemma scT_block_len : forall b k, length b = 8904%nat -> 0 <= k <= 342 -> length (scene_block b k) = 34%nat.
Proof.
  intros b k Hb Hk. change 8904%nat with (Z.to_nat 8904) in Hb.
  unfold scene_block, scene_fields. rewrite !length_app. cbn [length].
  destruct (Z.eqb_spec k 0) as [->|H0]; [rewrite scT_pay0, length_app, length_firstn; cbn [length]; lia|].
  destruct (Z.eqb_spec k 342) as [->|H342].
  - rewrite scT_pay342, length_app, length_firstn, length_skipn. change (scene_off 342) with 8890.
    unfold scene_trailer. rewrite length_map. cbn [length]. lia.
  - rewrite (scT_payK b k H0 H342), length_firstn, length_skipn. unfold scene_off.
    rewrite (proj2 (Z.eqb_neq _ _) H0), (proj2 (Z.eqb_neq _ _) H342). lia.
Qed.

Lemma scT_nth4 : forall b k, nth 4 (scene_block b k) (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof. reflexivity. Qed.

Lemma scT_nth5 : forall b k, nth 5 (scene_block b k) (Z_to_bv 8 0) = Z_to_bv 8 (scene_len k).
Proof. reflexivity. Qed.

Lemma scT_nth7_0 : forall b, nth 7 (scene_block b 0) (Z_to_bv 8 0) = Z_to_bv 8 0x22.
Proof. reflexivity. Qed.

Lemma scT_nth8_0 : forall b, nth 8 (scene_block b 0) (Z_to_bv 8 0) = Z_to_bv 8 0xc8.
Proof. reflexivity. Qed.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Bytes.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import Boxreg.
Import ListNotations.
Open Scope Z_scope.

Lemma list_ext_nth : forall {A} (l1 l2 : list A), (forall i, nth_error l1 i = nth_error l2 i) -> l1 = l2.
Proof.
  intros A l1. induction l1 as [|x l1 IH]; intros [|y l2] H.
  - reflexivity.
  - specialize (H O). discriminate.
  - specialize (H O). discriminate.
  - pose proof (H O) as H0. cbn in H0. injection H0 as ->. f_equal. apply IH. intros i. exact (H (S i)).
Qed.

Lemma nth_bsub : forall bs k n i, 0 <= k -> 0 <= n ->
  nth_error (bsub bs k n) i = if (i <? Z.to_nat n)%nat then nth_error bs (Z.to_nat k + i)%nat else None.
Proof.
  intros bs k n i Hk Hn. unfold bsub. rewrite nth_error_firstn.
  destruct (i <? Z.to_nat n)%nat; [|reflexivity]. rewrite nth_error_skipn. reflexivity.
Qed.

Lemma bsub_upd_out : forall cs k bs a n,
  0 <= a -> 0 <= n -> (k + length bs <= length cs)%nat -> a + n <= Z.of_nat (length cs) ->
  (a + n <= Z.of_nat k \/ Z.of_nat (k + length bs) <= a) ->
  bsub (upd_bytes cs k bs) a n = bsub cs a n.
Proof.
  intros cs k bs a n Ha Hn Hk Hl Hd. apply list_ext_nth. intros i.
  rewrite !nth_bsub by lia. destruct (Nat.ltb_spec i (Z.to_nat n)); [|reflexivity].
  rewrite upd_bytes_nth by lia.
  destruct (Nat.leb_spec k (Z.to_nat a + i)); destruct (Nat.ltb_spec (Z.to_nat a + i) (k + length bs));
    cbn [andb]; try reflexivity.
  exfalso; lia.
Qed.

Lemma bsub_upd_in : forall cs k bs o n,
  0 <= o -> 0 <= n -> (k + length bs <= length cs)%nat -> o + n <= Z.of_nat (length bs) ->
  bsub (upd_bytes cs k bs) (Z.of_nat k + o) n = bsub bs o n.
Proof.
  intros cs k bs o n Ho Hn Hk Hl. apply list_ext_nth. intros i.
  rewrite !nth_bsub by lia. destruct (Nat.ltb_spec i (Z.to_nat n)); [|reflexivity].
  rewrite upd_bytes_nth by lia.
  destruct (Nat.leb_spec k (Z.to_nat (Z.of_nat k + o) + i));
    destruct (Nat.ltb_spec (Z.to_nat (Z.of_nat k + o) + i) (k + length bs));
    cbn [andb]; try (exfalso; lia).
  f_equal. lia.
Qed.

Lemma bsub_app_r : forall (A B : list byte) o n, 0 <= o -> 0 <= n ->
  bsub (A ++ B) (Z.of_nat (length A) + o) n = bsub B o n.
Proof.
  intros A B o n Ho Hn. apply list_ext_nth. intros i. rewrite !nth_bsub by lia.
  destruct (i <? Z.to_nat n)%nat; [|reflexivity].
  rewrite nth_error_app2 by lia. f_equal. lia.
Qed.

Lemma bsub_app_l : forall (A B : list byte) o n, 0 <= o -> 0 <= n -> o + n <= Z.of_nat (length A) ->
  bsub (A ++ B) o n = bsub A o n.
Proof.
  intros A B o n Ho Hn H. apply list_ext_nth. intros i. rewrite !nth_bsub by lia.
  destruct (Nat.ltb_spec i (Z.to_nat n)); [|reflexivity].
  rewrite nth_error_app1 by lia. reflexivity.
Qed.

Lemma bsub_whole : forall (A : list byte) n, n = Z.of_nat (length A) -> bsub A 0 n = A.
Proof.
  intros A n ->. unfold bsub. change (Z.to_nat 0) with O. cbn [skipn]. rewrite Nat2Z.id. apply firstn_all.
Qed.

Lemma rd4_le4 : forall bs k z, -2^31 <= z < 2^31 -> bsub bs k 4 = le4 (Z_to_bv 64 z) -> rd4 bs k = z.
Proof.
  intros bs k z Hz H. unfold rd4. rewrite H, bytes_le_to_Z_le4, Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). change (2 ^ Z.of_N 32) with (2^32). change (2^32 / 2) with (2^31).
  Z.div_mod_to_equations. lia.
Qed.

Lemma In_zero_repeat : forall m, (0 < m)%nat -> In (Z_to_bv 8 0) (repeat (Z_to_bv 8 0) m).
Proof. intros [|m] H; [lia|]. left. reflexivity. Qed.

Section NewRow.
Variables (bs row : list byte).
Hypothesis HL : length bs = 288%nat.
Hypothesis Hn : 0 <= bx_n bs <= 4.
Hypothesis HR : length row = 56%nat.

Definition new_row_bytes : list byte :=
  upd_bytes (upd_bytes bs (Z.to_nat (56 * bx_n bs)) row) 280 (le4 (Z_to_bv 64 (bx_n bs + 1))).

Lemma new_row_len1 : length (upd_bytes bs (Z.to_nat (56 * bx_n bs)) row) = 288%nat.
Proof. rewrite upd_bytes_length; [exact HL|]. lia. Qed.

Lemma new_row_length : length new_row_bytes = 288%nat.
Proof.
  unfold new_row_bytes. rewrite upd_bytes_length; [exact new_row_len1|].
  rewrite new_row_len1, length_le4. lia.
Qed.

Lemma new_row_old : forall i o w, 0 <= i < bx_n bs -> 0 <= o -> 0 <= w -> o + w <= 56 ->
  bsub new_row_bytes (56 * i + o) w = bsub bs (56 * i + o) w.
Proof.
  intros i o w Hi Ho Hw Hs. unfold new_row_bytes.
  pose proof new_row_len1 as L1.
  rewrite bsub_upd_out; rewrite ?length_le4, ?L1; try lia.
  rewrite bsub_upd_out; rewrite ?HR, ?HL; try lia. reflexivity.
Qed.

Lemma new_row_new : forall o w, 0 <= o -> 0 <= w -> o + w <= 56 ->
  bsub new_row_bytes (56 * bx_n bs + o) w = bsub row o w.
Proof.
  intros o w Ho Hw Hs. unfold new_row_bytes.
  pose proof new_row_len1 as L1.
  rewrite bsub_upd_out; rewrite ?length_le4, ?L1; try lia.
  replace (56 * bx_n bs + o) with (Z.of_nat (Z.to_nat (56 * bx_n bs)) + o) by lia.
  apply bsub_upd_in; rewrite ?HR, ?HL; lia.
Qed.

Lemma new_row_n : bx_n new_row_bytes = bx_n bs + 1.
Proof.
  apply rd4_le4; [lia|]. unfold new_row_bytes.
  pose proof new_row_len1 as L1.
  replace 280 with (Z.of_nat 280 + 0) by reflexivity.
  rewrite bsub_upd_in; rewrite ?length_le4, ?L1; try lia.
  apply bsub_whole. rewrite length_le4. reflexivity.
Qed.

Lemma new_row_fabric : bx_fabric new_row_bytes = bx_fabric bs.
Proof.
  unfold bx_fabric, rd4. f_equal. f_equal. unfold new_row_bytes.
  pose proof new_row_len1 as L1.
  rewrite bsub_upd_out; rewrite ?length_le4, ?L1; try lia.
  rewrite bsub_upd_out; rewrite ?HR, ?HL; try lia. reflexivity.
Qed.

End NewRow.

Section Bind.
Variables (bs M : list byte) (z : Z).
Hypothesis HL : length bs = 288%nat.
Hypothesis Hz : 0 <= z <= 4.
Hypothesis HM : length M = 6%nat.

Definition bind_bytes : list byte := upd_bytes bs (Z.to_nat (56 * z)) M.

Lemma bind_length : length bind_bytes = 288%nat.
Proof. unfold bind_bytes. rewrite upd_bytes_length; [exact HL|]. lia. Qed.

Lemma bind_other : forall a w, 0 <= a -> 0 <= w -> a + w <= 288 -> (a + w <= 56 * z \/ 56 * z + 6 <= a) ->
  bsub bind_bytes a w = bsub bs a w.
Proof. intros a w Ha Hw Hs Hd. unfold bind_bytes. apply bsub_upd_out; rewrite ?HM, ?HL; lia. Qed.

Lemma bind_mac : bsub bind_bytes (56 * z) 6 = M.
Proof.
  unfold bind_bytes. assert (E : 56 * z = Z.of_nat (Z.to_nat (56 * z)) + 0) by lia. rewrite E at 2.
  rewrite bsub_upd_in; rewrite ?HM, ?HL; try lia. apply bsub_whole. rewrite HM. reflexivity.
Qed.

End Bind.

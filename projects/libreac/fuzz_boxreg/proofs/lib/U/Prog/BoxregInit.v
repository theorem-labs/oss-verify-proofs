From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Bytes.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import Boxreg reac_boxreg_init_c.
Import ListNotations.
Open Scope Z_scope.

Lemma clamp40_range : forall x, 1 <= clamp40 x <= 40.
Proof.
  intros x. unfold clamp40.
  destruct (Z.leb_spec 1 x), (Z.leb_spec x 40); cbn [andb]; lia.
Qed.

Lemma clamp40_in : forall x, 1 <= x <= 40 -> clamp40 x = x.
Proof.
  intros x H. unfold clamp40.
  destruct (Z.leb_spec 1 x), (Z.leb_spec x 40); cbn [andb]; lia.
Qed.

Lemma clamp40_out : forall x, ~ (1 <= x <= 40) -> clamp40 x = 40.
Proof.
  intros x H. unfold clamp40.
  destruct (Z.leb_spec 1 x), (Z.leb_spec x 40); cbn [andb]; lia.
Qed.

Lemma skipn_repeat_bx : forall (x : byte) n m, skipn n (repeat x m) = repeat x (m - n).
Proof.
  intros x n. induction n as [|n IH]; intros m; [ rewrite Nat.sub_0_r; reflexivity | ].
  destruct m as [|m]; [ reflexivity | ]. cbn [repeat skipn]. rewrite IH. reflexivity.
Qed.

Lemma init_bytes_length : forall f, length (init_bytes f) = 288%nat.
Proof. intros f. unfold init_bytes. rewrite length_app, repeat_length, length_le4. reflexivity. Qed.

Lemma init_bsub_n : forall f, bsub (init_bytes f) 280 4 = repeat (Z_to_bv 8 0) 4.
Proof.
  intros f. unfold bsub, init_bytes. change (Z.to_nat 280) with 280%nat. change (Z.to_nat 4) with 4%nat.
  rewrite skipn_app, repeat_length, skipn_repeat_bx.
  change (280 - 284)%nat with 0%nat. change (284 - 280)%nat with 4%nat. cbn [skipn].
  reflexivity.
Qed.

Lemma init_bsub_fabric : forall f, bsub (init_bytes f) 284 4 = le4 (Z_to_bv 64 f).
Proof.
  intros f. unfold bsub, init_bytes. change (Z.to_nat 284) with 284%nat. change (Z.to_nat 4) with 4%nat.
  rewrite skipn_app, repeat_length, skipn_repeat_bx.
  change (284 - 284)%nat with 0%nat. cbn [skipn repeat app].
  apply firstn_all2. rewrite length_le4. lia.
Qed.

Lemma init_bytes_n : forall f, bx_n (init_bytes f) = 0.
Proof. intros f. unfold bx_n, rd4. rewrite init_bsub_n. reflexivity. Qed.

Lemma init_bytes_fabric : forall f, 1 <= f <= 40 -> bx_fabric (init_bytes f) = f.
Proof.
  intros f Hf. unfold bx_fabric, rd4. rewrite init_bsub_fabric, bytes_le_to_Z_le4, unsigned_lit by lia.
  rewrite Z.mod_small by lia. apply bv_swrap_small. change (bv_half_modulus 32) with 2147483648. lia.
Qed.

Lemma init_bytes_inv : forall x,
  boxreg_inv (init_bytes (clamp40 x)) /\ bx_n (init_bytes (clamp40 x)) = 0 /\
  bx_fabric (init_bytes (clamp40 x)) = clamp40 x.
Proof.
  intros x. pose proof (clamp40_range x) as R.
  pose proof (init_bytes_n (clamp40 x)) as HN. pose proof (init_bytes_fabric (clamp40 x) R) as HF.
  split; [ | split; assumption ].
  unfold boxreg_inv, boxreg_B16, boxreg_B1, boxreg_B2, boxreg_B3, boxreg_B4, boxreg_B5, boxreg_B6, boxreg_B7.
  rewrite HN, HF, init_bytes_length.
  repeat split; try lia; intros; lia.
Qed.

(* lemmas for crt_m3.v (check_round_trip in fuzz_frame.ubsan, 0x133c4 .. 0x1344c): byte blocks in rw_cells, the bytes of the frame at buf, the loaded field registers, and the answer of diginet_frame_build when the frame is built. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac
  ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import diginet_frame_build_c.
Import ListNotations.
Open Scope Z_scope.

(** * Byte blocks *)

Lemma m3_rw_len : forall m A k bs, rw_cells rsegs m A [CB k bs] -> length bs = k.
Proof. intros m A k bs [[[Hl _] _] _]. exact Hl. Qed.

Lemma m3_rw_bytes : forall m A k bs, rw_cells rsegs m A [CB k bs] -> bytes_at rsegs m A bs.
Proof. intros m A k bs [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Lemma m3_cell_bytes : forall m A cs k c, rw_cells rsegs m A cs -> cell_at cs k = Some c ->
  bytes_at rsegs m (A + Z.of_nat k) (cbytes c).
Proof.
  intros m A cs k c [[Hwf Hb] _] Hc.
  destruct (cell_at_split _ _ _ c Hc) as (pre & post & Ecs & Hsz & _).
  rewrite Ecs in Hwf, Hb. apply cells_wf_app in Hwf. destruct Hwf as [Hwpre _].
  rewrite cells_bytes_app in Hb. cbn [cells_bytes] in Hb.
  apply bytes_at_app in Hb. destruct Hb as [_ Hb].
  rewrite cells_bytes_length in Hb by exact Hwpre. rewrite Hsz in Hb.
  apply bytes_at_app in Hb. exact (proj1 Hb).
Qed.

(** * The bytes of the frame at buf *)

Lemma m3_bytes_sub : forall m a l k n, bytes_at rsegs m a l -> (k <= length l)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m a l k n H Hk. rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn, Nat.min_l in H by exact Hk.
  rewrite <- (firstn_skipn n (skipn k l)) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma m3_dst_bytes : forall m buf b, bytes_at rsegs m buf b -> bytes_at rsegs m buf (fr_dst b).
Proof.
  intros m buf b H. pose proof (m3_bytes_sub m buf b 0 6 H (Nat.le_0_l _)) as S.
  cbn [skipn Z.of_nat] in S. rewrite Z.add_0_r in S. exact S.
Qed.

Lemma m3_src_bytes : forall m buf b, (6 <= length b)%nat -> bytes_at rsegs m buf b ->
  bytes_at rsegs m (buf + 6) (fr_src b).
Proof. intros m buf b L H. exact (m3_bytes_sub m buf b 6 6 H L). Qed.

Lemma m3_body_bytes : forall m buf b, fr_code b = 0 -> bytes_at rsegs m buf b ->
  bytes_at rsegs m (buf + 30) (fr_body b).
Proof.
  intros m buf b C H. destruct (fr_code_ok b C) as (L30 & _).
  exact (m3_bytes_sub m buf b 30 (Z.to_nat (fr_body_len b)) H L30).
Qed.

Lemma m3_len_dst : forall b, (6 <= length b)%nat -> length (fr_dst b) = 6%nat.
Proof. intros b L. unfold fr_dst. rewrite length_firstn. lia. Qed.

Lemma m3_len_src : forall b, (12 <= length b)%nat -> length (fr_src b) = 6%nat.
Proof. intros b L. unfold fr_src. rewrite length_firstn, length_skipn. lia. Qed.

(** * The registers that the loads of the spec_frame fields give *)

Lemma m3_zxb : forall z, 0 <= z < 2^8 -> zxb (b8 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zxb. f_equal. apply bz_b8. exact Hz. Qed.

Lemma m3_zx16 : forall z, 0 <= z < 2^16 -> zx16 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold zx16. rewrite unsigned_lit by lia. f_equal. apply Z.mod_small. lia.
Qed.

(** * diginet_frame_build when the frame is built *)

Lemma m3_build_code : forall bb, (Z.of_nat (length bb) <=? 1484) && negb (system_at bb) = true ->
  build_code bb (frame_len (length bb)) = frame_len (length bb).
Proof.
  intros bb H. apply andb_true_iff in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply negb_true_iff in H2.
  unfold build_code. replace (1484 <? Z.of_nat (length bb)) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite H2, Z.ltb_irrefl. reflexivity.
Qed.

Lemma m3_build_out : forall dmac smac send ack retry cmd ncmds bb x,
  (Z.of_nat (length bb) <=? 1484) && negb (system_at bb) = true ->
  build_out dmac smac send ack retry cmd ncmds bb 1 (repeat x (Z.to_nat (frame_len (length bb)))) =
  build_frame dmac smac send ack retry cmd ncmds bb true.
Proof.
  intros dmac smac send ack retry cmd ncmds bb x H. unfold build_out. cbv zeta. rewrite repeat_length.
  assert (F60 : 60 <= frame_len (length bb)) by (unfold frame_len; lia).
  rewrite Z2Nat.id by lia. rewrite (m3_build_code bb H).
  replace (0 <=? frame_len (length bb)) with true by (symmetry; apply Z.leb_le; lia).
  change (1 =? 1) with true.
  rewrite skipn_all2 by (rewrite repeat_length; lia). apply app_nil_r.
Qed.

Lemma m3_memcmp_self : forall l k, (k <= length l)%nat -> memcmp_model l l k = Some 0.
Proof.
  intros l k; revert l; induction k as [|k IH]; intros [|x l] H; cbn in *; try lia; try reflexivity.
  rewrite Z.eqb_refl. apply IH. lia.
Qed.

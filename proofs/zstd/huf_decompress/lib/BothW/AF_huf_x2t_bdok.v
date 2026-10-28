From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells ABase AF_huf_dec_iface AF_huf_x2t_hdefs.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Fixpoint x2_quads (l : list Z) : list deltX2 :=
  match l with a :: b :: c :: d :: r => mkX2 (a + 256 * b) c d :: x2_quads r | _ => [] end.

Lemma x2_z8_lo : forall a b, Z_to_bv 8 (a + 256 * b) = Z_to_bv 8 a.
Proof.
  intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256.
  replace (a + 256 * b) with (a + b * 256) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma x2_div_hi : forall a b, 0 <= a < 256 -> (a + 256 * b) / 256 = b.
Proof.
  intros a b Ha. replace (a + 256 * b) with (a + b * 256) by lia.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma x2_quads_bytes : forall n l, length l = (4 * n)%nat -> Forall (fun v : Z => 0 <= v < 256) l ->
  x2_bytes (x2_quads l) = map (Z_to_bv 8) l.
Proof.
  induction n as [|n IH]; intros l HL HB.
  - destruct l; [reflexivity| cbn in HL; lia].
  - destruct l as [|a [|b [|c [|d r]]]]; cbn [length] in HL; try lia.
    pose proof (Forall_inv HB) as Ha.
    apply Forall_inv_tail, Forall_inv_tail, Forall_inv_tail, Forall_inv_tail in HB.
    unfold x2_bytes in *. cbn [x2_quads map concat app x2_seq x2_nbBits x2_len].
    rewrite (IH r) by (auto; lia). rewrite x2_z8_lo, x2_div_hi by exact Ha. reflexivity.
Qed.

Lemma x2_quads_length : forall n l, length l = (4 * n)%nat -> length (x2_quads l) = n.
Proof.
  induction n as [|n IH]; intros l HL.
  - destruct l; [reflexivity| cbn in HL; lia].
  - destruct l as [|a [|b [|c [|d r]]]]; cbn [length] in HL; try lia.
    cbn [x2_quads length]. rewrite (IH r) by lia. reflexivity.
Qed.

Lemma x2_quads_nth : forall n l i, length l = (4 * n)%nat -> (i < n)%nat ->
  nth i (x2_quads l) x2_default =
  mkX2 (nth (4 * i) l 0 + 256 * nth (S (4 * i)) l 0) (nth (S (S (4 * i))) l 0) (nth (S (S (S (4 * i)))) l 0).
Proof.
  induction n as [|n IH]; intros l i HL Hi; [lia|].
  destruct l as [|a [|b [|c [|d r]]]]; cbn [length] in HL; try lia.
  destruct i as [|i]; [reflexivity|]. cbn [x2_quads nth]. rewrite (IH r i) by lia.
  replace (4 * S i)%nat with (S (S (S (S (4 * i))))) by lia. reflexivity.
Qed.

Section CANSEC1. Context {rc : runConstT}.

Lemma x2_dt_okB : forall m DT mtl T dt, 1 <= mtl <= 12 -> 1 <= T <= mtl ->
  x2pref T (2 ^ T) dt -> Znth 0 dt = mtl -> Znth 1 dt = 1 -> Znth 2 dt = T -> Znth 3 dt = mtl ->
  Z.of_nat (length dt) = 4 * (1 + 2 ^ mtl) -> Forall (fun v : Z => 0 <= v < 256) dt ->
  u8arr bsegs m DT (map (Z_to_bv 8) dt) -> huf_dt_okA m DT mtl.
Proof.
  intros m DT mtl T dt HM HT PC P0 P1 P2 P3 HL HB HU.
  assert (P2T : 2 ^ T <= 2 ^ mtl) by (apply Z.pow_le_mono_r; lia).
  assert (P2P : 0 < 2 ^ T) by (apply Z.pow_pos_nonneg; lia).
  assert (P2Q : 0 < 2 ^ mtl) by (apply Z.pow_pos_nonneg; lia).
  destruct dt as [|d0 [|d1 [|d2 [|d3 r]]]]; cbn [length] in HL; try lia.
  unfold Znth in P0, P1, P2, P3. change (Z.to_nat 0) with 0%nat in P0. change (Z.to_nat 1) with 1%nat in P1.
  change (Z.to_nat 2) with 2%nat in P2. change (Z.to_nat 3) with 3%nat in P3. cbn [nth] in P0, P1, P2, P3. subst d0 d1 d2 d3.
  apply Forall_inv_tail, Forall_inv_tail, Forall_inv_tail, Forall_inv_tail in HB.
  set (n := Z.to_nat (2 ^ mtl)).
  assert (HR : length r = (4 * n)%nat) by (unfold n; lia).
  destruct HU as [HB0 _].
  destruct (proj1 (bytes_at_app bsegs m DT [Z_to_bv 8 mtl; Z_to_bv 8 1; Z_to_bv 8 T; Z_to_bv 8 mtl] (map (Z_to_bv 8) r)) HB0)
    as [H4 HR4].
  change (Z.of_nat (length [Z_to_bv 8 mtl; Z_to_bv 8 1; Z_to_bv 8 T; Z_to_bv 8 mtl])) with 4 in HR4.
  rewrite <- (firstn_skipn (Z.to_nat (4 * 2 ^ T)) (map (Z_to_bv 8) r)) in HR4.
  destruct (proj1 (bytes_at_app bsegs m (DT + 4) _ _) HR4) as [HT4 _].
  exists 1, T. split.
  - exact H4.
  - right. split; [reflexivity|]. exists (x2_quads r).
    split; [rewrite (x2_quads_length n r HR); unfold n; lia|].
    split.
    + unfold x2_table_ok, HUF_TABLELOG_MAX. split; [lia|]. split.
      { unfold FseNCount.Zlength. rewrite (x2_quads_length n r HR). unfold n. lia. }
      intros i Hi. rewrite (x2_quads_nth n r (Z.to_nat i) HR) by (unfold n; lia).
      unfold x2_cell_ok. cbn [x2_seq x2_nbBits x2_len].
      assert (B0 := proj1 (Forall_nth _ r) HB (4 * Z.to_nat i)%nat 0 ltac:(lia)).
      assert (B1 := proj1 (Forall_nth _ r) HB (S (4 * Z.to_nat i)) 0 ltac:(lia)).
      cbn beta in B0, B1.
      destruct (PC i Hi) as [C6 C7]. unfold Znth in C6, C7.
      replace (Z.to_nat (4 * i + 6)) with (S (S (S (S (S (S (4 * Z.to_nat i))))))) in C6 by lia.
      replace (Z.to_nat (4 * i + 7)) with (S (S (S (S (S (S (S (4 * Z.to_nat i)))))))) in C7 by lia.
      cbn [nth] in C6, C7. split; [lia|]. split; assumption.
    + split; [lia|]. rewrite (x2_quads_bytes n r HR HB). exact HT4.
Qed.

End CANSEC1.

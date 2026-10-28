(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BLFrame BStep BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil BSegs BakeStackRep BsShadow BsConst BsIface BsCXXHeap.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition lb_own (LB : list block) (m : mem) : Prop :=
  Forall (fun b => wr_at asegs m (blk_addr b) (blk_size b)) LB.

Lemma lb_own_nil : forall m, lb_own [] m.
Proof. intros m. apply Forall_nil. Qed.

Lemma lb_own_cons : forall b LB m, wr_at asegs m (blk_addr b) (blk_size b) -> lb_own LB m -> lb_own (b :: LB) m.
Proof. intros b LB m H1 H2. apply Forall_cons; assumption. Qed.

Lemma lb_own_incl : forall LB LB' m, (forall b, In b LB' -> In b LB) -> lb_own LB m -> lb_own LB' m.
Proof.
  intros LB LB' m INC H0. unfold lb_own in *. rewrite Forall_forall in *. intros b Hb. apply H0, INC, Hb.
Qed.

Lemma lb_own_In : forall LB m b, lb_own LB m -> In b LB -> wr_at asegs m (blk_addr b) (blk_size b).
Proof. intros LB m b H0 Hb. unfold lb_own in H0. rewrite Forall_forall in H0. exact (H0 b Hb). Qed.

Lemma wr_at_wmono : forall m m' A n, wr_at asegs m A n -> wmono asegs m m' -> wr_at asegs m' A n.
Proof.
  intros m m' A n (H0 & H1 & HW) WM. split; [exact H0|]. split; [exact H1|]. intros i Hi. apply WM. apply HW. exact Hi.
Qed.

Lemma lb_own_wmono : forall LB m m', lb_own LB m -> wmono asegs m m' -> lb_own LB m'.
Proof.
  intros LB m m' H0 WM. unfold lb_own in *. eapply Forall_impl; [|exact H0]. intros b Hb.
  exact (wr_at_wmono _ _ _ _ Hb WM).
Qed.

Section Apres.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Lemma lb_own_apres : forall LB LB' SP m m',
    lb_own LB m -> apres H LB' SP m m' -> (forall b, In b LB -> In b LB') -> lb_own LB m'.
  Proof.
    intros LB LB' SP m m' H0 AP INC. unfold lb_own in *. rewrite Forall_forall in *. intros [[p A] n] Hb.
    cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in *.
    eapply (apres_wr_at H); [exact AP | exact (H0 _ Hb) |].
    eapply (aclient_range_block H); [exact (INC _ Hb) | apply Z.le_refl | apply Z.le_refl].
  Qed.
End Apres.

Lemma rw_cells_of_wr_hi : forall m A n, wr_at asegs m A n -> AIMG_TOP <= A -> 0 <= n ->
  exists bs, rw_cells asegs m A [CB (Z.to_nat n) bs].
Proof.
  intros m A n (W0 & W1 & WW) HA Hn.
  assert (DEF : forall i, 0 <= i < n -> exists b, m (wa (A + i)) = Some b).
  { intros i Hi. pose proof (WW i Hi) as Wi.
    rewrite (BakeStackRep.wview_high m (wa (A + i))) in Wi by (rewrite wa_unsigned by lia; lia).
    destruct (m (wa (A + i))) as [b|]; [exists b; reflexivity | contradiction]. }
  exists (map (fun i => match m (wa (A + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 (Z.to_nat n))).
  split.
  - split.
    + cbn [cells_wf cell_wf]. split; [|exact I]. rewrite length_map, length_seq. reflexivity.
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [rewrite length_map, length_seq; lia|].
      intros i Hi. rewrite length_map, length_seq in Hi.
      rewrite nth_error_map, nth_error_seq. rewrite (proj2 (Nat.ltb_lt _ _) Hi). cbn [option_map]. rewrite Nat.add_0_l.
      destruct (DEF (Z.of_nat i) ltac:(lia)) as (b & Eb). unfold mrd. rewrite Eb. reflexivity.
  - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. split; [exact W0|]. split; [exact W1|]. exact WW.
Qed.

Lemma rw_cells_of_own : forall LB m b, lb_own LB m -> In b LB -> AIMG_TOP <= blk_addr b -> 0 <= blk_size b ->
  exists bs, rw_cells asegs m (blk_addr b) [CB (Z.to_nat (blk_size b)) bs].
Proof. intros LB m b H0 Hb HA Hn. apply rw_cells_of_wr_hi; [exact (lb_own_In LB m b H0 Hb) | exact HA | exact Hn]. Qed.

Lemma own_of_rw_cells : forall m A n bs, rw_cells asegs m A [CB (Z.to_nat n) bs] -> 0 <= n -> wr_at asegs m A n.
Proof.
  intros m A n bs [_ W] Hn. cbn [cells_size csize] in W. rewrite Nat.add_0_r, Z2Nat.id in W by lia. exact W.
Qed.

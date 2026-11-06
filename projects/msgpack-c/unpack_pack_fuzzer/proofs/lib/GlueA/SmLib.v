(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs StepSoundBase StepSoundMem PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require MemFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require InitLib.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP StepB StepM PlanS CtrLib.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Section WithSegs.
Variable segs : list Segment.
Lemma ov_read_bytes_inv : forall m A n bs, ov_read_bytes segs m (Z_to_bv 64 A) n = Some bs ->
  0 <= A -> A + Z.of_nat n <= two64 ->
  length bs = n /\ forall i, 0 <= i < Z.of_nat n -> rb segs m (A + i) = nth_error bs (Z.to_nat i).
Proof.
  intros m A n. revert A. induction n as [|n IH]; intros A bs H HA HAn.
  - cbn in H. injection H as <-. split; [reflexivity | intros i Hi; lia].
  - cbn [ov_read_bytes] in H. rewrite <- rb_unfold in H.
    destruct (rb segs m A) as [b|] eqn:Hb; [|discriminate H].
    rewrite Z_to_bv_succ in H.
    destruct (ov_read_bytes segs m (Z_to_bv 64 (A + 1)) n) as [bs'|] eqn:Hr; [|discriminate H]. injection H as <-.
    destruct (IH (A + 1) bs' Hr ltac:(lia) ltac:(lia)) as [Hlen Hbs]. split; [cbn; lia|].
    intros i Hi. destruct (Z.eq_dec i 0) as [->|Hi0].
    + rewrite Z.add_0_r. cbn. exact Hb.
    + replace (A + i) with (A + 1 + (i - 1)) by lia. rewrite Hbs by lia.
      replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia. reflexivity.
Qed.

Lemma stored_is_loaded : forall (w : int) (x : word) bs, (to_Z w = 1 \/ to_Z w = 8) -> length bs = Z.to_nat (to_Z w) ->
  x = ext_word false 0 (to_Z w) (le_bytes_to_word bs) -> store_bytes w x = bs.
Proof.
  intros w x bs Hw Len ->.
  pose proof (MemFX.MemFX.Z_to_le_bytes_to_Z bs) as RT. pose proof (bytes_le_to_Z_bound bs) as BD.
  destruct Hw as [W1|W8].
  - assert (w = 1%uint63) by (apply Uint63.to_Z_inj; rewrite W1; reflexivity). subst w. change (to_Z 1%uint63) with 1 in *.
    change (Z.to_nat 1) with 1%nat in Len. destruct bs as [|b [|? ?]]; try discriminate Len. clear RT BD.
    rewrite <- (bytes_val_ext_word false 1 [b] eq_refl ltac:(lia)). unfold store_bytes, bytes_val.
    change (Z.to_nat (to_Z 1%uint63)) with 1%nat. cbn [Z_to_le_bytes]. f_equal.
    pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. cbn in Rb.
    assert (EB : bytes_le_to_Z [b] = bv_unsigned b) by (rewrite bytes_le_to_Z_cons; cbn; lia).
    rewrite EB, (ext_Z_small_id false 1 (bv_unsigned b)); [| lia| unfold two64; lia| change (2 ^ (8 * 1 - 0)) with 256; lia].
    apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite (bv_wrap_small 64 (bv_unsigned b)) by (rewrite bv_modulus_64; unfold W64.two64; lia).
    apply bv_wrap_small. unfold bv_modulus. cbn. lia.
  - assert (w = 8%uint63) by (apply Uint63.to_Z_inj; rewrite W8; reflexivity). subst w. change (to_Z 8%uint63) with 8 in *.
    rewrite <- store_bytes_64. rewrite <- RT at 2. rewrite Len. change (Z.to_nat 8) with 8%nat. f_equal.
    rewrite Len in BD. change (8 * Z.of_nat (Z.to_nat 8)) with 64 in BD.
    rewrite ext_word_id64. unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact BD.
Qed.

Lemma write_same : forall bs (m : word -> option byte) A, 0 <= A -> A + Z.of_nat (length bs) <= two64 ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> m (Z_to_bv 64 (A + i)) = nth_error bs (Z.to_nat i)) ->
  forall x, write_to_mem m (Z_to_bv 64 A) bs x = m x.
Proof.
  intros bs m A HA HB H x. pose proof (bv_unsigned_in_range _ x) as RX. unfold bv_modulus in RX.
  rewrite <- (Z_to_bv_bv_unsigned _ x).
  destruct (Z_lt_le_dec (bv_unsigned x) A) as [Q|Q]; [apply write_to_mem_frame; unfold two64 in *; lia|].
  destruct (Z_lt_le_dec (bv_unsigned x) (A + Z.of_nat (length bs))) as [Q2|Q2]; [| apply write_to_mem_frame; unfold two64 in *; lia].
  replace (bv_unsigned x) with (A + (bv_unsigned x - A)) by lia.
  rewrite write_to_mem_in by lia. symmetry. apply H. lia.
Qed.
End WithSegs.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem ALib.Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg ABase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Nia Cache. Unset Nra Cache.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.
Section Asan.
Context {rc : runConstT}.
Lemma no_seg_above : forall a, 0x62f000 <= a -> find_segment asegs a 1 = None.
Proof.
  intros a Ha. apply (InitLib.InitLib.find_segment_none asegs a 1 0x62f000); [vm_compute; reflexivity | exact Ha | lia].
Qed.

Lemma shmap_rb : forall m a, 0x62f000 <= a < 2 ^ 64 -> wb asegs m a = true -> rb asegs m a <> None.
Proof.
  intros m a Ha W. unfold wb, wview in W. unfold rb.
  destruct (m (Z_to_bv 64 a)) as [b|]; [discriminate|].
  rewrite Z_to_bv_unsigned, bv_wrap_small in W by (unfold bv_modulus; lia). rewrite (no_seg_above a (proj1 Ha)) in W. discriminate W.
Qed.

Lemma raw_of_view : forall (mm : amem) a b, 0x62f000 <= a < 2 ^ 64 -> St.rb asegs mm a = Some b -> mm (Z_to_bv 64 a) = Some b.
Proof.
  intros mm a b Ha H. unfold St.rb in H. destruct (mm (Z_to_bv 64 a)) as [b0|]; [exact H|]. exfalso. unfold St.rom_of in H.
  destruct (memory_read asegs (Z_to_bv 64 a) 1) as [[|b' l]|] eqn:MR; try discriminate H.
  destruct (MemP.memory_read_find_segment asegs a _ ltac:(unfold W64.two64; lia) MR) as [seg Hs].
  rewrite (no_seg_above a (proj1 Ha)) in Hs. discriminate Hs.
Qed.

Lemma ghost_c8 : forall (m' : amem) A cs k (v : word),
  AS.rw_cells asegs m' A cs -> cell_at cs k = Some (C8 v) -> 0x62f000 <= A ->
  forall x, write_to_mem m' (Z_to_bv 64 (A + Z.of_nat k)) (store_bytes 8%uint63 v) x = m' x.
Proof.
  intros m' A cs k v RW CA LOW.
  pose proof (AS.rw_cells_read asegs m' A cs k (C8 v) RW CA) as OV. cbn [csize cbytes] in OV.
  pose proof (AS.rw_cells_bound asegs m' A cs RW) as [B0 B1].
  assert (KB : Z.of_nat k + 8 <= Z.of_nat (cells_size cs)).
  { clear -CA. revert k CA. induction cs as [|c cs IH]; intros k CA; cbn [cell_at] in CA; [discriminate|].
    destruct (Nat.eqb k 0) eqn:K0.
    - apply Nat.eqb_eq in K0. subst k. injection CA as ->. cbn [cells_size csize]. lia.
    - destruct (Nat.ltb k (csize c)) eqn:LT; [discriminate|]. apply Nat.ltb_ge in LT. specialize (IH _ CA). cbn [cells_size]. lia. }
  unfold AM.wa in OV.
  destruct (ov_read_bytes_inv asegs m' (A + Z.of_nat k) 8 (AM.le8 v) OV ltac:(lia) ltac:(unfold two64; lia)) as [_ RB].
  assert (SB : store_bytes 8%uint63 v = AM.le8 v) by (rewrite <- OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundMem.StepM.store_bytes_64; apply AS.store_bytes_8').
  rewrite SB. apply write_same; [lia| rewrite AM.length_le8; unfold two64; lia|].
  rewrite AM.length_le8. intros i Hi. change (Z.of_nat 8) with 8 in *.
  pose proof (RB i Hi) as RBi.
  destruct (nth_error (AM.le8 v) (Z.to_nat i)) as [b|] eqn:NB; [| exfalso; apply nth_error_None in NB; rewrite AM.length_le8 in NB; lia].
  apply raw_of_view; [lia| exact RBi].
Qed.
End Asan.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundMem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP StepB StepM PlanS CtrLib.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Section WithSegs.
Variable segs : list Segment.
Lemma ov_read_bytes_inv : forall m A n bs, ov_read_bytes segs m (Z_to_bv 64 A) n = Some bs ->
  0 <= A -> A + Z.of_nat n <= two64 ->
  length bs = n /\ forall i, 0 <= i < Z.of_nat n -> rb segs m (A + i) = nth_error bs (Z.to_nat i).
Proof.
  intros m A n. revert A. induction n as [|n IH]; intros A bs H HA HAn.
  - cbn in H. injection H as <-. split; [reflexivity | intros i Hi; lia].
  - cbn [ov_read_bytes] in H. rewrite <- rb_unfold in H.
    destruct (rb segs m A) as [b|] eqn:Hb; [|discriminate H].
    rewrite Z_to_bv_succ in H.
    destruct (ov_read_bytes segs m (Z_to_bv 64 (A + 1)) n) as [bs'|] eqn:Hr; [|discriminate H]. injection H as <-.
    destruct (IH (A + 1) bs' Hr ltac:(lia) ltac:(lia)) as [Hlen Hbs]. split; [cbn; lia|].
    intros i Hi. destruct (Z.eq_dec i 0) as [->|Hi0].
    + rewrite Z.add_0_r. cbn. exact Hb.
    + replace (A + i) with (A + 1 + (i - 1)) by lia. rewrite Hbs by lia.
      replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia. reflexivity.
Qed.

Lemma stored_is_loaded : forall (w : int) (x : word) bs, (to_Z w = 1 \/ to_Z w = 8) -> length bs = Z.to_nat (to_Z w) ->
  x = ext_word false 0 (to_Z w) (le_bytes_to_word bs) -> store_bytes w x = bs.
Proof.
  intros w x bs Hw Len ->.
  pose proof (MemFX.MemFX.Z_to_le_bytes_to_Z bs) as RT. pose proof (bytes_le_to_Z_bound bs) as BD.
  destruct Hw as [W1|W8].
  - assert (w = 1%uint63) by (apply Uint63.to_Z_inj; rewrite W1; reflexivity). subst w. change (to_Z 1%uint63) with 1 in *.
    change (Z.to_nat 1) with 1%nat in Len. destruct bs as [|b [|? ?]]; try discriminate Len. clear RT BD.
    rewrite <- (bytes_val_ext_word false 1 [b] eq_refl ltac:(lia)). unfold store_bytes, bytes_val.
    change (Z.to_nat (to_Z 1%uint63)) with 1%nat. cbn [Z_to_le_bytes]. f_equal.
    pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. cbn in Rb.
    assert (EB : bytes_le_to_Z [b] = bv_unsigned b) by (rewrite bytes_le_to_Z_cons; cbn; lia).
    rewrite EB, (ext_Z_small_id false 1 (bv_unsigned b)); [| lia| unfold two64; lia| change (2 ^ (8 * 1 - 0)) with 256; lia].
    apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite (bv_wrap_small 64 (bv_unsigned b)) by (rewrite bv_modulus_64; unfold W64.two64; lia).
    apply bv_wrap_small. unfold bv_modulus. cbn. lia.
  - assert (w = 8%uint63) by (apply Uint63.to_Z_inj; rewrite W8; reflexivity). subst w. change (to_Z 8%uint63) with 8 in *.
    rewrite <- store_bytes_64. rewrite <- RT at 2. rewrite Len. change (Z.to_nat 8) with 8%nat. f_equal.
    rewrite Len in BD. change (8 * Z.of_nat (Z.to_nat 8)) with 64 in BD.
    rewrite ext_word_id64. unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact BD.
Qed.

Lemma write_same : forall bs (m : word -> option byte) A, 0 <= A -> A + Z.of_nat (length bs) <= two64 ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> m (Z_to_bv 64 (A + i)) = nth_error bs (Z.to_nat i)) ->
  forall x, write_to_mem m (Z_to_bv 64 A) bs x = m x.
Proof.
  intros bs m A HA HB H x. pose proof (bv_unsigned_in_range _ x) as RX. unfold bv_modulus in RX.
  rewrite <- (Z_to_bv_bv_unsigned _ x).
  destruct (Z_lt_le_dec (bv_unsigned x) A) as [Q|Q]; [apply write_to_mem_frame; unfold two64 in *; lia|].
  destruct (Z_lt_le_dec (bv_unsigned x) (A + Z.of_nat (length bs))) as [Q2|Q2]; [| apply write_to_mem_frame; unfold two64 in *; lia].
  replace (bv_unsigned x) with (A + (bv_unsigned x - A)) by lia.
  rewrite write_to_mem_in by lia. symmetry. apply H. lia.
Qed.
End WithSegs.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.

Import ABase.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Nia Cache. Unset Nra Cache.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.
Section Asan.
Context {rc : runConstT}.
Lemma no_seg_above : forall a, 0x631000 <= a -> find_segment bsegs a 1 = None.
Proof.
  intros a Ha. apply (InitLib.InitLib.find_segment_none bsegs a 1 0x631000); [vm_compute; reflexivity | exact Ha | lia].
Qed.

Lemma shmap_rb : forall m a, 0x631000 <= a < 2 ^ 64 -> wb bsegs m a = true -> rb bsegs m a <> None.
Proof.
  intros m a Ha W. unfold wb, wview in W. unfold rb.
  destruct (m (Z_to_bv 64 a)) as [b|]; [discriminate|].
  rewrite Z_to_bv_unsigned, bv_wrap_small in W by (unfold bv_modulus; lia). rewrite (no_seg_above a (proj1 Ha)) in W. discriminate W.
Qed.

Lemma raw_of_view : forall (mm : amem) a b, 0x631000 <= a < 2 ^ 64 -> St.rb bsegs mm a = Some b -> mm (Z_to_bv 64 a) = Some b.
Proof.
  intros mm a b Ha H. unfold St.rb in H. destruct (mm (Z_to_bv 64 a)) as [b0|]; [exact H|]. exfalso. unfold St.rom_of in H.
  destruct (memory_read bsegs (Z_to_bv 64 a) 1) as [[|b' l]|] eqn:MR; try discriminate H.
  destruct (MemP.memory_read_find_segment bsegs a _ ltac:(unfold W64.two64; lia) MR) as [seg Hs].
  rewrite (no_seg_above a (proj1 Ha)) in Hs. discriminate Hs.
Qed.

Lemma ghost_c8 : forall (m' : amem) A cs k (v : word),
  AS.rw_cells bsegs m' A cs -> cell_at cs k = Some (C8 v) -> 0x631000 <= A ->
  forall x, write_to_mem m' (Z_to_bv 64 (A + Z.of_nat k)) (store_bytes 8%uint63 v) x = m' x.
Proof.
  intros m' A cs k v RW CA LOW.
  pose proof (AS.rw_cells_read bsegs m' A cs k (C8 v) RW CA) as OV. cbn [csize cbytes] in OV.
  pose proof (AS.rw_cells_bound bsegs m' A cs RW) as [B0 B1].
  assert (KB : Z.of_nat k + 8 <= Z.of_nat (cells_size cs)).
  { clear -CA. revert k CA. induction cs as [|c cs IH]; intros k CA; cbn [cell_at] in CA; [discriminate|].
    destruct (Nat.eqb k 0) eqn:K0.
    - apply Nat.eqb_eq in K0. subst k. injection CA as ->. cbn [cells_size csize]. lia.
    - destruct (Nat.ltb k (csize c)) eqn:LT; [discriminate|]. apply Nat.ltb_ge in LT. specialize (IH _ CA). cbn [cells_size]. lia. }
  unfold AM.wa in OV.
  destruct (ov_read_bytes_inv bsegs m' (A + Z.of_nat k) 8 (AM.le8 v) OV ltac:(lia) ltac:(unfold two64; lia)) as [_ RB].
  assert (SB : store_bytes 8%uint63 v = AM.le8 v) by (rewrite <- OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundMem.StepM.store_bytes_64; apply AS.store_bytes_8').
  rewrite SB. apply write_same; [lia| rewrite AM.length_le8; unfold two64; lia|].
  rewrite AM.length_le8. intros i Hi. change (Z.of_nat 8) with 8 in *.
  pose proof (RB i Hi) as RBi.
  destruct (nth_error (AM.le8 v) (Z.to_nat i)) as [b|] eqn:NB; [| exfalso; apply nth_error_None in NB; rewrite AM.length_le8 in NB; lia].
  apply raw_of_view; [lia| exact RBi].
Qed.
End Asan.
End TwinB.

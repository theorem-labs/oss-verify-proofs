(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs StepSoundBase StepSoundMem PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Mem Frame Cells Step.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP StepB StepM PlanS.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Module AC := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.

Module FxOut.
Section WithSegs.
Variable segs : list Segment.
Variable OPS : optable.

Lemma rb_mrdA : forall m a, rb segs m a = AM.mrd segs m (AM.wa a).
Proof. reflexivity. Qed.

Lemma Z_to_bv_succ64 : forall A, (Z_to_bv 64 A + 1)%bv = Z_to_bv 64 (A + 1).
Proof. intros A. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. change (bv_unsigned 1%bv) with 1. unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity. Qed.

Lemma ov_read_bytes_inv : forall m A n bs, ov_read_bytes segs m (Z_to_bv 64 A) n = Some bs ->
  length bs = n /\ forall i, 0 <= i < Z.of_nat n -> rb segs m (A + i) = nth_error bs (Z.to_nat i).
Proof.
  intros m A n. revert A. induction n as [|n IH]; intros A bs H.
  - cbn in H. injection H as <-. split; [reflexivity | intros i Hi; lia].
  - cbn [ov_read_bytes] in H. rewrite <- rb_unfold in H.
    destruct (rb segs m A) as [b|] eqn:Hb; [|discriminate H].
    rewrite Z_to_bv_succ64 in H.
    destruct (ov_read_bytes segs m (Z_to_bv 64 (A + 1)) n) as [bs'|] eqn:Hr; [|discriminate H]. injection H as <-.
    destruct (IH (A + 1) bs' Hr) as [Hlen Hbs]. split; [cbn; lia|].
    intros i Hi. destruct (Z.eq_dec i 0) as [->|Hi0].
    + rewrite Z.add_0_r. cbn. exact Hb.
    + replace (A + i) with (A + 1 + (i - 1)) by lia. rewrite Hbs by lia.
      replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia. reflexivity.
Qed.

Lemma bytes_at_of_ov : forall m A n bs, 0 <= A -> A + Z.of_nat n <= 2 ^ 64 ->
  ov_read_bytes segs m (Z_to_bv 64 A) n = Some bs -> AM.bytes_at segs m A bs.
Proof.
  intros m A n bs HA HB H. destruct (ov_read_bytes_inv m A n bs H) as [L P]. subst n.
  split; [lia|]. split; [lia|]. intros i Hi. rewrite <- rb_mrdA. rewrite (P (Z.of_nat i)) by lia. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma Z_to_le_bytes_to_Z : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes]. rewrite bytes_le_to_Z_cons. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R.
    pose proof (bytes_le_to_Z_nonneg bs) as NN.
    unfold bv_wrap. replace (bv_modulus 8) with 256 by reflexivity.
    rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. pose proof (bytes_le_to_Z_nonneg bs) as NN.
    rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia. rewrite Z.div_small by lia. rewrite Z.add_0_r. exact IH.
Qed.

Lemma bytes_val_false_eq : forall n bs, length bs = n -> (1 <= n <= 8)%nat ->
  bv_unsigned (bytes_val false (Z.of_nat n) bs) = bytes_le_to_Z bs.
Proof.
  intros n bs Hl Hn. unfold bytes_val. rewrite Z_to_bv_unsigned.
  pose proof (bytes_le_to_Z_bound bs) as B. rewrite Hl in B.
  assert (P : 2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  rewrite (ext_Z_small_id false (Z.of_nat n) (bytes_le_to_Z bs)).
  1:{ apply bv_wrap_small. rewrite bv_modulus_64, two64_eq. lia. }
  1:{ lia. }
  1:{ rewrite two64_eq. lia. }
  rewrite Z.sub_0_r. exact B.
Qed.

Lemma load8_bytes : forall E bs v, length bs = 8%nat -> den E v = bytes_val false 8 bs -> bs = AM.le8 (den E v).
Proof.
  intros E bs v Hl H. unfold AM.le8, word_to_le_bytes.
  pose proof (bytes_val_false_eq 8 bs Hl ltac:(lia)) as Q. change (Z.of_nat 8) with 8 in Q. rewrite H, Q, <- Hl.
  symmetry. apply Z_to_le_bytes_to_Z.
Qed.

Lemma wok1 : wok 1%uint63. Proof. left. reflexivity. Qed.
Lemma wok8 : wok 8%uint63. Proof. right; right; right. reflexivity. Qed.

Definition slot_ok (st : sstate) (a v : sv) : bool :=
  match do_load segs st a 8%uint63 false with inl (Some v') => sv_eqb v' v | _ => false end.

Lemma slot_ok_sound : forall E st ms mo a v A,
  st_ok segs OPS E st ms mo -> slot_ok st a v = true -> bv_unsigned (den E a) = A -> A + 8 <= 2 ^ 64 ->
  AM.bytes_at segs (ms_mem ms) A (AM.le8 (den E v)).
Proof.
  intros E st ms mo a v A HS H HA HB. unfold slot_ok in H.
  destruct (do_load segs st a 8%uint63 false) as [[v'|]|] eqn:D; try discriminate H.
  apply sv_eqb_eq in H. subst v'.
  destruct (do_load_sound segs OPS E st ms mo a 8%uint63 false v HS wok8 D) as (bs & L & R & Dv).
  change (Z.to_nat (to_Z 8%uint63)) with 8%nat in L, R. change (to_Z 8%uint63) with 8 in Dv.
  rewrite <- (bytes_val_ext_word false 8 bs L ltac:(lia)) in Dv.
  rewrite (load8_bytes E bs v L Dv) in R.
  pose proof (bv_unsigned_in_range 64 (den E a)) as RA.
  apply (bytes_at_of_ov (ms_mem ms) A 8); [lia| lia|].
  rewrite <- HA, Z_to_bv_bv_unsigned. exact R.
Qed.

Definition byte_lit (st : sstate) (a : sv) : option Z :=
  match do_load segs st a 1%uint63 false with inl (Some (VL z)) => Some (w2Z z) | _ => None end.

Lemma byte_lit_sound : forall E st ms mo a z,
  st_ok segs OPS E st ms mo -> byte_lit st a = Some z ->
  rb segs (ms_mem ms) (bv_unsigned (den E a)) = Some (Z_to_bv 8 z) /\ 0 <= z < 256.
Proof.
  intros E st ms mo a z0 HS H. unfold byte_lit in H.
  destruct (do_load segs st a 1%uint63 false) as [[v|]|] eqn:DL; try discriminate H.
  destruct v as [z| | | | | | | | | |]; try discriminate H. injection H as <-.
  destruct (do_load_sound segs OPS E st ms mo a 1%uint63 false (VL z) HS wok1 DL) as (bs & Len & OV & Dv).
  change (Z.to_nat (to_Z 1%uint63)) with 1%nat in Len, OV. change (to_Z 1%uint63) with 1 in Dv.
  destruct bs as [|b [|]]; try discriminate Len.
  assert (RB : rb segs (ms_mem ms) (bv_unsigned (den E a)) = Some b).
  { rewrite rb_unfold, Z_to_bv_bv_unsigned. cbn [ov_read_bytes] in OV.
    destruct (match ms_mem ms (den E a) with Some b0 => Some b0 | None => match memory_read segs (den E a) 1 with Some (b0 :: _) => Some b0 | _ => None end end) as [b0|]; [|discriminate OV].
    cbn in OV. injection OV as <-. reflexivity. }
  pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
  assert (EZ : w2Z z = bv_unsigned b).
  { rewrite <- (bytes_val_ext_word false 1 [b] eq_refl ltac:(lia)) in Dv. unfold bytes_val in Dv. cbn [den] in Dv. unfold wbv in Dv.
    assert (EB : bytes_le_to_Z [b] = bv_unsigned b) by (rewrite bytes_le_to_Z_cons; cbn; lia).
    rewrite EB, (ext_Z_small_id false 1 (bv_unsigned b)) in Dv; [| lia| unfold two64; lia| change (2 ^ (8 * 1 - 0)) with 256; lia].
    apply (f_equal bv_unsigned) in Dv. rewrite !Z_to_bv_unsigned in Dv.
    pose proof (w2Z_range z) as RZ.
    rewrite (bv_wrap_small 64 (w2Z z)) in Dv by (rewrite bv_modulus_64; exact RZ).
    rewrite (bv_wrap_small 64 (bv_unsigned b)) in Dv by (rewrite bv_modulus_64; unfold two64; lia). exact Dv. }
  rewrite EZ. split; [| lia]. rewrite RB. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Definition text_ok (st : sstate) (k : int) (off : Z) (len : nat) : bool :=
  forallb (fun i => match byte_lit st (VP k (Z2w (off + Z.of_nat i))) with Some z => negb (z =? 0) | None => false end) (seq 0 len)
  && match byte_lit st (VP k (Z2w (off + Z.of_nat len))) with Some z => z =? 0 | None => false end.

Lemma w2Zs_Z2w : forall z, - two63 <= z < two63 -> w2Zs (Z2w z) = z.
Proof.
  intros z Hz. rewrite <- w2Zs_swrap, Z2w_ok. unfold bv_swrap, bv_wrap. rewrite bv_modulus_64, bv_half_modulus_64.
  unfold two63, two64 in *. rewrite Zplus_mod_idemp_l. rewrite Z.mod_small by lia. lia.
Qed.

Lemma den_VP_Z2w : forall E k z, - two63 <= z < two63 -> 0 <= bv_unsigned (ev E k) + z < two64 ->
  bv_unsigned (den E (VP k (Z2w z))) = bv_unsigned (ev E k) + z.
Proof. intros E k z Hz HR. rewrite den_VP, (w2Zs_Z2w z Hz). apply Z.mod_small. exact HR. Qed.

Lemma bytes_of_pointwise : forall (P : byte -> Prop) m A n,
  (forall j, 0 <= j < Z.of_nat n -> exists b, rb segs m (A + j) = Some b /\ P b) ->
  exists bs, length bs = n /\ Forall P bs /\ forall j, 0 <= j < Z.of_nat n -> rb segs m (A + j) = nth_error bs (Z.to_nat j).
Proof.
  intros P m A n. induction n as [|n IH]; intros H.
  - exists []. split; [reflexivity|]. split; [constructor|]. intros j Hj. lia.
  - destruct IH as (bs & L & FA & PW). { intros j Hj. apply H. lia. }
    destruct (H (Z.of_nat n) ltac:(lia)) as (b & RB & Pb).
    exists (bs ++ [b]). split; [rewrite length_app; cbn; lia|]. split; [apply Forall_app; split; [exact FA| constructor; [exact Pb| constructor]]|].
    intros j Hj. destruct (Z.eq_dec j (Z.of_nat n)) as [->|NE].
    + rewrite Nat2Z.id, nth_error_app2 by lia. rewrite L, Nat.sub_diag. exact RB.
    + rewrite nth_error_app1 by lia. apply PW. lia.
Qed.

Lemma text_ok_sound : forall E st ms mo k off len,
  st_ok segs OPS E st ms mo -> text_ok st k off len = true ->
  - two63 <= off -> off + Z.of_nat len < two63 -> 0 <= bv_unsigned (ev E k) + off -> bv_unsigned (ev E k) + off + Z.of_nat len < two64 ->
  exists str, length str = len /\ Forall (fun b : byte => bv_unsigned b <> 0) str
    /\ AM.bytes_at segs (ms_mem ms) (bv_unsigned (ev E k) + off) (str ++ [Z_to_bv 8 0]).
Proof.
  intros E st ms mo k off len HS H O1 O2 A1 A2. unfold text_ok in H. apply andb_prop in H as [HT HZ].
  set (A := bv_unsigned (ev E k) + off) in *.
  assert (PW : forall j, 0 <= j < Z.of_nat len -> exists b, rb segs (ms_mem ms) (A + j) = Some b /\ bv_unsigned b <> 0).
  { intros j Hj. rewrite forallb_forall in HT. specialize (HT (Z.to_nat j) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in HT by lia.
    destruct (byte_lit st (VP k (Z2w (off + j)))) as [z|] eqn:BL; [|discriminate HT].
    destruct (byte_lit_sound E st ms mo _ z HS BL) as [RB RZ]. rewrite (den_VP_Z2w E k (off + j)) in RB by (unfold two64 in *; lia).
    exists (Z_to_bv 8 z). split; [unfold A; rewrite <- Z.add_assoc; exact RB|].
    rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 8) with 256; lia).
    destruct (Z.eqb_spec z 0); [discriminate HT| assumption]. }
  destruct (bytes_of_pointwise (fun b => bv_unsigned b <> 0) (ms_mem ms) A len PW) as (str & L & FA & PW2).
  exists str. split; [exact L|]. split; [exact FA|].
  destruct (byte_lit st (VP k (Z2w (off + Z.of_nat len)))) as [z|] eqn:BL; [|discriminate HZ].
  apply Z.eqb_eq in HZ. subst z.
  destruct (byte_lit_sound E st ms mo _ 0 HS BL) as [RB _]. rewrite (den_VP_Z2w E k (off + Z.of_nat len)) in RB by (unfold two64 in *; lia).
  split; [unfold A; lia|]. split; [rewrite length_app, L; cbn [length]; unfold A, two64 in *; lia|].
  intros i Hi. rewrite length_app, L in Hi. cbn [length] in Hi. rewrite <- rb_mrdA.
  destruct (Nat.eq_dec i len) as [->|NE].
  - rewrite nth_error_app2 by lia. rewrite L, Nat.sub_diag. cbn [nth_error]. unfold A. rewrite <- Z.add_assoc. exact RB.
  - rewrite nth_error_app1 by lia. rewrite (PW2 (Z.of_nat i)) by lia. rewrite Nat2Z.id. reflexivity.
Qed.

End WithSegs.
End FxOut.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundMem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP StepB StepM PlanS.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Module AC := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.

Module FxOut.
Section WithSegs.
Variable segs : list Segment.
Variable OPS : optable.

Lemma rb_mrdA : forall m a, rb segs m a = AM.mrd segs m (AM.wa a).
Proof. reflexivity. Qed.

Lemma Z_to_bv_succ64 : forall A, (Z_to_bv 64 A + 1)%bv = Z_to_bv 64 (A + 1).
Proof. intros A. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. change (bv_unsigned 1%bv) with 1. unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity. Qed.

Lemma ov_read_bytes_inv : forall m A n bs, ov_read_bytes segs m (Z_to_bv 64 A) n = Some bs ->
  length bs = n /\ forall i, 0 <= i < Z.of_nat n -> rb segs m (A + i) = nth_error bs (Z.to_nat i).
Proof.
  intros m A n. revert A. induction n as [|n IH]; intros A bs H.
  - cbn in H. injection H as <-. split; [reflexivity | intros i Hi; lia].
  - cbn [ov_read_bytes] in H. rewrite <- rb_unfold in H.
    destruct (rb segs m A) as [b|] eqn:Hb; [|discriminate H].
    rewrite Z_to_bv_succ64 in H.
    destruct (ov_read_bytes segs m (Z_to_bv 64 (A + 1)) n) as [bs'|] eqn:Hr; [|discriminate H]. injection H as <-.
    destruct (IH (A + 1) bs' Hr) as [Hlen Hbs]. split; [cbn; lia|].
    intros i Hi. destruct (Z.eq_dec i 0) as [->|Hi0].
    + rewrite Z.add_0_r. cbn. exact Hb.
    + replace (A + i) with (A + 1 + (i - 1)) by lia. rewrite Hbs by lia.
      replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia. reflexivity.
Qed.

Lemma bytes_at_of_ov : forall m A n bs, 0 <= A -> A + Z.of_nat n <= 2 ^ 64 ->
  ov_read_bytes segs m (Z_to_bv 64 A) n = Some bs -> AM.bytes_at segs m A bs.
Proof.
  intros m A n bs HA HB H. destruct (ov_read_bytes_inv m A n bs H) as [L P]. subst n.
  split; [lia|]. split; [lia|]. intros i Hi. rewrite <- rb_mrdA. rewrite (P (Z.of_nat i)) by lia. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma Z_to_le_bytes_to_Z : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes]. rewrite bytes_le_to_Z_cons. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R.
    pose proof (bytes_le_to_Z_nonneg bs) as NN.
    unfold bv_wrap. replace (bv_modulus 8) with 256 by reflexivity.
    rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. pose proof (bytes_le_to_Z_nonneg bs) as NN.
    rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia. rewrite Z.div_small by lia. rewrite Z.add_0_r. exact IH.
Qed.

Lemma bytes_val_false_eq : forall n bs, length bs = n -> (1 <= n <= 8)%nat ->
  bv_unsigned (bytes_val false (Z.of_nat n) bs) = bytes_le_to_Z bs.
Proof.
  intros n bs Hl Hn. unfold bytes_val. rewrite Z_to_bv_unsigned.
  pose proof (bytes_le_to_Z_bound bs) as B. rewrite Hl in B.
  assert (P : 2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  rewrite (ext_Z_small_id false (Z.of_nat n) (bytes_le_to_Z bs)).
  1:{ apply bv_wrap_small. rewrite bv_modulus_64, two64_eq. lia. }
  1:{ lia. }
  1:{ rewrite two64_eq. lia. }
  rewrite Z.sub_0_r. exact B.
Qed.

Lemma load8_bytes : forall E bs v, length bs = 8%nat -> den E v = bytes_val false 8 bs -> bs = AM.le8 (den E v).
Proof.
  intros E bs v Hl H. unfold AM.le8, word_to_le_bytes.
  pose proof (bytes_val_false_eq 8 bs Hl ltac:(lia)) as Q. change (Z.of_nat 8) with 8 in Q. rewrite H, Q, <- Hl.
  symmetry. apply Z_to_le_bytes_to_Z.
Qed.

Lemma wok1 : wok 1%uint63. Proof. left. reflexivity. Qed.
Lemma wok8 : wok 8%uint63. Proof. right; right; right. reflexivity. Qed.

Definition slot_ok (st : sstate) (a v : sv) : bool :=
  match do_load segs st a 8%uint63 false with inl (Some v') => sv_eqb v' v | _ => false end.

Lemma slot_ok_sound : forall E st ms mo a v A,
  st_ok segs OPS E st ms mo -> slot_ok st a v = true -> bv_unsigned (den E a) = A -> A + 8 <= 2 ^ 64 ->
  AM.bytes_at segs (ms_mem ms) A (AM.le8 (den E v)).
Proof.
  intros E st ms mo a v A HS H HA HB. unfold slot_ok in H.
  destruct (do_load segs st a 8%uint63 false) as [[v'|]|] eqn:D; try discriminate H.
  apply sv_eqb_eq in H. subst v'.
  destruct (do_load_sound segs OPS E st ms mo a 8%uint63 false v HS wok8 D) as (bs & L & R & Dv).
  change (Z.to_nat (to_Z 8%uint63)) with 8%nat in L, R. change (to_Z 8%uint63) with 8 in Dv.
  rewrite <- (bytes_val_ext_word false 8 bs L ltac:(lia)) in Dv.
  rewrite (load8_bytes E bs v L Dv) in R.
  pose proof (bv_unsigned_in_range 64 (den E a)) as RA.
  apply (bytes_at_of_ov (ms_mem ms) A 8); [lia| lia|].
  rewrite <- HA, Z_to_bv_bv_unsigned. exact R.
Qed.

Definition byte_lit (st : sstate) (a : sv) : option Z :=
  match do_load segs st a 1%uint63 false with inl (Some (VL z)) => Some (w2Z z) | _ => None end.

Lemma byte_lit_sound : forall E st ms mo a z,
  st_ok segs OPS E st ms mo -> byte_lit st a = Some z ->
  rb segs (ms_mem ms) (bv_unsigned (den E a)) = Some (Z_to_bv 8 z) /\ 0 <= z < 256.
Proof.
  intros E st ms mo a z0 HS H. unfold byte_lit in H.
  destruct (do_load segs st a 1%uint63 false) as [[v|]|] eqn:DL; try discriminate H.
  destruct v as [z| | | | | | | | | |]; try discriminate H. injection H as <-.
  destruct (do_load_sound segs OPS E st ms mo a 1%uint63 false (VL z) HS wok1 DL) as (bs & Len & OV & Dv).
  change (Z.to_nat (to_Z 1%uint63)) with 1%nat in Len, OV. change (to_Z 1%uint63) with 1 in Dv.
  destruct bs as [|b [|]]; try discriminate Len.
  assert (RB : rb segs (ms_mem ms) (bv_unsigned (den E a)) = Some b).
  { rewrite rb_unfold, Z_to_bv_bv_unsigned. cbn [ov_read_bytes] in OV.
    destruct (match ms_mem ms (den E a) with Some b0 => Some b0 | None => match memory_read segs (den E a) 1 with Some (b0 :: _) => Some b0 | _ => None end end) as [b0|]; [|discriminate OV].
    cbn in OV. injection OV as <-. reflexivity. }
  pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
  assert (EZ : w2Z z = bv_unsigned b).
  { rewrite <- (bytes_val_ext_word false 1 [b] eq_refl ltac:(lia)) in Dv. unfold bytes_val in Dv. cbn [den] in Dv. unfold wbv in Dv.
    assert (EB : bytes_le_to_Z [b] = bv_unsigned b) by (rewrite bytes_le_to_Z_cons; cbn; lia).
    rewrite EB, (ext_Z_small_id false 1 (bv_unsigned b)) in Dv; [| lia| unfold two64; lia| change (2 ^ (8 * 1 - 0)) with 256; lia].
    apply (f_equal bv_unsigned) in Dv. rewrite !Z_to_bv_unsigned in Dv.
    pose proof (w2Z_range z) as RZ.
    rewrite (bv_wrap_small 64 (w2Z z)) in Dv by (rewrite bv_modulus_64; exact RZ).
    rewrite (bv_wrap_small 64 (bv_unsigned b)) in Dv by (rewrite bv_modulus_64; unfold two64; lia). exact Dv. }
  rewrite EZ. split; [| lia]. rewrite RB. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Definition text_ok (st : sstate) (k : int) (off : Z) (len : nat) : bool :=
  forallb (fun i => match byte_lit st (VP k (Z2w (off + Z.of_nat i))) with Some z => negb (z =? 0) | None => false end) (seq 0 len)
  && match byte_lit st (VP k (Z2w (off + Z.of_nat len))) with Some z => z =? 0 | None => false end.

Lemma w2Zs_Z2w : forall z, - two63 <= z < two63 -> w2Zs (Z2w z) = z.
Proof.
  intros z Hz. rewrite <- w2Zs_swrap, Z2w_ok. unfold bv_swrap, bv_wrap. rewrite bv_modulus_64, bv_half_modulus_64.
  unfold two63, two64 in *. rewrite Zplus_mod_idemp_l. rewrite Z.mod_small by lia. lia.
Qed.

Lemma den_VP_Z2w : forall E k z, - two63 <= z < two63 -> 0 <= bv_unsigned (ev E k) + z < two64 ->
  bv_unsigned (den E (VP k (Z2w z))) = bv_unsigned (ev E k) + z.
Proof. intros E k z Hz HR. rewrite den_VP, (w2Zs_Z2w z Hz). apply Z.mod_small. exact HR. Qed.

Lemma bytes_of_pointwise : forall (P : byte -> Prop) m A n,
  (forall j, 0 <= j < Z.of_nat n -> exists b, rb segs m (A + j) = Some b /\ P b) ->
  exists bs, length bs = n /\ Forall P bs /\ forall j, 0 <= j < Z.of_nat n -> rb segs m (A + j) = nth_error bs (Z.to_nat j).
Proof.
  intros P m A n. induction n as [|n IH]; intros H.
  - exists []. split; [reflexivity|]. split; [constructor|]. intros j Hj. lia.
  - destruct IH as (bs & L & FA & PW). { intros j Hj. apply H. lia. }
    destruct (H (Z.of_nat n) ltac:(lia)) as (b & RB & Pb).
    exists (bs ++ [b]). split; [rewrite length_app; cbn; lia|]. split; [apply Forall_app; split; [exact FA| constructor; [exact Pb| constructor]]|].
    intros j Hj. destruct (Z.eq_dec j (Z.of_nat n)) as [->|NE].
    + rewrite Nat2Z.id, nth_error_app2 by lia. rewrite L, Nat.sub_diag. exact RB.
    + rewrite nth_error_app1 by lia. apply PW. lia.
Qed.

Lemma text_ok_sound : forall E st ms mo k off len,
  st_ok segs OPS E st ms mo -> text_ok st k off len = true ->
  - two63 <= off -> off + Z.of_nat len < two63 -> 0 <= bv_unsigned (ev E k) + off -> bv_unsigned (ev E k) + off + Z.of_nat len < two64 ->
  exists str, length str = len /\ Forall (fun b : byte => bv_unsigned b <> 0) str
    /\ AM.bytes_at segs (ms_mem ms) (bv_unsigned (ev E k) + off) (str ++ [Z_to_bv 8 0]).
Proof.
  intros E st ms mo k off len HS H O1 O2 A1 A2. unfold text_ok in H. apply andb_prop in H as [HT HZ].
  set (A := bv_unsigned (ev E k) + off) in *.
  assert (PW : forall j, 0 <= j < Z.of_nat len -> exists b, rb segs (ms_mem ms) (A + j) = Some b /\ bv_unsigned b <> 0).
  { intros j Hj. rewrite forallb_forall in HT. specialize (HT (Z.to_nat j) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in HT by lia.
    destruct (byte_lit st (VP k (Z2w (off + j)))) as [z|] eqn:BL; [|discriminate HT].
    destruct (byte_lit_sound E st ms mo _ z HS BL) as [RB RZ]. rewrite (den_VP_Z2w E k (off + j)) in RB by (unfold two64 in *; lia).
    exists (Z_to_bv 8 z). split; [unfold A; rewrite <- Z.add_assoc; exact RB|].
    rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 8) with 256; lia).
    destruct (Z.eqb_spec z 0); [discriminate HT| assumption]. }
  destruct (bytes_of_pointwise (fun b => bv_unsigned b <> 0) (ms_mem ms) A len PW) as (str & L & FA & PW2).
  exists str. split; [exact L|]. split; [exact FA|].
  destruct (byte_lit st (VP k (Z2w (off + Z.of_nat len)))) as [z|] eqn:BL; [|discriminate HZ].
  apply Z.eqb_eq in HZ. subst z.
  destruct (byte_lit_sound E st ms mo _ 0 HS BL) as [RB _]. rewrite (den_VP_Z2w E k (off + Z.of_nat len)) in RB by (unfold two64 in *; lia).
  split; [unfold A; lia|]. split; [rewrite length_app, L; cbn [length]; unfold A, two64 in *; lia|].
  intros i Hi. rewrite length_app, L in Hi. cbn [length] in Hi. rewrite <- rb_mrdA.
  destruct (Nat.eq_dec i len) as [->|NE].
  - rewrite nth_error_app2 by lia. rewrite L, Nat.sub_diag. cbn [nth_error]. unfold A. rewrite <- Z.add_assoc. exact RB.
  - rewrite nth_error_app1 by lia. rewrite (PW2 (Z.of_nat i)) by lia. rewrite Nat2Z.id. reflexivity.
Qed.

End WithSegs.
End FxOut.
End TwinB.

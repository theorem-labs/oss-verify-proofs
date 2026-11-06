(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs MemProofs StepSoundBase StepSoundMem PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout OpsBridge GLib.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP StepB StepM PlanS UB.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module PkStep.
Section WithSegs.
Variable segs : list Segment.
Variable OPS : optable.

Lemma lor_shiftl_byte : forall b r, 0 <= b < 256 -> 0 <= r -> Z.lor b (Z.shiftl r 8) = b + 256 * r.
Proof.
  intros b r Hb Hr. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (MemP.lor_disjoint_add b r 8); [| exact Hb| exact Hr]. change (2 ^ 8) with 256. lia.
Qed.

Lemma rdZ_ov_read : forall m n A z, 0 <= A -> A + Z.of_nat n <= two64 ->
  rdZ (bmem_of segs m) A n = Some z ->
  exists bs, ov_read_bytes segs m (Z_to_bv 64 A) n = Some bs /\ length bs = n /\ bytes_le_to_Z bs = z.
Proof.
  intros m n. induction n as [|n IH]; intros A z HA HAn RD.
  - cbn in RD. injection RD as <-. exists []. split; [reflexivity| split; reflexivity].
  - cbn [rdZ] in RD. destruct (bmem_of segs m A) as [b0|] eqn:B0; [|discriminate].
    destruct (rdZ (bmem_of segs m) (A + 1) n) as [r|] eqn:RR; [|discriminate]. injection RD as <-.
    rewrite Nat2Z.inj_succ in HAn.
    destruct (IH (A + 1) r ltac:(lia) ltac:(lia) RR) as (bs' & OV & LEN & VAL).
    pose proof B0 as B0'. unfold bmem_of in B0'.
    replace ((0 <=? A) && (A <? two64)) with true in B0' by (symmetry; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
    destruct (rb segs m A) as [b|] eqn:RB; [|discriminate]. cbn [option_map] in B0'. injection B0' as <-.
    exists (b :: bs'). split; [| split; [cbn; lia|]].
    + cbn [ov_read_bytes]. rewrite <- rb_unfold, RB, Z_to_bv_succ, OV. reflexivity.
    + cbn [bytes_le_to_Z]. rewrite VAL. apply lor_shiftl_byte.
      * pose proof (bv_unsigned_in_range _ b) as R. change (bv_modulus 8) with 256 in R. lia.
      * exact (proj1 (UG.rdZ_nonneg (bmem_of segs m) n (A + 1) r (UG.bmem_of_bytes_range segs m) RR)).
Qed.

Lemma ext_word_small : forall sx w z, 1 <= w <= 8 -> 0 <= z < 2 ^ (8 * w - 1) ->
  ext_word sx 0 w (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros sx w z Hw Hz.
  assert (P : 2 ^ (8 * w - 1) <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia).
  assert (P2 : 2 ^ (8 * w) = 2 * 2 ^ (8 * w - 1)) by (replace (8 * w) with (1 + (8 * w - 1)) at 1 by lia; rewrite Z.pow_add_r by lia; reflexivity).
  apply bv_eq. unfold ext_word. rewrite !Z_to_bv_unsigned. unfold ext_Z, bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with two64.
  rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r. rewrite (Z.mod_small z two64) by (unfold two64; lia). rewrite (Z.mod_small z) by lia.
  assert (M64 : z mod two64 = z) by (apply Z.mod_small; unfold two64; lia).
  destruct sx; [| exact M64].
  destruct (Z.leb_spec (2 ^ (8 * w - 1)) z); [lia|]. rewrite ?M64. reflexivity.
Qed.

Lemma oracle_ILoad : forall E st ms model (w : bv 32) (i : instr) sz sx rd rs1 off A z (v : sv),
  st_ok segs OPS E st ms model -> PrimInt63.ltb (s_pc st) bit62i = true ->
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4%Z) ->
  of_instr i = Some (ILoad sz sx rd rs1 off) ->
  den E (sv_alu ALU_ADD (getr st rs1) (VL off)) = Z_to_bv 64 A -> 0 <= A -> A + to_Z (msize_bytes sz) <= two64 ->
  rdZ (bmem_of segs (ms_mem ms)) A (Z.to_nat (to_Z (msize_bytes sz))) = Some z ->
  den E v = ext_word sx 0 (to_Z (msize_bytes sz)) (Z_to_bv 64 z) ->
  exists ms', RiscvSemantics.step segs ms = MachineOk ms' /\ ms_mem ms' = ms_mem ms /\
              st_ok segs OPS E (setpc (setr st rd v) (pc4 st)) ms' model.
Proof.
  intros E st ms model w i sz sx rd rs1 off A z v HS Hpc Hf He Hd Hof HA A0 A1 RD Hv.
  destruct (of_instr_ILoad i sz sx rd rs1 off Hof) as (rd' & rs1' & imm & -> & Hrd & Hrs1 & ->).
  assert (W8 : 1 <= to_Z (msize_bytes sz) <= 8) by (destruct sz; cbn [msize_bytes]; [change (to_Z 1%uint63) with 1| change (to_Z 2%uint63) with 2| change (to_Z 4%uint63) with 4| change (to_Z 8%uint63) with 8]; lia).
  assert (A2 : A + Z.of_nat (Z.to_nat (to_Z (msize_bytes sz))) <= two64) by (rewrite Z2Nat.id; lia).
  destruct (rdZ_ov_read (ms_mem ms) _ A z A0 A2 RD) as (bs & OV & LEN & VAL).
  rewrite <- HA, <- (ea_den segs OPS E st ms model rs1 rs1' _ imm HS Hrs1) in OV.
  rewrite (step_exec segs ms w _ Hf He Hd).
  cbn [Sem.exec load_val]. rewrite <- (reg_of_r5_of_reg rd' rd Hrd). rewrite (npc_eq segs OPS E st ms model HS Hpc).
  assert (LW : le_bytes_to_word bs = Z_to_bv 64 z) by (unfold le_bytes_to_word; rewrite VAL; reflexivity).
  destruct sz; cbn [msize_bytes load_val width_bytes] in *;
    (erewrite interp_ELoad by exact OV); rewrite interp_EDone; eexists; (split; [reflexivity|]); (split; [reflexivity|]);
    apply (st_ok_reg_pc segs OPS E st ms model rd v _ (pc4 st) HS); rewrite Hv, LW.
  - change (to_Z 1%uint63) with 1. apply ext_word_1.
  - change (to_Z 2%uint63) with 2. apply ext_word_2.
  - change (to_Z 4%uint63) with 4. apply ext_word_4.
  - change (to_Z 8%uint63) with 8. apply ext_word_8.
Qed.

End WithSegs.
End PkStep.

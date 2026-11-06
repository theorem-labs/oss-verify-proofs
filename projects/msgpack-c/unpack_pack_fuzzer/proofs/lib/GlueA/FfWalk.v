(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF StepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg F_ffepi.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Lemma ffepi_shape_inv : forall pcz rt rf off, ffepi_shape pcz rt rf off = true ->
  exists (w1 w2 : bv 32) (sg : bool) (RTr RFr R2 : reg) (imm imm2 : bv 12),
    fetch_word asegs (Z_to_bv 64 pcz) = Some w1 /\ is_ecall w1 = false /\ decode_any w1 = Some (Load SZ8 sg RTr RFr imm, 4)
    /\ fetch_word asegs (bv_add (Z_to_bv 64 pcz) (Z_to_bv 64 4)) = Some w2 /\ is_ecall w2 = false
    /\ decode_any w2 = Some (Store SZ1 RTr R2 imm2, 4) /\ is_x0 R2 = true /\ bv_unsigned (sext 64 imm2) = 0 /\ is_x0 RTr = false
    /\ bv_unsigned RTr = rt /\ bv_unsigned RFr = rf /\ bv_unsigned (sext 64 imm) = off.
Proof.
  intros pcz rt rf off H. unfold ffepi_shape in H.
  destruct (fetch_word asegs (Z_to_bv 64 pcz)) as [w1|] eqn:F1; [|discriminate H].
  destruct (fetch_word asegs (bv_add (Z_to_bv 64 pcz) (Z_to_bv 64 4))) as [w2|] eqn:F2; [|discriminate H].
  apply andb_prop in H as [H M]. apply andb_prop in H as [E1 E2]. apply negb_true_iff in E1, E2.
  destruct (decode_any w1) as [[i1 n1]|] eqn:D1; [|discriminate M].
  destruct i1 as [| | | | |sz sg t f imm | | | | | | | | | | | | | | | | | | | | | | | | | | | | |]; try discriminate M.
  destruct sz; try discriminate M.
  destruct n1 as [|p|p]; try discriminate M. destruct p as [p|p|]; try discriminate M. destruct p as [p|p|]; try discriminate M. destruct p as [p|p|]; try discriminate M.
  destruct (decode_any w2) as [[i2 n2]|] eqn:D2; [|discriminate M].
  destruct i2 as [| | | | | |sz2 t2 r2 imm2 | | | | | | | | | | | | | | | | | | | | | | | | | | | |]; try discriminate M.
  destruct sz2; try discriminate M.
  destruct n2 as [|p|p]; try discriminate M. destruct p as [p|p|]; try discriminate M. destruct p as [p|p|]; try discriminate M. destruct p as [p|p|]; try discriminate M.
  repeat match type of M with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in M as [M X] end.
  apply Z.eqb_eq in M. apply Z.eqb_eq in Q4, Q3, Q2, Q0. apply negb_true_iff in Q.
  assert (ET : t2 = t) by (apply bv_eq; lia). subst t2.
  exists w1, w2, sg, t, f, r2, imm, imm2. repeat (split; [reflexivity || assumption|]). assumption.
Qed.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import F_ffepi.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Lemma ffepi_shape_inv : forall pcz rt rf off, ffepi_shape pcz rt rf off = true ->
  exists (w1 w2 : bv 32) (sg : bool) (RTr RFr R2 : reg) (imm imm2 : bv 12),
    fetch_word bsegs (Z_to_bv 64 pcz) = Some w1 /\ is_ecall w1 = false /\ decode_any w1 = Some (Load SZ8 sg RTr RFr imm, 4)
    /\ fetch_word bsegs (bv_add (Z_to_bv 64 pcz) (Z_to_bv 64 4)) = Some w2 /\ is_ecall w2 = false
    /\ decode_any w2 = Some (Store SZ1 RTr R2 imm2, 4) /\ is_x0 R2 = true /\ bv_unsigned (sext 64 imm2) = 0 /\ is_x0 RTr = false
    /\ bv_unsigned RTr = rt /\ bv_unsigned RFr = rf /\ bv_unsigned (sext 64 imm) = off.
Proof.
  intros pcz rt rf off H. unfold ffepi_shape in H.
  destruct (fetch_word bsegs (Z_to_bv 64 pcz)) as [w1|] eqn:F1; [|discriminate H].
  destruct (fetch_word bsegs (bv_add (Z_to_bv 64 pcz) (Z_to_bv 64 4))) as [w2|] eqn:F2; [|discriminate H].
  apply andb_prop in H as [H M]. apply andb_prop in H as [E1 E2]. apply negb_true_iff in E1, E2.
  destruct (decode_any w1) as [[i1 n1]|] eqn:D1; [|discriminate M].
  destruct i1 as [| | | | |sz sg t f imm | | | | | | | | | | | | | | | | | | | | | | | | | | | | |]; try discriminate M.
  destruct sz; try discriminate M.
  destruct n1 as [|p|p]; try discriminate M. destruct p as [p|p|]; try discriminate M. destruct p as [p|p|]; try discriminate M. destruct p as [p|p|]; try discriminate M.
  destruct (decode_any w2) as [[i2 n2]|] eqn:D2; [|discriminate M].
  destruct i2 as [| | | | | |sz2 t2 r2 imm2 | | | | | | | | | | | | | | | | | | | | | | | | | | | |]; try discriminate M.
  destruct sz2; try discriminate M.
  destruct n2 as [|p|p]; try discriminate M. destruct p as [p|p|]; try discriminate M. destruct p as [p|p|]; try discriminate M. destruct p as [p|p|]; try discriminate M.
  repeat match type of M with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in M as [M X] end.
  apply Z.eqb_eq in M. apply Z.eqb_eq in Q4, Q3, Q2, Q0. apply negb_true_iff in Q.
  assert (ET : t2 = t) by (apply bv_eq; lia). subst t2.
  exists w1, w2, sg, t, f, r2, imm, imm2. repeat (split; [reflexivity || assumption|]). assumption.
Qed.
End TwinB.

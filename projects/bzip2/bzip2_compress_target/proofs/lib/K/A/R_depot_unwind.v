(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac ImageA Arr Walk.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require R_unwind_defs R_depot_defs.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA Arr Walk.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_unwind_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_depot_defs.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).

Definition rng64 (x : Z) : Prop := 0 <= x < 2 ^ 64.

Lemma wr_trace_split : forall tr tb, wr_trace tr tb = map (Z_to_bv 64) tr ++ skipn (length tr) tb.
Proof. reflexivity. Qed.

Lemma map_unsigned_lits : forall tr, Forall rng64 tr -> map bv_unsigned (map (Z_to_bv 64) tr) = tr.
Proof.
  induction tr as [|x tr IH]; intros HF; [reflexivity|]. inversion HF as [|? ? Hx Htr]; subst.
  cbn [map]. rewrite unsigned_lit by (unfold rng64 in Hx; lia). f_equal. apply IH. exact Htr.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA Arr Walk.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import R_unwind_defs R_depot_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).

Definition rng64 (x : Z) : Prop := 0 <= x < 2 ^ 64.

Lemma wr_trace_split : forall tr tb, wr_trace tr tb = map (Z_to_bv 64) tr ++ skipn (length tr) tb.
Proof. reflexivity. Qed.

Lemma map_unsigned_lits : forall tr, Forall rng64 tr -> map bv_unsigned (map (Z_to_bv 64) tr) = tr.
Proof.
  induction tr as [|x tr IH]; intros HF; [reflexivity|]. inversion HF as [|? ? Hx Htr]; subst.
  cbn [map]. rewrite unsigned_lit by (unfold rng64 in Hx; lia). f_equal. apply IH. exact Htr.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

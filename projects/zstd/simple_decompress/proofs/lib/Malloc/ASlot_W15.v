(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr Bytes.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocKit_A.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Malloc Require Import Malloc_fp MallocKit_A2 F_malloc_bigw.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Malloc Require Import MallocKit_A3.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma lxor_b2z_1 b : Z.lxor (Z.b2z b) 1 = Z.b2z (negb b).
Proof. destruct b; reflexivity. Qed.

Lemma signed_lit_small z : -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros Hz. rewrite zb_signed, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  destruct (Z.ltb_spec (z mod 2^64) (2^63)); Z.div_mod_to_equations; lia.
Qed.

Lemma ltb99_leb100 b : (99 <? b) = (100 <=? b).
Proof. destruct (Z.ltb_spec 99 b), (Z.leb_spec 100 b); try reflexivity; lia. Qed.

Section SEQ.
Variables (sc : Z).
Hypothesis SC : 0 <= sc < 48.

Definition seqW : list (Z * Z) := [(CTX + 848, CTX + 913)]%Z.
End SEQ.


End CANSEC1.

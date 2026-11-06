(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzArr BzCMem BzCStream BzCState BzArrD CmpMem CmpCut CmpCutSM CmpCutSmA AsanKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_sdV.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition sm_set (cx : cctx) (FV : Z) : list cell :=
  let E := c_E cx in
  let NOT := fun z => Z_to_bv 64 (18446744073709551615 - z) in
  [C8 (Z_to_bv 64 (E + 51648)); C8 (Z_to_bv 64 (E + 38740)); C8 (NOT (E + 38740)); C8 (NOT (E + 38998)); C8 (Z_to_bv 64 (E + 51644)); C8 (Z_to_bv 64 (E + 38224)); C8 (Z_to_bv 64 (E + 38482));
   C8 (NOT (E + 38224)); C8 (NOT (E + 38482)); C8 (Z_to_bv 64 (E + 38998)); C8 (Z_to_bv 64 (E + 37966)); C8 (NOT (E + 51640)); C8 (NOT (E + 37966)); C8 (Z_to_bv 64 18002); C8 (NOT FV)].

(* [comment removed for export] *)
Lemma rw_cells_cutS : forall segs m A cs k, rw_cells segs m A cs ->
  rw_cells segs m A (firstn k cs) /\ rw_cells segs m (A + Z.of_nat (cells_size (firstn k cs)))%Z (skipn k cs).
Proof. intros segs m A cs k H. rewrite <- (firstn_skipn k cs) in H at 1. exact (proj1 (rw_cells_app_iff_c segs m A _ _) H). Qed.

End ACeilS1.

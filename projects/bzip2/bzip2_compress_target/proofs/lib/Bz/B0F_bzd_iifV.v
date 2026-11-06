(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzInv BzTables BzContracts AsanKit AsanCut AsanCutB0 CmpCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0F_leafCut B0F_idx.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.

Section ACeilS1. Context {ACEIL__ : ACeil}.
Lemma B0_iif_U :
  ltac:(let T := eval cbv beta iota zeta delta [indexIntoF_aspecF indexIntoF_apostF B0_FR_indexIntoF aci_segs aci_hi aci_c ci_segs ci_hi B0C]
                 in (indexIntoF_aspecF B0C 0x83de0 B0_FR_indexIntoF) in exact T).
Proof. exact B0_indexIntoF. Qed.
End ACeilS1.

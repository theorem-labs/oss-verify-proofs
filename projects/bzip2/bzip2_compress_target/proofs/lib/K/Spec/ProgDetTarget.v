(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import PropExec MState Mem ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Import Prelim Monad Stdio Prog Canon.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Malloc.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Import HexModel Target TargetSafe.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Import ProgDetIface ProgDetLogic ProgDetNodes ProgDetMalloc ProgDetStdio.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section TargetE.
Context {CE__ : Ceiling}.
Variable sel : option bool.
Variable X : list event -> Prop.

Let ops : target_ops (Monad.M PState) bptr := Target.ops raw_malloc raw_free ps_so set_so_ps.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Section Harness.
Variable K : assnE PState.
Hypothesis HK : fstable K.
Variable d : list Z.
Hypothesis Hd : zlength d < 2^60.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

End Harness.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma zlength_zeros_out : forall j, zlength (zeros_out j) = 2 * Z.of_nat j.
Proof.
  induction j as [|j IH]; [reflexivity|]. rewrite zeros_out_S, zlen_app, IH. unfold zlength. cbn [length]. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End TargetE.

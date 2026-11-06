(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Spec Require Import Prelim Monad PrintfModel.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.PG Require Import Printf_lib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Definition SN_CAP : Z := 80.

Definition OUT_sn (bs : list Z) : M (list Z) unit :=
  o <- mget ;; if zlength o + zlength bs <=? SN_CAP then mput (o ++ bs) else munr.

(* [comment removed for export] *)
Definition OUTFP_sn (y w p fl t : Z) : M (list Z) Z := munr.

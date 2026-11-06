(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec SeqExec StepTac StoreOk WalkFastM.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SumWalkTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac rdn_peel1_fast :=
  first [ rdn_peel_fast1
        | rewrite rdn_wbytes_out_Z by (zlen; lia_fast)
        | rewrite rdn_wbytes_out by (zsimp; lia_fast) ].

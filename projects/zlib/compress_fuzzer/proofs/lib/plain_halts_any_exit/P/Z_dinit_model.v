(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface DeflateState Trees DeflateLz Deflate RefDeflateInitLib RefDeflSafeI5b HarnessSmall ZApiInst ZTaint.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition spre (G : N -> Z -> Z) (po : Z) : deflate_state :=
  set_pending_out (s_fin (S5g 0%N 1%N 2%N 3%N 4%N (G 0%N) (G 1%N) (G 2%N) (G 3%N) (G 4%N) dinit_cs 1 15 8) 6 0 8) po.

Lemma RK0_set_po : forall s po, RK0 (set_pending_out s po) = RK0 s.
Proof. intros s po. destruct s. reflexivity. Qed.

Local Notation wz := (Z_to_bv 64).

Definition s_raw (G : N -> Z -> Z) : deflate_state := ds_of_oracle (G 0%N) 0%N dinit_cs.


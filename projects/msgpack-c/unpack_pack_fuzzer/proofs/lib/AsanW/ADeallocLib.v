(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma flag_ia_true : forall (m : amem) (A : Z) (ia : bool) (r1 r2 : list cell),
  rw_cells asegs m A (C1 (Z_to_bv 8 (if ia then 1 else 0)) :: r1) ->
  rw_cells asegs m A (C1 (Z_to_bv 8 1) :: r2) -> ia = true.
Proof.
  intros m A ia r1 r2 H1 H2. destruct ia; [reflexivity| exfalso].
  pose proof (rw_cells_read asegs m A _ 0%nat _ H1 eq_refl) as E1.
  pose proof (rw_cells_read asegs m A _ 0%nat _ H2 eq_refl) as E2.
  cbn [csize cbytes] in E1, E2. rewrite E1 in E2. injection E2 as E2.
  vm_compute in E2. discriminate.
Qed.
End CANSEC1.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.
Import AProto.TwinB ABase.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma flag_ia_true : forall (m : amem) (A : Z) (ia : bool) (r1 r2 : list cell),
  rw_cells bsegs m A (C1 (Z_to_bv 8 (if ia then 1 else 0)) :: r1) ->
  rw_cells bsegs m A (C1 (Z_to_bv 8 1) :: r2) -> ia = true.
Proof.
  intros m A ia r1 r2 H1 H2. destruct ia; [reflexivity| exfalso].
  pose proof (rw_cells_read bsegs m A _ 0%nat _ H1 eq_refl) as E1.
  pose proof (rw_cells_read bsegs m A _ 0%nat _ H2 eq_refl) as E2.
  cbn [csize cbytes] in E1, E2. rewrite E1 in E2. injection E2 as E2.
  vm_compute in E2. discriminate.
Qed.
End CANSEC1.
End TwinB.

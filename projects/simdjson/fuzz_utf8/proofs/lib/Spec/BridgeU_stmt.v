(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Run.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad Stdio Adapter Driver HarnessU ProgA ProgZ.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require TopLevel.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require ShapeAlg Spec.
Import ListNotations.

(* [comment removed for export] *)
Definition bridge_init_fds : list (word * FdEntry) :=
  [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ].

(* [comment removed for export] *)
Definition bridge_argv_Z (argv : list (list byte)) : list (list Z) := map (map bv_unsigned) argv.

Definition bridgeU_stmt : Prop :=
  forall (inp : ProcInput) (moZ : Model) (rs : Z),
  valid_input_either inp ->
  minv moZ -> m_halted moZ = None -> m_fds moZ = bridge_init_fds -> m_fs moZ = in_fs inp ->
  forall tr : list event,
    TopLevel.tree_traces (progZ_tree rs (bridge_argv_Z (in_argv inp))) moZ tr
    <-> Common.Spec.spec (in_argv inp) (in_fs inp) tr.

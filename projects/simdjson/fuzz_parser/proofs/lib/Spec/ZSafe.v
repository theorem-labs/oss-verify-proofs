(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Run.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prog ProgZ EquivZA BridgeU_stmt BridgeU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem progZ_no_leaf : forall inp moZ rs,
  valid_input_either inp -> minv moZ -> m_halted moZ = None -> m_fds moZ = init_fds -> m_fs moZ = in_fs inp ->
  forall tr r mo', ~ tpath nstep (progZ_tree rs (argv_Z (in_argv inp))) moZ tr r mo'.
Proof. intros inp moZ rs Hvi _ _ Hfds Hfs. exact (progZ_no_leaf_gen inp moZ rs Hvi Hfds Hfs). Qed.

(* [comment removed for export] *)
Theorem bridgeU' : forall (inp : ProcInput) (moZ : Model) (rs : Z),
  valid_input_either inp -> minv moZ -> m_halted moZ = None -> m_fds moZ = init_fds -> m_fs moZ = in_fs inp ->
  forall tr, TopLevel.tree_traces (progZ_tree rs (argv_Z (in_argv inp))) moZ tr
             <-> Common.Spec.spec (in_argv inp) (in_fs inp) tr.
Proof. exact bridgeU. Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Exec ITree Nodes Decode RegsEquiv Image.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.Plain Require Import PImg Harness_iface Fuzz_bridge PlainMain_asm.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import PState Monad Stdio Driver Prog.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only Require Import TopLevel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.Plain Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Theorem plain_impl_closed : forall (en : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage psegs p_init_pc p_phdrs) en inp ->
    valid_input_either inp ->
    impl psegs (at_node psegs) (Prog.prog psegs PREAD_STAGE inp en) (epost (fun (_ : unit) (_ : machine_state) => True))
         (ms0 psegs p_init_pc p_phdrs en inp).
Proof. exact (plain_impl (fun rc => @fuzz_one_bridge rc)). Qed.

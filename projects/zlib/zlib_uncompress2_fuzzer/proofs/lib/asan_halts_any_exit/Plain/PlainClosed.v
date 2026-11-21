(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Lib Require Import PropExec MState Mem Cells Exec ITree Nodes Decode RegsEquiv Image CTree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Plain Require Import PImg RMalloc_iface RF_malloc_spec RF_free_spec Harness_iface Fuzz_bridge PlainMain_asm.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Spec Require Import PState Monad Stdio Driver Prog ProgC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit Require Import TopLevel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Plain Require Import RunDraw.
Require OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.I7S.S_TopI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Theorem fuzz_one_closed : forall rc : runConstT, @fuzz_one_stmt rc.
Proof.
  intros rc.
  exact (@fuzz_one_bridge rc (fun fx => @OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.I7S.S_TopI.zlib_contract_S7 fx) rmalloc_spec rfree_spec_proof).
Qed.

Theorem plain_implC_closed : forall (en : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage psegs p_init_pc p_phdrs) en inp ->
    valid_input_either inp ->
    implC psegs (at_node psegs) (progC_tree psegs PREAD_STAGE inp en) (epost (fun (_ : unit) (_ : machine_state) => True))
          (ms0 psegs p_init_pc p_phdrs en inp).
Proof. exact (plain_impl fuzz_one_closed). Qed.

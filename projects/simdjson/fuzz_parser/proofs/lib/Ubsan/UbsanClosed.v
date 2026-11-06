(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ITree Nodes Decode RegsEquiv Image.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import UImg RMalloc_iface RF_malloc_spec RF_free_spec.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import PU_iface RDriver_iface PExitP UbsanImpl UbsanMain_asm.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import PState Monad Stdio Driver ProgP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import TopLevel.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ubsan_client_stmt : Prop := forall rc : runConstT, @fuzz_oneU_stmt rc ProgP.fuzz_one.

(* [comment removed for export] *)
Theorem ubsan_impl_closed_modulo_client : ubsan_client_stmt ->
  forall (en : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage usegs u_init_pc u_phdrs) en inp ->
    valid_input_either inp ->
    impl usegs (at_node usegs) (ProgP.prog usegs UREAD_STAGE inp en) (epost (fun (_ : unit) (_ : machine_state) => True))
         (ms0 usegs u_init_pc u_phdrs en inp).
Proof.
  intros FUZZ. exact (ubsan_impl FUZZ (fun rc => @pexitP_proof rc)).
Qed.

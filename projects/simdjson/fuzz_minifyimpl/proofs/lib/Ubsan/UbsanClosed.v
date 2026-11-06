(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ITree Nodes Decode RegsEquiv Image.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import UImg RMalloc_iface RF_malloc_spec RF_free_spec ROpNew_iface ROpNew.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import PU_iface RDriver_iface PExitU UbsanImpl UbsanMain_asm.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import PState Monad Stdio Driver ProgP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib Require Import TopLevel.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Lemma ubsan_opnew_closed : opnew_stmt.
Proof. exact (opnew_proof rmalloc_spec). Qed.
Lemma ubsan_opdelete_closed : opdelete_stmt.
Proof. exact (opdelete_proof rfree_spec_proof). Qed.

(* [comment removed for export] *)
Lemma ubsan_exit_closed : pexit_stmt.
Proof. exact (pexitU_proof ubsan_opdelete_closed). Qed.
End CANSEC1.

(* [comment removed for export] *)
Definition ubsan_client_stmt : Prop := forall rc : runConstT, @opnew_stmt rc -> @opdelete_stmt rc -> @fuzz_oneU_stmt rc ProgP.fuzz_one.

(* [comment removed for export] *)
Theorem ubsan_impl_closed_modulo_client : ubsan_client_stmt ->
  forall (en : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage usegs u_init_pc u_phdrs) en inp ->
    valid_input_either inp ->
    impl usegs (at_node usegs) (ProgP.prog usegs UREAD_STAGE inp en) (epost (fun (_ : unit) (_ : machine_state) => True))
         (ms0 usegs u_init_pc u_phdrs en inp).
Proof.
  intros FUZZ. exact (ubsan_impl (fun rc => FUZZ rc (@ubsan_opnew_closed rc) (@ubsan_opdelete_closed rc)) (fun rc => @ubsan_exit_closed rc)).
Qed.

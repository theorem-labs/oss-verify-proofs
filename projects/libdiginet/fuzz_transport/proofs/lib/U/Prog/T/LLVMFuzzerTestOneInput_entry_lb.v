(* The config read of LLVMFuzzerTestOneInput (ubsan), cursor lengths n = 5 .. 9 (the tactics and the statement:
   U/Prog/T/LLVMFuzzerTestOneInput_entry_lt.v). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_entry_m LLVMFuzzerTestOneInput_entry_d
  LLVMFuzzerTestOneInput_entry_lt.
Import ListNotations.
Open Scope Z_scope.

Lemma lad_n5 : ent_lad_stmt (fun n => n = 5).
Proof. lad_case. Qed.

Lemma lad_n6 : ent_lad_stmt (fun n => n = 6).
Proof. lad_case. Qed.

Lemma lad_n7 : ent_lad_stmt (fun n => n = 7).
Proof. lad_case. Qed.

Lemma lad_n8 : ent_lad_stmt (fun n => n = 8).
Proof. lad_case. Qed.

Lemma lad_n9 : ent_lad_stmt (fun n => n = 9).
Proof. lad_case. Qed.

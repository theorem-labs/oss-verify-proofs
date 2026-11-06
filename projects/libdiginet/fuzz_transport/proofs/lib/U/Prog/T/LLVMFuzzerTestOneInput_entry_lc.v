(* The config read of LLVMFuzzerTestOneInput (ubsan), cursor lengths n = 10 .. 13 and n >= 14 (the tactics and the
   statement: U/Prog/T/LLVMFuzzerTestOneInput_entry_lt.v). *)
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

Lemma lad_ge14 : ent_lad_stmt (fun n => 14 <= n).
Proof. lad_case. Qed.
Lemma lad_n10 : ent_lad_stmt (fun n => n = 10).
Proof. lad_case. Qed.

Lemma lad_n11 : ent_lad_stmt (fun n => n = 11).
Proof. lad_case. Qed.

Lemma lad_n12 : ent_lad_stmt (fun n => n = 12).
Proof. lad_case. Qed.

Lemma lad_n13 : ent_lad_stmt (fun n => n = 13).
Proof. lad_case. Qed.


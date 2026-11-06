(* The config read of LLVMFuzzerTestOneInput (ubsan), cursor lengths n = 0 .. 4 (the tactics and the statement:
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

(* n = 0: no byte is read (the input may be empty) *)
Lemma lad_n0 : ent_lad_stmt (fun n => n = 0).
Proof.
  intros data D regs0 m0 Sp lo B1 o n flags F fc ms Q HP HNUM HFL Ho Hn Hon HDAT HD0 HS K.
  cbv beta in HP. subst n.
  destruct HS as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s4 & s5 & s6 & s8 & s10 & s11 &
                  t3 & t4 & t5 & t6 & m & -> & HM).
  destruct HM as (j0 & j60 & ST & MI & WM & MU0 & WMO0 & FR).
  unfold ent_frame, llvm_saved in FR. cbn [app] in FR.
  destruct HNUM as (H16 & Hlo & HK & H63 & HWL). unfold LH_K, LH_FRAME in *.
  pose proof (wm_len _ _ _ _ WM) as LB.
  wk_facts. wk_eq_fact OFF_g_fail_next. wk_eq_fact OFF_g_cfg.
  lad_run MI o.
  lad_fin K.
Qed.

Lemma lad_n1 : ent_lad_stmt (fun n => n = 1).
Proof. lad_case. Qed.

Lemma lad_n2 : ent_lad_stmt (fun n => n = 2).
Proof. lad_case. Qed.

Lemma lad_n3 : ent_lad_stmt (fun n => n = 3).
Proof. lad_case. Qed.

Lemma lad_n4 : ent_lad_stmt (fun n => n = 4).
Proof. lad_case. Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (proofs as pix_orient_fuzzer's copy; the unused KReplay table removed). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec RefMemcpyLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2MainEntry V2LibStdioCall V2ReadErr_defs.
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition KEPT_RF : list nat := [2; 3; 4]%nat.
Definition srRF0 : list expr := Eval vm_compute in sr_after_call_j srRE_base KEPT_RF 6.

(* [comment removed for export] *)
Definition ssB0 : sym_state := SS 0x17ab0 srRF0 [] knRE0 39.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knRE0.
(* [comment removed for export] *)
Definition logM1 : list sentry :=
  [SE (SA (EVar 0) (-548)) 2 (ELit 8253);
   SE (SA (EVar 0) (-552)) 4 (ELit 1042314357);
   SE (SA (EVar 0) (-560)) 8 (ELit 8101528366825958499)].
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 39.

(* [comment removed for export] *)
Definition ssC0 : sym_state := SS 0x3e75c srC0 [] knC0 71.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

(* [comment removed for export] *)
Definition ssD0 : sym_state := SS 0x3e75c srD0 [] knC 103.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_MC 103.

(* [comment removed for export] *)
Definition ssE0 : sym_state := SS 0x3e75c srE0 [] knD 135.
Definition rE := Eval vm_compute in run scr0 ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knD.
(* [comment removed for export] *)
Definition logM4 : list sentry := [SE (SA (EVar 0) (-546)) 8 (ELit 3762256352692483894)].
Definition knF0 : list kentry := Eval vm_compute in fst (fst (carry logM4 knE [])).
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
Definition ssF0 : sym_state := SS 0x3e75c srF0 [] knF0 167.
Definition rF := Eval vm_compute in run scr0 ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knF0.
Definition logM5 : list sentry :=
  [SE (SA (EVar 0) (-530)) 8 (ELit 748834984615634290);
   SE (SA (EVar 0) (-538)) 8 (ELit 2318354787771965984)].
Definition knG0 : list kentry := Eval vm_compute in fst (fst (carry logM5 knF [])).
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : sym_state := SS 0x3e75c srG0 [] knG0 199.
Definition rG := Eval vm_compute in run scr0 ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition scRF : stdio_res := Eval vm_compute in
  match stdio_call 199 srG knG with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Definition srH0 : list expr := Eval vm_compute in sc_sr scRF.
Definition knH0 : list kentry := Eval vm_compute in sc_kn scRF.

(* [comment removed for export] *)
Definition ssH0 : sym_state := SS (sc_ret scRF) srH0 [] knH0 231.
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.

Section VP1.
Lemma itinerary_rf :
  (s_pc (fst (fst rB)), snd (fst rB)) = (0x4347c%Z, [])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0x4347c%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0x4347c%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE)) = (0x4347c%Z, [])
  /\ (s_pc (fst (fst rF)), snd (fst rF)) = (0x4347c%Z, [])
  /\ (s_pc (fst (fst rG)), snd (fst rG)) = (0x3e37c%Z, [])
  /\ stdio_call 199 srG knG = Some scRF
  /\ (sc_ret scRF, sc_f scRF, sc_fd scRF) = (0x3ea4c%Z, 0x45f30%Z, 2%Z)
  /\ (sc_wb scRF, sc_wp scRF, sc_l scRF) = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-522)), ELit 0)
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0x3bef8%Z, []).
Proof. vm_compute. repeat split; reflexivity. Qed.
End VP1.

(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc Require Import Reloc RelocCode CanonCode RelocSites CanonSites.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_1308c : bv 32 := 0x00010513.
Lemma D_1308c : decode_any W_1308c = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13098 : bv 32 := 0xff017113.
Lemma D_13098 : decode_any W_13098 = Some (OpImm ALU_AND 2 2 4080, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_130a0 : bv 32 := 0x00052583.
Lemma D_130a0 : decode_any W_130a0 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_130bc : bv 32 := 0x00850613.
Lemma D_130bc : decode_any W_130bc = Some (OpImm ALU_ADD 12 10 8, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_130c0 : bv 32 := 0x00078513.
Lemma D_130c0 : decode_any W_130c0 = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_130c4 : bv 32 := 0x00000793.
Lemma D_130c4 : decode_any W_130c4 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_130cc : bv 32 := 0xff010113.
Lemma D_130cc : decode_any W_130cc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_130d0 : bv 32 := 0x00113423.
Lemma D_130d0 : decode_any W_130d0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_130d4 : bv 32 := 0x00813023.
Lemma D_130d4 : decode_any W_130d4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_130d8 : bv 32 := 0x01010413.
Lemma D_130d8 : decode_any W_130d8 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_130e4 : bv 32 := 0x00054503.
Lemma D_130e4 : decode_any W_130e4 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_130e8 : bv 32 := 0x00157513.
Lemma D_130e8 : decode_any W_130e8 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_130ec : bv 32 := 0x00050663.
Lemma D_130ec : decode_any W_130ec = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13100 : bv 32 := 0x00100513.
Lemma D_13100 : decode_any W_13100 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13104 : bv 32 := 0x00a58023.
Lemma D_13104 : decode_any W_13104 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13110 : bv 32 := 0x02050063.
Lemma D_13110 : decode_any W_13110 = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13130 : bv 32 := 0x00813083.
Lemma D_13130 : decode_any W_13130 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13134 : bv 32 := 0x00013403.
Lemma D_13134 : decode_any W_13134 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13138 : bv 32 := 0x01010113.
Lemma D_13138 : decode_any W_13138 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_1313c : bv 32 := 0x00008067.
Lemma D_1313c : decode_any W_1313c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13140 : bv 32 := 0xff010113.
Lemma D_13140 : decode_any W_13140 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13144 : bv 32 := 0x00113423.
Lemma D_13144 : decode_any W_13144 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13148 : bv 32 := 0x00813023.
Lemma D_13148 : decode_any W_13148 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_1314c : bv 32 := 0x01010413.
Lemma D_1314c : decode_any W_1314c = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13158 : bv 32 := 0x00054503.
Lemma D_13158 : decode_any W_13158 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_1315c : bv 32 := 0x00157513.
Lemma D_1315c : decode_any W_1315c = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13160 : bv 32 := 0x00050663.
Lemma D_13160 : decode_any W_13160 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13174 : bv 32 := 0x00100513.
Lemma D_13174 : decode_any W_13174 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13178 : bv 32 := 0x00a58023.
Lemma D_13178 : decode_any W_13178 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13184 : bv 32 := 0x00050e63.
Lemma D_13184 : decode_any W_13184 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_131a8 : bv 32 := 0x00050c63.
Lemma D_131a8 : decode_any W_131a8 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_131c0 : bv 32 := 0x00813083.
Lemma D_131c0 : decode_any W_131c0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_131c4 : bv 32 := 0x00013403.
Lemma D_131c4 : decode_any W_131c4 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_131c8 : bv 32 := 0x01010113.
Lemma D_131c8 : decode_any W_131c8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_131cc : bv 32 := 0x00008067.
Lemma D_131cc : decode_any W_131cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_1365c : bv 32 := 0x00008067.
Lemma D_1365c : decode_any W_1365c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13660 : bv 32 := 0xff010113.
Lemma D_13660 : decode_any W_13660 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13664 : bv 32 := 0x00113423.
Lemma D_13664 : decode_any W_13664 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13668 : bv 32 := 0x00813023.
Lemma D_13668 : decode_any W_13668 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_1366c : bv 32 := 0x00060413.
Lemma D_1366c : decode_any W_1366c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13670 : bv 32 := 0x00050613.
Lemma D_13670 : decode_any W_13670 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13680 : bv 32 := 0x00040513.
Lemma D_13680 : decode_any W_13680 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13684 : bv 32 := 0x00813083.
Lemma D_13684 : decode_any W_13684 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13688 : bv 32 := 0x00013403.
Lemma D_13688 : decode_any W_13688 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_1368c : bv 32 := 0x01010113.
Lemma D_1368c : decode_any W_1368c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13690 : bv 32 := 0x00008067.
Lemma D_13690 : decode_any W_13690 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13694 : bv 32 := 0x81010113.
Lemma D_13694 : decode_any W_13694 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13698 : bv 32 := 0x7a113423.
Lemma D_13698 : decode_any W_13698 = Some (Store SZ8 2 1 1960, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_1369c : bv 32 := 0xfc010113.
Lemma D_1369c : decode_any W_1369c = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_136a0 : bv 32 := 0x00050293.
Lemma D_136a0 : decode_any W_136a0 = Some (OpImm ALU_ADD 5 10 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_136a4 : bv 32 := 0x00001537.
Lemma D_136a4 : decode_any W_136a4 = Some (Lui 10 1, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_136a8 : bv 32 := 0x00a10533.
Lemma D_136a8 : decode_any W_136a8 = Some (Op ALU_ADD 10 2 10, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_136ac : bv 32 := 0x80f53c23.
Lemma D_136ac : decode_any W_136ac = Some (Store SZ8 10 15 2072, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_136b0 : bv 32 := 0x00001537.
Lemma D_136b0 : decode_any W_136b0 = Some (Lui 10 1, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_136b4 : bv 32 := 0x00a10533.
Lemma D_136b4 : decode_any W_136b4 = Some (Op ALU_ADD 10 2 10, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_136b8 : bv 32 := 0x83053023.
Lemma D_136b8 : decode_any W_136b8 = Some (Store SZ8 10 16 2080, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_136bc : bv 32 := 0x00001537.
Lemma D_136bc : decode_any W_136bc = Some (Lui 10 1, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_136c0 : bv 32 := 0x00a10533.
Lemma D_136c0 : decode_any W_136c0 = Some (Op ALU_ADD 10 2 10, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_136c4 : bv 32 := 0x83153423.
Lemma D_136c4 : decode_any W_136c4 = Some (Store SZ8 10 17 2088, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_136c8 : bv 32 := 0x7eb13c23.
Lemma D_136c8 : decode_any W_136c8 = Some (Store SZ8 2 11 2040, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_136cc : bv 32 := 0x00001537.
Lemma D_136cc : decode_any W_136cc = Some (Lui 10 1, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_136d0 : bv 32 := 0x00a10533.
Lemma D_136d0 : decode_any W_136d0 = Some (Op ALU_ADD 10 2 10, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_136d4 : bv 32 := 0x80c53023.
Lemma D_136d4 : decode_any W_136d4 = Some (Store SZ8 10 12 2048, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_136d8 : bv 32 := 0x00001537.
Lemma D_136d8 : decode_any W_136d8 = Some (Lui 10 1, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_136dc : bv 32 := 0x00a10533.
Lemma D_136dc : decode_any W_136dc = Some (Op ALU_ADD 10 2 10, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_136e0 : bv 32 := 0x80d53423.
Lemma D_136e0 : decode_any W_136e0 = Some (Store SZ8 10 13 2056, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_136e4 : bv 32 := 0x00001537.
Lemma D_136e4 : decode_any W_136e4 = Some (Lui 10 1, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_136e8 : bv 32 := 0x00a10533.
Lemma D_136e8 : decode_any W_136e8 = Some (Op ALU_ADD 10 2 10, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_136ec : bv 32 := 0x80e53823.
Lemma D_136ec : decode_any W_136ec = Some (Store SZ8 10 14 2064, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_136f0 : bv 32 := 0x7f810513.
Lemma D_136f0 : decode_any W_136f0 = Some (OpImm ALU_ADD 10 2 2040, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_136f4 : bv 32 := 0x7ea13023.
Lemma D_136f4 : decode_any W_136f4 = Some (Store SZ8 2 10 2016, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_136f8 : bv 32 := 0x01010513.
Lemma D_136f8 : decode_any W_136f8 = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_136fc : bv 32 := 0x7d000593.
Lemma D_136fc : decode_any W_136fc = Some (OpImm ALU_ADD 11 0 2000, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13700 : bv 32 := 0x7f810693.
Lemma D_13700 : decode_any W_13700 = Some (OpImm ALU_ADD 13 2 2040, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13704 : bv 32 := 0x00028613.
Lemma D_13704 : decode_any W_13704 = Some (OpImm ALU_ADD 12 5 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_1370c : bv 32 := 0x00054a63.
Lemma D_1370c : decode_any W_1370c = Some (Branch BC_LT 10 0 20, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13718 : bv 32 := 0x01010513.
Lemma D_13718 : decode_any W_13718 = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_1371c : bv 32 := 0x000580e7.
Lemma D_1371c : decode_any W_1371c = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13720 : bv 32 := 0x04010113.
Lemma D_13720 : decode_any W_13720 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13724 : bv 32 := 0x7a813083.
Lemma D_13724 : decode_any W_13724 = Some (Load SZ8 true 1 2 1960, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13728 : bv 32 := 0x7f010113.
Lemma D_13728 : decode_any W_13728 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_1372c : bv 32 := 0x00008067.
Lemma D_1372c : decode_any W_1372c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13730 : bv 32 := 0xff010113.
Lemma D_13730 : decode_any W_13730 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13734 : bv 32 := 0x00113423.
Lemma D_13734 : decode_any W_13734 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13738 : bv 32 := 0x00813023.
Lemma D_13738 : decode_any W_13738 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_1373c : bv 32 := 0x00060413.
Lemma D_1373c : decode_any W_1373c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13740 : bv 32 := 0x00050613.
Lemma D_13740 : decode_any W_13740 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13750 : bv 32 := 0x00040513.
Lemma D_13750 : decode_any W_13750 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13754 : bv 32 := 0x00813083.
Lemma D_13754 : decode_any W_13754 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13758 : bv 32 := 0x00013403.
Lemma D_13758 : decode_any W_13758 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_1375c : bv 32 := 0x01010113.
Lemma D_1375c : decode_any W_1375c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13760 : bv 32 := 0x00008067.
Lemma D_13760 : decode_any W_13760 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_1377c : bv 32 := 0x00051663.
Lemma D_1377c : decode_any W_1377c = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_13790 : bv 32 := 0x00008067.
Lemma D_13790 : decode_any W_13790 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Section F.
Context {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL}.
Lemma F_1308c : fetch_word rl_segs (rl (rl_delta 1000%positive) 0x1308c) = Some W_1308c.
Proof. rl_F 0%nat cc_13084. Qed.
Lemma F_13098 : fetch_word rl_segs (rl (rl_delta 1000%positive) 0x13098) = Some W_13098.
Proof. rl_F 0%nat cc_13084. Qed.
Lemma F_130a0 : fetch_word rl_segs (rl (rl_delta 1001%positive) 0x130a0) = Some W_130a0.
Proof. rl_F 1%nat cc_130a0. Qed.
Lemma F_130bc : fetch_word rl_segs (rl (rl_delta 1001%positive) 0x130bc) = Some W_130bc.
Proof. rl_F 1%nat cc_130a0. Qed.
Lemma F_130c0 : fetch_word rl_segs (rl (rl_delta 1001%positive) 0x130c0) = Some W_130c0.
Proof. rl_F 1%nat cc_130a0. Qed.
Lemma F_130c4 : fetch_word rl_segs (rl (rl_delta 1001%positive) 0x130c4) = Some W_130c4.
Proof. rl_F 1%nat cc_130a0. Qed.
Lemma F_130cc : fetch_word rl_segs (rl (rl_delta 1002%positive) 0x130cc) = Some W_130cc.
Proof. rl_F 2%nat cc_130cc. Qed.
Lemma F_130d0 : fetch_word rl_segs (rl (rl_delta 1002%positive) 0x130d0) = Some W_130d0.
Proof. rl_F 2%nat cc_130cc. Qed.
Lemma F_130d4 : fetch_word rl_segs (rl (rl_delta 1002%positive) 0x130d4) = Some W_130d4.
Proof. rl_F 2%nat cc_130cc. Qed.
Lemma F_130d8 : fetch_word rl_segs (rl (rl_delta 1002%positive) 0x130d8) = Some W_130d8.
Proof. rl_F 2%nat cc_130cc. Qed.
Lemma F_130e4 : fetch_word rl_segs (rl (rl_delta 1002%positive) 0x130e4) = Some W_130e4.
Proof. rl_F 2%nat cc_130cc. Qed.
Lemma F_130e8 : fetch_word rl_segs (rl (rl_delta 1002%positive) 0x130e8) = Some W_130e8.
Proof. rl_F 2%nat cc_130cc. Qed.
Lemma F_130ec : fetch_word rl_segs (rl (rl_delta 1002%positive) 0x130ec) = Some W_130ec.
Proof. rl_F 2%nat cc_130cc. Qed.
Lemma F_13100 : fetch_word rl_segs (rl (rl_delta 1002%positive) 0x13100) = Some W_13100.
Proof. rl_F 2%nat cc_130cc. Qed.
Lemma F_13104 : fetch_word rl_segs (rl (rl_delta 1002%positive) 0x13104) = Some W_13104.
Proof. rl_F 2%nat cc_130cc. Qed.
Lemma F_13110 : fetch_word rl_segs (rl (rl_delta 1002%positive) 0x13110) = Some W_13110.
Proof. rl_F 2%nat cc_130cc. Qed.
Lemma F_13130 : fetch_word rl_segs (rl (rl_delta 1002%positive) 0x13130) = Some W_13130.
Proof. rl_F 2%nat cc_130cc. Qed.
Lemma F_13134 : fetch_word rl_segs (rl (rl_delta 1002%positive) 0x13134) = Some W_13134.
Proof. rl_F 2%nat cc_130cc. Qed.
Lemma F_13138 : fetch_word rl_segs (rl (rl_delta 1002%positive) 0x13138) = Some W_13138.
Proof. rl_F 2%nat cc_130cc. Qed.
Lemma F_1313c : fetch_word rl_segs (rl (rl_delta 1002%positive) 0x1313c) = Some W_1313c.
Proof. rl_F 2%nat cc_130cc. Qed.
Lemma F_13140 : fetch_word rl_segs (rl (rl_delta 1003%positive) 0x13140) = Some W_13140.
Proof. rl_F 3%nat cc_13140. Qed.
Lemma F_13144 : fetch_word rl_segs (rl (rl_delta 1003%positive) 0x13144) = Some W_13144.
Proof. rl_F 3%nat cc_13140. Qed.
Lemma F_13148 : fetch_word rl_segs (rl (rl_delta 1003%positive) 0x13148) = Some W_13148.
Proof. rl_F 3%nat cc_13140. Qed.
Lemma F_1314c : fetch_word rl_segs (rl (rl_delta 1003%positive) 0x1314c) = Some W_1314c.
Proof. rl_F 3%nat cc_13140. Qed.
Lemma F_13158 : fetch_word rl_segs (rl (rl_delta 1003%positive) 0x13158) = Some W_13158.
Proof. rl_F 3%nat cc_13140. Qed.
Lemma F_1315c : fetch_word rl_segs (rl (rl_delta 1003%positive) 0x1315c) = Some W_1315c.
Proof. rl_F 3%nat cc_13140. Qed.
Lemma F_13160 : fetch_word rl_segs (rl (rl_delta 1003%positive) 0x13160) = Some W_13160.
Proof. rl_F 3%nat cc_13140. Qed.
Lemma F_13174 : fetch_word rl_segs (rl (rl_delta 1003%positive) 0x13174) = Some W_13174.
Proof. rl_F 3%nat cc_13140. Qed.
Lemma F_13178 : fetch_word rl_segs (rl (rl_delta 1003%positive) 0x13178) = Some W_13178.
Proof. rl_F 3%nat cc_13140. Qed.
Lemma F_13184 : fetch_word rl_segs (rl (rl_delta 1003%positive) 0x13184) = Some W_13184.
Proof. rl_F 3%nat cc_13140. Qed.
Lemma F_131a8 : fetch_word rl_segs (rl (rl_delta 1003%positive) 0x131a8) = Some W_131a8.
Proof. rl_F 3%nat cc_13140. Qed.
Lemma F_131c0 : fetch_word rl_segs (rl (rl_delta 1003%positive) 0x131c0) = Some W_131c0.
Proof. rl_F 3%nat cc_13140. Qed.
Lemma F_131c4 : fetch_word rl_segs (rl (rl_delta 1003%positive) 0x131c4) = Some W_131c4.
Proof. rl_F 3%nat cc_13140. Qed.
Lemma F_131c8 : fetch_word rl_segs (rl (rl_delta 1003%positive) 0x131c8) = Some W_131c8.
Proof. rl_F 3%nat cc_13140. Qed.
Lemma F_131cc : fetch_word rl_segs (rl (rl_delta 1003%positive) 0x131cc) = Some W_131cc.
Proof. rl_F 3%nat cc_13140. Qed.
Lemma F_1365c : fetch_word rl_segs (rl (rl_delta 1009%positive) 0x1365c) = Some W_1365c.
Proof. rl_F 9%nat cc_1365c. Qed.
Lemma F_13660 : fetch_word rl_segs (rl (rl_delta 1010%positive) 0x13660) = Some W_13660.
Proof. rl_F 10%nat cc_13660. Qed.
Lemma F_13664 : fetch_word rl_segs (rl (rl_delta 1010%positive) 0x13664) = Some W_13664.
Proof. rl_F 10%nat cc_13660. Qed.
Lemma F_13668 : fetch_word rl_segs (rl (rl_delta 1010%positive) 0x13668) = Some W_13668.
Proof. rl_F 10%nat cc_13660. Qed.
Lemma F_1366c : fetch_word rl_segs (rl (rl_delta 1010%positive) 0x1366c) = Some W_1366c.
Proof. rl_F 10%nat cc_13660. Qed.
Lemma F_13670 : fetch_word rl_segs (rl (rl_delta 1010%positive) 0x13670) = Some W_13670.
Proof. rl_F 10%nat cc_13660. Qed.
Lemma F_13680 : fetch_word rl_segs (rl (rl_delta 1010%positive) 0x13680) = Some W_13680.
Proof. rl_F 10%nat cc_13660. Qed.
Lemma F_13684 : fetch_word rl_segs (rl (rl_delta 1010%positive) 0x13684) = Some W_13684.
Proof. rl_F 10%nat cc_13660. Qed.
Lemma F_13688 : fetch_word rl_segs (rl (rl_delta 1010%positive) 0x13688) = Some W_13688.
Proof. rl_F 10%nat cc_13660. Qed.
Lemma F_1368c : fetch_word rl_segs (rl (rl_delta 1010%positive) 0x1368c) = Some W_1368c.
Proof. rl_F 10%nat cc_13660. Qed.
Lemma F_13690 : fetch_word rl_segs (rl (rl_delta 1010%positive) 0x13690) = Some W_13690.
Proof. rl_F 10%nat cc_13660. Qed.
Lemma F_13694 : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x13694) = Some W_13694.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_13698 : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x13698) = Some W_13698.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_1369c : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x1369c) = Some W_1369c.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_136a0 : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x136a0) = Some W_136a0.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_136a4 : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x136a4) = Some W_136a4.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_136a8 : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x136a8) = Some W_136a8.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_136ac : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x136ac) = Some W_136ac.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_136b0 : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x136b0) = Some W_136b0.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_136b4 : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x136b4) = Some W_136b4.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_136b8 : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x136b8) = Some W_136b8.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_136bc : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x136bc) = Some W_136bc.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_136c0 : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x136c0) = Some W_136c0.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_136c4 : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x136c4) = Some W_136c4.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_136c8 : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x136c8) = Some W_136c8.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_136cc : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x136cc) = Some W_136cc.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_136d0 : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x136d0) = Some W_136d0.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_136d4 : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x136d4) = Some W_136d4.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_136d8 : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x136d8) = Some W_136d8.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_136dc : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x136dc) = Some W_136dc.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_136e0 : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x136e0) = Some W_136e0.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_136e4 : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x136e4) = Some W_136e4.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_136e8 : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x136e8) = Some W_136e8.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_136ec : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x136ec) = Some W_136ec.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_136f0 : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x136f0) = Some W_136f0.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_136f4 : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x136f4) = Some W_136f4.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_136f8 : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x136f8) = Some W_136f8.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_136fc : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x136fc) = Some W_136fc.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_13700 : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x13700) = Some W_13700.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_13704 : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x13704) = Some W_13704.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_1370c : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x1370c) = Some W_1370c.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_13718 : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x13718) = Some W_13718.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_1371c : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x1371c) = Some W_1371c.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_13720 : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x13720) = Some W_13720.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_13724 : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x13724) = Some W_13724.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_13728 : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x13728) = Some W_13728.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_1372c : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x1372c) = Some W_1372c.
Proof. rl_F 11%nat cc_13694. Qed.
Lemma F_13730 : fetch_word rl_segs (rl (rl_delta 1012%positive) 0x13730) = Some W_13730.
Proof. rl_F 12%nat cc_13730. Qed.
Lemma F_13734 : fetch_word rl_segs (rl (rl_delta 1012%positive) 0x13734) = Some W_13734.
Proof. rl_F 12%nat cc_13730. Qed.
Lemma F_13738 : fetch_word rl_segs (rl (rl_delta 1012%positive) 0x13738) = Some W_13738.
Proof. rl_F 12%nat cc_13730. Qed.
Lemma F_1373c : fetch_word rl_segs (rl (rl_delta 1012%positive) 0x1373c) = Some W_1373c.
Proof. rl_F 12%nat cc_13730. Qed.
Lemma F_13740 : fetch_word rl_segs (rl (rl_delta 1012%positive) 0x13740) = Some W_13740.
Proof. rl_F 12%nat cc_13730. Qed.
Lemma F_13750 : fetch_word rl_segs (rl (rl_delta 1012%positive) 0x13750) = Some W_13750.
Proof. rl_F 12%nat cc_13730. Qed.
Lemma F_13754 : fetch_word rl_segs (rl (rl_delta 1012%positive) 0x13754) = Some W_13754.
Proof. rl_F 12%nat cc_13730. Qed.
Lemma F_13758 : fetch_word rl_segs (rl (rl_delta 1012%positive) 0x13758) = Some W_13758.
Proof. rl_F 12%nat cc_13730. Qed.
Lemma F_1375c : fetch_word rl_segs (rl (rl_delta 1012%positive) 0x1375c) = Some W_1375c.
Proof. rl_F 12%nat cc_13730. Qed.
Lemma F_13760 : fetch_word rl_segs (rl (rl_delta 1012%positive) 0x13760) = Some W_13760.
Proof. rl_F 12%nat cc_13730. Qed.
Lemma F_1377c : fetch_word rl_segs (rl (rl_delta 1014%positive) 0x1377c) = Some W_1377c.
Proof. rl_F 14%nat cc_1377c. Qed.
Lemma F_13790 : fetch_word rl_segs (rl (rl_delta 1014%positive) 0x13790) = Some W_13790.
Proof. rl_F 14%nat cc_1377c. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition W_1309c : bv 32 := rl_w OP_JAL 0x1309c.
Lemma F_1309c : fetch_word rl_segs (rl (rl_delta 1000%positive) 0x1309c) = Some W_1309c.
Proof. exact (rl_site_F 4%nat cs_1309c eq_refl). Qed.
Lemma D_1309c : decode_any W_1309c = Some (Jal 0 (rl_imm21 0x1309c), 4%Z).
Proof. exact (rl_site_D 4%nat cs_1309c eq_refl). Qed.
(* [comment removed for export] *)
Definition W_1367c : bv 32 := rl_w OP_JAL 0x1367c.
Lemma F_1367c : fetch_word rl_segs (rl (rl_delta 1010%positive) 0x1367c) = Some W_1367c.
Proof. exact (rl_site_F 101%nat cs_1367c eq_refl). Qed.
Lemma D_1367c : decode_any W_1367c = Some (Jal 1 (rl_imm21 0x1367c), 4%Z).
Proof. exact (rl_site_D 101%nat cs_1367c eq_refl). Qed.
(* [comment removed for export] *)
Definition W_1374c : bv 32 := rl_w OP_JAL 0x1374c.
Lemma F_1374c : fetch_word rl_segs (rl (rl_delta 1012%positive) 0x1374c) = Some W_1374c.
Proof. exact (rl_site_F 107%nat cs_1374c eq_refl). Qed.
Lemma D_1374c : decode_any W_1374c = Some (Jal 1 (rl_imm21 0x1374c), 4%Z).
Proof. exact (rl_site_D 107%nat cs_1374c eq_refl). Qed.
(* [comment removed for export] *)
Definition W_13084 : bv 32 := rl_w OP_AUIPC 0x13084.
Lemma F_13084 : fetch_word rl_segs (rl (rl_delta 1000%positive) 0x13084) = Some W_13084.
Proof. exact (rl_site_F 0%nat cs_13084 eq_refl). Qed.
Lemma D_13084 : decode_any W_13084 = Some (Auipc 3 (rl_imm20 0x13084), 4%Z).
Proof. exact (rl_site_D 0%nat cs_13084 eq_refl). Qed.
(* [comment removed for export] *)
Definition W_13088 : bv 32 := rl_w OP_IMM 0x13088.
Lemma F_13088 : fetch_word rl_segs (rl (rl_delta 1000%positive) 0x13088) = Some W_13088.
Proof. exact (rl_site_F 1%nat cs_13088 eq_refl). Qed.
Lemma D_13088 : decode_any W_13088 = Some (OpImm ALU_ADD 3 3 (rl_imm12 0x13088), 4%Z).
Proof. exact (rl_site_D 1%nat cs_13088 eq_refl). Qed.
(* [comment removed for export] *)
Definition W_13090 : bv 32 := rl_w OP_AUIPC 0x13090.
Lemma F_13090 : fetch_word rl_segs (rl (rl_delta 1000%positive) 0x13090) = Some W_13090.
Proof. exact (rl_site_F 2%nat cs_13090 eq_refl). Qed.
Lemma D_13090 : decode_any W_13090 = Some (Auipc 11 (rl_imm20 0x13090), 4%Z).
Proof. exact (rl_site_D 2%nat cs_13090 eq_refl). Qed.
(* [comment removed for export] *)
Definition W_13094 : bv 32 := rl_w OP_IMM 0x13094.
Lemma F_13094 : fetch_word rl_segs (rl (rl_delta 1000%positive) 0x13094) = Some W_13094.
Proof. exact (rl_site_F 3%nat cs_13094 eq_refl). Qed.
Lemma D_13094 : decode_any W_13094 = Some (OpImm ALU_ADD 11 11 (rl_imm12 0x13094), 4%Z).
Proof. exact (rl_site_D 3%nat cs_13094 eq_refl). Qed.
(* [comment removed for export] *)
Definition W_130a4 : bv 32 := rl_w OP_AUIPC 0x130a4.
Lemma F_130a4 : fetch_word rl_segs (rl (rl_delta 1001%positive) 0x130a4) = Some W_130a4.
Proof. exact (rl_site_F 5%nat cs_130a4 eq_refl). Qed.
Lemma D_130a4 : decode_any W_130a4 = Some (Auipc 12 (rl_imm20 0x130a4), 4%Z).
Proof. exact (rl_site_D 5%nat cs_130a4 eq_refl). Qed.
(* [comment removed for export] *)
Definition W_130a8 : bv 32 := rl_w OP_AUIPC 0x130a8.
Lemma F_130a8 : fetch_word rl_segs (rl (rl_delta 1001%positive) 0x130a8) = Some W_130a8.
Proof. exact (rl_site_F 6%nat cs_130a8 eq_refl). Qed.
Lemma D_130a8 : decode_any W_130a8 = Some (Auipc 13 (rl_imm20 0x130a8), 4%Z).
Proof. exact (rl_site_D 6%nat cs_130a8 eq_refl). Qed.
(* [comment removed for export] *)
Definition W_130ac : bv 32 := rl_w OP_AUIPC 0x130ac.
Lemma F_130ac : fetch_word rl_segs (rl (rl_delta 1001%positive) 0x130ac) = Some W_130ac.
Proof. exact (rl_site_F 7%nat cs_130ac eq_refl). Qed.
Lemma D_130ac : decode_any W_130ac = Some (Auipc 14 (rl_imm20 0x130ac), 4%Z).
Proof. exact (rl_site_D 7%nat cs_130ac eq_refl). Qed.
(* [comment removed for export] *)
Definition W_130b0 : bv 32 := rl_w OP_LOAD 0x130b0.
Lemma F_130b0 : fetch_word rl_segs (rl (rl_delta 1001%positive) 0x130b0) = Some W_130b0.
Proof. exact (rl_site_F 8%nat cs_130b0 eq_refl). Qed.
Lemma D_130b0 : decode_any W_130b0 = Some (Load SZ8 true 15 12 (rl_imm12 0x130b0), 4%Z).
Proof. exact (rl_site_D 8%nat cs_130b0 eq_refl). Qed.
(* [comment removed for export] *)
Definition W_130b4 : bv 32 := rl_w OP_LOAD 0x130b4.
Lemma F_130b4 : fetch_word rl_segs (rl (rl_delta 1001%positive) 0x130b4) = Some W_130b4.
Proof. exact (rl_site_F 9%nat cs_130b4 eq_refl). Qed.
Lemma D_130b4 : decode_any W_130b4 = Some (Load SZ8 true 13 13 (rl_imm12 0x130b4), 4%Z).
Proof. exact (rl_site_D 9%nat cs_130b4 eq_refl). Qed.
(* [comment removed for export] *)
Definition W_130b8 : bv 32 := rl_w OP_LOAD 0x130b8.
Lemma F_130b8 : fetch_word rl_segs (rl (rl_delta 1001%positive) 0x130b8) = Some W_130b8.
Proof. exact (rl_site_F 10%nat cs_130b8 eq_refl). Qed.
Lemma D_130b8 : decode_any W_130b8 = Some (Load SZ8 true 14 14 (rl_imm12 0x130b8), 4%Z).
Proof. exact (rl_site_D 10%nat cs_130b8 eq_refl). Qed.
(* [comment removed for export] *)
Definition W_130c8 : bv 32 := rl_w OP_JAL 0x130c8.
Lemma F_130c8 : fetch_word rl_segs (rl (rl_delta 1001%positive) 0x130c8) = Some W_130c8.
Proof. exact (rl_site_F 11%nat cs_130c8 eq_refl). Qed.
Lemma D_130c8 : decode_any W_130c8 = Some (Jal 0 (rl_imm21 0x130c8), 4%Z).
Proof. exact (rl_site_D 11%nat cs_130c8 eq_refl). Qed.
(* [comment removed for export] *)
Definition W_130dc : bv 32 := rl_w OP_AUIPC 0x130dc.
Lemma F_130dc : fetch_word rl_segs (rl (rl_delta 1002%positive) 0x130dc) = Some W_130dc.
Proof. exact (rl_site_F 12%nat cs_130dc eq_refl). Qed.
Lemma D_130dc : decode_any W_130dc = Some (Auipc 10 (rl_imm20 0x130dc), 4%Z).
Proof. exact (rl_site_D 12%nat cs_130dc eq_refl). Qed.
(* [comment removed for export] *)
Definition W_130e0 : bv 32 := rl_w OP_IMM 0x130e0.
Lemma F_130e0 : fetch_word rl_segs (rl (rl_delta 1002%positive) 0x130e0) = Some W_130e0.
Proof. exact (rl_site_F 13%nat cs_130e0 eq_refl). Qed.
Lemma D_130e0 : decode_any W_130e0 = Some (OpImm ALU_ADD 10 10 (rl_imm12 0x130e0), 4%Z).
Proof. exact (rl_site_D 13%nat cs_130e0 eq_refl). Qed.
(* [comment removed for export] *)
Definition W_130f8 : bv 32 := rl_w OP_AUIPC 0x130f8.
Lemma F_130f8 : fetch_word rl_segs (rl (rl_delta 1002%positive) 0x130f8) = Some W_130f8.
Proof. exact (rl_site_F 14%nat cs_130f8 eq_refl). Qed.
Lemma D_130f8 : decode_any W_130f8 = Some (Auipc 10 (rl_imm20 0x130f8), 4%Z).
Proof. exact (rl_site_D 14%nat cs_130f8 eq_refl). Qed.
(* [comment removed for export] *)
Definition W_130fc : bv 32 := rl_w OP_IMM 0x130fc.
Lemma F_130fc : fetch_word rl_segs (rl (rl_delta 1002%positive) 0x130fc) = Some W_130fc.
Proof. exact (rl_site_F 15%nat cs_130fc eq_refl). Qed.
Lemma D_130fc : decode_any W_130fc = Some (OpImm ALU_ADD 11 10 (rl_imm12 0x130fc), 4%Z).
Proof. exact (rl_site_D 15%nat cs_130fc eq_refl). Qed.
(* [comment removed for export] *)
Definition W_13108 : bv 32 := rl_w OP_AUIPC 0x13108.
Lemma F_13108 : fetch_word rl_segs (rl (rl_delta 1002%positive) 0x13108) = Some W_13108.
Proof. exact (rl_site_F 16%nat cs_13108 eq_refl). Qed.
Lemma D_13108 : decode_any W_13108 = Some (Auipc 10 (rl_imm20 0x13108), 4%Z).
Proof. exact (rl_site_D 16%nat cs_13108 eq_refl). Qed.
(* [comment removed for export] *)
Definition W_1310c : bv 32 := rl_w OP_LOAD 0x1310c.
Lemma F_1310c : fetch_word rl_segs (rl (rl_delta 1002%positive) 0x1310c) = Some W_1310c.
Proof. exact (rl_site_F 17%nat cs_1310c eq_refl). Qed.
Lemma D_1310c : decode_any W_1310c = Some (Load SZ8 true 10 10 (rl_imm12 0x1310c), 4%Z).
Proof. exact (rl_site_D 17%nat cs_1310c eq_refl). Qed.
(* [comment removed for export] *)
Definition W_13150 : bv 32 := rl_w OP_AUIPC 0x13150.
Lemma F_13150 : fetch_word rl_segs (rl (rl_delta 1003%positive) 0x13150) = Some W_13150.
Proof. exact (rl_site_F 22%nat cs_13150 eq_refl). Qed.
Lemma D_13150 : decode_any W_13150 = Some (Auipc 10 (rl_imm20 0x13150), 4%Z).
Proof. exact (rl_site_D 22%nat cs_13150 eq_refl). Qed.
(* [comment removed for export] *)
Definition W_13154 : bv 32 := rl_w OP_IMM 0x13154.
Lemma F_13154 : fetch_word rl_segs (rl (rl_delta 1003%positive) 0x13154) = Some W_13154.
Proof. exact (rl_site_F 23%nat cs_13154 eq_refl). Qed.
Lemma D_13154 : decode_any W_13154 = Some (OpImm ALU_ADD 10 10 (rl_imm12 0x13154), 4%Z).
Proof. exact (rl_site_D 23%nat cs_13154 eq_refl). Qed.
(* [comment removed for export] *)
Definition W_1316c : bv 32 := rl_w OP_AUIPC 0x1316c.
Lemma F_1316c : fetch_word rl_segs (rl (rl_delta 1003%positive) 0x1316c) = Some W_1316c.
Proof. exact (rl_site_F 24%nat cs_1316c eq_refl). Qed.
Lemma D_1316c : decode_any W_1316c = Some (Auipc 10 (rl_imm20 0x1316c), 4%Z).
Proof. exact (rl_site_D 24%nat cs_1316c eq_refl). Qed.
(* [comment removed for export] *)
Definition W_13170 : bv 32 := rl_w OP_IMM 0x13170.
Lemma F_13170 : fetch_word rl_segs (rl (rl_delta 1003%positive) 0x13170) = Some W_13170.
Proof. exact (rl_site_F 25%nat cs_13170 eq_refl). Qed.
Lemma D_13170 : decode_any W_13170 = Some (OpImm ALU_ADD 11 10 (rl_imm12 0x13170), 4%Z).
Proof. exact (rl_site_D 25%nat cs_13170 eq_refl). Qed.
(* [comment removed for export] *)
Definition W_1317c : bv 32 := rl_w OP_AUIPC 0x1317c.
Lemma F_1317c : fetch_word rl_segs (rl (rl_delta 1003%positive) 0x1317c) = Some W_1317c.
Proof. exact (rl_site_F 26%nat cs_1317c eq_refl). Qed.
Lemma D_1317c : decode_any W_1317c = Some (Auipc 10 (rl_imm20 0x1317c), 4%Z).
Proof. exact (rl_site_D 26%nat cs_1317c eq_refl). Qed.
(* [comment removed for export] *)
Definition W_13180 : bv 32 := rl_w OP_LOAD 0x13180.
Lemma F_13180 : fetch_word rl_segs (rl (rl_delta 1003%positive) 0x13180) = Some W_13180.
Proof. exact (rl_site_F 27%nat cs_13180 eq_refl). Qed.
Lemma D_13180 : decode_any W_13180 = Some (Load SZ8 true 10 10 (rl_imm12 0x13180), 4%Z).
Proof. exact (rl_site_D 27%nat cs_13180 eq_refl). Qed.
(* [comment removed for export] *)
Definition W_131a0 : bv 32 := rl_w OP_AUIPC 0x131a0.
Lemma F_131a0 : fetch_word rl_segs (rl (rl_delta 1003%positive) 0x131a0) = Some W_131a0.
Proof. exact (rl_site_F 30%nat cs_131a0 eq_refl). Qed.
Lemma D_131a0 : decode_any W_131a0 = Some (Auipc 10 (rl_imm20 0x131a0), 4%Z).
Proof. exact (rl_site_D 30%nat cs_131a0 eq_refl). Qed.
(* [comment removed for export] *)
Definition W_131a4 : bv 32 := rl_w OP_LOAD 0x131a4.
Lemma F_131a4 : fetch_word rl_segs (rl (rl_delta 1003%positive) 0x131a4) = Some W_131a4.
Proof. exact (rl_site_F 31%nat cs_131a4 eq_refl). Qed.
Lemma D_131a4 : decode_any W_131a4 = Some (Load SZ8 true 10 10 (rl_imm12 0x131a4), 4%Z).
Proof. exact (rl_site_D 31%nat cs_131a4 eq_refl). Qed.
(* [comment removed for export] *)
Definition W_13674 : bv 32 := rl_w OP_AUIPC 0x13674.
Lemma F_13674 : fetch_word rl_segs (rl (rl_delta 1010%positive) 0x13674) = Some W_13674.
Proof. exact (rl_site_F 99%nat cs_13674 eq_refl). Qed.
Lemma D_13674 : decode_any W_13674 = Some (Auipc 10 (rl_imm20 0x13674), 4%Z).
Proof. exact (rl_site_D 99%nat cs_13674 eq_refl). Qed.
(* [comment removed for export] *)
Definition W_13678 : bv 32 := rl_w OP_IMM 0x13678.
Lemma F_13678 : fetch_word rl_segs (rl (rl_delta 1010%positive) 0x13678) = Some W_13678.
Proof. exact (rl_site_F 100%nat cs_13678 eq_refl). Qed.
Lemma D_13678 : decode_any W_13678 = Some (OpImm ALU_ADD 10 10 (rl_imm12 0x13678), 4%Z).
Proof. exact (rl_site_D 100%nat cs_13678 eq_refl). Qed.
(* [comment removed for export] *)
Definition W_13708 : bv 32 := rl_w OP_JAL 0x13708.
Lemma F_13708 : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x13708) = Some W_13708.
Proof. exact (rl_site_F 102%nat cs_13708 eq_refl). Qed.
Lemma D_13708 : decode_any W_13708 = Some (Jal 1 (rl_imm21 0x13708), 4%Z).
Proof. exact (rl_site_D 102%nat cs_13708 eq_refl). Qed.
(* [comment removed for export] *)
Definition W_13710 : bv 32 := rl_w OP_AUIPC 0x13710.
Lemma F_13710 : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x13710) = Some W_13710.
Proof. exact (rl_site_F 103%nat cs_13710 eq_refl). Qed.
Lemma D_13710 : decode_any W_13710 = Some (Auipc 10 (rl_imm20 0x13710), 4%Z).
Proof. exact (rl_site_D 103%nat cs_13710 eq_refl). Qed.
(* [comment removed for export] *)
Definition W_13714 : bv 32 := rl_w OP_LOAD 0x13714.
Lemma F_13714 : fetch_word rl_segs (rl (rl_delta 1011%positive) 0x13714) = Some W_13714.
Proof. exact (rl_site_F 104%nat cs_13714 eq_refl). Qed.
Lemma D_13714 : decode_any W_13714 = Some (Load SZ8 true 11 10 (rl_imm12 0x13714), 4%Z).
Proof. exact (rl_site_D 104%nat cs_13714 eq_refl). Qed.
(* [comment removed for export] *)
Definition W_13744 : bv 32 := rl_w OP_AUIPC 0x13744.
Lemma F_13744 : fetch_word rl_segs (rl (rl_delta 1012%positive) 0x13744) = Some W_13744.
Proof. exact (rl_site_F 105%nat cs_13744 eq_refl). Qed.
Lemma D_13744 : decode_any W_13744 = Some (Auipc 10 (rl_imm20 0x13744), 4%Z).
Proof. exact (rl_site_D 105%nat cs_13744 eq_refl). Qed.
(* [comment removed for export] *)
Definition W_13748 : bv 32 := rl_w OP_IMM 0x13748.
Lemma F_13748 : fetch_word rl_segs (rl (rl_delta 1012%positive) 0x13748) = Some W_13748.
Proof. exact (rl_site_F 106%nat cs_13748 eq_refl). Qed.
Lemma D_13748 : decode_any W_13748 = Some (OpImm ALU_ADD 10 10 (rl_imm12 0x13748), 4%Z).
Proof. exact (rl_site_D 106%nat cs_13748 eq_refl). Qed.
(* [comment removed for export] *)
Definition W_13788 : bv 32 := rl_w OP_AUIPC 0x13788.
Lemma F_13788 : fetch_word rl_segs (rl (rl_delta 1014%positive) 0x13788) = Some W_13788.
Proof. exact (rl_site_F 113%nat cs_13788 eq_refl). Qed.
Lemma D_13788 : decode_any W_13788 = Some (Auipc 11 (rl_imm20 0x13788), 4%Z).
Proof. exact (rl_site_D 113%nat cs_13788 eq_refl). Qed.
(* [comment removed for export] *)
Definition W_1378c : bv 32 := rl_w OP_STORE 0x1378c.
Lemma F_1378c : fetch_word rl_segs (rl (rl_delta 1014%positive) 0x1378c) = Some W_1378c.
Proof. exact (rl_site_F 114%nat cs_1378c eq_refl). Qed.
Lemma D_1378c : decode_any W_1378c = Some (Store SZ8 11 10 (rl_imm12 0x1378c), 4%Z).
Proof. exact (rl_site_D 114%nat cs_1378c eq_refl). Qed.
End F.

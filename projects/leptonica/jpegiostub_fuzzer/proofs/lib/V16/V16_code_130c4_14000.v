(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.H Require GcFlushU16.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.jpegiostub_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_13634 : bv 32 := 0xfe010113.
Lemma F_13634 : fetch_word Ubsan.M.loaded_segments (0x13738 : word) = Some W_13634.
Proof. vm_refl. Qed.
Lemma D_13634 : decode_any W_13634 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13638 : bv 32 := 0x00113c23.
Lemma F_13638 : fetch_word Ubsan.M.loaded_segments (0x1373c : word) = Some W_13638.
Proof. vm_refl. Qed.
Lemma D_13638 : decode_any W_13638 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1363c : bv 32 := 0x00813823.
Lemma F_1363c : fetch_word Ubsan.M.loaded_segments (0x13740 : word) = Some W_1363c.
Proof. vm_refl. Qed.
Lemma D_1363c : decode_any W_1363c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13640 : bv 32 := 0x00913423.
Lemma F_13640 : fetch_word Ubsan.M.loaded_segments (0x13744 : word) = Some W_13640.
Proof. vm_refl. Qed.
Lemma D_13640 : decode_any W_13640 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13644 : bv 32 := 0x00058413.
Lemma F_13644 : fetch_word Ubsan.M.loaded_segments (0x13748 : word) = Some W_13644.
Proof. vm_refl. Qed.
Lemma D_13644 : decode_any W_13644 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13648 : bv 32 := 0x00300593.
Lemma F_13648 : fetch_word Ubsan.M.loaded_segments (0x1374c : word) = Some W_13648.
Proof. vm_refl. Qed.
Lemma D_13648 : decode_any W_13648 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1364c : bv 32 := 0x02b46c63.
Lemma F_1364c : fetch_word Ubsan.M.loaded_segments (0x13750 : word) = Some W_1364c.
Proof. vm_refl. Qed.
Lemma D_1364c : decode_any W_1364c = Some (Branch BC_LTU 8 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13650 : bv 32 := 0x00050493.
Lemma F_13650 : fetch_word Ubsan.M.loaded_segments (0x13754 : word) = Some W_13650.
Proof. vm_refl. Qed.
Lemma D_13650 : decode_any W_13650 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13654 : bv 32 := 0x00000517.
Lemma F_13654 : fetch_word Ubsan.M.loaded_segments (0x13758 : word) = Some W_13654.
Proof. vm_refl. Qed.
Lemma D_13654 : decode_any W_13654 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13658 : bv 32 := 0x04850513.
Lemma F_13658 : fetch_word Ubsan.M.loaded_segments (0x1375c : word) = Some W_13658.
Proof. vm_refl. Qed.
Lemma D_13658 : decode_any W_13658 = Some (OpImm ALU_ADD 10 10 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1365c : bv 32 := 0x160000ef.
Lemma F_1365c : fetch_word Ubsan.M.loaded_segments (0x13760 : word) = Some W_1365c.
Proof. vm_refl. Qed.
Lemma D_1365c : decode_any W_1365c = Some (Jal 1 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13660 : bv 32 := 0x00048513.
Lemma F_13660 : fetch_word Ubsan.M.loaded_segments (0x13764 : word) = Some W_13660.
Proof. vm_refl. Qed.
Lemma D_13660 : decode_any W_13660 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13664 : bv 32 := 0x00040593.
Lemma F_13664 : fetch_word Ubsan.M.loaded_segments (0x13768 : word) = Some W_13664.
Proof. vm_refl. Qed.
Lemma D_13664 : decode_any W_13664 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13668 : bv 32 := 0x2c9010ef.
Lemma F_13668 : fetch_word Ubsan.M.loaded_segments (0x1376c : word) = Some W_13668.
Proof. vm_refl. Qed.
Lemma D_13668 : decode_any W_13668 = Some (Jal 1 6856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1366c : bv 32 := 0x00a13023.
Lemma F_1366c : fetch_word Ubsan.M.loaded_segments (0x13770 : word) = Some W_1366c.
Proof. vm_refl. Qed.
Lemma D_1366c : decode_any W_1366c = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13670 : bv 32 := 0x00050a63.
Lemma F_13670 : fetch_word Ubsan.M.loaded_segments (0x13774 : word) = Some W_13670.
Proof. vm_refl. Qed.
Lemma D_13670 : decode_any W_13670 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13674 : bv 32 := 0x00000593.
Lemma F_13674 : fetch_word Ubsan.M.loaded_segments (0x13778 : word) = Some W_13674.
Proof. vm_refl. Qed.
Lemma D_13674 : decode_any W_13674 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13678 : bv 32 := 0x24d010ef.
Lemma F_13678 : fetch_word Ubsan.M.loaded_segments (0x1377c : word) = Some W_13678.
Proof. vm_refl. Qed.
Lemma D_13678 : decode_any W_13678 = Some (Jal 1 6732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1367c : bv 32 := 0x00010513.
Lemma F_1367c : fetch_word Ubsan.M.loaded_segments (0x13780 : word) = Some W_1367c.
Proof. vm_refl. Qed.
Lemma D_1367c : decode_any W_1367c = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13680 : bv 32 := 0x6b0000ef.
Lemma F_13680 : fetch_word Ubsan.M.loaded_segments (0x13784 : word) = Some W_13680.
Proof. vm_refl. Qed.
Lemma D_13680 : decode_any W_13680 = Some (Jal 1 1712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13684 : bv 32 := 0x00000513.
Lemma F_13684 : fetch_word Ubsan.M.loaded_segments (0x13788 : word) = Some W_13684.
Proof. vm_refl. Qed.
Lemma D_13684 : decode_any W_13684 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13688 : bv 32 := 0x01813083.
Lemma F_13688 : fetch_word Ubsan.M.loaded_segments (0x1378c : word) = Some W_13688.
Proof. vm_refl. Qed.
Lemma D_13688 : decode_any W_13688 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1368c : bv 32 := 0x01013403.
Lemma F_1368c : fetch_word Ubsan.M.loaded_segments (0x13790 : word) = Some W_1368c.
Proof. vm_refl. Qed.
Lemma D_1368c : decode_any W_1368c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13690 : bv 32 := 0x00813483.
Lemma F_13690 : fetch_word Ubsan.M.loaded_segments (0x13794 : word) = Some W_13690.
Proof. vm_refl. Qed.
Lemma D_13690 : decode_any W_13690 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13694 : bv 32 := 0x02010113.
Lemma F_13694 : fetch_word Ubsan.M.loaded_segments (0x13798 : word) = Some W_13694.
Proof. vm_refl. Qed.
Lemma D_13694 : decode_any W_13694 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13698 : bv 32 := 0x00008067.
Lemma F_13698 : fetch_word Ubsan.M.loaded_segments (0x1379c : word) = Some W_13698.
Proof. vm_refl. Qed.
Lemma D_13698 : decode_any W_13698 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_136a0 : bv 32 := 0xff010113.
Lemma F_136a0 : fetch_word Ubsan.M.loaded_segments (0x137a4 : word) = Some W_136a0.
Proof. vm_refl. Qed.
Lemma D_136a0 : decode_any W_136a0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_136a4 : bv 32 := 0x00113423.
Lemma F_136a4 : fetch_word Ubsan.M.loaded_segments (0x137a8 : word) = Some W_136a4.
Proof. vm_refl. Qed.
Lemma D_136a4 : decode_any W_136a4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_136a8 : bv 32 := 0x00813023.
Lemma F_136a8 : fetch_word Ubsan.M.loaded_segments (0x137ac : word) = Some W_136a8.
Proof. vm_refl. Qed.
Lemma D_136a8 : decode_any W_136a8 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_136ac : bv 32 := 0x00060413.
Lemma F_136ac : fetch_word Ubsan.M.loaded_segments (0x137b0 : word) = Some W_136ac.
Proof. vm_refl. Qed.
Lemma D_136ac : decode_any W_136ac = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_136b0 : bv 32 := 0x00050613.
Lemma F_136b0 : fetch_word Ubsan.M.loaded_segments (0x137b4 : word) = Some W_136b0.
Proof. vm_refl. Qed.
Lemma D_136b0 : decode_any W_136b0 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_136b4 : bv 32 := 0xffffd517.
Lemma F_136b4 : fetch_word Ubsan.M.loaded_segments (0x137b8 : word) = Some W_136b4.
Proof. vm_refl. Qed.
Lemma D_136b4 : decode_any W_136b4 = Some (Auipc 10 1048573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_136b8 : bv 32 := 0x27850513.
Lemma F_136b8 : fetch_word Ubsan.M.loaded_segments (0x137bc : word) = Some W_136b8.
Proof. vm_refl. Qed.
Lemma D_136b8 : decode_any W_136b8 = Some (OpImm ALU_ADD 10 10 632, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_136bc : bv 32 := 0x018000ef.
Lemma F_136bc : fetch_word Ubsan.M.loaded_segments (0x137c0 : word) = Some W_136bc.
Proof. vm_refl. Qed.
Lemma D_136bc : decode_any W_136bc = Some (Jal 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_136c0 : bv 32 := 0x00040513.
Lemma F_136c0 : fetch_word Ubsan.M.loaded_segments (0x137c4 : word) = Some W_136c0.
Proof. vm_refl. Qed.
Lemma D_136c0 : decode_any W_136c0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_136c4 : bv 32 := 0x00813083.
Lemma F_136c4 : fetch_word Ubsan.M.loaded_segments (0x137c8 : word) = Some W_136c4.
Proof. vm_refl. Qed.
Lemma D_136c4 : decode_any W_136c4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_136c8 : bv 32 := 0x00013403.
Lemma F_136c8 : fetch_word Ubsan.M.loaded_segments (0x137cc : word) = Some W_136c8.
Proof. vm_refl. Qed.
Lemma D_136c8 : decode_any W_136c8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_136cc : bv 32 := 0x01010113.
Lemma F_136cc : fetch_word Ubsan.M.loaded_segments (0x137d0 : word) = Some W_136cc.
Proof. vm_refl. Qed.
Lemma D_136cc : decode_any W_136cc = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_136d0 : bv 32 := 0x00008067.
Lemma F_136d0 : fetch_word Ubsan.M.loaded_segments (0x137d4 : word) = Some W_136d0.
Proof. vm_refl. Qed.
Lemma D_136d0 : decode_any W_136d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13770 : bv 32 := 0xff010113.
Lemma F_13770 : fetch_word Ubsan.M.loaded_segments (0x13874 : word) = Some W_13770.
Proof. vm_refl. Qed.
Lemma D_13770 : decode_any W_13770 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13774 : bv 32 := 0x00113423.
Lemma F_13774 : fetch_word Ubsan.M.loaded_segments (0x13878 : word) = Some W_13774.
Proof. vm_refl. Qed.
Lemma D_13774 : decode_any W_13774 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13778 : bv 32 := 0x00813023.
Lemma F_13778 : fetch_word Ubsan.M.loaded_segments (0x1387c : word) = Some W_13778.
Proof. vm_refl. Qed.
Lemma D_13778 : decode_any W_13778 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1377c : bv 32 := 0x00060413.
Lemma F_1377c : fetch_word Ubsan.M.loaded_segments (0x13880 : word) = Some W_1377c.
Proof. vm_refl. Qed.
Lemma D_1377c : decode_any W_1377c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13780 : bv 32 := 0x00050613.
Lemma F_13780 : fetch_word Ubsan.M.loaded_segments (0x13884 : word) = Some W_13780.
Proof. vm_refl. Qed.
Lemma D_13780 : decode_any W_13780 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13784 : bv 32 := 0xffffd517.
Lemma F_13784 : fetch_word Ubsan.M.loaded_segments (0x13888 : word) = Some W_13784.
Proof. vm_refl. Qed.
Lemma D_13784 : decode_any W_13784 = Some (Auipc 10 1048573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13788 : bv 32 := 0x1a850513.
Lemma F_13788 : fetch_word Ubsan.M.loaded_segments (0x1388c : word) = Some W_13788.
Proof. vm_refl. Qed.
Lemma D_13788 : decode_any W_13788 = Some (OpImm ALU_ADD 10 10 424, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1378c : bv 32 := 0xf49ff0ef.
Lemma F_1378c : fetch_word Ubsan.M.loaded_segments (0x13890 : word) = Some W_1378c.
Proof. vm_refl. Qed.
Lemma D_1378c : decode_any W_1378c = Some (Jal 1 2096968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13790 : bv 32 := 0x00040513.
Lemma F_13790 : fetch_word Ubsan.M.loaded_segments (0x13894 : word) = Some W_13790.
Proof. vm_refl. Qed.
Lemma D_13790 : decode_any W_13790 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13794 : bv 32 := 0x00813083.
Lemma F_13794 : fetch_word Ubsan.M.loaded_segments (0x13898 : word) = Some W_13794.
Proof. vm_refl. Qed.
Lemma D_13794 : decode_any W_13794 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13798 : bv 32 := 0x00013403.
Lemma F_13798 : fetch_word Ubsan.M.loaded_segments (0x1389c : word) = Some W_13798.
Proof. vm_refl. Qed.
Lemma D_13798 : decode_any W_13798 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1379c : bv 32 := 0x01010113.
Lemma F_1379c : fetch_word Ubsan.M.loaded_segments (0x138a0 : word) = Some W_1379c.
Proof. vm_refl. Qed.
Lemma D_1379c : decode_any W_1379c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_137a0 : bv 32 := 0x00008067.
Lemma F_137a0 : fetch_word Ubsan.M.loaded_segments (0x138a4 : word) = Some W_137a0.
Proof. vm_refl. Qed.
Lemma D_137a0 : decode_any W_137a0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_137bc : bv 32 := 0x00051663.
Lemma F_137bc : fetch_word Ubsan.M.loaded_segments (0x138c0 : word) = Some W_137bc.
Proof. vm_refl. Qed.
Lemma D_137bc : decode_any W_137bc = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_137c8 : bv 32 := 0x0000c597.
Lemma F_137c8 : fetch_word Ubsan.M.loaded_segments (0x138cc : word) = Some W_137c8.
Proof. vm_refl. Qed.
Lemma D_137c8 : decode_any W_137c8 = Some (Auipc 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_137cc : bv 32 := 0x56a5ba23.
Lemma F_137cc : fetch_word Ubsan.M.loaded_segments (0x138d0 : word) = Some W_137cc.
Proof. vm_refl. Qed.
Lemma D_137cc : decode_any W_137cc = Some (Store SZ8 11 10 1396, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_137d0 : bv 32 := 0x00008067.
Lemma F_137d0 : fetch_word Ubsan.M.loaded_segments (0x138d4 : word) = Some W_137d0.
Proof. vm_refl. Qed.
Lemma D_137d0 : decode_any W_137d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

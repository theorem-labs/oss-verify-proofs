(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_175b8 : bv 32 := 0xfd010113.
Lemma F_175b8 : fetch_word Ubsan.M.loaded_segments (0x176bc : word) = Some W_175b8.
Proof. vm_refl. Qed.
Lemma D_175b8 : decode_any W_175b8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_175bc : bv 32 := 0x02113423.
Lemma F_175bc : fetch_word Ubsan.M.loaded_segments (0x176c0 : word) = Some W_175bc.
Proof. vm_refl. Qed.
Lemma D_175bc : decode_any W_175bc = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_175c0 : bv 32 := 0x02813023.
Lemma F_175c0 : fetch_word Ubsan.M.loaded_segments (0x176c4 : word) = Some W_175c0.
Proof. vm_refl. Qed.
Lemma D_175c0 : decode_any W_175c0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_175c4 : bv 32 := 0x00913c23.
Lemma F_175c4 : fetch_word Ubsan.M.loaded_segments (0x176c8 : word) = Some W_175c4.
Proof. vm_refl. Qed.
Lemma D_175c4 : decode_any W_175c4 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_175c8 : bv 32 := 0x04050c63.
Lemma F_175c8 : fetch_word Ubsan.M.loaded_segments (0x176cc : word) = Some W_175c8.
Proof. vm_refl. Qed.
Lemma D_175c8 : decode_any W_175c8 = Some (Branch BC_EQ 10 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_175cc : bv 32 := 0x04058663.
Lemma F_175cc : fetch_word Ubsan.M.loaded_segments (0x176d0 : word) = Some W_175cc.
Proof. vm_refl. Qed.
Lemma D_175cc : decode_any W_175cc = Some (Branch BC_EQ 11 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_175d0 : bv 32 := 0x00757613.
Lemma F_175d0 : fetch_word Ubsan.M.loaded_segments (0x176d4 : word) = Some W_175d0.
Proof. vm_refl. Qed.
Lemma D_175d0 : decode_any W_175d0 = Some (OpImm ALU_AND 12 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_175d4 : bv 32 := 0x0c061863.
Lemma F_175d4 : fetch_word Ubsan.M.loaded_segments (0x176d8 : word) = Some W_175d4.
Proof. vm_refl. Qed.
Lemma D_175d4 : decode_any W_175d4 = Some (Branch BC_NE 12 0 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_175d8 : bv 32 := 0x03053603.
Lemma F_175d8 : fetch_word Ubsan.M.loaded_segments (0x176dc : word) = Some W_175d8.
Proof. vm_refl. Qed.
Lemma D_175d8 : decode_any W_175d8 = Some (Load SZ8 true 12 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_175dc : bv 32 := 0x00c13823.
Lemma F_175dc : fetch_word Ubsan.M.loaded_segments (0x176e0 : word) = Some W_175dc.
Proof. vm_refl. Qed.
Lemma D_175dc : decode_any W_175dc = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_175e0 : bv 32 := 0x00060e63.
Lemma F_175e0 : fetch_word Ubsan.M.loaded_segments (0x176e4 : word) = Some W_175e0.
Proof. vm_refl. Qed.
Lemma D_175e0 : decode_any W_175e0 = Some (Branch BC_EQ 12 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_175e4 : bv 32 := 0x00050413.
Lemma F_175e4 : fetch_word Ubsan.M.loaded_segments (0x176e8 : word) = Some W_175e4.
Proof. vm_refl. Qed.
Lemma D_175e4 : decode_any W_175e4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_175e8 : bv 32 := 0x01010513.
Lemma F_175e8 : fetch_word Ubsan.M.loaded_segments (0x176ec : word) = Some W_175e8.
Proof. vm_refl. Qed.
Lemma D_175e8 : decode_any W_175e8 = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_175ec : bv 32 := 0x00058493.
Lemma F_175ec : fetch_word Ubsan.M.loaded_segments (0x176f0 : word) = Some W_175ec.
Proof. vm_refl. Qed.
Lemma D_175ec : decode_any W_175ec = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_175f0 : bv 32 := 0x4ac010ef.
Lemma F_175f0 : fetch_word Ubsan.M.loaded_segments (0x176f4 : word) = Some W_175f0.
Proof. vm_refl. Qed.
Lemma D_175f0 : decode_any W_175f0 = Some (Jal 1 5292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_175f4 : bv 32 := 0x00040513.
Lemma F_175f4 : fetch_word Ubsan.M.loaded_segments (0x176f8 : word) = Some W_175f4.
Proof. vm_refl. Qed.
Lemma D_175f4 : decode_any W_175f4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_175f8 : bv 32 := 0x00048593.
Lemma F_175f8 : fetch_word Ubsan.M.loaded_segments (0x176fc : word) = Some W_175f8.
Proof. vm_refl. Qed.
Lemma D_175f8 : decode_any W_175f8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_175fc : bv 32 := 0x02b53823.
Lemma F_175fc : fetch_word Ubsan.M.loaded_segments (0x17700 : word) = Some W_175fc.
Proof. vm_refl. Qed.
Lemma D_175fc : decode_any W_175fc = Some (Store SZ8 10 11 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17600 : bv 32 := 0x00c10613.
Lemma F_17600 : fetch_word Ubsan.M.loaded_segments (0x17704 : word) = Some W_17600.
Proof. vm_refl. Qed.
Lemma D_17600 : decode_any W_17600 = Some (OpImm ALU_ADD 12 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17604 : bv 32 := 0x00058513.
Lemma F_17604 : fetch_word Ubsan.M.loaded_segments (0x17708 : word) = Some W_17604.
Proof. vm_refl. Qed.
Lemma D_17604 : decode_any W_17604 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17608 : bv 32 := 0x00000593.
Lemma F_17608 : fetch_word Ubsan.M.loaded_segments (0x1770c : word) = Some W_17608.
Proof. vm_refl. Qed.
Lemma D_17608 : decode_any W_17608 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1760c : bv 32 := 0x178010ef.
Lemma F_1760c : fetch_word Ubsan.M.loaded_segments (0x17710 : word) = Some W_1760c.
Proof. vm_refl. Qed.
Lemma D_1760c : decode_any W_1760c = Some (Jal 1 4472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17610 : bv 32 := 0x00c12503.
Lemma F_17610 : fetch_word Ubsan.M.loaded_segments (0x17714 : word) = Some W_17610.
Proof. vm_refl. Qed.
Lemma D_17610 : decode_any W_17610 = Some (Load SZ4 true 10 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17614 : bv 32 := 0x04050463.
Lemma F_17614 : fetch_word Ubsan.M.loaded_segments (0x17718 : word) = Some W_17614.
Proof. vm_refl. Qed.
Lemma D_17614 : decode_any W_17614 = Some (Branch BC_EQ 10 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17618 : bv 32 := 0x00000513.
Lemma F_17618 : fetch_word Ubsan.M.loaded_segments (0x1771c : word) = Some W_17618.
Proof. vm_refl. Qed.
Lemma D_17618 : decode_any W_17618 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1761c : bv 32 := 0x0740006f.
Lemma F_1761c : fetch_word Ubsan.M.loaded_segments (0x17720 : word) = Some W_1761c.
Proof. vm_refl. Qed.
Lemma D_1761c : decode_any W_1761c = Some (Jal 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17620 : bv 32 := 0x0001d517.
Lemma F_17620 : fetch_word Ubsan.M.loaded_segments (0x17724 : word) = Some W_17620.
Proof. vm_refl. Qed.
Lemma D_17620 : decode_any W_17620 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17624 : bv 32 := 0xad453503.
Lemma F_17624 : fetch_word Ubsan.M.loaded_segments (0x17728 : word) = Some W_17624.
Proof. vm_refl. Qed.
Lemma D_17624 : decode_any W_17624 = Some (Load SZ8 true 10 10 2772, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17628 : bv 32 := 0x00052503.
Lemma F_17628 : fetch_word Ubsan.M.loaded_segments (0x1772c : word) = Some W_17628.
Proof. vm_refl. Qed.
Lemma D_17628 : decode_any W_17628 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1762c : bv 32 := 0x00500593.
Lemma F_1762c : fetch_word Ubsan.M.loaded_segments (0x17730 : word) = Some W_1762c.
Proof. vm_refl. Qed.
Lemma D_1762c : decode_any W_1762c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17630 : bv 32 := 0x04a5ce63.
Lemma F_17630 : fetch_word Ubsan.M.loaded_segments (0x17734 : word) = Some W_17630.
Proof. vm_refl. Qed.
Lemma D_17630 : decode_any W_17630 = Some (Branch BC_LT 11 10 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17634 : bv 32 := 0xffff9517.
Lemma F_17634 : fetch_word Ubsan.M.loaded_segments (0x17738 : word) = Some W_17634.
Proof. vm_refl. Qed.
Lemma D_17634 : decode_any W_17634 = Some (Auipc 10 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17638 : bv 32 := 0xffff9597.
Lemma F_17638 : fetch_word Ubsan.M.loaded_segments (0x1773c : word) = Some W_17638.
Proof. vm_refl. Qed.
Lemma D_17638 : decode_any W_17638 = Some (Auipc 11 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1763c : bv 32 := 0xc9350513.
Lemma F_1763c : fetch_word Ubsan.M.loaded_segments (0x17740 : word) = Some W_1763c.
Proof. vm_refl. Qed.
Lemma D_1763c : decode_any W_1763c = Some (OpImm ALU_ADD 10 10 3219, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17640 : bv 32 := 0x40c58593.
Lemma F_17640 : fetch_word Ubsan.M.loaded_segments (0x17744 : word) = Some W_17640.
Proof. vm_refl. Qed.
Lemma D_17640 : decode_any W_17640 = Some (OpImm ALU_ADD 11 11 1036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17644 : bv 32 := 0x00100613.
Lemma F_17644 : fetch_word Ubsan.M.loaded_segments (0x17748 : word) = Some W_17644.
Proof. vm_refl. Qed.
Lemma D_17644 : decode_any W_17644 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17648 : bv 32 := 0x02813083.
Lemma F_17648 : fetch_word Ubsan.M.loaded_segments (0x1774c : word) = Some W_17648.
Proof. vm_refl. Qed.
Lemma D_17648 : decode_any W_17648 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1764c : bv 32 := 0x02013403.
Lemma F_1764c : fetch_word Ubsan.M.loaded_segments (0x17750 : word) = Some W_1764c.
Proof. vm_refl. Qed.
Lemma D_1764c : decode_any W_1764c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17650 : bv 32 := 0x01813483.
Lemma F_17650 : fetch_word Ubsan.M.loaded_segments (0x17754 : word) = Some W_17650.
Proof. vm_refl. Qed.
Lemma D_17650 : decode_any W_17650 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17654 : bv 32 := 0x03010113.
Lemma F_17654 : fetch_word Ubsan.M.loaded_segments (0x17758 : word) = Some W_17654.
Proof. vm_refl. Qed.
Lemma D_17654 : decode_any W_17654 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17658 : bv 32 := 0xd91fd06f.
Lemma F_17658 : fetch_word Ubsan.M.loaded_segments (0x1775c : word) = Some W_17658.
Proof. vm_refl. Qed.
Lemma D_17658 : decode_any W_17658 = Some (Jal 0 2088336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1765c : bv 32 := 0x0001d517.
Lemma F_1765c : fetch_word Ubsan.M.loaded_segments (0x17760 : word) = Some W_1765c.
Proof. vm_refl. Qed.
Lemma D_1765c : decode_any W_1765c = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17660 : bv 32 := 0xa9853503.
Lemma F_17660 : fetch_word Ubsan.M.loaded_segments (0x17764 : word) = Some W_17660.
Proof. vm_refl. Qed.
Lemma D_17660 : decode_any W_17660 = Some (Load SZ8 true 10 10 2712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17664 : bv 32 := 0x00052503.
Lemma F_17664 : fetch_word Ubsan.M.loaded_segments (0x17768 : word) = Some W_17664.
Proof. vm_refl. Qed.
Lemma D_17664 : decode_any W_17664 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17668 : bv 32 := 0x00500593.
Lemma F_17668 : fetch_word Ubsan.M.loaded_segments (0x1776c : word) = Some W_17668.
Proof. vm_refl. Qed.
Lemma D_17668 : decode_any W_17668 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1766c : bv 32 := 0x02a5c063.
Lemma F_1766c : fetch_word Ubsan.M.loaded_segments (0x17770 : word) = Some W_1766c.
Proof. vm_refl. Qed.
Lemma D_1766c : decode_any W_1766c = Some (Branch BC_LT 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17670 : bv 32 := 0xffffa517.
Lemma F_17670 : fetch_word Ubsan.M.loaded_segments (0x17774 : word) = Some W_17670.
Proof. vm_refl. Qed.
Lemma D_17670 : decode_any W_17670 = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17674 : bv 32 := 0xffff9597.
Lemma F_17674 : fetch_word Ubsan.M.loaded_segments (0x17778 : word) = Some W_17674.
Proof. vm_refl. Qed.
Lemma D_17674 : decode_any W_17674 = Some (Auipc 11 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17678 : bv 32 := 0x84350513.
Lemma F_17678 : fetch_word Ubsan.M.loaded_segments (0x1777c : word) = Some W_17678.
Proof. vm_refl. Qed.
Lemma D_17678 : decode_any W_17678 = Some (OpImm ALU_ADD 10 10 2115, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1767c : bv 32 := 0x3d058593.
Lemma F_1767c : fetch_word Ubsan.M.loaded_segments (0x17780 : word) = Some W_1767c.
Proof. vm_refl. Qed.
Lemma D_1767c : decode_any W_1767c = Some (OpImm ALU_ADD 11 11 976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17680 : bv 32 := 0x00100613.
Lemma F_17680 : fetch_word Ubsan.M.loaded_segments (0x17784 : word) = Some W_17680.
Proof. vm_refl. Qed.
Lemma D_17680 : decode_any W_17680 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17684 : bv 32 := 0xd65fd0ef.
Lemma F_17684 : fetch_word Ubsan.M.loaded_segments (0x17788 : word) = Some W_17684.
Proof. vm_refl. Qed.
Lemma D_17684 : decode_any W_17684 = Some (Jal 1 2088292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17688 : bv 32 := 0x0080006f.
Lemma F_17688 : fetch_word Ubsan.M.loaded_segments (0x1778c : word) = Some W_17688.
Proof. vm_refl. Qed.
Lemma D_17688 : decode_any W_17688 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1768c : bv 32 := 0x00100513.
Lemma F_1768c : fetch_word Ubsan.M.loaded_segments (0x17790 : word) = Some W_1768c.
Proof. vm_refl. Qed.
Lemma D_1768c : decode_any W_1768c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17690 : bv 32 := 0x02813083.
Lemma F_17690 : fetch_word Ubsan.M.loaded_segments (0x17794 : word) = Some W_17690.
Proof. vm_refl. Qed.
Lemma D_17690 : decode_any W_17690 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17694 : bv 32 := 0x02013403.
Lemma F_17694 : fetch_word Ubsan.M.loaded_segments (0x17798 : word) = Some W_17694.
Proof. vm_refl. Qed.
Lemma D_17694 : decode_any W_17694 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17698 : bv 32 := 0x01813483.
Lemma F_17698 : fetch_word Ubsan.M.loaded_segments (0x1779c : word) = Some W_17698.
Proof. vm_refl. Qed.
Lemma D_17698 : decode_any W_17698 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1769c : bv 32 := 0x03010113.
Lemma F_1769c : fetch_word Ubsan.M.loaded_segments (0x177a0 : word) = Some W_1769c.
Proof. vm_refl. Qed.
Lemma D_1769c : decode_any W_1769c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_176a0 : bv 32 := 0x00008067.
Lemma F_176a0 : fetch_word Ubsan.M.loaded_segments (0x177a4 : word) = Some W_176a0.
Proof. vm_refl. Qed.
Lemma D_176a0 : decode_any W_176a0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_176a4 : bv 32 := 0xc0001073.
Lemma F_176a4 : fetch_word Ubsan.M.loaded_segments (0x177a8 : word) = Some W_176a4.
Proof. vm_refl. Qed.
Lemma D_176a4 : decode_any W_176a4 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.

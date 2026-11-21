(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. *)
(* reloc14 *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.World Require Import Tgt_checksum_fuzzer_ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_17650 : bv 32 := 0x02053703.
Lemma F_17650 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x176f0 : word) = Some W_17650.
Proof. vm_refl. Qed.
Lemma D_17650 : decode_any W_17650 = Some (Load SZ8 true 14 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_17654 : bv 32 := 0x00c75793.
Lemma F_17654 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x176f4 : word) = Some W_17654.
Proof. vm_refl. Qed.
Lemma D_17654 : decode_any W_17654 = Some (ShiftImm ALU_SRL 15 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17658 : bv 32 := 0x00078e63.
Lemma F_17658 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x176f8 : word) = Some W_17658.
Proof. vm_refl. Qed.
Lemma D_17658 : decode_any W_17658 = Some (Branch BC_EQ 15 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_1765c : bv 32 := 0x01f77793.
Lemma F_1765c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x176fc : word) = Some W_1765c.
Proof. vm_refl. Qed.
Lemma D_1765c : decode_any W_1765c = Some (OpImm ALU_AND 15 14 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_17660 : bv 32 := 0x00079a63.
Lemma F_17660 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17700 : word) = Some W_17660.
Proof. vm_refl. Qed.
Lemma D_17660 : decode_any W_17660 = Some (Branch BC_NE 15 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_17664 : bv 32 := 0xfffff7b7.
Lemma F_17664 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17704 : word) = Some W_17664.
Proof. vm_refl. Qed.
Lemma D_17664 : decode_any W_17664 = Some (Lui 15 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_17668 : bv 32 := 0x00f77733.
Lemma F_17668 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17708 : word) = Some W_17668.
Proof. vm_refl. Qed.
Lemma D_17668 : decode_any W_17668 = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_1766c : bv 32 := 0xff070713.
Lemma F_1766c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1770c : word) = Some W_1766c.
Proof. vm_refl. Qed.
Lemma D_1766c : decode_any W_1766c = Some (OpImm ALU_ADD 14 14 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_17670 : bv 32 := 0x0200006f.
Lemma F_17670 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17710 : word) = Some W_17670.
Proof. vm_refl. Qed.
Lemma D_17670 : decode_any W_17670 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_17674 : bv 32 := 0x00575713.
Lemma F_17674 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17714 : word) = Some W_17674.
Proof. vm_refl. Qed.
Lemma D_17674 : decode_any W_17674 = Some (ShiftImm ALU_SRL 14 14 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_17678 : bv 32 := 0xffffa797.
Lemma F_17678 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17718 : word) = Some W_17678.
Proof. vm_refl. Qed.
Lemma D_17678 : decode_any W_17678 = Some (Auipc 15 1048570, 4%Z).
Proof. vm_refl. Qed.

Definition W_1767c : bv 32 := 0x07e77713.
Lemma F_1767c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1771c : word) = Some W_1767c.
Proof. vm_refl. Qed.
Lemma D_1767c : decode_any W_1767c = Some (OpImm ALU_AND 14 14 126, 4%Z).
Proof. vm_refl. Qed.

Definition W_17680 : bv 32 := 0x39478793.
Lemma F_17680 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17720 : word) = Some W_17680.
Proof. vm_refl. Qed.
Lemma D_17680 : decode_any W_17680 = Some (OpImm ALU_ADD 15 15 916, 4%Z).
Proof. vm_refl. Qed.

Definition W_17684 : bv 32 := 0x00e78733.
Lemma F_17684 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17724 : word) = Some W_17684.
Proof. vm_refl. Qed.
Lemma D_17684 : decode_any W_17684 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_17688 : bv 32 := 0x00075703.
Lemma F_17688 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17728 : word) = Some W_17688.
Proof. vm_refl. Qed.
Lemma D_17688 : decode_any W_17688 = Some (Load SZ2 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1768c : bv 32 := 0x00471713.
Lemma F_1768c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1772c : word) = Some W_1768c.
Proof. vm_refl. Qed.
Lemma D_1768c : decode_any W_1768c = Some (ShiftImm ALU_SLL 14 14 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_17690 : bv 32 := 0x01053803.
Lemma F_17690 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17730 : word) = Some W_17690.
Proof. vm_refl. Qed.
Lemma D_17690 : decode_any W_17690 = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17694 : bv 32 := 0x02b707b3.
Lemma F_17694 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17734 : word) = Some W_17694.
Proof. vm_refl. Qed.
Lemma D_17694 : decode_any W_17694 = Some (Mul M_MUL 15 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_17698 : bv 32 := 0x00f807b3.
Lemma F_17698 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17738 : word) = Some W_17698.
Proof. vm_refl. Qed.
Lemma D_17698 : decode_any W_17698 = Some (Op ALU_ADD 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_1769c : bv 32 := 0x00d7c883.
Lemma F_1769c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1773c : word) = Some W_1769c.
Proof. vm_refl. Qed.
Lemma D_1769c : decode_any W_1769c = Some (Load SZ1 false 17 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_176a0 : bv 32 := 0x40c702b3.
Lemma F_176a0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17740 : word) = Some W_176a0.
Proof. vm_refl. Qed.
Lemma D_176a0 : decode_any W_176a0 = Some (Op ALU_SUB 5 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_176a4 : bv 32 := 0xffc28293.
Lemma F_176a4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17744 : word) = Some W_176a4.
Proof. vm_refl. Qed.
Lemma D_176a4 : decode_any W_176a4 = Some (OpImm ALU_ADD 5 5 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_176a8 : bv 32 := 0x01078793.
Lemma F_176a8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17748 : word) = Some W_176a8.
Proof. vm_refl. Qed.
Lemma D_176a8 : decode_any W_176a8 = Some (OpImm ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_176ac : bv 32 := 0x00088663.
Lemma F_176ac : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1774c : word) = Some W_176ac.
Proof. vm_refl. Qed.
Lemma D_176ac : decode_any W_176ac = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_176b0 : bv 32 := 0xffe7d683.
Lemma F_176b0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17750 : word) = Some W_176b0.
Proof. vm_refl. Qed.
Lemma D_176b0 : decode_any W_176b0 = Some (Load SZ2 false 13 15 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_176b4 : bv 32 := 0x00168693.
Lemma F_176b4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17754 : word) = Some W_176b4.
Proof. vm_refl. Qed.
Lemma D_176b4 : decode_any W_176b4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_176b8 : bv 32 := 0xffc7c383.
Lemma F_176b8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17758 : word) = Some W_176b8.
Proof. vm_refl. Qed.
Lemma D_176b8 : decode_any W_176b8 = Some (Load SZ1 false 7 15 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_176bc : bv 32 := 0x0042d313.
Lemma F_176bc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1775c : word) = Some W_176bc.
Proof. vm_refl. Qed.
Lemma D_176bc : decode_any W_176bc = Some (ShiftImm ALU_SRL 6 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_176c0 : bv 32 := 0x0ff6f893.
Lemma F_176c0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17760 : word) = Some W_176c0.
Proof. vm_refl. Qed.
Lemma D_176c0 : decode_any W_176c0 = Some (OpImm ALU_AND 17 13 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_176c4 : bv 32 := 0x00038463.
Lemma F_176c4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17764 : word) = Some W_176c4.
Proof. vm_refl. Qed.
Lemma D_176c4 : decode_any W_176c4 = Some (Branch BC_EQ 7 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_176cc : bv 32 := 0x03137e63.
Lemma F_176cc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1776c : word) = Some W_176cc.
Proof. vm_refl. Qed.
Lemma D_176cc : decode_any W_176cc = Some (Branch BC_GEU 6 17 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_176d0 : bv 32 := 0x0052d693.
Lemma F_176d0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17770 : word) = Some W_176d0.
Proof. vm_refl. Qed.
Lemma D_176d0 : decode_any W_176d0 = Some (ShiftImm ALU_SRL 13 5 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_176d4 : bv 32 := 0x00d366b3.
Lemma F_176d4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17774 : word) = Some W_176d4.
Proof. vm_refl. Qed.
Lemma D_176d4 : decode_any W_176d4 = Some (Op ALU_OR 13 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_176d8 : bv 32 := 0x0026d293.
Lemma F_176d8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17778 : word) = Some W_176d8.
Proof. vm_refl. Qed.
Lemma D_176d8 : decode_any W_176d8 = Some (ShiftImm ALU_SRL 5 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_176dc : bv 32 := 0x00d2e6b3.
Lemma F_176dc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1777c : word) = Some W_176dc.
Proof. vm_refl. Qed.
Lemma D_176dc : decode_any W_176dc = Some (Op ALU_OR 13 5 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_176e0 : bv 32 := 0x0046d293.
Lemma F_176e0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17780 : word) = Some W_176e0.
Proof. vm_refl. Qed.
Lemma D_176e0 : decode_any W_176e0 = Some (ShiftImm ALU_SRL 5 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_176e4 : bv 32 := 0x00d2e6b3.
Lemma F_176e4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17784 : word) = Some W_176e4.
Proof. vm_refl. Qed.
Lemma D_176e4 : decode_any W_176e4 = Some (Op ALU_OR 13 5 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_176e8 : bv 32 := 0x00d8f6b3.
Lemma F_176e8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17788 : word) = Some W_176e8.
Proof. vm_refl. Qed.
Lemma D_176e8 : decode_any W_176e8 = Some (Op ALU_AND 13 17 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_176ec : bv 32 := 0x00d338b3.
Lemma F_176ec : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1778c : word) = Some W_176ec.
Proof. vm_refl. Qed.
Lemma D_176ec : decode_any W_176ec = Some (Op ALU_SLTU 17 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_176f0 : bv 32 := 0xfff34293.
Lemma F_176f0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17790 : word) = Some W_176f0.
Proof. vm_refl. Qed.
Lemma D_176f0 : decode_any W_176f0 = Some (OpImm ALU_XOR 5 6 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_176f4 : bv 32 := 0x411008bb.
Lemma F_176f4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17794 : word) = Some W_176f4.
Proof. vm_refl. Qed.
Lemma D_176f4 : decode_any W_176f4 = Some (Op32 ALU_SUB 17 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_176f8 : bv 32 := 0x0058f8b3.
Lemma F_176f8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17798 : word) = Some W_176f8.
Proof. vm_refl. Qed.
Lemma D_176f8 : decode_any W_176f8 = Some (Op ALU_AND 17 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_176fc : bv 32 := 0x00d888bb.
Lemma F_176fc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1779c : word) = Some W_176fc.
Proof. vm_refl. Qed.
Lemma D_176fc : decode_any W_176fc = Some (Op32 ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_17700 : bv 32 := 0x01137463.
Lemma F_17700 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x177a0 : word) = Some W_17700.
Proof. vm_refl. Qed.
Lemma D_17700 : decode_any W_17700 = Some (Branch BC_GEU 6 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17708 : bv 32 := 0x00078693.
Lemma F_17708 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x177a8 : word) = Some W_17708.
Proof. vm_refl. Qed.
Lemma D_17708 : decode_any W_17708 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1770c : bv 32 := 0x02088063.
Lemma F_1770c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x177ac : word) = Some W_1770c.
Proof. vm_refl. Qed.
Lemma D_1770c : decode_any W_1770c = Some (Branch BC_EQ 17 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_17710 : bv 32 := 0xfe000813.
Lemma F_17710 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x177b0 : word) = Some W_17710.
Proof. vm_refl. Qed.
Lemma D_17710 : decode_any W_17710 = Some (OpImm ALU_ADD 16 0 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_17714 : bv 32 := 0x0048969b.
Lemma F_17714 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x177b4 : word) = Some W_17714.
Proof. vm_refl. Qed.
Lemma D_17714 : decode_any W_17714 = Some (ShiftImm32 ALU_SLL 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_17718 : bv 32 := 0x00d786b3.
Lemma F_17718 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x177b8 : word) = Some W_17718.
Proof. vm_refl. Qed.
Lemma D_17718 : decode_any W_17718 = Some (Op ALU_ADD 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1771c : bv 32 := 0xff078ea3.
Lemma F_1771c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x177bc : word) = Some W_1771c.
Proof. vm_refl. Qed.
Lemma D_1771c : decode_any W_1771c = Some (Store SZ1 15 16 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_17720 : bv 32 := 0xff179f23.
Lemma F_17720 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x177c0 : word) = Some W_17720.
Proof. vm_refl. Qed.
Lemma D_17720 : decode_any W_17720 = Some (Store SZ2 15 17 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_17724 : bv 32 := 0xfe068e23.
Lemma F_17724 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x177c4 : word) = Some W_17724.
Proof. vm_refl. Qed.
Lemma D_17724 : decode_any W_17724 = Some (Store SZ1 13 0 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_17728 : bv 32 := 0x01053803.
Lemma F_17728 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x177c8 : word) = Some W_17728.
Proof. vm_refl. Qed.
Lemma D_17728 : decode_any W_17728 = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1772c : bv 32 := 0x00e78733.
Lemma F_1772c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x177cc : word) = Some W_1772c.
Proof. vm_refl. Qed.
Lemma D_1772c : decode_any W_1772c = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_17730 : bv 32 := 0x410687bb.
Lemma F_17730 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x177d0 : word) = Some W_17730.
Proof. vm_refl. Qed.
Lemma D_17730 : decode_any W_17730 = Some (Op32 ALU_SUB 15 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17734 : bv 32 := 0x00d60633.
Lemma F_17734 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x177d4 : word) = Some W_17734.
Proof. vm_refl. Qed.
Lemma D_17734 : decode_any W_17734 = Some (Op ALU_ADD 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_17738 : bv 32 := 0xffc70513.
Lemma F_17738 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x177d8 : word) = Some W_17738.
Proof. vm_refl. Qed.
Lemma D_17738 : decode_any W_17738 = Some (OpImm ALU_ADD 10 14 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_1773c : bv 32 := 0xff078793.
Lemma F_1773c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x177dc : word) = Some W_1773c.
Proof. vm_refl. Qed.
Lemma D_1773c : decode_any W_1773c = Some (OpImm ALU_ADD 15 15 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_17740 : bv 32 := 0x0047d793.
Lemma F_17740 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x177e0 : word) = Some W_17740.
Proof. vm_refl. Qed.
Lemma D_17740 : decode_any W_17740 = Some (ShiftImm ALU_SRL 15 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_17744 : bv 32 := 0x40c5083b.
Lemma F_17744 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x177e4 : word) = Some W_17744.
Proof. vm_refl. Qed.
Lemma D_17744 : decode_any W_17744 = Some (Op32 ALU_SUB 16 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17748 : bv 32 := 0xfeb68ea3.
Lemma F_17748 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x177e8 : word) = Some W_17748.
Proof. vm_refl. Qed.
Lemma D_17748 : decode_any W_17748 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_1774c : bv 32 := 0xfef69f23.
Lemma F_1774c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x177ec : word) = Some W_1774c.
Proof. vm_refl. Qed.
Lemma D_1774c : decode_any W_1774c = Some (Store SZ2 13 15 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_17750 : bv 32 := 0x02080463.
Lemma F_17750 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x177f0 : word) = Some W_17750.
Proof. vm_refl. Qed.
Lemma D_17750 : decode_any W_17750 = Some (Branch BC_EQ 16 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_17754 : bv 32 := 0x40c505bb.
Lemma F_17754 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x177f4 : word) = Some W_17754.
Proof. vm_refl. Qed.
Lemma D_17754 : decode_any W_17754 = Some (Op32 ALU_SUB 11 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17758 : bv 32 := 0x40b0063b.
Lemma F_17758 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x177f8 : word) = Some W_17758.
Proof. vm_refl. Qed.
Lemma D_17758 : decode_any W_17758 = Some (Op32 ALU_SUB 12 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1775c : bv 32 := 0x00c50633.
Lemma F_1775c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x177fc : word) = Some W_1775c.
Proof. vm_refl. Qed.
Lemma D_1775c : decode_any W_1775c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17760 : bv 32 := 0x00500513.
Lemma F_17760 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17800 : word) = Some W_17760.
Proof. vm_refl. Qed.
Lemma D_17760 : decode_any W_17760 = Some (OpImm ALU_ADD 10 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_17764 : bv 32 := 0x00060023.
Lemma F_17764 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17804 : word) = Some W_17764.
Proof. vm_refl. Qed.
Lemma D_17764 : decode_any W_17764 = Some (Store SZ1 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17768 : bv 32 := 0x00a5cc63.
Lemma F_17768 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17808 : word) = Some W_17768.
Proof. vm_refl. Qed.
Lemma D_17768 : decode_any W_17768 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1776c : bv 32 := 0xfe070ba3.
Lemma F_1776c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1780c : word) = Some W_1776c.
Proof. vm_refl. Qed.
Lemma D_1776c : decode_any W_1776c = Some (Store SZ1 14 0 4087, 4%Z).
Proof. vm_refl. Qed.

Definition W_17770 : bv 32 := 0xfeb72c23.
Lemma F_17770 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17810 : word) = Some W_17770.
Proof. vm_refl. Qed.
Lemma D_17770 : decode_any W_17770 = Some (Store SZ4 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_17774 : bv 32 := 0x0100006f.
Lemma F_17774 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17814 : word) = Some W_17774.
Proof. vm_refl. Qed.
Lemma D_17774 : decode_any W_17774 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17778 : bv 32 := 0x00000513.
Lemma F_17778 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17818 : word) = Some W_17778.
Proof. vm_refl. Qed.
Lemma D_17778 : decode_any W_17778 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1777c : bv 32 := 0x0080006f.
Lemma F_1777c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1781c : word) = Some W_1777c.
Proof. vm_refl. Qed.
Lemma D_1777c : decode_any W_1777c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17780 : bv 32 := 0x00058513.
Lemma F_17780 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17820 : word) = Some W_17780.
Proof. vm_refl. Qed.
Lemma D_17780 : decode_any W_17780 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17784 : bv 32 := 0xffd6c583.
Lemma F_17784 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17824 : word) = Some W_17784.
Proof. vm_refl. Qed.
Lemma D_17784 : decode_any W_17784 = Some (Load SZ1 false 11 13 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_17788 : bv 32 := 0x01f5f593.
Lemma F_17788 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17828 : word) = Some W_17788.
Proof. vm_refl. Qed.
Lemma D_17788 : decode_any W_17788 = Some (OpImm ALU_AND 11 11 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_1778c : bv 32 := 0x00551513.
Lemma F_1778c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1782c : word) = Some W_1778c.
Proof. vm_refl. Qed.
Lemma D_1778c : decode_any W_1778c = Some (ShiftImm ALU_SLL 10 10 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_17790 : bv 32 := 0x00b56533.
Lemma F_17790 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17830 : word) = Some W_17790.
Proof. vm_refl. Qed.
Lemma D_17790 : decode_any W_17790 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_17794 : bv 32 := 0xfea68ea3.
Lemma F_17794 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17834 : word) = Some W_17794.
Proof. vm_refl. Qed.
Lemma D_17794 : decode_any W_17794 = Some (Store SZ1 13 10 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_17798 : bv 32 := 0x00068513.
Lemma F_17798 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x17838 : word) = Some W_17798.
Proof. vm_refl. Qed.
Lemma D_17798 : decode_any W_17798 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1779c : bv 32 := 0x00008067.
Lemma F_1779c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1783c : word) = Some W_1779c.
Proof. vm_refl. Qed.
Lemma D_1779c : decode_any W_1779c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

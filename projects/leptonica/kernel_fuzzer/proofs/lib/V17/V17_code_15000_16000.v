(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.H Require GcFlushU17.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.kernel_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_15000 : bv 32 := 0x00400b13.
Lemma F_15000 : fetch_word Ubsan.M.loaded_segments (0x150fc : word) = Some W_15000.
Proof. vm_refl. Qed.
Lemma D_15000 : decode_any W_15000 = Some (OpImm ALU_ADD 22 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15004 : bv 32 := 0x449010ef.
Lemma F_15004 : fetch_word Ubsan.M.loaded_segments (0x15100 : word) = Some W_15004.
Proof. vm_refl. Qed.
Lemma D_15004 : decode_any W_15004 = Some (Jal 1 7240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15008 : bv 32 := 0x00000b93.
Lemma F_15008 : fetch_word Ubsan.M.loaded_segments (0x15104 : word) = Some W_15008.
Proof. vm_refl. Qed.
Lemma D_15008 : decode_any W_15008 = Some (OpImm ALU_ADD 23 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1500c : bv 32 := 0x00a9b023.
Lemma F_1500c : fetch_word Ubsan.M.loaded_segments (0x15108 : word) = Some W_1500c.
Proof. vm_refl. Qed.
Lemma D_1500c : decode_any W_1500c = Some (Store SZ8 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15010 : bv 32 := 0x0009a823.
Lemma F_15010 : fetch_word Ubsan.M.loaded_segments (0x1510c : word) = Some W_15010.
Proof. vm_refl. Qed.
Lemma D_15010 : decode_any W_15010 = Some (Store SZ4 19 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15014 : bv 32 := 0x0000b517.
Lemma F_15014 : fetch_word Ubsan.M.loaded_segments (0x15110 : word) = Some W_15014.
Proof. vm_refl. Qed.
Lemma D_15014 : decode_any W_15014 = Some (Auipc 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15018 : bv 32 := 0x00500c13.
Lemma F_15018 : fetch_word Ubsan.M.loaded_segments (0x15114 : word) = Some W_15018.
Proof. vm_refl. Qed.
Lemma D_15018 : decode_any W_15018 = Some (OpImm ALU_ADD 24 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1501c : bv 32 := 0x8c053c83.
Lemma F_1501c : fetch_word Ubsan.M.loaded_segments (0x15118 : word) = Some W_1501c.
Proof. vm_refl. Qed.
Lemma D_1501c : decode_any W_1501c = Some (Load SZ8 true 25 10 2240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15020 : bv 32 := 0xffffc517.
Lemma F_15020 : fetch_word Ubsan.M.loaded_segments (0x1511c : word) = Some W_15020.
Proof. vm_refl. Qed.
Lemma D_15020 : decode_any W_15020 = Some (Auipc 10 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15024 : bv 32 := 0x8fa50a13.
Lemma F_15024 : fetch_word Ubsan.M.loaded_segments (0x15120 : word) = Some W_15024.
Proof. vm_refl. Qed.
Lemma D_15024 : decode_any W_15024 = Some (OpImm ALU_ADD 20 10 2298, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15028 : bv 32 := 0xffffb517.
Lemma F_15028 : fetch_word Ubsan.M.loaded_segments (0x15124 : word) = Some W_15028.
Proof. vm_refl. Qed.
Lemma D_15028 : decode_any W_15028 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1502c : bv 32 := 0x1af50a93.
Lemma F_1502c : fetch_word Ubsan.M.loaded_segments (0x15128 : word) = Some W_1502c.
Proof. vm_refl. Qed.
Lemma D_1502c : decode_any W_1502c = Some (OpImm ALU_ADD 21 10 431, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15030 : bv 32 := 0x0200006f.
Lemma F_15030 : fetch_word Ubsan.M.loaded_segments (0x1512c : word) = Some W_15030.
Proof. vm_refl. Qed.
Lemma D_15030 : decode_any W_15030 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156b4 : bv 32 := 0x0040006f.
Lemma F_156b4 : fetch_word Ubsan.M.loaded_segments (0x157b0 : word) = Some W_156b4.
Proof. vm_refl. Qed.
Lemma D_156b4 : decode_any W_156b4 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156b8 : bv 32 := 0xfa010113.
Lemma F_156b8 : fetch_word Ubsan.M.loaded_segments (0x157b4 : word) = Some W_156b8.
Proof. vm_refl. Qed.
Lemma D_156b8 : decode_any W_156b8 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156bc : bv 32 := 0x04113c23.
Lemma F_156bc : fetch_word Ubsan.M.loaded_segments (0x157b8 : word) = Some W_156bc.
Proof. vm_refl. Qed.
Lemma D_156bc : decode_any W_156bc = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156c0 : bv 32 := 0x04813823.
Lemma F_156c0 : fetch_word Ubsan.M.loaded_segments (0x157bc : word) = Some W_156c0.
Proof. vm_refl. Qed.
Lemma D_156c0 : decode_any W_156c0 = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156c4 : bv 32 := 0x04913423.
Lemma F_156c4 : fetch_word Ubsan.M.loaded_segments (0x157c0 : word) = Some W_156c4.
Proof. vm_refl. Qed.
Lemma D_156c4 : decode_any W_156c4 = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156c8 : bv 32 := 0x05213023.
Lemma F_156c8 : fetch_word Ubsan.M.loaded_segments (0x157c4 : word) = Some W_156c8.
Proof. vm_refl. Qed.
Lemma D_156c8 : decode_any W_156c8 = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156cc : bv 32 := 0x03313c23.
Lemma F_156cc : fetch_word Ubsan.M.loaded_segments (0x157c8 : word) = Some W_156cc.
Proof. vm_refl. Qed.
Lemma D_156cc : decode_any W_156cc = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156d0 : bv 32 := 0x03413823.
Lemma F_156d0 : fetch_word Ubsan.M.loaded_segments (0x157cc : word) = Some W_156d0.
Proof. vm_refl. Qed.
Lemma D_156d0 : decode_any W_156d0 = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156d4 : bv 32 := 0x03513423.
Lemma F_156d4 : fetch_word Ubsan.M.loaded_segments (0x157d0 : word) = Some W_156d4.
Proof. vm_refl. Qed.
Lemma D_156d4 : decode_any W_156d4 = Some (Store SZ8 2 21 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156d8 : bv 32 := 0x03613023.
Lemma F_156d8 : fetch_word Ubsan.M.loaded_segments (0x157d4 : word) = Some W_156d8.
Proof. vm_refl. Qed.
Lemma D_156d8 : decode_any W_156d8 = Some (Store SZ8 2 22 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156dc : bv 32 := 0x01713c23.
Lemma F_156dc : fetch_word Ubsan.M.loaded_segments (0x157d8 : word) = Some W_156dc.
Proof. vm_refl. Qed.
Lemma D_156dc : decode_any W_156dc = Some (Store SZ8 2 23 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156e0 : bv 32 := 0x04050463.
Lemma F_156e0 : fetch_word Ubsan.M.loaded_segments (0x157dc : word) = Some W_156e0.
Proof. vm_refl. Qed.
Lemma D_156e0 : decode_any W_156e0 = Some (Branch BC_EQ 10 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156e4 : bv 32 := 0x80000637.
Lemma F_156e4 : fetch_word Ubsan.M.loaded_segments (0x157e0 : word) = Some W_156e4.
Proof. vm_refl. Qed.
Lemma D_156e4 : decode_any W_156e4 = Some (Lui 12 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156e8 : bv 32 := 0x00c586b3.
Lemma F_156e8 : fetch_word Ubsan.M.loaded_segments (0x157e4 : word) = Some W_156e8.
Proof. vm_refl. Qed.
Lemma D_156e8 : decode_any W_156e8 = Some (Op ALU_ADD 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156ec : bv 32 := 0x01b6061b.
Lemma F_156ec : fetch_word Ubsan.M.loaded_segments (0x157e8 : word) = Some W_156ec.
Proof. vm_refl. Qed.
Lemma D_156ec : decode_any W_156ec = Some (OpImm32 12 12 27, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156f0 : bv 32 := 0x06d66063.
Lemma F_156f0 : fetch_word Ubsan.M.loaded_segments (0x157ec : word) = Some W_156f0.
Proof. vm_refl. Qed.
Lemma D_156f0 : decode_any W_156f0 = Some (Branch BC_LTU 12 13 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156f4 : bv 32 := 0x0000a517.
Lemma F_156f4 : fetch_word Ubsan.M.loaded_segments (0x157f0 : word) = Some W_156f4.
Proof. vm_refl. Qed.
Lemma D_156f4 : decode_any W_156f4 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156f8 : bv 32 := 0x1e053503.
Lemma F_156f8 : fetch_word Ubsan.M.loaded_segments (0x157f4 : word) = Some W_156f8.
Proof. vm_refl. Qed.
Lemma D_156f8 : decode_any W_156f8 = Some (Load SZ8 true 10 10 480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156fc : bv 32 := 0x00052503.
Lemma F_156fc : fetch_word Ubsan.M.loaded_segments (0x157f8 : word) = Some W_156fc.
Proof. vm_refl. Qed.
Lemma D_156fc : decode_any W_156fc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15700 : bv 32 := 0x00500613.
Lemma F_15700 : fetch_word Ubsan.M.loaded_segments (0x157fc : word) = Some W_15700.
Proof. vm_refl. Qed.
Lemma D_15700 : decode_any W_15700 = Some (OpImm ALU_ADD 12 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15704 : bv 32 := 0x46a64663.
Lemma F_15704 : fetch_word Ubsan.M.loaded_segments (0x15800 : word) = Some W_15704.
Proof. vm_refl. Qed.
Lemma D_15704 : decode_any W_15704 = Some (Branch BC_LT 12 10 1132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15708 : bv 32 := 0xffffb517.
Lemma F_15708 : fetch_word Ubsan.M.loaded_segments (0x15804 : word) = Some W_15708.
Proof. vm_refl. Qed.
Lemma D_15708 : decode_any W_15708 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1570c : bv 32 := 0xffffb617.
Lemma F_1570c : fetch_word Ubsan.M.loaded_segments (0x15808 : word) = Some W_1570c.
Proof. vm_refl. Qed.
Lemma D_1570c : decode_any W_1570c = Some (Auipc 12 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15710 : bv 32 := 0xfe650513.
Lemma F_15710 : fetch_word Ubsan.M.loaded_segments (0x1580c : word) = Some W_15710.
Proof. vm_refl. Qed.
Lemma D_15710 : decode_any W_15710 = Some (OpImm ALU_ADD 10 10 4070, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15714 : bv 32 := 0xea660693.
Lemma F_15714 : fetch_word Ubsan.M.loaded_segments (0x15810 : word) = Some W_15714.
Proof. vm_refl. Qed.
Lemma D_15714 : decode_any W_15714 = Some (OpImm ALU_ADD 13 12 3750, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15718 : bv 32 := 0x00058613.
Lemma F_15718 : fetch_word Ubsan.M.loaded_segments (0x15814 : word) = Some W_15718.
Proof. vm_refl. Qed.
Lemma D_15718 : decode_any W_15718 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1571c : bv 32 := 0x00068593.
Lemma F_1571c : fetch_word Ubsan.M.loaded_segments (0x15818 : word) = Some W_1571c.
Proof. vm_refl. Qed.
Lemma D_1571c : decode_any W_1571c = Some (OpImm ALU_ADD 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15720 : bv 32 := 0xaecfe0ef.
Lemma F_15720 : fetch_word Ubsan.M.loaded_segments (0x1581c : word) = Some W_15720.
Proof. vm_refl. Qed.
Lemma D_15720 : decode_any W_15720 = Some (Jal 1 2089708, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15724 : bv 32 := 0x44c0006f.
Lemma F_15724 : fetch_word Ubsan.M.loaded_segments (0x15820 : word) = Some W_15724.
Proof. vm_refl. Qed.
Lemma D_15724 : decode_any W_15724 = Some (Jal 0 1100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15750 : bv 32 := 0x00054603.
Lemma F_15750 : fetch_word Ubsan.M.loaded_segments (0x1584c : word) = Some W_15750.
Proof. vm_refl. Qed.
Lemma D_15750 : decode_any W_15750 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15754 : bv 32 := 0x07300693.
Lemma F_15754 : fetch_word Ubsan.M.loaded_segments (0x15850 : word) = Some W_15754.
Proof. vm_refl. Qed.
Lemma D_15754 : decode_any W_15754 = Some (OpImm ALU_ADD 13 0 115, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15758 : bv 32 := 0x0cd61663.
Lemma F_15758 : fetch_word Ubsan.M.loaded_segments (0x15854 : word) = Some W_15758.
Proof. vm_refl. Qed.
Lemma D_15758 : decode_any W_15758 = Some (Branch BC_NE 12 13 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1575c : bv 32 := 0xfff00613.
Lemma F_1575c : fetch_word Ubsan.M.loaded_segments (0x15858 : word) = Some W_1575c.
Proof. vm_refl. Qed.
Lemma D_1575c : decode_any W_1575c = Some (OpImm ALU_ADD 12 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15760 : bv 32 := 0x44c50063.
Lemma F_15760 : fetch_word Ubsan.M.loaded_segments (0x1585c : word) = Some W_15760.
Proof. vm_refl. Qed.
Lemma D_15760 : decode_any W_15760 = Some (Branch BC_EQ 10 12 1088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15764 : bv 32 := 0x00154603.
Lemma F_15764 : fetch_word Ubsan.M.loaded_segments (0x15860 : word) = Some W_15764.
Proof. vm_refl. Qed.
Lemma D_15764 : decode_any W_15764 = Some (Load SZ1 false 12 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15768 : bv 32 := 0x07000693.
Lemma F_15768 : fetch_word Ubsan.M.loaded_segments (0x15864 : word) = Some W_15768.
Proof. vm_refl. Qed.
Lemma D_15768 : decode_any W_15768 = Some (OpImm ALU_ADD 13 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1576c : bv 32 := 0x0ad61c63.
Lemma F_1576c : fetch_word Ubsan.M.loaded_segments (0x15868 : word) = Some W_1576c.
Proof. vm_refl. Qed.
Lemma D_1576c : decode_any W_1576c = Some (Branch BC_NE 12 13 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15770 : bv 32 := 0xffd00613.
Lemma F_15770 : fetch_word Ubsan.M.loaded_segments (0x1586c : word) = Some W_15770.
Proof. vm_refl. Qed.
Lemma D_15770 : decode_any W_15770 = Some (OpImm ALU_ADD 12 0 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15774 : bv 32 := 0x42a66663.
Lemma F_15774 : fetch_word Ubsan.M.loaded_segments (0x15870 : word) = Some W_15774.
Proof. vm_refl. Qed.
Lemma D_15774 : decode_any W_15774 = Some (Branch BC_LTU 12 10 1068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15778 : bv 32 := 0x00254603.
Lemma F_15778 : fetch_word Ubsan.M.loaded_segments (0x15874 : word) = Some W_15778.
Proof. vm_refl. Qed.
Lemma D_15778 : decode_any W_15778 = Some (Load SZ1 false 12 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1577c : bv 32 := 0x06900693.
Lemma F_1577c : fetch_word Ubsan.M.loaded_segments (0x15878 : word) = Some W_1577c.
Proof. vm_refl. Qed.
Lemma D_1577c : decode_any W_1577c = Some (OpImm ALU_ADD 13 0 105, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15780 : bv 32 := 0x0ad61263.
Lemma F_15780 : fetch_word Ubsan.M.loaded_segments (0x1587c : word) = Some W_15780.
Proof. vm_refl. Qed.
Lemma D_15780 : decode_any W_15780 = Some (Branch BC_NE 12 13 164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15784 : bv 32 := 0xffc00613.
Lemma F_15784 : fetch_word Ubsan.M.loaded_segments (0x15880 : word) = Some W_15784.
Proof. vm_refl. Qed.
Lemma D_15784 : decode_any W_15784 = Some (OpImm ALU_ADD 12 0 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15788 : bv 32 := 0x40a66c63.
Lemma F_15788 : fetch_word Ubsan.M.loaded_segments (0x15884 : word) = Some W_15788.
Proof. vm_refl. Qed.
Lemma D_15788 : decode_any W_15788 = Some (Branch BC_LTU 12 10 1048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1578c : bv 32 := 0x00354603.
Lemma F_1578c : fetch_word Ubsan.M.loaded_segments (0x15888 : word) = Some W_1578c.
Proof. vm_refl. Qed.
Lemma D_1578c : decode_any W_1578c = Some (Load SZ1 false 12 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15790 : bv 32 := 0x07800693.
Lemma F_15790 : fetch_word Ubsan.M.loaded_segments (0x1588c : word) = Some W_15790.
Proof. vm_refl. Qed.
Lemma D_15790 : decode_any W_15790 = Some (OpImm ALU_ADD 13 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15794 : bv 32 := 0x08d61863.
Lemma F_15794 : fetch_word Ubsan.M.loaded_segments (0x15890 : word) = Some W_15794.
Proof. vm_refl. Qed.
Lemma D_15794 : decode_any W_15794 = Some (Branch BC_NE 12 13 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15798 : bv 32 := 0xffb00613.
Lemma F_15798 : fetch_word Ubsan.M.loaded_segments (0x15894 : word) = Some W_15798.
Proof. vm_refl. Qed.
Lemma D_15798 : decode_any W_15798 = Some (OpImm ALU_ADD 12 0 4091, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1579c : bv 32 := 0x40a66263.
Lemma F_1579c : fetch_word Ubsan.M.loaded_segments (0x15898 : word) = Some W_1579c.
Proof. vm_refl. Qed.
Lemma D_1579c : decode_any W_1579c = Some (Branch BC_LTU 12 10 1028, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157a0 : bv 32 := 0x00450613.
Lemma F_157a0 : fetch_word Ubsan.M.loaded_segments (0x1589c : word) = Some W_157a0.
Proof. vm_refl. Qed.
Lemma D_157a0 : decode_any W_157a0 = Some (OpImm ALU_ADD 12 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157a4 : bv 32 := 0x00367613.
Lemma F_157a4 : fetch_word Ubsan.M.loaded_segments (0x158a0 : word) = Some W_157a4.
Proof. vm_refl. Qed.
Lemma D_157a4 : decode_any W_157a4 = Some (OpImm ALU_AND 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157a8 : bv 32 := 0x3e061c63.
Lemma F_157a8 : fetch_word Ubsan.M.loaded_segments (0x158a4 : word) = Some W_157a8.
Proof. vm_refl. Qed.
Lemma D_157a8 : decode_any W_157a8 = Some (Branch BC_NE 12 0 1016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157ac : bv 32 := 0xff700613.
Lemma F_157ac : fetch_word Ubsan.M.loaded_segments (0x158a8 : word) = Some W_157ac.
Proof. vm_refl. Qed.
Lemma D_157ac : decode_any W_157ac = Some (OpImm ALU_ADD 12 0 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157b0 : bv 32 := 0x3ea66863.
Lemma F_157b0 : fetch_word Ubsan.M.loaded_segments (0x158ac : word) = Some W_157b0.
Proof. vm_refl. Qed.
Lemma D_157b0 : decode_any W_157b0 = Some (Branch BC_LTU 12 10 1008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157b4 : bv 32 := 0x00850613.
Lemma F_157b4 : fetch_word Ubsan.M.loaded_segments (0x158b0 : word) = Some W_157b4.
Proof. vm_refl. Qed.
Lemma D_157b4 : decode_any W_157b4 = Some (OpImm ALU_ADD 12 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157b8 : bv 32 := 0x00367613.
Lemma F_157b8 : fetch_word Ubsan.M.loaded_segments (0x158b4 : word) = Some W_157b8.
Proof. vm_refl. Qed.
Lemma D_157b8 : decode_any W_157b8 = Some (OpImm ALU_AND 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157bc : bv 32 := 0x3e061263.
Lemma F_157bc : fetch_word Ubsan.M.loaded_segments (0x158b8 : word) = Some W_157bc.
Proof. vm_refl. Qed.
Lemma D_157bc : decode_any W_157bc = Some (Branch BC_NE 12 0 996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157c0 : bv 32 := 0xff300613.
Lemma F_157c0 : fetch_word Ubsan.M.loaded_segments (0x158bc : word) = Some W_157c0.
Proof. vm_refl. Qed.
Lemma D_157c0 : decode_any W_157c0 = Some (OpImm ALU_ADD 12 0 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157c4 : bv 32 := 0x3ca66e63.
Lemma F_157c4 : fetch_word Ubsan.M.loaded_segments (0x158c0 : word) = Some W_157c4.
Proof. vm_refl. Qed.
Lemma D_157c4 : decode_any W_157c4 = Some (Branch BC_LTU 12 10 988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157c8 : bv 32 := 0x00c50613.
Lemma F_157c8 : fetch_word Ubsan.M.loaded_segments (0x158c4 : word) = Some W_157c8.
Proof. vm_refl. Qed.
Lemma D_157c8 : decode_any W_157c8 = Some (OpImm ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157cc : bv 32 := 0x00367613.
Lemma F_157cc : fetch_word Ubsan.M.loaded_segments (0x158c8 : word) = Some W_157cc.
Proof. vm_refl. Qed.
Lemma D_157cc : decode_any W_157cc = Some (OpImm ALU_AND 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157d0 : bv 32 := 0x3c061863.
Lemma F_157d0 : fetch_word Ubsan.M.loaded_segments (0x158cc : word) = Some W_157d0.
Proof. vm_refl. Qed.
Lemma D_157d0 : decode_any W_157d0 = Some (Branch BC_NE 12 0 976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157d4 : bv 32 := 0xfeb00613.
Lemma F_157d4 : fetch_word Ubsan.M.loaded_segments (0x158d0 : word) = Some W_157d4.
Proof. vm_refl. Qed.
Lemma D_157d4 : decode_any W_157d4 = Some (OpImm ALU_ADD 12 0 4075, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157d8 : bv 32 := 0x3ca66463.
Lemma F_157d8 : fetch_word Ubsan.M.loaded_segments (0x158d4 : word) = Some W_157d8.
Proof. vm_refl. Qed.
Lemma D_157d8 : decode_any W_157d8 = Some (Branch BC_LTU 12 10 968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157dc : bv 32 := 0x01450613.
Lemma F_157dc : fetch_word Ubsan.M.loaded_segments (0x158d8 : word) = Some W_157dc.
Proof. vm_refl. Qed.
Lemma D_157dc : decode_any W_157dc = Some (OpImm ALU_ADD 12 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157e0 : bv 32 := 0x00367693.
Lemma F_157e0 : fetch_word Ubsan.M.loaded_segments (0x158dc : word) = Some W_157e0.
Proof. vm_refl. Qed.
Lemma D_157e0 : decode_any W_157e0 = Some (OpImm ALU_AND 13 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157e4 : bv 32 := 0x3a069e63.
Lemma F_157e4 : fetch_word Ubsan.M.loaded_segments (0x158e0 : word) = Some W_157e4.
Proof. vm_refl. Qed.
Lemma D_157e4 : decode_any W_157e4 = Some (Branch BC_NE 13 0 956, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157e8 : bv 32 := 0x00452483.
Lemma F_157e8 : fetch_word Ubsan.M.loaded_segments (0x158e4 : word) = Some W_157e8.
Proof. vm_refl. Qed.
Lemma D_157e8 : decode_any W_157e8 = Some (Load SZ4 true 9 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157ec : bv 32 := 0xfff0c6b7.
Lemma F_157ec : fetch_word Ubsan.M.loaded_segments (0x158e8 : word) = Some W_157ec.
Proof. vm_refl. Qed.
Lemma D_157ec : decode_any W_157ec = Some (Lui 13 1048332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157f0 : bv 32 := 0xdbf6869b.
Lemma F_157f0 : fetch_word Ubsan.M.loaded_segments (0x158ec : word) = Some W_157f0.
Proof. vm_refl. Qed.
Lemma D_157f0 : decode_any W_157f0 = Some (OpImm32 13 13 3519, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157f4 : bv 32 := 0x00d4873b.
Lemma F_157f4 : fetch_word Ubsan.M.loaded_segments (0x158f0 : word) = Some W_157f4.
Proof. vm_refl. Qed.
Lemma D_157f4 : decode_any W_157f4 = Some (Op32 ALU_ADD 14 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157f8 : bv 32 := 0x08e6e063.
Lemma F_157f8 : fetch_word Ubsan.M.loaded_segments (0x158f4 : word) = Some W_157f8.
Proof. vm_refl. Qed.
Lemma D_157f8 : decode_any W_157f8 = Some (Branch BC_LTU 13 14 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157fc : bv 32 := 0x0000a517.
Lemma F_157fc : fetch_word Ubsan.M.loaded_segments (0x158f8 : word) = Some W_157fc.
Proof. vm_refl. Qed.
Lemma D_157fc : decode_any W_157fc = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15800 : bv 32 := 0x0d853503.
Lemma F_15800 : fetch_word Ubsan.M.loaded_segments (0x158fc : word) = Some W_15800.
Proof. vm_refl. Qed.
Lemma D_15800 : decode_any W_15800 = Some (Load SZ8 true 10 10 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15804 : bv 32 := 0x00052503.
Lemma F_15804 : fetch_word Ubsan.M.loaded_segments (0x15900 : word) = Some W_15804.
Proof. vm_refl. Qed.
Lemma D_15804 : decode_any W_15804 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15808 : bv 32 := 0x00500593.
Lemma F_15808 : fetch_word Ubsan.M.loaded_segments (0x15904 : word) = Some W_15808.
Proof. vm_refl. Qed.
Lemma D_15808 : decode_any W_15808 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1580c : bv 32 := 0x36a5c263.
Lemma F_1580c : fetch_word Ubsan.M.loaded_segments (0x15908 : word) = Some W_1580c.
Proof. vm_refl. Qed.
Lemma D_1580c : decode_any W_1580c = Some (Branch BC_LT 11 10 868, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15810 : bv 32 := 0xffffb517.
Lemma F_15810 : fetch_word Ubsan.M.loaded_segments (0x1590c : word) = Some W_15810.
Proof. vm_refl. Qed.
Lemma D_15810 : decode_any W_15810 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15814 : bv 32 := 0xffffb597.
Lemma F_15814 : fetch_word Ubsan.M.loaded_segments (0x15910 : word) = Some W_15814.
Proof. vm_refl. Qed.
Lemma D_15814 : decode_any W_15814 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15818 : bv 32 := 0x16c50513.
Lemma F_15818 : fetch_word Ubsan.M.loaded_segments (0x15914 : word) = Some W_15818.
Proof. vm_refl. Qed.
Lemma D_15818 : decode_any W_15818 = Some (OpImm ALU_ADD 10 10 364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1581c : bv 32 := 0xd9e58593.
Lemma F_1581c : fetch_word Ubsan.M.loaded_segments (0x15918 : word) = Some W_1581c.
Proof. vm_refl. Qed.
Lemma D_1581c : decode_any W_1581c = Some (OpImm ALU_ADD 11 11 3486, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15820 : bv 32 := 0x0280006f.
Lemma F_15820 : fetch_word Ubsan.M.loaded_segments (0x1591c : word) = Some W_15820.
Proof. vm_refl. Qed.
Lemma D_15820 : decode_any W_15820 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15824 : bv 32 := 0x0000a517.
Lemma F_15824 : fetch_word Ubsan.M.loaded_segments (0x15920 : word) = Some W_15824.
Proof. vm_refl. Qed.
Lemma D_15824 : decode_any W_15824 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15828 : bv 32 := 0x0b053503.
Lemma F_15828 : fetch_word Ubsan.M.loaded_segments (0x15924 : word) = Some W_15828.
Proof. vm_refl. Qed.
Lemma D_15828 : decode_any W_15828 = Some (Load SZ8 true 10 10 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1582c : bv 32 := 0x00052503.
Lemma F_1582c : fetch_word Ubsan.M.loaded_segments (0x15928 : word) = Some W_1582c.
Proof. vm_refl. Qed.
Lemma D_1582c : decode_any W_1582c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15830 : bv 32 := 0x00500593.
Lemma F_15830 : fetch_word Ubsan.M.loaded_segments (0x1592c : word) = Some W_15830.
Proof. vm_refl. Qed.
Lemma D_15830 : decode_any W_15830 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15834 : bv 32 := 0x32a5ce63.
Lemma F_15834 : fetch_word Ubsan.M.loaded_segments (0x15930 : word) = Some W_15834.
Proof. vm_refl. Qed.
Lemma D_15834 : decode_any W_15834 = Some (Branch BC_LT 11 10 828, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15838 : bv 32 := 0xffffb517.
Lemma F_15838 : fetch_word Ubsan.M.loaded_segments (0x15934 : word) = Some W_15838.
Proof. vm_refl. Qed.
Lemma D_15838 : decode_any W_15838 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1583c : bv 32 := 0xffffb597.
Lemma F_1583c : fetch_word Ubsan.M.loaded_segments (0x15938 : word) = Some W_1583c.
Proof. vm_refl. Qed.
Lemma D_1583c : decode_any W_1583c = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15840 : bv 32 := 0xed950513.
Lemma F_15840 : fetch_word Ubsan.M.loaded_segments (0x1593c : word) = Some W_15840.
Proof. vm_refl. Qed.
Lemma D_15840 : decode_any W_15840 = Some (OpImm ALU_ADD 10 10 3801, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15844 : bv 32 := 0xd7658593.
Lemma F_15844 : fetch_word Ubsan.M.loaded_segments (0x15940 : word) = Some W_15844.
Proof. vm_refl. Qed.
Lemma D_15844 : decode_any W_15844 = Some (OpImm ALU_ADD 11 11 3446, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15848 : bv 32 := 0x00000613.
Lemma F_15848 : fetch_word Ubsan.M.loaded_segments (0x15944 : word) = Some W_15848.
Proof. vm_refl. Qed.
Lemma D_15848 : decode_any W_15848 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1584c : bv 32 := 0x05813083.
Lemma F_1584c : fetch_word Ubsan.M.loaded_segments (0x15948 : word) = Some W_1584c.
Proof. vm_refl. Qed.
Lemma D_1584c : decode_any W_1584c = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15850 : bv 32 := 0x05013403.
Lemma F_15850 : fetch_word Ubsan.M.loaded_segments (0x1594c : word) = Some W_15850.
Proof. vm_refl. Qed.
Lemma D_15850 : decode_any W_15850 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15854 : bv 32 := 0x04813483.
Lemma F_15854 : fetch_word Ubsan.M.loaded_segments (0x15950 : word) = Some W_15854.
Proof. vm_refl. Qed.
Lemma D_15854 : decode_any W_15854 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15858 : bv 32 := 0x04013903.
Lemma F_15858 : fetch_word Ubsan.M.loaded_segments (0x15954 : word) = Some W_15858.
Proof. vm_refl. Qed.
Lemma D_15858 : decode_any W_15858 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1585c : bv 32 := 0x03813983.
Lemma F_1585c : fetch_word Ubsan.M.loaded_segments (0x15958 : word) = Some W_1585c.
Proof. vm_refl. Qed.
Lemma D_1585c : decode_any W_1585c = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15860 : bv 32 := 0x03013a03.
Lemma F_15860 : fetch_word Ubsan.M.loaded_segments (0x1595c : word) = Some W_15860.
Proof. vm_refl. Qed.
Lemma D_15860 : decode_any W_15860 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15864 : bv 32 := 0x02813a83.
Lemma F_15864 : fetch_word Ubsan.M.loaded_segments (0x15960 : word) = Some W_15864.
Proof. vm_refl. Qed.
Lemma D_15864 : decode_any W_15864 = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15868 : bv 32 := 0x02013b03.
Lemma F_15868 : fetch_word Ubsan.M.loaded_segments (0x15964 : word) = Some W_15868.
Proof. vm_refl. Qed.
Lemma D_15868 : decode_any W_15868 = Some (Load SZ8 true 22 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1586c : bv 32 := 0x01813b83.
Lemma F_1586c : fetch_word Ubsan.M.loaded_segments (0x15968 : word) = Some W_1586c.
Proof. vm_refl. Qed.
Lemma D_1586c : decode_any W_1586c = Some (Load SZ8 true 23 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15870 : bv 32 := 0x06010113.
Lemma F_15870 : fetch_word Ubsan.M.loaded_segments (0x1596c : word) = Some W_15870.
Proof. vm_refl. Qed.
Lemma D_15870 : decode_any W_15870 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15874 : bv 32 := 0xa34fe06f.
Lemma F_15874 : fetch_word Ubsan.M.loaded_segments (0x15970 : word) = Some W_15874.
Proof. vm_refl. Qed.
Lemma D_15874 : decode_any W_15874 = Some (Jal 0 2089524, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15878 : bv 32 := 0x00852903.
Lemma F_15878 : fetch_word Ubsan.M.loaded_segments (0x15974 : word) = Some W_15878.
Proof. vm_refl. Qed.
Lemma D_15878 : decode_any W_15878 = Some (Load SZ4 true 18 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1587c : bv 32 := 0x00d9073b.
Lemma F_1587c : fetch_word Ubsan.M.loaded_segments (0x15978 : word) = Some W_1587c.
Proof. vm_refl. Qed.
Lemma D_1587c : decode_any W_1587c = Some (Op32 ALU_ADD 14 18 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15880 : bv 32 := 0x02e6e663.
Lemma F_15880 : fetch_word Ubsan.M.loaded_segments (0x1597c : word) = Some W_15880.
Proof. vm_refl. Qed.
Lemma D_15880 : decode_any W_15880 = Some (Branch BC_LTU 13 14 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15884 : bv 32 := 0x0000a517.
Lemma F_15884 : fetch_word Ubsan.M.loaded_segments (0x15980 : word) = Some W_15884.
Proof. vm_refl. Qed.
Lemma D_15884 : decode_any W_15884 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15888 : bv 32 := 0x05053503.
Lemma F_15888 : fetch_word Ubsan.M.loaded_segments (0x15984 : word) = Some W_15888.
Proof. vm_refl. Qed.
Lemma D_15888 : decode_any W_15888 = Some (Load SZ8 true 10 10 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1588c : bv 32 := 0x00052503.
Lemma F_1588c : fetch_word Ubsan.M.loaded_segments (0x15988 : word) = Some W_1588c.
Proof. vm_refl. Qed.
Lemma D_1588c : decode_any W_1588c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15890 : bv 32 := 0x00500593.
Lemma F_15890 : fetch_word Ubsan.M.loaded_segments (0x1598c : word) = Some W_15890.
Proof. vm_refl. Qed.
Lemma D_15890 : decode_any W_15890 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15894 : bv 32 := 0x2ca5ce63.
Lemma F_15894 : fetch_word Ubsan.M.loaded_segments (0x15990 : word) = Some W_15894.
Proof. vm_refl. Qed.
Lemma D_15894 : decode_any W_15894 = Some (Branch BC_LT 11 10 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15898 : bv 32 := 0xffffb517.
Lemma F_15898 : fetch_word Ubsan.M.loaded_segments (0x15994 : word) = Some W_15898.
Proof. vm_refl. Qed.
Lemma D_15898 : decode_any W_15898 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1589c : bv 32 := 0xffffb597.
Lemma F_1589c : fetch_word Ubsan.M.loaded_segments (0x15998 : word) = Some W_1589c.
Proof. vm_refl. Qed.
Lemma D_1589c : decode_any W_1589c = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158a0 : bv 32 := 0x9e950513.
Lemma F_158a0 : fetch_word Ubsan.M.loaded_segments (0x1599c : word) = Some W_158a0.
Proof. vm_refl. Qed.
Lemma D_158a0 : decode_any W_158a0 = Some (OpImm ALU_ADD 10 10 2537, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158a4 : bv 32 := 0xd1658593.
Lemma F_158a4 : fetch_word Ubsan.M.loaded_segments (0x159a0 : word) = Some W_158a4.
Proof. vm_refl. Qed.
Lemma D_158a4 : decode_any W_158a4 = Some (OpImm ALU_ADD 11 11 3350, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158a8 : bv 32 := 0xfa1ff06f.
Lemma F_158a8 : fetch_word Ubsan.M.loaded_segments (0x159a4 : word) = Some W_158a8.
Proof. vm_refl. Qed.
Lemma D_158a8 : decode_any W_158a8 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158ac : bv 32 := 0x029906b3.
Lemma F_158ac : fetch_word Ubsan.M.loaded_segments (0x159a8 : word) = Some W_158ac.
Proof. vm_refl. Qed.
Lemma D_158ac : decode_any W_158ac = Some (Mul M_MUL 13 18 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158b0 : bv 32 := 0x17d78737.
Lemma F_158b0 : fetch_word Ubsan.M.loaded_segments (0x159ac : word) = Some W_158b0.
Proof. vm_refl. Qed.
Lemma D_158b0 : decode_any W_158b0 = Some (Lui 14 97656, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158b4 : bv 32 := 0x4017071b.
Lemma F_158b4 : fetch_word Ubsan.M.loaded_segments (0x159b0 : word) = Some W_158b4.
Proof. vm_refl. Qed.
Lemma D_158b4 : decode_any W_158b4 = Some (OpImm32 14 14 1025, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158b8 : bv 32 := 0x02e6e663.
Lemma F_158b8 : fetch_word Ubsan.M.loaded_segments (0x159b4 : word) = Some W_158b8.
Proof. vm_refl. Qed.
Lemma D_158b8 : decode_any W_158b8 = Some (Branch BC_LTU 13 14 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158bc : bv 32 := 0x0000a517.
Lemma F_158bc : fetch_word Ubsan.M.loaded_segments (0x159b8 : word) = Some W_158bc.
Proof. vm_refl. Qed.
Lemma D_158bc : decode_any W_158bc = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158c0 : bv 32 := 0x01853503.
Lemma F_158c0 : fetch_word Ubsan.M.loaded_segments (0x159bc : word) = Some W_158c0.
Proof. vm_refl. Qed.
Lemma D_158c0 : decode_any W_158c0 = Some (Load SZ8 true 10 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158c4 : bv 32 := 0x00052503.
Lemma F_158c4 : fetch_word Ubsan.M.loaded_segments (0x159c0 : word) = Some W_158c4.
Proof. vm_refl. Qed.
Lemma D_158c4 : decode_any W_158c4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158c8 : bv 32 := 0x00500593.
Lemma F_158c8 : fetch_word Ubsan.M.loaded_segments (0x159c4 : word) = Some W_158c8.
Proof. vm_refl. Qed.
Lemma D_158c8 : decode_any W_158c8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158cc : bv 32 := 0x2aa5c263.
Lemma F_158cc : fetch_word Ubsan.M.loaded_segments (0x159c8 : word) = Some W_158cc.
Proof. vm_refl. Qed.
Lemma D_158cc : decode_any W_158cc = Some (Branch BC_LT 11 10 676, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158d0 : bv 32 := 0xffffb517.
Lemma F_158d0 : fetch_word Ubsan.M.loaded_segments (0x159cc : word) = Some W_158d0.
Proof. vm_refl. Qed.
Lemma D_158d0 : decode_any W_158d0 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158d4 : bv 32 := 0xffffb597.
Lemma F_158d4 : fetch_word Ubsan.M.loaded_segments (0x159d0 : word) = Some W_158d4.
Proof. vm_refl. Qed.
Lemma D_158d4 : decode_any W_158d4 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158d8 : bv 32 := 0x96750513.
Lemma F_158d8 : fetch_word Ubsan.M.loaded_segments (0x159d4 : word) = Some W_158d8.
Proof. vm_refl. Qed.
Lemma D_158d8 : decode_any W_158d8 = Some (OpImm ALU_ADD 10 10 2407, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158dc : bv 32 := 0xcde58593.
Lemma F_158dc : fetch_word Ubsan.M.loaded_segments (0x159d8 : word) = Some W_158dc.
Proof. vm_refl. Qed.
Lemma D_158dc : decode_any W_158dc = Some (OpImm ALU_ADD 11 11 3294, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158e0 : bv 32 := 0xf69ff06f.
Lemma F_158e0 : fetch_word Ubsan.M.loaded_segments (0x159dc : word) = Some W_158e0.
Proof. vm_refl. Qed.
Lemma D_158e0 : decode_any W_158e0 = Some (Jal 0 2097000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158e4 : bv 32 := 0x00066b03.
Lemma F_158e4 : fetch_word Ubsan.M.loaded_segments (0x159e0 : word) = Some W_158e4.
Proof. vm_refl. Qed.
Lemma D_158e4 : decode_any W_158e4 = Some (Load SZ4 false 22 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158e8 : bv 32 := 0x10000613.
Lemma F_158e8 : fetch_word Ubsan.M.loaded_segments (0x159e4 : word) = Some W_158e8.
Proof. vm_refl. Qed.
Lemma D_158e8 : decode_any W_158e8 = Some (OpImm ALU_ADD 12 0 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158ec : bv 32 := 0x11666463.
Lemma F_158ec : fetch_word Ubsan.M.loaded_segments (0x159e8 : word) = Some W_158ec.
Proof. vm_refl. Qed.
Lemma D_158ec : decode_any W_158ec = Some (Branch BC_LTU 12 22 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158f0 : bv 32 := 0x007b0613.
Lemma F_158f0 : fetch_word Ubsan.M.loaded_segments (0x159ec : word) = Some W_158f0.
Proof. vm_refl. Qed.
Lemma D_158f0 : decode_any W_158f0 = Some (OpImm ALU_ADD 12 22 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158f4 : bv 32 := 0x0025d693.
Lemma F_158f4 : fetch_word Ubsan.M.loaded_segments (0x159f0 : word) = Some W_158f4.
Proof. vm_refl. Qed.
Lemma D_158f4 : decode_any W_158f4 = Some (ShiftImm ALU_SRL 13 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158f8 : bv 32 := 0x0ed67e63.
Lemma F_158f8 : fetch_word Ubsan.M.loaded_segments (0x159f4 : word) = Some W_158f8.
Proof. vm_refl. Qed.
Lemma D_158f8 : decode_any W_158f8 = Some (Branch BC_GEU 12 13 252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158fc : bv 32 := 0x00058a13.
Lemma F_158fc : fetch_word Ubsan.M.loaded_segments (0x159f8 : word) = Some W_158fc.
Proof. vm_refl. Qed.
Lemma D_158fc : decode_any W_158fc = Some (OpImm ALU_ADD 20 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15900 : bv 32 := 0x00050b93.
Lemma F_15900 : fetch_word Ubsan.M.loaded_segments (0x159fc : word) = Some W_15900.
Proof. vm_refl. Qed.
Lemma D_15900 : decode_any W_15900 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15904 : bv 32 := 0x00c52983.
Lemma F_15904 : fetch_word Ubsan.M.loaded_segments (0x15a00 : word) = Some W_15904.
Proof. vm_refl. Qed.
Lemma D_15904 : decode_any W_15904 = Some (Load SZ4 true 19 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15908 : bv 32 := 0x00048513.
Lemma F_15908 : fetch_word Ubsan.M.loaded_segments (0x15a04 : word) = Some W_15908.
Proof. vm_refl. Qed.
Lemma D_15908 : decode_any W_15908 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1590c : bv 32 := 0x00090593.
Lemma F_1590c : fetch_word Ubsan.M.loaded_segments (0x15a08 : word) = Some W_1590c.
Proof. vm_refl. Qed.
Lemma D_1590c : decode_any W_1590c = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15910 : bv 32 := 0x00098613.
Lemma F_15910 : fetch_word Ubsan.M.loaded_segments (0x15a0c : word) = Some W_15910.
Proof. vm_refl. Qed.
Lemma D_15910 : decode_any W_15910 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15914 : bv 32 := 0xbe4fe0ef.
Lemma F_15914 : fetch_word Ubsan.M.loaded_segments (0x15a10 : word) = Some W_15914.
Proof. vm_refl. Qed.
Lemma D_15914 : decode_any W_15914 = Some (Jal 1 2089956, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15918 : bv 32 := 0x00a13423.
Lemma F_15918 : fetch_word Ubsan.M.loaded_segments (0x15a14 : word) = Some W_15918.
Proof. vm_refl. Qed.
Lemma D_15918 : decode_any W_15918 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1591c : bv 32 := 0x10050063.
Lemma F_1591c : fetch_word Ubsan.M.loaded_segments (0x15a18 : word) = Some W_1591c.
Proof. vm_refl. Qed.
Lemma D_1591c : decode_any W_1591c = Some (Branch BC_EQ 10 0 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15920 : bv 32 := 0x00291a9b.
Lemma F_15920 : fetch_word Ubsan.M.loaded_segments (0x15a1c : word) = Some W_15920.
Proof. vm_refl. Qed.
Lemma D_15920 : decode_any W_15920 = Some (ShiftImm32 ALU_SLL 21 18 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15924 : bv 32 := 0xef8fe0ef.
Lemma F_15924 : fetch_word Ubsan.M.loaded_segments (0x15a20 : word) = Some W_15924.
Proof. vm_refl. Qed.
Lemma D_15924 : decode_any W_15924 = Some (Jal 1 2090744, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15928 : bv 32 := 0x02aa843b.
Lemma F_15928 : fetch_word Ubsan.M.loaded_segments (0x15a24 : word) = Some W_15928.
Proof. vm_refl. Qed.
Lemma D_15928 : decode_any W_15928 = Some (Mul32 M_MUL 8 21 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1592c : bv 32 := 0x02aa8533.
Lemma F_1592c : fetch_word Ubsan.M.loaded_segments (0x15a28 : word) = Some W_1592c.
Proof. vm_refl. Qed.
Lemma D_1592c : decode_any W_1592c = Some (Mul M_MUL 10 21 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15930 : bv 32 := 0x26a41863.
Lemma F_15930 : fetch_word Ubsan.M.loaded_segments (0x15a2c : word) = Some W_15930.
Proof. vm_refl. Qed.
Lemma D_15930 : decode_any W_15930 = Some (Branch BC_NE 8 10 624, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15934 : bv 32 := 0x002b1593.
Lemma F_15934 : fetch_word Ubsan.M.loaded_segments (0x15a30 : word) = Some W_15934.
Proof. vm_refl. Qed.
Lemma D_15934 : decode_any W_15934 = Some (ShiftImm ALU_SLL 11 22 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15938 : bv 32 := 0x01858593.
Lemma F_15938 : fetch_word Ubsan.M.loaded_segments (0x15a34 : word) = Some W_15938.
Proof. vm_refl. Qed.
Lemma D_15938 : decode_any W_15938 = Some (OpImm ALU_ADD 11 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1593c : bv 32 := 0xfffbc693.
Lemma F_1593c : fetch_word Ubsan.M.loaded_segments (0x15a38 : word) = Some W_1593c.
Proof. vm_refl. Qed.
Lemma D_1593c : decode_any W_1593c = Some (OpImm ALU_XOR 13 23 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15940 : bv 32 := 0x26b6e063.
Lemma F_15940 : fetch_word Ubsan.M.loaded_segments (0x15a3c : word) = Some W_15940.
Proof. vm_refl. Qed.
Lemma D_15940 : decode_any W_15940 = Some (Branch BC_LTU 13 11 608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15944 : bv 32 := 0x00bb85b3.
Lemma F_15944 : fetch_word Ubsan.M.loaded_segments (0x15a40 : word) = Some W_15944.
Proof. vm_refl. Qed.
Lemma D_15944 : decode_any W_15944 = Some (Op ALU_ADD 11 23 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15948 : bv 32 := 0x0035f613.
Lemma F_15948 : fetch_word Ubsan.M.loaded_segments (0x15a44 : word) = Some W_15948.
Proof. vm_refl. Qed.
Lemma D_15948 : decode_any W_15948 = Some (OpImm ALU_AND 12 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1594c : bv 32 := 0x24061a63.
Lemma F_1594c : fetch_word Ubsan.M.loaded_segments (0x15a48 : word) = Some W_1594c.
Proof. vm_refl. Qed.
Lemma D_1594c : decode_any W_1594c = Some (Branch BC_NE 12 0 596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15950 : bv 32 := 0x000a0513.
Lemma F_15950 : fetch_word Ubsan.M.loaded_segments (0x15a4c : word) = Some W_15950.
Proof. vm_refl. Qed.
Lemma D_15950 : decode_any W_15950 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15954 : bv 32 := 0x0005aa03.
Lemma F_15954 : fetch_word Ubsan.M.loaded_segments (0x15a50 : word) = Some W_15954.
Proof. vm_refl. Qed.
Lemma D_15954 : decode_any W_15954 = Some (Load SZ4 true 20 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15958 : bv 32 := 0x002b1593.
Lemma F_15958 : fetch_word Ubsan.M.loaded_segments (0x15a54 : word) = Some W_15958.
Proof. vm_refl. Qed.
Lemma D_15958 : decode_any W_15958 = Some (ShiftImm ALU_SLL 11 22 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1595c : bv 32 := 0x40b5053b.
Lemma F_1595c : fetch_word Ubsan.M.loaded_segments (0x15a58 : word) = Some W_1595c.
Proof. vm_refl. Qed.
Lemma D_1595c : decode_any W_1595c = Some (Op32 ALU_SUB 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15960 : bv 32 := 0xfe450a9b.
Lemma F_15960 : fetch_word Ubsan.M.loaded_segments (0x15a5c : word) = Some W_15960.
Proof. vm_refl. Qed.
Lemma D_15960 : decode_any W_15960 = Some (OpImm32 21 10 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15964 : bv 32 := 0x00810513.
Lemma F_15964 : fetch_word Ubsan.M.loaded_segments (0x15a60 : word) = Some W_15964.
Proof. vm_refl. Qed.
Lemma D_15964 : decode_any W_15964 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15968 : bv 32 := 0xf00fe0ef.
Lemma F_15968 : fetch_word Ubsan.M.loaded_segments (0x15a64 : word) = Some W_15968.
Proof. vm_refl. Qed.
Lemma D_15968 : decode_any W_15968 = Some (Jal 1 2090752, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1596c : bv 32 := 0x0d541c63.
Lemma F_1596c : fetch_word Ubsan.M.loaded_segments (0x15a68 : word) = Some W_1596c.
Proof. vm_refl. Qed.
Lemma D_1596c : decode_any W_1596c = Some (Branch BC_NE 8 21 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15970 : bv 32 := 0x0d441a63.
Lemma F_15970 : fetch_word Ubsan.M.loaded_segments (0x15a6c : word) = Some W_15970.
Proof. vm_refl. Qed.
Lemma D_15970 : decode_any W_15970 = Some (Branch BC_NE 8 20 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15974 : bv 32 := 0x00048513.
Lemma F_15974 : fetch_word Ubsan.M.loaded_segments (0x15a70 : word) = Some W_15974.
Proof. vm_refl. Qed.
Lemma D_15974 : decode_any W_15974 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15978 : bv 32 := 0x00090593.
Lemma F_15978 : fetch_word Ubsan.M.loaded_segments (0x15a74 : word) = Some W_15978.
Proof. vm_refl. Qed.
Lemma D_15978 : decode_any W_15978 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1597c : bv 32 := 0x00098613.
Lemma F_1597c : fetch_word Ubsan.M.loaded_segments (0x15a78 : word) = Some W_1597c.
Proof. vm_refl. Qed.
Lemma D_1597c : decode_any W_1597c = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15980 : bv 32 := 0x98cfe0ef.
Lemma F_15980 : fetch_word Ubsan.M.loaded_segments (0x15a7c : word) = Some W_15980.
Proof. vm_refl. Qed.
Lemma D_15980 : decode_any W_15980 = Some (Jal 1 2089356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15984 : bv 32 := 0x00a13023.
Lemma F_15984 : fetch_word Ubsan.M.loaded_segments (0x15a80 : word) = Some W_15984.
Proof. vm_refl. Qed.
Lemma D_15984 : decode_any W_15984 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15988 : bv 32 := 0x0e050a63.
Lemma F_15988 : fetch_word Ubsan.M.loaded_segments (0x15a84 : word) = Some W_15988.
Proof. vm_refl. Qed.
Lemma D_15988 : decode_any W_15988 = Some (Branch BC_EQ 10 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1598c : bv 32 := 0x000b091b.
Lemma F_1598c : fetch_word Ubsan.M.loaded_segments (0x15a88 : word) = Some W_1598c.
Proof. vm_refl. Qed.
Lemma D_1598c : decode_any W_1598c = Some (OpImm32 18 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15990 : bv 32 := 0x100b0a63.
Lemma F_15990 : fetch_word Ubsan.M.loaded_segments (0x15a8c : word) = Some W_15990.
Proof. vm_refl. Qed.
Lemma D_15990 : decode_any W_15990 = Some (Branch BC_EQ 22 0 276, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15994 : bv 32 := 0xfe700593.
Lemma F_15994 : fetch_word Ubsan.M.loaded_segments (0x15a90 : word) = Some W_15994.
Proof. vm_refl. Qed.
Lemma D_15994 : decode_any W_15994 = Some (OpImm ALU_ADD 11 0 4071, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15998 : bv 32 := 0x2175e463.
Lemma F_15998 : fetch_word Ubsan.M.loaded_segments (0x15a94 : word) = Some W_15998.
Proof. vm_refl. Qed.
Lemma D_15998 : decode_any W_15998 = Some (Branch BC_LTU 11 23 520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1599c : bv 32 := 0x018b8513.
Lemma F_1599c : fetch_word Ubsan.M.loaded_segments (0x15a98 : word) = Some W_1599c.
Proof. vm_refl. Qed.
Lemma D_1599c : decode_any W_1599c = Some (OpImm ALU_ADD 10 23 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159a0 : bv 32 := 0x00400593.
Lemma F_159a0 : fetch_word Ubsan.M.loaded_segments (0x15a9c : word) = Some W_159a0.
Proof. vm_refl. Qed.
Lemma D_159a0 : decode_any W_159a0 = Some (OpImm ALU_ADD 11 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159a4 : bv 32 := 0x00090613.
Lemma F_159a4 : fetch_word Ubsan.M.loaded_segments (0x15aa0 : word) = Some W_159a4.
Proof. vm_refl. Qed.
Lemma D_159a4 : decode_any W_159a4 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159a8 : bv 32 := 0xcb4ff0ef.
Lemma F_159a8 : fetch_word Ubsan.M.loaded_segments (0x15aa4 : word) = Some W_159a8.
Proof. vm_refl. Qed.
Lemma D_159a8 : decode_any W_159a8 = Some (Jal 1 2094260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159ac : bv 32 := 0x10050063.
Lemma F_159ac : fetch_word Ubsan.M.loaded_segments (0x15aa8 : word) = Some W_159ac.
Proof. vm_refl. Qed.
Lemma D_159ac : decode_any W_159ac = Some (Branch BC_EQ 10 0 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159b0 : bv 32 := 0x00050493.
Lemma F_159b0 : fetch_word Ubsan.M.loaded_segments (0x15aac : word) = Some W_159b0.
Proof. vm_refl. Qed.
Lemma D_159b0 : decode_any W_159b0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159b4 : bv 32 := 0x00013503.
Lemma F_159b4 : fetch_word Ubsan.M.loaded_segments (0x15ab0 : word) = Some W_159b4.
Proof. vm_refl. Qed.
Lemma D_159b4 : decode_any W_159b4 = Some (Load SZ8 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159b8 : bv 32 := 0x00048593.
Lemma F_159b8 : fetch_word Ubsan.M.loaded_segments (0x15ab4 : word) = Some W_159b8.
Proof. vm_refl. Qed.
Lemma D_159b8 : decode_any W_159b8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159bc : bv 32 := 0x849fe0ef.
Lemma F_159bc : fetch_word Ubsan.M.loaded_segments (0x15ab8 : word) = Some W_159bc.
Proof. vm_refl. Qed.
Lemma D_159bc : decode_any W_159bc = Some (Jal 1 2091080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159c0 : bv 32 := 0x10050e63.
Lemma F_159c0 : fetch_word Ubsan.M.loaded_segments (0x15abc : word) = Some W_159c0.
Proof. vm_refl. Qed.
Lemma D_159c0 : decode_any W_159c0 = Some (Branch BC_EQ 10 0 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159f4 : bv 32 := 0x0000a517.
Lemma F_159f4 : fetch_word Ubsan.M.loaded_segments (0x15af0 : word) = Some W_159f4.
Proof. vm_refl. Qed.
Lemma D_159f4 : decode_any W_159f4 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159f8 : bv 32 := 0xee053503.
Lemma F_159f8 : fetch_word Ubsan.M.loaded_segments (0x15af4 : word) = Some W_159f8.
Proof. vm_refl. Qed.
Lemma D_159f8 : decode_any W_159f8 = Some (Load SZ8 true 10 10 3808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159fc : bv 32 := 0x00052503.
Lemma F_159fc : fetch_word Ubsan.M.loaded_segments (0x15af8 : word) = Some W_159fc.
Proof. vm_refl. Qed.
Lemma D_159fc : decode_any W_159fc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a00 : bv 32 := 0x00500593.
Lemma F_15a00 : fetch_word Ubsan.M.loaded_segments (0x15afc : word) = Some W_15a00.
Proof. vm_refl. Qed.
Lemma D_15a00 : decode_any W_15a00 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a04 : bv 32 := 0x16a5c663.
Lemma F_15a04 : fetch_word Ubsan.M.loaded_segments (0x15b00 : word) = Some W_15a04.
Proof. vm_refl. Qed.
Lemma D_15a04 : decode_any W_15a04 = Some (Branch BC_LT 11 10 364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a08 : bv 32 := 0xffffb517.
Lemma F_15a08 : fetch_word Ubsan.M.loaded_segments (0x15b04 : word) = Some W_15a08.
Proof. vm_refl. Qed.
Lemma D_15a08 : decode_any W_15a08 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a0c : bv 32 := 0xffffb597.
Lemma F_15a0c : fetch_word Ubsan.M.loaded_segments (0x15b08 : word) = Some W_15a0c.
Proof. vm_refl. Qed.
Lemma D_15a0c : decode_any W_15a0c = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a10 : bv 32 := 0xd9d50513.
Lemma F_15a10 : fetch_word Ubsan.M.loaded_segments (0x15b0c : word) = Some W_15a10.
Proof. vm_refl. Qed.
Lemma D_15a10 : decode_any W_15a10 = Some (OpImm ALU_ADD 10 10 3485, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a14 : bv 32 := 0xba658593.
Lemma F_15a14 : fetch_word Ubsan.M.loaded_segments (0x15b10 : word) = Some W_15a14.
Proof. vm_refl. Qed.
Lemma D_15a14 : decode_any W_15a14 = Some (OpImm ALU_ADD 11 11 2982, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a18 : bv 32 := 0xe31ff06f.
Lemma F_15a18 : fetch_word Ubsan.M.loaded_segments (0x15b14 : word) = Some W_15a18.
Proof. vm_refl. Qed.
Lemma D_15a18 : decode_any W_15a18 = Some (Jal 0 2096688, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a1c : bv 32 := 0x0000a517.
Lemma F_15a1c : fetch_word Ubsan.M.loaded_segments (0x15b18 : word) = Some W_15a1c.
Proof. vm_refl. Qed.
Lemma D_15a1c : decode_any W_15a1c = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a20 : bv 32 := 0xeb853503.
Lemma F_15a20 : fetch_word Ubsan.M.loaded_segments (0x15b1c : word) = Some W_15a20.
Proof. vm_refl. Qed.
Lemma D_15a20 : decode_any W_15a20 = Some (Load SZ8 true 10 10 3768, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a24 : bv 32 := 0x00052503.
Lemma F_15a24 : fetch_word Ubsan.M.loaded_segments (0x15b20 : word) = Some W_15a24.
Proof. vm_refl. Qed.
Lemma D_15a24 : decode_any W_15a24 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a28 : bv 32 := 0x00500593.
Lemma F_15a28 : fetch_word Ubsan.M.loaded_segments (0x15b24 : word) = Some W_15a28.
Proof. vm_refl. Qed.
Lemma D_15a28 : decode_any W_15a28 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a2c : bv 32 := 0x14a5c263.
Lemma F_15a2c : fetch_word Ubsan.M.loaded_segments (0x15b28 : word) = Some W_15a2c.
Proof. vm_refl. Qed.
Lemma D_15a2c : decode_any W_15a2c = Some (Branch BC_LT 11 10 324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a30 : bv 32 := 0xffffb517.
Lemma F_15a30 : fetch_word Ubsan.M.loaded_segments (0x15b2c : word) = Some W_15a30.
Proof. vm_refl. Qed.
Lemma D_15a30 : decode_any W_15a30 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a34 : bv 32 := 0xffffb597.
Lemma F_15a34 : fetch_word Ubsan.M.loaded_segments (0x15b30 : word) = Some W_15a34.
Proof. vm_refl. Qed.
Lemma D_15a34 : decode_any W_15a34 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a38 : bv 32 := 0x9e550513.
Lemma F_15a38 : fetch_word Ubsan.M.loaded_segments (0x15b34 : word) = Some W_15a38.
Proof. vm_refl. Qed.
Lemma D_15a38 : decode_any W_15a38 = Some (OpImm ALU_ADD 10 10 2533, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a3c : bv 32 := 0xb7e58593.
Lemma F_15a3c : fetch_word Ubsan.M.loaded_segments (0x15b38 : word) = Some W_15a3c.
Proof. vm_refl. Qed.
Lemma D_15a3c : decode_any W_15a3c = Some (OpImm ALU_ADD 11 11 2942, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a40 : bv 32 := 0xe09ff06f.
Lemma F_15a40 : fetch_word Ubsan.M.loaded_segments (0x15b3c : word) = Some W_15a40.
Proof. vm_refl. Qed.
Lemma D_15a40 : decode_any W_15a40 = Some (Jal 0 2096648, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a44 : bv 32 := 0x0000a517.
Lemma F_15a44 : fetch_word Ubsan.M.loaded_segments (0x15b40 : word) = Some W_15a44.
Proof. vm_refl. Qed.
Lemma D_15a44 : decode_any W_15a44 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a48 : bv 32 := 0xe9053503.
Lemma F_15a48 : fetch_word Ubsan.M.loaded_segments (0x15b44 : word) = Some W_15a48.
Proof. vm_refl. Qed.
Lemma D_15a48 : decode_any W_15a48 = Some (Load SZ8 true 10 10 3728, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a4c : bv 32 := 0x00052503.
Lemma F_15a4c : fetch_word Ubsan.M.loaded_segments (0x15b48 : word) = Some W_15a4c.
Proof. vm_refl. Qed.
Lemma D_15a4c : decode_any W_15a4c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a50 : bv 32 := 0x00500593.
Lemma F_15a50 : fetch_word Ubsan.M.loaded_segments (0x15b4c : word) = Some W_15a50.
Proof. vm_refl. Qed.
Lemma D_15a50 : decode_any W_15a50 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a54 : bv 32 := 0x10a5ce63.
Lemma F_15a54 : fetch_word Ubsan.M.loaded_segments (0x15b50 : word) = Some W_15a54.
Proof. vm_refl. Qed.
Lemma D_15a54 : decode_any W_15a54 = Some (Branch BC_LT 11 10 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a58 : bv 32 := 0xffffb517.
Lemma F_15a58 : fetch_word Ubsan.M.loaded_segments (0x15b54 : word) = Some W_15a58.
Proof. vm_refl. Qed.
Lemma D_15a58 : decode_any W_15a58 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a5c : bv 32 := 0xffffb597.
Lemma F_15a5c : fetch_word Ubsan.M.loaded_segments (0x15b58 : word) = Some W_15a5c.
Proof. vm_refl. Qed.
Lemma D_15a5c : decode_any W_15a5c = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a60 : bv 32 := 0xa5e50513.
Lemma F_15a60 : fetch_word Ubsan.M.loaded_segments (0x15b5c : word) = Some W_15a60.
Proof. vm_refl. Qed.
Lemma D_15a60 : decode_any W_15a60 = Some (OpImm ALU_ADD 10 10 2654, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a64 : bv 32 := 0xb5658593.
Lemma F_15a64 : fetch_word Ubsan.M.loaded_segments (0x15b60 : word) = Some W_15a64.
Proof. vm_refl. Qed.
Lemma D_15a64 : decode_any W_15a64 = Some (OpImm ALU_ADD 11 11 2902, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a68 : bv 32 := 0x00040613.
Lemma F_15a68 : fetch_word Ubsan.M.loaded_segments (0x15b64 : word) = Some W_15a68.
Proof. vm_refl. Qed.
Lemma D_15a68 : decode_any W_15a68 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a6c : bv 32 := 0x000a8693.
Lemma F_15a6c : fetch_word Ubsan.M.loaded_segments (0x15b68 : word) = Some W_15a6c.
Proof. vm_refl. Qed.
Lemma D_15a6c : decode_any W_15a6c = Some (OpImm ALU_ADD 13 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a70 : bv 32 := 0x000a0713.
Lemma F_15a70 : fetch_word Ubsan.M.loaded_segments (0x15b6c : word) = Some W_15a70.
Proof. vm_refl. Qed.
Lemma D_15a70 : decode_any W_15a70 = Some (OpImm ALU_ADD 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a74 : bv 32 := 0xf99fd0ef.
Lemma F_15a74 : fetch_word Ubsan.M.loaded_segments (0x15b70 : word) = Some W_15a74.
Proof. vm_refl. Qed.
Lemma D_15a74 : decode_any W_15a74 = Some (Jal 1 2088856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a78 : bv 32 := 0x0f80006f.
Lemma F_15a78 : fetch_word Ubsan.M.loaded_segments (0x15b74 : word) = Some W_15a78.
Proof. vm_refl. Qed.
Lemma D_15a78 : decode_any W_15a78 = Some (Jal 0 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a7c : bv 32 := 0x0000a517.
Lemma F_15a7c : fetch_word Ubsan.M.loaded_segments (0x15b78 : word) = Some W_15a7c.
Proof. vm_refl. Qed.
Lemma D_15a7c : decode_any W_15a7c = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a80 : bv 32 := 0xe5853503.
Lemma F_15a80 : fetch_word Ubsan.M.loaded_segments (0x15b7c : word) = Some W_15a80.
Proof. vm_refl. Qed.
Lemma D_15a80 : decode_any W_15a80 = Some (Load SZ8 true 10 10 3672, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a84 : bv 32 := 0x00052503.
Lemma F_15a84 : fetch_word Ubsan.M.loaded_segments (0x15b80 : word) = Some W_15a84.
Proof. vm_refl. Qed.
Lemma D_15a84 : decode_any W_15a84 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a88 : bv 32 := 0x00500593.
Lemma F_15a88 : fetch_word Ubsan.M.loaded_segments (0x15b84 : word) = Some W_15a88.
Proof. vm_refl. Qed.
Lemma D_15a88 : decode_any W_15a88 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a8c : bv 32 := 0x0ea5c263.
Lemma F_15a8c : fetch_word Ubsan.M.loaded_segments (0x15b88 : word) = Some W_15a8c.
Proof. vm_refl. Qed.
Lemma D_15a8c : decode_any W_15a8c = Some (Branch BC_LT 11 10 228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a90 : bv 32 := 0xffffb517.
Lemma F_15a90 : fetch_word Ubsan.M.loaded_segments (0x15b8c : word) = Some W_15a90.
Proof. vm_refl. Qed.
Lemma D_15a90 : decode_any W_15a90 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a94 : bv 32 := 0xffffb597.
Lemma F_15a94 : fetch_word Ubsan.M.loaded_segments (0x15b90 : word) = Some W_15a94.
Proof. vm_refl. Qed.
Lemma D_15a94 : decode_any W_15a94 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a98 : bv 32 := 0xd8950513.
Lemma F_15a98 : fetch_word Ubsan.M.loaded_segments (0x15b94 : word) = Some W_15a98.
Proof. vm_refl. Qed.
Lemma D_15a98 : decode_any W_15a98 = Some (OpImm ALU_ADD 10 10 3465, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a9c : bv 32 := 0xb1e58593.
Lemma F_15a9c : fetch_word Ubsan.M.loaded_segments (0x15b98 : word) = Some W_15a9c.
Proof. vm_refl. Qed.
Lemma D_15a9c : decode_any W_15a9c = Some (OpImm ALU_ADD 11 11 2846, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15aa0 : bv 32 := 0x0c40006f.
Lemma F_15aa0 : fetch_word Ubsan.M.loaded_segments (0x15b9c : word) = Some W_15aa0.
Proof. vm_refl. Qed.
Lemma D_15aa0 : decode_any W_15aa0 = Some (Jal 0 196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15aa4 : bv 32 := 0x00000493.
Lemma F_15aa4 : fetch_word Ubsan.M.loaded_segments (0x15ba0 : word) = Some W_15aa4.
Proof. vm_refl. Qed.
Lemma D_15aa4 : decode_any W_15aa4 = Some (OpImm ALU_ADD 9 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15aa8 : bv 32 := 0x0380006f.
Lemma F_15aa8 : fetch_word Ubsan.M.loaded_segments (0x15ba4 : word) = Some W_15aa8.
Proof. vm_refl. Qed.
Lemma D_15aa8 : decode_any W_15aa8 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15aac : bv 32 := 0x00010513.
Lemma F_15aac : fetch_word Ubsan.M.loaded_segments (0x15ba8 : word) = Some W_15aac.
Proof. vm_refl. Qed.
Lemma D_15aac : decode_any W_15aac = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ab0 : bv 32 := 0xdb8fe0ef.
Lemma F_15ab0 : fetch_word Ubsan.M.loaded_segments (0x15bac : word) = Some W_15ab0.
Proof. vm_refl. Qed.
Lemma D_15ab0 : decode_any W_15ab0 = Some (Jal 1 2090424, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ab4 : bv 32 := 0x0000a517.
Lemma F_15ab4 : fetch_word Ubsan.M.loaded_segments (0x15bb0 : word) = Some W_15ab4.
Proof. vm_refl. Qed.
Lemma D_15ab4 : decode_any W_15ab4 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ab8 : bv 32 := 0xe2053503.
Lemma F_15ab8 : fetch_word Ubsan.M.loaded_segments (0x15bb4 : word) = Some W_15ab8.
Proof. vm_refl. Qed.
Lemma D_15ab8 : decode_any W_15ab8 = Some (Load SZ8 true 10 10 3616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15abc : bv 32 := 0x00052503.
Lemma F_15abc : fetch_word Ubsan.M.loaded_segments (0x15bb8 : word) = Some W_15abc.
Proof. vm_refl. Qed.
Lemma D_15abc : decode_any W_15abc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ac0 : bv 32 := 0x00500593.
Lemma F_15ac0 : fetch_word Ubsan.M.loaded_segments (0x15bbc : word) = Some W_15ac0.
Proof. vm_refl. Qed.
Lemma D_15ac0 : decode_any W_15ac0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ac4 : bv 32 := 0x0aa5c663.
Lemma F_15ac4 : fetch_word Ubsan.M.loaded_segments (0x15bc0 : word) = Some W_15ac4.
Proof. vm_refl. Qed.
Lemma D_15ac4 : decode_any W_15ac4 = Some (Branch BC_LT 11 10 172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ac8 : bv 32 := 0xffffb517.
Lemma F_15ac8 : fetch_word Ubsan.M.loaded_segments (0x15bc4 : word) = Some W_15ac8.
Proof. vm_refl. Qed.
Lemma D_15ac8 : decode_any W_15ac8 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15acc : bv 32 := 0xffffb597.
Lemma F_15acc : fetch_word Ubsan.M.loaded_segments (0x15bc8 : word) = Some W_15acc.
Proof. vm_refl. Qed.
Lemma D_15acc : decode_any W_15acc = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ad0 : bv 32 := 0x00950513.
Lemma F_15ad0 : fetch_word Ubsan.M.loaded_segments (0x15bcc : word) = Some W_15ad0.
Proof. vm_refl. Qed.
Lemma D_15ad0 : decode_any W_15ad0 = Some (OpImm ALU_ADD 10 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ad4 : bv 32 := 0xae658593.
Lemma F_15ad4 : fetch_word Ubsan.M.loaded_segments (0x15bd0 : word) = Some W_15ad4.
Proof. vm_refl. Qed.
Lemma D_15ad4 : decode_any W_15ad4 = Some (OpImm ALU_ADD 11 11 2790, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ad8 : bv 32 := 0x08c0006f.
Lemma F_15ad8 : fetch_word Ubsan.M.loaded_segments (0x15bd4 : word) = Some W_15ad8.
Proof. vm_refl. Qed.
Lemma D_15ad8 : decode_any W_15ad8 = Some (Jal 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15adc : bv 32 := 0x00013503.
Lemma F_15adc : fetch_word Ubsan.M.loaded_segments (0x15bd8 : word) = Some W_15adc.
Proof. vm_refl. Qed.
Lemma D_15adc : decode_any W_15adc = Some (Load SZ8 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ae0 : bv 32 := 0xa3dfe0ef.
Lemma F_15ae0 : fetch_word Ubsan.M.loaded_segments (0x15bdc : word) = Some W_15ae0.
Proof. vm_refl. Qed.
Lemma D_15ae0 : decode_any W_15ae0 = Some (Jal 1 2091580, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ae4 : bv 32 := 0xfe300593.
Lemma F_15ae4 : fetch_word Ubsan.M.loaded_segments (0x15be0 : word) = Some W_15ae4.
Proof. vm_refl. Qed.
Lemma D_15ae4 : decode_any W_15ae4 = Some (OpImm ALU_ADD 11 0 4067, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ae8 : bv 32 := 0x0b75ec63.
Lemma F_15ae8 : fetch_word Ubsan.M.loaded_segments (0x15be4 : word) = Some W_15ae8.
Proof. vm_refl. Qed.
Lemma D_15ae8 : decode_any W_15ae8 = Some (Branch BC_LTU 11 23 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15aec : bv 32 := 0x01cb8593.
Lemma F_15aec : fetch_word Ubsan.M.loaded_segments (0x15be8 : word) = Some W_15aec.
Proof. vm_refl. Qed.
Lemma D_15aec : decode_any W_15aec = Some (OpImm ALU_ADD 11 23 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15af0 : bv 32 := 0x00291913.
Lemma F_15af0 : fetch_word Ubsan.M.loaded_segments (0x15bec : word) = Some W_15af0.
Proof. vm_refl. Qed.
Lemma D_15af0 : decode_any W_15af0 = Some (ShiftImm ALU_SLL 18 18 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15af4 : bv 32 := 0xfff5c613.
Lemma F_15af4 : fetch_word Ubsan.M.loaded_segments (0x15bf0 : word) = Some W_15af4.
Proof. vm_refl. Qed.
Lemma D_15af4 : decode_any W_15af4 = Some (OpImm ALU_XOR 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15af8 : bv 32 := 0x0b266463.
Lemma F_15af8 : fetch_word Ubsan.M.loaded_segments (0x15bf4 : word) = Some W_15af8.
Proof. vm_refl. Qed.
Lemma D_15af8 : decode_any W_15af8 = Some (Branch BC_LTU 12 18 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15afc : bv 32 := 0x012585b3.
Lemma F_15afc : fetch_word Ubsan.M.loaded_segments (0x15bf8 : word) = Some W_15afc.
Proof. vm_refl. Qed.
Lemma D_15afc : decode_any W_15afc = Some (Op ALU_ADD 11 11 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b00 : bv 32 := 0x00b56633.
Lemma F_15b00 : fetch_word Ubsan.M.loaded_segments (0x15bfc : word) = Some W_15b00.
Proof. vm_refl. Qed.
Lemma D_15b00 : decode_any W_15b00 = Some (Op ALU_OR 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b04 : bv 32 := 0x00367613.
Lemma F_15b04 : fetch_word Ubsan.M.loaded_segments (0x15c00 : word) = Some W_15b04.
Proof. vm_refl. Qed.
Lemma D_15b04 : decode_any W_15b04 = Some (OpImm ALU_AND 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b08 : bv 32 := 0x08061c63.
Lemma F_15b08 : fetch_word Ubsan.M.loaded_segments (0x15c04 : word) = Some W_15b08.
Proof. vm_refl. Qed.
Lemma D_15b08 : decode_any W_15b08 = Some (Branch BC_NE 12 0 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b0c : bv 32 := 0x00040613.
Lemma F_15b0c : fetch_word Ubsan.M.loaded_segments (0x15c08 : word) = Some W_15b0c.
Proof. vm_refl. Qed.
Lemma D_15b0c : decode_any W_15b0c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b10 : bv 32 := 0x3a8080ef.
Lemma F_15b10 : fetch_word Ubsan.M.loaded_segments (0x15c0c : word) = Some W_15b10.
Proof. vm_refl. Qed.
Lemma D_15b10 : decode_any W_15b10 = Some (Jal 1 33704, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b14 : bv 32 := 0x000b0e63.
Lemma F_15b14 : fetch_word Ubsan.M.loaded_segments (0x15c10 : word) = Some W_15b14.
Proof. vm_refl. Qed.
Lemma D_15b14 : decode_any W_15b14 = Some (Branch BC_EQ 22 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b18 : bv 32 := 0x00013583.
Lemma F_15b18 : fetch_word Ubsan.M.loaded_segments (0x15c14 : word) = Some W_15b18.
Proof. vm_refl. Qed.
Lemma D_15b18 : decode_any W_15b18 = Some (Load SZ8 true 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b1c : bv 32 := 0x01410613.
Lemma F_15b1c : fetch_word Ubsan.M.loaded_segments (0x15c18 : word) = Some W_15b1c.
Proof. vm_refl. Qed.
Lemma D_15b1c : decode_any W_15b1c = Some (OpImm ALU_ADD 12 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b20 : bv 32 := 0x00048513.
Lemma F_15b20 : fetch_word Ubsan.M.loaded_segments (0x15c1c : word) = Some W_15b20.
Proof. vm_refl. Qed.
Lemma D_15b20 : decode_any W_15b20 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b24 : bv 32 := 0xf89fe0ef.
Lemma F_15b24 : fetch_word Ubsan.M.loaded_segments (0x15c20 : word) = Some W_15b24.
Proof. vm_refl. Qed.
Lemma D_15b24 : decode_any W_15b24 = Some (Jal 1 2092936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b28 : bv 32 := 0x01412503.
Lemma F_15b28 : fetch_word Ubsan.M.loaded_segments (0x15c24 : word) = Some W_15b28.
Proof. vm_refl. Qed.
Lemma D_15b28 : decode_any W_15b28 = Some (Load SZ4 true 10 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b2c : bv 32 := 0x00050663.
Lemma F_15b2c : fetch_word Ubsan.M.loaded_segments (0x15c28 : word) = Some W_15b2c.
Proof. vm_refl. Qed.
Lemma D_15b2c : decode_any W_15b2c = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b30 : bv 32 := 0x00013503.
Lemma F_15b30 : fetch_word Ubsan.M.loaded_segments (0x15c2c : word) = Some W_15b30.
Proof. vm_refl. Qed.
Lemma D_15b30 : decode_any W_15b30 = Some (Load SZ8 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b34 : bv 32 := 0x0400006f.
Lemma F_15b34 : fetch_word Ubsan.M.loaded_segments (0x15c30 : word) = Some W_15b34.
Proof. vm_refl. Qed.
Lemma D_15b34 : decode_any W_15b34 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b38 : bv 32 := 0x00010513.
Lemma F_15b38 : fetch_word Ubsan.M.loaded_segments (0x15c34 : word) = Some W_15b38.
Proof. vm_refl. Qed.
Lemma D_15b38 : decode_any W_15b38 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b3c : bv 32 := 0xd2cfe0ef.
Lemma F_15b3c : fetch_word Ubsan.M.loaded_segments (0x15c38 : word) = Some W_15b3c.
Proof. vm_refl. Qed.
Lemma D_15b3c : decode_any W_15b3c = Some (Jal 1 2090284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b40 : bv 32 := 0x0000a517.
Lemma F_15b40 : fetch_word Ubsan.M.loaded_segments (0x15c3c : word) = Some W_15b40.
Proof. vm_refl. Qed.
Lemma D_15b40 : decode_any W_15b40 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b44 : bv 32 := 0xd9453503.
Lemma F_15b44 : fetch_word Ubsan.M.loaded_segments (0x15c40 : word) = Some W_15b44.
Proof. vm_refl. Qed.
Lemma D_15b44 : decode_any W_15b44 = Some (Load SZ8 true 10 10 3476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b48 : bv 32 := 0x00052503.
Lemma F_15b48 : fetch_word Ubsan.M.loaded_segments (0x15c44 : word) = Some W_15b48.
Proof. vm_refl. Qed.
Lemma D_15b48 : decode_any W_15b48 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b4c : bv 32 := 0x00500593.
Lemma F_15b4c : fetch_word Ubsan.M.loaded_segments (0x15c48 : word) = Some W_15b4c.
Proof. vm_refl. Qed.
Lemma D_15b4c : decode_any W_15b4c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b50 : bv 32 := 0x02a5c063.
Lemma F_15b50 : fetch_word Ubsan.M.loaded_segments (0x15c4c : word) = Some W_15b50.
Proof. vm_refl. Qed.
Lemma D_15b50 : decode_any W_15b50 = Some (Branch BC_LT 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b54 : bv 32 := 0xffffa517.
Lemma F_15b54 : fetch_word Ubsan.M.loaded_segments (0x15c50 : word) = Some W_15b54.
Proof. vm_refl. Qed.
Lemma D_15b54 : decode_any W_15b54 = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b58 : bv 32 := 0xffffb597.
Lemma F_15b58 : fetch_word Ubsan.M.loaded_segments (0x15c54 : word) = Some W_15b58.
Proof. vm_refl. Qed.
Lemma D_15b58 : decode_any W_15b58 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b5c : bv 32 := 0x7e050513.
Lemma F_15b5c : fetch_word Ubsan.M.loaded_segments (0x15c58 : word) = Some W_15b5c.
Proof. vm_refl. Qed.
Lemma D_15b5c : decode_any W_15b5c = Some (OpImm ALU_ADD 10 10 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b60 : bv 32 := 0xa5a58593.
Lemma F_15b60 : fetch_word Ubsan.M.loaded_segments (0x15c5c : word) = Some W_15b60.
Proof. vm_refl. Qed.
Lemma D_15b60 : decode_any W_15b60 = Some (OpImm ALU_ADD 11 11 2650, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b64 : bv 32 := 0x00000613.
Lemma F_15b64 : fetch_word Ubsan.M.loaded_segments (0x15c60 : word) = Some W_15b64.
Proof. vm_refl. Qed.
Lemma D_15b64 : decode_any W_15b64 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b68 : bv 32 := 0xf41fd0ef.
Lemma F_15b68 : fetch_word Ubsan.M.loaded_segments (0x15c64 : word) = Some W_15b68.
Proof. vm_refl. Qed.
Lemma D_15b68 : decode_any W_15b68 = Some (Jal 1 2088768, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b6c : bv 32 := 0x0080006f.
Lemma F_15b6c : fetch_word Ubsan.M.loaded_segments (0x15c68 : word) = Some W_15b6c.
Proof. vm_refl. Qed.
Lemma D_15b6c : decode_any W_15b6c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b70 : bv 32 := 0x00000513.
Lemma F_15b70 : fetch_word Ubsan.M.loaded_segments (0x15c6c : word) = Some W_15b70.
Proof. vm_refl. Qed.
Lemma D_15b70 : decode_any W_15b70 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b74 : bv 32 := 0x05813083.
Lemma F_15b74 : fetch_word Ubsan.M.loaded_segments (0x15c70 : word) = Some W_15b74.
Proof. vm_refl. Qed.
Lemma D_15b74 : decode_any W_15b74 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b78 : bv 32 := 0x05013403.
Lemma F_15b78 : fetch_word Ubsan.M.loaded_segments (0x15c74 : word) = Some W_15b78.
Proof. vm_refl. Qed.
Lemma D_15b78 : decode_any W_15b78 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b7c : bv 32 := 0x04813483.
Lemma F_15b7c : fetch_word Ubsan.M.loaded_segments (0x15c78 : word) = Some W_15b7c.
Proof. vm_refl. Qed.
Lemma D_15b7c : decode_any W_15b7c = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b80 : bv 32 := 0x04013903.
Lemma F_15b80 : fetch_word Ubsan.M.loaded_segments (0x15c7c : word) = Some W_15b80.
Proof. vm_refl. Qed.
Lemma D_15b80 : decode_any W_15b80 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b84 : bv 32 := 0x03813983.
Lemma F_15b84 : fetch_word Ubsan.M.loaded_segments (0x15c80 : word) = Some W_15b84.
Proof. vm_refl. Qed.
Lemma D_15b84 : decode_any W_15b84 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b88 : bv 32 := 0x03013a03.
Lemma F_15b88 : fetch_word Ubsan.M.loaded_segments (0x15c84 : word) = Some W_15b88.
Proof. vm_refl. Qed.
Lemma D_15b88 : decode_any W_15b88 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b8c : bv 32 := 0x02813a83.
Lemma F_15b8c : fetch_word Ubsan.M.loaded_segments (0x15c88 : word) = Some W_15b8c.
Proof. vm_refl. Qed.
Lemma D_15b8c : decode_any W_15b8c = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b90 : bv 32 := 0x02013b03.
Lemma F_15b90 : fetch_word Ubsan.M.loaded_segments (0x15c8c : word) = Some W_15b90.
Proof. vm_refl. Qed.
Lemma D_15b90 : decode_any W_15b90 = Some (Load SZ8 true 22 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b94 : bv 32 := 0x01813b83.
Lemma F_15b94 : fetch_word Ubsan.M.loaded_segments (0x15c90 : word) = Some W_15b94.
Proof. vm_refl. Qed.
Lemma D_15b94 : decode_any W_15b94 = Some (Load SZ8 true 23 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b98 : bv 32 := 0x06010113.
Lemma F_15b98 : fetch_word Ubsan.M.loaded_segments (0x15c94 : word) = Some W_15b98.
Proof. vm_refl. Qed.
Lemma D_15b98 : decode_any W_15b98 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b9c : bv 32 := 0x00008067.
Lemma F_15b9c : fetch_word Ubsan.M.loaded_segments (0x15c98 : word) = Some W_15b9c.
Proof. vm_refl. Qed.
Lemma D_15b9c : decode_any W_15b9c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ba4 : bv 32 := 0xfe010113.
Lemma F_15ba4 : fetch_word Ubsan.M.loaded_segments (0x15ca0 : word) = Some W_15ba4.
Proof. vm_refl. Qed.
Lemma D_15ba4 : decode_any W_15ba4 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ba8 : bv 32 := 0x00113c23.
Lemma F_15ba8 : fetch_word Ubsan.M.loaded_segments (0x15ca4 : word) = Some W_15ba8.
Proof. vm_refl. Qed.
Lemma D_15ba8 : decode_any W_15ba8 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bac : bv 32 := 0x00813823.
Lemma F_15bac : fetch_word Ubsan.M.loaded_segments (0x15ca8 : word) = Some W_15bac.
Proof. vm_refl. Qed.
Lemma D_15bac : decode_any W_15bac = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bb0 : bv 32 := 0x00913423.
Lemma F_15bb0 : fetch_word Ubsan.M.loaded_segments (0x15cac : word) = Some W_15bb0.
Proof. vm_refl. Qed.
Lemma D_15bb0 : decode_any W_15bb0 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bb4 : bv 32 := 0x06b05263.
Lemma F_15bb4 : fetch_word Ubsan.M.loaded_segments (0x15cb0 : word) = Some W_15bb4.
Proof. vm_refl. Qed.
Lemma D_15bb4 : decode_any W_15bb4 = Some (Branch BC_GE 0 11 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bb8 : bv 32 := 0x08a05063.
Lemma F_15bb8 : fetch_word Ubsan.M.loaded_segments (0x15cb4 : word) = Some W_15bb8.
Proof. vm_refl. Qed.
Lemma D_15bb8 : decode_any W_15bb8 = Some (Branch BC_GE 0 10 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bbc : bv 32 := 0x02a58633.
Lemma F_15bbc : fetch_word Ubsan.M.loaded_segments (0x15cb8 : word) = Some W_15bbc.
Proof. vm_refl. Qed.
Lemma D_15bbc : decode_any W_15bbc = Some (Mul M_MUL 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bc0 : bv 32 := 0x01d65613.
Lemma F_15bc0 : fetch_word Ubsan.M.loaded_segments (0x15cbc : word) = Some W_15bc0.
Proof. vm_refl. Qed.
Lemma D_15bc0 : decode_any W_15bc0 = Some (ShiftImm ALU_SRL 12 12 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bc4 : bv 32 := 0x08060a63.
Lemma F_15bc4 : fetch_word Ubsan.M.loaded_segments (0x15cc0 : word) = Some W_15bc4.
Proof. vm_refl. Qed.
Lemma D_15bc4 : decode_any W_15bc4 = Some (Branch BC_EQ 12 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c58 : bv 32 := 0x00050493.
Lemma F_15c58 : fetch_word Ubsan.M.loaded_segments (0x15d54 : word) = Some W_15c58.
Proof. vm_refl. Qed.
Lemma D_15c58 : decode_any W_15c58 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c5c : bv 32 := 0x00058413.
Lemma F_15c5c : fetch_word Ubsan.M.loaded_segments (0x15d58 : word) = Some W_15c5c.
Proof. vm_refl. Qed.
Lemma D_15c5c : decode_any W_15c5c = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c60 : bv 32 := 0x00100513.
Lemma F_15c60 : fetch_word Ubsan.M.loaded_segments (0x15d5c : word) = Some W_15c60.
Proof. vm_refl. Qed.
Lemma D_15c60 : decode_any W_15c60 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c64 : bv 32 := 0x01800593.
Lemma F_15c64 : fetch_word Ubsan.M.loaded_segments (0x15d60 : word) = Some W_15c64.
Proof. vm_refl. Qed.
Lemma D_15c64 : decode_any W_15c64 = Some (OpImm ALU_ADD 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c68 : bv 32 := 0x7e5000ef.
Lemma F_15c68 : fetch_word Ubsan.M.loaded_segments (0x15d64 : word) = Some W_15c68.
Proof. vm_refl. Qed.
Lemma D_15c68 : decode_any W_15c68 = Some (Jal 1 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c6c : bv 32 := 0x08050663.
Lemma F_15c6c : fetch_word Ubsan.M.loaded_segments (0x15d68 : word) = Some W_15c6c.
Proof. vm_refl. Qed.
Lemma D_15c6c : decode_any W_15c6c = Some (Branch BC_EQ 10 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c70 : bv 32 := 0x00757593.
Lemma F_15c70 : fetch_word Ubsan.M.loaded_segments (0x15d6c : word) = Some W_15c70.
Proof. vm_refl. Qed.
Lemma D_15c70 : decode_any W_15c70 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c74 : bv 32 := 0x08059263.
Lemma F_15c74 : fetch_word Ubsan.M.loaded_segments (0x15d70 : word) = Some W_15c74.
Proof. vm_refl. Qed.
Lemma D_15c74 : decode_any W_15c74 = Some (Branch BC_NE 11 0 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c78 : bv 32 := 0x00952023.
Lemma F_15c78 : fetch_word Ubsan.M.loaded_segments (0x15d74 : word) = Some W_15c78.
Proof. vm_refl. Qed.
Lemma D_15c78 : decode_any W_15c78 = Some (Store SZ4 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c7c : bv 32 := 0x00040593.
Lemma F_15c7c : fetch_word Ubsan.M.loaded_segments (0x15d78 : word) = Some W_15c7c.
Proof. vm_refl. Qed.
Lemma D_15c7c : decode_any W_15c7c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c80 : bv 32 := 0x00852223.
Lemma F_15c80 : fetch_word Ubsan.M.loaded_segments (0x15d7c : word) = Some W_15c80.
Proof. vm_refl. Qed.
Lemma D_15c80 : decode_any W_15c80 = Some (Store SZ4 10 8 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c84 : bv 32 := 0x00050413.
Lemma F_15c84 : fetch_word Ubsan.M.loaded_segments (0x15d80 : word) = Some W_15c84.
Proof. vm_refl. Qed.
Lemma D_15c84 : decode_any W_15c84 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c88 : bv 32 := 0x00048513.
Lemma F_15c88 : fetch_word Ubsan.M.loaded_segments (0x15d84 : word) = Some W_15c88.
Proof. vm_refl. Qed.
Lemma D_15c88 : decode_any W_15c88 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c8c : bv 32 := 0x070000ef.
Lemma F_15c8c : fetch_word Ubsan.M.loaded_segments (0x15d88 : word) = Some W_15c8c.
Proof. vm_refl. Qed.
Lemma D_15c8c : decode_any W_15c8c = Some (Jal 1 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c90 : bv 32 := 0x00050593.
Lemma F_15c90 : fetch_word Ubsan.M.loaded_segments (0x15d8c : word) = Some W_15c90.
Proof. vm_refl. Qed.
Lemma D_15c90 : decode_any W_15c90 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c94 : bv 32 := 0x00040513.
Lemma F_15c94 : fetch_word Ubsan.M.loaded_segments (0x15d90 : word) = Some W_15c94.
Proof. vm_refl. Qed.
Lemma D_15c94 : decode_any W_15c94 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c98 : bv 32 := 0x00b43823.
Lemma F_15c98 : fetch_word Ubsan.M.loaded_segments (0x15d94 : word) = Some W_15c98.
Proof. vm_refl. Qed.
Lemma D_15c98 : decode_any W_15c98 = Some (Store SZ8 8 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c9c : bv 32 := 0x04059463.
Lemma F_15c9c : fetch_word Ubsan.M.loaded_segments (0x15d98 : word) = Some W_15c9c.
Proof. vm_refl. Qed.
Lemma D_15c9c : decode_any W_15c9c = Some (Branch BC_NE 11 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ce4 : bv 32 := 0x01813083.
Lemma F_15ce4 : fetch_word Ubsan.M.loaded_segments (0x15de0 : word) = Some W_15ce4.
Proof. vm_refl. Qed.
Lemma D_15ce4 : decode_any W_15ce4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ce8 : bv 32 := 0x01013403.
Lemma F_15ce8 : fetch_word Ubsan.M.loaded_segments (0x15de4 : word) = Some W_15ce8.
Proof. vm_refl. Qed.
Lemma D_15ce8 : decode_any W_15ce8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15cec : bv 32 := 0x00813483.
Lemma F_15cec : fetch_word Ubsan.M.loaded_segments (0x15de8 : word) = Some W_15cec.
Proof. vm_refl. Qed.
Lemma D_15cec : decode_any W_15cec = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15cf0 : bv 32 := 0x02010113.
Lemma F_15cf0 : fetch_word Ubsan.M.loaded_segments (0x15dec : word) = Some W_15cf0.
Proof. vm_refl. Qed.
Lemma D_15cf0 : decode_any W_15cf0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15cf4 : bv 32 := 0x00008067.
Lemma F_15cf4 : fetch_word Ubsan.M.loaded_segments (0x15df0 : word) = Some W_15cf4.
Proof. vm_refl. Qed.
Lemma D_15cf4 : decode_any W_15cf4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15cfc : bv 32 := 0xfc010113.
Lemma F_15cfc : fetch_word Ubsan.M.loaded_segments (0x15df8 : word) = Some W_15cfc.
Proof. vm_refl. Qed.
Lemma D_15cfc : decode_any W_15cfc = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d00 : bv 32 := 0x02113c23.
Lemma F_15d00 : fetch_word Ubsan.M.loaded_segments (0x15dfc : word) = Some W_15d00.
Proof. vm_refl. Qed.
Lemma D_15d00 : decode_any W_15d00 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d04 : bv 32 := 0x02813823.
Lemma F_15d04 : fetch_word Ubsan.M.loaded_segments (0x15e00 : word) = Some W_15d04.
Proof. vm_refl. Qed.
Lemma D_15d04 : decode_any W_15d04 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d08 : bv 32 := 0x02913423.
Lemma F_15d08 : fetch_word Ubsan.M.loaded_segments (0x15e04 : word) = Some W_15d08.
Proof. vm_refl. Qed.
Lemma D_15d08 : decode_any W_15d08 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d0c : bv 32 := 0x03213023.
Lemma F_15d0c : fetch_word Ubsan.M.loaded_segments (0x15e08 : word) = Some W_15d0c.
Proof. vm_refl. Qed.
Lemma D_15d0c : decode_any W_15d0c = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d10 : bv 32 := 0x01313c23.
Lemma F_15d10 : fetch_word Ubsan.M.loaded_segments (0x15e0c : word) = Some W_15d10.
Proof. vm_refl. Qed.
Lemma D_15d10 : decode_any W_15d10 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d14 : bv 32 := 0x01413823.
Lemma F_15d14 : fetch_word Ubsan.M.loaded_segments (0x15e10 : word) = Some W_15d14.
Proof. vm_refl. Qed.
Lemma D_15d14 : decode_any W_15d14 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d18 : bv 32 := 0x01513423.
Lemma F_15d18 : fetch_word Ubsan.M.loaded_segments (0x15e14 : word) = Some W_15d18.
Proof. vm_refl. Qed.
Lemma D_15d18 : decode_any W_15d18 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d1c : bv 32 := 0x01613023.
Lemma F_15d1c : fetch_word Ubsan.M.loaded_segments (0x15e18 : word) = Some W_15d1c.
Proof. vm_refl. Qed.
Lemma D_15d1c : decode_any W_15d1c = Some (Store SZ8 2 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d20 : bv 32 := 0x00058413.
Lemma F_15d20 : fetch_word Ubsan.M.loaded_segments (0x15e1c : word) = Some W_15d20.
Proof. vm_refl. Qed.
Lemma D_15d20 : decode_any W_15d20 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d24 : bv 32 := 0xfffe85b7.
Lemma F_15d24 : fetch_word Ubsan.M.loaded_segments (0x15e20 : word) = Some W_15d24.
Proof. vm_refl. Qed.
Lemma D_15d24 : decode_any W_15d24 = Some (Lui 11 1048552, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d28 : bv 32 := 0x95f5859b.
Lemma F_15d28 : fetch_word Ubsan.M.loaded_segments (0x15e24 : word) = Some W_15d28.
Proof. vm_refl. Qed.
Lemma D_15d28 : decode_any W_15d28 = Some (OpImm32 11 11 2399, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d2c : bv 32 := 0x00b4063b.
Lemma F_15d2c : fetch_word Ubsan.M.loaded_segments (0x15e28 : word) = Some W_15d2c.
Proof. vm_refl. Qed.
Lemma D_15d2c : decode_any W_15d2c = Some (Op32 ALU_ADD 12 8 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d30 : bv 32 := 0x02c5e263.
Lemma F_15d30 : fetch_word Ubsan.M.loaded_segments (0x15e2c : word) = Some W_15d30.
Proof. vm_refl. Qed.
Lemma D_15d30 : decode_any W_15d30 = Some (Branch BC_LTU 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d54 : bv 32 := 0x00050493.
Lemma F_15d54 : fetch_word Ubsan.M.loaded_segments (0x15e50 : word) = Some W_15d54.
Proof. vm_refl. Qed.
Lemma D_15d54 : decode_any W_15d54 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d58 : bv 32 := 0x00b5053b.
Lemma F_15d58 : fetch_word Ubsan.M.loaded_segments (0x15e54 : word) = Some W_15d58.
Proof. vm_refl. Qed.
Lemma D_15d58 : decode_any W_15d58 = Some (Op32 ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d5c : bv 32 := 0x04a5ee63.
Lemma F_15d5c : fetch_word Ubsan.M.loaded_segments (0x15e58 : word) = Some W_15d5c.
Proof. vm_refl. Qed.
Lemma D_15d5c : decode_any W_15d5c = Some (Branch BC_LTU 11 10 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15db8 : bv 32 := 0x00800593.
Lemma F_15db8 : fetch_word Ubsan.M.loaded_segments (0x15eb4 : word) = Some W_15db8.
Proof. vm_refl. Qed.
Lemma D_15db8 : decode_any W_15db8 = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15dbc : bv 32 := 0x00048513.
Lemma F_15dbc : fetch_word Ubsan.M.loaded_segments (0x15eb8 : word) = Some W_15dbc.
Proof. vm_refl. Qed.
Lemma D_15dbc : decode_any W_15dbc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15dc0 : bv 32 := 0x68d000ef.
Lemma F_15dc0 : fetch_word Ubsan.M.loaded_segments (0x15ebc : word) = Some W_15dc0.
Proof. vm_refl. Qed.
Lemma D_15dc0 : decode_any W_15dc0 = Some (Jal 1 3724, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15dc4 : bv 32 := 0x00050913.
Lemma F_15dc4 : fetch_word Ubsan.M.loaded_segments (0x15ec0 : word) = Some W_15dc4.
Proof. vm_refl. Qed.
Lemma D_15dc4 : decode_any W_15dc4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15dc8 : bv 32 := 0x00a039b3.
Lemma F_15dc8 : fetch_word Ubsan.M.loaded_segments (0x15ec4 : word) = Some W_15dc8.
Proof. vm_refl. Qed.
Lemma D_15dc8 : decode_any W_15dc8 = Some (Op ALU_SLTU 19 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15dcc : bv 32 := 0x00757513.
Lemma F_15dcc : fetch_word Ubsan.M.loaded_segments (0x15ec8 : word) = Some W_15dcc.
Proof. vm_refl. Qed.
Lemma D_15dcc : decode_any W_15dcc = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15dd0 : bv 32 := 0x00153513.
Lemma F_15dd0 : fetch_word Ubsan.M.loaded_segments (0x15ecc : word) = Some W_15dd0.
Proof. vm_refl. Qed.
Lemma D_15dd0 : decode_any W_15dd0 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15dd4 : bv 32 := 0x01357a33.
Lemma F_15dd4 : fetch_word Ubsan.M.loaded_segments (0x15ed0 : word) = Some W_15dd4.
Proof. vm_refl. Qed.
Lemma D_15dd4 : decode_any W_15dd4 = Some (Op ALU_AND 20 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15dd8 : bv 32 := 0x00090a93.
Lemma F_15dd8 : fetch_word Ubsan.M.loaded_segments (0x15ed4 : word) = Some W_15dd8.
Proof. vm_refl. Qed.
Lemma D_15dd8 : decode_any W_15dd8 = Some (OpImm ALU_ADD 21 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ddc : bv 32 := 0x00090b13.
Lemma F_15ddc : fetch_word Ubsan.M.loaded_segments (0x15ed8 : word) = Some W_15ddc.
Proof. vm_refl. Qed.
Lemma D_15ddc : decode_any W_15ddc = Some (OpImm ALU_ADD 22 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15de0 : bv 32 := 0x00400593.
Lemma F_15de0 : fetch_word Ubsan.M.loaded_segments (0x15edc : word) = Some W_15de0.
Proof. vm_refl. Qed.
Lemma D_15de0 : decode_any W_15de0 = Some (OpImm ALU_ADD 11 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15de4 : bv 32 := 0x00040513.
Lemma F_15de4 : fetch_word Ubsan.M.loaded_segments (0x15ee0 : word) = Some W_15de4.
Proof. vm_refl. Qed.
Lemma D_15de4 : decode_any W_15de4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15de8 : bv 32 := 0x665000ef.
Lemma F_15de8 : fetch_word Ubsan.M.loaded_segments (0x15ee4 : word) = Some W_15de8.
Proof. vm_refl. Qed.
Lemma D_15de8 : decode_any W_15de8 = Some (Jal 1 3684, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15dec : bv 32 := 0x052b6a63.
Lemma F_15dec : fetch_word Ubsan.M.loaded_segments (0x15ee8 : word) = Some W_15dec.
Proof. vm_refl. Qed.
Lemma D_15dec : decode_any W_15dec = Some (Branch BC_LTU 22 18 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15df0 : bv 32 := 0x001b3593.
Lemma F_15df0 : fetch_word Ubsan.M.loaded_segments (0x15eec : word) = Some W_15df0.
Proof. vm_refl. Qed.
Lemma D_15df0 : decode_any W_15df0 = Some (OpImm ALU_SLTU 11 22 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15df4 : bv 32 := 0x00b9c5b3.
Lemma F_15df4 : fetch_word Ubsan.M.loaded_segments (0x15ef0 : word) = Some W_15df4.
Proof. vm_refl. Qed.
Lemma D_15df4 : decode_any W_15df4 = Some (Op ALU_XOR 11 19 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15df8 : bv 32 := 0x04058463.
Lemma F_15df8 : fetch_word Ubsan.M.loaded_segments (0x15ef4 : word) = Some W_15df8.
Proof. vm_refl. Qed.
Lemma D_15df8 : decode_any W_15df8 = Some (Branch BC_EQ 11 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15dfc : bv 32 := 0x040a0263.
Lemma F_15dfc : fetch_word Ubsan.M.loaded_segments (0x15ef8 : word) = Some W_15dfc.
Proof. vm_refl. Qed.
Lemma D_15dfc : decode_any W_15dfc = Some (Branch BC_EQ 20 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e00 : bv 32 := 0x00aab023.
Lemma F_15e00 : fetch_word Ubsan.M.loaded_segments (0x15efc : word) = Some W_15e00.
Proof. vm_refl. Qed.
Lemma D_15e00 : decode_any W_15e00 = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e04 : bv 32 := 0x008b0b13.
Lemma F_15e04 : fetch_word Ubsan.M.loaded_segments (0x15f00 : word) = Some W_15e04.
Proof. vm_refl. Qed.
Lemma D_15e04 : decode_any W_15e04 = Some (OpImm ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e08 : bv 32 := 0xfff48493.
Lemma F_15e08 : fetch_word Ubsan.M.loaded_segments (0x15f04 : word) = Some W_15e08.
Proof. vm_refl. Qed.
Lemma D_15e08 : decode_any W_15e08 = Some (OpImm ALU_ADD 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e0c : bv 32 := 0x008a8a93.
Lemma F_15e0c : fetch_word Ubsan.M.loaded_segments (0x15f08 : word) = Some W_15e0c.
Proof. vm_refl. Qed.
Lemma D_15e0c : decode_any W_15e0c = Some (OpImm ALU_ADD 21 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e10 : bv 32 := 0xfc0498e3.
Lemma F_15e10 : fetch_word Ubsan.M.loaded_segments (0x15f0c : word) = Some W_15e10.
Proof. vm_refl. Qed.
Lemma D_15e10 : decode_any W_15e10 = Some (Branch BC_NE 9 0 8144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e14 : bv 32 := 0x00090513.
Lemma F_15e14 : fetch_word Ubsan.M.loaded_segments (0x15f10 : word) = Some W_15e14.
Proof. vm_refl. Qed.
Lemma D_15e14 : decode_any W_15e14 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e18 : bv 32 := 0x03813083.
Lemma F_15e18 : fetch_word Ubsan.M.loaded_segments (0x15f14 : word) = Some W_15e18.
Proof. vm_refl. Qed.
Lemma D_15e18 : decode_any W_15e18 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e1c : bv 32 := 0x03013403.
Lemma F_15e1c : fetch_word Ubsan.M.loaded_segments (0x15f18 : word) = Some W_15e1c.
Proof. vm_refl. Qed.
Lemma D_15e1c : decode_any W_15e1c = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e20 : bv 32 := 0x02813483.
Lemma F_15e20 : fetch_word Ubsan.M.loaded_segments (0x15f1c : word) = Some W_15e20.
Proof. vm_refl. Qed.
Lemma D_15e20 : decode_any W_15e20 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e24 : bv 32 := 0x02013903.
Lemma F_15e24 : fetch_word Ubsan.M.loaded_segments (0x15f20 : word) = Some W_15e24.
Proof. vm_refl. Qed.
Lemma D_15e24 : decode_any W_15e24 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e28 : bv 32 := 0x01813983.
Lemma F_15e28 : fetch_word Ubsan.M.loaded_segments (0x15f24 : word) = Some W_15e28.
Proof. vm_refl. Qed.
Lemma D_15e28 : decode_any W_15e28 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e2c : bv 32 := 0x01013a03.
Lemma F_15e2c : fetch_word Ubsan.M.loaded_segments (0x15f28 : word) = Some W_15e2c.
Proof. vm_refl. Qed.
Lemma D_15e2c : decode_any W_15e2c = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e30 : bv 32 := 0x00813a83.
Lemma F_15e30 : fetch_word Ubsan.M.loaded_segments (0x15f2c : word) = Some W_15e30.
Proof. vm_refl. Qed.
Lemma D_15e30 : decode_any W_15e30 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e34 : bv 32 := 0x00013b03.
Lemma F_15e34 : fetch_word Ubsan.M.loaded_segments (0x15f30 : word) = Some W_15e34.
Proof. vm_refl. Qed.
Lemma D_15e34 : decode_any W_15e34 = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e38 : bv 32 := 0x04010113.
Lemma F_15e38 : fetch_word Ubsan.M.loaded_segments (0x15f34 : word) = Some W_15e38.
Proof. vm_refl. Qed.
Lemma D_15e38 : decode_any W_15e38 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e3c : bv 32 := 0x00008067.
Lemma F_15e3c : fetch_word Ubsan.M.loaded_segments (0x15f38 : word) = Some W_15e3c.
Proof. vm_refl. Qed.
Lemma D_15e3c : decode_any W_15e3c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e44 : bv 32 := 0xfd010113.
Lemma F_15e44 : fetch_word Ubsan.M.loaded_segments (0x15f40 : word) = Some W_15e44.
Proof. vm_refl. Qed.
Lemma D_15e44 : decode_any W_15e44 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e48 : bv 32 := 0x02113423.
Lemma F_15e48 : fetch_word Ubsan.M.loaded_segments (0x15f44 : word) = Some W_15e48.
Proof. vm_refl. Qed.
Lemma D_15e48 : decode_any W_15e48 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e4c : bv 32 := 0x02813023.
Lemma F_15e4c : fetch_word Ubsan.M.loaded_segments (0x15f48 : word) = Some W_15e4c.
Proof. vm_refl. Qed.
Lemma D_15e4c : decode_any W_15e4c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e50 : bv 32 := 0x00913c23.
Lemma F_15e50 : fetch_word Ubsan.M.loaded_segments (0x15f4c : word) = Some W_15e50.
Proof. vm_refl. Qed.
Lemma D_15e50 : decode_any W_15e50 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e54 : bv 32 := 0x01213823.
Lemma F_15e54 : fetch_word Ubsan.M.loaded_segments (0x15f50 : word) = Some W_15e54.
Proof. vm_refl. Qed.
Lemma D_15e54 : decode_any W_15e54 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e58 : bv 32 := 0x01313423.
Lemma F_15e58 : fetch_word Ubsan.M.loaded_segments (0x15f54 : word) = Some W_15e58.
Proof. vm_refl. Qed.
Lemma D_15e58 : decode_any W_15e58 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e5c : bv 32 := 0x08050663.
Lemma F_15e5c : fetch_word Ubsan.M.loaded_segments (0x15f58 : word) = Some W_15e5c.
Proof. vm_refl. Qed.
Lemma D_15e5c : decode_any W_15e5c = Some (Branch BC_EQ 10 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e60 : bv 32 := 0x00050413.
Lemma F_15e60 : fetch_word Ubsan.M.loaded_segments (0x15f5c : word) = Some W_15e60.
Proof. vm_refl. Qed.
Lemma D_15e60 : decode_any W_15e60 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e64 : bv 32 := 0x00757513.
Lemma F_15e64 : fetch_word Ubsan.M.loaded_segments (0x15f60 : word) = Some W_15e64.
Proof. vm_refl. Qed.
Lemma D_15e64 : decode_any W_15e64 = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e68 : bv 32 := 0x0c051e63.
Lemma F_15e68 : fetch_word Ubsan.M.loaded_segments (0x15f64 : word) = Some W_15e68.
Proof. vm_refl. Qed.
Lemma D_15e68 : decode_any W_15e68 = Some (Branch BC_NE 10 0 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e6c : bv 32 := 0x00043483.
Lemma F_15e6c : fetch_word Ubsan.M.loaded_segments (0x15f68 : word) = Some W_15e6c.
Proof. vm_refl. Qed.
Lemma D_15e6c : decode_any W_15e6c = Some (Load SZ8 true 9 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e70 : bv 32 := 0x0a048c63.
Lemma F_15e70 : fetch_word Ubsan.M.loaded_segments (0x15f6c : word) = Some W_15e70.
Proof. vm_refl. Qed.
Lemma D_15e70 : decode_any W_15e70 = Some (Branch BC_EQ 9 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e74 : bv 32 := 0x0074f513.
Lemma F_15e74 : fetch_word Ubsan.M.loaded_segments (0x15f70 : word) = Some W_15e74.
Proof. vm_refl. Qed.
Lemma D_15e74 : decode_any W_15e74 = Some (OpImm ALU_AND 10 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e78 : bv 32 := 0x0c051663.
Lemma F_15e78 : fetch_word Ubsan.M.loaded_segments (0x15f74 : word) = Some W_15e78.
Proof. vm_refl. Qed.
Lemma D_15e78 : decode_any W_15e78 = Some (Branch BC_NE 10 0 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e7c : bv 32 := 0x0004a503.
Lemma F_15e7c : fetch_word Ubsan.M.loaded_segments (0x15f78 : word) = Some W_15e7c.
Proof. vm_refl. Qed.
Lemma D_15e7c : decode_any W_15e7c = Some (Load SZ4 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e80 : bv 32 := 0x04a05863.
Lemma F_15e80 : fetch_word Ubsan.M.loaded_segments (0x15f7c : word) = Some W_15e80.
Proof. vm_refl. Qed.
Lemma D_15e80 : decode_any W_15e80 = Some (Branch BC_GE 0 10 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e84 : bv 32 := 0x00000913.
Lemma F_15e84 : fetch_word Ubsan.M.loaded_segments (0x15f80 : word) = Some W_15e84.
Proof. vm_refl. Qed.
Lemma D_15e84 : decode_any W_15e84 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e88 : bv 32 := 0x00000993.
Lemma F_15e88 : fetch_word Ubsan.M.loaded_segments (0x15f84 : word) = Some W_15e88.
Proof. vm_refl. Qed.
Lemma D_15e88 : decode_any W_15e88 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e8c : bv 32 := 0x0104b583.
Lemma F_15e8c : fetch_word Ubsan.M.loaded_segments (0x15f88 : word) = Some W_15e8c.
Proof. vm_refl. Qed.
Lemma D_15e8c : decode_any W_15e8c = Some (Load SZ8 true 11 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e90 : bv 32 := 0x01258533.
Lemma F_15e90 : fetch_word Ubsan.M.loaded_segments (0x15f8c : word) = Some W_15e90.
Proof. vm_refl. Qed.
Lemma D_15e90 : decode_any W_15e90 = Some (Op ALU_ADD 10 11 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e94 : bv 32 := 0x0ab56863.
Lemma F_15e94 : fetch_word Ubsan.M.loaded_segments (0x15f90 : word) = Some W_15e94.
Proof. vm_refl. Qed.
Lemma D_15e94 : decode_any W_15e94 = Some (Branch BC_LTU 10 11 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e98 : bv 32 := 0x00b03633.
Lemma F_15e98 : fetch_word Ubsan.M.loaded_segments (0x15f94 : word) = Some W_15e98.
Proof. vm_refl. Qed.
Lemma D_15e98 : decode_any W_15e98 = Some (Op ALU_SLTU 12 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e9c : bv 32 := 0x00153693.
Lemma F_15e9c : fetch_word Ubsan.M.loaded_segments (0x15f98 : word) = Some W_15e9c.
Proof. vm_refl. Qed.
Lemma D_15e9c : decode_any W_15e9c = Some (OpImm ALU_SLTU 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ea0 : bv 32 := 0x00d64633.
Lemma F_15ea0 : fetch_word Ubsan.M.loaded_segments (0x15f9c : word) = Some W_15ea0.
Proof. vm_refl. Qed.
Lemma D_15ea0 : decode_any W_15ea0 = Some (Op ALU_XOR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ea4 : bv 32 := 0x0a060063.
Lemma F_15ea4 : fetch_word Ubsan.M.loaded_segments (0x15fa0 : word) = Some W_15ea4.
Proof. vm_refl. Qed.
Lemma D_15ea4 : decode_any W_15ea4 = Some (Branch BC_EQ 12 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ea8 : bv 32 := 0x08058e63.
Lemma F_15ea8 : fetch_word Ubsan.M.loaded_segments (0x15fa4 : word) = Some W_15ea8.
Proof. vm_refl. Qed.
Lemma D_15ea8 : decode_any W_15ea8 = Some (Branch BC_EQ 11 0 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15eac : bv 32 := 0x00b905b3.
Lemma F_15eac : fetch_word Ubsan.M.loaded_segments (0x15fa8 : word) = Some W_15eac.
Proof. vm_refl. Qed.
Lemma D_15eac : decode_any W_15eac = Some (Op ALU_ADD 11 18 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15eb0 : bv 32 := 0x0075f593.
Lemma F_15eb0 : fetch_word Ubsan.M.loaded_segments (0x15fac : word) = Some W_15eb0.
Proof. vm_refl. Qed.
Lemma D_15eb0 : decode_any W_15eb0 = Some (OpImm ALU_AND 11 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15eb4 : bv 32 := 0x08059863.
Lemma F_15eb4 : fetch_word Ubsan.M.loaded_segments (0x15fb0 : word) = Some W_15eb4.
Proof. vm_refl. Qed.
Lemma D_15eb4 : decode_any W_15eb4 = Some (Branch BC_NE 11 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15eb8 : bv 32 := 0x00053503.
Lemma F_15eb8 : fetch_word Ubsan.M.loaded_segments (0x15fb4 : word) = Some W_15eb8.
Proof. vm_refl. Qed.
Lemma D_15eb8 : decode_any W_15eb8 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ebc : bv 32 := 0x6c9000ef.
Lemma F_15ebc : fetch_word Ubsan.M.loaded_segments (0x15fb8 : word) = Some W_15ebc.
Proof. vm_refl. Qed.
Lemma D_15ebc : decode_any W_15ebc = Some (Jal 1 3784, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ec0 : bv 32 := 0x0004a503.
Lemma F_15ec0 : fetch_word Ubsan.M.loaded_segments (0x15fbc : word) = Some W_15ec0.
Proof. vm_refl. Qed.
Lemma D_15ec0 : decode_any W_15ec0 = Some (Load SZ4 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ec4 : bv 32 := 0x00198993.
Lemma F_15ec4 : fetch_word Ubsan.M.loaded_segments (0x15fc0 : word) = Some W_15ec4.
Proof. vm_refl. Qed.
Lemma D_15ec4 : decode_any W_15ec4 = Some (OpImm ALU_ADD 19 19 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ec8 : bv 32 := 0x00890913.
Lemma F_15ec8 : fetch_word Ubsan.M.loaded_segments (0x15fc4 : word) = Some W_15ec8.
Proof. vm_refl. Qed.
Lemma D_15ec8 : decode_any W_15ec8 = Some (OpImm ALU_ADD 18 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ecc : bv 32 := 0xfca9c0e3.
Lemma F_15ecc : fetch_word Ubsan.M.loaded_segments (0x15fc8 : word) = Some W_15ecc.
Proof. vm_refl. Qed.
Lemma D_15ecc : decode_any W_15ecc = Some (Branch BC_LT 19 10 8128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ed0 : bv 32 := 0x0104b503.
Lemma F_15ed0 : fetch_word Ubsan.M.loaded_segments (0x15fcc : word) = Some W_15ed0.
Proof. vm_refl. Qed.
Lemma D_15ed0 : decode_any W_15ed0 = Some (Load SZ8 true 10 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ed4 : bv 32 := 0x6b1000ef.
Lemma F_15ed4 : fetch_word Ubsan.M.loaded_segments (0x15fd0 : word) = Some W_15ed4.
Proof. vm_refl. Qed.
Lemma D_15ed4 : decode_any W_15ed4 = Some (Jal 1 3760, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ed8 : bv 32 := 0x00048513.
Lemma F_15ed8 : fetch_word Ubsan.M.loaded_segments (0x15fd4 : word) = Some W_15ed8.
Proof. vm_refl. Qed.
Lemma D_15ed8 : decode_any W_15ed8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15edc : bv 32 := 0x6a9000ef.
Lemma F_15edc : fetch_word Ubsan.M.loaded_segments (0x15fd8 : word) = Some W_15edc.
Proof. vm_refl. Qed.
Lemma D_15edc : decode_any W_15edc = Some (Jal 1 3752, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ee0 : bv 32 := 0x00043023.
Lemma F_15ee0 : fetch_word Ubsan.M.loaded_segments (0x15fdc : word) = Some W_15ee0.
Proof. vm_refl. Qed.
Lemma D_15ee0 : decode_any W_15ee0 = Some (Store SZ8 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ee4 : bv 32 := 0x0440006f.
Lemma F_15ee4 : fetch_word Ubsan.M.loaded_segments (0x15fe0 : word) = Some W_15ee4.
Proof. vm_refl. Qed.
Lemma D_15ee4 : decode_any W_15ee4 = Some (Jal 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f28 : bv 32 := 0x02813083.
Lemma F_15f28 : fetch_word Ubsan.M.loaded_segments (0x16024 : word) = Some W_15f28.
Proof. vm_refl. Qed.
Lemma D_15f28 : decode_any W_15f28 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f2c : bv 32 := 0x02013403.
Lemma F_15f2c : fetch_word Ubsan.M.loaded_segments (0x16028 : word) = Some W_15f2c.
Proof. vm_refl. Qed.
Lemma D_15f2c : decode_any W_15f2c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f30 : bv 32 := 0x01813483.
Lemma F_15f30 : fetch_word Ubsan.M.loaded_segments (0x1602c : word) = Some W_15f30.
Proof. vm_refl. Qed.
Lemma D_15f30 : decode_any W_15f30 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f34 : bv 32 := 0x01013903.
Lemma F_15f34 : fetch_word Ubsan.M.loaded_segments (0x16030 : word) = Some W_15f34.
Proof. vm_refl. Qed.
Lemma D_15f34 : decode_any W_15f34 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f38 : bv 32 := 0x00813983.
Lemma F_15f38 : fetch_word Ubsan.M.loaded_segments (0x16034 : word) = Some W_15f38.
Proof. vm_refl. Qed.
Lemma D_15f38 : decode_any W_15f38 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f3c : bv 32 := 0x03010113.
Lemma F_15f3c : fetch_word Ubsan.M.loaded_segments (0x16038 : word) = Some W_15f3c.
Proof. vm_refl. Qed.
Lemma D_15f3c : decode_any W_15f3c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f40 : bv 32 := 0x00008067.
Lemma F_15f40 : fetch_word Ubsan.M.loaded_segments (0x1603c : word) = Some W_15f40.
Proof. vm_refl. Qed.
Lemma D_15f40 : decode_any W_15f40 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f48 : bv 32 := 0x0a050863.
Lemma F_15f48 : fetch_word Ubsan.M.loaded_segments (0x16044 : word) = Some W_15f48.
Proof. vm_refl. Qed.
Lemma D_15f48 : decode_any W_15f48 = Some (Branch BC_EQ 10 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f4c : bv 32 := 0x0805c063.
Lemma F_15f4c : fetch_word Ubsan.M.loaded_segments (0x16048 : word) = Some W_15f4c.
Proof. vm_refl. Qed.
Lemma D_15f4c : decode_any W_15f4c = Some (Branch BC_LT 11 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f50 : bv 32 := 0x00757693.
Lemma F_15f50 : fetch_word Ubsan.M.loaded_segments (0x1604c : word) = Some W_15f50.
Proof. vm_refl. Qed.
Lemma D_15f50 : decode_any W_15f50 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f54 : bv 32 := 0x10069263.
Lemma F_15f54 : fetch_word Ubsan.M.loaded_segments (0x16050 : word) = Some W_15f54.
Proof. vm_refl. Qed.
Lemma D_15f54 : decode_any W_15f54 = Some (Branch BC_NE 13 0 260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f58 : bv 32 := 0x00052683.
Lemma F_15f58 : fetch_word Ubsan.M.loaded_segments (0x16054 : word) = Some W_15f58.
Proof. vm_refl. Qed.
Lemma D_15f58 : decode_any W_15f58 = Some (Load SZ4 true 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f5c : bv 32 := 0x06d5d863.
Lemma F_15f5c : fetch_word Ubsan.M.loaded_segments (0x16058 : word) = Some W_15f5c.
Proof. vm_refl. Qed.
Lemma D_15f5c : decode_any W_15f5c = Some (Branch BC_GE 11 13 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f60 : bv 32 := 0x0c064263.
Lemma F_15f60 : fetch_word Ubsan.M.loaded_segments (0x1605c : word) = Some W_15f60.
Proof. vm_refl. Qed.
Lemma D_15f60 : decode_any W_15f60 = Some (Branch BC_LT 12 0 196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f64 : bv 32 := 0x00452683.
Lemma F_15f64 : fetch_word Ubsan.M.loaded_segments (0x16060 : word) = Some W_15f64.
Proof. vm_refl. Qed.
Lemma D_15f64 : decode_any W_15f64 = Some (Load SZ4 true 13 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f68 : bv 32 := 0x0ad65e63.
Lemma F_15f68 : fetch_word Ubsan.M.loaded_segments (0x16064 : word) = Some W_15f68.
Proof. vm_refl. Qed.
Lemma D_15f68 : decode_any W_15f68 = Some (Branch BC_GE 12 13 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f6c : bv 32 := 0x01053683.
Lemma F_15f6c : fetch_word Ubsan.M.loaded_segments (0x16068 : word) = Some W_15f6c.
Proof. vm_refl. Qed.
Lemma D_15f6c : decode_any W_15f6c = Some (Load SZ8 true 13 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f70 : bv 32 := 0x00359513.
Lemma F_15f70 : fetch_word Ubsan.M.loaded_segments (0x1606c : word) = Some W_15f70.
Proof. vm_refl. Qed.
Lemma D_15f70 : decode_any W_15f70 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f74 : bv 32 := 0x00a68533.
Lemma F_15f74 : fetch_word Ubsan.M.loaded_segments (0x16070 : word) = Some W_15f74.
Proof. vm_refl. Qed.
Lemma D_15f74 : decode_any W_15f74 = Some (Op ALU_ADD 10 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f78 : bv 32 := 0x0ed56063.
Lemma F_15f78 : fetch_word Ubsan.M.loaded_segments (0x16074 : word) = Some W_15f78.
Proof. vm_refl. Qed.
Lemma D_15f78 : decode_any W_15f78 = Some (Branch BC_LTU 10 13 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f7c : bv 32 := 0x00d035b3.
Lemma F_15f7c : fetch_word Ubsan.M.loaded_segments (0x16078 : word) = Some W_15f7c.
Proof. vm_refl. Qed.
Lemma D_15f7c : decode_any W_15f7c = Some (Op ALU_SLTU 11 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f80 : bv 32 := 0x00153713.
Lemma F_15f80 : fetch_word Ubsan.M.loaded_segments (0x1607c : word) = Some W_15f80.
Proof. vm_refl. Qed.
Lemma D_15f80 : decode_any W_15f80 = Some (OpImm ALU_SLTU 14 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f84 : bv 32 := 0x00e5c5b3.
Lemma F_15f84 : fetch_word Ubsan.M.loaded_segments (0x16080 : word) = Some W_15f84.
Proof. vm_refl. Qed.
Lemma D_15f84 : decode_any W_15f84 = Some (Op ALU_XOR 11 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f88 : bv 32 := 0x0c058863.
Lemma F_15f88 : fetch_word Ubsan.M.loaded_segments (0x16084 : word) = Some W_15f88.
Proof. vm_refl. Qed.
Lemma D_15f88 : decode_any W_15f88 = Some (Branch BC_EQ 11 0 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f8c : bv 32 := 0x0c068663.
Lemma F_15f8c : fetch_word Ubsan.M.loaded_segments (0x16088 : word) = Some W_15f8c.
Proof. vm_refl. Qed.
Lemma D_15f8c : decode_any W_15f8c = Some (Branch BC_EQ 13 0 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f90 : bv 32 := 0x00757593.
Lemma F_15f90 : fetch_word Ubsan.M.loaded_segments (0x1608c : word) = Some W_15f90.
Proof. vm_refl. Qed.
Lemma D_15f90 : decode_any W_15f90 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f94 : bv 32 := 0x0c059263.
Lemma F_15f94 : fetch_word Ubsan.M.loaded_segments (0x16090 : word) = Some W_15f94.
Proof. vm_refl. Qed.
Lemma D_15f94 : decode_any W_15f94 = Some (Branch BC_NE 11 0 196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f98 : bv 32 := 0x00053503.
Lemma F_15f98 : fetch_word Ubsan.M.loaded_segments (0x16094 : word) = Some W_15f98.
Proof. vm_refl. Qed.
Lemma D_15f98 : decode_any W_15f98 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15f9c : bv 32 := 0x00261593.
Lemma F_15f9c : fetch_word Ubsan.M.loaded_segments (0x16098 : word) = Some W_15f9c.
Proof. vm_refl. Qed.
Lemma D_15f9c : decode_any W_15f9c = Some (ShiftImm ALU_SLL 11 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15fa0 : bv 32 := 0x00b505b3.
Lemma F_15fa0 : fetch_word Ubsan.M.loaded_segments (0x1609c : word) = Some W_15fa0.
Proof. vm_refl. Qed.
Lemma D_15fa0 : decode_any W_15fa0 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15fa4 : bv 32 := 0x0aa5ea63.
Lemma F_15fa4 : fetch_word Ubsan.M.loaded_segments (0x160a0 : word) = Some W_15fa4.
Proof. vm_refl. Qed.
Lemma D_15fa4 : decode_any W_15fa4 = Some (Branch BC_LTU 11 10 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15fa8 : bv 32 := 0x00a03633.
Lemma F_15fa8 : fetch_word Ubsan.M.loaded_segments (0x160a4 : word) = Some W_15fa8.
Proof. vm_refl. Qed.
Lemma D_15fa8 : decode_any W_15fa8 = Some (Op ALU_SLTU 12 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15fac : bv 32 := 0x0015b693.
Lemma F_15fac : fetch_word Ubsan.M.loaded_segments (0x160a8 : word) = Some W_15fac.
Proof. vm_refl. Qed.
Lemma D_15fac : decode_any W_15fac = Some (OpImm ALU_SLTU 13 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15fb0 : bv 32 := 0x00d64633.
Lemma F_15fb0 : fetch_word Ubsan.M.loaded_segments (0x160ac : word) = Some W_15fb0.
Proof. vm_refl. Qed.
Lemma D_15fb0 : decode_any W_15fb0 = Some (Op ALU_XOR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15fb4 : bv 32 := 0x0a060263.
Lemma F_15fb4 : fetch_word Ubsan.M.loaded_segments (0x160b0 : word) = Some W_15fb4.
Proof. vm_refl. Qed.
Lemma D_15fb4 : decode_any W_15fb4 = Some (Branch BC_EQ 12 0 164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15fb8 : bv 32 := 0x0a050063.
Lemma F_15fb8 : fetch_word Ubsan.M.loaded_segments (0x160b4 : word) = Some W_15fb8.
Proof. vm_refl. Qed.
Lemma D_15fb8 : decode_any W_15fb8 = Some (Branch BC_EQ 10 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15fbc : bv 32 := 0x0035f513.
Lemma F_15fbc : fetch_word Ubsan.M.loaded_segments (0x160b8 : word) = Some W_15fbc.
Proof. vm_refl. Qed.
Lemma D_15fbc : decode_any W_15fbc = Some (OpImm ALU_AND 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15fc0 : bv 32 := 0x08051c63.
Lemma F_15fc0 : fetch_word Ubsan.M.loaded_segments (0x160bc : word) = Some W_15fc0.
Proof. vm_refl. Qed.
Lemma D_15fc0 : decode_any W_15fc0 = Some (Branch BC_NE 10 0 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15fc4 : bv 32 := 0x00a5a027.
Lemma F_15fc4 : fetch_word Ubsan.M.loaded_segments (0x160c0 : word) = Some W_15fc4.
Proof. vm_refl. Qed.
Lemma D_15fc4 : decode_any W_15fc4 = Some (FStore FMT_S 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15fc8 : bv 32 := 0x00008067.
Lemma F_15fc8 : fetch_word Ubsan.M.loaded_segments (0x160c4 : word) = Some W_15fc8.
Proof. vm_refl. Qed.
Lemma D_15fc8 : decode_any W_15fc8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ff8 : bv 32 := 0x0000a517.
Lemma F_15ff8 : fetch_word Ubsan.M.loaded_segments (0x160f4 : word) = Some W_15ff8.
Proof. vm_refl. Qed.
Lemma D_15ff8 : decode_any W_15ff8 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ffc : bv 32 := 0x8dc53503.
Lemma F_15ffc : fetch_word Ubsan.M.loaded_segments (0x160f8 : word) = Some W_15ffc.
Proof. vm_refl. Qed.
Lemma D_15ffc : decode_any W_15ffc = Some (Load SZ8 true 10 10 2268, 4%Z).
Proof. vm_refl. Qed.

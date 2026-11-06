(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation USEGS := ImgU.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_a71b8 : bv 32 := 0x0015c783.
Lemma F_a71b8 : fetch_word USEGS (0xa71b8 : word) = Some W_a71b8.
Proof. vm_refl. Qed.
Lemma D_a71b8 : decode_any W_a71b8 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71bc : bv 32 := 0x0025c803.
Lemma F_a71bc : fetch_word USEGS (0xa71bc : word) = Some W_a71bc.
Proof. vm_refl. Qed.
Lemma D_a71bc : decode_any W_a71bc = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71c0 : bv 32 := 0x0035c883.
Lemma F_a71c0 : fetch_word USEGS (0xa71c0 : word) = Some W_a71c0.
Proof. vm_refl. Qed.
Lemma D_a71c0 : decode_any W_a71c0 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71c4 : bv 32 := 0x00458593.
Lemma F_a71c4 : fetch_word USEGS (0xa71c4 : word) = Some W_a71c4.
Proof. vm_refl. Qed.
Lemma D_a71c4 : decode_any W_a71c4 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71c8 : bv 32 := 0x00468293.
Lemma F_a71c8 : fetch_word USEGS (0xa71c8 : word) = Some W_a71c8.
Proof. vm_refl. Qed.
Lemma D_a71c8 : decode_any W_a71c8 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71cc : bv 32 := 0x00e68023.
Lemma F_a71cc : fetch_word USEGS (0xa71cc : word) = Some W_a71cc.
Proof. vm_refl. Qed.
Lemma D_a71cc : decode_any W_a71cc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71d0 : bv 32 := 0x00f680a3.
Lemma F_a71d0 : fetch_word USEGS (0xa71d0 : word) = Some W_a71d0.
Proof. vm_refl. Qed.
Lemma D_a71d0 : decode_any W_a71d0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71d4 : bv 32 := 0x01068123.
Lemma F_a71d4 : fetch_word USEGS (0xa71d4 : word) = Some W_a71d4.
Proof. vm_refl. Qed.
Lemma D_a71d4 : decode_any W_a71d4 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71d8 : bv 32 := 0x011681a3.
Lemma F_a71d8 : fetch_word USEGS (0xa71d8 : word) = Some W_a71d8.
Proof. vm_refl. Qed.
Lemma D_a71d8 : decode_any W_a71d8 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71dc : bv 32 := 0x00028693.
Lemma F_a71dc : fetch_word USEGS (0xa71dc : word) = Some W_a71dc.
Proof. vm_refl. Qed.
Lemma D_a71dc : decode_any W_a71dc = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71e0 : bv 32 := 0x00267713.
Lemma F_a71e0 : fetch_word USEGS (0xa71e0 : word) = Some W_a71e0.
Proof. vm_refl. Qed.
Lemma D_a71e0 : decode_any W_a71e0 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71e4 : bv 32 := 0x00071863.
Lemma F_a71e4 : fetch_word USEGS (0xa71e4 : word) = Some W_a71e4.
Proof. vm_refl. Qed.
Lemma D_a71e4 : decode_any W_a71e4 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71e8 : bv 32 := 0x00167613.
Lemma F_a71e8 : fetch_word USEGS (0xa71e8 : word) = Some W_a71e8.
Proof. vm_refl. Qed.
Lemma D_a71e8 : decode_any W_a71e8 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71ec : bv 32 := 0x02061663.
Lemma F_a71ec : fetch_word USEGS (0xa71ec : word) = Some W_a71ec.
Proof. vm_refl. Qed.
Lemma D_a71ec : decode_any W_a71ec = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71f0 : bv 32 := 0x00008067.
Lemma F_a71f0 : fetch_word USEGS (0xa71f0 : word) = Some W_a71f0.
Proof. vm_refl. Qed.
Lemma D_a71f0 : decode_any W_a71f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71f4 : bv 32 := 0x0005c703.
Lemma F_a71f4 : fetch_word USEGS (0xa71f4 : word) = Some W_a71f4.
Proof. vm_refl. Qed.
Lemma D_a71f4 : decode_any W_a71f4 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71f8 : bv 32 := 0x0015c783.
Lemma F_a71f8 : fetch_word USEGS (0xa71f8 : word) = Some W_a71f8.
Proof. vm_refl. Qed.
Lemma D_a71f8 : decode_any W_a71f8 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71fc : bv 32 := 0x00258593.
Lemma F_a71fc : fetch_word USEGS (0xa71fc : word) = Some W_a71fc.
Proof. vm_refl. Qed.
Lemma D_a71fc : decode_any W_a71fc = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7200 : bv 32 := 0x00268813.
Lemma F_a7200 : fetch_word USEGS (0xa7200 : word) = Some W_a7200.
Proof. vm_refl. Qed.
Lemma D_a7200 : decode_any W_a7200 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7204 : bv 32 := 0x00e68023.
Lemma F_a7204 : fetch_word USEGS (0xa7204 : word) = Some W_a7204.
Proof. vm_refl. Qed.
Lemma D_a7204 : decode_any W_a7204 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7208 : bv 32 := 0x00f680a3.
Lemma F_a7208 : fetch_word USEGS (0xa7208 : word) = Some W_a7208.
Proof. vm_refl. Qed.
Lemma D_a7208 : decode_any W_a7208 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a720c : bv 32 := 0x00080693.
Lemma F_a720c : fetch_word USEGS (0xa720c : word) = Some W_a720c.
Proof. vm_refl. Qed.
Lemma D_a720c : decode_any W_a720c = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7210 : bv 32 := 0x00167613.
Lemma F_a7210 : fetch_word USEGS (0xa7210 : word) = Some W_a7210.
Proof. vm_refl. Qed.
Lemma D_a7210 : decode_any W_a7210 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7214 : bv 32 := 0xfc060ee3.
Lemma F_a7214 : fetch_word USEGS (0xa7214 : word) = Some W_a7214.
Proof. vm_refl. Qed.
Lemma D_a7214 : decode_any W_a7214 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7218 : bv 32 := 0x0005c583.
Lemma F_a7218 : fetch_word USEGS (0xa7218 : word) = Some W_a7218.
Proof. vm_refl. Qed.
Lemma D_a7218 : decode_any W_a7218 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a721c : bv 32 := 0x00b68023.
Lemma F_a721c : fetch_word USEGS (0xa721c : word) = Some W_a721c.
Proof. vm_refl. Qed.
Lemma D_a721c : decode_any W_a721c = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7220 : bv 32 := 0x00008067.
Lemma F_a7220 : fetch_word USEGS (0xa7220 : word) = Some W_a7220.
Proof. vm_refl. Qed.
Lemma D_a7220 : decode_any W_a7220 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7320 : bv 32 := 0x0077f813.
Lemma F_a7320 : fetch_word USEGS (0xa7320 : word) = Some W_a7320.
Proof. vm_refl. Qed.
Lemma D_a7320 : decode_any W_a7320 = Some (OpImm ALU_AND 16 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7324 : bv 32 := 0x00168693.
Lemma F_a7324 : fetch_word USEGS (0xa7324 : word) = Some W_a7324.
Proof. vm_refl. Qed.
Lemma D_a7324 : decode_any W_a7324 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7328 : bv 32 := 0xfff78793.
Lemma F_a7328 : fetch_word USEGS (0xa7328 : word) = Some W_a7328.
Proof. vm_refl. Qed.
Lemma D_a7328 : decode_any W_a7328 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73a0 : bv 32 := 0x0e060a63.
Lemma F_a73a0 : fetch_word USEGS (0xa73a0 : word) = Some W_a73a0.
Proof. vm_refl. Qed.
Lemma D_a73a0 : decode_any W_a73a0 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73a4 : bv 32 := 0x00b50023.
Lemma F_a73a4 : fetch_word USEGS (0xa73a4 : word) = Some W_a73a4.
Proof. vm_refl. Qed.
Lemma D_a73a4 : decode_any W_a73a4 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73a8 : bv 32 := 0x00c506b3.
Lemma F_a73a8 : fetch_word USEGS (0xa73a8 : word) = Some W_a73a8.
Proof. vm_refl. Qed.
Lemma D_a73a8 : decode_any W_a73a8 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73ac : bv 32 := 0x00300713.
Lemma F_a73ac : fetch_word USEGS (0xa73ac : word) = Some W_a73ac.
Proof. vm_refl. Qed.
Lemma D_a73ac : decode_any W_a73ac = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73b0 : bv 32 := 0xfeb68fa3.
Lemma F_a73b0 : fetch_word USEGS (0xa73b0 : word) = Some W_a73b0.
Proof. vm_refl. Qed.
Lemma D_a73b0 : decode_any W_a73b0 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73b4 : bv 32 := 0x0ee66063.
Lemma F_a73b4 : fetch_word USEGS (0xa73b4 : word) = Some W_a73b4.
Proof. vm_refl. Qed.
Lemma D_a73b4 : decode_any W_a73b4 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73b8 : bv 32 := 0x00b500a3.
Lemma F_a73b8 : fetch_word USEGS (0xa73b8 : word) = Some W_a73b8.
Proof. vm_refl. Qed.
Lemma D_a73b8 : decode_any W_a73b8 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73bc : bv 32 := 0x00b50123.
Lemma F_a73bc : fetch_word USEGS (0xa73bc : word) = Some W_a73bc.
Proof. vm_refl. Qed.
Lemma D_a73bc : decode_any W_a73bc = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73c0 : bv 32 := 0x00700713.
Lemma F_a73c0 : fetch_word USEGS (0xa73c0 : word) = Some W_a73c0.
Proof. vm_refl. Qed.
Lemma D_a73c0 : decode_any W_a73c0 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73c4 : bv 32 := 0xfeb68ea3.
Lemma F_a73c4 : fetch_word USEGS (0xa73c4 : word) = Some W_a73c4.
Proof. vm_refl. Qed.
Lemma D_a73c4 : decode_any W_a73c4 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73c8 : bv 32 := 0xfeb68f23.
Lemma F_a73c8 : fetch_word USEGS (0xa73c8 : word) = Some W_a73c8.
Proof. vm_refl. Qed.
Lemma D_a73c8 : decode_any W_a73c8 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73cc : bv 32 := 0x0ce66463.
Lemma F_a73cc : fetch_word USEGS (0xa73cc : word) = Some W_a73cc.
Proof. vm_refl. Qed.
Lemma D_a73cc : decode_any W_a73cc = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73d0 : bv 32 := 0x00b501a3.
Lemma F_a73d0 : fetch_word USEGS (0xa73d0 : word) = Some W_a73d0.
Proof. vm_refl. Qed.
Lemma D_a73d0 : decode_any W_a73d0 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73d4 : bv 32 := 0x00900793.
Lemma F_a73d4 : fetch_word USEGS (0xa73d4 : word) = Some W_a73d4.
Proof. vm_refl. Qed.
Lemma D_a73d4 : decode_any W_a73d4 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73d8 : bv 32 := 0xfeb68e23.
Lemma F_a73d8 : fetch_word USEGS (0xa73d8 : word) = Some W_a73d8.
Proof. vm_refl. Qed.
Lemma D_a73d8 : decode_any W_a73d8 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73dc : bv 32 := 0x0af66c63.
Lemma F_a73dc : fetch_word USEGS (0xa73dc : word) = Some W_a73dc.
Proof. vm_refl. Qed.
Lemma D_a73dc : decode_any W_a73dc = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73e0 : bv 32 := 0x40a006bb.
Lemma F_a73e0 : fetch_word USEGS (0xa73e0 : word) = Some W_a73e0.
Proof. vm_refl. Qed.
Lemma D_a73e0 : decode_any W_a73e0 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73e4 : bv 32 := 0x03859813.
Lemma F_a73e4 : fetch_word USEGS (0xa73e4 : word) = Some W_a73e4.
Proof. vm_refl. Qed.
Lemma D_a73e4 : decode_any W_a73e4 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73e8 : bv 32 := 0x101015b7.
Lemma F_a73e8 : fetch_word USEGS (0xa73e8 : word) = Some W_a73e8.
Proof. vm_refl. Qed.
Lemma D_a73e8 : decode_any W_a73e8 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73ec : bv 32 := 0x0036f693.
Lemma F_a73ec : fetch_word USEGS (0xa73ec : word) = Some W_a73ec.
Proof. vm_refl. Qed.
Lemma D_a73ec : decode_any W_a73ec = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73f0 : bv 32 := 0x00459713.
Lemma F_a73f0 : fetch_word USEGS (0xa73f0 : word) = Some W_a73f0.
Proof. vm_refl. Qed.
Lemma D_a73f0 : decode_any W_a73f0 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73f4 : bv 32 := 0x40d60633.
Lemma F_a73f4 : fetch_word USEGS (0xa73f4 : word) = Some W_a73f4.
Proof. vm_refl. Qed.
Lemma D_a73f4 : decode_any W_a73f4 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73f8 : bv 32 := 0x00d505b3.
Lemma F_a73f8 : fetch_word USEGS (0xa73f8 : word) = Some W_a73f8.
Proof. vm_refl. Qed.
Lemma D_a73f8 : decode_any W_a73f8 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73fc : bv 32 := 0x10070693.
Lemma F_a73fc : fetch_word USEGS (0xa73fc : word) = Some W_a73fc.
Proof. vm_refl. Qed.
Lemma D_a73fc : decode_any W_a73fc = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7400 : bv 32 := 0xffc67713.
Lemma F_a7400 : fetch_word USEGS (0xa7400 : word) = Some W_a7400.
Proof. vm_refl. Qed.
Lemma D_a7400 : decode_any W_a7400 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7404 : bv 32 := 0x02d83633.
Lemma F_a7404 : fetch_word USEGS (0xa7404 : word) = Some W_a7404.
Proof. vm_refl. Qed.
Lemma D_a7404 : decode_any W_a7404 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7408 : bv 32 := 0x00c5a023.
Lemma F_a7408 : fetch_word USEGS (0xa7408 : word) = Some W_a7408.
Proof. vm_refl. Qed.
Lemma D_a7408 : decode_any W_a7408 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a740c : bv 32 := 0x00e586b3.
Lemma F_a740c : fetch_word USEGS (0xa740c : word) = Some W_a740c.
Proof. vm_refl. Qed.
Lemma D_a740c : decode_any W_a740c = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7410 : bv 32 := 0xfec6ae23.
Lemma F_a7410 : fetch_word USEGS (0xa7410 : word) = Some W_a7410.
Proof. vm_refl. Qed.
Lemma D_a7410 : decode_any W_a7410 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7414 : bv 32 := 0x08f76063.
Lemma F_a7414 : fetch_word USEGS (0xa7414 : word) = Some W_a7414.
Proof. vm_refl. Qed.
Lemma D_a7414 : decode_any W_a7414 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7418 : bv 32 := 0x00c5a223.
Lemma F_a7418 : fetch_word USEGS (0xa7418 : word) = Some W_a7418.
Proof. vm_refl. Qed.
Lemma D_a7418 : decode_any W_a7418 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a741c : bv 32 := 0x00c5a423.
Lemma F_a741c : fetch_word USEGS (0xa741c : word) = Some W_a741c.
Proof. vm_refl. Qed.
Lemma D_a741c : decode_any W_a741c = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7420 : bv 32 := 0x01900793.
Lemma F_a7420 : fetch_word USEGS (0xa7420 : word) = Some W_a7420.
Proof. vm_refl. Qed.
Lemma D_a7420 : decode_any W_a7420 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7424 : bv 32 := 0xfec6aa23.
Lemma F_a7424 : fetch_word USEGS (0xa7424 : word) = Some W_a7424.
Proof. vm_refl. Qed.
Lemma D_a7424 : decode_any W_a7424 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7428 : bv 32 := 0xfec6ac23.
Lemma F_a7428 : fetch_word USEGS (0xa7428 : word) = Some W_a7428.
Proof. vm_refl. Qed.
Lemma D_a7428 : decode_any W_a7428 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a742c : bv 32 := 0x06f76463.
Lemma F_a742c : fetch_word USEGS (0xa742c : word) = Some W_a742c.
Proof. vm_refl. Qed.
Lemma D_a742c : decode_any W_a742c = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7430 : bv 32 := 0x00c5a623.
Lemma F_a7430 : fetch_word USEGS (0xa7430 : word) = Some W_a7430.
Proof. vm_refl. Qed.
Lemma D_a7430 : decode_any W_a7430 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7434 : bv 32 := 0x00c5a823.
Lemma F_a7434 : fetch_word USEGS (0xa7434 : word) = Some W_a7434.
Proof. vm_refl. Qed.
Lemma D_a7434 : decode_any W_a7434 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7438 : bv 32 := 0x00c5aa23.
Lemma F_a7438 : fetch_word USEGS (0xa7438 : word) = Some W_a7438.
Proof. vm_refl. Qed.
Lemma D_a7438 : decode_any W_a7438 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a743c : bv 32 := 0x00c5ac23.
Lemma F_a743c : fetch_word USEGS (0xa743c : word) = Some W_a743c.
Proof. vm_refl. Qed.
Lemma D_a743c : decode_any W_a743c = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7440 : bv 32 := 0x0045f793.
Lemma F_a7440 : fetch_word USEGS (0xa7440 : word) = Some W_a7440.
Proof. vm_refl. Qed.
Lemma D_a7440 : decode_any W_a7440 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7444 : bv 32 := 0x02000813.
Lemma F_a7444 : fetch_word USEGS (0xa7444 : word) = Some W_a7444.
Proof. vm_refl. Qed.
Lemma D_a7444 : decode_any W_a7444 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7448 : bv 32 := 0x01878793.
Lemma F_a7448 : fetch_word USEGS (0xa7448 : word) = Some W_a7448.
Proof. vm_refl. Qed.
Lemma D_a7448 : decode_any W_a7448 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a744c : bv 32 := 0x40f70733.
Lemma F_a744c : fetch_word USEGS (0xa744c : word) = Some W_a744c.
Proof. vm_refl. Qed.
Lemma D_a744c : decode_any W_a744c = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7450 : bv 32 := 0xfec6a223.
Lemma F_a7450 : fetch_word USEGS (0xa7450 : word) = Some W_a7450.
Proof. vm_refl. Qed.
Lemma D_a7450 : decode_any W_a7450 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7454 : bv 32 := 0xfec6a423.
Lemma F_a7454 : fetch_word USEGS (0xa7454 : word) = Some W_a7454.
Proof. vm_refl. Qed.
Lemma D_a7454 : decode_any W_a7454 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7458 : bv 32 := 0xfec6a623.
Lemma F_a7458 : fetch_word USEGS (0xa7458 : word) = Some W_a7458.
Proof. vm_refl. Qed.
Lemma D_a7458 : decode_any W_a7458 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a745c : bv 32 := 0xfec6a823.
Lemma F_a745c : fetch_word USEGS (0xa745c : word) = Some W_a745c.
Proof. vm_refl. Qed.
Lemma D_a745c : decode_any W_a745c = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7460 : bv 32 := 0x03076a63.
Lemma F_a7460 : fetch_word USEGS (0xa7460 : word) = Some W_a7460.
Proof. vm_refl. Qed.
Lemma D_a7460 : decode_any W_a7460 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7464 : bv 32 := 0x02061613.
Lemma F_a7464 : fetch_word USEGS (0xa7464 : word) = Some W_a7464.
Proof. vm_refl. Qed.
Lemma D_a7464 : decode_any W_a7464 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7468 : bv 32 := 0x00f585b3.
Lemma F_a7468 : fetch_word USEGS (0xa7468 : word) = Some W_a7468.
Proof. vm_refl. Qed.
Lemma D_a7468 : decode_any W_a7468 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a746c : bv 32 := 0x02065693.
Lemma F_a746c : fetch_word USEGS (0xa746c : word) = Some W_a746c.
Proof. vm_refl. Qed.
Lemma D_a746c : decode_any W_a746c = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7470 : bv 32 := 0x00d66633.
Lemma F_a7470 : fetch_word USEGS (0xa7470 : word) = Some W_a7470.
Proof. vm_refl. Qed.
Lemma D_a7470 : decode_any W_a7470 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7474 : bv 32 := 0x01f00693.
Lemma F_a7474 : fetch_word USEGS (0xa7474 : word) = Some W_a7474.
Proof. vm_refl. Qed.
Lemma D_a7474 : decode_any W_a7474 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7478 : bv 32 := 0x00c5b023.
Lemma F_a7478 : fetch_word USEGS (0xa7478 : word) = Some W_a7478.
Proof. vm_refl. Qed.
Lemma D_a7478 : decode_any W_a7478 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a747c : bv 32 := 0x00c5b423.
Lemma F_a747c : fetch_word USEGS (0xa747c : word) = Some W_a747c.
Proof. vm_refl. Qed.
Lemma D_a747c : decode_any W_a747c = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7480 : bv 32 := 0x00c5b823.
Lemma F_a7480 : fetch_word USEGS (0xa7480 : word) = Some W_a7480.
Proof. vm_refl. Qed.
Lemma D_a7480 : decode_any W_a7480 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7484 : bv 32 := 0x00c5bc23.
Lemma F_a7484 : fetch_word USEGS (0xa7484 : word) = Some W_a7484.
Proof. vm_refl. Qed.
Lemma D_a7484 : decode_any W_a7484 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7488 : bv 32 := 0xfe070713.
Lemma F_a7488 : fetch_word USEGS (0xa7488 : word) = Some W_a7488.
Proof. vm_refl. Qed.
Lemma D_a7488 : decode_any W_a7488 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a748c : bv 32 := 0x02058593.
Lemma F_a748c : fetch_word USEGS (0xa748c : word) = Some W_a748c.
Proof. vm_refl. Qed.
Lemma D_a748c : decode_any W_a748c = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7490 : bv 32 := 0xfee6e4e3.
Lemma F_a7490 : fetch_word USEGS (0xa7490 : word) = Some W_a7490.
Proof. vm_refl. Qed.
Lemma D_a7490 : decode_any W_a7490 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7494 : bv 32 := 0x00008067.
Lemma F_a7494 : fetch_word USEGS (0xa7494 : word) = Some W_a7494.
Proof. vm_refl. Qed.
Lemma D_a7494 : decode_any W_a7494 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7518 : bv 32 := 0x00053703.
Lemma F_a7518 : fetch_word USEGS (0xa7518 : word) = Some W_a7518.
Proof. vm_refl. Qed.
Lemma D_a7518 : decode_any W_a7518 = Some (Load SZ8 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a75a8 : bv 32 := 0x00013403.
Lemma F_a75a8 : fetch_word USEGS (0xa75a8 : word) = Some W_a75a8.
Proof. vm_refl. Qed.
Lemma D_a75a8 : decode_any W_a75a8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a75ac : bv 32 := 0x01010113.
Lemma F_a75ac : fetch_word USEGS (0xa75ac : word) = Some W_a75ac.
Proof. vm_refl. Qed.
Lemma D_a75ac : decode_any W_a75ac = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a75b0 : bv 32 := 0x00008067.
Lemma F_a75b0 : fetch_word USEGS (0xa75b0 : word) = Some W_a75b0.
Proof. vm_refl. Qed.
Lemma D_a75b0 : decode_any W_a75b0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a761c : bv 32 := 0x00060a63.
Lemma F_a761c : fetch_word USEGS (0xa761c : word) = Some W_a761c.
Proof. vm_refl. Qed.
Lemma D_a761c : decode_any W_a761c = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7620 : bv 32 := 0x0005c603.
Lemma F_a7620 : fetch_word USEGS (0xa7620 : word) = Some W_a7620.
Proof. vm_refl. Qed.
Lemma D_a7620 : decode_any W_a7620 = Some (Load SZ1 false 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7624 : bv 32 := 0x00c50023.
Lemma F_a7624 : fetch_word USEGS (0xa7624 : word) = Some W_a7624.
Proof. vm_refl. Qed.
Lemma D_a7624 : decode_any W_a7624 = Some (Store SZ1 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7628 : bv 32 := 0x08061263.
Lemma F_a7628 : fetch_word USEGS (0xa7628 : word) = Some W_a7628.
Proof. vm_refl. Qed.
Lemma D_a7628 : decode_any W_a7628 = Some (Branch BC_NE 12 0 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a762c : bv 32 := 0x0a40006f.
Lemma F_a762c : fetch_word USEGS (0xa762c : word) = Some W_a762c.
Proof. vm_refl. Qed.
Lemma D_a762c : decode_any W_a762c = Some (Jal 0 164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7630 : bv 32 := 0x0075f613.
Lemma F_a7630 : fetch_word USEGS (0xa7630 : word) = Some W_a7630.
Proof. vm_refl. Qed.
Lemma D_a7630 : decode_any W_a7630 = Some (OpImm ALU_AND 12 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7634 : bv 32 := 0x02060463.
Lemma F_a7634 : fetch_word USEGS (0xa7634 : word) = Some W_a7634.
Proof. vm_refl. Qed.
Lemma D_a7634 : decode_any W_a7634 = Some (Branch BC_EQ 12 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7638 : bv 32 := 0x00158613.
Lemma F_a7638 : fetch_word USEGS (0xa7638 : word) = Some W_a7638.
Proof. vm_refl. Qed.
Lemma D_a7638 : decode_any W_a7638 = Some (OpImm ALU_ADD 12 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a763c : bv 32 := 0x0005c683.
Lemma F_a763c : fetch_word USEGS (0xa763c : word) = Some W_a763c.
Proof. vm_refl. Qed.
Lemma D_a763c : decode_any W_a763c = Some (Load SZ1 false 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7640 : bv 32 := 0x00d50023.
Lemma F_a7640 : fetch_word USEGS (0xa7640 : word) = Some W_a7640.
Proof. vm_refl. Qed.
Lemma D_a7640 : decode_any W_a7640 = Some (Store SZ1 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a787c : bv 32 := 0xfe010113.
Lemma F_a787c : fetch_word USEGS (0xa787c : word) = Some W_a787c.
Proof. vm_refl. Qed.
Lemma D_a787c : decode_any W_a787c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7880 : bv 32 := 0x00113c23.
Lemma F_a7880 : fetch_word USEGS (0xa7880 : word) = Some W_a7880.
Proof. vm_refl. Qed.
Lemma D_a7880 : decode_any W_a7880 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7884 : bv 32 := 0x00813823.
Lemma F_a7884 : fetch_word USEGS (0xa7884 : word) = Some W_a7884.
Proof. vm_refl. Qed.
Lemma D_a7884 : decode_any W_a7884 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7888 : bv 32 := 0x00913423.
Lemma F_a7888 : fetch_word USEGS (0xa7888 : word) = Some W_a7888.
Proof. vm_refl. Qed.
Lemma D_a7888 : decode_any W_a7888 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a788c : bv 32 := 0x00058413.
Lemma F_a788c : fetch_word USEGS (0xa788c : word) = Some W_a788c.
Proof. vm_refl. Qed.
Lemma D_a788c : decode_any W_a788c = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7890 : bv 32 := 0x00050493.
Lemma F_a7890 : fetch_word USEGS (0xa7890 : word) = Some W_a7890.
Proof. vm_refl. Qed.
Lemma D_a7890 : decode_any W_a7890 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7894 : bv 32 := 0x00000593.
Lemma F_a7894 : fetch_word USEGS (0xa7894 : word) = Some W_a7894.
Proof. vm_refl. Qed.
Lemma D_a7894 : decode_any W_a7894 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7898 : bv 32 := 0x00040613.
Lemma F_a7898 : fetch_word USEGS (0xa7898 : word) = Some W_a7898.
Proof. vm_refl. Qed.
Lemma D_a7898 : decode_any W_a7898 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a789c : bv 32 := 0xc88ff0ef.
Lemma F_a789c : fetch_word USEGS (0xa789c : word) = Some W_a789c.
Proof. vm_refl. Qed.
Lemma D_a789c : decode_any W_a789c = Some (Jal 1 2094216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a78a0 : bv 32 := 0x00050463.
Lemma F_a78a0 : fetch_word USEGS (0xa78a0 : word) = Some W_a78a0.
Proof. vm_refl. Qed.
Lemma D_a78a0 : decode_any W_a78a0 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a78a4 : bv 32 := 0x40950433.
Lemma F_a78a4 : fetch_word USEGS (0xa78a4 : word) = Some W_a78a4.
Proof. vm_refl. Qed.
Lemma D_a78a4 : decode_any W_a78a4 = Some (Op ALU_SUB 8 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a78a8 : bv 32 := 0x00040513.
Lemma F_a78a8 : fetch_word USEGS (0xa78a8 : word) = Some W_a78a8.
Proof. vm_refl. Qed.
Lemma D_a78a8 : decode_any W_a78a8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a78ac : bv 32 := 0x01813083.
Lemma F_a78ac : fetch_word USEGS (0xa78ac : word) = Some W_a78ac.
Proof. vm_refl. Qed.
Lemma D_a78ac : decode_any W_a78ac = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a78b0 : bv 32 := 0x01013403.
Lemma F_a78b0 : fetch_word USEGS (0xa78b0 : word) = Some W_a78b0.
Proof. vm_refl. Qed.
Lemma D_a78b0 : decode_any W_a78b0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a78b4 : bv 32 := 0x00813483.
Lemma F_a78b4 : fetch_word USEGS (0xa78b4 : word) = Some W_a78b4.
Proof. vm_refl. Qed.
Lemma D_a78b4 : decode_any W_a78b4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a78b8 : bv 32 := 0x02010113.
Lemma F_a78b8 : fetch_word USEGS (0xa78b8 : word) = Some W_a78b8.
Proof. vm_refl. Qed.
Lemma D_a78b8 : decode_any W_a78b8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a78bc : bv 32 := 0x00008067.
Lemma F_a78bc : fetch_word USEGS (0xa78bc : word) = Some W_a78bc.
Proof. vm_refl. Qed.
Lemma D_a78bc : decode_any W_a78bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7a18 : bv 32 := 0x0003e597.
Lemma F_a7a18 : fetch_word USEGS (0xa7a18 : word) = Some W_a7a18.
Proof. vm_refl. Qed.
Lemma D_a7a18 : decode_any W_a7a18 = Some (Auipc 11 62, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7a1c : bv 32 := 0x89358683.
Lemma F_a7a1c : fetch_word USEGS (0xa7a1c : word) = Some W_a7a1c.
Proof. vm_refl. Qed.
Lemma D_a7a1c : decode_any W_a7a1c = Some (Load SZ1 true 13 11 2195, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7a20 : bv 32 := 0x1e068863.
Lemma F_a7a20 : fetch_word USEGS (0xa7a20 : word) = Some W_a7a20.
Proof. vm_refl. Qed.
Lemma D_a7a20 : decode_any W_a7a20 = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7c10 : bv 32 := 0x00008067.
Lemma F_a7c10 : fetch_word USEGS (0xa7c10 : word) = Some W_a7c10.
Proof. vm_refl. Qed.
Lemma D_a7c10 : decode_any W_a7c10 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7ca0 : bv 32 := 0x00052583.
Lemma F_a7ca0 : fetch_word USEGS (0xa7ca0 : word) = Some W_a7ca0.
Proof. vm_refl. Qed.
Lemma D_a7ca0 : decode_any W_a7ca0 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7ca4 : bv 32 := 0x0005c463.
Lemma F_a7ca4 : fetch_word USEGS (0xa7ca4 : word) = Some W_a7ca4.
Proof. vm_refl. Qed.
Lemma D_a7ca4 : decode_any W_a7ca4 = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7ca8 : bv 32 := 0x00008067.
Lemma F_a7ca8 : fetch_word USEGS (0xa7ca8 : word) = Some W_a7ca8.
Proof. vm_refl. Qed.
Lemma D_a7ca8 : decode_any W_a7ca8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7d14 : bv 32 := 0x00050893.
Lemma F_a7d14 : fetch_word USEGS (0xa7d14 : word) = Some W_a7d14.
Proof. vm_refl. Qed.
Lemma D_a7d14 : decode_any W_a7d14 = Some (OpImm ALU_ADD 17 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7d18 : bv 32 := 0x00058513.
Lemma F_a7d18 : fetch_word USEGS (0xa7d18 : word) = Some W_a7d18.
Proof. vm_refl. Qed.
Lemma D_a7d18 : decode_any W_a7d18 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7d1c : bv 32 := 0x00060593.
Lemma F_a7d1c : fetch_word USEGS (0xa7d1c : word) = Some W_a7d1c.
Proof. vm_refl. Qed.
Lemma D_a7d1c : decode_any W_a7d1c = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7d20 : bv 32 := 0x00068613.
Lemma F_a7d20 : fetch_word USEGS (0xa7d20 : word) = Some W_a7d20.
Proof. vm_refl. Qed.
Lemma D_a7d20 : decode_any W_a7d20 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7d24 : bv 32 := 0x00070693.
Lemma F_a7d24 : fetch_word USEGS (0xa7d24 : word) = Some W_a7d24.
Proof. vm_refl. Qed.
Lemma D_a7d24 : decode_any W_a7d24 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7d28 : bv 32 := 0x00078713.
Lemma F_a7d28 : fetch_word USEGS (0xa7d28 : word) = Some W_a7d28.
Proof. vm_refl. Qed.
Lemma D_a7d28 : decode_any W_a7d28 = Some (OpImm ALU_ADD 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7d2c : bv 32 := 0x00080793.
Lemma F_a7d2c : fetch_word USEGS (0xa7d2c : word) = Some W_a7d2c.
Proof. vm_refl. Qed.
Lemma D_a7d2c : decode_any W_a7d2c = Some (OpImm ALU_ADD 15 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7d30 : bv 32 := 0x00000073.
Lemma F_a7d30 : fetch_word USEGS (0xa7d30 : word) = Some W_a7d30.
Proof. vm_refl. Qed.
Lemma D_a7d30 : decode_any W_a7d30 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_a7d30 : is_ecall W_a7d30 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_a7d34 : bv 32 := 0x00008067.
Lemma F_a7d34 : fetch_word USEGS (0xa7d34 : word) = Some W_a7d34.
Proof. vm_refl. Qed.
Lemma D_a7d34 : decode_any W_a7d34 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7d38 : bv 32 := 0xfddff06f.
Lemma F_a7d38 : fetch_word USEGS (0xa7d38 : word) = Some W_a7d38.
Proof. vm_refl. Qed.
Lemma D_a7d38 : decode_any W_a7d38 = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.


(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6c5d8 : bv 32 := 0x060a0063.
Lemma F_6c5d8 : fetch_word AsanUbsan.M.loaded_segments (0x6c620 : word) = Some W_6c5d8.
Proof. vm_refl. Qed.
Lemma D_6c5d8 : decode_any W_6c5d8 = Some (Branch BC_EQ 20 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c5dc : bv 32 := 0x0a051c63.
Lemma F_6c5dc : fetch_word AsanUbsan.M.loaded_segments (0x6c624 : word) = Some W_6c5dc.
Proof. vm_refl. Qed.
Lemma D_6c5dc : decode_any W_6c5dc = Some (Branch BC_NE 10 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c5f0 : bv 32 := 0xfbf48593.
Lemma F_6c5f0 : fetch_word AsanUbsan.M.loaded_segments (0x6c638 : word) = Some W_6c5f0.
Proof. vm_refl. Qed.
Lemma D_6c5f0 : decode_any W_6c5f0 = Some (OpImm ALU_ADD 11 9 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c5f4 : bv 32 := 0xfbf00613.
Lemma F_6c5f4 : fetch_word AsanUbsan.M.loaded_segments (0x6c63c : word) = Some W_6c5f4.
Proof. vm_refl. Qed.
Lemma D_6c5f4 : decode_any W_6c5f4 = Some (OpImm ALU_ADD 12 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c5f8 : bv 32 := 0x12b67663.
Lemma F_6c5f8 : fetch_word AsanUbsan.M.loaded_segments (0x6c640 : word) = Some W_6c5f8.
Proof. vm_refl. Qed.
Lemma D_6c5f8 : decode_any W_6c5f8 = Some (Branch BC_GEU 12 11 300, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c5fc : bv 32 := 0x000e8597.
Lemma F_6c5fc : fetch_word AsanUbsan.M.loaded_segments (0x6c644 : word) = Some W_6c5fc.
Proof. vm_refl. Qed.
Lemma D_6c5fc : decode_any W_6c5fc = Some (Auipc 11 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c600 : bv 32 := 0xebc5b583.
Lemma F_6c600 : fetch_word AsanUbsan.M.loaded_segments (0x6c648 : word) = Some W_6c600.
Proof. vm_refl. Qed.
Lemma D_6c600 : decode_any W_6c600 = Some (Load SZ8 true 11 11 3772, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c604 : bv 32 := 0x009906b3.
Lemma F_6c604 : fetch_word AsanUbsan.M.loaded_segments (0x6c64c : word) = Some W_6c604.
Proof. vm_refl. Qed.
Lemma D_6c604 : decode_any W_6c604 = Some (Op ALU_ADD 13 18 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c608 : bv 32 := 0x0005b603.
Lemma F_6c608 : fetch_word AsanUbsan.M.loaded_segments (0x6c650 : word) = Some W_6c608.
Proof. vm_refl. Qed.
Lemma D_6c608 : decode_any W_6c608 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c60c : bv 32 := 0x00395593.
Lemma F_6c60c : fetch_word AsanUbsan.M.loaded_segments (0x6c654 : word) = Some W_6c60c.
Proof. vm_refl. Qed.
Lemma D_6c60c : decode_any W_6c60c = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c610 : bv 32 := 0xfff68693.
Lemma F_6c610 : fetch_word AsanUbsan.M.loaded_segments (0x6c658 : word) = Some W_6c610.
Proof. vm_refl. Qed.
Lemma D_6c610 : decode_any W_6c610 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c614 : bv 32 := 0x0036d713.
Lemma F_6c614 : fetch_word AsanUbsan.M.loaded_segments (0x6c65c : word) = Some W_6c614.
Proof. vm_refl. Qed.
Lemma D_6c614 : decode_any W_6c614 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c618 : bv 32 := 0x00b605b3.
Lemma F_6c618 : fetch_word AsanUbsan.M.loaded_segments (0x6c660 : word) = Some W_6c618.
Proof. vm_refl. Qed.
Lemma D_6c618 : decode_any W_6c618 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c61c : bv 32 := 0x00e60633.
Lemma F_6c61c : fetch_word AsanUbsan.M.loaded_segments (0x6c664 : word) = Some W_6c61c.
Proof. vm_refl. Qed.
Lemma D_6c61c : decode_any W_6c61c = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c620 : bv 32 := 0xff85f713.
Lemma F_6c620 : fetch_word AsanUbsan.M.loaded_segments (0x6c668 : word) = Some W_6c620.
Proof. vm_refl. Qed.
Lemma D_6c620 : decode_any W_6c620 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c624 : bv 32 := 0xff867793.
Lemma F_6c624 : fetch_word AsanUbsan.M.loaded_segments (0x6c66c : word) = Some W_6c624.
Proof. vm_refl. Qed.
Lemma D_6c624 : decode_any W_6c624 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c628 : bv 32 := 0x00073703.
Lemma F_6c628 : fetch_word AsanUbsan.M.loaded_segments (0x6c670 : word) = Some W_6c628.
Proof. vm_refl. Qed.
Lemma D_6c628 : decode_any W_6c628 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c62c : bv 32 := 0x0007b783.
Lemma F_6c62c : fetch_word AsanUbsan.M.loaded_segments (0x6c674 : word) = Some W_6c62c.
Proof. vm_refl. Qed.
Lemma D_6c62c : decode_any W_6c62c = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c630 : bv 32 := 0x00e7e733.
Lemma F_6c630 : fetch_word AsanUbsan.M.loaded_segments (0x6c678 : word) = Some W_6c630.
Proof. vm_refl. Qed.
Lemma D_6c630 : decode_any W_6c630 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c634 : bv 32 := 0x0e071c63.
Lemma F_6c634 : fetch_word AsanUbsan.M.loaded_segments (0x6c67c : word) = Some W_6c634.
Proof. vm_refl. Qed.
Lemma D_6c634 : decode_any W_6c634 = Some (Branch BC_NE 14 0 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c694 : bv 32 := 0x412504b3.
Lemma F_6c694 : fetch_word AsanUbsan.M.loaded_segments (0x6c6dc : word) = Some W_6c694.
Proof. vm_refl. Qed.
Lemma D_6c694 : decode_any W_6c694 = Some (Op ALU_SUB 9 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c698 : bv 32 := 0x00148493.
Lemma F_6c698 : fetch_word AsanUbsan.M.loaded_segments (0x6c6e0 : word) = Some W_6c698.
Proof. vm_refl. Qed.
Lemma D_6c698 : decode_any W_6c698 = Some (OpImm ALU_ADD 9 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c69c : bv 32 := 0xfff94593.
Lemma F_6c69c : fetch_word AsanUbsan.M.loaded_segments (0x6c6e4 : word) = Some W_6c69c.
Proof. vm_refl. Qed.
Lemma D_6c69c : decode_any W_6c69c = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c6a0 : bv 32 := 0x80040a13.
Lemma F_6c6a0 : fetch_word AsanUbsan.M.loaded_segments (0x6c6e8 : word) = Some W_6c6a0.
Proof. vm_refl. Qed.
Lemma D_6c6a0 : decode_any W_6c6a0 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c6a4 : bv 32 := 0xfb0a0a13.
Lemma F_6c6a4 : fetch_word AsanUbsan.M.loaded_segments (0x6c6ec : word) = Some W_6c6a4.
Proof. vm_refl. Qed.
Lemma D_6c6a4 : decode_any W_6c6a4 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c6a8 : bv 32 := 0xf495f4e3.
Lemma F_6c6a8 : fetch_word AsanUbsan.M.loaded_segments (0x6c6f0 : word) = Some W_6c6a8.
Proof. vm_refl. Qed.
Lemma D_6c6a8 : decode_any W_6c6a8 = Some (Branch BC_GEU 11 9 8008, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c724 : bv 32 := 0x02049e63.
Lemma F_6c724 : fetch_word AsanUbsan.M.loaded_segments (0x6c76c : word) = Some W_6c724.
Proof. vm_refl. Qed.
Lemma D_6c724 : decode_any W_6c724 = Some (Branch BC_NE 9 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c760 : bv 32 := 0x00050a93.
Lemma F_6c760 : fetch_word AsanUbsan.M.loaded_segments (0x6c7a8 : word) = Some W_6c760.
Proof. vm_refl. Qed.
Lemma D_6c760 : decode_any W_6c760 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c764 : bv 32 := 0x00090513.
Lemma F_6c764 : fetch_word AsanUbsan.M.loaded_segments (0x6c7ac : word) = Some W_6c764.
Proof. vm_refl. Qed.
Lemma D_6c764 : decode_any W_6c764 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c768 : bv 32 := 0x00048593.
Lemma F_6c768 : fetch_word AsanUbsan.M.loaded_segments (0x6c7b0 : word) = Some W_6c768.
Proof. vm_refl. Qed.
Lemma D_6c768 : decode_any W_6c768 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c76c : bv 32 := 0x2ac160ef.
Lemma F_6c76c : fetch_word AsanUbsan.M.loaded_segments (0x6c7b4 : word) = Some W_6c76c.
Proof. vm_refl. Qed.
Lemma D_6c76c : decode_any W_6c76c = Some (Jal 1 90796, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c770 : bv 32 := 0x00050913.
Lemma F_6c770 : fetch_word AsanUbsan.M.loaded_segments (0x6c7b8 : word) = Some W_6c770.
Proof. vm_refl. Qed.
Lemma D_6c770 : decode_any W_6c770 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c774 : bv 32 := 0x000a8513.
Lemma F_6c774 : fetch_word AsanUbsan.M.loaded_segments (0x6c7bc : word) = Some W_6c774.
Proof. vm_refl. Qed.
Lemma D_6c774 : decode_any W_6c774 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c778 : bv 32 := 0xec0900e3.
Lemma F_6c778 : fetch_word AsanUbsan.M.loaded_segments (0x6c7c0 : word) = Some W_6c778.
Proof. vm_refl. Qed.
Lemma D_6c778 : decode_any W_6c778 = Some (Branch BC_EQ 18 0 7872, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cac4 : bv 32 := 0x81010113.
Lemma F_6cac4 : fetch_word AsanUbsan.M.loaded_segments (0x6cb0c : word) = Some W_6cac4.
Proof. vm_refl. Qed.
Lemma D_6cac4 : decode_any W_6cac4 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cac8 : bv 32 := 0x7e113423.
Lemma F_6cac8 : fetch_word AsanUbsan.M.loaded_segments (0x6cb10 : word) = Some W_6cac8.
Proof. vm_refl. Qed.
Lemma D_6cac8 : decode_any W_6cac8 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cacc : bv 32 := 0x7e813023.
Lemma F_6cacc : fetch_word AsanUbsan.M.loaded_segments (0x6cb14 : word) = Some W_6cacc.
Proof. vm_refl. Qed.
Lemma D_6cacc : decode_any W_6cacc = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cad0 : bv 32 := 0x7c913c23.
Lemma F_6cad0 : fetch_word AsanUbsan.M.loaded_segments (0x6cb18 : word) = Some W_6cad0.
Proof. vm_refl. Qed.
Lemma D_6cad0 : decode_any W_6cad0 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cad4 : bv 32 := 0x7d213823.
Lemma F_6cad4 : fetch_word AsanUbsan.M.loaded_segments (0x6cb1c : word) = Some W_6cad4.
Proof. vm_refl. Qed.
Lemma D_6cad4 : decode_any W_6cad4 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cad8 : bv 32 := 0x7d313423.
Lemma F_6cad8 : fetch_word AsanUbsan.M.loaded_segments (0x6cb20 : word) = Some W_6cad8.
Proof. vm_refl. Qed.
Lemma D_6cad8 : decode_any W_6cad8 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cadc : bv 32 := 0x7d413023.
Lemma F_6cadc : fetch_word AsanUbsan.M.loaded_segments (0x6cb24 : word) = Some W_6cadc.
Proof. vm_refl. Qed.
Lemma D_6cadc : decode_any W_6cadc = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cae0 : bv 32 := 0x7f010413.
Lemma F_6cae0 : fetch_word AsanUbsan.M.loaded_segments (0x6cb28 : word) = Some W_6cae0.
Proof. vm_refl. Qed.
Lemma D_6cae0 : decode_any W_6cae0 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cae4 : bv 32 := 0xfa010113.
Lemma F_6cae4 : fetch_word AsanUbsan.M.loaded_segments (0x6cb2c : word) = Some W_6cae4.
Proof. vm_refl. Qed.
Lemma D_6cae4 : decode_any W_6cae4 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cae8 : bv 32 := 0x00060913.
Lemma F_6cae8 : fetch_word AsanUbsan.M.loaded_segments (0x6cb30 : word) = Some W_6cae8.
Proof. vm_refl. Qed.
Lemma D_6cae8 : decode_any W_6cae8 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6caec : bv 32 := 0x00058493.
Lemma F_6caec : fetch_word AsanUbsan.M.loaded_segments (0x6cb34 : word) = Some W_6caec.
Proof. vm_refl. Qed.
Lemma D_6caec : decode_any W_6caec = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6caf0 : bv 32 := 0x00050993.
Lemma F_6caf0 : fetch_word AsanUbsan.M.loaded_segments (0x6cb38 : word) = Some W_6caf0.
Proof. vm_refl. Qed.
Lemma D_6caf0 : decode_any W_6caf0 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6caf4 : bv 32 := 0x3491b0ef.
Lemma F_6caf4 : fetch_word AsanUbsan.M.loaded_segments (0x6cb3c : word) = Some W_6caf4.
Proof. vm_refl. Qed.
Lemma D_6caf4 : decode_any W_6caf4 = Some (Jal 1 113480, 4%Z).
Proof. vm_refl. Qed.

Definition W_6caf8 : bv 32 := 0x000ea597.
Lemma F_6caf8 : fetch_word AsanUbsan.M.loaded_segments (0x6cb40 : word) = Some W_6caf8.
Proof. vm_refl. Qed.
Lemma D_6caf8 : decode_any W_6caf8 = Some (Auipc 11 234, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cafc : bv 32 := 0x8305b683.
Lemma F_6cafc : fetch_word AsanUbsan.M.loaded_segments (0x6cb44 : word) = Some W_6cafc.
Proof. vm_refl. Qed.
Lemma D_6cafc : decode_any W_6cafc = Some (Load SZ8 true 13 11 2096, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb00 : bv 32 := 0x00050a13.
Lemma F_6cb00 : fetch_word AsanUbsan.M.loaded_segments (0x6cb48 : word) = Some W_6cb00.
Proof. vm_refl. Qed.
Lemma D_6cb00 : decode_any W_6cb00 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb04 : bv 32 := 0x00098513.
Lemma F_6cb04 : fetch_word AsanUbsan.M.loaded_segments (0x6cb4c : word) = Some W_6cb04.
Proof. vm_refl. Qed.
Lemma D_6cb04 : decode_any W_6cb04 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb08 : bv 32 := 0x00048593.
Lemma F_6cb08 : fetch_word AsanUbsan.M.loaded_segments (0x6cb50 : word) = Some W_6cb08.
Proof. vm_refl. Qed.
Lemma D_6cb08 : decode_any W_6cb08 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb0c : bv 32 := 0x00090613.
Lemma F_6cb0c : fetch_word AsanUbsan.M.loaded_segments (0x6cb54 : word) = Some W_6cb0c.
Proof. vm_refl. Qed.
Lemma D_6cb0c : decode_any W_6cb0c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb10 : bv 32 := 0x000680e7.
Lemma F_6cb10 : fetch_word AsanUbsan.M.loaded_segments (0x6cb58 : word) = Some W_6cb10.
Proof. vm_refl. Qed.
Lemma D_6cb10 : decode_any W_6cb10 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb14 : bv 32 := 0x060a0063.
Lemma F_6cb14 : fetch_word AsanUbsan.M.loaded_segments (0x6cb5c : word) = Some W_6cb14.
Proof. vm_refl. Qed.
Lemma D_6cb14 : decode_any W_6cb14 = Some (Branch BC_EQ 20 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb18 : bv 32 := 0x04a05e63.
Lemma F_6cb18 : fetch_word AsanUbsan.M.loaded_segments (0x6cb60 : word) = Some W_6cb18.
Proof. vm_refl. Qed.
Lemma D_6cb18 : decode_any W_6cb18 = Some (Branch BC_GE 0 10 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb1c : bv 32 := 0xfff4c593.
Lemma F_6cb1c : fetch_word AsanUbsan.M.loaded_segments (0x6cb64 : word) = Some W_6cb1c.
Proof. vm_refl. Qed.
Lemma D_6cb1c : decode_any W_6cb1c = Some (OpImm ALU_XOR 11 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb20 : bv 32 := 0x80040a13.
Lemma F_6cb20 : fetch_word AsanUbsan.M.loaded_segments (0x6cb68 : word) = Some W_6cb20.
Proof. vm_refl. Qed.
Lemma D_6cb20 : decode_any W_6cb20 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb24 : bv 32 := 0xfb8a0a13.
Lemma F_6cb24 : fetch_word AsanUbsan.M.loaded_segments (0x6cb6c : word) = Some W_6cb24.
Proof. vm_refl. Qed.
Lemma D_6cb24 : decode_any W_6cb24 = Some (OpImm ALU_ADD 20 20 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb28 : bv 32 := 0x06a5e863.
Lemma F_6cb28 : fetch_word AsanUbsan.M.loaded_segments (0x6cb70 : word) = Some W_6cb28.
Proof. vm_refl. Qed.
Lemma D_6cb28 : decode_any W_6cb28 = Some (Branch BC_LTU 11 10 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb2c : bv 32 := 0xfbf50593.
Lemma F_6cb2c : fetch_word AsanUbsan.M.loaded_segments (0x6cb74 : word) = Some W_6cb2c.
Proof. vm_refl. Qed.
Lemma D_6cb2c : decode_any W_6cb2c = Some (OpImm ALU_ADD 11 10 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb30 : bv 32 := 0xfc000613.
Lemma F_6cb30 : fetch_word AsanUbsan.M.loaded_segments (0x6cb78 : word) = Some W_6cb30.
Proof. vm_refl. Qed.
Lemma D_6cb30 : decode_any W_6cb30 = Some (OpImm ALU_ADD 12 0 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb34 : bv 32 := 0x0cc5ee63.
Lemma F_6cb34 : fetch_word AsanUbsan.M.loaded_segments (0x6cb7c : word) = Some W_6cb34.
Proof. vm_refl. Qed.
Lemma D_6cb34 : decode_any W_6cb34 = Some (Branch BC_LTU 11 12 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb38 : bv 32 := 0x000e8597.
Lemma F_6cb38 : fetch_word AsanUbsan.M.loaded_segments (0x6cb80 : word) = Some W_6cb38.
Proof. vm_refl. Qed.
Lemma D_6cb38 : decode_any W_6cb38 = Some (Auipc 11 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb3c : bv 32 := 0x9805b583.
Lemma F_6cb3c : fetch_word AsanUbsan.M.loaded_segments (0x6cb84 : word) = Some W_6cb3c.
Proof. vm_refl. Qed.
Lemma D_6cb3c : decode_any W_6cb3c = Some (Load SZ8 true 11 11 2432, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb40 : bv 32 := 0x00a486b3.
Lemma F_6cb40 : fetch_word AsanUbsan.M.loaded_segments (0x6cb88 : word) = Some W_6cb40.
Proof. vm_refl. Qed.
Lemma D_6cb40 : decode_any W_6cb40 = Some (Op ALU_ADD 13 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb44 : bv 32 := 0x0005b603.
Lemma F_6cb44 : fetch_word AsanUbsan.M.loaded_segments (0x6cb8c : word) = Some W_6cb44.
Proof. vm_refl. Qed.
Lemma D_6cb44 : decode_any W_6cb44 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb48 : bv 32 := 0x0034d593.
Lemma F_6cb48 : fetch_word AsanUbsan.M.loaded_segments (0x6cb90 : word) = Some W_6cb48.
Proof. vm_refl. Qed.
Lemma D_6cb48 : decode_any W_6cb48 = Some (ShiftImm ALU_SRL 11 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb4c : bv 32 := 0xfff68693.
Lemma F_6cb4c : fetch_word AsanUbsan.M.loaded_segments (0x6cb94 : word) = Some W_6cb4c.
Proof. vm_refl. Qed.
Lemma D_6cb4c : decode_any W_6cb4c = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb50 : bv 32 := 0x0036d713.
Lemma F_6cb50 : fetch_word AsanUbsan.M.loaded_segments (0x6cb98 : word) = Some W_6cb50.
Proof. vm_refl. Qed.
Lemma D_6cb50 : decode_any W_6cb50 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb54 : bv 32 := 0x00b605b3.
Lemma F_6cb54 : fetch_word AsanUbsan.M.loaded_segments (0x6cb9c : word) = Some W_6cb54.
Proof. vm_refl. Qed.
Lemma D_6cb54 : decode_any W_6cb54 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb58 : bv 32 := 0x00e60633.
Lemma F_6cb58 : fetch_word AsanUbsan.M.loaded_segments (0x6cba0 : word) = Some W_6cb58.
Proof. vm_refl. Qed.
Lemma D_6cb58 : decode_any W_6cb58 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb5c : bv 32 := 0xff85f713.
Lemma F_6cb5c : fetch_word AsanUbsan.M.loaded_segments (0x6cba4 : word) = Some W_6cb5c.
Proof. vm_refl. Qed.
Lemma D_6cb5c : decode_any W_6cb5c = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb60 : bv 32 := 0xff867793.
Lemma F_6cb60 : fetch_word AsanUbsan.M.loaded_segments (0x6cba8 : word) = Some W_6cb60.
Proof. vm_refl. Qed.
Lemma D_6cb60 : decode_any W_6cb60 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb64 : bv 32 := 0x00073703.
Lemma F_6cb64 : fetch_word AsanUbsan.M.loaded_segments (0x6cbac : word) = Some W_6cb64.
Proof. vm_refl. Qed.
Lemma D_6cb64 : decode_any W_6cb64 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb68 : bv 32 := 0x0007b783.
Lemma F_6cb68 : fetch_word AsanUbsan.M.loaded_segments (0x6cbb0 : word) = Some W_6cb68.
Proof. vm_refl. Qed.
Lemma D_6cb68 : decode_any W_6cb68 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb6c : bv 32 := 0x00e7e733.
Lemma F_6cb6c : fetch_word AsanUbsan.M.loaded_segments (0x6cbb4 : word) = Some W_6cb6c.
Proof. vm_refl. Qed.
Lemma D_6cb6c : decode_any W_6cb6c = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb70 : bv 32 := 0x14071663.
Lemma F_6cb70 : fetch_word AsanUbsan.M.loaded_segments (0x6cbb8 : word) = Some W_6cb70.
Proof. vm_refl. Qed.
Lemma D_6cb70 : decode_any W_6cb70 = Some (Branch BC_NE 14 0 332, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb74 : bv 32 := 0x06010113.
Lemma F_6cb74 : fetch_word AsanUbsan.M.loaded_segments (0x6cbbc : word) = Some W_6cb74.
Proof. vm_refl. Qed.
Lemma D_6cb74 : decode_any W_6cb74 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb78 : bv 32 := 0x7e813083.
Lemma F_6cb78 : fetch_word AsanUbsan.M.loaded_segments (0x6cbc0 : word) = Some W_6cb78.
Proof. vm_refl. Qed.
Lemma D_6cb78 : decode_any W_6cb78 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb7c : bv 32 := 0x7e013403.
Lemma F_6cb7c : fetch_word AsanUbsan.M.loaded_segments (0x6cbc4 : word) = Some W_6cb7c.
Proof. vm_refl. Qed.
Lemma D_6cb7c : decode_any W_6cb7c = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb80 : bv 32 := 0x7d813483.
Lemma F_6cb80 : fetch_word AsanUbsan.M.loaded_segments (0x6cbc8 : word) = Some W_6cb80.
Proof. vm_refl. Qed.
Lemma D_6cb80 : decode_any W_6cb80 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb84 : bv 32 := 0x7d013903.
Lemma F_6cb84 : fetch_word AsanUbsan.M.loaded_segments (0x6cbcc : word) = Some W_6cb84.
Proof. vm_refl. Qed.
Lemma D_6cb84 : decode_any W_6cb84 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb88 : bv 32 := 0x7c813983.
Lemma F_6cb88 : fetch_word AsanUbsan.M.loaded_segments (0x6cbd0 : word) = Some W_6cb88.
Proof. vm_refl. Qed.
Lemma D_6cb88 : decode_any W_6cb88 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb8c : bv 32 := 0x7c013a03.
Lemma F_6cb8c : fetch_word AsanUbsan.M.loaded_segments (0x6cbd4 : word) = Some W_6cb8c.
Proof. vm_refl. Qed.
Lemma D_6cb8c : decode_any W_6cb8c = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb90 : bv 32 := 0x7f010113.
Lemma F_6cb90 : fetch_word AsanUbsan.M.loaded_segments (0x6cbd8 : word) = Some W_6cb90.
Proof. vm_refl. Qed.
Lemma D_6cb90 : decode_any W_6cb90 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cb94 : bv 32 := 0x00008067.
Lemma F_6cb94 : fetch_word AsanUbsan.M.loaded_segments (0x6cbdc : word) = Some W_6cb94.
Proof. vm_refl. Qed.
Lemma D_6cb94 : decode_any W_6cb94 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cc10 : bv 32 := 0x00050913.
Lemma F_6cc10 : fetch_word AsanUbsan.M.loaded_segments (0x6cc58 : word) = Some W_6cc10.
Proof. vm_refl. Qed.
Lemma D_6cc10 : decode_any W_6cc10 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cc14 : bv 32 := 0x00048513.
Lemma F_6cc14 : fetch_word AsanUbsan.M.loaded_segments (0x6cc5c : word) = Some W_6cc14.
Proof. vm_refl. Qed.
Lemma D_6cc14 : decode_any W_6cc14 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cc18 : bv 32 := 0x00090593.
Lemma F_6cc18 : fetch_word AsanUbsan.M.loaded_segments (0x6cc60 : word) = Some W_6cc18.
Proof. vm_refl. Qed.
Lemma D_6cc18 : decode_any W_6cc18 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cc1c : bv 32 := 0x5fd150ef.
Lemma F_6cc1c : fetch_word AsanUbsan.M.loaded_segments (0x6cc64 : word) = Some W_6cc1c.
Proof. vm_refl. Qed.
Lemma D_6cc1c : decode_any W_6cc1c = Some (Jal 1 89596, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cc20 : bv 32 := 0x00050493.
Lemma F_6cc20 : fetch_word AsanUbsan.M.loaded_segments (0x6cc68 : word) = Some W_6cc20.
Proof. vm_refl. Qed.
Lemma D_6cc20 : decode_any W_6cc20 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cc24 : bv 32 := 0x00090513.
Lemma F_6cc24 : fetch_word AsanUbsan.M.loaded_segments (0x6cc6c : word) = Some W_6cc24.
Proof. vm_refl. Qed.
Lemma D_6cc24 : decode_any W_6cc24 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cc28 : bv 32 := 0xf40486e3.
Lemma F_6cc28 : fetch_word AsanUbsan.M.loaded_segments (0x6cc70 : word) = Some W_6cc28.
Proof. vm_refl. Qed.
Lemma D_6cc28 : decode_any W_6cc28 = Some (Branch BC_EQ 9 0 8012, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ccbc : bv 32 := 0x00060703.
Lemma F_6ccbc : fetch_word AsanUbsan.M.loaded_segments (0x6cd04 : word) = Some W_6ccbc.
Proof. vm_refl. Qed.
Lemma D_6ccbc : decode_any W_6ccbc = Some (Load SZ1 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ccc0 : bv 32 := 0x0076f693.
Lemma F_6ccc0 : fetch_word AsanUbsan.M.loaded_segments (0x6cd08 : word) = Some W_6ccc0.
Proof. vm_refl. Qed.
Lemma D_6ccc0 : decode_any W_6ccc0 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ccc4 : bv 32 := 0x00e037b3.
Lemma F_6ccc4 : fetch_word AsanUbsan.M.loaded_segments (0x6cd0c : word) = Some W_6ccc4.
Proof. vm_refl. Qed.
Lemma D_6ccc4 : decode_any W_6ccc4 = Some (Op ALU_SLTU 15 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ccc8 : bv 32 := 0x00e6a6b3.
Lemma F_6ccc8 : fetch_word AsanUbsan.M.loaded_segments (0x6cd10 : word) = Some W_6ccc8.
Proof. vm_refl. Qed.
Lemma D_6ccc8 : decode_any W_6ccc8 = Some (Op ALU_SLT 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cccc : bv 32 := 0x0016c693.
Lemma F_6cccc : fetch_word AsanUbsan.M.loaded_segments (0x6cd14 : word) = Some W_6cccc.
Proof. vm_refl. Qed.
Lemma D_6cccc : decode_any W_6cccc = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ccd0 : bv 32 := 0x00d7f6b3.
Lemma F_6ccd0 : fetch_word AsanUbsan.M.loaded_segments (0x6cd18 : word) = Some W_6ccd0.
Proof. vm_refl. Qed.
Lemma D_6ccd0 : decode_any W_6ccd0 = Some (Op ALU_AND 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ccd4 : bv 32 := 0x00c5fa63.
Lemma F_6ccd4 : fetch_word AsanUbsan.M.loaded_segments (0x6cd1c : word) = Some W_6ccd4.
Proof. vm_refl. Qed.
Lemma D_6ccd4 : decode_any W_6ccd4 = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ccd8 : bv 32 := 0x0005c703.
Lemma F_6ccd8 : fetch_word AsanUbsan.M.loaded_segments (0x6cd20 : word) = Some W_6ccd8.
Proof. vm_refl. Qed.
Lemma D_6ccd8 : decode_any W_6ccd8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ccdc : bv 32 := 0x00158593.
Lemma F_6ccdc : fetch_word AsanUbsan.M.loaded_segments (0x6cd24 : word) = Some W_6ccdc.
Proof. vm_refl. Qed.
Lemma D_6ccdc : decode_any W_6ccdc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cce0 : bv 32 := 0x00d766b3.
Lemma F_6cce0 : fetch_word AsanUbsan.M.loaded_segments (0x6cd28 : word) = Some W_6cce0.
Proof. vm_refl. Qed.
Lemma D_6cce0 : decode_any W_6cce0 = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cce4 : bv 32 := 0xfec59ae3.
Lemma F_6cce4 : fetch_word AsanUbsan.M.loaded_segments (0x6cd2c : word) = Some W_6cce4.
Proof. vm_refl. Qed.
Lemma D_6cce4 : decode_any W_6cce4 = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_6cce8 : bv 32 := 0x0ff6f593.
Lemma F_6cce8 : fetch_word AsanUbsan.M.loaded_segments (0x6cd30 : word) = Some W_6cce8.
Proof. vm_refl. Qed.
Lemma D_6cce8 : decode_any W_6cce8 = Some (OpImm ALU_AND 11 13 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ccec : bv 32 := 0xe80584e3.
Lemma F_6ccec : fetch_word AsanUbsan.M.loaded_segments (0x6cd34 : word) = Some W_6ccec.
Proof. vm_refl. Qed.
Lemma D_6ccec : decode_any W_6ccec = Some (Branch BC_EQ 11 0 7816, 4%Z).
Proof. vm_refl. Qed.


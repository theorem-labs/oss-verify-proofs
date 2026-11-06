(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_4f680 : bv 32 := 0x060a0063.
Lemma F_4f680 : fetch_word AsanUbsan.M.loaded_segments (0x4f680 : word) = Some W_4f680.
Proof. vm_refl. Qed.
Lemma D_4f680 : decode_any W_4f680 = Some (Branch BC_EQ 20 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f684 : bv 32 := 0x0a051c63.
Lemma F_4f684 : fetch_word AsanUbsan.M.loaded_segments (0x4f684 : word) = Some W_4f684.
Proof. vm_refl. Qed.
Lemma D_4f684 : decode_any W_4f684 = Some (Branch BC_NE 10 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f688 : bv 32 := 0xfff94593.
Lemma F_4f688 : fetch_word AsanUbsan.M.loaded_segments (0x4f688 : word) = Some W_4f688.
Proof. vm_refl. Qed.
Lemma D_4f688 : decode_any W_4f688 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f68c : bv 32 := 0x80040a13.
Lemma F_4f68c : fetch_word AsanUbsan.M.loaded_segments (0x4f68c : word) = Some W_4f68c.
Proof. vm_refl. Qed.
Lemma D_4f68c : decode_any W_4f68c = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f690 : bv 32 := 0xfb0a0a13.
Lemma F_4f690 : fetch_word AsanUbsan.M.loaded_segments (0x4f690 : word) = Some W_4f690.
Proof. vm_refl. Qed.
Lemma D_4f690 : decode_any W_4f690 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f694 : bv 32 := 0x0c95e063.
Lemma F_4f694 : fetch_word AsanUbsan.M.loaded_segments (0x4f694 : word) = Some W_4f694.
Proof. vm_refl. Qed.
Lemma D_4f694 : decode_any W_4f694 = Some (Branch BC_LTU 11 9 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f698 : bv 32 := 0xfbf48593.
Lemma F_4f698 : fetch_word AsanUbsan.M.loaded_segments (0x4f698 : word) = Some W_4f698.
Proof. vm_refl. Qed.
Lemma D_4f698 : decode_any W_4f698 = Some (OpImm ALU_ADD 11 9 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f69c : bv 32 := 0xfbf00613.
Lemma F_4f69c : fetch_word AsanUbsan.M.loaded_segments (0x4f69c : word) = Some W_4f69c.
Proof. vm_refl. Qed.
Lemma D_4f69c : decode_any W_4f69c = Some (OpImm ALU_ADD 12 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f6a0 : bv 32 := 0x12b67663.
Lemma F_4f6a0 : fetch_word AsanUbsan.M.loaded_segments (0x4f6a0 : word) = Some W_4f6a0.
Proof. vm_refl. Qed.
Lemma D_4f6a0 : decode_any W_4f6a0 = Some (Branch BC_GEU 12 11 300, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f6a4 : bv 32 := 0x00087597.
Lemma F_4f6a4 : fetch_word AsanUbsan.M.loaded_segments (0x4f6a4 : word) = Some W_4f6a4.
Proof. vm_refl. Qed.
Lemma D_4f6a4 : decode_any W_4f6a4 = Some (Auipc 11 135, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f6a8 : bv 32 := 0xe245b583.
Lemma F_4f6a8 : fetch_word AsanUbsan.M.loaded_segments (0x4f6a8 : word) = Some W_4f6a8.
Proof. vm_refl. Qed.
Lemma D_4f6a8 : decode_any W_4f6a8 = Some (Load SZ8 true 11 11 3620, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f6ac : bv 32 := 0x009906b3.
Lemma F_4f6ac : fetch_word AsanUbsan.M.loaded_segments (0x4f6ac : word) = Some W_4f6ac.
Proof. vm_refl. Qed.
Lemma D_4f6ac : decode_any W_4f6ac = Some (Op ALU_ADD 13 18 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f6b0 : bv 32 := 0x0005b603.
Lemma F_4f6b0 : fetch_word AsanUbsan.M.loaded_segments (0x4f6b0 : word) = Some W_4f6b0.
Proof. vm_refl. Qed.
Lemma D_4f6b0 : decode_any W_4f6b0 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f6b4 : bv 32 := 0x00395593.
Lemma F_4f6b4 : fetch_word AsanUbsan.M.loaded_segments (0x4f6b4 : word) = Some W_4f6b4.
Proof. vm_refl. Qed.
Lemma D_4f6b4 : decode_any W_4f6b4 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f6b8 : bv 32 := 0xfff68693.
Lemma F_4f6b8 : fetch_word AsanUbsan.M.loaded_segments (0x4f6b8 : word) = Some W_4f6b8.
Proof. vm_refl. Qed.
Lemma D_4f6b8 : decode_any W_4f6b8 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f6bc : bv 32 := 0x0036d713.
Lemma F_4f6bc : fetch_word AsanUbsan.M.loaded_segments (0x4f6bc : word) = Some W_4f6bc.
Proof. vm_refl. Qed.
Lemma D_4f6bc : decode_any W_4f6bc = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f6c0 : bv 32 := 0x00b605b3.
Lemma F_4f6c0 : fetch_word AsanUbsan.M.loaded_segments (0x4f6c0 : word) = Some W_4f6c0.
Proof. vm_refl. Qed.
Lemma D_4f6c0 : decode_any W_4f6c0 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f6c4 : bv 32 := 0x00e60633.
Lemma F_4f6c4 : fetch_word AsanUbsan.M.loaded_segments (0x4f6c4 : word) = Some W_4f6c4.
Proof. vm_refl. Qed.
Lemma D_4f6c4 : decode_any W_4f6c4 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f6c8 : bv 32 := 0xff85f713.
Lemma F_4f6c8 : fetch_word AsanUbsan.M.loaded_segments (0x4f6c8 : word) = Some W_4f6c8.
Proof. vm_refl. Qed.
Lemma D_4f6c8 : decode_any W_4f6c8 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f6cc : bv 32 := 0xff867793.
Lemma F_4f6cc : fetch_word AsanUbsan.M.loaded_segments (0x4f6cc : word) = Some W_4f6cc.
Proof. vm_refl. Qed.
Lemma D_4f6cc : decode_any W_4f6cc = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f6d0 : bv 32 := 0x00073703.
Lemma F_4f6d0 : fetch_word AsanUbsan.M.loaded_segments (0x4f6d0 : word) = Some W_4f6d0.
Proof. vm_refl. Qed.
Lemma D_4f6d0 : decode_any W_4f6d0 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f6d4 : bv 32 := 0x0007b783.
Lemma F_4f6d4 : fetch_word AsanUbsan.M.loaded_segments (0x4f6d4 : word) = Some W_4f6d4.
Proof. vm_refl. Qed.
Lemma D_4f6d4 : decode_any W_4f6d4 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f6d8 : bv 32 := 0x00e7e733.
Lemma F_4f6d8 : fetch_word AsanUbsan.M.loaded_segments (0x4f6d8 : word) = Some W_4f6d8.
Proof. vm_refl. Qed.
Lemma D_4f6d8 : decode_any W_4f6d8 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f6dc : bv 32 := 0x0e071c63.
Lemma F_4f6dc : fetch_word AsanUbsan.M.loaded_segments (0x4f6dc : word) = Some W_4f6dc.
Proof. vm_refl. Qed.
Lemma D_4f6dc : decode_any W_4f6dc = Some (Branch BC_NE 14 0 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f6e0 : bv 32 := 0x06010113.
Lemma F_4f6e0 : fetch_word AsanUbsan.M.loaded_segments (0x4f6e0 : word) = Some W_4f6e0.
Proof. vm_refl. Qed.
Lemma D_4f6e0 : decode_any W_4f6e0 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f6e4 : bv 32 := 0x7e813083.
Lemma F_4f6e4 : fetch_word AsanUbsan.M.loaded_segments (0x4f6e4 : word) = Some W_4f6e4.
Proof. vm_refl. Qed.
Lemma D_4f6e4 : decode_any W_4f6e4 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f6e8 : bv 32 := 0x7e013403.
Lemma F_4f6e8 : fetch_word AsanUbsan.M.loaded_segments (0x4f6e8 : word) = Some W_4f6e8.
Proof. vm_refl. Qed.
Lemma D_4f6e8 : decode_any W_4f6e8 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f6ec : bv 32 := 0x7d813483.
Lemma F_4f6ec : fetch_word AsanUbsan.M.loaded_segments (0x4f6ec : word) = Some W_4f6ec.
Proof. vm_refl. Qed.
Lemma D_4f6ec : decode_any W_4f6ec = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f6f0 : bv 32 := 0x7d013903.
Lemma F_4f6f0 : fetch_word AsanUbsan.M.loaded_segments (0x4f6f0 : word) = Some W_4f6f0.
Proof. vm_refl. Qed.
Lemma D_4f6f0 : decode_any W_4f6f0 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f6f4 : bv 32 := 0x7c813983.
Lemma F_4f6f4 : fetch_word AsanUbsan.M.loaded_segments (0x4f6f4 : word) = Some W_4f6f4.
Proof. vm_refl. Qed.
Lemma D_4f6f4 : decode_any W_4f6f4 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f6f8 : bv 32 := 0x7c013a03.
Lemma F_4f6f8 : fetch_word AsanUbsan.M.loaded_segments (0x4f6f8 : word) = Some W_4f6f8.
Proof. vm_refl. Qed.
Lemma D_4f6f8 : decode_any W_4f6f8 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f6fc : bv 32 := 0x7b813a83.
Lemma F_4f6fc : fetch_word AsanUbsan.M.loaded_segments (0x4f6fc : word) = Some W_4f6fc.
Proof. vm_refl. Qed.
Lemma D_4f6fc : decode_any W_4f6fc = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f700 : bv 32 := 0x7f010113.
Lemma F_4f700 : fetch_word AsanUbsan.M.loaded_segments (0x4f700 : word) = Some W_4f700.
Proof. vm_refl. Qed.
Lemma D_4f700 : decode_any W_4f700 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f704 : bv 32 := 0x00008067.
Lemma F_4f704 : fetch_word AsanUbsan.M.loaded_segments (0x4f704 : word) = Some W_4f704.
Proof. vm_refl. Qed.
Lemma D_4f704 : decode_any W_4f704 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f708 : bv 32 := 0x00090513.
Lemma F_4f708 : fetch_word AsanUbsan.M.loaded_segments (0x4f708 : word) = Some W_4f708.
Proof. vm_refl. Qed.
Lemma D_4f708 : decode_any W_4f708 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f70c : bv 32 := 0x00098593.
Lemma F_4f70c : fetch_word AsanUbsan.M.loaded_segments (0x4f70c : word) = Some W_4f70c.
Proof. vm_refl. Qed.
Lemma D_4f70c : decode_any W_4f70c = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f710 : bv 32 := 0x00048613.
Lemma F_4f710 : fetch_word AsanUbsan.M.loaded_segments (0x4f710 : word) = Some W_4f710.
Proof. vm_refl. Qed.
Lemma D_4f710 : decode_any W_4f710 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f714 : bv 32 := 0x06010113.
Lemma F_4f714 : fetch_word AsanUbsan.M.loaded_segments (0x4f714 : word) = Some W_4f714.
Proof. vm_refl. Qed.
Lemma D_4f714 : decode_any W_4f714 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f718 : bv 32 := 0x7e813083.
Lemma F_4f718 : fetch_word AsanUbsan.M.loaded_segments (0x4f718 : word) = Some W_4f718.
Proof. vm_refl. Qed.
Lemma D_4f718 : decode_any W_4f718 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f71c : bv 32 := 0x7e013403.
Lemma F_4f71c : fetch_word AsanUbsan.M.loaded_segments (0x4f71c : word) = Some W_4f71c.
Proof. vm_refl. Qed.
Lemma D_4f71c : decode_any W_4f71c = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f720 : bv 32 := 0x7d813483.
Lemma F_4f720 : fetch_word AsanUbsan.M.loaded_segments (0x4f720 : word) = Some W_4f720.
Proof. vm_refl. Qed.
Lemma D_4f720 : decode_any W_4f720 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f724 : bv 32 := 0x7d013903.
Lemma F_4f724 : fetch_word AsanUbsan.M.loaded_segments (0x4f724 : word) = Some W_4f724.
Proof. vm_refl. Qed.
Lemma D_4f724 : decode_any W_4f724 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f728 : bv 32 := 0x7c813983.
Lemma F_4f728 : fetch_word AsanUbsan.M.loaded_segments (0x4f728 : word) = Some W_4f728.
Proof. vm_refl. Qed.
Lemma D_4f728 : decode_any W_4f728 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f72c : bv 32 := 0x7c013a03.
Lemma F_4f72c : fetch_word AsanUbsan.M.loaded_segments (0x4f72c : word) = Some W_4f72c.
Proof. vm_refl. Qed.
Lemma D_4f72c : decode_any W_4f72c = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f730 : bv 32 := 0x7b813a83.
Lemma F_4f730 : fetch_word AsanUbsan.M.loaded_segments (0x4f730 : word) = Some W_4f730.
Proof. vm_refl. Qed.
Lemma D_4f730 : decode_any W_4f730 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f734 : bv 32 := 0x7f010113.
Lemma F_4f734 : fetch_word AsanUbsan.M.loaded_segments (0x4f734 : word) = Some W_4f734.
Proof. vm_refl. Qed.
Lemma D_4f734 : decode_any W_4f734 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f738 : bv 32 := 0x5d52106f.
Lemma F_4f738 : fetch_word AsanUbsan.M.loaded_segments (0x4f738 : word) = Some W_4f738.
Proof. vm_refl. Qed.
Lemma D_4f738 : decode_any W_4f738 = Some (Jal 0 138708, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f73c : bv 32 := 0x412504b3.
Lemma F_4f73c : fetch_word AsanUbsan.M.loaded_segments (0x4f73c : word) = Some W_4f73c.
Proof. vm_refl. Qed.
Lemma D_4f73c : decode_any W_4f73c = Some (Op ALU_SUB 9 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f740 : bv 32 := 0x00148493.
Lemma F_4f740 : fetch_word AsanUbsan.M.loaded_segments (0x4f740 : word) = Some W_4f740.
Proof. vm_refl. Qed.
Lemma D_4f740 : decode_any W_4f740 = Some (OpImm ALU_ADD 9 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f744 : bv 32 := 0xfff94593.
Lemma F_4f744 : fetch_word AsanUbsan.M.loaded_segments (0x4f744 : word) = Some W_4f744.
Proof. vm_refl. Qed.
Lemma D_4f744 : decode_any W_4f744 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f748 : bv 32 := 0x80040a13.
Lemma F_4f748 : fetch_word AsanUbsan.M.loaded_segments (0x4f748 : word) = Some W_4f748.
Proof. vm_refl. Qed.
Lemma D_4f748 : decode_any W_4f748 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f74c : bv 32 := 0xfb0a0a13.
Lemma F_4f74c : fetch_word AsanUbsan.M.loaded_segments (0x4f74c : word) = Some W_4f74c.
Proof. vm_refl. Qed.
Lemma D_4f74c : decode_any W_4f74c = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f750 : bv 32 := 0xf495f4e3.
Lemma F_4f750 : fetch_word AsanUbsan.M.loaded_segments (0x4f750 : word) = Some W_4f750.
Proof. vm_refl. Qed.
Lemma D_4f750 : decode_any W_4f750 = Some (Branch BC_GEU 11 9 8008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f754 : bv 32 := 0x80040593.
Lemma F_4f754 : fetch_word AsanUbsan.M.loaded_segments (0x4f754 : word) = Some W_4f754.
Proof. vm_refl. Qed.
Lemma D_4f754 : decode_any W_4f754 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f758 : bv 32 := 0xfc058593.
Lemma F_4f758 : fetch_word AsanUbsan.M.loaded_segments (0x4f758 : word) = Some W_4f758.
Proof. vm_refl. Qed.
Lemma D_4f758 : decode_any W_4f758 = Some (OpImm ALU_ADD 11 11 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f75c : bv 32 := 0x80040613.
Lemma F_4f75c : fetch_word AsanUbsan.M.loaded_segments (0x4f75c : word) = Some W_4f75c.
Proof. vm_refl. Qed.
Lemma D_4f75c : decode_any W_4f75c = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f760 : bv 32 := 0xfb060613.
Lemma F_4f760 : fetch_word AsanUbsan.M.loaded_segments (0x4f760 : word) = Some W_4f760.
Proof. vm_refl. Qed.
Lemma D_4f760 : decode_any W_4f760 = Some (OpImm ALU_ADD 12 12 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f764 : bv 32 := 0x7ff60a93.
Lemma F_4f764 : fetch_word AsanUbsan.M.loaded_segments (0x4f764 : word) = Some W_4f764.
Proof. vm_refl. Qed.
Lemma D_4f764 : decode_any W_4f764 = Some (OpImm ALU_ADD 21 12 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f768 : bv 32 := 0x000ab4a3.
Lemma F_4f768 : fetch_word AsanUbsan.M.loaded_segments (0x4f768 : word) = Some W_4f768.
Proof. vm_refl. Qed.
Lemma D_4f768 : decode_any W_4f768 = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f76c : bv 32 := 0x00ba3023.
Lemma F_4f76c : fetch_word AsanUbsan.M.loaded_segments (0x4f76c : word) = Some W_4f76c.
Proof. vm_refl. Qed.
Lemma D_4f76c : decode_any W_4f76c = Some (Store SZ8 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f770 : bv 32 := 0x000a3423.
Lemma F_4f770 : fetch_word AsanUbsan.M.loaded_segments (0x4f770 : word) = Some W_4f770.
Proof. vm_refl. Qed.
Lemma D_4f770 : decode_any W_4f770 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f774 : bv 32 := 0x00050993.
Lemma F_4f774 : fetch_word AsanUbsan.M.loaded_segments (0x4f774 : word) = Some W_4f774.
Proof. vm_refl. Qed.
Lemma D_4f774 : decode_any W_4f774 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f778 : bv 32 := 0x334310ef.
Lemma F_4f778 : fetch_word AsanUbsan.M.loaded_segments (0x4f778 : word) = Some W_4f778.
Proof. vm_refl. Qed.
Lemma D_4f778 : decode_any W_4f778 = Some (Jal 1 201524, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f77c : bv 32 := 0x00050593.
Lemma F_4f77c : fetch_word AsanUbsan.M.loaded_segments (0x4f77c : word) = Some W_4f77c.
Proof. vm_refl. Qed.
Lemma D_4f77c : decode_any W_4f77c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f780 : bv 32 := 0x00087517.
Lemma F_4f780 : fetch_word AsanUbsan.M.loaded_segments (0x4f780 : word) = Some W_4f780.
Proof. vm_refl. Qed.
Lemma D_4f780 : decode_any W_4f780 = Some (Auipc 10 135, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f784 : bv 32 := 0xd3853503.
Lemma F_4f784 : fetch_word AsanUbsan.M.loaded_segments (0x4f784 : word) = Some W_4f784.
Proof. vm_refl. Qed.
Lemma D_4f784 : decode_any W_4f784 = Some (Load SZ8 true 10 10 3384, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f788 : bv 32 := 0x02154703.
Lemma F_4f788 : fetch_word AsanUbsan.M.loaded_segments (0x4f788 : word) = Some W_4f788.
Proof. vm_refl. Qed.
Lemma D_4f788 : decode_any W_4f788 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f78c : bv 32 := 0x008ab4a3.
Lemma F_4f78c : fetch_word AsanUbsan.M.loaded_segments (0x4f78c : word) = Some W_4f78c.
Proof. vm_refl. Qed.
Lemma D_4f78c : decode_any W_4f78c = Some (Store SZ8 21 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f790 : bv 32 := 0x80040513.
Lemma F_4f790 : fetch_word AsanUbsan.M.loaded_segments (0x4f790 : word) = Some W_4f790.
Proof. vm_refl. Qed.
Lemma D_4f790 : decode_any W_4f790 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f794 : bv 32 := 0xfb050513.
Lemma F_4f794 : fetch_word AsanUbsan.M.loaded_segments (0x4f794 : word) = Some W_4f794.
Proof. vm_refl. Qed.
Lemma D_4f794 : decode_any W_4f794 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f798 : bv 32 := 0x0ff00793.
Lemma F_4f798 : fetch_word AsanUbsan.M.loaded_segments (0x4f798 : word) = Some W_4f798.
Proof. vm_refl. Qed.
Lemma D_4f798 : decode_any W_4f798 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f79c : bv 32 := 0x00040613.
Lemma F_4f79c : fetch_word AsanUbsan.M.loaded_segments (0x4f79c : word) = Some W_4f79c.
Proof. vm_refl. Qed.
Lemma D_4f79c : decode_any W_4f79c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f7a0 : bv 32 := 0x00000693.
Lemma F_4f7a0 : fetch_word AsanUbsan.M.loaded_segments (0x4f7a0 : word) = Some W_4f7a0.
Proof. vm_refl. Qed.
Lemma D_4f7a0 : decode_any W_4f7a0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f7a4 : bv 32 := 0x059180ef.
Lemma F_4f7a4 : fetch_word AsanUbsan.M.loaded_segments (0x4f7a4 : word) = Some W_4f7a4.
Proof. vm_refl. Qed.
Lemma D_4f7a4 : decode_any W_4f7a4 = Some (Jal 1 100440, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f7a8 : bv 32 := 0x80040613.
Lemma F_4f7a8 : fetch_word AsanUbsan.M.loaded_segments (0x4f7a8 : word) = Some W_4f7a8.
Proof. vm_refl. Qed.
Lemma D_4f7a8 : decode_any W_4f7a8 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f7ac : bv 32 := 0xfb060613.
Lemma F_4f7ac : fetch_word AsanUbsan.M.loaded_segments (0x4f7ac : word) = Some W_4f7ac.
Proof. vm_refl. Qed.
Lemma D_4f7ac : decode_any W_4f7ac = Some (OpImm ALU_ADD 12 12 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f7b0 : bv 32 := 0x00090513.
Lemma F_4f7b0 : fetch_word AsanUbsan.M.loaded_segments (0x4f7b0 : word) = Some W_4f7b0.
Proof. vm_refl. Qed.
Lemma D_4f7b0 : decode_any W_4f7b0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f7b4 : bv 32 := 0x00048593.
Lemma F_4f7b4 : fetch_word AsanUbsan.M.loaded_segments (0x4f7b4 : word) = Some W_4f7b4.
Proof. vm_refl. Qed.
Lemma D_4f7b4 : decode_any W_4f7b4 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f7b8 : bv 32 := 0x5fc150ef.
Lemma F_4f7b8 : fetch_word AsanUbsan.M.loaded_segments (0x4f7b8 : word) = Some W_4f7b8.
Proof. vm_refl. Qed.
Lemma D_4f7b8 : decode_any W_4f7b8 = Some (Jal 1 87548, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f7bc : bv 32 := 0x00098513.
Lemma F_4f7bc : fetch_word AsanUbsan.M.loaded_segments (0x4f7bc : word) = Some W_4f7bc.
Proof. vm_refl. Qed.
Lemma D_4f7bc : decode_any W_4f7bc = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f7c0 : bv 32 := 0xfbf48593.
Lemma F_4f7c0 : fetch_word AsanUbsan.M.loaded_segments (0x4f7c0 : word) = Some W_4f7c0.
Proof. vm_refl. Qed.
Lemma D_4f7c0 : decode_any W_4f7c0 = Some (OpImm ALU_ADD 11 9 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f7c4 : bv 32 := 0xfbf00613.
Lemma F_4f7c4 : fetch_word AsanUbsan.M.loaded_segments (0x4f7c4 : word) = Some W_4f7c4.
Proof. vm_refl. Qed.
Lemma D_4f7c4 : decode_any W_4f7c4 = Some (OpImm ALU_ADD 12 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f7c8 : bv 32 := 0xecb66ee3.
Lemma F_4f7c8 : fetch_word AsanUbsan.M.loaded_segments (0x4f7c8 : word) = Some W_4f7c8.
Proof. vm_refl. Qed.
Lemma D_4f7c8 : decode_any W_4f7c8 = Some (Branch BC_LTU 12 11 7900, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f7cc : bv 32 := 0x02049e63.
Lemma F_4f7cc : fetch_word AsanUbsan.M.loaded_segments (0x4f7cc : word) = Some W_4f7cc.
Proof. vm_refl. Qed.
Lemma D_4f7cc : decode_any W_4f7cc = Some (Branch BC_NE 9 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f7d0 : bv 32 := 0xf11ff06f.
Lemma F_4f7d0 : fetch_word AsanUbsan.M.loaded_segments (0x4f7d0 : word) = Some W_4f7d0.
Proof. vm_refl. Qed.
Lemma D_4f7d0 : decode_any W_4f7d0 = Some (Jal 0 2096912, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f7d4 : bv 32 := 0x00060703.
Lemma F_4f7d4 : fetch_word AsanUbsan.M.loaded_segments (0x4f7d4 : word) = Some W_4f7d4.
Proof. vm_refl. Qed.
Lemma D_4f7d4 : decode_any W_4f7d4 = Some (Load SZ1 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f7d8 : bv 32 := 0x0076f693.
Lemma F_4f7d8 : fetch_word AsanUbsan.M.loaded_segments (0x4f7d8 : word) = Some W_4f7d8.
Proof. vm_refl. Qed.
Lemma D_4f7d8 : decode_any W_4f7d8 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f7dc : bv 32 := 0x00e037b3.
Lemma F_4f7dc : fetch_word AsanUbsan.M.loaded_segments (0x4f7dc : word) = Some W_4f7dc.
Proof. vm_refl. Qed.
Lemma D_4f7dc : decode_any W_4f7dc = Some (Op ALU_SLTU 15 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f7e0 : bv 32 := 0x00e6a6b3.
Lemma F_4f7e0 : fetch_word AsanUbsan.M.loaded_segments (0x4f7e0 : word) = Some W_4f7e0.
Proof. vm_refl. Qed.
Lemma D_4f7e0 : decode_any W_4f7e0 = Some (Op ALU_SLT 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f7e4 : bv 32 := 0x0016c693.
Lemma F_4f7e4 : fetch_word AsanUbsan.M.loaded_segments (0x4f7e4 : word) = Some W_4f7e4.
Proof. vm_refl. Qed.
Lemma D_4f7e4 : decode_any W_4f7e4 = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f7e8 : bv 32 := 0x00d7f6b3.
Lemma F_4f7e8 : fetch_word AsanUbsan.M.loaded_segments (0x4f7e8 : word) = Some W_4f7e8.
Proof. vm_refl. Qed.
Lemma D_4f7e8 : decode_any W_4f7e8 = Some (Op ALU_AND 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f7ec : bv 32 := 0x00c5fa63.
Lemma F_4f7ec : fetch_word AsanUbsan.M.loaded_segments (0x4f7ec : word) = Some W_4f7ec.
Proof. vm_refl. Qed.
Lemma D_4f7ec : decode_any W_4f7ec = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f7f0 : bv 32 := 0x0005c703.
Lemma F_4f7f0 : fetch_word AsanUbsan.M.loaded_segments (0x4f7f0 : word) = Some W_4f7f0.
Proof. vm_refl. Qed.
Lemma D_4f7f0 : decode_any W_4f7f0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f7f4 : bv 32 := 0x00158593.
Lemma F_4f7f4 : fetch_word AsanUbsan.M.loaded_segments (0x4f7f4 : word) = Some W_4f7f4.
Proof. vm_refl. Qed.
Lemma D_4f7f4 : decode_any W_4f7f4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f7f8 : bv 32 := 0x00d766b3.
Lemma F_4f7f8 : fetch_word AsanUbsan.M.loaded_segments (0x4f7f8 : word) = Some W_4f7f8.
Proof. vm_refl. Qed.
Lemma D_4f7f8 : decode_any W_4f7f8 = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f7fc : bv 32 := 0xfec59ae3.
Lemma F_4f7fc : fetch_word AsanUbsan.M.loaded_segments (0x4f7fc : word) = Some W_4f7fc.
Proof. vm_refl. Qed.
Lemma D_4f7fc : decode_any W_4f7fc = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f800 : bv 32 := 0x0ff6f593.
Lemma F_4f800 : fetch_word AsanUbsan.M.loaded_segments (0x4f800 : word) = Some W_4f800.
Proof. vm_refl. Qed.
Lemma D_4f800 : decode_any W_4f800 = Some (OpImm ALU_AND 11 13 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f804 : bv 32 := 0xec058ee3.
Lemma F_4f804 : fetch_word AsanUbsan.M.loaded_segments (0x4f804 : word) = Some W_4f804.
Proof. vm_refl. Qed.
Lemma D_4f804 : decode_any W_4f804 = Some (Branch BC_EQ 11 0 7900, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f808 : bv 32 := 0x00050a93.
Lemma F_4f808 : fetch_word AsanUbsan.M.loaded_segments (0x4f808 : word) = Some W_4f808.
Proof. vm_refl. Qed.
Lemma D_4f808 : decode_any W_4f808 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f80c : bv 32 := 0x00090513.
Lemma F_4f80c : fetch_word AsanUbsan.M.loaded_segments (0x4f80c : word) = Some W_4f80c.
Proof. vm_refl. Qed.
Lemma D_4f80c : decode_any W_4f80c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f810 : bv 32 := 0x00048593.
Lemma F_4f810 : fetch_word AsanUbsan.M.loaded_segments (0x4f810 : word) = Some W_4f810.
Proof. vm_refl. Qed.
Lemma D_4f810 : decode_any W_4f810 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f814 : bv 32 := 0x36c120ef.
Lemma F_4f814 : fetch_word AsanUbsan.M.loaded_segments (0x4f814 : word) = Some W_4f814.
Proof. vm_refl. Qed.
Lemma D_4f814 : decode_any W_4f814 = Some (Jal 1 74604, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f818 : bv 32 := 0x00050913.
Lemma F_4f818 : fetch_word AsanUbsan.M.loaded_segments (0x4f818 : word) = Some W_4f818.
Proof. vm_refl. Qed.
Lemma D_4f818 : decode_any W_4f818 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f81c : bv 32 := 0x000a8513.
Lemma F_4f81c : fetch_word AsanUbsan.M.loaded_segments (0x4f81c : word) = Some W_4f81c.
Proof. vm_refl. Qed.
Lemma D_4f81c : decode_any W_4f81c = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f820 : bv 32 := 0xec0900e3.
Lemma F_4f820 : fetch_word AsanUbsan.M.loaded_segments (0x4f820 : word) = Some W_4f820.
Proof. vm_refl. Qed.
Lemma D_4f820 : decode_any W_4f820 = Some (Branch BC_EQ 18 0 7872, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f824 : bv 32 := 0xfffcc517.
Lemma F_4f824 : fetch_word AsanUbsan.M.loaded_segments (0x4f824 : word) = Some W_4f824.
Proof. vm_refl. Qed.
Lemma D_4f824 : decode_any W_4f824 = Some (Auipc 10 1048524, 4%Z).
Proof. vm_refl. Qed.

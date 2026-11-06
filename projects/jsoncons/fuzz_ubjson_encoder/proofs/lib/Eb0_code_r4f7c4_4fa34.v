(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_666c8 : bv 32 := 0x81010113.
Lemma F_666c8 : fetch_word AsanUbsan.M.loaded_segments (0x66718 : word) = Some W_666c8.
Proof. vm_refl. Qed.
Lemma D_666c8 : decode_any W_666c8 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_666cc : bv 32 := 0x7e113423.
Lemma F_666cc : fetch_word AsanUbsan.M.loaded_segments (0x6671c : word) = Some W_666cc.
Proof. vm_refl. Qed.
Lemma D_666cc : decode_any W_666cc = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_666d0 : bv 32 := 0x7e813023.
Lemma F_666d0 : fetch_word AsanUbsan.M.loaded_segments (0x66720 : word) = Some W_666d0.
Proof. vm_refl. Qed.
Lemma D_666d0 : decode_any W_666d0 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_666d4 : bv 32 := 0x7c913c23.
Lemma F_666d4 : fetch_word AsanUbsan.M.loaded_segments (0x66724 : word) = Some W_666d4.
Proof. vm_refl. Qed.
Lemma D_666d4 : decode_any W_666d4 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_666d8 : bv 32 := 0x7d213823.
Lemma F_666d8 : fetch_word AsanUbsan.M.loaded_segments (0x66728 : word) = Some W_666d8.
Proof. vm_refl. Qed.
Lemma D_666d8 : decode_any W_666d8 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_666dc : bv 32 := 0x7d313423.
Lemma F_666dc : fetch_word AsanUbsan.M.loaded_segments (0x6672c : word) = Some W_666dc.
Proof. vm_refl. Qed.
Lemma D_666dc : decode_any W_666dc = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_666e0 : bv 32 := 0x7d413023.
Lemma F_666e0 : fetch_word AsanUbsan.M.loaded_segments (0x66730 : word) = Some W_666e0.
Proof. vm_refl. Qed.
Lemma D_666e0 : decode_any W_666e0 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_666e4 : bv 32 := 0x7f010413.
Lemma F_666e4 : fetch_word AsanUbsan.M.loaded_segments (0x66734 : word) = Some W_666e4.
Proof. vm_refl. Qed.
Lemma D_666e4 : decode_any W_666e4 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_666e8 : bv 32 := 0xfa010113.
Lemma F_666e8 : fetch_word AsanUbsan.M.loaded_segments (0x66738 : word) = Some W_666e8.
Proof. vm_refl. Qed.
Lemma D_666e8 : decode_any W_666e8 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_666ec : bv 32 := 0x00060913.
Lemma F_666ec : fetch_word AsanUbsan.M.loaded_segments (0x6673c : word) = Some W_666ec.
Proof. vm_refl. Qed.
Lemma D_666ec : decode_any W_666ec = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_666f0 : bv 32 := 0x00058493.
Lemma F_666f0 : fetch_word AsanUbsan.M.loaded_segments (0x66740 : word) = Some W_666f0.
Proof. vm_refl. Qed.
Lemma D_666f0 : decode_any W_666f0 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_666f4 : bv 32 := 0x00050993.
Lemma F_666f4 : fetch_word AsanUbsan.M.loaded_segments (0x66744 : word) = Some W_666f4.
Proof. vm_refl. Qed.
Lemma D_666f4 : decode_any W_666f4 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_666f8 : bv 32 := 0x3491b0ef.
Lemma F_666f8 : fetch_word AsanUbsan.M.loaded_segments (0x66748 : word) = Some W_666f8.
Proof. vm_refl. Qed.
Lemma D_666f8 : decode_any W_666f8 = Some (Jal 1 113480, 4%Z).
Proof. vm_refl. Qed.

Definition W_666fc : bv 32 := 0x000d9597.
Lemma F_666fc : fetch_word AsanUbsan.M.loaded_segments (0x6674c : word) = Some W_666fc.
Proof. vm_refl. Qed.
Lemma D_666fc : decode_any W_666fc = Some (Auipc 11 217, 4%Z).
Proof. vm_refl. Qed.

Definition W_66700 : bv 32 := 0xfd45b683.
Lemma F_66700 : fetch_word AsanUbsan.M.loaded_segments (0x66750 : word) = Some W_66700.
Proof. vm_refl. Qed.
Lemma D_66700 : decode_any W_66700 = Some (Load SZ8 true 13 11 4052, 4%Z).
Proof. vm_refl. Qed.

Definition W_66704 : bv 32 := 0x00050a13.
Lemma F_66704 : fetch_word AsanUbsan.M.loaded_segments (0x66754 : word) = Some W_66704.
Proof. vm_refl. Qed.
Lemma D_66704 : decode_any W_66704 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66708 : bv 32 := 0x00098513.
Lemma F_66708 : fetch_word AsanUbsan.M.loaded_segments (0x66758 : word) = Some W_66708.
Proof. vm_refl. Qed.
Lemma D_66708 : decode_any W_66708 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6670c : bv 32 := 0x00048593.
Lemma F_6670c : fetch_word AsanUbsan.M.loaded_segments (0x6675c : word) = Some W_6670c.
Proof. vm_refl. Qed.
Lemma D_6670c : decode_any W_6670c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66710 : bv 32 := 0x00090613.
Lemma F_66710 : fetch_word AsanUbsan.M.loaded_segments (0x66760 : word) = Some W_66710.
Proof. vm_refl. Qed.
Lemma D_66710 : decode_any W_66710 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66714 : bv 32 := 0x000680e7.
Lemma F_66714 : fetch_word AsanUbsan.M.loaded_segments (0x66764 : word) = Some W_66714.
Proof. vm_refl. Qed.
Lemma D_66714 : decode_any W_66714 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66718 : bv 32 := 0x060a0063.
Lemma F_66718 : fetch_word AsanUbsan.M.loaded_segments (0x66768 : word) = Some W_66718.
Proof. vm_refl. Qed.
Lemma D_66718 : decode_any W_66718 = Some (Branch BC_EQ 20 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_6671c : bv 32 := 0x04a05e63.
Lemma F_6671c : fetch_word AsanUbsan.M.loaded_segments (0x6676c : word) = Some W_6671c.
Proof. vm_refl. Qed.
Lemma D_6671c : decode_any W_6671c = Some (Branch BC_GE 0 10 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_66720 : bv 32 := 0xfff4c593.
Lemma F_66720 : fetch_word AsanUbsan.M.loaded_segments (0x66770 : word) = Some W_66720.
Proof. vm_refl. Qed.
Lemma D_66720 : decode_any W_66720 = Some (OpImm ALU_XOR 11 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_66724 : bv 32 := 0x80040a13.
Lemma F_66724 : fetch_word AsanUbsan.M.loaded_segments (0x66774 : word) = Some W_66724.
Proof. vm_refl. Qed.
Lemma D_66724 : decode_any W_66724 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_66728 : bv 32 := 0xfb8a0a13.
Lemma F_66728 : fetch_word AsanUbsan.M.loaded_segments (0x66778 : word) = Some W_66728.
Proof. vm_refl. Qed.
Lemma D_66728 : decode_any W_66728 = Some (OpImm ALU_ADD 20 20 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_6672c : bv 32 := 0x06a5e863.
Lemma F_6672c : fetch_word AsanUbsan.M.loaded_segments (0x6677c : word) = Some W_6672c.
Proof. vm_refl. Qed.
Lemma D_6672c : decode_any W_6672c = Some (Branch BC_LTU 11 10 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_66730 : bv 32 := 0xfbf50593.
Lemma F_66730 : fetch_word AsanUbsan.M.loaded_segments (0x66780 : word) = Some W_66730.
Proof. vm_refl. Qed.
Lemma D_66730 : decode_any W_66730 = Some (OpImm ALU_ADD 11 10 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_66734 : bv 32 := 0xfc000613.
Lemma F_66734 : fetch_word AsanUbsan.M.loaded_segments (0x66784 : word) = Some W_66734.
Proof. vm_refl. Qed.
Lemma D_66734 : decode_any W_66734 = Some (OpImm ALU_ADD 12 0 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_66738 : bv 32 := 0x0cc5ee63.
Lemma F_66738 : fetch_word AsanUbsan.M.loaded_segments (0x66788 : word) = Some W_66738.
Proof. vm_refl. Qed.
Lemma D_66738 : decode_any W_66738 = Some (Branch BC_LTU 11 12 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_6673c : bv 32 := 0x000d7597.
Lemma F_6673c : fetch_word AsanUbsan.M.loaded_segments (0x6678c : word) = Some W_6673c.
Proof. vm_refl. Qed.
Lemma D_6673c : decode_any W_6673c = Some (Auipc 11 215, 4%Z).
Proof. vm_refl. Qed.

Definition W_66740 : bv 32 := 0x13c5b583.
Lemma F_66740 : fetch_word AsanUbsan.M.loaded_segments (0x66790 : word) = Some W_66740.
Proof. vm_refl. Qed.
Lemma D_66740 : decode_any W_66740 = Some (Load SZ8 true 11 11 316, 4%Z).
Proof. vm_refl. Qed.

Definition W_66744 : bv 32 := 0x00a486b3.
Lemma F_66744 : fetch_word AsanUbsan.M.loaded_segments (0x66794 : word) = Some W_66744.
Proof. vm_refl. Qed.
Lemma D_66744 : decode_any W_66744 = Some (Op ALU_ADD 13 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_66748 : bv 32 := 0x0005b603.
Lemma F_66748 : fetch_word AsanUbsan.M.loaded_segments (0x66798 : word) = Some W_66748.
Proof. vm_refl. Qed.
Lemma D_66748 : decode_any W_66748 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6674c : bv 32 := 0x0034d593.
Lemma F_6674c : fetch_word AsanUbsan.M.loaded_segments (0x6679c : word) = Some W_6674c.
Proof. vm_refl. Qed.
Lemma D_6674c : decode_any W_6674c = Some (ShiftImm ALU_SRL 11 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_66750 : bv 32 := 0xfff68693.
Lemma F_66750 : fetch_word AsanUbsan.M.loaded_segments (0x667a0 : word) = Some W_66750.
Proof. vm_refl. Qed.
Lemma D_66750 : decode_any W_66750 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_66754 : bv 32 := 0x0036d713.
Lemma F_66754 : fetch_word AsanUbsan.M.loaded_segments (0x667a4 : word) = Some W_66754.
Proof. vm_refl. Qed.
Lemma D_66754 : decode_any W_66754 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_66758 : bv 32 := 0x00b605b3.
Lemma F_66758 : fetch_word AsanUbsan.M.loaded_segments (0x667a8 : word) = Some W_66758.
Proof. vm_refl. Qed.
Lemma D_66758 : decode_any W_66758 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6675c : bv 32 := 0x00e60633.
Lemma F_6675c : fetch_word AsanUbsan.M.loaded_segments (0x667ac : word) = Some W_6675c.
Proof. vm_refl. Qed.
Lemma D_6675c : decode_any W_6675c = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_66760 : bv 32 := 0xff85f713.
Lemma F_66760 : fetch_word AsanUbsan.M.loaded_segments (0x667b0 : word) = Some W_66760.
Proof. vm_refl. Qed.
Lemma D_66760 : decode_any W_66760 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_66764 : bv 32 := 0xff867793.
Lemma F_66764 : fetch_word AsanUbsan.M.loaded_segments (0x667b4 : word) = Some W_66764.
Proof. vm_refl. Qed.
Lemma D_66764 : decode_any W_66764 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_66768 : bv 32 := 0x00073703.
Lemma F_66768 : fetch_word AsanUbsan.M.loaded_segments (0x667b8 : word) = Some W_66768.
Proof. vm_refl. Qed.
Lemma D_66768 : decode_any W_66768 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6676c : bv 32 := 0x0007b783.
Lemma F_6676c : fetch_word AsanUbsan.M.loaded_segments (0x667bc : word) = Some W_6676c.
Proof. vm_refl. Qed.
Lemma D_6676c : decode_any W_6676c = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66770 : bv 32 := 0x00e7e733.
Lemma F_66770 : fetch_word AsanUbsan.M.loaded_segments (0x667c0 : word) = Some W_66770.
Proof. vm_refl. Qed.
Lemma D_66770 : decode_any W_66770 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_66774 : bv 32 := 0x14071663.
Lemma F_66774 : fetch_word AsanUbsan.M.loaded_segments (0x667c4 : word) = Some W_66774.
Proof. vm_refl. Qed.
Lemma D_66774 : decode_any W_66774 = Some (Branch BC_NE 14 0 332, 4%Z).
Proof. vm_refl. Qed.

Definition W_66778 : bv 32 := 0x06010113.
Lemma F_66778 : fetch_word AsanUbsan.M.loaded_segments (0x667c8 : word) = Some W_66778.
Proof. vm_refl. Qed.
Lemma D_66778 : decode_any W_66778 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_6677c : bv 32 := 0x7e813083.
Lemma F_6677c : fetch_word AsanUbsan.M.loaded_segments (0x667cc : word) = Some W_6677c.
Proof. vm_refl. Qed.
Lemma D_6677c : decode_any W_6677c = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_66780 : bv 32 := 0x7e013403.
Lemma F_66780 : fetch_word AsanUbsan.M.loaded_segments (0x667d0 : word) = Some W_66780.
Proof. vm_refl. Qed.
Lemma D_66780 : decode_any W_66780 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_66784 : bv 32 := 0x7d813483.
Lemma F_66784 : fetch_word AsanUbsan.M.loaded_segments (0x667d4 : word) = Some W_66784.
Proof. vm_refl. Qed.
Lemma D_66784 : decode_any W_66784 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_66788 : bv 32 := 0x7d013903.
Lemma F_66788 : fetch_word AsanUbsan.M.loaded_segments (0x667d8 : word) = Some W_66788.
Proof. vm_refl. Qed.
Lemma D_66788 : decode_any W_66788 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_6678c : bv 32 := 0x7c813983.
Lemma F_6678c : fetch_word AsanUbsan.M.loaded_segments (0x667dc : word) = Some W_6678c.
Proof. vm_refl. Qed.
Lemma D_6678c : decode_any W_6678c = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_66790 : bv 32 := 0x7c013a03.
Lemma F_66790 : fetch_word AsanUbsan.M.loaded_segments (0x667e0 : word) = Some W_66790.
Proof. vm_refl. Qed.
Lemma D_66790 : decode_any W_66790 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_66794 : bv 32 := 0x7f010113.
Lemma F_66794 : fetch_word AsanUbsan.M.loaded_segments (0x667e4 : word) = Some W_66794.
Proof. vm_refl. Qed.
Lemma D_66794 : decode_any W_66794 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_66798 : bv 32 := 0x00008067.
Lemma F_66798 : fetch_word AsanUbsan.M.loaded_segments (0x667e8 : word) = Some W_66798.
Proof. vm_refl. Qed.
Lemma D_66798 : decode_any W_66798 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66814 : bv 32 := 0x00050913.
Lemma F_66814 : fetch_word AsanUbsan.M.loaded_segments (0x66864 : word) = Some W_66814.
Proof. vm_refl. Qed.
Lemma D_66814 : decode_any W_66814 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66818 : bv 32 := 0x00048513.
Lemma F_66818 : fetch_word AsanUbsan.M.loaded_segments (0x66868 : word) = Some W_66818.
Proof. vm_refl. Qed.
Lemma D_66818 : decode_any W_66818 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6681c : bv 32 := 0x00090593.
Lemma F_6681c : fetch_word AsanUbsan.M.loaded_segments (0x6686c : word) = Some W_6681c.
Proof. vm_refl. Qed.
Lemma D_6681c : decode_any W_6681c = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66820 : bv 32 := 0x5fd150ef.
Lemma F_66820 : fetch_word AsanUbsan.M.loaded_segments (0x66870 : word) = Some W_66820.
Proof. vm_refl. Qed.
Lemma D_66820 : decode_any W_66820 = Some (Jal 1 89596, 4%Z).
Proof. vm_refl. Qed.

Definition W_66824 : bv 32 := 0x00050493.
Lemma F_66824 : fetch_word AsanUbsan.M.loaded_segments (0x66874 : word) = Some W_66824.
Proof. vm_refl. Qed.
Lemma D_66824 : decode_any W_66824 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66828 : bv 32 := 0x00090513.
Lemma F_66828 : fetch_word AsanUbsan.M.loaded_segments (0x66878 : word) = Some W_66828.
Proof. vm_refl. Qed.
Lemma D_66828 : decode_any W_66828 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6682c : bv 32 := 0xf40486e3.
Lemma F_6682c : fetch_word AsanUbsan.M.loaded_segments (0x6687c : word) = Some W_6682c.
Proof. vm_refl. Qed.
Lemma D_6682c : decode_any W_6682c = Some (Branch BC_EQ 9 0 8012, 4%Z).
Proof. vm_refl. Qed.

Definition W_668c0 : bv 32 := 0x00060703.
Lemma F_668c0 : fetch_word AsanUbsan.M.loaded_segments (0x66910 : word) = Some W_668c0.
Proof. vm_refl. Qed.
Lemma D_668c0 : decode_any W_668c0 = Some (Load SZ1 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_668c4 : bv 32 := 0x0076f693.
Lemma F_668c4 : fetch_word AsanUbsan.M.loaded_segments (0x66914 : word) = Some W_668c4.
Proof. vm_refl. Qed.
Lemma D_668c4 : decode_any W_668c4 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_668c8 : bv 32 := 0x00e037b3.
Lemma F_668c8 : fetch_word AsanUbsan.M.loaded_segments (0x66918 : word) = Some W_668c8.
Proof. vm_refl. Qed.
Lemma D_668c8 : decode_any W_668c8 = Some (Op ALU_SLTU 15 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_668cc : bv 32 := 0x00e6a6b3.
Lemma F_668cc : fetch_word AsanUbsan.M.loaded_segments (0x6691c : word) = Some W_668cc.
Proof. vm_refl. Qed.
Lemma D_668cc : decode_any W_668cc = Some (Op ALU_SLT 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_668d0 : bv 32 := 0x0016c693.
Lemma F_668d0 : fetch_word AsanUbsan.M.loaded_segments (0x66920 : word) = Some W_668d0.
Proof. vm_refl. Qed.
Lemma D_668d0 : decode_any W_668d0 = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_668d4 : bv 32 := 0x00d7f6b3.
Lemma F_668d4 : fetch_word AsanUbsan.M.loaded_segments (0x66924 : word) = Some W_668d4.
Proof. vm_refl. Qed.
Lemma D_668d4 : decode_any W_668d4 = Some (Op ALU_AND 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_668d8 : bv 32 := 0x00c5fa63.
Lemma F_668d8 : fetch_word AsanUbsan.M.loaded_segments (0x66928 : word) = Some W_668d8.
Proof. vm_refl. Qed.
Lemma D_668d8 : decode_any W_668d8 = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_668dc : bv 32 := 0x0005c703.
Lemma F_668dc : fetch_word AsanUbsan.M.loaded_segments (0x6692c : word) = Some W_668dc.
Proof. vm_refl. Qed.
Lemma D_668dc : decode_any W_668dc = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_668e0 : bv 32 := 0x00158593.
Lemma F_668e0 : fetch_word AsanUbsan.M.loaded_segments (0x66930 : word) = Some W_668e0.
Proof. vm_refl. Qed.
Lemma D_668e0 : decode_any W_668e0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_668e4 : bv 32 := 0x00d766b3.
Lemma F_668e4 : fetch_word AsanUbsan.M.loaded_segments (0x66934 : word) = Some W_668e4.
Proof. vm_refl. Qed.
Lemma D_668e4 : decode_any W_668e4 = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_668e8 : bv 32 := 0xfec59ae3.
Lemma F_668e8 : fetch_word AsanUbsan.M.loaded_segments (0x66938 : word) = Some W_668e8.
Proof. vm_refl. Qed.
Lemma D_668e8 : decode_any W_668e8 = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_668ec : bv 32 := 0x0ff6f593.
Lemma F_668ec : fetch_word AsanUbsan.M.loaded_segments (0x6693c : word) = Some W_668ec.
Proof. vm_refl. Qed.
Lemma D_668ec : decode_any W_668ec = Some (OpImm ALU_AND 11 13 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_668f0 : bv 32 := 0xe80584e3.
Lemma F_668f0 : fetch_word AsanUbsan.M.loaded_segments (0x66940 : word) = Some W_668f0.
Proof. vm_refl. Qed.
Lemma D_668f0 : decode_any W_668f0 = Some (Branch BC_EQ 11 0 7816, 4%Z).
Proof. vm_refl. Qed.

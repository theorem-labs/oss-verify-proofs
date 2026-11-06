(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require CTabKA.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
Open Scope bv_scope.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Definition W_5d878 : bv 32 := 0xfe010113.
Lemma F_5d878 : CTabKA.F 0x5d878 W_5d878.
Proof. vm_refl. Qed.
Lemma D_5d878 : CTabKA.D W_5d878 (OpImm ALU_ADD 2 2 4064).
Proof. vm_refl. Qed.
Definition W_5d87c : bv 32 := 0x00113c23.
Lemma F_5d87c : CTabKA.F 0x5d87c W_5d87c.
Proof. vm_refl. Qed.
Lemma D_5d87c : CTabKA.D W_5d87c (Store SZ8 2 1 24).
Proof. vm_refl. Qed.
Definition W_5d880 : bv 32 := 0x00813823.
Lemma F_5d880 : CTabKA.F 0x5d880 W_5d880.
Proof. vm_refl. Qed.
Lemma D_5d880 : CTabKA.D W_5d880 (Store SZ8 2 8 16).
Proof. vm_refl. Qed.
Definition W_5d884 : bv 32 := 0x00913423.
Lemma F_5d884 : CTabKA.F 0x5d884 W_5d884.
Proof. vm_refl. Qed.
Lemma D_5d884 : CTabKA.D W_5d884 (Store SZ8 2 9 8).
Proof. vm_refl. Qed.
Definition W_5d888 : bv 32 := 0x01213023.
Lemma F_5d888 : CTabKA.F 0x5d888 W_5d888.
Proof. vm_refl. Qed.
Lemma D_5d888 : CTabKA.D W_5d888 (Store SZ8 2 18 0).
Proof. vm_refl. Qed.
Definition W_5d88c : bv 32 := 0x02010413.
Lemma F_5d88c : CTabKA.F 0x5d88c W_5d88c.
Proof. vm_refl. Qed.
Lemma D_5d88c : CTabKA.D W_5d88c (OpImm ALU_ADD 8 2 32).
Proof. vm_refl. Qed.
Definition W_5d890 : bv 32 := 0x000d6517.
Lemma F_5d890 : CTabKA.F 0x5d890 W_5d890.
Proof. vm_refl. Qed.
Lemma D_5d890 : CTabKA.D W_5d890 (Auipc 10 214).
Proof. vm_refl. Qed.
Definition W_5d894 : bv 32 := 0xba050513.
Lemma F_5d894 : CTabKA.F 0x5d894 W_5d894.
Proof. vm_refl. Qed.
Lemma D_5d894 : CTabKA.D W_5d894 (OpImm ALU_ADD 10 10 2976).
Proof. vm_refl. Qed.
Definition W_5d898 : bv 32 := 0x200050ef.
Lemma F_5d898 : CTabKA.F 0x5d898 W_5d898.
Proof. vm_refl. Qed.
Lemma D_5d898 : CTabKA.D W_5d898 (Jal 1 20992).
Proof. vm_refl. Qed.
Definition W_5d89c : bv 32 := 0x00053483.
Lemma F_5d89c : CTabKA.F 0x5d89c W_5d89c.
Proof. vm_refl. Qed.
Lemma D_5d89c : CTabKA.D W_5d89c (Load SZ8 true 9 10 0).
Proof. vm_refl. Qed.
Definition W_5d8a0 : bv 32 := 0x08048863.
Lemma F_5d8a0 : CTabKA.F 0x5d8a0 W_5d8a0.
Proof. vm_refl. Qed.
Lemma D_5d8a0 : CTabKA.D W_5d8a0 (Branch BC_EQ 9 0 144).
Proof. vm_refl. Qed.
Definition W_5d8a4 : bv 32 := 0x0604c503.
Lemma F_5d8a4 : CTabKA.F 0x5d8a4 W_5d8a4.
Proof. vm_refl. Qed.
Lemma D_5d8a4 : CTabKA.D W_5d8a4 (Load SZ1 false 10 9 96).
Proof. vm_refl. Qed.
Definition W_5d8a8 : bv 32 := 0x0584b903.
Lemma F_5d8a8 : CTabKA.F 0x5d8a8 W_5d8a8.
Proof. vm_refl. Qed.
Lemma D_5d8a8 : CTabKA.D W_5d8a8 (Load SZ8 true 18 9 88).
Proof. vm_refl. Qed.
Definition W_5d8ac : bv 32 := 0x00050863.
Lemma F_5d8ac : CTabKA.F 0x5d8ac W_5d8ac.
Proof. vm_refl. Qed.
Lemma D_5d8ac : CTabKA.D W_5d8ac (Branch BC_EQ 10 0 16).
Proof. vm_refl. Qed.
Definition W_5d8b0 : bv 32 := 0x00048513.
Lemma F_5d8b0 : CTabKA.F 0x5d8b0 W_5d8b0.
Proof. vm_refl. Qed.
Lemma D_5d8b0 : CTabKA.D W_5d8b0 (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_5d8b4 : bv 32 := 0x00040593.
Lemma F_5d8b4 : CTabKA.F 0x5d8b4 W_5d8b4.
Proof. vm_refl. Qed.
Lemma D_5d8b4 : CTabKA.D W_5d8b4 (OpImm ALU_ADD 11 8 0).
Proof. vm_refl. Qed.
Definition W_5d8b8 : bv 32 := 0xd28ff0ef.
Lemma F_5d8b8 : CTabKA.F 0x5d8b8 W_5d8b8.
Proof. vm_refl. Qed.
Lemma D_5d8b8 : CTabKA.D W_5d8b8 (Jal 1 2094376).
Proof. vm_refl. Qed.
Definition W_5d8bc : bv 32 := 0xff690593.
Lemma F_5d8bc : CTabKA.F 0x5d8bc W_5d8bc.
Proof. vm_refl. Qed.
Lemma D_5d8bc : CTabKA.D W_5d8bc (OpImm ALU_ADD 11 18 4086).
Proof. vm_refl. Qed.
Definition W_5d8c0 : bv 32 := 0x00100513.
Lemma F_5d8c0 : CTabKA.F 0x5d8c0 W_5d8c0.
Proof. vm_refl. Qed.
Lemma D_5d8c0 : CTabKA.D W_5d8c0 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_5d8c4 : bv 32 := 0x00b51533.
Lemma F_5d8c4 : CTabKA.F 0x5d8c4 W_5d8c4.
Proof. vm_refl. Qed.
Lemma D_5d8c4 : CTabKA.D W_5d8c4 (Op ALU_SLL 10 10 11).
Proof. vm_refl. Qed.
Definition W_5d8c8 : bv 32 := 0x0005061b.
Lemma F_5d8c8 : CTabKA.F 0x5d8c8 W_5d8c8.
Proof. vm_refl. Qed.
Lemma D_5d8c8 : CTabKA.D W_5d8c8 (OpImm32 12 10 0).
Proof. vm_refl. Qed.
Definition W_5d8cc : bv 32 := 0x08c05263.
Lemma F_5d8cc : CTabKA.F 0x5d8cc W_5d8cc.
Proof. vm_refl. Qed.
Lemma D_5d8cc : CTabKA.D W_5d8cc (Branch BC_GE 0 12 132).
Proof. vm_refl. Qed.
Definition W_5d8d0 : bv 32 := 0x000016b7.
Lemma F_5d8d0 : CTabKA.F 0x5d8d0 W_5d8d0.
Proof. vm_refl. Qed.
Lemma D_5d8d0 : CTabKA.D W_5d8d0 (Lui 13 1).
Proof. vm_refl. Qed.
Definition W_5d8d4 : bv 32 := 0xff190613.
Lemma F_5d8d4 : CTabKA.F 0x5d8d4 W_5d8d4.
Proof. vm_refl. Qed.
Lemma D_5d8d4 : CTabKA.D W_5d8d4 (OpImm ALU_ADD 12 18 4081).
Proof. vm_refl. Qed.
Definition W_5d8d8 : bv 32 := 0x3c000713.
Lemma F_5d8d8 : CTabKA.F 0x5d8d8 W_5d8d8.
Proof. vm_refl. Qed.
Lemma D_5d8d8 : CTabKA.D W_5d8d8 (OpImm ALU_ADD 14 0 960).
Proof. vm_refl. Qed.
Definition W_5d8dc : bv 32 := 0xfff00793.
Lemma F_5d8dc : CTabKA.F 0x5d8dc W_5d8dc.
Proof. vm_refl. Qed.
Lemma D_5d8dc : CTabKA.D W_5d8dc (OpImm ALU_ADD 15 0 4095).
Proof. vm_refl. Qed.
Definition W_5d8e0 : bv 32 := 0x00c71733.
Lemma F_5d8e0 : CTabKA.F 0x5d8e0 W_5d8e0.
Proof. vm_refl. Qed.
Lemma D_5d8e0 : CTabKA.D W_5d8e0 (Op ALU_SLL 14 14 12).
Proof. vm_refl. Qed.
Definition W_5d8e4 : bv 32 := 0x0204b603.
Lemma F_5d8e4 : CTabKA.F 0x5d8e4 W_5d8e4.
Proof. vm_refl. Qed.
Lemma D_5d8e4 : CTabKA.D W_5d8e4 (Load SZ8 true 12 9 32).
Proof. vm_refl. Qed.
Definition W_5d8e8 : bv 32 := 0x00b797b3.
Lemma F_5d8e8 : CTabKA.F 0x5d8e8 W_5d8e8.
Proof. vm_refl. Qed.
Lemma D_5d8e8 : CTabKA.D W_5d8e8 (Op ALU_SLL 15 15 11).
Proof. vm_refl. Qed.
Definition W_5d8ec : bv 32 := 0xfff50813.
Lemma F_5d8ec : CTabKA.F 0x5d8ec W_5d8ec.
Proof. vm_refl. Qed.
Lemma D_5d8ec : CTabKA.D W_5d8ec (OpImm ALU_ADD 16 10 4095).
Proof. vm_refl. Qed.
Definition W_5d8f0 : bv 32 := 0x00d485b3.
Lemma F_5d8f0 : CTabKA.F 0x5d8f0 W_5d8f0.
Proof. vm_refl. Qed.
Lemma D_5d8f0 : CTabKA.D W_5d8f0 (Op ALU_ADD 11 9 13).
Proof. vm_refl. Qed.
Definition W_5d8f4 : bv 32 := 0x00e586b3.
Lemma F_5d8f4 : CTabKA.F 0x5d8f4 W_5d8f4.
Proof. vm_refl. Qed.
Lemma D_5d8f4 : CTabKA.D W_5d8f4 (Op ALU_ADD 13 11 14).
Proof. vm_refl. Qed.
Definition W_5d8f8 : bv 32 := 0xfff7c713.
Lemma F_5d8f8 : CTabKA.F 0x5d8f8 W_5d8f8.
Proof. vm_refl. Qed.
Lemma D_5d8f8 : CTabKA.D W_5d8f8 (OpImm ALU_XOR 14 15 4095).
Proof. vm_refl. Qed.
Definition W_5d8fc : bv 32 := 0x02081813.
Lemma F_5d8fc : CTabKA.F 0x5d8fc W_5d8fc.
Proof. vm_refl. Qed.
Lemma D_5d8fc : CTabKA.D W_5d8fc (ShiftImm ALU_SLL 16 16 32).
Proof. vm_refl. Qed.
Definition W_5d900 : bv 32 := 0x02085793.
Lemma F_5d900 : CTabKA.F 0x5d900 W_5d900.
Proof. vm_refl. Qed.
Lemma D_5d900 : CTabKA.D W_5d900 (ShiftImm ALU_SRL 15 16 32).
Proof. vm_refl. Qed.
Definition W_5d904 : bv 32 := 0x00f607b3.
Lemma F_5d904 : CTabKA.F 0x5d904 W_5d904.
Proof. vm_refl. Qed.
Lemma D_5d904 : CTabKA.D W_5d904 (Op ALU_ADD 15 12 15).
Proof. vm_refl. Qed.
Definition W_5d908 : bv 32 := 0x00178813.
Lemma F_5d908 : CTabKA.F 0x5d908 W_5d908.
Proof. vm_refl. Qed.
Lemma D_5d908 : CTabKA.D W_5d908 (OpImm ALU_ADD 16 15 1).
Proof. vm_refl. Qed.
Definition W_5d90c : bv 32 := 0x00e678b3.
Lemma F_5d90c : CTabKA.F 0x5d90c W_5d90c.
Proof. vm_refl. Qed.
Lemma D_5d90c : CTabKA.D W_5d90c (Op ALU_AND 17 12 14).
Proof. vm_refl. Qed.
Definition W_5d910 : bv 32 := 0x011687b3.
Lemma F_5d910 : CTabKA.F 0x5d910 W_5d910.
Proof. vm_refl. Qed.
Lemma D_5d910 : CTabKA.D W_5d910 (Op ALU_ADD 15 13 17).
Proof. vm_refl. Qed.
Definition W_5d914 : bv 32 := 0x0007c283.
Lemma F_5d914 : CTabKA.F 0x5d914 W_5d914.
Proof. vm_refl. Qed.
Lemma D_5d914 : CTabKA.D W_5d914 (Load SZ1 false 5 15 0).
Proof. vm_refl. Qed.
Definition W_5d918 : bv 32 := 0x06028663.
Lemma F_5d918 : CTabKA.F 0x5d918 W_5d918.
Proof. vm_refl. Qed.
Lemma D_5d918 : CTabKA.D W_5d918 (Branch BC_EQ 5 0 108).
Proof. vm_refl. Qed.
Definition W_5d91c : bv 32 := 0xfff5051b.
Lemma F_5d91c : CTabKA.F 0x5d91c W_5d91c.
Proof. vm_refl. Qed.
Lemma D_5d91c : CTabKA.D W_5d91c (OpImm32 10 10 4095).
Proof. vm_refl. Qed.
Definition W_5d920 : bv 32 := 0x00160613.
Lemma F_5d920 : CTabKA.F 0x5d920 W_5d920.
Proof. vm_refl. Qed.
Lemma D_5d920 : CTabKA.D W_5d920 (OpImm ALU_ADD 12 12 1).
Proof. vm_refl. Qed.
Definition W_5d924 : bv 32 := 0xfe0514e3.
Lemma F_5d924 : CTabKA.F 0x5d924 W_5d924.
Proof. vm_refl. Qed.
Lemma D_5d924 : CTabKA.D W_5d924 (Branch BC_NE 10 0 8168).
Proof. vm_refl. Qed.
Definition W_5d928 : bv 32 := 0x0304b023.
Lemma F_5d928 : CTabKA.F 0x5d928 W_5d928.
Proof. vm_refl. Qed.
Lemma D_5d928 : CTabKA.D W_5d928 (Store SZ8 9 16 32).
Proof. vm_refl. Qed.
Definition W_5d92c : bv 32 := 0x0400006f.
Lemma F_5d92c : CTabKA.F 0x5d92c W_5d92c.
Proof. vm_refl. Qed.
Lemma D_5d92c : CTabKA.D W_5d92c (Jal 0 64).
Proof. vm_refl. Qed.
Definition W_5d930 : bv 32 := 0x000d5517.
Lemma F_5d930 : CTabKA.F 0x5d930 W_5d930.
Proof. vm_refl. Qed.
Lemma D_5d930 : CTabKA.D W_5d930 (Auipc 10 213).
Proof. vm_refl. Qed.
Definition W_5d934 : bv 32 := 0xd6053503.
Lemma F_5d934 : CTabKA.F 0x5d934 W_5d934.
Proof. vm_refl. Qed.
Lemma D_5d934 : CTabKA.D W_5d934 (Load SZ8 true 10 10 3424).
Proof. vm_refl. Qed.
Definition W_5d938 : bv 32 := 0x00052503.
Lemma F_5d938 : CTabKA.F 0x5d938 W_5d938.
Proof. vm_refl. Qed.
Lemma D_5d938 : CTabKA.D W_5d938 (Load SZ4 true 10 10 0).
Proof. vm_refl. Qed.
Definition W_5d93c : bv 32 := 0x02050863.
Lemma F_5d93c : CTabKA.F 0x5d93c W_5d93c.
Proof. vm_refl. Qed.
Lemma D_5d93c : CTabKA.D W_5d93c (Branch BC_EQ 10 0 48).
Proof. vm_refl. Qed.
Definition W_5d940 : bv 32 := 0x64c250ef.
Lemma F_5d940 : CTabKA.F 0x5d940 W_5d940.
Proof. vm_refl. Qed.
Lemma D_5d940 : CTabKA.D W_5d940 (Jal 1 153164).
Proof. vm_refl. Qed.
Definition W_5d944 : bv 32 := 0x02050463.
Lemma F_5d944 : CTabKA.F 0x5d944 W_5d944.
Proof. vm_refl. Qed.
Lemma D_5d944 : CTabKA.D W_5d944 (Branch BC_EQ 10 0 40).
Proof. vm_refl. Qed.
Definition W_5d948 : bv 32 := 0x02850583.
Lemma F_5d948 : CTabKA.F 0x5d948 W_5d948.
Proof. vm_refl. Qed.
Lemma D_5d948 : CTabKA.D W_5d948 (Load SZ1 true 11 10 40).
Proof. vm_refl. Qed.
Definition W_5d94c : bv 32 := 0x0c058e63.
Lemma F_5d94c : CTabKA.F 0x5d94c W_5d94c.
Proof. vm_refl. Qed.
Lemma D_5d94c : CTabKA.D W_5d94c (Branch BC_EQ 11 0 220).
Proof. vm_refl. Qed.
Definition W_5d950 : bv 32 := 0x00000513.
Lemma F_5d950 : CTabKA.F 0x5d950 W_5d950.
Proof. vm_refl. Qed.
Lemma D_5d950 : CTabKA.D W_5d950 (OpImm ALU_ADD 10 0 0).
Proof. vm_refl. Qed.
Definition W_5d954 : bv 32 := 0x01813083.
Lemma F_5d954 : CTabKA.F 0x5d954 W_5d954.
Proof. vm_refl. Qed.
Lemma D_5d954 : CTabKA.D W_5d954 (Load SZ8 true 1 2 24).
Proof. vm_refl. Qed.
Definition W_5d958 : bv 32 := 0x01013403.
Lemma F_5d958 : CTabKA.F 0x5d958 W_5d958.
Proof. vm_refl. Qed.
Lemma D_5d958 : CTabKA.D W_5d958 (Load SZ8 true 8 2 16).
Proof. vm_refl. Qed.
Definition W_5d95c : bv 32 := 0x00813483.
Lemma F_5d95c : CTabKA.F 0x5d95c W_5d95c.
Proof. vm_refl. Qed.
Lemma D_5d95c : CTabKA.D W_5d95c (Load SZ8 true 9 2 8).
Proof. vm_refl. Qed.
Definition W_5d960 : bv 32 := 0x00013903.
Lemma F_5d960 : CTabKA.F 0x5d960 W_5d960.
Proof. vm_refl. Qed.
Lemma D_5d960 : CTabKA.D W_5d960 (Load SZ8 true 18 2 0).
Proof. vm_refl. Qed.
Definition W_5d964 : bv 32 := 0x02010113.
Lemma F_5d964 : CTabKA.F 0x5d964 W_5d964.
Proof. vm_refl. Qed.
Lemma D_5d964 : CTabKA.D W_5d964 (OpImm ALU_ADD 2 2 32).
Proof. vm_refl. Qed.
Definition W_5d968 : bv 32 := 0x00008067.
Lemma F_5d968 : CTabKA.F 0x5d968 W_5d968.
Proof. vm_refl. Qed.
Lemma D_5d968 : CTabKA.D W_5d968 (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_5d96c : bv 32 := 0x01813083.
Lemma F_5d96c : CTabKA.F 0x5d96c W_5d96c.
Proof. vm_refl. Qed.
Lemma D_5d96c : CTabKA.D W_5d96c (Load SZ8 true 1 2 24).
Proof. vm_refl. Qed.
Definition W_5d970 : bv 32 := 0x01013403.
Lemma F_5d970 : CTabKA.F 0x5d970 W_5d970.
Proof. vm_refl. Qed.
Lemma D_5d970 : CTabKA.D W_5d970 (Load SZ8 true 8 2 16).
Proof. vm_refl. Qed.
Definition W_5d974 : bv 32 := 0x00813483.
Lemma F_5d974 : CTabKA.F 0x5d974 W_5d974.
Proof. vm_refl. Qed.
Lemma D_5d974 : CTabKA.D W_5d974 (Load SZ8 true 9 2 8).
Proof. vm_refl. Qed.
Definition W_5d978 : bv 32 := 0x00013903.
Lemma F_5d978 : CTabKA.F 0x5d978 W_5d978.
Proof. vm_refl. Qed.
Lemma D_5d978 : CTabKA.D W_5d978 (Load SZ8 true 18 2 0).
Proof. vm_refl. Qed.
Definition W_5d97c : bv 32 := 0x02010113.
Lemma F_5d97c : CTabKA.F 0x5d97c W_5d97c.
Proof. vm_refl. Qed.
Lemma D_5d97c : CTabKA.D W_5d97c (OpImm ALU_ADD 2 2 32).
Proof. vm_refl. Qed.
Definition W_5d980 : bv 32 := 0x00008067.
Lemma F_5d980 : CTabKA.F 0x5d980 W_5d980.
Proof. vm_refl. Qed.
Lemma D_5d980 : CTabKA.D W_5d980 (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_5d984 : bv 32 := 0x00160613.
Lemma F_5d984 : CTabKA.F 0x5d984 W_5d984.
Proof. vm_refl. Qed.
Lemma D_5d984 : CTabKA.D W_5d984 (OpImm ALU_ADD 12 12 1).
Proof. vm_refl. Qed.
Definition W_5d988 : bv 32 := 0x00100513.
Lemma F_5d988 : CTabKA.F 0x5d988 W_5d988.
Proof. vm_refl. Qed.
Lemma D_5d988 : CTabKA.D W_5d988 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_5d98c : bv 32 := 0xffb90693.
Lemma F_5d98c : CTabKA.F 0x5d98c W_5d98c.
Proof. vm_refl. Qed.
Lemma D_5d98c : CTabKA.D W_5d98c (OpImm ALU_ADD 13 18 4091).
Proof. vm_refl. Qed.
Definition W_5d990 : bv 32 := 0x02c4b023.
Lemma F_5d990 : CTabKA.F 0x5d990 W_5d990.
Proof. vm_refl. Qed.
Lemma D_5d990 : CTabKA.D W_5d990 (Store SZ8 9 12 32).
Proof. vm_refl. Qed.
Definition W_5d994 : bv 32 := 0x00a78023.
Lemma F_5d994 : CTabKA.F 0x5d994 W_5d994.
Proof. vm_refl. Qed.
Lemma D_5d994 : CTabKA.D W_5d994 (Store SZ1 15 10 0).
Proof. vm_refl. Qed.
Definition W_5d998 : bv 32 := 0x00d51533.
Lemma F_5d998 : CTabKA.F 0x5d998 W_5d998.
Proof. vm_refl. Qed.
Lemma D_5d998 : CTabKA.D W_5d998 (Op ALU_SLL 10 10 13).
Proof. vm_refl. Qed.
Definition W_5d99c : bv 32 := 0x00400613.
Lemma F_5d99c : CTabKA.F 0x5d99c W_5d99c.
Proof. vm_refl. Qed.
Lemma D_5d99c : CTabKA.D W_5d99c (OpImm ALU_ADD 12 0 4).
Proof. vm_refl. Qed.
Definition W_5d9a0 : bv 32 := 0x00a89893.
Lemma F_5d9a0 : CTabKA.F 0x5d9a0 W_5d9a0.
Proof. vm_refl. Qed.
Lemma D_5d9a0 : CTabKA.D W_5d9a0 (ShiftImm ALU_SLL 17 17 10).
Proof. vm_refl. Qed.
Definition W_5d9a4 : bv 32 := 0x01261633.
Lemma F_5d9a4 : CTabKA.F 0x5d9a4 W_5d9a4.
Proof. vm_refl. Qed.
Lemma D_5d9a4 : CTabKA.D W_5d9a4 (Op ALU_SLL 12 12 18).
Proof. vm_refl. Qed.
Definition W_5d9a8 : bv 32 := 0x00a58533.
Lemma F_5d9a8 : CTabKA.F 0x5d9a8 W_5d9a8.
Proof. vm_refl. Qed.
Lemma D_5d9a8 : CTabKA.D W_5d9a8 (Op ALU_ADD 10 11 10).
Proof. vm_refl. Qed.
Definition W_5d9ac : bv 32 := 0x01160633.
Lemma F_5d9ac : CTabKA.F 0x5d9ac W_5d9ac.
Proof. vm_refl. Qed.
Lemma D_5d9ac : CTabKA.D W_5d9ac (Op ALU_ADD 12 12 17).
Proof. vm_refl. Qed.
Definition W_5d9b0 : bv 32 := 0x00c504b3.
Lemma F_5d9b0 : CTabKA.F 0x5d9b0 W_5d9b0.
Proof. vm_refl. Qed.
Lemma D_5d9b0 : CTabKA.D W_5d9b0 (Op ALU_ADD 9 10 12).
Proof. vm_refl. Qed.
Definition W_5d9b4 : bv 32 := 0x0084bc23.
Lemma F_5d9b4 : CTabKA.F 0x5d9b4 W_5d9b4.
Proof. vm_refl. Qed.
Lemma D_5d9b4 : CTabKA.D W_5d9b4 (Store SZ8 9 8 24).
Proof. vm_refl. Qed.
Definition W_5d9b8 : bv 32 := 0x3ef4bc23.
Lemma F_5d9b8 : CTabKA.F 0x5d9b8 W_5d9b8.
Proof. vm_refl. Qed.
Lemma D_5d9b8 : CTabKA.D W_5d9b8 (Store SZ8 9 15 1016).
Proof. vm_refl. Qed.
Definition W_5d9bc : bv 32 := 0x00048513.
Lemma F_5d9bc : CTabKA.F 0x5d9bc W_5d9bc.
Proof. vm_refl. Qed.
Lemma D_5d9bc : CTabKA.D W_5d9bc (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_5d9c0 : bv 32 := 0x084000ef.
Lemma F_5d9c0 : CTabKA.F 0x5d9c0 W_5d9c0.
Proof. vm_refl. Qed.
Lemma D_5d9c0 : CTabKA.D W_5d9c0 (Jal 1 132).
Proof. vm_refl. Qed.
Definition W_5d9c4 : bv 32 := 0x00050593.
Lemma F_5d9c4 : CTabKA.F 0x5d9c4 W_5d9c4.
Proof. vm_refl. Qed.
Lemma D_5d9c4 : CTabKA.D W_5d9c4 (OpImm ALU_ADD 11 10 0).
Proof. vm_refl. Qed.
Definition W_5d9c8 : bv 32 := 0x00048513.
Lemma F_5d9c8 : CTabKA.F 0x5d9c8 W_5d9c8.
Proof. vm_refl. Qed.
Lemma D_5d9c8 : CTabKA.D W_5d9c8 (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_5d9cc : bv 32 := 0x00000613.
Lemma F_5d9cc : CTabKA.F 0x5d9cc W_5d9cc.
Proof. vm_refl. Qed.
Lemma D_5d9cc : CTabKA.D W_5d9cc (OpImm ALU_ADD 12 0 0).
Proof. vm_refl. Qed.
Definition W_5d9d0 : bv 32 := 0x0005b023.
Lemma F_5d9d0 : CTabKA.F 0x5d9d0 W_5d9d0.
Proof. vm_refl. Qed.
Lemma D_5d9d0 : CTabKA.D W_5d9d0 (Store SZ8 11 0 0).
Proof. vm_refl. Qed.
Definition W_5d9d4 : bv 32 := 0x0005b423.
Lemma F_5d9d4 : CTabKA.F 0x5d9d4 W_5d9d4.
Proof. vm_refl. Qed.
Lemma D_5d9d4 : CTabKA.D W_5d9d4 (Store SZ8 11 0 8).
Proof. vm_refl. Qed.
Definition W_5d9d8 : bv 32 := 0x0005b823.
Lemma F_5d9d8 : CTabKA.F 0x5d9d8 W_5d9d8.
Proof. vm_refl. Qed.
Lemma D_5d9d8 : CTabKA.D W_5d9d8 (Store SZ8 11 0 16).
Proof. vm_refl. Qed.
Definition W_5d9dc : bv 32 := 0x0005bc23.
Lemma F_5d9dc : CTabKA.F 0x5d9dc W_5d9dc.
Proof. vm_refl. Qed.
Lemma D_5d9dc : CTabKA.D W_5d9dc (Store SZ8 11 0 24).
Proof. vm_refl. Qed.
Definition W_5d9e0 : bv 32 := 0x0205b023.
Lemma F_5d9e0 : CTabKA.F 0x5d9e0 W_5d9e0.
Proof. vm_refl. Qed.
Lemma D_5d9e0 : CTabKA.D W_5d9e0 (Store SZ8 11 0 32).
Proof. vm_refl. Qed.
Definition W_5d9e4 : bv 32 := 0x0205b423.
Lemma F_5d9e4 : CTabKA.F 0x5d9e4 W_5d9e4.
Proof. vm_refl. Qed.
Lemma D_5d9e4 : CTabKA.D W_5d9e4 (Store SZ8 11 0 40).
Proof. vm_refl. Qed.
Definition W_5d9e8 : bv 32 := 0x0205b823.
Lemma F_5d9e8 : CTabKA.F 0x5d9e8 W_5d9e8.
Proof. vm_refl. Qed.
Lemma D_5d9e8 : CTabKA.D W_5d9e8 (Store SZ8 11 0 48).
Proof. vm_refl. Qed.
Definition W_5d9ec : bv 32 := 0x0205bc23.
Lemma F_5d9ec : CTabKA.F 0x5d9ec W_5d9ec.
Proof. vm_refl. Qed.
Lemma D_5d9ec : CTabKA.D W_5d9ec (Store SZ8 11 0 56).
Proof. vm_refl. Qed.
Definition W_5d9f0 : bv 32 := 0x0405b023.
Lemma F_5d9f0 : CTabKA.F 0x5d9f0 W_5d9f0.
Proof. vm_refl. Qed.
Lemma D_5d9f0 : CTabKA.D W_5d9f0 (Store SZ8 11 0 64).
Proof. vm_refl. Qed.
Definition W_5d9f4 : bv 32 := 0x0405b423.
Lemma F_5d9f4 : CTabKA.F 0x5d9f4 W_5d9f4.
Proof. vm_refl. Qed.
Lemma D_5d9f4 : CTabKA.D W_5d9f4 (Store SZ8 11 0 72).
Proof. vm_refl. Qed.
Definition W_5d9f8 : bv 32 := 0x0405b823.
Lemma F_5d9f8 : CTabKA.F 0x5d9f8 W_5d9f8.
Proof. vm_refl. Qed.
Lemma D_5d9f8 : CTabKA.D W_5d9f8 (Store SZ8 11 0 80).
Proof. vm_refl. Qed.
Definition W_5d9fc : bv 32 := 0x0405bc23.
Lemma F_5d9fc : CTabKA.F 0x5d9fc W_5d9fc.
Proof. vm_refl. Qed.
Lemma D_5d9fc : CTabKA.D W_5d9fc (Store SZ8 11 0 88).
Proof. vm_refl. Qed.
Definition W_5da00 : bv 32 := 0x0605b023.
Lemma F_5da00 : CTabKA.F 0x5da00 W_5da00.
Proof. vm_refl. Qed.
Lemma D_5da00 : CTabKA.D W_5da00 (Store SZ8 11 0 96).
Proof. vm_refl. Qed.
Definition W_5da04 : bv 32 := 0x0605b423.
Lemma F_5da04 : CTabKA.F 0x5da04 W_5da04.
Proof. vm_refl. Qed.
Lemma D_5da04 : CTabKA.D W_5da04 (Store SZ8 11 0 104).
Proof. vm_refl. Qed.
Definition W_5da08 : bv 32 := 0x0605b823.
Lemma F_5da08 : CTabKA.F 0x5da08 W_5da08.
Proof. vm_refl. Qed.
Lemma D_5da08 : CTabKA.D W_5da08 (Store SZ8 11 0 112).
Proof. vm_refl. Qed.
Definition W_5da0c : bv 32 := 0x0605bc23.
Lemma F_5da0c : CTabKA.F 0x5da0c W_5da0c.
Proof. vm_refl. Qed.
Lemma D_5da0c : CTabKA.D W_5da0c (Store SZ8 11 0 120).
Proof. vm_refl. Qed.
Definition W_5da10 : bv 32 := 0x01813083.
Lemma F_5da10 : CTabKA.F 0x5da10 W_5da10.
Proof. vm_refl. Qed.
Lemma D_5da10 : CTabKA.D W_5da10 (Load SZ8 true 1 2 24).
Proof. vm_refl. Qed.
Definition W_5da14 : bv 32 := 0x01013403.
Lemma F_5da14 : CTabKA.F 0x5da14 W_5da14.
Proof. vm_refl. Qed.
Lemma D_5da14 : CTabKA.D W_5da14 (Load SZ8 true 8 2 16).
Proof. vm_refl. Qed.
Definition W_5da18 : bv 32 := 0x00813483.
Lemma F_5da18 : CTabKA.F 0x5da18 W_5da18.
Proof. vm_refl. Qed.
Lemma D_5da18 : CTabKA.D W_5da18 (Load SZ8 true 9 2 8).
Proof. vm_refl. Qed.
Definition W_5da1c : bv 32 := 0x00013903.
Lemma F_5da1c : CTabKA.F 0x5da1c W_5da1c.
Proof. vm_refl. Qed.
Lemma D_5da1c : CTabKA.D W_5da1c (Load SZ8 true 18 2 0).
Proof. vm_refl. Qed.
Definition W_5da20 : bv 32 := 0x02010113.
Lemma F_5da20 : CTabKA.F 0x5da20 W_5da20.
Proof. vm_refl. Qed.
Lemma D_5da20 : CTabKA.D W_5da20 (OpImm ALU_ADD 2 2 32).
Proof. vm_refl. Qed.
Definition W_5da24 : bv 32 := 0x00008067.
Lemma F_5da24 : CTabKA.F 0x5da24 W_5da24.
Proof. vm_refl. Qed.
Lemma D_5da24 : CTabKA.D W_5da24 (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_5da28 : bv 32 := 0x04853483.
Lemma F_5da28 : CTabKA.F 0x5da28 W_5da28.
Proof. vm_refl. Qed.
Lemma D_5da28 : CTabKA.D W_5da28 (Load SZ8 true 9 10 72).
Proof. vm_refl. Qed.

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
Definition W_78ebc : bv 32 := 0x0100006f.
Lemma F_78ebc : CTabKA.F 0x78ebc W_78ebc.
Proof. vm_refl. Qed.
Lemma D_78ebc : CTabKA.D W_78ebc (Jal 0 16).
Proof. vm_refl. Qed.
Definition W_78ec0 : bv 32 := 0x1dc0006f.
Lemma F_78ec0 : CTabKA.F 0x78ec0 W_78ec0.
Proof. vm_refl. Qed.
Lemma D_78ec0 : CTabKA.D W_78ec0 (Jal 0 476).
Proof. vm_refl. Qed.
Definition W_78ec8 : bv 32 := 0x7400006f.
Lemma F_78ec8 : CTabKA.F 0x78ec8 W_78ec8.
Proof. vm_refl. Qed.
Lemma D_78ec8 : CTabKA.D W_78ec8 (Jal 0 1856).
Proof. vm_refl. Qed.
Definition W_78ecc : bv 32 := 0x81010113.
Lemma F_78ecc : CTabKA.F 0x78ecc W_78ecc.
Proof. vm_refl. Qed.
Lemma D_78ecc : CTabKA.D W_78ecc (OpImm ALU_ADD 2 2 2064).
Proof. vm_refl. Qed.
Definition W_78ed0 : bv 32 := 0x7e113423.
Lemma F_78ed0 : CTabKA.F 0x78ed0 W_78ed0.
Proof. vm_refl. Qed.
Lemma D_78ed0 : CTabKA.D W_78ed0 (Store SZ8 2 1 2024).
Proof. vm_refl. Qed.
Definition W_78ed4 : bv 32 := 0x7e813023.
Lemma F_78ed4 : CTabKA.F 0x78ed4 W_78ed4.
Proof. vm_refl. Qed.
Lemma D_78ed4 : CTabKA.D W_78ed4 (Store SZ8 2 8 2016).
Proof. vm_refl. Qed.
Definition W_78ed8 : bv 32 := 0x7c913c23.
Lemma F_78ed8 : CTabKA.F 0x78ed8 W_78ed8.
Proof. vm_refl. Qed.
Lemma D_78ed8 : CTabKA.D W_78ed8 (Store SZ8 2 9 2008).
Proof. vm_refl. Qed.
Definition W_78edc : bv 32 := 0x7d213823.
Lemma F_78edc : CTabKA.F 0x78edc W_78edc.
Proof. vm_refl. Qed.
Lemma D_78edc : CTabKA.D W_78edc (Store SZ8 2 18 2000).
Proof. vm_refl. Qed.
Definition W_78ee0 : bv 32 := 0x7d313423.
Lemma F_78ee0 : CTabKA.F 0x78ee0 W_78ee0.
Proof. vm_refl. Qed.
Lemma D_78ee0 : CTabKA.D W_78ee0 (Store SZ8 2 19 1992).
Proof. vm_refl. Qed.
Definition W_78ee4 : bv 32 := 0x7d413023.
Lemma F_78ee4 : CTabKA.F 0x78ee4 W_78ee4.
Proof. vm_refl. Qed.
Lemma D_78ee4 : CTabKA.D W_78ee4 (Store SZ8 2 20 1984).
Proof. vm_refl. Qed.
Definition W_78ee8 : bv 32 := 0x7b513c23.
Lemma F_78ee8 : CTabKA.F 0x78ee8 W_78ee8.
Proof. vm_refl. Qed.
Lemma D_78ee8 : CTabKA.D W_78ee8 (Store SZ8 2 21 1976).
Proof. vm_refl. Qed.
Definition W_78eec : bv 32 := 0x7f010413.
Lemma F_78eec : CTabKA.F 0x78eec W_78eec.
Proof. vm_refl. Qed.
Lemma D_78eec : CTabKA.D W_78eec (OpImm ALU_ADD 8 2 2032).
Proof. vm_refl. Qed.
Definition W_78ef0 : bv 32 := 0xfa010113.
Lemma F_78ef0 : CTabKA.F 0x78ef0 W_78ef0.
Proof. vm_refl. Qed.
Lemma D_78ef0 : CTabKA.D W_78ef0 (OpImm ALU_ADD 2 2 4000).
Proof. vm_refl. Qed.
Definition W_78ef4 : bv 32 := 0x00008913.
Lemma F_78ef4 : CTabKA.F 0x78ef4 W_78ef4.
Proof. vm_refl. Qed.
Lemma D_78ef4 : CTabKA.D W_78ef4 (OpImm ALU_ADD 18 1 0).
Proof. vm_refl. Qed.
Definition W_78ef8 : bv 32 := 0x00050493.
Lemma F_78ef8 : CTabKA.F 0x78ef8 W_78ef8.
Proof. vm_refl. Qed.
Lemma D_78ef8 : CTabKA.D W_78ef8 (OpImm ALU_ADD 9 10 0).
Proof. vm_refl. Qed.
Definition W_78efc : bv 32 := 0x10c0c0ef.
Lemma F_78efc : CTabKA.F 0x78efc W_78efc.
Proof. vm_refl. Qed.
Lemma D_78efc : CTabKA.D W_78efc (Jal 1 49420).
Proof. vm_refl. Qed.
Definition W_78f00 : bv 32 := 0x02f4d593.
Lemma F_78f00 : CTabKA.F 0x78f00 W_78f00.
Proof. vm_refl. Qed.
Lemma D_78f00 : CTabKA.D W_78f00 (ShiftImm ALU_SRL 11 9 47).
Proof. vm_refl. Qed.
Definition W_78f04 : bv 32 := 0x0a059063.
Lemma F_78f04 : CTabKA.F 0x78f04 W_78f04.
Proof. vm_refl. Qed.
Lemma D_78f04 : CTabKA.D W_78f04 (Branch BC_NE 11 0 160).
Proof. vm_refl. Qed.
Definition W_78f08 : bv 32 := 0x0204d593.
Lemma F_78f08 : CTabKA.F 0x78f08 W_78f08.
Proof. vm_refl. Qed.
Lemma D_78f08 : CTabKA.D W_78f08 (ShiftImm ALU_SRL 11 9 32).
Proof. vm_refl. Qed.
Definition W_78f0c : bv 32 := 0x00359613.
Lemma F_78f0c : CTabKA.F 0x78f0c W_78f0c.
Proof. vm_refl. Qed.
Lemma D_78f0c : CTabKA.D W_78f0c (ShiftImm ALU_SLL 12 11 3).
Proof. vm_refl. Qed.
Definition W_78f10 : bv 32 := 0x00c50633.
Lemma F_78f10 : CTabKA.F 0x78f10 W_78f10.
Proof. vm_refl. Qed.
Lemma D_78f10 : CTabKA.D W_78f10 (Op ALU_ADD 12 10 12).
Proof. vm_refl. Qed.
Definition W_78f14 : bv 32 := 0x00863683.
Lemma F_78f14 : CTabKA.F 0x78f14 W_78f14.
Proof. vm_refl. Qed.
Lemma D_78f14 : CTabKA.D W_78f14 (Load SZ8 true 13 12 8).
Proof. vm_refl. Qed.
Definition W_78f18 : bv 32 := 0x0230000f.
Lemma F_78f18 : CTabKA.F 0x78f18 W_78f18.
Proof. vm_refl. Qed.
Lemma D_78f18 : CTabKA.D W_78f18 (Fence 0 2 3 0 0).
Proof. vm_refl. Qed.
Definition W_78f1c : bv 32 := 0x08068463.
Lemma F_78f1c : CTabKA.F 0x78f1c W_78f1c.
Proof. vm_refl. Qed.
Lemma D_78f1c : CTabKA.D W_78f1c (Branch BC_EQ 13 0 136).
Proof. vm_refl. Qed.
Definition W_78fa4 : bv 32 := 0x80040a13.
Lemma F_78fa4 : CTabKA.F 0x78fa4 W_78fa4.
Proof. vm_refl. Qed.
Lemma D_78fa4 : CTabKA.D W_78fa4 (OpImm ALU_ADD 20 8 2048).
Proof. vm_refl. Qed.
Definition W_78fa8 : bv 32 := 0xfb0a0a13.
Lemma F_78fa8 : CTabKA.F 0x78fa8 W_78fa8.
Proof. vm_refl. Qed.
Lemma D_78fa8 : CTabKA.D W_78fa8 (OpImm ALU_ADD 20 20 4016).
Proof. vm_refl. Qed.
Definition W_78fac : bv 32 := 0x80040513.
Lemma F_78fac : CTabKA.F 0x78fac W_78fac.
Proof. vm_refl. Qed.
Lemma D_78fac : CTabKA.D W_78fac (OpImm ALU_ADD 10 8 2048).
Proof. vm_refl. Qed.
Definition W_78fb0 : bv 32 := 0xfc050513.
Lemma F_78fb0 : CTabKA.F 0x78fb0 W_78fb0.
Proof. vm_refl. Qed.
Lemma D_78fb0 : CTabKA.D W_78fb0 (OpImm ALU_ADD 10 10 4032).
Proof. vm_refl. Qed.
Definition W_78fb4 : bv 32 := 0x7ffa0a93.
Lemma F_78fb4 : CTabKA.F 0x78fb4 W_78fb4.
Proof. vm_refl. Qed.
Lemma D_78fb4 : CTabKA.D W_78fb4 (OpImm ALU_ADD 21 20 2047).
Proof. vm_refl. Qed.
Definition W_78fb8 : bv 32 := 0x000ab4a3.
Lemma F_78fb8 : CTabKA.F 0x78fb8 W_78fb8.
Proof. vm_refl. Qed.
Lemma D_78fb8 : CTabKA.D W_78fb8 (Store SZ8 21 0 9).
Proof. vm_refl. Qed.
Definition W_78fbc : bv 32 := 0x00aa3023.
Lemma F_78fbc : CTabKA.F 0x78fbc W_78fbc.
Proof. vm_refl. Qed.
Lemma D_78fbc : CTabKA.D W_78fbc (Store SZ8 20 10 0).
Proof. vm_refl. Qed.
Definition W_78fc0 : bv 32 := 0x000a3423.
Lemma F_78fc0 : CTabKA.F 0x78fc0 W_78fc0.
Proof. vm_refl. Qed.
Lemma D_78fc0 : CTabKA.D W_78fc0 (Store SZ8 20 0 8).
Proof. vm_refl. Qed.
Definition W_78fc4 : bv 32 := 0x550080ef.
Lemma F_78fc4 : CTabKA.F 0x78fc4 W_78fc4.
Proof. vm_refl. Qed.
Lemma D_78fc4 : CTabKA.D W_78fc4 (Jal 1 34128).
Proof. vm_refl. Qed.
Definition W_78fc8 : bv 32 := 0x00200593.
Lemma F_78fc8 : CTabKA.F 0x78fc8 W_78fc8.
Proof. vm_refl. Qed.
Lemma D_78fc8 : CTabKA.D W_78fc8 (OpImm ALU_ADD 11 0 2).
Proof. vm_refl. Qed.
Definition W_78fcc : bv 32 := 0x02a5ea63.
Lemma F_78fcc : CTabKA.F 0x78fcc W_78fcc.
Proof. vm_refl. Qed.
Lemma D_78fcc : CTabKA.D W_78fcc (Branch BC_LTU 11 10 52).
Proof. vm_refl. Qed.
Definition W_79000 : bv 32 := 0x7f1200ef.
Lemma F_79000 : CTabKA.F 0x79000 W_79000.
Proof. vm_refl. Qed.
Lemma D_79000 : CTabKA.D W_79000 (Jal 1 135152).
Proof. vm_refl. Qed.
Definition W_79004 : bv 32 := 0x000b9597.
Lemma F_79004 : CTabKA.F 0x79004 W_79004.
Proof. vm_refl. Qed.
Lemma D_79004 : CTabKA.D W_79004 (Auipc 11 185).
Proof. vm_refl. Qed.
Definition W_79008 : bv 32 := 0x6245b583.
Lemma F_79008 : CTabKA.F 0x79008 W_79008.
Proof. vm_refl. Qed.
Lemma D_79008 : CTabKA.D W_79008 (Load SZ8 true 11 11 1572).
Proof. vm_refl. Qed.
Definition W_7900c : bv 32 := 0x0225c983.
Lemma F_7900c : CTabKA.F 0x7900c W_7900c.
Proof. vm_refl. Qed.
Lemma D_7900c : CTabKA.D W_7900c (Load SZ1 false 19 11 34).
Proof. vm_refl. Qed.
Definition W_79010 : bv 32 := 0x00050913.
Lemma F_79010 : CTabKA.F 0x79010 W_79010.
Proof. vm_refl. Qed.
Lemma D_79010 : CTabKA.D W_79010 (OpImm ALU_ADD 18 10 0).
Proof. vm_refl. Qed.
Definition W_79014 : bv 32 := 0x500080ef.
Lemma F_79014 : CTabKA.F 0x79014 W_79014.
Proof. vm_refl. Qed.
Lemma D_79014 : CTabKA.D W_79014 (Jal 1 34048).
Proof. vm_refl. Qed.
Definition W_79018 : bv 32 := 0x00050793.
Lemma F_79018 : CTabKA.F 0x79018 W_79018.
Proof. vm_refl. Qed.
Lemma D_79018 : CTabKA.D W_79018 (OpImm ALU_ADD 15 10 0).
Proof. vm_refl. Qed.
Definition W_7901c : bv 32 := 0x00153513.
Lemma F_7901c : CTabKA.F 0x7901c W_7901c.
Proof. vm_refl. Qed.
Lemma D_7901c : CTabKA.D W_7901c (OpImm ALU_SLTU 10 10 1).
Proof. vm_refl. Qed.
Definition W_79020 : bv 32 := 0xfff50513.
Lemma F_79020 : CTabKA.F 0x79020 W_79020.
Proof. vm_refl. Qed.
Lemma D_79020 : CTabKA.D W_79020 (OpImm ALU_ADD 10 10 4095).
Proof. vm_refl. Qed.
Definition W_79024 : bv 32 := 0x008575b3.
Lemma F_79024 : CTabKA.F 0x79024 W_79024.
Proof. vm_refl. Qed.
Lemma D_79024 : CTabKA.D W_79024 (Op ALU_AND 11 10 8).
Proof. vm_refl. Qed.
Definition W_79028 : bv 32 := 0x00100513.
Lemma F_79028 : CTabKA.F 0x79028 W_79028.
Proof. vm_refl. Qed.
Lemma D_79028 : CTabKA.D W_79028 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_7902c : bv 32 := 0x00bab4a3.
Lemma F_7902c : CTabKA.F 0x7902c W_7902c.
Proof. vm_refl. Qed.
Lemma D_7902c : CTabKA.D W_7902c (Store SZ8 21 11 9).
Proof. vm_refl. Qed.
Definition W_79030 : bv 32 := 0x00f56a63.
Lemma F_79030 : CTabKA.F 0x79030 W_79030.
Proof. vm_refl. Qed.
Lemma D_79030 : CTabKA.D W_79030 (Branch BC_LTU 10 15 20).
Proof. vm_refl. Qed.
Definition W_79044 : bv 32 := 0x80040513.
Lemma F_79044 : CTabKA.F 0x79044 W_79044.
Proof. vm_refl. Qed.
Lemma D_79044 : CTabKA.D W_79044 (OpImm ALU_ADD 10 8 2048).
Proof. vm_refl. Qed.
Definition W_79048 : bv 32 := 0xfb050513.
Lemma F_79048 : CTabKA.F 0x79048 W_79048.
Proof. vm_refl. Qed.
Lemma D_79048 : CTabKA.D W_79048 (OpImm ALU_ADD 10 10 4016).
Proof. vm_refl. Qed.
Definition W_7904c : bv 32 := 0x00090593.
Lemma F_7904c : CTabKA.F 0x7904c W_7904c.
Proof. vm_refl. Qed.
Lemma D_7904c : CTabKA.D W_7904c (OpImm ALU_ADD 11 18 0).
Proof. vm_refl. Qed.
Definition W_79050 : bv 32 := 0x00040613.
Lemma F_79050 : CTabKA.F 0x79050 W_79050.
Proof. vm_refl. Qed.
Lemma D_79050 : CTabKA.D W_79050 (OpImm ALU_ADD 12 8 0).
Proof. vm_refl. Qed.
Definition W_79054 : bv 32 := 0x00000693.
Lemma F_79054 : CTabKA.F 0x79054 W_79054.
Proof. vm_refl. Qed.
Lemma D_79054 : CTabKA.D W_79054 (OpImm ALU_ADD 13 0 0).
Proof. vm_refl. Qed.
Definition W_79058 : bv 32 := 0x00098713.
Lemma F_79058 : CTabKA.F 0x79058 W_79058.
Proof. vm_refl. Qed.
Lemma D_79058 : CTabKA.D W_79058 (OpImm ALU_ADD 14 19 0).
Proof. vm_refl. Qed.
Definition W_7905c : bv 32 := 0x4c8080ef.
Lemma F_7905c : CTabKA.F 0x7905c W_7905c.
Proof. vm_refl. Qed.
Lemma D_7905c : CTabKA.D W_7905c (Jal 1 33992).
Proof. vm_refl. Qed.
Definition W_79060 : bv 32 := 0x80040593.
Lemma F_79060 : CTabKA.F 0x79060 W_79060.
Proof. vm_refl. Qed.
Lemma D_79060 : CTabKA.D W_79060 (OpImm ALU_ADD 11 8 2048).
Proof. vm_refl. Qed.
Definition W_79064 : bv 32 := 0xfb058593.
Lemma F_79064 : CTabKA.F 0x79064 W_79064.
Proof. vm_refl. Qed.
Lemma D_79064 : CTabKA.D W_79064 (OpImm ALU_ADD 11 11 4016).
Proof. vm_refl. Qed.
Definition W_79068 : bv 32 := 0x00100613.
Lemma F_79068 : CTabKA.F 0x79068 W_79068.
Proof. vm_refl. Qed.
Lemma D_79068 : CTabKA.D W_79068 (OpImm ALU_ADD 12 0 1).
Proof. vm_refl. Qed.
Definition W_7906c : bv 32 := 0x00048513.
Lemma F_7906c : CTabKA.F 0x7906c W_7906c.
Proof. vm_refl. Qed.
Lemma D_7906c : CTabKA.D W_7906c (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_79070 : bv 32 := 0x839d80ef.
Lemma F_79070 : CTabKA.F 0x79070 W_79070.
Proof. vm_refl. Qed.
Lemma D_79070 : CTabKA.D W_79070 (Jal 1 1935416).
Proof. vm_refl. Qed.
Definition W_79074 : bv 32 := 0x06010113.
Lemma F_79074 : CTabKA.F 0x79074 W_79074.
Proof. vm_refl. Qed.
Lemma D_79074 : CTabKA.D W_79074 (OpImm ALU_ADD 2 2 96).
Proof. vm_refl. Qed.
Definition W_79078 : bv 32 := 0x7e813083.
Lemma F_79078 : CTabKA.F 0x79078 W_79078.
Proof. vm_refl. Qed.
Lemma D_79078 : CTabKA.D W_79078 (Load SZ8 true 1 2 2024).
Proof. vm_refl. Qed.
Definition W_7907c : bv 32 := 0x7e013403.
Lemma F_7907c : CTabKA.F 0x7907c W_7907c.
Proof. vm_refl. Qed.
Lemma D_7907c : CTabKA.D W_7907c (Load SZ8 true 8 2 2016).
Proof. vm_refl. Qed.
Definition W_79080 : bv 32 := 0x7d813483.
Lemma F_79080 : CTabKA.F 0x79080 W_79080.
Proof. vm_refl. Qed.
Lemma D_79080 : CTabKA.D W_79080 (Load SZ8 true 9 2 2008).
Proof. vm_refl. Qed.
Definition W_79084 : bv 32 := 0x7d013903.
Lemma F_79084 : CTabKA.F 0x79084 W_79084.
Proof. vm_refl. Qed.
Lemma D_79084 : CTabKA.D W_79084 (Load SZ8 true 18 2 2000).
Proof. vm_refl. Qed.
Definition W_79088 : bv 32 := 0x7c813983.
Lemma F_79088 : CTabKA.F 0x79088 W_79088.
Proof. vm_refl. Qed.
Lemma D_79088 : CTabKA.D W_79088 (Load SZ8 true 19 2 1992).
Proof. vm_refl. Qed.
Definition W_7908c : bv 32 := 0x7c013a03.
Lemma F_7908c : CTabKA.F 0x7908c W_7908c.
Proof. vm_refl. Qed.
Lemma D_7908c : CTabKA.D W_7908c (Load SZ8 true 20 2 1984).
Proof. vm_refl. Qed.
Definition W_79090 : bv 32 := 0x7b813a83.
Lemma F_79090 : CTabKA.F 0x79090 W_79090.
Proof. vm_refl. Qed.
Lemma D_79090 : CTabKA.D W_79090 (Load SZ8 true 21 2 1976).
Proof. vm_refl. Qed.
Definition W_79094 : bv 32 := 0x7f010113.
Lemma F_79094 : CTabKA.F 0x79094 W_79094.
Proof. vm_refl. Qed.
Lemma D_79094 : CTabKA.D W_79094 (OpImm ALU_ADD 2 2 2032).
Proof. vm_refl. Qed.
Definition W_79098 : bv 32 := 0x00008067.
Lemma F_79098 : CTabKA.F 0x79098 W_79098.
Proof. vm_refl. Qed.
Lemma D_79098 : CTabKA.D W_79098 (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_7909c : bv 32 := 0x81010113.
Lemma F_7909c : CTabKA.F 0x7909c W_7909c.
Proof. vm_refl. Qed.
Lemma D_7909c : CTabKA.D W_7909c (OpImm ALU_ADD 2 2 2064).
Proof. vm_refl. Qed.
Definition W_790a0 : bv 32 := 0x7e113423.
Lemma F_790a0 : CTabKA.F 0x790a0 W_790a0.
Proof. vm_refl. Qed.
Lemma D_790a0 : CTabKA.D W_790a0 (Store SZ8 2 1 2024).
Proof. vm_refl. Qed.
Definition W_790a4 : bv 32 := 0x7e813023.
Lemma F_790a4 : CTabKA.F 0x790a4 W_790a4.
Proof. vm_refl. Qed.
Lemma D_790a4 : CTabKA.D W_790a4 (Store SZ8 2 8 2016).
Proof. vm_refl. Qed.
Definition W_790a8 : bv 32 := 0x7c913c23.
Lemma F_790a8 : CTabKA.F 0x790a8 W_790a8.
Proof. vm_refl. Qed.
Lemma D_790a8 : CTabKA.D W_790a8 (Store SZ8 2 9 2008).
Proof. vm_refl. Qed.
Definition W_790ac : bv 32 := 0x7d213823.
Lemma F_790ac : CTabKA.F 0x790ac W_790ac.
Proof. vm_refl. Qed.
Lemma D_790ac : CTabKA.D W_790ac (Store SZ8 2 18 2000).
Proof. vm_refl. Qed.
Definition W_790b0 : bv 32 := 0x7d313423.
Lemma F_790b0 : CTabKA.F 0x790b0 W_790b0.
Proof. vm_refl. Qed.
Lemma D_790b0 : CTabKA.D W_790b0 (Store SZ8 2 19 1992).
Proof. vm_refl. Qed.
Definition W_790b4 : bv 32 := 0x7d413023.
Lemma F_790b4 : CTabKA.F 0x790b4 W_790b4.
Proof. vm_refl. Qed.
Lemma D_790b4 : CTabKA.D W_790b4 (Store SZ8 2 20 1984).
Proof. vm_refl. Qed.
Definition W_790b8 : bv 32 := 0x7b513c23.
Lemma F_790b8 : CTabKA.F 0x790b8 W_790b8.
Proof. vm_refl. Qed.
Lemma D_790b8 : CTabKA.D W_790b8 (Store SZ8 2 21 1976).
Proof. vm_refl. Qed.
Definition W_790bc : bv 32 := 0x7f010413.
Lemma F_790bc : CTabKA.F 0x790bc W_790bc.
Proof. vm_refl. Qed.
Lemma D_790bc : CTabKA.D W_790bc (OpImm ALU_ADD 8 2 2032).
Proof. vm_refl. Qed.
Definition W_790c0 : bv 32 := 0xfa010113.
Lemma F_790c0 : CTabKA.F 0x790c0 W_790c0.
Proof. vm_refl. Qed.
Lemma D_790c0 : CTabKA.D W_790c0 (OpImm ALU_ADD 2 2 4000).
Proof. vm_refl. Qed.
Definition W_790c4 : bv 32 := 0x00008913.
Lemma F_790c4 : CTabKA.F 0x790c4 W_790c4.
Proof. vm_refl. Qed.
Lemma D_790c4 : CTabKA.D W_790c4 (OpImm ALU_ADD 18 1 0).
Proof. vm_refl. Qed.
Definition W_790c8 : bv 32 := 0x00050493.
Lemma F_790c8 : CTabKA.F 0x790c8 W_790c8.
Proof. vm_refl. Qed.
Lemma D_790c8 : CTabKA.D W_790c8 (OpImm ALU_ADD 9 10 0).
Proof. vm_refl. Qed.
Definition W_790cc : bv 32 := 0x6c0070ef.
Lemma F_790cc : CTabKA.F 0x790cc W_790cc.
Proof. vm_refl. Qed.
Lemma D_790cc : CTabKA.D W_790cc (Jal 1 30400).
Proof. vm_refl. Qed.
Definition W_790d0 : bv 32 := 0x06050063.
Lemma F_790d0 : CTabKA.F 0x790d0 W_790d0.
Proof. vm_refl. Qed.
Lemma D_790d0 : CTabKA.D W_790d0 (Branch BC_EQ 10 0 96).
Proof. vm_refl. Qed.
Definition W_790d4 : bv 32 := 0x80040a13.
Lemma F_790d4 : CTabKA.F 0x790d4 W_790d4.
Proof. vm_refl. Qed.
Lemma D_790d4 : CTabKA.D W_790d4 (OpImm ALU_ADD 20 8 2048).
Proof. vm_refl. Qed.
Definition W_790d8 : bv 32 := 0xfb0a0a13.
Lemma F_790d8 : CTabKA.F 0x790d8 W_790d8.
Proof. vm_refl. Qed.
Lemma D_790d8 : CTabKA.D W_790d8 (OpImm ALU_ADD 20 20 4016).
Proof. vm_refl. Qed.
Definition W_790dc : bv 32 := 0x80040513.
Lemma F_790dc : CTabKA.F 0x790dc W_790dc.
Proof. vm_refl. Qed.
Lemma D_790dc : CTabKA.D W_790dc (OpImm ALU_ADD 10 8 2048).
Proof. vm_refl. Qed.
Definition W_790e0 : bv 32 := 0xfc050513.
Lemma F_790e0 : CTabKA.F 0x790e0 W_790e0.
Proof. vm_refl. Qed.
Lemma D_790e0 : CTabKA.D W_790e0 (OpImm ALU_ADD 10 10 4032).
Proof. vm_refl. Qed.
Definition W_790e4 : bv 32 := 0x7ffa0a93.
Lemma F_790e4 : CTabKA.F 0x790e4 W_790e4.
Proof. vm_refl. Qed.
Lemma D_790e4 : CTabKA.D W_790e4 (OpImm ALU_ADD 21 20 2047).
Proof. vm_refl. Qed.
Definition W_790e8 : bv 32 := 0x000ab4a3.
Lemma F_790e8 : CTabKA.F 0x790e8 W_790e8.
Proof. vm_refl. Qed.
Lemma D_790e8 : CTabKA.D W_790e8 (Store SZ8 21 0 9).
Proof. vm_refl. Qed.
Definition W_790ec : bv 32 := 0x00aa3023.
Lemma F_790ec : CTabKA.F 0x790ec W_790ec.
Proof. vm_refl. Qed.
Lemma D_790ec : CTabKA.D W_790ec (Store SZ8 20 10 0).
Proof. vm_refl. Qed.
Definition W_790f0 : bv 32 := 0x000a3423.
Lemma F_790f0 : CTabKA.F 0x790f0 W_790f0.
Proof. vm_refl. Qed.
Lemma D_790f0 : CTabKA.D W_790f0 (Store SZ8 20 0 8).
Proof. vm_refl. Qed.
Definition W_790f4 : bv 32 := 0x420080ef.
Lemma F_790f4 : CTabKA.F 0x790f4 W_790f4.
Proof. vm_refl. Qed.
Lemma D_790f4 : CTabKA.D W_790f4 (Jal 1 33824).
Proof. vm_refl. Qed.
Definition W_790f8 : bv 32 := 0x00200593.
Lemma F_790f8 : CTabKA.F 0x790f8 W_790f8.
Proof. vm_refl. Qed.
Lemma D_790f8 : CTabKA.D W_790f8 (OpImm ALU_ADD 11 0 2).
Proof. vm_refl. Qed.
Definition W_790fc : bv 32 := 0x06a5e263.
Lemma F_790fc : CTabKA.F 0x790fc W_790fc.
Proof. vm_refl. Qed.
Lemma D_790fc : CTabKA.D W_790fc (Branch BC_LTU 11 10 100).
Proof. vm_refl. Qed.
Definition W_79160 : bv 32 := 0x691200ef.
Lemma F_79160 : CTabKA.F 0x79160 W_79160.
Proof. vm_refl. Qed.
Lemma D_79160 : CTabKA.D W_79160 (Jal 1 134800).
Proof. vm_refl. Qed.
Definition W_79164 : bv 32 := 0x000b9597.
Lemma F_79164 : CTabKA.F 0x79164 W_79164.
Proof. vm_refl. Qed.
Lemma D_79164 : CTabKA.D W_79164 (Auipc 11 185).
Proof. vm_refl. Qed.
Definition W_79168 : bv 32 := 0x4c45b583.
Lemma F_79168 : CTabKA.F 0x79168 W_79168.
Proof. vm_refl. Qed.
Lemma D_79168 : CTabKA.D W_79168 (Load SZ8 true 11 11 1220).
Proof. vm_refl. Qed.
Definition W_7916c : bv 32 := 0x0225c983.
Lemma F_7916c : CTabKA.F 0x7916c W_7916c.
Proof. vm_refl. Qed.
Lemma D_7916c : CTabKA.D W_7916c (Load SZ1 false 19 11 34).
Proof. vm_refl. Qed.
Definition W_79170 : bv 32 := 0x00050913.
Lemma F_79170 : CTabKA.F 0x79170 W_79170.
Proof. vm_refl. Qed.
Lemma D_79170 : CTabKA.D W_79170 (OpImm ALU_ADD 18 10 0).
Proof. vm_refl. Qed.
Definition W_79174 : bv 32 := 0x3a0080ef.
Lemma F_79174 : CTabKA.F 0x79174 W_79174.
Proof. vm_refl. Qed.
Lemma D_79174 : CTabKA.D W_79174 (Jal 1 33696).
Proof. vm_refl. Qed.
Definition W_79178 : bv 32 := 0x00050793.
Lemma F_79178 : CTabKA.F 0x79178 W_79178.
Proof. vm_refl. Qed.
Lemma D_79178 : CTabKA.D W_79178 (OpImm ALU_ADD 15 10 0).
Proof. vm_refl. Qed.
Definition W_7917c : bv 32 := 0x00153513.
Lemma F_7917c : CTabKA.F 0x7917c W_7917c.
Proof. vm_refl. Qed.
Lemma D_7917c : CTabKA.D W_7917c (OpImm ALU_SLTU 10 10 1).
Proof. vm_refl. Qed.
Definition W_79180 : bv 32 := 0xfff50513.
Lemma F_79180 : CTabKA.F 0x79180 W_79180.
Proof. vm_refl. Qed.
Lemma D_79180 : CTabKA.D W_79180 (OpImm ALU_ADD 10 10 4095).
Proof. vm_refl. Qed.
Definition W_79184 : bv 32 := 0x008575b3.
Lemma F_79184 : CTabKA.F 0x79184 W_79184.
Proof. vm_refl. Qed.
Lemma D_79184 : CTabKA.D W_79184 (Op ALU_AND 11 10 8).
Proof. vm_refl. Qed.
Definition W_79188 : bv 32 := 0x00100513.
Lemma F_79188 : CTabKA.F 0x79188 W_79188.
Proof. vm_refl. Qed.
Lemma D_79188 : CTabKA.D W_79188 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_7918c : bv 32 := 0x00bab4a3.
Lemma F_7918c : CTabKA.F 0x7918c W_7918c.
Proof. vm_refl. Qed.
Lemma D_7918c : CTabKA.D W_7918c (Store SZ8 21 11 9).
Proof. vm_refl. Qed.
Definition W_79190 : bv 32 := 0x00f56a63.
Lemma F_79190 : CTabKA.F 0x79190 W_79190.
Proof. vm_refl. Qed.
Lemma D_79190 : CTabKA.D W_79190 (Branch BC_LTU 10 15 20).
Proof. vm_refl. Qed.
Definition W_791a4 : bv 32 := 0x80040513.
Lemma F_791a4 : CTabKA.F 0x791a4 W_791a4.
Proof. vm_refl. Qed.
Lemma D_791a4 : CTabKA.D W_791a4 (OpImm ALU_ADD 10 8 2048).
Proof. vm_refl. Qed.
Definition W_791a8 : bv 32 := 0xfb050513.
Lemma F_791a8 : CTabKA.F 0x791a8 W_791a8.
Proof. vm_refl. Qed.
Lemma D_791a8 : CTabKA.D W_791a8 (OpImm ALU_ADD 10 10 4016).
Proof. vm_refl. Qed.
Definition W_791ac : bv 32 := 0x00090593.
Lemma F_791ac : CTabKA.F 0x791ac W_791ac.
Proof. vm_refl. Qed.
Lemma D_791ac : CTabKA.D W_791ac (OpImm ALU_ADD 11 18 0).
Proof. vm_refl. Qed.
Definition W_791b0 : bv 32 := 0x00040613.
Lemma F_791b0 : CTabKA.F 0x791b0 W_791b0.
Proof. vm_refl. Qed.
Lemma D_791b0 : CTabKA.D W_791b0 (OpImm ALU_ADD 12 8 0).
Proof. vm_refl. Qed.
Definition W_791b4 : bv 32 := 0x00000693.
Lemma F_791b4 : CTabKA.F 0x791b4 W_791b4.
Proof. vm_refl. Qed.
Lemma D_791b4 : CTabKA.D W_791b4 (OpImm ALU_ADD 13 0 0).
Proof. vm_refl. Qed.
Definition W_791b8 : bv 32 := 0x00098713.
Lemma F_791b8 : CTabKA.F 0x791b8 W_791b8.
Proof. vm_refl. Qed.
Lemma D_791b8 : CTabKA.D W_791b8 (OpImm ALU_ADD 14 19 0).
Proof. vm_refl. Qed.
Definition W_791bc : bv 32 := 0x368080ef.
Lemma F_791bc : CTabKA.F 0x791bc W_791bc.
Proof. vm_refl. Qed.
Lemma D_791bc : CTabKA.D W_791bc (Jal 1 33640).
Proof. vm_refl. Qed.
Definition W_791c0 : bv 32 := 0x80040593.
Lemma F_791c0 : CTabKA.F 0x791c0 W_791c0.
Proof. vm_refl. Qed.
Lemma D_791c0 : CTabKA.D W_791c0 (OpImm ALU_ADD 11 8 2048).
Proof. vm_refl. Qed.
Definition W_791c4 : bv 32 := 0xfb058593.
Lemma F_791c4 : CTabKA.F 0x791c4 W_791c4.
Proof. vm_refl. Qed.
Lemma D_791c4 : CTabKA.D W_791c4 (OpImm ALU_ADD 11 11 4016).
Proof. vm_refl. Qed.
Definition W_791c8 : bv 32 := 0x00048513.
Lemma F_791c8 : CTabKA.F 0x791c8 W_791c8.
Proof. vm_refl. Qed.
Lemma D_791c8 : CTabKA.D W_791c8 (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_791cc : bv 32 := 0x9bdd80ef.
Lemma F_791cc : CTabKA.F 0x791cc W_791cc.
Proof. vm_refl. Qed.
Lemma D_791cc : CTabKA.D W_791cc (Jal 1 1935804).
Proof. vm_refl. Qed.
Definition W_791d0 : bv 32 := 0x06010113.
Lemma F_791d0 : CTabKA.F 0x791d0 W_791d0.
Proof. vm_refl. Qed.
Lemma D_791d0 : CTabKA.D W_791d0 (OpImm ALU_ADD 2 2 96).
Proof. vm_refl. Qed.
Definition W_791d4 : bv 32 := 0x7e813083.
Lemma F_791d4 : CTabKA.F 0x791d4 W_791d4.
Proof. vm_refl. Qed.
Lemma D_791d4 : CTabKA.D W_791d4 (Load SZ8 true 1 2 2024).
Proof. vm_refl. Qed.
Definition W_791d8 : bv 32 := 0x7e013403.
Lemma F_791d8 : CTabKA.F 0x791d8 W_791d8.
Proof. vm_refl. Qed.
Lemma D_791d8 : CTabKA.D W_791d8 (Load SZ8 true 8 2 2016).
Proof. vm_refl. Qed.
Definition W_791dc : bv 32 := 0x7d813483.
Lemma F_791dc : CTabKA.F 0x791dc W_791dc.
Proof. vm_refl. Qed.
Lemma D_791dc : CTabKA.D W_791dc (Load SZ8 true 9 2 2008).
Proof. vm_refl. Qed.
Definition W_791e0 : bv 32 := 0x7d013903.
Lemma F_791e0 : CTabKA.F 0x791e0 W_791e0.
Proof. vm_refl. Qed.
Lemma D_791e0 : CTabKA.D W_791e0 (Load SZ8 true 18 2 2000).
Proof. vm_refl. Qed.
Definition W_791e4 : bv 32 := 0x7c813983.
Lemma F_791e4 : CTabKA.F 0x791e4 W_791e4.
Proof. vm_refl. Qed.
Lemma D_791e4 : CTabKA.D W_791e4 (Load SZ8 true 19 2 1992).
Proof. vm_refl. Qed.
Definition W_791e8 : bv 32 := 0x7c013a03.
Lemma F_791e8 : CTabKA.F 0x791e8 W_791e8.
Proof. vm_refl. Qed.
Lemma D_791e8 : CTabKA.D W_791e8 (Load SZ8 true 20 2 1984).
Proof. vm_refl. Qed.
Definition W_791ec : bv 32 := 0x7b813a83.
Lemma F_791ec : CTabKA.F 0x791ec W_791ec.
Proof. vm_refl. Qed.
Lemma D_791ec : CTabKA.D W_791ec (Load SZ8 true 21 2 1976).
Proof. vm_refl. Qed.
Definition W_791f0 : bv 32 := 0x7f010113.
Lemma F_791f0 : CTabKA.F 0x791f0 W_791f0.
Proof. vm_refl. Qed.
Lemma D_791f0 : CTabKA.D W_791f0 (OpImm ALU_ADD 2 2 2032).
Proof. vm_refl. Qed.
Definition W_791f4 : bv 32 := 0x00008067.
Lemma F_791f4 : CTabKA.F 0x791f4 W_791f4.
Proof. vm_refl. Qed.
Lemma D_791f4 : CTabKA.D W_791f4 (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_79608 : bv 32 := 0x81010113.
Lemma F_79608 : CTabKA.F 0x79608 W_79608.
Proof. vm_refl. Qed.
Lemma D_79608 : CTabKA.D W_79608 (OpImm ALU_ADD 2 2 2064).
Proof. vm_refl. Qed.
Definition W_7960c : bv 32 := 0x7e113423.
Lemma F_7960c : CTabKA.F 0x7960c W_7960c.
Proof. vm_refl. Qed.
Lemma D_7960c : CTabKA.D W_7960c (Store SZ8 2 1 2024).
Proof. vm_refl. Qed.
Definition W_79610 : bv 32 := 0x7e813023.
Lemma F_79610 : CTabKA.F 0x79610 W_79610.
Proof. vm_refl. Qed.
Lemma D_79610 : CTabKA.D W_79610 (Store SZ8 2 8 2016).
Proof. vm_refl. Qed.
Definition W_79614 : bv 32 := 0x7c913c23.
Lemma F_79614 : CTabKA.F 0x79614 W_79614.
Proof. vm_refl. Qed.
Lemma D_79614 : CTabKA.D W_79614 (Store SZ8 2 9 2008).
Proof. vm_refl. Qed.
Definition W_79618 : bv 32 := 0x7d213823.
Lemma F_79618 : CTabKA.F 0x79618 W_79618.
Proof. vm_refl. Qed.
Lemma D_79618 : CTabKA.D W_79618 (Store SZ8 2 18 2000).
Proof. vm_refl. Qed.
Definition W_7961c : bv 32 := 0x7d313423.
Lemma F_7961c : CTabKA.F 0x7961c W_7961c.
Proof. vm_refl. Qed.
Lemma D_7961c : CTabKA.D W_7961c (Store SZ8 2 19 1992).
Proof. vm_refl. Qed.
Definition W_79620 : bv 32 := 0x7d413023.
Lemma F_79620 : CTabKA.F 0x79620 W_79620.
Proof. vm_refl. Qed.
Lemma D_79620 : CTabKA.D W_79620 (Store SZ8 2 20 1984).
Proof. vm_refl. Qed.
Definition W_79624 : bv 32 := 0x7b513c23.
Lemma F_79624 : CTabKA.F 0x79624 W_79624.
Proof. vm_refl. Qed.
Lemma D_79624 : CTabKA.D W_79624 (Store SZ8 2 21 1976).
Proof. vm_refl. Qed.
Definition W_79628 : bv 32 := 0x7b613823.
Lemma F_79628 : CTabKA.F 0x79628 W_79628.
Proof. vm_refl. Qed.
Lemma D_79628 : CTabKA.D W_79628 (Store SZ8 2 22 1968).
Proof. vm_refl. Qed.
Definition W_7962c : bv 32 := 0x7f010413.
Lemma F_7962c : CTabKA.F 0x7962c W_7962c.
Proof. vm_refl. Qed.
Lemma D_7962c : CTabKA.D W_7962c (OpImm ALU_ADD 8 2 2032).
Proof. vm_refl. Qed.
Definition W_79630 : bv 32 := 0xf9010113.
Lemma F_79630 : CTabKA.F 0x79630 W_79630.
Proof. vm_refl. Qed.
Lemma D_79630 : CTabKA.D W_79630 (OpImm ALU_ADD 2 2 3984).
Proof. vm_refl. Qed.
Definition W_79634 : bv 32 := 0x00008993.
Lemma F_79634 : CTabKA.F 0x79634 W_79634.
Proof. vm_refl. Qed.
Lemma D_79634 : CTabKA.D W_79634 (OpImm ALU_ADD 19 1 0).
Proof. vm_refl. Qed.
Definition W_79638 : bv 32 := 0x00058493.
Lemma F_79638 : CTabKA.F 0x79638 W_79638.
Proof. vm_refl. Qed.
Lemma D_79638 : CTabKA.D W_79638 (OpImm ALU_ADD 9 11 0).
Proof. vm_refl. Qed.
Definition W_7963c : bv 32 := 0x00050913.
Lemma F_7963c : CTabKA.F 0x7963c W_7963c.
Proof. vm_refl. Qed.
Lemma D_7963c : CTabKA.D W_7963c (OpImm ALU_ADD 18 10 0).
Proof. vm_refl. Qed.
Definition W_79640 : bv 32 := 0x80040a93.
Lemma F_79640 : CTabKA.F 0x79640 W_79640.
Proof. vm_refl. Qed.
Lemma D_79640 : CTabKA.D W_79640 (OpImm ALU_ADD 21 8 2048).
Proof. vm_refl. Qed.
Definition W_79644 : bv 32 := 0xfa8a8a93.
Lemma F_79644 : CTabKA.F 0x79644 W_79644.
Proof. vm_refl. Qed.
Lemma D_79644 : CTabKA.D W_79644 (OpImm ALU_ADD 21 21 4008).
Proof. vm_refl. Qed.
Definition W_79648 : bv 32 := 0x80040513.
Lemma F_79648 : CTabKA.F 0x79648 W_79648.
Proof. vm_refl. Qed.
Lemma D_79648 : CTabKA.D W_79648 (OpImm ALU_ADD 10 8 2048).
Proof. vm_refl. Qed.
Definition W_7964c : bv 32 := 0xfb850513.
Lemma F_7964c : CTabKA.F 0x7964c W_7964c.
Proof. vm_refl. Qed.
Lemma D_7964c : CTabKA.D W_7964c (OpImm ALU_ADD 10 10 4024).
Proof. vm_refl. Qed.
Definition W_79650 : bv 32 := 0x7ffa8b13.
Lemma F_79650 : CTabKA.F 0x79650 W_79650.
Proof. vm_refl. Qed.
Lemma D_79650 : CTabKA.D W_79650 (OpImm ALU_ADD 22 21 2047).
Proof. vm_refl. Qed.
Definition W_79654 : bv 32 := 0x000b34a3.
Lemma F_79654 : CTabKA.F 0x79654 W_79654.
Proof. vm_refl. Qed.
Lemma D_79654 : CTabKA.D W_79654 (Store SZ8 22 0 9).
Proof. vm_refl. Qed.
Definition W_79658 : bv 32 := 0x00aab023.
Lemma F_79658 : CTabKA.F 0x79658 W_79658.
Proof. vm_refl. Qed.
Lemma D_79658 : CTabKA.D W_79658 (Store SZ8 21 10 0).
Proof. vm_refl. Qed.
Definition W_7965c : bv 32 := 0x000ab423.
Lemma F_7965c : CTabKA.F 0x7965c W_7965c.
Proof. vm_refl. Qed.
Lemma D_7965c : CTabKA.D W_7965c (Store SZ8 21 0 8).
Proof. vm_refl. Qed.
Definition W_79660 : bv 32 := 0x6b5070ef.
Lemma F_79660 : CTabKA.F 0x79660 W_79660.
Proof. vm_refl. Qed.
Lemma D_79660 : CTabKA.D W_79660 (Jal 1 32436).
Proof. vm_refl. Qed.
Definition W_79664 : bv 32 := 0x00200593.
Lemma F_79664 : CTabKA.F 0x79664 W_79664.
Proof. vm_refl. Qed.
Lemma D_79664 : CTabKA.D W_79664 (OpImm ALU_ADD 11 0 2).
Proof. vm_refl. Qed.
Definition W_79668 : bv 32 := 0x02a5ea63.
Lemma F_79668 : CTabKA.F 0x79668 W_79668.
Proof. vm_refl. Qed.
Lemma D_79668 : CTabKA.D W_79668 (Branch BC_LTU 11 10 52).
Proof. vm_refl. Qed.
Definition W_7969c : bv 32 := 0x155200ef.
Lemma F_7969c : CTabKA.F 0x7969c W_7969c.
Proof. vm_refl. Qed.
Lemma D_7969c : CTabKA.D W_7969c (Jal 1 133460).
Proof. vm_refl. Qed.
Definition W_796a0 : bv 32 := 0x000b9597.
Lemma F_796a0 : CTabKA.F 0x796a0 W_796a0.
Proof. vm_refl. Qed.
Lemma D_796a0 : CTabKA.D W_796a0 (Auipc 11 185).
Proof. vm_refl. Qed.
Definition W_796a4 : bv 32 := 0xf885b583.
Lemma F_796a4 : CTabKA.F 0x796a4 W_796a4.
Proof. vm_refl. Qed.
Lemma D_796a4 : CTabKA.D W_796a4 (Load SZ8 true 11 11 3976).
Proof. vm_refl. Qed.
Definition W_796a8 : bv 32 := 0x0225ca03.
Lemma F_796a8 : CTabKA.F 0x796a8 W_796a8.
Proof. vm_refl. Qed.
Lemma D_796a8 : CTabKA.D W_796a8 (Load SZ1 false 20 11 34).
Proof. vm_refl. Qed.
Definition W_796ac : bv 32 := 0x00050993.
Lemma F_796ac : CTabKA.F 0x796ac W_796ac.
Proof. vm_refl. Qed.
Lemma D_796ac : CTabKA.D W_796ac (OpImm ALU_ADD 19 10 0).
Proof. vm_refl. Qed.
Definition W_796b0 : bv 32 := 0x665070ef.
Lemma F_796b0 : CTabKA.F 0x796b0 W_796b0.
Proof. vm_refl. Qed.
Lemma D_796b0 : CTabKA.D W_796b0 (Jal 1 32356).
Proof. vm_refl. Qed.
Definition W_796b4 : bv 32 := 0x00050793.
Lemma F_796b4 : CTabKA.F 0x796b4 W_796b4.
Proof. vm_refl. Qed.
Lemma D_796b4 : CTabKA.D W_796b4 (OpImm ALU_ADD 15 10 0).
Proof. vm_refl. Qed.
Definition W_796b8 : bv 32 := 0x00153513.
Lemma F_796b8 : CTabKA.F 0x796b8 W_796b8.
Proof. vm_refl. Qed.
Lemma D_796b8 : CTabKA.D W_796b8 (OpImm ALU_SLTU 10 10 1).
Proof. vm_refl. Qed.
Definition W_796bc : bv 32 := 0xfff50513.
Lemma F_796bc : CTabKA.F 0x796bc W_796bc.
Proof. vm_refl. Qed.
Lemma D_796bc : CTabKA.D W_796bc (OpImm ALU_ADD 10 10 4095).
Proof. vm_refl. Qed.
Definition W_796c0 : bv 32 := 0x008575b3.
Lemma F_796c0 : CTabKA.F 0x796c0 W_796c0.
Proof. vm_refl. Qed.
Lemma D_796c0 : CTabKA.D W_796c0 (Op ALU_AND 11 10 8).
Proof. vm_refl. Qed.
Definition W_796c4 : bv 32 := 0x00100513.
Lemma F_796c4 : CTabKA.F 0x796c4 W_796c4.
Proof. vm_refl. Qed.
Lemma D_796c4 : CTabKA.D W_796c4 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_796c8 : bv 32 := 0x00bb34a3.
Lemma F_796c8 : CTabKA.F 0x796c8 W_796c8.
Proof. vm_refl. Qed.
Lemma D_796c8 : CTabKA.D W_796c8 (Store SZ8 22 11 9).
Proof. vm_refl. Qed.
Definition W_796cc : bv 32 := 0x00f56a63.
Lemma F_796cc : CTabKA.F 0x796cc W_796cc.
Proof. vm_refl. Qed.
Lemma D_796cc : CTabKA.D W_796cc (Branch BC_LTU 10 15 20).
Proof. vm_refl. Qed.
Definition W_796e0 : bv 32 := 0x80040513.
Lemma F_796e0 : CTabKA.F 0x796e0 W_796e0.
Proof. vm_refl. Qed.
Lemma D_796e0 : CTabKA.D W_796e0 (OpImm ALU_ADD 10 8 2048).
Proof. vm_refl. Qed.
Definition W_796e4 : bv 32 := 0xfa850513.
Lemma F_796e4 : CTabKA.F 0x796e4 W_796e4.
Proof. vm_refl. Qed.
Lemma D_796e4 : CTabKA.D W_796e4 (OpImm ALU_ADD 10 10 4008).
Proof. vm_refl. Qed.
Definition W_796e8 : bv 32 := 0x00098593.
Lemma F_796e8 : CTabKA.F 0x796e8 W_796e8.
Proof. vm_refl. Qed.
Lemma D_796e8 : CTabKA.D W_796e8 (OpImm ALU_ADD 11 19 0).
Proof. vm_refl. Qed.
Definition W_796ec : bv 32 := 0x00040613.
Lemma F_796ec : CTabKA.F 0x796ec W_796ec.
Proof. vm_refl. Qed.
Lemma D_796ec : CTabKA.D W_796ec (OpImm ALU_ADD 12 8 0).
Proof. vm_refl. Qed.
Definition W_796f0 : bv 32 := 0x00000693.
Lemma F_796f0 : CTabKA.F 0x796f0 W_796f0.
Proof. vm_refl. Qed.
Lemma D_796f0 : CTabKA.D W_796f0 (OpImm ALU_ADD 13 0 0).
Proof. vm_refl. Qed.
Definition W_796f4 : bv 32 := 0x000a0713.
Lemma F_796f4 : CTabKA.F 0x796f4 W_796f4.
Proof. vm_refl. Qed.
Lemma D_796f4 : CTabKA.D W_796f4 (OpImm ALU_ADD 14 20 0).
Proof. vm_refl. Qed.
Definition W_796f8 : bv 32 := 0x62d070ef.
Lemma F_796f8 : CTabKA.F 0x796f8 W_796f8.
Proof. vm_refl. Qed.
Lemma D_796f8 : CTabKA.D W_796f8 (Jal 1 32300).
Proof. vm_refl. Qed.
Definition W_796fc : bv 32 := 0x80040613.
Lemma F_796fc : CTabKA.F 0x796fc W_796fc.
Proof. vm_refl. Qed.
Lemma D_796fc : CTabKA.D W_796fc (OpImm ALU_ADD 12 8 2048).
Proof. vm_refl. Qed.
Definition W_79700 : bv 32 := 0xfa860613.
Lemma F_79700 : CTabKA.F 0x79700 W_79700.
Proof. vm_refl. Qed.
Lemma D_79700 : CTabKA.D W_79700 (OpImm ALU_ADD 12 12 4008).
Proof. vm_refl. Qed.
Definition W_79704 : bv 32 := 0x00090513.
Lemma F_79704 : CTabKA.F 0x79704 W_79704.
Proof. vm_refl. Qed.
Lemma D_79704 : CTabKA.D W_79704 (OpImm ALU_ADD 10 18 0).
Proof. vm_refl. Qed.
Definition W_79708 : bv 32 := 0x00048593.
Lemma F_79708 : CTabKA.F 0x79708 W_79708.
Proof. vm_refl. Qed.
Lemma D_79708 : CTabKA.D W_79708 (OpImm ALU_ADD 11 9 0).
Proof. vm_refl. Qed.
Definition W_7970c : bv 32 := 0x86cd90ef.
Lemma F_7970c : CTabKA.F 0x7970c W_7970c.
Proof. vm_refl. Qed.
Lemma D_7970c : CTabKA.D W_7970c (Jal 1 1937516).
Proof. vm_refl. Qed.
Definition W_79710 : bv 32 := 0x07010113.
Lemma F_79710 : CTabKA.F 0x79710 W_79710.
Proof. vm_refl. Qed.
Lemma D_79710 : CTabKA.D W_79710 (OpImm ALU_ADD 2 2 112).
Proof. vm_refl. Qed.
Definition W_79714 : bv 32 := 0x7e813083.
Lemma F_79714 : CTabKA.F 0x79714 W_79714.
Proof. vm_refl. Qed.
Lemma D_79714 : CTabKA.D W_79714 (Load SZ8 true 1 2 2024).
Proof. vm_refl. Qed.
Definition W_79718 : bv 32 := 0x7e013403.
Lemma F_79718 : CTabKA.F 0x79718 W_79718.
Proof. vm_refl. Qed.
Lemma D_79718 : CTabKA.D W_79718 (Load SZ8 true 8 2 2016).
Proof. vm_refl. Qed.
Definition W_7971c : bv 32 := 0x7d813483.
Lemma F_7971c : CTabKA.F 0x7971c W_7971c.
Proof. vm_refl. Qed.
Lemma D_7971c : CTabKA.D W_7971c (Load SZ8 true 9 2 2008).
Proof. vm_refl. Qed.
Definition W_79720 : bv 32 := 0x7d013903.
Lemma F_79720 : CTabKA.F 0x79720 W_79720.
Proof. vm_refl. Qed.
Lemma D_79720 : CTabKA.D W_79720 (Load SZ8 true 18 2 2000).
Proof. vm_refl. Qed.
Definition W_79724 : bv 32 := 0x7c813983.
Lemma F_79724 : CTabKA.F 0x79724 W_79724.
Proof. vm_refl. Qed.
Lemma D_79724 : CTabKA.D W_79724 (Load SZ8 true 19 2 1992).
Proof. vm_refl. Qed.
Definition W_79728 : bv 32 := 0x7c013a03.
Lemma F_79728 : CTabKA.F 0x79728 W_79728.
Proof. vm_refl. Qed.
Lemma D_79728 : CTabKA.D W_79728 (Load SZ8 true 20 2 1984).
Proof. vm_refl. Qed.
Definition W_7972c : bv 32 := 0x7b813a83.
Lemma F_7972c : CTabKA.F 0x7972c W_7972c.
Proof. vm_refl. Qed.
Lemma D_7972c : CTabKA.D W_7972c (Load SZ8 true 21 2 1976).
Proof. vm_refl. Qed.
Definition W_79730 : bv 32 := 0x7b013b03.
Lemma F_79730 : CTabKA.F 0x79730 W_79730.
Proof. vm_refl. Qed.
Lemma D_79730 : CTabKA.D W_79730 (Load SZ8 true 22 2 1968).
Proof. vm_refl. Qed.
Definition W_79734 : bv 32 := 0x7f010113.
Lemma F_79734 : CTabKA.F 0x79734 W_79734.
Proof. vm_refl. Qed.
Lemma D_79734 : CTabKA.D W_79734 (OpImm ALU_ADD 2 2 2032).
Proof. vm_refl. Qed.
Definition W_79738 : bv 32 := 0x00008067.
Lemma F_79738 : CTabKA.F 0x79738 W_79738.
Proof. vm_refl. Qed.
Lemma D_79738 : CTabKA.D W_79738 (Jalr 0 1 0).
Proof. vm_refl. Qed.

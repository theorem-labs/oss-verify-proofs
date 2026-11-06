(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require CTabKB.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
Open Scope bv_scope.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Definition W_7918c : bv 32 := 0x0100006f.
Lemma F_7918c : CTabKB.F 0x7918c W_7918c.
Proof. vm_refl. Qed.
Lemma D_7918c : CTabKB.D W_7918c (Jal 0 16).
Proof. vm_refl. Qed.
Definition W_79190 : bv 32 := 0x1dc0006f.
Lemma F_79190 : CTabKB.F 0x79190 W_79190.
Proof. vm_refl. Qed.
Lemma D_79190 : CTabKB.D W_79190 (Jal 0 476).
Proof. vm_refl. Qed.
Definition W_79198 : bv 32 := 0x7400006f.
Lemma F_79198 : CTabKB.F 0x79198 W_79198.
Proof. vm_refl. Qed.
Lemma D_79198 : CTabKB.D W_79198 (Jal 0 1856).
Proof. vm_refl. Qed.
Definition W_7919c : bv 32 := 0x81010113.
Lemma F_7919c : CTabKB.F 0x7919c W_7919c.
Proof. vm_refl. Qed.
Lemma D_7919c : CTabKB.D W_7919c (OpImm ALU_ADD 2 2 2064).
Proof. vm_refl. Qed.
Definition W_791a0 : bv 32 := 0x7e113423.
Lemma F_791a0 : CTabKB.F 0x791a0 W_791a0.
Proof. vm_refl. Qed.
Lemma D_791a0 : CTabKB.D W_791a0 (Store SZ8 2 1 2024).
Proof. vm_refl. Qed.
Definition W_791a4 : bv 32 := 0x7e813023.
Lemma F_791a4 : CTabKB.F 0x791a4 W_791a4.
Proof. vm_refl. Qed.
Lemma D_791a4 : CTabKB.D W_791a4 (Store SZ8 2 8 2016).
Proof. vm_refl. Qed.
Definition W_791a8 : bv 32 := 0x7c913c23.
Lemma F_791a8 : CTabKB.F 0x791a8 W_791a8.
Proof. vm_refl. Qed.
Lemma D_791a8 : CTabKB.D W_791a8 (Store SZ8 2 9 2008).
Proof. vm_refl. Qed.
Definition W_791ac : bv 32 := 0x7d213823.
Lemma F_791ac : CTabKB.F 0x791ac W_791ac.
Proof. vm_refl. Qed.
Lemma D_791ac : CTabKB.D W_791ac (Store SZ8 2 18 2000).
Proof. vm_refl. Qed.
Definition W_791b0 : bv 32 := 0x7d313423.
Lemma F_791b0 : CTabKB.F 0x791b0 W_791b0.
Proof. vm_refl. Qed.
Lemma D_791b0 : CTabKB.D W_791b0 (Store SZ8 2 19 1992).
Proof. vm_refl. Qed.
Definition W_791b4 : bv 32 := 0x7d413023.
Lemma F_791b4 : CTabKB.F 0x791b4 W_791b4.
Proof. vm_refl. Qed.
Lemma D_791b4 : CTabKB.D W_791b4 (Store SZ8 2 20 1984).
Proof. vm_refl. Qed.
Definition W_791b8 : bv 32 := 0x7b513c23.
Lemma F_791b8 : CTabKB.F 0x791b8 W_791b8.
Proof. vm_refl. Qed.
Lemma D_791b8 : CTabKB.D W_791b8 (Store SZ8 2 21 1976).
Proof. vm_refl. Qed.
Definition W_791bc : bv 32 := 0x7f010413.
Lemma F_791bc : CTabKB.F 0x791bc W_791bc.
Proof. vm_refl. Qed.
Lemma D_791bc : CTabKB.D W_791bc (OpImm ALU_ADD 8 2 2032).
Proof. vm_refl. Qed.
Definition W_791c0 : bv 32 := 0xfa010113.
Lemma F_791c0 : CTabKB.F 0x791c0 W_791c0.
Proof. vm_refl. Qed.
Lemma D_791c0 : CTabKB.D W_791c0 (OpImm ALU_ADD 2 2 4000).
Proof. vm_refl. Qed.
Definition W_791c4 : bv 32 := 0x00008913.
Lemma F_791c4 : CTabKB.F 0x791c4 W_791c4.
Proof. vm_refl. Qed.
Lemma D_791c4 : CTabKB.D W_791c4 (OpImm ALU_ADD 18 1 0).
Proof. vm_refl. Qed.
Definition W_791c8 : bv 32 := 0x00050493.
Lemma F_791c8 : CTabKB.F 0x791c8 W_791c8.
Proof. vm_refl. Qed.
Lemma D_791c8 : CTabKB.D W_791c8 (OpImm ALU_ADD 9 10 0).
Proof. vm_refl. Qed.
Definition W_791cc : bv 32 := 0x10c0c0ef.
Lemma F_791cc : CTabKB.F 0x791cc W_791cc.
Proof. vm_refl. Qed.
Lemma D_791cc : CTabKB.D W_791cc (Jal 1 49420).
Proof. vm_refl. Qed.
Definition W_791d0 : bv 32 := 0x02f4d593.
Lemma F_791d0 : CTabKB.F 0x791d0 W_791d0.
Proof. vm_refl. Qed.
Lemma D_791d0 : CTabKB.D W_791d0 (ShiftImm ALU_SRL 11 9 47).
Proof. vm_refl. Qed.
Definition W_791d4 : bv 32 := 0x0a059063.
Lemma F_791d4 : CTabKB.F 0x791d4 W_791d4.
Proof. vm_refl. Qed.
Lemma D_791d4 : CTabKB.D W_791d4 (Branch BC_NE 11 0 160).
Proof. vm_refl. Qed.
Definition W_791d8 : bv 32 := 0x0204d593.
Lemma F_791d8 : CTabKB.F 0x791d8 W_791d8.
Proof. vm_refl. Qed.
Lemma D_791d8 : CTabKB.D W_791d8 (ShiftImm ALU_SRL 11 9 32).
Proof. vm_refl. Qed.
Definition W_791dc : bv 32 := 0x00359613.
Lemma F_791dc : CTabKB.F 0x791dc W_791dc.
Proof. vm_refl. Qed.
Lemma D_791dc : CTabKB.D W_791dc (ShiftImm ALU_SLL 12 11 3).
Proof. vm_refl. Qed.
Definition W_791e0 : bv 32 := 0x00c50633.
Lemma F_791e0 : CTabKB.F 0x791e0 W_791e0.
Proof. vm_refl. Qed.
Lemma D_791e0 : CTabKB.D W_791e0 (Op ALU_ADD 12 10 12).
Proof. vm_refl. Qed.
Definition W_791e4 : bv 32 := 0x00863683.
Lemma F_791e4 : CTabKB.F 0x791e4 W_791e4.
Proof. vm_refl. Qed.
Lemma D_791e4 : CTabKB.D W_791e4 (Load SZ8 true 13 12 8).
Proof. vm_refl. Qed.
Definition W_791e8 : bv 32 := 0x0230000f.
Lemma F_791e8 : CTabKB.F 0x791e8 W_791e8.
Proof. vm_refl. Qed.
Lemma D_791e8 : CTabKB.D W_791e8 (Fence 0 2 3 0 0).
Proof. vm_refl. Qed.
Definition W_791ec : bv 32 := 0x08068463.
Lemma F_791ec : CTabKB.F 0x791ec W_791ec.
Proof. vm_refl. Qed.
Lemma D_791ec : CTabKB.D W_791ec (Branch BC_EQ 13 0 136).
Proof. vm_refl. Qed.
Definition W_79274 : bv 32 := 0x80040a13.
Lemma F_79274 : CTabKB.F 0x79274 W_79274.
Proof. vm_refl. Qed.
Lemma D_79274 : CTabKB.D W_79274 (OpImm ALU_ADD 20 8 2048).
Proof. vm_refl. Qed.
Definition W_79278 : bv 32 := 0xfb0a0a13.
Lemma F_79278 : CTabKB.F 0x79278 W_79278.
Proof. vm_refl. Qed.
Lemma D_79278 : CTabKB.D W_79278 (OpImm ALU_ADD 20 20 4016).
Proof. vm_refl. Qed.
Definition W_7927c : bv 32 := 0x80040513.
Lemma F_7927c : CTabKB.F 0x7927c W_7927c.
Proof. vm_refl. Qed.
Lemma D_7927c : CTabKB.D W_7927c (OpImm ALU_ADD 10 8 2048).
Proof. vm_refl. Qed.
Definition W_79280 : bv 32 := 0xfc050513.
Lemma F_79280 : CTabKB.F 0x79280 W_79280.
Proof. vm_refl. Qed.
Lemma D_79280 : CTabKB.D W_79280 (OpImm ALU_ADD 10 10 4032).
Proof. vm_refl. Qed.
Definition W_79284 : bv 32 := 0x7ffa0a93.
Lemma F_79284 : CTabKB.F 0x79284 W_79284.
Proof. vm_refl. Qed.
Lemma D_79284 : CTabKB.D W_79284 (OpImm ALU_ADD 21 20 2047).
Proof. vm_refl. Qed.
Definition W_79288 : bv 32 := 0x000ab4a3.
Lemma F_79288 : CTabKB.F 0x79288 W_79288.
Proof. vm_refl. Qed.
Lemma D_79288 : CTabKB.D W_79288 (Store SZ8 21 0 9).
Proof. vm_refl. Qed.
Definition W_7928c : bv 32 := 0x00aa3023.
Lemma F_7928c : CTabKB.F 0x7928c W_7928c.
Proof. vm_refl. Qed.
Lemma D_7928c : CTabKB.D W_7928c (Store SZ8 20 10 0).
Proof. vm_refl. Qed.
Definition W_79290 : bv 32 := 0x000a3423.
Lemma F_79290 : CTabKB.F 0x79290 W_79290.
Proof. vm_refl. Qed.
Lemma D_79290 : CTabKB.D W_79290 (Store SZ8 20 0 8).
Proof. vm_refl. Qed.
Definition W_79294 : bv 32 := 0x550080ef.
Lemma F_79294 : CTabKB.F 0x79294 W_79294.
Proof. vm_refl. Qed.
Lemma D_79294 : CTabKB.D W_79294 (Jal 1 34128).
Proof. vm_refl. Qed.
Definition W_79298 : bv 32 := 0x00200593.
Lemma F_79298 : CTabKB.F 0x79298 W_79298.
Proof. vm_refl. Qed.
Lemma D_79298 : CTabKB.D W_79298 (OpImm ALU_ADD 11 0 2).
Proof. vm_refl. Qed.
Definition W_7929c : bv 32 := 0x02a5ea63.
Lemma F_7929c : CTabKB.F 0x7929c W_7929c.
Proof. vm_refl. Qed.
Lemma D_7929c : CTabKB.D W_7929c (Branch BC_LTU 11 10 52).
Proof. vm_refl. Qed.
Definition W_792d0 : bv 32 := 0x7f1200ef.
Lemma F_792d0 : CTabKB.F 0x792d0 W_792d0.
Proof. vm_refl. Qed.
Lemma D_792d0 : CTabKB.D W_792d0 (Jal 1 135152).
Proof. vm_refl. Qed.
Definition W_792d4 : bv 32 := 0x000bb597.
Lemma F_792d4 : CTabKB.F 0x792d4 W_792d4.
Proof. vm_refl. Qed.
Lemma D_792d4 : CTabKB.D W_792d4 (Auipc 11 187).
Proof. vm_refl. Qed.
Definition W_792d8 : bv 32 := 0x0bc5b583.
Lemma F_792d8 : CTabKB.F 0x792d8 W_792d8.
Proof. vm_refl. Qed.
Lemma D_792d8 : CTabKB.D W_792d8 (Load SZ8 true 11 11 188).
Proof. vm_refl. Qed.
Definition W_792dc : bv 32 := 0x0225c983.
Lemma F_792dc : CTabKB.F 0x792dc W_792dc.
Proof. vm_refl. Qed.
Lemma D_792dc : CTabKB.D W_792dc (Load SZ1 false 19 11 34).
Proof. vm_refl. Qed.
Definition W_792e0 : bv 32 := 0x00050913.
Lemma F_792e0 : CTabKB.F 0x792e0 W_792e0.
Proof. vm_refl. Qed.
Lemma D_792e0 : CTabKB.D W_792e0 (OpImm ALU_ADD 18 10 0).
Proof. vm_refl. Qed.
Definition W_792e4 : bv 32 := 0x500080ef.
Lemma F_792e4 : CTabKB.F 0x792e4 W_792e4.
Proof. vm_refl. Qed.
Lemma D_792e4 : CTabKB.D W_792e4 (Jal 1 34048).
Proof. vm_refl. Qed.
Definition W_792e8 : bv 32 := 0x00050793.
Lemma F_792e8 : CTabKB.F 0x792e8 W_792e8.
Proof. vm_refl. Qed.
Lemma D_792e8 : CTabKB.D W_792e8 (OpImm ALU_ADD 15 10 0).
Proof. vm_refl. Qed.
Definition W_792ec : bv 32 := 0x00153513.
Lemma F_792ec : CTabKB.F 0x792ec W_792ec.
Proof. vm_refl. Qed.
Lemma D_792ec : CTabKB.D W_792ec (OpImm ALU_SLTU 10 10 1).
Proof. vm_refl. Qed.
Definition W_792f0 : bv 32 := 0xfff50513.
Lemma F_792f0 : CTabKB.F 0x792f0 W_792f0.
Proof. vm_refl. Qed.
Lemma D_792f0 : CTabKB.D W_792f0 (OpImm ALU_ADD 10 10 4095).
Proof. vm_refl. Qed.
Definition W_792f4 : bv 32 := 0x008575b3.
Lemma F_792f4 : CTabKB.F 0x792f4 W_792f4.
Proof. vm_refl. Qed.
Lemma D_792f4 : CTabKB.D W_792f4 (Op ALU_AND 11 10 8).
Proof. vm_refl. Qed.
Definition W_792f8 : bv 32 := 0x00100513.
Lemma F_792f8 : CTabKB.F 0x792f8 W_792f8.
Proof. vm_refl. Qed.
Lemma D_792f8 : CTabKB.D W_792f8 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_792fc : bv 32 := 0x00bab4a3.
Lemma F_792fc : CTabKB.F 0x792fc W_792fc.
Proof. vm_refl. Qed.
Lemma D_792fc : CTabKB.D W_792fc (Store SZ8 21 11 9).
Proof. vm_refl. Qed.
Definition W_79300 : bv 32 := 0x00f56a63.
Lemma F_79300 : CTabKB.F 0x79300 W_79300.
Proof. vm_refl. Qed.
Lemma D_79300 : CTabKB.D W_79300 (Branch BC_LTU 10 15 20).
Proof. vm_refl. Qed.
Definition W_79314 : bv 32 := 0x80040513.
Lemma F_79314 : CTabKB.F 0x79314 W_79314.
Proof. vm_refl. Qed.
Lemma D_79314 : CTabKB.D W_79314 (OpImm ALU_ADD 10 8 2048).
Proof. vm_refl. Qed.
Definition W_79318 : bv 32 := 0xfb050513.
Lemma F_79318 : CTabKB.F 0x79318 W_79318.
Proof. vm_refl. Qed.
Lemma D_79318 : CTabKB.D W_79318 (OpImm ALU_ADD 10 10 4016).
Proof. vm_refl. Qed.
Definition W_7931c : bv 32 := 0x00090593.
Lemma F_7931c : CTabKB.F 0x7931c W_7931c.
Proof. vm_refl. Qed.
Lemma D_7931c : CTabKB.D W_7931c (OpImm ALU_ADD 11 18 0).
Proof. vm_refl. Qed.
Definition W_79320 : bv 32 := 0x00040613.
Lemma F_79320 : CTabKB.F 0x79320 W_79320.
Proof. vm_refl. Qed.
Lemma D_79320 : CTabKB.D W_79320 (OpImm ALU_ADD 12 8 0).
Proof. vm_refl. Qed.
Definition W_79324 : bv 32 := 0x00000693.
Lemma F_79324 : CTabKB.F 0x79324 W_79324.
Proof. vm_refl. Qed.
Lemma D_79324 : CTabKB.D W_79324 (OpImm ALU_ADD 13 0 0).
Proof. vm_refl. Qed.
Definition W_79328 : bv 32 := 0x00098713.
Lemma F_79328 : CTabKB.F 0x79328 W_79328.
Proof. vm_refl. Qed.
Lemma D_79328 : CTabKB.D W_79328 (OpImm ALU_ADD 14 19 0).
Proof. vm_refl. Qed.
Definition W_7932c : bv 32 := 0x4c8080ef.
Lemma F_7932c : CTabKB.F 0x7932c W_7932c.
Proof. vm_refl. Qed.
Lemma D_7932c : CTabKB.D W_7932c (Jal 1 33992).
Proof. vm_refl. Qed.
Definition W_79330 : bv 32 := 0x80040593.
Lemma F_79330 : CTabKB.F 0x79330 W_79330.
Proof. vm_refl. Qed.
Lemma D_79330 : CTabKB.D W_79330 (OpImm ALU_ADD 11 8 2048).
Proof. vm_refl. Qed.
Definition W_79334 : bv 32 := 0xfb058593.
Lemma F_79334 : CTabKB.F 0x79334 W_79334.
Proof. vm_refl. Qed.
Lemma D_79334 : CTabKB.D W_79334 (OpImm ALU_ADD 11 11 4016).
Proof. vm_refl. Qed.
Definition W_79338 : bv 32 := 0x00100613.
Lemma F_79338 : CTabKB.F 0x79338 W_79338.
Proof. vm_refl. Qed.
Lemma D_79338 : CTabKB.D W_79338 (OpImm ALU_ADD 12 0 1).
Proof. vm_refl. Qed.
Definition W_7933c : bv 32 := 0x00048513.
Lemma F_7933c : CTabKB.F 0x7933c W_7933c.
Proof. vm_refl. Qed.
Lemma D_7933c : CTabKB.D W_7933c (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_79340 : bv 32 := 0x839d80ef.
Lemma F_79340 : CTabKB.F 0x79340 W_79340.
Proof. vm_refl. Qed.
Lemma D_79340 : CTabKB.D W_79340 (Jal 1 1935416).
Proof. vm_refl. Qed.
Definition W_79344 : bv 32 := 0x06010113.
Lemma F_79344 : CTabKB.F 0x79344 W_79344.
Proof. vm_refl. Qed.
Lemma D_79344 : CTabKB.D W_79344 (OpImm ALU_ADD 2 2 96).
Proof. vm_refl. Qed.
Definition W_79348 : bv 32 := 0x7e813083.
Lemma F_79348 : CTabKB.F 0x79348 W_79348.
Proof. vm_refl. Qed.
Lemma D_79348 : CTabKB.D W_79348 (Load SZ8 true 1 2 2024).
Proof. vm_refl. Qed.
Definition W_7934c : bv 32 := 0x7e013403.
Lemma F_7934c : CTabKB.F 0x7934c W_7934c.
Proof. vm_refl. Qed.
Lemma D_7934c : CTabKB.D W_7934c (Load SZ8 true 8 2 2016).
Proof. vm_refl. Qed.
Definition W_79350 : bv 32 := 0x7d813483.
Lemma F_79350 : CTabKB.F 0x79350 W_79350.
Proof. vm_refl. Qed.
Lemma D_79350 : CTabKB.D W_79350 (Load SZ8 true 9 2 2008).
Proof. vm_refl. Qed.
Definition W_79354 : bv 32 := 0x7d013903.
Lemma F_79354 : CTabKB.F 0x79354 W_79354.
Proof. vm_refl. Qed.
Lemma D_79354 : CTabKB.D W_79354 (Load SZ8 true 18 2 2000).
Proof. vm_refl. Qed.
Definition W_79358 : bv 32 := 0x7c813983.
Lemma F_79358 : CTabKB.F 0x79358 W_79358.
Proof. vm_refl. Qed.
Lemma D_79358 : CTabKB.D W_79358 (Load SZ8 true 19 2 1992).
Proof. vm_refl. Qed.
Definition W_7935c : bv 32 := 0x7c013a03.
Lemma F_7935c : CTabKB.F 0x7935c W_7935c.
Proof. vm_refl. Qed.
Lemma D_7935c : CTabKB.D W_7935c (Load SZ8 true 20 2 1984).
Proof. vm_refl. Qed.
Definition W_79360 : bv 32 := 0x7b813a83.
Lemma F_79360 : CTabKB.F 0x79360 W_79360.
Proof. vm_refl. Qed.
Lemma D_79360 : CTabKB.D W_79360 (Load SZ8 true 21 2 1976).
Proof. vm_refl. Qed.
Definition W_79364 : bv 32 := 0x7f010113.
Lemma F_79364 : CTabKB.F 0x79364 W_79364.
Proof. vm_refl. Qed.
Lemma D_79364 : CTabKB.D W_79364 (OpImm ALU_ADD 2 2 2032).
Proof. vm_refl. Qed.
Definition W_79368 : bv 32 := 0x00008067.
Lemma F_79368 : CTabKB.F 0x79368 W_79368.
Proof. vm_refl. Qed.
Lemma D_79368 : CTabKB.D W_79368 (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_7936c : bv 32 := 0x81010113.
Lemma F_7936c : CTabKB.F 0x7936c W_7936c.
Proof. vm_refl. Qed.
Lemma D_7936c : CTabKB.D W_7936c (OpImm ALU_ADD 2 2 2064).
Proof. vm_refl. Qed.
Definition W_79370 : bv 32 := 0x7e113423.
Lemma F_79370 : CTabKB.F 0x79370 W_79370.
Proof. vm_refl. Qed.
Lemma D_79370 : CTabKB.D W_79370 (Store SZ8 2 1 2024).
Proof. vm_refl. Qed.
Definition W_79374 : bv 32 := 0x7e813023.
Lemma F_79374 : CTabKB.F 0x79374 W_79374.
Proof. vm_refl. Qed.
Lemma D_79374 : CTabKB.D W_79374 (Store SZ8 2 8 2016).
Proof. vm_refl. Qed.
Definition W_79378 : bv 32 := 0x7c913c23.
Lemma F_79378 : CTabKB.F 0x79378 W_79378.
Proof. vm_refl. Qed.
Lemma D_79378 : CTabKB.D W_79378 (Store SZ8 2 9 2008).
Proof. vm_refl. Qed.
Definition W_7937c : bv 32 := 0x7d213823.
Lemma F_7937c : CTabKB.F 0x7937c W_7937c.
Proof. vm_refl. Qed.
Lemma D_7937c : CTabKB.D W_7937c (Store SZ8 2 18 2000).
Proof. vm_refl. Qed.
Definition W_79380 : bv 32 := 0x7d313423.
Lemma F_79380 : CTabKB.F 0x79380 W_79380.
Proof. vm_refl. Qed.
Lemma D_79380 : CTabKB.D W_79380 (Store SZ8 2 19 1992).
Proof. vm_refl. Qed.
Definition W_79384 : bv 32 := 0x7d413023.
Lemma F_79384 : CTabKB.F 0x79384 W_79384.
Proof. vm_refl. Qed.
Lemma D_79384 : CTabKB.D W_79384 (Store SZ8 2 20 1984).
Proof. vm_refl. Qed.
Definition W_79388 : bv 32 := 0x7b513c23.
Lemma F_79388 : CTabKB.F 0x79388 W_79388.
Proof. vm_refl. Qed.
Lemma D_79388 : CTabKB.D W_79388 (Store SZ8 2 21 1976).
Proof. vm_refl. Qed.
Definition W_7938c : bv 32 := 0x7f010413.
Lemma F_7938c : CTabKB.F 0x7938c W_7938c.
Proof. vm_refl. Qed.
Lemma D_7938c : CTabKB.D W_7938c (OpImm ALU_ADD 8 2 2032).
Proof. vm_refl. Qed.
Definition W_79390 : bv 32 := 0xfa010113.
Lemma F_79390 : CTabKB.F 0x79390 W_79390.
Proof. vm_refl. Qed.
Lemma D_79390 : CTabKB.D W_79390 (OpImm ALU_ADD 2 2 4000).
Proof. vm_refl. Qed.
Definition W_79394 : bv 32 := 0x00008913.
Lemma F_79394 : CTabKB.F 0x79394 W_79394.
Proof. vm_refl. Qed.
Lemma D_79394 : CTabKB.D W_79394 (OpImm ALU_ADD 18 1 0).
Proof. vm_refl. Qed.
Definition W_79398 : bv 32 := 0x00050493.
Lemma F_79398 : CTabKB.F 0x79398 W_79398.
Proof. vm_refl. Qed.
Lemma D_79398 : CTabKB.D W_79398 (OpImm ALU_ADD 9 10 0).
Proof. vm_refl. Qed.
Definition W_7939c : bv 32 := 0x6c0070ef.
Lemma F_7939c : CTabKB.F 0x7939c W_7939c.
Proof. vm_refl. Qed.
Lemma D_7939c : CTabKB.D W_7939c (Jal 1 30400).
Proof. vm_refl. Qed.
Definition W_793a0 : bv 32 := 0x06050063.
Lemma F_793a0 : CTabKB.F 0x793a0 W_793a0.
Proof. vm_refl. Qed.
Lemma D_793a0 : CTabKB.D W_793a0 (Branch BC_EQ 10 0 96).
Proof. vm_refl. Qed.
Definition W_793a4 : bv 32 := 0x80040a13.
Lemma F_793a4 : CTabKB.F 0x793a4 W_793a4.
Proof. vm_refl. Qed.
Lemma D_793a4 : CTabKB.D W_793a4 (OpImm ALU_ADD 20 8 2048).
Proof. vm_refl. Qed.
Definition W_793a8 : bv 32 := 0xfb0a0a13.
Lemma F_793a8 : CTabKB.F 0x793a8 W_793a8.
Proof. vm_refl. Qed.
Lemma D_793a8 : CTabKB.D W_793a8 (OpImm ALU_ADD 20 20 4016).
Proof. vm_refl. Qed.
Definition W_793ac : bv 32 := 0x80040513.
Lemma F_793ac : CTabKB.F 0x793ac W_793ac.
Proof. vm_refl. Qed.
Lemma D_793ac : CTabKB.D W_793ac (OpImm ALU_ADD 10 8 2048).
Proof. vm_refl. Qed.
Definition W_793b0 : bv 32 := 0xfc050513.
Lemma F_793b0 : CTabKB.F 0x793b0 W_793b0.
Proof. vm_refl. Qed.
Lemma D_793b0 : CTabKB.D W_793b0 (OpImm ALU_ADD 10 10 4032).
Proof. vm_refl. Qed.
Definition W_793b4 : bv 32 := 0x7ffa0a93.
Lemma F_793b4 : CTabKB.F 0x793b4 W_793b4.
Proof. vm_refl. Qed.
Lemma D_793b4 : CTabKB.D W_793b4 (OpImm ALU_ADD 21 20 2047).
Proof. vm_refl. Qed.
Definition W_793b8 : bv 32 := 0x000ab4a3.
Lemma F_793b8 : CTabKB.F 0x793b8 W_793b8.
Proof. vm_refl. Qed.
Lemma D_793b8 : CTabKB.D W_793b8 (Store SZ8 21 0 9).
Proof. vm_refl. Qed.
Definition W_793bc : bv 32 := 0x00aa3023.
Lemma F_793bc : CTabKB.F 0x793bc W_793bc.
Proof. vm_refl. Qed.
Lemma D_793bc : CTabKB.D W_793bc (Store SZ8 20 10 0).
Proof. vm_refl. Qed.
Definition W_793c0 : bv 32 := 0x000a3423.
Lemma F_793c0 : CTabKB.F 0x793c0 W_793c0.
Proof. vm_refl. Qed.
Lemma D_793c0 : CTabKB.D W_793c0 (Store SZ8 20 0 8).
Proof. vm_refl. Qed.
Definition W_793c4 : bv 32 := 0x420080ef.
Lemma F_793c4 : CTabKB.F 0x793c4 W_793c4.
Proof. vm_refl. Qed.
Lemma D_793c4 : CTabKB.D W_793c4 (Jal 1 33824).
Proof. vm_refl. Qed.
Definition W_793c8 : bv 32 := 0x00200593.
Lemma F_793c8 : CTabKB.F 0x793c8 W_793c8.
Proof. vm_refl. Qed.
Lemma D_793c8 : CTabKB.D W_793c8 (OpImm ALU_ADD 11 0 2).
Proof. vm_refl. Qed.
Definition W_793cc : bv 32 := 0x06a5e263.
Lemma F_793cc : CTabKB.F 0x793cc W_793cc.
Proof. vm_refl. Qed.
Lemma D_793cc : CTabKB.D W_793cc (Branch BC_LTU 11 10 100).
Proof. vm_refl. Qed.
Definition W_79430 : bv 32 := 0x691200ef.
Lemma F_79430 : CTabKB.F 0x79430 W_79430.
Proof. vm_refl. Qed.
Lemma D_79430 : CTabKB.D W_79430 (Jal 1 134800).
Proof. vm_refl. Qed.
Definition W_79434 : bv 32 := 0x000bb597.
Lemma F_79434 : CTabKB.F 0x79434 W_79434.
Proof. vm_refl. Qed.
Lemma D_79434 : CTabKB.D W_79434 (Auipc 11 187).
Proof. vm_refl. Qed.
Definition W_79438 : bv 32 := 0xf5c5b583.
Lemma F_79438 : CTabKB.F 0x79438 W_79438.
Proof. vm_refl. Qed.
Lemma D_79438 : CTabKB.D W_79438 (Load SZ8 true 11 11 3932).
Proof. vm_refl. Qed.
Definition W_7943c : bv 32 := 0x0225c983.
Lemma F_7943c : CTabKB.F 0x7943c W_7943c.
Proof. vm_refl. Qed.
Lemma D_7943c : CTabKB.D W_7943c (Load SZ1 false 19 11 34).
Proof. vm_refl. Qed.
Definition W_79440 : bv 32 := 0x00050913.
Lemma F_79440 : CTabKB.F 0x79440 W_79440.
Proof. vm_refl. Qed.
Lemma D_79440 : CTabKB.D W_79440 (OpImm ALU_ADD 18 10 0).
Proof. vm_refl. Qed.
Definition W_79444 : bv 32 := 0x3a0080ef.
Lemma F_79444 : CTabKB.F 0x79444 W_79444.
Proof. vm_refl. Qed.
Lemma D_79444 : CTabKB.D W_79444 (Jal 1 33696).
Proof. vm_refl. Qed.
Definition W_79448 : bv 32 := 0x00050793.
Lemma F_79448 : CTabKB.F 0x79448 W_79448.
Proof. vm_refl. Qed.
Lemma D_79448 : CTabKB.D W_79448 (OpImm ALU_ADD 15 10 0).
Proof. vm_refl. Qed.
Definition W_7944c : bv 32 := 0x00153513.
Lemma F_7944c : CTabKB.F 0x7944c W_7944c.
Proof. vm_refl. Qed.
Lemma D_7944c : CTabKB.D W_7944c (OpImm ALU_SLTU 10 10 1).
Proof. vm_refl. Qed.
Definition W_79450 : bv 32 := 0xfff50513.
Lemma F_79450 : CTabKB.F 0x79450 W_79450.
Proof. vm_refl. Qed.
Lemma D_79450 : CTabKB.D W_79450 (OpImm ALU_ADD 10 10 4095).
Proof. vm_refl. Qed.
Definition W_79454 : bv 32 := 0x008575b3.
Lemma F_79454 : CTabKB.F 0x79454 W_79454.
Proof. vm_refl. Qed.
Lemma D_79454 : CTabKB.D W_79454 (Op ALU_AND 11 10 8).
Proof. vm_refl. Qed.
Definition W_79458 : bv 32 := 0x00100513.
Lemma F_79458 : CTabKB.F 0x79458 W_79458.
Proof. vm_refl. Qed.
Lemma D_79458 : CTabKB.D W_79458 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_7945c : bv 32 := 0x00bab4a3.
Lemma F_7945c : CTabKB.F 0x7945c W_7945c.
Proof. vm_refl. Qed.
Lemma D_7945c : CTabKB.D W_7945c (Store SZ8 21 11 9).
Proof. vm_refl. Qed.
Definition W_79460 : bv 32 := 0x00f56a63.
Lemma F_79460 : CTabKB.F 0x79460 W_79460.
Proof. vm_refl. Qed.
Lemma D_79460 : CTabKB.D W_79460 (Branch BC_LTU 10 15 20).
Proof. vm_refl. Qed.
Definition W_79474 : bv 32 := 0x80040513.
Lemma F_79474 : CTabKB.F 0x79474 W_79474.
Proof. vm_refl. Qed.
Lemma D_79474 : CTabKB.D W_79474 (OpImm ALU_ADD 10 8 2048).
Proof. vm_refl. Qed.
Definition W_79478 : bv 32 := 0xfb050513.
Lemma F_79478 : CTabKB.F 0x79478 W_79478.
Proof. vm_refl. Qed.
Lemma D_79478 : CTabKB.D W_79478 (OpImm ALU_ADD 10 10 4016).
Proof. vm_refl. Qed.
Definition W_7947c : bv 32 := 0x00090593.
Lemma F_7947c : CTabKB.F 0x7947c W_7947c.
Proof. vm_refl. Qed.
Lemma D_7947c : CTabKB.D W_7947c (OpImm ALU_ADD 11 18 0).
Proof. vm_refl. Qed.
Definition W_79480 : bv 32 := 0x00040613.
Lemma F_79480 : CTabKB.F 0x79480 W_79480.
Proof. vm_refl. Qed.
Lemma D_79480 : CTabKB.D W_79480 (OpImm ALU_ADD 12 8 0).
Proof. vm_refl. Qed.
Definition W_79484 : bv 32 := 0x00000693.
Lemma F_79484 : CTabKB.F 0x79484 W_79484.
Proof. vm_refl. Qed.
Lemma D_79484 : CTabKB.D W_79484 (OpImm ALU_ADD 13 0 0).
Proof. vm_refl. Qed.
Definition W_79488 : bv 32 := 0x00098713.
Lemma F_79488 : CTabKB.F 0x79488 W_79488.
Proof. vm_refl. Qed.
Lemma D_79488 : CTabKB.D W_79488 (OpImm ALU_ADD 14 19 0).
Proof. vm_refl. Qed.
Definition W_7948c : bv 32 := 0x368080ef.
Lemma F_7948c : CTabKB.F 0x7948c W_7948c.
Proof. vm_refl. Qed.
Lemma D_7948c : CTabKB.D W_7948c (Jal 1 33640).
Proof. vm_refl. Qed.
Definition W_79490 : bv 32 := 0x80040593.
Lemma F_79490 : CTabKB.F 0x79490 W_79490.
Proof. vm_refl. Qed.
Lemma D_79490 : CTabKB.D W_79490 (OpImm ALU_ADD 11 8 2048).
Proof. vm_refl. Qed.
Definition W_79494 : bv 32 := 0xfb058593.
Lemma F_79494 : CTabKB.F 0x79494 W_79494.
Proof. vm_refl. Qed.
Lemma D_79494 : CTabKB.D W_79494 (OpImm ALU_ADD 11 11 4016).
Proof. vm_refl. Qed.
Definition W_79498 : bv 32 := 0x00048513.
Lemma F_79498 : CTabKB.F 0x79498 W_79498.
Proof. vm_refl. Qed.
Lemma D_79498 : CTabKB.D W_79498 (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_7949c : bv 32 := 0x9bdd80ef.
Lemma F_7949c : CTabKB.F 0x7949c W_7949c.
Proof. vm_refl. Qed.
Lemma D_7949c : CTabKB.D W_7949c (Jal 1 1935804).
Proof. vm_refl. Qed.
Definition W_794a0 : bv 32 := 0x06010113.
Lemma F_794a0 : CTabKB.F 0x794a0 W_794a0.
Proof. vm_refl. Qed.
Lemma D_794a0 : CTabKB.D W_794a0 (OpImm ALU_ADD 2 2 96).
Proof. vm_refl. Qed.
Definition W_794a4 : bv 32 := 0x7e813083.
Lemma F_794a4 : CTabKB.F 0x794a4 W_794a4.
Proof. vm_refl. Qed.
Lemma D_794a4 : CTabKB.D W_794a4 (Load SZ8 true 1 2 2024).
Proof. vm_refl. Qed.
Definition W_794a8 : bv 32 := 0x7e013403.
Lemma F_794a8 : CTabKB.F 0x794a8 W_794a8.
Proof. vm_refl. Qed.
Lemma D_794a8 : CTabKB.D W_794a8 (Load SZ8 true 8 2 2016).
Proof. vm_refl. Qed.
Definition W_794ac : bv 32 := 0x7d813483.
Lemma F_794ac : CTabKB.F 0x794ac W_794ac.
Proof. vm_refl. Qed.
Lemma D_794ac : CTabKB.D W_794ac (Load SZ8 true 9 2 2008).
Proof. vm_refl. Qed.
Definition W_794b0 : bv 32 := 0x7d013903.
Lemma F_794b0 : CTabKB.F 0x794b0 W_794b0.
Proof. vm_refl. Qed.
Lemma D_794b0 : CTabKB.D W_794b0 (Load SZ8 true 18 2 2000).
Proof. vm_refl. Qed.
Definition W_794b4 : bv 32 := 0x7c813983.
Lemma F_794b4 : CTabKB.F 0x794b4 W_794b4.
Proof. vm_refl. Qed.
Lemma D_794b4 : CTabKB.D W_794b4 (Load SZ8 true 19 2 1992).
Proof. vm_refl. Qed.
Definition W_794b8 : bv 32 := 0x7c013a03.
Lemma F_794b8 : CTabKB.F 0x794b8 W_794b8.
Proof. vm_refl. Qed.
Lemma D_794b8 : CTabKB.D W_794b8 (Load SZ8 true 20 2 1984).
Proof. vm_refl. Qed.
Definition W_794bc : bv 32 := 0x7b813a83.
Lemma F_794bc : CTabKB.F 0x794bc W_794bc.
Proof. vm_refl. Qed.
Lemma D_794bc : CTabKB.D W_794bc (Load SZ8 true 21 2 1976).
Proof. vm_refl. Qed.
Definition W_794c0 : bv 32 := 0x7f010113.
Lemma F_794c0 : CTabKB.F 0x794c0 W_794c0.
Proof. vm_refl. Qed.
Lemma D_794c0 : CTabKB.D W_794c0 (OpImm ALU_ADD 2 2 2032).
Proof. vm_refl. Qed.
Definition W_794c4 : bv 32 := 0x00008067.
Lemma F_794c4 : CTabKB.F 0x794c4 W_794c4.
Proof. vm_refl. Qed.
Lemma D_794c4 : CTabKB.D W_794c4 (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_798d8 : bv 32 := 0x81010113.
Lemma F_798d8 : CTabKB.F 0x798d8 W_798d8.
Proof. vm_refl. Qed.
Lemma D_798d8 : CTabKB.D W_798d8 (OpImm ALU_ADD 2 2 2064).
Proof. vm_refl. Qed.
Definition W_798dc : bv 32 := 0x7e113423.
Lemma F_798dc : CTabKB.F 0x798dc W_798dc.
Proof. vm_refl. Qed.
Lemma D_798dc : CTabKB.D W_798dc (Store SZ8 2 1 2024).
Proof. vm_refl. Qed.
Definition W_798e0 : bv 32 := 0x7e813023.
Lemma F_798e0 : CTabKB.F 0x798e0 W_798e0.
Proof. vm_refl. Qed.
Lemma D_798e0 : CTabKB.D W_798e0 (Store SZ8 2 8 2016).
Proof. vm_refl. Qed.
Definition W_798e4 : bv 32 := 0x7c913c23.
Lemma F_798e4 : CTabKB.F 0x798e4 W_798e4.
Proof. vm_refl. Qed.
Lemma D_798e4 : CTabKB.D W_798e4 (Store SZ8 2 9 2008).
Proof. vm_refl. Qed.
Definition W_798e8 : bv 32 := 0x7d213823.
Lemma F_798e8 : CTabKB.F 0x798e8 W_798e8.
Proof. vm_refl. Qed.
Lemma D_798e8 : CTabKB.D W_798e8 (Store SZ8 2 18 2000).
Proof. vm_refl. Qed.
Definition W_798ec : bv 32 := 0x7d313423.
Lemma F_798ec : CTabKB.F 0x798ec W_798ec.
Proof. vm_refl. Qed.
Lemma D_798ec : CTabKB.D W_798ec (Store SZ8 2 19 1992).
Proof. vm_refl. Qed.
Definition W_798f0 : bv 32 := 0x7d413023.
Lemma F_798f0 : CTabKB.F 0x798f0 W_798f0.
Proof. vm_refl. Qed.
Lemma D_798f0 : CTabKB.D W_798f0 (Store SZ8 2 20 1984).
Proof. vm_refl. Qed.
Definition W_798f4 : bv 32 := 0x7b513c23.
Lemma F_798f4 : CTabKB.F 0x798f4 W_798f4.
Proof. vm_refl. Qed.
Lemma D_798f4 : CTabKB.D W_798f4 (Store SZ8 2 21 1976).
Proof. vm_refl. Qed.
Definition W_798f8 : bv 32 := 0x7b613823.
Lemma F_798f8 : CTabKB.F 0x798f8 W_798f8.
Proof. vm_refl. Qed.
Lemma D_798f8 : CTabKB.D W_798f8 (Store SZ8 2 22 1968).
Proof. vm_refl. Qed.
Definition W_798fc : bv 32 := 0x7f010413.
Lemma F_798fc : CTabKB.F 0x798fc W_798fc.
Proof. vm_refl. Qed.
Lemma D_798fc : CTabKB.D W_798fc (OpImm ALU_ADD 8 2 2032).
Proof. vm_refl. Qed.
Definition W_79900 : bv 32 := 0xf9010113.
Lemma F_79900 : CTabKB.F 0x79900 W_79900.
Proof. vm_refl. Qed.
Lemma D_79900 : CTabKB.D W_79900 (OpImm ALU_ADD 2 2 3984).
Proof. vm_refl. Qed.
Definition W_79904 : bv 32 := 0x00008993.
Lemma F_79904 : CTabKB.F 0x79904 W_79904.
Proof. vm_refl. Qed.
Lemma D_79904 : CTabKB.D W_79904 (OpImm ALU_ADD 19 1 0).
Proof. vm_refl. Qed.
Definition W_79908 : bv 32 := 0x00058493.
Lemma F_79908 : CTabKB.F 0x79908 W_79908.
Proof. vm_refl. Qed.
Lemma D_79908 : CTabKB.D W_79908 (OpImm ALU_ADD 9 11 0).
Proof. vm_refl. Qed.
Definition W_7990c : bv 32 := 0x00050913.
Lemma F_7990c : CTabKB.F 0x7990c W_7990c.
Proof. vm_refl. Qed.
Lemma D_7990c : CTabKB.D W_7990c (OpImm ALU_ADD 18 10 0).
Proof. vm_refl. Qed.
Definition W_79910 : bv 32 := 0x80040a93.
Lemma F_79910 : CTabKB.F 0x79910 W_79910.
Proof. vm_refl. Qed.
Lemma D_79910 : CTabKB.D W_79910 (OpImm ALU_ADD 21 8 2048).
Proof. vm_refl. Qed.
Definition W_79914 : bv 32 := 0xfa8a8a93.
Lemma F_79914 : CTabKB.F 0x79914 W_79914.
Proof. vm_refl. Qed.
Lemma D_79914 : CTabKB.D W_79914 (OpImm ALU_ADD 21 21 4008).
Proof. vm_refl. Qed.
Definition W_79918 : bv 32 := 0x80040513.
Lemma F_79918 : CTabKB.F 0x79918 W_79918.
Proof. vm_refl. Qed.
Lemma D_79918 : CTabKB.D W_79918 (OpImm ALU_ADD 10 8 2048).
Proof. vm_refl. Qed.
Definition W_7991c : bv 32 := 0xfb850513.
Lemma F_7991c : CTabKB.F 0x7991c W_7991c.
Proof. vm_refl. Qed.
Lemma D_7991c : CTabKB.D W_7991c (OpImm ALU_ADD 10 10 4024).
Proof. vm_refl. Qed.
Definition W_79920 : bv 32 := 0x7ffa8b13.
Lemma F_79920 : CTabKB.F 0x79920 W_79920.
Proof. vm_refl. Qed.
Lemma D_79920 : CTabKB.D W_79920 (OpImm ALU_ADD 22 21 2047).
Proof. vm_refl. Qed.
Definition W_79924 : bv 32 := 0x000b34a3.
Lemma F_79924 : CTabKB.F 0x79924 W_79924.
Proof. vm_refl. Qed.
Lemma D_79924 : CTabKB.D W_79924 (Store SZ8 22 0 9).
Proof. vm_refl. Qed.
Definition W_79928 : bv 32 := 0x00aab023.
Lemma F_79928 : CTabKB.F 0x79928 W_79928.
Proof. vm_refl. Qed.
Lemma D_79928 : CTabKB.D W_79928 (Store SZ8 21 10 0).
Proof. vm_refl. Qed.
Definition W_7992c : bv 32 := 0x000ab423.
Lemma F_7992c : CTabKB.F 0x7992c W_7992c.
Proof. vm_refl. Qed.
Lemma D_7992c : CTabKB.D W_7992c (Store SZ8 21 0 8).
Proof. vm_refl. Qed.
Definition W_79930 : bv 32 := 0x6b5070ef.
Lemma F_79930 : CTabKB.F 0x79930 W_79930.
Proof. vm_refl. Qed.
Lemma D_79930 : CTabKB.D W_79930 (Jal 1 32436).
Proof. vm_refl. Qed.
Definition W_79934 : bv 32 := 0x00200593.
Lemma F_79934 : CTabKB.F 0x79934 W_79934.
Proof. vm_refl. Qed.
Lemma D_79934 : CTabKB.D W_79934 (OpImm ALU_ADD 11 0 2).
Proof. vm_refl. Qed.
Definition W_79938 : bv 32 := 0x02a5ea63.
Lemma F_79938 : CTabKB.F 0x79938 W_79938.
Proof. vm_refl. Qed.
Lemma D_79938 : CTabKB.D W_79938 (Branch BC_LTU 11 10 52).
Proof. vm_refl. Qed.
Definition W_7996c : bv 32 := 0x155200ef.
Lemma F_7996c : CTabKB.F 0x7996c W_7996c.
Proof. vm_refl. Qed.
Lemma D_7996c : CTabKB.D W_7996c (Jal 1 133460).
Proof. vm_refl. Qed.
Definition W_79970 : bv 32 := 0x000bb597.
Lemma F_79970 : CTabKB.F 0x79970 W_79970.
Proof. vm_refl. Qed.
Lemma D_79970 : CTabKB.D W_79970 (Auipc 11 187).
Proof. vm_refl. Qed.
Definition W_79974 : bv 32 := 0xa205b583.
Lemma F_79974 : CTabKB.F 0x79974 W_79974.
Proof. vm_refl. Qed.
Lemma D_79974 : CTabKB.D W_79974 (Load SZ8 true 11 11 2592).
Proof. vm_refl. Qed.
Definition W_79978 : bv 32 := 0x0225ca03.
Lemma F_79978 : CTabKB.F 0x79978 W_79978.
Proof. vm_refl. Qed.
Lemma D_79978 : CTabKB.D W_79978 (Load SZ1 false 20 11 34).
Proof. vm_refl. Qed.
Definition W_7997c : bv 32 := 0x00050993.
Lemma F_7997c : CTabKB.F 0x7997c W_7997c.
Proof. vm_refl. Qed.
Lemma D_7997c : CTabKB.D W_7997c (OpImm ALU_ADD 19 10 0).
Proof. vm_refl. Qed.
Definition W_79980 : bv 32 := 0x665070ef.
Lemma F_79980 : CTabKB.F 0x79980 W_79980.
Proof. vm_refl. Qed.
Lemma D_79980 : CTabKB.D W_79980 (Jal 1 32356).
Proof. vm_refl. Qed.
Definition W_79984 : bv 32 := 0x00050793.
Lemma F_79984 : CTabKB.F 0x79984 W_79984.
Proof. vm_refl. Qed.
Lemma D_79984 : CTabKB.D W_79984 (OpImm ALU_ADD 15 10 0).
Proof. vm_refl. Qed.
Definition W_79988 : bv 32 := 0x00153513.
Lemma F_79988 : CTabKB.F 0x79988 W_79988.
Proof. vm_refl. Qed.
Lemma D_79988 : CTabKB.D W_79988 (OpImm ALU_SLTU 10 10 1).
Proof. vm_refl. Qed.
Definition W_7998c : bv 32 := 0xfff50513.
Lemma F_7998c : CTabKB.F 0x7998c W_7998c.
Proof. vm_refl. Qed.
Lemma D_7998c : CTabKB.D W_7998c (OpImm ALU_ADD 10 10 4095).
Proof. vm_refl. Qed.
Definition W_79990 : bv 32 := 0x008575b3.
Lemma F_79990 : CTabKB.F 0x79990 W_79990.
Proof. vm_refl. Qed.
Lemma D_79990 : CTabKB.D W_79990 (Op ALU_AND 11 10 8).
Proof. vm_refl. Qed.
Definition W_79994 : bv 32 := 0x00100513.
Lemma F_79994 : CTabKB.F 0x79994 W_79994.
Proof. vm_refl. Qed.
Lemma D_79994 : CTabKB.D W_79994 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_79998 : bv 32 := 0x00bb34a3.
Lemma F_79998 : CTabKB.F 0x79998 W_79998.
Proof. vm_refl. Qed.
Lemma D_79998 : CTabKB.D W_79998 (Store SZ8 22 11 9).
Proof. vm_refl. Qed.
Definition W_7999c : bv 32 := 0x00f56a63.
Lemma F_7999c : CTabKB.F 0x7999c W_7999c.
Proof. vm_refl. Qed.
Lemma D_7999c : CTabKB.D W_7999c (Branch BC_LTU 10 15 20).
Proof. vm_refl. Qed.
Definition W_799b0 : bv 32 := 0x80040513.
Lemma F_799b0 : CTabKB.F 0x799b0 W_799b0.
Proof. vm_refl. Qed.
Lemma D_799b0 : CTabKB.D W_799b0 (OpImm ALU_ADD 10 8 2048).
Proof. vm_refl. Qed.
Definition W_799b4 : bv 32 := 0xfa850513.
Lemma F_799b4 : CTabKB.F 0x799b4 W_799b4.
Proof. vm_refl. Qed.
Lemma D_799b4 : CTabKB.D W_799b4 (OpImm ALU_ADD 10 10 4008).
Proof. vm_refl. Qed.
Definition W_799b8 : bv 32 := 0x00098593.
Lemma F_799b8 : CTabKB.F 0x799b8 W_799b8.
Proof. vm_refl. Qed.
Lemma D_799b8 : CTabKB.D W_799b8 (OpImm ALU_ADD 11 19 0).
Proof. vm_refl. Qed.
Definition W_799bc : bv 32 := 0x00040613.
Lemma F_799bc : CTabKB.F 0x799bc W_799bc.
Proof. vm_refl. Qed.
Lemma D_799bc : CTabKB.D W_799bc (OpImm ALU_ADD 12 8 0).
Proof. vm_refl. Qed.
Definition W_799c0 : bv 32 := 0x00000693.
Lemma F_799c0 : CTabKB.F 0x799c0 W_799c0.
Proof. vm_refl. Qed.
Lemma D_799c0 : CTabKB.D W_799c0 (OpImm ALU_ADD 13 0 0).
Proof. vm_refl. Qed.
Definition W_799c4 : bv 32 := 0x000a0713.
Lemma F_799c4 : CTabKB.F 0x799c4 W_799c4.
Proof. vm_refl. Qed.
Lemma D_799c4 : CTabKB.D W_799c4 (OpImm ALU_ADD 14 20 0).
Proof. vm_refl. Qed.
Definition W_799c8 : bv 32 := 0x62d070ef.
Lemma F_799c8 : CTabKB.F 0x799c8 W_799c8.
Proof. vm_refl. Qed.
Lemma D_799c8 : CTabKB.D W_799c8 (Jal 1 32300).
Proof. vm_refl. Qed.
Definition W_799cc : bv 32 := 0x80040613.
Lemma F_799cc : CTabKB.F 0x799cc W_799cc.
Proof. vm_refl. Qed.
Lemma D_799cc : CTabKB.D W_799cc (OpImm ALU_ADD 12 8 2048).
Proof. vm_refl. Qed.
Definition W_799d0 : bv 32 := 0xfa860613.
Lemma F_799d0 : CTabKB.F 0x799d0 W_799d0.
Proof. vm_refl. Qed.
Lemma D_799d0 : CTabKB.D W_799d0 (OpImm ALU_ADD 12 12 4008).
Proof. vm_refl. Qed.
Definition W_799d4 : bv 32 := 0x00090513.
Lemma F_799d4 : CTabKB.F 0x799d4 W_799d4.
Proof. vm_refl. Qed.
Lemma D_799d4 : CTabKB.D W_799d4 (OpImm ALU_ADD 10 18 0).
Proof. vm_refl. Qed.
Definition W_799d8 : bv 32 := 0x00048593.
Lemma F_799d8 : CTabKB.F 0x799d8 W_799d8.
Proof. vm_refl. Qed.
Lemma D_799d8 : CTabKB.D W_799d8 (OpImm ALU_ADD 11 9 0).
Proof. vm_refl. Qed.
Definition W_799dc : bv 32 := 0x86cd90ef.
Lemma F_799dc : CTabKB.F 0x799dc W_799dc.
Proof. vm_refl. Qed.
Lemma D_799dc : CTabKB.D W_799dc (Jal 1 1937516).
Proof. vm_refl. Qed.
Definition W_799e0 : bv 32 := 0x07010113.
Lemma F_799e0 : CTabKB.F 0x799e0 W_799e0.
Proof. vm_refl. Qed.
Lemma D_799e0 : CTabKB.D W_799e0 (OpImm ALU_ADD 2 2 112).
Proof. vm_refl. Qed.
Definition W_799e4 : bv 32 := 0x7e813083.
Lemma F_799e4 : CTabKB.F 0x799e4 W_799e4.
Proof. vm_refl. Qed.
Lemma D_799e4 : CTabKB.D W_799e4 (Load SZ8 true 1 2 2024).
Proof. vm_refl. Qed.
Definition W_799e8 : bv 32 := 0x7e013403.
Lemma F_799e8 : CTabKB.F 0x799e8 W_799e8.
Proof. vm_refl. Qed.
Lemma D_799e8 : CTabKB.D W_799e8 (Load SZ8 true 8 2 2016).
Proof. vm_refl. Qed.
Definition W_799ec : bv 32 := 0x7d813483.
Lemma F_799ec : CTabKB.F 0x799ec W_799ec.
Proof. vm_refl. Qed.
Lemma D_799ec : CTabKB.D W_799ec (Load SZ8 true 9 2 2008).
Proof. vm_refl. Qed.
Definition W_799f0 : bv 32 := 0x7d013903.
Lemma F_799f0 : CTabKB.F 0x799f0 W_799f0.
Proof. vm_refl. Qed.
Lemma D_799f0 : CTabKB.D W_799f0 (Load SZ8 true 18 2 2000).
Proof. vm_refl. Qed.
Definition W_799f4 : bv 32 := 0x7c813983.
Lemma F_799f4 : CTabKB.F 0x799f4 W_799f4.
Proof. vm_refl. Qed.
Lemma D_799f4 : CTabKB.D W_799f4 (Load SZ8 true 19 2 1992).
Proof. vm_refl. Qed.
Definition W_799f8 : bv 32 := 0x7c013a03.
Lemma F_799f8 : CTabKB.F 0x799f8 W_799f8.
Proof. vm_refl. Qed.
Lemma D_799f8 : CTabKB.D W_799f8 (Load SZ8 true 20 2 1984).
Proof. vm_refl. Qed.
Definition W_799fc : bv 32 := 0x7b813a83.
Lemma F_799fc : CTabKB.F 0x799fc W_799fc.
Proof. vm_refl. Qed.
Lemma D_799fc : CTabKB.D W_799fc (Load SZ8 true 21 2 1976).
Proof. vm_refl. Qed.
Definition W_79a00 : bv 32 := 0x7b013b03.
Lemma F_79a00 : CTabKB.F 0x79a00 W_79a00.
Proof. vm_refl. Qed.
Lemma D_79a00 : CTabKB.D W_79a00 (Load SZ8 true 22 2 1968).
Proof. vm_refl. Qed.
Definition W_79a04 : bv 32 := 0x7f010113.
Lemma F_79a04 : CTabKB.F 0x79a04 W_79a04.
Proof. vm_refl. Qed.
Lemma D_79a04 : CTabKB.D W_79a04 (OpImm ALU_ADD 2 2 2032).
Proof. vm_refl. Qed.
Definition W_79a08 : bv 32 := 0x00008067.
Lemma F_79a08 : CTabKB.F 0x79a08 W_79a08.
Proof. vm_refl. Qed.
Lemma D_79a08 : CTabKB.D W_79a08 (Jalr 0 1 0).
Proof. vm_refl. Qed.

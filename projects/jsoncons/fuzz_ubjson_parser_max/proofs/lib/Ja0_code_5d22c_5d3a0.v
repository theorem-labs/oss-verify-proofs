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
Definition W_5d22c : bv 32 := 0xfe010113.
Lemma F_5d22c : CTabKA.F 0x5d22c W_5d22c.
Proof. vm_refl. Qed.
Lemma D_5d22c : CTabKA.D W_5d22c (OpImm ALU_ADD 2 2 4064).
Proof. vm_refl. Qed.
Definition W_5d230 : bv 32 := 0x00113c23.
Lemma F_5d230 : CTabKA.F 0x5d230 W_5d230.
Proof. vm_refl. Qed.
Lemma D_5d230 : CTabKA.D W_5d230 (Store SZ8 2 1 24).
Proof. vm_refl. Qed.
Definition W_5d234 : bv 32 := 0x00813823.
Lemma F_5d234 : CTabKA.F 0x5d234 W_5d234.
Proof. vm_refl. Qed.
Lemma D_5d234 : CTabKA.D W_5d234 (Store SZ8 2 8 16).
Proof. vm_refl. Qed.
Definition W_5d238 : bv 32 := 0x00913423.
Lemma F_5d238 : CTabKA.F 0x5d238 W_5d238.
Proof. vm_refl. Qed.
Lemma D_5d238 : CTabKA.D W_5d238 (Store SZ8 2 9 8).
Proof. vm_refl. Qed.
Definition W_5d23c : bv 32 := 0x01213023.
Lemma F_5d23c : CTabKA.F 0x5d23c W_5d23c.
Proof. vm_refl. Qed.
Lemma D_5d23c : CTabKA.D W_5d23c (Store SZ8 2 18 0).
Proof. vm_refl. Qed.
Definition W_5d240 : bv 32 := 0x02010413.
Lemma F_5d240 : CTabKA.F 0x5d240 W_5d240.
Proof. vm_refl. Qed.
Lemma D_5d240 : CTabKA.D W_5d240 (OpImm ALU_ADD 8 2 32).
Proof. vm_refl. Qed.
Definition W_5d244 : bv 32 := 0x000d6517.
Lemma F_5d244 : CTabKA.F 0x5d244 W_5d244.
Proof. vm_refl. Qed.
Lemma D_5d244 : CTabKA.D W_5d244 (Auipc 10 214).
Proof. vm_refl. Qed.
Definition W_5d248 : bv 32 := 0x1ec50513.
Lemma F_5d248 : CTabKA.F 0x5d248 W_5d248.
Proof. vm_refl. Qed.
Lemma D_5d248 : CTabKA.D W_5d248 (OpImm ALU_ADD 10 10 492).
Proof. vm_refl. Qed.
Definition W_5d24c : bv 32 := 0x04d050ef.
Lemma F_5d24c : CTabKA.F 0x5d24c W_5d24c.
Proof. vm_refl. Qed.
Lemma D_5d24c : CTabKA.D W_5d24c (Jal 1 22604).
Proof. vm_refl. Qed.
Definition W_5d250 : bv 32 := 0x00053483.
Lemma F_5d250 : CTabKA.F 0x5d250 W_5d250.
Proof. vm_refl. Qed.
Lemma D_5d250 : CTabKA.D W_5d250 (Load SZ8 true 9 10 0).
Proof. vm_refl. Qed.
Definition W_5d254 : bv 32 := 0x08048063.
Lemma F_5d254 : CTabKA.F 0x5d254 W_5d254.
Proof. vm_refl. Qed.
Lemma D_5d254 : CTabKA.D W_5d254 (Branch BC_EQ 9 0 128).
Proof. vm_refl. Qed.
Definition W_5d258 : bv 32 := 0x0604c503.
Lemma F_5d258 : CTabKA.F 0x5d258 W_5d258.
Proof. vm_refl. Qed.
Lemma D_5d258 : CTabKA.D W_5d258 (Load SZ1 false 10 9 96).
Proof. vm_refl. Qed.
Definition W_5d25c : bv 32 := 0x0584b903.
Lemma F_5d25c : CTabKA.F 0x5d25c W_5d25c.
Proof. vm_refl. Qed.
Lemma D_5d25c : CTabKA.D W_5d25c (Load SZ8 true 18 9 88).
Proof. vm_refl. Qed.
Definition W_5d260 : bv 32 := 0x00050863.
Lemma F_5d260 : CTabKA.F 0x5d260 W_5d260.
Proof. vm_refl. Qed.
Lemma D_5d260 : CTabKA.D W_5d260 (Branch BC_EQ 10 0 16).
Proof. vm_refl. Qed.
Definition W_5d264 : bv 32 := 0x00048513.
Lemma F_5d264 : CTabKA.F 0x5d264 W_5d264.
Proof. vm_refl. Qed.
Lemma D_5d264 : CTabKA.D W_5d264 (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_5d268 : bv 32 := 0x00040593.
Lemma F_5d268 : CTabKA.F 0x5d268 W_5d268.
Proof. vm_refl. Qed.
Lemma D_5d268 : CTabKA.D W_5d268 (OpImm ALU_ADD 11 8 0).
Proof. vm_refl. Qed.
Definition W_5d26c : bv 32 := 0xb75ff0ef.
Lemma F_5d26c : CTabKA.F 0x5d26c W_5d26c.
Proof. vm_refl. Qed.
Lemma D_5d26c : CTabKA.D W_5d26c (Jal 1 2095988).
Proof. vm_refl. Qed.
Definition W_5d270 : bv 32 := 0xffa90593.
Lemma F_5d270 : CTabKA.F 0x5d270 W_5d270.
Proof. vm_refl. Qed.
Lemma D_5d270 : CTabKA.D W_5d270 (OpImm ALU_ADD 11 18 4090).
Proof. vm_refl. Qed.
Definition W_5d274 : bv 32 := 0x00100513.
Lemma F_5d274 : CTabKA.F 0x5d274 W_5d274.
Proof. vm_refl. Qed.
Lemma D_5d274 : CTabKA.D W_5d274 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_5d278 : bv 32 := 0x00b51533.
Lemma F_5d278 : CTabKA.F 0x5d278 W_5d278.
Proof. vm_refl. Qed.
Lemma D_5d278 : CTabKA.D W_5d278 (Op ALU_SLL 10 10 11).
Proof. vm_refl. Qed.
Definition W_5d27c : bv 32 := 0x0005061b.
Lemma F_5d27c : CTabKA.F 0x5d27c W_5d27c.
Proof. vm_refl. Qed.
Lemma D_5d27c : CTabKA.D W_5d27c (OpImm32 12 10 0).
Proof. vm_refl. Qed.
Definition W_5d280 : bv 32 := 0x06c05a63.
Lemma F_5d280 : CTabKA.F 0x5d280 W_5d280.
Proof. vm_refl. Qed.
Lemma D_5d280 : CTabKA.D W_5d280 (Branch BC_GE 0 12 116).
Proof. vm_refl. Qed.
Definition W_5d284 : bv 32 := 0x000016b7.
Lemma F_5d284 : CTabKA.F 0x5d284 W_5d284.
Proof. vm_refl. Qed.
Lemma D_5d284 : CTabKA.D W_5d284 (Lui 13 1).
Proof. vm_refl. Qed.
Definition W_5d288 : bv 32 := 0xfff00713.
Lemma F_5d288 : CTabKA.F 0x5d288 W_5d288.
Proof. vm_refl. Qed.
Lemma D_5d288 : CTabKA.D W_5d288 (OpImm ALU_ADD 14 0 4095).
Proof. vm_refl. Qed.
Definition W_5d28c : bv 32 := 0x0004b603.
Lemma F_5d28c : CTabKA.F 0x5d28c W_5d28c.
Proof. vm_refl. Qed.
Lemma D_5d28c : CTabKA.D W_5d28c (Load SZ8 true 12 9 0).
Proof. vm_refl. Qed.
Definition W_5d290 : bv 32 := 0x00b71733.
Lemma F_5d290 : CTabKA.F 0x5d290 W_5d290.
Proof. vm_refl. Qed.
Lemma D_5d290 : CTabKA.D W_5d290 (Op ALU_SLL 14 14 11).
Proof. vm_refl. Qed.
Definition W_5d294 : bv 32 := 0xfff50793.
Lemma F_5d294 : CTabKA.F 0x5d294 W_5d294.
Proof. vm_refl. Qed.
Lemma D_5d294 : CTabKA.D W_5d294 (OpImm ALU_ADD 15 10 4095).
Proof. vm_refl. Qed.
Definition W_5d298 : bv 32 := 0x00d485b3.
Lemma F_5d298 : CTabKA.F 0x5d298 W_5d298.
Proof. vm_refl. Qed.
Lemma D_5d298 : CTabKA.D W_5d298 (Op ALU_ADD 11 9 13).
Proof. vm_refl. Qed.
Definition W_5d29c : bv 32 := 0xfff74693.
Lemma F_5d29c : CTabKA.F 0x5d29c W_5d29c.
Proof. vm_refl. Qed.
Lemma D_5d29c : CTabKA.D W_5d29c (OpImm ALU_XOR 13 14 4095).
Proof. vm_refl. Qed.
Definition W_5d2a0 : bv 32 := 0x02079793.
Lemma F_5d2a0 : CTabKA.F 0x5d2a0 W_5d2a0.
Proof. vm_refl. Qed.
Lemma D_5d2a0 : CTabKA.D W_5d2a0 (ShiftImm ALU_SLL 15 15 32).
Proof. vm_refl. Qed.
Definition W_5d2a4 : bv 32 := 0x0207d793.
Lemma F_5d2a4 : CTabKA.F 0x5d2a4 W_5d2a4.
Proof. vm_refl. Qed.
Lemma D_5d2a4 : CTabKA.D W_5d2a4 (ShiftImm ALU_SRL 15 15 32).
Proof. vm_refl. Qed.
Definition W_5d2a8 : bv 32 := 0x00f60733.
Lemma F_5d2a8 : CTabKA.F 0x5d2a8 W_5d2a8.
Proof. vm_refl. Qed.
Lemma D_5d2a8 : CTabKA.D W_5d2a8 (Op ALU_ADD 14 12 15).
Proof. vm_refl. Qed.
Definition W_5d2ac : bv 32 := 0x00170713.
Lemma F_5d2ac : CTabKA.F 0x5d2ac W_5d2ac.
Proof. vm_refl. Qed.
Lemma D_5d2ac : CTabKA.D W_5d2ac (OpImm ALU_ADD 14 14 1).
Proof. vm_refl. Qed.
Definition W_5d2b0 : bv 32 := 0x00d67833.
Lemma F_5d2b0 : CTabKA.F 0x5d2b0 W_5d2b0.
Proof. vm_refl. Qed.
Lemma D_5d2b0 : CTabKA.D W_5d2b0 (Op ALU_AND 16 12 13).
Proof. vm_refl. Qed.
Definition W_5d2b4 : bv 32 := 0x010587b3.
Lemma F_5d2b4 : CTabKA.F 0x5d2b4 W_5d2b4.
Proof. vm_refl. Qed.
Lemma D_5d2b4 : CTabKA.D W_5d2b4 (Op ALU_ADD 15 11 16).
Proof. vm_refl. Qed.
Definition W_5d2b8 : bv 32 := 0x0007c883.
Lemma F_5d2b8 : CTabKA.F 0x5d2b8 W_5d2b8.
Proof. vm_refl. Qed.
Lemma D_5d2b8 : CTabKA.D W_5d2b8 (Load SZ1 false 17 15 0).
Proof. vm_refl. Qed.
Definition W_5d2bc : bv 32 := 0x06088663.
Lemma F_5d2bc : CTabKA.F 0x5d2bc W_5d2bc.
Proof. vm_refl. Qed.
Lemma D_5d2bc : CTabKA.D W_5d2bc (Branch BC_EQ 17 0 108).
Proof. vm_refl. Qed.
Definition W_5d2c0 : bv 32 := 0xfff5051b.
Lemma F_5d2c0 : CTabKA.F 0x5d2c0 W_5d2c0.
Proof. vm_refl. Qed.
Lemma D_5d2c0 : CTabKA.D W_5d2c0 (OpImm32 10 10 4095).
Proof. vm_refl. Qed.
Definition W_5d2c4 : bv 32 := 0x00160613.
Lemma F_5d2c4 : CTabKA.F 0x5d2c4 W_5d2c4.
Proof. vm_refl. Qed.
Lemma D_5d2c4 : CTabKA.D W_5d2c4 (OpImm ALU_ADD 12 12 1).
Proof. vm_refl. Qed.
Definition W_5d2c8 : bv 32 := 0xfe0514e3.
Lemma F_5d2c8 : CTabKA.F 0x5d2c8 W_5d2c8.
Proof. vm_refl. Qed.
Lemma D_5d2c8 : CTabKA.D W_5d2c8 (Branch BC_NE 10 0 8168).
Proof. vm_refl. Qed.
Definition W_5d2cc : bv 32 := 0x00e4b023.
Lemma F_5d2cc : CTabKA.F 0x5d2cc W_5d2cc.
Proof. vm_refl. Qed.
Lemma D_5d2cc : CTabKA.D W_5d2cc (Store SZ8 9 14 0).
Proof. vm_refl. Qed.
Definition W_5d2d0 : bv 32 := 0x0400006f.
Lemma F_5d2d0 : CTabKA.F 0x5d2d0 W_5d2d0.
Proof. vm_refl. Qed.
Lemma D_5d2d0 : CTabKA.D W_5d2d0 (Jal 0 64).
Proof. vm_refl. Qed.
Definition W_5d2d4 : bv 32 := 0x000d5517.
Lemma F_5d2d4 : CTabKA.F 0x5d2d4 W_5d2d4.
Proof. vm_refl. Qed.
Lemma D_5d2d4 : CTabKA.D W_5d2d4 (Auipc 10 213).
Proof. vm_refl. Qed.
Definition W_5d2d8 : bv 32 := 0x3bc53503.
Lemma F_5d2d8 : CTabKA.F 0x5d2d8 W_5d2d8.
Proof. vm_refl. Qed.
Lemma D_5d2d8 : CTabKA.D W_5d2d8 (Load SZ8 true 10 10 956).
Proof. vm_refl. Qed.
Definition W_5d2dc : bv 32 := 0x00052503.
Lemma F_5d2dc : CTabKA.F 0x5d2dc W_5d2dc.
Proof. vm_refl. Qed.
Lemma D_5d2dc : CTabKA.D W_5d2dc (Load SZ4 true 10 10 0).
Proof. vm_refl. Qed.
Definition W_5d2e0 : bv 32 := 0x02050863.
Lemma F_5d2e0 : CTabKA.F 0x5d2e0 W_5d2e0.
Proof. vm_refl. Qed.
Lemma D_5d2e0 : CTabKA.D W_5d2e0 (Branch BC_EQ 10 0 48).
Proof. vm_refl. Qed.
Definition W_5d2e4 : bv 32 := 0x4a9250ef.
Lemma F_5d2e4 : CTabKA.F 0x5d2e4 W_5d2e4.
Proof. vm_refl. Qed.
Lemma D_5d2e4 : CTabKA.D W_5d2e4 (Jal 1 154792).
Proof. vm_refl. Qed.
Definition W_5d2e8 : bv 32 := 0x02050463.
Lemma F_5d2e8 : CTabKA.F 0x5d2e8 W_5d2e8.
Proof. vm_refl. Qed.
Lemma D_5d2e8 : CTabKA.D W_5d2e8 (Branch BC_EQ 10 0 40).
Proof. vm_refl. Qed.
Definition W_5d2ec : bv 32 := 0x02850583.
Lemma F_5d2ec : CTabKA.F 0x5d2ec W_5d2ec.
Proof. vm_refl. Qed.
Lemma D_5d2ec : CTabKA.D W_5d2ec (Load SZ1 true 11 10 40).
Proof. vm_refl. Qed.
Definition W_5d2f0 : bv 32 := 0x08058a63.
Lemma F_5d2f0 : CTabKA.F 0x5d2f0 W_5d2f0.
Proof. vm_refl. Qed.
Lemma D_5d2f0 : CTabKA.D W_5d2f0 (Branch BC_EQ 11 0 148).
Proof. vm_refl. Qed.
Definition W_5d2f4 : bv 32 := 0x00000513.
Lemma F_5d2f4 : CTabKA.F 0x5d2f4 W_5d2f4.
Proof. vm_refl. Qed.
Lemma D_5d2f4 : CTabKA.D W_5d2f4 (OpImm ALU_ADD 10 0 0).
Proof. vm_refl. Qed.
Definition W_5d2f8 : bv 32 := 0x01813083.
Lemma F_5d2f8 : CTabKA.F 0x5d2f8 W_5d2f8.
Proof. vm_refl. Qed.
Lemma D_5d2f8 : CTabKA.D W_5d2f8 (Load SZ8 true 1 2 24).
Proof. vm_refl. Qed.
Definition W_5d2fc : bv 32 := 0x01013403.
Lemma F_5d2fc : CTabKA.F 0x5d2fc W_5d2fc.
Proof. vm_refl. Qed.
Lemma D_5d2fc : CTabKA.D W_5d2fc (Load SZ8 true 8 2 16).
Proof. vm_refl. Qed.
Definition W_5d300 : bv 32 := 0x00813483.
Lemma F_5d300 : CTabKA.F 0x5d300 W_5d300.
Proof. vm_refl. Qed.
Lemma D_5d300 : CTabKA.D W_5d300 (Load SZ8 true 9 2 8).
Proof. vm_refl. Qed.
Definition W_5d304 : bv 32 := 0x00013903.
Lemma F_5d304 : CTabKA.F 0x5d304 W_5d304.
Proof. vm_refl. Qed.
Lemma D_5d304 : CTabKA.D W_5d304 (Load SZ8 true 18 2 0).
Proof. vm_refl. Qed.
Definition W_5d308 : bv 32 := 0x02010113.
Lemma F_5d308 : CTabKA.F 0x5d308 W_5d308.
Proof. vm_refl. Qed.
Lemma D_5d308 : CTabKA.D W_5d308 (OpImm ALU_ADD 2 2 32).
Proof. vm_refl. Qed.
Definition W_5d30c : bv 32 := 0x00008067.
Lemma F_5d30c : CTabKA.F 0x5d30c W_5d30c.
Proof. vm_refl. Qed.
Lemma D_5d30c : CTabKA.D W_5d30c (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_5d310 : bv 32 := 0x01813083.
Lemma F_5d310 : CTabKA.F 0x5d310 W_5d310.
Proof. vm_refl. Qed.
Lemma D_5d310 : CTabKA.D W_5d310 (Load SZ8 true 1 2 24).
Proof. vm_refl. Qed.
Definition W_5d314 : bv 32 := 0x01013403.
Lemma F_5d314 : CTabKA.F 0x5d314 W_5d314.
Proof. vm_refl. Qed.
Lemma D_5d314 : CTabKA.D W_5d314 (Load SZ8 true 8 2 16).
Proof. vm_refl. Qed.
Definition W_5d318 : bv 32 := 0x00813483.
Lemma F_5d318 : CTabKA.F 0x5d318 W_5d318.
Proof. vm_refl. Qed.
Lemma D_5d318 : CTabKA.D W_5d318 (Load SZ8 true 9 2 8).
Proof. vm_refl. Qed.
Definition W_5d31c : bv 32 := 0x00013903.
Lemma F_5d31c : CTabKA.F 0x5d31c W_5d31c.
Proof. vm_refl. Qed.
Lemma D_5d31c : CTabKA.D W_5d31c (Load SZ8 true 18 2 0).
Proof. vm_refl. Qed.
Definition W_5d320 : bv 32 := 0x02010113.
Lemma F_5d320 : CTabKA.F 0x5d320 W_5d320.
Proof. vm_refl. Qed.
Lemma D_5d320 : CTabKA.D W_5d320 (OpImm ALU_ADD 2 2 32).
Proof. vm_refl. Qed.
Definition W_5d324 : bv 32 := 0x00008067.
Lemma F_5d324 : CTabKA.F 0x5d324 W_5d324.
Proof. vm_refl. Qed.
Lemma D_5d324 : CTabKA.D W_5d324 (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_5d328 : bv 32 := 0x00160613.
Lemma F_5d328 : CTabKA.F 0x5d328 W_5d328.
Proof. vm_refl. Qed.
Lemma D_5d328 : CTabKA.D W_5d328 (OpImm ALU_ADD 12 12 1).
Proof. vm_refl. Qed.
Definition W_5d32c : bv 32 := 0x00100513.
Lemma F_5d32c : CTabKA.F 0x5d32c W_5d32c.
Proof. vm_refl. Qed.
Lemma D_5d32c : CTabKA.D W_5d32c (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_5d330 : bv 32 := 0xffb90913.
Lemma F_5d330 : CTabKA.F 0x5d330 W_5d330.
Proof. vm_refl. Qed.
Lemma D_5d330 : CTabKA.D W_5d330 (OpImm ALU_ADD 18 18 4091).
Proof. vm_refl. Qed.
Definition W_5d334 : bv 32 := 0x00681813.
Lemma F_5d334 : CTabKA.F 0x5d334 W_5d334.
Proof. vm_refl. Qed.
Lemma D_5d334 : CTabKA.D W_5d334 (ShiftImm ALU_SLL 16 16 6).
Proof. vm_refl. Qed.
Definition W_5d338 : bv 32 := 0x00c4b023.
Lemma F_5d338 : CTabKA.F 0x5d338 W_5d338.
Proof. vm_refl. Qed.
Lemma D_5d338 : CTabKA.D W_5d338 (Store SZ8 9 12 0).
Proof. vm_refl. Qed.
Definition W_5d33c : bv 32 := 0x00a78023.
Lemma F_5d33c : CTabKA.F 0x5d33c W_5d33c.
Proof. vm_refl. Qed.
Lemma D_5d33c : CTabKA.D W_5d33c (Store SZ1 15 10 0).
Proof. vm_refl. Qed.
Definition W_5d340 : bv 32 := 0x01251533.
Lemma F_5d340 : CTabKA.F 0x5d340 W_5d340.
Proof. vm_refl. Qed.
Lemma D_5d340 : CTabKA.D W_5d340 (Op ALU_SLL 10 10 18).
Proof. vm_refl. Qed.
Definition W_5d344 : bv 32 := 0x00a58533.
Lemma F_5d344 : CTabKA.F 0x5d344 W_5d344.
Proof. vm_refl. Qed.
Lemma D_5d344 : CTabKA.D W_5d344 (Op ALU_ADD 10 11 10).
Proof. vm_refl. Qed.
Definition W_5d348 : bv 32 := 0x010504b3.
Lemma F_5d348 : CTabKA.F 0x5d348 W_5d348.
Proof. vm_refl. Qed.
Lemma D_5d348 : CTabKA.D W_5d348 (Op ALU_ADD 9 10 16).
Proof. vm_refl. Qed.
Definition W_5d34c : bv 32 := 0x0084bc23.
Lemma F_5d34c : CTabKA.F 0x5d34c W_5d34c.
Proof. vm_refl. Qed.
Lemma D_5d34c : CTabKA.D W_5d34c (Store SZ8 9 8 24).
Proof. vm_refl. Qed.
Definition W_5d350 : bv 32 := 0x02f4bc23.
Lemma F_5d350 : CTabKA.F 0x5d350 W_5d350.
Proof. vm_refl. Qed.
Lemma D_5d350 : CTabKA.D W_5d350 (Store SZ8 9 15 56).
Proof. vm_refl. Qed.
Definition W_5d354 : bv 32 := 0x00048513.
Lemma F_5d354 : CTabKA.F 0x5d354 W_5d354.
Proof. vm_refl. Qed.
Lemma D_5d354 : CTabKA.D W_5d354 (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_5d358 : bv 32 := 0x6ec000ef.
Lemma F_5d358 : CTabKA.F 0x5d358 W_5d358.
Proof. vm_refl. Qed.
Lemma D_5d358 : CTabKA.D W_5d358 (Jal 1 1772).
Proof. vm_refl. Qed.
Definition W_5d35c : bv 32 := 0x00050593.
Lemma F_5d35c : CTabKA.F 0x5d35c W_5d35c.
Proof. vm_refl. Qed.
Lemma D_5d35c : CTabKA.D W_5d35c (OpImm ALU_ADD 11 10 0).
Proof. vm_refl. Qed.
Definition W_5d360 : bv 32 := 0x00048513.
Lemma F_5d360 : CTabKA.F 0x5d360 W_5d360.
Proof. vm_refl. Qed.
Lemma D_5d360 : CTabKA.D W_5d360 (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_5d364 : bv 32 := 0x00000613.
Lemma F_5d364 : CTabKA.F 0x5d364 W_5d364.
Proof. vm_refl. Qed.
Lemma D_5d364 : CTabKA.D W_5d364 (OpImm ALU_ADD 12 0 0).
Proof. vm_refl. Qed.
Definition W_5d368 : bv 32 := 0x0005b023.
Lemma F_5d368 : CTabKA.F 0x5d368 W_5d368.
Proof. vm_refl. Qed.
Lemma D_5d368 : CTabKA.D W_5d368 (Store SZ8 11 0 0).
Proof. vm_refl. Qed.
Definition W_5d36c : bv 32 := 0x01813083.
Lemma F_5d36c : CTabKA.F 0x5d36c W_5d36c.
Proof. vm_refl. Qed.
Lemma D_5d36c : CTabKA.D W_5d36c (Load SZ8 true 1 2 24).
Proof. vm_refl. Qed.
Definition W_5d370 : bv 32 := 0x01013403.
Lemma F_5d370 : CTabKA.F 0x5d370 W_5d370.
Proof. vm_refl. Qed.
Lemma D_5d370 : CTabKA.D W_5d370 (Load SZ8 true 8 2 16).
Proof. vm_refl. Qed.
Definition W_5d374 : bv 32 := 0x00813483.
Lemma F_5d374 : CTabKA.F 0x5d374 W_5d374.
Proof. vm_refl. Qed.
Lemma D_5d374 : CTabKA.D W_5d374 (Load SZ8 true 9 2 8).
Proof. vm_refl. Qed.
Definition W_5d378 : bv 32 := 0x00013903.
Lemma F_5d378 : CTabKA.F 0x5d378 W_5d378.
Proof. vm_refl. Qed.
Lemma D_5d378 : CTabKA.D W_5d378 (Load SZ8 true 18 2 0).
Proof. vm_refl. Qed.
Definition W_5d37c : bv 32 := 0x02010113.
Lemma F_5d37c : CTabKA.F 0x5d37c W_5d37c.
Proof. vm_refl. Qed.
Lemma D_5d37c : CTabKA.D W_5d37c (OpImm ALU_ADD 2 2 32).
Proof. vm_refl. Qed.
Definition W_5d380 : bv 32 := 0x00008067.
Lemma F_5d380 : CTabKA.F 0x5d380 W_5d380.
Proof. vm_refl. Qed.
Lemma D_5d380 : CTabKA.D W_5d380 (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_5d384 : bv 32 := 0x04853483.
Lemma F_5d384 : CTabKA.F 0x5d384 W_5d384.
Proof. vm_refl. Qed.
Lemma D_5d384 : CTabKA.D W_5d384 (Load SZ8 true 9 10 72).
Proof. vm_refl. Qed.
Definition W_5d388 : bv 32 := 0x00100593.
Lemma F_5d388 : CTabKA.F 0x5d388 W_5d388.
Proof. vm_refl. Qed.
Lemma D_5d388 : CTabKA.D W_5d388 (OpImm ALU_ADD 11 0 1).
Proof. vm_refl. Qed.
Definition W_5d38c : bv 32 := 0x0095e663.
Lemma F_5d38c : CTabKA.F 0x5d38c W_5d38c.
Proof. vm_refl. Qed.
Lemma D_5d38c : CTabKA.D W_5d38c (Branch BC_LTU 11 9 12).
Proof. vm_refl. Qed.
Definition W_5d390 : bv 32 := 0x671250ef.
Lemma F_5d390 : CTabKA.F 0x5d390 W_5d390.
Proof. vm_refl. Qed.
Lemma D_5d390 : CTabKA.D W_5d390 (Jal 1 155248).
Proof. vm_refl. Qed.
Definition W_5d394 : bv 32 := 0x00050493.
Lemma F_5d394 : CTabKA.F 0x5d394 W_5d394.
Proof. vm_refl. Qed.
Lemma D_5d394 : CTabKA.D W_5d394 (OpImm ALU_ADD 9 10 0).
Proof. vm_refl. Qed.
Definition W_5d398 : bv 32 := 0xec0490e3.
Lemma F_5d398 : CTabKA.F 0x5d398 W_5d398.
Proof. vm_refl. Qed.
Lemma D_5d398 : CTabKA.D W_5d398 (Branch BC_NE 9 0 7872).
Proof. vm_refl. Qed.
Definition W_5d39c : bv 32 := 0xf59ff06f.
Lemma F_5d39c : CTabKA.F 0x5d39c W_5d39c.
Proof. vm_refl. Qed.
Lemma D_5d39c : CTabKA.D W_5d39c (Jal 0 2096984).
Proof. vm_refl. Qed.

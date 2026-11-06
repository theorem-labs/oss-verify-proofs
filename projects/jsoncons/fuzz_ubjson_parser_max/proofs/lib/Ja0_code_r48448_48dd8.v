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
Definition W_5cde0 : bv 32 := 0xf7010113.
Lemma F_5cde0 : CTabKA.F 0x5cde0 W_5cde0.
Proof. vm_refl. Qed.
Lemma D_5cde0 : CTabKA.D W_5cde0 (OpImm ALU_ADD 2 2 3952).
Proof. vm_refl. Qed.
Definition W_5cde4 : bv 32 := 0x08113423.
Lemma F_5cde4 : CTabKA.F 0x5cde4 W_5cde4.
Proof. vm_refl. Qed.
Lemma D_5cde4 : CTabKA.D W_5cde4 (Store SZ8 2 1 136).
Proof. vm_refl. Qed.
Definition W_5cde8 : bv 32 := 0x08813023.
Lemma F_5cde8 : CTabKA.F 0x5cde8 W_5cde8.
Proof. vm_refl. Qed.
Lemma D_5cde8 : CTabKA.D W_5cde8 (Store SZ8 2 8 128).
Proof. vm_refl. Qed.
Definition W_5cdec : bv 32 := 0x06913c23.
Lemma F_5cdec : CTabKA.F 0x5cdec W_5cdec.
Proof. vm_refl. Qed.
Lemma D_5cdec : CTabKA.D W_5cdec (Store SZ8 2 9 120).
Proof. vm_refl. Qed.
Definition W_5cdf0 : bv 32 := 0x07213823.
Lemma F_5cdf0 : CTabKA.F 0x5cdf0 W_5cdf0.
Proof. vm_refl. Qed.
Lemma D_5cdf0 : CTabKA.D W_5cdf0 (Store SZ8 2 18 112).
Proof. vm_refl. Qed.
Definition W_5cdf4 : bv 32 := 0x07313423.
Lemma F_5cdf4 : CTabKA.F 0x5cdf4 W_5cdf4.
Proof. vm_refl. Qed.
Lemma D_5cdf4 : CTabKA.D W_5cdf4 (Store SZ8 2 19 104).
Proof. vm_refl. Qed.
Definition W_5cdf8 : bv 32 := 0x07413023.
Lemma F_5cdf8 : CTabKA.F 0x5cdf8 W_5cdf8.
Proof. vm_refl. Qed.
Lemma D_5cdf8 : CTabKA.D W_5cdf8 (Store SZ8 2 20 96).
Proof. vm_refl. Qed.
Definition W_5cdfc : bv 32 := 0x05513c23.
Lemma F_5cdfc : CTabKA.F 0x5cdfc W_5cdfc.
Proof. vm_refl. Qed.
Lemma D_5cdfc : CTabKA.D W_5cdfc (Store SZ8 2 21 88).
Proof. vm_refl. Qed.
Definition W_5ce00 : bv 32 := 0x05613823.
Lemma F_5ce00 : CTabKA.F 0x5ce00 W_5ce00.
Proof. vm_refl. Qed.
Lemma D_5ce00 : CTabKA.D W_5ce00 (Store SZ8 2 22 80).
Proof. vm_refl. Qed.
Definition W_5ce04 : bv 32 := 0x05713423.
Lemma F_5ce04 : CTabKA.F 0x5ce04 W_5ce04.
Proof. vm_refl. Qed.
Lemma D_5ce04 : CTabKA.D W_5ce04 (Store SZ8 2 23 72).
Proof. vm_refl. Qed.
Definition W_5ce08 : bv 32 := 0x05813023.
Lemma F_5ce08 : CTabKA.F 0x5ce08 W_5ce08.
Proof. vm_refl. Qed.
Lemma D_5ce08 : CTabKA.D W_5ce08 (Store SZ8 2 24 64).
Proof. vm_refl. Qed.
Definition W_5ce0c : bv 32 := 0x03913c23.
Lemma F_5ce0c : CTabKA.F 0x5ce0c W_5ce0c.
Proof. vm_refl. Qed.
Lemma D_5ce0c : CTabKA.D W_5ce0c (Store SZ8 2 25 56).
Proof. vm_refl. Qed.
Definition W_5ce10 : bv 32 := 0x03a13823.
Lemma F_5ce10 : CTabKA.F 0x5ce10 W_5ce10.
Proof. vm_refl. Qed.
Lemma D_5ce10 : CTabKA.D W_5ce10 (Store SZ8 2 26 48).
Proof. vm_refl. Qed.
Definition W_5ce14 : bv 32 := 0x03b13423.
Lemma F_5ce14 : CTabKA.F 0x5ce14 W_5ce14.
Proof. vm_refl. Qed.
Lemma D_5ce14 : CTabKA.D W_5ce14 (Store SZ8 2 27 40).
Proof. vm_refl. Qed.
Definition W_5ce18 : bv 32 := 0x00058493.
Lemma F_5ce18 : CTabKA.F 0x5ce18 W_5ce18.
Proof. vm_refl. Qed.
Lemma D_5ce18 : CTabKA.D W_5ce18 (OpImm ALU_ADD 9 11 0).
Proof. vm_refl. Qed.
Definition W_5ce1c : bv 32 := 0x00050c93.
Lemma F_5ce1c : CTabKA.F 0x5ce1c W_5ce1c.
Proof. vm_refl. Qed.
Lemma D_5ce1c : CTabKA.D W_5ce1c (OpImm ALU_ADD 25 10 0).
Proof. vm_refl. Qed.
Definition W_5ce20 : bv 32 := 0x16c260ef.
Lemma F_5ce20 : CTabKA.F 0x5ce20 W_5ce20.
Proof. vm_refl. Qed.
Lemma D_5ce20 : CTabKA.D W_5ce20 (Jal 1 156012).
Proof. vm_refl. Qed.
Definition W_5ce24 : bv 32 := 0x26050463.
Lemma F_5ce24 : CTabKA.F 0x5ce24 W_5ce24.
Proof. vm_refl. Qed.
Lemma D_5ce24 : CTabKA.D W_5ce24 (Branch BC_EQ 10 0 616).
Proof. vm_refl. Qed.
Definition W_5ce28 : bv 32 := 0x00050913.
Lemma F_5ce28 : CTabKA.F 0x5ce28 W_5ce28.
Proof. vm_refl. Qed.
Lemma D_5ce28 : CTabKA.D W_5ce28 (OpImm ALU_ADD 18 10 0).
Proof. vm_refl. Qed.
Definition W_5ce2c : bv 32 := 0x324260ef.
Lemma F_5ce2c : CTabKA.F 0x5ce2c W_5ce2c.
Proof. vm_refl. Qed.
Lemma D_5ce2c : CTabKA.D W_5ce2c (Jal 1 156452).
Proof. vm_refl. Qed.
Definition W_5ce30 : bv 32 := 0x00050993.
Lemma F_5ce30 : CTabKA.F 0x5ce30 W_5ce30.
Proof. vm_refl. Qed.
Lemma D_5ce30 : CTabKA.D W_5ce30 (OpImm ALU_ADD 19 10 0).
Proof. vm_refl. Qed.
Definition W_5ce34 : bv 32 := 0x00090513.
Lemma F_5ce34 : CTabKA.F 0x5ce34 W_5ce34.
Proof. vm_refl. Qed.
Lemma D_5ce34 : CTabKA.D W_5ce34 (OpImm ALU_ADD 10 18 0).
Proof. vm_refl. Qed.
Definition W_5ce38 : bv 32 := 0x370260ef.
Lemma F_5ce38 : CTabKA.F 0x5ce38 W_5ce38.
Proof. vm_refl. Qed.
Lemma D_5ce38 : CTabKA.D W_5ce38 (Jal 1 156528).
Proof. vm_refl. Qed.
Definition W_5ce3c : bv 32 := 0x2499e863.
Lemma F_5ce3c : CTabKA.F 0x5ce3c W_5ce3c.
Proof. vm_refl. Qed.
Lemma D_5ce3c : CTabKA.D W_5ce3c (Branch BC_LTU 19 9 592).
Proof. vm_refl. Qed.
Definition W_5ce40 : bv 32 := 0x00050913.
Lemma F_5ce40 : CTabKA.F 0x5ce40 W_5ce40.
Proof. vm_refl. Qed.
Lemma D_5ce40 : CTabKA.D W_5ce40 (OpImm ALU_ADD 18 10 0).
Proof. vm_refl. Qed.
Definition W_5ce44 : bv 32 := 0x24a4e463.
Lemma F_5ce44 : CTabKA.F 0x5ce44 W_5ce44.
Proof. vm_refl. Qed.
Lemma D_5ce44 : CTabKA.D W_5ce44 (Branch BC_LTU 9 10 584).
Proof. vm_refl. Qed.
Definition W_5ce48 : bv 32 := 0x00000d13.
Lemma F_5ce48 : CTabKA.F 0x5ce48 W_5ce48.
Proof. vm_refl. Qed.
Lemma D_5ce48 : CTabKA.D W_5ce48 (OpImm ALU_ADD 26 0 0).
Proof. vm_refl. Qed.
Definition W_5ce4c : bv 32 := 0x00001437.
Lemma F_5ce4c : CTabKA.F 0x5ce4c W_5ce4c.
Proof. vm_refl. Qed.
Lemma D_5ce4c : CTabKA.D W_5ce4c (Lui 8 1).
Proof. vm_refl. Qed.
Definition W_5ce50 : bv 32 := 0x000d5517.
Lemma F_5ce50 : CTabKA.F 0x5ce50 W_5ce50.
Proof. vm_refl. Qed.
Lemma D_5ce50 : CTabKA.D W_5ce50 (Auipc 10 213).
Proof. vm_refl. Qed.
Definition W_5ce54 : bv 32 := 0x000d5597.
Lemma F_5ce54 : CTabKA.F 0x5ce54 W_5ce54.
Proof. vm_refl. Qed.
Lemma D_5ce54 : CTabKA.D W_5ce54 (Auipc 11 213).
Proof. vm_refl. Qed.
Definition W_5ce58 : bv 32 := 0x000d5617.
Lemma F_5ce58 : CTabKA.F 0x5ce58 W_5ce58.
Proof. vm_refl. Qed.
Lemma D_5ce58 : CTabKA.D W_5ce58 (Auipc 12 213).
Proof. vm_refl. Qed.
Definition W_5ce5c : bv 32 := 0x000d5697.
Lemma F_5ce5c : CTabKA.F 0x5ce5c W_5ce5c.
Proof. vm_refl. Qed.
Lemma D_5ce5c : CTabKA.D W_5ce5c (Auipc 13 213).
Proof. vm_refl. Qed.
Definition W_5ce60 : bv 32 := 0x000d5717.
Lemma F_5ce60 : CTabKA.F 0x5ce60 W_5ce60.
Proof. vm_refl. Qed.
Lemma D_5ce60 : CTabKA.D W_5ce60 (Auipc 14 213).
Proof. vm_refl. Qed.
Definition W_5ce64 : bv 32 := 0xfffb3797.
Lemma F_5ce64 : CTabKA.F 0x5ce64 W_5ce64.
Proof. vm_refl. Qed.
Lemma D_5ce64 : CTabKA.D W_5ce64 (Auipc 15 1048499).
Proof. vm_refl. Qed.
Definition W_5ce68 : bv 32 := 0x008c8433.
Lemma F_5ce68 : CTabKA.F 0x5ce68 W_5ce68.
Proof. vm_refl. Qed.
Lemma D_5ce68 : CTabKA.D W_5ce68 (Op ALU_ADD 8 25 8).
Proof. vm_refl. Qed.
Definition W_5ce6c : bv 32 := 0x7e853b03.
Lemma F_5ce6c : CTabKA.F 0x5ce6c W_5ce6c.
Proof. vm_refl. Qed.
Lemma D_5ce6c : CTabKA.D W_5ce6c (Load SZ8 true 22 10 2024).
Proof. vm_refl. Qed.
Definition W_5ce70 : bv 32 := 0x7ec5b503.
Lemma F_5ce70 : CTabKA.F 0x5ce70 W_5ce70.
Proof. vm_refl. Qed.
Lemma D_5ce70 : CTabKA.D W_5ce70 (Load SZ8 true 10 11 2028).
Proof. vm_refl. Qed.
Definition W_5ce74 : bv 32 := 0x00a13c23.
Lemma F_5ce74 : CTabKA.F 0x5ce74 W_5ce74.
Proof. vm_refl. Qed.
Lemma D_5ce74 : CTabKA.D W_5ce74 (Store SZ8 2 10 24).
Proof. vm_refl. Qed.
Definition W_5ce78 : bv 32 := 0x7f063503.
Lemma F_5ce78 : CTabKA.F 0x5ce78 W_5ce78.
Proof. vm_refl. Qed.
Lemma D_5ce78 : CTabKA.D W_5ce78 (Load SZ8 true 10 12 2032).
Proof. vm_refl. Qed.
Definition W_5ce7c : bv 32 := 0x00a13823.
Lemma F_5ce7c : CTabKA.F 0x5ce7c W_5ce7c.
Proof. vm_refl. Qed.
Lemma D_5ce7c : CTabKA.D W_5ce7c (Store SZ8 2 10 16).
Proof. vm_refl. Qed.
Definition W_5ce80 : bv 32 := 0x7f46b503.
Lemma F_5ce80 : CTabKA.F 0x5ce80 W_5ce80.
Proof. vm_refl. Qed.
Lemma D_5ce80 : CTabKA.D W_5ce80 (Load SZ8 true 10 13 2036).
Proof. vm_refl. Qed.
Definition W_5ce84 : bv 32 := 0x00a13423.
Lemma F_5ce84 : CTabKA.F 0x5ce84 W_5ce84.
Proof. vm_refl. Qed.
Lemma D_5ce84 : CTabKA.D W_5ce84 (Store SZ8 2 10 8).
Proof. vm_refl. Qed.
Definition W_5ce88 : bv 32 := 0x7d073503.
Lemma F_5ce88 : CTabKA.F 0x5ce88 W_5ce88.
Proof. vm_refl. Qed.
Lemma D_5ce88 : CTabKA.D W_5ce88 (Load SZ8 true 10 14 2000).
Proof. vm_refl. Qed.
Definition W_5ce8c : bv 32 := 0x00a13023.
Lemma F_5ce8c : CTabKA.F 0x5ce8c W_5ce8c.
Proof. vm_refl. Qed.
Lemma D_5ce8c : CTabKA.D W_5ce8c (Store SZ8 2 10 0).
Proof. vm_refl. Qed.
Definition W_5ce90 : bv 32 := 0x50c7bb83.
Lemma F_5ce90 : CTabKA.F 0x5ce90 W_5ce90.
Proof. vm_refl. Qed.
Lemma D_5ce90 : CTabKA.D W_5ce90 (Load SZ8 true 23 15 1292).
Proof. vm_refl. Qed.
Definition W_5ce94 : bv 32 := 0x00100393.
Lemma F_5ce94 : CTabKA.F 0x5ce94 W_5ce94.
Proof. vm_refl. Qed.
Lemma D_5ce94 : CTabKA.D W_5ce94 (OpImm ALU_ADD 7 0 1).
Proof. vm_refl. Qed.
Definition W_5ce98 : bv 32 := 0x00600e13.
Lemma F_5ce98 : CTabKA.F 0x5ce98 W_5ce98.
Proof. vm_refl. Qed.
Lemma D_5ce98 : CTabKA.D W_5ce98 (OpImm ALU_ADD 28 0 6).
Proof. vm_refl. Qed.
Definition W_5ce9c : bv 32 := 0x00000a13.
Lemma F_5ce9c : CTabKA.F 0x5ce9c W_5ce9c.
Proof. vm_refl. Qed.
Lemma D_5ce9c : CTabKA.D W_5ce9c (OpImm ALU_ADD 20 0 0).
Proof. vm_refl. Qed.
Definition W_5cea0 : bv 32 := 0x0100006f.
Lemma F_5cea0 : CTabKA.F 0x5cea0 W_5cea0.
Proof. vm_refl. Qed.
Lemma D_5cea0 : CTabKA.D W_5cea0 (Jal 0 16).
Proof. vm_refl. Qed.
Definition W_5cea4 : bv 32 := 0x001a0a13.
Lemma F_5cea4 : CTabKA.F 0x5cea4 W_5cea4.
Proof. vm_refl. Qed.
Lemma D_5cea4 : CTabKA.D W_5cea4 (OpImm ALU_ADD 20 20 1).
Proof. vm_refl. Qed.
Definition W_5cea8 : bv 32 := 0x00b00513.
Lemma F_5cea8 : CTabKA.F 0x5cea8 W_5cea8.
Proof. vm_refl. Qed.
Lemma D_5cea8 : CTabKA.D W_5cea8 (OpImm ALU_ADD 10 0 11).
Proof. vm_refl. Qed.
Definition W_5ceac : bv 32 := 0x1caa0e63.
Lemma F_5ceac : CTabKA.F 0x5ceac W_5ceac.
Proof. vm_refl. Qed.
Lemma D_5ceac : CTabKA.D W_5ceac (Branch BC_EQ 20 10 476).
Proof. vm_refl. Qed.
Definition W_5ceb0 : bv 32 := 0x00000d93.
Lemma F_5ceb0 : CTabKA.F 0x5ceb0 W_5ceb0.
Proof. vm_refl. Qed.
Lemma D_5ceb0 : CTabKA.D W_5ceb0 (OpImm ALU_ADD 27 0 0).
Proof. vm_refl. Qed.
Definition W_5ceb4 : bv 32 := 0x058cb503.
Lemma F_5ceb4 : CTabKA.F 0x5ceb4 W_5ceb4.
Proof. vm_refl. Qed.
Lemma D_5ceb4 : CTabKA.D W_5ceb4 (Load SZ8 true 10 25 88).
Proof. vm_refl. Qed.
Definition W_5ceb8 : bv 32 := 0x00a00593.
Lemma F_5ceb8 : CTabKA.F 0x5ceb8 W_5ceb8.
Proof. vm_refl. Qed.
Lemma D_5ceb8 : CTabKA.D W_5ceb8 (OpImm ALU_ADD 11 0 10).
Proof. vm_refl. Qed.
Definition W_5cebc : bv 32 := 0x414585bb.
Lemma F_5cebc : CTabKA.F 0x5cebc W_5cebc.
Proof. vm_refl. Qed.
Lemma D_5cebc : CTabKA.D W_5cebc (Op32 ALU_SUB 11 11 20).
Proof. vm_refl. Qed.
Definition W_5cec0 : bv 32 := 0x006a0a93.
Lemma F_5cec0 : CTabKA.F 0x5cec0 W_5cec0.
Proof. vm_refl. Qed.
Lemma D_5cec0 : CTabKA.D W_5cec0 (OpImm ALU_ADD 21 20 6).
Proof. vm_refl. Qed.
Definition W_5cec4 : bv 32 := 0xfff00613.
Lemma F_5cec4 : CTabKA.F 0x5cec4 W_5cec4.
Proof. vm_refl. Qed.
Lemma D_5cec4 : CTabKA.D W_5cec4 (OpImm ALU_ADD 12 0 4095).
Proof. vm_refl. Qed.
Definition W_5cec8 : bv 32 := 0x00b615b3.
Lemma F_5cec8 : CTabKA.F 0x5cec8 W_5cec8.
Proof. vm_refl. Qed.
Lemma D_5cec8 : CTabKA.D W_5cec8 (Op ALU_SLL 11 12 11).
Proof. vm_refl. Qed.
Definition W_5cecc : bv 32 := 0x3ff5f593.
Lemma F_5cecc : CTabKA.F 0x5cecc W_5cecc.
Proof. vm_refl. Qed.
Lemma D_5cecc : CTabKA.D W_5cecc (OpImm ALU_AND 11 11 1023).
Proof. vm_refl. Qed.
Definition W_5ced0 : bv 32 := 0xff150613.
Lemma F_5ced0 : CTabKA.F 0x5ced0 W_5ced0.
Proof. vm_refl. Qed.
Lemma D_5ced0 : CTabKA.D W_5ced0 (OpImm ALU_ADD 12 10 4081).
Proof. vm_refl. Qed.
Definition W_5ced4 : bv 32 := 0x414509b3.
Lemma F_5ced4 : CTabKA.F 0x5ced4 W_5ced4.
Proof. vm_refl. Qed.
Lemma D_5ced4 : CTabKA.D W_5ced4 (Op ALU_SUB 19 10 20).
Proof. vm_refl. Qed.
Definition W_5ced8 : bv 32 := 0x00c59c33.
Lemma F_5ced8 : CTabKA.F 0x5ced8 W_5ced8.
Proof. vm_refl. Qed.
Lemma D_5ced8 : CTabKA.D W_5ced8 (Op ALU_SLL 24 11 12).
Proof. vm_refl. Qed.
Definition W_5cedc : bv 32 := 0xffa98993.
Lemma F_5cedc : CTabKA.F 0x5cedc W_5cedc.
Proof. vm_refl. Qed.
Lemma D_5cedc : CTabKA.D W_5cedc (OpImm ALU_ADD 19 19 4090).
Proof. vm_refl. Qed.
Definition W_5cee0 : bv 32 := 0x01840c33.
Lemma F_5cee0 : CTabKA.F 0x5cee0 W_5cee0.
Proof. vm_refl. Qed.
Lemma D_5cee0 : CTabKA.D W_5cee0 (Op ALU_ADD 24 8 24).
Proof. vm_refl. Qed.
Definition W_5cee4 : bv 32 := 0x04000513.
Lemma F_5cee4 : CTabKA.F 0x5cee4 W_5cee4.
Proof. vm_refl. Qed.
Lemma D_5cee4 : CTabKA.D W_5cee4 (OpImm ALU_ADD 10 0 64).
Proof. vm_refl. Qed.
Definition W_5cee8 : bv 32 := 0x01451533.
Lemma F_5cee8 : CTabKA.F 0x5cee8 W_5cee8.
Proof. vm_refl. Qed.
Lemma D_5cee8 : CTabKA.D W_5cee8 (Op ALU_SLL 10 10 20).
Proof. vm_refl. Qed.
Definition W_5ceec : bv 32 := 0x02a13023.
Lemma F_5ceec : CTabKA.F 0x5ceec W_5ceec.
Proof. vm_refl. Qed.
Lemma D_5ceec : CTabKA.D W_5ceec (Store SZ8 2 10 32).
Proof. vm_refl. Qed.
Definition W_5cef0 : bv 32 := 0x0240006f.
Lemma F_5cef0 : CTabKA.F 0x5cef0 W_5cef0.
Proof. vm_refl. Qed.
Lemma D_5cef0 : CTabKA.D W_5cef0 (Jal 0 36).
Proof. vm_refl. Qed.
Definition W_5cf08 : bv 32 := 0x001d8d93.
Lemma F_5cf08 : CTabKA.F 0x5cf08 W_5cf08.
Proof. vm_refl. Qed.
Lemma D_5cf08 : CTabKA.D W_5cf08 (OpImm ALU_ADD 27 27 1).
Proof. vm_refl. Qed.
Definition W_5cf0c : bv 32 := 0x013dd533.
Lemma F_5cf0c : CTabKA.F 0x5cf0c W_5cf0c.
Proof. vm_refl. Qed.
Lemma D_5cf0c : CTabKA.D W_5cf0c (Op ALU_SRL 10 27 19).
Proof. vm_refl. Qed.
Definition W_5cf10 : bv 32 := 0xf8051ae3.
Lemma F_5cf10 : CTabKA.F 0x5cf10 W_5cf10.
Proof. vm_refl. Qed.
Lemma D_5cf10 : CTabKA.D W_5cf10 (Branch BC_NE 10 0 8084).
Proof. vm_refl. Qed.
Definition W_5cf14 : bv 32 := 0x01bc05b3.
Lemma F_5cf14 : CTabKA.F 0x5cf14 W_5cf14.
Proof. vm_refl. Qed.
Lemma D_5cf14 : CTabKA.D W_5cf14 (Op ALU_ADD 11 24 27).
Proof. vm_refl. Qed.
Definition W_5cf18 : bv 32 := 0x0005c503.
Lemma F_5cf18 : CTabKA.F 0x5cf18 W_5cf18.
Proof. vm_refl. Qed.
Lemma D_5cf18 : CTabKA.D W_5cf18 (Load SZ1 false 10 11 0).
Proof. vm_refl. Qed.
Definition W_5cf1c : bv 32 := 0xfe0506e3.
Lemma F_5cf1c : CTabKA.F 0x5cf1c W_5cf1c.
Proof. vm_refl. Qed.
Lemma D_5cf1c : CTabKA.D W_5cf1c (Branch BC_EQ 10 0 8172).
Proof. vm_refl. Qed.
Definition W_5cf20 : bv 32 := 0x058cb503.
Lemma F_5cf20 : CTabKA.F 0x5cf20 W_5cf20.
Proof. vm_refl. Qed.
Lemma D_5cf20 : CTabKA.D W_5cf20 (Load SZ8 true 10 25 88).
Proof. vm_refl. Qed.
Definition W_5cf24 : bv 32 := 0xffb50613.
Lemma F_5cf24 : CTabKA.F 0x5cf24 W_5cf24.
Proof. vm_refl. Qed.
Lemma D_5cf24 : CTabKA.D W_5cf24 (OpImm ALU_ADD 12 10 4091).
Proof. vm_refl. Qed.
Definition W_5cf28 : bv 32 := 0x00aa1533.
Lemma F_5cf28 : CTabKA.F 0x5cf28 W_5cf28.
Proof. vm_refl. Qed.
Lemma D_5cf28 : CTabKA.D W_5cf28 (Op ALU_SLL 10 20 10).
Proof. vm_refl. Qed.
Definition W_5cf2c : bv 32 := 0x00c39633.
Lemma F_5cf2c : CTabKA.F 0x5cf2c W_5cf2c.
Proof. vm_refl. Qed.
Lemma D_5cf2c : CTabKA.D W_5cf2c (Op ALU_SLL 12 7 12).
Proof. vm_refl. Qed.
Definition W_5cf30 : bv 32 := 0x00a40533.
Lemma F_5cf30 : CTabKA.F 0x5cf30 W_5cf30.
Proof. vm_refl. Qed.
Lemma D_5cf30 : CTabKA.D W_5cf30 (Op ALU_ADD 10 8 10).
Proof. vm_refl. Qed.
Definition W_5cf34 : bv 32 := 0x00c50533.
Lemma F_5cf34 : CTabKA.F 0x5cf34 W_5cf34.
Proof. vm_refl. Qed.
Lemma D_5cf34 : CTabKA.D W_5cf34 (Op ALU_ADD 10 10 12).
Proof. vm_refl. Qed.
Definition W_5cf38 : bv 32 := 0x015d9633.
Lemma F_5cf38 : CTabKA.F 0x5cf38 W_5cf38.
Proof. vm_refl. Qed.
Lemma D_5cf38 : CTabKA.D W_5cf38 (Op ALU_SLL 12 27 21).
Proof. vm_refl. Qed.
Definition W_5cf3c : bv 32 := 0x00c50533.
Lemma F_5cf3c : CTabKA.F 0x5cf3c W_5cf3c.
Proof. vm_refl. Qed.
Lemma D_5cf3c : CTabKA.D W_5cf3c (Op ALU_ADD 10 10 12).
Proof. vm_refl. Qed.
Definition W_5cf40 : bv 32 := 0x01853603.
Lemma F_5cf40 : CTabKA.F 0x5cf40 W_5cf40.
Proof. vm_refl. Qed.
Lemma D_5cf40 : CTabKA.D W_5cf40 (Load SZ8 true 12 10 24).
Proof. vm_refl. Qed.
Definition W_5cf44 : bv 32 := 0xfcc972e3.
Lemma F_5cf44 : CTabKA.F 0x5cf44 W_5cf44.
Proof. vm_refl. Qed.
Lemma D_5cf44 : CTabKA.D W_5cf44 (Branch BC_GEU 18 12 8132).
Proof. vm_refl. Qed.
Definition W_5cf48 : bv 32 := 0xfc9670e3.
Lemma F_5cf48 : CTabKA.F 0x5cf48 W_5cf48.
Proof. vm_refl. Qed.
Lemma D_5cf48 : CTabKA.D W_5cf48 (Branch BC_GEU 12 9 8128).
Proof. vm_refl. Qed.
Definition W_5cf4c : bv 32 := 0x01a58023.
Lemma F_5cf4c : CTabKA.F 0x5cf4c W_5cf4c.
Proof. vm_refl. Qed.
Lemma D_5cf4c : CTabKA.D W_5cf4c (Store SZ1 11 26 0).
Proof. vm_refl. Qed.
Definition W_5cf50 : bv 32 := 0x000b3583.
Lemma F_5cf50 : CTabKA.F 0x5cf50 W_5cf50.
Proof. vm_refl. Qed.
Lemma D_5cf50 : CTabKA.D W_5cf50 (Load SZ8 true 11 22 0).
Proof. vm_refl. Qed.
Definition W_5cf54 : bv 32 := 0xfff58613.
Lemma F_5cf54 : CTabKA.F 0x5cf54 W_5cf54.
Proof. vm_refl. Qed.
Lemma D_5cf54 : CTabKA.D W_5cf54 (OpImm ALU_ADD 12 11 4095).
Proof. vm_refl. Qed.
Definition W_5cf58 : bv 32 := 0x00c5b6b3.
Lemma F_5cf58 : CTabKA.F 0x5cf58 W_5cf58.
Proof. vm_refl. Qed.
Lemma D_5cf58 : CTabKA.D W_5cf58 (Op ALU_SLTU 13 11 12).
Proof. vm_refl. Qed.
Definition W_5cf5c : bv 32 := 0xfff68693.
Lemma F_5cf5c : CTabKA.F 0x5cf5c W_5cf5c.
Proof. vm_refl. Qed.
Lemma D_5cf5c : CTabKA.D W_5cf5c (OpImm ALU_ADD 13 13 4095).
Proof. vm_refl. Qed.
Definition W_5cf60 : bv 32 := 0x00c6f6b3.
Lemma F_5cf60 : CTabKA.F 0x5cf60 W_5cf60.
Proof. vm_refl. Qed.
Lemma D_5cf60 : CTabKA.D W_5cf60 (Op ALU_AND 13 13 12).
Proof. vm_refl. Qed.
Definition W_5cf64 : bv 32 := 0x02a6fc63.
Lemma F_5cf64 : CTabKA.F 0x5cf64 W_5cf64.
Proof. vm_refl. Qed.
Lemma D_5cf64 : CTabKA.D W_5cf64 (Branch BC_GEU 13 10 56).
Proof. vm_refl. Qed.
Definition W_5cf68 : bv 32 := 0x01813683.
Lemma F_5cf68 : CTabKA.F 0x5cf68 W_5cf68.
Proof. vm_refl. Qed.
Lemma D_5cf68 : CTabKA.D W_5cf68 (Load SZ8 true 13 2 24).
Proof. vm_refl. Qed.
Definition W_5cf6c : bv 32 := 0x0006b803.
Lemma F_5cf6c : CTabKA.F 0x5cf6c W_5cf6c.
Proof. vm_refl. Qed.
Lemma D_5cf6c : CTabKA.D W_5cf6c (Load SZ8 true 16 13 0).
Proof. vm_refl. Qed.
Definition W_5cf70 : bv 32 := 0x01013683.
Lemma F_5cf70 : CTabKA.F 0x5cf70 W_5cf70.
Proof. vm_refl. Qed.
Lemma D_5cf70 : CTabKA.D W_5cf70 (Load SZ8 true 13 2 16).
Proof. vm_refl. Qed.
Definition W_5cf74 : bv 32 := 0x0006b683.
Lemma F_5cf74 : CTabKA.F 0x5cf74 W_5cf74.
Proof. vm_refl. Qed.
Lemma D_5cf74 : CTabKA.D W_5cf74 (Load SZ8 true 13 13 0).
Proof. vm_refl. Qed.
Definition W_5cf78 : bv 32 := 0xfff80793.
Lemma F_5cf78 : CTabKA.F 0x5cf78 W_5cf78.
Proof. vm_refl. Qed.
Lemma D_5cf78 : CTabKA.D W_5cf78 (OpImm ALU_ADD 15 16 4095).
Proof. vm_refl. Qed.
Definition W_5cf7c : bv 32 := 0x00a7f463.
Lemma F_5cf7c : CTabKA.F 0x5cf7c W_5cf7c.
Proof. vm_refl. Qed.
Lemma D_5cf7c : CTabKA.D W_5cf7c (Branch BC_GEU 15 10 8).
Proof. vm_refl. Qed.
Definition W_5cf84 : bv 32 := 0x00813703.
Lemma F_5cf84 : CTabKA.F 0x5cf84 W_5cf84.
Proof. vm_refl. Qed.
Lemma D_5cf84 : CTabKA.D W_5cf84 (Load SZ8 true 14 2 8).
Proof. vm_refl. Qed.
Definition W_5cf88 : bv 32 := 0x00073283.
Lemma F_5cf88 : CTabKA.F 0x5cf88 W_5cf88.
Proof. vm_refl. Qed.
Lemma D_5cf88 : CTabKA.D W_5cf88 (Load SZ8 true 5 14 0).
Proof. vm_refl. Qed.
Definition W_5cf8c : bv 32 := 0x0032d713.
Lemma F_5cf8c : CTabKA.F 0x5cf8c W_5cf8c.
Proof. vm_refl. Qed.
Lemma D_5cf8c : CTabKA.D W_5cf8c (ShiftImm ALU_SRL 14 5 3).
Proof. vm_refl. Qed.
Definition W_5cf90 : bv 32 := 0x00b708b3.
Lemma F_5cf90 : CTabKA.F 0x5cf90 W_5cf90.
Proof. vm_refl. Qed.
Lemma D_5cf90 : CTabKA.D W_5cf90 (Op ALU_ADD 17 14 11).
Proof. vm_refl. Qed.
Definition W_5cf94 : bv 32 := 0x02a2e863.
Lemma F_5cf94 : CTabKA.F 0x5cf94 W_5cf94.
Proof. vm_refl. Qed.
Lemma D_5cf94 : CTabKA.D W_5cf94 (Branch BC_LTU 5 10 48).
Proof. vm_refl. Qed.
Definition W_5cf98 : bv 32 := 0x02a8f663.
Lemma F_5cf98 : CTabKA.F 0x5cf98 W_5cf98.
Proof. vm_refl. Qed.
Lemma D_5cf98 : CTabKA.D W_5cf98 (Branch BC_GEU 17 10 44).
Proof. vm_refl. Qed.
Definition W_5cf9c : bv 32 := 0xf54e6ce3.
Lemma F_5cf9c : CTabKA.F 0x5cf9c W_5cf9c.
Proof. vm_refl. Qed.
Lemma D_5cf9c : CTabKA.D W_5cf9c (Branch BC_LTU 28 20 8024).
Proof. vm_refl. Qed.
Definition W_5cfa0 : bv 32 := 0x00355513.
Lemma F_5cfa0 : CTabKA.F 0x5cfa0 W_5cfa0.
Proof. vm_refl. Qed.
Lemma D_5cfa0 : CTabKA.D W_5cfa0 (ShiftImm ALU_SRL 10 10 3).
Proof. vm_refl. Qed.
Definition W_5cfa4 : bv 32 := 0x00a585b3.
Lemma F_5cfa4 : CTabKA.F 0x5cfa4 W_5cfa4.
Proof. vm_refl. Qed.
Lemma D_5cfa4 : CTabKA.D W_5cfa4 (Op ALU_ADD 11 11 10).
Proof. vm_refl. Qed.
Definition W_5cfa8 : bv 32 := 0x00100513.
Lemma F_5cfa8 : CTabKA.F 0x5cfa8 W_5cfa8.
Proof. vm_refl. Qed.
Lemma D_5cfa8 : CTabKA.D W_5cfa8 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_5cfac : bv 32 := 0x0175b023.
Lemma F_5cfac : CTabKA.F 0x5cfac W_5cfac.
Proof. vm_refl. Qed.
Lemma D_5cfac : CTabKA.D W_5cfac (Store SZ8 11 23 0).
Proof. vm_refl. Qed.
Definition W_5cfb0 : bv 32 := 0x01455633.
Lemma F_5cfb0 : CTabKA.F 0x5cfb0 W_5cfb0.
Proof. vm_refl. Qed.
Lemma D_5cfb0 : CTabKA.D W_5cfb0 (Op ALU_SRL 12 10 20).
Proof. vm_refl. Qed.
Definition W_5cfb4 : bv 32 := 0x00858593.
Lemma F_5cfb4 : CTabKA.F 0x5cfb4 W_5cfb4.
Proof. vm_refl. Qed.
Lemma D_5cfb4 : CTabKA.D W_5cfb4 (OpImm ALU_ADD 11 11 8).
Proof. vm_refl. Qed.
Definition W_5cfb8 : bv 32 := 0x00150513.
Lemma F_5cfb8 : CTabKA.F 0x5cfb8 W_5cfb8.
Proof. vm_refl. Qed.
Lemma D_5cfb8 : CTabKA.D W_5cfb8 (OpImm ALU_ADD 10 10 1).
Proof. vm_refl. Qed.
Definition W_5cfbc : bv 32 := 0xfe0608e3.
Lemma F_5cfbc : CTabKA.F 0x5cfbc W_5cfbc.
Proof. vm_refl. Qed.
Lemma D_5cfbc : CTabKA.D W_5cfbc (Branch BC_EQ 12 0 8176).
Proof. vm_refl. Qed.
Definition W_5cfc0 : bv 32 := 0xf49ff06f.
Lemma F_5cfc0 : CTabKA.F 0x5cfc0 W_5cfc0.
Proof. vm_refl. Qed.
Lemma D_5cfc0 : CTabKA.D W_5cfc0 (Jal 0 2096968).
Proof. vm_refl. Qed.
Definition W_5d088 : bv 32 := 0x060c8023.
Lemma F_5d088 : CTabKA.F 0x5d088 W_5d088.
Proof. vm_refl. Qed.
Lemma D_5d088 : CTabKA.D W_5d088 (Store SZ1 25 0 96).
Proof. vm_refl. Qed.
Definition W_5d08c : bv 32 := 0x08813083.
Lemma F_5d08c : CTabKA.F 0x5d08c W_5d08c.
Proof. vm_refl. Qed.
Lemma D_5d08c : CTabKA.D W_5d08c (Load SZ8 true 1 2 136).
Proof. vm_refl. Qed.
Definition W_5d090 : bv 32 := 0x08013403.
Lemma F_5d090 : CTabKA.F 0x5d090 W_5d090.
Proof. vm_refl. Qed.
Lemma D_5d090 : CTabKA.D W_5d090 (Load SZ8 true 8 2 128).
Proof. vm_refl. Qed.
Definition W_5d094 : bv 32 := 0x07813483.
Lemma F_5d094 : CTabKA.F 0x5d094 W_5d094.
Proof. vm_refl. Qed.
Lemma D_5d094 : CTabKA.D W_5d094 (Load SZ8 true 9 2 120).
Proof. vm_refl. Qed.
Definition W_5d098 : bv 32 := 0x07013903.
Lemma F_5d098 : CTabKA.F 0x5d098 W_5d098.
Proof. vm_refl. Qed.
Lemma D_5d098 : CTabKA.D W_5d098 (Load SZ8 true 18 2 112).
Proof. vm_refl. Qed.
Definition W_5d09c : bv 32 := 0x06813983.
Lemma F_5d09c : CTabKA.F 0x5d09c W_5d09c.
Proof. vm_refl. Qed.
Lemma D_5d09c : CTabKA.D W_5d09c (Load SZ8 true 19 2 104).
Proof. vm_refl. Qed.
Definition W_5d0a0 : bv 32 := 0x06013a03.
Lemma F_5d0a0 : CTabKA.F 0x5d0a0 W_5d0a0.
Proof. vm_refl. Qed.
Lemma D_5d0a0 : CTabKA.D W_5d0a0 (Load SZ8 true 20 2 96).
Proof. vm_refl. Qed.
Definition W_5d0a4 : bv 32 := 0x05813a83.
Lemma F_5d0a4 : CTabKA.F 0x5d0a4 W_5d0a4.
Proof. vm_refl. Qed.
Lemma D_5d0a4 : CTabKA.D W_5d0a4 (Load SZ8 true 21 2 88).
Proof. vm_refl. Qed.
Definition W_5d0a8 : bv 32 := 0x05013b03.
Lemma F_5d0a8 : CTabKA.F 0x5d0a8 W_5d0a8.
Proof. vm_refl. Qed.
Lemma D_5d0a8 : CTabKA.D W_5d0a8 (Load SZ8 true 22 2 80).
Proof. vm_refl. Qed.
Definition W_5d0ac : bv 32 := 0x04813b83.
Lemma F_5d0ac : CTabKA.F 0x5d0ac W_5d0ac.
Proof. vm_refl. Qed.
Lemma D_5d0ac : CTabKA.D W_5d0ac (Load SZ8 true 23 2 72).
Proof. vm_refl. Qed.
Definition W_5d0b0 : bv 32 := 0x04013c03.
Lemma F_5d0b0 : CTabKA.F 0x5d0b0 W_5d0b0.
Proof. vm_refl. Qed.
Lemma D_5d0b0 : CTabKA.D W_5d0b0 (Load SZ8 true 24 2 64).
Proof. vm_refl. Qed.
Definition W_5d0b4 : bv 32 := 0x03813c83.
Lemma F_5d0b4 : CTabKA.F 0x5d0b4 W_5d0b4.
Proof. vm_refl. Qed.
Lemma D_5d0b4 : CTabKA.D W_5d0b4 (Load SZ8 true 25 2 56).
Proof. vm_refl. Qed.
Definition W_5d0b8 : bv 32 := 0x03013d03.
Lemma F_5d0b8 : CTabKA.F 0x5d0b8 W_5d0b8.
Proof. vm_refl. Qed.
Lemma D_5d0b8 : CTabKA.D W_5d0b8 (Load SZ8 true 26 2 48).
Proof. vm_refl. Qed.
Definition W_5d0bc : bv 32 := 0x02813d83.
Lemma F_5d0bc : CTabKA.F 0x5d0bc W_5d0bc.
Proof. vm_refl. Qed.
Lemma D_5d0bc : CTabKA.D W_5d0bc (Load SZ8 true 27 2 40).
Proof. vm_refl. Qed.
Definition W_5d0c0 : bv 32 := 0x09010113.
Lemma F_5d0c0 : CTabKA.F 0x5d0c0 W_5d0c0.
Proof. vm_refl. Qed.
Lemma D_5d0c0 : CTabKA.D W_5d0c0 (OpImm ALU_ADD 2 2 144).
Proof. vm_refl. Qed.
Definition W_5d0c4 : bv 32 := 0x00008067.
Lemma F_5d0c4 : CTabKA.F 0x5d0c4 W_5d0c4.
Proof. vm_refl. Qed.
Lemma D_5d0c4 : CTabKA.D W_5d0c4 (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_5d0c8 : bv 32 := 0x00100593.
Lemma F_5d0c8 : CTabKA.F 0x5d0c8 W_5d0c8.
Proof. vm_refl. Qed.
Lemma D_5d0c8 : CTabKA.D W_5d0c8 (OpImm ALU_ADD 11 0 1).
Proof. vm_refl. Qed.
Definition W_5d0cc : bv 32 := 0x06b50023.
Lemma F_5d0cc : CTabKA.F 0x5d0cc W_5d0cc.
Proof. vm_refl. Qed.
Lemma D_5d0cc : CTabKA.D W_5d0cc (Store SZ1 10 11 96).
Proof. vm_refl. Qed.
Definition W_5d0d0 : bv 32 := 0x00008067.
Lemma F_5d0d0 : CTabKA.F 0x5d0d0 W_5d0d0.
Proof. vm_refl. Qed.
Lemma D_5d0d0 : CTabKA.D W_5d0d0 (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_5d3a0 : bv 32 := 0xfe010113.
Lemma F_5d3a0 : CTabKA.F 0x5d3a0 W_5d3a0.
Proof. vm_refl. Qed.
Lemma D_5d3a0 : CTabKA.D W_5d3a0 (OpImm ALU_ADD 2 2 4064).
Proof. vm_refl. Qed.
Definition W_5d3a4 : bv 32 := 0x00113c23.
Lemma F_5d3a4 : CTabKA.F 0x5d3a4 W_5d3a4.
Proof. vm_refl. Qed.
Lemma D_5d3a4 : CTabKA.D W_5d3a4 (Store SZ8 2 1 24).
Proof. vm_refl. Qed.
Definition W_5d3a8 : bv 32 := 0x00813823.
Lemma F_5d3a8 : CTabKA.F 0x5d3a8 W_5d3a8.
Proof. vm_refl. Qed.
Lemma D_5d3a8 : CTabKA.D W_5d3a8 (Store SZ8 2 8 16).
Proof. vm_refl. Qed.
Definition W_5d3ac : bv 32 := 0x00913423.
Lemma F_5d3ac : CTabKA.F 0x5d3ac W_5d3ac.
Proof. vm_refl. Qed.
Lemma D_5d3ac : CTabKA.D W_5d3ac (Store SZ8 2 9 8).
Proof. vm_refl. Qed.
Definition W_5d3b0 : bv 32 := 0x01213023.
Lemma F_5d3b0 : CTabKA.F 0x5d3b0 W_5d3b0.
Proof. vm_refl. Qed.
Lemma D_5d3b0 : CTabKA.D W_5d3b0 (Store SZ8 2 18 0).
Proof. vm_refl. Qed.
Definition W_5d3b4 : bv 32 := 0x02010413.
Lemma F_5d3b4 : CTabKA.F 0x5d3b4 W_5d3b4.
Proof. vm_refl. Qed.
Lemma D_5d3b4 : CTabKA.D W_5d3b4 (OpImm ALU_ADD 8 2 32).
Proof. vm_refl. Qed.
Definition W_5d3b8 : bv 32 := 0x000d6517.
Lemma F_5d3b8 : CTabKA.F 0x5d3b8 W_5d3b8.
Proof. vm_refl. Qed.
Lemma D_5d3b8 : CTabKA.D W_5d3b8 (Auipc 10 214).
Proof. vm_refl. Qed.
Definition W_5d3bc : bv 32 := 0x07850513.
Lemma F_5d3bc : CTabKA.F 0x5d3bc W_5d3bc.
Proof. vm_refl. Qed.
Lemma D_5d3bc : CTabKA.D W_5d3bc (OpImm ALU_ADD 10 10 120).
Proof. vm_refl. Qed.
Definition W_5d3c0 : bv 32 := 0x6d8050ef.
Lemma F_5d3c0 : CTabKA.F 0x5d3c0 W_5d3c0.
Proof. vm_refl. Qed.
Lemma D_5d3c0 : CTabKA.D W_5d3c0 (Jal 1 22232).
Proof. vm_refl. Qed.
Definition W_5d3c4 : bv 32 := 0x00053483.
Lemma F_5d3c4 : CTabKA.F 0x5d3c4 W_5d3c4.
Proof. vm_refl. Qed.
Lemma D_5d3c4 : CTabKA.D W_5d3c4 (Load SZ8 true 9 10 0).
Proof. vm_refl. Qed.
Definition W_5d3c8 : bv 32 := 0x08048863.
Lemma F_5d3c8 : CTabKA.F 0x5d3c8 W_5d3c8.
Proof. vm_refl. Qed.
Lemma D_5d3c8 : CTabKA.D W_5d3c8 (Branch BC_EQ 9 0 144).
Proof. vm_refl. Qed.
Definition W_5d3cc : bv 32 := 0x0604c503.
Lemma F_5d3cc : CTabKA.F 0x5d3cc W_5d3cc.
Proof. vm_refl. Qed.
Lemma D_5d3cc : CTabKA.D W_5d3cc (Load SZ1 false 10 9 96).
Proof. vm_refl. Qed.
Definition W_5d3d0 : bv 32 := 0x0584b903.
Lemma F_5d3d0 : CTabKA.F 0x5d3d0 W_5d3d0.
Proof. vm_refl. Qed.
Lemma D_5d3d0 : CTabKA.D W_5d3d0 (Load SZ8 true 18 9 88).
Proof. vm_refl. Qed.
Definition W_5d3d4 : bv 32 := 0x00050863.
Lemma F_5d3d4 : CTabKA.F 0x5d3d4 W_5d3d4.
Proof. vm_refl. Qed.
Lemma D_5d3d4 : CTabKA.D W_5d3d4 (Branch BC_EQ 10 0 16).
Proof. vm_refl. Qed.
Definition W_5d3d8 : bv 32 := 0x00048513.
Lemma F_5d3d8 : CTabKA.F 0x5d3d8 W_5d3d8.
Proof. vm_refl. Qed.
Lemma D_5d3d8 : CTabKA.D W_5d3d8 (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_5d3dc : bv 32 := 0x00040593.
Lemma F_5d3dc : CTabKA.F 0x5d3dc W_5d3dc.
Proof. vm_refl. Qed.
Lemma D_5d3dc : CTabKA.D W_5d3dc (OpImm ALU_ADD 11 8 0).
Proof. vm_refl. Qed.
Definition W_5d3e0 : bv 32 := 0xa01ff0ef.
Lemma F_5d3e0 : CTabKA.F 0x5d3e0 W_5d3e0.
Proof. vm_refl. Qed.
Lemma D_5d3e0 : CTabKA.D W_5d3e0 (Jal 1 2095616).
Proof. vm_refl. Qed.
Definition W_5d3e4 : bv 32 := 0xff990593.
Lemma F_5d3e4 : CTabKA.F 0x5d3e4 W_5d3e4.
Proof. vm_refl. Qed.
Lemma D_5d3e4 : CTabKA.D W_5d3e4 (OpImm ALU_ADD 11 18 4089).
Proof. vm_refl. Qed.
Definition W_5d3e8 : bv 32 := 0x00100513.
Lemma F_5d3e8 : CTabKA.F 0x5d3e8 W_5d3e8.
Proof. vm_refl. Qed.
Lemma D_5d3e8 : CTabKA.D W_5d3e8 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_5d3ec : bv 32 := 0x00b51533.
Lemma F_5d3ec : CTabKA.F 0x5d3ec W_5d3ec.
Proof. vm_refl. Qed.
Lemma D_5d3ec : CTabKA.D W_5d3ec (Op ALU_SLL 10 10 11).
Proof. vm_refl. Qed.
Definition W_5d3f0 : bv 32 := 0x0005061b.
Lemma F_5d3f0 : CTabKA.F 0x5d3f0 W_5d3f0.
Proof. vm_refl. Qed.
Lemma D_5d3f0 : CTabKA.D W_5d3f0 (OpImm32 12 10 0).
Proof. vm_refl. Qed.
Definition W_5d3f4 : bv 32 := 0x08c05263.
Lemma F_5d3f4 : CTabKA.F 0x5d3f4 W_5d3f4.
Proof. vm_refl. Qed.
Lemma D_5d3f4 : CTabKA.D W_5d3f4 (Branch BC_GE 0 12 132).
Proof. vm_refl. Qed.
Definition W_5d3f8 : bv 32 := 0x000016b7.
Lemma F_5d3f8 : CTabKA.F 0x5d3f8 W_5d3f8.
Proof. vm_refl. Qed.
Lemma D_5d3f8 : CTabKA.D W_5d3f8 (Lui 13 1).
Proof. vm_refl. Qed.
Definition W_5d3fc : bv 32 := 0xff190613.
Lemma F_5d3fc : CTabKA.F 0x5d3fc W_5d3fc.
Proof. vm_refl. Qed.
Lemma D_5d3fc : CTabKA.D W_5d3fc (OpImm ALU_ADD 12 18 4081).
Proof. vm_refl. Qed.
Definition W_5d400 : bv 32 := 0x20000713.
Lemma F_5d400 : CTabKA.F 0x5d400 W_5d400.
Proof. vm_refl. Qed.
Lemma D_5d400 : CTabKA.D W_5d400 (OpImm ALU_ADD 14 0 512).
Proof. vm_refl. Qed.
Definition W_5d404 : bv 32 := 0xfff00793.
Lemma F_5d404 : CTabKA.F 0x5d404 W_5d404.
Proof. vm_refl. Qed.
Lemma D_5d404 : CTabKA.D W_5d404 (OpImm ALU_ADD 15 0 4095).
Proof. vm_refl. Qed.
Definition W_5d408 : bv 32 := 0x00c71733.
Lemma F_5d408 : CTabKA.F 0x5d408 W_5d408.
Proof. vm_refl. Qed.
Lemma D_5d408 : CTabKA.D W_5d408 (Op ALU_SLL 14 14 12).
Proof. vm_refl. Qed.
Definition W_5d40c : bv 32 := 0x0084b603.
Lemma F_5d40c : CTabKA.F 0x5d40c W_5d40c.
Proof. vm_refl. Qed.
Lemma D_5d40c : CTabKA.D W_5d40c (Load SZ8 true 12 9 8).
Proof. vm_refl. Qed.
Definition W_5d410 : bv 32 := 0x00b797b3.
Lemma F_5d410 : CTabKA.F 0x5d410 W_5d410.
Proof. vm_refl. Qed.
Lemma D_5d410 : CTabKA.D W_5d410 (Op ALU_SLL 15 15 11).
Proof. vm_refl. Qed.
Definition W_5d414 : bv 32 := 0xfff50813.
Lemma F_5d414 : CTabKA.F 0x5d414 W_5d414.
Proof. vm_refl. Qed.
Lemma D_5d414 : CTabKA.D W_5d414 (OpImm ALU_ADD 16 10 4095).
Proof. vm_refl. Qed.
Definition W_5d418 : bv 32 := 0x00d485b3.
Lemma F_5d418 : CTabKA.F 0x5d418 W_5d418.
Proof. vm_refl. Qed.
Lemma D_5d418 : CTabKA.D W_5d418 (Op ALU_ADD 11 9 13).
Proof. vm_refl. Qed.
Definition W_5d41c : bv 32 := 0x00e586b3.
Lemma F_5d41c : CTabKA.F 0x5d41c W_5d41c.
Proof. vm_refl. Qed.
Lemma D_5d41c : CTabKA.D W_5d41c (Op ALU_ADD 13 11 14).
Proof. vm_refl. Qed.
Definition W_5d420 : bv 32 := 0xfff7c713.
Lemma F_5d420 : CTabKA.F 0x5d420 W_5d420.
Proof. vm_refl. Qed.
Lemma D_5d420 : CTabKA.D W_5d420 (OpImm ALU_XOR 14 15 4095).
Proof. vm_refl. Qed.
Definition W_5d424 : bv 32 := 0x02081813.
Lemma F_5d424 : CTabKA.F 0x5d424 W_5d424.
Proof. vm_refl. Qed.
Lemma D_5d424 : CTabKA.D W_5d424 (ShiftImm ALU_SLL 16 16 32).
Proof. vm_refl. Qed.
Definition W_5d428 : bv 32 := 0x02085793.
Lemma F_5d428 : CTabKA.F 0x5d428 W_5d428.
Proof. vm_refl. Qed.
Lemma D_5d428 : CTabKA.D W_5d428 (ShiftImm ALU_SRL 15 16 32).
Proof. vm_refl. Qed.
Definition W_5d42c : bv 32 := 0x00f607b3.
Lemma F_5d42c : CTabKA.F 0x5d42c W_5d42c.
Proof. vm_refl. Qed.
Lemma D_5d42c : CTabKA.D W_5d42c (Op ALU_ADD 15 12 15).
Proof. vm_refl. Qed.
Definition W_5d430 : bv 32 := 0x00178813.
Lemma F_5d430 : CTabKA.F 0x5d430 W_5d430.
Proof. vm_refl. Qed.
Lemma D_5d430 : CTabKA.D W_5d430 (OpImm ALU_ADD 16 15 1).
Proof. vm_refl. Qed.
Definition W_5d434 : bv 32 := 0x00e678b3.
Lemma F_5d434 : CTabKA.F 0x5d434 W_5d434.
Proof. vm_refl. Qed.
Lemma D_5d434 : CTabKA.D W_5d434 (Op ALU_AND 17 12 14).
Proof. vm_refl. Qed.
Definition W_5d438 : bv 32 := 0x011687b3.
Lemma F_5d438 : CTabKA.F 0x5d438 W_5d438.
Proof. vm_refl. Qed.
Lemma D_5d438 : CTabKA.D W_5d438 (Op ALU_ADD 15 13 17).
Proof. vm_refl. Qed.
Definition W_5d43c : bv 32 := 0x0007c283.
Lemma F_5d43c : CTabKA.F 0x5d43c W_5d43c.
Proof. vm_refl. Qed.
Lemma D_5d43c : CTabKA.D W_5d43c (Load SZ1 false 5 15 0).
Proof. vm_refl. Qed.
Definition W_5d440 : bv 32 := 0x06028663.
Lemma F_5d440 : CTabKA.F 0x5d440 W_5d440.
Proof. vm_refl. Qed.
Lemma D_5d440 : CTabKA.D W_5d440 (Branch BC_EQ 5 0 108).
Proof. vm_refl. Qed.
Definition W_5d444 : bv 32 := 0xfff5051b.
Lemma F_5d444 : CTabKA.F 0x5d444 W_5d444.
Proof. vm_refl. Qed.
Lemma D_5d444 : CTabKA.D W_5d444 (OpImm32 10 10 4095).
Proof. vm_refl. Qed.
Definition W_5d448 : bv 32 := 0x00160613.
Lemma F_5d448 : CTabKA.F 0x5d448 W_5d448.
Proof. vm_refl. Qed.
Lemma D_5d448 : CTabKA.D W_5d448 (OpImm ALU_ADD 12 12 1).
Proof. vm_refl. Qed.
Definition W_5d44c : bv 32 := 0xfe0514e3.
Lemma F_5d44c : CTabKA.F 0x5d44c W_5d44c.
Proof. vm_refl. Qed.
Lemma D_5d44c : CTabKA.D W_5d44c (Branch BC_NE 10 0 8168).
Proof. vm_refl. Qed.
Definition W_5d4ac : bv 32 := 0x00160613.
Lemma F_5d4ac : CTabKA.F 0x5d4ac W_5d4ac.
Proof. vm_refl. Qed.
Lemma D_5d4ac : CTabKA.D W_5d4ac (OpImm ALU_ADD 12 12 1).
Proof. vm_refl. Qed.
Definition W_5d4b0 : bv 32 := 0x00100513.
Lemma F_5d4b0 : CTabKA.F 0x5d4b0 W_5d4b0.
Proof. vm_refl. Qed.
Lemma D_5d4b0 : CTabKA.D W_5d4b0 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_5d4b4 : bv 32 := 0xffb90693.
Lemma F_5d4b4 : CTabKA.F 0x5d4b4 W_5d4b4.
Proof. vm_refl. Qed.
Lemma D_5d4b4 : CTabKA.D W_5d4b4 (OpImm ALU_ADD 13 18 4091).
Proof. vm_refl. Qed.
Definition W_5d4b8 : bv 32 := 0x00789893.
Lemma F_5d4b8 : CTabKA.F 0x5d4b8 W_5d4b8.
Proof. vm_refl. Qed.
Lemma D_5d4b8 : CTabKA.D W_5d4b8 (ShiftImm ALU_SLL 17 17 7).
Proof. vm_refl. Qed.
Definition W_5d4bc : bv 32 := 0x00c4b423.
Lemma F_5d4bc : CTabKA.F 0x5d4bc W_5d4bc.
Proof. vm_refl. Qed.
Lemma D_5d4bc : CTabKA.D W_5d4bc (Store SZ8 9 12 8).
Proof. vm_refl. Qed.
Definition W_5d4c0 : bv 32 := 0x00a78023.
Lemma F_5d4c0 : CTabKA.F 0x5d4c0 W_5d4c0.
Proof. vm_refl. Qed.
Lemma D_5d4c0 : CTabKA.D W_5d4c0 (Store SZ1 15 10 0).
Proof. vm_refl. Qed.
Definition W_5d4c4 : bv 32 := 0x00d51633.
Lemma F_5d4c4 : CTabKA.F 0x5d4c4 W_5d4c4.
Proof. vm_refl. Qed.
Lemma D_5d4c4 : CTabKA.D W_5d4c4 (Op ALU_SLL 12 10 13).
Proof. vm_refl. Qed.
Definition W_5d4c8 : bv 32 := 0x01251533.
Lemma F_5d4c8 : CTabKA.F 0x5d4c8 W_5d4c8.
Proof. vm_refl. Qed.
Lemma D_5d4c8 : CTabKA.D W_5d4c8 (Op ALU_SLL 10 10 18).
Proof. vm_refl. Qed.
Definition W_5d4cc : bv 32 := 0x00c585b3.
Lemma F_5d4cc : CTabKA.F 0x5d4cc W_5d4cc.
Proof. vm_refl. Qed.
Lemma D_5d4cc : CTabKA.D W_5d4cc (Op ALU_ADD 11 11 12).
Proof. vm_refl. Qed.
Definition W_5d4d0 : bv 32 := 0x01150533.
Lemma F_5d4d0 : CTabKA.F 0x5d4d0 W_5d4d0.
Proof. vm_refl. Qed.
Lemma D_5d4d0 : CTabKA.D W_5d4d0 (Op ALU_ADD 10 10 17).
Proof. vm_refl. Qed.
Definition W_5d4d4 : bv 32 := 0x00a584b3.
Lemma F_5d4d4 : CTabKA.F 0x5d4d4 W_5d4d4.
Proof. vm_refl. Qed.
Lemma D_5d4d4 : CTabKA.D W_5d4d4 (Op ALU_ADD 9 11 10).
Proof. vm_refl. Qed.
Definition W_5d4d8 : bv 32 := 0x0084bc23.
Lemma F_5d4d8 : CTabKA.F 0x5d4d8 W_5d4d8.
Proof. vm_refl. Qed.
Lemma D_5d4d8 : CTabKA.D W_5d4d8 (Store SZ8 9 8 24).
Proof. vm_refl. Qed.
Definition W_5d4dc : bv 32 := 0x06f4bc23.
Lemma F_5d4dc : CTabKA.F 0x5d4dc W_5d4dc.
Proof. vm_refl. Qed.
Lemma D_5d4dc : CTabKA.D W_5d4dc (Store SZ8 9 15 120).
Proof. vm_refl. Qed.
Definition W_5d4e0 : bv 32 := 0x00048513.
Lemma F_5d4e0 : CTabKA.F 0x5d4e0 W_5d4e0.
Proof. vm_refl. Qed.
Lemma D_5d4e0 : CTabKA.D W_5d4e0 (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_5d4e4 : bv 32 := 0x560000ef.
Lemma F_5d4e4 : CTabKA.F 0x5d4e4 W_5d4e4.
Proof. vm_refl. Qed.
Lemma D_5d4e4 : CTabKA.D W_5d4e4 (Jal 1 1376).
Proof. vm_refl. Qed.
Definition W_5d4e8 : bv 32 := 0x00050593.
Lemma F_5d4e8 : CTabKA.F 0x5d4e8 W_5d4e8.
Proof. vm_refl. Qed.
Lemma D_5d4e8 : CTabKA.D W_5d4e8 (OpImm ALU_ADD 11 10 0).
Proof. vm_refl. Qed.
Definition W_5d4ec : bv 32 := 0x00048513.
Lemma F_5d4ec : CTabKA.F 0x5d4ec W_5d4ec.
Proof. vm_refl. Qed.
Lemma D_5d4ec : CTabKA.D W_5d4ec (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_5d4f0 : bv 32 := 0x00000613.
Lemma F_5d4f0 : CTabKA.F 0x5d4f0 W_5d4f0.
Proof. vm_refl. Qed.
Lemma D_5d4f0 : CTabKA.D W_5d4f0 (OpImm ALU_ADD 12 0 0).
Proof. vm_refl. Qed.
Definition W_5d4f4 : bv 32 := 0x0005b023.
Lemma F_5d4f4 : CTabKA.F 0x5d4f4 W_5d4f4.
Proof. vm_refl. Qed.
Lemma D_5d4f4 : CTabKA.D W_5d4f4 (Store SZ8 11 0 0).
Proof. vm_refl. Qed.
Definition W_5d4f8 : bv 32 := 0x0005b423.
Lemma F_5d4f8 : CTabKA.F 0x5d4f8 W_5d4f8.
Proof. vm_refl. Qed.
Lemma D_5d4f8 : CTabKA.D W_5d4f8 (Store SZ8 11 0 8).
Proof. vm_refl. Qed.
Definition W_5d4fc : bv 32 := 0x01813083.
Lemma F_5d4fc : CTabKA.F 0x5d4fc W_5d4fc.
Proof. vm_refl. Qed.
Lemma D_5d4fc : CTabKA.D W_5d4fc (Load SZ8 true 1 2 24).
Proof. vm_refl. Qed.
Definition W_5d500 : bv 32 := 0x01013403.
Lemma F_5d500 : CTabKA.F 0x5d500 W_5d500.
Proof. vm_refl. Qed.
Lemma D_5d500 : CTabKA.D W_5d500 (Load SZ8 true 8 2 16).
Proof. vm_refl. Qed.
Definition W_5d504 : bv 32 := 0x00813483.
Lemma F_5d504 : CTabKA.F 0x5d504 W_5d504.
Proof. vm_refl. Qed.
Lemma D_5d504 : CTabKA.D W_5d504 (Load SZ8 true 9 2 8).
Proof. vm_refl. Qed.
Definition W_5d508 : bv 32 := 0x00013903.
Lemma F_5d508 : CTabKA.F 0x5d508 W_5d508.
Proof. vm_refl. Qed.
Lemma D_5d508 : CTabKA.D W_5d508 (Load SZ8 true 18 2 0).
Proof. vm_refl. Qed.
Definition W_5d50c : bv 32 := 0x02010113.
Lemma F_5d50c : CTabKA.F 0x5d50c W_5d50c.
Proof. vm_refl. Qed.
Lemma D_5d50c : CTabKA.D W_5d50c (OpImm ALU_ADD 2 2 32).
Proof. vm_refl. Qed.
Definition W_5d510 : bv 32 := 0x00008067.
Lemma F_5d510 : CTabKA.F 0x5d510 W_5d510.
Proof. vm_refl. Qed.
Lemma D_5d510 : CTabKA.D W_5d510 (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_5d530 : bv 32 := 0xfe010113.
Lemma F_5d530 : CTabKA.F 0x5d530 W_5d530.
Proof. vm_refl. Qed.
Lemma D_5d530 : CTabKA.D W_5d530 (OpImm ALU_ADD 2 2 4064).
Proof. vm_refl. Qed.
Definition W_5d534 : bv 32 := 0x00113c23.
Lemma F_5d534 : CTabKA.F 0x5d534 W_5d534.
Proof. vm_refl. Qed.
Lemma D_5d534 : CTabKA.D W_5d534 (Store SZ8 2 1 24).
Proof. vm_refl. Qed.
Definition W_5d538 : bv 32 := 0x00813823.
Lemma F_5d538 : CTabKA.F 0x5d538 W_5d538.
Proof. vm_refl. Qed.
Lemma D_5d538 : CTabKA.D W_5d538 (Store SZ8 2 8 16).
Proof. vm_refl. Qed.
Definition W_5d53c : bv 32 := 0x00913423.
Lemma F_5d53c : CTabKA.F 0x5d53c W_5d53c.
Proof. vm_refl. Qed.
Lemma D_5d53c : CTabKA.D W_5d53c (Store SZ8 2 9 8).
Proof. vm_refl. Qed.
Definition W_5d540 : bv 32 := 0x01213023.
Lemma F_5d540 : CTabKA.F 0x5d540 W_5d540.
Proof. vm_refl. Qed.
Lemma D_5d540 : CTabKA.D W_5d540 (Store SZ8 2 18 0).
Proof. vm_refl. Qed.
Definition W_5d544 : bv 32 := 0x02010413.
Lemma F_5d544 : CTabKA.F 0x5d544 W_5d544.
Proof. vm_refl. Qed.
Lemma D_5d544 : CTabKA.D W_5d544 (OpImm ALU_ADD 8 2 32).
Proof. vm_refl. Qed.
Definition W_5d548 : bv 32 := 0x000d6517.
Lemma F_5d548 : CTabKA.F 0x5d548 W_5d548.
Proof. vm_refl. Qed.
Lemma D_5d548 : CTabKA.D W_5d548 (Auipc 10 214).
Proof. vm_refl. Qed.
Definition W_5d54c : bv 32 := 0xee850513.
Lemma F_5d54c : CTabKA.F 0x5d54c W_5d54c.
Proof. vm_refl. Qed.
Lemma D_5d54c : CTabKA.D W_5d54c (OpImm ALU_ADD 10 10 3816).
Proof. vm_refl. Qed.
Definition W_5d550 : bv 32 := 0x548050ef.
Lemma F_5d550 : CTabKA.F 0x5d550 W_5d550.
Proof. vm_refl. Qed.
Lemma D_5d550 : CTabKA.D W_5d550 (Jal 1 21832).
Proof. vm_refl. Qed.
Definition W_5d554 : bv 32 := 0x00053483.
Lemma F_5d554 : CTabKA.F 0x5d554 W_5d554.
Proof. vm_refl. Qed.
Lemma D_5d554 : CTabKA.D W_5d554 (Load SZ8 true 9 10 0).
Proof. vm_refl. Qed.
Definition W_5d558 : bv 32 := 0x08048863.
Lemma F_5d558 : CTabKA.F 0x5d558 W_5d558.
Proof. vm_refl. Qed.
Lemma D_5d558 : CTabKA.D W_5d558 (Branch BC_EQ 9 0 144).
Proof. vm_refl. Qed.
Definition W_5d55c : bv 32 := 0x0604c503.
Lemma F_5d55c : CTabKA.F 0x5d55c W_5d55c.
Proof. vm_refl. Qed.
Lemma D_5d55c : CTabKA.D W_5d55c (Load SZ1 false 10 9 96).
Proof. vm_refl. Qed.
Definition W_5d560 : bv 32 := 0x0584b903.
Lemma F_5d560 : CTabKA.F 0x5d560 W_5d560.
Proof. vm_refl. Qed.
Lemma D_5d560 : CTabKA.D W_5d560 (Load SZ8 true 18 9 88).
Proof. vm_refl. Qed.
Definition W_5d564 : bv 32 := 0x00050863.
Lemma F_5d564 : CTabKA.F 0x5d564 W_5d564.
Proof. vm_refl. Qed.
Lemma D_5d564 : CTabKA.D W_5d564 (Branch BC_EQ 10 0 16).
Proof. vm_refl. Qed.
Definition W_5d568 : bv 32 := 0x00048513.
Lemma F_5d568 : CTabKA.F 0x5d568 W_5d568.
Proof. vm_refl. Qed.
Lemma D_5d568 : CTabKA.D W_5d568 (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_5d56c : bv 32 := 0x00040593.
Lemma F_5d56c : CTabKA.F 0x5d56c W_5d56c.
Proof. vm_refl. Qed.
Lemma D_5d56c : CTabKA.D W_5d56c (OpImm ALU_ADD 11 8 0).
Proof. vm_refl. Qed.
Definition W_5d570 : bv 32 := 0x871ff0ef.
Lemma F_5d570 : CTabKA.F 0x5d570 W_5d570.
Proof. vm_refl. Qed.
Lemma D_5d570 : CTabKA.D W_5d570 (Jal 1 2095216).
Proof. vm_refl. Qed.
Definition W_5d574 : bv 32 := 0xff890593.
Lemma F_5d574 : CTabKA.F 0x5d574 W_5d574.
Proof. vm_refl. Qed.
Lemma D_5d574 : CTabKA.D W_5d574 (OpImm ALU_ADD 11 18 4088).
Proof. vm_refl. Qed.
Definition W_5d578 : bv 32 := 0x00100513.
Lemma F_5d578 : CTabKA.F 0x5d578 W_5d578.
Proof. vm_refl. Qed.
Lemma D_5d578 : CTabKA.D W_5d578 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_5d57c : bv 32 := 0x00b51533.
Lemma F_5d57c : CTabKA.F 0x5d57c W_5d57c.
Proof. vm_refl. Qed.
Lemma D_5d57c : CTabKA.D W_5d57c (Op ALU_SLL 10 10 11).
Proof. vm_refl. Qed.
Definition W_5d580 : bv 32 := 0x0005061b.
Lemma F_5d580 : CTabKA.F 0x5d580 W_5d580.
Proof. vm_refl. Qed.
Lemma D_5d580 : CTabKA.D W_5d580 (OpImm32 12 10 0).
Proof. vm_refl. Qed.
Definition W_5d584 : bv 32 := 0x08c05263.
Lemma F_5d584 : CTabKA.F 0x5d584 W_5d584.
Proof. vm_refl. Qed.
Lemma D_5d584 : CTabKA.D W_5d584 (Branch BC_GE 0 12 132).
Proof. vm_refl. Qed.
Definition W_5d588 : bv 32 := 0x000016b7.
Lemma F_5d588 : CTabKA.F 0x5d588 W_5d588.
Proof. vm_refl. Qed.
Lemma D_5d588 : CTabKA.D W_5d588 (Lui 13 1).
Proof. vm_refl. Qed.
Definition W_5d58c : bv 32 := 0xff190613.
Lemma F_5d58c : CTabKA.F 0x5d58c W_5d58c.
Proof. vm_refl. Qed.
Lemma D_5d58c : CTabKA.D W_5d58c (OpImm ALU_ADD 12 18 4081).
Proof. vm_refl. Qed.
Definition W_5d590 : bv 32 := 0x30000713.
Lemma F_5d590 : CTabKA.F 0x5d590 W_5d590.
Proof. vm_refl. Qed.
Lemma D_5d590 : CTabKA.D W_5d590 (OpImm ALU_ADD 14 0 768).
Proof. vm_refl. Qed.
Definition W_5d594 : bv 32 := 0xfff00793.
Lemma F_5d594 : CTabKA.F 0x5d594 W_5d594.
Proof. vm_refl. Qed.
Lemma D_5d594 : CTabKA.D W_5d594 (OpImm ALU_ADD 15 0 4095).
Proof. vm_refl. Qed.
Definition W_5d598 : bv 32 := 0x00c71733.
Lemma F_5d598 : CTabKA.F 0x5d598 W_5d598.
Proof. vm_refl. Qed.
Lemma D_5d598 : CTabKA.D W_5d598 (Op ALU_SLL 14 14 12).
Proof. vm_refl. Qed.
Definition W_5d59c : bv 32 := 0x0104b603.
Lemma F_5d59c : CTabKA.F 0x5d59c W_5d59c.
Proof. vm_refl. Qed.
Lemma D_5d59c : CTabKA.D W_5d59c (Load SZ8 true 12 9 16).
Proof. vm_refl. Qed.
Definition W_5d5a0 : bv 32 := 0x00b797b3.
Lemma F_5d5a0 : CTabKA.F 0x5d5a0 W_5d5a0.
Proof. vm_refl. Qed.
Lemma D_5d5a0 : CTabKA.D W_5d5a0 (Op ALU_SLL 15 15 11).
Proof. vm_refl. Qed.
Definition W_5d5a4 : bv 32 := 0xfff50813.
Lemma F_5d5a4 : CTabKA.F 0x5d5a4 W_5d5a4.
Proof. vm_refl. Qed.
Lemma D_5d5a4 : CTabKA.D W_5d5a4 (OpImm ALU_ADD 16 10 4095).
Proof. vm_refl. Qed.
Definition W_5d5a8 : bv 32 := 0x00d485b3.
Lemma F_5d5a8 : CTabKA.F 0x5d5a8 W_5d5a8.
Proof. vm_refl. Qed.
Lemma D_5d5a8 : CTabKA.D W_5d5a8 (Op ALU_ADD 11 9 13).
Proof. vm_refl. Qed.
Definition W_5d5ac : bv 32 := 0x00e586b3.
Lemma F_5d5ac : CTabKA.F 0x5d5ac W_5d5ac.
Proof. vm_refl. Qed.
Lemma D_5d5ac : CTabKA.D W_5d5ac (Op ALU_ADD 13 11 14).
Proof. vm_refl. Qed.
Definition W_5d5b0 : bv 32 := 0xfff7c713.
Lemma F_5d5b0 : CTabKA.F 0x5d5b0 W_5d5b0.
Proof. vm_refl. Qed.
Lemma D_5d5b0 : CTabKA.D W_5d5b0 (OpImm ALU_XOR 14 15 4095).
Proof. vm_refl. Qed.
Definition W_5d5b4 : bv 32 := 0x02081813.
Lemma F_5d5b4 : CTabKA.F 0x5d5b4 W_5d5b4.
Proof. vm_refl. Qed.
Lemma D_5d5b4 : CTabKA.D W_5d5b4 (ShiftImm ALU_SLL 16 16 32).
Proof. vm_refl. Qed.
Definition W_5d5b8 : bv 32 := 0x02085793.
Lemma F_5d5b8 : CTabKA.F 0x5d5b8 W_5d5b8.
Proof. vm_refl. Qed.
Lemma D_5d5b8 : CTabKA.D W_5d5b8 (ShiftImm ALU_SRL 15 16 32).
Proof. vm_refl. Qed.
Definition W_5d5bc : bv 32 := 0x00f607b3.
Lemma F_5d5bc : CTabKA.F 0x5d5bc W_5d5bc.
Proof. vm_refl. Qed.
Lemma D_5d5bc : CTabKA.D W_5d5bc (Op ALU_ADD 15 12 15).
Proof. vm_refl. Qed.
Definition W_5d5c0 : bv 32 := 0x00178813.
Lemma F_5d5c0 : CTabKA.F 0x5d5c0 W_5d5c0.
Proof. vm_refl. Qed.
Lemma D_5d5c0 : CTabKA.D W_5d5c0 (OpImm ALU_ADD 16 15 1).
Proof. vm_refl. Qed.
Definition W_5d5c4 : bv 32 := 0x00e678b3.
Lemma F_5d5c4 : CTabKA.F 0x5d5c4 W_5d5c4.
Proof. vm_refl. Qed.
Lemma D_5d5c4 : CTabKA.D W_5d5c4 (Op ALU_AND 17 12 14).
Proof. vm_refl. Qed.
Definition W_5d5c8 : bv 32 := 0x011687b3.
Lemma F_5d5c8 : CTabKA.F 0x5d5c8 W_5d5c8.
Proof. vm_refl. Qed.
Lemma D_5d5c8 : CTabKA.D W_5d5c8 (Op ALU_ADD 15 13 17).
Proof. vm_refl. Qed.
Definition W_5d5cc : bv 32 := 0x0007c283.
Lemma F_5d5cc : CTabKA.F 0x5d5cc W_5d5cc.
Proof. vm_refl. Qed.
Lemma D_5d5cc : CTabKA.D W_5d5cc (Load SZ1 false 5 15 0).
Proof. vm_refl. Qed.
Definition W_5d5d0 : bv 32 := 0x06028663.
Lemma F_5d5d0 : CTabKA.F 0x5d5d0 W_5d5d0.
Proof. vm_refl. Qed.
Lemma D_5d5d0 : CTabKA.D W_5d5d0 (Branch BC_EQ 5 0 108).
Proof. vm_refl. Qed.
Definition W_5d5d4 : bv 32 := 0xfff5051b.
Lemma F_5d5d4 : CTabKA.F 0x5d5d4 W_5d5d4.
Proof. vm_refl. Qed.
Lemma D_5d5d4 : CTabKA.D W_5d5d4 (OpImm32 10 10 4095).
Proof. vm_refl. Qed.
Definition W_5d5d8 : bv 32 := 0x00160613.
Lemma F_5d5d8 : CTabKA.F 0x5d5d8 W_5d5d8.
Proof. vm_refl. Qed.
Lemma D_5d5d8 : CTabKA.D W_5d5d8 (OpImm ALU_ADD 12 12 1).
Proof. vm_refl. Qed.
Definition W_5d5dc : bv 32 := 0xfe0514e3.
Lemma F_5d5dc : CTabKA.F 0x5d5dc W_5d5dc.
Proof. vm_refl. Qed.
Lemma D_5d5dc : CTabKA.D W_5d5dc (Branch BC_NE 10 0 8168).
Proof. vm_refl. Qed.
Definition W_5d63c : bv 32 := 0x00160613.
Lemma F_5d63c : CTabKA.F 0x5d63c W_5d63c.
Proof. vm_refl. Qed.
Lemma D_5d63c : CTabKA.D W_5d63c (OpImm ALU_ADD 12 12 1).
Proof. vm_refl. Qed.
Definition W_5d640 : bv 32 := 0x00100513.
Lemma F_5d640 : CTabKA.F 0x5d640 W_5d640.
Proof. vm_refl. Qed.
Lemma D_5d640 : CTabKA.D W_5d640 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_5d644 : bv 32 := 0xffb90693.
Lemma F_5d644 : CTabKA.F 0x5d644 W_5d644.
Proof. vm_refl. Qed.
Lemma D_5d644 : CTabKA.D W_5d644 (OpImm ALU_ADD 13 18 4091).
Proof. vm_refl. Qed.
Definition W_5d648 : bv 32 := 0x00c4b823.
Lemma F_5d648 : CTabKA.F 0x5d648 W_5d648.
Proof. vm_refl. Qed.
Lemma D_5d648 : CTabKA.D W_5d648 (Store SZ8 9 12 16).
Proof. vm_refl. Qed.
Definition W_5d64c : bv 32 := 0x00a78023.
Lemma F_5d64c : CTabKA.F 0x5d64c W_5d64c.
Proof. vm_refl. Qed.
Lemma D_5d64c : CTabKA.D W_5d64c (Store SZ1 15 10 0).
Proof. vm_refl. Qed.
Definition W_5d650 : bv 32 := 0x00d51533.
Lemma F_5d650 : CTabKA.F 0x5d650 W_5d650.
Proof. vm_refl. Qed.
Lemma D_5d650 : CTabKA.D W_5d650 (Op ALU_SLL 10 10 13).
Proof. vm_refl. Qed.
Definition W_5d654 : bv 32 := 0x00200613.
Lemma F_5d654 : CTabKA.F 0x5d654 W_5d654.
Proof. vm_refl. Qed.
Lemma D_5d654 : CTabKA.D W_5d654 (OpImm ALU_ADD 12 0 2).
Proof. vm_refl. Qed.
Definition W_5d658 : bv 32 := 0x00889893.
Lemma F_5d658 : CTabKA.F 0x5d658 W_5d658.
Proof. vm_refl. Qed.
Lemma D_5d658 : CTabKA.D W_5d658 (ShiftImm ALU_SLL 17 17 8).
Proof. vm_refl. Qed.
Definition W_5d65c : bv 32 := 0x01261633.
Lemma F_5d65c : CTabKA.F 0x5d65c W_5d65c.
Proof. vm_refl. Qed.
Lemma D_5d65c : CTabKA.D W_5d65c (Op ALU_SLL 12 12 18).
Proof. vm_refl. Qed.
Definition W_5d660 : bv 32 := 0x00a58533.
Lemma F_5d660 : CTabKA.F 0x5d660 W_5d660.
Proof. vm_refl. Qed.
Lemma D_5d660 : CTabKA.D W_5d660 (Op ALU_ADD 10 11 10).
Proof. vm_refl. Qed.
Definition W_5d664 : bv 32 := 0x01160633.
Lemma F_5d664 : CTabKA.F 0x5d664 W_5d664.
Proof. vm_refl. Qed.
Lemma D_5d664 : CTabKA.D W_5d664 (Op ALU_ADD 12 12 17).
Proof. vm_refl. Qed.
Definition W_5d668 : bv 32 := 0x00c504b3.
Lemma F_5d668 : CTabKA.F 0x5d668 W_5d668.
Proof. vm_refl. Qed.
Lemma D_5d668 : CTabKA.D W_5d668 (Op ALU_ADD 9 10 12).
Proof. vm_refl. Qed.
Definition W_5d66c : bv 32 := 0x0084bc23.
Lemma F_5d66c : CTabKA.F 0x5d66c W_5d66c.
Proof. vm_refl. Qed.
Lemma D_5d66c : CTabKA.D W_5d66c (Store SZ8 9 8 24).
Proof. vm_refl. Qed.
Definition W_5d670 : bv 32 := 0x0ef4bc23.
Lemma F_5d670 : CTabKA.F 0x5d670 W_5d670.
Proof. vm_refl. Qed.
Lemma D_5d670 : CTabKA.D W_5d670 (Store SZ8 9 15 248).
Proof. vm_refl. Qed.
Definition W_5d674 : bv 32 := 0x00048513.
Lemma F_5d674 : CTabKA.F 0x5d674 W_5d674.
Proof. vm_refl. Qed.
Lemma D_5d674 : CTabKA.D W_5d674 (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_5d678 : bv 32 := 0x3cc000ef.
Lemma F_5d678 : CTabKA.F 0x5d678 W_5d678.
Proof. vm_refl. Qed.
Lemma D_5d678 : CTabKA.D W_5d678 (Jal 1 972).
Proof. vm_refl. Qed.
Definition W_5d67c : bv 32 := 0x00050593.
Lemma F_5d67c : CTabKA.F 0x5d67c W_5d67c.
Proof. vm_refl. Qed.
Lemma D_5d67c : CTabKA.D W_5d67c (OpImm ALU_ADD 11 10 0).
Proof. vm_refl. Qed.
Definition W_5d680 : bv 32 := 0x00048513.
Lemma F_5d680 : CTabKA.F 0x5d680 W_5d680.
Proof. vm_refl. Qed.
Lemma D_5d680 : CTabKA.D W_5d680 (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_5d684 : bv 32 := 0x00000613.
Lemma F_5d684 : CTabKA.F 0x5d684 W_5d684.
Proof. vm_refl. Qed.
Lemma D_5d684 : CTabKA.D W_5d684 (OpImm ALU_ADD 12 0 0).
Proof. vm_refl. Qed.
Definition W_5d688 : bv 32 := 0x0005b023.
Lemma F_5d688 : CTabKA.F 0x5d688 W_5d688.
Proof. vm_refl. Qed.
Lemma D_5d688 : CTabKA.D W_5d688 (Store SZ8 11 0 0).
Proof. vm_refl. Qed.
Definition W_5d68c : bv 32 := 0x0005b423.
Lemma F_5d68c : CTabKA.F 0x5d68c W_5d68c.
Proof. vm_refl. Qed.
Lemma D_5d68c : CTabKA.D W_5d68c (Store SZ8 11 0 8).
Proof. vm_refl. Qed.
Definition W_5d690 : bv 32 := 0x0005b823.
Lemma F_5d690 : CTabKA.F 0x5d690 W_5d690.
Proof. vm_refl. Qed.
Lemma D_5d690 : CTabKA.D W_5d690 (Store SZ8 11 0 16).
Proof. vm_refl. Qed.
Definition W_5d694 : bv 32 := 0x0005bc23.
Lemma F_5d694 : CTabKA.F 0x5d694 W_5d694.
Proof. vm_refl. Qed.
Lemma D_5d694 : CTabKA.D W_5d694 (Store SZ8 11 0 24).
Proof. vm_refl. Qed.
Definition W_5d698 : bv 32 := 0x01813083.
Lemma F_5d698 : CTabKA.F 0x5d698 W_5d698.
Proof. vm_refl. Qed.
Lemma D_5d698 : CTabKA.D W_5d698 (Load SZ8 true 1 2 24).
Proof. vm_refl. Qed.
Definition W_5d69c : bv 32 := 0x01013403.
Lemma F_5d69c : CTabKA.F 0x5d69c W_5d69c.
Proof. vm_refl. Qed.
Lemma D_5d69c : CTabKA.D W_5d69c (Load SZ8 true 8 2 16).
Proof. vm_refl. Qed.
Definition W_5d6a0 : bv 32 := 0x00813483.
Lemma F_5d6a0 : CTabKA.F 0x5d6a0 W_5d6a0.
Proof. vm_refl. Qed.
Lemma D_5d6a0 : CTabKA.D W_5d6a0 (Load SZ8 true 9 2 8).
Proof. vm_refl. Qed.
Definition W_5d6a4 : bv 32 := 0x00013903.
Lemma F_5d6a4 : CTabKA.F 0x5d6a4 W_5d6a4.
Proof. vm_refl. Qed.
Lemma D_5d6a4 : CTabKA.D W_5d6a4 (Load SZ8 true 18 2 0).
Proof. vm_refl. Qed.
Definition W_5d6a8 : bv 32 := 0x02010113.
Lemma F_5d6a8 : CTabKA.F 0x5d6a8 W_5d6a8.
Proof. vm_refl. Qed.
Lemma D_5d6a8 : CTabKA.D W_5d6a8 (OpImm ALU_ADD 2 2 32).
Proof. vm_refl. Qed.
Definition W_5d6ac : bv 32 := 0x00008067.
Lemma F_5d6ac : CTabKA.F 0x5d6ac W_5d6ac.
Proof. vm_refl. Qed.
Lemma D_5d6ac : CTabKA.D W_5d6ac (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_5d6cc : bv 32 := 0xfe010113.
Lemma F_5d6cc : CTabKA.F 0x5d6cc W_5d6cc.
Proof. vm_refl. Qed.
Lemma D_5d6cc : CTabKA.D W_5d6cc (OpImm ALU_ADD 2 2 4064).
Proof. vm_refl. Qed.
Definition W_5d6d0 : bv 32 := 0x00113c23.
Lemma F_5d6d0 : CTabKA.F 0x5d6d0 W_5d6d0.
Proof. vm_refl. Qed.
Lemma D_5d6d0 : CTabKA.D W_5d6d0 (Store SZ8 2 1 24).
Proof. vm_refl. Qed.
Definition W_5d6d4 : bv 32 := 0x00813823.
Lemma F_5d6d4 : CTabKA.F 0x5d6d4 W_5d6d4.
Proof. vm_refl. Qed.
Lemma D_5d6d4 : CTabKA.D W_5d6d4 (Store SZ8 2 8 16).
Proof. vm_refl. Qed.
Definition W_5d6d8 : bv 32 := 0x00913423.
Lemma F_5d6d8 : CTabKA.F 0x5d6d8 W_5d6d8.
Proof. vm_refl. Qed.
Lemma D_5d6d8 : CTabKA.D W_5d6d8 (Store SZ8 2 9 8).
Proof. vm_refl. Qed.
Definition W_5d6dc : bv 32 := 0x01213023.
Lemma F_5d6dc : CTabKA.F 0x5d6dc W_5d6dc.
Proof. vm_refl. Qed.
Lemma D_5d6dc : CTabKA.D W_5d6dc (Store SZ8 2 18 0).
Proof. vm_refl. Qed.
Definition W_5d6e0 : bv 32 := 0x02010413.
Lemma F_5d6e0 : CTabKA.F 0x5d6e0 W_5d6e0.
Proof. vm_refl. Qed.
Lemma D_5d6e0 : CTabKA.D W_5d6e0 (OpImm ALU_ADD 8 2 32).
Proof. vm_refl. Qed.
Definition W_5d6e4 : bv 32 := 0x000d6517.
Lemma F_5d6e4 : CTabKA.F 0x5d6e4 W_5d6e4.
Proof. vm_refl. Qed.
Lemma D_5d6e4 : CTabKA.D W_5d6e4 (Auipc 10 214).
Proof. vm_refl. Qed.
Definition W_5d6e8 : bv 32 := 0xd4c50513.
Lemma F_5d6e8 : CTabKA.F 0x5d6e8 W_5d6e8.
Proof. vm_refl. Qed.
Lemma D_5d6e8 : CTabKA.D W_5d6e8 (OpImm ALU_ADD 10 10 3404).
Proof. vm_refl. Qed.
Definition W_5d6ec : bv 32 := 0x3ac050ef.
Lemma F_5d6ec : CTabKA.F 0x5d6ec W_5d6ec.
Proof. vm_refl. Qed.
Lemma D_5d6ec : CTabKA.D W_5d6ec (Jal 1 21420).
Proof. vm_refl. Qed.
Definition W_5d6f0 : bv 32 := 0x00053483.
Lemma F_5d6f0 : CTabKA.F 0x5d6f0 W_5d6f0.
Proof. vm_refl. Qed.
Lemma D_5d6f0 : CTabKA.D W_5d6f0 (Load SZ8 true 9 10 0).
Proof. vm_refl. Qed.
Definition W_5d6f4 : bv 32 := 0x08048863.
Lemma F_5d6f4 : CTabKA.F 0x5d6f4 W_5d6f4.
Proof. vm_refl. Qed.
Lemma D_5d6f4 : CTabKA.D W_5d6f4 (Branch BC_EQ 9 0 144).
Proof. vm_refl. Qed.
Definition W_5d6f8 : bv 32 := 0x0604c503.
Lemma F_5d6f8 : CTabKA.F 0x5d6f8 W_5d6f8.
Proof. vm_refl. Qed.
Lemma D_5d6f8 : CTabKA.D W_5d6f8 (Load SZ1 false 10 9 96).
Proof. vm_refl. Qed.
Definition W_5d6fc : bv 32 := 0x0584b903.
Lemma F_5d6fc : CTabKA.F 0x5d6fc W_5d6fc.
Proof. vm_refl. Qed.
Lemma D_5d6fc : CTabKA.D W_5d6fc (Load SZ8 true 18 9 88).
Proof. vm_refl. Qed.
Definition W_5d700 : bv 32 := 0x00050863.
Lemma F_5d700 : CTabKA.F 0x5d700 W_5d700.
Proof. vm_refl. Qed.
Lemma D_5d700 : CTabKA.D W_5d700 (Branch BC_EQ 10 0 16).
Proof. vm_refl. Qed.
Definition W_5d704 : bv 32 := 0x00048513.
Lemma F_5d704 : CTabKA.F 0x5d704 W_5d704.
Proof. vm_refl. Qed.
Lemma D_5d704 : CTabKA.D W_5d704 (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_5d708 : bv 32 := 0x00040593.
Lemma F_5d708 : CTabKA.F 0x5d708 W_5d708.
Proof. vm_refl. Qed.
Lemma D_5d708 : CTabKA.D W_5d708 (OpImm ALU_ADD 11 8 0).
Proof. vm_refl. Qed.
Definition W_5d70c : bv 32 := 0xed4ff0ef.
Lemma F_5d70c : CTabKA.F 0x5d70c W_5d70c.
Proof. vm_refl. Qed.
Lemma D_5d70c : CTabKA.D W_5d70c (Jal 1 2094804).
Proof. vm_refl. Qed.
Definition W_5d710 : bv 32 := 0xff790593.
Lemma F_5d710 : CTabKA.F 0x5d710 W_5d710.
Proof. vm_refl. Qed.
Lemma D_5d710 : CTabKA.D W_5d710 (OpImm ALU_ADD 11 18 4087).
Proof. vm_refl. Qed.
Definition W_5d714 : bv 32 := 0x00100513.
Lemma F_5d714 : CTabKA.F 0x5d714 W_5d714.
Proof. vm_refl. Qed.
Lemma D_5d714 : CTabKA.D W_5d714 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_5d718 : bv 32 := 0x00b51533.
Lemma F_5d718 : CTabKA.F 0x5d718 W_5d718.
Proof. vm_refl. Qed.
Lemma D_5d718 : CTabKA.D W_5d718 (Op ALU_SLL 10 10 11).
Proof. vm_refl. Qed.
Definition W_5d71c : bv 32 := 0x0005061b.
Lemma F_5d71c : CTabKA.F 0x5d71c W_5d71c.
Proof. vm_refl. Qed.
Lemma D_5d71c : CTabKA.D W_5d71c (OpImm32 12 10 0).
Proof. vm_refl. Qed.
Definition W_5d720 : bv 32 := 0x08c05263.
Lemma F_5d720 : CTabKA.F 0x5d720 W_5d720.
Proof. vm_refl. Qed.
Lemma D_5d720 : CTabKA.D W_5d720 (Branch BC_GE 0 12 132).
Proof. vm_refl. Qed.
Definition W_5d724 : bv 32 := 0x000016b7.
Lemma F_5d724 : CTabKA.F 0x5d724 W_5d724.
Proof. vm_refl. Qed.
Lemma D_5d724 : CTabKA.D W_5d724 (Lui 13 1).
Proof. vm_refl. Qed.
Definition W_5d728 : bv 32 := 0xff190613.
Lemma F_5d728 : CTabKA.F 0x5d728 W_5d728.
Proof. vm_refl. Qed.
Lemma D_5d728 : CTabKA.D W_5d728 (OpImm ALU_ADD 12 18 4081).
Proof. vm_refl. Qed.
Definition W_5d72c : bv 32 := 0x38000713.
Lemma F_5d72c : CTabKA.F 0x5d72c W_5d72c.
Proof. vm_refl. Qed.
Lemma D_5d72c : CTabKA.D W_5d72c (OpImm ALU_ADD 14 0 896).
Proof. vm_refl. Qed.
Definition W_5d730 : bv 32 := 0xfff00793.
Lemma F_5d730 : CTabKA.F 0x5d730 W_5d730.
Proof. vm_refl. Qed.
Lemma D_5d730 : CTabKA.D W_5d730 (OpImm ALU_ADD 15 0 4095).
Proof. vm_refl. Qed.
Definition W_5d734 : bv 32 := 0x00c71733.
Lemma F_5d734 : CTabKA.F 0x5d734 W_5d734.
Proof. vm_refl. Qed.
Lemma D_5d734 : CTabKA.D W_5d734 (Op ALU_SLL 14 14 12).
Proof. vm_refl. Qed.
Definition W_5d738 : bv 32 := 0x0184b603.
Lemma F_5d738 : CTabKA.F 0x5d738 W_5d738.
Proof. vm_refl. Qed.
Lemma D_5d738 : CTabKA.D W_5d738 (Load SZ8 true 12 9 24).
Proof. vm_refl. Qed.
Definition W_5d73c : bv 32 := 0x00b797b3.
Lemma F_5d73c : CTabKA.F 0x5d73c W_5d73c.
Proof. vm_refl. Qed.
Lemma D_5d73c : CTabKA.D W_5d73c (Op ALU_SLL 15 15 11).
Proof. vm_refl. Qed.
Definition W_5d740 : bv 32 := 0xfff50813.
Lemma F_5d740 : CTabKA.F 0x5d740 W_5d740.
Proof. vm_refl. Qed.
Lemma D_5d740 : CTabKA.D W_5d740 (OpImm ALU_ADD 16 10 4095).
Proof. vm_refl. Qed.
Definition W_5d744 : bv 32 := 0x00d485b3.
Lemma F_5d744 : CTabKA.F 0x5d744 W_5d744.
Proof. vm_refl. Qed.
Lemma D_5d744 : CTabKA.D W_5d744 (Op ALU_ADD 11 9 13).
Proof. vm_refl. Qed.
Definition W_5d748 : bv 32 := 0x00e586b3.
Lemma F_5d748 : CTabKA.F 0x5d748 W_5d748.
Proof. vm_refl. Qed.
Lemma D_5d748 : CTabKA.D W_5d748 (Op ALU_ADD 13 11 14).
Proof. vm_refl. Qed.
Definition W_5d74c : bv 32 := 0xfff7c713.
Lemma F_5d74c : CTabKA.F 0x5d74c W_5d74c.
Proof. vm_refl. Qed.
Lemma D_5d74c : CTabKA.D W_5d74c (OpImm ALU_XOR 14 15 4095).
Proof. vm_refl. Qed.
Definition W_5d750 : bv 32 := 0x02081813.
Lemma F_5d750 : CTabKA.F 0x5d750 W_5d750.
Proof. vm_refl. Qed.
Lemma D_5d750 : CTabKA.D W_5d750 (ShiftImm ALU_SLL 16 16 32).
Proof. vm_refl. Qed.
Definition W_5d754 : bv 32 := 0x02085793.
Lemma F_5d754 : CTabKA.F 0x5d754 W_5d754.
Proof. vm_refl. Qed.
Lemma D_5d754 : CTabKA.D W_5d754 (ShiftImm ALU_SRL 15 16 32).
Proof. vm_refl. Qed.
Definition W_5d758 : bv 32 := 0x00f607b3.
Lemma F_5d758 : CTabKA.F 0x5d758 W_5d758.
Proof. vm_refl. Qed.
Lemma D_5d758 : CTabKA.D W_5d758 (Op ALU_ADD 15 12 15).
Proof. vm_refl. Qed.
Definition W_5d75c : bv 32 := 0x00178813.
Lemma F_5d75c : CTabKA.F 0x5d75c W_5d75c.
Proof. vm_refl. Qed.
Lemma D_5d75c : CTabKA.D W_5d75c (OpImm ALU_ADD 16 15 1).
Proof. vm_refl. Qed.
Definition W_5d760 : bv 32 := 0x00e678b3.
Lemma F_5d760 : CTabKA.F 0x5d760 W_5d760.
Proof. vm_refl. Qed.
Lemma D_5d760 : CTabKA.D W_5d760 (Op ALU_AND 17 12 14).
Proof. vm_refl. Qed.
Definition W_5d764 : bv 32 := 0x011687b3.
Lemma F_5d764 : CTabKA.F 0x5d764 W_5d764.
Proof. vm_refl. Qed.
Lemma D_5d764 : CTabKA.D W_5d764 (Op ALU_ADD 15 13 17).
Proof. vm_refl. Qed.
Definition W_5d768 : bv 32 := 0x0007c283.
Lemma F_5d768 : CTabKA.F 0x5d768 W_5d768.
Proof. vm_refl. Qed.
Lemma D_5d768 : CTabKA.D W_5d768 (Load SZ1 false 5 15 0).
Proof. vm_refl. Qed.
Definition W_5d76c : bv 32 := 0x06028663.
Lemma F_5d76c : CTabKA.F 0x5d76c W_5d76c.
Proof. vm_refl. Qed.
Lemma D_5d76c : CTabKA.D W_5d76c (Branch BC_EQ 5 0 108).
Proof. vm_refl. Qed.
Definition W_5d770 : bv 32 := 0xfff5051b.
Lemma F_5d770 : CTabKA.F 0x5d770 W_5d770.
Proof. vm_refl. Qed.
Lemma D_5d770 : CTabKA.D W_5d770 (OpImm32 10 10 4095).
Proof. vm_refl. Qed.
Definition W_5d774 : bv 32 := 0x00160613.
Lemma F_5d774 : CTabKA.F 0x5d774 W_5d774.
Proof. vm_refl. Qed.
Lemma D_5d774 : CTabKA.D W_5d774 (OpImm ALU_ADD 12 12 1).
Proof. vm_refl. Qed.
Definition W_5d778 : bv 32 := 0xfe0514e3.
Lemma F_5d778 : CTabKA.F 0x5d778 W_5d778.
Proof. vm_refl. Qed.
Lemma D_5d778 : CTabKA.D W_5d778 (Branch BC_NE 10 0 8168).
Proof. vm_refl. Qed.
Definition W_5d7d8 : bv 32 := 0x00160613.
Lemma F_5d7d8 : CTabKA.F 0x5d7d8 W_5d7d8.
Proof. vm_refl. Qed.
Lemma D_5d7d8 : CTabKA.D W_5d7d8 (OpImm ALU_ADD 12 12 1).
Proof. vm_refl. Qed.
Definition W_5d7dc : bv 32 := 0x00100513.
Lemma F_5d7dc : CTabKA.F 0x5d7dc W_5d7dc.
Proof. vm_refl. Qed.
Lemma D_5d7dc : CTabKA.D W_5d7dc (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_5d7e0 : bv 32 := 0xffb90693.
Lemma F_5d7e0 : CTabKA.F 0x5d7e0 W_5d7e0.
Proof. vm_refl. Qed.
Lemma D_5d7e0 : CTabKA.D W_5d7e0 (OpImm ALU_ADD 13 18 4091).
Proof. vm_refl. Qed.
Definition W_5d7e4 : bv 32 := 0x00c4bc23.
Lemma F_5d7e4 : CTabKA.F 0x5d7e4 W_5d7e4.
Proof. vm_refl. Qed.
Lemma D_5d7e4 : CTabKA.D W_5d7e4 (Store SZ8 9 12 24).
Proof. vm_refl. Qed.
Definition W_5d7e8 : bv 32 := 0x00a78023.
Lemma F_5d7e8 : CTabKA.F 0x5d7e8 W_5d7e8.
Proof. vm_refl. Qed.
Lemma D_5d7e8 : CTabKA.D W_5d7e8 (Store SZ1 15 10 0).
Proof. vm_refl. Qed.
Definition W_5d7ec : bv 32 := 0x00d51533.
Lemma F_5d7ec : CTabKA.F 0x5d7ec W_5d7ec.
Proof. vm_refl. Qed.
Lemma D_5d7ec : CTabKA.D W_5d7ec (Op ALU_SLL 10 10 13).
Proof. vm_refl. Qed.
Definition W_5d7f0 : bv 32 := 0x00300613.
Lemma F_5d7f0 : CTabKA.F 0x5d7f0 W_5d7f0.
Proof. vm_refl. Qed.
Lemma D_5d7f0 : CTabKA.D W_5d7f0 (OpImm ALU_ADD 12 0 3).
Proof. vm_refl. Qed.
Definition W_5d7f4 : bv 32 := 0x00989893.
Lemma F_5d7f4 : CTabKA.F 0x5d7f4 W_5d7f4.
Proof. vm_refl. Qed.
Lemma D_5d7f4 : CTabKA.D W_5d7f4 (ShiftImm ALU_SLL 17 17 9).
Proof. vm_refl. Qed.
Definition W_5d7f8 : bv 32 := 0x01261633.
Lemma F_5d7f8 : CTabKA.F 0x5d7f8 W_5d7f8.
Proof. vm_refl. Qed.
Lemma D_5d7f8 : CTabKA.D W_5d7f8 (Op ALU_SLL 12 12 18).
Proof. vm_refl. Qed.
Definition W_5d7fc : bv 32 := 0x00a58533.
Lemma F_5d7fc : CTabKA.F 0x5d7fc W_5d7fc.
Proof. vm_refl. Qed.
Lemma D_5d7fc : CTabKA.D W_5d7fc (Op ALU_ADD 10 11 10).
Proof. vm_refl. Qed.
Definition W_5d800 : bv 32 := 0x01160633.
Lemma F_5d800 : CTabKA.F 0x5d800 W_5d800.
Proof. vm_refl. Qed.
Lemma D_5d800 : CTabKA.D W_5d800 (Op ALU_ADD 12 12 17).
Proof. vm_refl. Qed.
Definition W_5d804 : bv 32 := 0x00c504b3.
Lemma F_5d804 : CTabKA.F 0x5d804 W_5d804.
Proof. vm_refl. Qed.
Lemma D_5d804 : CTabKA.D W_5d804 (Op ALU_ADD 9 10 12).
Proof. vm_refl. Qed.
Definition W_5d808 : bv 32 := 0x0084bc23.
Lemma F_5d808 : CTabKA.F 0x5d808 W_5d808.
Proof. vm_refl. Qed.
Lemma D_5d808 : CTabKA.D W_5d808 (Store SZ8 9 8 24).
Proof. vm_refl. Qed.
Definition W_5d80c : bv 32 := 0x1ef4bc23.
Lemma F_5d80c : CTabKA.F 0x5d80c W_5d80c.
Proof. vm_refl. Qed.
Lemma D_5d80c : CTabKA.D W_5d80c (Store SZ8 9 15 504).
Proof. vm_refl. Qed.
Definition W_5d810 : bv 32 := 0x00048513.
Lemma F_5d810 : CTabKA.F 0x5d810 W_5d810.
Proof. vm_refl. Qed.
Lemma D_5d810 : CTabKA.D W_5d810 (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_5d814 : bv 32 := 0x230000ef.
Lemma F_5d814 : CTabKA.F 0x5d814 W_5d814.
Proof. vm_refl. Qed.
Lemma D_5d814 : CTabKA.D W_5d814 (Jal 1 560).
Proof. vm_refl. Qed.
Definition W_5d818 : bv 32 := 0x00050593.
Lemma F_5d818 : CTabKA.F 0x5d818 W_5d818.
Proof. vm_refl. Qed.
Lemma D_5d818 : CTabKA.D W_5d818 (OpImm ALU_ADD 11 10 0).
Proof. vm_refl. Qed.
Definition W_5d81c : bv 32 := 0x00048513.
Lemma F_5d81c : CTabKA.F 0x5d81c W_5d81c.
Proof. vm_refl. Qed.
Lemma D_5d81c : CTabKA.D W_5d81c (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_5d820 : bv 32 := 0x00000613.
Lemma F_5d820 : CTabKA.F 0x5d820 W_5d820.
Proof. vm_refl. Qed.
Lemma D_5d820 : CTabKA.D W_5d820 (OpImm ALU_ADD 12 0 0).
Proof. vm_refl. Qed.
Definition W_5d824 : bv 32 := 0x0005b023.
Lemma F_5d824 : CTabKA.F 0x5d824 W_5d824.
Proof. vm_refl. Qed.
Lemma D_5d824 : CTabKA.D W_5d824 (Store SZ8 11 0 0).
Proof. vm_refl. Qed.
Definition W_5d828 : bv 32 := 0x0005b423.
Lemma F_5d828 : CTabKA.F 0x5d828 W_5d828.
Proof. vm_refl. Qed.
Lemma D_5d828 : CTabKA.D W_5d828 (Store SZ8 11 0 8).
Proof. vm_refl. Qed.
Definition W_5d82c : bv 32 := 0x0005b823.
Lemma F_5d82c : CTabKA.F 0x5d82c W_5d82c.
Proof. vm_refl. Qed.
Lemma D_5d82c : CTabKA.D W_5d82c (Store SZ8 11 0 16).
Proof. vm_refl. Qed.
Definition W_5d830 : bv 32 := 0x0005bc23.
Lemma F_5d830 : CTabKA.F 0x5d830 W_5d830.
Proof. vm_refl. Qed.
Lemma D_5d830 : CTabKA.D W_5d830 (Store SZ8 11 0 24).
Proof. vm_refl. Qed.
Definition W_5d834 : bv 32 := 0x0205b023.
Lemma F_5d834 : CTabKA.F 0x5d834 W_5d834.
Proof. vm_refl. Qed.
Lemma D_5d834 : CTabKA.D W_5d834 (Store SZ8 11 0 32).
Proof. vm_refl. Qed.
Definition W_5d838 : bv 32 := 0x0205b423.
Lemma F_5d838 : CTabKA.F 0x5d838 W_5d838.
Proof. vm_refl. Qed.
Lemma D_5d838 : CTabKA.D W_5d838 (Store SZ8 11 0 40).
Proof. vm_refl. Qed.
Definition W_5d83c : bv 32 := 0x0205b823.
Lemma F_5d83c : CTabKA.F 0x5d83c W_5d83c.
Proof. vm_refl. Qed.
Lemma D_5d83c : CTabKA.D W_5d83c (Store SZ8 11 0 48).
Proof. vm_refl. Qed.
Definition W_5d840 : bv 32 := 0x0205bc23.
Lemma F_5d840 : CTabKA.F 0x5d840 W_5d840.
Proof. vm_refl. Qed.
Lemma D_5d840 : CTabKA.D W_5d840 (Store SZ8 11 0 56).
Proof. vm_refl. Qed.
Definition W_5d844 : bv 32 := 0x01813083.
Lemma F_5d844 : CTabKA.F 0x5d844 W_5d844.
Proof. vm_refl. Qed.
Lemma D_5d844 : CTabKA.D W_5d844 (Load SZ8 true 1 2 24).
Proof. vm_refl. Qed.
Definition W_5d848 : bv 32 := 0x01013403.
Lemma F_5d848 : CTabKA.F 0x5d848 W_5d848.
Proof. vm_refl. Qed.
Lemma D_5d848 : CTabKA.D W_5d848 (Load SZ8 true 8 2 16).
Proof. vm_refl. Qed.
Definition W_5d84c : bv 32 := 0x00813483.
Lemma F_5d84c : CTabKA.F 0x5d84c W_5d84c.
Proof. vm_refl. Qed.
Lemma D_5d84c : CTabKA.D W_5d84c (Load SZ8 true 9 2 8).
Proof. vm_refl. Qed.
Definition W_5d850 : bv 32 := 0x00013903.
Lemma F_5d850 : CTabKA.F 0x5d850 W_5d850.
Proof. vm_refl. Qed.
Lemma D_5d850 : CTabKA.D W_5d850 (Load SZ8 true 18 2 0).
Proof. vm_refl. Qed.
Definition W_5d854 : bv 32 := 0x02010113.
Lemma F_5d854 : CTabKA.F 0x5d854 W_5d854.
Proof. vm_refl. Qed.
Lemma D_5d854 : CTabKA.D W_5d854 (OpImm ALU_ADD 2 2 32).
Proof. vm_refl. Qed.
Definition W_5d858 : bv 32 := 0x00008067.
Lemma F_5d858 : CTabKA.F 0x5d858 W_5d858.
Proof. vm_refl. Qed.
Lemma D_5d858 : CTabKA.D W_5d858 (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_5da44 : bv 32 := 0x000d5597.
Lemma F_5da44 : CTabKA.F 0x5da44 W_5da44.
Proof. vm_refl. Qed.
Lemma D_5da44 : CTabKA.D W_5da44 (Auipc 11 213).
Proof. vm_refl. Qed.
Definition W_5da48 : bv 32 := 0xbf45b583.
Lemma F_5da48 : CTabKA.F 0x5da48 W_5da48.
Proof. vm_refl. Qed.
Lemma D_5da48 : CTabKA.D W_5da48 (Load SZ8 true 11 11 3060).
Proof. vm_refl. Qed.
Definition W_5da4c : bv 32 := 0x0005b583.
Lemma F_5da4c : CTabKA.F 0x5da4c W_5da4c.
Proof. vm_refl. Qed.
Lemma D_5da4c : CTabKA.D W_5da4c (Load SZ8 true 11 11 0).
Proof. vm_refl. Qed.
Definition W_5da50 : bv 32 := 0xfff58613.
Lemma F_5da50 : CTabKA.F 0x5da50 W_5da50.
Proof. vm_refl. Qed.
Lemma D_5da50 : CTabKA.D W_5da50 (OpImm ALU_ADD 12 11 4095).
Proof. vm_refl. Qed.
Definition W_5da54 : bv 32 := 0x00c5b6b3.
Lemma F_5da54 : CTabKA.F 0x5da54 W_5da54.
Proof. vm_refl. Qed.
Lemma D_5da54 : CTabKA.D W_5da54 (Op ALU_SLTU 13 11 12).
Proof. vm_refl. Qed.
Definition W_5da58 : bv 32 := 0xfff68693.
Lemma F_5da58 : CTabKA.F 0x5da58 W_5da58.
Proof. vm_refl. Qed.
Lemma D_5da58 : CTabKA.D W_5da58 (OpImm ALU_ADD 13 13 4095).
Proof. vm_refl. Qed.
Definition W_5da5c : bv 32 := 0x00c6f6b3.
Lemma F_5da5c : CTabKA.F 0x5da5c W_5da5c.
Proof. vm_refl. Qed.
Lemma D_5da5c : CTabKA.D W_5da5c (Op ALU_AND 13 13 12).
Proof. vm_refl. Qed.
Definition W_5da60 : bv 32 := 0x04a6f263.
Lemma F_5da60 : CTabKA.F 0x5da60 W_5da60.
Proof. vm_refl. Qed.
Lemma D_5da60 : CTabKA.D W_5da60 (Branch BC_GEU 13 10 68).
Proof. vm_refl. Qed.
Definition W_5da64 : bv 32 := 0x000d5697.
Lemma F_5da64 : CTabKA.F 0x5da64 W_5da64.
Proof. vm_refl. Qed.
Lemma D_5da64 : CTabKA.D W_5da64 (Auipc 13 213).
Proof. vm_refl. Qed.
Definition W_5da68 : bv 32 := 0xbdc6b683.
Lemma F_5da68 : CTabKA.F 0x5da68 W_5da68.
Proof. vm_refl. Qed.
Lemma D_5da68 : CTabKA.D W_5da68 (Load SZ8 true 13 13 3036).
Proof. vm_refl. Qed.
Definition W_5da6c : bv 32 := 0x000d5717.
Lemma F_5da6c : CTabKA.F 0x5da6c W_5da6c.
Proof. vm_refl. Qed.
Lemma D_5da6c : CTabKA.D W_5da6c (Auipc 14 213).
Proof. vm_refl. Qed.
Definition W_5da70 : bv 32 := 0xbdc73703.
Lemma F_5da70 : CTabKA.F 0x5da70 W_5da70.
Proof. vm_refl. Qed.
Lemma D_5da70 : CTabKA.D W_5da70 (Load SZ8 true 14 14 3036).
Proof. vm_refl. Qed.
Definition W_5da74 : bv 32 := 0x0006b803.
Lemma F_5da74 : CTabKA.F 0x5da74 W_5da74.
Proof. vm_refl. Qed.
Lemma D_5da74 : CTabKA.D W_5da74 (Load SZ8 true 16 13 0).
Proof. vm_refl. Qed.
Definition W_5da78 : bv 32 := 0x00073683.
Lemma F_5da78 : CTabKA.F 0x5da78 W_5da78.
Proof. vm_refl. Qed.
Lemma D_5da78 : CTabKA.D W_5da78 (Load SZ8 true 13 14 0).
Proof. vm_refl. Qed.
Definition W_5da7c : bv 32 := 0xfff80793.
Lemma F_5da7c : CTabKA.F 0x5da7c W_5da7c.
Proof. vm_refl. Qed.
Lemma D_5da7c : CTabKA.D W_5da7c (OpImm ALU_ADD 15 16 4095).
Proof. vm_refl. Qed.
Definition W_5da80 : bv 32 := 0x00a7f463.
Lemma F_5da80 : CTabKA.F 0x5da80 W_5da80.
Proof. vm_refl. Qed.
Lemma D_5da80 : CTabKA.D W_5da80 (Branch BC_GEU 15 10 8).
Proof. vm_refl. Qed.
Definition W_5da88 : bv 32 := 0x000d5717.
Lemma F_5da88 : CTabKA.F 0x5da88 W_5da88.
Proof. vm_refl. Qed.
Lemma D_5da88 : CTabKA.D W_5da88 (Auipc 14 213).
Proof. vm_refl. Qed.
Definition W_5da8c : bv 32 := 0xbc873703.
Lemma F_5da8c : CTabKA.F 0x5da8c W_5da8c.
Proof. vm_refl. Qed.
Lemma D_5da8c : CTabKA.D W_5da8c (Load SZ8 true 14 14 3016).
Proof. vm_refl. Qed.
Definition W_5da90 : bv 32 := 0x00073283.
Lemma F_5da90 : CTabKA.F 0x5da90 W_5da90.
Proof. vm_refl. Qed.
Lemma D_5da90 : CTabKA.D W_5da90 (Load SZ8 true 5 14 0).
Proof. vm_refl. Qed.
Definition W_5da94 : bv 32 := 0x0032d713.
Lemma F_5da94 : CTabKA.F 0x5da94 W_5da94.
Proof. vm_refl. Qed.
Lemma D_5da94 : CTabKA.D W_5da94 (ShiftImm ALU_SRL 14 5 3).
Proof. vm_refl. Qed.
Definition W_5da98 : bv 32 := 0x00b708b3.
Lemma F_5da98 : CTabKA.F 0x5da98 W_5da98.
Proof. vm_refl. Qed.
Lemma D_5da98 : CTabKA.D W_5da98 (Op ALU_ADD 17 14 11).
Proof. vm_refl. Qed.
Definition W_5da9c : bv 32 := 0x00a2ea63.
Lemma F_5da9c : CTabKA.F 0x5da9c W_5da9c.
Proof. vm_refl. Qed.
Lemma D_5da9c : CTabKA.D W_5da9c (Branch BC_LTU 5 10 20).
Proof. vm_refl. Qed.
Definition W_5daa0 : bv 32 := 0x00a8f863.
Lemma F_5daa0 : CTabKA.F 0x5daa0 W_5daa0.
Proof. vm_refl. Qed.
Lemma D_5daa0 : CTabKA.D W_5daa0 (Branch BC_GEU 17 10 16).
Proof. vm_refl. Qed.
Definition W_5daa4 : bv 32 := 0x00355513.
Lemma F_5daa4 : CTabKA.F 0x5daa4 W_5daa4.
Proof. vm_refl. Qed.
Lemma D_5daa4 : CTabKA.D W_5daa4 (ShiftImm ALU_SRL 10 10 3).
Proof. vm_refl. Qed.
Definition W_5daa8 : bv 32 := 0x00a58533.
Lemma F_5daa8 : CTabKA.F 0x5daa8 W_5daa8.
Proof. vm_refl. Qed.
Lemma D_5daa8 : CTabKA.D W_5daa8 (Op ALU_ADD 10 11 10).
Proof. vm_refl. Qed.
Definition W_5daac : bv 32 := 0x00008067.
Lemma F_5daac : CTabKA.F 0x5daac W_5daac.
Proof. vm_refl. Qed.
Lemma D_5daac : CTabKA.D W_5daac (Jalr 0 1 0).
Proof. vm_refl. Qed.

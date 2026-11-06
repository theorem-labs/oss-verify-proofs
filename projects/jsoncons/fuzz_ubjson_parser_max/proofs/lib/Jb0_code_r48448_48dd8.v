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
Definition W_5d0b0 : bv 32 := 0xf7010113.
Lemma F_5d0b0 : CTabKB.F 0x5d0b0 W_5d0b0.
Proof. vm_refl. Qed.
Lemma D_5d0b0 : CTabKB.D W_5d0b0 (OpImm ALU_ADD 2 2 3952).
Proof. vm_refl. Qed.
Definition W_5d0b4 : bv 32 := 0x08113423.
Lemma F_5d0b4 : CTabKB.F 0x5d0b4 W_5d0b4.
Proof. vm_refl. Qed.
Lemma D_5d0b4 : CTabKB.D W_5d0b4 (Store SZ8 2 1 136).
Proof. vm_refl. Qed.
Definition W_5d0b8 : bv 32 := 0x08813023.
Lemma F_5d0b8 : CTabKB.F 0x5d0b8 W_5d0b8.
Proof. vm_refl. Qed.
Lemma D_5d0b8 : CTabKB.D W_5d0b8 (Store SZ8 2 8 128).
Proof. vm_refl. Qed.
Definition W_5d0bc : bv 32 := 0x06913c23.
Lemma F_5d0bc : CTabKB.F 0x5d0bc W_5d0bc.
Proof. vm_refl. Qed.
Lemma D_5d0bc : CTabKB.D W_5d0bc (Store SZ8 2 9 120).
Proof. vm_refl. Qed.
Definition W_5d0c0 : bv 32 := 0x07213823.
Lemma F_5d0c0 : CTabKB.F 0x5d0c0 W_5d0c0.
Proof. vm_refl. Qed.
Lemma D_5d0c0 : CTabKB.D W_5d0c0 (Store SZ8 2 18 112).
Proof. vm_refl. Qed.
Definition W_5d0c4 : bv 32 := 0x07313423.
Lemma F_5d0c4 : CTabKB.F 0x5d0c4 W_5d0c4.
Proof. vm_refl. Qed.
Lemma D_5d0c4 : CTabKB.D W_5d0c4 (Store SZ8 2 19 104).
Proof. vm_refl. Qed.
Definition W_5d0c8 : bv 32 := 0x07413023.
Lemma F_5d0c8 : CTabKB.F 0x5d0c8 W_5d0c8.
Proof. vm_refl. Qed.
Lemma D_5d0c8 : CTabKB.D W_5d0c8 (Store SZ8 2 20 96).
Proof. vm_refl. Qed.
Definition W_5d0cc : bv 32 := 0x05513c23.
Lemma F_5d0cc : CTabKB.F 0x5d0cc W_5d0cc.
Proof. vm_refl. Qed.
Lemma D_5d0cc : CTabKB.D W_5d0cc (Store SZ8 2 21 88).
Proof. vm_refl. Qed.
Definition W_5d0d0 : bv 32 := 0x05613823.
Lemma F_5d0d0 : CTabKB.F 0x5d0d0 W_5d0d0.
Proof. vm_refl. Qed.
Lemma D_5d0d0 : CTabKB.D W_5d0d0 (Store SZ8 2 22 80).
Proof. vm_refl. Qed.
Definition W_5d0d4 : bv 32 := 0x05713423.
Lemma F_5d0d4 : CTabKB.F 0x5d0d4 W_5d0d4.
Proof. vm_refl. Qed.
Lemma D_5d0d4 : CTabKB.D W_5d0d4 (Store SZ8 2 23 72).
Proof. vm_refl. Qed.
Definition W_5d0d8 : bv 32 := 0x05813023.
Lemma F_5d0d8 : CTabKB.F 0x5d0d8 W_5d0d8.
Proof. vm_refl. Qed.
Lemma D_5d0d8 : CTabKB.D W_5d0d8 (Store SZ8 2 24 64).
Proof. vm_refl. Qed.
Definition W_5d0dc : bv 32 := 0x03913c23.
Lemma F_5d0dc : CTabKB.F 0x5d0dc W_5d0dc.
Proof. vm_refl. Qed.
Lemma D_5d0dc : CTabKB.D W_5d0dc (Store SZ8 2 25 56).
Proof. vm_refl. Qed.
Definition W_5d0e0 : bv 32 := 0x03a13823.
Lemma F_5d0e0 : CTabKB.F 0x5d0e0 W_5d0e0.
Proof. vm_refl. Qed.
Lemma D_5d0e0 : CTabKB.D W_5d0e0 (Store SZ8 2 26 48).
Proof. vm_refl. Qed.
Definition W_5d0e4 : bv 32 := 0x03b13423.
Lemma F_5d0e4 : CTabKB.F 0x5d0e4 W_5d0e4.
Proof. vm_refl. Qed.
Lemma D_5d0e4 : CTabKB.D W_5d0e4 (Store SZ8 2 27 40).
Proof. vm_refl. Qed.
Definition W_5d0e8 : bv 32 := 0x00058493.
Lemma F_5d0e8 : CTabKB.F 0x5d0e8 W_5d0e8.
Proof. vm_refl. Qed.
Lemma D_5d0e8 : CTabKB.D W_5d0e8 (OpImm ALU_ADD 9 11 0).
Proof. vm_refl. Qed.
Definition W_5d0ec : bv 32 := 0x00050c93.
Lemma F_5d0ec : CTabKB.F 0x5d0ec W_5d0ec.
Proof. vm_refl. Qed.
Lemma D_5d0ec : CTabKB.D W_5d0ec (OpImm ALU_ADD 25 10 0).
Proof. vm_refl. Qed.
Definition W_5d0f0 : bv 32 := 0x16c260ef.
Lemma F_5d0f0 : CTabKB.F 0x5d0f0 W_5d0f0.
Proof. vm_refl. Qed.
Lemma D_5d0f0 : CTabKB.D W_5d0f0 (Jal 1 156012).
Proof. vm_refl. Qed.
Definition W_5d0f4 : bv 32 := 0x26050463.
Lemma F_5d0f4 : CTabKB.F 0x5d0f4 W_5d0f4.
Proof. vm_refl. Qed.
Lemma D_5d0f4 : CTabKB.D W_5d0f4 (Branch BC_EQ 10 0 616).
Proof. vm_refl. Qed.
Definition W_5d0f8 : bv 32 := 0x00050913.
Lemma F_5d0f8 : CTabKB.F 0x5d0f8 W_5d0f8.
Proof. vm_refl. Qed.
Lemma D_5d0f8 : CTabKB.D W_5d0f8 (OpImm ALU_ADD 18 10 0).
Proof. vm_refl. Qed.
Definition W_5d0fc : bv 32 := 0x324260ef.
Lemma F_5d0fc : CTabKB.F 0x5d0fc W_5d0fc.
Proof. vm_refl. Qed.
Lemma D_5d0fc : CTabKB.D W_5d0fc (Jal 1 156452).
Proof. vm_refl. Qed.
Definition W_5d100 : bv 32 := 0x00050993.
Lemma F_5d100 : CTabKB.F 0x5d100 W_5d100.
Proof. vm_refl. Qed.
Lemma D_5d100 : CTabKB.D W_5d100 (OpImm ALU_ADD 19 10 0).
Proof. vm_refl. Qed.
Definition W_5d104 : bv 32 := 0x00090513.
Lemma F_5d104 : CTabKB.F 0x5d104 W_5d104.
Proof. vm_refl. Qed.
Lemma D_5d104 : CTabKB.D W_5d104 (OpImm ALU_ADD 10 18 0).
Proof. vm_refl. Qed.
Definition W_5d108 : bv 32 := 0x370260ef.
Lemma F_5d108 : CTabKB.F 0x5d108 W_5d108.
Proof. vm_refl. Qed.
Lemma D_5d108 : CTabKB.D W_5d108 (Jal 1 156528).
Proof. vm_refl. Qed.
Definition W_5d10c : bv 32 := 0x2499e863.
Lemma F_5d10c : CTabKB.F 0x5d10c W_5d10c.
Proof. vm_refl. Qed.
Lemma D_5d10c : CTabKB.D W_5d10c (Branch BC_LTU 19 9 592).
Proof. vm_refl. Qed.
Definition W_5d110 : bv 32 := 0x00050913.
Lemma F_5d110 : CTabKB.F 0x5d110 W_5d110.
Proof. vm_refl. Qed.
Lemma D_5d110 : CTabKB.D W_5d110 (OpImm ALU_ADD 18 10 0).
Proof. vm_refl. Qed.
Definition W_5d114 : bv 32 := 0x24a4e463.
Lemma F_5d114 : CTabKB.F 0x5d114 W_5d114.
Proof. vm_refl. Qed.
Lemma D_5d114 : CTabKB.D W_5d114 (Branch BC_LTU 9 10 584).
Proof. vm_refl. Qed.
Definition W_5d118 : bv 32 := 0x00000d13.
Lemma F_5d118 : CTabKB.F 0x5d118 W_5d118.
Proof. vm_refl. Qed.
Lemma D_5d118 : CTabKB.D W_5d118 (OpImm ALU_ADD 26 0 0).
Proof. vm_refl. Qed.
Definition W_5d11c : bv 32 := 0x00001437.
Lemma F_5d11c : CTabKB.F 0x5d11c W_5d11c.
Proof. vm_refl. Qed.
Lemma D_5d11c : CTabKB.D W_5d11c (Lui 8 1).
Proof. vm_refl. Qed.
Definition W_5d120 : bv 32 := 0x000d7517.
Lemma F_5d120 : CTabKB.F 0x5d120 W_5d120.
Proof. vm_refl. Qed.
Lemma D_5d120 : CTabKB.D W_5d120 (Auipc 10 215).
Proof. vm_refl. Qed.
Definition W_5d124 : bv 32 := 0x000d7597.
Lemma F_5d124 : CTabKB.F 0x5d124 W_5d124.
Proof. vm_refl. Qed.
Lemma D_5d124 : CTabKB.D W_5d124 (Auipc 11 215).
Proof. vm_refl. Qed.
Definition W_5d128 : bv 32 := 0x000d7617.
Lemma F_5d128 : CTabKB.F 0x5d128 W_5d128.
Proof. vm_refl. Qed.
Lemma D_5d128 : CTabKB.D W_5d128 (Auipc 12 215).
Proof. vm_refl. Qed.
Definition W_5d12c : bv 32 := 0x000d7697.
Lemma F_5d12c : CTabKB.F 0x5d12c W_5d12c.
Proof. vm_refl. Qed.
Lemma D_5d12c : CTabKB.D W_5d12c (Auipc 13 215).
Proof. vm_refl. Qed.
Definition W_5d130 : bv 32 := 0x000d7717.
Lemma F_5d130 : CTabKB.F 0x5d130 W_5d130.
Proof. vm_refl. Qed.
Lemma D_5d130 : CTabKB.D W_5d130 (Auipc 14 215).
Proof. vm_refl. Qed.
Definition W_5d134 : bv 32 := 0xfffb3797.
Lemma F_5d134 : CTabKB.F 0x5d134 W_5d134.
Proof. vm_refl. Qed.
Lemma D_5d134 : CTabKB.D W_5d134 (Auipc 15 1048499).
Proof. vm_refl. Qed.
Definition W_5d138 : bv 32 := 0x008c8433.
Lemma F_5d138 : CTabKB.F 0x5d138 W_5d138.
Proof. vm_refl. Qed.
Lemma D_5d138 : CTabKB.D W_5d138 (Op ALU_ADD 8 25 8).
Proof. vm_refl. Qed.
Definition W_5d13c : bv 32 := 0x28053b03.
Lemma F_5d13c : CTabKB.F 0x5d13c W_5d13c.
Proof. vm_refl. Qed.
Lemma D_5d13c : CTabKB.D W_5d13c (Load SZ8 true 22 10 640).
Proof. vm_refl. Qed.
Definition W_5d140 : bv 32 := 0x2845b503.
Lemma F_5d140 : CTabKB.F 0x5d140 W_5d140.
Proof. vm_refl. Qed.
Lemma D_5d140 : CTabKB.D W_5d140 (Load SZ8 true 10 11 644).
Proof. vm_refl. Qed.
Definition W_5d144 : bv 32 := 0x00a13c23.
Lemma F_5d144 : CTabKB.F 0x5d144 W_5d144.
Proof. vm_refl. Qed.
Lemma D_5d144 : CTabKB.D W_5d144 (Store SZ8 2 10 24).
Proof. vm_refl. Qed.
Definition W_5d148 : bv 32 := 0x28863503.
Lemma F_5d148 : CTabKB.F 0x5d148 W_5d148.
Proof. vm_refl. Qed.
Lemma D_5d148 : CTabKB.D W_5d148 (Load SZ8 true 10 12 648).
Proof. vm_refl. Qed.
Definition W_5d14c : bv 32 := 0x00a13823.
Lemma F_5d14c : CTabKB.F 0x5d14c W_5d14c.
Proof. vm_refl. Qed.
Lemma D_5d14c : CTabKB.D W_5d14c (Store SZ8 2 10 16).
Proof. vm_refl. Qed.
Definition W_5d150 : bv 32 := 0x28c6b503.
Lemma F_5d150 : CTabKB.F 0x5d150 W_5d150.
Proof. vm_refl. Qed.
Lemma D_5d150 : CTabKB.D W_5d150 (Load SZ8 true 10 13 652).
Proof. vm_refl. Qed.
Definition W_5d154 : bv 32 := 0x00a13423.
Lemma F_5d154 : CTabKB.F 0x5d154 W_5d154.
Proof. vm_refl. Qed.
Lemma D_5d154 : CTabKB.D W_5d154 (Store SZ8 2 10 8).
Proof. vm_refl. Qed.
Definition W_5d158 : bv 32 := 0x26873503.
Lemma F_5d158 : CTabKB.F 0x5d158 W_5d158.
Proof. vm_refl. Qed.
Lemma D_5d158 : CTabKB.D W_5d158 (Load SZ8 true 10 14 616).
Proof. vm_refl. Qed.
Definition W_5d15c : bv 32 := 0x00a13023.
Lemma F_5d15c : CTabKB.F 0x5d15c W_5d15c.
Proof. vm_refl. Qed.
Lemma D_5d15c : CTabKB.D W_5d15c (Store SZ8 2 10 0).
Proof. vm_refl. Qed.
Definition W_5d160 : bv 32 := 0x23c7bb83.
Lemma F_5d160 : CTabKB.F 0x5d160 W_5d160.
Proof. vm_refl. Qed.
Lemma D_5d160 : CTabKB.D W_5d160 (Load SZ8 true 23 15 572).
Proof. vm_refl. Qed.
Definition W_5d164 : bv 32 := 0x00100393.
Lemma F_5d164 : CTabKB.F 0x5d164 W_5d164.
Proof. vm_refl. Qed.
Lemma D_5d164 : CTabKB.D W_5d164 (OpImm ALU_ADD 7 0 1).
Proof. vm_refl. Qed.
Definition W_5d168 : bv 32 := 0x00600e13.
Lemma F_5d168 : CTabKB.F 0x5d168 W_5d168.
Proof. vm_refl. Qed.
Lemma D_5d168 : CTabKB.D W_5d168 (OpImm ALU_ADD 28 0 6).
Proof. vm_refl. Qed.
Definition W_5d16c : bv 32 := 0x00000a13.
Lemma F_5d16c : CTabKB.F 0x5d16c W_5d16c.
Proof. vm_refl. Qed.
Lemma D_5d16c : CTabKB.D W_5d16c (OpImm ALU_ADD 20 0 0).
Proof. vm_refl. Qed.
Definition W_5d170 : bv 32 := 0x0100006f.
Lemma F_5d170 : CTabKB.F 0x5d170 W_5d170.
Proof. vm_refl. Qed.
Lemma D_5d170 : CTabKB.D W_5d170 (Jal 0 16).
Proof. vm_refl. Qed.
Definition W_5d174 : bv 32 := 0x001a0a13.
Lemma F_5d174 : CTabKB.F 0x5d174 W_5d174.
Proof. vm_refl. Qed.
Lemma D_5d174 : CTabKB.D W_5d174 (OpImm ALU_ADD 20 20 1).
Proof. vm_refl. Qed.
Definition W_5d178 : bv 32 := 0x00b00513.
Lemma F_5d178 : CTabKB.F 0x5d178 W_5d178.
Proof. vm_refl. Qed.
Lemma D_5d178 : CTabKB.D W_5d178 (OpImm ALU_ADD 10 0 11).
Proof. vm_refl. Qed.
Definition W_5d17c : bv 32 := 0x1caa0e63.
Lemma F_5d17c : CTabKB.F 0x5d17c W_5d17c.
Proof. vm_refl. Qed.
Lemma D_5d17c : CTabKB.D W_5d17c (Branch BC_EQ 20 10 476).
Proof. vm_refl. Qed.
Definition W_5d180 : bv 32 := 0x00000d93.
Lemma F_5d180 : CTabKB.F 0x5d180 W_5d180.
Proof. vm_refl. Qed.
Lemma D_5d180 : CTabKB.D W_5d180 (OpImm ALU_ADD 27 0 0).
Proof. vm_refl. Qed.
Definition W_5d184 : bv 32 := 0x058cb503.
Lemma F_5d184 : CTabKB.F 0x5d184 W_5d184.
Proof. vm_refl. Qed.
Lemma D_5d184 : CTabKB.D W_5d184 (Load SZ8 true 10 25 88).
Proof. vm_refl. Qed.
Definition W_5d188 : bv 32 := 0x00a00593.
Lemma F_5d188 : CTabKB.F 0x5d188 W_5d188.
Proof. vm_refl. Qed.
Lemma D_5d188 : CTabKB.D W_5d188 (OpImm ALU_ADD 11 0 10).
Proof. vm_refl. Qed.
Definition W_5d18c : bv 32 := 0x414585bb.
Lemma F_5d18c : CTabKB.F 0x5d18c W_5d18c.
Proof. vm_refl. Qed.
Lemma D_5d18c : CTabKB.D W_5d18c (Op32 ALU_SUB 11 11 20).
Proof. vm_refl. Qed.
Definition W_5d190 : bv 32 := 0x006a0a93.
Lemma F_5d190 : CTabKB.F 0x5d190 W_5d190.
Proof. vm_refl. Qed.
Lemma D_5d190 : CTabKB.D W_5d190 (OpImm ALU_ADD 21 20 6).
Proof. vm_refl. Qed.
Definition W_5d194 : bv 32 := 0xfff00613.
Lemma F_5d194 : CTabKB.F 0x5d194 W_5d194.
Proof. vm_refl. Qed.
Lemma D_5d194 : CTabKB.D W_5d194 (OpImm ALU_ADD 12 0 4095).
Proof. vm_refl. Qed.
Definition W_5d198 : bv 32 := 0x00b615b3.
Lemma F_5d198 : CTabKB.F 0x5d198 W_5d198.
Proof. vm_refl. Qed.
Lemma D_5d198 : CTabKB.D W_5d198 (Op ALU_SLL 11 12 11).
Proof. vm_refl. Qed.
Definition W_5d19c : bv 32 := 0x3ff5f593.
Lemma F_5d19c : CTabKB.F 0x5d19c W_5d19c.
Proof. vm_refl. Qed.
Lemma D_5d19c : CTabKB.D W_5d19c (OpImm ALU_AND 11 11 1023).
Proof. vm_refl. Qed.
Definition W_5d1a0 : bv 32 := 0xff150613.
Lemma F_5d1a0 : CTabKB.F 0x5d1a0 W_5d1a0.
Proof. vm_refl. Qed.
Lemma D_5d1a0 : CTabKB.D W_5d1a0 (OpImm ALU_ADD 12 10 4081).
Proof. vm_refl. Qed.
Definition W_5d1a4 : bv 32 := 0x414509b3.
Lemma F_5d1a4 : CTabKB.F 0x5d1a4 W_5d1a4.
Proof. vm_refl. Qed.
Lemma D_5d1a4 : CTabKB.D W_5d1a4 (Op ALU_SUB 19 10 20).
Proof. vm_refl. Qed.
Definition W_5d1a8 : bv 32 := 0x00c59c33.
Lemma F_5d1a8 : CTabKB.F 0x5d1a8 W_5d1a8.
Proof. vm_refl. Qed.
Lemma D_5d1a8 : CTabKB.D W_5d1a8 (Op ALU_SLL 24 11 12).
Proof. vm_refl. Qed.
Definition W_5d1ac : bv 32 := 0xffa98993.
Lemma F_5d1ac : CTabKB.F 0x5d1ac W_5d1ac.
Proof. vm_refl. Qed.
Lemma D_5d1ac : CTabKB.D W_5d1ac (OpImm ALU_ADD 19 19 4090).
Proof. vm_refl. Qed.
Definition W_5d1b0 : bv 32 := 0x01840c33.
Lemma F_5d1b0 : CTabKB.F 0x5d1b0 W_5d1b0.
Proof. vm_refl. Qed.
Lemma D_5d1b0 : CTabKB.D W_5d1b0 (Op ALU_ADD 24 8 24).
Proof. vm_refl. Qed.
Definition W_5d1b4 : bv 32 := 0x04000513.
Lemma F_5d1b4 : CTabKB.F 0x5d1b4 W_5d1b4.
Proof. vm_refl. Qed.
Lemma D_5d1b4 : CTabKB.D W_5d1b4 (OpImm ALU_ADD 10 0 64).
Proof. vm_refl. Qed.
Definition W_5d1b8 : bv 32 := 0x01451533.
Lemma F_5d1b8 : CTabKB.F 0x5d1b8 W_5d1b8.
Proof. vm_refl. Qed.
Lemma D_5d1b8 : CTabKB.D W_5d1b8 (Op ALU_SLL 10 10 20).
Proof. vm_refl. Qed.
Definition W_5d1bc : bv 32 := 0x02a13023.
Lemma F_5d1bc : CTabKB.F 0x5d1bc W_5d1bc.
Proof. vm_refl. Qed.
Lemma D_5d1bc : CTabKB.D W_5d1bc (Store SZ8 2 10 32).
Proof. vm_refl. Qed.
Definition W_5d1c0 : bv 32 := 0x0240006f.
Lemma F_5d1c0 : CTabKB.F 0x5d1c0 W_5d1c0.
Proof. vm_refl. Qed.
Lemma D_5d1c0 : CTabKB.D W_5d1c0 (Jal 0 36).
Proof. vm_refl. Qed.
Definition W_5d1d8 : bv 32 := 0x001d8d93.
Lemma F_5d1d8 : CTabKB.F 0x5d1d8 W_5d1d8.
Proof. vm_refl. Qed.
Lemma D_5d1d8 : CTabKB.D W_5d1d8 (OpImm ALU_ADD 27 27 1).
Proof. vm_refl. Qed.
Definition W_5d1dc : bv 32 := 0x013dd533.
Lemma F_5d1dc : CTabKB.F 0x5d1dc W_5d1dc.
Proof. vm_refl. Qed.
Lemma D_5d1dc : CTabKB.D W_5d1dc (Op ALU_SRL 10 27 19).
Proof. vm_refl. Qed.
Definition W_5d1e0 : bv 32 := 0xf8051ae3.
Lemma F_5d1e0 : CTabKB.F 0x5d1e0 W_5d1e0.
Proof. vm_refl. Qed.
Lemma D_5d1e0 : CTabKB.D W_5d1e0 (Branch BC_NE 10 0 8084).
Proof. vm_refl. Qed.
Definition W_5d1e4 : bv 32 := 0x01bc05b3.
Lemma F_5d1e4 : CTabKB.F 0x5d1e4 W_5d1e4.
Proof. vm_refl. Qed.
Lemma D_5d1e4 : CTabKB.D W_5d1e4 (Op ALU_ADD 11 24 27).
Proof. vm_refl. Qed.
Definition W_5d1e8 : bv 32 := 0x0005c503.
Lemma F_5d1e8 : CTabKB.F 0x5d1e8 W_5d1e8.
Proof. vm_refl. Qed.
Lemma D_5d1e8 : CTabKB.D W_5d1e8 (Load SZ1 false 10 11 0).
Proof. vm_refl. Qed.
Definition W_5d1ec : bv 32 := 0xfe0506e3.
Lemma F_5d1ec : CTabKB.F 0x5d1ec W_5d1ec.
Proof. vm_refl. Qed.
Lemma D_5d1ec : CTabKB.D W_5d1ec (Branch BC_EQ 10 0 8172).
Proof. vm_refl. Qed.
Definition W_5d1f0 : bv 32 := 0x058cb503.
Lemma F_5d1f0 : CTabKB.F 0x5d1f0 W_5d1f0.
Proof. vm_refl. Qed.
Lemma D_5d1f0 : CTabKB.D W_5d1f0 (Load SZ8 true 10 25 88).
Proof. vm_refl. Qed.
Definition W_5d1f4 : bv 32 := 0xffb50613.
Lemma F_5d1f4 : CTabKB.F 0x5d1f4 W_5d1f4.
Proof. vm_refl. Qed.
Lemma D_5d1f4 : CTabKB.D W_5d1f4 (OpImm ALU_ADD 12 10 4091).
Proof. vm_refl. Qed.
Definition W_5d1f8 : bv 32 := 0x00aa1533.
Lemma F_5d1f8 : CTabKB.F 0x5d1f8 W_5d1f8.
Proof. vm_refl. Qed.
Lemma D_5d1f8 : CTabKB.D W_5d1f8 (Op ALU_SLL 10 20 10).
Proof. vm_refl. Qed.
Definition W_5d1fc : bv 32 := 0x00c39633.
Lemma F_5d1fc : CTabKB.F 0x5d1fc W_5d1fc.
Proof. vm_refl. Qed.
Lemma D_5d1fc : CTabKB.D W_5d1fc (Op ALU_SLL 12 7 12).
Proof. vm_refl. Qed.
Definition W_5d200 : bv 32 := 0x00a40533.
Lemma F_5d200 : CTabKB.F 0x5d200 W_5d200.
Proof. vm_refl. Qed.
Lemma D_5d200 : CTabKB.D W_5d200 (Op ALU_ADD 10 8 10).
Proof. vm_refl. Qed.
Definition W_5d204 : bv 32 := 0x00c50533.
Lemma F_5d204 : CTabKB.F 0x5d204 W_5d204.
Proof. vm_refl. Qed.
Lemma D_5d204 : CTabKB.D W_5d204 (Op ALU_ADD 10 10 12).
Proof. vm_refl. Qed.
Definition W_5d208 : bv 32 := 0x015d9633.
Lemma F_5d208 : CTabKB.F 0x5d208 W_5d208.
Proof. vm_refl. Qed.
Lemma D_5d208 : CTabKB.D W_5d208 (Op ALU_SLL 12 27 21).
Proof. vm_refl. Qed.
Definition W_5d20c : bv 32 := 0x00c50533.
Lemma F_5d20c : CTabKB.F 0x5d20c W_5d20c.
Proof. vm_refl. Qed.
Lemma D_5d20c : CTabKB.D W_5d20c (Op ALU_ADD 10 10 12).
Proof. vm_refl. Qed.
Definition W_5d210 : bv 32 := 0x01853603.
Lemma F_5d210 : CTabKB.F 0x5d210 W_5d210.
Proof. vm_refl. Qed.
Lemma D_5d210 : CTabKB.D W_5d210 (Load SZ8 true 12 10 24).
Proof. vm_refl. Qed.
Definition W_5d214 : bv 32 := 0xfcc972e3.
Lemma F_5d214 : CTabKB.F 0x5d214 W_5d214.
Proof. vm_refl. Qed.
Lemma D_5d214 : CTabKB.D W_5d214 (Branch BC_GEU 18 12 8132).
Proof. vm_refl. Qed.
Definition W_5d218 : bv 32 := 0xfc9670e3.
Lemma F_5d218 : CTabKB.F 0x5d218 W_5d218.
Proof. vm_refl. Qed.
Lemma D_5d218 : CTabKB.D W_5d218 (Branch BC_GEU 12 9 8128).
Proof. vm_refl. Qed.
Definition W_5d21c : bv 32 := 0x01a58023.
Lemma F_5d21c : CTabKB.F 0x5d21c W_5d21c.
Proof. vm_refl. Qed.
Lemma D_5d21c : CTabKB.D W_5d21c (Store SZ1 11 26 0).
Proof. vm_refl. Qed.
Definition W_5d220 : bv 32 := 0x000b3583.
Lemma F_5d220 : CTabKB.F 0x5d220 W_5d220.
Proof. vm_refl. Qed.
Lemma D_5d220 : CTabKB.D W_5d220 (Load SZ8 true 11 22 0).
Proof. vm_refl. Qed.
Definition W_5d224 : bv 32 := 0xfff58613.
Lemma F_5d224 : CTabKB.F 0x5d224 W_5d224.
Proof. vm_refl. Qed.
Lemma D_5d224 : CTabKB.D W_5d224 (OpImm ALU_ADD 12 11 4095).
Proof. vm_refl. Qed.
Definition W_5d228 : bv 32 := 0x00c5b6b3.
Lemma F_5d228 : CTabKB.F 0x5d228 W_5d228.
Proof. vm_refl. Qed.
Lemma D_5d228 : CTabKB.D W_5d228 (Op ALU_SLTU 13 11 12).
Proof. vm_refl. Qed.
Definition W_5d22c : bv 32 := 0xfff68693.
Lemma F_5d22c : CTabKB.F 0x5d22c W_5d22c.
Proof. vm_refl. Qed.
Lemma D_5d22c : CTabKB.D W_5d22c (OpImm ALU_ADD 13 13 4095).
Proof. vm_refl. Qed.
Definition W_5d230 : bv 32 := 0x00c6f6b3.
Lemma F_5d230 : CTabKB.F 0x5d230 W_5d230.
Proof. vm_refl. Qed.
Lemma D_5d230 : CTabKB.D W_5d230 (Op ALU_AND 13 13 12).
Proof. vm_refl. Qed.
Definition W_5d234 : bv 32 := 0x02a6fc63.
Lemma F_5d234 : CTabKB.F 0x5d234 W_5d234.
Proof. vm_refl. Qed.
Lemma D_5d234 : CTabKB.D W_5d234 (Branch BC_GEU 13 10 56).
Proof. vm_refl. Qed.
Definition W_5d238 : bv 32 := 0x01813683.
Lemma F_5d238 : CTabKB.F 0x5d238 W_5d238.
Proof. vm_refl. Qed.
Lemma D_5d238 : CTabKB.D W_5d238 (Load SZ8 true 13 2 24).
Proof. vm_refl. Qed.
Definition W_5d23c : bv 32 := 0x0006b803.
Lemma F_5d23c : CTabKB.F 0x5d23c W_5d23c.
Proof. vm_refl. Qed.
Lemma D_5d23c : CTabKB.D W_5d23c (Load SZ8 true 16 13 0).
Proof. vm_refl. Qed.
Definition W_5d240 : bv 32 := 0x01013683.
Lemma F_5d240 : CTabKB.F 0x5d240 W_5d240.
Proof. vm_refl. Qed.
Lemma D_5d240 : CTabKB.D W_5d240 (Load SZ8 true 13 2 16).
Proof. vm_refl. Qed.
Definition W_5d244 : bv 32 := 0x0006b683.
Lemma F_5d244 : CTabKB.F 0x5d244 W_5d244.
Proof. vm_refl. Qed.
Lemma D_5d244 : CTabKB.D W_5d244 (Load SZ8 true 13 13 0).
Proof. vm_refl. Qed.
Definition W_5d248 : bv 32 := 0xfff80793.
Lemma F_5d248 : CTabKB.F 0x5d248 W_5d248.
Proof. vm_refl. Qed.
Lemma D_5d248 : CTabKB.D W_5d248 (OpImm ALU_ADD 15 16 4095).
Proof. vm_refl. Qed.
Definition W_5d24c : bv 32 := 0x00a7f463.
Lemma F_5d24c : CTabKB.F 0x5d24c W_5d24c.
Proof. vm_refl. Qed.
Lemma D_5d24c : CTabKB.D W_5d24c (Branch BC_GEU 15 10 8).
Proof. vm_refl. Qed.
Definition W_5d254 : bv 32 := 0x00813703.
Lemma F_5d254 : CTabKB.F 0x5d254 W_5d254.
Proof. vm_refl. Qed.
Lemma D_5d254 : CTabKB.D W_5d254 (Load SZ8 true 14 2 8).
Proof. vm_refl. Qed.
Definition W_5d258 : bv 32 := 0x00073283.
Lemma F_5d258 : CTabKB.F 0x5d258 W_5d258.
Proof. vm_refl. Qed.
Lemma D_5d258 : CTabKB.D W_5d258 (Load SZ8 true 5 14 0).
Proof. vm_refl. Qed.
Definition W_5d25c : bv 32 := 0x0032d713.
Lemma F_5d25c : CTabKB.F 0x5d25c W_5d25c.
Proof. vm_refl. Qed.
Lemma D_5d25c : CTabKB.D W_5d25c (ShiftImm ALU_SRL 14 5 3).
Proof. vm_refl. Qed.
Definition W_5d260 : bv 32 := 0x00b708b3.
Lemma F_5d260 : CTabKB.F 0x5d260 W_5d260.
Proof. vm_refl. Qed.
Lemma D_5d260 : CTabKB.D W_5d260 (Op ALU_ADD 17 14 11).
Proof. vm_refl. Qed.
Definition W_5d264 : bv 32 := 0x02a2e863.
Lemma F_5d264 : CTabKB.F 0x5d264 W_5d264.
Proof. vm_refl. Qed.
Lemma D_5d264 : CTabKB.D W_5d264 (Branch BC_LTU 5 10 48).
Proof. vm_refl. Qed.
Definition W_5d268 : bv 32 := 0x02a8f663.
Lemma F_5d268 : CTabKB.F 0x5d268 W_5d268.
Proof. vm_refl. Qed.
Lemma D_5d268 : CTabKB.D W_5d268 (Branch BC_GEU 17 10 44).
Proof. vm_refl. Qed.
Definition W_5d26c : bv 32 := 0xf54e6ce3.
Lemma F_5d26c : CTabKB.F 0x5d26c W_5d26c.
Proof. vm_refl. Qed.
Lemma D_5d26c : CTabKB.D W_5d26c (Branch BC_LTU 28 20 8024).
Proof. vm_refl. Qed.
Definition W_5d270 : bv 32 := 0x00355513.
Lemma F_5d270 : CTabKB.F 0x5d270 W_5d270.
Proof. vm_refl. Qed.
Lemma D_5d270 : CTabKB.D W_5d270 (ShiftImm ALU_SRL 10 10 3).
Proof. vm_refl. Qed.
Definition W_5d274 : bv 32 := 0x00a585b3.
Lemma F_5d274 : CTabKB.F 0x5d274 W_5d274.
Proof. vm_refl. Qed.
Lemma D_5d274 : CTabKB.D W_5d274 (Op ALU_ADD 11 11 10).
Proof. vm_refl. Qed.
Definition W_5d278 : bv 32 := 0x00100513.
Lemma F_5d278 : CTabKB.F 0x5d278 W_5d278.
Proof. vm_refl. Qed.
Lemma D_5d278 : CTabKB.D W_5d278 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_5d27c : bv 32 := 0x0175b023.
Lemma F_5d27c : CTabKB.F 0x5d27c W_5d27c.
Proof. vm_refl. Qed.
Lemma D_5d27c : CTabKB.D W_5d27c (Store SZ8 11 23 0).
Proof. vm_refl. Qed.
Definition W_5d280 : bv 32 := 0x01455633.
Lemma F_5d280 : CTabKB.F 0x5d280 W_5d280.
Proof. vm_refl. Qed.
Lemma D_5d280 : CTabKB.D W_5d280 (Op ALU_SRL 12 10 20).
Proof. vm_refl. Qed.
Definition W_5d284 : bv 32 := 0x00858593.
Lemma F_5d284 : CTabKB.F 0x5d284 W_5d284.
Proof. vm_refl. Qed.
Lemma D_5d284 : CTabKB.D W_5d284 (OpImm ALU_ADD 11 11 8).
Proof. vm_refl. Qed.
Definition W_5d288 : bv 32 := 0x00150513.
Lemma F_5d288 : CTabKB.F 0x5d288 W_5d288.
Proof. vm_refl. Qed.
Lemma D_5d288 : CTabKB.D W_5d288 (OpImm ALU_ADD 10 10 1).
Proof. vm_refl. Qed.
Definition W_5d28c : bv 32 := 0xfe0608e3.
Lemma F_5d28c : CTabKB.F 0x5d28c W_5d28c.
Proof. vm_refl. Qed.
Lemma D_5d28c : CTabKB.D W_5d28c (Branch BC_EQ 12 0 8176).
Proof. vm_refl. Qed.
Definition W_5d290 : bv 32 := 0xf49ff06f.
Lemma F_5d290 : CTabKB.F 0x5d290 W_5d290.
Proof. vm_refl. Qed.
Lemma D_5d290 : CTabKB.D W_5d290 (Jal 0 2096968).
Proof. vm_refl. Qed.
Definition W_5d358 : bv 32 := 0x060c8023.
Lemma F_5d358 : CTabKB.F 0x5d358 W_5d358.
Proof. vm_refl. Qed.
Lemma D_5d358 : CTabKB.D W_5d358 (Store SZ1 25 0 96).
Proof. vm_refl. Qed.
Definition W_5d35c : bv 32 := 0x08813083.
Lemma F_5d35c : CTabKB.F 0x5d35c W_5d35c.
Proof. vm_refl. Qed.
Lemma D_5d35c : CTabKB.D W_5d35c (Load SZ8 true 1 2 136).
Proof. vm_refl. Qed.
Definition W_5d360 : bv 32 := 0x08013403.
Lemma F_5d360 : CTabKB.F 0x5d360 W_5d360.
Proof. vm_refl. Qed.
Lemma D_5d360 : CTabKB.D W_5d360 (Load SZ8 true 8 2 128).
Proof. vm_refl. Qed.
Definition W_5d364 : bv 32 := 0x07813483.
Lemma F_5d364 : CTabKB.F 0x5d364 W_5d364.
Proof. vm_refl. Qed.
Lemma D_5d364 : CTabKB.D W_5d364 (Load SZ8 true 9 2 120).
Proof. vm_refl. Qed.
Definition W_5d368 : bv 32 := 0x07013903.
Lemma F_5d368 : CTabKB.F 0x5d368 W_5d368.
Proof. vm_refl. Qed.
Lemma D_5d368 : CTabKB.D W_5d368 (Load SZ8 true 18 2 112).
Proof. vm_refl. Qed.
Definition W_5d36c : bv 32 := 0x06813983.
Lemma F_5d36c : CTabKB.F 0x5d36c W_5d36c.
Proof. vm_refl. Qed.
Lemma D_5d36c : CTabKB.D W_5d36c (Load SZ8 true 19 2 104).
Proof. vm_refl. Qed.
Definition W_5d370 : bv 32 := 0x06013a03.
Lemma F_5d370 : CTabKB.F 0x5d370 W_5d370.
Proof. vm_refl. Qed.
Lemma D_5d370 : CTabKB.D W_5d370 (Load SZ8 true 20 2 96).
Proof. vm_refl. Qed.
Definition W_5d374 : bv 32 := 0x05813a83.
Lemma F_5d374 : CTabKB.F 0x5d374 W_5d374.
Proof. vm_refl. Qed.
Lemma D_5d374 : CTabKB.D W_5d374 (Load SZ8 true 21 2 88).
Proof. vm_refl. Qed.
Definition W_5d378 : bv 32 := 0x05013b03.
Lemma F_5d378 : CTabKB.F 0x5d378 W_5d378.
Proof. vm_refl. Qed.
Lemma D_5d378 : CTabKB.D W_5d378 (Load SZ8 true 22 2 80).
Proof. vm_refl. Qed.
Definition W_5d37c : bv 32 := 0x04813b83.
Lemma F_5d37c : CTabKB.F 0x5d37c W_5d37c.
Proof. vm_refl. Qed.
Lemma D_5d37c : CTabKB.D W_5d37c (Load SZ8 true 23 2 72).
Proof. vm_refl. Qed.
Definition W_5d380 : bv 32 := 0x04013c03.
Lemma F_5d380 : CTabKB.F 0x5d380 W_5d380.
Proof. vm_refl. Qed.
Lemma D_5d380 : CTabKB.D W_5d380 (Load SZ8 true 24 2 64).
Proof. vm_refl. Qed.
Definition W_5d384 : bv 32 := 0x03813c83.
Lemma F_5d384 : CTabKB.F 0x5d384 W_5d384.
Proof. vm_refl. Qed.
Lemma D_5d384 : CTabKB.D W_5d384 (Load SZ8 true 25 2 56).
Proof. vm_refl. Qed.
Definition W_5d388 : bv 32 := 0x03013d03.
Lemma F_5d388 : CTabKB.F 0x5d388 W_5d388.
Proof. vm_refl. Qed.
Lemma D_5d388 : CTabKB.D W_5d388 (Load SZ8 true 26 2 48).
Proof. vm_refl. Qed.
Definition W_5d38c : bv 32 := 0x02813d83.
Lemma F_5d38c : CTabKB.F 0x5d38c W_5d38c.
Proof. vm_refl. Qed.
Lemma D_5d38c : CTabKB.D W_5d38c (Load SZ8 true 27 2 40).
Proof. vm_refl. Qed.
Definition W_5d390 : bv 32 := 0x09010113.
Lemma F_5d390 : CTabKB.F 0x5d390 W_5d390.
Proof. vm_refl. Qed.
Lemma D_5d390 : CTabKB.D W_5d390 (OpImm ALU_ADD 2 2 144).
Proof. vm_refl. Qed.
Definition W_5d394 : bv 32 := 0x00008067.
Lemma F_5d394 : CTabKB.F 0x5d394 W_5d394.
Proof. vm_refl. Qed.
Lemma D_5d394 : CTabKB.D W_5d394 (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_5d398 : bv 32 := 0x00100593.
Lemma F_5d398 : CTabKB.F 0x5d398 W_5d398.
Proof. vm_refl. Qed.
Lemma D_5d398 : CTabKB.D W_5d398 (OpImm ALU_ADD 11 0 1).
Proof. vm_refl. Qed.
Definition W_5d39c : bv 32 := 0x06b50023.
Lemma F_5d39c : CTabKB.F 0x5d39c W_5d39c.
Proof. vm_refl. Qed.
Lemma D_5d39c : CTabKB.D W_5d39c (Store SZ1 10 11 96).
Proof. vm_refl. Qed.
Definition W_5d3a0 : bv 32 := 0x00008067.
Lemma F_5d3a0 : CTabKB.F 0x5d3a0 W_5d3a0.
Proof. vm_refl. Qed.
Lemma D_5d3a0 : CTabKB.D W_5d3a0 (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_5d670 : bv 32 := 0xfe010113.
Lemma F_5d670 : CTabKB.F 0x5d670 W_5d670.
Proof. vm_refl. Qed.
Lemma D_5d670 : CTabKB.D W_5d670 (OpImm ALU_ADD 2 2 4064).
Proof. vm_refl. Qed.
Definition W_5d674 : bv 32 := 0x00113c23.
Lemma F_5d674 : CTabKB.F 0x5d674 W_5d674.
Proof. vm_refl. Qed.
Lemma D_5d674 : CTabKB.D W_5d674 (Store SZ8 2 1 24).
Proof. vm_refl. Qed.
Definition W_5d678 : bv 32 := 0x00813823.
Lemma F_5d678 : CTabKB.F 0x5d678 W_5d678.
Proof. vm_refl. Qed.
Lemma D_5d678 : CTabKB.D W_5d678 (Store SZ8 2 8 16).
Proof. vm_refl. Qed.
Definition W_5d67c : bv 32 := 0x00913423.
Lemma F_5d67c : CTabKB.F 0x5d67c W_5d67c.
Proof. vm_refl. Qed.
Lemma D_5d67c : CTabKB.D W_5d67c (Store SZ8 2 9 8).
Proof. vm_refl. Qed.
Definition W_5d680 : bv 32 := 0x01213023.
Lemma F_5d680 : CTabKB.F 0x5d680 W_5d680.
Proof. vm_refl. Qed.
Lemma D_5d680 : CTabKB.D W_5d680 (Store SZ8 2 18 0).
Proof. vm_refl. Qed.
Definition W_5d684 : bv 32 := 0x02010413.
Lemma F_5d684 : CTabKB.F 0x5d684 W_5d684.
Proof. vm_refl. Qed.
Lemma D_5d684 : CTabKB.D W_5d684 (OpImm ALU_ADD 8 2 32).
Proof. vm_refl. Qed.
Definition W_5d688 : bv 32 := 0x000d8517.
Lemma F_5d688 : CTabKB.F 0x5d688 W_5d688.
Proof. vm_refl. Qed.
Lemma D_5d688 : CTabKB.D W_5d688 (Auipc 10 216).
Proof. vm_refl. Qed.
Definition W_5d68c : bv 32 := 0xb1050513.
Lemma F_5d68c : CTabKB.F 0x5d68c W_5d68c.
Proof. vm_refl. Qed.
Lemma D_5d68c : CTabKB.D W_5d68c (OpImm ALU_ADD 10 10 2832).
Proof. vm_refl. Qed.
Definition W_5d690 : bv 32 := 0x6d8050ef.
Lemma F_5d690 : CTabKB.F 0x5d690 W_5d690.
Proof. vm_refl. Qed.
Lemma D_5d690 : CTabKB.D W_5d690 (Jal 1 22232).
Proof. vm_refl. Qed.
Definition W_5d694 : bv 32 := 0x00053483.
Lemma F_5d694 : CTabKB.F 0x5d694 W_5d694.
Proof. vm_refl. Qed.
Lemma D_5d694 : CTabKB.D W_5d694 (Load SZ8 true 9 10 0).
Proof. vm_refl. Qed.
Definition W_5d698 : bv 32 := 0x08048863.
Lemma F_5d698 : CTabKB.F 0x5d698 W_5d698.
Proof. vm_refl. Qed.
Lemma D_5d698 : CTabKB.D W_5d698 (Branch BC_EQ 9 0 144).
Proof. vm_refl. Qed.
Definition W_5d69c : bv 32 := 0x0604c503.
Lemma F_5d69c : CTabKB.F 0x5d69c W_5d69c.
Proof. vm_refl. Qed.
Lemma D_5d69c : CTabKB.D W_5d69c (Load SZ1 false 10 9 96).
Proof. vm_refl. Qed.
Definition W_5d6a0 : bv 32 := 0x0584b903.
Lemma F_5d6a0 : CTabKB.F 0x5d6a0 W_5d6a0.
Proof. vm_refl. Qed.
Lemma D_5d6a0 : CTabKB.D W_5d6a0 (Load SZ8 true 18 9 88).
Proof. vm_refl. Qed.
Definition W_5d6a4 : bv 32 := 0x00050863.
Lemma F_5d6a4 : CTabKB.F 0x5d6a4 W_5d6a4.
Proof. vm_refl. Qed.
Lemma D_5d6a4 : CTabKB.D W_5d6a4 (Branch BC_EQ 10 0 16).
Proof. vm_refl. Qed.
Definition W_5d6a8 : bv 32 := 0x00048513.
Lemma F_5d6a8 : CTabKB.F 0x5d6a8 W_5d6a8.
Proof. vm_refl. Qed.
Lemma D_5d6a8 : CTabKB.D W_5d6a8 (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_5d6ac : bv 32 := 0x00040593.
Lemma F_5d6ac : CTabKB.F 0x5d6ac W_5d6ac.
Proof. vm_refl. Qed.
Lemma D_5d6ac : CTabKB.D W_5d6ac (OpImm ALU_ADD 11 8 0).
Proof. vm_refl. Qed.
Definition W_5d6b0 : bv 32 := 0xa01ff0ef.
Lemma F_5d6b0 : CTabKB.F 0x5d6b0 W_5d6b0.
Proof. vm_refl. Qed.
Lemma D_5d6b0 : CTabKB.D W_5d6b0 (Jal 1 2095616).
Proof. vm_refl. Qed.
Definition W_5d6b4 : bv 32 := 0xff990593.
Lemma F_5d6b4 : CTabKB.F 0x5d6b4 W_5d6b4.
Proof. vm_refl. Qed.
Lemma D_5d6b4 : CTabKB.D W_5d6b4 (OpImm ALU_ADD 11 18 4089).
Proof. vm_refl. Qed.
Definition W_5d6b8 : bv 32 := 0x00100513.
Lemma F_5d6b8 : CTabKB.F 0x5d6b8 W_5d6b8.
Proof. vm_refl. Qed.
Lemma D_5d6b8 : CTabKB.D W_5d6b8 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_5d6bc : bv 32 := 0x00b51533.
Lemma F_5d6bc : CTabKB.F 0x5d6bc W_5d6bc.
Proof. vm_refl. Qed.
Lemma D_5d6bc : CTabKB.D W_5d6bc (Op ALU_SLL 10 10 11).
Proof. vm_refl. Qed.
Definition W_5d6c0 : bv 32 := 0x0005061b.
Lemma F_5d6c0 : CTabKB.F 0x5d6c0 W_5d6c0.
Proof. vm_refl. Qed.
Lemma D_5d6c0 : CTabKB.D W_5d6c0 (OpImm32 12 10 0).
Proof. vm_refl. Qed.
Definition W_5d6c4 : bv 32 := 0x08c05263.
Lemma F_5d6c4 : CTabKB.F 0x5d6c4 W_5d6c4.
Proof. vm_refl. Qed.
Lemma D_5d6c4 : CTabKB.D W_5d6c4 (Branch BC_GE 0 12 132).
Proof. vm_refl. Qed.
Definition W_5d6c8 : bv 32 := 0x000016b7.
Lemma F_5d6c8 : CTabKB.F 0x5d6c8 W_5d6c8.
Proof. vm_refl. Qed.
Lemma D_5d6c8 : CTabKB.D W_5d6c8 (Lui 13 1).
Proof. vm_refl. Qed.
Definition W_5d6cc : bv 32 := 0xff190613.
Lemma F_5d6cc : CTabKB.F 0x5d6cc W_5d6cc.
Proof. vm_refl. Qed.
Lemma D_5d6cc : CTabKB.D W_5d6cc (OpImm ALU_ADD 12 18 4081).
Proof. vm_refl. Qed.
Definition W_5d6d0 : bv 32 := 0x20000713.
Lemma F_5d6d0 : CTabKB.F 0x5d6d0 W_5d6d0.
Proof. vm_refl. Qed.
Lemma D_5d6d0 : CTabKB.D W_5d6d0 (OpImm ALU_ADD 14 0 512).
Proof. vm_refl. Qed.
Definition W_5d6d4 : bv 32 := 0xfff00793.
Lemma F_5d6d4 : CTabKB.F 0x5d6d4 W_5d6d4.
Proof. vm_refl. Qed.
Lemma D_5d6d4 : CTabKB.D W_5d6d4 (OpImm ALU_ADD 15 0 4095).
Proof. vm_refl. Qed.
Definition W_5d6d8 : bv 32 := 0x00c71733.
Lemma F_5d6d8 : CTabKB.F 0x5d6d8 W_5d6d8.
Proof. vm_refl. Qed.
Lemma D_5d6d8 : CTabKB.D W_5d6d8 (Op ALU_SLL 14 14 12).
Proof. vm_refl. Qed.
Definition W_5d6dc : bv 32 := 0x0084b603.
Lemma F_5d6dc : CTabKB.F 0x5d6dc W_5d6dc.
Proof. vm_refl. Qed.
Lemma D_5d6dc : CTabKB.D W_5d6dc (Load SZ8 true 12 9 8).
Proof. vm_refl. Qed.
Definition W_5d6e0 : bv 32 := 0x00b797b3.
Lemma F_5d6e0 : CTabKB.F 0x5d6e0 W_5d6e0.
Proof. vm_refl. Qed.
Lemma D_5d6e0 : CTabKB.D W_5d6e0 (Op ALU_SLL 15 15 11).
Proof. vm_refl. Qed.
Definition W_5d6e4 : bv 32 := 0xfff50813.
Lemma F_5d6e4 : CTabKB.F 0x5d6e4 W_5d6e4.
Proof. vm_refl. Qed.
Lemma D_5d6e4 : CTabKB.D W_5d6e4 (OpImm ALU_ADD 16 10 4095).
Proof. vm_refl. Qed.
Definition W_5d6e8 : bv 32 := 0x00d485b3.
Lemma F_5d6e8 : CTabKB.F 0x5d6e8 W_5d6e8.
Proof. vm_refl. Qed.
Lemma D_5d6e8 : CTabKB.D W_5d6e8 (Op ALU_ADD 11 9 13).
Proof. vm_refl. Qed.
Definition W_5d6ec : bv 32 := 0x00e586b3.
Lemma F_5d6ec : CTabKB.F 0x5d6ec W_5d6ec.
Proof. vm_refl. Qed.
Lemma D_5d6ec : CTabKB.D W_5d6ec (Op ALU_ADD 13 11 14).
Proof. vm_refl. Qed.
Definition W_5d6f0 : bv 32 := 0xfff7c713.
Lemma F_5d6f0 : CTabKB.F 0x5d6f0 W_5d6f0.
Proof. vm_refl. Qed.
Lemma D_5d6f0 : CTabKB.D W_5d6f0 (OpImm ALU_XOR 14 15 4095).
Proof. vm_refl. Qed.
Definition W_5d6f4 : bv 32 := 0x02081813.
Lemma F_5d6f4 : CTabKB.F 0x5d6f4 W_5d6f4.
Proof. vm_refl. Qed.
Lemma D_5d6f4 : CTabKB.D W_5d6f4 (ShiftImm ALU_SLL 16 16 32).
Proof. vm_refl. Qed.
Definition W_5d6f8 : bv 32 := 0x02085793.
Lemma F_5d6f8 : CTabKB.F 0x5d6f8 W_5d6f8.
Proof. vm_refl. Qed.
Lemma D_5d6f8 : CTabKB.D W_5d6f8 (ShiftImm ALU_SRL 15 16 32).
Proof. vm_refl. Qed.
Definition W_5d6fc : bv 32 := 0x00f607b3.
Lemma F_5d6fc : CTabKB.F 0x5d6fc W_5d6fc.
Proof. vm_refl. Qed.
Lemma D_5d6fc : CTabKB.D W_5d6fc (Op ALU_ADD 15 12 15).
Proof. vm_refl. Qed.
Definition W_5d700 : bv 32 := 0x00178813.
Lemma F_5d700 : CTabKB.F 0x5d700 W_5d700.
Proof. vm_refl. Qed.
Lemma D_5d700 : CTabKB.D W_5d700 (OpImm ALU_ADD 16 15 1).
Proof. vm_refl. Qed.
Definition W_5d704 : bv 32 := 0x00e678b3.
Lemma F_5d704 : CTabKB.F 0x5d704 W_5d704.
Proof. vm_refl. Qed.
Lemma D_5d704 : CTabKB.D W_5d704 (Op ALU_AND 17 12 14).
Proof. vm_refl. Qed.
Definition W_5d708 : bv 32 := 0x011687b3.
Lemma F_5d708 : CTabKB.F 0x5d708 W_5d708.
Proof. vm_refl. Qed.
Lemma D_5d708 : CTabKB.D W_5d708 (Op ALU_ADD 15 13 17).
Proof. vm_refl. Qed.
Definition W_5d70c : bv 32 := 0x0007c283.
Lemma F_5d70c : CTabKB.F 0x5d70c W_5d70c.
Proof. vm_refl. Qed.
Lemma D_5d70c : CTabKB.D W_5d70c (Load SZ1 false 5 15 0).
Proof. vm_refl. Qed.
Definition W_5d710 : bv 32 := 0x06028663.
Lemma F_5d710 : CTabKB.F 0x5d710 W_5d710.
Proof. vm_refl. Qed.
Lemma D_5d710 : CTabKB.D W_5d710 (Branch BC_EQ 5 0 108).
Proof. vm_refl. Qed.
Definition W_5d714 : bv 32 := 0xfff5051b.
Lemma F_5d714 : CTabKB.F 0x5d714 W_5d714.
Proof. vm_refl. Qed.
Lemma D_5d714 : CTabKB.D W_5d714 (OpImm32 10 10 4095).
Proof. vm_refl. Qed.
Definition W_5d718 : bv 32 := 0x00160613.
Lemma F_5d718 : CTabKB.F 0x5d718 W_5d718.
Proof. vm_refl. Qed.
Lemma D_5d718 : CTabKB.D W_5d718 (OpImm ALU_ADD 12 12 1).
Proof. vm_refl. Qed.
Definition W_5d71c : bv 32 := 0xfe0514e3.
Lemma F_5d71c : CTabKB.F 0x5d71c W_5d71c.
Proof. vm_refl. Qed.
Lemma D_5d71c : CTabKB.D W_5d71c (Branch BC_NE 10 0 8168).
Proof. vm_refl. Qed.
Definition W_5d77c : bv 32 := 0x00160613.
Lemma F_5d77c : CTabKB.F 0x5d77c W_5d77c.
Proof. vm_refl. Qed.
Lemma D_5d77c : CTabKB.D W_5d77c (OpImm ALU_ADD 12 12 1).
Proof. vm_refl. Qed.
Definition W_5d780 : bv 32 := 0x00100513.
Lemma F_5d780 : CTabKB.F 0x5d780 W_5d780.
Proof. vm_refl. Qed.
Lemma D_5d780 : CTabKB.D W_5d780 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_5d784 : bv 32 := 0xffb90693.
Lemma F_5d784 : CTabKB.F 0x5d784 W_5d784.
Proof. vm_refl. Qed.
Lemma D_5d784 : CTabKB.D W_5d784 (OpImm ALU_ADD 13 18 4091).
Proof. vm_refl. Qed.
Definition W_5d788 : bv 32 := 0x00789893.
Lemma F_5d788 : CTabKB.F 0x5d788 W_5d788.
Proof. vm_refl. Qed.
Lemma D_5d788 : CTabKB.D W_5d788 (ShiftImm ALU_SLL 17 17 7).
Proof. vm_refl. Qed.
Definition W_5d78c : bv 32 := 0x00c4b423.
Lemma F_5d78c : CTabKB.F 0x5d78c W_5d78c.
Proof. vm_refl. Qed.
Lemma D_5d78c : CTabKB.D W_5d78c (Store SZ8 9 12 8).
Proof. vm_refl. Qed.
Definition W_5d790 : bv 32 := 0x00a78023.
Lemma F_5d790 : CTabKB.F 0x5d790 W_5d790.
Proof. vm_refl. Qed.
Lemma D_5d790 : CTabKB.D W_5d790 (Store SZ1 15 10 0).
Proof. vm_refl. Qed.
Definition W_5d794 : bv 32 := 0x00d51633.
Lemma F_5d794 : CTabKB.F 0x5d794 W_5d794.
Proof. vm_refl. Qed.
Lemma D_5d794 : CTabKB.D W_5d794 (Op ALU_SLL 12 10 13).
Proof. vm_refl. Qed.
Definition W_5d798 : bv 32 := 0x01251533.
Lemma F_5d798 : CTabKB.F 0x5d798 W_5d798.
Proof. vm_refl. Qed.
Lemma D_5d798 : CTabKB.D W_5d798 (Op ALU_SLL 10 10 18).
Proof. vm_refl. Qed.
Definition W_5d79c : bv 32 := 0x00c585b3.
Lemma F_5d79c : CTabKB.F 0x5d79c W_5d79c.
Proof. vm_refl. Qed.
Lemma D_5d79c : CTabKB.D W_5d79c (Op ALU_ADD 11 11 12).
Proof. vm_refl. Qed.
Definition W_5d7a0 : bv 32 := 0x01150533.
Lemma F_5d7a0 : CTabKB.F 0x5d7a0 W_5d7a0.
Proof. vm_refl. Qed.
Lemma D_5d7a0 : CTabKB.D W_5d7a0 (Op ALU_ADD 10 10 17).
Proof. vm_refl. Qed.
Definition W_5d7a4 : bv 32 := 0x00a584b3.
Lemma F_5d7a4 : CTabKB.F 0x5d7a4 W_5d7a4.
Proof. vm_refl. Qed.
Lemma D_5d7a4 : CTabKB.D W_5d7a4 (Op ALU_ADD 9 11 10).
Proof. vm_refl. Qed.
Definition W_5d7a8 : bv 32 := 0x0084bc23.
Lemma F_5d7a8 : CTabKB.F 0x5d7a8 W_5d7a8.
Proof. vm_refl. Qed.
Lemma D_5d7a8 : CTabKB.D W_5d7a8 (Store SZ8 9 8 24).
Proof. vm_refl. Qed.
Definition W_5d7ac : bv 32 := 0x06f4bc23.
Lemma F_5d7ac : CTabKB.F 0x5d7ac W_5d7ac.
Proof. vm_refl. Qed.
Lemma D_5d7ac : CTabKB.D W_5d7ac (Store SZ8 9 15 120).
Proof. vm_refl. Qed.
Definition W_5d7b0 : bv 32 := 0x00048513.
Lemma F_5d7b0 : CTabKB.F 0x5d7b0 W_5d7b0.
Proof. vm_refl. Qed.
Lemma D_5d7b0 : CTabKB.D W_5d7b0 (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_5d7b4 : bv 32 := 0x560000ef.
Lemma F_5d7b4 : CTabKB.F 0x5d7b4 W_5d7b4.
Proof. vm_refl. Qed.
Lemma D_5d7b4 : CTabKB.D W_5d7b4 (Jal 1 1376).
Proof. vm_refl. Qed.
Definition W_5d7b8 : bv 32 := 0x00050593.
Lemma F_5d7b8 : CTabKB.F 0x5d7b8 W_5d7b8.
Proof. vm_refl. Qed.
Lemma D_5d7b8 : CTabKB.D W_5d7b8 (OpImm ALU_ADD 11 10 0).
Proof. vm_refl. Qed.
Definition W_5d7bc : bv 32 := 0x00048513.
Lemma F_5d7bc : CTabKB.F 0x5d7bc W_5d7bc.
Proof. vm_refl. Qed.
Lemma D_5d7bc : CTabKB.D W_5d7bc (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_5d7c0 : bv 32 := 0x00000613.
Lemma F_5d7c0 : CTabKB.F 0x5d7c0 W_5d7c0.
Proof. vm_refl. Qed.
Lemma D_5d7c0 : CTabKB.D W_5d7c0 (OpImm ALU_ADD 12 0 0).
Proof. vm_refl. Qed.
Definition W_5d7c4 : bv 32 := 0x0005b023.
Lemma F_5d7c4 : CTabKB.F 0x5d7c4 W_5d7c4.
Proof. vm_refl. Qed.
Lemma D_5d7c4 : CTabKB.D W_5d7c4 (Store SZ8 11 0 0).
Proof. vm_refl. Qed.
Definition W_5d7c8 : bv 32 := 0x0005b423.
Lemma F_5d7c8 : CTabKB.F 0x5d7c8 W_5d7c8.
Proof. vm_refl. Qed.
Lemma D_5d7c8 : CTabKB.D W_5d7c8 (Store SZ8 11 0 8).
Proof. vm_refl. Qed.
Definition W_5d7cc : bv 32 := 0x01813083.
Lemma F_5d7cc : CTabKB.F 0x5d7cc W_5d7cc.
Proof. vm_refl. Qed.
Lemma D_5d7cc : CTabKB.D W_5d7cc (Load SZ8 true 1 2 24).
Proof. vm_refl. Qed.
Definition W_5d7d0 : bv 32 := 0x01013403.
Lemma F_5d7d0 : CTabKB.F 0x5d7d0 W_5d7d0.
Proof. vm_refl. Qed.
Lemma D_5d7d0 : CTabKB.D W_5d7d0 (Load SZ8 true 8 2 16).
Proof. vm_refl. Qed.
Definition W_5d7d4 : bv 32 := 0x00813483.
Lemma F_5d7d4 : CTabKB.F 0x5d7d4 W_5d7d4.
Proof. vm_refl. Qed.
Lemma D_5d7d4 : CTabKB.D W_5d7d4 (Load SZ8 true 9 2 8).
Proof. vm_refl. Qed.
Definition W_5d7d8 : bv 32 := 0x00013903.
Lemma F_5d7d8 : CTabKB.F 0x5d7d8 W_5d7d8.
Proof. vm_refl. Qed.
Lemma D_5d7d8 : CTabKB.D W_5d7d8 (Load SZ8 true 18 2 0).
Proof. vm_refl. Qed.
Definition W_5d7dc : bv 32 := 0x02010113.
Lemma F_5d7dc : CTabKB.F 0x5d7dc W_5d7dc.
Proof. vm_refl. Qed.
Lemma D_5d7dc : CTabKB.D W_5d7dc (OpImm ALU_ADD 2 2 32).
Proof. vm_refl. Qed.
Definition W_5d7e0 : bv 32 := 0x00008067.
Lemma F_5d7e0 : CTabKB.F 0x5d7e0 W_5d7e0.
Proof. vm_refl. Qed.
Lemma D_5d7e0 : CTabKB.D W_5d7e0 (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_5d800 : bv 32 := 0xfe010113.
Lemma F_5d800 : CTabKB.F 0x5d800 W_5d800.
Proof. vm_refl. Qed.
Lemma D_5d800 : CTabKB.D W_5d800 (OpImm ALU_ADD 2 2 4064).
Proof. vm_refl. Qed.
Definition W_5d804 : bv 32 := 0x00113c23.
Lemma F_5d804 : CTabKB.F 0x5d804 W_5d804.
Proof. vm_refl. Qed.
Lemma D_5d804 : CTabKB.D W_5d804 (Store SZ8 2 1 24).
Proof. vm_refl. Qed.
Definition W_5d808 : bv 32 := 0x00813823.
Lemma F_5d808 : CTabKB.F 0x5d808 W_5d808.
Proof. vm_refl. Qed.
Lemma D_5d808 : CTabKB.D W_5d808 (Store SZ8 2 8 16).
Proof. vm_refl. Qed.
Definition W_5d80c : bv 32 := 0x00913423.
Lemma F_5d80c : CTabKB.F 0x5d80c W_5d80c.
Proof. vm_refl. Qed.
Lemma D_5d80c : CTabKB.D W_5d80c (Store SZ8 2 9 8).
Proof. vm_refl. Qed.
Definition W_5d810 : bv 32 := 0x01213023.
Lemma F_5d810 : CTabKB.F 0x5d810 W_5d810.
Proof. vm_refl. Qed.
Lemma D_5d810 : CTabKB.D W_5d810 (Store SZ8 2 18 0).
Proof. vm_refl. Qed.
Definition W_5d814 : bv 32 := 0x02010413.
Lemma F_5d814 : CTabKB.F 0x5d814 W_5d814.
Proof. vm_refl. Qed.
Lemma D_5d814 : CTabKB.D W_5d814 (OpImm ALU_ADD 8 2 32).
Proof. vm_refl. Qed.
Definition W_5d818 : bv 32 := 0x000d8517.
Lemma F_5d818 : CTabKB.F 0x5d818 W_5d818.
Proof. vm_refl. Qed.
Lemma D_5d818 : CTabKB.D W_5d818 (Auipc 10 216).
Proof. vm_refl. Qed.
Definition W_5d81c : bv 32 := 0x98050513.
Lemma F_5d81c : CTabKB.F 0x5d81c W_5d81c.
Proof. vm_refl. Qed.
Lemma D_5d81c : CTabKB.D W_5d81c (OpImm ALU_ADD 10 10 2432).
Proof. vm_refl. Qed.
Definition W_5d820 : bv 32 := 0x548050ef.
Lemma F_5d820 : CTabKB.F 0x5d820 W_5d820.
Proof. vm_refl. Qed.
Lemma D_5d820 : CTabKB.D W_5d820 (Jal 1 21832).
Proof. vm_refl. Qed.
Definition W_5d824 : bv 32 := 0x00053483.
Lemma F_5d824 : CTabKB.F 0x5d824 W_5d824.
Proof. vm_refl. Qed.
Lemma D_5d824 : CTabKB.D W_5d824 (Load SZ8 true 9 10 0).
Proof. vm_refl. Qed.
Definition W_5d828 : bv 32 := 0x08048863.
Lemma F_5d828 : CTabKB.F 0x5d828 W_5d828.
Proof. vm_refl. Qed.
Lemma D_5d828 : CTabKB.D W_5d828 (Branch BC_EQ 9 0 144).
Proof. vm_refl. Qed.
Definition W_5d82c : bv 32 := 0x0604c503.
Lemma F_5d82c : CTabKB.F 0x5d82c W_5d82c.
Proof. vm_refl. Qed.
Lemma D_5d82c : CTabKB.D W_5d82c (Load SZ1 false 10 9 96).
Proof. vm_refl. Qed.
Definition W_5d830 : bv 32 := 0x0584b903.
Lemma F_5d830 : CTabKB.F 0x5d830 W_5d830.
Proof. vm_refl. Qed.
Lemma D_5d830 : CTabKB.D W_5d830 (Load SZ8 true 18 9 88).
Proof. vm_refl. Qed.
Definition W_5d834 : bv 32 := 0x00050863.
Lemma F_5d834 : CTabKB.F 0x5d834 W_5d834.
Proof. vm_refl. Qed.
Lemma D_5d834 : CTabKB.D W_5d834 (Branch BC_EQ 10 0 16).
Proof. vm_refl. Qed.
Definition W_5d838 : bv 32 := 0x00048513.
Lemma F_5d838 : CTabKB.F 0x5d838 W_5d838.
Proof. vm_refl. Qed.
Lemma D_5d838 : CTabKB.D W_5d838 (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_5d83c : bv 32 := 0x00040593.
Lemma F_5d83c : CTabKB.F 0x5d83c W_5d83c.
Proof. vm_refl. Qed.
Lemma D_5d83c : CTabKB.D W_5d83c (OpImm ALU_ADD 11 8 0).
Proof. vm_refl. Qed.
Definition W_5d840 : bv 32 := 0x871ff0ef.
Lemma F_5d840 : CTabKB.F 0x5d840 W_5d840.
Proof. vm_refl. Qed.
Lemma D_5d840 : CTabKB.D W_5d840 (Jal 1 2095216).
Proof. vm_refl. Qed.
Definition W_5d844 : bv 32 := 0xff890593.
Lemma F_5d844 : CTabKB.F 0x5d844 W_5d844.
Proof. vm_refl. Qed.
Lemma D_5d844 : CTabKB.D W_5d844 (OpImm ALU_ADD 11 18 4088).
Proof. vm_refl. Qed.
Definition W_5d848 : bv 32 := 0x00100513.
Lemma F_5d848 : CTabKB.F 0x5d848 W_5d848.
Proof. vm_refl. Qed.
Lemma D_5d848 : CTabKB.D W_5d848 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_5d84c : bv 32 := 0x00b51533.
Lemma F_5d84c : CTabKB.F 0x5d84c W_5d84c.
Proof. vm_refl. Qed.
Lemma D_5d84c : CTabKB.D W_5d84c (Op ALU_SLL 10 10 11).
Proof. vm_refl. Qed.
Definition W_5d850 : bv 32 := 0x0005061b.
Lemma F_5d850 : CTabKB.F 0x5d850 W_5d850.
Proof. vm_refl. Qed.
Lemma D_5d850 : CTabKB.D W_5d850 (OpImm32 12 10 0).
Proof. vm_refl. Qed.
Definition W_5d854 : bv 32 := 0x08c05263.
Lemma F_5d854 : CTabKB.F 0x5d854 W_5d854.
Proof. vm_refl. Qed.
Lemma D_5d854 : CTabKB.D W_5d854 (Branch BC_GE 0 12 132).
Proof. vm_refl. Qed.
Definition W_5d858 : bv 32 := 0x000016b7.
Lemma F_5d858 : CTabKB.F 0x5d858 W_5d858.
Proof. vm_refl. Qed.
Lemma D_5d858 : CTabKB.D W_5d858 (Lui 13 1).
Proof. vm_refl. Qed.
Definition W_5d85c : bv 32 := 0xff190613.
Lemma F_5d85c : CTabKB.F 0x5d85c W_5d85c.
Proof. vm_refl. Qed.
Lemma D_5d85c : CTabKB.D W_5d85c (OpImm ALU_ADD 12 18 4081).
Proof. vm_refl. Qed.
Definition W_5d860 : bv 32 := 0x30000713.
Lemma F_5d860 : CTabKB.F 0x5d860 W_5d860.
Proof. vm_refl. Qed.
Lemma D_5d860 : CTabKB.D W_5d860 (OpImm ALU_ADD 14 0 768).
Proof. vm_refl. Qed.
Definition W_5d864 : bv 32 := 0xfff00793.
Lemma F_5d864 : CTabKB.F 0x5d864 W_5d864.
Proof. vm_refl. Qed.
Lemma D_5d864 : CTabKB.D W_5d864 (OpImm ALU_ADD 15 0 4095).
Proof. vm_refl. Qed.
Definition W_5d868 : bv 32 := 0x00c71733.
Lemma F_5d868 : CTabKB.F 0x5d868 W_5d868.
Proof. vm_refl. Qed.
Lemma D_5d868 : CTabKB.D W_5d868 (Op ALU_SLL 14 14 12).
Proof. vm_refl. Qed.
Definition W_5d86c : bv 32 := 0x0104b603.
Lemma F_5d86c : CTabKB.F 0x5d86c W_5d86c.
Proof. vm_refl. Qed.
Lemma D_5d86c : CTabKB.D W_5d86c (Load SZ8 true 12 9 16).
Proof. vm_refl. Qed.
Definition W_5d870 : bv 32 := 0x00b797b3.
Lemma F_5d870 : CTabKB.F 0x5d870 W_5d870.
Proof. vm_refl. Qed.
Lemma D_5d870 : CTabKB.D W_5d870 (Op ALU_SLL 15 15 11).
Proof. vm_refl. Qed.
Definition W_5d874 : bv 32 := 0xfff50813.
Lemma F_5d874 : CTabKB.F 0x5d874 W_5d874.
Proof. vm_refl. Qed.
Lemma D_5d874 : CTabKB.D W_5d874 (OpImm ALU_ADD 16 10 4095).
Proof. vm_refl. Qed.
Definition W_5d878 : bv 32 := 0x00d485b3.
Lemma F_5d878 : CTabKB.F 0x5d878 W_5d878.
Proof. vm_refl. Qed.
Lemma D_5d878 : CTabKB.D W_5d878 (Op ALU_ADD 11 9 13).
Proof. vm_refl. Qed.
Definition W_5d87c : bv 32 := 0x00e586b3.
Lemma F_5d87c : CTabKB.F 0x5d87c W_5d87c.
Proof. vm_refl. Qed.
Lemma D_5d87c : CTabKB.D W_5d87c (Op ALU_ADD 13 11 14).
Proof. vm_refl. Qed.
Definition W_5d880 : bv 32 := 0xfff7c713.
Lemma F_5d880 : CTabKB.F 0x5d880 W_5d880.
Proof. vm_refl. Qed.
Lemma D_5d880 : CTabKB.D W_5d880 (OpImm ALU_XOR 14 15 4095).
Proof. vm_refl. Qed.
Definition W_5d884 : bv 32 := 0x02081813.
Lemma F_5d884 : CTabKB.F 0x5d884 W_5d884.
Proof. vm_refl. Qed.
Lemma D_5d884 : CTabKB.D W_5d884 (ShiftImm ALU_SLL 16 16 32).
Proof. vm_refl. Qed.
Definition W_5d888 : bv 32 := 0x02085793.
Lemma F_5d888 : CTabKB.F 0x5d888 W_5d888.
Proof. vm_refl. Qed.
Lemma D_5d888 : CTabKB.D W_5d888 (ShiftImm ALU_SRL 15 16 32).
Proof. vm_refl. Qed.
Definition W_5d88c : bv 32 := 0x00f607b3.
Lemma F_5d88c : CTabKB.F 0x5d88c W_5d88c.
Proof. vm_refl. Qed.
Lemma D_5d88c : CTabKB.D W_5d88c (Op ALU_ADD 15 12 15).
Proof. vm_refl. Qed.
Definition W_5d890 : bv 32 := 0x00178813.
Lemma F_5d890 : CTabKB.F 0x5d890 W_5d890.
Proof. vm_refl. Qed.
Lemma D_5d890 : CTabKB.D W_5d890 (OpImm ALU_ADD 16 15 1).
Proof. vm_refl. Qed.
Definition W_5d894 : bv 32 := 0x00e678b3.
Lemma F_5d894 : CTabKB.F 0x5d894 W_5d894.
Proof. vm_refl. Qed.
Lemma D_5d894 : CTabKB.D W_5d894 (Op ALU_AND 17 12 14).
Proof. vm_refl. Qed.
Definition W_5d898 : bv 32 := 0x011687b3.
Lemma F_5d898 : CTabKB.F 0x5d898 W_5d898.
Proof. vm_refl. Qed.
Lemma D_5d898 : CTabKB.D W_5d898 (Op ALU_ADD 15 13 17).
Proof. vm_refl. Qed.
Definition W_5d89c : bv 32 := 0x0007c283.
Lemma F_5d89c : CTabKB.F 0x5d89c W_5d89c.
Proof. vm_refl. Qed.
Lemma D_5d89c : CTabKB.D W_5d89c (Load SZ1 false 5 15 0).
Proof. vm_refl. Qed.
Definition W_5d8a0 : bv 32 := 0x06028663.
Lemma F_5d8a0 : CTabKB.F 0x5d8a0 W_5d8a0.
Proof. vm_refl. Qed.
Lemma D_5d8a0 : CTabKB.D W_5d8a0 (Branch BC_EQ 5 0 108).
Proof. vm_refl. Qed.
Definition W_5d8a4 : bv 32 := 0xfff5051b.
Lemma F_5d8a4 : CTabKB.F 0x5d8a4 W_5d8a4.
Proof. vm_refl. Qed.
Lemma D_5d8a4 : CTabKB.D W_5d8a4 (OpImm32 10 10 4095).
Proof. vm_refl. Qed.
Definition W_5d8a8 : bv 32 := 0x00160613.
Lemma F_5d8a8 : CTabKB.F 0x5d8a8 W_5d8a8.
Proof. vm_refl. Qed.
Lemma D_5d8a8 : CTabKB.D W_5d8a8 (OpImm ALU_ADD 12 12 1).
Proof. vm_refl. Qed.
Definition W_5d8ac : bv 32 := 0xfe0514e3.
Lemma F_5d8ac : CTabKB.F 0x5d8ac W_5d8ac.
Proof. vm_refl. Qed.
Lemma D_5d8ac : CTabKB.D W_5d8ac (Branch BC_NE 10 0 8168).
Proof. vm_refl. Qed.
Definition W_5d90c : bv 32 := 0x00160613.
Lemma F_5d90c : CTabKB.F 0x5d90c W_5d90c.
Proof. vm_refl. Qed.
Lemma D_5d90c : CTabKB.D W_5d90c (OpImm ALU_ADD 12 12 1).
Proof. vm_refl. Qed.
Definition W_5d910 : bv 32 := 0x00100513.
Lemma F_5d910 : CTabKB.F 0x5d910 W_5d910.
Proof. vm_refl. Qed.
Lemma D_5d910 : CTabKB.D W_5d910 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_5d914 : bv 32 := 0xffb90693.
Lemma F_5d914 : CTabKB.F 0x5d914 W_5d914.
Proof. vm_refl. Qed.
Lemma D_5d914 : CTabKB.D W_5d914 (OpImm ALU_ADD 13 18 4091).
Proof. vm_refl. Qed.
Definition W_5d918 : bv 32 := 0x00c4b823.
Lemma F_5d918 : CTabKB.F 0x5d918 W_5d918.
Proof. vm_refl. Qed.
Lemma D_5d918 : CTabKB.D W_5d918 (Store SZ8 9 12 16).
Proof. vm_refl. Qed.
Definition W_5d91c : bv 32 := 0x00a78023.
Lemma F_5d91c : CTabKB.F 0x5d91c W_5d91c.
Proof. vm_refl. Qed.
Lemma D_5d91c : CTabKB.D W_5d91c (Store SZ1 15 10 0).
Proof. vm_refl. Qed.
Definition W_5d920 : bv 32 := 0x00d51533.
Lemma F_5d920 : CTabKB.F 0x5d920 W_5d920.
Proof. vm_refl. Qed.
Lemma D_5d920 : CTabKB.D W_5d920 (Op ALU_SLL 10 10 13).
Proof. vm_refl. Qed.
Definition W_5d924 : bv 32 := 0x00200613.
Lemma F_5d924 : CTabKB.F 0x5d924 W_5d924.
Proof. vm_refl. Qed.
Lemma D_5d924 : CTabKB.D W_5d924 (OpImm ALU_ADD 12 0 2).
Proof. vm_refl. Qed.
Definition W_5d928 : bv 32 := 0x00889893.
Lemma F_5d928 : CTabKB.F 0x5d928 W_5d928.
Proof. vm_refl. Qed.
Lemma D_5d928 : CTabKB.D W_5d928 (ShiftImm ALU_SLL 17 17 8).
Proof. vm_refl. Qed.
Definition W_5d92c : bv 32 := 0x01261633.
Lemma F_5d92c : CTabKB.F 0x5d92c W_5d92c.
Proof. vm_refl. Qed.
Lemma D_5d92c : CTabKB.D W_5d92c (Op ALU_SLL 12 12 18).
Proof. vm_refl. Qed.
Definition W_5d930 : bv 32 := 0x00a58533.
Lemma F_5d930 : CTabKB.F 0x5d930 W_5d930.
Proof. vm_refl. Qed.
Lemma D_5d930 : CTabKB.D W_5d930 (Op ALU_ADD 10 11 10).
Proof. vm_refl. Qed.
Definition W_5d934 : bv 32 := 0x01160633.
Lemma F_5d934 : CTabKB.F 0x5d934 W_5d934.
Proof. vm_refl. Qed.
Lemma D_5d934 : CTabKB.D W_5d934 (Op ALU_ADD 12 12 17).
Proof. vm_refl. Qed.
Definition W_5d938 : bv 32 := 0x00c504b3.
Lemma F_5d938 : CTabKB.F 0x5d938 W_5d938.
Proof. vm_refl. Qed.
Lemma D_5d938 : CTabKB.D W_5d938 (Op ALU_ADD 9 10 12).
Proof. vm_refl. Qed.
Definition W_5d93c : bv 32 := 0x0084bc23.
Lemma F_5d93c : CTabKB.F 0x5d93c W_5d93c.
Proof. vm_refl. Qed.
Lemma D_5d93c : CTabKB.D W_5d93c (Store SZ8 9 8 24).
Proof. vm_refl. Qed.
Definition W_5d940 : bv 32 := 0x0ef4bc23.
Lemma F_5d940 : CTabKB.F 0x5d940 W_5d940.
Proof. vm_refl. Qed.
Lemma D_5d940 : CTabKB.D W_5d940 (Store SZ8 9 15 248).
Proof. vm_refl. Qed.
Definition W_5d944 : bv 32 := 0x00048513.
Lemma F_5d944 : CTabKB.F 0x5d944 W_5d944.
Proof. vm_refl. Qed.
Lemma D_5d944 : CTabKB.D W_5d944 (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_5d948 : bv 32 := 0x3cc000ef.
Lemma F_5d948 : CTabKB.F 0x5d948 W_5d948.
Proof. vm_refl. Qed.
Lemma D_5d948 : CTabKB.D W_5d948 (Jal 1 972).
Proof. vm_refl. Qed.
Definition W_5d94c : bv 32 := 0x00050593.
Lemma F_5d94c : CTabKB.F 0x5d94c W_5d94c.
Proof. vm_refl. Qed.
Lemma D_5d94c : CTabKB.D W_5d94c (OpImm ALU_ADD 11 10 0).
Proof. vm_refl. Qed.
Definition W_5d950 : bv 32 := 0x00048513.
Lemma F_5d950 : CTabKB.F 0x5d950 W_5d950.
Proof. vm_refl. Qed.
Lemma D_5d950 : CTabKB.D W_5d950 (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_5d954 : bv 32 := 0x00000613.
Lemma F_5d954 : CTabKB.F 0x5d954 W_5d954.
Proof. vm_refl. Qed.
Lemma D_5d954 : CTabKB.D W_5d954 (OpImm ALU_ADD 12 0 0).
Proof. vm_refl. Qed.
Definition W_5d958 : bv 32 := 0x0005b023.
Lemma F_5d958 : CTabKB.F 0x5d958 W_5d958.
Proof. vm_refl. Qed.
Lemma D_5d958 : CTabKB.D W_5d958 (Store SZ8 11 0 0).
Proof. vm_refl. Qed.
Definition W_5d95c : bv 32 := 0x0005b423.
Lemma F_5d95c : CTabKB.F 0x5d95c W_5d95c.
Proof. vm_refl. Qed.
Lemma D_5d95c : CTabKB.D W_5d95c (Store SZ8 11 0 8).
Proof. vm_refl. Qed.
Definition W_5d960 : bv 32 := 0x0005b823.
Lemma F_5d960 : CTabKB.F 0x5d960 W_5d960.
Proof. vm_refl. Qed.
Lemma D_5d960 : CTabKB.D W_5d960 (Store SZ8 11 0 16).
Proof. vm_refl. Qed.
Definition W_5d964 : bv 32 := 0x0005bc23.
Lemma F_5d964 : CTabKB.F 0x5d964 W_5d964.
Proof. vm_refl. Qed.
Lemma D_5d964 : CTabKB.D W_5d964 (Store SZ8 11 0 24).
Proof. vm_refl. Qed.
Definition W_5d968 : bv 32 := 0x01813083.
Lemma F_5d968 : CTabKB.F 0x5d968 W_5d968.
Proof. vm_refl. Qed.
Lemma D_5d968 : CTabKB.D W_5d968 (Load SZ8 true 1 2 24).
Proof. vm_refl. Qed.
Definition W_5d96c : bv 32 := 0x01013403.
Lemma F_5d96c : CTabKB.F 0x5d96c W_5d96c.
Proof. vm_refl. Qed.
Lemma D_5d96c : CTabKB.D W_5d96c (Load SZ8 true 8 2 16).
Proof. vm_refl. Qed.
Definition W_5d970 : bv 32 := 0x00813483.
Lemma F_5d970 : CTabKB.F 0x5d970 W_5d970.
Proof. vm_refl. Qed.
Lemma D_5d970 : CTabKB.D W_5d970 (Load SZ8 true 9 2 8).
Proof. vm_refl. Qed.
Definition W_5d974 : bv 32 := 0x00013903.
Lemma F_5d974 : CTabKB.F 0x5d974 W_5d974.
Proof. vm_refl. Qed.
Lemma D_5d974 : CTabKB.D W_5d974 (Load SZ8 true 18 2 0).
Proof. vm_refl. Qed.
Definition W_5d978 : bv 32 := 0x02010113.
Lemma F_5d978 : CTabKB.F 0x5d978 W_5d978.
Proof. vm_refl. Qed.
Lemma D_5d978 : CTabKB.D W_5d978 (OpImm ALU_ADD 2 2 32).
Proof. vm_refl. Qed.
Definition W_5d97c : bv 32 := 0x00008067.
Lemma F_5d97c : CTabKB.F 0x5d97c W_5d97c.
Proof. vm_refl. Qed.
Lemma D_5d97c : CTabKB.D W_5d97c (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_5d99c : bv 32 := 0xfe010113.
Lemma F_5d99c : CTabKB.F 0x5d99c W_5d99c.
Proof. vm_refl. Qed.
Lemma D_5d99c : CTabKB.D W_5d99c (OpImm ALU_ADD 2 2 4064).
Proof. vm_refl. Qed.
Definition W_5d9a0 : bv 32 := 0x00113c23.
Lemma F_5d9a0 : CTabKB.F 0x5d9a0 W_5d9a0.
Proof. vm_refl. Qed.
Lemma D_5d9a0 : CTabKB.D W_5d9a0 (Store SZ8 2 1 24).
Proof. vm_refl. Qed.
Definition W_5d9a4 : bv 32 := 0x00813823.
Lemma F_5d9a4 : CTabKB.F 0x5d9a4 W_5d9a4.
Proof. vm_refl. Qed.
Lemma D_5d9a4 : CTabKB.D W_5d9a4 (Store SZ8 2 8 16).
Proof. vm_refl. Qed.
Definition W_5d9a8 : bv 32 := 0x00913423.
Lemma F_5d9a8 : CTabKB.F 0x5d9a8 W_5d9a8.
Proof. vm_refl. Qed.
Lemma D_5d9a8 : CTabKB.D W_5d9a8 (Store SZ8 2 9 8).
Proof. vm_refl. Qed.
Definition W_5d9ac : bv 32 := 0x01213023.
Lemma F_5d9ac : CTabKB.F 0x5d9ac W_5d9ac.
Proof. vm_refl. Qed.
Lemma D_5d9ac : CTabKB.D W_5d9ac (Store SZ8 2 18 0).
Proof. vm_refl. Qed.
Definition W_5d9b0 : bv 32 := 0x02010413.
Lemma F_5d9b0 : CTabKB.F 0x5d9b0 W_5d9b0.
Proof. vm_refl. Qed.
Lemma D_5d9b0 : CTabKB.D W_5d9b0 (OpImm ALU_ADD 8 2 32).
Proof. vm_refl. Qed.
Definition W_5d9b4 : bv 32 := 0x000d7517.
Lemma F_5d9b4 : CTabKB.F 0x5d9b4 W_5d9b4.
Proof. vm_refl. Qed.
Lemma D_5d9b4 : CTabKB.D W_5d9b4 (Auipc 10 215).
Proof. vm_refl. Qed.
Definition W_5d9b8 : bv 32 := 0x7e450513.
Lemma F_5d9b8 : CTabKB.F 0x5d9b8 W_5d9b8.
Proof. vm_refl. Qed.
Lemma D_5d9b8 : CTabKB.D W_5d9b8 (OpImm ALU_ADD 10 10 2020).
Proof. vm_refl. Qed.
Definition W_5d9bc : bv 32 := 0x3ac050ef.
Lemma F_5d9bc : CTabKB.F 0x5d9bc W_5d9bc.
Proof. vm_refl. Qed.
Lemma D_5d9bc : CTabKB.D W_5d9bc (Jal 1 21420).
Proof. vm_refl. Qed.
Definition W_5d9c0 : bv 32 := 0x00053483.
Lemma F_5d9c0 : CTabKB.F 0x5d9c0 W_5d9c0.
Proof. vm_refl. Qed.
Lemma D_5d9c0 : CTabKB.D W_5d9c0 (Load SZ8 true 9 10 0).
Proof. vm_refl. Qed.
Definition W_5d9c4 : bv 32 := 0x08048863.
Lemma F_5d9c4 : CTabKB.F 0x5d9c4 W_5d9c4.
Proof. vm_refl. Qed.
Lemma D_5d9c4 : CTabKB.D W_5d9c4 (Branch BC_EQ 9 0 144).
Proof. vm_refl. Qed.
Definition W_5d9c8 : bv 32 := 0x0604c503.
Lemma F_5d9c8 : CTabKB.F 0x5d9c8 W_5d9c8.
Proof. vm_refl. Qed.
Lemma D_5d9c8 : CTabKB.D W_5d9c8 (Load SZ1 false 10 9 96).
Proof. vm_refl. Qed.
Definition W_5d9cc : bv 32 := 0x0584b903.
Lemma F_5d9cc : CTabKB.F 0x5d9cc W_5d9cc.
Proof. vm_refl. Qed.
Lemma D_5d9cc : CTabKB.D W_5d9cc (Load SZ8 true 18 9 88).
Proof. vm_refl. Qed.
Definition W_5d9d0 : bv 32 := 0x00050863.
Lemma F_5d9d0 : CTabKB.F 0x5d9d0 W_5d9d0.
Proof. vm_refl. Qed.
Lemma D_5d9d0 : CTabKB.D W_5d9d0 (Branch BC_EQ 10 0 16).
Proof. vm_refl. Qed.
Definition W_5d9d4 : bv 32 := 0x00048513.
Lemma F_5d9d4 : CTabKB.F 0x5d9d4 W_5d9d4.
Proof. vm_refl. Qed.
Lemma D_5d9d4 : CTabKB.D W_5d9d4 (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_5d9d8 : bv 32 := 0x00040593.
Lemma F_5d9d8 : CTabKB.F 0x5d9d8 W_5d9d8.
Proof. vm_refl. Qed.
Lemma D_5d9d8 : CTabKB.D W_5d9d8 (OpImm ALU_ADD 11 8 0).
Proof. vm_refl. Qed.
Definition W_5d9dc : bv 32 := 0xed4ff0ef.
Lemma F_5d9dc : CTabKB.F 0x5d9dc W_5d9dc.
Proof. vm_refl. Qed.
Lemma D_5d9dc : CTabKB.D W_5d9dc (Jal 1 2094804).
Proof. vm_refl. Qed.
Definition W_5d9e0 : bv 32 := 0xff790593.
Lemma F_5d9e0 : CTabKB.F 0x5d9e0 W_5d9e0.
Proof. vm_refl. Qed.
Lemma D_5d9e0 : CTabKB.D W_5d9e0 (OpImm ALU_ADD 11 18 4087).
Proof. vm_refl. Qed.
Definition W_5d9e4 : bv 32 := 0x00100513.
Lemma F_5d9e4 : CTabKB.F 0x5d9e4 W_5d9e4.
Proof. vm_refl. Qed.
Lemma D_5d9e4 : CTabKB.D W_5d9e4 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_5d9e8 : bv 32 := 0x00b51533.
Lemma F_5d9e8 : CTabKB.F 0x5d9e8 W_5d9e8.
Proof. vm_refl. Qed.
Lemma D_5d9e8 : CTabKB.D W_5d9e8 (Op ALU_SLL 10 10 11).
Proof. vm_refl. Qed.
Definition W_5d9ec : bv 32 := 0x0005061b.
Lemma F_5d9ec : CTabKB.F 0x5d9ec W_5d9ec.
Proof. vm_refl. Qed.
Lemma D_5d9ec : CTabKB.D W_5d9ec (OpImm32 12 10 0).
Proof. vm_refl. Qed.
Definition W_5d9f0 : bv 32 := 0x08c05263.
Lemma F_5d9f0 : CTabKB.F 0x5d9f0 W_5d9f0.
Proof. vm_refl. Qed.
Lemma D_5d9f0 : CTabKB.D W_5d9f0 (Branch BC_GE 0 12 132).
Proof. vm_refl. Qed.
Definition W_5d9f4 : bv 32 := 0x000016b7.
Lemma F_5d9f4 : CTabKB.F 0x5d9f4 W_5d9f4.
Proof. vm_refl. Qed.
Lemma D_5d9f4 : CTabKB.D W_5d9f4 (Lui 13 1).
Proof. vm_refl. Qed.
Definition W_5d9f8 : bv 32 := 0xff190613.
Lemma F_5d9f8 : CTabKB.F 0x5d9f8 W_5d9f8.
Proof. vm_refl. Qed.
Lemma D_5d9f8 : CTabKB.D W_5d9f8 (OpImm ALU_ADD 12 18 4081).
Proof. vm_refl. Qed.
Definition W_5d9fc : bv 32 := 0x38000713.
Lemma F_5d9fc : CTabKB.F 0x5d9fc W_5d9fc.
Proof. vm_refl. Qed.
Lemma D_5d9fc : CTabKB.D W_5d9fc (OpImm ALU_ADD 14 0 896).
Proof. vm_refl. Qed.
Definition W_5da00 : bv 32 := 0xfff00793.
Lemma F_5da00 : CTabKB.F 0x5da00 W_5da00.
Proof. vm_refl. Qed.
Lemma D_5da00 : CTabKB.D W_5da00 (OpImm ALU_ADD 15 0 4095).
Proof. vm_refl. Qed.
Definition W_5da04 : bv 32 := 0x00c71733.
Lemma F_5da04 : CTabKB.F 0x5da04 W_5da04.
Proof. vm_refl. Qed.
Lemma D_5da04 : CTabKB.D W_5da04 (Op ALU_SLL 14 14 12).
Proof. vm_refl. Qed.
Definition W_5da08 : bv 32 := 0x0184b603.
Lemma F_5da08 : CTabKB.F 0x5da08 W_5da08.
Proof. vm_refl. Qed.
Lemma D_5da08 : CTabKB.D W_5da08 (Load SZ8 true 12 9 24).
Proof. vm_refl. Qed.
Definition W_5da0c : bv 32 := 0x00b797b3.
Lemma F_5da0c : CTabKB.F 0x5da0c W_5da0c.
Proof. vm_refl. Qed.
Lemma D_5da0c : CTabKB.D W_5da0c (Op ALU_SLL 15 15 11).
Proof. vm_refl. Qed.
Definition W_5da10 : bv 32 := 0xfff50813.
Lemma F_5da10 : CTabKB.F 0x5da10 W_5da10.
Proof. vm_refl. Qed.
Lemma D_5da10 : CTabKB.D W_5da10 (OpImm ALU_ADD 16 10 4095).
Proof. vm_refl. Qed.
Definition W_5da14 : bv 32 := 0x00d485b3.
Lemma F_5da14 : CTabKB.F 0x5da14 W_5da14.
Proof. vm_refl. Qed.
Lemma D_5da14 : CTabKB.D W_5da14 (Op ALU_ADD 11 9 13).
Proof. vm_refl. Qed.
Definition W_5da18 : bv 32 := 0x00e586b3.
Lemma F_5da18 : CTabKB.F 0x5da18 W_5da18.
Proof. vm_refl. Qed.
Lemma D_5da18 : CTabKB.D W_5da18 (Op ALU_ADD 13 11 14).
Proof. vm_refl. Qed.
Definition W_5da1c : bv 32 := 0xfff7c713.
Lemma F_5da1c : CTabKB.F 0x5da1c W_5da1c.
Proof. vm_refl. Qed.
Lemma D_5da1c : CTabKB.D W_5da1c (OpImm ALU_XOR 14 15 4095).
Proof. vm_refl. Qed.
Definition W_5da20 : bv 32 := 0x02081813.
Lemma F_5da20 : CTabKB.F 0x5da20 W_5da20.
Proof. vm_refl. Qed.
Lemma D_5da20 : CTabKB.D W_5da20 (ShiftImm ALU_SLL 16 16 32).
Proof. vm_refl. Qed.
Definition W_5da24 : bv 32 := 0x02085793.
Lemma F_5da24 : CTabKB.F 0x5da24 W_5da24.
Proof. vm_refl. Qed.
Lemma D_5da24 : CTabKB.D W_5da24 (ShiftImm ALU_SRL 15 16 32).
Proof. vm_refl. Qed.
Definition W_5da28 : bv 32 := 0x00f607b3.
Lemma F_5da28 : CTabKB.F 0x5da28 W_5da28.
Proof. vm_refl. Qed.
Lemma D_5da28 : CTabKB.D W_5da28 (Op ALU_ADD 15 12 15).
Proof. vm_refl. Qed.
Definition W_5da2c : bv 32 := 0x00178813.
Lemma F_5da2c : CTabKB.F 0x5da2c W_5da2c.
Proof. vm_refl. Qed.
Lemma D_5da2c : CTabKB.D W_5da2c (OpImm ALU_ADD 16 15 1).
Proof. vm_refl. Qed.
Definition W_5da30 : bv 32 := 0x00e678b3.
Lemma F_5da30 : CTabKB.F 0x5da30 W_5da30.
Proof. vm_refl. Qed.
Lemma D_5da30 : CTabKB.D W_5da30 (Op ALU_AND 17 12 14).
Proof. vm_refl. Qed.
Definition W_5da34 : bv 32 := 0x011687b3.
Lemma F_5da34 : CTabKB.F 0x5da34 W_5da34.
Proof. vm_refl. Qed.
Lemma D_5da34 : CTabKB.D W_5da34 (Op ALU_ADD 15 13 17).
Proof. vm_refl. Qed.
Definition W_5da38 : bv 32 := 0x0007c283.
Lemma F_5da38 : CTabKB.F 0x5da38 W_5da38.
Proof. vm_refl. Qed.
Lemma D_5da38 : CTabKB.D W_5da38 (Load SZ1 false 5 15 0).
Proof. vm_refl. Qed.
Definition W_5da3c : bv 32 := 0x06028663.
Lemma F_5da3c : CTabKB.F 0x5da3c W_5da3c.
Proof. vm_refl. Qed.
Lemma D_5da3c : CTabKB.D W_5da3c (Branch BC_EQ 5 0 108).
Proof. vm_refl. Qed.
Definition W_5da40 : bv 32 := 0xfff5051b.
Lemma F_5da40 : CTabKB.F 0x5da40 W_5da40.
Proof. vm_refl. Qed.
Lemma D_5da40 : CTabKB.D W_5da40 (OpImm32 10 10 4095).
Proof. vm_refl. Qed.
Definition W_5da44 : bv 32 := 0x00160613.
Lemma F_5da44 : CTabKB.F 0x5da44 W_5da44.
Proof. vm_refl. Qed.
Lemma D_5da44 : CTabKB.D W_5da44 (OpImm ALU_ADD 12 12 1).
Proof. vm_refl. Qed.
Definition W_5da48 : bv 32 := 0xfe0514e3.
Lemma F_5da48 : CTabKB.F 0x5da48 W_5da48.
Proof. vm_refl. Qed.
Lemma D_5da48 : CTabKB.D W_5da48 (Branch BC_NE 10 0 8168).
Proof. vm_refl. Qed.
Definition W_5daa8 : bv 32 := 0x00160613.
Lemma F_5daa8 : CTabKB.F 0x5daa8 W_5daa8.
Proof. vm_refl. Qed.
Lemma D_5daa8 : CTabKB.D W_5daa8 (OpImm ALU_ADD 12 12 1).
Proof. vm_refl. Qed.
Definition W_5daac : bv 32 := 0x00100513.
Lemma F_5daac : CTabKB.F 0x5daac W_5daac.
Proof. vm_refl. Qed.
Lemma D_5daac : CTabKB.D W_5daac (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_5dab0 : bv 32 := 0xffb90693.
Lemma F_5dab0 : CTabKB.F 0x5dab0 W_5dab0.
Proof. vm_refl. Qed.
Lemma D_5dab0 : CTabKB.D W_5dab0 (OpImm ALU_ADD 13 18 4091).
Proof. vm_refl. Qed.
Definition W_5dab4 : bv 32 := 0x00c4bc23.
Lemma F_5dab4 : CTabKB.F 0x5dab4 W_5dab4.
Proof. vm_refl. Qed.
Lemma D_5dab4 : CTabKB.D W_5dab4 (Store SZ8 9 12 24).
Proof. vm_refl. Qed.
Definition W_5dab8 : bv 32 := 0x00a78023.
Lemma F_5dab8 : CTabKB.F 0x5dab8 W_5dab8.
Proof. vm_refl. Qed.
Lemma D_5dab8 : CTabKB.D W_5dab8 (Store SZ1 15 10 0).
Proof. vm_refl. Qed.
Definition W_5dabc : bv 32 := 0x00d51533.
Lemma F_5dabc : CTabKB.F 0x5dabc W_5dabc.
Proof. vm_refl. Qed.
Lemma D_5dabc : CTabKB.D W_5dabc (Op ALU_SLL 10 10 13).
Proof. vm_refl. Qed.
Definition W_5dac0 : bv 32 := 0x00300613.
Lemma F_5dac0 : CTabKB.F 0x5dac0 W_5dac0.
Proof. vm_refl. Qed.
Lemma D_5dac0 : CTabKB.D W_5dac0 (OpImm ALU_ADD 12 0 3).
Proof. vm_refl. Qed.
Definition W_5dac4 : bv 32 := 0x00989893.
Lemma F_5dac4 : CTabKB.F 0x5dac4 W_5dac4.
Proof. vm_refl. Qed.
Lemma D_5dac4 : CTabKB.D W_5dac4 (ShiftImm ALU_SLL 17 17 9).
Proof. vm_refl. Qed.
Definition W_5dac8 : bv 32 := 0x01261633.
Lemma F_5dac8 : CTabKB.F 0x5dac8 W_5dac8.
Proof. vm_refl. Qed.
Lemma D_5dac8 : CTabKB.D W_5dac8 (Op ALU_SLL 12 12 18).
Proof. vm_refl. Qed.
Definition W_5dacc : bv 32 := 0x00a58533.
Lemma F_5dacc : CTabKB.F 0x5dacc W_5dacc.
Proof. vm_refl. Qed.
Lemma D_5dacc : CTabKB.D W_5dacc (Op ALU_ADD 10 11 10).
Proof. vm_refl. Qed.
Definition W_5dad0 : bv 32 := 0x01160633.
Lemma F_5dad0 : CTabKB.F 0x5dad0 W_5dad0.
Proof. vm_refl. Qed.
Lemma D_5dad0 : CTabKB.D W_5dad0 (Op ALU_ADD 12 12 17).
Proof. vm_refl. Qed.
Definition W_5dad4 : bv 32 := 0x00c504b3.
Lemma F_5dad4 : CTabKB.F 0x5dad4 W_5dad4.
Proof. vm_refl. Qed.
Lemma D_5dad4 : CTabKB.D W_5dad4 (Op ALU_ADD 9 10 12).
Proof. vm_refl. Qed.
Definition W_5dad8 : bv 32 := 0x0084bc23.
Lemma F_5dad8 : CTabKB.F 0x5dad8 W_5dad8.
Proof. vm_refl. Qed.
Lemma D_5dad8 : CTabKB.D W_5dad8 (Store SZ8 9 8 24).
Proof. vm_refl. Qed.
Definition W_5dadc : bv 32 := 0x1ef4bc23.
Lemma F_5dadc : CTabKB.F 0x5dadc W_5dadc.
Proof. vm_refl. Qed.
Lemma D_5dadc : CTabKB.D W_5dadc (Store SZ8 9 15 504).
Proof. vm_refl. Qed.
Definition W_5dae0 : bv 32 := 0x00048513.
Lemma F_5dae0 : CTabKB.F 0x5dae0 W_5dae0.
Proof. vm_refl. Qed.
Lemma D_5dae0 : CTabKB.D W_5dae0 (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_5dae4 : bv 32 := 0x230000ef.
Lemma F_5dae4 : CTabKB.F 0x5dae4 W_5dae4.
Proof. vm_refl. Qed.
Lemma D_5dae4 : CTabKB.D W_5dae4 (Jal 1 560).
Proof. vm_refl. Qed.
Definition W_5dae8 : bv 32 := 0x00050593.
Lemma F_5dae8 : CTabKB.F 0x5dae8 W_5dae8.
Proof. vm_refl. Qed.
Lemma D_5dae8 : CTabKB.D W_5dae8 (OpImm ALU_ADD 11 10 0).
Proof. vm_refl. Qed.
Definition W_5daec : bv 32 := 0x00048513.
Lemma F_5daec : CTabKB.F 0x5daec W_5daec.
Proof. vm_refl. Qed.
Lemma D_5daec : CTabKB.D W_5daec (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_5daf0 : bv 32 := 0x00000613.
Lemma F_5daf0 : CTabKB.F 0x5daf0 W_5daf0.
Proof. vm_refl. Qed.
Lemma D_5daf0 : CTabKB.D W_5daf0 (OpImm ALU_ADD 12 0 0).
Proof. vm_refl. Qed.
Definition W_5daf4 : bv 32 := 0x0005b023.
Lemma F_5daf4 : CTabKB.F 0x5daf4 W_5daf4.
Proof. vm_refl. Qed.
Lemma D_5daf4 : CTabKB.D W_5daf4 (Store SZ8 11 0 0).
Proof. vm_refl. Qed.
Definition W_5daf8 : bv 32 := 0x0005b423.
Lemma F_5daf8 : CTabKB.F 0x5daf8 W_5daf8.
Proof. vm_refl. Qed.
Lemma D_5daf8 : CTabKB.D W_5daf8 (Store SZ8 11 0 8).
Proof. vm_refl. Qed.
Definition W_5dafc : bv 32 := 0x0005b823.
Lemma F_5dafc : CTabKB.F 0x5dafc W_5dafc.
Proof. vm_refl. Qed.
Lemma D_5dafc : CTabKB.D W_5dafc (Store SZ8 11 0 16).
Proof. vm_refl. Qed.
Definition W_5db00 : bv 32 := 0x0005bc23.
Lemma F_5db00 : CTabKB.F 0x5db00 W_5db00.
Proof. vm_refl. Qed.
Lemma D_5db00 : CTabKB.D W_5db00 (Store SZ8 11 0 24).
Proof. vm_refl. Qed.
Definition W_5db04 : bv 32 := 0x0205b023.
Lemma F_5db04 : CTabKB.F 0x5db04 W_5db04.
Proof. vm_refl. Qed.
Lemma D_5db04 : CTabKB.D W_5db04 (Store SZ8 11 0 32).
Proof. vm_refl. Qed.
Definition W_5db08 : bv 32 := 0x0205b423.
Lemma F_5db08 : CTabKB.F 0x5db08 W_5db08.
Proof. vm_refl. Qed.
Lemma D_5db08 : CTabKB.D W_5db08 (Store SZ8 11 0 40).
Proof. vm_refl. Qed.
Definition W_5db0c : bv 32 := 0x0205b823.
Lemma F_5db0c : CTabKB.F 0x5db0c W_5db0c.
Proof. vm_refl. Qed.
Lemma D_5db0c : CTabKB.D W_5db0c (Store SZ8 11 0 48).
Proof. vm_refl. Qed.
Definition W_5db10 : bv 32 := 0x0205bc23.
Lemma F_5db10 : CTabKB.F 0x5db10 W_5db10.
Proof. vm_refl. Qed.
Lemma D_5db10 : CTabKB.D W_5db10 (Store SZ8 11 0 56).
Proof. vm_refl. Qed.
Definition W_5db14 : bv 32 := 0x01813083.
Lemma F_5db14 : CTabKB.F 0x5db14 W_5db14.
Proof. vm_refl. Qed.
Lemma D_5db14 : CTabKB.D W_5db14 (Load SZ8 true 1 2 24).
Proof. vm_refl. Qed.
Definition W_5db18 : bv 32 := 0x01013403.
Lemma F_5db18 : CTabKB.F 0x5db18 W_5db18.
Proof. vm_refl. Qed.
Lemma D_5db18 : CTabKB.D W_5db18 (Load SZ8 true 8 2 16).
Proof. vm_refl. Qed.
Definition W_5db1c : bv 32 := 0x00813483.
Lemma F_5db1c : CTabKB.F 0x5db1c W_5db1c.
Proof. vm_refl. Qed.
Lemma D_5db1c : CTabKB.D W_5db1c (Load SZ8 true 9 2 8).
Proof. vm_refl. Qed.
Definition W_5db20 : bv 32 := 0x00013903.
Lemma F_5db20 : CTabKB.F 0x5db20 W_5db20.
Proof. vm_refl. Qed.
Lemma D_5db20 : CTabKB.D W_5db20 (Load SZ8 true 18 2 0).
Proof. vm_refl. Qed.
Definition W_5db24 : bv 32 := 0x02010113.
Lemma F_5db24 : CTabKB.F 0x5db24 W_5db24.
Proof. vm_refl. Qed.
Lemma D_5db24 : CTabKB.D W_5db24 (OpImm ALU_ADD 2 2 32).
Proof. vm_refl. Qed.
Definition W_5db28 : bv 32 := 0x00008067.
Lemma F_5db28 : CTabKB.F 0x5db28 W_5db28.
Proof. vm_refl. Qed.
Lemma D_5db28 : CTabKB.D W_5db28 (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_5dd14 : bv 32 := 0x000d6597.
Lemma F_5dd14 : CTabKB.F 0x5dd14 W_5dd14.
Proof. vm_refl. Qed.
Lemma D_5dd14 : CTabKB.D W_5dd14 (Auipc 11 214).
Proof. vm_refl. Qed.
Definition W_5dd18 : bv 32 := 0x68c5b583.
Lemma F_5dd18 : CTabKB.F 0x5dd18 W_5dd18.
Proof. vm_refl. Qed.
Lemma D_5dd18 : CTabKB.D W_5dd18 (Load SZ8 true 11 11 1676).
Proof. vm_refl. Qed.
Definition W_5dd1c : bv 32 := 0x0005b583.
Lemma F_5dd1c : CTabKB.F 0x5dd1c W_5dd1c.
Proof. vm_refl. Qed.
Lemma D_5dd1c : CTabKB.D W_5dd1c (Load SZ8 true 11 11 0).
Proof. vm_refl. Qed.
Definition W_5dd20 : bv 32 := 0xfff58613.
Lemma F_5dd20 : CTabKB.F 0x5dd20 W_5dd20.
Proof. vm_refl. Qed.
Lemma D_5dd20 : CTabKB.D W_5dd20 (OpImm ALU_ADD 12 11 4095).
Proof. vm_refl. Qed.
Definition W_5dd24 : bv 32 := 0x00c5b6b3.
Lemma F_5dd24 : CTabKB.F 0x5dd24 W_5dd24.
Proof. vm_refl. Qed.
Lemma D_5dd24 : CTabKB.D W_5dd24 (Op ALU_SLTU 13 11 12).
Proof. vm_refl. Qed.
Definition W_5dd28 : bv 32 := 0xfff68693.
Lemma F_5dd28 : CTabKB.F 0x5dd28 W_5dd28.
Proof. vm_refl. Qed.
Lemma D_5dd28 : CTabKB.D W_5dd28 (OpImm ALU_ADD 13 13 4095).
Proof. vm_refl. Qed.
Definition W_5dd2c : bv 32 := 0x00c6f6b3.
Lemma F_5dd2c : CTabKB.F 0x5dd2c W_5dd2c.
Proof. vm_refl. Qed.
Lemma D_5dd2c : CTabKB.D W_5dd2c (Op ALU_AND 13 13 12).
Proof. vm_refl. Qed.
Definition W_5dd30 : bv 32 := 0x04a6f263.
Lemma F_5dd30 : CTabKB.F 0x5dd30 W_5dd30.
Proof. vm_refl. Qed.
Lemma D_5dd30 : CTabKB.D W_5dd30 (Branch BC_GEU 13 10 68).
Proof. vm_refl. Qed.
Definition W_5dd34 : bv 32 := 0x000d6697.
Lemma F_5dd34 : CTabKB.F 0x5dd34 W_5dd34.
Proof. vm_refl. Qed.
Lemma D_5dd34 : CTabKB.D W_5dd34 (Auipc 13 214).
Proof. vm_refl. Qed.
Definition W_5dd38 : bv 32 := 0x6746b683.
Lemma F_5dd38 : CTabKB.F 0x5dd38 W_5dd38.
Proof. vm_refl. Qed.
Lemma D_5dd38 : CTabKB.D W_5dd38 (Load SZ8 true 13 13 1652).
Proof. vm_refl. Qed.
Definition W_5dd3c : bv 32 := 0x000d6717.
Lemma F_5dd3c : CTabKB.F 0x5dd3c W_5dd3c.
Proof. vm_refl. Qed.
Lemma D_5dd3c : CTabKB.D W_5dd3c (Auipc 14 214).
Proof. vm_refl. Qed.
Definition W_5dd40 : bv 32 := 0x67473703.
Lemma F_5dd40 : CTabKB.F 0x5dd40 W_5dd40.
Proof. vm_refl. Qed.
Lemma D_5dd40 : CTabKB.D W_5dd40 (Load SZ8 true 14 14 1652).
Proof. vm_refl. Qed.
Definition W_5dd44 : bv 32 := 0x0006b803.
Lemma F_5dd44 : CTabKB.F 0x5dd44 W_5dd44.
Proof. vm_refl. Qed.
Lemma D_5dd44 : CTabKB.D W_5dd44 (Load SZ8 true 16 13 0).
Proof. vm_refl. Qed.
Definition W_5dd48 : bv 32 := 0x00073683.
Lemma F_5dd48 : CTabKB.F 0x5dd48 W_5dd48.
Proof. vm_refl. Qed.
Lemma D_5dd48 : CTabKB.D W_5dd48 (Load SZ8 true 13 14 0).
Proof. vm_refl. Qed.
Definition W_5dd4c : bv 32 := 0xfff80793.
Lemma F_5dd4c : CTabKB.F 0x5dd4c W_5dd4c.
Proof. vm_refl. Qed.
Lemma D_5dd4c : CTabKB.D W_5dd4c (OpImm ALU_ADD 15 16 4095).
Proof. vm_refl. Qed.
Definition W_5dd50 : bv 32 := 0x00a7f463.
Lemma F_5dd50 : CTabKB.F 0x5dd50 W_5dd50.
Proof. vm_refl. Qed.
Lemma D_5dd50 : CTabKB.D W_5dd50 (Branch BC_GEU 15 10 8).
Proof. vm_refl. Qed.
Definition W_5dd58 : bv 32 := 0x000d6717.
Lemma F_5dd58 : CTabKB.F 0x5dd58 W_5dd58.
Proof. vm_refl. Qed.
Lemma D_5dd58 : CTabKB.D W_5dd58 (Auipc 14 214).
Proof. vm_refl. Qed.
Definition W_5dd5c : bv 32 := 0x66073703.
Lemma F_5dd5c : CTabKB.F 0x5dd5c W_5dd5c.
Proof. vm_refl. Qed.
Lemma D_5dd5c : CTabKB.D W_5dd5c (Load SZ8 true 14 14 1632).
Proof. vm_refl. Qed.
Definition W_5dd60 : bv 32 := 0x00073283.
Lemma F_5dd60 : CTabKB.F 0x5dd60 W_5dd60.
Proof. vm_refl. Qed.
Lemma D_5dd60 : CTabKB.D W_5dd60 (Load SZ8 true 5 14 0).
Proof. vm_refl. Qed.
Definition W_5dd64 : bv 32 := 0x0032d713.
Lemma F_5dd64 : CTabKB.F 0x5dd64 W_5dd64.
Proof. vm_refl. Qed.
Lemma D_5dd64 : CTabKB.D W_5dd64 (ShiftImm ALU_SRL 14 5 3).
Proof. vm_refl. Qed.
Definition W_5dd68 : bv 32 := 0x00b708b3.
Lemma F_5dd68 : CTabKB.F 0x5dd68 W_5dd68.
Proof. vm_refl. Qed.
Lemma D_5dd68 : CTabKB.D W_5dd68 (Op ALU_ADD 17 14 11).
Proof. vm_refl. Qed.
Definition W_5dd6c : bv 32 := 0x00a2ea63.
Lemma F_5dd6c : CTabKB.F 0x5dd6c W_5dd6c.
Proof. vm_refl. Qed.
Lemma D_5dd6c : CTabKB.D W_5dd6c (Branch BC_LTU 5 10 20).
Proof. vm_refl. Qed.
Definition W_5dd70 : bv 32 := 0x00a8f863.
Lemma F_5dd70 : CTabKB.F 0x5dd70 W_5dd70.
Proof. vm_refl. Qed.
Lemma D_5dd70 : CTabKB.D W_5dd70 (Branch BC_GEU 17 10 16).
Proof. vm_refl. Qed.
Definition W_5dd74 : bv 32 := 0x00355513.
Lemma F_5dd74 : CTabKB.F 0x5dd74 W_5dd74.
Proof. vm_refl. Qed.
Lemma D_5dd74 : CTabKB.D W_5dd74 (ShiftImm ALU_SRL 10 10 3).
Proof. vm_refl. Qed.
Definition W_5dd78 : bv 32 := 0x00a58533.
Lemma F_5dd78 : CTabKB.F 0x5dd78 W_5dd78.
Proof. vm_refl. Qed.
Lemma D_5dd78 : CTabKB.D W_5dd78 (Op ALU_ADD 10 11 10).
Proof. vm_refl. Qed.
Definition W_5dd7c : bv 32 := 0x00008067.
Lemma F_5dd7c : CTabKB.F 0x5dd7c W_5dd7c.
Proof. vm_refl. Qed.
Lemma D_5dd7c : CTabKB.D W_5dd7c (Jalr 0 1 0).
Proof. vm_refl. Qed.

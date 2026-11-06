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

Definition W_78de4 : bv 32 := 0x2590006f.
Lemma F_78de4 : fetch_word AsanUbsan.M.loaded_segments (0x78e34 : word) = Some W_78de4.
Proof. vm_refl. Qed.
Lemma D_78de4 : decode_any W_78de4 = Some (Jal 0 2648, 4%Z).
Proof. vm_refl. Qed.

Definition W_78de8 : bv 32 := 0x5450006f.
Lemma F_78de8 : fetch_word AsanUbsan.M.loaded_segments (0x78e38 : word) = Some W_78de8.
Proof. vm_refl. Qed.
Lemma D_78de8 : decode_any W_78de8 = Some (Jal 0 3396, 4%Z).
Proof. vm_refl. Qed.

Definition W_78dec : bv 32 := 0x2000106f.
Lemma F_78dec : fetch_word AsanUbsan.M.loaded_segments (0x78e3c : word) = Some W_78dec.
Proof. vm_refl. Qed.
Lemma D_78dec : decode_any W_78dec = Some (Jal 0 4608, 4%Z).
Proof. vm_refl. Qed.

Definition W_78df0 : bv 32 := 0x81010113.
Lemma F_78df0 : fetch_word AsanUbsan.M.loaded_segments (0x78e40 : word) = Some W_78df0.
Proof. vm_refl. Qed.
Lemma D_78df0 : decode_any W_78df0 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_78df4 : bv 32 := 0x7e113423.
Lemma F_78df4 : fetch_word AsanUbsan.M.loaded_segments (0x78e44 : word) = Some W_78df4.
Proof. vm_refl. Qed.
Lemma D_78df4 : decode_any W_78df4 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_78df8 : bv 32 := 0x7e813023.
Lemma F_78df8 : fetch_word AsanUbsan.M.loaded_segments (0x78e48 : word) = Some W_78df8.
Proof. vm_refl. Qed.
Lemma D_78df8 : decode_any W_78df8 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_78dfc : bv 32 := 0x7c913c23.
Lemma F_78dfc : fetch_word AsanUbsan.M.loaded_segments (0x78e4c : word) = Some W_78dfc.
Proof. vm_refl. Qed.
Lemma D_78dfc : decode_any W_78dfc = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e00 : bv 32 := 0x7d213823.
Lemma F_78e00 : fetch_word AsanUbsan.M.loaded_segments (0x78e50 : word) = Some W_78e00.
Proof. vm_refl. Qed.
Lemma D_78e00 : decode_any W_78e00 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e04 : bv 32 := 0x7d313423.
Lemma F_78e04 : fetch_word AsanUbsan.M.loaded_segments (0x78e54 : word) = Some W_78e04.
Proof. vm_refl. Qed.
Lemma D_78e04 : decode_any W_78e04 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e08 : bv 32 := 0x7d413023.
Lemma F_78e08 : fetch_word AsanUbsan.M.loaded_segments (0x78e58 : word) = Some W_78e08.
Proof. vm_refl. Qed.
Lemma D_78e08 : decode_any W_78e08 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e0c : bv 32 := 0x7b513c23.
Lemma F_78e0c : fetch_word AsanUbsan.M.loaded_segments (0x78e5c : word) = Some W_78e0c.
Proof. vm_refl. Qed.
Lemma D_78e0c : decode_any W_78e0c = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e10 : bv 32 := 0x7b613823.
Lemma F_78e10 : fetch_word AsanUbsan.M.loaded_segments (0x78e60 : word) = Some W_78e10.
Proof. vm_refl. Qed.
Lemma D_78e10 : decode_any W_78e10 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e14 : bv 32 := 0x7b713423.
Lemma F_78e14 : fetch_word AsanUbsan.M.loaded_segments (0x78e64 : word) = Some W_78e14.
Proof. vm_refl. Qed.
Lemma D_78e14 : decode_any W_78e14 = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e18 : bv 32 := 0x7f010413.
Lemma F_78e18 : fetch_word AsanUbsan.M.loaded_segments (0x78e68 : word) = Some W_78e18.
Proof. vm_refl. Qed.
Lemma D_78e18 : decode_any W_78e18 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e1c : bv 32 := 0xf9010113.
Lemma F_78e1c : fetch_word AsanUbsan.M.loaded_segments (0x78e6c : word) = Some W_78e1c.
Proof. vm_refl. Qed.
Lemma D_78e1c : decode_any W_78e1c = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e20 : bv 32 := 0x000c5697.
Lemma F_78e20 : fetch_word AsanUbsan.M.loaded_segments (0x78e70 : word) = Some W_78e20.
Proof. vm_refl. Qed.
Lemma D_78e20 : decode_any W_78e20 = Some (Auipc 13 197, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e24 : bv 32 := 0x5c06b683.
Lemma F_78e24 : fetch_word AsanUbsan.M.loaded_segments (0x78e74 : word) = Some W_78e24.
Proof. vm_refl. Qed.
Lemma D_78e24 : decode_any W_78e24 = Some (Load SZ8 true 13 13 1472, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e28 : bv 32 := 0x0006c683.
Lemma F_78e28 : fetch_word AsanUbsan.M.loaded_segments (0x78e78 : word) = Some W_78e28.
Proof. vm_refl. Qed.
Lemma D_78e28 : decode_any W_78e28 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e2c : bv 32 := 0x0e068863.
Lemma F_78e2c : fetch_word AsanUbsan.M.loaded_segments (0x78e7c : word) = Some W_78e2c.
Proof. vm_refl. Qed.
Lemma D_78e2c : decode_any W_78e2c = Some (Branch BC_EQ 13 0 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e30 : bv 32 := 0x80040a13.
Lemma F_78e30 : fetch_word AsanUbsan.M.loaded_segments (0x78e80 : word) = Some W_78e30.
Proof. vm_refl. Qed.
Lemma D_78e30 : decode_any W_78e30 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e34 : bv 32 := 0xfa0a0a13.
Lemma F_78e34 : fetch_word AsanUbsan.M.loaded_segments (0x78e84 : word) = Some W_78e34.
Proof. vm_refl. Qed.
Lemma D_78e34 : decode_any W_78e34 = Some (OpImm ALU_ADD 20 20 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e38 : bv 32 := 0x00c58ab3.
Lemma F_78e38 : fetch_word AsanUbsan.M.loaded_segments (0x78e88 : word) = Some W_78e38.
Proof. vm_refl. Qed.
Lemma D_78e38 : decode_any W_78e38 = Some (Op ALU_ADD 21 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e3c : bv 32 := 0x00c509b3.
Lemma F_78e3c : fetch_word AsanUbsan.M.loaded_segments (0x78e8c : word) = Some W_78e3c.
Proof. vm_refl. Qed.
Lemma D_78e3c : decode_any W_78e3c = Some (Op ALU_ADD 19 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e40 : bv 32 := 0x00b50663.
Lemma F_78e40 : fetch_word AsanUbsan.M.loaded_segments (0x78e90 : word) = Some W_78e40.
Proof. vm_refl. Qed.
Lemma D_78e40 : decode_any W_78e40 = Some (Branch BC_EQ 10 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e44 : bv 32 := 0x0135f463.
Lemma F_78e44 : fetch_word AsanUbsan.M.loaded_segments (0x78e94 : word) = Some W_78e44.
Proof. vm_refl. Qed.
Lemma D_78e44 : decode_any W_78e44 = Some (Branch BC_GEU 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e48 : bv 32 := 0x1b556a63.
Lemma F_78e48 : fetch_word AsanUbsan.M.loaded_segments (0x78e98 : word) = Some W_78e48.
Proof. vm_refl. Qed.
Lemma D_78e48 : decode_any W_78e48 = Some (Branch BC_LTU 10 21 436, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e4c : bv 32 := 0xfff5c693.
Lemma F_78e4c : fetch_word AsanUbsan.M.loaded_segments (0x78e9c : word) = Some W_78e4c.
Proof. vm_refl. Qed.
Lemma D_78e4c : decode_any W_78e4c = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e50 : bv 32 := 0x26c6e463.
Lemma F_78e50 : fetch_word AsanUbsan.M.loaded_segments (0x78ea0 : word) = Some W_78e50.
Proof. vm_refl. Qed.
Lemma D_78e50 : decode_any W_78e50 = Some (Branch BC_LTU 13 12 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e54 : bv 32 := 0xfbf60b13.
Lemma F_78e54 : fetch_word AsanUbsan.M.loaded_segments (0x78ea4 : word) = Some W_78e54.
Proof. vm_refl. Qed.
Lemma D_78e54 : decode_any W_78e54 = Some (OpImm ALU_ADD 22 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e58 : bv 32 := 0xfbf00693.
Lemma F_78e58 : fetch_word AsanUbsan.M.loaded_segments (0x78ea8 : word) = Some W_78e58.
Proof. vm_refl. Qed.
Lemma D_78e58 : decode_any W_78e58 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e5c : bv 32 := 0x2f66f263.
Lemma F_78e5c : fetch_word AsanUbsan.M.loaded_segments (0x78eac : word) = Some W_78e5c.
Proof. vm_refl. Qed.
Lemma D_78e5c : decode_any W_78e5c = Some (Branch BC_GEU 13 22 740, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e60 : bv 32 := 0x000c5697.
Lemma F_78e60 : fetch_word AsanUbsan.M.loaded_segments (0x78eb0 : word) = Some W_78e60.
Proof. vm_refl. Qed.
Lemma D_78e60 : decode_any W_78e60 = Some (Auipc 13 197, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e64 : bv 32 := 0xa186b683.
Lemma F_78e64 : fetch_word AsanUbsan.M.loaded_segments (0x78eb4 : word) = Some W_78e64.
Proof. vm_refl. Qed.
Lemma D_78e64 : decode_any W_78e64 = Some (Load SZ8 true 13 13 2584, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e68 : bv 32 := 0x0006b703.
Lemma F_78e68 : fetch_word AsanUbsan.M.loaded_segments (0x78eb8 : word) = Some W_78e68.
Proof. vm_refl. Qed.
Lemma D_78e68 : decode_any W_78e68 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e6c : bv 32 := 0xfffa8a93.
Lemma F_78e6c : fetch_word AsanUbsan.M.loaded_segments (0x78ebc : word) = Some W_78e6c.
Proof. vm_refl. Qed.
Lemma D_78e6c : decode_any W_78e6c = Some (OpImm ALU_ADD 21 21 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e70 : bv 32 := 0x0035d693.
Lemma F_78e70 : fetch_word AsanUbsan.M.loaded_segments (0x78ec0 : word) = Some W_78e70.
Proof. vm_refl. Qed.
Lemma D_78e70 : decode_any W_78e70 = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e74 : bv 32 := 0x003ad793.
Lemma F_78e74 : fetch_word AsanUbsan.M.loaded_segments (0x78ec4 : word) = Some W_78e74.
Proof. vm_refl. Qed.
Lemma D_78e74 : decode_any W_78e74 = Some (ShiftImm ALU_SRL 15 21 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e78 : bv 32 := 0x00d706b3.
Lemma F_78e78 : fetch_word AsanUbsan.M.loaded_segments (0x78ec8 : word) = Some W_78e78.
Proof. vm_refl. Qed.
Lemma D_78e78 : decode_any W_78e78 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e7c : bv 32 := 0x00f70733.
Lemma F_78e7c : fetch_word AsanUbsan.M.loaded_segments (0x78ecc : word) = Some W_78e7c.
Proof. vm_refl. Qed.
Lemma D_78e7c : decode_any W_78e7c = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e80 : bv 32 := 0xff86f793.
Lemma F_78e80 : fetch_word AsanUbsan.M.loaded_segments (0x78ed0 : word) = Some W_78e80.
Proof. vm_refl. Qed.
Lemma D_78e80 : decode_any W_78e80 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e84 : bv 32 := 0xff877813.
Lemma F_78e84 : fetch_word AsanUbsan.M.loaded_segments (0x78ed4 : word) = Some W_78e84.
Proof. vm_refl. Qed.
Lemma D_78e84 : decode_any W_78e84 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e88 : bv 32 := 0x0007b783.
Lemma F_78e88 : fetch_word AsanUbsan.M.loaded_segments (0x78ed8 : word) = Some W_78e88.
Proof. vm_refl. Qed.
Lemma D_78e88 : decode_any W_78e88 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e8c : bv 32 := 0x00083803.
Lemma F_78e8c : fetch_word AsanUbsan.M.loaded_segments (0x78edc : word) = Some W_78e8c.
Proof. vm_refl. Qed.
Lemma D_78e8c : decode_any W_78e8c = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e90 : bv 32 := 0x00f867b3.
Lemma F_78e90 : fetch_word AsanUbsan.M.loaded_segments (0x78ee0 : word) = Some W_78e90.
Proof. vm_refl. Qed.
Lemma D_78e90 : decode_any W_78e90 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e94 : bv 32 := 0x2a079a63.
Lemma F_78e94 : fetch_word AsanUbsan.M.loaded_segments (0x78ee4 : word) = Some W_78e94.
Proof. vm_refl. Qed.
Lemma D_78e94 : decode_any W_78e94 = Some (Branch BC_NE 15 0 692, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e98 : bv 32 := 0xfff54693.
Lemma F_78e98 : fetch_word AsanUbsan.M.loaded_segments (0x78ee8 : word) = Some W_78e98.
Proof. vm_refl. Qed.
Lemma D_78e98 : decode_any W_78e98 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_78e9c : bv 32 := 0x0cc6ea63.
Lemma F_78e9c : fetch_word AsanUbsan.M.loaded_segments (0x78eec : word) = Some W_78e9c.
Proof. vm_refl. Qed.
Lemma D_78e9c : decode_any W_78e9c = Some (Branch BC_LTU 13 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ea0 : bv 32 := 0xfbf00693.
Lemma F_78ea0 : fetch_word AsanUbsan.M.loaded_segments (0x78ef0 : word) = Some W_78ea0.
Proof. vm_refl. Qed.
Lemma D_78ea0 : decode_any W_78ea0 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ea4 : bv 32 := 0x1566f863.
Lemma F_78ea4 : fetch_word AsanUbsan.M.loaded_segments (0x78ef4 : word) = Some W_78ea4.
Proof. vm_refl. Qed.
Lemma D_78ea4 : decode_any W_78ea4 = Some (Branch BC_GEU 13 22 336, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ea8 : bv 32 := 0x000c5697.
Lemma F_78ea8 : fetch_word AsanUbsan.M.loaded_segments (0x78ef8 : word) = Some W_78ea8.
Proof. vm_refl. Qed.
Lemma D_78ea8 : decode_any W_78ea8 = Some (Auipc 13 197, 4%Z).
Proof. vm_refl. Qed.

Definition W_78eac : bv 32 := 0x9d06b683.
Lemma F_78eac : fetch_word AsanUbsan.M.loaded_segments (0x78efc : word) = Some W_78eac.
Proof. vm_refl. Qed.
Lemma D_78eac : decode_any W_78eac = Some (Load SZ8 true 13 13 2512, 4%Z).
Proof. vm_refl. Qed.

Definition W_78eb0 : bv 32 := 0x0006b703.
Lemma F_78eb0 : fetch_word AsanUbsan.M.loaded_segments (0x78f00 : word) = Some W_78eb0.
Proof. vm_refl. Qed.
Lemma D_78eb0 : decode_any W_78eb0 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78eb4 : bv 32 := 0xfff98993.
Lemma F_78eb4 : fetch_word AsanUbsan.M.loaded_segments (0x78f04 : word) = Some W_78eb4.
Proof. vm_refl. Qed.
Lemma D_78eb4 : decode_any W_78eb4 = Some (OpImm ALU_ADD 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_78eb8 : bv 32 := 0x00355693.
Lemma F_78eb8 : fetch_word AsanUbsan.M.loaded_segments (0x78f08 : word) = Some W_78eb8.
Proof. vm_refl. Qed.
Lemma D_78eb8 : decode_any W_78eb8 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ebc : bv 32 := 0x0039d793.
Lemma F_78ebc : fetch_word AsanUbsan.M.loaded_segments (0x78f0c : word) = Some W_78ebc.
Proof. vm_refl. Qed.
Lemma D_78ebc : decode_any W_78ebc = Some (ShiftImm ALU_SRL 15 19 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ec0 : bv 32 := 0x00d706b3.
Lemma F_78ec0 : fetch_word AsanUbsan.M.loaded_segments (0x78f10 : word) = Some W_78ec0.
Proof. vm_refl. Qed.
Lemma D_78ec0 : decode_any W_78ec0 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ec4 : bv 32 := 0x00f70733.
Lemma F_78ec4 : fetch_word AsanUbsan.M.loaded_segments (0x78f14 : word) = Some W_78ec4.
Proof. vm_refl. Qed.
Lemma D_78ec4 : decode_any W_78ec4 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ec8 : bv 32 := 0xff86f793.
Lemma F_78ec8 : fetch_word AsanUbsan.M.loaded_segments (0x78f18 : word) = Some W_78ec8.
Proof. vm_refl. Qed.
Lemma D_78ec8 : decode_any W_78ec8 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ecc : bv 32 := 0xff877813.
Lemma F_78ecc : fetch_word AsanUbsan.M.loaded_segments (0x78f1c : word) = Some W_78ecc.
Proof. vm_refl. Qed.
Lemma D_78ecc : decode_any W_78ecc = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ed0 : bv 32 := 0x0007b783.
Lemma F_78ed0 : fetch_word AsanUbsan.M.loaded_segments (0x78f20 : word) = Some W_78ed0.
Proof. vm_refl. Qed.
Lemma D_78ed0 : decode_any W_78ed0 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ed4 : bv 32 := 0x00083803.
Lemma F_78ed4 : fetch_word AsanUbsan.M.loaded_segments (0x78f24 : word) = Some W_78ed4.
Proof. vm_refl. Qed.
Lemma D_78ed4 : decode_any W_78ed4 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ed8 : bv 32 := 0x00f867b3.
Lemma F_78ed8 : fetch_word AsanUbsan.M.loaded_segments (0x78f28 : word) = Some W_78ed8.
Proof. vm_refl. Qed.
Lemma D_78ed8 : decode_any W_78ed8 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_78edc : bv 32 := 0x30079863.
Lemma F_78edc : fetch_word AsanUbsan.M.loaded_segments (0x78f2c : word) = Some W_78edc.
Proof. vm_refl. Qed.
Lemma D_78edc : decode_any W_78edc = Some (Branch BC_NE 15 0 784, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ee0 : bv 32 := 0x000c7697.
Lemma F_78ee0 : fetch_word AsanUbsan.M.loaded_segments (0x78f30 : word) = Some W_78ee0.
Proof. vm_refl. Qed.
Lemma D_78ee0 : decode_any W_78ee0 = Some (Auipc 13 199, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ee4 : bv 32 := 0x9a06b683.
Lemma F_78ee4 : fetch_word AsanUbsan.M.loaded_segments (0x78f34 : word) = Some W_78ee4.
Proof. vm_refl. Qed.
Lemma D_78ee4 : decode_any W_78ee4 = Some (Load SZ8 true 13 13 2464, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ee8 : bv 32 := 0x000680e7.
Lemma F_78ee8 : fetch_word AsanUbsan.M.loaded_segments (0x78f38 : word) = Some W_78ee8.
Proof. vm_refl. Qed.
Lemma D_78ee8 : decode_any W_78ee8 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78eec : bv 32 := 0x07010113.
Lemma F_78eec : fetch_word AsanUbsan.M.loaded_segments (0x78f3c : word) = Some W_78eec.
Proof. vm_refl. Qed.
Lemma D_78eec : decode_any W_78eec = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ef0 : bv 32 := 0x7e813083.
Lemma F_78ef0 : fetch_word AsanUbsan.M.loaded_segments (0x78f40 : word) = Some W_78ef0.
Proof. vm_refl. Qed.
Lemma D_78ef0 : decode_any W_78ef0 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ef4 : bv 32 := 0x7e013403.
Lemma F_78ef4 : fetch_word AsanUbsan.M.loaded_segments (0x78f44 : word) = Some W_78ef4.
Proof. vm_refl. Qed.
Lemma D_78ef4 : decode_any W_78ef4 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ef8 : bv 32 := 0x7d813483.
Lemma F_78ef8 : fetch_word AsanUbsan.M.loaded_segments (0x78f48 : word) = Some W_78ef8.
Proof. vm_refl. Qed.
Lemma D_78ef8 : decode_any W_78ef8 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_78efc : bv 32 := 0x7d013903.
Lemma F_78efc : fetch_word AsanUbsan.M.loaded_segments (0x78f4c : word) = Some W_78efc.
Proof. vm_refl. Qed.
Lemma D_78efc : decode_any W_78efc = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_78f00 : bv 32 := 0x7c813983.
Lemma F_78f00 : fetch_word AsanUbsan.M.loaded_segments (0x78f50 : word) = Some W_78f00.
Proof. vm_refl. Qed.
Lemma D_78f00 : decode_any W_78f00 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_78f04 : bv 32 := 0x7c013a03.
Lemma F_78f04 : fetch_word AsanUbsan.M.loaded_segments (0x78f54 : word) = Some W_78f04.
Proof. vm_refl. Qed.
Lemma D_78f04 : decode_any W_78f04 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_78f08 : bv 32 := 0x7b813a83.
Lemma F_78f08 : fetch_word AsanUbsan.M.loaded_segments (0x78f58 : word) = Some W_78f08.
Proof. vm_refl. Qed.
Lemma D_78f08 : decode_any W_78f08 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_78f0c : bv 32 := 0x7b013b03.
Lemma F_78f0c : fetch_word AsanUbsan.M.loaded_segments (0x78f5c : word) = Some W_78f0c.
Proof. vm_refl. Qed.
Lemma D_78f0c : decode_any W_78f0c = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_78f10 : bv 32 := 0x7a813b83.
Lemma F_78f10 : fetch_word AsanUbsan.M.loaded_segments (0x78f60 : word) = Some W_78f10.
Proof. vm_refl. Qed.
Lemma D_78f10 : decode_any W_78f10 = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_78f14 : bv 32 := 0x7f010113.
Lemma F_78f14 : fetch_word AsanUbsan.M.loaded_segments (0x78f64 : word) = Some W_78f14.
Proof. vm_refl. Qed.
Lemma D_78f14 : decode_any W_78f14 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_78f18 : bv 32 := 0x00008067.
Lemma F_78f18 : fetch_word AsanUbsan.M.loaded_segments (0x78f68 : word) = Some W_78f18.
Proof. vm_refl. Qed.
Lemma D_78f18 : decode_any W_78f18 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ff4 : bv 32 := 0x22061663.
Lemma F_78ff4 : fetch_word AsanUbsan.M.loaded_segments (0x79044 : word) = Some W_78ff4.
Proof. vm_refl. Qed.
Lemma D_78ff4 : decode_any W_78ff4 = Some (Branch BC_NE 12 0 556, 4%Z).
Proof. vm_refl. Qed.

Definition W_78ff8 : bv 32 := 0xee9ff06f.
Lemma F_78ff8 : fetch_word AsanUbsan.M.loaded_segments (0x79048 : word) = Some W_78ff8.
Proof. vm_refl. Qed.
Lemma D_78ff8 : decode_any W_78ff8 = Some (Jal 0 2096872, 4%Z).
Proof. vm_refl. Qed.

Definition W_79140 : bv 32 := 0x02061e63.
Lemma F_79140 : fetch_word AsanUbsan.M.loaded_segments (0x79190 : word) = Some W_79140.
Proof. vm_refl. Qed.
Lemma D_79140 : decode_any W_79140 = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_79144 : bv 32 := 0xd55ff06f.
Lemma F_79144 : fetch_word AsanUbsan.M.loaded_segments (0x79194 : word) = Some W_79144.
Proof. vm_refl. Qed.
Lemma D_79144 : decode_any W_79144 = Some (Jal 0 2096468, 4%Z).
Proof. vm_refl. Qed.

Definition W_79148 : bv 32 := 0x00070783.
Lemma F_79148 : fetch_word AsanUbsan.M.loaded_segments (0x79198 : word) = Some W_79148.
Proof. vm_refl. Qed.
Lemma D_79148 : decode_any W_79148 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7914c : bv 32 := 0x007af813.
Lemma F_7914c : fetch_word AsanUbsan.M.loaded_segments (0x7919c : word) = Some W_7914c.
Proof. vm_refl. Qed.
Lemma D_7914c : decode_any W_7914c = Some (OpImm ALU_AND 16 21 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_79150 : bv 32 := 0x00f038b3.
Lemma F_79150 : fetch_word AsanUbsan.M.loaded_segments (0x791a0 : word) = Some W_79150.
Proof. vm_refl. Qed.
Lemma D_79150 : decode_any W_79150 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_79154 : bv 32 := 0x00f827b3.
Lemma F_79154 : fetch_word AsanUbsan.M.loaded_segments (0x791a4 : word) = Some W_79154.
Proof. vm_refl. Qed.
Lemma D_79154 : decode_any W_79154 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_79158 : bv 32 := 0x0017c793.
Lemma F_79158 : fetch_word AsanUbsan.M.loaded_segments (0x791a8 : word) = Some W_79158.
Proof. vm_refl. Qed.
Lemma D_79158 : decode_any W_79158 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7915c : bv 32 := 0x00f8f7b3.
Lemma F_7915c : fetch_word AsanUbsan.M.loaded_segments (0x791ac : word) = Some W_7915c.
Proof. vm_refl. Qed.
Lemma D_7915c : decode_any W_7915c = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_79160 : bv 32 := 0x00e6fa63.
Lemma F_79160 : fetch_word AsanUbsan.M.loaded_segments (0x791b0 : word) = Some W_79160.
Proof. vm_refl. Qed.
Lemma D_79160 : decode_any W_79160 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_79164 : bv 32 := 0x0006c803.
Lemma F_79164 : fetch_word AsanUbsan.M.loaded_segments (0x791b4 : word) = Some W_79164.
Proof. vm_refl. Qed.
Lemma D_79164 : decode_any W_79164 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79168 : bv 32 := 0x00168693.
Lemma F_79168 : fetch_word AsanUbsan.M.loaded_segments (0x791b8 : word) = Some W_79168.
Proof. vm_refl. Qed.
Lemma D_79168 : decode_any W_79168 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7916c : bv 32 := 0x00f867b3.
Lemma F_7916c : fetch_word AsanUbsan.M.loaded_segments (0x791bc : word) = Some W_7916c.
Proof. vm_refl. Qed.
Lemma D_7916c : decode_any W_7916c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_79170 : bv 32 := 0xfee69ae3.
Lemma F_79170 : fetch_word AsanUbsan.M.loaded_segments (0x791c0 : word) = Some W_79170.
Proof. vm_refl. Qed.
Lemma D_79170 : decode_any W_79170 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_79174 : bv 32 := 0x0ff7f693.
Lemma F_79174 : fetch_word AsanUbsan.M.loaded_segments (0x791c4 : word) = Some W_79174.
Proof. vm_refl. Qed.
Lemma D_79174 : decode_any W_79174 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_79178 : bv 32 := 0xd20680e3.
Lemma F_79178 : fetch_word AsanUbsan.M.loaded_segments (0x791c8 : word) = Some W_79178.
Proof. vm_refl. Qed.
Lemma D_79178 : decode_any W_79178 = Some (Branch BC_EQ 13 0 7456, 4%Z).
Proof. vm_refl. Qed.

Definition W_7917c : bv 32 := 0x00050a93.
Lemma F_7917c : fetch_word AsanUbsan.M.loaded_segments (0x791cc : word) = Some W_7917c.
Proof. vm_refl. Qed.
Lemma D_7917c : decode_any W_7917c = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79180 : bv 32 := 0x00058513.
Lemma F_79180 : fetch_word AsanUbsan.M.loaded_segments (0x791d0 : word) = Some W_79180.
Proof. vm_refl. Qed.
Lemma D_79180 : decode_any W_79180 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79184 : bv 32 := 0x00058b93.
Lemma F_79184 : fetch_word AsanUbsan.M.loaded_segments (0x791d4 : word) = Some W_79184.
Proof. vm_refl. Qed.
Lemma D_79184 : decode_any W_79184 = Some (OpImm ALU_ADD 23 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79188 : bv 32 := 0x00060593.
Lemma F_79188 : fetch_word AsanUbsan.M.loaded_segments (0x791d8 : word) = Some W_79188.
Proof. vm_refl. Qed.
Lemma D_79188 : decode_any W_79188 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7918c : bv 32 := 0x00060493.
Lemma F_7918c : fetch_word AsanUbsan.M.loaded_segments (0x791dc : word) = Some W_7918c.
Proof. vm_refl. Qed.
Lemma D_7918c : decode_any W_7918c = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79190 : bv 32 := 0x48c030ef.
Lemma F_79190 : fetch_word AsanUbsan.M.loaded_segments (0x791e0 : word) = Some W_79190.
Proof. vm_refl. Qed.
Lemma D_79190 : decode_any W_79190 = Some (Jal 1 13452, 4%Z).
Proof. vm_refl. Qed.

Definition W_79194 : bv 32 := 0x000b8593.
Lemma F_79194 : fetch_word AsanUbsan.M.loaded_segments (0x791e4 : word) = Some W_79194.
Proof. vm_refl. Qed.
Lemma D_79194 : decode_any W_79194 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79198 : bv 32 := 0x00048613.
Lemma F_79198 : fetch_word AsanUbsan.M.loaded_segments (0x791e8 : word) = Some W_79198.
Proof. vm_refl. Qed.
Lemma D_79198 : decode_any W_79198 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7919c : bv 32 := 0x00050913.
Lemma F_7919c : fetch_word AsanUbsan.M.loaded_segments (0x791ec : word) = Some W_7919c.
Proof. vm_refl. Qed.
Lemma D_7919c : decode_any W_7919c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_791a0 : bv 32 := 0x000a8513.
Lemma F_791a0 : fetch_word AsanUbsan.M.loaded_segments (0x791f0 : word) = Some W_791a0.
Proof. vm_refl. Qed.
Lemma D_791a0 : decode_any W_791a0 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_791a4 : bv 32 := 0xce090ae3.
Lemma F_791a4 : fetch_word AsanUbsan.M.loaded_segments (0x791f4 : word) = Some W_791a4.
Proof. vm_refl. Qed.
Lemma D_791a4 : decode_any W_791a4 = Some (Branch BC_EQ 18 0 7412, 4%Z).
Proof. vm_refl. Qed.

Definition W_791ec : bv 32 := 0x00070783.
Lemma F_791ec : fetch_word AsanUbsan.M.loaded_segments (0x7923c : word) = Some W_791ec.
Proof. vm_refl. Qed.
Lemma D_791ec : decode_any W_791ec = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_791f0 : bv 32 := 0x0079f813.
Lemma F_791f0 : fetch_word AsanUbsan.M.loaded_segments (0x79240 : word) = Some W_791f0.
Proof. vm_refl. Qed.
Lemma D_791f0 : decode_any W_791f0 = Some (OpImm ALU_AND 16 19 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_791f4 : bv 32 := 0x00f038b3.
Lemma F_791f4 : fetch_word AsanUbsan.M.loaded_segments (0x79244 : word) = Some W_791f4.
Proof. vm_refl. Qed.
Lemma D_791f4 : decode_any W_791f4 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_791f8 : bv 32 := 0x00f827b3.
Lemma F_791f8 : fetch_word AsanUbsan.M.loaded_segments (0x79248 : word) = Some W_791f8.
Proof. vm_refl. Qed.
Lemma D_791f8 : decode_any W_791f8 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_791fc : bv 32 := 0x0017c793.
Lemma F_791fc : fetch_word AsanUbsan.M.loaded_segments (0x7924c : word) = Some W_791fc.
Proof. vm_refl. Qed.
Lemma D_791fc : decode_any W_791fc = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_79200 : bv 32 := 0x00f8f7b3.
Lemma F_79200 : fetch_word AsanUbsan.M.loaded_segments (0x79250 : word) = Some W_79200.
Proof. vm_refl. Qed.
Lemma D_79200 : decode_any W_79200 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_79204 : bv 32 := 0x00e6fa63.
Lemma F_79204 : fetch_word AsanUbsan.M.loaded_segments (0x79254 : word) = Some W_79204.
Proof. vm_refl. Qed.
Lemma D_79204 : decode_any W_79204 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_79208 : bv 32 := 0x0006c803.
Lemma F_79208 : fetch_word AsanUbsan.M.loaded_segments (0x79258 : word) = Some W_79208.
Proof. vm_refl. Qed.
Lemma D_79208 : decode_any W_79208 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7920c : bv 32 := 0x00168693.
Lemma F_7920c : fetch_word AsanUbsan.M.loaded_segments (0x7925c : word) = Some W_7920c.
Proof. vm_refl. Qed.
Lemma D_7920c : decode_any W_7920c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_79210 : bv 32 := 0x00f867b3.
Lemma F_79210 : fetch_word AsanUbsan.M.loaded_segments (0x79260 : word) = Some W_79210.
Proof. vm_refl. Qed.
Lemma D_79210 : decode_any W_79210 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_79214 : bv 32 := 0xfee69ae3.
Lemma F_79214 : fetch_word AsanUbsan.M.loaded_segments (0x79264 : word) = Some W_79214.
Proof. vm_refl. Qed.
Lemma D_79214 : decode_any W_79214 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_79218 : bv 32 := 0x0ff7f693.
Lemma F_79218 : fetch_word AsanUbsan.M.loaded_segments (0x79268 : word) = Some W_79218.
Proof. vm_refl. Qed.
Lemma D_79218 : decode_any W_79218 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7921c : bv 32 := 0xcc0682e3.
Lemma F_7921c : fetch_word AsanUbsan.M.loaded_segments (0x7926c : word) = Some W_7921c.
Proof. vm_refl. Qed.
Lemma D_7921c : decode_any W_7921c = Some (Branch BC_EQ 13 0 7364, 4%Z).
Proof. vm_refl. Qed.

Definition W_79220 : bv 32 := 0x00050493.
Lemma F_79220 : fetch_word AsanUbsan.M.loaded_segments (0x79270 : word) = Some W_79220.
Proof. vm_refl. Qed.
Lemma D_79220 : decode_any W_79220 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79224 : bv 32 := 0x00058a93.
Lemma F_79224 : fetch_word AsanUbsan.M.loaded_segments (0x79274 : word) = Some W_79224.
Proof. vm_refl. Qed.
Lemma D_79224 : decode_any W_79224 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79228 : bv 32 := 0x00060593.
Lemma F_79228 : fetch_word AsanUbsan.M.loaded_segments (0x79278 : word) = Some W_79228.
Proof. vm_refl. Qed.
Lemma D_79228 : decode_any W_79228 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7922c : bv 32 := 0x00060913.
Lemma F_7922c : fetch_word AsanUbsan.M.loaded_segments (0x7927c : word) = Some W_7922c.
Proof. vm_refl. Qed.
Lemma D_7922c : decode_any W_7922c = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79230 : bv 32 := 0x3ec030ef.
Lemma F_79230 : fetch_word AsanUbsan.M.loaded_segments (0x79280 : word) = Some W_79230.
Proof. vm_refl. Qed.
Lemma D_79230 : decode_any W_79230 = Some (Jal 1 13292, 4%Z).
Proof. vm_refl. Qed.

Definition W_79234 : bv 32 := 0x000a8593.
Lemma F_79234 : fetch_word AsanUbsan.M.loaded_segments (0x79284 : word) = Some W_79234.
Proof. vm_refl. Qed.
Lemma D_79234 : decode_any W_79234 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79238 : bv 32 := 0x00090613.
Lemma F_79238 : fetch_word AsanUbsan.M.loaded_segments (0x79288 : word) = Some W_79238.
Proof. vm_refl. Qed.
Lemma D_79238 : decode_any W_79238 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7923c : bv 32 := 0x00050993.
Lemma F_7923c : fetch_word AsanUbsan.M.loaded_segments (0x7928c : word) = Some W_7923c.
Proof. vm_refl. Qed.
Lemma D_7923c : decode_any W_7923c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79240 : bv 32 := 0x00048513.
Lemma F_79240 : fetch_word AsanUbsan.M.loaded_segments (0x79290 : word) = Some W_79240.
Proof. vm_refl. Qed.
Lemma D_79240 : decode_any W_79240 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79244 : bv 32 := 0xc8098ee3.
Lemma F_79244 : fetch_word AsanUbsan.M.loaded_segments (0x79294 : word) = Some W_79244.
Proof. vm_refl. Qed.
Lemma D_79244 : decode_any W_79244 = Some (Branch BC_EQ 19 0 7324, 4%Z).
Proof. vm_refl. Qed.

Definition W_7928c : bv 32 := 0x81010113.
Lemma F_7928c : fetch_word AsanUbsan.M.loaded_segments (0x792dc : word) = Some W_7928c.
Proof. vm_refl. Qed.
Lemma D_7928c : decode_any W_7928c = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_79290 : bv 32 := 0x7e113423.
Lemma F_79290 : fetch_word AsanUbsan.M.loaded_segments (0x792e0 : word) = Some W_79290.
Proof. vm_refl. Qed.
Lemma D_79290 : decode_any W_79290 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_79294 : bv 32 := 0x7e813023.
Lemma F_79294 : fetch_word AsanUbsan.M.loaded_segments (0x792e4 : word) = Some W_79294.
Proof. vm_refl. Qed.
Lemma D_79294 : decode_any W_79294 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_79298 : bv 32 := 0x7c913c23.
Lemma F_79298 : fetch_word AsanUbsan.M.loaded_segments (0x792e8 : word) = Some W_79298.
Proof. vm_refl. Qed.
Lemma D_79298 : decode_any W_79298 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7929c : bv 32 := 0x7d213823.
Lemma F_7929c : fetch_word AsanUbsan.M.loaded_segments (0x792ec : word) = Some W_7929c.
Proof. vm_refl. Qed.
Lemma D_7929c : decode_any W_7929c = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_792a0 : bv 32 := 0x7d313423.
Lemma F_792a0 : fetch_word AsanUbsan.M.loaded_segments (0x792f0 : word) = Some W_792a0.
Proof. vm_refl. Qed.
Lemma D_792a0 : decode_any W_792a0 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_792a4 : bv 32 := 0x7d413023.
Lemma F_792a4 : fetch_word AsanUbsan.M.loaded_segments (0x792f4 : word) = Some W_792a4.
Proof. vm_refl. Qed.
Lemma D_792a4 : decode_any W_792a4 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_792a8 : bv 32 := 0x7b513c23.
Lemma F_792a8 : fetch_word AsanUbsan.M.loaded_segments (0x792f8 : word) = Some W_792a8.
Proof. vm_refl. Qed.
Lemma D_792a8 : decode_any W_792a8 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_792ac : bv 32 := 0x7f010413.
Lemma F_792ac : fetch_word AsanUbsan.M.loaded_segments (0x792fc : word) = Some W_792ac.
Proof. vm_refl. Qed.
Lemma D_792ac : decode_any W_792ac = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_792b0 : bv 32 := 0xfa010113.
Lemma F_792b0 : fetch_word AsanUbsan.M.loaded_segments (0x79300 : word) = Some W_792b0.
Proof. vm_refl. Qed.
Lemma D_792b0 : decode_any W_792b0 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_792b4 : bv 32 := 0x000c5697.
Lemma F_792b4 : fetch_word AsanUbsan.M.loaded_segments (0x79304 : word) = Some W_792b4.
Proof. vm_refl. Qed.
Lemma D_792b4 : decode_any W_792b4 = Some (Auipc 13 197, 4%Z).
Proof. vm_refl. Qed.

Definition W_792b8 : bv 32 := 0x12c6b683.
Lemma F_792b8 : fetch_word AsanUbsan.M.loaded_segments (0x79308 : word) = Some W_792b8.
Proof. vm_refl. Qed.
Lemma D_792b8 : decode_any W_792b8 = Some (Load SZ8 true 13 13 300, 4%Z).
Proof. vm_refl. Qed.

Definition W_792bc : bv 32 := 0x0006c683.
Lemma F_792bc : fetch_word AsanUbsan.M.loaded_segments (0x7930c : word) = Some W_792bc.
Proof. vm_refl. Qed.
Lemma D_792bc : decode_any W_792bc = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_792c0 : bv 32 := 0x08068863.
Lemma F_792c0 : fetch_word AsanUbsan.M.loaded_segments (0x79310 : word) = Some W_792c0.
Proof. vm_refl. Qed.
Lemma D_792c0 : decode_any W_792c0 = Some (Branch BC_EQ 13 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_792c4 : bv 32 := 0xfff54693.
Lemma F_792c4 : fetch_word AsanUbsan.M.loaded_segments (0x79314 : word) = Some W_792c4.
Proof. vm_refl. Qed.
Lemma D_792c4 : decode_any W_792c4 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_792c8 : bv 32 := 0x80040a13.
Lemma F_792c8 : fetch_word AsanUbsan.M.loaded_segments (0x79318 : word) = Some W_792c8.
Proof. vm_refl. Qed.
Lemma D_792c8 : decode_any W_792c8 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_792cc : bv 32 := 0xfb0a0a13.
Lemma F_792cc : fetch_word AsanUbsan.M.loaded_segments (0x7931c : word) = Some W_792cc.
Proof. vm_refl. Qed.
Lemma D_792cc : decode_any W_792cc = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_792d0 : bv 32 := 0x0cc6e663.
Lemma F_792d0 : fetch_word AsanUbsan.M.loaded_segments (0x79320 : word) = Some W_792d0.
Proof. vm_refl. Qed.
Lemma D_792d0 : decode_any W_792d0 = Some (Branch BC_LTU 13 12 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_792d4 : bv 32 := 0xfbf60693.
Lemma F_792d4 : fetch_word AsanUbsan.M.loaded_segments (0x79324 : word) = Some W_792d4.
Proof. vm_refl. Qed.
Lemma D_792d4 : decode_any W_792d4 = Some (OpImm ALU_ADD 13 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_792d8 : bv 32 := 0xfbf00713.
Lemma F_792d8 : fetch_word AsanUbsan.M.loaded_segments (0x79328 : word) = Some W_792d8.
Proof. vm_refl. Qed.
Lemma D_792d8 : decode_any W_792d8 = Some (OpImm ALU_ADD 14 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_792dc : bv 32 := 0x14d77463.
Lemma F_792dc : fetch_word AsanUbsan.M.loaded_segments (0x7932c : word) = Some W_792dc.
Proof. vm_refl. Qed.
Lemma D_792dc : decode_any W_792dc = Some (Branch BC_GEU 14 13 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_792e0 : bv 32 := 0x000c4697.
Lemma F_792e0 : fetch_word AsanUbsan.M.loaded_segments (0x79330 : word) = Some W_792e0.
Proof. vm_refl. Qed.
Lemma D_792e0 : decode_any W_792e0 = Some (Auipc 13 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_792e4 : bv 32 := 0x5986b683.
Lemma F_792e4 : fetch_word AsanUbsan.M.loaded_segments (0x79334 : word) = Some W_792e4.
Proof. vm_refl. Qed.
Lemma D_792e4 : decode_any W_792e4 = Some (Load SZ8 true 13 13 1432, 4%Z).
Proof. vm_refl. Qed.

Definition W_792e8 : bv 32 := 0x00c507b3.
Lemma F_792e8 : fetch_word AsanUbsan.M.loaded_segments (0x79338 : word) = Some W_792e8.
Proof. vm_refl. Qed.
Lemma D_792e8 : decode_any W_792e8 = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_792ec : bv 32 := 0x0006b703.
Lemma F_792ec : fetch_word AsanUbsan.M.loaded_segments (0x7933c : word) = Some W_792ec.
Proof. vm_refl. Qed.
Lemma D_792ec : decode_any W_792ec = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_792f0 : bv 32 := 0x00355693.
Lemma F_792f0 : fetch_word AsanUbsan.M.loaded_segments (0x79340 : word) = Some W_792f0.
Proof. vm_refl. Qed.
Lemma D_792f0 : decode_any W_792f0 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_792f4 : bv 32 := 0xfff78793.
Lemma F_792f4 : fetch_word AsanUbsan.M.loaded_segments (0x79344 : word) = Some W_792f4.
Proof. vm_refl. Qed.
Lemma D_792f4 : decode_any W_792f4 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_792f8 : bv 32 := 0x0037d813.
Lemma F_792f8 : fetch_word AsanUbsan.M.loaded_segments (0x79348 : word) = Some W_792f8.
Proof. vm_refl. Qed.
Lemma D_792f8 : decode_any W_792f8 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_792fc : bv 32 := 0x00d706b3.
Lemma F_792fc : fetch_word AsanUbsan.M.loaded_segments (0x7934c : word) = Some W_792fc.
Proof. vm_refl. Qed.
Lemma D_792fc : decode_any W_792fc = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_79300 : bv 32 := 0x01070733.
Lemma F_79300 : fetch_word AsanUbsan.M.loaded_segments (0x79350 : word) = Some W_79300.
Proof. vm_refl. Qed.
Lemma D_79300 : decode_any W_79300 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_79304 : bv 32 := 0xff86f813.
Lemma F_79304 : fetch_word AsanUbsan.M.loaded_segments (0x79354 : word) = Some W_79304.
Proof. vm_refl. Qed.
Lemma D_79304 : decode_any W_79304 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_79308 : bv 32 := 0xff877893.
Lemma F_79308 : fetch_word AsanUbsan.M.loaded_segments (0x79358 : word) = Some W_79308.
Proof. vm_refl. Qed.
Lemma D_79308 : decode_any W_79308 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7930c : bv 32 := 0x00083803.
Lemma F_7930c : fetch_word AsanUbsan.M.loaded_segments (0x7935c : word) = Some W_7930c.
Proof. vm_refl. Qed.
Lemma D_7930c : decode_any W_7930c = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79310 : bv 32 := 0x0008b883.
Lemma F_79310 : fetch_word AsanUbsan.M.loaded_segments (0x79360 : word) = Some W_79310.
Proof. vm_refl. Qed.
Lemma D_79310 : decode_any W_79310 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79314 : bv 32 := 0x0108e833.
Lemma F_79314 : fetch_word AsanUbsan.M.loaded_segments (0x79364 : word) = Some W_79314.
Proof. vm_refl. Qed.
Lemma D_79314 : decode_any W_79314 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_79318 : bv 32 := 0x10081a63.
Lemma F_79318 : fetch_word AsanUbsan.M.loaded_segments (0x79368 : word) = Some W_79318.
Proof. vm_refl. Qed.
Lemma D_79318 : decode_any W_79318 = Some (Branch BC_NE 16 0 276, 4%Z).
Proof. vm_refl. Qed.

Definition W_7931c : bv 32 := 0x000c6697.
Lemma F_7931c : fetch_word AsanUbsan.M.loaded_segments (0x7936c : word) = Some W_7931c.
Proof. vm_refl. Qed.
Lemma D_7931c : decode_any W_7931c = Some (Auipc 13 198, 4%Z).
Proof. vm_refl. Qed.

Definition W_79320 : bv 32 := 0x56c6b683.
Lemma F_79320 : fetch_word AsanUbsan.M.loaded_segments (0x79370 : word) = Some W_79320.
Proof. vm_refl. Qed.
Lemma D_79320 : decode_any W_79320 = Some (Load SZ8 true 13 13 1388, 4%Z).
Proof. vm_refl. Qed.

Definition W_79324 : bv 32 := 0x000680e7.
Lemma F_79324 : fetch_word AsanUbsan.M.loaded_segments (0x79374 : word) = Some W_79324.
Proof. vm_refl. Qed.
Lemma D_79324 : decode_any W_79324 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79328 : bv 32 := 0x06010113.
Lemma F_79328 : fetch_word AsanUbsan.M.loaded_segments (0x79378 : word) = Some W_79328.
Proof. vm_refl. Qed.
Lemma D_79328 : decode_any W_79328 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_7932c : bv 32 := 0x7e813083.
Lemma F_7932c : fetch_word AsanUbsan.M.loaded_segments (0x7937c : word) = Some W_7932c.
Proof. vm_refl. Qed.
Lemma D_7932c : decode_any W_7932c = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_79330 : bv 32 := 0x7e013403.
Lemma F_79330 : fetch_word AsanUbsan.M.loaded_segments (0x79380 : word) = Some W_79330.
Proof. vm_refl. Qed.
Lemma D_79330 : decode_any W_79330 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_79334 : bv 32 := 0x7d813483.
Lemma F_79334 : fetch_word AsanUbsan.M.loaded_segments (0x79384 : word) = Some W_79334.
Proof. vm_refl. Qed.
Lemma D_79334 : decode_any W_79334 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_79338 : bv 32 := 0x7d013903.
Lemma F_79338 : fetch_word AsanUbsan.M.loaded_segments (0x79388 : word) = Some W_79338.
Proof. vm_refl. Qed.
Lemma D_79338 : decode_any W_79338 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7933c : bv 32 := 0x7c813983.
Lemma F_7933c : fetch_word AsanUbsan.M.loaded_segments (0x7938c : word) = Some W_7933c.
Proof. vm_refl. Qed.
Lemma D_7933c : decode_any W_7933c = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_79340 : bv 32 := 0x7c013a03.
Lemma F_79340 : fetch_word AsanUbsan.M.loaded_segments (0x79390 : word) = Some W_79340.
Proof. vm_refl. Qed.
Lemma D_79340 : decode_any W_79340 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_79344 : bv 32 := 0x7b813a83.
Lemma F_79344 : fetch_word AsanUbsan.M.loaded_segments (0x79394 : word) = Some W_79344.
Proof. vm_refl. Qed.
Lemma D_79344 : decode_any W_79344 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_79348 : bv 32 := 0x7f010113.
Lemma F_79348 : fetch_word AsanUbsan.M.loaded_segments (0x79398 : word) = Some W_79348.
Proof. vm_refl. Qed.
Lemma D_79348 : decode_any W_79348 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7934c : bv 32 := 0x00008067.
Lemma F_7934c : fetch_word AsanUbsan.M.loaded_segments (0x7939c : word) = Some W_7934c.
Proof. vm_refl. Qed.
Lemma D_7934c : decode_any W_7934c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79424 : bv 32 := 0x02061e63.
Lemma F_79424 : fetch_word AsanUbsan.M.loaded_segments (0x79474 : word) = Some W_79424.
Proof. vm_refl. Qed.
Lemma D_79424 : decode_any W_79424 = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_79428 : bv 32 := 0xef5ff06f.
Lemma F_79428 : fetch_word AsanUbsan.M.loaded_segments (0x79478 : word) = Some W_79428.
Proof. vm_refl. Qed.
Lemma D_79428 : decode_any W_79428 = Some (Jal 0 2096884, 4%Z).
Proof. vm_refl. Qed.

Definition W_7942c : bv 32 := 0x00070803.
Lemma F_7942c : fetch_word AsanUbsan.M.loaded_segments (0x7947c : word) = Some W_7942c.
Proof. vm_refl. Qed.
Lemma D_7942c : decode_any W_7942c = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79430 : bv 32 := 0x0077f793.
Lemma F_79430 : fetch_word AsanUbsan.M.loaded_segments (0x79480 : word) = Some W_79430.
Proof. vm_refl. Qed.
Lemma D_79430 : decode_any W_79430 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_79434 : bv 32 := 0x010038b3.
Lemma F_79434 : fetch_word AsanUbsan.M.loaded_segments (0x79484 : word) = Some W_79434.
Proof. vm_refl. Qed.
Lemma D_79434 : decode_any W_79434 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_79438 : bv 32 := 0x0107a7b3.
Lemma F_79438 : fetch_word AsanUbsan.M.loaded_segments (0x79488 : word) = Some W_79438.
Proof. vm_refl. Qed.
Lemma D_79438 : decode_any W_79438 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7943c : bv 32 := 0x0017c793.
Lemma F_7943c : fetch_word AsanUbsan.M.loaded_segments (0x7948c : word) = Some W_7943c.
Proof. vm_refl. Qed.
Lemma D_7943c : decode_any W_7943c = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_79440 : bv 32 := 0x00f8f7b3.
Lemma F_79440 : fetch_word AsanUbsan.M.loaded_segments (0x79490 : word) = Some W_79440.
Proof. vm_refl. Qed.
Lemma D_79440 : decode_any W_79440 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_79444 : bv 32 := 0x00e6fa63.
Lemma F_79444 : fetch_word AsanUbsan.M.loaded_segments (0x79494 : word) = Some W_79444.
Proof. vm_refl. Qed.
Lemma D_79444 : decode_any W_79444 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_79448 : bv 32 := 0x0006c803.
Lemma F_79448 : fetch_word AsanUbsan.M.loaded_segments (0x79498 : word) = Some W_79448.
Proof. vm_refl. Qed.
Lemma D_79448 : decode_any W_79448 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7944c : bv 32 := 0x00168693.
Lemma F_7944c : fetch_word AsanUbsan.M.loaded_segments (0x7949c : word) = Some W_7944c.
Proof. vm_refl. Qed.
Lemma D_7944c : decode_any W_7944c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_79450 : bv 32 := 0x00f867b3.
Lemma F_79450 : fetch_word AsanUbsan.M.loaded_segments (0x794a0 : word) = Some W_79450.
Proof. vm_refl. Qed.
Lemma D_79450 : decode_any W_79450 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_79454 : bv 32 := 0xfee69ae3.
Lemma F_79454 : fetch_word AsanUbsan.M.loaded_segments (0x794a4 : word) = Some W_79454.
Proof. vm_refl. Qed.
Lemma D_79454 : decode_any W_79454 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_79458 : bv 32 := 0x0ff7f693.
Lemma F_79458 : fetch_word AsanUbsan.M.loaded_segments (0x794a8 : word) = Some W_79458.
Proof. vm_refl. Qed.
Lemma D_79458 : decode_any W_79458 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7945c : bv 32 := 0xec0680e3.
Lemma F_7945c : fetch_word AsanUbsan.M.loaded_segments (0x794ac : word) = Some W_7945c.
Proof. vm_refl. Qed.
Lemma D_7945c : decode_any W_7945c = Some (Branch BC_EQ 13 0 7872, 4%Z).
Proof. vm_refl. Qed.

Definition W_79460 : bv 32 := 0x00050493.
Lemma F_79460 : fetch_word AsanUbsan.M.loaded_segments (0x794b0 : word) = Some W_79460.
Proof. vm_refl. Qed.
Lemma D_79460 : decode_any W_79460 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79464 : bv 32 := 0x00058a93.
Lemma F_79464 : fetch_word AsanUbsan.M.loaded_segments (0x794b4 : word) = Some W_79464.
Proof. vm_refl. Qed.
Lemma D_79464 : decode_any W_79464 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79468 : bv 32 := 0x00060593.
Lemma F_79468 : fetch_word AsanUbsan.M.loaded_segments (0x794b8 : word) = Some W_79468.
Proof. vm_refl. Qed.
Lemma D_79468 : decode_any W_79468 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7946c : bv 32 := 0x00060913.
Lemma F_7946c : fetch_word AsanUbsan.M.loaded_segments (0x794bc : word) = Some W_7946c.
Proof. vm_refl. Qed.
Lemma D_7946c : decode_any W_7946c = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79470 : bv 32 := 0x1ac030ef.
Lemma F_79470 : fetch_word AsanUbsan.M.loaded_segments (0x794c0 : word) = Some W_79470.
Proof. vm_refl. Qed.
Lemma D_79470 : decode_any W_79470 = Some (Jal 1 12716, 4%Z).
Proof. vm_refl. Qed.

Definition W_79474 : bv 32 := 0x000a8593.
Lemma F_79474 : fetch_word AsanUbsan.M.loaded_segments (0x794c4 : word) = Some W_79474.
Proof. vm_refl. Qed.
Lemma D_79474 : decode_any W_79474 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79478 : bv 32 := 0x00090613.
Lemma F_79478 : fetch_word AsanUbsan.M.loaded_segments (0x794c8 : word) = Some W_79478.
Proof. vm_refl. Qed.
Lemma D_79478 : decode_any W_79478 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7947c : bv 32 := 0x00050993.
Lemma F_7947c : fetch_word AsanUbsan.M.loaded_segments (0x794cc : word) = Some W_7947c.
Proof. vm_refl. Qed.
Lemma D_7947c : decode_any W_7947c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79480 : bv 32 := 0x00048513.
Lemma F_79480 : fetch_word AsanUbsan.M.loaded_segments (0x794d0 : word) = Some W_79480.
Proof. vm_refl. Qed.
Lemma D_79480 : decode_any W_79480 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79484 : bv 32 := 0xe8098ce3.
Lemma F_79484 : fetch_word AsanUbsan.M.loaded_segments (0x794d4 : word) = Some W_79484.
Proof. vm_refl. Qed.
Lemma D_79484 : decode_any W_79484 = Some (Branch BC_EQ 19 0 7832, 4%Z).
Proof. vm_refl. Qed.

Definition W_794cc : bv 32 := 0x81010113.
Lemma F_794cc : fetch_word AsanUbsan.M.loaded_segments (0x7951c : word) = Some W_794cc.
Proof. vm_refl. Qed.
Lemma D_794cc : decode_any W_794cc = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_794d0 : bv 32 := 0x7e113423.
Lemma F_794d0 : fetch_word AsanUbsan.M.loaded_segments (0x79520 : word) = Some W_794d0.
Proof. vm_refl. Qed.
Lemma D_794d0 : decode_any W_794d0 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_794d4 : bv 32 := 0x7e813023.
Lemma F_794d4 : fetch_word AsanUbsan.M.loaded_segments (0x79524 : word) = Some W_794d4.
Proof. vm_refl. Qed.
Lemma D_794d4 : decode_any W_794d4 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_794d8 : bv 32 := 0x7c913c23.
Lemma F_794d8 : fetch_word AsanUbsan.M.loaded_segments (0x79528 : word) = Some W_794d8.
Proof. vm_refl. Qed.
Lemma D_794d8 : decode_any W_794d8 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_794dc : bv 32 := 0x7d213823.
Lemma F_794dc : fetch_word AsanUbsan.M.loaded_segments (0x7952c : word) = Some W_794dc.
Proof. vm_refl. Qed.
Lemma D_794dc : decode_any W_794dc = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_794e0 : bv 32 := 0x7d313423.
Lemma F_794e0 : fetch_word AsanUbsan.M.loaded_segments (0x79530 : word) = Some W_794e0.
Proof. vm_refl. Qed.
Lemma D_794e0 : decode_any W_794e0 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_794e4 : bv 32 := 0x7d413023.
Lemma F_794e4 : fetch_word AsanUbsan.M.loaded_segments (0x79534 : word) = Some W_794e4.
Proof. vm_refl. Qed.
Lemma D_794e4 : decode_any W_794e4 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_794e8 : bv 32 := 0x7b513c23.
Lemma F_794e8 : fetch_word AsanUbsan.M.loaded_segments (0x79538 : word) = Some W_794e8.
Proof. vm_refl. Qed.
Lemma D_794e8 : decode_any W_794e8 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_794ec : bv 32 := 0x7b613823.
Lemma F_794ec : fetch_word AsanUbsan.M.loaded_segments (0x7953c : word) = Some W_794ec.
Proof. vm_refl. Qed.
Lemma D_794ec : decode_any W_794ec = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_794f0 : bv 32 := 0x7f010413.
Lemma F_794f0 : fetch_word AsanUbsan.M.loaded_segments (0x79540 : word) = Some W_794f0.
Proof. vm_refl. Qed.
Lemma D_794f0 : decode_any W_794f0 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_794f4 : bv 32 := 0xf9010113.
Lemma F_794f4 : fetch_word AsanUbsan.M.loaded_segments (0x79544 : word) = Some W_794f4.
Proof. vm_refl. Qed.
Lemma D_794f4 : decode_any W_794f4 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_794f8 : bv 32 := 0x000c5697.
Lemma F_794f8 : fetch_word AsanUbsan.M.loaded_segments (0x79548 : word) = Some W_794f8.
Proof. vm_refl. Qed.
Lemma D_794f8 : decode_any W_794f8 = Some (Auipc 13 197, 4%Z).
Proof. vm_refl. Qed.

Definition W_794fc : bv 32 := 0xee86b683.
Lemma F_794fc : fetch_word AsanUbsan.M.loaded_segments (0x7954c : word) = Some W_794fc.
Proof. vm_refl. Qed.
Lemma D_794fc : decode_any W_794fc = Some (Load SZ8 true 13 13 3816, 4%Z).
Proof. vm_refl. Qed.

Definition W_79500 : bv 32 := 0x0006c683.
Lemma F_79500 : fetch_word AsanUbsan.M.loaded_segments (0x79550 : word) = Some W_79500.
Proof. vm_refl. Qed.
Lemma D_79500 : decode_any W_79500 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79504 : bv 32 := 0x0a068463.
Lemma F_79504 : fetch_word AsanUbsan.M.loaded_segments (0x79554 : word) = Some W_79504.
Proof. vm_refl. Qed.
Lemma D_79504 : decode_any W_79504 = Some (Branch BC_EQ 13 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_79508 : bv 32 := 0xfff5c693.
Lemma F_79508 : fetch_word AsanUbsan.M.loaded_segments (0x79558 : word) = Some W_79508.
Proof. vm_refl. Qed.
Lemma D_79508 : decode_any W_79508 = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7950c : bv 32 := 0x80040a13.
Lemma F_7950c : fetch_word AsanUbsan.M.loaded_segments (0x7955c : word) = Some W_7950c.
Proof. vm_refl. Qed.
Lemma D_7950c : decode_any W_7950c = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_79510 : bv 32 := 0xfa8a0a13.
Lemma F_79510 : fetch_word AsanUbsan.M.loaded_segments (0x79560 : word) = Some W_79510.
Proof. vm_refl. Qed.
Lemma D_79510 : decode_any W_79510 = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_79514 : bv 32 := 0x0cc6e463.
Lemma F_79514 : fetch_word AsanUbsan.M.loaded_segments (0x79564 : word) = Some W_79514.
Proof. vm_refl. Qed.
Lemma D_79514 : decode_any W_79514 = Some (Branch BC_LTU 13 12 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_79518 : bv 32 := 0xfbf60993.
Lemma F_79518 : fetch_word AsanUbsan.M.loaded_segments (0x79568 : word) = Some W_79518.
Proof. vm_refl. Qed.
Lemma D_79518 : decode_any W_79518 = Some (OpImm ALU_ADD 19 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7951c : bv 32 := 0xfbf00693.
Lemma F_7951c : fetch_word AsanUbsan.M.loaded_segments (0x7956c : word) = Some W_7951c.
Proof. vm_refl. Qed.
Lemma D_7951c : decode_any W_7951c = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_79520 : bv 32 := 0x1536f263.
Lemma F_79520 : fetch_word AsanUbsan.M.loaded_segments (0x79570 : word) = Some W_79520.
Proof. vm_refl. Qed.
Lemma D_79520 : decode_any W_79520 = Some (Branch BC_GEU 13 19 324, 4%Z).
Proof. vm_refl. Qed.

Definition W_79524 : bv 32 := 0x000c4697.
Lemma F_79524 : fetch_word AsanUbsan.M.loaded_segments (0x79574 : word) = Some W_79524.
Proof. vm_refl. Qed.
Lemma D_79524 : decode_any W_79524 = Some (Auipc 13 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_79528 : bv 32 := 0x3546b683.
Lemma F_79528 : fetch_word AsanUbsan.M.loaded_segments (0x79578 : word) = Some W_79528.
Proof. vm_refl. Qed.
Lemma D_79528 : decode_any W_79528 = Some (Load SZ8 true 13 13 852, 4%Z).
Proof. vm_refl. Qed.

Definition W_7952c : bv 32 := 0x00c587b3.
Lemma F_7952c : fetch_word AsanUbsan.M.loaded_segments (0x7957c : word) = Some W_7952c.
Proof. vm_refl. Qed.
Lemma D_7952c : decode_any W_7952c = Some (Op ALU_ADD 15 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_79530 : bv 32 := 0x0006b703.
Lemma F_79530 : fetch_word AsanUbsan.M.loaded_segments (0x79580 : word) = Some W_79530.
Proof. vm_refl. Qed.
Lemma D_79530 : decode_any W_79530 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79534 : bv 32 := 0x0035d693.
Lemma F_79534 : fetch_word AsanUbsan.M.loaded_segments (0x79584 : word) = Some W_79534.
Proof. vm_refl. Qed.
Lemma D_79534 : decode_any W_79534 = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_79538 : bv 32 := 0xfff78793.
Lemma F_79538 : fetch_word AsanUbsan.M.loaded_segments (0x79588 : word) = Some W_79538.
Proof. vm_refl. Qed.
Lemma D_79538 : decode_any W_79538 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7953c : bv 32 := 0x0037d813.
Lemma F_7953c : fetch_word AsanUbsan.M.loaded_segments (0x7958c : word) = Some W_7953c.
Proof. vm_refl. Qed.
Lemma D_7953c : decode_any W_7953c = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_79540 : bv 32 := 0x00d706b3.
Lemma F_79540 : fetch_word AsanUbsan.M.loaded_segments (0x79590 : word) = Some W_79540.
Proof. vm_refl. Qed.
Lemma D_79540 : decode_any W_79540 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_79544 : bv 32 := 0x01070733.
Lemma F_79544 : fetch_word AsanUbsan.M.loaded_segments (0x79594 : word) = Some W_79544.
Proof. vm_refl. Qed.
Lemma D_79544 : decode_any W_79544 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_79548 : bv 32 := 0xff86f813.
Lemma F_79548 : fetch_word AsanUbsan.M.loaded_segments (0x79598 : word) = Some W_79548.
Proof. vm_refl. Qed.
Lemma D_79548 : decode_any W_79548 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7954c : bv 32 := 0xff877893.
Lemma F_7954c : fetch_word AsanUbsan.M.loaded_segments (0x7959c : word) = Some W_7954c.
Proof. vm_refl. Qed.
Lemma D_7954c : decode_any W_7954c = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_79550 : bv 32 := 0x00083803.
Lemma F_79550 : fetch_word AsanUbsan.M.loaded_segments (0x795a0 : word) = Some W_79550.
Proof. vm_refl. Qed.
Lemma D_79550 : decode_any W_79550 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79554 : bv 32 := 0x0008b883.
Lemma F_79554 : fetch_word AsanUbsan.M.loaded_segments (0x795a4 : word) = Some W_79554.
Proof. vm_refl. Qed.
Lemma D_79554 : decode_any W_79554 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79558 : bv 32 := 0x0108e833.
Lemma F_79558 : fetch_word AsanUbsan.M.loaded_segments (0x795a8 : word) = Some W_79558.
Proof. vm_refl. Qed.
Lemma D_79558 : decode_any W_79558 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7955c : bv 32 := 0x18081e63.
Lemma F_7955c : fetch_word AsanUbsan.M.loaded_segments (0x795ac : word) = Some W_7955c.
Proof. vm_refl. Qed.
Lemma D_7955c : decode_any W_7955c = Some (Branch BC_NE 16 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_79560 : bv 32 := 0xfff54693.
Lemma F_79560 : fetch_word AsanUbsan.M.loaded_segments (0x795b0 : word) = Some W_79560.
Proof. vm_refl. Qed.
Lemma D_79560 : decode_any W_79560 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_79564 : bv 32 := 0x10c6e463.
Lemma F_79564 : fetch_word AsanUbsan.M.loaded_segments (0x795b4 : word) = Some W_79564.
Proof. vm_refl. Qed.
Lemma D_79564 : decode_any W_79564 = Some (Branch BC_LTU 13 12 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_79568 : bv 32 := 0xfbf00693.
Lemma F_79568 : fetch_word AsanUbsan.M.loaded_segments (0x795b8 : word) = Some W_79568.
Proof. vm_refl. Qed.
Lemma D_79568 : decode_any W_79568 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7956c : bv 32 := 0x1936f263.
Lemma F_7956c : fetch_word AsanUbsan.M.loaded_segments (0x795bc : word) = Some W_7956c.
Proof. vm_refl. Qed.
Lemma D_7956c : decode_any W_7956c = Some (Branch BC_GEU 13 19 388, 4%Z).
Proof. vm_refl. Qed.

Definition W_79570 : bv 32 := 0x000c4697.
Lemma F_79570 : fetch_word AsanUbsan.M.loaded_segments (0x795c0 : word) = Some W_79570.
Proof. vm_refl. Qed.
Lemma D_79570 : decode_any W_79570 = Some (Auipc 13 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_79574 : bv 32 := 0x3086b683.
Lemma F_79574 : fetch_word AsanUbsan.M.loaded_segments (0x795c4 : word) = Some W_79574.
Proof. vm_refl. Qed.
Lemma D_79574 : decode_any W_79574 = Some (Load SZ8 true 13 13 776, 4%Z).
Proof. vm_refl. Qed.

Definition W_79578 : bv 32 := 0x00c507b3.
Lemma F_79578 : fetch_word AsanUbsan.M.loaded_segments (0x795c8 : word) = Some W_79578.
Proof. vm_refl. Qed.
Lemma D_79578 : decode_any W_79578 = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7957c : bv 32 := 0x0006b703.
Lemma F_7957c : fetch_word AsanUbsan.M.loaded_segments (0x795cc : word) = Some W_7957c.
Proof. vm_refl. Qed.
Lemma D_7957c : decode_any W_7957c = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79580 : bv 32 := 0x00355693.
Lemma F_79580 : fetch_word AsanUbsan.M.loaded_segments (0x795d0 : word) = Some W_79580.
Proof. vm_refl. Qed.
Lemma D_79580 : decode_any W_79580 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_79584 : bv 32 := 0xfff78793.
Lemma F_79584 : fetch_word AsanUbsan.M.loaded_segments (0x795d4 : word) = Some W_79584.
Proof. vm_refl. Qed.
Lemma D_79584 : decode_any W_79584 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_79588 : bv 32 := 0x0037d813.
Lemma F_79588 : fetch_word AsanUbsan.M.loaded_segments (0x795d8 : word) = Some W_79588.
Proof. vm_refl. Qed.
Lemma D_79588 : decode_any W_79588 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7958c : bv 32 := 0x00d706b3.
Lemma F_7958c : fetch_word AsanUbsan.M.loaded_segments (0x795dc : word) = Some W_7958c.
Proof. vm_refl. Qed.
Lemma D_7958c : decode_any W_7958c = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_79590 : bv 32 := 0x01070733.
Lemma F_79590 : fetch_word AsanUbsan.M.loaded_segments (0x795e0 : word) = Some W_79590.
Proof. vm_refl. Qed.
Lemma D_79590 : decode_any W_79590 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_79594 : bv 32 := 0xff86f813.
Lemma F_79594 : fetch_word AsanUbsan.M.loaded_segments (0x795e4 : word) = Some W_79594.
Proof. vm_refl. Qed.
Lemma D_79594 : decode_any W_79594 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_79598 : bv 32 := 0xff877893.
Lemma F_79598 : fetch_word AsanUbsan.M.loaded_segments (0x795e8 : word) = Some W_79598.
Proof. vm_refl. Qed.
Lemma D_79598 : decode_any W_79598 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7959c : bv 32 := 0x00083803.
Lemma F_7959c : fetch_word AsanUbsan.M.loaded_segments (0x795ec : word) = Some W_7959c.
Proof. vm_refl. Qed.
Lemma D_7959c : decode_any W_7959c = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_795a0 : bv 32 := 0x0008b883.
Lemma F_795a0 : fetch_word AsanUbsan.M.loaded_segments (0x795f0 : word) = Some W_795a0.
Proof. vm_refl. Qed.
Lemma D_795a0 : decode_any W_795a0 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_795a4 : bv 32 := 0x0108e833.
Lemma F_795a4 : fetch_word AsanUbsan.M.loaded_segments (0x795f4 : word) = Some W_795a4.
Proof. vm_refl. Qed.
Lemma D_795a4 : decode_any W_795a4 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_795a8 : bv 32 := 0x1e081a63.
Lemma F_795a8 : fetch_word AsanUbsan.M.loaded_segments (0x795f8 : word) = Some W_795a8.
Proof. vm_refl. Qed.
Lemma D_795a8 : decode_any W_795a8 = Some (Branch BC_NE 16 0 500, 4%Z).
Proof. vm_refl. Qed.

Definition W_795ac : bv 32 := 0x7b9120ef.
Lemma F_795ac : fetch_word AsanUbsan.M.loaded_segments (0x795fc : word) = Some W_795ac.
Proof. vm_refl. Qed.
Lemma D_795ac : decode_any W_795ac = Some (Jal 1 77752, 4%Z).
Proof. vm_refl. Qed.

Definition W_795b0 : bv 32 := 0x07010113.
Lemma F_795b0 : fetch_word AsanUbsan.M.loaded_segments (0x79600 : word) = Some W_795b0.
Proof. vm_refl. Qed.
Lemma D_795b0 : decode_any W_795b0 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_795b4 : bv 32 := 0x7e813083.
Lemma F_795b4 : fetch_word AsanUbsan.M.loaded_segments (0x79604 : word) = Some W_795b4.
Proof. vm_refl. Qed.
Lemma D_795b4 : decode_any W_795b4 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_795b8 : bv 32 := 0x7e013403.
Lemma F_795b8 : fetch_word AsanUbsan.M.loaded_segments (0x79608 : word) = Some W_795b8.
Proof. vm_refl. Qed.
Lemma D_795b8 : decode_any W_795b8 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_795bc : bv 32 := 0x7d813483.
Lemma F_795bc : fetch_word AsanUbsan.M.loaded_segments (0x7960c : word) = Some W_795bc.
Proof. vm_refl. Qed.
Lemma D_795bc : decode_any W_795bc = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_795c0 : bv 32 := 0x7d013903.
Lemma F_795c0 : fetch_word AsanUbsan.M.loaded_segments (0x79610 : word) = Some W_795c0.
Proof. vm_refl. Qed.
Lemma D_795c0 : decode_any W_795c0 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_795c4 : bv 32 := 0x7c813983.
Lemma F_795c4 : fetch_word AsanUbsan.M.loaded_segments (0x79614 : word) = Some W_795c4.
Proof. vm_refl. Qed.
Lemma D_795c4 : decode_any W_795c4 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_795c8 : bv 32 := 0x7c013a03.
Lemma F_795c8 : fetch_word AsanUbsan.M.loaded_segments (0x79618 : word) = Some W_795c8.
Proof. vm_refl. Qed.
Lemma D_795c8 : decode_any W_795c8 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_795cc : bv 32 := 0x7b813a83.
Lemma F_795cc : fetch_word AsanUbsan.M.loaded_segments (0x7961c : word) = Some W_795cc.
Proof. vm_refl. Qed.
Lemma D_795cc : decode_any W_795cc = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_795d0 : bv 32 := 0x7b013b03.
Lemma F_795d0 : fetch_word AsanUbsan.M.loaded_segments (0x79620 : word) = Some W_795d0.
Proof. vm_refl. Qed.
Lemma D_795d0 : decode_any W_795d0 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_795d4 : bv 32 := 0x7f010113.
Lemma F_795d4 : fetch_word AsanUbsan.M.loaded_segments (0x79624 : word) = Some W_795d4.
Proof. vm_refl. Qed.
Lemma D_795d4 : decode_any W_795d4 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_795d8 : bv 32 := 0x00008067.
Lemma F_795d8 : fetch_word AsanUbsan.M.loaded_segments (0x79628 : word) = Some W_795d8.
Proof. vm_refl. Qed.
Lemma D_795d8 : decode_any W_795d8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79664 : bv 32 := 0x0c061463.
Lemma F_79664 : fetch_word AsanUbsan.M.loaded_segments (0x796b4 : word) = Some W_79664.
Proof. vm_refl. Qed.
Lemma D_79664 : decode_any W_79664 = Some (Branch BC_NE 12 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_79668 : bv 32 := 0xef9ff06f.
Lemma F_79668 : fetch_word AsanUbsan.M.loaded_segments (0x796b8 : word) = Some W_79668.
Proof. vm_refl. Qed.
Lemma D_79668 : decode_any W_79668 = Some (Jal 0 2096888, 4%Z).
Proof. vm_refl. Qed.

Definition W_796f0 : bv 32 := 0x0e061063.
Lemma F_796f0 : fetch_word AsanUbsan.M.loaded_segments (0x79740 : word) = Some W_796f0.
Proof. vm_refl. Qed.
Lemma D_796f0 : decode_any W_796f0 = Some (Branch BC_NE 12 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_796f4 : bv 32 := 0xeb9ff06f.
Lemma F_796f4 : fetch_word AsanUbsan.M.loaded_segments (0x79744 : word) = Some W_796f4.
Proof. vm_refl. Qed.
Lemma D_796f4 : decode_any W_796f4 = Some (Jal 0 2096824, 4%Z).
Proof. vm_refl. Qed.

Definition W_796f8 : bv 32 := 0x00070803.
Lemma F_796f8 : fetch_word AsanUbsan.M.loaded_segments (0x79748 : word) = Some W_796f8.
Proof. vm_refl. Qed.
Lemma D_796f8 : decode_any W_796f8 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_796fc : bv 32 := 0x0077f793.
Lemma F_796fc : fetch_word AsanUbsan.M.loaded_segments (0x7974c : word) = Some W_796fc.
Proof. vm_refl. Qed.
Lemma D_796fc : decode_any W_796fc = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_79700 : bv 32 := 0x010038b3.
Lemma F_79700 : fetch_word AsanUbsan.M.loaded_segments (0x79750 : word) = Some W_79700.
Proof. vm_refl. Qed.
Lemma D_79700 : decode_any W_79700 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_79704 : bv 32 := 0x0107a7b3.
Lemma F_79704 : fetch_word AsanUbsan.M.loaded_segments (0x79754 : word) = Some W_79704.
Proof. vm_refl. Qed.
Lemma D_79704 : decode_any W_79704 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_79708 : bv 32 := 0x0017c793.
Lemma F_79708 : fetch_word AsanUbsan.M.loaded_segments (0x79758 : word) = Some W_79708.
Proof. vm_refl. Qed.
Lemma D_79708 : decode_any W_79708 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7970c : bv 32 := 0x00f8f7b3.
Lemma F_7970c : fetch_word AsanUbsan.M.loaded_segments (0x7975c : word) = Some W_7970c.
Proof. vm_refl. Qed.
Lemma D_7970c : decode_any W_7970c = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_79710 : bv 32 := 0x00e6fa63.
Lemma F_79710 : fetch_word AsanUbsan.M.loaded_segments (0x79760 : word) = Some W_79710.
Proof. vm_refl. Qed.
Lemma D_79710 : decode_any W_79710 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_79714 : bv 32 := 0x0006c803.
Lemma F_79714 : fetch_word AsanUbsan.M.loaded_segments (0x79764 : word) = Some W_79714.
Proof. vm_refl. Qed.
Lemma D_79714 : decode_any W_79714 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79718 : bv 32 := 0x00168693.
Lemma F_79718 : fetch_word AsanUbsan.M.loaded_segments (0x79768 : word) = Some W_79718.
Proof. vm_refl. Qed.
Lemma D_79718 : decode_any W_79718 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7971c : bv 32 := 0x00f867b3.
Lemma F_7971c : fetch_word AsanUbsan.M.loaded_segments (0x7976c : word) = Some W_7971c.
Proof. vm_refl. Qed.
Lemma D_7971c : decode_any W_7971c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_79720 : bv 32 := 0xfee69ae3.
Lemma F_79720 : fetch_word AsanUbsan.M.loaded_segments (0x79770 : word) = Some W_79720.
Proof. vm_refl. Qed.
Lemma D_79720 : decode_any W_79720 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_79724 : bv 32 := 0x0ff7f693.
Lemma F_79724 : fetch_word AsanUbsan.M.loaded_segments (0x79774 : word) = Some W_79724.
Proof. vm_refl. Qed.
Lemma D_79724 : decode_any W_79724 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_79728 : bv 32 := 0xe2068ce3.
Lemma F_79728 : fetch_word AsanUbsan.M.loaded_segments (0x79778 : word) = Some W_79728.
Proof. vm_refl. Qed.
Lemma D_79728 : decode_any W_79728 = Some (Branch BC_EQ 13 0 7736, 4%Z).
Proof. vm_refl. Qed.

Definition W_7972c : bv 32 := 0x00050a93.
Lemma F_7972c : fetch_word AsanUbsan.M.loaded_segments (0x7977c : word) = Some W_7972c.
Proof. vm_refl. Qed.
Lemma D_7972c : decode_any W_7972c = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79730 : bv 32 := 0x00058513.
Lemma F_79730 : fetch_word AsanUbsan.M.loaded_segments (0x79780 : word) = Some W_79730.
Proof. vm_refl. Qed.
Lemma D_79730 : decode_any W_79730 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79734 : bv 32 := 0x00058b13.
Lemma F_79734 : fetch_word AsanUbsan.M.loaded_segments (0x79784 : word) = Some W_79734.
Proof. vm_refl. Qed.
Lemma D_79734 : decode_any W_79734 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79738 : bv 32 := 0x00060593.
Lemma F_79738 : fetch_word AsanUbsan.M.loaded_segments (0x79788 : word) = Some W_79738.
Proof. vm_refl. Qed.
Lemma D_79738 : decode_any W_79738 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7973c : bv 32 := 0x00060493.
Lemma F_7973c : fetch_word AsanUbsan.M.loaded_segments (0x7978c : word) = Some W_7973c.
Proof. vm_refl. Qed.
Lemma D_7973c : decode_any W_7973c = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79740 : bv 32 := 0x6dd020ef.
Lemma F_79740 : fetch_word AsanUbsan.M.loaded_segments (0x79790 : word) = Some W_79740.
Proof. vm_refl. Qed.
Lemma D_79740 : decode_any W_79740 = Some (Jal 1 11996, 4%Z).
Proof. vm_refl. Qed.

Definition W_79744 : bv 32 := 0x000b0593.
Lemma F_79744 : fetch_word AsanUbsan.M.loaded_segments (0x79794 : word) = Some W_79744.
Proof. vm_refl. Qed.
Lemma D_79744 : decode_any W_79744 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79748 : bv 32 := 0x00048613.
Lemma F_79748 : fetch_word AsanUbsan.M.loaded_segments (0x79798 : word) = Some W_79748.
Proof. vm_refl. Qed.
Lemma D_79748 : decode_any W_79748 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7974c : bv 32 := 0x00050913.
Lemma F_7974c : fetch_word AsanUbsan.M.loaded_segments (0x7979c : word) = Some W_7974c.
Proof. vm_refl. Qed.
Lemma D_7974c : decode_any W_7974c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79750 : bv 32 := 0x000a8513.
Lemma F_79750 : fetch_word AsanUbsan.M.loaded_segments (0x797a0 : word) = Some W_79750.
Proof. vm_refl. Qed.
Lemma D_79750 : decode_any W_79750 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79754 : bv 32 := 0xe00906e3.
Lemma F_79754 : fetch_word AsanUbsan.M.loaded_segments (0x797a4 : word) = Some W_79754.
Proof. vm_refl. Qed.
Lemma D_79754 : decode_any W_79754 = Some (Branch BC_EQ 18 0 7692, 4%Z).
Proof. vm_refl. Qed.

Definition W_7979c : bv 32 := 0x00070803.
Lemma F_7979c : fetch_word AsanUbsan.M.loaded_segments (0x797ec : word) = Some W_7979c.
Proof. vm_refl. Qed.
Lemma D_7979c : decode_any W_7979c = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_797a0 : bv 32 := 0x0077f793.
Lemma F_797a0 : fetch_word AsanUbsan.M.loaded_segments (0x797f0 : word) = Some W_797a0.
Proof. vm_refl. Qed.
Lemma D_797a0 : decode_any W_797a0 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_797a4 : bv 32 := 0x010038b3.
Lemma F_797a4 : fetch_word AsanUbsan.M.loaded_segments (0x797f4 : word) = Some W_797a4.
Proof. vm_refl. Qed.
Lemma D_797a4 : decode_any W_797a4 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_797a8 : bv 32 := 0x0107a7b3.
Lemma F_797a8 : fetch_word AsanUbsan.M.loaded_segments (0x797f8 : word) = Some W_797a8.
Proof. vm_refl. Qed.
Lemma D_797a8 : decode_any W_797a8 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_797ac : bv 32 := 0x0017c793.
Lemma F_797ac : fetch_word AsanUbsan.M.loaded_segments (0x797fc : word) = Some W_797ac.
Proof. vm_refl. Qed.
Lemma D_797ac : decode_any W_797ac = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_797b0 : bv 32 := 0x00f8f7b3.
Lemma F_797b0 : fetch_word AsanUbsan.M.loaded_segments (0x79800 : word) = Some W_797b0.
Proof. vm_refl. Qed.
Lemma D_797b0 : decode_any W_797b0 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_797b4 : bv 32 := 0x00e6fa63.
Lemma F_797b4 : fetch_word AsanUbsan.M.loaded_segments (0x79804 : word) = Some W_797b4.
Proof. vm_refl. Qed.
Lemma D_797b4 : decode_any W_797b4 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_797b8 : bv 32 := 0x0006c803.
Lemma F_797b8 : fetch_word AsanUbsan.M.loaded_segments (0x79808 : word) = Some W_797b8.
Proof. vm_refl. Qed.
Lemma D_797b8 : decode_any W_797b8 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_797bc : bv 32 := 0x00168693.
Lemma F_797bc : fetch_word AsanUbsan.M.loaded_segments (0x7980c : word) = Some W_797bc.
Proof. vm_refl. Qed.
Lemma D_797bc : decode_any W_797bc = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_797c0 : bv 32 := 0x00f867b3.
Lemma F_797c0 : fetch_word AsanUbsan.M.loaded_segments (0x79810 : word) = Some W_797c0.
Proof. vm_refl. Qed.
Lemma D_797c0 : decode_any W_797c0 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_797c4 : bv 32 := 0xfee69ae3.
Lemma F_797c4 : fetch_word AsanUbsan.M.loaded_segments (0x79814 : word) = Some W_797c4.
Proof. vm_refl. Qed.
Lemma D_797c4 : decode_any W_797c4 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_797c8 : bv 32 := 0x0ff7f693.
Lemma F_797c8 : fetch_word AsanUbsan.M.loaded_segments (0x79818 : word) = Some W_797c8.
Proof. vm_refl. Qed.
Lemma D_797c8 : decode_any W_797c8 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_797cc : bv 32 := 0xde0680e3.
Lemma F_797cc : fetch_word AsanUbsan.M.loaded_segments (0x7981c : word) = Some W_797cc.
Proof. vm_refl. Qed.
Lemma D_797cc : decode_any W_797cc = Some (Branch BC_EQ 13 0 7648, 4%Z).
Proof. vm_refl. Qed.

Definition W_797d0 : bv 32 := 0x00050493.
Lemma F_797d0 : fetch_word AsanUbsan.M.loaded_segments (0x79820 : word) = Some W_797d0.
Proof. vm_refl. Qed.
Lemma D_797d0 : decode_any W_797d0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_797d4 : bv 32 := 0x00058a93.
Lemma F_797d4 : fetch_word AsanUbsan.M.loaded_segments (0x79824 : word) = Some W_797d4.
Proof. vm_refl. Qed.
Lemma D_797d4 : decode_any W_797d4 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_797d8 : bv 32 := 0x00060593.
Lemma F_797d8 : fetch_word AsanUbsan.M.loaded_segments (0x79828 : word) = Some W_797d8.
Proof. vm_refl. Qed.
Lemma D_797d8 : decode_any W_797d8 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_797dc : bv 32 := 0x00060913.
Lemma F_797dc : fetch_word AsanUbsan.M.loaded_segments (0x7982c : word) = Some W_797dc.
Proof. vm_refl. Qed.
Lemma D_797dc : decode_any W_797dc = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_797e0 : bv 32 := 0x63d020ef.
Lemma F_797e0 : fetch_word AsanUbsan.M.loaded_segments (0x79830 : word) = Some W_797e0.
Proof. vm_refl. Qed.
Lemma D_797e0 : decode_any W_797e0 = Some (Jal 1 11836, 4%Z).
Proof. vm_refl. Qed.

Definition W_797e4 : bv 32 := 0x000a8593.
Lemma F_797e4 : fetch_word AsanUbsan.M.loaded_segments (0x79834 : word) = Some W_797e4.
Proof. vm_refl. Qed.
Lemma D_797e4 : decode_any W_797e4 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_797e8 : bv 32 := 0x00090613.
Lemma F_797e8 : fetch_word AsanUbsan.M.loaded_segments (0x79838 : word) = Some W_797e8.
Proof. vm_refl. Qed.
Lemma D_797e8 : decode_any W_797e8 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_797ec : bv 32 := 0x00050993.
Lemma F_797ec : fetch_word AsanUbsan.M.loaded_segments (0x7983c : word) = Some W_797ec.
Proof. vm_refl. Qed.
Lemma D_797ec : decode_any W_797ec = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_797f0 : bv 32 := 0x00048513.
Lemma F_797f0 : fetch_word AsanUbsan.M.loaded_segments (0x79840 : word) = Some W_797f0.
Proof. vm_refl. Qed.
Lemma D_797f0 : decode_any W_797f0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_797f4 : bv 32 := 0xda098ce3.
Lemma F_797f4 : fetch_word AsanUbsan.M.loaded_segments (0x79844 : word) = Some W_797f4.
Proof. vm_refl. Qed.
Lemma D_797f4 : decode_any W_797f4 = Some (Branch BC_EQ 19 0 7608, 4%Z).
Proof. vm_refl. Qed.

Definition W_7983c : bv 32 := 0x81010113.
Lemma F_7983c : fetch_word AsanUbsan.M.loaded_segments (0x7988c : word) = Some W_7983c.
Proof. vm_refl. Qed.
Lemma D_7983c : decode_any W_7983c = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_79840 : bv 32 := 0x7e113423.
Lemma F_79840 : fetch_word AsanUbsan.M.loaded_segments (0x79890 : word) = Some W_79840.
Proof. vm_refl. Qed.
Lemma D_79840 : decode_any W_79840 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_79844 : bv 32 := 0x7e813023.
Lemma F_79844 : fetch_word AsanUbsan.M.loaded_segments (0x79894 : word) = Some W_79844.
Proof. vm_refl. Qed.
Lemma D_79844 : decode_any W_79844 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_79848 : bv 32 := 0x7c913c23.
Lemma F_79848 : fetch_word AsanUbsan.M.loaded_segments (0x79898 : word) = Some W_79848.
Proof. vm_refl. Qed.
Lemma D_79848 : decode_any W_79848 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7984c : bv 32 := 0x7d213823.
Lemma F_7984c : fetch_word AsanUbsan.M.loaded_segments (0x7989c : word) = Some W_7984c.
Proof. vm_refl. Qed.
Lemma D_7984c : decode_any W_7984c = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_79850 : bv 32 := 0x7d313423.
Lemma F_79850 : fetch_word AsanUbsan.M.loaded_segments (0x798a0 : word) = Some W_79850.
Proof. vm_refl. Qed.
Lemma D_79850 : decode_any W_79850 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_79854 : bv 32 := 0x7d413023.
Lemma F_79854 : fetch_word AsanUbsan.M.loaded_segments (0x798a4 : word) = Some W_79854.
Proof. vm_refl. Qed.
Lemma D_79854 : decode_any W_79854 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_79858 : bv 32 := 0x7b513c23.
Lemma F_79858 : fetch_word AsanUbsan.M.loaded_segments (0x798a8 : word) = Some W_79858.
Proof. vm_refl. Qed.
Lemma D_79858 : decode_any W_79858 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7985c : bv 32 := 0x7b613823.
Lemma F_7985c : fetch_word AsanUbsan.M.loaded_segments (0x798ac : word) = Some W_7985c.
Proof. vm_refl. Qed.
Lemma D_7985c : decode_any W_7985c = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_79860 : bv 32 := 0x7f010413.
Lemma F_79860 : fetch_word AsanUbsan.M.loaded_segments (0x798b0 : word) = Some W_79860.
Proof. vm_refl. Qed.
Lemma D_79860 : decode_any W_79860 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_79864 : bv 32 := 0xf9010113.
Lemma F_79864 : fetch_word AsanUbsan.M.loaded_segments (0x798b4 : word) = Some W_79864.
Proof. vm_refl. Qed.
Lemma D_79864 : decode_any W_79864 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_79868 : bv 32 := 0x000c5697.
Lemma F_79868 : fetch_word AsanUbsan.M.loaded_segments (0x798b8 : word) = Some W_79868.
Proof. vm_refl. Qed.
Lemma D_79868 : decode_any W_79868 = Some (Auipc 13 197, 4%Z).
Proof. vm_refl. Qed.

Definition W_7986c : bv 32 := 0xb786b683.
Lemma F_7986c : fetch_word AsanUbsan.M.loaded_segments (0x798bc : word) = Some W_7986c.
Proof. vm_refl. Qed.
Lemma D_7986c : decode_any W_7986c = Some (Load SZ8 true 13 13 2936, 4%Z).
Proof. vm_refl. Qed.

Definition W_79870 : bv 32 := 0x0006c683.
Lemma F_79870 : fetch_word AsanUbsan.M.loaded_segments (0x798c0 : word) = Some W_79870.
Proof. vm_refl. Qed.
Lemma D_79870 : decode_any W_79870 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79874 : bv 32 := 0x08068a63.
Lemma F_79874 : fetch_word AsanUbsan.M.loaded_segments (0x798c4 : word) = Some W_79874.
Proof. vm_refl. Qed.
Lemma D_79874 : decode_any W_79874 = Some (Branch BC_EQ 13 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_79878 : bv 32 := 0xfff54693.
Lemma F_79878 : fetch_word AsanUbsan.M.loaded_segments (0x798c8 : word) = Some W_79878.
Proof. vm_refl. Qed.
Lemma D_79878 : decode_any W_79878 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7987c : bv 32 := 0x80040a93.
Lemma F_7987c : fetch_word AsanUbsan.M.loaded_segments (0x798cc : word) = Some W_7987c.
Proof. vm_refl. Qed.
Lemma D_7987c : decode_any W_7987c = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_79880 : bv 32 := 0xfa8a8a93.
Lemma F_79880 : fetch_word AsanUbsan.M.loaded_segments (0x798d0 : word) = Some W_79880.
Proof. vm_refl. Qed.
Lemma D_79880 : decode_any W_79880 = Some (OpImm ALU_ADD 21 21 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_79884 : bv 32 := 0x0cc6ea63.
Lemma F_79884 : fetch_word AsanUbsan.M.loaded_segments (0x798d4 : word) = Some W_79884.
Proof. vm_refl. Qed.
Lemma D_79884 : decode_any W_79884 = Some (Branch BC_LTU 13 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_79888 : bv 32 := 0xfbf60693.
Lemma F_79888 : fetch_word AsanUbsan.M.loaded_segments (0x798d8 : word) = Some W_79888.
Proof. vm_refl. Qed.
Lemma D_79888 : decode_any W_79888 = Some (OpImm ALU_ADD 13 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7988c : bv 32 := 0xfbf00713.
Lemma F_7988c : fetch_word AsanUbsan.M.loaded_segments (0x798dc : word) = Some W_7988c.
Proof. vm_refl. Qed.
Lemma D_7988c : decode_any W_7988c = Some (OpImm ALU_ADD 14 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_79890 : bv 32 := 0x14d77863.
Lemma F_79890 : fetch_word AsanUbsan.M.loaded_segments (0x798e0 : word) = Some W_79890.
Proof. vm_refl. Qed.
Lemma D_79890 : decode_any W_79890 = Some (Branch BC_GEU 14 13 336, 4%Z).
Proof. vm_refl. Qed.

Definition W_79894 : bv 32 := 0x000c4697.
Lemma F_79894 : fetch_word AsanUbsan.M.loaded_segments (0x798e4 : word) = Some W_79894.
Proof. vm_refl. Qed.
Lemma D_79894 : decode_any W_79894 = Some (Auipc 13 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_79898 : bv 32 := 0xfe46b683.
Lemma F_79898 : fetch_word AsanUbsan.M.loaded_segments (0x798e8 : word) = Some W_79898.
Proof. vm_refl. Qed.
Lemma D_79898 : decode_any W_79898 = Some (Load SZ8 true 13 13 4068, 4%Z).
Proof. vm_refl. Qed.

Definition W_7989c : bv 32 := 0x00c507b3.
Lemma F_7989c : fetch_word AsanUbsan.M.loaded_segments (0x798ec : word) = Some W_7989c.
Proof. vm_refl. Qed.
Lemma D_7989c : decode_any W_7989c = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_798a0 : bv 32 := 0x0006b703.
Lemma F_798a0 : fetch_word AsanUbsan.M.loaded_segments (0x798f0 : word) = Some W_798a0.
Proof. vm_refl. Qed.
Lemma D_798a0 : decode_any W_798a0 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_798a4 : bv 32 := 0x00355693.
Lemma F_798a4 : fetch_word AsanUbsan.M.loaded_segments (0x798f4 : word) = Some W_798a4.
Proof. vm_refl. Qed.
Lemma D_798a4 : decode_any W_798a4 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_798a8 : bv 32 := 0xfff78793.
Lemma F_798a8 : fetch_word AsanUbsan.M.loaded_segments (0x798f8 : word) = Some W_798a8.
Proof. vm_refl. Qed.
Lemma D_798a8 : decode_any W_798a8 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_798ac : bv 32 := 0x0037d813.
Lemma F_798ac : fetch_word AsanUbsan.M.loaded_segments (0x798fc : word) = Some W_798ac.
Proof. vm_refl. Qed.
Lemma D_798ac : decode_any W_798ac = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_798b0 : bv 32 := 0x00d706b3.
Lemma F_798b0 : fetch_word AsanUbsan.M.loaded_segments (0x79900 : word) = Some W_798b0.
Proof. vm_refl. Qed.
Lemma D_798b0 : decode_any W_798b0 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_798b4 : bv 32 := 0x01070733.
Lemma F_798b4 : fetch_word AsanUbsan.M.loaded_segments (0x79904 : word) = Some W_798b4.
Proof. vm_refl. Qed.
Lemma D_798b4 : decode_any W_798b4 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_798b8 : bv 32 := 0xff86f813.
Lemma F_798b8 : fetch_word AsanUbsan.M.loaded_segments (0x79908 : word) = Some W_798b8.
Proof. vm_refl. Qed.
Lemma D_798b8 : decode_any W_798b8 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_798bc : bv 32 := 0xff877893.
Lemma F_798bc : fetch_word AsanUbsan.M.loaded_segments (0x7990c : word) = Some W_798bc.
Proof. vm_refl. Qed.
Lemma D_798bc : decode_any W_798bc = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_798c0 : bv 32 := 0x00083803.
Lemma F_798c0 : fetch_word AsanUbsan.M.loaded_segments (0x79910 : word) = Some W_798c0.
Proof. vm_refl. Qed.
Lemma D_798c0 : decode_any W_798c0 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_798c4 : bv 32 := 0x0008b883.
Lemma F_798c4 : fetch_word AsanUbsan.M.loaded_segments (0x79914 : word) = Some W_798c4.
Proof. vm_refl. Qed.
Lemma D_798c4 : decode_any W_798c4 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_798c8 : bv 32 := 0x0108e833.
Lemma F_798c8 : fetch_word AsanUbsan.M.loaded_segments (0x79918 : word) = Some W_798c8.
Proof. vm_refl. Qed.
Lemma D_798c8 : decode_any W_798c8 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_798cc : bv 32 := 0x10081e63.
Lemma F_798cc : fetch_word AsanUbsan.M.loaded_segments (0x7991c : word) = Some W_798cc.
Proof. vm_refl. Qed.
Lemma D_798cc : decode_any W_798cc = Some (Branch BC_NE 16 0 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_798d0 : bv 32 := 0x000c6697.
Lemma F_798d0 : fetch_word AsanUbsan.M.loaded_segments (0x79920 : word) = Some W_798d0.
Proof. vm_refl. Qed.
Lemma D_798d0 : decode_any W_798d0 = Some (Auipc 13 198, 4%Z).
Proof. vm_refl. Qed.

Definition W_798d4 : bv 32 := 0xfb86b683.
Lemma F_798d4 : fetch_word AsanUbsan.M.loaded_segments (0x79924 : word) = Some W_798d4.
Proof. vm_refl. Qed.
Lemma D_798d4 : decode_any W_798d4 = Some (Load SZ8 true 13 13 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_798d8 : bv 32 := 0x000680e7.
Lemma F_798d8 : fetch_word AsanUbsan.M.loaded_segments (0x79928 : word) = Some W_798d8.
Proof. vm_refl. Qed.
Lemma D_798d8 : decode_any W_798d8 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_798dc : bv 32 := 0x07010113.
Lemma F_798dc : fetch_word AsanUbsan.M.loaded_segments (0x7992c : word) = Some W_798dc.
Proof. vm_refl. Qed.
Lemma D_798dc : decode_any W_798dc = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_798e0 : bv 32 := 0x7e813083.
Lemma F_798e0 : fetch_word AsanUbsan.M.loaded_segments (0x79930 : word) = Some W_798e0.
Proof. vm_refl. Qed.
Lemma D_798e0 : decode_any W_798e0 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_798e4 : bv 32 := 0x7e013403.
Lemma F_798e4 : fetch_word AsanUbsan.M.loaded_segments (0x79934 : word) = Some W_798e4.
Proof. vm_refl. Qed.
Lemma D_798e4 : decode_any W_798e4 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_798e8 : bv 32 := 0x7d813483.
Lemma F_798e8 : fetch_word AsanUbsan.M.loaded_segments (0x79938 : word) = Some W_798e8.
Proof. vm_refl. Qed.
Lemma D_798e8 : decode_any W_798e8 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_798ec : bv 32 := 0x7d013903.
Lemma F_798ec : fetch_word AsanUbsan.M.loaded_segments (0x7993c : word) = Some W_798ec.
Proof. vm_refl. Qed.
Lemma D_798ec : decode_any W_798ec = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_798f0 : bv 32 := 0x7c813983.
Lemma F_798f0 : fetch_word AsanUbsan.M.loaded_segments (0x79940 : word) = Some W_798f0.
Proof. vm_refl. Qed.
Lemma D_798f0 : decode_any W_798f0 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_798f4 : bv 32 := 0x7c013a03.
Lemma F_798f4 : fetch_word AsanUbsan.M.loaded_segments (0x79944 : word) = Some W_798f4.
Proof. vm_refl. Qed.
Lemma D_798f4 : decode_any W_798f4 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_798f8 : bv 32 := 0x7b813a83.
Lemma F_798f8 : fetch_word AsanUbsan.M.loaded_segments (0x79948 : word) = Some W_798f8.
Proof. vm_refl. Qed.
Lemma D_798f8 : decode_any W_798f8 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_798fc : bv 32 := 0x7b013b03.
Lemma F_798fc : fetch_word AsanUbsan.M.loaded_segments (0x7994c : word) = Some W_798fc.
Proof. vm_refl. Qed.
Lemma D_798fc : decode_any W_798fc = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_79900 : bv 32 := 0x7f010113.
Lemma F_79900 : fetch_word AsanUbsan.M.loaded_segments (0x79950 : word) = Some W_79900.
Proof. vm_refl. Qed.
Lemma D_79900 : decode_any W_79900 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_79904 : bv 32 := 0x00008067.
Lemma F_79904 : fetch_word AsanUbsan.M.loaded_segments (0x79954 : word) = Some W_79904.
Proof. vm_refl. Qed.
Lemma D_79904 : decode_any W_79904 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_799e0 : bv 32 := 0x02061e63.
Lemma F_799e0 : fetch_word AsanUbsan.M.loaded_segments (0x79a30 : word) = Some W_799e0.
Proof. vm_refl. Qed.
Lemma D_799e0 : decode_any W_799e0 = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_799e4 : bv 32 := 0xeedff06f.
Lemma F_799e4 : fetch_word AsanUbsan.M.loaded_segments (0x79a34 : word) = Some W_799e4.
Proof. vm_refl. Qed.
Lemma D_799e4 : decode_any W_799e4 = Some (Jal 0 2096876, 4%Z).
Proof. vm_refl. Qed.

Definition W_799e8 : bv 32 := 0x00070803.
Lemma F_799e8 : fetch_word AsanUbsan.M.loaded_segments (0x79a38 : word) = Some W_799e8.
Proof. vm_refl. Qed.
Lemma D_799e8 : decode_any W_799e8 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_799ec : bv 32 := 0x0077f793.
Lemma F_799ec : fetch_word AsanUbsan.M.loaded_segments (0x79a3c : word) = Some W_799ec.
Proof. vm_refl. Qed.
Lemma D_799ec : decode_any W_799ec = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_799f0 : bv 32 := 0x010038b3.
Lemma F_799f0 : fetch_word AsanUbsan.M.loaded_segments (0x79a40 : word) = Some W_799f0.
Proof. vm_refl. Qed.
Lemma D_799f0 : decode_any W_799f0 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_799f4 : bv 32 := 0x0107a7b3.
Lemma F_799f4 : fetch_word AsanUbsan.M.loaded_segments (0x79a44 : word) = Some W_799f4.
Proof. vm_refl. Qed.
Lemma D_799f4 : decode_any W_799f4 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_799f8 : bv 32 := 0x0017c793.
Lemma F_799f8 : fetch_word AsanUbsan.M.loaded_segments (0x79a48 : word) = Some W_799f8.
Proof. vm_refl. Qed.
Lemma D_799f8 : decode_any W_799f8 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_799fc : bv 32 := 0x00f8f7b3.
Lemma F_799fc : fetch_word AsanUbsan.M.loaded_segments (0x79a4c : word) = Some W_799fc.
Proof. vm_refl. Qed.
Lemma D_799fc : decode_any W_799fc = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_79a00 : bv 32 := 0x00e6fa63.
Lemma F_79a00 : fetch_word AsanUbsan.M.loaded_segments (0x79a50 : word) = Some W_79a00.
Proof. vm_refl. Qed.
Lemma D_79a00 : decode_any W_79a00 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_79a04 : bv 32 := 0x0006c803.
Lemma F_79a04 : fetch_word AsanUbsan.M.loaded_segments (0x79a54 : word) = Some W_79a04.
Proof. vm_refl. Qed.
Lemma D_79a04 : decode_any W_79a04 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79a08 : bv 32 := 0x00168693.
Lemma F_79a08 : fetch_word AsanUbsan.M.loaded_segments (0x79a58 : word) = Some W_79a08.
Proof. vm_refl. Qed.
Lemma D_79a08 : decode_any W_79a08 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_79a0c : bv 32 := 0x00f867b3.
Lemma F_79a0c : fetch_word AsanUbsan.M.loaded_segments (0x79a5c : word) = Some W_79a0c.
Proof. vm_refl. Qed.
Lemma D_79a0c : decode_any W_79a0c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_79a10 : bv 32 := 0xfee69ae3.
Lemma F_79a10 : fetch_word AsanUbsan.M.loaded_segments (0x79a60 : word) = Some W_79a10.
Proof. vm_refl. Qed.
Lemma D_79a10 : decode_any W_79a10 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_79a14 : bv 32 := 0x0ff7f693.
Lemma F_79a14 : fetch_word AsanUbsan.M.loaded_segments (0x79a64 : word) = Some W_79a14.
Proof. vm_refl. Qed.
Lemma D_79a14 : decode_any W_79a14 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_79a18 : bv 32 := 0xea068ce3.
Lemma F_79a18 : fetch_word AsanUbsan.M.loaded_segments (0x79a68 : word) = Some W_79a18.
Proof. vm_refl. Qed.
Lemma D_79a18 : decode_any W_79a18 = Some (Branch BC_EQ 13 0 7864, 4%Z).
Proof. vm_refl. Qed.

Definition W_79a1c : bv 32 := 0x00050493.
Lemma F_79a1c : fetch_word AsanUbsan.M.loaded_segments (0x79a6c : word) = Some W_79a1c.
Proof. vm_refl. Qed.
Lemma D_79a1c : decode_any W_79a1c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79a20 : bv 32 := 0x00058b13.
Lemma F_79a20 : fetch_word AsanUbsan.M.loaded_segments (0x79a70 : word) = Some W_79a20.
Proof. vm_refl. Qed.
Lemma D_79a20 : decode_any W_79a20 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79a24 : bv 32 := 0x00060593.
Lemma F_79a24 : fetch_word AsanUbsan.M.loaded_segments (0x79a74 : word) = Some W_79a24.
Proof. vm_refl. Qed.
Lemma D_79a24 : decode_any W_79a24 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79a28 : bv 32 := 0x00060913.
Lemma F_79a28 : fetch_word AsanUbsan.M.loaded_segments (0x79a78 : word) = Some W_79a28.
Proof. vm_refl. Qed.
Lemma D_79a28 : decode_any W_79a28 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79a2c : bv 32 := 0x3f1020ef.
Lemma F_79a2c : fetch_word AsanUbsan.M.loaded_segments (0x79a7c : word) = Some W_79a2c.
Proof. vm_refl. Qed.
Lemma D_79a2c : decode_any W_79a2c = Some (Jal 1 11248, 4%Z).
Proof. vm_refl. Qed.

Definition W_79a30 : bv 32 := 0x000b0593.
Lemma F_79a30 : fetch_word AsanUbsan.M.loaded_segments (0x79a80 : word) = Some W_79a30.
Proof. vm_refl. Qed.
Lemma D_79a30 : decode_any W_79a30 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79a34 : bv 32 := 0x00090613.
Lemma F_79a34 : fetch_word AsanUbsan.M.loaded_segments (0x79a84 : word) = Some W_79a34.
Proof. vm_refl. Qed.
Lemma D_79a34 : decode_any W_79a34 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79a38 : bv 32 := 0x00050993.
Lemma F_79a38 : fetch_word AsanUbsan.M.loaded_segments (0x79a88 : word) = Some W_79a38.
Proof. vm_refl. Qed.
Lemma D_79a38 : decode_any W_79a38 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79a3c : bv 32 := 0x00048513.
Lemma F_79a3c : fetch_word AsanUbsan.M.loaded_segments (0x79a8c : word) = Some W_79a3c.
Proof. vm_refl. Qed.
Lemma D_79a3c : decode_any W_79a3c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79a40 : bv 32 := 0xe80988e3.
Lemma F_79a40 : fetch_word AsanUbsan.M.loaded_segments (0x79a90 : word) = Some W_79a40.
Proof. vm_refl. Qed.
Lemma D_79a40 : decode_any W_79a40 = Some (Branch BC_EQ 19 0 7824, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b2c : bv 32 := 0x81010113.
Lemma F_79b2c : fetch_word AsanUbsan.M.loaded_segments (0x79b7c : word) = Some W_79b2c.
Proof. vm_refl. Qed.
Lemma D_79b2c : decode_any W_79b2c = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b30 : bv 32 := 0x7e113423.
Lemma F_79b30 : fetch_word AsanUbsan.M.loaded_segments (0x79b80 : word) = Some W_79b30.
Proof. vm_refl. Qed.
Lemma D_79b30 : decode_any W_79b30 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b34 : bv 32 := 0x7e813023.
Lemma F_79b34 : fetch_word AsanUbsan.M.loaded_segments (0x79b84 : word) = Some W_79b34.
Proof. vm_refl. Qed.
Lemma D_79b34 : decode_any W_79b34 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b38 : bv 32 := 0x7c913c23.
Lemma F_79b38 : fetch_word AsanUbsan.M.loaded_segments (0x79b88 : word) = Some W_79b38.
Proof. vm_refl. Qed.
Lemma D_79b38 : decode_any W_79b38 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b3c : bv 32 := 0x7d213823.
Lemma F_79b3c : fetch_word AsanUbsan.M.loaded_segments (0x79b8c : word) = Some W_79b3c.
Proof. vm_refl. Qed.
Lemma D_79b3c : decode_any W_79b3c = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b40 : bv 32 := 0x7d313423.
Lemma F_79b40 : fetch_word AsanUbsan.M.loaded_segments (0x79b90 : word) = Some W_79b40.
Proof. vm_refl. Qed.
Lemma D_79b40 : decode_any W_79b40 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b44 : bv 32 := 0x7d413023.
Lemma F_79b44 : fetch_word AsanUbsan.M.loaded_segments (0x79b94 : word) = Some W_79b44.
Proof. vm_refl. Qed.
Lemma D_79b44 : decode_any W_79b44 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b48 : bv 32 := 0x7b513c23.
Lemma F_79b48 : fetch_word AsanUbsan.M.loaded_segments (0x79b98 : word) = Some W_79b48.
Proof. vm_refl. Qed.
Lemma D_79b48 : decode_any W_79b48 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b4c : bv 32 := 0x7b613823.
Lemma F_79b4c : fetch_word AsanUbsan.M.loaded_segments (0x79b9c : word) = Some W_79b4c.
Proof. vm_refl. Qed.
Lemma D_79b4c : decode_any W_79b4c = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b50 : bv 32 := 0x7b713423.
Lemma F_79b50 : fetch_word AsanUbsan.M.loaded_segments (0x79ba0 : word) = Some W_79b50.
Proof. vm_refl. Qed.
Lemma D_79b50 : decode_any W_79b50 = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b54 : bv 32 := 0x7f010413.
Lemma F_79b54 : fetch_word AsanUbsan.M.loaded_segments (0x79ba4 : word) = Some W_79b54.
Proof. vm_refl. Qed.
Lemma D_79b54 : decode_any W_79b54 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b58 : bv 32 := 0xf9010113.
Lemma F_79b58 : fetch_word AsanUbsan.M.loaded_segments (0x79ba8 : word) = Some W_79b58.
Proof. vm_refl. Qed.
Lemma D_79b58 : decode_any W_79b58 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b5c : bv 32 := 0x000c5697.
Lemma F_79b5c : fetch_word AsanUbsan.M.loaded_segments (0x79bac : word) = Some W_79b5c.
Proof. vm_refl. Qed.
Lemma D_79b5c : decode_any W_79b5c = Some (Auipc 13 197, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b60 : bv 32 := 0x8846b683.
Lemma F_79b60 : fetch_word AsanUbsan.M.loaded_segments (0x79bb0 : word) = Some W_79b60.
Proof. vm_refl. Qed.
Lemma D_79b60 : decode_any W_79b60 = Some (Load SZ8 true 13 13 2180, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b64 : bv 32 := 0x0006c683.
Lemma F_79b64 : fetch_word AsanUbsan.M.loaded_segments (0x79bb4 : word) = Some W_79b64.
Proof. vm_refl. Qed.
Lemma D_79b64 : decode_any W_79b64 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b68 : bv 32 := 0x0a068463.
Lemma F_79b68 : fetch_word AsanUbsan.M.loaded_segments (0x79bb8 : word) = Some W_79b68.
Proof. vm_refl. Qed.
Lemma D_79b68 : decode_any W_79b68 = Some (Branch BC_EQ 13 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b6c : bv 32 := 0xfff5c693.
Lemma F_79b6c : fetch_word AsanUbsan.M.loaded_segments (0x79bbc : word) = Some W_79b6c.
Proof. vm_refl. Qed.
Lemma D_79b6c : decode_any W_79b6c = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b70 : bv 32 := 0x80040a93.
Lemma F_79b70 : fetch_word AsanUbsan.M.loaded_segments (0x79bc0 : word) = Some W_79b70.
Proof. vm_refl. Qed.
Lemma D_79b70 : decode_any W_79b70 = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b74 : bv 32 := 0xfa0a8a93.
Lemma F_79b74 : fetch_word AsanUbsan.M.loaded_segments (0x79bc4 : word) = Some W_79b74.
Proof. vm_refl. Qed.
Lemma D_79b74 : decode_any W_79b74 = Some (OpImm ALU_ADD 21 21 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b78 : bv 32 := 0x0cc6e663.
Lemma F_79b78 : fetch_word AsanUbsan.M.loaded_segments (0x79bc8 : word) = Some W_79b78.
Proof. vm_refl. Qed.
Lemma D_79b78 : decode_any W_79b78 = Some (Branch BC_LTU 13 12 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b7c : bv 32 := 0xfbf60a13.
Lemma F_79b7c : fetch_word AsanUbsan.M.loaded_segments (0x79bcc : word) = Some W_79b7c.
Proof. vm_refl. Qed.
Lemma D_79b7c : decode_any W_79b7c = Some (OpImm ALU_ADD 20 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b80 : bv 32 := 0xfbf00693.
Lemma F_79b80 : fetch_word AsanUbsan.M.loaded_segments (0x79bd0 : word) = Some W_79b80.
Proof. vm_refl. Qed.
Lemma D_79b80 : decode_any W_79b80 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b84 : bv 32 := 0x1546f463.
Lemma F_79b84 : fetch_word AsanUbsan.M.loaded_segments (0x79bd4 : word) = Some W_79b84.
Proof. vm_refl. Qed.
Lemma D_79b84 : decode_any W_79b84 = Some (Branch BC_GEU 13 20 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b88 : bv 32 := 0x000c4697.
Lemma F_79b88 : fetch_word AsanUbsan.M.loaded_segments (0x79bd8 : word) = Some W_79b88.
Proof. vm_refl. Qed.
Lemma D_79b88 : decode_any W_79b88 = Some (Auipc 13 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b8c : bv 32 := 0xcf06b683.
Lemma F_79b8c : fetch_word AsanUbsan.M.loaded_segments (0x79bdc : word) = Some W_79b8c.
Proof. vm_refl. Qed.
Lemma D_79b8c : decode_any W_79b8c = Some (Load SZ8 true 13 13 3312, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b90 : bv 32 := 0x00c587b3.
Lemma F_79b90 : fetch_word AsanUbsan.M.loaded_segments (0x79be0 : word) = Some W_79b90.
Proof. vm_refl. Qed.
Lemma D_79b90 : decode_any W_79b90 = Some (Op ALU_ADD 15 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b94 : bv 32 := 0x0006b703.
Lemma F_79b94 : fetch_word AsanUbsan.M.loaded_segments (0x79be4 : word) = Some W_79b94.
Proof. vm_refl. Qed.
Lemma D_79b94 : decode_any W_79b94 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b98 : bv 32 := 0x0035d693.
Lemma F_79b98 : fetch_word AsanUbsan.M.loaded_segments (0x79be8 : word) = Some W_79b98.
Proof. vm_refl. Qed.
Lemma D_79b98 : decode_any W_79b98 = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_79b9c : bv 32 := 0xfff78793.
Lemma F_79b9c : fetch_word AsanUbsan.M.loaded_segments (0x79bec : word) = Some W_79b9c.
Proof. vm_refl. Qed.
Lemma D_79b9c : decode_any W_79b9c = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_79ba0 : bv 32 := 0x0037d813.
Lemma F_79ba0 : fetch_word AsanUbsan.M.loaded_segments (0x79bf0 : word) = Some W_79ba0.
Proof. vm_refl. Qed.
Lemma D_79ba0 : decode_any W_79ba0 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_79ba4 : bv 32 := 0x00d706b3.
Lemma F_79ba4 : fetch_word AsanUbsan.M.loaded_segments (0x79bf4 : word) = Some W_79ba4.
Proof. vm_refl. Qed.
Lemma D_79ba4 : decode_any W_79ba4 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_79ba8 : bv 32 := 0x01070733.
Lemma F_79ba8 : fetch_word AsanUbsan.M.loaded_segments (0x79bf8 : word) = Some W_79ba8.
Proof. vm_refl. Qed.
Lemma D_79ba8 : decode_any W_79ba8 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_79bac : bv 32 := 0xff86f813.
Lemma F_79bac : fetch_word AsanUbsan.M.loaded_segments (0x79bfc : word) = Some W_79bac.
Proof. vm_refl. Qed.
Lemma D_79bac : decode_any W_79bac = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_79bb0 : bv 32 := 0xff877893.
Lemma F_79bb0 : fetch_word AsanUbsan.M.loaded_segments (0x79c00 : word) = Some W_79bb0.
Proof. vm_refl. Qed.
Lemma D_79bb0 : decode_any W_79bb0 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_79bb4 : bv 32 := 0x00083803.
Lemma F_79bb4 : fetch_word AsanUbsan.M.loaded_segments (0x79c04 : word) = Some W_79bb4.
Proof. vm_refl. Qed.
Lemma D_79bb4 : decode_any W_79bb4 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79bb8 : bv 32 := 0x0008b883.
Lemma F_79bb8 : fetch_word AsanUbsan.M.loaded_segments (0x79c08 : word) = Some W_79bb8.
Proof. vm_refl. Qed.
Lemma D_79bb8 : decode_any W_79bb8 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79bbc : bv 32 := 0x0108e833.
Lemma F_79bbc : fetch_word AsanUbsan.M.loaded_segments (0x79c0c : word) = Some W_79bbc.
Proof. vm_refl. Qed.
Lemma D_79bbc : decode_any W_79bbc = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_79bc0 : bv 32 := 0x1a081063.
Lemma F_79bc0 : fetch_word AsanUbsan.M.loaded_segments (0x79c10 : word) = Some W_79bc0.
Proof. vm_refl. Qed.
Lemma D_79bc0 : decode_any W_79bc0 = Some (Branch BC_NE 16 0 416, 4%Z).
Proof. vm_refl. Qed.

Definition W_79bc4 : bv 32 := 0xfff54693.
Lemma F_79bc4 : fetch_word AsanUbsan.M.loaded_segments (0x79c14 : word) = Some W_79bc4.
Proof. vm_refl. Qed.
Lemma D_79bc4 : decode_any W_79bc4 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_79bc8 : bv 32 := 0x10c6e663.
Lemma F_79bc8 : fetch_word AsanUbsan.M.loaded_segments (0x79c18 : word) = Some W_79bc8.
Proof. vm_refl. Qed.
Lemma D_79bc8 : decode_any W_79bc8 = Some (Branch BC_LTU 13 12 268, 4%Z).
Proof. vm_refl. Qed.

Definition W_79bcc : bv 32 := 0xfbf00693.
Lemma F_79bcc : fetch_word AsanUbsan.M.loaded_segments (0x79c1c : word) = Some W_79bcc.
Proof. vm_refl. Qed.
Lemma D_79bcc : decode_any W_79bcc = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_79bd0 : bv 32 := 0x1946f463.
Lemma F_79bd0 : fetch_word AsanUbsan.M.loaded_segments (0x79c20 : word) = Some W_79bd0.
Proof. vm_refl. Qed.
Lemma D_79bd0 : decode_any W_79bd0 = Some (Branch BC_GEU 13 20 392, 4%Z).
Proof. vm_refl. Qed.

Definition W_79bd4 : bv 32 := 0x000c4697.
Lemma F_79bd4 : fetch_word AsanUbsan.M.loaded_segments (0x79c24 : word) = Some W_79bd4.
Proof. vm_refl. Qed.
Lemma D_79bd4 : decode_any W_79bd4 = Some (Auipc 13 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_79bd8 : bv 32 := 0xca46b683.
Lemma F_79bd8 : fetch_word AsanUbsan.M.loaded_segments (0x79c28 : word) = Some W_79bd8.
Proof. vm_refl. Qed.
Lemma D_79bd8 : decode_any W_79bd8 = Some (Load SZ8 true 13 13 3236, 4%Z).
Proof. vm_refl. Qed.

Definition W_79bdc : bv 32 := 0x00c507b3.
Lemma F_79bdc : fetch_word AsanUbsan.M.loaded_segments (0x79c2c : word) = Some W_79bdc.
Proof. vm_refl. Qed.
Lemma D_79bdc : decode_any W_79bdc = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_79be0 : bv 32 := 0x0006b703.
Lemma F_79be0 : fetch_word AsanUbsan.M.loaded_segments (0x79c30 : word) = Some W_79be0.
Proof. vm_refl. Qed.
Lemma D_79be0 : decode_any W_79be0 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79be4 : bv 32 := 0x00355693.
Lemma F_79be4 : fetch_word AsanUbsan.M.loaded_segments (0x79c34 : word) = Some W_79be4.
Proof. vm_refl. Qed.
Lemma D_79be4 : decode_any W_79be4 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_79be8 : bv 32 := 0xfff78793.
Lemma F_79be8 : fetch_word AsanUbsan.M.loaded_segments (0x79c38 : word) = Some W_79be8.
Proof. vm_refl. Qed.
Lemma D_79be8 : decode_any W_79be8 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_79bec : bv 32 := 0x0037d813.
Lemma F_79bec : fetch_word AsanUbsan.M.loaded_segments (0x79c3c : word) = Some W_79bec.
Proof. vm_refl. Qed.
Lemma D_79bec : decode_any W_79bec = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_79bf0 : bv 32 := 0x00d706b3.
Lemma F_79bf0 : fetch_word AsanUbsan.M.loaded_segments (0x79c40 : word) = Some W_79bf0.
Proof. vm_refl. Qed.
Lemma D_79bf0 : decode_any W_79bf0 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_79bf4 : bv 32 := 0x01070733.
Lemma F_79bf4 : fetch_word AsanUbsan.M.loaded_segments (0x79c44 : word) = Some W_79bf4.
Proof. vm_refl. Qed.
Lemma D_79bf4 : decode_any W_79bf4 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_79bf8 : bv 32 := 0xff86f813.
Lemma F_79bf8 : fetch_word AsanUbsan.M.loaded_segments (0x79c48 : word) = Some W_79bf8.
Proof. vm_refl. Qed.
Lemma D_79bf8 : decode_any W_79bf8 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_79bfc : bv 32 := 0xff877893.
Lemma F_79bfc : fetch_word AsanUbsan.M.loaded_segments (0x79c4c : word) = Some W_79bfc.
Proof. vm_refl. Qed.
Lemma D_79bfc : decode_any W_79bfc = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c00 : bv 32 := 0x00083803.
Lemma F_79c00 : fetch_word AsanUbsan.M.loaded_segments (0x79c50 : word) = Some W_79c00.
Proof. vm_refl. Qed.
Lemma D_79c00 : decode_any W_79c00 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c04 : bv 32 := 0x0008b883.
Lemma F_79c04 : fetch_word AsanUbsan.M.loaded_segments (0x79c54 : word) = Some W_79c04.
Proof. vm_refl. Qed.
Lemma D_79c04 : decode_any W_79c04 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c08 : bv 32 := 0x0108e833.
Lemma F_79c08 : fetch_word AsanUbsan.M.loaded_segments (0x79c58 : word) = Some W_79c08.
Proof. vm_refl. Qed.
Lemma D_79c08 : decode_any W_79c08 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c0c : bv 32 := 0x24081a63.
Lemma F_79c0c : fetch_word AsanUbsan.M.loaded_segments (0x79c5c : word) = Some W_79c0c.
Proof. vm_refl. Qed.
Lemma D_79c0c : decode_any W_79c0c = Some (Branch BC_NE 16 0 596, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c10 : bv 32 := 0x155120ef.
Lemma F_79c10 : fetch_word AsanUbsan.M.loaded_segments (0x79c60 : word) = Some W_79c10.
Proof. vm_refl. Qed.
Lemma D_79c10 : decode_any W_79c10 = Some (Jal 1 76116, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c14 : bv 32 := 0x07010113.
Lemma F_79c14 : fetch_word AsanUbsan.M.loaded_segments (0x79c64 : word) = Some W_79c14.
Proof. vm_refl. Qed.
Lemma D_79c14 : decode_any W_79c14 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c18 : bv 32 := 0x7e813083.
Lemma F_79c18 : fetch_word AsanUbsan.M.loaded_segments (0x79c68 : word) = Some W_79c18.
Proof. vm_refl. Qed.
Lemma D_79c18 : decode_any W_79c18 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c1c : bv 32 := 0x7e013403.
Lemma F_79c1c : fetch_word AsanUbsan.M.loaded_segments (0x79c6c : word) = Some W_79c1c.
Proof. vm_refl. Qed.
Lemma D_79c1c : decode_any W_79c1c = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c20 : bv 32 := 0x7d813483.
Lemma F_79c20 : fetch_word AsanUbsan.M.loaded_segments (0x79c70 : word) = Some W_79c20.
Proof. vm_refl. Qed.
Lemma D_79c20 : decode_any W_79c20 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c24 : bv 32 := 0x7d013903.
Lemma F_79c24 : fetch_word AsanUbsan.M.loaded_segments (0x79c74 : word) = Some W_79c24.
Proof. vm_refl. Qed.
Lemma D_79c24 : decode_any W_79c24 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c28 : bv 32 := 0x7c813983.
Lemma F_79c28 : fetch_word AsanUbsan.M.loaded_segments (0x79c78 : word) = Some W_79c28.
Proof. vm_refl. Qed.
Lemma D_79c28 : decode_any W_79c28 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c2c : bv 32 := 0x7c013a03.
Lemma F_79c2c : fetch_word AsanUbsan.M.loaded_segments (0x79c7c : word) = Some W_79c2c.
Proof. vm_refl. Qed.
Lemma D_79c2c : decode_any W_79c2c = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c30 : bv 32 := 0x7b813a83.
Lemma F_79c30 : fetch_word AsanUbsan.M.loaded_segments (0x79c80 : word) = Some W_79c30.
Proof. vm_refl. Qed.
Lemma D_79c30 : decode_any W_79c30 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c34 : bv 32 := 0x7b013b03.
Lemma F_79c34 : fetch_word AsanUbsan.M.loaded_segments (0x79c84 : word) = Some W_79c34.
Proof. vm_refl. Qed.
Lemma D_79c34 : decode_any W_79c34 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c38 : bv 32 := 0x7a813b83.
Lemma F_79c38 : fetch_word AsanUbsan.M.loaded_segments (0x79c88 : word) = Some W_79c38.
Proof. vm_refl. Qed.
Lemma D_79c38 : decode_any W_79c38 = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c3c : bv 32 := 0x7f010113.
Lemma F_79c3c : fetch_word AsanUbsan.M.loaded_segments (0x79c8c : word) = Some W_79c3c.
Proof. vm_refl. Qed.
Lemma D_79c3c : decode_any W_79c3c = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_79c40 : bv 32 := 0x00008067.
Lemma F_79c40 : fetch_word AsanUbsan.M.loaded_segments (0x79c90 : word) = Some W_79c40.
Proof. vm_refl. Qed.
Lemma D_79c40 : decode_any W_79c40 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79ccc : bv 32 := 0x0c061463.
Lemma F_79ccc : fetch_word AsanUbsan.M.loaded_segments (0x79d1c : word) = Some W_79ccc.
Proof. vm_refl. Qed.
Lemma D_79ccc : decode_any W_79ccc = Some (Branch BC_NE 12 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_79cd0 : bv 32 := 0xef5ff06f.
Lemma F_79cd0 : fetch_word AsanUbsan.M.loaded_segments (0x79d20 : word) = Some W_79cd0.
Proof. vm_refl. Qed.
Lemma D_79cd0 : decode_any W_79cd0 = Some (Jal 0 2096884, 4%Z).
Proof. vm_refl. Qed.

Definition W_79d58 : bv 32 := 0x12061e63.
Lemma F_79d58 : fetch_word AsanUbsan.M.loaded_segments (0x79da8 : word) = Some W_79d58.
Proof. vm_refl. Qed.
Lemma D_79d58 : decode_any W_79d58 = Some (Branch BC_NE 12 0 316, 4%Z).
Proof. vm_refl. Qed.

Definition W_79d5c : bv 32 := 0xeb5ff06f.
Lemma F_79d5c : fetch_word AsanUbsan.M.loaded_segments (0x79dac : word) = Some W_79d5c.
Proof. vm_refl. Qed.
Lemma D_79d5c : decode_any W_79d5c = Some (Jal 0 2096820, 4%Z).
Proof. vm_refl. Qed.

Definition W_79d60 : bv 32 := 0x00070803.
Lemma F_79d60 : fetch_word AsanUbsan.M.loaded_segments (0x79db0 : word) = Some W_79d60.
Proof. vm_refl. Qed.
Lemma D_79d60 : decode_any W_79d60 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79d64 : bv 32 := 0x0077f793.
Lemma F_79d64 : fetch_word AsanUbsan.M.loaded_segments (0x79db4 : word) = Some W_79d64.
Proof. vm_refl. Qed.
Lemma D_79d64 : decode_any W_79d64 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_79d68 : bv 32 := 0x010038b3.
Lemma F_79d68 : fetch_word AsanUbsan.M.loaded_segments (0x79db8 : word) = Some W_79d68.
Proof. vm_refl. Qed.
Lemma D_79d68 : decode_any W_79d68 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_79d6c : bv 32 := 0x0107a7b3.
Lemma F_79d6c : fetch_word AsanUbsan.M.loaded_segments (0x79dbc : word) = Some W_79d6c.
Proof. vm_refl. Qed.
Lemma D_79d6c : decode_any W_79d6c = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_79d70 : bv 32 := 0x0017c793.
Lemma F_79d70 : fetch_word AsanUbsan.M.loaded_segments (0x79dc0 : word) = Some W_79d70.
Proof. vm_refl. Qed.
Lemma D_79d70 : decode_any W_79d70 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_79d74 : bv 32 := 0x00f8f7b3.
Lemma F_79d74 : fetch_word AsanUbsan.M.loaded_segments (0x79dc4 : word) = Some W_79d74.
Proof. vm_refl. Qed.
Lemma D_79d74 : decode_any W_79d74 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_79d78 : bv 32 := 0x00e6fa63.
Lemma F_79d78 : fetch_word AsanUbsan.M.loaded_segments (0x79dc8 : word) = Some W_79d78.
Proof. vm_refl. Qed.
Lemma D_79d78 : decode_any W_79d78 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_79d7c : bv 32 := 0x0006c803.
Lemma F_79d7c : fetch_word AsanUbsan.M.loaded_segments (0x79dcc : word) = Some W_79d7c.
Proof. vm_refl. Qed.
Lemma D_79d7c : decode_any W_79d7c = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79d80 : bv 32 := 0x00168693.
Lemma F_79d80 : fetch_word AsanUbsan.M.loaded_segments (0x79dd0 : word) = Some W_79d80.
Proof. vm_refl. Qed.
Lemma D_79d80 : decode_any W_79d80 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_79d84 : bv 32 := 0x00f867b3.
Lemma F_79d84 : fetch_word AsanUbsan.M.loaded_segments (0x79dd4 : word) = Some W_79d84.
Proof. vm_refl. Qed.
Lemma D_79d84 : decode_any W_79d84 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_79d88 : bv 32 := 0xfee69ae3.
Lemma F_79d88 : fetch_word AsanUbsan.M.loaded_segments (0x79dd8 : word) = Some W_79d88.
Proof. vm_refl. Qed.
Lemma D_79d88 : decode_any W_79d88 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_79d8c : bv 32 := 0x0ff7f693.
Lemma F_79d8c : fetch_word AsanUbsan.M.loaded_segments (0x79ddc : word) = Some W_79d8c.
Proof. vm_refl. Qed.
Lemma D_79d8c : decode_any W_79d8c = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_79d90 : bv 32 := 0xe2068ae3.
Lemma F_79d90 : fetch_word AsanUbsan.M.loaded_segments (0x79de0 : word) = Some W_79d90.
Proof. vm_refl. Qed.
Lemma D_79d90 : decode_any W_79d90 = Some (Branch BC_EQ 13 0 7732, 4%Z).
Proof. vm_refl. Qed.

Definition W_79d94 : bv 32 := 0x00050b13.
Lemma F_79d94 : fetch_word AsanUbsan.M.loaded_segments (0x79de4 : word) = Some W_79d94.
Proof. vm_refl. Qed.
Lemma D_79d94 : decode_any W_79d94 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79d98 : bv 32 := 0x00058513.
Lemma F_79d98 : fetch_word AsanUbsan.M.loaded_segments (0x79de8 : word) = Some W_79d98.
Proof. vm_refl. Qed.
Lemma D_79d98 : decode_any W_79d98 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79d9c : bv 32 := 0x00058b93.
Lemma F_79d9c : fetch_word AsanUbsan.M.loaded_segments (0x79dec : word) = Some W_79d9c.
Proof. vm_refl. Qed.
Lemma D_79d9c : decode_any W_79d9c = Some (OpImm ALU_ADD 23 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79da0 : bv 32 := 0x00060593.
Lemma F_79da0 : fetch_word AsanUbsan.M.loaded_segments (0x79df0 : word) = Some W_79da0.
Proof. vm_refl. Qed.
Lemma D_79da0 : decode_any W_79da0 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79da4 : bv 32 := 0x00060493.
Lemma F_79da4 : fetch_word AsanUbsan.M.loaded_segments (0x79df4 : word) = Some W_79da4.
Proof. vm_refl. Qed.
Lemma D_79da4 : decode_any W_79da4 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79da8 : bv 32 := 0x075020ef.
Lemma F_79da8 : fetch_word AsanUbsan.M.loaded_segments (0x79df8 : word) = Some W_79da8.
Proof. vm_refl. Qed.
Lemma D_79da8 : decode_any W_79da8 = Some (Jal 1 10356, 4%Z).
Proof. vm_refl. Qed.

Definition W_79dac : bv 32 := 0x000b8593.
Lemma F_79dac : fetch_word AsanUbsan.M.loaded_segments (0x79dfc : word) = Some W_79dac.
Proof. vm_refl. Qed.
Lemma D_79dac : decode_any W_79dac = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79db0 : bv 32 := 0x00048613.
Lemma F_79db0 : fetch_word AsanUbsan.M.loaded_segments (0x79e00 : word) = Some W_79db0.
Proof. vm_refl. Qed.
Lemma D_79db0 : decode_any W_79db0 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79db4 : bv 32 := 0x00050913.
Lemma F_79db4 : fetch_word AsanUbsan.M.loaded_segments (0x79e04 : word) = Some W_79db4.
Proof. vm_refl. Qed.
Lemma D_79db4 : decode_any W_79db4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79db8 : bv 32 := 0x000b0513.
Lemma F_79db8 : fetch_word AsanUbsan.M.loaded_segments (0x79e08 : word) = Some W_79db8.
Proof. vm_refl. Qed.
Lemma D_79db8 : decode_any W_79db8 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79dbc : bv 32 := 0xe00904e3.
Lemma F_79dbc : fetch_word AsanUbsan.M.loaded_segments (0x79e0c : word) = Some W_79dbc.
Proof. vm_refl. Qed.
Lemma D_79dbc : decode_any W_79dbc = Some (Branch BC_EQ 18 0 7688, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e60 : bv 32 := 0x00070803.
Lemma F_79e60 : fetch_word AsanUbsan.M.loaded_segments (0x79eb0 : word) = Some W_79e60.
Proof. vm_refl. Qed.
Lemma D_79e60 : decode_any W_79e60 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e64 : bv 32 := 0x0077f793.
Lemma F_79e64 : fetch_word AsanUbsan.M.loaded_segments (0x79eb4 : word) = Some W_79e64.
Proof. vm_refl. Qed.
Lemma D_79e64 : decode_any W_79e64 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e68 : bv 32 := 0x010038b3.
Lemma F_79e68 : fetch_word AsanUbsan.M.loaded_segments (0x79eb8 : word) = Some W_79e68.
Proof. vm_refl. Qed.
Lemma D_79e68 : decode_any W_79e68 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e6c : bv 32 := 0x0107a7b3.
Lemma F_79e6c : fetch_word AsanUbsan.M.loaded_segments (0x79ebc : word) = Some W_79e6c.
Proof. vm_refl. Qed.
Lemma D_79e6c : decode_any W_79e6c = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e70 : bv 32 := 0x0017c793.
Lemma F_79e70 : fetch_word AsanUbsan.M.loaded_segments (0x79ec0 : word) = Some W_79e70.
Proof. vm_refl. Qed.
Lemma D_79e70 : decode_any W_79e70 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e74 : bv 32 := 0x00f8f7b3.
Lemma F_79e74 : fetch_word AsanUbsan.M.loaded_segments (0x79ec4 : word) = Some W_79e74.
Proof. vm_refl. Qed.
Lemma D_79e74 : decode_any W_79e74 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e78 : bv 32 := 0x00e6fa63.
Lemma F_79e78 : fetch_word AsanUbsan.M.loaded_segments (0x79ec8 : word) = Some W_79e78.
Proof. vm_refl. Qed.
Lemma D_79e78 : decode_any W_79e78 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e7c : bv 32 := 0x0006c803.
Lemma F_79e7c : fetch_word AsanUbsan.M.loaded_segments (0x79ecc : word) = Some W_79e7c.
Proof. vm_refl. Qed.
Lemma D_79e7c : decode_any W_79e7c = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e80 : bv 32 := 0x00168693.
Lemma F_79e80 : fetch_word AsanUbsan.M.loaded_segments (0x79ed0 : word) = Some W_79e80.
Proof. vm_refl. Qed.
Lemma D_79e80 : decode_any W_79e80 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e84 : bv 32 := 0x00f867b3.
Lemma F_79e84 : fetch_word AsanUbsan.M.loaded_segments (0x79ed4 : word) = Some W_79e84.
Proof. vm_refl. Qed.
Lemma D_79e84 : decode_any W_79e84 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e88 : bv 32 := 0xfee69ae3.
Lemma F_79e88 : fetch_word AsanUbsan.M.loaded_segments (0x79ed8 : word) = Some W_79e88.
Proof. vm_refl. Qed.
Lemma D_79e88 : decode_any W_79e88 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e8c : bv 32 := 0x0ff7f693.
Lemma F_79e8c : fetch_word AsanUbsan.M.loaded_segments (0x79edc : word) = Some W_79e8c.
Proof. vm_refl. Qed.
Lemma D_79e8c : decode_any W_79e8c = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e90 : bv 32 := 0xd80680e3.
Lemma F_79e90 : fetch_word AsanUbsan.M.loaded_segments (0x79ee0 : word) = Some W_79e90.
Proof. vm_refl. Qed.
Lemma D_79e90 : decode_any W_79e90 = Some (Branch BC_EQ 13 0 7552, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e94 : bv 32 := 0x00050493.
Lemma F_79e94 : fetch_word AsanUbsan.M.loaded_segments (0x79ee4 : word) = Some W_79e94.
Proof. vm_refl. Qed.
Lemma D_79e94 : decode_any W_79e94 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e98 : bv 32 := 0x00058b13.
Lemma F_79e98 : fetch_word AsanUbsan.M.loaded_segments (0x79ee8 : word) = Some W_79e98.
Proof. vm_refl. Qed.
Lemma D_79e98 : decode_any W_79e98 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e9c : bv 32 := 0x00060593.
Lemma F_79e9c : fetch_word AsanUbsan.M.loaded_segments (0x79eec : word) = Some W_79e9c.
Proof. vm_refl. Qed.
Lemma D_79e9c : decode_any W_79e9c = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79ea0 : bv 32 := 0x00060913.
Lemma F_79ea0 : fetch_word AsanUbsan.M.loaded_segments (0x79ef0 : word) = Some W_79ea0.
Proof. vm_refl. Qed.
Lemma D_79ea0 : decode_any W_79ea0 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79ea4 : bv 32 := 0x778020ef.
Lemma F_79ea4 : fetch_word AsanUbsan.M.loaded_segments (0x79ef4 : word) = Some W_79ea4.
Proof. vm_refl. Qed.
Lemma D_79ea4 : decode_any W_79ea4 = Some (Jal 1 10104, 4%Z).
Proof. vm_refl. Qed.

Definition W_79ea8 : bv 32 := 0x000b0593.
Lemma F_79ea8 : fetch_word AsanUbsan.M.loaded_segments (0x79ef8 : word) = Some W_79ea8.
Proof. vm_refl. Qed.
Lemma D_79ea8 : decode_any W_79ea8 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79eac : bv 32 := 0x00090613.
Lemma F_79eac : fetch_word AsanUbsan.M.loaded_segments (0x79efc : word) = Some W_79eac.
Proof. vm_refl. Qed.
Lemma D_79eac : decode_any W_79eac = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79eb0 : bv 32 := 0x00050993.
Lemma F_79eb0 : fetch_word AsanUbsan.M.loaded_segments (0x79f00 : word) = Some W_79eb0.
Proof. vm_refl. Qed.
Lemma D_79eb0 : decode_any W_79eb0 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79eb4 : bv 32 := 0x00048513.
Lemma F_79eb4 : fetch_word AsanUbsan.M.loaded_segments (0x79f04 : word) = Some W_79eb4.
Proof. vm_refl. Qed.
Lemma D_79eb4 : decode_any W_79eb4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79eb8 : bv 32 := 0xd4098ce3.
Lemma F_79eb8 : fetch_word AsanUbsan.M.loaded_segments (0x79f08 : word) = Some W_79eb8.
Proof. vm_refl. Qed.
Lemma D_79eb8 : decode_any W_79eb8 = Some (Branch BC_EQ 19 0 7512, 4%Z).
Proof. vm_refl. Qed.

Definition W_79fec : bv 32 := 0x81010113.
Lemma F_79fec : fetch_word AsanUbsan.M.loaded_segments (0x7a03c : word) = Some W_79fec.
Proof. vm_refl. Qed.
Lemma D_79fec : decode_any W_79fec = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_79ff0 : bv 32 := 0x7e113423.
Lemma F_79ff0 : fetch_word AsanUbsan.M.loaded_segments (0x7a040 : word) = Some W_79ff0.
Proof. vm_refl. Qed.
Lemma D_79ff0 : decode_any W_79ff0 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_79ff4 : bv 32 := 0x7e813023.
Lemma F_79ff4 : fetch_word AsanUbsan.M.loaded_segments (0x7a044 : word) = Some W_79ff4.
Proof. vm_refl. Qed.
Lemma D_79ff4 : decode_any W_79ff4 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_79ff8 : bv 32 := 0x7c913c23.
Lemma F_79ff8 : fetch_word AsanUbsan.M.loaded_segments (0x7a048 : word) = Some W_79ff8.
Proof. vm_refl. Qed.
Lemma D_79ff8 : decode_any W_79ff8 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_79ffc : bv 32 := 0x7d213823.
Lemma F_79ffc : fetch_word AsanUbsan.M.loaded_segments (0x7a04c : word) = Some W_79ffc.
Proof. vm_refl. Qed.
Lemma D_79ffc : decode_any W_79ffc = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a000 : bv 32 := 0x7d313423.
Lemma F_7a000 : fetch_word AsanUbsan.M.loaded_segments (0x7a050 : word) = Some W_7a000.
Proof. vm_refl. Qed.
Lemma D_7a000 : decode_any W_7a000 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a004 : bv 32 := 0x7d413023.
Lemma F_7a004 : fetch_word AsanUbsan.M.loaded_segments (0x7a054 : word) = Some W_7a004.
Proof. vm_refl. Qed.
Lemma D_7a004 : decode_any W_7a004 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a008 : bv 32 := 0x7b513c23.
Lemma F_7a008 : fetch_word AsanUbsan.M.loaded_segments (0x7a058 : word) = Some W_7a008.
Proof. vm_refl. Qed.
Lemma D_7a008 : decode_any W_7a008 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a00c : bv 32 := 0x7b613823.
Lemma F_7a00c : fetch_word AsanUbsan.M.loaded_segments (0x7a05c : word) = Some W_7a00c.
Proof. vm_refl. Qed.
Lemma D_7a00c : decode_any W_7a00c = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a010 : bv 32 := 0x7b713423.
Lemma F_7a010 : fetch_word AsanUbsan.M.loaded_segments (0x7a060 : word) = Some W_7a010.
Proof. vm_refl. Qed.
Lemma D_7a010 : decode_any W_7a010 = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a014 : bv 32 := 0x7b813023.
Lemma F_7a014 : fetch_word AsanUbsan.M.loaded_segments (0x7a064 : word) = Some W_7a014.
Proof. vm_refl. Qed.
Lemma D_7a014 : decode_any W_7a014 = Some (Store SZ8 2 24 1952, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a018 : bv 32 := 0x7f010413.
Lemma F_7a018 : fetch_word AsanUbsan.M.loaded_segments (0x7a068 : word) = Some W_7a018.
Proof. vm_refl. Qed.
Lemma D_7a018 : decode_any W_7a018 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a01c : bv 32 := 0xf8010113.
Lemma F_7a01c : fetch_word AsanUbsan.M.loaded_segments (0x7a06c : word) = Some W_7a01c.
Proof. vm_refl. Qed.
Lemma D_7a01c : decode_any W_7a01c = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a020 : bv 32 := 0x000c4697.
Lemma F_7a020 : fetch_word AsanUbsan.M.loaded_segments (0x7a070 : word) = Some W_7a020.
Proof. vm_refl. Qed.
Lemma D_7a020 : decode_any W_7a020 = Some (Auipc 13 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a024 : bv 32 := 0x3c06b683.
Lemma F_7a024 : fetch_word AsanUbsan.M.loaded_segments (0x7a074 : word) = Some W_7a024.
Proof. vm_refl. Qed.
Lemma D_7a024 : decode_any W_7a024 = Some (Load SZ8 true 13 13 960, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a028 : bv 32 := 0x0006c683.
Lemma F_7a028 : fetch_word AsanUbsan.M.loaded_segments (0x7a078 : word) = Some W_7a028.
Proof. vm_refl. Qed.
Lemma D_7a028 : decode_any W_7a028 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a02c : bv 32 := 0x0e068a63.
Lemma F_7a02c : fetch_word AsanUbsan.M.loaded_segments (0x7a07c : word) = Some W_7a02c.
Proof. vm_refl. Qed.
Lemma D_7a02c : decode_any W_7a02c = Some (Branch BC_EQ 13 0 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a030 : bv 32 := 0x80040a93.
Lemma F_7a030 : fetch_word AsanUbsan.M.loaded_segments (0x7a080 : word) = Some W_7a030.
Proof. vm_refl. Qed.
Lemma D_7a030 : decode_any W_7a030 = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a034 : bv 32 := 0xf98a8a93.
Lemma F_7a034 : fetch_word AsanUbsan.M.loaded_segments (0x7a084 : word) = Some W_7a034.
Proof. vm_refl. Qed.
Lemma D_7a034 : decode_any W_7a034 = Some (OpImm ALU_ADD 21 21 3992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a038 : bv 32 := 0x00c589b3.
Lemma F_7a038 : fetch_word AsanUbsan.M.loaded_segments (0x7a088 : word) = Some W_7a038.
Proof. vm_refl. Qed.
Lemma D_7a038 : decode_any W_7a038 = Some (Op ALU_ADD 19 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a03c : bv 32 := 0x00c50a33.
Lemma F_7a03c : fetch_word AsanUbsan.M.loaded_segments (0x7a08c : word) = Some W_7a03c.
Proof. vm_refl. Qed.
Lemma D_7a03c : decode_any W_7a03c = Some (Op ALU_ADD 20 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a040 : bv 32 := 0x00b50663.
Lemma F_7a040 : fetch_word AsanUbsan.M.loaded_segments (0x7a090 : word) = Some W_7a040.
Proof. vm_refl. Qed.
Lemma D_7a040 : decode_any W_7a040 = Some (Branch BC_EQ 10 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a044 : bv 32 := 0x0145f463.
Lemma F_7a044 : fetch_word AsanUbsan.M.loaded_segments (0x7a094 : word) = Some W_7a044.
Proof. vm_refl. Qed.
Lemma D_7a044 : decode_any W_7a044 = Some (Branch BC_GEU 11 20 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a048 : bv 32 := 0x1b356e63.
Lemma F_7a048 : fetch_word AsanUbsan.M.loaded_segments (0x7a098 : word) = Some W_7a048.
Proof. vm_refl. Qed.
Lemma D_7a048 : decode_any W_7a048 = Some (Branch BC_LTU 10 19 444, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a04c : bv 32 := 0xfff5c693.
Lemma F_7a04c : fetch_word AsanUbsan.M.loaded_segments (0x7a09c : word) = Some W_7a04c.
Proof. vm_refl. Qed.
Lemma D_7a04c : decode_any W_7a04c = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a050 : bv 32 := 0x26c6e863.
Lemma F_7a050 : fetch_word AsanUbsan.M.loaded_segments (0x7a0a0 : word) = Some W_7a050.
Proof. vm_refl. Qed.
Lemma D_7a050 : decode_any W_7a050 = Some (Branch BC_LTU 13 12 624, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a054 : bv 32 := 0xfbf60b13.
Lemma F_7a054 : fetch_word AsanUbsan.M.loaded_segments (0x7a0a4 : word) = Some W_7a054.
Proof. vm_refl. Qed.
Lemma D_7a054 : decode_any W_7a054 = Some (OpImm ALU_ADD 22 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a058 : bv 32 := 0xfbf00693.
Lemma F_7a058 : fetch_word AsanUbsan.M.loaded_segments (0x7a0a8 : word) = Some W_7a058.
Proof. vm_refl. Qed.
Lemma D_7a058 : decode_any W_7a058 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a05c : bv 32 := 0x2f66f663.
Lemma F_7a05c : fetch_word AsanUbsan.M.loaded_segments (0x7a0ac : word) = Some W_7a05c.
Proof. vm_refl. Qed.
Lemma D_7a05c : decode_any W_7a05c = Some (Branch BC_GEU 13 22 748, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a060 : bv 32 := 0x000c4697.
Lemma F_7a060 : fetch_word AsanUbsan.M.loaded_segments (0x7a0b0 : word) = Some W_7a060.
Proof. vm_refl. Qed.
Lemma D_7a060 : decode_any W_7a060 = Some (Auipc 13 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a064 : bv 32 := 0x8186b683.
Lemma F_7a064 : fetch_word AsanUbsan.M.loaded_segments (0x7a0b4 : word) = Some W_7a064.
Proof. vm_refl. Qed.
Lemma D_7a064 : decode_any W_7a064 = Some (Load SZ8 true 13 13 2072, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a068 : bv 32 := 0x0006b703.
Lemma F_7a068 : fetch_word AsanUbsan.M.loaded_segments (0x7a0b8 : word) = Some W_7a068.
Proof. vm_refl. Qed.
Lemma D_7a068 : decode_any W_7a068 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a06c : bv 32 := 0xfff98993.
Lemma F_7a06c : fetch_word AsanUbsan.M.loaded_segments (0x7a0bc : word) = Some W_7a06c.
Proof. vm_refl. Qed.
Lemma D_7a06c : decode_any W_7a06c = Some (OpImm ALU_ADD 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a070 : bv 32 := 0x0035d693.
Lemma F_7a070 : fetch_word AsanUbsan.M.loaded_segments (0x7a0c0 : word) = Some W_7a070.
Proof. vm_refl. Qed.
Lemma D_7a070 : decode_any W_7a070 = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a074 : bv 32 := 0x0039d793.
Lemma F_7a074 : fetch_word AsanUbsan.M.loaded_segments (0x7a0c4 : word) = Some W_7a074.
Proof. vm_refl. Qed.
Lemma D_7a074 : decode_any W_7a074 = Some (ShiftImm ALU_SRL 15 19 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a078 : bv 32 := 0x00d706b3.
Lemma F_7a078 : fetch_word AsanUbsan.M.loaded_segments (0x7a0c8 : word) = Some W_7a078.
Proof. vm_refl. Qed.
Lemma D_7a078 : decode_any W_7a078 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a07c : bv 32 := 0x00f70733.
Lemma F_7a07c : fetch_word AsanUbsan.M.loaded_segments (0x7a0cc : word) = Some W_7a07c.
Proof. vm_refl. Qed.
Lemma D_7a07c : decode_any W_7a07c = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a080 : bv 32 := 0xff86f793.
Lemma F_7a080 : fetch_word AsanUbsan.M.loaded_segments (0x7a0d0 : word) = Some W_7a080.
Proof. vm_refl. Qed.
Lemma D_7a080 : decode_any W_7a080 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a084 : bv 32 := 0xff877813.
Lemma F_7a084 : fetch_word AsanUbsan.M.loaded_segments (0x7a0d4 : word) = Some W_7a084.
Proof. vm_refl. Qed.
Lemma D_7a084 : decode_any W_7a084 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a088 : bv 32 := 0x0007b783.
Lemma F_7a088 : fetch_word AsanUbsan.M.loaded_segments (0x7a0d8 : word) = Some W_7a088.
Proof. vm_refl. Qed.
Lemma D_7a088 : decode_any W_7a088 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a08c : bv 32 := 0x00083803.
Lemma F_7a08c : fetch_word AsanUbsan.M.loaded_segments (0x7a0dc : word) = Some W_7a08c.
Proof. vm_refl. Qed.
Lemma D_7a08c : decode_any W_7a08c = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a090 : bv 32 := 0x00f867b3.
Lemma F_7a090 : fetch_word AsanUbsan.M.loaded_segments (0x7a0e0 : word) = Some W_7a090.
Proof. vm_refl. Qed.
Lemma D_7a090 : decode_any W_7a090 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a094 : bv 32 := 0x2a079e63.
Lemma F_7a094 : fetch_word AsanUbsan.M.loaded_segments (0x7a0e4 : word) = Some W_7a094.
Proof. vm_refl. Qed.
Lemma D_7a094 : decode_any W_7a094 = Some (Branch BC_NE 15 0 700, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a098 : bv 32 := 0xfff54693.
Lemma F_7a098 : fetch_word AsanUbsan.M.loaded_segments (0x7a0e8 : word) = Some W_7a098.
Proof. vm_refl. Qed.
Lemma D_7a098 : decode_any W_7a098 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a09c : bv 32 := 0x0cc6ee63.
Lemma F_7a09c : fetch_word AsanUbsan.M.loaded_segments (0x7a0ec : word) = Some W_7a09c.
Proof. vm_refl. Qed.
Lemma D_7a09c : decode_any W_7a09c = Some (Branch BC_LTU 13 12 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a0a0 : bv 32 := 0xfbf00693.
Lemma F_7a0a0 : fetch_word AsanUbsan.M.loaded_segments (0x7a0f0 : word) = Some W_7a0a0.
Proof. vm_refl. Qed.
Lemma D_7a0a0 : decode_any W_7a0a0 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a0a4 : bv 32 := 0x1566fc63.
Lemma F_7a0a4 : fetch_word AsanUbsan.M.loaded_segments (0x7a0f4 : word) = Some W_7a0a4.
Proof. vm_refl. Qed.
Lemma D_7a0a4 : decode_any W_7a0a4 = Some (Branch BC_GEU 13 22 344, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a0a8 : bv 32 := 0x000c3697.
Lemma F_7a0a8 : fetch_word AsanUbsan.M.loaded_segments (0x7a0f8 : word) = Some W_7a0a8.
Proof. vm_refl. Qed.
Lemma D_7a0a8 : decode_any W_7a0a8 = Some (Auipc 13 195, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a0ac : bv 32 := 0x7d06b683.
Lemma F_7a0ac : fetch_word AsanUbsan.M.loaded_segments (0x7a0fc : word) = Some W_7a0ac.
Proof. vm_refl. Qed.
Lemma D_7a0ac : decode_any W_7a0ac = Some (Load SZ8 true 13 13 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a0b0 : bv 32 := 0x0006b703.
Lemma F_7a0b0 : fetch_word AsanUbsan.M.loaded_segments (0x7a100 : word) = Some W_7a0b0.
Proof. vm_refl. Qed.
Lemma D_7a0b0 : decode_any W_7a0b0 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a0b4 : bv 32 := 0xfffa0a13.
Lemma F_7a0b4 : fetch_word AsanUbsan.M.loaded_segments (0x7a104 : word) = Some W_7a0b4.
Proof. vm_refl. Qed.
Lemma D_7a0b4 : decode_any W_7a0b4 = Some (OpImm ALU_ADD 20 20 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a0b8 : bv 32 := 0x00355693.
Lemma F_7a0b8 : fetch_word AsanUbsan.M.loaded_segments (0x7a108 : word) = Some W_7a0b8.
Proof. vm_refl. Qed.
Lemma D_7a0b8 : decode_any W_7a0b8 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a0bc : bv 32 := 0x003a5793.
Lemma F_7a0bc : fetch_word AsanUbsan.M.loaded_segments (0x7a10c : word) = Some W_7a0bc.
Proof. vm_refl. Qed.
Lemma D_7a0bc : decode_any W_7a0bc = Some (ShiftImm ALU_SRL 15 20 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a0c0 : bv 32 := 0x00d706b3.
Lemma F_7a0c0 : fetch_word AsanUbsan.M.loaded_segments (0x7a110 : word) = Some W_7a0c0.
Proof. vm_refl. Qed.
Lemma D_7a0c0 : decode_any W_7a0c0 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a0c4 : bv 32 := 0x00f70733.
Lemma F_7a0c4 : fetch_word AsanUbsan.M.loaded_segments (0x7a114 : word) = Some W_7a0c4.
Proof. vm_refl. Qed.
Lemma D_7a0c4 : decode_any W_7a0c4 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a0c8 : bv 32 := 0xff86f793.
Lemma F_7a0c8 : fetch_word AsanUbsan.M.loaded_segments (0x7a118 : word) = Some W_7a0c8.
Proof. vm_refl. Qed.
Lemma D_7a0c8 : decode_any W_7a0c8 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a0cc : bv 32 := 0xff877813.
Lemma F_7a0cc : fetch_word AsanUbsan.M.loaded_segments (0x7a11c : word) = Some W_7a0cc.
Proof. vm_refl. Qed.
Lemma D_7a0cc : decode_any W_7a0cc = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a0d0 : bv 32 := 0x0007b783.
Lemma F_7a0d0 : fetch_word AsanUbsan.M.loaded_segments (0x7a120 : word) = Some W_7a0d0.
Proof. vm_refl. Qed.
Lemma D_7a0d0 : decode_any W_7a0d0 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a0d4 : bv 32 := 0x00083803.
Lemma F_7a0d4 : fetch_word AsanUbsan.M.loaded_segments (0x7a124 : word) = Some W_7a0d4.
Proof. vm_refl. Qed.
Lemma D_7a0d4 : decode_any W_7a0d4 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a0d8 : bv 32 := 0x00f867b3.
Lemma F_7a0d8 : fetch_word AsanUbsan.M.loaded_segments (0x7a128 : word) = Some W_7a0d8.
Proof. vm_refl. Qed.
Lemma D_7a0d8 : decode_any W_7a0d8 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a0dc : bv 32 := 0x36079a63.
Lemma F_7a0dc : fetch_word AsanUbsan.M.loaded_segments (0x7a12c : word) = Some W_7a0dc.
Proof. vm_refl. Qed.
Lemma D_7a0dc : decode_any W_7a0dc = Some (Branch BC_NE 15 0 884, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a0e0 : bv 32 := 0x000c5697.
Lemma F_7a0e0 : fetch_word AsanUbsan.M.loaded_segments (0x7a130 : word) = Some W_7a0e0.
Proof. vm_refl. Qed.
Lemma D_7a0e0 : decode_any W_7a0e0 = Some (Auipc 13 197, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a0e4 : bv 32 := 0x7a06b683.
Lemma F_7a0e4 : fetch_word AsanUbsan.M.loaded_segments (0x7a134 : word) = Some W_7a0e4.
Proof. vm_refl. Qed.
Lemma D_7a0e4 : decode_any W_7a0e4 = Some (Load SZ8 true 13 13 1952, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a0e8 : bv 32 := 0x000680e7.
Lemma F_7a0e8 : fetch_word AsanUbsan.M.loaded_segments (0x7a138 : word) = Some W_7a0e8.
Proof. vm_refl. Qed.
Lemma D_7a0e8 : decode_any W_7a0e8 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a0ec : bv 32 := 0x08010113.
Lemma F_7a0ec : fetch_word AsanUbsan.M.loaded_segments (0x7a13c : word) = Some W_7a0ec.
Proof. vm_refl. Qed.
Lemma D_7a0ec : decode_any W_7a0ec = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a0f0 : bv 32 := 0x7e813083.
Lemma F_7a0f0 : fetch_word AsanUbsan.M.loaded_segments (0x7a140 : word) = Some W_7a0f0.
Proof. vm_refl. Qed.
Lemma D_7a0f0 : decode_any W_7a0f0 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a0f4 : bv 32 := 0x7e013403.
Lemma F_7a0f4 : fetch_word AsanUbsan.M.loaded_segments (0x7a144 : word) = Some W_7a0f4.
Proof. vm_refl. Qed.
Lemma D_7a0f4 : decode_any W_7a0f4 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a0f8 : bv 32 := 0x7d813483.
Lemma F_7a0f8 : fetch_word AsanUbsan.M.loaded_segments (0x7a148 : word) = Some W_7a0f8.
Proof. vm_refl. Qed.
Lemma D_7a0f8 : decode_any W_7a0f8 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a0fc : bv 32 := 0x7d013903.
Lemma F_7a0fc : fetch_word AsanUbsan.M.loaded_segments (0x7a14c : word) = Some W_7a0fc.
Proof. vm_refl. Qed.
Lemma D_7a0fc : decode_any W_7a0fc = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a100 : bv 32 := 0x7c813983.
Lemma F_7a100 : fetch_word AsanUbsan.M.loaded_segments (0x7a150 : word) = Some W_7a100.
Proof. vm_refl. Qed.
Lemma D_7a100 : decode_any W_7a100 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a104 : bv 32 := 0x7c013a03.
Lemma F_7a104 : fetch_word AsanUbsan.M.loaded_segments (0x7a154 : word) = Some W_7a104.
Proof. vm_refl. Qed.
Lemma D_7a104 : decode_any W_7a104 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a108 : bv 32 := 0x7b813a83.
Lemma F_7a108 : fetch_word AsanUbsan.M.loaded_segments (0x7a158 : word) = Some W_7a108.
Proof. vm_refl. Qed.
Lemma D_7a108 : decode_any W_7a108 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a10c : bv 32 := 0x7b013b03.
Lemma F_7a10c : fetch_word AsanUbsan.M.loaded_segments (0x7a15c : word) = Some W_7a10c.
Proof. vm_refl. Qed.
Lemma D_7a10c : decode_any W_7a10c = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a110 : bv 32 := 0x7a813b83.
Lemma F_7a110 : fetch_word AsanUbsan.M.loaded_segments (0x7a160 : word) = Some W_7a110.
Proof. vm_refl. Qed.
Lemma D_7a110 : decode_any W_7a110 = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a114 : bv 32 := 0x7a013c03.
Lemma F_7a114 : fetch_word AsanUbsan.M.loaded_segments (0x7a164 : word) = Some W_7a114.
Proof. vm_refl. Qed.
Lemma D_7a114 : decode_any W_7a114 = Some (Load SZ8 true 24 2 1952, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a118 : bv 32 := 0x7f010113.
Lemma F_7a118 : fetch_word AsanUbsan.M.loaded_segments (0x7a168 : word) = Some W_7a118.
Proof. vm_refl. Qed.
Lemma D_7a118 : decode_any W_7a118 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a11c : bv 32 := 0x00008067.
Lemma F_7a11c : fetch_word AsanUbsan.M.loaded_segments (0x7a16c : word) = Some W_7a11c.
Proof. vm_refl. Qed.
Lemma D_7a11c : decode_any W_7a11c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a1fc : bv 32 := 0x28061463.
Lemma F_7a1fc : fetch_word AsanUbsan.M.loaded_segments (0x7a24c : word) = Some W_7a1fc.
Proof. vm_refl. Qed.
Lemma D_7a1fc : decode_any W_7a1fc = Some (Branch BC_NE 12 0 648, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a200 : bv 32 := 0xee1ff06f.
Lemma F_7a200 : fetch_word AsanUbsan.M.loaded_segments (0x7a250 : word) = Some W_7a200.
Proof. vm_refl. Qed.
Lemma D_7a200 : decode_any W_7a200 = Some (Jal 0 2096864, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a348 : bv 32 := 0x02061e63.
Lemma F_7a348 : fetch_word AsanUbsan.M.loaded_segments (0x7a398 : word) = Some W_7a348.
Proof. vm_refl. Qed.
Lemma D_7a348 : decode_any W_7a348 = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a34c : bv 32 := 0xd4dff06f.
Lemma F_7a34c : fetch_word AsanUbsan.M.loaded_segments (0x7a39c : word) = Some W_7a34c.
Proof. vm_refl. Qed.
Lemma D_7a34c : decode_any W_7a34c = Some (Jal 0 2096460, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a350 : bv 32 := 0x00070783.
Lemma F_7a350 : fetch_word AsanUbsan.M.loaded_segments (0x7a3a0 : word) = Some W_7a350.
Proof. vm_refl. Qed.
Lemma D_7a350 : decode_any W_7a350 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a354 : bv 32 := 0x0079f813.
Lemma F_7a354 : fetch_word AsanUbsan.M.loaded_segments (0x7a3a4 : word) = Some W_7a354.
Proof. vm_refl. Qed.
Lemma D_7a354 : decode_any W_7a354 = Some (OpImm ALU_AND 16 19 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a358 : bv 32 := 0x00f038b3.
Lemma F_7a358 : fetch_word AsanUbsan.M.loaded_segments (0x7a3a8 : word) = Some W_7a358.
Proof. vm_refl. Qed.
Lemma D_7a358 : decode_any W_7a358 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a35c : bv 32 := 0x00f827b3.
Lemma F_7a35c : fetch_word AsanUbsan.M.loaded_segments (0x7a3ac : word) = Some W_7a35c.
Proof. vm_refl. Qed.
Lemma D_7a35c : decode_any W_7a35c = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a360 : bv 32 := 0x0017c793.
Lemma F_7a360 : fetch_word AsanUbsan.M.loaded_segments (0x7a3b0 : word) = Some W_7a360.
Proof. vm_refl. Qed.
Lemma D_7a360 : decode_any W_7a360 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a364 : bv 32 := 0x00f8f7b3.
Lemma F_7a364 : fetch_word AsanUbsan.M.loaded_segments (0x7a3b4 : word) = Some W_7a364.
Proof. vm_refl. Qed.
Lemma D_7a364 : decode_any W_7a364 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a368 : bv 32 := 0x00e6fa63.
Lemma F_7a368 : fetch_word AsanUbsan.M.loaded_segments (0x7a3b8 : word) = Some W_7a368.
Proof. vm_refl. Qed.
Lemma D_7a368 : decode_any W_7a368 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a36c : bv 32 := 0x0006c803.
Lemma F_7a36c : fetch_word AsanUbsan.M.loaded_segments (0x7a3bc : word) = Some W_7a36c.
Proof. vm_refl. Qed.
Lemma D_7a36c : decode_any W_7a36c = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a370 : bv 32 := 0x00168693.
Lemma F_7a370 : fetch_word AsanUbsan.M.loaded_segments (0x7a3c0 : word) = Some W_7a370.
Proof. vm_refl. Qed.
Lemma D_7a370 : decode_any W_7a370 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a374 : bv 32 := 0x00f867b3.
Lemma F_7a374 : fetch_word AsanUbsan.M.loaded_segments (0x7a3c4 : word) = Some W_7a374.
Proof. vm_refl. Qed.
Lemma D_7a374 : decode_any W_7a374 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a378 : bv 32 := 0xfee69ae3.
Lemma F_7a378 : fetch_word AsanUbsan.M.loaded_segments (0x7a3c8 : word) = Some W_7a378.
Proof. vm_refl. Qed.
Lemma D_7a378 : decode_any W_7a378 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a37c : bv 32 := 0x0ff7f693.
Lemma F_7a37c : fetch_word AsanUbsan.M.loaded_segments (0x7a3cc : word) = Some W_7a37c.
Proof. vm_refl. Qed.
Lemma D_7a37c : decode_any W_7a37c = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a380 : bv 32 := 0xd0068ce3.
Lemma F_7a380 : fetch_word AsanUbsan.M.loaded_segments (0x7a3d0 : word) = Some W_7a380.
Proof. vm_refl. Qed.
Lemma D_7a380 : decode_any W_7a380 = Some (Branch BC_EQ 13 0 7448, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a384 : bv 32 := 0x00050b93.
Lemma F_7a384 : fetch_word AsanUbsan.M.loaded_segments (0x7a3d4 : word) = Some W_7a384.
Proof. vm_refl. Qed.
Lemma D_7a384 : decode_any W_7a384 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a388 : bv 32 := 0x00058513.
Lemma F_7a388 : fetch_word AsanUbsan.M.loaded_segments (0x7a3d8 : word) = Some W_7a388.
Proof. vm_refl. Qed.
Lemma D_7a388 : decode_any W_7a388 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a38c : bv 32 := 0x00058c13.
Lemma F_7a38c : fetch_word AsanUbsan.M.loaded_segments (0x7a3dc : word) = Some W_7a38c.
Proof. vm_refl. Qed.
Lemma D_7a38c : decode_any W_7a38c = Some (OpImm ALU_ADD 24 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a390 : bv 32 := 0x00060593.
Lemma F_7a390 : fetch_word AsanUbsan.M.loaded_segments (0x7a3e0 : word) = Some W_7a390.
Proof. vm_refl. Qed.
Lemma D_7a390 : decode_any W_7a390 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a394 : bv 32 := 0x00060493.
Lemma F_7a394 : fetch_word AsanUbsan.M.loaded_segments (0x7a3e4 : word) = Some W_7a394.
Proof. vm_refl. Qed.
Lemma D_7a394 : decode_any W_7a394 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a398 : bv 32 := 0x284020ef.
Lemma F_7a398 : fetch_word AsanUbsan.M.loaded_segments (0x7a3e8 : word) = Some W_7a398.
Proof. vm_refl. Qed.
Lemma D_7a398 : decode_any W_7a398 = Some (Jal 1 8836, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a39c : bv 32 := 0x000c0593.
Lemma F_7a39c : fetch_word AsanUbsan.M.loaded_segments (0x7a3ec : word) = Some W_7a39c.
Proof. vm_refl. Qed.
Lemma D_7a39c : decode_any W_7a39c = Some (OpImm ALU_ADD 11 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a3a0 : bv 32 := 0x00048613.
Lemma F_7a3a0 : fetch_word AsanUbsan.M.loaded_segments (0x7a3f0 : word) = Some W_7a3a0.
Proof. vm_refl. Qed.
Lemma D_7a3a0 : decode_any W_7a3a0 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a3a4 : bv 32 := 0x00050913.
Lemma F_7a3a4 : fetch_word AsanUbsan.M.loaded_segments (0x7a3f4 : word) = Some W_7a3a4.
Proof. vm_refl. Qed.
Lemma D_7a3a4 : decode_any W_7a3a4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a3a8 : bv 32 := 0x000b8513.
Lemma F_7a3a8 : fetch_word AsanUbsan.M.loaded_segments (0x7a3f8 : word) = Some W_7a3a8.
Proof. vm_refl. Qed.
Lemma D_7a3a8 : decode_any W_7a3a8 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a3ac : bv 32 := 0xce0906e3.
Lemma F_7a3ac : fetch_word AsanUbsan.M.loaded_segments (0x7a3fc : word) = Some W_7a3ac.
Proof. vm_refl. Qed.
Lemma D_7a3ac : decode_any W_7a3ac = Some (Branch BC_EQ 18 0 7404, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a450 : bv 32 := 0x00070783.
Lemma F_7a450 : fetch_word AsanUbsan.M.loaded_segments (0x7a4a0 : word) = Some W_7a450.
Proof. vm_refl. Qed.
Lemma D_7a450 : decode_any W_7a450 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a454 : bv 32 := 0x007a7813.
Lemma F_7a454 : fetch_word AsanUbsan.M.loaded_segments (0x7a4a4 : word) = Some W_7a454.
Proof. vm_refl. Qed.
Lemma D_7a454 : decode_any W_7a454 = Some (OpImm ALU_AND 16 20 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a458 : bv 32 := 0x00f038b3.
Lemma F_7a458 : fetch_word AsanUbsan.M.loaded_segments (0x7a4a8 : word) = Some W_7a458.
Proof. vm_refl. Qed.
Lemma D_7a458 : decode_any W_7a458 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a45c : bv 32 := 0x00f827b3.
Lemma F_7a45c : fetch_word AsanUbsan.M.loaded_segments (0x7a4ac : word) = Some W_7a45c.
Proof. vm_refl. Qed.
Lemma D_7a45c : decode_any W_7a45c = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a460 : bv 32 := 0x0017c793.
Lemma F_7a460 : fetch_word AsanUbsan.M.loaded_segments (0x7a4b0 : word) = Some W_7a460.
Proof. vm_refl. Qed.
Lemma D_7a460 : decode_any W_7a460 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a464 : bv 32 := 0x00f8f7b3.
Lemma F_7a464 : fetch_word AsanUbsan.M.loaded_segments (0x7a4b4 : word) = Some W_7a464.
Proof. vm_refl. Qed.
Lemma D_7a464 : decode_any W_7a464 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a468 : bv 32 := 0x00e6fa63.
Lemma F_7a468 : fetch_word AsanUbsan.M.loaded_segments (0x7a4b8 : word) = Some W_7a468.
Proof. vm_refl. Qed.
Lemma D_7a468 : decode_any W_7a468 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a46c : bv 32 := 0x0006c803.
Lemma F_7a46c : fetch_word AsanUbsan.M.loaded_segments (0x7a4bc : word) = Some W_7a46c.
Proof. vm_refl. Qed.
Lemma D_7a46c : decode_any W_7a46c = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a470 : bv 32 := 0x00168693.
Lemma F_7a470 : fetch_word AsanUbsan.M.loaded_segments (0x7a4c0 : word) = Some W_7a470.
Proof. vm_refl. Qed.
Lemma D_7a470 : decode_any W_7a470 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a474 : bv 32 := 0x00f867b3.
Lemma F_7a474 : fetch_word AsanUbsan.M.loaded_segments (0x7a4c4 : word) = Some W_7a474.
Proof. vm_refl. Qed.
Lemma D_7a474 : decode_any W_7a474 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a478 : bv 32 := 0xfee69ae3.
Lemma F_7a478 : fetch_word AsanUbsan.M.loaded_segments (0x7a4c8 : word) = Some W_7a478.
Proof. vm_refl. Qed.
Lemma D_7a478 : decode_any W_7a478 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a47c : bv 32 := 0x0ff7f693.
Lemma F_7a47c : fetch_word AsanUbsan.M.loaded_segments (0x7a4cc : word) = Some W_7a47c.
Proof. vm_refl. Qed.
Lemma D_7a47c : decode_any W_7a47c = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a480 : bv 32 := 0xc60680e3.
Lemma F_7a480 : fetch_word AsanUbsan.M.loaded_segments (0x7a4d0 : word) = Some W_7a480.
Proof. vm_refl. Qed.
Lemma D_7a480 : decode_any W_7a480 = Some (Branch BC_EQ 13 0 7264, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a484 : bv 32 := 0x00050493.
Lemma F_7a484 : fetch_word AsanUbsan.M.loaded_segments (0x7a4d4 : word) = Some W_7a484.
Proof. vm_refl. Qed.
Lemma D_7a484 : decode_any W_7a484 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a488 : bv 32 := 0x00058b13.
Lemma F_7a488 : fetch_word AsanUbsan.M.loaded_segments (0x7a4d8 : word) = Some W_7a488.
Proof. vm_refl. Qed.
Lemma D_7a488 : decode_any W_7a488 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a48c : bv 32 := 0x00060593.
Lemma F_7a48c : fetch_word AsanUbsan.M.loaded_segments (0x7a4dc : word) = Some W_7a48c.
Proof. vm_refl. Qed.
Lemma D_7a48c : decode_any W_7a48c = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a490 : bv 32 := 0x00060913.
Lemma F_7a490 : fetch_word AsanUbsan.M.loaded_segments (0x7a4e0 : word) = Some W_7a490.
Proof. vm_refl. Qed.
Lemma D_7a490 : decode_any W_7a490 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a494 : bv 32 := 0x188020ef.
Lemma F_7a494 : fetch_word AsanUbsan.M.loaded_segments (0x7a4e4 : word) = Some W_7a494.
Proof. vm_refl. Qed.
Lemma D_7a494 : decode_any W_7a494 = Some (Jal 1 8584, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a498 : bv 32 := 0x000b0593.
Lemma F_7a498 : fetch_word AsanUbsan.M.loaded_segments (0x7a4e8 : word) = Some W_7a498.
Proof. vm_refl. Qed.
Lemma D_7a498 : decode_any W_7a498 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a49c : bv 32 := 0x00090613.
Lemma F_7a49c : fetch_word AsanUbsan.M.loaded_segments (0x7a4ec : word) = Some W_7a49c.
Proof. vm_refl. Qed.
Lemma D_7a49c : decode_any W_7a49c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a4a0 : bv 32 := 0x00050993.
Lemma F_7a4a0 : fetch_word AsanUbsan.M.loaded_segments (0x7a4f0 : word) = Some W_7a4a0.
Proof. vm_refl. Qed.
Lemma D_7a4a0 : decode_any W_7a4a0 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a4a4 : bv 32 := 0x00048513.
Lemma F_7a4a4 : fetch_word AsanUbsan.M.loaded_segments (0x7a4f4 : word) = Some W_7a4a4.
Proof. vm_refl. Qed.
Lemma D_7a4a4 : decode_any W_7a4a4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a4a8 : bv 32 := 0xc2098ce3.
Lemma F_7a4a8 : fetch_word AsanUbsan.M.loaded_segments (0x7a4f8 : word) = Some W_7a4a8.
Proof. vm_refl. Qed.
Lemma D_7a4a8 : decode_any W_7a4a8 = Some (Branch BC_EQ 19 0 7224, 4%Z).
Proof. vm_refl. Qed.

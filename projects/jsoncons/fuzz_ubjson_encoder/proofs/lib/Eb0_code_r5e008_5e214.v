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

Definition W_5f238 : bv 32 := 0xfe010113.
Lemma F_5f238 : fetch_word AsanUbsan.M.loaded_segments (0x5f288 : word) = Some W_5f238.
Proof. vm_refl. Qed.
Lemma D_5f238 : decode_any W_5f238 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f23c : bv 32 := 0x00113c23.
Lemma F_5f23c : fetch_word AsanUbsan.M.loaded_segments (0x5f28c : word) = Some W_5f23c.
Proof. vm_refl. Qed.
Lemma D_5f23c : decode_any W_5f23c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f240 : bv 32 := 0x00813823.
Lemma F_5f240 : fetch_word AsanUbsan.M.loaded_segments (0x5f290 : word) = Some W_5f240.
Proof. vm_refl. Qed.
Lemma D_5f240 : decode_any W_5f240 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f244 : bv 32 := 0x00913423.
Lemma F_5f244 : fetch_word AsanUbsan.M.loaded_segments (0x5f294 : word) = Some W_5f244.
Proof. vm_refl. Qed.
Lemma D_5f244 : decode_any W_5f244 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f248 : bv 32 := 0x01213023.
Lemma F_5f248 : fetch_word AsanUbsan.M.loaded_segments (0x5f298 : word) = Some W_5f248.
Proof. vm_refl. Qed.
Lemma D_5f248 : decode_any W_5f248 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f24c : bv 32 := 0x02010413.
Lemma F_5f24c : fetch_word AsanUbsan.M.loaded_segments (0x5f29c : word) = Some W_5f24c.
Proof. vm_refl. Qed.
Lemma D_5f24c : decode_any W_5f24c = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f250 : bv 32 := 0x000df517.
Lemma F_5f250 : fetch_word AsanUbsan.M.loaded_segments (0x5f2a0 : word) = Some W_5f250.
Proof. vm_refl. Qed.
Lemma D_5f250 : decode_any W_5f250 = Some (Auipc 10 223, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f254 : bv 32 := 0x42050513.
Lemma F_5f254 : fetch_word AsanUbsan.M.loaded_segments (0x5f2a4 : word) = Some W_5f254.
Proof. vm_refl. Qed.
Lemma D_5f254 : decode_any W_5f254 = Some (OpImm ALU_ADD 10 10 1056, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f258 : bv 32 := 0x2f4050ef.
Lemma F_5f258 : fetch_word AsanUbsan.M.loaded_segments (0x5f2a8 : word) = Some W_5f258.
Proof. vm_refl. Qed.
Lemma D_5f258 : decode_any W_5f258 = Some (Jal 1 21236, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f25c : bv 32 := 0x00053483.
Lemma F_5f25c : fetch_word AsanUbsan.M.loaded_segments (0x5f2ac : word) = Some W_5f25c.
Proof. vm_refl. Qed.
Lemma D_5f25c : decode_any W_5f25c = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f260 : bv 32 := 0x08048863.
Lemma F_5f260 : fetch_word AsanUbsan.M.loaded_segments (0x5f2b0 : word) = Some W_5f260.
Proof. vm_refl. Qed.
Lemma D_5f260 : decode_any W_5f260 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f264 : bv 32 := 0x0604c503.
Lemma F_5f264 : fetch_word AsanUbsan.M.loaded_segments (0x5f2b4 : word) = Some W_5f264.
Proof. vm_refl. Qed.
Lemma D_5f264 : decode_any W_5f264 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f268 : bv 32 := 0x0584b903.
Lemma F_5f268 : fetch_word AsanUbsan.M.loaded_segments (0x5f2b8 : word) = Some W_5f268.
Proof. vm_refl. Qed.
Lemma D_5f268 : decode_any W_5f268 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f26c : bv 32 := 0x00050863.
Lemma F_5f26c : fetch_word AsanUbsan.M.loaded_segments (0x5f2bc : word) = Some W_5f26c.
Proof. vm_refl. Qed.
Lemma D_5f26c : decode_any W_5f26c = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f270 : bv 32 := 0x00048513.
Lemma F_5f270 : fetch_word AsanUbsan.M.loaded_segments (0x5f2c0 : word) = Some W_5f270.
Proof. vm_refl. Qed.
Lemma D_5f270 : decode_any W_5f270 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f274 : bv 32 := 0x00040593.
Lemma F_5f274 : fetch_word AsanUbsan.M.loaded_segments (0x5f2c4 : word) = Some W_5f274.
Proof. vm_refl. Qed.
Lemma D_5f274 : decode_any W_5f274 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f278 : bv 32 := 0xd28ff0ef.
Lemma F_5f278 : fetch_word AsanUbsan.M.loaded_segments (0x5f2c8 : word) = Some W_5f278.
Proof. vm_refl. Qed.
Lemma D_5f278 : decode_any W_5f278 = Some (Jal 1 2094376, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f27c : bv 32 := 0xff590593.
Lemma F_5f27c : fetch_word AsanUbsan.M.loaded_segments (0x5f2cc : word) = Some W_5f27c.
Proof. vm_refl. Qed.
Lemma D_5f27c : decode_any W_5f27c = Some (OpImm ALU_ADD 11 18 4085, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f280 : bv 32 := 0x00100513.
Lemma F_5f280 : fetch_word AsanUbsan.M.loaded_segments (0x5f2d0 : word) = Some W_5f280.
Proof. vm_refl. Qed.
Lemma D_5f280 : decode_any W_5f280 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f284 : bv 32 := 0x00b51533.
Lemma F_5f284 : fetch_word AsanUbsan.M.loaded_segments (0x5f2d4 : word) = Some W_5f284.
Proof. vm_refl. Qed.
Lemma D_5f284 : decode_any W_5f284 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f288 : bv 32 := 0x0005061b.
Lemma F_5f288 : fetch_word AsanUbsan.M.loaded_segments (0x5f2d8 : word) = Some W_5f288.
Proof. vm_refl. Qed.
Lemma D_5f288 : decode_any W_5f288 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f28c : bv 32 := 0x08c05263.
Lemma F_5f28c : fetch_word AsanUbsan.M.loaded_segments (0x5f2dc : word) = Some W_5f28c.
Proof. vm_refl. Qed.
Lemma D_5f28c : decode_any W_5f28c = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f290 : bv 32 := 0x000016b7.
Lemma F_5f290 : fetch_word AsanUbsan.M.loaded_segments (0x5f2e0 : word) = Some W_5f290.
Proof. vm_refl. Qed.
Lemma D_5f290 : decode_any W_5f290 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f294 : bv 32 := 0xff190613.
Lemma F_5f294 : fetch_word AsanUbsan.M.loaded_segments (0x5f2e4 : word) = Some W_5f294.
Proof. vm_refl. Qed.
Lemma D_5f294 : decode_any W_5f294 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f298 : bv 32 := 0x3e000713.
Lemma F_5f298 : fetch_word AsanUbsan.M.loaded_segments (0x5f2e8 : word) = Some W_5f298.
Proof. vm_refl. Qed.
Lemma D_5f298 : decode_any W_5f298 = Some (OpImm ALU_ADD 14 0 992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f29c : bv 32 := 0xfff00793.
Lemma F_5f29c : fetch_word AsanUbsan.M.loaded_segments (0x5f2ec : word) = Some W_5f29c.
Proof. vm_refl. Qed.
Lemma D_5f29c : decode_any W_5f29c = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2a0 : bv 32 := 0x00c71733.
Lemma F_5f2a0 : fetch_word AsanUbsan.M.loaded_segments (0x5f2f0 : word) = Some W_5f2a0.
Proof. vm_refl. Qed.
Lemma D_5f2a0 : decode_any W_5f2a0 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2a4 : bv 32 := 0x0284b603.
Lemma F_5f2a4 : fetch_word AsanUbsan.M.loaded_segments (0x5f2f4 : word) = Some W_5f2a4.
Proof. vm_refl. Qed.
Lemma D_5f2a4 : decode_any W_5f2a4 = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2a8 : bv 32 := 0x00b797b3.
Lemma F_5f2a8 : fetch_word AsanUbsan.M.loaded_segments (0x5f2f8 : word) = Some W_5f2a8.
Proof. vm_refl. Qed.
Lemma D_5f2a8 : decode_any W_5f2a8 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2ac : bv 32 := 0xfff50813.
Lemma F_5f2ac : fetch_word AsanUbsan.M.loaded_segments (0x5f2fc : word) = Some W_5f2ac.
Proof. vm_refl. Qed.
Lemma D_5f2ac : decode_any W_5f2ac = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2b0 : bv 32 := 0x00d485b3.
Lemma F_5f2b0 : fetch_word AsanUbsan.M.loaded_segments (0x5f300 : word) = Some W_5f2b0.
Proof. vm_refl. Qed.
Lemma D_5f2b0 : decode_any W_5f2b0 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2b4 : bv 32 := 0x00e586b3.
Lemma F_5f2b4 : fetch_word AsanUbsan.M.loaded_segments (0x5f304 : word) = Some W_5f2b4.
Proof. vm_refl. Qed.
Lemma D_5f2b4 : decode_any W_5f2b4 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2b8 : bv 32 := 0xfff7c713.
Lemma F_5f2b8 : fetch_word AsanUbsan.M.loaded_segments (0x5f308 : word) = Some W_5f2b8.
Proof. vm_refl. Qed.
Lemma D_5f2b8 : decode_any W_5f2b8 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2bc : bv 32 := 0x02081813.
Lemma F_5f2bc : fetch_word AsanUbsan.M.loaded_segments (0x5f30c : word) = Some W_5f2bc.
Proof. vm_refl. Qed.
Lemma D_5f2bc : decode_any W_5f2bc = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2c0 : bv 32 := 0x02085793.
Lemma F_5f2c0 : fetch_word AsanUbsan.M.loaded_segments (0x5f310 : word) = Some W_5f2c0.
Proof. vm_refl. Qed.
Lemma D_5f2c0 : decode_any W_5f2c0 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2c4 : bv 32 := 0x00f607b3.
Lemma F_5f2c4 : fetch_word AsanUbsan.M.loaded_segments (0x5f314 : word) = Some W_5f2c4.
Proof. vm_refl. Qed.
Lemma D_5f2c4 : decode_any W_5f2c4 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2c8 : bv 32 := 0x00178813.
Lemma F_5f2c8 : fetch_word AsanUbsan.M.loaded_segments (0x5f318 : word) = Some W_5f2c8.
Proof. vm_refl. Qed.
Lemma D_5f2c8 : decode_any W_5f2c8 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2cc : bv 32 := 0x00e678b3.
Lemma F_5f2cc : fetch_word AsanUbsan.M.loaded_segments (0x5f31c : word) = Some W_5f2cc.
Proof. vm_refl. Qed.
Lemma D_5f2cc : decode_any W_5f2cc = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2d0 : bv 32 := 0x011687b3.
Lemma F_5f2d0 : fetch_word AsanUbsan.M.loaded_segments (0x5f320 : word) = Some W_5f2d0.
Proof. vm_refl. Qed.
Lemma D_5f2d0 : decode_any W_5f2d0 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2d4 : bv 32 := 0x0007c283.
Lemma F_5f2d4 : fetch_word AsanUbsan.M.loaded_segments (0x5f324 : word) = Some W_5f2d4.
Proof. vm_refl. Qed.
Lemma D_5f2d4 : decode_any W_5f2d4 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2d8 : bv 32 := 0x06028663.
Lemma F_5f2d8 : fetch_word AsanUbsan.M.loaded_segments (0x5f328 : word) = Some W_5f2d8.
Proof. vm_refl. Qed.
Lemma D_5f2d8 : decode_any W_5f2d8 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2dc : bv 32 := 0xfff5051b.
Lemma F_5f2dc : fetch_word AsanUbsan.M.loaded_segments (0x5f32c : word) = Some W_5f2dc.
Proof. vm_refl. Qed.
Lemma D_5f2dc : decode_any W_5f2dc = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2e0 : bv 32 := 0x00160613.
Lemma F_5f2e0 : fetch_word AsanUbsan.M.loaded_segments (0x5f330 : word) = Some W_5f2e0.
Proof. vm_refl. Qed.
Lemma D_5f2e0 : decode_any W_5f2e0 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2e4 : bv 32 := 0xfe0514e3.
Lemma F_5f2e4 : fetch_word AsanUbsan.M.loaded_segments (0x5f334 : word) = Some W_5f2e4.
Proof. vm_refl. Qed.
Lemma D_5f2e4 : decode_any W_5f2e4 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2e8 : bv 32 := 0x0304b423.
Lemma F_5f2e8 : fetch_word AsanUbsan.M.loaded_segments (0x5f338 : word) = Some W_5f2e8.
Proof. vm_refl. Qed.
Lemma D_5f2e8 : decode_any W_5f2e8 = Some (Store SZ8 9 16 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2ec : bv 32 := 0x0400006f.
Lemma F_5f2ec : fetch_word AsanUbsan.M.loaded_segments (0x5f33c : word) = Some W_5f2ec.
Proof. vm_refl. Qed.
Lemma D_5f2ec : decode_any W_5f2ec = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2f0 : bv 32 := 0x000de517.
Lemma F_5f2f0 : fetch_word AsanUbsan.M.loaded_segments (0x5f340 : word) = Some W_5f2f0.
Proof. vm_refl. Qed.
Lemma D_5f2f0 : decode_any W_5f2f0 = Some (Auipc 10 222, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2f4 : bv 32 := 0x5e053503.
Lemma F_5f2f4 : fetch_word AsanUbsan.M.loaded_segments (0x5f344 : word) = Some W_5f2f4.
Proof. vm_refl. Qed.
Lemma D_5f2f4 : decode_any W_5f2f4 = Some (Load SZ8 true 10 10 1504, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2f8 : bv 32 := 0x00052503.
Lemma F_5f2f8 : fetch_word AsanUbsan.M.loaded_segments (0x5f348 : word) = Some W_5f2f8.
Proof. vm_refl. Qed.
Lemma D_5f2f8 : decode_any W_5f2f8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f2fc : bv 32 := 0x02050863.
Lemma F_5f2fc : fetch_word AsanUbsan.M.loaded_segments (0x5f34c : word) = Some W_5f2fc.
Proof. vm_refl. Qed.
Lemma D_5f2fc : decode_any W_5f2fc = Some (Branch BC_EQ 10 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f300 : bv 32 := 0x740250ef.
Lemma F_5f300 : fetch_word AsanUbsan.M.loaded_segments (0x5f350 : word) = Some W_5f300.
Proof. vm_refl. Qed.
Lemma D_5f300 : decode_any W_5f300 = Some (Jal 1 153408, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f304 : bv 32 := 0x02050463.
Lemma F_5f304 : fetch_word AsanUbsan.M.loaded_segments (0x5f354 : word) = Some W_5f304.
Proof. vm_refl. Qed.
Lemma D_5f304 : decode_any W_5f304 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f308 : bv 32 := 0x02850583.
Lemma F_5f308 : fetch_word AsanUbsan.M.loaded_segments (0x5f358 : word) = Some W_5f308.
Proof. vm_refl. Qed.
Lemma D_5f308 : decode_any W_5f308 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f30c : bv 32 := 0x10058e63.
Lemma F_5f30c : fetch_word AsanUbsan.M.loaded_segments (0x5f35c : word) = Some W_5f30c.
Proof. vm_refl. Qed.
Lemma D_5f30c : decode_any W_5f30c = Some (Branch BC_EQ 11 0 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f310 : bv 32 := 0x00000513.
Lemma F_5f310 : fetch_word AsanUbsan.M.loaded_segments (0x5f360 : word) = Some W_5f310.
Proof. vm_refl. Qed.
Lemma D_5f310 : decode_any W_5f310 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f314 : bv 32 := 0x01813083.
Lemma F_5f314 : fetch_word AsanUbsan.M.loaded_segments (0x5f364 : word) = Some W_5f314.
Proof. vm_refl. Qed.
Lemma D_5f314 : decode_any W_5f314 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f318 : bv 32 := 0x01013403.
Lemma F_5f318 : fetch_word AsanUbsan.M.loaded_segments (0x5f368 : word) = Some W_5f318.
Proof. vm_refl. Qed.
Lemma D_5f318 : decode_any W_5f318 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f31c : bv 32 := 0x00813483.
Lemma F_5f31c : fetch_word AsanUbsan.M.loaded_segments (0x5f36c : word) = Some W_5f31c.
Proof. vm_refl. Qed.
Lemma D_5f31c : decode_any W_5f31c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f320 : bv 32 := 0x00013903.
Lemma F_5f320 : fetch_word AsanUbsan.M.loaded_segments (0x5f370 : word) = Some W_5f320.
Proof. vm_refl. Qed.
Lemma D_5f320 : decode_any W_5f320 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f324 : bv 32 := 0x02010113.
Lemma F_5f324 : fetch_word AsanUbsan.M.loaded_segments (0x5f374 : word) = Some W_5f324.
Proof. vm_refl. Qed.
Lemma D_5f324 : decode_any W_5f324 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f328 : bv 32 := 0x00008067.
Lemma F_5f328 : fetch_word AsanUbsan.M.loaded_segments (0x5f378 : word) = Some W_5f328.
Proof. vm_refl. Qed.
Lemma D_5f328 : decode_any W_5f328 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f32c : bv 32 := 0x01813083.
Lemma F_5f32c : fetch_word AsanUbsan.M.loaded_segments (0x5f37c : word) = Some W_5f32c.
Proof. vm_refl. Qed.
Lemma D_5f32c : decode_any W_5f32c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f330 : bv 32 := 0x01013403.
Lemma F_5f330 : fetch_word AsanUbsan.M.loaded_segments (0x5f380 : word) = Some W_5f330.
Proof. vm_refl. Qed.
Lemma D_5f330 : decode_any W_5f330 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f334 : bv 32 := 0x00813483.
Lemma F_5f334 : fetch_word AsanUbsan.M.loaded_segments (0x5f384 : word) = Some W_5f334.
Proof. vm_refl. Qed.
Lemma D_5f334 : decode_any W_5f334 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f338 : bv 32 := 0x00013903.
Lemma F_5f338 : fetch_word AsanUbsan.M.loaded_segments (0x5f388 : word) = Some W_5f338.
Proof. vm_refl. Qed.
Lemma D_5f338 : decode_any W_5f338 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f33c : bv 32 := 0x02010113.
Lemma F_5f33c : fetch_word AsanUbsan.M.loaded_segments (0x5f38c : word) = Some W_5f33c.
Proof. vm_refl. Qed.
Lemma D_5f33c : decode_any W_5f33c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f340 : bv 32 := 0x00008067.
Lemma F_5f340 : fetch_word AsanUbsan.M.loaded_segments (0x5f390 : word) = Some W_5f340.
Proof. vm_refl. Qed.
Lemma D_5f340 : decode_any W_5f340 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f344 : bv 32 := 0x00160613.
Lemma F_5f344 : fetch_word AsanUbsan.M.loaded_segments (0x5f394 : word) = Some W_5f344.
Proof. vm_refl. Qed.
Lemma D_5f344 : decode_any W_5f344 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f348 : bv 32 := 0x00100513.
Lemma F_5f348 : fetch_word AsanUbsan.M.loaded_segments (0x5f398 : word) = Some W_5f348.
Proof. vm_refl. Qed.
Lemma D_5f348 : decode_any W_5f348 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f34c : bv 32 := 0xffb90693.
Lemma F_5f34c : fetch_word AsanUbsan.M.loaded_segments (0x5f39c : word) = Some W_5f34c.
Proof. vm_refl. Qed.
Lemma D_5f34c : decode_any W_5f34c = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f350 : bv 32 := 0x02c4b423.
Lemma F_5f350 : fetch_word AsanUbsan.M.loaded_segments (0x5f3a0 : word) = Some W_5f350.
Proof. vm_refl. Qed.
Lemma D_5f350 : decode_any W_5f350 = Some (Store SZ8 9 12 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f354 : bv 32 := 0x00a78023.
Lemma F_5f354 : fetch_word AsanUbsan.M.loaded_segments (0x5f3a4 : word) = Some W_5f354.
Proof. vm_refl. Qed.
Lemma D_5f354 : decode_any W_5f354 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f358 : bv 32 := 0x00d51533.
Lemma F_5f358 : fetch_word AsanUbsan.M.loaded_segments (0x5f3a8 : word) = Some W_5f358.
Proof. vm_refl. Qed.
Lemma D_5f358 : decode_any W_5f358 = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f35c : bv 32 := 0x00500613.
Lemma F_5f35c : fetch_word AsanUbsan.M.loaded_segments (0x5f3ac : word) = Some W_5f35c.
Proof. vm_refl. Qed.
Lemma D_5f35c : decode_any W_5f35c = Some (OpImm ALU_ADD 12 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f360 : bv 32 := 0x00b89893.
Lemma F_5f360 : fetch_word AsanUbsan.M.loaded_segments (0x5f3b0 : word) = Some W_5f360.
Proof. vm_refl. Qed.
Lemma D_5f360 : decode_any W_5f360 = Some (ShiftImm ALU_SLL 17 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f364 : bv 32 := 0x01261633.
Lemma F_5f364 : fetch_word AsanUbsan.M.loaded_segments (0x5f3b4 : word) = Some W_5f364.
Proof. vm_refl. Qed.
Lemma D_5f364 : decode_any W_5f364 = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f368 : bv 32 := 0x00a58533.
Lemma F_5f368 : fetch_word AsanUbsan.M.loaded_segments (0x5f3b8 : word) = Some W_5f368.
Proof. vm_refl. Qed.
Lemma D_5f368 : decode_any W_5f368 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f36c : bv 32 := 0x01160633.
Lemma F_5f36c : fetch_word AsanUbsan.M.loaded_segments (0x5f3bc : word) = Some W_5f36c.
Proof. vm_refl. Qed.
Lemma D_5f36c : decode_any W_5f36c = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f370 : bv 32 := 0x00c504b3.
Lemma F_5f370 : fetch_word AsanUbsan.M.loaded_segments (0x5f3c0 : word) = Some W_5f370.
Proof. vm_refl. Qed.
Lemma D_5f370 : decode_any W_5f370 = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f374 : bv 32 := 0x0084bc23.
Lemma F_5f374 : fetch_word AsanUbsan.M.loaded_segments (0x5f3c4 : word) = Some W_5f374.
Proof. vm_refl. Qed.
Lemma D_5f374 : decode_any W_5f374 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f378 : bv 32 := 0x7ef4bc23.
Lemma F_5f378 : fetch_word AsanUbsan.M.loaded_segments (0x5f3c8 : word) = Some W_5f378.
Proof. vm_refl. Qed.
Lemma D_5f378 : decode_any W_5f378 = Some (Store SZ8 9 15 2040, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f37c : bv 32 := 0x00048513.
Lemma F_5f37c : fetch_word AsanUbsan.M.loaded_segments (0x5f3cc : word) = Some W_5f37c.
Proof. vm_refl. Qed.
Lemma D_5f37c : decode_any W_5f37c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f380 : bv 32 := 0x178000ef.
Lemma F_5f380 : fetch_word AsanUbsan.M.loaded_segments (0x5f3d0 : word) = Some W_5f380.
Proof. vm_refl. Qed.
Lemma D_5f380 : decode_any W_5f380 = Some (Jal 1 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f384 : bv 32 := 0x00050593.
Lemma F_5f384 : fetch_word AsanUbsan.M.loaded_segments (0x5f3d4 : word) = Some W_5f384.
Proof. vm_refl. Qed.
Lemma D_5f384 : decode_any W_5f384 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f388 : bv 32 := 0x00048513.
Lemma F_5f388 : fetch_word AsanUbsan.M.loaded_segments (0x5f3d8 : word) = Some W_5f388.
Proof. vm_refl. Qed.
Lemma D_5f388 : decode_any W_5f388 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f38c : bv 32 := 0x00000613.
Lemma F_5f38c : fetch_word AsanUbsan.M.loaded_segments (0x5f3dc : word) = Some W_5f38c.
Proof. vm_refl. Qed.
Lemma D_5f38c : decode_any W_5f38c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f390 : bv 32 := 0x0005b023.
Lemma F_5f390 : fetch_word AsanUbsan.M.loaded_segments (0x5f3e0 : word) = Some W_5f390.
Proof. vm_refl. Qed.
Lemma D_5f390 : decode_any W_5f390 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f394 : bv 32 := 0x0005b423.
Lemma F_5f394 : fetch_word AsanUbsan.M.loaded_segments (0x5f3e4 : word) = Some W_5f394.
Proof. vm_refl. Qed.
Lemma D_5f394 : decode_any W_5f394 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f398 : bv 32 := 0x0005b823.
Lemma F_5f398 : fetch_word AsanUbsan.M.loaded_segments (0x5f3e8 : word) = Some W_5f398.
Proof. vm_refl. Qed.
Lemma D_5f398 : decode_any W_5f398 = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f39c : bv 32 := 0x0005bc23.
Lemma F_5f39c : fetch_word AsanUbsan.M.loaded_segments (0x5f3ec : word) = Some W_5f39c.
Proof. vm_refl. Qed.
Lemma D_5f39c : decode_any W_5f39c = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3a0 : bv 32 := 0x0205b023.
Lemma F_5f3a0 : fetch_word AsanUbsan.M.loaded_segments (0x5f3f0 : word) = Some W_5f3a0.
Proof. vm_refl. Qed.
Lemma D_5f3a0 : decode_any W_5f3a0 = Some (Store SZ8 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3a4 : bv 32 := 0x0205b423.
Lemma F_5f3a4 : fetch_word AsanUbsan.M.loaded_segments (0x5f3f4 : word) = Some W_5f3a4.
Proof. vm_refl. Qed.
Lemma D_5f3a4 : decode_any W_5f3a4 = Some (Store SZ8 11 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3a8 : bv 32 := 0x0205b823.
Lemma F_5f3a8 : fetch_word AsanUbsan.M.loaded_segments (0x5f3f8 : word) = Some W_5f3a8.
Proof. vm_refl. Qed.
Lemma D_5f3a8 : decode_any W_5f3a8 = Some (Store SZ8 11 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3ac : bv 32 := 0x0205bc23.
Lemma F_5f3ac : fetch_word AsanUbsan.M.loaded_segments (0x5f3fc : word) = Some W_5f3ac.
Proof. vm_refl. Qed.
Lemma D_5f3ac : decode_any W_5f3ac = Some (Store SZ8 11 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3b0 : bv 32 := 0x0405b023.
Lemma F_5f3b0 : fetch_word AsanUbsan.M.loaded_segments (0x5f400 : word) = Some W_5f3b0.
Proof. vm_refl. Qed.
Lemma D_5f3b0 : decode_any W_5f3b0 = Some (Store SZ8 11 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3b4 : bv 32 := 0x0405b423.
Lemma F_5f3b4 : fetch_word AsanUbsan.M.loaded_segments (0x5f404 : word) = Some W_5f3b4.
Proof. vm_refl. Qed.
Lemma D_5f3b4 : decode_any W_5f3b4 = Some (Store SZ8 11 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3b8 : bv 32 := 0x0405b823.
Lemma F_5f3b8 : fetch_word AsanUbsan.M.loaded_segments (0x5f408 : word) = Some W_5f3b8.
Proof. vm_refl. Qed.
Lemma D_5f3b8 : decode_any W_5f3b8 = Some (Store SZ8 11 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3bc : bv 32 := 0x0405bc23.
Lemma F_5f3bc : fetch_word AsanUbsan.M.loaded_segments (0x5f40c : word) = Some W_5f3bc.
Proof. vm_refl. Qed.
Lemma D_5f3bc : decode_any W_5f3bc = Some (Store SZ8 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3c0 : bv 32 := 0x0605b023.
Lemma F_5f3c0 : fetch_word AsanUbsan.M.loaded_segments (0x5f410 : word) = Some W_5f3c0.
Proof. vm_refl. Qed.
Lemma D_5f3c0 : decode_any W_5f3c0 = Some (Store SZ8 11 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3c4 : bv 32 := 0x0605b423.
Lemma F_5f3c4 : fetch_word AsanUbsan.M.loaded_segments (0x5f414 : word) = Some W_5f3c4.
Proof. vm_refl. Qed.
Lemma D_5f3c4 : decode_any W_5f3c4 = Some (Store SZ8 11 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3c8 : bv 32 := 0x0605b823.
Lemma F_5f3c8 : fetch_word AsanUbsan.M.loaded_segments (0x5f418 : word) = Some W_5f3c8.
Proof. vm_refl. Qed.
Lemma D_5f3c8 : decode_any W_5f3c8 = Some (Store SZ8 11 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3cc : bv 32 := 0x0605bc23.
Lemma F_5f3cc : fetch_word AsanUbsan.M.loaded_segments (0x5f41c : word) = Some W_5f3cc.
Proof. vm_refl. Qed.
Lemma D_5f3cc : decode_any W_5f3cc = Some (Store SZ8 11 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3d0 : bv 32 := 0x0805b023.
Lemma F_5f3d0 : fetch_word AsanUbsan.M.loaded_segments (0x5f420 : word) = Some W_5f3d0.
Proof. vm_refl. Qed.
Lemma D_5f3d0 : decode_any W_5f3d0 = Some (Store SZ8 11 0 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3d4 : bv 32 := 0x0805b423.
Lemma F_5f3d4 : fetch_word AsanUbsan.M.loaded_segments (0x5f424 : word) = Some W_5f3d4.
Proof. vm_refl. Qed.
Lemma D_5f3d4 : decode_any W_5f3d4 = Some (Store SZ8 11 0 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3d8 : bv 32 := 0x0805b823.
Lemma F_5f3d8 : fetch_word AsanUbsan.M.loaded_segments (0x5f428 : word) = Some W_5f3d8.
Proof. vm_refl. Qed.
Lemma D_5f3d8 : decode_any W_5f3d8 = Some (Store SZ8 11 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3dc : bv 32 := 0x0805bc23.
Lemma F_5f3dc : fetch_word AsanUbsan.M.loaded_segments (0x5f42c : word) = Some W_5f3dc.
Proof. vm_refl. Qed.
Lemma D_5f3dc : decode_any W_5f3dc = Some (Store SZ8 11 0 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3e0 : bv 32 := 0x0a05b023.
Lemma F_5f3e0 : fetch_word AsanUbsan.M.loaded_segments (0x5f430 : word) = Some W_5f3e0.
Proof. vm_refl. Qed.
Lemma D_5f3e0 : decode_any W_5f3e0 = Some (Store SZ8 11 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3e4 : bv 32 := 0x0a05b423.
Lemma F_5f3e4 : fetch_word AsanUbsan.M.loaded_segments (0x5f434 : word) = Some W_5f3e4.
Proof. vm_refl. Qed.
Lemma D_5f3e4 : decode_any W_5f3e4 = Some (Store SZ8 11 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3e8 : bv 32 := 0x0a05b823.
Lemma F_5f3e8 : fetch_word AsanUbsan.M.loaded_segments (0x5f438 : word) = Some W_5f3e8.
Proof. vm_refl. Qed.
Lemma D_5f3e8 : decode_any W_5f3e8 = Some (Store SZ8 11 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3ec : bv 32 := 0x0a05bc23.
Lemma F_5f3ec : fetch_word AsanUbsan.M.loaded_segments (0x5f43c : word) = Some W_5f3ec.
Proof. vm_refl. Qed.
Lemma D_5f3ec : decode_any W_5f3ec = Some (Store SZ8 11 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3f0 : bv 32 := 0x0c05b023.
Lemma F_5f3f0 : fetch_word AsanUbsan.M.loaded_segments (0x5f440 : word) = Some W_5f3f0.
Proof. vm_refl. Qed.
Lemma D_5f3f0 : decode_any W_5f3f0 = Some (Store SZ8 11 0 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3f4 : bv 32 := 0x0c05b423.
Lemma F_5f3f4 : fetch_word AsanUbsan.M.loaded_segments (0x5f444 : word) = Some W_5f3f4.
Proof. vm_refl. Qed.
Lemma D_5f3f4 : decode_any W_5f3f4 = Some (Store SZ8 11 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3f8 : bv 32 := 0x0c05b823.
Lemma F_5f3f8 : fetch_word AsanUbsan.M.loaded_segments (0x5f448 : word) = Some W_5f3f8.
Proof. vm_refl. Qed.
Lemma D_5f3f8 : decode_any W_5f3f8 = Some (Store SZ8 11 0 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f3fc : bv 32 := 0x0c05bc23.
Lemma F_5f3fc : fetch_word AsanUbsan.M.loaded_segments (0x5f44c : word) = Some W_5f3fc.
Proof. vm_refl. Qed.
Lemma D_5f3fc : decode_any W_5f3fc = Some (Store SZ8 11 0 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f400 : bv 32 := 0x0e05b023.
Lemma F_5f400 : fetch_word AsanUbsan.M.loaded_segments (0x5f450 : word) = Some W_5f400.
Proof. vm_refl. Qed.
Lemma D_5f400 : decode_any W_5f400 = Some (Store SZ8 11 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f404 : bv 32 := 0x0e05b423.
Lemma F_5f404 : fetch_word AsanUbsan.M.loaded_segments (0x5f454 : word) = Some W_5f404.
Proof. vm_refl. Qed.
Lemma D_5f404 : decode_any W_5f404 = Some (Store SZ8 11 0 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f408 : bv 32 := 0x0e05b823.
Lemma F_5f408 : fetch_word AsanUbsan.M.loaded_segments (0x5f458 : word) = Some W_5f408.
Proof. vm_refl. Qed.
Lemma D_5f408 : decode_any W_5f408 = Some (Store SZ8 11 0 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f40c : bv 32 := 0x0e05bc23.
Lemma F_5f40c : fetch_word AsanUbsan.M.loaded_segments (0x5f45c : word) = Some W_5f40c.
Proof. vm_refl. Qed.
Lemma D_5f40c : decode_any W_5f40c = Some (Store SZ8 11 0 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f410 : bv 32 := 0x01813083.
Lemma F_5f410 : fetch_word AsanUbsan.M.loaded_segments (0x5f460 : word) = Some W_5f410.
Proof. vm_refl. Qed.
Lemma D_5f410 : decode_any W_5f410 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f414 : bv 32 := 0x01013403.
Lemma F_5f414 : fetch_word AsanUbsan.M.loaded_segments (0x5f464 : word) = Some W_5f414.
Proof. vm_refl. Qed.
Lemma D_5f414 : decode_any W_5f414 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f418 : bv 32 := 0x00813483.
Lemma F_5f418 : fetch_word AsanUbsan.M.loaded_segments (0x5f468 : word) = Some W_5f418.
Proof. vm_refl. Qed.
Lemma D_5f418 : decode_any W_5f418 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f41c : bv 32 := 0x00013903.
Lemma F_5f41c : fetch_word AsanUbsan.M.loaded_segments (0x5f46c : word) = Some W_5f41c.
Proof. vm_refl. Qed.
Lemma D_5f41c : decode_any W_5f41c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f420 : bv 32 := 0x02010113.
Lemma F_5f420 : fetch_word AsanUbsan.M.loaded_segments (0x5f470 : word) = Some W_5f420.
Proof. vm_refl. Qed.
Lemma D_5f420 : decode_any W_5f420 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f424 : bv 32 := 0x00008067.
Lemma F_5f424 : fetch_word AsanUbsan.M.loaded_segments (0x5f474 : word) = Some W_5f424.
Proof. vm_refl. Qed.
Lemma D_5f424 : decode_any W_5f424 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f428 : bv 32 := 0x04853483.
Lemma F_5f428 : fetch_word AsanUbsan.M.loaded_segments (0x5f478 : word) = Some W_5f428.
Proof. vm_refl. Qed.
Lemma D_5f428 : decode_any W_5f428 = Some (Load SZ8 true 9 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f42c : bv 32 := 0x00100593.
Lemma F_5f42c : fetch_word AsanUbsan.M.loaded_segments (0x5f47c : word) = Some W_5f42c.
Proof. vm_refl. Qed.
Lemma D_5f42c : decode_any W_5f42c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f430 : bv 32 := 0x0095e663.
Lemma F_5f430 : fetch_word AsanUbsan.M.loaded_segments (0x5f480 : word) = Some W_5f430.
Proof. vm_refl. Qed.
Lemma D_5f430 : decode_any W_5f430 = Some (Branch BC_LTU 11 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f434 : bv 32 := 0x081250ef.
Lemma F_5f434 : fetch_word AsanUbsan.M.loaded_segments (0x5f484 : word) = Some W_5f434.
Proof. vm_refl. Qed.
Lemma D_5f434 : decode_any W_5f434 = Some (Jal 1 153728, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f438 : bv 32 := 0x00050493.
Lemma F_5f438 : fetch_word AsanUbsan.M.loaded_segments (0x5f488 : word) = Some W_5f438.
Proof. vm_refl. Qed.
Lemma D_5f438 : decode_any W_5f438 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f43c : bv 32 := 0xe20494e3.
Lemma F_5f43c : fetch_word AsanUbsan.M.loaded_segments (0x5f48c : word) = Some W_5f43c.
Proof. vm_refl. Qed.
Lemma D_5f43c : decode_any W_5f43c = Some (Branch BC_NE 9 0 7720, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f440 : bv 32 := 0xed1ff06f.
Lemma F_5f440 : fetch_word AsanUbsan.M.loaded_segments (0x5f490 : word) = Some W_5f440.
Proof. vm_refl. Qed.
Lemma D_5f440 : decode_any W_5f440 = Some (Jal 0 2096848, 4%Z).
Proof. vm_refl. Qed.

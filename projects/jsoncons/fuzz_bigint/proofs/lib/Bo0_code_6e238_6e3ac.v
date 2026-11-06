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

Definition W_6e238 : bv 32 := 0xfe010113.
Lemma F_6e238 : fetch_word AsanUbsan.M.loaded_segments (0x6e238 : word) = Some W_6e238.
Proof. vm_refl. Qed.
Lemma D_6e238 : decode_any W_6e238 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e23c : bv 32 := 0x00113c23.
Lemma F_6e23c : fetch_word AsanUbsan.M.loaded_segments (0x6e23c : word) = Some W_6e23c.
Proof. vm_refl. Qed.
Lemma D_6e23c : decode_any W_6e23c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e240 : bv 32 := 0x00813823.
Lemma F_6e240 : fetch_word AsanUbsan.M.loaded_segments (0x6e240 : word) = Some W_6e240.
Proof. vm_refl. Qed.
Lemma D_6e240 : decode_any W_6e240 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e244 : bv 32 := 0x00913423.
Lemma F_6e244 : fetch_word AsanUbsan.M.loaded_segments (0x6e244 : word) = Some W_6e244.
Proof. vm_refl. Qed.
Lemma D_6e244 : decode_any W_6e244 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e248 : bv 32 := 0x01213023.
Lemma F_6e248 : fetch_word AsanUbsan.M.loaded_segments (0x6e248 : word) = Some W_6e248.
Proof. vm_refl. Qed.
Lemma D_6e248 : decode_any W_6e248 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e24c : bv 32 := 0x00058413.
Lemma F_6e24c : fetch_word AsanUbsan.M.loaded_segments (0x6e24c : word) = Some W_6e24c.
Proof. vm_refl. Qed.
Lemma D_6e24c : decode_any W_6e24c = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e250 : bv 32 := 0x00050493.
Lemma F_6e250 : fetch_word AsanUbsan.M.loaded_segments (0x6e250 : word) = Some W_6e250.
Proof. vm_refl. Qed.
Lemma D_6e250 : decode_any W_6e250 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e254 : bv 32 := 0x09c000ef.
Lemma F_6e254 : fetch_word AsanUbsan.M.loaded_segments (0x6e254 : word) = Some W_6e254.
Proof. vm_refl. Qed.
Lemma D_6e254 : decode_any W_6e254 = Some (Jal 1 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e258 : bv 32 := 0x00102517.
Lemma F_6e258 : fetch_word AsanUbsan.M.loaded_segments (0x6e258 : word) = Some W_6e258.
Proof. vm_refl. Qed.
Lemma D_6e258 : decode_any W_6e258 = Some (Auipc 10 258, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e25c : bv 32 := 0xfa850913.
Lemma F_6e25c : fetch_word AsanUbsan.M.loaded_segments (0x6e25c : word) = Some W_6e25c.
Proof. vm_refl. Qed.
Lemma D_6e25c : decode_any W_6e25c = Some (OpImm ALU_ADD 18 10 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e260 : bv 32 := 0x00093603.
Lemma F_6e260 : fetch_word AsanUbsan.M.loaded_segments (0x6e260 : word) = Some W_6e260.
Proof. vm_refl. Qed.
Lemma D_6e260 : decode_any W_6e260 = Some (Load SZ8 true 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e264 : bv 32 := 0x06060a63.
Lemma F_6e264 : fetch_word AsanUbsan.M.loaded_segments (0x6e264 : word) = Some W_6e264.
Proof. vm_refl. Qed.
Lemma D_6e264 : decode_any W_6e264 = Some (Branch BC_EQ 12 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e268 : bv 32 := 0x00048513.
Lemma F_6e268 : fetch_word AsanUbsan.M.loaded_segments (0x6e268 : word) = Some W_6e268.
Proof. vm_refl. Qed.
Lemma D_6e268 : decode_any W_6e268 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e26c : bv 32 := 0x00040593.
Lemma F_6e26c : fetch_word AsanUbsan.M.loaded_segments (0x6e26c : word) = Some W_6e26c.
Proof. vm_refl. Qed.
Lemma D_6e26c : decode_any W_6e26c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e270 : bv 32 := 0x000600e7.
Lemma F_6e270 : fetch_word AsanUbsan.M.loaded_segments (0x6e270 : word) = Some W_6e270.
Proof. vm_refl. Qed.
Lemma D_6e270 : decode_any W_6e270 = Some (Jalr 1 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e274 : bv 32 := 0x01093603.
Lemma F_6e274 : fetch_word AsanUbsan.M.loaded_segments (0x6e274 : word) = Some W_6e274.
Proof. vm_refl. Qed.
Lemma D_6e274 : decode_any W_6e274 = Some (Load SZ8 true 12 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e278 : bv 32 := 0x06060063.
Lemma F_6e278 : fetch_word AsanUbsan.M.loaded_segments (0x6e278 : word) = Some W_6e278.
Proof. vm_refl. Qed.
Lemma D_6e278 : decode_any W_6e278 = Some (Branch BC_EQ 12 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e27c : bv 32 := 0x00048513.
Lemma F_6e27c : fetch_word AsanUbsan.M.loaded_segments (0x6e27c : word) = Some W_6e27c.
Proof. vm_refl. Qed.
Lemma D_6e27c : decode_any W_6e27c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e280 : bv 32 := 0x00040593.
Lemma F_6e280 : fetch_word AsanUbsan.M.loaded_segments (0x6e280 : word) = Some W_6e280.
Proof. vm_refl. Qed.
Lemma D_6e280 : decode_any W_6e280 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e284 : bv 32 := 0x000600e7.
Lemma F_6e284 : fetch_word AsanUbsan.M.loaded_segments (0x6e284 : word) = Some W_6e284.
Proof. vm_refl. Qed.
Lemma D_6e284 : decode_any W_6e284 = Some (Jalr 1 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e288 : bv 32 := 0x02093603.
Lemma F_6e288 : fetch_word AsanUbsan.M.loaded_segments (0x6e288 : word) = Some W_6e288.
Proof. vm_refl. Qed.
Lemma D_6e288 : decode_any W_6e288 = Some (Load SZ8 true 12 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e28c : bv 32 := 0x04060663.
Lemma F_6e28c : fetch_word AsanUbsan.M.loaded_segments (0x6e28c : word) = Some W_6e28c.
Proof. vm_refl. Qed.
Lemma D_6e28c : decode_any W_6e28c = Some (Branch BC_EQ 12 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e290 : bv 32 := 0x00048513.
Lemma F_6e290 : fetch_word AsanUbsan.M.loaded_segments (0x6e290 : word) = Some W_6e290.
Proof. vm_refl. Qed.
Lemma D_6e290 : decode_any W_6e290 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e294 : bv 32 := 0x00040593.
Lemma F_6e294 : fetch_word AsanUbsan.M.loaded_segments (0x6e294 : word) = Some W_6e294.
Proof. vm_refl. Qed.
Lemma D_6e294 : decode_any W_6e294 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e298 : bv 32 := 0x000600e7.
Lemma F_6e298 : fetch_word AsanUbsan.M.loaded_segments (0x6e298 : word) = Some W_6e298.
Proof. vm_refl. Qed.
Lemma D_6e298 : decode_any W_6e298 = Some (Jalr 1 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e29c : bv 32 := 0x03093603.
Lemma F_6e29c : fetch_word AsanUbsan.M.loaded_segments (0x6e29c : word) = Some W_6e29c.
Proof. vm_refl. Qed.
Lemma D_6e29c : decode_any W_6e29c = Some (Load SZ8 true 12 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2a0 : bv 32 := 0x02060c63.
Lemma F_6e2a0 : fetch_word AsanUbsan.M.loaded_segments (0x6e2a0 : word) = Some W_6e2a0.
Proof. vm_refl. Qed.
Lemma D_6e2a0 : decode_any W_6e2a0 = Some (Branch BC_EQ 12 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2a4 : bv 32 := 0x00048513.
Lemma F_6e2a4 : fetch_word AsanUbsan.M.loaded_segments (0x6e2a4 : word) = Some W_6e2a4.
Proof. vm_refl. Qed.
Lemma D_6e2a4 : decode_any W_6e2a4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2a8 : bv 32 := 0x00040593.
Lemma F_6e2a8 : fetch_word AsanUbsan.M.loaded_segments (0x6e2a8 : word) = Some W_6e2a8.
Proof. vm_refl. Qed.
Lemma D_6e2a8 : decode_any W_6e2a8 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2ac : bv 32 := 0x000600e7.
Lemma F_6e2ac : fetch_word AsanUbsan.M.loaded_segments (0x6e2ac : word) = Some W_6e2ac.
Proof. vm_refl. Qed.
Lemma D_6e2ac : decode_any W_6e2ac = Some (Jalr 1 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2b0 : bv 32 := 0x04093303.
Lemma F_6e2b0 : fetch_word AsanUbsan.M.loaded_segments (0x6e2b0 : word) = Some W_6e2b0.
Proof. vm_refl. Qed.
Lemma D_6e2b0 : decode_any W_6e2b0 = Some (Load SZ8 true 6 18 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2b4 : bv 32 := 0x02030263.
Lemma F_6e2b4 : fetch_word AsanUbsan.M.loaded_segments (0x6e2b4 : word) = Some W_6e2b4.
Proof. vm_refl. Qed.
Lemma D_6e2b4 : decode_any W_6e2b4 = Some (Branch BC_EQ 6 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2b8 : bv 32 := 0x00048513.
Lemma F_6e2b8 : fetch_word AsanUbsan.M.loaded_segments (0x6e2b8 : word) = Some W_6e2b8.
Proof. vm_refl. Qed.
Lemma D_6e2b8 : decode_any W_6e2b8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2bc : bv 32 := 0x00040593.
Lemma F_6e2bc : fetch_word AsanUbsan.M.loaded_segments (0x6e2bc : word) = Some W_6e2bc.
Proof. vm_refl. Qed.
Lemma D_6e2bc : decode_any W_6e2bc = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2c0 : bv 32 := 0x01813083.
Lemma F_6e2c0 : fetch_word AsanUbsan.M.loaded_segments (0x6e2c0 : word) = Some W_6e2c0.
Proof. vm_refl. Qed.
Lemma D_6e2c0 : decode_any W_6e2c0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2c4 : bv 32 := 0x01013403.
Lemma F_6e2c4 : fetch_word AsanUbsan.M.loaded_segments (0x6e2c4 : word) = Some W_6e2c4.
Proof. vm_refl. Qed.
Lemma D_6e2c4 : decode_any W_6e2c4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2c8 : bv 32 := 0x00813483.
Lemma F_6e2c8 : fetch_word AsanUbsan.M.loaded_segments (0x6e2c8 : word) = Some W_6e2c8.
Proof. vm_refl. Qed.
Lemma D_6e2c8 : decode_any W_6e2c8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2cc : bv 32 := 0x00013903.
Lemma F_6e2cc : fetch_word AsanUbsan.M.loaded_segments (0x6e2cc : word) = Some W_6e2cc.
Proof. vm_refl. Qed.
Lemma D_6e2cc : decode_any W_6e2cc = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2d0 : bv 32 := 0x02010113.
Lemma F_6e2d0 : fetch_word AsanUbsan.M.loaded_segments (0x6e2d0 : word) = Some W_6e2d0.
Proof. vm_refl. Qed.
Lemma D_6e2d0 : decode_any W_6e2d0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2d4 : bv 32 := 0x00030067.
Lemma F_6e2d4 : fetch_word AsanUbsan.M.loaded_segments (0x6e2d4 : word) = Some W_6e2d4.
Proof. vm_refl. Qed.
Lemma D_6e2d4 : decode_any W_6e2d4 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2d8 : bv 32 := 0x01813083.
Lemma F_6e2d8 : fetch_word AsanUbsan.M.loaded_segments (0x6e2d8 : word) = Some W_6e2d8.
Proof. vm_refl. Qed.
Lemma D_6e2d8 : decode_any W_6e2d8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2dc : bv 32 := 0x01013403.
Lemma F_6e2dc : fetch_word AsanUbsan.M.loaded_segments (0x6e2dc : word) = Some W_6e2dc.
Proof. vm_refl. Qed.
Lemma D_6e2dc : decode_any W_6e2dc = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2e0 : bv 32 := 0x00813483.
Lemma F_6e2e0 : fetch_word AsanUbsan.M.loaded_segments (0x6e2e0 : word) = Some W_6e2e0.
Proof. vm_refl. Qed.
Lemma D_6e2e0 : decode_any W_6e2e0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2e4 : bv 32 := 0x00013903.
Lemma F_6e2e4 : fetch_word AsanUbsan.M.loaded_segments (0x6e2e4 : word) = Some W_6e2e4.
Proof. vm_refl. Qed.
Lemma D_6e2e4 : decode_any W_6e2e4 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2e8 : bv 32 := 0x02010113.
Lemma F_6e2e8 : fetch_word AsanUbsan.M.loaded_segments (0x6e2e8 : word) = Some W_6e2e8.
Proof. vm_refl. Qed.
Lemma D_6e2e8 : decode_any W_6e2e8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2ec : bv 32 := 0x00008067.
Lemma F_6e2ec : fetch_word AsanUbsan.M.loaded_segments (0x6e2ec : word) = Some W_6e2ec.
Proof. vm_refl. Qed.
Lemma D_6e2ec : decode_any W_6e2ec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2f0 : bv 32 := 0x00008067.
Lemma F_6e2f0 : fetch_word AsanUbsan.M.loaded_segments (0x6e2f0 : word) = Some W_6e2f0.
Proof. vm_refl. Qed.
Lemma D_6e2f0 : decode_any W_6e2f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2f4 : bv 32 := 0xfe010113.
Lemma F_6e2f4 : fetch_word AsanUbsan.M.loaded_segments (0x6e2f4 : word) = Some W_6e2f4.
Proof. vm_refl. Qed.
Lemma D_6e2f4 : decode_any W_6e2f4 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2f8 : bv 32 := 0x00113c23.
Lemma F_6e2f8 : fetch_word AsanUbsan.M.loaded_segments (0x6e2f8 : word) = Some W_6e2f8.
Proof. vm_refl. Qed.
Lemma D_6e2f8 : decode_any W_6e2f8 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e2fc : bv 32 := 0x00813823.
Lemma F_6e2fc : fetch_word AsanUbsan.M.loaded_segments (0x6e2fc : word) = Some W_6e2fc.
Proof. vm_refl. Qed.
Lemma D_6e2fc : decode_any W_6e2fc = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e300 : bv 32 := 0x00913423.
Lemma F_6e300 : fetch_word AsanUbsan.M.loaded_segments (0x6e300 : word) = Some W_6e300.
Proof. vm_refl. Qed.
Lemma D_6e300 : decode_any W_6e300 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e304 : bv 32 := 0x00050413.
Lemma F_6e304 : fetch_word AsanUbsan.M.loaded_segments (0x6e304 : word) = Some W_6e304.
Proof. vm_refl. Qed.
Lemma D_6e304 : decode_any W_6e304 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e308 : bv 32 := 0x098000ef.
Lemma F_6e308 : fetch_word AsanUbsan.M.loaded_segments (0x6e308 : word) = Some W_6e308.
Proof. vm_refl. Qed.
Lemma D_6e308 : decode_any W_6e308 = Some (Jal 1 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e30c : bv 32 := 0x00050e63.
Lemma F_6e30c : fetch_word AsanUbsan.M.loaded_segments (0x6e30c : word) = Some W_6e30c.
Proof. vm_refl. Qed.
Lemma D_6e30c : decode_any W_6e30c = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e310 : bv 32 := 0x00100513.
Lemma F_6e310 : fetch_word AsanUbsan.M.loaded_segments (0x6e310 : word) = Some W_6e310.
Proof. vm_refl. Qed.
Lemma D_6e310 : decode_any W_6e310 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e314 : bv 32 := 0x01813083.
Lemma F_6e314 : fetch_word AsanUbsan.M.loaded_segments (0x6e314 : word) = Some W_6e314.
Proof. vm_refl. Qed.
Lemma D_6e314 : decode_any W_6e314 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e318 : bv 32 := 0x01013403.
Lemma F_6e318 : fetch_word AsanUbsan.M.loaded_segments (0x6e318 : word) = Some W_6e318.
Proof. vm_refl. Qed.
Lemma D_6e318 : decode_any W_6e318 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e31c : bv 32 := 0x00813483.
Lemma F_6e31c : fetch_word AsanUbsan.M.loaded_segments (0x6e31c : word) = Some W_6e31c.
Proof. vm_refl. Qed.
Lemma D_6e31c : decode_any W_6e31c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e320 : bv 32 := 0x02010113.
Lemma F_6e320 : fetch_word AsanUbsan.M.loaded_segments (0x6e320 : word) = Some W_6e320.
Proof. vm_refl. Qed.
Lemma D_6e320 : decode_any W_6e320 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e324 : bv 32 := 0x00008067.
Lemma F_6e324 : fetch_word AsanUbsan.M.loaded_segments (0x6e324 : word) = Some W_6e324.
Proof. vm_refl. Qed.
Lemma D_6e324 : decode_any W_6e324 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e328 : bv 32 := 0x00040513.
Lemma F_6e328 : fetch_word AsanUbsan.M.loaded_segments (0x6e328 : word) = Some W_6e328.
Proof. vm_refl. Qed.
Lemma D_6e328 : decode_any W_6e328 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e32c : bv 32 := 0x07c000ef.
Lemma F_6e32c : fetch_word AsanUbsan.M.loaded_segments (0x6e32c : word) = Some W_6e32c.
Proof. vm_refl. Qed.
Lemma D_6e32c : decode_any W_6e32c = Some (Jal 1 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e330 : bv 32 := 0x00102517.
Lemma F_6e330 : fetch_word AsanUbsan.M.loaded_segments (0x6e330 : word) = Some W_6e330.
Proof. vm_refl. Qed.
Lemma D_6e330 : decode_any W_6e330 = Some (Auipc 10 258, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e334 : bv 32 := 0xed050493.
Lemma F_6e334 : fetch_word AsanUbsan.M.loaded_segments (0x6e334 : word) = Some W_6e334.
Proof. vm_refl. Qed.
Lemma D_6e334 : decode_any W_6e334 = Some (OpImm ALU_ADD 9 10 3792, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e338 : bv 32 := 0x0084b583.
Lemma F_6e338 : fetch_word AsanUbsan.M.loaded_segments (0x6e338 : word) = Some W_6e338.
Proof. vm_refl. Qed.
Lemma D_6e338 : decode_any W_6e338 = Some (Load SZ8 true 11 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e33c : bv 32 := 0x04058663.
Lemma F_6e33c : fetch_word AsanUbsan.M.loaded_segments (0x6e33c : word) = Some W_6e33c.
Proof. vm_refl. Qed.
Lemma D_6e33c : decode_any W_6e33c = Some (Branch BC_EQ 11 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e340 : bv 32 := 0x00040513.
Lemma F_6e340 : fetch_word AsanUbsan.M.loaded_segments (0x6e340 : word) = Some W_6e340.
Proof. vm_refl. Qed.
Lemma D_6e340 : decode_any W_6e340 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e344 : bv 32 := 0x000580e7.
Lemma F_6e344 : fetch_word AsanUbsan.M.loaded_segments (0x6e344 : word) = Some W_6e344.
Proof. vm_refl. Qed.
Lemma D_6e344 : decode_any W_6e344 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e348 : bv 32 := 0x0184b583.
Lemma F_6e348 : fetch_word AsanUbsan.M.loaded_segments (0x6e348 : word) = Some W_6e348.
Proof. vm_refl. Qed.
Lemma D_6e348 : decode_any W_6e348 = Some (Load SZ8 true 11 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e34c : bv 32 := 0x02058e63.
Lemma F_6e34c : fetch_word AsanUbsan.M.loaded_segments (0x6e34c : word) = Some W_6e34c.
Proof. vm_refl. Qed.
Lemma D_6e34c : decode_any W_6e34c = Some (Branch BC_EQ 11 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e350 : bv 32 := 0x00040513.
Lemma F_6e350 : fetch_word AsanUbsan.M.loaded_segments (0x6e350 : word) = Some W_6e350.
Proof. vm_refl. Qed.
Lemma D_6e350 : decode_any W_6e350 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e354 : bv 32 := 0x000580e7.
Lemma F_6e354 : fetch_word AsanUbsan.M.loaded_segments (0x6e354 : word) = Some W_6e354.
Proof. vm_refl. Qed.
Lemma D_6e354 : decode_any W_6e354 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e358 : bv 32 := 0x0284b583.
Lemma F_6e358 : fetch_word AsanUbsan.M.loaded_segments (0x6e358 : word) = Some W_6e358.
Proof. vm_refl. Qed.
Lemma D_6e358 : decode_any W_6e358 = Some (Load SZ8 true 11 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e35c : bv 32 := 0x02058663.
Lemma F_6e35c : fetch_word AsanUbsan.M.loaded_segments (0x6e35c : word) = Some W_6e35c.
Proof. vm_refl. Qed.
Lemma D_6e35c : decode_any W_6e35c = Some (Branch BC_EQ 11 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e360 : bv 32 := 0x00040513.
Lemma F_6e360 : fetch_word AsanUbsan.M.loaded_segments (0x6e360 : word) = Some W_6e360.
Proof. vm_refl. Qed.
Lemma D_6e360 : decode_any W_6e360 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e364 : bv 32 := 0x000580e7.
Lemma F_6e364 : fetch_word AsanUbsan.M.loaded_segments (0x6e364 : word) = Some W_6e364.
Proof. vm_refl. Qed.
Lemma D_6e364 : decode_any W_6e364 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e368 : bv 32 := 0x0384b583.
Lemma F_6e368 : fetch_word AsanUbsan.M.loaded_segments (0x6e368 : word) = Some W_6e368.
Proof. vm_refl. Qed.
Lemma D_6e368 : decode_any W_6e368 = Some (Load SZ8 true 11 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e36c : bv 32 := 0x00058e63.
Lemma F_6e36c : fetch_word AsanUbsan.M.loaded_segments (0x6e36c : word) = Some W_6e36c.
Proof. vm_refl. Qed.
Lemma D_6e36c : decode_any W_6e36c = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e370 : bv 32 := 0x00040513.
Lemma F_6e370 : fetch_word AsanUbsan.M.loaded_segments (0x6e370 : word) = Some W_6e370.
Proof. vm_refl. Qed.
Lemma D_6e370 : decode_any W_6e370 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e374 : bv 32 := 0x000580e7.
Lemma F_6e374 : fetch_word AsanUbsan.M.loaded_segments (0x6e374 : word) = Some W_6e374.
Proof. vm_refl. Qed.
Lemma D_6e374 : decode_any W_6e374 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e378 : bv 32 := 0x0484b583.
Lemma F_6e378 : fetch_word AsanUbsan.M.loaded_segments (0x6e378 : word) = Some W_6e378.
Proof. vm_refl. Qed.
Lemma D_6e378 : decode_any W_6e378 = Some (Load SZ8 true 11 9 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e37c : bv 32 := 0x00058663.
Lemma F_6e37c : fetch_word AsanUbsan.M.loaded_segments (0x6e37c : word) = Some W_6e37c.
Proof. vm_refl. Qed.
Lemma D_6e37c : decode_any W_6e37c = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e380 : bv 32 := 0x00040513.
Lemma F_6e380 : fetch_word AsanUbsan.M.loaded_segments (0x6e380 : word) = Some W_6e380.
Proof. vm_refl. Qed.
Lemma D_6e380 : decode_any W_6e380 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e384 : bv 32 := 0x000580e7.
Lemma F_6e384 : fetch_word AsanUbsan.M.loaded_segments (0x6e384 : word) = Some W_6e384.
Proof. vm_refl. Qed.
Lemma D_6e384 : decode_any W_6e384 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e388 : bv 32 := 0x00000513.
Lemma F_6e388 : fetch_word AsanUbsan.M.loaded_segments (0x6e388 : word) = Some W_6e388.
Proof. vm_refl. Qed.
Lemma D_6e388 : decode_any W_6e388 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e38c : bv 32 := 0x01813083.
Lemma F_6e38c : fetch_word AsanUbsan.M.loaded_segments (0x6e38c : word) = Some W_6e38c.
Proof. vm_refl. Qed.
Lemma D_6e38c : decode_any W_6e38c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e390 : bv 32 := 0x01013403.
Lemma F_6e390 : fetch_word AsanUbsan.M.loaded_segments (0x6e390 : word) = Some W_6e390.
Proof. vm_refl. Qed.
Lemma D_6e390 : decode_any W_6e390 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e394 : bv 32 := 0x00813483.
Lemma F_6e394 : fetch_word AsanUbsan.M.loaded_segments (0x6e394 : word) = Some W_6e394.
Proof. vm_refl. Qed.
Lemma D_6e394 : decode_any W_6e394 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e398 : bv 32 := 0x02010113.
Lemma F_6e398 : fetch_word AsanUbsan.M.loaded_segments (0x6e398 : word) = Some W_6e398.
Proof. vm_refl. Qed.
Lemma D_6e398 : decode_any W_6e398 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e39c : bv 32 := 0x00008067.
Lemma F_6e39c : fetch_word AsanUbsan.M.loaded_segments (0x6e39c : word) = Some W_6e39c.
Proof. vm_refl. Qed.
Lemma D_6e39c : decode_any W_6e39c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e3a0 : bv 32 := 0x00000513.
Lemma F_6e3a0 : fetch_word AsanUbsan.M.loaded_segments (0x6e3a0 : word) = Some W_6e3a0.
Proof. vm_refl. Qed.
Lemma D_6e3a0 : decode_any W_6e3a0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e3a4 : bv 32 := 0x00008067.
Lemma F_6e3a4 : fetch_word AsanUbsan.M.loaded_segments (0x6e3a4 : word) = Some W_6e3a4.
Proof. vm_refl. Qed.
Lemma D_6e3a4 : decode_any W_6e3a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e3a8 : bv 32 := 0x00008067.
Lemma F_6e3a8 : fetch_word AsanUbsan.M.loaded_segments (0x6e3a8 : word) = Some W_6e3a8.
Proof. vm_refl. Qed.
Lemma D_6e3a8 : decode_any W_6e3a8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

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

Definition W_4e1bc : bv 32 := 0x06048a63.
Lemma F_4e1bc : fetch_word AsanUbsan.M.loaded_segments (0x4e1bc : word) = Some W_4e1bc.
Proof. vm_refl. Qed.
Lemma D_4e1bc : decode_any W_4e1bc = Some (Branch BC_EQ 9 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e1c0 : bv 32 := 0x00088597.
Lemma F_4e1c0 : fetch_word AsanUbsan.M.loaded_segments (0x4e1c0 : word) = Some W_4e1c0.
Proof. vm_refl. Qed.
Lemma D_4e1c0 : decode_any W_4e1c0 = Some (Auipc 11 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e1c4 : bv 32 := 0x2f85ba83.
Lemma F_4e1c4 : fetch_word AsanUbsan.M.loaded_segments (0x4e1c4 : word) = Some W_4e1c4.
Proof. vm_refl. Qed.
Lemma D_4e1c4 : decode_any W_4e1c4 = Some (Load SZ8 true 21 11 760, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e1c8 : bv 32 := 0x0fbac583.
Lemma F_4e1c8 : fetch_word AsanUbsan.M.loaded_segments (0x4e1c8 : word) = Some W_4e1c8.
Proof. vm_refl. Qed.
Lemma D_4e1c8 : decode_any W_4e1c8 = Some (Load SZ1 false 11 21 251, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e1cc : bv 32 := 0x06058263.
Lemma F_4e1cc : fetch_word AsanUbsan.M.loaded_segments (0x4e1cc : word) = Some W_4e1cc.
Proof. vm_refl. Qed.
Lemma D_4e1cc : decode_any W_4e1cc = Some (Branch BC_EQ 11 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e1d0 : bv 32 := 0x00150493.
Lemma F_4e1d0 : fetch_word AsanUbsan.M.loaded_segments (0x4e1d0 : word) = Some W_4e1d0.
Proof. vm_refl. Qed.
Lemma D_4e1d0 : decode_any W_4e1d0 = Some (OpImm ALU_ADD 9 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e1d4 : bv 32 := 0x0934f463.
Lemma F_4e1d4 : fetch_word AsanUbsan.M.loaded_segments (0x4e1d4 : word) = Some W_4e1d4.
Proof. vm_refl. Qed.
Lemma D_4e1d4 : decode_any W_4e1d4 = Some (Branch BC_GEU 9 19 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e1d8 : bv 32 := 0xfff94593.
Lemma F_4e1d8 : fetch_word AsanUbsan.M.loaded_segments (0x4e1d8 : word) = Some W_4e1d8.
Proof. vm_refl. Qed.
Lemma D_4e1d8 : decode_any W_4e1d8 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e1dc : bv 32 := 0x80040a13.
Lemma F_4e1dc : fetch_word AsanUbsan.M.loaded_segments (0x4e1dc : word) = Some W_4e1dc.
Proof. vm_refl. Qed.
Lemma D_4e1dc : decode_any W_4e1dc = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e1e0 : bv 32 := 0xfa8a0a13.
Lemma F_4e1e0 : fetch_word AsanUbsan.M.loaded_segments (0x4e1e0 : word) = Some W_4e1e0.
Proof. vm_refl. Qed.
Lemma D_4e1e0 : decode_any W_4e1e0 = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e1e4 : bv 32 := 0x0895e663.
Lemma F_4e1e4 : fetch_word AsanUbsan.M.loaded_segments (0x4e1e4 : word) = Some W_4e1e4.
Proof. vm_refl. Qed.
Lemma D_4e1e4 : decode_any W_4e1e4 = Some (Branch BC_LTU 11 9 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e1e8 : bv 32 := 0xfbf48593.
Lemma F_4e1e8 : fetch_word AsanUbsan.M.loaded_segments (0x4e1e8 : word) = Some W_4e1e8.
Proof. vm_refl. Qed.
Lemma D_4e1e8 : decode_any W_4e1e8 = Some (OpImm ALU_ADD 11 9 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e1ec : bv 32 := 0xfbf00613.
Lemma F_4e1ec : fetch_word AsanUbsan.M.loaded_segments (0x4e1ec : word) = Some W_4e1ec.
Proof. vm_refl. Qed.
Lemma D_4e1ec : decode_any W_4e1ec = Some (OpImm ALU_ADD 12 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e1f0 : bv 32 := 0x0eb67863.
Lemma F_4e1f0 : fetch_word AsanUbsan.M.loaded_segments (0x4e1f0 : word) = Some W_4e1f0.
Proof. vm_refl. Qed.
Lemma D_4e1f0 : decode_any W_4e1f0 = Some (Branch BC_GEU 12 11 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e1f4 : bv 32 := 0x00088597.
Lemma F_4e1f4 : fetch_word AsanUbsan.M.loaded_segments (0x4e1f4 : word) = Some W_4e1f4.
Proof. vm_refl. Qed.
Lemma D_4e1f4 : decode_any W_4e1f4 = Some (Auipc 11 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e1f8 : bv 32 := 0x2d45b583.
Lemma F_4e1f8 : fetch_word AsanUbsan.M.loaded_segments (0x4e1f8 : word) = Some W_4e1f8.
Proof. vm_refl. Qed.
Lemma D_4e1f8 : decode_any W_4e1f8 = Some (Load SZ8 true 11 11 724, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e1fc : bv 32 := 0x009906b3.
Lemma F_4e1fc : fetch_word AsanUbsan.M.loaded_segments (0x4e1fc : word) = Some W_4e1fc.
Proof. vm_refl. Qed.
Lemma D_4e1fc : decode_any W_4e1fc = Some (Op ALU_ADD 13 18 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e200 : bv 32 := 0x0005b603.
Lemma F_4e200 : fetch_word AsanUbsan.M.loaded_segments (0x4e200 : word) = Some W_4e200.
Proof. vm_refl. Qed.
Lemma D_4e200 : decode_any W_4e200 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e204 : bv 32 := 0x00395593.
Lemma F_4e204 : fetch_word AsanUbsan.M.loaded_segments (0x4e204 : word) = Some W_4e204.
Proof. vm_refl. Qed.
Lemma D_4e204 : decode_any W_4e204 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e208 : bv 32 := 0xfff68693.
Lemma F_4e208 : fetch_word AsanUbsan.M.loaded_segments (0x4e208 : word) = Some W_4e208.
Proof. vm_refl. Qed.
Lemma D_4e208 : decode_any W_4e208 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e20c : bv 32 := 0x0036d713.
Lemma F_4e20c : fetch_word AsanUbsan.M.loaded_segments (0x4e20c : word) = Some W_4e20c.
Proof. vm_refl. Qed.
Lemma D_4e20c : decode_any W_4e20c = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e210 : bv 32 := 0x00b605b3.
Lemma F_4e210 : fetch_word AsanUbsan.M.loaded_segments (0x4e210 : word) = Some W_4e210.
Proof. vm_refl. Qed.
Lemma D_4e210 : decode_any W_4e210 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e214 : bv 32 := 0x00e60633.
Lemma F_4e214 : fetch_word AsanUbsan.M.loaded_segments (0x4e214 : word) = Some W_4e214.
Proof. vm_refl. Qed.
Lemma D_4e214 : decode_any W_4e214 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e218 : bv 32 := 0xff85f713.
Lemma F_4e218 : fetch_word AsanUbsan.M.loaded_segments (0x4e218 : word) = Some W_4e218.
Proof. vm_refl. Qed.
Lemma D_4e218 : decode_any W_4e218 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e21c : bv 32 := 0xff867793.
Lemma F_4e21c : fetch_word AsanUbsan.M.loaded_segments (0x4e21c : word) = Some W_4e21c.
Proof. vm_refl. Qed.
Lemma D_4e21c : decode_any W_4e21c = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e220 : bv 32 := 0x00073703.
Lemma F_4e220 : fetch_word AsanUbsan.M.loaded_segments (0x4e220 : word) = Some W_4e220.
Proof. vm_refl. Qed.
Lemma D_4e220 : decode_any W_4e220 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e224 : bv 32 := 0x0007b783.
Lemma F_4e224 : fetch_word AsanUbsan.M.loaded_segments (0x4e224 : word) = Some W_4e224.
Proof. vm_refl. Qed.
Lemma D_4e224 : decode_any W_4e224 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e228 : bv 32 := 0x00e7e733.
Lemma F_4e228 : fetch_word AsanUbsan.M.loaded_segments (0x4e228 : word) = Some W_4e228.
Proof. vm_refl. Qed.
Lemma D_4e228 : decode_any W_4e228 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e22c : bv 32 := 0x0a071e63.
Lemma F_4e22c : fetch_word AsanUbsan.M.loaded_segments (0x4e22c : word) = Some W_4e22c.
Proof. vm_refl. Qed.
Lemma D_4e22c : decode_any W_4e22c = Some (Branch BC_NE 14 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e230 : bv 32 := 0x07010113.
Lemma F_4e230 : fetch_word AsanUbsan.M.loaded_segments (0x4e230 : word) = Some W_4e230.
Proof. vm_refl. Qed.
Lemma D_4e230 : decode_any W_4e230 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e234 : bv 32 := 0x7e813083.
Lemma F_4e234 : fetch_word AsanUbsan.M.loaded_segments (0x4e234 : word) = Some W_4e234.
Proof. vm_refl. Qed.
Lemma D_4e234 : decode_any W_4e234 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e238 : bv 32 := 0x7e013403.
Lemma F_4e238 : fetch_word AsanUbsan.M.loaded_segments (0x4e238 : word) = Some W_4e238.
Proof. vm_refl. Qed.
Lemma D_4e238 : decode_any W_4e238 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e23c : bv 32 := 0x7d813483.
Lemma F_4e23c : fetch_word AsanUbsan.M.loaded_segments (0x4e23c : word) = Some W_4e23c.
Proof. vm_refl. Qed.
Lemma D_4e23c : decode_any W_4e23c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e240 : bv 32 := 0x7d013903.
Lemma F_4e240 : fetch_word AsanUbsan.M.loaded_segments (0x4e240 : word) = Some W_4e240.
Proof. vm_refl. Qed.
Lemma D_4e240 : decode_any W_4e240 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e244 : bv 32 := 0x7c813983.
Lemma F_4e244 : fetch_word AsanUbsan.M.loaded_segments (0x4e244 : word) = Some W_4e244.
Proof. vm_refl. Qed.
Lemma D_4e244 : decode_any W_4e244 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e248 : bv 32 := 0x7c013a03.
Lemma F_4e248 : fetch_word AsanUbsan.M.loaded_segments (0x4e248 : word) = Some W_4e248.
Proof. vm_refl. Qed.
Lemma D_4e248 : decode_any W_4e248 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e24c : bv 32 := 0x7b813a83.
Lemma F_4e24c : fetch_word AsanUbsan.M.loaded_segments (0x4e24c : word) = Some W_4e24c.
Proof. vm_refl. Qed.
Lemma D_4e24c : decode_any W_4e24c = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e250 : bv 32 := 0x7b013b03.
Lemma F_4e250 : fetch_word AsanUbsan.M.loaded_segments (0x4e250 : word) = Some W_4e250.
Proof. vm_refl. Qed.
Lemma D_4e250 : decode_any W_4e250 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e254 : bv 32 := 0x7f010113.
Lemma F_4e254 : fetch_word AsanUbsan.M.loaded_segments (0x4e254 : word) = Some W_4e254.
Proof. vm_refl. Qed.
Lemma D_4e254 : decode_any W_4e254 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e258 : bv 32 := 0x00008067.
Lemma F_4e258 : fetch_word AsanUbsan.M.loaded_segments (0x4e258 : word) = Some W_4e258.
Proof. vm_refl. Qed.
Lemma D_4e258 : decode_any W_4e258 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e25c : bv 32 := 0x00098493.
Lemma F_4e25c : fetch_word AsanUbsan.M.loaded_segments (0x4e25c : word) = Some W_4e25c.
Proof. vm_refl. Qed.
Lemma D_4e25c : decode_any W_4e25c = Some (OpImm ALU_ADD 9 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e260 : bv 32 := 0xfff94593.
Lemma F_4e260 : fetch_word AsanUbsan.M.loaded_segments (0x4e260 : word) = Some W_4e260.
Proof. vm_refl. Qed.
Lemma D_4e260 : decode_any W_4e260 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e264 : bv 32 := 0x80040a13.
Lemma F_4e264 : fetch_word AsanUbsan.M.loaded_segments (0x4e264 : word) = Some W_4e264.
Proof. vm_refl. Qed.
Lemma D_4e264 : decode_any W_4e264 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e268 : bv 32 := 0xfa8a0a13.
Lemma F_4e268 : fetch_word AsanUbsan.M.loaded_segments (0x4e268 : word) = Some W_4e268.
Proof. vm_refl. Qed.
Lemma D_4e268 : decode_any W_4e268 = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e26c : bv 32 := 0xf735fee3.
Lemma F_4e26c : fetch_word AsanUbsan.M.loaded_segments (0x4e26c : word) = Some W_4e26c.
Proof. vm_refl. Qed.
Lemma D_4e26c : decode_any W_4e26c = Some (Branch BC_GEU 11 19 8060, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e270 : bv 32 := 0x80040593.
Lemma F_4e270 : fetch_word AsanUbsan.M.loaded_segments (0x4e270 : word) = Some W_4e270.
Proof. vm_refl. Qed.
Lemma D_4e270 : decode_any W_4e270 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e274 : bv 32 := 0xfb858593.
Lemma F_4e274 : fetch_word AsanUbsan.M.loaded_segments (0x4e274 : word) = Some W_4e274.
Proof. vm_refl. Qed.
Lemma D_4e274 : decode_any W_4e274 = Some (OpImm ALU_ADD 11 11 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e278 : bv 32 := 0x80040613.
Lemma F_4e278 : fetch_word AsanUbsan.M.loaded_segments (0x4e278 : word) = Some W_4e278.
Proof. vm_refl. Qed.
Lemma D_4e278 : decode_any W_4e278 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e27c : bv 32 := 0xfa860613.
Lemma F_4e27c : fetch_word AsanUbsan.M.loaded_segments (0x4e27c : word) = Some W_4e27c.
Proof. vm_refl. Qed.
Lemma D_4e27c : decode_any W_4e27c = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e280 : bv 32 := 0x7ff60b13.
Lemma F_4e280 : fetch_word AsanUbsan.M.loaded_segments (0x4e280 : word) = Some W_4e280.
Proof. vm_refl. Qed.
Lemma D_4e280 : decode_any W_4e280 = Some (OpImm ALU_ADD 22 12 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e284 : bv 32 := 0x000b34a3.
Lemma F_4e284 : fetch_word AsanUbsan.M.loaded_segments (0x4e284 : word) = Some W_4e284.
Proof. vm_refl. Qed.
Lemma D_4e284 : decode_any W_4e284 = Some (Store SZ8 22 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e288 : bv 32 := 0x00ba3023.
Lemma F_4e288 : fetch_word AsanUbsan.M.loaded_segments (0x4e288 : word) = Some W_4e288.
Proof. vm_refl. Qed.
Lemma D_4e288 : decode_any W_4e288 = Some (Store SZ8 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e28c : bv 32 := 0x000a3423.
Lemma F_4e28c : fetch_word AsanUbsan.M.loaded_segments (0x4e28c : word) = Some W_4e28c.
Proof. vm_refl. Qed.
Lemma D_4e28c : decode_any W_4e28c = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e290 : bv 32 := 0x00050993.
Lemma F_4e290 : fetch_word AsanUbsan.M.loaded_segments (0x4e290 : word) = Some W_4e290.
Proof. vm_refl. Qed.
Lemma D_4e290 : decode_any W_4e290 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e294 : bv 32 := 0x019320ef.
Lemma F_4e294 : fetch_word AsanUbsan.M.loaded_segments (0x4e294 : word) = Some W_4e294.
Proof. vm_refl. Qed.
Lemma D_4e294 : decode_any W_4e294 = Some (Jal 1 206872, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e298 : bv 32 := 0x00050593.
Lemma F_4e298 : fetch_word AsanUbsan.M.loaded_segments (0x4e298 : word) = Some W_4e298.
Proof. vm_refl. Qed.
Lemma D_4e298 : decode_any W_4e298 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e29c : bv 32 := 0x021ac703.
Lemma F_4e29c : fetch_word AsanUbsan.M.loaded_segments (0x4e29c : word) = Some W_4e29c.
Proof. vm_refl. Qed.
Lemma D_4e29c : decode_any W_4e29c = Some (Load SZ1 false 14 21 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2a0 : bv 32 := 0x008b34a3.
Lemma F_4e2a0 : fetch_word AsanUbsan.M.loaded_segments (0x4e2a0 : word) = Some W_4e2a0.
Proof. vm_refl. Qed.
Lemma D_4e2a0 : decode_any W_4e2a0 = Some (Store SZ8 22 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2a4 : bv 32 := 0x80040513.
Lemma F_4e2a4 : fetch_word AsanUbsan.M.loaded_segments (0x4e2a4 : word) = Some W_4e2a4.
Proof. vm_refl. Qed.
Lemma D_4e2a4 : decode_any W_4e2a4 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2a8 : bv 32 := 0xfa850513.
Lemma F_4e2a8 : fetch_word AsanUbsan.M.loaded_segments (0x4e2a8 : word) = Some W_4e2a8.
Proof. vm_refl. Qed.
Lemma D_4e2a8 : decode_any W_4e2a8 = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2ac : bv 32 := 0x0ff00793.
Lemma F_4e2ac : fetch_word AsanUbsan.M.loaded_segments (0x4e2ac : word) = Some W_4e2ac.
Proof. vm_refl. Qed.
Lemma D_4e2ac : decode_any W_4e2ac = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2b0 : bv 32 := 0x00040613.
Lemma F_4e2b0 : fetch_word AsanUbsan.M.loaded_segments (0x4e2b0 : word) = Some W_4e2b0.
Proof. vm_refl. Qed.
Lemma D_4e2b0 : decode_any W_4e2b0 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2b4 : bv 32 := 0x00000693.
Lemma F_4e2b4 : fetch_word AsanUbsan.M.loaded_segments (0x4e2b4 : word) = Some W_4e2b4.
Proof. vm_refl. Qed.
Lemma D_4e2b4 : decode_any W_4e2b4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2b8 : bv 32 := 0x545190ef.
Lemma F_4e2b8 : fetch_word AsanUbsan.M.loaded_segments (0x4e2b8 : word) = Some W_4e2b8.
Proof. vm_refl. Qed.
Lemma D_4e2b8 : decode_any W_4e2b8 = Some (Jal 1 105796, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2bc : bv 32 := 0x80040613.
Lemma F_4e2bc : fetch_word AsanUbsan.M.loaded_segments (0x4e2bc : word) = Some W_4e2bc.
Proof. vm_refl. Qed.
Lemma D_4e2bc : decode_any W_4e2bc = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2c0 : bv 32 := 0xfa860613.
Lemma F_4e2c0 : fetch_word AsanUbsan.M.loaded_segments (0x4e2c0 : word) = Some W_4e2c0.
Proof. vm_refl. Qed.
Lemma D_4e2c0 : decode_any W_4e2c0 = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2c4 : bv 32 := 0x00090513.
Lemma F_4e2c4 : fetch_word AsanUbsan.M.loaded_segments (0x4e2c4 : word) = Some W_4e2c4.
Proof. vm_refl. Qed.
Lemma D_4e2c4 : decode_any W_4e2c4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2c8 : bv 32 := 0x00048593.
Lemma F_4e2c8 : fetch_word AsanUbsan.M.loaded_segments (0x4e2c8 : word) = Some W_4e2c8.
Proof. vm_refl. Qed.
Lemma D_4e2c8 : decode_any W_4e2c8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2cc : bv 32 := 0x2e9160ef.
Lemma F_4e2cc : fetch_word AsanUbsan.M.loaded_segments (0x4e2cc : word) = Some W_4e2cc.
Proof. vm_refl. Qed.
Lemma D_4e2cc : decode_any W_4e2cc = Some (Jal 1 92904, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2d0 : bv 32 := 0x00098513.
Lemma F_4e2d0 : fetch_word AsanUbsan.M.loaded_segments (0x4e2d0 : word) = Some W_4e2d0.
Proof. vm_refl. Qed.
Lemma D_4e2d0 : decode_any W_4e2d0 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2d4 : bv 32 := 0xfbf48593.
Lemma F_4e2d4 : fetch_word AsanUbsan.M.loaded_segments (0x4e2d4 : word) = Some W_4e2d4.
Proof. vm_refl. Qed.
Lemma D_4e2d4 : decode_any W_4e2d4 = Some (OpImm ALU_ADD 11 9 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2d8 : bv 32 := 0xfbf00613.
Lemma F_4e2d8 : fetch_word AsanUbsan.M.loaded_segments (0x4e2d8 : word) = Some W_4e2d8.
Proof. vm_refl. Qed.
Lemma D_4e2d8 : decode_any W_4e2d8 = Some (OpImm ALU_ADD 12 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2dc : bv 32 := 0xf0b66ce3.
Lemma F_4e2dc : fetch_word AsanUbsan.M.loaded_segments (0x4e2dc : word) = Some W_4e2dc.
Proof. vm_refl. Qed.
Lemma D_4e2dc : decode_any W_4e2dc = Some (Branch BC_LTU 12 11 7960, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2e0 : bv 32 := 0x02049e63.
Lemma F_4e2e0 : fetch_word AsanUbsan.M.loaded_segments (0x4e2e0 : word) = Some W_4e2e0.
Proof. vm_refl. Qed.
Lemma D_4e2e0 : decode_any W_4e2e0 = Some (Branch BC_NE 9 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2e4 : bv 32 := 0xf4dff06f.
Lemma F_4e2e4 : fetch_word AsanUbsan.M.loaded_segments (0x4e2e4 : word) = Some W_4e2e4.
Proof. vm_refl. Qed.
Lemma D_4e2e4 : decode_any W_4e2e4 = Some (Jal 0 2096972, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2e8 : bv 32 := 0x00060703.
Lemma F_4e2e8 : fetch_word AsanUbsan.M.loaded_segments (0x4e2e8 : word) = Some W_4e2e8.
Proof. vm_refl. Qed.
Lemma D_4e2e8 : decode_any W_4e2e8 = Some (Load SZ1 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2ec : bv 32 := 0x0076f693.
Lemma F_4e2ec : fetch_word AsanUbsan.M.loaded_segments (0x4e2ec : word) = Some W_4e2ec.
Proof. vm_refl. Qed.
Lemma D_4e2ec : decode_any W_4e2ec = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2f0 : bv 32 := 0x00e037b3.
Lemma F_4e2f0 : fetch_word AsanUbsan.M.loaded_segments (0x4e2f0 : word) = Some W_4e2f0.
Proof. vm_refl. Qed.
Lemma D_4e2f0 : decode_any W_4e2f0 = Some (Op ALU_SLTU 15 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2f4 : bv 32 := 0x00e6a6b3.
Lemma F_4e2f4 : fetch_word AsanUbsan.M.loaded_segments (0x4e2f4 : word) = Some W_4e2f4.
Proof. vm_refl. Qed.
Lemma D_4e2f4 : decode_any W_4e2f4 = Some (Op ALU_SLT 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2f8 : bv 32 := 0x0016c693.
Lemma F_4e2f8 : fetch_word AsanUbsan.M.loaded_segments (0x4e2f8 : word) = Some W_4e2f8.
Proof. vm_refl. Qed.
Lemma D_4e2f8 : decode_any W_4e2f8 = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e2fc : bv 32 := 0x00d7f6b3.
Lemma F_4e2fc : fetch_word AsanUbsan.M.loaded_segments (0x4e2fc : word) = Some W_4e2fc.
Proof. vm_refl. Qed.
Lemma D_4e2fc : decode_any W_4e2fc = Some (Op ALU_AND 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e300 : bv 32 := 0x00c5fa63.
Lemma F_4e300 : fetch_word AsanUbsan.M.loaded_segments (0x4e300 : word) = Some W_4e300.
Proof. vm_refl. Qed.
Lemma D_4e300 : decode_any W_4e300 = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e304 : bv 32 := 0x0005c703.
Lemma F_4e304 : fetch_word AsanUbsan.M.loaded_segments (0x4e304 : word) = Some W_4e304.
Proof. vm_refl. Qed.
Lemma D_4e304 : decode_any W_4e304 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e308 : bv 32 := 0x00158593.
Lemma F_4e308 : fetch_word AsanUbsan.M.loaded_segments (0x4e308 : word) = Some W_4e308.
Proof. vm_refl. Qed.
Lemma D_4e308 : decode_any W_4e308 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e30c : bv 32 := 0x00d766b3.
Lemma F_4e30c : fetch_word AsanUbsan.M.loaded_segments (0x4e30c : word) = Some W_4e30c.
Proof. vm_refl. Qed.
Lemma D_4e30c : decode_any W_4e30c = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e310 : bv 32 := 0xfec59ae3.
Lemma F_4e310 : fetch_word AsanUbsan.M.loaded_segments (0x4e310 : word) = Some W_4e310.
Proof. vm_refl. Qed.
Lemma D_4e310 : decode_any W_4e310 = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e314 : bv 32 := 0x0ff6f593.
Lemma F_4e314 : fetch_word AsanUbsan.M.loaded_segments (0x4e314 : word) = Some W_4e314.
Proof. vm_refl. Qed.
Lemma D_4e314 : decode_any W_4e314 = Some (OpImm ALU_AND 11 13 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e318 : bv 32 := 0xf0058ce3.
Lemma F_4e318 : fetch_word AsanUbsan.M.loaded_segments (0x4e318 : word) = Some W_4e318.
Proof. vm_refl. Qed.
Lemma D_4e318 : decode_any W_4e318 = Some (Branch BC_EQ 11 0 7960, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e31c : bv 32 := 0x00050b13.
Lemma F_4e31c : fetch_word AsanUbsan.M.loaded_segments (0x4e31c : word) = Some W_4e31c.
Proof. vm_refl. Qed.
Lemma D_4e31c : decode_any W_4e31c = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e320 : bv 32 := 0x00090513.
Lemma F_4e320 : fetch_word AsanUbsan.M.loaded_segments (0x4e320 : word) = Some W_4e320.
Proof. vm_refl. Qed.
Lemma D_4e320 : decode_any W_4e320 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e324 : bv 32 := 0x00048593.
Lemma F_4e324 : fetch_word AsanUbsan.M.loaded_segments (0x4e324 : word) = Some W_4e324.
Proof. vm_refl. Qed.
Lemma D_4e324 : decode_any W_4e324 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e328 : bv 32 := 0x059130ef.
Lemma F_4e328 : fetch_word AsanUbsan.M.loaded_segments (0x4e328 : word) = Some W_4e328.
Proof. vm_refl. Qed.
Lemma D_4e328 : decode_any W_4e328 = Some (Jal 1 79960, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e32c : bv 32 := 0x00050913.
Lemma F_4e32c : fetch_word AsanUbsan.M.loaded_segments (0x4e32c : word) = Some W_4e32c.
Proof. vm_refl. Qed.
Lemma D_4e32c : decode_any W_4e32c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e330 : bv 32 := 0x000b0513.
Lemma F_4e330 : fetch_word AsanUbsan.M.loaded_segments (0x4e330 : word) = Some W_4e330.
Proof. vm_refl. Qed.
Lemma D_4e330 : decode_any W_4e330 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e334 : bv 32 := 0xee090ee3.
Lemma F_4e334 : fetch_word AsanUbsan.M.loaded_segments (0x4e334 : word) = Some W_4e334.
Proof. vm_refl. Qed.
Lemma D_4e334 : decode_any W_4e334 = Some (Branch BC_EQ 18 0 7932, 4%Z).
Proof. vm_refl. Qed.

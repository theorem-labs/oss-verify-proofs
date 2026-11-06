(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_5e1f0 : bv 32 := 0x0d00006f.
Lemma F_5e1f0 : fetch_word Plain.M.loaded_segments (0x5e1f0 : word) = Some W_5e1f0.
Proof. vm_refl. Qed.
Lemma D_5e1f0 : decode_any W_5e1f0 = Some (Jal 0 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e1f4 : bv 32 := 0x0ff5f593.
Lemma F_5e1f4 : fetch_word Plain.M.loaded_segments (0x5e1f4 : word) = Some W_5e1f4.
Proof. vm_refl. Qed.
Lemma D_5e1f4 : decode_any W_5e1f4 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e1f8 : bv 32 := 0x00757693.
Lemma F_5e1f8 : fetch_word Plain.M.loaded_segments (0x5e1f8 : word) = Some W_5e1f8.
Proof. vm_refl. Qed.
Lemma D_5e1f8 : decode_any W_5e1f8 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e1fc : bv 32 := 0x00c03733.
Lemma F_5e1fc : fetch_word Plain.M.loaded_segments (0x5e1fc : word) = Some W_5e1fc.
Proof. vm_refl. Qed.
Lemma D_5e1fc : decode_any W_5e1fc = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e200 : bv 32 := 0x02068c63.
Lemma F_5e200 : fetch_word Plain.M.loaded_segments (0x5e200 : word) = Some W_5e200.
Proof. vm_refl. Qed.
Lemma D_5e200 : decode_any W_5e200 = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e204 : bv 32 := 0x02060a63.
Lemma F_5e204 : fetch_word Plain.M.loaded_segments (0x5e204 : word) = Some W_5e204.
Proof. vm_refl. Qed.
Lemma D_5e204 : decode_any W_5e204 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e208 : bv 32 := 0x00150793.
Lemma F_5e208 : fetch_word Plain.M.loaded_segments (0x5e208 : word) = Some W_5e208.
Proof. vm_refl. Qed.
Lemma D_5e208 : decode_any W_5e208 = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e20c : bv 32 := 0x00100813.
Lemma F_5e20c : fetch_word Plain.M.loaded_segments (0x5e20c : word) = Some W_5e20c.
Proof. vm_refl. Qed.
Lemma D_5e20c : decode_any W_5e20c = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e210 : bv 32 := 0x00054703.
Lemma F_5e210 : fetch_word Plain.M.loaded_segments (0x5e210 : word) = Some W_5e210.
Proof. vm_refl. Qed.
Lemma D_5e210 : decode_any W_5e210 = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e214 : bv 32 := 0x00060693.
Lemma F_5e214 : fetch_word Plain.M.loaded_segments (0x5e214 : word) = Some W_5e214.
Proof. vm_refl. Qed.
Lemma D_5e214 : decode_any W_5e214 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e218 : bv 32 := 0x06b70e63.
Lemma F_5e218 : fetch_word Plain.M.loaded_segments (0x5e218 : word) = Some W_5e218.
Proof. vm_refl. Qed.
Lemma D_5e218 : decode_any W_5e218 = Some (Branch BC_EQ 14 11 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e21c : bv 32 := 0x00150513.
Lemma F_5e21c : fetch_word Plain.M.loaded_segments (0x5e21c : word) = Some W_5e21c.
Proof. vm_refl. Qed.
Lemma D_5e21c : decode_any W_5e21c = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e220 : bv 32 := 0xfff68613.
Lemma F_5e220 : fetch_word Plain.M.loaded_segments (0x5e220 : word) = Some W_5e220.
Proof. vm_refl. Qed.
Lemma D_5e220 : decode_any W_5e220 = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e224 : bv 32 := 0x0077f893.
Lemma F_5e224 : fetch_word Plain.M.loaded_segments (0x5e224 : word) = Some W_5e224.
Proof. vm_refl. Qed.
Lemma D_5e224 : decode_any W_5e224 = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e228 : bv 32 := 0x00c03733.
Lemma F_5e228 : fetch_word Plain.M.loaded_segments (0x5e228 : word) = Some W_5e228.
Proof. vm_refl. Qed.
Lemma D_5e228 : decode_any W_5e228 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e22c : bv 32 := 0x00088663.
Lemma F_5e22c : fetch_word Plain.M.loaded_segments (0x5e22c : word) = Some W_5e22c.
Proof. vm_refl. Qed.
Lemma D_5e22c : decode_any W_5e22c = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e230 : bv 32 := 0x00178793.
Lemma F_5e230 : fetch_word Plain.M.loaded_segments (0x5e230 : word) = Some W_5e230.
Proof. vm_refl. Qed.
Lemma D_5e230 : decode_any W_5e230 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e234 : bv 32 := 0xfd069ee3.
Lemma F_5e234 : fetch_word Plain.M.loaded_segments (0x5e234 : word) = Some W_5e234.
Proof. vm_refl. Qed.
Lemma D_5e234 : decode_any W_5e234 = Some (Branch BC_NE 13 16 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e238 : bv 32 := 0x06070863.
Lemma F_5e238 : fetch_word Plain.M.loaded_segments (0x5e238 : word) = Some W_5e238.
Proof. vm_refl. Qed.
Lemma D_5e238 : decode_any W_5e238 = Some (Branch BC_EQ 14 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e23c : bv 32 := 0x00054683.
Lemma F_5e23c : fetch_word Plain.M.loaded_segments (0x5e23c : word) = Some W_5e23c.
Proof. vm_refl. Qed.
Lemma D_5e23c : decode_any W_5e23c = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e240 : bv 32 := 0x04b68663.
Lemma F_5e240 : fetch_word Plain.M.loaded_segments (0x5e240 : word) = Some W_5e240.
Proof. vm_refl. Qed.
Lemma D_5e240 : decode_any W_5e240 = Some (Branch BC_EQ 13 11 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e244 : bv 32 := 0x00800693.
Lemma F_5e244 : fetch_word Plain.M.loaded_segments (0x5e244 : word) = Some W_5e244.
Proof. vm_refl. Qed.
Lemma D_5e244 : decode_any W_5e244 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e248 : bv 32 := 0x04d66263.
Lemma F_5e248 : fetch_word Plain.M.loaded_segments (0x5e248 : word) = Some W_5e248.
Proof. vm_refl. Qed.
Lemma D_5e248 : decode_any W_5e248 = Some (Branch BC_LTU 12 13 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e24c : bv 32 := 0xfffb5697.
Lemma F_5e24c : fetch_word Plain.M.loaded_segments (0x5e24c : word) = Some W_5e24c.
Proof. vm_refl. Qed.
Lemma D_5e24c : decode_any W_5e24c = Some (Auipc 13 1048501, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e250 : bv 32 := 0xd6c6b683.
Lemma F_5e250 : fetch_word Plain.M.loaded_segments (0x5e250 : word) = Some W_5e250.
Proof. vm_refl. Qed.
Lemma D_5e250 : decode_any W_5e250 = Some (Load SZ8 true 13 13 3436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e254 : bv 32 := 0xfffb5717.
Lemma F_5e254 : fetch_word Plain.M.loaded_segments (0x5e254 : word) = Some W_5e254.
Proof. vm_refl. Qed.
Lemma D_5e254 : decode_any W_5e254 = Some (Auipc 14 1048501, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e258 : bv 32 := 0xd4c73703.
Lemma F_5e258 : fetch_word Plain.M.loaded_segments (0x5e258 : word) = Some W_5e258.
Proof. vm_refl. Qed.
Lemma D_5e258 : decode_any W_5e258 = Some (Load SZ8 true 14 14 3404, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e25c : bv 32 := 0x00168793.
Lemma F_5e25c : fetch_word Plain.M.loaded_segments (0x5e25c : word) = Some W_5e25c.
Proof. vm_refl. Qed.
Lemma D_5e25c : decode_any W_5e25c = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e260 : bv 32 := 0x02f587b3.
Lemma F_5e260 : fetch_word Plain.M.loaded_segments (0x5e260 : word) = Some W_5e260.
Proof. vm_refl. Qed.
Lemma D_5e260 : decode_any W_5e260 = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e264 : bv 32 := 0x00700813.
Lemma F_5e264 : fetch_word Plain.M.loaded_segments (0x5e264 : word) = Some W_5e264.
Proof. vm_refl. Qed.
Lemma D_5e264 : decode_any W_5e264 = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e268 : bv 32 := 0x00053883.
Lemma F_5e268 : fetch_word Plain.M.loaded_segments (0x5e268 : word) = Some W_5e268.
Proof. vm_refl. Qed.
Lemma D_5e268 : decode_any W_5e268 = Some (Load SZ8 true 17 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e26c : bv 32 := 0x00f8c8b3.
Lemma F_5e26c : fetch_word Plain.M.loaded_segments (0x5e26c : word) = Some W_5e26c.
Proof. vm_refl. Qed.
Lemma D_5e26c : decode_any W_5e26c = Some (Op ALU_XOR 17 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e270 : bv 32 := 0x411682b3.
Lemma F_5e270 : fetch_word Plain.M.loaded_segments (0x5e270 : word) = Some W_5e270.
Proof. vm_refl. Qed.
Lemma D_5e270 : decode_any W_5e270 = Some (Op ALU_SUB 5 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e274 : bv 32 := 0x0112e8b3.
Lemma F_5e274 : fetch_word Plain.M.loaded_segments (0x5e274 : word) = Some W_5e274.
Proof. vm_refl. Qed.
Lemma D_5e274 : decode_any W_5e274 = Some (Op ALU_OR 17 5 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e278 : bv 32 := 0x00e8f8b3.
Lemma F_5e278 : fetch_word Plain.M.loaded_segments (0x5e278 : word) = Some W_5e278.
Proof. vm_refl. Qed.
Lemma D_5e278 : decode_any W_5e278 = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e27c : bv 32 := 0x02e89a63.
Lemma F_5e27c : fetch_word Plain.M.loaded_segments (0x5e27c : word) = Some W_5e27c.
Proof. vm_refl. Qed.
Lemma D_5e27c : decode_any W_5e27c = Some (Branch BC_NE 17 14 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e280 : bv 32 := 0xff860613.
Lemma F_5e280 : fetch_word Plain.M.loaded_segments (0x5e280 : word) = Some W_5e280.
Proof. vm_refl. Qed.
Lemma D_5e280 : decode_any W_5e280 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e284 : bv 32 := 0x00850513.
Lemma F_5e284 : fetch_word Plain.M.loaded_segments (0x5e284 : word) = Some W_5e284.
Proof. vm_refl. Qed.
Lemma D_5e284 : decode_any W_5e284 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e288 : bv 32 := 0xfec860e3.
Lemma F_5e288 : fetch_word Plain.M.loaded_segments (0x5e288 : word) = Some W_5e288.
Proof. vm_refl. Qed.
Lemma D_5e288 : decode_any W_5e288 = Some (Branch BC_LTU 16 12 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e28c : bv 32 := 0x00060693.
Lemma F_5e28c : fetch_word Plain.M.loaded_segments (0x5e28c : word) = Some W_5e28c.
Proof. vm_refl. Qed.
Lemma D_5e28c : decode_any W_5e28c = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e290 : bv 32 := 0x00060c63.
Lemma F_5e290 : fetch_word Plain.M.loaded_segments (0x5e290 : word) = Some W_5e290.
Proof. vm_refl. Qed.
Lemma D_5e290 : decode_any W_5e290 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e294 : bv 32 := 0x00054603.
Lemma F_5e294 : fetch_word Plain.M.loaded_segments (0x5e294 : word) = Some W_5e294.
Proof. vm_refl. Qed.
Lemma D_5e294 : decode_any W_5e294 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e298 : bv 32 := 0x00b60a63.
Lemma F_5e298 : fetch_word Plain.M.loaded_segments (0x5e298 : word) = Some W_5e298.
Proof. vm_refl. Qed.
Lemma D_5e298 : decode_any W_5e298 = Some (Branch BC_EQ 12 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e29c : bv 32 := 0xfff68693.
Lemma F_5e29c : fetch_word Plain.M.loaded_segments (0x5e29c : word) = Some W_5e29c.
Proof. vm_refl. Qed.
Lemma D_5e29c : decode_any W_5e29c = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2a0 : bv 32 := 0x00150513.
Lemma F_5e2a0 : fetch_word Plain.M.loaded_segments (0x5e2a0 : word) = Some W_5e2a0.
Proof. vm_refl. Qed.
Lemma D_5e2a0 : decode_any W_5e2a0 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2a4 : bv 32 := 0xfe0698e3.
Lemma F_5e2a4 : fetch_word Plain.M.loaded_segments (0x5e2a4 : word) = Some W_5e2a4.
Proof. vm_refl. Qed.
Lemma D_5e2a4 : decode_any W_5e2a4 = Some (Branch BC_NE 13 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2a8 : bv 32 := 0x00000513.
Lemma F_5e2a8 : fetch_word Plain.M.loaded_segments (0x5e2a8 : word) = Some W_5e2a8.
Proof. vm_refl. Qed.
Lemma D_5e2a8 : decode_any W_5e2a8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2ac : bv 32 := 0x00008067.
Lemma F_5e2ac : fetch_word Plain.M.loaded_segments (0x5e2ac : word) = Some W_5e2ac.
Proof. vm_refl. Qed.
Lemma D_5e2ac : decode_any W_5e2ac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2b0 : bv 32 := 0x00060693.
Lemma F_5e2b0 : fetch_word Plain.M.loaded_segments (0x5e2b0 : word) = Some W_5e2b0.
Proof. vm_refl. Qed.
Lemma D_5e2b0 : decode_any W_5e2b0 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2b4 : bv 32 := 0x00054603.
Lemma F_5e2b4 : fetch_word Plain.M.loaded_segments (0x5e2b4 : word) = Some W_5e2b4.
Proof. vm_refl. Qed.
Lemma D_5e2b4 : decode_any W_5e2b4 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2b8 : bv 32 := 0xfeb612e3.
Lemma F_5e2b8 : fetch_word Plain.M.loaded_segments (0x5e2b8 : word) = Some W_5e2b8.
Proof. vm_refl. Qed.
Lemma D_5e2b8 : decode_any W_5e2b8 = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2bc : bv 32 := 0xff1ff06f.
Lemma F_5e2bc : fetch_word Plain.M.loaded_segments (0x5e2bc : word) = Some W_5e2bc.
Proof. vm_refl. Qed.
Lemma D_5e2bc : decode_any W_5e2bc = Some (Jal 0 2097136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2c0 : bv 32 := 0x02060063.
Lemma F_5e2c0 : fetch_word Plain.M.loaded_segments (0x5e2c0 : word) = Some W_5e2c0.
Proof. vm_refl. Qed.
Lemma D_5e2c0 : decode_any W_5e2c0 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2c4 : bv 32 := 0x00054683.
Lemma F_5e2c4 : fetch_word Plain.M.loaded_segments (0x5e2c4 : word) = Some W_5e2c4.
Proof. vm_refl. Qed.
Lemma D_5e2c4 : decode_any W_5e2c4 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2c8 : bv 32 := 0x0005c703.
Lemma F_5e2c8 : fetch_word Plain.M.loaded_segments (0x5e2c8 : word) = Some W_5e2c8.
Proof. vm_refl. Qed.
Lemma D_5e2c8 : decode_any W_5e2c8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2cc : bv 32 := 0x00e69e63.
Lemma F_5e2cc : fetch_word Plain.M.loaded_segments (0x5e2cc : word) = Some W_5e2cc.
Proof. vm_refl. Qed.
Lemma D_5e2cc : decode_any W_5e2cc = Some (Branch BC_NE 13 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2d0 : bv 32 := 0xfff60613.
Lemma F_5e2d0 : fetch_word Plain.M.loaded_segments (0x5e2d0 : word) = Some W_5e2d0.
Proof. vm_refl. Qed.
Lemma D_5e2d0 : decode_any W_5e2d0 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2d4 : bv 32 := 0x00150513.
Lemma F_5e2d4 : fetch_word Plain.M.loaded_segments (0x5e2d4 : word) = Some W_5e2d4.
Proof. vm_refl. Qed.
Lemma D_5e2d4 : decode_any W_5e2d4 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2d8 : bv 32 := 0x00158593.
Lemma F_5e2d8 : fetch_word Plain.M.loaded_segments (0x5e2d8 : word) = Some W_5e2d8.
Proof. vm_refl. Qed.
Lemma D_5e2d8 : decode_any W_5e2d8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2dc : bv 32 := 0xfe0614e3.
Lemma F_5e2dc : fetch_word Plain.M.loaded_segments (0x5e2dc : word) = Some W_5e2dc.
Proof. vm_refl. Qed.
Lemma D_5e2dc : decode_any W_5e2dc = Some (Branch BC_NE 12 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2e0 : bv 32 := 0x00000513.
Lemma F_5e2e0 : fetch_word Plain.M.loaded_segments (0x5e2e0 : word) = Some W_5e2e0.
Proof. vm_refl. Qed.
Lemma D_5e2e0 : decode_any W_5e2e0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2e4 : bv 32 := 0x00008067.
Lemma F_5e2e4 : fetch_word Plain.M.loaded_segments (0x5e2e4 : word) = Some W_5e2e4.
Proof. vm_refl. Qed.
Lemma D_5e2e4 : decode_any W_5e2e4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2e8 : bv 32 := 0x40e68533.
Lemma F_5e2e8 : fetch_word Plain.M.loaded_segments (0x5e2e8 : word) = Some W_5e2e8.
Proof. vm_refl. Qed.
Lemma D_5e2e8 : decode_any W_5e2e8 = Some (Op ALU_SUB 10 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2ec : bv 32 := 0x00008067.
Lemma F_5e2ec : fetch_word Plain.M.loaded_segments (0x5e2ec : word) = Some W_5e2ec.
Proof. vm_refl. Qed.
Lemma D_5e2ec : decode_any W_5e2ec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

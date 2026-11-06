(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.simdjson.fuzz_utf8.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_c3e6c : bv 32 := 0x0ff5f593.
Lemma F_c3e6c : fetch_word Plain.M.loaded_segments (0xc4024 : word) = Some W_c3e6c.
Proof. vm_refl. Qed.
Lemma D_c3e6c : decode_any W_c3e6c = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3e70 : bv 32 := 0x00757693.
Lemma F_c3e70 : fetch_word Plain.M.loaded_segments (0xc4028 : word) = Some W_c3e70.
Proof. vm_refl. Qed.
Lemma D_c3e70 : decode_any W_c3e70 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3e74 : bv 32 := 0x00c03733.
Lemma F_c3e74 : fetch_word Plain.M.loaded_segments (0xc402c : word) = Some W_c3e74.
Proof. vm_refl. Qed.
Lemma D_c3e74 : decode_any W_c3e74 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3e78 : bv 32 := 0x02068c63.
Lemma F_c3e78 : fetch_word Plain.M.loaded_segments (0xc4030 : word) = Some W_c3e78.
Proof. vm_refl. Qed.
Lemma D_c3e78 : decode_any W_c3e78 = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3e7c : bv 32 := 0x02060a63.
Lemma F_c3e7c : fetch_word Plain.M.loaded_segments (0xc4034 : word) = Some W_c3e7c.
Proof. vm_refl. Qed.
Lemma D_c3e7c : decode_any W_c3e7c = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3e80 : bv 32 := 0x00150793.
Lemma F_c3e80 : fetch_word Plain.M.loaded_segments (0xc4038 : word) = Some W_c3e80.
Proof. vm_refl. Qed.
Lemma D_c3e80 : decode_any W_c3e80 = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3e84 : bv 32 := 0x00100813.
Lemma F_c3e84 : fetch_word Plain.M.loaded_segments (0xc403c : word) = Some W_c3e84.
Proof. vm_refl. Qed.
Lemma D_c3e84 : decode_any W_c3e84 = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3e88 : bv 32 := 0x00054703.
Lemma F_c3e88 : fetch_word Plain.M.loaded_segments (0xc4040 : word) = Some W_c3e88.
Proof. vm_refl. Qed.
Lemma D_c3e88 : decode_any W_c3e88 = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3e8c : bv 32 := 0x00060693.
Lemma F_c3e8c : fetch_word Plain.M.loaded_segments (0xc4044 : word) = Some W_c3e8c.
Proof. vm_refl. Qed.
Lemma D_c3e8c : decode_any W_c3e8c = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3e90 : bv 32 := 0x06b70e63.
Lemma F_c3e90 : fetch_word Plain.M.loaded_segments (0xc4048 : word) = Some W_c3e90.
Proof. vm_refl. Qed.
Lemma D_c3e90 : decode_any W_c3e90 = Some (Branch BC_EQ 14 11 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3e94 : bv 32 := 0x00150513.
Lemma F_c3e94 : fetch_word Plain.M.loaded_segments (0xc404c : word) = Some W_c3e94.
Proof. vm_refl. Qed.
Lemma D_c3e94 : decode_any W_c3e94 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3e98 : bv 32 := 0xfff68613.
Lemma F_c3e98 : fetch_word Plain.M.loaded_segments (0xc4050 : word) = Some W_c3e98.
Proof. vm_refl. Qed.
Lemma D_c3e98 : decode_any W_c3e98 = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3e9c : bv 32 := 0x0077f893.
Lemma F_c3e9c : fetch_word Plain.M.loaded_segments (0xc4054 : word) = Some W_c3e9c.
Proof. vm_refl. Qed.
Lemma D_c3e9c : decode_any W_c3e9c = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3ea0 : bv 32 := 0x00c03733.
Lemma F_c3ea0 : fetch_word Plain.M.loaded_segments (0xc4058 : word) = Some W_c3ea0.
Proof. vm_refl. Qed.
Lemma D_c3ea0 : decode_any W_c3ea0 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3ea4 : bv 32 := 0x00088663.
Lemma F_c3ea4 : fetch_word Plain.M.loaded_segments (0xc405c : word) = Some W_c3ea4.
Proof. vm_refl. Qed.
Lemma D_c3ea4 : decode_any W_c3ea4 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3ea8 : bv 32 := 0x00178793.
Lemma F_c3ea8 : fetch_word Plain.M.loaded_segments (0xc4060 : word) = Some W_c3ea8.
Proof. vm_refl. Qed.
Lemma D_c3ea8 : decode_any W_c3ea8 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3eac : bv 32 := 0xfd069ee3.
Lemma F_c3eac : fetch_word Plain.M.loaded_segments (0xc4064 : word) = Some W_c3eac.
Proof. vm_refl. Qed.
Lemma D_c3eac : decode_any W_c3eac = Some (Branch BC_NE 13 16 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3eb0 : bv 32 := 0x06070863.
Lemma F_c3eb0 : fetch_word Plain.M.loaded_segments (0xc4068 : word) = Some W_c3eb0.
Proof. vm_refl. Qed.
Lemma D_c3eb0 : decode_any W_c3eb0 = Some (Branch BC_EQ 14 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3eb4 : bv 32 := 0x00054683.
Lemma F_c3eb4 : fetch_word Plain.M.loaded_segments (0xc406c : word) = Some W_c3eb4.
Proof. vm_refl. Qed.
Lemma D_c3eb4 : decode_any W_c3eb4 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3eb8 : bv 32 := 0x04b68663.
Lemma F_c3eb8 : fetch_word Plain.M.loaded_segments (0xc4070 : word) = Some W_c3eb8.
Proof. vm_refl. Qed.
Lemma D_c3eb8 : decode_any W_c3eb8 = Some (Branch BC_EQ 13 11 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3ebc : bv 32 := 0x00800693.
Lemma F_c3ebc : fetch_word Plain.M.loaded_segments (0xc4074 : word) = Some W_c3ebc.
Proof. vm_refl. Qed.
Lemma D_c3ebc : decode_any W_c3ebc = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3ec0 : bv 32 := 0x04d66263.
Lemma F_c3ec0 : fetch_word Plain.M.loaded_segments (0xc4078 : word) = Some W_c3ec0.
Proof. vm_refl. Qed.
Lemma D_c3ec0 : decode_any W_c3ec0 = Some (Branch BC_LTU 12 13 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3ec4 : bv 32 := 0xfff4f697.
Lemma F_c3ec4 : fetch_word Plain.M.loaded_segments (0xc407c : word) = Some W_c3ec4.
Proof. vm_refl. Qed.
Lemma D_c3ec4 : decode_any W_c3ec4 = Some (Auipc 13 1048399, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3ec8 : bv 32 := 0x4746b683.
Lemma F_c3ec8 : fetch_word Plain.M.loaded_segments (0xc4080 : word) = Some W_c3ec8.
Proof. vm_refl. Qed.
Lemma D_c3ec8 : decode_any W_c3ec8 = Some (Load SZ8 true 13 13 1140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3ecc : bv 32 := 0xfff4f717.
Lemma F_c3ecc : fetch_word Plain.M.loaded_segments (0xc4084 : word) = Some W_c3ecc.
Proof. vm_refl. Qed.
Lemma D_c3ecc : decode_any W_c3ecc = Some (Auipc 14 1048399, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3ed0 : bv 32 := 0x45473703.
Lemma F_c3ed0 : fetch_word Plain.M.loaded_segments (0xc4088 : word) = Some W_c3ed0.
Proof. vm_refl. Qed.
Lemma D_c3ed0 : decode_any W_c3ed0 = Some (Load SZ8 true 14 14 1108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3ed4 : bv 32 := 0x00168793.
Lemma F_c3ed4 : fetch_word Plain.M.loaded_segments (0xc408c : word) = Some W_c3ed4.
Proof. vm_refl. Qed.
Lemma D_c3ed4 : decode_any W_c3ed4 = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3ed8 : bv 32 := 0x02f587b3.
Lemma F_c3ed8 : fetch_word Plain.M.loaded_segments (0xc4090 : word) = Some W_c3ed8.
Proof. vm_refl. Qed.
Lemma D_c3ed8 : decode_any W_c3ed8 = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3edc : bv 32 := 0x00700813.
Lemma F_c3edc : fetch_word Plain.M.loaded_segments (0xc4094 : word) = Some W_c3edc.
Proof. vm_refl. Qed.
Lemma D_c3edc : decode_any W_c3edc = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3ee0 : bv 32 := 0x00053883.
Lemma F_c3ee0 : fetch_word Plain.M.loaded_segments (0xc4098 : word) = Some W_c3ee0.
Proof. vm_refl. Qed.
Lemma D_c3ee0 : decode_any W_c3ee0 = Some (Load SZ8 true 17 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3ee4 : bv 32 := 0x00f8c8b3.
Lemma F_c3ee4 : fetch_word Plain.M.loaded_segments (0xc409c : word) = Some W_c3ee4.
Proof. vm_refl. Qed.
Lemma D_c3ee4 : decode_any W_c3ee4 = Some (Op ALU_XOR 17 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3ee8 : bv 32 := 0x411682b3.
Lemma F_c3ee8 : fetch_word Plain.M.loaded_segments (0xc40a0 : word) = Some W_c3ee8.
Proof. vm_refl. Qed.
Lemma D_c3ee8 : decode_any W_c3ee8 = Some (Op ALU_SUB 5 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3eec : bv 32 := 0x0112e8b3.
Lemma F_c3eec : fetch_word Plain.M.loaded_segments (0xc40a4 : word) = Some W_c3eec.
Proof. vm_refl. Qed.
Lemma D_c3eec : decode_any W_c3eec = Some (Op ALU_OR 17 5 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3ef0 : bv 32 := 0x00e8f8b3.
Lemma F_c3ef0 : fetch_word Plain.M.loaded_segments (0xc40a8 : word) = Some W_c3ef0.
Proof. vm_refl. Qed.
Lemma D_c3ef0 : decode_any W_c3ef0 = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3ef4 : bv 32 := 0x02e89a63.
Lemma F_c3ef4 : fetch_word Plain.M.loaded_segments (0xc40ac : word) = Some W_c3ef4.
Proof. vm_refl. Qed.
Lemma D_c3ef4 : decode_any W_c3ef4 = Some (Branch BC_NE 17 14 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3ef8 : bv 32 := 0xff860613.
Lemma F_c3ef8 : fetch_word Plain.M.loaded_segments (0xc40b0 : word) = Some W_c3ef8.
Proof. vm_refl. Qed.
Lemma D_c3ef8 : decode_any W_c3ef8 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3efc : bv 32 := 0x00850513.
Lemma F_c3efc : fetch_word Plain.M.loaded_segments (0xc40b4 : word) = Some W_c3efc.
Proof. vm_refl. Qed.
Lemma D_c3efc : decode_any W_c3efc = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3f00 : bv 32 := 0xfec860e3.
Lemma F_c3f00 : fetch_word Plain.M.loaded_segments (0xc40b8 : word) = Some W_c3f00.
Proof. vm_refl. Qed.
Lemma D_c3f00 : decode_any W_c3f00 = Some (Branch BC_LTU 16 12 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3f04 : bv 32 := 0x00060693.
Lemma F_c3f04 : fetch_word Plain.M.loaded_segments (0xc40bc : word) = Some W_c3f04.
Proof. vm_refl. Qed.
Lemma D_c3f04 : decode_any W_c3f04 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3f08 : bv 32 := 0x00060c63.
Lemma F_c3f08 : fetch_word Plain.M.loaded_segments (0xc40c0 : word) = Some W_c3f08.
Proof. vm_refl. Qed.
Lemma D_c3f08 : decode_any W_c3f08 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3f0c : bv 32 := 0x00054603.
Lemma F_c3f0c : fetch_word Plain.M.loaded_segments (0xc40c4 : word) = Some W_c3f0c.
Proof. vm_refl. Qed.
Lemma D_c3f0c : decode_any W_c3f0c = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3f10 : bv 32 := 0x00b60a63.
Lemma F_c3f10 : fetch_word Plain.M.loaded_segments (0xc40c8 : word) = Some W_c3f10.
Proof. vm_refl. Qed.
Lemma D_c3f10 : decode_any W_c3f10 = Some (Branch BC_EQ 12 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3f14 : bv 32 := 0xfff68693.
Lemma F_c3f14 : fetch_word Plain.M.loaded_segments (0xc40cc : word) = Some W_c3f14.
Proof. vm_refl. Qed.
Lemma D_c3f14 : decode_any W_c3f14 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3f18 : bv 32 := 0x00150513.
Lemma F_c3f18 : fetch_word Plain.M.loaded_segments (0xc40d0 : word) = Some W_c3f18.
Proof. vm_refl. Qed.
Lemma D_c3f18 : decode_any W_c3f18 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3f1c : bv 32 := 0xfe0698e3.
Lemma F_c3f1c : fetch_word Plain.M.loaded_segments (0xc40d4 : word) = Some W_c3f1c.
Proof. vm_refl. Qed.
Lemma D_c3f1c : decode_any W_c3f1c = Some (Branch BC_NE 13 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3f20 : bv 32 := 0x00000513.
Lemma F_c3f20 : fetch_word Plain.M.loaded_segments (0xc40d8 : word) = Some W_c3f20.
Proof. vm_refl. Qed.
Lemma D_c3f20 : decode_any W_c3f20 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3f24 : bv 32 := 0x00008067.
Lemma F_c3f24 : fetch_word Plain.M.loaded_segments (0xc40dc : word) = Some W_c3f24.
Proof. vm_refl. Qed.
Lemma D_c3f24 : decode_any W_c3f24 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3f28 : bv 32 := 0x00060693.
Lemma F_c3f28 : fetch_word Plain.M.loaded_segments (0xc40e0 : word) = Some W_c3f28.
Proof. vm_refl. Qed.
Lemma D_c3f28 : decode_any W_c3f28 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3f2c : bv 32 := 0x00054603.
Lemma F_c3f2c : fetch_word Plain.M.loaded_segments (0xc40e4 : word) = Some W_c3f2c.
Proof. vm_refl. Qed.
Lemma D_c3f2c : decode_any W_c3f2c = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3f30 : bv 32 := 0xfeb612e3.
Lemma F_c3f30 : fetch_word Plain.M.loaded_segments (0xc40e8 : word) = Some W_c3f30.
Proof. vm_refl. Qed.
Lemma D_c3f30 : decode_any W_c3f30 = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c3f34 : bv 32 := 0xff1ff06f.
Lemma F_c3f34 : fetch_word Plain.M.loaded_segments (0xc40ec : word) = Some W_c3f34.
Proof. vm_refl. Qed.
Lemma D_c3f34 : decode_any W_c3f34 = Some (Jal 0 2097136, 4%Z).
Proof. vm_refl. Qed.

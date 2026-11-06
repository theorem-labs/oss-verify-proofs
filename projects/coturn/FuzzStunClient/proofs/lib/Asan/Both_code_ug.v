(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_41d28 : bv 32 := 0x000bb683.
Lemma F_41d28 : fetch_word AsanUbsan.M.loaded_segments (0x41d28 : word) = Some W_41d28.
Proof. vm_refl. Qed.
Lemma D_41d28 : decode_any W_41d28 = Some (Load SZ8 true 13 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41d2c : bv 32 := 0x00000593.
Lemma F_41d2c : fetch_word AsanUbsan.M.loaded_segments (0x41d2c : word) = Some W_41d2c.
Proof. vm_refl. Qed.
Lemma D_41d2c : decode_any W_41d2c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41d30 : bv 32 := 0x000680e7.
Lemma F_41d30 : fetch_word AsanUbsan.M.loaded_segments (0x41d30 : word) = Some W_41d30.
Proof. vm_refl. Qed.
Lemma D_41d30 : decode_any W_41d30 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41d34 : bv 32 := 0x038a3503.
Lemma F_41d34 : fetch_word AsanUbsan.M.loaded_segments (0x41d34 : word) = Some W_41d34.
Proof. vm_refl. Qed.
Lemma D_41d34 : decode_any W_41d34 = Some (Load SZ8 true 10 20 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41d38 : bv 32 := 0x00150593.
Lemma F_41d38 : fetch_word AsanUbsan.M.loaded_segments (0x41d38 : word) = Some W_41d38.
Proof. vm_refl. Qed.
Lemma D_41d38 : decode_any W_41d38 = Some (OpImm ALU_ADD 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41d3c : bv 32 := 0x0d25f263.
Lemma F_41d3c : fetch_word AsanUbsan.M.loaded_segments (0x41d3c : word) = Some W_41d3c.
Proof. vm_refl. Qed.
Lemma D_41d3c : decode_any W_41d3c = Some (Branch BC_GEU 11 18 196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41d40 : bv 32 := 0xfffd8d93.
Lemma F_41d40 : fetch_word AsanUbsan.M.loaded_segments (0x41d40 : word) = Some W_41d40.
Proof. vm_refl. Qed.
Lemma D_41d40 : decode_any W_41d40 = Some (OpImm ALU_ADD 27 27 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41d44 : bv 32 := 0x040a0a13.
Lemma F_41d44 : fetch_word AsanUbsan.M.loaded_segments (0x41d44 : word) = Some W_41d44.
Proof. vm_refl. Qed.
Lemma D_41d44 : decode_any W_41d44 = Some (OpImm ALU_ADD 20 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41d48 : bv 32 := 0x200d8463.
Lemma F_41d48 : fetch_word AsanUbsan.M.loaded_segments (0x41d48 : word) = Some W_41d48.
Proof. vm_refl. Qed.
Lemma D_41d48 : decode_any W_41d48 = Some (Branch BC_EQ 27 0 520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41d4c : bv 32 := 0x1d4190ef.
Lemma F_41d4c : fetch_word AsanUbsan.M.loaded_segments (0x41d4c : word) = Some W_41d4c.
Proof. vm_refl. Qed.
Lemma D_41d4c : decode_any W_41d4c = Some (Jal 1 102868, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41d50 : bv 32 := 0x34050a63.
Lemma F_41d50 : fetch_word AsanUbsan.M.loaded_segments (0x41d50 : word) = Some W_41d50.
Proof. vm_refl. Qed.
Lemma D_41d50 : decode_any W_41d50 = Some (Branch BC_EQ 10 0 852, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41d54 : bv 32 := 0x018ca503.
Lemma F_41d54 : fetch_word AsanUbsan.M.loaded_segments (0x41d54 : word) = Some W_41d54.
Proof. vm_refl. Qed.
Lemma D_41d54 : decode_any W_41d54 = Some (Load SZ4 true 10 25 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41d58 : bv 32 := 0x01254a63.
Lemma F_41d58 : fetch_word AsanUbsan.M.loaded_segments (0x41d58 : word) = Some W_41d58.
Proof. vm_refl. Qed.
Lemma D_41d58 : decode_any W_41d58 = Some (Branch BC_LT 10 18 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41d6c : bv 32 := 0x34050c63.
Lemma F_41d6c : fetch_word AsanUbsan.M.loaded_segments (0x41d6c : word) = Some W_41d6c.
Proof. vm_refl. Qed.
Lemma D_41d6c : decode_any W_41d6c = Some (Branch BC_EQ 10 0 856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41d70 : bv 32 := 0x000d3603.
Lemma F_41d70 : fetch_word AsanUbsan.M.loaded_segments (0x41d70 : word) = Some W_41d70.
Proof. vm_refl. Qed.
Lemma D_41d70 : decode_any W_41d70 = Some (Load SZ8 true 12 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41d74 : bv 32 := 0x000a3503.
Lemma F_41d74 : fetch_word AsanUbsan.M.loaded_segments (0x41d74 : word) = Some W_41d74.
Proof. vm_refl. Qed.
Lemma D_41d74 : decode_any W_41d74 = Some (Load SZ8 true 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41d78 : bv 32 := 0xfff60593.
Lemma F_41d78 : fetch_word AsanUbsan.M.loaded_segments (0x41d78 : word) = Some W_41d78.
Proof. vm_refl. Qed.
Lemma D_41d78 : decode_any W_41d78 = Some (OpImm ALU_ADD 11 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41d7c : bv 32 := 0x00b636b3.
Lemma F_41d7c : fetch_word AsanUbsan.M.loaded_segments (0x41d7c : word) = Some W_41d7c.
Proof. vm_refl. Qed.
Lemma D_41d7c : decode_any W_41d7c = Some (Op ALU_SLTU 13 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41d80 : bv 32 := 0xfff68693.
Lemma F_41d80 : fetch_word AsanUbsan.M.loaded_segments (0x41d80 : word) = Some W_41d80.
Proof. vm_refl. Qed.
Lemma D_41d80 : decode_any W_41d80 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41d84 : bv 32 := 0x00b6f6b3.
Lemma F_41d84 : fetch_word AsanUbsan.M.loaded_segments (0x41d84 : word) = Some W_41d84.
Proof. vm_refl. Qed.
Lemma D_41d84 : decode_any W_41d84 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41d88 : bv 32 := 0x0ea6f263.
Lemma F_41d88 : fetch_word AsanUbsan.M.loaded_segments (0x41d88 : word) = Some W_41d88.
Proof. vm_refl. Qed.
Lemma D_41d88 : decode_any W_41d88 = Some (Branch BC_GEU 13 10 228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41e6c : bv 32 := 0x00757513.
Lemma F_41e6c : fetch_word AsanUbsan.M.loaded_segments (0x41e6c : word) = Some W_41e6c.
Proof. vm_refl. Qed.
Lemma D_41e6c : decode_any W_41e6c = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41e70 : bv 32 := 0x28051a63.
Lemma F_41e70 : fetch_word AsanUbsan.M.loaded_segments (0x41e70 : word) = Some W_41e70.
Proof. vm_refl. Qed.
Lemma D_41e70 : decode_any W_41e70 = Some (Branch BC_NE 10 0 660, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41e74 : bv 32 := 0x010a4503.
Lemma F_41e74 : fetch_word AsanUbsan.M.loaded_segments (0x41e74 : word) = Some W_41e74.
Proof. vm_refl. Qed.
Lemma D_41e74 : decode_any W_41e74 = Some (Load SZ1 false 10 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41e78 : bv 32 := 0x00757513.
Lemma F_41e78 : fetch_word AsanUbsan.M.loaded_segments (0x41e78 : word) = Some W_41e78.
Proof. vm_refl. Qed.
Lemma D_41e78 : decode_any W_41e78 = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41e7c : bv 32 := 0x2a051463.
Lemma F_41e7c : fetch_word AsanUbsan.M.loaded_segments (0x41e7c : word) = Some W_41e7c.
Proof. vm_refl. Qed.
Lemma D_41e7c : decode_any W_41e7c = Some (Branch BC_NE 10 0 680, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41e80 : bv 32 := 0x180140ef.
Lemma F_41e80 : fetch_word AsanUbsan.M.loaded_segments (0x41e80 : word) = Some W_41e80.
Proof. vm_refl. Qed.
Lemma D_41e80 : decode_any W_41e80 = Some (Jal 1 82304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41e84 : bv 32 := 0xea0508e3.
Lemma F_41e84 : fetch_word AsanUbsan.M.loaded_segments (0x41e84 : word) = Some W_41e84.
Proof. vm_refl. Qed.
Lemma D_41e84 : decode_any W_41e84 = Some (Branch BC_EQ 10 0 7856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41e88 : bv 32 := 0x000a3503.
Lemma F_41e88 : fetch_word AsanUbsan.M.loaded_segments (0x41e88 : word) = Some W_41e88.
Proof. vm_refl. Qed.
Lemma D_41e88 : decode_any W_41e88 = Some (Load SZ8 true 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41e8c : bv 32 := 0x010a3583.
Lemma F_41e8c : fetch_word AsanUbsan.M.loaded_segments (0x41e8c : word) = Some W_41e8c.
Proof. vm_refl. Qed.
Lemma D_41e8c : decode_any W_41e8c = Some (Load SZ8 true 11 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41e90 : bv 32 := 0x000d3603.
Lemma F_41e90 : fetch_word AsanUbsan.M.loaded_segments (0x41e90 : word) = Some W_41e90.
Proof. vm_refl. Qed.
Lemma D_41e90 : decode_any W_41e90 = Some (Load SZ8 true 12 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41e94 : bv 32 := 0x00355693.
Lemma F_41e94 : fetch_word AsanUbsan.M.loaded_segments (0x41e94 : word) = Some W_41e94.
Proof. vm_refl. Qed.
Lemma D_41e94 : decode_any W_41e94 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41e98 : bv 32 := 0x00b505b3.
Lemma F_41e98 : fetch_word AsanUbsan.M.loaded_segments (0x41e98 : word) = Some W_41e98.
Proof. vm_refl. Qed.
Lemma D_41e98 : decode_any W_41e98 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41e9c : bv 32 := 0x00d60533.
Lemma F_41e9c : fetch_word AsanUbsan.M.loaded_segments (0x41e9c : word) = Some W_41e9c.
Proof. vm_refl. Qed.
Lemma D_41e9c : decode_any W_41e9c = Some (Op ALU_ADD 10 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41ea0 : bv 32 := 0xff858593.
Lemma F_41ea0 : fetch_word AsanUbsan.M.loaded_segments (0x41ea0 : word) = Some W_41ea0.
Proof. vm_refl. Qed.
Lemma D_41ea0 : decode_any W_41ea0 = Some (OpImm ALU_ADD 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41ea4 : bv 32 := 0x0035d593.
Lemma F_41ea4 : fetch_word AsanUbsan.M.loaded_segments (0x41ea4 : word) = Some W_41ea4.
Proof. vm_refl. Qed.
Lemma D_41ea4 : decode_any W_41ea4 = Some (ShiftImm ALU_SRL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41ea8 : bv 32 := 0x0784b683.
Lemma F_41ea8 : fetch_word AsanUbsan.M.loaded_segments (0x41ea8 : word) = Some W_41ea8.
Proof. vm_refl. Qed.
Lemma D_41ea8 : decode_any W_41ea8 = Some (Load SZ8 true 13 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41eac : bv 32 := 0x00b605b3.
Lemma F_41eac : fetch_word AsanUbsan.M.loaded_segments (0x41eac : word) = Some W_41eac.
Proof. vm_refl. Qed.
Lemma D_41eac : decode_any W_41eac = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41eb0 : bv 32 := 0x00158413.
Lemma F_41eb0 : fetch_word AsanUbsan.M.loaded_segments (0x41eb0 : word) = Some W_41eb0.
Proof. vm_refl. Qed.
Lemma D_41eb0 : decode_any W_41eb0 = Some (OpImm ALU_ADD 8 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41eb4 : bv 32 := 0x40a40633.
Lemma F_41eb4 : fetch_word AsanUbsan.M.loaded_segments (0x41eb4 : word) = Some W_41eb4.
Proof. vm_refl. Qed.
Lemma D_41eb4 : decode_any W_41eb4 = Some (Op ALU_SUB 12 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_41eb8 : bv 32 := 0xe6d668e3.
Lemma F_41eb8 : fetch_word AsanUbsan.M.loaded_segments (0x41eb8 : word) = Some W_41eb8.
Proof. vm_refl. Qed.
Lemma D_41eb8 : decode_any W_41eb8 = Some (Branch BC_LTU 12 13 7792, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5af20 : bv 32 := 0x00058517.
Lemma F_5af20 : fetch_word AsanUbsan.M.loaded_segments (0x5af20 : word) = Some W_5af20.
Proof. vm_refl. Qed.
Lemma D_5af20 : decode_any W_5af20 = Some (Auipc 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5af24 : bv 32 := 0x97850503.
Lemma F_5af24 : fetch_word AsanUbsan.M.loaded_segments (0x5af24 : word) = Some W_5af24.
Proof. vm_refl. Qed.
Lemma D_5af24 : decode_any W_5af24 = Some (Load SZ1 true 10 10 2424, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5af28 : bv 32 := 0x0230000f.
Lemma F_5af28 : fetch_word AsanUbsan.M.loaded_segments (0x5af28 : word) = Some W_5af28.
Proof. vm_refl. Qed.
Lemma D_5af28 : decode_any W_5af28 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5af2c : bv 32 := 0xfff50513.
Lemma F_5af2c : fetch_word AsanUbsan.M.loaded_segments (0x5af2c : word) = Some W_5af2c.
Proof. vm_refl. Qed.
Lemma D_5af2c : decode_any W_5af2c = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5af30 : bv 32 := 0x00153513.
Lemma F_5af30 : fetch_word AsanUbsan.M.loaded_segments (0x5af30 : word) = Some W_5af30.
Proof. vm_refl. Qed.
Lemma D_5af30 : decode_any W_5af30 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5af34 : bv 32 := 0x00008067.
Lemma F_5af34 : fetch_word AsanUbsan.M.loaded_segments (0x5af34 : word) = Some W_5af34.
Proof. vm_refl. Qed.
Lemma D_5af34 : decode_any W_5af34 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

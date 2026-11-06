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

Definition W_96d28 : bv 32 := 0xfe010113.
Lemma F_96d28 : fetch_word AsanUbsan.M.loaded_segments (0x96d78 : word) = Some W_96d28.
Proof. vm_refl. Qed.
Lemma D_96d28 : decode_any W_96d28 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_96d2c : bv 32 := 0x00113c23.
Lemma F_96d2c : fetch_word AsanUbsan.M.loaded_segments (0x96d7c : word) = Some W_96d2c.
Proof. vm_refl. Qed.
Lemma D_96d2c : decode_any W_96d2c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_96d30 : bv 32 := 0x00813823.
Lemma F_96d30 : fetch_word AsanUbsan.M.loaded_segments (0x96d80 : word) = Some W_96d30.
Proof. vm_refl. Qed.
Lemma D_96d30 : decode_any W_96d30 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_96d34 : bv 32 := 0x00913423.
Lemma F_96d34 : fetch_word AsanUbsan.M.loaded_segments (0x96d84 : word) = Some W_96d34.
Proof. vm_refl. Qed.
Lemma D_96d34 : decode_any W_96d34 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_96d38 : bv 32 := 0x01213023.
Lemma F_96d38 : fetch_word AsanUbsan.M.loaded_segments (0x96d88 : word) = Some W_96d38.
Proof. vm_refl. Qed.
Lemma D_96d38 : decode_any W_96d38 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_96d3c : bv 32 := 0x00060413.
Lemma F_96d3c : fetch_word AsanUbsan.M.loaded_segments (0x96d8c : word) = Some W_96d3c.
Proof. vm_refl. Qed.
Lemma D_96d3c : decode_any W_96d3c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_96d40 : bv 32 := 0x00058493.
Lemma F_96d40 : fetch_word AsanUbsan.M.loaded_segments (0x96d90 : word) = Some W_96d40.
Proof. vm_refl. Qed.
Lemma D_96d40 : decode_any W_96d40 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_96d44 : bv 32 := 0x00058513.
Lemma F_96d44 : fetch_word AsanUbsan.M.loaded_segments (0x96d94 : word) = Some W_96d44.
Proof. vm_refl. Qed.
Lemma D_96d44 : decode_any W_96d44 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_96d48 : bv 32 := 0x00060593.
Lemma F_96d48 : fetch_word AsanUbsan.M.loaded_segments (0x96d98 : word) = Some W_96d48.
Proof. vm_refl. Qed.
Lemma D_96d48 : decode_any W_96d48 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_96d4c : bv 32 := 0x00068613.
Lemma F_96d4c : fetch_word AsanUbsan.M.loaded_segments (0x96d9c : word) = Some W_96d4c.
Proof. vm_refl. Qed.
Lemma D_96d4c : decode_any W_96d4c = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_96d50 : bv 32 := 0xf19f70ef.
Lemma F_96d50 : fetch_word AsanUbsan.M.loaded_segments (0x96da0 : word) = Some W_96d50.
Proof. vm_refl. Qed.
Lemma D_96d50 : decode_any W_96d50 = Some (Jal 1 2064152, 4%Z).
Proof. vm_refl. Qed.

Definition W_96d54 : bv 32 := 0x00050e63.
Lemma F_96d54 : fetch_word AsanUbsan.M.loaded_segments (0x96da4 : word) = Some W_96d54.
Proof. vm_refl. Qed.
Lemma D_96d54 : decode_any W_96d54 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_96d58 : bv 32 := 0x01813083.
Lemma F_96d58 : fetch_word AsanUbsan.M.loaded_segments (0x96da8 : word) = Some W_96d58.
Proof. vm_refl. Qed.
Lemma D_96d58 : decode_any W_96d58 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_96d5c : bv 32 := 0x01013403.
Lemma F_96d5c : fetch_word AsanUbsan.M.loaded_segments (0x96dac : word) = Some W_96d5c.
Proof. vm_refl. Qed.
Lemma D_96d5c : decode_any W_96d5c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_96d60 : bv 32 := 0x00813483.
Lemma F_96d60 : fetch_word AsanUbsan.M.loaded_segments (0x96db0 : word) = Some W_96d60.
Proof. vm_refl. Qed.
Lemma D_96d60 : decode_any W_96d60 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_96d64 : bv 32 := 0x00013903.
Lemma F_96d64 : fetch_word AsanUbsan.M.loaded_segments (0x96db4 : word) = Some W_96d64.
Proof. vm_refl. Qed.
Lemma D_96d64 : decode_any W_96d64 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_96d68 : bv 32 := 0x02010113.
Lemma F_96d68 : fetch_word AsanUbsan.M.loaded_segments (0x96db8 : word) = Some W_96d68.
Proof. vm_refl. Qed.
Lemma D_96d68 : decode_any W_96d68 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_96d6c : bv 32 := 0x00008067.
Lemma F_96d6c : fetch_word AsanUbsan.M.loaded_segments (0x96dbc : word) = Some W_96d6c.
Proof. vm_refl. Qed.
Lemma D_96d6c : decode_any W_96d6c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_96d70 : bv 32 := 0x00050913.
Lemma F_96d70 : fetch_word AsanUbsan.M.loaded_segments (0x96dc0 : word) = Some W_96d70.
Proof. vm_refl. Qed.
Lemma D_96d70 : decode_any W_96d70 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_96d74 : bv 32 := 0x00048513.
Lemma F_96d74 : fetch_word AsanUbsan.M.loaded_segments (0x96dc4 : word) = Some W_96d74.
Proof. vm_refl. Qed.
Lemma D_96d74 : decode_any W_96d74 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_96d78 : bv 32 := 0x00040593.
Lemma F_96d78 : fetch_word AsanUbsan.M.loaded_segments (0x96dc8 : word) = Some W_96d78.
Proof. vm_refl. Qed.
Lemma D_96d78 : decode_any W_96d78 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_96d7c : bv 32 := 0x020000ef.
Lemma F_96d7c : fetch_word AsanUbsan.M.loaded_segments (0x96dcc : word) = Some W_96d7c.
Proof. vm_refl. Qed.
Lemma D_96d7c : decode_any W_96d7c = Some (Jal 1 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_96d80 : bv 32 := 0x00090513.
Lemma F_96d80 : fetch_word AsanUbsan.M.loaded_segments (0x96dd0 : word) = Some W_96d80.
Proof. vm_refl. Qed.
Lemma D_96d80 : decode_any W_96d80 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_96d84 : bv 32 := 0x01813083.
Lemma F_96d84 : fetch_word AsanUbsan.M.loaded_segments (0x96dd4 : word) = Some W_96d84.
Proof. vm_refl. Qed.
Lemma D_96d84 : decode_any W_96d84 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_96d88 : bv 32 := 0x01013403.
Lemma F_96d88 : fetch_word AsanUbsan.M.loaded_segments (0x96dd8 : word) = Some W_96d88.
Proof. vm_refl. Qed.
Lemma D_96d88 : decode_any W_96d88 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_96d8c : bv 32 := 0x00813483.
Lemma F_96d8c : fetch_word AsanUbsan.M.loaded_segments (0x96ddc : word) = Some W_96d8c.
Proof. vm_refl. Qed.
Lemma D_96d8c : decode_any W_96d8c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_96d90 : bv 32 := 0x00013903.
Lemma F_96d90 : fetch_word AsanUbsan.M.loaded_segments (0x96de0 : word) = Some W_96d90.
Proof. vm_refl. Qed.
Lemma D_96d90 : decode_any W_96d90 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_96d94 : bv 32 := 0x02010113.
Lemma F_96d94 : fetch_word AsanUbsan.M.loaded_segments (0x96de4 : word) = Some W_96d94.
Proof. vm_refl. Qed.
Lemma D_96d94 : decode_any W_96d94 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_96d98 : bv 32 := 0x00008067.
Lemma F_96d98 : fetch_word AsanUbsan.M.loaded_segments (0x96de8 : word) = Some W_96d98.
Proof. vm_refl. Qed.
Lemma D_96d98 : decode_any W_96d98 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

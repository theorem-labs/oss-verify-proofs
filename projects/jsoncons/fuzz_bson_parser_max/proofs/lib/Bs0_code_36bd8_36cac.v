(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_36c7c : bv 32 := 0x001a9a93.
Lemma F_36c7c : fetch_word Plain.M.loaded_segments (0x36cd4 : word) = Some W_36c7c.
Proof. vm_refl. Qed.
Lemma D_36c7c : decode_any W_36c7c = Some (ShiftImm ALU_SLL 21 21 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36c80 : bv 32 := 0xfffdd617.
Lemma F_36c80 : fetch_word Plain.M.loaded_segments (0x36cd8 : word) = Some W_36c80.
Proof. vm_refl. Qed.
Lemma D_36c80 : decode_any W_36c80 = Some (Auipc 12 1048541, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36c84 : bv 32 := 0xd5860613.
Lemma F_36c84 : fetch_word Plain.M.loaded_segments (0x36cdc : word) = Some W_36c84.
Proof. vm_refl. Qed.
Lemma D_36c84 : decode_any W_36c84 = Some (OpImm ALU_ADD 12 12 3416, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36c88 : bv 32 := 0x01560ab3.
Lemma F_36c88 : fetch_word Plain.M.loaded_segments (0x36ce0 : word) = Some W_36c88.
Proof. vm_refl. Qed.
Lemma D_36c88 : decode_any W_36c88 = Some (Op ALU_ADD 21 12 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36c8c : bv 32 := 0x000a9683.
Lemma F_36c8c : fetch_word Plain.M.loaded_segments (0x36ce4 : word) = Some W_36c8c.
Proof. vm_refl. Qed.
Lemma D_36c8c : decode_any W_36c8c = Some (Load SZ2 true 13 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36c90 : bv 32 := 0x001a1a13.
Lemma F_36c90 : fetch_word Plain.M.loaded_segments (0x36ce8 : word) = Some W_36c90.
Proof. vm_refl. Qed.
Lemma D_36c90 : decode_any W_36c90 = Some (ShiftImm ALU_SLL 20 20 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36c94 : bv 32 := 0x01460a33.
Lemma F_36c94 : fetch_word Plain.M.loaded_segments (0x36cec : word) = Some W_36c94.
Proof. vm_refl. Qed.
Lemma D_36c94 : decode_any W_36c94 = Some (Op ALU_ADD 20 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36c98 : bv 32 := 0x00d59023.
Lemma F_36c98 : fetch_word Plain.M.loaded_segments (0x36cf0 : word) = Some W_36c98.
Proof. vm_refl. Qed.
Lemma D_36c98 : decode_any W_36c98 = Some (Store SZ2 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36c9c : bv 32 := 0x000a1683.
Lemma F_36c9c : fetch_word Plain.M.loaded_segments (0x36cf4 : word) = Some W_36c9c.
Proof. vm_refl. Qed.
Lemma D_36c9c : decode_any W_36c9c = Some (Load SZ2 true 13 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36ca0 : bv 32 := 0x00199993.
Lemma F_36ca0 : fetch_word Plain.M.loaded_segments (0x36cf8 : word) = Some W_36ca0.
Proof. vm_refl. Qed.
Lemma D_36ca0 : decode_any W_36ca0 = Some (ShiftImm ALU_SLL 19 19 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36ca4 : bv 32 := 0x013609b3.
Lemma F_36ca4 : fetch_word Plain.M.loaded_segments (0x36cfc : word) = Some W_36ca4.
Proof. vm_refl. Qed.
Lemma D_36ca4 : decode_any W_36ca4 = Some (Op ALU_ADD 19 12 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36ca8 : bv 32 := 0x00d59123.
Lemma F_36ca8 : fetch_word Plain.M.loaded_segments (0x36d00 : word) = Some W_36ca8.
Proof. vm_refl. Qed.
Lemma D_36ca8 : decode_any W_36ca8 = Some (Store SZ2 11 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36cac : bv 32 := 0x00099683.
Lemma F_36cac : fetch_word Plain.M.loaded_segments (0x36d04 : word) = Some W_36cac.
Proof. vm_refl. Qed.
Lemma D_36cac : decode_any W_36cac = Some (Load SZ2 true 13 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36cb0 : bv 32 := 0x001d9d93.
Lemma F_36cb0 : fetch_word Plain.M.loaded_segments (0x36d08 : word) = Some W_36cb0.
Proof. vm_refl. Qed.
Lemma D_36cb0 : decode_any W_36cb0 = Some (ShiftImm ALU_SLL 27 27 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36cb4 : bv 32 := 0x01b60db3.
Lemma F_36cb4 : fetch_word Plain.M.loaded_segments (0x36d0c : word) = Some W_36cb4.
Proof. vm_refl. Qed.
Lemma D_36cb4 : decode_any W_36cb4 = Some (Op ALU_ADD 27 12 27, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36cb8 : bv 32 := 0x00d59223.
Lemma F_36cb8 : fetch_word Plain.M.loaded_segments (0x36d10 : word) = Some W_36cb8.
Proof. vm_refl. Qed.
Lemma D_36cb8 : decode_any W_36cb8 = Some (Store SZ2 11 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36cbc : bv 32 := 0x000d9683.
Lemma F_36cbc : fetch_word Plain.M.loaded_segments (0x36d14 : word) = Some W_36cbc.
Proof. vm_refl. Qed.
Lemma D_36cbc : decode_any W_36cbc = Some (Load SZ2 true 13 27 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36cc0 : bv 32 := 0x001d1d13.
Lemma F_36cc0 : fetch_word Plain.M.loaded_segments (0x36d18 : word) = Some W_36cc0.
Proof. vm_refl. Qed.
Lemma D_36cc0 : decode_any W_36cc0 = Some (ShiftImm ALU_SLL 26 26 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36cc4 : bv 32 := 0x01a60d33.
Lemma F_36cc4 : fetch_word Plain.M.loaded_segments (0x36d1c : word) = Some W_36cc4.
Proof. vm_refl. Qed.
Lemma D_36cc4 : decode_any W_36cc4 = Some (Op ALU_ADD 26 12 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36cc8 : bv 32 := 0x00d59323.
Lemma F_36cc8 : fetch_word Plain.M.loaded_segments (0x36d20 : word) = Some W_36cc8.
Proof. vm_refl. Qed.
Lemma D_36cc8 : decode_any W_36cc8 = Some (Store SZ2 11 13 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36ccc : bv 32 := 0x000d1683.
Lemma F_36ccc : fetch_word Plain.M.loaded_segments (0x36d24 : word) = Some W_36ccc.
Proof. vm_refl. Qed.
Lemma D_36ccc : decode_any W_36ccc = Some (Load SZ2 true 13 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36cd0 : bv 32 := 0x001c9c93.
Lemma F_36cd0 : fetch_word Plain.M.loaded_segments (0x36d28 : word) = Some W_36cd0.
Proof. vm_refl. Qed.
Lemma D_36cd0 : decode_any W_36cd0 = Some (ShiftImm ALU_SLL 25 25 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36cd4 : bv 32 := 0x01960cb3.
Lemma F_36cd4 : fetch_word Plain.M.loaded_segments (0x36d2c : word) = Some W_36cd4.
Proof. vm_refl. Qed.
Lemma D_36cd4 : decode_any W_36cd4 = Some (Op ALU_ADD 25 12 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36cd8 : bv 32 := 0x00d59423.
Lemma F_36cd8 : fetch_word Plain.M.loaded_segments (0x36d30 : word) = Some W_36cd8.
Proof. vm_refl. Qed.
Lemma D_36cd8 : decode_any W_36cd8 = Some (Store SZ2 11 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36cdc : bv 32 := 0x000c9683.
Lemma F_36cdc : fetch_word Plain.M.loaded_segments (0x36d34 : word) = Some W_36cdc.
Proof. vm_refl. Qed.
Lemma D_36cdc : decode_any W_36cdc = Some (Load SZ2 true 13 25 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36ce0 : bv 32 := 0x001c1c13.
Lemma F_36ce0 : fetch_word Plain.M.loaded_segments (0x36d38 : word) = Some W_36ce0.
Proof. vm_refl. Qed.
Lemma D_36ce0 : decode_any W_36ce0 = Some (ShiftImm ALU_SLL 24 24 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36ce4 : bv 32 := 0x01860c33.
Lemma F_36ce4 : fetch_word Plain.M.loaded_segments (0x36d3c : word) = Some W_36ce4.
Proof. vm_refl. Qed.
Lemma D_36ce4 : decode_any W_36ce4 = Some (Op ALU_ADD 24 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36ce8 : bv 32 := 0x00d59523.
Lemma F_36ce8 : fetch_word Plain.M.loaded_segments (0x36d40 : word) = Some W_36ce8.
Proof. vm_refl. Qed.
Lemma D_36ce8 : decode_any W_36ce8 = Some (Store SZ2 11 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36cec : bv 32 := 0x000c1683.
Lemma F_36cec : fetch_word Plain.M.loaded_segments (0x36d44 : word) = Some W_36cec.
Proof. vm_refl. Qed.
Lemma D_36cec : decode_any W_36cec = Some (Load SZ2 true 13 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36cf0 : bv 32 := 0x001b9b93.
Lemma F_36cf0 : fetch_word Plain.M.loaded_segments (0x36d48 : word) = Some W_36cf0.
Proof. vm_refl. Qed.
Lemma D_36cf0 : decode_any W_36cf0 = Some (ShiftImm ALU_SLL 23 23 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36cf4 : bv 32 := 0x01760bb3.
Lemma F_36cf4 : fetch_word Plain.M.loaded_segments (0x36d4c : word) = Some W_36cf4.
Proof. vm_refl. Qed.
Lemma D_36cf4 : decode_any W_36cf4 = Some (Op ALU_ADD 23 12 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36cf8 : bv 32 := 0x00d59623.
Lemma F_36cf8 : fetch_word Plain.M.loaded_segments (0x36d50 : word) = Some W_36cf8.
Proof. vm_refl. Qed.
Lemma D_36cf8 : decode_any W_36cf8 = Some (Store SZ2 11 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36cfc : bv 32 := 0x000b9683.
Lemma F_36cfc : fetch_word Plain.M.loaded_segments (0x36d54 : word) = Some W_36cfc.
Proof. vm_refl. Qed.
Lemma D_36cfc : decode_any W_36cfc = Some (Load SZ2 true 13 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36d00 : bv 32 := 0x001b1b13.
Lemma F_36d00 : fetch_word Plain.M.loaded_segments (0x36d58 : word) = Some W_36d00.
Proof. vm_refl. Qed.
Lemma D_36d00 : decode_any W_36d00 = Some (ShiftImm ALU_SLL 22 22 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36d04 : bv 32 := 0x01660b33.
Lemma F_36d04 : fetch_word Plain.M.loaded_segments (0x36d5c : word) = Some W_36d04.
Proof. vm_refl. Qed.
Lemma D_36d04 : decode_any W_36d04 = Some (Op ALU_ADD 22 12 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36d08 : bv 32 := 0x00d59723.
Lemma F_36d08 : fetch_word Plain.M.loaded_segments (0x36d60 : word) = Some W_36d08.
Proof. vm_refl. Qed.
Lemma D_36d08 : decode_any W_36d08 = Some (Store SZ2 11 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36d0c : bv 32 := 0x000b1683.
Lemma F_36d0c : fetch_word Plain.M.loaded_segments (0x36d64 : word) = Some W_36d0c.
Proof. vm_refl. Qed.
Lemma D_36d0c : decode_any W_36d0c = Some (Load SZ2 true 13 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36d10 : bv 32 := 0x00013703.
Lemma F_36d10 : fetch_word Plain.M.loaded_segments (0x36d68 : word) = Some W_36d10.
Proof. vm_refl. Qed.
Lemma D_36d10 : decode_any W_36d10 = Some (Load SZ8 true 14 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36d14 : bv 32 := 0x00171713.
Lemma F_36d14 : fetch_word Plain.M.loaded_segments (0x36d6c : word) = Some W_36d14.
Proof. vm_refl. Qed.
Lemma D_36d14 : decode_any W_36d14 = Some (ShiftImm ALU_SLL 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36d18 : bv 32 := 0x00e60733.
Lemma F_36d18 : fetch_word Plain.M.loaded_segments (0x36d70 : word) = Some W_36d18.
Proof. vm_refl. Qed.
Lemma D_36d18 : decode_any W_36d18 = Some (Op ALU_ADD 14 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36d1c : bv 32 := 0x00d59823.
Lemma F_36d1c : fetch_word Plain.M.loaded_segments (0x36d74 : word) = Some W_36d1c.
Proof. vm_refl. Qed.
Lemma D_36d1c : decode_any W_36d1c = Some (Store SZ2 11 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36d20 : bv 32 := 0x00071683.
Lemma F_36d20 : fetch_word Plain.M.loaded_segments (0x36d78 : word) = Some W_36d20.
Proof. vm_refl. Qed.
Lemma D_36d20 : decode_any W_36d20 = Some (Load SZ2 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36d24 : bv 32 := 0x00813703.
Lemma F_36d24 : fetch_word Plain.M.loaded_segments (0x36d7c : word) = Some W_36d24.
Proof. vm_refl. Qed.
Lemma D_36d24 : decode_any W_36d24 = Some (Load SZ8 true 14 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36d28 : bv 32 := 0x00171713.
Lemma F_36d28 : fetch_word Plain.M.loaded_segments (0x36d80 : word) = Some W_36d28.
Proof. vm_refl. Qed.
Lemma D_36d28 : decode_any W_36d28 = Some (ShiftImm ALU_SLL 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36d2c : bv 32 := 0x00e60733.
Lemma F_36d2c : fetch_word Plain.M.loaded_segments (0x36d84 : word) = Some W_36d2c.
Proof. vm_refl. Qed.
Lemma D_36d2c : decode_any W_36d2c = Some (Op ALU_ADD 14 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36d30 : bv 32 := 0x00d59923.
Lemma F_36d30 : fetch_word Plain.M.loaded_segments (0x36d88 : word) = Some W_36d30.
Proof. vm_refl. Qed.
Lemma D_36d30 : decode_any W_36d30 = Some (Store SZ2 11 13 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36d34 : bv 32 := 0x00071683.
Lemma F_36d34 : fetch_word Plain.M.loaded_segments (0x36d8c : word) = Some W_36d34.
Proof. vm_refl. Qed.
Lemma D_36d34 : decode_any W_36d34 = Some (Load SZ2 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36d38 : bv 32 := 0x01013703.
Lemma F_36d38 : fetch_word Plain.M.loaded_segments (0x36d90 : word) = Some W_36d38.
Proof. vm_refl. Qed.
Lemma D_36d38 : decode_any W_36d38 = Some (Load SZ8 true 14 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36d3c : bv 32 := 0x00171713.
Lemma F_36d3c : fetch_word Plain.M.loaded_segments (0x36d94 : word) = Some W_36d3c.
Proof. vm_refl. Qed.
Lemma D_36d3c : decode_any W_36d3c = Some (ShiftImm ALU_SLL 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36d40 : bv 32 := 0x00d59a23.
Lemma F_36d40 : fetch_word Plain.M.loaded_segments (0x36d98 : word) = Some W_36d40.
Proof. vm_refl. Qed.
Lemma D_36d40 : decode_any W_36d40 = Some (Store SZ2 11 13 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36d44 : bv 32 := 0x00e60633.
Lemma F_36d44 : fetch_word Plain.M.loaded_segments (0x36d9c : word) = Some W_36d44.
Proof. vm_refl. Qed.
Lemma D_36d44 : decode_any W_36d44 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36d48 : bv 32 := 0x00061603.
Lemma F_36d48 : fetch_word Plain.M.loaded_segments (0x36da0 : word) = Some W_36d48.
Proof. vm_refl. Qed.
Lemma D_36d48 : decode_any W_36d48 = Some (Load SZ2 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_36d4c : bv 32 := 0x00c59b23.
Lemma F_36d4c : fetch_word Plain.M.loaded_segments (0x36da4 : word) = Some W_36d4c.
Proof. vm_refl. Qed.
Lemma D_36d4c : decode_any W_36d4c = Some (Store SZ2 11 12 22, 4%Z).
Proof. vm_refl. Qed.

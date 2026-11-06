(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_93c54 : bv 32 := 0x00155593.
Lemma F_93c54 : fetch_word Asan.M.loaded_segments (0x93ca4 : word) = Some W_93c54.
Proof. vm_refl. Qed.
Lemma D_93c54 : decode_any W_93c54 = Some (ShiftImm ALU_SRL 11 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_93c58 : bv 32 := 0x55555637.
Lemma F_93c58 : fetch_word Asan.M.loaded_segments (0x93ca8 : word) = Some W_93c58.
Proof. vm_refl. Qed.
Lemma D_93c58 : decode_any W_93c58 = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

Definition W_93c5c : bv 32 := 0x333336b7.
Lemma F_93c5c : fetch_word Asan.M.loaded_segments (0x93cac : word) = Some W_93c5c.
Proof. vm_refl. Qed.
Lemma D_93c5c : decode_any W_93c5c = Some (Lui 13 209715, 4%Z).
Proof. vm_refl. Qed.

Definition W_93c60 : bv 32 := 0x0f0f1737.
Lemma F_93c60 : fetch_word Asan.M.loaded_segments (0x93cb0 : word) = Some W_93c60.
Proof. vm_refl. Qed.
Lemma D_93c60 : decode_any W_93c60 = Some (Lui 14 61681, 4%Z).
Proof. vm_refl. Qed.

Definition W_93c64 : bv 32 := 0x010107b7.
Lemma F_93c64 : fetch_word Asan.M.loaded_segments (0x93cb4 : word) = Some W_93c64.
Proof. vm_refl. Qed.
Lemma D_93c64 : decode_any W_93c64 = Some (Lui 15 4112, 4%Z).
Proof. vm_refl. Qed.

Definition W_93c68 : bv 32 := 0x00b56533.
Lemma F_93c68 : fetch_word Asan.M.loaded_segments (0x93cb8 : word) = Some W_93c68.
Proof. vm_refl. Qed.
Lemma D_93c68 : decode_any W_93c68 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_93c6c : bv 32 := 0x5556059b.
Lemma F_93c6c : fetch_word Asan.M.loaded_segments (0x93cbc : word) = Some W_93c6c.
Proof. vm_refl. Qed.
Lemma D_93c6c : decode_any W_93c6c = Some (OpImm32 11 12 1365, 4%Z).
Proof. vm_refl. Qed.

Definition W_93c70 : bv 32 := 0x3336861b.
Lemma F_93c70 : fetch_word Asan.M.loaded_segments (0x93cc0 : word) = Some W_93c70.
Proof. vm_refl. Qed.
Lemma D_93c70 : decode_any W_93c70 = Some (OpImm32 12 13 819, 4%Z).
Proof. vm_refl. Qed.

Definition W_93c74 : bv 32 := 0xf0f7069b.
Lemma F_93c74 : fetch_word Asan.M.loaded_segments (0x93cc4 : word) = Some W_93c74.
Proof. vm_refl. Qed.
Lemma D_93c74 : decode_any W_93c74 = Some (OpImm32 13 14 3855, 4%Z).
Proof. vm_refl. Qed.

Definition W_93c78 : bv 32 := 0x1017871b.
Lemma F_93c78 : fetch_word Asan.M.loaded_segments (0x93cc8 : word) = Some W_93c78.
Proof. vm_refl. Qed.
Lemma D_93c78 : decode_any W_93c78 = Some (OpImm32 14 15 257, 4%Z).
Proof. vm_refl. Qed.

Definition W_93c7c : bv 32 := 0x00255793.
Lemma F_93c7c : fetch_word Asan.M.loaded_segments (0x93ccc : word) = Some W_93c7c.
Proof. vm_refl. Qed.
Lemma D_93c7c : decode_any W_93c7c = Some (ShiftImm ALU_SRL 15 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_93c80 : bv 32 := 0x00f56533.
Lemma F_93c80 : fetch_word Asan.M.loaded_segments (0x93cd0 : word) = Some W_93c80.
Proof. vm_refl. Qed.
Lemma D_93c80 : decode_any W_93c80 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_93c84 : bv 32 := 0x02059793.
Lemma F_93c84 : fetch_word Asan.M.loaded_segments (0x93cd4 : word) = Some W_93c84.
Proof. vm_refl. Qed.
Lemma D_93c84 : decode_any W_93c84 = Some (ShiftImm ALU_SLL 15 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_93c88 : bv 32 := 0x00f585b3.
Lemma F_93c88 : fetch_word Asan.M.loaded_segments (0x93cd8 : word) = Some W_93c88.
Proof. vm_refl. Qed.
Lemma D_93c88 : decode_any W_93c88 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_93c8c : bv 32 := 0x02061793.
Lemma F_93c8c : fetch_word Asan.M.loaded_segments (0x93cdc : word) = Some W_93c8c.
Proof. vm_refl. Qed.
Lemma D_93c8c : decode_any W_93c8c = Some (ShiftImm ALU_SLL 15 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_93c90 : bv 32 := 0x00f60633.
Lemma F_93c90 : fetch_word Asan.M.loaded_segments (0x93ce0 : word) = Some W_93c90.
Proof. vm_refl. Qed.
Lemma D_93c90 : decode_any W_93c90 = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_93c94 : bv 32 := 0x02069793.
Lemma F_93c94 : fetch_word Asan.M.loaded_segments (0x93ce4 : word) = Some W_93c94.
Proof. vm_refl. Qed.
Lemma D_93c94 : decode_any W_93c94 = Some (ShiftImm ALU_SLL 15 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_93c98 : bv 32 := 0x00f686b3.
Lemma F_93c98 : fetch_word Asan.M.loaded_segments (0x93ce8 : word) = Some W_93c98.
Proof. vm_refl. Qed.
Lemma D_93c98 : decode_any W_93c98 = Some (Op ALU_ADD 13 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_93c9c : bv 32 := 0x02071793.
Lemma F_93c9c : fetch_word Asan.M.loaded_segments (0x93cec : word) = Some W_93c9c.
Proof. vm_refl. Qed.
Lemma D_93c9c : decode_any W_93c9c = Some (ShiftImm ALU_SLL 15 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_93ca0 : bv 32 := 0x00f70733.
Lemma F_93ca0 : fetch_word Asan.M.loaded_segments (0x93cf0 : word) = Some W_93ca0.
Proof. vm_refl. Qed.
Lemma D_93ca0 : decode_any W_93ca0 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_93ca4 : bv 32 := 0x00455793.
Lemma F_93ca4 : fetch_word Asan.M.loaded_segments (0x93cf4 : word) = Some W_93ca4.
Proof. vm_refl. Qed.
Lemma D_93ca4 : decode_any W_93ca4 = Some (ShiftImm ALU_SRL 15 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_93ca8 : bv 32 := 0x00f56533.
Lemma F_93ca8 : fetch_word Asan.M.loaded_segments (0x93cf8 : word) = Some W_93ca8.
Proof. vm_refl. Qed.
Lemma D_93ca8 : decode_any W_93ca8 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_93cac : bv 32 := 0x00855793.
Lemma F_93cac : fetch_word Asan.M.loaded_segments (0x93cfc : word) = Some W_93cac.
Proof. vm_refl. Qed.
Lemma D_93cac : decode_any W_93cac = Some (ShiftImm ALU_SRL 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_93cb0 : bv 32 := 0x00f56533.
Lemma F_93cb0 : fetch_word Asan.M.loaded_segments (0x93d00 : word) = Some W_93cb0.
Proof. vm_refl. Qed.
Lemma D_93cb0 : decode_any W_93cb0 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_93cb4 : bv 32 := 0x01055793.
Lemma F_93cb4 : fetch_word Asan.M.loaded_segments (0x93d04 : word) = Some W_93cb4.
Proof. vm_refl. Qed.
Lemma D_93cb4 : decode_any W_93cb4 = Some (ShiftImm ALU_SRL 15 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_93cb8 : bv 32 := 0x00f56533.
Lemma F_93cb8 : fetch_word Asan.M.loaded_segments (0x93d08 : word) = Some W_93cb8.
Proof. vm_refl. Qed.
Lemma D_93cb8 : decode_any W_93cb8 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_93cbc : bv 32 := 0x02055793.
Lemma F_93cbc : fetch_word Asan.M.loaded_segments (0x93d0c : word) = Some W_93cbc.
Proof. vm_refl. Qed.
Lemma D_93cbc : decode_any W_93cbc = Some (ShiftImm ALU_SRL 15 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_93cc0 : bv 32 := 0x00f56533.
Lemma F_93cc0 : fetch_word Asan.M.loaded_segments (0x93d10 : word) = Some W_93cc0.
Proof. vm_refl. Qed.
Lemma D_93cc0 : decode_any W_93cc0 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_93cc4 : bv 32 := 0xfff54513.
Lemma F_93cc4 : fetch_word Asan.M.loaded_segments (0x93d14 : word) = Some W_93cc4.
Proof. vm_refl. Qed.
Lemma D_93cc4 : decode_any W_93cc4 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_93cc8 : bv 32 := 0x00155793.
Lemma F_93cc8 : fetch_word Asan.M.loaded_segments (0x93d18 : word) = Some W_93cc8.
Proof. vm_refl. Qed.
Lemma D_93cc8 : decode_any W_93cc8 = Some (ShiftImm ALU_SRL 15 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_93ccc : bv 32 := 0x00b7f5b3.
Lemma F_93ccc : fetch_word Asan.M.loaded_segments (0x93d1c : word) = Some W_93ccc.
Proof. vm_refl. Qed.
Lemma D_93ccc : decode_any W_93ccc = Some (Op ALU_AND 11 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_93cd0 : bv 32 := 0x40b50533.
Lemma F_93cd0 : fetch_word Asan.M.loaded_segments (0x93d20 : word) = Some W_93cd0.
Proof. vm_refl. Qed.
Lemma D_93cd0 : decode_any W_93cd0 = Some (Op ALU_SUB 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_93cd4 : bv 32 := 0x00c575b3.
Lemma F_93cd4 : fetch_word Asan.M.loaded_segments (0x93d24 : word) = Some W_93cd4.
Proof. vm_refl. Qed.
Lemma D_93cd4 : decode_any W_93cd4 = Some (Op ALU_AND 11 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_93cd8 : bv 32 := 0x00255513.
Lemma F_93cd8 : fetch_word Asan.M.loaded_segments (0x93d28 : word) = Some W_93cd8.
Proof. vm_refl. Qed.
Lemma D_93cd8 : decode_any W_93cd8 = Some (ShiftImm ALU_SRL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_93cdc : bv 32 := 0x00c57533.
Lemma F_93cdc : fetch_word Asan.M.loaded_segments (0x93d2c : word) = Some W_93cdc.
Proof. vm_refl. Qed.
Lemma D_93cdc : decode_any W_93cdc = Some (Op ALU_AND 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_93ce0 : bv 32 := 0x00a58533.
Lemma F_93ce0 : fetch_word Asan.M.loaded_segments (0x93d30 : word) = Some W_93ce0.
Proof. vm_refl. Qed.
Lemma D_93ce0 : decode_any W_93ce0 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_93ce4 : bv 32 := 0x00455593.
Lemma F_93ce4 : fetch_word Asan.M.loaded_segments (0x93d34 : word) = Some W_93ce4.
Proof. vm_refl. Qed.
Lemma D_93ce4 : decode_any W_93ce4 = Some (ShiftImm ALU_SRL 11 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_93ce8 : bv 32 := 0x00b50533.
Lemma F_93ce8 : fetch_word Asan.M.loaded_segments (0x93d38 : word) = Some W_93ce8.
Proof. vm_refl. Qed.
Lemma D_93ce8 : decode_any W_93ce8 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_93cec : bv 32 := 0x00d57533.
Lemma F_93cec : fetch_word Asan.M.loaded_segments (0x93d3c : word) = Some W_93cec.
Proof. vm_refl. Qed.
Lemma D_93cec : decode_any W_93cec = Some (Op ALU_AND 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_93cf0 : bv 32 := 0x02e50533.
Lemma F_93cf0 : fetch_word Asan.M.loaded_segments (0x93d40 : word) = Some W_93cf0.
Proof. vm_refl. Qed.
Lemma D_93cf0 : decode_any W_93cf0 = Some (Mul M_MUL 10 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_93cf4 : bv 32 := 0x03855513.
Lemma F_93cf4 : fetch_word Asan.M.loaded_segments (0x93d44 : word) = Some W_93cf4.
Proof. vm_refl. Qed.
Lemma D_93cf4 : decode_any W_93cf4 = Some (ShiftImm ALU_SRL 10 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_93cf8 : bv 32 := 0x40a0053b.
Lemma F_93cf8 : fetch_word Asan.M.loaded_segments (0x93d48 : word) = Some W_93cf8.
Proof. vm_refl. Qed.
Lemma D_93cf8 : decode_any W_93cf8 = Some (Op32 ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_93cfc : bv 32 := 0xfff00593.
Lemma F_93cfc : fetch_word Asan.M.loaded_segments (0x93d4c : word) = Some W_93cfc.
Proof. vm_refl. Qed.
Lemma D_93cfc : decode_any W_93cfc = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_93d00 : bv 32 := 0x00a59533.
Lemma F_93d00 : fetch_word Asan.M.loaded_segments (0x93d50 : word) = Some W_93d00.
Proof. vm_refl. Qed.
Lemma D_93d00 : decode_any W_93d00 = Some (Op ALU_SLL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_93d04 : bv 32 := 0xfff54513.
Lemma F_93d04 : fetch_word Asan.M.loaded_segments (0x93d54 : word) = Some W_93d04.
Proof. vm_refl. Qed.
Lemma D_93d04 : decode_any W_93d04 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.


(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_72c28 : bv 32 := 0x00155593.
Lemma F_72c28 : fetch_word AsanUbsan.M.loaded_segments (0x72c28 : word) = Some W_72c28.
Proof. vm_refl. Qed.
Lemma D_72c28 : decode_any W_72c28 = Some (ShiftImm ALU_SRL 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72c2c : bv 32 := 0x55555637.
Lemma F_72c2c : fetch_word AsanUbsan.M.loaded_segments (0x72c2c : word) = Some W_72c2c.
Proof. vm_refl. Qed.
Lemma D_72c2c : decode_any W_72c2c = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72c30 : bv 32 := 0x333336b7.
Lemma F_72c30 : fetch_word AsanUbsan.M.loaded_segments (0x72c30 : word) = Some W_72c30.
Proof. vm_refl. Qed.
Lemma D_72c30 : decode_any W_72c30 = Some (Lui 13 209715, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72c34 : bv 32 := 0x0f0f1737.
Lemma F_72c34 : fetch_word AsanUbsan.M.loaded_segments (0x72c34 : word) = Some W_72c34.
Proof. vm_refl. Qed.
Lemma D_72c34 : decode_any W_72c34 = Some (Lui 14 61681, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72c38 : bv 32 := 0x010107b7.
Lemma F_72c38 : fetch_word AsanUbsan.M.loaded_segments (0x72c38 : word) = Some W_72c38.
Proof. vm_refl. Qed.
Lemma D_72c38 : decode_any W_72c38 = Some (Lui 15 4112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72c3c : bv 32 := 0x00b56533.
Lemma F_72c3c : fetch_word AsanUbsan.M.loaded_segments (0x72c3c : word) = Some W_72c3c.
Proof. vm_refl. Qed.
Lemma D_72c3c : decode_any W_72c3c = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72c40 : bv 32 := 0x5556059b.
Lemma F_72c40 : fetch_word AsanUbsan.M.loaded_segments (0x72c40 : word) = Some W_72c40.
Proof. vm_refl. Qed.
Lemma D_72c40 : decode_any W_72c40 = Some (OpImm32 11 12 1365, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72c44 : bv 32 := 0x3336861b.
Lemma F_72c44 : fetch_word AsanUbsan.M.loaded_segments (0x72c44 : word) = Some W_72c44.
Proof. vm_refl. Qed.
Lemma D_72c44 : decode_any W_72c44 = Some (OpImm32 12 13 819, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72c48 : bv 32 := 0xf0f7069b.
Lemma F_72c48 : fetch_word AsanUbsan.M.loaded_segments (0x72c48 : word) = Some W_72c48.
Proof. vm_refl. Qed.
Lemma D_72c48 : decode_any W_72c48 = Some (OpImm32 13 14 3855, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72c4c : bv 32 := 0x1017871b.
Lemma F_72c4c : fetch_word AsanUbsan.M.loaded_segments (0x72c4c : word) = Some W_72c4c.
Proof. vm_refl. Qed.
Lemma D_72c4c : decode_any W_72c4c = Some (OpImm32 14 15 257, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72c50 : bv 32 := 0x00255793.
Lemma F_72c50 : fetch_word AsanUbsan.M.loaded_segments (0x72c50 : word) = Some W_72c50.
Proof. vm_refl. Qed.
Lemma D_72c50 : decode_any W_72c50 = Some (ShiftImm ALU_SRL 15 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72c54 : bv 32 := 0x00f56533.
Lemma F_72c54 : fetch_word AsanUbsan.M.loaded_segments (0x72c54 : word) = Some W_72c54.
Proof. vm_refl. Qed.
Lemma D_72c54 : decode_any W_72c54 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72c58 : bv 32 := 0x02059793.
Lemma F_72c58 : fetch_word AsanUbsan.M.loaded_segments (0x72c58 : word) = Some W_72c58.
Proof. vm_refl. Qed.
Lemma D_72c58 : decode_any W_72c58 = Some (ShiftImm ALU_SLL 15 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72c5c : bv 32 := 0x00f585b3.
Lemma F_72c5c : fetch_word AsanUbsan.M.loaded_segments (0x72c5c : word) = Some W_72c5c.
Proof. vm_refl. Qed.
Lemma D_72c5c : decode_any W_72c5c = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72c60 : bv 32 := 0x02061793.
Lemma F_72c60 : fetch_word AsanUbsan.M.loaded_segments (0x72c60 : word) = Some W_72c60.
Proof. vm_refl. Qed.
Lemma D_72c60 : decode_any W_72c60 = Some (ShiftImm ALU_SLL 15 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72c64 : bv 32 := 0x00f60633.
Lemma F_72c64 : fetch_word AsanUbsan.M.loaded_segments (0x72c64 : word) = Some W_72c64.
Proof. vm_refl. Qed.
Lemma D_72c64 : decode_any W_72c64 = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72c68 : bv 32 := 0x02069793.
Lemma F_72c68 : fetch_word AsanUbsan.M.loaded_segments (0x72c68 : word) = Some W_72c68.
Proof. vm_refl. Qed.
Lemma D_72c68 : decode_any W_72c68 = Some (ShiftImm ALU_SLL 15 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72c6c : bv 32 := 0x00f686b3.
Lemma F_72c6c : fetch_word AsanUbsan.M.loaded_segments (0x72c6c : word) = Some W_72c6c.
Proof. vm_refl. Qed.
Lemma D_72c6c : decode_any W_72c6c = Some (Op ALU_ADD 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72c70 : bv 32 := 0x02071793.
Lemma F_72c70 : fetch_word AsanUbsan.M.loaded_segments (0x72c70 : word) = Some W_72c70.
Proof. vm_refl. Qed.
Lemma D_72c70 : decode_any W_72c70 = Some (ShiftImm ALU_SLL 15 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72c74 : bv 32 := 0x00f70733.
Lemma F_72c74 : fetch_word AsanUbsan.M.loaded_segments (0x72c74 : word) = Some W_72c74.
Proof. vm_refl. Qed.
Lemma D_72c74 : decode_any W_72c74 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72c78 : bv 32 := 0x00455793.
Lemma F_72c78 : fetch_word AsanUbsan.M.loaded_segments (0x72c78 : word) = Some W_72c78.
Proof. vm_refl. Qed.
Lemma D_72c78 : decode_any W_72c78 = Some (ShiftImm ALU_SRL 15 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72c7c : bv 32 := 0x00f56533.
Lemma F_72c7c : fetch_word AsanUbsan.M.loaded_segments (0x72c7c : word) = Some W_72c7c.
Proof. vm_refl. Qed.
Lemma D_72c7c : decode_any W_72c7c = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72c80 : bv 32 := 0x00855793.
Lemma F_72c80 : fetch_word AsanUbsan.M.loaded_segments (0x72c80 : word) = Some W_72c80.
Proof. vm_refl. Qed.
Lemma D_72c80 : decode_any W_72c80 = Some (ShiftImm ALU_SRL 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72c84 : bv 32 := 0x00f56533.
Lemma F_72c84 : fetch_word AsanUbsan.M.loaded_segments (0x72c84 : word) = Some W_72c84.
Proof. vm_refl. Qed.
Lemma D_72c84 : decode_any W_72c84 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72c88 : bv 32 := 0x01055793.
Lemma F_72c88 : fetch_word AsanUbsan.M.loaded_segments (0x72c88 : word) = Some W_72c88.
Proof. vm_refl. Qed.
Lemma D_72c88 : decode_any W_72c88 = Some (ShiftImm ALU_SRL 15 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72c8c : bv 32 := 0x00f56533.
Lemma F_72c8c : fetch_word AsanUbsan.M.loaded_segments (0x72c8c : word) = Some W_72c8c.
Proof. vm_refl. Qed.
Lemma D_72c8c : decode_any W_72c8c = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72c90 : bv 32 := 0x02055793.
Lemma F_72c90 : fetch_word AsanUbsan.M.loaded_segments (0x72c90 : word) = Some W_72c90.
Proof. vm_refl. Qed.
Lemma D_72c90 : decode_any W_72c90 = Some (ShiftImm ALU_SRL 15 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72c94 : bv 32 := 0x00f56533.
Lemma F_72c94 : fetch_word AsanUbsan.M.loaded_segments (0x72c94 : word) = Some W_72c94.
Proof. vm_refl. Qed.
Lemma D_72c94 : decode_any W_72c94 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72c98 : bv 32 := 0xfff54513.
Lemma F_72c98 : fetch_word AsanUbsan.M.loaded_segments (0x72c98 : word) = Some W_72c98.
Proof. vm_refl. Qed.
Lemma D_72c98 : decode_any W_72c98 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72c9c : bv 32 := 0x00155793.
Lemma F_72c9c : fetch_word AsanUbsan.M.loaded_segments (0x72c9c : word) = Some W_72c9c.
Proof. vm_refl. Qed.
Lemma D_72c9c : decode_any W_72c9c = Some (ShiftImm ALU_SRL 15 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72ca0 : bv 32 := 0x00b7f5b3.
Lemma F_72ca0 : fetch_word AsanUbsan.M.loaded_segments (0x72ca0 : word) = Some W_72ca0.
Proof. vm_refl. Qed.
Lemma D_72ca0 : decode_any W_72ca0 = Some (Op ALU_AND 11 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72ca4 : bv 32 := 0x40b50533.
Lemma F_72ca4 : fetch_word AsanUbsan.M.loaded_segments (0x72ca4 : word) = Some W_72ca4.
Proof. vm_refl. Qed.
Lemma D_72ca4 : decode_any W_72ca4 = Some (Op ALU_SUB 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72ca8 : bv 32 := 0x00c575b3.
Lemma F_72ca8 : fetch_word AsanUbsan.M.loaded_segments (0x72ca8 : word) = Some W_72ca8.
Proof. vm_refl. Qed.
Lemma D_72ca8 : decode_any W_72ca8 = Some (Op ALU_AND 11 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72cac : bv 32 := 0x00255513.
Lemma F_72cac : fetch_word AsanUbsan.M.loaded_segments (0x72cac : word) = Some W_72cac.
Proof. vm_refl. Qed.
Lemma D_72cac : decode_any W_72cac = Some (ShiftImm ALU_SRL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72cb0 : bv 32 := 0x00c57533.
Lemma F_72cb0 : fetch_word AsanUbsan.M.loaded_segments (0x72cb0 : word) = Some W_72cb0.
Proof. vm_refl. Qed.
Lemma D_72cb0 : decode_any W_72cb0 = Some (Op ALU_AND 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72cb4 : bv 32 := 0x00a58533.
Lemma F_72cb4 : fetch_word AsanUbsan.M.loaded_segments (0x72cb4 : word) = Some W_72cb4.
Proof. vm_refl. Qed.
Lemma D_72cb4 : decode_any W_72cb4 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72cb8 : bv 32 := 0x00455593.
Lemma F_72cb8 : fetch_word AsanUbsan.M.loaded_segments (0x72cb8 : word) = Some W_72cb8.
Proof. vm_refl. Qed.
Lemma D_72cb8 : decode_any W_72cb8 = Some (ShiftImm ALU_SRL 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72cbc : bv 32 := 0x00b50533.
Lemma F_72cbc : fetch_word AsanUbsan.M.loaded_segments (0x72cbc : word) = Some W_72cbc.
Proof. vm_refl. Qed.
Lemma D_72cbc : decode_any W_72cbc = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72cc0 : bv 32 := 0x00d57533.
Lemma F_72cc0 : fetch_word AsanUbsan.M.loaded_segments (0x72cc0 : word) = Some W_72cc0.
Proof. vm_refl. Qed.
Lemma D_72cc0 : decode_any W_72cc0 = Some (Op ALU_AND 10 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72cc4 : bv 32 := 0x02e50533.
Lemma F_72cc4 : fetch_word AsanUbsan.M.loaded_segments (0x72cc4 : word) = Some W_72cc4.
Proof. vm_refl. Qed.
Lemma D_72cc4 : decode_any W_72cc4 = Some (Mul M_MUL 10 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72cc8 : bv 32 := 0x03855513.
Lemma F_72cc8 : fetch_word AsanUbsan.M.loaded_segments (0x72cc8 : word) = Some W_72cc8.
Proof. vm_refl. Qed.
Lemma D_72cc8 : decode_any W_72cc8 = Some (ShiftImm ALU_SRL 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72ccc : bv 32 := 0x40a0053b.
Lemma F_72ccc : fetch_word AsanUbsan.M.loaded_segments (0x72ccc : word) = Some W_72ccc.
Proof. vm_refl. Qed.
Lemma D_72ccc : decode_any W_72ccc = Some (Op32 ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72cd0 : bv 32 := 0xfff00593.
Lemma F_72cd0 : fetch_word AsanUbsan.M.loaded_segments (0x72cd0 : word) = Some W_72cd0.
Proof. vm_refl. Qed.
Lemma D_72cd0 : decode_any W_72cd0 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72cd4 : bv 32 := 0x00a59533.
Lemma F_72cd4 : fetch_word AsanUbsan.M.loaded_segments (0x72cd4 : word) = Some W_72cd4.
Proof. vm_refl. Qed.
Lemma D_72cd4 : decode_any W_72cd4 = Some (Op ALU_SLL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72cd8 : bv 32 := 0xfff54513.
Lemma F_72cd8 : fetch_word AsanUbsan.M.loaded_segments (0x72cd8 : word) = Some W_72cd8.
Proof. vm_refl. Qed.
Lemma D_72cd8 : decode_any W_72cd8 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_8dc20 : bv 32 := 0x00155593.
Lemma F_8dc20 : fetch_word AsanUbsan.M.loaded_segments (0x8dc70 : word) = Some W_8dc20.
Proof. vm_refl. Qed.
Lemma D_8dc20 : decode_any W_8dc20 = Some (ShiftImm ALU_SRL 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc24 : bv 32 := 0x55555637.
Lemma F_8dc24 : fetch_word AsanUbsan.M.loaded_segments (0x8dc74 : word) = Some W_8dc24.
Proof. vm_refl. Qed.
Lemma D_8dc24 : decode_any W_8dc24 = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc28 : bv 32 := 0x333336b7.
Lemma F_8dc28 : fetch_word AsanUbsan.M.loaded_segments (0x8dc78 : word) = Some W_8dc28.
Proof. vm_refl. Qed.
Lemma D_8dc28 : decode_any W_8dc28 = Some (Lui 13 209715, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc2c : bv 32 := 0x0f0f1737.
Lemma F_8dc2c : fetch_word AsanUbsan.M.loaded_segments (0x8dc7c : word) = Some W_8dc2c.
Proof. vm_refl. Qed.
Lemma D_8dc2c : decode_any W_8dc2c = Some (Lui 14 61681, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc30 : bv 32 := 0x010107b7.
Lemma F_8dc30 : fetch_word AsanUbsan.M.loaded_segments (0x8dc80 : word) = Some W_8dc30.
Proof. vm_refl. Qed.
Lemma D_8dc30 : decode_any W_8dc30 = Some (Lui 15 4112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc34 : bv 32 := 0x00b56533.
Lemma F_8dc34 : fetch_word AsanUbsan.M.loaded_segments (0x8dc84 : word) = Some W_8dc34.
Proof. vm_refl. Qed.
Lemma D_8dc34 : decode_any W_8dc34 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc38 : bv 32 := 0x5556059b.
Lemma F_8dc38 : fetch_word AsanUbsan.M.loaded_segments (0x8dc88 : word) = Some W_8dc38.
Proof. vm_refl. Qed.
Lemma D_8dc38 : decode_any W_8dc38 = Some (OpImm32 11 12 1365, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc3c : bv 32 := 0x3336861b.
Lemma F_8dc3c : fetch_word AsanUbsan.M.loaded_segments (0x8dc8c : word) = Some W_8dc3c.
Proof. vm_refl. Qed.
Lemma D_8dc3c : decode_any W_8dc3c = Some (OpImm32 12 13 819, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc40 : bv 32 := 0xf0f7069b.
Lemma F_8dc40 : fetch_word AsanUbsan.M.loaded_segments (0x8dc90 : word) = Some W_8dc40.
Proof. vm_refl. Qed.
Lemma D_8dc40 : decode_any W_8dc40 = Some (OpImm32 13 14 3855, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc44 : bv 32 := 0x1017871b.
Lemma F_8dc44 : fetch_word AsanUbsan.M.loaded_segments (0x8dc94 : word) = Some W_8dc44.
Proof. vm_refl. Qed.
Lemma D_8dc44 : decode_any W_8dc44 = Some (OpImm32 14 15 257, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc48 : bv 32 := 0x00255793.
Lemma F_8dc48 : fetch_word AsanUbsan.M.loaded_segments (0x8dc98 : word) = Some W_8dc48.
Proof. vm_refl. Qed.
Lemma D_8dc48 : decode_any W_8dc48 = Some (ShiftImm ALU_SRL 15 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc4c : bv 32 := 0x00f56533.
Lemma F_8dc4c : fetch_word AsanUbsan.M.loaded_segments (0x8dc9c : word) = Some W_8dc4c.
Proof. vm_refl. Qed.
Lemma D_8dc4c : decode_any W_8dc4c = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc50 : bv 32 := 0x02059793.
Lemma F_8dc50 : fetch_word AsanUbsan.M.loaded_segments (0x8dca0 : word) = Some W_8dc50.
Proof. vm_refl. Qed.
Lemma D_8dc50 : decode_any W_8dc50 = Some (ShiftImm ALU_SLL 15 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc54 : bv 32 := 0x00f585b3.
Lemma F_8dc54 : fetch_word AsanUbsan.M.loaded_segments (0x8dca4 : word) = Some W_8dc54.
Proof. vm_refl. Qed.
Lemma D_8dc54 : decode_any W_8dc54 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc58 : bv 32 := 0x02061793.
Lemma F_8dc58 : fetch_word AsanUbsan.M.loaded_segments (0x8dca8 : word) = Some W_8dc58.
Proof. vm_refl. Qed.
Lemma D_8dc58 : decode_any W_8dc58 = Some (ShiftImm ALU_SLL 15 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc5c : bv 32 := 0x00f60633.
Lemma F_8dc5c : fetch_word AsanUbsan.M.loaded_segments (0x8dcac : word) = Some W_8dc5c.
Proof. vm_refl. Qed.
Lemma D_8dc5c : decode_any W_8dc5c = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc60 : bv 32 := 0x02069793.
Lemma F_8dc60 : fetch_word AsanUbsan.M.loaded_segments (0x8dcb0 : word) = Some W_8dc60.
Proof. vm_refl. Qed.
Lemma D_8dc60 : decode_any W_8dc60 = Some (ShiftImm ALU_SLL 15 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc64 : bv 32 := 0x00f686b3.
Lemma F_8dc64 : fetch_word AsanUbsan.M.loaded_segments (0x8dcb4 : word) = Some W_8dc64.
Proof. vm_refl. Qed.
Lemma D_8dc64 : decode_any W_8dc64 = Some (Op ALU_ADD 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc68 : bv 32 := 0x02071793.
Lemma F_8dc68 : fetch_word AsanUbsan.M.loaded_segments (0x8dcb8 : word) = Some W_8dc68.
Proof. vm_refl. Qed.
Lemma D_8dc68 : decode_any W_8dc68 = Some (ShiftImm ALU_SLL 15 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc6c : bv 32 := 0x00f70733.
Lemma F_8dc6c : fetch_word AsanUbsan.M.loaded_segments (0x8dcbc : word) = Some W_8dc6c.
Proof. vm_refl. Qed.
Lemma D_8dc6c : decode_any W_8dc6c = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc70 : bv 32 := 0x00455793.
Lemma F_8dc70 : fetch_word AsanUbsan.M.loaded_segments (0x8dcc0 : word) = Some W_8dc70.
Proof. vm_refl. Qed.
Lemma D_8dc70 : decode_any W_8dc70 = Some (ShiftImm ALU_SRL 15 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc74 : bv 32 := 0x00f56533.
Lemma F_8dc74 : fetch_word AsanUbsan.M.loaded_segments (0x8dcc4 : word) = Some W_8dc74.
Proof. vm_refl. Qed.
Lemma D_8dc74 : decode_any W_8dc74 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc78 : bv 32 := 0x00855793.
Lemma F_8dc78 : fetch_word AsanUbsan.M.loaded_segments (0x8dcc8 : word) = Some W_8dc78.
Proof. vm_refl. Qed.
Lemma D_8dc78 : decode_any W_8dc78 = Some (ShiftImm ALU_SRL 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc7c : bv 32 := 0x00f56533.
Lemma F_8dc7c : fetch_word AsanUbsan.M.loaded_segments (0x8dccc : word) = Some W_8dc7c.
Proof. vm_refl. Qed.
Lemma D_8dc7c : decode_any W_8dc7c = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc80 : bv 32 := 0x01055793.
Lemma F_8dc80 : fetch_word AsanUbsan.M.loaded_segments (0x8dcd0 : word) = Some W_8dc80.
Proof. vm_refl. Qed.
Lemma D_8dc80 : decode_any W_8dc80 = Some (ShiftImm ALU_SRL 15 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc84 : bv 32 := 0x00f56533.
Lemma F_8dc84 : fetch_word AsanUbsan.M.loaded_segments (0x8dcd4 : word) = Some W_8dc84.
Proof. vm_refl. Qed.
Lemma D_8dc84 : decode_any W_8dc84 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc88 : bv 32 := 0x02055793.
Lemma F_8dc88 : fetch_word AsanUbsan.M.loaded_segments (0x8dcd8 : word) = Some W_8dc88.
Proof. vm_refl. Qed.
Lemma D_8dc88 : decode_any W_8dc88 = Some (ShiftImm ALU_SRL 15 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc8c : bv 32 := 0x00f56533.
Lemma F_8dc8c : fetch_word AsanUbsan.M.loaded_segments (0x8dcdc : word) = Some W_8dc8c.
Proof. vm_refl. Qed.
Lemma D_8dc8c : decode_any W_8dc8c = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc90 : bv 32 := 0xfff54513.
Lemma F_8dc90 : fetch_word AsanUbsan.M.loaded_segments (0x8dce0 : word) = Some W_8dc90.
Proof. vm_refl. Qed.
Lemma D_8dc90 : decode_any W_8dc90 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc94 : bv 32 := 0x00155793.
Lemma F_8dc94 : fetch_word AsanUbsan.M.loaded_segments (0x8dce4 : word) = Some W_8dc94.
Proof. vm_refl. Qed.
Lemma D_8dc94 : decode_any W_8dc94 = Some (ShiftImm ALU_SRL 15 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc98 : bv 32 := 0x00b7f5b3.
Lemma F_8dc98 : fetch_word AsanUbsan.M.loaded_segments (0x8dce8 : word) = Some W_8dc98.
Proof. vm_refl. Qed.
Lemma D_8dc98 : decode_any W_8dc98 = Some (Op ALU_AND 11 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc9c : bv 32 := 0x40b50533.
Lemma F_8dc9c : fetch_word AsanUbsan.M.loaded_segments (0x8dcec : word) = Some W_8dc9c.
Proof. vm_refl. Qed.
Lemma D_8dc9c : decode_any W_8dc9c = Some (Op ALU_SUB 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dca0 : bv 32 := 0x00c575b3.
Lemma F_8dca0 : fetch_word AsanUbsan.M.loaded_segments (0x8dcf0 : word) = Some W_8dca0.
Proof. vm_refl. Qed.
Lemma D_8dca0 : decode_any W_8dca0 = Some (Op ALU_AND 11 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dca4 : bv 32 := 0x00255513.
Lemma F_8dca4 : fetch_word AsanUbsan.M.loaded_segments (0x8dcf4 : word) = Some W_8dca4.
Proof. vm_refl. Qed.
Lemma D_8dca4 : decode_any W_8dca4 = Some (ShiftImm ALU_SRL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dca8 : bv 32 := 0x00c57533.
Lemma F_8dca8 : fetch_word AsanUbsan.M.loaded_segments (0x8dcf8 : word) = Some W_8dca8.
Proof. vm_refl. Qed.
Lemma D_8dca8 : decode_any W_8dca8 = Some (Op ALU_AND 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dcac : bv 32 := 0x00a58533.
Lemma F_8dcac : fetch_word AsanUbsan.M.loaded_segments (0x8dcfc : word) = Some W_8dcac.
Proof. vm_refl. Qed.
Lemma D_8dcac : decode_any W_8dcac = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dcb0 : bv 32 := 0x00455593.
Lemma F_8dcb0 : fetch_word AsanUbsan.M.loaded_segments (0x8dd00 : word) = Some W_8dcb0.
Proof. vm_refl. Qed.
Lemma D_8dcb0 : decode_any W_8dcb0 = Some (ShiftImm ALU_SRL 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dcb4 : bv 32 := 0x00b50533.
Lemma F_8dcb4 : fetch_word AsanUbsan.M.loaded_segments (0x8dd04 : word) = Some W_8dcb4.
Proof. vm_refl. Qed.
Lemma D_8dcb4 : decode_any W_8dcb4 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dcb8 : bv 32 := 0x00d57533.
Lemma F_8dcb8 : fetch_word AsanUbsan.M.loaded_segments (0x8dd08 : word) = Some W_8dcb8.
Proof. vm_refl. Qed.
Lemma D_8dcb8 : decode_any W_8dcb8 = Some (Op ALU_AND 10 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dcbc : bv 32 := 0x02e50533.
Lemma F_8dcbc : fetch_word AsanUbsan.M.loaded_segments (0x8dd0c : word) = Some W_8dcbc.
Proof. vm_refl. Qed.
Lemma D_8dcbc : decode_any W_8dcbc = Some (Mul M_MUL 10 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dcc0 : bv 32 := 0x03855513.
Lemma F_8dcc0 : fetch_word AsanUbsan.M.loaded_segments (0x8dd10 : word) = Some W_8dcc0.
Proof. vm_refl. Qed.
Lemma D_8dcc0 : decode_any W_8dcc0 = Some (ShiftImm ALU_SRL 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dcc4 : bv 32 := 0x40a0053b.
Lemma F_8dcc4 : fetch_word AsanUbsan.M.loaded_segments (0x8dd14 : word) = Some W_8dcc4.
Proof. vm_refl. Qed.
Lemma D_8dcc4 : decode_any W_8dcc4 = Some (Op32 ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dcc8 : bv 32 := 0xfff00593.
Lemma F_8dcc8 : fetch_word AsanUbsan.M.loaded_segments (0x8dd18 : word) = Some W_8dcc8.
Proof. vm_refl. Qed.
Lemma D_8dcc8 : decode_any W_8dcc8 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dccc : bv 32 := 0x00a59533.
Lemma F_8dccc : fetch_word AsanUbsan.M.loaded_segments (0x8dd1c : word) = Some W_8dccc.
Proof. vm_refl. Qed.
Lemma D_8dccc : decode_any W_8dccc = Some (Op ALU_SLL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dcd0 : bv 32 := 0xfff54513.
Lemma F_8dcd0 : fetch_word AsanUbsan.M.loaded_segments (0x8dd20 : word) = Some W_8dcd0.
Proof. vm_refl. Qed.
Lemma D_8dcd0 : decode_any W_8dcd0 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

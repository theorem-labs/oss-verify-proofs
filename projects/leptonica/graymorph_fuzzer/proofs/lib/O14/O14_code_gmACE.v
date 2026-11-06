(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_15b48 : bv 32 := 0xff010113.
Lemma F_15b48 : fetch_word Plain.M.loaded_segments (0x15c44 : word) = Some W_15b48.
Proof. vm_refl. Qed.
Lemma D_15b48 : decode_any W_15b48 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b4c : bv 32 := 0x00113423.
Lemma F_15b4c : fetch_word Plain.M.loaded_segments (0x15c48 : word) = Some W_15b4c.
Proof. vm_refl. Qed.
Lemma D_15b4c : decode_any W_15b4c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b50 : bv 32 := 0x00813023.
Lemma F_15b50 : fetch_word Plain.M.loaded_segments (0x15c4c : word) = Some W_15b50.
Proof. vm_refl. Qed.
Lemma D_15b50 : decode_any W_15b50 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b54 : bv 32 := 0x02050c63.
Lemma F_15b54 : fetch_word Plain.M.loaded_segments (0x15c50 : word) = Some W_15b54.
Proof. vm_refl. Qed.
Lemma D_15b54 : decode_any W_15b54 = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b58 : bv 32 := 0x0a8000ef.
Lemma F_15b58 : fetch_word Plain.M.loaded_segments (0x15c54 : word) = Some W_15b58.
Proof. vm_refl. Qed.
Lemma D_15b58 : decode_any W_15b58 = Some (Jal 1 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b5c : bv 32 := 0x04050c63.
Lemma F_15b5c : fetch_word Plain.M.loaded_segments (0x15c58 : word) = Some W_15b5c.
Proof. vm_refl. Qed.
Lemma D_15b5c : decode_any W_15b5c = Some (Branch BC_EQ 10 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b60 : bv 32 := 0x00456603.
Lemma F_15b60 : fetch_word Plain.M.loaded_segments (0x15c5c : word) = Some W_15b60.
Proof. vm_refl. Qed.
Lemma D_15b60 : decode_any W_15b60 = Some (Load SZ4 false 12 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b64 : bv 32 := 0x01056683.
Lemma F_15b64 : fetch_word Plain.M.loaded_segments (0x15c60 : word) = Some W_15b64.
Proof. vm_refl. Qed.
Lemma D_15b64 : decode_any W_15b64 = Some (Load SZ4 false 13 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b68 : bv 32 := 0x03853583.
Lemma F_15b68 : fetch_word Plain.M.loaded_segments (0x15c64 : word) = Some W_15b68.
Proof. vm_refl. Qed.
Lemma D_15b68 : decode_any W_15b68 = Some (Load SZ8 true 11 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b6c : bv 32 := 0x02c68633.
Lemma F_15b6c : fetch_word Plain.M.loaded_segments (0x15c68 : word) = Some W_15b6c.
Proof. vm_refl. Qed.
Lemma D_15b6c : decode_any W_15b6c = Some (Mul M_MUL 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b70 : bv 32 := 0x00261613.
Lemma F_15b70 : fetch_word Plain.M.loaded_segments (0x15c6c : word) = Some W_15b70.
Proof. vm_refl. Qed.
Lemma D_15b70 : decode_any W_15b70 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b74 : bv 32 := 0x00050413.
Lemma F_15b74 : fetch_word Plain.M.loaded_segments (0x15c70 : word) = Some W_15b74.
Proof. vm_refl. Qed.
Lemma D_15b74 : decode_any W_15b74 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b78 : bv 32 := 0x00058513.
Lemma F_15b78 : fetch_word Plain.M.loaded_segments (0x15c74 : word) = Some W_15b78.
Proof. vm_refl. Qed.
Lemma D_15b78 : decode_any W_15b78 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b7c : bv 32 := 0x00000593.
Lemma F_15b7c : fetch_word Plain.M.loaded_segments (0x15c78 : word) = Some W_15b7c.
Proof. vm_refl. Qed.
Lemma D_15b7c : decode_any W_15b7c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b80 : bv 32 := 0x7b0130ef.
Lemma F_15b80 : fetch_word Plain.M.loaded_segments (0x15c7c : word) = Some W_15b80.
Proof. vm_refl. Qed.
Lemma D_15b80 : decode_any W_15b80 = Some (Jal 1 79792, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b84 : bv 32 := 0x00040513.
Lemma F_15b84 : fetch_word Plain.M.loaded_segments (0x15c80 : word) = Some W_15b84.
Proof. vm_refl. Qed.
Lemma D_15b84 : decode_any W_15b84 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b88 : bv 32 := 0x0680006f.
Lemma F_15b88 : fetch_word Plain.M.loaded_segments (0x15c84 : word) = Some W_15b88.
Proof. vm_refl. Qed.
Lemma D_15b88 : decode_any W_15b88 = Some (Jal 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bb4 : bv 32 := 0x00015517.
Lemma F_15bb4 : fetch_word Plain.M.loaded_segments (0x15cb0 : word) = Some W_15bb4.
Proof. vm_refl. Qed.
Lemma D_15bb4 : decode_any W_15bb4 = Some (Auipc 10 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bb8 : bv 32 := 0xd9053503.
Lemma F_15bb8 : fetch_word Plain.M.loaded_segments (0x15cb4 : word) = Some W_15bb8.
Proof. vm_refl. Qed.
Lemma D_15bb8 : decode_any W_15bb8 = Some (Load SZ8 true 10 10 3472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bbc : bv 32 := 0x00052503.
Lemma F_15bbc : fetch_word Plain.M.loaded_segments (0x15cb8 : word) = Some W_15bbc.
Proof. vm_refl. Qed.
Lemma D_15bbc : decode_any W_15bbc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bc0 : bv 32 := 0x00500593.
Lemma F_15bc0 : fetch_word Plain.M.loaded_segments (0x15cbc : word) = Some W_15bc0.
Proof. vm_refl. Qed.
Lemma D_15bc0 : decode_any W_15bc0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bc4 : bv 32 := 0x02a5c463.
Lemma F_15bc4 : fetch_word Plain.M.loaded_segments (0x15cc0 : word) = Some W_15bc4.
Proof. vm_refl. Qed.
Lemma D_15bc4 : decode_any W_15bc4 = Some (Branch BC_LT 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bc8 : bv 32 := 0xffffa517.
Lemma F_15bc8 : fetch_word Plain.M.loaded_segments (0x15cc4 : word) = Some W_15bc8.
Proof. vm_refl. Qed.
Lemma D_15bc8 : decode_any W_15bc8 = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bcc : bv 32 := 0xffffb597.
Lemma F_15bcc : fetch_word Plain.M.loaded_segments (0x15cc8 : word) = Some W_15bcc.
Proof. vm_refl. Qed.
Lemma D_15bcc : decode_any W_15bcc = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bd0 : bv 32 := 0x7f950513.
Lemma F_15bd0 : fetch_word Plain.M.loaded_segments (0x15ccc : word) = Some W_15bd0.
Proof. vm_refl. Qed.
Lemma D_15bd0 : decode_any W_15bd0 = Some (OpImm ALU_ADD 10 10 2041, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bd4 : bv 32 := 0x0dc58593.
Lemma F_15bd4 : fetch_word Plain.M.loaded_segments (0x15cd0 : word) = Some W_15bd4.
Proof. vm_refl. Qed.
Lemma D_15bd4 : decode_any W_15bd4 = Some (OpImm ALU_ADD 11 11 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bd8 : bv 32 := 0x00000613.
Lemma F_15bd8 : fetch_word Plain.M.loaded_segments (0x15cd4 : word) = Some W_15bd8.
Proof. vm_refl. Qed.
Lemma D_15bd8 : decode_any W_15bd8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bdc : bv 32 := 0x00813083.
Lemma F_15bdc : fetch_word Plain.M.loaded_segments (0x15cd8 : word) = Some W_15bdc.
Proof. vm_refl. Qed.
Lemma D_15bdc : decode_any W_15bdc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15be0 : bv 32 := 0x00013403.
Lemma F_15be0 : fetch_word Plain.M.loaded_segments (0x15cdc : word) = Some W_15be0.
Proof. vm_refl. Qed.
Lemma D_15be0 : decode_any W_15be0 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15be4 : bv 32 := 0x01010113.
Lemma F_15be4 : fetch_word Plain.M.loaded_segments (0x15ce0 : word) = Some W_15be4.
Proof. vm_refl. Qed.
Lemma D_15be4 : decode_any W_15be4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15be8 : bv 32 := 0xf58ff06f.
Lemma F_15be8 : fetch_word Plain.M.loaded_segments (0x15ce4 : word) = Some W_15be8.
Proof. vm_refl. Qed.
Lemma D_15be8 : decode_any W_15be8 = Some (Jal 0 2094936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bf0 : bv 32 := 0x00813083.
Lemma F_15bf0 : fetch_word Plain.M.loaded_segments (0x15cec : word) = Some W_15bf0.
Proof. vm_refl. Qed.
Lemma D_15bf0 : decode_any W_15bf0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bf4 : bv 32 := 0x00013403.
Lemma F_15bf4 : fetch_word Plain.M.loaded_segments (0x15cf0 : word) = Some W_15bf4.
Proof. vm_refl. Qed.
Lemma D_15bf4 : decode_any W_15bf4 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bf8 : bv 32 := 0x01010113.
Lemma F_15bf8 : fetch_word Plain.M.loaded_segments (0x15cf4 : word) = Some W_15bf8.
Proof. vm_refl. Qed.
Lemma D_15bf8 : decode_any W_15bf8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bfc : bv 32 := 0x00008067.
Lemma F_15bfc : fetch_word Plain.M.loaded_segments (0x15cf8 : word) = Some W_15bfc.
Proof. vm_refl. Qed.
Lemma D_15bfc : decode_any W_15bfc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_15d38 : bv 32 := 0x00058463.
Lemma F_15d38 : fetch_word Plain.M.loaded_segments (0x15e34 : word) = Some W_15d38.
Proof. vm_refl. Qed.
Lemma D_15d38 : decode_any W_15d38 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d3c : bv 32 := 0x0005a023.
Lemma F_15d3c : fetch_word Plain.M.loaded_segments (0x15e38 : word) = Some W_15d3c.
Proof. vm_refl. Qed.
Lemma D_15d3c : decode_any W_15d3c = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d40 : bv 32 := 0x00060463.
Lemma F_15d40 : fetch_word Plain.M.loaded_segments (0x15e3c : word) = Some W_15d40.
Proof. vm_refl. Qed.
Lemma D_15d40 : decode_any W_15d40 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d44 : bv 32 := 0x00062023.
Lemma F_15d44 : fetch_word Plain.M.loaded_segments (0x15e40 : word) = Some W_15d44.
Proof. vm_refl. Qed.
Lemma D_15d44 : decode_any W_15d44 = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d48 : bv 32 := 0x00068463.
Lemma F_15d48 : fetch_word Plain.M.loaded_segments (0x15e44 : word) = Some W_15d48.
Proof. vm_refl. Qed.
Lemma D_15d48 : decode_any W_15d48 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d4c : bv 32 := 0x0006a023.
Lemma F_15d4c : fetch_word Plain.M.loaded_segments (0x15e48 : word) = Some W_15d4c.
Proof. vm_refl. Qed.
Lemma D_15d4c : decode_any W_15d4c = Some (Store SZ4 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d50 : bv 32 := 0x02050a63.
Lemma F_15d50 : fetch_word Plain.M.loaded_segments (0x15e4c : word) = Some W_15d50.
Proof. vm_refl. Qed.
Lemma D_15d50 : decode_any W_15d50 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d54 : bv 32 := 0x00058663.
Lemma F_15d54 : fetch_word Plain.M.loaded_segments (0x15e50 : word) = Some W_15d54.
Proof. vm_refl. Qed.
Lemma D_15d54 : decode_any W_15d54 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d58 : bv 32 := 0x00052703.
Lemma F_15d58 : fetch_word Plain.M.loaded_segments (0x15e54 : word) = Some W_15d58.
Proof. vm_refl. Qed.
Lemma D_15d58 : decode_any W_15d58 = Some (Load SZ4 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d5c : bv 32 := 0x00e5a023.
Lemma F_15d5c : fetch_word Plain.M.loaded_segments (0x15e58 : word) = Some W_15d5c.
Proof. vm_refl. Qed.
Lemma D_15d5c : decode_any W_15d5c = Some (Store SZ4 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d60 : bv 32 := 0x00060663.
Lemma F_15d60 : fetch_word Plain.M.loaded_segments (0x15e5c : word) = Some W_15d60.
Proof. vm_refl. Qed.
Lemma D_15d60 : decode_any W_15d60 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d64 : bv 32 := 0x00452583.
Lemma F_15d64 : fetch_word Plain.M.loaded_segments (0x15e60 : word) = Some W_15d64.
Proof. vm_refl. Qed.
Lemma D_15d64 : decode_any W_15d64 = Some (Load SZ4 true 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d68 : bv 32 := 0x00b62023.
Lemma F_15d68 : fetch_word Plain.M.loaded_segments (0x15e64 : word) = Some W_15d68.
Proof. vm_refl. Qed.
Lemma D_15d68 : decode_any W_15d68 = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d6c : bv 32 := 0x00000593.
Lemma F_15d6c : fetch_word Plain.M.loaded_segments (0x15e68 : word) = Some W_15d6c.
Proof. vm_refl. Qed.
Lemma D_15d6c : decode_any W_15d6c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d70 : bv 32 := 0x00068663.
Lemma F_15d70 : fetch_word Plain.M.loaded_segments (0x15e6c : word) = Some W_15d70.
Proof. vm_refl. Qed.
Lemma D_15d70 : decode_any W_15d70 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d74 : bv 32 := 0x00852503.
Lemma F_15d74 : fetch_word Plain.M.loaded_segments (0x15e70 : word) = Some W_15d74.
Proof. vm_refl. Qed.
Lemma D_15d74 : decode_any W_15d74 = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d78 : bv 32 := 0x00a6a023.
Lemma F_15d78 : fetch_word Plain.M.loaded_segments (0x15e74 : word) = Some W_15d78.
Proof. vm_refl. Qed.
Lemma D_15d78 : decode_any W_15d78 = Some (Store SZ4 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d7c : bv 32 := 0x00058513.
Lemma F_15d7c : fetch_word Plain.M.loaded_segments (0x15e78 : word) = Some W_15d7c.
Proof. vm_refl. Qed.
Lemma D_15d7c : decode_any W_15d7c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15d80 : bv 32 := 0x00008067.
Lemma F_15d80 : fetch_word Plain.M.loaded_segments (0x15e7c : word) = Some W_15d80.
Proof. vm_refl. Qed.
Lemma D_15d80 : decode_any W_15d80 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15db8 : bv 32 := 0x02050263.
Lemma F_15db8 : fetch_word Plain.M.loaded_segments (0x15eb4 : word) = Some W_15db8.
Proof. vm_refl. Qed.
Lemma D_15db8 : decode_any W_15db8 = Some (Branch BC_EQ 10 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15dbc : bv 32 := 0x04058663.
Lemma F_15dbc : fetch_word Plain.M.loaded_segments (0x15eb8 : word) = Some W_15dbc.
Proof. vm_refl. Qed.
Lemma D_15dbc : decode_any W_15dbc = Some (Branch BC_EQ 11 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15dc0 : bv 32 := 0x0ca58063.
Lemma F_15dc0 : fetch_word Plain.M.loaded_segments (0x15ebc : word) = Some W_15dc0.
Proof. vm_refl. Qed.
Lemma D_15dc0 : decode_any W_15dc0 = Some (Branch BC_EQ 11 10 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15dc4 : bv 32 := 0x00c5a583.
Lemma F_15dc4 : fetch_word Plain.M.loaded_segments (0x15ec0 : word) = Some W_15dc4.
Proof. vm_refl. Qed.
Lemma D_15dc4 : decode_any W_15dc4 = Some (Load SZ4 true 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15dc8 : bv 32 := 0x06b05a63.
Lemma F_15dc8 : fetch_word Plain.M.loaded_segments (0x15ec4 : word) = Some W_15dc8.
Proof. vm_refl. Qed.
Lemma D_15dc8 : decode_any W_15dc8 = Some (Branch BC_GE 0 11 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15dcc : bv 32 := 0x00050613.
Lemma F_15dcc : fetch_word Plain.M.loaded_segments (0x15ec8 : word) = Some W_15dcc.
Proof. vm_refl. Qed.
Lemma D_15dcc : decode_any W_15dcc = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15dd0 : bv 32 := 0x00000513.
Lemma F_15dd0 : fetch_word Plain.M.loaded_segments (0x15ecc : word) = Some W_15dd0.
Proof. vm_refl. Qed.
Lemma D_15dd0 : decode_any W_15dd0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15dd4 : bv 32 := 0x00b62623.
Lemma F_15dd4 : fetch_word Plain.M.loaded_segments (0x15ed0 : word) = Some W_15dd4.
Proof. vm_refl. Qed.
Lemma D_15dd4 : decode_any W_15dd4 = Some (Store SZ4 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15dd8 : bv 32 := 0x00008067.
Lemma F_15dd8 : fetch_word Plain.M.loaded_segments (0x15ed4 : word) = Some W_15dd8.
Proof. vm_refl. Qed.
Lemma D_15dd8 : decode_any W_15dd8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e88 : bv 32 := 0x02058063.
Lemma F_15e88 : fetch_word Plain.M.loaded_segments (0x15f84 : word) = Some W_15e88.
Proof. vm_refl. Qed.
Lemma D_15e88 : decode_any W_15e88 = Some (Branch BC_EQ 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e8c : bv 32 := 0x04050463.
Lemma F_15e8c : fetch_word Plain.M.loaded_segments (0x15f88 : word) = Some W_15e8c.
Proof. vm_refl. Qed.
Lemma D_15e8c : decode_any W_15e8c = Some (Branch BC_EQ 10 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e90 : bv 32 := 0x06a58c63.
Lemma F_15e90 : fetch_word Plain.M.loaded_segments (0x15f8c : word) = Some W_15e90.
Proof. vm_refl. Qed.
Lemma D_15e90 : decode_any W_15e90 = Some (Branch BC_EQ 11 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e94 : bv 32 := 0x00050613.
Lemma F_15e94 : fetch_word Plain.M.loaded_segments (0x15f90 : word) = Some W_15e94.
Proof. vm_refl. Qed.
Lemma D_15e94 : decode_any W_15e94 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e98 : bv 32 := 0x00000513.
Lemma F_15e98 : fetch_word Plain.M.loaded_segments (0x15f94 : word) = Some W_15e98.
Proof. vm_refl. Qed.
Lemma D_15e98 : decode_any W_15e98 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15e9c : bv 32 := 0x0185b583.
Lemma F_15e9c : fetch_word Plain.M.loaded_segments (0x15f98 : word) = Some W_15e9c.
Proof. vm_refl. Qed.
Lemma D_15e9c : decode_any W_15e9c = Some (Load SZ8 true 11 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ea0 : bv 32 := 0x00b63c23.
Lemma F_15ea0 : fetch_word Plain.M.loaded_segments (0x15f9c : word) = Some W_15ea0.
Proof. vm_refl. Qed.
Lemma D_15ea0 : decode_any W_15ea0 = Some (Store SZ8 12 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ea4 : bv 32 := 0x00008067.
Lemma F_15ea4 : fetch_word Plain.M.loaded_segments (0x15fa0 : word) = Some W_15ea4.
Proof. vm_refl. Qed.
Lemma D_15ea4 : decode_any W_15ea4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167b4 : bv 32 := 0x00050663.
Lemma F_167b4 : fetch_word Plain.M.loaded_segments (0x168b0 : word) = Some W_167b4.
Proof. vm_refl. Qed.
Lemma D_167b4 : decode_any W_167b4 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167b8 : bv 32 := 0x00852503.
Lemma F_167b8 : fetch_word Plain.M.loaded_segments (0x168b4 : word) = Some W_167b8.
Proof. vm_refl. Qed.
Lemma D_167b8 : decode_any W_167b8 = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167bc : bv 32 := 0x00008067.
Lemma F_167bc : fetch_word Plain.M.loaded_segments (0x168b8 : word) = Some W_167bc.
Proof. vm_refl. Qed.
Lemma D_167bc : decode_any W_167bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_177a8 : bv 32 := 0xf8010113.
Lemma F_177a8 : fetch_word Plain.M.loaded_segments (0x178a4 : word) = Some W_177a8.
Proof. vm_refl. Qed.
Lemma D_177a8 : decode_any W_177a8 = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_177ac : bv 32 := 0x06113c23.
Lemma F_177ac : fetch_word Plain.M.loaded_segments (0x178a8 : word) = Some W_177ac.
Proof. vm_refl. Qed.
Lemma D_177ac : decode_any W_177ac = Some (Store SZ8 2 1 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_177b0 : bv 32 := 0x06813823.
Lemma F_177b0 : fetch_word Plain.M.loaded_segments (0x178ac : word) = Some W_177b0.
Proof. vm_refl. Qed.
Lemma D_177b0 : decode_any W_177b0 = Some (Store SZ8 2 8 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_177b4 : bv 32 := 0x06913423.
Lemma F_177b4 : fetch_word Plain.M.loaded_segments (0x178b0 : word) = Some W_177b4.
Proof. vm_refl. Qed.
Lemma D_177b4 : decode_any W_177b4 = Some (Store SZ8 2 9 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_177b8 : bv 32 := 0x07213023.
Lemma F_177b8 : fetch_word Plain.M.loaded_segments (0x178b4 : word) = Some W_177b8.
Proof. vm_refl. Qed.
Lemma D_177b8 : decode_any W_177b8 = Some (Store SZ8 2 18 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_177bc : bv 32 := 0x05313c23.
Lemma F_177bc : fetch_word Plain.M.loaded_segments (0x178b8 : word) = Some W_177bc.
Proof. vm_refl. Qed.
Lemma D_177bc : decode_any W_177bc = Some (Store SZ8 2 19 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_177c0 : bv 32 := 0x05413823.
Lemma F_177c0 : fetch_word Plain.M.loaded_segments (0x178bc : word) = Some W_177c0.
Proof. vm_refl. Qed.
Lemma D_177c0 : decode_any W_177c0 = Some (Store SZ8 2 20 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_177c4 : bv 32 := 0x05513423.
Lemma F_177c4 : fetch_word Plain.M.loaded_segments (0x178c0 : word) = Some W_177c4.
Proof. vm_refl. Qed.
Lemma D_177c4 : decode_any W_177c4 = Some (Store SZ8 2 21 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_177c8 : bv 32 := 0x05613023.
Lemma F_177c8 : fetch_word Plain.M.loaded_segments (0x178c4 : word) = Some W_177c8.
Proof. vm_refl. Qed.
Lemma D_177c8 : decode_any W_177c8 = Some (Store SZ8 2 22 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_177cc : bv 32 := 0x03713c23.
Lemma F_177cc : fetch_word Plain.M.loaded_segments (0x178c8 : word) = Some W_177cc.
Proof. vm_refl. Qed.
Lemma D_177cc : decode_any W_177cc = Some (Store SZ8 2 23 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_177d0 : bv 32 := 0x03813823.
Lemma F_177d0 : fetch_word Plain.M.loaded_segments (0x178cc : word) = Some W_177d0.
Proof. vm_refl. Qed.
Lemma D_177d0 : decode_any W_177d0 = Some (Store SZ8 2 24 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_177d4 : bv 32 := 0x03913423.
Lemma F_177d4 : fetch_word Plain.M.loaded_segments (0x178d0 : word) = Some W_177d4.
Proof. vm_refl. Qed.
Lemma D_177d4 : decode_any W_177d4 = Some (Store SZ8 2 25 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_177d8 : bv 32 := 0x03a13023.
Lemma F_177d8 : fetch_word Plain.M.loaded_segments (0x178d4 : word) = Some W_177d8.
Proof. vm_refl. Qed.
Lemma D_177d8 : decode_any W_177d8 = Some (Store SZ8 2 26 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_177dc : bv 32 := 0x14050463.
Lemma F_177dc : fetch_word Plain.M.loaded_segments (0x178d8 : word) = Some W_177dc.
Proof. vm_refl. Qed.
Lemma D_177dc : decode_any W_177dc = Some (Branch BC_EQ 10 0 328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_177e0 : bv 32 := 0x00070a13.
Lemma F_177e0 : fetch_word Plain.M.loaded_segments (0x178dc : word) = Some W_177e0.
Proof. vm_refl. Qed.
Lemma D_177e0 : decode_any W_177e0 = Some (OpImm ALU_ADD 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_177e4 : bv 32 := 0x00068493.
Lemma F_177e4 : fetch_word Plain.M.loaded_segments (0x178e0 : word) = Some W_177e4.
Proof. vm_refl. Qed.
Lemma D_177e4 : decode_any W_177e4 = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_177e8 : bv 32 := 0x00060a93.
Lemma F_177e8 : fetch_word Plain.M.loaded_segments (0x178e4 : word) = Some W_177e8.
Proof. vm_refl. Qed.
Lemma D_177e8 : decode_any W_177e8 = Some (OpImm ALU_ADD 21 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_177ec : bv 32 := 0x00058913.
Lemma F_177ec : fetch_word Plain.M.loaded_segments (0x178e8 : word) = Some W_177ec.
Proof. vm_refl. Qed.
Lemma D_177ec : decode_any W_177ec = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_177f0 : bv 32 := 0x00050413.
Lemma F_177f0 : fetch_word Plain.M.loaded_segments (0x178ec : word) = Some W_177f0.
Proof. vm_refl. Qed.
Lemma D_177f0 : decode_any W_177f0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_177f4 : bv 32 := 0x00b66533.
Lemma F_177f4 : fetch_word Plain.M.loaded_segments (0x178f0 : word) = Some W_177f4.
Proof. vm_refl. Qed.
Lemma D_177f4 : decode_any W_177f4 = Some (Op ALU_OR 10 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_177f8 : bv 32 := 0x00e6e5b3.
Lemma F_177f8 : fetch_word Plain.M.loaded_segments (0x178f4 : word) = Some W_177f8.
Proof. vm_refl. Qed.
Lemma D_177f8 : decode_any W_177f8 = Some (Op ALU_OR 11 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_177fc : bv 32 := 0x00b56533.
Lemma F_177fc : fetch_word Plain.M.loaded_segments (0x178f8 : word) = Some W_177fc.
Proof. vm_refl. Qed.
Lemma D_177fc : decode_any W_177fc = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17800 : bv 32 := 0x14054663.
Lemma F_17800 : fetch_word Plain.M.loaded_segments (0x178fc : word) = Some W_17800.
Proof. vm_refl. Qed.
Lemma D_17800 : decode_any W_17800 = Some (Branch BC_LT 10 0 332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17804 : bv 32 := 0x00078d13.
Lemma F_17804 : fetch_word Plain.M.loaded_segments (0x17900 : word) = Some W_17804.
Proof. vm_refl. Qed.
Lemma D_17804 : decode_any W_17804 = Some (OpImm ALU_ADD 26 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17808 : bv 32 := 0x01c10593.
Lemma F_17808 : fetch_word Plain.M.loaded_segments (0x17904 : word) = Some W_17808.
Proof. vm_refl. Qed.
Lemma D_17808 : decode_any W_17808 = Some (OpImm ALU_ADD 11 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1780c : bv 32 := 0x01810613.
Lemma F_1780c : fetch_word Plain.M.loaded_segments (0x17908 : word) = Some W_1780c.
Proof. vm_refl. Qed.
Lemma D_1780c : decode_any W_1780c = Some (OpImm ALU_ADD 12 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17810 : bv 32 := 0x01410693.
Lemma F_17810 : fetch_word Plain.M.loaded_segments (0x1790c : word) = Some W_17810.
Proof. vm_refl. Qed.
Lemma D_17810 : decode_any W_17810 = Some (OpImm ALU_ADD 13 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17814 : bv 32 := 0x00040513.
Lemma F_17814 : fetch_word Plain.M.loaded_segments (0x17910 : word) = Some W_17814.
Proof. vm_refl. Qed.
Lemma D_17814 : decode_any W_17814 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17818 : bv 32 := 0xd20fe0ef.
Lemma F_17818 : fetch_word Plain.M.loaded_segments (0x17914 : word) = Some W_17818.
Proof. vm_refl. Qed.
Lemma D_17818 : decode_any W_17818 = Some (Jal 1 2090272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1781c : bv 32 := 0x01c12503.
Lemma F_1781c : fetch_word Plain.M.loaded_segments (0x17918 : word) = Some W_1781c.
Proof. vm_refl. Qed.
Lemma D_1781c : decode_any W_1781c = Some (Load SZ4 true 10 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17820 : bv 32 := 0x01812583.
Lemma F_17820 : fetch_word Plain.M.loaded_segments (0x1791c : word) = Some W_17820.
Proof. vm_refl. Qed.
Lemma D_17820 : decode_any W_17820 = Some (Load SZ4 true 11 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17824 : bv 32 := 0x01412603.
Lemma F_17824 : fetch_word Plain.M.loaded_segments (0x17920 : word) = Some W_17824.
Proof. vm_refl. Qed.
Lemma D_17824 : decode_any W_17824 = Some (Load SZ4 true 12 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17828 : bv 32 := 0x01250c3b.
Lemma F_17828 : fetch_word Plain.M.loaded_segments (0x17924 : word) = Some W_17828.
Proof. vm_refl. Qed.
Lemma D_17828 : decode_any W_17828 = Some (Op32 ALU_ADD 24 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1782c : bv 32 := 0x00958bbb.
Lemma F_1782c : fetch_word Plain.M.loaded_segments (0x17928 : word) = Some W_1782c.
Proof. vm_refl. Qed.
Lemma D_1782c : decode_any W_1782c = Some (Op32 ALU_ADD 23 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17830 : bv 32 := 0x015c0b3b.
Lemma F_17830 : fetch_word Plain.M.loaded_segments (0x1792c : word) = Some W_17830.
Proof. vm_refl. Qed.
Lemma D_17830 : decode_any W_17830 = Some (Op32 ALU_ADD 22 24 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17834 : bv 32 := 0x014b8cbb.
Lemma F_17834 : fetch_word Plain.M.loaded_segments (0x17930 : word) = Some W_17834.
Proof. vm_refl. Qed.
Lemma D_17834 : decode_any W_17834 = Some (Op32 ALU_ADD 25 23 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17838 : bv 32 := 0x000b0513.
Lemma F_17838 : fetch_word Plain.M.loaded_segments (0x17934 : word) = Some W_17838.
Proof. vm_refl. Qed.
Lemma D_17838 : decode_any W_17838 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1783c : bv 32 := 0x000c8593.
Lemma F_1783c : fetch_word Plain.M.loaded_segments (0x17938 : word) = Some W_1783c.
Proof. vm_refl. Qed.
Lemma D_1783c : decode_any W_1783c = Some (OpImm ALU_ADD 11 25 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17840 : bv 32 := 0xd39fd0ef.
Lemma F_17840 : fetch_word Plain.M.loaded_segments (0x1793c : word) = Some W_17840.
Proof. vm_refl. Qed.
Lemma D_17840 : decode_any W_17840 = Some (Jal 1 2088248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17844 : bv 32 := 0x16050463.
Lemma F_17844 : fetch_word Plain.M.loaded_segments (0x17940 : word) = Some W_17844.
Proof. vm_refl. Qed.
Lemma D_17844 : decode_any W_17844 = Some (Branch BC_EQ 10 0 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17848 : bv 32 := 0x00050993.
Lemma F_17848 : fetch_word Plain.M.loaded_segments (0x17944 : word) = Some W_17848.
Proof. vm_refl. Qed.
Lemma D_17848 : decode_any W_17848 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1784c : bv 32 := 0x00040593.
Lemma F_1784c : fetch_word Plain.M.loaded_segments (0x17948 : word) = Some W_1784c.
Proof. vm_refl. Qed.
Lemma D_1784c : decode_any W_1784c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17850 : bv 32 := 0xe38fe0ef.
Lemma F_17850 : fetch_word Plain.M.loaded_segments (0x1794c : word) = Some W_17850.
Proof. vm_refl. Qed.
Lemma D_17850 : decode_any W_17850 = Some (Jal 1 2090552, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17854 : bv 32 := 0x00098513.
Lemma F_17854 : fetch_word Plain.M.loaded_segments (0x17950 : word) = Some W_17854.
Proof. vm_refl. Qed.
Lemma D_17854 : decode_any W_17854 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17858 : bv 32 := 0x00040593.
Lemma F_17858 : fetch_word Plain.M.loaded_segments (0x17954 : word) = Some W_17858.
Proof. vm_refl. Qed.
Lemma D_17858 : decode_any W_17858 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1785c : bv 32 := 0xeb4fe0ef.
Lemma F_1785c : fetch_word Plain.M.loaded_segments (0x17958 : word) = Some W_1785c.
Proof. vm_refl. Qed.
Lemma D_1785c : decode_any W_1785c = Some (Jal 1 2090676, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17860 : bv 32 := 0x020d0063.
Lemma F_17860 : fetch_word Plain.M.loaded_segments (0x1795c : word) = Some W_17860.
Proof. vm_refl. Qed.
Lemma D_17860 : decode_any W_17860 = Some (Branch BC_EQ 26 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17864 : bv 32 := 0x000d0593.
Lemma F_17864 : fetch_word Plain.M.loaded_segments (0x17960 : word) = Some W_17864.
Proof. vm_refl. Qed.
Lemma D_17864 : decode_any W_17864 = Some (OpImm ALU_ADD 11 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17868 : bv 32 := 0x01416503.
Lemma F_17868 : fetch_word Plain.M.loaded_segments (0x17964 : word) = Some W_17868.
Proof. vm_refl. Qed.
Lemma D_17868 : decode_any W_17868 = Some (Load SZ4 false 10 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1786c : bv 32 := 0x02000613.
Lemma F_1786c : fetch_word Plain.M.loaded_segments (0x17968 : word) = Some W_1786c.
Proof. vm_refl. Qed.
Lemma D_1786c : decode_any W_1786c = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17870 : bv 32 := 0x16c51c63.
Lemma F_17870 : fetch_word Plain.M.loaded_segments (0x1796c : word) = Some W_17870.
Proof. vm_refl. Qed.
Lemma D_17870 : decode_any W_17870 = Some (Branch BC_NE 10 12 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1787c : bv 32 := 0x00f00d13.
Lemma F_1787c : fetch_word Plain.M.loaded_segments (0x17978 : word) = Some W_1787c.
Proof. vm_refl. Qed.
Lemma D_1787c : decode_any W_1787c = Some (OpImm ALU_ADD 26 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17880 : bv 32 := 0x00013023.
Lemma F_17880 : fetch_word Plain.M.loaded_segments (0x1797c : word) = Some W_17880.
Proof. vm_refl. Qed.
Lemma D_17880 : decode_any W_17880 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17884 : bv 32 := 0x00098513.
Lemma F_17884 : fetch_word Plain.M.loaded_segments (0x17980 : word) = Some W_17884.
Proof. vm_refl. Qed.
Lemma D_17884 : decode_any W_17884 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17888 : bv 32 := 0x00000593.
Lemma F_17888 : fetch_word Plain.M.loaded_segments (0x17984 : word) = Some W_17888.
Proof. vm_refl. Qed.
Lemma D_17888 : decode_any W_17888 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1788c : bv 32 := 0x00000613.
Lemma F_1788c : fetch_word Plain.M.loaded_segments (0x17988 : word) = Some W_1788c.
Proof. vm_refl. Qed.
Lemma D_1788c : decode_any W_1788c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17890 : bv 32 := 0x00090693.
Lemma F_17890 : fetch_word Plain.M.loaded_segments (0x1798c : word) = Some W_17890.
Proof. vm_refl. Qed.
Lemma D_17890 : decode_any W_17890 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17894 : bv 32 := 0x000c8713.
Lemma F_17894 : fetch_word Plain.M.loaded_segments (0x17990 : word) = Some W_17894.
Proof. vm_refl. Qed.
Lemma D_17894 : decode_any W_17894 = Some (OpImm ALU_ADD 14 25 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17898 : bv 32 := 0x000d0793.
Lemma F_17898 : fetch_word Plain.M.loaded_segments (0x17994 : word) = Some W_17898.
Proof. vm_refl. Qed.
Lemma D_17898 : decode_any W_17898 = Some (OpImm ALU_ADD 15 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1789c : bv 32 := 0x00000813.
Lemma F_1789c : fetch_word Plain.M.loaded_segments (0x17998 : word) = Some W_1789c.
Proof. vm_refl. Qed.
Lemma D_1789c : decode_any W_1789c = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_178a0 : bv 32 := 0x00000893.
Lemma F_178a0 : fetch_word Plain.M.loaded_segments (0x1799c : word) = Some W_178a0.
Proof. vm_refl. Qed.
Lemma D_178a0 : decode_any W_178a0 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_178a4 : bv 32 := 0x485040ef.
Lemma F_178a4 : fetch_word Plain.M.loaded_segments (0x179a0 : word) = Some W_178a4.
Proof. vm_refl. Qed.
Lemma D_178a4 : decode_any W_178a4 = Some (Jal 1 19588, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_178a8 : bv 32 := 0x00013023.
Lemma F_178a8 : fetch_word Plain.M.loaded_segments (0x179a4 : word) = Some W_178a8.
Proof. vm_refl. Qed.
Lemma D_178a8 : decode_any W_178a8 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_178ac : bv 32 := 0x00098513.
Lemma F_178ac : fetch_word Plain.M.loaded_segments (0x179a8 : word) = Some W_178ac.
Proof. vm_refl. Qed.
Lemma D_178ac : decode_any W_178ac = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_178b0 : bv 32 := 0x000c0593.
Lemma F_178b0 : fetch_word Plain.M.loaded_segments (0x179ac : word) = Some W_178b0.
Proof. vm_refl. Qed.
Lemma D_178b0 : decode_any W_178b0 = Some (OpImm ALU_ADD 11 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_178b4 : bv 32 := 0x00000613.
Lemma F_178b4 : fetch_word Plain.M.loaded_segments (0x179b0 : word) = Some W_178b4.
Proof. vm_refl. Qed.
Lemma D_178b4 : decode_any W_178b4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_178b8 : bv 32 := 0x000a8693.
Lemma F_178b8 : fetch_word Plain.M.loaded_segments (0x179b4 : word) = Some W_178b8.
Proof. vm_refl. Qed.
Lemma D_178b8 : decode_any W_178b8 = Some (OpImm ALU_ADD 13 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_178bc : bv 32 := 0x000c8713.
Lemma F_178bc : fetch_word Plain.M.loaded_segments (0x179b8 : word) = Some W_178bc.
Proof. vm_refl. Qed.
Lemma D_178bc : decode_any W_178bc = Some (OpImm ALU_ADD 14 25 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_178c0 : bv 32 := 0x000d0793.
Lemma F_178c0 : fetch_word Plain.M.loaded_segments (0x179bc : word) = Some W_178c0.
Proof. vm_refl. Qed.
Lemma D_178c0 : decode_any W_178c0 = Some (OpImm ALU_ADD 15 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_178c4 : bv 32 := 0x00000813.
Lemma F_178c4 : fetch_word Plain.M.loaded_segments (0x179c0 : word) = Some W_178c4.
Proof. vm_refl. Qed.
Lemma D_178c4 : decode_any W_178c4 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_178c8 : bv 32 := 0x00000893.
Lemma F_178c8 : fetch_word Plain.M.loaded_segments (0x179c4 : word) = Some W_178c8.
Proof. vm_refl. Qed.
Lemma D_178c8 : decode_any W_178c8 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_178cc : bv 32 := 0x45d040ef.
Lemma F_178cc : fetch_word Plain.M.loaded_segments (0x179c8 : word) = Some W_178cc.
Proof. vm_refl. Qed.
Lemma D_178cc : decode_any W_178cc = Some (Jal 1 19548, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_178d0 : bv 32 := 0x00013023.
Lemma F_178d0 : fetch_word Plain.M.loaded_segments (0x179cc : word) = Some W_178d0.
Proof. vm_refl. Qed.
Lemma D_178d0 : decode_any W_178d0 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_178d4 : bv 32 := 0x00098513.
Lemma F_178d4 : fetch_word Plain.M.loaded_segments (0x179d0 : word) = Some W_178d4.
Proof. vm_refl. Qed.
Lemma D_178d4 : decode_any W_178d4 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_178d8 : bv 32 := 0x00000593.
Lemma F_178d8 : fetch_word Plain.M.loaded_segments (0x179d4 : word) = Some W_178d8.
Proof. vm_refl. Qed.
Lemma D_178d8 : decode_any W_178d8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_178dc : bv 32 := 0x00000613.
Lemma F_178dc : fetch_word Plain.M.loaded_segments (0x179d8 : word) = Some W_178dc.
Proof. vm_refl. Qed.
Lemma D_178dc : decode_any W_178dc = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_178e0 : bv 32 := 0x000b0693.
Lemma F_178e0 : fetch_word Plain.M.loaded_segments (0x179dc : word) = Some W_178e0.
Proof. vm_refl. Qed.
Lemma D_178e0 : decode_any W_178e0 = Some (OpImm ALU_ADD 13 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_178e4 : bv 32 := 0x00048713.
Lemma F_178e4 : fetch_word Plain.M.loaded_segments (0x179e0 : word) = Some W_178e4.
Proof. vm_refl. Qed.
Lemma D_178e4 : decode_any W_178e4 = Some (OpImm ALU_ADD 14 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_178e8 : bv 32 := 0x000d0793.
Lemma F_178e8 : fetch_word Plain.M.loaded_segments (0x179e4 : word) = Some W_178e8.
Proof. vm_refl. Qed.
Lemma D_178e8 : decode_any W_178e8 = Some (OpImm ALU_ADD 15 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_178ec : bv 32 := 0x00000813.
Lemma F_178ec : fetch_word Plain.M.loaded_segments (0x179e8 : word) = Some W_178ec.
Proof. vm_refl. Qed.
Lemma D_178ec : decode_any W_178ec = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_178f0 : bv 32 := 0x00000893.
Lemma F_178f0 : fetch_word Plain.M.loaded_segments (0x179ec : word) = Some W_178f0.
Proof. vm_refl. Qed.
Lemma D_178f0 : decode_any W_178f0 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_178f4 : bv 32 := 0x435040ef.
Lemma F_178f4 : fetch_word Plain.M.loaded_segments (0x179f0 : word) = Some W_178f4.
Proof. vm_refl. Qed.
Lemma D_178f4 : decode_any W_178f4 = Some (Jal 1 19508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_178f8 : bv 32 := 0x00013023.
Lemma F_178f8 : fetch_word Plain.M.loaded_segments (0x179f4 : word) = Some W_178f8.
Proof. vm_refl. Qed.
Lemma D_178f8 : decode_any W_178f8 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_178fc : bv 32 := 0x00098513.
Lemma F_178fc : fetch_word Plain.M.loaded_segments (0x179f8 : word) = Some W_178fc.
Proof. vm_refl. Qed.
Lemma D_178fc : decode_any W_178fc = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17900 : bv 32 := 0x00000593.
Lemma F_17900 : fetch_word Plain.M.loaded_segments (0x179fc : word) = Some W_17900.
Proof. vm_refl. Qed.
Lemma D_17900 : decode_any W_17900 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17904 : bv 32 := 0x000b8613.
Lemma F_17904 : fetch_word Plain.M.loaded_segments (0x17a00 : word) = Some W_17904.
Proof. vm_refl. Qed.
Lemma D_17904 : decode_any W_17904 = Some (OpImm ALU_ADD 12 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17908 : bv 32 := 0x000b0693.
Lemma F_17908 : fetch_word Plain.M.loaded_segments (0x17a04 : word) = Some W_17908.
Proof. vm_refl. Qed.
Lemma D_17908 : decode_any W_17908 = Some (OpImm ALU_ADD 13 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1790c : bv 32 := 0x000a0713.
Lemma F_1790c : fetch_word Plain.M.loaded_segments (0x17a08 : word) = Some W_1790c.
Proof. vm_refl. Qed.
Lemma D_1790c : decode_any W_1790c = Some (OpImm ALU_ADD 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17910 : bv 32 := 0x000d0793.
Lemma F_17910 : fetch_word Plain.M.loaded_segments (0x17a0c : word) = Some W_17910.
Proof. vm_refl. Qed.
Lemma D_17910 : decode_any W_17910 = Some (OpImm ALU_ADD 15 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17914 : bv 32 := 0x00000813.
Lemma F_17914 : fetch_word Plain.M.loaded_segments (0x17a10 : word) = Some W_17914.
Proof. vm_refl. Qed.
Lemma D_17914 : decode_any W_17914 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17918 : bv 32 := 0x00000893.
Lemma F_17918 : fetch_word Plain.M.loaded_segments (0x17a14 : word) = Some W_17918.
Proof. vm_refl. Qed.
Lemma D_17918 : decode_any W_17918 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1791c : bv 32 := 0x40d040ef.
Lemma F_1791c : fetch_word Plain.M.loaded_segments (0x17a18 : word) = Some W_1791c.
Proof. vm_refl. Qed.
Lemma D_1791c : decode_any W_1791c = Some (Jal 1 19468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17920 : bv 32 := 0x0e00006f.
Lemma F_17920 : fetch_word Plain.M.loaded_segments (0x17a1c : word) = Some W_17920.
Proof. vm_refl. Qed.
Lemma D_17920 : decode_any W_17920 = Some (Jal 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179ac : bv 32 := 0x00013517.
Lemma F_179ac : fetch_word Plain.M.loaded_segments (0x17aa8 : word) = Some W_179ac.
Proof. vm_refl. Qed.
Lemma D_179ac : decode_any W_179ac = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179b0 : bv 32 := 0xf9853503.
Lemma F_179b0 : fetch_word Plain.M.loaded_segments (0x17aac : word) = Some W_179b0.
Proof. vm_refl. Qed.
Lemma D_179b0 : decode_any W_179b0 = Some (Load SZ8 true 10 10 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179b4 : bv 32 := 0x00052503.
Lemma F_179b4 : fetch_word Plain.M.loaded_segments (0x17ab0 : word) = Some W_179b4.
Proof. vm_refl. Qed.
Lemma D_179b4 : decode_any W_179b4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179b8 : bv 32 := 0x00500593.
Lemma F_179b8 : fetch_word Plain.M.loaded_segments (0x17ab4 : word) = Some W_179b8.
Proof. vm_refl. Qed.
Lemma D_179b8 : decode_any W_179b8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179bc : bv 32 := 0x02a5c263.
Lemma F_179bc : fetch_word Plain.M.loaded_segments (0x17ab8 : word) = Some W_179bc.
Proof. vm_refl. Qed.
Lemma D_179bc : decode_any W_179bc = Some (Branch BC_LT 11 10 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179c0 : bv 32 := 0xffff9517.
Lemma F_179c0 : fetch_word Plain.M.loaded_segments (0x17abc : word) = Some W_179c0.
Proof. vm_refl. Qed.
Lemma D_179c0 : decode_any W_179c0 = Some (Auipc 10 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179c4 : bv 32 := 0xffff9597.
Lemma F_179c4 : fetch_word Plain.M.loaded_segments (0x17ac0 : word) = Some W_179c4.
Proof. vm_refl. Qed.
Lemma D_179c4 : decode_any W_179c4 = Some (Auipc 11 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179c8 : bv 32 := 0xa0150513.
Lemma F_179c8 : fetch_word Plain.M.loaded_segments (0x17ac4 : word) = Some W_179c8.
Proof. vm_refl. Qed.
Lemma D_179c8 : decode_any W_179c8 = Some (OpImm ALU_ADD 10 10 2561, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179cc : bv 32 := 0x0e858593.
Lemma F_179cc : fetch_word Plain.M.loaded_segments (0x17ac8 : word) = Some W_179cc.
Proof. vm_refl. Qed.
Lemma D_179cc : decode_any W_179cc = Some (OpImm ALU_ADD 11 11 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179d0 : bv 32 := 0x00000613.
Lemma F_179d0 : fetch_word Plain.M.loaded_segments (0x17acc : word) = Some W_179d0.
Proof. vm_refl. Qed.
Lemma D_179d0 : decode_any W_179d0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179d4 : bv 32 := 0x96dfd0ef.
Lemma F_179d4 : fetch_word Plain.M.loaded_segments (0x17ad0 : word) = Some W_179d4.
Proof. vm_refl. Qed.
Lemma D_179d4 : decode_any W_179d4 = Some (Jal 1 2087276, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179d8 : bv 32 := 0x00050993.
Lemma F_179d8 : fetch_word Plain.M.loaded_segments (0x17ad4 : word) = Some W_179d8.
Proof. vm_refl. Qed.
Lemma D_179d8 : decode_any W_179d8 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179dc : bv 32 := 0x04c0006f.
Lemma F_179dc : fetch_word Plain.M.loaded_segments (0x17ad8 : word) = Some W_179dc.
Proof. vm_refl. Qed.
Lemma D_179dc : decode_any W_179dc = Some (Jal 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179e8 : bv 32 := 0xfff00613.
Lemma F_179e8 : fetch_word Plain.M.loaded_segments (0x17ae4 : word) = Some W_179e8.
Proof. vm_refl. Qed.
Lemma D_179e8 : decode_any W_179e8 = Some (OpImm ALU_ADD 12 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179ec : bv 32 := 0x00a6153b.
Lemma F_179ec : fetch_word Plain.M.loaded_segments (0x17ae8 : word) = Some W_179ec.
Proof. vm_refl. Qed.
Lemma D_179ec : decode_any W_179ec = Some (Op32 ALU_SLL 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179f0 : bv 32 := 0xfff54513.
Lemma F_179f0 : fetch_word Plain.M.loaded_segments (0x17aec : word) = Some W_179f0.
Proof. vm_refl. Qed.
Lemma D_179f0 : decode_any W_179f0 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_179f4 : bv 32 := 0xe8a5f4e3.
Lemma F_179f4 : fetch_word Plain.M.loaded_segments (0x17af0 : word) = Some W_179f4.
Proof. vm_refl. Qed.
Lemma D_179f4 : decode_any W_179f4 = Some (Branch BC_GEU 11 10 7816, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a00 : bv 32 := 0x01c12683.
Lemma F_17a00 : fetch_word Plain.M.loaded_segments (0x17afc : word) = Some W_17a00.
Proof. vm_refl. Qed.
Lemma D_17a00 : decode_any W_17a00 = Some (Load SZ4 true 13 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a04 : bv 32 := 0x01812703.
Lemma F_17a04 : fetch_word Plain.M.loaded_segments (0x17b00 : word) = Some W_17a04.
Proof. vm_refl. Qed.
Lemma D_17a04 : decode_any W_17a04 = Some (Load SZ4 true 14 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a08 : bv 32 := 0x00c00793.
Lemma F_17a08 : fetch_word Plain.M.loaded_segments (0x17b04 : word) = Some W_17a08.
Proof. vm_refl. Qed.
Lemma D_17a08 : decode_any W_17a08 = Some (OpImm ALU_ADD 15 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a0c : bv 32 := 0x00013023.
Lemma F_17a0c : fetch_word Plain.M.loaded_segments (0x17b08 : word) = Some W_17a0c.
Proof. vm_refl. Qed.
Lemma D_17a0c : decode_any W_17a0c = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a10 : bv 32 := 0x00098513.
Lemma F_17a10 : fetch_word Plain.M.loaded_segments (0x17b0c : word) = Some W_17a10.
Proof. vm_refl. Qed.
Lemma D_17a10 : decode_any W_17a10 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a14 : bv 32 := 0x00090593.
Lemma F_17a14 : fetch_word Plain.M.loaded_segments (0x17b10 : word) = Some W_17a14.
Proof. vm_refl. Qed.
Lemma D_17a14 : decode_any W_17a14 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a18 : bv 32 := 0x00048613.
Lemma F_17a18 : fetch_word Plain.M.loaded_segments (0x17b14 : word) = Some W_17a18.
Proof. vm_refl. Qed.
Lemma D_17a18 : decode_any W_17a18 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a1c : bv 32 := 0x00040813.
Lemma F_17a1c : fetch_word Plain.M.loaded_segments (0x17b18 : word) = Some W_17a1c.
Proof. vm_refl. Qed.
Lemma D_17a1c : decode_any W_17a1c = Some (OpImm ALU_ADD 16 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a20 : bv 32 := 0x00000893.
Lemma F_17a20 : fetch_word Plain.M.loaded_segments (0x17b1c : word) = Some W_17a20.
Proof. vm_refl. Qed.
Lemma D_17a20 : decode_any W_17a20 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a24 : bv 32 := 0x305040ef.
Lemma F_17a24 : fetch_word Plain.M.loaded_segments (0x17b20 : word) = Some W_17a24.
Proof. vm_refl. Qed.
Lemma D_17a24 : decode_any W_17a24 = Some (Jal 1 19204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a28 : bv 32 := 0x00098513.
Lemma F_17a28 : fetch_word Plain.M.loaded_segments (0x17b24 : word) = Some W_17a28.
Proof. vm_refl. Qed.
Lemma D_17a28 : decode_any W_17a28 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a2c : bv 32 := 0x07813083.
Lemma F_17a2c : fetch_word Plain.M.loaded_segments (0x17b28 : word) = Some W_17a2c.
Proof. vm_refl. Qed.
Lemma D_17a2c : decode_any W_17a2c = Some (Load SZ8 true 1 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a30 : bv 32 := 0x07013403.
Lemma F_17a30 : fetch_word Plain.M.loaded_segments (0x17b2c : word) = Some W_17a30.
Proof. vm_refl. Qed.
Lemma D_17a30 : decode_any W_17a30 = Some (Load SZ8 true 8 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a34 : bv 32 := 0x06813483.
Lemma F_17a34 : fetch_word Plain.M.loaded_segments (0x17b30 : word) = Some W_17a34.
Proof. vm_refl. Qed.
Lemma D_17a34 : decode_any W_17a34 = Some (Load SZ8 true 9 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a38 : bv 32 := 0x06013903.
Lemma F_17a38 : fetch_word Plain.M.loaded_segments (0x17b34 : word) = Some W_17a38.
Proof. vm_refl. Qed.
Lemma D_17a38 : decode_any W_17a38 = Some (Load SZ8 true 18 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a3c : bv 32 := 0x05813983.
Lemma F_17a3c : fetch_word Plain.M.loaded_segments (0x17b38 : word) = Some W_17a3c.
Proof. vm_refl. Qed.
Lemma D_17a3c : decode_any W_17a3c = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a40 : bv 32 := 0x05013a03.
Lemma F_17a40 : fetch_word Plain.M.loaded_segments (0x17b3c : word) = Some W_17a40.
Proof. vm_refl. Qed.
Lemma D_17a40 : decode_any W_17a40 = Some (Load SZ8 true 20 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a44 : bv 32 := 0x04813a83.
Lemma F_17a44 : fetch_word Plain.M.loaded_segments (0x17b40 : word) = Some W_17a44.
Proof. vm_refl. Qed.
Lemma D_17a44 : decode_any W_17a44 = Some (Load SZ8 true 21 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a48 : bv 32 := 0x04013b03.
Lemma F_17a48 : fetch_word Plain.M.loaded_segments (0x17b44 : word) = Some W_17a48.
Proof. vm_refl. Qed.
Lemma D_17a48 : decode_any W_17a48 = Some (Load SZ8 true 22 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a4c : bv 32 := 0x03813b83.
Lemma F_17a4c : fetch_word Plain.M.loaded_segments (0x17b48 : word) = Some W_17a4c.
Proof. vm_refl. Qed.
Lemma D_17a4c : decode_any W_17a4c = Some (Load SZ8 true 23 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a50 : bv 32 := 0x03013c03.
Lemma F_17a50 : fetch_word Plain.M.loaded_segments (0x17b4c : word) = Some W_17a50.
Proof. vm_refl. Qed.
Lemma D_17a50 : decode_any W_17a50 = Some (Load SZ8 true 24 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a54 : bv 32 := 0x02813c83.
Lemma F_17a54 : fetch_word Plain.M.loaded_segments (0x17b50 : word) = Some W_17a54.
Proof. vm_refl. Qed.
Lemma D_17a54 : decode_any W_17a54 = Some (Load SZ8 true 25 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a58 : bv 32 := 0x02013d03.
Lemma F_17a58 : fetch_word Plain.M.loaded_segments (0x17b54 : word) = Some W_17a58.
Proof. vm_refl. Qed.
Lemma D_17a58 : decode_any W_17a58 = Some (Load SZ8 true 26 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a5c : bv 32 := 0x08010113.
Lemma F_17a5c : fetch_word Plain.M.loaded_segments (0x17b58 : word) = Some W_17a5c.
Proof. vm_refl. Qed.
Lemma D_17a5c : decode_any W_17a5c = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a60 : bv 32 := 0x00008067.
Lemma F_17a60 : fetch_word Plain.M.loaded_segments (0x17b5c : word) = Some W_17a60.
Proof. vm_refl. Qed.
Lemma D_17a60 : decode_any W_17a60 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a64 : bv 32 := 0xfa010113.
Lemma F_17a64 : fetch_word Plain.M.loaded_segments (0x17b60 : word) = Some W_17a64.
Proof. vm_refl. Qed.
Lemma D_17a64 : decode_any W_17a64 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a68 : bv 32 := 0x04113c23.
Lemma F_17a68 : fetch_word Plain.M.loaded_segments (0x17b64 : word) = Some W_17a68.
Proof. vm_refl. Qed.
Lemma D_17a68 : decode_any W_17a68 = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a6c : bv 32 := 0x04813823.
Lemma F_17a6c : fetch_word Plain.M.loaded_segments (0x17b68 : word) = Some W_17a6c.
Proof. vm_refl. Qed.
Lemma D_17a6c : decode_any W_17a6c = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a70 : bv 32 := 0x04913423.
Lemma F_17a70 : fetch_word Plain.M.loaded_segments (0x17b6c : word) = Some W_17a70.
Proof. vm_refl. Qed.
Lemma D_17a70 : decode_any W_17a70 = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a74 : bv 32 := 0x05213023.
Lemma F_17a74 : fetch_word Plain.M.loaded_segments (0x17b70 : word) = Some W_17a74.
Proof. vm_refl. Qed.
Lemma D_17a74 : decode_any W_17a74 = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a78 : bv 32 := 0x03313c23.
Lemma F_17a78 : fetch_word Plain.M.loaded_segments (0x17b74 : word) = Some W_17a78.
Proof. vm_refl. Qed.
Lemma D_17a78 : decode_any W_17a78 = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a7c : bv 32 := 0x03413823.
Lemma F_17a7c : fetch_word Plain.M.loaded_segments (0x17b78 : word) = Some W_17a7c.
Proof. vm_refl. Qed.
Lemma D_17a7c : decode_any W_17a7c = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a80 : bv 32 := 0x03513423.
Lemma F_17a80 : fetch_word Plain.M.loaded_segments (0x17b7c : word) = Some W_17a80.
Proof. vm_refl. Qed.
Lemma D_17a80 : decode_any W_17a80 = Some (Store SZ8 2 21 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a84 : bv 32 := 0x03713023.
Lemma F_17a84 : fetch_word Plain.M.loaded_segments (0x17b80 : word) = Some W_17a84.
Proof. vm_refl. Qed.
Lemma D_17a84 : decode_any W_17a84 = Some (Store SZ8 2 23 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a88 : bv 32 := 0x10050063.
Lemma F_17a88 : fetch_word Plain.M.loaded_segments (0x17b84 : word) = Some W_17a88.
Proof. vm_refl. Qed.
Lemma D_17a88 : decode_any W_17a88 = Some (Branch BC_EQ 10 0 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a8c : bv 32 := 0x00068413.
Lemma F_17a8c : fetch_word Plain.M.loaded_segments (0x17b88 : word) = Some W_17a8c.
Proof. vm_refl. Qed.
Lemma D_17a8c : decode_any W_17a8c = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a90 : bv 32 := 0x00060993.
Lemma F_17a90 : fetch_word Plain.M.loaded_segments (0x17b8c : word) = Some W_17a90.
Proof. vm_refl. Qed.
Lemma D_17a90 : decode_any W_17a90 = Some (OpImm ALU_ADD 19 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a94 : bv 32 := 0x00058493.
Lemma F_17a94 : fetch_word Plain.M.loaded_segments (0x17b90 : word) = Some W_17a94.
Proof. vm_refl. Qed.
Lemma D_17a94 : decode_any W_17a94 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a98 : bv 32 := 0x00b665b3.
Lemma F_17a98 : fetch_word Plain.M.loaded_segments (0x17b94 : word) = Some W_17a98.
Proof. vm_refl. Qed.
Lemma D_17a98 : decode_any W_17a98 = Some (Op ALU_OR 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a9c : bv 32 := 0x00e6e633.
Lemma F_17a9c : fetch_word Plain.M.loaded_segments (0x17b98 : word) = Some W_17a9c.
Proof. vm_refl. Qed.
Lemma D_17a9c : decode_any W_17a9c = Some (Op ALU_OR 12 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17aa0 : bv 32 := 0x00c5e5b3.
Lemma F_17aa0 : fetch_word Plain.M.loaded_segments (0x17b9c : word) = Some W_17aa0.
Proof. vm_refl. Qed.
Lemma D_17aa0 : decode_any W_17aa0 = Some (Op ALU_OR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17aa4 : bv 32 := 0x1005c663.
Lemma F_17aa4 : fetch_word Plain.M.loaded_segments (0x17ba0 : word) = Some W_17aa4.
Proof. vm_refl. Qed.
Lemma D_17aa4 : decode_any W_17aa4 = Some (Branch BC_LT 11 0 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17aa8 : bv 32 := 0x00070a13.
Lemma F_17aa8 : fetch_word Plain.M.loaded_segments (0x17ba4 : word) = Some W_17aa8.
Proof. vm_refl. Qed.
Lemma D_17aa8 : decode_any W_17aa8 = Some (OpImm ALU_ADD 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17aac : bv 32 := 0x01c10593.
Lemma F_17aac : fetch_word Plain.M.loaded_segments (0x17ba8 : word) = Some W_17aac.
Proof. vm_refl. Qed.
Lemma D_17aac : decode_any W_17aac = Some (OpImm ALU_ADD 11 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ab0 : bv 32 := 0x01810613.
Lemma F_17ab0 : fetch_word Plain.M.loaded_segments (0x17bac : word) = Some W_17ab0.
Proof. vm_refl. Qed.
Lemma D_17ab0 : decode_any W_17ab0 = Some (OpImm ALU_ADD 12 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ab4 : bv 32 := 0x01410693.
Lemma F_17ab4 : fetch_word Plain.M.loaded_segments (0x17bb0 : word) = Some W_17ab4.
Proof. vm_refl. Qed.
Lemma D_17ab4 : decode_any W_17ab4 = Some (OpImm ALU_ADD 13 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ab8 : bv 32 := 0x00050913.
Lemma F_17ab8 : fetch_word Plain.M.loaded_segments (0x17bb4 : word) = Some W_17ab8.
Proof. vm_refl. Qed.
Lemma D_17ab8 : decode_any W_17ab8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17abc : bv 32 := 0xa7cfe0ef.
Lemma F_17abc : fetch_word Plain.M.loaded_segments (0x17bb8 : word) = Some W_17abc.
Proof. vm_refl. Qed.
Lemma D_17abc : decode_any W_17abc = Some (Jal 1 2089596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ac0 : bv 32 := 0x01c12503.
Lemma F_17ac0 : fetch_word Plain.M.loaded_segments (0x17bbc : word) = Some W_17ac0.
Proof. vm_refl. Qed.
Lemma D_17ac0 : decode_any W_17ac0 = Some (Load SZ4 true 10 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ac4 : bv 32 := 0x009989b3.
Lemma F_17ac4 : fetch_word Plain.M.loaded_segments (0x17bc0 : word) = Some W_17ac4.
Proof. vm_refl. Qed.
Lemma D_17ac4 : decode_any W_17ac4 = Some (Op ALU_ADD 19 19 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ac8 : bv 32 := 0x413509bb.
Lemma F_17ac8 : fetch_word Plain.M.loaded_segments (0x17bc4 : word) = Some W_17ac8.
Proof. vm_refl. Qed.
Lemma D_17ac8 : decode_any W_17ac8 = Some (Op32 ALU_SUB 19 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17acc : bv 32 := 0x13305a63.
Lemma F_17acc : fetch_word Plain.M.loaded_segments (0x17bc8 : word) = Some W_17acc.
Proof. vm_refl. Qed.
Lemma D_17acc : decode_any W_17acc = Some (Branch BC_GE 0 19 308, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ad0 : bv 32 := 0x01812503.
Lemma F_17ad0 : fetch_word Plain.M.loaded_segments (0x17bcc : word) = Some W_17ad0.
Proof. vm_refl. Qed.
Lemma D_17ad0 : decode_any W_17ad0 = Some (Load SZ4 true 10 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ad4 : bv 32 := 0x008a0a33.
Lemma F_17ad4 : fetch_word Plain.M.loaded_segments (0x17bd0 : word) = Some W_17ad4.
Proof. vm_refl. Qed.
Lemma D_17ad4 : decode_any W_17ad4 = Some (Op ALU_ADD 20 20 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ad8 : bv 32 := 0x41450a3b.
Lemma F_17ad8 : fetch_word Plain.M.loaded_segments (0x17bd4 : word) = Some W_17ad8.
Proof. vm_refl. Qed.
Lemma D_17ad8 : decode_any W_17ad8 = Some (Op32 ALU_SUB 20 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17adc : bv 32 := 0x15405663.
Lemma F_17adc : fetch_word Plain.M.loaded_segments (0x17bd8 : word) = Some W_17adc.
Proof. vm_refl. Qed.
Lemma D_17adc : decode_any W_17adc = Some (Branch BC_GE 0 20 332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ae0 : bv 32 := 0x01412603.
Lemma F_17ae0 : fetch_word Plain.M.loaded_segments (0x17bdc : word) = Some W_17ae0.
Proof. vm_refl. Qed.
Lemma D_17ae0 : decode_any W_17ae0 = Some (Load SZ4 true 12 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ae4 : bv 32 := 0x00098513.
Lemma F_17ae4 : fetch_word Plain.M.loaded_segments (0x17be0 : word) = Some W_17ae4.
Proof. vm_refl. Qed.
Lemma D_17ae4 : decode_any W_17ae4 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ae8 : bv 32 := 0x000a0593.
Lemma F_17ae8 : fetch_word Plain.M.loaded_segments (0x17be4 : word) = Some W_17ae8.
Proof. vm_refl. Qed.
Lemma D_17ae8 : decode_any W_17ae8 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17aec : bv 32 := 0xa8dfd0ef.
Lemma F_17aec : fetch_word Plain.M.loaded_segments (0x17be8 : word) = Some W_17aec.
Proof. vm_refl. Qed.
Lemma D_17aec : decode_any W_17aec = Some (Jal 1 2087564, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17af0 : bv 32 := 0x16050063.
Lemma F_17af0 : fetch_word Plain.M.loaded_segments (0x17bec : word) = Some W_17af0.
Proof. vm_refl. Qed.
Lemma D_17af0 : decode_any W_17af0 = Some (Branch BC_EQ 10 0 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17af4 : bv 32 := 0x00050a93.
Lemma F_17af4 : fetch_word Plain.M.loaded_segments (0x17bf0 : word) = Some W_17af4.
Proof. vm_refl. Qed.
Lemma D_17af4 : decode_any W_17af4 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17af8 : bv 32 := 0x00090593.
Lemma F_17af8 : fetch_word Plain.M.loaded_segments (0x17bf4 : word) = Some W_17af8.
Proof. vm_refl. Qed.
Lemma D_17af8 : decode_any W_17af8 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17afc : bv 32 := 0xb8cfe0ef.
Lemma F_17afc : fetch_word Plain.M.loaded_segments (0x17bf8 : word) = Some W_17afc.
Proof. vm_refl. Qed.
Lemma D_17afc : decode_any W_17afc = Some (Jal 1 2089868, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b00 : bv 32 := 0x000a8513.
Lemma F_17b00 : fetch_word Plain.M.loaded_segments (0x17bfc : word) = Some W_17b00.
Proof. vm_refl. Qed.
Lemma D_17b00 : decode_any W_17b00 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b04 : bv 32 := 0x00090593.
Lemma F_17b04 : fetch_word Plain.M.loaded_segments (0x17c00 : word) = Some W_17b04.
Proof. vm_refl. Qed.
Lemma D_17b04 : decode_any W_17b04 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b08 : bv 32 := 0xab0fe0ef.
Lemma F_17b08 : fetch_word Plain.M.loaded_segments (0x17c04 : word) = Some W_17b08.
Proof. vm_refl. Qed.
Lemma D_17b08 : decode_any W_17b08 = Some (Jal 1 2089648, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b0c : bv 32 := 0x000a8513.
Lemma F_17b0c : fetch_word Plain.M.loaded_segments (0x17c08 : word) = Some W_17b0c.
Proof. vm_refl. Qed.
Lemma D_17b0c : decode_any W_17b0c = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b10 : bv 32 := 0x00090593.
Lemma F_17b10 : fetch_word Plain.M.loaded_segments (0x17c0c : word) = Some W_17b10.
Proof. vm_refl. Qed.
Lemma D_17b10 : decode_any W_17b10 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b14 : bv 32 := 0xbfcfe0ef.
Lemma F_17b14 : fetch_word Plain.M.loaded_segments (0x17c10 : word) = Some W_17b14.
Proof. vm_refl. Qed.
Lemma D_17b14 : decode_any W_17b14 = Some (Jal 1 2089980, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b18 : bv 32 := 0x00c00793.
Lemma F_17b18 : fetch_word Plain.M.loaded_segments (0x17c14 : word) = Some W_17b18.
Proof. vm_refl. Qed.
Lemma D_17b18 : decode_any W_17b18 = Some (OpImm ALU_ADD 15 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b1c : bv 32 := 0x00813023.
Lemma F_17b1c : fetch_word Plain.M.loaded_segments (0x17c18 : word) = Some W_17b1c.
Proof. vm_refl. Qed.
Lemma D_17b1c : decode_any W_17b1c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b20 : bv 32 := 0x000a8b93.
Lemma F_17b20 : fetch_word Plain.M.loaded_segments (0x17c1c : word) = Some W_17b20.
Proof. vm_refl. Qed.
Lemma D_17b20 : decode_any W_17b20 = Some (OpImm ALU_ADD 23 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b24 : bv 32 := 0x000a8513.
Lemma F_17b24 : fetch_word Plain.M.loaded_segments (0x17c20 : word) = Some W_17b24.
Proof. vm_refl. Qed.
Lemma D_17b24 : decode_any W_17b24 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b28 : bv 32 := 0x00000593.
Lemma F_17b28 : fetch_word Plain.M.loaded_segments (0x17c24 : word) = Some W_17b28.
Proof. vm_refl. Qed.
Lemma D_17b28 : decode_any W_17b28 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b2c : bv 32 := 0x00000613.
Lemma F_17b2c : fetch_word Plain.M.loaded_segments (0x17c28 : word) = Some W_17b2c.
Proof. vm_refl. Qed.
Lemma D_17b2c : decode_any W_17b2c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b30 : bv 32 := 0x00098693.
Lemma F_17b30 : fetch_word Plain.M.loaded_segments (0x17c2c : word) = Some W_17b30.
Proof. vm_refl. Qed.
Lemma D_17b30 : decode_any W_17b30 = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b34 : bv 32 := 0x000a0713.
Lemma F_17b34 : fetch_word Plain.M.loaded_segments (0x17c30 : word) = Some W_17b34.
Proof. vm_refl. Qed.
Lemma D_17b34 : decode_any W_17b34 = Some (OpImm ALU_ADD 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b38 : bv 32 := 0x00090813.
Lemma F_17b38 : fetch_word Plain.M.loaded_segments (0x17c34 : word) = Some W_17b38.
Proof. vm_refl. Qed.
Lemma D_17b38 : decode_any W_17b38 = Some (OpImm ALU_ADD 16 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b3c : bv 32 := 0x00048893.
Lemma F_17b3c : fetch_word Plain.M.loaded_segments (0x17c38 : word) = Some W_17b3c.
Proof. vm_refl. Qed.
Lemma D_17b3c : decode_any W_17b3c = Some (OpImm ALU_ADD 17 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b40 : bv 32 := 0x1e9040ef.
Lemma F_17b40 : fetch_word Plain.M.loaded_segments (0x17c3c : word) = Some W_17b40.
Proof. vm_refl. Qed.
Lemma D_17b40 : decode_any W_17b40 = Some (Jal 1 18920, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b44 : bv 32 := 0x00090513.
Lemma F_17b44 : fetch_word Plain.M.loaded_segments (0x17c40 : word) = Some W_17b44.
Proof. vm_refl. Qed.
Lemma D_17b44 : decode_any W_17b44 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b48 : bv 32 := 0xc6dfe0ef.
Lemma F_17b48 : fetch_word Plain.M.loaded_segments (0x17c44 : word) = Some W_17b48.
Proof. vm_refl. Qed.
Lemma D_17b48 : decode_any W_17b48 = Some (Jal 1 2092140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b4c : bv 32 := 0x02000593.
Lemma F_17b4c : fetch_word Plain.M.loaded_segments (0x17c48 : word) = Some W_17b4c.
Proof. vm_refl. Qed.
Lemma D_17b4c : decode_any W_17b4c = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b50 : bv 32 := 0x02b51863.
Lemma F_17b50 : fetch_word Plain.M.loaded_segments (0x17c4c : word) = Some W_17b50.
Proof. vm_refl. Qed.
Lemma D_17b50 : decode_any W_17b50 = Some (Branch BC_NE 10 11 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b80 : bv 32 := 0x000b8513.
Lemma F_17b80 : fetch_word Plain.M.loaded_segments (0x17c7c : word) = Some W_17b80.
Proof. vm_refl. Qed.
Lemma D_17b80 : decode_any W_17b80 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b84 : bv 32 := 0x1000006f.
Lemma F_17b84 : fetch_word Plain.M.loaded_segments (0x17c80 : word) = Some W_17b84.
Proof. vm_refl. Qed.
Lemma D_17b84 : decode_any W_17b84 = Some (Jal 0 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b88 : bv 32 := 0x00013517.
Lemma F_17b88 : fetch_word Plain.M.loaded_segments (0x17c84 : word) = Some W_17b88.
Proof. vm_refl. Qed.
Lemma D_17b88 : decode_any W_17b88 = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b8c : bv 32 := 0xdbc53503.
Lemma F_17b8c : fetch_word Plain.M.loaded_segments (0x17c88 : word) = Some W_17b8c.
Proof. vm_refl. Qed.
Lemma D_17b8c : decode_any W_17b8c = Some (Load SZ8 true 10 10 3516, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b90 : bv 32 := 0x00052503.
Lemma F_17b90 : fetch_word Plain.M.loaded_segments (0x17c8c : word) = Some W_17b90.
Proof. vm_refl. Qed.
Lemma D_17b90 : decode_any W_17b90 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b94 : bv 32 := 0x00500593.
Lemma F_17b94 : fetch_word Plain.M.loaded_segments (0x17c90 : word) = Some W_17b94.
Proof. vm_refl. Qed.
Lemma D_17b94 : decode_any W_17b94 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b98 : bv 32 := 0x0ea5c463.
Lemma F_17b98 : fetch_word Plain.M.loaded_segments (0x17c94 : word) = Some W_17b98.
Proof. vm_refl. Qed.
Lemma D_17b98 : decode_any W_17b98 = Some (Branch BC_LT 11 10 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b9c : bv 32 := 0xffff8517.
Lemma F_17b9c : fetch_word Plain.M.loaded_segments (0x17c98 : word) = Some W_17b9c.
Proof. vm_refl. Qed.
Lemma D_17b9c : decode_any W_17b9c = Some (Auipc 10 1048568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ba0 : bv 32 := 0xffff9597.
Lemma F_17ba0 : fetch_word Plain.M.loaded_segments (0x17c9c : word) = Some W_17ba0.
Proof. vm_refl. Qed.
Lemma D_17ba0 : decode_any W_17ba0 = Some (Auipc 11 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ba4 : bv 32 := 0x60050513.
Lemma F_17ba4 : fetch_word Plain.M.loaded_segments (0x17ca0 : word) = Some W_17ba4.
Proof. vm_refl. Qed.
Lemma D_17ba4 : decode_any W_17ba4 = Some (OpImm ALU_ADD 10 10 1536, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ba8 : bv 32 := 0x05858593.
Lemma F_17ba8 : fetch_word Plain.M.loaded_segments (0x17ca4 : word) = Some W_17ba8.
Proof. vm_refl. Qed.
Lemma D_17ba8 : decode_any W_17ba8 = Some (OpImm ALU_ADD 11 11 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17bac : bv 32 := 0x0280006f.
Lemma F_17bac : fetch_word Plain.M.loaded_segments (0x17ca8 : word) = Some W_17bac.
Proof. vm_refl. Qed.
Lemma D_17bac : decode_any W_17bac = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17bd4 : bv 32 := 0x00000613.
Lemma F_17bd4 : fetch_word Plain.M.loaded_segments (0x17cd0 : word) = Some W_17bd4.
Proof. vm_refl. Qed.
Lemma D_17bd4 : decode_any W_17bd4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17bd8 : bv 32 := 0x05813083.
Lemma F_17bd8 : fetch_word Plain.M.loaded_segments (0x17cd4 : word) = Some W_17bd8.
Proof. vm_refl. Qed.
Lemma D_17bd8 : decode_any W_17bd8 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17bdc : bv 32 := 0x05013403.
Lemma F_17bdc : fetch_word Plain.M.loaded_segments (0x17cd8 : word) = Some W_17bdc.
Proof. vm_refl. Qed.
Lemma D_17bdc : decode_any W_17bdc = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17be0 : bv 32 := 0x04813483.
Lemma F_17be0 : fetch_word Plain.M.loaded_segments (0x17cdc : word) = Some W_17be0.
Proof. vm_refl. Qed.
Lemma D_17be0 : decode_any W_17be0 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17be4 : bv 32 := 0x04013903.
Lemma F_17be4 : fetch_word Plain.M.loaded_segments (0x17ce0 : word) = Some W_17be4.
Proof. vm_refl. Qed.
Lemma D_17be4 : decode_any W_17be4 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17be8 : bv 32 := 0x03813983.
Lemma F_17be8 : fetch_word Plain.M.loaded_segments (0x17ce4 : word) = Some W_17be8.
Proof. vm_refl. Qed.
Lemma D_17be8 : decode_any W_17be8 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17bec : bv 32 := 0x03013a03.
Lemma F_17bec : fetch_word Plain.M.loaded_segments (0x17ce8 : word) = Some W_17bec.
Proof. vm_refl. Qed.
Lemma D_17bec : decode_any W_17bec = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17bf0 : bv 32 := 0x02813a83.
Lemma F_17bf0 : fetch_word Plain.M.loaded_segments (0x17cec : word) = Some W_17bf0.
Proof. vm_refl. Qed.
Lemma D_17bf0 : decode_any W_17bf0 = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17bf4 : bv 32 := 0x02013b83.
Lemma F_17bf4 : fetch_word Plain.M.loaded_segments (0x17cf0 : word) = Some W_17bf4.
Proof. vm_refl. Qed.
Lemma D_17bf4 : decode_any W_17bf4 = Some (Load SZ8 true 23 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17bf8 : bv 32 := 0x06010113.
Lemma F_17bf8 : fetch_word Plain.M.loaded_segments (0x17cf4 : word) = Some W_17bf8.
Proof. vm_refl. Qed.
Lemma D_17bf8 : decode_any W_17bf8 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17bfc : bv 32 := 0xf44fd06f.
Lemma F_17bfc : fetch_word Plain.M.loaded_segments (0x17cf8 : word) = Some W_17bfc.
Proof. vm_refl. Qed.
Lemma D_17bfc : decode_any W_17bfc = Some (Jal 0 2086724, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c50 : bv 32 := 0x00013517.
Lemma F_17c50 : fetch_word Plain.M.loaded_segments (0x17d4c : word) = Some W_17c50.
Proof. vm_refl. Qed.
Lemma D_17c50 : decode_any W_17c50 = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c54 : bv 32 := 0xcf453503.
Lemma F_17c54 : fetch_word Plain.M.loaded_segments (0x17d50 : word) = Some W_17c54.
Proof. vm_refl. Qed.
Lemma D_17c54 : decode_any W_17c54 = Some (Load SZ8 true 10 10 3316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c58 : bv 32 := 0x00052503.
Lemma F_17c58 : fetch_word Plain.M.loaded_segments (0x17d54 : word) = Some W_17c58.
Proof. vm_refl. Qed.
Lemma D_17c58 : decode_any W_17c58 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c5c : bv 32 := 0x00500593.
Lemma F_17c5c : fetch_word Plain.M.loaded_segments (0x17d58 : word) = Some W_17c5c.
Proof. vm_refl. Qed.
Lemma D_17c5c : decode_any W_17c5c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c60 : bv 32 := 0x02a5c063.
Lemma F_17c60 : fetch_word Plain.M.loaded_segments (0x17d5c : word) = Some W_17c60.
Proof. vm_refl. Qed.
Lemma D_17c60 : decode_any W_17c60 = Some (Branch BC_LT 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c64 : bv 32 := 0xffff8517.
Lemma F_17c64 : fetch_word Plain.M.loaded_segments (0x17d60 : word) = Some W_17c64.
Proof. vm_refl. Qed.
Lemma D_17c64 : decode_any W_17c64 = Some (Auipc 10 1048568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c68 : bv 32 := 0xffff9597.
Lemma F_17c68 : fetch_word Plain.M.loaded_segments (0x17d64 : word) = Some W_17c68.
Proof. vm_refl. Qed.
Lemma D_17c68 : decode_any W_17c68 = Some (Auipc 11 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c6c : bv 32 := 0x75d50513.
Lemma F_17c6c : fetch_word Plain.M.loaded_segments (0x17d68 : word) = Some W_17c6c.
Proof. vm_refl. Qed.
Lemma D_17c6c : decode_any W_17c6c = Some (OpImm ALU_ADD 10 10 1885, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c70 : bv 32 := 0xf9058593.
Lemma F_17c70 : fetch_word Plain.M.loaded_segments (0x17d6c : word) = Some W_17c70.
Proof. vm_refl. Qed.
Lemma D_17c70 : decode_any W_17c70 = Some (OpImm ALU_ADD 11 11 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c74 : bv 32 := 0x00000613.
Lemma F_17c74 : fetch_word Plain.M.loaded_segments (0x17d70 : word) = Some W_17c74.
Proof. vm_refl. Qed.
Lemma D_17c74 : decode_any W_17c74 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c78 : bv 32 := 0xec8fd0ef.
Lemma F_17c78 : fetch_word Plain.M.loaded_segments (0x17d74 : word) = Some W_17c78.
Proof. vm_refl. Qed.
Lemma D_17c78 : decode_any W_17c78 = Some (Jal 1 2086600, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c7c : bv 32 := 0x0080006f.
Lemma F_17c7c : fetch_word Plain.M.loaded_segments (0x17d78 : word) = Some W_17c7c.
Proof. vm_refl. Qed.
Lemma D_17c7c : decode_any W_17c7c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c84 : bv 32 := 0x05813083.
Lemma F_17c84 : fetch_word Plain.M.loaded_segments (0x17d80 : word) = Some W_17c84.
Proof. vm_refl. Qed.
Lemma D_17c84 : decode_any W_17c84 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c88 : bv 32 := 0x05013403.
Lemma F_17c88 : fetch_word Plain.M.loaded_segments (0x17d84 : word) = Some W_17c88.
Proof. vm_refl. Qed.
Lemma D_17c88 : decode_any W_17c88 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c8c : bv 32 := 0x04813483.
Lemma F_17c8c : fetch_word Plain.M.loaded_segments (0x17d88 : word) = Some W_17c8c.
Proof. vm_refl. Qed.
Lemma D_17c8c : decode_any W_17c8c = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c90 : bv 32 := 0x04013903.
Lemma F_17c90 : fetch_word Plain.M.loaded_segments (0x17d8c : word) = Some W_17c90.
Proof. vm_refl. Qed.
Lemma D_17c90 : decode_any W_17c90 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c94 : bv 32 := 0x03813983.
Lemma F_17c94 : fetch_word Plain.M.loaded_segments (0x17d90 : word) = Some W_17c94.
Proof. vm_refl. Qed.
Lemma D_17c94 : decode_any W_17c94 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c98 : bv 32 := 0x03013a03.
Lemma F_17c98 : fetch_word Plain.M.loaded_segments (0x17d94 : word) = Some W_17c98.
Proof. vm_refl. Qed.
Lemma D_17c98 : decode_any W_17c98 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c9c : bv 32 := 0x02813a83.
Lemma F_17c9c : fetch_word Plain.M.loaded_segments (0x17d98 : word) = Some W_17c9c.
Proof. vm_refl. Qed.
Lemma D_17c9c : decode_any W_17c9c = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ca0 : bv 32 := 0x02013b83.
Lemma F_17ca0 : fetch_word Plain.M.loaded_segments (0x17d9c : word) = Some W_17ca0.
Proof. vm_refl. Qed.
Lemma D_17ca0 : decode_any W_17ca0 = Some (Load SZ8 true 23 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ca4 : bv 32 := 0x06010113.
Lemma F_17ca4 : fetch_word Plain.M.loaded_segments (0x17da0 : word) = Some W_17ca4.
Proof. vm_refl. Qed.
Lemma D_17ca4 : decode_any W_17ca4 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ca8 : bv 32 := 0x00008067.
Lemma F_17ca8 : fetch_word Plain.M.loaded_segments (0x17da4 : word) = Some W_17ca8.
Proof. vm_refl. Qed.
Lemma D_17ca8 : decode_any W_17ca8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

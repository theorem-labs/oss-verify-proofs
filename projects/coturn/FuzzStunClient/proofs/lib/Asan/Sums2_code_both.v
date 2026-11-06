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
Definition W_53cbc : bv 32 := 0x00200613.
Lemma F_53cbc : fetch_word AsanUbsan.M.loaded_segments (0x53cbc : word) = Some W_53cbc.
Proof. vm_refl. Qed.
Lemma D_53cbc : decode_any W_53cbc = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53cc0 : bv 32 := 0x14c5ea63.
Lemma F_53cc0 : fetch_word AsanUbsan.M.loaded_segments (0x53cc0 : word) = Some W_53cc0.
Proof. vm_refl. Qed.
Lemma D_53cc0 : decode_any W_53cc0 = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53cc4 : bv 32 := 0x00100613.
Lemma F_53cc4 : fetch_word AsanUbsan.M.loaded_segments (0x53cc4 : word) = Some W_53cc4.
Proof. vm_refl. Qed.
Lemma D_53cc4 : decode_any W_53cc4 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53cc8 : bv 32 := 0x00100693.
Lemma F_53cc8 : fetch_word AsanUbsan.M.loaded_segments (0x53cc8 : word) = Some W_53cc8.
Proof. vm_refl. Qed.
Lemma D_53cc8 : decode_any W_53cc8 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ccc : bv 32 := 0x00c0006f.
Lemma F_53ccc : fetch_word AsanUbsan.M.loaded_segments (0x53ccc : word) = Some W_53ccc.
Proof. vm_refl. Qed.
Lemma D_53ccc : decode_any W_53ccc = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53cd0 : bv 32 := 0x00160613.
Lemma F_53cd0 : fetch_word AsanUbsan.M.loaded_segments (0x53cd0 : word) = Some W_53cd0.
Proof. vm_refl. Qed.
Lemma D_53cd0 : decode_any W_53cd0 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53cd4 : bv 32 := 0x12b60c63.
Lemma F_53cd4 : fetch_word AsanUbsan.M.loaded_segments (0x53cd4 : word) = Some W_53cd4.
Proof. vm_refl. Qed.
Lemma D_53cd4 : decode_any W_53cd4 = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53cd8 : bv 32 := 0x00461713.
Lemma F_53cd8 : fetch_word AsanUbsan.M.loaded_segments (0x53cd8 : word) = Some W_53cd8.
Proof. vm_refl. Qed.
Lemma D_53cd8 : decode_any W_53cd8 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53cdc : bv 32 := 0x00e50733.
Lemma F_53cdc : fetch_word AsanUbsan.M.loaded_segments (0x53cdc : word) = Some W_53cdc.
Proof. vm_refl. Qed.
Lemma D_53cdc : decode_any W_53cdc = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ce0 : bv 32 := 0x00072703.
Lemma F_53ce0 : fetch_word AsanUbsan.M.loaded_segments (0x53ce0 : word) = Some W_53ce0.
Proof. vm_refl. Qed.
Lemma D_53ce0 : decode_any W_53ce0 = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ce4 : bv 32 := 0x00060893.
Lemma F_53ce4 : fetch_word AsanUbsan.M.loaded_segments (0x53ce4 : word) = Some W_53ce4.
Proof. vm_refl. Qed.
Lemma D_53ce4 : decode_any W_53ce4 = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ce8 : bv 32 := 0xfff88793.
Lemma F_53ce8 : fetch_word AsanUbsan.M.loaded_segments (0x53ce8 : word) = Some W_53ce8.
Proof. vm_refl. Qed.
Lemma D_53ce8 : decode_any W_53ce8 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53cec : bv 32 := 0x0017d813.
Lemma F_53cec : fetch_word AsanUbsan.M.loaded_segments (0x53cec : word) = Some W_53cec.
Proof. vm_refl. Qed.
Lemma D_53cec : decode_any W_53cec = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53cf0 : bv 32 := 0x00481293.
Lemma F_53cf0 : fetch_word AsanUbsan.M.loaded_segments (0x53cf0 : word) = Some W_53cf0.
Proof. vm_refl. Qed.
Lemma D_53cf0 : decode_any W_53cf0 = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53cf4 : bv 32 := 0x005502b3.
Lemma F_53cf4 : fetch_word AsanUbsan.M.loaded_segments (0x53cf4 : word) = Some W_53cf4.
Proof. vm_refl. Qed.
Lemma D_53cf4 : decode_any W_53cf4 = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53cf8 : bv 32 := 0x0002a303.
Lemma F_53cf8 : fetch_word AsanUbsan.M.loaded_segments (0x53cf8 : word) = Some W_53cf8.
Proof. vm_refl. Qed.
Lemma D_53cf8 : decode_any W_53cf8 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53cfc : bv 32 := 0xfce37ae3.
Lemma F_53cfc : fetch_word AsanUbsan.M.loaded_segments (0x53cfc : word) = Some W_53cfc.
Proof. vm_refl. Qed.
Lemma D_53cfc : decode_any W_53cfc = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d00 : bv 32 := 0x0002b303.
Lemma F_53d00 : fetch_word AsanUbsan.M.loaded_segments (0x53d00 : word) = Some W_53d00.
Proof. vm_refl. Qed.
Lemma D_53d00 : decode_any W_53d00 = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d04 : bv 32 := 0x00489893.
Lemma F_53d04 : fetch_word AsanUbsan.M.loaded_segments (0x53d04 : word) = Some W_53d04.
Proof. vm_refl. Qed.
Lemma D_53d04 : decode_any W_53d04 = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d08 : bv 32 := 0x011508b3.
Lemma F_53d08 : fetch_word AsanUbsan.M.loaded_segments (0x53d08 : word) = Some W_53d08.
Proof. vm_refl. Qed.
Lemma D_53d08 : decode_any W_53d08 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d0c : bv 32 := 0x0048a383.
Lemma F_53d0c : fetch_word AsanUbsan.M.loaded_segments (0x53d0c : word) = Some W_53d0c.
Proof. vm_refl. Qed.
Lemma D_53d0c : decode_any W_53d0c = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d10 : bv 32 := 0x0068b023.
Lemma F_53d10 : fetch_word AsanUbsan.M.loaded_segments (0x53d10 : word) = Some W_53d10.
Proof. vm_refl. Qed.
Lemma D_53d10 : decode_any W_53d10 = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d14 : bv 32 := 0x0082b303.
Lemma F_53d14 : fetch_word AsanUbsan.M.loaded_segments (0x53d14 : word) = Some W_53d14.
Proof. vm_refl. Qed.
Lemma D_53d14 : decode_any W_53d14 = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d18 : bv 32 := 0x0088be03.
Lemma F_53d18 : fetch_word AsanUbsan.M.loaded_segments (0x53d18 : word) = Some W_53d18.
Proof. vm_refl. Qed.
Lemma D_53d18 : decode_any W_53d18 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d1c : bv 32 := 0x0068b423.
Lemma F_53d1c : fetch_word AsanUbsan.M.loaded_segments (0x53d1c : word) = Some W_53d1c.
Proof. vm_refl. Qed.
Lemma D_53d1c : decode_any W_53d1c = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d20 : bv 32 := 0x00e2a023.
Lemma F_53d20 : fetch_word AsanUbsan.M.loaded_segments (0x53d20 : word) = Some W_53d20.
Proof. vm_refl. Qed.
Lemma D_53d20 : decode_any W_53d20 = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d24 : bv 32 := 0x0072a223.
Lemma F_53d24 : fetch_word AsanUbsan.M.loaded_segments (0x53d24 : word) = Some W_53d24.
Proof. vm_refl. Qed.
Lemma D_53d24 : decode_any W_53d24 = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d28 : bv 32 := 0x01c2b423.
Lemma F_53d28 : fetch_word AsanUbsan.M.loaded_segments (0x53d28 : word) = Some W_53d28.
Proof. vm_refl. Qed.
Lemma D_53d28 : decode_any W_53d28 = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d2c : bv 32 := 0x00080893.
Lemma F_53d2c : fetch_word AsanUbsan.M.loaded_segments (0x53d2c : word) = Some W_53d2c.
Proof. vm_refl. Qed.
Lemma D_53d2c : decode_any W_53d2c = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d30 : bv 32 := 0xfaf6ece3.
Lemma F_53d30 : fetch_word AsanUbsan.M.loaded_segments (0x53d30 : word) = Some W_53d30.
Proof. vm_refl. Qed.
Lemma D_53d30 : decode_any W_53d30 = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d34 : bv 32 := 0xf9dff06f.
Lemma F_53d34 : fetch_word AsanUbsan.M.loaded_segments (0x53d34 : word) = Some W_53d34.
Proof. vm_refl. Qed.
Lemma D_53d34 : decode_any W_53d34 = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d38 : bv 32 := 0x00000613.
Lemma F_53d38 : fetch_word AsanUbsan.M.loaded_segments (0x53d38 : word) = Some W_53d38.
Proof. vm_refl. Qed.
Lemma D_53d38 : decode_any W_53d38 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d3c : bv 32 := 0x00459693.
Lemma F_53d3c : fetch_word AsanUbsan.M.loaded_segments (0x53d3c : word) = Some W_53d3c.
Proof. vm_refl. Qed.
Lemma D_53d3c : decode_any W_53d3c = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d40 : bv 32 := 0x00d506b3.
Lemma F_53d40 : fetch_word AsanUbsan.M.loaded_segments (0x53d40 : word) = Some W_53d40.
Proof. vm_refl. Qed.
Lemma D_53d40 : decode_any W_53d40 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d44 : bv 32 := 0x0006b703.
Lemma F_53d44 : fetch_word AsanUbsan.M.loaded_segments (0x53d44 : word) = Some W_53d44.
Proof. vm_refl. Qed.
Lemma D_53d44 : decode_any W_53d44 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d48 : bv 32 := 0x0086b783.
Lemma F_53d48 : fetch_word AsanUbsan.M.loaded_segments (0x53d48 : word) = Some W_53d48.
Proof. vm_refl. Qed.
Lemma D_53d48 : decode_any W_53d48 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d4c : bv 32 := 0x00053803.
Lemma F_53d4c : fetch_word AsanUbsan.M.loaded_segments (0x53d4c : word) = Some W_53d4c.
Proof. vm_refl. Qed.
Lemma D_53d4c : decode_any W_53d4c = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d50 : bv 32 := 0x00853883.
Lemma F_53d50 : fetch_word AsanUbsan.M.loaded_segments (0x53d50 : word) = Some W_53d50.
Proof. vm_refl. Qed.
Lemma D_53d50 : decode_any W_53d50 = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d54 : bv 32 := 0x00e53023.
Lemma F_53d54 : fetch_word AsanUbsan.M.loaded_segments (0x53d54 : word) = Some W_53d54.
Proof. vm_refl. Qed.
Lemma D_53d54 : decode_any W_53d54 = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d58 : bv 32 := 0x00f53423.
Lemma F_53d58 : fetch_word AsanUbsan.M.loaded_segments (0x53d58 : word) = Some W_53d58.
Proof. vm_refl. Qed.
Lemma D_53d58 : decode_any W_53d58 = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d5c : bv 32 := 0x0106b023.
Lemma F_53d5c : fetch_word AsanUbsan.M.loaded_segments (0x53d5c : word) = Some W_53d5c.
Proof. vm_refl. Qed.
Lemma D_53d5c : decode_any W_53d5c = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d60 : bv 32 := 0x0116b423.
Lemma F_53d60 : fetch_word AsanUbsan.M.loaded_segments (0x53d60 : word) = Some W_53d60.
Proof. vm_refl. Qed.
Lemma D_53d60 : decode_any W_53d60 = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d64 : bv 32 := 0x00000693.
Lemma F_53d64 : fetch_word AsanUbsan.M.loaded_segments (0x53d64 : word) = Some W_53d64.
Proof. vm_refl. Qed.
Lemma D_53d64 : decode_any W_53d64 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d68 : bv 32 := 0x00161793.
Lemma F_53d68 : fetch_word AsanUbsan.M.loaded_segments (0x53d68 : word) = Some W_53d68.
Proof. vm_refl. Qed.
Lemma D_53d68 : decode_any W_53d68 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d6c : bv 32 := 0x00178813.
Lemma F_53d6c : fetch_word AsanUbsan.M.loaded_segments (0x53d6c : word) = Some W_53d6c.
Proof. vm_refl. Qed.
Lemma D_53d6c : decode_any W_53d6c = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d70 : bv 32 := 0x00461713.
Lemma F_53d70 : fetch_word AsanUbsan.M.loaded_segments (0x53d70 : word) = Some W_53d70.
Proof. vm_refl. Qed.
Lemma D_53d70 : decode_any W_53d70 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d74 : bv 32 := 0x00b86a63.
Lemma F_53d74 : fetch_word AsanUbsan.M.loaded_segments (0x53d74 : word) = Some W_53d74.
Proof. vm_refl. Qed.
Lemma D_53d74 : decode_any W_53d74 = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d78 : bv 32 := 0x00278793.
Lemma F_53d78 : fetch_word AsanUbsan.M.loaded_segments (0x53d78 : word) = Some W_53d78.
Proof. vm_refl. Qed.
Lemma D_53d78 : decode_any W_53d78 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d7c : bv 32 := 0x02b7ea63.
Lemma F_53d7c : fetch_word AsanUbsan.M.loaded_segments (0x53d7c : word) = Some W_53d7c.
Proof. vm_refl. Qed.
Lemma D_53d7c : decode_any W_53d7c = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d80 : bv 32 := 0x04c69c63.
Lemma F_53d80 : fetch_word AsanUbsan.M.loaded_segments (0x53d80 : word) = Some W_53d80.
Proof. vm_refl. Qed.
Lemma D_53d80 : decode_any W_53d80 = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d84 : bv 32 := 0x0880006f.
Lemma F_53d84 : fetch_word AsanUbsan.M.loaded_segments (0x53d84 : word) = Some W_53d84.
Proof. vm_refl. Qed.
Lemma D_53d84 : decode_any W_53d84 = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d88 : bv 32 := 0x00e506b3.
Lemma F_53d88 : fetch_word AsanUbsan.M.loaded_segments (0x53d88 : word) = Some W_53d88.
Proof. vm_refl. Qed.
Lemma D_53d88 : decode_any W_53d88 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d8c : bv 32 := 0x00481893.
Lemma F_53d8c : fetch_word AsanUbsan.M.loaded_segments (0x53d8c : word) = Some W_53d8c.
Proof. vm_refl. Qed.
Lemma D_53d8c : decode_any W_53d8c = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d90 : bv 32 := 0x011508b3.
Lemma F_53d90 : fetch_word AsanUbsan.M.loaded_segments (0x53d90 : word) = Some W_53d90.
Proof. vm_refl. Qed.
Lemma D_53d90 : decode_any W_53d90 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d94 : bv 32 := 0x0006a683.
Lemma F_53d94 : fetch_word AsanUbsan.M.loaded_segments (0x53d94 : word) = Some W_53d94.
Proof. vm_refl. Qed.
Lemma D_53d94 : decode_any W_53d94 = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d98 : bv 32 := 0x0008a883.
Lemma F_53d98 : fetch_word AsanUbsan.M.loaded_segments (0x53d98 : word) = Some W_53d98.
Proof. vm_refl. Qed.
Lemma D_53d98 : decode_any W_53d98 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53d9c : bv 32 := 0x0116e463.
Lemma F_53d9c : fetch_word AsanUbsan.M.loaded_segments (0x53d9c : word) = Some W_53d9c.
Proof. vm_refl. Qed.
Lemma D_53d9c : decode_any W_53d9c = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53da0 : bv 32 := 0x00060813.
Lemma F_53da0 : fetch_word AsanUbsan.M.loaded_segments (0x53da0 : word) = Some W_53da0.
Proof. vm_refl. Qed.
Lemma D_53da0 : decode_any W_53da0 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53da4 : bv 32 := 0x00080693.
Lemma F_53da4 : fetch_word AsanUbsan.M.loaded_segments (0x53da4 : word) = Some W_53da4.
Proof. vm_refl. Qed.
Lemma D_53da4 : decode_any W_53da4 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53da8 : bv 32 := 0x00278793.
Lemma F_53da8 : fetch_word AsanUbsan.M.loaded_segments (0x53da8 : word) = Some W_53da8.
Proof. vm_refl. Qed.
Lemma D_53da8 : decode_any W_53da8 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53dac : bv 32 := 0xfcb7fae3.
Lemma F_53dac : fetch_word AsanUbsan.M.loaded_segments (0x53dac : word) = Some W_53dac.
Proof. vm_refl. Qed.
Lemma D_53dac : decode_any W_53dac = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53db0 : bv 32 := 0x00469813.
Lemma F_53db0 : fetch_word AsanUbsan.M.loaded_segments (0x53db0 : word) = Some W_53db0.
Proof. vm_refl. Qed.
Lemma D_53db0 : decode_any W_53db0 = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53db4 : bv 32 := 0x00479893.
Lemma F_53db4 : fetch_word AsanUbsan.M.loaded_segments (0x53db4 : word) = Some W_53db4.
Proof. vm_refl. Qed.
Lemma D_53db4 : decode_any W_53db4 = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53db8 : bv 32 := 0x01050833.
Lemma F_53db8 : fetch_word AsanUbsan.M.loaded_segments (0x53db8 : word) = Some W_53db8.
Proof. vm_refl. Qed.
Lemma D_53db8 : decode_any W_53db8 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53dbc : bv 32 := 0x011508b3.
Lemma F_53dbc : fetch_word AsanUbsan.M.loaded_segments (0x53dbc : word) = Some W_53dbc.
Proof. vm_refl. Qed.
Lemma D_53dbc : decode_any W_53dbc = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53dc0 : bv 32 := 0x00082803.
Lemma F_53dc0 : fetch_word AsanUbsan.M.loaded_segments (0x53dc0 : word) = Some W_53dc0.
Proof. vm_refl. Qed.
Lemma D_53dc0 : decode_any W_53dc0 = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53dc4 : bv 32 := 0x0008a883.
Lemma F_53dc4 : fetch_word AsanUbsan.M.loaded_segments (0x53dc4 : word) = Some W_53dc4.
Proof. vm_refl. Qed.
Lemma D_53dc4 : decode_any W_53dc4 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53dc8 : bv 32 := 0x01186463.
Lemma F_53dc8 : fetch_word AsanUbsan.M.loaded_segments (0x53dc8 : word) = Some W_53dc8.
Proof. vm_refl. Qed.
Lemma D_53dc8 : decode_any W_53dc8 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53dcc : bv 32 := 0x00068793.
Lemma F_53dcc : fetch_word AsanUbsan.M.loaded_segments (0x53dcc : word) = Some W_53dcc.
Proof. vm_refl. Qed.
Lemma D_53dcc : decode_any W_53dcc = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53dd0 : bv 32 := 0x00078693.
Lemma F_53dd0 : fetch_word AsanUbsan.M.loaded_segments (0x53dd0 : word) = Some W_53dd0.
Proof. vm_refl. Qed.
Lemma D_53dd0 : decode_any W_53dd0 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53dd4 : bv 32 := 0x02c78c63.
Lemma F_53dd4 : fetch_word AsanUbsan.M.loaded_segments (0x53dd4 : word) = Some W_53dd4.
Proof. vm_refl. Qed.
Lemma D_53dd4 : decode_any W_53dd4 = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53dd8 : bv 32 := 0x00469613.
Lemma F_53dd8 : fetch_word AsanUbsan.M.loaded_segments (0x53dd8 : word) = Some W_53dd8.
Proof. vm_refl. Qed.
Lemma D_53dd8 : decode_any W_53dd8 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53ddc : bv 32 := 0x00c50633.
Lemma F_53ddc : fetch_word AsanUbsan.M.loaded_segments (0x53ddc : word) = Some W_53ddc.
Proof. vm_refl. Qed.
Lemma D_53ddc : decode_any W_53ddc = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53de0 : bv 32 := 0x00063783.
Lemma F_53de0 : fetch_word AsanUbsan.M.loaded_segments (0x53de0 : word) = Some W_53de0.
Proof. vm_refl. Qed.
Lemma D_53de0 : decode_any W_53de0 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53de4 : bv 32 := 0x00e50733.
Lemma F_53de4 : fetch_word AsanUbsan.M.loaded_segments (0x53de4 : word) = Some W_53de4.
Proof. vm_refl. Qed.
Lemma D_53de4 : decode_any W_53de4 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53de8 : bv 32 := 0x00073803.
Lemma F_53de8 : fetch_word AsanUbsan.M.loaded_segments (0x53de8 : word) = Some W_53de8.
Proof. vm_refl. Qed.
Lemma D_53de8 : decode_any W_53de8 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53dec : bv 32 := 0x00873883.
Lemma F_53dec : fetch_word AsanUbsan.M.loaded_segments (0x53dec : word) = Some W_53dec.
Proof. vm_refl. Qed.
Lemma D_53dec : decode_any W_53dec = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53df0 : bv 32 := 0x00f73023.
Lemma F_53df0 : fetch_word AsanUbsan.M.loaded_segments (0x53df0 : word) = Some W_53df0.
Proof. vm_refl. Qed.
Lemma D_53df0 : decode_any W_53df0 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53df4 : bv 32 := 0x00863783.
Lemma F_53df4 : fetch_word AsanUbsan.M.loaded_segments (0x53df4 : word) = Some W_53df4.
Proof. vm_refl. Qed.
Lemma D_53df4 : decode_any W_53df4 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53df8 : bv 32 := 0x00f73423.
Lemma F_53df8 : fetch_word AsanUbsan.M.loaded_segments (0x53df8 : word) = Some W_53df8.
Proof. vm_refl. Qed.
Lemma D_53df8 : decode_any W_53df8 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53dfc : bv 32 := 0x01063023.
Lemma F_53dfc : fetch_word AsanUbsan.M.loaded_segments (0x53dfc : word) = Some W_53dfc.
Proof. vm_refl. Qed.
Lemma D_53dfc : decode_any W_53dfc = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e00 : bv 32 := 0x01163423.
Lemma F_53e00 : fetch_word AsanUbsan.M.loaded_segments (0x53e00 : word) = Some W_53e00.
Proof. vm_refl. Qed.
Lemma D_53e00 : decode_any W_53e00 = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e04 : bv 32 := 0x00068613.
Lemma F_53e04 : fetch_word AsanUbsan.M.loaded_segments (0x53e04 : word) = Some W_53e04.
Proof. vm_refl. Qed.
Lemma D_53e04 : decode_any W_53e04 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e08 : bv 32 := 0xf6b6e0e3.
Lemma F_53e08 : fetch_word AsanUbsan.M.loaded_segments (0x53e08 : word) = Some W_53e08.
Proof. vm_refl. Qed.
Lemma D_53e08 : decode_any W_53e08 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e0c : bv 32 := 0xfff58593.
Lemma F_53e0c : fetch_word AsanUbsan.M.loaded_segments (0x53e0c : word) = Some W_53e0c.
Proof. vm_refl. Qed.
Lemma D_53e0c : decode_any W_53e0c = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e10 : bv 32 := 0xf20594e3.
Lemma F_53e10 : fetch_word AsanUbsan.M.loaded_segments (0x53e10 : word) = Some W_53e10.
Proof. vm_refl. Qed.
Lemma D_53e10 : decode_any W_53e10 = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53e14 : bv 32 := 0x00008067.
Lemma F_53e14 : fetch_word AsanUbsan.M.loaded_segments (0x53e14 : word) = Some W_53e14.
Proof. vm_refl. Qed.
Lemma D_53e14 : decode_any W_53e14 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665d8 : bv 32 := 0x06060663.
Lemma F_665d8 : fetch_word AsanUbsan.M.loaded_segments (0x665d8 : word) = Some W_665d8.
Proof. vm_refl. Qed.
Lemma D_665d8 : decode_any W_665d8 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665dc : bv 32 := 0x00000693.
Lemma F_665dc : fetch_word AsanUbsan.M.loaded_segments (0x665dc : word) = Some W_665dc.
Proof. vm_refl. Qed.
Lemma D_665dc : decode_any W_665dc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665e0 : bv 32 := 0x00d58733.
Lemma F_665e0 : fetch_word AsanUbsan.M.loaded_segments (0x665e0 : word) = Some W_665e0.
Proof. vm_refl. Qed.
Lemma D_665e0 : decode_any W_665e0 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665e4 : bv 32 := 0x00074703.
Lemma F_665e4 : fetch_word AsanUbsan.M.loaded_segments (0x665e4 : word) = Some W_665e4.
Proof. vm_refl. Qed.
Lemma D_665e4 : decode_any W_665e4 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665e8 : bv 32 := 0x00070c63.
Lemma F_665e8 : fetch_word AsanUbsan.M.loaded_segments (0x665e8 : word) = Some W_665e8.
Proof. vm_refl. Qed.
Lemma D_665e8 : decode_any W_665e8 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665ec : bv 32 := 0x00d507b3.
Lemma F_665ec : fetch_word AsanUbsan.M.loaded_segments (0x665ec : word) = Some W_665ec.
Proof. vm_refl. Qed.
Lemma D_665ec : decode_any W_665ec = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665f0 : bv 32 := 0x00168693.
Lemma F_665f0 : fetch_word AsanUbsan.M.loaded_segments (0x665f0 : word) = Some W_665f0.
Proof. vm_refl. Qed.
Lemma D_665f0 : decode_any W_665f0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665f4 : bv 32 := 0x00e78023.
Lemma F_665f4 : fetch_word AsanUbsan.M.loaded_segments (0x665f4 : word) = Some W_665f4.
Proof. vm_refl. Qed.
Lemma D_665f4 : decode_any W_665f4 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665f8 : bv 32 := 0xfed614e3.
Lemma F_665f8 : fetch_word AsanUbsan.M.loaded_segments (0x665f8 : word) = Some W_665f8.
Proof. vm_refl. Qed.
Lemma D_665f8 : decode_any W_665f8 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665fc : bv 32 := 0x00060693.
Lemma F_665fc : fetch_word AsanUbsan.M.loaded_segments (0x665fc : word) = Some W_665fc.
Proof. vm_refl. Qed.
Lemma D_665fc : decode_any W_665fc = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66600 : bv 32 := 0x00d505b3.
Lemma F_66600 : fetch_word AsanUbsan.M.loaded_segments (0x66600 : word) = Some W_66600.
Proof. vm_refl. Qed.
Lemma D_66600 : decode_any W_66600 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66604 : bv 32 := 0x40d6073b.
Lemma F_66604 : fetch_word AsanUbsan.M.loaded_segments (0x66604 : word) = Some W_66604.
Proof. vm_refl. Qed.
Lemma D_66604 : decode_any W_66604 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66608 : bv 32 := 0x00b76733.
Lemma F_66608 : fetch_word AsanUbsan.M.loaded_segments (0x66608 : word) = Some W_66608.
Proof. vm_refl. Qed.
Lemma D_66608 : decode_any W_66608 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6660c : bv 32 := 0x00f77713.
Lemma F_6660c : fetch_word AsanUbsan.M.loaded_segments (0x6660c : word) = Some W_6660c.
Proof. vm_refl. Qed.
Lemma D_6660c : decode_any W_6660c = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66610 : bv 32 := 0x00070e63.
Lemma F_66610 : fetch_word AsanUbsan.M.loaded_segments (0x66610 : word) = Some W_66610.
Proof. vm_refl. Qed.
Lemma D_66610 : decode_any W_66610 = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66614 : bv 32 := 0x02d60863.
Lemma F_66614 : fetch_word AsanUbsan.M.loaded_segments (0x66614 : word) = Some W_66614.
Proof. vm_refl. Qed.
Lemma D_66614 : decode_any W_66614 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66618 : bv 32 := 0x00c50633.
Lemma F_66618 : fetch_word AsanUbsan.M.loaded_segments (0x66618 : word) = Some W_66618.
Proof. vm_refl. Qed.
Lemma D_66618 : decode_any W_66618 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6661c : bv 32 := 0x00058023.
Lemma F_6661c : fetch_word AsanUbsan.M.loaded_segments (0x6661c : word) = Some W_6661c.
Proof. vm_refl. Qed.
Lemma D_6661c : decode_any W_6661c = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66620 : bv 32 := 0x00158593.
Lemma F_66620 : fetch_word AsanUbsan.M.loaded_segments (0x66620 : word) = Some W_66620.
Proof. vm_refl. Qed.
Lemma D_66620 : decode_any W_66620 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66624 : bv 32 := 0xfec59ce3.
Lemma F_66624 : fetch_word AsanUbsan.M.loaded_segments (0x66624 : word) = Some W_66624.
Proof. vm_refl. Qed.
Lemma D_66624 : decode_any W_66624 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66628 : bv 32 := 0x01c0006f.
Lemma F_66628 : fetch_word AsanUbsan.M.loaded_segments (0x66628 : word) = Some W_66628.
Proof. vm_refl. Qed.
Lemma D_66628 : decode_any W_66628 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6662c : bv 32 := 0x00d60c63.
Lemma F_6662c : fetch_word AsanUbsan.M.loaded_segments (0x6662c : word) = Some W_6662c.
Proof. vm_refl. Qed.
Lemma D_6662c : decode_any W_6662c = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66630 : bv 32 := 0x00c50633.
Lemma F_66630 : fetch_word AsanUbsan.M.loaded_segments (0x66630 : word) = Some W_66630.
Proof. vm_refl. Qed.
Lemma D_66630 : decode_any W_66630 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66634 : bv 32 := 0x0005b023.
Lemma F_66634 : fetch_word AsanUbsan.M.loaded_segments (0x66634 : word) = Some W_66634.
Proof. vm_refl. Qed.
Lemma D_66634 : decode_any W_66634 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66638 : bv 32 := 0x0005b423.
Lemma F_66638 : fetch_word AsanUbsan.M.loaded_segments (0x66638 : word) = Some W_66638.
Proof. vm_refl. Qed.
Lemma D_66638 : decode_any W_66638 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6663c : bv 32 := 0x01058593.
Lemma F_6663c : fetch_word AsanUbsan.M.loaded_segments (0x6663c : word) = Some W_6663c.
Proof. vm_refl. Qed.
Lemma D_6663c : decode_any W_6663c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66640 : bv 32 := 0xfec5eae3.
Lemma F_66640 : fetch_word AsanUbsan.M.loaded_segments (0x66640 : word) = Some W_66640.
Proof. vm_refl. Qed.
Lemma D_66640 : decode_any W_66640 = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66644 : bv 32 := 0x00008067.
Lemma F_66644 : fetch_word AsanUbsan.M.loaded_segments (0x66644 : word) = Some W_66644.
Proof. vm_refl. Qed.
Lemma D_66644 : decode_any W_66644 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

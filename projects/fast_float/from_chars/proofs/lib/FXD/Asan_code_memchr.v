(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_d2b80 : bv 32 := 0x00008067.
Lemma F_d2b80 : fetch_word Asan.M.loaded_segments (0xd2b80 : word) = Some W_d2b80.
Proof. vm_refl. Qed.
Lemma D_d2b80 : decode_any W_d2b80 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2b84 : bv 32 := 0xbac7d06f.
Lemma F_d2b84 : fetch_word Asan.M.loaded_segments (0xd2b84 : word) = Some W_d2b84.
Proof. vm_refl. Qed.
Lemma D_d2b84 : decode_any W_d2b84 = Some (Jal 0 1561516, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2b88 : bv 32 := 0x0ff5f593.
Lemma F_d2b88 : fetch_word Asan.M.loaded_segments (0xd2b88 : word) = Some W_d2b88.
Proof. vm_refl. Qed.
Lemma D_d2b88 : decode_any W_d2b88 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2b8c : bv 32 := 0x00757693.
Lemma F_d2b8c : fetch_word Asan.M.loaded_segments (0xd2b8c : word) = Some W_d2b8c.
Proof. vm_refl. Qed.
Lemma D_d2b8c : decode_any W_d2b8c = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2b90 : bv 32 := 0x00c03733.
Lemma F_d2b90 : fetch_word Asan.M.loaded_segments (0xd2b90 : word) = Some W_d2b90.
Proof. vm_refl. Qed.
Lemma D_d2b90 : decode_any W_d2b90 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2b94 : bv 32 := 0x02068c63.
Lemma F_d2b94 : fetch_word Asan.M.loaded_segments (0xd2b94 : word) = Some W_d2b94.
Proof. vm_refl. Qed.
Lemma D_d2b94 : decode_any W_d2b94 = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2b98 : bv 32 := 0x02060a63.
Lemma F_d2b98 : fetch_word Asan.M.loaded_segments (0xd2b98 : word) = Some W_d2b98.
Proof. vm_refl. Qed.
Lemma D_d2b98 : decode_any W_d2b98 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2b9c : bv 32 := 0x00150793.
Lemma F_d2b9c : fetch_word Asan.M.loaded_segments (0xd2b9c : word) = Some W_d2b9c.
Proof. vm_refl. Qed.
Lemma D_d2b9c : decode_any W_d2b9c = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2ba0 : bv 32 := 0x00100813.
Lemma F_d2ba0 : fetch_word Asan.M.loaded_segments (0xd2ba0 : word) = Some W_d2ba0.
Proof. vm_refl. Qed.
Lemma D_d2ba0 : decode_any W_d2ba0 = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2ba4 : bv 32 := 0x00054703.
Lemma F_d2ba4 : fetch_word Asan.M.loaded_segments (0xd2ba4 : word) = Some W_d2ba4.
Proof. vm_refl. Qed.
Lemma D_d2ba4 : decode_any W_d2ba4 = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2ba8 : bv 32 := 0x00060693.
Lemma F_d2ba8 : fetch_word Asan.M.loaded_segments (0xd2ba8 : word) = Some W_d2ba8.
Proof. vm_refl. Qed.
Lemma D_d2ba8 : decode_any W_d2ba8 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2bac : bv 32 := 0x06b70e63.
Lemma F_d2bac : fetch_word Asan.M.loaded_segments (0xd2bac : word) = Some W_d2bac.
Proof. vm_refl. Qed.
Lemma D_d2bac : decode_any W_d2bac = Some (Branch BC_EQ 14 11 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2bb0 : bv 32 := 0x00150513.
Lemma F_d2bb0 : fetch_word Asan.M.loaded_segments (0xd2bb0 : word) = Some W_d2bb0.
Proof. vm_refl. Qed.
Lemma D_d2bb0 : decode_any W_d2bb0 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2bb4 : bv 32 := 0xfff68613.
Lemma F_d2bb4 : fetch_word Asan.M.loaded_segments (0xd2bb4 : word) = Some W_d2bb4.
Proof. vm_refl. Qed.
Lemma D_d2bb4 : decode_any W_d2bb4 = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2bb8 : bv 32 := 0x0077f893.
Lemma F_d2bb8 : fetch_word Asan.M.loaded_segments (0xd2bb8 : word) = Some W_d2bb8.
Proof. vm_refl. Qed.
Lemma D_d2bb8 : decode_any W_d2bb8 = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2bbc : bv 32 := 0x00c03733.
Lemma F_d2bbc : fetch_word Asan.M.loaded_segments (0xd2bbc : word) = Some W_d2bbc.
Proof. vm_refl. Qed.
Lemma D_d2bbc : decode_any W_d2bbc = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2bc0 : bv 32 := 0x00088663.
Lemma F_d2bc0 : fetch_word Asan.M.loaded_segments (0xd2bc0 : word) = Some W_d2bc0.
Proof. vm_refl. Qed.
Lemma D_d2bc0 : decode_any W_d2bc0 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2bc4 : bv 32 := 0x00178793.
Lemma F_d2bc4 : fetch_word Asan.M.loaded_segments (0xd2bc4 : word) = Some W_d2bc4.
Proof. vm_refl. Qed.
Lemma D_d2bc4 : decode_any W_d2bc4 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2bc8 : bv 32 := 0xfd069ee3.
Lemma F_d2bc8 : fetch_word Asan.M.loaded_segments (0xd2bc8 : word) = Some W_d2bc8.
Proof. vm_refl. Qed.
Lemma D_d2bc8 : decode_any W_d2bc8 = Some (Branch BC_NE 13 16 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2bcc : bv 32 := 0x06070863.
Lemma F_d2bcc : fetch_word Asan.M.loaded_segments (0xd2bcc : word) = Some W_d2bcc.
Proof. vm_refl. Qed.
Lemma D_d2bcc : decode_any W_d2bcc = Some (Branch BC_EQ 14 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2bd0 : bv 32 := 0x00054683.
Lemma F_d2bd0 : fetch_word Asan.M.loaded_segments (0xd2bd0 : word) = Some W_d2bd0.
Proof. vm_refl. Qed.
Lemma D_d2bd0 : decode_any W_d2bd0 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2bd4 : bv 32 := 0x04b68663.
Lemma F_d2bd4 : fetch_word Asan.M.loaded_segments (0xd2bd4 : word) = Some W_d2bd4.
Proof. vm_refl. Qed.
Lemma D_d2bd4 : decode_any W_d2bd4 = Some (Branch BC_EQ 13 11 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2bd8 : bv 32 := 0x00800693.
Lemma F_d2bd8 : fetch_word Asan.M.loaded_segments (0xd2bd8 : word) = Some W_d2bd8.
Proof. vm_refl. Qed.
Lemma D_d2bd8 : decode_any W_d2bd8 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2bdc : bv 32 := 0x04d66263.
Lemma F_d2bdc : fetch_word Asan.M.loaded_segments (0xd2bdc : word) = Some W_d2bdc.
Proof. vm_refl. Qed.
Lemma D_d2bdc : decode_any W_d2bdc = Some (Branch BC_LTU 12 13 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2be0 : bv 32 := 0xfff3d697.
Lemma F_d2be0 : fetch_word Asan.M.loaded_segments (0xd2be0 : word) = Some W_d2be0.
Proof. vm_refl. Qed.
Lemma D_d2be0 : decode_any W_d2be0 = Some (Auipc 13 1048381, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2be4 : bv 32 := 0x7e86b683.
Lemma F_d2be4 : fetch_word Asan.M.loaded_segments (0xd2be4 : word) = Some W_d2be4.
Proof. vm_refl. Qed.
Lemma D_d2be4 : decode_any W_d2be4 = Some (Load SZ8 true 13 13 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2be8 : bv 32 := 0xfff3d717.
Lemma F_d2be8 : fetch_word Asan.M.loaded_segments (0xd2be8 : word) = Some W_d2be8.
Proof. vm_refl. Qed.
Lemma D_d2be8 : decode_any W_d2be8 = Some (Auipc 14 1048381, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2bec : bv 32 := 0x7c073703.
Lemma F_d2bec : fetch_word Asan.M.loaded_segments (0xd2bec : word) = Some W_d2bec.
Proof. vm_refl. Qed.
Lemma D_d2bec : decode_any W_d2bec = Some (Load SZ8 true 14 14 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2bf0 : bv 32 := 0x00168793.
Lemma F_d2bf0 : fetch_word Asan.M.loaded_segments (0xd2bf0 : word) = Some W_d2bf0.
Proof. vm_refl. Qed.
Lemma D_d2bf0 : decode_any W_d2bf0 = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2bf4 : bv 32 := 0x02f587b3.
Lemma F_d2bf4 : fetch_word Asan.M.loaded_segments (0xd2bf4 : word) = Some W_d2bf4.
Proof. vm_refl. Qed.
Lemma D_d2bf4 : decode_any W_d2bf4 = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2bf8 : bv 32 := 0x00700813.
Lemma F_d2bf8 : fetch_word Asan.M.loaded_segments (0xd2bf8 : word) = Some W_d2bf8.
Proof. vm_refl. Qed.
Lemma D_d2bf8 : decode_any W_d2bf8 = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2bfc : bv 32 := 0x00053883.
Lemma F_d2bfc : fetch_word Asan.M.loaded_segments (0xd2bfc : word) = Some W_d2bfc.
Proof. vm_refl. Qed.
Lemma D_d2bfc : decode_any W_d2bfc = Some (Load SZ8 true 17 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c00 : bv 32 := 0x00f8c8b3.
Lemma F_d2c00 : fetch_word Asan.M.loaded_segments (0xd2c00 : word) = Some W_d2c00.
Proof. vm_refl. Qed.
Lemma D_d2c00 : decode_any W_d2c00 = Some (Op ALU_XOR 17 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c04 : bv 32 := 0x411682b3.
Lemma F_d2c04 : fetch_word Asan.M.loaded_segments (0xd2c04 : word) = Some W_d2c04.
Proof. vm_refl. Qed.
Lemma D_d2c04 : decode_any W_d2c04 = Some (Op ALU_SUB 5 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c08 : bv 32 := 0x0112e8b3.
Lemma F_d2c08 : fetch_word Asan.M.loaded_segments (0xd2c08 : word) = Some W_d2c08.
Proof. vm_refl. Qed.
Lemma D_d2c08 : decode_any W_d2c08 = Some (Op ALU_OR 17 5 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c0c : bv 32 := 0x00e8f8b3.
Lemma F_d2c0c : fetch_word Asan.M.loaded_segments (0xd2c0c : word) = Some W_d2c0c.
Proof. vm_refl. Qed.
Lemma D_d2c0c : decode_any W_d2c0c = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c10 : bv 32 := 0x02e89a63.
Lemma F_d2c10 : fetch_word Asan.M.loaded_segments (0xd2c10 : word) = Some W_d2c10.
Proof. vm_refl. Qed.
Lemma D_d2c10 : decode_any W_d2c10 = Some (Branch BC_NE 17 14 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c14 : bv 32 := 0xff860613.
Lemma F_d2c14 : fetch_word Asan.M.loaded_segments (0xd2c14 : word) = Some W_d2c14.
Proof. vm_refl. Qed.
Lemma D_d2c14 : decode_any W_d2c14 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c18 : bv 32 := 0x00850513.
Lemma F_d2c18 : fetch_word Asan.M.loaded_segments (0xd2c18 : word) = Some W_d2c18.
Proof. vm_refl. Qed.
Lemma D_d2c18 : decode_any W_d2c18 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c1c : bv 32 := 0xfec860e3.
Lemma F_d2c1c : fetch_word Asan.M.loaded_segments (0xd2c1c : word) = Some W_d2c1c.
Proof. vm_refl. Qed.
Lemma D_d2c1c : decode_any W_d2c1c = Some (Branch BC_LTU 16 12 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c20 : bv 32 := 0x00060693.
Lemma F_d2c20 : fetch_word Asan.M.loaded_segments (0xd2c20 : word) = Some W_d2c20.
Proof. vm_refl. Qed.
Lemma D_d2c20 : decode_any W_d2c20 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c24 : bv 32 := 0x00060c63.
Lemma F_d2c24 : fetch_word Asan.M.loaded_segments (0xd2c24 : word) = Some W_d2c24.
Proof. vm_refl. Qed.
Lemma D_d2c24 : decode_any W_d2c24 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c28 : bv 32 := 0x00054603.
Lemma F_d2c28 : fetch_word Asan.M.loaded_segments (0xd2c28 : word) = Some W_d2c28.
Proof. vm_refl. Qed.
Lemma D_d2c28 : decode_any W_d2c28 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c2c : bv 32 := 0x00b60a63.
Lemma F_d2c2c : fetch_word Asan.M.loaded_segments (0xd2c2c : word) = Some W_d2c2c.
Proof. vm_refl. Qed.
Lemma D_d2c2c : decode_any W_d2c2c = Some (Branch BC_EQ 12 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c30 : bv 32 := 0xfff68693.
Lemma F_d2c30 : fetch_word Asan.M.loaded_segments (0xd2c30 : word) = Some W_d2c30.
Proof. vm_refl. Qed.
Lemma D_d2c30 : decode_any W_d2c30 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c34 : bv 32 := 0x00150513.
Lemma F_d2c34 : fetch_word Asan.M.loaded_segments (0xd2c34 : word) = Some W_d2c34.
Proof. vm_refl. Qed.
Lemma D_d2c34 : decode_any W_d2c34 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c38 : bv 32 := 0xfe0698e3.
Lemma F_d2c38 : fetch_word Asan.M.loaded_segments (0xd2c38 : word) = Some W_d2c38.
Proof. vm_refl. Qed.
Lemma D_d2c38 : decode_any W_d2c38 = Some (Branch BC_NE 13 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c3c : bv 32 := 0x00000513.
Lemma F_d2c3c : fetch_word Asan.M.loaded_segments (0xd2c3c : word) = Some W_d2c3c.
Proof. vm_refl. Qed.
Lemma D_d2c3c : decode_any W_d2c3c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c40 : bv 32 := 0x00008067.
Lemma F_d2c40 : fetch_word Asan.M.loaded_segments (0xd2c40 : word) = Some W_d2c40.
Proof. vm_refl. Qed.
Lemma D_d2c40 : decode_any W_d2c40 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c44 : bv 32 := 0x00060693.
Lemma F_d2c44 : fetch_word Asan.M.loaded_segments (0xd2c44 : word) = Some W_d2c44.
Proof. vm_refl. Qed.
Lemma D_d2c44 : decode_any W_d2c44 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c48 : bv 32 := 0x00054603.
Lemma F_d2c48 : fetch_word Asan.M.loaded_segments (0xd2c48 : word) = Some W_d2c48.
Proof. vm_refl. Qed.
Lemma D_d2c48 : decode_any W_d2c48 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c4c : bv 32 := 0xfeb612e3.
Lemma F_d2c4c : fetch_word Asan.M.loaded_segments (0xd2c4c : word) = Some W_d2c4c.
Proof. vm_refl. Qed.
Lemma D_d2c4c : decode_any W_d2c4c = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c50 : bv 32 := 0xff1ff06f.
Lemma F_d2c50 : fetch_word Asan.M.loaded_segments (0xd2c50 : word) = Some W_d2c50.
Proof. vm_refl. Qed.
Lemma D_d2c50 : decode_any W_d2c50 = Some (Jal 0 2097136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c54 : bv 32 := 0x02060063.
Lemma F_d2c54 : fetch_word Asan.M.loaded_segments (0xd2c54 : word) = Some W_d2c54.
Proof. vm_refl. Qed.
Lemma D_d2c54 : decode_any W_d2c54 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c58 : bv 32 := 0x00054683.
Lemma F_d2c58 : fetch_word Asan.M.loaded_segments (0xd2c58 : word) = Some W_d2c58.
Proof. vm_refl. Qed.
Lemma D_d2c58 : decode_any W_d2c58 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c5c : bv 32 := 0x0005c703.
Lemma F_d2c5c : fetch_word Asan.M.loaded_segments (0xd2c5c : word) = Some W_d2c5c.
Proof. vm_refl. Qed.
Lemma D_d2c5c : decode_any W_d2c5c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c60 : bv 32 := 0x00e69e63.
Lemma F_d2c60 : fetch_word Asan.M.loaded_segments (0xd2c60 : word) = Some W_d2c60.
Proof. vm_refl. Qed.
Lemma D_d2c60 : decode_any W_d2c60 = Some (Branch BC_NE 13 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c64 : bv 32 := 0xfff60613.
Lemma F_d2c64 : fetch_word Asan.M.loaded_segments (0xd2c64 : word) = Some W_d2c64.
Proof. vm_refl. Qed.
Lemma D_d2c64 : decode_any W_d2c64 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c68 : bv 32 := 0x00150513.
Lemma F_d2c68 : fetch_word Asan.M.loaded_segments (0xd2c68 : word) = Some W_d2c68.
Proof. vm_refl. Qed.
Lemma D_d2c68 : decode_any W_d2c68 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c6c : bv 32 := 0x00158593.
Lemma F_d2c6c : fetch_word Asan.M.loaded_segments (0xd2c6c : word) = Some W_d2c6c.
Proof. vm_refl. Qed.
Lemma D_d2c6c : decode_any W_d2c6c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c70 : bv 32 := 0xfe0614e3.
Lemma F_d2c70 : fetch_word Asan.M.loaded_segments (0xd2c70 : word) = Some W_d2c70.
Proof. vm_refl. Qed.
Lemma D_d2c70 : decode_any W_d2c70 = Some (Branch BC_NE 12 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c74 : bv 32 := 0x00000513.
Lemma F_d2c74 : fetch_word Asan.M.loaded_segments (0xd2c74 : word) = Some W_d2c74.
Proof. vm_refl. Qed.
Lemma D_d2c74 : decode_any W_d2c74 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c78 : bv 32 := 0x00008067.
Lemma F_d2c78 : fetch_word Asan.M.loaded_segments (0xd2c78 : word) = Some W_d2c78.
Proof. vm_refl. Qed.
Lemma D_d2c78 : decode_any W_d2c78 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d2c7c : bv 32 := 0x40e68533.
Lemma F_d2c7c : fetch_word Asan.M.loaded_segments (0xd2c7c : word) = Some W_d2c7c.
Proof. vm_refl. Qed.
Lemma D_d2c7c : decode_any W_d2c7c = Some (Op ALU_SUB 10 13 14, 4%Z).
Proof. vm_refl. Qed.

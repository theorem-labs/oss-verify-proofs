(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_92b54 : bv 32 := 0x10058463.
Lemma F_92b54 : fetch_word Plain.M.loaded_segments (0x92bac : word) = Some W_92b54.
Proof. vm_refl. Qed.
Lemma D_92b54 : decode_any W_92b54 = Some (Branch BC_EQ 11 0 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92b58 : bv 32 := 0x10060263.
Lemma F_92b58 : fetch_word Plain.M.loaded_segments (0x92bb0 : word) = Some W_92b58.
Proof. vm_refl. Qed.
Lemma D_92b58 : decode_any W_92b58 = Some (Branch BC_EQ 12 0 260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92b5c : bv 32 := 0x10068063.
Lemma F_92b5c : fetch_word Plain.M.loaded_segments (0x92bb4 : word) = Some W_92b5c.
Proof. vm_refl. Qed.
Lemma D_92b5c : decode_any W_92b5c = Some (Branch BC_EQ 13 0 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92b60 : bv 32 := 0x0e070e63.
Lemma F_92b60 : fetch_word Plain.M.loaded_segments (0x92bb8 : word) = Some W_92b60.
Proof. vm_refl. Qed.
Lemma D_92b60 : decode_any W_92b60 = Some (Branch BC_EQ 14 0 252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92b64 : bv 32 := 0x00072023.
Lemma F_92b64 : fetch_word Plain.M.loaded_segments (0x92bbc : word) = Some W_92b64.
Proof. vm_refl. Qed.
Lemma D_92b64 : decode_any W_92b64 = Some (Store SZ4 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92b68 : bv 32 := 0x0006a023.
Lemma F_92b68 : fetch_word Plain.M.loaded_segments (0x92bc0 : word) = Some W_92b68.
Proof. vm_refl. Qed.
Lemma D_92b68 : decode_any W_92b68 = Some (Store SZ4 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92b6c : bv 32 := 0x00062023.
Lemma F_92b6c : fetch_word Plain.M.loaded_segments (0x92bc4 : word) = Some W_92b6c.
Proof. vm_refl. Qed.
Lemma D_92b6c : decode_any W_92b6c = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92b70 : bv 32 := 0x0005a023.
Lemma F_92b70 : fetch_word Plain.M.loaded_segments (0x92bc8 : word) = Some W_92b70.
Proof. vm_refl. Qed.
Lemma D_92b70 : decode_any W_92b70 = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92b74 : bv 32 := 0x14050063.
Lemma F_92b74 : fetch_word Plain.M.loaded_segments (0x92bcc : word) = Some W_92b74.
Proof. vm_refl. Qed.
Lemma D_92b74 : decode_any W_92b74 = Some (Branch BC_EQ 10 0 320, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92b78 : bv 32 := 0x00052303.
Lemma F_92b78 : fetch_word Plain.M.loaded_segments (0x92bd0 : word) = Some W_92b78.
Proof. vm_refl. Qed.
Lemma D_92b78 : decode_any W_92b78 = Some (Load SZ4 true 6 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92b7c : bv 32 := 0x16605663.
Lemma F_92b7c : fetch_word Plain.M.loaded_segments (0x92bd4 : word) = Some W_92b7c.
Proof. vm_refl. Qed.
Lemma D_92b7c : decode_any W_92b7c = Some (Branch BC_GE 0 6 364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92b80 : bv 32 := 0xfb010113.
Lemma F_92b80 : fetch_word Plain.M.loaded_segments (0x92bd8 : word) = Some W_92b80.
Proof. vm_refl. Qed.
Lemma D_92b80 : decode_any W_92b80 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92b84 : bv 32 := 0x04813423.
Lemma F_92b84 : fetch_word Plain.M.loaded_segments (0x92bdc : word) = Some W_92b84.
Proof. vm_refl. Qed.
Lemma D_92b84 : decode_any W_92b84 = Some (Store SZ8 2 8 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92b88 : bv 32 := 0x04913023.
Lemma F_92b88 : fetch_word Plain.M.loaded_segments (0x92be0 : word) = Some W_92b88.
Proof. vm_refl. Qed.
Lemma D_92b88 : decode_any W_92b88 = Some (Store SZ8 2 9 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92b8c : bv 32 := 0x03213c23.
Lemma F_92b8c : fetch_word Plain.M.loaded_segments (0x92be4 : word) = Some W_92b8c.
Proof. vm_refl. Qed.
Lemma D_92b8c : decode_any W_92b8c = Some (Store SZ8 2 18 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92b90 : bv 32 := 0x03313823.
Lemma F_92b90 : fetch_word Plain.M.loaded_segments (0x92be8 : word) = Some W_92b90.
Proof. vm_refl. Qed.
Lemma D_92b90 : decode_any W_92b90 = Some (Store SZ8 2 19 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92b94 : bv 32 := 0x03413423.
Lemma F_92b94 : fetch_word Plain.M.loaded_segments (0x92bec : word) = Some W_92b94.
Proof. vm_refl. Qed.
Lemma D_92b94 : decode_any W_92b94 = Some (Store SZ8 2 20 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92b98 : bv 32 := 0x03513023.
Lemma F_92b98 : fetch_word Plain.M.loaded_segments (0x92bf0 : word) = Some W_92b98.
Proof. vm_refl. Qed.
Lemma D_92b98 : decode_any W_92b98 = Some (Store SZ8 2 21 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92b9c : bv 32 := 0x01613c23.
Lemma F_92b9c : fetch_word Plain.M.loaded_segments (0x92bf4 : word) = Some W_92b9c.
Proof. vm_refl. Qed.
Lemma D_92b9c : decode_any W_92b9c = Some (Store SZ8 2 22 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92ba0 : bv 32 := 0x01713823.
Lemma F_92ba0 : fetch_word Plain.M.loaded_segments (0x92bf8 : word) = Some W_92ba0.
Proof. vm_refl. Qed.
Lemma D_92ba0 : decode_any W_92ba0 = Some (Store SZ8 2 23 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92ba4 : bv 32 := 0x01813423.
Lemma F_92ba4 : fetch_word Plain.M.loaded_segments (0x92bfc : word) = Some W_92ba4.
Proof. vm_refl. Qed.
Lemma D_92ba4 : decode_any W_92ba4 = Some (Store SZ8 2 24 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92ba8 : bv 32 := 0x00000393.
Lemma F_92ba8 : fetch_word Plain.M.loaded_segments (0x92c00 : word) = Some W_92ba8.
Proof. vm_refl. Qed.
Lemma D_92ba8 : decode_any W_92ba8 = Some (OpImm ALU_ADD 7 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92bac : bv 32 := 0x00000793.
Lemma F_92bac : fetch_word Plain.M.loaded_segments (0x92c04 : word) = Some W_92bac.
Proof. vm_refl. Qed.
Lemma D_92bac : decode_any W_92bac = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92bb0 : bv 32 := 0x00000813.
Lemma F_92bb0 : fetch_word Plain.M.loaded_segments (0x92c08 : word) = Some W_92bb0.
Proof. vm_refl. Qed.
Lemma D_92bb0 : decode_any W_92bb0 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92bb4 : bv 32 := 0x00000893.
Lemma F_92bb4 : fetch_word Plain.M.loaded_segments (0x92c0c : word) = Some W_92bb4.
Proof. vm_refl. Qed.
Lemma D_92bb4 : decode_any W_92bb4 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92bb8 : bv 32 := 0x00000293.
Lemma F_92bb8 : fetch_word Plain.M.loaded_segments (0x92c10 : word) = Some W_92bb8.
Proof. vm_refl. Qed.
Lemma D_92bb8 : decode_any W_92bb8 = Some (OpImm ALU_ADD 5 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92bbc : bv 32 := 0x00456403.
Lemma F_92bbc : fetch_word Plain.M.loaded_segments (0x92c14 : word) = Some W_92bbc.
Proof. vm_refl. Qed.
Lemma D_92bbc : decode_any W_92bbc = Some (Load SZ4 false 8 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92bc0 : bv 32 := 0x00c52e03.
Lemma F_92bc0 : fetch_word Plain.M.loaded_segments (0x92c18 : word) = Some W_92bc0.
Proof. vm_refl. Qed.
Lemma D_92bc0 : decode_any W_92bc0 = Some (Load SZ4 true 28 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92bc4 : bv 32 := 0x00852e83.
Lemma F_92bc4 : fetch_word Plain.M.loaded_segments (0x92c1c : word) = Some W_92bc4.
Proof. vm_refl. Qed.
Lemma D_92bc4 : decode_any W_92bc4 = Some (Load SZ4 true 29 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92bc8 : bv 32 := 0x00040f1b.
Lemma F_92bc8 : fetch_word Plain.M.loaded_segments (0x92c20 : word) = Some W_92bc8.
Proof. vm_refl. Qed.
Lemma D_92bc8 : decode_any W_92bc8 = Some (OpImm32 30 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92bcc : bv 32 := 0x41c00fbb.
Lemma F_92bcc : fetch_word Plain.M.loaded_segments (0x92c24 : word) = Some W_92bcc.
Proof. vm_refl. Qed.
Lemma D_92bcc : decode_any W_92bcc = Some (Op32 ALU_SUB 31 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92bd0 : bv 32 := 0x00241413.
Lemma F_92bd0 : fetch_word Plain.M.loaded_segments (0x92c28 : word) = Some W_92bd0.
Proof. vm_refl. Qed.
Lemma D_92bd0 : decode_any W_92bd0 = Some (ShiftImm ALU_SLL 8 8 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92bd4 : bv 32 := 0x00100493.
Lemma F_92bd4 : fetch_word Plain.M.loaded_segments (0x92c2c : word) = Some W_92bd4.
Proof. vm_refl. Qed.
Lemma D_92bd4 : decode_any W_92bd4 = Some (OpImm ALU_ADD 9 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92bd8 : bv 32 := 0x00c0006f.
Lemma F_92bd8 : fetch_word Plain.M.loaded_segments (0x92c30 : word) = Some W_92bd8.
Proof. vm_refl. Qed.
Lemma D_92bd8 : decode_any W_92bd8 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92bdc : bv 32 := 0x00138393.
Lemma F_92bdc : fetch_word Plain.M.loaded_segments (0x92c34 : word) = Some W_92bdc.
Proof. vm_refl. Qed.
Lemma D_92bdc : decode_any W_92bdc = Some (OpImm ALU_ADD 7 7 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92be0 : bv 32 := 0x0a638463.
Lemma F_92be0 : fetch_word Plain.M.loaded_segments (0x92c38 : word) = Some W_92be0.
Proof. vm_refl. Qed.
Lemma D_92be0 : decode_any W_92be0 = Some (Branch BC_EQ 7 6 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92be4 : bv 32 := 0xffe05ce3.
Lemma F_92be4 : fetch_word Plain.M.loaded_segments (0x92c3c : word) = Some W_92be4.
Proof. vm_refl. Qed.
Lemma D_92be4 : decode_any W_92be4 = Some (Branch BC_GE 0 30 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92be8 : bv 32 := 0x01053903.
Lemma F_92be8 : fetch_word Plain.M.loaded_segments (0x92c40 : word) = Some W_92be8.
Proof. vm_refl. Qed.
Lemma D_92be8 : decode_any W_92be8 = Some (Load SZ8 true 18 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92bec : bv 32 := 0x00339993.
Lemma F_92bec : fetch_word Plain.M.loaded_segments (0x92c44 : word) = Some W_92bec.
Proof. vm_refl. Qed.
Lemma D_92bec : decode_any W_92bec = Some (ShiftImm ALU_SLL 19 7 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92bf0 : bv 32 := 0x01390933.
Lemma F_92bf0 : fetch_word Plain.M.loaded_segments (0x92c48 : word) = Some W_92bf0.
Proof. vm_refl. Qed.
Lemma D_92bf0 : decode_any W_92bf0 = Some (Op ALU_ADD 18 18 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92bf4 : bv 32 := 0x00093903.
Lemma F_92bf4 : fetch_word Plain.M.loaded_segments (0x92c4c : word) = Some W_92bf4.
Proof. vm_refl. Qed.
Lemma D_92bf4 : decode_any W_92bf4 = Some (Load SZ8 true 18 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92bf8 : bv 32 := 0x407e89bb.
Lemma F_92bf8 : fetch_word Plain.M.loaded_segments (0x92c50 : word) = Some W_92bf8.
Proof. vm_refl. Qed.
Lemma D_92bf8 : decode_any W_92bf8 = Some (Op32 ALU_SUB 19 29 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92bfc : bv 32 := 0x41d38a3b.
Lemma F_92bfc : fetch_word Plain.M.loaded_segments (0x92c54 : word) = Some W_92bfc.
Proof. vm_refl. Qed.
Lemma D_92bfc : decode_any W_92bfc = Some (Op32 ALU_SUB 20 7 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c00 : bv 32 := 0x00890ab3.
Lemma F_92c00 : fetch_word Plain.M.loaded_segments (0x92c58 : word) = Some W_92c00.
Proof. vm_refl. Qed.
Lemma D_92c00 : decode_any W_92c00 = Some (Op ALU_ADD 21 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c04 : bv 32 := 0x000e0b13.
Lemma F_92c04 : fetch_word Plain.M.loaded_segments (0x92c5c : word) = Some W_92c04.
Proof. vm_refl. Qed.
Lemma D_92c04 : decode_any W_92c04 = Some (OpImm ALU_ADD 22 28 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c08 : bv 32 := 0x000f8b93.
Lemma F_92c08 : fetch_word Plain.M.loaded_segments (0x92c60 : word) = Some W_92c08.
Proof. vm_refl. Qed.
Lemma D_92c08 : decode_any W_92c08 = Some (OpImm ALU_ADD 23 31 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c0c : bv 32 := 0x0140006f.
Lemma F_92c0c : fetch_word Plain.M.loaded_segments (0x92c64 : word) = Some W_92c0c.
Proof. vm_refl. Qed.
Lemma D_92c0c : decode_any W_92c0c = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c10 : bv 32 := 0x001b8b9b.
Lemma F_92c10 : fetch_word Plain.M.loaded_segments (0x92c68 : word) = Some W_92c10.
Proof. vm_refl. Qed.
Lemma D_92c10 : decode_any W_92c10 = Some (OpImm32 23 23 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c14 : bv 32 := 0x00490913.
Lemma F_92c14 : fetch_word Plain.M.loaded_segments (0x92c6c : word) = Some W_92c14.
Proof. vm_refl. Qed.
Lemma D_92c14 : decode_any W_92c14 = Some (OpImm ALU_ADD 18 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c18 : bv 32 := 0xfffb0b1b.
Lemma F_92c18 : fetch_word Plain.M.loaded_segments (0x92c70 : word) = Some W_92c18.
Proof. vm_refl. Qed.
Lemma D_92c18 : decode_any W_92c18 = Some (OpImm32 22 22 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c1c : bv 32 := 0xfd5900e3.
Lemma F_92c1c : fetch_word Plain.M.loaded_segments (0x92c74 : word) = Some W_92c1c.
Proof. vm_refl. Qed.
Lemma D_92c1c : decode_any W_92c1c = Some (Branch BC_EQ 18 21 8128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c20 : bv 32 := 0x00092c03.
Lemma F_92c20 : fetch_word Plain.M.loaded_segments (0x92c78 : word) = Some W_92c20.
Proof. vm_refl. Qed.
Lemma D_92c20 : decode_any W_92c20 = Some (Load SZ4 true 24 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c24 : bv 32 := 0xfe9c16e3.
Lemma F_92c24 : fetch_word Plain.M.loaded_segments (0x92c7c : word) = Some W_92c24.
Proof. vm_refl. Qed.
Lemma D_92c24 : decode_any W_92c24 = Some (Branch BC_NE 24 9 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c28 : bv 32 := 0x005b4e63.
Lemma F_92c28 : fetch_word Plain.M.loaded_segments (0x92c80 : word) = Some W_92c28.
Proof. vm_refl. Qed.
Lemma D_92c28 : decode_any W_92c28 = Some (Branch BC_LT 22 5 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c2c : bv 32 := 0x000b0293.
Lemma F_92c2c : fetch_word Plain.M.loaded_segments (0x92c84 : word) = Some W_92c2c.
Proof. vm_refl. Qed.
Lemma D_92c2c : decode_any W_92c2c = Some (OpImm ALU_ADD 5 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c30 : bv 32 := 0x0119dc63.
Lemma F_92c30 : fetch_word Plain.M.loaded_segments (0x92c88 : word) = Some W_92c30.
Proof. vm_refl. Qed.
Lemma D_92c30 : decode_any W_92c30 = Some (Branch BC_GE 19 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c34 : bv 32 := 0x010bce63.
Lemma F_92c34 : fetch_word Plain.M.loaded_segments (0x92c8c : word) = Some W_92c34.
Proof. vm_refl. Qed.
Lemma D_92c34 : decode_any W_92c34 = Some (Branch BC_LT 23 16 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c38 : bv 32 := 0x000b8813.
Lemma F_92c38 : fetch_word Plain.M.loaded_segments (0x92c90 : word) = Some W_92c38.
Proof. vm_refl. Qed.
Lemma D_92c38 : decode_any W_92c38 = Some (OpImm ALU_ADD 16 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c3c : bv 32 := 0xfcfa4ae3.
Lemma F_92c3c : fetch_word Plain.M.loaded_segments (0x92c94 : word) = Some W_92c3c.
Proof. vm_refl. Qed.
Lemma D_92c3c : decode_any W_92c3c = Some (Branch BC_LT 20 15 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c40 : bv 32 := 0x0140006f.
Lemma F_92c40 : fetch_word Plain.M.loaded_segments (0x92c98 : word) = Some W_92c40.
Proof. vm_refl. Qed.
Lemma D_92c40 : decode_any W_92c40 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c44 : bv 32 := 0xff19c8e3.
Lemma F_92c44 : fetch_word Plain.M.loaded_segments (0x92c9c : word) = Some W_92c44.
Proof. vm_refl. Qed.
Lemma D_92c44 : decode_any W_92c44 = Some (Branch BC_LT 19 17 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c48 : bv 32 := 0x00098893.
Lemma F_92c48 : fetch_word Plain.M.loaded_segments (0x92ca0 : word) = Some W_92c48.
Proof. vm_refl. Qed.
Lemma D_92c48 : decode_any W_92c48 = Some (OpImm ALU_ADD 17 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c4c : bv 32 := 0xff0bd6e3.
Lemma F_92c4c : fetch_word Plain.M.loaded_segments (0x92ca4 : word) = Some W_92c4c.
Proof. vm_refl. Qed.
Lemma D_92c4c : decode_any W_92c4c = Some (Branch BC_GE 23 16 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c50 : bv 32 := 0xfcfa40e3.
Lemma F_92c50 : fetch_word Plain.M.loaded_segments (0x92ca8 : word) = Some W_92c50.
Proof. vm_refl. Qed.
Lemma D_92c50 : decode_any W_92c50 = Some (Branch BC_LT 20 15 8128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c54 : bv 32 := 0x000a0793.
Lemma F_92c54 : fetch_word Plain.M.loaded_segments (0x92cac : word) = Some W_92c54.
Proof. vm_refl. Qed.
Lemma D_92c54 : decode_any W_92c54 = Some (OpImm ALU_ADD 15 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c58 : bv 32 := 0xfb9ff06f.
Lemma F_92c58 : fetch_word Plain.M.loaded_segments (0x92cb0 : word) = Some W_92c58.
Proof. vm_refl. Qed.
Lemma D_92c58 : decode_any W_92c58 = Some (Jal 0 2097080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c5c : bv 32 := 0x00080517.
Lemma F_92c5c : fetch_word Plain.M.loaded_segments (0x92cb4 : word) = Some W_92c5c.
Proof. vm_refl. Qed.
Lemma D_92c5c : decode_any W_92c5c = Some (Auipc 10 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c60 : bv 32 := 0x91453503.
Lemma F_92c60 : fetch_word Plain.M.loaded_segments (0x92cb8 : word) = Some W_92c60.
Proof. vm_refl. Qed.
Lemma D_92c60 : decode_any W_92c60 = Some (Load SZ8 true 10 10 2324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c64 : bv 32 := 0x00052503.
Lemma F_92c64 : fetch_word Plain.M.loaded_segments (0x92cbc : word) = Some W_92c64.
Proof. vm_refl. Qed.
Lemma D_92c64 : decode_any W_92c64 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c68 : bv 32 := 0x00500593.
Lemma F_92c68 : fetch_word Plain.M.loaded_segments (0x92cc0 : word) = Some W_92c68.
Proof. vm_refl. Qed.
Lemma D_92c68 : decode_any W_92c68 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c6c : bv 32 := 0x06a5ca63.
Lemma F_92c6c : fetch_word Plain.M.loaded_segments (0x92cc4 : word) = Some W_92c6c.
Proof. vm_refl. Qed.
Lemma D_92c6c : decode_any W_92c6c = Some (Branch BC_LT 11 10 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c70 : bv 32 := 0xfff8a517.
Lemma F_92c70 : fetch_word Plain.M.loaded_segments (0x92cc8 : word) = Some W_92c70.
Proof. vm_refl. Qed.
Lemma D_92c70 : decode_any W_92c70 = Some (Auipc 10 1048458, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c74 : bv 32 := 0xfff80597.
Lemma F_92c74 : fetch_word Plain.M.loaded_segments (0x92ccc : word) = Some W_92c74.
Proof. vm_refl. Qed.
Lemma D_92c74 : decode_any W_92c74 = Some (Auipc 11 1048448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c78 : bv 32 := 0xd0750513.
Lemma F_92c78 : fetch_word Plain.M.loaded_segments (0x92cd0 : word) = Some W_92c78.
Proof. vm_refl. Qed.
Lemma D_92c78 : decode_any W_92c78 = Some (OpImm ALU_ADD 10 10 3335, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c7c : bv 32 := 0x2c358593.
Lemma F_92c7c : fetch_word Plain.M.loaded_segments (0x92cd4 : word) = Some W_92c7c.
Proof. vm_refl. Qed.
Lemma D_92c7c : decode_any W_92c7c = Some (OpImm ALU_ADD 11 11 707, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c80 : bv 32 := 0x00100613.
Lemma F_92c80 : fetch_word Plain.M.loaded_segments (0x92cd8 : word) = Some W_92c80.
Proof. vm_refl. Qed.
Lemma D_92c80 : decode_any W_92c80 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c84 : bv 32 := 0xb70d006f.
Lemma F_92c84 : fetch_word Plain.M.loaded_segments (0x92cdc : word) = Some W_92c84.
Proof. vm_refl. Qed.
Lemma D_92c84 : decode_any W_92c84 = Some (Jal 0 1901424, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c88 : bv 32 := 0x04813403.
Lemma F_92c88 : fetch_word Plain.M.loaded_segments (0x92ce0 : word) = Some W_92c88.
Proof. vm_refl. Qed.
Lemma D_92c88 : decode_any W_92c88 = Some (Load SZ8 true 8 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c8c : bv 32 := 0x04013483.
Lemma F_92c8c : fetch_word Plain.M.loaded_segments (0x92ce4 : word) = Some W_92c8c.
Proof. vm_refl. Qed.
Lemma D_92c8c : decode_any W_92c8c = Some (Load SZ8 true 9 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c90 : bv 32 := 0x03813903.
Lemma F_92c90 : fetch_word Plain.M.loaded_segments (0x92ce8 : word) = Some W_92c90.
Proof. vm_refl. Qed.
Lemma D_92c90 : decode_any W_92c90 = Some (Load SZ8 true 18 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c94 : bv 32 := 0x03013983.
Lemma F_92c94 : fetch_word Plain.M.loaded_segments (0x92cec : word) = Some W_92c94.
Proof. vm_refl. Qed.
Lemma D_92c94 : decode_any W_92c94 = Some (Load SZ8 true 19 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c98 : bv 32 := 0x02813a03.
Lemma F_92c98 : fetch_word Plain.M.loaded_segments (0x92cf0 : word) = Some W_92c98.
Proof. vm_refl. Qed.
Lemma D_92c98 : decode_any W_92c98 = Some (Load SZ8 true 20 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92c9c : bv 32 := 0x02013a83.
Lemma F_92c9c : fetch_word Plain.M.loaded_segments (0x92cf4 : word) = Some W_92c9c.
Proof. vm_refl. Qed.
Lemma D_92c9c : decode_any W_92c9c = Some (Load SZ8 true 21 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92ca0 : bv 32 := 0x01813b03.
Lemma F_92ca0 : fetch_word Plain.M.loaded_segments (0x92cf8 : word) = Some W_92ca0.
Proof. vm_refl. Qed.
Lemma D_92ca0 : decode_any W_92ca0 = Some (Load SZ8 true 22 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92ca4 : bv 32 := 0x01013b83.
Lemma F_92ca4 : fetch_word Plain.M.loaded_segments (0x92cfc : word) = Some W_92ca4.
Proof. vm_refl. Qed.
Lemma D_92ca4 : decode_any W_92ca4 = Some (Load SZ8 true 23 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92ca8 : bv 32 := 0x00813c03.
Lemma F_92ca8 : fetch_word Plain.M.loaded_segments (0x92d00 : word) = Some W_92ca8.
Proof. vm_refl. Qed.
Lemma D_92ca8 : decode_any W_92ca8 = Some (Load SZ8 true 24 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92cac : bv 32 := 0x05010113.
Lemma F_92cac : fetch_word Plain.M.loaded_segments (0x92d04 : word) = Some W_92cac.
Proof. vm_refl. Qed.
Lemma D_92cac : decode_any W_92cac = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92cb0 : bv 32 := 0x0480006f.
Lemma F_92cb0 : fetch_word Plain.M.loaded_segments (0x92d08 : word) = Some W_92cb0.
Proof. vm_refl. Qed.
Lemma D_92cb0 : decode_any W_92cb0 = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92cb4 : bv 32 := 0x00080517.
Lemma F_92cb4 : fetch_word Plain.M.loaded_segments (0x92d0c : word) = Some W_92cb4.
Proof. vm_refl. Qed.
Lemma D_92cb4 : decode_any W_92cb4 = Some (Auipc 10 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92cb8 : bv 32 := 0x8bc53503.
Lemma F_92cb8 : fetch_word Plain.M.loaded_segments (0x92d10 : word) = Some W_92cb8.
Proof. vm_refl. Qed.
Lemma D_92cb8 : decode_any W_92cb8 = Some (Load SZ8 true 10 10 2236, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92cbc : bv 32 := 0x00052503.
Lemma F_92cbc : fetch_word Plain.M.loaded_segments (0x92d14 : word) = Some W_92cbc.
Proof. vm_refl. Qed.
Lemma D_92cbc : decode_any W_92cbc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92cc0 : bv 32 := 0x00500593.
Lemma F_92cc0 : fetch_word Plain.M.loaded_segments (0x92d18 : word) = Some W_92cc0.
Proof. vm_refl. Qed.
Lemma D_92cc0 : decode_any W_92cc0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92cc4 : bv 32 := 0x00a5ce63.
Lemma F_92cc4 : fetch_word Plain.M.loaded_segments (0x92d1c : word) = Some W_92cc4.
Proof. vm_refl. Qed.
Lemma D_92cc4 : decode_any W_92cc4 = Some (Branch BC_LT 11 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92cc8 : bv 32 := 0xfff84517.
Lemma F_92cc8 : fetch_word Plain.M.loaded_segments (0x92d20 : word) = Some W_92cc8.
Proof. vm_refl. Qed.
Lemma D_92cc8 : decode_any W_92cc8 = Some (Auipc 10 1048452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92ccc : bv 32 := 0xfff80597.
Lemma F_92ccc : fetch_word Plain.M.loaded_segments (0x92d24 : word) = Some W_92ccc.
Proof. vm_refl. Qed.
Lemma D_92ccc : decode_any W_92ccc = Some (Auipc 11 1048448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92cd0 : bv 32 := 0x4c950513.
Lemma F_92cd0 : fetch_word Plain.M.loaded_segments (0x92d28 : word) = Some W_92cd0.
Proof. vm_refl. Qed.
Lemma D_92cd0 : decode_any W_92cd0 = Some (OpImm ALU_ADD 10 10 1225, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92cd4 : bv 32 := 0x26b58593.
Lemma F_92cd4 : fetch_word Plain.M.loaded_segments (0x92d2c : word) = Some W_92cd4.
Proof. vm_refl. Qed.
Lemma D_92cd4 : decode_any W_92cd4 = Some (OpImm ALU_ADD 11 11 619, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92cd8 : bv 32 := 0x00100613.
Lemma F_92cd8 : fetch_word Plain.M.loaded_segments (0x92d30 : word) = Some W_92cd8.
Proof. vm_refl. Qed.
Lemma D_92cd8 : decode_any W_92cd8 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92cdc : bv 32 := 0xb18d006f.
Lemma F_92cdc : fetch_word Plain.M.loaded_segments (0x92d34 : word) = Some W_92cdc.
Proof. vm_refl. Qed.
Lemma D_92cdc : decode_any W_92cdc = Some (Jal 0 1901336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92ce0 : bv 32 := 0x00100513.
Lemma F_92ce0 : fetch_word Plain.M.loaded_segments (0x92d38 : word) = Some W_92ce0.
Proof. vm_refl. Qed.
Lemma D_92ce0 : decode_any W_92ce0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92ce4 : bv 32 := 0x00008067.
Lemma F_92ce4 : fetch_word Plain.M.loaded_segments (0x92d3c : word) = Some W_92ce4.
Proof. vm_refl. Qed.
Lemma D_92ce4 : decode_any W_92ce4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92ce8 : bv 32 := 0x00000293.
Lemma F_92ce8 : fetch_word Plain.M.loaded_segments (0x92d40 : word) = Some W_92ce8.
Proof. vm_refl. Qed.
Lemma D_92ce8 : decode_any W_92ce8 = Some (OpImm ALU_ADD 5 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92cec : bv 32 := 0x00000893.
Lemma F_92cec : fetch_word Plain.M.loaded_segments (0x92d44 : word) = Some W_92cec.
Proof. vm_refl. Qed.
Lemma D_92cec : decode_any W_92cec = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92cf0 : bv 32 := 0x00000813.
Lemma F_92cf0 : fetch_word Plain.M.loaded_segments (0x92d48 : word) = Some W_92cf0.
Proof. vm_refl. Qed.
Lemma D_92cf0 : decode_any W_92cf0 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92cf4 : bv 32 := 0x00000793.
Lemma F_92cf4 : fetch_word Plain.M.loaded_segments (0x92d4c : word) = Some W_92cf4.
Proof. vm_refl. Qed.
Lemma D_92cf4 : decode_any W_92cf4 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92cf8 : bv 32 := 0x00000513.
Lemma F_92cf8 : fetch_word Plain.M.loaded_segments (0x92d50 : word) = Some W_92cf8.
Proof. vm_refl. Qed.
Lemma D_92cf8 : decode_any W_92cf8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92cfc : bv 32 := 0x0055a023.
Lemma F_92cfc : fetch_word Plain.M.loaded_segments (0x92d54 : word) = Some W_92cfc.
Proof. vm_refl. Qed.
Lemma D_92cfc : decode_any W_92cfc = Some (Store SZ4 11 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92d00 : bv 32 := 0x01162023.
Lemma F_92d00 : fetch_word Plain.M.loaded_segments (0x92d58 : word) = Some W_92d00.
Proof. vm_refl. Qed.
Lemma D_92d00 : decode_any W_92d00 = Some (Store SZ4 12 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92d04 : bv 32 := 0x0106a023.
Lemma F_92d04 : fetch_word Plain.M.loaded_segments (0x92d5c : word) = Some W_92d04.
Proof. vm_refl. Qed.
Lemma D_92d04 : decode_any W_92d04 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92d08 : bv 32 := 0x00f72023.
Lemma F_92d08 : fetch_word Plain.M.loaded_segments (0x92d60 : word) = Some W_92d08.
Proof. vm_refl. Qed.
Lemma D_92d08 : decode_any W_92d08 = Some (Store SZ4 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92d0c : bv 32 := 0x00008067.
Lemma F_92d0c : fetch_word Plain.M.loaded_segments (0x92d64 : word) = Some W_92d0c.
Proof. vm_refl. Qed.
Lemma D_92d0c : decode_any W_92d0c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

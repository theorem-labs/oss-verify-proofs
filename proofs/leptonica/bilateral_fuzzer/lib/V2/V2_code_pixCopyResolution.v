(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_19bf4 : bv 32 := 0x02058663.
Lemma F_19bf4 : fetch_word Ubsan.M.loaded_segments (0x19bf4 : word) = Some W_19bf4.
Proof. vm_refl. Qed.
Lemma D_19bf4 : decode_any W_19bf4 = Some (Branch BC_EQ 11 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bf8 : bv 32 := 0x04050a63.
Lemma F_19bf8 : fetch_word Ubsan.M.loaded_segments (0x19bf8 : word) = Some W_19bf8.
Proof. vm_refl. Qed.
Lemma D_19bf8 : decode_any W_19bf8 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bfc : bv 32 := 0x00a58e63.
Lemma F_19bfc : fetch_word Ubsan.M.loaded_segments (0x19bfc : word) = Some W_19bfc.
Proof. vm_refl. Qed.
Lemma D_19bfc : decode_any W_19bfc = Some (Branch BC_EQ 11 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c00 : bv 32 := 0x0075f613.
Lemma F_19c00 : fetch_word Ubsan.M.loaded_segments (0x19c00 : word) = Some W_19c00.
Proof. vm_refl. Qed.
Lemma D_19c00 : decode_any W_19c00 = Some (OpImm ALU_AND 12 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c04 : bv 32 := 0x06061e63.
Lemma F_19c04 : fetch_word Ubsan.M.loaded_segments (0x19c04 : word) = Some W_19c04.
Proof. vm_refl. Qed.
Lemma D_19c04 : decode_any W_19c04 = Some (Branch BC_NE 12 0 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c08 : bv 32 := 0x00757613.
Lemma F_19c08 : fetch_word Ubsan.M.loaded_segments (0x19c08 : word) = Some W_19c08.
Proof. vm_refl. Qed.
Lemma D_19c08 : decode_any W_19c08 = Some (OpImm ALU_AND 12 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c0c : bv 32 := 0x06061a63.
Lemma F_19c0c : fetch_word Ubsan.M.loaded_segments (0x19c0c : word) = Some W_19c0c.
Proof. vm_refl. Qed.
Lemma D_19c0c : decode_any W_19c0c = Some (Branch BC_NE 12 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c10 : bv 32 := 0x0185b583.
Lemma F_19c10 : fetch_word Ubsan.M.loaded_segments (0x19c10 : word) = Some W_19c10.
Proof. vm_refl. Qed.
Lemma D_19c10 : decode_any W_19c10 = Some (Load SZ8 true 11 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c14 : bv 32 := 0x00b53c23.
Lemma F_19c14 : fetch_word Ubsan.M.loaded_segments (0x19c14 : word) = Some W_19c14.
Proof. vm_refl. Qed.
Lemma D_19c14 : decode_any W_19c14 = Some (Store SZ8 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c18 : bv 32 := 0x00000513.
Lemma F_19c18 : fetch_word Ubsan.M.loaded_segments (0x19c18 : word) = Some W_19c18.
Proof. vm_refl. Qed.
Lemma D_19c18 : decode_any W_19c18 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c1c : bv 32 := 0x00008067.
Lemma F_19c1c : fetch_word Ubsan.M.loaded_segments (0x19c1c : word) = Some W_19c1c.
Proof. vm_refl. Qed.
Lemma D_19c1c : decode_any W_19c1c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c20 : bv 32 := 0x0002b517.
Lemma F_19c20 : fetch_word Ubsan.M.loaded_segments (0x19c20 : word) = Some W_19c20.
Proof. vm_refl. Qed.
Lemma D_19c20 : decode_any W_19c20 = Some (Auipc 10 43, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c24 : bv 32 := 0x27853503.
Lemma F_19c24 : fetch_word Ubsan.M.loaded_segments (0x19c24 : word) = Some W_19c24.
Proof. vm_refl. Qed.
Lemma D_19c24 : decode_any W_19c24 = Some (Load SZ8 true 10 10 632, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c28 : bv 32 := 0x00052503.
Lemma F_19c28 : fetch_word Ubsan.M.loaded_segments (0x19c28 : word) = Some W_19c28.
Proof. vm_refl. Qed.
Lemma D_19c28 : decode_any W_19c28 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c2c : bv 32 := 0x00500593.
Lemma F_19c2c : fetch_word Ubsan.M.loaded_segments (0x19c2c : word) = Some W_19c2c.
Proof. vm_refl. Qed.
Lemma D_19c2c : decode_any W_19c2c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c30 : bv 32 := 0x04a5c463.
Lemma F_19c30 : fetch_word Ubsan.M.loaded_segments (0x19c30 : word) = Some W_19c30.
Proof. vm_refl. Qed.
Lemma D_19c30 : decode_any W_19c30 = Some (Branch BC_LT 11 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c34 : bv 32 := 0xffff6517.
Lemma F_19c34 : fetch_word Ubsan.M.loaded_segments (0x19c34 : word) = Some W_19c34.
Proof. vm_refl. Qed.
Lemma D_19c34 : decode_any W_19c34 = Some (Auipc 10 1048566, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c38 : bv 32 := 0xffff7597.
Lemma F_19c38 : fetch_word Ubsan.M.loaded_segments (0x19c38 : word) = Some W_19c38.
Proof. vm_refl. Qed.
Lemma D_19c38 : decode_any W_19c38 = Some (Auipc 11 1048567, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c3c : bv 32 := 0x68050513.
Lemma F_19c3c : fetch_word Ubsan.M.loaded_segments (0x19c3c : word) = Some W_19c3c.
Proof. vm_refl. Qed.
Lemma D_19c3c : decode_any W_19c3c = Some (OpImm ALU_ADD 10 10 1664, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c40 : bv 32 := 0xff258593.
Lemma F_19c40 : fetch_word Ubsan.M.loaded_segments (0x19c40 : word) = Some W_19c40.
Proof. vm_refl. Qed.
Lemma D_19c40 : decode_any W_19c40 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c44 : bv 32 := 0x00100613.
Lemma F_19c44 : fetch_word Ubsan.M.loaded_segments (0x19c44 : word) = Some W_19c44.
Proof. vm_refl. Qed.
Lemma D_19c44 : decode_any W_19c44 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c48 : bv 32 := 0x9acfe06f.
Lemma F_19c48 : fetch_word Ubsan.M.loaded_segments (0x19c48 : word) = Some W_19c48.
Proof. vm_refl. Qed.
Lemma D_19c48 : decode_any W_19c48 = Some (Jal 0 2089388, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c4c : bv 32 := 0x0002b517.
Lemma F_19c4c : fetch_word Ubsan.M.loaded_segments (0x19c4c : word) = Some W_19c4c.
Proof. vm_refl. Qed.
Lemma D_19c4c : decode_any W_19c4c = Some (Auipc 10 43, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c50 : bv 32 := 0x24c53503.
Lemma F_19c50 : fetch_word Ubsan.M.loaded_segments (0x19c50 : word) = Some W_19c50.
Proof. vm_refl. Qed.
Lemma D_19c50 : decode_any W_19c50 = Some (Load SZ8 true 10 10 588, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c54 : bv 32 := 0x00052503.
Lemma F_19c54 : fetch_word Ubsan.M.loaded_segments (0x19c54 : word) = Some W_19c54.
Proof. vm_refl. Qed.
Lemma D_19c54 : decode_any W_19c54 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c58 : bv 32 := 0x00500593.
Lemma F_19c58 : fetch_word Ubsan.M.loaded_segments (0x19c58 : word) = Some W_19c58.
Proof. vm_refl. Qed.
Lemma D_19c58 : decode_any W_19c58 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c5c : bv 32 := 0x00a5ce63.
Lemma F_19c5c : fetch_word Ubsan.M.loaded_segments (0x19c5c : word) = Some W_19c5c.
Proof. vm_refl. Qed.
Lemma D_19c5c : decode_any W_19c5c = Some (Branch BC_LT 11 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c60 : bv 32 := 0xffff8517.
Lemma F_19c60 : fetch_word Ubsan.M.loaded_segments (0x19c60 : word) = Some W_19c60.
Proof. vm_refl. Qed.
Lemma D_19c60 : decode_any W_19c60 = Some (Auipc 10 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c64 : bv 32 := 0xffff7597.
Lemma F_19c64 : fetch_word Ubsan.M.loaded_segments (0x19c64 : word) = Some W_19c64.
Proof. vm_refl. Qed.
Lemma D_19c64 : decode_any W_19c64 = Some (Auipc 11 1048567, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c68 : bv 32 := 0xcd050513.
Lemma F_19c68 : fetch_word Ubsan.M.loaded_segments (0x19c68 : word) = Some W_19c68.
Proof. vm_refl. Qed.
Lemma D_19c68 : decode_any W_19c68 = Some (OpImm ALU_ADD 10 10 3280, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c6c : bv 32 := 0xfc658593.
Lemma F_19c6c : fetch_word Ubsan.M.loaded_segments (0x19c6c : word) = Some W_19c6c.
Proof. vm_refl. Qed.
Lemma D_19c6c : decode_any W_19c6c = Some (OpImm ALU_ADD 11 11 4038, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c70 : bv 32 := 0x00100613.
Lemma F_19c70 : fetch_word Ubsan.M.loaded_segments (0x19c70 : word) = Some W_19c70.
Proof. vm_refl. Qed.
Lemma D_19c70 : decode_any W_19c70 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c74 : bv 32 := 0x980fe06f.
Lemma F_19c74 : fetch_word Ubsan.M.loaded_segments (0x19c74 : word) = Some W_19c74.
Proof. vm_refl. Qed.
Lemma D_19c74 : decode_any W_19c74 = Some (Jal 0 2089344, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c78 : bv 32 := 0x00100513.
Lemma F_19c78 : fetch_word Ubsan.M.loaded_segments (0x19c78 : word) = Some W_19c78.
Proof. vm_refl. Qed.
Lemma D_19c78 : decode_any W_19c78 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c7c : bv 32 := 0x00008067.
Lemma F_19c7c : fetch_word Ubsan.M.loaded_segments (0x19c7c : word) = Some W_19c7c.
Proof. vm_refl. Qed.
Lemma D_19c7c : decode_any W_19c7c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19c80 : bv 32 := 0xc0001073.
Lemma F_19c80 : fetch_word Ubsan.M.loaded_segments (0x19c80 : word) = Some W_19c80.
Proof. vm_refl. Qed.
Lemma D_19c80 : decode_any W_19c80 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.

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

Definition W_1a9f0 : bv 32 := 0x00050a63.
Lemma F_1a9f0 : fetch_word Ubsan.M.loaded_segments (0x1a9f0 : word) = Some W_1a9f0.
Proof. vm_refl. Qed.
Lemma D_1a9f0 : decode_any W_1a9f0 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a9f4 : bv 32 := 0x00757593.
Lemma F_1a9f4 : fetch_word Ubsan.M.loaded_segments (0x1a9f4 : word) = Some W_1a9f4.
Proof. vm_refl. Qed.
Lemma D_1a9f4 : decode_any W_1a9f4 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a9f8 : bv 32 := 0x04059063.
Lemma F_1a9f8 : fetch_word Ubsan.M.loaded_segments (0x1a9f8 : word) = Some W_1a9f8.
Proof. vm_refl. Qed.
Lemma D_1a9f8 : decode_any W_1a9f8 = Some (Branch BC_NE 11 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a9fc : bv 32 := 0x03053503.
Lemma F_1a9fc : fetch_word Ubsan.M.loaded_segments (0x1a9fc : word) = Some W_1a9fc.
Proof. vm_refl. Qed.
Lemma D_1a9fc : decode_any W_1a9fc = Some (Load SZ8 true 10 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_1aa00 : bv 32 := 0x00008067.
Lemma F_1aa00 : fetch_word Ubsan.M.loaded_segments (0x1aa00 : word) = Some W_1aa00.
Proof. vm_refl. Qed.
Lemma D_1aa00 : decode_any W_1aa00 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1aa04 : bv 32 := 0x0002a517.
Lemma F_1aa04 : fetch_word Ubsan.M.loaded_segments (0x1aa04 : word) = Some W_1aa04.
Proof. vm_refl. Qed.
Lemma D_1aa04 : decode_any W_1aa04 = Some (Auipc 10 42, 4%Z).
Proof. vm_refl. Qed.

Definition W_1aa08 : bv 32 := 0x49453503.
Lemma F_1aa08 : fetch_word Ubsan.M.loaded_segments (0x1aa08 : word) = Some W_1aa08.
Proof. vm_refl. Qed.
Lemma D_1aa08 : decode_any W_1aa08 = Some (Load SZ8 true 10 10 1172, 4%Z).
Proof. vm_refl. Qed.

Definition W_1aa0c : bv 32 := 0x00052503.
Lemma F_1aa0c : fetch_word Ubsan.M.loaded_segments (0x1aa0c : word) = Some W_1aa0c.
Proof. vm_refl. Qed.
Lemma D_1aa0c : decode_any W_1aa0c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1aa10 : bv 32 := 0x00500593.
Lemma F_1aa10 : fetch_word Ubsan.M.loaded_segments (0x1aa10 : word) = Some W_1aa10.
Proof. vm_refl. Qed.
Lemma D_1aa10 : decode_any W_1aa10 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1aa14 : bv 32 := 0x00a5ce63.
Lemma F_1aa14 : fetch_word Ubsan.M.loaded_segments (0x1aa14 : word) = Some W_1aa14.
Proof. vm_refl. Qed.
Lemma D_1aa14 : decode_any W_1aa14 = Some (Branch BC_LT 11 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_1aa18 : bv 32 := 0xffff6517.
Lemma F_1aa18 : fetch_word Ubsan.M.loaded_segments (0x1aa18 : word) = Some W_1aa18.
Proof. vm_refl. Qed.
Lemma D_1aa18 : decode_any W_1aa18 = Some (Auipc 10 1048566, 4%Z).
Proof. vm_refl. Qed.

Definition W_1aa1c : bv 32 := 0xffff6597.
Lemma F_1aa1c : fetch_word Ubsan.M.loaded_segments (0x1aa1c : word) = Some W_1aa1c.
Proof. vm_refl. Qed.
Lemma D_1aa1c : decode_any W_1aa1c = Some (Auipc 11 1048566, 4%Z).
Proof. vm_refl. Qed.

Definition W_1aa20 : bv 32 := 0xa4d50513.
Lemma F_1aa20 : fetch_word Ubsan.M.loaded_segments (0x1aa20 : word) = Some W_1aa20.
Proof. vm_refl. Qed.
Lemma D_1aa20 : decode_any W_1aa20 = Some (OpImm ALU_ADD 10 10 2637, 4%Z).
Proof. vm_refl. Qed.

Definition W_1aa24 : bv 32 := 0xc0458593.
Lemma F_1aa24 : fetch_word Ubsan.M.loaded_segments (0x1aa24 : word) = Some W_1aa24.
Proof. vm_refl. Qed.
Lemma D_1aa24 : decode_any W_1aa24 = Some (OpImm ALU_ADD 11 11 3076, 4%Z).
Proof. vm_refl. Qed.

Definition W_1aa28 : bv 32 := 0x00000613.
Lemma F_1aa28 : fetch_word Ubsan.M.loaded_segments (0x1aa28 : word) = Some W_1aa28.
Proof. vm_refl. Qed.
Lemma D_1aa28 : decode_any W_1aa28 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1aa2c : bv 32 := 0xc98fd06f.
Lemma F_1aa2c : fetch_word Ubsan.M.loaded_segments (0x1aa2c : word) = Some W_1aa2c.
Proof. vm_refl. Qed.
Lemma D_1aa2c : decode_any W_1aa2c = Some (Jal 0 2086040, 4%Z).
Proof. vm_refl. Qed.

Definition W_1aa30 : bv 32 := 0x00000513.
Lemma F_1aa30 : fetch_word Ubsan.M.loaded_segments (0x1aa30 : word) = Some W_1aa30.
Proof. vm_refl. Qed.
Lemma D_1aa30 : decode_any W_1aa30 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1aa34 : bv 32 := 0x00008067.
Lemma F_1aa34 : fetch_word Ubsan.M.loaded_segments (0x1aa34 : word) = Some W_1aa34.
Proof. vm_refl. Qed.
Lemma D_1aa34 : decode_any W_1aa34 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1aa38 : bv 32 := 0xc0001073.
Lemma F_1aa38 : fetch_word Ubsan.M.loaded_segments (0x1aa38 : word) = Some W_1aa38.
Proof. vm_refl. Qed.
Lemma D_1aa38 : decode_any W_1aa38 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.

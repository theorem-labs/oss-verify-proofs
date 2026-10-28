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

Definition W_1a8cc : bv 32 := 0x00050a63.
Lemma F_1a8cc : fetch_word Ubsan.M.loaded_segments (0x1a8cc : word) = Some W_1a8cc.
Proof. vm_refl. Qed.
Lemma D_1a8cc : decode_any W_1a8cc = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8d0 : bv 32 := 0x00757593.
Lemma F_1a8d0 : fetch_word Ubsan.M.loaded_segments (0x1a8d0 : word) = Some W_1a8d0.
Proof. vm_refl. Qed.
Lemma D_1a8d0 : decode_any W_1a8d0 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8d4 : bv 32 := 0x04059063.
Lemma F_1a8d4 : fetch_word Ubsan.M.loaded_segments (0x1a8d4 : word) = Some W_1a8d4.
Proof. vm_refl. Qed.
Lemma D_1a8d4 : decode_any W_1a8d4 = Some (Branch BC_NE 11 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8d8 : bv 32 := 0x00852503.
Lemma F_1a8d8 : fetch_word Ubsan.M.loaded_segments (0x1a8d8 : word) = Some W_1a8d8.
Proof. vm_refl. Qed.
Lemma D_1a8d8 : decode_any W_1a8d8 = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8dc : bv 32 := 0x00008067.
Lemma F_1a8dc : fetch_word Ubsan.M.loaded_segments (0x1a8dc : word) = Some W_1a8dc.
Proof. vm_refl. Qed.
Lemma D_1a8dc : decode_any W_1a8dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8e0 : bv 32 := 0x0002a517.
Lemma F_1a8e0 : fetch_word Ubsan.M.loaded_segments (0x1a8e0 : word) = Some W_1a8e0.
Proof. vm_refl. Qed.
Lemma D_1a8e0 : decode_any W_1a8e0 = Some (Auipc 10 42, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8e4 : bv 32 := 0x5b853503.
Lemma F_1a8e4 : fetch_word Ubsan.M.loaded_segments (0x1a8e4 : word) = Some W_1a8e4.
Proof. vm_refl. Qed.
Lemma D_1a8e4 : decode_any W_1a8e4 = Some (Load SZ8 true 10 10 1464, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8e8 : bv 32 := 0x00052503.
Lemma F_1a8e8 : fetch_word Ubsan.M.loaded_segments (0x1a8e8 : word) = Some W_1a8e8.
Proof. vm_refl. Qed.
Lemma D_1a8e8 : decode_any W_1a8e8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8ec : bv 32 := 0x00500593.
Lemma F_1a8ec : fetch_word Ubsan.M.loaded_segments (0x1a8ec : word) = Some W_1a8ec.
Proof. vm_refl. Qed.
Lemma D_1a8ec : decode_any W_1a8ec = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8f0 : bv 32 := 0x00a5ce63.
Lemma F_1a8f0 : fetch_word Ubsan.M.loaded_segments (0x1a8f0 : word) = Some W_1a8f0.
Proof. vm_refl. Qed.
Lemma D_1a8f0 : decode_any W_1a8f0 = Some (Branch BC_LT 11 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8f4 : bv 32 := 0xffff6517.
Lemma F_1a8f4 : fetch_word Ubsan.M.loaded_segments (0x1a8f4 : word) = Some W_1a8f4.
Proof. vm_refl. Qed.
Lemma D_1a8f4 : decode_any W_1a8f4 = Some (Auipc 10 1048566, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8f8 : bv 32 := 0xffff6597.
Lemma F_1a8f8 : fetch_word Ubsan.M.loaded_segments (0x1a8f8 : word) = Some W_1a8f8.
Proof. vm_refl. Qed.
Lemma D_1a8f8 : decode_any W_1a8f8 = Some (Auipc 11 1048566, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a8fc : bv 32 := 0xb7150513.
Lemma F_1a8fc : fetch_word Ubsan.M.loaded_segments (0x1a8fc : word) = Some W_1a8fc.
Proof. vm_refl. Qed.
Lemma D_1a8fc : decode_any W_1a8fc = Some (OpImm ALU_ADD 10 10 2929, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a900 : bv 32 := 0x9df58593.
Lemma F_1a900 : fetch_word Ubsan.M.loaded_segments (0x1a900 : word) = Some W_1a900.
Proof. vm_refl. Qed.
Lemma D_1a900 : decode_any W_1a900 = Some (OpImm ALU_ADD 11 11 2527, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a904 : bv 32 := 0x00000613.
Lemma F_1a904 : fetch_word Ubsan.M.loaded_segments (0x1a904 : word) = Some W_1a904.
Proof. vm_refl. Qed.
Lemma D_1a904 : decode_any W_1a904 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a908 : bv 32 := 0xcecfd06f.
Lemma F_1a908 : fetch_word Ubsan.M.loaded_segments (0x1a908 : word) = Some W_1a908.
Proof. vm_refl. Qed.
Lemma D_1a908 : decode_any W_1a908 = Some (Jal 0 2086124, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a90c : bv 32 := 0x00000513.
Lemma F_1a90c : fetch_word Ubsan.M.loaded_segments (0x1a90c : word) = Some W_1a90c.
Proof. vm_refl. Qed.
Lemma D_1a90c : decode_any W_1a90c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a910 : bv 32 := 0x00008067.
Lemma F_1a910 : fetch_word Ubsan.M.loaded_segments (0x1a910 : word) = Some W_1a910.
Proof. vm_refl. Qed.
Lemma D_1a910 : decode_any W_1a910 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1a914 : bv 32 := 0xc0001073.
Lemma F_1a914 : fetch_word Ubsan.M.loaded_segments (0x1a914 : word) = Some W_1a914.
Proof. vm_refl. Qed.
Lemma D_1a914 : decode_any W_1a914 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.

(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)




(* [comment removed for export] *)
Definition W_7c90c : bv 32 := 0x00000513.
Lemma F_7c90c : fetch_word Plain.M.loaded_segments (0x7c964 : word) = Some W_7c90c.
Proof. vm_refl. Qed.
Lemma D_7c90c : decode_any W_7c90c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c910 : bv 32 := 0x00000593.
Lemma F_7c910 : fetch_word Plain.M.loaded_segments (0x7c968 : word) = Some W_7c910.
Proof. vm_refl. Qed.
Lemma D_7c910 : decode_any W_7c910 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c914 : bv 32 := 0xfff8c413.
Lemma F_7c914 : fetch_word Plain.M.loaded_segments (0x7c96c : word) = Some W_7c914.
Proof. vm_refl. Qed.
Lemma D_7c914 : decode_any W_7c914 = Some (OpImm ALU_XOR 8 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c918 : bv 32 := 0x00271913.
Lemma F_7c918 : fetch_word Plain.M.loaded_segments (0x7c970 : word) = Some W_7c918.
Proof. vm_refl. Qed.
Lemma D_7c918 : decode_any W_7c918 = Some (ShiftImm ALU_SLL 18 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c91c : bv 32 := 0x00448493.
Lemma F_7c91c : fetch_word Plain.M.loaded_segments (0x7c974 : word) = Some W_7c91c.
Proof. vm_refl. Qed.
Lemma D_7c91c : decode_any W_7c91c = Some (OpImm ALU_ADD 9 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c920 : bv 32 := 0x00269993.
Lemma F_7c920 : fetch_word Plain.M.loaded_segments (0x7c978 : word) = Some W_7c920.
Proof. vm_refl. Qed.
Lemma D_7c920 : decode_any W_7c920 = Some (ShiftImm ALU_SLL 19 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c924 : bv 32 := 0x002e1a13.
Lemma F_7c924 : fetch_word Plain.M.loaded_segments (0x7c97c : word) = Some W_7c924.
Proof. vm_refl. Qed.
Lemma D_7c924 : decode_any W_7c924 = Some (ShiftImm ALU_SLL 20 28 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c928 : bv 32 := 0x000e8a93.
Lemma F_7c928 : fetch_word Plain.M.loaded_segments (0x7c980 : word) = Some W_7c928.
Proof. vm_refl. Qed.
Lemma D_7c928 : decode_any W_7c928 = Some (OpImm ALU_ADD 21 29 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c92c : bv 32 := 0x0180006f.
Lemma F_7c92c : fetch_word Plain.M.loaded_segments (0x7c984 : word) = Some W_7c92c.
Proof. vm_refl. Qed.
Lemma D_7c92c : decode_any W_7c92c = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c930 : bv 32 := 0x0015859b.
Lemma F_7c930 : fetch_word Plain.M.loaded_segments (0x7c988 : word) = Some W_7c930.
Proof. vm_refl. Qed.
Lemma D_7c930 : decode_any W_7c930 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c934 : bv 32 := 0x012a8ab3.
Lemma F_7c934 : fetch_word Plain.M.loaded_segments (0x7c98c : word) = Some W_7c934.
Proof. vm_refl. Qed.
Lemma D_7c934 : decode_any W_7c934 = Some (Op ALU_ADD 21 21 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c938 : bv 32 := 0x013484b3.
Lemma F_7c938 : fetch_word Plain.M.loaded_segments (0x7c990 : word) = Some W_7c938.
Proof. vm_refl. Qed.
Lemma D_7c938 : decode_any W_7c938 = Some (Op ALU_ADD 9 9 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c93c : bv 32 := 0x00150513.
Lemma F_7c93c : fetch_word Plain.M.loaded_segments (0x7c994 : word) = Some W_7c93c.
Proof. vm_refl. Qed.
Lemma D_7c93c : decode_any W_7c93c = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c940 : bv 32 := 0xc2c58663.
Lemma F_7c940 : fetch_word Plain.M.loaded_segments (0x7c998 : word) = Some W_7c940.
Proof. vm_refl. Qed.
Lemma D_7c940 : decode_any W_7c940 = Some (Branch BC_EQ 11 12 5164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c944 : bv 32 := 0xfe0e06e3.
Lemma F_7c944 : fetch_word Plain.M.loaded_segments (0x7c99c : word) = Some W_7c944.
Proof. vm_refl. Qed.
Lemma D_7c944 : decode_any W_7c944 = Some (Branch BC_EQ 28 0 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c948 : bv 32 := 0x02a903b3.
Lemma F_7c948 : fetch_word Plain.M.loaded_segments (0x7c9a0 : word) = Some W_7c948.
Proof. vm_refl. Qed.
Lemma D_7c948 : decode_any W_7c948 = Some (Mul M_MUL 7 18 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c94c : bv 32 := 0x007a03b3.
Lemma F_7c94c : fetch_word Plain.M.loaded_segments (0x7c9a4 : word) = Some W_7c94c.
Proof. vm_refl. Qed.
Lemma D_7c94c : decode_any W_7c94c = Some (Op ALU_ADD 7 20 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c950 : bv 32 := 0x007e83b3.
Lemma F_7c950 : fetch_word Plain.M.loaded_segments (0x7c9a8 : word) = Some W_7c950.
Proof. vm_refl. Qed.
Lemma D_7c950 : decode_any W_7c950 = Some (Op ALU_ADD 7 29 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c954 : bv 32 := 0x00048b13.
Lemma F_7c954 : fetch_word Plain.M.loaded_segments (0x7c9ac : word) = Some W_7c954.
Proof. vm_refl. Qed.
Lemma D_7c954 : decode_any W_7c954 = Some (OpImm ALU_ADD 22 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c958 : bv 32 := 0x000a8b93.
Lemma F_7c958 : fetch_word Plain.M.loaded_segments (0x7c9b0 : word) = Some W_7c958.
Proof. vm_refl. Qed.
Lemma D_7c958 : decode_any W_7c958 = Some (OpImm ALU_ADD 23 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c95c : bv 32 := 0xffcb2f83.
Lemma F_7c95c : fetch_word Plain.M.loaded_segments (0x7c9b4 : word) = Some W_7c95c.
Proof. vm_refl. Qed.
Lemma D_7c95c : decode_any W_7c95c = Some (Load SZ4 true 31 22 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c960 : bv 32 := 0x000b2c03.
Lemma F_7c960 : fetch_word Plain.M.loaded_segments (0x7c9b8 : word) = Some W_7c960.
Proof. vm_refl. Qed.
Lemma D_7c960 : decode_any W_7c960 = Some (Load SZ4 true 24 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c964 : bv 32 := 0x00ff9fbb.
Lemma F_7c964 : fetch_word Plain.M.loaded_segments (0x7c9bc : word) = Some W_7c964.
Proof. vm_refl. Qed.
Lemma D_7c964 : decode_any W_7c964 = Some (Op32 ALU_SLL 31 31 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c968 : bv 32 := 0x010c5c3b.
Lemma F_7c968 : fetch_word Plain.M.loaded_segments (0x7c9c0 : word) = Some W_7c968.
Proof. vm_refl. Qed.
Lemma D_7c968 : decode_any W_7c968 = Some (Op32 ALU_SRL 24 24 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c96c : bv 32 := 0x008fffb3.
Lemma F_7c96c : fetch_word Plain.M.loaded_segments (0x7c9c4 : word) = Some W_7c96c.
Proof. vm_refl. Qed.
Lemma D_7c96c : decode_any W_7c96c = Some (Op ALU_AND 31 31 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c970 : bv 32 := 0x011c7c33.
Lemma F_7c970 : fetch_word Plain.M.loaded_segments (0x7c9c8 : word) = Some W_7c970.
Proof. vm_refl. Qed.
Lemma D_7c970 : decode_any W_7c970 = Some (Op ALU_AND 24 24 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c974 : bv 32 := 0x01fc6fb3.
Lemma F_7c974 : fetch_word Plain.M.loaded_segments (0x7c9cc : word) = Some W_7c974.
Proof. vm_refl. Qed.
Lemma D_7c974 : decode_any W_7c974 = Some (Op ALU_OR 31 24 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c978 : bv 32 := 0x01fba023.
Lemma F_7c978 : fetch_word Plain.M.loaded_segments (0x7c9d0 : word) = Some W_7c978.
Proof. vm_refl. Qed.
Lemma D_7c978 : decode_any W_7c978 = Some (Store SZ4 23 31 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c97c : bv 32 := 0x004b8b93.
Lemma F_7c97c : fetch_word Plain.M.loaded_segments (0x7c9d4 : word) = Some W_7c97c.
Proof. vm_refl. Qed.
Lemma D_7c97c : decode_any W_7c97c = Some (OpImm ALU_ADD 23 23 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c980 : bv 32 := 0x004b0b13.
Lemma F_7c980 : fetch_word Plain.M.loaded_segments (0x7c9d8 : word) = Some W_7c980.
Proof. vm_refl. Qed.
Lemma D_7c980 : decode_any W_7c980 = Some (OpImm ALU_ADD 22 22 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c984 : bv 32 := 0xfc7b9ce3.
Lemma F_7c984 : fetch_word Plain.M.loaded_segments (0x7c9dc : word) = Some W_7c984.
Proof. vm_refl. Qed.
Lemma D_7c984 : decode_any W_7c984 = Some (Branch BC_NE 23 7 8152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c988 : bv 32 := 0xfa9ff06f.
Lemma F_7c988 : fetch_word Plain.M.loaded_segments (0x7c9e0 : word) = Some W_7c988.
Proof. vm_refl. Qed.
Lemma D_7c988 : decode_any W_7c988 = Some (Jal 0 2097064, 4%Z).
Proof. vm_refl. Qed.

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
Definition W_6c7e4 : bv 32 := 0x06a05a63.
Lemma F_6c7e4 : fetch_word Plain.M.loaded_segments (0x6c83c : word) = Some W_6c7e4.
Proof. vm_refl. Qed.
Lemma D_6c7e4 : decode_any W_6c7e4 = Some (Branch BC_GE 0 10 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c7e8 : bv 32 := 0x08b05c63.
Lemma F_6c7e8 : fetch_word Plain.M.loaded_segments (0x6c840 : word) = Some W_6c7e8.
Proof. vm_refl. Qed.
Lemma D_6c7e8 : decode_any W_6c7e8 = Some (Branch BC_GE 0 11 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c7ec : bv 32 := 0x02a606b3.
Lemma F_6c7ec : fetch_word Plain.M.loaded_segments (0x6c844 : word) = Some W_6c7ec.
Proof. vm_refl. Qed.
Lemma D_6c7ec : decode_any W_6c7ec = Some (Mul M_MUL 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c7f0 : bv 32 := 0x20000737.
Lemma F_6c7f0 : fetch_word Plain.M.loaded_segments (0x6c848 : word) = Some W_6c7f0.
Proof. vm_refl. Qed.
Lemma D_6c7f0 : decode_any W_6c7f0 = Some (Lui 14 131072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c7f4 : bv 32 := 0xfe17071b.
Lemma F_6c7f4 : fetch_word Plain.M.loaded_segments (0x6c84c : word) = Some W_6c7f4.
Proof. vm_refl. Qed.
Lemma D_6c7f4 : decode_any W_6c7f4 = Some (OpImm32 14 14 4065, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c7f8 : bv 32 := 0x0ae6e863.
Lemma F_6c7f8 : fetch_word Plain.M.loaded_segments (0x6c850 : word) = Some W_6c7f8.
Proof. vm_refl. Qed.
Lemma D_6c7f8 : decode_any W_6c7f8 = Some (Branch BC_LTU 13 14 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c8a8 : bv 32 := 0x01f68693.
Lemma F_6c8a8 : fetch_word Plain.M.loaded_segments (0x6c900 : word) = Some W_6c8a8.
Proof. vm_refl. Qed.
Lemma D_6c8a8 : decode_any W_6c8a8 = Some (OpImm ALU_ADD 13 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c8ac : bv 32 := 0x0056d413.
Lemma F_6c8ac : fetch_word Plain.M.loaded_segments (0x6c904 : word) = Some W_6c8ac.
Proof. vm_refl. Qed.
Lemma D_6c8ac : decode_any W_6c8ac = Some (ShiftImm ALU_SRL 8 13 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c8b0 : bv 32 := 0x02b406b3.
Lemma F_6c8b0 : fetch_word Plain.M.loaded_segments (0x6c908 : word) = Some W_6c8b0.
Proof. vm_refl. Qed.
Lemma D_6c8b0 : decode_any W_6c8b0 = Some (Mul M_MUL 13 8 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c8b4 : bv 32 := 0x00269693.
Lemma F_6c8b4 : fetch_word Plain.M.loaded_segments (0x6c90c : word) = Some W_6c8b4.
Proof. vm_refl. Qed.
Lemma D_6c8b4 : decode_any W_6c8b4 = Some (ShiftImm ALU_SLL 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c8b8 : bv 32 := 0x01f6d713.
Lemma F_6c8b8 : fetch_word Plain.M.loaded_segments (0x6c910 : word) = Some W_6c8b8.
Proof. vm_refl. Qed.
Lemma D_6c8b8 : decode_any W_6c8b8 = Some (ShiftImm ALU_SRL 14 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c8bc : bv 32 := 0x0a070463.
Lemma F_6c8bc : fetch_word Plain.M.loaded_segments (0x6c914 : word) = Some W_6c8bc.
Proof. vm_refl. Qed.
Lemma D_6c8bc : decode_any W_6c8bc = Some (Branch BC_EQ 14 0 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c964 : bv 32 := 0x04000737.
Lemma F_6c964 : fetch_word Plain.M.loaded_segments (0x6c9bc : word) = Some W_6c964.
Proof. vm_refl. Qed.
Lemma D_6c964 : decode_any W_6c964 = Some (Lui 14 16384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c968 : bv 32 := 0x0017071b.
Lemma F_6c968 : fetch_word Plain.M.loaded_segments (0x6c9c0 : word) = Some W_6c968.
Proof. vm_refl. Qed.
Lemma D_6c968 : decode_any W_6c968 = Some (OpImm32 14 14 1, 4%Z).
Proof. vm_refl. Qed.


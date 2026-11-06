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
Definition W_6c858 : bv 32 := 0x000a6517.
Lemma F_6c858 : fetch_word Plain.M.loaded_segments (0x6c8b0 : word) = Some W_6c858.
Proof. vm_refl. Qed.
Lemma D_6c858 : decode_any W_6c858 = Some (Auipc 10 166, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c85c : bv 32 := 0xd1853503.
Lemma F_6c85c : fetch_word Plain.M.loaded_segments (0x6c8b4 : word) = Some W_6c85c.
Proof. vm_refl. Qed.
Lemma D_6c85c : decode_any W_6c85c = Some (Load SZ8 true 10 10 3352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c860 : bv 32 := 0x00052503.
Lemma F_6c860 : fetch_word Plain.M.loaded_segments (0x6c8b8 : word) = Some W_6c860.
Proof. vm_refl. Qed.
Lemma D_6c860 : decode_any W_6c860 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c864 : bv 32 := 0x00500593.
Lemma F_6c864 : fetch_word Plain.M.loaded_segments (0x6c8bc : word) = Some W_6c864.
Proof. vm_refl. Qed.
Lemma D_6c864 : decode_any W_6c864 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c868 : bv 32 := 0x18a5c863.
Lemma F_6c868 : fetch_word Plain.M.loaded_segments (0x6c8c0 : word) = Some W_6c868.
Proof. vm_refl. Qed.
Lemma D_6c868 : decode_any W_6c868 = Some (Branch BC_LT 11 10 400, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c86c : bv 32 := 0xfffa4517.
Lemma F_6c86c : fetch_word Plain.M.loaded_segments (0x6c8c4 : word) = Some W_6c86c.
Proof. vm_refl. Qed.
Lemma D_6c86c : decode_any W_6c86c = Some (Auipc 10 1048484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c870 : bv 32 := 0xfffa9597.
Lemma F_6c870 : fetch_word Plain.M.loaded_segments (0x6c8c8 : word) = Some W_6c870.
Proof. vm_refl. Qed.
Lemma D_6c870 : decode_any W_6c870 = Some (Auipc 11 1048489, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c874 : bv 32 := 0xae950513.
Lemma F_6c874 : fetch_word Plain.M.loaded_segments (0x6c8cc : word) = Some W_6c874.
Proof. vm_refl. Qed.
Lemma D_6c874 : decode_any W_6c874 = Some (OpImm ALU_ADD 10 10 2793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c878 : bv 32 := 0x16458593.
Lemma F_6c878 : fetch_word Plain.M.loaded_segments (0x6c8d0 : word) = Some W_6c878.
Proof. vm_refl. Qed.
Lemma D_6c878 : decode_any W_6c878 = Some (OpImm ALU_ADD 11 11 356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c87c : bv 32 := 0x0c40006f.
Lemma F_6c87c : fetch_word Plain.M.loaded_segments (0x6c8d4 : word) = Some W_6c87c.
Proof. vm_refl. Qed.
Lemma D_6c87c : decode_any W_6c87c = Some (Jal 0 196, 4%Z).
Proof. vm_refl. Qed.


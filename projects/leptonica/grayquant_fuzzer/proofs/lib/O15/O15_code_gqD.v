(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.H Require GcFlushS15.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.grayquant_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_16b4c : bv 32 := 0xfe010113.
Lemma F_16b4c : fetch_word Plain.M.loaded_segments (0x16ba4 : word) = Some W_16b4c.
Proof. vm_refl. Qed.
Lemma D_16b4c : decode_any W_16b4c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b50 : bv 32 := 0x00113c23.
Lemma F_16b50 : fetch_word Plain.M.loaded_segments (0x16ba8 : word) = Some W_16b50.
Proof. vm_refl. Qed.
Lemma D_16b50 : decode_any W_16b50 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b54 : bv 32 := 0x00813823.
Lemma F_16b54 : fetch_word Plain.M.loaded_segments (0x16bac : word) = Some W_16b54.
Proof. vm_refl. Qed.
Lemma D_16b54 : decode_any W_16b54 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b58 : bv 32 := 0x00913423.
Lemma F_16b58 : fetch_word Plain.M.loaded_segments (0x16bb0 : word) = Some W_16b58.
Proof. vm_refl. Qed.
Lemma D_16b58 : decode_any W_16b58 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b5c : bv 32 := 0x06050863.
Lemma F_16b5c : fetch_word Plain.M.loaded_segments (0x16bb4 : word) = Some W_16b5c.
Proof. vm_refl. Qed.
Lemma D_16b5c : decode_any W_16b5c = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b60 : bv 32 := 0x00053403.
Lemma F_16b60 : fetch_word Plain.M.loaded_segments (0x16bb8 : word) = Some W_16b60.
Proof. vm_refl. Qed.
Lemma D_16b60 : decode_any W_16b60 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b64 : bv 32 := 0x0a040063.
Lemma F_16b64 : fetch_word Plain.M.loaded_segments (0x16bbc : word) = Some W_16b64.
Proof. vm_refl. Qed.
Lemma D_16b64 : decode_any W_16b64 = Some (Branch BC_EQ 8 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b68 : bv 32 := 0x01440593.
Lemma F_16b68 : fetch_word Plain.M.loaded_segments (0x16bc0 : word) = Some W_16b68.
Proof. vm_refl. Qed.
Lemma D_16b68 : decode_any W_16b68 = Some (OpImm ALU_ADD 11 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b6c : bv 32 := 0xfff00613.
Lemma F_16b6c : fetch_word Plain.M.loaded_segments (0x16bc4 : word) = Some W_16b6c.
Proof. vm_refl. Qed.
Lemma D_16b6c : decode_any W_16b6c = Some (OpImm ALU_ADD 12 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b70 : bv 32 := 0x06c5a5af.
Lemma F_16b70 : fetch_word Plain.M.loaded_segments (0x16bc8 : word) = Some W_16b70.
Proof. vm_refl. Qed.
Lemma D_16b70 : decode_any W_16b70 = Some (Amo AMO_ADD AW true true 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b74 : bv 32 := 0x00100613.
Lemma F_16b74 : fetch_word Plain.M.loaded_segments (0x16bcc : word) = Some W_16b74.
Proof. vm_refl. Qed.
Lemma D_16b74 : decode_any W_16b74 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b78 : bv 32 := 0x04c59663.
Lemma F_16b78 : fetch_word Plain.M.loaded_segments (0x16bd0 : word) = Some W_16b78.
Proof. vm_refl. Qed.
Lemma D_16b78 : decode_any W_16b78 = Some (Branch BC_NE 11 12 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16bc4 : bv 32 := 0x00053023.
Lemma F_16bc4 : fetch_word Plain.M.loaded_segments (0x16c1c : word) = Some W_16bc4.
Proof. vm_refl. Qed.
Lemma D_16bc4 : decode_any W_16bc4 = Some (Store SZ8 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16bc8 : bv 32 := 0x03c0006f.
Lemma F_16bc8 : fetch_word Plain.M.loaded_segments (0x16c20 : word) = Some W_16bc8.
Proof. vm_refl. Qed.
Lemma D_16bc8 : decode_any W_16bc8 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c04 : bv 32 := 0x01813083.
Lemma F_16c04 : fetch_word Plain.M.loaded_segments (0x16c5c : word) = Some W_16c04.
Proof. vm_refl. Qed.
Lemma D_16c04 : decode_any W_16c04 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c08 : bv 32 := 0x01013403.
Lemma F_16c08 : fetch_word Plain.M.loaded_segments (0x16c60 : word) = Some W_16c08.
Proof. vm_refl. Qed.
Lemma D_16c08 : decode_any W_16c08 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c0c : bv 32 := 0x00813483.
Lemma F_16c0c : fetch_word Plain.M.loaded_segments (0x16c64 : word) = Some W_16c0c.
Proof. vm_refl. Qed.
Lemma D_16c0c : decode_any W_16c0c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c10 : bv 32 := 0x02010113.
Lemma F_16c10 : fetch_word Plain.M.loaded_segments (0x16c68 : word) = Some W_16c10.
Proof. vm_refl. Qed.
Lemma D_16c10 : decode_any W_16c10 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c14 : bv 32 := 0x00008067.
Lemma F_16c14 : fetch_word Plain.M.loaded_segments (0x16c6c : word) = Some W_16c14.
Proof. vm_refl. Qed.
Lemma D_16c14 : decode_any W_16c14 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17e54 : bv 32 := 0x00008067.
Lemma F_17e54 : fetch_word Plain.M.loaded_segments (0x17eac : word) = Some W_17e54.
Proof. vm_refl. Qed.
Lemma D_17e54 : decode_any W_17e54 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a644 : bv 32 := 0x00008067.
Lemma F_1a644 : fetch_word Plain.M.loaded_segments (0x1a69c : word) = Some W_1a644.
Proof. vm_refl. Qed.
Lemma D_1a644 : decode_any W_1a644 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a97c : bv 32 := 0x00008067.
Lemma F_1a97c : fetch_word Plain.M.loaded_segments (0x1a9d4 : word) = Some W_1a97c.
Proof. vm_refl. Qed.
Lemma D_1a97c : decode_any W_1a97c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.


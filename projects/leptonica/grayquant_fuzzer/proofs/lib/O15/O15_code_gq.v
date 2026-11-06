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
Definition W_16b7c : bv 32 := 0x00050493.
Lemma F_16b7c : fetch_word Plain.M.loaded_segments (0x16bd4 : word) = Some W_16b7c.
Proof. vm_refl. Qed.
Lemma D_16b7c : decode_any W_16b7c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b80 : bv 32 := 0x03843503.
Lemma F_16b80 : fetch_word Plain.M.loaded_segments (0x16bd8 : word) = Some W_16b80.
Proof. vm_refl. Qed.
Lemma D_16b80 : decode_any W_16b80 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b84 : bv 32 := 0x00050863.
Lemma F_16b84 : fetch_word Plain.M.loaded_segments (0x16bdc : word) = Some W_16b84.
Proof. vm_refl. Qed.
Lemma D_16b84 : decode_any W_16b84 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b88 : bv 32 := 0x00017597.
Lemma F_16b88 : fetch_word Plain.M.loaded_segments (0x16be0 : word) = Some W_16b88.
Proof. vm_refl. Qed.
Lemma D_16b88 : decode_any W_16b88 = Some (Auipc 11 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b8c : bv 32 := 0xc285b583.
Lemma F_16b8c : fetch_word Plain.M.loaded_segments (0x16be4 : word) = Some W_16b8c.
Proof. vm_refl. Qed.
Lemma D_16b8c : decode_any W_16b8c = Some (Load SZ8 true 11 11 3112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b90 : bv 32 := 0x000580e7.
Lemma F_16b90 : fetch_word Plain.M.loaded_segments (0x16be8 : word) = Some W_16b90.
Proof. vm_refl. Qed.
Lemma D_16b90 : decode_any W_16b90 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b94 : bv 32 := 0x02843503.
Lemma F_16b94 : fetch_word Plain.M.loaded_segments (0x16bec : word) = Some W_16b94.
Proof. vm_refl. Qed.
Lemma D_16b94 : decode_any W_16b94 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16b98 : bv 32 := 0x00050463.
Lemma F_16b98 : fetch_word Plain.M.loaded_segments (0x16bf0 : word) = Some W_16b98.
Proof. vm_refl. Qed.
Lemma D_16b98 : decode_any W_16b98 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ba0 : bv 32 := 0x03043503.
Lemma F_16ba0 : fetch_word Plain.M.loaded_segments (0x16bf8 : word) = Some W_16ba0.
Proof. vm_refl. Qed.
Lemma D_16ba0 : decode_any W_16ba0 = Some (Load SZ8 true 10 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ba4 : bv 32 := 0x00a13023.
Lemma F_16ba4 : fetch_word Plain.M.loaded_segments (0x16bfc : word) = Some W_16ba4.
Proof. vm_refl. Qed.
Lemma D_16ba4 : decode_any W_16ba4 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ba8 : bv 32 := 0x00050863.
Lemma F_16ba8 : fetch_word Plain.M.loaded_segments (0x16c00 : word) = Some W_16ba8.
Proof. vm_refl. Qed.
Lemma D_16ba8 : decode_any W_16ba8 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16bac : bv 32 := 0x00010513.
Lemma F_16bac : fetch_word Plain.M.loaded_segments (0x16c04 : word) = Some W_16bac.
Proof. vm_refl. Qed.
Lemma D_16bac : decode_any W_16bac = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16bb0 : bv 32 := 0x6dc010ef.
Lemma F_16bb0 : fetch_word Plain.M.loaded_segments (0x16c08 : word) = Some W_16bb0.
Proof. vm_refl. Qed.
Lemma D_16bb0 : decode_any W_16bb0 = Some (Jal 1 5852, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16bb4 : bv 32 := 0x02043823.
Lemma F_16bb4 : fetch_word Plain.M.loaded_segments (0x16c0c : word) = Some W_16bb4.
Proof. vm_refl. Qed.
Lemma D_16bb4 : decode_any W_16bb4 = Some (Store SZ8 8 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16bb8 : bv 32 := 0x00040513.
Lemma F_16bb8 : fetch_word Plain.M.loaded_segments (0x16c10 : word) = Some W_16bb8.
Proof. vm_refl. Qed.
Lemma D_16bb8 : decode_any W_16bb8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16bbc : bv 32 := 0x3c40a0ef.
Lemma F_16bbc : fetch_word Plain.M.loaded_segments (0x16c14 : word) = Some W_16bbc.
Proof. vm_refl. Qed.
Lemma D_16bbc : decode_any W_16bbc = Some (Jal 1 41924, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16bc0 : bv 32 := 0x00048513.
Lemma F_16bc0 : fetch_word Plain.M.loaded_segments (0x16c18 : word) = Some W_16bc0.
Proof. vm_refl. Qed.
Lemma D_16bc0 : decode_any W_16bc0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
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


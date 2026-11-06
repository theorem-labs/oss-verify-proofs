(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_1b060 : bv 32 := 0xfd010113.
Lemma F_1b060 : fetch_word Plain.M.loaded_segments (0x1b0b8 : word) = Some W_1b060.
Proof. vm_refl. Qed.
Lemma D_1b060 : decode_any W_1b060 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b064 : bv 32 := 0x02113423.
Lemma F_1b064 : fetch_word Plain.M.loaded_segments (0x1b0bc : word) = Some W_1b064.
Proof. vm_refl. Qed.
Lemma D_1b064 : decode_any W_1b064 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b068 : bv 32 := 0x02813023.
Lemma F_1b068 : fetch_word Plain.M.loaded_segments (0x1b0c0 : word) = Some W_1b068.
Proof. vm_refl. Qed.
Lemma D_1b068 : decode_any W_1b068 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b06c : bv 32 := 0x00913c23.
Lemma F_1b06c : fetch_word Plain.M.loaded_segments (0x1b0c4 : word) = Some W_1b06c.
Proof. vm_refl. Qed.
Lemma D_1b06c : decode_any W_1b06c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b070 : bv 32 := 0x01213823.
Lemma F_1b070 : fetch_word Plain.M.loaded_segments (0x1b0c8 : word) = Some W_1b070.
Proof. vm_refl. Qed.
Lemma D_1b070 : decode_any W_1b070 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b074 : bv 32 := 0x06050063.
Lemma F_1b074 : fetch_word Plain.M.loaded_segments (0x1b0cc : word) = Some W_1b074.
Proof. vm_refl. Qed.
Lemma D_1b074 : decode_any W_1b074 = Some (Branch BC_EQ 10 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b078 : bv 32 := 0x00050493.
Lemma F_1b078 : fetch_word Plain.M.loaded_segments (0x1b0d0 : word) = Some W_1b078.
Proof. vm_refl. Qed.
Lemma D_1b078 : decode_any W_1b078 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b07c : bv 32 := 0x00058913.
Lemma F_1b07c : fetch_word Plain.M.loaded_segments (0x1b0d4 : word) = Some W_1b07c.
Proof. vm_refl. Qed.
Lemma D_1b07c : decode_any W_1b07c = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b080 : bv 32 := 0x00c10593.
Lemma F_1b080 : fetch_word Plain.M.loaded_segments (0x1b0d8 : word) = Some W_1b080.
Proof. vm_refl. Qed.
Lemma D_1b080 : decode_any W_1b080 = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b084 : bv 32 := 0x00810613.
Lemma F_1b084 : fetch_word Plain.M.loaded_segments (0x1b0dc : word) = Some W_1b084.
Proof. vm_refl. Qed.
Lemma D_1b084 : decode_any W_1b084 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b088 : bv 32 := 0x00410693.
Lemma F_1b088 : fetch_word Plain.M.loaded_segments (0x1b0e0 : word) = Some W_1b088.
Proof. vm_refl. Qed.
Lemma D_1b088 : decode_any W_1b088 = Some (OpImm ALU_ADD 13 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b08c : bv 32 := 0xe00fe0ef.
Lemma F_1b08c : fetch_word Plain.M.loaded_segments (0x1b0e4 : word) = Some W_1b08c.
Proof. vm_refl. Qed.
Lemma D_1b08c : decode_any W_1b08c = Some (Jal 1 2090496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b090 : bv 32 := 0x00412503.
Lemma F_1b090 : fetch_word Plain.M.loaded_segments (0x1b0e8 : word) = Some W_1b090.
Proof. vm_refl. Qed.
Lemma D_1b090 : decode_any W_1b090 = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b094 : bv 32 := 0x02000593.
Lemma F_1b094 : fetch_word Plain.M.loaded_segments (0x1b0ec : word) = Some W_1b094.
Proof. vm_refl. Qed.
Lemma D_1b094 : decode_any W_1b094 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b098 : bv 32 := 0x12b50463.
Lemma F_1b098 : fetch_word Plain.M.loaded_segments (0x1b0f0 : word) = Some W_1b098.
Proof. vm_refl. Qed.
Lemma D_1b098 : decode_any W_1b098 = Some (Branch BC_EQ 10 11 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b1c0 : bv 32 := 0x00000513.
Lemma F_1b1c0 : fetch_word Plain.M.loaded_segments (0x1b218 : word) = Some W_1b1c0.
Proof. vm_refl. Qed.
Lemma D_1b1c0 : decode_any W_1b1c0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b1c4 : bv 32 := 0x02813083.
Lemma F_1b1c4 : fetch_word Plain.M.loaded_segments (0x1b21c : word) = Some W_1b1c4.
Proof. vm_refl. Qed.
Lemma D_1b1c4 : decode_any W_1b1c4 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b1c8 : bv 32 := 0x02013403.
Lemma F_1b1c8 : fetch_word Plain.M.loaded_segments (0x1b220 : word) = Some W_1b1c8.
Proof. vm_refl. Qed.
Lemma D_1b1c8 : decode_any W_1b1c8 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b1cc : bv 32 := 0x01813483.
Lemma F_1b1cc : fetch_word Plain.M.loaded_segments (0x1b224 : word) = Some W_1b1cc.
Proof. vm_refl. Qed.
Lemma D_1b1cc : decode_any W_1b1cc = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b1d0 : bv 32 := 0x01013903.
Lemma F_1b1d0 : fetch_word Plain.M.loaded_segments (0x1b228 : word) = Some W_1b1d0.
Proof. vm_refl. Qed.
Lemma D_1b1d0 : decode_any W_1b1d0 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b1d4 : bv 32 := 0x03010113.
Lemma F_1b1d4 : fetch_word Plain.M.loaded_segments (0x1b22c : word) = Some W_1b1d4.
Proof. vm_refl. Qed.
Lemma D_1b1d4 : decode_any W_1b1d4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b1d8 : bv 32 := 0x00008067.
Lemma F_1b1d8 : fetch_word Plain.M.loaded_segments (0x1b230 : word) = Some W_1b1d8.
Proof. vm_refl. Qed.
Lemma D_1b1d8 : decode_any W_1b1d8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

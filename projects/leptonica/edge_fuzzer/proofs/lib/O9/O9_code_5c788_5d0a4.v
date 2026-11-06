(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.H Require GcFlushS9.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_5cd7c : bv 32 := 0xff010113.
Lemma F_5cd7c : fetch_word Plain.M.loaded_segments (0x5cdd4 : word) = Some W_5cd7c.
Proof. vm_refl. Qed.
Lemma D_5cd7c : decode_any W_5cd7c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd80 : bv 32 := 0x00113423.
Lemma F_5cd80 : fetch_word Plain.M.loaded_segments (0x5cdd8 : word) = Some W_5cd80.
Proof. vm_refl. Qed.
Lemma D_5cd80 : decode_any W_5cd80 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd84 : bv 32 := 0x00813023.
Lemma F_5cd84 : fetch_word Plain.M.loaded_segments (0x5cddc : word) = Some W_5cd84.
Proof. vm_refl. Qed.
Lemma D_5cd84 : decode_any W_5cd84 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd88 : bv 32 := 0x00060413.
Lemma F_5cd88 : fetch_word Plain.M.loaded_segments (0x5cde0 : word) = Some W_5cd88.
Proof. vm_refl. Qed.
Lemma D_5cd88 : decode_any W_5cd88 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd8c : bv 32 := 0x00050613.
Lemma F_5cd8c : fetch_word Plain.M.loaded_segments (0x5cde4 : word) = Some W_5cd8c.
Proof. vm_refl. Qed.
Lemma D_5cd8c : decode_any W_5cd8c = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd90 : bv 32 := 0xfffbf517.
Lemma F_5cd90 : fetch_word Plain.M.loaded_segments (0x5cde8 : word) = Some W_5cd90.
Proof. vm_refl. Qed.
Lemma D_5cd90 : decode_any W_5cd90 = Some (Auipc 10 1048511, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd94 : bv 32 := 0xdda50513.
Lemma F_5cd94 : fetch_word Plain.M.loaded_segments (0x5cdec : word) = Some W_5cd94.
Proof. vm_refl. Qed.
Lemma D_5cd94 : decode_any W_5cd94 = Some (OpImm ALU_ADD 10 10 3546, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd98 : bv 32 := 0x018000ef.
Lemma F_5cd98 : fetch_word Plain.M.loaded_segments (0x5cdf0 : word) = Some W_5cd98.
Proof. vm_refl. Qed.
Lemma D_5cd98 : decode_any W_5cd98 = Some (Jal 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd9c : bv 32 := 0x00040513.
Lemma F_5cd9c : fetch_word Plain.M.loaded_segments (0x5cdf4 : word) = Some W_5cd9c.
Proof. vm_refl. Qed.
Lemma D_5cd9c : decode_any W_5cd9c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cda0 : bv 32 := 0x00813083.
Lemma F_5cda0 : fetch_word Plain.M.loaded_segments (0x5cdf8 : word) = Some W_5cda0.
Proof. vm_refl. Qed.
Lemma D_5cda0 : decode_any W_5cda0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cda4 : bv 32 := 0x00013403.
Lemma F_5cda4 : fetch_word Plain.M.loaded_segments (0x5cdfc : word) = Some W_5cda4.
Proof. vm_refl. Qed.
Lemma D_5cda4 : decode_any W_5cda4 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cda8 : bv 32 := 0x01010113.
Lemma F_5cda8 : fetch_word Plain.M.loaded_segments (0x5ce00 : word) = Some W_5cda8.
Proof. vm_refl. Qed.
Lemma D_5cda8 : decode_any W_5cda8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cdac : bv 32 := 0x00008067.
Lemma F_5cdac : fetch_word Plain.M.loaded_segments (0x5ce04 : word) = Some W_5cdac.
Proof. vm_refl. Qed.
Lemma D_5cdac : decode_any W_5cdac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce4c : bv 32 := 0xff010113.
Lemma F_5ce4c : fetch_word Plain.M.loaded_segments (0x5cea4 : word) = Some W_5ce4c.
Proof. vm_refl. Qed.
Lemma D_5ce4c : decode_any W_5ce4c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce50 : bv 32 := 0x00113423.
Lemma F_5ce50 : fetch_word Plain.M.loaded_segments (0x5cea8 : word) = Some W_5ce50.
Proof. vm_refl. Qed.
Lemma D_5ce50 : decode_any W_5ce50 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce54 : bv 32 := 0x00813023.
Lemma F_5ce54 : fetch_word Plain.M.loaded_segments (0x5ceac : word) = Some W_5ce54.
Proof. vm_refl. Qed.
Lemma D_5ce54 : decode_any W_5ce54 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce58 : bv 32 := 0x00060413.
Lemma F_5ce58 : fetch_word Plain.M.loaded_segments (0x5ceb0 : word) = Some W_5ce58.
Proof. vm_refl. Qed.
Lemma D_5ce58 : decode_any W_5ce58 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce5c : bv 32 := 0x00050613.
Lemma F_5ce5c : fetch_word Plain.M.loaded_segments (0x5ceb4 : word) = Some W_5ce5c.
Proof. vm_refl. Qed.
Lemma D_5ce5c : decode_any W_5ce5c = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce60 : bv 32 := 0xfffbf517.
Lemma F_5ce60 : fetch_word Plain.M.loaded_segments (0x5ceb8 : word) = Some W_5ce60.
Proof. vm_refl. Qed.
Lemma D_5ce60 : decode_any W_5ce60 = Some (Auipc 10 1048511, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce64 : bv 32 := 0xd0a50513.
Lemma F_5ce64 : fetch_word Plain.M.loaded_segments (0x5cebc : word) = Some W_5ce64.
Proof. vm_refl. Qed.
Lemma D_5ce64 : decode_any W_5ce64 = Some (OpImm ALU_ADD 10 10 3338, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce68 : bv 32 := 0xf49ff0ef.
Lemma F_5ce68 : fetch_word Plain.M.loaded_segments (0x5cec0 : word) = Some W_5ce68.
Proof. vm_refl. Qed.
Lemma D_5ce68 : decode_any W_5ce68 = Some (Jal 1 2096968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce6c : bv 32 := 0x00040513.
Lemma F_5ce6c : fetch_word Plain.M.loaded_segments (0x5cec4 : word) = Some W_5ce6c.
Proof. vm_refl. Qed.
Lemma D_5ce6c : decode_any W_5ce6c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce70 : bv 32 := 0x00813083.
Lemma F_5ce70 : fetch_word Plain.M.loaded_segments (0x5cec8 : word) = Some W_5ce70.
Proof. vm_refl. Qed.
Lemma D_5ce70 : decode_any W_5ce70 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce74 : bv 32 := 0x00013403.
Lemma F_5ce74 : fetch_word Plain.M.loaded_segments (0x5cecc : word) = Some W_5ce74.
Proof. vm_refl. Qed.
Lemma D_5ce74 : decode_any W_5ce74 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce78 : bv 32 := 0x01010113.
Lemma F_5ce78 : fetch_word Plain.M.loaded_segments (0x5ced0 : word) = Some W_5ce78.
Proof. vm_refl. Qed.
Lemma D_5ce78 : decode_any W_5ce78 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce7c : bv 32 := 0x00008067.
Lemma F_5ce7c : fetch_word Plain.M.loaded_segments (0x5ced4 : word) = Some W_5ce7c.
Proof. vm_refl. Qed.
Lemma D_5ce7c : decode_any W_5ce7c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.


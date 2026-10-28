(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.H Require GcFlushU10.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_17c78 : bv 32 := 0xfd010113.
Lemma F_17c78 : fetch_word Ubsan.M.loaded_segments (0x17d74 : word) = Some W_17c78.
Proof. vm_refl. Qed.
Lemma D_17c78 : decode_any W_17c78 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c7c : bv 32 := 0x02113423.
Lemma F_17c7c : fetch_word Ubsan.M.loaded_segments (0x17d78 : word) = Some W_17c7c.
Proof. vm_refl. Qed.
Lemma D_17c7c : decode_any W_17c7c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c80 : bv 32 := 0x02813023.
Lemma F_17c80 : fetch_word Ubsan.M.loaded_segments (0x17d7c : word) = Some W_17c80.
Proof. vm_refl. Qed.
Lemma D_17c80 : decode_any W_17c80 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c84 : bv 32 := 0x00913c23.
Lemma F_17c84 : fetch_word Ubsan.M.loaded_segments (0x17d80 : word) = Some W_17c84.
Proof. vm_refl. Qed.
Lemma D_17c84 : decode_any W_17c84 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c88 : bv 32 := 0x01213823.
Lemma F_17c88 : fetch_word Ubsan.M.loaded_segments (0x17d84 : word) = Some W_17c88.
Proof. vm_refl. Qed.
Lemma D_17c88 : decode_any W_17c88 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c8c : bv 32 := 0x06050063.
Lemma F_17c8c : fetch_word Ubsan.M.loaded_segments (0x17d88 : word) = Some W_17c8c.
Proof. vm_refl. Qed.
Lemma D_17c8c : decode_any W_17c8c = Some (Branch BC_EQ 10 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c90 : bv 32 := 0x00058413.
Lemma F_17c90 : fetch_word Ubsan.M.loaded_segments (0x17d8c : word) = Some W_17c90.
Proof. vm_refl. Qed.
Lemma D_17c90 : decode_any W_17c90 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c94 : bv 32 := 0x00050913.
Lemma F_17c94 : fetch_word Ubsan.M.loaded_segments (0x17d90 : word) = Some W_17c94.
Proof. vm_refl. Qed.
Lemma D_17c94 : decode_any W_17c94 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c98 : bv 32 := 0x00c10593.
Lemma F_17c98 : fetch_word Ubsan.M.loaded_segments (0x17d94 : word) = Some W_17c98.
Proof. vm_refl. Qed.
Lemma D_17c98 : decode_any W_17c98 = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c9c : bv 32 := 0x00810613.
Lemma F_17c9c : fetch_word Ubsan.M.loaded_segments (0x17d98 : word) = Some W_17c9c.
Proof. vm_refl. Qed.
Lemma D_17c9c : decode_any W_17c9c = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ca0 : bv 32 := 0x00410693.
Lemma F_17ca0 : fetch_word Ubsan.M.loaded_segments (0x17d9c : word) = Some W_17ca0.
Proof. vm_refl. Qed.
Lemma D_17ca0 : decode_any W_17ca0 = Some (OpImm ALU_ADD 13 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ca4 : bv 32 := 0xec8fe0ef.
Lemma F_17ca4 : fetch_word Ubsan.M.loaded_segments (0x17da0 : word) = Some W_17ca4.
Proof. vm_refl. Qed.
Lemma D_17ca4 : decode_any W_17ca4 = Some (Jal 1 2090696, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ca8 : bv 32 := 0x00412503.
Lemma F_17ca8 : fetch_word Ubsan.M.loaded_segments (0x17da4 : word) = Some W_17ca8.
Proof. vm_refl. Qed.
Lemma D_17ca8 : decode_any W_17ca8 = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17cac : bv 32 := 0x02000593.
Lemma F_17cac : fetch_word Ubsan.M.loaded_segments (0x17da8 : word) = Some W_17cac.
Proof. vm_refl. Qed.
Lemma D_17cac : decode_any W_17cac = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17cb0 : bv 32 := 0x18b50c63.
Lemma F_17cb0 : fetch_word Ubsan.M.loaded_segments (0x17dac : word) = Some W_17cb0.
Proof. vm_refl. Qed.
Lemma D_17cb0 : decode_any W_17cb0 = Some (Branch BC_EQ 10 11 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17e48 : bv 32 := 0x00000513.
Lemma F_17e48 : fetch_word Ubsan.M.loaded_segments (0x17f44 : word) = Some W_17e48.
Proof. vm_refl. Qed.
Lemma D_17e48 : decode_any W_17e48 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17e4c : bv 32 := 0x02813083.
Lemma F_17e4c : fetch_word Ubsan.M.loaded_segments (0x17f48 : word) = Some W_17e4c.
Proof. vm_refl. Qed.
Lemma D_17e4c : decode_any W_17e4c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17e50 : bv 32 := 0x02013403.
Lemma F_17e50 : fetch_word Ubsan.M.loaded_segments (0x17f4c : word) = Some W_17e50.
Proof. vm_refl. Qed.
Lemma D_17e50 : decode_any W_17e50 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17e54 : bv 32 := 0x01813483.
Lemma F_17e54 : fetch_word Ubsan.M.loaded_segments (0x17f50 : word) = Some W_17e54.
Proof. vm_refl. Qed.
Lemma D_17e54 : decode_any W_17e54 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17e58 : bv 32 := 0x01013903.
Lemma F_17e58 : fetch_word Ubsan.M.loaded_segments (0x17f54 : word) = Some W_17e58.
Proof. vm_refl. Qed.
Lemma D_17e58 : decode_any W_17e58 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17e5c : bv 32 := 0x03010113.
Lemma F_17e5c : fetch_word Ubsan.M.loaded_segments (0x17f58 : word) = Some W_17e5c.
Proof. vm_refl. Qed.
Lemma D_17e5c : decode_any W_17e5c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17e60 : bv 32 := 0x00008067.
Lemma F_17e60 : fetch_word Ubsan.M.loaded_segments (0x17f5c : word) = Some W_17e60.
Proof. vm_refl. Qed.
Lemma D_17e60 : decode_any W_17e60 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

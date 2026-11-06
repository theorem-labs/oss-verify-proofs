(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.H Require GcFlushU21.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.paintcmap_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_17180 : bv 32 := 0x00058513.
Lemma F_17180 : fetch_word Ubsan.M.loaded_segments (0x17284 : word) = Some W_17180.
Proof. vm_refl. Qed.
Lemma D_17180 : decode_any W_17180 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17184 : bv 32 := 0x07813083.
Lemma F_17184 : fetch_word Ubsan.M.loaded_segments (0x17288 : word) = Some W_17184.
Proof. vm_refl. Qed.
Lemma D_17184 : decode_any W_17184 = Some (Load SZ8 true 1 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17188 : bv 32 := 0x07013403.
Lemma F_17188 : fetch_word Ubsan.M.loaded_segments (0x1728c : word) = Some W_17188.
Proof. vm_refl. Qed.
Lemma D_17188 : decode_any W_17188 = Some (Load SZ8 true 8 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1718c : bv 32 := 0x06813483.
Lemma F_1718c : fetch_word Ubsan.M.loaded_segments (0x17290 : word) = Some W_1718c.
Proof. vm_refl. Qed.
Lemma D_1718c : decode_any W_1718c = Some (Load SZ8 true 9 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17190 : bv 32 := 0x06013903.
Lemma F_17190 : fetch_word Ubsan.M.loaded_segments (0x17294 : word) = Some W_17190.
Proof. vm_refl. Qed.
Lemma D_17190 : decode_any W_17190 = Some (Load SZ8 true 18 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17194 : bv 32 := 0x05813983.
Lemma F_17194 : fetch_word Ubsan.M.loaded_segments (0x17298 : word) = Some W_17194.
Proof. vm_refl. Qed.
Lemma D_17194 : decode_any W_17194 = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17198 : bv 32 := 0x05013a03.
Lemma F_17198 : fetch_word Ubsan.M.loaded_segments (0x1729c : word) = Some W_17198.
Proof. vm_refl. Qed.
Lemma D_17198 : decode_any W_17198 = Some (Load SZ8 true 20 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1719c : bv 32 := 0x04813a83.
Lemma F_1719c : fetch_word Ubsan.M.loaded_segments (0x172a0 : word) = Some W_1719c.
Proof. vm_refl. Qed.
Lemma D_1719c : decode_any W_1719c = Some (Load SZ8 true 21 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171a0 : bv 32 := 0x04013b03.
Lemma F_171a0 : fetch_word Ubsan.M.loaded_segments (0x172a4 : word) = Some W_171a0.
Proof. vm_refl. Qed.
Lemma D_171a0 : decode_any W_171a0 = Some (Load SZ8 true 22 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171a4 : bv 32 := 0x03813b83.
Lemma F_171a4 : fetch_word Ubsan.M.loaded_segments (0x172a8 : word) = Some W_171a4.
Proof. vm_refl. Qed.
Lemma D_171a4 : decode_any W_171a4 = Some (Load SZ8 true 23 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171a8 : bv 32 := 0x03013c03.
Lemma F_171a8 : fetch_word Ubsan.M.loaded_segments (0x172ac : word) = Some W_171a8.
Proof. vm_refl. Qed.
Lemma D_171a8 : decode_any W_171a8 = Some (Load SZ8 true 24 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171ac : bv 32 := 0x02813c83.
Lemma F_171ac : fetch_word Ubsan.M.loaded_segments (0x172b0 : word) = Some W_171ac.
Proof. vm_refl. Qed.
Lemma D_171ac : decode_any W_171ac = Some (Load SZ8 true 25 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171b0 : bv 32 := 0x02013d03.
Lemma F_171b0 : fetch_word Ubsan.M.loaded_segments (0x172b4 : word) = Some W_171b0.
Proof. vm_refl. Qed.
Lemma D_171b0 : decode_any W_171b0 = Some (Load SZ8 true 26 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171b4 : bv 32 := 0x01813d83.
Lemma F_171b4 : fetch_word Ubsan.M.loaded_segments (0x172b8 : word) = Some W_171b4.
Proof. vm_refl. Qed.
Lemma D_171b4 : decode_any W_171b4 = Some (Load SZ8 true 27 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171b8 : bv 32 := 0x08010113.
Lemma F_171b8 : fetch_word Ubsan.M.loaded_segments (0x172bc : word) = Some W_171b8.
Proof. vm_refl. Qed.
Lemma D_171b8 : decode_any W_171b8 = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171bc : bv 32 := 0x00008067.
Lemma F_171bc : fetch_word Ubsan.M.loaded_segments (0x172c0 : word) = Some W_171bc.
Proof. vm_refl. Qed.
Lemma D_171bc : decode_any W_171bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_171c4 : bv 32 := 0x0040006f.
Lemma F_171c4 : fetch_word Ubsan.M.loaded_segments (0x172c8 : word) = Some W_171c4.
Proof. vm_refl. Qed.
Lemma D_171c4 : decode_any W_171c4 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

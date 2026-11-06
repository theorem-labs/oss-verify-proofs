(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.H Require GcFlushU9.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_6559c : bv 32 := 0xfd010113.
Lemma F_6559c : fetch_word Ubsan.M.loaded_segments (0x655f4 : word) = Some W_6559c.
Proof. vm_refl. Qed.
Lemma D_6559c : decode_any W_6559c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_655a0 : bv 32 := 0x02113423.
Lemma F_655a0 : fetch_word Ubsan.M.loaded_segments (0x655f8 : word) = Some W_655a0.
Proof. vm_refl. Qed.
Lemma D_655a0 : decode_any W_655a0 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_655a4 : bv 32 := 0x02813023.
Lemma F_655a4 : fetch_word Ubsan.M.loaded_segments (0x655fc : word) = Some W_655a4.
Proof. vm_refl. Qed.
Lemma D_655a4 : decode_any W_655a4 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_655a8 : bv 32 := 0x00913c23.
Lemma F_655a8 : fetch_word Ubsan.M.loaded_segments (0x65600 : word) = Some W_655a8.
Proof. vm_refl. Qed.
Lemma D_655a8 : decode_any W_655a8 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_655ac : bv 32 := 0x01213823.
Lemma F_655ac : fetch_word Ubsan.M.loaded_segments (0x65604 : word) = Some W_655ac.
Proof. vm_refl. Qed.
Lemma D_655ac : decode_any W_655ac = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_655b0 : bv 32 := 0x06050063.
Lemma F_655b0 : fetch_word Ubsan.M.loaded_segments (0x65608 : word) = Some W_655b0.
Proof. vm_refl. Qed.
Lemma D_655b0 : decode_any W_655b0 = Some (Branch BC_EQ 10 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_655b4 : bv 32 := 0x00058413.
Lemma F_655b4 : fetch_word Ubsan.M.loaded_segments (0x6560c : word) = Some W_655b4.
Proof. vm_refl. Qed.
Lemma D_655b4 : decode_any W_655b4 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_655b8 : bv 32 := 0x00050913.
Lemma F_655b8 : fetch_word Ubsan.M.loaded_segments (0x65610 : word) = Some W_655b8.
Proof. vm_refl. Qed.
Lemma D_655b8 : decode_any W_655b8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_655bc : bv 32 := 0x00c10593.
Lemma F_655bc : fetch_word Ubsan.M.loaded_segments (0x65614 : word) = Some W_655bc.
Proof. vm_refl. Qed.
Lemma D_655bc : decode_any W_655bc = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_655c0 : bv 32 := 0x00810613.
Lemma F_655c0 : fetch_word Ubsan.M.loaded_segments (0x65618 : word) = Some W_655c0.
Proof. vm_refl. Qed.
Lemma D_655c0 : decode_any W_655c0 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_655c4 : bv 32 := 0x00410693.
Lemma F_655c4 : fetch_word Ubsan.M.loaded_segments (0x6561c : word) = Some W_655c4.
Proof. vm_refl. Qed.
Lemma D_655c4 : decode_any W_655c4 = Some (OpImm ALU_ADD 13 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_655c8 : bv 32 := 0xbb4fe0ef.
Lemma F_655c8 : fetch_word Ubsan.M.loaded_segments (0x65620 : word) = Some W_655c8.
Proof. vm_refl. Qed.
Lemma D_655c8 : decode_any W_655c8 = Some (Jal 1 2089908, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_655cc : bv 32 := 0x00412503.
Lemma F_655cc : fetch_word Ubsan.M.loaded_segments (0x65624 : word) = Some W_655cc.
Proof. vm_refl. Qed.
Lemma D_655cc : decode_any W_655cc = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_655d0 : bv 32 := 0x02000593.
Lemma F_655d0 : fetch_word Ubsan.M.loaded_segments (0x65628 : word) = Some W_655d0.
Proof. vm_refl. Qed.
Lemma D_655d0 : decode_any W_655d0 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_655d4 : bv 32 := 0x18b50c63.
Lemma F_655d4 : fetch_word Ubsan.M.loaded_segments (0x6562c : word) = Some W_655d4.
Proof. vm_refl. Qed.
Lemma D_655d4 : decode_any W_655d4 = Some (Branch BC_EQ 10 11 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6576c : bv 32 := 0x00000513.
Lemma F_6576c : fetch_word Ubsan.M.loaded_segments (0x657c4 : word) = Some W_6576c.
Proof. vm_refl. Qed.
Lemma D_6576c : decode_any W_6576c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65770 : bv 32 := 0x02813083.
Lemma F_65770 : fetch_word Ubsan.M.loaded_segments (0x657c8 : word) = Some W_65770.
Proof. vm_refl. Qed.
Lemma D_65770 : decode_any W_65770 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65774 : bv 32 := 0x02013403.
Lemma F_65774 : fetch_word Ubsan.M.loaded_segments (0x657cc : word) = Some W_65774.
Proof. vm_refl. Qed.
Lemma D_65774 : decode_any W_65774 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65778 : bv 32 := 0x01813483.
Lemma F_65778 : fetch_word Ubsan.M.loaded_segments (0x657d0 : word) = Some W_65778.
Proof. vm_refl. Qed.
Lemma D_65778 : decode_any W_65778 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6577c : bv 32 := 0x01013903.
Lemma F_6577c : fetch_word Ubsan.M.loaded_segments (0x657d4 : word) = Some W_6577c.
Proof. vm_refl. Qed.
Lemma D_6577c : decode_any W_6577c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65780 : bv 32 := 0x03010113.
Lemma F_65780 : fetch_word Ubsan.M.loaded_segments (0x657d8 : word) = Some W_65780.
Proof. vm_refl. Qed.
Lemma D_65780 : decode_any W_65780 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65784 : bv 32 := 0x00008067.
Lemma F_65784 : fetch_word Ubsan.M.loaded_segments (0x657dc : word) = Some W_65784.
Proof. vm_refl. Qed.
Lemma D_65784 : decode_any W_65784 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.


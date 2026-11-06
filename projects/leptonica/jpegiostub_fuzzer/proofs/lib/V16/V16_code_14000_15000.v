(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.H Require GcFlushU16.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.jpegiostub_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_1427c : bv 32 := 0x00050c63.
Lemma F_1427c : fetch_word Ubsan.M.loaded_segments (0x14380 : word) = Some W_1427c.
Proof. vm_refl. Qed.
Lemma D_1427c : decode_any W_1427c = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14280 : bv 32 := 0x00050613.
Lemma F_14280 : fetch_word Ubsan.M.loaded_segments (0x14384 : word) = Some W_14280.
Proof. vm_refl. Qed.
Lemma D_14280 : decode_any W_14280 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14284 : bv 32 := 0x00757513.
Lemma F_14284 : fetch_word Ubsan.M.loaded_segments (0x14388 : word) = Some W_14284.
Proof. vm_refl. Qed.
Lemma D_14284 : decode_any W_14284 = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14288 : bv 32 := 0x04051063.
Lemma F_14288 : fetch_word Ubsan.M.loaded_segments (0x1438c : word) = Some W_14288.
Proof. vm_refl. Qed.
Lemma D_14288 : decode_any W_14288 = Some (Branch BC_NE 10 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1428c : bv 32 := 0x02b62223.
Lemma F_1428c : fetch_word Ubsan.M.loaded_segments (0x14390 : word) = Some W_1428c.
Proof. vm_refl. Qed.
Lemma D_1428c : decode_any W_1428c = Some (Store SZ4 12 11 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14290 : bv 32 := 0x00008067.
Lemma F_14290 : fetch_word Ubsan.M.loaded_segments (0x14394 : word) = Some W_14290.
Proof. vm_refl. Qed.
Lemma D_14290 : decode_any W_14290 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

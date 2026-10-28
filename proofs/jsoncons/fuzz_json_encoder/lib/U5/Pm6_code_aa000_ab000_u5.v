(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_aa0e4 : bv 32 := 0xff010113.
Lemma F_aa0e4 : fetch_word Ubsan.M.loaded_segments (0xada6c : word) = Some W_aa0e4.
Proof. vm_refl. Qed.
Lemma D_aa0e4 : decode_any W_aa0e4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa0e8 : bv 32 := 0x00113423.
Lemma F_aa0e8 : fetch_word Ubsan.M.loaded_segments (0xada70 : word) = Some W_aa0e8.
Proof. vm_refl. Qed.
Lemma D_aa0e8 : decode_any W_aa0e8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa0ec : bv 32 := 0x00050e63.
Lemma F_aa0ec : fetch_word Ubsan.M.loaded_segments (0xada74 : word) = Some W_aa0ec.
Proof. vm_refl. Qed.
Lemma D_aa0ec : decode_any W_aa0ec = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa0f0 : bv 32 := 0x00050593.
Lemma F_aa0f0 : fetch_word Ubsan.M.loaded_segments (0xada78 : word) = Some W_aa0f0.
Proof. vm_refl. Qed.
Lemma D_aa0f0 : decode_any W_aa0f0 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa0f4 : bv 32 := 0x0001c517.
Lemma F_aa0f4 : fetch_word Ubsan.M.loaded_segments (0xada7c : word) = Some W_aa0f4.
Proof. vm_refl. Qed.
Lemma D_aa0f4 : decode_any W_aa0f4 = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa0f8 : bv 32 := 0x7a453503.
Lemma F_aa0f8 : fetch_word Ubsan.M.loaded_segments (0xada80 : word) = Some W_aa0f8.
Proof. vm_refl. Qed.
Lemma D_aa0f8 : decode_any W_aa0f8 = Some (Load SZ8 true 10 10 1956, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa0fc : bv 32 := 0x00800613.
Lemma F_aa0fc : fetch_word Ubsan.M.loaded_segments (0xada84 : word) = Some W_aa0fc.
Proof. vm_refl. Qed.
Lemma D_aa0fc : decode_any W_aa0fc = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa100 : bv 32 := 0x5c0100ef.
Lemma F_aa100 : fetch_word Ubsan.M.loaded_segments (0xada88 : word) = Some W_aa100.
Proof. vm_refl. Qed.
Lemma D_aa100 : decode_any W_aa100 = Some (Jal 1 67008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa104 : bv 32 := 0x01c0006f.
Lemma F_aa104 : fetch_word Ubsan.M.loaded_segments (0xada8c : word) = Some W_aa104.
Proof. vm_refl. Qed.
Lemma D_aa104 : decode_any W_aa104 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa120 : bv 32 := 0x0001c517.
Lemma F_aa120 : fetch_word Ubsan.M.loaded_segments (0xadaa8 : word) = Some W_aa120.
Proof. vm_refl. Qed.
Lemma D_aa120 : decode_any W_aa120 = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa124 : bv 32 := 0x77853503.
Lemma F_aa124 : fetch_word Ubsan.M.loaded_segments (0xadaac : word) = Some W_aa124.
Proof. vm_refl. Qed.
Lemma D_aa124 : decode_any W_aa124 = Some (Load SZ8 true 10 10 1912, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa128 : bv 32 := 0x000500a3.
Lemma F_aa128 : fetch_word Ubsan.M.loaded_segments (0xadab0 : word) = Some W_aa128.
Proof. vm_refl. Qed.
Lemma D_aa128 : decode_any W_aa128 = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa12c : bv 32 := 0x00053503.
Lemma F_aa12c : fetch_word Ubsan.M.loaded_segments (0xadab4 : word) = Some W_aa12c.
Proof. vm_refl. Qed.
Lemma D_aa12c : decode_any W_aa12c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa130 : bv 32 := 0x00020593.
Lemma F_aa130 : fetch_word Ubsan.M.loaded_segments (0xadab8 : word) = Some W_aa130.
Proof. vm_refl. Qed.
Lemma D_aa130 : decode_any W_aa130 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa134 : bv 32 := 0xfea5b823.
Lemma F_aa134 : fetch_word Ubsan.M.loaded_segments (0xadabc : word) = Some W_aa134.
Proof. vm_refl. Qed.
Lemma D_aa134 : decode_any W_aa134 = Some (Store SZ8 11 10 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa138 : bv 32 := 0x00813083.
Lemma F_aa138 : fetch_word Ubsan.M.loaded_segments (0xadac0 : word) = Some W_aa138.
Proof. vm_refl. Qed.
Lemma D_aa138 : decode_any W_aa138 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa13c : bv 32 := 0x01010113.
Lemma F_aa13c : fetch_word Ubsan.M.loaded_segments (0xadac4 : word) = Some W_aa13c.
Proof. vm_refl. Qed.
Lemma D_aa13c : decode_any W_aa13c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa140 : bv 32 := 0x00008067.
Lemma F_aa140 : fetch_word Ubsan.M.loaded_segments (0xadac8 : word) = Some W_aa140.
Proof. vm_refl. Qed.
Lemma D_aa140 : decode_any W_aa140 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa14c : bv 32 := 0xfffff5b7.
Lemma F_aa14c : fetch_word Ubsan.M.loaded_segments (0xadad4 : word) = Some W_aa14c.
Proof. vm_refl. Qed.
Lemma D_aa14c : decode_any W_aa14c = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa150 : bv 32 := 0x0015859b.
Lemma F_aa150 : fetch_word Ubsan.M.loaded_segments (0xadad8 : word) = Some W_aa150.
Proof. vm_refl. Qed.
Lemma D_aa150 : decode_any W_aa150 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa154 : bv 32 := 0x02b56663.
Lemma F_aa154 : fetch_word Ubsan.M.loaded_segments (0xadadc : word) = Some W_aa154.
Proof. vm_refl. Qed.
Lemma D_aa154 : decode_any W_aa154 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aa180 : bv 32 := 0x00008067.
Lemma F_aa180 : fetch_word Ubsan.M.loaded_segments (0xadb08 : word) = Some W_aa180.
Proof. vm_refl. Qed.
Lemma D_aa180 : decode_any W_aa180 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.


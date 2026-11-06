(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.simdjson.fuzz_utf8.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_bd594 : bv 32 := 0xfffff5b7.
Lemma F_bd594 : fetch_word Ubsan.M.loaded_segments (0xbd74c : word) = Some W_bd594.
Proof. vm_refl. Qed.
Lemma D_bd594 : decode_any W_bd594 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bd598 : bv 32 := 0x0015859b.
Lemma F_bd598 : fetch_word Ubsan.M.loaded_segments (0xbd750 : word) = Some W_bd598.
Proof. vm_refl. Qed.
Lemma D_bd598 : decode_any W_bd598 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bd59c : bv 32 := 0x02b56663.
Lemma F_bd59c : fetch_word Ubsan.M.loaded_segments (0xbd754 : word) = Some W_bd59c.
Proof. vm_refl. Qed.
Lemma D_bd59c : decode_any W_bd59c = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bd5a0 : bv 32 := 0xff010113.
Lemma F_bd5a0 : fetch_word Ubsan.M.loaded_segments (0xbd758 : word) = Some W_bd5a0.
Proof. vm_refl. Qed.
Lemma D_bd5a0 : decode_any W_bd5a0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bd5a4 : bv 32 := 0x00113423.
Lemma F_bd5a4 : fetch_word Ubsan.M.loaded_segments (0xbd75c : word) = Some W_bd5a4.
Proof. vm_refl. Qed.
Lemma D_bd5a4 : decode_any W_bd5a4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bd5a8 : bv 32 := 0x00813023.
Lemma F_bd5a8 : fetch_word Ubsan.M.loaded_segments (0xbd760 : word) = Some W_bd5a8.
Proof. vm_refl. Qed.
Lemma D_bd5a8 : decode_any W_bd5a8 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bd5ac : bv 32 := 0x40a0043b.
Lemma F_bd5ac : fetch_word Ubsan.M.loaded_segments (0xbd764 : word) = Some W_bd5ac.
Proof. vm_refl. Qed.
Lemma D_bd5ac : decode_any W_bd5ac = Some (Op32 ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bd5b0 : bv 32 := 0xa8dff0ef.
Lemma F_bd5b0 : fetch_word Ubsan.M.loaded_segments (0xbd768 : word) = Some W_bd5b0.
Proof. vm_refl. Qed.
Lemma D_bd5b0 : decode_any W_bd5b0 = Some (Jal 1 2095756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bd5b4 : bv 32 := 0x00852023.
Lemma F_bd5b4 : fetch_word Ubsan.M.loaded_segments (0xbd76c : word) = Some W_bd5b4.
Proof. vm_refl. Qed.
Lemma D_bd5b4 : decode_any W_bd5b4 = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bd5b8 : bv 32 := 0xfff00513.
Lemma F_bd5b8 : fetch_word Ubsan.M.loaded_segments (0xbd770 : word) = Some W_bd5b8.
Proof. vm_refl. Qed.
Lemma D_bd5b8 : decode_any W_bd5b8 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bd5bc : bv 32 := 0x00813083.
Lemma F_bd5bc : fetch_word Ubsan.M.loaded_segments (0xbd774 : word) = Some W_bd5bc.
Proof. vm_refl. Qed.
Lemma D_bd5bc : decode_any W_bd5bc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bd5c0 : bv 32 := 0x00013403.
Lemma F_bd5c0 : fetch_word Ubsan.M.loaded_segments (0xbd778 : word) = Some W_bd5c0.
Proof. vm_refl. Qed.
Lemma D_bd5c0 : decode_any W_bd5c0 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bd5c4 : bv 32 := 0x01010113.
Lemma F_bd5c4 : fetch_word Ubsan.M.loaded_segments (0xbd77c : word) = Some W_bd5c4.
Proof. vm_refl. Qed.
Lemma D_bd5c4 : decode_any W_bd5c4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bd5c8 : bv 32 := 0x00008067.
Lemma F_bd5c8 : fetch_word Ubsan.M.loaded_segments (0xbd780 : word) = Some W_bd5c8.
Proof. vm_refl. Qed.
Lemma D_bd5c8 : decode_any W_bd5c8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

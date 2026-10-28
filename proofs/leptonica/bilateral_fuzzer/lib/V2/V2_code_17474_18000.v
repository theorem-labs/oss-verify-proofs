(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_17b4c : bv 32 := 0xff010113.
Lemma F_17b4c : fetch_word Ubsan.M.loaded_segments (0x17df4 : word) = Some W_17b4c.
Proof. vm_refl. Qed.
Lemma D_17b4c : decode_any W_17b4c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b50 : bv 32 := 0x00113423.
Lemma F_17b50 : fetch_word Ubsan.M.loaded_segments (0x17df8 : word) = Some W_17b50.
Proof. vm_refl. Qed.
Lemma D_17b50 : decode_any W_17b50 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b54 : bv 32 := 0x00813023.
Lemma F_17b54 : fetch_word Ubsan.M.loaded_segments (0x17dfc : word) = Some W_17b54.
Proof. vm_refl. Qed.
Lemma D_17b54 : decode_any W_17b54 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b58 : bv 32 := 0x00060413.
Lemma F_17b58 : fetch_word Ubsan.M.loaded_segments (0x17e00 : word) = Some W_17b58.
Proof. vm_refl. Qed.
Lemma D_17b58 : decode_any W_17b58 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b5c : bv 32 := 0x00050613.
Lemma F_17b5c : fetch_word Ubsan.M.loaded_segments (0x17e04 : word) = Some W_17b5c.
Proof. vm_refl. Qed.
Lemma D_17b5c : decode_any W_17b5c = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b60 : bv 32 := 0xffffa517.
Lemma F_17b60 : fetch_word Ubsan.M.loaded_segments (0x17e08 : word) = Some W_17b60.
Proof. vm_refl. Qed.
Lemma D_17b60 : decode_any W_17b60 = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b64 : bv 32 := 0x60650513.
Lemma F_17b64 : fetch_word Ubsan.M.loaded_segments (0x17e0c : word) = Some W_17b64.
Proof. vm_refl. Qed.
Lemma D_17b64 : decode_any W_17b64 = Some (OpImm ALU_ADD 10 10 1542, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b68 : bv 32 := 0x018000ef.
Lemma F_17b68 : fetch_word Ubsan.M.loaded_segments (0x17e10 : word) = Some W_17b68.
Proof. vm_refl. Qed.
Lemma D_17b68 : decode_any W_17b68 = Some (Jal 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b6c : bv 32 := 0x00040513.
Lemma F_17b6c : fetch_word Ubsan.M.loaded_segments (0x17e14 : word) = Some W_17b6c.
Proof. vm_refl. Qed.
Lemma D_17b6c : decode_any W_17b6c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b70 : bv 32 := 0x00813083.
Lemma F_17b70 : fetch_word Ubsan.M.loaded_segments (0x17e18 : word) = Some W_17b70.
Proof. vm_refl. Qed.
Lemma D_17b70 : decode_any W_17b70 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b74 : bv 32 := 0x00013403.
Lemma F_17b74 : fetch_word Ubsan.M.loaded_segments (0x17e1c : word) = Some W_17b74.
Proof. vm_refl. Qed.
Lemma D_17b74 : decode_any W_17b74 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b78 : bv 32 := 0x01010113.
Lemma F_17b78 : fetch_word Ubsan.M.loaded_segments (0x17e20 : word) = Some W_17b78.
Proof. vm_refl. Qed.
Lemma D_17b78 : decode_any W_17b78 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b7c : bv 32 := 0x00008067.
Lemma F_17b7c : fetch_word Ubsan.M.loaded_segments (0x17e24 : word) = Some W_17b7c.
Proof. vm_refl. Qed.
Lemma D_17b7c : decode_any W_17b7c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c1c : bv 32 := 0xff010113.
Lemma F_17c1c : fetch_word Ubsan.M.loaded_segments (0x17ec4 : word) = Some W_17c1c.
Proof. vm_refl. Qed.
Lemma D_17c1c : decode_any W_17c1c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c20 : bv 32 := 0x00113423.
Lemma F_17c20 : fetch_word Ubsan.M.loaded_segments (0x17ec8 : word) = Some W_17c20.
Proof. vm_refl. Qed.
Lemma D_17c20 : decode_any W_17c20 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c24 : bv 32 := 0x00813023.
Lemma F_17c24 : fetch_word Ubsan.M.loaded_segments (0x17ecc : word) = Some W_17c24.
Proof. vm_refl. Qed.
Lemma D_17c24 : decode_any W_17c24 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c28 : bv 32 := 0x00060413.
Lemma F_17c28 : fetch_word Ubsan.M.loaded_segments (0x17ed0 : word) = Some W_17c28.
Proof. vm_refl. Qed.
Lemma D_17c28 : decode_any W_17c28 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c2c : bv 32 := 0x00050613.
Lemma F_17c2c : fetch_word Ubsan.M.loaded_segments (0x17ed4 : word) = Some W_17c2c.
Proof. vm_refl. Qed.
Lemma D_17c2c : decode_any W_17c2c = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c30 : bv 32 := 0xffffa517.
Lemma F_17c30 : fetch_word Ubsan.M.loaded_segments (0x17ed8 : word) = Some W_17c30.
Proof. vm_refl. Qed.
Lemma D_17c30 : decode_any W_17c30 = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c34 : bv 32 := 0x53650513.
Lemma F_17c34 : fetch_word Ubsan.M.loaded_segments (0x17edc : word) = Some W_17c34.
Proof. vm_refl. Qed.
Lemma D_17c34 : decode_any W_17c34 = Some (OpImm ALU_ADD 10 10 1334, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c38 : bv 32 := 0xf49ff0ef.
Lemma F_17c38 : fetch_word Ubsan.M.loaded_segments (0x17ee0 : word) = Some W_17c38.
Proof. vm_refl. Qed.
Lemma D_17c38 : decode_any W_17c38 = Some (Jal 1 2096968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c3c : bv 32 := 0x00040513.
Lemma F_17c3c : fetch_word Ubsan.M.loaded_segments (0x17ee4 : word) = Some W_17c3c.
Proof. vm_refl. Qed.
Lemma D_17c3c : decode_any W_17c3c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c40 : bv 32 := 0x00813083.
Lemma F_17c40 : fetch_word Ubsan.M.loaded_segments (0x17ee8 : word) = Some W_17c40.
Proof. vm_refl. Qed.
Lemma D_17c40 : decode_any W_17c40 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c44 : bv 32 := 0x00013403.
Lemma F_17c44 : fetch_word Ubsan.M.loaded_segments (0x17eec : word) = Some W_17c44.
Proof. vm_refl. Qed.
Lemma D_17c44 : decode_any W_17c44 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c48 : bv 32 := 0x01010113.
Lemma F_17c48 : fetch_word Ubsan.M.loaded_segments (0x17ef0 : word) = Some W_17c48.
Proof. vm_refl. Qed.
Lemma D_17c48 : decode_any W_17c48 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17c4c : bv 32 := 0x00008067.
Lemma F_17c4c : fetch_word Ubsan.M.loaded_segments (0x17ef4 : word) = Some W_17c4c.
Proof. vm_refl. Qed.
Lemma D_17c4c : decode_any W_17c4c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
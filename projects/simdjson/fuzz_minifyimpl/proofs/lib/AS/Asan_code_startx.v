(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.simdjson.fuzz_minifyimpl.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_147020 : bv 32 := 0x0004b503.
Lemma F_147020 : fetch_word Asan.M.loaded_segments (0x147030 : word) = Some W_147020.
Proof. vm_refl. Qed.
Lemma D_147020 : decode_any W_147020 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_147024 : bv 32 := 0x00848493.
Lemma F_147024 : fetch_word Asan.M.loaded_segments (0x147034 : word) = Some W_147024.
Proof. vm_refl. Qed.
Lemma D_147024 : decode_any W_147024 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_147028 : bv 32 := 0xfe051ce3.
Lemma F_147028 : fetch_word Asan.M.loaded_segments (0x147038 : word) = Some W_147028.
Proof. vm_refl. Qed.
Lemma D_147028 : decode_any W_147028 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition W_1470dc : bv 32 := 0x00b53023.
Lemma F_1470dc : fetch_word Asan.M.loaded_segments (0x1470ec : word) = Some W_1470dc.
Proof. vm_refl. Qed.
Lemma D_1470dc : decode_any W_1470dc = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1470e0 : bv 32 := 0x00158593.
Lemma F_1470e0 : fetch_word Asan.M.loaded_segments (0x1470f0 : word) = Some W_1470e0.
Proof. vm_refl. Qed.
Lemma D_1470e0 : decode_any W_1470e0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1470e4 : bv 32 := 0xfff5c683.
Lemma F_1470e4 : fetch_word Asan.M.loaded_segments (0x1470f4 : word) = Some W_1470e4.
Proof. vm_refl. Qed.
Lemma D_1470e4 : decode_any W_1470e4 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1470e8 : bv 32 := 0xfec68ae3.
Lemma F_1470e8 : fetch_word Asan.M.loaded_segments (0x1470f8 : word) = Some W_1470e8.
Proof. vm_refl. Qed.
Lemma D_1470e8 : decode_any W_1470e8 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1470ec : bv 32 := 0xfe069ae3.
Lemma F_1470ec : fetch_word Asan.M.loaded_segments (0x1470fc : word) = Some W_1470ec.
Proof. vm_refl. Qed.
Lemma D_1470ec : decode_any W_1470ec = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

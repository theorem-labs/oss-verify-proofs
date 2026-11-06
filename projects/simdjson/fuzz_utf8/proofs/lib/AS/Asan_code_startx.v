(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.simdjson.fuzz_utf8.images Require Import Asan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_146024 : bv 32 := 0x0004b503.
Lemma F_146024 : fetch_word Asan.M.loaded_segments (0x146380 : word) = Some W_146024.
Proof. vm_refl. Qed.
Lemma D_146024 : decode_any W_146024 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_146028 : bv 32 := 0x00848493.
Lemma F_146028 : fetch_word Asan.M.loaded_segments (0x146384 : word) = Some W_146028.
Proof. vm_refl. Qed.
Lemma D_146028 : decode_any W_146028 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14602c : bv 32 := 0xfe051ce3.
Lemma F_14602c : fetch_word Asan.M.loaded_segments (0x146388 : word) = Some W_14602c.
Proof. vm_refl. Qed.
Lemma D_14602c : decode_any W_14602c = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition W_1460e0 : bv 32 := 0x00b53023.
Lemma F_1460e0 : fetch_word Asan.M.loaded_segments (0x14643c : word) = Some W_1460e0.
Proof. vm_refl. Qed.
Lemma D_1460e0 : decode_any W_1460e0 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1460e4 : bv 32 := 0x00158593.
Lemma F_1460e4 : fetch_word Asan.M.loaded_segments (0x146440 : word) = Some W_1460e4.
Proof. vm_refl. Qed.
Lemma D_1460e4 : decode_any W_1460e4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1460e8 : bv 32 := 0xfff5c683.
Lemma F_1460e8 : fetch_word Asan.M.loaded_segments (0x146444 : word) = Some W_1460e8.
Proof. vm_refl. Qed.
Lemma D_1460e8 : decode_any W_1460e8 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1460ec : bv 32 := 0xfec68ae3.
Lemma F_1460ec : fetch_word Asan.M.loaded_segments (0x146448 : word) = Some W_1460ec.
Proof. vm_refl. Qed.
Lemma D_1460ec : decode_any W_1460ec = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1460f0 : bv 32 := 0xfe069ae3.
Lemma F_1460f0 : fetch_word Asan.M.loaded_segments (0x14644c : word) = Some W_1460f0.
Proof. vm_refl. Qed.
Lemma D_1460f0 : decode_any W_1460f0 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

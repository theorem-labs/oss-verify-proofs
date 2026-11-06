(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_8772c : bv 32 := 0x000ae597.
Lemma F_8772c : fetch_word Asan.M.loaded_segments (0x8777c : word) = Some W_8772c.
Proof. vm_refl. Qed.
Lemma D_8772c : decode_any W_8772c = Some (Auipc 11 174, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87730 : bv 32 := 0x84c5b583.
Lemma F_87730 : fetch_word Asan.M.loaded_segments (0x87780 : word) = Some W_87730.
Proof. vm_refl. Qed.
Lemma D_87730 : decode_any W_87730 = Some (Load SZ8 true 11 11 2124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87734 : bv 32 := 0x0905b583.
Lemma F_87734 : fetch_word Asan.M.loaded_segments (0x87784 : word) = Some W_87734.
Proof. vm_refl. Qed.
Lemma D_87734 : decode_any W_87734 = Some (Load SZ8 true 11 11 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87738 : bv 32 := 0x00058e63.
Lemma F_87738 : fetch_word Asan.M.loaded_segments (0x87788 : word) = Some W_87738.
Proof. vm_refl. Qed.
Lemma D_87738 : decode_any W_87738 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87754 : bv 32 := 0x00008067.
Lemma F_87754 : fetch_word Asan.M.loaded_segments (0x877a4 : word) = Some W_87754.
Proof. vm_refl. Qed.
Lemma D_87754 : decode_any W_87754 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87770 : bv 32 := 0x000ae597.
Lemma F_87770 : fetch_word Asan.M.loaded_segments (0x877c0 : word) = Some W_87770.
Proof. vm_refl. Qed.
Lemma D_87770 : decode_any W_87770 = Some (Auipc 11 174, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87774 : bv 32 := 0x8085b583.
Lemma F_87774 : fetch_word Asan.M.loaded_segments (0x877c4 : word) = Some W_87774.
Proof. vm_refl. Qed.
Lemma D_87774 : decode_any W_87774 = Some (Load SZ8 true 11 11 2056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87778 : bv 32 := 0x0905b583.
Lemma F_87778 : fetch_word Asan.M.loaded_segments (0x877c8 : word) = Some W_87778.
Proof. vm_refl. Qed.
Lemma D_87778 : decode_any W_87778 = Some (Load SZ8 true 11 11 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8777c : bv 32 := 0x00058a63.
Lemma F_8777c : fetch_word Asan.M.loaded_segments (0x877cc : word) = Some W_8777c.
Proof. vm_refl. Qed.
Lemma D_8777c : decode_any W_8777c = Some (Branch BC_EQ 11 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87790 : bv 32 := 0x00008067.
Lemma F_87790 : fetch_word Asan.M.loaded_segments (0x877e0 : word) = Some W_87790.
Proof. vm_refl. Qed.
Lemma D_87790 : decode_any W_87790 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

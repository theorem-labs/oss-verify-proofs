(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.yajl_ruby.json_fuzzer.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_91efc : bv 32 := 0x0004b503.
Lemma F_91efc : fetch_word AsanUbsan.M.loaded_segments (0x91f1c : word) = Some W_91efc.
Proof. vm_refl. Qed.
Lemma D_91efc : decode_any W_91efc = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91f00 : bv 32 := 0x00848493.
Lemma F_91f00 : fetch_word AsanUbsan.M.loaded_segments (0x91f20 : word) = Some W_91f00.
Proof. vm_refl. Qed.
Lemma D_91f00 : decode_any W_91f00 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91f04 : bv 32 := 0xfe051ce3.
Lemma F_91f04 : fetch_word AsanUbsan.M.loaded_segments (0x91f24 : word) = Some W_91f04.
Proof. vm_refl. Qed.
Lemma D_91f04 : decode_any W_91f04 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_91fb8 : bv 32 := 0x00b53023.
Lemma F_91fb8 : fetch_word AsanUbsan.M.loaded_segments (0x91fd8 : word) = Some W_91fb8.
Proof. vm_refl. Qed.
Lemma D_91fb8 : decode_any W_91fb8 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91fbc : bv 32 := 0x00158593.
Lemma F_91fbc : fetch_word AsanUbsan.M.loaded_segments (0x91fdc : word) = Some W_91fbc.
Proof. vm_refl. Qed.
Lemma D_91fbc : decode_any W_91fbc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91fc0 : bv 32 := 0xfff5c683.
Lemma F_91fc0 : fetch_word AsanUbsan.M.loaded_segments (0x91fe0 : word) = Some W_91fc0.
Proof. vm_refl. Qed.
Lemma D_91fc0 : decode_any W_91fc0 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91fc4 : bv 32 := 0xfec68ae3.
Lemma F_91fc4 : fetch_word AsanUbsan.M.loaded_segments (0x91fe4 : word) = Some W_91fc4.
Proof. vm_refl. Qed.
Lemma D_91fc4 : decode_any W_91fc4 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_91fc8 : bv 32 := 0xfe069ae3.
Lemma F_91fc8 : fetch_word AsanUbsan.M.loaded_segments (0x91fe8 : word) = Some W_91fc8.
Proof. vm_refl. Qed.
Lemma D_91fc8 : decode_any W_91fc8 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

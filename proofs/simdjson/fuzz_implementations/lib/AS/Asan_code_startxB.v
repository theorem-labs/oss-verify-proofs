(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.simdjson.fuzz_implementations.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_88d40 : bv 32 := 0x0004b503.
Lemma F_88d40 : fetch_word AsanUbsan.M.loaded_segments (0x15fcac : word) = Some W_88d40.
Proof. vm_refl. Qed.
Lemma D_88d40 : decode_any W_88d40 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88d44 : bv 32 := 0x00848493.
Lemma F_88d44 : fetch_word AsanUbsan.M.loaded_segments (0x15fcb0 : word) = Some W_88d44.
Proof. vm_refl. Qed.
Lemma D_88d44 : decode_any W_88d44 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_88d48 : bv 32 := 0xfe051ce3.
Lemma F_88d48 : fetch_word AsanUbsan.M.loaded_segments (0x15fcb4 : word) = Some W_88d48.
Proof. vm_refl. Qed.
Lemma D_88d48 : decode_any W_88d48 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_88dfc : bv 32 := 0x00b53023.
Lemma F_88dfc : fetch_word AsanUbsan.M.loaded_segments (0x15fd68 : word) = Some W_88dfc.
Proof. vm_refl. Qed.
Lemma D_88dfc : decode_any W_88dfc = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88e00 : bv 32 := 0x00158593.
Lemma F_88e00 : fetch_word AsanUbsan.M.loaded_segments (0x15fd6c : word) = Some W_88e00.
Proof. vm_refl. Qed.
Lemma D_88e00 : decode_any W_88e00 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_88e04 : bv 32 := 0xfff5c683.
Lemma F_88e04 : fetch_word AsanUbsan.M.loaded_segments (0x15fd70 : word) = Some W_88e04.
Proof. vm_refl. Qed.
Lemma D_88e04 : decode_any W_88e04 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_88e08 : bv 32 := 0xfec68ae3.
Lemma F_88e08 : fetch_word AsanUbsan.M.loaded_segments (0x15fd74 : word) = Some W_88e08.
Proof. vm_refl. Qed.
Lemma D_88e08 : decode_any W_88e08 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_88e0c : bv 32 := 0xfe069ae3.
Lemma F_88e0c : fetch_word AsanUbsan.M.loaded_segments (0x15fd78 : word) = Some W_88e0c.
Proof. vm_refl. Qed.
Lemma D_88e0c : decode_any W_88e0c = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

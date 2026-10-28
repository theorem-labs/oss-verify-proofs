(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)


From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.

Definition W_5e774 : bv 32 := 0x00038597.
Lemma F_5e774 : fetch_word Ubsan.M.loaded_segments (0x60550 : word) = Some W_5e774.
Proof. vm_refl. Qed.
Lemma D_5e774 : decode_any W_5e774 = Some (Auipc 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e778 : bv 32 := 0x94358683.
Lemma F_5e778 : fetch_word Ubsan.M.loaded_segments (0x60554 : word) = Some W_5e778.
Proof. vm_refl. Qed.
Lemma D_5e778 : decode_any W_5e778 = Some (Load SZ1 true 13 11 2371, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e77c : bv 32 := 0x1e068863.
Lemma F_5e77c : fetch_word Ubsan.M.loaded_segments (0x60558 : word) = Some W_5e77c.
Proof. vm_refl. Qed.
Lemma D_5e77c : decode_any W_5e77c = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

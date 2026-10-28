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

Definition W_5f094 : bv 32 := 0x00050213.
Lemma F_5f094 : fetch_word Ubsan.M.loaded_segments (0x60e70 : word) = Some W_5f094.
Proof. vm_refl. Qed.
Lemma D_5f094 : decode_any W_5f094 = Some (OpImm ALU_ADD 4 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f098 : bv 32 := 0x00000513.
Lemma F_5f098 : fetch_word Ubsan.M.loaded_segments (0x60e74 : word) = Some W_5f098.
Proof. vm_refl. Qed.
Lemma D_5f098 : decode_any W_5f098 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f09c : bv 32 := 0x00008067.
Lemma F_5f09c : fetch_word Ubsan.M.loaded_segments (0x60e78 : word) = Some W_5f09c.
Proof. vm_refl. Qed.
Lemma D_5f09c : decode_any W_5f09c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

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

Definition W_5e96c : bv 32 := 0x00008067.
Lemma F_5e96c : fetch_word Ubsan.M.loaded_segments (0x60748 : word) = Some W_5e96c.
Proof. vm_refl. Qed.
Lemma D_5e96c : decode_any W_5e96c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9fc : bv 32 := 0x00052583.
Lemma F_5e9fc : fetch_word Ubsan.M.loaded_segments (0x607d8 : word) = Some W_5e9fc.
Proof. vm_refl. Qed.
Lemma D_5e9fc : decode_any W_5e9fc = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea00 : bv 32 := 0x0005c463.
Lemma F_5ea00 : fetch_word Ubsan.M.loaded_segments (0x607dc : word) = Some W_5ea00.
Proof. vm_refl. Qed.
Lemma D_5ea00 : decode_any W_5ea00 = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea04 : bv 32 := 0x00008067.
Lemma F_5ea04 : fetch_word Ubsan.M.loaded_segments (0x607e0 : word) = Some W_5ea04.
Proof. vm_refl. Qed.
Lemma D_5ea04 : decode_any W_5ea04 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

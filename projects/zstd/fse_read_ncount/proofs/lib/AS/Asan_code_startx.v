(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.zstd.fse_read_ncount.images Require Import Asan.
Open Scope bv_scope.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Definition W_88908 : bv 32 := 0x0004b503.
Lemma F_88908 : fetch_word Asan.M.loaded_segments (0x888b8 : word) = Some W_88908.
Proof. vm_refl. Qed.
Lemma D_88908 : decode_any W_88908 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_8890c : bv 32 := 0x00848493.
Lemma F_8890c : fetch_word Asan.M.loaded_segments (0x888bc : word) = Some W_8890c.
Proof. vm_refl. Qed.
Lemma D_8890c : decode_any W_8890c = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_88910 : bv 32 := 0xfe051ce3.
Lemma F_88910 : fetch_word Asan.M.loaded_segments (0x888c0 : word) = Some W_88910.
Proof. vm_refl. Qed.
Lemma D_88910 : decode_any W_88910 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.
Definition W_889c4 : bv 32 := 0x00b53023.
Lemma F_889c4 : fetch_word Asan.M.loaded_segments (0x88974 : word) = Some W_889c4.
Proof. vm_refl. Qed.
Lemma D_889c4 : decode_any W_889c4 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_889c8 : bv 32 := 0x00158593.
Lemma F_889c8 : fetch_word Asan.M.loaded_segments (0x88978 : word) = Some W_889c8.
Proof. vm_refl. Qed.
Lemma D_889c8 : decode_any W_889c8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_889cc : bv 32 := 0xfff5c683.
Lemma F_889cc : fetch_word Asan.M.loaded_segments (0x8897c : word) = Some W_889cc.
Proof. vm_refl. Qed.
Lemma D_889cc : decode_any W_889cc = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.
Definition W_889d0 : bv 32 := 0xfec68ae3.
Lemma F_889d0 : fetch_word Asan.M.loaded_segments (0x88980 : word) = Some W_889d0.
Proof. vm_refl. Qed.
Lemma D_889d0 : decode_any W_889d0 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.
Definition W_889d4 : bv 32 := 0xfe069ae3.
Lemma F_889d4 : fetch_word Asan.M.loaded_segments (0x88984 : word) = Some W_889d4.
Proof. vm_refl. Qed.
Lemma D_889d4 : decode_any W_889d4 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

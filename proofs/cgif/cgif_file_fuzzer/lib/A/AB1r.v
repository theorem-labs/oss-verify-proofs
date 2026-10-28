(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
Open Scope bv_scope.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Definition W_52d28 : bv 32 := 0x000a2603.
Lemma F_52d28 : fetch_word Asan.M.loaded_segments (0x36378 : word) = Some W_52d28.
Proof. vm_refl. Qed.
Lemma D_52d28 : decode_any W_52d28 = Some (Load SZ4 true 12 20 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_52d2c : bv 32 := 0x00c6a023.
Lemma F_52d2c : fetch_word Asan.M.loaded_segments (0x3637c : word) = Some W_52d2c.
Proof. vm_refl. Qed.
Lemma D_52d2c : decode_any W_52d2c = Some (Store SZ4 13 12 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_52d30 : bv 32 := 0x00468693.
Lemma F_52d30 : fetch_word Asan.M.loaded_segments (0x36380 : word) = Some W_52d30.
Proof. vm_refl. Qed.
Lemma D_52d30 : decode_any W_52d30 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_52d34 : bv 32 := 0x004a0a13.
Lemma F_52d34 : fetch_word Asan.M.loaded_segments (0x36384 : word) = Some W_52d34.
Proof. vm_refl. Qed.
Lemma D_52d34 : decode_any W_52d34 = Some (OpImm ALU_ADD 20 20 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_52d38 : bv 32 := 0xfeb698e3.
Lemma F_52d38 : fetch_word Asan.M.loaded_segments (0x36388 : word) = Some W_52d38.
Proof. vm_refl. Qed.
Lemma D_52d38 : decode_any W_52d38 = Some (Branch BC_NE 13 11 8176, 4%Z).
Proof. vm_refl. Qed.

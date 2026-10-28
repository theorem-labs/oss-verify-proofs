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
Definition W_509d4 : bv 32 := 0x000b2583.
Lemma F_509d4 : fetch_word Asan.M.loaded_segments (0x34024 : word) = Some W_509d4.
Proof. vm_refl. Qed.
Lemma D_509d4 : decode_any W_509d4 = Some (Load SZ4 true 11 22 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_509d8 : bv 32 := 0x004b0b13.
Lemma F_509d8 : fetch_word Asan.M.loaded_segments (0x34028 : word) = Some W_509d8.
Proof. vm_refl. Qed.
Lemma D_509d8 : decode_any W_509d8 = Some (OpImm ALU_ADD 22 22 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_509dc : bv 32 := 0x00bca023.
Lemma F_509dc : fetch_word Asan.M.loaded_segments (0x3402c : word) = Some W_509dc.
Proof. vm_refl. Qed.
Lemma D_509dc : decode_any W_509dc = Some (Store SZ4 25 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_509e0 : bv 32 := 0x004c8c93.
Lemma F_509e0 : fetch_word Asan.M.loaded_segments (0x34030 : word) = Some W_509e0.
Proof. vm_refl. Qed.
Lemma D_509e0 : decode_any W_509e0 = Some (OpImm ALU_ADD 25 25 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_509e4 : bv 32 := 0xfeab18e3.
Lemma F_509e4 : fetch_word Asan.M.loaded_segments (0x34034 : word) = Some W_509e4.
Proof. vm_refl. Qed.
Lemma D_509e4 : decode_any W_509e4 = Some (Branch BC_NE 22 10 8176, 4%Z).
Proof. vm_refl. Qed.

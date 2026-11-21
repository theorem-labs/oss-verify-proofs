(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. *)
(* reloc14 *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.World Require Import Tgt_checksum_fuzzer_both.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_88960 : bv 32 := 0x0004b503.
Lemma F_88960 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x88a10 : word) = Some W_88960.
Proof. vm_refl. Qed.
Lemma D_88960 : decode_any W_88960 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88964 : bv 32 := 0x00848493.
Lemma F_88964 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x88a14 : word) = Some W_88964.
Proof. vm_refl. Qed.
Lemma D_88964 : decode_any W_88964 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_88968 : bv 32 := 0xfe051ce3.
Lemma F_88968 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x88a18 : word) = Some W_88968.
Proof. vm_refl. Qed.
Lemma D_88968 : decode_any W_88968 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


Definition W_88a1c : bv 32 := 0x00b53023.
Lemma F_88a1c : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x88acc : word) = Some W_88a1c.
Proof. vm_refl. Qed.
Lemma D_88a1c : decode_any W_88a1c = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88a20 : bv 32 := 0x00158593.
Lemma F_88a20 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x88ad0 : word) = Some W_88a20.
Proof. vm_refl. Qed.
Lemma D_88a20 : decode_any W_88a20 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_88a24 : bv 32 := 0xfff5c683.
Lemma F_88a24 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x88ad4 : word) = Some W_88a24.
Proof. vm_refl. Qed.
Lemma D_88a24 : decode_any W_88a24 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_88a28 : bv 32 := 0xfec68ae3.
Lemma F_88a28 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x88ad8 : word) = Some W_88a28.
Proof. vm_refl. Qed.
Lemma D_88a28 : decode_any W_88a28 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_88a2c : bv 32 := 0xfe069ae3.
Lemma F_88a2c : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x88adc : word) = Some W_88a2c.
Proof. vm_refl. Qed.
Lemma D_88a2c : decode_any W_88a2c = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

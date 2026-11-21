(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. *)
(* reloc14 *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.World Require Import Tgt_checksum_fuzzer_asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_88818 : bv 32 := 0x0004b503.
Lemma F_88818 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x888c0 : word) = Some W_88818.
Proof. vm_refl. Qed.
Lemma D_88818 : decode_any W_88818 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8881c : bv 32 := 0x00848493.
Lemma F_8881c : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x888c4 : word) = Some W_8881c.
Proof. vm_refl. Qed.
Lemma D_8881c : decode_any W_8881c = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_88820 : bv 32 := 0xfe051ce3.
Lemma F_88820 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x888c8 : word) = Some W_88820.
Proof. vm_refl. Qed.
Lemma D_88820 : decode_any W_88820 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


Definition W_888d4 : bv 32 := 0x00b53023.
Lemma F_888d4 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x8897c : word) = Some W_888d4.
Proof. vm_refl. Qed.
Lemma D_888d4 : decode_any W_888d4 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_888d8 : bv 32 := 0x00158593.
Lemma F_888d8 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x88980 : word) = Some W_888d8.
Proof. vm_refl. Qed.
Lemma D_888d8 : decode_any W_888d8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_888dc : bv 32 := 0xfff5c683.
Lemma F_888dc : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x88984 : word) = Some W_888dc.
Proof. vm_refl. Qed.
Lemma D_888dc : decode_any W_888dc = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_888e0 : bv 32 := 0xfec68ae3.
Lemma F_888e0 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x88988 : word) = Some W_888e0.
Proof. vm_refl. Qed.
Lemma D_888e0 : decode_any W_888e0 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_888e4 : bv 32 := 0xfe069ae3.
Lemma F_888e4 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x8898c : word) = Some W_888e4.
Proof. vm_refl. Qed.
Lemma D_888e4 : decode_any W_888e4 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

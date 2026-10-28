(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushU23.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_afcf4 : bv 32 := 0x08412503.
Lemma F_afcf4 : fetch_word Ubsan.M.loaded_segments (0xafcf4 : word) = Some W_afcf4.
Proof. vm_refl. Qed.
Lemma D_afcf4 : decode_any W_afcf4 = Some (Load SZ4 true 10 2 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_afcf8 : bv 32 := 0x08012583.
Lemma F_afcf8 : fetch_word Ubsan.M.loaded_segments (0xafcf8 : word) = Some W_afcf8.
Proof. vm_refl. Qed.
Lemma D_afcf8 : decode_any W_afcf8 = Some (Load SZ4 true 11 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_afcfc : bv 32 := 0x00050613.
Lemma F_afcfc : fetch_word Ubsan.M.loaded_segments (0xafcfc : word) = Some W_afcfc.
Proof. vm_refl. Qed.
Lemma D_afcfc : decode_any W_afcfc = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_afd00 : bv 32 := 0x00a5c463.
Lemma F_afd00 : fetch_word Ubsan.M.loaded_segments (0xafd00 : word) = Some W_afd00.
Proof. vm_refl. Qed.
Lemma D_afd00 : decode_any W_afd00 = Some (Branch BC_LT 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_afd04 : bv 32 := 0x00058613.
Lemma F_afd04 : fetch_word Ubsan.M.loaded_segments (0xafd04 : word) = Some W_afd04.
Proof. vm_refl. Qed.
Lemma D_afd04 : decode_any W_afd04 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_afd08 : bv 32 := 0xd0057453.
Lemma F_afd08 : fetch_word Ubsan.M.loaded_segments (0xafd08 : word) = Some W_afd08.
Proof. vm_refl. Qed.
Lemma D_afd08 : decode_any W_afd08 = Some (Fcvt FC_S FC_W 8 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_afd0c : bv 32 := 0xd005f4d3.
Lemma F_afd0c : fetch_word Ubsan.M.loaded_segments (0xafd0c : word) = Some W_afd0c.
Proof. vm_refl. Qed.
Lemma D_afd0c : decode_any W_afd0c = Some (Fcvt FC_S FC_W 9 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_afd10 : bv 32 := 0x02c95463.
Lemma F_afd10 : fetch_word Ubsan.M.loaded_segments (0xafd10 : word) = Some W_afd10.
Proof. vm_refl. Qed.
Lemma D_afd10 : decode_any W_afd10 = Some (Branch BC_GE 18 12 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_afd14 : bv 32 := 0x089477d3.
Lemma F_afd14 : fetch_word Ubsan.M.loaded_segments (0xafd14 : word) = Some W_afd14.
Proof. vm_refl. Qed.
Lemma D_afd14 : decode_any W_afd14 = Some (Fari F_SUB FMT_S 15 8 9 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_afd18 : bv 32 := 0x00947753.
Lemma F_afd18 : fetch_word Ubsan.M.loaded_segments (0xafd18 : word) = Some W_afd18.
Proof. vm_refl. Qed.
Lemma D_afd18 : decode_any W_afd18 = Some (Fari F_ADD FMT_S 14 8 9 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_afd1c : bv 32 := 0x420787d3.
Lemma F_afd1c : fetch_word Ubsan.M.loaded_segments (0xafd1c : word) = Some W_afd1c.
Proof. vm_refl. Qed.
Lemma D_afd1c : decode_any W_afd1c = Some (Fcvt FC_D FC_S 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_afd20 : bv 32 := 0x42070753.
Lemma F_afd20 : fetch_word Ubsan.M.loaded_segments (0xafd20 : word) = Some W_afd20.
Proof. vm_refl. Qed.
Lemma D_afd20 : decode_any W_afd20 = Some (Fcvt FC_D FC_S 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_afd24 : bv 32 := 0x5a077753.
Lemma F_afd24 : fetch_word Ubsan.M.loaded_segments (0xafd24 : word) = Some W_afd24.
Proof. vm_refl. Qed.
Lemma D_afd24 : decode_any W_afd24 = Some (Fsqrt FMT_D 14 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_afd28 : bv 32 := 0x1ae7f7d3.
Lemma F_afd28 : fetch_word Ubsan.M.loaded_segments (0xafd28 : word) = Some W_afd28.
Proof. vm_refl. Qed.
Lemma D_afd28 : decode_any W_afd28 = Some (Fari F_DIV FMT_D 15 15 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_afd2c : bv 32 := 0x02f7f7d3.
Lemma F_afd2c : fetch_word Ubsan.M.loaded_segments (0xafd2c : word) = Some W_afd2c.
Proof. vm_refl. Qed.
Lemma D_afd2c : decode_any W_afd2c = Some (Fari F_ADD FMT_D 15 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_afd30 : bv 32 := 0x4017f7d3.
Lemma F_afd30 : fetch_word Ubsan.M.loaded_segments (0xafd30 : word) = Some W_afd30.
Proof. vm_refl. Qed.
Lemma D_afd30 : decode_any W_afd30 = Some (Fcvt FC_S FC_D 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_afd34 : bv 32 := 0x00f42027.
Lemma F_afd34 : fetch_word Ubsan.M.loaded_segments (0xafd34 : word) = Some W_afd34.
Proof. vm_refl. Qed.
Lemma D_afd34 : decode_any W_afd34 = Some (FStore FMT_S 8 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_afd38 : bv 32 := 0x08048263.
Lemma F_afd38 : fetch_word Ubsan.M.loaded_segments (0xafd38 : word) = Some W_afd38.
Proof. vm_refl. Qed.
Lemma D_afd38 : decode_any W_afd38 = Some (Branch BC_EQ 9 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_afd3c : bv 32 := 0x000a0c63.
Lemma F_afd3c : fetch_word Ubsan.M.loaded_segments (0xafd3c : word) = Some W_afd3c.
Proof. vm_refl. Qed.
Lemma D_afd3c : decode_any W_afd3c = Some (Branch BC_EQ 20 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_afd40 : bv 32 := 0xfff64517.
Lemma F_afd40 : fetch_word Ubsan.M.loaded_segments (0xafd40 : word) = Some W_afd40.
Proof. vm_refl. Qed.
Lemma D_afd40 : decode_any W_afd40 = Some (Auipc 10 1048420, 4%Z).
Proof. vm_refl. Qed.

Definition W_afd44 : bv 32 := 0xad950513.
Lemma F_afd44 : fetch_word Ubsan.M.loaded_segments (0xafd44 : word) = Some W_afd44.
Proof. vm_refl. Qed.
Lemma D_afd44 : decode_any W_afd44 = Some (OpImm ALU_ADD 10 10 2777, 4%Z).
Proof. vm_refl. Qed.

Definition W_afd48 : bv 32 := 0x00300613.
Lemma F_afd48 : fetch_word Ubsan.M.loaded_segments (0xafd48 : word) = Some W_afd48.
Proof. vm_refl. Qed.
Lemma D_afd48 : decode_any W_afd48 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_afd4c : bv 32 := 0x000a0593.
Lemma F_afd4c : fetch_word Ubsan.M.loaded_segments (0xafd4c : word) = Some W_afd4c.
Proof. vm_refl. Qed.
Lemma D_afd4c : decode_any W_afd4c = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_afd50 : bv 32 := 0xefcba0ef.
Lemma F_afd50 : fetch_word Ubsan.M.loaded_segments (0xafd50 : word) = Some W_afd50.
Proof. vm_refl. Qed.
Lemma D_afd50 : decode_any W_afd50 = Some (Jal 1 1812220, 4%Z).
Proof. vm_refl. Qed.

(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushU23.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_70e84 : bv 32 := 0x00050e63.
Lemma F_70e84 : fetch_word Ubsan.M.loaded_segments (0x70e84 : word) = Some W_70e84.
Proof. vm_refl. Qed.
Lemma D_70e84 : decode_any W_70e84 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e88 : bv 32 := 0x04058263.
Lemma F_70e88 : fetch_word Ubsan.M.loaded_segments (0x70e88 : word) = Some W_70e88.
Proof. vm_refl. Qed.
Lemma D_70e88 : decode_any W_70e88 = Some (Branch BC_EQ 11 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e8c : bv 32 := 0x00060793.
Lemma F_70e8c : fetch_word Ubsan.M.loaded_segments (0x70e8c : word) = Some W_70e8c.
Proof. vm_refl. Qed.
Lemma D_70e8c : decode_any W_70e8c = Some (OpImm ALU_ADD 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e90 : bv 32 := 0x00058613.
Lemma F_70e90 : fetch_word Ubsan.M.loaded_segments (0x70e90 : word) = Some W_70e90.
Proof. vm_refl. Qed.
Lemma D_70e90 : decode_any W_70e90 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e94 : bv 32 := 0x00058693.
Lemma F_70e94 : fetch_word Ubsan.M.loaded_segments (0x70e94 : word) = Some W_70e94.
Proof. vm_refl. Qed.
Lemma D_70e94 : decode_any W_70e94 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e98 : bv 32 := 0x00058713.
Lemma F_70e98 : fetch_word Ubsan.M.loaded_segments (0x70e98 : word) = Some W_70e98.
Proof. vm_refl. Qed.
Lemma D_70e98 : decode_any W_70e98 = Some (OpImm ALU_ADD 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e9c : bv 32 := 0x03c0006f.
Lemma F_70e9c : fetch_word Ubsan.M.loaded_segments (0x70e9c : word) = Some W_70e9c.
Proof. vm_refl. Qed.
Lemma D_70e9c : decode_any W_70e9c = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_70ea0 : bv 32 := 0x000b6517.
Lemma F_70ea0 : fetch_word Ubsan.M.loaded_segments (0x70ea0 : word) = Some W_70ea0.
Proof. vm_refl. Qed.
Lemma D_70ea0 : decode_any W_70ea0 = Some (Auipc 10 182, 4%Z).
Proof. vm_refl. Qed.

Definition W_70ea4 : bv 32 := 0xbd053503.
Lemma F_70ea4 : fetch_word Ubsan.M.loaded_segments (0x70ea4 : word) = Some W_70ea4.
Proof. vm_refl. Qed.
Lemma D_70ea4 : decode_any W_70ea4 = Some (Load SZ8 true 10 10 3024, 4%Z).
Proof. vm_refl. Qed.

Definition W_70ea8 : bv 32 := 0x00052503.
Lemma F_70ea8 : fetch_word Ubsan.M.loaded_segments (0x70ea8 : word) = Some W_70ea8.
Proof. vm_refl. Qed.
Lemma D_70ea8 : decode_any W_70ea8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70eac : bv 32 := 0x00500593.
Lemma F_70eac : fetch_word Ubsan.M.loaded_segments (0x70eac : word) = Some W_70eac.
Proof. vm_refl. Qed.
Lemma D_70eac : decode_any W_70eac = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_70eb0 : bv 32 := 0x02a5c063.
Lemma F_70eb0 : fetch_word Ubsan.M.loaded_segments (0x70eb0 : word) = Some W_70eb0.
Proof. vm_refl. Qed.
Lemma D_70eb0 : decode_any W_70eb0 = Some (Branch BC_LT 11 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_70eb4 : bv 32 := 0xfff9f517.
Lemma F_70eb4 : fetch_word Ubsan.M.loaded_segments (0x70eb4 : word) = Some W_70eb4.
Proof. vm_refl. Qed.
Lemma D_70eb4 : decode_any W_70eb4 = Some (Auipc 10 1048479, 4%Z).
Proof. vm_refl. Qed.

Definition W_70eb8 : bv 32 := 0xfffab597.
Lemma F_70eb8 : fetch_word Ubsan.M.loaded_segments (0x70eb8 : word) = Some W_70eb8.
Proof. vm_refl. Qed.
Lemma D_70eb8 : decode_any W_70eb8 = Some (Auipc 11 1048491, 4%Z).
Proof. vm_refl. Qed.

Definition W_70ebc : bv 32 := 0x4a150513.
Lemma F_70ebc : fetch_word Ubsan.M.loaded_segments (0x70ebc : word) = Some W_70ebc.
Proof. vm_refl. Qed.
Lemma D_70ebc : decode_any W_70ebc = Some (OpImm ALU_ADD 10 10 1185, 4%Z).
Proof. vm_refl. Qed.

Definition W_70ec0 : bv 32 := 0xb5758593.
Lemma F_70ec0 : fetch_word Ubsan.M.loaded_segments (0x70ec0 : word) = Some W_70ec0.
Proof. vm_refl. Qed.
Lemma D_70ec0 : decode_any W_70ec0 = Some (OpImm ALU_ADD 11 11 2903, 4%Z).
Proof. vm_refl. Qed.

Definition W_70ec4 : bv 32 := 0x00000613.
Lemma F_70ec4 : fetch_word Ubsan.M.loaded_segments (0x70ec4 : word) = Some W_70ec4.
Proof. vm_refl. Qed.
Lemma D_70ec4 : decode_any W_70ec4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70ec8 : bv 32 := 0x879f206f.
Lemma F_70ec8 : fetch_word Ubsan.M.loaded_segments (0x70ec8 : word) = Some W_70ec8.
Proof. vm_refl. Qed.
Lemma D_70ec8 : decode_any W_70ec8 = Some (Jal 0 2041976, 4%Z).
Proof. vm_refl. Qed.

Definition W_70ecc : bv 32 := 0xc3dfd06f.
Lemma F_70ecc : fetch_word Ubsan.M.loaded_segments (0x70ecc : word) = Some W_70ecc.
Proof. vm_refl. Qed.
Lemma D_70ecc : decode_any W_70ecc = Some (Jal 0 2087996, 4%Z).
Proof. vm_refl. Qed.

Definition W_70ed0 : bv 32 := 0x00000513.
Lemma F_70ed0 : fetch_word Ubsan.M.loaded_segments (0x70ed0 : word) = Some W_70ed0.
Proof. vm_refl. Qed.
Lemma D_70ed0 : decode_any W_70ed0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70ed4 : bv 32 := 0x00008067.
Lemma F_70ed4 : fetch_word Ubsan.M.loaded_segments (0x70ed4 : word) = Some W_70ed4.
Proof. vm_refl. Qed.
Lemma D_70ed4 : decode_any W_70ed4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

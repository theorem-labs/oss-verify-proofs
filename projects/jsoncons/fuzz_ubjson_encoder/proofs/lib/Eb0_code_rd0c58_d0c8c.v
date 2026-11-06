(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_1365f0 : bv 32 := 0xff010113.
Lemma F_1365f0 : fetch_word AsanUbsan.M.loaded_segments (0x136634 : word) = Some W_1365f0.
Proof. vm_refl. Qed.
Lemma D_1365f0 : decode_any W_1365f0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1365f4 : bv 32 := 0x00113423.
Lemma F_1365f4 : fetch_word AsanUbsan.M.loaded_segments (0x136638 : word) = Some W_1365f4.
Proof. vm_refl. Qed.
Lemma D_1365f4 : decode_any W_1365f4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1365f8 : bv 32 := 0x00060693.
Lemma F_1365f8 : fetch_word AsanUbsan.M.loaded_segments (0x13663c : word) = Some W_1365f8.
Proof. vm_refl. Qed.
Lemma D_1365f8 : decode_any W_1365f8 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1365fc : bv 32 := 0x00058613.
Lemma F_1365fc : fetch_word AsanUbsan.M.loaded_segments (0x136640 : word) = Some W_1365fc.
Proof. vm_refl. Qed.
Lemma D_1365fc : decode_any W_1365fc = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_136600 : bv 32 := 0x00050593.
Lemma F_136600 : fetch_word AsanUbsan.M.loaded_segments (0x136644 : word) = Some W_136600.
Proof. vm_refl. Qed.
Lemma D_136600 : decode_any W_136600 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_136604 : bv 32 := 0x03f00513.
Lemma F_136604 : fetch_word AsanUbsan.M.loaded_segments (0x136648 : word) = Some W_136604.
Proof. vm_refl. Qed.
Lemma D_136604 : decode_any W_136604 = Some (OpImm ALU_ADD 10 0 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_136608 : bv 32 := 0x00000713.
Lemma F_136608 : fetch_word AsanUbsan.M.loaded_segments (0x13664c : word) = Some W_136608.
Proof. vm_refl. Qed.
Lemma D_136608 : decode_any W_136608 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13660c : bv 32 := 0x00000793.
Lemma F_13660c : fetch_word AsanUbsan.M.loaded_segments (0x136650 : word) = Some W_13660c.
Proof. vm_refl. Qed.
Lemma D_13660c : decode_any W_13660c = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_136610 : bv 32 := 0x00000813.
Lemma F_136610 : fetch_word AsanUbsan.M.loaded_segments (0x136654 : word) = Some W_136610.
Proof. vm_refl. Qed.
Lemma D_136610 : decode_any W_136610 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_136614 : bv 32 := 0xdb8fa0ef.
Lemma F_136614 : fetch_word AsanUbsan.M.loaded_segments (0x136658 : word) = Some W_136614.
Proof. vm_refl. Qed.
Lemma D_136614 : decode_any W_136614 = Some (Jal 1 2074040, 4%Z).
Proof. vm_refl. Qed.

Definition W_136618 : bv 32 := 0x00813083.
Lemma F_136618 : fetch_word AsanUbsan.M.loaded_segments (0x13665c : word) = Some W_136618.
Proof. vm_refl. Qed.
Lemma D_136618 : decode_any W_136618 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13661c : bv 32 := 0x01010113.
Lemma F_13661c : fetch_word AsanUbsan.M.loaded_segments (0x136660 : word) = Some W_13661c.
Proof. vm_refl. Qed.
Lemma D_13661c : decode_any W_13661c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_136620 : bv 32 := 0x899e806f.
Lemma F_136620 : fetch_word AsanUbsan.M.loaded_segments (0x136664 : word) = Some W_136620.
Proof. vm_refl. Qed.
Lemma D_136620 : decode_any W_136620 = Some (Jal 0 2001048, 4%Z).
Proof. vm_refl. Qed.

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

Definition W_6dc64 : bv 32 := 0x06a05a63.
Lemma F_6dc64 : fetch_word Ubsan.M.loaded_segments (0x6dc64 : word) = Some W_6dc64.
Proof. vm_refl. Qed.
Lemma D_6dc64 : decode_any W_6dc64 = Some (Branch BC_GE 0 10 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dc68 : bv 32 := 0x08b05c63.
Lemma F_6dc68 : fetch_word Ubsan.M.loaded_segments (0x6dc68 : word) = Some W_6dc68.
Proof. vm_refl. Qed.
Lemma D_6dc68 : decode_any W_6dc68 = Some (Branch BC_GE 0 11 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dc6c : bv 32 := 0x02a606b3.
Lemma F_6dc6c : fetch_word Ubsan.M.loaded_segments (0x6dc6c : word) = Some W_6dc6c.
Proof. vm_refl. Qed.
Lemma D_6dc6c : decode_any W_6dc6c = Some (Mul M_MUL 13 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dc70 : bv 32 := 0x20000737.
Lemma F_6dc70 : fetch_word Ubsan.M.loaded_segments (0x6dc70 : word) = Some W_6dc70.
Proof. vm_refl. Qed.
Lemma D_6dc70 : decode_any W_6dc70 = Some (Lui 14 131072, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dc74 : bv 32 := 0xfe17071b.
Lemma F_6dc74 : fetch_word Ubsan.M.loaded_segments (0x6dc74 : word) = Some W_6dc74.
Proof. vm_refl. Qed.
Lemma D_6dc74 : decode_any W_6dc74 = Some (OpImm32 14 14 4065, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dc78 : bv 32 := 0x0ae6e863.
Lemma F_6dc78 : fetch_word Ubsan.M.loaded_segments (0x6dc78 : word) = Some W_6dc78.
Proof. vm_refl. Qed.
Lemma D_6dc78 : decode_any W_6dc78 = Some (Branch BC_LTU 13 14 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd28 : bv 32 := 0x01f68693.
Lemma F_6dd28 : fetch_word Ubsan.M.loaded_segments (0x6dd28 : word) = Some W_6dd28.
Proof. vm_refl. Qed.
Lemma D_6dd28 : decode_any W_6dd28 = Some (OpImm ALU_ADD 13 13 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd2c : bv 32 := 0x0056da13.
Lemma F_6dd2c : fetch_word Ubsan.M.loaded_segments (0x6dd2c : word) = Some W_6dd2c.
Proof. vm_refl. Qed.
Lemma D_6dd2c : decode_any W_6dd2c = Some (ShiftImm ALU_SRL 20 13 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd30 : bv 32 := 0x02ba06b3.
Lemma F_6dd30 : fetch_word Ubsan.M.loaded_segments (0x6dd30 : word) = Some W_6dd30.
Proof. vm_refl. Qed.
Lemma D_6dd30 : decode_any W_6dd30 = Some (Mul M_MUL 13 20 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd34 : bv 32 := 0x00269693.
Lemma F_6dd34 : fetch_word Ubsan.M.loaded_segments (0x6dd34 : word) = Some W_6dd34.
Proof. vm_refl. Qed.
Lemma D_6dd34 : decode_any W_6dd34 = Some (ShiftImm ALU_SLL 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd38 : bv 32 := 0x01f6d713.
Lemma F_6dd38 : fetch_word Ubsan.M.loaded_segments (0x6dd38 : word) = Some W_6dd38.
Proof. vm_refl. Qed.
Lemma D_6dd38 : decode_any W_6dd38 = Some (ShiftImm ALU_SRL 14 13 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd3c : bv 32 := 0x0a070463.
Lemma F_6dd3c : fetch_word Ubsan.M.loaded_segments (0x6dd3c : word) = Some W_6dd3c.
Proof. vm_refl. Qed.
Lemma D_6dd3c : decode_any W_6dd3c = Some (Branch BC_EQ 14 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dde4 : bv 32 := 0x04000737.
Lemma F_6dde4 : fetch_word Ubsan.M.loaded_segments (0x6dde4 : word) = Some W_6dde4.
Proof. vm_refl. Qed.
Lemma D_6dde4 : decode_any W_6dde4 = Some (Lui 14 16384, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dde8 : bv 32 := 0x0017071b.
Lemma F_6dde8 : fetch_word Ubsan.M.loaded_segments (0x6dde8 : word) = Some W_6dde8.
Proof. vm_refl. Qed.
Lemma D_6dde8 : decode_any W_6dde8 = Some (OpImm32 14 14 1, 4%Z).
Proof. vm_refl. Qed.

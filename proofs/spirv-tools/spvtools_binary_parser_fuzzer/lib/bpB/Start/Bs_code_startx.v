(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_163018 : bv 32 := 0x0004b503.
Lemma F_163018 : fetch_word AsanUbsan.M.loaded_segments (0x1649cc : word) = Some W_163018.
Proof. vm_refl. Qed.
Lemma D_163018 : decode_any W_163018 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16301c : bv 32 := 0x00848493.
Lemma F_16301c : fetch_word AsanUbsan.M.loaded_segments (0x1649d0 : word) = Some W_16301c.
Proof. vm_refl. Qed.
Lemma D_16301c : decode_any W_16301c = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_163020 : bv 32 := 0xfe051ce3.
Lemma F_163020 : fetch_word AsanUbsan.M.loaded_segments (0x1649d4 : word) = Some W_163020.
Proof. vm_refl. Qed.
Lemma D_163020 : decode_any W_163020 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_1630d4 : bv 32 := 0x00b53023.
Lemma F_1630d4 : fetch_word AsanUbsan.M.loaded_segments (0x164a88 : word) = Some W_1630d4.
Proof. vm_refl. Qed.
Lemma D_1630d4 : decode_any W_1630d4 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1630d8 : bv 32 := 0x00158593.
Lemma F_1630d8 : fetch_word AsanUbsan.M.loaded_segments (0x164a8c : word) = Some W_1630d8.
Proof. vm_refl. Qed.
Lemma D_1630d8 : decode_any W_1630d8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1630dc : bv 32 := 0xfff5c683.
Lemma F_1630dc : fetch_word AsanUbsan.M.loaded_segments (0x164a90 : word) = Some W_1630dc.
Proof. vm_refl. Qed.
Lemma D_1630dc : decode_any W_1630dc = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1630e0 : bv 32 := 0xfec68ae3.
Lemma F_1630e0 : fetch_word AsanUbsan.M.loaded_segments (0x164a94 : word) = Some W_1630e0.
Proof. vm_refl. Qed.
Lemma D_1630e0 : decode_any W_1630e0 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_1630e4 : bv 32 := 0xfe069ae3.
Lemma F_1630e4 : fetch_word AsanUbsan.M.loaded_segments (0x164a98 : word) = Some W_1630e4.
Proof. vm_refl. Qed.
Lemma D_1630e4 : decode_any W_1630e4 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

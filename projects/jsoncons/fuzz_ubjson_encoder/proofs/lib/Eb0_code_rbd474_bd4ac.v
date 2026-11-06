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

Definition W_11eeb8 : bv 32 := 0xfffff5b7.
Lemma F_11eeb8 : fetch_word AsanUbsan.M.loaded_segments (0x11eefc : word) = Some W_11eeb8.
Proof. vm_refl. Qed.
Lemma D_11eeb8 : decode_any W_11eeb8 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_11eebc : bv 32 := 0x0015859b.
Lemma F_11eebc : fetch_word AsanUbsan.M.loaded_segments (0x11ef00 : word) = Some W_11eebc.
Proof. vm_refl. Qed.
Lemma D_11eebc : decode_any W_11eebc = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_11eec0 : bv 32 := 0x02b56663.
Lemma F_11eec0 : fetch_word AsanUbsan.M.loaded_segments (0x11ef04 : word) = Some W_11eec0.
Proof. vm_refl. Qed.
Lemma D_11eec0 : decode_any W_11eec0 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_11eec4 : bv 32 := 0xff010113.
Lemma F_11eec4 : fetch_word AsanUbsan.M.loaded_segments (0x11ef08 : word) = Some W_11eec4.
Proof. vm_refl. Qed.
Lemma D_11eec4 : decode_any W_11eec4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_11eec8 : bv 32 := 0x00113423.
Lemma F_11eec8 : fetch_word AsanUbsan.M.loaded_segments (0x11ef0c : word) = Some W_11eec8.
Proof. vm_refl. Qed.
Lemma D_11eec8 : decode_any W_11eec8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_11eecc : bv 32 := 0x00813023.
Lemma F_11eecc : fetch_word AsanUbsan.M.loaded_segments (0x11ef10 : word) = Some W_11eecc.
Proof. vm_refl. Qed.
Lemma D_11eecc : decode_any W_11eecc = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_11eed0 : bv 32 := 0x40a0043b.
Lemma F_11eed0 : fetch_word AsanUbsan.M.loaded_segments (0x11ef14 : word) = Some W_11eed0.
Proof. vm_refl. Qed.
Lemma D_11eed0 : decode_any W_11eed0 = Some (Op32 ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_11eed4 : bv 32 := 0x8b9ff0ef.
Lemma F_11eed4 : fetch_word AsanUbsan.M.loaded_segments (0x11ef18 : word) = Some W_11eed4.
Proof. vm_refl. Qed.
Lemma D_11eed4 : decode_any W_11eed4 = Some (Jal 1 2095288, 4%Z).
Proof. vm_refl. Qed.

Definition W_11eed8 : bv 32 := 0x00852023.
Lemma F_11eed8 : fetch_word AsanUbsan.M.loaded_segments (0x11ef1c : word) = Some W_11eed8.
Proof. vm_refl. Qed.
Lemma D_11eed8 : decode_any W_11eed8 = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_11eedc : bv 32 := 0xfff00513.
Lemma F_11eedc : fetch_word AsanUbsan.M.loaded_segments (0x11ef20 : word) = Some W_11eedc.
Proof. vm_refl. Qed.
Lemma D_11eedc : decode_any W_11eedc = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_11eee0 : bv 32 := 0x00813083.
Lemma F_11eee0 : fetch_word AsanUbsan.M.loaded_segments (0x11ef24 : word) = Some W_11eee0.
Proof. vm_refl. Qed.
Lemma D_11eee0 : decode_any W_11eee0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_11eee4 : bv 32 := 0x00013403.
Lemma F_11eee4 : fetch_word AsanUbsan.M.loaded_segments (0x11ef28 : word) = Some W_11eee4.
Proof. vm_refl. Qed.
Lemma D_11eee4 : decode_any W_11eee4 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_11eee8 : bv 32 := 0x01010113.
Lemma F_11eee8 : fetch_word AsanUbsan.M.loaded_segments (0x11ef2c : word) = Some W_11eee8.
Proof. vm_refl. Qed.
Lemma D_11eee8 : decode_any W_11eee8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_11eeec : bv 32 := 0x00008067.
Lemma F_11eeec : fetch_word AsanUbsan.M.loaded_segments (0x11ef30 : word) = Some W_11eeec.
Proof. vm_refl. Qed.
Lemma D_11eeec : decode_any W_11eeec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

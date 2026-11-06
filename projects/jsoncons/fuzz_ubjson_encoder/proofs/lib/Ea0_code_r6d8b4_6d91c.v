(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_88478 : bv 32 := 0x000b1597.
Lemma F_88478 : fetch_word Asan.M.loaded_segments (0x884c8 : word) = Some W_88478.
Proof. vm_refl. Qed.
Lemma D_88478 : decode_any W_88478 = Some (Auipc 11 177, 4%Z).
Proof. vm_refl. Qed.

Definition W_8847c : bv 32 := 0xce05b583.
Lemma F_8847c : fetch_word Asan.M.loaded_segments (0x884cc : word) = Some W_8847c.
Proof. vm_refl. Qed.
Lemma D_8847c : decode_any W_8847c = Some (Load SZ8 true 11 11 3296, 4%Z).
Proof. vm_refl. Qed.

Definition W_88480 : bv 32 := 0x0905b583.
Lemma F_88480 : fetch_word Asan.M.loaded_segments (0x884d0 : word) = Some W_88480.
Proof. vm_refl. Qed.
Lemma D_88480 : decode_any W_88480 = Some (Load SZ8 true 11 11 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_88484 : bv 32 := 0x00058e63.
Lemma F_88484 : fetch_word Asan.M.loaded_segments (0x884d4 : word) = Some W_88484.
Proof. vm_refl. Qed.
Lemma D_88484 : decode_any W_88484 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_884a0 : bv 32 := 0x00008067.
Lemma F_884a0 : fetch_word Asan.M.loaded_segments (0x884f0 : word) = Some W_884a0.
Proof. vm_refl. Qed.
Lemma D_884a0 : decode_any W_884a0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_884bc : bv 32 := 0x000b1597.
Lemma F_884bc : fetch_word Asan.M.loaded_segments (0x8850c : word) = Some W_884bc.
Proof. vm_refl. Qed.
Lemma D_884bc : decode_any W_884bc = Some (Auipc 11 177, 4%Z).
Proof. vm_refl. Qed.

Definition W_884c0 : bv 32 := 0xc9c5b583.
Lemma F_884c0 : fetch_word Asan.M.loaded_segments (0x88510 : word) = Some W_884c0.
Proof. vm_refl. Qed.
Lemma D_884c0 : decode_any W_884c0 = Some (Load SZ8 true 11 11 3228, 4%Z).
Proof. vm_refl. Qed.

Definition W_884c4 : bv 32 := 0x0905b583.
Lemma F_884c4 : fetch_word Asan.M.loaded_segments (0x88514 : word) = Some W_884c4.
Proof. vm_refl. Qed.
Lemma D_884c4 : decode_any W_884c4 = Some (Load SZ8 true 11 11 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_884c8 : bv 32 := 0x00058a63.
Lemma F_884c8 : fetch_word Asan.M.loaded_segments (0x88518 : word) = Some W_884c8.
Proof. vm_refl. Qed.
Lemma D_884c8 : decode_any W_884c8 = Some (Branch BC_EQ 11 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_884dc : bv 32 := 0x00008067.
Lemma F_884dc : fetch_word Asan.M.loaded_segments (0x8852c : word) = Some W_884dc.
Proof. vm_refl. Qed.
Lemma D_884dc : decode_any W_884dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

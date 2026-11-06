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

Definition W_84c04 : bv 32 := 0x02850583.
Lemma F_84c04 : fetch_word AsanUbsan.M.loaded_segments (0x84c54 : word) = Some W_84c04.
Proof. vm_refl. Qed.
Lemma D_84c04 : decode_any W_84c04 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c08 : bv 32 := 0x0230000f.
Lemma F_84c08 : fetch_word AsanUbsan.M.loaded_segments (0x84c58 : word) = Some W_84c08.
Proof. vm_refl. Qed.
Lemma D_84c08 : decode_any W_84c08 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c0c : bv 32 := 0x02058c63.
Lemma F_84c0c : fetch_word AsanUbsan.M.loaded_segments (0x84c5c : word) = Some W_84c0c.
Proof. vm_refl. Qed.
Lemma D_84c0c : decode_any W_84c0c = Some (Branch BC_EQ 11 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c44 : bv 32 := 0x00853583.
Lemma F_84c44 : fetch_word AsanUbsan.M.loaded_segments (0x84c94 : word) = Some W_84c44.
Proof. vm_refl. Qed.
Lemma D_84c44 : decode_any W_84c44 = Some (Load SZ8 true 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c48 : bv 32 := 0x01053503.
Lemma F_84c48 : fetch_word AsanUbsan.M.loaded_segments (0x84c98 : word) = Some W_84c48.
Proof. vm_refl. Qed.
Lemma D_84c48 : decode_any W_84c48 = Some (Load SZ8 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c4c : bv 32 := 0x00b53533.
Lemma F_84c4c : fetch_word AsanUbsan.M.loaded_segments (0x84c9c : word) = Some W_84c4c.
Proof. vm_refl. Qed.
Lemma D_84c4c : decode_any W_84c4c = Some (Op ALU_SLTU 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c50 : bv 32 := 0x40a00533.
Lemma F_84c50 : fetch_word AsanUbsan.M.loaded_segments (0x84ca0 : word) = Some W_84c50.
Proof. vm_refl. Qed.
Lemma D_84c50 : decode_any W_84c50 = Some (Op ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c54 : bv 32 := 0x00b57533.
Lemma F_84c54 : fetch_word AsanUbsan.M.loaded_segments (0x84ca4 : word) = Some W_84c54.
Proof. vm_refl. Qed.
Lemma D_84c54 : decode_any W_84c54 = Some (Op ALU_AND 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c58 : bv 32 := 0x00008067.
Lemma F_84c58 : fetch_word AsanUbsan.M.loaded_segments (0x84ca8 : word) = Some W_84c58.
Proof. vm_refl. Qed.
Lemma D_84c58 : decode_any W_84c58 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c5c : bv 32 := 0x02850583.
Lemma F_84c5c : fetch_word AsanUbsan.M.loaded_segments (0x84cac : word) = Some W_84c5c.
Proof. vm_refl. Qed.
Lemma D_84c5c : decode_any W_84c5c = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c60 : bv 32 := 0x0230000f.
Lemma F_84c60 : fetch_word AsanUbsan.M.loaded_segments (0x84cb0 : word) = Some W_84c60.
Proof. vm_refl. Qed.
Lemma D_84c60 : decode_any W_84c60 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c64 : bv 32 := 0x02058c63.
Lemma F_84c64 : fetch_word AsanUbsan.M.loaded_segments (0x84cb4 : word) = Some W_84c64.
Proof. vm_refl. Qed.
Lemma D_84c64 : decode_any W_84c64 = Some (Branch BC_EQ 11 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_84c9c : bv 32 := 0x00853583.
Lemma F_84c9c : fetch_word AsanUbsan.M.loaded_segments (0x84cec : word) = Some W_84c9c.
Proof. vm_refl. Qed.
Lemma D_84c9c : decode_any W_84c9c = Some (Load SZ8 true 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ca0 : bv 32 := 0x01053503.
Lemma F_84ca0 : fetch_word AsanUbsan.M.loaded_segments (0x84cf0 : word) = Some W_84ca0.
Proof. vm_refl. Qed.
Lemma D_84ca0 : decode_any W_84ca0 = Some (Load SZ8 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ca4 : bv 32 := 0x00b535b3.
Lemma F_84ca4 : fetch_word AsanUbsan.M.loaded_segments (0x84cf4 : word) = Some W_84ca4.
Proof. vm_refl. Qed.
Lemma D_84ca4 : decode_any W_84ca4 = Some (Op ALU_SLTU 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_84ca8 : bv 32 := 0x40b005b3.
Lemma F_84ca8 : fetch_word AsanUbsan.M.loaded_segments (0x84cf8 : word) = Some W_84ca8.
Proof. vm_refl. Qed.
Lemma D_84ca8 : decode_any W_84ca8 = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_84cac : bv 32 := 0x00a5f533.
Lemma F_84cac : fetch_word AsanUbsan.M.loaded_segments (0x84cfc : word) = Some W_84cac.
Proof. vm_refl. Qed.
Lemma D_84cac : decode_any W_84cac = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_84cb0 : bv 32 := 0x00008067.
Lemma F_84cb0 : fetch_word AsanUbsan.M.loaded_segments (0x84d00 : word) = Some W_84cb0.
Proof. vm_refl. Qed.
Lemma D_84cb0 : decode_any W_84cb0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

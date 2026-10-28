(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_19b38 : bv 32 := 0x0035f713.
Lemma F_19b38 : fetch_word Ubsan.M.loaded_segments (0x19b38 : word) = Some W_19b38.
Proof. vm_refl. Qed.
Lemma D_19b38 : decode_any W_19b38 = Some (OpImm ALU_AND 14 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b3c : bv 32 := 0x00058663.
Lemma F_19b3c : fetch_word Ubsan.M.loaded_segments (0x19b3c : word) = Some W_19b3c.
Proof. vm_refl. Qed.
Lemma D_19b3c : decode_any W_19b3c = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b40 : bv 32 := 0x0a071863.
Lemma F_19b40 : fetch_word Ubsan.M.loaded_segments (0x19b40 : word) = Some W_19b40.
Proof. vm_refl. Qed.
Lemma D_19b40 : decode_any W_19b40 = Some (Branch BC_NE 14 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b44 : bv 32 := 0x0005a023.
Lemma F_19b44 : fetch_word Ubsan.M.loaded_segments (0x19b44 : word) = Some W_19b44.
Proof. vm_refl. Qed.
Lemma D_19b44 : decode_any W_19b44 = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b48 : bv 32 := 0x00367793.
Lemma F_19b48 : fetch_word Ubsan.M.loaded_segments (0x19b48 : word) = Some W_19b48.
Proof. vm_refl. Qed.
Lemma D_19b48 : decode_any W_19b48 = Some (OpImm ALU_AND 15 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b4c : bv 32 := 0x00060663.
Lemma F_19b4c : fetch_word Ubsan.M.loaded_segments (0x19b4c : word) = Some W_19b4c.
Proof. vm_refl. Qed.
Lemma D_19b4c : decode_any W_19b4c = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b50 : bv 32 := 0x0a079063.
Lemma F_19b50 : fetch_word Ubsan.M.loaded_segments (0x19b50 : word) = Some W_19b50.
Proof. vm_refl. Qed.
Lemma D_19b50 : decode_any W_19b50 = Some (Branch BC_NE 15 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b54 : bv 32 := 0x00062023.
Lemma F_19b54 : fetch_word Ubsan.M.loaded_segments (0x19b54 : word) = Some W_19b54.
Proof. vm_refl. Qed.
Lemma D_19b54 : decode_any W_19b54 = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b58 : bv 32 := 0x0036f813.
Lemma F_19b58 : fetch_word Ubsan.M.loaded_segments (0x19b58 : word) = Some W_19b58.
Proof. vm_refl. Qed.
Lemma D_19b58 : decode_any W_19b58 = Some (OpImm ALU_AND 16 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b5c : bv 32 := 0x00068663.
Lemma F_19b5c : fetch_word Ubsan.M.loaded_segments (0x19b5c : word) = Some W_19b5c.
Proof. vm_refl. Qed.
Lemma D_19b5c : decode_any W_19b5c = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b60 : bv 32 := 0x08081863.
Lemma F_19b60 : fetch_word Ubsan.M.loaded_segments (0x19b60 : word) = Some W_19b60.
Proof. vm_refl. Qed.
Lemma D_19b60 : decode_any W_19b60 = Some (Branch BC_NE 16 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b64 : bv 32 := 0x0006a023.
Lemma F_19b64 : fetch_word Ubsan.M.loaded_segments (0x19b64 : word) = Some W_19b64.
Proof. vm_refl. Qed.
Lemma D_19b64 : decode_any W_19b64 = Some (Store SZ4 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b68 : bv 32 := 0x04050663.
Lemma F_19b68 : fetch_word Ubsan.M.loaded_segments (0x19b68 : word) = Some W_19b68.
Proof. vm_refl. Qed.
Lemma D_19b68 : decode_any W_19b68 = Some (Branch BC_EQ 10 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b6c : bv 32 := 0x00757893.
Lemma F_19b6c : fetch_word Ubsan.M.loaded_segments (0x19b6c : word) = Some W_19b6c.
Proof. vm_refl. Qed.
Lemma D_19b6c : decode_any W_19b6c = Some (OpImm ALU_AND 17 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b70 : bv 32 := 0x00058a63.
Lemma F_19b70 : fetch_word Ubsan.M.loaded_segments (0x19b70 : word) = Some W_19b70.
Proof. vm_refl. Qed.
Lemma D_19b70 : decode_any W_19b70 = Some (Branch BC_EQ 11 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b74 : bv 32 := 0x00e8e733.
Lemma F_19b74 : fetch_word Ubsan.M.loaded_segments (0x19b74 : word) = Some W_19b74.
Proof. vm_refl. Qed.
Lemma D_19b74 : decode_any W_19b74 = Some (Op ALU_OR 14 17 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b78 : bv 32 := 0x06071c63.
Lemma F_19b78 : fetch_word Ubsan.M.loaded_segments (0x19b78 : word) = Some W_19b78.
Proof. vm_refl. Qed.
Lemma D_19b78 : decode_any W_19b78 = Some (Branch BC_NE 14 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b7c : bv 32 := 0x00052703.
Lemma F_19b7c : fetch_word Ubsan.M.loaded_segments (0x19b7c : word) = Some W_19b7c.
Proof. vm_refl. Qed.
Lemma D_19b7c : decode_any W_19b7c = Some (Load SZ4 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b80 : bv 32 := 0x00e5a023.
Lemma F_19b80 : fetch_word Ubsan.M.loaded_segments (0x19b80 : word) = Some W_19b80.
Proof. vm_refl. Qed.
Lemma D_19b80 : decode_any W_19b80 = Some (Store SZ4 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b84 : bv 32 := 0x00060a63.
Lemma F_19b84 : fetch_word Ubsan.M.loaded_segments (0x19b84 : word) = Some W_19b84.
Proof. vm_refl. Qed.
Lemma D_19b84 : decode_any W_19b84 = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b88 : bv 32 := 0x00f8e5b3.
Lemma F_19b88 : fetch_word Ubsan.M.loaded_segments (0x19b88 : word) = Some W_19b88.
Proof. vm_refl. Qed.
Lemma D_19b88 : decode_any W_19b88 = Some (Op ALU_OR 11 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b8c : bv 32 := 0x06059263.
Lemma F_19b8c : fetch_word Ubsan.M.loaded_segments (0x19b8c : word) = Some W_19b8c.
Proof. vm_refl. Qed.
Lemma D_19b8c : decode_any W_19b8c = Some (Branch BC_NE 11 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b90 : bv 32 := 0x00452583.
Lemma F_19b90 : fetch_word Ubsan.M.loaded_segments (0x19b90 : word) = Some W_19b90.
Proof. vm_refl. Qed.
Lemma D_19b90 : decode_any W_19b90 = Some (Load SZ4 true 11 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b94 : bv 32 := 0x00b62023.
Lemma F_19b94 : fetch_word Ubsan.M.loaded_segments (0x19b94 : word) = Some W_19b94.
Proof. vm_refl. Qed.
Lemma D_19b94 : decode_any W_19b94 = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b98 : bv 32 := 0x04068463.
Lemma F_19b98 : fetch_word Ubsan.M.loaded_segments (0x19b98 : word) = Some W_19b98.
Proof. vm_refl. Qed.
Lemma D_19b98 : decode_any W_19b98 = Some (Branch BC_EQ 13 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_19b9c : bv 32 := 0x0108e5b3.
Lemma F_19b9c : fetch_word Ubsan.M.loaded_segments (0x19b9c : word) = Some W_19b9c.
Proof. vm_refl. Qed.
Lemma D_19b9c : decode_any W_19b9c = Some (Op ALU_OR 11 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ba0 : bv 32 := 0x04059863.
Lemma F_19ba0 : fetch_word Ubsan.M.loaded_segments (0x19ba0 : word) = Some W_19ba0.
Proof. vm_refl. Qed.
Lemma D_19ba0 : decode_any W_19ba0 = Some (Branch BC_NE 11 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ba4 : bv 32 := 0x00852503.
Lemma F_19ba4 : fetch_word Ubsan.M.loaded_segments (0x19ba4 : word) = Some W_19ba4.
Proof. vm_refl. Qed.
Lemma D_19ba4 : decode_any W_19ba4 = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_19ba8 : bv 32 := 0x00a6a023.
Lemma F_19ba8 : fetch_word Ubsan.M.loaded_segments (0x19ba8 : word) = Some W_19ba8.
Proof. vm_refl. Qed.
Lemma D_19ba8 : decode_any W_19ba8 = Some (Store SZ4 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bac : bv 32 := 0x00058513.
Lemma F_19bac : fetch_word Ubsan.M.loaded_segments (0x19bac : word) = Some W_19bac.
Proof. vm_refl. Qed.
Lemma D_19bac : decode_any W_19bac = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_19bb0 : bv 32 := 0x00008067.
Lemma F_19bb0 : fetch_word Ubsan.M.loaded_segments (0x19bb0 : word) = Some W_19bb0.
Proof. vm_refl. Qed.
Lemma D_19bb0 : decode_any W_19bb0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

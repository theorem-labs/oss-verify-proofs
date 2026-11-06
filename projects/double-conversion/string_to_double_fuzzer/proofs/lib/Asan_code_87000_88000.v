(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation ASEGS_I := ImgA.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_879cc : bv 32 := 0x02060063.
Lemma F_879cc : fetch_word ASEGS_I (0x879cc : word) = Some W_879cc.
Proof. vm_refl. Qed.
Lemma D_879cc : decode_any W_879cc = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879d0 : bv 32 := 0x00c50633.
Lemma F_879d0 : fetch_word ASEGS_I (0x879d0 : word) = Some W_879d0.
Proof. vm_refl. Qed.
Lemma D_879d0 : decode_any W_879d0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879d4 : bv 32 := 0x00050693.
Lemma F_879d4 : fetch_word ASEGS_I (0x879d4 : word) = Some W_879d4.
Proof. vm_refl. Qed.
Lemma D_879d4 : decode_any W_879d4 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879d8 : bv 32 := 0x0005c703.
Lemma F_879d8 : fetch_word ASEGS_I (0x879d8 : word) = Some W_879d8.
Proof. vm_refl. Qed.
Lemma D_879d8 : decode_any W_879d8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879dc : bv 32 := 0x00e68023.
Lemma F_879dc : fetch_word ASEGS_I (0x879dc : word) = Some W_879dc.
Proof. vm_refl. Qed.
Lemma D_879dc : decode_any W_879dc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879e0 : bv 32 := 0x00168693.
Lemma F_879e0 : fetch_word ASEGS_I (0x879e0 : word) = Some W_879e0.
Proof. vm_refl. Qed.
Lemma D_879e0 : decode_any W_879e0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879e4 : bv 32 := 0x00158593.
Lemma F_879e4 : fetch_word ASEGS_I (0x879e4 : word) = Some W_879e4.
Proof. vm_refl. Qed.
Lemma D_879e4 : decode_any W_879e4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879e8 : bv 32 := 0xfec698e3.
Lemma F_879e8 : fetch_word ASEGS_I (0x879e8 : word) = Some W_879e8.
Proof. vm_refl. Qed.
Lemma D_879e8 : decode_any W_879e8 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_879ec : bv 32 := 0x00008067.
Lemma F_879ec : fetch_word ASEGS_I (0x879ec : word) = Some W_879ec.
Proof. vm_refl. Qed.
Lemma D_879ec : decode_any W_879ec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a48 : bv 32 := 0x00a666b3.
Lemma F_87a48 : fetch_word ASEGS_I (0x87a48 : word) = Some W_87a48.
Proof. vm_refl. Qed.
Lemma D_87a48 : decode_any W_87a48 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a4c : bv 32 := 0x00f6f693.
Lemma F_87a4c : fetch_word ASEGS_I (0x87a4c : word) = Some W_87a4c.
Proof. vm_refl. Qed.
Lemma D_87a4c : decode_any W_87a4c = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a50 : bv 32 := 0x02068063.
Lemma F_87a50 : fetch_word ASEGS_I (0x87a50 : word) = Some W_87a50.
Proof. vm_refl. Qed.
Lemma D_87a50 : decode_any W_87a50 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a54 : bv 32 := 0x04060863.
Lemma F_87a54 : fetch_word ASEGS_I (0x87a54 : word) = Some W_87a54.
Proof. vm_refl. Qed.
Lemma D_87a54 : decode_any W_87a54 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a58 : bv 32 := 0x00c50633.
Lemma F_87a58 : fetch_word ASEGS_I (0x87a58 : word) = Some W_87a58.
Proof. vm_refl. Qed.
Lemma D_87a58 : decode_any W_87a58 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a5c : bv 32 := 0x00050693.
Lemma F_87a5c : fetch_word ASEGS_I (0x87a5c : word) = Some W_87a5c.
Proof. vm_refl. Qed.
Lemma D_87a5c : decode_any W_87a5c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a60 : bv 32 := 0x00b68023.
Lemma F_87a60 : fetch_word ASEGS_I (0x87a60 : word) = Some W_87a60.
Proof. vm_refl. Qed.
Lemma D_87a60 : decode_any W_87a60 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a64 : bv 32 := 0x00168693.
Lemma F_87a64 : fetch_word ASEGS_I (0x87a64 : word) = Some W_87a64.
Proof. vm_refl. Qed.
Lemma D_87a64 : decode_any W_87a64 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a68 : bv 32 := 0xfec69ce3.
Lemma F_87a68 : fetch_word ASEGS_I (0x87a68 : word) = Some W_87a68.
Proof. vm_refl. Qed.
Lemma D_87a68 : decode_any W_87a68 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a6c : bv 32 := 0x0380006f.
Lemma F_87a6c : fetch_word ASEGS_I (0x87a6c : word) = Some W_87a6c.
Proof. vm_refl. Qed.
Lemma D_87a6c : decode_any W_87a6c = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a70 : bv 32 := 0x02060a63.
Lemma F_87a70 : fetch_word ASEGS_I (0x87a70 : word) = Some W_87a70.
Proof. vm_refl. Qed.
Lemma D_87a70 : decode_any W_87a70 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a74 : bv 32 := 0x00c50633.
Lemma F_87a74 : fetch_word ASEGS_I (0x87a74 : word) = Some W_87a74.
Proof. vm_refl. Qed.
Lemma D_87a74 : decode_any W_87a74 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a78 : bv 32 := 0x00859693.
Lemma F_87a78 : fetch_word ASEGS_I (0x87a78 : word) = Some W_87a78.
Proof. vm_refl. Qed.
Lemma D_87a78 : decode_any W_87a78 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a7c : bv 32 := 0x00b6e5b3.
Lemma F_87a7c : fetch_word ASEGS_I (0x87a7c : word) = Some W_87a7c.
Proof. vm_refl. Qed.
Lemma D_87a7c : decode_any W_87a7c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a80 : bv 32 := 0x01059693.
Lemma F_87a80 : fetch_word ASEGS_I (0x87a80 : word) = Some W_87a80.
Proof. vm_refl. Qed.
Lemma D_87a80 : decode_any W_87a80 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a84 : bv 32 := 0x00b6e5b3.
Lemma F_87a84 : fetch_word ASEGS_I (0x87a84 : word) = Some W_87a84.
Proof. vm_refl. Qed.
Lemma D_87a84 : decode_any W_87a84 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a88 : bv 32 := 0x02059693.
Lemma F_87a88 : fetch_word ASEGS_I (0x87a88 : word) = Some W_87a88.
Proof. vm_refl. Qed.
Lemma D_87a88 : decode_any W_87a88 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a8c : bv 32 := 0x00b6e5b3.
Lemma F_87a8c : fetch_word ASEGS_I (0x87a8c : word) = Some W_87a8c.
Proof. vm_refl. Qed.
Lemma D_87a8c : decode_any W_87a8c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a90 : bv 32 := 0x00050693.
Lemma F_87a90 : fetch_word ASEGS_I (0x87a90 : word) = Some W_87a90.
Proof. vm_refl. Qed.
Lemma D_87a90 : decode_any W_87a90 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a94 : bv 32 := 0x00b6b023.
Lemma F_87a94 : fetch_word ASEGS_I (0x87a94 : word) = Some W_87a94.
Proof. vm_refl. Qed.
Lemma D_87a94 : decode_any W_87a94 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a98 : bv 32 := 0x00b6b423.
Lemma F_87a98 : fetch_word ASEGS_I (0x87a98 : word) = Some W_87a98.
Proof. vm_refl. Qed.
Lemma D_87a98 : decode_any W_87a98 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87a9c : bv 32 := 0x01068693.
Lemma F_87a9c : fetch_word ASEGS_I (0x87a9c : word) = Some W_87a9c.
Proof. vm_refl. Qed.
Lemma D_87a9c : decode_any W_87a9c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87aa0 : bv 32 := 0xfec6eae3.
Lemma F_87aa0 : fetch_word ASEGS_I (0x87aa0 : word) = Some W_87aa0.
Proof. vm_refl. Qed.
Lemma D_87aa0 : decode_any W_87aa0 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87aa4 : bv 32 := 0x00008067.
Lemma F_87aa4 : fetch_word ASEGS_I (0x87aa4 : word) = Some W_87aa4.
Proof. vm_refl. Qed.
Lemma D_87aa4 : decode_any W_87aa4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87b9c : bv 32 := 0x00000593.
Lemma F_87b9c : fetch_word ASEGS_I (0x87b9c : word) = Some W_87b9c.
Proof. vm_refl. Qed.
Lemma D_87b9c : decode_any W_87b9c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ba0 : bv 32 := 0x00b50633.
Lemma F_87ba0 : fetch_word ASEGS_I (0x87ba0 : word) = Some W_87ba0.
Proof. vm_refl. Qed.
Lemma D_87ba0 : decode_any W_87ba0 = Some (Op ALU_ADD 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ba4 : bv 32 := 0x00064603.
Lemma F_87ba4 : fetch_word ASEGS_I (0x87ba4 : word) = Some W_87ba4.
Proof. vm_refl. Qed.
Lemma D_87ba4 : decode_any W_87ba4 = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ba8 : bv 32 := 0x00158593.
Lemma F_87ba8 : fetch_word ASEGS_I (0x87ba8 : word) = Some W_87ba8.
Proof. vm_refl. Qed.
Lemma D_87ba8 : decode_any W_87ba8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bac : bv 32 := 0xfe061ae3.
Lemma F_87bac : fetch_word ASEGS_I (0x87bac : word) = Some W_87bac.
Proof. vm_refl. Qed.
Lemma D_87bac : decode_any W_87bac = Some (Branch BC_NE 12 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bb0 : bv 32 := 0xfff58513.
Lemma F_87bb0 : fetch_word ASEGS_I (0x87bb0 : word) = Some W_87bb0.
Proof. vm_refl. Qed.
Lemma D_87bb0 : decode_any W_87bb0 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87bb4 : bv 32 := 0x00008067.
Lemma F_87bb4 : fetch_word ASEGS_I (0x87bb4 : word) = Some W_87bb4.
Proof. vm_refl. Qed.
Lemma D_87bb4 : decode_any W_87bb4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87e74 : bv 32 := 0x06060663.
Lemma F_87e74 : fetch_word ASEGS_I (0x87e74 : word) = Some W_87e74.
Proof. vm_refl. Qed.
Lemma D_87e74 : decode_any W_87e74 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87e78 : bv 32 := 0x00000693.
Lemma F_87e78 : fetch_word ASEGS_I (0x87e78 : word) = Some W_87e78.
Proof. vm_refl. Qed.
Lemma D_87e78 : decode_any W_87e78 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87e7c : bv 32 := 0x00d58733.
Lemma F_87e7c : fetch_word ASEGS_I (0x87e7c : word) = Some W_87e7c.
Proof. vm_refl. Qed.
Lemma D_87e7c : decode_any W_87e7c = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87e80 : bv 32 := 0x00074703.
Lemma F_87e80 : fetch_word ASEGS_I (0x87e80 : word) = Some W_87e80.
Proof. vm_refl. Qed.
Lemma D_87e80 : decode_any W_87e80 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87e84 : bv 32 := 0x00070c63.
Lemma F_87e84 : fetch_word ASEGS_I (0x87e84 : word) = Some W_87e84.
Proof. vm_refl. Qed.
Lemma D_87e84 : decode_any W_87e84 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87e88 : bv 32 := 0x00d507b3.
Lemma F_87e88 : fetch_word ASEGS_I (0x87e88 : word) = Some W_87e88.
Proof. vm_refl. Qed.
Lemma D_87e88 : decode_any W_87e88 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87e8c : bv 32 := 0x00168693.
Lemma F_87e8c : fetch_word ASEGS_I (0x87e8c : word) = Some W_87e8c.
Proof. vm_refl. Qed.
Lemma D_87e8c : decode_any W_87e8c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87e90 : bv 32 := 0x00e78023.
Lemma F_87e90 : fetch_word ASEGS_I (0x87e90 : word) = Some W_87e90.
Proof. vm_refl. Qed.
Lemma D_87e90 : decode_any W_87e90 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87e94 : bv 32 := 0xfed614e3.
Lemma F_87e94 : fetch_word ASEGS_I (0x87e94 : word) = Some W_87e94.
Proof. vm_refl. Qed.
Lemma D_87e94 : decode_any W_87e94 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87e98 : bv 32 := 0x00060693.
Lemma F_87e98 : fetch_word ASEGS_I (0x87e98 : word) = Some W_87e98.
Proof. vm_refl. Qed.
Lemma D_87e98 : decode_any W_87e98 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87e9c : bv 32 := 0x00d505b3.
Lemma F_87e9c : fetch_word ASEGS_I (0x87e9c : word) = Some W_87e9c.
Proof. vm_refl. Qed.
Lemma D_87e9c : decode_any W_87e9c = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ea0 : bv 32 := 0x40d6073b.
Lemma F_87ea0 : fetch_word ASEGS_I (0x87ea0 : word) = Some W_87ea0.
Proof. vm_refl. Qed.
Lemma D_87ea0 : decode_any W_87ea0 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ea4 : bv 32 := 0x00b76733.
Lemma F_87ea4 : fetch_word ASEGS_I (0x87ea4 : word) = Some W_87ea4.
Proof. vm_refl. Qed.
Lemma D_87ea4 : decode_any W_87ea4 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ea8 : bv 32 := 0x00f77713.
Lemma F_87ea8 : fetch_word ASEGS_I (0x87ea8 : word) = Some W_87ea8.
Proof. vm_refl. Qed.
Lemma D_87ea8 : decode_any W_87ea8 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87eac : bv 32 := 0x00070e63.
Lemma F_87eac : fetch_word ASEGS_I (0x87eac : word) = Some W_87eac.
Proof. vm_refl. Qed.
Lemma D_87eac : decode_any W_87eac = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87eb0 : bv 32 := 0x02d60863.
Lemma F_87eb0 : fetch_word ASEGS_I (0x87eb0 : word) = Some W_87eb0.
Proof. vm_refl. Qed.
Lemma D_87eb0 : decode_any W_87eb0 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87eb4 : bv 32 := 0x00c50633.
Lemma F_87eb4 : fetch_word ASEGS_I (0x87eb4 : word) = Some W_87eb4.
Proof. vm_refl. Qed.
Lemma D_87eb4 : decode_any W_87eb4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87eb8 : bv 32 := 0x00058023.
Lemma F_87eb8 : fetch_word ASEGS_I (0x87eb8 : word) = Some W_87eb8.
Proof. vm_refl. Qed.
Lemma D_87eb8 : decode_any W_87eb8 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ebc : bv 32 := 0x00158593.
Lemma F_87ebc : fetch_word ASEGS_I (0x87ebc : word) = Some W_87ebc.
Proof. vm_refl. Qed.
Lemma D_87ebc : decode_any W_87ebc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ec0 : bv 32 := 0xfec59ce3.
Lemma F_87ec0 : fetch_word ASEGS_I (0x87ec0 : word) = Some W_87ec0.
Proof. vm_refl. Qed.
Lemma D_87ec0 : decode_any W_87ec0 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ec4 : bv 32 := 0x01c0006f.
Lemma F_87ec4 : fetch_word ASEGS_I (0x87ec4 : word) = Some W_87ec4.
Proof. vm_refl. Qed.
Lemma D_87ec4 : decode_any W_87ec4 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ec8 : bv 32 := 0x00d60c63.
Lemma F_87ec8 : fetch_word ASEGS_I (0x87ec8 : word) = Some W_87ec8.
Proof. vm_refl. Qed.
Lemma D_87ec8 : decode_any W_87ec8 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ecc : bv 32 := 0x00c50633.
Lemma F_87ecc : fetch_word ASEGS_I (0x87ecc : word) = Some W_87ecc.
Proof. vm_refl. Qed.
Lemma D_87ecc : decode_any W_87ecc = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ed0 : bv 32 := 0x0005b023.
Lemma F_87ed0 : fetch_word ASEGS_I (0x87ed0 : word) = Some W_87ed0.
Proof. vm_refl. Qed.
Lemma D_87ed0 : decode_any W_87ed0 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ed4 : bv 32 := 0x0005b423.
Lemma F_87ed4 : fetch_word ASEGS_I (0x87ed4 : word) = Some W_87ed4.
Proof. vm_refl. Qed.
Lemma D_87ed4 : decode_any W_87ed4 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ed8 : bv 32 := 0x01058593.
Lemma F_87ed8 : fetch_word ASEGS_I (0x87ed8 : word) = Some W_87ed8.
Proof. vm_refl. Qed.
Lemma D_87ed8 : decode_any W_87ed8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87edc : bv 32 := 0xfec5eae3.
Lemma F_87edc : fetch_word ASEGS_I (0x87edc : word) = Some W_87edc.
Proof. vm_refl. Qed.
Lemma D_87edc : decode_any W_87edc = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ee0 : bv 32 := 0x00008067.
Lemma F_87ee0 : fetch_word ASEGS_I (0x87ee0 : word) = Some W_87ee0.
Proof. vm_refl. Qed.
Lemma D_87ee0 : decode_any W_87ee0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87f94 : bv 32 := 0xff010113.
Lemma F_87f94 : fetch_word ASEGS_I (0x87f94 : word) = Some W_87f94.
Proof. vm_refl. Qed.
Lemma D_87f94 : decode_any W_87f94 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87f98 : bv 32 := 0x00113423.
Lemma F_87f98 : fetch_word ASEGS_I (0x87f98 : word) = Some W_87f98.
Proof. vm_refl. Qed.
Lemma D_87f98 : decode_any W_87f98 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87f9c : bv 32 := 0x00058693.
Lemma F_87f9c : fetch_word ASEGS_I (0x87f9c : word) = Some W_87f9c.
Proof. vm_refl. Qed.
Lemma D_87f9c : decode_any W_87f9c = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fa0 : bv 32 := 0x00100713.
Lemma F_87fa0 : fetch_word ASEGS_I (0x87fa0 : word) = Some W_87fa0.
Proof. vm_refl. Qed.
Lemma D_87fa0 : decode_any W_87fa0 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fa4 : bv 32 := 0x02871713.
Lemma F_87fa4 : fetch_word ASEGS_I (0x87fa4 : word) = Some W_87fa4.
Proof. vm_refl. Qed.
Lemma D_87fa4 : decode_any W_87fa4 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fa8 : bv 32 := 0x00170593.
Lemma F_87fa8 : fetch_word ASEGS_I (0x87fa8 : word) = Some W_87fa8.
Proof. vm_refl. Qed.
Lemma D_87fa8 : decode_any W_87fa8 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fac : bv 32 := 0x08b6f263.
Lemma F_87fac : fetch_word ASEGS_I (0x87fac : word) = Some W_87fac.
Proof. vm_refl. Qed.
Lemma D_87fac : decode_any W_87fac = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fb0 : bv 32 := 0x00000593.
Lemma F_87fb0 : fetch_word ASEGS_I (0x87fb0 : word) = Some W_87fb0.
Proof. vm_refl. Qed.
Lemma D_87fb0 : decode_any W_87fb0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fb4 : bv 32 := 0x00d50733.
Lemma F_87fb4 : fetch_word ASEGS_I (0x87fb4 : word) = Some W_87fb4.
Proof. vm_refl. Qed.
Lemma D_87fb4 : decode_any W_87fb4 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fb8 : bv 32 := 0x00750793.
Lemma F_87fb8 : fetch_word ASEGS_I (0x87fb8 : word) = Some W_87fb8.
Proof. vm_refl. Qed.
Lemma D_87fb8 : decode_any W_87fb8 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fbc : bv 32 := 0xff87f793.
Lemma F_87fbc : fetch_word ASEGS_I (0x87fbc : word) = Some W_87fbc.
Proof. vm_refl. Qed.
Lemma D_87fbc : decode_any W_87fbc = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fc0 : bv 32 := 0xff877613.
Lemma F_87fc0 : fetch_word ASEGS_I (0x87fc0 : word) = Some W_87fc0.
Proof. vm_refl. Qed.
Lemma D_87fc0 : decode_any W_87fc0 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fc4 : bv 32 := 0x02f57463.
Lemma F_87fc4 : fetch_word ASEGS_I (0x87fc4 : word) = Some W_87fc4.
Proof. vm_refl. Qed.
Lemma D_87fc4 : decode_any W_87fc4 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fc8 : bv 32 := 0x02068263.
Lemma F_87fc8 : fetch_word ASEGS_I (0x87fc8 : word) = Some W_87fc8.
Proof. vm_refl. Qed.
Lemma D_87fc8 : decode_any W_87fc8 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fcc : bv 32 := 0x00000593.
Lemma F_87fcc : fetch_word ASEGS_I (0x87fcc : word) = Some W_87fcc.
Proof. vm_refl. Qed.
Lemma D_87fcc : decode_any W_87fcc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fd0 : bv 32 := 0x00150693.
Lemma F_87fd0 : fetch_word ASEGS_I (0x87fd0 : word) = Some W_87fd0.
Proof. vm_refl. Qed.
Lemma D_87fd0 : decode_any W_87fd0 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fd4 : bv 32 := 0x00068813.
Lemma F_87fd4 : fetch_word ASEGS_I (0x87fd4 : word) = Some W_87fd4.
Proof. vm_refl. Qed.
Lemma D_87fd4 : decode_any W_87fd4 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fd8 : bv 32 := 0xfff6c683.
Lemma F_87fd8 : fetch_word ASEGS_I (0x87fd8 : word) = Some W_87fd8.
Proof. vm_refl. Qed.
Lemma D_87fd8 : decode_any W_87fd8 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fdc : bv 32 := 0x00d5e5b3.
Lemma F_87fdc : fetch_word ASEGS_I (0x87fdc : word) = Some W_87fdc.
Proof. vm_refl. Qed.
Lemma D_87fdc : decode_any W_87fdc = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fe0 : bv 32 := 0x00f87663.
Lemma F_87fe0 : fetch_word ASEGS_I (0x87fe0 : word) = Some W_87fe0.
Proof. vm_refl. Qed.
Lemma D_87fe0 : decode_any W_87fe0 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fe4 : bv 32 := 0x00180693.
Lemma F_87fe4 : fetch_word ASEGS_I (0x87fe4 : word) = Some W_87fe4.
Proof. vm_refl. Qed.
Lemma D_87fe4 : decode_any W_87fe4 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fe8 : bv 32 := 0xfee866e3.
Lemma F_87fe8 : fetch_word ASEGS_I (0x87fe8 : word) = Some W_87fe8.
Proof. vm_refl. Qed.
Lemma D_87fe8 : decode_any W_87fe8 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87fec : bv 32 := 0x00c7fa63.
Lemma F_87fec : fetch_word ASEGS_I (0x87fec : word) = Some W_87fec.
Proof. vm_refl. Qed.
Lemma D_87fec : decode_any W_87fec = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ff0 : bv 32 := 0x0007b683.
Lemma F_87ff0 : fetch_word ASEGS_I (0x87ff0 : word) = Some W_87ff0.
Proof. vm_refl. Qed.
Lemma D_87ff0 : decode_any W_87ff0 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ff4 : bv 32 := 0x00878793.
Lemma F_87ff4 : fetch_word ASEGS_I (0x87ff4 : word) = Some W_87ff4.
Proof. vm_refl. Qed.
Lemma D_87ff4 : decode_any W_87ff4 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ff8 : bv 32 := 0x00b6e5b3.
Lemma F_87ff8 : fetch_word ASEGS_I (0x87ff8 : word) = Some W_87ff8.
Proof. vm_refl. Qed.
Lemma D_87ff8 : decode_any W_87ff8 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ffc : bv 32 := 0xfec7eae3.
Lemma F_87ffc : fetch_word ASEGS_I (0x87ffc : word) = Some W_87ffc.
Proof. vm_refl. Qed.
Lemma D_87ffc : decode_any W_87ffc = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88000 : bv 32 := 0x02a66063.
Lemma F_88000 : fetch_word ASEGS_I (0x88000 : word) = Some W_88000.
Proof. vm_refl. Qed.
Lemma D_88000 : decode_any W_88000 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88004 : bv 32 := 0x00e67e63.
Lemma F_88004 : fetch_word ASEGS_I (0x88004 : word) = Some W_88004.
Proof. vm_refl. Qed.
Lemma D_88004 : decode_any W_88004 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88008 : bv 32 := 0x40c70733.
Lemma F_88008 : fetch_word ASEGS_I (0x88008 : word) = Some W_88008.
Proof. vm_refl. Qed.
Lemma D_88008 : decode_any W_88008 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8800c : bv 32 := 0x00064503.
Lemma F_8800c : fetch_word ASEGS_I (0x8800c : word) = Some W_8800c.
Proof. vm_refl. Qed.
Lemma D_8800c : decode_any W_8800c = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88010 : bv 32 := 0xfff70713.
Lemma F_88010 : fetch_word ASEGS_I (0x88010 : word) = Some W_88010.
Proof. vm_refl. Qed.
Lemma D_88010 : decode_any W_88010 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88014 : bv 32 := 0x00a5e5b3.
Lemma F_88014 : fetch_word ASEGS_I (0x88014 : word) = Some W_88014.
Proof. vm_refl. Qed.
Lemma D_88014 : decode_any W_88014 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88018 : bv 32 := 0x00160613.
Lemma F_88018 : fetch_word ASEGS_I (0x88018 : word) = Some W_88018.
Proof. vm_refl. Qed.
Lemma D_88018 : decode_any W_88018 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8801c : bv 32 := 0xfe0718e3.
Lemma F_8801c : fetch_word ASEGS_I (0x8801c : word) = Some W_8801c.
Proof. vm_refl. Qed.
Lemma D_8801c : decode_any W_8801c = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88020 : bv 32 := 0x0015b513.
Lemma F_88020 : fetch_word ASEGS_I (0x88020 : word) = Some W_88020.
Proof. vm_refl. Qed.
Lemma D_88020 : decode_any W_88020 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88024 : bv 32 := 0x00813083.
Lemma F_88024 : fetch_word ASEGS_I (0x88024 : word) = Some W_88024.
Proof. vm_refl. Qed.
Lemma D_88024 : decode_any W_88024 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88028 : bv 32 := 0x01010113.
Lemma F_88028 : fetch_word ASEGS_I (0x88028 : word) = Some W_88028.
Proof. vm_refl. Qed.
Lemma D_88028 : decode_any W_88028 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8802c : bv 32 := 0x00008067.
Lemma F_8802c : fetch_word ASEGS_I (0x8802c : word) = Some W_8802c.
Proof. vm_refl. Qed.
Lemma D_8802c : decode_any W_8802c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

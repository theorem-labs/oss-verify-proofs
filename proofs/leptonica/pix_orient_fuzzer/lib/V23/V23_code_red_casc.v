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

Definition W_a6c38 : bv 32 := 0xfa010113.
Lemma F_a6c38 : fetch_word Ubsan.M.loaded_segments (0xa6c38 : word) = Some W_a6c38.
Proof. vm_refl. Qed.
Lemma D_a6c38 : decode_any W_a6c38 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6c3c : bv 32 := 0x04113c23.
Lemma F_a6c3c : fetch_word Ubsan.M.loaded_segments (0xa6c3c : word) = Some W_a6c3c.
Proof. vm_refl. Qed.
Lemma D_a6c3c : decode_any W_a6c3c = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6c40 : bv 32 := 0x04813823.
Lemma F_a6c40 : fetch_word Ubsan.M.loaded_segments (0xa6c40 : word) = Some W_a6c40.
Proof. vm_refl. Qed.
Lemma D_a6c40 : decode_any W_a6c40 = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6c44 : bv 32 := 0x04913423.
Lemma F_a6c44 : fetch_word Ubsan.M.loaded_segments (0xa6c44 : word) = Some W_a6c44.
Proof. vm_refl. Qed.
Lemma D_a6c44 : decode_any W_a6c44 = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6c48 : bv 32 := 0x05213023.
Lemma F_a6c48 : fetch_word Ubsan.M.loaded_segments (0xa6c48 : word) = Some W_a6c48.
Proof. vm_refl. Qed.
Lemma D_a6c48 : decode_any W_a6c48 = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6c4c : bv 32 := 0x03313c23.
Lemma F_a6c4c : fetch_word Ubsan.M.loaded_segments (0xa6c4c : word) = Some W_a6c4c.
Proof. vm_refl. Qed.
Lemma D_a6c4c : decode_any W_a6c4c = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6c50 : bv 32 := 0x03413823.
Lemma F_a6c50 : fetch_word Ubsan.M.loaded_segments (0xa6c50 : word) = Some W_a6c50.
Proof. vm_refl. Qed.
Lemma D_a6c50 : decode_any W_a6c50 = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6c54 : bv 32 := 0x03513423.
Lemma F_a6c54 : fetch_word Ubsan.M.loaded_segments (0xa6c54 : word) = Some W_a6c54.
Proof. vm_refl. Qed.
Lemma D_a6c54 : decode_any W_a6c54 = Some (Store SZ8 2 21 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6c58 : bv 32 := 0x03613023.
Lemma F_a6c58 : fetch_word Ubsan.M.loaded_segments (0xa6c58 : word) = Some W_a6c58.
Proof. vm_refl. Qed.
Lemma D_a6c58 : decode_any W_a6c58 = Some (Store SZ8 2 22 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6c5c : bv 32 := 0x16050463.
Lemma F_a6c5c : fetch_word Ubsan.M.loaded_segments (0xa6c5c : word) = Some W_a6c5c.
Proof. vm_refl. Qed.
Lemma D_a6c5c : decode_any W_a6c5c = Some (Branch BC_EQ 10 0 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6c60 : bv 32 := 0x00070413.
Lemma F_a6c60 : fetch_word Ubsan.M.loaded_segments (0xa6c60 : word) = Some W_a6c60.
Proof. vm_refl. Qed.
Lemma D_a6c60 : decode_any W_a6c60 = Some (OpImm ALU_ADD 8 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6c64 : bv 32 := 0x00068493.
Lemma F_a6c64 : fetch_word Ubsan.M.loaded_segments (0xa6c64 : word) = Some W_a6c64.
Proof. vm_refl. Qed.
Lemma D_a6c64 : decode_any W_a6c64 = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6c68 : bv 32 := 0x00060993.
Lemma F_a6c68 : fetch_word Ubsan.M.loaded_segments (0xa6c68 : word) = Some W_a6c68.
Proof. vm_refl. Qed.
Lemma D_a6c68 : decode_any W_a6c68 = Some (OpImm ALU_ADD 19 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6c6c : bv 32 := 0x00058a13.
Lemma F_a6c6c : fetch_word Ubsan.M.loaded_segments (0xa6c6c : word) = Some W_a6c6c.
Proof. vm_refl. Qed.
Lemma D_a6c6c : decode_any W_a6c6c = Some (OpImm ALU_ADD 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6c70 : bv 32 := 0x00050a93.
Lemma F_a6c70 : fetch_word Ubsan.M.loaded_segments (0xa6c70 : word) = Some W_a6c70.
Proof. vm_refl. Qed.
Lemma D_a6c70 : decode_any W_a6c70 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6c74 : bv 32 := 0xca0c80ef.
Lemma F_a6c74 : fetch_word Ubsan.M.loaded_segments (0xa6c74 : word) = Some W_a6c74.
Proof. vm_refl. Qed.
Lemma D_a6c74 : decode_any W_a6c74 = Some (Jal 1 1868960, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6c78 : bv 32 := 0x00100593.
Lemma F_a6c78 : fetch_word Ubsan.M.loaded_segments (0xa6c78 : word) = Some W_a6c78.
Proof. vm_refl. Qed.
Lemma D_a6c78 : decode_any W_a6c78 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6c7c : bv 32 := 0x16b51863.
Lemma F_a6c7c : fetch_word Ubsan.M.loaded_segments (0xa6c7c : word) = Some W_a6c7c.
Proof. vm_refl. Qed.
Lemma D_a6c7c : decode_any W_a6c7c = Some (Branch BC_NE 10 11 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6c80 : bv 32 := 0x00400513.
Lemma F_a6c80 : fetch_word Ubsan.M.loaded_segments (0xa6c80 : word) = Some W_a6c80.
Proof. vm_refl. Qed.
Lemma D_a6c80 : decode_any W_a6c80 = Some (OpImm ALU_ADD 10 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6c84 : bv 32 := 0x19454863.
Lemma F_a6c84 : fetch_word Ubsan.M.loaded_segments (0xa6c84 : word) = Some W_a6c84.
Proof. vm_refl. Qed.
Lemma D_a6c84 : decode_any W_a6c84 = Some (Branch BC_LT 10 20 400, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6c88 : bv 32 := 0x19354663.
Lemma F_a6c88 : fetch_word Ubsan.M.loaded_segments (0xa6c88 : word) = Some W_a6c88.
Proof. vm_refl. Qed.
Lemma D_a6c88 : decode_any W_a6c88 = Some (Branch BC_LT 10 19 396, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6c8c : bv 32 := 0x00400513.
Lemma F_a6c8c : fetch_word Ubsan.M.loaded_segments (0xa6c8c : word) = Some W_a6c8c.
Proof. vm_refl. Qed.
Lemma D_a6c8c : decode_any W_a6c8c = Some (OpImm ALU_ADD 10 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6c90 : bv 32 := 0x18954263.
Lemma F_a6c90 : fetch_word Ubsan.M.loaded_segments (0xa6c90 : word) = Some W_a6c90.
Proof. vm_refl. Qed.
Lemma D_a6c90 : decode_any W_a6c90 = Some (Branch BC_LT 10 9 388, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6c94 : bv 32 := 0x00500513.
Lemma F_a6c94 : fetch_word Ubsan.M.loaded_segments (0xa6c94 : word) = Some W_a6c94.
Proof. vm_refl. Qed.
Lemma D_a6c94 : decode_any W_a6c94 = Some (OpImm ALU_ADD 10 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6c98 : bv 32 := 0x16a45e63.
Lemma F_a6c98 : fetch_word Ubsan.M.loaded_segments (0xa6c98 : word) = Some W_a6c98.
Proof. vm_refl. Qed.
Lemma D_a6c98 : decode_any W_a6c98 = Some (Branch BC_GE 8 10 380, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6c9c : bv 32 := 0x1f405a63.
Lemma F_a6c9c : fetch_word Ubsan.M.loaded_segments (0xa6c9c : word) = Some W_a6c9c.
Proof. vm_refl. Qed.
Lemma D_a6c9c : decode_any W_a6c9c = Some (Branch BC_GE 0 20 500, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6ca0 : bv 32 := 0x10000513.
Lemma F_a6ca0 : fetch_word Ubsan.M.loaded_segments (0xa6ca0 : word) = Some W_a6ca0.
Proof. vm_refl. Qed.
Lemma D_a6ca0 : decode_any W_a6ca0 = Some (OpImm ALU_ADD 10 0 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6ca4 : bv 32 := 0x00100593.
Lemma F_a6ca4 : fetch_word Ubsan.M.loaded_segments (0xa6ca4 : word) = Some W_a6ca4.
Proof. vm_refl. Qed.
Lemma D_a6ca4 : decode_any W_a6ca4 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6ca8 : bv 32 := 0x10000b13.
Lemma F_a6ca8 : fetch_word Ubsan.M.loaded_segments (0xa6ca8 : word) = Some W_a6ca8.
Proof. vm_refl. Qed.
Lemma D_a6ca8 : decode_any W_a6ca8 = Some (OpImm ALU_ADD 22 0 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6cac : bv 32 := 0x235670ef.
Lemma F_a6cac : fetch_word Ubsan.M.loaded_segments (0xa6cac : word) = Some W_a6cac.
Proof. vm_refl. Qed.
Lemma D_a6cac : decode_any W_a6cac = Some (Jal 1 424500, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6cb0 : bv 32 := 0x00050913.
Lemma F_a6cb0 : fetch_word Ubsan.M.loaded_segments (0xa6cb0 : word) = Some W_a6cb0.
Proof. vm_refl. Qed.
Lemma D_a6cb0 : decode_any W_a6cb0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6cb4 : bv 32 := 0x00000593.
Lemma F_a6cb4 : fetch_word Ubsan.M.loaded_segments (0xa6cb4 : word) = Some W_a6cb4.
Proof. vm_refl. Qed.
Lemma D_a6cb4 : decode_any W_a6cb4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6cb8 : bv 32 := 0x00000613.
Lemma F_a6cb8 : fetch_word Ubsan.M.loaded_segments (0xa6cb8 : word) = Some W_a6cb8.
Proof. vm_refl. Qed.
Lemma D_a6cb8 : decode_any W_a6cb8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6cbc : bv 32 := 0x00000693.
Lemma F_a6cbc : fetch_word Ubsan.M.loaded_segments (0xa6cbc : word) = Some W_a6cbc.
Proof. vm_refl. Qed.
Lemma D_a6cbc : decode_any W_a6cbc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6cc0 : bv 32 := 0x00000713.
Lemma F_a6cc0 : fetch_word Ubsan.M.loaded_segments (0xa6cc0 : word) = Some W_a6cc0.
Proof. vm_refl. Qed.
Lemma D_a6cc0 : decode_any W_a6cc0 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6cc4 : bv 32 := 0x00a037b3.
Lemma F_a6cc4 : fetch_word Ubsan.M.loaded_segments (0xa6cc4 : word) = Some W_a6cc4.
Proof. vm_refl. Qed.
Lemma D_a6cc4 : decode_any W_a6cc4 = Some (Op ALU_SLTU 15 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6cc8 : bv 32 := 0x00050813.
Lemma F_a6cc8 : fetch_word Ubsan.M.loaded_segments (0xa6cc8 : word) = Some W_a6cc8.
Proof. vm_refl. Qed.
Lemma D_a6cc8 : decode_any W_a6cc8 = Some (OpImm ALU_ADD 16 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6ccc : bv 32 := 0x00050893.
Lemma F_a6ccc : fetch_word Ubsan.M.loaded_segments (0xa6ccc : word) = Some W_a6ccc.
Proof. vm_refl. Qed.
Lemma D_a6ccc : decode_any W_a6ccc = Some (OpImm ALU_ADD 17 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6cd0 : bv 32 := 0x2528e663.
Lemma F_a6cd0 : fetch_word Ubsan.M.loaded_segments (0xa6cd0 : word) = Some W_a6cd0.
Proof. vm_refl. Qed.
Lemma D_a6cd0 : decode_any W_a6cd0 = Some (Branch BC_LTU 17 18 588, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6cd4 : bv 32 := 0x0018b293.
Lemma F_a6cd4 : fetch_word Ubsan.M.loaded_segments (0xa6cd4 : word) = Some W_a6cd4.
Proof. vm_refl. Qed.
Lemma D_a6cd4 : decode_any W_a6cd4 = Some (OpImm ALU_SLTU 5 17 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6cd8 : bv 32 := 0x0057c2b3.
Lemma F_a6cd8 : fetch_word Ubsan.M.loaded_segments (0xa6cd8 : word) = Some W_a6cd8.
Proof. vm_refl. Qed.
Lemma D_a6cd8 : decode_any W_a6cd8 = Some (Op ALU_XOR 5 15 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6cdc : bv 32 := 0x24028063.
Lemma F_a6cdc : fetch_word Ubsan.M.loaded_segments (0xa6cdc : word) = Some W_a6cdc.
Proof. vm_refl. Qed.
Lemma D_a6cdc : decode_any W_a6cdc = Some (Branch BC_EQ 5 0 576, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6ce0 : bv 32 := 0x22090e63.
Lemma F_a6ce0 : fetch_word Ubsan.M.loaded_segments (0xa6ce0 : word) = Some W_a6ce0.
Proof. vm_refl. Qed.
Lemma D_a6ce0 : decode_any W_a6ce0 = Some (Branch BC_EQ 18 0 572, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6ce4 : bv 32 := 0x0015d293.
Lemma F_a6ce4 : fetch_word Ubsan.M.loaded_segments (0xa6ce4 : word) = Some W_a6ce4.
Proof. vm_refl. Qed.
Lemma D_a6ce4 : decode_any W_a6ce4 = Some (ShiftImm ALU_SRL 5 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6ce8 : bv 32 := 0x0025d313.
Lemma F_a6ce8 : fetch_word Ubsan.M.loaded_segments (0xa6ce8 : word) = Some W_a6ce8.
Proof. vm_refl. Qed.
Lemma D_a6ce8 : decode_any W_a6ce8 = Some (ShiftImm ALU_SRL 6 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6cec : bv 32 := 0x0035d393.
Lemma F_a6cec : fetch_word Ubsan.M.loaded_segments (0xa6cec : word) = Some W_a6cec.
Proof. vm_refl. Qed.
Lemma D_a6cec : decode_any W_a6cec = Some (ShiftImm ALU_SRL 7 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6cf0 : bv 32 := 0x01067e13.
Lemma F_a6cf0 : fetch_word Ubsan.M.loaded_segments (0xa6cf0 : word) = Some W_a6cf0.
Proof. vm_refl. Qed.
Lemma D_a6cf0 : decode_any W_a6cf0 = Some (OpImm ALU_AND 28 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6cf4 : bv 32 := 0x0206fe93.
Lemma F_a6cf4 : fetch_word Ubsan.M.loaded_segments (0xa6cf4 : word) = Some W_a6cf4.
Proof. vm_refl. Qed.
Lemma D_a6cf4 : decode_any W_a6cf4 = Some (OpImm ALU_AND 29 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6cf8 : bv 32 := 0x04077f13.
Lemma F_a6cf8 : fetch_word Ubsan.M.loaded_segments (0xa6cf8 : word) = Some W_a6cf8.
Proof. vm_refl. Qed.
Lemma D_a6cf8 : decode_any W_a6cf8 = Some (OpImm ALU_AND 30 14 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6cfc : bv 32 := 0x0815ff93.
Lemma F_a6cfc : fetch_word Ubsan.M.loaded_segments (0xa6cfc : word) = Some W_a6cfc.
Proof. vm_refl. Qed.
Lemma D_a6cfc : decode_any W_a6cfc = Some (OpImm ALU_AND 31 11 129, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d00 : bv 32 := 0xfffb0b13.
Lemma F_a6d00 : fetch_word Ubsan.M.loaded_segments (0xa6d00 : word) = Some W_a6d00.
Proof. vm_refl. Qed.
Lemma D_a6d00 : decode_any W_a6d00 = Some (OpImm ALU_ADD 22 22 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d04 : bv 32 := 0x00188893.
Lemma F_a6d04 : fetch_word Ubsan.M.loaded_segments (0xa6d04 : word) = Some W_a6d04.
Proof. vm_refl. Qed.
Lemma D_a6d04 : decode_any W_a6d04 = Some (OpImm ALU_ADD 17 17 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d08 : bv 32 := 0x00270713.
Lemma F_a6d08 : fetch_word Ubsan.M.loaded_segments (0xa6d08 : word) = Some W_a6d08.
Proof. vm_refl. Qed.
Lemma D_a6d08 : decode_any W_a6d08 = Some (OpImm ALU_ADD 14 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d0c : bv 32 := 0x00468693.
Lemma F_a6d0c : fetch_word Ubsan.M.loaded_segments (0xa6d0c : word) = Some W_a6d0c.
Proof. vm_refl. Qed.
Lemma D_a6d0c : decode_any W_a6d0c = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d10 : bv 32 := 0x00860613.
Lemma F_a6d10 : fetch_word Ubsan.M.loaded_segments (0xa6d10 : word) = Some W_a6d10.
Proof. vm_refl. Qed.
Lemma D_a6d10 : decode_any W_a6d10 = Some (OpImm ALU_ADD 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d14 : bv 32 := 0x0022f293.
Lemma F_a6d14 : fetch_word Ubsan.M.loaded_segments (0xa6d14 : word) = Some W_a6d14.
Proof. vm_refl. Qed.
Lemma D_a6d14 : decode_any W_a6d14 = Some (OpImm ALU_AND 5 5 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d18 : bv 32 := 0x00437313.
Lemma F_a6d18 : fetch_word Ubsan.M.loaded_segments (0xa6d18 : word) = Some W_a6d18.
Proof. vm_refl. Qed.
Lemma D_a6d18 : decode_any W_a6d18 = Some (OpImm ALU_AND 6 6 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d1c : bv 32 := 0x0083f393.
Lemma F_a6d1c : fetch_word Ubsan.M.loaded_segments (0xa6d1c : word) = Some W_a6d1c.
Proof. vm_refl. Qed.
Lemma D_a6d1c : decode_any W_a6d1c = Some (OpImm ALU_AND 7 7 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d20 : bv 32 := 0x01de6e33.
Lemma F_a6d20 : fetch_word Ubsan.M.loaded_segments (0xa6d20 : word) = Some W_a6d20.
Proof. vm_refl. Qed.
Lemma D_a6d20 : decode_any W_a6d20 = Some (Op ALU_OR 28 28 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d24 : bv 32 := 0x01f2e2b3.
Lemma F_a6d24 : fetch_word Ubsan.M.loaded_segments (0xa6d24 : word) = Some W_a6d24.
Proof. vm_refl. Qed.
Lemma D_a6d24 : decode_any W_a6d24 = Some (Op ALU_OR 5 5 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d28 : bv 32 := 0x00736333.
Lemma F_a6d28 : fetch_word Ubsan.M.loaded_segments (0xa6d28 : word) = Some W_a6d28.
Proof. vm_refl. Qed.
Lemma D_a6d28 : decode_any W_a6d28 = Some (Op ALU_OR 6 6 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d2c : bv 32 := 0x01ee63b3.
Lemma F_a6d2c : fetch_word Ubsan.M.loaded_segments (0xa6d2c : word) = Some W_a6d2c.
Proof. vm_refl. Qed.
Lemma D_a6d2c : decode_any W_a6d2c = Some (Op ALU_OR 7 28 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d30 : bv 32 := 0x0062e2b3.
Lemma F_a6d30 : fetch_word Ubsan.M.loaded_segments (0xa6d30 : word) = Some W_a6d30.
Proof. vm_refl. Qed.
Lemma D_a6d30 : decode_any W_a6d30 = Some (Op ALU_OR 5 5 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d34 : bv 32 := 0x0072e2b3.
Lemma F_a6d34 : fetch_word Ubsan.M.loaded_segments (0xa6d34 : word) = Some W_a6d34.
Proof. vm_refl. Qed.
Lemma D_a6d34 : decode_any W_a6d34 = Some (Op ALU_OR 5 5 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d38 : bv 32 := 0x00580023.
Lemma F_a6d38 : fetch_word Ubsan.M.loaded_segments (0xa6d38 : word) = Some W_a6d38.
Proof. vm_refl. Qed.
Lemma D_a6d38 : decode_any W_a6d38 = Some (Store SZ1 16 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d3c : bv 32 := 0x00180813.
Lemma F_a6d3c : fetch_word Ubsan.M.loaded_segments (0xa6d3c : word) = Some W_a6d3c.
Proof. vm_refl. Qed.
Lemma D_a6d3c : decode_any W_a6d3c = Some (OpImm ALU_ADD 16 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d40 : bv 32 := 0x00158593.
Lemma F_a6d40 : fetch_word Ubsan.M.loaded_segments (0xa6d40 : word) = Some W_a6d40.
Proof. vm_refl. Qed.
Lemma D_a6d40 : decode_any W_a6d40 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d44 : bv 32 := 0xf80b16e3.
Lemma F_a6d44 : fetch_word Ubsan.M.loaded_segments (0xa6d44 : word) = Some W_a6d44.
Proof. vm_refl. Qed.
Lemma D_a6d44 : decode_any W_a6d44 = Some (Branch BC_NE 22 0 8076, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d48 : bv 32 := 0x000a8513.
Lemma F_a6d48 : fetch_word Ubsan.M.loaded_segments (0xa6d48 : word) = Some W_a6d48.
Proof. vm_refl. Qed.
Lemma D_a6d48 : decode_any W_a6d48 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d4c : bv 32 := 0x000a0593.
Lemma F_a6d4c : fetch_word Ubsan.M.loaded_segments (0xa6d4c : word) = Some W_a6d4c.
Proof. vm_refl. Qed.
Lemma D_a6d4c : decode_any W_a6d4c = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d50 : bv 32 := 0x00090613.
Lemma F_a6d50 : fetch_word Ubsan.M.loaded_segments (0xa6d50 : word) = Some W_a6d50.
Proof. vm_refl. Qed.
Lemma D_a6d50 : decode_any W_a6d50 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d54 : bv 32 := 0x1cc000ef.
Lemma F_a6d54 : fetch_word Ubsan.M.loaded_segments (0xa6d54 : word) = Some W_a6d54.
Proof. vm_refl. Qed.
Lemma D_a6d54 : decode_any W_a6d54 = Some (Jal 1 460, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d58 : bv 32 := 0x00a13c23.
Lemma F_a6d58 : fetch_word Ubsan.M.loaded_segments (0xa6d58 : word) = Some W_a6d58.
Proof. vm_refl. Qed.
Lemma D_a6d58 : decode_any W_a6d58 = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d5c : bv 32 := 0x19305663.
Lemma F_a6d5c : fetch_word Ubsan.M.loaded_segments (0xa6d5c : word) = Some W_a6d5c.
Proof. vm_refl. Qed.
Lemma D_a6d5c : decode_any W_a6d5c = Some (Branch BC_GE 0 19 396, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d60 : bv 32 := 0x00098593.
Lemma F_a6d60 : fetch_word Ubsan.M.loaded_segments (0xa6d60 : word) = Some W_a6d60.
Proof. vm_refl. Qed.
Lemma D_a6d60 : decode_any W_a6d60 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d64 : bv 32 := 0x00090613.
Lemma F_a6d64 : fetch_word Ubsan.M.loaded_segments (0xa6d64 : word) = Some W_a6d64.
Proof. vm_refl. Qed.
Lemma D_a6d64 : decode_any W_a6d64 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d68 : bv 32 := 0x1b8000ef.
Lemma F_a6d68 : fetch_word Ubsan.M.loaded_segments (0xa6d68 : word) = Some W_a6d68.
Proof. vm_refl. Qed.
Lemma D_a6d68 : decode_any W_a6d68 = Some (Jal 1 440, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d6c : bv 32 := 0x00050993.
Lemma F_a6d6c : fetch_word Ubsan.M.loaded_segments (0xa6d6c : word) = Some W_a6d6c.
Proof. vm_refl. Qed.
Lemma D_a6d6c : decode_any W_a6d6c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d70 : bv 32 := 0x00a13823.
Lemma F_a6d70 : fetch_word Ubsan.M.loaded_segments (0xa6d70 : word) = Some W_a6d70.
Proof. vm_refl. Qed.
Lemma D_a6d70 : decode_any W_a6d70 = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d74 : bv 32 := 0x01810513.
Lemma F_a6d74 : fetch_word Ubsan.M.loaded_segments (0xa6d74 : word) = Some W_a6d74.
Proof. vm_refl. Qed.
Lemma D_a6d74 : decode_any W_a6d74 = Some (OpImm ALU_ADD 10 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d78 : bv 32 := 0xa20c70ef.
Lemma F_a6d78 : fetch_word Ubsan.M.loaded_segments (0xa6d78 : word) = Some W_a6d78.
Proof. vm_refl. Qed.
Lemma D_a6d78 : decode_any W_a6d78 = Some (Jal 1 1864224, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d7c : bv 32 := 0x18905063.
Lemma F_a6d7c : fetch_word Ubsan.M.loaded_segments (0xa6d7c : word) = Some W_a6d7c.
Proof. vm_refl. Qed.
Lemma D_a6d7c : decode_any W_a6d7c = Some (Branch BC_GE 0 9 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d80 : bv 32 := 0x00098513.
Lemma F_a6d80 : fetch_word Ubsan.M.loaded_segments (0xa6d80 : word) = Some W_a6d80.
Proof. vm_refl. Qed.
Lemma D_a6d80 : decode_any W_a6d80 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d84 : bv 32 := 0x00048593.
Lemma F_a6d84 : fetch_word Ubsan.M.loaded_segments (0xa6d84 : word) = Some W_a6d84.
Proof. vm_refl. Qed.
Lemma D_a6d84 : decode_any W_a6d84 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d88 : bv 32 := 0x00090613.
Lemma F_a6d88 : fetch_word Ubsan.M.loaded_segments (0xa6d88 : word) = Some W_a6d88.
Proof. vm_refl. Qed.
Lemma D_a6d88 : decode_any W_a6d88 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d8c : bv 32 := 0x194000ef.
Lemma F_a6d8c : fetch_word Ubsan.M.loaded_segments (0xa6d8c : word) = Some W_a6d8c.
Proof. vm_refl. Qed.
Lemma D_a6d8c : decode_any W_a6d8c = Some (Jal 1 404, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d90 : bv 32 := 0x00050493.
Lemma F_a6d90 : fetch_word Ubsan.M.loaded_segments (0xa6d90 : word) = Some W_a6d90.
Proof. vm_refl. Qed.
Lemma D_a6d90 : decode_any W_a6d90 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d94 : bv 32 := 0x00a13423.
Lemma F_a6d94 : fetch_word Ubsan.M.loaded_segments (0xa6d94 : word) = Some W_a6d94.
Proof. vm_refl. Qed.
Lemma D_a6d94 : decode_any W_a6d94 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d98 : bv 32 := 0x01010513.
Lemma F_a6d98 : fetch_word Ubsan.M.loaded_segments (0xa6d98 : word) = Some W_a6d98.
Proof. vm_refl. Qed.
Lemma D_a6d98 : decode_any W_a6d98 = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6d9c : bv 32 := 0x9fcc70ef.
Lemma F_a6d9c : fetch_word Ubsan.M.loaded_segments (0xa6d9c : word) = Some W_a6d9c.
Proof. vm_refl. Qed.
Lemma D_a6d9c : decode_any W_a6d9c = Some (Jal 1 1864188, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6da0 : bv 32 := 0x16805663.
Lemma F_a6da0 : fetch_word Ubsan.M.loaded_segments (0xa6da0 : word) = Some W_a6da0.
Proof. vm_refl. Qed.
Lemma D_a6da0 : decode_any W_a6da0 = Some (Branch BC_GE 0 8 364, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6da4 : bv 32 := 0x00048513.
Lemma F_a6da4 : fetch_word Ubsan.M.loaded_segments (0xa6da4 : word) = Some W_a6da4.
Proof. vm_refl. Qed.
Lemma D_a6da4 : decode_any W_a6da4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6da8 : bv 32 := 0x00040593.
Lemma F_a6da8 : fetch_word Ubsan.M.loaded_segments (0xa6da8 : word) = Some W_a6da8.
Proof. vm_refl. Qed.
Lemma D_a6da8 : decode_any W_a6da8 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6dac : bv 32 := 0x00090613.
Lemma F_a6dac : fetch_word Ubsan.M.loaded_segments (0xa6dac : word) = Some W_a6dac.
Proof. vm_refl. Qed.
Lemma D_a6dac : decode_any W_a6dac = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6db0 : bv 32 := 0x170000ef.
Lemma F_a6db0 : fetch_word Ubsan.M.loaded_segments (0xa6db0 : word) = Some W_a6db0.
Proof. vm_refl. Qed.
Lemma D_a6db0 : decode_any W_a6db0 = Some (Jal 1 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6db4 : bv 32 := 0x00050413.
Lemma F_a6db4 : fetch_word Ubsan.M.loaded_segments (0xa6db4 : word) = Some W_a6db4.
Proof. vm_refl. Qed.
Lemma D_a6db4 : decode_any W_a6db4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6db8 : bv 32 := 0x00810513.
Lemma F_a6db8 : fetch_word Ubsan.M.loaded_segments (0xa6db8 : word) = Some W_a6db8.
Proof. vm_refl. Qed.
Lemma D_a6db8 : decode_any W_a6db8 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6dbc : bv 32 := 0x9dcc70ef.
Lemma F_a6dbc : fetch_word Ubsan.M.loaded_segments (0xa6dbc : word) = Some W_a6dbc.
Proof. vm_refl. Qed.
Lemma D_a6dbc : decode_any W_a6dbc = Some (Jal 1 1864156, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6dc0 : bv 32 := 0x12c0006f.
Lemma F_a6dc0 : fetch_word Ubsan.M.loaded_segments (0xa6dc0 : word) = Some W_a6dc0.
Proof. vm_refl. Qed.
Lemma D_a6dc0 : decode_any W_a6dc0 = Some (Jal 0 300, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6dc4 : bv 32 := 0x00080517.
Lemma F_a6dc4 : fetch_word Ubsan.M.loaded_segments (0xa6dc4 : word) = Some W_a6dc4.
Proof. vm_refl. Qed.
Lemma D_a6dc4 : decode_any W_a6dc4 = Some (Auipc 10 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6dc8 : bv 32 := 0xcac53503.
Lemma F_a6dc8 : fetch_word Ubsan.M.loaded_segments (0xa6dc8 : word) = Some W_a6dc8.
Proof. vm_refl. Qed.
Lemma D_a6dc8 : decode_any W_a6dc8 = Some (Load SZ8 true 10 10 3244, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6dcc : bv 32 := 0x00052503.
Lemma F_a6dcc : fetch_word Ubsan.M.loaded_segments (0xa6dcc : word) = Some W_a6dcc.
Proof. vm_refl. Qed.
Lemma D_a6dcc : decode_any W_a6dcc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6dd0 : bv 32 := 0x00500593.
Lemma F_a6dd0 : fetch_word Ubsan.M.loaded_segments (0xa6dd0 : word) = Some W_a6dd0.
Proof. vm_refl. Qed.
Lemma D_a6dd0 : decode_any W_a6dd0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6dd4 : bv 32 := 0x08a5c863.
Lemma F_a6dd4 : fetch_word Ubsan.M.loaded_segments (0xa6dd4 : word) = Some W_a6dd4.
Proof. vm_refl. Qed.
Lemma D_a6dd4 : decode_any W_a6dd4 = Some (Branch BC_LT 11 10 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6dd8 : bv 32 := 0xfff69517.
Lemma F_a6dd8 : fetch_word Ubsan.M.loaded_segments (0xa6dd8 : word) = Some W_a6dd8.
Proof. vm_refl. Qed.
Lemma D_a6dd8 : decode_any W_a6dd8 = Some (Auipc 10 1048425, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6ddc : bv 32 := 0xfff6f597.
Lemma F_a6ddc : fetch_word Ubsan.M.loaded_segments (0xa6ddc : word) = Some W_a6ddc.
Proof. vm_refl. Qed.
Lemma D_a6ddc : decode_any W_a6ddc = Some (Auipc 11 1048431, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6de0 : bv 32 := 0x57d50513.
Lemma F_a6de0 : fetch_word Ubsan.M.loaded_segments (0xa6de0 : word) = Some W_a6de0.
Proof. vm_refl. Qed.
Lemma D_a6de0 : decode_any W_a6de0 = Some (OpImm ALU_ADD 10 10 1405, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6de4 : bv 32 := 0xeb458593.
Lemma F_a6de4 : fetch_word Ubsan.M.loaded_segments (0xa6de4 : word) = Some W_a6de4.
Proof. vm_refl. Qed.
Lemma D_a6de4 : decode_any W_a6de4 = Some (OpImm ALU_ADD 11 11 3764, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6de8 : bv 32 := 0x0500006f.
Lemma F_a6de8 : fetch_word Ubsan.M.loaded_segments (0xa6de8 : word) = Some W_a6de8.
Proof. vm_refl. Qed.
Lemma D_a6de8 : decode_any W_a6de8 = Some (Jal 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6dec : bv 32 := 0x00080517.
Lemma F_a6dec : fetch_word Ubsan.M.loaded_segments (0xa6dec : word) = Some W_a6dec.
Proof. vm_refl. Qed.
Lemma D_a6dec : decode_any W_a6dec = Some (Auipc 10 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6df0 : bv 32 := 0xc8453503.
Lemma F_a6df0 : fetch_word Ubsan.M.loaded_segments (0xa6df0 : word) = Some W_a6df0.
Proof. vm_refl. Qed.
Lemma D_a6df0 : decode_any W_a6df0 = Some (Load SZ8 true 10 10 3204, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6df4 : bv 32 := 0x00052503.
Lemma F_a6df4 : fetch_word Ubsan.M.loaded_segments (0xa6df4 : word) = Some W_a6df4.
Proof. vm_refl. Qed.
Lemma D_a6df4 : decode_any W_a6df4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6df8 : bv 32 := 0x00500593.
Lemma F_a6df8 : fetch_word Ubsan.M.loaded_segments (0xa6df8 : word) = Some W_a6df8.
Proof. vm_refl. Qed.
Lemma D_a6df8 : decode_any W_a6df8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6dfc : bv 32 := 0x06a5c463.
Lemma F_a6dfc : fetch_word Ubsan.M.loaded_segments (0xa6dfc : word) = Some W_a6dfc.
Proof. vm_refl. Qed.
Lemma D_a6dfc : decode_any W_a6dfc = Some (Branch BC_LT 11 10 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e00 : bv 32 := 0xfff6f517.
Lemma F_a6e00 : fetch_word Ubsan.M.loaded_segments (0xa6e00 : word) = Some W_a6e00.
Proof. vm_refl. Qed.
Lemma D_a6e00 : decode_any W_a6e00 = Some (Auipc 10 1048431, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e04 : bv 32 := 0xfff6f597.
Lemma F_a6e04 : fetch_word Ubsan.M.loaded_segments (0xa6e04 : word) = Some W_a6e04.
Proof. vm_refl. Qed.
Lemma D_a6e04 : decode_any W_a6e04 = Some (Auipc 11 1048431, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e08 : bv 32 := 0xeab50513.
Lemma F_a6e08 : fetch_word Ubsan.M.loaded_segments (0xa6e08 : word) = Some W_a6e08.
Proof. vm_refl. Qed.
Lemma D_a6e08 : decode_any W_a6e08 = Some (OpImm ALU_ADD 10 10 3755, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e0c : bv 32 := 0xe8c58593.
Lemma F_a6e0c : fetch_word Ubsan.M.loaded_segments (0xa6e0c : word) = Some W_a6e0c.
Proof. vm_refl. Qed.
Lemma D_a6e0c : decode_any W_a6e0c = Some (OpImm ALU_ADD 11 11 3724, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e10 : bv 32 := 0x0280006f.
Lemma F_a6e10 : fetch_word Ubsan.M.loaded_segments (0xa6e10 : word) = Some W_a6e10.
Proof. vm_refl. Qed.
Lemma D_a6e10 : decode_any W_a6e10 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e14 : bv 32 := 0x00080517.
Lemma F_a6e14 : fetch_word Ubsan.M.loaded_segments (0xa6e14 : word) = Some W_a6e14.
Proof. vm_refl. Qed.
Lemma D_a6e14 : decode_any W_a6e14 = Some (Auipc 10 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e18 : bv 32 := 0xc5c53503.
Lemma F_a6e18 : fetch_word Ubsan.M.loaded_segments (0xa6e18 : word) = Some W_a6e18.
Proof. vm_refl. Qed.
Lemma D_a6e18 : decode_any W_a6e18 = Some (Load SZ8 true 10 10 3164, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e1c : bv 32 := 0x00052503.
Lemma F_a6e1c : fetch_word Ubsan.M.loaded_segments (0xa6e1c : word) = Some W_a6e1c.
Proof. vm_refl. Qed.
Lemma D_a6e1c : decode_any W_a6e1c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e20 : bv 32 := 0x00500593.
Lemma F_a6e20 : fetch_word Ubsan.M.loaded_segments (0xa6e20 : word) = Some W_a6e20.
Proof. vm_refl. Qed.
Lemma D_a6e20 : decode_any W_a6e20 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e24 : bv 32 := 0x04a5c063.
Lemma F_a6e24 : fetch_word Ubsan.M.loaded_segments (0xa6e24 : word) = Some W_a6e24.
Proof. vm_refl. Qed.
Lemma D_a6e24 : decode_any W_a6e24 = Some (Branch BC_LT 11 10 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e28 : bv 32 := 0xfff6d517.
Lemma F_a6e28 : fetch_word Ubsan.M.loaded_segments (0xa6e28 : word) = Some W_a6e28.
Proof. vm_refl. Qed.
Lemma D_a6e28 : decode_any W_a6e28 = Some (Auipc 10 1048429, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e2c : bv 32 := 0xfff6f597.
Lemma F_a6e2c : fetch_word Ubsan.M.loaded_segments (0xa6e2c : word) = Some W_a6e2c.
Proof. vm_refl. Qed.
Lemma D_a6e2c : decode_any W_a6e2c = Some (Auipc 11 1048431, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e30 : bv 32 := 0x92750513.
Lemma F_a6e30 : fetch_word Ubsan.M.loaded_segments (0xa6e30 : word) = Some W_a6e30.
Proof. vm_refl. Qed.
Lemma D_a6e30 : decode_any W_a6e30 = Some (OpImm ALU_ADD 10 10 2343, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e34 : bv 32 := 0xe6458593.
Lemma F_a6e34 : fetch_word Ubsan.M.loaded_segments (0xa6e34 : word) = Some W_a6e34.
Proof. vm_refl. Qed.
Lemma D_a6e34 : decode_any W_a6e34 = Some (OpImm ALU_ADD 11 11 3684, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e38 : bv 32 := 0x00000613.
Lemma F_a6e38 : fetch_word Ubsan.M.loaded_segments (0xa6e38 : word) = Some W_a6e38.
Proof. vm_refl. Qed.
Lemma D_a6e38 : decode_any W_a6e38 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e3c : bv 32 := 0x05813083.
Lemma F_a6e3c : fetch_word Ubsan.M.loaded_segments (0xa6e3c : word) = Some W_a6e3c.
Proof. vm_refl. Qed.
Lemma D_a6e3c : decode_any W_a6e3c = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e40 : bv 32 := 0x05013403.
Lemma F_a6e40 : fetch_word Ubsan.M.loaded_segments (0xa6e40 : word) = Some W_a6e40.
Proof. vm_refl. Qed.
Lemma D_a6e40 : decode_any W_a6e40 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e44 : bv 32 := 0x04813483.
Lemma F_a6e44 : fetch_word Ubsan.M.loaded_segments (0xa6e44 : word) = Some W_a6e44.
Proof. vm_refl. Qed.
Lemma D_a6e44 : decode_any W_a6e44 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e48 : bv 32 := 0x04013903.
Lemma F_a6e48 : fetch_word Ubsan.M.loaded_segments (0xa6e48 : word) = Some W_a6e48.
Proof. vm_refl. Qed.
Lemma D_a6e48 : decode_any W_a6e48 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e4c : bv 32 := 0x03813983.
Lemma F_a6e4c : fetch_word Ubsan.M.loaded_segments (0xa6e4c : word) = Some W_a6e4c.
Proof. vm_refl. Qed.
Lemma D_a6e4c : decode_any W_a6e4c = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e50 : bv 32 := 0x03013a03.
Lemma F_a6e50 : fetch_word Ubsan.M.loaded_segments (0xa6e50 : word) = Some W_a6e50.
Proof. vm_refl. Qed.
Lemma D_a6e50 : decode_any W_a6e50 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e54 : bv 32 := 0x02813a83.
Lemma F_a6e54 : fetch_word Ubsan.M.loaded_segments (0xa6e54 : word) = Some W_a6e54.
Proof. vm_refl. Qed.
Lemma D_a6e54 : decode_any W_a6e54 = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e58 : bv 32 := 0x02013b03.
Lemma F_a6e58 : fetch_word Ubsan.M.loaded_segments (0xa6e58 : word) = Some W_a6e58.
Proof. vm_refl. Qed.
Lemma D_a6e58 : decode_any W_a6e58 = Some (Load SZ8 true 22 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e5c : bv 32 := 0x06010113.
Lemma F_a6e5c : fetch_word Ubsan.M.loaded_segments (0xa6e5c : word) = Some W_a6e5c.
Proof. vm_refl. Qed.
Lemma D_a6e5c : decode_any W_a6e5c = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e60 : bv 32 := 0x8e1bc06f.
Lemma F_a6e60 : fetch_word Ubsan.M.loaded_segments (0xa6e60 : word) = Some W_a6e60.
Proof. vm_refl. Qed.
Lemma D_a6e60 : decode_any W_a6e60 = Some (Jal 0 1820896, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e64 : bv 32 := 0x00000513.
Lemma F_a6e64 : fetch_word Ubsan.M.loaded_segments (0xa6e64 : word) = Some W_a6e64.
Proof. vm_refl. Qed.
Lemma D_a6e64 : decode_any W_a6e64 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e68 : bv 32 := 0x05813083.
Lemma F_a6e68 : fetch_word Ubsan.M.loaded_segments (0xa6e68 : word) = Some W_a6e68.
Proof. vm_refl. Qed.
Lemma D_a6e68 : decode_any W_a6e68 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e6c : bv 32 := 0x05013403.
Lemma F_a6e6c : fetch_word Ubsan.M.loaded_segments (0xa6e6c : word) = Some W_a6e6c.
Proof. vm_refl. Qed.
Lemma D_a6e6c : decode_any W_a6e6c = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e70 : bv 32 := 0x04813483.
Lemma F_a6e70 : fetch_word Ubsan.M.loaded_segments (0xa6e70 : word) = Some W_a6e70.
Proof. vm_refl. Qed.
Lemma D_a6e70 : decode_any W_a6e70 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e74 : bv 32 := 0x04013903.
Lemma F_a6e74 : fetch_word Ubsan.M.loaded_segments (0xa6e74 : word) = Some W_a6e74.
Proof. vm_refl. Qed.
Lemma D_a6e74 : decode_any W_a6e74 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e78 : bv 32 := 0x03813983.
Lemma F_a6e78 : fetch_word Ubsan.M.loaded_segments (0xa6e78 : word) = Some W_a6e78.
Proof. vm_refl. Qed.
Lemma D_a6e78 : decode_any W_a6e78 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e7c : bv 32 := 0x03013a03.
Lemma F_a6e7c : fetch_word Ubsan.M.loaded_segments (0xa6e7c : word) = Some W_a6e7c.
Proof. vm_refl. Qed.
Lemma D_a6e7c : decode_any W_a6e7c = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e80 : bv 32 := 0x02813a83.
Lemma F_a6e80 : fetch_word Ubsan.M.loaded_segments (0xa6e80 : word) = Some W_a6e80.
Proof. vm_refl. Qed.
Lemma D_a6e80 : decode_any W_a6e80 = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e84 : bv 32 := 0x02013b03.
Lemma F_a6e84 : fetch_word Ubsan.M.loaded_segments (0xa6e84 : word) = Some W_a6e84.
Proof. vm_refl. Qed.
Lemma D_a6e84 : decode_any W_a6e84 = Some (Load SZ8 true 22 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e88 : bv 32 := 0x06010113.
Lemma F_a6e88 : fetch_word Ubsan.M.loaded_segments (0xa6e88 : word) = Some W_a6e88.
Proof. vm_refl. Qed.
Lemma D_a6e88 : decode_any W_a6e88 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e8c : bv 32 := 0x00008067.
Lemma F_a6e8c : fetch_word Ubsan.M.loaded_segments (0xa6e8c : word) = Some W_a6e8c.
Proof. vm_refl. Qed.
Lemma D_a6e8c : decode_any W_a6e8c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e90 : bv 32 := 0x00080517.
Lemma F_a6e90 : fetch_word Ubsan.M.loaded_segments (0xa6e90 : word) = Some W_a6e90.
Proof. vm_refl. Qed.
Lemma D_a6e90 : decode_any W_a6e90 = Some (Auipc 10 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e94 : bv 32 := 0xbe053503.
Lemma F_a6e94 : fetch_word Ubsan.M.loaded_segments (0xa6e94 : word) = Some W_a6e94.
Proof. vm_refl. Qed.
Lemma D_a6e94 : decode_any W_a6e94 = Some (Load SZ8 true 10 10 3040, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e98 : bv 32 := 0x00052503.
Lemma F_a6e98 : fetch_word Ubsan.M.loaded_segments (0xa6e98 : word) = Some W_a6e98.
Proof. vm_refl. Qed.
Lemma D_a6e98 : decode_any W_a6e98 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6e9c : bv 32 := 0x00400593.
Lemma F_a6e9c : fetch_word Ubsan.M.loaded_segments (0xa6e9c : word) = Some W_a6e9c.
Proof. vm_refl. Qed.
Lemma D_a6e9c : decode_any W_a6e9c = Some (OpImm ALU_ADD 11 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6ea0 : bv 32 := 0x00a5cc63.
Lemma F_a6ea0 : fetch_word Ubsan.M.loaded_segments (0xa6ea0 : word) = Some W_a6ea0.
Proof. vm_refl. Qed.
Lemma D_a6ea0 : decode_any W_a6ea0 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6ea4 : bv 32 := 0xfff73517.
Lemma F_a6ea4 : fetch_word Ubsan.M.loaded_segments (0xa6ea4 : word) = Some W_a6ea4.
Proof. vm_refl. Qed.
Lemma D_a6ea4 : decode_any W_a6ea4 = Some (Auipc 10 1048435, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6ea8 : bv 32 := 0xfff6f597.
Lemma F_a6ea8 : fetch_word Ubsan.M.loaded_segments (0xa6ea8 : word) = Some W_a6ea8.
Proof. vm_refl. Qed.
Lemma D_a6ea8 : decode_any W_a6ea8 = Some (Auipc 11 1048431, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6eac : bv 32 := 0xdbb50513.
Lemma F_a6eac : fetch_word Ubsan.M.loaded_segments (0xa6eac : word) = Some W_a6eac.
Proof. vm_refl. Qed.
Lemma D_a6eac : decode_any W_a6eac = Some (OpImm ALU_ADD 10 10 3515, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6eb0 : bv 32 := 0xde858593.
Lemma F_a6eb0 : fetch_word Ubsan.M.loaded_segments (0xa6eb0 : word) = Some W_a6eb0.
Proof. vm_refl. Qed.
Lemma D_a6eb0 : decode_any W_a6eb0 = Some (OpImm ALU_ADD 11 11 3560, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6eb4 : bv 32 := 0xff0bc0ef.
Lemma F_a6eb4 : fetch_word Ubsan.M.loaded_segments (0xa6eb4 : word) = Some W_a6eb4.
Proof. vm_refl. Qed.
Lemma D_a6eb4 : decode_any W_a6eb4 = Some (Jal 1 1820656, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6eb8 : bv 32 := 0x00000513.
Lemma F_a6eb8 : fetch_word Ubsan.M.loaded_segments (0xa6eb8 : word) = Some W_a6eb8.
Proof. vm_refl. Qed.
Lemma D_a6eb8 : decode_any W_a6eb8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6ebc : bv 32 := 0x000a8593.
Lemma F_a6ebc : fetch_word Ubsan.M.loaded_segments (0xa6ebc : word) = Some W_a6ebc.
Proof. vm_refl. Qed.
Lemma D_a6ebc : decode_any W_a6ebc = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6ec0 : bv 32 := 0x05813083.
Lemma F_a6ec0 : fetch_word Ubsan.M.loaded_segments (0xa6ec0 : word) = Some W_a6ec0.
Proof. vm_refl. Qed.
Lemma D_a6ec0 : decode_any W_a6ec0 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6ec4 : bv 32 := 0x05013403.
Lemma F_a6ec4 : fetch_word Ubsan.M.loaded_segments (0xa6ec4 : word) = Some W_a6ec4.
Proof. vm_refl. Qed.
Lemma D_a6ec4 : decode_any W_a6ec4 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6ec8 : bv 32 := 0x04813483.
Lemma F_a6ec8 : fetch_word Ubsan.M.loaded_segments (0xa6ec8 : word) = Some W_a6ec8.
Proof. vm_refl. Qed.
Lemma D_a6ec8 : decode_any W_a6ec8 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6ecc : bv 32 := 0x04013903.
Lemma F_a6ecc : fetch_word Ubsan.M.loaded_segments (0xa6ecc : word) = Some W_a6ecc.
Proof. vm_refl. Qed.
Lemma D_a6ecc : decode_any W_a6ecc = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6ed0 : bv 32 := 0x03813983.
Lemma F_a6ed0 : fetch_word Ubsan.M.loaded_segments (0xa6ed0 : word) = Some W_a6ed0.
Proof. vm_refl. Qed.
Lemma D_a6ed0 : decode_any W_a6ed0 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6ed4 : bv 32 := 0x03013a03.
Lemma F_a6ed4 : fetch_word Ubsan.M.loaded_segments (0xa6ed4 : word) = Some W_a6ed4.
Proof. vm_refl. Qed.
Lemma D_a6ed4 : decode_any W_a6ed4 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6ed8 : bv 32 := 0x02813a83.
Lemma F_a6ed8 : fetch_word Ubsan.M.loaded_segments (0xa6ed8 : word) = Some W_a6ed8.
Proof. vm_refl. Qed.
Lemma D_a6ed8 : decode_any W_a6ed8 = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6edc : bv 32 := 0x02013b03.
Lemma F_a6edc : fetch_word Ubsan.M.loaded_segments (0xa6edc : word) = Some W_a6edc.
Proof. vm_refl. Qed.
Lemma D_a6edc : decode_any W_a6edc = Some (Load SZ8 true 22 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6ee0 : bv 32 := 0x06010113.
Lemma F_a6ee0 : fetch_word Ubsan.M.loaded_segments (0xa6ee0 : word) = Some W_a6ee0.
Proof. vm_refl. Qed.
Lemma D_a6ee0 : decode_any W_a6ee0 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6ee4 : bv 32 := 0xc79c706f.
Lemma F_a6ee4 : fetch_word Ubsan.M.loaded_segments (0xa6ee4 : word) = Some W_a6ee4.
Proof. vm_refl. Qed.
Lemma D_a6ee4 : decode_any W_a6ee4 = Some (Jal 0 1866872, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6ee8 : bv 32 := 0x00050413.
Lemma F_a6ee8 : fetch_word Ubsan.M.loaded_segments (0xa6ee8 : word) = Some W_a6ee8.
Proof. vm_refl. Qed.
Lemma D_a6ee8 : decode_any W_a6ee8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6eec : bv 32 := 0x00090513.
Lemma F_a6eec : fetch_word Ubsan.M.loaded_segments (0xa6eec : word) = Some W_a6eec.
Proof. vm_refl. Qed.
Lemma D_a6eec : decode_any W_a6eec = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6ef0 : bv 32 := 0x129670ef.
Lemma F_a6ef0 : fetch_word Ubsan.M.loaded_segments (0xa6ef0 : word) = Some W_a6ef0.
Proof. vm_refl. Qed.
Lemma D_a6ef0 : decode_any W_a6ef0 = Some (Jal 1 424232, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6ef4 : bv 32 := 0x00040513.
Lemma F_a6ef4 : fetch_word Ubsan.M.loaded_segments (0xa6ef4 : word) = Some W_a6ef4.
Proof. vm_refl. Qed.
Lemma D_a6ef4 : decode_any W_a6ef4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6ef8 : bv 32 := 0xf71ff06f.
Lemma F_a6ef8 : fetch_word Ubsan.M.loaded_segments (0xa6ef8 : word) = Some W_a6ef8.
Proof. vm_refl. Qed.
Lemma D_a6ef8 : decode_any W_a6ef8 = Some (Jal 0 2097008, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6efc : bv 32 := 0x00090513.
Lemma F_a6efc : fetch_word Ubsan.M.loaded_segments (0xa6efc : word) = Some W_a6efc.
Proof. vm_refl. Qed.
Lemma D_a6efc : decode_any W_a6efc = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f00 : bv 32 := 0x119670ef.
Lemma F_a6f00 : fetch_word Ubsan.M.loaded_segments (0xa6f00 : word) = Some W_a6f00.
Proof. vm_refl. Qed.
Lemma D_a6f00 : decode_any W_a6f00 = Some (Jal 1 424216, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f04 : bv 32 := 0x00098513.
Lemma F_a6f04 : fetch_word Ubsan.M.loaded_segments (0xa6f04 : word) = Some W_a6f04.
Proof. vm_refl. Qed.
Lemma D_a6f04 : decode_any W_a6f04 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f08 : bv 32 := 0xf61ff06f.
Lemma F_a6f08 : fetch_word Ubsan.M.loaded_segments (0xa6f08 : word) = Some W_a6f08.
Proof. vm_refl. Qed.
Lemma D_a6f08 : decode_any W_a6f08 = Some (Jal 0 2096992, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f0c : bv 32 := 0x00090513.
Lemma F_a6f0c : fetch_word Ubsan.M.loaded_segments (0xa6f0c : word) = Some W_a6f0c.
Proof. vm_refl. Qed.
Lemma D_a6f0c : decode_any W_a6f0c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f10 : bv 32 := 0x109670ef.
Lemma F_a6f10 : fetch_word Ubsan.M.loaded_segments (0xa6f10 : word) = Some W_a6f10.
Proof. vm_refl. Qed.
Lemma D_a6f10 : decode_any W_a6f10 = Some (Jal 1 424200, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f14 : bv 32 := 0x00048513.
Lemma F_a6f14 : fetch_word Ubsan.M.loaded_segments (0xa6f14 : word) = Some W_a6f14.
Proof. vm_refl. Qed.
Lemma D_a6f14 : decode_any W_a6f14 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a6f18 : bv 32 := 0xf51ff06f.
Lemma F_a6f18 : fetch_word Ubsan.M.loaded_segments (0xa6f18 : word) = Some W_a6f18.
Proof. vm_refl. Qed.
Lemma D_a6f18 : decode_any W_a6f18 = Some (Jal 0 2096976, 4%Z).
Proof. vm_refl. Qed.

(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.H Require GcFlushU9.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_61b68 : bv 32 := 0x0a060a63.
Lemma F_61b68 : fetch_word Ubsan.M.loaded_segments (0x61bc0 : word) = Some W_61b68.
Proof. vm_refl. Qed.
Lemma D_61b68 : decode_any W_61b68 = Some (Branch BC_EQ 12 0 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61b6c : bv 32 := 0x00367693.
Lemma F_61b6c : fetch_word Ubsan.M.loaded_segments (0x61bc4 : word) = Some W_61b6c.
Proof. vm_refl. Qed.
Lemma D_61b6c : decode_any W_61b6c = Some (OpImm ALU_AND 13 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61b70 : bv 32 := 0x12069c63.
Lemma F_61b70 : fetch_word Ubsan.M.loaded_segments (0x61bc8 : word) = Some W_61b70.
Proof. vm_refl. Qed.
Lemma D_61b70 : decode_any W_61b70 = Some (Branch BC_NE 13 0 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61b74 : bv 32 := 0x00062023.
Lemma F_61b74 : fetch_word Ubsan.M.loaded_segments (0x61bcc : word) = Some W_61b74.
Proof. vm_refl. Qed.
Lemma D_61b74 : decode_any W_61b74 = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61b78 : bv 32 := 0x0e050e63.
Lemma F_61b78 : fetch_word Ubsan.M.loaded_segments (0x61bd0 : word) = Some W_61b78.
Proof. vm_refl. Qed.
Lemma D_61b78 : decode_any W_61b78 = Some (Branch BC_EQ 10 0 252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61b7c : bv 32 := 0x0c05c663.
Lemma F_61b7c : fetch_word Ubsan.M.loaded_segments (0x61bd4 : word) = Some W_61b7c.
Proof. vm_refl. Qed.
Lemma D_61b7c : decode_any W_61b7c = Some (Branch BC_LT 11 0 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61b80 : bv 32 := 0x00757693.
Lemma F_61b80 : fetch_word Ubsan.M.loaded_segments (0x61bd8 : word) = Some W_61b80.
Proof. vm_refl. Qed.
Lemma D_61b80 : decode_any W_61b80 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61b84 : bv 32 := 0x12069263.
Lemma F_61b84 : fetch_word Ubsan.M.loaded_segments (0x61bdc : word) = Some W_61b84.
Proof. vm_refl. Qed.
Lemma D_61b84 : decode_any W_61b84 = Some (Branch BC_NE 13 0 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61b88 : bv 32 := 0x00452683.
Lemma F_61b88 : fetch_word Ubsan.M.loaded_segments (0x61be0 : word) = Some W_61b88.
Proof. vm_refl. Qed.
Lemma D_61b88 : decode_any W_61b88 = Some (Load SZ4 true 13 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61b8c : bv 32 := 0x0ad5de63.
Lemma F_61b8c : fetch_word Ubsan.M.loaded_segments (0x61be4 : word) = Some W_61b8c.
Proof. vm_refl. Qed.
Lemma D_61b8c : decode_any W_61b8c = Some (Branch BC_GE 11 13 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61b90 : bv 32 := 0x01853683.
Lemma F_61b90 : fetch_word Ubsan.M.loaded_segments (0x61be8 : word) = Some W_61b90.
Proof. vm_refl. Qed.
Lemma D_61b90 : decode_any W_61b90 = Some (Load SZ8 true 13 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61b94 : bv 32 := 0x00259513.
Lemma F_61b94 : fetch_word Ubsan.M.loaded_segments (0x61bec : word) = Some W_61b94.
Proof. vm_refl. Qed.
Lemma D_61b94 : decode_any W_61b94 = Some (ShiftImm ALU_SLL 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61b98 : bv 32 := 0x00a68533.
Lemma F_61b98 : fetch_word Ubsan.M.loaded_segments (0x61bf0 : word) = Some W_61b98.
Proof. vm_refl. Qed.
Lemma D_61b98 : decode_any W_61b98 = Some (Op ALU_ADD 10 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61b9c : bv 32 := 0x10d56663.
Lemma F_61b9c : fetch_word Ubsan.M.loaded_segments (0x61bf4 : word) = Some W_61b9c.
Proof. vm_refl. Qed.
Lemma D_61b9c : decode_any W_61b9c = Some (Branch BC_LTU 10 13 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61ba0 : bv 32 := 0x00d035b3.
Lemma F_61ba0 : fetch_word Ubsan.M.loaded_segments (0x61bf8 : word) = Some W_61ba0.
Proof. vm_refl. Qed.
Lemma D_61ba0 : decode_any W_61ba0 = Some (Op ALU_SLTU 11 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61ba4 : bv 32 := 0x00153713.
Lemma F_61ba4 : fetch_word Ubsan.M.loaded_segments (0x61bfc : word) = Some W_61ba4.
Proof. vm_refl. Qed.
Lemma D_61ba4 : decode_any W_61ba4 = Some (OpImm ALU_SLTU 14 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61ba8 : bv 32 := 0x00e5c5b3.
Lemma F_61ba8 : fetch_word Ubsan.M.loaded_segments (0x61c00 : word) = Some W_61ba8.
Proof. vm_refl. Qed.
Lemma D_61ba8 : decode_any W_61ba8 = Some (Op ALU_XOR 11 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61bac : bv 32 := 0x0e058e63.
Lemma F_61bac : fetch_word Ubsan.M.loaded_segments (0x61c04 : word) = Some W_61bac.
Proof. vm_refl. Qed.
Lemma D_61bac : decode_any W_61bac = Some (Branch BC_EQ 11 0 252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61bb0 : bv 32 := 0x0e068c63.
Lemma F_61bb0 : fetch_word Ubsan.M.loaded_segments (0x61c08 : word) = Some W_61bb0.
Proof. vm_refl. Qed.
Lemma D_61bb0 : decode_any W_61bb0 = Some (Branch BC_EQ 13 0 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61bb4 : bv 32 := 0x00357593.
Lemma F_61bb4 : fetch_word Ubsan.M.loaded_segments (0x61c0c : word) = Some W_61bb4.
Proof. vm_refl. Qed.
Lemma D_61bb4 : decode_any W_61bb4 = Some (OpImm ALU_AND 11 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61bb8 : bv 32 := 0x0e059863.
Lemma F_61bb8 : fetch_word Ubsan.M.loaded_segments (0x61c10 : word) = Some W_61bb8.
Proof. vm_refl. Qed.
Lemma D_61bb8 : decode_any W_61bb8 = Some (Branch BC_NE 11 0 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61bbc : bv 32 := 0x00052787.
Lemma F_61bbc : fetch_word Ubsan.M.loaded_segments (0x61c14 : word) = Some W_61bbc.
Proof. vm_refl. Qed.
Lemma D_61bbc : decode_any W_61bbc = Some (FLoad FMT_S 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61bc0 : bv 32 := 0xf0000753.
Lemma F_61bc0 : fetch_word Ubsan.M.loaded_segments (0x61c18 : word) = Some W_61bc0.
Proof. vm_refl. Qed.
Lemma D_61bc0 : decode_any W_61bc0 = Some (Fmv FMV_F_X FMT_S 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61bc4 : bv 32 := 0xfffbb517.
Lemma F_61bc4 : fetch_word Ubsan.M.loaded_segments (0x61c1c : word) = Some W_61bc4.
Proof. vm_refl. Qed.
Lemma D_61bc4 : decode_any W_61bc4 = Some (Auipc 10 1048507, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61bc8 : bv 32 := 0xfffbb597.
Lemma F_61bc8 : fetch_word Ubsan.M.loaded_segments (0x61c20 : word) = Some W_61bc8.
Proof. vm_refl. Qed.
Lemma D_61bc8 : decode_any W_61bc8 = Some (Auipc 11 1048507, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61bcc : bv 32 := 0xa6450513.
Lemma F_61bcc : fetch_word Ubsan.M.loaded_segments (0x61c24 : word) = Some W_61bcc.
Proof. vm_refl. Qed.
Lemma D_61bcc : decode_any W_61bcc = Some (OpImm ALU_ADD 10 10 2660, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61bd0 : bv 32 := 0x8105b687.
Lemma F_61bd0 : fetch_word Ubsan.M.loaded_segments (0x61c28 : word) = Some W_61bd0.
Proof. vm_refl. Qed.
Lemma D_61bd0 : decode_any W_61bd0 = Some (FLoad FMT_D 13 11 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61bd4 : bv 32 := 0xa0e795d3.
Lemma F_61bd4 : fetch_word Ubsan.M.loaded_segments (0x61c2c : word) = Some W_61bd4.
Proof. vm_refl. Qed.
Lemma D_61bd4 : decode_any W_61bd4 = Some (Fcmp F_LT FMT_S 11 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61bd8 : bv 32 := 0x00359593.
Lemma F_61bd8 : fetch_word Ubsan.M.loaded_segments (0x61c30 : word) = Some W_61bd8.
Proof. vm_refl. Qed.
Lemma D_61bd8 : decode_any W_61bd8 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61bdc : bv 32 := 0x00b50533.
Lemma F_61bdc : fetch_word Ubsan.M.loaded_segments (0x61c34 : word) = Some W_61bdc.
Proof. vm_refl. Qed.
Lemma D_61bdc : decode_any W_61bdc = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61be0 : bv 32 := 0x00053707.
Lemma F_61be0 : fetch_word Ubsan.M.loaded_segments (0x61c38 : word) = Some W_61be0.
Proof. vm_refl. Qed.
Lemma D_61be0 : decode_any W_61be0 = Some (FLoad FMT_D 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61be4 : bv 32 := 0xfffbb517.
Lemma F_61be4 : fetch_word Ubsan.M.loaded_segments (0x61c3c : word) = Some W_61be4.
Proof. vm_refl. Qed.
Lemma D_61be4 : decode_any W_61be4 = Some (Auipc 10 1048507, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61be8 : bv 32 := 0x83c53607.
Lemma F_61be8 : fetch_word Ubsan.M.loaded_segments (0x61c40 : word) = Some W_61be8.
Proof. vm_refl. Qed.
Lemma D_61be8 : decode_any W_61be8 = Some (FLoad FMT_D 12 10 2108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61bec : bv 32 := 0x420787d3.
Lemma F_61bec : fetch_word Ubsan.M.loaded_segments (0x61c44 : word) = Some W_61bec.
Proof. vm_refl. Qed.
Lemma D_61bec : decode_any W_61bec = Some (Fcvt FC_D FC_S 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61bf0 : bv 32 := 0x7ad777c3.
Lemma F_61bf0 : fetch_word Ubsan.M.loaded_segments (0x61c48 : word) = Some W_61bf0.
Proof. vm_refl. Qed.
Lemma D_61bf0 : decode_any W_61bf0 = Some (Fma F_MADD FMT_D 15 14 13 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61bf4 : bv 32 := 0xa2f61553.
Lemma F_61bf4 : fetch_word Ubsan.M.loaded_segments (0x61c4c : word) = Some W_61bf4.
Proof. vm_refl. Qed.
Lemma D_61bf4 : decode_any W_61bf4 = Some (Fcmp F_LT FMT_D 10 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61bf8 : bv 32 := 0x0a050863.
Lemma F_61bf8 : fetch_word Ubsan.M.loaded_segments (0x61c50 : word) = Some W_61bf8.
Proof. vm_refl. Qed.
Lemma D_61bf8 : decode_any W_61bf8 = Some (Branch BC_EQ 10 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61bfc : bv 32 := 0xfffba517.
Lemma F_61bfc : fetch_word Ubsan.M.loaded_segments (0x61c54 : word) = Some W_61bfc.
Proof. vm_refl. Qed.
Lemma D_61bfc : decode_any W_61bfc = Some (Auipc 10 1048506, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61c00 : bv 32 := 0x6f453707.
Lemma F_61c00 : fetch_word Ubsan.M.loaded_segments (0x61c58 : word) = Some W_61c00.
Proof. vm_refl. Qed.
Lemma D_61c00 : decode_any W_61c00 = Some (FLoad FMT_D 14 10 1780, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61c04 : bv 32 := 0xa2e79553.
Lemma F_61c04 : fetch_word Ubsan.M.loaded_segments (0x61c5c : word) = Some W_61c04.
Proof. vm_refl. Qed.
Lemma D_61c04 : decode_any W_61c04 = Some (Fcmp F_LT FMT_D 10 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61c08 : bv 32 := 0x0a050063.
Lemma F_61c08 : fetch_word Ubsan.M.loaded_segments (0x61c60 : word) = Some W_61c08.
Proof. vm_refl. Qed.
Lemma D_61c08 : decode_any W_61c08 = Some (Branch BC_EQ 10 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61c0c : bv 32 := 0x00000513.
Lemma F_61c0c : fetch_word Ubsan.M.loaded_segments (0x61c64 : word) = Some W_61c0c.
Proof. vm_refl. Qed.
Lemma D_61c0c : decode_any W_61c0c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61c10 : bv 32 := 0xc20795d3.
Lemma F_61c10 : fetch_word Ubsan.M.loaded_segments (0x61c68 : word) = Some W_61c10.
Proof. vm_refl. Qed.
Lemma D_61c10 : decode_any W_61c10 = Some (Fcvt FC_W FC_D 11 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61c14 : bv 32 := 0x00b62023.
Lemma F_61c14 : fetch_word Ubsan.M.loaded_segments (0x61c6c : word) = Some W_61c14.
Proof. vm_refl. Qed.
Lemma D_61c14 : decode_any W_61c14 = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61c18 : bv 32 := 0x00008067.
Lemma F_61c18 : fetch_word Ubsan.M.loaded_segments (0x61c70 : word) = Some W_61c18.
Proof. vm_refl. Qed.
Lemma D_61c18 : decode_any W_61c18 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.


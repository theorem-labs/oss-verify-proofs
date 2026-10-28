(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6ff30 : bv 32 := 0x04050663.
Lemma F_6ff30 : fetch_word Ubsan.M.loaded_segments (0x6ff30 : word) = Some W_6ff30.
Proof. vm_refl. Qed.
Lemma D_6ff30 : decode_any W_6ff30 = Some (Branch BC_EQ 10 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff34 : bv 32 := 0x00757593.
Lemma F_6ff34 : fetch_word Ubsan.M.loaded_segments (0x6ff34 : word) = Some W_6ff34.
Proof. vm_refl. Qed.
Lemma D_6ff34 : decode_any W_6ff34 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff38 : bv 32 := 0x06059c63.
Lemma F_6ff38 : fetch_word Ubsan.M.loaded_segments (0x6ff38 : word) = Some W_6ff38.
Proof. vm_refl. Qed.
Lemma D_6ff38 : decode_any W_6ff38 = Some (Branch BC_NE 11 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff3c : bv 32 := 0x01056583.
Lemma F_6ff3c : fetch_word Ubsan.M.loaded_segments (0x6ff3c : word) = Some W_6ff3c.
Proof. vm_refl. Qed.
Lemma D_6ff3c : decode_any W_6ff3c = Some (Load SZ4 false 11 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff40 : bv 32 := 0x00456603.
Lemma F_6ff40 : fetch_word Ubsan.M.loaded_segments (0x6ff40 : word) = Some W_6ff40.
Proof. vm_refl. Qed.
Lemma D_6ff40 : decode_any W_6ff40 = Some (Load SZ4 false 12 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff44 : bv 32 := 0x00259593.
Lemma F_6ff44 : fetch_word Ubsan.M.loaded_segments (0x6ff44 : word) = Some W_6ff44.
Proof. vm_refl. Qed.
Lemma D_6ff44 : decode_any W_6ff44 = Some (ShiftImm ALU_SLL 11 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff48 : bv 32 := 0x02c596b3.
Lemma F_6ff48 : fetch_word Ubsan.M.loaded_segments (0x6ff48 : word) = Some W_6ff48.
Proof. vm_refl. Qed.
Lemma D_6ff48 : decode_any W_6ff48 = Some (Mul M_MULH 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff4c : bv 32 := 0x02c58633.
Lemma F_6ff4c : fetch_word Ubsan.M.loaded_segments (0x6ff4c : word) = Some W_6ff4c.
Proof. vm_refl. Qed.
Lemma D_6ff4c : decode_any W_6ff4c = Some (Mul M_MUL 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff50 : bv 32 := 0x43f65593.
Lemma F_6ff50 : fetch_word Ubsan.M.loaded_segments (0x6ff50 : word) = Some W_6ff50.
Proof. vm_refl. Qed.
Lemma D_6ff50 : decode_any W_6ff50 = Some (ShiftImm ALU_SRA 11 12 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff54 : bv 32 := 0x04b69e63.
Lemma F_6ff54 : fetch_word Ubsan.M.loaded_segments (0x6ff54 : word) = Some W_6ff54.
Proof. vm_refl. Qed.
Lemma D_6ff54 : decode_any W_6ff54 = Some (Branch BC_NE 13 11 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff58 : bv 32 := 0xff010113.
Lemma F_6ff58 : fetch_word Ubsan.M.loaded_segments (0x6ff58 : word) = Some W_6ff58.
Proof. vm_refl. Qed.
Lemma D_6ff58 : decode_any W_6ff58 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff5c : bv 32 := 0x00113423.
Lemma F_6ff5c : fetch_word Ubsan.M.loaded_segments (0x6ff5c : word) = Some W_6ff5c.
Proof. vm_refl. Qed.
Lemma D_6ff5c : decode_any W_6ff5c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff60 : bv 32 := 0x03853503.
Lemma F_6ff60 : fetch_word Ubsan.M.loaded_segments (0x6ff60 : word) = Some W_6ff60.
Proof. vm_refl. Qed.
Lemma D_6ff60 : decode_any W_6ff60 = Some (Load SZ8 true 10 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff64 : bv 32 := 0x00000593.
Lemma F_6ff64 : fetch_word Ubsan.M.loaded_segments (0x6ff64 : word) = Some W_6ff64.
Proof. vm_refl. Qed.
Lemma D_6ff64 : decode_any W_6ff64 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff68 : bv 32 := 0x76cae0ef.
Lemma F_6ff68 : fetch_word Ubsan.M.loaded_segments (0x6ff68 : word) = Some W_6ff68.
Proof. vm_refl. Qed.
Lemma D_6ff68 : decode_any W_6ff68 = Some (Jal 1 714604, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff6c : bv 32 := 0x00000513.
Lemma F_6ff6c : fetch_word Ubsan.M.loaded_segments (0x6ff6c : word) = Some W_6ff6c.
Proof. vm_refl. Qed.
Lemma D_6ff6c : decode_any W_6ff6c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff70 : bv 32 := 0x00813083.
Lemma F_6ff70 : fetch_word Ubsan.M.loaded_segments (0x6ff70 : word) = Some W_6ff70.
Proof. vm_refl. Qed.
Lemma D_6ff70 : decode_any W_6ff70 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff74 : bv 32 := 0x01010113.
Lemma F_6ff74 : fetch_word Ubsan.M.loaded_segments (0x6ff74 : word) = Some W_6ff74.
Proof. vm_refl. Qed.
Lemma D_6ff74 : decode_any W_6ff74 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff78 : bv 32 := 0x00008067.
Lemma F_6ff78 : fetch_word Ubsan.M.loaded_segments (0x6ff78 : word) = Some W_6ff78.
Proof. vm_refl. Qed.
Lemma D_6ff78 : decode_any W_6ff78 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff7c : bv 32 := 0x000b7517.
Lemma F_6ff7c : fetch_word Ubsan.M.loaded_segments (0x6ff7c : word) = Some W_6ff7c.
Proof. vm_refl. Qed.
Lemma D_6ff7c : decode_any W_6ff7c = Some (Auipc 10 183, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff80 : bv 32 := 0xaf453503.
Lemma F_6ff80 : fetch_word Ubsan.M.loaded_segments (0x6ff80 : word) = Some W_6ff80.
Proof. vm_refl. Qed.
Lemma D_6ff80 : decode_any W_6ff80 = Some (Load SZ8 true 10 10 2804, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff84 : bv 32 := 0x00052503.
Lemma F_6ff84 : fetch_word Ubsan.M.loaded_segments (0x6ff84 : word) = Some W_6ff84.
Proof. vm_refl. Qed.
Lemma D_6ff84 : decode_any W_6ff84 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff88 : bv 32 := 0x00500593.
Lemma F_6ff88 : fetch_word Ubsan.M.loaded_segments (0x6ff88 : word) = Some W_6ff88.
Proof. vm_refl. Qed.
Lemma D_6ff88 : decode_any W_6ff88 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff8c : bv 32 := 0x00a5ce63.
Lemma F_6ff8c : fetch_word Ubsan.M.loaded_segments (0x6ff8c : word) = Some W_6ff8c.
Proof. vm_refl. Qed.
Lemma D_6ff8c : decode_any W_6ff8c = Some (Branch BC_LT 11 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff90 : bv 32 := 0xfffa1517.
Lemma F_6ff90 : fetch_word Ubsan.M.loaded_segments (0x6ff90 : word) = Some W_6ff90.
Proof. vm_refl. Qed.
Lemma D_6ff90 : decode_any W_6ff90 = Some (Auipc 10 1048481, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff94 : bv 32 := 0xfffa7597.
Lemma F_6ff94 : fetch_word Ubsan.M.loaded_segments (0x6ff94 : word) = Some W_6ff94.
Proof. vm_refl. Qed.
Lemma D_6ff94 : decode_any W_6ff94 = Some (Auipc 11 1048487, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff98 : bv 32 := 0x0bb50513.
Lemma F_6ff98 : fetch_word Ubsan.M.loaded_segments (0x6ff98 : word) = Some W_6ff98.
Proof. vm_refl. Qed.
Lemma D_6ff98 : decode_any W_6ff98 = Some (OpImm ALU_ADD 10 10 187, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff9c : bv 32 := 0x17658593.
Lemma F_6ff9c : fetch_word Ubsan.M.loaded_segments (0x6ff9c : word) = Some W_6ff9c.
Proof. vm_refl. Qed.
Lemma D_6ff9c : decode_any W_6ff9c = Some (OpImm ALU_ADD 11 11 374, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffa0 : bv 32 := 0x00100613.
Lemma F_6ffa0 : fetch_word Ubsan.M.loaded_segments (0x6ffa0 : word) = Some W_6ffa0.
Proof. vm_refl. Qed.
Lemma D_6ffa0 : decode_any W_6ffa0 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffa4 : bv 32 := 0xeccf306f.
Lemma F_6ffa4 : fetch_word Ubsan.M.loaded_segments (0x6ffa4 : word) = Some W_6ffa4.
Proof. vm_refl. Qed.
Lemma D_6ffa4 : decode_any W_6ffa4 = Some (Jal 0 2045644, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffa8 : bv 32 := 0x00100513.
Lemma F_6ffa8 : fetch_word Ubsan.M.loaded_segments (0x6ffa8 : word) = Some W_6ffa8.
Proof. vm_refl. Qed.
Lemma D_6ffa8 : decode_any W_6ffa8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffac : bv 32 := 0x00008067.
Lemma F_6ffac : fetch_word Ubsan.M.loaded_segments (0x6ffac : word) = Some W_6ffac.
Proof. vm_refl. Qed.
Lemma D_6ffac : decode_any W_6ffac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

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

Definition W_6da3c : bv 32 := 0xff010113.
Lemma F_6da3c : fetch_word Ubsan.M.loaded_segments (0x6da3c : word) = Some W_6da3c.
Proof. vm_refl. Qed.
Lemma D_6da3c : decode_any W_6da3c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da40 : bv 32 := 0x00113423.
Lemma F_6da40 : fetch_word Ubsan.M.loaded_segments (0x6da40 : word) = Some W_6da40.
Proof. vm_refl. Qed.
Lemma D_6da40 : decode_any W_6da40 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da44 : bv 32 := 0x00813023.
Lemma F_6da44 : fetch_word Ubsan.M.loaded_segments (0x6da44 : word) = Some W_6da44.
Proof. vm_refl. Qed.
Lemma D_6da44 : decode_any W_6da44 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da48 : bv 32 := 0x098000ef.
Lemma F_6da48 : fetch_word Ubsan.M.loaded_segments (0x6da48 : word) = Some W_6da48.
Proof. vm_refl. Qed.
Lemma D_6da48 : decode_any W_6da48 = Some (Jal 1 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da4c : bv 32 := 0x04050263.
Lemma F_6da4c : fetch_word Ubsan.M.loaded_segments (0x6da4c : word) = Some W_6da4c.
Proof. vm_refl. Qed.
Lemma D_6da4c : decode_any W_6da4c = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da50 : bv 32 := 0x00757593.
Lemma F_6da50 : fetch_word Ubsan.M.loaded_segments (0x6da50 : word) = Some W_6da50.
Proof. vm_refl. Qed.
Lemma D_6da50 : decode_any W_6da50 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da54 : bv 32 := 0x08059463.
Lemma F_6da54 : fetch_word Ubsan.M.loaded_segments (0x6da54 : word) = Some W_6da54.
Proof. vm_refl. Qed.
Lemma D_6da54 : decode_any W_6da54 = Some (Branch BC_NE 11 0 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da58 : bv 32 := 0x01056583.
Lemma F_6da58 : fetch_word Ubsan.M.loaded_segments (0x6da58 : word) = Some W_6da58.
Proof. vm_refl. Qed.
Lemma D_6da58 : decode_any W_6da58 = Some (Load SZ4 false 11 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da5c : bv 32 := 0x00456603.
Lemma F_6da5c : fetch_word Ubsan.M.loaded_segments (0x6da5c : word) = Some W_6da5c.
Proof. vm_refl. Qed.
Lemma D_6da5c : decode_any W_6da5c = Some (Load SZ4 false 12 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da60 : bv 32 := 0x00259593.
Lemma F_6da60 : fetch_word Ubsan.M.loaded_segments (0x6da60 : word) = Some W_6da60.
Proof. vm_refl. Qed.
Lemma D_6da60 : decode_any W_6da60 = Some (ShiftImm ALU_SLL 11 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da64 : bv 32 := 0x02c596b3.
Lemma F_6da64 : fetch_word Ubsan.M.loaded_segments (0x6da64 : word) = Some W_6da64.
Proof. vm_refl. Qed.
Lemma D_6da64 : decode_any W_6da64 = Some (Mul M_MULH 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da68 : bv 32 := 0x02c58633.
Lemma F_6da68 : fetch_word Ubsan.M.loaded_segments (0x6da68 : word) = Some W_6da68.
Proof. vm_refl. Qed.
Lemma D_6da68 : decode_any W_6da68 = Some (Mul M_MUL 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da6c : bv 32 := 0x43f65593.
Lemma F_6da6c : fetch_word Ubsan.M.loaded_segments (0x6da6c : word) = Some W_6da6c.
Proof. vm_refl. Qed.
Lemma D_6da6c : decode_any W_6da6c = Some (ShiftImm ALU_SRA 11 12 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da70 : bv 32 := 0x06b69663.
Lemma F_6da70 : fetch_word Ubsan.M.loaded_segments (0x6da70 : word) = Some W_6da70.
Proof. vm_refl. Qed.
Lemma D_6da70 : decode_any W_6da70 = Some (Branch BC_NE 13 11 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da74 : bv 32 := 0x03853583.
Lemma F_6da74 : fetch_word Ubsan.M.loaded_segments (0x6da74 : word) = Some W_6da74.
Proof. vm_refl. Qed.
Lemma D_6da74 : decode_any W_6da74 = Some (Load SZ8 true 11 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da78 : bv 32 := 0x00050413.
Lemma F_6da78 : fetch_word Ubsan.M.loaded_segments (0x6da78 : word) = Some W_6da78.
Proof. vm_refl. Qed.
Lemma D_6da78 : decode_any W_6da78 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da7c : bv 32 := 0x00058513.
Lemma F_6da7c : fetch_word Ubsan.M.loaded_segments (0x6da7c : word) = Some W_6da7c.
Proof. vm_refl. Qed.
Lemma D_6da7c : decode_any W_6da7c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da80 : bv 32 := 0x00000593.
Lemma F_6da80 : fetch_word Ubsan.M.loaded_segments (0x6da80 : word) = Some W_6da80.
Proof. vm_refl. Qed.
Lemma D_6da80 : decode_any W_6da80 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da84 : bv 32 := 0x451b00ef.
Lemma F_6da84 : fetch_word Ubsan.M.loaded_segments (0x6da84 : word) = Some W_6da84.
Proof. vm_refl. Qed.
Lemma D_6da84 : decode_any W_6da84 = Some (Jal 1 724048, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da88 : bv 32 := 0x00040513.
Lemma F_6da88 : fetch_word Ubsan.M.loaded_segments (0x6da88 : word) = Some W_6da88.
Proof. vm_refl. Qed.
Lemma D_6da88 : decode_any W_6da88 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da8c : bv 32 := 0x0400006f.
Lemma F_6da8c : fetch_word Ubsan.M.loaded_segments (0x6da8c : word) = Some W_6da8c.
Proof. vm_refl. Qed.
Lemma D_6da8c : decode_any W_6da8c = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da90 : bv 32 := 0x000b9517.
Lemma F_6da90 : fetch_word Ubsan.M.loaded_segments (0x6da90 : word) = Some W_6da90.
Proof. vm_refl. Qed.
Lemma D_6da90 : decode_any W_6da90 = Some (Auipc 10 185, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da94 : bv 32 := 0xfe053503.
Lemma F_6da94 : fetch_word Ubsan.M.loaded_segments (0x6da94 : word) = Some W_6da94.
Proof. vm_refl. Qed.
Lemma D_6da94 : decode_any W_6da94 = Some (Load SZ8 true 10 10 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da98 : bv 32 := 0x00052503.
Lemma F_6da98 : fetch_word Ubsan.M.loaded_segments (0x6da98 : word) = Some W_6da98.
Proof. vm_refl. Qed.
Lemma D_6da98 : decode_any W_6da98 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da9c : bv 32 := 0x00500593.
Lemma F_6da9c : fetch_word Ubsan.M.loaded_segments (0x6da9c : word) = Some W_6da9c.
Proof. vm_refl. Qed.
Lemma D_6da9c : decode_any W_6da9c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_6daa0 : bv 32 := 0x02a5c463.
Lemma F_6daa0 : fetch_word Ubsan.M.loaded_segments (0x6daa0 : word) = Some W_6daa0.
Proof. vm_refl. Qed.
Lemma D_6daa0 : decode_any W_6daa0 = Some (Branch BC_LT 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_6daa4 : bv 32 := 0xfffa5517.
Lemma F_6daa4 : fetch_word Ubsan.M.loaded_segments (0x6daa4 : word) = Some W_6daa4.
Proof. vm_refl. Qed.
Lemma D_6daa4 : decode_any W_6daa4 = Some (Auipc 10 1048485, 4%Z).
Proof. vm_refl. Qed.

Definition W_6daa8 : bv 32 := 0xfffa7597.
Lemma F_6daa8 : fetch_word Ubsan.M.loaded_segments (0x6daa8 : word) = Some W_6daa8.
Proof. vm_refl. Qed.
Lemma D_6daa8 : decode_any W_6daa8 = Some (Auipc 11 1048487, 4%Z).
Proof. vm_refl. Qed.

Definition W_6daac : bv 32 := 0xc3650513.
Lemma F_6daac : fetch_word Ubsan.M.loaded_segments (0x6daac : word) = Some W_6daac.
Proof. vm_refl. Qed.
Lemma D_6daac : decode_any W_6daac = Some (OpImm ALU_ADD 10 10 3126, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dab0 : bv 32 := 0x77458593.
Lemma F_6dab0 : fetch_word Ubsan.M.loaded_segments (0x6dab0 : word) = Some W_6dab0.
Proof. vm_refl. Qed.
Lemma D_6dab0 : decode_any W_6dab0 = Some (OpImm ALU_ADD 11 11 1908, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dab4 : bv 32 := 0x00000613.
Lemma F_6dab4 : fetch_word Ubsan.M.loaded_segments (0x6dab4 : word) = Some W_6dab4.
Proof. vm_refl. Qed.
Lemma D_6dab4 : decode_any W_6dab4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dab8 : bv 32 := 0x00813083.
Lemma F_6dab8 : fetch_word Ubsan.M.loaded_segments (0x6dab8 : word) = Some W_6dab8.
Proof. vm_refl. Qed.
Lemma D_6dab8 : decode_any W_6dab8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dabc : bv 32 := 0x00013403.
Lemma F_6dabc : fetch_word Ubsan.M.loaded_segments (0x6dabc : word) = Some W_6dabc.
Proof. vm_refl. Qed.
Lemma D_6dabc : decode_any W_6dabc = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dac0 : bv 32 := 0x01010113.
Lemma F_6dac0 : fetch_word Ubsan.M.loaded_segments (0x6dac0 : word) = Some W_6dac0.
Proof. vm_refl. Qed.
Lemma D_6dac0 : decode_any W_6dac0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dac4 : bv 32 := 0xc7df506f.
Lemma F_6dac4 : fetch_word Ubsan.M.loaded_segments (0x6dac4 : word) = Some W_6dac4.
Proof. vm_refl. Qed.
Lemma D_6dac4 : decode_any W_6dac4 = Some (Jal 0 2055292, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dacc : bv 32 := 0x00813083.
Lemma F_6dacc : fetch_word Ubsan.M.loaded_segments (0x6dacc : word) = Some W_6dacc.
Proof. vm_refl. Qed.
Lemma D_6dacc : decode_any W_6dacc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dad0 : bv 32 := 0x00013403.
Lemma F_6dad0 : fetch_word Ubsan.M.loaded_segments (0x6dad0 : word) = Some W_6dad0.
Proof. vm_refl. Qed.
Lemma D_6dad0 : decode_any W_6dad0 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dad4 : bv 32 := 0x01010113.
Lemma F_6dad4 : fetch_word Ubsan.M.loaded_segments (0x6dad4 : word) = Some W_6dad4.
Proof. vm_refl. Qed.
Lemma D_6dad4 : decode_any W_6dad4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dad8 : bv 32 := 0x00008067.
Lemma F_6dad8 : fetch_word Ubsan.M.loaded_segments (0x6dad8 : word) = Some W_6dad8.
Proof. vm_refl. Qed.
Lemma D_6dad8 : decode_any W_6dad8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dae0 : bv 32 := 0xfe010113.
Lemma F_6dae0 : fetch_word Ubsan.M.loaded_segments (0x6dae0 : word) = Some W_6dae0.
Proof. vm_refl. Qed.
Lemma D_6dae0 : decode_any W_6dae0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dae4 : bv 32 := 0x00113c23.
Lemma F_6dae4 : fetch_word Ubsan.M.loaded_segments (0x6dae4 : word) = Some W_6dae4.
Proof. vm_refl. Qed.
Lemma D_6dae4 : decode_any W_6dae4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dae8 : bv 32 := 0x00813823.
Lemma F_6dae8 : fetch_word Ubsan.M.loaded_segments (0x6dae8 : word) = Some W_6dae8.
Proof. vm_refl. Qed.
Lemma D_6dae8 : decode_any W_6dae8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6daec : bv 32 := 0x00913423.
Lemma F_6daec : fetch_word Ubsan.M.loaded_segments (0x6daec : word) = Some W_6daec.
Proof. vm_refl. Qed.
Lemma D_6daec : decode_any W_6daec = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6daf0 : bv 32 := 0x00058493.
Lemma F_6daf0 : fetch_word Ubsan.M.loaded_segments (0x6daf0 : word) = Some W_6daf0.
Proof. vm_refl. Qed.
Lemma D_6daf0 : decode_any W_6daf0 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6daf4 : bv 32 := 0x134000ef.
Lemma F_6daf4 : fetch_word Ubsan.M.loaded_segments (0x6daf4 : word) = Some W_6daf4.
Proof. vm_refl. Qed.
Lemma D_6daf4 : decode_any W_6daf4 = Some (Jal 1 308, 4%Z).
Proof. vm_refl. Qed.

Definition W_6daf8 : bv 32 := 0x04050863.
Lemma F_6daf8 : fetch_word Ubsan.M.loaded_segments (0x6daf8 : word) = Some W_6daf8.
Proof. vm_refl. Qed.
Lemma D_6daf8 : decode_any W_6daf8 = Some (Branch BC_EQ 10 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dafc : bv 32 := 0x00050413.
Lemma F_6dafc : fetch_word Ubsan.M.loaded_segments (0x6dafc : word) = Some W_6dafc.
Proof. vm_refl. Qed.
Lemma D_6dafc : decode_any W_6dafc = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db00 : bv 32 := 0x00757513.
Lemma F_6db00 : fetch_word Ubsan.M.loaded_segments (0x6db00 : word) = Some W_6db00.
Proof. vm_refl. Qed.
Lemma D_6db00 : decode_any W_6db00 = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db04 : bv 32 := 0x12051063.
Lemma F_6db04 : fetch_word Ubsan.M.loaded_segments (0x6db04 : word) = Some W_6db04.
Proof. vm_refl. Qed.
Lemma D_6db04 : decode_any W_6db04 = Some (Branch BC_NE 10 0 288, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db08 : bv 32 := 0x01042503.
Lemma F_6db08 : fetch_word Ubsan.M.loaded_segments (0x6db08 : word) = Some W_6db08.
Proof. vm_refl. Qed.
Lemma D_6db08 : decode_any W_6db08 = Some (Load SZ4 true 10 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db0c : bv 32 := 0x00251513.
Lemma F_6db0c : fetch_word Ubsan.M.loaded_segments (0x6db0c : word) = Some W_6db0c.
Proof. vm_refl. Qed.
Lemma D_6db0c : decode_any W_6db0c = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db10 : bv 32 := 0x029515b3.
Lemma F_6db10 : fetch_word Ubsan.M.loaded_segments (0x6db10 : word) = Some W_6db10.
Proof. vm_refl. Qed.
Lemma D_6db10 : decode_any W_6db10 = Some (Mul M_MULH 11 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db14 : bv 32 := 0x02950533.
Lemma F_6db14 : fetch_word Ubsan.M.loaded_segments (0x6db14 : word) = Some W_6db14.
Proof. vm_refl. Qed.
Lemma D_6db14 : decode_any W_6db14 = Some (Mul M_MUL 10 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db18 : bv 32 := 0x43f55613.
Lemma F_6db18 : fetch_word Ubsan.M.loaded_segments (0x6db18 : word) = Some W_6db18.
Proof. vm_refl. Qed.
Lemma D_6db18 : decode_any W_6db18 = Some (ShiftImm ALU_SRA 12 10 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db1c : bv 32 := 0x10c59463.
Lemma F_6db1c : fetch_word Ubsan.M.loaded_segments (0x6db1c : word) = Some W_6db1c.
Proof. vm_refl. Qed.
Lemma D_6db1c : decode_any W_6db1c = Some (Branch BC_NE 11 12 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db20 : bv 32 := 0x000ba597.
Lemma F_6db20 : fetch_word Ubsan.M.loaded_segments (0x6db20 : word) = Some W_6db20.
Proof. vm_refl. Qed.
Lemma D_6db20 : decode_any W_6db20 = Some (Auipc 11 186, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db24 : bv 32 := 0x15858493.
Lemma F_6db24 : fetch_word Ubsan.M.loaded_segments (0x6db24 : word) = Some W_6db24.
Proof. vm_refl. Qed.
Lemma D_6db24 : decode_any W_6db24 = Some (OpImm ALU_ADD 9 11 344, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db28 : bv 32 := 0x0004b583.
Lemma F_6db28 : fetch_word Ubsan.M.loaded_segments (0x6db28 : word) = Some W_6db28.
Proof. vm_refl. Qed.
Lemma D_6db28 : decode_any W_6db28 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db2c : bv 32 := 0x000580e7.
Lemma F_6db2c : fetch_word Ubsan.M.loaded_segments (0x6db2c : word) = Some W_6db2c.
Proof. vm_refl. Qed.
Lemma D_6db2c : decode_any W_6db2c = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db30 : bv 32 := 0x04050a63.
Lemma F_6db30 : fetch_word Ubsan.M.loaded_segments (0x6db30 : word) = Some W_6db30.
Proof. vm_refl. Qed.
Lemma D_6db30 : decode_any W_6db30 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db34 : bv 32 := 0x02a43c23.
Lemma F_6db34 : fetch_word Ubsan.M.loaded_segments (0x6db34 : word) = Some W_6db34.
Proof. vm_refl. Qed.
Lemma D_6db34 : decode_any W_6db34 = Some (Store SZ8 8 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db38 : bv 32 := 0x00040513.
Lemma F_6db38 : fetch_word Ubsan.M.loaded_segments (0x6db38 : word) = Some W_6db38.
Proof. vm_refl. Qed.
Lemma D_6db38 : decode_any W_6db38 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db3c : bv 32 := 0x00000593.
Lemma F_6db3c : fetch_word Ubsan.M.loaded_segments (0x6db3c : word) = Some W_6db3c.
Proof. vm_refl. Qed.
Lemma D_6db3c : decode_any W_6db3c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db40 : bv 32 := 0x715020ef.
Lemma F_6db40 : fetch_word Ubsan.M.loaded_segments (0x6db40 : word) = Some W_6db40.
Proof. vm_refl. Qed.
Lemma D_6db40 : decode_any W_6db40 = Some (Jal 1 12052, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db44 : bv 32 := 0x0c80006f.
Lemma F_6db44 : fetch_word Ubsan.M.loaded_segments (0x6db44 : word) = Some W_6db44.
Proof. vm_refl. Qed.
Lemma D_6db44 : decode_any W_6db44 = Some (Jal 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db48 : bv 32 := 0x000b9517.
Lemma F_6db48 : fetch_word Ubsan.M.loaded_segments (0x6db48 : word) = Some W_6db48.
Proof. vm_refl. Qed.
Lemma D_6db48 : decode_any W_6db48 = Some (Auipc 10 185, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db4c : bv 32 := 0xf2853503.
Lemma F_6db4c : fetch_word Ubsan.M.loaded_segments (0x6db4c : word) = Some W_6db4c.
Proof. vm_refl. Qed.
Lemma D_6db4c : decode_any W_6db4c = Some (Load SZ8 true 10 10 3880, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db50 : bv 32 := 0x00052503.
Lemma F_6db50 : fetch_word Ubsan.M.loaded_segments (0x6db50 : word) = Some W_6db50.
Proof. vm_refl. Qed.
Lemma D_6db50 : decode_any W_6db50 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db54 : bv 32 := 0x00500593.
Lemma F_6db54 : fetch_word Ubsan.M.loaded_segments (0x6db54 : word) = Some W_6db54.
Proof. vm_refl. Qed.
Lemma D_6db54 : decode_any W_6db54 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db58 : bv 32 := 0x0aa5c863.
Lemma F_6db58 : fetch_word Ubsan.M.loaded_segments (0x6db58 : word) = Some W_6db58.
Proof. vm_refl. Qed.
Lemma D_6db58 : decode_any W_6db58 = Some (Branch BC_LT 11 10 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db5c : bv 32 := 0xfffa5517.
Lemma F_6db5c : fetch_word Ubsan.M.loaded_segments (0x6db5c : word) = Some W_6db5c.
Proof. vm_refl. Qed.
Lemma D_6db5c : decode_any W_6db5c = Some (Auipc 10 1048485, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db60 : bv 32 := 0xfffa6597.
Lemma F_6db60 : fetch_word Ubsan.M.loaded_segments (0x6db60 : word) = Some W_6db60.
Proof. vm_refl. Qed.
Lemma D_6db60 : decode_any W_6db60 = Some (Auipc 11 1048486, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db64 : bv 32 := 0xb7e50513.
Lemma F_6db64 : fetch_word Ubsan.M.loaded_segments (0x6db64 : word) = Some W_6db64.
Proof. vm_refl. Qed.
Lemma D_6db64 : decode_any W_6db64 = Some (OpImm ALU_ADD 10 10 2942, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db68 : bv 32 := 0x12158593.
Lemma F_6db68 : fetch_word Ubsan.M.loaded_segments (0x6db68 : word) = Some W_6db68.
Proof. vm_refl. Qed.
Lemma D_6db68 : decode_any W_6db68 = Some (OpImm ALU_ADD 11 11 289, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db6c : bv 32 := 0x00000613.
Lemma F_6db6c : fetch_word Ubsan.M.loaded_segments (0x6db6c : word) = Some W_6db6c.
Proof. vm_refl. Qed.
Lemma D_6db6c : decode_any W_6db6c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db70 : bv 32 := 0x01813083.
Lemma F_6db70 : fetch_word Ubsan.M.loaded_segments (0x6db70 : word) = Some W_6db70.
Proof. vm_refl. Qed.
Lemma D_6db70 : decode_any W_6db70 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db74 : bv 32 := 0x01013403.
Lemma F_6db74 : fetch_word Ubsan.M.loaded_segments (0x6db74 : word) = Some W_6db74.
Proof. vm_refl. Qed.
Lemma D_6db74 : decode_any W_6db74 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db78 : bv 32 := 0x00813483.
Lemma F_6db78 : fetch_word Ubsan.M.loaded_segments (0x6db78 : word) = Some W_6db78.
Proof. vm_refl. Qed.
Lemma D_6db78 : decode_any W_6db78 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db7c : bv 32 := 0x02010113.
Lemma F_6db7c : fetch_word Ubsan.M.loaded_segments (0x6db7c : word) = Some W_6db7c.
Proof. vm_refl. Qed.
Lemma D_6db7c : decode_any W_6db7c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db80 : bv 32 := 0xbc1f506f.
Lemma F_6db80 : fetch_word Ubsan.M.loaded_segments (0x6db80 : word) = Some W_6db80.
Proof. vm_refl. Qed.
Lemma D_6db80 : decode_any W_6db80 = Some (Jal 0 2055104, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db84 : bv 32 := 0x01440513.
Lemma F_6db84 : fetch_word Ubsan.M.loaded_segments (0x6db84 : word) = Some W_6db84.
Proof. vm_refl. Qed.
Lemma D_6db84 : decode_any W_6db84 = Some (OpImm ALU_ADD 10 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db88 : bv 32 := 0xfff00593.
Lemma F_6db88 : fetch_word Ubsan.M.loaded_segments (0x6db88 : word) = Some W_6db88.
Proof. vm_refl. Qed.
Lemma D_6db88 : decode_any W_6db88 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db8c : bv 32 := 0x06b5252f.
Lemma F_6db8c : fetch_word Ubsan.M.loaded_segments (0x6db8c : word) = Some W_6db8c.
Proof. vm_refl. Qed.
Lemma D_6db8c : decode_any W_6db8c = Some (Amo AMO_ADD AW true true 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db90 : bv 32 := 0x00100593.
Lemma F_6db90 : fetch_word Ubsan.M.loaded_segments (0x6db90 : word) = Some W_6db90.
Proof. vm_refl. Qed.
Lemma D_6db90 : decode_any W_6db90 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db94 : bv 32 := 0x04b51063.
Lemma F_6db94 : fetch_word Ubsan.M.loaded_segments (0x6db94 : word) = Some W_6db94.
Proof. vm_refl. Qed.
Lemma D_6db94 : decode_any W_6db94 = Some (Branch BC_NE 10 11 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db98 : bv 32 := 0x03843503.
Lemma F_6db98 : fetch_word Ubsan.M.loaded_segments (0x6db98 : word) = Some W_6db98.
Proof. vm_refl. Qed.
Lemma D_6db98 : decode_any W_6db98 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_6db9c : bv 32 := 0x00050663.
Lemma F_6db9c : fetch_word Ubsan.M.loaded_segments (0x6db9c : word) = Some W_6db9c.
Proof. vm_refl. Qed.
Lemma D_6db9c : decode_any W_6db9c = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dba8 : bv 32 := 0x02843503.
Lemma F_6dba8 : fetch_word Ubsan.M.loaded_segments (0x6dba8 : word) = Some W_6dba8.
Proof. vm_refl. Qed.
Lemma D_6dba8 : decode_any W_6dba8 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dbac : bv 32 := 0x00050463.
Lemma F_6dbac : fetch_word Ubsan.M.loaded_segments (0x6dbac : word) = Some W_6dbac.
Proof. vm_refl. Qed.
Lemma D_6dbac : decode_any W_6dbac = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dbb4 : bv 32 := 0x03043503.
Lemma F_6dbb4 : fetch_word Ubsan.M.loaded_segments (0x6dbb4 : word) = Some W_6dbb4.
Proof. vm_refl. Qed.
Lemma D_6dbb4 : decode_any W_6dbb4 = Some (Load SZ8 true 10 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dbb8 : bv 32 := 0x00a13023.
Lemma F_6dbb8 : fetch_word Ubsan.M.loaded_segments (0x6dbb8 : word) = Some W_6dbb8.
Proof. vm_refl. Qed.
Lemma D_6dbb8 : decode_any W_6dbb8 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dbbc : bv 32 := 0x00050863.
Lemma F_6dbbc : fetch_word Ubsan.M.loaded_segments (0x6dbbc : word) = Some W_6dbbc.
Proof. vm_refl. Qed.
Lemma D_6dbbc : decode_any W_6dbbc = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dbcc : bv 32 := 0x00040513.
Lemma F_6dbcc : fetch_word Ubsan.M.loaded_segments (0x6dbcc : word) = Some W_6dbcc.
Proof. vm_refl. Qed.
Lemma D_6dbcc : decode_any W_6dbcc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dbd0 : bv 32 := 0x449a00ef.
Lemma F_6dbd0 : fetch_word Ubsan.M.loaded_segments (0x6dbd0 : word) = Some W_6dbd0.
Proof. vm_refl. Qed.
Lemma D_6dbd0 : decode_any W_6dbd0 = Some (Jal 1 658504, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dbd4 : bv 32 := 0x000b9517.
Lemma F_6dbd4 : fetch_word Ubsan.M.loaded_segments (0x6dbd4 : word) = Some W_6dbd4.
Proof. vm_refl. Qed.
Lemma D_6dbd4 : decode_any W_6dbd4 = Some (Auipc 10 185, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dbd8 : bv 32 := 0xe9c53503.
Lemma F_6dbd8 : fetch_word Ubsan.M.loaded_segments (0x6dbd8 : word) = Some W_6dbd8.
Proof. vm_refl. Qed.
Lemma D_6dbd8 : decode_any W_6dbd8 = Some (Load SZ8 true 10 10 3740, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dbdc : bv 32 := 0x00052503.
Lemma F_6dbdc : fetch_word Ubsan.M.loaded_segments (0x6dbdc : word) = Some W_6dbdc.
Proof. vm_refl. Qed.
Lemma D_6dbdc : decode_any W_6dbdc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dbe0 : bv 32 := 0x00500593.
Lemma F_6dbe0 : fetch_word Ubsan.M.loaded_segments (0x6dbe0 : word) = Some W_6dbe0.
Proof. vm_refl. Qed.
Lemma D_6dbe0 : decode_any W_6dbe0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dbe4 : bv 32 := 0x02a5c263.
Lemma F_6dbe4 : fetch_word Ubsan.M.loaded_segments (0x6dbe4 : word) = Some W_6dbe4.
Proof. vm_refl. Qed.
Lemma D_6dbe4 : decode_any W_6dbe4 = Some (Branch BC_LT 11 10 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dbe8 : bv 32 := 0xfffae517.
Lemma F_6dbe8 : fetch_word Ubsan.M.loaded_segments (0x6dbe8 : word) = Some W_6dbe8.
Proof. vm_refl. Qed.
Lemma D_6dbe8 : decode_any W_6dbe8 = Some (Auipc 10 1048494, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dbec : bv 32 := 0xfffa6597.
Lemma F_6dbec : fetch_word Ubsan.M.loaded_segments (0x6dbec : word) = Some W_6dbec.
Proof. vm_refl. Qed.
Lemma D_6dbec : decode_any W_6dbec = Some (Auipc 11 1048486, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dbf0 : bv 32 := 0xdab50513.
Lemma F_6dbf0 : fetch_word Ubsan.M.loaded_segments (0x6dbf0 : word) = Some W_6dbf0.
Proof. vm_refl. Qed.
Lemma D_6dbf0 : decode_any W_6dbf0 = Some (OpImm ALU_ADD 10 10 3499, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dbf4 : bv 32 := 0x09558593.
Lemma F_6dbf4 : fetch_word Ubsan.M.loaded_segments (0x6dbf4 : word) = Some W_6dbf4.
Proof. vm_refl. Qed.
Lemma D_6dbf4 : decode_any W_6dbf4 = Some (OpImm ALU_ADD 11 11 149, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dbf8 : bv 32 := 0x00000613.
Lemma F_6dbf8 : fetch_word Ubsan.M.loaded_segments (0x6dbf8 : word) = Some W_6dbf8.
Proof. vm_refl. Qed.
Lemma D_6dbf8 : decode_any W_6dbf8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dbfc : bv 32 := 0xb45f50ef.
Lemma F_6dbfc : fetch_word Ubsan.M.loaded_segments (0x6dbfc : word) = Some W_6dbfc.
Proof. vm_refl. Qed.
Lemma D_6dbfc : decode_any W_6dbfc = Some (Jal 1 2054980, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dc00 : bv 32 := 0x00050413.
Lemma F_6dc00 : fetch_word Ubsan.M.loaded_segments (0x6dc00 : word) = Some W_6dc00.
Proof. vm_refl. Qed.
Lemma D_6dc00 : decode_any W_6dc00 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dc04 : bv 32 := 0x0080006f.
Lemma F_6dc04 : fetch_word Ubsan.M.loaded_segments (0x6dc04 : word) = Some W_6dc04.
Proof. vm_refl. Qed.
Lemma D_6dc04 : decode_any W_6dc04 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dc0c : bv 32 := 0x00040513.
Lemma F_6dc0c : fetch_word Ubsan.M.loaded_segments (0x6dc0c : word) = Some W_6dc0c.
Proof. vm_refl. Qed.
Lemma D_6dc0c : decode_any W_6dc0c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dc10 : bv 32 := 0x01813083.
Lemma F_6dc10 : fetch_word Ubsan.M.loaded_segments (0x6dc10 : word) = Some W_6dc10.
Proof. vm_refl. Qed.
Lemma D_6dc10 : decode_any W_6dc10 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dc14 : bv 32 := 0x01013403.
Lemma F_6dc14 : fetch_word Ubsan.M.loaded_segments (0x6dc14 : word) = Some W_6dc14.
Proof. vm_refl. Qed.
Lemma D_6dc14 : decode_any W_6dc14 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dc18 : bv 32 := 0x00813483.
Lemma F_6dc18 : fetch_word Ubsan.M.loaded_segments (0x6dc18 : word) = Some W_6dc18.
Proof. vm_refl. Qed.
Lemma D_6dc18 : decode_any W_6dc18 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dc1c : bv 32 := 0x02010113.
Lemma F_6dc1c : fetch_word Ubsan.M.loaded_segments (0x6dc1c : word) = Some W_6dc1c.
Proof. vm_refl. Qed.
Lemma D_6dc1c : decode_any W_6dc1c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dc20 : bv 32 := 0x00008067.
Lemma F_6dc20 : fetch_word Ubsan.M.loaded_segments (0x6dc20 : word) = Some W_6dc20.
Proof. vm_refl. Qed.
Lemma D_6dc20 : decode_any W_6dc20 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_3ad78 : bv 32 := 0xf5010113.
Lemma F_3ad78 : fetch_word Ubsan.M.loaded_segments (0x3ad78 : word) = Some W_3ad78.
Proof. vm_refl. Qed.
Lemma D_3ad78 : decode_any W_3ad78 = Some (OpImm ALU_ADD 2 2 3920, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ad7c : bv 32 := 0x0a113423.
Lemma F_3ad7c : fetch_word Ubsan.M.loaded_segments (0x3ad7c : word) = Some W_3ad7c.
Proof. vm_refl. Qed.
Lemma D_3ad7c : decode_any W_3ad7c = Some (Store SZ8 2 1 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ad80 : bv 32 := 0x0a813023.
Lemma F_3ad80 : fetch_word Ubsan.M.loaded_segments (0x3ad80 : word) = Some W_3ad80.
Proof. vm_refl. Qed.
Lemma D_3ad80 : decode_any W_3ad80 = Some (Store SZ8 2 8 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ad84 : bv 32 := 0x08913c23.
Lemma F_3ad84 : fetch_word Ubsan.M.loaded_segments (0x3ad84 : word) = Some W_3ad84.
Proof. vm_refl. Qed.
Lemma D_3ad84 : decode_any W_3ad84 = Some (Store SZ8 2 9 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ad88 : bv 32 := 0x09213823.
Lemma F_3ad88 : fetch_word Ubsan.M.loaded_segments (0x3ad88 : word) = Some W_3ad88.
Proof. vm_refl. Qed.
Lemma D_3ad88 : decode_any W_3ad88 = Some (Store SZ8 2 18 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ad8c : bv 32 := 0x09313423.
Lemma F_3ad8c : fetch_word Ubsan.M.loaded_segments (0x3ad8c : word) = Some W_3ad8c.
Proof. vm_refl. Qed.
Lemma D_3ad8c : decode_any W_3ad8c = Some (Store SZ8 2 19 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ad90 : bv 32 := 0x09413023.
Lemma F_3ad90 : fetch_word Ubsan.M.loaded_segments (0x3ad90 : word) = Some W_3ad90.
Proof. vm_refl. Qed.
Lemma D_3ad90 : decode_any W_3ad90 = Some (Store SZ8 2 20 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ad94 : bv 32 := 0x07513c23.
Lemma F_3ad94 : fetch_word Ubsan.M.loaded_segments (0x3ad94 : word) = Some W_3ad94.
Proof. vm_refl. Qed.
Lemma D_3ad94 : decode_any W_3ad94 = Some (Store SZ8 2 21 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ad98 : bv 32 := 0x07613823.
Lemma F_3ad98 : fetch_word Ubsan.M.loaded_segments (0x3ad98 : word) = Some W_3ad98.
Proof. vm_refl. Qed.
Lemma D_3ad98 : decode_any W_3ad98 = Some (Store SZ8 2 22 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ad9c : bv 32 := 0x07713423.
Lemma F_3ad9c : fetch_word Ubsan.M.loaded_segments (0x3ad9c : word) = Some W_3ad9c.
Proof. vm_refl. Qed.
Lemma D_3ad9c : decode_any W_3ad9c = Some (Store SZ8 2 23 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ada0 : bv 32 := 0x07813023.
Lemma F_3ada0 : fetch_word Ubsan.M.loaded_segments (0x3ada0 : word) = Some W_3ada0.
Proof. vm_refl. Qed.
Lemma D_3ada0 : decode_any W_3ada0 = Some (Store SZ8 2 24 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ada4 : bv 32 := 0x05913c23.
Lemma F_3ada4 : fetch_word Ubsan.M.loaded_segments (0x3ada4 : word) = Some W_3ada4.
Proof. vm_refl. Qed.
Lemma D_3ada4 : decode_any W_3ada4 = Some (Store SZ8 2 25 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ada8 : bv 32 := 0x05a13823.
Lemma F_3ada8 : fetch_word Ubsan.M.loaded_segments (0x3ada8 : word) = Some W_3ada8.
Proof. vm_refl. Qed.
Lemma D_3ada8 : decode_any W_3ada8 = Some (Store SZ8 2 26 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_3adac : bv 32 := 0x05b13423.
Lemma F_3adac : fetch_word Ubsan.M.loaded_segments (0x3adac : word) = Some W_3adac.
Proof. vm_refl. Qed.
Lemma D_3adac : decode_any W_3adac = Some (Store SZ8 2 27 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_3adb0 : bv 32 := 0x16050863.
Lemma F_3adb0 : fetch_word Ubsan.M.loaded_segments (0x3adb0 : word) = Some W_3adb0.
Proof. vm_refl. Qed.
Lemma D_3adb0 : decode_any W_3adb0 = Some (Branch BC_EQ 10 0 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_3adb4 : bv 32 := 0x00060413.
Lemma F_3adb4 : fetch_word Ubsan.M.loaded_segments (0x3adb4 : word) = Some W_3adb4.
Proof. vm_refl. Qed.
Lemma D_3adb4 : decode_any W_3adb4 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3adb8 : bv 32 := 0x00058913.
Lemma F_3adb8 : fetch_word Ubsan.M.loaded_segments (0x3adb8 : word) = Some W_3adb8.
Proof. vm_refl. Qed.
Lemma D_3adb8 : decode_any W_3adb8 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3adbc : bv 32 := 0x00050493.
Lemma F_3adbc : fetch_word Ubsan.M.loaded_segments (0x3adbc : word) = Some W_3adbc.
Proof. vm_refl. Qed.
Lemma D_3adbc : decode_any W_3adbc = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3adc0 : bv 32 := 0xb0ddf0ef.
Lemma F_3adc0 : fetch_word Ubsan.M.loaded_segments (0x3adc0 : word) = Some W_3adc0.
Proof. vm_refl. Qed.
Lemma D_3adc0 : decode_any W_3adc0 = Some (Jal 1 1964812, 4%Z).
Proof. vm_refl. Qed.

Definition W_3adc4 : bv 32 := 0x00800593.
Lemma F_3adc4 : fetch_word Ubsan.M.loaded_segments (0x3adc4 : word) = Some W_3adc4.
Proof. vm_refl. Qed.
Lemma D_3adc4 : decode_any W_3adc4 = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3adc8 : bv 32 := 0x18b51063.
Lemma F_3adc8 : fetch_word Ubsan.M.loaded_segments (0x3adc8 : word) = Some W_3adc8.
Proof. vm_refl. Qed.
Lemma D_3adc8 : decode_any W_3adc8 = Some (Branch BC_NE 10 11 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_3adcc : bv 32 := 0x04410593.
Lemma F_3adcc : fetch_word Ubsan.M.loaded_segments (0x3adcc : word) = Some W_3adcc.
Proof. vm_refl. Qed.
Lemma D_3adcc : decode_any W_3adcc = Some (OpImm ALU_ADD 11 2 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_3add0 : bv 32 := 0x04010613.
Lemma F_3add0 : fetch_word Ubsan.M.loaded_segments (0x3add0 : word) = Some W_3add0.
Proof. vm_refl. Qed.
Lemma D_3add0 : decode_any W_3add0 = Some (OpImm ALU_ADD 12 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_3add4 : bv 32 := 0x03c10693.
Lemma F_3add4 : fetch_word Ubsan.M.loaded_segments (0x3add4 : word) = Some W_3add4.
Proof. vm_refl. Qed.
Lemma D_3add4 : decode_any W_3add4 = Some (OpImm ALU_ADD 13 2 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_3add8 : bv 32 := 0x00048513.
Lemma F_3add8 : fetch_word Ubsan.M.loaded_segments (0x3add8 : word) = Some W_3add8.
Proof. vm_refl. Qed.
Lemma D_3add8 : decode_any W_3add8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3addc : bv 32 := 0xd5dde0ef.
Lemma F_3addc : fetch_word Ubsan.M.loaded_segments (0x3addc : word) = Some W_3addc.
Proof. vm_refl. Qed.
Lemma D_3addc : decode_any W_3addc = Some (Jal 1 1961308, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ade0 : bv 32 := 0x22090263.
Lemma F_3ade0 : fetch_word Ubsan.M.loaded_segments (0x3ade0 : word) = Some W_3ade0.
Proof. vm_refl. Qed.
Lemma D_3ade0 : decode_any W_3ade0 = Some (Branch BC_EQ 18 0 548, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ade4 : bv 32 := 0x03410593.
Lemma F_3ade4 : fetch_word Ubsan.M.loaded_segments (0x3ade4 : word) = Some W_3ade4.
Proof. vm_refl. Qed.
Lemma D_3ade4 : decode_any W_3ade4 = Some (OpImm ALU_ADD 11 2 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ade8 : bv 32 := 0x03810613.
Lemma F_3ade8 : fetch_word Ubsan.M.loaded_segments (0x3ade8 : word) = Some W_3ade8.
Proof. vm_refl. Qed.
Lemma D_3ade8 : decode_any W_3ade8 = Some (OpImm ALU_ADD 12 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_3adec : bv 32 := 0x00090513.
Lemma F_3adec : fetch_word Ubsan.M.loaded_segments (0x3adec : word) = Some W_3adec.
Proof. vm_refl. Qed.
Lemma D_3adec : decode_any W_3adec = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3adf0 : bv 32 := 0x00000693.
Lemma F_3adf0 : fetch_word Ubsan.M.loaded_segments (0x3adf0 : word) = Some W_3adf0.
Proof. vm_refl. Qed.
Lemma D_3adf0 : decode_any W_3adf0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3adf4 : bv 32 := 0x00000713.
Lemma F_3adf4 : fetch_word Ubsan.M.loaded_segments (0x3adf4 : word) = Some W_3adf4.
Proof. vm_refl. Qed.
Lemma D_3adf4 : decode_any W_3adf4 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3adf8 : bv 32 := 0xa69fd0ef.
Lemma F_3adf8 : fetch_word Ubsan.M.loaded_segments (0x3adf8 : word) = Some W_3adf8.
Proof. vm_refl. Qed.
Lemma D_3adf8 : decode_any W_3adf8 = Some (Jal 1 2087528, 4%Z).
Proof. vm_refl. Qed.

Definition W_3adfc : bv 32 := 0x03812503.
Lemma F_3adfc : fetch_word Ubsan.M.loaded_segments (0x3adfc : word) = Some W_3adfc.
Proof. vm_refl. Qed.
Lemma D_3adfc : decode_any W_3adfc = Some (Load SZ4 true 10 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae00 : bv 32 := 0x400005b7.
Lemma F_3ae00 : fetch_word Ubsan.M.loaded_segments (0x3ae00 : word) = Some W_3ae00.
Proof. vm_refl. Qed.
Lemma D_3ae00 : decode_any W_3ae00 = Some (Lui 11 262144, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae04 : bv 32 := 0x00b505bb.
Lemma F_3ae04 : fetch_word Ubsan.M.loaded_segments (0x3ae04 : word) = Some W_3ae04.
Proof. vm_refl. Qed.
Lemma D_3ae04 : decode_any W_3ae04 = Some (Op32 ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae08 : bv 32 := 0x5c05c063.
Lemma F_3ae08 : fetch_word Ubsan.M.loaded_segments (0x3ae08 : word) = Some W_3ae08.
Proof. vm_refl. Qed.
Lemma D_3ae08 : decode_any W_3ae08 = Some (Branch BC_LT 11 0 1472, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae0c : bv 32 := 0x04412603.
Lemma F_3ae0c : fetch_word Ubsan.M.loaded_segments (0x3ae0c : word) = Some W_3ae0c.
Proof. vm_refl. Qed.
Lemma D_3ae0c : decode_any W_3ae0c = Some (Load SZ4 true 12 2 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae10 : bv 32 := 0x0015151b.
Lemma F_3ae10 : fetch_word Ubsan.M.loaded_segments (0x3ae10 : word) = Some W_3ae10.
Proof. vm_refl. Qed.
Lemma D_3ae10 : decode_any W_3ae10 = Some (ShiftImm32 ALU_SLL 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae14 : bv 32 := 0x18c55c63.
Lemma F_3ae14 : fetch_word Ubsan.M.loaded_segments (0x3ae14 : word) = Some W_3ae14.
Proof. vm_refl. Qed.
Lemma D_3ae14 : decode_any W_3ae14 = Some (Branch BC_GE 10 12 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae18 : bv 32 := 0x03412583.
Lemma F_3ae18 : fetch_word Ubsan.M.loaded_segments (0x3ae18 : word) = Some W_3ae18.
Proof. vm_refl. Qed.
Lemma D_3ae18 : decode_any W_3ae18 = Some (Load SZ4 true 11 2 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae1c : bv 32 := 0x400006b7.
Lemma F_3ae1c : fetch_word Ubsan.M.loaded_segments (0x3ae1c : word) = Some W_3ae1c.
Proof. vm_refl. Qed.
Lemma D_3ae1c : decode_any W_3ae1c = Some (Lui 13 262144, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae20 : bv 32 := 0x00d586bb.
Lemma F_3ae20 : fetch_word Ubsan.M.loaded_segments (0x3ae20 : word) = Some W_3ae20.
Proof. vm_refl. Qed.
Lemma D_3ae20 : decode_any W_3ae20 = Some (Op32 ALU_ADD 13 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae24 : bv 32 := 0x5a06c263.
Lemma F_3ae24 : fetch_word Ubsan.M.loaded_segments (0x3ae24 : word) = Some W_3ae24.
Proof. vm_refl. Qed.
Lemma D_3ae24 : decode_any W_3ae24 = Some (Branch BC_LT 13 0 1444, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae28 : bv 32 := 0x04012683.
Lemma F_3ae28 : fetch_word Ubsan.M.loaded_segments (0x3ae28 : word) = Some W_3ae28.
Proof. vm_refl. Qed.
Lemma D_3ae28 : decode_any W_3ae28 = Some (Load SZ4 true 13 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae2c : bv 32 := 0x0015959b.
Lemma F_3ae2c : fetch_word Ubsan.M.loaded_segments (0x3ae2c : word) = Some W_3ae2c.
Proof. vm_refl. Qed.
Lemma D_3ae2c : decode_any W_3ae2c = Some (ShiftImm32 ALU_SLL 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae30 : bv 32 := 0x16d5de63.
Lemma F_3ae30 : fetch_word Ubsan.M.loaded_segments (0x3ae30 : word) = Some W_3ae30.
Proof. vm_refl. Qed.
Lemma D_3ae30 : decode_any W_3ae30 = Some (Branch BC_GE 11 13 380, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae34 : bv 32 := 0x50040663.
Lemma F_3ae34 : fetch_word Ubsan.M.loaded_segments (0x3ae34 : word) = Some W_3ae34.
Proof. vm_refl. Qed.
Lemma D_3ae34 : decode_any W_3ae34 = Some (Branch BC_EQ 8 0 1292, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae38 : bv 32 := 0x00747513.
Lemma F_3ae38 : fetch_word Ubsan.M.loaded_segments (0x3ae38 : word) = Some W_3ae38.
Proof. vm_refl. Qed.
Lemma D_3ae38 : decode_any W_3ae38 = Some (OpImm ALU_AND 10 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae3c : bv 32 := 0x58051663.
Lemma F_3ae3c : fetch_word Ubsan.M.loaded_segments (0x3ae3c : word) = Some W_3ae3c.
Proof. vm_refl. Qed.
Lemma D_3ae3c : decode_any W_3ae3c = Some (Branch BC_NE 10 0 1420, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae40 : bv 32 := 0x00442503.
Lemma F_3ae40 : fetch_word Ubsan.M.loaded_segments (0x3ae40 : word) = Some W_3ae40.
Proof. vm_refl. Qed.
Lemma D_3ae40 : decode_any W_3ae40 = Some (Load SZ4 true 10 8 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae44 : bv 32 := 0x10000593.
Lemma F_3ae44 : fetch_word Ubsan.M.loaded_segments (0x3ae44 : word) = Some W_3ae44.
Proof. vm_refl. Qed.
Lemma D_3ae44 : decode_any W_3ae44 = Some (OpImm ALU_ADD 11 0 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae48 : bv 32 := 0x1eb51663.
Lemma F_3ae48 : fetch_word Ubsan.M.loaded_segments (0x3ae48 : word) = Some W_3ae48.
Proof. vm_refl. Qed.
Lemma D_3ae48 : decode_any W_3ae48 = Some (Branch BC_NE 10 11 492, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae4c : bv 32 := 0x00042503.
Lemma F_3ae4c : fetch_word Ubsan.M.loaded_segments (0x3ae4c : word) = Some W_3ae4c.
Proof. vm_refl. Qed.
Lemma D_3ae4c : decode_any W_3ae4c = Some (Load SZ4 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae50 : bv 32 := 0x00100593.
Lemma F_3ae50 : fetch_word Ubsan.M.loaded_segments (0x3ae50 : word) = Some W_3ae50.
Proof. vm_refl. Qed.
Lemma D_3ae50 : decode_any W_3ae50 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae54 : bv 32 := 0x1eb51063.
Lemma F_3ae54 : fetch_word Ubsan.M.loaded_segments (0x3ae54 : word) = Some W_3ae54.
Proof. vm_refl. Qed.
Lemma D_3ae54 : decode_any W_3ae54 = Some (Branch BC_NE 10 11 480, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae58 : bv 32 := 0x00090513.
Lemma F_3ae58 : fetch_word Ubsan.M.loaded_segments (0x3ae58 : word) = Some W_3ae58.
Proof. vm_refl. Qed.
Lemma D_3ae58 : decode_any W_3ae58 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae5c : bv 32 := 0xff9fd0ef.
Lemma F_3ae5c : fetch_word Ubsan.M.loaded_segments (0x3ae5c : word) = Some W_3ae5c.
Proof. vm_refl. Qed.
Lemma D_3ae5c : decode_any W_3ae5c = Some (Jal 1 2088952, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae60 : bv 32 := 0x02a13023.
Lemma F_3ae60 : fetch_word Ubsan.M.loaded_segments (0x3ae60 : word) = Some W_3ae60.
Proof. vm_refl. Qed.
Lemma D_3ae60 : decode_any W_3ae60 = Some (Store SZ8 2 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae64 : bv 32 := 0x03410593.
Lemma F_3ae64 : fetch_word Ubsan.M.loaded_segments (0x3ae64 : word) = Some W_3ae64.
Proof. vm_refl. Qed.
Lemma D_3ae64 : decode_any W_3ae64 = Some (OpImm ALU_ADD 11 2 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae68 : bv 32 := 0x03810613.
Lemma F_3ae68 : fetch_word Ubsan.M.loaded_segments (0x3ae68 : word) = Some W_3ae68.
Proof. vm_refl. Qed.
Lemma D_3ae68 : decode_any W_3ae68 = Some (OpImm ALU_ADD 12 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae6c : bv 32 := 0x02c10693.
Lemma F_3ae6c : fetch_word Ubsan.M.loaded_segments (0x3ae6c : word) = Some W_3ae6c.
Proof. vm_refl. Qed.
Lemma D_3ae6c : decode_any W_3ae6c = Some (OpImm ALU_ADD 13 2 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae70 : bv 32 := 0x03010713.
Lemma F_3ae70 : fetch_word Ubsan.M.loaded_segments (0x3ae70 : word) = Some W_3ae70.
Proof. vm_refl. Qed.
Lemma D_3ae70 : decode_any W_3ae70 = Some (OpImm ALU_ADD 14 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae74 : bv 32 := 0x9edfd0ef.
Lemma F_3ae74 : fetch_word Ubsan.M.loaded_segments (0x3ae74 : word) = Some W_3ae74.
Proof. vm_refl. Qed.
Lemma D_3ae74 : decode_any W_3ae74 = Some (Jal 1 2087404, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae78 : bv 32 := 0x03012583.
Lemma F_3ae78 : fetch_word Ubsan.M.loaded_segments (0x3ae78 : word) = Some W_3ae78.
Proof. vm_refl. Qed.
Lemma D_3ae78 : decode_any W_3ae78 = Some (Load SZ4 true 11 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae7c : bv 32 := 0x03812503.
Lemma F_3ae7c : fetch_word Ubsan.M.loaded_segments (0x3ae7c : word) = Some W_3ae7c.
Proof. vm_refl. Qed.
Lemma D_3ae7c : decode_any W_3ae7c = Some (Load SZ4 true 10 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae80 : bv 32 := 0x40b5063b.
Lemma F_3ae80 : fetch_word Ubsan.M.loaded_segments (0x3ae80 : word) = Some W_3ae80.
Proof. vm_refl. Qed.
Lemma D_3ae80 : decode_any W_3ae80 = Some (Op32 ALU_SUB 12 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae84 : bv 32 := 0x40b50533.
Lemma F_3ae84 : fetch_word Ubsan.M.loaded_segments (0x3ae84 : word) = Some W_3ae84.
Proof. vm_refl. Qed.
Lemma D_3ae84 : decode_any W_3ae84 = Some (Op ALU_SUB 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae88 : bv 32 := 0x54a61063.
Lemma F_3ae88 : fetch_word Ubsan.M.loaded_segments (0x3ae88 : word) = Some W_3ae88.
Proof. vm_refl. Qed.
Lemma D_3ae88 : decode_any W_3ae88 = Some (Branch BC_NE 12 10 1344, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae8c : bv 32 := 0x02c12683.
Lemma F_3ae8c : fetch_word Ubsan.M.loaded_segments (0x3ae8c : word) = Some W_3ae8c.
Proof. vm_refl. Qed.
Lemma D_3ae8c : decode_any W_3ae8c = Some (Load SZ4 true 13 2 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae90 : bv 32 := 0x03412503.
Lemma F_3ae90 : fetch_word Ubsan.M.loaded_segments (0x3ae90 : word) = Some W_3ae90.
Proof. vm_refl. Qed.
Lemma D_3ae90 : decode_any W_3ae90 = Some (Load SZ4 true 10 2 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae94 : bv 32 := 0x40d50733.
Lemma F_3ae94 : fetch_word Ubsan.M.loaded_segments (0x3ae94 : word) = Some W_3ae94.
Proof. vm_refl. Qed.
Lemma D_3ae94 : decode_any W_3ae94 = Some (Op ALU_SUB 14 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae98 : bv 32 := 0x40d5053b.
Lemma F_3ae98 : fetch_word Ubsan.M.loaded_segments (0x3ae98 : word) = Some W_3ae98.
Proof. vm_refl. Qed.
Lemma D_3ae98 : decode_any W_3ae98 = Some (Op32 ALU_SUB 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae9c : bv 32 := 0x52e51663.
Lemma F_3ae9c : fetch_word Ubsan.M.loaded_segments (0x3ae9c : word) = Some W_3ae9c.
Proof. vm_refl. Qed.
Lemma D_3ae9c : decode_any W_3ae9c = Some (Branch BC_NE 10 14 1324, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aea0 : bv 32 := 0x0007071b.
Lemma F_3aea0 : fetch_word Ubsan.M.loaded_segments (0x3aea0 : word) = Some W_3aea0.
Proof. vm_refl. Qed.
Lemma D_3aea0 : decode_any W_3aea0 = Some (OpImm32 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aea4 : bv 32 := 0x00048513.
Lemma F_3aea4 : fetch_word Ubsan.M.loaded_segments (0x3aea4 : word) = Some W_3aea4.
Proof. vm_refl. Qed.
Lemma D_3aea4 : decode_any W_3aea4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aea8 : bv 32 := 0xd98e10ef.
Lemma F_3aea8 : fetch_word Ubsan.M.loaded_segments (0x3aea8 : word) = Some W_3aea8.
Proof. vm_refl. Qed.
Lemma D_3aea8 : decode_any W_3aea8 = Some (Jal 1 1971608, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aeac : bv 32 := 0x00a13c23.
Lemma F_3aeac : fetch_word Ubsan.M.loaded_segments (0x3aeac : word) = Some W_3aeac.
Proof. vm_refl. Qed.
Lemma D_3aeac : decode_any W_3aeac = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aeb0 : bv 32 := 0x4a050463.
Lemma F_3aeb0 : fetch_word Ubsan.M.loaded_segments (0x3aeb0 : word) = Some W_3aeb0.
Proof. vm_refl. Qed.
Lemma D_3aeb0 : decode_any W_3aeb0 = Some (Branch BC_EQ 10 0 1192, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aeb4 : bv 32 := 0x00050993.
Lemma F_3aeb4 : fetch_word Ubsan.M.loaded_segments (0x3aeb4 : word) = Some W_3aeb4.
Proof. vm_refl. Qed.
Lemma D_3aeb4 : decode_any W_3aeb4 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aeb8 : bv 32 := 0x04412503.
Lemma F_3aeb8 : fetch_word Ubsan.M.loaded_segments (0x3aeb8 : word) = Some W_3aeb8.
Proof. vm_refl. Qed.
Lemma D_3aeb8 : decode_any W_3aeb8 = Some (Load SZ4 true 10 2 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aebc : bv 32 := 0x04012583.
Lemma F_3aebc : fetch_word Ubsan.M.loaded_segments (0x3aebc : word) = Some W_3aebc.
Proof. vm_refl. Qed.
Lemma D_3aebc : decode_any W_3aebc = Some (Load SZ4 true 11 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aec0 : bv 32 := 0x00800613.
Lemma F_3aec0 : fetch_word Ubsan.M.loaded_segments (0x3aec0 : word) = Some W_3aec0.
Proof. vm_refl. Qed.
Lemma D_3aec0 : decode_any W_3aec0 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aec4 : bv 32 := 0xc0cde0ef.
Lemma F_3aec4 : fetch_word Ubsan.M.loaded_segments (0x3aec4 : word) = Some W_3aec4.
Proof. vm_refl. Qed.
Lemma D_3aec4 : decode_any W_3aec4 = Some (Jal 1 1958924, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aec8 : bv 32 := 0x00050a13.
Lemma F_3aec8 : fetch_word Ubsan.M.loaded_segments (0x3aec8 : word) = Some W_3aec8.
Proof. vm_refl. Qed.
Lemma D_3aec8 : decode_any W_3aec8 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aecc : bv 32 := 0x00098513.
Lemma F_3aecc : fetch_word Ubsan.M.loaded_segments (0x3aecc : word) = Some W_3aecc.
Proof. vm_refl. Qed.
Lemma D_3aecc : decode_any W_3aecc = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aed0 : bv 32 := 0xad5df0ef.
Lemma F_3aed0 : fetch_word Ubsan.M.loaded_segments (0x3aed0 : word) = Some W_3aed0.
Proof. vm_refl. Qed.
Lemma D_3aed0 : decode_any W_3aed0 = Some (Jal 1 1964756, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aed4 : bv 32 := 0x00050493.
Lemma F_3aed4 : fetch_word Ubsan.M.loaded_segments (0x3aed4 : word) = Some W_3aed4.
Proof. vm_refl. Qed.
Lemma D_3aed4 : decode_any W_3aed4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aed8 : bv 32 := 0x000a0513.
Lemma F_3aed8 : fetch_word Ubsan.M.loaded_segments (0x3aed8 : word) = Some W_3aed8.
Proof. vm_refl. Qed.
Lemma D_3aed8 : decode_any W_3aed8 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aedc : bv 32 := 0xac9df0ef.
Lemma F_3aedc : fetch_word Ubsan.M.loaded_segments (0x3aedc : word) = Some W_3aedc.
Proof. vm_refl. Qed.
Lemma D_3aedc : decode_any W_3aedc = Some (Jal 1 1964744, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aee0 : bv 32 := 0x00a13823.
Lemma F_3aee0 : fetch_word Ubsan.M.loaded_segments (0x3aee0 : word) = Some W_3aee0.
Proof. vm_refl. Qed.
Lemma D_3aee0 : decode_any W_3aee0 = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aee4 : bv 32 := 0x00098513.
Lemma F_3aee4 : fetch_word Ubsan.M.loaded_segments (0x3aee4 : word) = Some W_3aee4.
Proof. vm_refl. Qed.
Lemma D_3aee4 : decode_any W_3aee4 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aee8 : bv 32 := 0x8f9de0ef.
Lemma F_3aee8 : fetch_word Ubsan.M.loaded_segments (0x3aee8 : word) = Some W_3aee8.
Proof. vm_refl. Qed.
Lemma D_3aee8 : decode_any W_3aee8 = Some (Jal 1 1960184, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aeec : bv 32 := 0x00050993.
Lemma F_3aeec : fetch_word Ubsan.M.loaded_segments (0x3aeec : word) = Some W_3aeec.
Proof. vm_refl. Qed.
Lemma D_3aeec : decode_any W_3aeec = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aef0 : bv 32 := 0x01413423.
Lemma F_3aef0 : fetch_word Ubsan.M.loaded_segments (0x3aef0 : word) = Some W_3aef0.
Proof. vm_refl. Qed.
Lemma D_3aef0 : decode_any W_3aef0 = Some (Store SZ8 2 20 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aef4 : bv 32 := 0x000a0513.
Lemma F_3aef4 : fetch_word Ubsan.M.loaded_segments (0x3aef4 : word) = Some W_3aef4.
Proof. vm_refl. Qed.
Lemma D_3aef4 : decode_any W_3aef4 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aef8 : bv 32 := 0x8e9de0ef.
Lemma F_3aef8 : fetch_word Ubsan.M.loaded_segments (0x3aef8 : word) = Some W_3aef8.
Proof. vm_refl. Qed.
Lemma D_3aef8 : decode_any W_3aef8 = Some (Jal 1 1960168, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aefc : bv 32 := 0x04012583.
Lemma F_3aefc : fetch_word Ubsan.M.loaded_segments (0x3aefc : word) = Some W_3aefc.
Proof. vm_refl. Qed.
Lemma D_3aefc : decode_any W_3aefc = Some (Load SZ4 true 11 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af00 : bv 32 := 0x4cb05663.
Lemma F_3af00 : fetch_word Ubsan.M.loaded_segments (0x3af00 : word) = Some W_3af00.
Proof. vm_refl. Qed.
Lemma D_3af00 : decode_any W_3af00 = Some (Branch BC_GE 0 11 1228, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af04 : bv 32 := 0x00000593.
Lemma F_3af04 : fetch_word Ubsan.M.loaded_segments (0x3af04 : word) = Some W_3af04.
Proof. vm_refl. Qed.
Lemma D_3af04 : decode_any W_3af04 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af08 : bv 32 := 0x01013603.
Lemma F_3af08 : fetch_word Ubsan.M.loaded_segments (0x3af08 : word) = Some W_3af08.
Proof. vm_refl. Qed.
Lemma D_3af08 : decode_any W_3af08 = Some (Load SZ8 true 12 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af0c : bv 32 := 0x00c03633.
Lemma F_3af0c : fetch_word Ubsan.M.loaded_segments (0x3af0c : word) = Some W_3af0c.
Proof. vm_refl. Qed.
Lemma D_3af0c : decode_any W_3af0c = Some (Op ALU_SLTU 12 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af10 : bv 32 := 0x009036b3.
Lemma F_3af10 : fetch_word Ubsan.M.loaded_segments (0x3af10 : word) = Some W_3af10.
Proof. vm_refl. Qed.
Lemma D_3af10 : decode_any W_3af10 = Some (Op ALU_SLTU 13 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af14 : bv 32 := 0x00300713.
Lemma F_3af14 : fetch_word Ubsan.M.loaded_segments (0x3af14 : word) = Some W_3af14.
Proof. vm_refl. Qed.
Lemma D_3af14 : decode_any W_3af14 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af18 : bv 32 := 0xf00007d3.
Lemma F_3af18 : fetch_word Ubsan.M.loaded_segments (0x3af18 : word) = Some W_3af18.
Proof. vm_refl. Qed.
Lemma D_3af18 : decode_any W_3af18 = Some (Fmv FMV_F_X FMT_S 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af1c : bv 32 := 0x14c0006f.
Lemma F_3af1c : fetch_word Ubsan.M.loaded_segments (0x3af1c : word) = Some W_3af1c.
Proof. vm_refl. Qed.
Lemma D_3af1c : decode_any W_3af1c = Some (Jal 0 332, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af20 : bv 32 := 0x0000a517.
Lemma F_3af20 : fetch_word Ubsan.M.loaded_segments (0x3af20 : word) = Some W_3af20.
Proof. vm_refl. Qed.
Lemma D_3af20 : decode_any W_3af20 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af24 : bv 32 := 0xf7853503.
Lemma F_3af24 : fetch_word Ubsan.M.loaded_segments (0x3af24 : word) = Some W_3af24.
Proof. vm_refl. Qed.
Lemma D_3af24 : decode_any W_3af24 = Some (Load SZ8 true 10 10 3960, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af28 : bv 32 := 0x00052503.
Lemma F_3af28 : fetch_word Ubsan.M.loaded_segments (0x3af28 : word) = Some W_3af28.
Proof. vm_refl. Qed.
Lemma D_3af28 : decode_any W_3af28 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af2c : bv 32 := 0x00500593.
Lemma F_3af2c : fetch_word Ubsan.M.loaded_segments (0x3af2c : word) = Some W_3af2c.
Proof. vm_refl. Qed.
Lemma D_3af2c : decode_any W_3af2c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af30 : bv 32 := 0x44a5cc63.
Lemma F_3af30 : fetch_word Ubsan.M.loaded_segments (0x3af30 : word) = Some W_3af30.
Proof. vm_refl. Qed.
Lemma D_3af30 : decode_any W_3af30 = Some (Branch BC_LT 11 10 1112, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af34 : bv 32 := 0xfffd5517.
Lemma F_3af34 : fetch_word Ubsan.M.loaded_segments (0x3af34 : word) = Some W_3af34.
Proof. vm_refl. Qed.
Lemma D_3af34 : decode_any W_3af34 = Some (Auipc 10 1048533, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af38 : bv 32 := 0xfffd7597.
Lemma F_3af38 : fetch_word Ubsan.M.loaded_segments (0x3af38 : word) = Some W_3af38.
Proof. vm_refl. Qed.
Lemma D_3af38 : decode_any W_3af38 = Some (Auipc 11 1048535, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af3c : bv 32 := 0x38050513.
Lemma F_3af3c : fetch_word Ubsan.M.loaded_segments (0x3af3c : word) = Some W_3af3c.
Proof. vm_refl. Qed.
Lemma D_3af3c : decode_any W_3af3c = Some (OpImm ALU_ADD 10 10 896, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af40 : bv 32 := 0x06458593.
Lemma F_3af40 : fetch_word Ubsan.M.loaded_segments (0x3af40 : word) = Some W_3af40.
Proof. vm_refl. Qed.
Lemma D_3af40 : decode_any W_3af40 = Some (OpImm ALU_ADD 11 11 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af44 : bv 32 := 0x0280006f.
Lemma F_3af44 : fetch_word Ubsan.M.loaded_segments (0x3af44 : word) = Some W_3af44.
Proof. vm_refl. Qed.
Lemma D_3af44 : decode_any W_3af44 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af48 : bv 32 := 0x0000a517.
Lemma F_3af48 : fetch_word Ubsan.M.loaded_segments (0x3af48 : word) = Some W_3af48.
Proof. vm_refl. Qed.
Lemma D_3af48 : decode_any W_3af48 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af4c : bv 32 := 0xf5053503.
Lemma F_3af4c : fetch_word Ubsan.M.loaded_segments (0x3af4c : word) = Some W_3af4c.
Proof. vm_refl. Qed.
Lemma D_3af4c : decode_any W_3af4c = Some (Load SZ8 true 10 10 3920, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af50 : bv 32 := 0x00052503.
Lemma F_3af50 : fetch_word Ubsan.M.loaded_segments (0x3af50 : word) = Some W_3af50.
Proof. vm_refl. Qed.
Lemma D_3af50 : decode_any W_3af50 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af54 : bv 32 := 0x00500593.
Lemma F_3af54 : fetch_word Ubsan.M.loaded_segments (0x3af54 : word) = Some W_3af54.
Proof. vm_refl. Qed.
Lemma D_3af54 : decode_any W_3af54 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af58 : bv 32 := 0x42a5c863.
Lemma F_3af58 : fetch_word Ubsan.M.loaded_segments (0x3af58 : word) = Some W_3af58.
Proof. vm_refl. Qed.
Lemma D_3af58 : decode_any W_3af58 = Some (Branch BC_LT 11 10 1072, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af5c : bv 32 := 0xfffd5517.
Lemma F_3af5c : fetch_word Ubsan.M.loaded_segments (0x3af5c : word) = Some W_3af5c.
Proof. vm_refl. Qed.
Lemma D_3af5c : decode_any W_3af5c = Some (Auipc 10 1048533, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af60 : bv 32 := 0xfffd7597.
Lemma F_3af60 : fetch_word Ubsan.M.loaded_segments (0x3af60 : word) = Some W_3af60.
Proof. vm_refl. Qed.
Lemma D_3af60 : decode_any W_3af60 = Some (Auipc 11 1048535, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af64 : bv 32 := 0x5d950513.
Lemma F_3af64 : fetch_word Ubsan.M.loaded_segments (0x3af64 : word) = Some W_3af64.
Proof. vm_refl. Qed.
Lemma D_3af64 : decode_any W_3af64 = Some (OpImm ALU_ADD 10 10 1497, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af68 : bv 32 := 0x03c58593.
Lemma F_3af68 : fetch_word Ubsan.M.loaded_segments (0x3af68 : word) = Some W_3af68.
Proof. vm_refl. Qed.
Lemma D_3af68 : decode_any W_3af68 = Some (OpImm ALU_ADD 11 11 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af6c : bv 32 := 0x00000613.
Lemma F_3af6c : fetch_word Ubsan.M.loaded_segments (0x3af6c : word) = Some W_3af6c.
Proof. vm_refl. Qed.
Lemma D_3af6c : decode_any W_3af6c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af70 : bv 32 := 0x0a813083.
Lemma F_3af70 : fetch_word Ubsan.M.loaded_segments (0x3af70 : word) = Some W_3af70.
Proof. vm_refl. Qed.
Lemma D_3af70 : decode_any W_3af70 = Some (Load SZ8 true 1 2 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af74 : bv 32 := 0x0a013403.
Lemma F_3af74 : fetch_word Ubsan.M.loaded_segments (0x3af74 : word) = Some W_3af74.
Proof. vm_refl. Qed.
Lemma D_3af74 : decode_any W_3af74 = Some (Load SZ8 true 8 2 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af78 : bv 32 := 0x09813483.
Lemma F_3af78 : fetch_word Ubsan.M.loaded_segments (0x3af78 : word) = Some W_3af78.
Proof. vm_refl. Qed.
Lemma D_3af78 : decode_any W_3af78 = Some (Load SZ8 true 9 2 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af7c : bv 32 := 0x09013903.
Lemma F_3af7c : fetch_word Ubsan.M.loaded_segments (0x3af7c : word) = Some W_3af7c.
Proof. vm_refl. Qed.
Lemma D_3af7c : decode_any W_3af7c = Some (Load SZ8 true 18 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af80 : bv 32 := 0x08813983.
Lemma F_3af80 : fetch_word Ubsan.M.loaded_segments (0x3af80 : word) = Some W_3af80.
Proof. vm_refl. Qed.
Lemma D_3af80 : decode_any W_3af80 = Some (Load SZ8 true 19 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af84 : bv 32 := 0x08013a03.
Lemma F_3af84 : fetch_word Ubsan.M.loaded_segments (0x3af84 : word) = Some W_3af84.
Proof. vm_refl. Qed.
Lemma D_3af84 : decode_any W_3af84 = Some (Load SZ8 true 20 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af88 : bv 32 := 0x07813a83.
Lemma F_3af88 : fetch_word Ubsan.M.loaded_segments (0x3af88 : word) = Some W_3af88.
Proof. vm_refl. Qed.
Lemma D_3af88 : decode_any W_3af88 = Some (Load SZ8 true 21 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af8c : bv 32 := 0x07013b03.
Lemma F_3af8c : fetch_word Ubsan.M.loaded_segments (0x3af8c : word) = Some W_3af8c.
Proof. vm_refl. Qed.
Lemma D_3af8c : decode_any W_3af8c = Some (Load SZ8 true 22 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af90 : bv 32 := 0x06813b83.
Lemma F_3af90 : fetch_word Ubsan.M.loaded_segments (0x3af90 : word) = Some W_3af90.
Proof. vm_refl. Qed.
Lemma D_3af90 : decode_any W_3af90 = Some (Load SZ8 true 23 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af94 : bv 32 := 0x06013c03.
Lemma F_3af94 : fetch_word Ubsan.M.loaded_segments (0x3af94 : word) = Some W_3af94.
Proof. vm_refl. Qed.
Lemma D_3af94 : decode_any W_3af94 = Some (Load SZ8 true 24 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af98 : bv 32 := 0x05813c83.
Lemma F_3af98 : fetch_word Ubsan.M.loaded_segments (0x3af98 : word) = Some W_3af98.
Proof. vm_refl. Qed.
Lemma D_3af98 : decode_any W_3af98 = Some (Load SZ8 true 25 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_3af9c : bv 32 := 0x05013d03.
Lemma F_3af9c : fetch_word Ubsan.M.loaded_segments (0x3af9c : word) = Some W_3af9c.
Proof. vm_refl. Qed.
Lemma D_3af9c : decode_any W_3af9c = Some (Load SZ8 true 26 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_3afa0 : bv 32 := 0x04813d83.
Lemma F_3afa0 : fetch_word Ubsan.M.loaded_segments (0x3afa0 : word) = Some W_3afa0.
Proof. vm_refl. Qed.
Lemma D_3afa0 : decode_any W_3afa0 = Some (Load SZ8 true 27 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_3afa4 : bv 32 := 0x0b010113.
Lemma F_3afa4 : fetch_word Ubsan.M.loaded_segments (0x3afa4 : word) = Some W_3afa4.
Proof. vm_refl. Qed.
Lemma D_3afa4 : decode_any W_3afa4 = Some (OpImm ALU_ADD 2 2 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_3afa8 : bv 32 := 0xf1ddc06f.
Lemma F_3afa8 : fetch_word Ubsan.M.loaded_segments (0x3afa8 : word) = Some W_3afa8.
Proof. vm_refl. Qed.
Lemma D_3afa8 : decode_any W_3afa8 = Some (Jal 0 1953564, 4%Z).
Proof. vm_refl. Qed.

Definition W_3afac : bv 32 := 0x0000a597.
Lemma F_3afac : fetch_word Ubsan.M.loaded_segments (0x3afac : word) = Some W_3afac.
Proof. vm_refl. Qed.
Lemma D_3afac : decode_any W_3afac = Some (Auipc 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3afb0 : bv 32 := 0xeec5b583.
Lemma F_3afb0 : fetch_word Ubsan.M.loaded_segments (0x3afb0 : word) = Some W_3afb0.
Proof. vm_refl. Qed.
Lemma D_3afb0 : decode_any W_3afb0 = Some (Load SZ8 true 11 11 3820, 4%Z).
Proof. vm_refl. Qed.

Definition W_3afb4 : bv 32 := 0x0005a583.
Lemma F_3afb4 : fetch_word Ubsan.M.loaded_segments (0x3afb4 : word) = Some W_3afb4.
Proof. vm_refl. Qed.
Lemma D_3afb4 : decode_any W_3afb4 = Some (Load SZ4 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3afb8 : bv 32 := 0x00400693.
Lemma F_3afb8 : fetch_word Ubsan.M.loaded_segments (0x3afb8 : word) = Some W_3afb8.
Proof. vm_refl. Qed.
Lemma D_3afb8 : decode_any W_3afb8 = Some (OpImm ALU_ADD 13 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_3afbc : bv 32 := 0x02b6cc63.
Lemma F_3afbc : fetch_word Ubsan.M.loaded_segments (0x3afbc : word) = Some W_3afbc.
Proof. vm_refl. Qed.
Lemma D_3afbc : decode_any W_3afbc = Some (Branch BC_LT 13 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_3afc0 : bv 32 := 0x03412583.
Lemma F_3afc0 : fetch_word Ubsan.M.loaded_segments (0x3afc0 : word) = Some W_3afc0.
Proof. vm_refl. Qed.
Lemma D_3afc0 : decode_any W_3afc0 = Some (Load SZ4 true 11 2 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_3afc4 : bv 32 := 0x400006b7.
Lemma F_3afc4 : fetch_word Ubsan.M.loaded_segments (0x3afc4 : word) = Some W_3afc4.
Proof. vm_refl. Qed.
Lemma D_3afc4 : decode_any W_3afc4 = Some (Lui 13 262144, 4%Z).
Proof. vm_refl. Qed.

Definition W_3afc8 : bv 32 := 0x00d586bb.
Lemma F_3afc8 : fetch_word Ubsan.M.loaded_segments (0x3afc8 : word) = Some W_3afc8.
Proof. vm_refl. Qed.
Lemma D_3afc8 : decode_any W_3afc8 = Some (Op32 ALU_ADD 13 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_3afcc : bv 32 := 0x3e06ce63.
Lemma F_3afcc : fetch_word Ubsan.M.loaded_segments (0x3afcc : word) = Some W_3afcc.
Proof. vm_refl. Qed.
Lemma D_3afcc : decode_any W_3afcc = Some (Branch BC_LT 13 0 1020, 4%Z).
Proof. vm_refl. Qed.

Definition W_3afd0 : bv 32 := 0x04012703.
Lemma F_3afd0 : fetch_word Ubsan.M.loaded_segments (0x3afd0 : word) = Some W_3afd0.
Proof. vm_refl. Qed.
Lemma D_3afd0 : decode_any W_3afd0 = Some (Load SZ4 true 14 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_3afd4 : bv 32 := 0x00156693.
Lemma F_3afd4 : fetch_word Ubsan.M.loaded_segments (0x3afd4 : word) = Some W_3afd4.
Proof. vm_refl. Qed.
Lemma D_3afd4 : decode_any W_3afd4 = Some (OpImm ALU_OR 13 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3afd8 : bv 32 := 0x0015979b.
Lemma F_3afd8 : fetch_word Ubsan.M.loaded_segments (0x3afd8 : word) = Some W_3afd8.
Proof. vm_refl. Qed.
Lemma D_3afd8 : decode_any W_3afd8 = Some (ShiftImm32 ALU_SLL 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3afdc : bv 32 := 0x00178793.
Lemma F_3afdc : fetch_word Ubsan.M.loaded_segments (0x3afdc : word) = Some W_3afdc.
Proof. vm_refl. Qed.
Lemma D_3afdc : decode_any W_3afdc = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3afe0 : bv 32 := 0xfffd6517.
Lemma F_3afe0 : fetch_word Ubsan.M.loaded_segments (0x3afe0 : word) = Some W_3afe0.
Proof. vm_refl. Qed.
Lemma D_3afe0 : decode_any W_3afe0 = Some (Auipc 10 1048534, 4%Z).
Proof. vm_refl. Qed.

Definition W_3afe4 : bv 32 := 0xfffd7597.
Lemma F_3afe4 : fetch_word Ubsan.M.loaded_segments (0x3afe4 : word) = Some W_3afe4.
Proof. vm_refl. Qed.
Lemma D_3afe4 : decode_any W_3afe4 = Some (Auipc 11 1048535, 4%Z).
Proof. vm_refl. Qed.

Definition W_3afe8 : bv 32 := 0xf8050513.
Lemma F_3afe8 : fetch_word Ubsan.M.loaded_segments (0x3afe8 : word) = Some W_3afe8.
Proof. vm_refl. Qed.
Lemma D_3afe8 : decode_any W_3afe8 = Some (OpImm ALU_ADD 10 10 3968, 4%Z).
Proof. vm_refl. Qed.

Definition W_3afec : bv 32 := 0xfb858593.
Lemma F_3afec : fetch_word Ubsan.M.loaded_segments (0x3afec : word) = Some W_3afec.
Proof. vm_refl. Qed.
Lemma D_3afec : decode_any W_3afec = Some (OpImm ALU_ADD 11 11 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aff0 : bv 32 := 0xe39dc0ef.
Lemma F_3aff0 : fetch_word Ubsan.M.loaded_segments (0x3aff0 : word) = Some W_3aff0.
Proof. vm_refl. Qed.
Lemma D_3aff0 : decode_any W_3aff0 = Some (Jal 1 1953336, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aff4 : bv 32 := 0x00000513.
Lemma F_3aff4 : fetch_word Ubsan.M.loaded_segments (0x3aff4 : word) = Some W_3aff4.
Proof. vm_refl. Qed.
Lemma D_3aff4 : decode_any W_3aff4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3aff8 : bv 32 := 0x00048593.
Lemma F_3aff8 : fetch_word Ubsan.M.loaded_segments (0x3aff8 : word) = Some W_3aff8.
Proof. vm_refl. Qed.
Lemma D_3aff8 : decode_any W_3aff8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3affc : bv 32 := 0xb18df0ef.
Lemma F_3affc : fetch_word Ubsan.M.loaded_segments (0x3affc : word) = Some W_3affc.
Proof. vm_refl. Qed.
Lemma D_3affc : decode_any W_3affc = Some (Jal 1 1962776, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b000 : bv 32 := 0x38c0006f.
Lemma F_3b000 : fetch_word Ubsan.M.loaded_segments (0x3b000 : word) = Some W_3b000.
Proof. vm_refl. Qed.
Lemma D_3b000 : decode_any W_3b000 = Some (Jal 0 908, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b004 : bv 32 := 0x0000a517.
Lemma F_3b004 : fetch_word Ubsan.M.loaded_segments (0x3b004 : word) = Some W_3b004.
Proof. vm_refl. Qed.
Lemma D_3b004 : decode_any W_3b004 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b008 : bv 32 := 0xe9453503.
Lemma F_3b008 : fetch_word Ubsan.M.loaded_segments (0x3b008 : word) = Some W_3b008.
Proof. vm_refl. Qed.
Lemma D_3b008 : decode_any W_3b008 = Some (Load SZ8 true 10 10 3732, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b00c : bv 32 := 0x00052503.
Lemma F_3b00c : fetch_word Ubsan.M.loaded_segments (0x3b00c : word) = Some W_3b00c.
Proof. vm_refl. Qed.
Lemma D_3b00c : decode_any W_3b00c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b010 : bv 32 := 0x00500593.
Lemma F_3b010 : fetch_word Ubsan.M.loaded_segments (0x3b010 : word) = Some W_3b010.
Proof. vm_refl. Qed.
Lemma D_3b010 : decode_any W_3b010 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b014 : bv 32 := 0x36a5ca63.
Lemma F_3b014 : fetch_word Ubsan.M.loaded_segments (0x3b014 : word) = Some W_3b014.
Proof. vm_refl. Qed.
Lemma D_3b014 : decode_any W_3b014 = Some (Branch BC_LT 11 10 884, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b018 : bv 32 := 0xfffd7517.
Lemma F_3b018 : fetch_word Ubsan.M.loaded_segments (0x3b018 : word) = Some W_3b018.
Proof. vm_refl. Qed.
Lemma D_3b018 : decode_any W_3b018 = Some (Auipc 10 1048535, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b01c : bv 32 := 0xfffd7597.
Lemma F_3b01c : fetch_word Ubsan.M.loaded_segments (0x3b01c : word) = Some W_3b01c.
Proof. vm_refl. Qed.
Lemma D_3b01c : decode_any W_3b01c = Some (Auipc 11 1048535, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b020 : bv 32 := 0xcd150513.
Lemma F_3b020 : fetch_word Ubsan.M.loaded_segments (0x3b020 : word) = Some W_3b020.
Proof. vm_refl. Qed.
Lemma D_3b020 : decode_any W_3b020 = Some (OpImm ALU_ADD 10 10 3281, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b024 : bv 32 := 0xf8058593.
Lemma F_3b024 : fetch_word Ubsan.M.loaded_segments (0x3b024 : word) = Some W_3b024.
Proof. vm_refl. Qed.
Lemma D_3b024 : decode_any W_3b024 = Some (OpImm ALU_ADD 11 11 3968, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b028 : bv 32 := 0x00000613.
Lemma F_3b028 : fetch_word Ubsan.M.loaded_segments (0x3b028 : word) = Some W_3b028.
Proof. vm_refl. Qed.
Lemma D_3b028 : decode_any W_3b028 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b02c : bv 32 := 0xe99dc0ef.
Lemma F_3b02c : fetch_word Ubsan.M.loaded_segments (0x3b02c : word) = Some W_3b02c.
Proof. vm_refl. Qed.
Lemma D_3b02c : decode_any W_3b02c = Some (Jal 1 1953432, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b030 : bv 32 := 0x35c0006f.
Lemma F_3b030 : fetch_word Ubsan.M.loaded_segments (0x3b030 : word) = Some W_3b030.
Proof. vm_refl. Qed.
Lemma D_3b030 : decode_any W_3b030 = Some (Jal 0 860, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b034 : bv 32 := 0x0000a517.
Lemma F_3b034 : fetch_word Ubsan.M.loaded_segments (0x3b034 : word) = Some W_3b034.
Proof. vm_refl. Qed.
Lemma D_3b034 : decode_any W_3b034 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b038 : bv 32 := 0xe6453503.
Lemma F_3b038 : fetch_word Ubsan.M.loaded_segments (0x3b038 : word) = Some W_3b038.
Proof. vm_refl. Qed.
Lemma D_3b038 : decode_any W_3b038 = Some (Load SZ8 true 10 10 3684, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b03c : bv 32 := 0x00052503.
Lemma F_3b03c : fetch_word Ubsan.M.loaded_segments (0x3b03c : word) = Some W_3b03c.
Proof. vm_refl. Qed.
Lemma D_3b03c : decode_any W_3b03c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b040 : bv 32 := 0x00500593.
Lemma F_3b040 : fetch_word Ubsan.M.loaded_segments (0x3b040 : word) = Some W_3b040.
Proof. vm_refl. Qed.
Lemma D_3b040 : decode_any W_3b040 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b044 : bv 32 := 0x34a5c263.
Lemma F_3b044 : fetch_word Ubsan.M.loaded_segments (0x3b044 : word) = Some W_3b044.
Proof. vm_refl. Qed.
Lemma D_3b044 : decode_any W_3b044 = Some (Branch BC_LT 11 10 836, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b048 : bv 32 := 0xfffd7517.
Lemma F_3b048 : fetch_word Ubsan.M.loaded_segments (0x3b048 : word) = Some W_3b048.
Proof. vm_refl. Qed.
Lemma D_3b048 : decode_any W_3b048 = Some (Auipc 10 1048535, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b04c : bv 32 := 0xfffd7597.
Lemma F_3b04c : fetch_word Ubsan.M.loaded_segments (0x3b04c : word) = Some W_3b04c.
Proof. vm_refl. Qed.
Lemma D_3b04c : decode_any W_3b04c = Some (Auipc 11 1048535, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b050 : bv 32 := 0x97750513.
Lemma F_3b050 : fetch_word Ubsan.M.loaded_segments (0x3b050 : word) = Some W_3b050.
Proof. vm_refl. Qed.
Lemma D_3b050 : decode_any W_3b050 = Some (OpImm ALU_ADD 10 10 2423, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b054 : bv 32 := 0xf5058593.
Lemma F_3b054 : fetch_word Ubsan.M.loaded_segments (0x3b054 : word) = Some W_3b054.
Proof. vm_refl. Qed.
Lemma D_3b054 : decode_any W_3b054 = Some (OpImm ALU_ADD 11 11 3920, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b058 : bv 32 := 0xfd1ff06f.
Lemma F_3b058 : fetch_word Ubsan.M.loaded_segments (0x3b058 : word) = Some W_3b058.
Proof. vm_refl. Qed.
Lemma D_3b058 : decode_any W_3b058 = Some (Jal 0 2097104, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b05c : bv 32 := 0x04012783.
Lemma F_3b05c : fetch_word Ubsan.M.loaded_segments (0x3b05c : word) = Some W_3b05c.
Proof. vm_refl. Qed.
Lemma D_3b05c : decode_any W_3b05c = Some (Load SZ4 true 15 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b060 : bv 32 := 0x0015859b.
Lemma F_3b060 : fetch_word Ubsan.M.loaded_segments (0x3b060 : word) = Some W_3b060.
Proof. vm_refl. Qed.
Lemma D_3b060 : decode_any W_3b060 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b064 : bv 32 := 0x36f5d463.
Lemma F_3b064 : fetch_word Ubsan.M.loaded_segments (0x3b064 : word) = Some W_3b064.
Proof. vm_refl. Qed.
Lemma D_3b064 : decode_any W_3b064 = Some (Branch BC_GE 11 15 872, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b068 : bv 32 := 0x02a58833.
Lemma F_3b068 : fetch_word Ubsan.M.loaded_segments (0x3b068 : word) = Some W_3b068.
Proof. vm_refl. Qed.
Lemma D_3b068 : decode_any W_3b068 = Some (Mul M_MUL 16 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b06c : bv 32 := 0x02a587bb.
Lemma F_3b06c : fetch_word Ubsan.M.loaded_segments (0x3b06c : word) = Some W_3b06c.
Proof. vm_refl. Qed.
Lemma D_3b06c : decode_any W_3b06c = Some (Mul32 M_MUL 15 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b070 : bv 32 := 0x35079c63.
Lemma F_3b070 : fetch_word Ubsan.M.loaded_segments (0x3b070 : word) = Some W_3b070.
Proof. vm_refl. Qed.
Lemma D_3b070 : decode_any W_3b070 = Some (Branch BC_NE 15 16 856, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b074 : bv 32 := 0x0008081b.
Lemma F_3b074 : fetch_word Ubsan.M.loaded_segments (0x3b074 : word) = Some W_3b074.
Proof. vm_refl. Qed.
Lemma D_3b074 : decode_any W_3b074 = Some (OpImm32 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b078 : bv 32 := 0x00281793.
Lemma F_3b078 : fetch_word Ubsan.M.loaded_segments (0x3b078 : word) = Some W_3b078.
Proof. vm_refl. Qed.
Lemma D_3b078 : decode_any W_3b078 = Some (ShiftImm ALU_SLL 15 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b07c : bv 32 := 0x01013883.
Lemma F_3b07c : fetch_word Ubsan.M.loaded_segments (0x3b07c : word) = Some W_3b07c.
Proof. vm_refl. Qed.
Lemma D_3b07c : decode_any W_3b07c = Some (Load SZ8 true 17 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b080 : bv 32 := 0x00f887b3.
Lemma F_3b080 : fetch_word Ubsan.M.loaded_segments (0x3b080 : word) = Some W_3b080.
Proof. vm_refl. Qed.
Lemma D_3b080 : decode_any W_3b080 = Some (Op ALU_ADD 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b084 : bv 32 := 0x0017b893.
Lemma F_3b084 : fetch_word Ubsan.M.loaded_segments (0x3b084 : word) = Some W_3b084.
Proof. vm_refl. Qed.
Lemma D_3b084 : decode_any W_3b084 = Some (OpImm ALU_SLTU 17 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b088 : bv 32 := 0x35160063.
Lemma F_3b088 : fetch_word Ubsan.M.loaded_segments (0x3b088 : word) = Some W_3b088.
Proof. vm_refl. Qed.
Lemma D_3b088 : decode_any W_3b088 = Some (Branch BC_EQ 12 17 832, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b08c : bv 32 := 0x01013883.
Lemma F_3b08c : fetch_word Ubsan.M.loaded_segments (0x3b08c : word) = Some W_3b08c.
Proof. vm_refl. Qed.
Lemma D_3b08c : decode_any W_3b08c = Some (Load SZ8 true 17 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b090 : bv 32 := 0x0117b8b3.
Lemma F_3b090 : fetch_word Ubsan.M.loaded_segments (0x3b090 : word) = Some W_3b090.
Proof. vm_refl. Qed.
Lemma D_3b090 : decode_any W_3b090 = Some (Op ALU_SLTU 17 15 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b094 : bv 32 := 0x00082813.
Lemma F_3b094 : fetch_word Ubsan.M.loaded_segments (0x3b094 : word) = Some W_3b094.
Proof. vm_refl. Qed.
Lemma D_3b094 : decode_any W_3b094 = Some (OpImm ALU_SLT 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b098 : bv 32 := 0x0108c833.
Lemma F_3b098 : fetch_word Ubsan.M.loaded_segments (0x3b098 : word) = Some W_3b098.
Proof. vm_refl. Qed.
Lemma D_3b098 : decode_any W_3b098 = Some (Op ALU_XOR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b09c : bv 32 := 0x00184813.
Lemma F_3b09c : fetch_word Ubsan.M.loaded_segments (0x3b09c : word) = Some W_3b09c.
Proof. vm_refl. Qed.
Lemma D_3b09c : decode_any W_3b09c = Some (OpImm ALU_XOR 16 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b0a0 : bv 32 := 0x32080463.
Lemma F_3b0a0 : fetch_word Ubsan.M.loaded_segments (0x3b0a0 : word) = Some W_3b0a0.
Proof. vm_refl. Qed.
Lemma D_3b0a0 : decode_any W_3b0a0 = Some (Branch BC_EQ 16 0 808, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b0a4 : bv 32 := 0x04412803.
Lemma F_3b0a4 : fetch_word Ubsan.M.loaded_segments (0x3b0a4 : word) = Some W_3b0a4.
Proof. vm_refl. Qed.
Lemma D_3b0a4 : decode_any W_3b0a4 = Some (Load SZ4 true 16 2 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b0a8 : bv 32 := 0xfb005ae3.
Lemma F_3b0a8 : fetch_word Ubsan.M.loaded_segments (0x3b0a8 : word) = Some W_3b0a8.
Proof. vm_refl. Qed.
Lemma D_3b0a8 : decode_any W_3b0a8 = Some (Branch BC_GE 0 16 8116, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b0ac : bv 32 := 0x00000813.
Lemma F_3b0ac : fetch_word Ubsan.M.loaded_segments (0x3b0ac : word) = Some W_3b0ac.
Proof. vm_refl. Qed.
Lemma D_3b0ac : decode_any W_3b0ac = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b0b0 : bv 32 := 0x00000893.
Lemma F_3b0b0 : fetch_word Ubsan.M.loaded_segments (0x3b0b0 : word) = Some W_3b0b0.
Proof. vm_refl. Qed.
Lemma D_3b0b0 : decode_any W_3b0b0 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b0b4 : bv 32 := 0x02c12303.
Lemma F_3b0b4 : fetch_word Ubsan.M.loaded_segments (0x3b0b4 : word) = Some W_3b0b4.
Proof. vm_refl. Qed.
Lemma D_3b0b4 : decode_any W_3b0b4 = Some (Load SZ4 true 6 2 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b0b8 : bv 32 := 0x006582b3.
Lemma F_3b0b8 : fetch_word Ubsan.M.loaded_segments (0x3b0b8 : word) = Some W_3b0b8.
Proof. vm_refl. Qed.
Lemma D_3b0b8 : decode_any W_3b0b8 = Some (Op ALU_ADD 5 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b0bc : bv 32 := 0x0065833b.
Lemma F_3b0bc : fetch_word Ubsan.M.loaded_segments (0x3b0bc : word) = Some W_3b0bc.
Proof. vm_refl. Qed.
Lemma D_3b0bc : decode_any W_3b0bc = Some (Op32 ALU_ADD 6 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b0c0 : bv 32 := 0x30531463.
Lemma F_3b0c0 : fetch_word Ubsan.M.loaded_segments (0x3b0c0 : word) = Some W_3b0c0.
Proof. vm_refl. Qed.
Lemma D_3b0c0 : decode_any W_3b0c0 = Some (Branch BC_NE 6 5 776, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b0c4 : bv 32 := 0x0002829b.
Lemma F_3b0c4 : fetch_word Ubsan.M.loaded_segments (0x3b0c4 : word) = Some W_3b0c4.
Proof. vm_refl. Qed.
Lemma D_3b0c4 : decode_any W_3b0c4 = Some (OpImm32 5 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b0c8 : bv 32 := 0x03328333.
Lemma F_3b0c8 : fetch_word Ubsan.M.loaded_segments (0x3b0c8 : word) = Some W_3b0c8.
Proof. vm_refl. Qed.
Lemma D_3b0c8 : decode_any W_3b0c8 = Some (Mul M_MUL 6 5 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b0cc : bv 32 := 0x033282bb.
Lemma F_3b0cc : fetch_word Ubsan.M.loaded_segments (0x3b0cc : word) = Some W_3b0cc.
Proof. vm_refl. Qed.
Lemma D_3b0cc : decode_any W_3b0cc = Some (Mul32 M_MUL 5 5 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b0d0 : bv 32 := 0x2e629c63.
Lemma F_3b0d0 : fetch_word Ubsan.M.loaded_segments (0x3b0d0 : word) = Some W_3b0d0.
Proof. vm_refl. Qed.
Lemma D_3b0d0 : decode_any W_3b0d0 = Some (Branch BC_NE 5 6 760, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b0d4 : bv 32 := 0x0003031b.
Lemma F_3b0d4 : fetch_word Ubsan.M.loaded_segments (0x3b0d4 : word) = Some W_3b0d4.
Proof. vm_refl. Qed.
Lemma D_3b0d4 : decode_any W_3b0d4 = Some (OpImm32 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b0d8 : bv 32 := 0x00231293.
Lemma F_3b0d8 : fetch_word Ubsan.M.loaded_segments (0x3b0d8 : word) = Some W_3b0d8.
Proof. vm_refl. Qed.
Lemma D_3b0d8 : decode_any W_3b0d8 = Some (ShiftImm ALU_SLL 5 6 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b0dc : bv 32 := 0x005482b3.
Lemma F_3b0dc : fetch_word Ubsan.M.loaded_segments (0x3b0dc : word) = Some W_3b0dc.
Proof. vm_refl. Qed.
Lemma D_3b0dc : decode_any W_3b0dc = Some (Op ALU_ADD 5 9 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b0e0 : bv 32 := 0x0012b393.
Lemma F_3b0e0 : fetch_word Ubsan.M.loaded_segments (0x3b0e0 : word) = Some W_3b0e0.
Proof. vm_refl. Qed.
Lemma D_3b0e0 : decode_any W_3b0e0 = Some (OpImm ALU_SLTU 7 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b0e4 : bv 32 := 0x2e768263.
Lemma F_3b0e4 : fetch_word Ubsan.M.loaded_segments (0x3b0e4 : word) = Some W_3b0e4.
Proof. vm_refl. Qed.
Lemma D_3b0e4 : decode_any W_3b0e4 = Some (Branch BC_EQ 13 7 740, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b0e8 : bv 32 := 0x0092b3b3.
Lemma F_3b0e8 : fetch_word Ubsan.M.loaded_segments (0x3b0e8 : word) = Some W_3b0e8.
Proof. vm_refl. Qed.
Lemma D_3b0e8 : decode_any W_3b0e8 = Some (Op ALU_SLTU 7 5 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b0ec : bv 32 := 0x00032313.
Lemma F_3b0ec : fetch_word Ubsan.M.loaded_segments (0x3b0ec : word) = Some W_3b0ec.
Proof. vm_refl. Qed.
Lemma D_3b0ec : decode_any W_3b0ec = Some (OpImm ALU_SLT 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b0f0 : bv 32 := 0x0063c333.
Lemma F_3b0f0 : fetch_word Ubsan.M.loaded_segments (0x3b0f0 : word) = Some W_3b0f0.
Proof. vm_refl. Qed.
Lemma D_3b0f0 : decode_any W_3b0f0 = Some (Op ALU_XOR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b0f4 : bv 32 := 0x00134313.
Lemma F_3b0f4 : fetch_word Ubsan.M.loaded_segments (0x3b0f4 : word) = Some W_3b0f4.
Proof. vm_refl. Qed.
Lemma D_3b0f4 : decode_any W_3b0f4 = Some (OpImm ALU_XOR 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b0f8 : bv 32 := 0x2c030863.
Lemma F_3b0f8 : fetch_word Ubsan.M.loaded_segments (0x3b0f8 : word) = Some W_3b0f8.
Proof. vm_refl. Qed.
Lemma D_3b0f8 : decode_any W_3b0f8 = Some (Branch BC_EQ 6 0 720, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b0fc : bv 32 := 0x03012383.
Lemma F_3b0fc : fetch_word Ubsan.M.loaded_segments (0x3b0fc : word) = Some W_3b0fc.
Proof. vm_refl. Qed.
Lemma D_3b0fc : decode_any W_3b0fc = Some (Load SZ4 true 7 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b100 : bv 32 := 0x00788333.
Lemma F_3b100 : fetch_word Ubsan.M.loaded_segments (0x3b100 : word) = Some W_3b100.
Proof. vm_refl. Qed.
Lemma D_3b100 : decode_any W_3b100 = Some (Op ALU_ADD 6 17 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b104 : bv 32 := 0x007883bb.
Lemma F_3b104 : fetch_word Ubsan.M.loaded_segments (0x3b104 : word) = Some W_3b104.
Proof. vm_refl. Qed.
Lemma D_3b104 : decode_any W_3b104 = Some (Op32 ALU_ADD 7 17 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b108 : bv 32 := 0x2c639063.
Lemma F_3b108 : fetch_word Ubsan.M.loaded_segments (0x3b108 : word) = Some W_3b108.
Proof. vm_refl. Qed.
Lemma D_3b108 : decode_any W_3b108 = Some (Branch BC_NE 7 6 704, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b10c : bv 32 := 0x0003031b.
Lemma F_3b10c : fetch_word Ubsan.M.loaded_segments (0x3b10c : word) = Some W_3b10c.
Proof. vm_refl. Qed.
Lemma D_3b10c : decode_any W_3b10c = Some (OpImm32 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b110 : bv 32 := 0x00530e33.
Lemma F_3b110 : fetch_word Ubsan.M.loaded_segments (0x3b110 : word) = Some W_3b110.
Proof. vm_refl. Qed.
Lemma D_3b110 : decode_any W_3b110 = Some (Op ALU_ADD 28 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b114 : bv 32 := 0x001e3393.
Lemma F_3b114 : fetch_word Ubsan.M.loaded_segments (0x3b114 : word) = Some W_3b114.
Proof. vm_refl. Qed.
Lemma D_3b114 : decode_any W_3b114 = Some (OpImm ALU_SLTU 7 28 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b118 : bv 32 := 0x2a768863.
Lemma F_3b118 : fetch_word Ubsan.M.loaded_segments (0x3b118 : word) = Some W_3b118.
Proof. vm_refl. Qed.
Lemma D_3b118 : decode_any W_3b118 = Some (Branch BC_EQ 13 7 688, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b11c : bv 32 := 0x005e32b3.
Lemma F_3b11c : fetch_word Ubsan.M.loaded_segments (0x3b11c : word) = Some W_3b11c.
Proof. vm_refl. Qed.
Lemma D_3b11c : decode_any W_3b11c = Some (Op ALU_SLTU 5 28 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b120 : bv 32 := 0x00032313.
Lemma F_3b120 : fetch_word Ubsan.M.loaded_segments (0x3b120 : word) = Some W_3b120.
Proof. vm_refl. Qed.
Lemma D_3b120 : decode_any W_3b120 = Some (OpImm ALU_SLT 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b124 : bv 32 := 0x0062c2b3.
Lemma F_3b124 : fetch_word Ubsan.M.loaded_segments (0x3b124 : word) = Some W_3b124.
Proof. vm_refl. Qed.
Lemma D_3b124 : decode_any W_3b124 = Some (Op ALU_XOR 5 5 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b128 : bv 32 := 0x0012c293.
Lemma F_3b128 : fetch_word Ubsan.M.loaded_segments (0x3b128 : word) = Some W_3b128.
Proof. vm_refl. Qed.
Lemma D_3b128 : decode_any W_3b128 = Some (OpImm ALU_XOR 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b12c : bv 32 := 0x28028e63.
Lemma F_3b12c : fetch_word Ubsan.M.loaded_segments (0x3b12c : word) = Some W_3b12c.
Proof. vm_refl. Qed.
Lemma D_3b12c : decode_any W_3b12c = Some (Branch BC_EQ 5 0 668, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b130 : bv 32 := 0x28ee0c63.
Lemma F_3b130 : fetch_word Ubsan.M.loaded_segments (0x3b130 : word) = Some W_3b130.
Proof. vm_refl. Qed.
Lemma D_3b130 : decode_any W_3b130 = Some (Branch BC_EQ 28 14 664, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b134 : bv 32 := 0x03412283.
Lemma F_3b134 : fetch_word Ubsan.M.loaded_segments (0x3b134 : word) = Some W_3b134.
Proof. vm_refl. Qed.
Lemma D_3b134 : decode_any W_3b134 = Some (Load SZ4 true 5 2 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b138 : bv 32 := 0x28505863.
Lemma F_3b138 : fetch_word Ubsan.M.loaded_segments (0x3b138 : word) = Some W_3b138.
Proof. vm_refl. Qed.
Lemma D_3b138 : decode_any W_3b138 = Some (Branch BC_GE 0 5 656, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b13c : bv 32 := 0x00000313.
Lemma F_3b13c : fetch_word Ubsan.M.loaded_segments (0x3b13c : word) = Some W_3b13c.
Proof. vm_refl. Qed.
Lemma D_3b13c : decode_any W_3b13c = Some (OpImm ALU_ADD 6 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b140 : bv 32 := 0x02013383.
Lemma F_3b140 : fetch_word Ubsan.M.loaded_segments (0x3b140 : word) = Some W_3b140.
Proof. vm_refl. Qed.
Lemma D_3b140 : decode_any W_3b140 = Some (Load SZ8 true 7 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b144 : bv 32 := 0x003e4e13.
Lemma F_3b144 : fetch_word Ubsan.M.loaded_segments (0x3b144 : word) = Some W_3b144.
Proof. vm_refl. Qed.
Lemma D_3b144 : decode_any W_3b144 = Some (OpImm ALU_XOR 28 28 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b148 : bv 32 := 0x03816f83.
Lemma F_3b148 : fetch_word Ubsan.M.loaded_segments (0x3b148 : word) = Some W_3b148.
Proof. vm_refl. Qed.
Lemma D_3b148 : decode_any W_3b148 = Some (Load SZ4 false 31 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b14c : bv 32 := 0x000e4e03.
Lemma F_3b14c : fetch_word Ubsan.M.loaded_segments (0x3b14c : word) = Some W_3b14c.
Proof. vm_refl. Qed.
Lemma D_3b14c : decode_any W_3b14c = Some (Load SZ1 false 28 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b150 : bv 32 := 0x0013be93.
Lemma F_3b150 : fetch_word Ubsan.M.loaded_segments (0x3b150 : word) = Some W_3b150.
Proof. vm_refl. Qed.
Lemma D_3b150 : decode_any W_3b150 = Some (OpImm ALU_SLTU 29 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b154 : bv 32 := 0x0073ff13.
Lemma F_3b154 : fetch_word Ubsan.M.loaded_segments (0x3b154 : word) = Some W_3b154.
Proof. vm_refl. Qed.
Lemma D_3b154 : decode_any W_3b154 = Some (OpImm ALU_AND 30 7 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b158 : bv 32 := 0x01e03f33.
Lemma F_3b158 : fetch_word Ubsan.M.loaded_segments (0x3b158 : word) = Some W_3b158.
Proof. vm_refl. Qed.
Lemma D_3b158 : decode_any W_3b158 = Some (Op ALU_SLTU 30 0 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b15c : bv 32 := 0x01eeeeb3.
Lemma F_3b15c : fetch_word Ubsan.M.loaded_segments (0x3b15c : word) = Some W_3b15c.
Proof. vm_refl. Qed.
Lemma D_3b15c : decode_any W_3b15c = Some (Op ALU_OR 29 29 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b160 : bv 32 := 0x000f8f1b.
Lemma F_3b160 : fetch_word Ubsan.M.loaded_segments (0x3b160 : word) = Some W_3b160.
Proof. vm_refl. Qed.
Lemma D_3b160 : decode_any W_3b160 = Some (OpImm32 30 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b164 : bv 32 := 0x002f9f93.
Lemma F_3b164 : fetch_word Ubsan.M.loaded_segments (0x3b164 : word) = Some W_3b164.
Proof. vm_refl. Qed.
Lemma D_3b164 : decode_any W_3b164 = Some (ShiftImm ALU_SLL 31 31 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b168 : bv 32 := 0x20f78753.
Lemma F_3b168 : fetch_word Ubsan.M.loaded_segments (0x3b168 : word) = Some W_3b168.
Proof. vm_refl. Qed.
Lemma D_3b168 : decode_any W_3b168 = Some (Fsgnj F_SGNJ FMT_S 14 15 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b16c : bv 32 := 0x20f786d3.
Lemma F_3b16c : fetch_word Ubsan.M.loaded_segments (0x3b16c : word) = Some W_3b16c.
Proof. vm_refl. Qed.
Lemma D_3b16c : decode_any W_3b16c = Some (Fsgnj F_SGNJ FMT_S 13 15 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b170 : bv 32 := 0x00c0006f.
Lemma F_3b170 : fetch_word Ubsan.M.loaded_segments (0x3b170 : word) = Some W_3b170.
Proof. vm_refl. Qed.
Lemma D_3b170 : decode_any W_3b170 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b174 : bv 32 := 0x00130313.
Lemma F_3b174 : fetch_word Ubsan.M.loaded_segments (0x3b174 : word) = Some W_3b174.
Proof. vm_refl. Qed.
Lemma D_3b174 : decode_any W_3b174 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b178 : bv 32 := 0x16530063.
Lemma F_3b178 : fetch_word Ubsan.M.loaded_segments (0x3b178 : word) = Some W_3b178.
Proof. vm_refl. Qed.
Lemma D_3b178 : decode_any W_3b178 = Some (Branch BC_EQ 6 5 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b17c : bv 32 := 0x00030b1b.
Lemma F_3b17c : fetch_word Ubsan.M.loaded_segments (0x3b17c : word) = Some W_3b17c.
Proof. vm_refl. Qed.
Lemma D_3b17c : decode_any W_3b17c = Some (OpImm32 22 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b180 : bv 32 := 0x01658a33.
Lemma F_3b180 : fetch_word Ubsan.M.loaded_segments (0x3b180 : word) = Some W_3b180.
Proof. vm_refl. Qed.
Lemma D_3b180 : decode_any W_3b180 = Some (Op ALU_ADD 20 11 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b184 : bv 32 := 0x01658b3b.
Lemma F_3b184 : fetch_word Ubsan.M.loaded_segments (0x3b184 : word) = Some W_3b184.
Proof. vm_refl. Qed.
Lemma D_3b184 : decode_any W_3b184 = Some (Op32 ALU_ADD 22 11 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b188 : bv 32 := 0x254b1063.
Lemma F_3b188 : fetch_word Ubsan.M.loaded_segments (0x3b188 : word) = Some W_3b188.
Proof. vm_refl. Qed.
Lemma D_3b188 : decode_any W_3b188 = Some (Branch BC_NE 22 20 576, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b18c : bv 32 := 0x000a0a1b.
Lemma F_3b18c : fetch_word Ubsan.M.loaded_segments (0x3b18c : word) = Some W_3b18c.
Proof. vm_refl. Qed.
Lemma D_3b18c : decode_any W_3b18c = Some (OpImm32 20 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b190 : bv 32 := 0x033a0b33.
Lemma F_3b190 : fetch_word Ubsan.M.loaded_segments (0x3b190 : word) = Some W_3b190.
Proof. vm_refl. Qed.
Lemma D_3b190 : decode_any W_3b190 = Some (Mul M_MUL 22 20 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b194 : bv 32 := 0x033a0a3b.
Lemma F_3b194 : fetch_word Ubsan.M.loaded_segments (0x3b194 : word) = Some W_3b194.
Proof. vm_refl. Qed.
Lemma D_3b194 : decode_any W_3b194 = Some (Mul32 M_MUL 20 20 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b198 : bv 32 := 0x236a1863.
Lemma F_3b198 : fetch_word Ubsan.M.loaded_segments (0x3b198 : word) = Some W_3b198.
Proof. vm_refl. Qed.
Lemma D_3b198 : decode_any W_3b198 = Some (Branch BC_NE 20 22 560, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b19c : bv 32 := 0x000b0b1b.
Lemma F_3b19c : fetch_word Ubsan.M.loaded_segments (0x3b19c : word) = Some W_3b19c.
Proof. vm_refl. Qed.
Lemma D_3b19c : decode_any W_3b19c = Some (OpImm32 22 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b1a0 : bv 32 := 0x002b1a13.
Lemma F_3b1a0 : fetch_word Ubsan.M.loaded_segments (0x3b1a0 : word) = Some W_3b1a0.
Proof. vm_refl. Qed.
Lemma D_3b1a0 : decode_any W_3b1a0 = Some (ShiftImm ALU_SLL 20 22 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b1a4 : bv 32 := 0x01448a33.
Lemma F_3b1a4 : fetch_word Ubsan.M.loaded_segments (0x3b1a4 : word) = Some W_3b1a4.
Proof. vm_refl. Qed.
Lemma D_3b1a4 : decode_any W_3b1a4 = Some (Op ALU_ADD 20 9 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b1a8 : bv 32 := 0x001a3b93.
Lemma F_3b1a8 : fetch_word Ubsan.M.loaded_segments (0x3b1a8 : word) = Some W_3b1a8.
Proof. vm_refl. Qed.
Lemma D_3b1a8 : decode_any W_3b1a8 = Some (OpImm ALU_SLTU 23 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b1ac : bv 32 := 0x21768e63.
Lemma F_3b1ac : fetch_word Ubsan.M.loaded_segments (0x3b1ac : word) = Some W_3b1ac.
Proof. vm_refl. Qed.
Lemma D_3b1ac : decode_any W_3b1ac = Some (Branch BC_EQ 13 23 540, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b1b0 : bv 32 := 0x009a3bb3.
Lemma F_3b1b0 : fetch_word Ubsan.M.loaded_segments (0x3b1b0 : word) = Some W_3b1b0.
Proof. vm_refl. Qed.
Lemma D_3b1b0 : decode_any W_3b1b0 = Some (Op ALU_SLTU 23 20 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b1b4 : bv 32 := 0x000b2b13.
Lemma F_3b1b4 : fetch_word Ubsan.M.loaded_segments (0x3b1b4 : word) = Some W_3b1b4.
Proof. vm_refl. Qed.
Lemma D_3b1b4 : decode_any W_3b1b4 = Some (OpImm ALU_SLT 22 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b1b8 : bv 32 := 0x016bcb33.
Lemma F_3b1b8 : fetch_word Ubsan.M.loaded_segments (0x3b1b8 : word) = Some W_3b1b8.
Proof. vm_refl. Qed.
Lemma D_3b1b8 : decode_any W_3b1b8 = Some (Op ALU_XOR 22 23 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b1bc : bv 32 := 0x001b4b13.
Lemma F_3b1bc : fetch_word Ubsan.M.loaded_segments (0x3b1bc : word) = Some W_3b1bc.
Proof. vm_refl. Qed.
Lemma D_3b1bc : decode_any W_3b1bc = Some (OpImm ALU_XOR 22 22 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b1c0 : bv 32 := 0x200b0463.
Lemma F_3b1c0 : fetch_word Ubsan.M.loaded_segments (0x3b1c0 : word) = Some W_3b1c0.
Proof. vm_refl. Qed.
Lemma D_3b1c0 : decode_any W_3b1c0 = Some (Branch BC_EQ 22 0 520, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b1c4 : bv 32 := 0xfbe058e3.
Lemma F_3b1c4 : fetch_word Ubsan.M.loaded_segments (0x3b1c4 : word) = Some W_3b1c4.
Proof. vm_refl. Qed.
Lemma D_3b1c4 : decode_any W_3b1c4 = Some (Branch BC_GE 0 30 8112, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b1c8 : bv 32 := 0x00000b13.
Lemma F_3b1c8 : fetch_word Ubsan.M.loaded_segments (0x3b1c8 : word) = Some W_3b1c8.
Proof. vm_refl. Qed.
Lemma D_3b1c8 : decode_any W_3b1c8 = Some (OpImm ALU_ADD 22 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b1cc : bv 32 := 0x00000b93.
Lemma F_3b1cc : fetch_word Ubsan.M.loaded_segments (0x3b1cc : word) = Some W_3b1cc.
Proof. vm_refl. Qed.
Lemma D_3b1cc : decode_any W_3b1cc = Some (OpImm ALU_ADD 23 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b1d0 : bv 32 := 0x00331c13.
Lemma F_3b1d0 : fetch_word Ubsan.M.loaded_segments (0x3b1d0 : word) = Some W_3b1d0.
Proof. vm_refl. Qed.
Lemma D_3b1d0 : decode_any W_3b1d0 = Some (ShiftImm ALU_SLL 24 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b1d4 : bv 32 := 0x01788d33.
Lemma F_3b1d4 : fetch_word Ubsan.M.loaded_segments (0x3b1d4 : word) = Some W_3b1d4.
Proof. vm_refl. Qed.
Lemma D_3b1d4 : decode_any W_3b1d4 = Some (Op ALU_ADD 26 17 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b1d8 : bv 32 := 0x01788cbb.
Lemma F_3b1d8 : fetch_word Ubsan.M.loaded_segments (0x3b1d8 : word) = Some W_3b1d8.
Proof. vm_refl. Qed.
Lemma D_3b1d8 : decode_any W_3b1d8 = Some (Op32 ALU_ADD 25 17 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b1dc : bv 32 := 0x1fac9663.
Lemma F_3b1dc : fetch_word Ubsan.M.loaded_segments (0x3b1dc : word) = Some W_3b1dc.
Proof. vm_refl. Qed.
Lemma D_3b1dc : decode_any W_3b1dc = Some (Branch BC_NE 25 26 492, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b1e0 : bv 32 := 0x000d0d1b.
Lemma F_3b1e0 : fetch_word Ubsan.M.loaded_segments (0x3b1e0 : word) = Some W_3b1e0.
Proof. vm_refl. Qed.
Lemma D_3b1e0 : decode_any W_3b1e0 = Some (OpImm32 26 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b1e4 : bv 32 := 0x014d0cb3.
Lemma F_3b1e4 : fetch_word Ubsan.M.loaded_segments (0x3b1e4 : word) = Some W_3b1e4.
Proof. vm_refl. Qed.
Lemma D_3b1e4 : decode_any W_3b1e4 = Some (Op ALU_ADD 25 26 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b1e8 : bv 32 := 0x001cbd93.
Lemma F_3b1e8 : fetch_word Ubsan.M.loaded_segments (0x3b1e8 : word) = Some W_3b1e8.
Proof. vm_refl. Qed.
Lemma D_3b1e8 : decode_any W_3b1e8 = Some (OpImm ALU_SLTU 27 25 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b1ec : bv 32 := 0x1db68e63.
Lemma F_3b1ec : fetch_word Ubsan.M.loaded_segments (0x3b1ec : word) = Some W_3b1ec.
Proof. vm_refl. Qed.
Lemma D_3b1ec : decode_any W_3b1ec = Some (Branch BC_EQ 13 27 476, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b1f0 : bv 32 := 0x014cbdb3.
Lemma F_3b1f0 : fetch_word Ubsan.M.loaded_segments (0x3b1f0 : word) = Some W_3b1f0.
Proof. vm_refl. Qed.
Lemma D_3b1f0 : decode_any W_3b1f0 = Some (Op ALU_SLTU 27 25 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b1f4 : bv 32 := 0x000d2d13.
Lemma F_3b1f4 : fetch_word Ubsan.M.loaded_segments (0x3b1f4 : word) = Some W_3b1f4.
Proof. vm_refl. Qed.
Lemma D_3b1f4 : decode_any W_3b1f4 = Some (OpImm ALU_SLT 26 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b1f8 : bv 32 := 0x01adcd33.
Lemma F_3b1f8 : fetch_word Ubsan.M.loaded_segments (0x3b1f8 : word) = Some W_3b1f8.
Proof. vm_refl. Qed.
Lemma D_3b1f8 : decode_any W_3b1f8 = Some (Op ALU_XOR 26 27 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b1fc : bv 32 := 0x001d4d13.
Lemma F_3b1fc : fetch_word Ubsan.M.loaded_segments (0x3b1fc : word) = Some W_3b1fc.
Proof. vm_refl. Qed.
Lemma D_3b1fc : decode_any W_3b1fc = Some (OpImm ALU_XOR 26 26 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b200 : bv 32 := 0x1c0d0463.
Lemma F_3b200 : fetch_word Ubsan.M.loaded_segments (0x3b200 : word) = Some W_3b200.
Proof. vm_refl. Qed.
Lemma D_3b200 : decode_any W_3b200 = Some (Branch BC_EQ 26 0 456, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b204 : bv 32 := 0x1cec8263.
Lemma F_3b204 : fetch_word Ubsan.M.loaded_segments (0x3b204 : word) = Some W_3b204.
Proof. vm_refl. Qed.
Lemma D_3b204 : decode_any W_3b204 = Some (Branch BC_EQ 25 14 452, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b208 : bv 32 := 0x1c0e9063.
Lemma F_3b208 : fetch_word Ubsan.M.loaded_segments (0x3b208 : word) = Some W_3b208.
Proof. vm_refl. Qed.
Lemma D_3b208 : decode_any W_3b208 = Some (Branch BC_NE 29 0 448, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b20c : bv 32 := 0x0103bd83.
Lemma F_3b20c : fetch_word Ubsan.M.loaded_segments (0x3b20c : word) = Some W_3b20c.
Proof. vm_refl. Qed.
Lemma D_3b20c : decode_any W_3b20c = Some (Load SZ8 true 27 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b210 : bv 32 := 0x018d8d33.
Lemma F_3b210 : fetch_word Ubsan.M.loaded_segments (0x3b210 : word) = Some W_3b210.
Proof. vm_refl. Qed.
Lemma D_3b210 : decode_any W_3b210 = Some (Op ALU_ADD 26 27 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b214 : bv 32 := 0x01b030b3.
Lemma F_3b214 : fetch_word Ubsan.M.loaded_segments (0x3b214 : word) = Some W_3b214.
Proof. vm_refl. Qed.
Lemma D_3b214 : decode_any W_3b214 = Some (Op ALU_SLTU 1 0 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b218 : bv 32 := 0x001d3a93.
Lemma F_3b218 : fetch_word Ubsan.M.loaded_segments (0x3b218 : word) = Some W_3b218.
Proof. vm_refl. Qed.
Lemma D_3b218 : decode_any W_3b218 = Some (OpImm ALU_SLTU 21 26 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b21c : bv 32 := 0x1b508663.
Lemma F_3b21c : fetch_word Ubsan.M.loaded_segments (0x3b21c : word) = Some W_3b21c.
Proof. vm_refl. Qed.
Lemma D_3b21c : decode_any W_3b21c = Some (Branch BC_EQ 1 21 428, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b220 : bv 32 := 0x1bbd6463.
Lemma F_3b220 : fetch_word Ubsan.M.loaded_segments (0x3b220 : word) = Some W_3b220.
Proof. vm_refl. Qed.
Lemma D_3b220 : decode_any W_3b220 = Some (Branch BC_LTU 26 27 424, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b224 : bv 32 := 0x1a0d8263.
Lemma F_3b224 : fetch_word Ubsan.M.loaded_segments (0x3b224 : word) = Some W_3b224.
Proof. vm_refl. Qed.
Lemma D_3b224 : decode_any W_3b224 = Some (Branch BC_EQ 27 0 420, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b228 : bv 32 := 0x007d7a93.
Lemma F_3b228 : fetch_word Ubsan.M.loaded_segments (0x3b228 : word) = Some W_3b228.
Proof. vm_refl. Qed.
Lemma D_3b228 : decode_any W_3b228 = Some (OpImm ALU_AND 21 26 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b22c : bv 32 := 0x180a9e63.
Lemma F_3b22c : fetch_word Ubsan.M.loaded_segments (0x3b22c : word) = Some W_3b22c.
Proof. vm_refl. Qed.
Lemma D_3b22c : decode_any W_3b22c = Some (Branch BC_NE 21 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b230 : bv 32 := 0x000d3d83.
Lemma F_3b230 : fetch_word Ubsan.M.loaded_segments (0x3b230 : word) = Some W_3b230.
Proof. vm_refl. Qed.
Lemma D_3b230 : decode_any W_3b230 = Some (Load SZ8 true 27 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b234 : bv 32 := 0x016d8d33.
Lemma F_3b234 : fetch_word Ubsan.M.loaded_segments (0x3b234 : word) = Some W_3b234.
Proof. vm_refl. Qed.
Lemma D_3b234 : decode_any W_3b234 = Some (Op ALU_ADD 26 27 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b238 : bv 32 := 0x19bd6863.
Lemma F_3b238 : fetch_word Ubsan.M.loaded_segments (0x3b238 : word) = Some W_3b238.
Proof. vm_refl. Qed.
Lemma D_3b238 : decode_any W_3b238 = Some (Branch BC_LTU 26 27 400, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b23c : bv 32 := 0x01b03ab3.
Lemma F_3b23c : fetch_word Ubsan.M.loaded_segments (0x3b23c : word) = Some W_3b23c.
Proof. vm_refl. Qed.
Lemma D_3b23c : decode_any W_3b23c = Some (Op ALU_SLTU 21 0 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b240 : bv 32 := 0x001d3093.
Lemma F_3b240 : fetch_word Ubsan.M.loaded_segments (0x3b240 : word) = Some W_3b240.
Proof. vm_refl. Qed.
Lemma D_3b240 : decode_any W_3b240 = Some (OpImm ALU_SLTU 1 26 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b244 : bv 32 := 0x001acab3.
Lemma F_3b244 : fetch_word Ubsan.M.loaded_segments (0x3b244 : word) = Some W_3b244.
Proof. vm_refl. Qed.
Lemma D_3b244 : decode_any W_3b244 = Some (Op ALU_XOR 21 21 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b248 : bv 32 := 0x180a8063.
Lemma F_3b248 : fetch_word Ubsan.M.loaded_segments (0x3b248 : word) = Some W_3b248.
Proof. vm_refl. Qed.
Lemma D_3b248 : decode_any W_3b248 = Some (Branch BC_EQ 21 0 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b24c : bv 32 := 0x160d8e63.
Lemma F_3b24c : fetch_word Ubsan.M.loaded_segments (0x3b24c : word) = Some W_3b24c.
Proof. vm_refl. Qed.
Lemma D_3b24c : decode_any W_3b24c = Some (Branch BC_EQ 27 0 380, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b250 : bv 32 := 0x01bb0db3.
Lemma F_3b250 : fetch_word Ubsan.M.loaded_segments (0x3b250 : word) = Some W_3b250.
Proof. vm_refl. Qed.
Lemma D_3b250 : decode_any W_3b250 = Some (Op ALU_ADD 27 22 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b254 : bv 32 := 0x003dfa93.
Lemma F_3b254 : fetch_word Ubsan.M.loaded_segments (0x3b254 : word) = Some W_3b254.
Proof. vm_refl. Qed.
Lemma D_3b254 : decode_any W_3b254 = Some (OpImm ALU_AND 21 27 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b258 : bv 32 := 0x160a9863.
Lemma F_3b258 : fetch_word Ubsan.M.loaded_segments (0x3b258 : word) = Some W_3b258.
Proof. vm_refl. Qed.
Lemma D_3b258 : decode_any W_3b258 = Some (Branch BC_NE 21 0 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b25c : bv 32 := 0x01043d83.
Lemma F_3b25c : fetch_word Ubsan.M.loaded_segments (0x3b25c : word) = Some W_3b25c.
Proof. vm_refl. Qed.
Lemma D_3b25c : decode_any W_3b25c = Some (Load SZ8 true 27 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b260 : bv 32 := 0x160d8463.
Lemma F_3b260 : fetch_word Ubsan.M.loaded_segments (0x3b260 : word) = Some W_3b260.
Proof. vm_refl. Qed.
Lemma D_3b260 : decode_any W_3b260 = Some (Branch BC_EQ 27 0 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b264 : bv 32 := 0x007dfa93.
Lemma F_3b264 : fetch_word Ubsan.M.loaded_segments (0x3b264 : word) = Some W_3b264.
Proof. vm_refl. Qed.
Lemma D_3b264 : decode_any W_3b264 = Some (OpImm ALU_AND 21 27 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b268 : bv 32 := 0x160a9063.
Lemma F_3b268 : fetch_word Ubsan.M.loaded_segments (0x3b268 : word) = Some W_3b268.
Proof. vm_refl. Qed.
Lemma D_3b268 : decode_any W_3b268 = Some (Branch BC_NE 21 0 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b26c : bv 32 := 0x003cca93.
Lemma F_3b26c : fetch_word Ubsan.M.loaded_segments (0x3b26c : word) = Some W_3b26c.
Proof. vm_refl. Qed.
Lemma D_3b26c : decode_any W_3b26c = Some (OpImm ALU_XOR 21 25 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b270 : bv 32 := 0x000acc83.
Lemma F_3b270 : fetch_word Ubsan.M.loaded_segments (0x3b270 : word) = Some W_3b270.
Proof. vm_refl. Qed.
Lemma D_3b270 : decode_any W_3b270 = Some (Load SZ1 false 25 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b274 : bv 32 := 0x000db083.
Lemma F_3b274 : fetch_word Ubsan.M.loaded_segments (0x3b274 : word) = Some W_3b274.
Proof. vm_refl. Qed.
Lemma D_3b274 : decode_any W_3b274 = Some (Load SZ8 true 1 27 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b278 : bv 32 := 0x419e0ab3.
Lemma F_3b278 : fetch_word Ubsan.M.loaded_segments (0x3b278 : word) = Some W_3b278.
Proof. vm_refl. Qed.
Lemma D_3b278 : decode_any W_3b278 = Some (Op ALU_SUB 21 28 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b27c : bv 32 := 0x43fadd93.
Lemma F_3b27c : fetch_word Ubsan.M.loaded_segments (0x3b27c : word) = Some W_3b27c.
Proof. vm_refl. Qed.
Lemma D_3b27c : decode_any W_3b27c = Some (ShiftImm ALU_SRA 27 21 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b280 : bv 32 := 0x01bacab3.
Lemma F_3b280 : fetch_word Ubsan.M.loaded_segments (0x3b280 : word) = Some W_3b280.
Proof. vm_refl. Qed.
Lemma D_3b280 : decode_any W_3b280 = Some (Op ALU_XOR 21 21 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b284 : bv 32 := 0x41ba8ab3.
Lemma F_3b284 : fetch_word Ubsan.M.loaded_segments (0x3b284 : word) = Some W_3b284.
Proof. vm_refl. Qed.
Lemma D_3b284 : decode_any W_3b284 = Some (Op ALU_SUB 21 21 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b288 : bv 32 := 0x002a9a93.
Lemma F_3b288 : fetch_word Ubsan.M.loaded_segments (0x3b288 : word) = Some W_3b288.
Proof. vm_refl. Qed.
Lemma D_3b288 : decode_any W_3b288 = Some (ShiftImm ALU_SLL 21 21 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b28c : bv 32 := 0x01508db3.
Lemma F_3b28c : fetch_word Ubsan.M.loaded_segments (0x3b28c : word) = Some W_3b28c.
Proof. vm_refl. Qed.
Lemma D_3b28c : decode_any W_3b28c = Some (Op ALU_ADD 27 1 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b290 : bv 32 := 0x121dec63.
Lemma F_3b290 : fetch_word Ubsan.M.loaded_segments (0x3b290 : word) = Some W_3b290.
Proof. vm_refl. Qed.
Lemma D_3b290 : decode_any W_3b290 = Some (Branch BC_LTU 27 1 312, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b294 : bv 32 := 0x00103ab3.
Lemma F_3b294 : fetch_word Ubsan.M.loaded_segments (0x3b294 : word) = Some W_3b294.
Proof. vm_refl. Qed.
Lemma D_3b294 : decode_any W_3b294 = Some (Op ALU_SLTU 21 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b298 : bv 32 := 0x001db913.
Lemma F_3b298 : fetch_word Ubsan.M.loaded_segments (0x3b298 : word) = Some W_3b298.
Proof. vm_refl. Qed.
Lemma D_3b298 : decode_any W_3b298 = Some (OpImm ALU_SLTU 18 27 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b29c : bv 32 := 0x012ac933.
Lemma F_3b29c : fetch_word Ubsan.M.loaded_segments (0x3b29c : word) = Some W_3b29c.
Proof. vm_refl. Qed.
Lemma D_3b29c : decode_any W_3b29c = Some (Op ALU_XOR 18 21 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b2a0 : bv 32 := 0x12090463.
Lemma F_3b2a0 : fetch_word Ubsan.M.loaded_segments (0x3b2a0 : word) = Some W_3b2a0.
Proof. vm_refl. Qed.
Lemma D_3b2a0 : decode_any W_3b2a0 = Some (Branch BC_EQ 18 0 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b2a4 : bv 32 := 0x12008263.
Lemma F_3b2a4 : fetch_word Ubsan.M.loaded_segments (0x3b2a4 : word) = Some W_3b2a4.
Proof. vm_refl. Qed.
Lemma D_3b2a4 : decode_any W_3b2a4 = Some (Branch BC_EQ 1 0 292, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b2a8 : bv 32 := 0x003df913.
Lemma F_3b2a8 : fetch_word Ubsan.M.loaded_segments (0x3b2a8 : word) = Some W_3b2a8.
Proof. vm_refl. Qed.
Lemma D_3b2a8 : decode_any W_3b2a8 = Some (OpImm ALU_AND 18 27 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b2ac : bv 32 := 0x10091e63.
Lemma F_3b2ac : fetch_word Ubsan.M.loaded_segments (0x3b2ac : word) = Some W_3b2ac.
Proof. vm_refl. Qed.
Lemma D_3b2ac : decode_any W_3b2ac = Some (Branch BC_NE 18 0 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b2b0 : bv 32 := 0x000d2607.
Lemma F_3b2b0 : fetch_word Ubsan.M.loaded_segments (0x3b2b0 : word) = Some W_3b2b0.
Proof. vm_refl. Qed.
Lemma D_3b2b0 : decode_any W_3b2b0 = Some (FLoad FMT_S 12 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b2b4 : bv 32 := 0x000da587.
Lemma F_3b2b4 : fetch_word Ubsan.M.loaded_segments (0x3b2b4 : word) = Some W_3b2b4.
Proof. vm_refl. Qed.
Lemma D_3b2b4 : decode_any W_3b2b4 = Some (FLoad FMT_S 11 27 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b2b8 : bv 32 := 0xd01cf553.
Lemma F_3b2b8 : fetch_word Ubsan.M.loaded_segments (0x3b2b8 : word) = Some W_3b2b8.
Proof. vm_refl. Qed.
Lemma D_3b2b8 : decode_any W_3b2b8 = Some (Fcvt FC_S FC_WU 10 25 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b2bc : bv 32 := 0x004b0b13.
Lemma F_3b2bc : fetch_word Ubsan.M.loaded_segments (0x3b2bc : word) = Some W_3b2bc.
Proof. vm_refl. Qed.
Lemma D_3b2bc : decode_any W_3b2bc = Some (OpImm ALU_ADD 22 22 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b2c0 : bv 32 := 0x10b67653.
Lemma F_3b2c0 : fetch_word Ubsan.M.loaded_segments (0x3b2c0 : word) = Some W_3b2c0.
Proof. vm_refl. Qed.
Lemma D_3b2c0 : decode_any W_3b2c0 = Some (Fari F_MUL FMT_S 12 12 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b2c4 : bv 32 := 0x68c576c3.
Lemma F_3b2c4 : fetch_word Ubsan.M.loaded_segments (0x3b2c4 : word) = Some W_3b2c4.
Proof. vm_refl. Qed.
Lemma D_3b2c4 : decode_any W_3b2c4 = Some (Fma F_MADD FMT_S 13 10 12 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b2c8 : bv 32 := 0x00c77753.
Lemma F_3b2c8 : fetch_word Ubsan.M.loaded_segments (0x3b2c8 : word) = Some W_3b2c8.
Proof. vm_refl. Qed.
Lemma D_3b2c8 : decode_any W_3b2c8 = Some (Fari F_ADD FMT_S 14 14 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b2cc : bv 32 := 0x001b8b9b.
Lemma F_3b2cc : fetch_word Ubsan.M.loaded_segments (0x3b2cc : word) = Some W_3b2cc.
Proof. vm_refl. Qed.
Lemma D_3b2cc : decode_any W_3b2cc = Some (OpImm32 23 23 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b2d0 : bv 32 := 0xf16f92e3.
Lemma F_3b2d0 : fetch_word Ubsan.M.loaded_segments (0x3b2d0 : word) = Some W_3b2d0.
Proof. vm_refl. Qed.
Lemma D_3b2d0 : decode_any W_3b2d0 = Some (Branch BC_NE 31 22 7940, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b2d4 : bv 32 := 0xea1ff06f.
Lemma F_3b2d4 : fetch_word Ubsan.M.loaded_segments (0x3b2d4 : word) = Some W_3b2d4.
Proof. vm_refl. Qed.
Lemma D_3b2d4 : decode_any W_3b2d4 = Some (Jal 0 2096800, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b2d8 : bv 32 := 0xfffd7297.
Lemma F_3b2d8 : fetch_word Ubsan.M.loaded_segments (0x3b2d8 : word) = Some W_3b2d8.
Proof. vm_refl. Qed.
Lemma D_3b2d8 : decode_any W_3b2d8 = Some (Auipc 5 1048535, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b2dc : bv 32 := 0x2e02b607.
Lemma F_3b2dc : fetch_word Ubsan.M.loaded_segments (0x3b2dc : word) = Some W_3b2dc.
Proof. vm_refl. Qed.
Lemma D_3b2dc : decode_any W_3b2dc = Some (FLoad FMT_D 12 5 736, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b2e0 : bv 32 := 0xfffd7297.
Lemma F_3b2e0 : fetch_word Ubsan.M.loaded_segments (0x3b2e0 : word) = Some W_3b2e0.
Proof. vm_refl. Qed.
Lemma D_3b2e0 : decode_any W_3b2e0 = Some (Auipc 5 1048535, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b2e4 : bv 32 := 0x2f02b587.
Lemma F_3b2e4 : fetch_word Ubsan.M.loaded_segments (0x3b2e4 : word) = Some W_3b2e4.
Proof. vm_refl. Qed.
Lemma D_3b2e4 : decode_any W_3b2e4 = Some (FLoad FMT_D 11 5 752, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b2e8 : bv 32 := 0x18e6f753.
Lemma F_3b2e8 : fetch_word Ubsan.M.loaded_segments (0x3b2e8 : word) = Some W_3b2e8.
Proof. vm_refl. Qed.
Lemma D_3b2e8 : decode_any W_3b2e8 = Some (Fari F_DIV FMT_S 14 13 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b2ec : bv 32 := 0x42070753.
Lemma F_3b2ec : fetch_word Ubsan.M.loaded_segments (0x3b2ec : word) = Some W_3b2ec.
Proof. vm_refl. Qed.
Lemma D_3b2ec : decode_any W_3b2ec = Some (Fcvt FC_D FC_S 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b2f0 : bv 32 := 0x02c77753.
Lemma F_3b2f0 : fetch_word Ubsan.M.loaded_segments (0x3b2f0 : word) = Some W_3b2f0.
Proof. vm_refl. Qed.
Lemma D_3b2f0 : decode_any W_3b2f0 = Some (Fari F_ADD FMT_D 14 14 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b2f4 : bv 32 := 0xa2e592d3.
Lemma F_3b2f4 : fetch_word Ubsan.M.loaded_segments (0x3b2f4 : word) = Some W_3b2f4.
Proof. vm_refl. Qed.
Lemma D_3b2f4 : decode_any W_3b2f4 = Some (Fcmp F_LT FMT_D 5 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b2f8 : bv 32 := 0x0c028863.
Lemma F_3b2f8 : fetch_word Ubsan.M.loaded_segments (0x3b2f8 : word) = Some W_3b2f8.
Proof. vm_refl. Qed.
Lemma D_3b2f8 : decode_any W_3b2f8 = Some (Branch BC_EQ 5 0 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b2fc : bv 32 := 0xfffd7297.
Lemma F_3b2fc : fetch_word Ubsan.M.loaded_segments (0x3b2fc : word) = Some W_3b2fc.
Proof. vm_refl. Qed.
Lemma D_3b2fc : decode_any W_3b2fc = Some (Auipc 5 1048535, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b300 : bv 32 := 0x28c2b687.
Lemma F_3b300 : fetch_word Ubsan.M.loaded_segments (0x3b300 : word) = Some W_3b300.
Proof. vm_refl. Qed.
Lemma D_3b300 : decode_any W_3b300 = Some (FLoad FMT_D 13 5 652, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b304 : bv 32 := 0xa2d712d3.
Lemma F_3b304 : fetch_word Ubsan.M.loaded_segments (0x3b304 : word) = Some W_3b304.
Proof. vm_refl. Qed.
Lemma D_3b304 : decode_any W_3b304 = Some (Fcmp F_LT FMT_D 5 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b308 : bv 32 := 0x0c028063.
Lemma F_3b308 : fetch_word Ubsan.M.loaded_segments (0x3b308 : word) = Some W_3b308.
Proof. vm_refl. Qed.
Lemma D_3b308 : decode_any W_3b308 = Some (Branch BC_EQ 5 0 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b30c : bv 32 := 0x00f802b3.
Lemma F_3b30c : fetch_word Ubsan.M.loaded_segments (0x3b30c : word) = Some W_3b30c.
Proof. vm_refl. Qed.
Lemma D_3b30c : decode_any W_3b30c = Some (Op ALU_ADD 5 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b310 : bv 32 := 0x0012b313.
Lemma F_3b310 : fetch_word Ubsan.M.loaded_segments (0x3b310 : word) = Some W_3b310.
Proof. vm_refl. Qed.
Lemma D_3b310 : decode_any W_3b310 = Some (OpImm ALU_SLTU 6 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b314 : bv 32 := 0x0a660a63.
Lemma F_3b314 : fetch_word Ubsan.M.loaded_segments (0x3b314 : word) = Some W_3b314.
Proof. vm_refl. Qed.
Lemma D_3b314 : decode_any W_3b314 = Some (Branch BC_EQ 12 6 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b318 : bv 32 := 0x0af2e863.
Lemma F_3b318 : fetch_word Ubsan.M.loaded_segments (0x3b318 : word) = Some W_3b318.
Proof. vm_refl. Qed.
Lemma D_3b318 : decode_any W_3b318 = Some (Branch BC_LTU 5 15 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b31c : bv 32 := 0x0ae28663.
Lemma F_3b31c : fetch_word Ubsan.M.loaded_segments (0x3b31c : word) = Some W_3b31c.
Proof. vm_refl. Qed.
Lemma D_3b31c : decode_any W_3b31c = Some (Branch BC_EQ 5 14 172, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b320 : bv 32 := 0xc2071353.
Lemma F_3b320 : fetch_word Ubsan.M.loaded_segments (0x3b320 : word) = Some W_3b320.
Proof. vm_refl. Qed.
Lemma D_3b320 : decode_any W_3b320 = Some (Fcvt FC_W FC_D 6 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b324 : bv 32 := 0x0032c293.
Lemma F_3b324 : fetch_word Ubsan.M.loaded_segments (0x3b324 : word) = Some W_3b324.
Proof. vm_refl. Qed.
Lemma D_3b324 : decode_any W_3b324 = Some (OpImm ALU_XOR 5 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b328 : bv 32 := 0x00628023.
Lemma F_3b328 : fetch_word Ubsan.M.loaded_segments (0x3b328 : word) = Some W_3b328.
Proof. vm_refl. Qed.
Lemma D_3b328 : decode_any W_3b328 = Some (Store SZ1 5 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b32c : bv 32 := 0x04412283.
Lemma F_3b32c : fetch_word Ubsan.M.loaded_segments (0x3b32c : word) = Some W_3b32c.
Proof. vm_refl. Qed.
Lemma D_3b32c : decode_any W_3b32c = Some (Load SZ4 true 5 2 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b330 : bv 32 := 0x00180813.
Lemma F_3b330 : fetch_word Ubsan.M.loaded_segments (0x3b330 : word) = Some W_3b330.
Proof. vm_refl. Qed.
Lemma D_3b330 : decode_any W_3b330 = Some (OpImm ALU_ADD 16 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b334 : bv 32 := 0x0018889b.
Lemma F_3b334 : fetch_word Ubsan.M.loaded_segments (0x3b334 : word) = Some W_3b334.
Proof. vm_refl. Qed.
Lemma D_3b334 : decode_any W_3b334 = Some (OpImm32 17 17 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b338 : bv 32 := 0xd6584ee3.
Lemma F_3b338 : fetch_word Ubsan.M.loaded_segments (0x3b338 : word) = Some W_3b338.
Proof. vm_refl. Qed.
Lemma D_3b338 : decode_any W_3b338 = Some (Branch BC_LT 16 5 7548, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b33c : bv 32 := 0xd21ff06f.
Lemma F_3b33c : fetch_word Ubsan.M.loaded_segments (0x3b33c : word) = Some W_3b33c.
Proof. vm_refl. Qed.
Lemma D_3b33c : decode_any W_3b33c = Some (Jal 0 2096416, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b340 : bv 32 := 0x00800613.
Lemma F_3b340 : fetch_word Ubsan.M.loaded_segments (0x3b340 : word) = Some W_3b340.
Proof. vm_refl. Qed.
Lemma D_3b340 : decode_any W_3b340 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b344 : bv 32 := 0x00100693.
Lemma F_3b344 : fetch_word Ubsan.M.loaded_segments (0x3b344 : word) = Some W_3b344.
Proof. vm_refl. Qed.
Lemma D_3b344 : decode_any W_3b344 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b348 : bv 32 := 0x00048513.
Lemma F_3b348 : fetch_word Ubsan.M.loaded_segments (0x3b348 : word) = Some W_3b348.
Proof. vm_refl. Qed.
Lemma D_3b348 : decode_any W_3b348 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b34c : bv 32 := 0x00090593.
Lemma F_3b34c : fetch_word Ubsan.M.loaded_segments (0x3b34c : word) = Some W_3b34c.
Proof. vm_refl. Qed.
Lemma D_3b34c : decode_any W_3b34c = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b350 : bv 32 := 0xd00eb0ef.
Lemma F_3b350 : fetch_word Ubsan.M.loaded_segments (0x3b350 : word) = Some W_3b350.
Proof. vm_refl. Qed.
Lemma D_3b350 : decode_any W_3b350 = Some (Jal 1 2012416, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b354 : bv 32 := 0x0380006f.
Lemma F_3b354 : fetch_word Ubsan.M.loaded_segments (0x3b354 : word) = Some W_3b354.
Proof. vm_refl. Qed.
Lemma D_3b354 : decode_any W_3b354 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b358 : bv 32 := 0x02010513.
Lemma F_3b358 : fetch_word Ubsan.M.loaded_segments (0x3b358 : word) = Some W_3b358.
Proof. vm_refl. Qed.
Lemma D_3b358 : decode_any W_3b358 = Some (OpImm ALU_ADD 10 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b35c : bv 32 := 0xa14fd0ef.
Lemma F_3b35c : fetch_word Ubsan.M.loaded_segments (0x3b35c : word) = Some W_3b35c.
Proof. vm_refl. Qed.
Lemma D_3b35c : decode_any W_3b35c = Some (Jal 1 2085396, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b360 : bv 32 := 0x0000a517.
Lemma F_3b360 : fetch_word Ubsan.M.loaded_segments (0x3b360 : word) = Some W_3b360.
Proof. vm_refl. Qed.
Lemma D_3b360 : decode_any W_3b360 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b364 : bv 32 := 0xb3853503.
Lemma F_3b364 : fetch_word Ubsan.M.loaded_segments (0x3b364 : word) = Some W_3b364.
Proof. vm_refl. Qed.
Lemma D_3b364 : decode_any W_3b364 = Some (Load SZ8 true 10 10 2872, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b368 : bv 32 := 0x00052503.
Lemma F_3b368 : fetch_word Ubsan.M.loaded_segments (0x3b368 : word) = Some W_3b368.
Proof. vm_refl. Qed.
Lemma D_3b368 : decode_any W_3b368 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b36c : bv 32 := 0x00500593.
Lemma F_3b36c : fetch_word Ubsan.M.loaded_segments (0x3b36c : word) = Some W_3b36c.
Proof. vm_refl. Qed.
Lemma D_3b36c : decode_any W_3b36c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b370 : bv 32 := 0x00a5cc63.
Lemma F_3b370 : fetch_word Ubsan.M.loaded_segments (0x3b370 : word) = Some W_3b370.
Proof. vm_refl. Qed.
Lemma D_3b370 : decode_any W_3b370 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b374 : bv 32 := 0xfffd6517.
Lemma F_3b374 : fetch_word Ubsan.M.loaded_segments (0x3b374 : word) = Some W_3b374.
Proof. vm_refl. Qed.
Lemma D_3b374 : decode_any W_3b374 = Some (Auipc 10 1048534, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b378 : bv 32 := 0xfffd7597.
Lemma F_3b378 : fetch_word Ubsan.M.loaded_segments (0x3b378 : word) = Some W_3b378.
Proof. vm_refl. Qed.
Lemma D_3b378 : decode_any W_3b378 = Some (Auipc 11 1048535, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b37c : bv 32 := 0x71150513.
Lemma F_3b37c : fetch_word Ubsan.M.loaded_segments (0x3b37c : word) = Some W_3b37c.
Proof. vm_refl. Qed.
Lemma D_3b37c : decode_any W_3b37c = Some (OpImm ALU_ADD 10 10 1809, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b380 : bv 32 := 0xc2458593.
Lemma F_3b380 : fetch_word Ubsan.M.loaded_segments (0x3b380 : word) = Some W_3b380.
Proof. vm_refl. Qed.
Lemma D_3b380 : decode_any W_3b380 = Some (OpImm ALU_ADD 11 11 3108, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b384 : bv 32 := 0xca5ff06f.
Lemma F_3b384 : fetch_word Ubsan.M.loaded_segments (0x3b384 : word) = Some W_3b384.
Proof. vm_refl. Qed.
Lemma D_3b384 : decode_any W_3b384 = Some (Jal 0 2096292, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b388 : bv 32 := 0x00000513.
Lemma F_3b388 : fetch_word Ubsan.M.loaded_segments (0x3b388 : word) = Some W_3b388.
Proof. vm_refl. Qed.
Lemma D_3b388 : decode_any W_3b388 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b38c : bv 32 := 0x0a813083.
Lemma F_3b38c : fetch_word Ubsan.M.loaded_segments (0x3b38c : word) = Some W_3b38c.
Proof. vm_refl. Qed.
Lemma D_3b38c : decode_any W_3b38c = Some (Load SZ8 true 1 2 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b390 : bv 32 := 0x0a013403.
Lemma F_3b390 : fetch_word Ubsan.M.loaded_segments (0x3b390 : word) = Some W_3b390.
Proof. vm_refl. Qed.
Lemma D_3b390 : decode_any W_3b390 = Some (Load SZ8 true 8 2 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b394 : bv 32 := 0x09813483.
Lemma F_3b394 : fetch_word Ubsan.M.loaded_segments (0x3b394 : word) = Some W_3b394.
Proof. vm_refl. Qed.
Lemma D_3b394 : decode_any W_3b394 = Some (Load SZ8 true 9 2 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b398 : bv 32 := 0x09013903.
Lemma F_3b398 : fetch_word Ubsan.M.loaded_segments (0x3b398 : word) = Some W_3b398.
Proof. vm_refl. Qed.
Lemma D_3b398 : decode_any W_3b398 = Some (Load SZ8 true 18 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b39c : bv 32 := 0x08813983.
Lemma F_3b39c : fetch_word Ubsan.M.loaded_segments (0x3b39c : word) = Some W_3b39c.
Proof. vm_refl. Qed.
Lemma D_3b39c : decode_any W_3b39c = Some (Load SZ8 true 19 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b3a0 : bv 32 := 0x08013a03.
Lemma F_3b3a0 : fetch_word Ubsan.M.loaded_segments (0x3b3a0 : word) = Some W_3b3a0.
Proof. vm_refl. Qed.
Lemma D_3b3a0 : decode_any W_3b3a0 = Some (Load SZ8 true 20 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b3a4 : bv 32 := 0x07813a83.
Lemma F_3b3a4 : fetch_word Ubsan.M.loaded_segments (0x3b3a4 : word) = Some W_3b3a4.
Proof. vm_refl. Qed.
Lemma D_3b3a4 : decode_any W_3b3a4 = Some (Load SZ8 true 21 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b3a8 : bv 32 := 0x07013b03.
Lemma F_3b3a8 : fetch_word Ubsan.M.loaded_segments (0x3b3a8 : word) = Some W_3b3a8.
Proof. vm_refl. Qed.
Lemma D_3b3a8 : decode_any W_3b3a8 = Some (Load SZ8 true 22 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b3ac : bv 32 := 0x06813b83.
Lemma F_3b3ac : fetch_word Ubsan.M.loaded_segments (0x3b3ac : word) = Some W_3b3ac.
Proof. vm_refl. Qed.
Lemma D_3b3ac : decode_any W_3b3ac = Some (Load SZ8 true 23 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b3b0 : bv 32 := 0x06013c03.
Lemma F_3b3b0 : fetch_word Ubsan.M.loaded_segments (0x3b3b0 : word) = Some W_3b3b0.
Proof. vm_refl. Qed.
Lemma D_3b3b0 : decode_any W_3b3b0 = Some (Load SZ8 true 24 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b3b4 : bv 32 := 0x05813c83.
Lemma F_3b3b4 : fetch_word Ubsan.M.loaded_segments (0x3b3b4 : word) = Some W_3b3b4.
Proof. vm_refl. Qed.
Lemma D_3b3b4 : decode_any W_3b3b4 = Some (Load SZ8 true 25 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b3b8 : bv 32 := 0x05013d03.
Lemma F_3b3b8 : fetch_word Ubsan.M.loaded_segments (0x3b3b8 : word) = Some W_3b3b8.
Proof. vm_refl. Qed.
Lemma D_3b3b8 : decode_any W_3b3b8 = Some (Load SZ8 true 26 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b3bc : bv 32 := 0x04813d83.
Lemma F_3b3bc : fetch_word Ubsan.M.loaded_segments (0x3b3bc : word) = Some W_3b3bc.
Proof. vm_refl. Qed.
Lemma D_3b3bc : decode_any W_3b3bc = Some (Load SZ8 true 27 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b3c0 : bv 32 := 0x0b010113.
Lemma F_3b3c0 : fetch_word Ubsan.M.loaded_segments (0x3b3c0 : word) = Some W_3b3c0.
Proof. vm_refl. Qed.
Lemma D_3b3c0 : decode_any W_3b3c0 = Some (OpImm ALU_ADD 2 2 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b3c4 : bv 32 := 0x00008067.
Lemma F_3b3c4 : fetch_word Ubsan.M.loaded_segments (0x3b3c4 : word) = Some W_3b3c4.
Proof. vm_refl. Qed.
Lemma D_3b3c4 : decode_any W_3b3c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b3c8 : bv 32 := 0xc0001073.
Lemma F_3b3c8 : fetch_word Ubsan.M.loaded_segments (0x3b3c8 : word) = Some W_3b3c8.
Proof. vm_refl. Qed.
Lemma D_3b3c8 : decode_any W_3b3c8 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b3cc : bv 32 := 0x02010513.
Lemma F_3b3cc : fetch_word Ubsan.M.loaded_segments (0x3b3cc : word) = Some W_3b3cc.
Proof. vm_refl. Qed.
Lemma D_3b3cc : decode_any W_3b3cc = Some (OpImm ALU_ADD 10 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b3d0 : bv 32 := 0x9a0fd0ef.
Lemma F_3b3d0 : fetch_word Ubsan.M.loaded_segments (0x3b3d0 : word) = Some W_3b3d0.
Proof. vm_refl. Qed.
Lemma D_3b3d0 : decode_any W_3b3d0 = Some (Jal 1 2085280, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b3d4 : bv 32 := 0x01810513.
Lemma F_3b3d4 : fetch_word Ubsan.M.loaded_segments (0x3b3d4 : word) = Some W_3b3d4.
Proof. vm_refl. Qed.
Lemma D_3b3d4 : decode_any W_3b3d4 = Some (OpImm ALU_ADD 10 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b3d8 : bv 32 := 0xc54de0ef.
Lemma F_3b3d8 : fetch_word Ubsan.M.loaded_segments (0x3b3d8 : word) = Some W_3b3d8.
Proof. vm_refl. Qed.
Lemma D_3b3d8 : decode_any W_3b3d8 = Some (Jal 1 1958996, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b3dc : bv 32 := 0x00813503.
Lemma F_3b3dc : fetch_word Ubsan.M.loaded_segments (0x3b3dc : word) = Some W_3b3dc.
Proof. vm_refl. Qed.
Lemma D_3b3dc : decode_any W_3b3dc = Some (Load SZ8 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b3e0 : bv 32 := 0xfadff06f.
Lemma F_3b3e0 : fetch_word Ubsan.M.loaded_segments (0x3b3e0 : word) = Some W_3b3e0.
Proof. vm_refl. Qed.
Lemma D_3b3e0 : decode_any W_3b3e0 = Some (Jal 0 2097068, 4%Z).
Proof. vm_refl. Qed.

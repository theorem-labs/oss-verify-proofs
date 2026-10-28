(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_18d08 : bv 32 := 0xfb010113.
Lemma F_18d08 : fetch_word Ubsan.M.loaded_segments (0x18d08 : word) = Some W_18d08.
Proof. vm_refl. Qed.
Lemma D_18d08 : decode_any W_18d08 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d0c : bv 32 := 0x04113423.
Lemma F_18d0c : fetch_word Ubsan.M.loaded_segments (0x18d0c : word) = Some W_18d0c.
Proof. vm_refl. Qed.
Lemma D_18d0c : decode_any W_18d0c = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d10 : bv 32 := 0x04813023.
Lemma F_18d10 : fetch_word Ubsan.M.loaded_segments (0x18d10 : word) = Some W_18d10.
Proof. vm_refl. Qed.
Lemma D_18d10 : decode_any W_18d10 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d14 : bv 32 := 0x02913c23.
Lemma F_18d14 : fetch_word Ubsan.M.loaded_segments (0x18d14 : word) = Some W_18d14.
Proof. vm_refl. Qed.
Lemma D_18d14 : decode_any W_18d14 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d18 : bv 32 := 0x03213823.
Lemma F_18d18 : fetch_word Ubsan.M.loaded_segments (0x18d18 : word) = Some W_18d18.
Proof. vm_refl. Qed.
Lemma D_18d18 : decode_any W_18d18 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d1c : bv 32 := 0x03313423.
Lemma F_18d1c : fetch_word Ubsan.M.loaded_segments (0x18d1c : word) = Some W_18d1c.
Proof. vm_refl. Qed.
Lemma D_18d1c : decode_any W_18d1c = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d20 : bv 32 := 0x03413023.
Lemma F_18d20 : fetch_word Ubsan.M.loaded_segments (0x18d20 : word) = Some W_18d20.
Proof. vm_refl. Qed.
Lemma D_18d20 : decode_any W_18d20 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d24 : bv 32 := 0x01513c23.
Lemma F_18d24 : fetch_word Ubsan.M.loaded_segments (0x18d24 : word) = Some W_18d24.
Proof. vm_refl. Qed.
Lemma D_18d24 : decode_any W_18d24 = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d28 : bv 32 := 0x01613823.
Lemma F_18d28 : fetch_word Ubsan.M.loaded_segments (0x18d28 : word) = Some W_18d28.
Proof. vm_refl. Qed.
Lemma D_18d28 : decode_any W_18d28 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d2c : bv 32 := 0x00058493.
Lemma F_18d2c : fetch_word Ubsan.M.loaded_segments (0x18d2c : word) = Some W_18d2c.
Proof. vm_refl. Qed.
Lemma D_18d2c : decode_any W_18d2c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d30 : bv 32 := 0x00050413.
Lemma F_18d30 : fetch_word Ubsan.M.loaded_segments (0x18d30 : word) = Some W_18d30.
Proof. vm_refl. Qed.
Lemma D_18d30 : decode_any W_18d30 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d34 : bv 32 := 0x00058863.
Lemma F_18d34 : fetch_word Ubsan.M.loaded_segments (0x18d34 : word) = Some W_18d34.
Proof. vm_refl. Qed.
Lemma D_18d34 : decode_any W_18d34 = Some (Branch BC_EQ 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d38 : bv 32 := 0x0034f513.
Lemma F_18d38 : fetch_word Ubsan.M.loaded_segments (0x18d38 : word) = Some W_18d38.
Proof. vm_refl. Qed.
Lemma D_18d38 : decode_any W_18d38 = Some (OpImm ALU_AND 10 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d3c : bv 32 := 0x18051663.
Lemma F_18d3c : fetch_word Ubsan.M.loaded_segments (0x18d3c : word) = Some W_18d3c.
Proof. vm_refl. Qed.
Lemma D_18d3c : decode_any W_18d3c = Some (Branch BC_NE 10 0 396, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d40 : bv 32 := 0x0004a023.
Lemma F_18d40 : fetch_word Ubsan.M.loaded_segments (0x18d40 : word) = Some W_18d40.
Proof. vm_refl. Qed.
Lemma D_18d40 : decode_any W_18d40 = Some (Store SZ4 9 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d44 : bv 32 := 0x0a040463.
Lemma F_18d44 : fetch_word Ubsan.M.loaded_segments (0x18d44 : word) = Some W_18d44.
Proof. vm_refl. Qed.
Lemma D_18d44 : decode_any W_18d44 = Some (Branch BC_EQ 8 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d48 : bv 32 := 0x00c10593.
Lemma F_18d48 : fetch_word Ubsan.M.loaded_segments (0x18d48 : word) = Some W_18d48.
Proof. vm_refl. Qed.
Lemma D_18d48 : decode_any W_18d48 = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d4c : bv 32 := 0x00040513.
Lemma F_18d4c : fetch_word Ubsan.M.loaded_segments (0x18d4c : word) = Some W_18d4c.
Proof. vm_refl. Qed.
Lemma D_18d4c : decode_any W_18d4c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d50 : bv 32 := 0x00000613.
Lemma F_18d50 : fetch_word Ubsan.M.loaded_segments (0x18d50 : word) = Some W_18d50.
Proof. vm_refl. Qed.
Lemma D_18d50 : decode_any W_18d50 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d54 : bv 32 := 0xdc5ff0ef.
Lemma F_18d54 : fetch_word Ubsan.M.loaded_segments (0x18d54 : word) = Some W_18d54.
Proof. vm_refl. Qed.
Lemma D_18d54 : decode_any W_18d54 = Some (Jal 1 2096580, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d58 : bv 32 := 0x00c12503.
Lemma F_18d58 : fetch_word Ubsan.M.loaded_segments (0x18d58 : word) = Some W_18d58.
Proof. vm_refl. Qed.
Lemma D_18d58 : decode_any W_18d58 = Some (Load SZ4 true 10 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d5c : bv 32 := 0x0e050063.
Lemma F_18d5c : fetch_word Ubsan.M.loaded_segments (0x18d5c : word) = Some W_18d5c.
Proof. vm_refl. Qed.
Lemma D_18d5c : decode_any W_18d5c = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d60 : bv 32 := 0x00747513.
Lemma F_18d60 : fetch_word Ubsan.M.loaded_segments (0x18d60 : word) = Some W_18d60.
Proof. vm_refl. Qed.
Lemma D_18d60 : decode_any W_18d60 = Some (OpImm ALU_AND 10 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d64 : bv 32 := 0x16051263.
Lemma F_18d64 : fetch_word Ubsan.M.loaded_segments (0x18d64 : word) = Some W_18d64.
Proof. vm_refl. Qed.
Lemma D_18d64 : decode_any W_18d64 = Some (Branch BC_NE 10 0 356, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d68 : bv 32 := 0x00042983.
Lemma F_18d68 : fetch_word Ubsan.M.loaded_segments (0x18d68 : word) = Some W_18d68.
Proof. vm_refl. Qed.
Lemma D_18d68 : decode_any W_18d68 = Some (Load SZ4 true 19 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d6c : bv 32 := 0x00048863.
Lemma F_18d6c : fetch_word Ubsan.M.loaded_segments (0x18d6c : word) = Some W_18d6c.
Proof. vm_refl. Qed.
Lemma D_18d6c : decode_any W_18d6c = Some (Branch BC_EQ 9 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d70 : bv 32 := 0x0034f513.
Lemma F_18d70 : fetch_word Ubsan.M.loaded_segments (0x18d70 : word) = Some W_18d70.
Proof. vm_refl. Qed.
Lemma D_18d70 : decode_any W_18d70 = Some (OpImm ALU_AND 10 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d74 : bv 32 := 0x14051a63.
Lemma F_18d74 : fetch_word Ubsan.M.loaded_segments (0x18d74 : word) = Some W_18d74.
Proof. vm_refl. Qed.
Lemma D_18d74 : decode_any W_18d74 = Some (Branch BC_NE 10 0 340, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d78 : bv 32 := 0x0134a023.
Lemma F_18d78 : fetch_word Ubsan.M.loaded_segments (0x18d78 : word) = Some W_18d78.
Proof. vm_refl. Qed.
Lemma D_18d78 : decode_any W_18d78 = Some (Store SZ4 9 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d7c : bv 32 := 0x00800593.
Lemma F_18d7c : fetch_word Ubsan.M.loaded_segments (0x18d7c : word) = Some W_18d7c.
Proof. vm_refl. Qed.
Lemma D_18d7c : decode_any W_18d7c = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d80 : bv 32 := 0x00098513.
Lemma F_18d80 : fetch_word Ubsan.M.loaded_segments (0x18d80 : word) = Some W_18d80.
Proof. vm_refl. Qed.
Lemma D_18d80 : decode_any W_18d80 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d84 : bv 32 := 0x374230ef.
Lemma F_18d84 : fetch_word Ubsan.M.loaded_segments (0x18d84 : word) = Some W_18d84.
Proof. vm_refl. Qed.
Lemma D_18d84 : decode_any W_18d84 = Some (Jal 1 144244, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d88 : bv 32 := 0x0c050e63.
Lemma F_18d88 : fetch_word Ubsan.M.loaded_segments (0x18d88 : word) = Some W_18d88.
Proof. vm_refl. Qed.
Lemma D_18d88 : decode_any W_18d88 = Some (Branch BC_EQ 10 0 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d8c : bv 32 := 0x00050493.
Lemma F_18d8c : fetch_word Ubsan.M.loaded_segments (0x18d8c : word) = Some W_18d8c.
Proof. vm_refl. Qed.
Lemma D_18d8c : decode_any W_18d8c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d90 : bv 32 := 0x11305663.
Lemma F_18d90 : fetch_word Ubsan.M.loaded_segments (0x18d90 : word) = Some W_18d90.
Proof. vm_refl. Qed.
Lemma D_18d90 : decode_any W_18d90 = Some (Branch BC_GE 0 19 268, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d94 : bv 32 := 0x00000a13.
Lemma F_18d94 : fetch_word Ubsan.M.loaded_segments (0x18d94 : word) = Some W_18d94.
Proof. vm_refl. Qed.
Lemma D_18d94 : decode_any W_18d94 = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d98 : bv 32 := 0x00000913.
Lemma F_18d98 : fetch_word Ubsan.M.loaded_segments (0x18d98 : word) = Some W_18d98.
Proof. vm_refl. Qed.
Lemma D_18d98 : decode_any W_18d98 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d9c : bv 32 := 0xfff4ca93.
Lemma F_18d9c : fetch_word Ubsan.M.loaded_segments (0x18d9c : word) = Some W_18d9c.
Proof. vm_refl. Qed.
Lemma D_18d9c : decode_any W_18d9c = Some (OpImm ALU_XOR 21 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_18da0 : bv 32 := 0x0074fb13.
Lemma F_18da0 : fetch_word Ubsan.M.loaded_segments (0x18da0 : word) = Some W_18da0.
Proof. vm_refl. Qed.
Lemma D_18da0 : decode_any W_18da0 = Some (OpImm ALU_AND 22 9 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_18da4 : bv 32 := 0x00399993.
Lemma F_18da4 : fetch_word Ubsan.M.loaded_segments (0x18da4 : word) = Some W_18da4.
Proof. vm_refl. Qed.
Lemma D_18da4 : decode_any W_18da4 = Some (ShiftImm ALU_SLL 19 19 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_18da8 : bv 32 := 0x00200613.
Lemma F_18da8 : fetch_word Ubsan.M.loaded_segments (0x18da8 : word) = Some W_18da8.
Proof. vm_refl. Qed.
Lemma D_18da8 : decode_any W_18da8 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_18dac : bv 32 := 0x00040513.
Lemma F_18dac : fetch_word Ubsan.M.loaded_segments (0x18dac : word) = Some W_18dac.
Proof. vm_refl. Qed.
Lemma D_18dac : decode_any W_18dac = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18db0 : bv 32 := 0x00090593.
Lemma F_18db0 : fetch_word Ubsan.M.loaded_segments (0x18db0 : word) = Some W_18db0.
Proof. vm_refl. Qed.
Lemma D_18db0 : decode_any W_18db0 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18db4 : bv 32 := 0x8c5ff0ef.
Lemma F_18db4 : fetch_word Ubsan.M.loaded_segments (0x18db4 : word) = Some W_18db4.
Proof. vm_refl. Qed.
Lemma D_18db4 : decode_any W_18db4 = Some (Jal 1 2095300, 4%Z).
Proof. vm_refl. Qed.

Definition W_18db8 : bv 32 := 0x00a13023.
Lemma F_18db8 : fetch_word Ubsan.M.loaded_segments (0x18db8 : word) = Some W_18db8.
Proof. vm_refl. Qed.
Lemma D_18db8 : decode_any W_18db8 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18dbc : bv 32 := 0x00000593.
Lemma F_18dbc : fetch_word Ubsan.M.loaded_segments (0x18dbc : word) = Some W_18dbc.
Proof. vm_refl. Qed.
Lemma D_18dbc : decode_any W_18dbc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18dc0 : bv 32 := 0x621010ef.
Lemma F_18dc0 : fetch_word Ubsan.M.loaded_segments (0x18dc0 : word) = Some W_18dc0.
Proof. vm_refl. Qed.
Lemma D_18dc0 : decode_any W_18dc0 = Some (Jal 1 7712, 4%Z).
Proof. vm_refl. Qed.

Definition W_18dc4 : bv 32 := 0x114ae263.
Lemma F_18dc4 : fetch_word Ubsan.M.loaded_segments (0x18dc4 : word) = Some W_18dc4.
Proof. vm_refl. Qed.
Lemma D_18dc4 : decode_any W_18dc4 = Some (Branch BC_LTU 21 20 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_18dc8 : bv 32 := 0x100b1063.
Lemma F_18dc8 : fetch_word Ubsan.M.loaded_segments (0x18dc8 : word) = Some W_18dc8.
Proof. vm_refl. Qed.
Lemma D_18dc8 : decode_any W_18dc8 = Some (Branch BC_NE 22 0 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_18dcc : bv 32 := 0x014485b3.
Lemma F_18dcc : fetch_word Ubsan.M.loaded_segments (0x18dcc : word) = Some W_18dcc.
Proof. vm_refl. Qed.
Lemma D_18dcc : decode_any W_18dcc = Some (Op ALU_ADD 11 9 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_18dd0 : bv 32 := 0x00a5b023.
Lemma F_18dd0 : fetch_word Ubsan.M.loaded_segments (0x18dd0 : word) = Some W_18dd0.
Proof. vm_refl. Qed.
Lemma D_18dd0 : decode_any W_18dd0 = Some (Store SZ8 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18dd4 : bv 32 := 0x00010513.
Lemma F_18dd4 : fetch_word Ubsan.M.loaded_segments (0x18dd4 : word) = Some W_18dd4.
Proof. vm_refl. Qed.
Lemma D_18dd4 : decode_any W_18dd4 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18dd8 : bv 32 := 0x255000ef.
Lemma F_18dd8 : fetch_word Ubsan.M.loaded_segments (0x18dd8 : word) = Some W_18dd8.
Proof. vm_refl. Qed.
Lemma D_18dd8 : decode_any W_18dd8 = Some (Jal 1 2644, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ddc : bv 32 := 0x008a0a13.
Lemma F_18ddc : fetch_word Ubsan.M.loaded_segments (0x18ddc : word) = Some W_18ddc.
Proof. vm_refl. Qed.
Lemma D_18ddc : decode_any W_18ddc = Some (OpImm ALU_ADD 20 20 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18de0 : bv 32 := 0x0019091b.
Lemma F_18de0 : fetch_word Ubsan.M.loaded_segments (0x18de0 : word) = Some W_18de0.
Proof. vm_refl. Qed.
Lemma D_18de0 : decode_any W_18de0 = Some (OpImm32 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_18de4 : bv 32 := 0xfd4992e3.
Lemma F_18de4 : fetch_word Ubsan.M.loaded_segments (0x18de4 : word) = Some W_18de4.
Proof. vm_refl. Qed.
Lemma D_18de4 : decode_any W_18de4 = Some (Branch BC_NE 19 20 8132, 4%Z).
Proof. vm_refl. Qed.

Definition W_18de8 : bv 32 := 0x0b40006f.
Lemma F_18de8 : fetch_word Ubsan.M.loaded_segments (0x18de8 : word) = Some W_18de8.
Proof. vm_refl. Qed.
Lemma D_18de8 : decode_any W_18de8 = Some (Jal 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_18dec : bv 32 := 0x0002c517.
Lemma F_18dec : fetch_word Ubsan.M.loaded_segments (0x18dec : word) = Some W_18dec.
Proof. vm_refl. Qed.
Lemma D_18dec : decode_any W_18dec = Some (Auipc 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_18df0 : bv 32 := 0x0ac53503.
Lemma F_18df0 : fetch_word Ubsan.M.loaded_segments (0x18df0 : word) = Some W_18df0.
Proof. vm_refl. Qed.
Lemma D_18df0 : decode_any W_18df0 = Some (Load SZ8 true 10 10 172, 4%Z).
Proof. vm_refl. Qed.

Definition W_18df4 : bv 32 := 0x00052503.
Lemma F_18df4 : fetch_word Ubsan.M.loaded_segments (0x18df4 : word) = Some W_18df4.
Proof. vm_refl. Qed.
Lemma D_18df4 : decode_any W_18df4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18df8 : bv 32 := 0x00500593.
Lemma F_18df8 : fetch_word Ubsan.M.loaded_segments (0x18df8 : word) = Some W_18df8.
Proof. vm_refl. Qed.
Lemma D_18df8 : decode_any W_18df8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_18dfc : bv 32 := 0x08a5ce63.
Lemma F_18dfc : fetch_word Ubsan.M.loaded_segments (0x18dfc : word) = Some W_18dfc.
Proof. vm_refl. Qed.
Lemma D_18dfc : decode_any W_18dfc = Some (Branch BC_LT 11 10 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e00 : bv 32 := 0xffff9517.
Lemma F_18e00 : fetch_word Ubsan.M.loaded_segments (0x18e00 : word) = Some W_18e00.
Proof. vm_refl. Qed.
Lemma D_18e00 : decode_any W_18e00 = Some (Auipc 10 1048569, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e04 : bv 32 := 0xffff8597.
Lemma F_18e04 : fetch_word Ubsan.M.loaded_segments (0x18e04 : word) = Some W_18e04.
Proof. vm_refl. Qed.
Lemma D_18e04 : decode_any W_18e04 = Some (Auipc 11 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e08 : bv 32 := 0x42750513.
Lemma F_18e08 : fetch_word Ubsan.M.loaded_segments (0x18e08 : word) = Some W_18e08.
Proof. vm_refl. Qed.
Lemma D_18e08 : decode_any W_18e08 = Some (OpImm ALU_ADD 10 10 1063, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e0c : bv 32 := 0x36058593.
Lemma F_18e0c : fetch_word Ubsan.M.loaded_segments (0x18e0c : word) = Some W_18e0c.
Proof. vm_refl. Qed.
Lemma D_18e0c : decode_any W_18e0c = Some (OpImm ALU_ADD 11 11 864, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e10 : bv 32 := 0x00000613.
Lemma F_18e10 : fetch_word Ubsan.M.loaded_segments (0x18e10 : word) = Some W_18e10.
Proof. vm_refl. Qed.
Lemma D_18e10 : decode_any W_18e10 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e14 : bv 32 := 0x04813083.
Lemma F_18e14 : fetch_word Ubsan.M.loaded_segments (0x18e14 : word) = Some W_18e14.
Proof. vm_refl. Qed.
Lemma D_18e14 : decode_any W_18e14 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e18 : bv 32 := 0x04013403.
Lemma F_18e18 : fetch_word Ubsan.M.loaded_segments (0x18e18 : word) = Some W_18e18.
Proof. vm_refl. Qed.
Lemma D_18e18 : decode_any W_18e18 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e1c : bv 32 := 0x03813483.
Lemma F_18e1c : fetch_word Ubsan.M.loaded_segments (0x18e1c : word) = Some W_18e1c.
Proof. vm_refl. Qed.
Lemma D_18e1c : decode_any W_18e1c = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e20 : bv 32 := 0x03013903.
Lemma F_18e20 : fetch_word Ubsan.M.loaded_segments (0x18e20 : word) = Some W_18e20.
Proof. vm_refl. Qed.
Lemma D_18e20 : decode_any W_18e20 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e24 : bv 32 := 0x02813983.
Lemma F_18e24 : fetch_word Ubsan.M.loaded_segments (0x18e24 : word) = Some W_18e24.
Proof. vm_refl. Qed.
Lemma D_18e24 : decode_any W_18e24 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e28 : bv 32 := 0x02013a03.
Lemma F_18e28 : fetch_word Ubsan.M.loaded_segments (0x18e28 : word) = Some W_18e28.
Proof. vm_refl. Qed.
Lemma D_18e28 : decode_any W_18e28 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e2c : bv 32 := 0x01813a83.
Lemma F_18e2c : fetch_word Ubsan.M.loaded_segments (0x18e2c : word) = Some W_18e2c.
Proof. vm_refl. Qed.
Lemma D_18e2c : decode_any W_18e2c = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e30 : bv 32 := 0x01013b03.
Lemma F_18e30 : fetch_word Ubsan.M.loaded_segments (0x18e30 : word) = Some W_18e30.
Proof. vm_refl. Qed.
Lemma D_18e30 : decode_any W_18e30 = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e34 : bv 32 := 0x05010113.
Lemma F_18e34 : fetch_word Ubsan.M.loaded_segments (0x18e34 : word) = Some W_18e34.
Proof. vm_refl. Qed.
Lemma D_18e34 : decode_any W_18e34 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e38 : bv 32 := 0x88cff06f.
Lemma F_18e38 : fetch_word Ubsan.M.loaded_segments (0x18e38 : word) = Some W_18e38.
Proof. vm_refl. Qed.
Lemma D_18e38 : decode_any W_18e38 = Some (Jal 0 2093196, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e3c : bv 32 := 0x0002c517.
Lemma F_18e3c : fetch_word Ubsan.M.loaded_segments (0x18e3c : word) = Some W_18e3c.
Proof. vm_refl. Qed.
Lemma D_18e3c : decode_any W_18e3c = Some (Auipc 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e40 : bv 32 := 0x05c53503.
Lemma F_18e40 : fetch_word Ubsan.M.loaded_segments (0x18e40 : word) = Some W_18e40.
Proof. vm_refl. Qed.
Lemma D_18e40 : decode_any W_18e40 = Some (Load SZ8 true 10 10 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e44 : bv 32 := 0x00052503.
Lemma F_18e44 : fetch_word Ubsan.M.loaded_segments (0x18e44 : word) = Some W_18e44.
Proof. vm_refl. Qed.
Lemma D_18e44 : decode_any W_18e44 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e48 : bv 32 := 0x00500593.
Lemma F_18e48 : fetch_word Ubsan.M.loaded_segments (0x18e48 : word) = Some W_18e48.
Proof. vm_refl. Qed.
Lemma D_18e48 : decode_any W_18e48 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e4c : bv 32 := 0x04a5c663.
Lemma F_18e4c : fetch_word Ubsan.M.loaded_segments (0x18e4c : word) = Some W_18e4c.
Proof. vm_refl. Qed.
Lemma D_18e4c : decode_any W_18e4c = Some (Branch BC_LT 11 10 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e50 : bv 32 := 0xffff9517.
Lemma F_18e50 : fetch_word Ubsan.M.loaded_segments (0x18e50 : word) = Some W_18e50.
Proof. vm_refl. Qed.
Lemma D_18e50 : decode_any W_18e50 = Some (Auipc 10 1048569, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e54 : bv 32 := 0xffff8597.
Lemma F_18e54 : fetch_word Ubsan.M.loaded_segments (0x18e54 : word) = Some W_18e54.
Proof. vm_refl. Qed.
Lemma D_18e54 : decode_any W_18e54 = Some (Auipc 11 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e58 : bv 32 := 0x89e50513.
Lemma F_18e58 : fetch_word Ubsan.M.loaded_segments (0x18e58 : word) = Some W_18e58.
Proof. vm_refl. Qed.
Lemma D_18e58 : decode_any W_18e58 = Some (OpImm ALU_ADD 10 10 2206, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e5c : bv 32 := 0x31058593.
Lemma F_18e5c : fetch_word Ubsan.M.loaded_segments (0x18e5c : word) = Some W_18e5c.
Proof. vm_refl. Qed.
Lemma D_18e5c : decode_any W_18e5c = Some (OpImm ALU_ADD 11 11 784, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e60 : bv 32 := 0x0280006f.
Lemma F_18e60 : fetch_word Ubsan.M.loaded_segments (0x18e60 : word) = Some W_18e60.
Proof. vm_refl. Qed.
Lemma D_18e60 : decode_any W_18e60 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e64 : bv 32 := 0x0002c517.
Lemma F_18e64 : fetch_word Ubsan.M.loaded_segments (0x18e64 : word) = Some W_18e64.
Proof. vm_refl. Qed.
Lemma D_18e64 : decode_any W_18e64 = Some (Auipc 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e68 : bv 32 := 0x03453503.
Lemma F_18e68 : fetch_word Ubsan.M.loaded_segments (0x18e68 : word) = Some W_18e68.
Proof. vm_refl. Qed.
Lemma D_18e68 : decode_any W_18e68 = Some (Load SZ8 true 10 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e6c : bv 32 := 0x00052503.
Lemma F_18e6c : fetch_word Ubsan.M.loaded_segments (0x18e6c : word) = Some W_18e6c.
Proof. vm_refl. Qed.
Lemma D_18e6c : decode_any W_18e6c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e70 : bv 32 := 0x00500593.
Lemma F_18e70 : fetch_word Ubsan.M.loaded_segments (0x18e70 : word) = Some W_18e70.
Proof. vm_refl. Qed.
Lemma D_18e70 : decode_any W_18e70 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e74 : bv 32 := 0x02a5c263.
Lemma F_18e74 : fetch_word Ubsan.M.loaded_segments (0x18e74 : word) = Some W_18e74.
Proof. vm_refl. Qed.
Lemma D_18e74 : decode_any W_18e74 = Some (Branch BC_LT 11 10 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e78 : bv 32 := 0xffff8517.
Lemma F_18e78 : fetch_word Ubsan.M.loaded_segments (0x18e78 : word) = Some W_18e78.
Proof. vm_refl. Qed.
Lemma D_18e78 : decode_any W_18e78 = Some (Auipc 10 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e7c : bv 32 := 0xffff8597.
Lemma F_18e7c : fetch_word Ubsan.M.loaded_segments (0x18e7c : word) = Some W_18e7c.
Proof. vm_refl. Qed.
Lemma D_18e7c : decode_any W_18e7c = Some (Auipc 11 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e80 : bv 32 := 0x8dc50513.
Lemma F_18e80 : fetch_word Ubsan.M.loaded_segments (0x18e80 : word) = Some W_18e80.
Proof. vm_refl. Qed.
Lemma D_18e80 : decode_any W_18e80 = Some (OpImm ALU_ADD 10 10 2268, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e84 : bv 32 := 0x2e858593.
Lemma F_18e84 : fetch_word Ubsan.M.loaded_segments (0x18e84 : word) = Some W_18e84.
Proof. vm_refl. Qed.
Lemma D_18e84 : decode_any W_18e84 = Some (OpImm ALU_ADD 11 11 744, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e88 : bv 32 := 0x00000613.
Lemma F_18e88 : fetch_word Ubsan.M.loaded_segments (0x18e88 : word) = Some W_18e88.
Proof. vm_refl. Qed.
Lemma D_18e88 : decode_any W_18e88 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e8c : bv 32 := 0x838ff0ef.
Lemma F_18e8c : fetch_word Ubsan.M.loaded_segments (0x18e8c : word) = Some W_18e8c.
Proof. vm_refl. Qed.
Lemma D_18e8c : decode_any W_18e8c = Some (Jal 1 2093112, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e90 : bv 32 := 0x00050493.
Lemma F_18e90 : fetch_word Ubsan.M.loaded_segments (0x18e90 : word) = Some W_18e90.
Proof. vm_refl. Qed.
Lemma D_18e90 : decode_any W_18e90 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e94 : bv 32 := 0x0080006f.
Lemma F_18e94 : fetch_word Ubsan.M.loaded_segments (0x18e94 : word) = Some W_18e94.
Proof. vm_refl. Qed.
Lemma D_18e94 : decode_any W_18e94 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e98 : bv 32 := 0x00000493.
Lemma F_18e98 : fetch_word Ubsan.M.loaded_segments (0x18e98 : word) = Some W_18e98.
Proof. vm_refl. Qed.
Lemma D_18e98 : decode_any W_18e98 = Some (OpImm ALU_ADD 9 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e9c : bv 32 := 0x00048513.
Lemma F_18e9c : fetch_word Ubsan.M.loaded_segments (0x18e9c : word) = Some W_18e9c.
Proof. vm_refl. Qed.
Lemma D_18e9c : decode_any W_18e9c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ea0 : bv 32 := 0x04813083.
Lemma F_18ea0 : fetch_word Ubsan.M.loaded_segments (0x18ea0 : word) = Some W_18ea0.
Proof. vm_refl. Qed.
Lemma D_18ea0 : decode_any W_18ea0 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ea4 : bv 32 := 0x04013403.
Lemma F_18ea4 : fetch_word Ubsan.M.loaded_segments (0x18ea4 : word) = Some W_18ea4.
Proof. vm_refl. Qed.
Lemma D_18ea4 : decode_any W_18ea4 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ea8 : bv 32 := 0x03813483.
Lemma F_18ea8 : fetch_word Ubsan.M.loaded_segments (0x18ea8 : word) = Some W_18ea8.
Proof. vm_refl. Qed.
Lemma D_18ea8 : decode_any W_18ea8 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_18eac : bv 32 := 0x03013903.
Lemma F_18eac : fetch_word Ubsan.M.loaded_segments (0x18eac : word) = Some W_18eac.
Proof. vm_refl. Qed.
Lemma D_18eac : decode_any W_18eac = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_18eb0 : bv 32 := 0x02813983.
Lemma F_18eb0 : fetch_word Ubsan.M.loaded_segments (0x18eb0 : word) = Some W_18eb0.
Proof. vm_refl. Qed.
Lemma D_18eb0 : decode_any W_18eb0 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_18eb4 : bv 32 := 0x02013a03.
Lemma F_18eb4 : fetch_word Ubsan.M.loaded_segments (0x18eb4 : word) = Some W_18eb4.
Proof. vm_refl. Qed.
Lemma D_18eb4 : decode_any W_18eb4 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18eb8 : bv 32 := 0x01813a83.
Lemma F_18eb8 : fetch_word Ubsan.M.loaded_segments (0x18eb8 : word) = Some W_18eb8.
Proof. vm_refl. Qed.
Lemma D_18eb8 : decode_any W_18eb8 = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ebc : bv 32 := 0x01013b03.
Lemma F_18ebc : fetch_word Ubsan.M.loaded_segments (0x18ebc : word) = Some W_18ebc.
Proof. vm_refl. Qed.
Lemma D_18ebc : decode_any W_18ebc = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ec0 : bv 32 := 0x05010113.
Lemma F_18ec0 : fetch_word Ubsan.M.loaded_segments (0x18ec0 : word) = Some W_18ec0.
Proof. vm_refl. Qed.
Lemma D_18ec0 : decode_any W_18ec0 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ec4 : bv 32 := 0x00008067.
Lemma F_18ec4 : fetch_word Ubsan.M.loaded_segments (0x18ec4 : word) = Some W_18ec4.
Proof. vm_refl. Qed.
Lemma D_18ec4 : decode_any W_18ec4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ec8 : bv 32 := 0xc0001073.
Lemma F_18ec8 : fetch_word Ubsan.M.loaded_segments (0x18ec8 : word) = Some W_18ec8.
Proof. vm_refl. Qed.
Lemma D_18ec8 : decode_any W_18ec8 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.

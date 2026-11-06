(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_5fed4 : bv 32 := 0x0100006f.
Lemma F_5fed4 : fetch_word AsanUbsan.M.loaded_segments (0x5fed4 : word) = Some W_5fed4.
Proof. vm_refl. Qed.
Lemma D_5fed4 : decode_any W_5fed4 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fed8 : bv 32 := 0x1dc0006f.
Lemma F_5fed8 : fetch_word AsanUbsan.M.loaded_segments (0x5fed8 : word) = Some W_5fed8.
Proof. vm_refl. Qed.
Lemma D_5fed8 : decode_any W_5fed8 = Some (Jal 0 476, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fedc : bv 32 := 0x4000006f.
Lemma F_5fedc : fetch_word AsanUbsan.M.loaded_segments (0x5fedc : word) = Some W_5fedc.
Proof. vm_refl. Qed.
Lemma D_5fedc : decode_any W_5fedc = Some (Jal 0 1024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fee0 : bv 32 := 0x7400006f.
Lemma F_5fee0 : fetch_word AsanUbsan.M.loaded_segments (0x5fee0 : word) = Some W_5fee0.
Proof. vm_refl. Qed.
Lemma D_5fee0 : decode_any W_5fee0 = Some (Jal 0 1856, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fee4 : bv 32 := 0x81010113.
Lemma F_5fee4 : fetch_word AsanUbsan.M.loaded_segments (0x5fee4 : word) = Some W_5fee4.
Proof. vm_refl. Qed.
Lemma D_5fee4 : decode_any W_5fee4 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fee8 : bv 32 := 0x7e113423.
Lemma F_5fee8 : fetch_word AsanUbsan.M.loaded_segments (0x5fee8 : word) = Some W_5fee8.
Proof. vm_refl. Qed.
Lemma D_5fee8 : decode_any W_5fee8 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5feec : bv 32 := 0x7e813023.
Lemma F_5feec : fetch_word AsanUbsan.M.loaded_segments (0x5feec : word) = Some W_5feec.
Proof. vm_refl. Qed.
Lemma D_5feec : decode_any W_5feec = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fef0 : bv 32 := 0x7c913c23.
Lemma F_5fef0 : fetch_word AsanUbsan.M.loaded_segments (0x5fef0 : word) = Some W_5fef0.
Proof. vm_refl. Qed.
Lemma D_5fef0 : decode_any W_5fef0 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fef4 : bv 32 := 0x7d213823.
Lemma F_5fef4 : fetch_word AsanUbsan.M.loaded_segments (0x5fef4 : word) = Some W_5fef4.
Proof. vm_refl. Qed.
Lemma D_5fef4 : decode_any W_5fef4 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fef8 : bv 32 := 0x7d313423.
Lemma F_5fef8 : fetch_word AsanUbsan.M.loaded_segments (0x5fef8 : word) = Some W_5fef8.
Proof. vm_refl. Qed.
Lemma D_5fef8 : decode_any W_5fef8 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fefc : bv 32 := 0x7d413023.
Lemma F_5fefc : fetch_word AsanUbsan.M.loaded_segments (0x5fefc : word) = Some W_5fefc.
Proof. vm_refl. Qed.
Lemma D_5fefc : decode_any W_5fefc = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff00 : bv 32 := 0x7b513c23.
Lemma F_5ff00 : fetch_word AsanUbsan.M.loaded_segments (0x5ff00 : word) = Some W_5ff00.
Proof. vm_refl. Qed.
Lemma D_5ff00 : decode_any W_5ff00 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff04 : bv 32 := 0x7f010413.
Lemma F_5ff04 : fetch_word AsanUbsan.M.loaded_segments (0x5ff04 : word) = Some W_5ff04.
Proof. vm_refl. Qed.
Lemma D_5ff04 : decode_any W_5ff04 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff08 : bv 32 := 0xfa010113.
Lemma F_5ff08 : fetch_word AsanUbsan.M.loaded_segments (0x5ff08 : word) = Some W_5ff08.
Proof. vm_refl. Qed.
Lemma D_5ff08 : decode_any W_5ff08 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff0c : bv 32 := 0x00008913.
Lemma F_5ff0c : fetch_word AsanUbsan.M.loaded_segments (0x5ff0c : word) = Some W_5ff0c.
Proof. vm_refl. Qed.
Lemma D_5ff0c : decode_any W_5ff0c = Some (OpImm ALU_ADD 18 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff10 : bv 32 := 0x00050493.
Lemma F_5ff10 : fetch_word AsanUbsan.M.loaded_segments (0x5ff10 : word) = Some W_5ff10.
Proof. vm_refl. Qed.
Lemma D_5ff10 : decode_any W_5ff10 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff14 : bv 32 := 0x3cd0b0ef.
Lemma F_5ff14 : fetch_word AsanUbsan.M.loaded_segments (0x5ff14 : word) = Some W_5ff14.
Proof. vm_refl. Qed.
Lemma D_5ff14 : decode_any W_5ff14 = Some (Jal 1 48076, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff18 : bv 32 := 0x02f4d593.
Lemma F_5ff18 : fetch_word AsanUbsan.M.loaded_segments (0x5ff18 : word) = Some W_5ff18.
Proof. vm_refl. Qed.
Lemma D_5ff18 : decode_any W_5ff18 = Some (ShiftImm ALU_SRL 11 9 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff1c : bv 32 := 0x0a059063.
Lemma F_5ff1c : fetch_word AsanUbsan.M.loaded_segments (0x5ff1c : word) = Some W_5ff1c.
Proof. vm_refl. Qed.
Lemma D_5ff1c : decode_any W_5ff1c = Some (Branch BC_NE 11 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff20 : bv 32 := 0x0204d593.
Lemma F_5ff20 : fetch_word AsanUbsan.M.loaded_segments (0x5ff20 : word) = Some W_5ff20.
Proof. vm_refl. Qed.
Lemma D_5ff20 : decode_any W_5ff20 = Some (ShiftImm ALU_SRL 11 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff24 : bv 32 := 0x00359613.
Lemma F_5ff24 : fetch_word AsanUbsan.M.loaded_segments (0x5ff24 : word) = Some W_5ff24.
Proof. vm_refl. Qed.
Lemma D_5ff24 : decode_any W_5ff24 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff28 : bv 32 := 0x00c50633.
Lemma F_5ff28 : fetch_word AsanUbsan.M.loaded_segments (0x5ff28 : word) = Some W_5ff28.
Proof. vm_refl. Qed.
Lemma D_5ff28 : decode_any W_5ff28 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff2c : bv 32 := 0x00863683.
Lemma F_5ff2c : fetch_word AsanUbsan.M.loaded_segments (0x5ff2c : word) = Some W_5ff2c.
Proof. vm_refl. Qed.
Lemma D_5ff2c : decode_any W_5ff2c = Some (Load SZ8 true 13 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff30 : bv 32 := 0x0230000f.
Lemma F_5ff30 : fetch_word AsanUbsan.M.loaded_segments (0x5ff30 : word) = Some W_5ff30.
Proof. vm_refl. Qed.
Lemma D_5ff30 : decode_any W_5ff30 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff34 : bv 32 := 0x08068463.
Lemma F_5ff34 : fetch_word AsanUbsan.M.loaded_segments (0x5ff34 : word) = Some W_5ff34.
Proof. vm_refl. Qed.
Lemma D_5ff34 : decode_any W_5ff34 = Some (Branch BC_EQ 13 0 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff38 : bv 32 := 0x00863603.
Lemma F_5ff38 : fetch_word AsanUbsan.M.loaded_segments (0x5ff38 : word) = Some W_5ff38.
Proof. vm_refl. Qed.
Lemma D_5ff38 : decode_any W_5ff38 = Some (Load SZ8 true 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff3c : bv 32 := 0x0144d993.
Lemma F_5ff3c : fetch_word AsanUbsan.M.loaded_segments (0x5ff3c : word) = Some W_5ff3c.
Proof. vm_refl. Qed.
Lemma D_5ff3c : decode_any W_5ff3c = Some (ShiftImm ALU_SRL 19 9 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff40 : bv 32 := 0x06060063.
Lemma F_5ff40 : fetch_word AsanUbsan.M.loaded_segments (0x5ff40 : word) = Some W_5ff40.
Proof. vm_refl. Qed.
Lemma D_5ff40 : decode_any W_5ff40 = Some (Branch BC_EQ 12 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff44 : bv 32 := 0x03499993.
Lemma F_5ff44 : fetch_word AsanUbsan.M.loaded_segments (0x5ff44 : word) = Some W_5ff44.
Proof. vm_refl. Qed.
Lemma D_5ff44 : decode_any W_5ff44 = Some (ShiftImm ALU_SLL 19 19 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff48 : bv 32 := 0x0349d513.
Lemma F_5ff48 : fetch_word AsanUbsan.M.loaded_segments (0x5ff48 : word) = Some W_5ff48.
Proof. vm_refl. Qed.
Lemma D_5ff48 : decode_any W_5ff48 = Some (ShiftImm ALU_SRL 10 19 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff4c : bv 32 := 0x00a60533.
Lemma F_5ff4c : fetch_word AsanUbsan.M.loaded_segments (0x5ff4c : word) = Some W_5ff4c.
Proof. vm_refl. Qed.
Lemma D_5ff4c : decode_any W_5ff4c = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff50 : bv 32 := 0x00054503.
Lemma F_5ff50 : fetch_word AsanUbsan.M.loaded_segments (0x5ff50 : word) = Some W_5ff50.
Proof. vm_refl. Qed.
Lemma D_5ff50 : decode_any W_5ff50 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff54 : bv 32 := 0x06050463.
Lemma F_5ff54 : fetch_word AsanUbsan.M.loaded_segments (0x5ff54 : word) = Some W_5ff54.
Proof. vm_refl. Qed.
Lemma D_5ff54 : decode_any W_5ff54 = Some (Branch BC_EQ 10 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff58 : bv 32 := 0x3890b0ef.
Lemma F_5ff58 : fetch_word AsanUbsan.M.loaded_segments (0x5ff58 : word) = Some W_5ff58.
Proof. vm_refl. Qed.
Lemma D_5ff58 : decode_any W_5ff58 = Some (Jal 1 48008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff5c : bv 32 := 0x00048593.
Lemma F_5ff5c : fetch_word AsanUbsan.M.loaded_segments (0x5ff5c : word) = Some W_5ff5c.
Proof. vm_refl. Qed.
Lemma D_5ff5c : decode_any W_5ff5c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff60 : bv 32 := 0x0f9000ef.
Lemma F_5ff60 : fetch_word AsanUbsan.M.loaded_segments (0x5ff60 : word) = Some W_5ff60.
Proof. vm_refl. Qed.
Lemma D_5ff60 : decode_any W_5ff60 = Some (Jal 1 2296, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff64 : bv 32 := 0x00050593.
Lemma F_5ff64 : fetch_word AsanUbsan.M.loaded_segments (0x5ff64 : word) = Some W_5ff64.
Proof. vm_refl. Qed.
Lemma D_5ff64 : decode_any W_5ff64 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff68 : bv 32 := 0x00048513.
Lemma F_5ff68 : fetch_word AsanUbsan.M.loaded_segments (0x5ff68 : word) = Some W_5ff68.
Proof. vm_refl. Qed.
Lemma D_5ff68 : decode_any W_5ff68 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff6c : bv 32 := 0x6702a0ef.
Lemma F_5ff6c : fetch_word AsanUbsan.M.loaded_segments (0x5ff6c : word) = Some W_5ff6c.
Proof. vm_refl. Qed.
Lemma D_5ff6c : decode_any W_5ff6c = Some (Jal 1 173680, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff70 : bv 32 := 0x00048513.
Lemma F_5ff70 : fetch_word AsanUbsan.M.loaded_segments (0x5ff70 : word) = Some W_5ff70.
Proof. vm_refl. Qed.
Lemma D_5ff70 : decode_any W_5ff70 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff74 : bv 32 := 0x00000593.
Lemma F_5ff74 : fetch_word AsanUbsan.M.loaded_segments (0x5ff74 : word) = Some W_5ff74.
Proof. vm_refl. Qed.
Lemma D_5ff74 : decode_any W_5ff74 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff78 : bv 32 := 0x06010113.
Lemma F_5ff78 : fetch_word AsanUbsan.M.loaded_segments (0x5ff78 : word) = Some W_5ff78.
Proof. vm_refl. Qed.
Lemma D_5ff78 : decode_any W_5ff78 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff7c : bv 32 := 0x7e813083.
Lemma F_5ff7c : fetch_word AsanUbsan.M.loaded_segments (0x5ff7c : word) = Some W_5ff7c.
Proof. vm_refl. Qed.
Lemma D_5ff7c : decode_any W_5ff7c = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff80 : bv 32 := 0x7e013403.
Lemma F_5ff80 : fetch_word AsanUbsan.M.loaded_segments (0x5ff80 : word) = Some W_5ff80.
Proof. vm_refl. Qed.
Lemma D_5ff80 : decode_any W_5ff80 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff84 : bv 32 := 0x7d813483.
Lemma F_5ff84 : fetch_word AsanUbsan.M.loaded_segments (0x5ff84 : word) = Some W_5ff84.
Proof. vm_refl. Qed.
Lemma D_5ff84 : decode_any W_5ff84 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff88 : bv 32 := 0x7d013903.
Lemma F_5ff88 : fetch_word AsanUbsan.M.loaded_segments (0x5ff88 : word) = Some W_5ff88.
Proof. vm_refl. Qed.
Lemma D_5ff88 : decode_any W_5ff88 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff8c : bv 32 := 0x7c813983.
Lemma F_5ff8c : fetch_word AsanUbsan.M.loaded_segments (0x5ff8c : word) = Some W_5ff8c.
Proof. vm_refl. Qed.
Lemma D_5ff8c : decode_any W_5ff8c = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff90 : bv 32 := 0x7c013a03.
Lemma F_5ff90 : fetch_word AsanUbsan.M.loaded_segments (0x5ff90 : word) = Some W_5ff90.
Proof. vm_refl. Qed.
Lemma D_5ff90 : decode_any W_5ff90 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff94 : bv 32 := 0x7b813a83.
Lemma F_5ff94 : fetch_word AsanUbsan.M.loaded_segments (0x5ff94 : word) = Some W_5ff94.
Proof. vm_refl. Qed.
Lemma D_5ff94 : decode_any W_5ff94 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff98 : bv 32 := 0x7f010113.
Lemma F_5ff98 : fetch_word AsanUbsan.M.loaded_segments (0x5ff98 : word) = Some W_5ff98.
Proof. vm_refl. Qed.
Lemma D_5ff98 : decode_any W_5ff98 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff9c : bv 32 := 0x5c10b06f.
Lemma F_5ff9c : fetch_word AsanUbsan.M.loaded_segments (0x5ff9c : word) = Some W_5ff9c.
Proof. vm_refl. Qed.
Lemma D_5ff9c : decode_any W_5ff9c = Some (Jal 0 48576, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffa0 : bv 32 := 0x7b8000ef.
Lemma F_5ffa0 : fetch_word AsanUbsan.M.loaded_segments (0x5ffa0 : word) = Some W_5ffa0.
Proof. vm_refl. Qed.
Lemma D_5ffa0 : decode_any W_5ffa0 = Some (Jal 1 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffa4 : bv 32 := 0x00050613.
Lemma F_5ffa4 : fetch_word AsanUbsan.M.loaded_segments (0x5ffa4 : word) = Some W_5ffa4.
Proof. vm_refl. Qed.
Lemma D_5ffa4 : decode_any W_5ffa4 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffa8 : bv 32 := 0x03499993.
Lemma F_5ffa8 : fetch_word AsanUbsan.M.loaded_segments (0x5ffa8 : word) = Some W_5ffa8.
Proof. vm_refl. Qed.
Lemma D_5ffa8 : decode_any W_5ffa8 = Some (ShiftImm ALU_SLL 19 19 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffac : bv 32 := 0x0349d513.
Lemma F_5ffac : fetch_word AsanUbsan.M.loaded_segments (0x5ffac : word) = Some W_5ffac.
Proof. vm_refl. Qed.
Lemma D_5ffac : decode_any W_5ffac = Some (ShiftImm ALU_SRL 10 19 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffb0 : bv 32 := 0x00a60533.
Lemma F_5ffb0 : fetch_word AsanUbsan.M.loaded_segments (0x5ffb0 : word) = Some W_5ffb0.
Proof. vm_refl. Qed.
Lemma D_5ffb0 : decode_any W_5ffb0 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffb4 : bv 32 := 0x00054503.
Lemma F_5ffb4 : fetch_word AsanUbsan.M.loaded_segments (0x5ffb4 : word) = Some W_5ffb4.
Proof. vm_refl. Qed.
Lemma D_5ffb4 : decode_any W_5ffb4 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffb8 : bv 32 := 0xfa0510e3.
Lemma F_5ffb8 : fetch_word AsanUbsan.M.loaded_segments (0x5ffb8 : word) = Some W_5ffb8.
Proof. vm_refl. Qed.
Lemma D_5ffb8 : decode_any W_5ffb8 = Some (Branch BC_NE 10 0 8096, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffbc : bv 32 := 0x80040a13.
Lemma F_5ffbc : fetch_word AsanUbsan.M.loaded_segments (0x5ffbc : word) = Some W_5ffbc.
Proof. vm_refl. Qed.
Lemma D_5ffbc : decode_any W_5ffbc = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffc0 : bv 32 := 0xfb0a0a13.
Lemma F_5ffc0 : fetch_word AsanUbsan.M.loaded_segments (0x5ffc0 : word) = Some W_5ffc0.
Proof. vm_refl. Qed.
Lemma D_5ffc0 : decode_any W_5ffc0 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffc4 : bv 32 := 0x80040513.
Lemma F_5ffc4 : fetch_word AsanUbsan.M.loaded_segments (0x5ffc4 : word) = Some W_5ffc4.
Proof. vm_refl. Qed.
Lemma D_5ffc4 : decode_any W_5ffc4 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffc8 : bv 32 := 0xfc050513.
Lemma F_5ffc8 : fetch_word AsanUbsan.M.loaded_segments (0x5ffc8 : word) = Some W_5ffc8.
Proof. vm_refl. Qed.
Lemma D_5ffc8 : decode_any W_5ffc8 = Some (OpImm ALU_ADD 10 10 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffcc : bv 32 := 0x7ffa0a93.
Lemma F_5ffcc : fetch_word AsanUbsan.M.loaded_segments (0x5ffcc : word) = Some W_5ffcc.
Proof. vm_refl. Qed.
Lemma D_5ffcc : decode_any W_5ffcc = Some (OpImm ALU_ADD 21 20 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffd0 : bv 32 := 0x000ab4a3.
Lemma F_5ffd0 : fetch_word AsanUbsan.M.loaded_segments (0x5ffd0 : word) = Some W_5ffd0.
Proof. vm_refl. Qed.
Lemma D_5ffd0 : decode_any W_5ffd0 = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffd4 : bv 32 := 0x00aa3023.
Lemma F_5ffd4 : fetch_word AsanUbsan.M.loaded_segments (0x5ffd4 : word) = Some W_5ffd4.
Proof. vm_refl. Qed.
Lemma D_5ffd4 : decode_any W_5ffd4 = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffd8 : bv 32 := 0x000a3423.
Lemma F_5ffd8 : fetch_word AsanUbsan.M.loaded_segments (0x5ffd8 : word) = Some W_5ffd8.
Proof. vm_refl. Qed.
Lemma D_5ffd8 : decode_any W_5ffd8 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffdc : bv 32 := 0x010080ef.
Lemma F_5ffdc : fetch_word AsanUbsan.M.loaded_segments (0x5ffdc : word) = Some W_5ffdc.
Proof. vm_refl. Qed.
Lemma D_5ffdc : decode_any W_5ffdc = Some (Jal 1 32784, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffe0 : bv 32 := 0x00200593.
Lemma F_5ffe0 : fetch_word AsanUbsan.M.loaded_segments (0x5ffe0 : word) = Some W_5ffe0.
Proof. vm_refl. Qed.
Lemma D_5ffe0 : decode_any W_5ffe0 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffe4 : bv 32 := 0x02a5ea63.
Lemma F_5ffe4 : fetch_word AsanUbsan.M.loaded_segments (0x5ffe4 : word) = Some W_5ffe4.
Proof. vm_refl. Qed.
Lemma D_5ffe4 : decode_any W_5ffe4 = Some (Branch BC_LTU 11 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffe8 : bv 32 := 0x004080ef.
Lemma F_5ffe8 : fetch_word AsanUbsan.M.loaded_segments (0x5ffe8 : word) = Some W_5ffe8.
Proof. vm_refl. Qed.
Lemma D_5ffe8 : decode_any W_5ffe8 = Some (Jal 1 32772, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffec : bv 32 := 0x00aa2423.
Lemma F_5ffec : fetch_word AsanUbsan.M.loaded_segments (0x5ffec : word) = Some W_5ffec.
Proof. vm_refl. Qed.
Lemma D_5ffec : decode_any W_5ffec = Some (Store SZ4 20 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fff0 : bv 32 := 0x7fd070ef.
Lemma F_5fff0 : fetch_word AsanUbsan.M.loaded_segments (0x5fff0 : word) = Some W_5fff0.
Proof. vm_refl. Qed.
Lemma D_5fff0 : decode_any W_5fff0 = Some (Jal 1 32764, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fff4 : bv 32 := 0x08050263.
Lemma F_5fff4 : fetch_word AsanUbsan.M.loaded_segments (0x5fff4 : word) = Some W_5fff4.
Proof. vm_refl. Qed.
Lemma D_5fff4 : decode_any W_5fff4 = Some (Branch BC_EQ 10 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fff8 : bv 32 := 0x008ab4a3.
Lemma F_5fff8 : fetch_word AsanUbsan.M.loaded_segments (0x5fff8 : word) = Some W_5fff8.
Proof. vm_refl. Qed.
Lemma D_5fff8 : decode_any W_5fff8 = Some (Store SZ8 21 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fffc : bv 32 := 0x2b1200ef.
Lemma F_5fffc : fetch_word AsanUbsan.M.loaded_segments (0x5fffc : word) = Some W_5fffc.
Proof. vm_refl. Qed.
Lemma D_5fffc : decode_any W_5fffc = Some (Jal 1 133808, 4%Z).
Proof. vm_refl. Qed.

Definition W_60000 : bv 32 := 0x00aa3823.
Lemma F_60000 : fetch_word AsanUbsan.M.loaded_segments (0x60000 : word) = Some W_60000.
Proof. vm_refl. Qed.
Lemma D_60000 : decode_any W_60000 = Some (Store SZ8 20 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_60004 : bv 32 := 0x7e9070ef.
Lemma F_60004 : fetch_word AsanUbsan.M.loaded_segments (0x60004 : word) = Some W_60004.
Proof. vm_refl. Qed.
Lemma D_60004 : decode_any W_60004 = Some (Jal 1 32744, 4%Z).
Proof. vm_refl. Qed.

Definition W_60008 : bv 32 := 0x00200593.
Lemma F_60008 : fetch_word AsanUbsan.M.loaded_segments (0x60008 : word) = Some W_60008.
Proof. vm_refl. Qed.
Lemma D_60008 : decode_any W_60008 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_6000c : bv 32 := 0x06b56663.
Lemma F_6000c : fetch_word AsanUbsan.M.loaded_segments (0x6000c : word) = Some W_6000c.
Proof. vm_refl. Qed.
Lemma D_6000c : decode_any W_6000c = Some (Branch BC_LTU 10 11 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_60010 : bv 32 := 0x012a3c23.
Lemma F_60010 : fetch_word AsanUbsan.M.loaded_segments (0x60010 : word) = Some W_60010.
Proof. vm_refl. Qed.
Lemma D_60010 : decode_any W_60010 = Some (Store SZ8 20 18 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_60014 : bv 32 := 0x0640006f.
Lemma F_60014 : fetch_word AsanUbsan.M.loaded_segments (0x60014 : word) = Some W_60014.
Proof. vm_refl. Qed.
Lemma D_60014 : decode_any W_60014 = Some (Jal 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_60018 : bv 32 := 0x295200ef.
Lemma F_60018 : fetch_word AsanUbsan.M.loaded_segments (0x60018 : word) = Some W_60018.
Proof. vm_refl. Qed.
Lemma D_60018 : decode_any W_60018 = Some (Jal 1 133780, 4%Z).
Proof. vm_refl. Qed.

Definition W_6001c : bv 32 := 0x00076597.
Lemma F_6001c : fetch_word AsanUbsan.M.loaded_segments (0x6001c : word) = Some W_6001c.
Proof. vm_refl. Qed.
Lemma D_6001c : decode_any W_6001c = Some (Auipc 11 118, 4%Z).
Proof. vm_refl. Qed.

Definition W_60020 : bv 32 := 0x49c5b583.
Lemma F_60020 : fetch_word AsanUbsan.M.loaded_segments (0x60020 : word) = Some W_60020.
Proof. vm_refl. Qed.
Lemma D_60020 : decode_any W_60020 = Some (Load SZ8 true 11 11 1180, 4%Z).
Proof. vm_refl. Qed.

Definition W_60024 : bv 32 := 0x0225c983.
Lemma F_60024 : fetch_word AsanUbsan.M.loaded_segments (0x60024 : word) = Some W_60024.
Proof. vm_refl. Qed.
Lemma D_60024 : decode_any W_60024 = Some (Load SZ1 false 19 11 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_60028 : bv 32 := 0x00050913.
Lemma F_60028 : fetch_word AsanUbsan.M.loaded_segments (0x60028 : word) = Some W_60028.
Proof. vm_refl. Qed.
Lemma D_60028 : decode_any W_60028 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6002c : bv 32 := 0x7c1070ef.
Lemma F_6002c : fetch_word AsanUbsan.M.loaded_segments (0x6002c : word) = Some W_6002c.
Proof. vm_refl. Qed.
Lemma D_6002c : decode_any W_6002c = Some (Jal 1 32704, 4%Z).
Proof. vm_refl. Qed.

Definition W_60030 : bv 32 := 0x00050793.
Lemma F_60030 : fetch_word AsanUbsan.M.loaded_segments (0x60030 : word) = Some W_60030.
Proof. vm_refl. Qed.
Lemma D_60030 : decode_any W_60030 = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60034 : bv 32 := 0x00153513.
Lemma F_60034 : fetch_word AsanUbsan.M.loaded_segments (0x60034 : word) = Some W_60034.
Proof. vm_refl. Qed.
Lemma D_60034 : decode_any W_60034 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_60038 : bv 32 := 0xfff50513.
Lemma F_60038 : fetch_word AsanUbsan.M.loaded_segments (0x60038 : word) = Some W_60038.
Proof. vm_refl. Qed.
Lemma D_60038 : decode_any W_60038 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6003c : bv 32 := 0x008575b3.
Lemma F_6003c : fetch_word AsanUbsan.M.loaded_segments (0x6003c : word) = Some W_6003c.
Proof. vm_refl. Qed.
Lemma D_6003c : decode_any W_6003c = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_60040 : bv 32 := 0x00100513.
Lemma F_60040 : fetch_word AsanUbsan.M.loaded_segments (0x60040 : word) = Some W_60040.
Proof. vm_refl. Qed.
Lemma D_60040 : decode_any W_60040 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_60044 : bv 32 := 0x00bab4a3.
Lemma F_60044 : fetch_word AsanUbsan.M.loaded_segments (0x60044 : word) = Some W_60044.
Proof. vm_refl. Qed.
Lemma D_60044 : decode_any W_60044 = Some (Store SZ8 21 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_60048 : bv 32 := 0x00f56a63.
Lemma F_60048 : fetch_word AsanUbsan.M.loaded_segments (0x60048 : word) = Some W_60048.
Proof. vm_refl. Qed.
Lemma D_60048 : decode_any W_60048 = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6004c : bv 32 := 0x00a79463.
Lemma F_6004c : fetch_word AsanUbsan.M.loaded_segments (0x6004c : word) = Some W_6004c.
Proof. vm_refl. Qed.
Lemma D_6004c : decode_any W_6004c = Some (Branch BC_NE 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_60050 : bv 32 := 0x012a3823.
Lemma F_60050 : fetch_word AsanUbsan.M.loaded_segments (0x60050 : word) = Some W_60050.
Proof. vm_refl. Qed.
Lemma D_60050 : decode_any W_60050 = Some (Store SZ8 20 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_60054 : bv 32 := 0x00fa2423.
Lemma F_60054 : fetch_word AsanUbsan.M.loaded_segments (0x60054 : word) = Some W_60054.
Proof. vm_refl. Qed.
Lemma D_60054 : decode_any W_60054 = Some (Store SZ4 20 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_60058 : bv 32 := 0x0200006f.
Lemma F_60058 : fetch_word AsanUbsan.M.loaded_segments (0x60058 : word) = Some W_60058.
Proof. vm_refl. Qed.
Lemma D_60058 : decode_any W_60058 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6005c : bv 32 := 0x80040513.
Lemma F_6005c : fetch_word AsanUbsan.M.loaded_segments (0x6005c : word) = Some W_6005c.
Proof. vm_refl. Qed.
Lemma D_6005c : decode_any W_6005c = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_60060 : bv 32 := 0xfb050513.
Lemma F_60060 : fetch_word AsanUbsan.M.loaded_segments (0x60060 : word) = Some W_60060.
Proof. vm_refl. Qed.
Lemma D_60060 : decode_any W_60060 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_60064 : bv 32 := 0x00090593.
Lemma F_60064 : fetch_word AsanUbsan.M.loaded_segments (0x60064 : word) = Some W_60064.
Proof. vm_refl. Qed.
Lemma D_60064 : decode_any W_60064 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60068 : bv 32 := 0x00040613.
Lemma F_60068 : fetch_word AsanUbsan.M.loaded_segments (0x60068 : word) = Some W_60068.
Proof. vm_refl. Qed.
Lemma D_60068 : decode_any W_60068 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6006c : bv 32 := 0x00000693.
Lemma F_6006c : fetch_word AsanUbsan.M.loaded_segments (0x6006c : word) = Some W_6006c.
Proof. vm_refl. Qed.
Lemma D_6006c : decode_any W_6006c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60070 : bv 32 := 0x00098713.
Lemma F_60070 : fetch_word AsanUbsan.M.loaded_segments (0x60070 : word) = Some W_60070.
Proof. vm_refl. Qed.
Lemma D_60070 : decode_any W_60070 = Some (OpImm ALU_ADD 14 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60074 : bv 32 := 0x789070ef.
Lemma F_60074 : fetch_word AsanUbsan.M.loaded_segments (0x60074 : word) = Some W_60074.
Proof. vm_refl. Qed.
Lemma D_60074 : decode_any W_60074 = Some (Jal 1 32648, 4%Z).
Proof. vm_refl. Qed.

Definition W_60078 : bv 32 := 0x80040593.
Lemma F_60078 : fetch_word AsanUbsan.M.loaded_segments (0x60078 : word) = Some W_60078.
Proof. vm_refl. Qed.
Lemma D_60078 : decode_any W_60078 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_6007c : bv 32 := 0xfb058593.
Lemma F_6007c : fetch_word AsanUbsan.M.loaded_segments (0x6007c : word) = Some W_6007c.
Proof. vm_refl. Qed.
Lemma D_6007c : decode_any W_6007c = Some (OpImm ALU_ADD 11 11 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_60080 : bv 32 := 0x00100613.
Lemma F_60080 : fetch_word AsanUbsan.M.loaded_segments (0x60080 : word) = Some W_60080.
Proof. vm_refl. Qed.
Lemma D_60080 : decode_any W_60080 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_60084 : bv 32 := 0x00048513.
Lemma F_60084 : fetch_word AsanUbsan.M.loaded_segments (0x60084 : word) = Some W_60084.
Proof. vm_refl. Qed.
Lemma D_60084 : decode_any W_60084 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60088 : bv 32 := 0xa2cdd0ef.
Lemma F_60088 : fetch_word AsanUbsan.M.loaded_segments (0x60088 : word) = Some W_60088.
Proof. vm_refl. Qed.
Lemma D_60088 : decode_any W_60088 = Some (Jal 1 1954348, 4%Z).
Proof. vm_refl. Qed.

Definition W_6008c : bv 32 := 0x06010113.
Lemma F_6008c : fetch_word AsanUbsan.M.loaded_segments (0x6008c : word) = Some W_6008c.
Proof. vm_refl. Qed.
Lemma D_6008c : decode_any W_6008c = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_60090 : bv 32 := 0x7e813083.
Lemma F_60090 : fetch_word AsanUbsan.M.loaded_segments (0x60090 : word) = Some W_60090.
Proof. vm_refl. Qed.
Lemma D_60090 : decode_any W_60090 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_60094 : bv 32 := 0x7e013403.
Lemma F_60094 : fetch_word AsanUbsan.M.loaded_segments (0x60094 : word) = Some W_60094.
Proof. vm_refl. Qed.
Lemma D_60094 : decode_any W_60094 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_60098 : bv 32 := 0x7d813483.
Lemma F_60098 : fetch_word AsanUbsan.M.loaded_segments (0x60098 : word) = Some W_60098.
Proof. vm_refl. Qed.
Lemma D_60098 : decode_any W_60098 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_6009c : bv 32 := 0x7d013903.
Lemma F_6009c : fetch_word AsanUbsan.M.loaded_segments (0x6009c : word) = Some W_6009c.
Proof. vm_refl. Qed.
Lemma D_6009c : decode_any W_6009c = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_600a0 : bv 32 := 0x7c813983.
Lemma F_600a0 : fetch_word AsanUbsan.M.loaded_segments (0x600a0 : word) = Some W_600a0.
Proof. vm_refl. Qed.
Lemma D_600a0 : decode_any W_600a0 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_600a4 : bv 32 := 0x7c013a03.
Lemma F_600a4 : fetch_word AsanUbsan.M.loaded_segments (0x600a4 : word) = Some W_600a4.
Proof. vm_refl. Qed.
Lemma D_600a4 : decode_any W_600a4 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_600a8 : bv 32 := 0x7b813a83.
Lemma F_600a8 : fetch_word AsanUbsan.M.loaded_segments (0x600a8 : word) = Some W_600a8.
Proof. vm_refl. Qed.
Lemma D_600a8 : decode_any W_600a8 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_600ac : bv 32 := 0x7f010113.
Lemma F_600ac : fetch_word AsanUbsan.M.loaded_segments (0x600ac : word) = Some W_600ac.
Proof. vm_refl. Qed.
Lemma D_600ac : decode_any W_600ac = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_600b0 : bv 32 := 0x00008067.
Lemma F_600b0 : fetch_word AsanUbsan.M.loaded_segments (0x600b0 : word) = Some W_600b0.
Proof. vm_refl. Qed.
Lemma D_600b0 : decode_any W_600b0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_600b4 : bv 32 := 0x81010113.
Lemma F_600b4 : fetch_word AsanUbsan.M.loaded_segments (0x600b4 : word) = Some W_600b4.
Proof. vm_refl. Qed.
Lemma D_600b4 : decode_any W_600b4 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_600b8 : bv 32 := 0x7e113423.
Lemma F_600b8 : fetch_word AsanUbsan.M.loaded_segments (0x600b8 : word) = Some W_600b8.
Proof. vm_refl. Qed.
Lemma D_600b8 : decode_any W_600b8 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_600bc : bv 32 := 0x7e813023.
Lemma F_600bc : fetch_word AsanUbsan.M.loaded_segments (0x600bc : word) = Some W_600bc.
Proof. vm_refl. Qed.
Lemma D_600bc : decode_any W_600bc = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_600c0 : bv 32 := 0x7c913c23.
Lemma F_600c0 : fetch_word AsanUbsan.M.loaded_segments (0x600c0 : word) = Some W_600c0.
Proof. vm_refl. Qed.
Lemma D_600c0 : decode_any W_600c0 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_600c4 : bv 32 := 0x7d213823.
Lemma F_600c4 : fetch_word AsanUbsan.M.loaded_segments (0x600c4 : word) = Some W_600c4.
Proof. vm_refl. Qed.
Lemma D_600c4 : decode_any W_600c4 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_600c8 : bv 32 := 0x7d313423.
Lemma F_600c8 : fetch_word AsanUbsan.M.loaded_segments (0x600c8 : word) = Some W_600c8.
Proof. vm_refl. Qed.
Lemma D_600c8 : decode_any W_600c8 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_600cc : bv 32 := 0x7d413023.
Lemma F_600cc : fetch_word AsanUbsan.M.loaded_segments (0x600cc : word) = Some W_600cc.
Proof. vm_refl. Qed.
Lemma D_600cc : decode_any W_600cc = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_600d0 : bv 32 := 0x7b513c23.
Lemma F_600d0 : fetch_word AsanUbsan.M.loaded_segments (0x600d0 : word) = Some W_600d0.
Proof. vm_refl. Qed.
Lemma D_600d0 : decode_any W_600d0 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_600d4 : bv 32 := 0x7f010413.
Lemma F_600d4 : fetch_word AsanUbsan.M.loaded_segments (0x600d4 : word) = Some W_600d4.
Proof. vm_refl. Qed.
Lemma D_600d4 : decode_any W_600d4 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_600d8 : bv 32 := 0xfa010113.
Lemma F_600d8 : fetch_word AsanUbsan.M.loaded_segments (0x600d8 : word) = Some W_600d8.
Proof. vm_refl. Qed.
Lemma D_600d8 : decode_any W_600d8 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_600dc : bv 32 := 0x00008913.
Lemma F_600dc : fetch_word AsanUbsan.M.loaded_segments (0x600dc : word) = Some W_600dc.
Proof. vm_refl. Qed.
Lemma D_600dc : decode_any W_600dc = Some (OpImm ALU_ADD 18 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_600e0 : bv 32 := 0x00050493.
Lemma F_600e0 : fetch_word AsanUbsan.M.loaded_segments (0x600e0 : word) = Some W_600e0.
Proof. vm_refl. Qed.
Lemma D_600e0 : decode_any W_600e0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_600e4 : bv 32 := 0x180070ef.
Lemma F_600e4 : fetch_word AsanUbsan.M.loaded_segments (0x600e4 : word) = Some W_600e4.
Proof. vm_refl. Qed.
Lemma D_600e4 : decode_any W_600e4 = Some (Jal 1 29056, 4%Z).
Proof. vm_refl. Qed.

Definition W_600e8 : bv 32 := 0x06050063.
Lemma F_600e8 : fetch_word AsanUbsan.M.loaded_segments (0x600e8 : word) = Some W_600e8.
Proof. vm_refl. Qed.
Lemma D_600e8 : decode_any W_600e8 = Some (Branch BC_EQ 10 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_600ec : bv 32 := 0x80040a13.
Lemma F_600ec : fetch_word AsanUbsan.M.loaded_segments (0x600ec : word) = Some W_600ec.
Proof. vm_refl. Qed.
Lemma D_600ec : decode_any W_600ec = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_600f0 : bv 32 := 0xfb0a0a13.
Lemma F_600f0 : fetch_word AsanUbsan.M.loaded_segments (0x600f0 : word) = Some W_600f0.
Proof. vm_refl. Qed.
Lemma D_600f0 : decode_any W_600f0 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_600f4 : bv 32 := 0x80040513.
Lemma F_600f4 : fetch_word AsanUbsan.M.loaded_segments (0x600f4 : word) = Some W_600f4.
Proof. vm_refl. Qed.
Lemma D_600f4 : decode_any W_600f4 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_600f8 : bv 32 := 0xfc050513.
Lemma F_600f8 : fetch_word AsanUbsan.M.loaded_segments (0x600f8 : word) = Some W_600f8.
Proof. vm_refl. Qed.
Lemma D_600f8 : decode_any W_600f8 = Some (OpImm ALU_ADD 10 10 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_600fc : bv 32 := 0x7ffa0a93.
Lemma F_600fc : fetch_word AsanUbsan.M.loaded_segments (0x600fc : word) = Some W_600fc.
Proof. vm_refl. Qed.
Lemma D_600fc : decode_any W_600fc = Some (OpImm ALU_ADD 21 20 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_60100 : bv 32 := 0x000ab4a3.
Lemma F_60100 : fetch_word AsanUbsan.M.loaded_segments (0x60100 : word) = Some W_60100.
Proof. vm_refl. Qed.
Lemma D_60100 : decode_any W_60100 = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_60104 : bv 32 := 0x00aa3023.
Lemma F_60104 : fetch_word AsanUbsan.M.loaded_segments (0x60104 : word) = Some W_60104.
Proof. vm_refl. Qed.
Lemma D_60104 : decode_any W_60104 = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60108 : bv 32 := 0x000a3423.
Lemma F_60108 : fetch_word AsanUbsan.M.loaded_segments (0x60108 : word) = Some W_60108.
Proof. vm_refl. Qed.
Lemma D_60108 : decode_any W_60108 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6010c : bv 32 := 0x6e1070ef.
Lemma F_6010c : fetch_word AsanUbsan.M.loaded_segments (0x6010c : word) = Some W_6010c.
Proof. vm_refl. Qed.
Lemma D_6010c : decode_any W_6010c = Some (Jal 1 32480, 4%Z).
Proof. vm_refl. Qed.

Definition W_60110 : bv 32 := 0x00200593.
Lemma F_60110 : fetch_word AsanUbsan.M.loaded_segments (0x60110 : word) = Some W_60110.
Proof. vm_refl. Qed.
Lemma D_60110 : decode_any W_60110 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_60114 : bv 32 := 0x06a5e263.
Lemma F_60114 : fetch_word AsanUbsan.M.loaded_segments (0x60114 : word) = Some W_60114.
Proof. vm_refl. Qed.
Lemma D_60114 : decode_any W_60114 = Some (Branch BC_LTU 11 10 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_60118 : bv 32 := 0x6d5070ef.
Lemma F_60118 : fetch_word AsanUbsan.M.loaded_segments (0x60118 : word) = Some W_60118.
Proof. vm_refl. Qed.
Lemma D_60118 : decode_any W_60118 = Some (Jal 1 32468, 4%Z).
Proof. vm_refl. Qed.

Definition W_6011c : bv 32 := 0x00aa2423.
Lemma F_6011c : fetch_word AsanUbsan.M.loaded_segments (0x6011c : word) = Some W_6011c.
Proof. vm_refl. Qed.
Lemma D_6011c : decode_any W_6011c = Some (Store SZ4 20 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_60120 : bv 32 := 0x6cd070ef.
Lemma F_60120 : fetch_word AsanUbsan.M.loaded_segments (0x60120 : word) = Some W_60120.
Proof. vm_refl. Qed.
Lemma D_60120 : decode_any W_60120 = Some (Jal 1 32460, 4%Z).
Proof. vm_refl. Qed.

Definition W_60124 : bv 32 := 0x0a050a63.
Lemma F_60124 : fetch_word AsanUbsan.M.loaded_segments (0x60124 : word) = Some W_60124.
Proof. vm_refl. Qed.
Lemma D_60124 : decode_any W_60124 = Some (Branch BC_EQ 10 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_60128 : bv 32 := 0x008ab4a3.
Lemma F_60128 : fetch_word AsanUbsan.M.loaded_segments (0x60128 : word) = Some W_60128.
Proof. vm_refl. Qed.
Lemma D_60128 : decode_any W_60128 = Some (Store SZ8 21 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_6012c : bv 32 := 0x181200ef.
Lemma F_6012c : fetch_word AsanUbsan.M.loaded_segments (0x6012c : word) = Some W_6012c.
Proof. vm_refl. Qed.
Lemma D_6012c : decode_any W_6012c = Some (Jal 1 133504, 4%Z).
Proof. vm_refl. Qed.

Definition W_60130 : bv 32 := 0x00aa3823.
Lemma F_60130 : fetch_word AsanUbsan.M.loaded_segments (0x60130 : word) = Some W_60130.
Proof. vm_refl. Qed.
Lemma D_60130 : decode_any W_60130 = Some (Store SZ8 20 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_60134 : bv 32 := 0x6b9070ef.
Lemma F_60134 : fetch_word AsanUbsan.M.loaded_segments (0x60134 : word) = Some W_60134.
Proof. vm_refl. Qed.
Lemma D_60134 : decode_any W_60134 = Some (Jal 1 32440, 4%Z).
Proof. vm_refl. Qed.

Definition W_60138 : bv 32 := 0x00200593.
Lemma F_60138 : fetch_word AsanUbsan.M.loaded_segments (0x60138 : word) = Some W_60138.
Proof. vm_refl. Qed.
Lemma D_60138 : decode_any W_60138 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_6013c : bv 32 := 0x08b56e63.
Lemma F_6013c : fetch_word AsanUbsan.M.loaded_segments (0x6013c : word) = Some W_6013c.
Proof. vm_refl. Qed.
Lemma D_6013c : decode_any W_6013c = Some (Branch BC_LTU 10 11 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_60140 : bv 32 := 0x012a3c23.
Lemma F_60140 : fetch_word AsanUbsan.M.loaded_segments (0x60140 : word) = Some W_60140.
Proof. vm_refl. Qed.
Lemma D_60140 : decode_any W_60140 = Some (Store SZ8 20 18 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_60144 : bv 32 := 0x0940006f.
Lemma F_60144 : fetch_word AsanUbsan.M.loaded_segments (0x60144 : word) = Some W_60144.
Proof. vm_refl. Qed.
Lemma D_60144 : decode_any W_60144 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_60148 : bv 32 := 0x00800593.
Lemma F_60148 : fetch_word AsanUbsan.M.loaded_segments (0x60148 : word) = Some W_60148.
Proof. vm_refl. Qed.
Lemma D_60148 : decode_any W_60148 = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6014c : bv 32 := 0x00048513.
Lemma F_6014c : fetch_word AsanUbsan.M.loaded_segments (0x6014c : word) = Some W_6014c.
Proof. vm_refl. Qed.
Lemma D_6014c : decode_any W_6014c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60150 : bv 32 := 0x06010113.
Lemma F_60150 : fetch_word AsanUbsan.M.loaded_segments (0x60150 : word) = Some W_60150.
Proof. vm_refl. Qed.
Lemma D_60150 : decode_any W_60150 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_60154 : bv 32 := 0x7e813083.
Lemma F_60154 : fetch_word AsanUbsan.M.loaded_segments (0x60154 : word) = Some W_60154.
Proof. vm_refl. Qed.
Lemma D_60154 : decode_any W_60154 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_60158 : bv 32 := 0x7e013403.
Lemma F_60158 : fetch_word AsanUbsan.M.loaded_segments (0x60158 : word) = Some W_60158.
Proof. vm_refl. Qed.
Lemma D_60158 : decode_any W_60158 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_6015c : bv 32 := 0x7d813483.
Lemma F_6015c : fetch_word AsanUbsan.M.loaded_segments (0x6015c : word) = Some W_6015c.
Proof. vm_refl. Qed.
Lemma D_6015c : decode_any W_6015c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_60160 : bv 32 := 0x7d013903.
Lemma F_60160 : fetch_word AsanUbsan.M.loaded_segments (0x60160 : word) = Some W_60160.
Proof. vm_refl. Qed.
Lemma D_60160 : decode_any W_60160 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_60164 : bv 32 := 0x7c813983.
Lemma F_60164 : fetch_word AsanUbsan.M.loaded_segments (0x60164 : word) = Some W_60164.
Proof. vm_refl. Qed.
Lemma D_60164 : decode_any W_60164 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_60168 : bv 32 := 0x7c013a03.
Lemma F_60168 : fetch_word AsanUbsan.M.loaded_segments (0x60168 : word) = Some W_60168.
Proof. vm_refl. Qed.
Lemma D_60168 : decode_any W_60168 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_6016c : bv 32 := 0x7b813a83.
Lemma F_6016c : fetch_word AsanUbsan.M.loaded_segments (0x6016c : word) = Some W_6016c.
Proof. vm_refl. Qed.
Lemma D_6016c : decode_any W_6016c = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_60170 : bv 32 := 0x7f010113.
Lemma F_60170 : fetch_word AsanUbsan.M.loaded_segments (0x60170 : word) = Some W_60170.
Proof. vm_refl. Qed.
Lemma D_60170 : decode_any W_60170 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_60174 : bv 32 := 0x09c0006f.
Lemma F_60174 : fetch_word AsanUbsan.M.loaded_segments (0x60174 : word) = Some W_60174.
Proof. vm_refl. Qed.
Lemma D_60174 : decode_any W_60174 = Some (Jal 0 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_60178 : bv 32 := 0x135200ef.
Lemma F_60178 : fetch_word AsanUbsan.M.loaded_segments (0x60178 : word) = Some W_60178.
Proof. vm_refl. Qed.
Lemma D_60178 : decode_any W_60178 = Some (Jal 1 133428, 4%Z).
Proof. vm_refl. Qed.

Definition W_6017c : bv 32 := 0x00076597.
Lemma F_6017c : fetch_word AsanUbsan.M.loaded_segments (0x6017c : word) = Some W_6017c.
Proof. vm_refl. Qed.
Lemma D_6017c : decode_any W_6017c = Some (Auipc 11 118, 4%Z).
Proof. vm_refl. Qed.

Definition W_60180 : bv 32 := 0x33c5b583.
Lemma F_60180 : fetch_word AsanUbsan.M.loaded_segments (0x60180 : word) = Some W_60180.
Proof. vm_refl. Qed.
Lemma D_60180 : decode_any W_60180 = Some (Load SZ8 true 11 11 828, 4%Z).
Proof. vm_refl. Qed.

Definition W_60184 : bv 32 := 0x0225c983.
Lemma F_60184 : fetch_word AsanUbsan.M.loaded_segments (0x60184 : word) = Some W_60184.
Proof. vm_refl. Qed.
Lemma D_60184 : decode_any W_60184 = Some (Load SZ1 false 19 11 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_60188 : bv 32 := 0x00050913.
Lemma F_60188 : fetch_word AsanUbsan.M.loaded_segments (0x60188 : word) = Some W_60188.
Proof. vm_refl. Qed.
Lemma D_60188 : decode_any W_60188 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6018c : bv 32 := 0x661070ef.
Lemma F_6018c : fetch_word AsanUbsan.M.loaded_segments (0x6018c : word) = Some W_6018c.
Proof. vm_refl. Qed.
Lemma D_6018c : decode_any W_6018c = Some (Jal 1 32352, 4%Z).
Proof. vm_refl. Qed.

Definition W_60190 : bv 32 := 0x00050793.
Lemma F_60190 : fetch_word AsanUbsan.M.loaded_segments (0x60190 : word) = Some W_60190.
Proof. vm_refl. Qed.
Lemma D_60190 : decode_any W_60190 = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60194 : bv 32 := 0x00153513.
Lemma F_60194 : fetch_word AsanUbsan.M.loaded_segments (0x60194 : word) = Some W_60194.
Proof. vm_refl. Qed.
Lemma D_60194 : decode_any W_60194 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_60198 : bv 32 := 0xfff50513.
Lemma F_60198 : fetch_word AsanUbsan.M.loaded_segments (0x60198 : word) = Some W_60198.
Proof. vm_refl. Qed.
Lemma D_60198 : decode_any W_60198 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6019c : bv 32 := 0x008575b3.
Lemma F_6019c : fetch_word AsanUbsan.M.loaded_segments (0x6019c : word) = Some W_6019c.
Proof. vm_refl. Qed.
Lemma D_6019c : decode_any W_6019c = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_601a0 : bv 32 := 0x00100513.
Lemma F_601a0 : fetch_word AsanUbsan.M.loaded_segments (0x601a0 : word) = Some W_601a0.
Proof. vm_refl. Qed.
Lemma D_601a0 : decode_any W_601a0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_601a4 : bv 32 := 0x00bab4a3.
Lemma F_601a4 : fetch_word AsanUbsan.M.loaded_segments (0x601a4 : word) = Some W_601a4.
Proof. vm_refl. Qed.
Lemma D_601a4 : decode_any W_601a4 = Some (Store SZ8 21 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_601a8 : bv 32 := 0x00f56a63.
Lemma F_601a8 : fetch_word AsanUbsan.M.loaded_segments (0x601a8 : word) = Some W_601a8.
Proof. vm_refl. Qed.
Lemma D_601a8 : decode_any W_601a8 = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_601ac : bv 32 := 0x00a79463.
Lemma F_601ac : fetch_word AsanUbsan.M.loaded_segments (0x601ac : word) = Some W_601ac.
Proof. vm_refl. Qed.
Lemma D_601ac : decode_any W_601ac = Some (Branch BC_NE 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_601b0 : bv 32 := 0x012a3823.
Lemma F_601b0 : fetch_word AsanUbsan.M.loaded_segments (0x601b0 : word) = Some W_601b0.
Proof. vm_refl. Qed.
Lemma D_601b0 : decode_any W_601b0 = Some (Store SZ8 20 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_601b4 : bv 32 := 0x00fa2423.
Lemma F_601b4 : fetch_word AsanUbsan.M.loaded_segments (0x601b4 : word) = Some W_601b4.
Proof. vm_refl. Qed.
Lemma D_601b4 : decode_any W_601b4 = Some (Store SZ4 20 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_601b8 : bv 32 := 0x0200006f.
Lemma F_601b8 : fetch_word AsanUbsan.M.loaded_segments (0x601b8 : word) = Some W_601b8.
Proof. vm_refl. Qed.
Lemma D_601b8 : decode_any W_601b8 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_601bc : bv 32 := 0x80040513.
Lemma F_601bc : fetch_word AsanUbsan.M.loaded_segments (0x601bc : word) = Some W_601bc.
Proof. vm_refl. Qed.
Lemma D_601bc : decode_any W_601bc = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_601c0 : bv 32 := 0xfb050513.
Lemma F_601c0 : fetch_word AsanUbsan.M.loaded_segments (0x601c0 : word) = Some W_601c0.
Proof. vm_refl. Qed.
Lemma D_601c0 : decode_any W_601c0 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_601c4 : bv 32 := 0x00090593.
Lemma F_601c4 : fetch_word AsanUbsan.M.loaded_segments (0x601c4 : word) = Some W_601c4.
Proof. vm_refl. Qed.
Lemma D_601c4 : decode_any W_601c4 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_601c8 : bv 32 := 0x00040613.
Lemma F_601c8 : fetch_word AsanUbsan.M.loaded_segments (0x601c8 : word) = Some W_601c8.
Proof. vm_refl. Qed.
Lemma D_601c8 : decode_any W_601c8 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_601cc : bv 32 := 0x00000693.
Lemma F_601cc : fetch_word AsanUbsan.M.loaded_segments (0x601cc : word) = Some W_601cc.
Proof. vm_refl. Qed.
Lemma D_601cc : decode_any W_601cc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_601d0 : bv 32 := 0x00098713.
Lemma F_601d0 : fetch_word AsanUbsan.M.loaded_segments (0x601d0 : word) = Some W_601d0.
Proof. vm_refl. Qed.
Lemma D_601d0 : decode_any W_601d0 = Some (OpImm ALU_ADD 14 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_601d4 : bv 32 := 0x629070ef.
Lemma F_601d4 : fetch_word AsanUbsan.M.loaded_segments (0x601d4 : word) = Some W_601d4.
Proof. vm_refl. Qed.
Lemma D_601d4 : decode_any W_601d4 = Some (Jal 1 32296, 4%Z).
Proof. vm_refl. Qed.

Definition W_601d8 : bv 32 := 0x80040593.
Lemma F_601d8 : fetch_word AsanUbsan.M.loaded_segments (0x601d8 : word) = Some W_601d8.
Proof. vm_refl. Qed.
Lemma D_601d8 : decode_any W_601d8 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_601dc : bv 32 := 0xfb058593.
Lemma F_601dc : fetch_word AsanUbsan.M.loaded_segments (0x601dc : word) = Some W_601dc.
Proof. vm_refl. Qed.
Lemma D_601dc : decode_any W_601dc = Some (OpImm ALU_ADD 11 11 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_601e0 : bv 32 := 0x00048513.
Lemma F_601e0 : fetch_word AsanUbsan.M.loaded_segments (0x601e0 : word) = Some W_601e0.
Proof. vm_refl. Qed.
Lemma D_601e0 : decode_any W_601e0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_601e4 : bv 32 := 0xbb0dd0ef.
Lemma F_601e4 : fetch_word AsanUbsan.M.loaded_segments (0x601e4 : word) = Some W_601e4.
Proof. vm_refl. Qed.
Lemma D_601e4 : decode_any W_601e4 = Some (Jal 1 1954736, 4%Z).
Proof. vm_refl. Qed.

Definition W_601e8 : bv 32 := 0x06010113.
Lemma F_601e8 : fetch_word AsanUbsan.M.loaded_segments (0x601e8 : word) = Some W_601e8.
Proof. vm_refl. Qed.
Lemma D_601e8 : decode_any W_601e8 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_601ec : bv 32 := 0x7e813083.
Lemma F_601ec : fetch_word AsanUbsan.M.loaded_segments (0x601ec : word) = Some W_601ec.
Proof. vm_refl. Qed.
Lemma D_601ec : decode_any W_601ec = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_601f0 : bv 32 := 0x7e013403.
Lemma F_601f0 : fetch_word AsanUbsan.M.loaded_segments (0x601f0 : word) = Some W_601f0.
Proof. vm_refl. Qed.
Lemma D_601f0 : decode_any W_601f0 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_601f4 : bv 32 := 0x7d813483.
Lemma F_601f4 : fetch_word AsanUbsan.M.loaded_segments (0x601f4 : word) = Some W_601f4.
Proof. vm_refl. Qed.
Lemma D_601f4 : decode_any W_601f4 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_601f8 : bv 32 := 0x7d013903.
Lemma F_601f8 : fetch_word AsanUbsan.M.loaded_segments (0x601f8 : word) = Some W_601f8.
Proof. vm_refl. Qed.
Lemma D_601f8 : decode_any W_601f8 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_601fc : bv 32 := 0x7c813983.
Lemma F_601fc : fetch_word AsanUbsan.M.loaded_segments (0x601fc : word) = Some W_601fc.
Proof. vm_refl. Qed.
Lemma D_601fc : decode_any W_601fc = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_60200 : bv 32 := 0x7c013a03.
Lemma F_60200 : fetch_word AsanUbsan.M.loaded_segments (0x60200 : word) = Some W_60200.
Proof. vm_refl. Qed.
Lemma D_60200 : decode_any W_60200 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_60204 : bv 32 := 0x7b813a83.
Lemma F_60204 : fetch_word AsanUbsan.M.loaded_segments (0x60204 : word) = Some W_60204.
Proof. vm_refl. Qed.
Lemma D_60204 : decode_any W_60204 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_60208 : bv 32 := 0x7f010113.
Lemma F_60208 : fetch_word AsanUbsan.M.loaded_segments (0x60208 : word) = Some W_60208.
Proof. vm_refl. Qed.
Lemma D_60208 : decode_any W_60208 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_6020c : bv 32 := 0x00008067.
Lemma F_6020c : fetch_word AsanUbsan.M.loaded_segments (0x6020c : word) = Some W_6020c.
Proof. vm_refl. Qed.
Lemma D_6020c : decode_any W_6020c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60210 : bv 32 := 0xfe010113.
Lemma F_60210 : fetch_word AsanUbsan.M.loaded_segments (0x60210 : word) = Some W_60210.
Proof. vm_refl. Qed.
Lemma D_60210 : decode_any W_60210 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_60214 : bv 32 := 0x00113c23.
Lemma F_60214 : fetch_word AsanUbsan.M.loaded_segments (0x60214 : word) = Some W_60214.
Proof. vm_refl. Qed.
Lemma D_60214 : decode_any W_60214 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_60218 : bv 32 := 0x00813823.
Lemma F_60218 : fetch_word AsanUbsan.M.loaded_segments (0x60218 : word) = Some W_60218.
Proof. vm_refl. Qed.
Lemma D_60218 : decode_any W_60218 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6021c : bv 32 := 0x00913423.
Lemma F_6021c : fetch_word AsanUbsan.M.loaded_segments (0x6021c : word) = Some W_6021c.
Proof. vm_refl. Qed.
Lemma D_6021c : decode_any W_6021c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_60220 : bv 32 := 0x00058613.
Lemma F_60220 : fetch_word AsanUbsan.M.loaded_segments (0x60220 : word) = Some W_60220.
Proof. vm_refl. Qed.
Lemma D_60220 : decode_any W_60220 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60224 : bv 32 := 0x00000593.
Lemma F_60224 : fetch_word AsanUbsan.M.loaded_segments (0x60224 : word) = Some W_60224.
Proof. vm_refl. Qed.
Lemma D_60224 : decode_any W_60224 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60228 : bv 32 := 0x2110b0ef.
Lemma F_60228 : fetch_word AsanUbsan.M.loaded_segments (0x60228 : word) = Some W_60228.
Proof. vm_refl. Qed.
Lemma D_60228 : decode_any W_60228 = Some (Jal 1 47632, 4%Z).
Proof. vm_refl. Qed.

Definition W_6022c : bv 32 := 0x00050413.
Lemma F_6022c : fetch_word AsanUbsan.M.loaded_segments (0x6022c : word) = Some W_6022c.
Proof. vm_refl. Qed.
Lemma D_6022c : decode_any W_6022c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60230 : bv 32 := 0x0b10b0ef.
Lemma F_60230 : fetch_word AsanUbsan.M.loaded_segments (0x60230 : word) = Some W_60230.
Proof. vm_refl. Qed.
Lemma D_60230 : decode_any W_60230 = Some (Jal 1 47280, 4%Z).
Proof. vm_refl. Qed.

Definition W_60234 : bv 32 := 0x02f45593.
Lemma F_60234 : fetch_word AsanUbsan.M.loaded_segments (0x60234 : word) = Some W_60234.
Proof. vm_refl. Qed.
Lemma D_60234 : decode_any W_60234 = Some (ShiftImm ALU_SRL 11 8 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_60238 : bv 32 := 0x08059263.
Lemma F_60238 : fetch_word AsanUbsan.M.loaded_segments (0x60238 : word) = Some W_60238.
Proof. vm_refl. Qed.
Lemma D_60238 : decode_any W_60238 = Some (Branch BC_NE 11 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_6023c : bv 32 := 0x02045593.
Lemma F_6023c : fetch_word AsanUbsan.M.loaded_segments (0x6023c : word) = Some W_6023c.
Proof. vm_refl. Qed.
Lemma D_6023c : decode_any W_6023c = Some (ShiftImm ALU_SRL 11 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_60240 : bv 32 := 0x00359613.
Lemma F_60240 : fetch_word AsanUbsan.M.loaded_segments (0x60240 : word) = Some W_60240.
Proof. vm_refl. Qed.
Lemma D_60240 : decode_any W_60240 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_60244 : bv 32 := 0x00c50633.
Lemma F_60244 : fetch_word AsanUbsan.M.loaded_segments (0x60244 : word) = Some W_60244.
Proof. vm_refl. Qed.
Lemma D_60244 : decode_any W_60244 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_60248 : bv 32 := 0x00863683.
Lemma F_60248 : fetch_word AsanUbsan.M.loaded_segments (0x60248 : word) = Some W_60248.
Proof. vm_refl. Qed.
Lemma D_60248 : decode_any W_60248 = Some (Load SZ8 true 13 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6024c : bv 32 := 0x0230000f.
Lemma F_6024c : fetch_word AsanUbsan.M.loaded_segments (0x6024c : word) = Some W_6024c.
Proof. vm_refl. Qed.
Lemma D_6024c : decode_any W_6024c = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60250 : bv 32 := 0x06068663.
Lemma F_60250 : fetch_word AsanUbsan.M.loaded_segments (0x60250 : word) = Some W_60250.
Proof. vm_refl. Qed.
Lemma D_60250 : decode_any W_60250 = Some (Branch BC_EQ 13 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_60254 : bv 32 := 0x00863603.
Lemma F_60254 : fetch_word AsanUbsan.M.loaded_segments (0x60254 : word) = Some W_60254.
Proof. vm_refl. Qed.
Lemma D_60254 : decode_any W_60254 = Some (Load SZ8 true 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_60258 : bv 32 := 0x01445493.
Lemma F_60258 : fetch_word AsanUbsan.M.loaded_segments (0x60258 : word) = Some W_60258.
Proof. vm_refl. Qed.
Lemma D_60258 : decode_any W_60258 = Some (ShiftImm ALU_SRL 9 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6025c : bv 32 := 0x04060463.
Lemma F_6025c : fetch_word AsanUbsan.M.loaded_segments (0x6025c : word) = Some W_6025c.
Proof. vm_refl. Qed.
Lemma D_6025c : decode_any W_6025c = Some (Branch BC_EQ 12 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_60260 : bv 32 := 0x03449493.
Lemma F_60260 : fetch_word AsanUbsan.M.loaded_segments (0x60260 : word) = Some W_60260.
Proof. vm_refl. Qed.
Lemma D_60260 : decode_any W_60260 = Some (ShiftImm ALU_SLL 9 9 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_60264 : bv 32 := 0x0344d493.
Lemma F_60264 : fetch_word AsanUbsan.M.loaded_segments (0x60264 : word) = Some W_60264.
Proof. vm_refl. Qed.
Lemma D_60264 : decode_any W_60264 = Some (ShiftImm ALU_SRL 9 9 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_60268 : bv 32 := 0x00960633.
Lemma F_60268 : fetch_word AsanUbsan.M.loaded_segments (0x60268 : word) = Some W_60268.
Proof. vm_refl. Qed.
Lemma D_60268 : decode_any W_60268 = Some (Op ALU_ADD 12 12 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_6026c : bv 32 := 0x00064503.
Lemma F_6026c : fetch_word AsanUbsan.M.loaded_segments (0x6026c : word) = Some W_6026c.
Proof. vm_refl. Qed.
Lemma D_6026c : decode_any W_6026c = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60270 : bv 32 := 0x04050663.
Lemma F_60270 : fetch_word AsanUbsan.M.loaded_segments (0x60270 : word) = Some W_60270.
Proof. vm_refl. Qed.
Lemma D_60270 : decode_any W_60270 = Some (Branch BC_EQ 10 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_60274 : bv 32 := 0x06d0b0ef.
Lemma F_60274 : fetch_word AsanUbsan.M.loaded_segments (0x60274 : word) = Some W_60274.
Proof. vm_refl. Qed.
Lemma D_60274 : decode_any W_60274 = Some (Jal 1 47212, 4%Z).
Proof. vm_refl. Qed.

Definition W_60278 : bv 32 := 0x00040593.
Lemma F_60278 : fetch_word AsanUbsan.M.loaded_segments (0x60278 : word) = Some W_60278.
Proof. vm_refl. Qed.
Lemma D_60278 : decode_any W_60278 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6027c : bv 32 := 0x5dc000ef.
Lemma F_6027c : fetch_word AsanUbsan.M.loaded_segments (0x6027c : word) = Some W_6027c.
Proof. vm_refl. Qed.
Lemma D_6027c : decode_any W_6027c = Some (Jal 1 1500, 4%Z).
Proof. vm_refl. Qed.

Definition W_60280 : bv 32 := 0x00050593.
Lemma F_60280 : fetch_word AsanUbsan.M.loaded_segments (0x60280 : word) = Some W_60280.
Proof. vm_refl. Qed.
Lemma D_60280 : decode_any W_60280 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60284 : bv 32 := 0x00040513.
Lemma F_60284 : fetch_word AsanUbsan.M.loaded_segments (0x60284 : word) = Some W_60284.
Proof. vm_refl. Qed.
Lemma D_60284 : decode_any W_60284 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60288 : bv 32 := 0x0242a0ef.
Lemma F_60288 : fetch_word AsanUbsan.M.loaded_segments (0x60288 : word) = Some W_60288.
Proof. vm_refl. Qed.
Lemma D_60288 : decode_any W_60288 = Some (Jal 1 172068, 4%Z).
Proof. vm_refl. Qed.

Definition W_6028c : bv 32 := 0x00040513.
Lemma F_6028c : fetch_word AsanUbsan.M.loaded_segments (0x6028c : word) = Some W_6028c.
Proof. vm_refl. Qed.
Lemma D_6028c : decode_any W_6028c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60290 : bv 32 := 0x01813083.
Lemma F_60290 : fetch_word AsanUbsan.M.loaded_segments (0x60290 : word) = Some W_60290.
Proof. vm_refl. Qed.
Lemma D_60290 : decode_any W_60290 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_60294 : bv 32 := 0x01013403.
Lemma F_60294 : fetch_word AsanUbsan.M.loaded_segments (0x60294 : word) = Some W_60294.
Proof. vm_refl. Qed.
Lemma D_60294 : decode_any W_60294 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_60298 : bv 32 := 0x00813483.
Lemma F_60298 : fetch_word AsanUbsan.M.loaded_segments (0x60298 : word) = Some W_60298.
Proof. vm_refl. Qed.
Lemma D_60298 : decode_any W_60298 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6029c : bv 32 := 0x02010113.
Lemma F_6029c : fetch_word AsanUbsan.M.loaded_segments (0x6029c : word) = Some W_6029c.
Proof. vm_refl. Qed.
Lemma D_6029c : decode_any W_6029c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_602a0 : bv 32 := 0x00008067.
Lemma F_602a0 : fetch_word AsanUbsan.M.loaded_segments (0x602a0 : word) = Some W_602a0.
Proof. vm_refl. Qed.
Lemma D_602a0 : decode_any W_602a0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_602a4 : bv 32 := 0x4b4000ef.
Lemma F_602a4 : fetch_word AsanUbsan.M.loaded_segments (0x602a4 : word) = Some W_602a4.
Proof. vm_refl. Qed.
Lemma D_602a4 : decode_any W_602a4 = Some (Jal 1 1204, 4%Z).
Proof. vm_refl. Qed.

Definition W_602a8 : bv 32 := 0x03449493.
Lemma F_602a8 : fetch_word AsanUbsan.M.loaded_segments (0x602a8 : word) = Some W_602a8.
Proof. vm_refl. Qed.
Lemma D_602a8 : decode_any W_602a8 = Some (ShiftImm ALU_SLL 9 9 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_602ac : bv 32 := 0x0344d493.
Lemma F_602ac : fetch_word AsanUbsan.M.loaded_segments (0x602ac : word) = Some W_602ac.
Proof. vm_refl. Qed.
Lemma D_602ac : decode_any W_602ac = Some (ShiftImm ALU_SRL 9 9 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_602b0 : bv 32 := 0x00950633.
Lemma F_602b0 : fetch_word AsanUbsan.M.loaded_segments (0x602b0 : word) = Some W_602b0.
Proof. vm_refl. Qed.
Lemma D_602b0 : decode_any W_602b0 = Some (Op ALU_ADD 12 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_602b4 : bv 32 := 0x00064503.
Lemma F_602b4 : fetch_word AsanUbsan.M.loaded_segments (0x602b4 : word) = Some W_602b4.
Proof. vm_refl. Qed.
Lemma D_602b4 : decode_any W_602b4 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_602b8 : bv 32 := 0xfa051ee3.
Lemma F_602b8 : fetch_word AsanUbsan.M.loaded_segments (0x602b8 : word) = Some W_602b8.
Proof. vm_refl. Qed.
Lemma D_602b8 : decode_any W_602b8 = Some (Branch BC_NE 10 0 8124, 4%Z).
Proof. vm_refl. Qed.

Definition W_602bc : bv 32 := 0xfffbc517.
Lemma F_602bc : fetch_word AsanUbsan.M.loaded_segments (0x602bc : word) = Some W_602bc.
Proof. vm_refl. Qed.
Lemma D_602bc : decode_any W_602bc = Some (Auipc 10 1048508, 4%Z).
Proof. vm_refl. Qed.

Definition W_602c0 : bv 32 := 0xfffb3597.
Lemma F_602c0 : fetch_word AsanUbsan.M.loaded_segments (0x602c0 : word) = Some W_602c0.
Proof. vm_refl. Qed.
Lemma D_602c0 : decode_any W_602c0 = Some (Auipc 11 1048499, 4%Z).
Proof. vm_refl. Qed.

Definition W_602c4 : bv 32 := 0x1dd50513.
Lemma F_602c4 : fetch_word AsanUbsan.M.loaded_segments (0x602c4 : word) = Some W_602c4.
Proof. vm_refl. Qed.
Lemma D_602c4 : decode_any W_602c4 = Some (OpImm ALU_ADD 10 10 477, 4%Z).
Proof. vm_refl. Qed.

Definition W_602c8 : bv 32 := 0x83258613.
Lemma F_602c8 : fetch_word AsanUbsan.M.loaded_segments (0x602c8 : word) = Some W_602c8.
Proof. vm_refl. Qed.
Lemma D_602c8 : decode_any W_602c8 = Some (OpImm ALU_ADD 12 11 2098, 4%Z).
Proof. vm_refl. Qed.

Definition W_602cc : bv 32 := 0x02600593.
Lemma F_602cc : fetch_word AsanUbsan.M.loaded_segments (0x602cc : word) = Some W_602cc.
Proof. vm_refl. Qed.
Lemma D_602cc : decode_any W_602cc = Some (OpImm ALU_ADD 11 0 38, 4%Z).
Proof. vm_refl. Qed.

Definition W_602d0 : bv 32 := 0x00000693.
Lemma F_602d0 : fetch_word AsanUbsan.M.loaded_segments (0x602d0 : word) = Some W_602d0.
Proof. vm_refl. Qed.
Lemma D_602d0 : decode_any W_602d0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_602d4 : bv 32 := 0x00000713.
Lemma F_602d4 : fetch_word AsanUbsan.M.loaded_segments (0x602d4 : word) = Some W_602d4.
Proof. vm_refl. Qed.
Lemma D_602d4 : decode_any W_602d4 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_602d8 : bv 32 := 0x010190ef.
Lemma F_602d8 : fetch_word AsanUbsan.M.loaded_segments (0x602d8 : word) = Some W_602d8.
Proof. vm_refl. Qed.
Lemma D_602d8 : decode_any W_602d8 = Some (Jal 1 102416, 4%Z).
Proof. vm_refl. Qed.

Definition W_602dc : bv 32 := 0x81010113.
Lemma F_602dc : fetch_word AsanUbsan.M.loaded_segments (0x602dc : word) = Some W_602dc.
Proof. vm_refl. Qed.
Lemma D_602dc : decode_any W_602dc = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_602e0 : bv 32 := 0x7e113423.
Lemma F_602e0 : fetch_word AsanUbsan.M.loaded_segments (0x602e0 : word) = Some W_602e0.
Proof. vm_refl. Qed.
Lemma D_602e0 : decode_any W_602e0 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_602e4 : bv 32 := 0x7e813023.
Lemma F_602e4 : fetch_word AsanUbsan.M.loaded_segments (0x602e4 : word) = Some W_602e4.
Proof. vm_refl. Qed.
Lemma D_602e4 : decode_any W_602e4 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_602e8 : bv 32 := 0x7c913c23.
Lemma F_602e8 : fetch_word AsanUbsan.M.loaded_segments (0x602e8 : word) = Some W_602e8.
Proof. vm_refl. Qed.
Lemma D_602e8 : decode_any W_602e8 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_602ec : bv 32 := 0x7d213823.
Lemma F_602ec : fetch_word AsanUbsan.M.loaded_segments (0x602ec : word) = Some W_602ec.
Proof. vm_refl. Qed.
Lemma D_602ec : decode_any W_602ec = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_602f0 : bv 32 := 0x7d313423.
Lemma F_602f0 : fetch_word AsanUbsan.M.loaded_segments (0x602f0 : word) = Some W_602f0.
Proof. vm_refl. Qed.
Lemma D_602f0 : decode_any W_602f0 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_602f4 : bv 32 := 0x7d413023.
Lemma F_602f4 : fetch_word AsanUbsan.M.loaded_segments (0x602f4 : word) = Some W_602f4.
Proof. vm_refl. Qed.
Lemma D_602f4 : decode_any W_602f4 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_602f8 : bv 32 := 0x7b513c23.
Lemma F_602f8 : fetch_word AsanUbsan.M.loaded_segments (0x602f8 : word) = Some W_602f8.
Proof. vm_refl. Qed.
Lemma D_602f8 : decode_any W_602f8 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_602fc : bv 32 := 0x7b613823.
Lemma F_602fc : fetch_word AsanUbsan.M.loaded_segments (0x602fc : word) = Some W_602fc.
Proof. vm_refl. Qed.
Lemma D_602fc : decode_any W_602fc = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_60300 : bv 32 := 0x7f010413.
Lemma F_60300 : fetch_word AsanUbsan.M.loaded_segments (0x60300 : word) = Some W_60300.
Proof. vm_refl. Qed.
Lemma D_60300 : decode_any W_60300 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_60304 : bv 32 := 0xf9010113.
Lemma F_60304 : fetch_word AsanUbsan.M.loaded_segments (0x60304 : word) = Some W_60304.
Proof. vm_refl. Qed.
Lemma D_60304 : decode_any W_60304 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_60308 : bv 32 := 0x00008993.
Lemma F_60308 : fetch_word AsanUbsan.M.loaded_segments (0x60308 : word) = Some W_60308.
Proof. vm_refl. Qed.
Lemma D_60308 : decode_any W_60308 = Some (OpImm ALU_ADD 19 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6030c : bv 32 := 0x00058493.
Lemma F_6030c : fetch_word AsanUbsan.M.loaded_segments (0x6030c : word) = Some W_6030c.
Proof. vm_refl. Qed.
Lemma D_6030c : decode_any W_6030c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60310 : bv 32 := 0x00050913.
Lemma F_60310 : fetch_word AsanUbsan.M.loaded_segments (0x60310 : word) = Some W_60310.
Proof. vm_refl. Qed.
Lemma D_60310 : decode_any W_60310 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60314 : bv 32 := 0x751060ef.
Lemma F_60314 : fetch_word AsanUbsan.M.loaded_segments (0x60314 : word) = Some W_60314.
Proof. vm_refl. Qed.
Lemma D_60314 : decode_any W_60314 = Some (Jal 1 28496, 4%Z).
Proof. vm_refl. Qed.

Definition W_60318 : bv 32 := 0x04050463.
Lemma F_60318 : fetch_word AsanUbsan.M.loaded_segments (0x60318 : word) = Some W_60318.
Proof. vm_refl. Qed.
Lemma D_60318 : decode_any W_60318 = Some (Branch BC_EQ 10 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_6031c : bv 32 := 0x7c40b0ef.
Lemma F_6031c : fetch_word AsanUbsan.M.loaded_segments (0x6031c : word) = Some W_6031c.
Proof. vm_refl. Qed.
Lemma D_6031c : decode_any W_6031c = Some (Jal 1 47044, 4%Z).
Proof. vm_refl. Qed.

Definition W_60320 : bv 32 := 0x02f95593.
Lemma F_60320 : fetch_word AsanUbsan.M.loaded_segments (0x60320 : word) = Some W_60320.
Proof. vm_refl. Qed.
Lemma D_60320 : decode_any W_60320 = Some (ShiftImm ALU_SRL 11 18 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_60324 : bv 32 := 0x08059663.
Lemma F_60324 : fetch_word AsanUbsan.M.loaded_segments (0x60324 : word) = Some W_60324.
Proof. vm_refl. Qed.
Lemma D_60324 : decode_any W_60324 = Some (Branch BC_NE 11 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_60328 : bv 32 := 0x02095593.
Lemma F_60328 : fetch_word AsanUbsan.M.loaded_segments (0x60328 : word) = Some W_60328.
Proof. vm_refl. Qed.
Lemma D_60328 : decode_any W_60328 = Some (ShiftImm ALU_SRL 11 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6032c : bv 32 := 0x00359613.
Lemma F_6032c : fetch_word AsanUbsan.M.loaded_segments (0x6032c : word) = Some W_6032c.
Proof. vm_refl. Qed.
Lemma D_6032c : decode_any W_6032c = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_60330 : bv 32 := 0x00c50633.
Lemma F_60330 : fetch_word AsanUbsan.M.loaded_segments (0x60330 : word) = Some W_60330.
Proof. vm_refl. Qed.
Lemma D_60330 : decode_any W_60330 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_60334 : bv 32 := 0x00863683.
Lemma F_60334 : fetch_word AsanUbsan.M.loaded_segments (0x60334 : word) = Some W_60334.
Proof. vm_refl. Qed.
Lemma D_60334 : decode_any W_60334 = Some (Load SZ8 true 13 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_60338 : bv 32 := 0x0230000f.
Lemma F_60338 : fetch_word AsanUbsan.M.loaded_segments (0x60338 : word) = Some W_60338.
Proof. vm_refl. Qed.
Lemma D_60338 : decode_any W_60338 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6033c : bv 32 := 0x06068a63.
Lemma F_6033c : fetch_word AsanUbsan.M.loaded_segments (0x6033c : word) = Some W_6033c.
Proof. vm_refl. Qed.
Lemma D_6033c : decode_any W_6033c = Some (Branch BC_EQ 13 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_60340 : bv 32 := 0x00863603.
Lemma F_60340 : fetch_word AsanUbsan.M.loaded_segments (0x60340 : word) = Some W_60340.
Proof. vm_refl. Qed.
Lemma D_60340 : decode_any W_60340 = Some (Load SZ8 true 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_60344 : bv 32 := 0x01495a13.
Lemma F_60344 : fetch_word AsanUbsan.M.loaded_segments (0x60344 : word) = Some W_60344.
Proof. vm_refl. Qed.
Lemma D_60344 : decode_any W_60344 = Some (ShiftImm ALU_SRL 20 18 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_60348 : bv 32 := 0x04060663.
Lemma F_60348 : fetch_word AsanUbsan.M.loaded_segments (0x60348 : word) = Some W_60348.
Proof. vm_refl. Qed.
Lemma D_60348 : decode_any W_60348 = Some (Branch BC_EQ 12 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_6034c : bv 32 := 0x034a1a13.
Lemma F_6034c : fetch_word AsanUbsan.M.loaded_segments (0x6034c : word) = Some W_6034c.
Proof. vm_refl. Qed.
Lemma D_6034c : decode_any W_6034c = Some (ShiftImm ALU_SLL 20 20 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_60350 : bv 32 := 0x034a5513.
Lemma F_60350 : fetch_word AsanUbsan.M.loaded_segments (0x60350 : word) = Some W_60350.
Proof. vm_refl. Qed.
Lemma D_60350 : decode_any W_60350 = Some (ShiftImm ALU_SRL 10 20 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_60354 : bv 32 := 0x00a60533.
Lemma F_60354 : fetch_word AsanUbsan.M.loaded_segments (0x60354 : word) = Some W_60354.
Proof. vm_refl. Qed.
Lemma D_60354 : decode_any W_60354 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_60358 : bv 32 := 0x00054503.
Lemma F_60358 : fetch_word AsanUbsan.M.loaded_segments (0x60358 : word) = Some W_60358.
Proof. vm_refl. Qed.
Lemma D_60358 : decode_any W_60358 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6035c : bv 32 := 0x04050a63.
Lemma F_6035c : fetch_word AsanUbsan.M.loaded_segments (0x6035c : word) = Some W_6035c.
Proof. vm_refl. Qed.
Lemma D_6035c : decode_any W_6035c = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_60360 : bv 32 := 0x00090513.
Lemma F_60360 : fetch_word AsanUbsan.M.loaded_segments (0x60360 : word) = Some W_60360.
Proof. vm_refl. Qed.
Lemma D_60360 : decode_any W_60360 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60364 : bv 32 := 0x00048593.
Lemma F_60364 : fetch_word AsanUbsan.M.loaded_segments (0x60364 : word) = Some W_60364.
Proof. vm_refl. Qed.
Lemma D_60364 : decode_any W_60364 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60368 : bv 32 := 0x07010113.
Lemma F_60368 : fetch_word AsanUbsan.M.loaded_segments (0x60368 : word) = Some W_60368.
Proof. vm_refl. Qed.
Lemma D_60368 : decode_any W_60368 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_6036c : bv 32 := 0x7e813083.
Lemma F_6036c : fetch_word AsanUbsan.M.loaded_segments (0x6036c : word) = Some W_6036c.
Proof. vm_refl. Qed.
Lemma D_6036c : decode_any W_6036c = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_60370 : bv 32 := 0x7e013403.
Lemma F_60370 : fetch_word AsanUbsan.M.loaded_segments (0x60370 : word) = Some W_60370.
Proof. vm_refl. Qed.
Lemma D_60370 : decode_any W_60370 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_60374 : bv 32 := 0x7d813483.
Lemma F_60374 : fetch_word AsanUbsan.M.loaded_segments (0x60374 : word) = Some W_60374.
Proof. vm_refl. Qed.
Lemma D_60374 : decode_any W_60374 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_60378 : bv 32 := 0x7d013903.
Lemma F_60378 : fetch_word AsanUbsan.M.loaded_segments (0x60378 : word) = Some W_60378.
Proof. vm_refl. Qed.
Lemma D_60378 : decode_any W_60378 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_6037c : bv 32 := 0x7c813983.
Lemma F_6037c : fetch_word AsanUbsan.M.loaded_segments (0x6037c : word) = Some W_6037c.
Proof. vm_refl. Qed.
Lemma D_6037c : decode_any W_6037c = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_60380 : bv 32 := 0x7c013a03.
Lemma F_60380 : fetch_word AsanUbsan.M.loaded_segments (0x60380 : word) = Some W_60380.
Proof. vm_refl. Qed.
Lemma D_60380 : decode_any W_60380 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_60384 : bv 32 := 0x7b813a83.
Lemma F_60384 : fetch_word AsanUbsan.M.loaded_segments (0x60384 : word) = Some W_60384.
Proof. vm_refl. Qed.
Lemma D_60384 : decode_any W_60384 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_60388 : bv 32 := 0x7b013b03.
Lemma F_60388 : fetch_word AsanUbsan.M.loaded_segments (0x60388 : word) = Some W_60388.
Proof. vm_refl. Qed.
Lemma D_60388 : decode_any W_60388 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_6038c : bv 32 := 0x7f010113.
Lemma F_6038c : fetch_word AsanUbsan.M.loaded_segments (0x6038c : word) = Some W_6038c.
Proof. vm_refl. Qed.
Lemma D_6038c : decode_any W_6038c = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_60390 : bv 32 := 0x1240006f.
Lemma F_60390 : fetch_word AsanUbsan.M.loaded_segments (0x60390 : word) = Some W_60390.
Proof. vm_refl. Qed.
Lemma D_60390 : decode_any W_60390 = Some (Jal 0 292, 4%Z).
Proof. vm_refl. Qed.

Definition W_60394 : bv 32 := 0x3c4000ef.
Lemma F_60394 : fetch_word AsanUbsan.M.loaded_segments (0x60394 : word) = Some W_60394.
Proof. vm_refl. Qed.
Lemma D_60394 : decode_any W_60394 = Some (Jal 1 964, 4%Z).
Proof. vm_refl. Qed.

Definition W_60398 : bv 32 := 0x00050613.
Lemma F_60398 : fetch_word AsanUbsan.M.loaded_segments (0x60398 : word) = Some W_60398.
Proof. vm_refl. Qed.
Lemma D_60398 : decode_any W_60398 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6039c : bv 32 := 0x034a1a13.
Lemma F_6039c : fetch_word AsanUbsan.M.loaded_segments (0x6039c : word) = Some W_6039c.
Proof. vm_refl. Qed.
Lemma D_6039c : decode_any W_6039c = Some (ShiftImm ALU_SLL 20 20 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_603a0 : bv 32 := 0x034a5513.
Lemma F_603a0 : fetch_word AsanUbsan.M.loaded_segments (0x603a0 : word) = Some W_603a0.
Proof. vm_refl. Qed.
Lemma D_603a0 : decode_any W_603a0 = Some (ShiftImm ALU_SRL 10 20 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_603a4 : bv 32 := 0x00a60533.
Lemma F_603a4 : fetch_word AsanUbsan.M.loaded_segments (0x603a4 : word) = Some W_603a4.
Proof. vm_refl. Qed.
Lemma D_603a4 : decode_any W_603a4 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_603a8 : bv 32 := 0x00054503.
Lemma F_603a8 : fetch_word AsanUbsan.M.loaded_segments (0x603a8 : word) = Some W_603a8.
Proof. vm_refl. Qed.
Lemma D_603a8 : decode_any W_603a8 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_603ac : bv 32 := 0xfa051ae3.
Lemma F_603ac : fetch_word AsanUbsan.M.loaded_segments (0x603ac : word) = Some W_603ac.
Proof. vm_refl. Qed.
Lemma D_603ac : decode_any W_603ac = Some (Branch BC_NE 10 0 8116, 4%Z).
Proof. vm_refl. Qed.

Definition W_603b0 : bv 32 := 0x80040a93.
Lemma F_603b0 : fetch_word AsanUbsan.M.loaded_segments (0x603b0 : word) = Some W_603b0.
Proof. vm_refl. Qed.
Lemma D_603b0 : decode_any W_603b0 = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_603b4 : bv 32 := 0xfa8a8a93.
Lemma F_603b4 : fetch_word AsanUbsan.M.loaded_segments (0x603b4 : word) = Some W_603b4.
Proof. vm_refl. Qed.
Lemma D_603b4 : decode_any W_603b4 = Some (OpImm ALU_ADD 21 21 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_603b8 : bv 32 := 0x80040513.
Lemma F_603b8 : fetch_word AsanUbsan.M.loaded_segments (0x603b8 : word) = Some W_603b8.
Proof. vm_refl. Qed.
Lemma D_603b8 : decode_any W_603b8 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_603bc : bv 32 := 0xfb850513.
Lemma F_603bc : fetch_word AsanUbsan.M.loaded_segments (0x603bc : word) = Some W_603bc.
Proof. vm_refl. Qed.
Lemma D_603bc : decode_any W_603bc = Some (OpImm ALU_ADD 10 10 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_603c0 : bv 32 := 0x80040593.
Lemma F_603c0 : fetch_word AsanUbsan.M.loaded_segments (0x603c0 : word) = Some W_603c0.
Proof. vm_refl. Qed.
Lemma D_603c0 : decode_any W_603c0 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_603c4 : bv 32 := 0xfa858593.
Lemma F_603c4 : fetch_word AsanUbsan.M.loaded_segments (0x603c4 : word) = Some W_603c4.
Proof. vm_refl. Qed.
Lemma D_603c4 : decode_any W_603c4 = Some (OpImm ALU_ADD 11 11 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_603c8 : bv 32 := 0x7ff58b13.
Lemma F_603c8 : fetch_word AsanUbsan.M.loaded_segments (0x603c8 : word) = Some W_603c8.
Proof. vm_refl. Qed.
Lemma D_603c8 : decode_any W_603c8 = Some (OpImm ALU_ADD 22 11 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_603cc : bv 32 := 0x000b34a3.
Lemma F_603cc : fetch_word AsanUbsan.M.loaded_segments (0x603cc : word) = Some W_603cc.
Proof. vm_refl. Qed.
Lemma D_603cc : decode_any W_603cc = Some (Store SZ8 22 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_603d0 : bv 32 := 0x00aab023.
Lemma F_603d0 : fetch_word AsanUbsan.M.loaded_segments (0x603d0 : word) = Some W_603d0.
Proof. vm_refl. Qed.
Lemma D_603d0 : decode_any W_603d0 = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_603d4 : bv 32 := 0x000ab423.
Lemma F_603d4 : fetch_word AsanUbsan.M.loaded_segments (0x603d4 : word) = Some W_603d4.
Proof. vm_refl. Qed.
Lemma D_603d4 : decode_any W_603d4 = Some (Store SZ8 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_603d8 : bv 32 := 0x415070ef.
Lemma F_603d8 : fetch_word AsanUbsan.M.loaded_segments (0x603d8 : word) = Some W_603d8.
Proof. vm_refl. Qed.
Lemma D_603d8 : decode_any W_603d8 = Some (Jal 1 31764, 4%Z).
Proof. vm_refl. Qed.

Definition W_603dc : bv 32 := 0x00200593.
Lemma F_603dc : fetch_word AsanUbsan.M.loaded_segments (0x603dc : word) = Some W_603dc.
Proof. vm_refl. Qed.
Lemma D_603dc : decode_any W_603dc = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_603e0 : bv 32 := 0x02a5ea63.
Lemma F_603e0 : fetch_word AsanUbsan.M.loaded_segments (0x603e0 : word) = Some W_603e0.
Proof. vm_refl. Qed.
Lemma D_603e0 : decode_any W_603e0 = Some (Branch BC_LTU 11 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_603e4 : bv 32 := 0x409070ef.
Lemma F_603e4 : fetch_word AsanUbsan.M.loaded_segments (0x603e4 : word) = Some W_603e4.
Proof. vm_refl. Qed.
Lemma D_603e4 : decode_any W_603e4 = Some (Jal 1 31752, 4%Z).
Proof. vm_refl. Qed.

Definition W_603e8 : bv 32 := 0x00aaa423.
Lemma F_603e8 : fetch_word AsanUbsan.M.loaded_segments (0x603e8 : word) = Some W_603e8.
Proof. vm_refl. Qed.
Lemma D_603e8 : decode_any W_603e8 = Some (Store SZ4 21 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_603ec : bv 32 := 0x401070ef.
Lemma F_603ec : fetch_word AsanUbsan.M.loaded_segments (0x603ec : word) = Some W_603ec.
Proof. vm_refl. Qed.
Lemma D_603ec : decode_any W_603ec = Some (Jal 1 31744, 4%Z).
Proof. vm_refl. Qed.

Definition W_603f0 : bv 32 := 0x08050263.
Lemma F_603f0 : fetch_word AsanUbsan.M.loaded_segments (0x603f0 : word) = Some W_603f0.
Proof. vm_refl. Qed.
Lemma D_603f0 : decode_any W_603f0 = Some (Branch BC_EQ 10 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_603f4 : bv 32 := 0x008b34a3.
Lemma F_603f4 : fetch_word AsanUbsan.M.loaded_segments (0x603f4 : word) = Some W_603f4.
Proof. vm_refl. Qed.
Lemma D_603f4 : decode_any W_603f4 = Some (Store SZ8 22 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_603f8 : bv 32 := 0x6b4200ef.
Lemma F_603f8 : fetch_word AsanUbsan.M.loaded_segments (0x603f8 : word) = Some W_603f8.
Proof. vm_refl. Qed.
Lemma D_603f8 : decode_any W_603f8 = Some (Jal 1 132788, 4%Z).
Proof. vm_refl. Qed.

Definition W_603fc : bv 32 := 0x00aab823.
Lemma F_603fc : fetch_word AsanUbsan.M.loaded_segments (0x603fc : word) = Some W_603fc.
Proof. vm_refl. Qed.
Lemma D_603fc : decode_any W_603fc = Some (Store SZ8 21 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_60400 : bv 32 := 0x3ed070ef.
Lemma F_60400 : fetch_word AsanUbsan.M.loaded_segments (0x60400 : word) = Some W_60400.
Proof. vm_refl. Qed.
Lemma D_60400 : decode_any W_60400 = Some (Jal 1 31724, 4%Z).
Proof. vm_refl. Qed.

Definition W_60404 : bv 32 := 0x00200593.
Lemma F_60404 : fetch_word AsanUbsan.M.loaded_segments (0x60404 : word) = Some W_60404.
Proof. vm_refl. Qed.
Lemma D_60404 : decode_any W_60404 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_60408 : bv 32 := 0x06b56663.
Lemma F_60408 : fetch_word AsanUbsan.M.loaded_segments (0x60408 : word) = Some W_60408.
Proof. vm_refl. Qed.
Lemma D_60408 : decode_any W_60408 = Some (Branch BC_LTU 10 11 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_6040c : bv 32 := 0x013abc23.
Lemma F_6040c : fetch_word AsanUbsan.M.loaded_segments (0x6040c : word) = Some W_6040c.
Proof. vm_refl. Qed.
Lemma D_6040c : decode_any W_6040c = Some (Store SZ8 21 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_60410 : bv 32 := 0x0640006f.
Lemma F_60410 : fetch_word AsanUbsan.M.loaded_segments (0x60410 : word) = Some W_60410.
Proof. vm_refl. Qed.
Lemma D_60410 : decode_any W_60410 = Some (Jal 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_60414 : bv 32 := 0x698200ef.
Lemma F_60414 : fetch_word AsanUbsan.M.loaded_segments (0x60414 : word) = Some W_60414.
Proof. vm_refl. Qed.
Lemma D_60414 : decode_any W_60414 = Some (Jal 1 132760, 4%Z).
Proof. vm_refl. Qed.

Definition W_60418 : bv 32 := 0x00076597.
Lemma F_60418 : fetch_word AsanUbsan.M.loaded_segments (0x60418 : word) = Some W_60418.
Proof. vm_refl. Qed.
Lemma D_60418 : decode_any W_60418 = Some (Auipc 11 118, 4%Z).
Proof. vm_refl. Qed.

Definition W_6041c : bv 32 := 0x0a05b583.
Lemma F_6041c : fetch_word AsanUbsan.M.loaded_segments (0x6041c : word) = Some W_6041c.
Proof. vm_refl. Qed.
Lemma D_6041c : decode_any W_6041c = Some (Load SZ8 true 11 11 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_60420 : bv 32 := 0x0225ca03.
Lemma F_60420 : fetch_word AsanUbsan.M.loaded_segments (0x60420 : word) = Some W_60420.
Proof. vm_refl. Qed.
Lemma D_60420 : decode_any W_60420 = Some (Load SZ1 false 20 11 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_60424 : bv 32 := 0x00050993.
Lemma F_60424 : fetch_word AsanUbsan.M.loaded_segments (0x60424 : word) = Some W_60424.
Proof. vm_refl. Qed.
Lemma D_60424 : decode_any W_60424 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60428 : bv 32 := 0x3c5070ef.
Lemma F_60428 : fetch_word AsanUbsan.M.loaded_segments (0x60428 : word) = Some W_60428.
Proof. vm_refl. Qed.
Lemma D_60428 : decode_any W_60428 = Some (Jal 1 31684, 4%Z).
Proof. vm_refl. Qed.

Definition W_6042c : bv 32 := 0x00050793.
Lemma F_6042c : fetch_word AsanUbsan.M.loaded_segments (0x6042c : word) = Some W_6042c.
Proof. vm_refl. Qed.
Lemma D_6042c : decode_any W_6042c = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60430 : bv 32 := 0x00153513.
Lemma F_60430 : fetch_word AsanUbsan.M.loaded_segments (0x60430 : word) = Some W_60430.
Proof. vm_refl. Qed.
Lemma D_60430 : decode_any W_60430 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_60434 : bv 32 := 0xfff50513.
Lemma F_60434 : fetch_word AsanUbsan.M.loaded_segments (0x60434 : word) = Some W_60434.
Proof. vm_refl. Qed.
Lemma D_60434 : decode_any W_60434 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_60438 : bv 32 := 0x008575b3.
Lemma F_60438 : fetch_word AsanUbsan.M.loaded_segments (0x60438 : word) = Some W_60438.
Proof. vm_refl. Qed.
Lemma D_60438 : decode_any W_60438 = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6043c : bv 32 := 0x00100513.
Lemma F_6043c : fetch_word AsanUbsan.M.loaded_segments (0x6043c : word) = Some W_6043c.
Proof. vm_refl. Qed.
Lemma D_6043c : decode_any W_6043c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_60440 : bv 32 := 0x00bb34a3.
Lemma F_60440 : fetch_word AsanUbsan.M.loaded_segments (0x60440 : word) = Some W_60440.
Proof. vm_refl. Qed.
Lemma D_60440 : decode_any W_60440 = Some (Store SZ8 22 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_60444 : bv 32 := 0x00f56a63.
Lemma F_60444 : fetch_word AsanUbsan.M.loaded_segments (0x60444 : word) = Some W_60444.
Proof. vm_refl. Qed.
Lemma D_60444 : decode_any W_60444 = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_60448 : bv 32 := 0x00a79463.
Lemma F_60448 : fetch_word AsanUbsan.M.loaded_segments (0x60448 : word) = Some W_60448.
Proof. vm_refl. Qed.
Lemma D_60448 : decode_any W_60448 = Some (Branch BC_NE 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6044c : bv 32 := 0x013ab823.
Lemma F_6044c : fetch_word AsanUbsan.M.loaded_segments (0x6044c : word) = Some W_6044c.
Proof. vm_refl. Qed.
Lemma D_6044c : decode_any W_6044c = Some (Store SZ8 21 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_60450 : bv 32 := 0x00faa423.
Lemma F_60450 : fetch_word AsanUbsan.M.loaded_segments (0x60450 : word) = Some W_60450.
Proof. vm_refl. Qed.
Lemma D_60450 : decode_any W_60450 = Some (Store SZ4 21 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_60454 : bv 32 := 0x0200006f.
Lemma F_60454 : fetch_word AsanUbsan.M.loaded_segments (0x60454 : word) = Some W_60454.
Proof. vm_refl. Qed.
Lemma D_60454 : decode_any W_60454 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_60458 : bv 32 := 0x80040513.
Lemma F_60458 : fetch_word AsanUbsan.M.loaded_segments (0x60458 : word) = Some W_60458.
Proof. vm_refl. Qed.
Lemma D_60458 : decode_any W_60458 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_6045c : bv 32 := 0xfa850513.
Lemma F_6045c : fetch_word AsanUbsan.M.loaded_segments (0x6045c : word) = Some W_6045c.
Proof. vm_refl. Qed.
Lemma D_6045c : decode_any W_6045c = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_60460 : bv 32 := 0x00098593.
Lemma F_60460 : fetch_word AsanUbsan.M.loaded_segments (0x60460 : word) = Some W_60460.
Proof. vm_refl. Qed.
Lemma D_60460 : decode_any W_60460 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60464 : bv 32 := 0x00040613.
Lemma F_60464 : fetch_word AsanUbsan.M.loaded_segments (0x60464 : word) = Some W_60464.
Proof. vm_refl. Qed.
Lemma D_60464 : decode_any W_60464 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60468 : bv 32 := 0x00000693.
Lemma F_60468 : fetch_word AsanUbsan.M.loaded_segments (0x60468 : word) = Some W_60468.
Proof. vm_refl. Qed.
Lemma D_60468 : decode_any W_60468 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6046c : bv 32 := 0x000a0713.
Lemma F_6046c : fetch_word AsanUbsan.M.loaded_segments (0x6046c : word) = Some W_6046c.
Proof. vm_refl. Qed.
Lemma D_6046c : decode_any W_6046c = Some (OpImm ALU_ADD 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60470 : bv 32 := 0x38d070ef.
Lemma F_60470 : fetch_word AsanUbsan.M.loaded_segments (0x60470 : word) = Some W_60470.
Proof. vm_refl. Qed.
Lemma D_60470 : decode_any W_60470 = Some (Jal 1 31628, 4%Z).
Proof. vm_refl. Qed.

Definition W_60474 : bv 32 := 0x80040613.
Lemma F_60474 : fetch_word AsanUbsan.M.loaded_segments (0x60474 : word) = Some W_60474.
Proof. vm_refl. Qed.
Lemma D_60474 : decode_any W_60474 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_60478 : bv 32 := 0xfa860613.
Lemma F_60478 : fetch_word AsanUbsan.M.loaded_segments (0x60478 : word) = Some W_60478.
Proof. vm_refl. Qed.
Lemma D_60478 : decode_any W_60478 = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_6047c : bv 32 := 0x00090513.
Lemma F_6047c : fetch_word AsanUbsan.M.loaded_segments (0x6047c : word) = Some W_6047c.
Proof. vm_refl. Qed.
Lemma D_6047c : decode_any W_6047c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60480 : bv 32 := 0x00048593.
Lemma F_60480 : fetch_word AsanUbsan.M.loaded_segments (0x60480 : word) = Some W_60480.
Proof. vm_refl. Qed.
Lemma D_60480 : decode_any W_60480 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60484 : bv 32 := 0xaf5dd0ef.
Lemma F_60484 : fetch_word AsanUbsan.M.loaded_segments (0x60484 : word) = Some W_60484.
Proof. vm_refl. Qed.
Lemma D_60484 : decode_any W_60484 = Some (Jal 1 1956596, 4%Z).
Proof. vm_refl. Qed.

Definition W_60488 : bv 32 := 0x07010113.
Lemma F_60488 : fetch_word AsanUbsan.M.loaded_segments (0x60488 : word) = Some W_60488.
Proof. vm_refl. Qed.
Lemma D_60488 : decode_any W_60488 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_6048c : bv 32 := 0x7e813083.
Lemma F_6048c : fetch_word AsanUbsan.M.loaded_segments (0x6048c : word) = Some W_6048c.
Proof. vm_refl. Qed.
Lemma D_6048c : decode_any W_6048c = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_60490 : bv 32 := 0x7e013403.
Lemma F_60490 : fetch_word AsanUbsan.M.loaded_segments (0x60490 : word) = Some W_60490.
Proof. vm_refl. Qed.
Lemma D_60490 : decode_any W_60490 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_60494 : bv 32 := 0x7d813483.
Lemma F_60494 : fetch_word AsanUbsan.M.loaded_segments (0x60494 : word) = Some W_60494.
Proof. vm_refl. Qed.
Lemma D_60494 : decode_any W_60494 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_60498 : bv 32 := 0x7d013903.
Lemma F_60498 : fetch_word AsanUbsan.M.loaded_segments (0x60498 : word) = Some W_60498.
Proof. vm_refl. Qed.
Lemma D_60498 : decode_any W_60498 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_6049c : bv 32 := 0x7c813983.
Lemma F_6049c : fetch_word AsanUbsan.M.loaded_segments (0x6049c : word) = Some W_6049c.
Proof. vm_refl. Qed.
Lemma D_6049c : decode_any W_6049c = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_604a0 : bv 32 := 0x7c013a03.
Lemma F_604a0 : fetch_word AsanUbsan.M.loaded_segments (0x604a0 : word) = Some W_604a0.
Proof. vm_refl. Qed.
Lemma D_604a0 : decode_any W_604a0 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_604a4 : bv 32 := 0x7b813a83.
Lemma F_604a4 : fetch_word AsanUbsan.M.loaded_segments (0x604a4 : word) = Some W_604a4.
Proof. vm_refl. Qed.
Lemma D_604a4 : decode_any W_604a4 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_604a8 : bv 32 := 0x7b013b03.
Lemma F_604a8 : fetch_word AsanUbsan.M.loaded_segments (0x604a8 : word) = Some W_604a8.
Proof. vm_refl. Qed.
Lemma D_604a8 : decode_any W_604a8 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_604ac : bv 32 := 0x7f010113.
Lemma F_604ac : fetch_word AsanUbsan.M.loaded_segments (0x604ac : word) = Some W_604ac.
Proof. vm_refl. Qed.
Lemma D_604ac : decode_any W_604ac = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_604b0 : bv 32 := 0x00008067.
Lemma F_604b0 : fetch_word AsanUbsan.M.loaded_segments (0x604b0 : word) = Some W_604b0.
Proof. vm_refl. Qed.
Lemma D_604b0 : decode_any W_604b0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_604b4 : bv 32 := 0xfd010113.
Lemma F_604b4 : fetch_word AsanUbsan.M.loaded_segments (0x604b4 : word) = Some W_604b4.
Proof. vm_refl. Qed.
Lemma D_604b4 : decode_any W_604b4 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_604b8 : bv 32 := 0x02113423.
Lemma F_604b8 : fetch_word AsanUbsan.M.loaded_segments (0x604b8 : word) = Some W_604b8.
Proof. vm_refl. Qed.
Lemma D_604b8 : decode_any W_604b8 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_604bc : bv 32 := 0x02813023.
Lemma F_604bc : fetch_word AsanUbsan.M.loaded_segments (0x604bc : word) = Some W_604bc.
Proof. vm_refl. Qed.
Lemma D_604bc : decode_any W_604bc = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_604c0 : bv 32 := 0x00913c23.
Lemma F_604c0 : fetch_word AsanUbsan.M.loaded_segments (0x604c0 : word) = Some W_604c0.
Proof. vm_refl. Qed.
Lemma D_604c0 : decode_any W_604c0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_604c4 : bv 32 := 0x01213823.
Lemma F_604c4 : fetch_word AsanUbsan.M.loaded_segments (0x604c4 : word) = Some W_604c4.
Proof. vm_refl. Qed.
Lemma D_604c4 : decode_any W_604c4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_604c8 : bv 32 := 0x01313423.
Lemma F_604c8 : fetch_word AsanUbsan.M.loaded_segments (0x604c8 : word) = Some W_604c8.
Proof. vm_refl. Qed.
Lemma D_604c8 : decode_any W_604c8 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_604cc : bv 32 := 0x00058493.
Lemma F_604cc : fetch_word AsanUbsan.M.loaded_segments (0x604cc : word) = Some W_604cc.
Proof. vm_refl. Qed.
Lemma D_604cc : decode_any W_604cc = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_604d0 : bv 32 := 0x0a050a63.
Lemma F_604d0 : fetch_word AsanUbsan.M.loaded_segments (0x604d0 : word) = Some W_604d0.
Proof. vm_refl. Qed.
Lemma D_604d0 : decode_any W_604d0 = Some (Branch BC_EQ 10 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_604d4 : bv 32 := 0x00050413.
Lemma F_604d4 : fetch_word AsanUbsan.M.loaded_segments (0x604d4 : word) = Some W_604d4.
Proof. vm_refl. Qed.
Lemma D_604d4 : decode_any W_604d4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_604d8 : bv 32 := 0x6080b0ef.
Lemma F_604d8 : fetch_word AsanUbsan.M.loaded_segments (0x604d8 : word) = Some W_604d8.
Proof. vm_refl. Qed.
Lemma D_604d8 : decode_any W_604d8 = Some (Jal 1 46600, 4%Z).
Proof. vm_refl. Qed.

Definition W_604dc : bv 32 := 0x02f45593.
Lemma F_604dc : fetch_word AsanUbsan.M.loaded_segments (0x604dc : word) = Some W_604dc.
Proof. vm_refl. Qed.
Lemma D_604dc : decode_any W_604dc = Some (ShiftImm ALU_SRL 11 8 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_604e0 : bv 32 := 0x12059063.
Lemma F_604e0 : fetch_word AsanUbsan.M.loaded_segments (0x604e0 : word) = Some W_604e0.
Proof. vm_refl. Qed.
Lemma D_604e0 : decode_any W_604e0 = Some (Branch BC_NE 11 0 288, 4%Z).
Proof. vm_refl. Qed.

Definition W_604e4 : bv 32 := 0x02045593.
Lemma F_604e4 : fetch_word AsanUbsan.M.loaded_segments (0x604e4 : word) = Some W_604e4.
Proof. vm_refl. Qed.
Lemma D_604e4 : decode_any W_604e4 = Some (ShiftImm ALU_SRL 11 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_604e8 : bv 32 := 0x00359613.
Lemma F_604e8 : fetch_word AsanUbsan.M.loaded_segments (0x604e8 : word) = Some W_604e8.
Proof. vm_refl. Qed.
Lemma D_604e8 : decode_any W_604e8 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_604ec : bv 32 := 0x00c50633.
Lemma F_604ec : fetch_word AsanUbsan.M.loaded_segments (0x604ec : word) = Some W_604ec.
Proof. vm_refl. Qed.
Lemma D_604ec : decode_any W_604ec = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_604f0 : bv 32 := 0x00863683.
Lemma F_604f0 : fetch_word AsanUbsan.M.loaded_segments (0x604f0 : word) = Some W_604f0.
Proof. vm_refl. Qed.
Lemma D_604f0 : decode_any W_604f0 = Some (Load SZ8 true 13 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_604f4 : bv 32 := 0x0230000f.
Lemma F_604f4 : fetch_word AsanUbsan.M.loaded_segments (0x604f4 : word) = Some W_604f4.
Proof. vm_refl. Qed.
Lemma D_604f4 : decode_any W_604f4 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_604f8 : bv 32 := 0x10068463.
Lemma F_604f8 : fetch_word AsanUbsan.M.loaded_segments (0x604f8 : word) = Some W_604f8.
Proof. vm_refl. Qed.
Lemma D_604f8 : decode_any W_604f8 = Some (Branch BC_EQ 13 0 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_604fc : bv 32 := 0x00863603.
Lemma F_604fc : fetch_word AsanUbsan.M.loaded_segments (0x604fc : word) = Some W_604fc.
Proof. vm_refl. Qed.
Lemma D_604fc : decode_any W_604fc = Some (Load SZ8 true 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_60500 : bv 32 := 0x01445913.
Lemma F_60500 : fetch_word AsanUbsan.M.loaded_segments (0x60500 : word) = Some W_60500.
Proof. vm_refl. Qed.
Lemma D_60500 : decode_any W_60500 = Some (ShiftImm ALU_SRL 18 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_60504 : bv 32 := 0x0e060063.
Lemma F_60504 : fetch_word AsanUbsan.M.loaded_segments (0x60504 : word) = Some W_60504.
Proof. vm_refl. Qed.
Lemma D_60504 : decode_any W_60504 = Some (Branch BC_EQ 12 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_60508 : bv 32 := 0x03491913.
Lemma F_60508 : fetch_word AsanUbsan.M.loaded_segments (0x60508 : word) = Some W_60508.
Proof. vm_refl. Qed.
Lemma D_60508 : decode_any W_60508 = Some (ShiftImm ALU_SLL 18 18 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_6050c : bv 32 := 0x03495513.
Lemma F_6050c : fetch_word AsanUbsan.M.loaded_segments (0x6050c : word) = Some W_6050c.
Proof. vm_refl. Qed.
Lemma D_6050c : decode_any W_6050c = Some (ShiftImm ALU_SRL 10 18 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_60510 : bv 32 := 0x00a60533.
Lemma F_60510 : fetch_word AsanUbsan.M.loaded_segments (0x60510 : word) = Some W_60510.
Proof. vm_refl. Qed.
Lemma D_60510 : decode_any W_60510 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_60514 : bv 32 := 0x00054503.
Lemma F_60514 : fetch_word AsanUbsan.M.loaded_segments (0x60514 : word) = Some W_60514.
Proof. vm_refl. Qed.
Lemma D_60514 : decode_any W_60514 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60518 : bv 32 := 0x0e050463.
Lemma F_60518 : fetch_word AsanUbsan.M.loaded_segments (0x60518 : word) = Some W_60518.
Proof. vm_refl. Qed.
Lemma D_60518 : decode_any W_60518 = Some (Branch BC_EQ 10 0 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_6051c : bv 32 := 0x5c40b0ef.
Lemma F_6051c : fetch_word AsanUbsan.M.loaded_segments (0x6051c : word) = Some W_6051c.
Proof. vm_refl. Qed.
Lemma D_6051c : decode_any W_6051c = Some (Jal 1 46532, 4%Z).
Proof. vm_refl. Qed.

Definition W_60520 : bv 32 := 0x00040593.
Lemma F_60520 : fetch_word AsanUbsan.M.loaded_segments (0x60520 : word) = Some W_60520.
Proof. vm_refl. Qed.
Lemma D_60520 : decode_any W_60520 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60524 : bv 32 := 0x334000ef.
Lemma F_60524 : fetch_word AsanUbsan.M.loaded_segments (0x60524 : word) = Some W_60524.
Proof. vm_refl. Qed.
Lemma D_60524 : decode_any W_60524 = Some (Jal 1 820, 4%Z).
Proof. vm_refl. Qed.

Definition W_60528 : bv 32 := 0x00050993.
Lemma F_60528 : fetch_word AsanUbsan.M.loaded_segments (0x60528 : word) = Some W_60528.
Proof. vm_refl. Qed.
Lemma D_60528 : decode_any W_60528 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6052c : bv 32 := 0x06048e63.
Lemma F_6052c : fetch_word AsanUbsan.M.loaded_segments (0x6052c : word) = Some W_6052c.
Proof. vm_refl. Qed.
Lemma D_6052c : decode_any W_6052c = Some (Branch BC_EQ 9 0 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_60530 : bv 32 := 0x00800593.
Lemma F_60530 : fetch_word AsanUbsan.M.loaded_segments (0x60530 : word) = Some W_60530.
Proof. vm_refl. Qed.
Lemma D_60530 : decode_any W_60530 = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_60534 : bv 32 := 0x00048513.
Lemma F_60534 : fetch_word AsanUbsan.M.loaded_segments (0x60534 : word) = Some W_60534.
Proof. vm_refl. Qed.
Lemma D_60534 : decode_any W_60534 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60538 : bv 32 := 0xcd9ff0ef.
Lemma F_60538 : fetch_word AsanUbsan.M.loaded_segments (0x60538 : word) = Some W_60538.
Proof. vm_refl. Qed.
Lemma D_60538 : decode_any W_60538 = Some (Jal 1 2096344, 4%Z).
Proof. vm_refl. Qed.

Definition W_6053c : bv 32 := 0x00050913.
Lemma F_6053c : fetch_word AsanUbsan.M.loaded_segments (0x6053c : word) = Some W_6053c.
Proof. vm_refl. Qed.
Lemma D_6053c : decode_any W_6053c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60540 : bv 32 := 0x00050e63.
Lemma F_60540 : fetch_word AsanUbsan.M.loaded_segments (0x60540 : word) = Some W_60540.
Proof. vm_refl. Qed.
Lemma D_60540 : decode_any W_60540 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_60544 : bv 32 := 0x0134e463.
Lemma F_60544 : fetch_word AsanUbsan.M.loaded_segments (0x60544 : word) = Some W_60544.
Proof. vm_refl. Qed.
Lemma D_60544 : decode_any W_60544 = Some (Branch BC_LTU 9 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_60548 : bv 32 := 0x00098493.
Lemma F_60548 : fetch_word AsanUbsan.M.loaded_segments (0x60548 : word) = Some W_60548.
Proof. vm_refl. Qed.
Lemma D_60548 : decode_any W_60548 = Some (OpImm ALU_ADD 9 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6054c : bv 32 := 0x00090513.
Lemma F_6054c : fetch_word AsanUbsan.M.loaded_segments (0x6054c : word) = Some W_6054c.
Proof. vm_refl. Qed.
Lemma D_6054c : decode_any W_6054c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60550 : bv 32 := 0x00040593.
Lemma F_60550 : fetch_word AsanUbsan.M.loaded_segments (0x60550 : word) = Some W_60550.
Proof. vm_refl. Qed.
Lemma D_60550 : decode_any W_60550 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60554 : bv 32 := 0x00048613.
Lemma F_60554 : fetch_word AsanUbsan.M.loaded_segments (0x60554 : word) = Some W_60554.
Proof. vm_refl. Qed.
Lemma D_60554 : decode_any W_60554 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60558 : bv 32 := 0x00c110ef.
Lemma F_60558 : fetch_word AsanUbsan.M.loaded_segments (0x60558 : word) = Some W_60558.
Proof. vm_refl. Qed.
Lemma D_60558 : decode_any W_60558 = Some (Jal 1 69644, 4%Z).
Proof. vm_refl. Qed.

Definition W_6055c : bv 32 := 0x5840b0ef.
Lemma F_6055c : fetch_word AsanUbsan.M.loaded_segments (0x6055c : word) = Some W_6055c.
Proof. vm_refl. Qed.
Lemma D_6055c : decode_any W_6055c = Some (Jal 1 46468, 4%Z).
Proof. vm_refl. Qed.

Definition W_60560 : bv 32 := 0x00040593.
Lemma F_60560 : fetch_word AsanUbsan.M.loaded_segments (0x60560 : word) = Some W_60560.
Proof. vm_refl. Qed.
Lemma D_60560 : decode_any W_60560 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60564 : bv 32 := 0x2f4000ef.
Lemma F_60564 : fetch_word AsanUbsan.M.loaded_segments (0x60564 : word) = Some W_60564.
Proof. vm_refl. Qed.
Lemma D_60564 : decode_any W_60564 = Some (Jal 1 756, 4%Z).
Proof. vm_refl. Qed.

Definition W_60568 : bv 32 := 0x00050593.
Lemma F_60568 : fetch_word AsanUbsan.M.loaded_segments (0x60568 : word) = Some W_60568.
Proof. vm_refl. Qed.
Lemma D_60568 : decode_any W_60568 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6056c : bv 32 := 0x00040513.
Lemma F_6056c : fetch_word AsanUbsan.M.loaded_segments (0x6056c : word) = Some W_6056c.
Proof. vm_refl. Qed.
Lemma D_6056c : decode_any W_6056c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60570 : bv 32 := 0x06c2a0ef.
Lemma F_60570 : fetch_word AsanUbsan.M.loaded_segments (0x60570 : word) = Some W_60570.
Proof. vm_refl. Qed.
Lemma D_60570 : decode_any W_60570 = Some (Jal 1 172140, 4%Z).
Proof. vm_refl. Qed.

Definition W_60574 : bv 32 := 0x00040513.
Lemma F_60574 : fetch_word AsanUbsan.M.loaded_segments (0x60574 : word) = Some W_60574.
Proof. vm_refl. Qed.
Lemma D_60574 : decode_any W_60574 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60578 : bv 32 := 0x00000593.
Lemma F_60578 : fetch_word AsanUbsan.M.loaded_segments (0x60578 : word) = Some W_60578.
Proof. vm_refl. Qed.
Lemma D_60578 : decode_any W_60578 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6057c : bv 32 := 0x7e00b0ef.
Lemma F_6057c : fetch_word AsanUbsan.M.loaded_segments (0x6057c : word) = Some W_6057c.
Proof. vm_refl. Qed.
Lemma D_6057c : decode_any W_6057c = Some (Jal 1 47072, 4%Z).
Proof. vm_refl. Qed.

Definition W_60580 : bv 32 := 0x0440006f.
Lemma F_60580 : fetch_word AsanUbsan.M.loaded_segments (0x60580 : word) = Some W_60580.
Proof. vm_refl. Qed.
Lemma D_60580 : decode_any W_60580 = Some (Jal 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_60584 : bv 32 := 0x00800593.
Lemma F_60584 : fetch_word AsanUbsan.M.loaded_segments (0x60584 : word) = Some W_60584.
Proof. vm_refl. Qed.
Lemma D_60584 : decode_any W_60584 = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_60588 : bv 32 := 0x00048513.
Lemma F_60588 : fetch_word AsanUbsan.M.loaded_segments (0x60588 : word) = Some W_60588.
Proof. vm_refl. Qed.
Lemma D_60588 : decode_any W_60588 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6058c : bv 32 := 0x02813083.
Lemma F_6058c : fetch_word AsanUbsan.M.loaded_segments (0x6058c : word) = Some W_6058c.
Proof. vm_refl. Qed.
Lemma D_6058c : decode_any W_6058c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_60590 : bv 32 := 0x02013403.
Lemma F_60590 : fetch_word AsanUbsan.M.loaded_segments (0x60590 : word) = Some W_60590.
Proof. vm_refl. Qed.
Lemma D_60590 : decode_any W_60590 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_60594 : bv 32 := 0x01813483.
Lemma F_60594 : fetch_word AsanUbsan.M.loaded_segments (0x60594 : word) = Some W_60594.
Proof. vm_refl. Qed.
Lemma D_60594 : decode_any W_60594 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_60598 : bv 32 := 0x01013903.
Lemma F_60598 : fetch_word AsanUbsan.M.loaded_segments (0x60598 : word) = Some W_60598.
Proof. vm_refl. Qed.
Lemma D_60598 : decode_any W_60598 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6059c : bv 32 := 0x00813983.
Lemma F_6059c : fetch_word AsanUbsan.M.loaded_segments (0x6059c : word) = Some W_6059c.
Proof. vm_refl. Qed.
Lemma D_6059c : decode_any W_6059c = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_605a0 : bv 32 := 0x03010113.
Lemma F_605a0 : fetch_word AsanUbsan.M.loaded_segments (0x605a0 : word) = Some W_605a0.
Proof. vm_refl. Qed.
Lemma D_605a0 : decode_any W_605a0 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_605a4 : bv 32 := 0xc6dff06f.
Lemma F_605a4 : fetch_word AsanUbsan.M.loaded_segments (0x605a4 : word) = Some W_605a4.
Proof. vm_refl. Qed.
Lemma D_605a4 : decode_any W_605a4 = Some (Jal 0 2096236, 4%Z).
Proof. vm_refl. Qed.

Definition W_605a8 : bv 32 := 0x00040513.
Lemma F_605a8 : fetch_word AsanUbsan.M.loaded_segments (0x605a8 : word) = Some W_605a8.
Proof. vm_refl. Qed.
Lemma D_605a8 : decode_any W_605a8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_605ac : bv 32 := 0x00098593.
Lemma F_605ac : fetch_word AsanUbsan.M.loaded_segments (0x605ac : word) = Some W_605ac.
Proof. vm_refl. Qed.
Lemma D_605ac : decode_any W_605ac = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_605b0 : bv 32 := 0x02c2a0ef.
Lemma F_605b0 : fetch_word AsanUbsan.M.loaded_segments (0x605b0 : word) = Some W_605b0.
Proof. vm_refl. Qed.
Lemma D_605b0 : decode_any W_605b0 = Some (Jal 1 172076, 4%Z).
Proof. vm_refl. Qed.

Definition W_605b4 : bv 32 := 0x00040513.
Lemma F_605b4 : fetch_word AsanUbsan.M.loaded_segments (0x605b4 : word) = Some W_605b4.
Proof. vm_refl. Qed.
Lemma D_605b4 : decode_any W_605b4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_605b8 : bv 32 := 0x00000593.
Lemma F_605b8 : fetch_word AsanUbsan.M.loaded_segments (0x605b8 : word) = Some W_605b8.
Proof. vm_refl. Qed.
Lemma D_605b8 : decode_any W_605b8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_605bc : bv 32 := 0x7a00b0ef.
Lemma F_605bc : fetch_word AsanUbsan.M.loaded_segments (0x605bc : word) = Some W_605bc.
Proof. vm_refl. Qed.
Lemma D_605bc : decode_any W_605bc = Some (Jal 1 47008, 4%Z).
Proof. vm_refl. Qed.

Definition W_605c0 : bv 32 := 0x00000913.
Lemma F_605c0 : fetch_word AsanUbsan.M.loaded_segments (0x605c0 : word) = Some W_605c0.
Proof. vm_refl. Qed.
Lemma D_605c0 : decode_any W_605c0 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_605c4 : bv 32 := 0x00090513.
Lemma F_605c4 : fetch_word AsanUbsan.M.loaded_segments (0x605c4 : word) = Some W_605c4.
Proof. vm_refl. Qed.
Lemma D_605c4 : decode_any W_605c4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_605c8 : bv 32 := 0x02813083.
Lemma F_605c8 : fetch_word AsanUbsan.M.loaded_segments (0x605c8 : word) = Some W_605c8.
Proof. vm_refl. Qed.
Lemma D_605c8 : decode_any W_605c8 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_605cc : bv 32 := 0x02013403.
Lemma F_605cc : fetch_word AsanUbsan.M.loaded_segments (0x605cc : word) = Some W_605cc.
Proof. vm_refl. Qed.
Lemma D_605cc : decode_any W_605cc = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_605d0 : bv 32 := 0x01813483.
Lemma F_605d0 : fetch_word AsanUbsan.M.loaded_segments (0x605d0 : word) = Some W_605d0.
Proof. vm_refl. Qed.
Lemma D_605d0 : decode_any W_605d0 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_605d4 : bv 32 := 0x01013903.
Lemma F_605d4 : fetch_word AsanUbsan.M.loaded_segments (0x605d4 : word) = Some W_605d4.
Proof. vm_refl. Qed.
Lemma D_605d4 : decode_any W_605d4 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_605d8 : bv 32 := 0x00813983.
Lemma F_605d8 : fetch_word AsanUbsan.M.loaded_segments (0x605d8 : word) = Some W_605d8.
Proof. vm_refl. Qed.
Lemma D_605d8 : decode_any W_605d8 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_605dc : bv 32 := 0x03010113.
Lemma F_605dc : fetch_word AsanUbsan.M.loaded_segments (0x605dc : word) = Some W_605dc.
Proof. vm_refl. Qed.
Lemma D_605dc : decode_any W_605dc = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_605e0 : bv 32 := 0x00008067.
Lemma F_605e0 : fetch_word AsanUbsan.M.loaded_segments (0x605e0 : word) = Some W_605e0.
Proof. vm_refl. Qed.
Lemma D_605e0 : decode_any W_605e0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_605e4 : bv 32 := 0x174000ef.
Lemma F_605e4 : fetch_word AsanUbsan.M.loaded_segments (0x605e4 : word) = Some W_605e4.
Proof. vm_refl. Qed.
Lemma D_605e4 : decode_any W_605e4 = Some (Jal 1 372, 4%Z).
Proof. vm_refl. Qed.

Definition W_605e8 : bv 32 := 0x00050613.
Lemma F_605e8 : fetch_word AsanUbsan.M.loaded_segments (0x605e8 : word) = Some W_605e8.
Proof. vm_refl. Qed.
Lemma D_605e8 : decode_any W_605e8 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_605ec : bv 32 := 0x03491913.
Lemma F_605ec : fetch_word AsanUbsan.M.loaded_segments (0x605ec : word) = Some W_605ec.
Proof. vm_refl. Qed.
Lemma D_605ec : decode_any W_605ec = Some (ShiftImm ALU_SLL 18 18 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_605f0 : bv 32 := 0x03495513.
Lemma F_605f0 : fetch_word AsanUbsan.M.loaded_segments (0x605f0 : word) = Some W_605f0.
Proof. vm_refl. Qed.
Lemma D_605f0 : decode_any W_605f0 = Some (ShiftImm ALU_SRL 10 18 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_605f4 : bv 32 := 0x00a60533.
Lemma F_605f4 : fetch_word AsanUbsan.M.loaded_segments (0x605f4 : word) = Some W_605f4.
Proof. vm_refl. Qed.
Lemma D_605f4 : decode_any W_605f4 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_605f8 : bv 32 := 0x00054503.
Lemma F_605f8 : fetch_word AsanUbsan.M.loaded_segments (0x605f8 : word) = Some W_605f8.
Proof. vm_refl. Qed.
Lemma D_605f8 : decode_any W_605f8 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_605fc : bv 32 := 0xf20510e3.
Lemma F_605fc : fetch_word AsanUbsan.M.loaded_segments (0x605fc : word) = Some W_605fc.
Proof. vm_refl. Qed.
Lemma D_605fc : decode_any W_605fc = Some (Branch BC_NE 10 0 7968, 4%Z).
Proof. vm_refl. Qed.

Definition W_60600 : bv 32 := 0xfffbc517.
Lemma F_60600 : fetch_word AsanUbsan.M.loaded_segments (0x60600 : word) = Some W_60600.
Proof. vm_refl. Qed.
Lemma D_60600 : decode_any W_60600 = Some (Auipc 10 1048508, 4%Z).
Proof. vm_refl. Qed.

Definition W_60604 : bv 32 := 0xfffb2597.
Lemma F_60604 : fetch_word AsanUbsan.M.loaded_segments (0x60604 : word) = Some W_60604.
Proof. vm_refl. Qed.
Lemma D_60604 : decode_any W_60604 = Some (Auipc 11 1048498, 4%Z).
Proof. vm_refl. Qed.

Definition W_60608 : bv 32 := 0xe9950513.
Lemma F_60608 : fetch_word AsanUbsan.M.loaded_segments (0x60608 : word) = Some W_60608.
Proof. vm_refl. Qed.
Lemma D_60608 : decode_any W_60608 = Some (OpImm ALU_ADD 10 10 3737, 4%Z).
Proof. vm_refl. Qed.

Definition W_6060c : bv 32 := 0x4ee58613.
Lemma F_6060c : fetch_word AsanUbsan.M.loaded_segments (0x6060c : word) = Some W_6060c.
Proof. vm_refl. Qed.
Lemma D_6060c : decode_any W_6060c = Some (OpImm ALU_ADD 12 11 1262, 4%Z).
Proof. vm_refl. Qed.

Definition W_60610 : bv 32 := 0x03b00593.
Lemma F_60610 : fetch_word AsanUbsan.M.loaded_segments (0x60610 : word) = Some W_60610.
Proof. vm_refl. Qed.
Lemma D_60610 : decode_any W_60610 = Some (OpImm ALU_ADD 11 0 59, 4%Z).
Proof. vm_refl. Qed.

Definition W_60614 : bv 32 := 0x00000693.
Lemma F_60614 : fetch_word AsanUbsan.M.loaded_segments (0x60614 : word) = Some W_60614.
Proof. vm_refl. Qed.
Lemma D_60614 : decode_any W_60614 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60618 : bv 32 := 0x00000713.
Lemma F_60618 : fetch_word AsanUbsan.M.loaded_segments (0x60618 : word) = Some W_60618.
Proof. vm_refl. Qed.
Lemma D_60618 : decode_any W_60618 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6061c : bv 32 := 0x4cd180ef.
Lemma F_6061c : fetch_word AsanUbsan.M.loaded_segments (0x6061c : word) = Some W_6061c.
Proof. vm_refl. Qed.
Lemma D_6061c : decode_any W_6061c = Some (Jal 1 101580, 4%Z).
Proof. vm_refl. Qed.

Definition W_60620 : bv 32 := 0x81010113.
Lemma F_60620 : fetch_word AsanUbsan.M.loaded_segments (0x60620 : word) = Some W_60620.
Proof. vm_refl. Qed.
Lemma D_60620 : decode_any W_60620 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_60624 : bv 32 := 0x7e113423.
Lemma F_60624 : fetch_word AsanUbsan.M.loaded_segments (0x60624 : word) = Some W_60624.
Proof. vm_refl. Qed.
Lemma D_60624 : decode_any W_60624 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_60628 : bv 32 := 0x7e813023.
Lemma F_60628 : fetch_word AsanUbsan.M.loaded_segments (0x60628 : word) = Some W_60628.
Proof. vm_refl. Qed.
Lemma D_60628 : decode_any W_60628 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_6062c : bv 32 := 0x7c913c23.
Lemma F_6062c : fetch_word AsanUbsan.M.loaded_segments (0x6062c : word) = Some W_6062c.
Proof. vm_refl. Qed.
Lemma D_6062c : decode_any W_6062c = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_60630 : bv 32 := 0x7d213823.
Lemma F_60630 : fetch_word AsanUbsan.M.loaded_segments (0x60630 : word) = Some W_60630.
Proof. vm_refl. Qed.
Lemma D_60630 : decode_any W_60630 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_60634 : bv 32 := 0x7d313423.
Lemma F_60634 : fetch_word AsanUbsan.M.loaded_segments (0x60634 : word) = Some W_60634.
Proof. vm_refl. Qed.
Lemma D_60634 : decode_any W_60634 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_60638 : bv 32 := 0x7d413023.
Lemma F_60638 : fetch_word AsanUbsan.M.loaded_segments (0x60638 : word) = Some W_60638.
Proof. vm_refl. Qed.
Lemma D_60638 : decode_any W_60638 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_6063c : bv 32 := 0x7b513c23.
Lemma F_6063c : fetch_word AsanUbsan.M.loaded_segments (0x6063c : word) = Some W_6063c.
Proof. vm_refl. Qed.
Lemma D_6063c : decode_any W_6063c = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_60640 : bv 32 := 0x7b613823.
Lemma F_60640 : fetch_word AsanUbsan.M.loaded_segments (0x60640 : word) = Some W_60640.
Proof. vm_refl. Qed.
Lemma D_60640 : decode_any W_60640 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_60644 : bv 32 := 0x7f010413.
Lemma F_60644 : fetch_word AsanUbsan.M.loaded_segments (0x60644 : word) = Some W_60644.
Proof. vm_refl. Qed.
Lemma D_60644 : decode_any W_60644 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_60648 : bv 32 := 0xf9010113.
Lemma F_60648 : fetch_word AsanUbsan.M.loaded_segments (0x60648 : word) = Some W_60648.
Proof. vm_refl. Qed.
Lemma D_60648 : decode_any W_60648 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_6064c : bv 32 := 0x00008993.
Lemma F_6064c : fetch_word AsanUbsan.M.loaded_segments (0x6064c : word) = Some W_6064c.
Proof. vm_refl. Qed.
Lemma D_6064c : decode_any W_6064c = Some (OpImm ALU_ADD 19 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60650 : bv 32 := 0x00058493.
Lemma F_60650 : fetch_word AsanUbsan.M.loaded_segments (0x60650 : word) = Some W_60650.
Proof. vm_refl. Qed.
Lemma D_60650 : decode_any W_60650 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60654 : bv 32 := 0x00050913.
Lemma F_60654 : fetch_word AsanUbsan.M.loaded_segments (0x60654 : word) = Some W_60654.
Proof. vm_refl. Qed.
Lemma D_60654 : decode_any W_60654 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60658 : bv 32 := 0x80040a93.
Lemma F_60658 : fetch_word AsanUbsan.M.loaded_segments (0x60658 : word) = Some W_60658.
Proof. vm_refl. Qed.
Lemma D_60658 : decode_any W_60658 = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_6065c : bv 32 := 0xfa8a8a93.
Lemma F_6065c : fetch_word AsanUbsan.M.loaded_segments (0x6065c : word) = Some W_6065c.
Proof. vm_refl. Qed.
Lemma D_6065c : decode_any W_6065c = Some (OpImm ALU_ADD 21 21 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_60660 : bv 32 := 0x80040513.
Lemma F_60660 : fetch_word AsanUbsan.M.loaded_segments (0x60660 : word) = Some W_60660.
Proof. vm_refl. Qed.
Lemma D_60660 : decode_any W_60660 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_60664 : bv 32 := 0xfb850513.
Lemma F_60664 : fetch_word AsanUbsan.M.loaded_segments (0x60664 : word) = Some W_60664.
Proof. vm_refl. Qed.
Lemma D_60664 : decode_any W_60664 = Some (OpImm ALU_ADD 10 10 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_60668 : bv 32 := 0x7ffa8b13.
Lemma F_60668 : fetch_word AsanUbsan.M.loaded_segments (0x60668 : word) = Some W_60668.
Proof. vm_refl. Qed.
Lemma D_60668 : decode_any W_60668 = Some (OpImm ALU_ADD 22 21 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_6066c : bv 32 := 0x000b34a3.
Lemma F_6066c : fetch_word AsanUbsan.M.loaded_segments (0x6066c : word) = Some W_6066c.
Proof. vm_refl. Qed.
Lemma D_6066c : decode_any W_6066c = Some (Store SZ8 22 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_60670 : bv 32 := 0x00aab023.
Lemma F_60670 : fetch_word AsanUbsan.M.loaded_segments (0x60670 : word) = Some W_60670.
Proof. vm_refl. Qed.
Lemma D_60670 : decode_any W_60670 = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60674 : bv 32 := 0x000ab423.
Lemma F_60674 : fetch_word AsanUbsan.M.loaded_segments (0x60674 : word) = Some W_60674.
Proof. vm_refl. Qed.
Lemma D_60674 : decode_any W_60674 = Some (Store SZ8 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_60678 : bv 32 := 0x175070ef.
Lemma F_60678 : fetch_word AsanUbsan.M.loaded_segments (0x60678 : word) = Some W_60678.
Proof. vm_refl. Qed.
Lemma D_60678 : decode_any W_60678 = Some (Jal 1 31092, 4%Z).
Proof. vm_refl. Qed.

Definition W_6067c : bv 32 := 0x00200593.
Lemma F_6067c : fetch_word AsanUbsan.M.loaded_segments (0x6067c : word) = Some W_6067c.
Proof. vm_refl. Qed.
Lemma D_6067c : decode_any W_6067c = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_60680 : bv 32 := 0x02a5ea63.
Lemma F_60680 : fetch_word AsanUbsan.M.loaded_segments (0x60680 : word) = Some W_60680.
Proof. vm_refl. Qed.
Lemma D_60680 : decode_any W_60680 = Some (Branch BC_LTU 11 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_60684 : bv 32 := 0x169070ef.
Lemma F_60684 : fetch_word AsanUbsan.M.loaded_segments (0x60684 : word) = Some W_60684.
Proof. vm_refl. Qed.
Lemma D_60684 : decode_any W_60684 = Some (Jal 1 31080, 4%Z).
Proof. vm_refl. Qed.

Definition W_60688 : bv 32 := 0x00aaa423.
Lemma F_60688 : fetch_word AsanUbsan.M.loaded_segments (0x60688 : word) = Some W_60688.
Proof. vm_refl. Qed.
Lemma D_60688 : decode_any W_60688 = Some (Store SZ4 21 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6068c : bv 32 := 0x161070ef.
Lemma F_6068c : fetch_word AsanUbsan.M.loaded_segments (0x6068c : word) = Some W_6068c.
Proof. vm_refl. Qed.
Lemma D_6068c : decode_any W_6068c = Some (Jal 1 31072, 4%Z).
Proof. vm_refl. Qed.

Definition W_60690 : bv 32 := 0x08050263.
Lemma F_60690 : fetch_word AsanUbsan.M.loaded_segments (0x60690 : word) = Some W_60690.
Proof. vm_refl. Qed.
Lemma D_60690 : decode_any W_60690 = Some (Branch BC_EQ 10 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_60694 : bv 32 := 0x008b34a3.
Lemma F_60694 : fetch_word AsanUbsan.M.loaded_segments (0x60694 : word) = Some W_60694.
Proof. vm_refl. Qed.
Lemma D_60694 : decode_any W_60694 = Some (Store SZ8 22 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_60698 : bv 32 := 0x414200ef.
Lemma F_60698 : fetch_word AsanUbsan.M.loaded_segments (0x60698 : word) = Some W_60698.
Proof. vm_refl. Qed.
Lemma D_60698 : decode_any W_60698 = Some (Jal 1 132116, 4%Z).
Proof. vm_refl. Qed.

Definition W_6069c : bv 32 := 0x00aab823.
Lemma F_6069c : fetch_word AsanUbsan.M.loaded_segments (0x6069c : word) = Some W_6069c.
Proof. vm_refl. Qed.
Lemma D_6069c : decode_any W_6069c = Some (Store SZ8 21 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_606a0 : bv 32 := 0x14d070ef.
Lemma F_606a0 : fetch_word AsanUbsan.M.loaded_segments (0x606a0 : word) = Some W_606a0.
Proof. vm_refl. Qed.
Lemma D_606a0 : decode_any W_606a0 = Some (Jal 1 31052, 4%Z).
Proof. vm_refl. Qed.

Definition W_606a4 : bv 32 := 0x00200593.
Lemma F_606a4 : fetch_word AsanUbsan.M.loaded_segments (0x606a4 : word) = Some W_606a4.
Proof. vm_refl. Qed.
Lemma D_606a4 : decode_any W_606a4 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_606a8 : bv 32 := 0x06b56663.
Lemma F_606a8 : fetch_word AsanUbsan.M.loaded_segments (0x606a8 : word) = Some W_606a8.
Proof. vm_refl. Qed.
Lemma D_606a8 : decode_any W_606a8 = Some (Branch BC_LTU 10 11 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_606ac : bv 32 := 0x013abc23.
Lemma F_606ac : fetch_word AsanUbsan.M.loaded_segments (0x606ac : word) = Some W_606ac.
Proof. vm_refl. Qed.
Lemma D_606ac : decode_any W_606ac = Some (Store SZ8 21 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_606b0 : bv 32 := 0x0640006f.
Lemma F_606b0 : fetch_word AsanUbsan.M.loaded_segments (0x606b0 : word) = Some W_606b0.
Proof. vm_refl. Qed.
Lemma D_606b0 : decode_any W_606b0 = Some (Jal 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_606b4 : bv 32 := 0x3f8200ef.
Lemma F_606b4 : fetch_word AsanUbsan.M.loaded_segments (0x606b4 : word) = Some W_606b4.
Proof. vm_refl. Qed.
Lemma D_606b4 : decode_any W_606b4 = Some (Jal 1 132088, 4%Z).
Proof. vm_refl. Qed.

Definition W_606b8 : bv 32 := 0x00076597.
Lemma F_606b8 : fetch_word AsanUbsan.M.loaded_segments (0x606b8 : word) = Some W_606b8.
Proof. vm_refl. Qed.
Lemma D_606b8 : decode_any W_606b8 = Some (Auipc 11 118, 4%Z).
Proof. vm_refl. Qed.

Definition W_606bc : bv 32 := 0xe005b583.
Lemma F_606bc : fetch_word AsanUbsan.M.loaded_segments (0x606bc : word) = Some W_606bc.
Proof. vm_refl. Qed.
Lemma D_606bc : decode_any W_606bc = Some (Load SZ8 true 11 11 3584, 4%Z).
Proof. vm_refl. Qed.

Definition W_606c0 : bv 32 := 0x0225ca03.
Lemma F_606c0 : fetch_word AsanUbsan.M.loaded_segments (0x606c0 : word) = Some W_606c0.
Proof. vm_refl. Qed.
Lemma D_606c0 : decode_any W_606c0 = Some (Load SZ1 false 20 11 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_606c4 : bv 32 := 0x00050993.
Lemma F_606c4 : fetch_word AsanUbsan.M.loaded_segments (0x606c4 : word) = Some W_606c4.
Proof. vm_refl. Qed.
Lemma D_606c4 : decode_any W_606c4 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_606c8 : bv 32 := 0x125070ef.
Lemma F_606c8 : fetch_word AsanUbsan.M.loaded_segments (0x606c8 : word) = Some W_606c8.
Proof. vm_refl. Qed.
Lemma D_606c8 : decode_any W_606c8 = Some (Jal 1 31012, 4%Z).
Proof. vm_refl. Qed.

Definition W_606cc : bv 32 := 0x00050793.
Lemma F_606cc : fetch_word AsanUbsan.M.loaded_segments (0x606cc : word) = Some W_606cc.
Proof. vm_refl. Qed.
Lemma D_606cc : decode_any W_606cc = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_606d0 : bv 32 := 0x00153513.
Lemma F_606d0 : fetch_word AsanUbsan.M.loaded_segments (0x606d0 : word) = Some W_606d0.
Proof. vm_refl. Qed.
Lemma D_606d0 : decode_any W_606d0 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_606d4 : bv 32 := 0xfff50513.
Lemma F_606d4 : fetch_word AsanUbsan.M.loaded_segments (0x606d4 : word) = Some W_606d4.
Proof. vm_refl. Qed.
Lemma D_606d4 : decode_any W_606d4 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_606d8 : bv 32 := 0x008575b3.
Lemma F_606d8 : fetch_word AsanUbsan.M.loaded_segments (0x606d8 : word) = Some W_606d8.
Proof. vm_refl. Qed.
Lemma D_606d8 : decode_any W_606d8 = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_606dc : bv 32 := 0x00100513.
Lemma F_606dc : fetch_word AsanUbsan.M.loaded_segments (0x606dc : word) = Some W_606dc.
Proof. vm_refl. Qed.
Lemma D_606dc : decode_any W_606dc = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_606e0 : bv 32 := 0x00bb34a3.
Lemma F_606e0 : fetch_word AsanUbsan.M.loaded_segments (0x606e0 : word) = Some W_606e0.
Proof. vm_refl. Qed.
Lemma D_606e0 : decode_any W_606e0 = Some (Store SZ8 22 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_606e4 : bv 32 := 0x00f56a63.
Lemma F_606e4 : fetch_word AsanUbsan.M.loaded_segments (0x606e4 : word) = Some W_606e4.
Proof. vm_refl. Qed.
Lemma D_606e4 : decode_any W_606e4 = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_606e8 : bv 32 := 0x00a79463.
Lemma F_606e8 : fetch_word AsanUbsan.M.loaded_segments (0x606e8 : word) = Some W_606e8.
Proof. vm_refl. Qed.
Lemma D_606e8 : decode_any W_606e8 = Some (Branch BC_NE 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_606ec : bv 32 := 0x013ab823.
Lemma F_606ec : fetch_word AsanUbsan.M.loaded_segments (0x606ec : word) = Some W_606ec.
Proof. vm_refl. Qed.
Lemma D_606ec : decode_any W_606ec = Some (Store SZ8 21 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_606f0 : bv 32 := 0x00faa423.
Lemma F_606f0 : fetch_word AsanUbsan.M.loaded_segments (0x606f0 : word) = Some W_606f0.
Proof. vm_refl. Qed.
Lemma D_606f0 : decode_any W_606f0 = Some (Store SZ4 21 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_606f4 : bv 32 := 0x0200006f.
Lemma F_606f4 : fetch_word AsanUbsan.M.loaded_segments (0x606f4 : word) = Some W_606f4.
Proof. vm_refl. Qed.
Lemma D_606f4 : decode_any W_606f4 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_606f8 : bv 32 := 0x80040513.
Lemma F_606f8 : fetch_word AsanUbsan.M.loaded_segments (0x606f8 : word) = Some W_606f8.
Proof. vm_refl. Qed.
Lemma D_606f8 : decode_any W_606f8 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_606fc : bv 32 := 0xfa850513.
Lemma F_606fc : fetch_word AsanUbsan.M.loaded_segments (0x606fc : word) = Some W_606fc.
Proof. vm_refl. Qed.
Lemma D_606fc : decode_any W_606fc = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_60700 : bv 32 := 0x00098593.
Lemma F_60700 : fetch_word AsanUbsan.M.loaded_segments (0x60700 : word) = Some W_60700.
Proof. vm_refl. Qed.
Lemma D_60700 : decode_any W_60700 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60704 : bv 32 := 0x00040613.
Lemma F_60704 : fetch_word AsanUbsan.M.loaded_segments (0x60704 : word) = Some W_60704.
Proof. vm_refl. Qed.
Lemma D_60704 : decode_any W_60704 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60708 : bv 32 := 0x00000693.
Lemma F_60708 : fetch_word AsanUbsan.M.loaded_segments (0x60708 : word) = Some W_60708.
Proof. vm_refl. Qed.
Lemma D_60708 : decode_any W_60708 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6070c : bv 32 := 0x000a0713.
Lemma F_6070c : fetch_word AsanUbsan.M.loaded_segments (0x6070c : word) = Some W_6070c.
Proof. vm_refl. Qed.
Lemma D_6070c : decode_any W_6070c = Some (OpImm ALU_ADD 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60710 : bv 32 := 0x0ed070ef.
Lemma F_60710 : fetch_word AsanUbsan.M.loaded_segments (0x60710 : word) = Some W_60710.
Proof. vm_refl. Qed.
Lemma D_60710 : decode_any W_60710 = Some (Jal 1 30956, 4%Z).
Proof. vm_refl. Qed.

Definition W_60714 : bv 32 := 0x80040613.
Lemma F_60714 : fetch_word AsanUbsan.M.loaded_segments (0x60714 : word) = Some W_60714.
Proof. vm_refl. Qed.
Lemma D_60714 : decode_any W_60714 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_60718 : bv 32 := 0xfa860613.
Lemma F_60718 : fetch_word AsanUbsan.M.loaded_segments (0x60718 : word) = Some W_60718.
Proof. vm_refl. Qed.
Lemma D_60718 : decode_any W_60718 = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_6071c : bv 32 := 0x00090513.
Lemma F_6071c : fetch_word AsanUbsan.M.loaded_segments (0x6071c : word) = Some W_6071c.
Proof. vm_refl. Qed.
Lemma D_6071c : decode_any W_6071c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60720 : bv 32 := 0x00048593.
Lemma F_60720 : fetch_word AsanUbsan.M.loaded_segments (0x60720 : word) = Some W_60720.
Proof. vm_refl. Qed.
Lemma D_60720 : decode_any W_60720 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60724 : bv 32 := 0xa61dd0ef.
Lemma F_60724 : fetch_word AsanUbsan.M.loaded_segments (0x60724 : word) = Some W_60724.
Proof. vm_refl. Qed.
Lemma D_60724 : decode_any W_60724 = Some (Jal 1 1956448, 4%Z).
Proof. vm_refl. Qed.

Definition W_60728 : bv 32 := 0x07010113.
Lemma F_60728 : fetch_word AsanUbsan.M.loaded_segments (0x60728 : word) = Some W_60728.
Proof. vm_refl. Qed.
Lemma D_60728 : decode_any W_60728 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_6072c : bv 32 := 0x7e813083.
Lemma F_6072c : fetch_word AsanUbsan.M.loaded_segments (0x6072c : word) = Some W_6072c.
Proof. vm_refl. Qed.
Lemma D_6072c : decode_any W_6072c = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_60730 : bv 32 := 0x7e013403.
Lemma F_60730 : fetch_word AsanUbsan.M.loaded_segments (0x60730 : word) = Some W_60730.
Proof. vm_refl. Qed.
Lemma D_60730 : decode_any W_60730 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_60734 : bv 32 := 0x7d813483.
Lemma F_60734 : fetch_word AsanUbsan.M.loaded_segments (0x60734 : word) = Some W_60734.
Proof. vm_refl. Qed.
Lemma D_60734 : decode_any W_60734 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_60738 : bv 32 := 0x7d013903.
Lemma F_60738 : fetch_word AsanUbsan.M.loaded_segments (0x60738 : word) = Some W_60738.
Proof. vm_refl. Qed.
Lemma D_60738 : decode_any W_60738 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_6073c : bv 32 := 0x7c813983.
Lemma F_6073c : fetch_word AsanUbsan.M.loaded_segments (0x6073c : word) = Some W_6073c.
Proof. vm_refl. Qed.
Lemma D_6073c : decode_any W_6073c = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_60740 : bv 32 := 0x7c013a03.
Lemma F_60740 : fetch_word AsanUbsan.M.loaded_segments (0x60740 : word) = Some W_60740.
Proof. vm_refl. Qed.
Lemma D_60740 : decode_any W_60740 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_60744 : bv 32 := 0x7b813a83.
Lemma F_60744 : fetch_word AsanUbsan.M.loaded_segments (0x60744 : word) = Some W_60744.
Proof. vm_refl. Qed.
Lemma D_60744 : decode_any W_60744 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_60748 : bv 32 := 0x7b013b03.
Lemma F_60748 : fetch_word AsanUbsan.M.loaded_segments (0x60748 : word) = Some W_60748.
Proof. vm_refl. Qed.
Lemma D_60748 : decode_any W_60748 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_6074c : bv 32 := 0x7f010113.
Lemma F_6074c : fetch_word AsanUbsan.M.loaded_segments (0x6074c : word) = Some W_6074c.
Proof. vm_refl. Qed.
Lemma D_6074c : decode_any W_6074c = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_60750 : bv 32 := 0x00008067.
Lemma F_60750 : fetch_word AsanUbsan.M.loaded_segments (0x60750 : word) = Some W_60750.
Proof. vm_refl. Qed.
Lemma D_60750 : decode_any W_60750 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

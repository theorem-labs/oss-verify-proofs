(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_4df3c : bv 32 := 0x06048a63.
Lemma F_4df3c : fetch_word Asan.M.loaded_segments (0x4df3c : word) = Some W_4df3c.
Proof. vm_refl. Qed.
Lemma D_4df3c : decode_any W_4df3c = Some (Branch BC_EQ 9 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df40 : bv 32 := 0x00088597.
Lemma F_4df40 : fetch_word Asan.M.loaded_segments (0x4df40 : word) = Some W_4df40.
Proof. vm_refl. Qed.
Lemma D_4df40 : decode_any W_4df40 = Some (Auipc 11 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df44 : bv 32 := 0x9685ba83.
Lemma F_4df44 : fetch_word Asan.M.loaded_segments (0x4df44 : word) = Some W_4df44.
Proof. vm_refl. Qed.
Lemma D_4df44 : decode_any W_4df44 = Some (Load SZ8 true 21 11 2408, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df48 : bv 32 := 0x0fbac583.
Lemma F_4df48 : fetch_word Asan.M.loaded_segments (0x4df48 : word) = Some W_4df48.
Proof. vm_refl. Qed.
Lemma D_4df48 : decode_any W_4df48 = Some (Load SZ1 false 11 21 251, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df4c : bv 32 := 0x06058263.
Lemma F_4df4c : fetch_word Asan.M.loaded_segments (0x4df4c : word) = Some W_4df4c.
Proof. vm_refl. Qed.
Lemma D_4df4c : decode_any W_4df4c = Some (Branch BC_EQ 11 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df50 : bv 32 := 0x00150493.
Lemma F_4df50 : fetch_word Asan.M.loaded_segments (0x4df50 : word) = Some W_4df50.
Proof. vm_refl. Qed.
Lemma D_4df50 : decode_any W_4df50 = Some (OpImm ALU_ADD 9 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df54 : bv 32 := 0x0934f463.
Lemma F_4df54 : fetch_word Asan.M.loaded_segments (0x4df54 : word) = Some W_4df54.
Proof. vm_refl. Qed.
Lemma D_4df54 : decode_any W_4df54 = Some (Branch BC_GEU 9 19 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df58 : bv 32 := 0xfff94593.
Lemma F_4df58 : fetch_word Asan.M.loaded_segments (0x4df58 : word) = Some W_4df58.
Proof. vm_refl. Qed.
Lemma D_4df58 : decode_any W_4df58 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df5c : bv 32 := 0x80040a13.
Lemma F_4df5c : fetch_word Asan.M.loaded_segments (0x4df5c : word) = Some W_4df5c.
Proof. vm_refl. Qed.
Lemma D_4df5c : decode_any W_4df5c = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df60 : bv 32 := 0xfa8a0a13.
Lemma F_4df60 : fetch_word Asan.M.loaded_segments (0x4df60 : word) = Some W_4df60.
Proof. vm_refl. Qed.
Lemma D_4df60 : decode_any W_4df60 = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df64 : bv 32 := 0x0895e663.
Lemma F_4df64 : fetch_word Asan.M.loaded_segments (0x4df64 : word) = Some W_4df64.
Proof. vm_refl. Qed.
Lemma D_4df64 : decode_any W_4df64 = Some (Branch BC_LTU 11 9 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df68 : bv 32 := 0xfbf48593.
Lemma F_4df68 : fetch_word Asan.M.loaded_segments (0x4df68 : word) = Some W_4df68.
Proof. vm_refl. Qed.
Lemma D_4df68 : decode_any W_4df68 = Some (OpImm ALU_ADD 11 9 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df6c : bv 32 := 0xfbf00613.
Lemma F_4df6c : fetch_word Asan.M.loaded_segments (0x4df6c : word) = Some W_4df6c.
Proof. vm_refl. Qed.
Lemma D_4df6c : decode_any W_4df6c = Some (OpImm ALU_ADD 12 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df70 : bv 32 := 0x0eb67863.
Lemma F_4df70 : fetch_word Asan.M.loaded_segments (0x4df70 : word) = Some W_4df70.
Proof. vm_refl. Qed.
Lemma D_4df70 : decode_any W_4df70 = Some (Branch BC_GEU 12 11 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df74 : bv 32 := 0x00088597.
Lemma F_4df74 : fetch_word Asan.M.loaded_segments (0x4df74 : word) = Some W_4df74.
Proof. vm_refl. Qed.
Lemma D_4df74 : decode_any W_4df74 = Some (Auipc 11 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df78 : bv 32 := 0x9445b583.
Lemma F_4df78 : fetch_word Asan.M.loaded_segments (0x4df78 : word) = Some W_4df78.
Proof. vm_refl. Qed.
Lemma D_4df78 : decode_any W_4df78 = Some (Load SZ8 true 11 11 2372, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df7c : bv 32 := 0x009906b3.
Lemma F_4df7c : fetch_word Asan.M.loaded_segments (0x4df7c : word) = Some W_4df7c.
Proof. vm_refl. Qed.
Lemma D_4df7c : decode_any W_4df7c = Some (Op ALU_ADD 13 18 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df80 : bv 32 := 0x0005b603.
Lemma F_4df80 : fetch_word Asan.M.loaded_segments (0x4df80 : word) = Some W_4df80.
Proof. vm_refl. Qed.
Lemma D_4df80 : decode_any W_4df80 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df84 : bv 32 := 0x00395593.
Lemma F_4df84 : fetch_word Asan.M.loaded_segments (0x4df84 : word) = Some W_4df84.
Proof. vm_refl. Qed.
Lemma D_4df84 : decode_any W_4df84 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df88 : bv 32 := 0xfff68693.
Lemma F_4df88 : fetch_word Asan.M.loaded_segments (0x4df88 : word) = Some W_4df88.
Proof. vm_refl. Qed.
Lemma D_4df88 : decode_any W_4df88 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df8c : bv 32 := 0x0036d713.
Lemma F_4df8c : fetch_word Asan.M.loaded_segments (0x4df8c : word) = Some W_4df8c.
Proof. vm_refl. Qed.
Lemma D_4df8c : decode_any W_4df8c = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df90 : bv 32 := 0x00b605b3.
Lemma F_4df90 : fetch_word Asan.M.loaded_segments (0x4df90 : word) = Some W_4df90.
Proof. vm_refl. Qed.
Lemma D_4df90 : decode_any W_4df90 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df94 : bv 32 := 0x00e60633.
Lemma F_4df94 : fetch_word Asan.M.loaded_segments (0x4df94 : word) = Some W_4df94.
Proof. vm_refl. Qed.
Lemma D_4df94 : decode_any W_4df94 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df98 : bv 32 := 0xff85f713.
Lemma F_4df98 : fetch_word Asan.M.loaded_segments (0x4df98 : word) = Some W_4df98.
Proof. vm_refl. Qed.
Lemma D_4df98 : decode_any W_4df98 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4df9c : bv 32 := 0xff867793.
Lemma F_4df9c : fetch_word Asan.M.loaded_segments (0x4df9c : word) = Some W_4df9c.
Proof. vm_refl. Qed.
Lemma D_4df9c : decode_any W_4df9c = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfa0 : bv 32 := 0x00073703.
Lemma F_4dfa0 : fetch_word Asan.M.loaded_segments (0x4dfa0 : word) = Some W_4dfa0.
Proof. vm_refl. Qed.
Lemma D_4dfa0 : decode_any W_4dfa0 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfa4 : bv 32 := 0x0007b783.
Lemma F_4dfa4 : fetch_word Asan.M.loaded_segments (0x4dfa4 : word) = Some W_4dfa4.
Proof. vm_refl. Qed.
Lemma D_4dfa4 : decode_any W_4dfa4 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfa8 : bv 32 := 0x00e7e733.
Lemma F_4dfa8 : fetch_word Asan.M.loaded_segments (0x4dfa8 : word) = Some W_4dfa8.
Proof. vm_refl. Qed.
Lemma D_4dfa8 : decode_any W_4dfa8 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfac : bv 32 := 0x0a071e63.
Lemma F_4dfac : fetch_word Asan.M.loaded_segments (0x4dfac : word) = Some W_4dfac.
Proof. vm_refl. Qed.
Lemma D_4dfac : decode_any W_4dfac = Some (Branch BC_NE 14 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfb0 : bv 32 := 0x07010113.
Lemma F_4dfb0 : fetch_word Asan.M.loaded_segments (0x4dfb0 : word) = Some W_4dfb0.
Proof. vm_refl. Qed.
Lemma D_4dfb0 : decode_any W_4dfb0 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfb4 : bv 32 := 0x7e813083.
Lemma F_4dfb4 : fetch_word Asan.M.loaded_segments (0x4dfb4 : word) = Some W_4dfb4.
Proof. vm_refl. Qed.
Lemma D_4dfb4 : decode_any W_4dfb4 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfb8 : bv 32 := 0x7e013403.
Lemma F_4dfb8 : fetch_word Asan.M.loaded_segments (0x4dfb8 : word) = Some W_4dfb8.
Proof. vm_refl. Qed.
Lemma D_4dfb8 : decode_any W_4dfb8 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfbc : bv 32 := 0x7d813483.
Lemma F_4dfbc : fetch_word Asan.M.loaded_segments (0x4dfbc : word) = Some W_4dfbc.
Proof. vm_refl. Qed.
Lemma D_4dfbc : decode_any W_4dfbc = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfc0 : bv 32 := 0x7d013903.
Lemma F_4dfc0 : fetch_word Asan.M.loaded_segments (0x4dfc0 : word) = Some W_4dfc0.
Proof. vm_refl. Qed.
Lemma D_4dfc0 : decode_any W_4dfc0 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfc4 : bv 32 := 0x7c813983.
Lemma F_4dfc4 : fetch_word Asan.M.loaded_segments (0x4dfc4 : word) = Some W_4dfc4.
Proof. vm_refl. Qed.
Lemma D_4dfc4 : decode_any W_4dfc4 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfc8 : bv 32 := 0x7c013a03.
Lemma F_4dfc8 : fetch_word Asan.M.loaded_segments (0x4dfc8 : word) = Some W_4dfc8.
Proof. vm_refl. Qed.
Lemma D_4dfc8 : decode_any W_4dfc8 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfcc : bv 32 := 0x7b813a83.
Lemma F_4dfcc : fetch_word Asan.M.loaded_segments (0x4dfcc : word) = Some W_4dfcc.
Proof. vm_refl. Qed.
Lemma D_4dfcc : decode_any W_4dfcc = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfd0 : bv 32 := 0x7b013b03.
Lemma F_4dfd0 : fetch_word Asan.M.loaded_segments (0x4dfd0 : word) = Some W_4dfd0.
Proof. vm_refl. Qed.
Lemma D_4dfd0 : decode_any W_4dfd0 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfd4 : bv 32 := 0x7f010113.
Lemma F_4dfd4 : fetch_word Asan.M.loaded_segments (0x4dfd4 : word) = Some W_4dfd4.
Proof. vm_refl. Qed.
Lemma D_4dfd4 : decode_any W_4dfd4 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfd8 : bv 32 := 0x00008067.
Lemma F_4dfd8 : fetch_word Asan.M.loaded_segments (0x4dfd8 : word) = Some W_4dfd8.
Proof. vm_refl. Qed.
Lemma D_4dfd8 : decode_any W_4dfd8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfdc : bv 32 := 0x00098493.
Lemma F_4dfdc : fetch_word Asan.M.loaded_segments (0x4dfdc : word) = Some W_4dfdc.
Proof. vm_refl. Qed.
Lemma D_4dfdc : decode_any W_4dfdc = Some (OpImm ALU_ADD 9 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfe0 : bv 32 := 0xfff94593.
Lemma F_4dfe0 : fetch_word Asan.M.loaded_segments (0x4dfe0 : word) = Some W_4dfe0.
Proof. vm_refl. Qed.
Lemma D_4dfe0 : decode_any W_4dfe0 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfe4 : bv 32 := 0x80040a13.
Lemma F_4dfe4 : fetch_word Asan.M.loaded_segments (0x4dfe4 : word) = Some W_4dfe4.
Proof. vm_refl. Qed.
Lemma D_4dfe4 : decode_any W_4dfe4 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfe8 : bv 32 := 0xfa8a0a13.
Lemma F_4dfe8 : fetch_word Asan.M.loaded_segments (0x4dfe8 : word) = Some W_4dfe8.
Proof. vm_refl. Qed.
Lemma D_4dfe8 : decode_any W_4dfe8 = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dfec : bv 32 := 0xf735fee3.
Lemma F_4dfec : fetch_word Asan.M.loaded_segments (0x4dfec : word) = Some W_4dfec.
Proof. vm_refl. Qed.
Lemma D_4dfec : decode_any W_4dfec = Some (Branch BC_GEU 11 19 8060, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dff0 : bv 32 := 0x80040593.
Lemma F_4dff0 : fetch_word Asan.M.loaded_segments (0x4dff0 : word) = Some W_4dff0.
Proof. vm_refl. Qed.
Lemma D_4dff0 : decode_any W_4dff0 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dff4 : bv 32 := 0xfb858593.
Lemma F_4dff4 : fetch_word Asan.M.loaded_segments (0x4dff4 : word) = Some W_4dff4.
Proof. vm_refl. Qed.
Lemma D_4dff4 : decode_any W_4dff4 = Some (OpImm ALU_ADD 11 11 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dff8 : bv 32 := 0x80040613.
Lemma F_4dff8 : fetch_word Asan.M.loaded_segments (0x4dff8 : word) = Some W_4dff8.
Proof. vm_refl. Qed.
Lemma D_4dff8 : decode_any W_4dff8 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dffc : bv 32 := 0xfa860613.
Lemma F_4dffc : fetch_word Asan.M.loaded_segments (0x4dffc : word) = Some W_4dffc.
Proof. vm_refl. Qed.
Lemma D_4dffc : decode_any W_4dffc = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e000 : bv 32 := 0x7ff60b13.
Lemma F_4e000 : fetch_word Asan.M.loaded_segments (0x4e000 : word) = Some W_4e000.
Proof. vm_refl. Qed.
Lemma D_4e000 : decode_any W_4e000 = Some (OpImm ALU_ADD 22 12 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e004 : bv 32 := 0x000b34a3.
Lemma F_4e004 : fetch_word Asan.M.loaded_segments (0x4e004 : word) = Some W_4e004.
Proof. vm_refl. Qed.
Lemma D_4e004 : decode_any W_4e004 = Some (Store SZ8 22 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e008 : bv 32 := 0x00ba3023.
Lemma F_4e008 : fetch_word Asan.M.loaded_segments (0x4e008 : word) = Some W_4e008.
Proof. vm_refl. Qed.
Lemma D_4e008 : decode_any W_4e008 = Some (Store SZ8 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e00c : bv 32 := 0x000a3423.
Lemma F_4e00c : fetch_word Asan.M.loaded_segments (0x4e00c : word) = Some W_4e00c.
Proof. vm_refl. Qed.
Lemma D_4e00c : decode_any W_4e00c = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e010 : bv 32 := 0x00050993.
Lemma F_4e010 : fetch_word Asan.M.loaded_segments (0x4e010 : word) = Some W_4e010.
Proof. vm_refl. Qed.
Lemma D_4e010 : decode_any W_4e010 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e014 : bv 32 := 0x019320ef.
Lemma F_4e014 : fetch_word Asan.M.loaded_segments (0x4e014 : word) = Some W_4e014.
Proof. vm_refl. Qed.
Lemma D_4e014 : decode_any W_4e014 = Some (Jal 1 206872, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e018 : bv 32 := 0x00050593.
Lemma F_4e018 : fetch_word Asan.M.loaded_segments (0x4e018 : word) = Some W_4e018.
Proof. vm_refl. Qed.
Lemma D_4e018 : decode_any W_4e018 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e01c : bv 32 := 0x021ac703.
Lemma F_4e01c : fetch_word Asan.M.loaded_segments (0x4e01c : word) = Some W_4e01c.
Proof. vm_refl. Qed.
Lemma D_4e01c : decode_any W_4e01c = Some (Load SZ1 false 14 21 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e020 : bv 32 := 0x008b34a3.
Lemma F_4e020 : fetch_word Asan.M.loaded_segments (0x4e020 : word) = Some W_4e020.
Proof. vm_refl. Qed.
Lemma D_4e020 : decode_any W_4e020 = Some (Store SZ8 22 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e024 : bv 32 := 0x80040513.
Lemma F_4e024 : fetch_word Asan.M.loaded_segments (0x4e024 : word) = Some W_4e024.
Proof. vm_refl. Qed.
Lemma D_4e024 : decode_any W_4e024 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e028 : bv 32 := 0xfa850513.
Lemma F_4e028 : fetch_word Asan.M.loaded_segments (0x4e028 : word) = Some W_4e028.
Proof. vm_refl. Qed.
Lemma D_4e028 : decode_any W_4e028 = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e02c : bv 32 := 0x0ff00793.
Lemma F_4e02c : fetch_word Asan.M.loaded_segments (0x4e02c : word) = Some W_4e02c.
Proof. vm_refl. Qed.
Lemma D_4e02c : decode_any W_4e02c = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e030 : bv 32 := 0x00040613.
Lemma F_4e030 : fetch_word Asan.M.loaded_segments (0x4e030 : word) = Some W_4e030.
Proof. vm_refl. Qed.
Lemma D_4e030 : decode_any W_4e030 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e034 : bv 32 := 0x00000693.
Lemma F_4e034 : fetch_word Asan.M.loaded_segments (0x4e034 : word) = Some W_4e034.
Proof. vm_refl. Qed.
Lemma D_4e034 : decode_any W_4e034 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e038 : bv 32 := 0x545190ef.
Lemma F_4e038 : fetch_word Asan.M.loaded_segments (0x4e038 : word) = Some W_4e038.
Proof. vm_refl. Qed.
Lemma D_4e038 : decode_any W_4e038 = Some (Jal 1 105796, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e03c : bv 32 := 0x80040613.
Lemma F_4e03c : fetch_word Asan.M.loaded_segments (0x4e03c : word) = Some W_4e03c.
Proof. vm_refl. Qed.
Lemma D_4e03c : decode_any W_4e03c = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e040 : bv 32 := 0xfa860613.
Lemma F_4e040 : fetch_word Asan.M.loaded_segments (0x4e040 : word) = Some W_4e040.
Proof. vm_refl. Qed.
Lemma D_4e040 : decode_any W_4e040 = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e044 : bv 32 := 0x00090513.
Lemma F_4e044 : fetch_word Asan.M.loaded_segments (0x4e044 : word) = Some W_4e044.
Proof. vm_refl. Qed.
Lemma D_4e044 : decode_any W_4e044 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e048 : bv 32 := 0x00048593.
Lemma F_4e048 : fetch_word Asan.M.loaded_segments (0x4e048 : word) = Some W_4e048.
Proof. vm_refl. Qed.
Lemma D_4e048 : decode_any W_4e048 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e04c : bv 32 := 0x2e9160ef.
Lemma F_4e04c : fetch_word Asan.M.loaded_segments (0x4e04c : word) = Some W_4e04c.
Proof. vm_refl. Qed.
Lemma D_4e04c : decode_any W_4e04c = Some (Jal 1 92904, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e050 : bv 32 := 0x00098513.
Lemma F_4e050 : fetch_word Asan.M.loaded_segments (0x4e050 : word) = Some W_4e050.
Proof. vm_refl. Qed.
Lemma D_4e050 : decode_any W_4e050 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e054 : bv 32 := 0xfbf48593.
Lemma F_4e054 : fetch_word Asan.M.loaded_segments (0x4e054 : word) = Some W_4e054.
Proof. vm_refl. Qed.
Lemma D_4e054 : decode_any W_4e054 = Some (OpImm ALU_ADD 11 9 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e058 : bv 32 := 0xfbf00613.
Lemma F_4e058 : fetch_word Asan.M.loaded_segments (0x4e058 : word) = Some W_4e058.
Proof. vm_refl. Qed.
Lemma D_4e058 : decode_any W_4e058 = Some (OpImm ALU_ADD 12 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e05c : bv 32 := 0xf0b66ce3.
Lemma F_4e05c : fetch_word Asan.M.loaded_segments (0x4e05c : word) = Some W_4e05c.
Proof. vm_refl. Qed.
Lemma D_4e05c : decode_any W_4e05c = Some (Branch BC_LTU 12 11 7960, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e060 : bv 32 := 0x02049e63.
Lemma F_4e060 : fetch_word Asan.M.loaded_segments (0x4e060 : word) = Some W_4e060.
Proof. vm_refl. Qed.
Lemma D_4e060 : decode_any W_4e060 = Some (Branch BC_NE 9 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e064 : bv 32 := 0xf4dff06f.
Lemma F_4e064 : fetch_word Asan.M.loaded_segments (0x4e064 : word) = Some W_4e064.
Proof. vm_refl. Qed.
Lemma D_4e064 : decode_any W_4e064 = Some (Jal 0 2096972, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e068 : bv 32 := 0x00060703.
Lemma F_4e068 : fetch_word Asan.M.loaded_segments (0x4e068 : word) = Some W_4e068.
Proof. vm_refl. Qed.
Lemma D_4e068 : decode_any W_4e068 = Some (Load SZ1 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e06c : bv 32 := 0x0076f693.
Lemma F_4e06c : fetch_word Asan.M.loaded_segments (0x4e06c : word) = Some W_4e06c.
Proof. vm_refl. Qed.
Lemma D_4e06c : decode_any W_4e06c = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e070 : bv 32 := 0x00e037b3.
Lemma F_4e070 : fetch_word Asan.M.loaded_segments (0x4e070 : word) = Some W_4e070.
Proof. vm_refl. Qed.
Lemma D_4e070 : decode_any W_4e070 = Some (Op ALU_SLTU 15 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e074 : bv 32 := 0x00e6a6b3.
Lemma F_4e074 : fetch_word Asan.M.loaded_segments (0x4e074 : word) = Some W_4e074.
Proof. vm_refl. Qed.
Lemma D_4e074 : decode_any W_4e074 = Some (Op ALU_SLT 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e078 : bv 32 := 0x0016c693.
Lemma F_4e078 : fetch_word Asan.M.loaded_segments (0x4e078 : word) = Some W_4e078.
Proof. vm_refl. Qed.
Lemma D_4e078 : decode_any W_4e078 = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e07c : bv 32 := 0x00d7f6b3.
Lemma F_4e07c : fetch_word Asan.M.loaded_segments (0x4e07c : word) = Some W_4e07c.
Proof. vm_refl. Qed.
Lemma D_4e07c : decode_any W_4e07c = Some (Op ALU_AND 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e080 : bv 32 := 0x00c5fa63.
Lemma F_4e080 : fetch_word Asan.M.loaded_segments (0x4e080 : word) = Some W_4e080.
Proof. vm_refl. Qed.
Lemma D_4e080 : decode_any W_4e080 = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e084 : bv 32 := 0x0005c703.
Lemma F_4e084 : fetch_word Asan.M.loaded_segments (0x4e084 : word) = Some W_4e084.
Proof. vm_refl. Qed.
Lemma D_4e084 : decode_any W_4e084 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e088 : bv 32 := 0x00158593.
Lemma F_4e088 : fetch_word Asan.M.loaded_segments (0x4e088 : word) = Some W_4e088.
Proof. vm_refl. Qed.
Lemma D_4e088 : decode_any W_4e088 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e08c : bv 32 := 0x00d766b3.
Lemma F_4e08c : fetch_word Asan.M.loaded_segments (0x4e08c : word) = Some W_4e08c.
Proof. vm_refl. Qed.
Lemma D_4e08c : decode_any W_4e08c = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e090 : bv 32 := 0xfec59ae3.
Lemma F_4e090 : fetch_word Asan.M.loaded_segments (0x4e090 : word) = Some W_4e090.
Proof. vm_refl. Qed.
Lemma D_4e090 : decode_any W_4e090 = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e094 : bv 32 := 0x0ff6f593.
Lemma F_4e094 : fetch_word Asan.M.loaded_segments (0x4e094 : word) = Some W_4e094.
Proof. vm_refl. Qed.
Lemma D_4e094 : decode_any W_4e094 = Some (OpImm ALU_AND 11 13 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e098 : bv 32 := 0xf0058ce3.
Lemma F_4e098 : fetch_word Asan.M.loaded_segments (0x4e098 : word) = Some W_4e098.
Proof. vm_refl. Qed.
Lemma D_4e098 : decode_any W_4e098 = Some (Branch BC_EQ 11 0 7960, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e09c : bv 32 := 0x00050b13.
Lemma F_4e09c : fetch_word Asan.M.loaded_segments (0x4e09c : word) = Some W_4e09c.
Proof. vm_refl. Qed.
Lemma D_4e09c : decode_any W_4e09c = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0a0 : bv 32 := 0x00090513.
Lemma F_4e0a0 : fetch_word Asan.M.loaded_segments (0x4e0a0 : word) = Some W_4e0a0.
Proof. vm_refl. Qed.
Lemma D_4e0a0 : decode_any W_4e0a0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0a4 : bv 32 := 0x00048593.
Lemma F_4e0a4 : fetch_word Asan.M.loaded_segments (0x4e0a4 : word) = Some W_4e0a4.
Proof. vm_refl. Qed.
Lemma D_4e0a4 : decode_any W_4e0a4 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0a8 : bv 32 := 0x059130ef.
Lemma F_4e0a8 : fetch_word Asan.M.loaded_segments (0x4e0a8 : word) = Some W_4e0a8.
Proof. vm_refl. Qed.
Lemma D_4e0a8 : decode_any W_4e0a8 = Some (Jal 1 79960, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0ac : bv 32 := 0x00050913.
Lemma F_4e0ac : fetch_word Asan.M.loaded_segments (0x4e0ac : word) = Some W_4e0ac.
Proof. vm_refl. Qed.
Lemma D_4e0ac : decode_any W_4e0ac = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0b0 : bv 32 := 0x000b0513.
Lemma F_4e0b0 : fetch_word Asan.M.loaded_segments (0x4e0b0 : word) = Some W_4e0b0.
Proof. vm_refl. Qed.
Lemma D_4e0b0 : decode_any W_4e0b0 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e0b4 : bv 32 := 0xee090ee3.
Lemma F_4e0b4 : fetch_word Asan.M.loaded_segments (0x4e0b4 : word) = Some W_4e0b4.
Proof. vm_refl. Qed.
Lemma D_4e0b4 : decode_any W_4e0b4 = Some (Branch BC_EQ 18 0 7932, 4%Z).
Proof. vm_refl. Qed.

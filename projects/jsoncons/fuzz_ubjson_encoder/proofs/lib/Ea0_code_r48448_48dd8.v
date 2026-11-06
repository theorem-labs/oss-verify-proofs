(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_5df78 : bv 32 := 0xf7010113.
Lemma F_5df78 : fetch_word Asan.M.loaded_segments (0x5dfc8 : word) = Some W_5df78.
Proof. vm_refl. Qed.
Lemma D_5df78 : decode_any W_5df78 = Some (OpImm ALU_ADD 2 2 3952, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df7c : bv 32 := 0x08113423.
Lemma F_5df7c : fetch_word Asan.M.loaded_segments (0x5dfcc : word) = Some W_5df7c.
Proof. vm_refl. Qed.
Lemma D_5df7c : decode_any W_5df7c = Some (Store SZ8 2 1 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df80 : bv 32 := 0x08813023.
Lemma F_5df80 : fetch_word Asan.M.loaded_segments (0x5dfd0 : word) = Some W_5df80.
Proof. vm_refl. Qed.
Lemma D_5df80 : decode_any W_5df80 = Some (Store SZ8 2 8 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df84 : bv 32 := 0x06913c23.
Lemma F_5df84 : fetch_word Asan.M.loaded_segments (0x5dfd4 : word) = Some W_5df84.
Proof. vm_refl. Qed.
Lemma D_5df84 : decode_any W_5df84 = Some (Store SZ8 2 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df88 : bv 32 := 0x07213823.
Lemma F_5df88 : fetch_word Asan.M.loaded_segments (0x5dfd8 : word) = Some W_5df88.
Proof. vm_refl. Qed.
Lemma D_5df88 : decode_any W_5df88 = Some (Store SZ8 2 18 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df8c : bv 32 := 0x07313423.
Lemma F_5df8c : fetch_word Asan.M.loaded_segments (0x5dfdc : word) = Some W_5df8c.
Proof. vm_refl. Qed.
Lemma D_5df8c : decode_any W_5df8c = Some (Store SZ8 2 19 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df90 : bv 32 := 0x07413023.
Lemma F_5df90 : fetch_word Asan.M.loaded_segments (0x5dfe0 : word) = Some W_5df90.
Proof. vm_refl. Qed.
Lemma D_5df90 : decode_any W_5df90 = Some (Store SZ8 2 20 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df94 : bv 32 := 0x05513c23.
Lemma F_5df94 : fetch_word Asan.M.loaded_segments (0x5dfe4 : word) = Some W_5df94.
Proof. vm_refl. Qed.
Lemma D_5df94 : decode_any W_5df94 = Some (Store SZ8 2 21 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df98 : bv 32 := 0x05613823.
Lemma F_5df98 : fetch_word Asan.M.loaded_segments (0x5dfe8 : word) = Some W_5df98.
Proof. vm_refl. Qed.
Lemma D_5df98 : decode_any W_5df98 = Some (Store SZ8 2 22 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5df9c : bv 32 := 0x05713423.
Lemma F_5df9c : fetch_word Asan.M.loaded_segments (0x5dfec : word) = Some W_5df9c.
Proof. vm_refl. Qed.
Lemma D_5df9c : decode_any W_5df9c = Some (Store SZ8 2 23 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfa0 : bv 32 := 0x05813023.
Lemma F_5dfa0 : fetch_word Asan.M.loaded_segments (0x5dff0 : word) = Some W_5dfa0.
Proof. vm_refl. Qed.
Lemma D_5dfa0 : decode_any W_5dfa0 = Some (Store SZ8 2 24 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfa4 : bv 32 := 0x03913c23.
Lemma F_5dfa4 : fetch_word Asan.M.loaded_segments (0x5dff4 : word) = Some W_5dfa4.
Proof. vm_refl. Qed.
Lemma D_5dfa4 : decode_any W_5dfa4 = Some (Store SZ8 2 25 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfa8 : bv 32 := 0x03a13823.
Lemma F_5dfa8 : fetch_word Asan.M.loaded_segments (0x5dff8 : word) = Some W_5dfa8.
Proof. vm_refl. Qed.
Lemma D_5dfa8 : decode_any W_5dfa8 = Some (Store SZ8 2 26 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfac : bv 32 := 0x03b13423.
Lemma F_5dfac : fetch_word Asan.M.loaded_segments (0x5dffc : word) = Some W_5dfac.
Proof. vm_refl. Qed.
Lemma D_5dfac : decode_any W_5dfac = Some (Store SZ8 2 27 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfb0 : bv 32 := 0x00058493.
Lemma F_5dfb0 : fetch_word Asan.M.loaded_segments (0x5e000 : word) = Some W_5dfb0.
Proof. vm_refl. Qed.
Lemma D_5dfb0 : decode_any W_5dfb0 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfb4 : bv 32 := 0x00050c93.
Lemma F_5dfb4 : fetch_word Asan.M.loaded_segments (0x5e004 : word) = Some W_5dfb4.
Proof. vm_refl. Qed.
Lemma D_5dfb4 : decode_any W_5dfb4 = Some (OpImm ALU_ADD 25 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfb8 : bv 32 := 0x260260ef.
Lemma F_5dfb8 : fetch_word Asan.M.loaded_segments (0x5e008 : word) = Some W_5dfb8.
Proof. vm_refl. Qed.
Lemma D_5dfb8 : decode_any W_5dfb8 = Some (Jal 1 156256, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfbc : bv 32 := 0x26050463.
Lemma F_5dfbc : fetch_word Asan.M.loaded_segments (0x5e00c : word) = Some W_5dfbc.
Proof. vm_refl. Qed.
Lemma D_5dfbc : decode_any W_5dfbc = Some (Branch BC_EQ 10 0 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfc0 : bv 32 := 0x00050913.
Lemma F_5dfc0 : fetch_word Asan.M.loaded_segments (0x5e010 : word) = Some W_5dfc0.
Proof. vm_refl. Qed.
Lemma D_5dfc0 : decode_any W_5dfc0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfc4 : bv 32 := 0x418260ef.
Lemma F_5dfc4 : fetch_word Asan.M.loaded_segments (0x5e014 : word) = Some W_5dfc4.
Proof. vm_refl. Qed.
Lemma D_5dfc4 : decode_any W_5dfc4 = Some (Jal 1 156696, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfc8 : bv 32 := 0x00050993.
Lemma F_5dfc8 : fetch_word Asan.M.loaded_segments (0x5e018 : word) = Some W_5dfc8.
Proof. vm_refl. Qed.
Lemma D_5dfc8 : decode_any W_5dfc8 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfcc : bv 32 := 0x00090513.
Lemma F_5dfcc : fetch_word Asan.M.loaded_segments (0x5e01c : word) = Some W_5dfcc.
Proof. vm_refl. Qed.
Lemma D_5dfcc : decode_any W_5dfcc = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfd0 : bv 32 := 0x464260ef.
Lemma F_5dfd0 : fetch_word Asan.M.loaded_segments (0x5e020 : word) = Some W_5dfd0.
Proof. vm_refl. Qed.
Lemma D_5dfd0 : decode_any W_5dfd0 = Some (Jal 1 156772, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfd4 : bv 32 := 0x2499e863.
Lemma F_5dfd4 : fetch_word Asan.M.loaded_segments (0x5e024 : word) = Some W_5dfd4.
Proof. vm_refl. Qed.
Lemma D_5dfd4 : decode_any W_5dfd4 = Some (Branch BC_LTU 19 9 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfd8 : bv 32 := 0x00050913.
Lemma F_5dfd8 : fetch_word Asan.M.loaded_segments (0x5e028 : word) = Some W_5dfd8.
Proof. vm_refl. Qed.
Lemma D_5dfd8 : decode_any W_5dfd8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfdc : bv 32 := 0x24a4e463.
Lemma F_5dfdc : fetch_word Asan.M.loaded_segments (0x5e02c : word) = Some W_5dfdc.
Proof. vm_refl. Qed.
Lemma D_5dfdc : decode_any W_5dfdc = Some (Branch BC_LTU 9 10 584, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfe0 : bv 32 := 0x00000d13.
Lemma F_5dfe0 : fetch_word Asan.M.loaded_segments (0x5e030 : word) = Some W_5dfe0.
Proof. vm_refl. Qed.
Lemma D_5dfe0 : decode_any W_5dfe0 = Some (OpImm ALU_ADD 26 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfe4 : bv 32 := 0x00001437.
Lemma F_5dfe4 : fetch_word Asan.M.loaded_segments (0x5e034 : word) = Some W_5dfe4.
Proof. vm_refl. Qed.
Lemma D_5dfe4 : decode_any W_5dfe4 = Some (Lui 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfe8 : bv 32 := 0x000db517.
Lemma F_5dfe8 : fetch_word Asan.M.loaded_segments (0x5e038 : word) = Some W_5dfe8.
Proof. vm_refl. Qed.
Lemma D_5dfe8 : decode_any W_5dfe8 = Some (Auipc 10 219, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfec : bv 32 := 0x000db597.
Lemma F_5dfec : fetch_word Asan.M.loaded_segments (0x5e03c : word) = Some W_5dfec.
Proof. vm_refl. Qed.
Lemma D_5dfec : decode_any W_5dfec = Some (Auipc 11 219, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dff0 : bv 32 := 0x000db617.
Lemma F_5dff0 : fetch_word Asan.M.loaded_segments (0x5e040 : word) = Some W_5dff0.
Proof. vm_refl. Qed.
Lemma D_5dff0 : decode_any W_5dff0 = Some (Auipc 12 219, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dff4 : bv 32 := 0x000db697.
Lemma F_5dff4 : fetch_word Asan.M.loaded_segments (0x5e044 : word) = Some W_5dff4.
Proof. vm_refl. Qed.
Lemma D_5dff4 : decode_any W_5dff4 = Some (Auipc 13 219, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dff8 : bv 32 := 0x000db717.
Lemma F_5dff8 : fetch_word Asan.M.loaded_segments (0x5e048 : word) = Some W_5dff8.
Proof. vm_refl. Qed.
Lemma D_5dff8 : decode_any W_5dff8 = Some (Auipc 14 219, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dffc : bv 32 := 0xfffb2797.
Lemma F_5dffc : fetch_word Asan.M.loaded_segments (0x5e04c : word) = Some W_5dffc.
Proof. vm_refl. Qed.
Lemma D_5dffc : decode_any W_5dffc = Some (Auipc 15 1048498, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e000 : bv 32 := 0x008c8433.
Lemma F_5e000 : fetch_word Asan.M.loaded_segments (0x5e050 : word) = Some W_5e000.
Proof. vm_refl. Qed.
Lemma D_5e000 : decode_any W_5e000 = Some (Op ALU_ADD 8 25 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e004 : bv 32 := 0x18053b03.
Lemma F_5e004 : fetch_word Asan.M.loaded_segments (0x5e054 : word) = Some W_5e004.
Proof. vm_refl. Qed.
Lemma D_5e004 : decode_any W_5e004 = Some (Load SZ8 true 22 10 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e008 : bv 32 := 0x1845b503.
Lemma F_5e008 : fetch_word Asan.M.loaded_segments (0x5e058 : word) = Some W_5e008.
Proof. vm_refl. Qed.
Lemma D_5e008 : decode_any W_5e008 = Some (Load SZ8 true 10 11 388, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e00c : bv 32 := 0x00a13c23.
Lemma F_5e00c : fetch_word Asan.M.loaded_segments (0x5e05c : word) = Some W_5e00c.
Proof. vm_refl. Qed.
Lemma D_5e00c : decode_any W_5e00c = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e010 : bv 32 := 0x18863503.
Lemma F_5e010 : fetch_word Asan.M.loaded_segments (0x5e060 : word) = Some W_5e010.
Proof. vm_refl. Qed.
Lemma D_5e010 : decode_any W_5e010 = Some (Load SZ8 true 10 12 392, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e014 : bv 32 := 0x00a13823.
Lemma F_5e014 : fetch_word Asan.M.loaded_segments (0x5e064 : word) = Some W_5e014.
Proof. vm_refl. Qed.
Lemma D_5e014 : decode_any W_5e014 = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e018 : bv 32 := 0x18c6b503.
Lemma F_5e018 : fetch_word Asan.M.loaded_segments (0x5e068 : word) = Some W_5e018.
Proof. vm_refl. Qed.
Lemma D_5e018 : decode_any W_5e018 = Some (Load SZ8 true 10 13 396, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e01c : bv 32 := 0x00a13423.
Lemma F_5e01c : fetch_word Asan.M.loaded_segments (0x5e06c : word) = Some W_5e01c.
Proof. vm_refl. Qed.
Lemma D_5e01c : decode_any W_5e01c = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e020 : bv 32 := 0x16873503.
Lemma F_5e020 : fetch_word Asan.M.loaded_segments (0x5e070 : word) = Some W_5e020.
Proof. vm_refl. Qed.
Lemma D_5e020 : decode_any W_5e020 = Some (Load SZ8 true 10 14 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e024 : bv 32 := 0x00a13023.
Lemma F_5e024 : fetch_word Asan.M.loaded_segments (0x5e074 : word) = Some W_5e024.
Proof. vm_refl. Qed.
Lemma D_5e024 : decode_any W_5e024 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e028 : bv 32 := 0x3447bb83.
Lemma F_5e028 : fetch_word Asan.M.loaded_segments (0x5e078 : word) = Some W_5e028.
Proof. vm_refl. Qed.
Lemma D_5e028 : decode_any W_5e028 = Some (Load SZ8 true 23 15 836, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e02c : bv 32 := 0x00100393.
Lemma F_5e02c : fetch_word Asan.M.loaded_segments (0x5e07c : word) = Some W_5e02c.
Proof. vm_refl. Qed.
Lemma D_5e02c : decode_any W_5e02c = Some (OpImm ALU_ADD 7 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e030 : bv 32 := 0x00600e13.
Lemma F_5e030 : fetch_word Asan.M.loaded_segments (0x5e080 : word) = Some W_5e030.
Proof. vm_refl. Qed.
Lemma D_5e030 : decode_any W_5e030 = Some (OpImm ALU_ADD 28 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e034 : bv 32 := 0x00000a13.
Lemma F_5e034 : fetch_word Asan.M.loaded_segments (0x5e084 : word) = Some W_5e034.
Proof. vm_refl. Qed.
Lemma D_5e034 : decode_any W_5e034 = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e038 : bv 32 := 0x0100006f.
Lemma F_5e038 : fetch_word Asan.M.loaded_segments (0x5e088 : word) = Some W_5e038.
Proof. vm_refl. Qed.
Lemma D_5e038 : decode_any W_5e038 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e03c : bv 32 := 0x001a0a13.
Lemma F_5e03c : fetch_word Asan.M.loaded_segments (0x5e08c : word) = Some W_5e03c.
Proof. vm_refl. Qed.
Lemma D_5e03c : decode_any W_5e03c = Some (OpImm ALU_ADD 20 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e040 : bv 32 := 0x00b00513.
Lemma F_5e040 : fetch_word Asan.M.loaded_segments (0x5e090 : word) = Some W_5e040.
Proof. vm_refl. Qed.
Lemma D_5e040 : decode_any W_5e040 = Some (OpImm ALU_ADD 10 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e044 : bv 32 := 0x1caa0e63.
Lemma F_5e044 : fetch_word Asan.M.loaded_segments (0x5e094 : word) = Some W_5e044.
Proof. vm_refl. Qed.
Lemma D_5e044 : decode_any W_5e044 = Some (Branch BC_EQ 20 10 476, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e048 : bv 32 := 0x00000d93.
Lemma F_5e048 : fetch_word Asan.M.loaded_segments (0x5e098 : word) = Some W_5e048.
Proof. vm_refl. Qed.
Lemma D_5e048 : decode_any W_5e048 = Some (OpImm ALU_ADD 27 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e04c : bv 32 := 0x058cb503.
Lemma F_5e04c : fetch_word Asan.M.loaded_segments (0x5e09c : word) = Some W_5e04c.
Proof. vm_refl. Qed.
Lemma D_5e04c : decode_any W_5e04c = Some (Load SZ8 true 10 25 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e050 : bv 32 := 0x00a00593.
Lemma F_5e050 : fetch_word Asan.M.loaded_segments (0x5e0a0 : word) = Some W_5e050.
Proof. vm_refl. Qed.
Lemma D_5e050 : decode_any W_5e050 = Some (OpImm ALU_ADD 11 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e054 : bv 32 := 0x414585bb.
Lemma F_5e054 : fetch_word Asan.M.loaded_segments (0x5e0a4 : word) = Some W_5e054.
Proof. vm_refl. Qed.
Lemma D_5e054 : decode_any W_5e054 = Some (Op32 ALU_SUB 11 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e058 : bv 32 := 0x006a0a93.
Lemma F_5e058 : fetch_word Asan.M.loaded_segments (0x5e0a8 : word) = Some W_5e058.
Proof. vm_refl. Qed.
Lemma D_5e058 : decode_any W_5e058 = Some (OpImm ALU_ADD 21 20 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e05c : bv 32 := 0xfff00613.
Lemma F_5e05c : fetch_word Asan.M.loaded_segments (0x5e0ac : word) = Some W_5e05c.
Proof. vm_refl. Qed.
Lemma D_5e05c : decode_any W_5e05c = Some (OpImm ALU_ADD 12 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e060 : bv 32 := 0x00b615b3.
Lemma F_5e060 : fetch_word Asan.M.loaded_segments (0x5e0b0 : word) = Some W_5e060.
Proof. vm_refl. Qed.
Lemma D_5e060 : decode_any W_5e060 = Some (Op ALU_SLL 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e064 : bv 32 := 0x3ff5f593.
Lemma F_5e064 : fetch_word Asan.M.loaded_segments (0x5e0b4 : word) = Some W_5e064.
Proof. vm_refl. Qed.
Lemma D_5e064 : decode_any W_5e064 = Some (OpImm ALU_AND 11 11 1023, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e068 : bv 32 := 0xff150613.
Lemma F_5e068 : fetch_word Asan.M.loaded_segments (0x5e0b8 : word) = Some W_5e068.
Proof. vm_refl. Qed.
Lemma D_5e068 : decode_any W_5e068 = Some (OpImm ALU_ADD 12 10 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e06c : bv 32 := 0x414509b3.
Lemma F_5e06c : fetch_word Asan.M.loaded_segments (0x5e0bc : word) = Some W_5e06c.
Proof. vm_refl. Qed.
Lemma D_5e06c : decode_any W_5e06c = Some (Op ALU_SUB 19 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e070 : bv 32 := 0x00c59c33.
Lemma F_5e070 : fetch_word Asan.M.loaded_segments (0x5e0c0 : word) = Some W_5e070.
Proof. vm_refl. Qed.
Lemma D_5e070 : decode_any W_5e070 = Some (Op ALU_SLL 24 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e074 : bv 32 := 0xffa98993.
Lemma F_5e074 : fetch_word Asan.M.loaded_segments (0x5e0c4 : word) = Some W_5e074.
Proof. vm_refl. Qed.
Lemma D_5e074 : decode_any W_5e074 = Some (OpImm ALU_ADD 19 19 4090, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e078 : bv 32 := 0x01840c33.
Lemma F_5e078 : fetch_word Asan.M.loaded_segments (0x5e0c8 : word) = Some W_5e078.
Proof. vm_refl. Qed.
Lemma D_5e078 : decode_any W_5e078 = Some (Op ALU_ADD 24 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e07c : bv 32 := 0x04000513.
Lemma F_5e07c : fetch_word Asan.M.loaded_segments (0x5e0cc : word) = Some W_5e07c.
Proof. vm_refl. Qed.
Lemma D_5e07c : decode_any W_5e07c = Some (OpImm ALU_ADD 10 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e080 : bv 32 := 0x01451533.
Lemma F_5e080 : fetch_word Asan.M.loaded_segments (0x5e0d0 : word) = Some W_5e080.
Proof. vm_refl. Qed.
Lemma D_5e080 : decode_any W_5e080 = Some (Op ALU_SLL 10 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e084 : bv 32 := 0x02a13023.
Lemma F_5e084 : fetch_word Asan.M.loaded_segments (0x5e0d4 : word) = Some W_5e084.
Proof. vm_refl. Qed.
Lemma D_5e084 : decode_any W_5e084 = Some (Store SZ8 2 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e088 : bv 32 := 0x0240006f.
Lemma F_5e088 : fetch_word Asan.M.loaded_segments (0x5e0d8 : word) = Some W_5e088.
Proof. vm_refl. Qed.
Lemma D_5e088 : decode_any W_5e088 = Some (Jal 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0a0 : bv 32 := 0x001d8d93.
Lemma F_5e0a0 : fetch_word Asan.M.loaded_segments (0x5e0f0 : word) = Some W_5e0a0.
Proof. vm_refl. Qed.
Lemma D_5e0a0 : decode_any W_5e0a0 = Some (OpImm ALU_ADD 27 27 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0a4 : bv 32 := 0x013dd533.
Lemma F_5e0a4 : fetch_word Asan.M.loaded_segments (0x5e0f4 : word) = Some W_5e0a4.
Proof. vm_refl. Qed.
Lemma D_5e0a4 : decode_any W_5e0a4 = Some (Op ALU_SRL 10 27 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0a8 : bv 32 := 0xf8051ae3.
Lemma F_5e0a8 : fetch_word Asan.M.loaded_segments (0x5e0f8 : word) = Some W_5e0a8.
Proof. vm_refl. Qed.
Lemma D_5e0a8 : decode_any W_5e0a8 = Some (Branch BC_NE 10 0 8084, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0ac : bv 32 := 0x01bc05b3.
Lemma F_5e0ac : fetch_word Asan.M.loaded_segments (0x5e0fc : word) = Some W_5e0ac.
Proof. vm_refl. Qed.
Lemma D_5e0ac : decode_any W_5e0ac = Some (Op ALU_ADD 11 24 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0b0 : bv 32 := 0x0005c503.
Lemma F_5e0b0 : fetch_word Asan.M.loaded_segments (0x5e100 : word) = Some W_5e0b0.
Proof. vm_refl. Qed.
Lemma D_5e0b0 : decode_any W_5e0b0 = Some (Load SZ1 false 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0b4 : bv 32 := 0xfe0506e3.
Lemma F_5e0b4 : fetch_word Asan.M.loaded_segments (0x5e104 : word) = Some W_5e0b4.
Proof. vm_refl. Qed.
Lemma D_5e0b4 : decode_any W_5e0b4 = Some (Branch BC_EQ 10 0 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0b8 : bv 32 := 0x058cb503.
Lemma F_5e0b8 : fetch_word Asan.M.loaded_segments (0x5e108 : word) = Some W_5e0b8.
Proof. vm_refl. Qed.
Lemma D_5e0b8 : decode_any W_5e0b8 = Some (Load SZ8 true 10 25 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0bc : bv 32 := 0xffb50613.
Lemma F_5e0bc : fetch_word Asan.M.loaded_segments (0x5e10c : word) = Some W_5e0bc.
Proof. vm_refl. Qed.
Lemma D_5e0bc : decode_any W_5e0bc = Some (OpImm ALU_ADD 12 10 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0c0 : bv 32 := 0x00aa1533.
Lemma F_5e0c0 : fetch_word Asan.M.loaded_segments (0x5e110 : word) = Some W_5e0c0.
Proof. vm_refl. Qed.
Lemma D_5e0c0 : decode_any W_5e0c0 = Some (Op ALU_SLL 10 20 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0c4 : bv 32 := 0x00c39633.
Lemma F_5e0c4 : fetch_word Asan.M.loaded_segments (0x5e114 : word) = Some W_5e0c4.
Proof. vm_refl. Qed.
Lemma D_5e0c4 : decode_any W_5e0c4 = Some (Op ALU_SLL 12 7 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0c8 : bv 32 := 0x00a40533.
Lemma F_5e0c8 : fetch_word Asan.M.loaded_segments (0x5e118 : word) = Some W_5e0c8.
Proof. vm_refl. Qed.
Lemma D_5e0c8 : decode_any W_5e0c8 = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0cc : bv 32 := 0x00c50533.
Lemma F_5e0cc : fetch_word Asan.M.loaded_segments (0x5e11c : word) = Some W_5e0cc.
Proof. vm_refl. Qed.
Lemma D_5e0cc : decode_any W_5e0cc = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0d0 : bv 32 := 0x015d9633.
Lemma F_5e0d0 : fetch_word Asan.M.loaded_segments (0x5e120 : word) = Some W_5e0d0.
Proof. vm_refl. Qed.
Lemma D_5e0d0 : decode_any W_5e0d0 = Some (Op ALU_SLL 12 27 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0d4 : bv 32 := 0x00c50533.
Lemma F_5e0d4 : fetch_word Asan.M.loaded_segments (0x5e124 : word) = Some W_5e0d4.
Proof. vm_refl. Qed.
Lemma D_5e0d4 : decode_any W_5e0d4 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0d8 : bv 32 := 0x01853603.
Lemma F_5e0d8 : fetch_word Asan.M.loaded_segments (0x5e128 : word) = Some W_5e0d8.
Proof. vm_refl. Qed.
Lemma D_5e0d8 : decode_any W_5e0d8 = Some (Load SZ8 true 12 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0dc : bv 32 := 0xfcc972e3.
Lemma F_5e0dc : fetch_word Asan.M.loaded_segments (0x5e12c : word) = Some W_5e0dc.
Proof. vm_refl. Qed.
Lemma D_5e0dc : decode_any W_5e0dc = Some (Branch BC_GEU 18 12 8132, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0e0 : bv 32 := 0xfc9670e3.
Lemma F_5e0e0 : fetch_word Asan.M.loaded_segments (0x5e130 : word) = Some W_5e0e0.
Proof. vm_refl. Qed.
Lemma D_5e0e0 : decode_any W_5e0e0 = Some (Branch BC_GEU 12 9 8128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0e4 : bv 32 := 0x01a58023.
Lemma F_5e0e4 : fetch_word Asan.M.loaded_segments (0x5e134 : word) = Some W_5e0e4.
Proof. vm_refl. Qed.
Lemma D_5e0e4 : decode_any W_5e0e4 = Some (Store SZ1 11 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0e8 : bv 32 := 0x000b3583.
Lemma F_5e0e8 : fetch_word Asan.M.loaded_segments (0x5e138 : word) = Some W_5e0e8.
Proof. vm_refl. Qed.
Lemma D_5e0e8 : decode_any W_5e0e8 = Some (Load SZ8 true 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0ec : bv 32 := 0xfff58613.
Lemma F_5e0ec : fetch_word Asan.M.loaded_segments (0x5e13c : word) = Some W_5e0ec.
Proof. vm_refl. Qed.
Lemma D_5e0ec : decode_any W_5e0ec = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0f0 : bv 32 := 0x00c5b6b3.
Lemma F_5e0f0 : fetch_word Asan.M.loaded_segments (0x5e140 : word) = Some W_5e0f0.
Proof. vm_refl. Qed.
Lemma D_5e0f0 : decode_any W_5e0f0 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0f4 : bv 32 := 0xfff68693.
Lemma F_5e0f4 : fetch_word Asan.M.loaded_segments (0x5e144 : word) = Some W_5e0f4.
Proof. vm_refl. Qed.
Lemma D_5e0f4 : decode_any W_5e0f4 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0f8 : bv 32 := 0x00c6f6b3.
Lemma F_5e0f8 : fetch_word Asan.M.loaded_segments (0x5e148 : word) = Some W_5e0f8.
Proof. vm_refl. Qed.
Lemma D_5e0f8 : decode_any W_5e0f8 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0fc : bv 32 := 0x02a6fc63.
Lemma F_5e0fc : fetch_word Asan.M.loaded_segments (0x5e14c : word) = Some W_5e0fc.
Proof. vm_refl. Qed.
Lemma D_5e0fc : decode_any W_5e0fc = Some (Branch BC_GEU 13 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e100 : bv 32 := 0x01813683.
Lemma F_5e100 : fetch_word Asan.M.loaded_segments (0x5e150 : word) = Some W_5e100.
Proof. vm_refl. Qed.
Lemma D_5e100 : decode_any W_5e100 = Some (Load SZ8 true 13 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e104 : bv 32 := 0x0006b803.
Lemma F_5e104 : fetch_word Asan.M.loaded_segments (0x5e154 : word) = Some W_5e104.
Proof. vm_refl. Qed.
Lemma D_5e104 : decode_any W_5e104 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e108 : bv 32 := 0x01013683.
Lemma F_5e108 : fetch_word Asan.M.loaded_segments (0x5e158 : word) = Some W_5e108.
Proof. vm_refl. Qed.
Lemma D_5e108 : decode_any W_5e108 = Some (Load SZ8 true 13 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e10c : bv 32 := 0x0006b683.
Lemma F_5e10c : fetch_word Asan.M.loaded_segments (0x5e15c : word) = Some W_5e10c.
Proof. vm_refl. Qed.
Lemma D_5e10c : decode_any W_5e10c = Some (Load SZ8 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e110 : bv 32 := 0xfff80793.
Lemma F_5e110 : fetch_word Asan.M.loaded_segments (0x5e160 : word) = Some W_5e110.
Proof. vm_refl. Qed.
Lemma D_5e110 : decode_any W_5e110 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e114 : bv 32 := 0x00a7f463.
Lemma F_5e114 : fetch_word Asan.M.loaded_segments (0x5e164 : word) = Some W_5e114.
Proof. vm_refl. Qed.
Lemma D_5e114 : decode_any W_5e114 = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e11c : bv 32 := 0x00813703.
Lemma F_5e11c : fetch_word Asan.M.loaded_segments (0x5e16c : word) = Some W_5e11c.
Proof. vm_refl. Qed.
Lemma D_5e11c : decode_any W_5e11c = Some (Load SZ8 true 14 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e120 : bv 32 := 0x00073283.
Lemma F_5e120 : fetch_word Asan.M.loaded_segments (0x5e170 : word) = Some W_5e120.
Proof. vm_refl. Qed.
Lemma D_5e120 : decode_any W_5e120 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e124 : bv 32 := 0x0032d713.
Lemma F_5e124 : fetch_word Asan.M.loaded_segments (0x5e174 : word) = Some W_5e124.
Proof. vm_refl. Qed.
Lemma D_5e124 : decode_any W_5e124 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e128 : bv 32 := 0x00b708b3.
Lemma F_5e128 : fetch_word Asan.M.loaded_segments (0x5e178 : word) = Some W_5e128.
Proof. vm_refl. Qed.
Lemma D_5e128 : decode_any W_5e128 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e12c : bv 32 := 0x02a2e863.
Lemma F_5e12c : fetch_word Asan.M.loaded_segments (0x5e17c : word) = Some W_5e12c.
Proof. vm_refl. Qed.
Lemma D_5e12c : decode_any W_5e12c = Some (Branch BC_LTU 5 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e130 : bv 32 := 0x02a8f663.
Lemma F_5e130 : fetch_word Asan.M.loaded_segments (0x5e180 : word) = Some W_5e130.
Proof. vm_refl. Qed.
Lemma D_5e130 : decode_any W_5e130 = Some (Branch BC_GEU 17 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e134 : bv 32 := 0xf54e6ce3.
Lemma F_5e134 : fetch_word Asan.M.loaded_segments (0x5e184 : word) = Some W_5e134.
Proof. vm_refl. Qed.
Lemma D_5e134 : decode_any W_5e134 = Some (Branch BC_LTU 28 20 8024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e138 : bv 32 := 0x00355513.
Lemma F_5e138 : fetch_word Asan.M.loaded_segments (0x5e188 : word) = Some W_5e138.
Proof. vm_refl. Qed.
Lemma D_5e138 : decode_any W_5e138 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e13c : bv 32 := 0x00a585b3.
Lemma F_5e13c : fetch_word Asan.M.loaded_segments (0x5e18c : word) = Some W_5e13c.
Proof. vm_refl. Qed.
Lemma D_5e13c : decode_any W_5e13c = Some (Op ALU_ADD 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e140 : bv 32 := 0x00100513.
Lemma F_5e140 : fetch_word Asan.M.loaded_segments (0x5e190 : word) = Some W_5e140.
Proof. vm_refl. Qed.
Lemma D_5e140 : decode_any W_5e140 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e144 : bv 32 := 0x0175b023.
Lemma F_5e144 : fetch_word Asan.M.loaded_segments (0x5e194 : word) = Some W_5e144.
Proof. vm_refl. Qed.
Lemma D_5e144 : decode_any W_5e144 = Some (Store SZ8 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e148 : bv 32 := 0x01455633.
Lemma F_5e148 : fetch_word Asan.M.loaded_segments (0x5e198 : word) = Some W_5e148.
Proof. vm_refl. Qed.
Lemma D_5e148 : decode_any W_5e148 = Some (Op ALU_SRL 12 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e14c : bv 32 := 0x00858593.
Lemma F_5e14c : fetch_word Asan.M.loaded_segments (0x5e19c : word) = Some W_5e14c.
Proof. vm_refl. Qed.
Lemma D_5e14c : decode_any W_5e14c = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e150 : bv 32 := 0x00150513.
Lemma F_5e150 : fetch_word Asan.M.loaded_segments (0x5e1a0 : word) = Some W_5e150.
Proof. vm_refl. Qed.
Lemma D_5e150 : decode_any W_5e150 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e154 : bv 32 := 0xfe0608e3.
Lemma F_5e154 : fetch_word Asan.M.loaded_segments (0x5e1a4 : word) = Some W_5e154.
Proof. vm_refl. Qed.
Lemma D_5e154 : decode_any W_5e154 = Some (Branch BC_EQ 12 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e158 : bv 32 := 0xf49ff06f.
Lemma F_5e158 : fetch_word Asan.M.loaded_segments (0x5e1a8 : word) = Some W_5e158.
Proof. vm_refl. Qed.
Lemma D_5e158 : decode_any W_5e158 = Some (Jal 0 2096968, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e220 : bv 32 := 0x060c8023.
Lemma F_5e220 : fetch_word Asan.M.loaded_segments (0x5e270 : word) = Some W_5e220.
Proof. vm_refl. Qed.
Lemma D_5e220 : decode_any W_5e220 = Some (Store SZ1 25 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e224 : bv 32 := 0x08813083.
Lemma F_5e224 : fetch_word Asan.M.loaded_segments (0x5e274 : word) = Some W_5e224.
Proof. vm_refl. Qed.
Lemma D_5e224 : decode_any W_5e224 = Some (Load SZ8 true 1 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e228 : bv 32 := 0x08013403.
Lemma F_5e228 : fetch_word Asan.M.loaded_segments (0x5e278 : word) = Some W_5e228.
Proof. vm_refl. Qed.
Lemma D_5e228 : decode_any W_5e228 = Some (Load SZ8 true 8 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e22c : bv 32 := 0x07813483.
Lemma F_5e22c : fetch_word Asan.M.loaded_segments (0x5e27c : word) = Some W_5e22c.
Proof. vm_refl. Qed.
Lemma D_5e22c : decode_any W_5e22c = Some (Load SZ8 true 9 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e230 : bv 32 := 0x07013903.
Lemma F_5e230 : fetch_word Asan.M.loaded_segments (0x5e280 : word) = Some W_5e230.
Proof. vm_refl. Qed.
Lemma D_5e230 : decode_any W_5e230 = Some (Load SZ8 true 18 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e234 : bv 32 := 0x06813983.
Lemma F_5e234 : fetch_word Asan.M.loaded_segments (0x5e284 : word) = Some W_5e234.
Proof. vm_refl. Qed.
Lemma D_5e234 : decode_any W_5e234 = Some (Load SZ8 true 19 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e238 : bv 32 := 0x06013a03.
Lemma F_5e238 : fetch_word Asan.M.loaded_segments (0x5e288 : word) = Some W_5e238.
Proof. vm_refl. Qed.
Lemma D_5e238 : decode_any W_5e238 = Some (Load SZ8 true 20 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e23c : bv 32 := 0x05813a83.
Lemma F_5e23c : fetch_word Asan.M.loaded_segments (0x5e28c : word) = Some W_5e23c.
Proof. vm_refl. Qed.
Lemma D_5e23c : decode_any W_5e23c = Some (Load SZ8 true 21 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e240 : bv 32 := 0x05013b03.
Lemma F_5e240 : fetch_word Asan.M.loaded_segments (0x5e290 : word) = Some W_5e240.
Proof. vm_refl. Qed.
Lemma D_5e240 : decode_any W_5e240 = Some (Load SZ8 true 22 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e244 : bv 32 := 0x04813b83.
Lemma F_5e244 : fetch_word Asan.M.loaded_segments (0x5e294 : word) = Some W_5e244.
Proof. vm_refl. Qed.
Lemma D_5e244 : decode_any W_5e244 = Some (Load SZ8 true 23 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e248 : bv 32 := 0x04013c03.
Lemma F_5e248 : fetch_word Asan.M.loaded_segments (0x5e298 : word) = Some W_5e248.
Proof. vm_refl. Qed.
Lemma D_5e248 : decode_any W_5e248 = Some (Load SZ8 true 24 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e24c : bv 32 := 0x03813c83.
Lemma F_5e24c : fetch_word Asan.M.loaded_segments (0x5e29c : word) = Some W_5e24c.
Proof. vm_refl. Qed.
Lemma D_5e24c : decode_any W_5e24c = Some (Load SZ8 true 25 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e250 : bv 32 := 0x03013d03.
Lemma F_5e250 : fetch_word Asan.M.loaded_segments (0x5e2a0 : word) = Some W_5e250.
Proof. vm_refl. Qed.
Lemma D_5e250 : decode_any W_5e250 = Some (Load SZ8 true 26 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e254 : bv 32 := 0x02813d83.
Lemma F_5e254 : fetch_word Asan.M.loaded_segments (0x5e2a4 : word) = Some W_5e254.
Proof. vm_refl. Qed.
Lemma D_5e254 : decode_any W_5e254 = Some (Load SZ8 true 27 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e258 : bv 32 := 0x09010113.
Lemma F_5e258 : fetch_word Asan.M.loaded_segments (0x5e2a8 : word) = Some W_5e258.
Proof. vm_refl. Qed.
Lemma D_5e258 : decode_any W_5e258 = Some (OpImm ALU_ADD 2 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e25c : bv 32 := 0x00008067.
Lemma F_5e25c : fetch_word Asan.M.loaded_segments (0x5e2ac : word) = Some W_5e25c.
Proof. vm_refl. Qed.
Lemma D_5e25c : decode_any W_5e25c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e260 : bv 32 := 0x00100593.
Lemma F_5e260 : fetch_word Asan.M.loaded_segments (0x5e2b0 : word) = Some W_5e260.
Proof. vm_refl. Qed.
Lemma D_5e260 : decode_any W_5e260 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e264 : bv 32 := 0x06b50023.
Lemma F_5e264 : fetch_word Asan.M.loaded_segments (0x5e2b4 : word) = Some W_5e264.
Proof. vm_refl. Qed.
Lemma D_5e264 : decode_any W_5e264 = Some (Store SZ1 10 11 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e268 : bv 32 := 0x00008067.
Lemma F_5e268 : fetch_word Asan.M.loaded_segments (0x5e2b8 : word) = Some W_5e268.
Proof. vm_refl. Qed.
Lemma D_5e268 : decode_any W_5e268 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e538 : bv 32 := 0xfe010113.
Lemma F_5e538 : fetch_word Asan.M.loaded_segments (0x5e588 : word) = Some W_5e538.
Proof. vm_refl. Qed.
Lemma D_5e538 : decode_any W_5e538 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e53c : bv 32 := 0x00113c23.
Lemma F_5e53c : fetch_word Asan.M.loaded_segments (0x5e58c : word) = Some W_5e53c.
Proof. vm_refl. Qed.
Lemma D_5e53c : decode_any W_5e53c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e540 : bv 32 := 0x00813823.
Lemma F_5e540 : fetch_word Asan.M.loaded_segments (0x5e590 : word) = Some W_5e540.
Proof. vm_refl. Qed.
Lemma D_5e540 : decode_any W_5e540 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e544 : bv 32 := 0x00913423.
Lemma F_5e544 : fetch_word Asan.M.loaded_segments (0x5e594 : word) = Some W_5e544.
Proof. vm_refl. Qed.
Lemma D_5e544 : decode_any W_5e544 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e548 : bv 32 := 0x01213023.
Lemma F_5e548 : fetch_word Asan.M.loaded_segments (0x5e598 : word) = Some W_5e548.
Proof. vm_refl. Qed.
Lemma D_5e548 : decode_any W_5e548 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e54c : bv 32 := 0x02010413.
Lemma F_5e54c : fetch_word Asan.M.loaded_segments (0x5e59c : word) = Some W_5e54c.
Proof. vm_refl. Qed.
Lemma D_5e54c : decode_any W_5e54c = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e550 : bv 32 := 0x000dc517.
Lemma F_5e550 : fetch_word Asan.M.loaded_segments (0x5e5a0 : word) = Some W_5e550.
Proof. vm_refl. Qed.
Lemma D_5e550 : decode_any W_5e550 = Some (Auipc 10 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e554 : bv 32 := 0xa1050513.
Lemma F_5e554 : fetch_word Asan.M.loaded_segments (0x5e5a4 : word) = Some W_5e554.
Proof. vm_refl. Qed.
Lemma D_5e554 : decode_any W_5e554 = Some (OpImm ALU_ADD 10 10 2576, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e558 : bv 32 := 0x7cc050ef.
Lemma F_5e558 : fetch_word Asan.M.loaded_segments (0x5e5a8 : word) = Some W_5e558.
Proof. vm_refl. Qed.
Lemma D_5e558 : decode_any W_5e558 = Some (Jal 1 22476, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e55c : bv 32 := 0x00053483.
Lemma F_5e55c : fetch_word Asan.M.loaded_segments (0x5e5ac : word) = Some W_5e55c.
Proof. vm_refl. Qed.
Lemma D_5e55c : decode_any W_5e55c = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e560 : bv 32 := 0x08048863.
Lemma F_5e560 : fetch_word Asan.M.loaded_segments (0x5e5b0 : word) = Some W_5e560.
Proof. vm_refl. Qed.
Lemma D_5e560 : decode_any W_5e560 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e564 : bv 32 := 0x0604c503.
Lemma F_5e564 : fetch_word Asan.M.loaded_segments (0x5e5b4 : word) = Some W_5e564.
Proof. vm_refl. Qed.
Lemma D_5e564 : decode_any W_5e564 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e568 : bv 32 := 0x0584b903.
Lemma F_5e568 : fetch_word Asan.M.loaded_segments (0x5e5b8 : word) = Some W_5e568.
Proof. vm_refl. Qed.
Lemma D_5e568 : decode_any W_5e568 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e56c : bv 32 := 0x00050863.
Lemma F_5e56c : fetch_word Asan.M.loaded_segments (0x5e5bc : word) = Some W_5e56c.
Proof. vm_refl. Qed.
Lemma D_5e56c : decode_any W_5e56c = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e570 : bv 32 := 0x00048513.
Lemma F_5e570 : fetch_word Asan.M.loaded_segments (0x5e5c0 : word) = Some W_5e570.
Proof. vm_refl. Qed.
Lemma D_5e570 : decode_any W_5e570 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e574 : bv 32 := 0x00040593.
Lemma F_5e574 : fetch_word Asan.M.loaded_segments (0x5e5c4 : word) = Some W_5e574.
Proof. vm_refl. Qed.
Lemma D_5e574 : decode_any W_5e574 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e578 : bv 32 := 0xa01ff0ef.
Lemma F_5e578 : fetch_word Asan.M.loaded_segments (0x5e5c8 : word) = Some W_5e578.
Proof. vm_refl. Qed.
Lemma D_5e578 : decode_any W_5e578 = Some (Jal 1 2095616, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e57c : bv 32 := 0xff990593.
Lemma F_5e57c : fetch_word Asan.M.loaded_segments (0x5e5cc : word) = Some W_5e57c.
Proof. vm_refl. Qed.
Lemma D_5e57c : decode_any W_5e57c = Some (OpImm ALU_ADD 11 18 4089, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e580 : bv 32 := 0x00100513.
Lemma F_5e580 : fetch_word Asan.M.loaded_segments (0x5e5d0 : word) = Some W_5e580.
Proof. vm_refl. Qed.
Lemma D_5e580 : decode_any W_5e580 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e584 : bv 32 := 0x00b51533.
Lemma F_5e584 : fetch_word Asan.M.loaded_segments (0x5e5d4 : word) = Some W_5e584.
Proof. vm_refl. Qed.
Lemma D_5e584 : decode_any W_5e584 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e588 : bv 32 := 0x0005061b.
Lemma F_5e588 : fetch_word Asan.M.loaded_segments (0x5e5d8 : word) = Some W_5e588.
Proof. vm_refl. Qed.
Lemma D_5e588 : decode_any W_5e588 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e58c : bv 32 := 0x08c05263.
Lemma F_5e58c : fetch_word Asan.M.loaded_segments (0x5e5dc : word) = Some W_5e58c.
Proof. vm_refl. Qed.
Lemma D_5e58c : decode_any W_5e58c = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e590 : bv 32 := 0x000016b7.
Lemma F_5e590 : fetch_word Asan.M.loaded_segments (0x5e5e0 : word) = Some W_5e590.
Proof. vm_refl. Qed.
Lemma D_5e590 : decode_any W_5e590 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e594 : bv 32 := 0xff190613.
Lemma F_5e594 : fetch_word Asan.M.loaded_segments (0x5e5e4 : word) = Some W_5e594.
Proof. vm_refl. Qed.
Lemma D_5e594 : decode_any W_5e594 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e598 : bv 32 := 0x20000713.
Lemma F_5e598 : fetch_word Asan.M.loaded_segments (0x5e5e8 : word) = Some W_5e598.
Proof. vm_refl. Qed.
Lemma D_5e598 : decode_any W_5e598 = Some (OpImm ALU_ADD 14 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e59c : bv 32 := 0xfff00793.
Lemma F_5e59c : fetch_word Asan.M.loaded_segments (0x5e5ec : word) = Some W_5e59c.
Proof. vm_refl. Qed.
Lemma D_5e59c : decode_any W_5e59c = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5a0 : bv 32 := 0x00c71733.
Lemma F_5e5a0 : fetch_word Asan.M.loaded_segments (0x5e5f0 : word) = Some W_5e5a0.
Proof. vm_refl. Qed.
Lemma D_5e5a0 : decode_any W_5e5a0 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5a4 : bv 32 := 0x0084b603.
Lemma F_5e5a4 : fetch_word Asan.M.loaded_segments (0x5e5f4 : word) = Some W_5e5a4.
Proof. vm_refl. Qed.
Lemma D_5e5a4 : decode_any W_5e5a4 = Some (Load SZ8 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5a8 : bv 32 := 0x00b797b3.
Lemma F_5e5a8 : fetch_word Asan.M.loaded_segments (0x5e5f8 : word) = Some W_5e5a8.
Proof. vm_refl. Qed.
Lemma D_5e5a8 : decode_any W_5e5a8 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5ac : bv 32 := 0xfff50813.
Lemma F_5e5ac : fetch_word Asan.M.loaded_segments (0x5e5fc : word) = Some W_5e5ac.
Proof. vm_refl. Qed.
Lemma D_5e5ac : decode_any W_5e5ac = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5b0 : bv 32 := 0x00d485b3.
Lemma F_5e5b0 : fetch_word Asan.M.loaded_segments (0x5e600 : word) = Some W_5e5b0.
Proof. vm_refl. Qed.
Lemma D_5e5b0 : decode_any W_5e5b0 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5b4 : bv 32 := 0x00e586b3.
Lemma F_5e5b4 : fetch_word Asan.M.loaded_segments (0x5e604 : word) = Some W_5e5b4.
Proof. vm_refl. Qed.
Lemma D_5e5b4 : decode_any W_5e5b4 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5b8 : bv 32 := 0xfff7c713.
Lemma F_5e5b8 : fetch_word Asan.M.loaded_segments (0x5e608 : word) = Some W_5e5b8.
Proof. vm_refl. Qed.
Lemma D_5e5b8 : decode_any W_5e5b8 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5bc : bv 32 := 0x02081813.
Lemma F_5e5bc : fetch_word Asan.M.loaded_segments (0x5e60c : word) = Some W_5e5bc.
Proof. vm_refl. Qed.
Lemma D_5e5bc : decode_any W_5e5bc = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5c0 : bv 32 := 0x02085793.
Lemma F_5e5c0 : fetch_word Asan.M.loaded_segments (0x5e610 : word) = Some W_5e5c0.
Proof. vm_refl. Qed.
Lemma D_5e5c0 : decode_any W_5e5c0 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5c4 : bv 32 := 0x00f607b3.
Lemma F_5e5c4 : fetch_word Asan.M.loaded_segments (0x5e614 : word) = Some W_5e5c4.
Proof. vm_refl. Qed.
Lemma D_5e5c4 : decode_any W_5e5c4 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5c8 : bv 32 := 0x00178813.
Lemma F_5e5c8 : fetch_word Asan.M.loaded_segments (0x5e618 : word) = Some W_5e5c8.
Proof. vm_refl. Qed.
Lemma D_5e5c8 : decode_any W_5e5c8 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5cc : bv 32 := 0x00e678b3.
Lemma F_5e5cc : fetch_word Asan.M.loaded_segments (0x5e61c : word) = Some W_5e5cc.
Proof. vm_refl. Qed.
Lemma D_5e5cc : decode_any W_5e5cc = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5d0 : bv 32 := 0x011687b3.
Lemma F_5e5d0 : fetch_word Asan.M.loaded_segments (0x5e620 : word) = Some W_5e5d0.
Proof. vm_refl. Qed.
Lemma D_5e5d0 : decode_any W_5e5d0 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5d4 : bv 32 := 0x0007c283.
Lemma F_5e5d4 : fetch_word Asan.M.loaded_segments (0x5e624 : word) = Some W_5e5d4.
Proof. vm_refl. Qed.
Lemma D_5e5d4 : decode_any W_5e5d4 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5d8 : bv 32 := 0x06028663.
Lemma F_5e5d8 : fetch_word Asan.M.loaded_segments (0x5e628 : word) = Some W_5e5d8.
Proof. vm_refl. Qed.
Lemma D_5e5d8 : decode_any W_5e5d8 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5dc : bv 32 := 0xfff5051b.
Lemma F_5e5dc : fetch_word Asan.M.loaded_segments (0x5e62c : word) = Some W_5e5dc.
Proof. vm_refl. Qed.
Lemma D_5e5dc : decode_any W_5e5dc = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5e0 : bv 32 := 0x00160613.
Lemma F_5e5e0 : fetch_word Asan.M.loaded_segments (0x5e630 : word) = Some W_5e5e0.
Proof. vm_refl. Qed.
Lemma D_5e5e0 : decode_any W_5e5e0 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5e4 : bv 32 := 0xfe0514e3.
Lemma F_5e5e4 : fetch_word Asan.M.loaded_segments (0x5e634 : word) = Some W_5e5e4.
Proof. vm_refl. Qed.
Lemma D_5e5e4 : decode_any W_5e5e4 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e644 : bv 32 := 0x00160613.
Lemma F_5e644 : fetch_word Asan.M.loaded_segments (0x5e694 : word) = Some W_5e644.
Proof. vm_refl. Qed.
Lemma D_5e644 : decode_any W_5e644 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e648 : bv 32 := 0x00100513.
Lemma F_5e648 : fetch_word Asan.M.loaded_segments (0x5e698 : word) = Some W_5e648.
Proof. vm_refl. Qed.
Lemma D_5e648 : decode_any W_5e648 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e64c : bv 32 := 0xffb90693.
Lemma F_5e64c : fetch_word Asan.M.loaded_segments (0x5e69c : word) = Some W_5e64c.
Proof. vm_refl. Qed.
Lemma D_5e64c : decode_any W_5e64c = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e650 : bv 32 := 0x00789893.
Lemma F_5e650 : fetch_word Asan.M.loaded_segments (0x5e6a0 : word) = Some W_5e650.
Proof. vm_refl. Qed.
Lemma D_5e650 : decode_any W_5e650 = Some (ShiftImm ALU_SLL 17 17 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e654 : bv 32 := 0x00c4b423.
Lemma F_5e654 : fetch_word Asan.M.loaded_segments (0x5e6a4 : word) = Some W_5e654.
Proof. vm_refl. Qed.
Lemma D_5e654 : decode_any W_5e654 = Some (Store SZ8 9 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e658 : bv 32 := 0x00a78023.
Lemma F_5e658 : fetch_word Asan.M.loaded_segments (0x5e6a8 : word) = Some W_5e658.
Proof. vm_refl. Qed.
Lemma D_5e658 : decode_any W_5e658 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e65c : bv 32 := 0x00d51633.
Lemma F_5e65c : fetch_word Asan.M.loaded_segments (0x5e6ac : word) = Some W_5e65c.
Proof. vm_refl. Qed.
Lemma D_5e65c : decode_any W_5e65c = Some (Op ALU_SLL 12 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e660 : bv 32 := 0x01251533.
Lemma F_5e660 : fetch_word Asan.M.loaded_segments (0x5e6b0 : word) = Some W_5e660.
Proof. vm_refl. Qed.
Lemma D_5e660 : decode_any W_5e660 = Some (Op ALU_SLL 10 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e664 : bv 32 := 0x00c585b3.
Lemma F_5e664 : fetch_word Asan.M.loaded_segments (0x5e6b4 : word) = Some W_5e664.
Proof. vm_refl. Qed.
Lemma D_5e664 : decode_any W_5e664 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e668 : bv 32 := 0x01150533.
Lemma F_5e668 : fetch_word Asan.M.loaded_segments (0x5e6b8 : word) = Some W_5e668.
Proof. vm_refl. Qed.
Lemma D_5e668 : decode_any W_5e668 = Some (Op ALU_ADD 10 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e66c : bv 32 := 0x00a584b3.
Lemma F_5e66c : fetch_word Asan.M.loaded_segments (0x5e6bc : word) = Some W_5e66c.
Proof. vm_refl. Qed.
Lemma D_5e66c : decode_any W_5e66c = Some (Op ALU_ADD 9 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e670 : bv 32 := 0x0084bc23.
Lemma F_5e670 : fetch_word Asan.M.loaded_segments (0x5e6c0 : word) = Some W_5e670.
Proof. vm_refl. Qed.
Lemma D_5e670 : decode_any W_5e670 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e674 : bv 32 := 0x06f4bc23.
Lemma F_5e674 : fetch_word Asan.M.loaded_segments (0x5e6c4 : word) = Some W_5e674.
Proof. vm_refl. Qed.
Lemma D_5e674 : decode_any W_5e674 = Some (Store SZ8 9 15 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e678 : bv 32 := 0x00048513.
Lemma F_5e678 : fetch_word Asan.M.loaded_segments (0x5e6c8 : word) = Some W_5e678.
Proof. vm_refl. Qed.
Lemma D_5e678 : decode_any W_5e678 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e67c : bv 32 := 0x654000ef.
Lemma F_5e67c : fetch_word Asan.M.loaded_segments (0x5e6cc : word) = Some W_5e67c.
Proof. vm_refl. Qed.
Lemma D_5e67c : decode_any W_5e67c = Some (Jal 1 1620, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e680 : bv 32 := 0x00050593.
Lemma F_5e680 : fetch_word Asan.M.loaded_segments (0x5e6d0 : word) = Some W_5e680.
Proof. vm_refl. Qed.
Lemma D_5e680 : decode_any W_5e680 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e684 : bv 32 := 0x00048513.
Lemma F_5e684 : fetch_word Asan.M.loaded_segments (0x5e6d4 : word) = Some W_5e684.
Proof. vm_refl. Qed.
Lemma D_5e684 : decode_any W_5e684 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e688 : bv 32 := 0x00000613.
Lemma F_5e688 : fetch_word Asan.M.loaded_segments (0x5e6d8 : word) = Some W_5e688.
Proof. vm_refl. Qed.
Lemma D_5e688 : decode_any W_5e688 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e68c : bv 32 := 0x0005b023.
Lemma F_5e68c : fetch_word Asan.M.loaded_segments (0x5e6dc : word) = Some W_5e68c.
Proof. vm_refl. Qed.
Lemma D_5e68c : decode_any W_5e68c = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e690 : bv 32 := 0x0005b423.
Lemma F_5e690 : fetch_word Asan.M.loaded_segments (0x5e6e0 : word) = Some W_5e690.
Proof. vm_refl. Qed.
Lemma D_5e690 : decode_any W_5e690 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e694 : bv 32 := 0x01813083.
Lemma F_5e694 : fetch_word Asan.M.loaded_segments (0x5e6e4 : word) = Some W_5e694.
Proof. vm_refl. Qed.
Lemma D_5e694 : decode_any W_5e694 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e698 : bv 32 := 0x01013403.
Lemma F_5e698 : fetch_word Asan.M.loaded_segments (0x5e6e8 : word) = Some W_5e698.
Proof. vm_refl. Qed.
Lemma D_5e698 : decode_any W_5e698 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e69c : bv 32 := 0x00813483.
Lemma F_5e69c : fetch_word Asan.M.loaded_segments (0x5e6ec : word) = Some W_5e69c.
Proof. vm_refl. Qed.
Lemma D_5e69c : decode_any W_5e69c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6a0 : bv 32 := 0x00013903.
Lemma F_5e6a0 : fetch_word Asan.M.loaded_segments (0x5e6f0 : word) = Some W_5e6a0.
Proof. vm_refl. Qed.
Lemma D_5e6a0 : decode_any W_5e6a0 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6a4 : bv 32 := 0x02010113.
Lemma F_5e6a4 : fetch_word Asan.M.loaded_segments (0x5e6f4 : word) = Some W_5e6a4.
Proof. vm_refl. Qed.
Lemma D_5e6a4 : decode_any W_5e6a4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6a8 : bv 32 := 0x00008067.
Lemma F_5e6a8 : fetch_word Asan.M.loaded_segments (0x5e6f8 : word) = Some W_5e6a8.
Proof. vm_refl. Qed.
Lemma D_5e6a8 : decode_any W_5e6a8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e864 : bv 32 := 0xfe010113.
Lemma F_5e864 : fetch_word Asan.M.loaded_segments (0x5e8b4 : word) = Some W_5e864.
Proof. vm_refl. Qed.
Lemma D_5e864 : decode_any W_5e864 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e868 : bv 32 := 0x00113c23.
Lemma F_5e868 : fetch_word Asan.M.loaded_segments (0x5e8b8 : word) = Some W_5e868.
Proof. vm_refl. Qed.
Lemma D_5e868 : decode_any W_5e868 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e86c : bv 32 := 0x00813823.
Lemma F_5e86c : fetch_word Asan.M.loaded_segments (0x5e8bc : word) = Some W_5e86c.
Proof. vm_refl. Qed.
Lemma D_5e86c : decode_any W_5e86c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e870 : bv 32 := 0x00913423.
Lemma F_5e870 : fetch_word Asan.M.loaded_segments (0x5e8c0 : word) = Some W_5e870.
Proof. vm_refl. Qed.
Lemma D_5e870 : decode_any W_5e870 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e874 : bv 32 := 0x01213023.
Lemma F_5e874 : fetch_word Asan.M.loaded_segments (0x5e8c4 : word) = Some W_5e874.
Proof. vm_refl. Qed.
Lemma D_5e874 : decode_any W_5e874 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e878 : bv 32 := 0x02010413.
Lemma F_5e878 : fetch_word Asan.M.loaded_segments (0x5e8c8 : word) = Some W_5e878.
Proof. vm_refl. Qed.
Lemma D_5e878 : decode_any W_5e878 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e87c : bv 32 := 0x000db517.
Lemma F_5e87c : fetch_word Asan.M.loaded_segments (0x5e8cc : word) = Some W_5e87c.
Proof. vm_refl. Qed.
Lemma D_5e87c : decode_any W_5e87c = Some (Auipc 10 219, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e880 : bv 32 := 0x6e450513.
Lemma F_5e880 : fetch_word Asan.M.loaded_segments (0x5e8d0 : word) = Some W_5e880.
Proof. vm_refl. Qed.
Lemma D_5e880 : decode_any W_5e880 = Some (OpImm ALU_ADD 10 10 1764, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e884 : bv 32 := 0x4a0050ef.
Lemma F_5e884 : fetch_word Asan.M.loaded_segments (0x5e8d4 : word) = Some W_5e884.
Proof. vm_refl. Qed.
Lemma D_5e884 : decode_any W_5e884 = Some (Jal 1 21664, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e888 : bv 32 := 0x00053483.
Lemma F_5e888 : fetch_word Asan.M.loaded_segments (0x5e8d8 : word) = Some W_5e888.
Proof. vm_refl. Qed.
Lemma D_5e888 : decode_any W_5e888 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e88c : bv 32 := 0x08048863.
Lemma F_5e88c : fetch_word Asan.M.loaded_segments (0x5e8dc : word) = Some W_5e88c.
Proof. vm_refl. Qed.
Lemma D_5e88c : decode_any W_5e88c = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e890 : bv 32 := 0x0604c503.
Lemma F_5e890 : fetch_word Asan.M.loaded_segments (0x5e8e0 : word) = Some W_5e890.
Proof. vm_refl. Qed.
Lemma D_5e890 : decode_any W_5e890 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e894 : bv 32 := 0x0584b903.
Lemma F_5e894 : fetch_word Asan.M.loaded_segments (0x5e8e4 : word) = Some W_5e894.
Proof. vm_refl. Qed.
Lemma D_5e894 : decode_any W_5e894 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e898 : bv 32 := 0x00050863.
Lemma F_5e898 : fetch_word Asan.M.loaded_segments (0x5e8e8 : word) = Some W_5e898.
Proof. vm_refl. Qed.
Lemma D_5e898 : decode_any W_5e898 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e89c : bv 32 := 0x00048513.
Lemma F_5e89c : fetch_word Asan.M.loaded_segments (0x5e8ec : word) = Some W_5e89c.
Proof. vm_refl. Qed.
Lemma D_5e89c : decode_any W_5e89c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8a0 : bv 32 := 0x00040593.
Lemma F_5e8a0 : fetch_word Asan.M.loaded_segments (0x5e8f0 : word) = Some W_5e8a0.
Proof. vm_refl. Qed.
Lemma D_5e8a0 : decode_any W_5e8a0 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8a4 : bv 32 := 0xed4ff0ef.
Lemma F_5e8a4 : fetch_word Asan.M.loaded_segments (0x5e8f4 : word) = Some W_5e8a4.
Proof. vm_refl. Qed.
Lemma D_5e8a4 : decode_any W_5e8a4 = Some (Jal 1 2094804, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8a8 : bv 32 := 0xff790593.
Lemma F_5e8a8 : fetch_word Asan.M.loaded_segments (0x5e8f8 : word) = Some W_5e8a8.
Proof. vm_refl. Qed.
Lemma D_5e8a8 : decode_any W_5e8a8 = Some (OpImm ALU_ADD 11 18 4087, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8ac : bv 32 := 0x00100513.
Lemma F_5e8ac : fetch_word Asan.M.loaded_segments (0x5e8fc : word) = Some W_5e8ac.
Proof. vm_refl. Qed.
Lemma D_5e8ac : decode_any W_5e8ac = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8b0 : bv 32 := 0x00b51533.
Lemma F_5e8b0 : fetch_word Asan.M.loaded_segments (0x5e900 : word) = Some W_5e8b0.
Proof. vm_refl. Qed.
Lemma D_5e8b0 : decode_any W_5e8b0 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8b4 : bv 32 := 0x0005061b.
Lemma F_5e8b4 : fetch_word Asan.M.loaded_segments (0x5e904 : word) = Some W_5e8b4.
Proof. vm_refl. Qed.
Lemma D_5e8b4 : decode_any W_5e8b4 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8b8 : bv 32 := 0x08c05263.
Lemma F_5e8b8 : fetch_word Asan.M.loaded_segments (0x5e908 : word) = Some W_5e8b8.
Proof. vm_refl. Qed.
Lemma D_5e8b8 : decode_any W_5e8b8 = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8bc : bv 32 := 0x000016b7.
Lemma F_5e8bc : fetch_word Asan.M.loaded_segments (0x5e90c : word) = Some W_5e8bc.
Proof. vm_refl. Qed.
Lemma D_5e8bc : decode_any W_5e8bc = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8c0 : bv 32 := 0xff190613.
Lemma F_5e8c0 : fetch_word Asan.M.loaded_segments (0x5e910 : word) = Some W_5e8c0.
Proof. vm_refl. Qed.
Lemma D_5e8c0 : decode_any W_5e8c0 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8c4 : bv 32 := 0x38000713.
Lemma F_5e8c4 : fetch_word Asan.M.loaded_segments (0x5e914 : word) = Some W_5e8c4.
Proof. vm_refl. Qed.
Lemma D_5e8c4 : decode_any W_5e8c4 = Some (OpImm ALU_ADD 14 0 896, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8c8 : bv 32 := 0xfff00793.
Lemma F_5e8c8 : fetch_word Asan.M.loaded_segments (0x5e918 : word) = Some W_5e8c8.
Proof. vm_refl. Qed.
Lemma D_5e8c8 : decode_any W_5e8c8 = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8cc : bv 32 := 0x00c71733.
Lemma F_5e8cc : fetch_word Asan.M.loaded_segments (0x5e91c : word) = Some W_5e8cc.
Proof. vm_refl. Qed.
Lemma D_5e8cc : decode_any W_5e8cc = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8d0 : bv 32 := 0x0184b603.
Lemma F_5e8d0 : fetch_word Asan.M.loaded_segments (0x5e920 : word) = Some W_5e8d0.
Proof. vm_refl. Qed.
Lemma D_5e8d0 : decode_any W_5e8d0 = Some (Load SZ8 true 12 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8d4 : bv 32 := 0x00b797b3.
Lemma F_5e8d4 : fetch_word Asan.M.loaded_segments (0x5e924 : word) = Some W_5e8d4.
Proof. vm_refl. Qed.
Lemma D_5e8d4 : decode_any W_5e8d4 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8d8 : bv 32 := 0xfff50813.
Lemma F_5e8d8 : fetch_word Asan.M.loaded_segments (0x5e928 : word) = Some W_5e8d8.
Proof. vm_refl. Qed.
Lemma D_5e8d8 : decode_any W_5e8d8 = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8dc : bv 32 := 0x00d485b3.
Lemma F_5e8dc : fetch_word Asan.M.loaded_segments (0x5e92c : word) = Some W_5e8dc.
Proof. vm_refl. Qed.
Lemma D_5e8dc : decode_any W_5e8dc = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8e0 : bv 32 := 0x00e586b3.
Lemma F_5e8e0 : fetch_word Asan.M.loaded_segments (0x5e930 : word) = Some W_5e8e0.
Proof. vm_refl. Qed.
Lemma D_5e8e0 : decode_any W_5e8e0 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8e4 : bv 32 := 0xfff7c713.
Lemma F_5e8e4 : fetch_word Asan.M.loaded_segments (0x5e934 : word) = Some W_5e8e4.
Proof. vm_refl. Qed.
Lemma D_5e8e4 : decode_any W_5e8e4 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8e8 : bv 32 := 0x02081813.
Lemma F_5e8e8 : fetch_word Asan.M.loaded_segments (0x5e938 : word) = Some W_5e8e8.
Proof. vm_refl. Qed.
Lemma D_5e8e8 : decode_any W_5e8e8 = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8ec : bv 32 := 0x02085793.
Lemma F_5e8ec : fetch_word Asan.M.loaded_segments (0x5e93c : word) = Some W_5e8ec.
Proof. vm_refl. Qed.
Lemma D_5e8ec : decode_any W_5e8ec = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8f0 : bv 32 := 0x00f607b3.
Lemma F_5e8f0 : fetch_word Asan.M.loaded_segments (0x5e940 : word) = Some W_5e8f0.
Proof. vm_refl. Qed.
Lemma D_5e8f0 : decode_any W_5e8f0 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8f4 : bv 32 := 0x00178813.
Lemma F_5e8f4 : fetch_word Asan.M.loaded_segments (0x5e944 : word) = Some W_5e8f4.
Proof. vm_refl. Qed.
Lemma D_5e8f4 : decode_any W_5e8f4 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8f8 : bv 32 := 0x00e678b3.
Lemma F_5e8f8 : fetch_word Asan.M.loaded_segments (0x5e948 : word) = Some W_5e8f8.
Proof. vm_refl. Qed.
Lemma D_5e8f8 : decode_any W_5e8f8 = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8fc : bv 32 := 0x011687b3.
Lemma F_5e8fc : fetch_word Asan.M.loaded_segments (0x5e94c : word) = Some W_5e8fc.
Proof. vm_refl. Qed.
Lemma D_5e8fc : decode_any W_5e8fc = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e900 : bv 32 := 0x0007c283.
Lemma F_5e900 : fetch_word Asan.M.loaded_segments (0x5e950 : word) = Some W_5e900.
Proof. vm_refl. Qed.
Lemma D_5e900 : decode_any W_5e900 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e904 : bv 32 := 0x06028663.
Lemma F_5e904 : fetch_word Asan.M.loaded_segments (0x5e954 : word) = Some W_5e904.
Proof. vm_refl. Qed.
Lemma D_5e904 : decode_any W_5e904 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e908 : bv 32 := 0xfff5051b.
Lemma F_5e908 : fetch_word Asan.M.loaded_segments (0x5e958 : word) = Some W_5e908.
Proof. vm_refl. Qed.
Lemma D_5e908 : decode_any W_5e908 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e90c : bv 32 := 0x00160613.
Lemma F_5e90c : fetch_word Asan.M.loaded_segments (0x5e95c : word) = Some W_5e90c.
Proof. vm_refl. Qed.
Lemma D_5e90c : decode_any W_5e90c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e910 : bv 32 := 0xfe0514e3.
Lemma F_5e910 : fetch_word Asan.M.loaded_segments (0x5e960 : word) = Some W_5e910.
Proof. vm_refl. Qed.
Lemma D_5e910 : decode_any W_5e910 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e970 : bv 32 := 0x00160613.
Lemma F_5e970 : fetch_word Asan.M.loaded_segments (0x5e9c0 : word) = Some W_5e970.
Proof. vm_refl. Qed.
Lemma D_5e970 : decode_any W_5e970 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e974 : bv 32 := 0x00100513.
Lemma F_5e974 : fetch_word Asan.M.loaded_segments (0x5e9c4 : word) = Some W_5e974.
Proof. vm_refl. Qed.
Lemma D_5e974 : decode_any W_5e974 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e978 : bv 32 := 0xffb90693.
Lemma F_5e978 : fetch_word Asan.M.loaded_segments (0x5e9c8 : word) = Some W_5e978.
Proof. vm_refl. Qed.
Lemma D_5e978 : decode_any W_5e978 = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e97c : bv 32 := 0x00c4bc23.
Lemma F_5e97c : fetch_word Asan.M.loaded_segments (0x5e9cc : word) = Some W_5e97c.
Proof. vm_refl. Qed.
Lemma D_5e97c : decode_any W_5e97c = Some (Store SZ8 9 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e980 : bv 32 := 0x00a78023.
Lemma F_5e980 : fetch_word Asan.M.loaded_segments (0x5e9d0 : word) = Some W_5e980.
Proof. vm_refl. Qed.
Lemma D_5e980 : decode_any W_5e980 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e984 : bv 32 := 0x00d51533.
Lemma F_5e984 : fetch_word Asan.M.loaded_segments (0x5e9d4 : word) = Some W_5e984.
Proof. vm_refl. Qed.
Lemma D_5e984 : decode_any W_5e984 = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e988 : bv 32 := 0x00300613.
Lemma F_5e988 : fetch_word Asan.M.loaded_segments (0x5e9d8 : word) = Some W_5e988.
Proof. vm_refl. Qed.
Lemma D_5e988 : decode_any W_5e988 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e98c : bv 32 := 0x00989893.
Lemma F_5e98c : fetch_word Asan.M.loaded_segments (0x5e9dc : word) = Some W_5e98c.
Proof. vm_refl. Qed.
Lemma D_5e98c : decode_any W_5e98c = Some (ShiftImm ALU_SLL 17 17 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e990 : bv 32 := 0x01261633.
Lemma F_5e990 : fetch_word Asan.M.loaded_segments (0x5e9e0 : word) = Some W_5e990.
Proof. vm_refl. Qed.
Lemma D_5e990 : decode_any W_5e990 = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e994 : bv 32 := 0x00a58533.
Lemma F_5e994 : fetch_word Asan.M.loaded_segments (0x5e9e4 : word) = Some W_5e994.
Proof. vm_refl. Qed.
Lemma D_5e994 : decode_any W_5e994 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e998 : bv 32 := 0x01160633.
Lemma F_5e998 : fetch_word Asan.M.loaded_segments (0x5e9e8 : word) = Some W_5e998.
Proof. vm_refl. Qed.
Lemma D_5e998 : decode_any W_5e998 = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e99c : bv 32 := 0x00c504b3.
Lemma F_5e99c : fetch_word Asan.M.loaded_segments (0x5e9ec : word) = Some W_5e99c.
Proof. vm_refl. Qed.
Lemma D_5e99c : decode_any W_5e99c = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9a0 : bv 32 := 0x0084bc23.
Lemma F_5e9a0 : fetch_word Asan.M.loaded_segments (0x5e9f0 : word) = Some W_5e9a0.
Proof. vm_refl. Qed.
Lemma D_5e9a0 : decode_any W_5e9a0 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9a4 : bv 32 := 0x1ef4bc23.
Lemma F_5e9a4 : fetch_word Asan.M.loaded_segments (0x5e9f4 : word) = Some W_5e9a4.
Proof. vm_refl. Qed.
Lemma D_5e9a4 : decode_any W_5e9a4 = Some (Store SZ8 9 15 504, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9a8 : bv 32 := 0x00048513.
Lemma F_5e9a8 : fetch_word Asan.M.loaded_segments (0x5e9f8 : word) = Some W_5e9a8.
Proof. vm_refl. Qed.
Lemma D_5e9a8 : decode_any W_5e9a8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9ac : bv 32 := 0x324000ef.
Lemma F_5e9ac : fetch_word Asan.M.loaded_segments (0x5e9fc : word) = Some W_5e9ac.
Proof. vm_refl. Qed.
Lemma D_5e9ac : decode_any W_5e9ac = Some (Jal 1 804, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9b0 : bv 32 := 0x00050593.
Lemma F_5e9b0 : fetch_word Asan.M.loaded_segments (0x5ea00 : word) = Some W_5e9b0.
Proof. vm_refl. Qed.
Lemma D_5e9b0 : decode_any W_5e9b0 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9b4 : bv 32 := 0x00048513.
Lemma F_5e9b4 : fetch_word Asan.M.loaded_segments (0x5ea04 : word) = Some W_5e9b4.
Proof. vm_refl. Qed.
Lemma D_5e9b4 : decode_any W_5e9b4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9b8 : bv 32 := 0x00000613.
Lemma F_5e9b8 : fetch_word Asan.M.loaded_segments (0x5ea08 : word) = Some W_5e9b8.
Proof. vm_refl. Qed.
Lemma D_5e9b8 : decode_any W_5e9b8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9bc : bv 32 := 0x0005b023.
Lemma F_5e9bc : fetch_word Asan.M.loaded_segments (0x5ea0c : word) = Some W_5e9bc.
Proof. vm_refl. Qed.
Lemma D_5e9bc : decode_any W_5e9bc = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9c0 : bv 32 := 0x0005b423.
Lemma F_5e9c0 : fetch_word Asan.M.loaded_segments (0x5ea10 : word) = Some W_5e9c0.
Proof. vm_refl. Qed.
Lemma D_5e9c0 : decode_any W_5e9c0 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9c4 : bv 32 := 0x0005b823.
Lemma F_5e9c4 : fetch_word Asan.M.loaded_segments (0x5ea14 : word) = Some W_5e9c4.
Proof. vm_refl. Qed.
Lemma D_5e9c4 : decode_any W_5e9c4 = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9c8 : bv 32 := 0x0005bc23.
Lemma F_5e9c8 : fetch_word Asan.M.loaded_segments (0x5ea18 : word) = Some W_5e9c8.
Proof. vm_refl. Qed.
Lemma D_5e9c8 : decode_any W_5e9c8 = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9cc : bv 32 := 0x0205b023.
Lemma F_5e9cc : fetch_word Asan.M.loaded_segments (0x5ea1c : word) = Some W_5e9cc.
Proof. vm_refl. Qed.
Lemma D_5e9cc : decode_any W_5e9cc = Some (Store SZ8 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9d0 : bv 32 := 0x0205b423.
Lemma F_5e9d0 : fetch_word Asan.M.loaded_segments (0x5ea20 : word) = Some W_5e9d0.
Proof. vm_refl. Qed.
Lemma D_5e9d0 : decode_any W_5e9d0 = Some (Store SZ8 11 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9d4 : bv 32 := 0x0205b823.
Lemma F_5e9d4 : fetch_word Asan.M.loaded_segments (0x5ea24 : word) = Some W_5e9d4.
Proof. vm_refl. Qed.
Lemma D_5e9d4 : decode_any W_5e9d4 = Some (Store SZ8 11 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9d8 : bv 32 := 0x0205bc23.
Lemma F_5e9d8 : fetch_word Asan.M.loaded_segments (0x5ea28 : word) = Some W_5e9d8.
Proof. vm_refl. Qed.
Lemma D_5e9d8 : decode_any W_5e9d8 = Some (Store SZ8 11 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9dc : bv 32 := 0x01813083.
Lemma F_5e9dc : fetch_word Asan.M.loaded_segments (0x5ea2c : word) = Some W_5e9dc.
Proof. vm_refl. Qed.
Lemma D_5e9dc : decode_any W_5e9dc = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9e0 : bv 32 := 0x01013403.
Lemma F_5e9e0 : fetch_word Asan.M.loaded_segments (0x5ea30 : word) = Some W_5e9e0.
Proof. vm_refl. Qed.
Lemma D_5e9e0 : decode_any W_5e9e0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9e4 : bv 32 := 0x00813483.
Lemma F_5e9e4 : fetch_word Asan.M.loaded_segments (0x5ea34 : word) = Some W_5e9e4.
Proof. vm_refl. Qed.
Lemma D_5e9e4 : decode_any W_5e9e4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9e8 : bv 32 := 0x00013903.
Lemma F_5e9e8 : fetch_word Asan.M.loaded_segments (0x5ea38 : word) = Some W_5e9e8.
Proof. vm_refl. Qed.
Lemma D_5e9e8 : decode_any W_5e9e8 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9ec : bv 32 := 0x02010113.
Lemma F_5e9ec : fetch_word Asan.M.loaded_segments (0x5ea3c : word) = Some W_5e9ec.
Proof. vm_refl. Qed.
Lemma D_5e9ec : decode_any W_5e9ec = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e9f0 : bv 32 := 0x00008067.
Lemma F_5e9f0 : fetch_word Asan.M.loaded_segments (0x5ea40 : word) = Some W_5e9f0.
Proof. vm_refl. Qed.
Lemma D_5e9f0 : decode_any W_5e9f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecd0 : bv 32 := 0x000da597.
Lemma F_5ecd0 : fetch_word Asan.M.loaded_segments (0x5ed20 : word) = Some W_5ecd0.
Proof. vm_refl. Qed.
Lemma D_5ecd0 : decode_any W_5ecd0 = Some (Auipc 11 218, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecd4 : bv 32 := 0x4985b583.
Lemma F_5ecd4 : fetch_word Asan.M.loaded_segments (0x5ed24 : word) = Some W_5ecd4.
Proof. vm_refl. Qed.
Lemma D_5ecd4 : decode_any W_5ecd4 = Some (Load SZ8 true 11 11 1176, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecd8 : bv 32 := 0x0005b583.
Lemma F_5ecd8 : fetch_word Asan.M.loaded_segments (0x5ed28 : word) = Some W_5ecd8.
Proof. vm_refl. Qed.
Lemma D_5ecd8 : decode_any W_5ecd8 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecdc : bv 32 := 0xfff58613.
Lemma F_5ecdc : fetch_word Asan.M.loaded_segments (0x5ed2c : word) = Some W_5ecdc.
Proof. vm_refl. Qed.
Lemma D_5ecdc : decode_any W_5ecdc = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ece0 : bv 32 := 0x00c5b6b3.
Lemma F_5ece0 : fetch_word Asan.M.loaded_segments (0x5ed30 : word) = Some W_5ece0.
Proof. vm_refl. Qed.
Lemma D_5ece0 : decode_any W_5ece0 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ece4 : bv 32 := 0xfff68693.
Lemma F_5ece4 : fetch_word Asan.M.loaded_segments (0x5ed34 : word) = Some W_5ece4.
Proof. vm_refl. Qed.
Lemma D_5ece4 : decode_any W_5ece4 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ece8 : bv 32 := 0x00c6f6b3.
Lemma F_5ece8 : fetch_word Asan.M.loaded_segments (0x5ed38 : word) = Some W_5ece8.
Proof. vm_refl. Qed.
Lemma D_5ece8 : decode_any W_5ece8 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecec : bv 32 := 0x04a6f263.
Lemma F_5ecec : fetch_word Asan.M.loaded_segments (0x5ed3c : word) = Some W_5ecec.
Proof. vm_refl. Qed.
Lemma D_5ecec : decode_any W_5ecec = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecf0 : bv 32 := 0x000da697.
Lemma F_5ecf0 : fetch_word Asan.M.loaded_segments (0x5ed40 : word) = Some W_5ecf0.
Proof. vm_refl. Qed.
Lemma D_5ecf0 : decode_any W_5ecf0 = Some (Auipc 13 218, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecf4 : bv 32 := 0x4806b683.
Lemma F_5ecf4 : fetch_word Asan.M.loaded_segments (0x5ed44 : word) = Some W_5ecf4.
Proof. vm_refl. Qed.
Lemma D_5ecf4 : decode_any W_5ecf4 = Some (Load SZ8 true 13 13 1152, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecf8 : bv 32 := 0x000da717.
Lemma F_5ecf8 : fetch_word Asan.M.loaded_segments (0x5ed48 : word) = Some W_5ecf8.
Proof. vm_refl. Qed.
Lemma D_5ecf8 : decode_any W_5ecf8 = Some (Auipc 14 218, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecfc : bv 32 := 0x48073703.
Lemma F_5ecfc : fetch_word Asan.M.loaded_segments (0x5ed4c : word) = Some W_5ecfc.
Proof. vm_refl. Qed.
Lemma D_5ecfc : decode_any W_5ecfc = Some (Load SZ8 true 14 14 1152, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed00 : bv 32 := 0x0006b803.
Lemma F_5ed00 : fetch_word Asan.M.loaded_segments (0x5ed50 : word) = Some W_5ed00.
Proof. vm_refl. Qed.
Lemma D_5ed00 : decode_any W_5ed00 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed04 : bv 32 := 0x00073683.
Lemma F_5ed04 : fetch_word Asan.M.loaded_segments (0x5ed54 : word) = Some W_5ed04.
Proof. vm_refl. Qed.
Lemma D_5ed04 : decode_any W_5ed04 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed08 : bv 32 := 0xfff80793.
Lemma F_5ed08 : fetch_word Asan.M.loaded_segments (0x5ed58 : word) = Some W_5ed08.
Proof. vm_refl. Qed.
Lemma D_5ed08 : decode_any W_5ed08 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed0c : bv 32 := 0x00a7f463.
Lemma F_5ed0c : fetch_word Asan.M.loaded_segments (0x5ed5c : word) = Some W_5ed0c.
Proof. vm_refl. Qed.
Lemma D_5ed0c : decode_any W_5ed0c = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed14 : bv 32 := 0x000da717.
Lemma F_5ed14 : fetch_word Asan.M.loaded_segments (0x5ed64 : word) = Some W_5ed14.
Proof. vm_refl. Qed.
Lemma D_5ed14 : decode_any W_5ed14 = Some (Auipc 14 218, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed18 : bv 32 := 0x46c73703.
Lemma F_5ed18 : fetch_word Asan.M.loaded_segments (0x5ed68 : word) = Some W_5ed18.
Proof. vm_refl. Qed.
Lemma D_5ed18 : decode_any W_5ed18 = Some (Load SZ8 true 14 14 1132, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed1c : bv 32 := 0x00073283.
Lemma F_5ed1c : fetch_word Asan.M.loaded_segments (0x5ed6c : word) = Some W_5ed1c.
Proof. vm_refl. Qed.
Lemma D_5ed1c : decode_any W_5ed1c = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed20 : bv 32 := 0x0032d713.
Lemma F_5ed20 : fetch_word Asan.M.loaded_segments (0x5ed70 : word) = Some W_5ed20.
Proof. vm_refl. Qed.
Lemma D_5ed20 : decode_any W_5ed20 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed24 : bv 32 := 0x00b708b3.
Lemma F_5ed24 : fetch_word Asan.M.loaded_segments (0x5ed74 : word) = Some W_5ed24.
Proof. vm_refl. Qed.
Lemma D_5ed24 : decode_any W_5ed24 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed28 : bv 32 := 0x00a2ea63.
Lemma F_5ed28 : fetch_word Asan.M.loaded_segments (0x5ed78 : word) = Some W_5ed28.
Proof. vm_refl. Qed.
Lemma D_5ed28 : decode_any W_5ed28 = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed2c : bv 32 := 0x00a8f863.
Lemma F_5ed2c : fetch_word Asan.M.loaded_segments (0x5ed7c : word) = Some W_5ed2c.
Proof. vm_refl. Qed.
Lemma D_5ed2c : decode_any W_5ed2c = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed30 : bv 32 := 0x00355513.
Lemma F_5ed30 : fetch_word Asan.M.loaded_segments (0x5ed80 : word) = Some W_5ed30.
Proof. vm_refl. Qed.
Lemma D_5ed30 : decode_any W_5ed30 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed34 : bv 32 := 0x00a58533.
Lemma F_5ed34 : fetch_word Asan.M.loaded_segments (0x5ed84 : word) = Some W_5ed34.
Proof. vm_refl. Qed.
Lemma D_5ed34 : decode_any W_5ed34 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed38 : bv 32 := 0x00008067.
Lemma F_5ed38 : fetch_word Asan.M.loaded_segments (0x5ed88 : word) = Some W_5ed38.
Proof. vm_refl. Qed.
Lemma D_5ed38 : decode_any W_5ed38 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

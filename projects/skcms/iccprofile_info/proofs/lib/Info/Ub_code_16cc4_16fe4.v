(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import Ubsan.
Unset Nia Cache.
Unset Lia Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_16cc4 : bv 32 := 0x00008067.
Lemma F_16cc4 : fetch_word Ubsan.M.loaded_segments (0x16cc4 : word) = Some W_16cc4.
Proof. vm_refl. Qed.
Lemma D_16cc4 : decode_any W_16cc4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16cc8 : bv 32 := 0xe8010113.
Lemma F_16cc8 : fetch_word Ubsan.M.loaded_segments (0x16cc8 : word) = Some W_16cc8.
Proof. vm_refl. Qed.
Lemma D_16cc8 : decode_any W_16cc8 = Some (OpImm ALU_ADD 2 2 3712, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ccc : bv 32 := 0x16113c23.
Lemma F_16ccc : fetch_word Ubsan.M.loaded_segments (0x16ccc : word) = Some W_16ccc.
Proof. vm_refl. Qed.
Lemma D_16ccc : decode_any W_16ccc = Some (Store SZ8 2 1 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_16cd0 : bv 32 := 0x16813823.
Lemma F_16cd0 : fetch_word Ubsan.M.loaded_segments (0x16cd0 : word) = Some W_16cd0.
Proof. vm_refl. Qed.
Lemma D_16cd0 : decode_any W_16cd0 = Some (Store SZ8 2 8 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_16cd4 : bv 32 := 0x16913423.
Lemma F_16cd4 : fetch_word Ubsan.M.loaded_segments (0x16cd4 : word) = Some W_16cd4.
Proof. vm_refl. Qed.
Lemma D_16cd4 : decode_any W_16cd4 = Some (Store SZ8 2 9 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_16cd8 : bv 32 := 0x17213023.
Lemma F_16cd8 : fetch_word Ubsan.M.loaded_segments (0x16cd8 : word) = Some W_16cd8.
Proof. vm_refl. Qed.
Lemma D_16cd8 : decode_any W_16cd8 = Some (Store SZ8 2 18 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_16cdc : bv 32 := 0x00058413.
Lemma F_16cdc : fetch_word Ubsan.M.loaded_segments (0x16cdc : word) = Some W_16cdc.
Proof. vm_refl. Qed.
Lemma D_16cdc : decode_any W_16cdc = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ce0 : bv 32 := 0x00050493.
Lemma F_16ce0 : fetch_word Ubsan.M.loaded_segments (0x16ce0 : word) = Some W_16ce0.
Proof. vm_refl. Qed.
Lemma D_16ce0 : decode_any W_16ce0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ce4 : bv 32 := 0x03010513.
Lemma F_16ce4 : fetch_word Ubsan.M.loaded_segments (0x16ce4 : word) = Some W_16ce4.
Proof. vm_refl. Qed.
Lemma D_16ce4 : decode_any W_16ce4 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ce8 : bv 32 := 0x13000613.
Lemma F_16ce8 : fetch_word Ubsan.M.loaded_segments (0x16ce8 : word) = Some W_16ce8.
Proof. vm_refl. Qed.
Lemma D_16ce8 : decode_any W_16ce8 = Some (OpImm ALU_ADD 12 0 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_16cec : bv 32 := 0x00000593.
Lemma F_16cec : fetch_word Ubsan.M.loaded_segments (0x16cec : word) = Some W_16cec.
Proof. vm_refl. Qed.
Lemma D_16cec : decode_any W_16cec = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16cf0 : bv 32 := 0x5f1070ef.
Lemma F_16cf0 : fetch_word Ubsan.M.loaded_segments (0x16cf0 : word) = Some W_16cf0.
Proof. vm_refl. Qed.
Lemma D_16cf0 : decode_any W_16cf0 = Some (Jal 1 32240, 4%Z).
Proof. vm_refl. Qed.

Definition W_16cf4 : bv 32 := 0x00009517.
Lemma F_16cf4 : fetch_word Ubsan.M.loaded_segments (0x16cf4 : word) = Some W_16cf4.
Proof. vm_refl. Qed.
Lemma D_16cf4 : decode_any W_16cf4 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_16cf8 : bv 32 := 0x43c53503.
Lemma F_16cf8 : fetch_word Ubsan.M.loaded_segments (0x16cf8 : word) = Some W_16cf8.
Proof. vm_refl. Qed.
Lemma D_16cf8 : decode_any W_16cf8 = Some (Load SZ8 true 10 10 1084, 4%Z).
Proof. vm_refl. Qed.

Definition W_16cfc : bv 32 := 0x00953023.
Lemma F_16cfc : fetch_word Ubsan.M.loaded_segments (0x16cfc : word) = Some W_16cfc.
Proof. vm_refl. Qed.
Lemma D_16cfc : decode_any W_16cfc = Some (Store SZ8 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d00 : bv 32 := 0x0004b503.
Lemma F_16d00 : fetch_word Ubsan.M.loaded_segments (0x16d00 : word) = Some W_16d00.
Proof. vm_refl. Qed.
Lemma D_16d00 : decode_any W_16d00 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d04 : bv 32 := 0x00848493.
Lemma F_16d04 : fetch_word Ubsan.M.loaded_segments (0x16d04 : word) = Some W_16d04.
Proof. vm_refl. Qed.
Lemma D_16d04 : decode_any W_16d04 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d08 : bv 32 := 0xfe051ce3.
Lemma F_16d08 : fetch_word Ubsan.M.loaded_segments (0x16d08 : word) = Some W_16d08.
Proof. vm_refl. Qed.
Lemma D_16d08 : decode_any W_16d08 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d0c : bv 32 := 0x0003b517.
Lemma F_16d0c : fetch_word Ubsan.M.loaded_segments (0x16d0c : word) = Some W_16d0c.
Proof. vm_refl. Qed.
Lemma D_16d0c : decode_any W_16d0c = Some (Auipc 10 59, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d10 : bv 32 := 0xa5c50913.
Lemma F_16d10 : fetch_word Ubsan.M.loaded_segments (0x16d10 : word) = Some W_16d10.
Proof. vm_refl. Qed.
Lemma D_16d10 : decode_any W_16d10 = Some (OpImm ALU_ADD 18 10 2652, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d14 : bv 32 := 0x00993423.
Lemma F_16d14 : fetch_word Ubsan.M.loaded_segments (0x16d14 : word) = Some W_16d14.
Proof. vm_refl. Qed.
Lemma D_16d14 : decode_any W_16d14 = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d18 : bv 32 := 0x0004b583.
Lemma F_16d18 : fetch_word Ubsan.M.loaded_segments (0x16d18 : word) = Some W_16d18.
Proof. vm_refl. Qed.
Lemma D_16d18 : decode_any W_16d18 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d1c : bv 32 := 0x04058c63.
Lemma F_16d1c : fetch_word Ubsan.M.loaded_segments (0x16d1c : word) = Some W_16d1c.
Proof. vm_refl. Qed.
Lemma D_16d1c : decode_any W_16d1c = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d20 : bv 32 := 0x01048493.
Lemma F_16d20 : fetch_word Ubsan.M.loaded_segments (0x16d20 : word) = Some W_16d20.
Proof. vm_refl. Qed.
Lemma D_16d20 : decode_any W_16d20 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d24 : bv 32 := 0x02500513.
Lemma F_16d24 : fetch_word Ubsan.M.loaded_segments (0x16d24 : word) = Some W_16d24.
Proof. vm_refl. Qed.
Lemma D_16d24 : decode_any W_16d24 = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d28 : bv 32 := 0x03010613.
Lemma F_16d28 : fetch_word Ubsan.M.loaded_segments (0x16d28 : word) = Some W_16d28.
Proof. vm_refl. Qed.
Lemma D_16d28 : decode_any W_16d28 = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d2c : bv 32 := 0x0100006f.
Lemma F_16d2c : fetch_word Ubsan.M.loaded_segments (0x16d2c : word) = Some W_16d2c.
Proof. vm_refl. Qed.
Lemma D_16d2c : decode_any W_16d2c = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d30 : bv 32 := 0x0004b583.
Lemma F_16d30 : fetch_word Ubsan.M.loaded_segments (0x16d30 : word) = Some W_16d30.
Proof. vm_refl. Qed.
Lemma D_16d30 : decode_any W_16d30 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d34 : bv 32 := 0x01048493.
Lemma F_16d34 : fetch_word Ubsan.M.loaded_segments (0x16d34 : word) = Some W_16d34.
Proof. vm_refl. Qed.
Lemma D_16d34 : decode_any W_16d34 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d38 : bv 32 := 0x00058e63.
Lemma F_16d38 : fetch_word Ubsan.M.loaded_segments (0x16d38 : word) = Some W_16d38.
Proof. vm_refl. Qed.
Lemma D_16d38 : decode_any W_16d38 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d3c : bv 32 := 0xfeb56ae3.
Lemma F_16d3c : fetch_word Ubsan.M.loaded_segments (0x16d3c : word) = Some W_16d3c.
Proof. vm_refl. Qed.
Lemma D_16d3c : decode_any W_16d3c = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d40 : bv 32 := 0xff84b683.
Lemma F_16d40 : fetch_word Ubsan.M.loaded_segments (0x16d40 : word) = Some W_16d40.
Proof. vm_refl. Qed.
Lemma D_16d40 : decode_any W_16d40 = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d44 : bv 32 := 0x00359593.
Lemma F_16d44 : fetch_word Ubsan.M.loaded_segments (0x16d44 : word) = Some W_16d44.
Proof. vm_refl. Qed.
Lemma D_16d44 : decode_any W_16d44 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d48 : bv 32 := 0x00b605b3.
Lemma F_16d48 : fetch_word Ubsan.M.loaded_segments (0x16d48 : word) = Some W_16d48.
Proof. vm_refl. Qed.
Lemma D_16d48 : decode_any W_16d48 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d4c : bv 32 := 0x00d5b023.
Lemma F_16d4c : fetch_word Ubsan.M.loaded_segments (0x16d4c : word) = Some W_16d4c.
Proof. vm_refl. Qed.
Lemma D_16d4c : decode_any W_16d4c = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d50 : bv 32 := 0xfe1ff06f.
Lemma F_16d50 : fetch_word Ubsan.M.loaded_segments (0x16d50 : word) = Some W_16d50.
Proof. vm_refl. Qed.
Lemma D_16d50 : decode_any W_16d50 = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d54 : bv 32 := 0x0b013583.
Lemma F_16d54 : fetch_word Ubsan.M.loaded_segments (0x16d54 : word) = Some W_16d54.
Proof. vm_refl. Qed.
Lemma D_16d54 : decode_any W_16d54 = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d58 : bv 32 := 0x13013503.
Lemma F_16d58 : fetch_word Ubsan.M.loaded_segments (0x16d58 : word) = Some W_16d58.
Proof. vm_refl. Qed.
Lemma D_16d58 : decode_any W_16d58 = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d5c : bv 32 := 0x0003b617.
Lemma F_16d5c : fetch_word Ubsan.M.loaded_segments (0x16d5c : word) = Some W_16d5c.
Proof. vm_refl. Qed.
Lemma D_16d5c : decode_any W_16d5c = Some (Auipc 12 59, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d60 : bv 32 := 0xa6b63a23.
Lemma F_16d60 : fetch_word Ubsan.M.loaded_segments (0x16d60 : word) = Some W_16d60.
Proof. vm_refl. Qed.
Lemma D_16d60 : decode_any W_16d60 = Some (Store SZ8 12 11 2676, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d64 : bv 32 := 0x00050c63.
Lemma F_16d64 : fetch_word Ubsan.M.loaded_segments (0x16d64 : word) = Some W_16d64.
Proof. vm_refl. Qed.
Lemma D_16d64 : decode_any W_16d64 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d7c : bv 32 := 0x06013503.
Lemma F_16d7c : fetch_word Ubsan.M.loaded_segments (0x16d7c : word) = Some W_16d7c.
Proof. vm_refl. Qed.
Lemma D_16d7c : decode_any W_16d7c = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d80 : bv 32 := 0x02a93823.
Lemma F_16d80 : fetch_word Ubsan.M.loaded_segments (0x16d80 : word) = Some W_16d80.
Proof. vm_refl. Qed.
Lemma D_16d80 : decode_any W_16d80 = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d84 : bv 32 := 0x00041463.
Lemma F_16d84 : fetch_word Ubsan.M.loaded_segments (0x16d84 : word) = Some W_16d84.
Proof. vm_refl. Qed.
Lemma D_16d84 : decode_any W_16d84 = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d8c : bv 32 := 0x00041663.
Lemma F_16d8c : fetch_word Ubsan.M.loaded_segments (0x16d8c : word) = Some W_16d8c.
Proof. vm_refl. Qed.
Lemma D_16d8c : decode_any W_16d8c = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d98 : bv 32 := 0x00009517.
Lemma F_16d98 : fetch_word Ubsan.M.loaded_segments (0x16d98 : word) = Some W_16d98.
Proof. vm_refl. Qed.
Lemma D_16d98 : decode_any W_16d98 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_16d9c : bv 32 := 0x3a053583.
Lemma F_16d9c : fetch_word Ubsan.M.loaded_segments (0x16d9c : word) = Some W_16d9c.
Proof. vm_refl. Qed.
Lemma D_16d9c : decode_any W_16d9c = Some (Load SZ8 true 11 10 928, 4%Z).
Proof. vm_refl. Qed.

Definition W_16da0 : bv 32 := 0x00009517.
Lemma F_16da0 : fetch_word Ubsan.M.loaded_segments (0x16da0 : word) = Some W_16da0.
Proof. vm_refl. Qed.
Lemma D_16da0 : decode_any W_16da0 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_16da4 : bv 32 := 0x3a053503.
Lemma F_16da4 : fetch_word Ubsan.M.loaded_segments (0x16da4 : word) = Some W_16da4.
Proof. vm_refl. Qed.
Lemma D_16da4 : decode_any W_16da4 = Some (Load SZ8 true 10 10 928, 4%Z).
Proof. vm_refl. Qed.

Definition W_16da8 : bv 32 := 0x0085b023.
Lemma F_16da8 : fetch_word Ubsan.M.loaded_segments (0x16da8 : word) = Some W_16da8.
Proof. vm_refl. Qed.
Lemma D_16da8 : decode_any W_16da8 = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16dac : bv 32 := 0x00140593.
Lemma F_16dac : fetch_word Ubsan.M.loaded_segments (0x16dac : word) = Some W_16dac.
Proof. vm_refl. Qed.
Lemma D_16dac : decode_any W_16dac = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_16db0 : bv 32 := 0x00853023.
Lemma F_16db0 : fetch_word Ubsan.M.loaded_segments (0x16db0 : word) = Some W_16db0.
Proof. vm_refl. Qed.
Lemma D_16db0 : decode_any W_16db0 = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16db4 : bv 32 := 0x02f00613.
Lemma F_16db4 : fetch_word Ubsan.M.loaded_segments (0x16db4 : word) = Some W_16db4.
Proof. vm_refl. Qed.
Lemma D_16db4 : decode_any W_16db4 = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_16db8 : bv 32 := 0x00c0006f.
Lemma F_16db8 : fetch_word Ubsan.M.loaded_segments (0x16db8 : word) = Some W_16db8.
Proof. vm_refl. Qed.
Lemma D_16db8 : decode_any W_16db8 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_16dbc : bv 32 := 0x00b53023.
Lemma F_16dbc : fetch_word Ubsan.M.loaded_segments (0x16dbc : word) = Some W_16dbc.
Proof. vm_refl. Qed.
Lemma D_16dbc : decode_any W_16dbc = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16dc0 : bv 32 := 0x00158593.
Lemma F_16dc0 : fetch_word Ubsan.M.loaded_segments (0x16dc0 : word) = Some W_16dc0.
Proof. vm_refl. Qed.
Lemma D_16dc0 : decode_any W_16dc0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_16dc4 : bv 32 := 0xfff5c683.
Lemma F_16dc4 : fetch_word Ubsan.M.loaded_segments (0x16dc4 : word) = Some W_16dc4.
Proof. vm_refl. Qed.
Lemma D_16dc4 : decode_any W_16dc4 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_16dc8 : bv 32 := 0xfec68ae3.
Lemma F_16dc8 : fetch_word Ubsan.M.loaded_segments (0x16dc8 : word) = Some W_16dc8.
Proof. vm_refl. Qed.
Lemma D_16dc8 : decode_any W_16dc8 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_16dcc : bv 32 := 0xfe069ae3.
Lemma F_16dcc : fetch_word Ubsan.M.loaded_segments (0x16dcc : word) = Some W_16dcc.
Proof. vm_refl. Qed.
Lemma D_16dcc : decode_any W_16dcc = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_16dd0 : bv 32 := 0x03010513.
Lemma F_16dd0 : fetch_word Ubsan.M.loaded_segments (0x16dd0 : word) = Some W_16dd0.
Proof. vm_refl. Qed.
Lemma D_16dd0 : decode_any W_16dd0 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_16dd4 : bv 32 := 0x214000ef.
Lemma F_16dd4 : fetch_word Ubsan.M.loaded_segments (0x16dd4 : word) = Some W_16dd4.
Proof. vm_refl. Qed.
Lemma D_16dd4 : decode_any W_16dd4 = Some (Jal 1 532, 4%Z).
Proof. vm_refl. Qed.

Definition W_16dd8 : bv 32 := 0x0f813503.
Lemma F_16dd8 : fetch_word Ubsan.M.loaded_segments (0x16dd8 : word) = Some W_16dd8.
Proof. vm_refl. Qed.
Lemma D_16dd8 : decode_any W_16dd8 = Some (Load SZ8 true 10 2 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ddc : bv 32 := 0x0d9000ef.
Lemma F_16ddc : fetch_word Ubsan.M.loaded_segments (0x16ddc : word) = Some W_16ddc.
Proof. vm_refl. Qed.
Lemma D_16ddc : decode_any W_16ddc = Some (Jal 1 2264, 4%Z).
Proof. vm_refl. Qed.

Definition W_16de0 : bv 32 := 0x08813503.
Lemma F_16de0 : fetch_word Ubsan.M.loaded_segments (0x16de0 : word) = Some W_16de0.
Proof. vm_refl. Qed.
Lemma D_16de0 : decode_any W_16de0 = Some (Load SZ8 true 10 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_16de4 : bv 32 := 0x09013583.
Lemma F_16de4 : fetch_word Ubsan.M.loaded_segments (0x16de4 : word) = Some W_16de4.
Proof. vm_refl. Qed.
Lemma D_16de4 : decode_any W_16de4 = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_16de8 : bv 32 := 0x00b51c63.
Lemma F_16de8 : fetch_word Ubsan.M.loaded_segments (0x16de8 : word) = Some W_16de8.
Proof. vm_refl. Qed.
Lemma D_16de8 : decode_any W_16de8 = Some (Branch BC_NE 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_16dec : bv 32 := 0x09813503.
Lemma F_16dec : fetch_word Ubsan.M.loaded_segments (0x16dec : word) = Some W_16dec.
Proof. vm_refl. Qed.
Lemma D_16dec : decode_any W_16dec = Some (Load SZ8 true 10 2 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_16df0 : bv 32 := 0x0a013583.
Lemma F_16df0 : fetch_word Ubsan.M.loaded_segments (0x16df0 : word) = Some W_16df0.
Proof. vm_refl. Qed.
Lemma D_16df0 : decode_any W_16df0 = Some (Load SZ8 true 11 2 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_16df4 : bv 32 := 0x00b51663.
Lemma F_16df4 : fetch_word Ubsan.M.loaded_segments (0x16df4 : word) = Some W_16df4.
Proof. vm_refl. Qed.
Lemma D_16df4 : decode_any W_16df4 = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_16df8 : bv 32 := 0x0e813503.
Lemma F_16df8 : fetch_word Ubsan.M.loaded_segments (0x16df8 : word) = Some W_16df8.
Proof. vm_refl. Qed.
Lemma D_16df8 : decode_any W_16df8 = Some (Load SZ8 true 10 2 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_16dfc : bv 32 := 0x0e050063.
Lemma F_16dfc : fetch_word Ubsan.M.loaded_segments (0x16dfc : word) = Some W_16dfc.
Proof. vm_refl. Qed.
Lemma D_16dfc : decode_any W_16dfc = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_16edc : bv 32 := 0x17813083.
Lemma F_16edc : fetch_word Ubsan.M.loaded_segments (0x16edc : word) = Some W_16edc.
Proof. vm_refl. Qed.
Lemma D_16edc : decode_any W_16edc = Some (Load SZ8 true 1 2 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ee0 : bv 32 := 0x17013403.
Lemma F_16ee0 : fetch_word Ubsan.M.loaded_segments (0x16ee0 : word) = Some W_16ee0.
Proof. vm_refl. Qed.
Lemma D_16ee0 : decode_any W_16ee0 = Some (Load SZ8 true 8 2 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ee4 : bv 32 := 0x16813483.
Lemma F_16ee4 : fetch_word Ubsan.M.loaded_segments (0x16ee4 : word) = Some W_16ee4.
Proof. vm_refl. Qed.
Lemma D_16ee4 : decode_any W_16ee4 = Some (Load SZ8 true 9 2 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ee8 : bv 32 := 0x16013903.
Lemma F_16ee8 : fetch_word Ubsan.M.loaded_segments (0x16ee8 : word) = Some W_16ee8.
Proof. vm_refl. Qed.
Lemma D_16ee8 : decode_any W_16ee8 = Some (Load SZ8 true 18 2 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_16eec : bv 32 := 0x18010113.
Lemma F_16eec : fetch_word Ubsan.M.loaded_segments (0x16eec : word) = Some W_16eec.
Proof. vm_refl. Qed.
Lemma D_16eec : decode_any W_16eec = Some (OpImm ALU_ADD 2 2 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ef0 : bv 32 := 0x00008067.
Lemma F_16ef0 : fetch_word Ubsan.M.loaded_segments (0x16ef0 : word) = Some W_16ef0.
Proof. vm_refl. Qed.
Lemma D_16ef0 : decode_any W_16ef0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ef4 : bv 32 := 0xfe010113.
Lemma F_16ef4 : fetch_word Ubsan.M.loaded_segments (0x16ef4 : word) = Some W_16ef4.
Proof. vm_refl. Qed.
Lemma D_16ef4 : decode_any W_16ef4 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ef8 : bv 32 := 0x00113c23.
Lemma F_16ef8 : fetch_word Ubsan.M.loaded_segments (0x16ef8 : word) = Some W_16ef8.
Proof. vm_refl. Qed.
Lemma D_16ef8 : decode_any W_16ef8 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_16efc : bv 32 := 0x00813823.
Lemma F_16efc : fetch_word Ubsan.M.loaded_segments (0x16efc : word) = Some W_16efc.
Proof. vm_refl. Qed.
Lemma D_16efc : decode_any W_16efc = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f00 : bv 32 := 0x00913423.
Lemma F_16f00 : fetch_word Ubsan.M.loaded_segments (0x16f00 : word) = Some W_16f00.
Proof. vm_refl. Qed.
Lemma D_16f00 : decode_any W_16f00 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f04 : bv 32 := 0xdc1ff0ef.
Lemma F_16f04 : fetch_word Ubsan.M.loaded_segments (0x16f04 : word) = Some W_16f04.
Proof. vm_refl. Qed.
Lemma D_16f04 : decode_any W_16f04 = Some (Jal 1 2096576, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f08 : bv 32 := 0x00009517.
Lemma F_16f08 : fetch_word Ubsan.M.loaded_segments (0x16f08 : word) = Some W_16f08.
Proof. vm_refl. Qed.
Lemma D_16f08 : decode_any W_16f08 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f0c : bv 32 := 0x00009597.
Lemma F_16f0c : fetch_word Ubsan.M.loaded_segments (0x16f0c : word) = Some W_16f0c.
Proof. vm_refl. Qed.
Lemma D_16f0c : decode_any W_16f0c = Some (Auipc 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f10 : bv 32 := 0x24053403.
Lemma F_16f10 : fetch_word Ubsan.M.loaded_segments (0x16f10 : word) = Some W_16f10.
Proof. vm_refl. Qed.
Lemma D_16f10 : decode_any W_16f10 = Some (Load SZ8 true 8 10 576, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f14 : bv 32 := 0x2445b483.
Lemma F_16f14 : fetch_word Ubsan.M.loaded_segments (0x16f14 : word) = Some W_16f14.
Proof. vm_refl. Qed.
Lemma D_16f14 : decode_any W_16f14 = Some (Load SZ8 true 9 11 580, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f18 : bv 32 := 0x0084fa63.
Lemma F_16f18 : fetch_word Ubsan.M.loaded_segments (0x16f18 : word) = Some W_16f18.
Proof. vm_refl. Qed.
Lemma D_16f18 : decode_any W_16f18 = Some (Branch BC_GEU 9 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f1c : bv 32 := 0x0004b503.
Lemma F_16f1c : fetch_word Ubsan.M.loaded_segments (0x16f1c : word) = Some W_16f1c.
Proof. vm_refl. Qed.
Lemma D_16f1c : decode_any W_16f1c = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f20 : bv 32 := 0x000500e7.
Lemma F_16f20 : fetch_word Ubsan.M.loaded_segments (0x16f20 : word) = Some W_16f20.
Proof. vm_refl. Qed.
Lemma D_16f20 : decode_any W_16f20 = Some (Jalr 1 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f24 : bv 32 := 0x00848493.
Lemma F_16f24 : fetch_word Ubsan.M.loaded_segments (0x16f24 : word) = Some W_16f24.
Proof. vm_refl. Qed.
Lemma D_16f24 : decode_any W_16f24 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f28 : bv 32 := 0xfe84eae3.
Lemma F_16f28 : fetch_word Ubsan.M.loaded_segments (0x16f28 : word) = Some W_16f28.
Proof. vm_refl. Qed.
Lemma D_16f28 : decode_any W_16f28 = Some (Branch BC_LTU 9 8 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f2c : bv 32 := 0x01813083.
Lemma F_16f2c : fetch_word Ubsan.M.loaded_segments (0x16f2c : word) = Some W_16f2c.
Proof. vm_refl. Qed.
Lemma D_16f2c : decode_any W_16f2c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f30 : bv 32 := 0x01013403.
Lemma F_16f30 : fetch_word Ubsan.M.loaded_segments (0x16f30 : word) = Some W_16f30.
Proof. vm_refl. Qed.
Lemma D_16f30 : decode_any W_16f30 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f34 : bv 32 := 0x00813483.
Lemma F_16f34 : fetch_word Ubsan.M.loaded_segments (0x16f34 : word) = Some W_16f34.
Proof. vm_refl. Qed.
Lemma D_16f34 : decode_any W_16f34 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f38 : bv 32 := 0x02010113.
Lemma F_16f38 : fetch_word Ubsan.M.loaded_segments (0x16f38 : word) = Some W_16f38.
Proof. vm_refl. Qed.
Lemma D_16f38 : decode_any W_16f38 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f3c : bv 32 := 0x00008067.
Lemma F_16f3c : fetch_word Ubsan.M.loaded_segments (0x16f3c : word) = Some W_16f3c.
Proof. vm_refl. Qed.
Lemma D_16f3c : decode_any W_16f3c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f40 : bv 32 := 0xfe010113.
Lemma F_16f40 : fetch_word Ubsan.M.loaded_segments (0x16f40 : word) = Some W_16f40.
Proof. vm_refl. Qed.
Lemma D_16f40 : decode_any W_16f40 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f44 : bv 32 := 0x00113c23.
Lemma F_16f44 : fetch_word Ubsan.M.loaded_segments (0x16f44 : word) = Some W_16f44.
Proof. vm_refl. Qed.
Lemma D_16f44 : decode_any W_16f44 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f48 : bv 32 := 0x00813823.
Lemma F_16f48 : fetch_word Ubsan.M.loaded_segments (0x16f48 : word) = Some W_16f48.
Proof. vm_refl. Qed.
Lemma D_16f48 : decode_any W_16f48 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f4c : bv 32 := 0x00913423.
Lemma F_16f4c : fetch_word Ubsan.M.loaded_segments (0x16f4c : word) = Some W_16f4c.
Proof. vm_refl. Qed.
Lemma D_16f4c : decode_any W_16f4c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f50 : bv 32 := 0x01213023.
Lemma F_16f50 : fetch_word Ubsan.M.loaded_segments (0x16f50 : word) = Some W_16f50.
Proof. vm_refl. Qed.
Lemma D_16f50 : decode_any W_16f50 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f54 : bv 32 := 0x00060413.
Lemma F_16f54 : fetch_word Ubsan.M.loaded_segments (0x16f54 : word) = Some W_16f54.
Proof. vm_refl. Qed.
Lemma D_16f54 : decode_any W_16f54 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f58 : bv 32 := 0x00058493.
Lemma F_16f58 : fetch_word Ubsan.M.loaded_segments (0x16f58 : word) = Some W_16f58.
Proof. vm_refl. Qed.
Lemma D_16f58 : decode_any W_16f58 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f5c : bv 32 := 0x00050913.
Lemma F_16f5c : fetch_word Ubsan.M.loaded_segments (0x16f5c : word) = Some W_16f5c.
Proof. vm_refl. Qed.
Lemma D_16f5c : decode_any W_16f5c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f60 : bv 32 := 0x00063583.
Lemma F_16f60 : fetch_word Ubsan.M.loaded_segments (0x16f60 : word) = Some W_16f60.
Proof. vm_refl. Qed.
Lemma D_16f60 : decode_any W_16f60 = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f64 : bv 32 := 0x00349513.
Lemma F_16f64 : fetch_word Ubsan.M.loaded_segments (0x16f64 : word) = Some W_16f64.
Proof. vm_refl. Qed.
Lemma D_16f64 : decode_any W_16f64 = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f68 : bv 32 := 0x00a60533.
Lemma F_16f68 : fetch_word Ubsan.M.loaded_segments (0x16f68 : word) = Some W_16f68.
Proof. vm_refl. Qed.
Lemma D_16f68 : decode_any W_16f68 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f6c : bv 32 := 0x00850513.
Lemma F_16f6c : fetch_word Ubsan.M.loaded_segments (0x16f6c : word) = Some W_16f6c.
Proof. vm_refl. Qed.
Lemma D_16f6c : decode_any W_16f6c = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f70 : bv 32 := 0xd59ff0ef.
Lemma F_16f70 : fetch_word Ubsan.M.loaded_segments (0x16f70 : word) = Some W_16f70.
Proof. vm_refl. Qed.
Lemma D_16f70 : decode_any W_16f70 = Some (Jal 1 2096472, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f74 : bv 32 := 0x00000517.
Lemma F_16f74 : fetch_word Ubsan.M.loaded_segments (0x16f74 : word) = Some W_16f74.
Proof. vm_refl. Qed.
Lemma D_16f74 : decode_any W_16f74 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f78 : bv 32 := 0x02c50313.
Lemma F_16f78 : fetch_word Ubsan.M.loaded_segments (0x16f78 : word) = Some W_16f78.
Proof. vm_refl. Qed.
Lemma D_16f78 : decode_any W_16f78 = Some (OpImm ALU_ADD 6 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f7c : bv 32 := 0x00090513.
Lemma F_16f7c : fetch_word Ubsan.M.loaded_segments (0x16f7c : word) = Some W_16f7c.
Proof. vm_refl. Qed.
Lemma D_16f7c : decode_any W_16f7c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f80 : bv 32 := 0x00048593.
Lemma F_16f80 : fetch_word Ubsan.M.loaded_segments (0x16f80 : word) = Some W_16f80.
Proof. vm_refl. Qed.
Lemma D_16f80 : decode_any W_16f80 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f84 : bv 32 := 0x00040613.
Lemma F_16f84 : fetch_word Ubsan.M.loaded_segments (0x16f84 : word) = Some W_16f84.
Proof. vm_refl. Qed.
Lemma D_16f84 : decode_any W_16f84 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f88 : bv 32 := 0x01813083.
Lemma F_16f88 : fetch_word Ubsan.M.loaded_segments (0x16f88 : word) = Some W_16f88.
Proof. vm_refl. Qed.
Lemma D_16f88 : decode_any W_16f88 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f8c : bv 32 := 0x01013403.
Lemma F_16f8c : fetch_word Ubsan.M.loaded_segments (0x16f8c : word) = Some W_16f8c.
Proof. vm_refl. Qed.
Lemma D_16f8c : decode_any W_16f8c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f90 : bv 32 := 0x00813483.
Lemma F_16f90 : fetch_word Ubsan.M.loaded_segments (0x16f90 : word) = Some W_16f90.
Proof. vm_refl. Qed.
Lemma D_16f90 : decode_any W_16f90 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f94 : bv 32 := 0x00013903.
Lemma F_16f94 : fetch_word Ubsan.M.loaded_segments (0x16f94 : word) = Some W_16f94.
Proof. vm_refl. Qed.
Lemma D_16f94 : decode_any W_16f94 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f98 : bv 32 := 0x02010113.
Lemma F_16f98 : fetch_word Ubsan.M.loaded_segments (0x16f98 : word) = Some W_16f98.
Proof. vm_refl. Qed.
Lemma D_16f98 : decode_any W_16f98 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f9c : bv 32 := 0x00030067.
Lemma F_16f9c : fetch_word Ubsan.M.loaded_segments (0x16f9c : word) = Some W_16f9c.
Proof. vm_refl. Qed.
Lemma D_16f9c : decode_any W_16f9c = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fa0 : bv 32 := 0xfd010113.
Lemma F_16fa0 : fetch_word Ubsan.M.loaded_segments (0x16fa0 : word) = Some W_16fa0.
Proof. vm_refl. Qed.
Lemma D_16fa0 : decode_any W_16fa0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fa4 : bv 32 := 0x02113423.
Lemma F_16fa4 : fetch_word Ubsan.M.loaded_segments (0x16fa4 : word) = Some W_16fa4.
Proof. vm_refl. Qed.
Lemma D_16fa4 : decode_any W_16fa4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fa8 : bv 32 := 0x02813023.
Lemma F_16fa8 : fetch_word Ubsan.M.loaded_segments (0x16fa8 : word) = Some W_16fa8.
Proof. vm_refl. Qed.
Lemma D_16fa8 : decode_any W_16fa8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fac : bv 32 := 0x00913c23.
Lemma F_16fac : fetch_word Ubsan.M.loaded_segments (0x16fac : word) = Some W_16fac.
Proof. vm_refl. Qed.
Lemma D_16fac : decode_any W_16fac = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fb0 : bv 32 := 0x01213823.
Lemma F_16fb0 : fetch_word Ubsan.M.loaded_segments (0x16fb0 : word) = Some W_16fb0.
Proof. vm_refl. Qed.
Lemma D_16fb0 : decode_any W_16fb0 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fb4 : bv 32 := 0x01313423.
Lemma F_16fb4 : fetch_word Ubsan.M.loaded_segments (0x16fb4 : word) = Some W_16fb4.
Proof. vm_refl. Qed.
Lemma D_16fb4 : decode_any W_16fb4 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fb8 : bv 32 := 0x00060413.
Lemma F_16fb8 : fetch_word Ubsan.M.loaded_segments (0x16fb8 : word) = Some W_16fb8.
Proof. vm_refl. Qed.
Lemma D_16fb8 : decode_any W_16fb8 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fbc : bv 32 := 0x00058493.
Lemma F_16fbc : fetch_word Ubsan.M.loaded_segments (0x16fbc : word) = Some W_16fbc.
Proof. vm_refl. Qed.
Lemma D_16fbc : decode_any W_16fbc = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fc0 : bv 32 := 0x00050913.
Lemma F_16fc0 : fetch_word Ubsan.M.loaded_segments (0x16fc0 : word) = Some W_16fc0.
Proof. vm_refl. Qed.
Lemma D_16fc0 : decode_any W_16fc0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fc4 : bv 32 := 0x00359513.
Lemma F_16fc4 : fetch_word Ubsan.M.loaded_segments (0x16fc4 : word) = Some W_16fc4.
Proof. vm_refl. Qed.
Lemma D_16fc4 : decode_any W_16fc4 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fc8 : bv 32 := 0x00a60533.
Lemma F_16fc8 : fetch_word Ubsan.M.loaded_segments (0x16fc8 : word) = Some W_16fc8.
Proof. vm_refl. Qed.
Lemma D_16fc8 : decode_any W_16fc8 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fcc : bv 32 := 0x00850993.
Lemma F_16fcc : fetch_word Ubsan.M.loaded_segments (0x16fcc : word) = Some W_16fcc.
Proof. vm_refl. Qed.
Lemma D_16fcc : decode_any W_16fcc = Some (OpImm ALU_ADD 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fd0 : bv 32 := 0xf25ff0ef.
Lemma F_16fd0 : fetch_word Ubsan.M.loaded_segments (0x16fd0 : word) = Some W_16fd0.
Proof. vm_refl. Qed.
Lemma D_16fd0 : decode_any W_16fd0 = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fd4 : bv 32 := 0x00048513.
Lemma F_16fd4 : fetch_word Ubsan.M.loaded_segments (0x16fd4 : word) = Some W_16fd4.
Proof. vm_refl. Qed.
Lemma D_16fd4 : decode_any W_16fd4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fd8 : bv 32 := 0x00040593.
Lemma F_16fd8 : fetch_word Ubsan.M.loaded_segments (0x16fd8 : word) = Some W_16fd8.
Proof. vm_refl. Qed.
Lemma D_16fd8 : decode_any W_16fd8 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fdc : bv 32 := 0x00098613.
Lemma F_16fdc : fetch_word Ubsan.M.loaded_segments (0x16fdc : word) = Some W_16fdc.
Proof. vm_refl. Qed.
Lemma D_16fdc : decode_any W_16fdc = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fe0 : bv 32 := 0x000900e7.
Lemma F_16fe0 : fetch_word Ubsan.M.loaded_segments (0x16fe0 : word) = Some W_16fe0.
Proof. vm_refl. Qed.
Lemma D_16fe0 : decode_any W_16fe0 = Some (Jalr 1 18 0, 4%Z).
Proof. vm_refl. Qed.

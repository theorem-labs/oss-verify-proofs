(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_a8c88 : bv 32 := 0xfc010113.
Lemma F_a8c88 : fetch_word Plain.M.loaded_segments (0xa8c88 : word) = Some W_a8c88.
Proof. vm_refl. Qed.
Lemma D_a8c88 : decode_any W_a8c88 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8c8c : bv 32 := 0x02113c23.
Lemma F_a8c8c : fetch_word Plain.M.loaded_segments (0xa8c8c : word) = Some W_a8c8c.
Proof. vm_refl. Qed.
Lemma D_a8c8c : decode_any W_a8c8c = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8c90 : bv 32 := 0x02813823.
Lemma F_a8c90 : fetch_word Plain.M.loaded_segments (0xa8c90 : word) = Some W_a8c90.
Proof. vm_refl. Qed.
Lemma D_a8c90 : decode_any W_a8c90 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8c94 : bv 32 := 0x02913423.
Lemma F_a8c94 : fetch_word Plain.M.loaded_segments (0xa8c94 : word) = Some W_a8c94.
Proof. vm_refl. Qed.
Lemma D_a8c94 : decode_any W_a8c94 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8c98 : bv 32 := 0x03213023.
Lemma F_a8c98 : fetch_word Plain.M.loaded_segments (0xa8c98 : word) = Some W_a8c98.
Proof. vm_refl. Qed.
Lemma D_a8c98 : decode_any W_a8c98 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8c9c : bv 32 := 0x01313c23.
Lemma F_a8c9c : fetch_word Plain.M.loaded_segments (0xa8c9c : word) = Some W_a8c9c.
Proof. vm_refl. Qed.
Lemma D_a8c9c : decode_any W_a8c9c = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8ca0 : bv 32 := 0x01413823.
Lemma F_a8ca0 : fetch_word Plain.M.loaded_segments (0xa8ca0 : word) = Some W_a8ca0.
Proof. vm_refl. Qed.
Lemma D_a8ca0 : decode_any W_a8ca0 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8ca4 : bv 32 := 0x01513423.
Lemma F_a8ca4 : fetch_word Plain.M.loaded_segments (0xa8ca4 : word) = Some W_a8ca4.
Proof. vm_refl. Qed.
Lemma D_a8ca4 : decode_any W_a8ca4 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8ca8 : bv 32 := 0x02853683.
Lemma F_a8ca8 : fetch_word Plain.M.loaded_segments (0xa8ca8 : word) = Some W_a8ca8.
Proof. vm_refl. Qed.
Lemma D_a8ca8 : decode_any W_a8ca8 = Some (Load SZ8 true 13 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8cac : bv 32 := 0x00050597.
Lemma F_a8cac : fetch_word Plain.M.loaded_segments (0xa8cac : word) = Some W_a8cac.
Proof. vm_refl. Qed.
Lemma D_a8cac : decode_any W_a8cac = Some (Auipc 11 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8cb0 : bv 32 := 0xbac58593.
Lemma F_a8cb0 : fetch_word Plain.M.loaded_segments (0xa8cb0 : word) = Some W_a8cb0.
Proof. vm_refl. Qed.
Lemma D_a8cb0 : decode_any W_a8cb0 = Some (OpImm ALU_ADD 11 11 2988, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8cb4 : bv 32 := 0x00050617.
Lemma F_a8cb4 : fetch_word Plain.M.loaded_segments (0xa8cb4 : word) = Some W_a8cb4.
Proof. vm_refl. Qed.
Lemma D_a8cb4 : decode_any W_a8cb4 = Some (Auipc 12 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8cb8 : bv 32 := 0xe2c60493.
Lemma F_a8cb8 : fetch_word Plain.M.loaded_segments (0xa8cb8 : word) = Some W_a8cb8.
Proof. vm_refl. Qed.
Lemma D_a8cb8 : decode_any W_a8cb8 = Some (OpImm ALU_ADD 9 12 3628, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8cbc : bv 32 := 0x0c068e63.
Lemma F_a8cbc : fetch_word Plain.M.loaded_segments (0xa8cbc : word) = Some W_a8cbc.
Proof. vm_refl. Qed.
Lemma D_a8cbc : decode_any W_a8cbc = Some (Branch BC_EQ 13 0 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8cc0 : bv 32 := 0x00000613.
Lemma F_a8cc0 : fetch_word Plain.M.loaded_segments (0xa8cc0 : word) = Some W_a8cc0.
Proof. vm_refl. Qed.
Lemma D_a8cc0 : decode_any W_a8cc0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8cc4 : bv 32 := 0x00000893.
Lemma F_a8cc4 : fetch_word Plain.M.loaded_segments (0xa8cc4 : word) = Some W_a8cc4.
Proof. vm_refl. Qed.
Lemma D_a8cc4 : decode_any W_a8cc4 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8cc8 : bv 32 := 0x0001e717.
Lemma F_a8cc8 : fetch_word Plain.M.loaded_segments (0xa8cc8 : word) = Some W_a8cc8.
Proof. vm_refl. Qed.
Lemma D_a8cc8 : decode_any W_a8cc8 = Some (Auipc 14 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8ccc : bv 32 := 0x01853783.
Lemma F_a8ccc : fetch_word Plain.M.loaded_segments (0xa8ccc : word) = Some W_a8ccc.
Proof. vm_refl. Qed.
Lemma D_a8ccc : decode_any W_a8ccc = Some (Load SZ8 true 15 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8cd0 : bv 32 := 0x02053503.
Lemma F_a8cd0 : fetch_word Plain.M.loaded_segments (0xa8cd0 : word) = Some W_a8cd0.
Proof. vm_refl. Qed.
Lemma D_a8cd0 : decode_any W_a8cd0 = Some (Load SZ8 true 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8cd4 : bv 32 := 0x00600813.
Lemma F_a8cd4 : fetch_word Plain.M.loaded_segments (0xa8cd4 : word) = Some W_a8cd4.
Proof. vm_refl. Qed.
Lemma D_a8cd4 : decode_any W_a8cd4 = Some (OpImm ALU_ADD 16 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8cd8 : bv 32 := 0x0001d297.
Lemma F_a8cd8 : fetch_word Plain.M.loaded_segments (0xa8cd8 : word) = Some W_a8cd8.
Proof. vm_refl. Qed.
Lemma D_a8cd8 : decode_any W_a8cd8 = Some (Auipc 5 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8cdc : bv 32 := 0x0e876f03.
Lemma F_a8cdc : fetch_word Plain.M.loaded_segments (0xa8cdc : word) = Some W_a8cdc.
Proof. vm_refl. Qed.
Lemma D_a8cdc : decode_any W_a8cdc = Some (Load SZ4 false 30 14 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8ce0 : bv 32 := 0xc502b283.
Lemma F_a8ce0 : fetch_word Plain.M.loaded_segments (0xa8ce0 : word) = Some W_a8ce0.
Proof. vm_refl. Qed.
Lemma D_a8ce0 : decode_any W_a8ce0 = Some (Load SZ8 true 5 5 3152, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8ce4 : bv 32 := 0x00200313.
Lemma F_a8ce4 : fetch_word Plain.M.loaded_segments (0xa8ce4 : word) = Some W_a8ce4.
Proof. vm_refl. Qed.
Lemma D_a8ce4 : decode_any W_a8ce4 = Some (OpImm ALU_ADD 6 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8ce8 : bv 32 := 0x00700393.
Lemma F_a8ce8 : fetch_word Plain.M.loaded_segments (0xa8ce8 : word) = Some W_a8ce8.
Proof. vm_refl. Qed.
Lemma D_a8ce8 : decode_any W_a8ce8 = Some (OpImm ALU_ADD 7 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8cec : bv 32 := 0x6474ee37.
Lemma F_a8cec : fetch_word Plain.M.loaded_segments (0xa8cec : word) = Some W_a8cec.
Proof. vm_refl. Qed.
Lemma D_a8cec : decode_any W_a8cec = Some (Lui 28 411470, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8cf0 : bv 32 := 0x551e0e1b.
Lemma F_a8cf0 : fetch_word Plain.M.loaded_segments (0xa8cf0 : word) = Some W_a8cf0.
Proof. vm_refl. Qed.
Lemma D_a8cf0 : decode_any W_a8cf0 = Some (OpImm32 28 28 1361, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8cf4 : bv 32 := 0x00078e93.
Lemma F_a8cf4 : fetch_word Plain.M.loaded_segments (0xa8cf4 : word) = Some W_a8cf4.
Proof. vm_refl. Qed.
Lemma D_a8cf4 : decode_any W_a8cf4 = Some (OpImm ALU_ADD 29 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8cf8 : bv 32 := 0x0180006f.
Lemma F_a8cf8 : fetch_word Plain.M.loaded_segments (0xa8cf8 : word) = Some W_a8cf8.
Proof. vm_refl. Qed.
Lemma D_a8cf8 : decode_any W_a8cf8 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8cfc : bv 32 := 0x010eb603.
Lemma F_a8cfc : fetch_word Plain.M.loaded_segments (0xa8cfc : word) = Some W_a8cfc.
Proof. vm_refl. Qed.
Lemma D_a8cfc : decode_any W_a8cfc = Some (Load SZ8 true 12 29 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8d00 : bv 32 := 0x40c78633.
Lemma F_a8d00 : fetch_word Plain.M.loaded_segments (0xa8d00 : word) = Some W_a8d00.
Proof. vm_refl. Qed.
Lemma D_a8d00 : decode_any W_a8d00 = Some (Op ALU_SUB 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8d04 : bv 32 := 0xfff68693.
Lemma F_a8d04 : fetch_word Plain.M.loaded_segments (0xa8d04 : word) = Some W_a8d04.
Proof. vm_refl. Qed.
Lemma D_a8d04 : decode_any W_a8d04 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8d08 : bv 32 := 0x00ae8eb3.
Lemma F_a8d08 : fetch_word Plain.M.loaded_segments (0xa8d08 : word) = Some W_a8d08.
Proof. vm_refl. Qed.
Lemma D_a8d08 : decode_any W_a8d08 = Some (Op ALU_ADD 29 29 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8d0c : bv 32 := 0x04068a63.
Lemma F_a8d0c : fetch_word Plain.M.loaded_segments (0xa8d0c : word) = Some W_a8d0c.
Proof. vm_refl. Qed.
Lemma D_a8d0c : decode_any W_a8d0c = Some (Branch BC_EQ 13 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8d10 : bv 32 := 0x000ea403.
Lemma F_a8d10 : fetch_word Plain.M.loaded_segments (0xa8d10 : word) = Some W_a8d10.
Proof. vm_refl. Qed.
Lemma D_a8d10 : decode_any W_a8d10 = Some (Load SZ4 true 8 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8d14 : bv 32 := 0xff0404e3.
Lemma F_a8d14 : fetch_word Plain.M.loaded_segments (0xa8d14 : word) = Some W_a8d14.
Proof. vm_refl. Qed.
Lemma D_a8d14 : decode_any W_a8d14 = Some (Branch BC_EQ 8 16 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8d18 : bv 32 := 0x00028a63.
Lemma F_a8d18 : fetch_word Plain.M.loaded_segments (0xa8d18 : word) = Some W_a8d18.
Proof. vm_refl. Qed.
Lemma D_a8d18 : decode_any W_a8d18 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8d2c : bv 32 := 0x000e8f93.
Lemma F_a8d2c : fetch_word Plain.M.loaded_segments (0xa8d2c : word) = Some W_a8d2c.
Proof. vm_refl. Qed.
Lemma D_a8d2c : decode_any W_a8d2c = Some (OpImm ALU_ADD 31 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8d30 : bv 32 := 0x00740463.
Lemma F_a8d30 : fetch_word Plain.M.loaded_segments (0xa8d30 : word) = Some W_a8d30.
Proof. vm_refl. Qed.
Lemma D_a8d30 : decode_any W_a8d30 = Some (Branch BC_EQ 8 7 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8d34 : bv 32 := 0x00088f93.
Lemma F_a8d34 : fetch_word Plain.M.loaded_segments (0xa8d34 : word) = Some W_a8d34.
Proof. vm_refl. Qed.
Lemma D_a8d34 : decode_any W_a8d34 = Some (OpImm ALU_ADD 31 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8d38 : bv 32 := 0x03c41063.
Lemma F_a8d38 : fetch_word Plain.M.loaded_segments (0xa8d38 : word) = Some W_a8d38.
Proof. vm_refl. Qed.
Lemma D_a8d38 : decode_any W_a8d38 = Some (Branch BC_NE 8 28 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8d3c : bv 32 := 0x028eb883.
Lemma F_a8d3c : fetch_word Plain.M.loaded_segments (0xa8d3c : word) = Some W_a8d3c.
Proof. vm_refl. Qed.
Lemma D_a8d3c : decode_any W_a8d3c = Some (Load SZ8 true 17 29 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8d40 : bv 32 := 0x011f7c63.
Lemma F_a8d40 : fetch_word Plain.M.loaded_segments (0xa8d40 : word) = Some W_a8d40.
Proof. vm_refl. Qed.
Lemma D_a8d40 : decode_any W_a8d40 = Some (Branch BC_GEU 30 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8d58 : bv 32 := 0x000f8893.
Lemma F_a8d58 : fetch_word Plain.M.loaded_segments (0xa8d58 : word) = Some W_a8d58.
Proof. vm_refl. Qed.
Lemma D_a8d58 : decode_any W_a8d58 = Some (OpImm ALU_ADD 17 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8d5c : bv 32 := 0xfa9ff06f.
Lemma F_a8d5c : fetch_word Plain.M.loaded_segments (0xa8d5c : word) = Some W_a8d5c.
Proof. vm_refl. Qed.
Lemma D_a8d5c : decode_any W_a8d5c = Some (Jal 0 2097064, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8d60 : bv 32 := 0x02088c63.
Lemma F_a8d60 : fetch_word Plain.M.loaded_segments (0xa8d60 : word) = Some W_a8d60.
Proof. vm_refl. Qed.
Lemma D_a8d60 : decode_any W_a8d60 = Some (Branch BC_EQ 17 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8d98 : bv 32 := 0x0105b603.
Lemma F_a8d98 : fetch_word Plain.M.loaded_segments (0xa8d98 : word) = Some W_a8d98.
Proof. vm_refl. Qed.
Lemma D_a8d98 : decode_any W_a8d98 = Some (Load SZ8 true 12 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8d9c : bv 32 := 0x0205b683.
Lemma F_a8d9c : fetch_word Plain.M.loaded_segments (0xa8d9c : word) = Some W_a8d9c.
Proof. vm_refl. Qed.
Lemma D_a8d9c : decode_any W_a8d9c = Some (Load SZ8 true 13 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8da0 : bv 32 := 0x0285b503.
Lemma F_a8da0 : fetch_word Plain.M.loaded_segments (0xa8da0 : word) = Some W_a8da0.
Proof. vm_refl. Qed.
Lemma D_a8da0 : decode_any W_a8da0 = Some (Load SZ8 true 10 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8da4 : bv 32 := 0x00c68733.
Lemma F_a8da4 : fetch_word Plain.M.loaded_segments (0xa8da4 : word) = Some W_a8da4.
Proof. vm_refl. Qed.
Lemma D_a8da4 : decode_any W_a8da4 = Some (Op ALU_ADD 14 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8da8 : bv 32 := 0xfff50793.
Lemma F_a8da8 : fetch_word Plain.M.loaded_segments (0xa8da8 : word) = Some W_a8da8.
Proof. vm_refl. Qed.
Lemma D_a8da8 : decode_any W_a8da8 = Some (OpImm ALU_ADD 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8dac : bv 32 := 0x40e00733.
Lemma F_a8dac : fetch_word Plain.M.loaded_segments (0xa8dac : word) = Some W_a8dac.
Proof. vm_refl. Qed.
Lemma D_a8dac : decode_any W_a8dac = Some (Op ALU_SUB 14 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8db0 : bv 32 := 0x00c7f633.
Lemma F_a8db0 : fetch_word Plain.M.loaded_segments (0xa8db0 : word) = Some W_a8db0.
Proof. vm_refl. Qed.
Lemma D_a8db0 : decode_any W_a8db0 = Some (Op ALU_AND 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8db4 : bv 32 := 0x00e7f733.
Lemma F_a8db4 : fetch_word Plain.M.loaded_segments (0xa8db4 : word) = Some W_a8db4.
Proof. vm_refl. Qed.
Lemma D_a8db4 : decode_any W_a8db4 = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8db8 : bv 32 := 0x00700793.
Lemma F_a8db8 : fetch_word Plain.M.loaded_segments (0xa8db8 : word) = Some W_a8db8.
Proof. vm_refl. Qed.
Lemma D_a8db8 : decode_any W_a8db8 = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8dbc : bv 32 := 0x00d706b3.
Lemma F_a8dbc : fetch_word Plain.M.loaded_segments (0xa8dbc : word) = Some W_a8dbc.
Proof. vm_refl. Qed.
Lemma D_a8dbc : decode_any W_a8dbc = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8dc0 : bv 32 := 0x02d5b023.
Lemma F_a8dc0 : fetch_word Plain.M.loaded_segments (0xa8dc0 : word) = Some W_a8dc0.
Proof. vm_refl. Qed.
Lemma D_a8dc0 : decode_any W_a8dc0 = Some (Store SZ8 11 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8dc4 : bv 32 := 0x02c5b823.
Lemma F_a8dc4 : fetch_word Plain.M.loaded_segments (0xa8dc4 : word) = Some W_a8dc4.
Proof. vm_refl. Qed.
Lemma D_a8dc4 : decode_any W_a8dc4 = Some (Store SZ8 11 12 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8dc8 : bv 32 := 0x00a7e663.
Lemma F_a8dc8 : fetch_word Plain.M.loaded_segments (0xa8dc8 : word) = Some W_a8dc8.
Proof. vm_refl. Qed.
Lemma D_a8dc8 : decode_any W_a8dc8 = Some (Branch BC_LTU 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8dcc : bv 32 := 0x00800513.
Lemma F_a8dcc : fetch_word Plain.M.loaded_segments (0xa8dcc : word) = Some W_a8dcc.
Proof. vm_refl. Qed.
Lemma D_a8dcc : decode_any W_a8dcc = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8dd0 : bv 32 := 0x02a5b423.
Lemma F_a8dd0 : fetch_word Plain.M.loaded_segments (0xa8dd0 : word) = Some W_a8dd0.
Proof. vm_refl. Qed.
Lemma D_a8dd0 : decode_any W_a8dd0 = Some (Store SZ8 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8dd4 : bv 32 := 0x00d60633.
Lemma F_a8dd4 : fetch_word Plain.M.loaded_segments (0xa8dd4 : word) = Some W_a8dd4.
Proof. vm_refl. Qed.
Lemma D_a8dd4 : decode_any W_a8dd4 = Some (Op ALU_ADD 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8dd8 : bv 32 := 0x000205b7.
Lemma F_a8dd8 : fetch_word Plain.M.loaded_segments (0xa8dd8 : word) = Some W_a8dd8.
Proof. vm_refl. Qed.
Lemma D_a8dd8 : decode_any W_a8dd8 = Some (Lui 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8ddc : bv 32 := 0x00a60633.
Lemma F_a8ddc : fetch_word Plain.M.loaded_segments (0xa8ddc : word) = Some W_a8ddc.
Proof. vm_refl. Qed.
Lemma D_a8ddc : decode_any W_a8ddc = Some (Op ALU_ADD 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8de0 : bv 32 := 0x0d15869b.
Lemma F_a8de0 : fetch_word Plain.M.loaded_segments (0xa8de0 : word) = Some W_a8de0.
Proof. vm_refl. Qed.
Lemma D_a8de0 : decode_any W_a8de0 = Some (OpImm32 13 11 209, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8de4 : bv 32 := 0x0df60593.
Lemma F_a8de4 : fetch_word Plain.M.loaded_segments (0xa8de4 : word) = Some W_a8de4.
Proof. vm_refl. Qed.
Lemma D_a8de4 : decode_any W_a8de4 = Some (OpImm ALU_ADD 11 12 223, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8de8 : bv 32 := 0xff85f593.
Lemma F_a8de8 : fetch_word Plain.M.loaded_segments (0xa8de8 : word) = Some W_a8de8.
Proof. vm_refl. Qed.
Lemma D_a8de8 : decode_any W_a8de8 = Some (OpImm ALU_AND 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8dec : bv 32 := 0x00b4bc23.
Lemma F_a8dec : fetch_word Plain.M.loaded_segments (0xa8dec : word) = Some W_a8dec.
Proof. vm_refl. Qed.
Lemma D_a8dec : decode_any W_a8dec = Some (Store SZ8 9 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8df0 : bv 32 := 0x02a4b023.
Lemma F_a8df0 : fetch_word Plain.M.loaded_segments (0xa8df0 : word) = Some W_a8df0.
Proof. vm_refl. Qed.
Lemma D_a8df0 : decode_any W_a8df0 = Some (Store SZ8 9 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8df4 : bv 32 := 0x02d5ea63.
Lemma F_a8df4 : fetch_word Plain.M.loaded_segments (0xa8df4 : word) = Some W_a8df4.
Proof. vm_refl. Qed.
Lemma D_a8df4 : decode_any W_a8df4 = Some (Branch BC_LTU 11 13 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8e28 : bv 32 := 0x00030697.
Lemma F_a8e28 : fetch_word Plain.M.loaded_segments (0xa8e28 : word) = Some W_a8e28.
Proof. vm_refl. Qed.
Lemma D_a8e28 : decode_any W_a8e28 = Some (Auipc 13 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8e2c : bv 32 := 0x0104b983.
Lemma F_a8e2c : fetch_word Plain.M.loaded_segments (0xa8e2c : word) = Some W_a8e2c.
Proof. vm_refl. Qed.
Lemma D_a8e2c : decode_any W_a8e2c = Some (Load SZ8 true 19 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8e30 : bv 32 := 0x0284b603.
Lemma F_a8e30 : fetch_word Plain.M.loaded_segments (0xa8e30 : word) = Some W_a8e30.
Proof. vm_refl. Qed.
Lemma D_a8e30 : decode_any W_a8e30 = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8e34 : bv 32 := 0xfff50713.
Lemma F_a8e34 : fetch_word Plain.M.loaded_segments (0xa8e34 : word) = Some W_a8e34.
Proof. vm_refl. Qed.
Lemma D_a8e34 : decode_any W_a8e34 = Some (OpImm ALU_ADD 14 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8e38 : bv 32 := 0xf3800793.
Lemma F_a8e38 : fetch_word Plain.M.loaded_segments (0xa8e38 : word) = Some W_a8e38.
Proof. vm_refl. Qed.
Lemma D_a8e38 : decode_any W_a8e38 = Some (OpImm ALU_ADD 15 0 3896, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8e3c : bv 32 := 0x96068513.
Lemma F_a8e3c : fetch_word Plain.M.loaded_segments (0xa8e3c : word) = Some W_a8e3c.
Proof. vm_refl. Qed.
Lemma D_a8e3c : decode_any W_a8e3c = Some (OpImm ALU_ADD 10 13 2400, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8e40 : bv 32 := 0x40a787b3.
Lemma F_a8e40 : fetch_word Plain.M.loaded_segments (0xa8e40 : word) = Some W_a8e40.
Proof. vm_refl. Qed.
Lemma D_a8e40 : decode_any W_a8e40 = Some (Op ALU_SUB 15 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8e44 : bv 32 := 0x00f77733.
Lemma F_a8e44 : fetch_word Plain.M.loaded_segments (0xa8e44 : word) = Some W_a8e44.
Proof. vm_refl. Qed.
Lemma D_a8e44 : decode_any W_a8e44 = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8e48 : bv 32 := 0xfff64693.
Lemma F_a8e48 : fetch_word Plain.M.loaded_segments (0xa8e48 : word) = Some W_a8e48.
Proof. vm_refl. Qed.
Lemma D_a8e48 : decode_any W_a8e48 = Some (OpImm ALU_XOR 13 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8e4c : bv 32 := 0x00e50933.
Lemma F_a8e4c : fetch_word Plain.M.loaded_segments (0xa8e4c : word) = Some W_a8e4c.
Proof. vm_refl. Qed.
Lemma D_a8e4c : decode_any W_a8e4c = Some (Op ALU_ADD 18 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8e50 : bv 32 := 0x00369693.
Lemma F_a8e50 : fetch_word Plain.M.loaded_segments (0xa8e50 : word) = Some W_a8e50.
Proof. vm_refl. Qed.
Lemma D_a8e50 : decode_any W_a8e50 = Some (ShiftImm ALU_SLL 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8e54 : bv 32 := 0x00d506b3.
Lemma F_a8e54 : fetch_word Plain.M.loaded_segments (0xa8e54 : word) = Some W_a8e54.
Proof. vm_refl. Qed.
Lemma D_a8e54 : decode_any W_a8e54 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8e58 : bv 32 := 0x00b68a33.
Lemma F_a8e58 : fetch_word Plain.M.loaded_segments (0xa8e58 : word) = Some W_a8e58.
Proof. vm_refl. Qed.
Lemma D_a8e58 : decode_any W_a8e58 = Some (Op ALU_ADD 20 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8e5c : bv 32 := 0x0c890413.
Lemma F_a8e5c : fetch_word Plain.M.loaded_segments (0xa8e5c : word) = Some W_a8e5c.
Proof. vm_refl. Qed.
Lemma D_a8e5c : decode_any W_a8e5c = Some (OpImm ALU_ADD 8 18 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8e60 : bv 32 := 0x04098463.
Lemma F_a8e60 : fetch_word Plain.M.loaded_segments (0xa8e60 : word) = Some W_a8e60.
Proof. vm_refl. Qed.
Lemma D_a8e60 : decode_any W_a8e60 = Some (Branch BC_EQ 19 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8ea8 : bv 32 := 0x00ca3023.
Lemma F_a8ea8 : fetch_word Plain.M.loaded_segments (0xa8ea8 : word) = Some W_a8ea8.
Proof. vm_refl. Qed.
Lemma D_a8ea8 : decode_any W_a8ea8 = Some (Store SZ8 20 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8eac : bv 32 := 0x0d493023.
Lemma F_a8eac : fetch_word Plain.M.loaded_segments (0xa8eac : word) = Some W_a8eac.
Proof. vm_refl. Qed.
Lemma D_a8eac : decode_any W_a8eac = Some (Store SZ8 18 20 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8eb0 : bv 32 := 0x01293023.
Lemma F_a8eb0 : fetch_word Plain.M.loaded_segments (0xa8eb0 : word) = Some W_a8eb0.
Proof. vm_refl. Qed.
Lemma D_a8eb0 : decode_any W_a8eb0 = Some (Store SZ8 18 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8eb4 : bv 32 := 0x00040513.
Lemma F_a8eb4 : fetch_word Plain.M.loaded_segments (0xa8eb4 : word) = Some W_a8eb4.
Proof. vm_refl. Qed.
Lemma D_a8eb4 : decode_any W_a8eb4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8eb8 : bv 32 := 0x180130ef.
Lemma F_a8eb8 : fetch_word Plain.M.loaded_segments (0xa8eb8 : word) = Some W_a8eb8.
Proof. vm_refl. Qed.
Lemma D_a8eb8 : decode_any W_a8eb8 = Some (Jal 1 78208, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8ebc : bv 32 := 0x04054a63.
Lemma F_a8ebc : fetch_word Plain.M.loaded_segments (0xa8ebc : word) = Some W_a8ebc.
Proof. vm_refl. Qed.
Lemma D_a8ebc : decode_any W_a8ebc = Some (Branch BC_LT 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8ec0 : bv 32 := 0x00051663.
Lemma F_a8ec0 : fetch_word Plain.M.loaded_segments (0xa8ec0 : word) = Some W_a8ec0.
Proof. vm_refl. Qed.
Lemma D_a8ec0 : decode_any W_a8ec0 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8ec4 : bv 32 := 0x00100513.
Lemma F_a8ec4 : fetch_word Plain.M.loaded_segments (0xa8ec4 : word) = Some W_a8ec4.
Proof. vm_refl. Qed.
Lemma D_a8ec4 : decode_any W_a8ec4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8ec8 : bv 32 := 0x00a48023.
Lemma F_a8ec8 : fetch_word Plain.M.loaded_segments (0xa8ec8 : word) = Some W_a8ec8.
Proof. vm_refl. Qed.
Lemma D_a8ec8 : decode_any W_a8ec8 = Some (Store SZ1 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8ecc : bv 32 := 0x00200513.
Lemma F_a8ecc : fetch_word Plain.M.loaded_segments (0xa8ecc : word) = Some W_a8ecc.
Proof. vm_refl. Qed.
Lemma D_a8ecc : decode_any W_a8ecc = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8ed0 : bv 32 := 0x00050597.
Lemma F_a8ed0 : fetch_word Plain.M.loaded_segments (0xa8ed0 : word) = Some W_a8ed0.
Proof. vm_refl. Qed.
Lemma D_a8ed0 : decode_any W_a8ed0 = Some (Auipc 11 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8ed4 : bv 32 := 0x02a92423.
Lemma F_a8ed4 : fetch_word Plain.M.loaded_segments (0xa8ed4 : word) = Some W_a8ed4.
Proof. vm_refl. Qed.
Lemma D_a8ed4 : decode_any W_a8ed4 = Some (Store SZ4 18 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8ed8 : bv 32 := 0x06000893.
Lemma F_a8ed8 : fetch_word Plain.M.loaded_segments (0xa8ed8 : word) = Some W_a8ed8.
Proof. vm_refl. Qed.
Lemma D_a8ed8 : decode_any W_a8ed8 = Some (OpImm ALU_ADD 17 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8edc : bv 32 := 0x98858513.
Lemma F_a8edc : fetch_word Plain.M.loaded_segments (0xa8edc : word) = Some W_a8edc.
Proof. vm_refl. Qed.
Lemma D_a8edc : decode_any W_a8edc = Some (OpImm ALU_ADD 10 11 2440, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8ee0 : bv 32 := 0x03848593.
Lemma F_a8ee0 : fetch_word Plain.M.loaded_segments (0xa8ee0 : word) = Some W_a8ee0.
Proof. vm_refl. Qed.
Lemma D_a8ee0 : decode_any W_a8ee0 = Some (OpImm ALU_ADD 11 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8ee4 : bv 32 := 0x00000073.
Lemma F_a8ee4 : fetch_word Plain.M.loaded_segments (0xa8ee4 : word) = Some W_a8ee4.
Proof. vm_refl. Qed.
Lemma E_a8ee4 : is_ecall W_a8ee4 = true.
Proof. reflexivity. Qed.

Definition W_a8ee8 : bv 32 := 0x07890613.
Lemma F_a8ee8 : fetch_word Plain.M.loaded_segments (0xa8ee8 : word) = Some W_a8ee8.
Proof. vm_refl. Qed.
Lemma D_a8ee8 : decode_any W_a8ee8 = Some (OpImm ALU_ADD 12 18 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8eec : bv 32 := 0x02a92023.
Lemma F_a8eec : fetch_word Plain.M.loaded_segments (0xa8eec : word) = Some W_a8eec.
Proof. vm_refl. Qed.
Lemma D_a8eec : decode_any W_a8eec = Some (Store SZ4 18 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8ef0 : bv 32 := 0x08b93c23.
Lemma F_a8ef0 : fetch_word Plain.M.loaded_segments (0xa8ef0 : word) = Some W_a8ef0.
Proof. vm_refl. Qed.
Lemma D_a8ef0 : decode_any W_a8ef0 = Some (Store SZ8 18 11 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8ef4 : bv 32 := 0x06c93c23.
Lemma F_a8ef4 : fetch_word Plain.M.loaded_segments (0xa8ef4 : word) = Some W_a8ef4.
Proof. vm_refl. Qed.
Lemma D_a8ef4 : decode_any W_a8ef4 = Some (Store SZ8 18 12 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8ef8 : bv 32 := 0x00050517.
Lemma F_a8ef8 : fetch_word Plain.M.loaded_segments (0xa8ef8 : word) = Some W_a8ef8.
Proof. vm_refl. Qed.
Lemma D_a8ef8 : decode_any W_a8ef8 = Some (Auipc 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8efc : bv 32 := 0xbd053503.
Lemma F_a8efc : fetch_word Plain.M.loaded_segments (0xa8efc : word) = Some W_a8efc.
Proof. vm_refl. Qed.
Lemma D_a8efc : decode_any W_a8efc = Some (Load SZ8 true 10 10 3024, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8f00 : bv 32 := 0x01293423.
Lemma F_a8f00 : fetch_word Plain.M.loaded_segments (0xa8f00 : word) = Some W_a8f00.
Proof. vm_refl. Qed.
Lemma D_a8f00 : decode_any W_a8f00 = Some (Store SZ8 18 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8f04 : bv 32 := 0x01293823.
Lemma F_a8f04 : fetch_word Plain.M.loaded_segments (0xa8f04 : word) = Some W_a8f04.
Proof. vm_refl. Qed.
Lemma D_a8f04 : decode_any W_a8f04 = Some (Store SZ8 18 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8f08 : bv 32 := 0x00a93c23.
Lemma F_a8f08 : fetch_word Plain.M.loaded_segments (0xa8f08 : word) = Some W_a8f08.
Proof. vm_refl. Qed.
Lemma D_a8f08 : decode_any W_a8f08 = Some (Store SZ8 18 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8f0c : bv 32 := 0x0080006f.
Lemma F_a8f0c : fetch_word Plain.M.loaded_segments (0xa8f0c : word) = Some W_a8f0c.
Proof. vm_refl. Qed.
Lemma D_a8f0c : decode_any W_a8f0c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8f14 : bv 32 := 0x03813083.
Lemma F_a8f14 : fetch_word Plain.M.loaded_segments (0xa8f14 : word) = Some W_a8f14.
Proof. vm_refl. Qed.
Lemma D_a8f14 : decode_any W_a8f14 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8f18 : bv 32 := 0x03013403.
Lemma F_a8f18 : fetch_word Plain.M.loaded_segments (0xa8f18 : word) = Some W_a8f18.
Proof. vm_refl. Qed.
Lemma D_a8f18 : decode_any W_a8f18 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8f1c : bv 32 := 0x02813483.
Lemma F_a8f1c : fetch_word Plain.M.loaded_segments (0xa8f1c : word) = Some W_a8f1c.
Proof. vm_refl. Qed.
Lemma D_a8f1c : decode_any W_a8f1c = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8f20 : bv 32 := 0x02013903.
Lemma F_a8f20 : fetch_word Plain.M.loaded_segments (0xa8f20 : word) = Some W_a8f20.
Proof. vm_refl. Qed.
Lemma D_a8f20 : decode_any W_a8f20 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8f24 : bv 32 := 0x01813983.
Lemma F_a8f24 : fetch_word Plain.M.loaded_segments (0xa8f24 : word) = Some W_a8f24.
Proof. vm_refl. Qed.
Lemma D_a8f24 : decode_any W_a8f24 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8f28 : bv 32 := 0x01013a03.
Lemma F_a8f28 : fetch_word Plain.M.loaded_segments (0xa8f28 : word) = Some W_a8f28.
Proof. vm_refl. Qed.
Lemma D_a8f28 : decode_any W_a8f28 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8f2c : bv 32 := 0x00813a83.
Lemma F_a8f2c : fetch_word Plain.M.loaded_segments (0xa8f2c : word) = Some W_a8f2c.
Proof. vm_refl. Qed.
Lemma D_a8f2c : decode_any W_a8f2c = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8f30 : bv 32 := 0x04010113.
Lemma F_a8f30 : fetch_word Plain.M.loaded_segments (0xa8f30 : word) = Some W_a8f30.
Proof. vm_refl. Qed.
Lemma D_a8f30 : decode_any W_a8f30 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8f34 : bv 32 := 0x00008067.
Lemma F_a8f34 : fetch_word Plain.M.loaded_segments (0xa8f34 : word) = Some W_a8f34.
Proof. vm_refl. Qed.
Lemma D_a8f34 : decode_any W_a8f34 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

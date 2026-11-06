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

Definition W_4dc58 : bv 32 := 0x81010113.
Lemma F_4dc58 : fetch_word Asan.M.loaded_segments (0x4dc58 : word) = Some W_4dc58.
Proof. vm_refl. Qed.
Lemma D_4dc58 : decode_any W_4dc58 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dc5c : bv 32 := 0x7e113423.
Lemma F_4dc5c : fetch_word Asan.M.loaded_segments (0x4dc5c : word) = Some W_4dc5c.
Proof. vm_refl. Qed.
Lemma D_4dc5c : decode_any W_4dc5c = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dc60 : bv 32 := 0x7e813023.
Lemma F_4dc60 : fetch_word Asan.M.loaded_segments (0x4dc60 : word) = Some W_4dc60.
Proof. vm_refl. Qed.
Lemma D_4dc60 : decode_any W_4dc60 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dc64 : bv 32 := 0x7c913c23.
Lemma F_4dc64 : fetch_word Asan.M.loaded_segments (0x4dc64 : word) = Some W_4dc64.
Proof. vm_refl. Qed.
Lemma D_4dc64 : decode_any W_4dc64 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dc68 : bv 32 := 0x7d213823.
Lemma F_4dc68 : fetch_word Asan.M.loaded_segments (0x4dc68 : word) = Some W_4dc68.
Proof. vm_refl. Qed.
Lemma D_4dc68 : decode_any W_4dc68 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dc6c : bv 32 := 0x7d313423.
Lemma F_4dc6c : fetch_word Asan.M.loaded_segments (0x4dc6c : word) = Some W_4dc6c.
Proof. vm_refl. Qed.
Lemma D_4dc6c : decode_any W_4dc6c = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dc70 : bv 32 := 0x7d413023.
Lemma F_4dc70 : fetch_word Asan.M.loaded_segments (0x4dc70 : word) = Some W_4dc70.
Proof. vm_refl. Qed.
Lemma D_4dc70 : decode_any W_4dc70 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dc74 : bv 32 := 0x7b513c23.
Lemma F_4dc74 : fetch_word Asan.M.loaded_segments (0x4dc74 : word) = Some W_4dc74.
Proof. vm_refl. Qed.
Lemma D_4dc74 : decode_any W_4dc74 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dc78 : bv 32 := 0x7b613823.
Lemma F_4dc78 : fetch_word Asan.M.loaded_segments (0x4dc78 : word) = Some W_4dc78.
Proof. vm_refl. Qed.
Lemma D_4dc78 : decode_any W_4dc78 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dc7c : bv 32 := 0x7f010413.
Lemma F_4dc7c : fetch_word Asan.M.loaded_segments (0x4dc7c : word) = Some W_4dc7c.
Proof. vm_refl. Qed.
Lemma D_4dc7c : decode_any W_4dc7c = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dc80 : bv 32 := 0xf9010113.
Lemma F_4dc80 : fetch_word Asan.M.loaded_segments (0x4dc80 : word) = Some W_4dc80.
Proof. vm_refl. Qed.
Lemma D_4dc80 : decode_any W_4dc80 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dc84 : bv 32 := 0x00050913.
Lemma F_4dc84 : fetch_word Asan.M.loaded_segments (0x4dc84 : word) = Some W_4dc84.
Proof. vm_refl. Qed.
Lemma D_4dc84 : decode_any W_4dc84 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dc88 : bv 32 := 0x44c180ef.
Lemma F_4dc88 : fetch_word Asan.M.loaded_segments (0x4dc88 : word) = Some W_4dc88.
Proof. vm_refl. Qed.
Lemma D_4dc88 : decode_any W_4dc88 = Some (Jal 1 99404, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dc8c : bv 32 := 0x0a050863.
Lemma F_4dc8c : fetch_word Asan.M.loaded_segments (0x4dc8c : word) = Some W_4dc8c.
Proof. vm_refl. Qed.
Lemma D_4dc8c : decode_any W_4dc8c = Some (Branch BC_EQ 10 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dc90 : bv 32 := 0x354190ef.
Lemma F_4dc90 : fetch_word Asan.M.loaded_segments (0x4dc90 : word) = Some W_4dc90.
Proof. vm_refl. Qed.
Lemma D_4dc90 : decode_any W_4dc90 = Some (Jal 1 103252, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dc94 : bv 32 := 0x0008a597.
Lemma F_4dc94 : fetch_word Asan.M.loaded_segments (0x4dc94 : word) = Some W_4dc94.
Proof. vm_refl. Qed.
Lemma D_4dc94 : decode_any W_4dc94 = Some (Auipc 11 138, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dc98 : bv 32 := 0x9fc5b583.
Lemma F_4dc98 : fetch_word Asan.M.loaded_segments (0x4dc98 : word) = Some W_4dc98.
Proof. vm_refl. Qed.
Lemma D_4dc98 : decode_any W_4dc98 = Some (Load SZ8 true 11 11 2556, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dc9c : bv 32 := 0x00050493.
Lemma F_4dc9c : fetch_word Asan.M.loaded_segments (0x4dc9c : word) = Some W_4dc9c.
Proof. vm_refl. Qed.
Lemma D_4dc9c : decode_any W_4dc9c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dca0 : bv 32 := 0x00090513.
Lemma F_4dca0 : fetch_word Asan.M.loaded_segments (0x4dca0 : word) = Some W_4dca0.
Proof. vm_refl. Qed.
Lemma D_4dca0 : decode_any W_4dca0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dca4 : bv 32 := 0x000580e7.
Lemma F_4dca4 : fetch_word Asan.M.loaded_segments (0x4dca4 : word) = Some W_4dca4.
Proof. vm_refl. Qed.
Lemma D_4dca4 : decode_any W_4dca4 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dca8 : bv 32 := 0x06048463.
Lemma F_4dca8 : fetch_word Asan.M.loaded_segments (0x4dca8 : word) = Some W_4dca8.
Proof. vm_refl. Qed.
Lemma D_4dca8 : decode_any W_4dca8 = Some (Branch BC_EQ 9 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dcac : bv 32 := 0x00088597.
Lemma F_4dcac : fetch_word Asan.M.loaded_segments (0x4dcac : word) = Some W_4dcac.
Proof. vm_refl. Qed.
Lemma D_4dcac : decode_any W_4dcac = Some (Auipc 11 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dcb0 : bv 32 := 0xbfc5b983.
Lemma F_4dcb0 : fetch_word Asan.M.loaded_segments (0x4dcb0 : word) = Some W_4dcb0.
Proof. vm_refl. Qed.
Lemma D_4dcb0 : decode_any W_4dcb0 = Some (Load SZ8 true 19 11 3068, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dcb4 : bv 32 := 0x0fb9c583.
Lemma F_4dcb4 : fetch_word Asan.M.loaded_segments (0x4dcb4 : word) = Some W_4dcb4.
Proof. vm_refl. Qed.
Lemma D_4dcb4 : decode_any W_4dcb4 = Some (Load SZ1 false 11 19 251, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dcb8 : bv 32 := 0x04058c63.
Lemma F_4dcb8 : fetch_word Asan.M.loaded_segments (0x4dcb8 : word) = Some W_4dcb8.
Proof. vm_refl. Qed.
Lemma D_4dcb8 : decode_any W_4dcb8 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dcbc : bv 32 := 0x00150493.
Lemma F_4dcbc : fetch_word Asan.M.loaded_segments (0x4dcbc : word) = Some W_4dcbc.
Proof. vm_refl. Qed.
Lemma D_4dcbc : decode_any W_4dcbc = Some (OpImm ALU_ADD 9 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dcc0 : bv 32 := 0xfff94593.
Lemma F_4dcc0 : fetch_word Asan.M.loaded_segments (0x4dcc0 : word) = Some W_4dcc0.
Proof. vm_refl. Qed.
Lemma D_4dcc0 : decode_any W_4dcc0 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dcc4 : bv 32 := 0x80040a13.
Lemma F_4dcc4 : fetch_word Asan.M.loaded_segments (0x4dcc4 : word) = Some W_4dcc4.
Proof. vm_refl. Qed.
Lemma D_4dcc4 : decode_any W_4dcc4 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dcc8 : bv 32 := 0xfa8a0a13.
Lemma F_4dcc8 : fetch_word Asan.M.loaded_segments (0x4dcc8 : word) = Some W_4dcc8.
Proof. vm_refl. Qed.
Lemma D_4dcc8 : decode_any W_4dcc8 = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dccc : bv 32 := 0x0a95e063.
Lemma F_4dccc : fetch_word Asan.M.loaded_segments (0x4dccc : word) = Some W_4dccc.
Proof. vm_refl. Qed.
Lemma D_4dccc : decode_any W_4dccc = Some (Branch BC_LTU 11 9 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dcd0 : bv 32 := 0x04000593.
Lemma F_4dcd0 : fetch_word Asan.M.loaded_segments (0x4dcd0 : word) = Some W_4dcd0.
Proof. vm_refl. Qed.
Lemma D_4dcd0 : decode_any W_4dcd0 = Some (OpImm ALU_ADD 11 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dcd4 : bv 32 := 0x10b57263.
Lemma F_4dcd4 : fetch_word Asan.M.loaded_segments (0x4dcd4 : word) = Some W_4dcd4.
Proof. vm_refl. Qed.
Lemma D_4dcd4 : decode_any W_4dcd4 = Some (Branch BC_GEU 10 11 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dcd8 : bv 32 := 0x00088597.
Lemma F_4dcd8 : fetch_word Asan.M.loaded_segments (0x4dcd8 : word) = Some W_4dcd8.
Proof. vm_refl. Qed.
Lemma D_4dcd8 : decode_any W_4dcd8 = Some (Auipc 11 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dcdc : bv 32 := 0xbe05b583.
Lemma F_4dcdc : fetch_word Asan.M.loaded_segments (0x4dcdc : word) = Some W_4dcdc.
Proof. vm_refl. Qed.
Lemma D_4dcdc : decode_any W_4dcdc = Some (Load SZ8 true 11 11 3040, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dce0 : bv 32 := 0x0005b603.
Lemma F_4dce0 : fetch_word Asan.M.loaded_segments (0x4dce0 : word) = Some W_4dce0.
Proof. vm_refl. Qed.
Lemma D_4dce0 : decode_any W_4dce0 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dce4 : bv 32 := 0x012506b3.
Lemma F_4dce4 : fetch_word Asan.M.loaded_segments (0x4dce4 : word) = Some W_4dce4.
Proof. vm_refl. Qed.
Lemma D_4dce4 : decode_any W_4dce4 = Some (Op ALU_ADD 13 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dce8 : bv 32 := 0x00395593.
Lemma F_4dce8 : fetch_word Asan.M.loaded_segments (0x4dce8 : word) = Some W_4dce8.
Proof. vm_refl. Qed.
Lemma D_4dce8 : decode_any W_4dce8 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dcec : bv 32 := 0x0036d713.
Lemma F_4dcec : fetch_word Asan.M.loaded_segments (0x4dcec : word) = Some W_4dcec.
Proof. vm_refl. Qed.
Lemma D_4dcec : decode_any W_4dcec = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dcf0 : bv 32 := 0x00b605b3.
Lemma F_4dcf0 : fetch_word Asan.M.loaded_segments (0x4dcf0 : word) = Some W_4dcf0.
Proof. vm_refl. Qed.
Lemma D_4dcf0 : decode_any W_4dcf0 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dcf4 : bv 32 := 0x00e60633.
Lemma F_4dcf4 : fetch_word Asan.M.loaded_segments (0x4dcf4 : word) = Some W_4dcf4.
Proof. vm_refl. Qed.
Lemma D_4dcf4 : decode_any W_4dcf4 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dcf8 : bv 32 := 0xff85f713.
Lemma F_4dcf8 : fetch_word Asan.M.loaded_segments (0x4dcf8 : word) = Some W_4dcf8.
Proof. vm_refl. Qed.
Lemma D_4dcf8 : decode_any W_4dcf8 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dcfc : bv 32 := 0xff867793.
Lemma F_4dcfc : fetch_word Asan.M.loaded_segments (0x4dcfc : word) = Some W_4dcfc.
Proof. vm_refl. Qed.
Lemma D_4dcfc : decode_any W_4dcfc = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd00 : bv 32 := 0x00073703.
Lemma F_4dd00 : fetch_word Asan.M.loaded_segments (0x4dd00 : word) = Some W_4dd00.
Proof. vm_refl. Qed.
Lemma D_4dd00 : decode_any W_4dd00 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd04 : bv 32 := 0x0007b783.
Lemma F_4dd04 : fetch_word Asan.M.loaded_segments (0x4dd04 : word) = Some W_4dd04.
Proof. vm_refl. Qed.
Lemma D_4dd04 : decode_any W_4dd04 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd08 : bv 32 := 0x00e7e733.
Lemma F_4dd08 : fetch_word Asan.M.loaded_segments (0x4dd08 : word) = Some W_4dd08.
Proof. vm_refl. Qed.
Lemma D_4dd08 : decode_any W_4dd08 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd0c : bv 32 := 0x0c071e63.
Lemma F_4dd0c : fetch_word Asan.M.loaded_segments (0x4dd0c : word) = Some W_4dd0c.
Proof. vm_refl. Qed.
Lemma D_4dd0c : decode_any W_4dd0c = Some (Branch BC_NE 14 0 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd10 : bv 32 := 0x07010113.
Lemma F_4dd10 : fetch_word Asan.M.loaded_segments (0x4dd10 : word) = Some W_4dd10.
Proof. vm_refl. Qed.
Lemma D_4dd10 : decode_any W_4dd10 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd14 : bv 32 := 0x7e813083.
Lemma F_4dd14 : fetch_word Asan.M.loaded_segments (0x4dd14 : word) = Some W_4dd14.
Proof. vm_refl. Qed.
Lemma D_4dd14 : decode_any W_4dd14 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd18 : bv 32 := 0x7e013403.
Lemma F_4dd18 : fetch_word Asan.M.loaded_segments (0x4dd18 : word) = Some W_4dd18.
Proof. vm_refl. Qed.
Lemma D_4dd18 : decode_any W_4dd18 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd1c : bv 32 := 0x7d813483.
Lemma F_4dd1c : fetch_word Asan.M.loaded_segments (0x4dd1c : word) = Some W_4dd1c.
Proof. vm_refl. Qed.
Lemma D_4dd1c : decode_any W_4dd1c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd20 : bv 32 := 0x7d013903.
Lemma F_4dd20 : fetch_word Asan.M.loaded_segments (0x4dd20 : word) = Some W_4dd20.
Proof. vm_refl. Qed.
Lemma D_4dd20 : decode_any W_4dd20 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd24 : bv 32 := 0x7c813983.
Lemma F_4dd24 : fetch_word Asan.M.loaded_segments (0x4dd24 : word) = Some W_4dd24.
Proof. vm_refl. Qed.
Lemma D_4dd24 : decode_any W_4dd24 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd28 : bv 32 := 0x7c013a03.
Lemma F_4dd28 : fetch_word Asan.M.loaded_segments (0x4dd28 : word) = Some W_4dd28.
Proof. vm_refl. Qed.
Lemma D_4dd28 : decode_any W_4dd28 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd2c : bv 32 := 0x7b813a83.
Lemma F_4dd2c : fetch_word Asan.M.loaded_segments (0x4dd2c : word) = Some W_4dd2c.
Proof. vm_refl. Qed.
Lemma D_4dd2c : decode_any W_4dd2c = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd30 : bv 32 := 0x7b013b03.
Lemma F_4dd30 : fetch_word Asan.M.loaded_segments (0x4dd30 : word) = Some W_4dd30.
Proof. vm_refl. Qed.
Lemma D_4dd30 : decode_any W_4dd30 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd34 : bv 32 := 0x7f010113.
Lemma F_4dd34 : fetch_word Asan.M.loaded_segments (0x4dd34 : word) = Some W_4dd34.
Proof. vm_refl. Qed.
Lemma D_4dd34 : decode_any W_4dd34 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd38 : bv 32 := 0x00008067.
Lemma F_4dd38 : fetch_word Asan.M.loaded_segments (0x4dd38 : word) = Some W_4dd38.
Proof. vm_refl. Qed.
Lemma D_4dd38 : decode_any W_4dd38 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd3c : bv 32 := 0x00090513.
Lemma F_4dd3c : fetch_word Asan.M.loaded_segments (0x4dd3c : word) = Some W_4dd3c.
Proof. vm_refl. Qed.
Lemma D_4dd3c : decode_any W_4dd3c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd40 : bv 32 := 0x07010113.
Lemma F_4dd40 : fetch_word Asan.M.loaded_segments (0x4dd40 : word) = Some W_4dd40.
Proof. vm_refl. Qed.
Lemma D_4dd40 : decode_any W_4dd40 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd44 : bv 32 := 0x7e813083.
Lemma F_4dd44 : fetch_word Asan.M.loaded_segments (0x4dd44 : word) = Some W_4dd44.
Proof. vm_refl. Qed.
Lemma D_4dd44 : decode_any W_4dd44 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd48 : bv 32 := 0x7e013403.
Lemma F_4dd48 : fetch_word Asan.M.loaded_segments (0x4dd48 : word) = Some W_4dd48.
Proof. vm_refl. Qed.
Lemma D_4dd48 : decode_any W_4dd48 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd4c : bv 32 := 0x7d813483.
Lemma F_4dd4c : fetch_word Asan.M.loaded_segments (0x4dd4c : word) = Some W_4dd4c.
Proof. vm_refl. Qed.
Lemma D_4dd4c : decode_any W_4dd4c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd50 : bv 32 := 0x7d013903.
Lemma F_4dd50 : fetch_word Asan.M.loaded_segments (0x4dd50 : word) = Some W_4dd50.
Proof. vm_refl. Qed.
Lemma D_4dd50 : decode_any W_4dd50 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd54 : bv 32 := 0x7c813983.
Lemma F_4dd54 : fetch_word Asan.M.loaded_segments (0x4dd54 : word) = Some W_4dd54.
Proof. vm_refl. Qed.
Lemma D_4dd54 : decode_any W_4dd54 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd58 : bv 32 := 0x7c013a03.
Lemma F_4dd58 : fetch_word Asan.M.loaded_segments (0x4dd58 : word) = Some W_4dd58.
Proof. vm_refl. Qed.
Lemma D_4dd58 : decode_any W_4dd58 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd5c : bv 32 := 0x7b813a83.
Lemma F_4dd5c : fetch_word Asan.M.loaded_segments (0x4dd5c : word) = Some W_4dd5c.
Proof. vm_refl. Qed.
Lemma D_4dd5c : decode_any W_4dd5c = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd60 : bv 32 := 0x7b013b03.
Lemma F_4dd60 : fetch_word Asan.M.loaded_segments (0x4dd60 : word) = Some W_4dd60.
Proof. vm_refl. Qed.
Lemma D_4dd60 : decode_any W_4dd60 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd64 : bv 32 := 0x7f010113.
Lemma F_4dd64 : fetch_word Asan.M.loaded_segments (0x4dd64 : word) = Some W_4dd64.
Proof. vm_refl. Qed.
Lemma D_4dd64 : decode_any W_4dd64 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd68 : bv 32 := 0x74c2306f.
Lemma F_4dd68 : fetch_word Asan.M.loaded_segments (0x4dd68 : word) = Some W_4dd68.
Proof. vm_refl. Qed.
Lemma D_4dd68 : decode_any W_4dd68 = Some (Jal 0 145228, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd6c : bv 32 := 0x80040593.
Lemma F_4dd6c : fetch_word Asan.M.loaded_segments (0x4dd6c : word) = Some W_4dd6c.
Proof. vm_refl. Qed.
Lemma D_4dd6c : decode_any W_4dd6c = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd70 : bv 32 := 0xfb858593.
Lemma F_4dd70 : fetch_word Asan.M.loaded_segments (0x4dd70 : word) = Some W_4dd70.
Proof. vm_refl. Qed.
Lemma D_4dd70 : decode_any W_4dd70 = Some (OpImm ALU_ADD 11 11 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd74 : bv 32 := 0x80040613.
Lemma F_4dd74 : fetch_word Asan.M.loaded_segments (0x4dd74 : word) = Some W_4dd74.
Proof. vm_refl. Qed.
Lemma D_4dd74 : decode_any W_4dd74 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd78 : bv 32 := 0xfa860613.
Lemma F_4dd78 : fetch_word Asan.M.loaded_segments (0x4dd78 : word) = Some W_4dd78.
Proof. vm_refl. Qed.
Lemma D_4dd78 : decode_any W_4dd78 = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd7c : bv 32 := 0x7ff60b13.
Lemma F_4dd7c : fetch_word Asan.M.loaded_segments (0x4dd7c : word) = Some W_4dd7c.
Proof. vm_refl. Qed.
Lemma D_4dd7c : decode_any W_4dd7c = Some (OpImm ALU_ADD 22 12 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd80 : bv 32 := 0x000b34a3.
Lemma F_4dd80 : fetch_word Asan.M.loaded_segments (0x4dd80 : word) = Some W_4dd80.
Proof. vm_refl. Qed.
Lemma D_4dd80 : decode_any W_4dd80 = Some (Store SZ8 22 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd84 : bv 32 := 0x00ba3023.
Lemma F_4dd84 : fetch_word Asan.M.loaded_segments (0x4dd84 : word) = Some W_4dd84.
Proof. vm_refl. Qed.
Lemma D_4dd84 : decode_any W_4dd84 = Some (Store SZ8 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd88 : bv 32 := 0x000a3423.
Lemma F_4dd88 : fetch_word Asan.M.loaded_segments (0x4dd88 : word) = Some W_4dd88.
Proof. vm_refl. Qed.
Lemma D_4dd88 : decode_any W_4dd88 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd8c : bv 32 := 0x00050a93.
Lemma F_4dd8c : fetch_word Asan.M.loaded_segments (0x4dd8c : word) = Some W_4dd8c.
Proof. vm_refl. Qed.
Lemma D_4dd8c : decode_any W_4dd8c = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd90 : bv 32 := 0x29d320ef.
Lemma F_4dd90 : fetch_word Asan.M.loaded_segments (0x4dd90 : word) = Some W_4dd90.
Proof. vm_refl. Qed.
Lemma D_4dd90 : decode_any W_4dd90 = Some (Jal 1 207516, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd94 : bv 32 := 0x00050593.
Lemma F_4dd94 : fetch_word Asan.M.loaded_segments (0x4dd94 : word) = Some W_4dd94.
Proof. vm_refl. Qed.
Lemma D_4dd94 : decode_any W_4dd94 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd98 : bv 32 := 0x0219c703.
Lemma F_4dd98 : fetch_word Asan.M.loaded_segments (0x4dd98 : word) = Some W_4dd98.
Proof. vm_refl. Qed.
Lemma D_4dd98 : decode_any W_4dd98 = Some (Load SZ1 false 14 19 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dd9c : bv 32 := 0x008b34a3.
Lemma F_4dd9c : fetch_word Asan.M.loaded_segments (0x4dd9c : word) = Some W_4dd9c.
Proof. vm_refl. Qed.
Lemma D_4dd9c : decode_any W_4dd9c = Some (Store SZ8 22 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dda0 : bv 32 := 0x80040513.
Lemma F_4dda0 : fetch_word Asan.M.loaded_segments (0x4dda0 : word) = Some W_4dda0.
Proof. vm_refl. Qed.
Lemma D_4dda0 : decode_any W_4dda0 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dda4 : bv 32 := 0xfa850513.
Lemma F_4dda4 : fetch_word Asan.M.loaded_segments (0x4dda4 : word) = Some W_4dda4.
Proof. vm_refl. Qed.
Lemma D_4dda4 : decode_any W_4dda4 = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dda8 : bv 32 := 0x0ff00793.
Lemma F_4dda8 : fetch_word Asan.M.loaded_segments (0x4dda8 : word) = Some W_4dda8.
Proof. vm_refl. Qed.
Lemma D_4dda8 : decode_any W_4dda8 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ddac : bv 32 := 0x00040613.
Lemma F_4ddac : fetch_word Asan.M.loaded_segments (0x4ddac : word) = Some W_4ddac.
Proof. vm_refl. Qed.
Lemma D_4ddac : decode_any W_4ddac = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ddb0 : bv 32 := 0x00000693.
Lemma F_4ddb0 : fetch_word Asan.M.loaded_segments (0x4ddb0 : word) = Some W_4ddb0.
Proof. vm_refl. Qed.
Lemma D_4ddb0 : decode_any W_4ddb0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ddb4 : bv 32 := 0x7c9190ef.
Lemma F_4ddb4 : fetch_word Asan.M.loaded_segments (0x4ddb4 : word) = Some W_4ddb4.
Proof. vm_refl. Qed.
Lemma D_4ddb4 : decode_any W_4ddb4 = Some (Jal 1 106440, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ddb8 : bv 32 := 0x80040613.
Lemma F_4ddb8 : fetch_word Asan.M.loaded_segments (0x4ddb8 : word) = Some W_4ddb8.
Proof. vm_refl. Qed.
Lemma D_4ddb8 : decode_any W_4ddb8 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ddbc : bv 32 := 0xfa860613.
Lemma F_4ddbc : fetch_word Asan.M.loaded_segments (0x4ddbc : word) = Some W_4ddbc.
Proof. vm_refl. Qed.
Lemma D_4ddbc : decode_any W_4ddbc = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ddc0 : bv 32 := 0x00090513.
Lemma F_4ddc0 : fetch_word Asan.M.loaded_segments (0x4ddc0 : word) = Some W_4ddc0.
Proof. vm_refl. Qed.
Lemma D_4ddc0 : decode_any W_4ddc0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ddc4 : bv 32 := 0x00048593.
Lemma F_4ddc4 : fetch_word Asan.M.loaded_segments (0x4ddc4 : word) = Some W_4ddc4.
Proof. vm_refl. Qed.
Lemma D_4ddc4 : decode_any W_4ddc4 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ddc8 : bv 32 := 0x56d160ef.
Lemma F_4ddc8 : fetch_word Asan.M.loaded_segments (0x4ddc8 : word) = Some W_4ddc8.
Proof. vm_refl. Qed.
Lemma D_4ddc8 : decode_any W_4ddc8 = Some (Jal 1 93548, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ddcc : bv 32 := 0x000a8513.
Lemma F_4ddcc : fetch_word Asan.M.loaded_segments (0x4ddcc : word) = Some W_4ddcc.
Proof. vm_refl. Qed.
Lemma D_4ddcc : decode_any W_4ddcc = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ddd0 : bv 32 := 0x04000593.
Lemma F_4ddd0 : fetch_word Asan.M.loaded_segments (0x4ddd0 : word) = Some W_4ddd0.
Proof. vm_refl. Qed.
Lemma D_4ddd0 : decode_any W_4ddd0 = Some (OpImm ALU_ADD 11 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ddd4 : bv 32 := 0xf0bae2e3.
Lemma F_4ddd4 : fetch_word Asan.M.loaded_segments (0x4ddd4 : word) = Some W_4ddd4.
Proof. vm_refl. Qed.
Lemma D_4ddd4 : decode_any W_4ddd4 = Some (Branch BC_LTU 21 11 7940, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ddd8 : bv 32 := 0x00050a93.
Lemma F_4ddd8 : fetch_word Asan.M.loaded_segments (0x4ddd8 : word) = Some W_4ddd8.
Proof. vm_refl. Qed.
Lemma D_4ddd8 : decode_any W_4ddd8 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dddc : bv 32 := 0x04049263.
Lemma F_4dddc : fetch_word Asan.M.loaded_segments (0x4dddc : word) = Some W_4dddc.
Proof. vm_refl. Qed.
Lemma D_4dddc : decode_any W_4dddc = Some (Branch BC_NE 9 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dde0 : bv 32 := 0xfff00513.
Lemma F_4dde0 : fetch_word Asan.M.loaded_segments (0x4dde0 : word) = Some W_4dde0.
Proof. vm_refl. Qed.
Lemma D_4dde0 : decode_any W_4dde0 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dde4 : bv 32 := 0xf2dff06f.
Lemma F_4dde4 : fetch_word Asan.M.loaded_segments (0x4dde4 : word) = Some W_4dde4.
Proof. vm_refl. Qed.
Lemma D_4dde4 : decode_any W_4dde4 = Some (Jal 0 2096940, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dde8 : bv 32 := 0x00050a93.
Lemma F_4dde8 : fetch_word Asan.M.loaded_segments (0x4dde8 : word) = Some W_4dde8.
Proof. vm_refl. Qed.
Lemma D_4dde8 : decode_any W_4dde8 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ddec : bv 32 := 0x00060503.
Lemma F_4ddec : fetch_word Asan.M.loaded_segments (0x4ddec : word) = Some W_4ddec.
Proof. vm_refl. Qed.
Lemma D_4ddec : decode_any W_4ddec = Some (Load SZ1 true 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ddf0 : bv 32 := 0x0076f693.
Lemma F_4ddf0 : fetch_word Asan.M.loaded_segments (0x4ddf0 : word) = Some W_4ddf0.
Proof. vm_refl. Qed.
Lemma D_4ddf0 : decode_any W_4ddf0 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ddf4 : bv 32 := 0x00a03733.
Lemma F_4ddf4 : fetch_word Asan.M.loaded_segments (0x4ddf4 : word) = Some W_4ddf4.
Proof. vm_refl. Qed.
Lemma D_4ddf4 : decode_any W_4ddf4 = Some (Op ALU_SLTU 14 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ddf8 : bv 32 := 0x00a6a533.
Lemma F_4ddf8 : fetch_word Asan.M.loaded_segments (0x4ddf8 : word) = Some W_4ddf8.
Proof. vm_refl. Qed.
Lemma D_4ddf8 : decode_any W_4ddf8 = Some (Op ALU_SLT 10 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ddfc : bv 32 := 0x00154513.
Lemma F_4ddfc : fetch_word Asan.M.loaded_segments (0x4ddfc : word) = Some W_4ddfc.
Proof. vm_refl. Qed.
Lemma D_4ddfc : decode_any W_4ddfc = Some (OpImm ALU_XOR 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de00 : bv 32 := 0x00a77533.
Lemma F_4de00 : fetch_word Asan.M.loaded_segments (0x4de00 : word) = Some W_4de00.
Proof. vm_refl. Qed.
Lemma D_4de00 : decode_any W_4de00 = Some (Op ALU_AND 10 14 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de04 : bv 32 := 0x00c5fa63.
Lemma F_4de04 : fetch_word Asan.M.loaded_segments (0x4de04 : word) = Some W_4de04.
Proof. vm_refl. Qed.
Lemma D_4de04 : decode_any W_4de04 = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de08 : bv 32 := 0x0005c683.
Lemma F_4de08 : fetch_word Asan.M.loaded_segments (0x4de08 : word) = Some W_4de08.
Proof. vm_refl. Qed.
Lemma D_4de08 : decode_any W_4de08 = Some (Load SZ1 false 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de0c : bv 32 := 0x00158593.
Lemma F_4de0c : fetch_word Asan.M.loaded_segments (0x4de0c : word) = Some W_4de0c.
Proof. vm_refl. Qed.
Lemma D_4de0c : decode_any W_4de0c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de10 : bv 32 := 0x00a6e533.
Lemma F_4de10 : fetch_word Asan.M.loaded_segments (0x4de10 : word) = Some W_4de10.
Proof. vm_refl. Qed.
Lemma D_4de10 : decode_any W_4de10 = Some (Op ALU_OR 10 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de14 : bv 32 := 0xfec59ae3.
Lemma F_4de14 : fetch_word Asan.M.loaded_segments (0x4de14 : word) = Some W_4de14.
Proof. vm_refl. Qed.
Lemma D_4de14 : decode_any W_4de14 = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de18 : bv 32 := 0x0ff57513.
Lemma F_4de18 : fetch_word Asan.M.loaded_segments (0x4de18 : word) = Some W_4de18.
Proof. vm_refl. Qed.
Lemma D_4de18 : decode_any W_4de18 = Some (OpImm ALU_AND 10 10 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de1c : bv 32 := 0x0c050463.
Lemma F_4de1c : fetch_word Asan.M.loaded_segments (0x4de1c : word) = Some W_4de1c.
Proof. vm_refl. Qed.
Lemma D_4de1c : decode_any W_4de1c = Some (Branch BC_EQ 10 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de20 : bv 32 := 0x00090513.
Lemma F_4de20 : fetch_word Asan.M.loaded_segments (0x4de20 : word) = Some W_4de20.
Proof. vm_refl. Qed.
Lemma D_4de20 : decode_any W_4de20 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de24 : bv 32 := 0x00048593.
Lemma F_4de24 : fetch_word Asan.M.loaded_segments (0x4de24 : word) = Some W_4de24.
Proof. vm_refl. Qed.
Lemma D_4de24 : decode_any W_4de24 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de28 : bv 32 := 0x2d9130ef.
Lemma F_4de28 : fetch_word Asan.M.loaded_segments (0x4de28 : word) = Some W_4de28.
Proof. vm_refl. Qed.
Lemma D_4de28 : decode_any W_4de28 = Some (Jal 1 80600, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de2c : bv 32 := 0x0a050c63.
Lemma F_4de2c : fetch_word Asan.M.loaded_segments (0x4de2c : word) = Some W_4de2c.
Proof. vm_refl. Qed.
Lemma D_4de2c : decode_any W_4de2c = Some (Branch BC_EQ 10 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de30 : bv 32 := 0x00050913.
Lemma F_4de30 : fetch_word Asan.M.loaded_segments (0x4de30 : word) = Some W_4de30.
Proof. vm_refl. Qed.
Lemma D_4de30 : decode_any W_4de30 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de34 : bv 32 := 0xfffc9517.
Lemma F_4de34 : fetch_word Asan.M.loaded_segments (0x4de34 : word) = Some W_4de34.
Proof. vm_refl. Qed.
Lemma D_4de34 : decode_any W_4de34 = Some (Auipc 10 1048521, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de38 : bv 32 := 0x4ce50513.
Lemma F_4de38 : fetch_word Asan.M.loaded_segments (0x4de38 : word) = Some W_4de38.
Proof. vm_refl. Qed.
Lemma D_4de38 : decode_any W_4de38 = Some (OpImm ALU_ADD 10 10 1230, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de3c : bv 32 := 0x6ed1a0ef.
Lemma F_4de3c : fetch_word Asan.M.loaded_segments (0x4de3c : word) = Some W_4de3c.
Proof. vm_refl. Qed.
Lemma D_4de3c : decode_any W_4de3c = Some (Jal 1 110316, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de40 : bv 32 := 0x0a051263.
Lemma F_4de40 : fetch_word Asan.M.loaded_segments (0x4de40 : word) = Some W_4de40.
Proof. vm_refl. Qed.
Lemma D_4de40 : decode_any W_4de40 = Some (Branch BC_NE 10 0 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de44 : bv 32 := 0x74d1a0ef.
Lemma F_4de44 : fetch_word Asan.M.loaded_segments (0x4de44 : word) = Some W_4de44.
Proof. vm_refl. Qed.
Lemma D_4de44 : decode_any W_4de44 = Some (Jal 1 110412, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de48 : bv 32 := 0x06050263.
Lemma F_4de48 : fetch_word Asan.M.loaded_segments (0x4de48 : word) = Some W_4de48.
Proof. vm_refl. Qed.
Lemma D_4de48 : decode_any W_4de48 = Some (Branch BC_EQ 10 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de4c : bv 32 := 0x80040513.
Lemma F_4de4c : fetch_word Asan.M.loaded_segments (0x4de4c : word) = Some W_4de4c.
Proof. vm_refl. Qed.
Lemma D_4de4c : decode_any W_4de4c = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de50 : bv 32 := 0xfb850513.
Lemma F_4de50 : fetch_word Asan.M.loaded_segments (0x4de50 : word) = Some W_4de50.
Proof. vm_refl. Qed.
Lemma D_4de50 : decode_any W_4de50 = Some (OpImm ALU_ADD 10 10 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de54 : bv 32 := 0x80040593.
Lemma F_4de54 : fetch_word Asan.M.loaded_segments (0x4de54 : word) = Some W_4de54.
Proof. vm_refl. Qed.
Lemma D_4de54 : decode_any W_4de54 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de58 : bv 32 := 0xfa858593.
Lemma F_4de58 : fetch_word Asan.M.loaded_segments (0x4de58 : word) = Some W_4de58.
Proof. vm_refl. Qed.
Lemma D_4de58 : decode_any W_4de58 = Some (OpImm ALU_ADD 11 11 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de5c : bv 32 := 0x7ff58b13.
Lemma F_4de5c : fetch_word Asan.M.loaded_segments (0x4de5c : word) = Some W_4de5c.
Proof. vm_refl. Qed.
Lemma D_4de5c : decode_any W_4de5c = Some (OpImm ALU_ADD 22 11 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de60 : bv 32 := 0x000b34a3.
Lemma F_4de60 : fetch_word Asan.M.loaded_segments (0x4de60 : word) = Some W_4de60.
Proof. vm_refl. Qed.
Lemma D_4de60 : decode_any W_4de60 = Some (Store SZ8 22 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de64 : bv 32 := 0x00aa3023.
Lemma F_4de64 : fetch_word Asan.M.loaded_segments (0x4de64 : word) = Some W_4de64.
Proof. vm_refl. Qed.
Lemma D_4de64 : decode_any W_4de64 = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de68 : bv 32 := 0x000a3423.
Lemma F_4de68 : fetch_word Asan.M.loaded_segments (0x4de68 : word) = Some W_4de68.
Proof. vm_refl. Qed.
Lemma D_4de68 : decode_any W_4de68 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de6c : bv 32 := 0x1c1320ef.
Lemma F_4de6c : fetch_word Asan.M.loaded_segments (0x4de6c : word) = Some W_4de6c.
Proof. vm_refl. Qed.
Lemma D_4de6c : decode_any W_4de6c = Some (Jal 1 207296, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de70 : bv 32 := 0x00050593.
Lemma F_4de70 : fetch_word Asan.M.loaded_segments (0x4de70 : word) = Some W_4de70.
Proof. vm_refl. Qed.
Lemma D_4de70 : decode_any W_4de70 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de74 : bv 32 := 0x0219c703.
Lemma F_4de74 : fetch_word Asan.M.loaded_segments (0x4de74 : word) = Some W_4de74.
Proof. vm_refl. Qed.
Lemma D_4de74 : decode_any W_4de74 = Some (Load SZ1 false 14 19 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de78 : bv 32 := 0x008b34a3.
Lemma F_4de78 : fetch_word Asan.M.loaded_segments (0x4de78 : word) = Some W_4de78.
Proof. vm_refl. Qed.
Lemma D_4de78 : decode_any W_4de78 = Some (Store SZ8 22 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de7c : bv 32 := 0x80040513.
Lemma F_4de7c : fetch_word Asan.M.loaded_segments (0x4de7c : word) = Some W_4de7c.
Proof. vm_refl. Qed.
Lemma D_4de7c : decode_any W_4de7c = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de80 : bv 32 := 0xfa850513.
Lemma F_4de80 : fetch_word Asan.M.loaded_segments (0x4de80 : word) = Some W_4de80.
Proof. vm_refl. Qed.
Lemma D_4de80 : decode_any W_4de80 = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de84 : bv 32 := 0x0ff00793.
Lemma F_4de84 : fetch_word Asan.M.loaded_segments (0x4de84 : word) = Some W_4de84.
Proof. vm_refl. Qed.
Lemma D_4de84 : decode_any W_4de84 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de88 : bv 32 := 0x00040613.
Lemma F_4de88 : fetch_word Asan.M.loaded_segments (0x4de88 : word) = Some W_4de88.
Proof. vm_refl. Qed.
Lemma D_4de88 : decode_any W_4de88 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de8c : bv 32 := 0x00000693.
Lemma F_4de8c : fetch_word Asan.M.loaded_segments (0x4de8c : word) = Some W_4de8c.
Proof. vm_refl. Qed.
Lemma D_4de8c : decode_any W_4de8c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de90 : bv 32 := 0x6ed190ef.
Lemma F_4de90 : fetch_word Asan.M.loaded_segments (0x4de90 : word) = Some W_4de90.
Proof. vm_refl. Qed.
Lemma D_4de90 : decode_any W_4de90 = Some (Jal 1 106220, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de94 : bv 32 := 0x80040513.
Lemma F_4de94 : fetch_word Asan.M.loaded_segments (0x4de94 : word) = Some W_4de94.
Proof. vm_refl. Qed.
Lemma D_4de94 : decode_any W_4de94 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de98 : bv 32 := 0xfa850513.
Lemma F_4de98 : fetch_word Asan.M.loaded_segments (0x4de98 : word) = Some W_4de98.
Proof. vm_refl. Qed.
Lemma D_4de98 : decode_any W_4de98 = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4de9c : bv 32 := 0x1fc1b0ef.
Lemma F_4de9c : fetch_word Asan.M.loaded_segments (0x4de9c : word) = Some W_4de9c.
Proof. vm_refl. Qed.
Lemma D_4de9c : decode_any W_4de9c = Some (Jal 1 111100, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dea0 : bv 32 := 0x00040993.
Lemma F_4dea0 : fetch_word Asan.M.loaded_segments (0x4dea0 : word) = Some W_4dea0.
Proof. vm_refl. Qed.
Lemma D_4dea0 : decode_any W_4dea0 = Some (OpImm ALU_ADD 19 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dea4 : bv 32 := 0x00050663.
Lemma F_4dea4 : fetch_word Asan.M.loaded_segments (0x4dea4 : word) = Some W_4dea4.
Proof. vm_refl. Qed.
Lemma D_4dea4 : decode_any W_4dea4 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dea8 : bv 32 := 0x03c0006f.
Lemma F_4dea8 : fetch_word Asan.M.loaded_segments (0x4dea8 : word) = Some W_4dea8.
Proof. vm_refl. Qed.
Lemma D_4dea8 : decode_any W_4dea8 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_4deac : bv 32 := 0x00040993.
Lemma F_4deac : fetch_word Asan.M.loaded_segments (0x4deac : word) = Some W_4deac.
Proof. vm_refl. Qed.
Lemma D_4deac : decode_any W_4deac = Some (OpImm ALU_ADD 19 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4deb0 : bv 32 := 0x17d320ef.
Lemma F_4deb0 : fetch_word Asan.M.loaded_segments (0x4deb0 : word) = Some W_4deb0.
Proof. vm_refl. Qed.
Lemma D_4deb0 : decode_any W_4deb0 = Some (Jal 1 207228, 4%Z).
Proof. vm_refl. Qed.

Definition W_4deb4 : bv 32 := 0xfffc2597.
Lemma F_4deb4 : fetch_word Asan.M.loaded_segments (0x4deb4 : word) = Some W_4deb4.
Proof. vm_refl. Qed.
Lemma D_4deb4 : decode_any W_4deb4 = Some (Auipc 11 1048514, 4%Z).
Proof. vm_refl. Qed.

Definition W_4deb8 : bv 32 := 0x5545b583.
Lemma F_4deb8 : fetch_word Asan.M.loaded_segments (0x4deb8 : word) = Some W_4deb8.
Proof. vm_refl. Qed.
Lemma D_4deb8 : decode_any W_4deb8 = Some (Load SZ8 true 11 11 1364, 4%Z).
Proof. vm_refl. Qed.

Definition W_4debc : bv 32 := 0x00ba3023.
Lemma F_4debc : fetch_word Asan.M.loaded_segments (0x4debc : word) = Some W_4debc.
Proof. vm_refl. Qed.
Lemma D_4debc : decode_any W_4debc = Some (Store SZ8 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dec0 : bv 32 := 0x80040613.
Lemma F_4dec0 : fetch_word Asan.M.loaded_segments (0x4dec0 : word) = Some W_4dec0.
Proof. vm_refl. Qed.
Lemma D_4dec0 : decode_any W_4dec0 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dec4 : bv 32 := 0xfa860613.
Lemma F_4dec4 : fetch_word Asan.M.loaded_segments (0x4dec4 : word) = Some W_4dec4.
Proof. vm_refl. Qed.
Lemma D_4dec4 : decode_any W_4dec4 = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dec8 : bv 32 := 0x00098593.
Lemma F_4dec8 : fetch_word Asan.M.loaded_segments (0x4dec8 : word) = Some W_4dec8.
Proof. vm_refl. Qed.
Lemma D_4dec8 : decode_any W_4dec8 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4decc : bv 32 := 0x00090693.
Lemma F_4decc : fetch_word Asan.M.loaded_segments (0x4decc : word) = Some W_4decc.
Proof. vm_refl. Qed.
Lemma D_4decc : decode_any W_4decc = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ded0 : bv 32 := 0x00000713.
Lemma F_4ded0 : fetch_word Asan.M.loaded_segments (0x4ded0 : word) = Some W_4ded0.
Proof. vm_refl. Qed.
Lemma D_4ded0 : decode_any W_4ded0 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ded4 : bv 32 := 0x00048793.
Lemma F_4ded4 : fetch_word Asan.M.loaded_segments (0x4ded4 : word) = Some W_4ded4.
Proof. vm_refl. Qed.
Lemma D_4ded4 : decode_any W_4ded4 = Some (OpImm ALU_ADD 15 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ded8 : bv 32 := 0x00000813.
Lemma F_4ded8 : fetch_word Asan.M.loaded_segments (0x4ded8 : word) = Some W_4ded8.
Proof. vm_refl. Qed.
Lemma D_4ded8 : decode_any W_4ded8 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dedc : bv 32 := 0x00000893.
Lemma F_4dedc : fetch_word Asan.M.loaded_segments (0x4dedc : word) = Some W_4dedc.
Proof. vm_refl. Qed.
Lemma D_4dedc : decode_any W_4dedc = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dee0 : bv 32 := 0x1ac170ef.
Lemma F_4dee0 : fetch_word Asan.M.loaded_segments (0x4dee0 : word) = Some W_4dee0.
Proof. vm_refl. Qed.
Lemma D_4dee0 : decode_any W_4dee0 = Some (Jal 1 94636, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dee4 : bv 32 := 0x000a8513.
Lemma F_4dee4 : fetch_word Asan.M.loaded_segments (0x4dee4 : word) = Some W_4dee4.
Proof. vm_refl. Qed.
Lemma D_4dee4 : decode_any W_4dee4 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4dee8 : bv 32 := 0xe29ff06f.
Lemma F_4dee8 : fetch_word Asan.M.loaded_segments (0x4dee8 : word) = Some W_4dee8.
Proof. vm_refl. Qed.
Lemma D_4dee8 : decode_any W_4dee8 = Some (Jal 0 2096680, 4%Z).
Proof. vm_refl. Qed.

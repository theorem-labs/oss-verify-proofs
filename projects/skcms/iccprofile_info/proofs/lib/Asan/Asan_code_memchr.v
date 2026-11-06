(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_97d20 : bv 32 := 0x0ff5f593.
Lemma F_97d20 : fetch_word Asan.M.loaded_segments (0x97d20 : word) = Some W_97d20.
Proof. vm_refl. Qed.
Lemma D_97d20 : decode_any W_97d20 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97d24 : bv 32 := 0x00757693.
Lemma F_97d24 : fetch_word Asan.M.loaded_segments (0x97d24 : word) = Some W_97d24.
Proof. vm_refl. Qed.
Lemma D_97d24 : decode_any W_97d24 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97d28 : bv 32 := 0x00c03733.
Lemma F_97d28 : fetch_word Asan.M.loaded_segments (0x97d28 : word) = Some W_97d28.
Proof. vm_refl. Qed.
Lemma D_97d28 : decode_any W_97d28 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97d2c : bv 32 := 0x02068c63.
Lemma F_97d2c : fetch_word Asan.M.loaded_segments (0x97d2c : word) = Some W_97d2c.
Proof. vm_refl. Qed.
Lemma D_97d2c : decode_any W_97d2c = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97d30 : bv 32 := 0x02060a63.
Lemma F_97d30 : fetch_word Asan.M.loaded_segments (0x97d30 : word) = Some W_97d30.
Proof. vm_refl. Qed.
Lemma D_97d30 : decode_any W_97d30 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97d34 : bv 32 := 0x00150793.
Lemma F_97d34 : fetch_word Asan.M.loaded_segments (0x97d34 : word) = Some W_97d34.
Proof. vm_refl. Qed.
Lemma D_97d34 : decode_any W_97d34 = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97d38 : bv 32 := 0x00100813.
Lemma F_97d38 : fetch_word Asan.M.loaded_segments (0x97d38 : word) = Some W_97d38.
Proof. vm_refl. Qed.
Lemma D_97d38 : decode_any W_97d38 = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97d3c : bv 32 := 0x00054703.
Lemma F_97d3c : fetch_word Asan.M.loaded_segments (0x97d3c : word) = Some W_97d3c.
Proof. vm_refl. Qed.
Lemma D_97d3c : decode_any W_97d3c = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97d40 : bv 32 := 0x00060693.
Lemma F_97d40 : fetch_word Asan.M.loaded_segments (0x97d40 : word) = Some W_97d40.
Proof. vm_refl. Qed.
Lemma D_97d40 : decode_any W_97d40 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97d44 : bv 32 := 0x06b70e63.
Lemma F_97d44 : fetch_word Asan.M.loaded_segments (0x97d44 : word) = Some W_97d44.
Proof. vm_refl. Qed.
Lemma D_97d44 : decode_any W_97d44 = Some (Branch BC_EQ 14 11 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97d48 : bv 32 := 0x00150513.
Lemma F_97d48 : fetch_word Asan.M.loaded_segments (0x97d48 : word) = Some W_97d48.
Proof. vm_refl. Qed.
Lemma D_97d48 : decode_any W_97d48 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97d4c : bv 32 := 0xfff68613.
Lemma F_97d4c : fetch_word Asan.M.loaded_segments (0x97d4c : word) = Some W_97d4c.
Proof. vm_refl. Qed.
Lemma D_97d4c : decode_any W_97d4c = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97d50 : bv 32 := 0x0077f893.
Lemma F_97d50 : fetch_word Asan.M.loaded_segments (0x97d50 : word) = Some W_97d50.
Proof. vm_refl. Qed.
Lemma D_97d50 : decode_any W_97d50 = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97d54 : bv 32 := 0x00c03733.
Lemma F_97d54 : fetch_word Asan.M.loaded_segments (0x97d54 : word) = Some W_97d54.
Proof. vm_refl. Qed.
Lemma D_97d54 : decode_any W_97d54 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97d58 : bv 32 := 0x00088663.
Lemma F_97d58 : fetch_word Asan.M.loaded_segments (0x97d58 : word) = Some W_97d58.
Proof. vm_refl. Qed.
Lemma D_97d58 : decode_any W_97d58 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97d5c : bv 32 := 0x00178793.
Lemma F_97d5c : fetch_word Asan.M.loaded_segments (0x97d5c : word) = Some W_97d5c.
Proof. vm_refl. Qed.
Lemma D_97d5c : decode_any W_97d5c = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97d60 : bv 32 := 0xfd069ee3.
Lemma F_97d60 : fetch_word Asan.M.loaded_segments (0x97d60 : word) = Some W_97d60.
Proof. vm_refl. Qed.
Lemma D_97d60 : decode_any W_97d60 = Some (Branch BC_NE 13 16 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97d64 : bv 32 := 0x06070863.
Lemma F_97d64 : fetch_word Asan.M.loaded_segments (0x97d64 : word) = Some W_97d64.
Proof. vm_refl. Qed.
Lemma D_97d64 : decode_any W_97d64 = Some (Branch BC_EQ 14 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97d68 : bv 32 := 0x00054683.
Lemma F_97d68 : fetch_word Asan.M.loaded_segments (0x97d68 : word) = Some W_97d68.
Proof. vm_refl. Qed.
Lemma D_97d68 : decode_any W_97d68 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97d6c : bv 32 := 0x04b68663.
Lemma F_97d6c : fetch_word Asan.M.loaded_segments (0x97d6c : word) = Some W_97d6c.
Proof. vm_refl. Qed.
Lemma D_97d6c : decode_any W_97d6c = Some (Branch BC_EQ 13 11 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97d70 : bv 32 := 0x00800693.
Lemma F_97d70 : fetch_word Asan.M.loaded_segments (0x97d70 : word) = Some W_97d70.
Proof. vm_refl. Qed.
Lemma D_97d70 : decode_any W_97d70 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97d74 : bv 32 := 0x04d66263.
Lemma F_97d74 : fetch_word Asan.M.loaded_segments (0x97d74 : word) = Some W_97d74.
Proof. vm_refl. Qed.
Lemma D_97d74 : decode_any W_97d74 = Some (Branch BC_LTU 12 13 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97d78 : bv 32 := 0xfff78697.
Lemma F_97d78 : fetch_word Asan.M.loaded_segments (0x97d78 : word) = Some W_97d78.
Proof. vm_refl. Qed.
Lemma D_97d78 : decode_any W_97d78 = Some (Auipc 13 1048440, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97d7c : bv 32 := 0x5f06b683.
Lemma F_97d7c : fetch_word Asan.M.loaded_segments (0x97d7c : word) = Some W_97d7c.
Proof. vm_refl. Qed.
Lemma D_97d7c : decode_any W_97d7c = Some (Load SZ8 true 13 13 1520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97d80 : bv 32 := 0xfff78717.
Lemma F_97d80 : fetch_word Asan.M.loaded_segments (0x97d80 : word) = Some W_97d80.
Proof. vm_refl. Qed.
Lemma D_97d80 : decode_any W_97d80 = Some (Auipc 14 1048440, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97d84 : bv 32 := 0x5d073703.
Lemma F_97d84 : fetch_word Asan.M.loaded_segments (0x97d84 : word) = Some W_97d84.
Proof. vm_refl. Qed.
Lemma D_97d84 : decode_any W_97d84 = Some (Load SZ8 true 14 14 1488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97d88 : bv 32 := 0x00168793.
Lemma F_97d88 : fetch_word Asan.M.loaded_segments (0x97d88 : word) = Some W_97d88.
Proof. vm_refl. Qed.
Lemma D_97d88 : decode_any W_97d88 = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97d8c : bv 32 := 0x02f587b3.
Lemma F_97d8c : fetch_word Asan.M.loaded_segments (0x97d8c : word) = Some W_97d8c.
Proof. vm_refl. Qed.
Lemma D_97d8c : decode_any W_97d8c = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97d90 : bv 32 := 0x00700813.
Lemma F_97d90 : fetch_word Asan.M.loaded_segments (0x97d90 : word) = Some W_97d90.
Proof. vm_refl. Qed.
Lemma D_97d90 : decode_any W_97d90 = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97d94 : bv 32 := 0x00053883.
Lemma F_97d94 : fetch_word Asan.M.loaded_segments (0x97d94 : word) = Some W_97d94.
Proof. vm_refl. Qed.
Lemma D_97d94 : decode_any W_97d94 = Some (Load SZ8 true 17 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97d98 : bv 32 := 0x00f8c8b3.
Lemma F_97d98 : fetch_word Asan.M.loaded_segments (0x97d98 : word) = Some W_97d98.
Proof. vm_refl. Qed.
Lemma D_97d98 : decode_any W_97d98 = Some (Op ALU_XOR 17 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97d9c : bv 32 := 0x411682b3.
Lemma F_97d9c : fetch_word Asan.M.loaded_segments (0x97d9c : word) = Some W_97d9c.
Proof. vm_refl. Qed.
Lemma D_97d9c : decode_any W_97d9c = Some (Op ALU_SUB 5 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97da0 : bv 32 := 0x0112e8b3.
Lemma F_97da0 : fetch_word Asan.M.loaded_segments (0x97da0 : word) = Some W_97da0.
Proof. vm_refl. Qed.
Lemma D_97da0 : decode_any W_97da0 = Some (Op ALU_OR 17 5 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97da4 : bv 32 := 0x00e8f8b3.
Lemma F_97da4 : fetch_word Asan.M.loaded_segments (0x97da4 : word) = Some W_97da4.
Proof. vm_refl. Qed.
Lemma D_97da4 : decode_any W_97da4 = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97da8 : bv 32 := 0x02e89a63.
Lemma F_97da8 : fetch_word Asan.M.loaded_segments (0x97da8 : word) = Some W_97da8.
Proof. vm_refl. Qed.
Lemma D_97da8 : decode_any W_97da8 = Some (Branch BC_NE 17 14 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97dac : bv 32 := 0xff860613.
Lemma F_97dac : fetch_word Asan.M.loaded_segments (0x97dac : word) = Some W_97dac.
Proof. vm_refl. Qed.
Lemma D_97dac : decode_any W_97dac = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97db0 : bv 32 := 0x00850513.
Lemma F_97db0 : fetch_word Asan.M.loaded_segments (0x97db0 : word) = Some W_97db0.
Proof. vm_refl. Qed.
Lemma D_97db0 : decode_any W_97db0 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97db4 : bv 32 := 0xfec860e3.
Lemma F_97db4 : fetch_word Asan.M.loaded_segments (0x97db4 : word) = Some W_97db4.
Proof. vm_refl. Qed.
Lemma D_97db4 : decode_any W_97db4 = Some (Branch BC_LTU 16 12 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97db8 : bv 32 := 0x00060693.
Lemma F_97db8 : fetch_word Asan.M.loaded_segments (0x97db8 : word) = Some W_97db8.
Proof. vm_refl. Qed.
Lemma D_97db8 : decode_any W_97db8 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97dbc : bv 32 := 0x00060c63.
Lemma F_97dbc : fetch_word Asan.M.loaded_segments (0x97dbc : word) = Some W_97dbc.
Proof. vm_refl. Qed.
Lemma D_97dbc : decode_any W_97dbc = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97dc0 : bv 32 := 0x00054603.
Lemma F_97dc0 : fetch_word Asan.M.loaded_segments (0x97dc0 : word) = Some W_97dc0.
Proof. vm_refl. Qed.
Lemma D_97dc0 : decode_any W_97dc0 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97dc4 : bv 32 := 0x00b60a63.
Lemma F_97dc4 : fetch_word Asan.M.loaded_segments (0x97dc4 : word) = Some W_97dc4.
Proof. vm_refl. Qed.
Lemma D_97dc4 : decode_any W_97dc4 = Some (Branch BC_EQ 12 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97dc8 : bv 32 := 0xfff68693.
Lemma F_97dc8 : fetch_word Asan.M.loaded_segments (0x97dc8 : word) = Some W_97dc8.
Proof. vm_refl. Qed.
Lemma D_97dc8 : decode_any W_97dc8 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97dcc : bv 32 := 0x00150513.
Lemma F_97dcc : fetch_word Asan.M.loaded_segments (0x97dcc : word) = Some W_97dcc.
Proof. vm_refl. Qed.
Lemma D_97dcc : decode_any W_97dcc = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97dd0 : bv 32 := 0xfe0698e3.
Lemma F_97dd0 : fetch_word Asan.M.loaded_segments (0x97dd0 : word) = Some W_97dd0.
Proof. vm_refl. Qed.
Lemma D_97dd0 : decode_any W_97dd0 = Some (Branch BC_NE 13 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97dd4 : bv 32 := 0x00000513.
Lemma F_97dd4 : fetch_word Asan.M.loaded_segments (0x97dd4 : word) = Some W_97dd4.
Proof. vm_refl. Qed.
Lemma D_97dd4 : decode_any W_97dd4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97dd8 : bv 32 := 0x00008067.
Lemma F_97dd8 : fetch_word Asan.M.loaded_segments (0x97dd8 : word) = Some W_97dd8.
Proof. vm_refl. Qed.
Lemma D_97dd8 : decode_any W_97dd8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97ddc : bv 32 := 0x00060693.
Lemma F_97ddc : fetch_word Asan.M.loaded_segments (0x97ddc : word) = Some W_97ddc.
Proof. vm_refl. Qed.
Lemma D_97ddc : decode_any W_97ddc = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97de0 : bv 32 := 0x00054603.
Lemma F_97de0 : fetch_word Asan.M.loaded_segments (0x97de0 : word) = Some W_97de0.
Proof. vm_refl. Qed.
Lemma D_97de0 : decode_any W_97de0 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97de4 : bv 32 := 0xfeb612e3.
Lemma F_97de4 : fetch_word Asan.M.loaded_segments (0x97de4 : word) = Some W_97de4.
Proof. vm_refl. Qed.
Lemma D_97de4 : decode_any W_97de4 = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97de8 : bv 32 := 0xff1ff06f.
Lemma F_97de8 : fetch_word Asan.M.loaded_segments (0x97de8 : word) = Some W_97de8.
Proof. vm_refl. Qed.
Lemma D_97de8 : decode_any W_97de8 = Some (Jal 0 2097136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_986a8 : bv 32 := 0xfe010113.
Lemma F_986a8 : fetch_word Asan.M.loaded_segments (0x986a8 : word) = Some W_986a8.
Proof. vm_refl. Qed.
Lemma D_986a8 : decode_any W_986a8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_986ac : bv 32 := 0x00113c23.
Lemma F_986ac : fetch_word Asan.M.loaded_segments (0x986ac : word) = Some W_986ac.
Proof. vm_refl. Qed.
Lemma D_986ac : decode_any W_986ac = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_986b0 : bv 32 := 0x00813823.
Lemma F_986b0 : fetch_word Asan.M.loaded_segments (0x986b0 : word) = Some W_986b0.
Proof. vm_refl. Qed.
Lemma D_986b0 : decode_any W_986b0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_986b4 : bv 32 := 0x00913423.
Lemma F_986b4 : fetch_word Asan.M.loaded_segments (0x986b4 : word) = Some W_986b4.
Proof. vm_refl. Qed.
Lemma D_986b4 : decode_any W_986b4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_986b8 : bv 32 := 0x00058413.
Lemma F_986b8 : fetch_word Asan.M.loaded_segments (0x986b8 : word) = Some W_986b8.
Proof. vm_refl. Qed.
Lemma D_986b8 : decode_any W_986b8 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_986bc : bv 32 := 0x00050493.
Lemma F_986bc : fetch_word Asan.M.loaded_segments (0x986bc : word) = Some W_986bc.
Proof. vm_refl. Qed.
Lemma D_986bc : decode_any W_986bc = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_986c0 : bv 32 := 0x00000593.
Lemma F_986c0 : fetch_word Asan.M.loaded_segments (0x986c0 : word) = Some W_986c0.
Proof. vm_refl. Qed.
Lemma D_986c0 : decode_any W_986c0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_986c4 : bv 32 := 0x00040613.
Lemma F_986c4 : fetch_word Asan.M.loaded_segments (0x986c4 : word) = Some W_986c4.
Proof. vm_refl. Qed.
Lemma D_986c4 : decode_any W_986c4 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_986c8 : bv 32 := 0xb74a90ef.
Lemma F_986c8 : fetch_word Asan.M.loaded_segments (0x986c8 : word) = Some W_986c8.
Proof. vm_refl. Qed.
Lemma D_986c8 : decode_any W_986c8 = Some (Jal 1 1741684, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_986cc : bv 32 := 0x00050463.
Lemma F_986cc : fetch_word Asan.M.loaded_segments (0x986cc : word) = Some W_986cc.
Proof. vm_refl. Qed.
Lemma D_986cc : decode_any W_986cc = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_986d0 : bv 32 := 0x40950433.
Lemma F_986d0 : fetch_word Asan.M.loaded_segments (0x986d0 : word) = Some W_986d0.
Proof. vm_refl. Qed.
Lemma D_986d0 : decode_any W_986d0 = Some (Op ALU_SUB 8 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_986d4 : bv 32 := 0x00040513.
Lemma F_986d4 : fetch_word Asan.M.loaded_segments (0x986d4 : word) = Some W_986d4.
Proof. vm_refl. Qed.
Lemma D_986d4 : decode_any W_986d4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_986d8 : bv 32 := 0x01813083.
Lemma F_986d8 : fetch_word Asan.M.loaded_segments (0x986d8 : word) = Some W_986d8.
Proof. vm_refl. Qed.
Lemma D_986d8 : decode_any W_986d8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_986dc : bv 32 := 0x01013403.
Lemma F_986dc : fetch_word Asan.M.loaded_segments (0x986dc : word) = Some W_986dc.
Proof. vm_refl. Qed.
Lemma D_986dc : decode_any W_986dc = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_986e0 : bv 32 := 0x00813483.
Lemma F_986e0 : fetch_word Asan.M.loaded_segments (0x986e0 : word) = Some W_986e0.
Proof. vm_refl. Qed.
Lemma D_986e0 : decode_any W_986e0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_986e4 : bv 32 := 0x02010113.
Lemma F_986e4 : fetch_word Asan.M.loaded_segments (0x986e4 : word) = Some W_986e4.
Proof. vm_refl. Qed.
Lemma D_986e4 : decode_any W_986e4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_986e8 : bv 32 := 0x00008067.
Lemma F_986e8 : fetch_word Asan.M.loaded_segments (0x986e8 : word) = Some W_986e8.
Proof. vm_refl. Qed.
Lemma D_986e8 : decode_any W_986e8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

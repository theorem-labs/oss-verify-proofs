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

Definition W_5f960 : bv 32 := 0xfe010113.
Lemma F_5f960 : fetch_word Asan.M.loaded_segments (0x5f960 : word) = Some W_5f960.
Proof. vm_refl. Qed.
Lemma D_5f960 : decode_any W_5f960 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f964 : bv 32 := 0x00113c23.
Lemma F_5f964 : fetch_word Asan.M.loaded_segments (0x5f964 : word) = Some W_5f964.
Proof. vm_refl. Qed.
Lemma D_5f964 : decode_any W_5f964 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f968 : bv 32 := 0x00813823.
Lemma F_5f968 : fetch_word Asan.M.loaded_segments (0x5f968 : word) = Some W_5f968.
Proof. vm_refl. Qed.
Lemma D_5f968 : decode_any W_5f968 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f96c : bv 32 := 0x00913423.
Lemma F_5f96c : fetch_word Asan.M.loaded_segments (0x5f96c : word) = Some W_5f96c.
Proof. vm_refl. Qed.
Lemma D_5f96c : decode_any W_5f96c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f970 : bv 32 := 0x01213023.
Lemma F_5f970 : fetch_word Asan.M.loaded_segments (0x5f970 : word) = Some W_5f970.
Proof. vm_refl. Qed.
Lemma D_5f970 : decode_any W_5f970 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f974 : bv 32 := 0x00058413.
Lemma F_5f974 : fetch_word Asan.M.loaded_segments (0x5f974 : word) = Some W_5f974.
Proof. vm_refl. Qed.
Lemma D_5f974 : decode_any W_5f974 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f978 : bv 32 := 0x00050493.
Lemma F_5f978 : fetch_word Asan.M.loaded_segments (0x5f978 : word) = Some W_5f978.
Proof. vm_refl. Qed.
Lemma D_5f978 : decode_any W_5f978 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f97c : bv 32 := 0x030000ef.
Lemma F_5f97c : fetch_word Asan.M.loaded_segments (0x5f97c : word) = Some W_5f97c.
Proof. vm_refl. Qed.
Lemma D_5f97c : decode_any W_5f97c = Some (Jal 1 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f980 : bv 32 := 0x00050913.
Lemma F_5f980 : fetch_word Asan.M.loaded_segments (0x5f980 : word) = Some W_5f980.
Proof. vm_refl. Qed.
Lemma D_5f980 : decode_any W_5f980 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f984 : bv 32 := 0x00940533.
Lemma F_5f984 : fetch_word Asan.M.loaded_segments (0x5f984 : word) = Some W_5f984.
Proof. vm_refl. Qed.
Lemma D_5f984 : decode_any W_5f984 = Some (Op ALU_ADD 10 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f988 : bv 32 := 0x024000ef.
Lemma F_5f988 : fetch_word Asan.M.loaded_segments (0x5f988 : word) = Some W_5f988.
Proof. vm_refl. Qed.
Lemma D_5f988 : decode_any W_5f988 = Some (Jal 1 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f98c : bv 32 := 0x00050593.
Lemma F_5f98c : fetch_word Asan.M.loaded_segments (0x5f98c : word) = Some W_5f98c.
Proof. vm_refl. Qed.
Lemma D_5f98c : decode_any W_5f98c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f990 : bv 32 := 0x00090513.
Lemma F_5f990 : fetch_word Asan.M.loaded_segments (0x5f990 : word) = Some W_5f990.
Proof. vm_refl. Qed.
Lemma D_5f990 : decode_any W_5f990 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f994 : bv 32 := 0x01813083.
Lemma F_5f994 : fetch_word Asan.M.loaded_segments (0x5f994 : word) = Some W_5f994.
Proof. vm_refl. Qed.
Lemma D_5f994 : decode_any W_5f994 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f998 : bv 32 := 0x01013403.
Lemma F_5f998 : fetch_word Asan.M.loaded_segments (0x5f998 : word) = Some W_5f998.
Proof. vm_refl. Qed.
Lemma D_5f998 : decode_any W_5f998 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f99c : bv 32 := 0x00813483.
Lemma F_5f99c : fetch_word Asan.M.loaded_segments (0x5f99c : word) = Some W_5f99c.
Proof. vm_refl. Qed.
Lemma D_5f99c : decode_any W_5f99c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9a0 : bv 32 := 0x00013903.
Lemma F_5f9a0 : fetch_word Asan.M.loaded_segments (0x5f9a0 : word) = Some W_5f9a0.
Proof. vm_refl. Qed.
Lemma D_5f9a0 : decode_any W_5f9a0 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9a4 : bv 32 := 0x02010113.
Lemma F_5f9a4 : fetch_word Asan.M.loaded_segments (0x5f9a4 : word) = Some W_5f9a4.
Proof. vm_refl. Qed.
Lemma D_5f9a4 : decode_any W_5f9a4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9a8 : bv 32 := 0x5b81b06f.
Lemma F_5f9a8 : fetch_word Asan.M.loaded_segments (0x5f9a8 : word) = Some W_5f9a8.
Proof. vm_refl. Qed.
Lemma D_5f9a8 : decode_any W_5f9a8 = Some (Jal 0 112056, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9ac : bv 32 := 0x00076597.
Lemma F_5f9ac : fetch_word Asan.M.loaded_segments (0x5f9ac : word) = Some W_5f9ac.
Proof. vm_refl. Qed.
Lemma D_5f9ac : decode_any W_5f9ac = Some (Auipc 11 118, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9b0 : bv 32 := 0xf0c5b583.
Lemma F_5f9b0 : fetch_word Asan.M.loaded_segments (0x5f9b0 : word) = Some W_5f9b0.
Proof. vm_refl. Qed.
Lemma D_5f9b0 : decode_any W_5f9b0 = Some (Load SZ8 true 11 11 3852, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9b4 : bv 32 := 0x0005b583.
Lemma F_5f9b4 : fetch_word Asan.M.loaded_segments (0x5f9b4 : word) = Some W_5f9b4.
Proof. vm_refl. Qed.
Lemma D_5f9b4 : decode_any W_5f9b4 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9b8 : bv 32 := 0xfff58613.
Lemma F_5f9b8 : fetch_word Asan.M.loaded_segments (0x5f9b8 : word) = Some W_5f9b8.
Proof. vm_refl. Qed.
Lemma D_5f9b8 : decode_any W_5f9b8 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9bc : bv 32 := 0x00c5b6b3.
Lemma F_5f9bc : fetch_word Asan.M.loaded_segments (0x5f9bc : word) = Some W_5f9bc.
Proof. vm_refl. Qed.
Lemma D_5f9bc : decode_any W_5f9bc = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9c0 : bv 32 := 0xfff68693.
Lemma F_5f9c0 : fetch_word Asan.M.loaded_segments (0x5f9c0 : word) = Some W_5f9c0.
Proof. vm_refl. Qed.
Lemma D_5f9c0 : decode_any W_5f9c0 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9c4 : bv 32 := 0x00c6f6b3.
Lemma F_5f9c4 : fetch_word Asan.M.loaded_segments (0x5f9c4 : word) = Some W_5f9c4.
Proof. vm_refl. Qed.
Lemma D_5f9c4 : decode_any W_5f9c4 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9c8 : bv 32 := 0x04a6f263.
Lemma F_5f9c8 : fetch_word Asan.M.loaded_segments (0x5f9c8 : word) = Some W_5f9c8.
Proof. vm_refl. Qed.
Lemma D_5f9c8 : decode_any W_5f9c8 = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9cc : bv 32 := 0x00076697.
Lemma F_5f9cc : fetch_word Asan.M.loaded_segments (0x5f9cc : word) = Some W_5f9cc.
Proof. vm_refl. Qed.
Lemma D_5f9cc : decode_any W_5f9cc = Some (Auipc 13 118, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9d0 : bv 32 := 0xef46b683.
Lemma F_5f9d0 : fetch_word Asan.M.loaded_segments (0x5f9d0 : word) = Some W_5f9d0.
Proof. vm_refl. Qed.
Lemma D_5f9d0 : decode_any W_5f9d0 = Some (Load SZ8 true 13 13 3828, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9d4 : bv 32 := 0x00076717.
Lemma F_5f9d4 : fetch_word Asan.M.loaded_segments (0x5f9d4 : word) = Some W_5f9d4.
Proof. vm_refl. Qed.
Lemma D_5f9d4 : decode_any W_5f9d4 = Some (Auipc 14 118, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9d8 : bv 32 := 0xef473703.
Lemma F_5f9d8 : fetch_word Asan.M.loaded_segments (0x5f9d8 : word) = Some W_5f9d8.
Proof. vm_refl. Qed.
Lemma D_5f9d8 : decode_any W_5f9d8 = Some (Load SZ8 true 14 14 3828, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9dc : bv 32 := 0x0006b803.
Lemma F_5f9dc : fetch_word Asan.M.loaded_segments (0x5f9dc : word) = Some W_5f9dc.
Proof. vm_refl. Qed.
Lemma D_5f9dc : decode_any W_5f9dc = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9e0 : bv 32 := 0x00073683.
Lemma F_5f9e0 : fetch_word Asan.M.loaded_segments (0x5f9e0 : word) = Some W_5f9e0.
Proof. vm_refl. Qed.
Lemma D_5f9e0 : decode_any W_5f9e0 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9e4 : bv 32 := 0xfff80793.
Lemma F_5f9e4 : fetch_word Asan.M.loaded_segments (0x5f9e4 : word) = Some W_5f9e4.
Proof. vm_refl. Qed.
Lemma D_5f9e4 : decode_any W_5f9e4 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9e8 : bv 32 := 0x00a7f463.
Lemma F_5f9e8 : fetch_word Asan.M.loaded_segments (0x5f9e8 : word) = Some W_5f9e8.
Proof. vm_refl. Qed.
Lemma D_5f9e8 : decode_any W_5f9e8 = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9ec : bv 32 := 0x02a6f063.
Lemma F_5f9ec : fetch_word Asan.M.loaded_segments (0x5f9ec : word) = Some W_5f9ec.
Proof. vm_refl. Qed.
Lemma D_5f9ec : decode_any W_5f9ec = Some (Branch BC_GEU 13 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9f0 : bv 32 := 0x00076717.
Lemma F_5f9f0 : fetch_word Asan.M.loaded_segments (0x5f9f0 : word) = Some W_5f9f0.
Proof. vm_refl. Qed.
Lemma D_5f9f0 : decode_any W_5f9f0 = Some (Auipc 14 118, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9f4 : bv 32 := 0xee073703.
Lemma F_5f9f4 : fetch_word Asan.M.loaded_segments (0x5f9f4 : word) = Some W_5f9f4.
Proof. vm_refl. Qed.
Lemma D_5f9f4 : decode_any W_5f9f4 = Some (Load SZ8 true 14 14 3808, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9f8 : bv 32 := 0x00073283.
Lemma F_5f9f8 : fetch_word Asan.M.loaded_segments (0x5f9f8 : word) = Some W_5f9f8.
Proof. vm_refl. Qed.
Lemma D_5f9f8 : decode_any W_5f9f8 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f9fc : bv 32 := 0x0032d713.
Lemma F_5f9fc : fetch_word Asan.M.loaded_segments (0x5f9fc : word) = Some W_5f9fc.
Proof. vm_refl. Qed.
Lemma D_5f9fc : decode_any W_5f9fc = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa00 : bv 32 := 0x00b708b3.
Lemma F_5fa00 : fetch_word Asan.M.loaded_segments (0x5fa00 : word) = Some W_5fa00.
Proof. vm_refl. Qed.
Lemma D_5fa00 : decode_any W_5fa00 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa04 : bv 32 := 0x00a2ea63.
Lemma F_5fa04 : fetch_word Asan.M.loaded_segments (0x5fa04 : word) = Some W_5fa04.
Proof. vm_refl. Qed.
Lemma D_5fa04 : decode_any W_5fa04 = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa08 : bv 32 := 0x00a8f863.
Lemma F_5fa08 : fetch_word Asan.M.loaded_segments (0x5fa08 : word) = Some W_5fa08.
Proof. vm_refl. Qed.
Lemma D_5fa08 : decode_any W_5fa08 = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa0c : bv 32 := 0x00355513.
Lemma F_5fa0c : fetch_word Asan.M.loaded_segments (0x5fa0c : word) = Some W_5fa0c.
Proof. vm_refl. Qed.
Lemma D_5fa0c : decode_any W_5fa0c = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa10 : bv 32 := 0x00a58533.
Lemma F_5fa10 : fetch_word Asan.M.loaded_segments (0x5fa10 : word) = Some W_5fa10.
Proof. vm_refl. Qed.
Lemma D_5fa10 : decode_any W_5fa10 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa14 : bv 32 := 0x00008067.
Lemma F_5fa14 : fetch_word Asan.M.loaded_segments (0x5fa14 : word) = Some W_5fa14.
Proof. vm_refl. Qed.
Lemma D_5fa14 : decode_any W_5fa14 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa18 : bv 32 := 0x00076297.
Lemma F_5fa18 : fetch_word Asan.M.loaded_segments (0x5fa18 : word) = Some W_5fa18.
Proof. vm_refl. Qed.
Lemma D_5fa18 : decode_any W_5fa18 = Some (Auipc 5 118, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa1c : bv 32 := 0xe982b283.
Lemma F_5fa1c : fetch_word Asan.M.loaded_segments (0x5fa1c : word) = Some W_5fa1c.
Proof. vm_refl. Qed.
Lemma D_5fa1c : decode_any W_5fa1c = Some (Load SZ8 true 5 5 3736, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa20 : bv 32 := 0x04e2c283.
Lemma F_5fa20 : fetch_word Asan.M.loaded_segments (0x5fa20 : word) = Some W_5fa20.
Proof. vm_refl. Qed.
Lemma D_5fa20 : decode_any W_5fa20 = Some (Load SZ1 false 5 5 78, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa24 : bv 32 := 0x08029e63.
Lemma F_5fa24 : fetch_word Asan.M.loaded_segments (0x5fa24 : word) = Some W_5fa24.
Proof. vm_refl. Qed.
Lemma D_5fa24 : decode_any W_5fa24 = Some (Branch BC_NE 5 0 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa28 : bv 32 := 0x04080063.
Lemma F_5fa28 : fetch_word Asan.M.loaded_segments (0x5fa28 : word) = Some W_5fa28.
Proof. vm_refl. Qed.
Lemma D_5fa28 : decode_any W_5fa28 = Some (Branch BC_EQ 16 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa2c : bv 32 := 0x00385813.
Lemma F_5fa2c : fetch_word Asan.M.loaded_segments (0x5fa2c : word) = Some W_5fa2c.
Proof. vm_refl. Qed.
Lemma D_5fa2c : decode_any W_5fa2c = Some (ShiftImm ALU_SRL 16 16 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa30 : bv 32 := 0x00c80833.
Lemma F_5fa30 : fetch_word Asan.M.loaded_segments (0x5fa30 : word) = Some W_5fa30.
Proof. vm_refl. Qed.
Lemma D_5fa30 : decode_any W_5fa30 = Some (Op ALU_ADD 16 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa34 : bv 32 := 0x06a87063.
Lemma F_5fa34 : fetch_word Asan.M.loaded_segments (0x5fa34 : word) = Some W_5fa34.
Proof. vm_refl. Qed.
Lemma D_5fa34 : decode_any W_5fa34 = Some (Branch BC_GEU 16 10 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa38 : bv 32 := 0x00158813.
Lemma F_5fa38 : fetch_word Asan.M.loaded_segments (0x5fa38 : word) = Some W_5fa38.
Proof. vm_refl. Qed.
Lemma D_5fa38 : decode_any W_5fa38 = Some (OpImm ALU_ADD 16 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa3c : bv 32 := 0x00a7e863.
Lemma F_5fa3c : fetch_word Asan.M.loaded_segments (0x5fa3c : word) = Some W_5fa3c.
Proof. vm_refl. Qed.
Lemma D_5fa3c : decode_any W_5fa3c = Some (Branch BC_LTU 15 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa40 : bv 32 := 0x0036d793.
Lemma F_5fa40 : fetch_word Asan.M.loaded_segments (0x5fa40 : word) = Some W_5fa40.
Proof. vm_refl. Qed.
Lemma D_5fa40 : decode_any W_5fa40 = Some (ShiftImm ALU_SRL 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa44 : bv 32 := 0x010787b3.
Lemma F_5fa44 : fetch_word Asan.M.loaded_segments (0x5fa44 : word) = Some W_5fa44.
Proof. vm_refl. Qed.
Lemma D_5fa44 : decode_any W_5fa44 = Some (Op ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa48 : bv 32 := 0xfcf572e3.
Lemma F_5fa48 : fetch_word Asan.M.loaded_segments (0x5fa48 : word) = Some W_5fa48.
Proof. vm_refl. Qed.
Lemma D_5fa48 : decode_any W_5fa48 = Some (Branch BC_GEU 10 15 8132, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa4c : bv 32 := 0x00168693.
Lemma F_5fa4c : fetch_word Asan.M.loaded_segments (0x5fa4c : word) = Some W_5fa4c.
Proof. vm_refl. Qed.
Lemma D_5fa4c : decode_any W_5fa4c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa50 : bv 32 := 0x06d56863.
Lemma F_5fa50 : fetch_word Asan.M.loaded_segments (0x5fa50 : word) = Some W_5fa50.
Proof. vm_refl. Qed.
Lemma D_5fa50 : decode_any W_5fa50 = Some (Branch BC_LTU 10 13 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa54 : bv 32 := 0x01070733.
Lemma F_5fa54 : fetch_word Asan.M.loaded_segments (0x5fa54 : word) = Some W_5fa54.
Proof. vm_refl. Qed.
Lemma D_5fa54 : decode_any W_5fa54 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa58 : bv 32 := 0x00375713.
Lemma F_5fa58 : fetch_word Asan.M.loaded_segments (0x5fa58 : word) = Some W_5fa58.
Proof. vm_refl. Qed.
Lemma D_5fa58 : decode_any W_5fa58 = Some (ShiftImm ALU_SRL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa5c : bv 32 := 0x00c70633.
Lemma F_5fa5c : fetch_word Asan.M.loaded_segments (0x5fa5c : word) = Some W_5fa5c.
Proof. vm_refl. Qed.
Lemma D_5fa5c : decode_any W_5fa5c = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa60 : bv 32 := 0xfaa676e3.
Lemma F_5fa60 : fetch_word Asan.M.loaded_segments (0x5fa60 : word) = Some W_5fa60.
Proof. vm_refl. Qed.
Lemma D_5fa60 : decode_any W_5fa60 = Some (Branch BC_GEU 12 10 8108, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa64 : bv 32 := 0x05c0006f.
Lemma F_5fa64 : fetch_word Asan.M.loaded_segments (0x5fa64 : word) = Some W_5fa64.
Proof. vm_refl. Qed.
Lemma D_5fa64 : decode_any W_5fa64 = Some (Jal 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa68 : bv 32 := 0x04058463.
Lemma F_5fa68 : fetch_word Asan.M.loaded_segments (0x5fa68 : word) = Some W_5fa68.
Proof. vm_refl. Qed.
Lemma D_5fa68 : decode_any W_5fa68 = Some (Branch BC_EQ 11 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa6c : bv 32 := 0x00365693.
Lemma F_5fa6c : fetch_word Asan.M.loaded_segments (0x5fa6c : word) = Some W_5fa6c.
Proof. vm_refl. Qed.
Lemma D_5fa6c : decode_any W_5fa6c = Some (ShiftImm ALU_SRL 13 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa70 : bv 32 := 0x00b686b3.
Lemma F_5fa70 : fetch_word Asan.M.loaded_segments (0x5fa70 : word) = Some W_5fa70.
Proof. vm_refl. Qed.
Lemma D_5fa70 : decode_any W_5fa70 = Some (Op ALU_ADD 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa74 : bv 32 := 0x00068663.
Lemma F_5fa74 : fetch_word Asan.M.loaded_segments (0x5fa74 : word) = Some W_5fa74.
Proof. vm_refl. Qed.
Lemma D_5fa74 : decode_any W_5fa74 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa78 : bv 32 := 0x00168693.
Lemma F_5fa78 : fetch_word Asan.M.loaded_segments (0x5fa78 : word) = Some W_5fa78.
Proof. vm_refl. Qed.
Lemma D_5fa78 : decode_any W_5fa78 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa7c : bv 32 := 0x04d56263.
Lemma F_5fa7c : fetch_word Asan.M.loaded_segments (0x5fa7c : word) = Some W_5fa7c.
Proof. vm_refl. Qed.
Lemma D_5fa7c : decode_any W_5fa7c = Some (Branch BC_LTU 10 13 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa80 : bv 32 := 0x00188893.
Lemma F_5fa80 : fetch_word Asan.M.loaded_segments (0x5fa80 : word) = Some W_5fa80.
Proof. vm_refl. Qed.
Lemma D_5fa80 : decode_any W_5fa80 = Some (OpImm ALU_ADD 17 17 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa84 : bv 32 := 0x0038d693.
Lemma F_5fa84 : fetch_word Asan.M.loaded_segments (0x5fa84 : word) = Some W_5fa84.
Proof. vm_refl. Qed.
Lemma D_5fa84 : decode_any W_5fa84 = Some (ShiftImm ALU_SRL 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa88 : bv 32 := 0x00c68633.
Lemma F_5fa88 : fetch_word Asan.M.loaded_segments (0x5fa88 : word) = Some W_5fa88.
Proof. vm_refl. Qed.
Lemma D_5fa88 : decode_any W_5fa88 = Some (Op ALU_ADD 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa8c : bv 32 := 0xf8a670e3.
Lemma F_5fa8c : fetch_word Asan.M.loaded_segments (0x5fa8c : word) = Some W_5fa8c.
Proof. vm_refl. Qed.
Lemma D_5fa8c : decode_any W_5fa8c = Some (Branch BC_GEU 12 10 8064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa90 : bv 32 := 0x0300006f.
Lemma F_5fa90 : fetch_word Asan.M.loaded_segments (0x5fa90 : word) = Some W_5fa90.
Proof. vm_refl. Qed.
Lemma D_5fa90 : decode_any W_5fa90 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa94 : bv 32 := 0xf6058ce3.
Lemma F_5fa94 : fetch_word Asan.M.loaded_segments (0x5fa94 : word) = Some W_5fa94.
Proof. vm_refl. Qed.
Lemma D_5fa94 : decode_any W_5fa94 = Some (Branch BC_EQ 11 0 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa98 : bv 32 := 0x00365613.
Lemma F_5fa98 : fetch_word Asan.M.loaded_segments (0x5fa98 : word) = Some W_5fa98.
Proof. vm_refl. Qed.
Lemma D_5fa98 : decode_any W_5fa98 = Some (ShiftImm ALU_SRL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fa9c : bv 32 := 0x00b60633.
Lemma F_5fa9c : fetch_word Asan.M.loaded_segments (0x5fa9c : word) = Some W_5fa9c.
Proof. vm_refl. Qed.
Lemma D_5fa9c : decode_any W_5fa9c = Some (Op ALU_ADD 12 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5faa0 : bv 32 := 0xf60606e3.
Lemma F_5faa0 : fetch_word Asan.M.loaded_segments (0x5faa0 : word) = Some W_5faa0.
Proof. vm_refl. Qed.
Lemma D_5faa0 : decode_any W_5faa0 = Some (Branch BC_EQ 12 0 8044, 4%Z).
Proof. vm_refl. Qed.

Definition W_5faa4 : bv 32 := 0x00160613.
Lemma F_5faa4 : fetch_word Asan.M.loaded_segments (0x5faa4 : word) = Some W_5faa4.
Proof. vm_refl. Qed.
Lemma D_5faa4 : decode_any W_5faa4 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5faa8 : bv 32 := 0xf6c572e3.
Lemma F_5faa8 : fetch_word Asan.M.loaded_segments (0x5faa8 : word) = Some W_5faa8.
Proof. vm_refl. Qed.
Lemma D_5faa8 : decode_any W_5faa8 = Some (Branch BC_GEU 10 12 8036, 4%Z).
Proof. vm_refl. Qed.

Definition W_5faac : bv 32 := 0x0140006f.
Lemma F_5faac : fetch_word Asan.M.loaded_segments (0x5faac : word) = Some W_5faac.
Proof. vm_refl. Qed.
Lemma D_5faac : decode_any W_5faac = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fab0 : bv 32 := 0x00170713.
Lemma F_5fab0 : fetch_word Asan.M.loaded_segments (0x5fab0 : word) = Some W_5fab0.
Proof. vm_refl. Qed.
Lemma D_5fab0 : decode_any W_5fab0 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fab4 : bv 32 := 0x00375713.
Lemma F_5fab4 : fetch_word Asan.M.loaded_segments (0x5fab4 : word) = Some W_5fab4.
Proof. vm_refl. Qed.
Lemma D_5fab4 : decode_any W_5fab4 = Some (ShiftImm ALU_SRL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fab8 : bv 32 := 0xfff70713.
Lemma F_5fab8 : fetch_word Asan.M.loaded_segments (0x5fab8 : word) = Some W_5fab8.
Proof. vm_refl. Qed.
Lemma D_5fab8 : decode_any W_5fab8 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fabc : bv 32 := 0xf4a778e3.
Lemma F_5fabc : fetch_word Asan.M.loaded_segments (0x5fabc : word) = Some W_5fabc.
Proof. vm_refl. Qed.
Lemma D_5fabc : decode_any W_5fabc = Some (Branch BC_GEU 14 10 8016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fac0 : bv 32 := 0xff010113.
Lemma F_5fac0 : fetch_word Asan.M.loaded_segments (0x5fac0 : word) = Some W_5fac0.
Proof. vm_refl. Qed.
Lemma D_5fac0 : decode_any W_5fac0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fac4 : bv 32 := 0x00113423.
Lemma F_5fac4 : fetch_word Asan.M.loaded_segments (0x5fac4 : word) = Some W_5fac4.
Proof. vm_refl. Qed.
Lemma D_5fac4 : decode_any W_5fac4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fac8 : bv 32 := 0xfffc2517.
Lemma F_5fac8 : fetch_word Asan.M.loaded_segments (0x5fac8 : word) = Some W_5fac8.
Proof. vm_refl. Qed.
Lemma D_5fac8 : decode_any W_5fac8 = Some (Auipc 10 1048514, 4%Z).
Proof. vm_refl. Qed.

Definition W_5facc : bv 32 := 0xfffb8597.
Lemma F_5facc : fetch_word Asan.M.loaded_segments (0x5facc : word) = Some W_5facc.
Proof. vm_refl. Qed.
Lemma D_5facc : decode_any W_5facc = Some (Auipc 11 1048504, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fad0 : bv 32 := 0x8c550513.
Lemma F_5fad0 : fetch_word Asan.M.loaded_segments (0x5fad0 : word) = Some W_5fad0.
Proof. vm_refl. Qed.
Lemma D_5fad0 : decode_any W_5fad0 = Some (OpImm ALU_ADD 10 10 2245, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fad4 : bv 32 := 0xe1f58613.
Lemma F_5fad4 : fetch_word Asan.M.loaded_segments (0x5fad4 : word) = Some W_5fad4.
Proof. vm_refl. Qed.
Lemma D_5fad4 : decode_any W_5fad4 = Some (OpImm ALU_ADD 12 11 3615, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fad8 : bv 32 := 0x17700593.
Lemma F_5fad8 : fetch_word Asan.M.loaded_segments (0x5fad8 : word) = Some W_5fad8.
Proof. vm_refl. Qed.
Lemma D_5fad8 : decode_any W_5fad8 = Some (OpImm ALU_ADD 11 0 375, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fadc : bv 32 := 0x00000693.
Lemma F_5fadc : fetch_word Asan.M.loaded_segments (0x5fadc : word) = Some W_5fadc.
Proof. vm_refl. Qed.
Lemma D_5fadc : decode_any W_5fadc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fae0 : bv 32 := 0x00000713.
Lemma F_5fae0 : fetch_word Asan.M.loaded_segments (0x5fae0 : word) = Some W_5fae0.
Proof. vm_refl. Qed.
Lemma D_5fae0 : decode_any W_5fae0 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fae4 : bv 32 := 0x584190ef.
Lemma F_5fae4 : fetch_word Asan.M.loaded_segments (0x5fae4 : word) = Some W_5fae4.
Proof. vm_refl. Qed.
Lemma D_5fae4 : decode_any W_5fae4 = Some (Jal 1 103812, 4%Z).
Proof. vm_refl. Qed.

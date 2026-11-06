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

Definition W_5fbe0 : bv 32 := 0xfe010113.
Lemma F_5fbe0 : fetch_word AsanUbsan.M.loaded_segments (0x5fbe0 : word) = Some W_5fbe0.
Proof. vm_refl. Qed.
Lemma D_5fbe0 : decode_any W_5fbe0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fbe4 : bv 32 := 0x00113c23.
Lemma F_5fbe4 : fetch_word AsanUbsan.M.loaded_segments (0x5fbe4 : word) = Some W_5fbe4.
Proof. vm_refl. Qed.
Lemma D_5fbe4 : decode_any W_5fbe4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fbe8 : bv 32 := 0x00813823.
Lemma F_5fbe8 : fetch_word AsanUbsan.M.loaded_segments (0x5fbe8 : word) = Some W_5fbe8.
Proof. vm_refl. Qed.
Lemma D_5fbe8 : decode_any W_5fbe8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fbec : bv 32 := 0x00913423.
Lemma F_5fbec : fetch_word AsanUbsan.M.loaded_segments (0x5fbec : word) = Some W_5fbec.
Proof. vm_refl. Qed.
Lemma D_5fbec : decode_any W_5fbec = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fbf0 : bv 32 := 0x01213023.
Lemma F_5fbf0 : fetch_word AsanUbsan.M.loaded_segments (0x5fbf0 : word) = Some W_5fbf0.
Proof. vm_refl. Qed.
Lemma D_5fbf0 : decode_any W_5fbf0 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fbf4 : bv 32 := 0x00058413.
Lemma F_5fbf4 : fetch_word AsanUbsan.M.loaded_segments (0x5fbf4 : word) = Some W_5fbf4.
Proof. vm_refl. Qed.
Lemma D_5fbf4 : decode_any W_5fbf4 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fbf8 : bv 32 := 0x00050493.
Lemma F_5fbf8 : fetch_word AsanUbsan.M.loaded_segments (0x5fbf8 : word) = Some W_5fbf8.
Proof. vm_refl. Qed.
Lemma D_5fbf8 : decode_any W_5fbf8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fbfc : bv 32 := 0x030000ef.
Lemma F_5fbfc : fetch_word AsanUbsan.M.loaded_segments (0x5fbfc : word) = Some W_5fbfc.
Proof. vm_refl. Qed.
Lemma D_5fbfc : decode_any W_5fbfc = Some (Jal 1 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc00 : bv 32 := 0x00050913.
Lemma F_5fc00 : fetch_word AsanUbsan.M.loaded_segments (0x5fc00 : word) = Some W_5fc00.
Proof. vm_refl. Qed.
Lemma D_5fc00 : decode_any W_5fc00 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc04 : bv 32 := 0x00940533.
Lemma F_5fc04 : fetch_word AsanUbsan.M.loaded_segments (0x5fc04 : word) = Some W_5fc04.
Proof. vm_refl. Qed.
Lemma D_5fc04 : decode_any W_5fc04 = Some (Op ALU_ADD 10 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc08 : bv 32 := 0x024000ef.
Lemma F_5fc08 : fetch_word AsanUbsan.M.loaded_segments (0x5fc08 : word) = Some W_5fc08.
Proof. vm_refl. Qed.
Lemma D_5fc08 : decode_any W_5fc08 = Some (Jal 1 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc0c : bv 32 := 0x00050593.
Lemma F_5fc0c : fetch_word AsanUbsan.M.loaded_segments (0x5fc0c : word) = Some W_5fc0c.
Proof. vm_refl. Qed.
Lemma D_5fc0c : decode_any W_5fc0c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc10 : bv 32 := 0x00090513.
Lemma F_5fc10 : fetch_word AsanUbsan.M.loaded_segments (0x5fc10 : word) = Some W_5fc10.
Proof. vm_refl. Qed.
Lemma D_5fc10 : decode_any W_5fc10 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc14 : bv 32 := 0x01813083.
Lemma F_5fc14 : fetch_word AsanUbsan.M.loaded_segments (0x5fc14 : word) = Some W_5fc14.
Proof. vm_refl. Qed.
Lemma D_5fc14 : decode_any W_5fc14 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc18 : bv 32 := 0x01013403.
Lemma F_5fc18 : fetch_word AsanUbsan.M.loaded_segments (0x5fc18 : word) = Some W_5fc18.
Proof. vm_refl. Qed.
Lemma D_5fc18 : decode_any W_5fc18 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc1c : bv 32 := 0x00813483.
Lemma F_5fc1c : fetch_word AsanUbsan.M.loaded_segments (0x5fc1c : word) = Some W_5fc1c.
Proof. vm_refl. Qed.
Lemma D_5fc1c : decode_any W_5fc1c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc20 : bv 32 := 0x00013903.
Lemma F_5fc20 : fetch_word AsanUbsan.M.loaded_segments (0x5fc20 : word) = Some W_5fc20.
Proof. vm_refl. Qed.
Lemma D_5fc20 : decode_any W_5fc20 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc24 : bv 32 := 0x02010113.
Lemma F_5fc24 : fetch_word AsanUbsan.M.loaded_segments (0x5fc24 : word) = Some W_5fc24.
Proof. vm_refl. Qed.
Lemma D_5fc24 : decode_any W_5fc24 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc28 : bv 32 := 0x5b81b06f.
Lemma F_5fc28 : fetch_word AsanUbsan.M.loaded_segments (0x5fc28 : word) = Some W_5fc28.
Proof. vm_refl. Qed.
Lemma D_5fc28 : decode_any W_5fc28 = Some (Jal 0 112056, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc2c : bv 32 := 0x00077597.
Lemma F_5fc2c : fetch_word AsanUbsan.M.loaded_segments (0x5fc2c : word) = Some W_5fc2c.
Proof. vm_refl. Qed.
Lemma D_5fc2c : decode_any W_5fc2c = Some (Auipc 11 119, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc30 : bv 32 := 0x89c5b583.
Lemma F_5fc30 : fetch_word AsanUbsan.M.loaded_segments (0x5fc30 : word) = Some W_5fc30.
Proof. vm_refl. Qed.
Lemma D_5fc30 : decode_any W_5fc30 = Some (Load SZ8 true 11 11 2204, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc34 : bv 32 := 0x0005b583.
Lemma F_5fc34 : fetch_word AsanUbsan.M.loaded_segments (0x5fc34 : word) = Some W_5fc34.
Proof. vm_refl. Qed.
Lemma D_5fc34 : decode_any W_5fc34 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc38 : bv 32 := 0xfff58613.
Lemma F_5fc38 : fetch_word AsanUbsan.M.loaded_segments (0x5fc38 : word) = Some W_5fc38.
Proof. vm_refl. Qed.
Lemma D_5fc38 : decode_any W_5fc38 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc3c : bv 32 := 0x00c5b6b3.
Lemma F_5fc3c : fetch_word AsanUbsan.M.loaded_segments (0x5fc3c : word) = Some W_5fc3c.
Proof. vm_refl. Qed.
Lemma D_5fc3c : decode_any W_5fc3c = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc40 : bv 32 := 0xfff68693.
Lemma F_5fc40 : fetch_word AsanUbsan.M.loaded_segments (0x5fc40 : word) = Some W_5fc40.
Proof. vm_refl. Qed.
Lemma D_5fc40 : decode_any W_5fc40 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc44 : bv 32 := 0x00c6f6b3.
Lemma F_5fc44 : fetch_word AsanUbsan.M.loaded_segments (0x5fc44 : word) = Some W_5fc44.
Proof. vm_refl. Qed.
Lemma D_5fc44 : decode_any W_5fc44 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc48 : bv 32 := 0x04a6f263.
Lemma F_5fc48 : fetch_word AsanUbsan.M.loaded_segments (0x5fc48 : word) = Some W_5fc48.
Proof. vm_refl. Qed.
Lemma D_5fc48 : decode_any W_5fc48 = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc4c : bv 32 := 0x00077697.
Lemma F_5fc4c : fetch_word AsanUbsan.M.loaded_segments (0x5fc4c : word) = Some W_5fc4c.
Proof. vm_refl. Qed.
Lemma D_5fc4c : decode_any W_5fc4c = Some (Auipc 13 119, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc50 : bv 32 := 0x8846b683.
Lemma F_5fc50 : fetch_word AsanUbsan.M.loaded_segments (0x5fc50 : word) = Some W_5fc50.
Proof. vm_refl. Qed.
Lemma D_5fc50 : decode_any W_5fc50 = Some (Load SZ8 true 13 13 2180, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc54 : bv 32 := 0x00077717.
Lemma F_5fc54 : fetch_word AsanUbsan.M.loaded_segments (0x5fc54 : word) = Some W_5fc54.
Proof. vm_refl. Qed.
Lemma D_5fc54 : decode_any W_5fc54 = Some (Auipc 14 119, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc58 : bv 32 := 0x88473703.
Lemma F_5fc58 : fetch_word AsanUbsan.M.loaded_segments (0x5fc58 : word) = Some W_5fc58.
Proof. vm_refl. Qed.
Lemma D_5fc58 : decode_any W_5fc58 = Some (Load SZ8 true 14 14 2180, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc5c : bv 32 := 0x0006b803.
Lemma F_5fc5c : fetch_word AsanUbsan.M.loaded_segments (0x5fc5c : word) = Some W_5fc5c.
Proof. vm_refl. Qed.
Lemma D_5fc5c : decode_any W_5fc5c = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc60 : bv 32 := 0x00073683.
Lemma F_5fc60 : fetch_word AsanUbsan.M.loaded_segments (0x5fc60 : word) = Some W_5fc60.
Proof. vm_refl. Qed.
Lemma D_5fc60 : decode_any W_5fc60 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc64 : bv 32 := 0xfff80793.
Lemma F_5fc64 : fetch_word AsanUbsan.M.loaded_segments (0x5fc64 : word) = Some W_5fc64.
Proof. vm_refl. Qed.
Lemma D_5fc64 : decode_any W_5fc64 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc68 : bv 32 := 0x00a7f463.
Lemma F_5fc68 : fetch_word AsanUbsan.M.loaded_segments (0x5fc68 : word) = Some W_5fc68.
Proof. vm_refl. Qed.
Lemma D_5fc68 : decode_any W_5fc68 = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc6c : bv 32 := 0x02a6f063.
Lemma F_5fc6c : fetch_word AsanUbsan.M.loaded_segments (0x5fc6c : word) = Some W_5fc6c.
Proof. vm_refl. Qed.
Lemma D_5fc6c : decode_any W_5fc6c = Some (Branch BC_GEU 13 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc70 : bv 32 := 0x00077717.
Lemma F_5fc70 : fetch_word AsanUbsan.M.loaded_segments (0x5fc70 : word) = Some W_5fc70.
Proof. vm_refl. Qed.
Lemma D_5fc70 : decode_any W_5fc70 = Some (Auipc 14 119, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc74 : bv 32 := 0x87073703.
Lemma F_5fc74 : fetch_word AsanUbsan.M.loaded_segments (0x5fc74 : word) = Some W_5fc74.
Proof. vm_refl. Qed.
Lemma D_5fc74 : decode_any W_5fc74 = Some (Load SZ8 true 14 14 2160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc78 : bv 32 := 0x00073283.
Lemma F_5fc78 : fetch_word AsanUbsan.M.loaded_segments (0x5fc78 : word) = Some W_5fc78.
Proof. vm_refl. Qed.
Lemma D_5fc78 : decode_any W_5fc78 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc7c : bv 32 := 0x0032d713.
Lemma F_5fc7c : fetch_word AsanUbsan.M.loaded_segments (0x5fc7c : word) = Some W_5fc7c.
Proof. vm_refl. Qed.
Lemma D_5fc7c : decode_any W_5fc7c = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc80 : bv 32 := 0x00b708b3.
Lemma F_5fc80 : fetch_word AsanUbsan.M.loaded_segments (0x5fc80 : word) = Some W_5fc80.
Proof. vm_refl. Qed.
Lemma D_5fc80 : decode_any W_5fc80 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc84 : bv 32 := 0x00a2ea63.
Lemma F_5fc84 : fetch_word AsanUbsan.M.loaded_segments (0x5fc84 : word) = Some W_5fc84.
Proof. vm_refl. Qed.
Lemma D_5fc84 : decode_any W_5fc84 = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc88 : bv 32 := 0x00a8f863.
Lemma F_5fc88 : fetch_word AsanUbsan.M.loaded_segments (0x5fc88 : word) = Some W_5fc88.
Proof. vm_refl. Qed.
Lemma D_5fc88 : decode_any W_5fc88 = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc8c : bv 32 := 0x00355513.
Lemma F_5fc8c : fetch_word AsanUbsan.M.loaded_segments (0x5fc8c : word) = Some W_5fc8c.
Proof. vm_refl. Qed.
Lemma D_5fc8c : decode_any W_5fc8c = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc90 : bv 32 := 0x00a58533.
Lemma F_5fc90 : fetch_word AsanUbsan.M.loaded_segments (0x5fc90 : word) = Some W_5fc90.
Proof. vm_refl. Qed.
Lemma D_5fc90 : decode_any W_5fc90 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc94 : bv 32 := 0x00008067.
Lemma F_5fc94 : fetch_word AsanUbsan.M.loaded_segments (0x5fc94 : word) = Some W_5fc94.
Proof. vm_refl. Qed.
Lemma D_5fc94 : decode_any W_5fc94 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc98 : bv 32 := 0x00077297.
Lemma F_5fc98 : fetch_word AsanUbsan.M.loaded_segments (0x5fc98 : word) = Some W_5fc98.
Proof. vm_refl. Qed.
Lemma D_5fc98 : decode_any W_5fc98 = Some (Auipc 5 119, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc9c : bv 32 := 0x8282b283.
Lemma F_5fc9c : fetch_word AsanUbsan.M.loaded_segments (0x5fc9c : word) = Some W_5fc9c.
Proof. vm_refl. Qed.
Lemma D_5fc9c : decode_any W_5fc9c = Some (Load SZ8 true 5 5 2088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fca0 : bv 32 := 0x04e2c283.
Lemma F_5fca0 : fetch_word AsanUbsan.M.loaded_segments (0x5fca0 : word) = Some W_5fca0.
Proof. vm_refl. Qed.
Lemma D_5fca0 : decode_any W_5fca0 = Some (Load SZ1 false 5 5 78, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fca4 : bv 32 := 0x08029e63.
Lemma F_5fca4 : fetch_word AsanUbsan.M.loaded_segments (0x5fca4 : word) = Some W_5fca4.
Proof. vm_refl. Qed.
Lemma D_5fca4 : decode_any W_5fca4 = Some (Branch BC_NE 5 0 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fca8 : bv 32 := 0x04080063.
Lemma F_5fca8 : fetch_word AsanUbsan.M.loaded_segments (0x5fca8 : word) = Some W_5fca8.
Proof. vm_refl. Qed.
Lemma D_5fca8 : decode_any W_5fca8 = Some (Branch BC_EQ 16 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcac : bv 32 := 0x00385813.
Lemma F_5fcac : fetch_word AsanUbsan.M.loaded_segments (0x5fcac : word) = Some W_5fcac.
Proof. vm_refl. Qed.
Lemma D_5fcac : decode_any W_5fcac = Some (ShiftImm ALU_SRL 16 16 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcb0 : bv 32 := 0x00c80833.
Lemma F_5fcb0 : fetch_word AsanUbsan.M.loaded_segments (0x5fcb0 : word) = Some W_5fcb0.
Proof. vm_refl. Qed.
Lemma D_5fcb0 : decode_any W_5fcb0 = Some (Op ALU_ADD 16 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcb4 : bv 32 := 0x06a87063.
Lemma F_5fcb4 : fetch_word AsanUbsan.M.loaded_segments (0x5fcb4 : word) = Some W_5fcb4.
Proof. vm_refl. Qed.
Lemma D_5fcb4 : decode_any W_5fcb4 = Some (Branch BC_GEU 16 10 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcb8 : bv 32 := 0x00158813.
Lemma F_5fcb8 : fetch_word AsanUbsan.M.loaded_segments (0x5fcb8 : word) = Some W_5fcb8.
Proof. vm_refl. Qed.
Lemma D_5fcb8 : decode_any W_5fcb8 = Some (OpImm ALU_ADD 16 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcbc : bv 32 := 0x00a7e863.
Lemma F_5fcbc : fetch_word AsanUbsan.M.loaded_segments (0x5fcbc : word) = Some W_5fcbc.
Proof. vm_refl. Qed.
Lemma D_5fcbc : decode_any W_5fcbc = Some (Branch BC_LTU 15 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcc0 : bv 32 := 0x0036d793.
Lemma F_5fcc0 : fetch_word AsanUbsan.M.loaded_segments (0x5fcc0 : word) = Some W_5fcc0.
Proof. vm_refl. Qed.
Lemma D_5fcc0 : decode_any W_5fcc0 = Some (ShiftImm ALU_SRL 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcc4 : bv 32 := 0x010787b3.
Lemma F_5fcc4 : fetch_word AsanUbsan.M.loaded_segments (0x5fcc4 : word) = Some W_5fcc4.
Proof. vm_refl. Qed.
Lemma D_5fcc4 : decode_any W_5fcc4 = Some (Op ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcc8 : bv 32 := 0xfcf572e3.
Lemma F_5fcc8 : fetch_word AsanUbsan.M.loaded_segments (0x5fcc8 : word) = Some W_5fcc8.
Proof. vm_refl. Qed.
Lemma D_5fcc8 : decode_any W_5fcc8 = Some (Branch BC_GEU 10 15 8132, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fccc : bv 32 := 0x00168693.
Lemma F_5fccc : fetch_word AsanUbsan.M.loaded_segments (0x5fccc : word) = Some W_5fccc.
Proof. vm_refl. Qed.
Lemma D_5fccc : decode_any W_5fccc = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcd0 : bv 32 := 0x06d56863.
Lemma F_5fcd0 : fetch_word AsanUbsan.M.loaded_segments (0x5fcd0 : word) = Some W_5fcd0.
Proof. vm_refl. Qed.
Lemma D_5fcd0 : decode_any W_5fcd0 = Some (Branch BC_LTU 10 13 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcd4 : bv 32 := 0x01070733.
Lemma F_5fcd4 : fetch_word AsanUbsan.M.loaded_segments (0x5fcd4 : word) = Some W_5fcd4.
Proof. vm_refl. Qed.
Lemma D_5fcd4 : decode_any W_5fcd4 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcd8 : bv 32 := 0x00375713.
Lemma F_5fcd8 : fetch_word AsanUbsan.M.loaded_segments (0x5fcd8 : word) = Some W_5fcd8.
Proof. vm_refl. Qed.
Lemma D_5fcd8 : decode_any W_5fcd8 = Some (ShiftImm ALU_SRL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcdc : bv 32 := 0x00c70633.
Lemma F_5fcdc : fetch_word AsanUbsan.M.loaded_segments (0x5fcdc : word) = Some W_5fcdc.
Proof. vm_refl. Qed.
Lemma D_5fcdc : decode_any W_5fcdc = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fce0 : bv 32 := 0xfaa676e3.
Lemma F_5fce0 : fetch_word AsanUbsan.M.loaded_segments (0x5fce0 : word) = Some W_5fce0.
Proof. vm_refl. Qed.
Lemma D_5fce0 : decode_any W_5fce0 = Some (Branch BC_GEU 12 10 8108, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fce4 : bv 32 := 0x05c0006f.
Lemma F_5fce4 : fetch_word AsanUbsan.M.loaded_segments (0x5fce4 : word) = Some W_5fce4.
Proof. vm_refl. Qed.
Lemma D_5fce4 : decode_any W_5fce4 = Some (Jal 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fce8 : bv 32 := 0x04058463.
Lemma F_5fce8 : fetch_word AsanUbsan.M.loaded_segments (0x5fce8 : word) = Some W_5fce8.
Proof. vm_refl. Qed.
Lemma D_5fce8 : decode_any W_5fce8 = Some (Branch BC_EQ 11 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcec : bv 32 := 0x00365693.
Lemma F_5fcec : fetch_word AsanUbsan.M.loaded_segments (0x5fcec : word) = Some W_5fcec.
Proof. vm_refl. Qed.
Lemma D_5fcec : decode_any W_5fcec = Some (ShiftImm ALU_SRL 13 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcf0 : bv 32 := 0x00b686b3.
Lemma F_5fcf0 : fetch_word AsanUbsan.M.loaded_segments (0x5fcf0 : word) = Some W_5fcf0.
Proof. vm_refl. Qed.
Lemma D_5fcf0 : decode_any W_5fcf0 = Some (Op ALU_ADD 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcf4 : bv 32 := 0x00068663.
Lemma F_5fcf4 : fetch_word AsanUbsan.M.loaded_segments (0x5fcf4 : word) = Some W_5fcf4.
Proof. vm_refl. Qed.
Lemma D_5fcf4 : decode_any W_5fcf4 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcf8 : bv 32 := 0x00168693.
Lemma F_5fcf8 : fetch_word AsanUbsan.M.loaded_segments (0x5fcf8 : word) = Some W_5fcf8.
Proof. vm_refl. Qed.
Lemma D_5fcf8 : decode_any W_5fcf8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcfc : bv 32 := 0x04d56263.
Lemma F_5fcfc : fetch_word AsanUbsan.M.loaded_segments (0x5fcfc : word) = Some W_5fcfc.
Proof. vm_refl. Qed.
Lemma D_5fcfc : decode_any W_5fcfc = Some (Branch BC_LTU 10 13 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd00 : bv 32 := 0x00188893.
Lemma F_5fd00 : fetch_word AsanUbsan.M.loaded_segments (0x5fd00 : word) = Some W_5fd00.
Proof. vm_refl. Qed.
Lemma D_5fd00 : decode_any W_5fd00 = Some (OpImm ALU_ADD 17 17 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd04 : bv 32 := 0x0038d693.
Lemma F_5fd04 : fetch_word AsanUbsan.M.loaded_segments (0x5fd04 : word) = Some W_5fd04.
Proof. vm_refl. Qed.
Lemma D_5fd04 : decode_any W_5fd04 = Some (ShiftImm ALU_SRL 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd08 : bv 32 := 0x00c68633.
Lemma F_5fd08 : fetch_word AsanUbsan.M.loaded_segments (0x5fd08 : word) = Some W_5fd08.
Proof. vm_refl. Qed.
Lemma D_5fd08 : decode_any W_5fd08 = Some (Op ALU_ADD 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd0c : bv 32 := 0xf8a670e3.
Lemma F_5fd0c : fetch_word AsanUbsan.M.loaded_segments (0x5fd0c : word) = Some W_5fd0c.
Proof. vm_refl. Qed.
Lemma D_5fd0c : decode_any W_5fd0c = Some (Branch BC_GEU 12 10 8064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd10 : bv 32 := 0x0300006f.
Lemma F_5fd10 : fetch_word AsanUbsan.M.loaded_segments (0x5fd10 : word) = Some W_5fd10.
Proof. vm_refl. Qed.
Lemma D_5fd10 : decode_any W_5fd10 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd14 : bv 32 := 0xf6058ce3.
Lemma F_5fd14 : fetch_word AsanUbsan.M.loaded_segments (0x5fd14 : word) = Some W_5fd14.
Proof. vm_refl. Qed.
Lemma D_5fd14 : decode_any W_5fd14 = Some (Branch BC_EQ 11 0 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd18 : bv 32 := 0x00365613.
Lemma F_5fd18 : fetch_word AsanUbsan.M.loaded_segments (0x5fd18 : word) = Some W_5fd18.
Proof. vm_refl. Qed.
Lemma D_5fd18 : decode_any W_5fd18 = Some (ShiftImm ALU_SRL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd1c : bv 32 := 0x00b60633.
Lemma F_5fd1c : fetch_word AsanUbsan.M.loaded_segments (0x5fd1c : word) = Some W_5fd1c.
Proof. vm_refl. Qed.
Lemma D_5fd1c : decode_any W_5fd1c = Some (Op ALU_ADD 12 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd20 : bv 32 := 0xf60606e3.
Lemma F_5fd20 : fetch_word AsanUbsan.M.loaded_segments (0x5fd20 : word) = Some W_5fd20.
Proof. vm_refl. Qed.
Lemma D_5fd20 : decode_any W_5fd20 = Some (Branch BC_EQ 12 0 8044, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd24 : bv 32 := 0x00160613.
Lemma F_5fd24 : fetch_word AsanUbsan.M.loaded_segments (0x5fd24 : word) = Some W_5fd24.
Proof. vm_refl. Qed.
Lemma D_5fd24 : decode_any W_5fd24 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd28 : bv 32 := 0xf6c572e3.
Lemma F_5fd28 : fetch_word AsanUbsan.M.loaded_segments (0x5fd28 : word) = Some W_5fd28.
Proof. vm_refl. Qed.
Lemma D_5fd28 : decode_any W_5fd28 = Some (Branch BC_GEU 10 12 8036, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd2c : bv 32 := 0x0140006f.
Lemma F_5fd2c : fetch_word AsanUbsan.M.loaded_segments (0x5fd2c : word) = Some W_5fd2c.
Proof. vm_refl. Qed.
Lemma D_5fd2c : decode_any W_5fd2c = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd30 : bv 32 := 0x00170713.
Lemma F_5fd30 : fetch_word AsanUbsan.M.loaded_segments (0x5fd30 : word) = Some W_5fd30.
Proof. vm_refl. Qed.
Lemma D_5fd30 : decode_any W_5fd30 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd34 : bv 32 := 0x00375713.
Lemma F_5fd34 : fetch_word AsanUbsan.M.loaded_segments (0x5fd34 : word) = Some W_5fd34.
Proof. vm_refl. Qed.
Lemma D_5fd34 : decode_any W_5fd34 = Some (ShiftImm ALU_SRL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd38 : bv 32 := 0xfff70713.
Lemma F_5fd38 : fetch_word AsanUbsan.M.loaded_segments (0x5fd38 : word) = Some W_5fd38.
Proof. vm_refl. Qed.
Lemma D_5fd38 : decode_any W_5fd38 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd3c : bv 32 := 0xf4a778e3.
Lemma F_5fd3c : fetch_word AsanUbsan.M.loaded_segments (0x5fd3c : word) = Some W_5fd3c.
Proof. vm_refl. Qed.
Lemma D_5fd3c : decode_any W_5fd3c = Some (Branch BC_GEU 14 10 8016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd40 : bv 32 := 0xff010113.
Lemma F_5fd40 : fetch_word AsanUbsan.M.loaded_segments (0x5fd40 : word) = Some W_5fd40.
Proof. vm_refl. Qed.
Lemma D_5fd40 : decode_any W_5fd40 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd44 : bv 32 := 0x00113423.
Lemma F_5fd44 : fetch_word AsanUbsan.M.loaded_segments (0x5fd44 : word) = Some W_5fd44.
Proof. vm_refl. Qed.
Lemma D_5fd44 : decode_any W_5fd44 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd48 : bv 32 := 0xfffc1517.
Lemma F_5fd48 : fetch_word AsanUbsan.M.loaded_segments (0x5fd48 : word) = Some W_5fd48.
Proof. vm_refl. Qed.
Lemma D_5fd48 : decode_any W_5fd48 = Some (Auipc 10 1048513, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd4c : bv 32 := 0xfffb8597.
Lemma F_5fd4c : fetch_word AsanUbsan.M.loaded_segments (0x5fd4c : word) = Some W_5fd4c.
Proof. vm_refl. Qed.
Lemma D_5fd4c : decode_any W_5fd4c = Some (Auipc 11 1048504, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd50 : bv 32 := 0x65250513.
Lemma F_5fd50 : fetch_word AsanUbsan.M.loaded_segments (0x5fd50 : word) = Some W_5fd50.
Proof. vm_refl. Qed.
Lemma D_5fd50 : decode_any W_5fd50 = Some (OpImm ALU_ADD 10 10 1618, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd54 : bv 32 := 0xb1458613.
Lemma F_5fd54 : fetch_word AsanUbsan.M.loaded_segments (0x5fd54 : word) = Some W_5fd54.
Proof. vm_refl. Qed.
Lemma D_5fd54 : decode_any W_5fd54 = Some (OpImm ALU_ADD 12 11 2836, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd58 : bv 32 := 0x17700593.
Lemma F_5fd58 : fetch_word AsanUbsan.M.loaded_segments (0x5fd58 : word) = Some W_5fd58.
Proof. vm_refl. Qed.
Lemma D_5fd58 : decode_any W_5fd58 = Some (OpImm ALU_ADD 11 0 375, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd5c : bv 32 := 0x00000693.
Lemma F_5fd5c : fetch_word AsanUbsan.M.loaded_segments (0x5fd5c : word) = Some W_5fd5c.
Proof. vm_refl. Qed.
Lemma D_5fd5c : decode_any W_5fd5c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd60 : bv 32 := 0x00000713.
Lemma F_5fd60 : fetch_word AsanUbsan.M.loaded_segments (0x5fd60 : word) = Some W_5fd60.
Proof. vm_refl. Qed.
Lemma D_5fd60 : decode_any W_5fd60 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd64 : bv 32 := 0x584190ef.
Lemma F_5fd64 : fetch_word AsanUbsan.M.loaded_segments (0x5fd64 : word) = Some W_5fd64.
Proof. vm_refl. Qed.
Lemma D_5fd64 : decode_any W_5fd64 = Some (Jal 1 103812, 4%Z).
Proof. vm_refl. Qed.

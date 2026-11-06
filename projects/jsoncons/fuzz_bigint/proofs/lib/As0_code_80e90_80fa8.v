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

Definition W_80e90 : bv 32 := 0xfc010113.
Lemma F_80e90 : fetch_word Asan.M.loaded_segments (0x80e90 : word) = Some W_80e90.
Proof. vm_refl. Qed.
Lemma D_80e90 : decode_any W_80e90 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e94 : bv 32 := 0x02113c23.
Lemma F_80e94 : fetch_word Asan.M.loaded_segments (0x80e94 : word) = Some W_80e94.
Proof. vm_refl. Qed.
Lemma D_80e94 : decode_any W_80e94 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e98 : bv 32 := 0x02813823.
Lemma F_80e98 : fetch_word Asan.M.loaded_segments (0x80e98 : word) = Some W_80e98.
Proof. vm_refl. Qed.
Lemma D_80e98 : decode_any W_80e98 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e9c : bv 32 := 0x02913423.
Lemma F_80e9c : fetch_word Asan.M.loaded_segments (0x80e9c : word) = Some W_80e9c.
Proof. vm_refl. Qed.
Lemma D_80e9c : decode_any W_80e9c = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ea0 : bv 32 := 0x03213023.
Lemma F_80ea0 : fetch_word Asan.M.loaded_segments (0x80ea0 : word) = Some W_80ea0.
Proof. vm_refl. Qed.
Lemma D_80ea0 : decode_any W_80ea0 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ea4 : bv 32 := 0x01313c23.
Lemma F_80ea4 : fetch_word Asan.M.loaded_segments (0x80ea4 : word) = Some W_80ea4.
Proof. vm_refl. Qed.
Lemma D_80ea4 : decode_any W_80ea4 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ea8 : bv 32 := 0x01413823.
Lemma F_80ea8 : fetch_word Asan.M.loaded_segments (0x80ea8 : word) = Some W_80ea8.
Proof. vm_refl. Qed.
Lemma D_80ea8 : decode_any W_80ea8 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80eac : bv 32 := 0x01513423.
Lemma F_80eac : fetch_word Asan.M.loaded_segments (0x80eac : word) = Some W_80eac.
Proof. vm_refl. Qed.
Lemma D_80eac : decode_any W_80eac = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80eb0 : bv 32 := 0x00058413.
Lemma F_80eb0 : fetch_word Asan.M.loaded_segments (0x80eb0 : word) = Some W_80eb0.
Proof. vm_refl. Qed.
Lemma D_80eb0 : decode_any W_80eb0 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80eb4 : bv 32 := 0x0015b593.
Lemma F_80eb4 : fetch_word Asan.M.loaded_segments (0x80eb4 : word) = Some W_80eb4.
Proof. vm_refl. Qed.
Lemma D_80eb4 : decode_any W_80eb4 = Some (OpImm ALU_SLTU 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80eb8 : bv 32 := 0x7ff50293.
Lemma F_80eb8 : fetch_word Asan.M.loaded_segments (0x80eb8 : word) = Some W_80eb8.
Proof. vm_refl. Qed.
Lemma D_80eb8 : decode_any W_80eb8 = Some (OpImm ALU_ADD 5 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ebc : bv 32 := 0xfff58593.
Lemma F_80ebc : fetch_word Asan.M.loaded_segments (0x80ebc : word) = Some W_80ebc.
Proof. vm_refl. Qed.
Lemma D_80ebc : decode_any W_80ebc = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ec0 : bv 32 := 0x00d5f333.
Lemma F_80ec0 : fetch_word Asan.M.loaded_segments (0x80ec0 : word) = Some W_80ec0.
Proof. vm_refl. Qed.
Lemma D_80ec0 : decode_any W_80ec0 = Some (Op ALU_AND 6 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ec4 : bv 32 := 0x00100593.
Lemma F_80ec4 : fetch_word Asan.M.loaded_segments (0x80ec4 : word) = Some W_80ec4.
Proof. vm_refl. Qed.
Lemma D_80ec4 : decode_any W_80ec4 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ec8 : bv 32 := 0x0062b4a3.
Lemma F_80ec8 : fetch_word Asan.M.loaded_segments (0x80ec8 : word) = Some W_80ec8.
Proof. vm_refl. Qed.
Lemma D_80ec8 : decode_any W_80ec8 = Some (Store SZ8 5 6 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ecc : bv 32 := 0x00b40863.
Lemma F_80ecc : fetch_word Asan.M.loaded_segments (0x80ecc : word) = Some W_80ecc.
Proof. vm_refl. Qed.
Lemma D_80ecc : decode_any W_80ecc = Some (Branch BC_EQ 8 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ed0 : bv 32 := 0x02041c63.
Lemma F_80ed0 : fetch_word Asan.M.loaded_segments (0x80ed0 : word) = Some W_80ed0.
Proof. vm_refl. Qed.
Lemma D_80ed0 : decode_any W_80ed0 = Some (Branch BC_NE 8 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ed4 : bv 32 := 0x00052423.
Lemma F_80ed4 : fetch_word Asan.M.loaded_segments (0x80ed4 : word) = Some W_80ed4.
Proof. vm_refl. Qed.
Lemma D_80ed4 : decode_any W_80ed4 = Some (Store SZ4 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ed8 : bv 32 := 0x00c0006f.
Lemma F_80ed8 : fetch_word Asan.M.loaded_segments (0x80ed8 : word) = Some W_80ed8.
Proof. vm_refl. Qed.
Lemma D_80ed8 : decode_any W_80ed8 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80edc : bv 32 := 0x00b52423.
Lemma F_80edc : fetch_word Asan.M.loaded_segments (0x80edc : word) = Some W_80edc.
Proof. vm_refl. Qed.
Lemma D_80edc : decode_any W_80edc = Some (Store SZ4 10 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ee0 : bv 32 := 0x00c53823.
Lemma F_80ee0 : fetch_word Asan.M.loaded_segments (0x80ee0 : word) = Some W_80ee0.
Proof. vm_refl. Qed.
Lemma D_80ee0 : decode_any W_80ee0 = Some (Store SZ8 10 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ee4 : bv 32 := 0x03813083.
Lemma F_80ee4 : fetch_word Asan.M.loaded_segments (0x80ee4 : word) = Some W_80ee4.
Proof. vm_refl. Qed.
Lemma D_80ee4 : decode_any W_80ee4 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ee8 : bv 32 := 0x03013403.
Lemma F_80ee8 : fetch_word Asan.M.loaded_segments (0x80ee8 : word) = Some W_80ee8.
Proof. vm_refl. Qed.
Lemma D_80ee8 : decode_any W_80ee8 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_80eec : bv 32 := 0x02813483.
Lemma F_80eec : fetch_word Asan.M.loaded_segments (0x80eec : word) = Some W_80eec.
Proof. vm_refl. Qed.
Lemma D_80eec : decode_any W_80eec = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ef0 : bv 32 := 0x02013903.
Lemma F_80ef0 : fetch_word Asan.M.loaded_segments (0x80ef0 : word) = Some W_80ef0.
Proof. vm_refl. Qed.
Lemma D_80ef0 : decode_any W_80ef0 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ef4 : bv 32 := 0x01813983.
Lemma F_80ef4 : fetch_word Asan.M.loaded_segments (0x80ef4 : word) = Some W_80ef4.
Proof. vm_refl. Qed.
Lemma D_80ef4 : decode_any W_80ef4 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ef8 : bv 32 := 0x01013a03.
Lemma F_80ef8 : fetch_word Asan.M.loaded_segments (0x80ef8 : word) = Some W_80ef8.
Proof. vm_refl. Qed.
Lemma D_80ef8 : decode_any W_80ef8 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80efc : bv 32 := 0x00813a83.
Lemma F_80efc : fetch_word Asan.M.loaded_segments (0x80efc : word) = Some W_80efc.
Proof. vm_refl. Qed.
Lemma D_80efc : decode_any W_80efc = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f00 : bv 32 := 0x04010113.
Lemma F_80f00 : fetch_word Asan.M.loaded_segments (0x80f00 : word) = Some W_80f00.
Proof. vm_refl. Qed.
Lemma D_80f00 : decode_any W_80f00 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f04 : bv 32 := 0x00008067.
Lemma F_80f04 : fetch_word Asan.M.loaded_segments (0x80f04 : word) = Some W_80f04.
Proof. vm_refl. Qed.
Lemma D_80f04 : decode_any W_80f04 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f08 : bv 32 := 0x06089463.
Lemma F_80f08 : fetch_word Asan.M.loaded_segments (0x80f08 : word) = Some W_80f08.
Proof. vm_refl. Qed.
Lemma D_80f08 : decode_any W_80f08 = Some (Branch BC_NE 17 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f0c : bv 32 := 0x00068493.
Lemma F_80f0c : fetch_word Asan.M.loaded_segments (0x80f0c : word) = Some W_80f0c.
Proof. vm_refl. Qed.
Lemma D_80f0c : decode_any W_80f0c = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f10 : bv 32 := 0x00078913.
Lemma F_80f10 : fetch_word Asan.M.loaded_segments (0x80f10 : word) = Some W_80f10.
Proof. vm_refl. Qed.
Lemma D_80f10 : decode_any W_80f10 = Some (OpImm ALU_ADD 18 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f14 : bv 32 := 0x00080993.
Lemma F_80f14 : fetch_word Asan.M.loaded_segments (0x80f14 : word) = Some W_80f14.
Proof. vm_refl. Qed.
Lemma D_80f14 : decode_any W_80f14 = Some (OpImm ALU_ADD 19 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f18 : bv 32 := 0x00050a93.
Lemma F_80f18 : fetch_word Asan.M.loaded_segments (0x80f18 : word) = Some W_80f18.
Proof. vm_refl. Qed.
Lemma D_80f18 : decode_any W_80f18 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f1c : bv 32 := 0x00060a13.
Lemma F_80f1c : fetch_word Asan.M.loaded_segments (0x80f1c : word) = Some W_80f1c.
Proof. vm_refl. Qed.
Lemma D_80f1c : decode_any W_80f1c = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f20 : bv 32 := 0x00060593.
Lemma F_80f20 : fetch_word Asan.M.loaded_segments (0x80f20 : word) = Some W_80f20.
Proof. vm_refl. Qed.
Lemma D_80f20 : decode_any W_80f20 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f24 : bv 32 := 0x02070063.
Lemma F_80f24 : fetch_word Asan.M.loaded_segments (0x80f24 : word) = Some W_80f24.
Proof. vm_refl. Qed.
Lemma D_80f24 : decode_any W_80f24 = Some (Branch BC_EQ 14 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f28 : bv 32 := 0x00070613.
Lemma F_80f28 : fetch_word Asan.M.loaded_segments (0x80f28 : word) = Some W_80f28.
Proof. vm_refl. Qed.
Lemma D_80f28 : decode_any W_80f28 = Some (OpImm ALU_ADD 12 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f2c : bv 32 := 0x00040693.
Lemma F_80f2c : fetch_word Asan.M.loaded_segments (0x80f2c : word) = Some W_80f2c.
Proof. vm_refl. Qed.
Lemma D_80f2c : decode_any W_80f2c = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f30 : bv 32 := 0x45c060ef.
Lemma F_80f30 : fetch_word Asan.M.loaded_segments (0x80f30 : word) = Some W_80f30.
Proof. vm_refl. Qed.
Lemma D_80f30 : decode_any W_80f30 = Some (Jal 1 25692, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f34 : bv 32 := 0x008aa583.
Lemma F_80f34 : fetch_word Asan.M.loaded_segments (0x80f34 : word) = Some W_80f34.
Proof. vm_refl. Qed.
Lemma D_80f34 : decode_any W_80f34 = Some (Load SZ4 true 11 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f38 : bv 32 := 0x00200713.
Lemma F_80f38 : fetch_word Asan.M.loaded_segments (0x80f38 : word) = Some W_80f38.
Proof. vm_refl. Qed.
Lemma D_80f38 : decode_any W_80f38 = Some (OpImm ALU_ADD 14 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f3c : bv 32 := 0x00b77e63.
Lemma F_80f3c : fetch_word Asan.M.loaded_segments (0x80f3c : word) = Some W_80f3c.
Proof. vm_refl. Qed.
Lemma D_80f3c : decode_any W_80f3c = Some (Branch BC_GEU 14 11 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f40 : bv 32 := 0xfa5ff06f.
Lemma F_80f40 : fetch_word Asan.M.loaded_segments (0x80f40 : word) = Some W_80f40.
Proof. vm_refl. Qed.
Lemma D_80f40 : decode_any W_80f40 = Some (Jal 0 2097060, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f44 : bv 32 := 0x00040613.
Lemma F_80f44 : fetch_word Asan.M.loaded_segments (0x80f44 : word) = Some W_80f44.
Proof. vm_refl. Qed.
Lemma D_80f44 : decode_any W_80f44 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f48 : bv 32 := 0x2b0060ef.
Lemma F_80f48 : fetch_word Asan.M.loaded_segments (0x80f48 : word) = Some W_80f48.
Proof. vm_refl. Qed.
Lemma D_80f48 : decode_any W_80f48 = Some (Jal 1 25264, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f4c : bv 32 := 0x008aa583.
Lemma F_80f4c : fetch_word Asan.M.loaded_segments (0x80f4c : word) = Some W_80f4c.
Proof. vm_refl. Qed.
Lemma D_80f4c : decode_any W_80f4c = Some (Load SZ4 true 11 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f50 : bv 32 := 0x00200713.
Lemma F_80f50 : fetch_word Asan.M.loaded_segments (0x80f50 : word) = Some W_80f50.
Proof. vm_refl. Qed.
Lemma D_80f50 : decode_any W_80f50 = Some (OpImm ALU_ADD 14 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f54 : bv 32 := 0xf8b768e3.
Lemma F_80f54 : fetch_word Asan.M.loaded_segments (0x80f54 : word) = Some W_80f54.
Proof. vm_refl. Qed.
Lemma D_80f54 : decode_any W_80f54 = Some (Branch BC_LTU 14 11 8080, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f58 : bv 32 := 0x000a8513.
Lemma F_80f58 : fetch_word Asan.M.loaded_segments (0x80f58 : word) = Some W_80f58.
Proof. vm_refl. Qed.
Lemma D_80f58 : decode_any W_80f58 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f5c : bv 32 := 0x00098813.
Lemma F_80f5c : fetch_word Asan.M.loaded_segments (0x80f5c : word) = Some W_80f5c.
Proof. vm_refl. Qed.
Lemma D_80f5c : decode_any W_80f5c = Some (OpImm ALU_ADD 16 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f60 : bv 32 := 0x00090793.
Lemma F_80f60 : fetch_word Asan.M.loaded_segments (0x80f60 : word) = Some W_80f60.
Proof. vm_refl. Qed.
Lemma D_80f60 : decode_any W_80f60 = Some (OpImm ALU_ADD 15 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f64 : bv 32 := 0x000a0613.
Lemma F_80f64 : fetch_word Asan.M.loaded_segments (0x80f64 : word) = Some W_80f64.
Proof. vm_refl. Qed.
Lemma D_80f64 : decode_any W_80f64 = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f68 : bv 32 := 0x00048693.
Lemma F_80f68 : fetch_word Asan.M.loaded_segments (0x80f68 : word) = Some W_80f68.
Proof. vm_refl. Qed.
Lemma D_80f68 : decode_any W_80f68 = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f6c : bv 32 := 0xf685fce3.
Lemma F_80f6c : fetch_word Asan.M.loaded_segments (0x80f6c : word) = Some W_80f6c.
Proof. vm_refl. Qed.
Lemma D_80f6c : decode_any W_80f6c = Some (Branch BC_GEU 11 8 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f70 : bv 32 := 0x00060593.
Lemma F_80f70 : fetch_word Asan.M.loaded_segments (0x80f70 : word) = Some W_80f70.
Proof. vm_refl. Qed.
Lemma D_80f70 : decode_any W_80f70 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f74 : bv 32 := 0x00068613.
Lemma F_80f74 : fetch_word Asan.M.loaded_segments (0x80f74 : word) = Some W_80f74.
Proof. vm_refl. Qed.
Lemma D_80f74 : decode_any W_80f74 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f78 : bv 32 := 0x00078693.
Lemma F_80f78 : fetch_word Asan.M.loaded_segments (0x80f78 : word) = Some W_80f78.
Proof. vm_refl. Qed.
Lemma D_80f78 : decode_any W_80f78 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f7c : bv 32 := 0x00080713.
Lemma F_80f7c : fetch_word Asan.M.loaded_segments (0x80f7c : word) = Some W_80f7c.
Proof. vm_refl. Qed.
Lemma D_80f7c : decode_any W_80f7c = Some (OpImm ALU_ADD 14 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f80 : bv 32 := 0x00040793.
Lemma F_80f80 : fetch_word Asan.M.loaded_segments (0x80f80 : word) = Some W_80f80.
Proof. vm_refl. Qed.
Lemma D_80f80 : decode_any W_80f80 = Some (OpImm ALU_ADD 15 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f84 : bv 32 := 0x03813083.
Lemma F_80f84 : fetch_word Asan.M.loaded_segments (0x80f84 : word) = Some W_80f84.
Proof. vm_refl. Qed.
Lemma D_80f84 : decode_any W_80f84 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f88 : bv 32 := 0x03013403.
Lemma F_80f88 : fetch_word Asan.M.loaded_segments (0x80f88 : word) = Some W_80f88.
Proof. vm_refl. Qed.
Lemma D_80f88 : decode_any W_80f88 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f8c : bv 32 := 0x02813483.
Lemma F_80f8c : fetch_word Asan.M.loaded_segments (0x80f8c : word) = Some W_80f8c.
Proof. vm_refl. Qed.
Lemma D_80f8c : decode_any W_80f8c = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f90 : bv 32 := 0x02013903.
Lemma F_80f90 : fetch_word Asan.M.loaded_segments (0x80f90 : word) = Some W_80f90.
Proof. vm_refl. Qed.
Lemma D_80f90 : decode_any W_80f90 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f94 : bv 32 := 0x01813983.
Lemma F_80f94 : fetch_word Asan.M.loaded_segments (0x80f94 : word) = Some W_80f94.
Proof. vm_refl. Qed.
Lemma D_80f94 : decode_any W_80f94 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f98 : bv 32 := 0x01013a03.
Lemma F_80f98 : fetch_word Asan.M.loaded_segments (0x80f98 : word) = Some W_80f98.
Proof. vm_refl. Qed.
Lemma D_80f98 : decode_any W_80f98 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f9c : bv 32 := 0x00813a83.
Lemma F_80f9c : fetch_word Asan.M.loaded_segments (0x80f9c : word) = Some W_80f9c.
Proof. vm_refl. Qed.
Lemma D_80f9c : decode_any W_80f9c = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80fa0 : bv 32 := 0x04010113.
Lemma F_80fa0 : fetch_word Asan.M.loaded_segments (0x80fa0 : word) = Some W_80fa0.
Proof. vm_refl. Qed.
Lemma D_80fa0 : decode_any W_80fa0 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_80fa4 : bv 32 := 0x891ff06f.
Lemma F_80fa4 : fetch_word Asan.M.loaded_segments (0x80fa4 : word) = Some W_80fa4.
Proof. vm_refl. Qed.
Lemma D_80fa4 : decode_any W_80fa4 = Some (Jal 0 2095248, 4%Z).
Proof. vm_refl. Qed.

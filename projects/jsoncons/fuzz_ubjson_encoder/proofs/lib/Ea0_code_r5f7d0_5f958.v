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

Definition W_79e54 : bv 32 := 0xfe010113.
Lemma F_79e54 : fetch_word Asan.M.loaded_segments (0x79ea4 : word) = Some W_79e54.
Proof. vm_refl. Qed.
Lemma D_79e54 : decode_any W_79e54 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e58 : bv 32 := 0x00113c23.
Lemma F_79e58 : fetch_word Asan.M.loaded_segments (0x79ea8 : word) = Some W_79e58.
Proof. vm_refl. Qed.
Lemma D_79e58 : decode_any W_79e58 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e5c : bv 32 := 0x00813823.
Lemma F_79e5c : fetch_word Asan.M.loaded_segments (0x79eac : word) = Some W_79e5c.
Proof. vm_refl. Qed.
Lemma D_79e5c : decode_any W_79e5c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e60 : bv 32 := 0x00913423.
Lemma F_79e60 : fetch_word Asan.M.loaded_segments (0x79eb0 : word) = Some W_79e60.
Proof. vm_refl. Qed.
Lemma D_79e60 : decode_any W_79e60 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e64 : bv 32 := 0x01213023.
Lemma F_79e64 : fetch_word Asan.M.loaded_segments (0x79eb4 : word) = Some W_79e64.
Proof. vm_refl. Qed.
Lemma D_79e64 : decode_any W_79e64 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e68 : bv 32 := 0x00058413.
Lemma F_79e68 : fetch_word Asan.M.loaded_segments (0x79eb8 : word) = Some W_79e68.
Proof. vm_refl. Qed.
Lemma D_79e68 : decode_any W_79e68 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e6c : bv 32 := 0x00050493.
Lemma F_79e6c : fetch_word Asan.M.loaded_segments (0x79ebc : word) = Some W_79e6c.
Proof. vm_refl. Qed.
Lemma D_79e6c : decode_any W_79e6c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e70 : bv 32 := 0x030000ef.
Lemma F_79e70 : fetch_word Asan.M.loaded_segments (0x79ec0 : word) = Some W_79e70.
Proof. vm_refl. Qed.
Lemma D_79e70 : decode_any W_79e70 = Some (Jal 1 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e74 : bv 32 := 0x00050913.
Lemma F_79e74 : fetch_word Asan.M.loaded_segments (0x79ec4 : word) = Some W_79e74.
Proof. vm_refl. Qed.
Lemma D_79e74 : decode_any W_79e74 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e78 : bv 32 := 0x00940533.
Lemma F_79e78 : fetch_word Asan.M.loaded_segments (0x79ec8 : word) = Some W_79e78.
Proof. vm_refl. Qed.
Lemma D_79e78 : decode_any W_79e78 = Some (Op ALU_ADD 10 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e7c : bv 32 := 0x024000ef.
Lemma F_79e7c : fetch_word Asan.M.loaded_segments (0x79ecc : word) = Some W_79e7c.
Proof. vm_refl. Qed.
Lemma D_79e7c : decode_any W_79e7c = Some (Jal 1 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e80 : bv 32 := 0x00050593.
Lemma F_79e80 : fetch_word Asan.M.loaded_segments (0x79ed0 : word) = Some W_79e80.
Proof. vm_refl. Qed.
Lemma D_79e80 : decode_any W_79e80 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e84 : bv 32 := 0x00090513.
Lemma F_79e84 : fetch_word Asan.M.loaded_segments (0x79ed4 : word) = Some W_79e84.
Proof. vm_refl. Qed.
Lemma D_79e84 : decode_any W_79e84 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e88 : bv 32 := 0x01813083.
Lemma F_79e88 : fetch_word Asan.M.loaded_segments (0x79ed8 : word) = Some W_79e88.
Proof. vm_refl. Qed.
Lemma D_79e88 : decode_any W_79e88 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e8c : bv 32 := 0x01013403.
Lemma F_79e8c : fetch_word Asan.M.loaded_segments (0x79edc : word) = Some W_79e8c.
Proof. vm_refl. Qed.
Lemma D_79e8c : decode_any W_79e8c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e90 : bv 32 := 0x00813483.
Lemma F_79e90 : fetch_word Asan.M.loaded_segments (0x79ee0 : word) = Some W_79e90.
Proof. vm_refl. Qed.
Lemma D_79e90 : decode_any W_79e90 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e94 : bv 32 := 0x00013903.
Lemma F_79e94 : fetch_word Asan.M.loaded_segments (0x79ee4 : word) = Some W_79e94.
Proof. vm_refl. Qed.
Lemma D_79e94 : decode_any W_79e94 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e98 : bv 32 := 0x02010113.
Lemma F_79e98 : fetch_word Asan.M.loaded_segments (0x79ee8 : word) = Some W_79e98.
Proof. vm_refl. Qed.
Lemma D_79e98 : decode_any W_79e98 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_79e9c : bv 32 := 0x3151b06f.
Lemma F_79e9c : fetch_word Asan.M.loaded_segments (0x79eec : word) = Some W_79e9c.
Proof. vm_refl. Qed.
Lemma D_79e9c : decode_any W_79e9c = Some (Jal 0 113428, 4%Z).
Proof. vm_refl. Qed.

Definition W_79ea0 : bv 32 := 0x000bf597.
Lemma F_79ea0 : fetch_word Asan.M.loaded_segments (0x79ef0 : word) = Some W_79ea0.
Proof. vm_refl. Qed.
Lemma D_79ea0 : decode_any W_79ea0 = Some (Auipc 11 191, 4%Z).
Proof. vm_refl. Qed.

Definition W_79ea4 : bv 32 := 0x2c85b583.
Lemma F_79ea4 : fetch_word Asan.M.loaded_segments (0x79ef4 : word) = Some W_79ea4.
Proof. vm_refl. Qed.
Lemma D_79ea4 : decode_any W_79ea4 = Some (Load SZ8 true 11 11 712, 4%Z).
Proof. vm_refl. Qed.

Definition W_79ea8 : bv 32 := 0x0005b583.
Lemma F_79ea8 : fetch_word Asan.M.loaded_segments (0x79ef8 : word) = Some W_79ea8.
Proof. vm_refl. Qed.
Lemma D_79ea8 : decode_any W_79ea8 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79eac : bv 32 := 0xfff58613.
Lemma F_79eac : fetch_word Asan.M.loaded_segments (0x79efc : word) = Some W_79eac.
Proof. vm_refl. Qed.
Lemma D_79eac : decode_any W_79eac = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_79eb0 : bv 32 := 0x00c5b6b3.
Lemma F_79eb0 : fetch_word Asan.M.loaded_segments (0x79f00 : word) = Some W_79eb0.
Proof. vm_refl. Qed.
Lemma D_79eb0 : decode_any W_79eb0 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_79eb4 : bv 32 := 0xfff68693.
Lemma F_79eb4 : fetch_word Asan.M.loaded_segments (0x79f04 : word) = Some W_79eb4.
Proof. vm_refl. Qed.
Lemma D_79eb4 : decode_any W_79eb4 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_79eb8 : bv 32 := 0x00c6f6b3.
Lemma F_79eb8 : fetch_word Asan.M.loaded_segments (0x79f08 : word) = Some W_79eb8.
Proof. vm_refl. Qed.
Lemma D_79eb8 : decode_any W_79eb8 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_79ebc : bv 32 := 0x04a6f263.
Lemma F_79ebc : fetch_word Asan.M.loaded_segments (0x79f0c : word) = Some W_79ebc.
Proof. vm_refl. Qed.
Lemma D_79ebc : decode_any W_79ebc = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_79ec0 : bv 32 := 0x000bf697.
Lemma F_79ec0 : fetch_word Asan.M.loaded_segments (0x79f10 : word) = Some W_79ec0.
Proof. vm_refl. Qed.
Lemma D_79ec0 : decode_any W_79ec0 = Some (Auipc 13 191, 4%Z).
Proof. vm_refl. Qed.

Definition W_79ec4 : bv 32 := 0x2b06b683.
Lemma F_79ec4 : fetch_word Asan.M.loaded_segments (0x79f14 : word) = Some W_79ec4.
Proof. vm_refl. Qed.
Lemma D_79ec4 : decode_any W_79ec4 = Some (Load SZ8 true 13 13 688, 4%Z).
Proof. vm_refl. Qed.

Definition W_79ec8 : bv 32 := 0x000bf717.
Lemma F_79ec8 : fetch_word Asan.M.loaded_segments (0x79f18 : word) = Some W_79ec8.
Proof. vm_refl. Qed.
Lemma D_79ec8 : decode_any W_79ec8 = Some (Auipc 14 191, 4%Z).
Proof. vm_refl. Qed.

Definition W_79ecc : bv 32 := 0x2b073703.
Lemma F_79ecc : fetch_word Asan.M.loaded_segments (0x79f1c : word) = Some W_79ecc.
Proof. vm_refl. Qed.
Lemma D_79ecc : decode_any W_79ecc = Some (Load SZ8 true 14 14 688, 4%Z).
Proof. vm_refl. Qed.

Definition W_79ed0 : bv 32 := 0x0006b803.
Lemma F_79ed0 : fetch_word Asan.M.loaded_segments (0x79f20 : word) = Some W_79ed0.
Proof. vm_refl. Qed.
Lemma D_79ed0 : decode_any W_79ed0 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79ed4 : bv 32 := 0x00073683.
Lemma F_79ed4 : fetch_word Asan.M.loaded_segments (0x79f24 : word) = Some W_79ed4.
Proof. vm_refl. Qed.
Lemma D_79ed4 : decode_any W_79ed4 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79ed8 : bv 32 := 0xfff80793.
Lemma F_79ed8 : fetch_word Asan.M.loaded_segments (0x79f28 : word) = Some W_79ed8.
Proof. vm_refl. Qed.
Lemma D_79ed8 : decode_any W_79ed8 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_79edc : bv 32 := 0x00a7f463.
Lemma F_79edc : fetch_word Asan.M.loaded_segments (0x79f2c : word) = Some W_79edc.
Proof. vm_refl. Qed.
Lemma D_79edc : decode_any W_79edc = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_79ee4 : bv 32 := 0x000bf717.
Lemma F_79ee4 : fetch_word Asan.M.loaded_segments (0x79f34 : word) = Some W_79ee4.
Proof. vm_refl. Qed.
Lemma D_79ee4 : decode_any W_79ee4 = Some (Auipc 14 191, 4%Z).
Proof. vm_refl. Qed.

Definition W_79ee8 : bv 32 := 0x29c73703.
Lemma F_79ee8 : fetch_word Asan.M.loaded_segments (0x79f38 : word) = Some W_79ee8.
Proof. vm_refl. Qed.
Lemma D_79ee8 : decode_any W_79ee8 = Some (Load SZ8 true 14 14 668, 4%Z).
Proof. vm_refl. Qed.

Definition W_79eec : bv 32 := 0x00073283.
Lemma F_79eec : fetch_word Asan.M.loaded_segments (0x79f3c : word) = Some W_79eec.
Proof. vm_refl. Qed.
Lemma D_79eec : decode_any W_79eec = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_79ef0 : bv 32 := 0x0032d713.
Lemma F_79ef0 : fetch_word Asan.M.loaded_segments (0x79f40 : word) = Some W_79ef0.
Proof. vm_refl. Qed.
Lemma D_79ef0 : decode_any W_79ef0 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_79ef4 : bv 32 := 0x00b708b3.
Lemma F_79ef4 : fetch_word Asan.M.loaded_segments (0x79f44 : word) = Some W_79ef4.
Proof. vm_refl. Qed.
Lemma D_79ef4 : decode_any W_79ef4 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_79ef8 : bv 32 := 0x00a2ea63.
Lemma F_79ef8 : fetch_word Asan.M.loaded_segments (0x79f48 : word) = Some W_79ef8.
Proof. vm_refl. Qed.
Lemma D_79ef8 : decode_any W_79ef8 = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_79efc : bv 32 := 0x00a8f863.
Lemma F_79efc : fetch_word Asan.M.loaded_segments (0x79f4c : word) = Some W_79efc.
Proof. vm_refl. Qed.
Lemma D_79efc : decode_any W_79efc = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_79f00 : bv 32 := 0x00355513.
Lemma F_79f00 : fetch_word Asan.M.loaded_segments (0x79f50 : word) = Some W_79f00.
Proof. vm_refl. Qed.
Lemma D_79f00 : decode_any W_79f00 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_79f04 : bv 32 := 0x00a58533.
Lemma F_79f04 : fetch_word Asan.M.loaded_segments (0x79f54 : word) = Some W_79f04.
Proof. vm_refl. Qed.
Lemma D_79f04 : decode_any W_79f04 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_79f08 : bv 32 := 0x00008067.
Lemma F_79f08 : fetch_word Asan.M.loaded_segments (0x79f58 : word) = Some W_79f08.
Proof. vm_refl. Qed.
Lemma D_79f08 : decode_any W_79f08 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

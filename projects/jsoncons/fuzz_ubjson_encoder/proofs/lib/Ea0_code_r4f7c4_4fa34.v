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

Definition W_65ea0 : bv 32 := 0x81010113.
Lemma F_65ea0 : fetch_word Asan.M.loaded_segments (0x65ef0 : word) = Some W_65ea0.
Proof. vm_refl. Qed.
Lemma D_65ea0 : decode_any W_65ea0 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ea4 : bv 32 := 0x7e113423.
Lemma F_65ea4 : fetch_word Asan.M.loaded_segments (0x65ef4 : word) = Some W_65ea4.
Proof. vm_refl. Qed.
Lemma D_65ea4 : decode_any W_65ea4 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ea8 : bv 32 := 0x7e813023.
Lemma F_65ea8 : fetch_word Asan.M.loaded_segments (0x65ef8 : word) = Some W_65ea8.
Proof. vm_refl. Qed.
Lemma D_65ea8 : decode_any W_65ea8 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_65eac : bv 32 := 0x7c913c23.
Lemma F_65eac : fetch_word Asan.M.loaded_segments (0x65efc : word) = Some W_65eac.
Proof. vm_refl. Qed.
Lemma D_65eac : decode_any W_65eac = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_65eb0 : bv 32 := 0x7d213823.
Lemma F_65eb0 : fetch_word Asan.M.loaded_segments (0x65f00 : word) = Some W_65eb0.
Proof. vm_refl. Qed.
Lemma D_65eb0 : decode_any W_65eb0 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_65eb4 : bv 32 := 0x7d313423.
Lemma F_65eb4 : fetch_word Asan.M.loaded_segments (0x65f04 : word) = Some W_65eb4.
Proof. vm_refl. Qed.
Lemma D_65eb4 : decode_any W_65eb4 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_65eb8 : bv 32 := 0x7d413023.
Lemma F_65eb8 : fetch_word Asan.M.loaded_segments (0x65f08 : word) = Some W_65eb8.
Proof. vm_refl. Qed.
Lemma D_65eb8 : decode_any W_65eb8 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ebc : bv 32 := 0x7f010413.
Lemma F_65ebc : fetch_word Asan.M.loaded_segments (0x65f0c : word) = Some W_65ebc.
Proof. vm_refl. Qed.
Lemma D_65ebc : decode_any W_65ebc = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ec0 : bv 32 := 0xfa010113.
Lemma F_65ec0 : fetch_word Asan.M.loaded_segments (0x65f10 : word) = Some W_65ec0.
Proof. vm_refl. Qed.
Lemma D_65ec0 : decode_any W_65ec0 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ec4 : bv 32 := 0x00060913.
Lemma F_65ec4 : fetch_word Asan.M.loaded_segments (0x65f14 : word) = Some W_65ec4.
Proof. vm_refl. Qed.
Lemma D_65ec4 : decode_any W_65ec4 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ec8 : bv 32 := 0x00058493.
Lemma F_65ec8 : fetch_word Asan.M.loaded_segments (0x65f18 : word) = Some W_65ec8.
Proof. vm_refl. Qed.
Lemma D_65ec8 : decode_any W_65ec8 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ecc : bv 32 := 0x00050993.
Lemma F_65ecc : fetch_word Asan.M.loaded_segments (0x65f1c : word) = Some W_65ecc.
Proof. vm_refl. Qed.
Lemma D_65ecc : decode_any W_65ecc = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ed0 : bv 32 := 0x3491b0ef.
Lemma F_65ed0 : fetch_word Asan.M.loaded_segments (0x65f20 : word) = Some W_65ed0.
Proof. vm_refl. Qed.
Lemma D_65ed0 : decode_any W_65ed0 = Some (Jal 1 113480, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ed4 : bv 32 := 0x000d5597.
Lemma F_65ed4 : fetch_word Asan.M.loaded_segments (0x65f24 : word) = Some W_65ed4.
Proof. vm_refl. Qed.
Lemma D_65ed4 : decode_any W_65ed4 = Some (Auipc 11 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ed8 : bv 32 := 0x0ec5b683.
Lemma F_65ed8 : fetch_word Asan.M.loaded_segments (0x65f28 : word) = Some W_65ed8.
Proof. vm_refl. Qed.
Lemma D_65ed8 : decode_any W_65ed8 = Some (Load SZ8 true 13 11 236, 4%Z).
Proof. vm_refl. Qed.

Definition W_65edc : bv 32 := 0x00050a13.
Lemma F_65edc : fetch_word Asan.M.loaded_segments (0x65f2c : word) = Some W_65edc.
Proof. vm_refl. Qed.
Lemma D_65edc : decode_any W_65edc = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ee0 : bv 32 := 0x00098513.
Lemma F_65ee0 : fetch_word Asan.M.loaded_segments (0x65f30 : word) = Some W_65ee0.
Proof. vm_refl. Qed.
Lemma D_65ee0 : decode_any W_65ee0 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ee4 : bv 32 := 0x00048593.
Lemma F_65ee4 : fetch_word Asan.M.loaded_segments (0x65f34 : word) = Some W_65ee4.
Proof. vm_refl. Qed.
Lemma D_65ee4 : decode_any W_65ee4 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ee8 : bv 32 := 0x00090613.
Lemma F_65ee8 : fetch_word Asan.M.loaded_segments (0x65f38 : word) = Some W_65ee8.
Proof. vm_refl. Qed.
Lemma D_65ee8 : decode_any W_65ee8 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65eec : bv 32 := 0x000680e7.
Lemma F_65eec : fetch_word Asan.M.loaded_segments (0x65f3c : word) = Some W_65eec.
Proof. vm_refl. Qed.
Lemma D_65eec : decode_any W_65eec = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ef0 : bv 32 := 0x060a0063.
Lemma F_65ef0 : fetch_word Asan.M.loaded_segments (0x65f40 : word) = Some W_65ef0.
Proof. vm_refl. Qed.
Lemma D_65ef0 : decode_any W_65ef0 = Some (Branch BC_EQ 20 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ef4 : bv 32 := 0x04a05e63.
Lemma F_65ef4 : fetch_word Asan.M.loaded_segments (0x65f44 : word) = Some W_65ef4.
Proof. vm_refl. Qed.
Lemma D_65ef4 : decode_any W_65ef4 = Some (Branch BC_GE 0 10 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ef8 : bv 32 := 0xfff4c593.
Lemma F_65ef8 : fetch_word Asan.M.loaded_segments (0x65f48 : word) = Some W_65ef8.
Proof. vm_refl. Qed.
Lemma D_65ef8 : decode_any W_65ef8 = Some (OpImm ALU_XOR 11 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_65efc : bv 32 := 0x80040a13.
Lemma F_65efc : fetch_word Asan.M.loaded_segments (0x65f4c : word) = Some W_65efc.
Proof. vm_refl. Qed.
Lemma D_65efc : decode_any W_65efc = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f00 : bv 32 := 0xfb8a0a13.
Lemma F_65f00 : fetch_word Asan.M.loaded_segments (0x65f50 : word) = Some W_65f00.
Proof. vm_refl. Qed.
Lemma D_65f00 : decode_any W_65f00 = Some (OpImm ALU_ADD 20 20 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f04 : bv 32 := 0x06a5e863.
Lemma F_65f04 : fetch_word Asan.M.loaded_segments (0x65f54 : word) = Some W_65f04.
Proof. vm_refl. Qed.
Lemma D_65f04 : decode_any W_65f04 = Some (Branch BC_LTU 11 10 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f08 : bv 32 := 0xfbf50593.
Lemma F_65f08 : fetch_word Asan.M.loaded_segments (0x65f58 : word) = Some W_65f08.
Proof. vm_refl. Qed.
Lemma D_65f08 : decode_any W_65f08 = Some (OpImm ALU_ADD 11 10 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f0c : bv 32 := 0xfc000613.
Lemma F_65f0c : fetch_word Asan.M.loaded_segments (0x65f5c : word) = Some W_65f0c.
Proof. vm_refl. Qed.
Lemma D_65f0c : decode_any W_65f0c = Some (OpImm ALU_ADD 12 0 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f10 : bv 32 := 0x0cc5ee63.
Lemma F_65f10 : fetch_word Asan.M.loaded_segments (0x65f60 : word) = Some W_65f10.
Proof. vm_refl. Qed.
Lemma D_65f10 : decode_any W_65f10 = Some (Branch BC_LTU 11 12 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f14 : bv 32 := 0x000d3597.
Lemma F_65f14 : fetch_word Asan.M.loaded_segments (0x65f64 : word) = Some W_65f14.
Proof. vm_refl. Qed.
Lemma D_65f14 : decode_any W_65f14 = Some (Auipc 11 211, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f18 : bv 32 := 0x2545b583.
Lemma F_65f18 : fetch_word Asan.M.loaded_segments (0x65f68 : word) = Some W_65f18.
Proof. vm_refl. Qed.
Lemma D_65f18 : decode_any W_65f18 = Some (Load SZ8 true 11 11 596, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f1c : bv 32 := 0x00a486b3.
Lemma F_65f1c : fetch_word Asan.M.loaded_segments (0x65f6c : word) = Some W_65f1c.
Proof. vm_refl. Qed.
Lemma D_65f1c : decode_any W_65f1c = Some (Op ALU_ADD 13 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f20 : bv 32 := 0x0005b603.
Lemma F_65f20 : fetch_word Asan.M.loaded_segments (0x65f70 : word) = Some W_65f20.
Proof. vm_refl. Qed.
Lemma D_65f20 : decode_any W_65f20 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f24 : bv 32 := 0x0034d593.
Lemma F_65f24 : fetch_word Asan.M.loaded_segments (0x65f74 : word) = Some W_65f24.
Proof. vm_refl. Qed.
Lemma D_65f24 : decode_any W_65f24 = Some (ShiftImm ALU_SRL 11 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f28 : bv 32 := 0xfff68693.
Lemma F_65f28 : fetch_word Asan.M.loaded_segments (0x65f78 : word) = Some W_65f28.
Proof. vm_refl. Qed.
Lemma D_65f28 : decode_any W_65f28 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f2c : bv 32 := 0x0036d713.
Lemma F_65f2c : fetch_word Asan.M.loaded_segments (0x65f7c : word) = Some W_65f2c.
Proof. vm_refl. Qed.
Lemma D_65f2c : decode_any W_65f2c = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f30 : bv 32 := 0x00b605b3.
Lemma F_65f30 : fetch_word Asan.M.loaded_segments (0x65f80 : word) = Some W_65f30.
Proof. vm_refl. Qed.
Lemma D_65f30 : decode_any W_65f30 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f34 : bv 32 := 0x00e60633.
Lemma F_65f34 : fetch_word Asan.M.loaded_segments (0x65f84 : word) = Some W_65f34.
Proof. vm_refl. Qed.
Lemma D_65f34 : decode_any W_65f34 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f38 : bv 32 := 0xff85f713.
Lemma F_65f38 : fetch_word Asan.M.loaded_segments (0x65f88 : word) = Some W_65f38.
Proof. vm_refl. Qed.
Lemma D_65f38 : decode_any W_65f38 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f3c : bv 32 := 0xff867793.
Lemma F_65f3c : fetch_word Asan.M.loaded_segments (0x65f8c : word) = Some W_65f3c.
Proof. vm_refl. Qed.
Lemma D_65f3c : decode_any W_65f3c = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f40 : bv 32 := 0x00073703.
Lemma F_65f40 : fetch_word Asan.M.loaded_segments (0x65f90 : word) = Some W_65f40.
Proof. vm_refl. Qed.
Lemma D_65f40 : decode_any W_65f40 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f44 : bv 32 := 0x0007b783.
Lemma F_65f44 : fetch_word Asan.M.loaded_segments (0x65f94 : word) = Some W_65f44.
Proof. vm_refl. Qed.
Lemma D_65f44 : decode_any W_65f44 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f48 : bv 32 := 0x00e7e733.
Lemma F_65f48 : fetch_word Asan.M.loaded_segments (0x65f98 : word) = Some W_65f48.
Proof. vm_refl. Qed.
Lemma D_65f48 : decode_any W_65f48 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f4c : bv 32 := 0x14071663.
Lemma F_65f4c : fetch_word Asan.M.loaded_segments (0x65f9c : word) = Some W_65f4c.
Proof. vm_refl. Qed.
Lemma D_65f4c : decode_any W_65f4c = Some (Branch BC_NE 14 0 332, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f50 : bv 32 := 0x06010113.
Lemma F_65f50 : fetch_word Asan.M.loaded_segments (0x65fa0 : word) = Some W_65f50.
Proof. vm_refl. Qed.
Lemma D_65f50 : decode_any W_65f50 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f54 : bv 32 := 0x7e813083.
Lemma F_65f54 : fetch_word Asan.M.loaded_segments (0x65fa4 : word) = Some W_65f54.
Proof. vm_refl. Qed.
Lemma D_65f54 : decode_any W_65f54 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f58 : bv 32 := 0x7e013403.
Lemma F_65f58 : fetch_word Asan.M.loaded_segments (0x65fa8 : word) = Some W_65f58.
Proof. vm_refl. Qed.
Lemma D_65f58 : decode_any W_65f58 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f5c : bv 32 := 0x7d813483.
Lemma F_65f5c : fetch_word Asan.M.loaded_segments (0x65fac : word) = Some W_65f5c.
Proof. vm_refl. Qed.
Lemma D_65f5c : decode_any W_65f5c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f60 : bv 32 := 0x7d013903.
Lemma F_65f60 : fetch_word Asan.M.loaded_segments (0x65fb0 : word) = Some W_65f60.
Proof. vm_refl. Qed.
Lemma D_65f60 : decode_any W_65f60 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f64 : bv 32 := 0x7c813983.
Lemma F_65f64 : fetch_word Asan.M.loaded_segments (0x65fb4 : word) = Some W_65f64.
Proof. vm_refl. Qed.
Lemma D_65f64 : decode_any W_65f64 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f68 : bv 32 := 0x7c013a03.
Lemma F_65f68 : fetch_word Asan.M.loaded_segments (0x65fb8 : word) = Some W_65f68.
Proof. vm_refl. Qed.
Lemma D_65f68 : decode_any W_65f68 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f6c : bv 32 := 0x7f010113.
Lemma F_65f6c : fetch_word Asan.M.loaded_segments (0x65fbc : word) = Some W_65f6c.
Proof. vm_refl. Qed.
Lemma D_65f6c : decode_any W_65f6c = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_65f70 : bv 32 := 0x00008067.
Lemma F_65f70 : fetch_word Asan.M.loaded_segments (0x65fc0 : word) = Some W_65f70.
Proof. vm_refl. Qed.
Lemma D_65f70 : decode_any W_65f70 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65fec : bv 32 := 0x00050913.
Lemma F_65fec : fetch_word Asan.M.loaded_segments (0x6603c : word) = Some W_65fec.
Proof. vm_refl. Qed.
Lemma D_65fec : decode_any W_65fec = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ff0 : bv 32 := 0x00048513.
Lemma F_65ff0 : fetch_word Asan.M.loaded_segments (0x66040 : word) = Some W_65ff0.
Proof. vm_refl. Qed.
Lemma D_65ff0 : decode_any W_65ff0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ff4 : bv 32 := 0x00090593.
Lemma F_65ff4 : fetch_word Asan.M.loaded_segments (0x66044 : word) = Some W_65ff4.
Proof. vm_refl. Qed.
Lemma D_65ff4 : decode_any W_65ff4 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ff8 : bv 32 := 0x5fd150ef.
Lemma F_65ff8 : fetch_word Asan.M.loaded_segments (0x66048 : word) = Some W_65ff8.
Proof. vm_refl. Qed.
Lemma D_65ff8 : decode_any W_65ff8 = Some (Jal 1 89596, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ffc : bv 32 := 0x00050493.
Lemma F_65ffc : fetch_word Asan.M.loaded_segments (0x6604c : word) = Some W_65ffc.
Proof. vm_refl. Qed.
Lemma D_65ffc : decode_any W_65ffc = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66000 : bv 32 := 0x00090513.
Lemma F_66000 : fetch_word Asan.M.loaded_segments (0x66050 : word) = Some W_66000.
Proof. vm_refl. Qed.
Lemma D_66000 : decode_any W_66000 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66004 : bv 32 := 0xf40486e3.
Lemma F_66004 : fetch_word Asan.M.loaded_segments (0x66054 : word) = Some W_66004.
Proof. vm_refl. Qed.
Lemma D_66004 : decode_any W_66004 = Some (Branch BC_EQ 9 0 8012, 4%Z).
Proof. vm_refl. Qed.

Definition W_66098 : bv 32 := 0x00060703.
Lemma F_66098 : fetch_word Asan.M.loaded_segments (0x660e8 : word) = Some W_66098.
Proof. vm_refl. Qed.
Lemma D_66098 : decode_any W_66098 = Some (Load SZ1 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6609c : bv 32 := 0x0076f693.
Lemma F_6609c : fetch_word Asan.M.loaded_segments (0x660ec : word) = Some W_6609c.
Proof. vm_refl. Qed.
Lemma D_6609c : decode_any W_6609c = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_660a0 : bv 32 := 0x00e037b3.
Lemma F_660a0 : fetch_word Asan.M.loaded_segments (0x660f0 : word) = Some W_660a0.
Proof. vm_refl. Qed.
Lemma D_660a0 : decode_any W_660a0 = Some (Op ALU_SLTU 15 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_660a4 : bv 32 := 0x00e6a6b3.
Lemma F_660a4 : fetch_word Asan.M.loaded_segments (0x660f4 : word) = Some W_660a4.
Proof. vm_refl. Qed.
Lemma D_660a4 : decode_any W_660a4 = Some (Op ALU_SLT 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_660a8 : bv 32 := 0x0016c693.
Lemma F_660a8 : fetch_word Asan.M.loaded_segments (0x660f8 : word) = Some W_660a8.
Proof. vm_refl. Qed.
Lemma D_660a8 : decode_any W_660a8 = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_660ac : bv 32 := 0x00d7f6b3.
Lemma F_660ac : fetch_word Asan.M.loaded_segments (0x660fc : word) = Some W_660ac.
Proof. vm_refl. Qed.
Lemma D_660ac : decode_any W_660ac = Some (Op ALU_AND 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_660b0 : bv 32 := 0x00c5fa63.
Lemma F_660b0 : fetch_word Asan.M.loaded_segments (0x66100 : word) = Some W_660b0.
Proof. vm_refl. Qed.
Lemma D_660b0 : decode_any W_660b0 = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_660b4 : bv 32 := 0x0005c703.
Lemma F_660b4 : fetch_word Asan.M.loaded_segments (0x66104 : word) = Some W_660b4.
Proof. vm_refl. Qed.
Lemma D_660b4 : decode_any W_660b4 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_660b8 : bv 32 := 0x00158593.
Lemma F_660b8 : fetch_word Asan.M.loaded_segments (0x66108 : word) = Some W_660b8.
Proof. vm_refl. Qed.
Lemma D_660b8 : decode_any W_660b8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_660bc : bv 32 := 0x00d766b3.
Lemma F_660bc : fetch_word Asan.M.loaded_segments (0x6610c : word) = Some W_660bc.
Proof. vm_refl. Qed.
Lemma D_660bc : decode_any W_660bc = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_660c0 : bv 32 := 0xfec59ae3.
Lemma F_660c0 : fetch_word Asan.M.loaded_segments (0x66110 : word) = Some W_660c0.
Proof. vm_refl. Qed.
Lemma D_660c0 : decode_any W_660c0 = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_660c4 : bv 32 := 0x0ff6f593.
Lemma F_660c4 : fetch_word Asan.M.loaded_segments (0x66114 : word) = Some W_660c4.
Proof. vm_refl. Qed.
Lemma D_660c4 : decode_any W_660c4 = Some (OpImm ALU_AND 11 13 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_660c8 : bv 32 := 0xe80584e3.
Lemma F_660c8 : fetch_word Asan.M.loaded_segments (0x66118 : word) = Some W_660c8.
Proof. vm_refl. Qed.
Lemma D_660c8 : decode_any W_660c8 = Some (Branch BC_EQ 11 0 7816, 4%Z).
Proof. vm_refl. Qed.

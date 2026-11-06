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

Definition W_4f400 : bv 32 := 0x060a0063.
Lemma F_4f400 : fetch_word Asan.M.loaded_segments (0x4f400 : word) = Some W_4f400.
Proof. vm_refl. Qed.
Lemma D_4f400 : decode_any W_4f400 = Some (Branch BC_EQ 20 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f404 : bv 32 := 0x0a051c63.
Lemma F_4f404 : fetch_word Asan.M.loaded_segments (0x4f404 : word) = Some W_4f404.
Proof. vm_refl. Qed.
Lemma D_4f404 : decode_any W_4f404 = Some (Branch BC_NE 10 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f408 : bv 32 := 0xfff94593.
Lemma F_4f408 : fetch_word Asan.M.loaded_segments (0x4f408 : word) = Some W_4f408.
Proof. vm_refl. Qed.
Lemma D_4f408 : decode_any W_4f408 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f40c : bv 32 := 0x80040a13.
Lemma F_4f40c : fetch_word Asan.M.loaded_segments (0x4f40c : word) = Some W_4f40c.
Proof. vm_refl. Qed.
Lemma D_4f40c : decode_any W_4f40c = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f410 : bv 32 := 0xfb0a0a13.
Lemma F_4f410 : fetch_word Asan.M.loaded_segments (0x4f410 : word) = Some W_4f410.
Proof. vm_refl. Qed.
Lemma D_4f410 : decode_any W_4f410 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f414 : bv 32 := 0x0c95e063.
Lemma F_4f414 : fetch_word Asan.M.loaded_segments (0x4f414 : word) = Some W_4f414.
Proof. vm_refl. Qed.
Lemma D_4f414 : decode_any W_4f414 = Some (Branch BC_LTU 11 9 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f418 : bv 32 := 0xfbf48593.
Lemma F_4f418 : fetch_word Asan.M.loaded_segments (0x4f418 : word) = Some W_4f418.
Proof. vm_refl. Qed.
Lemma D_4f418 : decode_any W_4f418 = Some (OpImm ALU_ADD 11 9 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f41c : bv 32 := 0xfbf00613.
Lemma F_4f41c : fetch_word Asan.M.loaded_segments (0x4f41c : word) = Some W_4f41c.
Proof. vm_refl. Qed.
Lemma D_4f41c : decode_any W_4f41c = Some (OpImm ALU_ADD 12 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f420 : bv 32 := 0x12b67663.
Lemma F_4f420 : fetch_word Asan.M.loaded_segments (0x4f420 : word) = Some W_4f420.
Proof. vm_refl. Qed.
Lemma D_4f420 : decode_any W_4f420 = Some (Branch BC_GEU 12 11 300, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f424 : bv 32 := 0x00086597.
Lemma F_4f424 : fetch_word Asan.M.loaded_segments (0x4f424 : word) = Some W_4f424.
Proof. vm_refl. Qed.
Lemma D_4f424 : decode_any W_4f424 = Some (Auipc 11 134, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f428 : bv 32 := 0x4945b583.
Lemma F_4f428 : fetch_word Asan.M.loaded_segments (0x4f428 : word) = Some W_4f428.
Proof. vm_refl. Qed.
Lemma D_4f428 : decode_any W_4f428 = Some (Load SZ8 true 11 11 1172, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f42c : bv 32 := 0x009906b3.
Lemma F_4f42c : fetch_word Asan.M.loaded_segments (0x4f42c : word) = Some W_4f42c.
Proof. vm_refl. Qed.
Lemma D_4f42c : decode_any W_4f42c = Some (Op ALU_ADD 13 18 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f430 : bv 32 := 0x0005b603.
Lemma F_4f430 : fetch_word Asan.M.loaded_segments (0x4f430 : word) = Some W_4f430.
Proof. vm_refl. Qed.
Lemma D_4f430 : decode_any W_4f430 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f434 : bv 32 := 0x00395593.
Lemma F_4f434 : fetch_word Asan.M.loaded_segments (0x4f434 : word) = Some W_4f434.
Proof. vm_refl. Qed.
Lemma D_4f434 : decode_any W_4f434 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f438 : bv 32 := 0xfff68693.
Lemma F_4f438 : fetch_word Asan.M.loaded_segments (0x4f438 : word) = Some W_4f438.
Proof. vm_refl. Qed.
Lemma D_4f438 : decode_any W_4f438 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f43c : bv 32 := 0x0036d713.
Lemma F_4f43c : fetch_word Asan.M.loaded_segments (0x4f43c : word) = Some W_4f43c.
Proof. vm_refl. Qed.
Lemma D_4f43c : decode_any W_4f43c = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f440 : bv 32 := 0x00b605b3.
Lemma F_4f440 : fetch_word Asan.M.loaded_segments (0x4f440 : word) = Some W_4f440.
Proof. vm_refl. Qed.
Lemma D_4f440 : decode_any W_4f440 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f444 : bv 32 := 0x00e60633.
Lemma F_4f444 : fetch_word Asan.M.loaded_segments (0x4f444 : word) = Some W_4f444.
Proof. vm_refl. Qed.
Lemma D_4f444 : decode_any W_4f444 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f448 : bv 32 := 0xff85f713.
Lemma F_4f448 : fetch_word Asan.M.loaded_segments (0x4f448 : word) = Some W_4f448.
Proof. vm_refl. Qed.
Lemma D_4f448 : decode_any W_4f448 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f44c : bv 32 := 0xff867793.
Lemma F_4f44c : fetch_word Asan.M.loaded_segments (0x4f44c : word) = Some W_4f44c.
Proof. vm_refl. Qed.
Lemma D_4f44c : decode_any W_4f44c = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f450 : bv 32 := 0x00073703.
Lemma F_4f450 : fetch_word Asan.M.loaded_segments (0x4f450 : word) = Some W_4f450.
Proof. vm_refl. Qed.
Lemma D_4f450 : decode_any W_4f450 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f454 : bv 32 := 0x0007b783.
Lemma F_4f454 : fetch_word Asan.M.loaded_segments (0x4f454 : word) = Some W_4f454.
Proof. vm_refl. Qed.
Lemma D_4f454 : decode_any W_4f454 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f458 : bv 32 := 0x00e7e733.
Lemma F_4f458 : fetch_word Asan.M.loaded_segments (0x4f458 : word) = Some W_4f458.
Proof. vm_refl. Qed.
Lemma D_4f458 : decode_any W_4f458 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f45c : bv 32 := 0x0e071c63.
Lemma F_4f45c : fetch_word Asan.M.loaded_segments (0x4f45c : word) = Some W_4f45c.
Proof. vm_refl. Qed.
Lemma D_4f45c : decode_any W_4f45c = Some (Branch BC_NE 14 0 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f460 : bv 32 := 0x06010113.
Lemma F_4f460 : fetch_word Asan.M.loaded_segments (0x4f460 : word) = Some W_4f460.
Proof. vm_refl. Qed.
Lemma D_4f460 : decode_any W_4f460 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f464 : bv 32 := 0x7e813083.
Lemma F_4f464 : fetch_word Asan.M.loaded_segments (0x4f464 : word) = Some W_4f464.
Proof. vm_refl. Qed.
Lemma D_4f464 : decode_any W_4f464 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f468 : bv 32 := 0x7e013403.
Lemma F_4f468 : fetch_word Asan.M.loaded_segments (0x4f468 : word) = Some W_4f468.
Proof. vm_refl. Qed.
Lemma D_4f468 : decode_any W_4f468 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f46c : bv 32 := 0x7d813483.
Lemma F_4f46c : fetch_word Asan.M.loaded_segments (0x4f46c : word) = Some W_4f46c.
Proof. vm_refl. Qed.
Lemma D_4f46c : decode_any W_4f46c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f470 : bv 32 := 0x7d013903.
Lemma F_4f470 : fetch_word Asan.M.loaded_segments (0x4f470 : word) = Some W_4f470.
Proof. vm_refl. Qed.
Lemma D_4f470 : decode_any W_4f470 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f474 : bv 32 := 0x7c813983.
Lemma F_4f474 : fetch_word Asan.M.loaded_segments (0x4f474 : word) = Some W_4f474.
Proof. vm_refl. Qed.
Lemma D_4f474 : decode_any W_4f474 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f478 : bv 32 := 0x7c013a03.
Lemma F_4f478 : fetch_word Asan.M.loaded_segments (0x4f478 : word) = Some W_4f478.
Proof. vm_refl. Qed.
Lemma D_4f478 : decode_any W_4f478 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f47c : bv 32 := 0x7b813a83.
Lemma F_4f47c : fetch_word Asan.M.loaded_segments (0x4f47c : word) = Some W_4f47c.
Proof. vm_refl. Qed.
Lemma D_4f47c : decode_any W_4f47c = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f480 : bv 32 := 0x7f010113.
Lemma F_4f480 : fetch_word Asan.M.loaded_segments (0x4f480 : word) = Some W_4f480.
Proof. vm_refl. Qed.
Lemma D_4f480 : decode_any W_4f480 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f484 : bv 32 := 0x00008067.
Lemma F_4f484 : fetch_word Asan.M.loaded_segments (0x4f484 : word) = Some W_4f484.
Proof. vm_refl. Qed.
Lemma D_4f484 : decode_any W_4f484 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f488 : bv 32 := 0x00090513.
Lemma F_4f488 : fetch_word Asan.M.loaded_segments (0x4f488 : word) = Some W_4f488.
Proof. vm_refl. Qed.
Lemma D_4f488 : decode_any W_4f488 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f48c : bv 32 := 0x00098593.
Lemma F_4f48c : fetch_word Asan.M.loaded_segments (0x4f48c : word) = Some W_4f48c.
Proof. vm_refl. Qed.
Lemma D_4f48c : decode_any W_4f48c = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f490 : bv 32 := 0x00048613.
Lemma F_4f490 : fetch_word Asan.M.loaded_segments (0x4f490 : word) = Some W_4f490.
Proof. vm_refl. Qed.
Lemma D_4f490 : decode_any W_4f490 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f494 : bv 32 := 0x06010113.
Lemma F_4f494 : fetch_word Asan.M.loaded_segments (0x4f494 : word) = Some W_4f494.
Proof. vm_refl. Qed.
Lemma D_4f494 : decode_any W_4f494 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f498 : bv 32 := 0x7e813083.
Lemma F_4f498 : fetch_word Asan.M.loaded_segments (0x4f498 : word) = Some W_4f498.
Proof. vm_refl. Qed.
Lemma D_4f498 : decode_any W_4f498 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f49c : bv 32 := 0x7e013403.
Lemma F_4f49c : fetch_word Asan.M.loaded_segments (0x4f49c : word) = Some W_4f49c.
Proof. vm_refl. Qed.
Lemma D_4f49c : decode_any W_4f49c = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f4a0 : bv 32 := 0x7d813483.
Lemma F_4f4a0 : fetch_word Asan.M.loaded_segments (0x4f4a0 : word) = Some W_4f4a0.
Proof. vm_refl. Qed.
Lemma D_4f4a0 : decode_any W_4f4a0 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f4a4 : bv 32 := 0x7d013903.
Lemma F_4f4a4 : fetch_word Asan.M.loaded_segments (0x4f4a4 : word) = Some W_4f4a4.
Proof. vm_refl. Qed.
Lemma D_4f4a4 : decode_any W_4f4a4 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f4a8 : bv 32 := 0x7c813983.
Lemma F_4f4a8 : fetch_word Asan.M.loaded_segments (0x4f4a8 : word) = Some W_4f4a8.
Proof. vm_refl. Qed.
Lemma D_4f4a8 : decode_any W_4f4a8 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f4ac : bv 32 := 0x7c013a03.
Lemma F_4f4ac : fetch_word Asan.M.loaded_segments (0x4f4ac : word) = Some W_4f4ac.
Proof. vm_refl. Qed.
Lemma D_4f4ac : decode_any W_4f4ac = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f4b0 : bv 32 := 0x7b813a83.
Lemma F_4f4b0 : fetch_word Asan.M.loaded_segments (0x4f4b0 : word) = Some W_4f4b0.
Proof. vm_refl. Qed.
Lemma D_4f4b0 : decode_any W_4f4b0 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f4b4 : bv 32 := 0x7f010113.
Lemma F_4f4b4 : fetch_word Asan.M.loaded_segments (0x4f4b4 : word) = Some W_4f4b4.
Proof. vm_refl. Qed.
Lemma D_4f4b4 : decode_any W_4f4b4 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f4b8 : bv 32 := 0x5d52106f.
Lemma F_4f4b8 : fetch_word Asan.M.loaded_segments (0x4f4b8 : word) = Some W_4f4b8.
Proof. vm_refl. Qed.
Lemma D_4f4b8 : decode_any W_4f4b8 = Some (Jal 0 138708, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f4bc : bv 32 := 0x412504b3.
Lemma F_4f4bc : fetch_word Asan.M.loaded_segments (0x4f4bc : word) = Some W_4f4bc.
Proof. vm_refl. Qed.
Lemma D_4f4bc : decode_any W_4f4bc = Some (Op ALU_SUB 9 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f4c0 : bv 32 := 0x00148493.
Lemma F_4f4c0 : fetch_word Asan.M.loaded_segments (0x4f4c0 : word) = Some W_4f4c0.
Proof. vm_refl. Qed.
Lemma D_4f4c0 : decode_any W_4f4c0 = Some (OpImm ALU_ADD 9 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f4c4 : bv 32 := 0xfff94593.
Lemma F_4f4c4 : fetch_word Asan.M.loaded_segments (0x4f4c4 : word) = Some W_4f4c4.
Proof. vm_refl. Qed.
Lemma D_4f4c4 : decode_any W_4f4c4 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f4c8 : bv 32 := 0x80040a13.
Lemma F_4f4c8 : fetch_word Asan.M.loaded_segments (0x4f4c8 : word) = Some W_4f4c8.
Proof. vm_refl. Qed.
Lemma D_4f4c8 : decode_any W_4f4c8 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f4cc : bv 32 := 0xfb0a0a13.
Lemma F_4f4cc : fetch_word Asan.M.loaded_segments (0x4f4cc : word) = Some W_4f4cc.
Proof. vm_refl. Qed.
Lemma D_4f4cc : decode_any W_4f4cc = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f4d0 : bv 32 := 0xf495f4e3.
Lemma F_4f4d0 : fetch_word Asan.M.loaded_segments (0x4f4d0 : word) = Some W_4f4d0.
Proof. vm_refl. Qed.
Lemma D_4f4d0 : decode_any W_4f4d0 = Some (Branch BC_GEU 11 9 8008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f4d4 : bv 32 := 0x80040593.
Lemma F_4f4d4 : fetch_word Asan.M.loaded_segments (0x4f4d4 : word) = Some W_4f4d4.
Proof. vm_refl. Qed.
Lemma D_4f4d4 : decode_any W_4f4d4 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f4d8 : bv 32 := 0xfc058593.
Lemma F_4f4d8 : fetch_word Asan.M.loaded_segments (0x4f4d8 : word) = Some W_4f4d8.
Proof. vm_refl. Qed.
Lemma D_4f4d8 : decode_any W_4f4d8 = Some (OpImm ALU_ADD 11 11 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f4dc : bv 32 := 0x80040613.
Lemma F_4f4dc : fetch_word Asan.M.loaded_segments (0x4f4dc : word) = Some W_4f4dc.
Proof. vm_refl. Qed.
Lemma D_4f4dc : decode_any W_4f4dc = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f4e0 : bv 32 := 0xfb060613.
Lemma F_4f4e0 : fetch_word Asan.M.loaded_segments (0x4f4e0 : word) = Some W_4f4e0.
Proof. vm_refl. Qed.
Lemma D_4f4e0 : decode_any W_4f4e0 = Some (OpImm ALU_ADD 12 12 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f4e4 : bv 32 := 0x7ff60a93.
Lemma F_4f4e4 : fetch_word Asan.M.loaded_segments (0x4f4e4 : word) = Some W_4f4e4.
Proof. vm_refl. Qed.
Lemma D_4f4e4 : decode_any W_4f4e4 = Some (OpImm ALU_ADD 21 12 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f4e8 : bv 32 := 0x000ab4a3.
Lemma F_4f4e8 : fetch_word Asan.M.loaded_segments (0x4f4e8 : word) = Some W_4f4e8.
Proof. vm_refl. Qed.
Lemma D_4f4e8 : decode_any W_4f4e8 = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f4ec : bv 32 := 0x00ba3023.
Lemma F_4f4ec : fetch_word Asan.M.loaded_segments (0x4f4ec : word) = Some W_4f4ec.
Proof. vm_refl. Qed.
Lemma D_4f4ec : decode_any W_4f4ec = Some (Store SZ8 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f4f0 : bv 32 := 0x000a3423.
Lemma F_4f4f0 : fetch_word Asan.M.loaded_segments (0x4f4f0 : word) = Some W_4f4f0.
Proof. vm_refl. Qed.
Lemma D_4f4f0 : decode_any W_4f4f0 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f4f4 : bv 32 := 0x00050993.
Lemma F_4f4f4 : fetch_word Asan.M.loaded_segments (0x4f4f4 : word) = Some W_4f4f4.
Proof. vm_refl. Qed.
Lemma D_4f4f4 : decode_any W_4f4f4 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f4f8 : bv 32 := 0x334310ef.
Lemma F_4f4f8 : fetch_word Asan.M.loaded_segments (0x4f4f8 : word) = Some W_4f4f8.
Proof. vm_refl. Qed.
Lemma D_4f4f8 : decode_any W_4f4f8 = Some (Jal 1 201524, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f4fc : bv 32 := 0x00050593.
Lemma F_4f4fc : fetch_word Asan.M.loaded_segments (0x4f4fc : word) = Some W_4f4fc.
Proof. vm_refl. Qed.
Lemma D_4f4fc : decode_any W_4f4fc = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f500 : bv 32 := 0x00086517.
Lemma F_4f500 : fetch_word Asan.M.loaded_segments (0x4f500 : word) = Some W_4f500.
Proof. vm_refl. Qed.
Lemma D_4f500 : decode_any W_4f500 = Some (Auipc 10 134, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f504 : bv 32 := 0x3a853503.
Lemma F_4f504 : fetch_word Asan.M.loaded_segments (0x4f504 : word) = Some W_4f504.
Proof. vm_refl. Qed.
Lemma D_4f504 : decode_any W_4f504 = Some (Load SZ8 true 10 10 936, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f508 : bv 32 := 0x02154703.
Lemma F_4f508 : fetch_word Asan.M.loaded_segments (0x4f508 : word) = Some W_4f508.
Proof. vm_refl. Qed.
Lemma D_4f508 : decode_any W_4f508 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f50c : bv 32 := 0x008ab4a3.
Lemma F_4f50c : fetch_word Asan.M.loaded_segments (0x4f50c : word) = Some W_4f50c.
Proof. vm_refl. Qed.
Lemma D_4f50c : decode_any W_4f50c = Some (Store SZ8 21 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f510 : bv 32 := 0x80040513.
Lemma F_4f510 : fetch_word Asan.M.loaded_segments (0x4f510 : word) = Some W_4f510.
Proof. vm_refl. Qed.
Lemma D_4f510 : decode_any W_4f510 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f514 : bv 32 := 0xfb050513.
Lemma F_4f514 : fetch_word Asan.M.loaded_segments (0x4f514 : word) = Some W_4f514.
Proof. vm_refl. Qed.
Lemma D_4f514 : decode_any W_4f514 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f518 : bv 32 := 0x0ff00793.
Lemma F_4f518 : fetch_word Asan.M.loaded_segments (0x4f518 : word) = Some W_4f518.
Proof. vm_refl. Qed.
Lemma D_4f518 : decode_any W_4f518 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f51c : bv 32 := 0x00040613.
Lemma F_4f51c : fetch_word Asan.M.loaded_segments (0x4f51c : word) = Some W_4f51c.
Proof. vm_refl. Qed.
Lemma D_4f51c : decode_any W_4f51c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f520 : bv 32 := 0x00000693.
Lemma F_4f520 : fetch_word Asan.M.loaded_segments (0x4f520 : word) = Some W_4f520.
Proof. vm_refl. Qed.
Lemma D_4f520 : decode_any W_4f520 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f524 : bv 32 := 0x059180ef.
Lemma F_4f524 : fetch_word Asan.M.loaded_segments (0x4f524 : word) = Some W_4f524.
Proof. vm_refl. Qed.
Lemma D_4f524 : decode_any W_4f524 = Some (Jal 1 100440, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f528 : bv 32 := 0x80040613.
Lemma F_4f528 : fetch_word Asan.M.loaded_segments (0x4f528 : word) = Some W_4f528.
Proof. vm_refl. Qed.
Lemma D_4f528 : decode_any W_4f528 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f52c : bv 32 := 0xfb060613.
Lemma F_4f52c : fetch_word Asan.M.loaded_segments (0x4f52c : word) = Some W_4f52c.
Proof. vm_refl. Qed.
Lemma D_4f52c : decode_any W_4f52c = Some (OpImm ALU_ADD 12 12 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f530 : bv 32 := 0x00090513.
Lemma F_4f530 : fetch_word Asan.M.loaded_segments (0x4f530 : word) = Some W_4f530.
Proof. vm_refl. Qed.
Lemma D_4f530 : decode_any W_4f530 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f534 : bv 32 := 0x00048593.
Lemma F_4f534 : fetch_word Asan.M.loaded_segments (0x4f534 : word) = Some W_4f534.
Proof. vm_refl. Qed.
Lemma D_4f534 : decode_any W_4f534 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f538 : bv 32 := 0x5fc150ef.
Lemma F_4f538 : fetch_word Asan.M.loaded_segments (0x4f538 : word) = Some W_4f538.
Proof. vm_refl. Qed.
Lemma D_4f538 : decode_any W_4f538 = Some (Jal 1 87548, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f53c : bv 32 := 0x00098513.
Lemma F_4f53c : fetch_word Asan.M.loaded_segments (0x4f53c : word) = Some W_4f53c.
Proof. vm_refl. Qed.
Lemma D_4f53c : decode_any W_4f53c = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f540 : bv 32 := 0xfbf48593.
Lemma F_4f540 : fetch_word Asan.M.loaded_segments (0x4f540 : word) = Some W_4f540.
Proof. vm_refl. Qed.
Lemma D_4f540 : decode_any W_4f540 = Some (OpImm ALU_ADD 11 9 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f544 : bv 32 := 0xfbf00613.
Lemma F_4f544 : fetch_word Asan.M.loaded_segments (0x4f544 : word) = Some W_4f544.
Proof. vm_refl. Qed.
Lemma D_4f544 : decode_any W_4f544 = Some (OpImm ALU_ADD 12 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f548 : bv 32 := 0xecb66ee3.
Lemma F_4f548 : fetch_word Asan.M.loaded_segments (0x4f548 : word) = Some W_4f548.
Proof. vm_refl. Qed.
Lemma D_4f548 : decode_any W_4f548 = Some (Branch BC_LTU 12 11 7900, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f54c : bv 32 := 0x02049e63.
Lemma F_4f54c : fetch_word Asan.M.loaded_segments (0x4f54c : word) = Some W_4f54c.
Proof. vm_refl. Qed.
Lemma D_4f54c : decode_any W_4f54c = Some (Branch BC_NE 9 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f550 : bv 32 := 0xf11ff06f.
Lemma F_4f550 : fetch_word Asan.M.loaded_segments (0x4f550 : word) = Some W_4f550.
Proof. vm_refl. Qed.
Lemma D_4f550 : decode_any W_4f550 = Some (Jal 0 2096912, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f554 : bv 32 := 0x00060703.
Lemma F_4f554 : fetch_word Asan.M.loaded_segments (0x4f554 : word) = Some W_4f554.
Proof. vm_refl. Qed.
Lemma D_4f554 : decode_any W_4f554 = Some (Load SZ1 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f558 : bv 32 := 0x0076f693.
Lemma F_4f558 : fetch_word Asan.M.loaded_segments (0x4f558 : word) = Some W_4f558.
Proof. vm_refl. Qed.
Lemma D_4f558 : decode_any W_4f558 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f55c : bv 32 := 0x00e037b3.
Lemma F_4f55c : fetch_word Asan.M.loaded_segments (0x4f55c : word) = Some W_4f55c.
Proof. vm_refl. Qed.
Lemma D_4f55c : decode_any W_4f55c = Some (Op ALU_SLTU 15 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f560 : bv 32 := 0x00e6a6b3.
Lemma F_4f560 : fetch_word Asan.M.loaded_segments (0x4f560 : word) = Some W_4f560.
Proof. vm_refl. Qed.
Lemma D_4f560 : decode_any W_4f560 = Some (Op ALU_SLT 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f564 : bv 32 := 0x0016c693.
Lemma F_4f564 : fetch_word Asan.M.loaded_segments (0x4f564 : word) = Some W_4f564.
Proof. vm_refl. Qed.
Lemma D_4f564 : decode_any W_4f564 = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f568 : bv 32 := 0x00d7f6b3.
Lemma F_4f568 : fetch_word Asan.M.loaded_segments (0x4f568 : word) = Some W_4f568.
Proof. vm_refl. Qed.
Lemma D_4f568 : decode_any W_4f568 = Some (Op ALU_AND 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f56c : bv 32 := 0x00c5fa63.
Lemma F_4f56c : fetch_word Asan.M.loaded_segments (0x4f56c : word) = Some W_4f56c.
Proof. vm_refl. Qed.
Lemma D_4f56c : decode_any W_4f56c = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f570 : bv 32 := 0x0005c703.
Lemma F_4f570 : fetch_word Asan.M.loaded_segments (0x4f570 : word) = Some W_4f570.
Proof. vm_refl. Qed.
Lemma D_4f570 : decode_any W_4f570 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f574 : bv 32 := 0x00158593.
Lemma F_4f574 : fetch_word Asan.M.loaded_segments (0x4f574 : word) = Some W_4f574.
Proof. vm_refl. Qed.
Lemma D_4f574 : decode_any W_4f574 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f578 : bv 32 := 0x00d766b3.
Lemma F_4f578 : fetch_word Asan.M.loaded_segments (0x4f578 : word) = Some W_4f578.
Proof. vm_refl. Qed.
Lemma D_4f578 : decode_any W_4f578 = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f57c : bv 32 := 0xfec59ae3.
Lemma F_4f57c : fetch_word Asan.M.loaded_segments (0x4f57c : word) = Some W_4f57c.
Proof. vm_refl. Qed.
Lemma D_4f57c : decode_any W_4f57c = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f580 : bv 32 := 0x0ff6f593.
Lemma F_4f580 : fetch_word Asan.M.loaded_segments (0x4f580 : word) = Some W_4f580.
Proof. vm_refl. Qed.
Lemma D_4f580 : decode_any W_4f580 = Some (OpImm ALU_AND 11 13 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f584 : bv 32 := 0xec058ee3.
Lemma F_4f584 : fetch_word Asan.M.loaded_segments (0x4f584 : word) = Some W_4f584.
Proof. vm_refl. Qed.
Lemma D_4f584 : decode_any W_4f584 = Some (Branch BC_EQ 11 0 7900, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f588 : bv 32 := 0x00050a93.
Lemma F_4f588 : fetch_word Asan.M.loaded_segments (0x4f588 : word) = Some W_4f588.
Proof. vm_refl. Qed.
Lemma D_4f588 : decode_any W_4f588 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f58c : bv 32 := 0x00090513.
Lemma F_4f58c : fetch_word Asan.M.loaded_segments (0x4f58c : word) = Some W_4f58c.
Proof. vm_refl. Qed.
Lemma D_4f58c : decode_any W_4f58c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f590 : bv 32 := 0x00048593.
Lemma F_4f590 : fetch_word Asan.M.loaded_segments (0x4f590 : word) = Some W_4f590.
Proof. vm_refl. Qed.
Lemma D_4f590 : decode_any W_4f590 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f594 : bv 32 := 0x36c120ef.
Lemma F_4f594 : fetch_word Asan.M.loaded_segments (0x4f594 : word) = Some W_4f594.
Proof. vm_refl. Qed.
Lemma D_4f594 : decode_any W_4f594 = Some (Jal 1 74604, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f598 : bv 32 := 0x00050913.
Lemma F_4f598 : fetch_word Asan.M.loaded_segments (0x4f598 : word) = Some W_4f598.
Proof. vm_refl. Qed.
Lemma D_4f598 : decode_any W_4f598 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f59c : bv 32 := 0x000a8513.
Lemma F_4f59c : fetch_word Asan.M.loaded_segments (0x4f59c : word) = Some W_4f59c.
Proof. vm_refl. Qed.
Lemma D_4f59c : decode_any W_4f59c = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f5a0 : bv 32 := 0xec0900e3.
Lemma F_4f5a0 : fetch_word Asan.M.loaded_segments (0x4f5a0 : word) = Some W_4f5a0.
Proof. vm_refl. Qed.
Lemma D_4f5a0 : decode_any W_4f5a0 = Some (Branch BC_EQ 18 0 7872, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f5a4 : bv 32 := 0xfffcc517.
Lemma F_4f5a4 : fetch_word Asan.M.loaded_segments (0x4f5a4 : word) = Some W_4f5a4.
Proof. vm_refl. Qed.
Lemma D_4f5a4 : decode_any W_4f5a4 = Some (Auipc 10 1048524, 4%Z).
Proof. vm_refl. Qed.

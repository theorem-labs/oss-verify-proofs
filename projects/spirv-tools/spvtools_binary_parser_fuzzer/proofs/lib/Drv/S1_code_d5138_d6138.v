(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_d5348 : bv 32 := 0xf9010113.
Lemma F_d5348 : fetch_word Plain.M.loaded_segments (0xd537c : word) = Some W_d5348.
Proof. vm_refl. Qed.
Lemma D_d5348 : decode_any W_d5348 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_d534c : bv 32 := 0x06113423.
Lemma F_d534c : fetch_word Plain.M.loaded_segments (0xd5380 : word) = Some W_d534c.
Proof. vm_refl. Qed.
Lemma D_d534c : decode_any W_d534c = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5350 : bv 32 := 0x06813023.
Lemma F_d5350 : fetch_word Plain.M.loaded_segments (0xd5384 : word) = Some W_d5350.
Proof. vm_refl. Qed.
Lemma D_d5350 : decode_any W_d5350 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5354 : bv 32 := 0x04913c23.
Lemma F_d5354 : fetch_word Plain.M.loaded_segments (0xd5388 : word) = Some W_d5354.
Proof. vm_refl. Qed.
Lemma D_d5354 : decode_any W_d5354 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5358 : bv 32 := 0x05213823.
Lemma F_d5358 : fetch_word Plain.M.loaded_segments (0xd538c : word) = Some W_d5358.
Proof. vm_refl. Qed.
Lemma D_d5358 : decode_any W_d5358 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_d535c : bv 32 := 0x05313423.
Lemma F_d535c : fetch_word Plain.M.loaded_segments (0xd5390 : word) = Some W_d535c.
Proof. vm_refl. Qed.
Lemma D_d535c : decode_any W_d535c = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5360 : bv 32 := 0x05413023.
Lemma F_d5360 : fetch_word Plain.M.loaded_segments (0xd5394 : word) = Some W_d5360.
Proof. vm_refl. Qed.
Lemma D_d5360 : decode_any W_d5360 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5364 : bv 32 := 0x03513c23.
Lemma F_d5364 : fetch_word Plain.M.loaded_segments (0xd5398 : word) = Some W_d5364.
Proof. vm_refl. Qed.
Lemma D_d5364 : decode_any W_d5364 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5368 : bv 32 := 0x03613823.
Lemma F_d5368 : fetch_word Plain.M.loaded_segments (0xd539c : word) = Some W_d5368.
Proof. vm_refl. Qed.
Lemma D_d5368 : decode_any W_d5368 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_d536c : bv 32 := 0x00060413.
Lemma F_d536c : fetch_word Plain.M.loaded_segments (0xd53a0 : word) = Some W_d536c.
Proof. vm_refl. Qed.
Lemma D_d536c : decode_any W_d536c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5370 : bv 32 := 0x00050493.
Lemma F_d5370 : fetch_word Plain.M.loaded_segments (0xd53a4 : word) = Some W_d5370.
Proof. vm_refl. Qed.
Lemma D_d5370 : decode_any W_d5370 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5374 : bv 32 := 0x00018517.
Lemma F_d5374 : fetch_word Plain.M.loaded_segments (0xd53a8 : word) = Some W_d5374.
Proof. vm_refl. Qed.
Lemma D_d5374 : decode_any W_d5374 = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5378 : bv 32 := 0xd1053a83.
Lemma F_d5378 : fetch_word Plain.M.loaded_segments (0xd53ac : word) = Some W_d5378.
Proof. vm_refl. Qed.
Lemma D_d5378 : decode_any W_d5378 = Some (Load SZ8 true 21 10 3344, 4%Z).
Proof. vm_refl. Qed.

Definition W_d537c : bv 32 := 0x000ab503.
Lemma F_d537c : fetch_word Plain.M.loaded_segments (0xd53b0 : word) = Some W_d537c.
Proof. vm_refl. Qed.
Lemma D_d537c : decode_any W_d537c = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5380 : bv 32 := 0x02a13423.
Lemma F_d5380 : fetch_word Plain.M.loaded_segments (0xd53b4 : word) = Some W_d5380.
Proof. vm_refl. Qed.
Lemma D_d5380 : decode_any W_d5380 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5384 : bv 32 := 0x0284b503.
Lemma F_d5384 : fetch_word Plain.M.loaded_segments (0xd53b8 : word) = Some W_d5384.
Proof. vm_refl. Qed.
Lemma D_d5384 : decode_any W_d5384 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5388 : bv 32 := 0x0384b603.
Lemma F_d5388 : fetch_word Plain.M.loaded_segments (0xd53bc : word) = Some W_d5388.
Proof. vm_refl. Qed.
Lemma D_d5388 : decode_any W_d5388 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_d538c : bv 32 := 0x40c50b33.
Lemma F_d538c : fetch_word Plain.M.loaded_segments (0xd53c0 : word) = Some W_d538c.
Proof. vm_refl. Qed.
Lemma D_d538c : decode_any W_d538c = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5390 : bv 32 := 0x00c546b3.
Lemma F_d5390 : fetch_word Plain.M.loaded_segments (0xd53c4 : word) = Some W_d5390.
Proof. vm_refl. Qed.
Lemma D_d5390 : decode_any W_d5390 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5394 : bv 32 := 0x00c13423.
Lemma F_d5394 : fetch_word Plain.M.loaded_segments (0xd53c8 : word) = Some W_d5394.
Proof. vm_refl. Qed.
Lemma D_d5394 : decode_any W_d5394 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5398 : bv 32 := 0x01613823.
Lemma F_d5398 : fetch_word Plain.M.loaded_segments (0xd53cc : word) = Some W_d5398.
Proof. vm_refl. Qed.
Lemma D_d5398 : decode_any W_d5398 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d539c : bv 32 := 0x00b13c23.
Lemma F_d539c : fetch_word Plain.M.loaded_segments (0xd53d0 : word) = Some W_d539c.
Proof. vm_refl. Qed.
Lemma D_d539c : decode_any W_d539c = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d53a0 : bv 32 := 0x02813023.
Lemma F_d53a0 : fetch_word Plain.M.loaded_segments (0xd53d4 : word) = Some W_d53a0.
Proof. vm_refl. Qed.
Lemma D_d53a0 : decode_any W_d53a0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_d53a4 : bv 32 := 0x008b0b33.
Lemma F_d53a4 : fetch_word Plain.M.loaded_segments (0xd53d8 : word) = Some W_d53a4.
Proof. vm_refl. Qed.
Lemma D_d53a4 : decode_any W_d53a4 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d53a8 : bv 32 := 0x00d03933.
Lemma F_d53a8 : fetch_word Plain.M.loaded_segments (0xd53dc : word) = Some W_d53a8.
Proof. vm_refl. Qed.
Lemma D_d53a8 : decode_any W_d53a8 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_d53ac : bv 32 := 0x00c50663.
Lemma F_d53ac : fetch_word Plain.M.loaded_segments (0xd53e0 : word) = Some W_d53ac.
Proof. vm_refl. Qed.
Lemma D_d53ac : decode_any W_d53ac = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d53b0 : bv 32 := 0x00810993.
Lemma F_d53b0 : fetch_word Plain.M.loaded_segments (0xd53e4 : word) = Some W_d53b0.
Proof. vm_refl. Qed.
Lemma D_d53b0 : decode_any W_d53b0 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d53b4 : bv 32 := 0x0080006f.
Lemma F_d53b4 : fetch_word Plain.M.loaded_segments (0xd53e8 : word) = Some W_d53b4.
Proof. vm_refl. Qed.
Lemma D_d53b4 : decode_any W_d53b4 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d53b8 : bv 32 := 0x01810993.
Lemma F_d53b8 : fetch_word Plain.M.loaded_segments (0xd53ec : word) = Some W_d53b8.
Proof. vm_refl. Qed.
Lemma D_d53b8 : decode_any W_d53b8 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d53bc : bv 32 := 0x0784a503.
Lemma F_d53bc : fetch_word Plain.M.loaded_segments (0xd53f0 : word) = Some W_d53bc.
Proof. vm_refl. Qed.
Lemma D_d53bc : decode_any W_d53bc = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_d53c0 : bv 32 := 0x00190913.
Lemma F_d53c0 : fetch_word Plain.M.loaded_segments (0xd53f4 : word) = Some W_d53c0.
Proof. vm_refl. Qed.
Lemma D_d53c0 : decode_any W_d53c0 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_d53c4 : bv 32 := 0x04200893.
Lemma F_d53c4 : fetch_word Plain.M.loaded_segments (0xd53f8 : word) = Some W_d53c4.
Proof. vm_refl. Qed.
Lemma D_d53c4 : decode_any W_d53c4 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_d53c8 : bv 32 := 0x00098593.
Lemma F_d53c8 : fetch_word Plain.M.loaded_segments (0xd53fc : word) = Some W_d53c8.
Proof. vm_refl. Qed.
Lemma D_d53c8 : decode_any W_d53c8 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d53cc : bv 32 := 0x00090613.
Lemma F_d53cc : fetch_word Plain.M.loaded_segments (0xd5400 : word) = Some W_d53cc.
Proof. vm_refl. Qed.
Lemma D_d53cc : decode_any W_d53cc = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d53d0 : bv 32 := 0x00000073.
Lemma F_d53d0 : fetch_word Plain.M.loaded_segments (0xd5404 : word) = Some W_d53d0.
Proof. vm_refl. Qed.

Lemma E_d53d0 : is_ecall W_d53d0 = true.
Proof. reflexivity. Qed.

Definition W_d53d4 : bv 32 := 0xeb5fa0ef.
Lemma F_d53d4 : fetch_word Plain.M.loaded_segments (0xd5408 : word) = Some W_d53d4.
Proof. vm_refl. Qed.
Lemma D_d53d4 : decode_any W_d53d4 = Some (Jal 1 2076340, 4%Z).
Proof. vm_refl. Qed.

Definition W_d53d8 : bv 32 := 0x09651863.
Lemma F_d53d8 : fetch_word Plain.M.loaded_segments (0xd540c : word) = Some W_d53d8.
Proof. vm_refl. Qed.
Lemma D_d53d8 : decode_any W_d53d8 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_d53dc : bv 32 := 0x0584b503.
Lemma F_d53dc : fetch_word Plain.M.loaded_segments (0xd5410 : word) = Some W_d53dc.
Proof. vm_refl. Qed.
Lemma D_d53dc : decode_any W_d53dc = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_d53e0 : bv 32 := 0x0604b583.
Lemma F_d53e0 : fetch_word Plain.M.loaded_segments (0xd5414 : word) = Some W_d53e0.
Proof. vm_refl. Qed.
Lemma D_d53e0 : decode_any W_d53e0 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_d53e4 : bv 32 := 0x00b505b3.
Lemma F_d53e4 : fetch_word Plain.M.loaded_segments (0xd5418 : word) = Some W_d53e4.
Proof. vm_refl. Qed.
Lemma D_d53e4 : decode_any W_d53e4 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_d53e8 : bv 32 := 0x02b4b023.
Lemma F_d53e8 : fetch_word Plain.M.loaded_segments (0xd541c : word) = Some W_d53e8.
Proof. vm_refl. Qed.
Lemma D_d53e8 : decode_any W_d53e8 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_d53ec : bv 32 := 0x02a4b423.
Lemma F_d53ec : fetch_word Plain.M.loaded_segments (0xd5420 : word) = Some W_d53ec.
Proof. vm_refl. Qed.
Lemma D_d53ec : decode_any W_d53ec = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_d53f0 : bv 32 := 0x02a4bc23.
Lemma F_d53f0 : fetch_word Plain.M.loaded_segments (0xd5424 : word) = Some W_d53f0.
Proof. vm_refl. Qed.
Lemma D_d53f0 : decode_any W_d53f0 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_d53f4 : bv 32 := 0x00040513.
Lemma F_d53f4 : fetch_word Plain.M.loaded_segments (0xd5428 : word) = Some W_d53f4.
Proof. vm_refl. Qed.
Lemma D_d53f4 : decode_any W_d53f4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d53f8 : bv 32 := 0x000ab583.
Lemma F_d53f8 : fetch_word Plain.M.loaded_segments (0xd542c : word) = Some W_d53f8.
Proof. vm_refl. Qed.
Lemma D_d53f8 : decode_any W_d53f8 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d53fc : bv 32 := 0x02813603.
Lemma F_d53fc : fetch_word Plain.M.loaded_segments (0xd5430 : word) = Some W_d53fc.
Proof. vm_refl. Qed.
Lemma D_d53fc : decode_any W_d53fc = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5400 : bv 32 := 0x0cc59a63.
Lemma F_d5400 : fetch_word Plain.M.loaded_segments (0xd5434 : word) = Some W_d5400.
Proof. vm_refl. Qed.
Lemma D_d5400 : decode_any W_d5400 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5404 : bv 32 := 0x06813083.
Lemma F_d5404 : fetch_word Plain.M.loaded_segments (0xd5438 : word) = Some W_d5404.
Proof. vm_refl. Qed.
Lemma D_d5404 : decode_any W_d5404 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5408 : bv 32 := 0x06013403.
Lemma F_d5408 : fetch_word Plain.M.loaded_segments (0xd543c : word) = Some W_d5408.
Proof. vm_refl. Qed.
Lemma D_d5408 : decode_any W_d5408 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_d540c : bv 32 := 0x05813483.
Lemma F_d540c : fetch_word Plain.M.loaded_segments (0xd5440 : word) = Some W_d540c.
Proof. vm_refl. Qed.
Lemma D_d540c : decode_any W_d540c = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5410 : bv 32 := 0x05013903.
Lemma F_d5410 : fetch_word Plain.M.loaded_segments (0xd5444 : word) = Some W_d5410.
Proof. vm_refl. Qed.
Lemma D_d5410 : decode_any W_d5410 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5414 : bv 32 := 0x04813983.
Lemma F_d5414 : fetch_word Plain.M.loaded_segments (0xd5448 : word) = Some W_d5414.
Proof. vm_refl. Qed.
Lemma D_d5414 : decode_any W_d5414 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5418 : bv 32 := 0x04013a03.
Lemma F_d5418 : fetch_word Plain.M.loaded_segments (0xd544c : word) = Some W_d5418.
Proof. vm_refl. Qed.
Lemma D_d5418 : decode_any W_d5418 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_d541c : bv 32 := 0x03813a83.
Lemma F_d541c : fetch_word Plain.M.loaded_segments (0xd5450 : word) = Some W_d541c.
Proof. vm_refl. Qed.
Lemma D_d541c : decode_any W_d541c = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5420 : bv 32 := 0x03013b03.
Lemma F_d5420 : fetch_word Plain.M.loaded_segments (0xd5454 : word) = Some W_d5420.
Proof. vm_refl. Qed.
Lemma D_d5420 : decode_any W_d5420 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5424 : bv 32 := 0x07010113.
Lemma F_d5424 : fetch_word Plain.M.loaded_segments (0xd5458 : word) = Some W_d5424.
Proof. vm_refl. Qed.
Lemma D_d5424 : decode_any W_d5424 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5428 : bv 32 := 0x00008067.
Lemma F_d5428 : fetch_word Plain.M.loaded_segments (0xd545c : word) = Some W_d5428.
Proof. vm_refl. Qed.
Lemma D_d5428 : decode_any W_d5428 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d542c : bv 32 := 0x00800713.
Lemma F_d542c : fetch_word Plain.M.loaded_segments (0xd5460 : word) = Some W_d542c.
Proof. vm_refl. Qed.
Lemma D_d542c : decode_any W_d542c = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5430 : bv 32 := 0x000a0593.
Lemma F_d5430 : fetch_word Plain.M.loaded_segments (0xd5464 : word) = Some W_d5430.
Proof. vm_refl. Qed.
Lemma D_d5430 : decode_any W_d5430 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5434 : bv 32 := 0x00e98733.
Lemma F_d5434 : fetch_word Plain.M.loaded_segments (0xd5468 : word) = Some W_d5434.
Proof. vm_refl. Qed.
Lemma D_d5434 : decode_any W_d5434 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5438 : bv 32 := 0x00073783.
Lemma F_d5438 : fetch_word Plain.M.loaded_segments (0xd546c : word) = Some W_d5438.
Proof. vm_refl. Qed.
Lemma D_d5438 : decode_any W_d5438 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d543c : bv 32 := 0x40ab0b33.
Lemma F_d543c : fetch_word Plain.M.loaded_segments (0xd5470 : word) = Some W_d543c.
Proof. vm_refl. Qed.
Lemma D_d543c : decode_any W_d543c = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5440 : bv 32 := 0x0784a503.
Lemma F_d5440 : fetch_word Plain.M.loaded_segments (0xd5474 : word) = Some W_d5440.
Proof. vm_refl. Qed.
Lemma D_d5440 : decode_any W_d5440 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5444 : bv 32 := 0x40c9093b.
Lemma F_d5444 : fetch_word Plain.M.loaded_segments (0xd5478 : word) = Some W_d5444.
Proof. vm_refl. Qed.
Lemma D_d5444 : decode_any W_d5444 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5448 : bv 32 := 0x40d787b3.
Lemma F_d5448 : fetch_word Plain.M.loaded_segments (0xd547c : word) = Some W_d5448.
Proof. vm_refl. Qed.
Lemma D_d5448 : decode_any W_d5448 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_d544c : bv 32 := 0x00f73023.
Lemma F_d544c : fetch_word Plain.M.loaded_segments (0xd5480 : word) = Some W_d544c.
Proof. vm_refl. Qed.
Lemma D_d544c : decode_any W_d544c = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5450 : bv 32 := 0x04200893.
Lemma F_d5450 : fetch_word Plain.M.loaded_segments (0xd5484 : word) = Some W_d5450.
Proof. vm_refl. Qed.
Lemma D_d5450 : decode_any W_d5450 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5454 : bv 32 := 0x00090613.
Lemma F_d5454 : fetch_word Plain.M.loaded_segments (0xd5488 : word) = Some W_d5454.
Proof. vm_refl. Qed.
Lemma D_d5454 : decode_any W_d5454 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5458 : bv 32 := 0x00000073.
Lemma F_d5458 : fetch_word Plain.M.loaded_segments (0xd548c : word) = Some W_d5458.
Proof. vm_refl. Qed.

Lemma E_d5458 : is_ecall W_d5458 = true.
Proof. reflexivity. Qed.

Definition W_d545c : bv 32 := 0xe2dfa0ef.
Lemma F_d545c : fetch_word Plain.M.loaded_segments (0xd5490 : word) = Some W_d545c.
Proof. vm_refl. Qed.
Lemma D_d545c : decode_any W_d545c = Some (Jal 1 2076204, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5460 : bv 32 := 0x000a0993.
Lemma F_d5460 : fetch_word Plain.M.loaded_segments (0xd5494 : word) = Some W_d5460.
Proof. vm_refl. Qed.
Lemma D_d5460 : decode_any W_d5460 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5464 : bv 32 := 0xf7650ce3.
Lemma F_d5464 : fetch_word Plain.M.loaded_segments (0xd5498 : word) = Some W_d5464.
Proof. vm_refl. Qed.
Lemma D_d5464 : decode_any W_d5464 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5468 : bv 32 := 0x02054c63.
Lemma F_d5468 : fetch_word Plain.M.loaded_segments (0xd549c : word) = Some W_d5468.
Proof. vm_refl. Qed.
Lemma D_d5468 : decode_any W_d5468 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_d546c : bv 32 := 0x0089b583.
Lemma F_d546c : fetch_word Plain.M.loaded_segments (0xd54a0 : word) = Some W_d546c.
Proof. vm_refl. Qed.
Lemma D_d546c : decode_any W_d546c = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5470 : bv 32 := 0x00a5b633.
Lemma F_d5470 : fetch_word Plain.M.loaded_segments (0xd54a4 : word) = Some W_d5470.
Proof. vm_refl. Qed.
Lemma D_d5470 : decode_any W_d5470 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5474 : bv 32 := 0x00461a13.
Lemma F_d5474 : fetch_word Plain.M.loaded_segments (0xd54a8 : word) = Some W_d5474.
Proof. vm_refl. Qed.
Lemma D_d5474 : decode_any W_d5474 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5478 : bv 32 := 0x01498a33.
Lemma F_d5478 : fetch_word Plain.M.loaded_segments (0xd54ac : word) = Some W_d5478.
Proof. vm_refl. Qed.
Lemma D_d5478 : decode_any W_d5478 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_d547c : bv 32 := 0x000a3703.
Lemma F_d547c : fetch_word Plain.M.loaded_segments (0xd54b0 : word) = Some W_d547c.
Proof. vm_refl. Qed.
Lemma D_d547c : decode_any W_d547c = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5480 : bv 32 := 0x40c006b3.
Lemma F_d5480 : fetch_word Plain.M.loaded_segments (0xd54b4 : word) = Some W_d5480.
Proof. vm_refl. Qed.
Lemma D_d5480 : decode_any W_d5480 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5484 : bv 32 := 0x00b6f6b3.
Lemma F_d5484 : fetch_word Plain.M.loaded_segments (0xd54b8 : word) = Some W_d5484.
Proof. vm_refl. Qed.
Lemma D_d5484 : decode_any W_d5484 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5488 : bv 32 := 0x40d506b3.
Lemma F_d5488 : fetch_word Plain.M.loaded_segments (0xd54bc : word) = Some W_d5488.
Proof. vm_refl. Qed.
Lemma D_d5488 : decode_any W_d5488 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_d548c : bv 32 := 0x00d70733.
Lemma F_d548c : fetch_word Plain.M.loaded_segments (0xd54c0 : word) = Some W_d548c.
Proof. vm_refl. Qed.
Lemma D_d548c : decode_any W_d548c = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5490 : bv 32 := 0x00ea3023.
Lemma F_d5490 : fetch_word Plain.M.loaded_segments (0xd54c4 : word) = Some W_d5490.
Proof. vm_refl. Qed.
Lemma D_d5490 : decode_any W_d5490 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5494 : bv 32 := 0xf8a5fce3.
Lemma F_d5494 : fetch_word Plain.M.loaded_segments (0xd54c8 : word) = Some W_d5494.
Proof. vm_refl. Qed.
Lemma D_d5494 : decode_any W_d5494 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_d5498 : bv 32 := 0x01800713.
Lemma F_d5498 : fetch_word Plain.M.loaded_segments (0xd54cc : word) = Some W_d5498.
Proof. vm_refl. Qed.
Lemma D_d5498 : decode_any W_d5498 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d549c : bv 32 := 0xf95ff06f.
Lemma F_d549c : fetch_word Plain.M.loaded_segments (0xd54d0 : word) = Some W_d549c.
Proof. vm_refl. Qed.
Lemma D_d549c : decode_any W_d549c = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

Definition W_d54e0 : bv 32 := 0x00008067.
Lemma F_d54e0 : fetch_word Plain.M.loaded_segments (0xd5514 : word) = Some W_d54e0.
Proof. vm_refl. Qed.
Lemma D_d54e0 : decode_any W_d54e0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

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

Definition W_982fc : bv 32 := 0xfc010113.
Lemma F_982fc : fetch_word Asan.M.loaded_segments (0x9834c : word) = Some W_982fc.
Proof. vm_refl. Qed.
Lemma D_982fc : decode_any W_982fc = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_98300 : bv 32 := 0x02113c23.
Lemma F_98300 : fetch_word Asan.M.loaded_segments (0x98350 : word) = Some W_98300.
Proof. vm_refl. Qed.
Lemma D_98300 : decode_any W_98300 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_98304 : bv 32 := 0x02813823.
Lemma F_98304 : fetch_word Asan.M.loaded_segments (0x98354 : word) = Some W_98304.
Proof. vm_refl. Qed.
Lemma D_98304 : decode_any W_98304 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_98308 : bv 32 := 0x02913423.
Lemma F_98308 : fetch_word Asan.M.loaded_segments (0x98358 : word) = Some W_98308.
Proof. vm_refl. Qed.
Lemma D_98308 : decode_any W_98308 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9830c : bv 32 := 0x03213023.
Lemma F_9830c : fetch_word Asan.M.loaded_segments (0x9835c : word) = Some W_9830c.
Proof. vm_refl. Qed.
Lemma D_9830c : decode_any W_9830c = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_98310 : bv 32 := 0x01313c23.
Lemma F_98310 : fetch_word Asan.M.loaded_segments (0x98360 : word) = Some W_98310.
Proof. vm_refl. Qed.
Lemma D_98310 : decode_any W_98310 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_98314 : bv 32 := 0x01413823.
Lemma F_98314 : fetch_word Asan.M.loaded_segments (0x98364 : word) = Some W_98314.
Proof. vm_refl. Qed.
Lemma D_98314 : decode_any W_98314 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_98318 : bv 32 := 0x01513423.
Lemma F_98318 : fetch_word Asan.M.loaded_segments (0x98368 : word) = Some W_98318.
Proof. vm_refl. Qed.
Lemma D_98318 : decode_any W_98318 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9831c : bv 32 := 0x00058993.
Lemma F_9831c : fetch_word Asan.M.loaded_segments (0x9836c : word) = Some W_9831c.
Proof. vm_refl. Qed.
Lemma D_9831c : decode_any W_9831c = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98320 : bv 32 := 0x0085aa03.
Lemma F_98320 : fetch_word Asan.M.loaded_segments (0x98370 : word) = Some W_98320.
Proof. vm_refl. Qed.
Lemma D_98320 : decode_any W_98320 = Some (Load SZ4 true 20 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_98324 : bv 32 := 0x00c5aa83.
Lemma F_98324 : fetch_word Asan.M.loaded_segments (0x98374 : word) = Some W_98324.
Proof. vm_refl. Qed.
Lemma D_98324 : decode_any W_98324 = Some (Load SZ4 true 21 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_98328 : bv 32 := 0x015a65b3.
Lemma F_98328 : fetch_word Asan.M.loaded_segments (0x98378 : word) = Some W_98328.
Proof. vm_refl. Qed.
Lemma D_98328 : decode_any W_98328 = Some (Op ALU_OR 11 20 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_9832c : bv 32 := 0x00059663.
Lemma F_9832c : fetch_word Asan.M.loaded_segments (0x9837c : word) = Some W_9832c.
Proof. vm_refl. Qed.
Lemma D_9832c : decode_any W_9832c = Some (Branch BC_NE 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_98338 : bv 32 := 0x00050493.
Lemma F_98338 : fetch_word Asan.M.loaded_segments (0x98388 : word) = Some W_98338.
Proof. vm_refl. Qed.
Lemma D_98338 : decode_any W_98338 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9833c : bv 32 := 0x10000513.
Lemma F_9833c : fetch_word Asan.M.loaded_segments (0x9838c : word) = Some W_9833c.
Proof. vm_refl. Qed.
Lemma D_9833c : decode_any W_9833c = Some (OpImm ALU_ADD 10 0 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_98340 : bv 32 := 0x0aaafe63.
Lemma F_98340 : fetch_word Asan.M.loaded_segments (0x98390 : word) = Some W_98340.
Proof. vm_refl. Qed.
Lemma D_98340 : decode_any W_98340 = Some (Branch BC_GEU 21 10 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_98344 : bv 32 := 0x00060413.
Lemma F_98344 : fetch_word Asan.M.loaded_segments (0x98394 : word) = Some W_98344.
Proof. vm_refl. Qed.
Lemma D_98344 : decode_any W_98344 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98348 : bv 32 := 0x0ff00513.
Lemma F_98348 : fetch_word Asan.M.loaded_segments (0x98398 : word) = Some W_98348.
Proof. vm_refl. Qed.
Lemma D_98348 : decode_any W_98348 = Some (OpImm ALU_ADD 10 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_9834c : bv 32 := 0x00aa6463.
Lemma F_9834c : fetch_word Asan.M.loaded_segments (0x9839c : word) = Some W_9834c.
Proof. vm_refl. Qed.
Lemma D_9834c : decode_any W_9834c = Some (Branch BC_LTU 20 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_98354 : bv 32 := 0x00013023.
Lemma F_98354 : fetch_word Asan.M.loaded_segments (0x983a4 : word) = Some W_98354.
Proof. vm_refl. Qed.
Lemma D_98354 : decode_any W_98354 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98358 : bv 32 := 0x00043023.
Lemma F_98358 : fetch_word Asan.M.loaded_segments (0x983a8 : word) = Some W_98358.
Proof. vm_refl. Qed.
Lemma D_98358 : decode_any W_98358 = Some (Store SZ8 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9835c : bv 32 := 0x001a0913.
Lemma F_9835c : fetch_word Asan.M.loaded_segments (0x983ac : word) = Some W_9835c.
Proof. vm_refl. Qed.
Lemma D_9835c : decode_any W_9835c = Some (OpImm ALU_ADD 18 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_98360 : bv 32 := 0x00010613.
Lemma F_98360 : fetch_word Asan.M.loaded_segments (0x983b0 : word) = Some W_98360.
Proof. vm_refl. Qed.
Lemma D_98360 : decode_any W_98360 = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98364 : bv 32 := 0x00048513.
Lemma F_98364 : fetch_word Asan.M.loaded_segments (0x983b4 : word) = Some W_98364.
Proof. vm_refl. Qed.
Lemma D_98364 : decode_any W_98364 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98368 : bv 32 := 0x00090593.
Lemma F_98368 : fetch_word Asan.M.loaded_segments (0x983b8 : word) = Some W_98368.
Proof. vm_refl. Qed.
Lemma D_98368 : decode_any W_98368 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9836c : bv 32 := 0x00040693.
Lemma F_9836c : fetch_word Asan.M.loaded_segments (0x983bc : word) = Some W_9836c.
Proof. vm_refl. Qed.
Lemma D_9836c : decode_any W_9836c = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98370 : bv 32 := 0x0b0000ef.
Lemma F_98370 : fetch_word Asan.M.loaded_segments (0x983c0 : word) = Some W_98370.
Proof. vm_refl. Qed.
Lemma D_98370 : decode_any W_98370 = Some (Jal 1 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_98374 : bv 32 := 0x06050263.
Lemma F_98374 : fetch_word Asan.M.loaded_segments (0x983c4 : word) = Some W_98374.
Proof. vm_refl. Qed.
Lemma D_98374 : decode_any W_98374 = Some (Branch BC_EQ 10 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_98378 : bv 32 := 0x008a961b.
Lemma F_98378 : fetch_word Asan.M.loaded_segments (0x983c8 : word) = Some W_98378.
Proof. vm_refl. Qed.
Lemma D_98378 : decode_any W_98378 = Some (ShiftImm32 ALU_SLL 12 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9837c : bv 32 := 0x0009b583.
Lemma F_9837c : fetch_word Asan.M.loaded_segments (0x983cc : word) = Some W_9837c.
Proof. vm_refl. Qed.
Lemma D_9837c : decode_any W_9837c = Some (Load SZ8 true 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98380 : bv 32 := 0x01466633.
Lemma F_98380 : fetch_word Asan.M.loaded_segments (0x983d0 : word) = Some W_98380.
Proof. vm_refl. Qed.
Lemma D_98380 : decode_any W_98380 = Some (Op ALU_OR 12 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_98384 : bv 32 := 0x00c53023.
Lemma F_98384 : fetch_word Asan.M.loaded_segments (0x983d4 : word) = Some W_98384.
Proof. vm_refl. Qed.
Lemma D_98384 : decode_any W_98384 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98388 : bv 32 := 0x00850513.
Lemma F_98388 : fetch_word Asan.M.loaded_segments (0x983d8 : word) = Some W_98388.
Proof. vm_refl. Qed.
Lemma D_98388 : decode_any W_98388 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9838c : bv 32 := 0x003a1613.
Lemma F_9838c : fetch_word Asan.M.loaded_segments (0x983dc : word) = Some W_9838c.
Proof. vm_refl. Qed.
Lemma D_9838c : decode_any W_9838c = Some (ShiftImm ALU_SLL 12 20 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_98390 : bv 32 := 0x989f30ef.
Lemma F_98390 : fetch_word Asan.M.loaded_segments (0x983e0 : word) = Some W_98390.
Proof. vm_refl. Qed.
Lemma D_98390 : decode_any W_98390 = Some (Jal 1 2046344, 4%Z).
Proof. vm_refl. Qed.

Definition W_98394 : bv 32 := 0x00013503.
Lemma F_98394 : fetch_word Asan.M.loaded_segments (0x983e4 : word) = Some W_98394.
Proof. vm_refl. Qed.
Lemma D_98394 : decode_any W_98394 = Some (Load SZ8 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98398 : bv 32 := 0x01055513.
Lemma F_98398 : fetch_word Asan.M.loaded_segments (0x983e8 : word) = Some W_98398.
Proof. vm_refl. Qed.
Lemma D_98398 : decode_any W_98398 = Some (ShiftImm ALU_SRL 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9839c : bv 32 := 0xff057513.
Lemma F_9839c : fetch_word Asan.M.loaded_segments (0x983ec : word) = Some W_9839c.
Proof. vm_refl. Qed.
Lemma D_9839c : decode_any W_9839c = Some (OpImm ALU_AND 10 10 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_983a0 : bv 32 := 0x00a48533.
Lemma F_983a0 : fetch_word Asan.M.loaded_segments (0x983f0 : word) = Some W_983a0.
Proof. vm_refl. Qed.
Lemma D_983a0 : decode_any W_983a0 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_983a4 : bv 32 := 0x01850513.
Lemma F_983a4 : fetch_word Asan.M.loaded_segments (0x983f4 : word) = Some W_983a4.
Proof. vm_refl. Qed.
Lemma D_983a4 : decode_any W_983a4 = Some (OpImm ALU_ADD 10 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_983a8 : bv 32 := 0x0325252f.
Lemma F_983a8 : fetch_word Asan.M.loaded_segments (0x983f8 : word) = Some W_983a8.
Proof. vm_refl. Qed.
Lemma D_983a8 : decode_any W_983a8 = Some (Amo AMO_ADD AW false true 10 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_983ac : bv 32 := 0x001005b7.
Lemma F_983ac : fetch_word Asan.M.loaded_segments (0x983fc : word) = Some W_983ac.
Proof. vm_refl. Qed.
Lemma D_983ac : decode_any W_983ac = Some (Lui 11 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_983b0 : bv 32 := 0x02051513.
Lemma F_983b0 : fetch_word Asan.M.loaded_segments (0x98400 : word) = Some W_983b0.
Proof. vm_refl. Qed.
Lemma D_983b0 : decode_any W_983b0 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_983b4 : bv 32 := 0x02055513.
Lemma F_983b4 : fetch_word Asan.M.loaded_segments (0x98404 : word) = Some W_983b4.
Proof. vm_refl. Qed.
Lemma D_983b4 : decode_any W_983b4 = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_983b8 : bv 32 := 0x00a90533.
Lemma F_983b8 : fetch_word Asan.M.loaded_segments (0x98408 : word) = Some W_983b8.
Proof. vm_refl. Qed.
Lemma D_983b8 : decode_any W_983b8 = Some (Op ALU_ADD 10 18 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_983bc : bv 32 := 0x00043603.
Lemma F_983bc : fetch_word Asan.M.loaded_segments (0x9840c : word) = Some W_983bc.
Proof. vm_refl. Qed.
Lemma D_983bc : decode_any W_983bc = Some (Load SZ8 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_983c0 : bv 32 := 0x00b54533.
Lemma F_983c0 : fetch_word Asan.M.loaded_segments (0x98410 : word) = Some W_983c0.
Proof. vm_refl. Qed.
Lemma D_983c0 : decode_any W_983c0 = Some (Op ALU_XOR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_983c4 : bv 32 := 0x00012583.
Lemma F_983c4 : fetch_word Asan.M.loaded_segments (0x98414 : word) = Some W_983c4.
Proof. vm_refl. Qed.
Lemma D_983c4 : decode_any W_983c4 = Some (Load SZ4 true 11 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_983c8 : bv 32 := 0x00153513.
Lemma F_983c8 : fetch_word Asan.M.loaded_segments (0x98418 : word) = Some W_983c8.
Proof. vm_refl. Qed.
Lemma D_983c8 : decode_any W_983c8 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_983cc : bv 32 := 0x00a60533.
Lemma F_983cc : fetch_word Asan.M.loaded_segments (0x9841c : word) = Some W_983cc.
Proof. vm_refl. Qed.
Lemma D_983cc : decode_any W_983cc = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_983d0 : bv 32 := 0x00a43023.
Lemma F_983d0 : fetch_word Asan.M.loaded_segments (0x98420 : word) = Some W_983d0.
Proof. vm_refl. Qed.
Lemma D_983d0 : decode_any W_983d0 = Some (Store SZ8 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_983d4 : bv 32 := 0x0015851b.
Lemma F_983d4 : fetch_word Asan.M.loaded_segments (0x98424 : word) = Some W_983d4.
Proof. vm_refl. Qed.
Lemma D_983d4 : decode_any W_983d4 = Some (OpImm32 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_983d8 : bv 32 := 0x03813083.
Lemma F_983d8 : fetch_word Asan.M.loaded_segments (0x98428 : word) = Some W_983d8.
Proof. vm_refl. Qed.
Lemma D_983d8 : decode_any W_983d8 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_983dc : bv 32 := 0x03013403.
Lemma F_983dc : fetch_word Asan.M.loaded_segments (0x9842c : word) = Some W_983dc.
Proof. vm_refl. Qed.
Lemma D_983dc : decode_any W_983dc = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_983e0 : bv 32 := 0x02813483.
Lemma F_983e0 : fetch_word Asan.M.loaded_segments (0x98430 : word) = Some W_983e0.
Proof. vm_refl. Qed.
Lemma D_983e0 : decode_any W_983e0 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_983e4 : bv 32 := 0x02013903.
Lemma F_983e4 : fetch_word Asan.M.loaded_segments (0x98434 : word) = Some W_983e4.
Proof. vm_refl. Qed.
Lemma D_983e4 : decode_any W_983e4 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_983e8 : bv 32 := 0x01813983.
Lemma F_983e8 : fetch_word Asan.M.loaded_segments (0x98438 : word) = Some W_983e8.
Proof. vm_refl. Qed.
Lemma D_983e8 : decode_any W_983e8 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_983ec : bv 32 := 0x01013a03.
Lemma F_983ec : fetch_word Asan.M.loaded_segments (0x9843c : word) = Some W_983ec.
Proof. vm_refl. Qed.
Lemma D_983ec : decode_any W_983ec = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_983f0 : bv 32 := 0x00813a83.
Lemma F_983f0 : fetch_word Asan.M.loaded_segments (0x98440 : word) = Some W_983f0.
Proof. vm_refl. Qed.
Lemma D_983f0 : decode_any W_983f0 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_983f4 : bv 32 := 0x04010113.
Lemma F_983f4 : fetch_word Asan.M.loaded_segments (0x98444 : word) = Some W_983f4.
Proof. vm_refl. Qed.
Lemma D_983f4 : decode_any W_983f4 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_983f8 : bv 32 := 0x00008067.
Lemma F_983f8 : fetch_word Asan.M.loaded_segments (0x98448 : word) = Some W_983f8.
Proof. vm_refl. Qed.
Lemma D_983f8 : decode_any W_983f8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98420 : bv 32 := 0xff010113.
Lemma F_98420 : fetch_word Asan.M.loaded_segments (0x98470 : word) = Some W_98420.
Proof. vm_refl. Qed.
Lemma D_98420 : decode_any W_98420 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_98424 : bv 32 := 0x00113423.
Lemma F_98424 : fetch_word Asan.M.loaded_segments (0x98474 : word) = Some W_98424.
Proof. vm_refl. Qed.
Lemma D_98424 : decode_any W_98424 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_98428 : bv 32 := 0x00813023.
Lemma F_98428 : fetch_word Asan.M.loaded_segments (0x98478 : word) = Some W_98428.
Proof. vm_refl. Qed.
Lemma D_98428 : decode_any W_98428 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9842c : bv 32 := 0x00058793.
Lemma F_9842c : fetch_word Asan.M.loaded_segments (0x9847c : word) = Some W_9842c.
Proof. vm_refl. Qed.
Lemma D_9842c : decode_any W_9842c = Some (OpImm ALU_ADD 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98430 : bv 32 := 0x00050593.
Lemma F_98430 : fetch_word Asan.M.loaded_segments (0x98480 : word) = Some W_98430.
Proof. vm_refl. Qed.
Lemma D_98430 : decode_any W_98430 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98434 : bv 32 := 0x00f5342f.
Lemma F_98434 : fetch_word Asan.M.loaded_segments (0x98484 : word) = Some W_98434.
Proof. vm_refl. Qed.
Lemma D_98434 : decode_any W_98434 = Some (Amo AMO_ADD AD false false 8 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_98438 : bv 32 := 0xfff78513.
Lemma F_98438 : fetch_word Asan.M.loaded_segments (0x98488 : word) = Some W_98438.
Proof. vm_refl. Qed.
Lemma D_98438 : decode_any W_98438 = Some (OpImm ALU_ADD 10 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_9843c : bv 32 := 0x01445293.
Lemma F_9843c : fetch_word Asan.M.loaded_segments (0x9848c : word) = Some W_9843c.
Proof. vm_refl. Qed.
Lemma D_9843c : decode_any W_9843c = Some (ShiftImm ALU_SRL 5 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_98440 : bv 32 := 0x00850733.
Lemma F_98440 : fetch_word Asan.M.loaded_segments (0x98490 : word) = Some W_98440.
Proof. vm_refl. Qed.
Lemma D_98440 : decode_any W_98440 = Some (Op ALU_ADD 14 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_98444 : bv 32 := 0x01475313.
Lemma F_98444 : fetch_word Asan.M.loaded_segments (0x98494 : word) = Some W_98444.
Proof. vm_refl. Qed.
Lemma D_98444 : decode_any W_98444 = Some (ShiftImm ALU_SRL 6 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_98448 : bv 32 := 0x04629863.
Lemma F_98448 : fetch_word Asan.M.loaded_segments (0x98498 : word) = Some W_98448.
Proof. vm_refl. Qed.
Lemma D_98448 : decode_any W_98448 = Some (Branch BC_NE 5 6 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_9844c : bv 32 := 0x02045513.
Lemma F_9844c : fetch_word Asan.M.loaded_segments (0x9849c : word) = Some W_9844c.
Proof. vm_refl. Qed.
Lemma D_9844c : decode_any W_9844c = Some (ShiftImm ALU_SRL 10 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_98450 : bv 32 := 0x00050c63.
Lemma F_98450 : fetch_word Asan.M.loaded_segments (0x984a0 : word) = Some W_98450.
Proof. vm_refl. Qed.
Lemma D_98450 : decode_any W_98450 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_98468 : bv 32 := 0x00863023.
Lemma F_98468 : fetch_word Asan.M.loaded_segments (0x984b8 : word) = Some W_98468.
Proof. vm_refl. Qed.
Lemma D_98468 : decode_any W_98468 = Some (Store SZ8 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9846c : bv 32 := 0x00429613.
Lemma F_9846c : fetch_word Asan.M.loaded_segments (0x984bc : word) = Some W_9846c.
Proof. vm_refl. Qed.
Lemma D_9846c : decode_any W_9846c = Some (ShiftImm ALU_SLL 12 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_98470 : bv 32 := 0x00c58633.
Lemma F_98470 : fetch_word Asan.M.loaded_segments (0x984c0 : word) = Some W_98470.
Proof. vm_refl. Qed.
Lemma D_98470 : decode_any W_98470 = Some (Op ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_98474 : bv 32 := 0x01063503.
Lemma F_98474 : fetch_word Asan.M.loaded_segments (0x984c4 : word) = Some W_98474.
Proof. vm_refl. Qed.
Lemma D_98474 : decode_any W_98474 = Some (Load SZ8 true 10 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_98478 : bv 32 := 0x0a050a63.
Lemma F_98478 : fetch_word Asan.M.loaded_segments (0x984c8 : word) = Some W_98478.
Proof. vm_refl. Qed.
Lemma D_98478 : decode_any W_98478 = Some (Branch BC_EQ 10 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_9847c : bv 32 := 0x02c41413.
Lemma F_9847c : fetch_word Asan.M.loaded_segments (0x984cc : word) = Some W_9847c.
Proof. vm_refl. Qed.
Lemma D_9847c : decode_any W_9847c = Some (ShiftImm ALU_SLL 8 8 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_98480 : bv 32 := 0x02945413.
Lemma F_98480 : fetch_word Asan.M.loaded_segments (0x984d0 : word) = Some W_98480.
Proof. vm_refl. Qed.
Lemma D_98480 : decode_any W_98480 = Some (ShiftImm ALU_SRL 8 8 41, 4%Z).
Proof. vm_refl. Qed.

Definition W_98484 : bv 32 := 0x00850533.
Lemma F_98484 : fetch_word Asan.M.loaded_segments (0x984d4 : word) = Some W_98484.
Proof. vm_refl. Qed.
Lemma D_98484 : decode_any W_98484 = Some (Op ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_98488 : bv 32 := 0x00813083.
Lemma F_98488 : fetch_word Asan.M.loaded_segments (0x984d8 : word) = Some W_98488.
Proof. vm_refl. Qed.
Lemma D_98488 : decode_any W_98488 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9848c : bv 32 := 0x00013403.
Lemma F_9848c : fetch_word Asan.M.loaded_segments (0x984dc : word) = Some W_9848c.
Proof. vm_refl. Qed.
Lemma D_9848c : decode_any W_9848c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98490 : bv 32 := 0x01010113.
Lemma F_98490 : fetch_word Asan.M.loaded_segments (0x984e0 : word) = Some W_98490.
Proof. vm_refl. Qed.
Lemma D_98490 : decode_any W_98490 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_98494 : bv 32 := 0x00008067.
Lemma F_98494 : fetch_word Asan.M.loaded_segments (0x984e4 : word) = Some W_98494.
Proof. vm_refl. Qed.
Lemma D_98494 : decode_any W_98494 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

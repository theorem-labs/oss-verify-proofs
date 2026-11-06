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

Definition W_94368 : bv 32 := 0x00a80833.
Lemma F_94368 : fetch_word Asan.M.loaded_segments (0x94368 : word) = Some W_94368.
Proof. vm_refl. Qed.
Lemma D_94368 : decode_any W_94368 = Some (Op ALU_ADD 16 16 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9436c : bv 32 := 0x011a08b3.
Lemma F_9436c : fetch_word Asan.M.loaded_segments (0x9436c : word) = Some W_9436c.
Proof. vm_refl. Qed.
Lemma D_9436c : decode_any W_9436c = Some (Op ALU_ADD 17 20 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_94370 : bv 32 := 0x00060513.
Lemma F_94370 : fetch_word Asan.M.loaded_segments (0x94370 : word) = Some W_94370.
Proof. vm_refl. Qed.
Lemma D_94370 : decode_any W_94370 = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94374 : bv 32 := 0x00d88333.
Lemma F_94374 : fetch_word Asan.M.loaded_segments (0x94374 : word) = Some W_94374.
Proof. vm_refl. Qed.
Lemma D_94374 : decode_any W_94374 = Some (Op ALU_ADD 6 17 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_94378 : bv 32 := 0x00034583.
Lemma F_94378 : fetch_word Asan.M.loaded_segments (0x94378 : word) = Some W_94378.
Proof. vm_refl. Qed.
Lemma D_94378 : decode_any W_94378 = Some (Load SZ1 false 11 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9437c : bv 32 := 0x0a059263.
Lemma F_9437c : fetch_word Asan.M.loaded_segments (0x9437c : word) = Some W_9437c.
Proof. vm_refl. Qed.
Lemma D_9437c : decode_any W_9437c = Some (Branch BC_NE 11 0 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_94380 : bv 32 := 0x00063583.
Lemma F_94380 : fetch_word Asan.M.loaded_segments (0x94380 : word) = Some W_94380.
Proof. vm_refl. Qed.
Lemma D_94380 : decode_any W_94380 = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94384 : bv 32 := 0x0095d2b3.
Lemma F_94384 : fetch_word Asan.M.loaded_segments (0x94384 : word) = Some W_94384.
Proof. vm_refl. Qed.
Lemma D_94384 : decode_any W_94384 = Some (Op ALU_SRL 5 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_94388 : bv 32 := 0x00563023.
Lemma F_94388 : fetch_word Asan.M.loaded_segments (0x94388 : word) = Some W_94388.
Proof. vm_refl. Qed.
Lemma D_94388 : decode_any W_94388 = Some (Store SZ8 12 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9438c : bv 32 := 0x02f6f863.
Lemma F_9438c : fetch_word Asan.M.loaded_segments (0x9438c : word) = Some W_9438c.
Proof. vm_refl. Qed.
Lemma D_9438c : decode_any W_9438c = Some (Branch BC_GEU 13 15 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_94390 : bv 32 := 0x00850593.
Lemma F_94390 : fetch_word Asan.M.loaded_segments (0x94390 : word) = Some W_94390.
Proof. vm_refl. Qed.
Lemma D_94390 : decode_any W_94390 = Some (OpImm ALU_ADD 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_94394 : bv 32 := 0x0035d393.
Lemma F_94394 : fetch_word Asan.M.loaded_segments (0x94394 : word) = Some W_94394.
Proof. vm_refl. Qed.
Lemma D_94394 : decode_any W_94394 = Some (ShiftImm ALU_SRL 7 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_94398 : bv 32 := 0x014383b3.
Lemma F_94398 : fetch_word Asan.M.loaded_segments (0x94398 : word) = Some W_94398.
Proof. vm_refl. Qed.
Lemma D_94398 : decode_any W_94398 = Some (Op ALU_ADD 7 7 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_9439c : bv 32 := 0x0003c383.
Lemma F_9439c : fetch_word Asan.M.loaded_segments (0x9439c : word) = Some W_9439c.
Proof. vm_refl. Qed.
Lemma D_9439c : decode_any W_9439c = Some (Load SZ1 false 7 7 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_943a0 : bv 32 := 0x08039263.
Lemma F_943a0 : fetch_word Asan.M.loaded_segments (0x943a0 : word) = Some W_943a0.
Proof. vm_refl. Qed.
Lemma D_943a0 : decode_any W_943a0 = Some (Branch BC_NE 7 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_943a4 : bv 32 := 0x00034583.
Lemma F_943a4 : fetch_word Asan.M.loaded_segments (0x943a4 : word) = Some W_943a4.
Proof. vm_refl. Qed.
Lemma D_943a4 : decode_any W_943a4 = Some (Load SZ1 false 11 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_943a8 : bv 32 := 0x08059263.
Lemma F_943a8 : fetch_word Asan.M.loaded_segments (0x943a8 : word) = Some W_943a8.
Proof. vm_refl. Qed.
Lemma D_943a8 : decode_any W_943a8 = Some (Branch BC_NE 11 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_943ac : bv 32 := 0x00863583.
Lemma F_943ac : fetch_word Asan.M.loaded_segments (0x943ac : word) = Some W_943ac.
Proof. vm_refl. Qed.
Lemma D_943ac : decode_any W_943ac = Some (Load SZ8 true 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_943b0 : bv 32 := 0x00e595b3.
Lemma F_943b0 : fetch_word Asan.M.loaded_segments (0x943b0 : word) = Some W_943b0.
Proof. vm_refl. Qed.
Lemma D_943b0 : decode_any W_943b0 = Some (Op ALU_SLL 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_943b4 : bv 32 := 0x0055e5b3.
Lemma F_943b4 : fetch_word Asan.M.loaded_segments (0x943b4 : word) = Some W_943b4.
Proof. vm_refl. Qed.
Lemma D_943b4 : decode_any W_943b4 = Some (Op ALU_OR 11 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_943b8 : bv 32 := 0x00b63023.
Lemma F_943b8 : fetch_word Asan.M.loaded_segments (0x943b8 : word) = Some W_943b8.
Proof. vm_refl. Qed.
Lemma D_943b8 : decode_any W_943b8 = Some (Store SZ8 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_943bc : bv 32 := 0x00850513.
Lemma F_943bc : fetch_word Asan.M.loaded_segments (0x943bc : word) = Some W_943bc.
Proof. vm_refl. Qed.
Lemma D_943bc : decode_any W_943bc = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_943c0 : bv 32 := 0x00168693.
Lemma F_943c0 : fetch_word Asan.M.loaded_segments (0x943c0 : word) = Some W_943c0.
Proof. vm_refl. Qed.
Lemma D_943c0 : decode_any W_943c0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_943c4 : bv 32 := 0x00860613.
Lemma F_943c4 : fetch_word Asan.M.loaded_segments (0x943c4 : word) = Some W_943c4.
Proof. vm_refl. Qed.
Lemma D_943c4 : decode_any W_943c4 = Some (OpImm ALU_ADD 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_943c8 : bv 32 := 0xfad816e3.
Lemma F_943c8 : fetch_word Asan.M.loaded_segments (0x943c8 : word) = Some W_943c8.
Proof. vm_refl. Qed.
Lemma D_943c8 : decode_any W_943c8 = Some (Branch BC_NE 16 13 8108, 4%Z).
Proof. vm_refl. Qed.

Definition W_943cc : bv 32 := 0x00040513.
Lemma F_943cc : fetch_word Asan.M.loaded_segments (0x943cc : word) = Some W_943cc.
Proof. vm_refl. Qed.
Lemma D_943cc : decode_any W_943cc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_943d0 : bv 32 := 0xbb0fc0ef.
Lemma F_943d0 : fetch_word Asan.M.loaded_segments (0x943d0 : word) = Some W_943d0.
Proof. vm_refl. Qed.
Lemma D_943d0 : decode_any W_943d0 = Some (Jal 1 2081712, 4%Z).
Proof. vm_refl. Qed.

Definition W_943d4 : bv 32 := 0x00040513.
Lemma F_943d4 : fetch_word Asan.M.loaded_segments (0x943d4 : word) = Some W_943d4.
Proof. vm_refl. Qed.
Lemma D_943d4 : decode_any W_943d4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_943d8 : bv 32 := 0x03813083.
Lemma F_943d8 : fetch_word Asan.M.loaded_segments (0x943d8 : word) = Some W_943d8.
Proof. vm_refl. Qed.
Lemma D_943d8 : decode_any W_943d8 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_943dc : bv 32 := 0x03013403.
Lemma F_943dc : fetch_word Asan.M.loaded_segments (0x943dc : word) = Some W_943dc.
Proof. vm_refl. Qed.
Lemma D_943dc : decode_any W_943dc = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_943e0 : bv 32 := 0x02813483.
Lemma F_943e0 : fetch_word Asan.M.loaded_segments (0x943e0 : word) = Some W_943e0.
Proof. vm_refl. Qed.
Lemma D_943e0 : decode_any W_943e0 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_943e4 : bv 32 := 0x02013903.
Lemma F_943e4 : fetch_word Asan.M.loaded_segments (0x943e4 : word) = Some W_943e4.
Proof. vm_refl. Qed.
Lemma D_943e4 : decode_any W_943e4 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_943e8 : bv 32 := 0x01813983.
Lemma F_943e8 : fetch_word Asan.M.loaded_segments (0x943e8 : word) = Some W_943e8.
Proof. vm_refl. Qed.
Lemma D_943e8 : decode_any W_943e8 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_943ec : bv 32 := 0x01013a03.
Lemma F_943ec : fetch_word Asan.M.loaded_segments (0x943ec : word) = Some W_943ec.
Proof. vm_refl. Qed.
Lemma D_943ec : decode_any W_943ec = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_943f0 : bv 32 := 0x00813a83.
Lemma F_943f0 : fetch_word Asan.M.loaded_segments (0x943f0 : word) = Some W_943f0.
Proof. vm_refl. Qed.
Lemma D_943f0 : decode_any W_943f0 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_943f4 : bv 32 := 0x00013b03.
Lemma F_943f4 : fetch_word Asan.M.loaded_segments (0x943f4 : word) = Some W_943f4.
Proof. vm_refl. Qed.
Lemma D_943f4 : decode_any W_943f4 = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_943f8 : bv 32 := 0x04010113.
Lemma F_943f8 : fetch_word Asan.M.loaded_segments (0x943f8 : word) = Some W_943f8.
Proof. vm_refl. Qed.
Lemma D_943f8 : decode_any W_943f8 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_943fc : bv 32 := 0x00008067.
Lemma F_943fc : fetch_word Asan.M.loaded_segments (0x943fc : word) = Some W_943fc.
Proof. vm_refl. Qed.
Lemma D_943fc : decode_any W_943fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94400 : bv 32 := 0x00747593.
Lemma F_94400 : fetch_word Asan.M.loaded_segments (0x94400 : word) = Some W_94400.
Proof. vm_refl. Qed.
Lemma D_94400 : decode_any W_94400 = Some (OpImm ALU_AND 11 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_94404 : bv 32 := 0xe8a5c0e3.
Lemma F_94404 : fetch_word Asan.M.loaded_segments (0x94404 : word) = Some W_94404.
Proof. vm_refl. Qed.
Lemma D_94404 : decode_any W_94404 = Some (Branch BC_LT 11 10 7808, 4%Z).
Proof. vm_refl. Qed.

Definition W_94408 : bv 32 := 0x00040513.
Lemma F_94408 : fetch_word Asan.M.loaded_segments (0x94408 : word) = Some W_94408.
Proof. vm_refl. Qed.
Lemma D_94408 : decode_any W_94408 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9440c : bv 32 := 0xce1d10ef.
Lemma F_9440c : fetch_word Asan.M.loaded_segments (0x9440c : word) = Some W_9440c.
Proof. vm_refl. Qed.
Lemma D_9440c : decode_any W_9440c = Some (Jal 1 1907936, 4%Z).
Proof. vm_refl. Qed.

Definition W_94410 : bv 32 := 0x00747593.
Lemma F_94410 : fetch_word Asan.M.loaded_segments (0x94410 : word) = Some W_94410.
Proof. vm_refl. Qed.
Lemma D_94410 : decode_any W_94410 = Some (OpImm ALU_AND 11 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_94414 : bv 32 := 0xeea5cae3.
Lemma F_94414 : fetch_word Asan.M.loaded_segments (0x94414 : word) = Some W_94414.
Proof. vm_refl. Qed.
Lemma D_94414 : decode_any W_94414 = Some (Branch BC_LT 11 10 7924, 4%Z).
Proof. vm_refl. Qed.

Definition W_94418 : bv 32 := 0x00040513.
Lemma F_94418 : fetch_word Asan.M.loaded_segments (0x94418 : word) = Some W_94418.
Proof. vm_refl. Qed.
Lemma D_94418 : decode_any W_94418 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9441c : bv 32 := 0xcd1d10ef.
Lemma F_9441c : fetch_word Asan.M.loaded_segments (0x9441c : word) = Some W_9441c.
Proof. vm_refl. Qed.
Lemma D_9441c : decode_any W_9441c = Some (Jal 1 1907920, 4%Z).
Proof. vm_refl. Qed.

Definition W_94420 : bv 32 := 0xeadd10ef.
Lemma F_94420 : fetch_word Asan.M.loaded_segments (0x94420 : word) = Some W_94420.
Proof. vm_refl. Qed.
Lemma D_94420 : decode_any W_94420 = Some (Jal 1 1908396, 4%Z).
Proof. vm_refl. Qed.

Definition W_94424 : bv 32 := 0x00058513.
Lemma F_94424 : fetch_word Asan.M.loaded_segments (0x94424 : word) = Some W_94424.
Proof. vm_refl. Qed.
Lemma D_94424 : decode_any W_94424 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94428 : bv 32 := 0xea5d10ef.
Lemma F_94428 : fetch_word Asan.M.loaded_segments (0x94428 : word) = Some W_94428.
Proof. vm_refl. Qed.
Lemma D_94428 : decode_any W_94428 = Some (Jal 1 1908388, 4%Z).
Proof. vm_refl. Qed.

Definition W_9442c : bv 32 := 0x9c0d20ef.
Lemma F_9442c : fetch_word Asan.M.loaded_segments (0x9442c : word) = Some W_9442c.
Proof. vm_refl. Qed.
Lemma D_9442c : decode_any W_9442c = Some (Jal 1 1909184, 4%Z).
Proof. vm_refl. Qed.

Definition W_94430 : bv 32 := 0x00090513.
Lemma F_94430 : fetch_word Asan.M.loaded_segments (0x94430 : word) = Some W_94430.
Proof. vm_refl. Qed.
Lemma D_94430 : decode_any W_94430 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94434 : bv 32 := 0xe99d10ef.
Lemma F_94434 : fetch_word Asan.M.loaded_segments (0x94434 : word) = Some W_94434.
Proof. vm_refl. Qed.
Lemma D_94434 : decode_any W_94434 = Some (Jal 1 1908376, 4%Z).
Proof. vm_refl. Qed.

Definition W_94438 : bv 32 := 0xe95d10ef.
Lemma F_94438 : fetch_word Asan.M.loaded_segments (0x94438 : word) = Some W_94438.
Proof. vm_refl. Qed.
Lemma D_94438 : decode_any W_94438 = Some (Jal 1 1908372, 4%Z).
Proof. vm_refl. Qed.

Definition W_9443c : bv 32 := 0x00090513.
Lemma F_9443c : fetch_word Asan.M.loaded_segments (0x9443c : word) = Some W_9443c.
Proof. vm_refl. Qed.
Lemma D_9443c : decode_any W_9443c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94440 : bv 32 := 0xe8dd10ef.
Lemma F_94440 : fetch_word Asan.M.loaded_segments (0x94440 : word) = Some W_94440.
Proof. vm_refl. Qed.
Lemma D_94440 : decode_any W_94440 = Some (Jal 1 1908364, 4%Z).
Proof. vm_refl. Qed.

Definition W_94444 : bv 32 := 0xe89d10ef.
Lemma F_94444 : fetch_word Asan.M.loaded_segments (0x94444 : word) = Some W_94444.
Proof. vm_refl. Qed.
Lemma D_94444 : decode_any W_94444 = Some (Jal 1 1908360, 4%Z).
Proof. vm_refl. Qed.

Definition W_94448 : bv 32 := 0xff010113.
Lemma F_94448 : fetch_word Asan.M.loaded_segments (0x94448 : word) = Some W_94448.
Proof. vm_refl. Qed.
Lemma D_94448 : decode_any W_94448 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_9444c : bv 32 := 0x00113423.
Lemma F_9444c : fetch_word Asan.M.loaded_segments (0x9444c : word) = Some W_9444c.
Proof. vm_refl. Qed.
Lemma D_9444c : decode_any W_9444c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_94450 : bv 32 := 0xe01d20ef.
Lemma F_94450 : fetch_word Asan.M.loaded_segments (0x94450 : word) = Some W_94450.
Proof. vm_refl. Qed.
Lemma D_94450 : decode_any W_94450 = Some (Jal 1 1912320, 4%Z).
Proof. vm_refl. Qed.

Definition W_94454 : bv 32 := 0xe91d20ef.
Lemma F_94454 : fetch_word Asan.M.loaded_segments (0x94454 : word) = Some W_94454.
Proof. vm_refl. Qed.
Lemma D_94454 : decode_any W_94454 = Some (Jal 1 1912464, 4%Z).
Proof. vm_refl. Qed.

Definition W_94458 : bv 32 := 0x00042517.
Lemma F_94458 : fetch_word Asan.M.loaded_segments (0x94458 : word) = Some W_94458.
Proof. vm_refl. Qed.
Lemma D_94458 : decode_any W_94458 = Some (Auipc 10 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_9445c : bv 32 := 0x00042617.
Lemma F_9445c : fetch_word Asan.M.loaded_segments (0x9445c : word) = Some W_9445c.
Proof. vm_refl. Qed.
Lemma D_9445c : decode_any W_9445c = Some (Auipc 12 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_94460 : bv 32 := 0x12853583.
Lemma F_94460 : fetch_word Asan.M.loaded_segments (0x94460 : word) = Some W_94460.
Proof. vm_refl. Qed.
Lemma D_94460 : decode_any W_94460 = Some (Load SZ8 true 11 10 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_94464 : bv 32 := 0x12c63603.
Lemma F_94464 : fetch_word Asan.M.loaded_segments (0x94464 : word) = Some W_94464.
Proof. vm_refl. Qed.
Lemma D_94464 : decode_any W_94464 = Some (Load SZ8 true 12 12 300, 4%Z).
Proof. vm_refl. Qed.

Definition W_94468 : bv 32 := 0x00046517.
Lemma F_94468 : fetch_word Asan.M.loaded_segments (0x94468 : word) = Some W_94468.
Proof. vm_refl. Qed.
Lemma D_94468 : decode_any W_94468 = Some (Auipc 10 70, 4%Z).
Proof. vm_refl. Qed.

Definition W_9446c : bv 32 := 0x01850513.
Lemma F_9446c : fetch_word Asan.M.loaded_segments (0x9446c : word) = Some W_9446c.
Proof. vm_refl. Qed.
Lemma D_9446c : decode_any W_9446c = Some (OpImm ALU_ADD 10 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_94470 : bv 32 := 0xe7cb70ef.
Lemma F_94470 : fetch_word Asan.M.loaded_segments (0x94470 : word) = Some W_94470.
Proof. vm_refl. Qed.
Lemma D_94470 : decode_any W_94470 = Some (Jal 1 1799804, 4%Z).
Proof. vm_refl. Qed.

Definition W_94474 : bv 32 := 0x00813083.
Lemma F_94474 : fetch_word Asan.M.loaded_segments (0x94474 : word) = Some W_94474.
Proof. vm_refl. Qed.
Lemma D_94474 : decode_any W_94474 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_94478 : bv 32 := 0x01010113.
Lemma F_94478 : fetch_word Asan.M.loaded_segments (0x94478 : word) = Some W_94478.
Proof. vm_refl. Qed.
Lemma D_94478 : decode_any W_94478 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9447c : bv 32 := 0x00008067.
Lemma F_9447c : fetch_word Asan.M.loaded_segments (0x9447c : word) = Some W_9447c.
Proof. vm_refl. Qed.
Lemma D_9447c : decode_any W_9447c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94480 : bv 32 := 0xff010113.
Lemma F_94480 : fetch_word Asan.M.loaded_segments (0x94480 : word) = Some W_94480.
Proof. vm_refl. Qed.
Lemma D_94480 : decode_any W_94480 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_94484 : bv 32 := 0x00113423.
Lemma F_94484 : fetch_word Asan.M.loaded_segments (0x94484 : word) = Some W_94484.
Proof. vm_refl. Qed.
Lemma D_94484 : decode_any W_94484 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_94488 : bv 32 := 0x00042517.
Lemma F_94488 : fetch_word Asan.M.loaded_segments (0x94488 : word) = Some W_94488.
Proof. vm_refl. Qed.
Lemma D_94488 : decode_any W_94488 = Some (Auipc 10 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_9448c : bv 32 := 0x00042617.
Lemma F_9448c : fetch_word Asan.M.loaded_segments (0x9448c : word) = Some W_9448c.
Proof. vm_refl. Qed.
Lemma D_9448c : decode_any W_9448c = Some (Auipc 12 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_94490 : bv 32 := 0x0f853583.
Lemma F_94490 : fetch_word Asan.M.loaded_segments (0x94490 : word) = Some W_94490.
Proof. vm_refl. Qed.
Lemma D_94490 : decode_any W_94490 = Some (Load SZ8 true 11 10 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_94494 : bv 32 := 0x0fc63603.
Lemma F_94494 : fetch_word Asan.M.loaded_segments (0x94494 : word) = Some W_94494.
Proof. vm_refl. Qed.
Lemma D_94494 : decode_any W_94494 = Some (Load SZ8 true 12 12 252, 4%Z).
Proof. vm_refl. Qed.

Definition W_94498 : bv 32 := 0x00046517.
Lemma F_94498 : fetch_word Asan.M.loaded_segments (0x94498 : word) = Some W_94498.
Proof. vm_refl. Qed.
Lemma D_94498 : decode_any W_94498 = Some (Auipc 10 70, 4%Z).
Proof. vm_refl. Qed.

Definition W_9449c : bv 32 := 0xfe850513.
Lemma F_9449c : fetch_word Asan.M.loaded_segments (0x9449c : word) = Some W_9449c.
Proof. vm_refl. Qed.
Lemma D_9449c : decode_any W_9449c = Some (OpImm ALU_ADD 10 10 4072, 4%Z).
Proof. vm_refl. Qed.

Definition W_944a0 : bv 32 := 0xeb8b70ef.
Lemma F_944a0 : fetch_word Asan.M.loaded_segments (0x944a0 : word) = Some W_944a0.
Proof. vm_refl. Qed.
Lemma D_944a0 : decode_any W_944a0 = Some (Jal 1 1799864, 4%Z).
Proof. vm_refl. Qed.

Definition W_944a4 : bv 32 := 0x00813083.
Lemma F_944a4 : fetch_word Asan.M.loaded_segments (0x944a4 : word) = Some W_944a4.
Proof. vm_refl. Qed.
Lemma D_944a4 : decode_any W_944a4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_944a8 : bv 32 := 0x01010113.
Lemma F_944a8 : fetch_word Asan.M.loaded_segments (0x944a8 : word) = Some W_944a8.
Proof. vm_refl. Qed.
Lemma D_944a8 : decode_any W_944a8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_944ac : bv 32 := 0x00008067.
Lemma F_944ac : fetch_word Asan.M.loaded_segments (0x944ac : word) = Some W_944ac.
Proof. vm_refl. Qed.
Lemma D_944ac : decode_any W_944ac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

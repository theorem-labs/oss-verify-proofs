(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan.
Module Na0_code_r48448_48dd8.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_64350 : bv 32 := 0xf7010113.
Lemma F_64350 : fetch_word Asan.M.loaded_segments (0x643a0 : word) = Some W_64350.
Proof. vm_refl. Qed.
Lemma D_64350 : decode_any W_64350 = Some (OpImm ALU_ADD 2 2 3952, 4%Z).
Proof. vm_refl. Qed.

Definition W_64354 : bv 32 := 0x08113423.
Lemma F_64354 : fetch_word Asan.M.loaded_segments (0x643a4 : word) = Some W_64354.
Proof. vm_refl. Qed.
Lemma D_64354 : decode_any W_64354 = Some (Store SZ8 2 1 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_64358 : bv 32 := 0x08813023.
Lemma F_64358 : fetch_word Asan.M.loaded_segments (0x643a8 : word) = Some W_64358.
Proof. vm_refl. Qed.
Lemma D_64358 : decode_any W_64358 = Some (Store SZ8 2 8 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_6435c : bv 32 := 0x06913c23.
Lemma F_6435c : fetch_word Asan.M.loaded_segments (0x643ac : word) = Some W_6435c.
Proof. vm_refl. Qed.
Lemma D_6435c : decode_any W_6435c = Some (Store SZ8 2 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_64360 : bv 32 := 0x07213823.
Lemma F_64360 : fetch_word Asan.M.loaded_segments (0x643b0 : word) = Some W_64360.
Proof. vm_refl. Qed.
Lemma D_64360 : decode_any W_64360 = Some (Store SZ8 2 18 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_64364 : bv 32 := 0x07313423.
Lemma F_64364 : fetch_word Asan.M.loaded_segments (0x643b4 : word) = Some W_64364.
Proof. vm_refl. Qed.
Lemma D_64364 : decode_any W_64364 = Some (Store SZ8 2 19 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_64368 : bv 32 := 0x07413023.
Lemma F_64368 : fetch_word Asan.M.loaded_segments (0x643b8 : word) = Some W_64368.
Proof. vm_refl. Qed.
Lemma D_64368 : decode_any W_64368 = Some (Store SZ8 2 20 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_6436c : bv 32 := 0x05513c23.
Lemma F_6436c : fetch_word Asan.M.loaded_segments (0x643bc : word) = Some W_6436c.
Proof. vm_refl. Qed.
Lemma D_6436c : decode_any W_6436c = Some (Store SZ8 2 21 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_64370 : bv 32 := 0x05613823.
Lemma F_64370 : fetch_word Asan.M.loaded_segments (0x643c0 : word) = Some W_64370.
Proof. vm_refl. Qed.
Lemma D_64370 : decode_any W_64370 = Some (Store SZ8 2 22 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_64374 : bv 32 := 0x05713423.
Lemma F_64374 : fetch_word Asan.M.loaded_segments (0x643c4 : word) = Some W_64374.
Proof. vm_refl. Qed.
Lemma D_64374 : decode_any W_64374 = Some (Store SZ8 2 23 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_64378 : bv 32 := 0x05813023.
Lemma F_64378 : fetch_word Asan.M.loaded_segments (0x643c8 : word) = Some W_64378.
Proof. vm_refl. Qed.
Lemma D_64378 : decode_any W_64378 = Some (Store SZ8 2 24 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6437c : bv 32 := 0x03913c23.
Lemma F_6437c : fetch_word Asan.M.loaded_segments (0x643cc : word) = Some W_6437c.
Proof. vm_refl. Qed.
Lemma D_6437c : decode_any W_6437c = Some (Store SZ8 2 25 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_64380 : bv 32 := 0x03a13823.
Lemma F_64380 : fetch_word Asan.M.loaded_segments (0x643d0 : word) = Some W_64380.
Proof. vm_refl. Qed.
Lemma D_64380 : decode_any W_64380 = Some (Store SZ8 2 26 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_64384 : bv 32 := 0x03b13423.
Lemma F_64384 : fetch_word Asan.M.loaded_segments (0x643d4 : word) = Some W_64384.
Proof. vm_refl. Qed.
Lemma D_64384 : decode_any W_64384 = Some (Store SZ8 2 27 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_64388 : bv 32 := 0x00058493.
Lemma F_64388 : fetch_word Asan.M.loaded_segments (0x643d8 : word) = Some W_64388.
Proof. vm_refl. Qed.
Lemma D_64388 : decode_any W_64388 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6438c : bv 32 := 0x00050c93.
Lemma F_6438c : fetch_word Asan.M.loaded_segments (0x643dc : word) = Some W_6438c.
Proof. vm_refl. Qed.
Lemma D_6438c : decode_any W_6438c = Some (OpImm ALU_ADD 25 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64390 : bv 32 := 0x42c260ef.
Lemma F_64390 : fetch_word Asan.M.loaded_segments (0x643e0 : word) = Some W_64390.
Proof. vm_refl. Qed.
Lemma D_64390 : decode_any W_64390 = Some (Jal 1 156716, 4%Z).
Proof. vm_refl. Qed.

Definition W_64394 : bv 32 := 0x26050463.
Lemma F_64394 : fetch_word Asan.M.loaded_segments (0x643e4 : word) = Some W_64394.
Proof. vm_refl. Qed.
Lemma D_64394 : decode_any W_64394 = Some (Branch BC_EQ 10 0 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_64398 : bv 32 := 0x00050913.
Lemma F_64398 : fetch_word Asan.M.loaded_segments (0x643e8 : word) = Some W_64398.
Proof. vm_refl. Qed.
Lemma D_64398 : decode_any W_64398 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6439c : bv 32 := 0x5e4260ef.
Lemma F_6439c : fetch_word Asan.M.loaded_segments (0x643ec : word) = Some W_6439c.
Proof. vm_refl. Qed.
Lemma D_6439c : decode_any W_6439c = Some (Jal 1 157156, 4%Z).
Proof. vm_refl. Qed.

Definition W_643a0 : bv 32 := 0x00050993.
Lemma F_643a0 : fetch_word Asan.M.loaded_segments (0x643f0 : word) = Some W_643a0.
Proof. vm_refl. Qed.
Lemma D_643a0 : decode_any W_643a0 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_643a4 : bv 32 := 0x00090513.
Lemma F_643a4 : fetch_word Asan.M.loaded_segments (0x643f4 : word) = Some W_643a4.
Proof. vm_refl. Qed.
Lemma D_643a4 : decode_any W_643a4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_643a8 : bv 32 := 0x630260ef.
Lemma F_643a8 : fetch_word Asan.M.loaded_segments (0x643f8 : word) = Some W_643a8.
Proof. vm_refl. Qed.
Lemma D_643a8 : decode_any W_643a8 = Some (Jal 1 157232, 4%Z).
Proof. vm_refl. Qed.

Definition W_643ac : bv 32 := 0x2499e863.
Lemma F_643ac : fetch_word Asan.M.loaded_segments (0x643fc : word) = Some W_643ac.
Proof. vm_refl. Qed.
Lemma D_643ac : decode_any W_643ac = Some (Branch BC_LTU 19 9 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_643b0 : bv 32 := 0x00050913.
Lemma F_643b0 : fetch_word Asan.M.loaded_segments (0x64400 : word) = Some W_643b0.
Proof. vm_refl. Qed.
Lemma D_643b0 : decode_any W_643b0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_643b4 : bv 32 := 0x24a4e463.
Lemma F_643b4 : fetch_word Asan.M.loaded_segments (0x64404 : word) = Some W_643b4.
Proof. vm_refl. Qed.
Lemma D_643b4 : decode_any W_643b4 = Some (Branch BC_LTU 9 10 584, 4%Z).
Proof. vm_refl. Qed.

Definition W_643b8 : bv 32 := 0x00000d13.
Lemma F_643b8 : fetch_word Asan.M.loaded_segments (0x64408 : word) = Some W_643b8.
Proof. vm_refl. Qed.
Lemma D_643b8 : decode_any W_643b8 = Some (OpImm ALU_ADD 26 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_643bc : bv 32 := 0x00001437.
Lemma F_643bc : fetch_word Asan.M.loaded_segments (0x6440c : word) = Some W_643bc.
Proof. vm_refl. Qed.
Lemma D_643bc : decode_any W_643bc = Some (Lui 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_643c0 : bv 32 := 0x000f3517.
Lemma F_643c0 : fetch_word Asan.M.loaded_segments (0x64410 : word) = Some W_643c0.
Proof. vm_refl. Qed.
Lemma D_643c0 : decode_any W_643c0 = Some (Auipc 10 243, 4%Z).
Proof. vm_refl. Qed.

Definition W_643c4 : bv 32 := 0x000f3597.
Lemma F_643c4 : fetch_word Asan.M.loaded_segments (0x64414 : word) = Some W_643c4.
Proof. vm_refl. Qed.
Lemma D_643c4 : decode_any W_643c4 = Some (Auipc 11 243, 4%Z).
Proof. vm_refl. Qed.

Definition W_643c8 : bv 32 := 0x000f3617.
Lemma F_643c8 : fetch_word Asan.M.loaded_segments (0x64418 : word) = Some W_643c8.
Proof. vm_refl. Qed.
Lemma D_643c8 : decode_any W_643c8 = Some (Auipc 12 243, 4%Z).
Proof. vm_refl. Qed.

Definition W_643cc : bv 32 := 0x000f3697.
Lemma F_643cc : fetch_word Asan.M.loaded_segments (0x6441c : word) = Some W_643cc.
Proof. vm_refl. Qed.
Lemma D_643cc : decode_any W_643cc = Some (Auipc 13 243, 4%Z).
Proof. vm_refl. Qed.

Definition W_643d0 : bv 32 := 0x000f3717.
Lemma F_643d0 : fetch_word Asan.M.loaded_segments (0x64420 : word) = Some W_643d0.
Proof. vm_refl. Qed.
Lemma D_643d0 : decode_any W_643d0 = Some (Auipc 14 243, 4%Z).
Proof. vm_refl. Qed.

Definition W_643d4 : bv 32 := 0xfffac797.
Lemma F_643d4 : fetch_word Asan.M.loaded_segments (0x64424 : word) = Some W_643d4.
Proof. vm_refl. Qed.
Lemma D_643d4 : decode_any W_643d4 = Some (Auipc 15 1048492, 4%Z).
Proof. vm_refl. Qed.

Definition W_643d8 : bv 32 := 0x008c8433.
Lemma F_643d8 : fetch_word Asan.M.loaded_segments (0x64428 : word) = Some W_643d8.
Proof. vm_refl. Qed.
Lemma D_643d8 : decode_any W_643d8 = Some (Op ALU_ADD 8 25 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_643dc : bv 32 := 0x98853b03.
Lemma F_643dc : fetch_word Asan.M.loaded_segments (0x6442c : word) = Some W_643dc.
Proof. vm_refl. Qed.
Lemma D_643dc : decode_any W_643dc = Some (Load SZ8 true 22 10 2440, 4%Z).
Proof. vm_refl. Qed.

Definition W_643e0 : bv 32 := 0x98c5b503.
Lemma F_643e0 : fetch_word Asan.M.loaded_segments (0x64430 : word) = Some W_643e0.
Proof. vm_refl. Qed.
Lemma D_643e0 : decode_any W_643e0 = Some (Load SZ8 true 10 11 2444, 4%Z).
Proof. vm_refl. Qed.

Definition W_643e4 : bv 32 := 0x00a13c23.
Lemma F_643e4 : fetch_word Asan.M.loaded_segments (0x64434 : word) = Some W_643e4.
Proof. vm_refl. Qed.
Lemma D_643e4 : decode_any W_643e4 = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_643e8 : bv 32 := 0x99063503.
Lemma F_643e8 : fetch_word Asan.M.loaded_segments (0x64438 : word) = Some W_643e8.
Proof. vm_refl. Qed.
Lemma D_643e8 : decode_any W_643e8 = Some (Load SZ8 true 10 12 2448, 4%Z).
Proof. vm_refl. Qed.

Definition W_643ec : bv 32 := 0x00a13823.
Lemma F_643ec : fetch_word Asan.M.loaded_segments (0x6443c : word) = Some W_643ec.
Proof. vm_refl. Qed.
Lemma D_643ec : decode_any W_643ec = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_643f0 : bv 32 := 0x9946b503.
Lemma F_643f0 : fetch_word Asan.M.loaded_segments (0x64440 : word) = Some W_643f0.
Proof. vm_refl. Qed.
Lemma D_643f0 : decode_any W_643f0 = Some (Load SZ8 true 10 13 2452, 4%Z).
Proof. vm_refl. Qed.

Definition W_643f4 : bv 32 := 0x00a13423.
Lemma F_643f4 : fetch_word Asan.M.loaded_segments (0x64444 : word) = Some W_643f4.
Proof. vm_refl. Qed.
Lemma D_643f4 : decode_any W_643f4 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_643f8 : bv 32 := 0x97073503.
Lemma F_643f8 : fetch_word Asan.M.loaded_segments (0x64448 : word) = Some W_643f8.
Proof. vm_refl. Qed.
Lemma D_643f8 : decode_any W_643f8 = Some (Load SZ8 true 10 14 2416, 4%Z).
Proof. vm_refl. Qed.

Definition W_643fc : bv 32 := 0x00a13023.
Lemma F_643fc : fetch_word Asan.M.loaded_segments (0x6444c : word) = Some W_643fc.
Proof. vm_refl. Qed.
Lemma D_643fc : decode_any W_643fc = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64400 : bv 32 := 0xf847bb83.
Lemma F_64400 : fetch_word Asan.M.loaded_segments (0x64450 : word) = Some W_64400.
Proof. vm_refl. Qed.
Lemma D_64400 : decode_any W_64400 = Some (Load SZ8 true 23 15 3972, 4%Z).
Proof. vm_refl. Qed.

Definition W_64404 : bv 32 := 0x00100393.
Lemma F_64404 : fetch_word Asan.M.loaded_segments (0x64454 : word) = Some W_64404.
Proof. vm_refl. Qed.
Lemma D_64404 : decode_any W_64404 = Some (OpImm ALU_ADD 7 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64408 : bv 32 := 0x00600e13.
Lemma F_64408 : fetch_word Asan.M.loaded_segments (0x64458 : word) = Some W_64408.
Proof. vm_refl. Qed.
Lemma D_64408 : decode_any W_64408 = Some (OpImm ALU_ADD 28 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_6440c : bv 32 := 0x00000a13.
Lemma F_6440c : fetch_word Asan.M.loaded_segments (0x6445c : word) = Some W_6440c.
Proof. vm_refl. Qed.
Lemma D_6440c : decode_any W_6440c = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64410 : bv 32 := 0x0100006f.
Lemma F_64410 : fetch_word Asan.M.loaded_segments (0x64460 : word) = Some W_64410.
Proof. vm_refl. Qed.
Lemma D_64410 : decode_any W_64410 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64414 : bv 32 := 0x001a0a13.
Lemma F_64414 : fetch_word Asan.M.loaded_segments (0x64464 : word) = Some W_64414.
Proof. vm_refl. Qed.
Lemma D_64414 : decode_any W_64414 = Some (OpImm ALU_ADD 20 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64418 : bv 32 := 0x00b00513.
Lemma F_64418 : fetch_word Asan.M.loaded_segments (0x64468 : word) = Some W_64418.
Proof. vm_refl. Qed.
Lemma D_64418 : decode_any W_64418 = Some (OpImm ALU_ADD 10 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6441c : bv 32 := 0x1caa0e63.
Lemma F_6441c : fetch_word Asan.M.loaded_segments (0x6446c : word) = Some W_6441c.
Proof. vm_refl. Qed.
Lemma D_6441c : decode_any W_6441c = Some (Branch BC_EQ 20 10 476, 4%Z).
Proof. vm_refl. Qed.

Definition W_64420 : bv 32 := 0x00000d93.
Lemma F_64420 : fetch_word Asan.M.loaded_segments (0x64470 : word) = Some W_64420.
Proof. vm_refl. Qed.
Lemma D_64420 : decode_any W_64420 = Some (OpImm ALU_ADD 27 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64424 : bv 32 := 0x058cb503.
Lemma F_64424 : fetch_word Asan.M.loaded_segments (0x64474 : word) = Some W_64424.
Proof. vm_refl. Qed.
Lemma D_64424 : decode_any W_64424 = Some (Load SZ8 true 10 25 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_64428 : bv 32 := 0x00a00593.
Lemma F_64428 : fetch_word Asan.M.loaded_segments (0x64478 : word) = Some W_64428.
Proof. vm_refl. Qed.
Lemma D_64428 : decode_any W_64428 = Some (OpImm ALU_ADD 11 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6442c : bv 32 := 0x414585bb.
Lemma F_6442c : fetch_word Asan.M.loaded_segments (0x6447c : word) = Some W_6442c.
Proof. vm_refl. Qed.
Lemma D_6442c : decode_any W_6442c = Some (Op32 ALU_SUB 11 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_64430 : bv 32 := 0x006a0a93.
Lemma F_64430 : fetch_word Asan.M.loaded_segments (0x64480 : word) = Some W_64430.
Proof. vm_refl. Qed.
Lemma D_64430 : decode_any W_64430 = Some (OpImm ALU_ADD 21 20 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_64434 : bv 32 := 0xfff00613.
Lemma F_64434 : fetch_word Asan.M.loaded_segments (0x64484 : word) = Some W_64434.
Proof. vm_refl. Qed.
Lemma D_64434 : decode_any W_64434 = Some (OpImm ALU_ADD 12 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64438 : bv 32 := 0x00b615b3.
Lemma F_64438 : fetch_word Asan.M.loaded_segments (0x64488 : word) = Some W_64438.
Proof. vm_refl. Qed.
Lemma D_64438 : decode_any W_64438 = Some (Op ALU_SLL 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6443c : bv 32 := 0x3ff5f593.
Lemma F_6443c : fetch_word Asan.M.loaded_segments (0x6448c : word) = Some W_6443c.
Proof. vm_refl. Qed.
Lemma D_6443c : decode_any W_6443c = Some (OpImm ALU_AND 11 11 1023, 4%Z).
Proof. vm_refl. Qed.

Definition W_64440 : bv 32 := 0xff150613.
Lemma F_64440 : fetch_word Asan.M.loaded_segments (0x64490 : word) = Some W_64440.
Proof. vm_refl. Qed.
Lemma D_64440 : decode_any W_64440 = Some (OpImm ALU_ADD 12 10 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_64444 : bv 32 := 0x414509b3.
Lemma F_64444 : fetch_word Asan.M.loaded_segments (0x64494 : word) = Some W_64444.
Proof. vm_refl. Qed.
Lemma D_64444 : decode_any W_64444 = Some (Op ALU_SUB 19 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_64448 : bv 32 := 0x00c59c33.
Lemma F_64448 : fetch_word Asan.M.loaded_segments (0x64498 : word) = Some W_64448.
Proof. vm_refl. Qed.
Lemma D_64448 : decode_any W_64448 = Some (Op ALU_SLL 24 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6444c : bv 32 := 0xffa98993.
Lemma F_6444c : fetch_word Asan.M.loaded_segments (0x6449c : word) = Some W_6444c.
Proof. vm_refl. Qed.
Lemma D_6444c : decode_any W_6444c = Some (OpImm ALU_ADD 19 19 4090, 4%Z).
Proof. vm_refl. Qed.

Definition W_64450 : bv 32 := 0x01840c33.
Lemma F_64450 : fetch_word Asan.M.loaded_segments (0x644a0 : word) = Some W_64450.
Proof. vm_refl. Qed.
Lemma D_64450 : decode_any W_64450 = Some (Op ALU_ADD 24 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64454 : bv 32 := 0x04000513.
Lemma F_64454 : fetch_word Asan.M.loaded_segments (0x644a4 : word) = Some W_64454.
Proof. vm_refl. Qed.
Lemma D_64454 : decode_any W_64454 = Some (OpImm ALU_ADD 10 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_64458 : bv 32 := 0x01451533.
Lemma F_64458 : fetch_word Asan.M.loaded_segments (0x644a8 : word) = Some W_64458.
Proof. vm_refl. Qed.
Lemma D_64458 : decode_any W_64458 = Some (Op ALU_SLL 10 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6445c : bv 32 := 0x02a13023.
Lemma F_6445c : fetch_word Asan.M.loaded_segments (0x644ac : word) = Some W_6445c.
Proof. vm_refl. Qed.
Lemma D_6445c : decode_any W_6445c = Some (Store SZ8 2 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64460 : bv 32 := 0x0240006f.
Lemma F_64460 : fetch_word Asan.M.loaded_segments (0x644b0 : word) = Some W_64460.
Proof. vm_refl. Qed.
Lemma D_64460 : decode_any W_64460 = Some (Jal 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_64478 : bv 32 := 0x001d8d93.
Lemma F_64478 : fetch_word Asan.M.loaded_segments (0x644c8 : word) = Some W_64478.
Proof. vm_refl. Qed.
Lemma D_64478 : decode_any W_64478 = Some (OpImm ALU_ADD 27 27 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6447c : bv 32 := 0x013dd533.
Lemma F_6447c : fetch_word Asan.M.loaded_segments (0x644cc : word) = Some W_6447c.
Proof. vm_refl. Qed.
Lemma D_6447c : decode_any W_6447c = Some (Op ALU_SRL 10 27 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_64480 : bv 32 := 0xf8051ae3.
Lemma F_64480 : fetch_word Asan.M.loaded_segments (0x644d0 : word) = Some W_64480.
Proof. vm_refl. Qed.
Lemma D_64480 : decode_any W_64480 = Some (Branch BC_NE 10 0 8084, 4%Z).
Proof. vm_refl. Qed.

Definition W_64484 : bv 32 := 0x01bc05b3.
Lemma F_64484 : fetch_word Asan.M.loaded_segments (0x644d4 : word) = Some W_64484.
Proof. vm_refl. Qed.
Lemma D_64484 : decode_any W_64484 = Some (Op ALU_ADD 11 24 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_64488 : bv 32 := 0x0005c503.
Lemma F_64488 : fetch_word Asan.M.loaded_segments (0x644d8 : word) = Some W_64488.
Proof. vm_refl. Qed.
Lemma D_64488 : decode_any W_64488 = Some (Load SZ1 false 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6448c : bv 32 := 0xfe0506e3.
Lemma F_6448c : fetch_word Asan.M.loaded_segments (0x644dc : word) = Some W_6448c.
Proof. vm_refl. Qed.
Lemma D_6448c : decode_any W_6448c = Some (Branch BC_EQ 10 0 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_64490 : bv 32 := 0x058cb503.
Lemma F_64490 : fetch_word Asan.M.loaded_segments (0x644e0 : word) = Some W_64490.
Proof. vm_refl. Qed.
Lemma D_64490 : decode_any W_64490 = Some (Load SZ8 true 10 25 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_64494 : bv 32 := 0xffb50613.
Lemma F_64494 : fetch_word Asan.M.loaded_segments (0x644e4 : word) = Some W_64494.
Proof. vm_refl. Qed.
Lemma D_64494 : decode_any W_64494 = Some (OpImm ALU_ADD 12 10 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_64498 : bv 32 := 0x00aa1533.
Lemma F_64498 : fetch_word Asan.M.loaded_segments (0x644e8 : word) = Some W_64498.
Proof. vm_refl. Qed.
Lemma D_64498 : decode_any W_64498 = Some (Op ALU_SLL 10 20 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6449c : bv 32 := 0x00c39633.
Lemma F_6449c : fetch_word Asan.M.loaded_segments (0x644ec : word) = Some W_6449c.
Proof. vm_refl. Qed.
Lemma D_6449c : decode_any W_6449c = Some (Op ALU_SLL 12 7 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_644a0 : bv 32 := 0x00a40533.
Lemma F_644a0 : fetch_word Asan.M.loaded_segments (0x644f0 : word) = Some W_644a0.
Proof. vm_refl. Qed.
Lemma D_644a0 : decode_any W_644a0 = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_644a4 : bv 32 := 0x00c50533.
Lemma F_644a4 : fetch_word Asan.M.loaded_segments (0x644f4 : word) = Some W_644a4.
Proof. vm_refl. Qed.
Lemma D_644a4 : decode_any W_644a4 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_644a8 : bv 32 := 0x015d9633.
Lemma F_644a8 : fetch_word Asan.M.loaded_segments (0x644f8 : word) = Some W_644a8.
Proof. vm_refl. Qed.
Lemma D_644a8 : decode_any W_644a8 = Some (Op ALU_SLL 12 27 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_644ac : bv 32 := 0x00c50533.
Lemma F_644ac : fetch_word Asan.M.loaded_segments (0x644fc : word) = Some W_644ac.
Proof. vm_refl. Qed.
Lemma D_644ac : decode_any W_644ac = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_644b0 : bv 32 := 0x01853603.
Lemma F_644b0 : fetch_word Asan.M.loaded_segments (0x64500 : word) = Some W_644b0.
Proof. vm_refl. Qed.
Lemma D_644b0 : decode_any W_644b0 = Some (Load SZ8 true 12 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_644b4 : bv 32 := 0xfcc972e3.
Lemma F_644b4 : fetch_word Asan.M.loaded_segments (0x64504 : word) = Some W_644b4.
Proof. vm_refl. Qed.
Lemma D_644b4 : decode_any W_644b4 = Some (Branch BC_GEU 18 12 8132, 4%Z).
Proof. vm_refl. Qed.

Definition W_644b8 : bv 32 := 0xfc9670e3.
Lemma F_644b8 : fetch_word Asan.M.loaded_segments (0x64508 : word) = Some W_644b8.
Proof. vm_refl. Qed.
Lemma D_644b8 : decode_any W_644b8 = Some (Branch BC_GEU 12 9 8128, 4%Z).
Proof. vm_refl. Qed.

Definition W_644bc : bv 32 := 0x01a58023.
Lemma F_644bc : fetch_word Asan.M.loaded_segments (0x6450c : word) = Some W_644bc.
Proof. vm_refl. Qed.
Lemma D_644bc : decode_any W_644bc = Some (Store SZ1 11 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_644c0 : bv 32 := 0x000b3583.
Lemma F_644c0 : fetch_word Asan.M.loaded_segments (0x64510 : word) = Some W_644c0.
Proof. vm_refl. Qed.
Lemma D_644c0 : decode_any W_644c0 = Some (Load SZ8 true 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_644c4 : bv 32 := 0xfff58613.
Lemma F_644c4 : fetch_word Asan.M.loaded_segments (0x64514 : word) = Some W_644c4.
Proof. vm_refl. Qed.
Lemma D_644c4 : decode_any W_644c4 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_644c8 : bv 32 := 0x00c5b6b3.
Lemma F_644c8 : fetch_word Asan.M.loaded_segments (0x64518 : word) = Some W_644c8.
Proof. vm_refl. Qed.
Lemma D_644c8 : decode_any W_644c8 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_644cc : bv 32 := 0xfff68693.
Lemma F_644cc : fetch_word Asan.M.loaded_segments (0x6451c : word) = Some W_644cc.
Proof. vm_refl. Qed.
Lemma D_644cc : decode_any W_644cc = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_644d0 : bv 32 := 0x00c6f6b3.
Lemma F_644d0 : fetch_word Asan.M.loaded_segments (0x64520 : word) = Some W_644d0.
Proof. vm_refl. Qed.
Lemma D_644d0 : decode_any W_644d0 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_644d4 : bv 32 := 0x02a6fc63.
Lemma F_644d4 : fetch_word Asan.M.loaded_segments (0x64524 : word) = Some W_644d4.
Proof. vm_refl. Qed.
Lemma D_644d4 : decode_any W_644d4 = Some (Branch BC_GEU 13 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_644d8 : bv 32 := 0x01813683.
Lemma F_644d8 : fetch_word Asan.M.loaded_segments (0x64528 : word) = Some W_644d8.
Proof. vm_refl. Qed.
Lemma D_644d8 : decode_any W_644d8 = Some (Load SZ8 true 13 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_644dc : bv 32 := 0x0006b803.
Lemma F_644dc : fetch_word Asan.M.loaded_segments (0x6452c : word) = Some W_644dc.
Proof. vm_refl. Qed.
Lemma D_644dc : decode_any W_644dc = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_644e0 : bv 32 := 0x01013683.
Lemma F_644e0 : fetch_word Asan.M.loaded_segments (0x64530 : word) = Some W_644e0.
Proof. vm_refl. Qed.
Lemma D_644e0 : decode_any W_644e0 = Some (Load SZ8 true 13 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_644e4 : bv 32 := 0x0006b683.
Lemma F_644e4 : fetch_word Asan.M.loaded_segments (0x64534 : word) = Some W_644e4.
Proof. vm_refl. Qed.
Lemma D_644e4 : decode_any W_644e4 = Some (Load SZ8 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_644e8 : bv 32 := 0xfff80793.
Lemma F_644e8 : fetch_word Asan.M.loaded_segments (0x64538 : word) = Some W_644e8.
Proof. vm_refl. Qed.
Lemma D_644e8 : decode_any W_644e8 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_644ec : bv 32 := 0x00a7f463.
Lemma F_644ec : fetch_word Asan.M.loaded_segments (0x6453c : word) = Some W_644ec.
Proof. vm_refl. Qed.
Lemma D_644ec : decode_any W_644ec = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_644f4 : bv 32 := 0x00813703.
Lemma F_644f4 : fetch_word Asan.M.loaded_segments (0x64544 : word) = Some W_644f4.
Proof. vm_refl. Qed.
Lemma D_644f4 : decode_any W_644f4 = Some (Load SZ8 true 14 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_644f8 : bv 32 := 0x00073283.
Lemma F_644f8 : fetch_word Asan.M.loaded_segments (0x64548 : word) = Some W_644f8.
Proof. vm_refl. Qed.
Lemma D_644f8 : decode_any W_644f8 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_644fc : bv 32 := 0x0032d713.
Lemma F_644fc : fetch_word Asan.M.loaded_segments (0x6454c : word) = Some W_644fc.
Proof. vm_refl. Qed.
Lemma D_644fc : decode_any W_644fc = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_64500 : bv 32 := 0x00b708b3.
Lemma F_64500 : fetch_word Asan.M.loaded_segments (0x64550 : word) = Some W_64500.
Proof. vm_refl. Qed.
Lemma D_64500 : decode_any W_64500 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_64504 : bv 32 := 0x02a2e863.
Lemma F_64504 : fetch_word Asan.M.loaded_segments (0x64554 : word) = Some W_64504.
Proof. vm_refl. Qed.
Lemma D_64504 : decode_any W_64504 = Some (Branch BC_LTU 5 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_64508 : bv 32 := 0x02a8f663.
Lemma F_64508 : fetch_word Asan.M.loaded_segments (0x64558 : word) = Some W_64508.
Proof. vm_refl. Qed.
Lemma D_64508 : decode_any W_64508 = Some (Branch BC_GEU 17 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_6450c : bv 32 := 0xf54e6ce3.
Lemma F_6450c : fetch_word Asan.M.loaded_segments (0x6455c : word) = Some W_6450c.
Proof. vm_refl. Qed.
Lemma D_6450c : decode_any W_6450c = Some (Branch BC_LTU 28 20 8024, 4%Z).
Proof. vm_refl. Qed.

Definition W_64510 : bv 32 := 0x00355513.
Lemma F_64510 : fetch_word Asan.M.loaded_segments (0x64560 : word) = Some W_64510.
Proof. vm_refl. Qed.
Lemma D_64510 : decode_any W_64510 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_64514 : bv 32 := 0x00a585b3.
Lemma F_64514 : fetch_word Asan.M.loaded_segments (0x64564 : word) = Some W_64514.
Proof. vm_refl. Qed.
Lemma D_64514 : decode_any W_64514 = Some (Op ALU_ADD 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_64518 : bv 32 := 0x00100513.
Lemma F_64518 : fetch_word Asan.M.loaded_segments (0x64568 : word) = Some W_64518.
Proof. vm_refl. Qed.
Lemma D_64518 : decode_any W_64518 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6451c : bv 32 := 0x0175b023.
Lemma F_6451c : fetch_word Asan.M.loaded_segments (0x6456c : word) = Some W_6451c.
Proof. vm_refl. Qed.
Lemma D_6451c : decode_any W_6451c = Some (Store SZ8 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64520 : bv 32 := 0x01455633.
Lemma F_64520 : fetch_word Asan.M.loaded_segments (0x64570 : word) = Some W_64520.
Proof. vm_refl. Qed.
Lemma D_64520 : decode_any W_64520 = Some (Op ALU_SRL 12 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_64524 : bv 32 := 0x00858593.
Lemma F_64524 : fetch_word Asan.M.loaded_segments (0x64574 : word) = Some W_64524.
Proof. vm_refl. Qed.
Lemma D_64524 : decode_any W_64524 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64528 : bv 32 := 0x00150513.
Lemma F_64528 : fetch_word Asan.M.loaded_segments (0x64578 : word) = Some W_64528.
Proof. vm_refl. Qed.
Lemma D_64528 : decode_any W_64528 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6452c : bv 32 := 0xfe0608e3.
Lemma F_6452c : fetch_word Asan.M.loaded_segments (0x6457c : word) = Some W_6452c.
Proof. vm_refl. Qed.
Lemma D_6452c : decode_any W_6452c = Some (Branch BC_EQ 12 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_64530 : bv 32 := 0xf49ff06f.
Lemma F_64530 : fetch_word Asan.M.loaded_segments (0x64580 : word) = Some W_64530.
Proof. vm_refl. Qed.
Lemma D_64530 : decode_any W_64530 = Some (Jal 0 2096968, 4%Z).
Proof. vm_refl. Qed.

Definition W_645f8 : bv 32 := 0x060c8023.
Lemma F_645f8 : fetch_word Asan.M.loaded_segments (0x64648 : word) = Some W_645f8.
Proof. vm_refl. Qed.
Lemma D_645f8 : decode_any W_645f8 = Some (Store SZ1 25 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_645fc : bv 32 := 0x08813083.
Lemma F_645fc : fetch_word Asan.M.loaded_segments (0x6464c : word) = Some W_645fc.
Proof. vm_refl. Qed.
Lemma D_645fc : decode_any W_645fc = Some (Load SZ8 true 1 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_64600 : bv 32 := 0x08013403.
Lemma F_64600 : fetch_word Asan.M.loaded_segments (0x64650 : word) = Some W_64600.
Proof. vm_refl. Qed.
Lemma D_64600 : decode_any W_64600 = Some (Load SZ8 true 8 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_64604 : bv 32 := 0x07813483.
Lemma F_64604 : fetch_word Asan.M.loaded_segments (0x64654 : word) = Some W_64604.
Proof. vm_refl. Qed.
Lemma D_64604 : decode_any W_64604 = Some (Load SZ8 true 9 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_64608 : bv 32 := 0x07013903.
Lemma F_64608 : fetch_word Asan.M.loaded_segments (0x64658 : word) = Some W_64608.
Proof. vm_refl. Qed.
Lemma D_64608 : decode_any W_64608 = Some (Load SZ8 true 18 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_6460c : bv 32 := 0x06813983.
Lemma F_6460c : fetch_word Asan.M.loaded_segments (0x6465c : word) = Some W_6460c.
Proof. vm_refl. Qed.
Lemma D_6460c : decode_any W_6460c = Some (Load SZ8 true 19 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_64610 : bv 32 := 0x06013a03.
Lemma F_64610 : fetch_word Asan.M.loaded_segments (0x64660 : word) = Some W_64610.
Proof. vm_refl. Qed.
Lemma D_64610 : decode_any W_64610 = Some (Load SZ8 true 20 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_64614 : bv 32 := 0x05813a83.
Lemma F_64614 : fetch_word Asan.M.loaded_segments (0x64664 : word) = Some W_64614.
Proof. vm_refl. Qed.
Lemma D_64614 : decode_any W_64614 = Some (Load SZ8 true 21 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_64618 : bv 32 := 0x05013b03.
Lemma F_64618 : fetch_word Asan.M.loaded_segments (0x64668 : word) = Some W_64618.
Proof. vm_refl. Qed.
Lemma D_64618 : decode_any W_64618 = Some (Load SZ8 true 22 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_6461c : bv 32 := 0x04813b83.
Lemma F_6461c : fetch_word Asan.M.loaded_segments (0x6466c : word) = Some W_6461c.
Proof. vm_refl. Qed.
Lemma D_6461c : decode_any W_6461c = Some (Load SZ8 true 23 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_64620 : bv 32 := 0x04013c03.
Lemma F_64620 : fetch_word Asan.M.loaded_segments (0x64670 : word) = Some W_64620.
Proof. vm_refl. Qed.
Lemma D_64620 : decode_any W_64620 = Some (Load SZ8 true 24 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_64624 : bv 32 := 0x03813c83.
Lemma F_64624 : fetch_word Asan.M.loaded_segments (0x64674 : word) = Some W_64624.
Proof. vm_refl. Qed.
Lemma D_64624 : decode_any W_64624 = Some (Load SZ8 true 25 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_64628 : bv 32 := 0x03013d03.
Lemma F_64628 : fetch_word Asan.M.loaded_segments (0x64678 : word) = Some W_64628.
Proof. vm_refl. Qed.
Lemma D_64628 : decode_any W_64628 = Some (Load SZ8 true 26 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_6462c : bv 32 := 0x02813d83.
Lemma F_6462c : fetch_word Asan.M.loaded_segments (0x6467c : word) = Some W_6462c.
Proof. vm_refl. Qed.
Lemma D_6462c : decode_any W_6462c = Some (Load SZ8 true 27 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_64630 : bv 32 := 0x09010113.
Lemma F_64630 : fetch_word Asan.M.loaded_segments (0x64680 : word) = Some W_64630.
Proof. vm_refl. Qed.
Lemma D_64630 : decode_any W_64630 = Some (OpImm ALU_ADD 2 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_64634 : bv 32 := 0x00008067.
Lemma F_64634 : fetch_word Asan.M.loaded_segments (0x64684 : word) = Some W_64634.
Proof. vm_refl. Qed.
Lemma D_64634 : decode_any W_64634 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64638 : bv 32 := 0x00100593.
Lemma F_64638 : fetch_word Asan.M.loaded_segments (0x64688 : word) = Some W_64638.
Proof. vm_refl. Qed.
Lemma D_64638 : decode_any W_64638 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6463c : bv 32 := 0x06b50023.
Lemma F_6463c : fetch_word Asan.M.loaded_segments (0x6468c : word) = Some W_6463c.
Proof. vm_refl. Qed.
Lemma D_6463c : decode_any W_6463c = Some (Store SZ1 10 11 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_64640 : bv 32 := 0x00008067.
Lemma F_64640 : fetch_word Asan.M.loaded_segments (0x64690 : word) = Some W_64640.
Proof. vm_refl. Qed.
Lemma D_64640 : decode_any W_64640 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64910 : bv 32 := 0xfe010113.
Lemma F_64910 : fetch_word Asan.M.loaded_segments (0x64960 : word) = Some W_64910.
Proof. vm_refl. Qed.
Lemma D_64910 : decode_any W_64910 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_64914 : bv 32 := 0x00113c23.
Lemma F_64914 : fetch_word Asan.M.loaded_segments (0x64964 : word) = Some W_64914.
Proof. vm_refl. Qed.
Lemma D_64914 : decode_any W_64914 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64918 : bv 32 := 0x00813823.
Lemma F_64918 : fetch_word Asan.M.loaded_segments (0x64968 : word) = Some W_64918.
Proof. vm_refl. Qed.
Lemma D_64918 : decode_any W_64918 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6491c : bv 32 := 0x00913423.
Lemma F_6491c : fetch_word Asan.M.loaded_segments (0x6496c : word) = Some W_6491c.
Proof. vm_refl. Qed.
Lemma D_6491c : decode_any W_6491c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64920 : bv 32 := 0x01213023.
Lemma F_64920 : fetch_word Asan.M.loaded_segments (0x64970 : word) = Some W_64920.
Proof. vm_refl. Qed.
Lemma D_64920 : decode_any W_64920 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64924 : bv 32 := 0x02010413.
Lemma F_64924 : fetch_word Asan.M.loaded_segments (0x64974 : word) = Some W_64924.
Proof. vm_refl. Qed.
Lemma D_64924 : decode_any W_64924 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64928 : bv 32 := 0x000f3517.
Lemma F_64928 : fetch_word Asan.M.loaded_segments (0x64978 : word) = Some W_64928.
Proof. vm_refl. Qed.
Lemma D_64928 : decode_any W_64928 = Some (Auipc 10 243, 4%Z).
Proof. vm_refl. Qed.

Definition W_6492c : bv 32 := 0x21850513.
Lemma F_6492c : fetch_word Asan.M.loaded_segments (0x6497c : word) = Some W_6492c.
Proof. vm_refl. Qed.
Lemma D_6492c : decode_any W_6492c = Some (OpImm ALU_ADD 10 10 536, 4%Z).
Proof. vm_refl. Qed.

Definition W_64930 : bv 32 := 0x199050ef.
Lemma F_64930 : fetch_word Asan.M.loaded_segments (0x64980 : word) = Some W_64930.
Proof. vm_refl. Qed.
Lemma D_64930 : decode_any W_64930 = Some (Jal 1 22936, 4%Z).
Proof. vm_refl. Qed.

Definition W_64934 : bv 32 := 0x00053483.
Lemma F_64934 : fetch_word Asan.M.loaded_segments (0x64984 : word) = Some W_64934.
Proof. vm_refl. Qed.
Lemma D_64934 : decode_any W_64934 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64938 : bv 32 := 0x08048863.
Lemma F_64938 : fetch_word Asan.M.loaded_segments (0x64988 : word) = Some W_64938.
Proof. vm_refl. Qed.
Lemma D_64938 : decode_any W_64938 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_6493c : bv 32 := 0x0604c503.
Lemma F_6493c : fetch_word Asan.M.loaded_segments (0x6498c : word) = Some W_6493c.
Proof. vm_refl. Qed.
Lemma D_6493c : decode_any W_6493c = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_64940 : bv 32 := 0x0584b903.
Lemma F_64940 : fetch_word Asan.M.loaded_segments (0x64990 : word) = Some W_64940.
Proof. vm_refl. Qed.
Lemma D_64940 : decode_any W_64940 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_64944 : bv 32 := 0x00050863.
Lemma F_64944 : fetch_word Asan.M.loaded_segments (0x64994 : word) = Some W_64944.
Proof. vm_refl. Qed.
Lemma D_64944 : decode_any W_64944 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64948 : bv 32 := 0x00048513.
Lemma F_64948 : fetch_word Asan.M.loaded_segments (0x64998 : word) = Some W_64948.
Proof. vm_refl. Qed.
Lemma D_64948 : decode_any W_64948 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6494c : bv 32 := 0x00040593.
Lemma F_6494c : fetch_word Asan.M.loaded_segments (0x6499c : word) = Some W_6494c.
Proof. vm_refl. Qed.
Lemma D_6494c : decode_any W_6494c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64950 : bv 32 := 0xa01ff0ef.
Lemma F_64950 : fetch_word Asan.M.loaded_segments (0x649a0 : word) = Some W_64950.
Proof. vm_refl. Qed.
Lemma D_64950 : decode_any W_64950 = Some (Jal 1 2095616, 4%Z).
Proof. vm_refl. Qed.

Definition W_64954 : bv 32 := 0xff990593.
Lemma F_64954 : fetch_word Asan.M.loaded_segments (0x649a4 : word) = Some W_64954.
Proof. vm_refl. Qed.
Lemma D_64954 : decode_any W_64954 = Some (OpImm ALU_ADD 11 18 4089, 4%Z).
Proof. vm_refl. Qed.

Definition W_64958 : bv 32 := 0x00100513.
Lemma F_64958 : fetch_word Asan.M.loaded_segments (0x649a8 : word) = Some W_64958.
Proof. vm_refl. Qed.
Lemma D_64958 : decode_any W_64958 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6495c : bv 32 := 0x00b51533.
Lemma F_6495c : fetch_word Asan.M.loaded_segments (0x649ac : word) = Some W_6495c.
Proof. vm_refl. Qed.
Lemma D_6495c : decode_any W_6495c = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_64960 : bv 32 := 0x0005061b.
Lemma F_64960 : fetch_word Asan.M.loaded_segments (0x649b0 : word) = Some W_64960.
Proof. vm_refl. Qed.
Lemma D_64960 : decode_any W_64960 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64964 : bv 32 := 0x08c05263.
Lemma F_64964 : fetch_word Asan.M.loaded_segments (0x649b4 : word) = Some W_64964.
Proof. vm_refl. Qed.
Lemma D_64964 : decode_any W_64964 = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_64968 : bv 32 := 0x000016b7.
Lemma F_64968 : fetch_word Asan.M.loaded_segments (0x649b8 : word) = Some W_64968.
Proof. vm_refl. Qed.
Lemma D_64968 : decode_any W_64968 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6496c : bv 32 := 0xff190613.
Lemma F_6496c : fetch_word Asan.M.loaded_segments (0x649bc : word) = Some W_6496c.
Proof. vm_refl. Qed.
Lemma D_6496c : decode_any W_6496c = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_64970 : bv 32 := 0x20000713.
Lemma F_64970 : fetch_word Asan.M.loaded_segments (0x649c0 : word) = Some W_64970.
Proof. vm_refl. Qed.
Lemma D_64970 : decode_any W_64970 = Some (OpImm ALU_ADD 14 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_64974 : bv 32 := 0xfff00793.
Lemma F_64974 : fetch_word Asan.M.loaded_segments (0x649c4 : word) = Some W_64974.
Proof. vm_refl. Qed.
Lemma D_64974 : decode_any W_64974 = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64978 : bv 32 := 0x00c71733.
Lemma F_64978 : fetch_word Asan.M.loaded_segments (0x649c8 : word) = Some W_64978.
Proof. vm_refl. Qed.
Lemma D_64978 : decode_any W_64978 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6497c : bv 32 := 0x0084b603.
Lemma F_6497c : fetch_word Asan.M.loaded_segments (0x649cc : word) = Some W_6497c.
Proof. vm_refl. Qed.
Lemma D_6497c : decode_any W_6497c = Some (Load SZ8 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64980 : bv 32 := 0x00b797b3.
Lemma F_64980 : fetch_word Asan.M.loaded_segments (0x649d0 : word) = Some W_64980.
Proof. vm_refl. Qed.
Lemma D_64980 : decode_any W_64980 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_64984 : bv 32 := 0xfff50813.
Lemma F_64984 : fetch_word Asan.M.loaded_segments (0x649d4 : word) = Some W_64984.
Proof. vm_refl. Qed.
Lemma D_64984 : decode_any W_64984 = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64988 : bv 32 := 0x00d485b3.
Lemma F_64988 : fetch_word Asan.M.loaded_segments (0x649d8 : word) = Some W_64988.
Proof. vm_refl. Qed.
Lemma D_64988 : decode_any W_64988 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6498c : bv 32 := 0x00e586b3.
Lemma F_6498c : fetch_word Asan.M.loaded_segments (0x649dc : word) = Some W_6498c.
Proof. vm_refl. Qed.
Lemma D_6498c : decode_any W_6498c = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_64990 : bv 32 := 0xfff7c713.
Lemma F_64990 : fetch_word Asan.M.loaded_segments (0x649e0 : word) = Some W_64990.
Proof. vm_refl. Qed.
Lemma D_64990 : decode_any W_64990 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64994 : bv 32 := 0x02081813.
Lemma F_64994 : fetch_word Asan.M.loaded_segments (0x649e4 : word) = Some W_64994.
Proof. vm_refl. Qed.
Lemma D_64994 : decode_any W_64994 = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64998 : bv 32 := 0x02085793.
Lemma F_64998 : fetch_word Asan.M.loaded_segments (0x649e8 : word) = Some W_64998.
Proof. vm_refl. Qed.
Lemma D_64998 : decode_any W_64998 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6499c : bv 32 := 0x00f607b3.
Lemma F_6499c : fetch_word Asan.M.loaded_segments (0x649ec : word) = Some W_6499c.
Proof. vm_refl. Qed.
Lemma D_6499c : decode_any W_6499c = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_649a0 : bv 32 := 0x00178813.
Lemma F_649a0 : fetch_word Asan.M.loaded_segments (0x649f0 : word) = Some W_649a0.
Proof. vm_refl. Qed.
Lemma D_649a0 : decode_any W_649a0 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_649a4 : bv 32 := 0x00e678b3.
Lemma F_649a4 : fetch_word Asan.M.loaded_segments (0x649f4 : word) = Some W_649a4.
Proof. vm_refl. Qed.
Lemma D_649a4 : decode_any W_649a4 = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_649a8 : bv 32 := 0x011687b3.
Lemma F_649a8 : fetch_word Asan.M.loaded_segments (0x649f8 : word) = Some W_649a8.
Proof. vm_refl. Qed.
Lemma D_649a8 : decode_any W_649a8 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_649ac : bv 32 := 0x0007c283.
Lemma F_649ac : fetch_word Asan.M.loaded_segments (0x649fc : word) = Some W_649ac.
Proof. vm_refl. Qed.
Lemma D_649ac : decode_any W_649ac = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_649b0 : bv 32 := 0x06028663.
Lemma F_649b0 : fetch_word Asan.M.loaded_segments (0x64a00 : word) = Some W_649b0.
Proof. vm_refl. Qed.
Lemma D_649b0 : decode_any W_649b0 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_649b4 : bv 32 := 0xfff5051b.
Lemma F_649b4 : fetch_word Asan.M.loaded_segments (0x64a04 : word) = Some W_649b4.
Proof. vm_refl. Qed.
Lemma D_649b4 : decode_any W_649b4 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_649b8 : bv 32 := 0x00160613.
Lemma F_649b8 : fetch_word Asan.M.loaded_segments (0x64a08 : word) = Some W_649b8.
Proof. vm_refl. Qed.
Lemma D_649b8 : decode_any W_649b8 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_649bc : bv 32 := 0xfe0514e3.
Lemma F_649bc : fetch_word Asan.M.loaded_segments (0x64a0c : word) = Some W_649bc.
Proof. vm_refl. Qed.
Lemma D_649bc : decode_any W_649bc = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a1c : bv 32 := 0x00160613.
Lemma F_64a1c : fetch_word Asan.M.loaded_segments (0x64a6c : word) = Some W_64a1c.
Proof. vm_refl. Qed.
Lemma D_64a1c : decode_any W_64a1c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a20 : bv 32 := 0x00100513.
Lemma F_64a20 : fetch_word Asan.M.loaded_segments (0x64a70 : word) = Some W_64a20.
Proof. vm_refl. Qed.
Lemma D_64a20 : decode_any W_64a20 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a24 : bv 32 := 0xffb90693.
Lemma F_64a24 : fetch_word Asan.M.loaded_segments (0x64a74 : word) = Some W_64a24.
Proof. vm_refl. Qed.
Lemma D_64a24 : decode_any W_64a24 = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a28 : bv 32 := 0x00789893.
Lemma F_64a28 : fetch_word Asan.M.loaded_segments (0x64a78 : word) = Some W_64a28.
Proof. vm_refl. Qed.
Lemma D_64a28 : decode_any W_64a28 = Some (ShiftImm ALU_SLL 17 17 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a2c : bv 32 := 0x00c4b423.
Lemma F_64a2c : fetch_word Asan.M.loaded_segments (0x64a7c : word) = Some W_64a2c.
Proof. vm_refl. Qed.
Lemma D_64a2c : decode_any W_64a2c = Some (Store SZ8 9 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a30 : bv 32 := 0x00a78023.
Lemma F_64a30 : fetch_word Asan.M.loaded_segments (0x64a80 : word) = Some W_64a30.
Proof. vm_refl. Qed.
Lemma D_64a30 : decode_any W_64a30 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a34 : bv 32 := 0x00d51633.
Lemma F_64a34 : fetch_word Asan.M.loaded_segments (0x64a84 : word) = Some W_64a34.
Proof. vm_refl. Qed.
Lemma D_64a34 : decode_any W_64a34 = Some (Op ALU_SLL 12 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a38 : bv 32 := 0x01251533.
Lemma F_64a38 : fetch_word Asan.M.loaded_segments (0x64a88 : word) = Some W_64a38.
Proof. vm_refl. Qed.
Lemma D_64a38 : decode_any W_64a38 = Some (Op ALU_SLL 10 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a3c : bv 32 := 0x00c585b3.
Lemma F_64a3c : fetch_word Asan.M.loaded_segments (0x64a8c : word) = Some W_64a3c.
Proof. vm_refl. Qed.
Lemma D_64a3c : decode_any W_64a3c = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a40 : bv 32 := 0x01150533.
Lemma F_64a40 : fetch_word Asan.M.loaded_segments (0x64a90 : word) = Some W_64a40.
Proof. vm_refl. Qed.
Lemma D_64a40 : decode_any W_64a40 = Some (Op ALU_ADD 10 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a44 : bv 32 := 0x00a584b3.
Lemma F_64a44 : fetch_word Asan.M.loaded_segments (0x64a94 : word) = Some W_64a44.
Proof. vm_refl. Qed.
Lemma D_64a44 : decode_any W_64a44 = Some (Op ALU_ADD 9 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a48 : bv 32 := 0x0084bc23.
Lemma F_64a48 : fetch_word Asan.M.loaded_segments (0x64a98 : word) = Some W_64a48.
Proof. vm_refl. Qed.
Lemma D_64a48 : decode_any W_64a48 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a4c : bv 32 := 0x06f4bc23.
Lemma F_64a4c : fetch_word Asan.M.loaded_segments (0x64a9c : word) = Some W_64a4c.
Proof. vm_refl. Qed.
Lemma D_64a4c : decode_any W_64a4c = Some (Store SZ8 9 15 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a50 : bv 32 := 0x00048513.
Lemma F_64a50 : fetch_word Asan.M.loaded_segments (0x64aa0 : word) = Some W_64a50.
Proof. vm_refl. Qed.
Lemma D_64a50 : decode_any W_64a50 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a54 : bv 32 := 0x021000ef.
Lemma F_64a54 : fetch_word Asan.M.loaded_segments (0x64aa4 : word) = Some W_64a54.
Proof. vm_refl. Qed.
Lemma D_64a54 : decode_any W_64a54 = Some (Jal 1 2080, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a58 : bv 32 := 0x00050593.
Lemma F_64a58 : fetch_word Asan.M.loaded_segments (0x64aa8 : word) = Some W_64a58.
Proof. vm_refl. Qed.
Lemma D_64a58 : decode_any W_64a58 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a5c : bv 32 := 0x00048513.
Lemma F_64a5c : fetch_word Asan.M.loaded_segments (0x64aac : word) = Some W_64a5c.
Proof. vm_refl. Qed.
Lemma D_64a5c : decode_any W_64a5c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a60 : bv 32 := 0x00000613.
Lemma F_64a60 : fetch_word Asan.M.loaded_segments (0x64ab0 : word) = Some W_64a60.
Proof. vm_refl. Qed.
Lemma D_64a60 : decode_any W_64a60 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a64 : bv 32 := 0x0005b023.
Lemma F_64a64 : fetch_word Asan.M.loaded_segments (0x64ab4 : word) = Some W_64a64.
Proof. vm_refl. Qed.
Lemma D_64a64 : decode_any W_64a64 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a68 : bv 32 := 0x0005b423.
Lemma F_64a68 : fetch_word Asan.M.loaded_segments (0x64ab8 : word) = Some W_64a68.
Proof. vm_refl. Qed.
Lemma D_64a68 : decode_any W_64a68 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a6c : bv 32 := 0x01813083.
Lemma F_64a6c : fetch_word Asan.M.loaded_segments (0x64abc : word) = Some W_64a6c.
Proof. vm_refl. Qed.
Lemma D_64a6c : decode_any W_64a6c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a70 : bv 32 := 0x01013403.
Lemma F_64a70 : fetch_word Asan.M.loaded_segments (0x64ac0 : word) = Some W_64a70.
Proof. vm_refl. Qed.
Lemma D_64a70 : decode_any W_64a70 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a74 : bv 32 := 0x00813483.
Lemma F_64a74 : fetch_word Asan.M.loaded_segments (0x64ac4 : word) = Some W_64a74.
Proof. vm_refl. Qed.
Lemma D_64a74 : decode_any W_64a74 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a78 : bv 32 := 0x00013903.
Lemma F_64a78 : fetch_word Asan.M.loaded_segments (0x64ac8 : word) = Some W_64a78.
Proof. vm_refl. Qed.
Lemma D_64a78 : decode_any W_64a78 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a7c : bv 32 := 0x02010113.
Lemma F_64a7c : fetch_word Asan.M.loaded_segments (0x64acc : word) = Some W_64a7c.
Proof. vm_refl. Qed.
Lemma D_64a7c : decode_any W_64a7c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a80 : bv 32 := 0x00008067.
Lemma F_64a80 : fetch_word Asan.M.loaded_segments (0x64ad0 : word) = Some W_64a80.
Proof. vm_refl. Qed.
Lemma D_64a80 : decode_any W_64a80 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c3c : bv 32 := 0xfe010113.
Lemma F_64c3c : fetch_word Asan.M.loaded_segments (0x64c8c : word) = Some W_64c3c.
Proof. vm_refl. Qed.
Lemma D_64c3c : decode_any W_64c3c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c40 : bv 32 := 0x00113c23.
Lemma F_64c40 : fetch_word Asan.M.loaded_segments (0x64c90 : word) = Some W_64c40.
Proof. vm_refl. Qed.
Lemma D_64c40 : decode_any W_64c40 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c44 : bv 32 := 0x00813823.
Lemma F_64c44 : fetch_word Asan.M.loaded_segments (0x64c94 : word) = Some W_64c44.
Proof. vm_refl. Qed.
Lemma D_64c44 : decode_any W_64c44 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c48 : bv 32 := 0x00913423.
Lemma F_64c48 : fetch_word Asan.M.loaded_segments (0x64c98 : word) = Some W_64c48.
Proof. vm_refl. Qed.
Lemma D_64c48 : decode_any W_64c48 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c4c : bv 32 := 0x01213023.
Lemma F_64c4c : fetch_word Asan.M.loaded_segments (0x64c9c : word) = Some W_64c4c.
Proof. vm_refl. Qed.
Lemma D_64c4c : decode_any W_64c4c = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c50 : bv 32 := 0x02010413.
Lemma F_64c50 : fetch_word Asan.M.loaded_segments (0x64ca0 : word) = Some W_64c50.
Proof. vm_refl. Qed.
Lemma D_64c50 : decode_any W_64c50 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c54 : bv 32 := 0x000f3517.
Lemma F_64c54 : fetch_word Asan.M.loaded_segments (0x64ca4 : word) = Some W_64c54.
Proof. vm_refl. Qed.
Lemma D_64c54 : decode_any W_64c54 = Some (Auipc 10 243, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c58 : bv 32 := 0xeec50513.
Lemma F_64c58 : fetch_word Asan.M.loaded_segments (0x64ca8 : word) = Some W_64c58.
Proof. vm_refl. Qed.
Lemma D_64c58 : decode_any W_64c58 = Some (OpImm ALU_ADD 10 10 3820, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c5c : bv 32 := 0x66c050ef.
Lemma F_64c5c : fetch_word Asan.M.loaded_segments (0x64cac : word) = Some W_64c5c.
Proof. vm_refl. Qed.
Lemma D_64c5c : decode_any W_64c5c = Some (Jal 1 22124, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c60 : bv 32 := 0x00053483.
Lemma F_64c60 : fetch_word Asan.M.loaded_segments (0x64cb0 : word) = Some W_64c60.
Proof. vm_refl. Qed.
Lemma D_64c60 : decode_any W_64c60 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c64 : bv 32 := 0x08048863.
Lemma F_64c64 : fetch_word Asan.M.loaded_segments (0x64cb4 : word) = Some W_64c64.
Proof. vm_refl. Qed.
Lemma D_64c64 : decode_any W_64c64 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c68 : bv 32 := 0x0604c503.
Lemma F_64c68 : fetch_word Asan.M.loaded_segments (0x64cb8 : word) = Some W_64c68.
Proof. vm_refl. Qed.
Lemma D_64c68 : decode_any W_64c68 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c6c : bv 32 := 0x0584b903.
Lemma F_64c6c : fetch_word Asan.M.loaded_segments (0x64cbc : word) = Some W_64c6c.
Proof. vm_refl. Qed.
Lemma D_64c6c : decode_any W_64c6c = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c70 : bv 32 := 0x00050863.
Lemma F_64c70 : fetch_word Asan.M.loaded_segments (0x64cc0 : word) = Some W_64c70.
Proof. vm_refl. Qed.
Lemma D_64c70 : decode_any W_64c70 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c74 : bv 32 := 0x00048513.
Lemma F_64c74 : fetch_word Asan.M.loaded_segments (0x64cc4 : word) = Some W_64c74.
Proof. vm_refl. Qed.
Lemma D_64c74 : decode_any W_64c74 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c78 : bv 32 := 0x00040593.
Lemma F_64c78 : fetch_word Asan.M.loaded_segments (0x64cc8 : word) = Some W_64c78.
Proof. vm_refl. Qed.
Lemma D_64c78 : decode_any W_64c78 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c7c : bv 32 := 0xed4ff0ef.
Lemma F_64c7c : fetch_word Asan.M.loaded_segments (0x64ccc : word) = Some W_64c7c.
Proof. vm_refl. Qed.
Lemma D_64c7c : decode_any W_64c7c = Some (Jal 1 2094804, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c80 : bv 32 := 0xff790593.
Lemma F_64c80 : fetch_word Asan.M.loaded_segments (0x64cd0 : word) = Some W_64c80.
Proof. vm_refl. Qed.
Lemma D_64c80 : decode_any W_64c80 = Some (OpImm ALU_ADD 11 18 4087, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c84 : bv 32 := 0x00100513.
Lemma F_64c84 : fetch_word Asan.M.loaded_segments (0x64cd4 : word) = Some W_64c84.
Proof. vm_refl. Qed.
Lemma D_64c84 : decode_any W_64c84 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c88 : bv 32 := 0x00b51533.
Lemma F_64c88 : fetch_word Asan.M.loaded_segments (0x64cd8 : word) = Some W_64c88.
Proof. vm_refl. Qed.
Lemma D_64c88 : decode_any W_64c88 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c8c : bv 32 := 0x0005061b.
Lemma F_64c8c : fetch_word Asan.M.loaded_segments (0x64cdc : word) = Some W_64c8c.
Proof. vm_refl. Qed.
Lemma D_64c8c : decode_any W_64c8c = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c90 : bv 32 := 0x08c05263.
Lemma F_64c90 : fetch_word Asan.M.loaded_segments (0x64ce0 : word) = Some W_64c90.
Proof. vm_refl. Qed.
Lemma D_64c90 : decode_any W_64c90 = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c94 : bv 32 := 0x000016b7.
Lemma F_64c94 : fetch_word Asan.M.loaded_segments (0x64ce4 : word) = Some W_64c94.
Proof. vm_refl. Qed.
Lemma D_64c94 : decode_any W_64c94 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c98 : bv 32 := 0xff190613.
Lemma F_64c98 : fetch_word Asan.M.loaded_segments (0x64ce8 : word) = Some W_64c98.
Proof. vm_refl. Qed.
Lemma D_64c98 : decode_any W_64c98 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c9c : bv 32 := 0x38000713.
Lemma F_64c9c : fetch_word Asan.M.loaded_segments (0x64cec : word) = Some W_64c9c.
Proof. vm_refl. Qed.
Lemma D_64c9c : decode_any W_64c9c = Some (OpImm ALU_ADD 14 0 896, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ca0 : bv 32 := 0xfff00793.
Lemma F_64ca0 : fetch_word Asan.M.loaded_segments (0x64cf0 : word) = Some W_64ca0.
Proof. vm_refl. Qed.
Lemma D_64ca0 : decode_any W_64ca0 = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ca4 : bv 32 := 0x00c71733.
Lemma F_64ca4 : fetch_word Asan.M.loaded_segments (0x64cf4 : word) = Some W_64ca4.
Proof. vm_refl. Qed.
Lemma D_64ca4 : decode_any W_64ca4 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ca8 : bv 32 := 0x0184b603.
Lemma F_64ca8 : fetch_word Asan.M.loaded_segments (0x64cf8 : word) = Some W_64ca8.
Proof. vm_refl. Qed.
Lemma D_64ca8 : decode_any W_64ca8 = Some (Load SZ8 true 12 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64cac : bv 32 := 0x00b797b3.
Lemma F_64cac : fetch_word Asan.M.loaded_segments (0x64cfc : word) = Some W_64cac.
Proof. vm_refl. Qed.
Lemma D_64cac : decode_any W_64cac = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_64cb0 : bv 32 := 0xfff50813.
Lemma F_64cb0 : fetch_word Asan.M.loaded_segments (0x64d00 : word) = Some W_64cb0.
Proof. vm_refl. Qed.
Lemma D_64cb0 : decode_any W_64cb0 = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64cb4 : bv 32 := 0x00d485b3.
Lemma F_64cb4 : fetch_word Asan.M.loaded_segments (0x64d04 : word) = Some W_64cb4.
Proof. vm_refl. Qed.
Lemma D_64cb4 : decode_any W_64cb4 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_64cb8 : bv 32 := 0x00e586b3.
Lemma F_64cb8 : fetch_word Asan.M.loaded_segments (0x64d08 : word) = Some W_64cb8.
Proof. vm_refl. Qed.
Lemma D_64cb8 : decode_any W_64cb8 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_64cbc : bv 32 := 0xfff7c713.
Lemma F_64cbc : fetch_word Asan.M.loaded_segments (0x64d0c : word) = Some W_64cbc.
Proof. vm_refl. Qed.
Lemma D_64cbc : decode_any W_64cbc = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64cc0 : bv 32 := 0x02081813.
Lemma F_64cc0 : fetch_word Asan.M.loaded_segments (0x64d10 : word) = Some W_64cc0.
Proof. vm_refl. Qed.
Lemma D_64cc0 : decode_any W_64cc0 = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64cc4 : bv 32 := 0x02085793.
Lemma F_64cc4 : fetch_word Asan.M.loaded_segments (0x64d14 : word) = Some W_64cc4.
Proof. vm_refl. Qed.
Lemma D_64cc4 : decode_any W_64cc4 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64cc8 : bv 32 := 0x00f607b3.
Lemma F_64cc8 : fetch_word Asan.M.loaded_segments (0x64d18 : word) = Some W_64cc8.
Proof. vm_refl. Qed.
Lemma D_64cc8 : decode_any W_64cc8 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ccc : bv 32 := 0x00178813.
Lemma F_64ccc : fetch_word Asan.M.loaded_segments (0x64d1c : word) = Some W_64ccc.
Proof. vm_refl. Qed.
Lemma D_64ccc : decode_any W_64ccc = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64cd0 : bv 32 := 0x00e678b3.
Lemma F_64cd0 : fetch_word Asan.M.loaded_segments (0x64d20 : word) = Some W_64cd0.
Proof. vm_refl. Qed.
Lemma D_64cd0 : decode_any W_64cd0 = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_64cd4 : bv 32 := 0x011687b3.
Lemma F_64cd4 : fetch_word Asan.M.loaded_segments (0x64d24 : word) = Some W_64cd4.
Proof. vm_refl. Qed.
Lemma D_64cd4 : decode_any W_64cd4 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_64cd8 : bv 32 := 0x0007c283.
Lemma F_64cd8 : fetch_word Asan.M.loaded_segments (0x64d28 : word) = Some W_64cd8.
Proof. vm_refl. Qed.
Lemma D_64cd8 : decode_any W_64cd8 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64cdc : bv 32 := 0x06028663.
Lemma F_64cdc : fetch_word Asan.M.loaded_segments (0x64d2c : word) = Some W_64cdc.
Proof. vm_refl. Qed.
Lemma D_64cdc : decode_any W_64cdc = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ce0 : bv 32 := 0xfff5051b.
Lemma F_64ce0 : fetch_word Asan.M.loaded_segments (0x64d30 : word) = Some W_64ce0.
Proof. vm_refl. Qed.
Lemma D_64ce0 : decode_any W_64ce0 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ce4 : bv 32 := 0x00160613.
Lemma F_64ce4 : fetch_word Asan.M.loaded_segments (0x64d34 : word) = Some W_64ce4.
Proof. vm_refl. Qed.
Lemma D_64ce4 : decode_any W_64ce4 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ce8 : bv 32 := 0xfe0514e3.
Lemma F_64ce8 : fetch_word Asan.M.loaded_segments (0x64d38 : word) = Some W_64ce8.
Proof. vm_refl. Qed.
Lemma D_64ce8 : decode_any W_64ce8 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d48 : bv 32 := 0x00160613.
Lemma F_64d48 : fetch_word Asan.M.loaded_segments (0x64d98 : word) = Some W_64d48.
Proof. vm_refl. Qed.
Lemma D_64d48 : decode_any W_64d48 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d4c : bv 32 := 0x00100513.
Lemma F_64d4c : fetch_word Asan.M.loaded_segments (0x64d9c : word) = Some W_64d4c.
Proof. vm_refl. Qed.
Lemma D_64d4c : decode_any W_64d4c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d50 : bv 32 := 0xffb90693.
Lemma F_64d50 : fetch_word Asan.M.loaded_segments (0x64da0 : word) = Some W_64d50.
Proof. vm_refl. Qed.
Lemma D_64d50 : decode_any W_64d50 = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d54 : bv 32 := 0x00c4bc23.
Lemma F_64d54 : fetch_word Asan.M.loaded_segments (0x64da4 : word) = Some W_64d54.
Proof. vm_refl. Qed.
Lemma D_64d54 : decode_any W_64d54 = Some (Store SZ8 9 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d58 : bv 32 := 0x00a78023.
Lemma F_64d58 : fetch_word Asan.M.loaded_segments (0x64da8 : word) = Some W_64d58.
Proof. vm_refl. Qed.
Lemma D_64d58 : decode_any W_64d58 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d5c : bv 32 := 0x00d51533.
Lemma F_64d5c : fetch_word Asan.M.loaded_segments (0x64dac : word) = Some W_64d5c.
Proof. vm_refl. Qed.
Lemma D_64d5c : decode_any W_64d5c = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d60 : bv 32 := 0x00300613.
Lemma F_64d60 : fetch_word Asan.M.loaded_segments (0x64db0 : word) = Some W_64d60.
Proof. vm_refl. Qed.
Lemma D_64d60 : decode_any W_64d60 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d64 : bv 32 := 0x00989893.
Lemma F_64d64 : fetch_word Asan.M.loaded_segments (0x64db4 : word) = Some W_64d64.
Proof. vm_refl. Qed.
Lemma D_64d64 : decode_any W_64d64 = Some (ShiftImm ALU_SLL 17 17 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d68 : bv 32 := 0x01261633.
Lemma F_64d68 : fetch_word Asan.M.loaded_segments (0x64db8 : word) = Some W_64d68.
Proof. vm_refl. Qed.
Lemma D_64d68 : decode_any W_64d68 = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d6c : bv 32 := 0x00a58533.
Lemma F_64d6c : fetch_word Asan.M.loaded_segments (0x64dbc : word) = Some W_64d6c.
Proof. vm_refl. Qed.
Lemma D_64d6c : decode_any W_64d6c = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d70 : bv 32 := 0x01160633.
Lemma F_64d70 : fetch_word Asan.M.loaded_segments (0x64dc0 : word) = Some W_64d70.
Proof. vm_refl. Qed.
Lemma D_64d70 : decode_any W_64d70 = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d74 : bv 32 := 0x00c504b3.
Lemma F_64d74 : fetch_word Asan.M.loaded_segments (0x64dc4 : word) = Some W_64d74.
Proof. vm_refl. Qed.
Lemma D_64d74 : decode_any W_64d74 = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d78 : bv 32 := 0x0084bc23.
Lemma F_64d78 : fetch_word Asan.M.loaded_segments (0x64dc8 : word) = Some W_64d78.
Proof. vm_refl. Qed.
Lemma D_64d78 : decode_any W_64d78 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d7c : bv 32 := 0x1ef4bc23.
Lemma F_64d7c : fetch_word Asan.M.loaded_segments (0x64dcc : word) = Some W_64d7c.
Proof. vm_refl. Qed.
Lemma D_64d7c : decode_any W_64d7c = Some (Store SZ8 9 15 504, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d80 : bv 32 := 0x00048513.
Lemma F_64d80 : fetch_word Asan.M.loaded_segments (0x64dd0 : word) = Some W_64d80.
Proof. vm_refl. Qed.
Lemma D_64d80 : decode_any W_64d80 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d84 : bv 32 := 0x4f0000ef.
Lemma F_64d84 : fetch_word Asan.M.loaded_segments (0x64dd4 : word) = Some W_64d84.
Proof. vm_refl. Qed.
Lemma D_64d84 : decode_any W_64d84 = Some (Jal 1 1264, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d88 : bv 32 := 0x00050593.
Lemma F_64d88 : fetch_word Asan.M.loaded_segments (0x64dd8 : word) = Some W_64d88.
Proof. vm_refl. Qed.
Lemma D_64d88 : decode_any W_64d88 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d8c : bv 32 := 0x00048513.
Lemma F_64d8c : fetch_word Asan.M.loaded_segments (0x64ddc : word) = Some W_64d8c.
Proof. vm_refl. Qed.
Lemma D_64d8c : decode_any W_64d8c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d90 : bv 32 := 0x00000613.
Lemma F_64d90 : fetch_word Asan.M.loaded_segments (0x64de0 : word) = Some W_64d90.
Proof. vm_refl. Qed.
Lemma D_64d90 : decode_any W_64d90 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d94 : bv 32 := 0x0005b023.
Lemma F_64d94 : fetch_word Asan.M.loaded_segments (0x64de4 : word) = Some W_64d94.
Proof. vm_refl. Qed.
Lemma D_64d94 : decode_any W_64d94 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d98 : bv 32 := 0x0005b423.
Lemma F_64d98 : fetch_word Asan.M.loaded_segments (0x64de8 : word) = Some W_64d98.
Proof. vm_refl. Qed.
Lemma D_64d98 : decode_any W_64d98 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d9c : bv 32 := 0x0005b823.
Lemma F_64d9c : fetch_word Asan.M.loaded_segments (0x64dec : word) = Some W_64d9c.
Proof. vm_refl. Qed.
Lemma D_64d9c : decode_any W_64d9c = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64da0 : bv 32 := 0x0005bc23.
Lemma F_64da0 : fetch_word Asan.M.loaded_segments (0x64df0 : word) = Some W_64da0.
Proof. vm_refl. Qed.
Lemma D_64da0 : decode_any W_64da0 = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64da4 : bv 32 := 0x0205b023.
Lemma F_64da4 : fetch_word Asan.M.loaded_segments (0x64df4 : word) = Some W_64da4.
Proof. vm_refl. Qed.
Lemma D_64da4 : decode_any W_64da4 = Some (Store SZ8 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64da8 : bv 32 := 0x0205b423.
Lemma F_64da8 : fetch_word Asan.M.loaded_segments (0x64df8 : word) = Some W_64da8.
Proof. vm_refl. Qed.
Lemma D_64da8 : decode_any W_64da8 = Some (Store SZ8 11 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_64dac : bv 32 := 0x0205b823.
Lemma F_64dac : fetch_word Asan.M.loaded_segments (0x64dfc : word) = Some W_64dac.
Proof. vm_refl. Qed.
Lemma D_64dac : decode_any W_64dac = Some (Store SZ8 11 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_64db0 : bv 32 := 0x0205bc23.
Lemma F_64db0 : fetch_word Asan.M.loaded_segments (0x64e00 : word) = Some W_64db0.
Proof. vm_refl. Qed.
Lemma D_64db0 : decode_any W_64db0 = Some (Store SZ8 11 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_64db4 : bv 32 := 0x01813083.
Lemma F_64db4 : fetch_word Asan.M.loaded_segments (0x64e04 : word) = Some W_64db4.
Proof. vm_refl. Qed.
Lemma D_64db4 : decode_any W_64db4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64db8 : bv 32 := 0x01013403.
Lemma F_64db8 : fetch_word Asan.M.loaded_segments (0x64e08 : word) = Some W_64db8.
Proof. vm_refl. Qed.
Lemma D_64db8 : decode_any W_64db8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64dbc : bv 32 := 0x00813483.
Lemma F_64dbc : fetch_word Asan.M.loaded_segments (0x64e0c : word) = Some W_64dbc.
Proof. vm_refl. Qed.
Lemma D_64dbc : decode_any W_64dbc = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64dc0 : bv 32 := 0x00013903.
Lemma F_64dc0 : fetch_word Asan.M.loaded_segments (0x64e10 : word) = Some W_64dc0.
Proof. vm_refl. Qed.
Lemma D_64dc0 : decode_any W_64dc0 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64dc4 : bv 32 := 0x02010113.
Lemma F_64dc4 : fetch_word Asan.M.loaded_segments (0x64e14 : word) = Some W_64dc4.
Proof. vm_refl. Qed.
Lemma D_64dc4 : decode_any W_64dc4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64dc8 : bv 32 := 0x00008067.
Lemma F_64dc8 : fetch_word Asan.M.loaded_segments (0x64e18 : word) = Some W_64dc8.
Proof. vm_refl. Qed.
Lemma D_64dc8 : decode_any W_64dc8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65274 : bv 32 := 0x000f2597.
Lemma F_65274 : fetch_word Asan.M.loaded_segments (0x652c4 : word) = Some W_65274.
Proof. vm_refl. Qed.
Lemma D_65274 : decode_any W_65274 = Some (Auipc 11 242, 4%Z).
Proof. vm_refl. Qed.

Definition W_65278 : bv 32 := 0xad45b583.
Lemma F_65278 : fetch_word Asan.M.loaded_segments (0x652c8 : word) = Some W_65278.
Proof. vm_refl. Qed.
Lemma D_65278 : decode_any W_65278 = Some (Load SZ8 true 11 11 2772, 4%Z).
Proof. vm_refl. Qed.

Definition W_6527c : bv 32 := 0x0005b583.
Lemma F_6527c : fetch_word Asan.M.loaded_segments (0x652cc : word) = Some W_6527c.
Proof. vm_refl. Qed.
Lemma D_6527c : decode_any W_6527c = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65280 : bv 32 := 0xfff58613.
Lemma F_65280 : fetch_word Asan.M.loaded_segments (0x652d0 : word) = Some W_65280.
Proof. vm_refl. Qed.
Lemma D_65280 : decode_any W_65280 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_65284 : bv 32 := 0x00c5b6b3.
Lemma F_65284 : fetch_word Asan.M.loaded_segments (0x652d4 : word) = Some W_65284.
Proof. vm_refl. Qed.
Lemma D_65284 : decode_any W_65284 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_65288 : bv 32 := 0xfff68693.
Lemma F_65288 : fetch_word Asan.M.loaded_segments (0x652d8 : word) = Some W_65288.
Proof. vm_refl. Qed.
Lemma D_65288 : decode_any W_65288 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6528c : bv 32 := 0x00c6f6b3.
Lemma F_6528c : fetch_word Asan.M.loaded_segments (0x652dc : word) = Some W_6528c.
Proof. vm_refl. Qed.
Lemma D_6528c : decode_any W_6528c = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_65290 : bv 32 := 0x04a6f263.
Lemma F_65290 : fetch_word Asan.M.loaded_segments (0x652e0 : word) = Some W_65290.
Proof. vm_refl. Qed.
Lemma D_65290 : decode_any W_65290 = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_65294 : bv 32 := 0x000f2697.
Lemma F_65294 : fetch_word Asan.M.loaded_segments (0x652e4 : word) = Some W_65294.
Proof. vm_refl. Qed.
Lemma D_65294 : decode_any W_65294 = Some (Auipc 13 242, 4%Z).
Proof. vm_refl. Qed.

Definition W_65298 : bv 32 := 0xabc6b683.
Lemma F_65298 : fetch_word Asan.M.loaded_segments (0x652e8 : word) = Some W_65298.
Proof. vm_refl. Qed.
Lemma D_65298 : decode_any W_65298 = Some (Load SZ8 true 13 13 2748, 4%Z).
Proof. vm_refl. Qed.

Definition W_6529c : bv 32 := 0x000f2717.
Lemma F_6529c : fetch_word Asan.M.loaded_segments (0x652ec : word) = Some W_6529c.
Proof. vm_refl. Qed.
Lemma D_6529c : decode_any W_6529c = Some (Auipc 14 242, 4%Z).
Proof. vm_refl. Qed.

Definition W_652a0 : bv 32 := 0xabc73703.
Lemma F_652a0 : fetch_word Asan.M.loaded_segments (0x652f0 : word) = Some W_652a0.
Proof. vm_refl. Qed.
Lemma D_652a0 : decode_any W_652a0 = Some (Load SZ8 true 14 14 2748, 4%Z).
Proof. vm_refl. Qed.

Definition W_652a4 : bv 32 := 0x0006b803.
Lemma F_652a4 : fetch_word Asan.M.loaded_segments (0x652f4 : word) = Some W_652a4.
Proof. vm_refl. Qed.
Lemma D_652a4 : decode_any W_652a4 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_652a8 : bv 32 := 0x00073683.
Lemma F_652a8 : fetch_word Asan.M.loaded_segments (0x652f8 : word) = Some W_652a8.
Proof. vm_refl. Qed.
Lemma D_652a8 : decode_any W_652a8 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_652ac : bv 32 := 0xfff80793.
Lemma F_652ac : fetch_word Asan.M.loaded_segments (0x652fc : word) = Some W_652ac.
Proof. vm_refl. Qed.
Lemma D_652ac : decode_any W_652ac = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_652b0 : bv 32 := 0x00a7f463.
Lemma F_652b0 : fetch_word Asan.M.loaded_segments (0x65300 : word) = Some W_652b0.
Proof. vm_refl. Qed.
Lemma D_652b0 : decode_any W_652b0 = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_652b8 : bv 32 := 0x000f2717.
Lemma F_652b8 : fetch_word Asan.M.loaded_segments (0x65308 : word) = Some W_652b8.
Proof. vm_refl. Qed.
Lemma D_652b8 : decode_any W_652b8 = Some (Auipc 14 242, 4%Z).
Proof. vm_refl. Qed.

Definition W_652bc : bv 32 := 0xaa873703.
Lemma F_652bc : fetch_word Asan.M.loaded_segments (0x6530c : word) = Some W_652bc.
Proof. vm_refl. Qed.
Lemma D_652bc : decode_any W_652bc = Some (Load SZ8 true 14 14 2728, 4%Z).
Proof. vm_refl. Qed.

Definition W_652c0 : bv 32 := 0x00073283.
Lemma F_652c0 : fetch_word Asan.M.loaded_segments (0x65310 : word) = Some W_652c0.
Proof. vm_refl. Qed.
Lemma D_652c0 : decode_any W_652c0 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_652c4 : bv 32 := 0x0032d713.
Lemma F_652c4 : fetch_word Asan.M.loaded_segments (0x65314 : word) = Some W_652c4.
Proof. vm_refl. Qed.
Lemma D_652c4 : decode_any W_652c4 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_652c8 : bv 32 := 0x00b708b3.
Lemma F_652c8 : fetch_word Asan.M.loaded_segments (0x65318 : word) = Some W_652c8.
Proof. vm_refl. Qed.
Lemma D_652c8 : decode_any W_652c8 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_652cc : bv 32 := 0x00a2ea63.
Lemma F_652cc : fetch_word Asan.M.loaded_segments (0x6531c : word) = Some W_652cc.
Proof. vm_refl. Qed.
Lemma D_652cc : decode_any W_652cc = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_652d0 : bv 32 := 0x00a8f863.
Lemma F_652d0 : fetch_word Asan.M.loaded_segments (0x65320 : word) = Some W_652d0.
Proof. vm_refl. Qed.
Lemma D_652d0 : decode_any W_652d0 = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_652d4 : bv 32 := 0x00355513.
Lemma F_652d4 : fetch_word Asan.M.loaded_segments (0x65324 : word) = Some W_652d4.
Proof. vm_refl. Qed.
Lemma D_652d4 : decode_any W_652d4 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_652d8 : bv 32 := 0x00a58533.
Lemma F_652d8 : fetch_word Asan.M.loaded_segments (0x65328 : word) = Some W_652d8.
Proof. vm_refl. Qed.
Lemma D_652d8 : decode_any W_652d8 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_652dc : bv 32 := 0x00008067.
Lemma F_652dc : fetch_word Asan.M.loaded_segments (0x6532c : word) = Some W_652dc.
Proof. vm_refl. Qed.
Lemma D_652dc : decode_any W_652dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r48448_48dd8.
Module Na0_code_r61de4_61ebc.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_82cd0 : bv 32 := 0xfb010113.
Lemma F_82cd0 : fetch_word Asan.M.loaded_segments (0x82d20 : word) = Some W_82cd0.
Proof. vm_refl. Qed.
Lemma D_82cd0 : decode_any W_82cd0 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_82cd4 : bv 32 := 0x04113423.
Lemma F_82cd4 : fetch_word Asan.M.loaded_segments (0x82d24 : word) = Some W_82cd4.
Proof. vm_refl. Qed.
Lemma D_82cd4 : decode_any W_82cd4 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_82cd8 : bv 32 := 0x04813023.
Lemma F_82cd8 : fetch_word Asan.M.loaded_segments (0x82d28 : word) = Some W_82cd8.
Proof. vm_refl. Qed.
Lemma D_82cd8 : decode_any W_82cd8 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_82cdc : bv 32 := 0x000d4517.
Lemma F_82cdc : fetch_word Asan.M.loaded_segments (0x82d2c : word) = Some W_82cdc.
Proof. vm_refl. Qed.
Lemma D_82cdc : decode_any W_82cdc = Some (Auipc 10 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ce0 : bv 32 := 0x0ac53503.
Lemma F_82ce0 : fetch_word Asan.M.loaded_segments (0x82d30 : word) = Some W_82ce0.
Proof. vm_refl. Qed.
Lemma D_82ce0 : decode_any W_82ce0 = Some (Load SZ8 true 10 10 172, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ce4 : bv 32 := 0x0a051463.
Lemma F_82ce4 : fetch_word Asan.M.loaded_segments (0x82d34 : word) = Some W_82ce4.
Proof. vm_refl. Qed.
Lemma D_82ce4 : decode_any W_82ce4 = Some (Branch BC_NE 10 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d8c : bv 32 := 0x00000513.
Lemma F_82d8c : fetch_word Asan.M.loaded_segments (0x82ddc : word) = Some W_82d8c.
Proof. vm_refl. Qed.
Lemma D_82d8c : decode_any W_82d8c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d90 : bv 32 := 0x04813083.
Lemma F_82d90 : fetch_word Asan.M.loaded_segments (0x82de0 : word) = Some W_82d90.
Proof. vm_refl. Qed.
Lemma D_82d90 : decode_any W_82d90 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d94 : bv 32 := 0x04013403.
Lemma F_82d94 : fetch_word Asan.M.loaded_segments (0x82de4 : word) = Some W_82d94.
Proof. vm_refl. Qed.
Lemma D_82d94 : decode_any W_82d94 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d98 : bv 32 := 0x05010113.
Lemma F_82d98 : fetch_word Asan.M.loaded_segments (0x82de8 : word) = Some W_82d98.
Proof. vm_refl. Qed.
Lemma D_82d98 : decode_any W_82d98 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_82d9c : bv 32 := 0x00008067.
Lemma F_82d9c : fetch_word Asan.M.loaded_segments (0x82dec : word) = Some W_82d9c.
Proof. vm_refl. Qed.
Lemma D_82d9c : decode_any W_82d9c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r61de4_61ebc.
Module Na0_code_r66f58_670bc.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_880c0 : bv 32 := 0xfb010113.
Lemma F_880c0 : fetch_word Asan.M.loaded_segments (0x88110 : word) = Some W_880c0.
Proof. vm_refl. Qed.
Lemma D_880c0 : decode_any W_880c0 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_880c4 : bv 32 := 0x04113423.
Lemma F_880c4 : fetch_word Asan.M.loaded_segments (0x88114 : word) = Some W_880c4.
Proof. vm_refl. Qed.
Lemma D_880c4 : decode_any W_880c4 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_880c8 : bv 32 := 0x04813023.
Lemma F_880c8 : fetch_word Asan.M.loaded_segments (0x88118 : word) = Some W_880c8.
Proof. vm_refl. Qed.
Lemma D_880c8 : decode_any W_880c8 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_880cc : bv 32 := 0x02913c23.
Lemma F_880cc : fetch_word Asan.M.loaded_segments (0x8811c : word) = Some W_880cc.
Proof. vm_refl. Qed.
Lemma D_880cc : decode_any W_880cc = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_880d0 : bv 32 := 0x03213823.
Lemma F_880d0 : fetch_word Asan.M.loaded_segments (0x88120 : word) = Some W_880d0.
Proof. vm_refl. Qed.
Lemma D_880d0 : decode_any W_880d0 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_880d4 : bv 32 := 0x03313423.
Lemma F_880d4 : fetch_word Asan.M.loaded_segments (0x88124 : word) = Some W_880d4.
Proof. vm_refl. Qed.
Lemma D_880d4 : decode_any W_880d4 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_880d8 : bv 32 := 0x000d8517.
Lemma F_880d8 : fetch_word Asan.M.loaded_segments (0x88128 : word) = Some W_880d8.
Proof. vm_refl. Qed.
Lemma D_880d8 : decode_any W_880d8 = Some (Auipc 10 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_880dc : bv 32 := 0x63050493.
Lemma F_880dc : fetch_word Asan.M.loaded_segments (0x8812c : word) = Some W_880dc.
Proof. vm_refl. Qed.
Lemma D_880dc : decode_any W_880dc = Some (OpImm ALU_ADD 9 10 1584, 4%Z).
Proof. vm_refl. Qed.

Definition W_880e0 : bv 32 := 0x00048503.
Lemma F_880e0 : fetch_word Asan.M.loaded_segments (0x88130 : word) = Some W_880e0.
Proof. vm_refl. Qed.
Lemma D_880e0 : decode_any W_880e0 = Some (Load SZ1 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_880e4 : bv 32 := 0x00100593.
Lemma F_880e4 : fetch_word Asan.M.loaded_segments (0x88134 : word) = Some W_880e4.
Proof. vm_refl. Qed.
Lemma D_880e4 : decode_any W_880e4 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_880e8 : bv 32 := 0x0230000f.
Lemma F_880e8 : fetch_word Asan.M.loaded_segments (0x88138 : word) = Some W_880e8.
Proof. vm_refl. Qed.
Lemma D_880e8 : decode_any W_880e8 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_880ec : bv 32 := 0x10b51e63.
Lemma F_880ec : fetch_word Asan.M.loaded_segments (0x8813c : word) = Some W_880ec.
Proof. vm_refl. Qed.
Lemma D_880ec : decode_any W_880ec = Some (Branch BC_NE 10 11 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_880f0 : bv 32 := 0xbe1fa0ef.
Lemma F_880f0 : fetch_word Asan.M.loaded_segments (0x88140 : word) = Some W_880f0.
Proof. vm_refl. Qed.
Lemma D_880f0 : decode_any W_880f0 = Some (Jal 1 2075616, 4%Z).
Proof. vm_refl. Qed.

Definition W_880f4 : bv 32 := 0x0e051663.
Lemma F_880f4 : fetch_word Asan.M.loaded_segments (0x88144 : word) = Some W_880f4.
Proof. vm_refl. Qed.
Lemma D_880f4 : decode_any W_880f4 = Some (Branch BC_NE 10 0 236, 4%Z).
Proof. vm_refl. Qed.

Definition W_880f8 : bv 32 := 0xfff88517.
Lemma F_880f8 : fetch_word Asan.M.loaded_segments (0x88148 : word) = Some W_880f8.
Proof. vm_refl. Qed.
Lemma D_880f8 : decode_any W_880f8 = Some (Auipc 10 1048456, 4%Z).
Proof. vm_refl. Qed.

Definition W_880fc : bv 32 := 0x34053403.
Lemma F_880fc : fetch_word Asan.M.loaded_segments (0x8814c : word) = Some W_880fc.
Proof. vm_refl. Qed.
Lemma D_880fc : decode_any W_880fc = Some (Load SZ8 true 8 10 832, 4%Z).
Proof. vm_refl. Qed.

Definition W_88100 : bv 32 := 0x02813023.
Lemma F_88100 : fetch_word Asan.M.loaded_segments (0x88150 : word) = Some W_88100.
Proof. vm_refl. Qed.
Lemma D_88100 : decode_any W_88100 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_88104 : bv 32 := 0x00813c23.
Lemma F_88104 : fetch_word Asan.M.loaded_segments (0x88154 : word) = Some W_88104.
Proof. vm_refl. Qed.
Lemma D_88104 : decode_any W_88104 = Some (Store SZ8 2 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_88108 : bv 32 := 0x6b4020ef.
Lemma F_88108 : fetch_word Asan.M.loaded_segments (0x88158 : word) = Some W_88108.
Proof. vm_refl. Qed.
Lemma D_88108 : decode_any W_88108 = Some (Jal 1 9908, 4%Z).
Proof. vm_refl. Qed.

Definition W_8810c : bv 32 := 0x08050263.
Lemma F_8810c : fetch_word Asan.M.loaded_segments (0x8815c : word) = Some W_8810c.
Proof. vm_refl. Qed.
Lemma D_8810c : decode_any W_8810c = Some (Branch BC_EQ 10 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_88110 : bv 32 := 0x000cf597.
Lemma F_88110 : fetch_word Asan.M.loaded_segments (0x88160 : word) = Some W_88110.
Proof. vm_refl. Qed.
Lemma D_88110 : decode_any W_88110 = Some (Auipc 11 207, 4%Z).
Proof. vm_refl. Qed.

Definition W_88114 : bv 32 := 0xc185b903.
Lemma F_88114 : fetch_word Asan.M.loaded_segments (0x88164 : word) = Some W_88114.
Proof. vm_refl. Qed.
Lemma D_88114 : decode_any W_88114 = Some (Load SZ8 true 18 11 3096, 4%Z).
Proof. vm_refl. Qed.

Definition W_88118 : bv 32 := 0x00093403.
Lemma F_88118 : fetch_word Asan.M.loaded_segments (0x88168 : word) = Some W_88118.
Proof. vm_refl. Qed.
Lemma D_88118 : decode_any W_88118 = Some (Load SZ8 true 8 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8811c : bv 32 := 0x00041c63.
Lemma F_8811c : fetch_word Asan.M.loaded_segments (0x8816c : word) = Some W_8811c.
Proof. vm_refl. Qed.
Lemma D_8811c : decode_any W_8811c = Some (Branch BC_NE 8 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_88134 : bv 32 := 0x04d020ef.
Lemma F_88134 : fetch_word Asan.M.loaded_segments (0x88184 : word) = Some W_88134.
Proof. vm_refl. Qed.
Lemma D_88134 : decode_any W_88134 = Some (Jal 1 10316, 4%Z).
Proof. vm_refl. Qed.

Definition W_88138 : bv 32 := 0x00050613.
Lemma F_88138 : fetch_word Asan.M.loaded_segments (0x88188 : word) = Some W_88138.
Proof. vm_refl. Qed.
Lemma D_88138 : decode_any W_88138 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8813c : bv 32 := 0x00a13c23.
Lemma F_8813c : fetch_word Asan.M.loaded_segments (0x8818c : word) = Some W_8813c.
Proof. vm_refl. Qed.
Lemma D_8813c : decode_any W_8813c = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_88140 : bv 32 := 0x01010513.
Lemma F_88140 : fetch_word Asan.M.loaded_segments (0x88190 : word) = Some W_88140.
Proof. vm_refl. Qed.
Lemma D_88140 : decode_any W_88140 = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_88144 : bv 32 := 0x40850533.
Lemma F_88144 : fetch_word Asan.M.loaded_segments (0x88194 : word) = Some W_88144.
Proof. vm_refl. Qed.
Lemma D_88144 : decode_any W_88144 = Some (Op ALU_SUB 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_88148 : bv 32 := 0x408006b3.
Lemma F_88148 : fetch_word Asan.M.loaded_segments (0x88198 : word) = Some W_88148.
Proof. vm_refl. Qed.
Lemma D_88148 : decode_any W_88148 = Some (Op ALU_SUB 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8814c : bv 32 := 0x00d576b3.
Lemma F_8814c : fetch_word Asan.M.loaded_segments (0x8819c : word) = Some W_8814c.
Proof. vm_refl. Qed.
Lemma D_8814c : decode_any W_8814c = Some (Op ALU_AND 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_88150 : bv 32 := 0x02d13023.
Lemma F_88150 : fetch_word Asan.M.loaded_segments (0x881a0 : word) = Some W_88150.
Proof. vm_refl. Qed.
Lemma D_88150 : decode_any W_88150 = Some (Store SZ8 2 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_88154 : bv 32 := 0x40d60733.
Lemma F_88154 : fetch_word Asan.M.loaded_segments (0x881a4 : word) = Some W_88154.
Proof. vm_refl. Qed.
Lemma D_88154 : decode_any W_88154 = Some (Op ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_88158 : bv 32 := 0x04000537.
Lemma F_88158 : fetch_word Asan.M.loaded_segments (0x881a8 : word) = Some W_88158.
Proof. vm_refl. Qed.
Lemma D_88158 : decode_any W_88158 = Some (Lui 10 16384, 4%Z).
Proof. vm_refl. Qed.

Definition W_8815c : bv 32 := 0x0015051b.
Lemma F_8815c : fetch_word Asan.M.loaded_segments (0x881ac : word) = Some W_8815c.
Proof. vm_refl. Qed.
Lemma D_8815c : decode_any W_8815c = Some (OpImm32 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_88160 : bv 32 := 0x06a76263.
Lemma F_88160 : fetch_word Asan.M.loaded_segments (0x881b0 : word) = Some W_88160.
Proof. vm_refl. Qed.
Lemma D_88160 : decode_any W_88160 = Some (Branch BC_LTU 14 10 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_881c4 : bv 32 := 0x00770713.
Lemma F_881c4 : fetch_word Asan.M.loaded_segments (0x88214 : word) = Some W_881c4.
Proof. vm_refl. Qed.
Lemma D_881c4 : decode_any W_881c4 = Some (OpImm ALU_ADD 14 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_881c8 : bv 32 := 0x10000537.
Lemma F_881c8 : fetch_word Asan.M.loaded_segments (0x88218 : word) = Some W_881c8.
Proof. vm_refl. Qed.
Lemma D_881c8 : decode_any W_881c8 = Some (Lui 10 65536, 4%Z).
Proof. vm_refl. Qed.

Definition W_881cc : bv 32 := 0xff85051b.
Lemma F_881cc : fetch_word Asan.M.loaded_segments (0x8821c : word) = Some W_881cc.
Proof. vm_refl. Qed.
Lemma D_881cc : decode_any W_881cc = Some (OpImm32 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_881d0 : bv 32 := 0x00a775b3.
Lemma F_881d0 : fetch_word Asan.M.loaded_segments (0x88220 : word) = Some W_881d0.
Proof. vm_refl. Qed.
Lemma D_881d0 : decode_any W_881d0 = Some (Op ALU_AND 11 14 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_881d4 : bv 32 := 0x00068513.
Lemma F_881d4 : fetch_word Asan.M.loaded_segments (0x88224 : word) = Some W_881d4.
Proof. vm_refl. Qed.
Lemma D_881d4 : decode_any W_881d4 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_881d8 : bv 32 := 0x00000613.
Lemma F_881d8 : fetch_word Asan.M.loaded_segments (0x88228 : word) = Some W_881d8.
Proof. vm_refl. Qed.
Lemma D_881d8 : decode_any W_881d8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_881dc : bv 32 := 0x835f90ef.
Lemma F_881dc : fetch_word Asan.M.loaded_segments (0x8822c : word) = Some W_881dc.
Proof. vm_refl. Qed.
Lemma D_881dc : decode_any W_881dc = Some (Jal 1 2070580, 4%Z).
Proof. vm_refl. Qed.

Definition W_881e0 : bv 32 := 0x5dc020ef.
Lemma F_881e0 : fetch_word Asan.M.loaded_segments (0x88230 : word) = Some W_881e0.
Proof. vm_refl. Qed.
Lemma D_881e0 : decode_any W_881e0 = Some (Jal 1 9692, 4%Z).
Proof. vm_refl. Qed.

Definition W_881e4 : bv 32 := 0x02050263.
Lemma F_881e4 : fetch_word Asan.M.loaded_segments (0x88234 : word) = Some W_881e4.
Proof. vm_refl. Qed.
Lemma D_881e4 : decode_any W_881e4 = Some (Branch BC_EQ 10 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_881e8 : bv 32 := 0x02850583.
Lemma F_881e8 : fetch_word Asan.M.loaded_segments (0x88238 : word) = Some W_881e8.
Proof. vm_refl. Qed.
Lemma D_881e8 : decode_any W_881e8 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_881ec : bv 32 := 0x00059e63.
Lemma F_881ec : fetch_word Asan.M.loaded_segments (0x8823c : word) = Some W_881ec.
Proof. vm_refl. Qed.
Lemma D_881ec : decode_any W_881ec = Some (Branch BC_NE 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_881f0 : bv 32 := 0x04853503.
Lemma F_881f0 : fetch_word Asan.M.loaded_segments (0x88240 : word) = Some W_881f0.
Proof. vm_refl. Qed.
Lemma D_881f0 : decode_any W_881f0 = Some (Load SZ8 true 10 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_881f4 : bv 32 := 0x00253593.
Lemma F_881f4 : fetch_word Asan.M.loaded_segments (0x88244 : word) = Some W_881f4.
Proof. vm_refl. Qed.
Lemma D_881f4 : decode_any W_881f4 = Some (OpImm ALU_SLTU 11 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_881f8 : bv 32 := 0xfff58593.
Lemma F_881f8 : fetch_word Asan.M.loaded_segments (0x88248 : word) = Some W_881f8.
Proof. vm_refl. Qed.
Lemma D_881f8 : decode_any W_881f8 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_881fc : bv 32 := 0x00a5f533.
Lemma F_881fc : fetch_word Asan.M.loaded_segments (0x8824c : word) = Some W_881fc.
Proof. vm_refl. Qed.
Lemma D_881fc : decode_any W_881fc = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_88200 : bv 32 := 0x00050463.
Lemma F_88200 : fetch_word Asan.M.loaded_segments (0x88250 : word) = Some W_88200.
Proof. vm_refl. Qed.
Lemma D_88200 : decode_any W_88200 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_88204 : bv 32 := 0xc34dc0ef.
Lemma F_88204 : fetch_word Asan.M.loaded_segments (0x88254 : word) = Some W_88204.
Proof. vm_refl. Qed.
Lemma D_88204 : decode_any W_88204 = Some (Jal 1 1950772, 4%Z).
Proof. vm_refl. Qed.

Definition W_88208 : bv 32 := 0x04813083.
Lemma F_88208 : fetch_word Asan.M.loaded_segments (0x88258 : word) = Some W_88208.
Proof. vm_refl. Qed.
Lemma D_88208 : decode_any W_88208 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_8820c : bv 32 := 0x04013403.
Lemma F_8820c : fetch_word Asan.M.loaded_segments (0x8825c : word) = Some W_8820c.
Proof. vm_refl. Qed.
Lemma D_8820c : decode_any W_8820c = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_88210 : bv 32 := 0x03813483.
Lemma F_88210 : fetch_word Asan.M.loaded_segments (0x88260 : word) = Some W_88210.
Proof. vm_refl. Qed.
Lemma D_88210 : decode_any W_88210 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_88214 : bv 32 := 0x03013903.
Lemma F_88214 : fetch_word Asan.M.loaded_segments (0x88264 : word) = Some W_88214.
Proof. vm_refl. Qed.
Lemma D_88214 : decode_any W_88214 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_88218 : bv 32 := 0x02813983.
Lemma F_88218 : fetch_word Asan.M.loaded_segments (0x88268 : word) = Some W_88218.
Proof. vm_refl. Qed.
Lemma D_88218 : decode_any W_88218 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8821c : bv 32 := 0x05010113.
Lemma F_8821c : fetch_word Asan.M.loaded_segments (0x8826c : word) = Some W_8821c.
Proof. vm_refl. Qed.
Lemma D_8821c : decode_any W_8821c = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_88220 : bv 32 := 0x00008067.
Lemma F_88220 : fetch_word Asan.M.loaded_segments (0x88270 : word) = Some W_88220.
Proof. vm_refl. Qed.
Lemma D_88220 : decode_any W_88220 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r66f58_670bc.
Module Na0_code_r5d100_5d274.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6479c : bv 32 := 0xfe010113.
Lemma F_6479c : fetch_word Asan.M.loaded_segments (0x647ec : word) = Some W_6479c.
Proof. vm_refl. Qed.
Lemma D_6479c : decode_any W_6479c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_647a0 : bv 32 := 0x00113c23.
Lemma F_647a0 : fetch_word Asan.M.loaded_segments (0x647f0 : word) = Some W_647a0.
Proof. vm_refl. Qed.
Lemma D_647a0 : decode_any W_647a0 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_647a4 : bv 32 := 0x00813823.
Lemma F_647a4 : fetch_word Asan.M.loaded_segments (0x647f4 : word) = Some W_647a4.
Proof. vm_refl. Qed.
Lemma D_647a4 : decode_any W_647a4 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_647a8 : bv 32 := 0x00913423.
Lemma F_647a8 : fetch_word Asan.M.loaded_segments (0x647f8 : word) = Some W_647a8.
Proof. vm_refl. Qed.
Lemma D_647a8 : decode_any W_647a8 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_647ac : bv 32 := 0x01213023.
Lemma F_647ac : fetch_word Asan.M.loaded_segments (0x647fc : word) = Some W_647ac.
Proof. vm_refl. Qed.
Lemma D_647ac : decode_any W_647ac = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_647b0 : bv 32 := 0x02010413.
Lemma F_647b0 : fetch_word Asan.M.loaded_segments (0x64800 : word) = Some W_647b0.
Proof. vm_refl. Qed.
Lemma D_647b0 : decode_any W_647b0 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_647b4 : bv 32 := 0x000f3517.
Lemma F_647b4 : fetch_word Asan.M.loaded_segments (0x64804 : word) = Some W_647b4.
Proof. vm_refl. Qed.
Lemma D_647b4 : decode_any W_647b4 = Some (Auipc 10 243, 4%Z).
Proof. vm_refl. Qed.

Definition W_647b8 : bv 32 := 0x38c50513.
Lemma F_647b8 : fetch_word Asan.M.loaded_segments (0x64808 : word) = Some W_647b8.
Proof. vm_refl. Qed.
Lemma D_647b8 : decode_any W_647b8 = Some (OpImm ALU_ADD 10 10 908, 4%Z).
Proof. vm_refl. Qed.

Definition W_647bc : bv 32 := 0x30d050ef.
Lemma F_647bc : fetch_word Asan.M.loaded_segments (0x6480c : word) = Some W_647bc.
Proof. vm_refl. Qed.
Lemma D_647bc : decode_any W_647bc = Some (Jal 1 23308, 4%Z).
Proof. vm_refl. Qed.

Definition W_647c0 : bv 32 := 0x00053483.
Lemma F_647c0 : fetch_word Asan.M.loaded_segments (0x64810 : word) = Some W_647c0.
Proof. vm_refl. Qed.
Lemma D_647c0 : decode_any W_647c0 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_647c4 : bv 32 := 0x08048063.
Lemma F_647c4 : fetch_word Asan.M.loaded_segments (0x64814 : word) = Some W_647c4.
Proof. vm_refl. Qed.
Lemma D_647c4 : decode_any W_647c4 = Some (Branch BC_EQ 9 0 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_647c8 : bv 32 := 0x0604c503.
Lemma F_647c8 : fetch_word Asan.M.loaded_segments (0x64818 : word) = Some W_647c8.
Proof. vm_refl. Qed.
Lemma D_647c8 : decode_any W_647c8 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_647cc : bv 32 := 0x0584b903.
Lemma F_647cc : fetch_word Asan.M.loaded_segments (0x6481c : word) = Some W_647cc.
Proof. vm_refl. Qed.
Lemma D_647cc : decode_any W_647cc = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_647d0 : bv 32 := 0x00050863.
Lemma F_647d0 : fetch_word Asan.M.loaded_segments (0x64820 : word) = Some W_647d0.
Proof. vm_refl. Qed.
Lemma D_647d0 : decode_any W_647d0 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_647d4 : bv 32 := 0x00048513.
Lemma F_647d4 : fetch_word Asan.M.loaded_segments (0x64824 : word) = Some W_647d4.
Proof. vm_refl. Qed.
Lemma D_647d4 : decode_any W_647d4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_647d8 : bv 32 := 0x00040593.
Lemma F_647d8 : fetch_word Asan.M.loaded_segments (0x64828 : word) = Some W_647d8.
Proof. vm_refl. Qed.
Lemma D_647d8 : decode_any W_647d8 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_647dc : bv 32 := 0xb75ff0ef.
Lemma F_647dc : fetch_word Asan.M.loaded_segments (0x6482c : word) = Some W_647dc.
Proof. vm_refl. Qed.
Lemma D_647dc : decode_any W_647dc = Some (Jal 1 2095988, 4%Z).
Proof. vm_refl. Qed.

Definition W_647e0 : bv 32 := 0xffa90593.
Lemma F_647e0 : fetch_word Asan.M.loaded_segments (0x64830 : word) = Some W_647e0.
Proof. vm_refl. Qed.
Lemma D_647e0 : decode_any W_647e0 = Some (OpImm ALU_ADD 11 18 4090, 4%Z).
Proof. vm_refl. Qed.

Definition W_647e4 : bv 32 := 0x00100513.
Lemma F_647e4 : fetch_word Asan.M.loaded_segments (0x64834 : word) = Some W_647e4.
Proof. vm_refl. Qed.
Lemma D_647e4 : decode_any W_647e4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_647e8 : bv 32 := 0x00b51533.
Lemma F_647e8 : fetch_word Asan.M.loaded_segments (0x64838 : word) = Some W_647e8.
Proof. vm_refl. Qed.
Lemma D_647e8 : decode_any W_647e8 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_647ec : bv 32 := 0x0005061b.
Lemma F_647ec : fetch_word Asan.M.loaded_segments (0x6483c : word) = Some W_647ec.
Proof. vm_refl. Qed.
Lemma D_647ec : decode_any W_647ec = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_647f0 : bv 32 := 0x06c05a63.
Lemma F_647f0 : fetch_word Asan.M.loaded_segments (0x64840 : word) = Some W_647f0.
Proof. vm_refl. Qed.
Lemma D_647f0 : decode_any W_647f0 = Some (Branch BC_GE 0 12 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_647f4 : bv 32 := 0x000016b7.
Lemma F_647f4 : fetch_word Asan.M.loaded_segments (0x64844 : word) = Some W_647f4.
Proof. vm_refl. Qed.
Lemma D_647f4 : decode_any W_647f4 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_647f8 : bv 32 := 0xfff00713.
Lemma F_647f8 : fetch_word Asan.M.loaded_segments (0x64848 : word) = Some W_647f8.
Proof. vm_refl. Qed.
Lemma D_647f8 : decode_any W_647f8 = Some (OpImm ALU_ADD 14 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_647fc : bv 32 := 0x0004b603.
Lemma F_647fc : fetch_word Asan.M.loaded_segments (0x6484c : word) = Some W_647fc.
Proof. vm_refl. Qed.
Lemma D_647fc : decode_any W_647fc = Some (Load SZ8 true 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64800 : bv 32 := 0x00b71733.
Lemma F_64800 : fetch_word Asan.M.loaded_segments (0x64850 : word) = Some W_64800.
Proof. vm_refl. Qed.
Lemma D_64800 : decode_any W_64800 = Some (Op ALU_SLL 14 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_64804 : bv 32 := 0xfff50793.
Lemma F_64804 : fetch_word Asan.M.loaded_segments (0x64854 : word) = Some W_64804.
Proof. vm_refl. Qed.
Lemma D_64804 : decode_any W_64804 = Some (OpImm ALU_ADD 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64808 : bv 32 := 0x00d485b3.
Lemma F_64808 : fetch_word Asan.M.loaded_segments (0x64858 : word) = Some W_64808.
Proof. vm_refl. Qed.
Lemma D_64808 : decode_any W_64808 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6480c : bv 32 := 0xfff74693.
Lemma F_6480c : fetch_word Asan.M.loaded_segments (0x6485c : word) = Some W_6480c.
Proof. vm_refl. Qed.
Lemma D_6480c : decode_any W_6480c = Some (OpImm ALU_XOR 13 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64810 : bv 32 := 0x02079793.
Lemma F_64810 : fetch_word Asan.M.loaded_segments (0x64860 : word) = Some W_64810.
Proof. vm_refl. Qed.
Lemma D_64810 : decode_any W_64810 = Some (ShiftImm ALU_SLL 15 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64814 : bv 32 := 0x0207d793.
Lemma F_64814 : fetch_word Asan.M.loaded_segments (0x64864 : word) = Some W_64814.
Proof. vm_refl. Qed.
Lemma D_64814 : decode_any W_64814 = Some (ShiftImm ALU_SRL 15 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64818 : bv 32 := 0x00f60733.
Lemma F_64818 : fetch_word Asan.M.loaded_segments (0x64868 : word) = Some W_64818.
Proof. vm_refl. Qed.
Lemma D_64818 : decode_any W_64818 = Some (Op ALU_ADD 14 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_6481c : bv 32 := 0x00170713.
Lemma F_6481c : fetch_word Asan.M.loaded_segments (0x6486c : word) = Some W_6481c.
Proof. vm_refl. Qed.
Lemma D_6481c : decode_any W_6481c = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64820 : bv 32 := 0x00d67833.
Lemma F_64820 : fetch_word Asan.M.loaded_segments (0x64870 : word) = Some W_64820.
Proof. vm_refl. Qed.
Lemma D_64820 : decode_any W_64820 = Some (Op ALU_AND 16 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_64824 : bv 32 := 0x010587b3.
Lemma F_64824 : fetch_word Asan.M.loaded_segments (0x64874 : word) = Some W_64824.
Proof. vm_refl. Qed.
Lemma D_64824 : decode_any W_64824 = Some (Op ALU_ADD 15 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64828 : bv 32 := 0x0007c883.
Lemma F_64828 : fetch_word Asan.M.loaded_segments (0x64878 : word) = Some W_64828.
Proof. vm_refl. Qed.
Lemma D_64828 : decode_any W_64828 = Some (Load SZ1 false 17 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6482c : bv 32 := 0x06088663.
Lemma F_6482c : fetch_word Asan.M.loaded_segments (0x6487c : word) = Some W_6482c.
Proof. vm_refl. Qed.
Lemma D_6482c : decode_any W_6482c = Some (Branch BC_EQ 17 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_64830 : bv 32 := 0xfff5051b.
Lemma F_64830 : fetch_word Asan.M.loaded_segments (0x64880 : word) = Some W_64830.
Proof. vm_refl. Qed.
Lemma D_64830 : decode_any W_64830 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64834 : bv 32 := 0x00160613.
Lemma F_64834 : fetch_word Asan.M.loaded_segments (0x64884 : word) = Some W_64834.
Proof. vm_refl. Qed.
Lemma D_64834 : decode_any W_64834 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64838 : bv 32 := 0xfe0514e3.
Lemma F_64838 : fetch_word Asan.M.loaded_segments (0x64888 : word) = Some W_64838.
Proof. vm_refl. Qed.
Lemma D_64838 : decode_any W_64838 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_6483c : bv 32 := 0x00e4b023.
Lemma F_6483c : fetch_word Asan.M.loaded_segments (0x6488c : word) = Some W_6483c.
Proof. vm_refl. Qed.
Lemma D_6483c : decode_any W_6483c = Some (Store SZ8 9 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64840 : bv 32 := 0x0400006f.
Lemma F_64840 : fetch_word Asan.M.loaded_segments (0x64890 : word) = Some W_64840.
Proof. vm_refl. Qed.
Lemma D_64840 : decode_any W_64840 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_64844 : bv 32 := 0x000f2517.
Lemma F_64844 : fetch_word Asan.M.loaded_segments (0x64894 : word) = Some W_64844.
Proof. vm_refl. Qed.
Lemma D_64844 : decode_any W_64844 = Some (Auipc 10 242, 4%Z).
Proof. vm_refl. Qed.

Definition W_64848 : bv 32 := 0x55c53503.
Lemma F_64848 : fetch_word Asan.M.loaded_segments (0x64898 : word) = Some W_64848.
Proof. vm_refl. Qed.
Lemma D_64848 : decode_any W_64848 = Some (Load SZ8 true 10 10 1372, 4%Z).
Proof. vm_refl. Qed.

Definition W_6484c : bv 32 := 0x00052503.
Lemma F_6484c : fetch_word Asan.M.loaded_segments (0x6489c : word) = Some W_6484c.
Proof. vm_refl. Qed.
Lemma D_6484c : decode_any W_6484c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64850 : bv 32 := 0x02050863.
Lemma F_64850 : fetch_word Asan.M.loaded_segments (0x648a0 : word) = Some W_64850.
Proof. vm_refl. Qed.
Lemma D_64850 : decode_any W_64850 = Some (Branch BC_EQ 10 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_64854 : bv 32 := 0x769250ef.
Lemma F_64854 : fetch_word Asan.M.loaded_segments (0x648a4 : word) = Some W_64854.
Proof. vm_refl. Qed.
Lemma D_64854 : decode_any W_64854 = Some (Jal 1 155496, 4%Z).
Proof. vm_refl. Qed.

Definition W_64858 : bv 32 := 0x02050463.
Lemma F_64858 : fetch_word Asan.M.loaded_segments (0x648a8 : word) = Some W_64858.
Proof. vm_refl. Qed.
Lemma D_64858 : decode_any W_64858 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_6485c : bv 32 := 0x02850583.
Lemma F_6485c : fetch_word Asan.M.loaded_segments (0x648ac : word) = Some W_6485c.
Proof. vm_refl. Qed.
Lemma D_6485c : decode_any W_6485c = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_64860 : bv 32 := 0x08058a63.
Lemma F_64860 : fetch_word Asan.M.loaded_segments (0x648b0 : word) = Some W_64860.
Proof. vm_refl. Qed.
Lemma D_64860 : decode_any W_64860 = Some (Branch BC_EQ 11 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_64864 : bv 32 := 0x00000513.
Lemma F_64864 : fetch_word Asan.M.loaded_segments (0x648b4 : word) = Some W_64864.
Proof. vm_refl. Qed.
Lemma D_64864 : decode_any W_64864 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64868 : bv 32 := 0x01813083.
Lemma F_64868 : fetch_word Asan.M.loaded_segments (0x648b8 : word) = Some W_64868.
Proof. vm_refl. Qed.
Lemma D_64868 : decode_any W_64868 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6486c : bv 32 := 0x01013403.
Lemma F_6486c : fetch_word Asan.M.loaded_segments (0x648bc : word) = Some W_6486c.
Proof. vm_refl. Qed.
Lemma D_6486c : decode_any W_6486c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64870 : bv 32 := 0x00813483.
Lemma F_64870 : fetch_word Asan.M.loaded_segments (0x648c0 : word) = Some W_64870.
Proof. vm_refl. Qed.
Lemma D_64870 : decode_any W_64870 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64874 : bv 32 := 0x00013903.
Lemma F_64874 : fetch_word Asan.M.loaded_segments (0x648c4 : word) = Some W_64874.
Proof. vm_refl. Qed.
Lemma D_64874 : decode_any W_64874 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64878 : bv 32 := 0x02010113.
Lemma F_64878 : fetch_word Asan.M.loaded_segments (0x648c8 : word) = Some W_64878.
Proof. vm_refl. Qed.
Lemma D_64878 : decode_any W_64878 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6487c : bv 32 := 0x00008067.
Lemma F_6487c : fetch_word Asan.M.loaded_segments (0x648cc : word) = Some W_6487c.
Proof. vm_refl. Qed.
Lemma D_6487c : decode_any W_6487c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64880 : bv 32 := 0x01813083.
Lemma F_64880 : fetch_word Asan.M.loaded_segments (0x648d0 : word) = Some W_64880.
Proof. vm_refl. Qed.
Lemma D_64880 : decode_any W_64880 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64884 : bv 32 := 0x01013403.
Lemma F_64884 : fetch_word Asan.M.loaded_segments (0x648d4 : word) = Some W_64884.
Proof. vm_refl. Qed.
Lemma D_64884 : decode_any W_64884 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64888 : bv 32 := 0x00813483.
Lemma F_64888 : fetch_word Asan.M.loaded_segments (0x648d8 : word) = Some W_64888.
Proof. vm_refl. Qed.
Lemma D_64888 : decode_any W_64888 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6488c : bv 32 := 0x00013903.
Lemma F_6488c : fetch_word Asan.M.loaded_segments (0x648dc : word) = Some W_6488c.
Proof. vm_refl. Qed.
Lemma D_6488c : decode_any W_6488c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64890 : bv 32 := 0x02010113.
Lemma F_64890 : fetch_word Asan.M.loaded_segments (0x648e0 : word) = Some W_64890.
Proof. vm_refl. Qed.
Lemma D_64890 : decode_any W_64890 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64894 : bv 32 := 0x00008067.
Lemma F_64894 : fetch_word Asan.M.loaded_segments (0x648e4 : word) = Some W_64894.
Proof. vm_refl. Qed.
Lemma D_64894 : decode_any W_64894 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64898 : bv 32 := 0x00160613.
Lemma F_64898 : fetch_word Asan.M.loaded_segments (0x648e8 : word) = Some W_64898.
Proof. vm_refl. Qed.
Lemma D_64898 : decode_any W_64898 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6489c : bv 32 := 0x00100513.
Lemma F_6489c : fetch_word Asan.M.loaded_segments (0x648ec : word) = Some W_6489c.
Proof. vm_refl. Qed.
Lemma D_6489c : decode_any W_6489c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_648a0 : bv 32 := 0xffb90913.
Lemma F_648a0 : fetch_word Asan.M.loaded_segments (0x648f0 : word) = Some W_648a0.
Proof. vm_refl. Qed.
Lemma D_648a0 : decode_any W_648a0 = Some (OpImm ALU_ADD 18 18 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_648a4 : bv 32 := 0x00681813.
Lemma F_648a4 : fetch_word Asan.M.loaded_segments (0x648f4 : word) = Some W_648a4.
Proof. vm_refl. Qed.
Lemma D_648a4 : decode_any W_648a4 = Some (ShiftImm ALU_SLL 16 16 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_648a8 : bv 32 := 0x00c4b023.
Lemma F_648a8 : fetch_word Asan.M.loaded_segments (0x648f8 : word) = Some W_648a8.
Proof. vm_refl. Qed.
Lemma D_648a8 : decode_any W_648a8 = Some (Store SZ8 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_648ac : bv 32 := 0x00a78023.
Lemma F_648ac : fetch_word Asan.M.loaded_segments (0x648fc : word) = Some W_648ac.
Proof. vm_refl. Qed.
Lemma D_648ac : decode_any W_648ac = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_648b0 : bv 32 := 0x01251533.
Lemma F_648b0 : fetch_word Asan.M.loaded_segments (0x64900 : word) = Some W_648b0.
Proof. vm_refl. Qed.
Lemma D_648b0 : decode_any W_648b0 = Some (Op ALU_SLL 10 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_648b4 : bv 32 := 0x00a58533.
Lemma F_648b4 : fetch_word Asan.M.loaded_segments (0x64904 : word) = Some W_648b4.
Proof. vm_refl. Qed.
Lemma D_648b4 : decode_any W_648b4 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_648b8 : bv 32 := 0x010504b3.
Lemma F_648b8 : fetch_word Asan.M.loaded_segments (0x64908 : word) = Some W_648b8.
Proof. vm_refl. Qed.
Lemma D_648b8 : decode_any W_648b8 = Some (Op ALU_ADD 9 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_648bc : bv 32 := 0x0084bc23.
Lemma F_648bc : fetch_word Asan.M.loaded_segments (0x6490c : word) = Some W_648bc.
Proof. vm_refl. Qed.
Lemma D_648bc : decode_any W_648bc = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_648c0 : bv 32 := 0x02f4bc23.
Lemma F_648c0 : fetch_word Asan.M.loaded_segments (0x64910 : word) = Some W_648c0.
Proof. vm_refl. Qed.
Lemma D_648c0 : decode_any W_648c0 = Some (Store SZ8 9 15 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_648c4 : bv 32 := 0x00048513.
Lemma F_648c4 : fetch_word Asan.M.loaded_segments (0x64914 : word) = Some W_648c4.
Proof. vm_refl. Qed.
Lemma D_648c4 : decode_any W_648c4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_648c8 : bv 32 := 0x1ad000ef.
Lemma F_648c8 : fetch_word Asan.M.loaded_segments (0x64918 : word) = Some W_648c8.
Proof. vm_refl. Qed.
Lemma D_648c8 : decode_any W_648c8 = Some (Jal 1 2476, 4%Z).
Proof. vm_refl. Qed.

Definition W_648cc : bv 32 := 0x00050593.
Lemma F_648cc : fetch_word Asan.M.loaded_segments (0x6491c : word) = Some W_648cc.
Proof. vm_refl. Qed.
Lemma D_648cc : decode_any W_648cc = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_648d0 : bv 32 := 0x00048513.
Lemma F_648d0 : fetch_word Asan.M.loaded_segments (0x64920 : word) = Some W_648d0.
Proof. vm_refl. Qed.
Lemma D_648d0 : decode_any W_648d0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_648d4 : bv 32 := 0x00000613.
Lemma F_648d4 : fetch_word Asan.M.loaded_segments (0x64924 : word) = Some W_648d4.
Proof. vm_refl. Qed.
Lemma D_648d4 : decode_any W_648d4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_648d8 : bv 32 := 0x0005b023.
Lemma F_648d8 : fetch_word Asan.M.loaded_segments (0x64928 : word) = Some W_648d8.
Proof. vm_refl. Qed.
Lemma D_648d8 : decode_any W_648d8 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_648dc : bv 32 := 0x01813083.
Lemma F_648dc : fetch_word Asan.M.loaded_segments (0x6492c : word) = Some W_648dc.
Proof. vm_refl. Qed.
Lemma D_648dc : decode_any W_648dc = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_648e0 : bv 32 := 0x01013403.
Lemma F_648e0 : fetch_word Asan.M.loaded_segments (0x64930 : word) = Some W_648e0.
Proof. vm_refl. Qed.
Lemma D_648e0 : decode_any W_648e0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_648e4 : bv 32 := 0x00813483.
Lemma F_648e4 : fetch_word Asan.M.loaded_segments (0x64934 : word) = Some W_648e4.
Proof. vm_refl. Qed.
Lemma D_648e4 : decode_any W_648e4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_648e8 : bv 32 := 0x00013903.
Lemma F_648e8 : fetch_word Asan.M.loaded_segments (0x64938 : word) = Some W_648e8.
Proof. vm_refl. Qed.
Lemma D_648e8 : decode_any W_648e8 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_648ec : bv 32 := 0x02010113.
Lemma F_648ec : fetch_word Asan.M.loaded_segments (0x6493c : word) = Some W_648ec.
Proof. vm_refl. Qed.
Lemma D_648ec : decode_any W_648ec = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_648f0 : bv 32 := 0x00008067.
Lemma F_648f0 : fetch_word Asan.M.loaded_segments (0x64940 : word) = Some W_648f0.
Proof. vm_refl. Qed.
Lemma D_648f0 : decode_any W_648f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_648f4 : bv 32 := 0x04853483.
Lemma F_648f4 : fetch_word Asan.M.loaded_segments (0x64944 : word) = Some W_648f4.
Proof. vm_refl. Qed.
Lemma D_648f4 : decode_any W_648f4 = Some (Load SZ8 true 9 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_648f8 : bv 32 := 0x00100593.
Lemma F_648f8 : fetch_word Asan.M.loaded_segments (0x64948 : word) = Some W_648f8.
Proof. vm_refl. Qed.
Lemma D_648f8 : decode_any W_648f8 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_648fc : bv 32 := 0x0095e663.
Lemma F_648fc : fetch_word Asan.M.loaded_segments (0x6494c : word) = Some W_648fc.
Proof. vm_refl. Qed.
Lemma D_648fc : decode_any W_648fc = Some (Branch BC_LTU 11 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64900 : bv 32 := 0x130260ef.
Lemma F_64900 : fetch_word Asan.M.loaded_segments (0x64950 : word) = Some W_64900.
Proof. vm_refl. Qed.
Lemma D_64900 : decode_any W_64900 = Some (Jal 1 155952, 4%Z).
Proof. vm_refl. Qed.

Definition W_64904 : bv 32 := 0x00050493.
Lemma F_64904 : fetch_word Asan.M.loaded_segments (0x64954 : word) = Some W_64904.
Proof. vm_refl. Qed.
Lemma D_64904 : decode_any W_64904 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64908 : bv 32 := 0xec0490e3.
Lemma F_64908 : fetch_word Asan.M.loaded_segments (0x64958 : word) = Some W_64908.
Proof. vm_refl. Qed.
Lemma D_64908 : decode_any W_64908 = Some (Branch BC_NE 9 0 7872, 4%Z).
Proof. vm_refl. Qed.

Definition W_6490c : bv 32 := 0xf59ff06f.
Lemma F_6490c : fetch_word Asan.M.loaded_segments (0x6495c : word) = Some W_6490c.
Proof. vm_refl. Qed.
Lemma D_6490c : decode_any W_6490c = Some (Jal 0 2096984, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r5d100_5d274.
Module Na0_code_r63228_633c4.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_64aa0 : bv 32 := 0xfe010113.
Lemma F_64aa0 : fetch_word Asan.M.loaded_segments (0x64af0 : word) = Some W_64aa0.
Proof. vm_refl. Qed.
Lemma D_64aa0 : decode_any W_64aa0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_64aa4 : bv 32 := 0x00113c23.
Lemma F_64aa4 : fetch_word Asan.M.loaded_segments (0x64af4 : word) = Some W_64aa4.
Proof. vm_refl. Qed.
Lemma D_64aa4 : decode_any W_64aa4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64aa8 : bv 32 := 0x00813823.
Lemma F_64aa8 : fetch_word Asan.M.loaded_segments (0x64af8 : word) = Some W_64aa8.
Proof. vm_refl. Qed.
Lemma D_64aa8 : decode_any W_64aa8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64aac : bv 32 := 0x00913423.
Lemma F_64aac : fetch_word Asan.M.loaded_segments (0x64afc : word) = Some W_64aac.
Proof. vm_refl. Qed.
Lemma D_64aac : decode_any W_64aac = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ab0 : bv 32 := 0x01213023.
Lemma F_64ab0 : fetch_word Asan.M.loaded_segments (0x64b00 : word) = Some W_64ab0.
Proof. vm_refl. Qed.
Lemma D_64ab0 : decode_any W_64ab0 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ab4 : bv 32 := 0x02010413.
Lemma F_64ab4 : fetch_word Asan.M.loaded_segments (0x64b04 : word) = Some W_64ab4.
Proof. vm_refl. Qed.
Lemma D_64ab4 : decode_any W_64ab4 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ab8 : bv 32 := 0x000f3517.
Lemma F_64ab8 : fetch_word Asan.M.loaded_segments (0x64b08 : word) = Some W_64ab8.
Proof. vm_refl. Qed.
Lemma D_64ab8 : decode_any W_64ab8 = Some (Auipc 10 243, 4%Z).
Proof. vm_refl. Qed.

Definition W_64abc : bv 32 := 0x08850513.
Lemma F_64abc : fetch_word Asan.M.loaded_segments (0x64b0c : word) = Some W_64abc.
Proof. vm_refl. Qed.
Lemma D_64abc : decode_any W_64abc = Some (OpImm ALU_ADD 10 10 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ac0 : bv 32 := 0x009050ef.
Lemma F_64ac0 : fetch_word Asan.M.loaded_segments (0x64b10 : word) = Some W_64ac0.
Proof. vm_refl. Qed.
Lemma D_64ac0 : decode_any W_64ac0 = Some (Jal 1 22536, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ac4 : bv 32 := 0x00053483.
Lemma F_64ac4 : fetch_word Asan.M.loaded_segments (0x64b14 : word) = Some W_64ac4.
Proof. vm_refl. Qed.
Lemma D_64ac4 : decode_any W_64ac4 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ac8 : bv 32 := 0x08048863.
Lemma F_64ac8 : fetch_word Asan.M.loaded_segments (0x64b18 : word) = Some W_64ac8.
Proof. vm_refl. Qed.
Lemma D_64ac8 : decode_any W_64ac8 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_64acc : bv 32 := 0x0604c503.
Lemma F_64acc : fetch_word Asan.M.loaded_segments (0x64b1c : word) = Some W_64acc.
Proof. vm_refl. Qed.
Lemma D_64acc : decode_any W_64acc = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ad0 : bv 32 := 0x0584b903.
Lemma F_64ad0 : fetch_word Asan.M.loaded_segments (0x64b20 : word) = Some W_64ad0.
Proof. vm_refl. Qed.
Lemma D_64ad0 : decode_any W_64ad0 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ad4 : bv 32 := 0x00050863.
Lemma F_64ad4 : fetch_word Asan.M.loaded_segments (0x64b24 : word) = Some W_64ad4.
Proof. vm_refl. Qed.
Lemma D_64ad4 : decode_any W_64ad4 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ad8 : bv 32 := 0x00048513.
Lemma F_64ad8 : fetch_word Asan.M.loaded_segments (0x64b28 : word) = Some W_64ad8.
Proof. vm_refl. Qed.
Lemma D_64ad8 : decode_any W_64ad8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64adc : bv 32 := 0x00040593.
Lemma F_64adc : fetch_word Asan.M.loaded_segments (0x64b2c : word) = Some W_64adc.
Proof. vm_refl. Qed.
Lemma D_64adc : decode_any W_64adc = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ae0 : bv 32 := 0x871ff0ef.
Lemma F_64ae0 : fetch_word Asan.M.loaded_segments (0x64b30 : word) = Some W_64ae0.
Proof. vm_refl. Qed.
Lemma D_64ae0 : decode_any W_64ae0 = Some (Jal 1 2095216, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ae4 : bv 32 := 0xff890593.
Lemma F_64ae4 : fetch_word Asan.M.loaded_segments (0x64b34 : word) = Some W_64ae4.
Proof. vm_refl. Qed.
Lemma D_64ae4 : decode_any W_64ae4 = Some (OpImm ALU_ADD 11 18 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ae8 : bv 32 := 0x00100513.
Lemma F_64ae8 : fetch_word Asan.M.loaded_segments (0x64b38 : word) = Some W_64ae8.
Proof. vm_refl. Qed.
Lemma D_64ae8 : decode_any W_64ae8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64aec : bv 32 := 0x00b51533.
Lemma F_64aec : fetch_word Asan.M.loaded_segments (0x64b3c : word) = Some W_64aec.
Proof. vm_refl. Qed.
Lemma D_64aec : decode_any W_64aec = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_64af0 : bv 32 := 0x0005061b.
Lemma F_64af0 : fetch_word Asan.M.loaded_segments (0x64b40 : word) = Some W_64af0.
Proof. vm_refl. Qed.
Lemma D_64af0 : decode_any W_64af0 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64af4 : bv 32 := 0x08c05263.
Lemma F_64af4 : fetch_word Asan.M.loaded_segments (0x64b44 : word) = Some W_64af4.
Proof. vm_refl. Qed.
Lemma D_64af4 : decode_any W_64af4 = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_64af8 : bv 32 := 0x000016b7.
Lemma F_64af8 : fetch_word Asan.M.loaded_segments (0x64b48 : word) = Some W_64af8.
Proof. vm_refl. Qed.
Lemma D_64af8 : decode_any W_64af8 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64afc : bv 32 := 0xff190613.
Lemma F_64afc : fetch_word Asan.M.loaded_segments (0x64b4c : word) = Some W_64afc.
Proof. vm_refl. Qed.
Lemma D_64afc : decode_any W_64afc = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b00 : bv 32 := 0x30000713.
Lemma F_64b00 : fetch_word Asan.M.loaded_segments (0x64b50 : word) = Some W_64b00.
Proof. vm_refl. Qed.
Lemma D_64b00 : decode_any W_64b00 = Some (OpImm ALU_ADD 14 0 768, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b04 : bv 32 := 0xfff00793.
Lemma F_64b04 : fetch_word Asan.M.loaded_segments (0x64b54 : word) = Some W_64b04.
Proof. vm_refl. Qed.
Lemma D_64b04 : decode_any W_64b04 = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b08 : bv 32 := 0x00c71733.
Lemma F_64b08 : fetch_word Asan.M.loaded_segments (0x64b58 : word) = Some W_64b08.
Proof. vm_refl. Qed.
Lemma D_64b08 : decode_any W_64b08 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b0c : bv 32 := 0x0104b603.
Lemma F_64b0c : fetch_word Asan.M.loaded_segments (0x64b5c : word) = Some W_64b0c.
Proof. vm_refl. Qed.
Lemma D_64b0c : decode_any W_64b0c = Some (Load SZ8 true 12 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b10 : bv 32 := 0x00b797b3.
Lemma F_64b10 : fetch_word Asan.M.loaded_segments (0x64b60 : word) = Some W_64b10.
Proof. vm_refl. Qed.
Lemma D_64b10 : decode_any W_64b10 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b14 : bv 32 := 0xfff50813.
Lemma F_64b14 : fetch_word Asan.M.loaded_segments (0x64b64 : word) = Some W_64b14.
Proof. vm_refl. Qed.
Lemma D_64b14 : decode_any W_64b14 = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b18 : bv 32 := 0x00d485b3.
Lemma F_64b18 : fetch_word Asan.M.loaded_segments (0x64b68 : word) = Some W_64b18.
Proof. vm_refl. Qed.
Lemma D_64b18 : decode_any W_64b18 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b1c : bv 32 := 0x00e586b3.
Lemma F_64b1c : fetch_word Asan.M.loaded_segments (0x64b6c : word) = Some W_64b1c.
Proof. vm_refl. Qed.
Lemma D_64b1c : decode_any W_64b1c = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b20 : bv 32 := 0xfff7c713.
Lemma F_64b20 : fetch_word Asan.M.loaded_segments (0x64b70 : word) = Some W_64b20.
Proof. vm_refl. Qed.
Lemma D_64b20 : decode_any W_64b20 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b24 : bv 32 := 0x02081813.
Lemma F_64b24 : fetch_word Asan.M.loaded_segments (0x64b74 : word) = Some W_64b24.
Proof. vm_refl. Qed.
Lemma D_64b24 : decode_any W_64b24 = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b28 : bv 32 := 0x02085793.
Lemma F_64b28 : fetch_word Asan.M.loaded_segments (0x64b78 : word) = Some W_64b28.
Proof. vm_refl. Qed.
Lemma D_64b28 : decode_any W_64b28 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b2c : bv 32 := 0x00f607b3.
Lemma F_64b2c : fetch_word Asan.M.loaded_segments (0x64b7c : word) = Some W_64b2c.
Proof. vm_refl. Qed.
Lemma D_64b2c : decode_any W_64b2c = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b30 : bv 32 := 0x00178813.
Lemma F_64b30 : fetch_word Asan.M.loaded_segments (0x64b80 : word) = Some W_64b30.
Proof. vm_refl. Qed.
Lemma D_64b30 : decode_any W_64b30 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b34 : bv 32 := 0x00e678b3.
Lemma F_64b34 : fetch_word Asan.M.loaded_segments (0x64b84 : word) = Some W_64b34.
Proof. vm_refl. Qed.
Lemma D_64b34 : decode_any W_64b34 = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b38 : bv 32 := 0x011687b3.
Lemma F_64b38 : fetch_word Asan.M.loaded_segments (0x64b88 : word) = Some W_64b38.
Proof. vm_refl. Qed.
Lemma D_64b38 : decode_any W_64b38 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b3c : bv 32 := 0x0007c283.
Lemma F_64b3c : fetch_word Asan.M.loaded_segments (0x64b8c : word) = Some W_64b3c.
Proof. vm_refl. Qed.
Lemma D_64b3c : decode_any W_64b3c = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b40 : bv 32 := 0x06028663.
Lemma F_64b40 : fetch_word Asan.M.loaded_segments (0x64b90 : word) = Some W_64b40.
Proof. vm_refl. Qed.
Lemma D_64b40 : decode_any W_64b40 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b44 : bv 32 := 0xfff5051b.
Lemma F_64b44 : fetch_word Asan.M.loaded_segments (0x64b94 : word) = Some W_64b44.
Proof. vm_refl. Qed.
Lemma D_64b44 : decode_any W_64b44 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b48 : bv 32 := 0x00160613.
Lemma F_64b48 : fetch_word Asan.M.loaded_segments (0x64b98 : word) = Some W_64b48.
Proof. vm_refl. Qed.
Lemma D_64b48 : decode_any W_64b48 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b4c : bv 32 := 0xfe0514e3.
Lemma F_64b4c : fetch_word Asan.M.loaded_segments (0x64b9c : word) = Some W_64b4c.
Proof. vm_refl. Qed.
Lemma D_64b4c : decode_any W_64b4c = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b50 : bv 32 := 0x0104b823.
Lemma F_64b50 : fetch_word Asan.M.loaded_segments (0x64ba0 : word) = Some W_64b50.
Proof. vm_refl. Qed.
Lemma D_64b50 : decode_any W_64b50 = Some (Store SZ8 9 16 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b54 : bv 32 := 0x0400006f.
Lemma F_64b54 : fetch_word Asan.M.loaded_segments (0x64ba4 : word) = Some W_64b54.
Proof. vm_refl. Qed.
Lemma D_64b54 : decode_any W_64b54 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b58 : bv 32 := 0x000f2517.
Lemma F_64b58 : fetch_word Asan.M.loaded_segments (0x64ba8 : word) = Some W_64b58.
Proof. vm_refl. Qed.
Lemma D_64b58 : decode_any W_64b58 = Some (Auipc 10 242, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b5c : bv 32 := 0x24853503.
Lemma F_64b5c : fetch_word Asan.M.loaded_segments (0x64bac : word) = Some W_64b5c.
Proof. vm_refl. Qed.
Lemma D_64b5c : decode_any W_64b5c = Some (Load SZ8 true 10 10 584, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b60 : bv 32 := 0x00052503.
Lemma F_64b60 : fetch_word Asan.M.loaded_segments (0x64bb0 : word) = Some W_64b60.
Proof. vm_refl. Qed.
Lemma D_64b60 : decode_any W_64b60 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b64 : bv 32 := 0x02050863.
Lemma F_64b64 : fetch_word Asan.M.loaded_segments (0x64bb4 : word) = Some W_64b64.
Proof. vm_refl. Qed.
Lemma D_64b64 : decode_any W_64b64 = Some (Branch BC_EQ 10 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b68 : bv 32 := 0x455250ef.
Lemma F_64b68 : fetch_word Asan.M.loaded_segments (0x64bb8 : word) = Some W_64b68.
Proof. vm_refl. Qed.
Lemma D_64b68 : decode_any W_64b68 = Some (Jal 1 154708, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b6c : bv 32 := 0x02050463.
Lemma F_64b6c : fetch_word Asan.M.loaded_segments (0x64bbc : word) = Some W_64b6c.
Proof. vm_refl. Qed.
Lemma D_64b6c : decode_any W_64b6c = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b70 : bv 32 := 0x02850583.
Lemma F_64b70 : fetch_word Asan.M.loaded_segments (0x64bc0 : word) = Some W_64b70.
Proof. vm_refl. Qed.
Lemma D_64b70 : decode_any W_64b70 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b74 : bv 32 := 0x0a058663.
Lemma F_64b74 : fetch_word Asan.M.loaded_segments (0x64bc4 : word) = Some W_64b74.
Proof. vm_refl. Qed.
Lemma D_64b74 : decode_any W_64b74 = Some (Branch BC_EQ 11 0 172, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b78 : bv 32 := 0x00000513.
Lemma F_64b78 : fetch_word Asan.M.loaded_segments (0x64bc8 : word) = Some W_64b78.
Proof. vm_refl. Qed.
Lemma D_64b78 : decode_any W_64b78 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b7c : bv 32 := 0x01813083.
Lemma F_64b7c : fetch_word Asan.M.loaded_segments (0x64bcc : word) = Some W_64b7c.
Proof. vm_refl. Qed.
Lemma D_64b7c : decode_any W_64b7c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b80 : bv 32 := 0x01013403.
Lemma F_64b80 : fetch_word Asan.M.loaded_segments (0x64bd0 : word) = Some W_64b80.
Proof. vm_refl. Qed.
Lemma D_64b80 : decode_any W_64b80 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b84 : bv 32 := 0x00813483.
Lemma F_64b84 : fetch_word Asan.M.loaded_segments (0x64bd4 : word) = Some W_64b84.
Proof. vm_refl. Qed.
Lemma D_64b84 : decode_any W_64b84 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b88 : bv 32 := 0x00013903.
Lemma F_64b88 : fetch_word Asan.M.loaded_segments (0x64bd8 : word) = Some W_64b88.
Proof. vm_refl. Qed.
Lemma D_64b88 : decode_any W_64b88 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b8c : bv 32 := 0x02010113.
Lemma F_64b8c : fetch_word Asan.M.loaded_segments (0x64bdc : word) = Some W_64b8c.
Proof. vm_refl. Qed.
Lemma D_64b8c : decode_any W_64b8c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b90 : bv 32 := 0x00008067.
Lemma F_64b90 : fetch_word Asan.M.loaded_segments (0x64be0 : word) = Some W_64b90.
Proof. vm_refl. Qed.
Lemma D_64b90 : decode_any W_64b90 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b94 : bv 32 := 0x01813083.
Lemma F_64b94 : fetch_word Asan.M.loaded_segments (0x64be4 : word) = Some W_64b94.
Proof. vm_refl. Qed.
Lemma D_64b94 : decode_any W_64b94 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b98 : bv 32 := 0x01013403.
Lemma F_64b98 : fetch_word Asan.M.loaded_segments (0x64be8 : word) = Some W_64b98.
Proof. vm_refl. Qed.
Lemma D_64b98 : decode_any W_64b98 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b9c : bv 32 := 0x00813483.
Lemma F_64b9c : fetch_word Asan.M.loaded_segments (0x64bec : word) = Some W_64b9c.
Proof. vm_refl. Qed.
Lemma D_64b9c : decode_any W_64b9c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ba0 : bv 32 := 0x00013903.
Lemma F_64ba0 : fetch_word Asan.M.loaded_segments (0x64bf0 : word) = Some W_64ba0.
Proof. vm_refl. Qed.
Lemma D_64ba0 : decode_any W_64ba0 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ba4 : bv 32 := 0x02010113.
Lemma F_64ba4 : fetch_word Asan.M.loaded_segments (0x64bf4 : word) = Some W_64ba4.
Proof. vm_refl. Qed.
Lemma D_64ba4 : decode_any W_64ba4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ba8 : bv 32 := 0x00008067.
Lemma F_64ba8 : fetch_word Asan.M.loaded_segments (0x64bf8 : word) = Some W_64ba8.
Proof. vm_refl. Qed.
Lemma D_64ba8 : decode_any W_64ba8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64bac : bv 32 := 0x00160613.
Lemma F_64bac : fetch_word Asan.M.loaded_segments (0x64bfc : word) = Some W_64bac.
Proof. vm_refl. Qed.
Lemma D_64bac : decode_any W_64bac = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64bb0 : bv 32 := 0x00100513.
Lemma F_64bb0 : fetch_word Asan.M.loaded_segments (0x64c00 : word) = Some W_64bb0.
Proof. vm_refl. Qed.
Lemma D_64bb0 : decode_any W_64bb0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64bb4 : bv 32 := 0xffb90693.
Lemma F_64bb4 : fetch_word Asan.M.loaded_segments (0x64c04 : word) = Some W_64bb4.
Proof. vm_refl. Qed.
Lemma D_64bb4 : decode_any W_64bb4 = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_64bb8 : bv 32 := 0x00c4b823.
Lemma F_64bb8 : fetch_word Asan.M.loaded_segments (0x64c08 : word) = Some W_64bb8.
Proof. vm_refl. Qed.
Lemma D_64bb8 : decode_any W_64bb8 = Some (Store SZ8 9 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64bbc : bv 32 := 0x00a78023.
Lemma F_64bbc : fetch_word Asan.M.loaded_segments (0x64c0c : word) = Some W_64bbc.
Proof. vm_refl. Qed.
Lemma D_64bbc : decode_any W_64bbc = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64bc0 : bv 32 := 0x00d51533.
Lemma F_64bc0 : fetch_word Asan.M.loaded_segments (0x64c10 : word) = Some W_64bc0.
Proof. vm_refl. Qed.
Lemma D_64bc0 : decode_any W_64bc0 = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_64bc4 : bv 32 := 0x00200613.
Lemma F_64bc4 : fetch_word Asan.M.loaded_segments (0x64c14 : word) = Some W_64bc4.
Proof. vm_refl. Qed.
Lemma D_64bc4 : decode_any W_64bc4 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_64bc8 : bv 32 := 0x00889893.
Lemma F_64bc8 : fetch_word Asan.M.loaded_segments (0x64c18 : word) = Some W_64bc8.
Proof. vm_refl. Qed.
Lemma D_64bc8 : decode_any W_64bc8 = Some (ShiftImm ALU_SLL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64bcc : bv 32 := 0x01261633.
Lemma F_64bcc : fetch_word Asan.M.loaded_segments (0x64c1c : word) = Some W_64bcc.
Proof. vm_refl. Qed.
Lemma D_64bcc : decode_any W_64bcc = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_64bd0 : bv 32 := 0x00a58533.
Lemma F_64bd0 : fetch_word Asan.M.loaded_segments (0x64c20 : word) = Some W_64bd0.
Proof. vm_refl. Qed.
Lemma D_64bd0 : decode_any W_64bd0 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_64bd4 : bv 32 := 0x01160633.
Lemma F_64bd4 : fetch_word Asan.M.loaded_segments (0x64c24 : word) = Some W_64bd4.
Proof. vm_refl. Qed.
Lemma D_64bd4 : decode_any W_64bd4 = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_64bd8 : bv 32 := 0x00c504b3.
Lemma F_64bd8 : fetch_word Asan.M.loaded_segments (0x64c28 : word) = Some W_64bd8.
Proof. vm_refl. Qed.
Lemma D_64bd8 : decode_any W_64bd8 = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64bdc : bv 32 := 0x0084bc23.
Lemma F_64bdc : fetch_word Asan.M.loaded_segments (0x64c2c : word) = Some W_64bdc.
Proof. vm_refl. Qed.
Lemma D_64bdc : decode_any W_64bdc = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64be0 : bv 32 := 0x0ef4bc23.
Lemma F_64be0 : fetch_word Asan.M.loaded_segments (0x64c30 : word) = Some W_64be0.
Proof. vm_refl. Qed.
Lemma D_64be0 : decode_any W_64be0 = Some (Store SZ8 9 15 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_64be4 : bv 32 := 0x00048513.
Lemma F_64be4 : fetch_word Asan.M.loaded_segments (0x64c34 : word) = Some W_64be4.
Proof. vm_refl. Qed.
Lemma D_64be4 : decode_any W_64be4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64be8 : bv 32 := 0x68c000ef.
Lemma F_64be8 : fetch_word Asan.M.loaded_segments (0x64c38 : word) = Some W_64be8.
Proof. vm_refl. Qed.
Lemma D_64be8 : decode_any W_64be8 = Some (Jal 1 1676, 4%Z).
Proof. vm_refl. Qed.

Definition W_64bec : bv 32 := 0x00050593.
Lemma F_64bec : fetch_word Asan.M.loaded_segments (0x64c3c : word) = Some W_64bec.
Proof. vm_refl. Qed.
Lemma D_64bec : decode_any W_64bec = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64bf0 : bv 32 := 0x00048513.
Lemma F_64bf0 : fetch_word Asan.M.loaded_segments (0x64c40 : word) = Some W_64bf0.
Proof. vm_refl. Qed.
Lemma D_64bf0 : decode_any W_64bf0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64bf4 : bv 32 := 0x00000613.
Lemma F_64bf4 : fetch_word Asan.M.loaded_segments (0x64c44 : word) = Some W_64bf4.
Proof. vm_refl. Qed.
Lemma D_64bf4 : decode_any W_64bf4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64bf8 : bv 32 := 0x0005b023.
Lemma F_64bf8 : fetch_word Asan.M.loaded_segments (0x64c48 : word) = Some W_64bf8.
Proof. vm_refl. Qed.
Lemma D_64bf8 : decode_any W_64bf8 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64bfc : bv 32 := 0x0005b423.
Lemma F_64bfc : fetch_word Asan.M.loaded_segments (0x64c4c : word) = Some W_64bfc.
Proof. vm_refl. Qed.
Lemma D_64bfc : decode_any W_64bfc = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c00 : bv 32 := 0x0005b823.
Lemma F_64c00 : fetch_word Asan.M.loaded_segments (0x64c50 : word) = Some W_64c00.
Proof. vm_refl. Qed.
Lemma D_64c00 : decode_any W_64c00 = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c04 : bv 32 := 0x0005bc23.
Lemma F_64c04 : fetch_word Asan.M.loaded_segments (0x64c54 : word) = Some W_64c04.
Proof. vm_refl. Qed.
Lemma D_64c04 : decode_any W_64c04 = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c08 : bv 32 := 0x01813083.
Lemma F_64c08 : fetch_word Asan.M.loaded_segments (0x64c58 : word) = Some W_64c08.
Proof. vm_refl. Qed.
Lemma D_64c08 : decode_any W_64c08 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c0c : bv 32 := 0x01013403.
Lemma F_64c0c : fetch_word Asan.M.loaded_segments (0x64c5c : word) = Some W_64c0c.
Proof. vm_refl. Qed.
Lemma D_64c0c : decode_any W_64c0c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c10 : bv 32 := 0x00813483.
Lemma F_64c10 : fetch_word Asan.M.loaded_segments (0x64c60 : word) = Some W_64c10.
Proof. vm_refl. Qed.
Lemma D_64c10 : decode_any W_64c10 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c14 : bv 32 := 0x00013903.
Lemma F_64c14 : fetch_word Asan.M.loaded_segments (0x64c64 : word) = Some W_64c14.
Proof. vm_refl. Qed.
Lemma D_64c14 : decode_any W_64c14 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c18 : bv 32 := 0x02010113.
Lemma F_64c18 : fetch_word Asan.M.loaded_segments (0x64c68 : word) = Some W_64c18.
Proof. vm_refl. Qed.
Lemma D_64c18 : decode_any W_64c18 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c1c : bv 32 := 0x00008067.
Lemma F_64c1c : fetch_word Asan.M.loaded_segments (0x64c6c : word) = Some W_64c1c.
Proof. vm_refl. Qed.
Lemma D_64c1c : decode_any W_64c1c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c20 : bv 32 := 0x04853483.
Lemma F_64c20 : fetch_word Asan.M.loaded_segments (0x64c70 : word) = Some W_64c20.
Proof. vm_refl. Qed.
Lemma D_64c20 : decode_any W_64c20 = Some (Load SZ8 true 9 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c24 : bv 32 := 0x00100593.
Lemma F_64c24 : fetch_word Asan.M.loaded_segments (0x64c74 : word) = Some W_64c24.
Proof. vm_refl. Qed.
Lemma D_64c24 : decode_any W_64c24 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c28 : bv 32 := 0x0095e663.
Lemma F_64c28 : fetch_word Asan.M.loaded_segments (0x64c78 : word) = Some W_64c28.
Proof. vm_refl. Qed.
Lemma D_64c28 : decode_any W_64c28 = Some (Branch BC_LTU 11 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c2c : bv 32 := 0x605250ef.
Lemma F_64c2c : fetch_word Asan.M.loaded_segments (0x64c7c : word) = Some W_64c2c.
Proof. vm_refl. Qed.
Lemma D_64c2c : decode_any W_64c2c = Some (Jal 1 155140, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c30 : bv 32 := 0x00050493.
Lemma F_64c30 : fetch_word Asan.M.loaded_segments (0x64c80 : word) = Some W_64c30.
Proof. vm_refl. Qed.
Lemma D_64c30 : decode_any W_64c30 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c34 : bv 32 := 0xe8049ce3.
Lemma F_64c34 : fetch_word Asan.M.loaded_segments (0x64c84 : word) = Some W_64c34.
Proof. vm_refl. Qed.
Lemma D_64c34 : decode_any W_64c34 = Some (Branch BC_NE 9 0 7832, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c38 : bv 32 := 0xf41ff06f.
Lemma F_64c38 : fetch_word Asan.M.loaded_segments (0x64c88 : word) = Some W_64c38.
Proof. vm_refl. Qed.
Lemma D_64c38 : decode_any W_64c38 = Some (Jal 0 2096960, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r63228_633c4.
Module Na0_code_r63570_6373c.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_64de8 : bv 32 := 0xfe010113.
Lemma F_64de8 : fetch_word Asan.M.loaded_segments (0x64e38 : word) = Some W_64de8.
Proof. vm_refl. Qed.
Lemma D_64de8 : decode_any W_64de8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_64dec : bv 32 := 0x00113c23.
Lemma F_64dec : fetch_word Asan.M.loaded_segments (0x64e3c : word) = Some W_64dec.
Proof. vm_refl. Qed.
Lemma D_64dec : decode_any W_64dec = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64df0 : bv 32 := 0x00813823.
Lemma F_64df0 : fetch_word Asan.M.loaded_segments (0x64e40 : word) = Some W_64df0.
Proof. vm_refl. Qed.
Lemma D_64df0 : decode_any W_64df0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64df4 : bv 32 := 0x00913423.
Lemma F_64df4 : fetch_word Asan.M.loaded_segments (0x64e44 : word) = Some W_64df4.
Proof. vm_refl. Qed.
Lemma D_64df4 : decode_any W_64df4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64df8 : bv 32 := 0x01213023.
Lemma F_64df8 : fetch_word Asan.M.loaded_segments (0x64e48 : word) = Some W_64df8.
Proof. vm_refl. Qed.
Lemma D_64df8 : decode_any W_64df8 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64dfc : bv 32 := 0x02010413.
Lemma F_64dfc : fetch_word Asan.M.loaded_segments (0x64e4c : word) = Some W_64dfc.
Proof. vm_refl. Qed.
Lemma D_64dfc : decode_any W_64dfc = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e00 : bv 32 := 0x000f3517.
Lemma F_64e00 : fetch_word Asan.M.loaded_segments (0x64e50 : word) = Some W_64e00.
Proof. vm_refl. Qed.
Lemma D_64e00 : decode_any W_64e00 = Some (Auipc 10 243, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e04 : bv 32 := 0xd4050513.
Lemma F_64e04 : fetch_word Asan.M.loaded_segments (0x64e54 : word) = Some W_64e04.
Proof. vm_refl. Qed.
Lemma D_64e04 : decode_any W_64e04 = Some (OpImm ALU_ADD 10 10 3392, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e08 : bv 32 := 0x4c0050ef.
Lemma F_64e08 : fetch_word Asan.M.loaded_segments (0x64e58 : word) = Some W_64e08.
Proof. vm_refl. Qed.
Lemma D_64e08 : decode_any W_64e08 = Some (Jal 1 21696, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e0c : bv 32 := 0x00053483.
Lemma F_64e0c : fetch_word Asan.M.loaded_segments (0x64e5c : word) = Some W_64e0c.
Proof. vm_refl. Qed.
Lemma D_64e0c : decode_any W_64e0c = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e10 : bv 32 := 0x08048863.
Lemma F_64e10 : fetch_word Asan.M.loaded_segments (0x64e60 : word) = Some W_64e10.
Proof. vm_refl. Qed.
Lemma D_64e10 : decode_any W_64e10 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e14 : bv 32 := 0x0604c503.
Lemma F_64e14 : fetch_word Asan.M.loaded_segments (0x64e64 : word) = Some W_64e14.
Proof. vm_refl. Qed.
Lemma D_64e14 : decode_any W_64e14 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e18 : bv 32 := 0x0584b903.
Lemma F_64e18 : fetch_word Asan.M.loaded_segments (0x64e68 : word) = Some W_64e18.
Proof. vm_refl. Qed.
Lemma D_64e18 : decode_any W_64e18 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e1c : bv 32 := 0x00050863.
Lemma F_64e1c : fetch_word Asan.M.loaded_segments (0x64e6c : word) = Some W_64e1c.
Proof. vm_refl. Qed.
Lemma D_64e1c : decode_any W_64e1c = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e20 : bv 32 := 0x00048513.
Lemma F_64e20 : fetch_word Asan.M.loaded_segments (0x64e70 : word) = Some W_64e20.
Proof. vm_refl. Qed.
Lemma D_64e20 : decode_any W_64e20 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e24 : bv 32 := 0x00040593.
Lemma F_64e24 : fetch_word Asan.M.loaded_segments (0x64e74 : word) = Some W_64e24.
Proof. vm_refl. Qed.
Lemma D_64e24 : decode_any W_64e24 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e28 : bv 32 := 0xd28ff0ef.
Lemma F_64e28 : fetch_word Asan.M.loaded_segments (0x64e78 : word) = Some W_64e28.
Proof. vm_refl. Qed.
Lemma D_64e28 : decode_any W_64e28 = Some (Jal 1 2094376, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e2c : bv 32 := 0xff690593.
Lemma F_64e2c : fetch_word Asan.M.loaded_segments (0x64e7c : word) = Some W_64e2c.
Proof. vm_refl. Qed.
Lemma D_64e2c : decode_any W_64e2c = Some (OpImm ALU_ADD 11 18 4086, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e30 : bv 32 := 0x00100513.
Lemma F_64e30 : fetch_word Asan.M.loaded_segments (0x64e80 : word) = Some W_64e30.
Proof. vm_refl. Qed.
Lemma D_64e30 : decode_any W_64e30 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e34 : bv 32 := 0x00b51533.
Lemma F_64e34 : fetch_word Asan.M.loaded_segments (0x64e84 : word) = Some W_64e34.
Proof. vm_refl. Qed.
Lemma D_64e34 : decode_any W_64e34 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e38 : bv 32 := 0x0005061b.
Lemma F_64e38 : fetch_word Asan.M.loaded_segments (0x64e88 : word) = Some W_64e38.
Proof. vm_refl. Qed.
Lemma D_64e38 : decode_any W_64e38 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e3c : bv 32 := 0x08c05263.
Lemma F_64e3c : fetch_word Asan.M.loaded_segments (0x64e8c : word) = Some W_64e3c.
Proof. vm_refl. Qed.
Lemma D_64e3c : decode_any W_64e3c = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e40 : bv 32 := 0x000016b7.
Lemma F_64e40 : fetch_word Asan.M.loaded_segments (0x64e90 : word) = Some W_64e40.
Proof. vm_refl. Qed.
Lemma D_64e40 : decode_any W_64e40 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e44 : bv 32 := 0xff190613.
Lemma F_64e44 : fetch_word Asan.M.loaded_segments (0x64e94 : word) = Some W_64e44.
Proof. vm_refl. Qed.
Lemma D_64e44 : decode_any W_64e44 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e48 : bv 32 := 0x3c000713.
Lemma F_64e48 : fetch_word Asan.M.loaded_segments (0x64e98 : word) = Some W_64e48.
Proof. vm_refl. Qed.
Lemma D_64e48 : decode_any W_64e48 = Some (OpImm ALU_ADD 14 0 960, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e4c : bv 32 := 0xfff00793.
Lemma F_64e4c : fetch_word Asan.M.loaded_segments (0x64e9c : word) = Some W_64e4c.
Proof. vm_refl. Qed.
Lemma D_64e4c : decode_any W_64e4c = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e50 : bv 32 := 0x00c71733.
Lemma F_64e50 : fetch_word Asan.M.loaded_segments (0x64ea0 : word) = Some W_64e50.
Proof. vm_refl. Qed.
Lemma D_64e50 : decode_any W_64e50 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e54 : bv 32 := 0x0204b603.
Lemma F_64e54 : fetch_word Asan.M.loaded_segments (0x64ea4 : word) = Some W_64e54.
Proof. vm_refl. Qed.
Lemma D_64e54 : decode_any W_64e54 = Some (Load SZ8 true 12 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e58 : bv 32 := 0x00b797b3.
Lemma F_64e58 : fetch_word Asan.M.loaded_segments (0x64ea8 : word) = Some W_64e58.
Proof. vm_refl. Qed.
Lemma D_64e58 : decode_any W_64e58 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e5c : bv 32 := 0xfff50813.
Lemma F_64e5c : fetch_word Asan.M.loaded_segments (0x64eac : word) = Some W_64e5c.
Proof. vm_refl. Qed.
Lemma D_64e5c : decode_any W_64e5c = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e60 : bv 32 := 0x00d485b3.
Lemma F_64e60 : fetch_word Asan.M.loaded_segments (0x64eb0 : word) = Some W_64e60.
Proof. vm_refl. Qed.
Lemma D_64e60 : decode_any W_64e60 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e64 : bv 32 := 0x00e586b3.
Lemma F_64e64 : fetch_word Asan.M.loaded_segments (0x64eb4 : word) = Some W_64e64.
Proof. vm_refl. Qed.
Lemma D_64e64 : decode_any W_64e64 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e68 : bv 32 := 0xfff7c713.
Lemma F_64e68 : fetch_word Asan.M.loaded_segments (0x64eb8 : word) = Some W_64e68.
Proof. vm_refl. Qed.
Lemma D_64e68 : decode_any W_64e68 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e6c : bv 32 := 0x02081813.
Lemma F_64e6c : fetch_word Asan.M.loaded_segments (0x64ebc : word) = Some W_64e6c.
Proof. vm_refl. Qed.
Lemma D_64e6c : decode_any W_64e6c = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e70 : bv 32 := 0x02085793.
Lemma F_64e70 : fetch_word Asan.M.loaded_segments (0x64ec0 : word) = Some W_64e70.
Proof. vm_refl. Qed.
Lemma D_64e70 : decode_any W_64e70 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e74 : bv 32 := 0x00f607b3.
Lemma F_64e74 : fetch_word Asan.M.loaded_segments (0x64ec4 : word) = Some W_64e74.
Proof. vm_refl. Qed.
Lemma D_64e74 : decode_any W_64e74 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e78 : bv 32 := 0x00178813.
Lemma F_64e78 : fetch_word Asan.M.loaded_segments (0x64ec8 : word) = Some W_64e78.
Proof. vm_refl. Qed.
Lemma D_64e78 : decode_any W_64e78 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e7c : bv 32 := 0x00e678b3.
Lemma F_64e7c : fetch_word Asan.M.loaded_segments (0x64ecc : word) = Some W_64e7c.
Proof. vm_refl. Qed.
Lemma D_64e7c : decode_any W_64e7c = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e80 : bv 32 := 0x011687b3.
Lemma F_64e80 : fetch_word Asan.M.loaded_segments (0x64ed0 : word) = Some W_64e80.
Proof. vm_refl. Qed.
Lemma D_64e80 : decode_any W_64e80 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e84 : bv 32 := 0x0007c283.
Lemma F_64e84 : fetch_word Asan.M.loaded_segments (0x64ed4 : word) = Some W_64e84.
Proof. vm_refl. Qed.
Lemma D_64e84 : decode_any W_64e84 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e88 : bv 32 := 0x06028663.
Lemma F_64e88 : fetch_word Asan.M.loaded_segments (0x64ed8 : word) = Some W_64e88.
Proof. vm_refl. Qed.
Lemma D_64e88 : decode_any W_64e88 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e8c : bv 32 := 0xfff5051b.
Lemma F_64e8c : fetch_word Asan.M.loaded_segments (0x64edc : word) = Some W_64e8c.
Proof. vm_refl. Qed.
Lemma D_64e8c : decode_any W_64e8c = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e90 : bv 32 := 0x00160613.
Lemma F_64e90 : fetch_word Asan.M.loaded_segments (0x64ee0 : word) = Some W_64e90.
Proof. vm_refl. Qed.
Lemma D_64e90 : decode_any W_64e90 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e94 : bv 32 := 0xfe0514e3.
Lemma F_64e94 : fetch_word Asan.M.loaded_segments (0x64ee4 : word) = Some W_64e94.
Proof. vm_refl. Qed.
Lemma D_64e94 : decode_any W_64e94 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e98 : bv 32 := 0x0304b023.
Lemma F_64e98 : fetch_word Asan.M.loaded_segments (0x64ee8 : word) = Some W_64e98.
Proof. vm_refl. Qed.
Lemma D_64e98 : decode_any W_64e98 = Some (Store SZ8 9 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e9c : bv 32 := 0x0400006f.
Lemma F_64e9c : fetch_word Asan.M.loaded_segments (0x64eec : word) = Some W_64e9c.
Proof. vm_refl. Qed.
Lemma D_64e9c : decode_any W_64e9c = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ea0 : bv 32 := 0x000f2517.
Lemma F_64ea0 : fetch_word Asan.M.loaded_segments (0x64ef0 : word) = Some W_64ea0.
Proof. vm_refl. Qed.
Lemma D_64ea0 : decode_any W_64ea0 = Some (Auipc 10 242, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ea4 : bv 32 := 0xf0053503.
Lemma F_64ea4 : fetch_word Asan.M.loaded_segments (0x64ef4 : word) = Some W_64ea4.
Proof. vm_refl. Qed.
Lemma D_64ea4 : decode_any W_64ea4 = Some (Load SZ8 true 10 10 3840, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ea8 : bv 32 := 0x00052503.
Lemma F_64ea8 : fetch_word Asan.M.loaded_segments (0x64ef8 : word) = Some W_64ea8.
Proof. vm_refl. Qed.
Lemma D_64ea8 : decode_any W_64ea8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64eac : bv 32 := 0x02050863.
Lemma F_64eac : fetch_word Asan.M.loaded_segments (0x64efc : word) = Some W_64eac.
Proof. vm_refl. Qed.
Lemma D_64eac : decode_any W_64eac = Some (Branch BC_EQ 10 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_64eb0 : bv 32 := 0x10d250ef.
Lemma F_64eb0 : fetch_word Asan.M.loaded_segments (0x64f00 : word) = Some W_64eb0.
Proof. vm_refl. Qed.
Lemma D_64eb0 : decode_any W_64eb0 = Some (Jal 1 153868, 4%Z).
Proof. vm_refl. Qed.

Definition W_64eb4 : bv 32 := 0x02050463.
Lemma F_64eb4 : fetch_word Asan.M.loaded_segments (0x64f04 : word) = Some W_64eb4.
Proof. vm_refl. Qed.
Lemma D_64eb4 : decode_any W_64eb4 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_64eb8 : bv 32 := 0x02850583.
Lemma F_64eb8 : fetch_word Asan.M.loaded_segments (0x64f08 : word) = Some W_64eb8.
Proof. vm_refl. Qed.
Lemma D_64eb8 : decode_any W_64eb8 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ebc : bv 32 := 0x0c058e63.
Lemma F_64ebc : fetch_word Asan.M.loaded_segments (0x64f0c : word) = Some W_64ebc.
Proof. vm_refl. Qed.
Lemma D_64ebc : decode_any W_64ebc = Some (Branch BC_EQ 11 0 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ec0 : bv 32 := 0x00000513.
Lemma F_64ec0 : fetch_word Asan.M.loaded_segments (0x64f10 : word) = Some W_64ec0.
Proof. vm_refl. Qed.
Lemma D_64ec0 : decode_any W_64ec0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ec4 : bv 32 := 0x01813083.
Lemma F_64ec4 : fetch_word Asan.M.loaded_segments (0x64f14 : word) = Some W_64ec4.
Proof. vm_refl. Qed.
Lemma D_64ec4 : decode_any W_64ec4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ec8 : bv 32 := 0x01013403.
Lemma F_64ec8 : fetch_word Asan.M.loaded_segments (0x64f18 : word) = Some W_64ec8.
Proof. vm_refl. Qed.
Lemma D_64ec8 : decode_any W_64ec8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ecc : bv 32 := 0x00813483.
Lemma F_64ecc : fetch_word Asan.M.loaded_segments (0x64f1c : word) = Some W_64ecc.
Proof. vm_refl. Qed.
Lemma D_64ecc : decode_any W_64ecc = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ed0 : bv 32 := 0x00013903.
Lemma F_64ed0 : fetch_word Asan.M.loaded_segments (0x64f20 : word) = Some W_64ed0.
Proof. vm_refl. Qed.
Lemma D_64ed0 : decode_any W_64ed0 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ed4 : bv 32 := 0x02010113.
Lemma F_64ed4 : fetch_word Asan.M.loaded_segments (0x64f24 : word) = Some W_64ed4.
Proof. vm_refl. Qed.
Lemma D_64ed4 : decode_any W_64ed4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ed8 : bv 32 := 0x00008067.
Lemma F_64ed8 : fetch_word Asan.M.loaded_segments (0x64f28 : word) = Some W_64ed8.
Proof. vm_refl. Qed.
Lemma D_64ed8 : decode_any W_64ed8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64edc : bv 32 := 0x01813083.
Lemma F_64edc : fetch_word Asan.M.loaded_segments (0x64f2c : word) = Some W_64edc.
Proof. vm_refl. Qed.
Lemma D_64edc : decode_any W_64edc = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ee0 : bv 32 := 0x01013403.
Lemma F_64ee0 : fetch_word Asan.M.loaded_segments (0x64f30 : word) = Some W_64ee0.
Proof. vm_refl. Qed.
Lemma D_64ee0 : decode_any W_64ee0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ee4 : bv 32 := 0x00813483.
Lemma F_64ee4 : fetch_word Asan.M.loaded_segments (0x64f34 : word) = Some W_64ee4.
Proof. vm_refl. Qed.
Lemma D_64ee4 : decode_any W_64ee4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ee8 : bv 32 := 0x00013903.
Lemma F_64ee8 : fetch_word Asan.M.loaded_segments (0x64f38 : word) = Some W_64ee8.
Proof. vm_refl. Qed.
Lemma D_64ee8 : decode_any W_64ee8 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64eec : bv 32 := 0x02010113.
Lemma F_64eec : fetch_word Asan.M.loaded_segments (0x64f3c : word) = Some W_64eec.
Proof. vm_refl. Qed.
Lemma D_64eec : decode_any W_64eec = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ef0 : bv 32 := 0x00008067.
Lemma F_64ef0 : fetch_word Asan.M.loaded_segments (0x64f40 : word) = Some W_64ef0.
Proof. vm_refl. Qed.
Lemma D_64ef0 : decode_any W_64ef0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ef4 : bv 32 := 0x00160613.
Lemma F_64ef4 : fetch_word Asan.M.loaded_segments (0x64f44 : word) = Some W_64ef4.
Proof. vm_refl. Qed.
Lemma D_64ef4 : decode_any W_64ef4 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ef8 : bv 32 := 0x00100513.
Lemma F_64ef8 : fetch_word Asan.M.loaded_segments (0x64f48 : word) = Some W_64ef8.
Proof. vm_refl. Qed.
Lemma D_64ef8 : decode_any W_64ef8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64efc : bv 32 := 0xffb90693.
Lemma F_64efc : fetch_word Asan.M.loaded_segments (0x64f4c : word) = Some W_64efc.
Proof. vm_refl. Qed.
Lemma D_64efc : decode_any W_64efc = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f00 : bv 32 := 0x02c4b023.
Lemma F_64f00 : fetch_word Asan.M.loaded_segments (0x64f50 : word) = Some W_64f00.
Proof. vm_refl. Qed.
Lemma D_64f00 : decode_any W_64f00 = Some (Store SZ8 9 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f04 : bv 32 := 0x00a78023.
Lemma F_64f04 : fetch_word Asan.M.loaded_segments (0x64f54 : word) = Some W_64f04.
Proof. vm_refl. Qed.
Lemma D_64f04 : decode_any W_64f04 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f08 : bv 32 := 0x00d51533.
Lemma F_64f08 : fetch_word Asan.M.loaded_segments (0x64f58 : word) = Some W_64f08.
Proof. vm_refl. Qed.
Lemma D_64f08 : decode_any W_64f08 = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f0c : bv 32 := 0x00400613.
Lemma F_64f0c : fetch_word Asan.M.loaded_segments (0x64f5c : word) = Some W_64f0c.
Proof. vm_refl. Qed.
Lemma D_64f0c : decode_any W_64f0c = Some (OpImm ALU_ADD 12 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f10 : bv 32 := 0x00a89893.
Lemma F_64f10 : fetch_word Asan.M.loaded_segments (0x64f60 : word) = Some W_64f10.
Proof. vm_refl. Qed.
Lemma D_64f10 : decode_any W_64f10 = Some (ShiftImm ALU_SLL 17 17 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f14 : bv 32 := 0x01261633.
Lemma F_64f14 : fetch_word Asan.M.loaded_segments (0x64f64 : word) = Some W_64f14.
Proof. vm_refl. Qed.
Lemma D_64f14 : decode_any W_64f14 = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f18 : bv 32 := 0x00a58533.
Lemma F_64f18 : fetch_word Asan.M.loaded_segments (0x64f68 : word) = Some W_64f18.
Proof. vm_refl. Qed.
Lemma D_64f18 : decode_any W_64f18 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f1c : bv 32 := 0x01160633.
Lemma F_64f1c : fetch_word Asan.M.loaded_segments (0x64f6c : word) = Some W_64f1c.
Proof. vm_refl. Qed.
Lemma D_64f1c : decode_any W_64f1c = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f20 : bv 32 := 0x00c504b3.
Lemma F_64f20 : fetch_word Asan.M.loaded_segments (0x64f70 : word) = Some W_64f20.
Proof. vm_refl. Qed.
Lemma D_64f20 : decode_any W_64f20 = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f24 : bv 32 := 0x0084bc23.
Lemma F_64f24 : fetch_word Asan.M.loaded_segments (0x64f74 : word) = Some W_64f24.
Proof. vm_refl. Qed.
Lemma D_64f24 : decode_any W_64f24 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f28 : bv 32 := 0x3ef4bc23.
Lemma F_64f28 : fetch_word Asan.M.loaded_segments (0x64f78 : word) = Some W_64f28.
Proof. vm_refl. Qed.
Lemma D_64f28 : decode_any W_64f28 = Some (Store SZ8 9 15 1016, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f2c : bv 32 := 0x00048513.
Lemma F_64f2c : fetch_word Asan.M.loaded_segments (0x64f7c : word) = Some W_64f2c.
Proof. vm_refl. Qed.
Lemma D_64f2c : decode_any W_64f2c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f30 : bv 32 := 0x344000ef.
Lemma F_64f30 : fetch_word Asan.M.loaded_segments (0x64f80 : word) = Some W_64f30.
Proof. vm_refl. Qed.
Lemma D_64f30 : decode_any W_64f30 = Some (Jal 1 836, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f34 : bv 32 := 0x00050593.
Lemma F_64f34 : fetch_word Asan.M.loaded_segments (0x64f84 : word) = Some W_64f34.
Proof. vm_refl. Qed.
Lemma D_64f34 : decode_any W_64f34 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f38 : bv 32 := 0x00048513.
Lemma F_64f38 : fetch_word Asan.M.loaded_segments (0x64f88 : word) = Some W_64f38.
Proof. vm_refl. Qed.
Lemma D_64f38 : decode_any W_64f38 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f3c : bv 32 := 0x00000613.
Lemma F_64f3c : fetch_word Asan.M.loaded_segments (0x64f8c : word) = Some W_64f3c.
Proof. vm_refl. Qed.
Lemma D_64f3c : decode_any W_64f3c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f40 : bv 32 := 0x0005b023.
Lemma F_64f40 : fetch_word Asan.M.loaded_segments (0x64f90 : word) = Some W_64f40.
Proof. vm_refl. Qed.
Lemma D_64f40 : decode_any W_64f40 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f44 : bv 32 := 0x0005b423.
Lemma F_64f44 : fetch_word Asan.M.loaded_segments (0x64f94 : word) = Some W_64f44.
Proof. vm_refl. Qed.
Lemma D_64f44 : decode_any W_64f44 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f48 : bv 32 := 0x0005b823.
Lemma F_64f48 : fetch_word Asan.M.loaded_segments (0x64f98 : word) = Some W_64f48.
Proof. vm_refl. Qed.
Lemma D_64f48 : decode_any W_64f48 = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f4c : bv 32 := 0x0005bc23.
Lemma F_64f4c : fetch_word Asan.M.loaded_segments (0x64f9c : word) = Some W_64f4c.
Proof. vm_refl. Qed.
Lemma D_64f4c : decode_any W_64f4c = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f50 : bv 32 := 0x0205b023.
Lemma F_64f50 : fetch_word Asan.M.loaded_segments (0x64fa0 : word) = Some W_64f50.
Proof. vm_refl. Qed.
Lemma D_64f50 : decode_any W_64f50 = Some (Store SZ8 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f54 : bv 32 := 0x0205b423.
Lemma F_64f54 : fetch_word Asan.M.loaded_segments (0x64fa4 : word) = Some W_64f54.
Proof. vm_refl. Qed.
Lemma D_64f54 : decode_any W_64f54 = Some (Store SZ8 11 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f58 : bv 32 := 0x0205b823.
Lemma F_64f58 : fetch_word Asan.M.loaded_segments (0x64fa8 : word) = Some W_64f58.
Proof. vm_refl. Qed.
Lemma D_64f58 : decode_any W_64f58 = Some (Store SZ8 11 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f5c : bv 32 := 0x0205bc23.
Lemma F_64f5c : fetch_word Asan.M.loaded_segments (0x64fac : word) = Some W_64f5c.
Proof. vm_refl. Qed.
Lemma D_64f5c : decode_any W_64f5c = Some (Store SZ8 11 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f60 : bv 32 := 0x0405b023.
Lemma F_64f60 : fetch_word Asan.M.loaded_segments (0x64fb0 : word) = Some W_64f60.
Proof. vm_refl. Qed.
Lemma D_64f60 : decode_any W_64f60 = Some (Store SZ8 11 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f64 : bv 32 := 0x0405b423.
Lemma F_64f64 : fetch_word Asan.M.loaded_segments (0x64fb4 : word) = Some W_64f64.
Proof. vm_refl. Qed.
Lemma D_64f64 : decode_any W_64f64 = Some (Store SZ8 11 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f68 : bv 32 := 0x0405b823.
Lemma F_64f68 : fetch_word Asan.M.loaded_segments (0x64fb8 : word) = Some W_64f68.
Proof. vm_refl. Qed.
Lemma D_64f68 : decode_any W_64f68 = Some (Store SZ8 11 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f6c : bv 32 := 0x0405bc23.
Lemma F_64f6c : fetch_word Asan.M.loaded_segments (0x64fbc : word) = Some W_64f6c.
Proof. vm_refl. Qed.
Lemma D_64f6c : decode_any W_64f6c = Some (Store SZ8 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f70 : bv 32 := 0x0605b023.
Lemma F_64f70 : fetch_word Asan.M.loaded_segments (0x64fc0 : word) = Some W_64f70.
Proof. vm_refl. Qed.
Lemma D_64f70 : decode_any W_64f70 = Some (Store SZ8 11 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f74 : bv 32 := 0x0605b423.
Lemma F_64f74 : fetch_word Asan.M.loaded_segments (0x64fc4 : word) = Some W_64f74.
Proof. vm_refl. Qed.
Lemma D_64f74 : decode_any W_64f74 = Some (Store SZ8 11 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f78 : bv 32 := 0x0605b823.
Lemma F_64f78 : fetch_word Asan.M.loaded_segments (0x64fc8 : word) = Some W_64f78.
Proof. vm_refl. Qed.
Lemma D_64f78 : decode_any W_64f78 = Some (Store SZ8 11 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f7c : bv 32 := 0x0605bc23.
Lemma F_64f7c : fetch_word Asan.M.loaded_segments (0x64fcc : word) = Some W_64f7c.
Proof. vm_refl. Qed.
Lemma D_64f7c : decode_any W_64f7c = Some (Store SZ8 11 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f80 : bv 32 := 0x01813083.
Lemma F_64f80 : fetch_word Asan.M.loaded_segments (0x64fd0 : word) = Some W_64f80.
Proof. vm_refl. Qed.
Lemma D_64f80 : decode_any W_64f80 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f84 : bv 32 := 0x01013403.
Lemma F_64f84 : fetch_word Asan.M.loaded_segments (0x64fd4 : word) = Some W_64f84.
Proof. vm_refl. Qed.
Lemma D_64f84 : decode_any W_64f84 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f88 : bv 32 := 0x00813483.
Lemma F_64f88 : fetch_word Asan.M.loaded_segments (0x64fd8 : word) = Some W_64f88.
Proof. vm_refl. Qed.
Lemma D_64f88 : decode_any W_64f88 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f8c : bv 32 := 0x00013903.
Lemma F_64f8c : fetch_word Asan.M.loaded_segments (0x64fdc : word) = Some W_64f8c.
Proof. vm_refl. Qed.
Lemma D_64f8c : decode_any W_64f8c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f90 : bv 32 := 0x02010113.
Lemma F_64f90 : fetch_word Asan.M.loaded_segments (0x64fe0 : word) = Some W_64f90.
Proof. vm_refl. Qed.
Lemma D_64f90 : decode_any W_64f90 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f94 : bv 32 := 0x00008067.
Lemma F_64f94 : fetch_word Asan.M.loaded_segments (0x64fe4 : word) = Some W_64f94.
Proof. vm_refl. Qed.
Lemma D_64f94 : decode_any W_64f94 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f98 : bv 32 := 0x04853483.
Lemma F_64f98 : fetch_word Asan.M.loaded_segments (0x64fe8 : word) = Some W_64f98.
Proof. vm_refl. Qed.
Lemma D_64f98 : decode_any W_64f98 = Some (Load SZ8 true 9 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f9c : bv 32 := 0x00100593.
Lemma F_64f9c : fetch_word Asan.M.loaded_segments (0x64fec : word) = Some W_64f9c.
Proof. vm_refl. Qed.
Lemma D_64f9c : decode_any W_64f9c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fa0 : bv 32 := 0x0095e663.
Lemma F_64fa0 : fetch_word Asan.M.loaded_segments (0x64ff0 : word) = Some W_64fa0.
Proof. vm_refl. Qed.
Lemma D_64fa0 : decode_any W_64fa0 = Some (Branch BC_LTU 11 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fa4 : bv 32 := 0x28d250ef.
Lemma F_64fa4 : fetch_word Asan.M.loaded_segments (0x64ff4 : word) = Some W_64fa4.
Proof. vm_refl. Qed.
Lemma D_64fa4 : decode_any W_64fa4 = Some (Jal 1 154252, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fa8 : bv 32 := 0x00050493.
Lemma F_64fa8 : fetch_word Asan.M.loaded_segments (0x64ff8 : word) = Some W_64fa8.
Proof. vm_refl. Qed.
Lemma D_64fa8 : decode_any W_64fa8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fac : bv 32 := 0xe60494e3.
Lemma F_64fac : fetch_word Asan.M.loaded_segments (0x64ffc : word) = Some W_64fac.
Proof. vm_refl. Qed.
Lemma D_64fac : decode_any W_64fac = Some (Branch BC_NE 9 0 7784, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fb0 : bv 32 := 0xf11ff06f.
Lemma F_64fb0 : fetch_word Asan.M.loaded_segments (0x65000 : word) = Some W_64fb0.
Proof. vm_refl. Qed.
Lemma D_64fb0 : decode_any W_64fb0 = Some (Jal 0 2096912, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r63570_6373c.
Module Na0_code_r5dc38_5de44.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_64fb4 : bv 32 := 0xfe010113.
Lemma F_64fb4 : fetch_word Asan.M.loaded_segments (0x65004 : word) = Some W_64fb4.
Proof. vm_refl. Qed.
Lemma D_64fb4 : decode_any W_64fb4 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fb8 : bv 32 := 0x00113c23.
Lemma F_64fb8 : fetch_word Asan.M.loaded_segments (0x65008 : word) = Some W_64fb8.
Proof. vm_refl. Qed.
Lemma D_64fb8 : decode_any W_64fb8 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fbc : bv 32 := 0x00813823.
Lemma F_64fbc : fetch_word Asan.M.loaded_segments (0x6500c : word) = Some W_64fbc.
Proof. vm_refl. Qed.
Lemma D_64fbc : decode_any W_64fbc = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fc0 : bv 32 := 0x00913423.
Lemma F_64fc0 : fetch_word Asan.M.loaded_segments (0x65010 : word) = Some W_64fc0.
Proof. vm_refl. Qed.
Lemma D_64fc0 : decode_any W_64fc0 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fc4 : bv 32 := 0x01213023.
Lemma F_64fc4 : fetch_word Asan.M.loaded_segments (0x65014 : word) = Some W_64fc4.
Proof. vm_refl. Qed.
Lemma D_64fc4 : decode_any W_64fc4 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fc8 : bv 32 := 0x02010413.
Lemma F_64fc8 : fetch_word Asan.M.loaded_segments (0x65018 : word) = Some W_64fc8.
Proof. vm_refl. Qed.
Lemma D_64fc8 : decode_any W_64fc8 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fcc : bv 32 := 0x000f3517.
Lemma F_64fcc : fetch_word Asan.M.loaded_segments (0x6501c : word) = Some W_64fcc.
Proof. vm_refl. Qed.
Lemma D_64fcc : decode_any W_64fcc = Some (Auipc 10 243, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fd0 : bv 32 := 0xb7450513.
Lemma F_64fd0 : fetch_word Asan.M.loaded_segments (0x65020 : word) = Some W_64fd0.
Proof. vm_refl. Qed.
Lemma D_64fd0 : decode_any W_64fd0 = Some (OpImm ALU_ADD 10 10 2932, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fd4 : bv 32 := 0x2f4050ef.
Lemma F_64fd4 : fetch_word Asan.M.loaded_segments (0x65024 : word) = Some W_64fd4.
Proof. vm_refl. Qed.
Lemma D_64fd4 : decode_any W_64fd4 = Some (Jal 1 21236, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fd8 : bv 32 := 0x00053483.
Lemma F_64fd8 : fetch_word Asan.M.loaded_segments (0x65028 : word) = Some W_64fd8.
Proof. vm_refl. Qed.
Lemma D_64fd8 : decode_any W_64fd8 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fdc : bv 32 := 0x08048863.
Lemma F_64fdc : fetch_word Asan.M.loaded_segments (0x6502c : word) = Some W_64fdc.
Proof. vm_refl. Qed.
Lemma D_64fdc : decode_any W_64fdc = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fe0 : bv 32 := 0x0604c503.
Lemma F_64fe0 : fetch_word Asan.M.loaded_segments (0x65030 : word) = Some W_64fe0.
Proof. vm_refl. Qed.
Lemma D_64fe0 : decode_any W_64fe0 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fe4 : bv 32 := 0x0584b903.
Lemma F_64fe4 : fetch_word Asan.M.loaded_segments (0x65034 : word) = Some W_64fe4.
Proof. vm_refl. Qed.
Lemma D_64fe4 : decode_any W_64fe4 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fe8 : bv 32 := 0x00050863.
Lemma F_64fe8 : fetch_word Asan.M.loaded_segments (0x65038 : word) = Some W_64fe8.
Proof. vm_refl. Qed.
Lemma D_64fe8 : decode_any W_64fe8 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fec : bv 32 := 0x00048513.
Lemma F_64fec : fetch_word Asan.M.loaded_segments (0x6503c : word) = Some W_64fec.
Proof. vm_refl. Qed.
Lemma D_64fec : decode_any W_64fec = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ff0 : bv 32 := 0x00040593.
Lemma F_64ff0 : fetch_word Asan.M.loaded_segments (0x65040 : word) = Some W_64ff0.
Proof. vm_refl. Qed.
Lemma D_64ff0 : decode_any W_64ff0 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ff4 : bv 32 := 0xb5cff0ef.
Lemma F_64ff4 : fetch_word Asan.M.loaded_segments (0x65044 : word) = Some W_64ff4.
Proof. vm_refl. Qed.
Lemma D_64ff4 : decode_any W_64ff4 = Some (Jal 1 2093916, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ff8 : bv 32 := 0xff590593.
Lemma F_64ff8 : fetch_word Asan.M.loaded_segments (0x65048 : word) = Some W_64ff8.
Proof. vm_refl. Qed.
Lemma D_64ff8 : decode_any W_64ff8 = Some (OpImm ALU_ADD 11 18 4085, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ffc : bv 32 := 0x00100513.
Lemma F_64ffc : fetch_word Asan.M.loaded_segments (0x6504c : word) = Some W_64ffc.
Proof. vm_refl. Qed.
Lemma D_64ffc : decode_any W_64ffc = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_65000 : bv 32 := 0x00b51533.
Lemma F_65000 : fetch_word Asan.M.loaded_segments (0x65050 : word) = Some W_65000.
Proof. vm_refl. Qed.
Lemma D_65000 : decode_any W_65000 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_65004 : bv 32 := 0x0005061b.
Lemma F_65004 : fetch_word Asan.M.loaded_segments (0x65054 : word) = Some W_65004.
Proof. vm_refl. Qed.
Lemma D_65004 : decode_any W_65004 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65008 : bv 32 := 0x08c05263.
Lemma F_65008 : fetch_word Asan.M.loaded_segments (0x65058 : word) = Some W_65008.
Proof. vm_refl. Qed.
Lemma D_65008 : decode_any W_65008 = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_6500c : bv 32 := 0x000016b7.
Lemma F_6500c : fetch_word Asan.M.loaded_segments (0x6505c : word) = Some W_6500c.
Proof. vm_refl. Qed.
Lemma D_6500c : decode_any W_6500c = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_65010 : bv 32 := 0xff190613.
Lemma F_65010 : fetch_word Asan.M.loaded_segments (0x65060 : word) = Some W_65010.
Proof. vm_refl. Qed.
Lemma D_65010 : decode_any W_65010 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_65014 : bv 32 := 0x3e000713.
Lemma F_65014 : fetch_word Asan.M.loaded_segments (0x65064 : word) = Some W_65014.
Proof. vm_refl. Qed.
Lemma D_65014 : decode_any W_65014 = Some (OpImm ALU_ADD 14 0 992, 4%Z).
Proof. vm_refl. Qed.

Definition W_65018 : bv 32 := 0xfff00793.
Lemma F_65018 : fetch_word Asan.M.loaded_segments (0x65068 : word) = Some W_65018.
Proof. vm_refl. Qed.
Lemma D_65018 : decode_any W_65018 = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6501c : bv 32 := 0x00c71733.
Lemma F_6501c : fetch_word Asan.M.loaded_segments (0x6506c : word) = Some W_6501c.
Proof. vm_refl. Qed.
Lemma D_6501c : decode_any W_6501c = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_65020 : bv 32 := 0x0284b603.
Lemma F_65020 : fetch_word Asan.M.loaded_segments (0x65070 : word) = Some W_65020.
Proof. vm_refl. Qed.
Lemma D_65020 : decode_any W_65020 = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_65024 : bv 32 := 0x00b797b3.
Lemma F_65024 : fetch_word Asan.M.loaded_segments (0x65074 : word) = Some W_65024.
Proof. vm_refl. Qed.
Lemma D_65024 : decode_any W_65024 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_65028 : bv 32 := 0xfff50813.
Lemma F_65028 : fetch_word Asan.M.loaded_segments (0x65078 : word) = Some W_65028.
Proof. vm_refl. Qed.
Lemma D_65028 : decode_any W_65028 = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6502c : bv 32 := 0x00d485b3.
Lemma F_6502c : fetch_word Asan.M.loaded_segments (0x6507c : word) = Some W_6502c.
Proof. vm_refl. Qed.
Lemma D_6502c : decode_any W_6502c = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_65030 : bv 32 := 0x00e586b3.
Lemma F_65030 : fetch_word Asan.M.loaded_segments (0x65080 : word) = Some W_65030.
Proof. vm_refl. Qed.
Lemma D_65030 : decode_any W_65030 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_65034 : bv 32 := 0xfff7c713.
Lemma F_65034 : fetch_word Asan.M.loaded_segments (0x65084 : word) = Some W_65034.
Proof. vm_refl. Qed.
Lemma D_65034 : decode_any W_65034 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_65038 : bv 32 := 0x02081813.
Lemma F_65038 : fetch_word Asan.M.loaded_segments (0x65088 : word) = Some W_65038.
Proof. vm_refl. Qed.
Lemma D_65038 : decode_any W_65038 = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6503c : bv 32 := 0x02085793.
Lemma F_6503c : fetch_word Asan.M.loaded_segments (0x6508c : word) = Some W_6503c.
Proof. vm_refl. Qed.
Lemma D_6503c : decode_any W_6503c = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_65040 : bv 32 := 0x00f607b3.
Lemma F_65040 : fetch_word Asan.M.loaded_segments (0x65090 : word) = Some W_65040.
Proof. vm_refl. Qed.
Lemma D_65040 : decode_any W_65040 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_65044 : bv 32 := 0x00178813.
Lemma F_65044 : fetch_word Asan.M.loaded_segments (0x65094 : word) = Some W_65044.
Proof. vm_refl. Qed.
Lemma D_65044 : decode_any W_65044 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_65048 : bv 32 := 0x00e678b3.
Lemma F_65048 : fetch_word Asan.M.loaded_segments (0x65098 : word) = Some W_65048.
Proof. vm_refl. Qed.
Lemma D_65048 : decode_any W_65048 = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6504c : bv 32 := 0x011687b3.
Lemma F_6504c : fetch_word Asan.M.loaded_segments (0x6509c : word) = Some W_6504c.
Proof. vm_refl. Qed.
Lemma D_6504c : decode_any W_6504c = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_65050 : bv 32 := 0x0007c283.
Lemma F_65050 : fetch_word Asan.M.loaded_segments (0x650a0 : word) = Some W_65050.
Proof. vm_refl. Qed.
Lemma D_65050 : decode_any W_65050 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65054 : bv 32 := 0x06028663.
Lemma F_65054 : fetch_word Asan.M.loaded_segments (0x650a4 : word) = Some W_65054.
Proof. vm_refl. Qed.
Lemma D_65054 : decode_any W_65054 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_65058 : bv 32 := 0xfff5051b.
Lemma F_65058 : fetch_word Asan.M.loaded_segments (0x650a8 : word) = Some W_65058.
Proof. vm_refl. Qed.
Lemma D_65058 : decode_any W_65058 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6505c : bv 32 := 0x00160613.
Lemma F_6505c : fetch_word Asan.M.loaded_segments (0x650ac : word) = Some W_6505c.
Proof. vm_refl. Qed.
Lemma D_6505c : decode_any W_6505c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_65060 : bv 32 := 0xfe0514e3.
Lemma F_65060 : fetch_word Asan.M.loaded_segments (0x650b0 : word) = Some W_65060.
Proof. vm_refl. Qed.
Lemma D_65060 : decode_any W_65060 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_65064 : bv 32 := 0x0304b423.
Lemma F_65064 : fetch_word Asan.M.loaded_segments (0x650b4 : word) = Some W_65064.
Proof. vm_refl. Qed.
Lemma D_65064 : decode_any W_65064 = Some (Store SZ8 9 16 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_65068 : bv 32 := 0x0400006f.
Lemma F_65068 : fetch_word Asan.M.loaded_segments (0x650b8 : word) = Some W_65068.
Proof. vm_refl. Qed.
Lemma D_65068 : decode_any W_65068 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6506c : bv 32 := 0x000f2517.
Lemma F_6506c : fetch_word Asan.M.loaded_segments (0x650bc : word) = Some W_6506c.
Proof. vm_refl. Qed.
Lemma D_6506c : decode_any W_6506c = Some (Auipc 10 242, 4%Z).
Proof. vm_refl. Qed.

Definition W_65070 : bv 32 := 0xd3453503.
Lemma F_65070 : fetch_word Asan.M.loaded_segments (0x650c0 : word) = Some W_65070.
Proof. vm_refl. Qed.
Lemma D_65070 : decode_any W_65070 = Some (Load SZ8 true 10 10 3380, 4%Z).
Proof. vm_refl. Qed.

Definition W_65074 : bv 32 := 0x00052503.
Lemma F_65074 : fetch_word Asan.M.loaded_segments (0x650c4 : word) = Some W_65074.
Proof. vm_refl. Qed.
Lemma D_65074 : decode_any W_65074 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65078 : bv 32 := 0x02050863.
Lemma F_65078 : fetch_word Asan.M.loaded_segments (0x650c8 : word) = Some W_65078.
Proof. vm_refl. Qed.
Lemma D_65078 : decode_any W_65078 = Some (Branch BC_EQ 10 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_6507c : bv 32 := 0x740250ef.
Lemma F_6507c : fetch_word Asan.M.loaded_segments (0x650cc : word) = Some W_6507c.
Proof. vm_refl. Qed.
Lemma D_6507c : decode_any W_6507c = Some (Jal 1 153408, 4%Z).
Proof. vm_refl. Qed.

Definition W_65080 : bv 32 := 0x02050463.
Lemma F_65080 : fetch_word Asan.M.loaded_segments (0x650d0 : word) = Some W_65080.
Proof. vm_refl. Qed.
Lemma D_65080 : decode_any W_65080 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_65084 : bv 32 := 0x02850583.
Lemma F_65084 : fetch_word Asan.M.loaded_segments (0x650d4 : word) = Some W_65084.
Proof. vm_refl. Qed.
Lemma D_65084 : decode_any W_65084 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_65088 : bv 32 := 0x10058e63.
Lemma F_65088 : fetch_word Asan.M.loaded_segments (0x650d8 : word) = Some W_65088.
Proof. vm_refl. Qed.
Lemma D_65088 : decode_any W_65088 = Some (Branch BC_EQ 11 0 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_6508c : bv 32 := 0x00000513.
Lemma F_6508c : fetch_word Asan.M.loaded_segments (0x650dc : word) = Some W_6508c.
Proof. vm_refl. Qed.
Lemma D_6508c : decode_any W_6508c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65090 : bv 32 := 0x01813083.
Lemma F_65090 : fetch_word Asan.M.loaded_segments (0x650e0 : word) = Some W_65090.
Proof. vm_refl. Qed.
Lemma D_65090 : decode_any W_65090 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_65094 : bv 32 := 0x01013403.
Lemma F_65094 : fetch_word Asan.M.loaded_segments (0x650e4 : word) = Some W_65094.
Proof. vm_refl. Qed.
Lemma D_65094 : decode_any W_65094 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65098 : bv 32 := 0x00813483.
Lemma F_65098 : fetch_word Asan.M.loaded_segments (0x650e8 : word) = Some W_65098.
Proof. vm_refl. Qed.
Lemma D_65098 : decode_any W_65098 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6509c : bv 32 := 0x00013903.
Lemma F_6509c : fetch_word Asan.M.loaded_segments (0x650ec : word) = Some W_6509c.
Proof. vm_refl. Qed.
Lemma D_6509c : decode_any W_6509c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_650a0 : bv 32 := 0x02010113.
Lemma F_650a0 : fetch_word Asan.M.loaded_segments (0x650f0 : word) = Some W_650a0.
Proof. vm_refl. Qed.
Lemma D_650a0 : decode_any W_650a0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_650a4 : bv 32 := 0x00008067.
Lemma F_650a4 : fetch_word Asan.M.loaded_segments (0x650f4 : word) = Some W_650a4.
Proof. vm_refl. Qed.
Lemma D_650a4 : decode_any W_650a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_650a8 : bv 32 := 0x01813083.
Lemma F_650a8 : fetch_word Asan.M.loaded_segments (0x650f8 : word) = Some W_650a8.
Proof. vm_refl. Qed.
Lemma D_650a8 : decode_any W_650a8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_650ac : bv 32 := 0x01013403.
Lemma F_650ac : fetch_word Asan.M.loaded_segments (0x650fc : word) = Some W_650ac.
Proof. vm_refl. Qed.
Lemma D_650ac : decode_any W_650ac = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_650b0 : bv 32 := 0x00813483.
Lemma F_650b0 : fetch_word Asan.M.loaded_segments (0x65100 : word) = Some W_650b0.
Proof. vm_refl. Qed.
Lemma D_650b0 : decode_any W_650b0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_650b4 : bv 32 := 0x00013903.
Lemma F_650b4 : fetch_word Asan.M.loaded_segments (0x65104 : word) = Some W_650b4.
Proof. vm_refl. Qed.
Lemma D_650b4 : decode_any W_650b4 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_650b8 : bv 32 := 0x02010113.
Lemma F_650b8 : fetch_word Asan.M.loaded_segments (0x65108 : word) = Some W_650b8.
Proof. vm_refl. Qed.
Lemma D_650b8 : decode_any W_650b8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_650bc : bv 32 := 0x00008067.
Lemma F_650bc : fetch_word Asan.M.loaded_segments (0x6510c : word) = Some W_650bc.
Proof. vm_refl. Qed.
Lemma D_650bc : decode_any W_650bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_650c0 : bv 32 := 0x00160613.
Lemma F_650c0 : fetch_word Asan.M.loaded_segments (0x65110 : word) = Some W_650c0.
Proof. vm_refl. Qed.
Lemma D_650c0 : decode_any W_650c0 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_650c4 : bv 32 := 0x00100513.
Lemma F_650c4 : fetch_word Asan.M.loaded_segments (0x65114 : word) = Some W_650c4.
Proof. vm_refl. Qed.
Lemma D_650c4 : decode_any W_650c4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_650c8 : bv 32 := 0xffb90693.
Lemma F_650c8 : fetch_word Asan.M.loaded_segments (0x65118 : word) = Some W_650c8.
Proof. vm_refl. Qed.
Lemma D_650c8 : decode_any W_650c8 = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_650cc : bv 32 := 0x02c4b423.
Lemma F_650cc : fetch_word Asan.M.loaded_segments (0x6511c : word) = Some W_650cc.
Proof. vm_refl. Qed.
Lemma D_650cc : decode_any W_650cc = Some (Store SZ8 9 12 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_650d0 : bv 32 := 0x00a78023.
Lemma F_650d0 : fetch_word Asan.M.loaded_segments (0x65120 : word) = Some W_650d0.
Proof. vm_refl. Qed.
Lemma D_650d0 : decode_any W_650d0 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_650d4 : bv 32 := 0x00d51533.
Lemma F_650d4 : fetch_word Asan.M.loaded_segments (0x65124 : word) = Some W_650d4.
Proof. vm_refl. Qed.
Lemma D_650d4 : decode_any W_650d4 = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_650d8 : bv 32 := 0x00500613.
Lemma F_650d8 : fetch_word Asan.M.loaded_segments (0x65128 : word) = Some W_650d8.
Proof. vm_refl. Qed.
Lemma D_650d8 : decode_any W_650d8 = Some (OpImm ALU_ADD 12 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_650dc : bv 32 := 0x00b89893.
Lemma F_650dc : fetch_word Asan.M.loaded_segments (0x6512c : word) = Some W_650dc.
Proof. vm_refl. Qed.
Lemma D_650dc : decode_any W_650dc = Some (ShiftImm ALU_SLL 17 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_650e0 : bv 32 := 0x01261633.
Lemma F_650e0 : fetch_word Asan.M.loaded_segments (0x65130 : word) = Some W_650e0.
Proof. vm_refl. Qed.
Lemma D_650e0 : decode_any W_650e0 = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_650e4 : bv 32 := 0x00a58533.
Lemma F_650e4 : fetch_word Asan.M.loaded_segments (0x65134 : word) = Some W_650e4.
Proof. vm_refl. Qed.
Lemma D_650e4 : decode_any W_650e4 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_650e8 : bv 32 := 0x01160633.
Lemma F_650e8 : fetch_word Asan.M.loaded_segments (0x65138 : word) = Some W_650e8.
Proof. vm_refl. Qed.
Lemma D_650e8 : decode_any W_650e8 = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_650ec : bv 32 := 0x00c504b3.
Lemma F_650ec : fetch_word Asan.M.loaded_segments (0x6513c : word) = Some W_650ec.
Proof. vm_refl. Qed.
Lemma D_650ec : decode_any W_650ec = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_650f0 : bv 32 := 0x0084bc23.
Lemma F_650f0 : fetch_word Asan.M.loaded_segments (0x65140 : word) = Some W_650f0.
Proof. vm_refl. Qed.
Lemma D_650f0 : decode_any W_650f0 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_650f4 : bv 32 := 0x7ef4bc23.
Lemma F_650f4 : fetch_word Asan.M.loaded_segments (0x65144 : word) = Some W_650f4.
Proof. vm_refl. Qed.
Lemma D_650f4 : decode_any W_650f4 = Some (Store SZ8 9 15 2040, 4%Z).
Proof. vm_refl. Qed.

Definition W_650f8 : bv 32 := 0x00048513.
Lemma F_650f8 : fetch_word Asan.M.loaded_segments (0x65148 : word) = Some W_650f8.
Proof. vm_refl. Qed.
Lemma D_650f8 : decode_any W_650f8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_650fc : bv 32 := 0x178000ef.
Lemma F_650fc : fetch_word Asan.M.loaded_segments (0x6514c : word) = Some W_650fc.
Proof. vm_refl. Qed.
Lemma D_650fc : decode_any W_650fc = Some (Jal 1 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_65100 : bv 32 := 0x00050593.
Lemma F_65100 : fetch_word Asan.M.loaded_segments (0x65150 : word) = Some W_65100.
Proof. vm_refl. Qed.
Lemma D_65100 : decode_any W_65100 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65104 : bv 32 := 0x00048513.
Lemma F_65104 : fetch_word Asan.M.loaded_segments (0x65154 : word) = Some W_65104.
Proof. vm_refl. Qed.
Lemma D_65104 : decode_any W_65104 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65108 : bv 32 := 0x00000613.
Lemma F_65108 : fetch_word Asan.M.loaded_segments (0x65158 : word) = Some W_65108.
Proof. vm_refl. Qed.
Lemma D_65108 : decode_any W_65108 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6510c : bv 32 := 0x0005b023.
Lemma F_6510c : fetch_word Asan.M.loaded_segments (0x6515c : word) = Some W_6510c.
Proof. vm_refl. Qed.
Lemma D_6510c : decode_any W_6510c = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65110 : bv 32 := 0x0005b423.
Lemma F_65110 : fetch_word Asan.M.loaded_segments (0x65160 : word) = Some W_65110.
Proof. vm_refl. Qed.
Lemma D_65110 : decode_any W_65110 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65114 : bv 32 := 0x0005b823.
Lemma F_65114 : fetch_word Asan.M.loaded_segments (0x65164 : word) = Some W_65114.
Proof. vm_refl. Qed.
Lemma D_65114 : decode_any W_65114 = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65118 : bv 32 := 0x0005bc23.
Lemma F_65118 : fetch_word Asan.M.loaded_segments (0x65168 : word) = Some W_65118.
Proof. vm_refl. Qed.
Lemma D_65118 : decode_any W_65118 = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6511c : bv 32 := 0x0205b023.
Lemma F_6511c : fetch_word Asan.M.loaded_segments (0x6516c : word) = Some W_6511c.
Proof. vm_refl. Qed.
Lemma D_6511c : decode_any W_6511c = Some (Store SZ8 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_65120 : bv 32 := 0x0205b423.
Lemma F_65120 : fetch_word Asan.M.loaded_segments (0x65170 : word) = Some W_65120.
Proof. vm_refl. Qed.
Lemma D_65120 : decode_any W_65120 = Some (Store SZ8 11 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_65124 : bv 32 := 0x0205b823.
Lemma F_65124 : fetch_word Asan.M.loaded_segments (0x65174 : word) = Some W_65124.
Proof. vm_refl. Qed.
Lemma D_65124 : decode_any W_65124 = Some (Store SZ8 11 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_65128 : bv 32 := 0x0205bc23.
Lemma F_65128 : fetch_word Asan.M.loaded_segments (0x65178 : word) = Some W_65128.
Proof. vm_refl. Qed.
Lemma D_65128 : decode_any W_65128 = Some (Store SZ8 11 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_6512c : bv 32 := 0x0405b023.
Lemma F_6512c : fetch_word Asan.M.loaded_segments (0x6517c : word) = Some W_6512c.
Proof. vm_refl. Qed.
Lemma D_6512c : decode_any W_6512c = Some (Store SZ8 11 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_65130 : bv 32 := 0x0405b423.
Lemma F_65130 : fetch_word Asan.M.loaded_segments (0x65180 : word) = Some W_65130.
Proof. vm_refl. Qed.
Lemma D_65130 : decode_any W_65130 = Some (Store SZ8 11 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_65134 : bv 32 := 0x0405b823.
Lemma F_65134 : fetch_word Asan.M.loaded_segments (0x65184 : word) = Some W_65134.
Proof. vm_refl. Qed.
Lemma D_65134 : decode_any W_65134 = Some (Store SZ8 11 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_65138 : bv 32 := 0x0405bc23.
Lemma F_65138 : fetch_word Asan.M.loaded_segments (0x65188 : word) = Some W_65138.
Proof. vm_refl. Qed.
Lemma D_65138 : decode_any W_65138 = Some (Store SZ8 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_6513c : bv 32 := 0x0605b023.
Lemma F_6513c : fetch_word Asan.M.loaded_segments (0x6518c : word) = Some W_6513c.
Proof. vm_refl. Qed.
Lemma D_6513c : decode_any W_6513c = Some (Store SZ8 11 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_65140 : bv 32 := 0x0605b423.
Lemma F_65140 : fetch_word Asan.M.loaded_segments (0x65190 : word) = Some W_65140.
Proof. vm_refl. Qed.
Lemma D_65140 : decode_any W_65140 = Some (Store SZ8 11 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_65144 : bv 32 := 0x0605b823.
Lemma F_65144 : fetch_word Asan.M.loaded_segments (0x65194 : word) = Some W_65144.
Proof. vm_refl. Qed.
Lemma D_65144 : decode_any W_65144 = Some (Store SZ8 11 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_65148 : bv 32 := 0x0605bc23.
Lemma F_65148 : fetch_word Asan.M.loaded_segments (0x65198 : word) = Some W_65148.
Proof. vm_refl. Qed.
Lemma D_65148 : decode_any W_65148 = Some (Store SZ8 11 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_6514c : bv 32 := 0x0805b023.
Lemma F_6514c : fetch_word Asan.M.loaded_segments (0x6519c : word) = Some W_6514c.
Proof. vm_refl. Qed.
Lemma D_6514c : decode_any W_6514c = Some (Store SZ8 11 0 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_65150 : bv 32 := 0x0805b423.
Lemma F_65150 : fetch_word Asan.M.loaded_segments (0x651a0 : word) = Some W_65150.
Proof. vm_refl. Qed.
Lemma D_65150 : decode_any W_65150 = Some (Store SZ8 11 0 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_65154 : bv 32 := 0x0805b823.
Lemma F_65154 : fetch_word Asan.M.loaded_segments (0x651a4 : word) = Some W_65154.
Proof. vm_refl. Qed.
Lemma D_65154 : decode_any W_65154 = Some (Store SZ8 11 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_65158 : bv 32 := 0x0805bc23.
Lemma F_65158 : fetch_word Asan.M.loaded_segments (0x651a8 : word) = Some W_65158.
Proof. vm_refl. Qed.
Lemma D_65158 : decode_any W_65158 = Some (Store SZ8 11 0 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_6515c : bv 32 := 0x0a05b023.
Lemma F_6515c : fetch_word Asan.M.loaded_segments (0x651ac : word) = Some W_6515c.
Proof. vm_refl. Qed.
Lemma D_6515c : decode_any W_6515c = Some (Store SZ8 11 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_65160 : bv 32 := 0x0a05b423.
Lemma F_65160 : fetch_word Asan.M.loaded_segments (0x651b0 : word) = Some W_65160.
Proof. vm_refl. Qed.
Lemma D_65160 : decode_any W_65160 = Some (Store SZ8 11 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_65164 : bv 32 := 0x0a05b823.
Lemma F_65164 : fetch_word Asan.M.loaded_segments (0x651b4 : word) = Some W_65164.
Proof. vm_refl. Qed.
Lemma D_65164 : decode_any W_65164 = Some (Store SZ8 11 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_65168 : bv 32 := 0x0a05bc23.
Lemma F_65168 : fetch_word Asan.M.loaded_segments (0x651b8 : word) = Some W_65168.
Proof. vm_refl. Qed.
Lemma D_65168 : decode_any W_65168 = Some (Store SZ8 11 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_6516c : bv 32 := 0x0c05b023.
Lemma F_6516c : fetch_word Asan.M.loaded_segments (0x651bc : word) = Some W_6516c.
Proof. vm_refl. Qed.
Lemma D_6516c : decode_any W_6516c = Some (Store SZ8 11 0 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_65170 : bv 32 := 0x0c05b423.
Lemma F_65170 : fetch_word Asan.M.loaded_segments (0x651c0 : word) = Some W_65170.
Proof. vm_refl. Qed.
Lemma D_65170 : decode_any W_65170 = Some (Store SZ8 11 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_65174 : bv 32 := 0x0c05b823.
Lemma F_65174 : fetch_word Asan.M.loaded_segments (0x651c4 : word) = Some W_65174.
Proof. vm_refl. Qed.
Lemma D_65174 : decode_any W_65174 = Some (Store SZ8 11 0 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_65178 : bv 32 := 0x0c05bc23.
Lemma F_65178 : fetch_word Asan.M.loaded_segments (0x651c8 : word) = Some W_65178.
Proof. vm_refl. Qed.
Lemma D_65178 : decode_any W_65178 = Some (Store SZ8 11 0 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_6517c : bv 32 := 0x0e05b023.
Lemma F_6517c : fetch_word Asan.M.loaded_segments (0x651cc : word) = Some W_6517c.
Proof. vm_refl. Qed.
Lemma D_6517c : decode_any W_6517c = Some (Store SZ8 11 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_65180 : bv 32 := 0x0e05b423.
Lemma F_65180 : fetch_word Asan.M.loaded_segments (0x651d0 : word) = Some W_65180.
Proof. vm_refl. Qed.
Lemma D_65180 : decode_any W_65180 = Some (Store SZ8 11 0 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_65184 : bv 32 := 0x0e05b823.
Lemma F_65184 : fetch_word Asan.M.loaded_segments (0x651d4 : word) = Some W_65184.
Proof. vm_refl. Qed.
Lemma D_65184 : decode_any W_65184 = Some (Store SZ8 11 0 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_65188 : bv 32 := 0x0e05bc23.
Lemma F_65188 : fetch_word Asan.M.loaded_segments (0x651d8 : word) = Some W_65188.
Proof. vm_refl. Qed.
Lemma D_65188 : decode_any W_65188 = Some (Store SZ8 11 0 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_6518c : bv 32 := 0x01813083.
Lemma F_6518c : fetch_word Asan.M.loaded_segments (0x651dc : word) = Some W_6518c.
Proof. vm_refl. Qed.
Lemma D_6518c : decode_any W_6518c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_65190 : bv 32 := 0x01013403.
Lemma F_65190 : fetch_word Asan.M.loaded_segments (0x651e0 : word) = Some W_65190.
Proof. vm_refl. Qed.
Lemma D_65190 : decode_any W_65190 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65194 : bv 32 := 0x00813483.
Lemma F_65194 : fetch_word Asan.M.loaded_segments (0x651e4 : word) = Some W_65194.
Proof. vm_refl. Qed.
Lemma D_65194 : decode_any W_65194 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65198 : bv 32 := 0x00013903.
Lemma F_65198 : fetch_word Asan.M.loaded_segments (0x651e8 : word) = Some W_65198.
Proof. vm_refl. Qed.
Lemma D_65198 : decode_any W_65198 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6519c : bv 32 := 0x02010113.
Lemma F_6519c : fetch_word Asan.M.loaded_segments (0x651ec : word) = Some W_6519c.
Proof. vm_refl. Qed.
Lemma D_6519c : decode_any W_6519c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_651a0 : bv 32 := 0x00008067.
Lemma F_651a0 : fetch_word Asan.M.loaded_segments (0x651f0 : word) = Some W_651a0.
Proof. vm_refl. Qed.
Lemma D_651a0 : decode_any W_651a0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_651a4 : bv 32 := 0x04853483.
Lemma F_651a4 : fetch_word Asan.M.loaded_segments (0x651f4 : word) = Some W_651a4.
Proof. vm_refl. Qed.
Lemma D_651a4 : decode_any W_651a4 = Some (Load SZ8 true 9 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_651a8 : bv 32 := 0x00100593.
Lemma F_651a8 : fetch_word Asan.M.loaded_segments (0x651f8 : word) = Some W_651a8.
Proof. vm_refl. Qed.
Lemma D_651a8 : decode_any W_651a8 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_651ac : bv 32 := 0x0095e663.
Lemma F_651ac : fetch_word Asan.M.loaded_segments (0x651fc : word) = Some W_651ac.
Proof. vm_refl. Qed.
Lemma D_651ac : decode_any W_651ac = Some (Branch BC_LTU 11 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_651b0 : bv 32 := 0x081250ef.
Lemma F_651b0 : fetch_word Asan.M.loaded_segments (0x65200 : word) = Some W_651b0.
Proof. vm_refl. Qed.
Lemma D_651b0 : decode_any W_651b0 = Some (Jal 1 153728, 4%Z).
Proof. vm_refl. Qed.

Definition W_651b4 : bv 32 := 0x00050493.
Lemma F_651b4 : fetch_word Asan.M.loaded_segments (0x65204 : word) = Some W_651b4.
Proof. vm_refl. Qed.
Lemma D_651b4 : decode_any W_651b4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_651b8 : bv 32 := 0xe20494e3.
Lemma F_651b8 : fetch_word Asan.M.loaded_segments (0x65208 : word) = Some W_651b8.
Proof. vm_refl. Qed.
Lemma D_651b8 : decode_any W_651b8 = Some (Branch BC_NE 9 0 7720, 4%Z).
Proof. vm_refl. Qed.

Definition W_651bc : bv 32 := 0xed1ff06f.
Lemma F_651bc : fetch_word Asan.M.loaded_segments (0x6520c : word) = Some W_651bc.
Proof. vm_refl. Qed.
Lemma D_651bc : decode_any W_651bc = Some (Jal 0 2096848, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r5dc38_5de44.

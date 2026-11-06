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

Definition W_7c3b0 : bv 32 := 0x81010113.
Lemma F_7c3b0 : fetch_word Asan.M.loaded_segments (0x7c400 : word) = Some W_7c3b0.
Proof. vm_refl. Qed.
Lemma D_7c3b0 : decode_any W_7c3b0 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c3b4 : bv 32 := 0x7e113423.
Lemma F_7c3b4 : fetch_word Asan.M.loaded_segments (0x7c404 : word) = Some W_7c3b4.
Proof. vm_refl. Qed.
Lemma D_7c3b4 : decode_any W_7c3b4 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c3b8 : bv 32 := 0x7e813023.
Lemma F_7c3b8 : fetch_word Asan.M.loaded_segments (0x7c408 : word) = Some W_7c3b8.
Proof. vm_refl. Qed.
Lemma D_7c3b8 : decode_any W_7c3b8 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c3bc : bv 32 := 0x7c913c23.
Lemma F_7c3bc : fetch_word Asan.M.loaded_segments (0x7c40c : word) = Some W_7c3bc.
Proof. vm_refl. Qed.
Lemma D_7c3bc : decode_any W_7c3bc = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c3c0 : bv 32 := 0x7d213823.
Lemma F_7c3c0 : fetch_word Asan.M.loaded_segments (0x7c410 : word) = Some W_7c3c0.
Proof. vm_refl. Qed.
Lemma D_7c3c0 : decode_any W_7c3c0 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c3c4 : bv 32 := 0x7d313423.
Lemma F_7c3c4 : fetch_word Asan.M.loaded_segments (0x7c414 : word) = Some W_7c3c4.
Proof. vm_refl. Qed.
Lemma D_7c3c4 : decode_any W_7c3c4 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c3c8 : bv 32 := 0x7d413023.
Lemma F_7c3c8 : fetch_word Asan.M.loaded_segments (0x7c418 : word) = Some W_7c3c8.
Proof. vm_refl. Qed.
Lemma D_7c3c8 : decode_any W_7c3c8 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c3cc : bv 32 := 0x7b513c23.
Lemma F_7c3cc : fetch_word Asan.M.loaded_segments (0x7c41c : word) = Some W_7c3cc.
Proof. vm_refl. Qed.
Lemma D_7c3cc : decode_any W_7c3cc = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c3d0 : bv 32 := 0x7f010413.
Lemma F_7c3d0 : fetch_word Asan.M.loaded_segments (0x7c420 : word) = Some W_7c3d0.
Proof. vm_refl. Qed.
Lemma D_7c3d0 : decode_any W_7c3d0 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c3d4 : bv 32 := 0xfa010113.
Lemma F_7c3d4 : fetch_word Asan.M.loaded_segments (0x7c424 : word) = Some W_7c3d4.
Proof. vm_refl. Qed.
Lemma D_7c3d4 : decode_any W_7c3d4 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c3d8 : bv 32 := 0x00058a13.
Lemma F_7c3d8 : fetch_word Asan.M.loaded_segments (0x7c428 : word) = Some W_7c3d8.
Proof. vm_refl. Qed.
Lemma D_7c3d8 : decode_any W_7c3d8 = Some (OpImm ALU_ADD 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c3dc : bv 32 := 0x000bd597.
Lemma F_7c3dc : fetch_word Asan.M.loaded_segments (0x7c42c : word) = Some W_7c3dc.
Proof. vm_refl. Qed.
Lemma D_7c3dc : decode_any W_7c3dc = Some (Auipc 11 189, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c3e0 : bv 32 := 0xd845b583.
Lemma F_7c3e0 : fetch_word Asan.M.loaded_segments (0x7c430 : word) = Some W_7c3e0.
Proof. vm_refl. Qed.
Lemma D_7c3e0 : decode_any W_7c3e0 = Some (Load SZ8 true 11 11 3460, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c3e4 : bv 32 := 0x0605c583.
Lemma F_7c3e4 : fetch_word Asan.M.loaded_segments (0x7c434 : word) = Some W_7c3e4.
Proof. vm_refl. Qed.
Lemma D_7c3e4 : decode_any W_7c3e4 = Some (Load SZ1 false 11 11 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c3e8 : bv 32 := 0x22058863.
Lemma F_7c3e8 : fetch_word Asan.M.loaded_segments (0x7c438 : word) = Some W_7c3e8.
Proof. vm_refl. Qed.
Lemma D_7c3e8 : decode_any W_7c3e8 = Some (Branch BC_EQ 11 0 560, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c3ec : bv 32 := 0x00068913.
Lemma F_7c3ec : fetch_word Asan.M.loaded_segments (0x7c43c : word) = Some W_7c3ec.
Proof. vm_refl. Qed.
Lemma D_7c3ec : decode_any W_7c3ec = Some (OpImm ALU_ADD 18 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c3f0 : bv 32 := 0x00060993.
Lemma F_7c3f0 : fetch_word Asan.M.loaded_segments (0x7c440 : word) = Some W_7c3f0.
Proof. vm_refl. Qed.
Lemma D_7c3f0 : decode_any W_7c3f0 = Some (OpImm ALU_ADD 19 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c3f4 : bv 32 := 0x00050493.
Lemma F_7c3f4 : fetch_word Asan.M.loaded_segments (0x7c444 : word) = Some W_7c3f4.
Proof. vm_refl. Qed.
Lemma D_7c3f4 : decode_any W_7c3f4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c3f8 : bv 32 := 0x000bd517.
Lemma F_7c3f8 : fetch_word Asan.M.loaded_segments (0x7c448 : word) = Some W_7c3f8.
Proof. vm_refl. Qed.
Lemma D_7c3f8 : decode_any W_7c3f8 = Some (Auipc 10 189, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c3fc : bv 32 := 0xdc053503.
Lemma F_7c3fc : fetch_word Asan.M.loaded_segments (0x7c44c : word) = Some W_7c3fc.
Proof. vm_refl. Qed.
Lemma D_7c3fc : decode_any W_7c3fc = Some (Load SZ8 true 10 10 3520, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c400 : bv 32 := 0x00052503.
Lemma F_7c400 : fetch_word Asan.M.loaded_segments (0x7c450 : word) = Some W_7c400.
Proof. vm_refl. Qed.
Lemma D_7c400 : decode_any W_7c400 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c404 : bv 32 := 0x00300593.
Lemma F_7c404 : fetch_word Asan.M.loaded_segments (0x7c454 : word) = Some W_7c404.
Proof. vm_refl. Qed.
Lemma D_7c404 : decode_any W_7c404 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c408 : bv 32 := 0x08b57063.
Lemma F_7c408 : fetch_word Asan.M.loaded_segments (0x7c458 : word) = Some W_7c408.
Proof. vm_refl. Qed.
Lemma D_7c408 : decode_any W_7c408 = Some (Branch BC_GEU 10 11 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c40c : bv 32 := 0x0899fe63.
Lemma F_7c40c : fetch_word Asan.M.loaded_segments (0x7c45c : word) = Some W_7c40c.
Proof. vm_refl. Qed.
Lemma D_7c40c : decode_any W_7c40c = Some (Branch BC_GEU 19 9 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c410 : bv 32 := 0x80040513.
Lemma F_7c410 : fetch_word Asan.M.loaded_segments (0x7c460 : word) = Some W_7c410.
Proof. vm_refl. Qed.
Lemma D_7c410 : decode_any W_7c410 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c414 : bv 32 := 0xfb050513.
Lemma F_7c414 : fetch_word Asan.M.loaded_segments (0x7c464 : word) = Some W_7c414.
Proof. vm_refl. Qed.
Lemma D_7c414 : decode_any W_7c414 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c418 : bv 32 := 0x80040593.
Lemma F_7c418 : fetch_word Asan.M.loaded_segments (0x7c468 : word) = Some W_7c418.
Proof. vm_refl. Qed.
Lemma D_7c418 : decode_any W_7c418 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c41c : bv 32 := 0xfc058593.
Lemma F_7c41c : fetch_word Asan.M.loaded_segments (0x7c46c : word) = Some W_7c41c.
Proof. vm_refl. Qed.
Lemma D_7c41c : decode_any W_7c41c = Some (OpImm ALU_ADD 11 11 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c420 : bv 32 := 0x80040613.
Lemma F_7c420 : fetch_word Asan.M.loaded_segments (0x7c470 : word) = Some W_7c420.
Proof. vm_refl. Qed.
Lemma D_7c420 : decode_any W_7c420 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c424 : bv 32 := 0xfb060613.
Lemma F_7c424 : fetch_word Asan.M.loaded_segments (0x7c474 : word) = Some W_7c424.
Proof. vm_refl. Qed.
Lemma D_7c424 : decode_any W_7c424 = Some (OpImm ALU_ADD 12 12 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c428 : bv 32 := 0x7ff60a93.
Lemma F_7c428 : fetch_word Asan.M.loaded_segments (0x7c478 : word) = Some W_7c428.
Proof. vm_refl. Qed.
Lemma D_7c428 : decode_any W_7c428 = Some (OpImm ALU_ADD 21 12 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c42c : bv 32 := 0x000ab4a3.
Lemma F_7c42c : fetch_word Asan.M.loaded_segments (0x7c47c : word) = Some W_7c42c.
Proof. vm_refl. Qed.
Lemma D_7c42c : decode_any W_7c42c = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c430 : bv 32 := 0x00b53023.
Lemma F_7c430 : fetch_word Asan.M.loaded_segments (0x7c480 : word) = Some W_7c430.
Proof. vm_refl. Qed.
Lemma D_7c430 : decode_any W_7c430 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c434 : bv 32 := 0x00053423.
Lemma F_7c434 : fetch_word Asan.M.loaded_segments (0x7c484 : word) = Some W_7c434.
Proof. vm_refl. Qed.
Lemma D_7c434 : decode_any W_7c434 = Some (Store SZ8 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c438 : bv 32 := 0x6451e0ef.
Lemma F_7c438 : fetch_word Asan.M.loaded_segments (0x7c488 : word) = Some W_7c438.
Proof. vm_refl. Qed.
Lemma D_7c438 : decode_any W_7c438 = Some (Jal 1 126532, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c43c : bv 32 := 0x00050593.
Lemma F_7c43c : fetch_word Asan.M.loaded_segments (0x7c48c : word) = Some W_7c43c.
Proof. vm_refl. Qed.
Lemma D_7c43c : decode_any W_7c43c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c440 : bv 32 := 0x000bd517.
Lemma F_7c440 : fetch_word Asan.M.loaded_segments (0x7c490 : word) = Some W_7c440.
Proof. vm_refl. Qed.
Lemma D_7c440 : decode_any W_7c440 = Some (Auipc 10 189, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c444 : bv 32 := 0xd1853503.
Lemma F_7c444 : fetch_word Asan.M.loaded_segments (0x7c494 : word) = Some W_7c444.
Proof. vm_refl. Qed.
Lemma D_7c444 : decode_any W_7c444 = Some (Load SZ8 true 10 10 3352, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c448 : bv 32 := 0x02154703.
Lemma F_7c448 : fetch_word Asan.M.loaded_segments (0x7c498 : word) = Some W_7c448.
Proof. vm_refl. Qed.
Lemma D_7c448 : decode_any W_7c448 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c44c : bv 32 := 0x008ab4a3.
Lemma F_7c44c : fetch_word Asan.M.loaded_segments (0x7c49c : word) = Some W_7c44c.
Proof. vm_refl. Qed.
Lemma D_7c44c : decode_any W_7c44c = Some (Store SZ8 21 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c450 : bv 32 := 0x80040513.
Lemma F_7c450 : fetch_word Asan.M.loaded_segments (0x7c4a0 : word) = Some W_7c450.
Proof. vm_refl. Qed.
Lemma D_7c450 : decode_any W_7c450 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c454 : bv 32 := 0xfb050513.
Lemma F_7c454 : fetch_word Asan.M.loaded_segments (0x7c4a4 : word) = Some W_7c454.
Proof. vm_refl. Qed.
Lemma D_7c454 : decode_any W_7c454 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c458 : bv 32 := 0x0ff00793.
Lemma F_7c458 : fetch_word Asan.M.loaded_segments (0x7c4a8 : word) = Some W_7c458.
Proof. vm_refl. Qed.
Lemma D_7c458 : decode_any W_7c458 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c45c : bv 32 := 0x00040613.
Lemma F_7c45c : fetch_word Asan.M.loaded_segments (0x7c4ac : word) = Some W_7c45c.
Proof. vm_refl. Qed.
Lemma D_7c45c : decode_any W_7c45c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c460 : bv 32 := 0x00000693.
Lemma F_7c460 : fetch_word Asan.M.loaded_segments (0x7c4b0 : word) = Some W_7c460.
Proof. vm_refl. Qed.
Lemma D_7c460 : decode_any W_7c460 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c464 : bv 32 := 0x34c060ef.
Lemma F_7c464 : fetch_word Asan.M.loaded_segments (0x7c4b4 : word) = Some W_7c464.
Proof. vm_refl. Qed.
Lemma D_7c464 : decode_any W_7c464 = Some (Jal 1 25420, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c468 : bv 32 := 0x80040713.
Lemma F_7c468 : fetch_word Asan.M.loaded_segments (0x7c4b8 : word) = Some W_7c468.
Proof. vm_refl. Qed.
Lemma D_7c468 : decode_any W_7c468 = Some (OpImm ALU_ADD 14 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c46c : bv 32 := 0xfb070713.
Lemma F_7c46c : fetch_word Asan.M.loaded_segments (0x7c4bc : word) = Some W_7c46c.
Proof. vm_refl. Qed.
Lemma D_7c46c : decode_any W_7c46c = Some (OpImm ALU_ADD 14 14 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c470 : bv 32 := 0x00048513.
Lemma F_7c470 : fetch_word Asan.M.loaded_segments (0x7c4c0 : word) = Some W_7c470.
Proof. vm_refl. Qed.
Lemma D_7c470 : decode_any W_7c470 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c474 : bv 32 := 0x000a0593.
Lemma F_7c474 : fetch_word Asan.M.loaded_segments (0x7c4c4 : word) = Some W_7c474.
Proof. vm_refl. Qed.
Lemma D_7c474 : decode_any W_7c474 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c478 : bv 32 := 0x00098613.
Lemma F_7c478 : fetch_word Asan.M.loaded_segments (0x7c4c8 : word) = Some W_7c478.
Proof. vm_refl. Qed.
Lemma D_7c478 : decode_any W_7c478 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c47c : bv 32 := 0x00090693.
Lemma F_7c47c : fetch_word Asan.M.loaded_segments (0x7c4cc : word) = Some W_7c47c.
Proof. vm_refl. Qed.
Lemma D_7c47c : decode_any W_7c47c = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c480 : bv 32 := 0x0e0030ef.
Lemma F_7c480 : fetch_word Asan.M.loaded_segments (0x7c4d0 : word) = Some W_7c480.
Proof. vm_refl. Qed.
Lemma D_7c480 : decode_any W_7c480 = Some (Jal 1 12512, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c484 : bv 32 := 0x0300006f.
Lemma F_7c484 : fetch_word Asan.M.loaded_segments (0x7c4d4 : word) = Some W_7c484.
Proof. vm_refl. Qed.
Lemma D_7c484 : decode_any W_7c484 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c488 : bv 32 := 0xfff9d517.
Lemma F_7c488 : fetch_word Asan.M.loaded_segments (0x7c4d8 : word) = Some W_7c488.
Proof. vm_refl. Qed.
Lemma D_7c488 : decode_any W_7c488 = Some (Auipc 10 1048477, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c48c : bv 32 := 0xe7350513.
Lemma F_7c48c : fetch_word Asan.M.loaded_segments (0x7c4dc : word) = Some W_7c48c.
Proof. vm_refl. Qed.
Lemma D_7c48c : decode_any W_7c48c = Some (OpImm ALU_ADD 10 10 3699, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c490 : bv 32 := 0x00048593.
Lemma F_7c490 : fetch_word Asan.M.loaded_segments (0x7c4e0 : word) = Some W_7c490.
Proof. vm_refl. Qed.
Lemma D_7c490 : decode_any W_7c490 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c494 : bv 32 := 0x000a0613.
Lemma F_7c494 : fetch_word Asan.M.loaded_segments (0x7c4e4 : word) = Some W_7c494.
Proof. vm_refl. Qed.
Lemma D_7c494 : decode_any W_7c494 = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c498 : bv 32 := 0x00098693.
Lemma F_7c498 : fetch_word Asan.M.loaded_segments (0x7c4e8 : word) = Some W_7c498.
Proof. vm_refl. Qed.
Lemma D_7c498 : decode_any W_7c498 = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c49c : bv 32 := 0x00090713.
Lemma F_7c49c : fetch_word Asan.M.loaded_segments (0x7c4ec : word) = Some W_7c49c.
Proof. vm_refl. Qed.
Lemma D_7c49c : decode_any W_7c49c = Some (OpImm ALU_ADD 14 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c4a0 : bv 32 := 0x491120ef.
Lemma F_7c4a0 : fetch_word Asan.M.loaded_segments (0x7c4f0 : word) = Some W_7c4a0.
Proof. vm_refl. Qed.
Lemma D_7c4a0 : decode_any W_7c4a0 = Some (Jal 1 76944, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c4a4 : bv 32 := 0xf699e6e3.
Lemma F_7c4a4 : fetch_word Asan.M.loaded_segments (0x7c4f4 : word) = Some W_7c4a4.
Proof. vm_refl. Qed.
Lemma D_7c4a4 : decode_any W_7c4a4 = Some (Branch BC_LTU 19 9 8044, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c4a8 : bv 32 := 0xf72a64e3.
Lemma F_7c4a8 : fetch_word Asan.M.loaded_segments (0x7c4f8 : word) = Some W_7c4a8.
Proof. vm_refl. Qed.
Lemma D_7c4a8 : decode_any W_7c4a8 = Some (Branch BC_LTU 20 18 8040, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c4ac : bv 32 := 0xf73a62e3.
Lemma F_7c4ac : fetch_word Asan.M.loaded_segments (0x7c4fc : word) = Some W_7c4ac.
Proof. vm_refl. Qed.
Lemma D_7c4ac : decode_any W_7c4ac = Some (Branch BC_LTU 20 19 8036, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c4b0 : bv 32 := 0xf69960e3.
Lemma F_7c4b0 : fetch_word Asan.M.loaded_segments (0x7c500 : word) = Some W_7c4b0.
Proof. vm_refl. Qed.
Lemma D_7c4b0 : decode_any W_7c4b0 = Some (Branch BC_LTU 18 9 8032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c4b4 : bv 32 := 0x409a06b3.
Lemma F_7c4b4 : fetch_word Asan.M.loaded_segments (0x7c504 : word) = Some W_7c4b4.
Proof. vm_refl. Qed.
Lemma D_7c4b4 : decode_any W_7c4b4 = Some (Op ALU_SUB 13 20 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c4b8 : bv 32 := 0x00100713.
Lemma F_7c4b8 : fetch_word Asan.M.loaded_segments (0x7c508 : word) = Some W_7c4b8.
Proof. vm_refl. Qed.
Lemma D_7c4b8 : decode_any W_7c4b8 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c4bc : bv 32 := 0x02871713.
Lemma F_7c4bc : fetch_word Asan.M.loaded_segments (0x7c50c : word) = Some W_7c4bc.
Proof. vm_refl. Qed.
Lemma D_7c4bc : decode_any W_7c4bc = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c4c0 : bv 32 := 0x00170513.
Lemma F_7c4c0 : fetch_word Asan.M.loaded_segments (0x7c510 : word) = Some W_7c4c0.
Proof. vm_refl. Qed.
Lemma D_7c4c0 : decode_any W_7c4c0 = Some (OpImm ALU_ADD 10 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c4c4 : bv 32 := 0x04a6fa63.
Lemma F_7c4c4 : fetch_word Asan.M.loaded_segments (0x7c514 : word) = Some W_7c4c4.
Proof. vm_refl. Qed.
Lemma D_7c4c4 : decode_any W_7c4c4 = Some (Branch BC_GEU 13 10 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c4c8 : bv 32 := 0x15298863.
Lemma F_7c4c8 : fetch_word Asan.M.loaded_segments (0x7c518 : word) = Some W_7c4c8.
Proof. vm_refl. Qed.
Lemma D_7c4c8 : decode_any W_7c4c8 = Some (Branch BC_EQ 19 18 336, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c4cc : bv 32 := 0x007a7513.
Lemma F_7c4cc : fetch_word Asan.M.loaded_segments (0x7c51c : word) = Some W_7c4cc.
Proof. vm_refl. Qed.
Lemma D_7c4cc : decode_any W_7c4cc = Some (OpImm ALU_AND 10 20 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c4d0 : bv 32 := 0x06051063.
Lemma F_7c4d0 : fetch_word Asan.M.loaded_segments (0x7c520 : word) = Some W_7c4d0.
Proof. vm_refl. Qed.
Lemma D_7c4d0 : decode_any W_7c4d0 = Some (Branch BC_NE 10 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c4d4 : bv 32 := 0x00098a13.
Lemma F_7c4d4 : fetch_word Asan.M.loaded_segments (0x7c524 : word) = Some W_7c4d4.
Proof. vm_refl. Qed.
Lemma D_7c4d4 : decode_any W_7c4d4 = Some (OpImm ALU_ADD 20 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c4d8 : bv 32 := 0x00090a93.
Lemma F_7c4d8 : fetch_word Asan.M.loaded_segments (0x7c528 : word) = Some W_7c4d8.
Proof. vm_refl. Qed.
Lemma D_7c4d8 : decode_any W_7c4d8 = Some (OpImm ALU_ADD 21 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c4dc : bv 32 := 0x00048513.
Lemma F_7c4dc : fetch_word Asan.M.loaded_segments (0x7c52c : word) = Some W_7c4dc.
Proof. vm_refl. Qed.
Lemma D_7c4dc : decode_any W_7c4dc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c4e0 : bv 32 := 0x0074f993.
Lemma F_7c4e0 : fetch_word Asan.M.loaded_segments (0x7c530 : word) = Some W_7c4e0.
Proof. vm_refl. Qed.
Lemma D_7c4e0 : decode_any W_7c4e0 = Some (OpImm ALU_AND 19 9 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c4e4 : bv 32 := 0x08099e63.
Lemma F_7c4e4 : fetch_word Asan.M.loaded_segments (0x7c534 : word) = Some W_7c4e4.
Proof. vm_refl. Qed.
Lemma D_7c4e4 : decode_any W_7c4e4 = Some (Branch BC_NE 19 0 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c4e8 : bv 32 := 0x000a0593.
Lemma F_7c4e8 : fetch_word Asan.M.loaded_segments (0x7c538 : word) = Some W_7c4e8.
Proof. vm_refl. Qed.
Lemma D_7c4e8 : decode_any W_7c4e8 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c4ec : bv 32 := 0x000a0513.
Lemma F_7c4ec : fetch_word Asan.M.loaded_segments (0x7c53c : word) = Some W_7c4ec.
Proof. vm_refl. Qed.
Lemma D_7c4ec : decode_any W_7c4ec = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c4f0 : bv 32 := 0x0d5a6863.
Lemma F_7c4f0 : fetch_word Asan.M.loaded_segments (0x7c540 : word) = Some W_7c4f0.
Proof. vm_refl. Qed.
Lemma D_7c4f0 : decode_any W_7c4f0 = Some (Branch BC_LTU 20 21 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c4f4 : bv 32 := 0xff8af513.
Lemma F_7c4f4 : fetch_word Asan.M.loaded_segments (0x7c544 : word) = Some W_7c4f4.
Proof. vm_refl. Qed.
Lemma D_7c4f4 : decode_any W_7c4f4 = Some (OpImm ALU_AND 10 21 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c4f8 : bv 32 := 0x0cbaf863.
Lemma F_7c4f8 : fetch_word Asan.M.loaded_segments (0x7c548 : word) = Some W_7c4f8.
Proof. vm_refl. Qed.
Lemma D_7c4f8 : decode_any W_7c4f8 = Some (Branch BC_GEU 21 11 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c4fc : bv 32 := 0xff8af493.
Lemma F_7c4fc : fetch_word Asan.M.loaded_segments (0x7c54c : word) = Some W_7c4fc.
Proof. vm_refl. Qed.
Lemma D_7c4fc : decode_any W_7c4fc = Some (OpImm ALU_AND 9 21 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c500 : bv 32 := 0x007a8613.
Lemma F_7c500 : fetch_word Asan.M.loaded_segments (0x7c550 : word) = Some W_7c500.
Proof. vm_refl. Qed.
Lemma D_7c500 : decode_any W_7c500 = Some (OpImm ALU_ADD 12 21 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c504 : bv 32 := 0xff867913.
Lemma F_7c504 : fetch_word Asan.M.loaded_segments (0x7c554 : word) = Some W_7c504.
Proof. vm_refl. Qed.
Lemma D_7c504 : decode_any W_7c504 = Some (OpImm ALU_AND 18 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c508 : bv 32 := 0x0c957a63.
Lemma F_7c508 : fetch_word Asan.M.loaded_segments (0x7c558 : word) = Some W_7c508.
Proof. vm_refl. Qed.
Lemma D_7c508 : decode_any W_7c508 = Some (Branch BC_GEU 10 9 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c50c : bv 32 := 0x40a485b3.
Lemma F_7c50c : fetch_word Asan.M.loaded_segments (0x7c55c : word) = Some W_7c50c.
Proof. vm_refl. Qed.
Lemma D_7c50c : decode_any W_7c50c = Some (Op ALU_SUB 11 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c510 : bv 32 := 0x00000613.
Lemma F_7c510 : fetch_word Asan.M.loaded_segments (0x7c560 : word) = Some W_7c510.
Proof. vm_refl. Qed.
Lemma D_7c510 : decode_any W_7c510 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c514 : bv 32 := 0x0e00006f.
Lemma F_7c514 : fetch_word Asan.M.loaded_segments (0x7c564 : word) = Some W_7c514.
Proof. vm_refl. Qed.
Lemma D_7c514 : decode_any W_7c514 = Some (Jal 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c518 : bv 32 := 0xfffa5517.
Lemma F_7c518 : fetch_word Asan.M.loaded_segments (0x7c568 : word) = Some W_7c518.
Proof. vm_refl. Qed.
Lemma D_7c518 : decode_any W_7c518 = Some (Auipc 10 1048485, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c51c : bv 32 := 0xfffa6597.
Lemma F_7c51c : fetch_word Asan.M.loaded_segments (0x7c56c : word) = Some W_7c51c.
Proof. vm_refl. Qed.
Lemma D_7c51c : decode_any W_7c51c = Some (Auipc 11 1048486, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c520 : bv 32 := 0xd7150513.
Lemma F_7c520 : fetch_word Asan.M.loaded_segments (0x7c570 : word) = Some W_7c520.
Proof. vm_refl. Qed.
Lemma D_7c520 : decode_any W_7c520 = Some (OpImm ALU_ADD 10 10 3441, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c524 : bv 32 := 0xebc58613.
Lemma F_7c524 : fetch_word Asan.M.loaded_segments (0x7c574 : word) = Some W_7c524.
Proof. vm_refl. Qed.
Lemma D_7c524 : decode_any W_7c524 = Some (OpImm ALU_ADD 12 11 3772, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c528 : bv 32 := 0x1b600593.
Lemma F_7c528 : fetch_word Asan.M.loaded_segments (0x7c578 : word) = Some W_7c528.
Proof. vm_refl. Qed.
Lemma D_7c528 : decode_any W_7c528 = Some (OpImm ALU_ADD 11 0 438, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c52c : bv 32 := 0x58c170ef.
Lemma F_7c52c : fetch_word Asan.M.loaded_segments (0x7c57c : word) = Some W_7c52c.
Proof. vm_refl. Qed.
Lemma D_7c52c : decode_any W_7c52c = Some (Jal 1 95628, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c530 : bv 32 := 0xff8a7a93.
Lemma F_7c530 : fetch_word Asan.M.loaded_segments (0x7c580 : word) = Some W_7c530.
Proof. vm_refl. Qed.
Lemma D_7c530 : decode_any W_7c530 = Some (OpImm ALU_AND 21 20 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c534 : bv 32 := 0x00098593.
Lemma F_7c534 : fetch_word Asan.M.loaded_segments (0x7c584 : word) = Some W_7c534.
Proof. vm_refl. Qed.
Lemma D_7c534 : decode_any W_7c534 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c538 : bv 32 := 0x01396463.
Lemma F_7c538 : fetch_word Asan.M.loaded_segments (0x7c588 : word) = Some W_7c538.
Proof. vm_refl. Qed.
Lemma D_7c538 : decode_any W_7c538 = Some (Branch BC_LTU 18 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c53c : bv 32 := 0x00090593.
Lemma F_7c53c : fetch_word Asan.M.loaded_segments (0x7c58c : word) = Some W_7c53c.
Proof. vm_refl. Qed.
Lemma D_7c53c : decode_any W_7c53c = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c540 : bv 32 := 0xf8bafae3.
Lemma F_7c540 : fetch_word Asan.M.loaded_segments (0x7c590 : word) = Some W_7c540.
Proof. vm_refl. Qed.
Lemma D_7c540 : decode_any W_7c540 = Some (Branch BC_GEU 21 11 8084, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c544 : bv 32 := 0x000bd597.
Lemma F_7c544 : fetch_word Asan.M.loaded_segments (0x7c594 : word) = Some W_7c544.
Proof. vm_refl. Qed.
Lemma D_7c544 : decode_any W_7c544 = Some (Auipc 11 189, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c548 : bv 32 := 0xc245b583.
Lemma F_7c548 : fetch_word Asan.M.loaded_segments (0x7c598 : word) = Some W_7c548.
Proof. vm_refl. Qed.
Lemma D_7c548 : decode_any W_7c548 = Some (Load SZ8 true 11 11 3108, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c54c : bv 32 := 0x0005b583.
Lemma F_7c54c : fetch_word Asan.M.loaded_segments (0x7c59c : word) = Some W_7c54c.
Proof. vm_refl. Qed.
Lemma D_7c54c : decode_any W_7c54c = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c550 : bv 32 := 0x003a5613.
Lemma F_7c550 : fetch_word Asan.M.loaded_segments (0x7c5a0 : word) = Some W_7c550.
Proof. vm_refl. Qed.
Lemma D_7c550 : decode_any W_7c550 = Some (ShiftImm ALU_SRL 12 20 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c554 : bv 32 := 0x00c585b3.
Lemma F_7c554 : fetch_word Asan.M.loaded_segments (0x7c5a4 : word) = Some W_7c554.
Proof. vm_refl. Qed.
Lemma D_7c554 : decode_any W_7c554 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c558 : bv 32 := 0x00058583.
Lemma F_7c558 : fetch_word Asan.M.loaded_segments (0x7c5a8 : word) = Some W_7c558.
Proof. vm_refl. Qed.
Lemma D_7c558 : decode_any W_7c558 = Some (Load SZ1 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c55c : bv 32 := 0x00058463.
Lemma F_7c55c : fetch_word Asan.M.loaded_segments (0x7c5ac : word) = Some W_7c55c.
Proof. vm_refl. Qed.
Lemma D_7c55c : decode_any W_7c55c = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c560 : bv 32 := 0xf6b55ae3.
Lemma F_7c560 : fetch_word Asan.M.loaded_segments (0x7c5b0 : word) = Some W_7c560.
Proof. vm_refl. Qed.
Lemma D_7c560 : decode_any W_7c560 = Some (Branch BC_GE 10 11 8052, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c564 : bv 32 := 0x000a8513.
Lemma F_7c564 : fetch_word Asan.M.loaded_segments (0x7c5b4 : word) = Some W_7c564.
Proof. vm_refl. Qed.
Lemma D_7c564 : decode_any W_7c564 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c568 : bv 32 := 0x0e9aea63.
Lemma F_7c568 : fetch_word Asan.M.loaded_segments (0x7c5b8 : word) = Some W_7c568.
Proof. vm_refl. Qed.
Lemma D_7c568 : decode_any W_7c568 = Some (Branch BC_LTU 21 9 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c56c : bv 32 := 0x00048513.
Lemma F_7c56c : fetch_word Asan.M.loaded_segments (0x7c5bc : word) = Some W_7c56c.
Proof. vm_refl. Qed.
Lemma D_7c56c : decode_any W_7c56c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c570 : bv 32 := 0x000a8a13.
Lemma F_7c570 : fetch_word Asan.M.loaded_segments (0x7c5c0 : word) = Some W_7c570.
Proof. vm_refl. Qed.
Lemma D_7c570 : decode_any W_7c570 = Some (OpImm ALU_ADD 20 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c574 : bv 32 := 0x0f3af863.
Lemma F_7c574 : fetch_word Asan.M.loaded_segments (0x7c5c4 : word) = Some W_7c574.
Proof. vm_refl. Qed.
Lemma D_7c574 : decode_any W_7c574 = Some (Branch BC_GEU 21 19 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c578 : bv 32 := 0xf72ae4e3.
Lemma F_7c578 : fetch_word Asan.M.loaded_segments (0x7c5c8 : word) = Some W_7c578.
Proof. vm_refl. Qed.
Lemma D_7c578 : decode_any W_7c578 = Some (Branch BC_LTU 21 18 8040, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c57c : bv 32 := 0x0f00006f.
Lemma F_7c57c : fetch_word Asan.M.loaded_segments (0x7c5cc : word) = Some W_7c57c.
Proof. vm_refl. Qed.
Lemma D_7c57c : decode_any W_7c57c = Some (Jal 0 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c580 : bv 32 := 0xf74504e3.
Lemma F_7c580 : fetch_word Asan.M.loaded_segments (0x7c5d0 : word) = Some W_7c580.
Proof. vm_refl. Qed.
Lemma D_7c580 : decode_any W_7c580 = Some (Branch BC_EQ 10 20 8040, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c584 : bv 32 := 0xf75512e3.
Lemma F_7c584 : fetch_word Asan.M.loaded_segments (0x7c5d4 : word) = Some W_7c584.
Proof. vm_refl. Qed.
Lemma D_7c584 : decode_any W_7c584 = Some (Branch BC_NE 10 21 8036, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c588 : bv 32 := 0x00748593.
Lemma F_7c588 : fetch_word Asan.M.loaded_segments (0x7c5d8 : word) = Some W_7c588.
Proof. vm_refl. Qed.
Lemma D_7c588 : decode_any W_7c588 = Some (OpImm ALU_ADD 11 9 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c58c : bv 32 := 0xff85f913.
Lemma F_7c58c : fetch_word Asan.M.loaded_segments (0x7c5dc : word) = Some W_7c58c.
Proof. vm_refl. Qed.
Lemma D_7c58c : decode_any W_7c58c = Some (OpImm ALU_AND 18 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c590 : bv 32 := 0xf5257ce3.
Lemma F_7c590 : fetch_word Asan.M.loaded_segments (0x7c5e0 : word) = Some W_7c590.
Proof. vm_refl. Qed.
Lemma D_7c590 : decode_any W_7c590 = Some (Branch BC_GEU 10 18 8024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c594 : bv 32 := 0xff84f513.
Lemma F_7c594 : fetch_word Asan.M.loaded_segments (0x7c5e4 : word) = Some W_7c594.
Proof. vm_refl. Qed.
Lemma D_7c594 : decode_any W_7c594 = Some (OpImm ALU_AND 10 9 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c598 : bv 32 := 0xbd0ff0ef.
Lemma F_7c598 : fetch_word Asan.M.loaded_segments (0x7c5e8 : word) = Some W_7c598.
Proof. vm_refl. Qed.
Lemma D_7c598 : decode_any W_7c598 = Some (Jal 1 2094032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c59c : bv 32 := 0x01350023.
Lemma F_7c59c : fetch_word Asan.M.loaded_segments (0x7c5ec : word) = Some W_7c59c.
Proof. vm_refl. Qed.
Lemma D_7c59c : decode_any W_7c59c = Some (Store SZ1 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c5a0 : bv 32 := 0x00090593.
Lemma F_7c5a0 : fetch_word Asan.M.loaded_segments (0x7c5f0 : word) = Some W_7c5a0.
Proof. vm_refl. Qed.
Lemma D_7c5a0 : decode_any W_7c5a0 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c5a4 : bv 32 := 0x012a6463.
Lemma F_7c5a4 : fetch_word Asan.M.loaded_segments (0x7c5f4 : word) = Some W_7c5a4.
Proof. vm_refl. Qed.
Lemma D_7c5a4 : decode_any W_7c5a4 = Some (Branch BC_LTU 20 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c5a8 : bv 32 := 0x000a0593.
Lemma F_7c5a8 : fetch_word Asan.M.loaded_segments (0x7c5f8 : word) = Some W_7c5a8.
Proof. vm_refl. Qed.
Lemma D_7c5a8 : decode_any W_7c5a8 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c5ac : bv 32 := 0x012ae463.
Lemma F_7c5ac : fetch_word Asan.M.loaded_segments (0x7c5fc : word) = Some W_7c5ac.
Proof. vm_refl. Qed.
Lemma D_7c5ac : decode_any W_7c5ac = Some (Branch BC_LTU 21 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c5b0 : bv 32 := 0x000a8913.
Lemma F_7c5b0 : fetch_word Asan.M.loaded_segments (0x7c600 : word) = Some W_7c5b0.
Proof. vm_refl. Qed.
Lemma D_7c5b0 : decode_any W_7c5b0 = Some (OpImm ALU_ADD 18 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c5b4 : bv 32 := 0x00090a93.
Lemma F_7c5b4 : fetch_word Asan.M.loaded_segments (0x7c604 : word) = Some W_7c5b4.
Proof. vm_refl. Qed.
Lemma D_7c5b4 : decode_any W_7c5b4 = Some (OpImm ALU_ADD 21 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c5b8 : bv 32 := 0x00058513.
Lemma F_7c5b8 : fetch_word Asan.M.loaded_segments (0x7c608 : word) = Some W_7c5b8.
Proof. vm_refl. Qed.
Lemma D_7c5b8 : decode_any W_7c5b8 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c5bc : bv 32 := 0xf325fce3.
Lemma F_7c5bc : fetch_word Asan.M.loaded_segments (0x7c60c : word) = Some W_7c5bc.
Proof. vm_refl. Qed.
Lemma D_7c5bc : decode_any W_7c5bc = Some (Branch BC_GEU 11 18 7992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c5c0 : bv 32 := 0xff857513.
Lemma F_7c5c0 : fetch_word Asan.M.loaded_segments (0x7c610 : word) = Some W_7c5c0.
Proof. vm_refl. Qed.
Lemma D_7c5c0 : decode_any W_7c5c0 = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c5c4 : bv 32 := 0xf2baece3.
Lemma F_7c5c4 : fetch_word Asan.M.loaded_segments (0x7c614 : word) = Some W_7c5c4.
Proof. vm_refl. Qed.
Lemma D_7c5c4 : decode_any W_7c5c4 = Some (Branch BC_LTU 21 11 7992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c5c8 : bv 32 := 0x000a8593.
Lemma F_7c5c8 : fetch_word Asan.M.loaded_segments (0x7c618 : word) = Some W_7c5c8.
Proof. vm_refl. Qed.
Lemma D_7c5c8 : decode_any W_7c5c8 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c5cc : bv 32 := 0xff8af493.
Lemma F_7c5cc : fetch_word Asan.M.loaded_segments (0x7c61c : word) = Some W_7c5cc.
Proof. vm_refl. Qed.
Lemma D_7c5cc : decode_any W_7c5cc = Some (OpImm ALU_AND 9 21 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c5d0 : bv 32 := 0x007a8613.
Lemma F_7c5d0 : fetch_word Asan.M.loaded_segments (0x7c620 : word) = Some W_7c5d0.
Proof. vm_refl. Qed.
Lemma D_7c5d0 : decode_any W_7c5d0 = Some (OpImm ALU_ADD 12 21 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c5d4 : bv 32 := 0xff867913.
Lemma F_7c5d4 : fetch_word Asan.M.loaded_segments (0x7c624 : word) = Some W_7c5d4.
Proof. vm_refl. Qed.
Lemma D_7c5d4 : decode_any W_7c5d4 = Some (OpImm ALU_AND 18 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c5d8 : bv 32 := 0xf2956ae3.
Lemma F_7c5d8 : fetch_word Asan.M.loaded_segments (0x7c628 : word) = Some W_7c5d8.
Proof. vm_refl. Qed.
Lemma D_7c5d8 : decode_any W_7c5d8 = Some (Branch BC_LTU 10 9 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c5dc : bv 32 := 0x00758513.
Lemma F_7c5dc : fetch_word Asan.M.loaded_segments (0x7c62c : word) = Some W_7c5dc.
Proof. vm_refl. Qed.
Lemma D_7c5dc : decode_any W_7c5dc = Some (OpImm ALU_ADD 10 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c5e0 : bv 32 := 0xff857513.
Lemma F_7c5e0 : fetch_word Asan.M.loaded_segments (0x7c630 : word) = Some W_7c5e0.
Proof. vm_refl. Qed.
Lemma D_7c5e0 : decode_any W_7c5e0 = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c5e4 : bv 32 := 0x00a97a63.
Lemma F_7c5e4 : fetch_word Asan.M.loaded_segments (0x7c634 : word) = Some W_7c5e4.
Proof. vm_refl. Qed.
Lemma D_7c5e4 : decode_any W_7c5e4 = Some (Branch BC_GEU 18 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c5e8 : bv 32 := 0x412505b3.
Lemma F_7c5e8 : fetch_word Asan.M.loaded_segments (0x7c638 : word) = Some W_7c5e8.
Proof. vm_refl. Qed.
Lemma D_7c5e8 : decode_any W_7c5e8 = Some (Op ALU_SUB 11 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c5ec : bv 32 := 0x0fc00613.
Lemma F_7c5ec : fetch_word Asan.M.loaded_segments (0x7c63c : word) = Some W_7c5ec.
Proof. vm_refl. Qed.
Lemma D_7c5ec : decode_any W_7c5ec = Some (OpImm ALU_ADD 12 0 252, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c5f0 : bv 32 := 0x00090513.
Lemma F_7c5f0 : fetch_word Asan.M.loaded_segments (0x7c640 : word) = Some W_7c5f0.
Proof. vm_refl. Qed.
Lemma D_7c5f0 : decode_any W_7c5f0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c5f4 : bv 32 := 0xe79fe0ef.
Lemma F_7c5f4 : fetch_word Asan.M.loaded_segments (0x7c644 : word) = Some W_7c5f4.
Proof. vm_refl. Qed.
Lemma D_7c5f4 : decode_any W_7c5f4 = Some (Jal 1 2092664, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c5f8 : bv 32 := 0x02990063.
Lemma F_7c5f8 : fetch_word Asan.M.loaded_segments (0x7c648 : word) = Some W_7c5f8.
Proof. vm_refl. Qed.
Lemma D_7c5f8 : decode_any W_7c5f8 = Some (Branch BC_EQ 18 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c5fc : bv 32 := 0x409906b3.
Lemma F_7c5fc : fetch_word Asan.M.loaded_segments (0x7c64c : word) = Some W_7c5fc.
Proof. vm_refl. Qed.
Lemma D_7c5fc : decode_any W_7c5fc = Some (Op ALU_SUB 13 18 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c600 : bv 32 := 0x00800513.
Lemma F_7c600 : fetch_word Asan.M.loaded_segments (0x7c650 : word) = Some W_7c600.
Proof. vm_refl. Qed.
Lemma D_7c600 : decode_any W_7c600 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c604 : bv 32 := 0x02a69e63.
Lemma F_7c604 : fetch_word Asan.M.loaded_segments (0x7c654 : word) = Some W_7c604.
Proof. vm_refl. Qed.
Lemma D_7c604 : decode_any W_7c604 = Some (Branch BC_NE 13 10 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c608 : bv 32 := 0x007af913.
Lemma F_7c608 : fetch_word Asan.M.loaded_segments (0x7c658 : word) = Some W_7c608.
Proof. vm_refl. Qed.
Lemma D_7c608 : decode_any W_7c608 = Some (OpImm ALU_AND 18 21 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c60c : bv 32 := 0x00048513.
Lemma F_7c60c : fetch_word Asan.M.loaded_segments (0x7c65c : word) = Some W_7c60c.
Proof. vm_refl. Qed.
Lemma D_7c60c : decode_any W_7c60c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c610 : bv 32 := 0xb58ff0ef.
Lemma F_7c610 : fetch_word Asan.M.loaded_segments (0x7c660 : word) = Some W_7c610.
Proof. vm_refl. Qed.
Lemma D_7c610 : decode_any W_7c610 = Some (Jal 1 2093912, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c614 : bv 32 := 0x01250023.
Lemma F_7c614 : fetch_word Asan.M.loaded_segments (0x7c664 : word) = Some W_7c614.
Proof. vm_refl. Qed.
Lemma D_7c614 : decode_any W_7c614 = Some (Store SZ1 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c618 : bv 32 := 0x06010113.
Lemma F_7c618 : fetch_word Asan.M.loaded_segments (0x7c668 : word) = Some W_7c618.
Proof. vm_refl. Qed.
Lemma D_7c618 : decode_any W_7c618 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c61c : bv 32 := 0x7e813083.
Lemma F_7c61c : fetch_word Asan.M.loaded_segments (0x7c66c : word) = Some W_7c61c.
Proof. vm_refl. Qed.
Lemma D_7c61c : decode_any W_7c61c = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c620 : bv 32 := 0x7e013403.
Lemma F_7c620 : fetch_word Asan.M.loaded_segments (0x7c670 : word) = Some W_7c620.
Proof. vm_refl. Qed.
Lemma D_7c620 : decode_any W_7c620 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c624 : bv 32 := 0x7d813483.
Lemma F_7c624 : fetch_word Asan.M.loaded_segments (0x7c674 : word) = Some W_7c624.
Proof. vm_refl. Qed.
Lemma D_7c624 : decode_any W_7c624 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c628 : bv 32 := 0x7d013903.
Lemma F_7c628 : fetch_word Asan.M.loaded_segments (0x7c678 : word) = Some W_7c628.
Proof. vm_refl. Qed.
Lemma D_7c628 : decode_any W_7c628 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c62c : bv 32 := 0x7c813983.
Lemma F_7c62c : fetch_word Asan.M.loaded_segments (0x7c67c : word) = Some W_7c62c.
Proof. vm_refl. Qed.
Lemma D_7c62c : decode_any W_7c62c = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c630 : bv 32 := 0x7c013a03.
Lemma F_7c630 : fetch_word Asan.M.loaded_segments (0x7c680 : word) = Some W_7c630.
Proof. vm_refl. Qed.
Lemma D_7c630 : decode_any W_7c630 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c634 : bv 32 := 0x7b813a83.
Lemma F_7c634 : fetch_word Asan.M.loaded_segments (0x7c684 : word) = Some W_7c634.
Proof. vm_refl. Qed.
Lemma D_7c634 : decode_any W_7c634 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c638 : bv 32 := 0x7f010113.
Lemma F_7c638 : fetch_word Asan.M.loaded_segments (0x7c688 : word) = Some W_7c638.
Proof. vm_refl. Qed.
Lemma D_7c638 : decode_any W_7c638 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c63c : bv 32 := 0x00008067.
Lemma F_7c63c : fetch_word Asan.M.loaded_segments (0x7c68c : word) = Some W_7c63c.
Proof. vm_refl. Qed.
Lemma D_7c63c : decode_any W_7c63c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c640 : bv 32 := 0xfffa5517.
Lemma F_7c640 : fetch_word Asan.M.loaded_segments (0x7c690 : word) = Some W_7c640.
Proof. vm_refl. Qed.
Lemma D_7c640 : decode_any W_7c640 = Some (Auipc 10 1048485, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c644 : bv 32 := 0xfff9c617.
Lemma F_7c644 : fetch_word Asan.M.loaded_segments (0x7c694 : word) = Some W_7c644.
Proof. vm_refl. Qed.
Lemma D_7c644 : decode_any W_7c644 = Some (Auipc 12 1048476, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c648 : bv 32 := 0x1dc00593.
Lemma F_7c648 : fetch_word Asan.M.loaded_segments (0x7c698 : word) = Some W_7c648.
Proof. vm_refl. Qed.
Lemma D_7c648 : decode_any W_7c648 = Some (OpImm ALU_ADD 11 0 476, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c64c : bv 32 := 0xc4950513.
Lemma F_7c64c : fetch_word Asan.M.loaded_segments (0x7c69c : word) = Some W_7c64c.
Proof. vm_refl. Qed.
Lemma D_7c64c : decode_any W_7c64c = Some (OpImm ALU_ADD 10 10 3145, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c650 : bv 32 := 0x2a560613.
Lemma F_7c650 : fetch_word Asan.M.loaded_segments (0x7c6a0 : word) = Some W_7c650.
Proof. vm_refl. Qed.
Lemma D_7c650 : decode_any W_7c650 = Some (OpImm ALU_ADD 12 12 677, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c654 : bv 32 := 0x00800713.
Lemma F_7c654 : fetch_word Asan.M.loaded_segments (0x7c6a4 : word) = Some W_7c654.
Proof. vm_refl. Qed.
Lemma D_7c654 : decode_any W_7c654 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c658 : bv 32 := 0x460170ef.
Lemma F_7c658 : fetch_word Asan.M.loaded_segments (0x7c6a8 : word) = Some W_7c658.
Proof. vm_refl. Qed.
Lemma D_7c658 : decode_any W_7c658 = Some (Jal 1 95328, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c65c : bv 32 := 0x000a8a13.
Lemma F_7c65c : fetch_word Asan.M.loaded_segments (0x7c6ac : word) = Some W_7c65c.
Proof. vm_refl. Qed.
Lemma D_7c65c : decode_any W_7c65c = Some (OpImm ALU_ADD 20 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c660 : bv 32 := 0xf13aece3.
Lemma F_7c660 : fetch_word Asan.M.loaded_segments (0x7c6b0 : word) = Some W_7c660.
Proof. vm_refl. Qed.
Lemma D_7c660 : decode_any W_7c660 = Some (Branch BC_LTU 21 19 7960, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c664 : bv 32 := 0x00098a13.
Lemma F_7c664 : fetch_word Asan.M.loaded_segments (0x7c6b4 : word) = Some W_7c664.
Proof. vm_refl. Qed.
Lemma D_7c664 : decode_any W_7c664 = Some (OpImm ALU_ADD 20 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c668 : bv 32 := 0xe72aece3.
Lemma F_7c668 : fetch_word Asan.M.loaded_segments (0x7c6b8 : word) = Some W_7c668.
Proof. vm_refl. Qed.
Lemma D_7c668 : decode_any W_7c668 = Some (Branch BC_LTU 21 18 7800, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c66c : bv 32 := 0x00090a93.
Lemma F_7c66c : fetch_word Asan.M.loaded_segments (0x7c6bc : word) = Some W_7c66c.
Proof. vm_refl. Qed.
Lemma D_7c66c : decode_any W_7c66c = Some (OpImm ALU_ADD 21 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c670 : bv 32 := 0xe71ff06f.
Lemma F_7c670 : fetch_word Asan.M.loaded_segments (0x7c6c0 : word) = Some W_7c670.
Proof. vm_refl. Qed.
Lemma D_7c670 : decode_any W_7c670 = Some (Jal 0 2096752, 4%Z).
Proof. vm_refl. Qed.

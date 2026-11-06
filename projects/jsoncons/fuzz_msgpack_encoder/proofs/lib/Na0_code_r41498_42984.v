(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
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

Definition W_5d3a0 : bv 32 := 0xfd010113.
Lemma F_5d3a0 : fetch_word Asan.M.loaded_segments (0x5d3f0 : word) = Some W_5d3a0.
Proof. vm_refl. Qed.
Lemma D_5d3a0 : decode_any W_5d3a0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d3a4 : bv 32 := 0x02113423.
Lemma F_5d3a4 : fetch_word Asan.M.loaded_segments (0x5d3f4 : word) = Some W_5d3a4.
Proof. vm_refl. Qed.
Lemma D_5d3a4 : decode_any W_5d3a4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d3a8 : bv 32 := 0x02813023.
Lemma F_5d3a8 : fetch_word Asan.M.loaded_segments (0x5d3f8 : word) = Some W_5d3a8.
Proof. vm_refl. Qed.
Lemma D_5d3a8 : decode_any W_5d3a8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d3ac : bv 32 := 0x00913c23.
Lemma F_5d3ac : fetch_word Asan.M.loaded_segments (0x5d3fc : word) = Some W_5d3ac.
Proof. vm_refl. Qed.
Lemma D_5d3ac : decode_any W_5d3ac = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d3b0 : bv 32 := 0x01213823.
Lemma F_5d3b0 : fetch_word Asan.M.loaded_segments (0x5d400 : word) = Some W_5d3b0.
Proof. vm_refl. Qed.
Lemma D_5d3b0 : decode_any W_5d3b0 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d3b4 : bv 32 := 0x01313423.
Lemma F_5d3b4 : fetch_word Asan.M.loaded_segments (0x5d404 : word) = Some W_5d3b4.
Proof. vm_refl. Qed.
Lemma D_5d3b4 : decode_any W_5d3b4 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d3b8 : bv 32 := 0x01413023.
Lemma F_5d3b8 : fetch_word Asan.M.loaded_segments (0x5d408 : word) = Some W_5d3b8.
Proof. vm_refl. Qed.
Lemma D_5d3b8 : decode_any W_5d3b8 = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d3bc : bv 32 := 0x00058413.
Lemma F_5d3bc : fetch_word Asan.M.loaded_segments (0x5d40c : word) = Some W_5d3bc.
Proof. vm_refl. Qed.
Lemma D_5d3bc : decode_any W_5d3bc = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d3c0 : bv 32 := 0x00058583.
Lemma F_5d3c0 : fetch_word Asan.M.loaded_segments (0x5d410 : word) = Some W_5d3c0.
Proof. vm_refl. Qed.
Lemma D_5d3c0 : decode_any W_5d3c0 = Some (Load SZ1 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d3c4 : bv 32 := 0x00300613.
Lemma F_5d3c4 : fetch_word Asan.M.loaded_segments (0x5d414 : word) = Some W_5d3c4.
Proof. vm_refl. Qed.
Lemma D_5d3c4 : decode_any W_5d3c4 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d3c8 : bv 32 := 0x12c59463.
Lemma F_5d3c8 : fetch_word Asan.M.loaded_segments (0x5d418 : word) = Some W_5d3c8.
Proof. vm_refl. Qed.
Lemma D_5d3c8 : decode_any W_5d3c8 = Some (Branch BC_NE 11 12 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d3cc : bv 32 := 0x00068493.
Lemma F_5d3cc : fetch_word Asan.M.loaded_segments (0x5d41c : word) = Some W_5d3cc.
Proof. vm_refl. Qed.
Lemma D_5d3cc : decode_any W_5d3cc = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d3d0 : bv 32 := 0x00050913.
Lemma F_5d3d0 : fetch_word Asan.M.loaded_segments (0x5d420 : word) = Some W_5d3d0.
Proof. vm_refl. Qed.
Lemma D_5d3d0 : decode_any W_5d3d0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d3d4 : bv 32 := 0x3e82d0ef.
Lemma F_5d3d4 : fetch_word Asan.M.loaded_segments (0x5d424 : word) = Some W_5d3d4.
Proof. vm_refl. Qed.
Lemma D_5d3d4 : decode_any W_5d3d4 = Some (Jal 1 185320, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d3d8 : bv 32 := 0x06050c63.
Lemma F_5d3d8 : fetch_word Asan.M.loaded_segments (0x5d428 : word) = Some W_5d3d8.
Proof. vm_refl. Qed.
Lemma D_5d3d8 : decode_any W_5d3d8 = Some (Branch BC_EQ 10 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d3dc : bv 32 := 0x00053683.
Lemma F_5d3dc : fetch_word Asan.M.loaded_segments (0x5d42c : word) = Some W_5d3dc.
Proof. vm_refl. Qed.
Lemma D_5d3dc : decode_any W_5d3dc = Some (Load SZ8 true 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d3e0 : bv 32 := 0x0004b603.
Lemma F_5d3e0 : fetch_word Asan.M.loaded_segments (0x5d430 : word) = Some W_5d3e0.
Proof. vm_refl. Qed.
Lemma D_5d3e0 : decode_any W_5d3e0 = Some (Load SZ8 true 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d3e4 : bv 32 := 0x0084b583.
Lemma F_5d3e4 : fetch_word Asan.M.loaded_segments (0x5d434 : word) = Some W_5d3e4.
Proof. vm_refl. Qed.
Lemma D_5d3e4 : decode_any W_5d3e4 = Some (Load SZ8 true 11 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d3e8 : bv 32 := 0x0086a983.
Lemma F_5d3e8 : fetch_word Asan.M.loaded_segments (0x5d438 : word) = Some W_5d3e8.
Proof. vm_refl. Qed.
Lemma D_5d3e8 : decode_any W_5d3e8 = Some (Load SZ4 true 19 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d3ec : bv 32 := 0x00050a13.
Lemma F_5d3ec : fetch_word Asan.M.loaded_segments (0x5d43c : word) = Some W_5d3ec.
Proof. vm_refl. Qed.
Lemma D_5d3ec : decode_any W_5d3ec = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d3f0 : bv 32 := 0x00060513.
Lemma F_5d3f0 : fetch_word Asan.M.loaded_segments (0x5d440 : word) = Some W_5d3f0.
Proof. vm_refl. Qed.
Lemma D_5d3f0 : decode_any W_5d3f0 = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d3f4 : bv 32 := 0x2a9430ef.
Lemma F_5d3f4 : fetch_word Asan.M.loaded_segments (0x5d444 : word) = Some W_5d3f4.
Proof. vm_refl. Qed.
Lemma D_5d3f4 : decode_any W_5d3f4 = Some (Jal 1 277160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d3f8 : bv 32 := 0x02099993.
Lemma F_5d3f8 : fetch_word Asan.M.loaded_segments (0x5d448 : word) = Some W_5d3f8.
Proof. vm_refl. Qed.
Lemma D_5d3f8 : decode_any W_5d3f8 = Some (ShiftImm ALU_SLL 19 19 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d3fc : bv 32 := 0x02051513.
Lemma F_5d3fc : fetch_word Asan.M.loaded_segments (0x5d44c : word) = Some W_5d3fc.
Proof. vm_refl. Qed.
Lemma D_5d3fc : decode_any W_5d3fc = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d400 : bv 32 := 0x02055513.
Lemma F_5d400 : fetch_word Asan.M.loaded_segments (0x5d450 : word) = Some W_5d400.
Proof. vm_refl. Qed.
Lemma D_5d400 : decode_any W_5d400 = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d404 : bv 32 := 0x00a9e533.
Lemma F_5d404 : fetch_word Asan.M.loaded_segments (0x5d454 : word) = Some W_5d404.
Proof. vm_refl. Qed.
Lemma D_5d404 : decode_any W_5d404 = Some (Op ALU_OR 10 19 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d408 : bv 32 := 0x00a43823.
Lemma F_5d408 : fetch_word Asan.M.loaded_segments (0x5d458 : word) = Some W_5d408.
Proof. vm_refl. Qed.
Lemma D_5d408 : decode_any W_5d408 = Some (Store SZ8 8 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d40c : bv 32 := 0x050a0593.
Lemma F_5d40c : fetch_word Asan.M.loaded_segments (0x5d45c : word) = Some W_5d40c.
Proof. vm_refl. Qed.
Lemma D_5d40c : decode_any W_5d40c = Some (OpImm ALU_ADD 11 20 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d410 : bv 32 := 0x00245683.
Lemma F_5d410 : fetch_word Asan.M.loaded_segments (0x5d460 : word) = Some W_5d410.
Proof. vm_refl. Qed.
Lemma D_5d410 : decode_any W_5d410 = Some (Load SZ2 false 13 8 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d414 : bv 32 := 0x00446703.
Lemma F_5d414 : fetch_word Asan.M.loaded_segments (0x5d464 : word) = Some W_5d414.
Proof. vm_refl. Qed.
Lemma D_5d414 : decode_any W_5d414 = Some (Load SZ4 false 14 8 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d418 : bv 32 := 0x0d0a0613.
Lemma F_5d418 : fetch_word Asan.M.loaded_segments (0x5d468 : word) = Some W_5d418.
Proof. vm_refl. Qed.
Lemma D_5d418 : decode_any W_5d418 = Some (OpImm ALU_ADD 12 20 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d41c : bv 32 := 0x2d890513.
Lemma F_5d41c : fetch_word Asan.M.loaded_segments (0x5d46c : word) = Some W_5d41c.
Proof. vm_refl. Qed.
Lemma D_5d41c : decode_any W_5d41c = Some (OpImm ALU_ADD 10 18 728, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d420 : bv 32 := 0x02069693.
Lemma F_5d420 : fetch_word Asan.M.loaded_segments (0x5d470 : word) = Some W_5d420.
Proof. vm_refl. Qed.
Lemma D_5d420 : decode_any W_5d420 = Some (ShiftImm ALU_SLL 13 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d424 : bv 32 := 0x00e6e7b3.
Lemma F_5d424 : fetch_word Asan.M.loaded_segments (0x5d474 : word) = Some W_5d424.
Proof. vm_refl. Qed.
Lemma D_5d424 : decode_any W_5d424 = Some (Op ALU_OR 15 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d428 : bv 32 := 0x00048693.
Lemma F_5d428 : fetch_word Asan.M.loaded_segments (0x5d478 : word) = Some W_5d428.
Proof. vm_refl. Qed.
Lemma D_5d428 : decode_any W_5d428 = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d42c : bv 32 := 0x00040713.
Lemma F_5d42c : fetch_word Asan.M.loaded_segments (0x5d47c : word) = Some W_5d42c.
Proof. vm_refl. Qed.
Lemma D_5d42c : decode_any W_5d42c = Some (OpImm ALU_ADD 14 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d430 : bv 32 := 0x02813083.
Lemma F_5d430 : fetch_word Asan.M.loaded_segments (0x5d480 : word) = Some W_5d430.
Proof. vm_refl. Qed.
Lemma D_5d430 : decode_any W_5d430 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d434 : bv 32 := 0x02013403.
Lemma F_5d434 : fetch_word Asan.M.loaded_segments (0x5d484 : word) = Some W_5d434.
Proof. vm_refl. Qed.
Lemma D_5d434 : decode_any W_5d434 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d438 : bv 32 := 0x01813483.
Lemma F_5d438 : fetch_word Asan.M.loaded_segments (0x5d488 : word) = Some W_5d438.
Proof. vm_refl. Qed.
Lemma D_5d438 : decode_any W_5d438 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d43c : bv 32 := 0x01013903.
Lemma F_5d43c : fetch_word Asan.M.loaded_segments (0x5d48c : word) = Some W_5d43c.
Proof. vm_refl. Qed.
Lemma D_5d43c : decode_any W_5d43c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d440 : bv 32 := 0x00813983.
Lemma F_5d440 : fetch_word Asan.M.loaded_segments (0x5d490 : word) = Some W_5d440.
Proof. vm_refl. Qed.
Lemma D_5d440 : decode_any W_5d440 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d444 : bv 32 := 0x00013a03.
Lemma F_5d444 : fetch_word Asan.M.loaded_segments (0x5d494 : word) = Some W_5d444.
Proof. vm_refl. Qed.
Lemma D_5d444 : decode_any W_5d444 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d448 : bv 32 := 0x03010113.
Lemma F_5d448 : fetch_word Asan.M.loaded_segments (0x5d498 : word) = Some W_5d448.
Proof. vm_refl. Qed.
Lemma D_5d448 : decode_any W_5d448 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d44c : bv 32 := 0x0cc0006f.
Lemma F_5d44c : fetch_word Asan.M.loaded_segments (0x5d49c : word) = Some W_5d44c.
Proof. vm_refl. Qed.
Lemma D_5d44c : decode_any W_5d44c = Some (Jal 0 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d518 : bv 32 := 0xfb010113.
Lemma F_5d518 : fetch_word Asan.M.loaded_segments (0x5d568 : word) = Some W_5d518.
Proof. vm_refl. Qed.
Lemma D_5d518 : decode_any W_5d518 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d51c : bv 32 := 0x04113423.
Lemma F_5d51c : fetch_word Asan.M.loaded_segments (0x5d56c : word) = Some W_5d51c.
Proof. vm_refl. Qed.
Lemma D_5d51c : decode_any W_5d51c = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d520 : bv 32 := 0x04813023.
Lemma F_5d520 : fetch_word Asan.M.loaded_segments (0x5d570 : word) = Some W_5d520.
Proof. vm_refl. Qed.
Lemma D_5d520 : decode_any W_5d520 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d524 : bv 32 := 0x02913c23.
Lemma F_5d524 : fetch_word Asan.M.loaded_segments (0x5d574 : word) = Some W_5d524.
Proof. vm_refl. Qed.
Lemma D_5d524 : decode_any W_5d524 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d528 : bv 32 := 0x03213823.
Lemma F_5d528 : fetch_word Asan.M.loaded_segments (0x5d578 : word) = Some W_5d528.
Proof. vm_refl. Qed.
Lemma D_5d528 : decode_any W_5d528 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d52c : bv 32 := 0x03313423.
Lemma F_5d52c : fetch_word Asan.M.loaded_segments (0x5d57c : word) = Some W_5d52c.
Proof. vm_refl. Qed.
Lemma D_5d52c : decode_any W_5d52c = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d530 : bv 32 := 0x03413023.
Lemma F_5d530 : fetch_word Asan.M.loaded_segments (0x5d580 : word) = Some W_5d530.
Proof. vm_refl. Qed.
Lemma D_5d530 : decode_any W_5d530 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d534 : bv 32 := 0x01513c23.
Lemma F_5d534 : fetch_word Asan.M.loaded_segments (0x5d584 : word) = Some W_5d534.
Proof. vm_refl. Qed.
Lemma D_5d534 : decode_any W_5d534 = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d538 : bv 32 := 0x01613823.
Lemma F_5d538 : fetch_word Asan.M.loaded_segments (0x5d588 : word) = Some W_5d538.
Proof. vm_refl. Qed.
Lemma D_5d538 : decode_any W_5d538 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d53c : bv 32 := 0x00050413.
Lemma F_5d53c : fetch_word Asan.M.loaded_segments (0x5d58c : word) = Some W_5d53c.
Proof. vm_refl. Qed.
Lemma D_5d53c : decode_any W_5d53c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d540 : bv 32 := 0x00c13023.
Lemma F_5d540 : fetch_word Asan.M.loaded_segments (0x5d590 : word) = Some W_5d540.
Proof. vm_refl. Qed.
Lemma D_5d540 : decode_any W_5d540 = Some (Store SZ8 2 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d544 : bv 32 := 0x00d13423.
Lemma F_5d544 : fetch_word Asan.M.loaded_segments (0x5d594 : word) = Some W_5d544.
Proof. vm_refl. Qed.
Lemma D_5d544 : decode_any W_5d544 = Some (Store SZ8 2 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d548 : bv 32 := 0x05053b03.
Lemma F_5d548 : fetch_word Asan.M.loaded_segments (0x5d598 : word) = Some W_5d548.
Proof. vm_refl. Qed.
Lemma D_5d548 : decode_any W_5d548 = Some (Load SZ8 true 22 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d54c : bv 32 := 0x00058493.
Lemma F_5d54c : fetch_word Asan.M.loaded_segments (0x5d59c : word) = Some W_5d54c.
Proof. vm_refl. Qed.
Lemma D_5d54c : decode_any W_5d54c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d550 : bv 32 := 0x000b0663.
Lemma F_5d550 : fetch_word Asan.M.loaded_segments (0x5d5a0 : word) = Some W_5d550.
Proof. vm_refl. Qed.
Lemma D_5d550 : decode_any W_5d550 = Some (Branch BC_EQ 22 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d554 : bv 32 := 0x04043503.
Lemma F_5d554 : fetch_word Asan.M.loaded_segments (0x5d5a4 : word) = Some W_5d554.
Proof. vm_refl. Qed.
Lemma D_5d554 : decode_any W_5d554 = Some (Load SZ8 true 10 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d558 : bv 32 := 0x0cf57263.
Lemma F_5d558 : fetch_word Asan.M.loaded_segments (0x5d5a8 : word) = Some W_5d558.
Proof. vm_refl. Qed.
Lemma D_5d558 : decode_any W_5d558 = Some (Branch BC_GEU 10 15 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5e0 : bv 32 := 0x00013603.
Lemma F_5d5e0 : fetch_word Asan.M.loaded_segments (0x5d630 : word) = Some W_5d5e0.
Proof. vm_refl. Qed.
Lemma D_5d5e0 : decode_any W_5d5e0 = Some (Load SZ8 true 12 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5e4 : bv 32 := 0x00813683.
Lemma F_5d5e4 : fetch_word Asan.M.loaded_segments (0x5d634 : word) = Some W_5d5e4.
Proof. vm_refl. Qed.
Lemma D_5d5e4 : decode_any W_5d5e4 = Some (Load SZ8 true 13 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5e8 : bv 32 := 0x00040513.
Lemma F_5d5e8 : fetch_word Asan.M.loaded_segments (0x5d638 : word) = Some W_5d5e8.
Proof. vm_refl. Qed.
Lemma D_5d5e8 : decode_any W_5d5e8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5ec : bv 32 := 0x00048593.
Lemma F_5d5ec : fetch_word Asan.M.loaded_segments (0x5d63c : word) = Some W_5d5ec.
Proof. vm_refl. Qed.
Lemma D_5d5ec : decode_any W_5d5ec = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5f0 : bv 32 := 0x831fd0ef.
Lemma F_5d5f0 : fetch_word Asan.M.loaded_segments (0x5d640 : word) = Some W_5d5f0.
Proof. vm_refl. Qed.
Lemma D_5d5f0 : decode_any W_5d5f0 = Some (Jal 1 2086960, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5f4 : bv 32 := 0x04813083.
Lemma F_5d5f4 : fetch_word Asan.M.loaded_segments (0x5d644 : word) = Some W_5d5f4.
Proof. vm_refl. Qed.
Lemma D_5d5f4 : decode_any W_5d5f4 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5f8 : bv 32 := 0x04013403.
Lemma F_5d5f8 : fetch_word Asan.M.loaded_segments (0x5d648 : word) = Some W_5d5f8.
Proof. vm_refl. Qed.
Lemma D_5d5f8 : decode_any W_5d5f8 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d5fc : bv 32 := 0x03813483.
Lemma F_5d5fc : fetch_word Asan.M.loaded_segments (0x5d64c : word) = Some W_5d5fc.
Proof. vm_refl. Qed.
Lemma D_5d5fc : decode_any W_5d5fc = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d600 : bv 32 := 0x03013903.
Lemma F_5d600 : fetch_word Asan.M.loaded_segments (0x5d650 : word) = Some W_5d600.
Proof. vm_refl. Qed.
Lemma D_5d600 : decode_any W_5d600 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d604 : bv 32 := 0x02813983.
Lemma F_5d604 : fetch_word Asan.M.loaded_segments (0x5d654 : word) = Some W_5d604.
Proof. vm_refl. Qed.
Lemma D_5d604 : decode_any W_5d604 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d608 : bv 32 := 0x02013a03.
Lemma F_5d608 : fetch_word Asan.M.loaded_segments (0x5d658 : word) = Some W_5d608.
Proof. vm_refl. Qed.
Lemma D_5d608 : decode_any W_5d608 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d60c : bv 32 := 0x01813a83.
Lemma F_5d60c : fetch_word Asan.M.loaded_segments (0x5d65c : word) = Some W_5d60c.
Proof. vm_refl. Qed.
Lemma D_5d60c : decode_any W_5d60c = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d610 : bv 32 := 0x01013b03.
Lemma F_5d610 : fetch_word Asan.M.loaded_segments (0x5d660 : word) = Some W_5d610.
Proof. vm_refl. Qed.
Lemma D_5d610 : decode_any W_5d610 = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d614 : bv 32 := 0x05010113.
Lemma F_5d614 : fetch_word Asan.M.loaded_segments (0x5d664 : word) = Some W_5d614.
Proof. vm_refl. Qed.
Lemma D_5d614 : decode_any W_5d614 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d618 : bv 32 := 0x00008067.
Lemma F_5d618 : fetch_word Asan.M.loaded_segments (0x5d668 : word) = Some W_5d618.
Proof. vm_refl. Qed.
Lemma D_5d618 : decode_any W_5d618 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d61c : bv 32 := 0x00060a13.
Lemma F_5d61c : fetch_word Asan.M.loaded_segments (0x5d66c : word) = Some W_5d61c.
Proof. vm_refl. Qed.
Lemma D_5d61c : decode_any W_5d61c = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d620 : bv 32 := 0x00068993.
Lemma F_5d620 : fetch_word Asan.M.loaded_segments (0x5d670 : word) = Some W_5d620.
Proof. vm_refl. Qed.
Lemma D_5d620 : decode_any W_5d620 = Some (OpImm ALU_ADD 19 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d624 : bv 32 := 0x00078913.
Lemma F_5d624 : fetch_word Asan.M.loaded_segments (0x5d674 : word) = Some W_5d624.
Proof. vm_refl. Qed.
Lemma D_5d624 : decode_any W_5d624 = Some (OpImm ALU_ADD 18 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d628 : bv 32 := 0x000f9517.
Lemma F_5d628 : fetch_word Asan.M.loaded_segments (0x5d678 : word) = Some W_5d628.
Proof. vm_refl. Qed.
Lemma D_5d628 : decode_any W_5d628 = Some (Auipc 10 249, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d62c : bv 32 := 0x71853583.
Lemma F_5d62c : fetch_word Asan.M.loaded_segments (0x5d67c : word) = Some W_5d62c.
Proof. vm_refl. Qed.
Lemma D_5d62c : decode_any W_5d62c = Some (Load SZ8 true 11 10 1816, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d630 : bv 32 := 0x0305a683.
Lemma F_5d630 : fetch_word Asan.M.loaded_segments (0x5d680 : word) = Some W_5d630.
Proof. vm_refl. Qed.
Lemma D_5d630 : decode_any W_5d630 = Some (Load SZ4 true 13 11 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d634 : bv 32 := 0x04d05463.
Lemma F_5d634 : fetch_word Asan.M.loaded_segments (0x5d684 : word) = Some W_5d634.
Proof. vm_refl. Qed.
Lemma D_5d634 : decode_any W_5d634 = Some (Branch BC_GE 0 13 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d67c : bv 32 := 0x00275583.
Lemma F_5d67c : fetch_word Asan.M.loaded_segments (0x5d6cc : word) = Some W_5d67c.
Proof. vm_refl. Qed.
Lemma D_5d67c : decode_any W_5d67c = Some (Load SZ2 false 11 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d680 : bv 32 := 0x00476603.
Lemma F_5d680 : fetch_word Asan.M.loaded_segments (0x5d6d0 : word) = Some W_5d680.
Proof. vm_refl. Qed.
Lemma D_5d680 : decode_any W_5d680 = Some (Load SZ4 false 12 14 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d684 : bv 32 := 0x01070513.
Lemma F_5d684 : fetch_word Asan.M.loaded_segments (0x5d6d4 : word) = Some W_5d684.
Proof. vm_refl. Qed.
Lemma D_5d684 : decode_any W_5d684 = Some (OpImm ALU_ADD 10 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d688 : bv 32 := 0x02059593.
Lemma F_5d688 : fetch_word Asan.M.loaded_segments (0x5d6d8 : word) = Some W_5d688.
Proof. vm_refl. Qed.
Lemma D_5d688 : decode_any W_5d688 = Some (ShiftImm ALU_SLL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d68c : bv 32 := 0x00c5e5b3.
Lemma F_5d68c : fetch_word Asan.M.loaded_segments (0x5d6dc : word) = Some W_5d68c.
Proof. vm_refl. Qed.
Lemma D_5d68c : decode_any W_5d68c = Some (Op ALU_OR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d690 : bv 32 := 0x00758593.
Lemma F_5d690 : fetch_word Asan.M.loaded_segments (0x5d6e0 : word) = Some W_5d690.
Proof. vm_refl. Qed.
Lemma D_5d690 : decode_any W_5d690 = Some (OpImm ALU_ADD 11 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d694 : bv 32 := 0xff85f593.
Lemma F_5d694 : fetch_word Asan.M.loaded_segments (0x5d6e4 : word) = Some W_5d694.
Proof. vm_refl. Qed.
Lemma D_5d694 : decode_any W_5d694 = Some (OpImm ALU_AND 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d698 : bv 32 := 0x0fd00613.
Lemma F_5d698 : fetch_word Asan.M.loaded_segments (0x5d6e8 : word) = Some W_5d698.
Proof. vm_refl. Qed.
Lemma D_5d698 : decode_any W_5d698 = Some (OpImm ALU_ADD 12 0 253, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d69c : bv 32 := 0x00070a93.
Lemma F_5d69c : fetch_word Asan.M.loaded_segments (0x5d6ec : word) = Some W_5d69c.
Proof. vm_refl. Qed.
Lemma D_5d69c : decode_any W_5d69c = Some (OpImm ALU_ADD 21 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6a0 : bv 32 := 0x370240ef.
Lemma F_5d6a0 : fetch_word Asan.M.loaded_segments (0x5d6f0 : word) = Some W_5d6a0.
Proof. vm_refl. Qed.
Lemma D_5d6a0 : decode_any W_5d6a0 = Some (Jal 1 148336, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6a4 : bv 32 := 0x00048513.
Lemma F_5d6a4 : fetch_word Asan.M.loaded_segments (0x5d6f4 : word) = Some W_5d6a4.
Proof. vm_refl. Qed.
Lemma D_5d6a4 : decode_any W_5d6a4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6a8 : bv 32 := 0x000a0593.
Lemma F_5d6a8 : fetch_word Asan.M.loaded_segments (0x5d6f8 : word) = Some W_5d6a8.
Proof. vm_refl. Qed.
Lemma D_5d6a8 : decode_any W_5d6a8 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6ac : bv 32 := 0x00098613.
Lemma F_5d6ac : fetch_word Asan.M.loaded_segments (0x5d6fc : word) = Some W_5d6ac.
Proof. vm_refl. Qed.
Lemma D_5d6ac : decode_any W_5d6ac = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6b0 : bv 32 := 0x000a8693.
Lemma F_5d6b0 : fetch_word Asan.M.loaded_segments (0x5d700 : word) = Some W_5d6b0.
Proof. vm_refl. Qed.
Lemma D_5d6b0 : decode_any W_5d6b0 = Some (OpImm ALU_ADD 13 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6b4 : bv 32 := 0x00090713.
Lemma F_5d6b4 : fetch_word Asan.M.loaded_segments (0x5d704 : word) = Some W_5d6b4.
Proof. vm_refl. Qed.
Lemma D_5d6b4 : decode_any W_5d6b4 = Some (OpImm ALU_ADD 14 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6b8 : bv 32 := 0x010000ef.
Lemma F_5d6b8 : fetch_word Asan.M.loaded_segments (0x5d708 : word) = Some W_5d6b8.
Proof. vm_refl. Qed.
Lemma D_5d6b8 : decode_any W_5d6b8 = Some (Jal 1 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6bc : bv 32 := 0x0184b503.
Lemma F_5d6bc : fetch_word Asan.M.loaded_segments (0x5d70c : word) = Some W_5d6bc.
Proof. vm_refl. Qed.
Lemma D_5d6bc : decode_any W_5d6bc = Some (Load SZ8 true 10 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6c0 : bv 32 := 0xf2ab60e3.
Lemma F_5d6c0 : fetch_word Asan.M.loaded_segments (0x5d710 : word) = Some W_5d6c0.
Proof. vm_refl. Qed.
Lemma D_5d6c0 : decode_any W_5d6c0 = Some (Branch BC_LTU 22 10 7968, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6c4 : bv 32 := 0xf31ff06f.
Lemma F_5d6c4 : fetch_word Asan.M.loaded_segments (0x5d714 : word) = Some W_5d6c4.
Proof. vm_refl. Qed.
Lemma D_5d6c4 : decode_any W_5d6c4 = Some (Jal 0 2096944, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6c8 : bv 32 := 0xfc010113.
Lemma F_5d6c8 : fetch_word Asan.M.loaded_segments (0x5d718 : word) = Some W_5d6c8.
Proof. vm_refl. Qed.
Lemma D_5d6c8 : decode_any W_5d6c8 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6cc : bv 32 := 0x02113c23.
Lemma F_5d6cc : fetch_word Asan.M.loaded_segments (0x5d71c : word) = Some W_5d6cc.
Proof. vm_refl. Qed.
Lemma D_5d6cc : decode_any W_5d6cc = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6d0 : bv 32 := 0x02813823.
Lemma F_5d6d0 : fetch_word Asan.M.loaded_segments (0x5d720 : word) = Some W_5d6d0.
Proof. vm_refl. Qed.
Lemma D_5d6d0 : decode_any W_5d6d0 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6d4 : bv 32 := 0x02913423.
Lemma F_5d6d4 : fetch_word Asan.M.loaded_segments (0x5d724 : word) = Some W_5d6d4.
Proof. vm_refl. Qed.
Lemma D_5d6d4 : decode_any W_5d6d4 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6d8 : bv 32 := 0x03213023.
Lemma F_5d6d8 : fetch_word Asan.M.loaded_segments (0x5d728 : word) = Some W_5d6d8.
Proof. vm_refl. Qed.
Lemma D_5d6d8 : decode_any W_5d6d8 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6dc : bv 32 := 0x01313c23.
Lemma F_5d6dc : fetch_word Asan.M.loaded_segments (0x5d72c : word) = Some W_5d6dc.
Proof. vm_refl. Qed.
Lemma D_5d6dc : decode_any W_5d6dc = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6e0 : bv 32 := 0x01413823.
Lemma F_5d6e0 : fetch_word Asan.M.loaded_segments (0x5d730 : word) = Some W_5d6e0.
Proof. vm_refl. Qed.
Lemma D_5d6e0 : decode_any W_5d6e0 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6e4 : bv 32 := 0x01513423.
Lemma F_5d6e4 : fetch_word Asan.M.loaded_segments (0x5d734 : word) = Some W_5d6e4.
Proof. vm_refl. Qed.
Lemma D_5d6e4 : decode_any W_5d6e4 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6e8 : bv 32 := 0x00053783.
Lemma F_5d6e8 : fetch_word Asan.M.loaded_segments (0x5d738 : word) = Some W_5d6e8.
Proof. vm_refl. Qed.
Lemma D_5d6e8 : decode_any W_5d6e8 = Some (Load SZ8 true 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6ec : bv 32 := 0x00078a63.
Lemma F_5d6ec : fetch_word Asan.M.loaded_segments (0x5d73c : word) = Some W_5d6ec.
Proof. vm_refl. Qed.
Lemma D_5d6ec : decode_any W_5d6ec = Some (Branch BC_EQ 15 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6f0 : bv 32 := 0x01053803.
Lemma F_5d6f0 : fetch_word Asan.M.loaded_segments (0x5d740 : word) = Some W_5d6f0.
Proof. vm_refl. Qed.
Lemma D_5d6f0 : decode_any W_5d6f0 = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6f4 : bv 32 := 0x01083783.
Lemma F_5d6f4 : fetch_word Asan.M.loaded_segments (0x5d744 : word) = Some W_5d6f4.
Proof. vm_refl. Qed.
Lemma D_5d6f4 : decode_any W_5d6f4 = Some (Load SZ8 true 15 16 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6f8 : bv 32 := 0x3fd00893.
Lemma F_5d6f8 : fetch_word Asan.M.loaded_segments (0x5d748 : word) = Some W_5d6f8.
Proof. vm_refl. Qed.
Lemma D_5d6f8 : decode_any W_5d6f8 = Some (OpImm ALU_ADD 17 0 1021, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d6fc : bv 32 := 0x09179463.
Lemma F_5d6fc : fetch_word Asan.M.loaded_segments (0x5d74c : word) = Some W_5d6fc.
Proof. vm_refl. Qed.
Lemma D_5d6fc : decode_any W_5d6fc = Some (Branch BC_NE 15 17 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d700 : bv 32 := 0x7805a783.
Lemma F_5d700 : fetch_word Asan.M.loaded_segments (0x5d750 : word) = Some W_5d700.
Proof. vm_refl. Qed.
Lemma D_5d700 : decode_any W_5d700 = Some (Load SZ4 true 15 11 1920, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d704 : bv 32 := 0x0e078263.
Lemma F_5d704 : fetch_word Asan.M.loaded_segments (0x5d754 : word) = Some W_5d704.
Proof. vm_refl. Qed.
Lemma D_5d704 : decode_any W_5d704 = Some (Branch BC_EQ 15 0 228, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d708 : bv 32 := 0xfff78793.
Lemma F_5d708 : fetch_word Asan.M.loaded_segments (0x5d758 : word) = Some W_5d708.
Proof. vm_refl. Qed.
Lemma D_5d708 : decode_any W_5d708 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d70c : bv 32 := 0x02079813.
Lemma F_5d70c : fetch_word Asan.M.loaded_segments (0x5d75c : word) = Some W_5d70c.
Proof. vm_refl. Qed.
Lemma D_5d70c : decode_any W_5d70c = Some (ShiftImm ALU_SLL 16 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d710 : bv 32 := 0x78f5a023.
Lemma F_5d710 : fetch_word Asan.M.loaded_segments (0x5d760 : word) = Some W_5d710.
Proof. vm_refl. Qed.
Lemma D_5d710 : decode_any W_5d710 = Some (Store SZ4 11 15 1920, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d714 : bv 32 := 0x01e85793.
Lemma F_5d714 : fetch_word Asan.M.loaded_segments (0x5d764 : word) = Some W_5d714.
Proof. vm_refl. Qed.
Lemma D_5d714 : decode_any W_5d714 = Some (ShiftImm ALU_SRL 15 16 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d718 : bv 32 := 0x00f587b3.
Lemma F_5d718 : fetch_word Asan.M.loaded_segments (0x5d768 : word) = Some W_5d718.
Proof. vm_refl. Qed.
Lemma D_5d718 : decode_any W_5d718 = Some (Op ALU_ADD 15 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d71c : bv 32 := 0x7885b803.
Lemma F_5d71c : fetch_word Asan.M.loaded_segments (0x5d76c : word) = Some W_5d71c.
Proof. vm_refl. Qed.
Lemma D_5d71c : decode_any W_5d71c = Some (Load SZ8 true 16 11 1928, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d720 : bv 32 := 0x7ff58593.
Lemma F_5d720 : fetch_word Asan.M.loaded_segments (0x5d770 : word) = Some W_5d720.
Proof. vm_refl. Qed.
Lemma D_5d720 : decode_any W_5d720 = Some (OpImm ALU_ADD 11 11 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d724 : bv 32 := 0x21158593.
Lemma F_5d724 : fetch_word Asan.M.loaded_segments (0x5d774 : word) = Some W_5d724.
Proof. vm_refl. Qed.
Lemma D_5d724 : decode_any W_5d724 = Some (OpImm ALU_ADD 11 11 529, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d728 : bv 32 := 0x7907e783.
Lemma F_5d728 : fetch_word Asan.M.loaded_segments (0x5d778 : word) = Some W_5d728.
Proof. vm_refl. Qed.
Lemma D_5d728 : decode_any W_5d728 = Some (Load SZ4 false 15 15 1936, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d72c : bv 32 := 0x0105b02f.
Lemma F_5d72c : fetch_word Asan.M.loaded_segments (0x5d77c : word) = Some W_5d72c.
Proof. vm_refl. Qed.
Lemma D_5d72c : decode_any W_5d72c = Some (Amo AMO_ADD AD false false 0 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d730 : bv 32 := 0x000ff597.
Lemma F_5d730 : fetch_word Asan.M.loaded_segments (0x5d780 : word) = Some W_5d730.
Proof. vm_refl. Qed.
Lemma D_5d730 : decode_any W_5d730 = Some (Auipc 11 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d734 : bv 32 := 0xcb85b583.
Lemma F_5d734 : fetch_word Asan.M.loaded_segments (0x5d784 : word) = Some W_5d734.
Proof. vm_refl. Qed.
Lemma D_5d734 : decode_any W_5d734 = Some (Load SZ8 true 11 11 3256, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d738 : bv 32 := 0x00300813.
Lemma F_5d738 : fetch_word Asan.M.loaded_segments (0x5d788 : word) = Some W_5d738.
Proof. vm_refl. Qed.
Lemma D_5d738 : decode_any W_5d738 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d73c : bv 32 := 0x00479793.
Lemma F_5d73c : fetch_word Asan.M.loaded_segments (0x5d78c : word) = Some W_5d73c.
Proof. vm_refl. Qed.
Lemma D_5d73c : decode_any W_5d73c = Some (ShiftImm ALU_SLL 15 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d740 : bv 32 := 0x02381813.
Lemma F_5d740 : fetch_word Asan.M.loaded_segments (0x5d790 : word) = Some W_5d740.
Proof. vm_refl. Qed.
Lemma D_5d740 : decode_any W_5d740 = Some (ShiftImm ALU_SLL 16 16 35, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d744 : bv 32 := 0x010585b3.
Lemma F_5d744 : fetch_word Asan.M.loaded_segments (0x5d794 : word) = Some W_5d744.
Proof. vm_refl. Qed.
Lemma D_5d744 : decode_any W_5d744 = Some (Op ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d748 : bv 32 := 0x00b785b3.
Lemma F_5d748 : fetch_word Asan.M.loaded_segments (0x5d798 : word) = Some W_5d748.
Proof. vm_refl. Qed.
Lemma D_5d748 : decode_any W_5d748 = Some (Op ALU_ADD 11 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d74c : bv 32 := 0x0e058863.
Lemma F_5d74c : fetch_word Asan.M.loaded_segments (0x5d79c : word) = Some W_5d74c.
Proof. vm_refl. Qed.
Lemma D_5d74c : decode_any W_5d74c = Some (Branch BC_EQ 11 0 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d750 : bv 32 := 0x00100613.
Lemma F_5d750 : fetch_word Asan.M.loaded_segments (0x5d7a0 : word) = Some W_5d750.
Proof. vm_refl. Qed.
Lemma D_5d750 : decode_any W_5d750 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d754 : bv 32 := 0x000027b7.
Lemma F_5d754 : fetch_word Asan.M.loaded_segments (0x5d7a4 : word) = Some W_5d754.
Proof. vm_refl. Qed.
Lemma D_5d754 : decode_any W_5d754 = Some (Lui 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d758 : bv 32 := 0x00f70733.
Lemma F_5d758 : fetch_word Asan.M.loaded_segments (0x5d7a8 : word) = Some W_5d758.
Proof. vm_refl. Qed.
Lemma D_5d758 : decode_any W_5d758 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d75c : bv 32 := 0x00053783.
Lemma F_5d75c : fetch_word Asan.M.loaded_segments (0x5d7ac : word) = Some W_5d75c.
Proof. vm_refl. Qed.
Lemma D_5d75c : decode_any W_5d75c = Some (Load SZ8 true 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d760 : bv 32 := 0x0005b023.
Lemma F_5d760 : fetch_word Asan.M.loaded_segments (0x5d7b0 : word) = Some W_5d760.
Proof. vm_refl. Qed.
Lemma D_5d760 : decode_any W_5d760 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d764 : bv 32 := 0x00e5b423.
Lemma F_5d764 : fetch_word Asan.M.loaded_segments (0x5d7b4 : word) = Some W_5d764.
Proof. vm_refl. Qed.
Lemma D_5d764 : decode_any W_5d764 = Some (Store SZ8 11 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d768 : bv 32 := 0x00c5b823.
Lemma F_5d768 : fetch_word Asan.M.loaded_segments (0x5d7b8 : word) = Some W_5d768.
Proof. vm_refl. Qed.
Lemma D_5d768 : decode_any W_5d768 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d76c : bv 32 := 0x00d5bc23.
Lemma F_5d76c : fetch_word Asan.M.loaded_segments (0x5d7bc : word) = Some W_5d76c.
Proof. vm_refl. Qed.
Lemma D_5d76c : decode_any W_5d76c = Some (Store SZ8 11 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d770 : bv 32 := 0x02078e63.
Lemma F_5d770 : fetch_word Asan.M.loaded_segments (0x5d7c0 : word) = Some W_5d770.
Proof. vm_refl. Qed.
Lemma D_5d770 : decode_any W_5d770 = Some (Branch BC_EQ 15 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d774 : bv 32 := 0x01053603.
Lemma F_5d774 : fetch_word Asan.M.loaded_segments (0x5d7c4 : word) = Some W_5d774.
Proof. vm_refl. Qed.
Lemma D_5d774 : decode_any W_5d774 = Some (Load SZ8 true 12 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d778 : bv 32 := 0x00b63023.
Lemma F_5d778 : fetch_word Asan.M.loaded_segments (0x5d7c8 : word) = Some W_5d778.
Proof. vm_refl. Qed.
Lemma D_5d778 : decode_any W_5d778 = Some (Store SZ8 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d77c : bv 32 := 0x00178613.
Lemma F_5d77c : fetch_word Asan.M.loaded_segments (0x5d7cc : word) = Some W_5d77c.
Proof. vm_refl. Qed.
Lemma D_5d77c : decode_any W_5d77c = Some (OpImm ALU_ADD 12 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d780 : bv 32 := 0x0300006f.
Lemma F_5d780 : fetch_word Asan.M.loaded_segments (0x5d7d0 : word) = Some W_5d780.
Proof. vm_refl. Qed.
Lemma D_5d780 : decode_any W_5d780 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d784 : bv 32 := 0x0d17fc63.
Lemma F_5d784 : fetch_word Asan.M.loaded_segments (0x5d7d4 : word) = Some W_5d784.
Proof. vm_refl. Qed.
Lemma D_5d784 : decode_any W_5d784 = Some (Branch BC_GEU 15 17 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d788 : bv 32 := 0x00883583.
Lemma F_5d788 : fetch_word Asan.M.loaded_segments (0x5d7d8 : word) = Some W_5d788.
Proof. vm_refl. Qed.
Lemma D_5d788 : decode_any W_5d788 = Some (Load SZ8 true 11 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d78c : bv 32 := 0x00379613.
Lemma F_5d78c : fetch_word Asan.M.loaded_segments (0x5d7dc : word) = Some W_5d78c.
Proof. vm_refl. Qed.
Lemma D_5d78c : decode_any W_5d78c = Some (ShiftImm ALU_SLL 12 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d790 : bv 32 := 0x00178793.
Lemma F_5d790 : fetch_word Asan.M.loaded_segments (0x5d7e0 : word) = Some W_5d790.
Proof. vm_refl. Qed.
Lemma D_5d790 : decode_any W_5d790 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d794 : bv 32 := 0x00c80633.
Lemma F_5d794 : fetch_word Asan.M.loaded_segments (0x5d7e4 : word) = Some W_5d794.
Proof. vm_refl. Qed.
Lemma D_5d794 : decode_any W_5d794 = Some (Op ALU_ADD 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d798 : bv 32 := 0x00e585b3.
Lemma F_5d798 : fetch_word Asan.M.loaded_segments (0x5d7e8 : word) = Some W_5d798.
Proof. vm_refl. Qed.
Lemma D_5d798 : decode_any W_5d798 = Some (Op ALU_ADD 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d79c : bv 32 := 0x00b83423.
Lemma F_5d79c : fetch_word Asan.M.loaded_segments (0x5d7ec : word) = Some W_5d79c.
Proof. vm_refl. Qed.
Lemma D_5d79c : decode_any W_5d79c = Some (Store SZ8 16 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7a0 : bv 32 := 0x00f83823.
Lemma F_5d7a0 : fetch_word Asan.M.loaded_segments (0x5d7f0 : word) = Some W_5d7a0.
Proof. vm_refl. Qed.
Lemma D_5d7a0 : decode_any W_5d7a0 = Some (Store SZ8 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7a4 : bv 32 := 0x00d63c23.
Lemma F_5d7a4 : fetch_word Asan.M.loaded_segments (0x5d7f4 : word) = Some W_5d7a4.
Proof. vm_refl. Qed.
Lemma D_5d7a4 : decode_any W_5d7a4 = Some (Store SZ8 12 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7a8 : bv 32 := 0x0100006f.
Lemma F_5d7a8 : fetch_word Asan.M.loaded_segments (0x5d7f8 : word) = Some W_5d7a8.
Proof. vm_refl. Qed.
Lemma D_5d7a8 : decode_any W_5d7a8 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7ac : bv 32 := 0x00b53423.
Lemma F_5d7ac : fetch_word Asan.M.loaded_segments (0x5d7fc : word) = Some W_5d7ac.
Proof. vm_refl. Qed.
Lemma D_5d7ac : decode_any W_5d7ac = Some (Store SZ8 10 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7b0 : bv 32 := 0x00c53023.
Lemma F_5d7b0 : fetch_word Asan.M.loaded_segments (0x5d800 : word) = Some W_5d7b0.
Proof. vm_refl. Qed.
Lemma D_5d7b0 : decode_any W_5d7b0 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7b4 : bv 32 := 0x00b53823.
Lemma F_5d7b4 : fetch_word Asan.M.loaded_segments (0x5d804 : word) = Some W_5d7b4.
Proof. vm_refl. Qed.
Lemma D_5d7b4 : decode_any W_5d7b4 = Some (Store SZ8 10 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7b8 : bv 32 := 0x01853583.
Lemma F_5d7b8 : fetch_word Asan.M.loaded_segments (0x5d808 : word) = Some W_5d7b8.
Proof. vm_refl. Qed.
Lemma D_5d7b8 : decode_any W_5d7b8 = Some (Load SZ8 true 11 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7bc : bv 32 := 0x00e585b3.
Lemma F_5d7bc : fetch_word Asan.M.loaded_segments (0x5d80c : word) = Some W_5d7bc.
Proof. vm_refl. Qed.
Lemma D_5d7bc : decode_any W_5d7bc = Some (Op ALU_ADD 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7c0 : bv 32 := 0x00b53c23.
Lemma F_5d7c0 : fetch_word Asan.M.loaded_segments (0x5d810 : word) = Some W_5d7c0.
Proof. vm_refl. Qed.
Lemma D_5d7c0 : decode_any W_5d7c0 = Some (Store SZ8 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7c4 : bv 32 := 0x03813083.
Lemma F_5d7c4 : fetch_word Asan.M.loaded_segments (0x5d814 : word) = Some W_5d7c4.
Proof. vm_refl. Qed.
Lemma D_5d7c4 : decode_any W_5d7c4 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7c8 : bv 32 := 0x03013403.
Lemma F_5d7c8 : fetch_word Asan.M.loaded_segments (0x5d818 : word) = Some W_5d7c8.
Proof. vm_refl. Qed.
Lemma D_5d7c8 : decode_any W_5d7c8 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7cc : bv 32 := 0x02813483.
Lemma F_5d7cc : fetch_word Asan.M.loaded_segments (0x5d81c : word) = Some W_5d7cc.
Proof. vm_refl. Qed.
Lemma D_5d7cc : decode_any W_5d7cc = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7d0 : bv 32 := 0x02013903.
Lemma F_5d7d0 : fetch_word Asan.M.loaded_segments (0x5d820 : word) = Some W_5d7d0.
Proof. vm_refl. Qed.
Lemma D_5d7d0 : decode_any W_5d7d0 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7d4 : bv 32 := 0x01813983.
Lemma F_5d7d4 : fetch_word Asan.M.loaded_segments (0x5d824 : word) = Some W_5d7d4.
Proof. vm_refl. Qed.
Lemma D_5d7d4 : decode_any W_5d7d4 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7d8 : bv 32 := 0x01013a03.
Lemma F_5d7d8 : fetch_word Asan.M.loaded_segments (0x5d828 : word) = Some W_5d7d8.
Proof. vm_refl. Qed.
Lemma D_5d7d8 : decode_any W_5d7d8 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7dc : bv 32 := 0x00813a83.
Lemma F_5d7dc : fetch_word Asan.M.loaded_segments (0x5d82c : word) = Some W_5d7dc.
Proof. vm_refl. Qed.
Lemma D_5d7dc : decode_any W_5d7dc = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7e0 : bv 32 := 0x04010113.
Lemma F_5d7e0 : fetch_word Asan.M.loaded_segments (0x5d830 : word) = Some W_5d7e0.
Proof. vm_refl. Qed.
Lemma D_5d7e0 : decode_any W_5d7e0 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7e4 : bv 32 := 0x00008067.
Lemma F_5d7e4 : fetch_word Asan.M.loaded_segments (0x5d834 : word) = Some W_5d7e4.
Proof. vm_refl. Qed.
Lemma D_5d7e4 : decode_any W_5d7e4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7e8 : bv 32 := 0x78058413.
Lemma F_5d7e8 : fetch_word Asan.M.loaded_segments (0x5d838 : word) = Some W_5d7e8.
Proof. vm_refl. Qed.
Lemma D_5d7e8 : decode_any W_5d7e8 = Some (OpImm ALU_ADD 8 11 1920, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7ec : bv 32 := 0x000ff797.
Lemma F_5d7ec : fetch_word Asan.M.loaded_segments (0x5d83c : word) = Some W_5d7ec.
Proof. vm_refl. Qed.
Lemma D_5d7ec : decode_any W_5d7ec = Some (Auipc 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7f0 : bv 32 := 0xbdc78793.
Lemma F_5d7f0 : fetch_word Asan.M.loaded_segments (0x5d840 : word) = Some W_5d7f0.
Proof. vm_refl. Qed.
Lemma D_5d7f0 : decode_any W_5d7f0 = Some (OpImm ALU_ADD 15 15 3036, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7f4 : bv 32 := 0x00068913.
Lemma F_5d7f4 : fetch_word Asan.M.loaded_segments (0x5d844 : word) = Some W_5d7f4.
Proof. vm_refl. Qed.
Lemma D_5d7f4 : decode_any W_5d7f4 = Some (OpImm ALU_ADD 18 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7f8 : bv 32 := 0x01800693.
Lemma F_5d7f8 : fetch_word Asan.M.loaded_segments (0x5d848 : word) = Some W_5d7f8.
Proof. vm_refl. Qed.
Lemma D_5d7f8 : decode_any W_5d7f8 = Some (OpImm ALU_ADD 13 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7fc : bv 32 := 0x00050993.
Lemma F_5d7fc : fetch_word Asan.M.loaded_segments (0x5d84c : word) = Some W_5d7fc.
Proof. vm_refl. Qed.
Lemma D_5d7fc : decode_any W_5d7fc = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d800 : bv 32 := 0x00058493.
Lemma F_5d800 : fetch_word Asan.M.loaded_segments (0x5d850 : word) = Some W_5d800.
Proof. vm_refl. Qed.
Lemma D_5d800 : decode_any W_5d800 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d804 : bv 32 := 0x00058513.
Lemma F_5d804 : fetch_word Asan.M.loaded_segments (0x5d854 : word) = Some W_5d804.
Proof. vm_refl. Qed.
Lemma D_5d804 : decode_any W_5d804 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d808 : bv 32 := 0x00040593.
Lemma F_5d808 : fetch_word Asan.M.loaded_segments (0x5d858 : word) = Some W_5d808.
Proof. vm_refl. Qed.
Lemma D_5d808 : decode_any W_5d808 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d80c : bv 32 := 0x00060a13.
Lemma F_5d80c : fetch_word Asan.M.loaded_segments (0x5d85c : word) = Some W_5d80c.
Proof. vm_refl. Qed.
Lemma D_5d80c : decode_any W_5d80c = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d810 : bv 32 := 0x00078613.
Lemma F_5d810 : fetch_word Asan.M.loaded_segments (0x5d860 : word) = Some W_5d810.
Proof. vm_refl. Qed.
Lemma D_5d810 : decode_any W_5d810 = Some (OpImm ALU_ADD 12 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d814 : bv 32 := 0x00070a93.
Lemma F_5d814 : fetch_word Asan.M.loaded_segments (0x5d864 : word) = Some W_5d814.
Proof. vm_refl. Qed.
Lemma D_5d814 : decode_any W_5d814 = Some (OpImm ALU_ADD 21 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d818 : bv 32 := 0x7e4000ef.
Lemma F_5d818 : fetch_word Asan.M.loaded_segments (0x5d868 : word) = Some W_5d818.
Proof. vm_refl. Qed.
Lemma D_5d818 : decode_any W_5d818 = Some (Jal 1 2020, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d81c : bv 32 := 0x000a0613.
Lemma F_5d81c : fetch_word Asan.M.loaded_segments (0x5d86c : word) = Some W_5d81c.
Proof. vm_refl. Qed.
Lemma D_5d81c : decode_any W_5d81c = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d820 : bv 32 := 0x00050e63.
Lemma F_5d820 : fetch_word Asan.M.loaded_segments (0x5d870 : word) = Some W_5d820.
Proof. vm_refl. Qed.
Lemma D_5d820 : decode_any W_5d820 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d824 : bv 32 := 0x00090693.
Lemma F_5d824 : fetch_word Asan.M.loaded_segments (0x5d874 : word) = Some W_5d824.
Proof. vm_refl. Qed.
Lemma D_5d824 : decode_any W_5d824 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d828 : bv 32 := 0x000a8713.
Lemma F_5d828 : fetch_word Asan.M.loaded_segments (0x5d878 : word) = Some W_5d828.
Proof. vm_refl. Qed.
Lemma D_5d828 : decode_any W_5d828 = Some (OpImm ALU_ADD 14 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d82c : bv 32 := 0x00098513.
Lemma F_5d82c : fetch_word Asan.M.loaded_segments (0x5d87c : word) = Some W_5d82c.
Proof. vm_refl. Qed.
Lemma D_5d82c : decode_any W_5d82c = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d830 : bv 32 := 0x00042783.
Lemma F_5d830 : fetch_word Asan.M.loaded_segments (0x5d880 : word) = Some W_5d830.
Proof. vm_refl. Qed.
Lemma D_5d830 : decode_any W_5d830 = Some (Load SZ4 true 15 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d834 : bv 32 := 0x00048593.
Lemma F_5d834 : fetch_word Asan.M.loaded_segments (0x5d884 : word) = Some W_5d834.
Proof. vm_refl. Qed.
Lemma D_5d834 : decode_any W_5d834 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d838 : bv 32 := 0xed1ff06f.
Lemma F_5d838 : fetch_word Asan.M.loaded_segments (0x5d888 : word) = Some W_5d838.
Proof. vm_refl. Qed.
Lemma D_5d838 : decode_any W_5d838 = Some (Jal 0 2096848, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8ac : bv 32 := 0xfd010113.
Lemma F_5d8ac : fetch_word Asan.M.loaded_segments (0x5d8fc : word) = Some W_5d8ac.
Proof. vm_refl. Qed.
Lemma D_5d8ac : decode_any W_5d8ac = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8b0 : bv 32 := 0x02113423.
Lemma F_5d8b0 : fetch_word Asan.M.loaded_segments (0x5d900 : word) = Some W_5d8b0.
Proof. vm_refl. Qed.
Lemma D_5d8b0 : decode_any W_5d8b0 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8b4 : bv 32 := 0x02813023.
Lemma F_5d8b4 : fetch_word Asan.M.loaded_segments (0x5d904 : word) = Some W_5d8b4.
Proof. vm_refl. Qed.
Lemma D_5d8b4 : decode_any W_5d8b4 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8b8 : bv 32 := 0x00913c23.
Lemma F_5d8b8 : fetch_word Asan.M.loaded_segments (0x5d908 : word) = Some W_5d8b8.
Proof. vm_refl. Qed.
Lemma D_5d8b8 : decode_any W_5d8b8 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8bc : bv 32 := 0x01213823.
Lemma F_5d8bc : fetch_word Asan.M.loaded_segments (0x5d90c : word) = Some W_5d8bc.
Proof. vm_refl. Qed.
Lemma D_5d8bc : decode_any W_5d8bc = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8c0 : bv 32 := 0x01313423.
Lemma F_5d8c0 : fetch_word Asan.M.loaded_segments (0x5d910 : word) = Some W_5d8c0.
Proof. vm_refl. Qed.
Lemma D_5d8c0 : decode_any W_5d8c0 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8c4 : bv 32 := 0x01413023.
Lemma F_5d8c4 : fetch_word Asan.M.loaded_segments (0x5d914 : word) = Some W_5d8c4.
Proof. vm_refl. Qed.
Lemma D_5d8c4 : decode_any W_5d8c4 = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8c8 : bv 32 := 0x00163713.
Lemma F_5d8c8 : fetch_word Asan.M.loaded_segments (0x5d918 : word) = Some W_5d8c8.
Proof. vm_refl. Qed.
Lemma D_5d8c8 : decode_any W_5d8c8 = Some (OpImm ALU_SLTU 14 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8cc : bv 32 := 0x00e60633.
Lemma F_5d8cc : fetch_word Asan.M.loaded_segments (0x5d91c : word) = Some W_5d8cc.
Proof. vm_refl. Qed.
Lemma D_5d8cc : decode_any W_5d8cc = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8d0 : bv 32 := 0xfff64713.
Lemma F_5d8d0 : fetch_word Asan.M.loaded_segments (0x5d920 : word) = Some W_5d8d0.
Proof. vm_refl. Qed.
Lemma D_5d8d0 : decode_any W_5d8d0 = Some (OpImm ALU_XOR 14 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8d4 : bv 32 := 0x02d77263.
Lemma F_5d8d4 : fetch_word Asan.M.loaded_segments (0x5d924 : word) = Some W_5d8d4.
Proof. vm_refl. Qed.
Lemma D_5d8d4 : decode_any W_5d8d4 = Some (Branch BC_GEU 14 13 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8f8 : bv 32 := 0x00900793.
Lemma F_5d8f8 : fetch_word Asan.M.loaded_segments (0x5d948 : word) = Some W_5d8f8.
Proof. vm_refl. Qed.
Lemma D_5d8f8 : decode_any W_5d8f8 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8fc : bv 32 := 0x00060713.
Lemma F_5d8fc : fetch_word Asan.M.loaded_segments (0x5d94c : word) = Some W_5d8fc.
Proof. vm_refl. Qed.
Lemma D_5d8fc : decode_any W_5d8fc = Some (OpImm ALU_ADD 14 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d900 : bv 32 := 0x02f6e063.
Lemma F_5d900 : fetch_word Asan.M.loaded_segments (0x5d950 : word) = Some W_5d900.
Proof. vm_refl. Qed.
Lemma D_5d900 : decode_any W_5d900 = Some (Branch BC_LTU 13 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d920 : bv 32 := 0x000107b7.
Lemma F_5d920 : fetch_word Asan.M.loaded_segments (0x5d970 : word) = Some W_5d920.
Proof. vm_refl. Qed.
Lemma D_5d920 : decode_any W_5d920 = Some (Lui 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d924 : bv 32 := 0x00d7ee63.
Lemma F_5d924 : fetch_word Asan.M.loaded_segments (0x5d974 : word) = Some W_5d924.
Proof. vm_refl. Qed.
Lemma D_5d924 : decode_any W_5d924 = Some (Branch BC_LTU 15 13 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d928 : bv 32 := 0x00e7ec63.
Lemma F_5d928 : fetch_word Asan.M.loaded_segments (0x5d978 : word) = Some W_5d928.
Proof. vm_refl. Qed.
Lemma D_5d928 : decode_any W_5d928 = Some (Branch BC_LTU 15 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d92c : bv 32 := 0x20000613.
Lemma F_5d92c : fetch_word Asan.M.loaded_segments (0x5d97c : word) = Some W_5d92c.
Proof. vm_refl. Qed.
Lemma D_5d92c : decode_any W_5d92c = Some (OpImm ALU_ADD 12 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d930 : bv 32 := 0x02e66a63.
Lemma F_5d930 : fetch_word Asan.M.loaded_segments (0x5d980 : word) = Some W_5d930.
Proof. vm_refl. Qed.
Lemma D_5d930 : decode_any W_5d930 = Some (Branch BC_LTU 12 14 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d934 : bv 32 := 0x01f70713.
Lemma F_5d934 : fetch_word Asan.M.loaded_segments (0x5d984 : word) = Some W_5d934.
Proof. vm_refl. Qed.
Lemma D_5d934 : decode_any W_5d934 = Some (OpImm ALU_ADD 14 14 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d938 : bv 32 := 0x00575413.
Lemma F_5d938 : fetch_word Asan.M.loaded_segments (0x5d988 : word) = Some W_5d938.
Proof. vm_refl. Qed.
Lemma D_5d938 : decode_any W_5d938 = Some (ShiftImm ALU_SRL 8 14 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d93c : bv 32 := 0x1040006f.
Lemma F_5d93c : fetch_word Asan.M.loaded_segments (0x5d98c : word) = Some W_5d93c.
Proof. vm_refl. Qed.
Lemma D_5d93c : decode_any W_5d93c = Some (Jal 0 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d940 : bv 32 := 0x04050713.
Lemma F_5d940 : fetch_word Asan.M.loaded_segments (0x5d990 : word) = Some W_5d940.
Proof. vm_refl. Qed.
Lemma D_5d940 : decode_any W_5d940 = Some (OpImm ALU_ADD 14 10 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d944 : bv 32 := 0x2b050593.
Lemma F_5d944 : fetch_word Asan.M.loaded_segments (0x5d994 : word) = Some W_5d944.
Proof. vm_refl. Qed.
Lemma D_5d944 : decode_any W_5d944 = Some (OpImm ALU_ADD 11 10 688, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d948 : bv 32 := 0x00070513.
Lemma F_5d948 : fetch_word Asan.M.loaded_segments (0x5d998 : word) = Some W_5d948.
Proof. vm_refl. Qed.
Lemma D_5d948 : decode_any W_5d948 = Some (OpImm ALU_ADD 10 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d94c : bv 32 := 0x00068413.
Lemma F_5d94c : fetch_word Asan.M.loaded_segments (0x5d99c : word) = Some W_5d94c.
Proof. vm_refl. Qed.
Lemma D_5d94c : decode_any W_5d94c = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d950 : bv 32 := 0x234000ef.
Lemma F_5d950 : fetch_word Asan.M.loaded_segments (0x5d9a0 : word) = Some W_5d950.
Proof. vm_refl. Qed.
Lemma D_5d950 : decode_any W_5d950 = Some (Jal 1 564, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d954 : bv 32 := 0x00040693.
Lemma F_5d954 : fetch_word Asan.M.loaded_segments (0x5d9a4 : word) = Some W_5d954.
Proof. vm_refl. Qed.
Lemma D_5d954 : decode_any W_5d954 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d958 : bv 32 := 0x00900593.
Lemma F_5d958 : fetch_word Asan.M.loaded_segments (0x5d9a8 : word) = Some W_5d958.
Proof. vm_refl. Qed.
Lemma D_5d958 : decode_any W_5d958 = Some (OpImm ALU_ADD 11 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d95c : bv 32 := 0x14b47463.
Lemma F_5d95c : fetch_word Asan.M.loaded_segments (0x5d9ac : word) = Some W_5d95c.
Proof. vm_refl. Qed.
Lemma D_5d95c : decode_any W_5d95c = Some (Branch BC_GEU 8 11 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d960 : bv 32 := 0x1500006f.
Lemma F_5d960 : fetch_word Asan.M.loaded_segments (0x5d9b0 : word) = Some W_5d960.
Proof. vm_refl. Qed.
Lemma D_5d960 : decode_any W_5d960 = Some (Jal 0 336, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d964 : bv 32 := 0x00175613.
Lemma F_5d964 : fetch_word Asan.M.loaded_segments (0x5d9b4 : word) = Some W_5d964.
Proof. vm_refl. Qed.
Lemma D_5d964 : decode_any W_5d964 = Some (ShiftImm ALU_SRL 12 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d968 : bv 32 := 0x555557b7.
Lemma F_5d968 : fetch_word Asan.M.loaded_segments (0x5d9b8 : word) = Some W_5d968.
Proof. vm_refl. Qed.
Lemma D_5d968 : decode_any W_5d968 = Some (Lui 15 349525, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d96c : bv 32 := 0x33333837.
Lemma F_5d96c : fetch_word Asan.M.loaded_segments (0x5d9bc : word) = Some W_5d96c.
Proof. vm_refl. Qed.
Lemma D_5d96c : decode_any W_5d96c = Some (Lui 16 209715, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d970 : bv 32 := 0x0f0f18b7.
Lemma F_5d970 : fetch_word Asan.M.loaded_segments (0x5d9c0 : word) = Some W_5d970.
Proof. vm_refl. Qed.
Lemma D_5d970 : decode_any W_5d970 = Some (Lui 17 61681, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d974 : bv 32 := 0x010102b7.
Lemma F_5d974 : fetch_word Asan.M.loaded_segments (0x5d9c4 : word) = Some W_5d974.
Proof. vm_refl. Qed.
Lemma D_5d974 : decode_any W_5d974 = Some (Lui 5 4112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d978 : bv 32 := 0x00c76633.
Lemma F_5d978 : fetch_word Asan.M.loaded_segments (0x5d9c8 : word) = Some W_5d978.
Proof. vm_refl. Qed.
Lemma D_5d978 : decode_any W_5d978 = Some (Op ALU_OR 12 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d97c : bv 32 := 0x5557879b.
Lemma F_5d97c : fetch_word Asan.M.loaded_segments (0x5d9cc : word) = Some W_5d97c.
Proof. vm_refl. Qed.
Lemma D_5d97c : decode_any W_5d97c = Some (OpImm32 15 15 1365, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d980 : bv 32 := 0x3338081b.
Lemma F_5d980 : fetch_word Asan.M.loaded_segments (0x5d9d0 : word) = Some W_5d980.
Proof. vm_refl. Qed.
Lemma D_5d980 : decode_any W_5d980 = Some (OpImm32 16 16 819, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d984 : bv 32 := 0xf0f8889b.
Lemma F_5d984 : fetch_word Asan.M.loaded_segments (0x5d9d4 : word) = Some W_5d984.
Proof. vm_refl. Qed.
Lemma D_5d984 : decode_any W_5d984 = Some (OpImm32 17 17 3855, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d988 : bv 32 := 0x1012829b.
Lemma F_5d988 : fetch_word Asan.M.loaded_segments (0x5d9d8 : word) = Some W_5d988.
Proof. vm_refl. Qed.
Lemma D_5d988 : decode_any W_5d988 = Some (OpImm32 5 5 257, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d98c : bv 32 := 0x00265313.
Lemma F_5d98c : fetch_word Asan.M.loaded_segments (0x5d9dc : word) = Some W_5d98c.
Proof. vm_refl. Qed.
Lemma D_5d98c : decode_any W_5d98c = Some (ShiftImm ALU_SRL 6 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d990 : bv 32 := 0x00666633.
Lemma F_5d990 : fetch_word Asan.M.loaded_segments (0x5d9e0 : word) = Some W_5d990.
Proof. vm_refl. Qed.
Lemma D_5d990 : decode_any W_5d990 = Some (Op ALU_OR 12 12 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d994 : bv 32 := 0x02079313.
Lemma F_5d994 : fetch_word Asan.M.loaded_segments (0x5d9e4 : word) = Some W_5d994.
Proof. vm_refl. Qed.
Lemma D_5d994 : decode_any W_5d994 = Some (ShiftImm ALU_SLL 6 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d998 : bv 32 := 0x006787b3.
Lemma F_5d998 : fetch_word Asan.M.loaded_segments (0x5d9e8 : word) = Some W_5d998.
Proof. vm_refl. Qed.
Lemma D_5d998 : decode_any W_5d998 = Some (Op ALU_ADD 15 15 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d99c : bv 32 := 0x02081313.
Lemma F_5d99c : fetch_word Asan.M.loaded_segments (0x5d9ec : word) = Some W_5d99c.
Proof. vm_refl. Qed.
Lemma D_5d99c : decode_any W_5d99c = Some (ShiftImm ALU_SLL 6 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9a0 : bv 32 := 0x00680833.
Lemma F_5d9a0 : fetch_word Asan.M.loaded_segments (0x5d9f0 : word) = Some W_5d9a0.
Proof. vm_refl. Qed.
Lemma D_5d9a0 : decode_any W_5d9a0 = Some (Op ALU_ADD 16 16 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9a4 : bv 32 := 0x02089313.
Lemma F_5d9a4 : fetch_word Asan.M.loaded_segments (0x5d9f4 : word) = Some W_5d9a4.
Proof. vm_refl. Qed.
Lemma D_5d9a4 : decode_any W_5d9a4 = Some (ShiftImm ALU_SLL 6 17 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9a8 : bv 32 := 0x006888b3.
Lemma F_5d9a8 : fetch_word Asan.M.loaded_segments (0x5d9f8 : word) = Some W_5d9a8.
Proof. vm_refl. Qed.
Lemma D_5d9a8 : decode_any W_5d9a8 = Some (Op ALU_ADD 17 17 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9ac : bv 32 := 0x02029313.
Lemma F_5d9ac : fetch_word Asan.M.loaded_segments (0x5d9fc : word) = Some W_5d9ac.
Proof. vm_refl. Qed.
Lemma D_5d9ac : decode_any W_5d9ac = Some (ShiftImm ALU_SLL 6 5 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9b0 : bv 32 := 0x006282b3.
Lemma F_5d9b0 : fetch_word Asan.M.loaded_segments (0x5da00 : word) = Some W_5d9b0.
Proof. vm_refl. Qed.
Lemma D_5d9b0 : decode_any W_5d9b0 = Some (Op ALU_ADD 5 5 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9b4 : bv 32 := 0x00465313.
Lemma F_5d9b4 : fetch_word Asan.M.loaded_segments (0x5da04 : word) = Some W_5d9b4.
Proof. vm_refl. Qed.
Lemma D_5d9b4 : decode_any W_5d9b4 = Some (ShiftImm ALU_SRL 6 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9b8 : bv 32 := 0x00666633.
Lemma F_5d9b8 : fetch_word Asan.M.loaded_segments (0x5da08 : word) = Some W_5d9b8.
Proof. vm_refl. Qed.
Lemma D_5d9b8 : decode_any W_5d9b8 = Some (Op ALU_OR 12 12 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9bc : bv 32 := 0x00865313.
Lemma F_5d9bc : fetch_word Asan.M.loaded_segments (0x5da0c : word) = Some W_5d9bc.
Proof. vm_refl. Qed.
Lemma D_5d9bc : decode_any W_5d9bc = Some (ShiftImm ALU_SRL 6 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9c0 : bv 32 := 0x00666633.
Lemma F_5d9c0 : fetch_word Asan.M.loaded_segments (0x5da10 : word) = Some W_5d9c0.
Proof. vm_refl. Qed.
Lemma D_5d9c0 : decode_any W_5d9c0 = Some (Op ALU_OR 12 12 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9c4 : bv 32 := 0x01065313.
Lemma F_5d9c4 : fetch_word Asan.M.loaded_segments (0x5da14 : word) = Some W_5d9c4.
Proof. vm_refl. Qed.
Lemma D_5d9c4 : decode_any W_5d9c4 = Some (ShiftImm ALU_SRL 6 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9c8 : bv 32 := 0x00666633.
Lemma F_5d9c8 : fetch_word Asan.M.loaded_segments (0x5da18 : word) = Some W_5d9c8.
Proof. vm_refl. Qed.
Lemma D_5d9c8 : decode_any W_5d9c8 = Some (Op ALU_OR 12 12 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9cc : bv 32 := 0x02065313.
Lemma F_5d9cc : fetch_word Asan.M.loaded_segments (0x5da1c : word) = Some W_5d9cc.
Proof. vm_refl. Qed.
Lemma D_5d9cc : decode_any W_5d9cc = Some (ShiftImm ALU_SRL 6 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9d0 : bv 32 := 0x00666633.
Lemma F_5d9d0 : fetch_word Asan.M.loaded_segments (0x5da20 : word) = Some W_5d9d0.
Proof. vm_refl. Qed.
Lemma D_5d9d0 : decode_any W_5d9d0 = Some (Op ALU_OR 12 12 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9d4 : bv 32 := 0xfff64613.
Lemma F_5d9d4 : fetch_word Asan.M.loaded_segments (0x5da24 : word) = Some W_5d9d4.
Proof. vm_refl. Qed.
Lemma D_5d9d4 : decode_any W_5d9d4 = Some (OpImm ALU_XOR 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9d8 : bv 32 := 0x00165313.
Lemma F_5d9d8 : fetch_word Asan.M.loaded_segments (0x5da28 : word) = Some W_5d9d8.
Proof. vm_refl. Qed.
Lemma D_5d9d8 : decode_any W_5d9d8 = Some (ShiftImm ALU_SRL 6 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9dc : bv 32 := 0x00f377b3.
Lemma F_5d9dc : fetch_word Asan.M.loaded_segments (0x5da2c : word) = Some W_5d9dc.
Proof. vm_refl. Qed.
Lemma D_5d9dc : decode_any W_5d9dc = Some (Op ALU_AND 15 6 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9e0 : bv 32 := 0x40f60633.
Lemma F_5d9e0 : fetch_word Asan.M.loaded_segments (0x5da30 : word) = Some W_5d9e0.
Proof. vm_refl. Qed.
Lemma D_5d9e0 : decode_any W_5d9e0 = Some (Op ALU_SUB 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9e4 : bv 32 := 0x010677b3.
Lemma F_5d9e4 : fetch_word Asan.M.loaded_segments (0x5da34 : word) = Some W_5d9e4.
Proof. vm_refl. Qed.
Lemma D_5d9e4 : decode_any W_5d9e4 = Some (Op ALU_AND 15 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9e8 : bv 32 := 0x00265613.
Lemma F_5d9e8 : fetch_word Asan.M.loaded_segments (0x5da38 : word) = Some W_5d9e8.
Proof. vm_refl. Qed.
Lemma D_5d9e8 : decode_any W_5d9e8 = Some (ShiftImm ALU_SRL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9ec : bv 32 := 0x01067633.
Lemma F_5d9ec : fetch_word Asan.M.loaded_segments (0x5da3c : word) = Some W_5d9ec.
Proof. vm_refl. Qed.
Lemma D_5d9ec : decode_any W_5d9ec = Some (Op ALU_AND 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9f0 : bv 32 := 0x00c78633.
Lemma F_5d9f0 : fetch_word Asan.M.loaded_segments (0x5da40 : word) = Some W_5d9f0.
Proof. vm_refl. Qed.
Lemma D_5d9f0 : decode_any W_5d9f0 = Some (Op ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9f4 : bv 32 := 0x00465793.
Lemma F_5d9f4 : fetch_word Asan.M.loaded_segments (0x5da44 : word) = Some W_5d9f4.
Proof. vm_refl. Qed.
Lemma D_5d9f4 : decode_any W_5d9f4 = Some (ShiftImm ALU_SRL 15 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9f8 : bv 32 := 0x00f60633.
Lemma F_5d9f8 : fetch_word Asan.M.loaded_segments (0x5da48 : word) = Some W_5d9f8.
Proof. vm_refl. Qed.
Lemma D_5d9f8 : decode_any W_5d9f8 = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9fc : bv 32 := 0x03e00793.
Lemma F_5d9fc : fetch_word Asan.M.loaded_segments (0x5da4c : word) = Some W_5d9fc.
Proof. vm_refl. Qed.
Lemma D_5d9fc : decode_any W_5d9fc = Some (OpImm ALU_ADD 15 0 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da00 : bv 32 := 0x01167633.
Lemma F_5da00 : fetch_word Asan.M.loaded_segments (0x5da50 : word) = Some W_5da00.
Proof. vm_refl. Qed.
Lemma D_5da00 : decode_any W_5da00 = Some (Op ALU_AND 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da04 : bv 32 := 0xfff00813.
Lemma F_5da04 : fetch_word Asan.M.loaded_segments (0x5da54 : word) = Some W_5da04.
Proof. vm_refl. Qed.
Lemma D_5da04 : decode_any W_5da04 = Some (OpImm ALU_ADD 16 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da08 : bv 32 := 0x02560633.
Lemma F_5da08 : fetch_word Asan.M.loaded_segments (0x5da58 : word) = Some W_5da08.
Proof. vm_refl. Qed.
Lemma D_5da08 : decode_any W_5da08 = Some (Mul M_MUL 12 12 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da0c : bv 32 := 0x03865613.
Lemma F_5da0c : fetch_word Asan.M.loaded_segments (0x5da5c : word) = Some W_5da0c.
Proof. vm_refl. Qed.
Lemma D_5da0c : decode_any W_5da0c = Some (ShiftImm ALU_SRL 12 12 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da10 : bv 32 := 0x40c787bb.
Lemma F_5da10 : fetch_word Asan.M.loaded_segments (0x5da60 : word) = Some W_5da10.
Proof. vm_refl. Qed.
Lemma D_5da10 : decode_any W_5da10 = Some (Op32 ALU_SUB 15 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da14 : bv 32 := 0x00161613.
Lemma F_5da14 : fetch_word Asan.M.loaded_segments (0x5da64 : word) = Some W_5da14.
Proof. vm_refl. Qed.
Lemma D_5da14 : decode_any W_5da14 = Some (ShiftImm ALU_SLL 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da18 : bv 32 := 0x00f758b3.
Lemma F_5da18 : fetch_word Asan.M.loaded_segments (0x5da68 : word) = Some W_5da18.
Proof. vm_refl. Qed.
Lemma D_5da18 : decode_any W_5da18 = Some (Op ALU_SRL 17 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da1c : bv 32 := 0x00f817bb.
Lemma F_5da1c : fetch_word Asan.M.loaded_segments (0x5da6c : word) = Some W_5da1c.
Proof. vm_refl. Qed.
Lemma D_5da1c : decode_any W_5da1c = Some (Op32 ALU_SLL 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da20 : bv 32 := 0x07e64613.
Lemma F_5da20 : fetch_word Asan.M.loaded_segments (0x5da70 : word) = Some W_5da20.
Proof. vm_refl. Qed.
Lemma D_5da20 : decode_any W_5da20 = Some (OpImm ALU_XOR 12 12 126, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da24 : bv 32 := 0x0018f813.
Lemma F_5da24 : fetch_word Asan.M.loaded_segments (0x5da74 : word) = Some W_5da24.
Proof. vm_refl. Qed.
Lemma D_5da24 : decode_any W_5da24 = Some (OpImm ALU_AND 16 17 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da28 : bv 32 := 0xfff7c793.
Lemma F_5da28 : fetch_word Asan.M.loaded_segments (0x5da78 : word) = Some W_5da28.
Proof. vm_refl. Qed.
Lemma D_5da28 : decode_any W_5da28 = Some (OpImm ALU_XOR 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da2c : bv 32 := 0x00f77733.
Lemma F_5da2c : fetch_word Asan.M.loaded_segments (0x5da7c : word) = Some W_5da2c.
Proof. vm_refl. Qed.
Lemma D_5da2c : decode_any W_5da2c = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da30 : bv 32 := 0x01066633.
Lemma F_5da30 : fetch_word Asan.M.loaded_segments (0x5da80 : word) = Some W_5da30.
Proof. vm_refl. Qed.
Lemma D_5da30 : decode_any W_5da30 = Some (Op ALU_OR 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da34 : bv 32 := 0x00e03733.
Lemma F_5da34 : fetch_word Asan.M.loaded_segments (0x5da84 : word) = Some W_5da34.
Proof. vm_refl. Qed.
Lemma D_5da34 : decode_any W_5da34 = Some (Op ALU_SLTU 14 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da38 : bv 32 := 0x00e60633.
Lemma F_5da38 : fetch_word Asan.M.loaded_segments (0x5da88 : word) = Some W_5da38.
Proof. vm_refl. Qed.
Lemma D_5da38 : decode_any W_5da38 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da3c : bv 32 := 0xffe60413.
Lemma F_5da3c : fetch_word Asan.M.loaded_segments (0x5da8c : word) = Some W_5da3c.
Proof. vm_refl. Qed.
Lemma D_5da3c : decode_any W_5da3c = Some (OpImm ALU_ADD 8 12 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da40 : bv 32 := 0x0a040063.
Lemma F_5da40 : fetch_word Asan.M.loaded_segments (0x5da90 : word) = Some W_5da40.
Proof. vm_refl. Qed.
Lemma D_5da40 : decode_any W_5da40 = Some (Branch BC_EQ 8 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da44 : bv 32 := 0x02000613.
Lemma F_5da44 : fetch_word Asan.M.loaded_segments (0x5da94 : word) = Some W_5da44.
Proof. vm_refl. Qed.
Lemma D_5da44 : decode_any W_5da44 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da48 : bv 32 := 0x0cc47a63.
Lemma F_5da48 : fetch_word Asan.M.loaded_segments (0x5da98 : word) = Some W_5da48.
Proof. vm_refl. Qed.
Lemma D_5da48 : decode_any W_5da48 = Some (Branch BC_GEU 8 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da4c : bv 32 := 0x05000613.
Lemma F_5da4c : fetch_word Asan.M.loaded_segments (0x5da9c : word) = Some W_5da4c.
Proof. vm_refl. Qed.
Lemma D_5da4c : decode_any W_5da4c = Some (OpImm ALU_ADD 12 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da50 : bv 32 := 0x02c404b3.
Lemma F_5da50 : fetch_word Asan.M.loaded_segments (0x5daa0 : word) = Some W_5da50.
Proof. vm_refl. Qed.
Lemma D_5da50 : decode_any W_5da50 = Some (Mul M_MUL 9 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da54 : bv 32 := 0x009584b3.
Lemma F_5da54 : fetch_word Asan.M.loaded_segments (0x5daa4 : word) = Some W_5da54.
Proof. vm_refl. Qed.
Lemma D_5da54 : decode_any W_5da54 = Some (Op ALU_ADD 9 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da58 : bv 32 := 0x0004a603.
Lemma F_5da58 : fetch_word Asan.M.loaded_segments (0x5daa8 : word) = Some W_5da58.
Proof. vm_refl. Qed.
Lemma D_5da58 : decode_any W_5da58 = Some (Load SZ4 true 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da5c : bv 32 := 0x0e060063.
Lemma F_5da5c : fetch_word Asan.M.loaded_segments (0x5daac : word) = Some W_5da5c.
Proof. vm_refl. Qed.
Lemma D_5da5c : decode_any W_5da5c = Some (Branch BC_EQ 12 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da60 : bv 32 := 0xfff60613.
Lemma F_5da60 : fetch_word Asan.M.loaded_segments (0x5dab0 : word) = Some W_5da60.
Proof. vm_refl. Qed.
Lemma D_5da60 : decode_any W_5da60 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da64 : bv 32 := 0x7ff58593.
Lemma F_5da64 : fetch_word Asan.M.loaded_segments (0x5dab4 : word) = Some W_5da64.
Proof. vm_refl. Qed.
Lemma D_5da64 : decode_any W_5da64 = Some (OpImm ALU_ADD 11 11 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da68 : bv 32 := 0x02061713.
Lemma F_5da68 : fetch_word Asan.M.loaded_segments (0x5dab8 : word) = Some W_5da68.
Proof. vm_refl. Qed.
Lemma D_5da68 : decode_any W_5da68 = Some (ShiftImm ALU_SLL 14 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da6c : bv 32 := 0x00c4a023.
Lemma F_5da6c : fetch_word Asan.M.loaded_segments (0x5dabc : word) = Some W_5da6c.
Proof. vm_refl. Qed.
Lemma D_5da6c : decode_any W_5da6c = Some (Store SZ4 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da70 : bv 32 := 0x21158593.
Lemma F_5da70 : fetch_word Asan.M.loaded_segments (0x5dac0 : word) = Some W_5da70.
Proof. vm_refl. Qed.
Lemma D_5da70 : decode_any W_5da70 = Some (OpImm ALU_ADD 11 11 529, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da74 : bv 32 := 0x0084b603.
Lemma F_5da74 : fetch_word Asan.M.loaded_segments (0x5dac4 : word) = Some W_5da74.
Proof. vm_refl. Qed.
Lemma D_5da74 : decode_any W_5da74 = Some (Load SZ8 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da78 : bv 32 := 0x01e75713.
Lemma F_5da78 : fetch_word Asan.M.loaded_segments (0x5dac8 : word) = Some W_5da78.
Proof. vm_refl. Qed.
Lemma D_5da78 : decode_any W_5da78 = Some (ShiftImm ALU_SRL 14 14 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da7c : bv 32 := 0x00e48733.
Lemma F_5da7c : fetch_word Asan.M.loaded_segments (0x5dacc : word) = Some W_5da7c.
Proof. vm_refl. Qed.
Lemma D_5da7c : decode_any W_5da7c = Some (Op ALU_ADD 14 9 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da80 : bv 32 := 0x01076703.
Lemma F_5da80 : fetch_word Asan.M.loaded_segments (0x5dad0 : word) = Some W_5da80.
Proof. vm_refl. Qed.
Lemma D_5da80 : decode_any W_5da80 = Some (Load SZ4 false 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da84 : bv 32 := 0x00c5b02f.
Lemma F_5da84 : fetch_word Asan.M.loaded_segments (0x5dad4 : word) = Some W_5da84.
Proof. vm_refl. Qed.
Lemma D_5da84 : decode_any W_5da84 = Some (Amo AMO_ADD AD false false 0 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da88 : bv 32 := 0x02053503.
Lemma F_5da88 : fetch_word Asan.M.loaded_segments (0x5dad8 : word) = Some W_5da88.
Proof. vm_refl. Qed.
Lemma D_5da88 : decode_any W_5da88 = Some (Load SZ8 true 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da8c : bv 32 := 0x02041413.
Lemma F_5da8c : fetch_word Asan.M.loaded_segments (0x5dadc : word) = Some W_5da8c.
Proof. vm_refl. Qed.
Lemma D_5da8c : decode_any W_5da8c = Some (ShiftImm ALU_SLL 8 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da90 : bv 32 := 0x00471713.
Lemma F_5da90 : fetch_word Asan.M.loaded_segments (0x5dae0 : word) = Some W_5da90.
Proof. vm_refl. Qed.
Lemma D_5da90 : decode_any W_5da90 = Some (ShiftImm ALU_SLL 14 14 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da94 : bv 32 := 0x00a40533.
Lemma F_5da94 : fetch_word Asan.M.loaded_segments (0x5dae4 : word) = Some W_5da94.
Proof. vm_refl. Qed.
Lemma D_5da94 : decode_any W_5da94 = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da98 : bv 32 := 0x00a70533.
Lemma F_5da98 : fetch_word Asan.M.loaded_segments (0x5dae8 : word) = Some W_5da98.
Proof. vm_refl. Qed.
Lemma D_5da98 : decode_any W_5da98 = Some (Op ALU_ADD 10 14 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da9c : bv 32 := 0x00900593.
Lemma F_5da9c : fetch_word Asan.M.loaded_segments (0x5daec : word) = Some W_5da9c.
Proof. vm_refl. Qed.
Lemma D_5da9c : decode_any W_5da9c = Some (OpImm ALU_ADD 11 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5daa0 : bv 32 := 0x00b6e863.
Lemma F_5daa0 : fetch_word Asan.M.loaded_segments (0x5daf0 : word) = Some W_5daa0.
Proof. vm_refl. Qed.
Lemma D_5daa0 : decode_any W_5daa0 = Some (Branch BC_LTU 13 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5daa4 : bv 32 := 0xfff68693.
Lemma F_5daa4 : fetch_word Asan.M.loaded_segments (0x5daf4 : word) = Some W_5daa4.
Proof. vm_refl. Qed.
Lemma D_5daa4 : decode_any W_5daa4 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5daa8 : bv 32 := 0x00a6f6b3.
Lemma F_5daa8 : fetch_word Asan.M.loaded_segments (0x5daf8 : word) = Some W_5daa8.
Proof. vm_refl. Qed.
Lemma D_5daa8 : decode_any W_5daa8 = Some (Op ALU_AND 13 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5daac : bv 32 := 0x04069a63.
Lemma F_5daac : fetch_word Asan.M.loaded_segments (0x5dafc : word) = Some W_5daac.
Proof. vm_refl. Qed.
Lemma D_5daac : decode_any W_5daac = Some (Branch BC_NE 13 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dab0 : bv 32 := 0x02813083.
Lemma F_5dab0 : fetch_word Asan.M.loaded_segments (0x5db00 : word) = Some W_5dab0.
Proof. vm_refl. Qed.
Lemma D_5dab0 : decode_any W_5dab0 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dab4 : bv 32 := 0x02013403.
Lemma F_5dab4 : fetch_word Asan.M.loaded_segments (0x5db04 : word) = Some W_5dab4.
Proof. vm_refl. Qed.
Lemma D_5dab4 : decode_any W_5dab4 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dab8 : bv 32 := 0x01813483.
Lemma F_5dab8 : fetch_word Asan.M.loaded_segments (0x5db08 : word) = Some W_5dab8.
Proof. vm_refl. Qed.
Lemma D_5dab8 : decode_any W_5dab8 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dabc : bv 32 := 0x01013903.
Lemma F_5dabc : fetch_word Asan.M.loaded_segments (0x5db0c : word) = Some W_5dabc.
Proof. vm_refl. Qed.
Lemma D_5dabc : decode_any W_5dabc = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dac0 : bv 32 := 0x00813983.
Lemma F_5dac0 : fetch_word Asan.M.loaded_segments (0x5db10 : word) = Some W_5dac0.
Proof. vm_refl. Qed.
Lemma D_5dac0 : decode_any W_5dac0 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dac4 : bv 32 := 0x00013a03.
Lemma F_5dac4 : fetch_word Asan.M.loaded_segments (0x5db14 : word) = Some W_5dac4.
Proof. vm_refl. Qed.
Lemma D_5dac4 : decode_any W_5dac4 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dac8 : bv 32 := 0x03010113.
Lemma F_5dac8 : fetch_word Asan.M.loaded_segments (0x5db18 : word) = Some W_5dac8.
Proof. vm_refl. Qed.
Lemma D_5dac8 : decode_any W_5dac8 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dacc : bv 32 := 0x00008067.
Lemma F_5dacc : fetch_word Asan.M.loaded_segments (0x5db1c : word) = Some W_5dacc.
Proof. vm_refl. Qed.
Lemma D_5dacc : decode_any W_5dacc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db3c : bv 32 := 0x00068913.
Lemma F_5db3c : fetch_word Asan.M.loaded_segments (0x5db8c : word) = Some W_5db3c.
Proof. vm_refl. Qed.
Lemma D_5db3c : decode_any W_5db3c = Some (OpImm ALU_ADD 18 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db40 : bv 32 := 0x00050613.
Lemma F_5db40 : fetch_word Asan.M.loaded_segments (0x5db90 : word) = Some W_5db40.
Proof. vm_refl. Qed.
Lemma D_5db40 : decode_any W_5db40 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db44 : bv 32 := 0x00058993.
Lemma F_5db44 : fetch_word Asan.M.loaded_segments (0x5db94 : word) = Some W_5db44.
Proof. vm_refl. Qed.
Lemma D_5db44 : decode_any W_5db44 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db48 : bv 32 := 0x00058513.
Lemma F_5db48 : fetch_word Asan.M.loaded_segments (0x5db98 : word) = Some W_5db48.
Proof. vm_refl. Qed.
Lemma D_5db48 : decode_any W_5db48 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db4c : bv 32 := 0x00048593.
Lemma F_5db4c : fetch_word Asan.M.loaded_segments (0x5db9c : word) = Some W_5db4c.
Proof. vm_refl. Qed.
Lemma D_5db4c : decode_any W_5db4c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db50 : bv 32 := 0x00060a13.
Lemma F_5db50 : fetch_word Asan.M.loaded_segments (0x5dba0 : word) = Some W_5db50.
Proof. vm_refl. Qed.
Lemma D_5db50 : decode_any W_5db50 = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db54 : bv 32 := 0x00040693.
Lemma F_5db54 : fetch_word Asan.M.loaded_segments (0x5dba4 : word) = Some W_5db54.
Proof. vm_refl. Qed.
Lemma D_5db54 : decode_any W_5db54 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db58 : bv 32 := 0x4a4000ef.
Lemma F_5db58 : fetch_word Asan.M.loaded_segments (0x5dba8 : word) = Some W_5db58.
Proof. vm_refl. Qed.
Lemma D_5db58 : decode_any W_5db58 = Some (Jal 1 1188, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db5c : bv 32 := 0x00050c63.
Lemma F_5db5c : fetch_word Asan.M.loaded_segments (0x5dbac : word) = Some W_5db5c.
Proof. vm_refl. Qed.
Lemma D_5db5c : decode_any W_5db5c = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db60 : bv 32 := 0x0004a603.
Lemma F_5db60 : fetch_word Asan.M.loaded_segments (0x5dbb0 : word) = Some W_5db60.
Proof. vm_refl. Qed.
Lemma D_5db60 : decode_any W_5db60 = Some (Load SZ4 true 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db64 : bv 32 := 0x00090693.
Lemma F_5db64 : fetch_word Asan.M.loaded_segments (0x5dbb4 : word) = Some W_5db64.
Proof. vm_refl. Qed.
Lemma D_5db64 : decode_any W_5db64 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db68 : bv 32 := 0x000a0513.
Lemma F_5db68 : fetch_word Asan.M.loaded_segments (0x5dbb8 : word) = Some W_5db68.
Proof. vm_refl. Qed.
Lemma D_5db68 : decode_any W_5db68 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db6c : bv 32 := 0x00098593.
Lemma F_5db6c : fetch_word Asan.M.loaded_segments (0x5dbbc : word) = Some W_5db6c.
Proof. vm_refl. Qed.
Lemma D_5db6c : decode_any W_5db6c = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db70 : bv 32 := 0xef1ff06f.
Lemma F_5db70 : fetch_word Asan.M.loaded_segments (0x5dbc0 : word) = Some W_5db70.
Proof. vm_refl. Qed.
Lemma D_5db70 : decode_any W_5db70 = Some (Jal 0 2096880, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db84 : bv 32 := 0xfa010113.
Lemma F_5db84 : fetch_word Asan.M.loaded_segments (0x5dbd4 : word) = Some W_5db84.
Proof. vm_refl. Qed.
Lemma D_5db84 : decode_any W_5db84 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db88 : bv 32 := 0x04113c23.
Lemma F_5db88 : fetch_word Asan.M.loaded_segments (0x5dbd8 : word) = Some W_5db88.
Proof. vm_refl. Qed.
Lemma D_5db88 : decode_any W_5db88 = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db8c : bv 32 := 0x04813823.
Lemma F_5db8c : fetch_word Asan.M.loaded_segments (0x5dbdc : word) = Some W_5db8c.
Proof. vm_refl. Qed.
Lemma D_5db8c : decode_any W_5db8c = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db90 : bv 32 := 0x04913423.
Lemma F_5db90 : fetch_word Asan.M.loaded_segments (0x5dbe0 : word) = Some W_5db90.
Proof. vm_refl. Qed.
Lemma D_5db90 : decode_any W_5db90 = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db94 : bv 32 := 0x05213023.
Lemma F_5db94 : fetch_word Asan.M.loaded_segments (0x5dbe4 : word) = Some W_5db94.
Proof. vm_refl. Qed.
Lemma D_5db94 : decode_any W_5db94 = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db98 : bv 32 := 0x03313c23.
Lemma F_5db98 : fetch_word Asan.M.loaded_segments (0x5dbe8 : word) = Some W_5db98.
Proof. vm_refl. Qed.
Lemma D_5db98 : decode_any W_5db98 = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5db9c : bv 32 := 0x03413823.
Lemma F_5db9c : fetch_word Asan.M.loaded_segments (0x5dbec : word) = Some W_5db9c.
Proof. vm_refl. Qed.
Lemma D_5db9c : decode_any W_5db9c = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dba0 : bv 32 := 0x03513423.
Lemma F_5dba0 : fetch_word Asan.M.loaded_segments (0x5dbf0 : word) = Some W_5dba0.
Proof. vm_refl. Qed.
Lemma D_5dba0 : decode_any W_5dba0 = Some (Store SZ8 2 21 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dba4 : bv 32 := 0x03613023.
Lemma F_5dba4 : fetch_word Asan.M.loaded_segments (0x5dbf4 : word) = Some W_5dba4.
Proof. vm_refl. Qed.
Lemma D_5dba4 : decode_any W_5dba4 = Some (Store SZ8 2 22 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dba8 : bv 32 := 0x01713c23.
Lemma F_5dba8 : fetch_word Asan.M.loaded_segments (0x5dbf8 : word) = Some W_5dba8.
Proof. vm_refl. Qed.
Lemma D_5dba8 : decode_any W_5dba8 = Some (Store SZ8 2 23 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbac : bv 32 := 0x01813823.
Lemma F_5dbac : fetch_word Asan.M.loaded_segments (0x5dbfc : word) = Some W_5dbac.
Proof. vm_refl. Qed.
Lemma D_5dbac : decode_any W_5dbac = Some (Store SZ8 2 24 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbb0 : bv 32 := 0x01913423.
Lemma F_5dbb0 : fetch_word Asan.M.loaded_segments (0x5dc00 : word) = Some W_5dbb0.
Proof. vm_refl. Qed.
Lemma D_5dbb0 : decode_any W_5dbb0 = Some (Store SZ8 2 25 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbb4 : bv 32 := 0x00058413.
Lemma F_5dbb4 : fetch_word Asan.M.loaded_segments (0x5dc04 : word) = Some W_5dbb4.
Proof. vm_refl. Qed.
Lemma D_5dbb4 : decode_any W_5dbb4 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbb8 : bv 32 := 0xfff68c13.
Lemma F_5dbb8 : fetch_word Asan.M.loaded_segments (0x5dc08 : word) = Some W_5dbb8.
Proof. vm_refl. Qed.
Lemma D_5dbb8 : decode_any W_5dbb8 = Some (OpImm ALU_ADD 24 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbbc : bv 32 := 0x0186f5b3.
Lemma F_5dbbc : fetch_word Asan.M.loaded_segments (0x5dc0c : word) = Some W_5dbbc.
Proof. vm_refl. Qed.
Lemma D_5dbbc : decode_any W_5dbbc = Some (Op ALU_AND 11 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbc0 : bv 32 := 0x2c059a63.
Lemma F_5dbc0 : fetch_word Asan.M.loaded_segments (0x5dc10 : word) = Some W_5dbc0.
Proof. vm_refl. Qed.
Lemma D_5dbc0 : decode_any W_5dbc0 = Some (Branch BC_NE 11 0 724, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbc4 : bv 32 := 0x00050493.
Lemma F_5dbc4 : fetch_word Asan.M.loaded_segments (0x5dc14 : word) = Some W_5dbc4.
Proof. vm_refl. Qed.
Lemma D_5dbc4 : decode_any W_5dbc4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbc8 : bv 32 := 0x00053503.
Lemma F_5dbc8 : fetch_word Asan.M.loaded_segments (0x5dc18 : word) = Some W_5dbc8.
Proof. vm_refl. Qed.
Lemma D_5dbc8 : decode_any W_5dbc8 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbcc : bv 32 := 0xfff50593.
Lemma F_5dbcc : fetch_word Asan.M.loaded_segments (0x5dc1c : word) = Some W_5dbcc.
Proof. vm_refl. Qed.
Lemma D_5dbcc : decode_any W_5dbcc = Some (OpImm ALU_ADD 11 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbd0 : bv 32 := 0x00b575b3.
Lemma F_5dbd0 : fetch_word Asan.M.loaded_segments (0x5dc20 : word) = Some W_5dbd0.
Proof. vm_refl. Qed.
Lemma D_5dbd0 : decode_any W_5dbd0 = Some (Op ALU_AND 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbd4 : bv 32 := 0x2e059063.
Lemma F_5dbd4 : fetch_word Asan.M.loaded_segments (0x5dc24 : word) = Some W_5dbd4.
Proof. vm_refl. Qed.
Lemma D_5dbd4 : decode_any W_5dbd4 = Some (Branch BC_NE 11 0 736, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbd8 : bv 32 := 0x00060993.
Lemma F_5dbd8 : fetch_word Asan.M.loaded_segments (0x5dc28 : word) = Some W_5dbd8.
Proof. vm_refl. Qed.
Lemma D_5dbd8 : decode_any W_5dbd8 = Some (OpImm ALU_ADD 19 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbdc : bv 32 := 0x00a605b3.
Lemma F_5dbdc : fetch_word Asan.M.loaded_segments (0x5dc2c : word) = Some W_5dbdc.
Proof. vm_refl. Qed.
Lemma D_5dbdc : decode_any W_5dbdc = Some (Op ALU_ADD 11 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbe0 : bv 32 := 0x40a00633.
Lemma F_5dbe0 : fetch_word Asan.M.loaded_segments (0x5dc30 : word) = Some W_5dbe0.
Proof. vm_refl. Qed.
Lemma D_5dbe0 : decode_any W_5dbe0 = Some (Op ALU_SUB 12 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbe4 : bv 32 := 0xfff58593.
Lemma F_5dbe4 : fetch_word Asan.M.loaded_segments (0x5dc34 : word) = Some W_5dbe4.
Proof. vm_refl. Qed.
Lemma D_5dbe4 : decode_any W_5dbe4 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbe8 : bv 32 := 0x00c5f5b3.
Lemma F_5dbe8 : fetch_word Asan.M.loaded_segments (0x5dc38 : word) = Some W_5dbe8.
Proof. vm_refl. Qed.
Lemma D_5dbe8 : decode_any W_5dbe8 = Some (Op ALU_AND 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbec : bv 32 := 0x00d53633.
Lemma F_5dbec : fetch_word Asan.M.loaded_segments (0x5dc3c : word) = Some W_5dbec.
Proof. vm_refl. Qed.
Lemma D_5dbec : decode_any W_5dbec = Some (Op ALU_SLTU 12 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbf0 : bv 32 := 0x40c00633.
Lemma F_5dbf0 : fetch_word Asan.M.loaded_segments (0x5dc40 : word) = Some W_5dbf0.
Proof. vm_refl. Qed.
Lemma D_5dbf0 : decode_any W_5dbf0 = Some (Op ALU_SUB 12 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbf4 : bv 32 := 0x00a58533.
Lemma F_5dbf4 : fetch_word Asan.M.loaded_segments (0x5dc44 : word) = Some W_5dbf4.
Proof. vm_refl. Qed.
Lemma D_5dbf4 : decode_any W_5dbf4 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbf8 : bv 32 := 0x00d67633.
Lemma F_5dbf8 : fetch_word Asan.M.loaded_segments (0x5dc48 : word) = Some W_5dbf8.
Proof. vm_refl. Qed.
Lemma D_5dbf8 : decode_any W_5dbf8 = Some (Op ALU_AND 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbfc : bv 32 := 0x00c50933.
Lemma F_5dbfc : fetch_word Asan.M.loaded_segments (0x5dc4c : word) = Some W_5dbfc.
Proof. vm_refl. Qed.
Lemma D_5dbfc : decode_any W_5dbfc = Some (Op ALU_ADD 18 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc00 : bv 32 := 0x03397463.
Lemma F_5dc00 : fetch_word Asan.M.loaded_segments (0x5dc50 : word) = Some W_5dc00.
Proof. vm_refl. Qed.
Lemma D_5dc00 : decode_any W_5dc00 = Some (Branch BC_GEU 18 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc28 : bv 32 := 0x00068a93.
Lemma F_5dc28 : fetch_word Asan.M.loaded_segments (0x5dc78 : word) = Some W_5dc28.
Proof. vm_refl. Qed.
Lemma D_5dc28 : decode_any W_5dc28 = Some (OpImm ALU_ADD 21 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc2c : bv 32 := 0x000f9517.
Lemma F_5dc2c : fetch_word Asan.M.loaded_segments (0x5dc7c : word) = Some W_5dc2c.
Proof. vm_refl. Qed.
Lemma D_5dc2c : decode_any W_5dc2c = Some (Auipc 10 249, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc30 : bv 32 := 0x10453503.
Lemma F_5dc30 : fetch_word Asan.M.loaded_segments (0x5dc80 : word) = Some W_5dc30.
Proof. vm_refl. Qed.
Lemma D_5dc30 : decode_any W_5dc30 = Some (Load SZ8 true 10 10 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc34 : bv 32 := 0x00053583.
Lemma F_5dc34 : fetch_word Asan.M.loaded_segments (0x5dc84 : word) = Some W_5dc34.
Proof. vm_refl. Qed.
Lemma D_5dc34 : decode_any W_5dc34 = Some (Load SZ8 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc38 : bv 32 := 0x00090513.
Lemma F_5dc38 : fetch_word Asan.M.loaded_segments (0x5dc88 : word) = Some W_5dc38.
Proof. vm_refl. Qed.
Lemma D_5dc38 : decode_any W_5dc38 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc3c : bv 32 := 0x7e4360ef.
Lemma F_5dc3c : fetch_word Asan.M.loaded_segments (0x5dc8c : word) = Some W_5dc3c.
Proof. vm_refl. Qed.
Lemma D_5dc3c : decode_any W_5dc3c = Some (Jal 1 223204, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc40 : bv 32 := 0x22050063.
Lemma F_5dc40 : fetch_word Asan.M.loaded_segments (0x5dc90 : word) = Some W_5dc40.
Proof. vm_refl. Qed.
Lemma D_5dc40 : decode_any W_5dc40 = Some (Branch BC_EQ 10 0 544, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc44 : bv 32 := 0x00050a13.
Lemma F_5dc44 : fetch_word Asan.M.loaded_segments (0x5dc94 : word) = Some W_5dc44.
Proof. vm_refl. Qed.
Lemma D_5dc44 : decode_any W_5dc44 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc48 : bv 32 := 0x0004b503.
Lemma F_5dc48 : fetch_word Asan.M.loaded_segments (0x5dc98 : word) = Some W_5dc48.
Proof. vm_refl. Qed.
Lemma D_5dc48 : decode_any W_5dc48 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc4c : bv 32 := 0xfff50593.
Lemma F_5dc4c : fetch_word Asan.M.loaded_segments (0x5dc9c : word) = Some W_5dc4c.
Proof. vm_refl. Qed.
Lemma D_5dc4c : decode_any W_5dc4c = Some (OpImm ALU_ADD 11 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc50 : bv 32 := 0x0145f5b3.
Lemma F_5dc50 : fetch_word Asan.M.loaded_segments (0x5dca0 : word) = Some W_5dc50.
Proof. vm_refl. Qed.
Lemma D_5dc50 : decode_any W_5dc50 = Some (Op ALU_AND 11 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc54 : bv 32 := 0x26059863.
Lemma F_5dc54 : fetch_word Asan.M.loaded_segments (0x5dca4 : word) = Some W_5dc54.
Proof. vm_refl. Qed.
Lemma D_5dc54 : decode_any W_5dc54 = Some (Branch BC_NE 11 0 624, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc58 : bv 32 := 0x01490b33.
Lemma F_5dc58 : fetch_word Asan.M.loaded_segments (0x5dca8 : word) = Some W_5dc58.
Proof. vm_refl. Qed.
Lemma D_5dc58 : decode_any W_5dc58 = Some (Op ALU_ADD 22 18 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc5c : bv 32 := 0x01450533.
Lemma F_5dc5c : fetch_word Asan.M.loaded_segments (0x5dcac : word) = Some W_5dc5c.
Proof. vm_refl. Qed.
Lemma D_5dc5c : decode_any W_5dc5c = Some (Op ALU_ADD 10 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc60 : bv 32 := 0x018575b3.
Lemma F_5dc60 : fetch_word Asan.M.loaded_segments (0x5dcb0 : word) = Some W_5dc60.
Proof. vm_refl. Qed.
Lemma D_5dc60 : decode_any W_5dc60 = Some (Op ALU_AND 11 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc64 : bv 32 := 0x0015b613.
Lemma F_5dc64 : fetch_word Asan.M.loaded_segments (0x5dcb4 : word) = Some W_5dc64.
Proof. vm_refl. Qed.
Lemma D_5dc64 : decode_any W_5dc64 = Some (OpImm ALU_SLTU 12 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc68 : bv 32 := 0x40ba85b3.
Lemma F_5dc68 : fetch_word Asan.M.loaded_segments (0x5dcb8 : word) = Some W_5dc68.
Proof. vm_refl. Qed.
Lemma D_5dc68 : decode_any W_5dc68 = Some (Op ALU_SUB 11 21 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc6c : bv 32 := 0xfff60613.
Lemma F_5dc6c : fetch_word Asan.M.loaded_segments (0x5dcbc : word) = Some W_5dc6c.
Proof. vm_refl. Qed.
Lemma D_5dc6c : decode_any W_5dc6c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc70 : bv 32 := 0x00b675b3.
Lemma F_5dc70 : fetch_word Asan.M.loaded_segments (0x5dcc0 : word) = Some W_5dc70.
Proof. vm_refl. Qed.
Lemma D_5dc70 : decode_any W_5dc70 = Some (Op ALU_AND 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc74 : bv 32 := 0x00a58cb3.
Lemma F_5dc74 : fetch_word Asan.M.loaded_segments (0x5dcc4 : word) = Some W_5dc74.
Proof. vm_refl. Qed.
Lemma D_5dc74 : decode_any W_5dc74 = Some (Op ALU_ADD 25 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc78 : bv 32 := 0x013c8ab3.
Lemma F_5dc78 : fetch_word Asan.M.loaded_segments (0x5dcc8 : word) = Some W_5dc78.
Proof. vm_refl. Qed.
Lemma D_5dc78 : decode_any W_5dc78 = Some (Op ALU_ADD 21 25 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc7c : bv 32 := 0x007c8513.
Lemma F_5dc7c : fetch_word Asan.M.loaded_segments (0x5dccc : word) = Some W_5dc7c.
Proof. vm_refl. Qed.
Lemma D_5dc7c : decode_any W_5dc7c = Some (OpImm ALU_ADD 10 25 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc80 : bv 32 := 0xff8afb93.
Lemma F_5dc80 : fetch_word Asan.M.loaded_segments (0x5dcd0 : word) = Some W_5dc80.
Proof. vm_refl. Qed.
Lemma D_5dc80 : decode_any W_5dc80 = Some (OpImm ALU_AND 23 21 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc84 : bv 32 := 0xff857513.
Lemma F_5dc84 : fetch_word Asan.M.loaded_segments (0x5dcd4 : word) = Some W_5dc84.
Proof. vm_refl. Qed.
Lemma D_5dc84 : decode_any W_5dc84 = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc88 : bv 32 := 0x414505b3.
Lemma F_5dc88 : fetch_word Asan.M.loaded_segments (0x5dcd8 : word) = Some W_5dc88.
Proof. vm_refl. Qed.
Lemma D_5dc88 : decode_any W_5dc88 = Some (Op ALU_SUB 11 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc8c : bv 32 := 0x0fa00613.
Lemma F_5dc8c : fetch_word Asan.M.loaded_segments (0x5dcdc : word) = Some W_5dc8c.
Proof. vm_refl. Qed.
Lemma D_5dc8c : decode_any W_5dc8c = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc90 : bv 32 := 0x000a0513.
Lemma F_5dc90 : fetch_word Asan.M.loaded_segments (0x5dce0 : word) = Some W_5dc90.
Proof. vm_refl. Qed.
Lemma D_5dc90 : decode_any W_5dc90 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc94 : bv 32 := 0x57d230ef.
Lemma F_5dc94 : fetch_word Asan.M.loaded_segments (0x5dce4 : word) = Some W_5dc94.
Proof. vm_refl. Qed.
Lemma D_5dc94 : decode_any W_5dc94 = Some (Jal 1 146812, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc98 : bv 32 := 0x417b05b3.
Lemma F_5dc98 : fetch_word Asan.M.loaded_segments (0x5dce8 : word) = Some W_5dc98.
Proof. vm_refl. Qed.
Lemma D_5dc98 : decode_any W_5dc98 = Some (Op ALU_SUB 11 22 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc9c : bv 32 := 0x0fa00613.
Lemma F_5dc9c : fetch_word Asan.M.loaded_segments (0x5dcec : word) = Some W_5dc9c.
Proof. vm_refl. Qed.
Lemma D_5dc9c : decode_any W_5dc9c = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dca0 : bv 32 := 0x000b8513.
Lemma F_5dca0 : fetch_word Asan.M.loaded_segments (0x5dcf0 : word) = Some W_5dca0.
Proof. vm_refl. Qed.
Lemma D_5dca0 : decode_any W_5dca0 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dca4 : bv 32 := 0x56d230ef.
Lemma F_5dca4 : fetch_word Asan.M.loaded_segments (0x5dcf4 : word) = Some W_5dca4.
Proof. vm_refl. Qed.
Lemma D_5dca4 : decode_any W_5dca4 = Some (Jal 1 146796, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dca8 : bv 32 := 0x4e12b0ef.
Lemma F_5dca8 : fetch_word Asan.M.loaded_segments (0x5dcf8 : word) = Some W_5dca8.
Proof. vm_refl. Qed.
Lemma D_5dca8 : decode_any W_5dca8 = Some (Jal 1 179424, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcac : bv 32 := 0x04853603.
Lemma F_5dcac : fetch_word Asan.M.loaded_segments (0x5dcfc : word) = Some W_5dcac.
Proof. vm_refl. Qed.
Lemma D_5dcac : decode_any W_5dcac = Some (Load SZ8 true 12 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcb0 : bv 32 := 0x05053683.
Lemma F_5dcb0 : fetch_word Asan.M.loaded_segments (0x5dd00 : word) = Some W_5dcb0.
Proof. vm_refl. Qed.
Lemma D_5dcb0 : decode_any W_5dcb0 = Some (Load SZ8 true 13 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcb4 : bv 32 := 0x018cf733.
Lemma F_5dcb4 : fetch_word Asan.M.loaded_segments (0x5dd04 : word) = Some W_5dcb4.
Proof. vm_refl. Qed.
Lemma D_5dcb4 : decode_any W_5dcb4 = Some (Op ALU_AND 14 25 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcb8 : bv 32 := 0x00160613.
Lemma F_5dcb8 : fetch_word Asan.M.loaded_segments (0x5dd08 : word) = Some W_5dcb8.
Proof. vm_refl. Qed.
Lemma D_5dcb8 : decode_any W_5dcb8 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcbc : bv 32 := 0x012686b3.
Lemma F_5dcbc : fetch_word Asan.M.loaded_segments (0x5dd0c : word) = Some W_5dcbc.
Proof. vm_refl. Qed.
Lemma D_5dcbc : decode_any W_5dcbc = Some (Op ALU_ADD 13 13 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcc0 : bv 32 := 0x04c53423.
Lemma F_5dcc0 : fetch_word Asan.M.loaded_segments (0x5dd10 : word) = Some W_5dcc0.
Proof. vm_refl. Qed.
Lemma D_5dcc0 : decode_any W_5dcc0 = Some (Store SZ8 10 12 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcc4 : bv 32 := 0x04d53823.
Lemma F_5dcc4 : fetch_word Asan.M.loaded_segments (0x5dd14 : word) = Some W_5dcc4.
Proof. vm_refl. Qed.
Lemma D_5dcc4 : decode_any W_5dcc4 = Some (Store SZ8 10 13 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcc8 : bv 32 := 0x20071e63.
Lemma F_5dcc8 : fetch_word Asan.M.loaded_segments (0x5dd18 : word) = Some W_5dcc8.
Proof. vm_refl. Qed.
Lemma D_5dcc8 : decode_any W_5dcc8 = Some (Branch BC_NE 14 0 540, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dccc : bv 32 := 0x000c8513.
Lemma F_5dccc : fetch_word Asan.M.loaded_segments (0x5dd1c : word) = Some W_5dccc.
Proof. vm_refl. Qed.
Lemma D_5dccc : decode_any W_5dccc = Some (OpImm ALU_ADD 10 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcd0 : bv 32 := 0x0004b583.
Lemma F_5dcd0 : fetch_word Asan.M.loaded_segments (0x5dd20 : word) = Some W_5dcd0.
Proof. vm_refl. Qed.
Lemma D_5dcd0 : decode_any W_5dcd0 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcd4 : bv 32 := 0xfff58613.
Lemma F_5dcd4 : fetch_word Asan.M.loaded_segments (0x5dd24 : word) = Some W_5dcd4.
Proof. vm_refl. Qed.
Lemma D_5dcd4 : decode_any W_5dcd4 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcd8 : bv 32 := 0x01967633.
Lemma F_5dcd8 : fetch_word Asan.M.loaded_segments (0x5dd28 : word) = Some W_5dcd8.
Proof. vm_refl. Qed.
Lemma D_5dcd8 : decode_any W_5dcd8 = Some (Op ALU_AND 12 12 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcdc : bv 32 := 0x22061463.
Lemma F_5dcdc : fetch_word Asan.M.loaded_segments (0x5dd2c : word) = Some W_5dcdc.
Proof. vm_refl. Qed.
Lemma D_5dcdc : decode_any W_5dcdc = Some (Branch BC_NE 12 0 552, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dce0 : bv 32 := 0x254ae263.
Lemma F_5dce0 : fetch_word Asan.M.loaded_segments (0x5dd30 : word) = Some W_5dce0.
Proof. vm_refl. Qed.
Lemma D_5dce0 : decode_any W_5dce0 = Some (Branch BC_LTU 21 20 580, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dce4 : bv 32 := 0x275b6063.
Lemma F_5dce4 : fetch_word Asan.M.loaded_segments (0x5dd34 : word) = Some W_5dce4.
Proof. vm_refl. Qed.
Lemma D_5dce4 : decode_any W_5dce4 = Some (Branch BC_LTU 22 21 608, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dce8 : bv 32 := 0x40b50ab3.
Lemma F_5dce8 : fetch_word Asan.M.loaded_segments (0x5dd38 : word) = Some W_5dce8.
Proof. vm_refl. Qed.
Lemma D_5dce8 : decode_any W_5dce8 = Some (Op ALU_SUB 21 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcec : bv 32 := 0x014ab023.
Lemma F_5dcec : fetch_word Asan.M.loaded_segments (0x5dd3c : word) = Some W_5dcec.
Proof. vm_refl. Qed.
Lemma D_5dcec : decode_any W_5dcec = Some (Store SZ8 21 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcf0 : bv 32 := 0x012ab423.
Lemma F_5dcf0 : fetch_word Asan.M.loaded_segments (0x5dd40 : word) = Some W_5dcf0.
Proof. vm_refl. Qed.
Lemma D_5dcf0 : decode_any W_5dcf0 = Some (Store SZ8 21 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcf4 : bv 32 := 0x013ab823.
Lemma F_5dcf4 : fetch_word Asan.M.loaded_segments (0x5dd44 : word) = Some W_5dcf4.
Proof. vm_refl. Qed.
Lemma D_5dcf4 : decode_any W_5dcf4 = Some (Store SZ8 21 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcf8 : bv 32 := 0x26090663.
Lemma F_5dcf8 : fetch_word Asan.M.loaded_segments (0x5dd48 : word) = Some W_5dcf8.
Proof. vm_refl. Qed.
Lemma D_5dcf8 : decode_any W_5dcf8 = Some (Branch BC_EQ 18 0 620, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcfc : bv 32 := 0x26848593.
Lemma F_5dcfc : fetch_word Asan.M.loaded_segments (0x5dd4c : word) = Some W_5dcfc.
Proof. vm_refl. Qed.
Lemma D_5dcfc : decode_any W_5dcfc = Some (OpImm ALU_ADD 11 9 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd00 : bv 32 := 0x0ff00613.
Lemma F_5dd00 : fetch_word Asan.M.loaded_segments (0x5dd50 : word) = Some W_5dd00.
Proof. vm_refl. Qed.
Lemma D_5dd00 : decode_any W_5dd00 = Some (OpImm ALU_ADD 12 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd04 : bv 32 := 0xffc5f693.
Lemma F_5dd04 : fetch_word Asan.M.loaded_segments (0x5dd54 : word) = Some W_5dd04.
Proof. vm_refl. Qed.
Lemma D_5dd04 : decode_any W_5dd04 = Some (OpImm ALU_AND 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd08 : bv 32 := 0x00100713.
Lemma F_5dd08 : fetch_word Asan.M.loaded_segments (0x5dd58 : word) = Some W_5dd08.
Proof. vm_refl. Qed.
Lemma D_5dd08 : decode_any W_5dd08 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd0c : bv 32 := 0x1406a7af.
Lemma F_5dd0c : fetch_word Asan.M.loaded_segments (0x5dd5c : word) = Some W_5dd0c.
Proof. vm_refl. Qed.
Lemma D_5dd0c : decode_any W_5dd0c = Some (Lr AW true false 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd10 : bv 32 := 0x00070813.
Lemma F_5dd10 : fetch_word Asan.M.loaded_segments (0x5dd60 : word) = Some W_5dd10.
Proof. vm_refl. Qed.
Lemma D_5dd10 : decode_any W_5dd10 = Some (OpImm ALU_ADD 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd14 : bv 32 := 0x0107c833.
Lemma F_5dd14 : fetch_word Asan.M.loaded_segments (0x5dd64 : word) = Some W_5dd14.
Proof. vm_refl. Qed.
Lemma D_5dd14 : decode_any W_5dd14 = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd18 : bv 32 := 0x00c87833.
Lemma F_5dd18 : fetch_word Asan.M.loaded_segments (0x5dd68 : word) = Some W_5dd18.
Proof. vm_refl. Qed.
Lemma D_5dd18 : decode_any W_5dd18 = Some (Op ALU_AND 16 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd1c : bv 32 := 0x0107c833.
Lemma F_5dd1c : fetch_word Asan.M.loaded_segments (0x5dd6c : word) = Some W_5dd1c.
Proof. vm_refl. Qed.
Lemma D_5dd1c : decode_any W_5dd1c = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd20 : bv 32 := 0x1906a82f.
Lemma F_5dd20 : fetch_word Asan.M.loaded_segments (0x5dd70 : word) = Some W_5dd20.
Proof. vm_refl. Qed.
Lemma D_5dd20 : decode_any W_5dd20 = Some (Sc AW false false 16 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd24 : bv 32 := 0xfe0814e3.
Lemma F_5dd24 : fetch_word Asan.M.loaded_segments (0x5dd74 : word) = Some W_5dd24.
Proof. vm_refl. Qed.
Lemma D_5dd24 : decode_any W_5dd24 = Some (Branch BC_NE 16 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd28 : bv 32 := 0x0ff7f613.
Lemma F_5dd28 : fetch_word Asan.M.loaded_segments (0x5dd78 : word) = Some W_5dd28.
Proof. vm_refl. Qed.
Lemma D_5dd28 : decode_any W_5dd28 = Some (OpImm ALU_AND 12 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd2c : bv 32 := 0x24061c63.
Lemma F_5dd2c : fetch_word Asan.M.loaded_segments (0x5dd7c : word) = Some W_5dd2c.
Proof. vm_refl. Qed.
Lemma D_5dd2c : decode_any W_5dd2c = Some (Branch BC_NE 12 0 600, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd30 : bv 32 := 0x0384b683.
Lemma F_5dd30 : fetch_word Asan.M.loaded_segments (0x5dd80 : word) = Some W_5dd30.
Proof. vm_refl. Qed.
Lemma D_5dd30 : decode_any W_5dd30 = Some (Load SZ8 true 13 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd34 : bv 32 := 0x0146d593.
Lemma F_5dd34 : fetch_word Asan.M.loaded_segments (0x5dd84 : word) = Some W_5dd34.
Proof. vm_refl. Qed.
Lemma D_5dd34 : decode_any W_5dd34 = Some (ShiftImm ALU_SRL 11 13 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd38 : bv 32 := 0x26059463.
Lemma F_5dd38 : fetch_word Asan.M.loaded_segments (0x5dd88 : word) = Some W_5dd38.
Proof. vm_refl. Qed.
Lemma D_5dd38 : decode_any W_5dd38 = Some (Branch BC_NE 11 0 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd3c : bv 32 := 0x00195593.
Lemma F_5dd3c : fetch_word Asan.M.loaded_segments (0x5dd8c : word) = Some W_5dd3c.
Proof. vm_refl. Qed.
Lemma D_5dd3c : decode_any W_5dd3c = Some (ShiftImm ALU_SRL 11 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd40 : bv 32 := 0x55555637.
Lemma F_5dd40 : fetch_word Asan.M.loaded_segments (0x5dd90 : word) = Some W_5dd40.
Proof. vm_refl. Qed.
Lemma D_5dd40 : decode_any W_5dd40 = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd44 : bv 32 := 0x33333737.
Lemma F_5dd44 : fetch_word Asan.M.loaded_segments (0x5dd94 : word) = Some W_5dd44.
Proof. vm_refl. Qed.
Lemma D_5dd44 : decode_any W_5dd44 = Some (Lui 14 209715, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd48 : bv 32 := 0x0f0f17b7.
Lemma F_5dd48 : fetch_word Asan.M.loaded_segments (0x5dd98 : word) = Some W_5dd48.
Proof. vm_refl. Qed.
Lemma D_5dd48 : decode_any W_5dd48 = Some (Lui 15 61681, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd4c : bv 32 := 0x00b965b3.
Lemma F_5dd4c : fetch_word Asan.M.loaded_segments (0x5dd9c : word) = Some W_5dd4c.
Proof. vm_refl. Qed.
Lemma D_5dd4c : decode_any W_5dd4c = Some (Op ALU_OR 11 18 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd50 : bv 32 := 0x5556061b.
Lemma F_5dd50 : fetch_word Asan.M.loaded_segments (0x5dda0 : word) = Some W_5dd50.
Proof. vm_refl. Qed.
Lemma D_5dd50 : decode_any W_5dd50 = Some (OpImm32 12 12 1365, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd54 : bv 32 := 0x3337071b.
Lemma F_5dd54 : fetch_word Asan.M.loaded_segments (0x5dda4 : word) = Some W_5dd54.
Proof. vm_refl. Qed.
Lemma D_5dd54 : decode_any W_5dd54 = Some (OpImm32 14 14 819, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd58 : bv 32 := 0xf0f7879b.
Lemma F_5dd58 : fetch_word Asan.M.loaded_segments (0x5dda8 : word) = Some W_5dd58.
Proof. vm_refl. Qed.
Lemma D_5dd58 : decode_any W_5dd58 = Some (OpImm32 15 15 3855, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd5c : bv 32 := 0x0025d813.
Lemma F_5dd5c : fetch_word Asan.M.loaded_segments (0x5ddac : word) = Some W_5dd5c.
Proof. vm_refl. Qed.
Lemma D_5dd5c : decode_any W_5dd5c = Some (ShiftImm ALU_SRL 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd60 : bv 32 := 0x0105e5b3.
Lemma F_5dd60 : fetch_word Asan.M.loaded_segments (0x5ddb0 : word) = Some W_5dd60.
Proof. vm_refl. Qed.
Lemma D_5dd60 : decode_any W_5dd60 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd64 : bv 32 := 0x02061813.
Lemma F_5dd64 : fetch_word Asan.M.loaded_segments (0x5ddb4 : word) = Some W_5dd64.
Proof. vm_refl. Qed.
Lemma D_5dd64 : decode_any W_5dd64 = Some (ShiftImm ALU_SLL 16 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd68 : bv 32 := 0x01060633.
Lemma F_5dd68 : fetch_word Asan.M.loaded_segments (0x5ddb8 : word) = Some W_5dd68.
Proof. vm_refl. Qed.
Lemma D_5dd68 : decode_any W_5dd68 = Some (Op ALU_ADD 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd6c : bv 32 := 0x02071813.
Lemma F_5dd6c : fetch_word Asan.M.loaded_segments (0x5ddbc : word) = Some W_5dd6c.
Proof. vm_refl. Qed.
Lemma D_5dd6c : decode_any W_5dd6c = Some (ShiftImm ALU_SLL 16 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd70 : bv 32 := 0x01070733.
Lemma F_5dd70 : fetch_word Asan.M.loaded_segments (0x5ddc0 : word) = Some W_5dd70.
Proof. vm_refl. Qed.
Lemma D_5dd70 : decode_any W_5dd70 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd74 : bv 32 := 0x02079813.
Lemma F_5dd74 : fetch_word Asan.M.loaded_segments (0x5ddc4 : word) = Some W_5dd74.
Proof. vm_refl. Qed.
Lemma D_5dd74 : decode_any W_5dd74 = Some (ShiftImm ALU_SLL 16 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd78 : bv 32 := 0x010787b3.
Lemma F_5dd78 : fetch_word Asan.M.loaded_segments (0x5ddc8 : word) = Some W_5dd78.
Proof. vm_refl. Qed.
Lemma D_5dd78 : decode_any W_5dd78 = Some (Op ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd7c : bv 32 := 0x0045d813.
Lemma F_5dd7c : fetch_word Asan.M.loaded_segments (0x5ddcc : word) = Some W_5dd7c.
Proof. vm_refl. Qed.
Lemma D_5dd7c : decode_any W_5dd7c = Some (ShiftImm ALU_SRL 16 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd80 : bv 32 := 0x0105e5b3.
Lemma F_5dd80 : fetch_word Asan.M.loaded_segments (0x5ddd0 : word) = Some W_5dd80.
Proof. vm_refl. Qed.
Lemma D_5dd80 : decode_any W_5dd80 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd84 : bv 32 := 0x0085d813.
Lemma F_5dd84 : fetch_word Asan.M.loaded_segments (0x5ddd4 : word) = Some W_5dd84.
Proof. vm_refl. Qed.
Lemma D_5dd84 : decode_any W_5dd84 = Some (ShiftImm ALU_SRL 16 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd88 : bv 32 := 0x0105e5b3.
Lemma F_5dd88 : fetch_word Asan.M.loaded_segments (0x5ddd8 : word) = Some W_5dd88.
Proof. vm_refl. Qed.
Lemma D_5dd88 : decode_any W_5dd88 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd8c : bv 32 := 0x0105d813.
Lemma F_5dd8c : fetch_word Asan.M.loaded_segments (0x5dddc : word) = Some W_5dd8c.
Proof. vm_refl. Qed.
Lemma D_5dd8c : decode_any W_5dd8c = Some (ShiftImm ALU_SRL 16 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd90 : bv 32 := 0x0105e5b3.
Lemma F_5dd90 : fetch_word Asan.M.loaded_segments (0x5dde0 : word) = Some W_5dd90.
Proof. vm_refl. Qed.
Lemma D_5dd90 : decode_any W_5dd90 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd94 : bv 32 := 0x0205d813.
Lemma F_5dd94 : fetch_word Asan.M.loaded_segments (0x5dde4 : word) = Some W_5dd94.
Proof. vm_refl. Qed.
Lemma D_5dd94 : decode_any W_5dd94 = Some (ShiftImm ALU_SRL 16 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd98 : bv 32 := 0x0105e5b3.
Lemma F_5dd98 : fetch_word Asan.M.loaded_segments (0x5dde8 : word) = Some W_5dd98.
Proof. vm_refl. Qed.
Lemma D_5dd98 : decode_any W_5dd98 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dd9c : bv 32 := 0xfff5c593.
Lemma F_5dd9c : fetch_word Asan.M.loaded_segments (0x5ddec : word) = Some W_5dd9c.
Proof. vm_refl. Qed.
Lemma D_5dd9c : decode_any W_5dd9c = Some (OpImm ALU_XOR 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dda0 : bv 32 := 0x0015d813.
Lemma F_5dda0 : fetch_word Asan.M.loaded_segments (0x5ddf0 : word) = Some W_5dda0.
Proof. vm_refl. Qed.
Lemma D_5dda0 : decode_any W_5dda0 = Some (ShiftImm ALU_SRL 16 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dda4 : bv 32 := 0x00c87633.
Lemma F_5dda4 : fetch_word Asan.M.loaded_segments (0x5ddf4 : word) = Some W_5dda4.
Proof. vm_refl. Qed.
Lemma D_5dda4 : decode_any W_5dda4 = Some (Op ALU_AND 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dda8 : bv 32 := 0x01010837.
Lemma F_5dda8 : fetch_word Asan.M.loaded_segments (0x5ddf8 : word) = Some W_5dda8.
Proof. vm_refl. Qed.
Lemma D_5dda8 : decode_any W_5dda8 = Some (Lui 16 4112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddac : bv 32 := 0x40c585b3.
Lemma F_5ddac : fetch_word Asan.M.loaded_segments (0x5ddfc : word) = Some W_5ddac.
Proof. vm_refl. Qed.
Lemma D_5ddac : decode_any W_5ddac = Some (Op ALU_SUB 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddb0 : bv 32 := 0x0025d613.
Lemma F_5ddb0 : fetch_word Asan.M.loaded_segments (0x5de00 : word) = Some W_5ddb0.
Proof. vm_refl. Qed.
Lemma D_5ddb0 : decode_any W_5ddb0 = Some (ShiftImm ALU_SRL 12 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddb4 : bv 32 := 0x00e5f5b3.
Lemma F_5ddb4 : fetch_word Asan.M.loaded_segments (0x5de04 : word) = Some W_5ddb4.
Proof. vm_refl. Qed.
Lemma D_5ddb4 : decode_any W_5ddb4 = Some (Op ALU_AND 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddb8 : bv 32 := 0x00e67633.
Lemma F_5ddb8 : fetch_word Asan.M.loaded_segments (0x5de08 : word) = Some W_5ddb8.
Proof. vm_refl. Qed.
Lemma D_5ddb8 : decode_any W_5ddb8 = Some (Op ALU_AND 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddbc : bv 32 := 0x0304b703.
Lemma F_5ddbc : fetch_word Asan.M.loaded_segments (0x5de0c : word) = Some W_5ddbc.
Proof. vm_refl. Qed.
Lemma D_5ddbc : decode_any W_5ddbc = Some (Load SZ8 true 14 9 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddc0 : bv 32 := 0x1018081b.
Lemma F_5ddc0 : fetch_word Asan.M.loaded_segments (0x5de10 : word) = Some W_5ddc0.
Proof. vm_refl. Qed.
Lemma D_5ddc0 : decode_any W_5ddc0 = Some (OpImm32 16 16 257, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddc4 : bv 32 := 0x00c585b3.
Lemma F_5ddc4 : fetch_word Asan.M.loaded_segments (0x5de14 : word) = Some W_5ddc4.
Proof. vm_refl. Qed.
Lemma D_5ddc4 : decode_any W_5ddc4 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddc8 : bv 32 := 0x0045d613.
Lemma F_5ddc8 : fetch_word Asan.M.loaded_segments (0x5de18 : word) = Some W_5ddc8.
Proof. vm_refl. Qed.
Lemma D_5ddc8 : decode_any W_5ddc8 = Some (ShiftImm ALU_SRL 12 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddcc : bv 32 := 0x00c585b3.
Lemma F_5ddcc : fetch_word Asan.M.loaded_segments (0x5de1c : word) = Some W_5ddcc.
Proof. vm_refl. Qed.
Lemma D_5ddcc : decode_any W_5ddcc = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddd0 : bv 32 := 0x02081613.
Lemma F_5ddd0 : fetch_word Asan.M.loaded_segments (0x5de20 : word) = Some W_5ddd0.
Proof. vm_refl. Qed.
Lemma D_5ddd0 : decode_any W_5ddd0 = Some (ShiftImm ALU_SLL 12 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddd4 : bv 32 := 0x00f5f5b3.
Lemma F_5ddd4 : fetch_word Asan.M.loaded_segments (0x5de24 : word) = Some W_5ddd4.
Proof. vm_refl. Qed.
Lemma D_5ddd4 : decode_any W_5ddd4 = Some (Op ALU_AND 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddd8 : bv 32 := 0x00c80633.
Lemma F_5ddd8 : fetch_word Asan.M.loaded_segments (0x5de28 : word) = Some W_5ddd8.
Proof. vm_refl. Qed.
Lemma D_5ddd8 : decode_any W_5ddd8 = Some (Op ALU_ADD 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dddc : bv 32 := 0x02c585b3.
Lemma F_5dddc : fetch_word Asan.M.loaded_segments (0x5de2c : word) = Some W_5dddc.
Proof. vm_refl. Qed.
Lemma D_5dddc : decode_any W_5dddc = Some (Mul M_MUL 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dde0 : bv 32 := 0x0385d993.
Lemma F_5dde0 : fetch_word Asan.M.loaded_segments (0x5de30 : word) = Some W_5dde0.
Proof. vm_refl. Qed.
Lemma D_5dde0 : decode_any W_5dde0 = Some (ShiftImm ALU_SRL 19 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dde4 : bv 32 := 0x1ce68c63.
Lemma F_5dde4 : fetch_word Asan.M.loaded_segments (0x5de34 : word) = Some W_5dde4.
Proof. vm_refl. Qed.
Lemma D_5dde4 : decode_any W_5dde4 = Some (Branch BC_EQ 13 14 472, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dde8 : bv 32 := 0x0084b603.
Lemma F_5dde8 : fetch_word Asan.M.loaded_segments (0x5de38 : word) = Some W_5dde8.
Proof. vm_refl. Qed.
Lemma D_5dde8 : decode_any W_5dde8 = Some (Load SZ8 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddec : bv 32 := 0x03f9c593.
Lemma F_5ddec : fetch_word Asan.M.loaded_segments (0x5de3c : word) = Some W_5ddec.
Proof. vm_refl. Qed.
Lemma D_5ddec : decode_any W_5ddec = Some (OpImm ALU_XOR 11 19 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddf0 : bv 32 := 0x00dabc23.
Lemma F_5ddf0 : fetch_word Asan.M.loaded_segments (0x5de40 : word) = Some W_5ddf0.
Proof. vm_refl. Qed.
Lemma D_5ddf0 : decode_any W_5ddf0 = Some (Store SZ8 21 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddf4 : bv 32 := 0x00369713.
Lemma F_5ddf4 : fetch_word Asan.M.loaded_segments (0x5de44 : word) = Some W_5ddf4.
Proof. vm_refl. Qed.
Lemma D_5ddf4 : decode_any W_5ddf4 = Some (ShiftImm ALU_SLL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddf8 : bv 32 := 0x00e60633.
Lemma F_5ddf8 : fetch_word Asan.M.loaded_segments (0x5de48 : word) = Some W_5ddf8.
Proof. vm_refl. Qed.
Lemma D_5ddf8 : decode_any W_5ddf8 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ddfc : bv 32 := 0x01563023.
Lemma F_5ddfc : fetch_word Asan.M.loaded_segments (0x5de4c : word) = Some W_5ddfc.
Proof. vm_refl. Qed.
Lemma D_5ddfc : decode_any W_5ddfc = Some (Store SZ8 12 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de00 : bv 32 := 0x0484b703.
Lemma F_5de00 : fetch_word Asan.M.loaded_segments (0x5de50 : word) = Some W_5de00.
Proof. vm_refl. Qed.
Lemma D_5de00 : decode_any W_5de00 = Some (Load SZ8 true 14 9 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de04 : bv 32 := 0x0584b783.
Lemma F_5de04 : fetch_word Asan.M.loaded_segments (0x5de54 : word) = Some W_5de04.
Proof. vm_refl. Qed.
Lemma D_5de04 : decode_any W_5de04 = Some (Load SZ8 true 15 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de08 : bv 32 := 0x00168813.
Lemma F_5de08 : fetch_word Asan.M.loaded_segments (0x5de58 : word) = Some W_5de08.
Proof. vm_refl. Qed.
Lemma D_5de08 : decode_any W_5de08 = Some (OpImm ALU_ADD 16 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de0c : bv 32 := 0x0604b603.
Lemma F_5de0c : fetch_word Asan.M.loaded_segments (0x5de5c : word) = Some W_5de0c.
Proof. vm_refl. Qed.
Lemma D_5de0c : decode_any W_5de0c = Some (Load SZ8 true 12 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de10 : bv 32 := 0x00170713.
Lemma F_5de10 : fetch_word Asan.M.loaded_segments (0x5de60 : word) = Some W_5de10.
Proof. vm_refl. Qed.
Lemma D_5de10 : decode_any W_5de10 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de14 : bv 32 := 0x012786b3.
Lemma F_5de14 : fetch_word Asan.M.loaded_segments (0x5de64 : word) = Some W_5de14.
Proof. vm_refl. Qed.
Lemma D_5de14 : decode_any W_5de14 = Some (Op ALU_ADD 13 15 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de18 : bv 32 := 0x0304bc23.
Lemma F_5de18 : fetch_word Asan.M.loaded_segments (0x5de68 : word) = Some W_5de18.
Proof. vm_refl. Qed.
Lemma D_5de18 : decode_any W_5de18 = Some (Store SZ8 9 16 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de1c : bv 32 := 0x04048023.
Lemma F_5de1c : fetch_word Asan.M.loaded_segments (0x5de6c : word) = Some W_5de1c.
Proof. vm_refl. Qed.
Lemma D_5de1c : decode_any W_5de1c = Some (Store SZ1 9 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de20 : bv 32 := 0x04e4b423.
Lemma F_5de20 : fetch_word Asan.M.loaded_segments (0x5de70 : word) = Some W_5de20.
Proof. vm_refl. Qed.
Lemma D_5de20 : decode_any W_5de20 = Some (Store SZ8 9 14 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de24 : bv 32 := 0x04d4bc23.
Lemma F_5de24 : fetch_word Asan.M.loaded_segments (0x5de74 : word) = Some W_5de24.
Proof. vm_refl. Qed.
Lemma D_5de24 : decode_any W_5de24 = Some (Store SZ8 9 13 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de28 : bv 32 := 0x00c6e463.
Lemma F_5de28 : fetch_word Asan.M.loaded_segments (0x5de78 : word) = Some W_5de28.
Proof. vm_refl. Qed.
Lemma D_5de28 : decode_any W_5de28 = Some (Branch BC_LTU 13 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de2c : bv 32 := 0x00068613.
Lemma F_5de2c : fetch_word Asan.M.loaded_segments (0x5de7c : word) = Some W_5de2c.
Proof. vm_refl. Qed.
Lemma D_5de2c : decode_any W_5de2c = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de30 : bv 32 := 0x00359593.
Lemma F_5de30 : fetch_word Asan.M.loaded_segments (0x5de80 : word) = Some W_5de30.
Proof. vm_refl. Qed.
Lemma D_5de30 : decode_any W_5de30 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de34 : bv 32 := 0x00b485b3.
Lemma F_5de34 : fetch_word Asan.M.loaded_segments (0x5de84 : word) = Some W_5de34.
Proof. vm_refl. Qed.
Lemma D_5de34 : decode_any W_5de34 = Some (Op ALU_ADD 11 9 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de38 : bv 32 := 0x0685b683.
Lemma F_5de38 : fetch_word Asan.M.loaded_segments (0x5de88 : word) = Some W_5de38.
Proof. vm_refl. Qed.
Lemma D_5de38 : decode_any W_5de38 = Some (Load SZ8 true 13 11 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de3c : bv 32 := 0x00168693.
Lemma F_5de3c : fetch_word Asan.M.loaded_segments (0x5de8c : word) = Some W_5de3c.
Proof. vm_refl. Qed.
Lemma D_5de3c : decode_any W_5de3c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de40 : bv 32 := 0x06c4b023.
Lemma F_5de40 : fetch_word Asan.M.loaded_segments (0x5de90 : word) = Some W_5de40.
Proof. vm_refl. Qed.
Lemma D_5de40 : decode_any W_5de40 = Some (Store SZ8 9 12 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de44 : bv 32 := 0x06d5b423.
Lemma F_5de44 : fetch_word Asan.M.loaded_segments (0x5de94 : word) = Some W_5de44.
Proof. vm_refl. Qed.
Lemma D_5de44 : decode_any W_5de44 = Some (Store SZ8 11 13 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de48 : bv 32 := 0x01040593.
Lemma F_5de48 : fetch_word Asan.M.loaded_segments (0x5de98 : word) = Some W_5de48.
Proof. vm_refl. Qed.
Lemma D_5de48 : decode_any W_5de48 = Some (OpImm ALU_ADD 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de4c : bv 32 := 0x0125b02f.
Lemma F_5de4c : fetch_word Asan.M.loaded_segments (0x5de9c : word) = Some W_5de4c.
Proof. vm_refl. Qed.
Lemma D_5de4c : decode_any W_5de4c = Some (Amo AMO_ADD AD false false 0 11 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de50 : bv 32 := 0x01840413.
Lemma F_5de50 : fetch_word Asan.M.loaded_segments (0x5dea0 : word) = Some W_5de50.
Proof. vm_refl. Qed.
Lemma D_5de50 : decode_any W_5de50 = Some (OpImm ALU_ADD 8 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de54 : bv 32 := 0x0124302f.
Lemma F_5de54 : fetch_word Asan.M.loaded_segments (0x5dea4 : word) = Some W_5de54.
Proof. vm_refl. Qed.
Lemma D_5de54 : decode_any W_5de54 = Some (Amo AMO_ADD AD false false 0 8 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de58 : bv 32 := 0x0310000f.
Lemma F_5de58 : fetch_word Asan.M.loaded_segments (0x5dea8 : word) = Some W_5de58.
Proof. vm_refl. Qed.
Lemma D_5de58 : decode_any W_5de58 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de5c : bv 32 := 0x26048423.
Lemma F_5de5c : fetch_word Asan.M.loaded_segments (0x5deac : word) = Some W_5de5c.
Proof. vm_refl. Qed.
Lemma D_5de5c : decode_any W_5de5c = Some (Store SZ1 9 0 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de60 : bv 32 := 0x05813083.
Lemma F_5de60 : fetch_word Asan.M.loaded_segments (0x5deb0 : word) = Some W_5de60.
Proof. vm_refl. Qed.
Lemma D_5de60 : decode_any W_5de60 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de64 : bv 32 := 0x05013403.
Lemma F_5de64 : fetch_word Asan.M.loaded_segments (0x5deb4 : word) = Some W_5de64.
Proof. vm_refl. Qed.
Lemma D_5de64 : decode_any W_5de64 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de68 : bv 32 := 0x04813483.
Lemma F_5de68 : fetch_word Asan.M.loaded_segments (0x5deb8 : word) = Some W_5de68.
Proof. vm_refl. Qed.
Lemma D_5de68 : decode_any W_5de68 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de6c : bv 32 := 0x04013903.
Lemma F_5de6c : fetch_word Asan.M.loaded_segments (0x5debc : word) = Some W_5de6c.
Proof. vm_refl. Qed.
Lemma D_5de6c : decode_any W_5de6c = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de70 : bv 32 := 0x03813983.
Lemma F_5de70 : fetch_word Asan.M.loaded_segments (0x5dec0 : word) = Some W_5de70.
Proof. vm_refl. Qed.
Lemma D_5de70 : decode_any W_5de70 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de74 : bv 32 := 0x03013a03.
Lemma F_5de74 : fetch_word Asan.M.loaded_segments (0x5dec4 : word) = Some W_5de74.
Proof. vm_refl. Qed.
Lemma D_5de74 : decode_any W_5de74 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de78 : bv 32 := 0x02813a83.
Lemma F_5de78 : fetch_word Asan.M.loaded_segments (0x5dec8 : word) = Some W_5de78.
Proof. vm_refl. Qed.
Lemma D_5de78 : decode_any W_5de78 = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de7c : bv 32 := 0x02013b03.
Lemma F_5de7c : fetch_word Asan.M.loaded_segments (0x5decc : word) = Some W_5de7c.
Proof. vm_refl. Qed.
Lemma D_5de7c : decode_any W_5de7c = Some (Load SZ8 true 22 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de80 : bv 32 := 0x01813b83.
Lemma F_5de80 : fetch_word Asan.M.loaded_segments (0x5ded0 : word) = Some W_5de80.
Proof. vm_refl. Qed.
Lemma D_5de80 : decode_any W_5de80 = Some (Load SZ8 true 23 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de84 : bv 32 := 0x01013c03.
Lemma F_5de84 : fetch_word Asan.M.loaded_segments (0x5ded4 : word) = Some W_5de84.
Proof. vm_refl. Qed.
Lemma D_5de84 : decode_any W_5de84 = Some (Load SZ8 true 24 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de88 : bv 32 := 0x00813c83.
Lemma F_5de88 : fetch_word Asan.M.loaded_segments (0x5ded8 : word) = Some W_5de88.
Proof. vm_refl. Qed.
Lemma D_5de88 : decode_any W_5de88 = Some (Load SZ8 true 25 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de8c : bv 32 := 0x06010113.
Lemma F_5de8c : fetch_word Asan.M.loaded_segments (0x5dedc : word) = Some W_5de8c.
Proof. vm_refl. Qed.
Lemma D_5de8c : decode_any W_5de8c = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5de90 : bv 32 := 0x00008067.
Lemma F_5de90 : fetch_word Asan.M.loaded_segments (0x5dee0 : word) = Some W_5de90.
Proof. vm_refl. Qed.
Lemma D_5de90 : decode_any W_5de90 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfbc : bv 32 := 0x0104b583.
Lemma F_5dfbc : fetch_word Asan.M.loaded_segments (0x5e00c : word) = Some W_5dfbc.
Proof. vm_refl. Qed.
Lemma D_5dfbc : decode_any W_5dfbc = Some (Load SZ8 true 11 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfc0 : bv 32 := 0x01048713.
Lemma F_5dfc0 : fetch_word Asan.M.loaded_segments (0x5e010 : word) = Some W_5dfc0.
Proof. vm_refl. Qed.
Lemma D_5dfc0 : decode_any W_5dfc0 = Some (OpImm ALU_ADD 14 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfc4 : bv 32 := 0x00369693.
Lemma F_5dfc4 : fetch_word Asan.M.loaded_segments (0x5e014 : word) = Some W_5dfc4.
Proof. vm_refl. Qed.
Lemma D_5dfc4 : decode_any W_5dfc4 = Some (ShiftImm ALU_SLL 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfc8 : bv 32 := 0x00b685b3.
Lemma F_5dfc8 : fetch_word Asan.M.loaded_segments (0x5e018 : word) = Some W_5dfc8.
Proof. vm_refl. Qed.
Lemma D_5dfc8 : decode_any W_5dfc8 = Some (Op ALU_ADD 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfcc : bv 32 := 0x00020637.
Lemma F_5dfcc : fetch_word Asan.M.loaded_segments (0x5e01c : word) = Some W_5dfcc.
Proof. vm_refl. Qed.
Lemma D_5dfcc : decode_any W_5dfcc = Some (Lui 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfd0 : bv 32 := 0x00050a13.
Lemma F_5dfd0 : fetch_word Asan.M.loaded_segments (0x5e020 : word) = Some W_5dfd0.
Proof. vm_refl. Qed.
Lemma D_5dfd0 : decode_any W_5dfd0 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfd4 : bv 32 := 0x00070513.
Lemma F_5dfd4 : fetch_word Asan.M.loaded_segments (0x5e024 : word) = Some W_5dfd4.
Proof. vm_refl. Qed.
Lemma D_5dfd4 : decode_any W_5dfd4 = Some (OpImm ALU_ADD 10 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfd8 : bv 32 := 0x00000693.
Lemma F_5dfd8 : fetch_word Asan.M.loaded_segments (0x5e028 : word) = Some W_5dfd8.
Proof. vm_refl. Qed.
Lemma D_5dfd8 : decode_any W_5dfd8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfdc : bv 32 := 0x4153e0ef.
Lemma F_5dfdc : fetch_word Asan.M.loaded_segments (0x5e02c : word) = Some W_5dfdc.
Proof. vm_refl. Qed.
Lemma D_5dfdc : decode_any W_5dfdc = Some (Jal 1 257044, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfe0 : bv 32 := 0x000a0513.
Lemma F_5dfe0 : fetch_word Asan.M.loaded_segments (0x5e030 : word) = Some W_5dfe0.
Proof. vm_refl. Qed.
Lemma D_5dfe0 : decode_any W_5dfe0 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfe4 : bv 32 := 0x0304b583.
Lemma F_5dfe4 : fetch_word Asan.M.loaded_segments (0x5e034 : word) = Some W_5dfe4.
Proof. vm_refl. Qed.
Lemma D_5dfe4 : decode_any W_5dfe4 = Some (Load SZ8 true 11 9 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfe8 : bv 32 := 0x0384b683.
Lemma F_5dfe8 : fetch_word Asan.M.loaded_segments (0x5e038 : word) = Some W_5dfe8.
Proof. vm_refl. Qed.
Lemma D_5dfe8 : decode_any W_5dfe8 = Some (Load SZ8 true 13 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dfec : bv 32 := 0x00004637.
Lemma F_5dfec : fetch_word Asan.M.loaded_segments (0x5e03c : word) = Some W_5dfec.
Proof. vm_refl. Qed.
Lemma D_5dfec : decode_any W_5dfec = Some (Lui 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dff0 : bv 32 := 0x00c585b3.
Lemma F_5dff0 : fetch_word Asan.M.loaded_segments (0x5e040 : word) = Some W_5dff0.
Proof. vm_refl. Qed.
Lemma D_5dff0 : decode_any W_5dff0 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dff4 : bv 32 := 0x02b4b823.
Lemma F_5dff4 : fetch_word Asan.M.loaded_segments (0x5e044 : word) = Some W_5dff4.
Proof. vm_refl. Qed.
Lemma D_5dff4 : decode_any W_5dff4 = Some (Store SZ8 9 11 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dff8 : bv 32 := 0xdf1ff06f.
Lemma F_5dff8 : fetch_word Asan.M.loaded_segments (0x5e048 : word) = Some W_5dff8.
Proof. vm_refl. Qed.
Lemma D_5dff8 : decode_any W_5dff8 = Some (Jal 0 2096624, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dffc : bv 32 := 0xfe010113.
Lemma F_5dffc : fetch_word Asan.M.loaded_segments (0x5e04c : word) = Some W_5dffc.
Proof. vm_refl. Qed.
Lemma D_5dffc : decode_any W_5dffc = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e000 : bv 32 := 0x00113c23.
Lemma F_5e000 : fetch_word Asan.M.loaded_segments (0x5e050 : word) = Some W_5e000.
Proof. vm_refl. Qed.
Lemma D_5e000 : decode_any W_5e000 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e004 : bv 32 := 0x00813823.
Lemma F_5e004 : fetch_word Asan.M.loaded_segments (0x5e054 : word) = Some W_5e004.
Proof. vm_refl. Qed.
Lemma D_5e004 : decode_any W_5e004 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e008 : bv 32 := 0x00913423.
Lemma F_5e008 : fetch_word Asan.M.loaded_segments (0x5e058 : word) = Some W_5e008.
Proof. vm_refl. Qed.
Lemma D_5e008 : decode_any W_5e008 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e00c : bv 32 := 0x00068713.
Lemma F_5e00c : fetch_word Asan.M.loaded_segments (0x5e05c : word) = Some W_5e00c.
Proof. vm_refl. Qed.
Lemma D_5e00c : decode_any W_5e00c = Some (OpImm ALU_ADD 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e010 : bv 32 := 0x00058413.
Lemma F_5e010 : fetch_word Asan.M.loaded_segments (0x5e060 : word) = Some W_5e010.
Proof. vm_refl. Qed.
Lemma D_5e010 : decode_any W_5e010 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e014 : bv 32 := 0x0045a583.
Lemma F_5e014 : fetch_word Asan.M.loaded_segments (0x5e064 : word) = Some W_5e014.
Proof. vm_refl. Qed.
Lemma D_5e014 : decode_any W_5e014 = Some (Load SZ4 true 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e018 : bv 32 := 0x04058063.
Lemma F_5e018 : fetch_word Asan.M.loaded_segments (0x5e068 : word) = Some W_5e018.
Proof. vm_refl. Qed.
Lemma D_5e018 : decode_any W_5e018 = Some (Branch BC_EQ 11 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e01c : bv 32 := 0x0015d49b.
Lemma F_5e01c : fetch_word Asan.M.loaded_segments (0x5e06c : word) = Some W_5e01c.
Proof. vm_refl. Qed.
Lemma D_5e01c : decode_any W_5e01c = Some (ShiftImm32 ALU_SRL 9 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e020 : bv 32 := 0x7ff50513.
Lemma F_5e020 : fetch_word Asan.M.loaded_segments (0x5e070 : word) = Some W_5e020.
Proof. vm_refl. Qed.
Lemma D_5e020 : decode_any W_5e020 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e024 : bv 32 := 0x20150593.
Lemma F_5e024 : fetch_word Asan.M.loaded_segments (0x5e074 : word) = Some W_5e024.
Proof. vm_refl. Qed.
Lemma D_5e024 : decode_any W_5e024 = Some (OpImm ALU_ADD 11 10 513, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e028 : bv 32 := 0x01040693.
Lemma F_5e028 : fetch_word Asan.M.loaded_segments (0x5e078 : word) = Some W_5e028.
Proof. vm_refl. Qed.
Lemma D_5e028 : decode_any W_5e028 = Some (OpImm ALU_ADD 13 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e02c : bv 32 := 0x00060513.
Lemma F_5e02c : fetch_word Asan.M.loaded_segments (0x5e07c : word) = Some W_5e02c.
Proof. vm_refl. Qed.
Lemma D_5e02c : decode_any W_5e02c = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e030 : bv 32 := 0x00070613.
Lemma F_5e030 : fetch_word Asan.M.loaded_segments (0x5e080 : word) = Some W_5e030.
Proof. vm_refl. Qed.
Lemma D_5e030 : decode_any W_5e030 = Some (OpImm ALU_ADD 12 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e034 : bv 32 := 0x00048713.
Lemma F_5e034 : fetch_word Asan.M.loaded_segments (0x5e084 : word) = Some W_5e034.
Proof. vm_refl. Qed.
Lemma D_5e034 : decode_any W_5e034 = Some (OpImm ALU_ADD 14 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e038 : bv 32 := 0x0c4000ef.
Lemma F_5e038 : fetch_word Asan.M.loaded_segments (0x5e088 : word) = Some W_5e038.
Proof. vm_refl. Qed.
Lemma D_5e038 : decode_any W_5e038 = Some (Jal 1 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e03c : bv 32 := 0x00050463.
Lemma F_5e03c : fetch_word Asan.M.loaded_segments (0x5e08c : word) = Some W_5e03c.
Proof. vm_refl. Qed.
Lemma D_5e03c : decode_any W_5e03c = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e040 : bv 32 := 0x00942023.
Lemma F_5e040 : fetch_word Asan.M.loaded_segments (0x5e090 : word) = Some W_5e040.
Proof. vm_refl. Qed.
Lemma D_5e040 : decode_any W_5e040 = Some (Store SZ4 8 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e044 : bv 32 := 0x01813083.
Lemma F_5e044 : fetch_word Asan.M.loaded_segments (0x5e094 : word) = Some W_5e044.
Proof. vm_refl. Qed.
Lemma D_5e044 : decode_any W_5e044 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e048 : bv 32 := 0x01013403.
Lemma F_5e048 : fetch_word Asan.M.loaded_segments (0x5e098 : word) = Some W_5e048.
Proof. vm_refl. Qed.
Lemma D_5e048 : decode_any W_5e048 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e04c : bv 32 := 0x00813483.
Lemma F_5e04c : fetch_word Asan.M.loaded_segments (0x5e09c : word) = Some W_5e04c.
Proof. vm_refl. Qed.
Lemma D_5e04c : decode_any W_5e04c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e050 : bv 32 := 0x02010113.
Lemma F_5e050 : fetch_word Asan.M.loaded_segments (0x5e0a0 : word) = Some W_5e050.
Proof. vm_refl. Qed.
Lemma D_5e050 : decode_any W_5e050 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e054 : bv 32 := 0x00008067.
Lemma F_5e054 : fetch_word Asan.M.loaded_segments (0x5e0a4 : word) = Some W_5e054.
Proof. vm_refl. Qed.
Lemma D_5e054 : decode_any W_5e054 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e058 : bv 32 := 0x05850593.
Lemma F_5e058 : fetch_word Asan.M.loaded_segments (0x5e0a8 : word) = Some W_5e058.
Proof. vm_refl. Qed.
Lemma D_5e058 : decode_any W_5e058 = Some (OpImm ALU_ADD 11 10 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e05c : bv 32 := 0x02000693.
Lemma F_5e05c : fetch_word Asan.M.loaded_segments (0x5e0ac : word) = Some W_5e05c.
Proof. vm_refl. Qed.
Lemma D_5e05c : decode_any W_5e05c = Some (OpImm ALU_ADD 13 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e060 : bv 32 := 0xff100793.
Lemma F_5e060 : fetch_word Asan.M.loaded_segments (0x5e0b0 : word) = Some W_5e060.
Proof. vm_refl. Qed.
Lemma D_5e060 : decode_any W_5e060 = Some (OpImm ALU_ADD 15 0 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e064 : bv 32 := 0x00f00813.
Lemma F_5e064 : fetch_word Asan.M.loaded_segments (0x5e0b4 : word) = Some W_5e064.
Proof. vm_refl. Qed.
Lemma D_5e064 : decode_any W_5e064 = Some (OpImm ALU_ADD 16 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e068 : bv 32 := 0x40000893.
Lemma F_5e068 : fetch_word Asan.M.loaded_segments (0x5e0b8 : word) = Some W_5e068.
Proof. vm_refl. Qed.
Lemma D_5e068 : decode_any W_5e068 = Some (OpImm ALU_ADD 17 0 1024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e06c : bv 32 := 0x01000293.
Lemma F_5e06c : fetch_word Asan.M.loaded_segments (0x5e0bc : word) = Some W_5e06c.
Proof. vm_refl. Qed.
Lemma D_5e06c : decode_any W_5e06c = Some (OpImm ALU_ADD 5 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e070 : bv 32 := 0x01100313.
Lemma F_5e070 : fetch_word Asan.M.loaded_segments (0x5e0c0 : word) = Some W_5e070.
Proof. vm_refl. Qed.
Lemma D_5e070 : decode_any W_5e070 = Some (OpImm ALU_ADD 6 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e074 : bv 32 := 0x20000393.
Lemma F_5e074 : fetch_word Asan.M.loaded_segments (0x5e0c4 : word) = Some W_5e074.
Proof. vm_refl. Qed.
Lemma D_5e074 : decode_any W_5e074 = Some (OpImm ALU_ADD 7 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e078 : bv 32 := 0x0280006f.
Lemma F_5e078 : fetch_word Asan.M.loaded_segments (0x5e0c8 : word) = Some W_5e078.
Proof. vm_refl. Qed.
Lemma D_5e078 : decode_any W_5e078 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e07c : bv 32 := 0x001ebf13.
Lemma F_5e07c : fetch_word Asan.M.loaded_segments (0x5e0cc : word) = Some W_5e07c.
Proof. vm_refl. Qed.
Lemma D_5e07c : decode_any W_5e07c = Some (OpImm ALU_SLTU 30 29 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e080 : bv 32 := 0x02068693.
Lemma F_5e080 : fetch_word Asan.M.loaded_segments (0x5e0d0 : word) = Some W_5e080.
Proof. vm_refl. Qed.
Lemma D_5e080 : decode_any W_5e080 = Some (OpImm ALU_ADD 13 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e084 : bv 32 := 0x00178793.
Lemma F_5e084 : fetch_word Asan.M.loaded_segments (0x5e0d4 : word) = Some W_5e084.
Proof. vm_refl. Qed.
Lemma D_5e084 : decode_any W_5e084 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e088 : bv 32 := 0x01ee8eb3.
Lemma F_5e088 : fetch_word Asan.M.loaded_segments (0x5e0d8 : word) = Some W_5e088.
Proof. vm_refl. Qed.
Lemma D_5e088 : decode_any W_5e088 = Some (Op ALU_ADD 29 29 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e08c : bv 32 := 0x001e9e93.
Lemma F_5e08c : fetch_word Asan.M.loaded_segments (0x5e0dc : word) = Some W_5e08c.
Proof. vm_refl. Qed.
Lemma D_5e08c : decode_any W_5e08c = Some (ShiftImm ALU_SLL 29 29 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e090 : bv 32 := 0xffd5ae23.
Lemma F_5e090 : fetch_word Asan.M.loaded_segments (0x5e0e0 : word) = Some W_5e090.
Proof. vm_refl. Qed.
Lemma D_5e090 : decode_any W_5e090 = Some (Store SZ4 11 29 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e094 : bv 32 := 0x01c5b023.
Lemma F_5e094 : fetch_word Asan.M.loaded_segments (0x5e0e4 : word) = Some W_5e094.
Proof. vm_refl. Qed.
Lemma D_5e094 : decode_any W_5e094 = Some (Store SZ8 11 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e098 : bv 32 := 0x05058593.
Lemma F_5e098 : fetch_word Asan.M.loaded_segments (0x5e0e8 : word) = Some W_5e098.
Proof. vm_refl. Qed.
Lemma D_5e098 : decode_any W_5e098 = Some (OpImm ALU_ADD 11 11 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e09c : bv 32 := 0x04578c63.
Lemma F_5e09c : fetch_word Asan.M.loaded_segments (0x5e0ec : word) = Some W_5e09c.
Proof. vm_refl. Qed.
Lemma D_5e09c : decode_any W_5e09c = Some (Branch BC_EQ 15 5 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0a0 : bv 32 := 0x05078063.
Lemma F_5e0a0 : fetch_word Asan.M.loaded_segments (0x5e0f0 : word) = Some W_5e0a0.
Proof. vm_refl. Qed.
Lemma D_5e0a0 : decode_any W_5e0a0 = Some (Branch BC_EQ 15 16 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0a4 : bv 32 := 0x01078e93.
Lemma F_5e0a4 : fetch_word Asan.M.loaded_segments (0x5e0f4 : word) = Some W_5e0a4.
Proof. vm_refl. Qed.
Lemma D_5e0a4 : decode_any W_5e0a4 = Some (OpImm ALU_ADD 29 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0a8 : bv 32 := 0x00068e13.
Lemma F_5e0a8 : fetch_word Asan.M.loaded_segments (0x5e0f8 : word) = Some W_5e0a8.
Proof. vm_refl. Qed.
Lemma D_5e0a8 : decode_any W_5e0a8 = Some (OpImm ALU_ADD 28 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0ac : bv 32 := 0x026ee063.
Lemma F_5e0ac : fetch_word Asan.M.loaded_segments (0x5e0fc : word) = Some W_5e0ac.
Proof. vm_refl. Qed.
Lemma D_5e0ac : decode_any W_5e0ac = Some (Branch BC_LTU 29 6 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0b0 : bv 32 := 0x0017de13.
Lemma F_5e0b0 : fetch_word Asan.M.loaded_segments (0x5e100 : word) = Some W_5e0b0.
Proof. vm_refl. Qed.
Lemma D_5e0b0 : decode_any W_5e0b0 = Some (ShiftImm ALU_SRL 28 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0b4 : bv 32 := 0x03fe9e93.
Lemma F_5e0b4 : fetch_word Asan.M.loaded_segments (0x5e104 : word) = Some W_5e0b4.
Proof. vm_refl. Qed.
Lemma D_5e0b4 : decode_any W_5e0b4 = Some (ShiftImm ALU_SLL 29 29 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0b8 : bv 32 := 0x01c39e33.
Lemma F_5e0b8 : fetch_word Asan.M.loaded_segments (0x5e108 : word) = Some W_5e0b8.
Proof. vm_refl. Qed.
Lemma D_5e0b8 : decode_any W_5e0b8 = Some (Op ALU_SLL 28 7 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0bc : bv 32 := 0x001e5f13.
Lemma F_5e0bc : fetch_word Asan.M.loaded_segments (0x5e10c : word) = Some W_5e0bc.
Proof. vm_refl. Qed.
Lemma D_5e0bc : decode_any W_5e0bc = Some (ShiftImm ALU_SRL 30 28 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0c0 : bv 32 := 0x43fede93.
Lemma F_5e0c0 : fetch_word Asan.M.loaded_segments (0x5e110 : word) = Some W_5e0c0.
Proof. vm_refl. Qed.
Lemma D_5e0c0 : decode_any W_5e0c0 = Some (ShiftImm ALU_SRA 29 29 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0c4 : bv 32 := 0x01eefeb3.
Lemma F_5e0c4 : fetch_word Asan.M.loaded_segments (0x5e114 : word) = Some W_5e0c4.
Proof. vm_refl. Qed.
Lemma D_5e0c4 : decode_any W_5e0c4 = Some (Op ALU_AND 29 29 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0c8 : bv 32 := 0x01ce8e33.
Lemma F_5e0c8 : fetch_word Asan.M.loaded_segments (0x5e118 : word) = Some W_5e0c8.
Proof. vm_refl. Qed.
Lemma D_5e0c8 : decode_any W_5e0c8 = Some (Op ALU_ADD 28 29 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0cc : bv 32 := 0x03c8debb.
Lemma F_5e0cc : fetch_word Asan.M.loaded_segments (0x5e11c : word) = Some W_5e0cc.
Proof. vm_refl. Qed.
Lemma D_5e0cc : decode_any W_5e0cc = Some (Mul32 M_DIVU 29 17 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0d0 : bv 32 := 0x00800f13.
Lemma F_5e0d0 : fetch_word Asan.M.loaded_segments (0x5e120 : word) = Some W_5e0d0.
Proof. vm_refl. Qed.
Lemma D_5e0d0 : decode_any W_5e0d0 = Some (OpImm ALU_ADD 30 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0d4 : bv 32 := 0xfbeee4e3.
Lemma F_5e0d4 : fetch_word Asan.M.loaded_segments (0x5e124 : word) = Some W_5e0d4.
Proof. vm_refl. Qed.
Lemma D_5e0d4 : decode_any W_5e0d4 = Some (Branch BC_LTU 29 30 8104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0d8 : bv 32 := 0x00800e93.
Lemma F_5e0d8 : fetch_word Asan.M.loaded_segments (0x5e128 : word) = Some W_5e0d8.
Proof. vm_refl. Qed.
Lemma D_5e0d8 : decode_any W_5e0d8 = Some (OpImm ALU_ADD 29 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0dc : bv 32 := 0xfa1ff06f.
Lemma F_5e0dc : fetch_word Asan.M.loaded_segments (0x5e12c : word) = Some W_5e0dc.
Proof. vm_refl. Qed.
Lemma D_5e0dc : decode_any W_5e0dc = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0e0 : bv 32 := 0x04000e13.
Lemma F_5e0e0 : fetch_word Asan.M.loaded_segments (0x5e130 : word) = Some W_5e0e0.
Proof. vm_refl. Qed.
Lemma D_5e0e0 : decode_any W_5e0e0 = Some (OpImm ALU_ADD 28 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0e4 : bv 32 := 0x03c8debb.
Lemma F_5e0e4 : fetch_word Asan.M.loaded_segments (0x5e134 : word) = Some W_5e0e4.
Proof. vm_refl. Qed.
Lemma D_5e0e4 : decode_any W_5e0e4 = Some (Mul32 M_DIVU 29 17 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0e8 : bv 32 := 0x00800f13.
Lemma F_5e0e8 : fetch_word Asan.M.loaded_segments (0x5e138 : word) = Some W_5e0e8.
Proof. vm_refl. Qed.
Lemma D_5e0e8 : decode_any W_5e0e8 = Some (OpImm ALU_ADD 30 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0ec : bv 32 := 0xf9eee8e3.
Lemma F_5e0ec : fetch_word Asan.M.loaded_segments (0x5e13c : word) = Some W_5e0ec.
Proof. vm_refl. Qed.
Lemma D_5e0ec : decode_any W_5e0ec = Some (Branch BC_LTU 29 30 8080, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0f0 : bv 32 := 0xfe9ff06f.
Lemma F_5e0f0 : fetch_word Asan.M.loaded_segments (0x5e140 : word) = Some W_5e0f0.
Proof. vm_refl. Qed.
Lemma D_5e0f0 : decode_any W_5e0f0 = Some (Jal 0 2097128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0f4 : bv 32 := 0x00442583.
Lemma F_5e0f4 : fetch_word Asan.M.loaded_segments (0x5e144 : word) = Some W_5e0f4.
Proof. vm_refl. Qed.
Lemma D_5e0f4 : decode_any W_5e0f4 = Some (Load SZ4 true 11 8 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0f8 : bv 32 := 0xf25ff06f.
Lemma F_5e0f8 : fetch_word Asan.M.loaded_segments (0x5e148 : word) = Some W_5e0f8.
Proof. vm_refl. Qed.
Lemma D_5e0f8 : decode_any W_5e0f8 = Some (Jal 0 2096932, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e0fc : bv 32 := 0xf8010113.
Lemma F_5e0fc : fetch_word Asan.M.loaded_segments (0x5e14c : word) = Some W_5e0fc.
Proof. vm_refl. Qed.
Lemma D_5e0fc : decode_any W_5e0fc = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e100 : bv 32 := 0x06113c23.
Lemma F_5e100 : fetch_word Asan.M.loaded_segments (0x5e150 : word) = Some W_5e100.
Proof. vm_refl. Qed.
Lemma D_5e100 : decode_any W_5e100 = Some (Store SZ8 2 1 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e104 : bv 32 := 0x06813823.
Lemma F_5e104 : fetch_word Asan.M.loaded_segments (0x5e154 : word) = Some W_5e104.
Proof. vm_refl. Qed.
Lemma D_5e104 : decode_any W_5e104 = Some (Store SZ8 2 8 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e108 : bv 32 := 0x06913423.
Lemma F_5e108 : fetch_word Asan.M.loaded_segments (0x5e158 : word) = Some W_5e108.
Proof. vm_refl. Qed.
Lemma D_5e108 : decode_any W_5e108 = Some (Store SZ8 2 9 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e10c : bv 32 := 0x07213023.
Lemma F_5e10c : fetch_word Asan.M.loaded_segments (0x5e15c : word) = Some W_5e10c.
Proof. vm_refl. Qed.
Lemma D_5e10c : decode_any W_5e10c = Some (Store SZ8 2 18 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e110 : bv 32 := 0x05313c23.
Lemma F_5e110 : fetch_word Asan.M.loaded_segments (0x5e160 : word) = Some W_5e110.
Proof. vm_refl. Qed.
Lemma D_5e110 : decode_any W_5e110 = Some (Store SZ8 2 19 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e114 : bv 32 := 0x05413823.
Lemma F_5e114 : fetch_word Asan.M.loaded_segments (0x5e164 : word) = Some W_5e114.
Proof. vm_refl. Qed.
Lemma D_5e114 : decode_any W_5e114 = Some (Store SZ8 2 20 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e118 : bv 32 := 0x05513423.
Lemma F_5e118 : fetch_word Asan.M.loaded_segments (0x5e168 : word) = Some W_5e118.
Proof. vm_refl. Qed.
Lemma D_5e118 : decode_any W_5e118 = Some (Store SZ8 2 21 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e11c : bv 32 := 0x05613023.
Lemma F_5e11c : fetch_word Asan.M.loaded_segments (0x5e16c : word) = Some W_5e11c.
Proof. vm_refl. Qed.
Lemma D_5e11c : decode_any W_5e11c = Some (Store SZ8 2 22 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e120 : bv 32 := 0x03713c23.
Lemma F_5e120 : fetch_word Asan.M.loaded_segments (0x5e170 : word) = Some W_5e120.
Proof. vm_refl. Qed.
Lemma D_5e120 : decode_any W_5e120 = Some (Store SZ8 2 23 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e124 : bv 32 := 0x03813823.
Lemma F_5e124 : fetch_word Asan.M.loaded_segments (0x5e174 : word) = Some W_5e124.
Proof. vm_refl. Qed.
Lemma D_5e124 : decode_any W_5e124 = Some (Store SZ8 2 24 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e128 : bv 32 := 0x03913423.
Lemma F_5e128 : fetch_word Asan.M.loaded_segments (0x5e178 : word) = Some W_5e128.
Proof. vm_refl. Qed.
Lemma D_5e128 : decode_any W_5e128 = Some (Store SZ8 2 25 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e12c : bv 32 := 0x03a13023.
Lemma F_5e12c : fetch_word Asan.M.loaded_segments (0x5e17c : word) = Some W_5e12c.
Proof. vm_refl. Qed.
Lemma D_5e12c : decode_any W_5e12c = Some (Store SZ8 2 26 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e130 : bv 32 := 0x01b13c23.
Lemma F_5e130 : fetch_word Asan.M.loaded_segments (0x5e180 : word) = Some W_5e130.
Proof. vm_refl. Qed.
Lemma D_5e130 : decode_any W_5e130 = Some (Store SZ8 2 27 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e134 : bv 32 := 0x00050493.
Lemma F_5e134 : fetch_word Asan.M.loaded_segments (0x5e184 : word) = Some W_5e134.
Proof. vm_refl. Qed.
Lemma D_5e134 : decode_any W_5e134 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e138 : bv 32 := 0x00000793.
Lemma F_5e138 : fetch_word Asan.M.loaded_segments (0x5e188 : word) = Some W_5e138.
Proof. vm_refl. Qed.
Lemma D_5e138 : decode_any W_5e138 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e13c : bv 32 := 0x00100b93.
Lemma F_5e13c : fetch_word Asan.M.loaded_segments (0x5e18c : word) = Some W_5e13c.
Proof. vm_refl. Qed.
Lemma D_5e13c : decode_any W_5e13c = Some (OpImm ALU_ADD 23 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e140 : bv 32 := 0x02053a03.
Lemma F_5e140 : fetch_word Asan.M.loaded_segments (0x5e190 : word) = Some W_5e140.
Proof. vm_refl. Qed.
Lemma D_5e140 : decode_any W_5e140 = Some (Load SZ8 true 20 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e144 : bv 32 := 0x03053403.
Lemma F_5e144 : fetch_word Asan.M.loaded_segments (0x5e194 : word) = Some W_5e144.
Proof. vm_refl. Qed.
Lemma D_5e144 : decode_any W_5e144 = Some (Load SZ8 true 8 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e148 : bv 32 := 0x00761513.
Lemma F_5e148 : fetch_word Asan.M.loaded_segments (0x5e198 : word) = Some W_5e148.
Proof. vm_refl. Qed.
Lemma D_5e148 : decode_any W_5e148 = Some (ShiftImm ALU_SLL 10 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e14c : bv 32 := 0x02061893.
Lemma F_5e14c : fetch_word Asan.M.loaded_segments (0x5e19c : word) = Some W_5e14c.
Proof. vm_refl. Qed.
Lemma D_5e14c : decode_any W_5e14c = Some (ShiftImm ALU_SLL 17 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e150 : bv 32 := 0x00700293.
Lemma F_5e150 : fetch_word Asan.M.loaded_segments (0x5e1a0 : word) = Some W_5e150.
Proof. vm_refl. Qed.
Lemma D_5e150 : decode_any W_5e150 = Some (OpImm ALU_ADD 5 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e154 : bv 32 := 0xfff00813.
Lemma F_5e154 : fetch_word Asan.M.loaded_segments (0x5e1a4 : word) = Some W_5e154.
Proof. vm_refl. Qed.
Lemma D_5e154 : decode_any W_5e154 = Some (OpImm ALU_ADD 16 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e158 : bv 32 := 0x03db9993.
Lemma F_5e158 : fetch_word Asan.M.loaded_segments (0x5e1a8 : word) = Some W_5e158.
Proof. vm_refl. Qed.
Lemma D_5e158 : decode_any W_5e158 = Some (ShiftImm ALU_SLL 19 23 61, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e15c : bv 32 := 0x01d29293.
Lemma F_5e15c : fetch_word Asan.M.loaded_segments (0x5e1ac : word) = Some W_5e15c.
Proof. vm_refl. Qed.
Lemma D_5e15c : decode_any W_5e15c = Some (ShiftImm ALU_SLL 5 5 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e160 : bv 32 := 0x028b9a93.
Lemma F_5e160 : fetch_word Asan.M.loaded_segments (0x5e1b0 : word) = Some W_5e160.
Proof. vm_refl. Qed.
Lemma D_5e160 : decode_any W_5e160 = Some (ShiftImm ALU_SLL 21 23 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e164 : bv 32 := 0x005888b3.
Lemma F_5e164 : fetch_word Asan.M.loaded_segments (0x5e1b4 : word) = Some W_5e164.
Proof. vm_refl. Qed.
Lemma D_5e164 : decode_any W_5e164 = Some (Op ALU_ADD 17 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e168 : bv 32 := 0x001a8293.
Lemma F_5e168 : fetch_word Asan.M.loaded_segments (0x5e1b8 : word) = Some W_5e168.
Proof. vm_refl. Qed.
Lemma D_5e168 : decode_any W_5e168 = Some (OpImm ALU_ADD 5 21 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e16c : bv 32 := 0x01429293.
Lemma F_5e16c : fetch_word Asan.M.loaded_segments (0x5e1bc : word) = Some W_5e16c.
Proof. vm_refl. Qed.
Lemma D_5e16c : decode_any W_5e16c = Some (ShiftImm ALU_SLL 5 5 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e170 : bv 32 := 0x00a40433.
Lemma F_5e170 : fetch_word Asan.M.loaded_segments (0x5e1c0 : word) = Some W_5e170.
Proof. vm_refl. Qed.
Lemma D_5e170 : decode_any W_5e170 = Some (Op ALU_ADD 8 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e174 : bv 32 := 0x011a0a33.
Lemma F_5e174 : fetch_word Asan.M.loaded_segments (0x5e1c4 : word) = Some W_5e174.
Proof. vm_refl. Qed.
Lemma D_5e174 : decode_any W_5e174 = Some (Op ALU_ADD 20 20 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e178 : bv 32 := 0xfff28b13.
Lemma F_5e178 : fetch_word Asan.M.loaded_segments (0x5e1c8 : word) = Some W_5e178.
Proof. vm_refl. Qed.
Lemma D_5e178 : decode_any W_5e178 = Some (OpImm ALU_ADD 22 5 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e17c : bv 32 := 0x00043883.
Lemma F_5e17c : fetch_word Asan.M.loaded_segments (0x5e1cc : word) = Some W_5e17c.
Proof. vm_refl. Qed.
Lemma D_5e17c : decode_any W_5e17c = Some (Load SZ8 true 17 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e180 : bv 32 := 0x00840513.
Lemma F_5e180 : fetch_word Asan.M.loaded_segments (0x5e1d0 : word) = Some W_5e180.
Proof. vm_refl. Qed.
Lemma D_5e180 : decode_any W_5e180 = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e184 : bv 32 := 0x03cb9b93.
Lemma F_5e184 : fetch_word Asan.M.loaded_segments (0x5e1d4 : word) = Some W_5e184.
Proof. vm_refl. Qed.
Lemma D_5e184 : decode_any W_5e184 = Some (ShiftImm ALU_SLL 23 23 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e188 : bv 32 := 0x5dc00c13.
Lemma F_5e188 : fetch_word Asan.M.loaded_segments (0x5e1d8 : word) = Some W_5e188.
Proof. vm_refl. Qed.
Lemma D_5e188 : decode_any W_5e188 = Some (OpImm ALU_ADD 24 0 1500, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e18c : bv 32 := 0x03d81c93.
Lemma F_5e18c : fetch_word Asan.M.loaded_segments (0x5e1dc : word) = Some W_5e18c.
Proof. vm_refl. Qed.
Lemma D_5e18c : decode_any W_5e18c = Some (ShiftImm ALU_SLL 25 16 61, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e190 : bv 32 := 0xfffc8c93.
Lemma F_5e190 : fetch_word Asan.M.loaded_segments (0x5e1e0 : word) = Some W_5e190.
Proof. vm_refl. Qed.
Lemma D_5e190 : decode_any W_5e190 = Some (OpImm ALU_ADD 25 25 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e194 : bv 32 := 0x0168f2b3.
Lemma F_5e194 : fetch_word Asan.M.loaded_segments (0x5e1e4 : word) = Some W_5e194.
Proof. vm_refl. Qed.
Lemma D_5e194 : decode_any W_5e194 = Some (Op ALU_AND 5 17 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e198 : bv 32 := 0x02029663.
Lemma F_5e198 : fetch_word Asan.M.loaded_segments (0x5e1e8 : word) = Some W_5e198.
Proof. vm_refl. Qed.
Lemma D_5e198 : decode_any W_5e198 = Some (Branch BC_NE 5 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e19c : bv 32 := 0x0178e2b3.
Lemma F_5e19c : fetch_word Asan.M.loaded_segments (0x5e1ec : word) = Some W_5e19c.
Proof. vm_refl. Qed.
Lemma D_5e19c : decode_any W_5e19c = Some (Op ALU_OR 5 17 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e1a0 : bv 32 := 0x00587333.
Lemma F_5e1a0 : fetch_word Asan.M.loaded_segments (0x5e1f0 : word) = Some W_5e1a0.
Proof. vm_refl. Qed.
Lemma D_5e1a0 : decode_any W_5e1a0 = Some (Op ALU_AND 6 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e1a4 : bv 32 := 0x160432af.
Lemma F_5e1a4 : fetch_word Asan.M.loaded_segments (0x5e1f4 : word) = Some W_5e1a4.
Proof. vm_refl. Qed.
Lemma D_5e1a4 : decode_any W_5e1a4 = Some (Lr AD true true 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e1a8 : bv 32 := 0x01129663.
Lemma F_5e1a8 : fetch_word Asan.M.loaded_segments (0x5e1f8 : word) = Some W_5e1a8.
Proof. vm_refl. Qed.
Lemma D_5e1a8 : decode_any W_5e1a8 = Some (Branch BC_NE 5 17 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e1ac : bv 32 := 0x1a6433af.
Lemma F_5e1ac : fetch_word Asan.M.loaded_segments (0x5e1fc : word) = Some W_5e1ac.
Proof. vm_refl. Qed.
Lemma D_5e1ac : decode_any W_5e1ac = Some (Sc AD false true 7 8 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e1b0 : bv 32 := 0xfe039ae3.
Lemma F_5e1b0 : fetch_word Asan.M.loaded_segments (0x5e200 : word) = Some W_5e1b0.
Proof. vm_refl. Qed.
Lemma D_5e1b0 : decode_any W_5e1b0 = Some (Branch BC_NE 7 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e1b4 : bv 32 := 0x09128c63.
Lemma F_5e1b4 : fetch_word Asan.M.loaded_segments (0x5e204 : word) = Some W_5e1b4.
Proof. vm_refl. Qed.
Lemma D_5e1b4 : decode_any W_5e1b4 = Some (Branch BC_EQ 5 17 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e24c : bv 32 := 0x01043783.
Lemma F_5e24c : fetch_word Asan.M.loaded_segments (0x5e29c : word) = Some W_5e24c.
Proof. vm_refl. Qed.
Lemma D_5e24c : decode_any W_5e24c = Some (Load SZ8 true 15 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e250 : bv 32 := 0x14e7e663.
Lemma F_5e250 : fetch_word Asan.M.loaded_segments (0x5e2a0 : word) = Some W_5e250.
Proof. vm_refl. Qed.
Lemma D_5e250 : decode_any W_5e250 = Some (Branch BC_LTU 15 14 332, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e254 : bv 32 := 0x40e787b3.
Lemma F_5e254 : fetch_word Asan.M.loaded_segments (0x5e2a4 : word) = Some W_5e254.
Proof. vm_refl. Qed.
Lemma D_5e254 : decode_any W_5e254 = Some (Op ALU_SUB 15 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e258 : bv 32 := 0x00f43823.
Lemma F_5e258 : fetch_word Asan.M.loaded_segments (0x5e2a8 : word) = Some W_5e258.
Proof. vm_refl. Qed.
Lemma D_5e258 : decode_any W_5e258 = Some (Store SZ8 8 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e25c : bv 32 := 0x02070463.
Lemma F_5e25c : fetch_word Asan.M.loaded_segments (0x5e2ac : word) = Some W_5e25c.
Proof. vm_refl. Qed.
Lemma D_5e25c : decode_any W_5e25c = Some (Branch BC_EQ 14 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e260 : bv 32 := 0x00279793.
Lemma F_5e260 : fetch_word Asan.M.loaded_segments (0x5e2b0 : word) = Some W_5e260.
Proof. vm_refl. Qed.
Lemma D_5e260 : decode_any W_5e260 = Some (ShiftImm ALU_SLL 15 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e264 : bv 32 := 0x00fa0a33.
Lemma F_5e264 : fetch_word Asan.M.loaded_segments (0x5e2b4 : word) = Some W_5e264.
Proof. vm_refl. Qed.
Lemma D_5e264 : decode_any W_5e264 = Some (Op ALU_ADD 20 20 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e268 : bv 32 := 0x00271593.
Lemma F_5e268 : fetch_word Asan.M.loaded_segments (0x5e2b8 : word) = Some W_5e268.
Proof. vm_refl. Qed.
Lemma D_5e268 : decode_any W_5e268 = Some (ShiftImm ALU_SLL 11 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e26c : bv 32 := 0x00b685b3.
Lemma F_5e26c : fetch_word Asan.M.loaded_segments (0x5e2bc : word) = Some W_5e26c.
Proof. vm_refl. Qed.
Lemma D_5e26c : decode_any W_5e26c = Some (Op ALU_ADD 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e270 : bv 32 := 0x000a2603.
Lemma F_5e270 : fetch_word Asan.M.loaded_segments (0x5e2c0 : word) = Some W_5e270.
Proof. vm_refl. Qed.
Lemma D_5e270 : decode_any W_5e270 = Some (Load SZ4 true 12 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e274 : bv 32 := 0x00c6a023.
Lemma F_5e274 : fetch_word Asan.M.loaded_segments (0x5e2c4 : word) = Some W_5e274.
Proof. vm_refl. Qed.
Lemma D_5e274 : decode_any W_5e274 = Some (Store SZ4 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e278 : bv 32 := 0x00468693.
Lemma F_5e278 : fetch_word Asan.M.loaded_segments (0x5e2c8 : word) = Some W_5e278.
Proof. vm_refl. Qed.
Lemma D_5e278 : decode_any W_5e278 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e27c : bv 32 := 0x004a0a13.
Lemma F_5e27c : fetch_word Asan.M.loaded_segments (0x5e2cc : word) = Some W_5e27c.
Proof. vm_refl. Qed.
Lemma D_5e27c : decode_any W_5e27c = Some (OpImm ALU_ADD 20 20 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e280 : bv 32 := 0xfeb698e3.
Lemma F_5e280 : fetch_word Asan.M.loaded_segments (0x5e2d0 : word) = Some W_5e280.
Proof. vm_refl. Qed.
Lemma D_5e280 : decode_any W_5e280 = Some (Branch BC_NE 13 11 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e284 : bv 32 := 0x04843583.
Lemma F_5e284 : fetch_word Asan.M.loaded_segments (0x5e2d4 : word) = Some W_5e284.
Proof. vm_refl. Qed.
Lemma D_5e284 : decode_any W_5e284 = Some (Load SZ8 true 11 8 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e288 : bv 32 := 0x00e585b3.
Lemma F_5e288 : fetch_word Asan.M.loaded_segments (0x5e2d8 : word) = Some W_5e288.
Proof. vm_refl. Qed.
Lemma D_5e288 : decode_any W_5e288 = Some (Op ALU_ADD 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e28c : bv 32 := 0x04b43423.
Lemma F_5e28c : fetch_word Asan.M.loaded_segments (0x5e2dc : word) = Some W_5e28c.
Proof. vm_refl. Qed.
Lemma D_5e28c : decode_any W_5e28c = Some (Store SZ8 8 11 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e290 : bv 32 := 0x00100493.
Lemma F_5e290 : fetch_word Asan.M.loaded_segments (0x5e2e0 : word) = Some W_5e290.
Proof. vm_refl. Qed.
Lemma D_5e290 : decode_any W_5e290 = Some (OpImm ALU_ADD 9 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e294 : bv 32 := 0x00043603.
Lemma F_5e294 : fetch_word Asan.M.loaded_segments (0x5e2e4 : word) = Some W_5e294.
Proof. vm_refl. Qed.
Lemma D_5e294 : decode_any W_5e294 = Some (Load SZ8 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e298 : bv 32 := 0xfff00893.
Lemma F_5e298 : fetch_word Asan.M.loaded_segments (0x5e2e8 : word) = Some W_5e298.
Proof. vm_refl. Qed.
Lemma D_5e298 : decode_any W_5e298 = Some (OpImm ALU_ADD 17 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e29c : bv 32 := 0x00300693.
Lemma F_5e29c : fetch_word Asan.M.loaded_segments (0x5e2ec : word) = Some W_5e29c.
Proof. vm_refl. Qed.
Lemma D_5e29c : decode_any W_5e29c = Some (OpImm ALU_ADD 13 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2a0 : bv 32 := 0x001005b7.
Lemma F_5e2a0 : fetch_word Asan.M.loaded_segments (0x5e2f0 : word) = Some W_5e2a0.
Proof. vm_refl. Qed.
Lemma D_5e2a0 : decode_any W_5e2a0 = Some (Lui 11 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2a4 : bv 32 := 0xfffb2717.
Lemma F_5e2a4 : fetch_word Asan.M.loaded_segments (0x5e2f4 : word) = Some W_5e2a4.
Proof. vm_refl. Qed.
Lemma D_5e2a4 : decode_any W_5e2a4 = Some (Auipc 14 1048498, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2a8 : bv 32 := 0x03c89793.
Lemma F_5e2a8 : fetch_word Asan.M.loaded_segments (0x5e2f8 : word) = Some W_5e2a8.
Proof. vm_refl. Qed.
Lemma D_5e2a8 : decode_any W_5e2a8 = Some (ShiftImm ALU_SLL 15 17 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2ac : bv 32 := 0x03d69693.
Lemma F_5e2ac : fetch_word Asan.M.loaded_segments (0x5e2fc : word) = Some W_5e2ac.
Proof. vm_refl. Qed.
Lemma D_5e2ac : decode_any W_5e2ac = Some (ShiftImm ALU_SLL 13 13 61, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2b0 : bv 32 := 0xfff58593.
Lemma F_5e2b0 : fetch_word Asan.M.loaded_segments (0x5e300 : word) = Some W_5e2b0.
Proof. vm_refl. Qed.
Lemma D_5e2b0 : decode_any W_5e2b0 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2b4 : bv 32 := 0x15473703.
Lemma F_5e2b4 : fetch_word Asan.M.loaded_segments (0x5e304 : word) = Some W_5e2b4.
Proof. vm_refl. Qed.
Lemma D_5e2b4 : decode_any W_5e2b4 = Some (Load SZ8 true 14 14 340, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2b8 : bv 32 := 0xfff78793.
Lemma F_5e2b8 : fetch_word Asan.M.loaded_segments (0x5e308 : word) = Some W_5e2b8.
Proof. vm_refl. Qed.
Lemma D_5e2b8 : decode_any W_5e2b8 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2bc : bv 32 := 0x02859813.
Lemma F_5e2bc : fetch_word Asan.M.loaded_segments (0x5e30c : word) = Some W_5e2bc.
Proof. vm_refl. Qed.
Lemma D_5e2bc : decode_any W_5e2bc = Some (ShiftImm ALU_SLL 16 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2c0 : bv 32 := 0x02889893.
Lemma F_5e2c0 : fetch_word Asan.M.loaded_segments (0x5e310 : word) = Some W_5e2c0.
Proof. vm_refl. Qed.
Lemma D_5e2c0 : decode_any W_5e2c0 = Some (ShiftImm ALU_SLL 17 17 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2c4 : bv 32 := 0x00100293.
Lemma F_5e2c4 : fetch_word Asan.M.loaded_segments (0x5e314 : word) = Some W_5e2c4.
Proof. vm_refl. Qed.
Lemma D_5e2c4 : decode_any W_5e2c4 = Some (OpImm ALU_ADD 5 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2c8 : bv 32 := 0x03e29293.
Lemma F_5e2c8 : fetch_word Asan.M.loaded_segments (0x5e318 : word) = Some W_5e2c8.
Proof. vm_refl. Qed.
Lemma D_5e2c8 : decode_any W_5e2c8 = Some (ShiftImm ALU_SLL 5 5 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2cc : bv 32 := 0x01c0006f.
Lemma F_5e2cc : fetch_word Asan.M.loaded_segments (0x5e31c : word) = Some W_5e2cc.
Proof. vm_refl. Qed.
Lemma D_5e2cc : decode_any W_5e2cc = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2d0 : bv 32 := 0x160433af.
Lemma F_5e2d0 : fetch_word Asan.M.loaded_segments (0x5e320 : word) = Some W_5e2d0.
Proof. vm_refl. Qed.
Lemma D_5e2d0 : decode_any W_5e2d0 = Some (Lr AD true true 7 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2d4 : bv 32 := 0x00c39663.
Lemma F_5e2d4 : fetch_word Asan.M.loaded_segments (0x5e324 : word) = Some W_5e2d4.
Proof. vm_refl. Qed.
Lemma D_5e2d4 : decode_any W_5e2d4 = Some (Branch BC_NE 7 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2d8 : bv 32 := 0x1a643e2f.
Lemma F_5e2d8 : fetch_word Asan.M.loaded_segments (0x5e328 : word) = Some W_5e2d8.
Proof. vm_refl. Qed.
Lemma D_5e2d8 : decode_any W_5e2d8 = Some (Sc AD false true 28 8 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2dc : bv 32 := 0xfe0e1ae3.
Lemma F_5e2dc : fetch_word Asan.M.loaded_segments (0x5e32c : word) = Some W_5e2dc.
Proof. vm_refl. Qed.
Lemma D_5e2dc : decode_any W_5e2dc = Some (Branch BC_NE 28 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2e0 : bv 32 := 0x06c38463.
Lemma F_5e2e0 : fetch_word Asan.M.loaded_segments (0x5e330 : word) = Some W_5e2e0.
Proof. vm_refl. Qed.
Lemma D_5e2e0 : decode_any W_5e2e0 = Some (Branch BC_EQ 7 12 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2e8 : bv 32 := 0x00d675b3.
Lemma F_5e2e8 : fetch_word Asan.M.loaded_segments (0x5e338 : word) = Some W_5e2e8.
Proof. vm_refl. Qed.
Lemma D_5e2e8 : decode_any W_5e2e8 = Some (Op ALU_AND 11 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2ec : bv 32 := 0x00f67333.
Lemma F_5e2ec : fetch_word Asan.M.loaded_segments (0x5e33c : word) = Some W_5e2ec.
Proof. vm_refl. Qed.
Lemma D_5e2ec : decode_any W_5e2ec = Some (Op ALU_AND 6 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2f0 : bv 32 := 0x02059663.
Lemma F_5e2f0 : fetch_word Asan.M.loaded_segments (0x5e340 : word) = Some W_5e2f0.
Proof. vm_refl. Qed.
Lemma D_5e2f0 : decode_any W_5e2f0 = Some (Branch BC_NE 11 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2f4 : bv 32 := 0x010675b3.
Lemma F_5e2f4 : fetch_word Asan.M.loaded_segments (0x5e344 : word) = Some W_5e2f4.
Proof. vm_refl. Qed.
Lemma D_5e2f4 : decode_any W_5e2f4 = Some (Op ALU_AND 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e2f8 : bv 32 := 0x02058263.
Lemma F_5e2f8 : fetch_word Asan.M.loaded_segments (0x5e348 : word) = Some W_5e2f8.
Proof. vm_refl. Qed.
Lemma D_5e2f8 : decode_any W_5e2f8 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e31c : bv 32 := 0x013675b3.
Lemma F_5e31c : fetch_word Asan.M.loaded_segments (0x5e36c : word) = Some W_5e31c.
Proof. vm_refl. Qed.
Lemma D_5e31c : decode_any W_5e31c = Some (Op ALU_AND 11 12 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e320 : bv 32 := 0x00b035b3.
Lemma F_5e320 : fetch_word Asan.M.loaded_segments (0x5e370 : word) = Some W_5e320.
Proof. vm_refl. Qed.
Lemma D_5e320 : decode_any W_5e320 = Some (Op ALU_SLTU 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e324 : bv 32 := 0x01465393.
Lemma F_5e324 : fetch_word Asan.M.loaded_segments (0x5e374 : word) = Some W_5e324.
Proof. vm_refl. Qed.
Lemma D_5e324 : decode_any W_5e324 = Some (ShiftImm ALU_SRL 7 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e328 : bv 32 := 0xfff58593.
Lemma F_5e328 : fetch_word Asan.M.loaded_segments (0x5e378 : word) = Some W_5e328.
Proof. vm_refl. Qed.
Lemma D_5e328 : decode_any W_5e328 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e32c : bv 32 := 0x00b3f5b3.
Lemma F_5e32c : fetch_word Asan.M.loaded_segments (0x5e37c : word) = Some W_5e32c.
Proof. vm_refl. Qed.
Lemma D_5e32c : decode_any W_5e32c = Some (Op ALU_AND 11 7 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e330 : bv 32 := 0x02c59593.
Lemma F_5e330 : fetch_word Asan.M.loaded_segments (0x5e380 : word) = Some W_5e330.
Proof. vm_refl. Qed.
Lemma D_5e330 : decode_any W_5e330 = Some (ShiftImm ALU_SLL 11 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e334 : bv 32 := 0x02c5d593.
Lemma F_5e334 : fetch_word Asan.M.loaded_segments (0x5e384 : word) = Some W_5e334.
Proof. vm_refl. Qed.
Lemma D_5e334 : decode_any W_5e334 = Some (ShiftImm ALU_SRL 11 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e338 : bv 32 := 0xf8058ce3.
Lemma F_5e338 : fetch_word Asan.M.loaded_segments (0x5e388 : word) = Some W_5e338.
Proof. vm_refl. Qed.
Lemma D_5e338 : decode_any W_5e338 = Some (Branch BC_EQ 11 0 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e348 : bv 32 := 0x00058a63.
Lemma F_5e348 : fetch_word Asan.M.loaded_segments (0x5e398 : word) = Some W_5e348.
Proof. vm_refl. Qed.
Lemma D_5e348 : decode_any W_5e348 = Some (Branch BC_EQ 11 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e35c : bv 32 := 0x00048513.
Lemma F_5e35c : fetch_word Asan.M.loaded_segments (0x5e3ac : word) = Some W_5e35c.
Proof. vm_refl. Qed.
Lemma D_5e35c : decode_any W_5e35c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e360 : bv 32 := 0x07813083.
Lemma F_5e360 : fetch_word Asan.M.loaded_segments (0x5e3b0 : word) = Some W_5e360.
Proof. vm_refl. Qed.
Lemma D_5e360 : decode_any W_5e360 = Some (Load SZ8 true 1 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e364 : bv 32 := 0x07013403.
Lemma F_5e364 : fetch_word Asan.M.loaded_segments (0x5e3b4 : word) = Some W_5e364.
Proof. vm_refl. Qed.
Lemma D_5e364 : decode_any W_5e364 = Some (Load SZ8 true 8 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e368 : bv 32 := 0x06813483.
Lemma F_5e368 : fetch_word Asan.M.loaded_segments (0x5e3b8 : word) = Some W_5e368.
Proof. vm_refl. Qed.
Lemma D_5e368 : decode_any W_5e368 = Some (Load SZ8 true 9 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e36c : bv 32 := 0x06013903.
Lemma F_5e36c : fetch_word Asan.M.loaded_segments (0x5e3bc : word) = Some W_5e36c.
Proof. vm_refl. Qed.
Lemma D_5e36c : decode_any W_5e36c = Some (Load SZ8 true 18 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e370 : bv 32 := 0x05813983.
Lemma F_5e370 : fetch_word Asan.M.loaded_segments (0x5e3c0 : word) = Some W_5e370.
Proof. vm_refl. Qed.
Lemma D_5e370 : decode_any W_5e370 = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e374 : bv 32 := 0x05013a03.
Lemma F_5e374 : fetch_word Asan.M.loaded_segments (0x5e3c4 : word) = Some W_5e374.
Proof. vm_refl. Qed.
Lemma D_5e374 : decode_any W_5e374 = Some (Load SZ8 true 20 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e378 : bv 32 := 0x04813a83.
Lemma F_5e378 : fetch_word Asan.M.loaded_segments (0x5e3c8 : word) = Some W_5e378.
Proof. vm_refl. Qed.
Lemma D_5e378 : decode_any W_5e378 = Some (Load SZ8 true 21 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e37c : bv 32 := 0x04013b03.
Lemma F_5e37c : fetch_word Asan.M.loaded_segments (0x5e3cc : word) = Some W_5e37c.
Proof. vm_refl. Qed.
Lemma D_5e37c : decode_any W_5e37c = Some (Load SZ8 true 22 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e380 : bv 32 := 0x03813b83.
Lemma F_5e380 : fetch_word Asan.M.loaded_segments (0x5e3d0 : word) = Some W_5e380.
Proof. vm_refl. Qed.
Lemma D_5e380 : decode_any W_5e380 = Some (Load SZ8 true 23 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e384 : bv 32 := 0x03013c03.
Lemma F_5e384 : fetch_word Asan.M.loaded_segments (0x5e3d4 : word) = Some W_5e384.
Proof. vm_refl. Qed.
Lemma D_5e384 : decode_any W_5e384 = Some (Load SZ8 true 24 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e388 : bv 32 := 0x02813c83.
Lemma F_5e388 : fetch_word Asan.M.loaded_segments (0x5e3d8 : word) = Some W_5e388.
Proof. vm_refl. Qed.
Lemma D_5e388 : decode_any W_5e388 = Some (Load SZ8 true 25 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e38c : bv 32 := 0x02013d03.
Lemma F_5e38c : fetch_word Asan.M.loaded_segments (0x5e3dc : word) = Some W_5e38c.
Proof. vm_refl. Qed.
Lemma D_5e38c : decode_any W_5e38c = Some (Load SZ8 true 26 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e390 : bv 32 := 0x01813d83.
Lemma F_5e390 : fetch_word Asan.M.loaded_segments (0x5e3e0 : word) = Some W_5e390.
Proof. vm_refl. Qed.
Lemma D_5e390 : decode_any W_5e390 = Some (Load SZ8 true 27 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e394 : bv 32 := 0x08010113.
Lemma F_5e394 : fetch_word Asan.M.loaded_segments (0x5e3e4 : word) = Some W_5e394.
Proof. vm_refl. Qed.
Lemma D_5e394 : decode_any W_5e394 = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e398 : bv 32 := 0x00008067.
Lemma F_5e398 : fetch_word Asan.M.loaded_segments (0x5e3e8 : word) = Some W_5e398.
Proof. vm_refl. Qed.
Lemma D_5e398 : decode_any W_5e398 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e39c : bv 32 := 0x00068a93.
Lemma F_5e39c : fetch_word Asan.M.loaded_segments (0x5e3ec : word) = Some W_5e39c.
Proof. vm_refl. Qed.
Lemma D_5e39c : decode_any W_5e39c = Some (OpImm ALU_ADD 21 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3a0 : bv 32 := 0x00050913.
Lemma F_5e3a0 : fetch_word Asan.M.loaded_segments (0x5e3f0 : word) = Some W_5e3a0.
Proof. vm_refl. Qed.
Lemma D_5e3a0 : decode_any W_5e3a0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3a4 : bv 32 := 0x00070b13.
Lemma F_5e3a4 : fetch_word Asan.M.loaded_segments (0x5e3f4 : word) = Some W_5e3a4.
Proof. vm_refl. Qed.
Lemma D_5e3a4 : decode_any W_5e3a4 = Some (OpImm ALU_ADD 22 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3a8 : bv 32 := 0x40f70733.
Lemma F_5e3a8 : fetch_word Asan.M.loaded_segments (0x5e3f8 : word) = Some W_5e3a8.
Proof. vm_refl. Qed.
Lemma D_5e3a8 : decode_any W_5e3a8 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3ac : bv 32 := 0x00048513.
Lemma F_5e3ac : fetch_word Asan.M.loaded_segments (0x5e3fc : word) = Some W_5e3ac.
Proof. vm_refl. Qed.
Lemma D_5e3ac : decode_any W_5e3ac = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3b0 : bv 32 := 0x00040693.
Lemma F_5e3b0 : fetch_word Asan.M.loaded_segments (0x5e400 : word) = Some W_5e3b0.
Proof. vm_refl. Qed.
Lemma D_5e3b0 : decode_any W_5e3b0 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3b4 : bv 32 := 0x050000ef.
Lemma F_5e3b4 : fetch_word Asan.M.loaded_segments (0x5e404 : word) = Some W_5e3b4.
Proof. vm_refl. Qed.
Lemma D_5e3b4 : decode_any W_5e3b4 = Some (Jal 1 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3b8 : bv 32 := 0x02050263.
Lemma F_5e3b8 : fetch_word Asan.M.loaded_segments (0x5e408 : word) = Some W_5e3b8.
Proof. vm_refl. Qed.
Lemma D_5e3b8 : decode_any W_5e3b8 = Some (Branch BC_EQ 10 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3bc : bv 32 := 0x01043783.
Lemma F_5e3bc : fetch_word Asan.M.loaded_segments (0x5e40c : word) = Some W_5e3bc.
Proof. vm_refl. Qed.
Lemma D_5e3bc : decode_any W_5e3bc = Some (Load SZ8 true 15 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3c0 : bv 32 := 0x000b0713.
Lemma F_5e3c0 : fetch_word Asan.M.loaded_segments (0x5e410 : word) = Some W_5e3c0.
Proof. vm_refl. Qed.
Lemma D_5e3c0 : decode_any W_5e3c0 = Some (OpImm ALU_ADD 14 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3c4 : bv 32 := 0x0367e263.
Lemma F_5e3c4 : fetch_word Asan.M.loaded_segments (0x5e414 : word) = Some W_5e3c4.
Proof. vm_refl. Qed.
Lemma D_5e3c4 : decode_any W_5e3c4 = Some (Branch BC_LTU 15 22 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3c8 : bv 32 := 0x000a8693.
Lemma F_5e3c8 : fetch_word Asan.M.loaded_segments (0x5e418 : word) = Some W_5e3c8.
Proof. vm_refl. Qed.
Lemma D_5e3c8 : decode_any W_5e3c8 = Some (OpImm ALU_ADD 13 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3cc : bv 32 := 0x40e787b3.
Lemma F_5e3cc : fetch_word Asan.M.loaded_segments (0x5e41c : word) = Some W_5e3cc.
Proof. vm_refl. Qed.
Lemma D_5e3cc : decode_any W_5e3cc = Some (Op ALU_SUB 15 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3d0 : bv 32 := 0x00f43823.
Lemma F_5e3d0 : fetch_word Asan.M.loaded_segments (0x5e420 : word) = Some W_5e3d0.
Proof. vm_refl. Qed.
Lemma D_5e3d0 : decode_any W_5e3d0 = Some (Store SZ8 8 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3d4 : bv 32 := 0x00090513.
Lemma F_5e3d4 : fetch_word Asan.M.loaded_segments (0x5e424 : word) = Some W_5e3d4.
Proof. vm_refl. Qed.
Lemma D_5e3d4 : decode_any W_5e3d4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3d8 : bv 32 := 0xe89ff06f.
Lemma F_5e3d8 : fetch_word Asan.M.loaded_segments (0x5e428 : word) = Some W_5e3d8.
Proof. vm_refl. Qed.
Lemma D_5e3d8 : decode_any W_5e3d8 = Some (Jal 0 2096776, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e404 : bv 32 := 0xfc010113.
Lemma F_5e404 : fetch_word Asan.M.loaded_segments (0x5e454 : word) = Some W_5e404.
Proof. vm_refl. Qed.
Lemma D_5e404 : decode_any W_5e404 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e408 : bv 32 := 0x02113c23.
Lemma F_5e408 : fetch_word Asan.M.loaded_segments (0x5e458 : word) = Some W_5e408.
Proof. vm_refl. Qed.
Lemma D_5e408 : decode_any W_5e408 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e40c : bv 32 := 0x02813823.
Lemma F_5e40c : fetch_word Asan.M.loaded_segments (0x5e45c : word) = Some W_5e40c.
Proof. vm_refl. Qed.
Lemma D_5e40c : decode_any W_5e40c = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e410 : bv 32 := 0x02913423.
Lemma F_5e410 : fetch_word Asan.M.loaded_segments (0x5e460 : word) = Some W_5e410.
Proof. vm_refl. Qed.
Lemma D_5e410 : decode_any W_5e410 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e414 : bv 32 := 0x03213023.
Lemma F_5e414 : fetch_word Asan.M.loaded_segments (0x5e464 : word) = Some W_5e414.
Proof. vm_refl. Qed.
Lemma D_5e414 : decode_any W_5e414 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e418 : bv 32 := 0x01313c23.
Lemma F_5e418 : fetch_word Asan.M.loaded_segments (0x5e468 : word) = Some W_5e418.
Proof. vm_refl. Qed.
Lemma D_5e418 : decode_any W_5e418 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e41c : bv 32 := 0x01413823.
Lemma F_5e41c : fetch_word Asan.M.loaded_segments (0x5e46c : word) = Some W_5e41c.
Proof. vm_refl. Qed.
Lemma D_5e41c : decode_any W_5e41c = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e420 : bv 32 := 0x01513423.
Lemma F_5e420 : fetch_word Asan.M.loaded_segments (0x5e470 : word) = Some W_5e420.
Proof. vm_refl. Qed.
Lemma D_5e420 : decode_any W_5e420 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e424 : bv 32 := 0x01613023.
Lemma F_5e424 : fetch_word Asan.M.loaded_segments (0x5e474 : word) = Some W_5e424.
Proof. vm_refl. Qed.
Lemma D_5e424 : decode_any W_5e424 = Some (Store SZ8 2 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e428 : bv 32 := 0x00068413.
Lemma F_5e428 : fetch_word Asan.M.loaded_segments (0x5e478 : word) = Some W_5e428.
Proof. vm_refl. Qed.
Lemma D_5e428 : decode_any W_5e428 = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e42c : bv 32 := 0x00058493.
Lemma F_5e42c : fetch_word Asan.M.loaded_segments (0x5e47c : word) = Some W_5e42c.
Proof. vm_refl. Qed.
Lemma D_5e42c : decode_any W_5e42c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e430 : bv 32 := 0x02053903.
Lemma F_5e430 : fetch_word Asan.M.loaded_segments (0x5e480 : word) = Some W_5e430.
Proof. vm_refl. Qed.
Lemma D_5e430 : decode_any W_5e430 = Some (Load SZ8 true 18 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e434 : bv 32 := 0x01f00693.
Lemma F_5e434 : fetch_word Asan.M.loaded_segments (0x5e484 : word) = Some W_5e434.
Proof. vm_refl. Qed.
Lemma D_5e434 : decode_any W_5e434 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e438 : bv 32 := 0x02061593.
Lemma F_5e438 : fetch_word Asan.M.loaded_segments (0x5e488 : word) = Some W_5e438.
Proof. vm_refl. Qed.
Lemma D_5e438 : decode_any W_5e438 = Some (ShiftImm ALU_SLL 11 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e43c : bv 32 := 0x20d60263.
Lemma F_5e43c : fetch_word Asan.M.loaded_segments (0x5e48c : word) = Some W_5e43c.
Proof. vm_refl. Qed.
Lemma D_5e43c : decode_any W_5e43c = Some (Branch BC_EQ 12 13 516, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e440 : bv 32 := 0x01000693.
Lemma F_5e440 : fetch_word Asan.M.loaded_segments (0x5e490 : word) = Some W_5e440.
Proof. vm_refl. Qed.
Lemma D_5e440 : decode_any W_5e440 = Some (OpImm ALU_ADD 13 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e444 : bv 32 := 0x02c6e263.
Lemma F_5e444 : fetch_word Asan.M.loaded_segments (0x5e494 : word) = Some W_5e444.
Proof. vm_refl. Qed.
Lemma D_5e444 : decode_any W_5e444 = Some (Branch BC_LTU 13 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e448 : bv 32 := 0x00561a93.
Lemma F_5e448 : fetch_word Asan.M.loaded_segments (0x5e498 : word) = Some W_5e448.
Proof. vm_refl. Qed.
Lemma D_5e448 : decode_any W_5e448 = Some (ShiftImm ALU_SLL 21 12 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e44c : bv 32 := 0x02043683.
Lemma F_5e44c : fetch_word Asan.M.loaded_segments (0x5e49c : word) = Some W_5e44c.
Proof. vm_refl. Qed.
Lemma D_5e44c : decode_any W_5e44c = Some (Load SZ8 true 13 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e450 : bv 32 := 0x03043a03.
Lemma F_5e450 : fetch_word Asan.M.loaded_segments (0x5e4a0 : word) = Some W_5e450.
Proof. vm_refl. Qed.
Lemma D_5e450 : decode_any W_5e450 = Some (Load SZ8 true 20 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e454 : bv 32 := 0x02ea89b3.
Lemma F_5e454 : fetch_word Asan.M.loaded_segments (0x5e4a4 : word) = Some W_5e454.
Proof. vm_refl. Qed.
Lemma D_5e454 : decode_any W_5e454 = Some (Mul M_MUL 19 21 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e458 : bv 32 := 0x013689b3.
Lemma F_5e458 : fetch_word Asan.M.loaded_segments (0x5e4a8 : word) = Some W_5e458.
Proof. vm_refl. Qed.
Lemma D_5e458 : decode_any W_5e458 = Some (Op ALU_ADD 19 13 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e45c : bv 32 := 0x00b90933.
Lemma F_5e45c : fetch_word Asan.M.loaded_segments (0x5e4ac : word) = Some W_5e45c.
Proof. vm_refl. Qed.
Lemma D_5e45c : decode_any W_5e45c = Some (Op ALU_ADD 18 18 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e460 : bv 32 := 0x053a6263.
Lemma F_5e460 : fetch_word Asan.M.loaded_segments (0x5e4b0 : word) = Some W_5e460.
Proof. vm_refl. Qed.
Lemma D_5e460 : decode_any W_5e460 = Some (Branch BC_LTU 20 19 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e468 : bv 32 := 0xff060693.
Lemma F_5e468 : fetch_word Asan.M.loaded_segments (0x5e4b8 : word) = Some W_5e468.
Proof. vm_refl. Qed.
Lemma D_5e468 : decode_any W_5e468 = Some (OpImm ALU_ADD 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e46c : bv 32 := 0x20000793.
Lemma F_5e46c : fetch_word Asan.M.loaded_segments (0x5e4bc : word) = Some W_5e46c.
Proof. vm_refl. Qed.
Lemma D_5e46c : decode_any W_5e46c = Some (OpImm ALU_ADD 15 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e470 : bv 32 := 0x03f61813.
Lemma F_5e470 : fetch_word Asan.M.loaded_segments (0x5e4c0 : word) = Some W_5e470.
Proof. vm_refl. Qed.
Lemma D_5e470 : decode_any W_5e470 = Some (ShiftImm ALU_SLL 16 12 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e474 : bv 32 := 0x0016d693.
Lemma F_5e474 : fetch_word Asan.M.loaded_segments (0x5e4c4 : word) = Some W_5e474.
Proof. vm_refl. Qed.
Lemma D_5e474 : decode_any W_5e474 = Some (ShiftImm ALU_SRL 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e478 : bv 32 := 0x00d79ab3.
Lemma F_5e478 : fetch_word Asan.M.loaded_segments (0x5e4c8 : word) = Some W_5e478.
Proof. vm_refl. Qed.
Lemma D_5e478 : decode_any W_5e478 = Some (Op ALU_SLL 21 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e47c : bv 32 := 0x001ad693.
Lemma F_5e47c : fetch_word Asan.M.loaded_segments (0x5e4cc : word) = Some W_5e47c.
Proof. vm_refl. Qed.
Lemma D_5e47c : decode_any W_5e47c = Some (ShiftImm ALU_SRL 13 21 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e480 : bv 32 := 0x43f85793.
Lemma F_5e480 : fetch_word Asan.M.loaded_segments (0x5e4d0 : word) = Some W_5e480.
Proof. vm_refl. Qed.
Lemma D_5e480 : decode_any W_5e480 = Some (ShiftImm ALU_SRA 15 16 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e484 : bv 32 := 0x00d7f6b3.
Lemma F_5e484 : fetch_word Asan.M.loaded_segments (0x5e4d4 : word) = Some W_5e484.
Proof. vm_refl. Qed.
Lemma D_5e484 : decode_any W_5e484 = Some (Op ALU_AND 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e488 : bv 32 := 0x01568ab3.
Lemma F_5e488 : fetch_word Asan.M.loaded_segments (0x5e4d8 : word) = Some W_5e488.
Proof. vm_refl. Qed.
Lemma D_5e488 : decode_any W_5e488 = Some (Op ALU_ADD 21 13 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e48c : bv 32 := 0x02043683.
Lemma F_5e48c : fetch_word Asan.M.loaded_segments (0x5e4dc : word) = Some W_5e48c.
Proof. vm_refl. Qed.
Lemma D_5e48c : decode_any W_5e48c = Some (Load SZ8 true 13 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e490 : bv 32 := 0x03043a03.
Lemma F_5e490 : fetch_word Asan.M.loaded_segments (0x5e4e0 : word) = Some W_5e490.
Proof. vm_refl. Qed.
Lemma D_5e490 : decode_any W_5e490 = Some (Load SZ8 true 20 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e494 : bv 32 := 0x02ea89b3.
Lemma F_5e494 : fetch_word Asan.M.loaded_segments (0x5e4e4 : word) = Some W_5e494.
Proof. vm_refl. Qed.
Lemma D_5e494 : decode_any W_5e494 = Some (Mul M_MUL 19 21 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e498 : bv 32 := 0x013689b3.
Lemma F_5e498 : fetch_word Asan.M.loaded_segments (0x5e4e8 : word) = Some W_5e498.
Proof. vm_refl. Qed.
Lemma D_5e498 : decode_any W_5e498 = Some (Op ALU_ADD 19 13 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e49c : bv 32 := 0x00b90933.
Lemma F_5e49c : fetch_word Asan.M.loaded_segments (0x5e4ec : word) = Some W_5e49c.
Proof. vm_refl. Qed.
Lemma D_5e49c : decode_any W_5e49c = Some (Op ALU_ADD 18 18 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4a0 : bv 32 := 0x0d3a7c63.
Lemma F_5e4a0 : fetch_word Asan.M.loaded_segments (0x5e4f0 : word) = Some W_5e4a0.
Proof. vm_refl. Qed.
Lemma D_5e4a0 : decode_any W_5e4a0 = Some (Branch BC_GEU 20 19 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4a4 : bv 32 := 0x1a0a0e63.
Lemma F_5e4a4 : fetch_word Asan.M.loaded_segments (0x5e4f4 : word) = Some W_5e4a4.
Proof. vm_refl. Qed.
Lemma D_5e4a4 : decode_any W_5e4a4 = Some (Branch BC_EQ 20 0 444, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4a8 : bv 32 := 0xfffa4593.
Lemma F_5e4a8 : fetch_word Asan.M.loaded_segments (0x5e4f8 : word) = Some W_5e4a8.
Proof. vm_refl. Qed.
Lemma D_5e4a8 : decode_any W_5e4a8 = Some (OpImm ALU_XOR 11 20 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4ac : bv 32 := 0xfffc06b7.
Lemma F_5e4ac : fetch_word Asan.M.loaded_segments (0x5e4fc : word) = Some W_5e4ac.
Proof. vm_refl. Qed.
Lemma D_5e4ac : decode_any W_5e4ac = Some (Lui 13 1048512, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4b0 : bv 32 := 0x00b985b3.
Lemma F_5e4b0 : fetch_word Asan.M.loaded_segments (0x5e500 : word) = Some W_5e4b0.
Proof. vm_refl. Qed.
Lemma D_5e4b0 : decode_any W_5e4b0 = Some (Op ALU_ADD 11 19 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4b4 : bv 32 := 0x000409b7.
Lemma F_5e4b4 : fetch_word Asan.M.loaded_segments (0x5e504 : word) = Some W_5e4b4.
Proof. vm_refl. Qed.
Lemma D_5e4b4 : decode_any W_5e4b4 = Some (Lui 19 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4b8 : bv 32 := 0x00d5f5b3.
Lemma F_5e4b8 : fetch_word Asan.M.loaded_segments (0x5e508 : word) = Some W_5e4b8.
Proof. vm_refl. Qed.
Lemma D_5e4b8 : decode_any W_5e4b8 = Some (Op ALU_AND 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4bc : bv 32 := 0x03843683.
Lemma F_5e4bc : fetch_word Asan.M.loaded_segments (0x5e50c : word) = Some W_5e4bc.
Proof. vm_refl. Qed.
Lemma D_5e4bc : decode_any W_5e4bc = Some (Load SZ8 true 13 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4c0 : bv 32 := 0x013589b3.
Lemma F_5e4c0 : fetch_word Asan.M.loaded_segments (0x5e510 : word) = Some W_5e4c0.
Proof. vm_refl. Qed.
Lemma D_5e4c0 : decode_any W_5e4c0 = Some (Op ALU_ADD 19 11 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4c4 : bv 32 := 0x00700593.
Lemma F_5e4c4 : fetch_word Asan.M.loaded_segments (0x5e514 : word) = Some W_5e4c4.
Proof. vm_refl. Qed.
Lemma D_5e4c4 : decode_any W_5e4c4 = Some (OpImm ALU_ADD 11 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4c8 : bv 32 := 0x01d59593.
Lemma F_5e4c8 : fetch_word Asan.M.loaded_segments (0x5e518 : word) = Some W_5e4c8.
Proof. vm_refl. Qed.
Lemma D_5e4c8 : decode_any W_5e4c8 = Some (ShiftImm ALU_SLL 11 11 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4cc : bv 32 := 0x014686b3.
Lemma F_5e4cc : fetch_word Asan.M.loaded_segments (0x5e51c : word) = Some W_5e4cc.
Proof. vm_refl. Qed.
Lemma D_5e4cc : decode_any W_5e4cc = Some (Op ALU_ADD 13 13 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4d0 : bv 32 := 0x013686b3.
Lemma F_5e4d0 : fetch_word Asan.M.loaded_segments (0x5e520 : word) = Some W_5e4d0.
Proof. vm_refl. Qed.
Lemma D_5e4d0 : decode_any W_5e4d0 = Some (Op ALU_ADD 13 13 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4d4 : bv 32 := 0x00158593.
Lemma F_5e4d4 : fetch_word Asan.M.loaded_segments (0x5e524 : word) = Some W_5e4d4.
Proof. vm_refl. Qed.
Lemma D_5e4d4 : decode_any W_5e4d4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4d8 : bv 32 := 0x1ab6fa63.
Lemma F_5e4d8 : fetch_word Asan.M.loaded_segments (0x5e528 : word) = Some W_5e4d8.
Proof. vm_refl. Qed.
Lemma D_5e4d8 : decode_any W_5e4d8 = Some (Branch BC_GEU 13 11 436, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4dc : bv 32 := 0x03854583.
Lemma F_5e4dc : fetch_word Asan.M.loaded_segments (0x5e52c : word) = Some W_5e4dc.
Proof. vm_refl. Qed.
Lemma D_5e4dc : decode_any W_5e4dc = Some (Load SZ1 false 11 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4e0 : bv 32 := 0x012a0a33.
Lemma F_5e4e0 : fetch_word Asan.M.loaded_segments (0x5e530 : word) = Some W_5e4e0.
Proof. vm_refl. Qed.
Lemma D_5e4e0 : decode_any W_5e4e0 = Some (Op ALU_ADD 20 20 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4e4 : bv 32 := 0x02058463.
Lemma F_5e4e4 : fetch_word Asan.M.loaded_segments (0x5e534 : word) = Some W_5e4e4.
Proof. vm_refl. Qed.
Lemma D_5e4e4 : decode_any W_5e4e4 = Some (Branch BC_EQ 11 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e50c : bv 32 := 0xfffba597.
Lemma F_5e50c : fetch_word Asan.M.loaded_segments (0x5e55c : word) = Some W_5e50c.
Proof. vm_refl. Qed.
Lemma D_5e50c : decode_any W_5e50c = Some (Auipc 11 1048506, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e510 : bv 32 := 0x9c658693.
Lemma F_5e510 : fetch_word Asan.M.loaded_segments (0x5e560 : word) = Some W_5e510.
Proof. vm_refl. Qed.
Lemma D_5e510 : decode_any W_5e510 = Some (OpImm ALU_ADD 13 11 2502, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e514 : bv 32 := 0x00050b13.
Lemma F_5e514 : fetch_word Asan.M.loaded_segments (0x5e564 : word) = Some W_5e514.
Proof. vm_refl. Qed.
Lemma D_5e514 : decode_any W_5e514 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e518 : bv 32 := 0x000a0593.
Lemma F_5e518 : fetch_word Asan.M.loaded_segments (0x5e568 : word) = Some W_5e518.
Proof. vm_refl. Qed.
Lemma D_5e518 : decode_any W_5e518 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e51c : bv 32 := 0x00098613.
Lemma F_5e51c : fetch_word Asan.M.loaded_segments (0x5e56c : word) = Some W_5e51c.
Proof. vm_refl. Qed.
Lemma D_5e51c : decode_any W_5e51c = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e520 : bv 32 := 0x5843e0ef.
Lemma F_5e520 : fetch_word Asan.M.loaded_segments (0x5e570 : word) = Some W_5e520.
Proof. vm_refl. Qed.
Lemma D_5e520 : decode_any W_5e520 = Some (Jal 1 255364, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e524 : bv 32 := 0x16050863.
Lemma F_5e524 : fetch_word Asan.M.loaded_segments (0x5e574 : word) = Some W_5e524.
Proof. vm_refl. Qed.
Lemma D_5e524 : decode_any W_5e524 = Some (Branch BC_EQ 10 0 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e528 : bv 32 := 0x00050713.
Lemma F_5e528 : fetch_word Asan.M.loaded_segments (0x5e578 : word) = Some W_5e528.
Proof. vm_refl. Qed.
Lemma D_5e528 : decode_any W_5e528 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e52c : bv 32 := 0x1eaa1063.
Lemma F_5e52c : fetch_word Asan.M.loaded_segments (0x5e57c : word) = Some W_5e52c.
Proof. vm_refl. Qed.
Lemma D_5e52c : decode_any W_5e52c = Some (Branch BC_NE 20 10 480, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e530 : bv 32 := 0x0fa00613.
Lemma F_5e530 : fetch_word Asan.M.loaded_segments (0x5e580 : word) = Some W_5e530.
Proof. vm_refl. Qed.
Lemma D_5e530 : decode_any W_5e530 = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e534 : bv 32 := 0x000a0513.
Lemma F_5e534 : fetch_word Asan.M.loaded_segments (0x5e584 : word) = Some W_5e534.
Proof. vm_refl. Qed.
Lemma D_5e534 : decode_any W_5e534 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e538 : bv 32 := 0x00098593.
Lemma F_5e538 : fetch_word Asan.M.loaded_segments (0x5e588 : word) = Some W_5e538.
Proof. vm_refl. Qed.
Lemma D_5e538 : decode_any W_5e538 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e53c : bv 32 := 0x4d4230ef.
Lemma F_5e53c : fetch_word Asan.M.loaded_segments (0x5e58c : word) = Some W_5e53c.
Proof. vm_refl. Qed.
Lemma D_5e53c : decode_any W_5e53c = Some (Jal 1 144596, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e540 : bv 32 := 0x4482b0ef.
Lemma F_5e540 : fetch_word Asan.M.loaded_segments (0x5e590 : word) = Some W_5e540.
Proof. vm_refl. Qed.
Lemma D_5e540 : decode_any W_5e540 = Some (Jal 1 177224, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e544 : bv 32 := 0x04853583.
Lemma F_5e544 : fetch_word Asan.M.loaded_segments (0x5e594 : word) = Some W_5e544.
Proof. vm_refl. Qed.
Lemma D_5e544 : decode_any W_5e544 = Some (Load SZ8 true 11 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e548 : bv 32 := 0x05053603.
Lemma F_5e548 : fetch_word Asan.M.loaded_segments (0x5e598 : word) = Some W_5e548.
Proof. vm_refl. Qed.
Lemma D_5e548 : decode_any W_5e548 = Some (Load SZ8 true 12 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e54c : bv 32 := 0x00158593.
Lemma F_5e54c : fetch_word Asan.M.loaded_segments (0x5e59c : word) = Some W_5e54c.
Proof. vm_refl. Qed.
Lemma D_5e54c : decode_any W_5e54c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e550 : bv 32 := 0x01360633.
Lemma F_5e550 : fetch_word Asan.M.loaded_segments (0x5e5a0 : word) = Some W_5e550.
Proof. vm_refl. Qed.
Lemma D_5e550 : decode_any W_5e550 = Some (Op ALU_ADD 12 12 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e554 : bv 32 := 0x04b53423.
Lemma F_5e554 : fetch_word Asan.M.loaded_segments (0x5e5a4 : word) = Some W_5e554.
Proof. vm_refl. Qed.
Lemma D_5e554 : decode_any W_5e554 = Some (Store SZ8 10 11 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e558 : bv 32 := 0x04c53823.
Lemma F_5e558 : fetch_word Asan.M.loaded_segments (0x5e5a8 : word) = Some W_5e558.
Proof. vm_refl. Qed.
Lemma D_5e558 : decode_any W_5e558 = Some (Store SZ8 10 12 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e55c : bv 32 := 0x000b0513.
Lemma F_5e55c : fetch_word Asan.M.loaded_segments (0x5e5ac : word) = Some W_5e55c.
Proof. vm_refl. Qed.
Lemma D_5e55c : decode_any W_5e55c = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e560 : bv 32 := 0x01848493.
Lemma F_5e560 : fetch_word Asan.M.loaded_segments (0x5e5b0 : word) = Some W_5e560.
Proof. vm_refl. Qed.
Lemma D_5e560 : decode_any W_5e560 = Some (OpImm ALU_ADD 9 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e564 : bv 32 := 0x0134b02f.
Lemma F_5e564 : fetch_word Asan.M.loaded_segments (0x5e5b4 : word) = Some W_5e564.
Proof. vm_refl. Qed.
Lemma D_5e564 : decode_any W_5e564 = Some (Amo AMO_ADD AD false false 0 9 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e568 : bv 32 := 0x03043a03.
Lemma F_5e568 : fetch_word Asan.M.loaded_segments (0x5e5b8 : word) = Some W_5e568.
Proof. vm_refl. Qed.
Lemma D_5e568 : decode_any W_5e568 = Some (Load SZ8 true 20 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e56c : bv 32 := 0x02043683.
Lemma F_5e56c : fetch_word Asan.M.loaded_segments (0x5e5bc : word) = Some W_5e56c.
Proof. vm_refl. Qed.
Lemma D_5e56c : decode_any W_5e56c = Some (Load SZ8 true 13 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e570 : bv 32 := 0x013a0a33.
Lemma F_5e570 : fetch_word Asan.M.loaded_segments (0x5e5c0 : word) = Some W_5e570.
Proof. vm_refl. Qed.
Lemma D_5e570 : decode_any W_5e570 = Some (Op ALU_ADD 20 20 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e574 : bv 32 := 0x03443823.
Lemma F_5e574 : fetch_word Asan.M.loaded_segments (0x5e5c4 : word) = Some W_5e574.
Proof. vm_refl. Qed.
Lemma D_5e574 : decode_any W_5e574 = Some (Store SZ8 8 20 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e578 : bv 32 := 0x01043483.
Lemma F_5e578 : fetch_word Asan.M.loaded_segments (0x5e5c8 : word) = Some W_5e578.
Proof. vm_refl. Qed.
Lemma D_5e578 : decode_any W_5e578 = Some (Load SZ8 true 9 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e57c : bv 32 := 0x40da0a33.
Lemma F_5e57c : fetch_word Asan.M.loaded_segments (0x5e5cc : word) = Some W_5e57c.
Proof. vm_refl. Qed.
Lemma D_5e57c : decode_any W_5e57c = Some (Op ALU_SUB 20 20 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e580 : bv 32 := 0x035a59b3.
Lemma F_5e580 : fetch_word Asan.M.loaded_segments (0x5e5d0 : word) = Some W_5e580.
Proof. vm_refl. Qed.
Lemma D_5e580 : decode_any W_5e580 = Some (Mul M_DIVU 19 20 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e584 : bv 32 := 0x013484b3.
Lemma F_5e584 : fetch_word Asan.M.loaded_segments (0x5e5d4 : word) = Some W_5e584.
Proof. vm_refl. Qed.
Lemma D_5e584 : decode_any W_5e584 = Some (Op ALU_ADD 9 9 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e588 : bv 32 := 0x00040593.
Lemma F_5e588 : fetch_word Asan.M.loaded_segments (0x5e5d8 : word) = Some W_5e588.
Proof. vm_refl. Qed.
Lemma D_5e588 : decode_any W_5e588 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e58c : bv 32 := 0x00090613.
Lemma F_5e58c : fetch_word Asan.M.loaded_segments (0x5e5dc : word) = Some W_5e58c.
Proof. vm_refl. Qed.
Lemma D_5e58c : decode_any W_5e58c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e590 : bv 32 := 0x00048693.
Lemma F_5e590 : fetch_word Asan.M.loaded_segments (0x5e5e0 : word) = Some W_5e590.
Proof. vm_refl. Qed.
Lemma D_5e590 : decode_any W_5e590 = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e594 : bv 32 := 0xb35fd0ef.
Lemma F_5e594 : fetch_word Asan.M.loaded_segments (0x5e5e4 : word) = Some W_5e594.
Proof. vm_refl. Qed.
Lemma D_5e594 : decode_any W_5e594 = Some (Jal 1 2087732, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e598 : bv 32 := 0x0e050e63.
Lemma F_5e598 : fetch_word Asan.M.loaded_segments (0x5e5e8 : word) = Some W_5e598.
Proof. vm_refl. Qed.
Lemma D_5e598 : decode_any W_5e598 = Some (Branch BC_EQ 10 0 252, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e59c : bv 32 := 0x02043683.
Lemma F_5e59c : fetch_word Asan.M.loaded_segments (0x5e5ec : word) = Some W_5e59c.
Proof. vm_refl. Qed.
Lemma D_5e59c : decode_any W_5e59c = Some (Load SZ8 true 13 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5a0 : bv 32 := 0x055a6063.
Lemma F_5e5a0 : fetch_word Asan.M.loaded_segments (0x5e5f0 : word) = Some W_5e5a0.
Proof. vm_refl. Qed.
Lemma D_5e5a0 : decode_any W_5e5a0 = Some (Branch BC_LTU 20 21 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5a4 : bv 32 := 0x00000513.
Lemma F_5e5a4 : fetch_word Asan.M.loaded_segments (0x5e5f4 : word) = Some W_5e5a4.
Proof. vm_refl. Qed.
Lemma D_5e5a4 : decode_any W_5e5a4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5a8 : bv 32 := 0x00700593.
Lemma F_5e5a8 : fetch_word Asan.M.loaded_segments (0x5e5f8 : word) = Some W_5e5a8.
Proof. vm_refl. Qed.
Lemma D_5e5a8 : decode_any W_5e5a8 = Some (OpImm ALU_ADD 11 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5ac : bv 32 := 0x01d59593.
Lemma F_5e5ac : fetch_word Asan.M.loaded_segments (0x5e5fc : word) = Some W_5e5ac.
Proof. vm_refl. Qed.
Lemma D_5e5ac : decode_any W_5e5ac = Some (ShiftImm ALU_SLL 11 11 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5b0 : bv 32 := 0x00b905b3.
Lemma F_5e5b0 : fetch_word Asan.M.loaded_segments (0x5e600 : word) = Some W_5e5b0.
Proof. vm_refl. Qed.
Lemma D_5e5b0 : decode_any W_5e5b0 = Some (Op ALU_ADD 11 18 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5b4 : bv 32 := 0x00249493.
Lemma F_5e5b4 : fetch_word Asan.M.loaded_segments (0x5e604 : word) = Some W_5e5b4.
Proof. vm_refl. Qed.
Lemma D_5e5b4 : decode_any W_5e5b4 = Some (ShiftImm ALU_SLL 9 9 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5b8 : bv 32 := 0x009585b3.
Lemma F_5e5b8 : fetch_word Asan.M.loaded_segments (0x5e608 : word) = Some W_5e5b8.
Proof. vm_refl. Qed.
Lemma D_5e5b8 : decode_any W_5e5b8 = Some (Op ALU_ADD 11 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5bc : bv 32 := 0x00068613.
Lemma F_5e5bc : fetch_word Asan.M.loaded_segments (0x5e60c : word) = Some W_5e5bc.
Proof. vm_refl. Qed.
Lemma D_5e5bc : decode_any W_5e5bc = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5c0 : bv 32 := 0x00465713.
Lemma F_5e5c0 : fetch_word Asan.M.loaded_segments (0x5e610 : word) = Some W_5e5c0.
Proof. vm_refl. Qed.
Lemma D_5e5c0 : decode_any W_5e5c0 = Some (ShiftImm ALU_SRL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5c4 : bv 32 := 0xfff54793.
Lemma F_5e5c4 : fetch_word Asan.M.loaded_segments (0x5e614 : word) = Some W_5e5c4.
Proof. vm_refl. Qed.
Lemma D_5e5c4 : decode_any W_5e5c4 = Some (OpImm ALU_XOR 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5c8 : bv 32 := 0x00150513.
Lemma F_5e5c8 : fetch_word Asan.M.loaded_segments (0x5e618 : word) = Some W_5e5c8.
Proof. vm_refl. Qed.
Lemma D_5e5c8 : decode_any W_5e5c8 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5cc : bv 32 := 0x00279793.
Lemma F_5e5cc : fetch_word Asan.M.loaded_segments (0x5e61c : word) = Some W_5e5cc.
Proof. vm_refl. Qed.
Lemma D_5e5cc : decode_any W_5e5cc = Some (ShiftImm ALU_SLL 15 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5d0 : bv 32 := 0x00f587b3.
Lemma F_5e5d0 : fetch_word Asan.M.loaded_segments (0x5e620 : word) = Some W_5e5d0.
Proof. vm_refl. Qed.
Lemma D_5e5d0 : decode_any W_5e5d0 = Some (Op ALU_ADD 15 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5d4 : bv 32 := 0x00e7a023.
Lemma F_5e5d4 : fetch_word Asan.M.loaded_segments (0x5e624 : word) = Some W_5e5d4.
Proof. vm_refl. Qed.
Lemma D_5e5d4 : decode_any W_5e5d4 = Some (Store SZ4 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5d8 : bv 32 := 0x01560633.
Lemma F_5e5d8 : fetch_word Asan.M.loaded_segments (0x5e628 : word) = Some W_5e5d8.
Proof. vm_refl. Qed.
Lemma D_5e5d8 : decode_any W_5e5d8 = Some (Op ALU_ADD 12 12 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5dc : bv 32 := 0xff3562e3.
Lemma F_5e5dc : fetch_word Asan.M.loaded_segments (0x5e62c : word) = Some W_5e5dc.
Proof. vm_refl. Qed.
Lemma D_5e5dc : decode_any W_5e5dc = Some (Branch BC_LTU 10 19 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5e0 : bv 32 := 0x01043503.
Lemma F_5e5e0 : fetch_word Asan.M.loaded_segments (0x5e630 : word) = Some W_5e5e0.
Proof. vm_refl. Qed.
Lemma D_5e5e0 : decode_any W_5e5e0 = Some (Load SZ8 true 10 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5e4 : bv 32 := 0x035985b3.
Lemma F_5e5e4 : fetch_word Asan.M.loaded_segments (0x5e634 : word) = Some W_5e5e4.
Proof. vm_refl. Qed.
Lemma D_5e5e4 : decode_any W_5e5e4 = Some (Mul M_MUL 11 19 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5e8 : bv 32 := 0x03043703.
Lemma F_5e5e8 : fetch_word Asan.M.loaded_segments (0x5e638 : word) = Some W_5e5e8.
Proof. vm_refl. Qed.
Lemma D_5e5e8 : decode_any W_5e5e8 = Some (Load SZ8 true 14 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5ec : bv 32 := 0x00b686b3.
Lemma F_5e5ec : fetch_word Asan.M.loaded_segments (0x5e63c : word) = Some W_5e5ec.
Proof. vm_refl. Qed.
Lemma D_5e5ec : decode_any W_5e5ec = Some (Op ALU_ADD 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5f0 : bv 32 := 0x01350533.
Lemma F_5e5f0 : fetch_word Asan.M.loaded_segments (0x5e640 : word) = Some W_5e5f0.
Proof. vm_refl. Qed.
Lemma D_5e5f0 : decode_any W_5e5f0 = Some (Op ALU_ADD 10 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5f4 : bv 32 := 0x00a43823.
Lemma F_5e5f4 : fetch_word Asan.M.loaded_segments (0x5e644 : word) = Some W_5e5f4.
Proof. vm_refl. Qed.
Lemma D_5e5f4 : decode_any W_5e5f4 = Some (Store SZ8 8 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5f8 : bv 32 := 0x02d43023.
Lemma F_5e5f8 : fetch_word Asan.M.loaded_segments (0x5e648 : word) = Some W_5e5f8.
Proof. vm_refl. Qed.
Lemma D_5e5f8 : decode_any W_5e5f8 = Some (Store SZ8 8 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e5fc : bv 32 := 0x0ad76063.
Lemma F_5e5fc : fetch_word Asan.M.loaded_segments (0x5e64c : word) = Some W_5e5fc.
Proof. vm_refl. Qed.
Lemma D_5e5fc : decode_any W_5e5fc = Some (Branch BC_LTU 14 13 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e600 : bv 32 := 0x02843683.
Lemma F_5e600 : fetch_word Asan.M.loaded_segments (0x5e650 : word) = Some W_5e600.
Proof. vm_refl. Qed.
Lemma D_5e600 : decode_any W_5e600 = Some (Load SZ8 true 13 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e604 : bv 32 := 0x03843703.
Lemma F_5e604 : fetch_word Asan.M.loaded_segments (0x5e654 : word) = Some W_5e604.
Proof. vm_refl. Qed.
Lemma D_5e604 : decode_any W_5e604 = Some (Load SZ8 true 14 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e608 : bv 32 := 0x0ad76663.
Lemma F_5e608 : fetch_word Asan.M.loaded_segments (0x5e658 : word) = Some W_5e608.
Proof. vm_refl. Qed.
Lemma D_5e608 : decode_any W_5e608 = Some (Branch BC_LTU 14 13 172, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e60c : bv 32 := 0x04040223.
Lemma F_5e60c : fetch_word Asan.M.loaded_segments (0x5e65c : word) = Some W_5e60c.
Proof. vm_refl. Qed.
Lemma D_5e60c : decode_any W_5e60c = Some (Store SZ1 8 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e610 : bv 32 := 0x00100593.
Lemma F_5e610 : fetch_word Asan.M.loaded_segments (0x5e660 : word) = Some W_5e610.
Proof. vm_refl. Qed.
Lemma D_5e610 : decode_any W_5e610 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e614 : bv 32 := 0x00058513.
Lemma F_5e614 : fetch_word Asan.M.loaded_segments (0x5e664 : word) = Some W_5e614.
Proof. vm_refl. Qed.
Lemma D_5e614 : decode_any W_5e614 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e618 : bv 32 := 0x03813083.
Lemma F_5e618 : fetch_word Asan.M.loaded_segments (0x5e668 : word) = Some W_5e618.
Proof. vm_refl. Qed.
Lemma D_5e618 : decode_any W_5e618 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e61c : bv 32 := 0x03013403.
Lemma F_5e61c : fetch_word Asan.M.loaded_segments (0x5e66c : word) = Some W_5e61c.
Proof. vm_refl. Qed.
Lemma D_5e61c : decode_any W_5e61c = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e620 : bv 32 := 0x02813483.
Lemma F_5e620 : fetch_word Asan.M.loaded_segments (0x5e670 : word) = Some W_5e620.
Proof. vm_refl. Qed.
Lemma D_5e620 : decode_any W_5e620 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e624 : bv 32 := 0x02013903.
Lemma F_5e624 : fetch_word Asan.M.loaded_segments (0x5e674 : word) = Some W_5e624.
Proof. vm_refl. Qed.
Lemma D_5e624 : decode_any W_5e624 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e628 : bv 32 := 0x01813983.
Lemma F_5e628 : fetch_word Asan.M.loaded_segments (0x5e678 : word) = Some W_5e628.
Proof. vm_refl. Qed.
Lemma D_5e628 : decode_any W_5e628 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e62c : bv 32 := 0x01013a03.
Lemma F_5e62c : fetch_word Asan.M.loaded_segments (0x5e67c : word) = Some W_5e62c.
Proof. vm_refl. Qed.
Lemma D_5e62c : decode_any W_5e62c = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e630 : bv 32 := 0x00813a83.
Lemma F_5e630 : fetch_word Asan.M.loaded_segments (0x5e680 : word) = Some W_5e630.
Proof. vm_refl. Qed.
Lemma D_5e630 : decode_any W_5e630 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e634 : bv 32 := 0x00013b03.
Lemma F_5e634 : fetch_word Asan.M.loaded_segments (0x5e684 : word) = Some W_5e634.
Proof. vm_refl. Qed.
Lemma D_5e634 : decode_any W_5e634 = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e638 : bv 32 := 0x04010113.
Lemma F_5e638 : fetch_word Asan.M.loaded_segments (0x5e688 : word) = Some W_5e638.
Proof. vm_refl. Qed.
Lemma D_5e638 : decode_any W_5e638 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e63c : bv 32 := 0x00008067.
Lemma F_5e63c : fetch_word Asan.M.loaded_segments (0x5e68c : word) = Some W_5e63c.
Proof. vm_refl. Qed.
Lemma D_5e63c : decode_any W_5e63c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e660 : bv 32 := 0x02852583.
Lemma F_5e660 : fetch_word Asan.M.loaded_segments (0x5e6b0 : word) = Some W_5e660.
Proof. vm_refl. Qed.
Lemma D_5e660 : decode_any W_5e660 = Some (Load SZ4 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e664 : bv 32 := 0x0c05c263.
Lemma F_5e664 : fetch_word Asan.M.loaded_segments (0x5e6b4 : word) = Some W_5e664.
Proof. vm_refl. Qed.
Lemma D_5e664 : decode_any W_5e664 = Some (Branch BC_LT 11 0 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e728 : bv 32 := 0x00000a13.
Lemma F_5e728 : fetch_word Asan.M.loaded_segments (0x5e778 : word) = Some W_5e728.
Proof. vm_refl. Qed.
Lemma D_5e728 : decode_any W_5e728 = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e72c : bv 32 := 0xd7dff06f.
Lemma F_5e72c : fetch_word Asan.M.loaded_segments (0x5e77c : word) = Some W_5e72c.
Proof. vm_refl. Qed.
Lemma D_5e72c : decode_any W_5e72c = Some (Jal 0 2096508, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e774 : bv 32 := 0xff010113.
Lemma F_5e774 : fetch_word Asan.M.loaded_segments (0x5e7c4 : word) = Some W_5e774.
Proof. vm_refl. Qed.
Lemma D_5e774 : decode_any W_5e774 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e778 : bv 32 := 0x00113423.
Lemma F_5e778 : fetch_word Asan.M.loaded_segments (0x5e7c8 : word) = Some W_5e778.
Proof. vm_refl. Qed.
Lemma D_5e778 : decode_any W_5e778 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e77c : bv 32 := 0x02051693.
Lemma F_5e77c : fetch_word Asan.M.loaded_segments (0x5e7cc : word) = Some W_5e77c.
Proof. vm_refl. Qed.
Lemma D_5e77c : decode_any W_5e77c = Some (ShiftImm ALU_SLL 13 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e780 : bv 32 := 0x00f00593.
Lemma F_5e780 : fetch_word Asan.M.loaded_segments (0x5e7d0 : word) = Some W_5e780.
Proof. vm_refl. Qed.
Lemma D_5e780 : decode_any W_5e780 = Some (OpImm ALU_ADD 11 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e784 : bv 32 := 0x0206d693.
Lemma F_5e784 : fetch_word Asan.M.loaded_segments (0x5e7d4 : word) = Some W_5e784.
Proof. vm_refl. Qed.
Lemma D_5e784 : decode_any W_5e784 = Some (ShiftImm ALU_SRL 13 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e788 : bv 32 := 0x06a5f663.
Lemma F_5e788 : fetch_word Asan.M.loaded_segments (0x5e7d8 : word) = Some W_5e788.
Proof. vm_refl. Qed.
Lemma D_5e788 : decode_any W_5e788 = Some (Branch BC_GEU 11 10 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e78c : bv 32 := 0x000015b7.
Lemma F_5e78c : fetch_word Asan.M.loaded_segments (0x5e7dc : word) = Some W_5e78c.
Proof. vm_refl. Qed.
Lemma D_5e78c : decode_any W_5e78c = Some (Lui 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e790 : bv 32 := 0x8015859b.
Lemma F_5e790 : fetch_word Asan.M.loaded_segments (0x5e7e0 : word) = Some W_5e790.
Proof. vm_refl. Qed.
Lemma D_5e790 : decode_any W_5e790 = Some (OpImm32 11 11 2049, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e794 : bv 32 := 0x06b57e63.
Lemma F_5e794 : fetch_word Asan.M.loaded_segments (0x5e7e4 : word) = Some W_5e794.
Proof. vm_refl. Qed.
Lemma D_5e794 : decode_any W_5e794 = Some (Branch BC_GEU 10 11 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e798 : bv 32 := 0xfff68593.
Lemma F_5e798 : fetch_word Asan.M.loaded_segments (0x5e7e8 : word) = Some W_5e798.
Proof. vm_refl. Qed.
Lemma D_5e798 : decode_any W_5e798 = Some (OpImm ALU_ADD 11 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e79c : bv 32 := 0x00b6f5b3.
Lemma F_5e79c : fetch_word Asan.M.loaded_segments (0x5e7ec : word) = Some W_5e79c.
Proof. vm_refl. Qed.
Lemma D_5e79c : decode_any W_5e79c = Some (Op ALU_AND 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7a0 : bv 32 := 0x08059863.
Lemma F_5e7a0 : fetch_word Asan.M.loaded_segments (0x5e7f0 : word) = Some W_5e7a0.
Proof. vm_refl. Qed.
Lemma D_5e7a0 : decode_any W_5e7a0 = Some (Branch BC_NE 11 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7a4 : bv 32 := 0x40d005b3.
Lemma F_5e7a4 : fetch_word Asan.M.loaded_segments (0x5e7f4 : word) = Some W_5e7a4.
Proof. vm_refl. Qed.
Lemma D_5e7a4 : decode_any W_5e7a4 = Some (Op ALU_SUB 11 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7a8 : bv 32 := 0xfffb2617.
Lemma F_5e7a8 : fetch_word Asan.M.loaded_segments (0x5e7f8 : word) = Some W_5e7a8.
Proof. vm_refl. Qed.
Lemma D_5e7a8 : decode_any W_5e7a8 = Some (Auipc 12 1048498, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7ac : bv 32 := 0xc7063603.
Lemma F_5e7ac : fetch_word Asan.M.loaded_segments (0x5e7fc : word) = Some W_5e7ac.
Proof. vm_refl. Qed.
Lemma D_5e7ac : decode_any W_5e7ac = Some (Load SZ8 true 12 12 3184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7b0 : bv 32 := 0xfffb2717.
Lemma F_5e7b0 : fetch_word Asan.M.loaded_segments (0x5e800 : word) = Some W_5e7b0.
Proof. vm_refl. Qed.
Lemma D_5e7b0 : decode_any W_5e7b0 = Some (Auipc 14 1048498, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7b4 : bv 32 := 0x00b6f5b3.
Lemma F_5e7b4 : fetch_word Asan.M.loaded_segments (0x5e804 : word) = Some W_5e7b4.
Proof. vm_refl. Qed.
Lemma D_5e7b4 : decode_any W_5e7b4 = Some (Op ALU_AND 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7b8 : bv 32 := 0xde870713.
Lemma F_5e7b8 : fetch_word Asan.M.loaded_segments (0x5e808 : word) = Some W_5e7b8.
Proof. vm_refl. Qed.
Lemma D_5e7b8 : decode_any W_5e7b8 = Some (OpImm ALU_ADD 14 14 3560, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7bc : bv 32 := 0x02c585b3.
Lemma F_5e7bc : fetch_word Asan.M.loaded_segments (0x5e80c : word) = Some W_5e7bc.
Proof. vm_refl. Qed.
Lemma D_5e7bc : decode_any W_5e7bc = Some (Mul M_MUL 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7c0 : bv 32 := 0x03a5d593.
Lemma F_5e7c0 : fetch_word Asan.M.loaded_segments (0x5e810 : word) = Some W_5e7c0.
Proof. vm_refl. Qed.
Lemma D_5e7c0 : decode_any W_5e7c0 = Some (ShiftImm ALU_SRL 11 11 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7c4 : bv 32 := 0x00b705b3.
Lemma F_5e7c4 : fetch_word Asan.M.loaded_segments (0x5e814 : word) = Some W_5e7c4.
Proof. vm_refl. Qed.
Lemma D_5e7c4 : decode_any W_5e7c4 = Some (Op ALU_ADD 11 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7c8 : bv 32 := 0x0005c603.
Lemma F_5e7c8 : fetch_word Asan.M.loaded_segments (0x5e818 : word) = Some W_5e7c8.
Proof. vm_refl. Qed.
Lemma D_5e7c8 : decode_any W_5e7c8 = Some (Load SZ1 false 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7cc : bv 32 := 0xffc60593.
Lemma F_5e7cc : fetch_word Asan.M.loaded_segments (0x5e81c : word) = Some W_5e7cc.
Proof. vm_refl. Qed.
Lemma D_5e7cc : decode_any W_5e7cc = Some (OpImm ALU_ADD 11 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7d0 : bv 32 := 0x00800713.
Lemma F_5e7d0 : fetch_word Asan.M.loaded_segments (0x5e820 : word) = Some W_5e7d0.
Proof. vm_refl. Qed.
Lemma D_5e7d0 : decode_any W_5e7d0 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7d4 : bv 32 := 0x06e5fe63.
Lemma F_5e7d4 : fetch_word Asan.M.loaded_segments (0x5e824 : word) = Some W_5e7d4.
Proof. vm_refl. Qed.
Lemma D_5e7d4 : decode_any W_5e7d4 = Some (Branch BC_GEU 11 14 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7d8 : bv 32 := 0x00100713.
Lemma F_5e7d8 : fetch_word Asan.M.loaded_segments (0x5e828 : word) = Some W_5e7d8.
Proof. vm_refl. Qed.
Lemma D_5e7d8 : decode_any W_5e7d8 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7dc : bv 32 := 0x00c7173b.
Lemma F_5e7dc : fetch_word Asan.M.loaded_segments (0x5e82c : word) = Some W_5e7dc.
Proof. vm_refl. Qed.
Lemma D_5e7dc : decode_any W_5e7dc = Some (Op32 ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7e0 : bv 32 := 0x08e51a63.
Lemma F_5e7e0 : fetch_word Asan.M.loaded_segments (0x5e830 : word) = Some W_5e7e0.
Proof. vm_refl. Qed.
Lemma D_5e7e0 : decode_any W_5e7e0 = Some (Branch BC_NE 10 14 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7e4 : bv 32 := 0x00058513.
Lemma F_5e7e4 : fetch_word Asan.M.loaded_segments (0x5e834 : word) = Some W_5e7e4.
Proof. vm_refl. Qed.
Lemma D_5e7e4 : decode_any W_5e7e4 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7e8 : bv 32 := 0x00813083.
Lemma F_5e7e8 : fetch_word Asan.M.loaded_segments (0x5e838 : word) = Some W_5e7e8.
Proof. vm_refl. Qed.
Lemma D_5e7e8 : decode_any W_5e7e8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7ec : bv 32 := 0x01010113.
Lemma F_5e7ec : fetch_word Asan.M.loaded_segments (0x5e83c : word) = Some W_5e7ec.
Proof. vm_refl. Qed.
Lemma D_5e7ec : decode_any W_5e7ec = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7f0 : bv 32 := 0x00008067.
Lemma F_5e7f0 : fetch_word Asan.M.loaded_segments (0x5e840 : word) = Some W_5e7f0.
Proof. vm_refl. Qed.
Lemma D_5e7f0 : decode_any W_5e7f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

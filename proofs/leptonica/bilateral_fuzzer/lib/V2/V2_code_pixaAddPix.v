(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_18450 : bv 32 := 0xfd010113.
Lemma F_18450 : fetch_word Ubsan.M.loaded_segments (0x18450 : word) = Some W_18450.
Proof. vm_refl. Qed.
Lemma D_18450 : decode_any W_18450 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_18454 : bv 32 := 0x02113423.
Lemma F_18454 : fetch_word Ubsan.M.loaded_segments (0x18454 : word) = Some W_18454.
Proof. vm_refl. Qed.
Lemma D_18454 : decode_any W_18454 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_18458 : bv 32 := 0x02813023.
Lemma F_18458 : fetch_word Ubsan.M.loaded_segments (0x18458 : word) = Some W_18458.
Proof. vm_refl. Qed.
Lemma D_18458 : decode_any W_18458 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1845c : bv 32 := 0x00913c23.
Lemma F_1845c : fetch_word Ubsan.M.loaded_segments (0x1845c : word) = Some W_1845c.
Proof. vm_refl. Qed.
Lemma D_1845c : decode_any W_1845c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18460 : bv 32 := 0x01213823.
Lemma F_18460 : fetch_word Ubsan.M.loaded_segments (0x18460 : word) = Some W_18460.
Proof. vm_refl. Qed.
Lemma D_18460 : decode_any W_18460 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18464 : bv 32 := 0x01313423.
Lemma F_18464 : fetch_word Ubsan.M.loaded_segments (0x18464 : word) = Some W_18464.
Proof. vm_refl. Qed.
Lemma D_18464 : decode_any W_18464 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18468 : bv 32 := 0x02050263.
Lemma F_18468 : fetch_word Ubsan.M.loaded_segments (0x18468 : word) = Some W_18468.
Proof. vm_refl. Qed.
Lemma D_18468 : decode_any W_18468 = Some (Branch BC_EQ 10 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_1846c : bv 32 := 0x04058463.
Lemma F_1846c : fetch_word Ubsan.M.loaded_segments (0x1846c : word) = Some W_1846c.
Proof. vm_refl. Qed.
Lemma D_1846c : decode_any W_1846c = Some (Branch BC_EQ 11 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_18470 : bv 32 := 0x00200693.
Lemma F_18470 : fetch_word Ubsan.M.loaded_segments (0x18470 : word) = Some W_18470.
Proof. vm_refl. Qed.
Lemma D_18470 : decode_any W_18470 = Some (OpImm ALU_ADD 13 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_18474 : bv 32 := 0x06d60e63.
Lemma F_18474 : fetch_word Ubsan.M.loaded_segments (0x18474 : word) = Some W_18474.
Proof. vm_refl. Qed.
Lemma D_18474 : decode_any W_18474 = Some (Branch BC_EQ 12 13 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_18478 : bv 32 := 0x00100693.
Lemma F_18478 : fetch_word Ubsan.M.loaded_segments (0x18478 : word) = Some W_18478.
Proof. vm_refl. Qed.
Lemma D_18478 : decode_any W_18478 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1847c : bv 32 := 0x06d60063.
Lemma F_1847c : fetch_word Ubsan.M.loaded_segments (0x1847c : word) = Some W_1847c.
Proof. vm_refl. Qed.
Lemma D_1847c : decode_any W_1847c = Some (Branch BC_EQ 12 13 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_18480 : bv 32 := 0x16061463.
Lemma F_18480 : fetch_word Ubsan.M.loaded_segments (0x18480 : word) = Some W_18480.
Proof. vm_refl. Qed.
Lemma D_18480 : decode_any W_18480 = Some (Branch BC_NE 12 0 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_18484 : bv 32 := 0x00b13023.
Lemma F_18484 : fetch_word Ubsan.M.loaded_segments (0x18484 : word) = Some W_18484.
Proof. vm_refl. Qed.
Lemma D_18484 : decode_any W_18484 = Some (Store SZ8 2 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18488 : bv 32 := 0x08c0006f.
Lemma F_18488 : fetch_word Ubsan.M.loaded_segments (0x18488 : word) = Some W_18488.
Proof. vm_refl. Qed.
Lemma D_18488 : decode_any W_18488 = Some (Jal 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_1848c : bv 32 := 0x0002d517.
Lemma F_1848c : fetch_word Ubsan.M.loaded_segments (0x1848c : word) = Some W_1848c.
Proof. vm_refl. Qed.
Lemma D_1848c : decode_any W_1848c = Some (Auipc 10 45, 4%Z).
Proof. vm_refl. Qed.

Definition W_18490 : bv 32 := 0xa0c53503.
Lemma F_18490 : fetch_word Ubsan.M.loaded_segments (0x18490 : word) = Some W_18490.
Proof. vm_refl. Qed.
Lemma D_18490 : decode_any W_18490 = Some (Load SZ8 true 10 10 2572, 4%Z).
Proof. vm_refl. Qed.

Definition W_18494 : bv 32 := 0x00052503.
Lemma F_18494 : fetch_word Ubsan.M.loaded_segments (0x18494 : word) = Some W_18494.
Proof. vm_refl. Qed.
Lemma D_18494 : decode_any W_18494 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18498 : bv 32 := 0x00500593.
Lemma F_18498 : fetch_word Ubsan.M.loaded_segments (0x18498 : word) = Some W_18498.
Proof. vm_refl. Qed.
Lemma D_18498 : decode_any W_18498 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1849c : bv 32 := 0x1aa5cc63.
Lemma F_1849c : fetch_word Ubsan.M.loaded_segments (0x1849c : word) = Some W_1849c.
Proof. vm_refl. Qed.
Lemma D_1849c : decode_any W_1849c = Some (Branch BC_LT 11 10 440, 4%Z).
Proof. vm_refl. Qed.

Definition W_184a0 : bv 32 := 0xffffa517.
Lemma F_184a0 : fetch_word Ubsan.M.loaded_segments (0x184a0 : word) = Some W_184a0.
Proof. vm_refl. Qed.
Lemma D_184a0 : decode_any W_184a0 = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

Definition W_184a4 : bv 32 := 0xffff8597.
Lemma F_184a4 : fetch_word Ubsan.M.loaded_segments (0x184a4 : word) = Some W_184a4.
Proof. vm_refl. Qed.
Lemma D_184a4 : decode_any W_184a4 = Some (Auipc 11 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_184a8 : bv 32 := 0xd8750513.
Lemma F_184a8 : fetch_word Ubsan.M.loaded_segments (0x184a8 : word) = Some W_184a8.
Proof. vm_refl. Qed.
Lemma D_184a8 : decode_any W_184a8 = Some (OpImm ALU_ADD 10 10 3463, 4%Z).
Proof. vm_refl. Qed.

Definition W_184ac : bv 32 := 0x26058593.
Lemma F_184ac : fetch_word Ubsan.M.loaded_segments (0x184ac : word) = Some W_184ac.
Proof. vm_refl. Qed.
Lemma D_184ac : decode_any W_184ac = Some (OpImm ALU_ADD 11 11 608, 4%Z).
Proof. vm_refl. Qed.

Definition W_184b0 : bv 32 := 0x1840006f.
Lemma F_184b0 : fetch_word Ubsan.M.loaded_segments (0x184b0 : word) = Some W_184b0.
Proof. vm_refl. Qed.
Lemma D_184b0 : decode_any W_184b0 = Some (Jal 0 388, 4%Z).
Proof. vm_refl. Qed.

Definition W_184b4 : bv 32 := 0x0002d517.
Lemma F_184b4 : fetch_word Ubsan.M.loaded_segments (0x184b4 : word) = Some W_184b4.
Proof. vm_refl. Qed.
Lemma D_184b4 : decode_any W_184b4 = Some (Auipc 10 45, 4%Z).
Proof. vm_refl. Qed.

Definition W_184b8 : bv 32 := 0x9e453503.
Lemma F_184b8 : fetch_word Ubsan.M.loaded_segments (0x184b8 : word) = Some W_184b8.
Proof. vm_refl. Qed.
Lemma D_184b8 : decode_any W_184b8 = Some (Load SZ8 true 10 10 2532, 4%Z).
Proof. vm_refl. Qed.

Definition W_184bc : bv 32 := 0x00052503.
Lemma F_184bc : fetch_word Ubsan.M.loaded_segments (0x184bc : word) = Some W_184bc.
Proof. vm_refl. Qed.
Lemma D_184bc : decode_any W_184bc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_184c0 : bv 32 := 0x00500593.
Lemma F_184c0 : fetch_word Ubsan.M.loaded_segments (0x184c0 : word) = Some W_184c0.
Proof. vm_refl. Qed.
Lemma D_184c0 : decode_any W_184c0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_184c4 : bv 32 := 0x18a5c863.
Lemma F_184c4 : fetch_word Ubsan.M.loaded_segments (0x184c4 : word) = Some W_184c4.
Proof. vm_refl. Qed.
Lemma D_184c4 : decode_any W_184c4 = Some (Branch BC_LT 11 10 400, 4%Z).
Proof. vm_refl. Qed.

Definition W_184c8 : bv 32 := 0xffff8517.
Lemma F_184c8 : fetch_word Ubsan.M.loaded_segments (0x184c8 : word) = Some W_184c8.
Proof. vm_refl. Qed.
Lemma D_184c8 : decode_any W_184c8 = Some (Auipc 10 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_184cc : bv 32 := 0xffff8597.
Lemma F_184cc : fetch_word Ubsan.M.loaded_segments (0x184cc : word) = Some W_184cc.
Proof. vm_refl. Qed.
Lemma D_184cc : decode_any W_184cc = Some (Auipc 11 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_184d0 : bv 32 := 0xf9d50513.
Lemma F_184d0 : fetch_word Ubsan.M.loaded_segments (0x184d0 : word) = Some W_184d0.
Proof. vm_refl. Qed.
Lemma D_184d0 : decode_any W_184d0 = Some (OpImm ALU_ADD 10 10 3997, 4%Z).
Proof. vm_refl. Qed.

Definition W_184d4 : bv 32 := 0x23858593.
Lemma F_184d4 : fetch_word Ubsan.M.loaded_segments (0x184d4 : word) = Some W_184d4.
Proof. vm_refl. Qed.
Lemma D_184d4 : decode_any W_184d4 = Some (OpImm ALU_ADD 11 11 568, 4%Z).
Proof. vm_refl. Qed.

Definition W_184d8 : bv 32 := 0x15c0006f.
Lemma F_184d8 : fetch_word Ubsan.M.loaded_segments (0x184d8 : word) = Some W_184d8.
Proof. vm_refl. Qed.
Lemma D_184d8 : decode_any W_184d8 = Some (Jal 0 348, 4%Z).
Proof. vm_refl. Qed.

Definition W_184dc : bv 32 := 0x00060413.
Lemma F_184dc : fetch_word Ubsan.M.loaded_segments (0x184dc : word) = Some W_184dc.
Proof. vm_refl. Qed.
Lemma D_184dc : decode_any W_184dc = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_184e0 : bv 32 := 0x00050493.
Lemma F_184e0 : fetch_word Ubsan.M.loaded_segments (0x184e0 : word) = Some W_184e0.
Proof. vm_refl. Qed.
Lemma D_184e0 : decode_any W_184e0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_184e4 : bv 32 := 0x00000513.
Lemma F_184e4 : fetch_word Ubsan.M.loaded_segments (0x184e4 : word) = Some W_184e4.
Proof. vm_refl. Qed.
Lemma D_184e4 : decode_any W_184e4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_184e8 : bv 32 := 0x62d010ef.
Lemma F_184e8 : fetch_word Ubsan.M.loaded_segments (0x184e8 : word) = Some W_184e8.
Proof. vm_refl. Qed.
Lemma D_184e8 : decode_any W_184e8 = Some (Jal 1 7724, 4%Z).
Proof. vm_refl. Qed.

Definition W_184ec : bv 32 := 0x0140006f.
Lemma F_184ec : fetch_word Ubsan.M.loaded_segments (0x184ec : word) = Some W_184ec.
Proof. vm_refl. Qed.
Lemma D_184ec : decode_any W_184ec = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_184f0 : bv 32 := 0x00060413.
Lemma F_184f0 : fetch_word Ubsan.M.loaded_segments (0x184f0 : word) = Some W_184f0.
Proof. vm_refl. Qed.
Lemma D_184f0 : decode_any W_184f0 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_184f4 : bv 32 := 0x00050493.
Lemma F_184f4 : fetch_word Ubsan.M.loaded_segments (0x184f4 : word) = Some W_184f4.
Proof. vm_refl. Qed.
Lemma D_184f4 : decode_any W_184f4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_184f8 : bv 32 := 0x00058513.
Lemma F_184f8 : fetch_word Ubsan.M.loaded_segments (0x184f8 : word) = Some W_184f8.
Proof. vm_refl. Qed.
Lemma D_184f8 : decode_any W_184f8 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_184fc : bv 32 := 0x5c5010ef.
Lemma F_184fc : fetch_word Ubsan.M.loaded_segments (0x184fc : word) = Some W_184fc.
Proof. vm_refl. Qed.
Lemma D_184fc : decode_any W_184fc = Some (Jal 1 7620, 4%Z).
Proof. vm_refl. Qed.

Definition W_18500 : bv 32 := 0x00050593.
Lemma F_18500 : fetch_word Ubsan.M.loaded_segments (0x18500 : word) = Some W_18500.
Proof. vm_refl. Qed.
Lemma D_18500 : decode_any W_18500 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18504 : bv 32 := 0x00a13023.
Lemma F_18504 : fetch_word Ubsan.M.loaded_segments (0x18504 : word) = Some W_18504.
Proof. vm_refl. Qed.
Lemma D_18504 : decode_any W_18504 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18508 : bv 32 := 0x00048513.
Lemma F_18508 : fetch_word Ubsan.M.loaded_segments (0x18508 : word) = Some W_18508.
Proof. vm_refl. Qed.
Lemma D_18508 : decode_any W_18508 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1850c : bv 32 := 0x00040613.
Lemma F_1850c : fetch_word Ubsan.M.loaded_segments (0x1850c : word) = Some W_1850c.
Proof. vm_refl. Qed.
Lemma D_1850c : decode_any W_1850c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18510 : bv 32 := 0x10058063.
Lemma F_18510 : fetch_word Ubsan.M.loaded_segments (0x18510 : word) = Some W_18510.
Proof. vm_refl. Qed.
Lemma D_18510 : decode_any W_18510 = Some (Branch BC_EQ 11 0 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_18514 : bv 32 := 0x00757693.
Lemma F_18514 : fetch_word Ubsan.M.loaded_segments (0x18514 : word) = Some W_18514.
Proof. vm_refl. Qed.
Lemma D_18514 : decode_any W_18514 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_18518 : bv 32 := 0x14069e63.
Lemma F_18518 : fetch_word Ubsan.M.loaded_segments (0x18518 : word) = Some W_18518.
Proof. vm_refl. Qed.
Lemma D_18518 : decode_any W_18518 = Some (Branch BC_NE 13 0 348, 4%Z).
Proof. vm_refl. Qed.

Definition W_1851c : bv 32 := 0x00052483.
Lemma F_1851c : fetch_word Ubsan.M.loaded_segments (0x1851c : word) = Some W_1851c.
Proof. vm_refl. Qed.
Lemma D_1851c : decode_any W_1851c = Some (Load SZ4 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18520 : bv 32 := 0x00452683.
Lemma F_18520 : fetch_word Ubsan.M.loaded_segments (0x18520 : word) = Some W_18520.
Proof. vm_refl. Qed.
Lemma D_18520 : decode_any W_18520 = Some (Load SZ4 true 13 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_18524 : bv 32 := 0x06d4c863.
Lemma F_18524 : fetch_word Ubsan.M.loaded_segments (0x18524 : word) = Some W_18524.
Proof. vm_refl. Qed.
Lemma D_18524 : decode_any W_18524 = Some (Branch BC_LT 9 13 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_18528 : bv 32 := 0x00058993.
Lemma F_18528 : fetch_word Ubsan.M.loaded_segments (0x18528 : word) = Some W_18528.
Proof. vm_refl. Qed.
Lemma D_18528 : decode_any W_18528 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1852c : bv 32 := 0x400005b7.
Lemma F_1852c : fetch_word Ubsan.M.loaded_segments (0x1852c : word) = Some W_1852c.
Proof. vm_refl. Qed.
Lemma D_1852c : decode_any W_1852c = Some (Lui 11 262144, 4%Z).
Proof. vm_refl. Qed.

Definition W_18530 : bv 32 := 0x00b685bb.
Lemma F_18530 : fetch_word Ubsan.M.loaded_segments (0x18530 : word) = Some W_18530.
Proof. vm_refl. Qed.
Lemma D_18530 : decode_any W_18530 = Some (Op32 ALU_ADD 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_18534 : bv 32 := 0x1405c063.
Lemma F_18534 : fetch_word Ubsan.M.loaded_segments (0x18534 : word) = Some W_18534.
Proof. vm_refl. Qed.
Lemma D_18534 : decode_any W_18534 = Some (Branch BC_LT 11 0 320, 4%Z).
Proof. vm_refl. Qed.

Definition W_18538 : bv 32 := 0x00060913.
Lemma F_18538 : fetch_word Ubsan.M.loaded_segments (0x18538 : word) = Some W_18538.
Proof. vm_refl. Qed.
Lemma D_18538 : decode_any W_18538 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1853c : bv 32 := 0x00169593.
Lemma F_1853c : fetch_word Ubsan.M.loaded_segments (0x1853c : word) = Some W_1853c.
Proof. vm_refl. Qed.
Lemma D_1853c : decode_any W_1853c = Some (ShiftImm ALU_SLL 11 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_18540 : bv 32 := 0x00050413.
Lemma F_18540 : fetch_word Ubsan.M.loaded_segments (0x18540 : word) = Some W_18540.
Proof. vm_refl. Qed.
Lemma D_18540 : decode_any W_18540 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18544 : bv 32 := 0x314000ef.
Lemma F_18544 : fetch_word Ubsan.M.loaded_segments (0x18544 : word) = Some W_18544.
Proof. vm_refl. Qed.
Lemma D_18544 : decode_any W_18544 = Some (Jal 1 788, 4%Z).
Proof. vm_refl. Qed.

Definition W_18548 : bv 32 := 0x00050613.
Lemma F_18548 : fetch_word Ubsan.M.loaded_segments (0x18548 : word) = Some W_18548.
Proof. vm_refl. Qed.
Lemma D_18548 : decode_any W_18548 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1854c : bv 32 := 0x00040513.
Lemma F_1854c : fetch_word Ubsan.M.loaded_segments (0x1854c : word) = Some W_1854c.
Proof. vm_refl. Qed.
Lemma D_1854c : decode_any W_1854c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18550 : bv 32 := 0x00098593.
Lemma F_18550 : fetch_word Ubsan.M.loaded_segments (0x18550 : word) = Some W_18550.
Proof. vm_refl. Qed.
Lemma D_18550 : decode_any W_18550 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18554 : bv 32 := 0x04060063.
Lemma F_18554 : fetch_word Ubsan.M.loaded_segments (0x18554 : word) = Some W_18554.
Proof. vm_refl. Qed.
Lemma D_18554 : decode_any W_18554 = Some (Branch BC_EQ 12 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_18558 : bv 32 := 0x00090663.
Lemma F_18558 : fetch_word Ubsan.M.loaded_segments (0x18558 : word) = Some W_18558.
Proof. vm_refl. Qed.
Lemma D_18558 : decode_any W_18558 = Some (Branch BC_EQ 18 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1855c : bv 32 := 0x00010513.
Lemma F_1855c : fetch_word Ubsan.M.loaded_segments (0x1855c : word) = Some W_1855c.
Proof. vm_refl. Qed.
Lemma D_1855c : decode_any W_1855c = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18560 : bv 32 := 0x2cc010ef.
Lemma F_18560 : fetch_word Ubsan.M.loaded_segments (0x18560 : word) = Some W_18560.
Proof. vm_refl. Qed.
Lemma D_18560 : decode_any W_18560 = Some (Jal 1 4812, 4%Z).
Proof. vm_refl. Qed.

Definition W_18564 : bv 32 := 0x0002d517.
Lemma F_18564 : fetch_word Ubsan.M.loaded_segments (0x18564 : word) = Some W_18564.
Proof. vm_refl. Qed.
Lemma D_18564 : decode_any W_18564 = Some (Auipc 10 45, 4%Z).
Proof. vm_refl. Qed.

Definition W_18568 : bv 32 := 0x93453503.
Lemma F_18568 : fetch_word Ubsan.M.loaded_segments (0x18568 : word) = Some W_18568.
Proof. vm_refl. Qed.
Lemma D_18568 : decode_any W_18568 = Some (Load SZ8 true 10 10 2356, 4%Z).
Proof. vm_refl. Qed.

Definition W_1856c : bv 32 := 0x00052503.
Lemma F_1856c : fetch_word Ubsan.M.loaded_segments (0x1856c : word) = Some W_1856c.
Proof. vm_refl. Qed.
Lemma D_1856c : decode_any W_1856c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18570 : bv 32 := 0x00500593.
Lemma F_18570 : fetch_word Ubsan.M.loaded_segments (0x18570 : word) = Some W_18570.
Proof. vm_refl. Qed.
Lemma D_18570 : decode_any W_18570 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_18574 : bv 32 := 0x0ea5c063.
Lemma F_18574 : fetch_word Ubsan.M.loaded_segments (0x18574 : word) = Some W_18574.
Proof. vm_refl. Qed.
Lemma D_18574 : decode_any W_18574 = Some (Branch BC_LT 11 10 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_18578 : bv 32 := 0xffff8517.
Lemma F_18578 : fetch_word Ubsan.M.loaded_segments (0x18578 : word) = Some W_18578.
Proof. vm_refl. Qed.
Lemma D_18578 : decode_any W_18578 = Some (Auipc 10 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_1857c : bv 32 := 0xffff8597.
Lemma F_1857c : fetch_word Ubsan.M.loaded_segments (0x1857c : word) = Some W_1857c.
Proof. vm_refl. Qed.
Lemma D_1857c : decode_any W_1857c = Some (Auipc 11 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_18580 : bv 32 := 0xd2050513.
Lemma F_18580 : fetch_word Ubsan.M.loaded_segments (0x18580 : word) = Some W_18580.
Proof. vm_refl. Qed.
Lemma D_18580 : decode_any W_18580 = Some (OpImm ALU_ADD 10 10 3360, 4%Z).
Proof. vm_refl. Qed.

Definition W_18584 : bv 32 := 0x18858593.
Lemma F_18584 : fetch_word Ubsan.M.loaded_segments (0x18584 : word) = Some W_18584.
Proof. vm_refl. Qed.
Lemma D_18584 : decode_any W_18584 = Some (OpImm ALU_ADD 11 11 392, 4%Z).
Proof. vm_refl. Qed.

Definition W_18588 : bv 32 := 0x00100613.
Lemma F_18588 : fetch_word Ubsan.M.loaded_segments (0x18588 : word) = Some W_18588.
Proof. vm_refl. Qed.
Lemma D_18588 : decode_any W_18588 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1858c : bv 32 := 0x869ff0ef.
Lemma F_1858c : fetch_word Ubsan.M.loaded_segments (0x1858c : word) = Some W_1858c.
Proof. vm_refl. Qed.
Lemma D_1858c : decode_any W_1858c = Some (Jal 1 2095208, 4%Z).
Proof. vm_refl. Qed.

Definition W_18590 : bv 32 := 0x0c80006f.
Lemma F_18590 : fetch_word Ubsan.M.loaded_segments (0x18590 : word) = Some W_18590.
Proof. vm_refl. Qed.
Lemma D_18590 : decode_any W_18590 = Some (Jal 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_18594 : bv 32 := 0x01053683.
Lemma F_18594 : fetch_word Ubsan.M.loaded_segments (0x18594 : word) = Some W_18594.
Proof. vm_refl. Qed.
Lemma D_18594 : decode_any W_18594 = Some (Load SZ8 true 13 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18598 : bv 32 := 0x00349613.
Lemma F_18598 : fetch_word Ubsan.M.loaded_segments (0x18598 : word) = Some W_18598.
Proof. vm_refl. Qed.
Lemma D_18598 : decode_any W_18598 = Some (ShiftImm ALU_SLL 12 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1859c : bv 32 := 0x00c68633.
Lemma F_1859c : fetch_word Ubsan.M.loaded_segments (0x1859c : word) = Some W_1859c.
Proof. vm_refl. Qed.
Lemma D_1859c : decode_any W_1859c = Some (Op ALU_ADD 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_185a0 : bv 32 := 0x00d03733.
Lemma F_185a0 : fetch_word Ubsan.M.loaded_segments (0x185a0 : word) = Some W_185a0.
Proof. vm_refl. Qed.
Lemma D_185a0 : decode_any W_185a0 = Some (Op ALU_SLTU 14 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_185a4 : bv 32 := 0x00163793.
Lemma F_185a4 : fetch_word Ubsan.M.loaded_segments (0x185a4 : word) = Some W_185a4.
Proof. vm_refl. Qed.
Lemma D_185a4 : decode_any W_185a4 = Some (OpImm ALU_SLTU 15 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_185a8 : bv 32 := 0x0cf70663.
Lemma F_185a8 : fetch_word Ubsan.M.loaded_segments (0x185a8 : word) = Some W_185a8.
Proof. vm_refl. Qed.
Lemma D_185a8 : decode_any W_185a8 = Some (Branch BC_EQ 14 15 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_185ac : bv 32 := 0x00d63733.
Lemma F_185ac : fetch_word Ubsan.M.loaded_segments (0x185ac : word) = Some W_185ac.
Proof. vm_refl. Qed.
Lemma D_185ac : decode_any W_185ac = Some (Op ALU_SLTU 14 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_185b0 : bv 32 := 0x0004a793.
Lemma F_185b0 : fetch_word Ubsan.M.loaded_segments (0x185b0 : word) = Some W_185b0.
Proof. vm_refl. Qed.
Lemma D_185b0 : decode_any W_185b0 = Some (OpImm ALU_SLT 15 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_185b4 : bv 32 := 0x00f74733.
Lemma F_185b4 : fetch_word Ubsan.M.loaded_segments (0x185b4 : word) = Some W_185b4.
Proof. vm_refl. Qed.
Lemma D_185b4 : decode_any W_185b4 = Some (Op ALU_XOR 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_185b8 : bv 32 := 0x00174713.
Lemma F_185b8 : fetch_word Ubsan.M.loaded_segments (0x185b8 : word) = Some W_185b8.
Proof. vm_refl. Qed.
Lemma D_185b8 : decode_any W_185b8 = Some (OpImm ALU_XOR 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_185bc : bv 32 := 0x0a070c63.
Lemma F_185bc : fetch_word Ubsan.M.loaded_segments (0x185bc : word) = Some W_185bc.
Proof. vm_refl. Qed.
Lemma D_185bc : decode_any W_185bc = Some (Branch BC_EQ 14 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_185c0 : bv 32 := 0x0a068a63.
Lemma F_185c0 : fetch_word Ubsan.M.loaded_segments (0x185c0 : word) = Some W_185c0.
Proof. vm_refl. Qed.
Lemma D_185c0 : decode_any W_185c0 = Some (Branch BC_EQ 13 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_185c4 : bv 32 := 0x00767693.
Lemma F_185c4 : fetch_word Ubsan.M.loaded_segments (0x185c4 : word) = Some W_185c4.
Proof. vm_refl. Qed.
Lemma D_185c4 : decode_any W_185c4 = Some (OpImm ALU_AND 13 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_185c8 : bv 32 := 0x0a069663.
Lemma F_185c8 : fetch_word Ubsan.M.loaded_segments (0x185c8 : word) = Some W_185c8.
Proof. vm_refl. Qed.
Lemma D_185c8 : decode_any W_185c8 = Some (Branch BC_NE 13 0 172, 4%Z).
Proof. vm_refl. Qed.

Definition W_185cc : bv 32 := 0x00052703.
Lemma F_185cc : fetch_word Ubsan.M.loaded_segments (0x185cc : word) = Some W_185cc.
Proof. vm_refl. Qed.
Lemma D_185cc : decode_any W_185cc = Some (Load SZ4 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_185d0 : bv 32 := 0x0017069b.
Lemma F_185d0 : fetch_word Ubsan.M.loaded_segments (0x185d0 : word) = Some W_185d0.
Proof. vm_refl. Qed.
Lemma D_185d0 : decode_any W_185d0 = Some (OpImm32 13 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_185d4 : bv 32 := 0x00b63023.
Lemma F_185d4 : fetch_word Ubsan.M.loaded_segments (0x185d4 : word) = Some W_185d4.
Proof. vm_refl. Qed.
Lemma D_185d4 : decode_any W_185d4 = Some (Store SZ8 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_185d8 : bv 32 := 0x08e6ce63.
Lemma F_185d8 : fetch_word Ubsan.M.loaded_segments (0x185d8 : word) = Some W_185d8.
Proof. vm_refl. Qed.
Lemma D_185d8 : decode_any W_185d8 = Some (Branch BC_LT 13 14 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_185dc : bv 32 := 0x00d52023.
Lemma F_185dc : fetch_word Ubsan.M.loaded_segments (0x185dc : word) = Some W_185dc.
Proof. vm_refl. Qed.
Lemma D_185dc : decode_any W_185dc = Some (Store SZ4 10 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_185e0 : bv 32 := 0x00000513.
Lemma F_185e0 : fetch_word Ubsan.M.loaded_segments (0x185e0 : word) = Some W_185e0.
Proof. vm_refl. Qed.
Lemma D_185e0 : decode_any W_185e0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_185e4 : bv 32 := 0x0740006f.
Lemma F_185e4 : fetch_word Ubsan.M.loaded_segments (0x185e4 : word) = Some W_185e4.
Proof. vm_refl. Qed.
Lemma D_185e4 : decode_any W_185e4 = Some (Jal 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_185e8 : bv 32 := 0x0002d517.
Lemma F_185e8 : fetch_word Ubsan.M.loaded_segments (0x185e8 : word) = Some W_185e8.
Proof. vm_refl. Qed.
Lemma D_185e8 : decode_any W_185e8 = Some (Auipc 10 45, 4%Z).
Proof. vm_refl. Qed.

Definition W_185ec : bv 32 := 0x8b053503.
Lemma F_185ec : fetch_word Ubsan.M.loaded_segments (0x185ec : word) = Some W_185ec.
Proof. vm_refl. Qed.
Lemma D_185ec : decode_any W_185ec = Some (Load SZ8 true 10 10 2224, 4%Z).
Proof. vm_refl. Qed.

Definition W_185f0 : bv 32 := 0x00052503.
Lemma F_185f0 : fetch_word Ubsan.M.loaded_segments (0x185f0 : word) = Some W_185f0.
Proof. vm_refl. Qed.
Lemma D_185f0 : decode_any W_185f0 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_185f4 : bv 32 := 0x00500593.
Lemma F_185f4 : fetch_word Ubsan.M.loaded_segments (0x185f4 : word) = Some W_185f4.
Proof. vm_refl. Qed.
Lemma D_185f4 : decode_any W_185f4 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_185f8 : bv 32 := 0x04a5ce63.
Lemma F_185f8 : fetch_word Ubsan.M.loaded_segments (0x185f8 : word) = Some W_185f8.
Proof. vm_refl. Qed.
Lemma D_185f8 : decode_any W_185f8 = Some (Branch BC_LT 11 10 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_185fc : bv 32 := 0xffff9517.
Lemma F_185fc : fetch_word Ubsan.M.loaded_segments (0x185fc : word) = Some W_185fc.
Proof. vm_refl. Qed.
Lemma D_185fc : decode_any W_185fc = Some (Auipc 10 1048569, 4%Z).
Proof. vm_refl. Qed.

Definition W_18600 : bv 32 := 0xffff8597.
Lemma F_18600 : fetch_word Ubsan.M.loaded_segments (0x18600 : word) = Some W_18600.
Proof. vm_refl. Qed.
Lemma D_18600 : decode_any W_18600 = Some (Auipc 11 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_18604 : bv 32 := 0xfea50513.
Lemma F_18604 : fetch_word Ubsan.M.loaded_segments (0x18604 : word) = Some W_18604.
Proof. vm_refl. Qed.
Lemma D_18604 : decode_any W_18604 = Some (OpImm ALU_ADD 10 10 4074, 4%Z).
Proof. vm_refl. Qed.

Definition W_18608 : bv 32 := 0x10458593.
Lemma F_18608 : fetch_word Ubsan.M.loaded_segments (0x18608 : word) = Some W_18608.
Proof. vm_refl. Qed.
Lemma D_18608 : decode_any W_18608 = Some (OpImm ALU_ADD 11 11 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_1860c : bv 32 := 0x0280006f.
Lemma F_1860c : fetch_word Ubsan.M.loaded_segments (0x1860c : word) = Some W_1860c.
Proof. vm_refl. Qed.
Lemma D_1860c : decode_any W_1860c = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_18610 : bv 32 := 0x0002d517.
Lemma F_18610 : fetch_word Ubsan.M.loaded_segments (0x18610 : word) = Some W_18610.
Proof. vm_refl. Qed.
Lemma D_18610 : decode_any W_18610 = Some (Auipc 10 45, 4%Z).
Proof. vm_refl. Qed.

Definition W_18614 : bv 32 := 0x88853503.
Lemma F_18614 : fetch_word Ubsan.M.loaded_segments (0x18614 : word) = Some W_18614.
Proof. vm_refl. Qed.
Lemma D_18614 : decode_any W_18614 = Some (Load SZ8 true 10 10 2184, 4%Z).
Proof. vm_refl. Qed.

Definition W_18618 : bv 32 := 0x00052503.
Lemma F_18618 : fetch_word Ubsan.M.loaded_segments (0x18618 : word) = Some W_18618.
Proof. vm_refl. Qed.
Lemma D_18618 : decode_any W_18618 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1861c : bv 32 := 0x00500593.
Lemma F_1861c : fetch_word Ubsan.M.loaded_segments (0x1861c : word) = Some W_1861c.
Proof. vm_refl. Qed.
Lemma D_1861c : decode_any W_1861c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_18620 : bv 32 := 0x02a5ca63.
Lemma F_18620 : fetch_word Ubsan.M.loaded_segments (0x18620 : word) = Some W_18620.
Proof. vm_refl. Qed.
Lemma D_18620 : decode_any W_18620 = Some (Branch BC_LT 11 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_18624 : bv 32 := 0xffffa517.
Lemma F_18624 : fetch_word Ubsan.M.loaded_segments (0x18624 : word) = Some W_18624.
Proof. vm_refl. Qed.
Lemma D_18624 : decode_any W_18624 = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

Definition W_18628 : bv 32 := 0xffff8597.
Lemma F_18628 : fetch_word Ubsan.M.loaded_segments (0x18628 : word) = Some W_18628.
Proof. vm_refl. Qed.
Lemma D_18628 : decode_any W_18628 = Some (Auipc 11 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_1862c : bv 32 := 0xce550513.
Lemma F_1862c : fetch_word Ubsan.M.loaded_segments (0x1862c : word) = Some W_1862c.
Proof. vm_refl. Qed.
Lemma D_1862c : decode_any W_1862c = Some (OpImm ALU_ADD 10 10 3301, 4%Z).
Proof. vm_refl. Qed.

Definition W_18630 : bv 32 := 0x0dc58593.
Lemma F_18630 : fetch_word Ubsan.M.loaded_segments (0x18630 : word) = Some W_18630.
Proof. vm_refl. Qed.
Lemma D_18630 : decode_any W_18630 = Some (OpImm ALU_ADD 11 11 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_18634 : bv 32 := 0x00100613.
Lemma F_18634 : fetch_word Ubsan.M.loaded_segments (0x18634 : word) = Some W_18634.
Proof. vm_refl. Qed.
Lemma D_18634 : decode_any W_18634 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_18638 : bv 32 := 0x02813083.
Lemma F_18638 : fetch_word Ubsan.M.loaded_segments (0x18638 : word) = Some W_18638.
Proof. vm_refl. Qed.
Lemma D_18638 : decode_any W_18638 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1863c : bv 32 := 0x02013403.
Lemma F_1863c : fetch_word Ubsan.M.loaded_segments (0x1863c : word) = Some W_1863c.
Proof. vm_refl. Qed.
Lemma D_1863c : decode_any W_1863c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18640 : bv 32 := 0x01813483.
Lemma F_18640 : fetch_word Ubsan.M.loaded_segments (0x18640 : word) = Some W_18640.
Proof. vm_refl. Qed.
Lemma D_18640 : decode_any W_18640 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18644 : bv 32 := 0x01013903.
Lemma F_18644 : fetch_word Ubsan.M.loaded_segments (0x18644 : word) = Some W_18644.
Proof. vm_refl. Qed.
Lemma D_18644 : decode_any W_18644 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18648 : bv 32 := 0x00813983.
Lemma F_18648 : fetch_word Ubsan.M.loaded_segments (0x18648 : word) = Some W_18648.
Proof. vm_refl. Qed.
Lemma D_18648 : decode_any W_18648 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1864c : bv 32 := 0x03010113.
Lemma F_1864c : fetch_word Ubsan.M.loaded_segments (0x1864c : word) = Some W_1864c.
Proof. vm_refl. Qed.
Lemma D_1864c : decode_any W_1864c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_18650 : bv 32 := 0xfa4ff06f.
Lemma F_18650 : fetch_word Ubsan.M.loaded_segments (0x18650 : word) = Some W_18650.
Proof. vm_refl. Qed.
Lemma D_18650 : decode_any W_18650 = Some (Jal 0 2095012, 4%Z).
Proof. vm_refl. Qed.

Definition W_18654 : bv 32 := 0x00100513.
Lemma F_18654 : fetch_word Ubsan.M.loaded_segments (0x18654 : word) = Some W_18654.
Proof. vm_refl. Qed.
Lemma D_18654 : decode_any W_18654 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_18658 : bv 32 := 0x02813083.
Lemma F_18658 : fetch_word Ubsan.M.loaded_segments (0x18658 : word) = Some W_18658.
Proof. vm_refl. Qed.
Lemma D_18658 : decode_any W_18658 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1865c : bv 32 := 0x02013403.
Lemma F_1865c : fetch_word Ubsan.M.loaded_segments (0x1865c : word) = Some W_1865c.
Proof. vm_refl. Qed.
Lemma D_1865c : decode_any W_1865c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18660 : bv 32 := 0x01813483.
Lemma F_18660 : fetch_word Ubsan.M.loaded_segments (0x18660 : word) = Some W_18660.
Proof. vm_refl. Qed.
Lemma D_18660 : decode_any W_18660 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18664 : bv 32 := 0x01013903.
Lemma F_18664 : fetch_word Ubsan.M.loaded_segments (0x18664 : word) = Some W_18664.
Proof. vm_refl. Qed.
Lemma D_18664 : decode_any W_18664 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18668 : bv 32 := 0x00813983.
Lemma F_18668 : fetch_word Ubsan.M.loaded_segments (0x18668 : word) = Some W_18668.
Proof. vm_refl. Qed.
Lemma D_18668 : decode_any W_18668 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1866c : bv 32 := 0x03010113.
Lemma F_1866c : fetch_word Ubsan.M.loaded_segments (0x1866c : word) = Some W_1866c.
Proof. vm_refl. Qed.
Lemma D_1866c : decode_any W_1866c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_18670 : bv 32 := 0x00008067.
Lemma F_18670 : fetch_word Ubsan.M.loaded_segments (0x18670 : word) = Some W_18670.
Proof. vm_refl. Qed.
Lemma D_18670 : decode_any W_18670 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

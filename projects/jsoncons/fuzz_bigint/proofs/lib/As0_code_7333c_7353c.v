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

Definition W_7333c : bv 32 := 0xfd010113.
Lemma F_7333c : fetch_word Asan.M.loaded_segments (0x7333c : word) = Some W_7333c.
Proof. vm_refl. Qed.
Lemma D_7333c : decode_any W_7333c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_73340 : bv 32 := 0x02113423.
Lemma F_73340 : fetch_word Asan.M.loaded_segments (0x73340 : word) = Some W_73340.
Proof. vm_refl. Qed.
Lemma D_73340 : decode_any W_73340 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_73344 : bv 32 := 0x02813023.
Lemma F_73344 : fetch_word Asan.M.loaded_segments (0x73344 : word) = Some W_73344.
Proof. vm_refl. Qed.
Lemma D_73344 : decode_any W_73344 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_73348 : bv 32 := 0x00913c23.
Lemma F_73348 : fetch_word Asan.M.loaded_segments (0x73348 : word) = Some W_73348.
Proof. vm_refl. Qed.
Lemma D_73348 : decode_any W_73348 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7334c : bv 32 := 0x01213823.
Lemma F_7334c : fetch_word Asan.M.loaded_segments (0x7334c : word) = Some W_7334c.
Proof. vm_refl. Qed.
Lemma D_7334c : decode_any W_7334c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_73350 : bv 32 := 0x00060413.
Lemma F_73350 : fetch_word Asan.M.loaded_segments (0x73350 : word) = Some W_73350.
Proof. vm_refl. Qed.
Lemma D_73350 : decode_any W_73350 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73354 : bv 32 := 0x00058493.
Lemma F_73354 : fetch_word Asan.M.loaded_segments (0x73354 : word) = Some W_73354.
Proof. vm_refl. Qed.
Lemma D_73354 : decode_any W_73354 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73358 : bv 32 := 0x00050913.
Lemma F_73358 : fetch_word Asan.M.loaded_segments (0x73358 : word) = Some W_73358.
Proof. vm_refl. Qed.
Lemma D_73358 : decode_any W_73358 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7335c : bv 32 := 0x00d12623.
Lemma F_7335c : fetch_word Asan.M.loaded_segments (0x7335c : word) = Some W_7335c.
Proof. vm_refl. Qed.
Lemma D_7335c : decode_any W_7335c = Some (Store SZ4 2 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_73360 : bv 32 := 0x00c10613.
Lemma F_73360 : fetch_word Asan.M.loaded_segments (0x73360 : word) = Some W_73360.
Proof. vm_refl. Qed.
Lemma D_73360 : decode_any W_73360 = Some (OpImm ALU_ADD 12 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_73364 : bv 32 := 0x00070513.
Lemma F_73364 : fetch_word Asan.M.loaded_segments (0x73364 : word) = Some W_73364.
Proof. vm_refl. Qed.
Lemma D_73364 : decode_any W_73364 = Some (OpImm ALU_ADD 10 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73368 : bv 32 := 0x3a5000ef.
Lemma F_73368 : fetch_word Asan.M.loaded_segments (0x73368 : word) = Some W_73368.
Proof. vm_refl. Qed.
Lemma D_73368 : decode_any W_73368 = Some (Jal 1 2980, 4%Z).
Proof. vm_refl. Qed.

Definition W_7336c : bv 32 := 0x00c12683.
Lemma F_7336c : fetch_word Asan.M.loaded_segments (0x7336c : word) = Some W_7336c.
Proof. vm_refl. Qed.
Lemma D_7336c : decode_any W_7336c = Some (Load SZ4 true 13 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_73370 : bv 32 := 0x00050713.
Lemma F_73370 : fetch_word Asan.M.loaded_segments (0x73370 : word) = Some W_73370.
Proof. vm_refl. Qed.
Lemma D_73370 : decode_any W_73370 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73374 : bv 32 := 0x00090513.
Lemma F_73374 : fetch_word Asan.M.loaded_segments (0x73374 : word) = Some W_73374.
Proof. vm_refl. Qed.
Lemma D_73374 : decode_any W_73374 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73378 : bv 32 := 0x00048593.
Lemma F_73378 : fetch_word Asan.M.loaded_segments (0x73378 : word) = Some W_73378.
Proof. vm_refl. Qed.
Lemma D_73378 : decode_any W_73378 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7337c : bv 32 := 0x00040613.
Lemma F_7337c : fetch_word Asan.M.loaded_segments (0x7337c : word) = Some W_7337c.
Proof. vm_refl. Qed.
Lemma D_7337c : decode_any W_7337c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73380 : bv 32 := 0x00000793.
Lemma F_73380 : fetch_word Asan.M.loaded_segments (0x73380 : word) = Some W_73380.
Proof. vm_refl. Qed.
Lemma D_73380 : decode_any W_73380 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73384 : bv 32 := 0xfdcfe0ef.
Lemma F_73384 : fetch_word Asan.M.loaded_segments (0x73384 : word) = Some W_73384.
Proof. vm_refl. Qed.
Lemma D_73384 : decode_any W_73384 = Some (Jal 1 2090972, 4%Z).
Proof. vm_refl. Qed.

Definition W_73388 : bv 32 := 0x00050413.
Lemma F_73388 : fetch_word Asan.M.loaded_segments (0x73388 : word) = Some W_73388.
Proof. vm_refl. Qed.
Lemma D_73388 : decode_any W_73388 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7338c : bv 32 := 0x00000593.
Lemma F_7338c : fetch_word Asan.M.loaded_segments (0x7338c : word) = Some W_7338c.
Proof. vm_refl. Qed.
Lemma D_7338c : decode_any W_7338c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73390 : bv 32 := 0xfb0fe0ef.
Lemma F_73390 : fetch_word Asan.M.loaded_segments (0x73390 : word) = Some W_73390.
Proof. vm_refl. Qed.
Lemma D_73390 : decode_any W_73390 = Some (Jal 1 2090928, 4%Z).
Proof. vm_refl. Qed.

Definition W_73394 : bv 32 := 0x00040513.
Lemma F_73394 : fetch_word Asan.M.loaded_segments (0x73394 : word) = Some W_73394.
Proof. vm_refl. Qed.
Lemma D_73394 : decode_any W_73394 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73398 : bv 32 := 0x02813083.
Lemma F_73398 : fetch_word Asan.M.loaded_segments (0x73398 : word) = Some W_73398.
Proof. vm_refl. Qed.
Lemma D_73398 : decode_any W_73398 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7339c : bv 32 := 0x02013403.
Lemma F_7339c : fetch_word Asan.M.loaded_segments (0x7339c : word) = Some W_7339c.
Proof. vm_refl. Qed.
Lemma D_7339c : decode_any W_7339c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_733a0 : bv 32 := 0x01813483.
Lemma F_733a0 : fetch_word Asan.M.loaded_segments (0x733a0 : word) = Some W_733a0.
Proof. vm_refl. Qed.
Lemma D_733a0 : decode_any W_733a0 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_733a4 : bv 32 := 0x01013903.
Lemma F_733a4 : fetch_word Asan.M.loaded_segments (0x733a4 : word) = Some W_733a4.
Proof. vm_refl. Qed.
Lemma D_733a4 : decode_any W_733a4 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_733a8 : bv 32 := 0x03010113.
Lemma F_733a8 : fetch_word Asan.M.loaded_segments (0x733a8 : word) = Some W_733a8.
Proof. vm_refl. Qed.
Lemma D_733a8 : decode_any W_733a8 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_733ac : bv 32 := 0x00008067.
Lemma F_733ac : fetch_word Asan.M.loaded_segments (0x733ac : word) = Some W_733ac.
Proof. vm_refl. Qed.
Lemma D_733ac : decode_any W_733ac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_733b0 : bv 32 := 0xfd010113.
Lemma F_733b0 : fetch_word Asan.M.loaded_segments (0x733b0 : word) = Some W_733b0.
Proof. vm_refl. Qed.
Lemma D_733b0 : decode_any W_733b0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_733b4 : bv 32 := 0x02113423.
Lemma F_733b4 : fetch_word Asan.M.loaded_segments (0x733b4 : word) = Some W_733b4.
Proof. vm_refl. Qed.
Lemma D_733b4 : decode_any W_733b4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_733b8 : bv 32 := 0x02813023.
Lemma F_733b8 : fetch_word Asan.M.loaded_segments (0x733b8 : word) = Some W_733b8.
Proof. vm_refl. Qed.
Lemma D_733b8 : decode_any W_733b8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_733bc : bv 32 := 0x00913c23.
Lemma F_733bc : fetch_word Asan.M.loaded_segments (0x733bc : word) = Some W_733bc.
Proof. vm_refl. Qed.
Lemma D_733bc : decode_any W_733bc = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_733c0 : bv 32 := 0x01213823.
Lemma F_733c0 : fetch_word Asan.M.loaded_segments (0x733c0 : word) = Some W_733c0.
Proof. vm_refl. Qed.
Lemma D_733c0 : decode_any W_733c0 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_733c4 : bv 32 := 0x02050e63.
Lemma F_733c4 : fetch_word Asan.M.loaded_segments (0x733c4 : word) = Some W_733c4.
Proof. vm_refl. Qed.
Lemma D_733c4 : decode_any W_733c4 = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_733c8 : bv 32 := 0x00058413.
Lemma F_733c8 : fetch_word Asan.M.loaded_segments (0x733c8 : word) = Some W_733c8.
Proof. vm_refl. Qed.
Lemma D_733c8 : decode_any W_733c8 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_733cc : bv 32 := 0x02058a63.
Lemma F_733cc : fetch_word Asan.M.loaded_segments (0x733cc : word) = Some W_733cc.
Proof. vm_refl. Qed.
Lemma D_733cc : decode_any W_733cc = Some (Branch BC_EQ 11 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_733d0 : bv 32 := 0x00060493.
Lemma F_733d0 : fetch_word Asan.M.loaded_segments (0x733d0 : word) = Some W_733d0.
Proof. vm_refl. Qed.
Lemma D_733d0 : decode_any W_733d0 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_733d4 : bv 32 := 0x00050913.
Lemma F_733d4 : fetch_word Asan.M.loaded_segments (0x733d4 : word) = Some W_733d4.
Proof. vm_refl. Qed.
Lemma D_733d4 : decode_any W_733d4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_733d8 : bv 32 := 0x00040593.
Lemma F_733d8 : fetch_word Asan.M.loaded_segments (0x733d8 : word) = Some W_733d8.
Proof. vm_refl. Qed.
Lemma D_733d8 : decode_any W_733d8 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_733dc : bv 32 := 0xf90fe0ef.
Lemma F_733dc : fetch_word Asan.M.loaded_segments (0x733dc : word) = Some W_733dc.
Proof. vm_refl. Qed.
Lemma D_733dc : decode_any W_733dc = Some (Jal 1 2090896, 4%Z).
Proof. vm_refl. Qed.

Definition W_733e0 : bv 32 := 0xaaaab5b7.
Lemma F_733e0 : fetch_word Asan.M.loaded_segments (0x733e0 : word) = Some W_733e0.
Proof. vm_refl. Qed.
Lemma D_733e0 : decode_any W_733e0 = Some (Lui 11 699051, 4%Z).
Proof. vm_refl. Qed.

Definition W_733e4 : bv 32 := 0xaaa58593.
Lemma F_733e4 : fetch_word Asan.M.loaded_segments (0x733e4 : word) = Some W_733e4.
Proof. vm_refl. Qed.
Lemma D_733e4 : decode_any W_733e4 = Some (OpImm ALU_ADD 11 11 2730, 4%Z).
Proof. vm_refl. Qed.

Definition W_733e8 : bv 32 := 0x00b12623.
Lemma F_733e8 : fetch_word Asan.M.loaded_segments (0x733e8 : word) = Some W_733e8.
Proof. vm_refl. Qed.
Lemma D_733e8 : decode_any W_733e8 = Some (Store SZ4 2 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_733ec : bv 32 := 0x00c10593.
Lemma F_733ec : fetch_word Asan.M.loaded_segments (0x733ec : word) = Some W_733ec.
Proof. vm_refl. Qed.
Lemma D_733ec : decode_any W_733ec = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_733f0 : bv 32 := 0xf50fe0ef.
Lemma F_733f0 : fetch_word Asan.M.loaded_segments (0x733f0 : word) = Some W_733f0.
Proof. vm_refl. Qed.
Lemma D_733f0 : decode_any W_733f0 = Some (Jal 1 2090832, 4%Z).
Proof. vm_refl. Qed.

Definition W_733f4 : bv 32 := 0x02051263.
Lemma F_733f4 : fetch_word Asan.M.loaded_segments (0x733f4 : word) = Some W_733f4.
Proof. vm_refl. Qed.
Lemma D_733f4 : decode_any W_733f4 = Some (Branch BC_NE 10 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_733f8 : bv 32 := 0x00040513.
Lemma F_733f8 : fetch_word Asan.M.loaded_segments (0x733f8 : word) = Some W_733f8.
Proof. vm_refl. Qed.
Lemma D_733f8 : decode_any W_733f8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_733fc : bv 32 := 0xe8cfa0ef.
Lemma F_733fc : fetch_word Asan.M.loaded_segments (0x733fc : word) = Some W_733fc.
Proof. vm_refl. Qed.
Lemma D_733fc : decode_any W_733fc = Some (Jal 1 2074252, 4%Z).
Proof. vm_refl. Qed.

Definition W_73400 : bv 32 := 0x02813083.
Lemma F_73400 : fetch_word Asan.M.loaded_segments (0x73400 : word) = Some W_73400.
Proof. vm_refl. Qed.
Lemma D_73400 : decode_any W_73400 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_73404 : bv 32 := 0x02013403.
Lemma F_73404 : fetch_word Asan.M.loaded_segments (0x73404 : word) = Some W_73404.
Proof. vm_refl. Qed.
Lemma D_73404 : decode_any W_73404 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_73408 : bv 32 := 0x01813483.
Lemma F_73408 : fetch_word Asan.M.loaded_segments (0x73408 : word) = Some W_73408.
Proof. vm_refl. Qed.
Lemma D_73408 : decode_any W_73408 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7340c : bv 32 := 0x01013903.
Lemma F_7340c : fetch_word Asan.M.loaded_segments (0x7340c : word) = Some W_7340c.
Proof. vm_refl. Qed.
Lemma D_7340c : decode_any W_7340c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_73410 : bv 32 := 0x03010113.
Lemma F_73410 : fetch_word Asan.M.loaded_segments (0x73410 : word) = Some W_73410.
Proof. vm_refl. Qed.
Lemma D_73410 : decode_any W_73410 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_73414 : bv 32 := 0x00008067.
Lemma F_73414 : fetch_word Asan.M.loaded_segments (0x73414 : word) = Some W_73414.
Proof. vm_refl. Qed.
Lemma D_73414 : decode_any W_73414 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73418 : bv 32 := 0x00c12603.
Lemma F_73418 : fetch_word Asan.M.loaded_segments (0x73418 : word) = Some W_73418.
Proof. vm_refl. Qed.
Lemma D_73418 : decode_any W_73418 = Some (Load SZ4 true 12 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7341c : bv 32 := 0x00090513.
Lemma F_7341c : fetch_word Asan.M.loaded_segments (0x7341c : word) = Some W_7341c.
Proof. vm_refl. Qed.
Lemma D_7341c : decode_any W_7341c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73420 : bv 32 := 0x00040593.
Lemma F_73420 : fetch_word Asan.M.loaded_segments (0x73420 : word) = Some W_73420.
Proof. vm_refl. Qed.
Lemma D_73420 : decode_any W_73420 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73424 : bv 32 := 0x00048693.
Lemma F_73424 : fetch_word Asan.M.loaded_segments (0x73424 : word) = Some W_73424.
Proof. vm_refl. Qed.
Lemma D_73424 : decode_any W_73424 = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73428 : bv 32 := 0x85cfa0ef.
Lemma F_73428 : fetch_word Asan.M.loaded_segments (0x73428 : word) = Some W_73428.
Proof. vm_refl. Qed.
Lemma D_73428 : decode_any W_73428 = Some (Jal 1 2072668, 4%Z).
Proof. vm_refl. Qed.

Definition W_7342c : bv 32 := 0xfd010113.
Lemma F_7342c : fetch_word Asan.M.loaded_segments (0x7342c : word) = Some W_7342c.
Proof. vm_refl. Qed.
Lemma D_7342c : decode_any W_7342c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_73430 : bv 32 := 0x02113423.
Lemma F_73430 : fetch_word Asan.M.loaded_segments (0x73430 : word) = Some W_73430.
Proof. vm_refl. Qed.
Lemma D_73430 : decode_any W_73430 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_73434 : bv 32 := 0x02813023.
Lemma F_73434 : fetch_word Asan.M.loaded_segments (0x73434 : word) = Some W_73434.
Proof. vm_refl. Qed.
Lemma D_73434 : decode_any W_73434 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_73438 : bv 32 := 0x00913c23.
Lemma F_73438 : fetch_word Asan.M.loaded_segments (0x73438 : word) = Some W_73438.
Proof. vm_refl. Qed.
Lemma D_73438 : decode_any W_73438 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7343c : bv 32 := 0x01213823.
Lemma F_7343c : fetch_word Asan.M.loaded_segments (0x7343c : word) = Some W_7343c.
Proof. vm_refl. Qed.
Lemma D_7343c : decode_any W_7343c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_73440 : bv 32 := 0x00058413.
Lemma F_73440 : fetch_word Asan.M.loaded_segments (0x73440 : word) = Some W_73440.
Proof. vm_refl. Qed.
Lemma D_73440 : decode_any W_73440 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73444 : bv 32 := 0x00062597.
Lemma F_73444 : fetch_word Asan.M.loaded_segments (0x73444 : word) = Some W_73444.
Proof. vm_refl. Qed.
Lemma D_73444 : decode_any W_73444 = Some (Auipc 11 98, 4%Z).
Proof. vm_refl. Qed.

Definition W_73448 : bv 32 := 0x4545b903.
Lemma F_73448 : fetch_word Asan.M.loaded_segments (0x73448 : word) = Some W_73448.
Proof. vm_refl. Qed.
Lemma D_73448 : decode_any W_73448 = Some (Load SZ8 true 18 11 1108, 4%Z).
Proof. vm_refl. Qed.

Definition W_7344c : bv 32 := 0x00093583.
Lemma F_7344c : fetch_word Asan.M.loaded_segments (0x7344c : word) = Some W_7344c.
Proof. vm_refl. Qed.
Lemma D_7344c : decode_any W_7344c = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73450 : bv 32 := 0x00050493.
Lemma F_73450 : fetch_word Asan.M.loaded_segments (0x73450 : word) = Some W_73450.
Proof. vm_refl. Qed.
Lemma D_73450 : decode_any W_73450 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73454 : bv 32 := 0x00059863.
Lemma F_73454 : fetch_word Asan.M.loaded_segments (0x73454 : word) = Some W_73454.
Proof. vm_refl. Qed.
Lemma D_73454 : decode_any W_73454 = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_73458 : bv 32 := 0xe34ff0ef.
Lemma F_73458 : fetch_word Asan.M.loaded_segments (0x73458 : word) = Some W_73458.
Proof. vm_refl. Qed.
Lemma D_73458 : decode_any W_73458 = Some (Jal 1 2094644, 4%Z).
Proof. vm_refl. Qed.

Definition W_7345c : bv 32 := 0x00050593.
Lemma F_7345c : fetch_word Asan.M.loaded_segments (0x7345c : word) = Some W_7345c.
Proof. vm_refl. Qed.
Lemma D_7345c : decode_any W_7345c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73460 : bv 32 := 0x00a93023.
Lemma F_73460 : fetch_word Asan.M.loaded_segments (0x73460 : word) = Some W_73460.
Proof. vm_refl. Qed.
Lemma D_73460 : decode_any W_73460 = Some (Store SZ8 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73464 : bv 32 := 0xfff58513.
Lemma F_73464 : fetch_word Asan.M.loaded_segments (0x73464 : word) = Some W_73464.
Proof. vm_refl. Qed.
Lemma D_73464 : decode_any W_73464 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_73468 : bv 32 := 0x00a5f533.
Lemma F_73468 : fetch_word Asan.M.loaded_segments (0x73468 : word) = Some W_73468.
Proof. vm_refl. Qed.
Lemma D_73468 : decode_any W_73468 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7346c : bv 32 := 0x08051a63.
Lemma F_7346c : fetch_word Asan.M.loaded_segments (0x7346c : word) = Some W_7346c.
Proof. vm_refl. Qed.
Lemma D_7346c : decode_any W_7346c = Some (Branch BC_NE 10 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_73470 : bv 32 := 0x00b484b3.
Lemma F_73470 : fetch_word Asan.M.loaded_segments (0x73470 : word) = Some W_73470.
Proof. vm_refl. Qed.
Lemma D_73470 : decode_any W_73470 = Some (Op ALU_ADD 9 9 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_73474 : bv 32 := 0x40b00533.
Lemma F_73474 : fetch_word Asan.M.loaded_segments (0x73474 : word) = Some W_73474.
Proof. vm_refl. Qed.
Lemma D_73474 : decode_any W_73474 = Some (Op ALU_SUB 10 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_73478 : bv 32 := 0xfff48493.
Lemma F_73478 : fetch_word Asan.M.loaded_segments (0x73478 : word) = Some W_73478.
Proof. vm_refl. Qed.
Lemma D_73478 : decode_any W_73478 = Some (OpImm ALU_ADD 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7347c : bv 32 := 0x00a4f4b3.
Lemma F_7347c : fetch_word Asan.M.loaded_segments (0x7347c : word) = Some W_7347c.
Proof. vm_refl. Qed.
Lemma D_7347c : decode_any W_7347c = Some (Op ALU_AND 9 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_73480 : bv 32 := 0x02200513.
Lemma F_73480 : fetch_word Asan.M.loaded_segments (0x73480 : word) = Some W_73480.
Proof. vm_refl. Qed.
Lemma D_73480 : decode_any W_73480 = Some (OpImm ALU_ADD 10 0 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_73484 : bv 32 := 0x00a12623.
Lemma F_73484 : fetch_word Asan.M.loaded_segments (0x73484 : word) = Some W_73484.
Proof. vm_refl. Qed.
Lemma D_73484 : decode_any W_73484 = Some (Store SZ4 2 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_73488 : bv 32 := 0x00c10613.
Lemma F_73488 : fetch_word Asan.M.loaded_segments (0x73488 : word) = Some W_73488.
Proof. vm_refl. Qed.
Lemma D_73488 : decode_any W_73488 = Some (OpImm ALU_ADD 12 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7348c : bv 32 := 0x00040513.
Lemma F_7348c : fetch_word Asan.M.loaded_segments (0x7348c : word) = Some W_7348c.
Proof. vm_refl. Qed.
Lemma D_7348c : decode_any W_7348c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73490 : bv 32 := 0x00048593.
Lemma F_73490 : fetch_word Asan.M.loaded_segments (0x73490 : word) = Some W_73490.
Proof. vm_refl. Qed.
Lemma D_73490 : decode_any W_73490 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73494 : bv 32 := 0x279000ef.
Lemma F_73494 : fetch_word Asan.M.loaded_segments (0x73494 : word) = Some W_73494.
Proof. vm_refl. Qed.
Lemma D_73494 : decode_any W_73494 = Some (Jal 1 2680, 4%Z).
Proof. vm_refl. Qed.

Definition W_73498 : bv 32 := 0x00c12683.
Lemma F_73498 : fetch_word Asan.M.loaded_segments (0x73498 : word) = Some W_73498.
Proof. vm_refl. Qed.
Lemma D_73498 : decode_any W_73498 = Some (Load SZ4 true 13 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7349c : bv 32 := 0x00050713.
Lemma F_7349c : fetch_word Asan.M.loaded_segments (0x7349c : word) = Some W_7349c.
Proof. vm_refl. Qed.
Lemma D_7349c : decode_any W_7349c = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_734a0 : bv 32 := 0x00300613.
Lemma F_734a0 : fetch_word Asan.M.loaded_segments (0x734a0 : word) = Some W_734a0.
Proof. vm_refl. Qed.
Lemma D_734a0 : decode_any W_734a0 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_734a4 : bv 32 := 0x00000513.
Lemma F_734a4 : fetch_word Asan.M.loaded_segments (0x734a4 : word) = Some W_734a4.
Proof. vm_refl. Qed.
Lemma D_734a4 : decode_any W_734a4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_734a8 : bv 32 := 0x00048593.
Lemma F_734a8 : fetch_word Asan.M.loaded_segments (0x734a8 : word) = Some W_734a8.
Proof. vm_refl. Qed.
Lemma D_734a8 : decode_any W_734a8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_734ac : bv 32 := 0x00000793.
Lemma F_734ac : fetch_word Asan.M.loaded_segments (0x734ac : word) = Some W_734ac.
Proof. vm_refl. Qed.
Lemma D_734ac : decode_any W_734ac = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_734b0 : bv 32 := 0xeb0fe0ef.
Lemma F_734b0 : fetch_word Asan.M.loaded_segments (0x734b0 : word) = Some W_734b0.
Proof. vm_refl. Qed.
Lemma D_734b0 : decode_any W_734b0 = Some (Jal 1 2090672, 4%Z).
Proof. vm_refl. Qed.

Definition W_734b4 : bv 32 := 0x00050913.
Lemma F_734b4 : fetch_word Asan.M.loaded_segments (0x734b4 : word) = Some W_734b4.
Proof. vm_refl. Qed.
Lemma D_734b4 : decode_any W_734b4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_734b8 : bv 32 := 0x00000593.
Lemma F_734b8 : fetch_word Asan.M.loaded_segments (0x734b8 : word) = Some W_734b8.
Proof. vm_refl. Qed.
Lemma D_734b8 : decode_any W_734b8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_734bc : bv 32 := 0xe84fe0ef.
Lemma F_734bc : fetch_word Asan.M.loaded_segments (0x734bc : word) = Some W_734bc.
Proof. vm_refl. Qed.
Lemma D_734bc : decode_any W_734bc = Some (Jal 1 2090628, 4%Z).
Proof. vm_refl. Qed.

Definition W_734c0 : bv 32 := 0xaaaab537.
Lemma F_734c0 : fetch_word Asan.M.loaded_segments (0x734c0 : word) = Some W_734c0.
Proof. vm_refl. Qed.
Lemma D_734c0 : decode_any W_734c0 = Some (Lui 10 699051, 4%Z).
Proof. vm_refl. Qed.

Definition W_734c4 : bv 32 := 0xaaa50513.
Lemma F_734c4 : fetch_word Asan.M.loaded_segments (0x734c4 : word) = Some W_734c4.
Proof. vm_refl. Qed.
Lemma D_734c4 : decode_any W_734c4 = Some (OpImm ALU_ADD 10 10 2730, 4%Z).
Proof. vm_refl. Qed.

Definition W_734c8 : bv 32 := 0x00a12423.
Lemma F_734c8 : fetch_word Asan.M.loaded_segments (0x734c8 : word) = Some W_734c8.
Proof. vm_refl. Qed.
Lemma D_734c8 : decode_any W_734c8 = Some (Store SZ4 2 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_734cc : bv 32 := 0x00810593.
Lemma F_734cc : fetch_word Asan.M.loaded_segments (0x734cc : word) = Some W_734cc.
Proof. vm_refl. Qed.
Lemma D_734cc : decode_any W_734cc = Some (OpImm ALU_ADD 11 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_734d0 : bv 32 := 0x00090513.
Lemma F_734d0 : fetch_word Asan.M.loaded_segments (0x734d0 : word) = Some W_734d0.
Proof. vm_refl. Qed.
Lemma D_734d0 : decode_any W_734d0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_734d4 : bv 32 := 0xe6cfe0ef.
Lemma F_734d4 : fetch_word Asan.M.loaded_segments (0x734d4 : word) = Some W_734d4.
Proof. vm_refl. Qed.
Lemma D_734d4 : decode_any W_734d4 = Some (Jal 1 2090604, 4%Z).
Proof. vm_refl. Qed.

Definition W_734d8 : bv 32 := 0x02051c63.
Lemma F_734d8 : fetch_word Asan.M.loaded_segments (0x734d8 : word) = Some W_734d8.
Proof. vm_refl. Qed.
Lemma D_734d8 : decode_any W_734d8 = Some (Branch BC_NE 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_734dc : bv 32 := 0x00048513.
Lemma F_734dc : fetch_word Asan.M.loaded_segments (0x734dc : word) = Some W_734dc.
Proof. vm_refl. Qed.
Lemma D_734dc : decode_any W_734dc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_734e0 : bv 32 := 0xd64fa0ef.
Lemma F_734e0 : fetch_word Asan.M.loaded_segments (0x734e0 : word) = Some W_734e0.
Proof. vm_refl. Qed.
Lemma D_734e0 : decode_any W_734e0 = Some (Jal 1 2073956, 4%Z).
Proof. vm_refl. Qed.

Definition W_734e4 : bv 32 := 0x00090513.
Lemma F_734e4 : fetch_word Asan.M.loaded_segments (0x734e4 : word) = Some W_734e4.
Proof. vm_refl. Qed.
Lemma D_734e4 : decode_any W_734e4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_734e8 : bv 32 := 0x02813083.
Lemma F_734e8 : fetch_word Asan.M.loaded_segments (0x734e8 : word) = Some W_734e8.
Proof. vm_refl. Qed.
Lemma D_734e8 : decode_any W_734e8 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_734ec : bv 32 := 0x02013403.
Lemma F_734ec : fetch_word Asan.M.loaded_segments (0x734ec : word) = Some W_734ec.
Proof. vm_refl. Qed.
Lemma D_734ec : decode_any W_734ec = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_734f0 : bv 32 := 0x01813483.
Lemma F_734f0 : fetch_word Asan.M.loaded_segments (0x734f0 : word) = Some W_734f0.
Proof. vm_refl. Qed.
Lemma D_734f0 : decode_any W_734f0 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_734f4 : bv 32 := 0x01013903.
Lemma F_734f4 : fetch_word Asan.M.loaded_segments (0x734f4 : word) = Some W_734f4.
Proof. vm_refl. Qed.
Lemma D_734f4 : decode_any W_734f4 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_734f8 : bv 32 := 0x03010113.
Lemma F_734f8 : fetch_word Asan.M.loaded_segments (0x734f8 : word) = Some W_734f8.
Proof. vm_refl. Qed.
Lemma D_734f8 : decode_any W_734f8 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_734fc : bv 32 := 0x00008067.
Lemma F_734fc : fetch_word Asan.M.loaded_segments (0x734fc : word) = Some W_734fc.
Proof. vm_refl. Qed.
Lemma D_734fc : decode_any W_734fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73500 : bv 32 := 0xfff9f517.
Lemma F_73500 : fetch_word Asan.M.loaded_segments (0x73500 : word) = Some W_73500.
Proof. vm_refl. Qed.
Lemma D_73500 : decode_any W_73500 = Some (Auipc 10 1048479, 4%Z).
Proof. vm_refl. Qed.

Definition W_73504 : bv 32 := 0x26a50513.
Lemma F_73504 : fetch_word Asan.M.loaded_segments (0x73504 : word) = Some W_73504.
Proof. vm_refl. Qed.
Lemma D_73504 : decode_any W_73504 = Some (OpImm ALU_ADD 10 10 618, 4%Z).
Proof. vm_refl. Qed.

Definition W_73508 : bv 32 := 0xd0dfa0ef.
Lemma F_73508 : fetch_word Asan.M.loaded_segments (0x73508 : word) = Some W_73508.
Proof. vm_refl. Qed.
Lemma D_73508 : decode_any W_73508 = Some (Jal 1 2075916, 4%Z).
Proof. vm_refl. Qed.

Definition W_7350c : bv 32 := 0x291050ef.
Lemma F_7350c : fetch_word Asan.M.loaded_segments (0x7350c : word) = Some W_7350c.
Proof. vm_refl. Qed.
Lemma D_7350c : decode_any W_7350c = Some (Jal 1 23184, 4%Z).
Proof. vm_refl. Qed.

Definition W_73510 : bv 32 := 0x00812683.
Lemma F_73510 : fetch_word Asan.M.loaded_segments (0x73510 : word) = Some W_73510.
Proof. vm_refl. Qed.
Lemma D_73510 : decode_any W_73510 = Some (Load SZ4 true 13 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_73514 : bv 32 := 0x00c00513.
Lemma F_73514 : fetch_word Asan.M.loaded_segments (0x73514 : word) = Some W_73514.
Proof. vm_refl. Qed.
Lemma D_73514 : decode_any W_73514 = Some (OpImm ALU_ADD 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_73518 : bv 32 := 0x00a69663.
Lemma F_73518 : fetch_word Asan.M.loaded_segments (0x73518 : word) = Some W_73518.
Proof. vm_refl. Qed.
Lemma D_73518 : decode_any W_73518 = Some (Branch BC_NE 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7351c : bv 32 := 0x00000913.
Lemma F_7351c : fetch_word Asan.M.loaded_segments (0x7351c : word) = Some W_7351c.
Proof. vm_refl. Qed.
Lemma D_7351c : decode_any W_7351c = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73520 : bv 32 := 0xfc5ff06f.
Lemma F_73520 : fetch_word Asan.M.loaded_segments (0x73520 : word) = Some W_73520.
Proof. vm_refl. Qed.
Lemma D_73520 : decode_any W_73520 = Some (Jal 0 2097092, 4%Z).
Proof. vm_refl. Qed.

Definition W_73524 : bv 32 := 0xfffa7517.
Lemma F_73524 : fetch_word Asan.M.loaded_segments (0x73524 : word) = Some W_73524.
Proof. vm_refl. Qed.
Lemma D_73524 : decode_any W_73524 = Some (Auipc 10 1048487, 4%Z).
Proof. vm_refl. Qed.

Definition W_73528 : bv 32 := 0x6ae50613.
Lemma F_73528 : fetch_word Asan.M.loaded_segments (0x73528 : word) = Some W_73528.
Proof. vm_refl. Qed.
Lemma D_73528 : decode_any W_73528 = Some (OpImm ALU_ADD 12 10 1710, 4%Z).
Proof. vm_refl. Qed.

Definition W_7352c : bv 32 := 0x00048513.
Lemma F_7352c : fetch_word Asan.M.loaded_segments (0x7352c : word) = Some W_7352c.
Proof. vm_refl. Qed.
Lemma D_7352c : decode_any W_7352c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73530 : bv 32 := 0x00040593.
Lemma F_73530 : fetch_word Asan.M.loaded_segments (0x73530 : word) = Some W_73530.
Proof. vm_refl. Qed.
Lemma D_73530 : decode_any W_73530 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73534 : bv 32 := 0x00000713.
Lemma F_73534 : fetch_word Asan.M.loaded_segments (0x73534 : word) = Some W_73534.
Proof. vm_refl. Qed.
Lemma D_73534 : decode_any W_73534 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73538 : bv 32 := 0xe75f90ef.
Lemma F_73538 : fetch_word Asan.M.loaded_segments (0x73538 : word) = Some W_73538.
Proof. vm_refl. Qed.
Lemma D_73538 : decode_any W_73538 = Some (Jal 1 2072180, 4%Z).
Proof. vm_refl. Qed.

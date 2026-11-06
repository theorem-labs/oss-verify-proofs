(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_893c4 : bv 32 := 0x000d5517.
Lemma F_893c4 : fetch_word AsanUbsan.M.loaded_segments (0x8940c : word) = Some W_893c4.
Proof. vm_refl. Qed.
Lemma D_893c4 : decode_any W_893c4 = Some (Auipc 10 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_893c8 : bv 32 := 0x5f052503.
Lemma F_893c8 : fetch_word AsanUbsan.M.loaded_segments (0x89410 : word) = Some W_893c8.
Proof. vm_refl. Qed.
Lemma D_893c8 : decode_any W_893c8 = Some (Load SZ4 true 10 10 1520, 4%Z).
Proof. vm_refl. Qed.

Definition W_893cc : bv 32 := 0x0230000f.
Lemma F_893cc : fetch_word AsanUbsan.M.loaded_segments (0x89414 : word) = Some W_893cc.
Proof. vm_refl. Qed.
Lemma D_893cc : decode_any W_893cc = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_893d0 : bv 32 := 0x00008067.
Lemma F_893d0 : fetch_word AsanUbsan.M.loaded_segments (0x89418 : word) = Some W_893d0.
Proof. vm_refl. Qed.
Lemma D_893d0 : decode_any W_893d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_893d4 : bv 32 := 0xfb010113.
Lemma F_893d4 : fetch_word AsanUbsan.M.loaded_segments (0x8941c : word) = Some W_893d4.
Proof. vm_refl. Qed.
Lemma D_893d4 : decode_any W_893d4 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_893d8 : bv 32 := 0x04113423.
Lemma F_893d8 : fetch_word AsanUbsan.M.loaded_segments (0x89420 : word) = Some W_893d8.
Proof. vm_refl. Qed.
Lemma D_893d8 : decode_any W_893d8 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_893dc : bv 32 := 0x04813023.
Lemma F_893dc : fetch_word AsanUbsan.M.loaded_segments (0x89424 : word) = Some W_893dc.
Proof. vm_refl. Qed.
Lemma D_893dc : decode_any W_893dc = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_893e0 : bv 32 := 0x02913c23.
Lemma F_893e0 : fetch_word AsanUbsan.M.loaded_segments (0x89428 : word) = Some W_893e0.
Proof. vm_refl. Qed.
Lemma D_893e0 : decode_any W_893e0 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_893e4 : bv 32 := 0x03213823.
Lemma F_893e4 : fetch_word AsanUbsan.M.loaded_segments (0x8942c : word) = Some W_893e4.
Proof. vm_refl. Qed.
Lemma D_893e4 : decode_any W_893e4 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_893e8 : bv 32 := 0x03313423.
Lemma F_893e8 : fetch_word AsanUbsan.M.loaded_segments (0x89430 : word) = Some W_893e8.
Proof. vm_refl. Qed.
Lemma D_893e8 : decode_any W_893e8 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_893ec : bv 32 := 0x03413023.
Lemma F_893ec : fetch_word AsanUbsan.M.loaded_segments (0x89434 : word) = Some W_893ec.
Proof. vm_refl. Qed.
Lemma D_893ec : decode_any W_893ec = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_893f0 : bv 32 := 0x01513c23.
Lemma F_893f0 : fetch_word AsanUbsan.M.loaded_segments (0x89438 : word) = Some W_893f0.
Proof. vm_refl. Qed.
Lemma D_893f0 : decode_any W_893f0 = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_893f4 : bv 32 := 0x01613823.
Lemma F_893f4 : fetch_word AsanUbsan.M.loaded_segments (0x8943c : word) = Some W_893f4.
Proof. vm_refl. Qed.
Lemma D_893f4 : decode_any W_893f4 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_893f8 : bv 32 := 0x01713423.
Lemma F_893f8 : fetch_word AsanUbsan.M.loaded_segments (0x89440 : word) = Some W_893f8.
Proof. vm_refl. Qed.
Lemma D_893f8 : decode_any W_893f8 = Some (Store SZ8 2 23 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_893fc : bv 32 := 0x01813023.
Lemma F_893fc : fetch_word AsanUbsan.M.loaded_segments (0x89444 : word) = Some W_893fc.
Proof. vm_refl. Qed.
Lemma D_893fc : decode_any W_893fc = Some (Store SZ8 2 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89400 : bv 32 := 0x00078493.
Lemma F_89400 : fetch_word AsanUbsan.M.loaded_segments (0x89448 : word) = Some W_89400.
Proof. vm_refl. Qed.
Lemma D_89400 : decode_any W_89400 = Some (OpImm ALU_ADD 9 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89404 : bv 32 := 0x00070a93.
Lemma F_89404 : fetch_word AsanUbsan.M.loaded_segments (0x8944c : word) = Some W_89404.
Proof. vm_refl. Qed.
Lemma D_89404 : decode_any W_89404 = Some (OpImm ALU_ADD 21 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89408 : bv 32 := 0x00068a13.
Lemma F_89408 : fetch_word AsanUbsan.M.loaded_segments (0x89450 : word) = Some W_89408.
Proof. vm_refl. Qed.
Lemma D_89408 : decode_any W_89408 = Some (OpImm ALU_ADD 20 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8940c : bv 32 := 0x00060413.
Lemma F_8940c : fetch_word AsanUbsan.M.loaded_segments (0x89454 : word) = Some W_8940c.
Proof. vm_refl. Qed.
Lemma D_8940c : decode_any W_8940c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89410 : bv 32 := 0x00058913.
Lemma F_89410 : fetch_word AsanUbsan.M.loaded_segments (0x89458 : word) = Some W_89410.
Proof. vm_refl. Qed.
Lemma D_89410 : decode_any W_89410 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89414 : bv 32 := 0x00050993.
Lemma F_89414 : fetch_word AsanUbsan.M.loaded_segments (0x8945c : word) = Some W_89414.
Proof. vm_refl. Qed.
Lemma D_89414 : decode_any W_89414 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89418 : bv 32 := 0x00052423.
Lemma F_89418 : fetch_word AsanUbsan.M.loaded_segments (0x89460 : word) = Some W_89418.
Proof. vm_refl. Qed.
Lemma D_89418 : decode_any W_89418 = Some (Store SZ4 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8941c : bv 32 := 0xb10fe0ef.
Lemma F_8941c : fetch_word AsanUbsan.M.loaded_segments (0x89464 : word) = Some W_8941c.
Proof. vm_refl. Qed.
Lemma D_8941c : decode_any W_8941c = Some (Jal 1 2089744, 4%Z).
Proof. vm_refl. Qed.

Definition W_89420 : bv 32 := 0x0c050a63.
Lemma F_89420 : fetch_word AsanUbsan.M.loaded_segments (0x89468 : word) = Some W_89420.
Proof. vm_refl. Qed.
Lemma D_89420 : decode_any W_89420 = Some (Branch BC_EQ 10 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_89424 : bv 32 := 0x219010ef.
Lemma F_89424 : fetch_word AsanUbsan.M.loaded_segments (0x8946c : word) = Some W_89424.
Proof. vm_refl. Qed.
Lemma D_89424 : decode_any W_89424 = Some (Jal 1 6680, 4%Z).
Proof. vm_refl. Qed.

Definition W_89428 : bv 32 := 0x04050a63.
Lemma F_89428 : fetch_word AsanUbsan.M.loaded_segments (0x89470 : word) = Some W_89428.
Proof. vm_refl. Qed.
Lemma D_89428 : decode_any W_89428 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_8942c : bv 32 := 0x7ff50c13.
Lemma F_8942c : fetch_word AsanUbsan.M.loaded_segments (0x89474 : word) = Some W_8942c.
Proof. vm_refl. Qed.
Lemma D_8942c : decode_any W_8942c = Some (OpImm ALU_ADD 24 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_89430 : bv 32 := 0x461c4583.
Lemma F_89430 : fetch_word AsanUbsan.M.loaded_segments (0x89478 : word) = Some W_89430.
Proof. vm_refl. Qed.
Lemma D_89430 : decode_any W_89430 = Some (Load SZ1 false 11 24 1121, 4%Z).
Proof. vm_refl. Qed.

Definition W_89434 : bv 32 := 0x00100613.
Lemma F_89434 : fetch_word AsanUbsan.M.loaded_segments (0x8947c : word) = Some W_89434.
Proof. vm_refl. Qed.
Lemma D_89434 : decode_any W_89434 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_89438 : bv 32 := 0x46cc00a3.
Lemma F_89438 : fetch_word AsanUbsan.M.loaded_segments (0x89480 : word) = Some W_89438.
Proof. vm_refl. Qed.
Lemma D_89438 : decode_any W_89438 = Some (Store SZ1 24 12 1121, 4%Z).
Proof. vm_refl. Qed.

Definition W_8943c : bv 32 := 0x0a059a63.
Lemma F_8943c : fetch_word AsanUbsan.M.loaded_segments (0x89484 : word) = Some W_8943c.
Proof. vm_refl. Qed.
Lemma D_8943c : decode_any W_8943c = Some (Branch BC_NE 11 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_89440 : bv 32 := 0x00050b93.
Lemma F_89440 : fetch_word AsanUbsan.M.loaded_segments (0x89488 : word) = Some W_89440.
Proof. vm_refl. Qed.
Lemma D_89440 : decode_any W_89440 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89444 : bv 32 := 0x3bd010ef.
Lemma F_89444 : fetch_word AsanUbsan.M.loaded_segments (0x8948c : word) = Some W_89444.
Proof. vm_refl. Qed.
Lemma D_89444 : decode_any W_89444 = Some (Jal 1 7100, 4%Z).
Proof. vm_refl. Qed.

Definition W_89448 : bv 32 := 0x00050b13.
Lemma F_89448 : fetch_word AsanUbsan.M.loaded_segments (0x89490 : word) = Some W_89448.
Proof. vm_refl. Qed.
Lemma D_89448 : decode_any W_89448 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8944c : bv 32 := 0x000b8513.
Lemma F_8944c : fetch_word AsanUbsan.M.loaded_segments (0x89494 : word) = Some W_8944c.
Proof. vm_refl. Qed.
Lemma D_8944c : decode_any W_8944c = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89450 : bv 32 := 0x409010ef.
Lemma F_89450 : fetch_word AsanUbsan.M.loaded_segments (0x89498 : word) = Some W_89450.
Proof. vm_refl. Qed.
Lemma D_89450 : decode_any W_89450 = Some (Jal 1 7176, 4%Z).
Proof. vm_refl. Qed.

Definition W_89454 : bv 32 := 0x00050813.
Lemma F_89454 : fetch_word AsanUbsan.M.loaded_segments (0x8949c : word) = Some W_89454.
Proof. vm_refl. Qed.
Lemma D_89454 : decode_any W_89454 = Some (OpImm ALU_ADD 16 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89458 : bv 32 := 0x060a8c63.
Lemma F_89458 : fetch_word AsanUbsan.M.loaded_segments (0x894a0 : word) = Some W_89458.
Proof. vm_refl. Qed.
Lemma D_89458 : decode_any W_89458 = Some (Branch BC_EQ 21 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_8945c : bv 32 := 0x00100893.
Lemma F_8945c : fetch_word AsanUbsan.M.loaded_segments (0x894a4 : word) = Some W_8945c.
Proof. vm_refl. Qed.
Lemma D_8945c : decode_any W_8945c = Some (OpImm ALU_ADD 17 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_89460 : bv 32 := 0x00098513.
Lemma F_89460 : fetch_word AsanUbsan.M.loaded_segments (0x894a8 : word) = Some W_89460.
Proof. vm_refl. Qed.
Lemma D_89460 : decode_any W_89460 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89464 : bv 32 := 0x00048593.
Lemma F_89464 : fetch_word AsanUbsan.M.loaded_segments (0x894ac : word) = Some W_89464.
Proof. vm_refl. Qed.
Lemma D_89464 : decode_any W_89464 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89468 : bv 32 := 0x00090613.
Lemma F_89468 : fetch_word AsanUbsan.M.loaded_segments (0x894b0 : word) = Some W_89468.
Proof. vm_refl. Qed.
Lemma D_89468 : decode_any W_89468 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8946c : bv 32 := 0x00040693.
Lemma F_8946c : fetch_word AsanUbsan.M.loaded_segments (0x894b4 : word) = Some W_8946c.
Proof. vm_refl. Qed.
Lemma D_8946c : decode_any W_8946c = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89470 : bv 32 := 0x00000713.
Lemma F_89470 : fetch_word AsanUbsan.M.loaded_segments (0x894b8 : word) = Some W_89470.
Proof. vm_refl. Qed.
Lemma D_89470 : decode_any W_89470 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89474 : bv 32 := 0x000b0793.
Lemma F_89474 : fetch_word AsanUbsan.M.loaded_segments (0x894bc : word) = Some W_89474.
Proof. vm_refl. Qed.
Lemma D_89474 : decode_any W_89474 = Some (OpImm ALU_ADD 15 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89478 : bv 32 := 0x0740006f.
Lemma F_89478 : fetch_word AsanUbsan.M.loaded_segments (0x894c0 : word) = Some W_89478.
Proof. vm_refl. Qed.
Lemma D_89478 : decode_any W_89478 = Some (Jal 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_894ec : bv 32 := 0x018190ef.
Lemma F_894ec : fetch_word AsanUbsan.M.loaded_segments (0x89534 : word) = Some W_894ec.
Proof. vm_refl. Qed.
Lemma D_894ec : decode_any W_894ec = Some (Jal 1 102424, 4%Z).
Proof. vm_refl. Qed.

Definition W_894f0 : bv 32 := 0x460c00a3.
Lemma F_894f0 : fetch_word AsanUbsan.M.loaded_segments (0x89538 : word) = Some W_894f0.
Proof. vm_refl. Qed.
Lemma D_894f0 : decode_any W_894f0 = Some (Store SZ1 24 0 1121, 4%Z).
Proof. vm_refl. Qed.

Definition W_894f4 : bv 32 := 0x04813083.
Lemma F_894f4 : fetch_word AsanUbsan.M.loaded_segments (0x8953c : word) = Some W_894f4.
Proof. vm_refl. Qed.
Lemma D_894f4 : decode_any W_894f4 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_894f8 : bv 32 := 0x04013403.
Lemma F_894f8 : fetch_word AsanUbsan.M.loaded_segments (0x89540 : word) = Some W_894f8.
Proof. vm_refl. Qed.
Lemma D_894f8 : decode_any W_894f8 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_894fc : bv 32 := 0x03813483.
Lemma F_894fc : fetch_word AsanUbsan.M.loaded_segments (0x89544 : word) = Some W_894fc.
Proof. vm_refl. Qed.
Lemma D_894fc : decode_any W_894fc = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_89500 : bv 32 := 0x03013903.
Lemma F_89500 : fetch_word AsanUbsan.M.loaded_segments (0x89548 : word) = Some W_89500.
Proof. vm_refl. Qed.
Lemma D_89500 : decode_any W_89500 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_89504 : bv 32 := 0x02813983.
Lemma F_89504 : fetch_word AsanUbsan.M.loaded_segments (0x8954c : word) = Some W_89504.
Proof. vm_refl. Qed.
Lemma D_89504 : decode_any W_89504 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_89508 : bv 32 := 0x02013a03.
Lemma F_89508 : fetch_word AsanUbsan.M.loaded_segments (0x89550 : word) = Some W_89508.
Proof. vm_refl. Qed.
Lemma D_89508 : decode_any W_89508 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8950c : bv 32 := 0x01813a83.
Lemma F_8950c : fetch_word AsanUbsan.M.loaded_segments (0x89554 : word) = Some W_8950c.
Proof. vm_refl. Qed.
Lemma D_8950c : decode_any W_8950c = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_89510 : bv 32 := 0x01013b03.
Lemma F_89510 : fetch_word AsanUbsan.M.loaded_segments (0x89558 : word) = Some W_89510.
Proof. vm_refl. Qed.
Lemma D_89510 : decode_any W_89510 = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_89514 : bv 32 := 0x00813b83.
Lemma F_89514 : fetch_word AsanUbsan.M.loaded_segments (0x8955c : word) = Some W_89514.
Proof. vm_refl. Qed.
Lemma D_89514 : decode_any W_89514 = Some (Load SZ8 true 23 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_89518 : bv 32 := 0x00013c03.
Lemma F_89518 : fetch_word AsanUbsan.M.loaded_segments (0x89560 : word) = Some W_89518.
Proof. vm_refl. Qed.
Lemma D_89518 : decode_any W_89518 = Some (Load SZ8 true 24 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8951c : bv 32 := 0x05010113.
Lemma F_8951c : fetch_word AsanUbsan.M.loaded_segments (0x89564 : word) = Some W_8951c.
Proof. vm_refl. Qed.
Lemma D_8951c : decode_any W_8951c = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_89520 : bv 32 := 0x00008067.
Lemma F_89520 : fetch_word AsanUbsan.M.loaded_segments (0x89568 : word) = Some W_89520.
Proof. vm_refl. Qed.
Lemma D_89520 : decode_any W_89520 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.


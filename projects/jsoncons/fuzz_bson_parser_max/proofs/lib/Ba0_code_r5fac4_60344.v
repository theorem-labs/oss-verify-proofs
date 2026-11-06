(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_793fc : bv 32 := 0x0100006f.
Lemma F_793fc : fetch_word Asan.M.loaded_segments (0x7944c : word) = Some W_793fc.
Proof. vm_refl. Qed.
Lemma D_793fc : decode_any W_793fc = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79400 : bv 32 := 0x1dc0006f.
Lemma F_79400 : fetch_word Asan.M.loaded_segments (0x79450 : word) = Some W_79400.
Proof. vm_refl. Qed.
Lemma D_79400 : decode_any W_79400 = Some (Jal 0 476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79408 : bv 32 := 0x7400006f.
Lemma F_79408 : fetch_word Asan.M.loaded_segments (0x79458 : word) = Some W_79408.
Proof. vm_refl. Qed.
Lemma D_79408 : decode_any W_79408 = Some (Jal 0 1856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7940c : bv 32 := 0x81010113.
Lemma F_7940c : fetch_word Asan.M.loaded_segments (0x7945c : word) = Some W_7940c.
Proof. vm_refl. Qed.
Lemma D_7940c : decode_any W_7940c = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79410 : bv 32 := 0x7e113423.
Lemma F_79410 : fetch_word Asan.M.loaded_segments (0x79460 : word) = Some W_79410.
Proof. vm_refl. Qed.
Lemma D_79410 : decode_any W_79410 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79414 : bv 32 := 0x7e813023.
Lemma F_79414 : fetch_word Asan.M.loaded_segments (0x79464 : word) = Some W_79414.
Proof. vm_refl. Qed.
Lemma D_79414 : decode_any W_79414 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79418 : bv 32 := 0x7c913c23.
Lemma F_79418 : fetch_word Asan.M.loaded_segments (0x79468 : word) = Some W_79418.
Proof. vm_refl. Qed.
Lemma D_79418 : decode_any W_79418 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7941c : bv 32 := 0x7d213823.
Lemma F_7941c : fetch_word Asan.M.loaded_segments (0x7946c : word) = Some W_7941c.
Proof. vm_refl. Qed.
Lemma D_7941c : decode_any W_7941c = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79420 : bv 32 := 0x7d313423.
Lemma F_79420 : fetch_word Asan.M.loaded_segments (0x79470 : word) = Some W_79420.
Proof. vm_refl. Qed.
Lemma D_79420 : decode_any W_79420 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79424 : bv 32 := 0x7d413023.
Lemma F_79424 : fetch_word Asan.M.loaded_segments (0x79474 : word) = Some W_79424.
Proof. vm_refl. Qed.
Lemma D_79424 : decode_any W_79424 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79428 : bv 32 := 0x7b513c23.
Lemma F_79428 : fetch_word Asan.M.loaded_segments (0x79478 : word) = Some W_79428.
Proof. vm_refl. Qed.
Lemma D_79428 : decode_any W_79428 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7942c : bv 32 := 0x7f010413.
Lemma F_7942c : fetch_word Asan.M.loaded_segments (0x7947c : word) = Some W_7942c.
Proof. vm_refl. Qed.
Lemma D_7942c : decode_any W_7942c = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79430 : bv 32 := 0xfa010113.
Lemma F_79430 : fetch_word Asan.M.loaded_segments (0x79480 : word) = Some W_79430.
Proof. vm_refl. Qed.
Lemma D_79430 : decode_any W_79430 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79434 : bv 32 := 0x00008913.
Lemma F_79434 : fetch_word Asan.M.loaded_segments (0x79484 : word) = Some W_79434.
Proof. vm_refl. Qed.
Lemma D_79434 : decode_any W_79434 = Some (OpImm ALU_ADD 18 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79438 : bv 32 := 0x00050493.
Lemma F_79438 : fetch_word Asan.M.loaded_segments (0x79488 : word) = Some W_79438.
Proof. vm_refl. Qed.
Lemma D_79438 : decode_any W_79438 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7943c : bv 32 := 0x10c0c0ef.
Lemma F_7943c : fetch_word Asan.M.loaded_segments (0x7948c : word) = Some W_7943c.
Proof. vm_refl. Qed.
Lemma D_7943c : decode_any W_7943c = Some (Jal 1 49420, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79440 : bv 32 := 0x02f4d593.
Lemma F_79440 : fetch_word Asan.M.loaded_segments (0x79490 : word) = Some W_79440.
Proof. vm_refl. Qed.
Lemma D_79440 : decode_any W_79440 = Some (ShiftImm ALU_SRL 11 9 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79444 : bv 32 := 0x0a059063.
Lemma F_79444 : fetch_word Asan.M.loaded_segments (0x79494 : word) = Some W_79444.
Proof. vm_refl. Qed.
Lemma D_79444 : decode_any W_79444 = Some (Branch BC_NE 11 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79448 : bv 32 := 0x0204d593.
Lemma F_79448 : fetch_word Asan.M.loaded_segments (0x79498 : word) = Some W_79448.
Proof. vm_refl. Qed.
Lemma D_79448 : decode_any W_79448 = Some (ShiftImm ALU_SRL 11 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7944c : bv 32 := 0x00359613.
Lemma F_7944c : fetch_word Asan.M.loaded_segments (0x7949c : word) = Some W_7944c.
Proof. vm_refl. Qed.
Lemma D_7944c : decode_any W_7944c = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79450 : bv 32 := 0x00c50633.
Lemma F_79450 : fetch_word Asan.M.loaded_segments (0x794a0 : word) = Some W_79450.
Proof. vm_refl. Qed.
Lemma D_79450 : decode_any W_79450 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79454 : bv 32 := 0x00863683.
Lemma F_79454 : fetch_word Asan.M.loaded_segments (0x794a4 : word) = Some W_79454.
Proof. vm_refl. Qed.
Lemma D_79454 : decode_any W_79454 = Some (Load SZ8 true 13 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79458 : bv 32 := 0x0230000f.
Lemma F_79458 : fetch_word Asan.M.loaded_segments (0x794a8 : word) = Some W_79458.
Proof. vm_refl. Qed.
Lemma D_79458 : decode_any W_79458 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7945c : bv 32 := 0x08068463.
Lemma F_7945c : fetch_word Asan.M.loaded_segments (0x794ac : word) = Some W_7945c.
Proof. vm_refl. Qed.
Lemma D_7945c : decode_any W_7945c = Some (Branch BC_EQ 13 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_794e4 : bv 32 := 0x80040a13.
Lemma F_794e4 : fetch_word Asan.M.loaded_segments (0x79534 : word) = Some W_794e4.
Proof. vm_refl. Qed.
Lemma D_794e4 : decode_any W_794e4 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_794e8 : bv 32 := 0xfb0a0a13.
Lemma F_794e8 : fetch_word Asan.M.loaded_segments (0x79538 : word) = Some W_794e8.
Proof. vm_refl. Qed.
Lemma D_794e8 : decode_any W_794e8 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_794ec : bv 32 := 0x80040513.
Lemma F_794ec : fetch_word Asan.M.loaded_segments (0x7953c : word) = Some W_794ec.
Proof. vm_refl. Qed.
Lemma D_794ec : decode_any W_794ec = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_794f0 : bv 32 := 0xfc050513.
Lemma F_794f0 : fetch_word Asan.M.loaded_segments (0x79540 : word) = Some W_794f0.
Proof. vm_refl. Qed.
Lemma D_794f0 : decode_any W_794f0 = Some (OpImm ALU_ADD 10 10 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_794f4 : bv 32 := 0x7ffa0a93.
Lemma F_794f4 : fetch_word Asan.M.loaded_segments (0x79544 : word) = Some W_794f4.
Proof. vm_refl. Qed.
Lemma D_794f4 : decode_any W_794f4 = Some (OpImm ALU_ADD 21 20 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_794f8 : bv 32 := 0x000ab4a3.
Lemma F_794f8 : fetch_word Asan.M.loaded_segments (0x79548 : word) = Some W_794f8.
Proof. vm_refl. Qed.
Lemma D_794f8 : decode_any W_794f8 = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_794fc : bv 32 := 0x00aa3023.
Lemma F_794fc : fetch_word Asan.M.loaded_segments (0x7954c : word) = Some W_794fc.
Proof. vm_refl. Qed.
Lemma D_794fc : decode_any W_794fc = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79500 : bv 32 := 0x000a3423.
Lemma F_79500 : fetch_word Asan.M.loaded_segments (0x79550 : word) = Some W_79500.
Proof. vm_refl. Qed.
Lemma D_79500 : decode_any W_79500 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79504 : bv 32 := 0x550080ef.
Lemma F_79504 : fetch_word Asan.M.loaded_segments (0x79554 : word) = Some W_79504.
Proof. vm_refl. Qed.
Lemma D_79504 : decode_any W_79504 = Some (Jal 1 34128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79508 : bv 32 := 0x00200593.
Lemma F_79508 : fetch_word Asan.M.loaded_segments (0x79558 : word) = Some W_79508.
Proof. vm_refl. Qed.
Lemma D_79508 : decode_any W_79508 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7950c : bv 32 := 0x02a5ea63.
Lemma F_7950c : fetch_word Asan.M.loaded_segments (0x7955c : word) = Some W_7950c.
Proof. vm_refl. Qed.
Lemma D_7950c : decode_any W_7950c = Some (Branch BC_LTU 11 10 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79540 : bv 32 := 0x7f1200ef.
Lemma F_79540 : fetch_word Asan.M.loaded_segments (0x79590 : word) = Some W_79540.
Proof. vm_refl. Qed.
Lemma D_79540 : decode_any W_79540 = Some (Jal 1 135152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79544 : bv 32 := 0x000bc597.
Lemma F_79544 : fetch_word Asan.M.loaded_segments (0x79594 : word) = Some W_79544.
Proof. vm_refl. Qed.
Lemma D_79544 : decode_any W_79544 = Some (Auipc 11 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79548 : bv 32 := 0xa345b583.
Lemma F_79548 : fetch_word Asan.M.loaded_segments (0x79598 : word) = Some W_79548.
Proof. vm_refl. Qed.
Lemma D_79548 : decode_any W_79548 = Some (Load SZ8 true 11 11 2612, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7954c : bv 32 := 0x0225c983.
Lemma F_7954c : fetch_word Asan.M.loaded_segments (0x7959c : word) = Some W_7954c.
Proof. vm_refl. Qed.
Lemma D_7954c : decode_any W_7954c = Some (Load SZ1 false 19 11 34, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79550 : bv 32 := 0x00050913.
Lemma F_79550 : fetch_word Asan.M.loaded_segments (0x795a0 : word) = Some W_79550.
Proof. vm_refl. Qed.
Lemma D_79550 : decode_any W_79550 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79554 : bv 32 := 0x500080ef.
Lemma F_79554 : fetch_word Asan.M.loaded_segments (0x795a4 : word) = Some W_79554.
Proof. vm_refl. Qed.
Lemma D_79554 : decode_any W_79554 = Some (Jal 1 34048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79558 : bv 32 := 0x00050793.
Lemma F_79558 : fetch_word Asan.M.loaded_segments (0x795a8 : word) = Some W_79558.
Proof. vm_refl. Qed.
Lemma D_79558 : decode_any W_79558 = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7955c : bv 32 := 0x00153513.
Lemma F_7955c : fetch_word Asan.M.loaded_segments (0x795ac : word) = Some W_7955c.
Proof. vm_refl. Qed.
Lemma D_7955c : decode_any W_7955c = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79560 : bv 32 := 0xfff50513.
Lemma F_79560 : fetch_word Asan.M.loaded_segments (0x795b0 : word) = Some W_79560.
Proof. vm_refl. Qed.
Lemma D_79560 : decode_any W_79560 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79564 : bv 32 := 0x008575b3.
Lemma F_79564 : fetch_word Asan.M.loaded_segments (0x795b4 : word) = Some W_79564.
Proof. vm_refl. Qed.
Lemma D_79564 : decode_any W_79564 = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79568 : bv 32 := 0x00100513.
Lemma F_79568 : fetch_word Asan.M.loaded_segments (0x795b8 : word) = Some W_79568.
Proof. vm_refl. Qed.
Lemma D_79568 : decode_any W_79568 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7956c : bv 32 := 0x00bab4a3.
Lemma F_7956c : fetch_word Asan.M.loaded_segments (0x795bc : word) = Some W_7956c.
Proof. vm_refl. Qed.
Lemma D_7956c : decode_any W_7956c = Some (Store SZ8 21 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79570 : bv 32 := 0x00f56a63.
Lemma F_79570 : fetch_word Asan.M.loaded_segments (0x795c0 : word) = Some W_79570.
Proof. vm_refl. Qed.
Lemma D_79570 : decode_any W_79570 = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79584 : bv 32 := 0x80040513.
Lemma F_79584 : fetch_word Asan.M.loaded_segments (0x795d4 : word) = Some W_79584.
Proof. vm_refl. Qed.
Lemma D_79584 : decode_any W_79584 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79588 : bv 32 := 0xfb050513.
Lemma F_79588 : fetch_word Asan.M.loaded_segments (0x795d8 : word) = Some W_79588.
Proof. vm_refl. Qed.
Lemma D_79588 : decode_any W_79588 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7958c : bv 32 := 0x00090593.
Lemma F_7958c : fetch_word Asan.M.loaded_segments (0x795dc : word) = Some W_7958c.
Proof. vm_refl. Qed.
Lemma D_7958c : decode_any W_7958c = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79590 : bv 32 := 0x00040613.
Lemma F_79590 : fetch_word Asan.M.loaded_segments (0x795e0 : word) = Some W_79590.
Proof. vm_refl. Qed.
Lemma D_79590 : decode_any W_79590 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79594 : bv 32 := 0x00000693.
Lemma F_79594 : fetch_word Asan.M.loaded_segments (0x795e4 : word) = Some W_79594.
Proof. vm_refl. Qed.
Lemma D_79594 : decode_any W_79594 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79598 : bv 32 := 0x00098713.
Lemma F_79598 : fetch_word Asan.M.loaded_segments (0x795e8 : word) = Some W_79598.
Proof. vm_refl. Qed.
Lemma D_79598 : decode_any W_79598 = Some (OpImm ALU_ADD 14 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7959c : bv 32 := 0x4c8080ef.
Lemma F_7959c : fetch_word Asan.M.loaded_segments (0x795ec : word) = Some W_7959c.
Proof. vm_refl. Qed.
Lemma D_7959c : decode_any W_7959c = Some (Jal 1 33992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795a0 : bv 32 := 0x80040593.
Lemma F_795a0 : fetch_word Asan.M.loaded_segments (0x795f0 : word) = Some W_795a0.
Proof. vm_refl. Qed.
Lemma D_795a0 : decode_any W_795a0 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795a4 : bv 32 := 0xfb058593.
Lemma F_795a4 : fetch_word Asan.M.loaded_segments (0x795f4 : word) = Some W_795a4.
Proof. vm_refl. Qed.
Lemma D_795a4 : decode_any W_795a4 = Some (OpImm ALU_ADD 11 11 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795a8 : bv 32 := 0x00100613.
Lemma F_795a8 : fetch_word Asan.M.loaded_segments (0x795f8 : word) = Some W_795a8.
Proof. vm_refl. Qed.
Lemma D_795a8 : decode_any W_795a8 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795ac : bv 32 := 0x00048513.
Lemma F_795ac : fetch_word Asan.M.loaded_segments (0x795fc : word) = Some W_795ac.
Proof. vm_refl. Qed.
Lemma D_795ac : decode_any W_795ac = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795b0 : bv 32 := 0x8e1d80ef.
Lemma F_795b0 : fetch_word Asan.M.loaded_segments (0x79600 : word) = Some W_795b0.
Proof. vm_refl. Qed.
Lemma D_795b0 : decode_any W_795b0 = Some (Jal 1 1935584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795b4 : bv 32 := 0x06010113.
Lemma F_795b4 : fetch_word Asan.M.loaded_segments (0x79604 : word) = Some W_795b4.
Proof. vm_refl. Qed.
Lemma D_795b4 : decode_any W_795b4 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795b8 : bv 32 := 0x7e813083.
Lemma F_795b8 : fetch_word Asan.M.loaded_segments (0x79608 : word) = Some W_795b8.
Proof. vm_refl. Qed.
Lemma D_795b8 : decode_any W_795b8 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795bc : bv 32 := 0x7e013403.
Lemma F_795bc : fetch_word Asan.M.loaded_segments (0x7960c : word) = Some W_795bc.
Proof. vm_refl. Qed.
Lemma D_795bc : decode_any W_795bc = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795c0 : bv 32 := 0x7d813483.
Lemma F_795c0 : fetch_word Asan.M.loaded_segments (0x79610 : word) = Some W_795c0.
Proof. vm_refl. Qed.
Lemma D_795c0 : decode_any W_795c0 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795c4 : bv 32 := 0x7d013903.
Lemma F_795c4 : fetch_word Asan.M.loaded_segments (0x79614 : word) = Some W_795c4.
Proof. vm_refl. Qed.
Lemma D_795c4 : decode_any W_795c4 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795c8 : bv 32 := 0x7c813983.
Lemma F_795c8 : fetch_word Asan.M.loaded_segments (0x79618 : word) = Some W_795c8.
Proof. vm_refl. Qed.
Lemma D_795c8 : decode_any W_795c8 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795cc : bv 32 := 0x7c013a03.
Lemma F_795cc : fetch_word Asan.M.loaded_segments (0x7961c : word) = Some W_795cc.
Proof. vm_refl. Qed.
Lemma D_795cc : decode_any W_795cc = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795d0 : bv 32 := 0x7b813a83.
Lemma F_795d0 : fetch_word Asan.M.loaded_segments (0x79620 : word) = Some W_795d0.
Proof. vm_refl. Qed.
Lemma D_795d0 : decode_any W_795d0 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795d4 : bv 32 := 0x7f010113.
Lemma F_795d4 : fetch_word Asan.M.loaded_segments (0x79624 : word) = Some W_795d4.
Proof. vm_refl. Qed.
Lemma D_795d4 : decode_any W_795d4 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795d8 : bv 32 := 0x00008067.
Lemma F_795d8 : fetch_word Asan.M.loaded_segments (0x79628 : word) = Some W_795d8.
Proof. vm_refl. Qed.
Lemma D_795d8 : decode_any W_795d8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795dc : bv 32 := 0x81010113.
Lemma F_795dc : fetch_word Asan.M.loaded_segments (0x7962c : word) = Some W_795dc.
Proof. vm_refl. Qed.
Lemma D_795dc : decode_any W_795dc = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795e0 : bv 32 := 0x7e113423.
Lemma F_795e0 : fetch_word Asan.M.loaded_segments (0x79630 : word) = Some W_795e0.
Proof. vm_refl. Qed.
Lemma D_795e0 : decode_any W_795e0 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795e4 : bv 32 := 0x7e813023.
Lemma F_795e4 : fetch_word Asan.M.loaded_segments (0x79634 : word) = Some W_795e4.
Proof. vm_refl. Qed.
Lemma D_795e4 : decode_any W_795e4 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795e8 : bv 32 := 0x7c913c23.
Lemma F_795e8 : fetch_word Asan.M.loaded_segments (0x79638 : word) = Some W_795e8.
Proof. vm_refl. Qed.
Lemma D_795e8 : decode_any W_795e8 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795ec : bv 32 := 0x7d213823.
Lemma F_795ec : fetch_word Asan.M.loaded_segments (0x7963c : word) = Some W_795ec.
Proof. vm_refl. Qed.
Lemma D_795ec : decode_any W_795ec = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795f0 : bv 32 := 0x7d313423.
Lemma F_795f0 : fetch_word Asan.M.loaded_segments (0x79640 : word) = Some W_795f0.
Proof. vm_refl. Qed.
Lemma D_795f0 : decode_any W_795f0 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795f4 : bv 32 := 0x7d413023.
Lemma F_795f4 : fetch_word Asan.M.loaded_segments (0x79644 : word) = Some W_795f4.
Proof. vm_refl. Qed.
Lemma D_795f4 : decode_any W_795f4 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795f8 : bv 32 := 0x7b513c23.
Lemma F_795f8 : fetch_word Asan.M.loaded_segments (0x79648 : word) = Some W_795f8.
Proof. vm_refl. Qed.
Lemma D_795f8 : decode_any W_795f8 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_795fc : bv 32 := 0x7f010413.
Lemma F_795fc : fetch_word Asan.M.loaded_segments (0x7964c : word) = Some W_795fc.
Proof. vm_refl. Qed.
Lemma D_795fc : decode_any W_795fc = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79600 : bv 32 := 0xfa010113.
Lemma F_79600 : fetch_word Asan.M.loaded_segments (0x79650 : word) = Some W_79600.
Proof. vm_refl. Qed.
Lemma D_79600 : decode_any W_79600 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79604 : bv 32 := 0x00008913.
Lemma F_79604 : fetch_word Asan.M.loaded_segments (0x79654 : word) = Some W_79604.
Proof. vm_refl. Qed.
Lemma D_79604 : decode_any W_79604 = Some (OpImm ALU_ADD 18 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79608 : bv 32 := 0x00050493.
Lemma F_79608 : fetch_word Asan.M.loaded_segments (0x79658 : word) = Some W_79608.
Proof. vm_refl. Qed.
Lemma D_79608 : decode_any W_79608 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7960c : bv 32 := 0x6c0070ef.
Lemma F_7960c : fetch_word Asan.M.loaded_segments (0x7965c : word) = Some W_7960c.
Proof. vm_refl. Qed.
Lemma D_7960c : decode_any W_7960c = Some (Jal 1 30400, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79610 : bv 32 := 0x06050063.
Lemma F_79610 : fetch_word Asan.M.loaded_segments (0x79660 : word) = Some W_79610.
Proof. vm_refl. Qed.
Lemma D_79610 : decode_any W_79610 = Some (Branch BC_EQ 10 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79614 : bv 32 := 0x80040a13.
Lemma F_79614 : fetch_word Asan.M.loaded_segments (0x79664 : word) = Some W_79614.
Proof. vm_refl. Qed.
Lemma D_79614 : decode_any W_79614 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79618 : bv 32 := 0xfb0a0a13.
Lemma F_79618 : fetch_word Asan.M.loaded_segments (0x79668 : word) = Some W_79618.
Proof. vm_refl. Qed.
Lemma D_79618 : decode_any W_79618 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7961c : bv 32 := 0x80040513.
Lemma F_7961c : fetch_word Asan.M.loaded_segments (0x7966c : word) = Some W_7961c.
Proof. vm_refl. Qed.
Lemma D_7961c : decode_any W_7961c = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79620 : bv 32 := 0xfc050513.
Lemma F_79620 : fetch_word Asan.M.loaded_segments (0x79670 : word) = Some W_79620.
Proof. vm_refl. Qed.
Lemma D_79620 : decode_any W_79620 = Some (OpImm ALU_ADD 10 10 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79624 : bv 32 := 0x7ffa0a93.
Lemma F_79624 : fetch_word Asan.M.loaded_segments (0x79674 : word) = Some W_79624.
Proof. vm_refl. Qed.
Lemma D_79624 : decode_any W_79624 = Some (OpImm ALU_ADD 21 20 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79628 : bv 32 := 0x000ab4a3.
Lemma F_79628 : fetch_word Asan.M.loaded_segments (0x79678 : word) = Some W_79628.
Proof. vm_refl. Qed.
Lemma D_79628 : decode_any W_79628 = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7962c : bv 32 := 0x00aa3023.
Lemma F_7962c : fetch_word Asan.M.loaded_segments (0x7967c : word) = Some W_7962c.
Proof. vm_refl. Qed.
Lemma D_7962c : decode_any W_7962c = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79630 : bv 32 := 0x000a3423.
Lemma F_79630 : fetch_word Asan.M.loaded_segments (0x79680 : word) = Some W_79630.
Proof. vm_refl. Qed.
Lemma D_79630 : decode_any W_79630 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79634 : bv 32 := 0x420080ef.
Lemma F_79634 : fetch_word Asan.M.loaded_segments (0x79684 : word) = Some W_79634.
Proof. vm_refl. Qed.
Lemma D_79634 : decode_any W_79634 = Some (Jal 1 33824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79638 : bv 32 := 0x00200593.
Lemma F_79638 : fetch_word Asan.M.loaded_segments (0x79688 : word) = Some W_79638.
Proof. vm_refl. Qed.
Lemma D_79638 : decode_any W_79638 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7963c : bv 32 := 0x06a5e263.
Lemma F_7963c : fetch_word Asan.M.loaded_segments (0x7968c : word) = Some W_7963c.
Proof. vm_refl. Qed.
Lemma D_7963c : decode_any W_7963c = Some (Branch BC_LTU 11 10 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796a0 : bv 32 := 0x691200ef.
Lemma F_796a0 : fetch_word Asan.M.loaded_segments (0x796f0 : word) = Some W_796a0.
Proof. vm_refl. Qed.
Lemma D_796a0 : decode_any W_796a0 = Some (Jal 1 134800, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796a4 : bv 32 := 0x000bc597.
Lemma F_796a4 : fetch_word Asan.M.loaded_segments (0x796f4 : word) = Some W_796a4.
Proof. vm_refl. Qed.
Lemma D_796a4 : decode_any W_796a4 = Some (Auipc 11 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796a8 : bv 32 := 0x8d45b583.
Lemma F_796a8 : fetch_word Asan.M.loaded_segments (0x796f8 : word) = Some W_796a8.
Proof. vm_refl. Qed.
Lemma D_796a8 : decode_any W_796a8 = Some (Load SZ8 true 11 11 2260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796ac : bv 32 := 0x0225c983.
Lemma F_796ac : fetch_word Asan.M.loaded_segments (0x796fc : word) = Some W_796ac.
Proof. vm_refl. Qed.
Lemma D_796ac : decode_any W_796ac = Some (Load SZ1 false 19 11 34, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796b0 : bv 32 := 0x00050913.
Lemma F_796b0 : fetch_word Asan.M.loaded_segments (0x79700 : word) = Some W_796b0.
Proof. vm_refl. Qed.
Lemma D_796b0 : decode_any W_796b0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796b4 : bv 32 := 0x3a0080ef.
Lemma F_796b4 : fetch_word Asan.M.loaded_segments (0x79704 : word) = Some W_796b4.
Proof. vm_refl. Qed.
Lemma D_796b4 : decode_any W_796b4 = Some (Jal 1 33696, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796b8 : bv 32 := 0x00050793.
Lemma F_796b8 : fetch_word Asan.M.loaded_segments (0x79708 : word) = Some W_796b8.
Proof. vm_refl. Qed.
Lemma D_796b8 : decode_any W_796b8 = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796bc : bv 32 := 0x00153513.
Lemma F_796bc : fetch_word Asan.M.loaded_segments (0x7970c : word) = Some W_796bc.
Proof. vm_refl. Qed.
Lemma D_796bc : decode_any W_796bc = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796c0 : bv 32 := 0xfff50513.
Lemma F_796c0 : fetch_word Asan.M.loaded_segments (0x79710 : word) = Some W_796c0.
Proof. vm_refl. Qed.
Lemma D_796c0 : decode_any W_796c0 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796c4 : bv 32 := 0x008575b3.
Lemma F_796c4 : fetch_word Asan.M.loaded_segments (0x79714 : word) = Some W_796c4.
Proof. vm_refl. Qed.
Lemma D_796c4 : decode_any W_796c4 = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796c8 : bv 32 := 0x00100513.
Lemma F_796c8 : fetch_word Asan.M.loaded_segments (0x79718 : word) = Some W_796c8.
Proof. vm_refl. Qed.
Lemma D_796c8 : decode_any W_796c8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796cc : bv 32 := 0x00bab4a3.
Lemma F_796cc : fetch_word Asan.M.loaded_segments (0x7971c : word) = Some W_796cc.
Proof. vm_refl. Qed.
Lemma D_796cc : decode_any W_796cc = Some (Store SZ8 21 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796d0 : bv 32 := 0x00f56a63.
Lemma F_796d0 : fetch_word Asan.M.loaded_segments (0x79720 : word) = Some W_796d0.
Proof. vm_refl. Qed.
Lemma D_796d0 : decode_any W_796d0 = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796e4 : bv 32 := 0x80040513.
Lemma F_796e4 : fetch_word Asan.M.loaded_segments (0x79734 : word) = Some W_796e4.
Proof. vm_refl. Qed.
Lemma D_796e4 : decode_any W_796e4 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796e8 : bv 32 := 0xfb050513.
Lemma F_796e8 : fetch_word Asan.M.loaded_segments (0x79738 : word) = Some W_796e8.
Proof. vm_refl. Qed.
Lemma D_796e8 : decode_any W_796e8 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796ec : bv 32 := 0x00090593.
Lemma F_796ec : fetch_word Asan.M.loaded_segments (0x7973c : word) = Some W_796ec.
Proof. vm_refl. Qed.
Lemma D_796ec : decode_any W_796ec = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796f0 : bv 32 := 0x00040613.
Lemma F_796f0 : fetch_word Asan.M.loaded_segments (0x79740 : word) = Some W_796f0.
Proof. vm_refl. Qed.
Lemma D_796f0 : decode_any W_796f0 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796f4 : bv 32 := 0x00000693.
Lemma F_796f4 : fetch_word Asan.M.loaded_segments (0x79744 : word) = Some W_796f4.
Proof. vm_refl. Qed.
Lemma D_796f4 : decode_any W_796f4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796f8 : bv 32 := 0x00098713.
Lemma F_796f8 : fetch_word Asan.M.loaded_segments (0x79748 : word) = Some W_796f8.
Proof. vm_refl. Qed.
Lemma D_796f8 : decode_any W_796f8 = Some (OpImm ALU_ADD 14 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_796fc : bv 32 := 0x368080ef.
Lemma F_796fc : fetch_word Asan.M.loaded_segments (0x7974c : word) = Some W_796fc.
Proof. vm_refl. Qed.
Lemma D_796fc : decode_any W_796fc = Some (Jal 1 33640, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79700 : bv 32 := 0x80040593.
Lemma F_79700 : fetch_word Asan.M.loaded_segments (0x79750 : word) = Some W_79700.
Proof. vm_refl. Qed.
Lemma D_79700 : decode_any W_79700 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79704 : bv 32 := 0xfb058593.
Lemma F_79704 : fetch_word Asan.M.loaded_segments (0x79754 : word) = Some W_79704.
Proof. vm_refl. Qed.
Lemma D_79704 : decode_any W_79704 = Some (OpImm ALU_ADD 11 11 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79708 : bv 32 := 0x00048513.
Lemma F_79708 : fetch_word Asan.M.loaded_segments (0x79758 : word) = Some W_79708.
Proof. vm_refl. Qed.
Lemma D_79708 : decode_any W_79708 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7970c : bv 32 := 0xa65d80ef.
Lemma F_7970c : fetch_word Asan.M.loaded_segments (0x7975c : word) = Some W_7970c.
Proof. vm_refl. Qed.
Lemma D_7970c : decode_any W_7970c = Some (Jal 1 1935972, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79710 : bv 32 := 0x06010113.
Lemma F_79710 : fetch_word Asan.M.loaded_segments (0x79760 : word) = Some W_79710.
Proof. vm_refl. Qed.
Lemma D_79710 : decode_any W_79710 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79714 : bv 32 := 0x7e813083.
Lemma F_79714 : fetch_word Asan.M.loaded_segments (0x79764 : word) = Some W_79714.
Proof. vm_refl. Qed.
Lemma D_79714 : decode_any W_79714 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79718 : bv 32 := 0x7e013403.
Lemma F_79718 : fetch_word Asan.M.loaded_segments (0x79768 : word) = Some W_79718.
Proof. vm_refl. Qed.
Lemma D_79718 : decode_any W_79718 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7971c : bv 32 := 0x7d813483.
Lemma F_7971c : fetch_word Asan.M.loaded_segments (0x7976c : word) = Some W_7971c.
Proof. vm_refl. Qed.
Lemma D_7971c : decode_any W_7971c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79720 : bv 32 := 0x7d013903.
Lemma F_79720 : fetch_word Asan.M.loaded_segments (0x79770 : word) = Some W_79720.
Proof. vm_refl. Qed.
Lemma D_79720 : decode_any W_79720 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79724 : bv 32 := 0x7c813983.
Lemma F_79724 : fetch_word Asan.M.loaded_segments (0x79774 : word) = Some W_79724.
Proof. vm_refl. Qed.
Lemma D_79724 : decode_any W_79724 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79728 : bv 32 := 0x7c013a03.
Lemma F_79728 : fetch_word Asan.M.loaded_segments (0x79778 : word) = Some W_79728.
Proof. vm_refl. Qed.
Lemma D_79728 : decode_any W_79728 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7972c : bv 32 := 0x7b813a83.
Lemma F_7972c : fetch_word Asan.M.loaded_segments (0x7977c : word) = Some W_7972c.
Proof. vm_refl. Qed.
Lemma D_7972c : decode_any W_7972c = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79730 : bv 32 := 0x7f010113.
Lemma F_79730 : fetch_word Asan.M.loaded_segments (0x79780 : word) = Some W_79730.
Proof. vm_refl. Qed.
Lemma D_79730 : decode_any W_79730 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79734 : bv 32 := 0x00008067.
Lemma F_79734 : fetch_word Asan.M.loaded_segments (0x79784 : word) = Some W_79734.
Proof. vm_refl. Qed.
Lemma D_79734 : decode_any W_79734 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b48 : bv 32 := 0x81010113.
Lemma F_79b48 : fetch_word Asan.M.loaded_segments (0x79b98 : word) = Some W_79b48.
Proof. vm_refl. Qed.
Lemma D_79b48 : decode_any W_79b48 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b4c : bv 32 := 0x7e113423.
Lemma F_79b4c : fetch_word Asan.M.loaded_segments (0x79b9c : word) = Some W_79b4c.
Proof. vm_refl. Qed.
Lemma D_79b4c : decode_any W_79b4c = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b50 : bv 32 := 0x7e813023.
Lemma F_79b50 : fetch_word Asan.M.loaded_segments (0x79ba0 : word) = Some W_79b50.
Proof. vm_refl. Qed.
Lemma D_79b50 : decode_any W_79b50 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b54 : bv 32 := 0x7c913c23.
Lemma F_79b54 : fetch_word Asan.M.loaded_segments (0x79ba4 : word) = Some W_79b54.
Proof. vm_refl. Qed.
Lemma D_79b54 : decode_any W_79b54 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b58 : bv 32 := 0x7d213823.
Lemma F_79b58 : fetch_word Asan.M.loaded_segments (0x79ba8 : word) = Some W_79b58.
Proof. vm_refl. Qed.
Lemma D_79b58 : decode_any W_79b58 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b5c : bv 32 := 0x7d313423.
Lemma F_79b5c : fetch_word Asan.M.loaded_segments (0x79bac : word) = Some W_79b5c.
Proof. vm_refl. Qed.
Lemma D_79b5c : decode_any W_79b5c = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b60 : bv 32 := 0x7d413023.
Lemma F_79b60 : fetch_word Asan.M.loaded_segments (0x79bb0 : word) = Some W_79b60.
Proof. vm_refl. Qed.
Lemma D_79b60 : decode_any W_79b60 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b64 : bv 32 := 0x7b513c23.
Lemma F_79b64 : fetch_word Asan.M.loaded_segments (0x79bb4 : word) = Some W_79b64.
Proof. vm_refl. Qed.
Lemma D_79b64 : decode_any W_79b64 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b68 : bv 32 := 0x7b613823.
Lemma F_79b68 : fetch_word Asan.M.loaded_segments (0x79bb8 : word) = Some W_79b68.
Proof. vm_refl. Qed.
Lemma D_79b68 : decode_any W_79b68 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b6c : bv 32 := 0x7f010413.
Lemma F_79b6c : fetch_word Asan.M.loaded_segments (0x79bbc : word) = Some W_79b6c.
Proof. vm_refl. Qed.
Lemma D_79b6c : decode_any W_79b6c = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b70 : bv 32 := 0xf9010113.
Lemma F_79b70 : fetch_word Asan.M.loaded_segments (0x79bc0 : word) = Some W_79b70.
Proof. vm_refl. Qed.
Lemma D_79b70 : decode_any W_79b70 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b74 : bv 32 := 0x00008993.
Lemma F_79b74 : fetch_word Asan.M.loaded_segments (0x79bc4 : word) = Some W_79b74.
Proof. vm_refl. Qed.
Lemma D_79b74 : decode_any W_79b74 = Some (OpImm ALU_ADD 19 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b78 : bv 32 := 0x00058493.
Lemma F_79b78 : fetch_word Asan.M.loaded_segments (0x79bc8 : word) = Some W_79b78.
Proof. vm_refl. Qed.
Lemma D_79b78 : decode_any W_79b78 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b7c : bv 32 := 0x00050913.
Lemma F_79b7c : fetch_word Asan.M.loaded_segments (0x79bcc : word) = Some W_79b7c.
Proof. vm_refl. Qed.
Lemma D_79b7c : decode_any W_79b7c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b80 : bv 32 := 0x80040a93.
Lemma F_79b80 : fetch_word Asan.M.loaded_segments (0x79bd0 : word) = Some W_79b80.
Proof. vm_refl. Qed.
Lemma D_79b80 : decode_any W_79b80 = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b84 : bv 32 := 0xfa8a8a93.
Lemma F_79b84 : fetch_word Asan.M.loaded_segments (0x79bd4 : word) = Some W_79b84.
Proof. vm_refl. Qed.
Lemma D_79b84 : decode_any W_79b84 = Some (OpImm ALU_ADD 21 21 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b88 : bv 32 := 0x80040513.
Lemma F_79b88 : fetch_word Asan.M.loaded_segments (0x79bd8 : word) = Some W_79b88.
Proof. vm_refl. Qed.
Lemma D_79b88 : decode_any W_79b88 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b8c : bv 32 := 0xfb850513.
Lemma F_79b8c : fetch_word Asan.M.loaded_segments (0x79bdc : word) = Some W_79b8c.
Proof. vm_refl. Qed.
Lemma D_79b8c : decode_any W_79b8c = Some (OpImm ALU_ADD 10 10 4024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b90 : bv 32 := 0x7ffa8b13.
Lemma F_79b90 : fetch_word Asan.M.loaded_segments (0x79be0 : word) = Some W_79b90.
Proof. vm_refl. Qed.
Lemma D_79b90 : decode_any W_79b90 = Some (OpImm ALU_ADD 22 21 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b94 : bv 32 := 0x000b34a3.
Lemma F_79b94 : fetch_word Asan.M.loaded_segments (0x79be4 : word) = Some W_79b94.
Proof. vm_refl. Qed.
Lemma D_79b94 : decode_any W_79b94 = Some (Store SZ8 22 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b98 : bv 32 := 0x00aab023.
Lemma F_79b98 : fetch_word Asan.M.loaded_segments (0x79be8 : word) = Some W_79b98.
Proof. vm_refl. Qed.
Lemma D_79b98 : decode_any W_79b98 = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79b9c : bv 32 := 0x000ab423.
Lemma F_79b9c : fetch_word Asan.M.loaded_segments (0x79bec : word) = Some W_79b9c.
Proof. vm_refl. Qed.
Lemma D_79b9c : decode_any W_79b9c = Some (Store SZ8 21 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ba0 : bv 32 := 0x6b5070ef.
Lemma F_79ba0 : fetch_word Asan.M.loaded_segments (0x79bf0 : word) = Some W_79ba0.
Proof. vm_refl. Qed.
Lemma D_79ba0 : decode_any W_79ba0 = Some (Jal 1 32436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ba4 : bv 32 := 0x00200593.
Lemma F_79ba4 : fetch_word Asan.M.loaded_segments (0x79bf4 : word) = Some W_79ba4.
Proof. vm_refl. Qed.
Lemma D_79ba4 : decode_any W_79ba4 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ba8 : bv 32 := 0x02a5ea63.
Lemma F_79ba8 : fetch_word Asan.M.loaded_segments (0x79bf8 : word) = Some W_79ba8.
Proof. vm_refl. Qed.
Lemma D_79ba8 : decode_any W_79ba8 = Some (Branch BC_LTU 11 10 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bdc : bv 32 := 0x155200ef.
Lemma F_79bdc : fetch_word Asan.M.loaded_segments (0x79c2c : word) = Some W_79bdc.
Proof. vm_refl. Qed.
Lemma D_79bdc : decode_any W_79bdc = Some (Jal 1 133460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79be0 : bv 32 := 0x000bb597.
Lemma F_79be0 : fetch_word Asan.M.loaded_segments (0x79c30 : word) = Some W_79be0.
Proof. vm_refl. Qed.
Lemma D_79be0 : decode_any W_79be0 = Some (Auipc 11 187, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79be4 : bv 32 := 0x3985b583.
Lemma F_79be4 : fetch_word Asan.M.loaded_segments (0x79c34 : word) = Some W_79be4.
Proof. vm_refl. Qed.
Lemma D_79be4 : decode_any W_79be4 = Some (Load SZ8 true 11 11 920, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79be8 : bv 32 := 0x0225ca03.
Lemma F_79be8 : fetch_word Asan.M.loaded_segments (0x79c38 : word) = Some W_79be8.
Proof. vm_refl. Qed.
Lemma D_79be8 : decode_any W_79be8 = Some (Load SZ1 false 20 11 34, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bec : bv 32 := 0x00050993.
Lemma F_79bec : fetch_word Asan.M.loaded_segments (0x79c3c : word) = Some W_79bec.
Proof. vm_refl. Qed.
Lemma D_79bec : decode_any W_79bec = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bf0 : bv 32 := 0x665070ef.
Lemma F_79bf0 : fetch_word Asan.M.loaded_segments (0x79c40 : word) = Some W_79bf0.
Proof. vm_refl. Qed.
Lemma D_79bf0 : decode_any W_79bf0 = Some (Jal 1 32356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bf4 : bv 32 := 0x00050793.
Lemma F_79bf4 : fetch_word Asan.M.loaded_segments (0x79c44 : word) = Some W_79bf4.
Proof. vm_refl. Qed.
Lemma D_79bf4 : decode_any W_79bf4 = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bf8 : bv 32 := 0x00153513.
Lemma F_79bf8 : fetch_word Asan.M.loaded_segments (0x79c48 : word) = Some W_79bf8.
Proof. vm_refl. Qed.
Lemma D_79bf8 : decode_any W_79bf8 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79bfc : bv 32 := 0xfff50513.
Lemma F_79bfc : fetch_word Asan.M.loaded_segments (0x79c4c : word) = Some W_79bfc.
Proof. vm_refl. Qed.
Lemma D_79bfc : decode_any W_79bfc = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c00 : bv 32 := 0x008575b3.
Lemma F_79c00 : fetch_word Asan.M.loaded_segments (0x79c50 : word) = Some W_79c00.
Proof. vm_refl. Qed.
Lemma D_79c00 : decode_any W_79c00 = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c04 : bv 32 := 0x00100513.
Lemma F_79c04 : fetch_word Asan.M.loaded_segments (0x79c54 : word) = Some W_79c04.
Proof. vm_refl. Qed.
Lemma D_79c04 : decode_any W_79c04 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c08 : bv 32 := 0x00bb34a3.
Lemma F_79c08 : fetch_word Asan.M.loaded_segments (0x79c58 : word) = Some W_79c08.
Proof. vm_refl. Qed.
Lemma D_79c08 : decode_any W_79c08 = Some (Store SZ8 22 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c0c : bv 32 := 0x00f56a63.
Lemma F_79c0c : fetch_word Asan.M.loaded_segments (0x79c5c : word) = Some W_79c0c.
Proof. vm_refl. Qed.
Lemma D_79c0c : decode_any W_79c0c = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c20 : bv 32 := 0x80040513.
Lemma F_79c20 : fetch_word Asan.M.loaded_segments (0x79c70 : word) = Some W_79c20.
Proof. vm_refl. Qed.
Lemma D_79c20 : decode_any W_79c20 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c24 : bv 32 := 0xfa850513.
Lemma F_79c24 : fetch_word Asan.M.loaded_segments (0x79c74 : word) = Some W_79c24.
Proof. vm_refl. Qed.
Lemma D_79c24 : decode_any W_79c24 = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c28 : bv 32 := 0x00098593.
Lemma F_79c28 : fetch_word Asan.M.loaded_segments (0x79c78 : word) = Some W_79c28.
Proof. vm_refl. Qed.
Lemma D_79c28 : decode_any W_79c28 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c2c : bv 32 := 0x00040613.
Lemma F_79c2c : fetch_word Asan.M.loaded_segments (0x79c7c : word) = Some W_79c2c.
Proof. vm_refl. Qed.
Lemma D_79c2c : decode_any W_79c2c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c30 : bv 32 := 0x00000693.
Lemma F_79c30 : fetch_word Asan.M.loaded_segments (0x79c80 : word) = Some W_79c30.
Proof. vm_refl. Qed.
Lemma D_79c30 : decode_any W_79c30 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c34 : bv 32 := 0x000a0713.
Lemma F_79c34 : fetch_word Asan.M.loaded_segments (0x79c84 : word) = Some W_79c34.
Proof. vm_refl. Qed.
Lemma D_79c34 : decode_any W_79c34 = Some (OpImm ALU_ADD 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c38 : bv 32 := 0x62d070ef.
Lemma F_79c38 : fetch_word Asan.M.loaded_segments (0x79c88 : word) = Some W_79c38.
Proof. vm_refl. Qed.
Lemma D_79c38 : decode_any W_79c38 = Some (Jal 1 32300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c3c : bv 32 := 0x80040613.
Lemma F_79c3c : fetch_word Asan.M.loaded_segments (0x79c8c : word) = Some W_79c3c.
Proof. vm_refl. Qed.
Lemma D_79c3c : decode_any W_79c3c = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c40 : bv 32 := 0xfa860613.
Lemma F_79c40 : fetch_word Asan.M.loaded_segments (0x79c90 : word) = Some W_79c40.
Proof. vm_refl. Qed.
Lemma D_79c40 : decode_any W_79c40 = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c44 : bv 32 := 0x00090513.
Lemma F_79c44 : fetch_word Asan.M.loaded_segments (0x79c94 : word) = Some W_79c44.
Proof. vm_refl. Qed.
Lemma D_79c44 : decode_any W_79c44 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c48 : bv 32 := 0x00048593.
Lemma F_79c48 : fetch_word Asan.M.loaded_segments (0x79c98 : word) = Some W_79c48.
Proof. vm_refl. Qed.
Lemma D_79c48 : decode_any W_79c48 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c4c : bv 32 := 0x914d90ef.
Lemma F_79c4c : fetch_word Asan.M.loaded_segments (0x79c9c : word) = Some W_79c4c.
Proof. vm_refl. Qed.
Lemma D_79c4c : decode_any W_79c4c = Some (Jal 1 1937684, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c50 : bv 32 := 0x07010113.
Lemma F_79c50 : fetch_word Asan.M.loaded_segments (0x79ca0 : word) = Some W_79c50.
Proof. vm_refl. Qed.
Lemma D_79c50 : decode_any W_79c50 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c54 : bv 32 := 0x7e813083.
Lemma F_79c54 : fetch_word Asan.M.loaded_segments (0x79ca4 : word) = Some W_79c54.
Proof. vm_refl. Qed.
Lemma D_79c54 : decode_any W_79c54 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c58 : bv 32 := 0x7e013403.
Lemma F_79c58 : fetch_word Asan.M.loaded_segments (0x79ca8 : word) = Some W_79c58.
Proof. vm_refl. Qed.
Lemma D_79c58 : decode_any W_79c58 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c5c : bv 32 := 0x7d813483.
Lemma F_79c5c : fetch_word Asan.M.loaded_segments (0x79cac : word) = Some W_79c5c.
Proof. vm_refl. Qed.
Lemma D_79c5c : decode_any W_79c5c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c60 : bv 32 := 0x7d013903.
Lemma F_79c60 : fetch_word Asan.M.loaded_segments (0x79cb0 : word) = Some W_79c60.
Proof. vm_refl. Qed.
Lemma D_79c60 : decode_any W_79c60 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c64 : bv 32 := 0x7c813983.
Lemma F_79c64 : fetch_word Asan.M.loaded_segments (0x79cb4 : word) = Some W_79c64.
Proof. vm_refl. Qed.
Lemma D_79c64 : decode_any W_79c64 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c68 : bv 32 := 0x7c013a03.
Lemma F_79c68 : fetch_word Asan.M.loaded_segments (0x79cb8 : word) = Some W_79c68.
Proof. vm_refl. Qed.
Lemma D_79c68 : decode_any W_79c68 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c6c : bv 32 := 0x7b813a83.
Lemma F_79c6c : fetch_word Asan.M.loaded_segments (0x79cbc : word) = Some W_79c6c.
Proof. vm_refl. Qed.
Lemma D_79c6c : decode_any W_79c6c = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c70 : bv 32 := 0x7b013b03.
Lemma F_79c70 : fetch_word Asan.M.loaded_segments (0x79cc0 : word) = Some W_79c70.
Proof. vm_refl. Qed.
Lemma D_79c70 : decode_any W_79c70 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c74 : bv 32 := 0x7f010113.
Lemma F_79c74 : fetch_word Asan.M.loaded_segments (0x79cc4 : word) = Some W_79c74.
Proof. vm_refl. Qed.
Lemma D_79c74 : decode_any W_79c74 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79c78 : bv 32 := 0x00008067.
Lemma F_79c78 : fetch_word Asan.M.loaded_segments (0x79cc8 : word) = Some W_79c78.
Proof. vm_refl. Qed.
Lemma D_79c78 : decode_any W_79c78 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

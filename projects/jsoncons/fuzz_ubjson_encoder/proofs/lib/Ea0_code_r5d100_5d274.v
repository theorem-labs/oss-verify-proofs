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

Definition W_5e3c4 : bv 32 := 0xfe010113.
Lemma F_5e3c4 : fetch_word Asan.M.loaded_segments (0x5e414 : word) = Some W_5e3c4.
Proof. vm_refl. Qed.
Lemma D_5e3c4 : decode_any W_5e3c4 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3c8 : bv 32 := 0x00113c23.
Lemma F_5e3c8 : fetch_word Asan.M.loaded_segments (0x5e418 : word) = Some W_5e3c8.
Proof. vm_refl. Qed.
Lemma D_5e3c8 : decode_any W_5e3c8 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3cc : bv 32 := 0x00813823.
Lemma F_5e3cc : fetch_word Asan.M.loaded_segments (0x5e41c : word) = Some W_5e3cc.
Proof. vm_refl. Qed.
Lemma D_5e3cc : decode_any W_5e3cc = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3d0 : bv 32 := 0x00913423.
Lemma F_5e3d0 : fetch_word Asan.M.loaded_segments (0x5e420 : word) = Some W_5e3d0.
Proof. vm_refl. Qed.
Lemma D_5e3d0 : decode_any W_5e3d0 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3d4 : bv 32 := 0x01213023.
Lemma F_5e3d4 : fetch_word Asan.M.loaded_segments (0x5e424 : word) = Some W_5e3d4.
Proof. vm_refl. Qed.
Lemma D_5e3d4 : decode_any W_5e3d4 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3d8 : bv 32 := 0x02010413.
Lemma F_5e3d8 : fetch_word Asan.M.loaded_segments (0x5e428 : word) = Some W_5e3d8.
Proof. vm_refl. Qed.
Lemma D_5e3d8 : decode_any W_5e3d8 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3dc : bv 32 := 0x000dc517.
Lemma F_5e3dc : fetch_word Asan.M.loaded_segments (0x5e42c : word) = Some W_5e3dc.
Proof. vm_refl. Qed.
Lemma D_5e3dc : decode_any W_5e3dc = Some (Auipc 10 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3e0 : bv 32 := 0xb8450513.
Lemma F_5e3e0 : fetch_word Asan.M.loaded_segments (0x5e430 : word) = Some W_5e3e0.
Proof. vm_refl. Qed.
Lemma D_5e3e0 : decode_any W_5e3e0 = Some (OpImm ALU_ADD 10 10 2948, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3e4 : bv 32 := 0x141050ef.
Lemma F_5e3e4 : fetch_word Asan.M.loaded_segments (0x5e434 : word) = Some W_5e3e4.
Proof. vm_refl. Qed.
Lemma D_5e3e4 : decode_any W_5e3e4 = Some (Jal 1 22848, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3e8 : bv 32 := 0x00053483.
Lemma F_5e3e8 : fetch_word Asan.M.loaded_segments (0x5e438 : word) = Some W_5e3e8.
Proof. vm_refl. Qed.
Lemma D_5e3e8 : decode_any W_5e3e8 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3ec : bv 32 := 0x08048063.
Lemma F_5e3ec : fetch_word Asan.M.loaded_segments (0x5e43c : word) = Some W_5e3ec.
Proof. vm_refl. Qed.
Lemma D_5e3ec : decode_any W_5e3ec = Some (Branch BC_EQ 9 0 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3f0 : bv 32 := 0x0604c503.
Lemma F_5e3f0 : fetch_word Asan.M.loaded_segments (0x5e440 : word) = Some W_5e3f0.
Proof. vm_refl. Qed.
Lemma D_5e3f0 : decode_any W_5e3f0 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3f4 : bv 32 := 0x0584b903.
Lemma F_5e3f4 : fetch_word Asan.M.loaded_segments (0x5e444 : word) = Some W_5e3f4.
Proof. vm_refl. Qed.
Lemma D_5e3f4 : decode_any W_5e3f4 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3f8 : bv 32 := 0x00050863.
Lemma F_5e3f8 : fetch_word Asan.M.loaded_segments (0x5e448 : word) = Some W_5e3f8.
Proof. vm_refl. Qed.
Lemma D_5e3f8 : decode_any W_5e3f8 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e3fc : bv 32 := 0x00048513.
Lemma F_5e3fc : fetch_word Asan.M.loaded_segments (0x5e44c : word) = Some W_5e3fc.
Proof. vm_refl. Qed.
Lemma D_5e3fc : decode_any W_5e3fc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e400 : bv 32 := 0x00040593.
Lemma F_5e400 : fetch_word Asan.M.loaded_segments (0x5e450 : word) = Some W_5e400.
Proof. vm_refl. Qed.
Lemma D_5e400 : decode_any W_5e400 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e404 : bv 32 := 0xb75ff0ef.
Lemma F_5e404 : fetch_word Asan.M.loaded_segments (0x5e454 : word) = Some W_5e404.
Proof. vm_refl. Qed.
Lemma D_5e404 : decode_any W_5e404 = Some (Jal 1 2095988, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e408 : bv 32 := 0xffa90593.
Lemma F_5e408 : fetch_word Asan.M.loaded_segments (0x5e458 : word) = Some W_5e408.
Proof. vm_refl. Qed.
Lemma D_5e408 : decode_any W_5e408 = Some (OpImm ALU_ADD 11 18 4090, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e40c : bv 32 := 0x00100513.
Lemma F_5e40c : fetch_word Asan.M.loaded_segments (0x5e45c : word) = Some W_5e40c.
Proof. vm_refl. Qed.
Lemma D_5e40c : decode_any W_5e40c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e410 : bv 32 := 0x00b51533.
Lemma F_5e410 : fetch_word Asan.M.loaded_segments (0x5e460 : word) = Some W_5e410.
Proof. vm_refl. Qed.
Lemma D_5e410 : decode_any W_5e410 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e414 : bv 32 := 0x0005061b.
Lemma F_5e414 : fetch_word Asan.M.loaded_segments (0x5e464 : word) = Some W_5e414.
Proof. vm_refl. Qed.
Lemma D_5e414 : decode_any W_5e414 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e418 : bv 32 := 0x06c05a63.
Lemma F_5e418 : fetch_word Asan.M.loaded_segments (0x5e468 : word) = Some W_5e418.
Proof. vm_refl. Qed.
Lemma D_5e418 : decode_any W_5e418 = Some (Branch BC_GE 0 12 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e41c : bv 32 := 0x000016b7.
Lemma F_5e41c : fetch_word Asan.M.loaded_segments (0x5e46c : word) = Some W_5e41c.
Proof. vm_refl. Qed.
Lemma D_5e41c : decode_any W_5e41c = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e420 : bv 32 := 0xfff00713.
Lemma F_5e420 : fetch_word Asan.M.loaded_segments (0x5e470 : word) = Some W_5e420.
Proof. vm_refl. Qed.
Lemma D_5e420 : decode_any W_5e420 = Some (OpImm ALU_ADD 14 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e424 : bv 32 := 0x0004b603.
Lemma F_5e424 : fetch_word Asan.M.loaded_segments (0x5e474 : word) = Some W_5e424.
Proof. vm_refl. Qed.
Lemma D_5e424 : decode_any W_5e424 = Some (Load SZ8 true 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e428 : bv 32 := 0x00b71733.
Lemma F_5e428 : fetch_word Asan.M.loaded_segments (0x5e478 : word) = Some W_5e428.
Proof. vm_refl. Qed.
Lemma D_5e428 : decode_any W_5e428 = Some (Op ALU_SLL 14 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e42c : bv 32 := 0xfff50793.
Lemma F_5e42c : fetch_word Asan.M.loaded_segments (0x5e47c : word) = Some W_5e42c.
Proof. vm_refl. Qed.
Lemma D_5e42c : decode_any W_5e42c = Some (OpImm ALU_ADD 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e430 : bv 32 := 0x00d485b3.
Lemma F_5e430 : fetch_word Asan.M.loaded_segments (0x5e480 : word) = Some W_5e430.
Proof. vm_refl. Qed.
Lemma D_5e430 : decode_any W_5e430 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e434 : bv 32 := 0xfff74693.
Lemma F_5e434 : fetch_word Asan.M.loaded_segments (0x5e484 : word) = Some W_5e434.
Proof. vm_refl. Qed.
Lemma D_5e434 : decode_any W_5e434 = Some (OpImm ALU_XOR 13 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e438 : bv 32 := 0x02079793.
Lemma F_5e438 : fetch_word Asan.M.loaded_segments (0x5e488 : word) = Some W_5e438.
Proof. vm_refl. Qed.
Lemma D_5e438 : decode_any W_5e438 = Some (ShiftImm ALU_SLL 15 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e43c : bv 32 := 0x0207d793.
Lemma F_5e43c : fetch_word Asan.M.loaded_segments (0x5e48c : word) = Some W_5e43c.
Proof. vm_refl. Qed.
Lemma D_5e43c : decode_any W_5e43c = Some (ShiftImm ALU_SRL 15 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e440 : bv 32 := 0x00f60733.
Lemma F_5e440 : fetch_word Asan.M.loaded_segments (0x5e490 : word) = Some W_5e440.
Proof. vm_refl. Qed.
Lemma D_5e440 : decode_any W_5e440 = Some (Op ALU_ADD 14 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e444 : bv 32 := 0x00170713.
Lemma F_5e444 : fetch_word Asan.M.loaded_segments (0x5e494 : word) = Some W_5e444.
Proof. vm_refl. Qed.
Lemma D_5e444 : decode_any W_5e444 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e448 : bv 32 := 0x00d67833.
Lemma F_5e448 : fetch_word Asan.M.loaded_segments (0x5e498 : word) = Some W_5e448.
Proof. vm_refl. Qed.
Lemma D_5e448 : decode_any W_5e448 = Some (Op ALU_AND 16 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e44c : bv 32 := 0x010587b3.
Lemma F_5e44c : fetch_word Asan.M.loaded_segments (0x5e49c : word) = Some W_5e44c.
Proof. vm_refl. Qed.
Lemma D_5e44c : decode_any W_5e44c = Some (Op ALU_ADD 15 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e450 : bv 32 := 0x0007c883.
Lemma F_5e450 : fetch_word Asan.M.loaded_segments (0x5e4a0 : word) = Some W_5e450.
Proof. vm_refl. Qed.
Lemma D_5e450 : decode_any W_5e450 = Some (Load SZ1 false 17 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e454 : bv 32 := 0x06088663.
Lemma F_5e454 : fetch_word Asan.M.loaded_segments (0x5e4a4 : word) = Some W_5e454.
Proof. vm_refl. Qed.
Lemma D_5e454 : decode_any W_5e454 = Some (Branch BC_EQ 17 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e458 : bv 32 := 0xfff5051b.
Lemma F_5e458 : fetch_word Asan.M.loaded_segments (0x5e4a8 : word) = Some W_5e458.
Proof. vm_refl. Qed.
Lemma D_5e458 : decode_any W_5e458 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e45c : bv 32 := 0x00160613.
Lemma F_5e45c : fetch_word Asan.M.loaded_segments (0x5e4ac : word) = Some W_5e45c.
Proof. vm_refl. Qed.
Lemma D_5e45c : decode_any W_5e45c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e460 : bv 32 := 0xfe0514e3.
Lemma F_5e460 : fetch_word Asan.M.loaded_segments (0x5e4b0 : word) = Some W_5e460.
Proof. vm_refl. Qed.
Lemma D_5e460 : decode_any W_5e460 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e464 : bv 32 := 0x00e4b023.
Lemma F_5e464 : fetch_word Asan.M.loaded_segments (0x5e4b4 : word) = Some W_5e464.
Proof. vm_refl. Qed.
Lemma D_5e464 : decode_any W_5e464 = Some (Store SZ8 9 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e468 : bv 32 := 0x0400006f.
Lemma F_5e468 : fetch_word Asan.M.loaded_segments (0x5e4b8 : word) = Some W_5e468.
Proof. vm_refl. Qed.
Lemma D_5e468 : decode_any W_5e468 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e46c : bv 32 := 0x000db517.
Lemma F_5e46c : fetch_word Asan.M.loaded_segments (0x5e4bc : word) = Some W_5e46c.
Proof. vm_refl. Qed.
Lemma D_5e46c : decode_any W_5e46c = Some (Auipc 10 219, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e470 : bv 32 := 0xd5453503.
Lemma F_5e470 : fetch_word Asan.M.loaded_segments (0x5e4c0 : word) = Some W_5e470.
Proof. vm_refl. Qed.
Lemma D_5e470 : decode_any W_5e470 = Some (Load SZ8 true 10 10 3412, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e474 : bv 32 := 0x00052503.
Lemma F_5e474 : fetch_word Asan.M.loaded_segments (0x5e4c4 : word) = Some W_5e474.
Proof. vm_refl. Qed.
Lemma D_5e474 : decode_any W_5e474 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e478 : bv 32 := 0x02050863.
Lemma F_5e478 : fetch_word Asan.M.loaded_segments (0x5e4c8 : word) = Some W_5e478.
Proof. vm_refl. Qed.
Lemma D_5e478 : decode_any W_5e478 = Some (Branch BC_EQ 10 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e47c : bv 32 := 0x59d250ef.
Lemma F_5e47c : fetch_word Asan.M.loaded_segments (0x5e4cc : word) = Some W_5e47c.
Proof. vm_refl. Qed.
Lemma D_5e47c : decode_any W_5e47c = Some (Jal 1 155036, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e480 : bv 32 := 0x02050463.
Lemma F_5e480 : fetch_word Asan.M.loaded_segments (0x5e4d0 : word) = Some W_5e480.
Proof. vm_refl. Qed.
Lemma D_5e480 : decode_any W_5e480 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e484 : bv 32 := 0x02850583.
Lemma F_5e484 : fetch_word Asan.M.loaded_segments (0x5e4d4 : word) = Some W_5e484.
Proof. vm_refl. Qed.
Lemma D_5e484 : decode_any W_5e484 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e488 : bv 32 := 0x08058a63.
Lemma F_5e488 : fetch_word Asan.M.loaded_segments (0x5e4d8 : word) = Some W_5e488.
Proof. vm_refl. Qed.
Lemma D_5e488 : decode_any W_5e488 = Some (Branch BC_EQ 11 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e48c : bv 32 := 0x00000513.
Lemma F_5e48c : fetch_word Asan.M.loaded_segments (0x5e4dc : word) = Some W_5e48c.
Proof. vm_refl. Qed.
Lemma D_5e48c : decode_any W_5e48c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e490 : bv 32 := 0x01813083.
Lemma F_5e490 : fetch_word Asan.M.loaded_segments (0x5e4e0 : word) = Some W_5e490.
Proof. vm_refl. Qed.
Lemma D_5e490 : decode_any W_5e490 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e494 : bv 32 := 0x01013403.
Lemma F_5e494 : fetch_word Asan.M.loaded_segments (0x5e4e4 : word) = Some W_5e494.
Proof. vm_refl. Qed.
Lemma D_5e494 : decode_any W_5e494 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e498 : bv 32 := 0x00813483.
Lemma F_5e498 : fetch_word Asan.M.loaded_segments (0x5e4e8 : word) = Some W_5e498.
Proof. vm_refl. Qed.
Lemma D_5e498 : decode_any W_5e498 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e49c : bv 32 := 0x00013903.
Lemma F_5e49c : fetch_word Asan.M.loaded_segments (0x5e4ec : word) = Some W_5e49c.
Proof. vm_refl. Qed.
Lemma D_5e49c : decode_any W_5e49c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4a0 : bv 32 := 0x02010113.
Lemma F_5e4a0 : fetch_word Asan.M.loaded_segments (0x5e4f0 : word) = Some W_5e4a0.
Proof. vm_refl. Qed.
Lemma D_5e4a0 : decode_any W_5e4a0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4a4 : bv 32 := 0x00008067.
Lemma F_5e4a4 : fetch_word Asan.M.loaded_segments (0x5e4f4 : word) = Some W_5e4a4.
Proof. vm_refl. Qed.
Lemma D_5e4a4 : decode_any W_5e4a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4a8 : bv 32 := 0x01813083.
Lemma F_5e4a8 : fetch_word Asan.M.loaded_segments (0x5e4f8 : word) = Some W_5e4a8.
Proof. vm_refl. Qed.
Lemma D_5e4a8 : decode_any W_5e4a8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4ac : bv 32 := 0x01013403.
Lemma F_5e4ac : fetch_word Asan.M.loaded_segments (0x5e4fc : word) = Some W_5e4ac.
Proof. vm_refl. Qed.
Lemma D_5e4ac : decode_any W_5e4ac = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4b0 : bv 32 := 0x00813483.
Lemma F_5e4b0 : fetch_word Asan.M.loaded_segments (0x5e500 : word) = Some W_5e4b0.
Proof. vm_refl. Qed.
Lemma D_5e4b0 : decode_any W_5e4b0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4b4 : bv 32 := 0x00013903.
Lemma F_5e4b4 : fetch_word Asan.M.loaded_segments (0x5e504 : word) = Some W_5e4b4.
Proof. vm_refl. Qed.
Lemma D_5e4b4 : decode_any W_5e4b4 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4b8 : bv 32 := 0x02010113.
Lemma F_5e4b8 : fetch_word Asan.M.loaded_segments (0x5e508 : word) = Some W_5e4b8.
Proof. vm_refl. Qed.
Lemma D_5e4b8 : decode_any W_5e4b8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4bc : bv 32 := 0x00008067.
Lemma F_5e4bc : fetch_word Asan.M.loaded_segments (0x5e50c : word) = Some W_5e4bc.
Proof. vm_refl. Qed.
Lemma D_5e4bc : decode_any W_5e4bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4c0 : bv 32 := 0x00160613.
Lemma F_5e4c0 : fetch_word Asan.M.loaded_segments (0x5e510 : word) = Some W_5e4c0.
Proof. vm_refl. Qed.
Lemma D_5e4c0 : decode_any W_5e4c0 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4c4 : bv 32 := 0x00100513.
Lemma F_5e4c4 : fetch_word Asan.M.loaded_segments (0x5e514 : word) = Some W_5e4c4.
Proof. vm_refl. Qed.
Lemma D_5e4c4 : decode_any W_5e4c4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4c8 : bv 32 := 0xffb90913.
Lemma F_5e4c8 : fetch_word Asan.M.loaded_segments (0x5e518 : word) = Some W_5e4c8.
Proof. vm_refl. Qed.
Lemma D_5e4c8 : decode_any W_5e4c8 = Some (OpImm ALU_ADD 18 18 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4cc : bv 32 := 0x00681813.
Lemma F_5e4cc : fetch_word Asan.M.loaded_segments (0x5e51c : word) = Some W_5e4cc.
Proof. vm_refl. Qed.
Lemma D_5e4cc : decode_any W_5e4cc = Some (ShiftImm ALU_SLL 16 16 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4d0 : bv 32 := 0x00c4b023.
Lemma F_5e4d0 : fetch_word Asan.M.loaded_segments (0x5e520 : word) = Some W_5e4d0.
Proof. vm_refl. Qed.
Lemma D_5e4d0 : decode_any W_5e4d0 = Some (Store SZ8 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4d4 : bv 32 := 0x00a78023.
Lemma F_5e4d4 : fetch_word Asan.M.loaded_segments (0x5e524 : word) = Some W_5e4d4.
Proof. vm_refl. Qed.
Lemma D_5e4d4 : decode_any W_5e4d4 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4d8 : bv 32 := 0x01251533.
Lemma F_5e4d8 : fetch_word Asan.M.loaded_segments (0x5e528 : word) = Some W_5e4d8.
Proof. vm_refl. Qed.
Lemma D_5e4d8 : decode_any W_5e4d8 = Some (Op ALU_SLL 10 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4dc : bv 32 := 0x00a58533.
Lemma F_5e4dc : fetch_word Asan.M.loaded_segments (0x5e52c : word) = Some W_5e4dc.
Proof. vm_refl. Qed.
Lemma D_5e4dc : decode_any W_5e4dc = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4e0 : bv 32 := 0x010504b3.
Lemma F_5e4e0 : fetch_word Asan.M.loaded_segments (0x5e530 : word) = Some W_5e4e0.
Proof. vm_refl. Qed.
Lemma D_5e4e0 : decode_any W_5e4e0 = Some (Op ALU_ADD 9 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4e4 : bv 32 := 0x0084bc23.
Lemma F_5e4e4 : fetch_word Asan.M.loaded_segments (0x5e534 : word) = Some W_5e4e4.
Proof. vm_refl. Qed.
Lemma D_5e4e4 : decode_any W_5e4e4 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4e8 : bv 32 := 0x02f4bc23.
Lemma F_5e4e8 : fetch_word Asan.M.loaded_segments (0x5e538 : word) = Some W_5e4e8.
Proof. vm_refl. Qed.
Lemma D_5e4e8 : decode_any W_5e4e8 = Some (Store SZ8 9 15 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4ec : bv 32 := 0x00048513.
Lemma F_5e4ec : fetch_word Asan.M.loaded_segments (0x5e53c : word) = Some W_5e4ec.
Proof. vm_refl. Qed.
Lemma D_5e4ec : decode_any W_5e4ec = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4f0 : bv 32 := 0x7e0000ef.
Lemma F_5e4f0 : fetch_word Asan.M.loaded_segments (0x5e540 : word) = Some W_5e4f0.
Proof. vm_refl. Qed.
Lemma D_5e4f0 : decode_any W_5e4f0 = Some (Jal 1 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4f4 : bv 32 := 0x00050593.
Lemma F_5e4f4 : fetch_word Asan.M.loaded_segments (0x5e544 : word) = Some W_5e4f4.
Proof. vm_refl. Qed.
Lemma D_5e4f4 : decode_any W_5e4f4 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4f8 : bv 32 := 0x00048513.
Lemma F_5e4f8 : fetch_word Asan.M.loaded_segments (0x5e548 : word) = Some W_5e4f8.
Proof. vm_refl. Qed.
Lemma D_5e4f8 : decode_any W_5e4f8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e4fc : bv 32 := 0x00000613.
Lemma F_5e4fc : fetch_word Asan.M.loaded_segments (0x5e54c : word) = Some W_5e4fc.
Proof. vm_refl. Qed.
Lemma D_5e4fc : decode_any W_5e4fc = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e500 : bv 32 := 0x0005b023.
Lemma F_5e500 : fetch_word Asan.M.loaded_segments (0x5e550 : word) = Some W_5e500.
Proof. vm_refl. Qed.
Lemma D_5e500 : decode_any W_5e500 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e504 : bv 32 := 0x01813083.
Lemma F_5e504 : fetch_word Asan.M.loaded_segments (0x5e554 : word) = Some W_5e504.
Proof. vm_refl. Qed.
Lemma D_5e504 : decode_any W_5e504 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e508 : bv 32 := 0x01013403.
Lemma F_5e508 : fetch_word Asan.M.loaded_segments (0x5e558 : word) = Some W_5e508.
Proof. vm_refl. Qed.
Lemma D_5e508 : decode_any W_5e508 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e50c : bv 32 := 0x00813483.
Lemma F_5e50c : fetch_word Asan.M.loaded_segments (0x5e55c : word) = Some W_5e50c.
Proof. vm_refl. Qed.
Lemma D_5e50c : decode_any W_5e50c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e510 : bv 32 := 0x00013903.
Lemma F_5e510 : fetch_word Asan.M.loaded_segments (0x5e560 : word) = Some W_5e510.
Proof. vm_refl. Qed.
Lemma D_5e510 : decode_any W_5e510 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e514 : bv 32 := 0x02010113.
Lemma F_5e514 : fetch_word Asan.M.loaded_segments (0x5e564 : word) = Some W_5e514.
Proof. vm_refl. Qed.
Lemma D_5e514 : decode_any W_5e514 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e518 : bv 32 := 0x00008067.
Lemma F_5e518 : fetch_word Asan.M.loaded_segments (0x5e568 : word) = Some W_5e518.
Proof. vm_refl. Qed.
Lemma D_5e518 : decode_any W_5e518 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e51c : bv 32 := 0x04853483.
Lemma F_5e51c : fetch_word Asan.M.loaded_segments (0x5e56c : word) = Some W_5e51c.
Proof. vm_refl. Qed.
Lemma D_5e51c : decode_any W_5e51c = Some (Load SZ8 true 9 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e520 : bv 32 := 0x00100593.
Lemma F_5e520 : fetch_word Asan.M.loaded_segments (0x5e570 : word) = Some W_5e520.
Proof. vm_refl. Qed.
Lemma D_5e520 : decode_any W_5e520 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e524 : bv 32 := 0x0095e663.
Lemma F_5e524 : fetch_word Asan.M.loaded_segments (0x5e574 : word) = Some W_5e524.
Proof. vm_refl. Qed.
Lemma D_5e524 : decode_any W_5e524 = Some (Branch BC_LTU 11 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e528 : bv 32 := 0x765250ef.
Lemma F_5e528 : fetch_word Asan.M.loaded_segments (0x5e578 : word) = Some W_5e528.
Proof. vm_refl. Qed.
Lemma D_5e528 : decode_any W_5e528 = Some (Jal 1 155492, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e52c : bv 32 := 0x00050493.
Lemma F_5e52c : fetch_word Asan.M.loaded_segments (0x5e57c : word) = Some W_5e52c.
Proof. vm_refl. Qed.
Lemma D_5e52c : decode_any W_5e52c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e530 : bv 32 := 0xec0490e3.
Lemma F_5e530 : fetch_word Asan.M.loaded_segments (0x5e580 : word) = Some W_5e530.
Proof. vm_refl. Qed.
Lemma D_5e530 : decode_any W_5e530 = Some (Branch BC_NE 9 0 7872, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e534 : bv 32 := 0xf59ff06f.
Lemma F_5e534 : fetch_word Asan.M.loaded_segments (0x5e584 : word) = Some W_5e534.
Proof. vm_refl. Qed.
Lemma D_5e534 : decode_any W_5e534 = Some (Jal 0 2096984, 4%Z).
Proof. vm_refl. Qed.

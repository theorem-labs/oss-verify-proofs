(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_38428 : bv 32 := 0xfc010113.
Lemma F_38428 : fetch_word Ubsan.M.loaded_segments (0x38428 : word) = Some W_38428.
Proof. vm_refl. Qed.
Lemma D_38428 : decode_any W_38428 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_3842c : bv 32 := 0x02113c23.
Lemma F_3842c : fetch_word Ubsan.M.loaded_segments (0x3842c : word) = Some W_3842c.
Proof. vm_refl. Qed.
Lemma D_3842c : decode_any W_3842c = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_38430 : bv 32 := 0x02813823.
Lemma F_38430 : fetch_word Ubsan.M.loaded_segments (0x38430 : word) = Some W_38430.
Proof. vm_refl. Qed.
Lemma D_38430 : decode_any W_38430 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_38434 : bv 32 := 0x02913423.
Lemma F_38434 : fetch_word Ubsan.M.loaded_segments (0x38434 : word) = Some W_38434.
Proof. vm_refl. Qed.
Lemma D_38434 : decode_any W_38434 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_38438 : bv 32 := 0x03213023.
Lemma F_38438 : fetch_word Ubsan.M.loaded_segments (0x38438 : word) = Some W_38438.
Proof. vm_refl. Qed.
Lemma D_38438 : decode_any W_38438 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3843c : bv 32 := 0x01313c23.
Lemma F_3843c : fetch_word Ubsan.M.loaded_segments (0x3843c : word) = Some W_3843c.
Proof. vm_refl. Qed.
Lemma D_3843c : decode_any W_3843c = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_38440 : bv 32 := 0x01413823.
Lemma F_38440 : fetch_word Ubsan.M.loaded_segments (0x38440 : word) = Some W_38440.
Proof. vm_refl. Qed.
Lemma D_38440 : decode_any W_38440 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_38444 : bv 32 := 0x01513423.
Lemma F_38444 : fetch_word Ubsan.M.loaded_segments (0x38444 : word) = Some W_38444.
Proof. vm_refl. Qed.
Lemma D_38444 : decode_any W_38444 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_38448 : bv 32 := 0x01613023.
Lemma F_38448 : fetch_word Ubsan.M.loaded_segments (0x38448 : word) = Some W_38448.
Proof. vm_refl. Qed.
Lemma D_38448 : decode_any W_38448 = Some (Store SZ8 2 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3844c : bv 32 := 0x00058413.
Lemma F_3844c : fetch_word Ubsan.M.loaded_segments (0x3844c : word) = Some W_3844c.
Proof. vm_refl. Qed.
Lemma D_3844c : decode_any W_3844c = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38450 : bv 32 := 0xfffe85b7.
Lemma F_38450 : fetch_word Ubsan.M.loaded_segments (0x38450 : word) = Some W_38450.
Proof. vm_refl. Qed.
Lemma D_38450 : decode_any W_38450 = Some (Lui 11 1048552, 4%Z).
Proof. vm_refl. Qed.

Definition W_38454 : bv 32 := 0x95f5859b.
Lemma F_38454 : fetch_word Ubsan.M.loaded_segments (0x38454 : word) = Some W_38454.
Proof. vm_refl. Qed.
Lemma D_38454 : decode_any W_38454 = Some (OpImm32 11 11 2399, 4%Z).
Proof. vm_refl. Qed.

Definition W_38458 : bv 32 := 0x00b4063b.
Lemma F_38458 : fetch_word Ubsan.M.loaded_segments (0x38458 : word) = Some W_38458.
Proof. vm_refl. Qed.
Lemma D_38458 : decode_any W_38458 = Some (Op32 ALU_ADD 12 8 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3845c : bv 32 := 0x02c5e263.
Lemma F_3845c : fetch_word Ubsan.M.loaded_segments (0x3845c : word) = Some W_3845c.
Proof. vm_refl. Qed.
Lemma D_3845c : decode_any W_3845c = Some (Branch BC_LTU 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_38460 : bv 32 := 0x0000d517.
Lemma F_38460 : fetch_word Ubsan.M.loaded_segments (0x38460 : word) = Some W_38460.
Proof. vm_refl. Qed.
Lemma D_38460 : decode_any W_38460 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_38464 : bv 32 := 0xa3853503.
Lemma F_38464 : fetch_word Ubsan.M.loaded_segments (0x38464 : word) = Some W_38464.
Proof. vm_refl. Qed.
Lemma D_38464 : decode_any W_38464 = Some (Load SZ8 true 10 10 2616, 4%Z).
Proof. vm_refl. Qed.

Definition W_38468 : bv 32 := 0x00052503.
Lemma F_38468 : fetch_word Ubsan.M.loaded_segments (0x38468 : word) = Some W_38468.
Proof. vm_refl. Qed.
Lemma D_38468 : decode_any W_38468 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3846c : bv 32 := 0x00600593.
Lemma F_3846c : fetch_word Ubsan.M.loaded_segments (0x3846c : word) = Some W_3846c.
Proof. vm_refl. Qed.
Lemma D_3846c : decode_any W_3846c = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_38470 : bv 32 := 0x06b55663.
Lemma F_38470 : fetch_word Ubsan.M.loaded_segments (0x38470 : word) = Some W_38470.
Proof. vm_refl. Qed.
Lemma D_38470 : decode_any W_38470 = Some (Branch BC_GE 10 11 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_38474 : bv 32 := 0xfffda517.
Lemma F_38474 : fetch_word Ubsan.M.loaded_segments (0x38474 : word) = Some W_38474.
Proof. vm_refl. Qed.
Lemma D_38474 : decode_any W_38474 = Some (Auipc 10 1048538, 4%Z).
Proof. vm_refl. Qed.

Definition W_38478 : bv 32 := 0xd6250513.
Lemma F_38478 : fetch_word Ubsan.M.loaded_segments (0x38478 : word) = Some W_38478.
Proof. vm_refl. Qed.
Lemma D_38478 : decode_any W_38478 = Some (OpImm ALU_ADD 10 10 3426, 4%Z).
Proof. vm_refl. Qed.

Definition W_3847c : bv 32 := 0x02c0006f.
Lemma F_3847c : fetch_word Ubsan.M.loaded_segments (0x3847c : word) = Some W_3847c.
Proof. vm_refl. Qed.
Lemma D_3847c : decode_any W_3847c = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_38480 : bv 32 := 0x00050493.
Lemma F_38480 : fetch_word Ubsan.M.loaded_segments (0x38480 : word) = Some W_38480.
Proof. vm_refl. Qed.
Lemma D_38480 : decode_any W_38480 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38484 : bv 32 := 0x00b5053b.
Lemma F_38484 : fetch_word Ubsan.M.loaded_segments (0x38484 : word) = Some W_38484.
Proof. vm_refl. Qed.
Lemma D_38484 : decode_any W_38484 = Some (Op32 ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_38488 : bv 32 := 0x04a5ee63.
Lemma F_38488 : fetch_word Ubsan.M.loaded_segments (0x38488 : word) = Some W_38488.
Proof. vm_refl. Qed.
Lemma D_38488 : decode_any W_38488 = Some (Branch BC_LTU 11 10 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_3848c : bv 32 := 0x0000d517.
Lemma F_3848c : fetch_word Ubsan.M.loaded_segments (0x3848c : word) = Some W_3848c.
Proof. vm_refl. Qed.
Lemma D_3848c : decode_any W_3848c = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_38490 : bv 32 := 0xa0c53503.
Lemma F_38490 : fetch_word Ubsan.M.loaded_segments (0x38490 : word) = Some W_38490.
Proof. vm_refl. Qed.
Lemma D_38490 : decode_any W_38490 = Some (Load SZ8 true 10 10 2572, 4%Z).
Proof. vm_refl. Qed.

Definition W_38494 : bv 32 := 0x00052503.
Lemma F_38494 : fetch_word Ubsan.M.loaded_segments (0x38494 : word) = Some W_38494.
Proof. vm_refl. Qed.
Lemma D_38494 : decode_any W_38494 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38498 : bv 32 := 0x00600593.
Lemma F_38498 : fetch_word Ubsan.M.loaded_segments (0x38498 : word) = Some W_38498.
Proof. vm_refl. Qed.
Lemma D_38498 : decode_any W_38498 = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_3849c : bv 32 := 0x04b55063.
Lemma F_3849c : fetch_word Ubsan.M.loaded_segments (0x3849c : word) = Some W_3849c.
Proof. vm_refl. Qed.
Lemma D_3849c : decode_any W_3849c = Some (Branch BC_GE 10 11 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_384a0 : bv 32 := 0xfffd9517.
Lemma F_384a0 : fetch_word Ubsan.M.loaded_segments (0x384a0 : word) = Some W_384a0.
Proof. vm_refl. Qed.
Lemma D_384a0 : decode_any W_384a0 = Some (Auipc 10 1048537, 4%Z).
Proof. vm_refl. Qed.

Definition W_384a4 : bv 32 := 0xca250513.
Lemma F_384a4 : fetch_word Ubsan.M.loaded_segments (0x384a4 : word) = Some W_384a4.
Proof. vm_refl. Qed.
Lemma D_384a4 : decode_any W_384a4 = Some (OpImm ALU_ADD 10 10 3234, 4%Z).
Proof. vm_refl. Qed.

Definition W_384a8 : bv 32 := 0xfffd8597.
Lemma F_384a8 : fetch_word Ubsan.M.loaded_segments (0x384a8 : word) = Some W_384a8.
Proof. vm_refl. Qed.
Lemma D_384a8 : decode_any W_384a8 = Some (Auipc 11 1048536, 4%Z).
Proof. vm_refl. Qed.

Definition W_384ac : bv 32 := 0x5f358593.
Lemma F_384ac : fetch_word Ubsan.M.loaded_segments (0x384ac : word) = Some W_384ac.
Proof. vm_refl. Qed.
Lemma D_384ac : decode_any W_384ac = Some (OpImm ALU_ADD 11 11 1523, 4%Z).
Proof. vm_refl. Qed.

Definition W_384b0 : bv 32 := 0x00000613.
Lemma F_384b0 : fetch_word Ubsan.M.loaded_segments (0x384b0 : word) = Some W_384b0.
Proof. vm_refl. Qed.
Lemma D_384b0 : decode_any W_384b0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_384b4 : bv 32 := 0x03813083.
Lemma F_384b4 : fetch_word Ubsan.M.loaded_segments (0x384b4 : word) = Some W_384b4.
Proof. vm_refl. Qed.
Lemma D_384b4 : decode_any W_384b4 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_384b8 : bv 32 := 0x03013403.
Lemma F_384b8 : fetch_word Ubsan.M.loaded_segments (0x384b8 : word) = Some W_384b8.
Proof. vm_refl. Qed.
Lemma D_384b8 : decode_any W_384b8 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_384bc : bv 32 := 0x02813483.
Lemma F_384bc : fetch_word Ubsan.M.loaded_segments (0x384bc : word) = Some W_384bc.
Proof. vm_refl. Qed.
Lemma D_384bc : decode_any W_384bc = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_384c0 : bv 32 := 0x02013903.
Lemma F_384c0 : fetch_word Ubsan.M.loaded_segments (0x384c0 : word) = Some W_384c0.
Proof. vm_refl. Qed.
Lemma D_384c0 : decode_any W_384c0 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_384c4 : bv 32 := 0x01813983.
Lemma F_384c4 : fetch_word Ubsan.M.loaded_segments (0x384c4 : word) = Some W_384c4.
Proof. vm_refl. Qed.
Lemma D_384c4 : decode_any W_384c4 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_384c8 : bv 32 := 0x01013a03.
Lemma F_384c8 : fetch_word Ubsan.M.loaded_segments (0x384c8 : word) = Some W_384c8.
Proof. vm_refl. Qed.
Lemma D_384c8 : decode_any W_384c8 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_384cc : bv 32 := 0x00813a83.
Lemma F_384cc : fetch_word Ubsan.M.loaded_segments (0x384cc : word) = Some W_384cc.
Proof. vm_refl. Qed.
Lemma D_384cc : decode_any W_384cc = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_384d0 : bv 32 := 0x00013b03.
Lemma F_384d0 : fetch_word Ubsan.M.loaded_segments (0x384d0 : word) = Some W_384d0.
Proof. vm_refl. Qed.
Lemma D_384d0 : decode_any W_384d0 = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_384d4 : bv 32 := 0x04010113.
Lemma F_384d4 : fetch_word Ubsan.M.loaded_segments (0x384d4 : word) = Some W_384d4.
Proof. vm_refl. Qed.
Lemma D_384d4 : decode_any W_384d4 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_384d8 : bv 32 := 0x9eddf06f.
Lemma F_384d8 : fetch_word Ubsan.M.loaded_segments (0x384d8 : word) = Some W_384d8.
Proof. vm_refl. Qed.
Lemma D_384d8 : decode_any W_384d8 = Some (Jal 0 1964524, 4%Z).
Proof. vm_refl. Qed.

Definition W_384dc : bv 32 := 0x00000913.
Lemma F_384dc : fetch_word Ubsan.M.loaded_segments (0x384dc : word) = Some W_384dc.
Proof. vm_refl. Qed.
Lemma D_384dc : decode_any W_384dc = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_384e0 : bv 32 := 0x0600006f.
Lemma F_384e0 : fetch_word Ubsan.M.loaded_segments (0x384e0 : word) = Some W_384e0.
Proof. vm_refl. Qed.
Lemma D_384e0 : decode_any W_384e0 = Some (Jal 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_384e4 : bv 32 := 0x00800593.
Lemma F_384e4 : fetch_word Ubsan.M.loaded_segments (0x384e4 : word) = Some W_384e4.
Proof. vm_refl. Qed.
Lemma D_384e4 : decode_any W_384e4 = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_384e8 : bv 32 := 0x00048513.
Lemma F_384e8 : fetch_word Ubsan.M.loaded_segments (0x384e8 : word) = Some W_384e8.
Proof. vm_refl. Qed.
Lemma D_384e8 : decode_any W_384e8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_384ec : bv 32 := 0x40d030ef.
Lemma F_384ec : fetch_word Ubsan.M.loaded_segments (0x384ec : word) = Some W_384ec.
Proof. vm_refl. Qed.
Lemma D_384ec : decode_any W_384ec = Some (Jal 1 15372, 4%Z).
Proof. vm_refl. Qed.

Definition W_384f0 : bv 32 := 0x00050913.
Lemma F_384f0 : fetch_word Ubsan.M.loaded_segments (0x384f0 : word) = Some W_384f0.
Proof. vm_refl. Qed.
Lemma D_384f0 : decode_any W_384f0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_384f4 : bv 32 := 0x00a039b3.
Lemma F_384f4 : fetch_word Ubsan.M.loaded_segments (0x384f4 : word) = Some W_384f4.
Proof. vm_refl. Qed.
Lemma D_384f4 : decode_any W_384f4 = Some (Op ALU_SLTU 19 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_384f8 : bv 32 := 0x00757513.
Lemma F_384f8 : fetch_word Ubsan.M.loaded_segments (0x384f8 : word) = Some W_384f8.
Proof. vm_refl. Qed.
Lemma D_384f8 : decode_any W_384f8 = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_384fc : bv 32 := 0x00153513.
Lemma F_384fc : fetch_word Ubsan.M.loaded_segments (0x384fc : word) = Some W_384fc.
Proof. vm_refl. Qed.
Lemma D_384fc : decode_any W_384fc = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_38500 : bv 32 := 0x01357a33.
Lemma F_38500 : fetch_word Ubsan.M.loaded_segments (0x38500 : word) = Some W_38500.
Proof. vm_refl. Qed.
Lemma D_38500 : decode_any W_38500 = Some (Op ALU_AND 20 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_38504 : bv 32 := 0x00090a93.
Lemma F_38504 : fetch_word Ubsan.M.loaded_segments (0x38504 : word) = Some W_38504.
Proof. vm_refl. Qed.
Lemma D_38504 : decode_any W_38504 = Some (OpImm ALU_ADD 21 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38508 : bv 32 := 0x00090b13.
Lemma F_38508 : fetch_word Ubsan.M.loaded_segments (0x38508 : word) = Some W_38508.
Proof. vm_refl. Qed.
Lemma D_38508 : decode_any W_38508 = Some (OpImm ALU_ADD 22 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3850c : bv 32 := 0x00400593.
Lemma F_3850c : fetch_word Ubsan.M.loaded_segments (0x3850c : word) = Some W_3850c.
Proof. vm_refl. Qed.
Lemma D_3850c : decode_any W_3850c = Some (OpImm ALU_ADD 11 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_38510 : bv 32 := 0x00040513.
Lemma F_38510 : fetch_word Ubsan.M.loaded_segments (0x38510 : word) = Some W_38510.
Proof. vm_refl. Qed.
Lemma D_38510 : decode_any W_38510 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38514 : bv 32 := 0x3e5030ef.
Lemma F_38514 : fetch_word Ubsan.M.loaded_segments (0x38514 : word) = Some W_38514.
Proof. vm_refl. Qed.
Lemma D_38514 : decode_any W_38514 = Some (Jal 1 15332, 4%Z).
Proof. vm_refl. Qed.

Definition W_38518 : bv 32 := 0x052b6a63.
Lemma F_38518 : fetch_word Ubsan.M.loaded_segments (0x38518 : word) = Some W_38518.
Proof. vm_refl. Qed.
Lemma D_38518 : decode_any W_38518 = Some (Branch BC_LTU 22 18 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_3851c : bv 32 := 0x001b3593.
Lemma F_3851c : fetch_word Ubsan.M.loaded_segments (0x3851c : word) = Some W_3851c.
Proof. vm_refl. Qed.
Lemma D_3851c : decode_any W_3851c = Some (OpImm ALU_SLTU 11 22 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_38520 : bv 32 := 0x00b9c5b3.
Lemma F_38520 : fetch_word Ubsan.M.loaded_segments (0x38520 : word) = Some W_38520.
Proof. vm_refl. Qed.
Lemma D_38520 : decode_any W_38520 = Some (Op ALU_XOR 11 19 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_38524 : bv 32 := 0x04058463.
Lemma F_38524 : fetch_word Ubsan.M.loaded_segments (0x38524 : word) = Some W_38524.
Proof. vm_refl. Qed.
Lemma D_38524 : decode_any W_38524 = Some (Branch BC_EQ 11 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_38528 : bv 32 := 0x040a0263.
Lemma F_38528 : fetch_word Ubsan.M.loaded_segments (0x38528 : word) = Some W_38528.
Proof. vm_refl. Qed.
Lemma D_38528 : decode_any W_38528 = Some (Branch BC_EQ 20 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_3852c : bv 32 := 0x00aab023.
Lemma F_3852c : fetch_word Ubsan.M.loaded_segments (0x3852c : word) = Some W_3852c.
Proof. vm_refl. Qed.
Lemma D_3852c : decode_any W_3852c = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38530 : bv 32 := 0x008b0b13.
Lemma F_38530 : fetch_word Ubsan.M.loaded_segments (0x38530 : word) = Some W_38530.
Proof. vm_refl. Qed.
Lemma D_38530 : decode_any W_38530 = Some (OpImm ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_38534 : bv 32 := 0xfff48493.
Lemma F_38534 : fetch_word Ubsan.M.loaded_segments (0x38534 : word) = Some W_38534.
Proof. vm_refl. Qed.
Lemma D_38534 : decode_any W_38534 = Some (OpImm ALU_ADD 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_38538 : bv 32 := 0x008a8a93.
Lemma F_38538 : fetch_word Ubsan.M.loaded_segments (0x38538 : word) = Some W_38538.
Proof. vm_refl. Qed.
Lemma D_38538 : decode_any W_38538 = Some (OpImm ALU_ADD 21 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3853c : bv 32 := 0xfc0498e3.
Lemma F_3853c : fetch_word Ubsan.M.loaded_segments (0x3853c : word) = Some W_3853c.
Proof. vm_refl. Qed.
Lemma D_3853c : decode_any W_3853c = Some (Branch BC_NE 9 0 8144, 4%Z).
Proof. vm_refl. Qed.

Definition W_38540 : bv 32 := 0x00090513.
Lemma F_38540 : fetch_word Ubsan.M.loaded_segments (0x38540 : word) = Some W_38540.
Proof. vm_refl. Qed.
Lemma D_38540 : decode_any W_38540 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38544 : bv 32 := 0x03813083.
Lemma F_38544 : fetch_word Ubsan.M.loaded_segments (0x38544 : word) = Some W_38544.
Proof. vm_refl. Qed.
Lemma D_38544 : decode_any W_38544 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_38548 : bv 32 := 0x03013403.
Lemma F_38548 : fetch_word Ubsan.M.loaded_segments (0x38548 : word) = Some W_38548.
Proof. vm_refl. Qed.
Lemma D_38548 : decode_any W_38548 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3854c : bv 32 := 0x02813483.
Lemma F_3854c : fetch_word Ubsan.M.loaded_segments (0x3854c : word) = Some W_3854c.
Proof. vm_refl. Qed.
Lemma D_3854c : decode_any W_3854c = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_38550 : bv 32 := 0x02013903.
Lemma F_38550 : fetch_word Ubsan.M.loaded_segments (0x38550 : word) = Some W_38550.
Proof. vm_refl. Qed.
Lemma D_38550 : decode_any W_38550 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_38554 : bv 32 := 0x01813983.
Lemma F_38554 : fetch_word Ubsan.M.loaded_segments (0x38554 : word) = Some W_38554.
Proof. vm_refl. Qed.
Lemma D_38554 : decode_any W_38554 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_38558 : bv 32 := 0x01013a03.
Lemma F_38558 : fetch_word Ubsan.M.loaded_segments (0x38558 : word) = Some W_38558.
Proof. vm_refl. Qed.
Lemma D_38558 : decode_any W_38558 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3855c : bv 32 := 0x00813a83.
Lemma F_3855c : fetch_word Ubsan.M.loaded_segments (0x3855c : word) = Some W_3855c.
Proof. vm_refl. Qed.
Lemma D_3855c : decode_any W_3855c = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_38560 : bv 32 := 0x00013b03.
Lemma F_38560 : fetch_word Ubsan.M.loaded_segments (0x38560 : word) = Some W_38560.
Proof. vm_refl. Qed.
Lemma D_38560 : decode_any W_38560 = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38564 : bv 32 := 0x04010113.
Lemma F_38564 : fetch_word Ubsan.M.loaded_segments (0x38564 : word) = Some W_38564.
Proof. vm_refl. Qed.
Lemma D_38564 : decode_any W_38564 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_38568 : bv 32 := 0x00008067.
Lemma F_38568 : fetch_word Ubsan.M.loaded_segments (0x38568 : word) = Some W_38568.
Proof. vm_refl. Qed.
Lemma D_38568 : decode_any W_38568 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3856c : bv 32 := 0xc0001073.
Lemma F_3856c : fetch_word Ubsan.M.loaded_segments (0x3856c : word) = Some W_3856c.
Proof. vm_refl. Qed.
Lemma D_3856c : decode_any W_3856c = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.

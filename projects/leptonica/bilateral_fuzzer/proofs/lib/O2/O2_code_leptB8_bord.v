(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_1968c : bv 32 := 0x00058463.
Lemma F_1968c : fetch_word Plain.M.loaded_segments (0x196e4 : word) = Some W_1968c.
Proof. vm_refl. Qed.
Lemma D_1968c : decode_any W_1968c = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19690 : bv 32 := 0x0005a023.
Lemma F_19690 : fetch_word Plain.M.loaded_segments (0x196e8 : word) = Some W_19690.
Proof. vm_refl. Qed.
Lemma D_19690 : decode_any W_19690 = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19694 : bv 32 := 0x00060463.
Lemma F_19694 : fetch_word Plain.M.loaded_segments (0x196ec : word) = Some W_19694.
Proof. vm_refl. Qed.
Lemma D_19694 : decode_any W_19694 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19698 : bv 32 := 0x00062023.
Lemma F_19698 : fetch_word Plain.M.loaded_segments (0x196f0 : word) = Some W_19698.
Proof. vm_refl. Qed.
Lemma D_19698 : decode_any W_19698 = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1969c : bv 32 := 0x00068463.
Lemma F_1969c : fetch_word Plain.M.loaded_segments (0x196f4 : word) = Some W_1969c.
Proof. vm_refl. Qed.
Lemma D_1969c : decode_any W_1969c = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196a0 : bv 32 := 0x0006a023.
Lemma F_196a0 : fetch_word Plain.M.loaded_segments (0x196f8 : word) = Some W_196a0.
Proof. vm_refl. Qed.
Lemma D_196a0 : decode_any W_196a0 = Some (Store SZ4 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196a4 : bv 32 := 0x02050a63.
Lemma F_196a4 : fetch_word Plain.M.loaded_segments (0x196fc : word) = Some W_196a4.
Proof. vm_refl. Qed.
Lemma D_196a4 : decode_any W_196a4 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196a8 : bv 32 := 0x00058663.
Lemma F_196a8 : fetch_word Plain.M.loaded_segments (0x19700 : word) = Some W_196a8.
Proof. vm_refl. Qed.
Lemma D_196a8 : decode_any W_196a8 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196ac : bv 32 := 0x00052703.
Lemma F_196ac : fetch_word Plain.M.loaded_segments (0x19704 : word) = Some W_196ac.
Proof. vm_refl. Qed.
Lemma D_196ac : decode_any W_196ac = Some (Load SZ4 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196b0 : bv 32 := 0x00e5a023.
Lemma F_196b0 : fetch_word Plain.M.loaded_segments (0x19708 : word) = Some W_196b0.
Proof. vm_refl. Qed.
Lemma D_196b0 : decode_any W_196b0 = Some (Store SZ4 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196b4 : bv 32 := 0x00060663.
Lemma F_196b4 : fetch_word Plain.M.loaded_segments (0x1970c : word) = Some W_196b4.
Proof. vm_refl. Qed.
Lemma D_196b4 : decode_any W_196b4 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196b8 : bv 32 := 0x00452583.
Lemma F_196b8 : fetch_word Plain.M.loaded_segments (0x19710 : word) = Some W_196b8.
Proof. vm_refl. Qed.
Lemma D_196b8 : decode_any W_196b8 = Some (Load SZ4 true 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196bc : bv 32 := 0x00b62023.
Lemma F_196bc : fetch_word Plain.M.loaded_segments (0x19714 : word) = Some W_196bc.
Proof. vm_refl. Qed.
Lemma D_196bc : decode_any W_196bc = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196c0 : bv 32 := 0x00000593.
Lemma F_196c0 : fetch_word Plain.M.loaded_segments (0x19718 : word) = Some W_196c0.
Proof. vm_refl. Qed.
Lemma D_196c0 : decode_any W_196c0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196c4 : bv 32 := 0x00068663.
Lemma F_196c4 : fetch_word Plain.M.loaded_segments (0x1971c : word) = Some W_196c4.
Proof. vm_refl. Qed.
Lemma D_196c4 : decode_any W_196c4 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196c8 : bv 32 := 0x00852503.
Lemma F_196c8 : fetch_word Plain.M.loaded_segments (0x19720 : word) = Some W_196c8.
Proof. vm_refl. Qed.
Lemma D_196c8 : decode_any W_196c8 = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196cc : bv 32 := 0x00a6a023.
Lemma F_196cc : fetch_word Plain.M.loaded_segments (0x19724 : word) = Some W_196cc.
Proof. vm_refl. Qed.
Lemma D_196cc : decode_any W_196cc = Some (Store SZ4 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196d0 : bv 32 := 0x00058513.
Lemma F_196d0 : fetch_word Plain.M.loaded_segments (0x19728 : word) = Some W_196d0.
Proof. vm_refl. Qed.
Lemma D_196d0 : decode_any W_196d0 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196d4 : bv 32 := 0x00008067.
Lemma F_196d4 : fetch_word Plain.M.loaded_segments (0x1972c : word) = Some W_196d4.
Proof. vm_refl. Qed.
Lemma D_196d4 : decode_any W_196d4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b400 : bv 32 := 0xf8010113.
Lemma F_1b400 : fetch_word Plain.M.loaded_segments (0x1b458 : word) = Some W_1b400.
Proof. vm_refl. Qed.
Lemma D_1b400 : decode_any W_1b400 = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b404 : bv 32 := 0x06113c23.
Lemma F_1b404 : fetch_word Plain.M.loaded_segments (0x1b45c : word) = Some W_1b404.
Proof. vm_refl. Qed.
Lemma D_1b404 : decode_any W_1b404 = Some (Store SZ8 2 1 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b408 : bv 32 := 0x06813823.
Lemma F_1b408 : fetch_word Plain.M.loaded_segments (0x1b460 : word) = Some W_1b408.
Proof. vm_refl. Qed.
Lemma D_1b408 : decode_any W_1b408 = Some (Store SZ8 2 8 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b40c : bv 32 := 0x06913423.
Lemma F_1b40c : fetch_word Plain.M.loaded_segments (0x1b464 : word) = Some W_1b40c.
Proof. vm_refl. Qed.
Lemma D_1b40c : decode_any W_1b40c = Some (Store SZ8 2 9 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b410 : bv 32 := 0x07213023.
Lemma F_1b410 : fetch_word Plain.M.loaded_segments (0x1b468 : word) = Some W_1b410.
Proof. vm_refl. Qed.
Lemma D_1b410 : decode_any W_1b410 = Some (Store SZ8 2 18 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b414 : bv 32 := 0x05313c23.
Lemma F_1b414 : fetch_word Plain.M.loaded_segments (0x1b46c : word) = Some W_1b414.
Proof. vm_refl. Qed.
Lemma D_1b414 : decode_any W_1b414 = Some (Store SZ8 2 19 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b418 : bv 32 := 0x05413823.
Lemma F_1b418 : fetch_word Plain.M.loaded_segments (0x1b470 : word) = Some W_1b418.
Proof. vm_refl. Qed.
Lemma D_1b418 : decode_any W_1b418 = Some (Store SZ8 2 20 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b41c : bv 32 := 0x05513423.
Lemma F_1b41c : fetch_word Plain.M.loaded_segments (0x1b474 : word) = Some W_1b41c.
Proof. vm_refl. Qed.
Lemma D_1b41c : decode_any W_1b41c = Some (Store SZ8 2 21 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b420 : bv 32 := 0x05613023.
Lemma F_1b420 : fetch_word Plain.M.loaded_segments (0x1b478 : word) = Some W_1b420.
Proof. vm_refl. Qed.
Lemma D_1b420 : decode_any W_1b420 = Some (Store SZ8 2 22 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b424 : bv 32 := 0x03713c23.
Lemma F_1b424 : fetch_word Plain.M.loaded_segments (0x1b47c : word) = Some W_1b424.
Proof. vm_refl. Qed.
Lemma D_1b424 : decode_any W_1b424 = Some (Store SZ8 2 23 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b428 : bv 32 := 0x03813823.
Lemma F_1b428 : fetch_word Plain.M.loaded_segments (0x1b480 : word) = Some W_1b428.
Proof. vm_refl. Qed.
Lemma D_1b428 : decode_any W_1b428 = Some (Store SZ8 2 24 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b42c : bv 32 := 0x03913423.
Lemma F_1b42c : fetch_word Plain.M.loaded_segments (0x1b484 : word) = Some W_1b42c.
Proof. vm_refl. Qed.
Lemma D_1b42c : decode_any W_1b42c = Some (Store SZ8 2 25 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b430 : bv 32 := 0x03a13023.
Lemma F_1b430 : fetch_word Plain.M.loaded_segments (0x1b488 : word) = Some W_1b430.
Proof. vm_refl. Qed.
Lemma D_1b430 : decode_any W_1b430 = Some (Store SZ8 2 26 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b434 : bv 32 := 0x14050463.
Lemma F_1b434 : fetch_word Plain.M.loaded_segments (0x1b48c : word) = Some W_1b434.
Proof. vm_refl. Qed.
Lemma D_1b434 : decode_any W_1b434 = Some (Branch BC_EQ 10 0 328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b438 : bv 32 := 0x00070a13.
Lemma F_1b438 : fetch_word Plain.M.loaded_segments (0x1b490 : word) = Some W_1b438.
Proof. vm_refl. Qed.
Lemma D_1b438 : decode_any W_1b438 = Some (OpImm ALU_ADD 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b43c : bv 32 := 0x00068493.
Lemma F_1b43c : fetch_word Plain.M.loaded_segments (0x1b494 : word) = Some W_1b43c.
Proof. vm_refl. Qed.
Lemma D_1b43c : decode_any W_1b43c = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b440 : bv 32 := 0x00060a93.
Lemma F_1b440 : fetch_word Plain.M.loaded_segments (0x1b498 : word) = Some W_1b440.
Proof. vm_refl. Qed.
Lemma D_1b440 : decode_any W_1b440 = Some (OpImm ALU_ADD 21 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b444 : bv 32 := 0x00058913.
Lemma F_1b444 : fetch_word Plain.M.loaded_segments (0x1b49c : word) = Some W_1b444.
Proof. vm_refl. Qed.
Lemma D_1b444 : decode_any W_1b444 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b448 : bv 32 := 0x00050413.
Lemma F_1b448 : fetch_word Plain.M.loaded_segments (0x1b4a0 : word) = Some W_1b448.
Proof. vm_refl. Qed.
Lemma D_1b448 : decode_any W_1b448 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b44c : bv 32 := 0x00b66533.
Lemma F_1b44c : fetch_word Plain.M.loaded_segments (0x1b4a4 : word) = Some W_1b44c.
Proof. vm_refl. Qed.
Lemma D_1b44c : decode_any W_1b44c = Some (Op ALU_OR 10 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b450 : bv 32 := 0x00e6e5b3.
Lemma F_1b450 : fetch_word Plain.M.loaded_segments (0x1b4a8 : word) = Some W_1b450.
Proof. vm_refl. Qed.
Lemma D_1b450 : decode_any W_1b450 = Some (Op ALU_OR 11 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b454 : bv 32 := 0x00b56533.
Lemma F_1b454 : fetch_word Plain.M.loaded_segments (0x1b4ac : word) = Some W_1b454.
Proof. vm_refl. Qed.
Lemma D_1b454 : decode_any W_1b454 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b458 : bv 32 := 0x14054663.
Lemma F_1b458 : fetch_word Plain.M.loaded_segments (0x1b4b0 : word) = Some W_1b458.
Proof. vm_refl. Qed.
Lemma D_1b458 : decode_any W_1b458 = Some (Branch BC_LT 10 0 332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b45c : bv 32 := 0x00078d13.
Lemma F_1b45c : fetch_word Plain.M.loaded_segments (0x1b4b4 : word) = Some W_1b45c.
Proof. vm_refl. Qed.
Lemma D_1b45c : decode_any W_1b45c = Some (OpImm ALU_ADD 26 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b460 : bv 32 := 0x01c10593.
Lemma F_1b460 : fetch_word Plain.M.loaded_segments (0x1b4b8 : word) = Some W_1b460.
Proof. vm_refl. Qed.
Lemma D_1b460 : decode_any W_1b460 = Some (OpImm ALU_ADD 11 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b464 : bv 32 := 0x01810613.
Lemma F_1b464 : fetch_word Plain.M.loaded_segments (0x1b4bc : word) = Some W_1b464.
Proof. vm_refl. Qed.
Lemma D_1b464 : decode_any W_1b464 = Some (OpImm ALU_ADD 12 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b468 : bv 32 := 0x01410693.
Lemma F_1b468 : fetch_word Plain.M.loaded_segments (0x1b4c0 : word) = Some W_1b468.
Proof. vm_refl. Qed.
Lemma D_1b468 : decode_any W_1b468 = Some (OpImm ALU_ADD 13 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b46c : bv 32 := 0x00040513.
Lemma F_1b46c : fetch_word Plain.M.loaded_segments (0x1b4c4 : word) = Some W_1b46c.
Proof. vm_refl. Qed.
Lemma D_1b46c : decode_any W_1b46c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b470 : bv 32 := 0xa1cfe0ef.
Lemma F_1b470 : fetch_word Plain.M.loaded_segments (0x1b4c8 : word) = Some W_1b470.
Proof. vm_refl. Qed.
Lemma D_1b470 : decode_any W_1b470 = Some (Jal 1 2089500, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b474 : bv 32 := 0x01c12503.
Lemma F_1b474 : fetch_word Plain.M.loaded_segments (0x1b4cc : word) = Some W_1b474.
Proof. vm_refl. Qed.
Lemma D_1b474 : decode_any W_1b474 = Some (Load SZ4 true 10 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b478 : bv 32 := 0x01812583.
Lemma F_1b478 : fetch_word Plain.M.loaded_segments (0x1b4d0 : word) = Some W_1b478.
Proof. vm_refl. Qed.
Lemma D_1b478 : decode_any W_1b478 = Some (Load SZ4 true 11 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b47c : bv 32 := 0x01412603.
Lemma F_1b47c : fetch_word Plain.M.loaded_segments (0x1b4d4 : word) = Some W_1b47c.
Proof. vm_refl. Qed.
Lemma D_1b47c : decode_any W_1b47c = Some (Load SZ4 true 12 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b480 : bv 32 := 0x01250c3b.
Lemma F_1b480 : fetch_word Plain.M.loaded_segments (0x1b4d8 : word) = Some W_1b480.
Proof. vm_refl. Qed.
Lemma D_1b480 : decode_any W_1b480 = Some (Op32 ALU_ADD 24 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b484 : bv 32 := 0x00958bbb.
Lemma F_1b484 : fetch_word Plain.M.loaded_segments (0x1b4dc : word) = Some W_1b484.
Proof. vm_refl. Qed.
Lemma D_1b484 : decode_any W_1b484 = Some (Op32 ALU_ADD 23 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b488 : bv 32 := 0x015c0b3b.
Lemma F_1b488 : fetch_word Plain.M.loaded_segments (0x1b4e0 : word) = Some W_1b488.
Proof. vm_refl. Qed.
Lemma D_1b488 : decode_any W_1b488 = Some (Op32 ALU_ADD 22 24 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b48c : bv 32 := 0x014b8cbb.
Lemma F_1b48c : fetch_word Plain.M.loaded_segments (0x1b4e4 : word) = Some W_1b48c.
Proof. vm_refl. Qed.
Lemma D_1b48c : decode_any W_1b48c = Some (Op32 ALU_ADD 25 23 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b490 : bv 32 := 0x000b0513.
Lemma F_1b490 : fetch_word Plain.M.loaded_segments (0x1b4e8 : word) = Some W_1b490.
Proof. vm_refl. Qed.
Lemma D_1b490 : decode_any W_1b490 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b494 : bv 32 := 0x000c8593.
Lemma F_1b494 : fetch_word Plain.M.loaded_segments (0x1b4ec : word) = Some W_1b494.
Proof. vm_refl. Qed.
Lemma D_1b494 : decode_any W_1b494 = Some (OpImm ALU_ADD 11 25 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b498 : bv 32 := 0xa35fd0ef.
Lemma F_1b498 : fetch_word Plain.M.loaded_segments (0x1b4f0 : word) = Some W_1b498.
Proof. vm_refl. Qed.
Lemma D_1b498 : decode_any W_1b498 = Some (Jal 1 2087476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b49c : bv 32 := 0x16050463.
Lemma F_1b49c : fetch_word Plain.M.loaded_segments (0x1b4f4 : word) = Some W_1b49c.
Proof. vm_refl. Qed.
Lemma D_1b49c : decode_any W_1b49c = Some (Branch BC_EQ 10 0 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4a0 : bv 32 := 0x00050993.
Lemma F_1b4a0 : fetch_word Plain.M.loaded_segments (0x1b4f8 : word) = Some W_1b4a0.
Proof. vm_refl. Qed.
Lemma D_1b4a0 : decode_any W_1b4a0 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4a4 : bv 32 := 0x00040593.
Lemma F_1b4a4 : fetch_word Plain.M.loaded_segments (0x1b4fc : word) = Some W_1b4a4.
Proof. vm_refl. Qed.
Lemma D_1b4a4 : decode_any W_1b4a4 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4a8 : bv 32 := 0xa64fe0ef.
Lemma F_1b4a8 : fetch_word Plain.M.loaded_segments (0x1b500 : word) = Some W_1b4a8.
Proof. vm_refl. Qed.
Lemma D_1b4a8 : decode_any W_1b4a8 = Some (Jal 1 2089572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4ac : bv 32 := 0x00098513.
Lemma F_1b4ac : fetch_word Plain.M.loaded_segments (0x1b504 : word) = Some W_1b4ac.
Proof. vm_refl. Qed.
Lemma D_1b4ac : decode_any W_1b4ac = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4b0 : bv 32 := 0x00040593.
Lemma F_1b4b0 : fetch_word Plain.M.loaded_segments (0x1b508 : word) = Some W_1b4b0.
Proof. vm_refl. Qed.
Lemma D_1b4b0 : decode_any W_1b4b0 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4b4 : bv 32 := 0xae0fe0ef.
Lemma F_1b4b4 : fetch_word Plain.M.loaded_segments (0x1b50c : word) = Some W_1b4b4.
Proof. vm_refl. Qed.
Lemma D_1b4b4 : decode_any W_1b4b4 = Some (Jal 1 2089696, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4b8 : bv 32 := 0x020d0063.
Lemma F_1b4b8 : fetch_word Plain.M.loaded_segments (0x1b510 : word) = Some W_1b4b8.
Proof. vm_refl. Qed.
Lemma D_1b4b8 : decode_any W_1b4b8 = Some (Branch BC_EQ 26 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4bc : bv 32 := 0x000d0593.
Lemma F_1b4bc : fetch_word Plain.M.loaded_segments (0x1b514 : word) = Some W_1b4bc.
Proof. vm_refl. Qed.
Lemma D_1b4bc : decode_any W_1b4bc = Some (OpImm ALU_ADD 11 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4c0 : bv 32 := 0x01416503.
Lemma F_1b4c0 : fetch_word Plain.M.loaded_segments (0x1b518 : word) = Some W_1b4c0.
Proof. vm_refl. Qed.
Lemma D_1b4c0 : decode_any W_1b4c0 = Some (Load SZ4 false 10 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4c4 : bv 32 := 0x02000613.
Lemma F_1b4c4 : fetch_word Plain.M.loaded_segments (0x1b51c : word) = Some W_1b4c4.
Proof. vm_refl. Qed.
Lemma D_1b4c4 : decode_any W_1b4c4 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4c8 : bv 32 := 0x16c51c63.
Lemma F_1b4c8 : fetch_word Plain.M.loaded_segments (0x1b520 : word) = Some W_1b4c8.
Proof. vm_refl. Qed.
Lemma D_1b4c8 : decode_any W_1b4c8 = Some (Branch BC_NE 10 12 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4d4 : bv 32 := 0x00f00d13.
Lemma F_1b4d4 : fetch_word Plain.M.loaded_segments (0x1b52c : word) = Some W_1b4d4.
Proof. vm_refl. Qed.
Lemma D_1b4d4 : decode_any W_1b4d4 = Some (OpImm ALU_ADD 26 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4d8 : bv 32 := 0x00013023.
Lemma F_1b4d8 : fetch_word Plain.M.loaded_segments (0x1b530 : word) = Some W_1b4d8.
Proof. vm_refl. Qed.
Lemma D_1b4d8 : decode_any W_1b4d8 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4dc : bv 32 := 0x00098513.
Lemma F_1b4dc : fetch_word Plain.M.loaded_segments (0x1b534 : word) = Some W_1b4dc.
Proof. vm_refl. Qed.
Lemma D_1b4dc : decode_any W_1b4dc = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4e0 : bv 32 := 0x00000593.
Lemma F_1b4e0 : fetch_word Plain.M.loaded_segments (0x1b538 : word) = Some W_1b4e0.
Proof. vm_refl. Qed.
Lemma D_1b4e0 : decode_any W_1b4e0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4e4 : bv 32 := 0x00000613.
Lemma F_1b4e4 : fetch_word Plain.M.loaded_segments (0x1b53c : word) = Some W_1b4e4.
Proof. vm_refl. Qed.
Lemma D_1b4e4 : decode_any W_1b4e4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4e8 : bv 32 := 0x00090693.
Lemma F_1b4e8 : fetch_word Plain.M.loaded_segments (0x1b540 : word) = Some W_1b4e8.
Proof. vm_refl. Qed.
Lemma D_1b4e8 : decode_any W_1b4e8 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4ec : bv 32 := 0x000c8713.
Lemma F_1b4ec : fetch_word Plain.M.loaded_segments (0x1b544 : word) = Some W_1b4ec.
Proof. vm_refl. Qed.
Lemma D_1b4ec : decode_any W_1b4ec = Some (OpImm ALU_ADD 14 25 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4f0 : bv 32 := 0x000d0793.
Lemma F_1b4f0 : fetch_word Plain.M.loaded_segments (0x1b548 : word) = Some W_1b4f0.
Proof. vm_refl. Qed.
Lemma D_1b4f0 : decode_any W_1b4f0 = Some (OpImm ALU_ADD 15 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4f4 : bv 32 := 0x00000813.
Lemma F_1b4f4 : fetch_word Plain.M.loaded_segments (0x1b54c : word) = Some W_1b4f4.
Proof. vm_refl. Qed.
Lemma D_1b4f4 : decode_any W_1b4f4 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4f8 : bv 32 := 0x00000893.
Lemma F_1b4f8 : fetch_word Plain.M.loaded_segments (0x1b550 : word) = Some W_1b4f8.
Proof. vm_refl. Qed.
Lemma D_1b4f8 : decode_any W_1b4f8 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4fc : bv 32 := 0x6f1070ef.
Lemma F_1b4fc : fetch_word Plain.M.loaded_segments (0x1b554 : word) = Some W_1b4fc.
Proof. vm_refl. Qed.
Lemma D_1b4fc : decode_any W_1b4fc = Some (Jal 1 32496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b500 : bv 32 := 0x00013023.
Lemma F_1b500 : fetch_word Plain.M.loaded_segments (0x1b558 : word) = Some W_1b500.
Proof. vm_refl. Qed.
Lemma D_1b500 : decode_any W_1b500 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b504 : bv 32 := 0x00098513.
Lemma F_1b504 : fetch_word Plain.M.loaded_segments (0x1b55c : word) = Some W_1b504.
Proof. vm_refl. Qed.
Lemma D_1b504 : decode_any W_1b504 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b508 : bv 32 := 0x000c0593.
Lemma F_1b508 : fetch_word Plain.M.loaded_segments (0x1b560 : word) = Some W_1b508.
Proof. vm_refl. Qed.
Lemma D_1b508 : decode_any W_1b508 = Some (OpImm ALU_ADD 11 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b50c : bv 32 := 0x00000613.
Lemma F_1b50c : fetch_word Plain.M.loaded_segments (0x1b564 : word) = Some W_1b50c.
Proof. vm_refl. Qed.
Lemma D_1b50c : decode_any W_1b50c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b510 : bv 32 := 0x000a8693.
Lemma F_1b510 : fetch_word Plain.M.loaded_segments (0x1b568 : word) = Some W_1b510.
Proof. vm_refl. Qed.
Lemma D_1b510 : decode_any W_1b510 = Some (OpImm ALU_ADD 13 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b514 : bv 32 := 0x000c8713.
Lemma F_1b514 : fetch_word Plain.M.loaded_segments (0x1b56c : word) = Some W_1b514.
Proof. vm_refl. Qed.
Lemma D_1b514 : decode_any W_1b514 = Some (OpImm ALU_ADD 14 25 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b518 : bv 32 := 0x000d0793.
Lemma F_1b518 : fetch_word Plain.M.loaded_segments (0x1b570 : word) = Some W_1b518.
Proof. vm_refl. Qed.
Lemma D_1b518 : decode_any W_1b518 = Some (OpImm ALU_ADD 15 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b51c : bv 32 := 0x00000813.
Lemma F_1b51c : fetch_word Plain.M.loaded_segments (0x1b574 : word) = Some W_1b51c.
Proof. vm_refl. Qed.
Lemma D_1b51c : decode_any W_1b51c = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b520 : bv 32 := 0x00000893.
Lemma F_1b520 : fetch_word Plain.M.loaded_segments (0x1b578 : word) = Some W_1b520.
Proof. vm_refl. Qed.
Lemma D_1b520 : decode_any W_1b520 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b524 : bv 32 := 0x6c9070ef.
Lemma F_1b524 : fetch_word Plain.M.loaded_segments (0x1b57c : word) = Some W_1b524.
Proof. vm_refl. Qed.
Lemma D_1b524 : decode_any W_1b524 = Some (Jal 1 32456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b528 : bv 32 := 0x00013023.
Lemma F_1b528 : fetch_word Plain.M.loaded_segments (0x1b580 : word) = Some W_1b528.
Proof. vm_refl. Qed.
Lemma D_1b528 : decode_any W_1b528 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b52c : bv 32 := 0x00098513.
Lemma F_1b52c : fetch_word Plain.M.loaded_segments (0x1b584 : word) = Some W_1b52c.
Proof. vm_refl. Qed.
Lemma D_1b52c : decode_any W_1b52c = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b530 : bv 32 := 0x00000593.
Lemma F_1b530 : fetch_word Plain.M.loaded_segments (0x1b588 : word) = Some W_1b530.
Proof. vm_refl. Qed.
Lemma D_1b530 : decode_any W_1b530 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b534 : bv 32 := 0x00000613.
Lemma F_1b534 : fetch_word Plain.M.loaded_segments (0x1b58c : word) = Some W_1b534.
Proof. vm_refl. Qed.
Lemma D_1b534 : decode_any W_1b534 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b538 : bv 32 := 0x000b0693.
Lemma F_1b538 : fetch_word Plain.M.loaded_segments (0x1b590 : word) = Some W_1b538.
Proof. vm_refl. Qed.
Lemma D_1b538 : decode_any W_1b538 = Some (OpImm ALU_ADD 13 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b53c : bv 32 := 0x00048713.
Lemma F_1b53c : fetch_word Plain.M.loaded_segments (0x1b594 : word) = Some W_1b53c.
Proof. vm_refl. Qed.
Lemma D_1b53c : decode_any W_1b53c = Some (OpImm ALU_ADD 14 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b540 : bv 32 := 0x000d0793.
Lemma F_1b540 : fetch_word Plain.M.loaded_segments (0x1b598 : word) = Some W_1b540.
Proof. vm_refl. Qed.
Lemma D_1b540 : decode_any W_1b540 = Some (OpImm ALU_ADD 15 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b544 : bv 32 := 0x00000813.
Lemma F_1b544 : fetch_word Plain.M.loaded_segments (0x1b59c : word) = Some W_1b544.
Proof. vm_refl. Qed.
Lemma D_1b544 : decode_any W_1b544 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b548 : bv 32 := 0x00000893.
Lemma F_1b548 : fetch_word Plain.M.loaded_segments (0x1b5a0 : word) = Some W_1b548.
Proof. vm_refl. Qed.
Lemma D_1b548 : decode_any W_1b548 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b54c : bv 32 := 0x6a1070ef.
Lemma F_1b54c : fetch_word Plain.M.loaded_segments (0x1b5a4 : word) = Some W_1b54c.
Proof. vm_refl. Qed.
Lemma D_1b54c : decode_any W_1b54c = Some (Jal 1 32416, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b550 : bv 32 := 0x00013023.
Lemma F_1b550 : fetch_word Plain.M.loaded_segments (0x1b5a8 : word) = Some W_1b550.
Proof. vm_refl. Qed.
Lemma D_1b550 : decode_any W_1b550 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b554 : bv 32 := 0x00098513.
Lemma F_1b554 : fetch_word Plain.M.loaded_segments (0x1b5ac : word) = Some W_1b554.
Proof. vm_refl. Qed.
Lemma D_1b554 : decode_any W_1b554 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b558 : bv 32 := 0x00000593.
Lemma F_1b558 : fetch_word Plain.M.loaded_segments (0x1b5b0 : word) = Some W_1b558.
Proof. vm_refl. Qed.
Lemma D_1b558 : decode_any W_1b558 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b55c : bv 32 := 0x000b8613.
Lemma F_1b55c : fetch_word Plain.M.loaded_segments (0x1b5b4 : word) = Some W_1b55c.
Proof. vm_refl. Qed.
Lemma D_1b55c : decode_any W_1b55c = Some (OpImm ALU_ADD 12 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b560 : bv 32 := 0x000b0693.
Lemma F_1b560 : fetch_word Plain.M.loaded_segments (0x1b5b8 : word) = Some W_1b560.
Proof. vm_refl. Qed.
Lemma D_1b560 : decode_any W_1b560 = Some (OpImm ALU_ADD 13 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b564 : bv 32 := 0x000a0713.
Lemma F_1b564 : fetch_word Plain.M.loaded_segments (0x1b5bc : word) = Some W_1b564.
Proof. vm_refl. Qed.
Lemma D_1b564 : decode_any W_1b564 = Some (OpImm ALU_ADD 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b568 : bv 32 := 0x000d0793.
Lemma F_1b568 : fetch_word Plain.M.loaded_segments (0x1b5c0 : word) = Some W_1b568.
Proof. vm_refl. Qed.
Lemma D_1b568 : decode_any W_1b568 = Some (OpImm ALU_ADD 15 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b56c : bv 32 := 0x00000813.
Lemma F_1b56c : fetch_word Plain.M.loaded_segments (0x1b5c4 : word) = Some W_1b56c.
Proof. vm_refl. Qed.
Lemma D_1b56c : decode_any W_1b56c = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b570 : bv 32 := 0x00000893.
Lemma F_1b570 : fetch_word Plain.M.loaded_segments (0x1b5c8 : word) = Some W_1b570.
Proof. vm_refl. Qed.
Lemma D_1b570 : decode_any W_1b570 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b574 : bv 32 := 0x679070ef.
Lemma F_1b574 : fetch_word Plain.M.loaded_segments (0x1b5cc : word) = Some W_1b574.
Proof. vm_refl. Qed.
Lemma D_1b574 : decode_any W_1b574 = Some (Jal 1 32376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b578 : bv 32 := 0x0e00006f.
Lemma F_1b578 : fetch_word Plain.M.loaded_segments (0x1b5d0 : word) = Some W_1b578.
Proof. vm_refl. Qed.
Lemma D_1b578 : decode_any W_1b578 = Some (Jal 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b604 : bv 32 := 0x0001d517.
Lemma F_1b604 : fetch_word Plain.M.loaded_segments (0x1b65c : word) = Some W_1b604.
Proof. vm_refl. Qed.
Lemma D_1b604 : decode_any W_1b604 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b608 : bv 32 := 0xe1453503.
Lemma F_1b608 : fetch_word Plain.M.loaded_segments (0x1b660 : word) = Some W_1b608.
Proof. vm_refl. Qed.
Lemma D_1b608 : decode_any W_1b608 = Some (Load SZ8 true 10 10 3604, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b60c : bv 32 := 0x00052503.
Lemma F_1b60c : fetch_word Plain.M.loaded_segments (0x1b664 : word) = Some W_1b60c.
Proof. vm_refl. Qed.
Lemma D_1b60c : decode_any W_1b60c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b610 : bv 32 := 0x00500593.
Lemma F_1b610 : fetch_word Plain.M.loaded_segments (0x1b668 : word) = Some W_1b610.
Proof. vm_refl. Qed.
Lemma D_1b610 : decode_any W_1b610 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b614 : bv 32 := 0x02a5c263.
Lemma F_1b614 : fetch_word Plain.M.loaded_segments (0x1b66c : word) = Some W_1b614.
Proof. vm_refl. Qed.
Lemma D_1b614 : decode_any W_1b614 = Some (Branch BC_LT 11 10 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b618 : bv 32 := 0xffff5517.
Lemma F_1b618 : fetch_word Plain.M.loaded_segments (0x1b670 : word) = Some W_1b618.
Proof. vm_refl. Qed.
Lemma D_1b618 : decode_any W_1b618 = Some (Auipc 10 1048565, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b61c : bv 32 := 0xffff6597.
Lemma F_1b61c : fetch_word Plain.M.loaded_segments (0x1b674 : word) = Some W_1b61c.
Proof. vm_refl. Qed.
Lemma D_1b61c : decode_any W_1b61c = Some (Auipc 11 1048566, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b620 : bv 32 := 0x0e850513.
Lemma F_1b620 : fetch_word Plain.M.loaded_segments (0x1b678 : word) = Some W_1b620.
Proof. vm_refl. Qed.
Lemma D_1b620 : decode_any W_1b620 = Some (OpImm ALU_ADD 10 10 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b624 : bv 32 := 0xce658593.
Lemma F_1b624 : fetch_word Plain.M.loaded_segments (0x1b67c : word) = Some W_1b624.
Proof. vm_refl. Qed.
Lemma D_1b624 : decode_any W_1b624 = Some (OpImm ALU_ADD 11 11 3302, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b628 : bv 32 := 0x00000613.
Lemma F_1b628 : fetch_word Plain.M.loaded_segments (0x1b680 : word) = Some W_1b628.
Proof. vm_refl. Qed.
Lemma D_1b628 : decode_any W_1b628 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b62c : bv 32 := 0xdf0fc0ef.
Lemma F_1b62c : fetch_word Plain.M.loaded_segments (0x1b684 : word) = Some W_1b62c.
Proof. vm_refl. Qed.
Lemma D_1b62c : decode_any W_1b62c = Some (Jal 1 2082288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b630 : bv 32 := 0x00050993.
Lemma F_1b630 : fetch_word Plain.M.loaded_segments (0x1b688 : word) = Some W_1b630.
Proof. vm_refl. Qed.
Lemma D_1b630 : decode_any W_1b630 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b634 : bv 32 := 0x04c0006f.
Lemma F_1b634 : fetch_word Plain.M.loaded_segments (0x1b68c : word) = Some W_1b634.
Proof. vm_refl. Qed.
Lemma D_1b634 : decode_any W_1b634 = Some (Jal 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b640 : bv 32 := 0xfff00613.
Lemma F_1b640 : fetch_word Plain.M.loaded_segments (0x1b698 : word) = Some W_1b640.
Proof. vm_refl. Qed.
Lemma D_1b640 : decode_any W_1b640 = Some (OpImm ALU_ADD 12 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b644 : bv 32 := 0x00a6153b.
Lemma F_1b644 : fetch_word Plain.M.loaded_segments (0x1b69c : word) = Some W_1b644.
Proof. vm_refl. Qed.
Lemma D_1b644 : decode_any W_1b644 = Some (Op32 ALU_SLL 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b648 : bv 32 := 0xfff54513.
Lemma F_1b648 : fetch_word Plain.M.loaded_segments (0x1b6a0 : word) = Some W_1b648.
Proof. vm_refl. Qed.
Lemma D_1b648 : decode_any W_1b648 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b64c : bv 32 := 0xe8a5f4e3.
Lemma F_1b64c : fetch_word Plain.M.loaded_segments (0x1b6a4 : word) = Some W_1b64c.
Proof. vm_refl. Qed.
Lemma D_1b64c : decode_any W_1b64c = Some (Branch BC_GEU 11 10 7816, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b658 : bv 32 := 0x01c12683.
Lemma F_1b658 : fetch_word Plain.M.loaded_segments (0x1b6b0 : word) = Some W_1b658.
Proof. vm_refl. Qed.
Lemma D_1b658 : decode_any W_1b658 = Some (Load SZ4 true 13 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b65c : bv 32 := 0x01812703.
Lemma F_1b65c : fetch_word Plain.M.loaded_segments (0x1b6b4 : word) = Some W_1b65c.
Proof. vm_refl. Qed.
Lemma D_1b65c : decode_any W_1b65c = Some (Load SZ4 true 14 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b660 : bv 32 := 0x00c00793.
Lemma F_1b660 : fetch_word Plain.M.loaded_segments (0x1b6b8 : word) = Some W_1b660.
Proof. vm_refl. Qed.
Lemma D_1b660 : decode_any W_1b660 = Some (OpImm ALU_ADD 15 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b664 : bv 32 := 0x00013023.
Lemma F_1b664 : fetch_word Plain.M.loaded_segments (0x1b6bc : word) = Some W_1b664.
Proof. vm_refl. Qed.
Lemma D_1b664 : decode_any W_1b664 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b668 : bv 32 := 0x00098513.
Lemma F_1b668 : fetch_word Plain.M.loaded_segments (0x1b6c0 : word) = Some W_1b668.
Proof. vm_refl. Qed.
Lemma D_1b668 : decode_any W_1b668 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b66c : bv 32 := 0x00090593.
Lemma F_1b66c : fetch_word Plain.M.loaded_segments (0x1b6c4 : word) = Some W_1b66c.
Proof. vm_refl. Qed.
Lemma D_1b66c : decode_any W_1b66c = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b670 : bv 32 := 0x00048613.
Lemma F_1b670 : fetch_word Plain.M.loaded_segments (0x1b6c8 : word) = Some W_1b670.
Proof. vm_refl. Qed.
Lemma D_1b670 : decode_any W_1b670 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b674 : bv 32 := 0x00040813.
Lemma F_1b674 : fetch_word Plain.M.loaded_segments (0x1b6cc : word) = Some W_1b674.
Proof. vm_refl. Qed.
Lemma D_1b674 : decode_any W_1b674 = Some (OpImm ALU_ADD 16 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b678 : bv 32 := 0x00000893.
Lemma F_1b678 : fetch_word Plain.M.loaded_segments (0x1b6d0 : word) = Some W_1b678.
Proof. vm_refl. Qed.
Lemma D_1b678 : decode_any W_1b678 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b67c : bv 32 := 0x571070ef.
Lemma F_1b67c : fetch_word Plain.M.loaded_segments (0x1b6d4 : word) = Some W_1b67c.
Proof. vm_refl. Qed.
Lemma D_1b67c : decode_any W_1b67c = Some (Jal 1 32112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b680 : bv 32 := 0x00098513.
Lemma F_1b680 : fetch_word Plain.M.loaded_segments (0x1b6d8 : word) = Some W_1b680.
Proof. vm_refl. Qed.
Lemma D_1b680 : decode_any W_1b680 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b684 : bv 32 := 0x07813083.
Lemma F_1b684 : fetch_word Plain.M.loaded_segments (0x1b6dc : word) = Some W_1b684.
Proof. vm_refl. Qed.
Lemma D_1b684 : decode_any W_1b684 = Some (Load SZ8 true 1 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b688 : bv 32 := 0x07013403.
Lemma F_1b688 : fetch_word Plain.M.loaded_segments (0x1b6e0 : word) = Some W_1b688.
Proof. vm_refl. Qed.
Lemma D_1b688 : decode_any W_1b688 = Some (Load SZ8 true 8 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b68c : bv 32 := 0x06813483.
Lemma F_1b68c : fetch_word Plain.M.loaded_segments (0x1b6e4 : word) = Some W_1b68c.
Proof. vm_refl. Qed.
Lemma D_1b68c : decode_any W_1b68c = Some (Load SZ8 true 9 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b690 : bv 32 := 0x06013903.
Lemma F_1b690 : fetch_word Plain.M.loaded_segments (0x1b6e8 : word) = Some W_1b690.
Proof. vm_refl. Qed.
Lemma D_1b690 : decode_any W_1b690 = Some (Load SZ8 true 18 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b694 : bv 32 := 0x05813983.
Lemma F_1b694 : fetch_word Plain.M.loaded_segments (0x1b6ec : word) = Some W_1b694.
Proof. vm_refl. Qed.
Lemma D_1b694 : decode_any W_1b694 = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b698 : bv 32 := 0x05013a03.
Lemma F_1b698 : fetch_word Plain.M.loaded_segments (0x1b6f0 : word) = Some W_1b698.
Proof. vm_refl. Qed.
Lemma D_1b698 : decode_any W_1b698 = Some (Load SZ8 true 20 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b69c : bv 32 := 0x04813a83.
Lemma F_1b69c : fetch_word Plain.M.loaded_segments (0x1b6f4 : word) = Some W_1b69c.
Proof. vm_refl. Qed.
Lemma D_1b69c : decode_any W_1b69c = Some (Load SZ8 true 21 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6a0 : bv 32 := 0x04013b03.
Lemma F_1b6a0 : fetch_word Plain.M.loaded_segments (0x1b6f8 : word) = Some W_1b6a0.
Proof. vm_refl. Qed.
Lemma D_1b6a0 : decode_any W_1b6a0 = Some (Load SZ8 true 22 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6a4 : bv 32 := 0x03813b83.
Lemma F_1b6a4 : fetch_word Plain.M.loaded_segments (0x1b6fc : word) = Some W_1b6a4.
Proof. vm_refl. Qed.
Lemma D_1b6a4 : decode_any W_1b6a4 = Some (Load SZ8 true 23 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6a8 : bv 32 := 0x03013c03.
Lemma F_1b6a8 : fetch_word Plain.M.loaded_segments (0x1b700 : word) = Some W_1b6a8.
Proof. vm_refl. Qed.
Lemma D_1b6a8 : decode_any W_1b6a8 = Some (Load SZ8 true 24 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6ac : bv 32 := 0x02813c83.
Lemma F_1b6ac : fetch_word Plain.M.loaded_segments (0x1b704 : word) = Some W_1b6ac.
Proof. vm_refl. Qed.
Lemma D_1b6ac : decode_any W_1b6ac = Some (Load SZ8 true 25 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6b0 : bv 32 := 0x02013d03.
Lemma F_1b6b0 : fetch_word Plain.M.loaded_segments (0x1b708 : word) = Some W_1b6b0.
Proof. vm_refl. Qed.
Lemma D_1b6b0 : decode_any W_1b6b0 = Some (Load SZ8 true 26 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6b4 : bv 32 := 0x08010113.
Lemma F_1b6b4 : fetch_word Plain.M.loaded_segments (0x1b70c : word) = Some W_1b6b4.
Proof. vm_refl. Qed.
Lemma D_1b6b4 : decode_any W_1b6b4 = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6b8 : bv 32 := 0x00008067.
Lemma F_1b6b8 : fetch_word Plain.M.loaded_segments (0x1b710 : word) = Some W_1b6b8.
Proof. vm_refl. Qed.
Lemma D_1b6b8 : decode_any W_1b6b8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

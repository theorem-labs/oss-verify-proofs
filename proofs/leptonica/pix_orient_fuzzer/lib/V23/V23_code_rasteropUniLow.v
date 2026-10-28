(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_7f3d8 : bv 32 := 0xfe010113.
Lemma F_7f3d8 : fetch_word Ubsan.M.loaded_segments (0x7f3d8 : word) = Some W_7f3d8.
Proof. vm_refl. Qed.
Lemma D_7f3d8 : decode_any W_7f3d8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f3dc : bv 32 := 0x00813c23.
Lemma F_7f3dc : fetch_word Ubsan.M.loaded_segments (0x7f3dc : word) = Some W_7f3dc.
Proof. vm_refl. Qed.
Lemma D_7f3dc : decode_any W_7f3dc = Some (Store SZ8 2 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f3e0 : bv 32 := 0x00913823.
Lemma F_7f3e0 : fetch_word Ubsan.M.loaded_segments (0x7f3e0 : word) = Some W_7f3e0.
Proof. vm_refl. Qed.
Lemma D_7f3e0 : decode_any W_7f3e0 = Some (Store SZ8 2 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f3e4 : bv 32 := 0x01213423.
Lemma F_7f3e4 : fetch_word Ubsan.M.loaded_segments (0x7f3e4 : word) = Some W_7f3e4.
Proof. vm_refl. Qed.
Lemma D_7f3e4 : decode_any W_7f3e4 = Some (Store SZ8 2 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f3e8 : bv 32 := 0x01313023.
Lemma F_7f3e8 : fetch_word Ubsan.M.loaded_segments (0x7f3e8 : word) = Some W_7f3e8.
Proof. vm_refl. Qed.
Lemma D_7f3e8 : decode_any W_7f3e8 = Some (Store SZ8 2 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f3ec : bv 32 := 0x00058293.
Lemma F_7f3ec : fetch_word Ubsan.M.loaded_segments (0x7f3ec : word) = Some W_7f3ec.
Proof. vm_refl. Qed.
Lemma D_7f3ec : decode_any W_7f3ec = Some (OpImm ALU_ADD 5 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f3f0 : bv 32 := 0x02813583.
Lemma F_7f3f0 : fetch_word Ubsan.M.loaded_segments (0x7f3f0 : word) = Some W_7f3f0.
Proof. vm_refl. Qed.
Lemma D_7f3f0 : decode_any W_7f3f0 = Some (Load SZ8 true 11 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f3f4 : bv 32 := 0x02013303.
Lemma F_7f3f4 : fetch_word Ubsan.M.loaded_segments (0x7f3f4 : word) = Some W_7f3f4.
Proof. vm_refl. Qed.
Lemma D_7f3f4 : decode_any W_7f3f4 = Some (Load SZ8 true 6 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f3f8 : bv 32 := 0x00100393.
Lemma F_7f3f8 : fetch_word Ubsan.M.loaded_segments (0x7f3f8 : word) = Some W_7f3f8.
Proof. vm_refl. Qed.
Lemma D_7f3f8 : decode_any W_7f3f8 = Some (OpImm ALU_ADD 7 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f3fc : bv 32 := 0x00769c63.
Lemma F_7f3fc : fetch_word Ubsan.M.loaded_segments (0x7f3fc : word) = Some W_7f3fc.
Proof. vm_refl. Qed.
Lemma D_7f3fc : decode_any W_7f3fc = Some (Branch BC_NE 13 7 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f400 : bv 32 := 0x00078393.
Lemma F_7f400 : fetch_word Ubsan.M.loaded_segments (0x7f400 : word) = Some W_7f400.
Proof. vm_refl. Qed.
Lemma D_7f400 : decode_any W_7f400 = Some (OpImm ALU_ADD 7 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f404 : bv 32 := 0x00028e13.
Lemma F_7f404 : fetch_word Ubsan.M.loaded_segments (0x7f404 : word) = Some W_7f404.
Proof. vm_refl. Qed.
Lemma D_7f404 : decode_any W_7f404 = Some (OpImm ALU_ADD 28 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f408 : bv 32 := 0x0007869b.
Lemma F_7f408 : fetch_word Ubsan.M.loaded_segments (0x7f408 : word) = Some W_7f408.
Proof. vm_refl. Qed.
Lemma D_7f408 : decode_any W_7f408 = Some (OpImm32 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f40c : bv 32 := 0x0406d663.
Lemma F_7f40c : fetch_word Ubsan.M.loaded_segments (0x7f40c : word) = Some W_7f40c.
Proof. vm_refl. Qed.
Lemma D_7f40c : decode_any W_7f40c = Some (Branch BC_GE 13 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f410 : bv 32 := 0x0340006f.
Lemma F_7f410 : fetch_word Ubsan.M.loaded_segments (0x7f410 : word) = Some W_7f410.
Proof. vm_refl. Qed.
Lemma D_7f410 : decode_any W_7f410 = Some (Jal 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f414 : bv 32 := 0x02d28e33.
Lemma F_7f414 : fetch_word Ubsan.M.loaded_segments (0x7f414 : word) = Some W_7f414.
Proof. vm_refl. Qed.
Lemma D_7f414 : decode_any W_7f414 = Some (Mul M_MUL 28 5 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f418 : bv 32 := 0x02d282bb.
Lemma F_7f418 : fetch_word Ubsan.M.loaded_segments (0x7f418 : word) = Some W_7f418.
Proof. vm_refl. Qed.
Lemma D_7f418 : decode_any W_7f418 = Some (Mul32 M_MUL 5 5 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f41c : bv 32 := 0x07c29ee3.
Lemma F_7f41c : fetch_word Ubsan.M.loaded_segments (0x7f41c : word) = Some W_7f41c.
Proof. vm_refl. Qed.
Lemma D_7f41c : decode_any W_7f41c = Some (Branch BC_NE 5 28 2172, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f420 : bv 32 := 0x02d783b3.
Lemma F_7f420 : fetch_word Ubsan.M.loaded_segments (0x7f420 : word) = Some W_7f420.
Proof. vm_refl. Qed.
Lemma D_7f420 : decode_any W_7f420 = Some (Mul M_MUL 7 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f424 : bv 32 := 0x02d787bb.
Lemma F_7f424 : fetch_word Ubsan.M.loaded_segments (0x7f424 : word) = Some W_7f424.
Proof. vm_refl. Qed.
Lemma D_7f424 : decode_any W_7f424 = Some (Mul32 M_MUL 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f428 : bv 32 := 0x067798e3.
Lemma F_7f428 : fetch_word Ubsan.M.loaded_segments (0x7f428 : word) = Some W_7f428.
Proof. vm_refl. Qed.
Lemma D_7f428 : decode_any W_7f428 = Some (Branch BC_NE 15 7 2160, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f42c : bv 32 := 0x02d887b3.
Lemma F_7f42c : fetch_word Ubsan.M.loaded_segments (0x7f42c : word) = Some W_7f42c.
Proof. vm_refl. Qed.
Lemma D_7f42c : decode_any W_7f42c = Some (Mul M_MUL 15 17 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f430 : bv 32 := 0x02d886bb.
Lemma F_7f430 : fetch_word Ubsan.M.loaded_segments (0x7f430 : word) = Some W_7f430.
Proof. vm_refl. Qed.
Lemma D_7f430 : decode_any W_7f430 = Some (Mul32 M_MUL 13 17 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f434 : bv 32 := 0x06f692e3.
Lemma F_7f434 : fetch_word Ubsan.M.loaded_segments (0x7f434 : word) = Some W_7f434.
Proof. vm_refl. Qed.
Lemma D_7f434 : decode_any W_7f434 = Some (Branch BC_NE 13 15 2148, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f438 : bv 32 := 0x00078893.
Lemma F_7f438 : fetch_word Ubsan.M.loaded_segments (0x7f438 : word) = Some W_7f438.
Proof. vm_refl. Qed.
Lemma D_7f438 : decode_any W_7f438 = Some (OpImm ALU_ADD 17 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f43c : bv 32 := 0x0003869b.
Lemma F_7f43c : fetch_word Ubsan.M.loaded_segments (0x7f43c : word) = Some W_7f43c.
Proof. vm_refl. Qed.
Lemma D_7f43c : decode_any W_7f43c = Some (OpImm32 13 7 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f440 : bv 32 := 0x0006dc63.
Lemma F_7f440 : fetch_word Ubsan.M.loaded_segments (0x7f440 : word) = Some W_7f440.
Proof. vm_refl. Qed.
Lemma D_7f440 : decode_any W_7f440 = Some (Branch BC_GE 13 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f444 : bv 32 := 0x0008879b.
Lemma F_7f444 : fetch_word Ubsan.M.loaded_segments (0x7f444 : word) = Some W_7f444.
Proof. vm_refl. Qed.
Lemma D_7f444 : decode_any W_7f444 = Some (OpImm32 15 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f448 : bv 32 := 0x00d788b3.
Lemma F_7f448 : fetch_word Ubsan.M.loaded_segments (0x7f448 : word) = Some W_7f448.
Proof. vm_refl. Qed.
Lemma D_7f448 : decode_any W_7f448 = Some (Op ALU_ADD 17 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f44c : bv 32 := 0x00d786bb.
Lemma F_7f44c : fetch_word Ubsan.M.loaded_segments (0x7f44c : word) = Some W_7f44c.
Proof. vm_refl. Qed.
Lemma D_7f44c : decode_any W_7f44c = Some (Op32 ALU_ADD 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f450 : bv 32 := 0x051694e3.
Lemma F_7f450 : fetch_word Ubsan.M.loaded_segments (0x7f450 : word) = Some W_7f450.
Proof. vm_refl. Qed.
Lemma D_7f450 : decode_any W_7f450 = Some (Branch BC_NE 13 17 2120, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f454 : bv 32 := 0x00000393.
Lemma F_7f454 : fetch_word Ubsan.M.loaded_segments (0x7f454 : word) = Some W_7f454.
Proof. vm_refl. Qed.
Lemma D_7f454 : decode_any W_7f454 = Some (OpImm ALU_ADD 7 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f458 : bv 32 := 0x0008869b.
Lemma F_7f458 : fetch_word Ubsan.M.loaded_segments (0x7f458 : word) = Some W_7f458.
Proof. vm_refl. Qed.
Lemma D_7f458 : decode_any W_7f458 = Some (OpImm32 13 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f45c : bv 32 := 0x00038e9b.
Lemma F_7f45c : fetch_word Ubsan.M.loaded_segments (0x7f45c : word) = Some W_7f45c.
Proof. vm_refl. Qed.
Lemma D_7f45c : decode_any W_7f45c = Some (OpImm32 29 7 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f460 : bv 32 := 0x00de87b3.
Lemma F_7f460 : fetch_word Ubsan.M.loaded_segments (0x7f460 : word) = Some W_7f460.
Proof. vm_refl. Qed.
Lemma D_7f460 : decode_any W_7f460 = Some (Op ALU_ADD 15 29 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f464 : bv 32 := 0x00de82bb.
Lemma F_7f464 : fetch_word Ubsan.M.loaded_segments (0x7f464 : word) = Some W_7f464.
Proof. vm_refl. Qed.
Lemma D_7f464 : decode_any W_7f464 = Some (Op32 ALU_ADD 5 29 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f468 : bv 32 := 0x02f298e3.
Lemma F_7f468 : fetch_word Ubsan.M.loaded_segments (0x7f468 : word) = Some W_7f468.
Proof. vm_refl. Qed.
Lemma D_7f468 : decode_any W_7f468 = Some (Branch BC_NE 5 15 2096, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f46c : bv 32 := 0x0007829b.
Lemma F_7f46c : fetch_word Ubsan.M.loaded_segments (0x7f46c : word) = Some W_7f46c.
Proof. vm_refl. Qed.
Lemma D_7f46c : decode_any W_7f46c = Some (OpImm32 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f470 : bv 32 := 0x000e0e1b.
Lemma F_7f470 : fetch_word Ubsan.M.loaded_segments (0x7f470 : word) = Some W_7f470.
Proof. vm_refl. Qed.
Lemma D_7f470 : decode_any W_7f470 = Some (OpImm32 28 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f474 : bv 32 := 0x41c287bb.
Lemma F_7f474 : fetch_word Ubsan.M.loaded_segments (0x7f474 : word) = Some W_7f474.
Proof. vm_refl. Qed.
Lemma D_7f474 : decode_any W_7f474 = Some (Op32 ALU_SUB 15 5 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f478 : bv 32 := 0x41c282b3.
Lemma F_7f478 : fetch_word Ubsan.M.loaded_segments (0x7f478 : word) = Some W_7f478.
Proof. vm_refl. Qed.
Lemma D_7f478 : decode_any W_7f478 = Some (Op ALU_SUB 5 5 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f47c : bv 32 := 0x00579ee3.
Lemma F_7f47c : fetch_word Ubsan.M.loaded_segments (0x7f47c : word) = Some W_7f47c.
Proof. vm_refl. Qed.
Lemma D_7f47c : decode_any W_7f47c = Some (Branch BC_NE 15 5 2076, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f480 : bv 32 := 0x00f05863.
Lemma F_7f480 : fetch_word Ubsan.M.loaded_segments (0x7f480 : word) = Some W_7f480.
Proof. vm_refl. Qed.
Lemma D_7f480 : decode_any W_7f480 = Some (Branch BC_GE 0 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f484 : bv 32 := 0x40f688b3.
Lemma F_7f484 : fetch_word Ubsan.M.loaded_segments (0x7f484 : word) = Some W_7f484.
Proof. vm_refl. Qed.
Lemma D_7f484 : decode_any W_7f484 = Some (Op ALU_SUB 17 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f488 : bv 32 := 0x40f686bb.
Lemma F_7f488 : fetch_word Ubsan.M.loaded_segments (0x7f488 : word) = Some W_7f488.
Proof. vm_refl. Qed.
Lemma D_7f488 : decode_any W_7f488 = Some (Op32 ALU_SUB 13 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f48c : bv 32 := 0x011696e3.
Lemma F_7f48c : fetch_word Ubsan.M.loaded_segments (0x7f48c : word) = Some W_7f48c.
Proof. vm_refl. Qed.
Lemma D_7f48c : decode_any W_7f48c = Some (Branch BC_NE 13 17 2060, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f490 : bv 32 := 0x00085c63.
Lemma F_7f490 : fetch_word Ubsan.M.loaded_segments (0x7f490 : word) = Some W_7f490.
Proof. vm_refl. Qed.
Lemma D_7f490 : decode_any W_7f490 = Some (Branch BC_GE 16 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f494 : bv 32 := 0x010306b3.
Lemma F_7f494 : fetch_word Ubsan.M.loaded_segments (0x7f494 : word) = Some W_7f494.
Proof. vm_refl. Qed.
Lemma D_7f494 : decode_any W_7f494 = Some (Op ALU_ADD 13 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f498 : bv 32 := 0x010307bb.
Lemma F_7f498 : fetch_word Ubsan.M.loaded_segments (0x7f498 : word) = Some W_7f498.
Proof. vm_refl. Qed.
Lemma D_7f498 : decode_any W_7f498 = Some (Op32 ALU_ADD 15 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f49c : bv 32 := 0x7ed79e63.
Lemma F_7f49c : fetch_word Ubsan.M.loaded_segments (0x7f49c : word) = Some W_7f49c.
Proof. vm_refl. Qed.
Lemma D_7f49c : decode_any W_7f49c = Some (Branch BC_NE 15 13 2044, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4a0 : bv 32 := 0x00000813.
Lemma F_7f4a0 : fetch_word Ubsan.M.loaded_segments (0x7f4a0 : word) = Some W_7f4a0.
Proof. vm_refl. Qed.
Lemma D_7f4a0 : decode_any W_7f4a0 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4a4 : bv 32 := 0x00068313.
Lemma F_7f4a4 : fetch_word Ubsan.M.loaded_segments (0x7f4a4 : word) = Some W_7f4a4.
Proof. vm_refl. Qed.
Lemma D_7f4a4 : decode_any W_7f4a4 = Some (OpImm ALU_ADD 6 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4a8 : bv 32 := 0x0003069b.
Lemma F_7f4a8 : fetch_word Ubsan.M.loaded_segments (0x7f4a8 : word) = Some W_7f4a8.
Proof. vm_refl. Qed.
Lemma D_7f4a8 : decode_any W_7f4a8 = Some (OpImm32 13 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4ac : bv 32 := 0x00d807b3.
Lemma F_7f4ac : fetch_word Ubsan.M.loaded_segments (0x7f4ac : word) = Some W_7f4ac.
Proof. vm_refl. Qed.
Lemma D_7f4ac : decode_any W_7f4ac = Some (Op ALU_ADD 15 16 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4b0 : bv 32 := 0x00d802bb.
Lemma F_7f4b0 : fetch_word Ubsan.M.loaded_segments (0x7f4b0 : word) = Some W_7f4b0.
Proof. vm_refl. Qed.
Lemma D_7f4b0 : decode_any W_7f4b0 = Some (Op32 ALU_ADD 5 16 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4b4 : bv 32 := 0x7ef29263.
Lemma F_7f4b4 : fetch_word Ubsan.M.loaded_segments (0x7f4b4 : word) = Some W_7f4b4.
Proof. vm_refl. Qed.
Lemma D_7f4b4 : decode_any W_7f4b4 = Some (Branch BC_NE 5 15 2020, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4b8 : bv 32 := 0x0007829b.
Lemma F_7f4b8 : fetch_word Ubsan.M.loaded_segments (0x7f4b8 : word) = Some W_7f4b8.
Proof. vm_refl. Qed.
Lemma D_7f4b8 : decode_any W_7f4b8 = Some (OpImm32 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4bc : bv 32 := 0x40c287bb.
Lemma F_7f4bc : fetch_word Ubsan.M.loaded_segments (0x7f4bc : word) = Some W_7f4bc.
Proof. vm_refl. Qed.
Lemma D_7f4bc : decode_any W_7f4bc = Some (Op32 ALU_SUB 15 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4c0 : bv 32 := 0x40c28633.
Lemma F_7f4c0 : fetch_word Ubsan.M.loaded_segments (0x7f4c0 : word) = Some W_7f4c0.
Proof. vm_refl. Qed.
Lemma D_7f4c0 : decode_any W_7f4c0 = Some (Op ALU_SUB 12 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4c4 : bv 32 := 0x7cc79a63.
Lemma F_7f4c4 : fetch_word Ubsan.M.loaded_segments (0x7f4c4 : word) = Some W_7f4c4.
Proof. vm_refl. Qed.
Lemma D_7f4c4 : decode_any W_7f4c4 = Some (Branch BC_NE 15 12 2004, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4c8 : bv 32 := 0x00f05863.
Lemma F_7f4c8 : fetch_word Ubsan.M.loaded_segments (0x7f4c8 : word) = Some W_7f4c8.
Proof. vm_refl. Qed.
Lemma D_7f4c8 : decode_any W_7f4c8 = Some (Branch BC_GE 0 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4cc : bv 32 := 0x40f68333.
Lemma F_7f4cc : fetch_word Ubsan.M.loaded_segments (0x7f4cc : word) = Some W_7f4cc.
Proof. vm_refl. Qed.
Lemma D_7f4cc : decode_any W_7f4cc = Some (Op ALU_SUB 6 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4d0 : bv 32 := 0x40f686bb.
Lemma F_7f4d0 : fetch_word Ubsan.M.loaded_segments (0x7f4d0 : word) = Some W_7f4d0.
Proof. vm_refl. Qed.
Lemma D_7f4d0 : decode_any W_7f4d0 = Some (Op32 ALU_SUB 13 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4d4 : bv 32 := 0x7c669263.
Lemma F_7f4d4 : fetch_word Ubsan.M.loaded_segments (0x7f4d4 : word) = Some W_7f4d4.
Proof. vm_refl. Qed.
Lemma D_7f4d4 : decode_any W_7f4d4 = Some (Branch BC_NE 13 6 1988, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4d8 : bv 32 := 0x0008869b.
Lemma F_7f4d8 : fetch_word Ubsan.M.loaded_segments (0x7f4d8 : word) = Some W_7f4d8.
Proof. vm_refl. Qed.
Lemma D_7f4d8 : decode_any W_7f4d8 = Some (OpImm32 13 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4dc : bv 32 := 0x62d05663.
Lemma F_7f4dc : fetch_word Ubsan.M.loaded_segments (0x7f4dc : word) = Some W_7f4dc.
Proof. vm_refl. Qed.
Lemma D_7f4dc : decode_any W_7f4dc = Some (Branch BC_GE 0 13 1580, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4e0 : bv 32 := 0x0003061b.
Lemma F_7f4e0 : fetch_word Ubsan.M.loaded_segments (0x7f4e0 : word) = Some W_7f4e0.
Proof. vm_refl. Qed.
Lemma D_7f4e0 : decode_any W_7f4e0 = Some (OpImm32 12 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4e4 : bv 32 := 0x62c05263.
Lemma F_7f4e4 : fetch_word Ubsan.M.loaded_segments (0x7f4e4 : word) = Some W_7f4e4.
Proof. vm_refl. Qed.
Lemma D_7f4e4 : decode_any W_7f4e4 = Some (Branch BC_GE 0 12 1572, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4e8 : bv 32 := 0x01f3f793.
Lemma F_7f4e8 : fetch_word Ubsan.M.loaded_segments (0x7f4e8 : word) = Some W_7f4e8.
Proof. vm_refl. Qed.
Lemma D_7f4e8 : decode_any W_7f4e8 = Some (OpImm ALU_AND 15 7 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4ec : bv 32 := 0x0a078e63.
Lemma F_7f4ec : fetch_word Ubsan.M.loaded_segments (0x7f4ec : word) = Some W_7f4ec.
Proof. vm_refl. Qed.
Lemma D_7f4ec : decode_any W_7f4ec = Some (Branch BC_EQ 15 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4f0 : bv 32 := 0x02000293.
Lemma F_7f4f0 : fetch_word Ubsan.M.loaded_segments (0x7f4f0 : word) = Some W_7f4f0.
Proof. vm_refl. Qed.
Lemma D_7f4f0 : decode_any W_7f4f0 = Some (OpImm ALU_ADD 5 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4f4 : bv 32 := 0xfffa0e17.
Lemma F_7f4f4 : fetch_word Ubsan.M.loaded_segments (0x7f4f4 : word) = Some W_7f4f4.
Proof. vm_refl. Qed.
Lemma D_7f4f4 : decode_any W_7f4f4 = Some (Auipc 28 1048480, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4f8 : bv 32 := 0x40f28f33.
Lemma F_7f4f8 : fetch_word Ubsan.M.loaded_segments (0x7f4f8 : word) = Some W_7f4f8.
Proof. vm_refl. Qed.
Lemma D_7f4f8 : decode_any W_7f4f8 = Some (Op ALU_SUB 30 5 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4fc : bv 32 := 0xf4ce0793.
Lemma F_7f4fc : fetch_word Ubsan.M.loaded_segments (0x7f4fc : word) = Some W_7f4fc.
Proof. vm_refl. Qed.
Lemma D_7f4fc : decode_any W_7f4fc = Some (OpImm ALU_ADD 15 28 3916, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f500 : bv 32 := 0x002f1e13.
Lemma F_7f500 : fetch_word Ubsan.M.loaded_segments (0x7f500 : word) = Some W_7f500.
Proof. vm_refl. Qed.
Lemma D_7f500 : decode_any W_7f500 = Some (ShiftImm ALU_SLL 28 30 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f504 : bv 32 := 0xfff7c293.
Lemma F_7f504 : fetch_word Ubsan.M.loaded_segments (0x7f504 : word) = Some W_7f504.
Proof. vm_refl. Qed.
Lemma D_7f504 : decode_any W_7f504 = Some (OpImm ALU_XOR 5 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f508 : bv 32 := 0x79c2e863.
Lemma F_7f508 : fetch_word Ubsan.M.loaded_segments (0x7f508 : word) = Some W_7f508.
Proof. vm_refl. Qed.
Lemma D_7f508 : decode_any W_7f508 = Some (Branch BC_LTU 5 28 1936, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f50c : bv 32 := 0x030702b3.
Lemma F_7f50c : fetch_word Ubsan.M.loaded_segments (0x7f50c : word) = Some W_7f50c.
Proof. vm_refl. Qed.
Lemma D_7f50c : decode_any W_7f50c = Some (Mul M_MUL 5 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f510 : bv 32 := 0x0307083b.
Lemma F_7f510 : fetch_word Ubsan.M.loaded_segments (0x7f510 : word) = Some W_7f510.
Proof. vm_refl. Qed.
Lemma D_7f510 : decode_any W_7f510 = Some (Mul32 M_MUL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f514 : bv 32 := 0x78581263.
Lemma F_7f514 : fetch_word Ubsan.M.loaded_segments (0x7f514 : word) = Some W_7f514.
Proof. vm_refl. Qed.
Lemma D_7f514 : decode_any W_7f514 = Some (Branch BC_NE 16 5 1924, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f518 : bv 32 := 0x0002829b.
Lemma F_7f518 : fetch_word Ubsan.M.loaded_segments (0x7f518 : word) = Some W_7f518.
Proof. vm_refl. Qed.
Lemma D_7f518 : decode_any W_7f518 = Some (OpImm32 5 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f51c : bv 32 := 0x00229f93.
Lemma F_7f51c : fetch_word Ubsan.M.loaded_segments (0x7f51c : word) = Some W_7f51c.
Proof. vm_refl. Qed.
Lemma D_7f51c : decode_any W_7f51c = Some (ShiftImm ALU_SLL 31 5 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f520 : bv 32 := 0x00af8fb3.
Lemma F_7f520 : fetch_word Ubsan.M.loaded_segments (0x7f520 : word) = Some W_7f520.
Proof. vm_refl. Qed.
Lemma D_7f520 : decode_any W_7f520 = Some (Op ALU_ADD 31 31 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f524 : bv 32 := 0x00a03833.
Lemma F_7f524 : fetch_word Ubsan.M.loaded_segments (0x7f524 : word) = Some W_7f524.
Proof. vm_refl. Qed.
Lemma D_7f524 : decode_any W_7f524 = Some (Op ALU_SLTU 16 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f528 : bv 32 := 0x001fb413.
Lemma F_7f528 : fetch_word Ubsan.M.loaded_segments (0x7f528 : word) = Some W_7f528.
Proof. vm_refl. Qed.
Lemma D_7f528 : decode_any W_7f528 = Some (OpImm ALU_SLTU 8 31 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f52c : bv 32 := 0x76880663.
Lemma F_7f52c : fetch_word Ubsan.M.loaded_segments (0x7f52c : word) = Some W_7f52c.
Proof. vm_refl. Qed.
Lemma D_7f52c : decode_any W_7f52c = Some (Branch BC_EQ 16 8 1900, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f530 : bv 32 := 0x00afb533.
Lemma F_7f530 : fetch_word Ubsan.M.loaded_segments (0x7f530 : word) = Some W_7f530.
Proof. vm_refl. Qed.
Lemma D_7f530 : decode_any W_7f530 = Some (Op ALU_SLTU 10 31 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f534 : bv 32 := 0x0002a293.
Lemma F_7f534 : fetch_word Ubsan.M.loaded_segments (0x7f534 : word) = Some W_7f534.
Proof. vm_refl. Qed.
Lemma D_7f534 : decode_any W_7f534 = Some (OpImm ALU_SLT 5 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f538 : bv 32 := 0x00554533.
Lemma F_7f538 : fetch_word Ubsan.M.loaded_segments (0x7f538 : word) = Some W_7f538.
Proof. vm_refl. Qed.
Lemma D_7f538 : decode_any W_7f538 = Some (Op ALU_XOR 10 10 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f53c : bv 32 := 0x00154513.
Lemma F_7f53c : fetch_word Ubsan.M.loaded_segments (0x7f53c : word) = Some W_7f53c.
Proof. vm_refl. Qed.
Lemma D_7f53c : decode_any W_7f53c = Some (OpImm ALU_XOR 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f540 : bv 32 := 0x74050c63.
Lemma F_7f540 : fetch_word Ubsan.M.loaded_segments (0x7f540 : word) = Some W_7f540.
Proof. vm_refl. Qed.
Lemma D_7f540 : decode_any W_7f540 = Some (Branch BC_EQ 10 0 1880, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f544 : bv 32 := 0x0053d51b.
Lemma F_7f544 : fetch_word Ubsan.M.loaded_segments (0x7f544 : word) = Some W_7f544.
Proof. vm_refl. Qed.
Lemma D_7f544 : decode_any W_7f544 = Some (ShiftImm32 ALU_SRL 10 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f548 : bv 32 := 0x00251513.
Lemma F_7f548 : fetch_word Ubsan.M.loaded_segments (0x7f548 : word) = Some W_7f548.
Proof. vm_refl. Qed.
Lemma D_7f548 : decode_any W_7f548 = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f54c : bv 32 := 0x01f502b3.
Lemma F_7f54c : fetch_word Ubsan.M.loaded_segments (0x7f54c : word) = Some W_7f54c.
Proof. vm_refl. Qed.
Lemma D_7f54c : decode_any W_7f54c = Some (Op ALU_ADD 5 10 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f550 : bv 32 := 0x75f2e463.
Lemma F_7f550 : fetch_word Ubsan.M.loaded_segments (0x7f550 : word) = Some W_7f550.
Proof. vm_refl. Qed.
Lemma D_7f550 : decode_any W_7f550 = Some (Branch BC_LTU 5 31 1864, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f554 : bv 32 := 0x0012b513.
Lemma F_7f554 : fetch_word Ubsan.M.loaded_segments (0x7f554 : word) = Some W_7f554.
Proof. vm_refl. Qed.
Lemma D_7f554 : decode_any W_7f554 = Some (OpImm ALU_SLTU 10 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f558 : bv 32 := 0x00a84533.
Lemma F_7f558 : fetch_word Ubsan.M.loaded_segments (0x7f558 : word) = Some W_7f558.
Proof. vm_refl. Qed.
Lemma D_7f558 : decode_any W_7f558 = Some (Op ALU_XOR 10 16 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f55c : bv 32 := 0x72050e63.
Lemma F_7f55c : fetch_word Ubsan.M.loaded_segments (0x7f55c : word) = Some W_7f55c.
Proof. vm_refl. Qed.
Lemma D_7f55c : decode_any W_7f55c = Some (Branch BC_EQ 10 0 1852, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f560 : bv 32 := 0x01c787b3.
Lemma F_7f560 : fetch_word Ubsan.M.loaded_segments (0x7f560 : word) = Some W_7f560.
Proof. vm_refl. Qed.
Lemma D_7f560 : decode_any W_7f560 = Some (Op ALU_ADD 15 15 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f564 : bv 32 := 0x0007a383.
Lemma F_7f564 : fetch_word Ubsan.M.loaded_segments (0x7f564 : word) = Some W_7f564.
Proof. vm_refl. Qed.
Lemma D_7f564 : decode_any W_7f564 = Some (Load SZ4 true 7 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f568 : bv 32 := 0x41e8853b.
Lemma F_7f568 : fetch_word Ubsan.M.loaded_segments (0x7f568 : word) = Some W_7f568.
Proof. vm_refl. Qed.
Lemma D_7f568 : decode_any W_7f568 = Some (Op32 ALU_SUB 10 17 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f56c : bv 32 := 0x07e6f263.
Lemma F_7f56c : fetch_word Ubsan.M.loaded_segments (0x7f56c : word) = Some W_7f56c.
Proof. vm_refl. Qed.
Lemma D_7f56c : decode_any W_7f56c = Some (Branch BC_GEU 13 30 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f570 : bv 32 := 0x0205051b.
Lemma F_7f570 : fetch_word Ubsan.M.loaded_segments (0x7f570 : word) = Some W_7f570.
Proof. vm_refl. Qed.
Lemma D_7f570 : decode_any W_7f570 = Some (OpImm32 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f574 : bv 32 := 0x02000793.
Lemma F_7f574 : fetch_word Ubsan.M.loaded_segments (0x7f574 : word) = Some W_7f574.
Proof. vm_refl. Qed.
Lemma D_7f574 : decode_any W_7f574 = Some (OpImm ALU_ADD 15 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f578 : bv 32 := 0x72a7e063.
Lemma F_7f578 : fetch_word Ubsan.M.loaded_segments (0x7f578 : word) = Some W_7f578.
Proof. vm_refl. Qed.
Lemma D_7f578 : decode_any W_7f578 = Some (Branch BC_LTU 15 10 1824, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f57c : bv 32 := 0x00251513.
Lemma F_7f57c : fetch_word Ubsan.M.loaded_segments (0x7f57c : word) = Some W_7f57c.
Proof. vm_refl. Qed.
Lemma D_7f57c : decode_any W_7f57c = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f580 : bv 32 := 0xfffa0797.
Lemma F_7f580 : fetch_word Ubsan.M.loaded_segments (0x7f580 : word) = Some W_7f580.
Proof. vm_refl. Qed.
Lemma D_7f580 : decode_any W_7f580 = Some (Auipc 15 1048480, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f584 : bv 32 := 0xf4478893.
Lemma F_7f584 : fetch_word Ubsan.M.loaded_segments (0x7f584 : word) = Some W_7f584.
Proof. vm_refl. Qed.
Lemma D_7f584 : decode_any W_7f584 = Some (OpImm ALU_ADD 17 15 3908, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f588 : bv 32 := 0xfff8c793.
Lemma F_7f588 : fetch_word Ubsan.M.loaded_segments (0x7f588 : word) = Some W_7f588.
Proof. vm_refl. Qed.
Lemma D_7f588 : decode_any W_7f588 = Some (OpImm ALU_XOR 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f58c : bv 32 := 0x70a7e663.
Lemma F_7f58c : fetch_word Ubsan.M.loaded_segments (0x7f58c : word) = Some W_7f58c.
Proof. vm_refl. Qed.
Lemma D_7f58c : decode_any W_7f58c = Some (Branch BC_LTU 15 10 1804, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f590 : bv 32 := 0x00000793.
Lemma F_7f590 : fetch_word Ubsan.M.loaded_segments (0x7f590 : word) = Some W_7f590.
Proof. vm_refl. Qed.
Lemma D_7f590 : decode_any W_7f590 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f594 : bv 32 := 0x00000813.
Lemma F_7f594 : fetch_word Ubsan.M.loaded_segments (0x7f594 : word) = Some W_7f594.
Proof. vm_refl. Qed.
Lemma D_7f594 : decode_any W_7f594 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f598 : bv 32 := 0x00a88533.
Lemma F_7f598 : fetch_word Ubsan.M.loaded_segments (0x7f598 : word) = Some W_7f598.
Proof. vm_refl. Qed.
Lemma D_7f598 : decode_any W_7f598 = Some (Op ALU_ADD 10 17 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f59c : bv 32 := 0x00052503.
Lemma F_7f59c : fetch_word Ubsan.M.loaded_segments (0x7f59c : word) = Some W_7f59c.
Proof. vm_refl. Qed.
Lemma D_7f59c : decode_any W_7f59c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5a0 : bv 32 := 0x007573b3.
Lemma F_7f5a0 : fetch_word Ubsan.M.loaded_segments (0x7f5a0 : word) = Some W_7f5a0.
Proof. vm_refl. Qed.
Lemma D_7f5a0 : decode_any W_7f5a0 = Some (Op ALU_AND 7 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5a4 : bv 32 := 0x1540006f.
Lemma F_7f5a4 : fetch_word Ubsan.M.loaded_segments (0x7f5a4 : word) = Some W_7f5a4.
Proof. vm_refl. Qed.
Lemma D_7f5a4 : decode_any W_7f5a4 = Some (Jal 0 340, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5a8 : bv 32 := 0x01f8f793.
Lemma F_7f5a8 : fetch_word Ubsan.M.loaded_segments (0x7f5a8 : word) = Some W_7f5a8.
Proof. vm_refl. Qed.
Lemma D_7f5a8 : decode_any W_7f5a8 = Some (OpImm ALU_AND 15 17 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5ac : bv 32 := 0x04078063.
Lemma F_7f5ac : fetch_word Ubsan.M.loaded_segments (0x7f5ac : word) = Some W_7f5ac.
Proof. vm_refl. Qed.
Lemma D_7f5ac : decode_any W_7f5ac = Some (Branch BC_EQ 15 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5b0 : bv 32 := 0x00279293.
Lemma F_7f5b0 : fetch_word Ubsan.M.loaded_segments (0x7f5b0 : word) = Some W_7f5b0.
Proof. vm_refl. Qed.
Lemma D_7f5b0 : decode_any W_7f5b0 = Some (ShiftImm ALU_SLL 5 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5b4 : bv 32 := 0xfffa0317.
Lemma F_7f5b4 : fetch_word Ubsan.M.loaded_segments (0x7f5b4 : word) = Some W_7f5b4.
Proof. vm_refl. Qed.
Lemma D_7f5b4 : decode_any W_7f5b4 = Some (Auipc 6 1048480, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5b8 : bv 32 := 0xf1030313.
Lemma F_7f5b8 : fetch_word Ubsan.M.loaded_segments (0x7f5b8 : word) = Some W_7f5b8.
Proof. vm_refl. Qed.
Lemma D_7f5b8 : decode_any W_7f5b8 = Some (OpImm ALU_ADD 6 6 3856, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5bc : bv 32 := 0xfff34e13.
Lemma F_7f5bc : fetch_word Ubsan.M.loaded_segments (0x7f5bc : word) = Some W_7f5bc.
Proof. vm_refl. Qed.
Lemma D_7f5bc : decode_any W_7f5bc = Some (OpImm ALU_XOR 28 6 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5c0 : bv 32 := 0x6c5e6c63.
Lemma F_7f5c0 : fetch_word Ubsan.M.loaded_segments (0x7f5c0 : word) = Some W_7f5c0.
Proof. vm_refl. Qed.
Lemma D_7f5c0 : decode_any W_7f5c0 = Some (Branch BC_LTU 28 5 1752, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5c4 : bv 32 := 0x005302b3.
Lemma F_7f5c4 : fetch_word Ubsan.M.loaded_segments (0x7f5c4 : word) = Some W_7f5c4.
Proof. vm_refl. Qed.
Lemma D_7f5c4 : decode_any W_7f5c4 = Some (Op ALU_ADD 5 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5c8 : bv 32 := 0x0002a303.
Lemma F_7f5c8 : fetch_word Ubsan.M.loaded_segments (0x7f5c8 : word) = Some W_7f5c8.
Proof. vm_refl. Qed.
Lemma D_7f5c8 : decode_any W_7f5c8 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5cc : bv 32 := 0x0200006f.
Lemma F_7f5cc : fetch_word Ubsan.M.loaded_segments (0x7f5cc : word) = Some W_7f5cc.
Proof. vm_refl. Qed.
Lemma D_7f5cc : decode_any W_7f5cc = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5d0 : bv 32 := 0x0055579b.
Lemma F_7f5d0 : fetch_word Ubsan.M.loaded_segments (0x7f5d0 : word) = Some W_7f5d0.
Proof. vm_refl. Qed.
Lemma D_7f5d0 : decode_any W_7f5d0 = Some (ShiftImm32 ALU_SRL 15 10 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5d4 : bv 32 := 0x12078063.
Lemma F_7f5d4 : fetch_word Ubsan.M.loaded_segments (0x7f5d4 : word) = Some W_7f5d4.
Proof. vm_refl. Qed.
Lemma D_7f5d4 : decode_any W_7f5d4 = Some (Branch BC_EQ 15 0 288, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5d8 : bv 32 := 0x00428813.
Lemma F_7f5d8 : fetch_word Ubsan.M.loaded_segments (0x7f5d8 : word) = Some W_7f5d8.
Proof. vm_refl. Qed.
Lemma D_7f5d8 : decode_any W_7f5d8 = Some (OpImm ALU_ADD 16 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5dc : bv 32 := 0x00500513.
Lemma F_7f5dc : fetch_word Ubsan.M.loaded_segments (0x7f5dc : word) = Some W_7f5dc.
Proof. vm_refl. Qed.
Lemma D_7f5dc : decode_any W_7f5dc = Some (OpImm ALU_ADD 10 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5e0 : bv 32 := 0x6aa86c63.
Lemma F_7f5e0 : fetch_word Ubsan.M.loaded_segments (0x7f5e0 : word) = Some W_7f5e0.
Proof. vm_refl. Qed.
Lemma D_7f5e0 : decode_any W_7f5e0 = Some (Branch BC_LTU 16 10 1720, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5e4 : bv 32 := 0x00000e13.
Lemma F_7f5e4 : fetch_word Ubsan.M.loaded_segments (0x7f5e4 : word) = Some W_7f5e4.
Proof. vm_refl. Qed.
Lemma D_7f5e4 : decode_any W_7f5e4 = Some (OpImm ALU_ADD 28 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5e8 : bv 32 := 0x1140006f.
Lemma F_7f5e8 : fetch_word Ubsan.M.loaded_segments (0x7f5e8 : word) = Some W_7f5e8.
Proof. vm_refl. Qed.
Lemma D_7f5e8 : decode_any W_7f5e8 = Some (Jal 0 276, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5ec : bv 32 := 0x030702b3.
Lemma F_7f5ec : fetch_word Ubsan.M.loaded_segments (0x7f5ec : word) = Some W_7f5ec.
Proof. vm_refl. Qed.
Lemma D_7f5ec : decode_any W_7f5ec = Some (Mul M_MUL 5 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5f0 : bv 32 := 0x0307083b.
Lemma F_7f5f0 : fetch_word Ubsan.M.loaded_segments (0x7f5f0 : word) = Some W_7f5f0.
Proof. vm_refl. Qed.
Lemma D_7f5f0 : decode_any W_7f5f0 = Some (Mul32 M_MUL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5f4 : bv 32 := 0x6a581263.
Lemma F_7f5f4 : fetch_word Ubsan.M.loaded_segments (0x7f5f4 : word) = Some W_7f5f4.
Proof. vm_refl. Qed.
Lemma D_7f5f4 : decode_any W_7f5f4 = Some (Branch BC_NE 16 5 1700, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5f8 : bv 32 := 0x0002829b.
Lemma F_7f5f8 : fetch_word Ubsan.M.loaded_segments (0x7f5f8 : word) = Some W_7f5f8.
Proof. vm_refl. Qed.
Lemma D_7f5f8 : decode_any W_7f5f8 = Some (OpImm32 5 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5fc : bv 32 := 0x00229f13.
Lemma F_7f5fc : fetch_word Ubsan.M.loaded_segments (0x7f5fc : word) = Some W_7f5fc.
Proof. vm_refl. Qed.
Lemma D_7f5fc : decode_any W_7f5fc = Some (ShiftImm ALU_SLL 30 5 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f600 : bv 32 := 0x00af0e33.
Lemma F_7f600 : fetch_word Ubsan.M.loaded_segments (0x7f600 : word) = Some W_7f600.
Proof. vm_refl. Qed.
Lemma D_7f600 : decode_any W_7f600 = Some (Op ALU_ADD 28 30 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f604 : bv 32 := 0x00a03833.
Lemma F_7f604 : fetch_word Ubsan.M.loaded_segments (0x7f604 : word) = Some W_7f604.
Proof. vm_refl. Qed.
Lemma D_7f604 : decode_any W_7f604 = Some (Op ALU_SLTU 16 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f608 : bv 32 := 0x001e3e93.
Lemma F_7f608 : fetch_word Ubsan.M.loaded_segments (0x7f608 : word) = Some W_7f608.
Proof. vm_refl. Qed.
Lemma D_7f608 : decode_any W_7f608 = Some (OpImm ALU_SLTU 29 28 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f60c : bv 32 := 0x69d80663.
Lemma F_7f60c : fetch_word Ubsan.M.loaded_segments (0x7f60c : word) = Some W_7f60c.
Proof. vm_refl. Qed.
Lemma D_7f60c : decode_any W_7f60c = Some (Branch BC_EQ 16 29 1676, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f610 : bv 32 := 0x00ae3eb3.
Lemma F_7f610 : fetch_word Ubsan.M.loaded_segments (0x7f610 : word) = Some W_7f610.
Proof. vm_refl. Qed.
Lemma D_7f610 : decode_any W_7f610 = Some (Op ALU_SLTU 29 28 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f614 : bv 32 := 0x0002a293.
Lemma F_7f614 : fetch_word Ubsan.M.loaded_segments (0x7f614 : word) = Some W_7f614.
Proof. vm_refl. Qed.
Lemma D_7f614 : decode_any W_7f614 = Some (OpImm ALU_SLT 5 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f618 : bv 32 := 0x005ec2b3.
Lemma F_7f618 : fetch_word Ubsan.M.loaded_segments (0x7f618 : word) = Some W_7f618.
Proof. vm_refl. Qed.
Lemma D_7f618 : decode_any W_7f618 = Some (Op ALU_XOR 5 29 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f61c : bv 32 := 0x0012c293.
Lemma F_7f61c : fetch_word Ubsan.M.loaded_segments (0x7f61c : word) = Some W_7f61c.
Proof. vm_refl. Qed.
Lemma D_7f61c : decode_any W_7f61c = Some (OpImm ALU_XOR 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f620 : bv 32 := 0x66028c63.
Lemma F_7f620 : fetch_word Ubsan.M.loaded_segments (0x7f620 : word) = Some W_7f620.
Proof. vm_refl. Qed.
Lemma D_7f620 : decode_any W_7f620 = Some (Branch BC_EQ 5 0 1656, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f624 : bv 32 := 0x0053de9b.
Lemma F_7f624 : fetch_word Ubsan.M.loaded_segments (0x7f624 : word) = Some W_7f624.
Proof. vm_refl. Qed.
Lemma D_7f624 : decode_any W_7f624 = Some (ShiftImm32 ALU_SRL 29 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f628 : bv 32 := 0x002e9e93.
Lemma F_7f628 : fetch_word Ubsan.M.loaded_segments (0x7f628 : word) = Some W_7f628.
Proof. vm_refl. Qed.
Lemma D_7f628 : decode_any W_7f628 = Some (ShiftImm ALU_SLL 29 29 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f62c : bv 32 := 0x01de02b3.
Lemma F_7f62c : fetch_word Ubsan.M.loaded_segments (0x7f62c : word) = Some W_7f62c.
Proof. vm_refl. Qed.
Lemma D_7f62c : decode_any W_7f62c = Some (Op ALU_ADD 5 28 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f630 : bv 32 := 0x67c2e463.
Lemma F_7f630 : fetch_word Ubsan.M.loaded_segments (0x7f630 : word) = Some W_7f630.
Proof. vm_refl. Qed.
Lemma D_7f630 : decode_any W_7f630 = Some (Branch BC_LTU 5 28 1640, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f634 : bv 32 := 0x0012b393.
Lemma F_7f634 : fetch_word Ubsan.M.loaded_segments (0x7f634 : word) = Some W_7f634.
Proof. vm_refl. Qed.
Lemma D_7f634 : decode_any W_7f634 = Some (OpImm ALU_SLTU 7 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f638 : bv 32 := 0x007843b3.
Lemma F_7f638 : fetch_word Ubsan.M.loaded_segments (0x7f638 : word) = Some W_7f638.
Proof. vm_refl. Qed.
Lemma D_7f638 : decode_any W_7f638 = Some (Op ALU_XOR 7 16 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f63c : bv 32 := 0x64038e63.
Lemma F_7f63c : fetch_word Ubsan.M.loaded_segments (0x7f63c : word) = Some W_7f63c.
Proof. vm_refl. Qed.
Lemma D_7f63c : decode_any W_7f63c = Some (Branch BC_EQ 7 0 1628, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f640 : bv 32 := 0x0058d89b.
Lemma F_7f640 : fetch_word Ubsan.M.loaded_segments (0x7f640 : word) = Some W_7f640.
Proof. vm_refl. Qed.
Lemma D_7f640 : decode_any W_7f640 = Some (ShiftImm32 ALU_SRL 17 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f644 : bv 32 := 0x58058e63.
Lemma F_7f644 : fetch_word Ubsan.M.loaded_segments (0x7f644 : word) = Some W_7f644.
Proof. vm_refl. Qed.
Lemma D_7f644 : decode_any W_7f644 = Some (Branch BC_EQ 11 0 1436, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f648 : bv 32 := 0x00f00393.
Lemma F_7f648 : fetch_word Ubsan.M.loaded_segments (0x7f648 : word) = Some W_7f648.
Proof. vm_refl. Qed.
Lemma D_7f648 : decode_any W_7f648 = Some (OpImm ALU_ADD 7 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f64c : bv 32 := 0x4c758a63.
Lemma F_7f64c : fetch_word Ubsan.M.loaded_segments (0x7f64c : word) = Some W_7f64c.
Proof. vm_refl. Qed.
Lemma D_7f64c : decode_any W_7f64c = Some (Branch BC_EQ 11 7 1236, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f650 : bv 32 := 0x00500393.
Lemma F_7f650 : fetch_word Ubsan.M.loaded_segments (0x7f650 : word) = Some W_7f650.
Proof. vm_refl. Qed.
Lemma D_7f650 : decode_any W_7f650 = Some (OpImm ALU_ADD 7 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f654 : bv 32 := 0x36759863.
Lemma F_7f654 : fetch_word Ubsan.M.loaded_segments (0x7f654 : word) = Some W_7f654.
Proof. vm_refl. Qed.
Lemma D_7f654 : decode_any W_7f654 = Some (Branch BC_NE 11 7 880, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f658 : bv 32 := 0x00000593.
Lemma F_7f658 : fetch_word Ubsan.M.loaded_segments (0x7f658 : word) = Some W_7f658.
Proof. vm_refl. Qed.
Lemma D_7f658 : decode_any W_7f658 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f65c : bv 32 := 0x00357513.
Lemma F_7f65c : fetch_word Ubsan.M.loaded_segments (0x7f65c : word) = Some W_7f65c.
Proof. vm_refl. Qed.
Lemma D_7f65c : decode_any W_7f65c = Some (OpImm ALU_AND 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f660 : bv 32 := 0x02000393.
Lemma F_7f660 : fetch_word Ubsan.M.loaded_segments (0x7f660 : word) = Some W_7f660.
Proof. vm_refl. Qed.
Lemma D_7f660 : decode_any W_7f660 = Some (OpImm ALU_ADD 7 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f664 : bv 32 := 0xffb00e13.
Lemma F_7f664 : fetch_word Ubsan.M.loaded_segments (0x7f664 : word) = Some W_7f664.
Proof. vm_refl. Qed.
Lemma D_7f664 : decode_any W_7f664 = Some (OpImm ALU_ADD 28 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f668 : bv 32 := 0x0180006f.
Lemma F_7f668 : fetch_word Ubsan.M.loaded_segments (0x7f668 : word) = Some W_7f668.
Proof. vm_refl. Qed.
Lemma D_7f668 : decode_any W_7f668 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f66c : bv 32 := 0x000eaf03.
Lemma F_7f66c : fetch_word Ubsan.M.loaded_segments (0x7f66c : word) = Some W_7f66c.
Proof. vm_refl. Qed.
Lemma D_7f66c : decode_any W_7f66c = Some (Load SZ4 true 30 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f670 : bv 32 := 0x006f4f33.
Lemma F_7f670 : fetch_word Ubsan.M.loaded_segments (0x7f670 : word) = Some W_7f670.
Proof. vm_refl. Qed.
Lemma D_7f670 : decode_any W_7f670 = Some (Op ALU_XOR 30 30 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f674 : bv 32 := 0x01eea023.
Lemma F_7f674 : fetch_word Ubsan.M.loaded_segments (0x7f674 : word) = Some W_7f674.
Proof. vm_refl. Qed.
Lemma D_7f674 : decode_any W_7f674 = Some (Store SZ4 29 30 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f678 : bv 32 := 0x0015859b.
Lemma F_7f678 : fetch_word Ubsan.M.loaded_segments (0x7f678 : word) = Some W_7f678.
Proof. vm_refl. Qed.
Lemma D_7f678 : decode_any W_7f678 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f67c : bv 32 := 0x48c58663.
Lemma F_7f67c : fetch_word Ubsan.M.loaded_segments (0x7f67c : word) = Some W_7f67c.
Proof. vm_refl. Qed.
Lemma D_7f67c : decode_any W_7f67c = Some (Branch BC_EQ 11 12 1164, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f680 : bv 32 := 0x02e58f33.
Lemma F_7f680 : fetch_word Ubsan.M.loaded_segments (0x7f680 : word) = Some W_7f680.
Proof. vm_refl. Qed.
Lemma D_7f680 : decode_any W_7f680 = Some (Mul M_MUL 30 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f684 : bv 32 := 0x02e58ebb.
Lemma F_7f684 : fetch_word Ubsan.M.loaded_segments (0x7f684 : word) = Some W_7f684.
Proof. vm_refl. Qed.
Lemma D_7f684 : decode_any W_7f684 = Some (Mul32 M_MUL 29 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f688 : bv 32 := 0x61ee9863.
Lemma F_7f688 : fetch_word Ubsan.M.loaded_segments (0x7f688 : word) = Some W_7f688.
Proof. vm_refl. Qed.
Lemma D_7f688 : decode_any W_7f688 = Some (Branch BC_NE 29 30 1552, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f68c : bv 32 := 0x000f0f1b.
Lemma F_7f68c : fetch_word Ubsan.M.loaded_segments (0x7f68c : word) = Some W_7f68c.
Proof. vm_refl. Qed.
Lemma D_7f68c : decode_any W_7f68c = Some (OpImm32 30 30 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f690 : bv 32 := 0x002f1e93.
Lemma F_7f690 : fetch_word Ubsan.M.loaded_segments (0x7f690 : word) = Some W_7f690.
Proof. vm_refl. Qed.
Lemma D_7f690 : decode_any W_7f690 = Some (ShiftImm ALU_SLL 29 30 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f694 : bv 32 := 0x005e8eb3.
Lemma F_7f694 : fetch_word Ubsan.M.loaded_segments (0x7f694 : word) = Some W_7f694.
Proof. vm_refl. Qed.
Lemma D_7f694 : decode_any W_7f694 = Some (Op ALU_ADD 29 29 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f698 : bv 32 := 0x001ebf93.
Lemma F_7f698 : fetch_word Ubsan.M.loaded_segments (0x7f698 : word) = Some W_7f698.
Proof. vm_refl. Qed.
Lemma D_7f698 : decode_any W_7f698 = Some (OpImm ALU_SLTU 31 29 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f69c : bv 32 := 0x5ff80e63.
Lemma F_7f69c : fetch_word Ubsan.M.loaded_segments (0x7f69c : word) = Some W_7f69c.
Proof. vm_refl. Qed.
Lemma D_7f69c : decode_any W_7f69c = Some (Branch BC_EQ 16 31 1532, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6a0 : bv 32 := 0x005ebfb3.
Lemma F_7f6a0 : fetch_word Ubsan.M.loaded_segments (0x7f6a0 : word) = Some W_7f6a0.
Proof. vm_refl. Qed.
Lemma D_7f6a0 : decode_any W_7f6a0 = Some (Op ALU_SLTU 31 29 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6a4 : bv 32 := 0x000f2f13.
Lemma F_7f6a4 : fetch_word Ubsan.M.loaded_segments (0x7f6a4 : word) = Some W_7f6a4.
Proof. vm_refl. Qed.
Lemma D_7f6a4 : decode_any W_7f6a4 = Some (OpImm ALU_SLT 30 30 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6a8 : bv 32 := 0x01efcf33.
Lemma F_7f6a8 : fetch_word Ubsan.M.loaded_segments (0x7f6a8 : word) = Some W_7f6a8.
Proof. vm_refl. Qed.
Lemma D_7f6a8 : decode_any W_7f6a8 = Some (Op ALU_XOR 30 31 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6ac : bv 32 := 0x001f4f13.
Lemma F_7f6ac : fetch_word Ubsan.M.loaded_segments (0x7f6ac : word) = Some W_7f6ac.
Proof. vm_refl. Qed.
Lemma D_7f6ac : decode_any W_7f6ac = Some (OpImm ALU_XOR 30 30 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6b0 : bv 32 := 0x5e0f0463.
Lemma F_7f6b0 : fetch_word Ubsan.M.loaded_segments (0x7f6b0 : word) = Some W_7f6b0.
Proof. vm_refl. Qed.
Lemma D_7f6b0 : decode_any W_7f6b0 = Some (Branch BC_EQ 30 0 1512, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6b4 : bv 32 := 0x0276e663.
Lemma F_7f6b4 : fetch_word Ubsan.M.loaded_segments (0x7f6b4 : word) = Some W_7f6b4.
Proof. vm_refl. Qed.
Lemma D_7f6b4 : decode_any W_7f6b4 = Some (Branch BC_LTU 13 7 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6b8 : bv 32 := 0x5e051063.
Lemma F_7f6b8 : fetch_word Ubsan.M.loaded_segments (0x7f6b8 : word) = Some W_7f6b8.
Proof. vm_refl. Qed.
Lemma D_7f6b8 : decode_any W_7f6b8 = Some (Branch BC_NE 10 0 1504, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6bc : bv 32 := 0x00088f13.
Lemma F_7f6bc : fetch_word Ubsan.M.loaded_segments (0x7f6bc : word) = Some W_7f6bc.
Proof. vm_refl. Qed.
Lemma D_7f6bc : decode_any W_7f6bc = Some (OpImm ALU_ADD 30 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6c0 : bv 32 := 0x5c0e8c63.
Lemma F_7f6c0 : fetch_word Ubsan.M.loaded_segments (0x7f6c0 : word) = Some W_7f6c0.
Proof. vm_refl. Qed.
Lemma D_7f6c0 : decode_any W_7f6c0 = Some (Branch BC_EQ 29 0 1496, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6c4 : bv 32 := 0x000eaf83.
Lemma F_7f6c4 : fetch_word Ubsan.M.loaded_segments (0x7f6c4 : word) = Some W_7f6c4.
Proof. vm_refl. Qed.
Lemma D_7f6c4 : decode_any W_7f6c4 = Some (Load SZ4 true 31 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6c8 : bv 32 := 0xffffcf93.
Lemma F_7f6c8 : fetch_word Ubsan.M.loaded_segments (0x7f6c8 : word) = Some W_7f6c8.
Proof. vm_refl. Qed.
Lemma D_7f6c8 : decode_any W_7f6c8 = Some (OpImm ALU_XOR 31 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6cc : bv 32 := 0x01fea023.
Lemma F_7f6cc : fetch_word Ubsan.M.loaded_segments (0x7f6cc : word) = Some W_7f6cc.
Proof. vm_refl. Qed.
Lemma D_7f6cc : decode_any W_7f6cc = Some (Store SZ4 29 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6d0 : bv 32 := 0x5dde6463.
Lemma F_7f6d0 : fetch_word Ubsan.M.loaded_segments (0x7f6d0 : word) = Some W_7f6d0.
Proof. vm_refl. Qed.
Lemma D_7f6d0 : decode_any W_7f6d0 = Some (Branch BC_LTU 28 29 1480, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6d4 : bv 32 := 0xffff0f1b.
Lemma F_7f6d4 : fetch_word Ubsan.M.loaded_segments (0x7f6d4 : word) = Some W_7f6d4.
Proof. vm_refl. Qed.
Lemma D_7f6d4 : decode_any W_7f6d4 = Some (OpImm32 30 30 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6d8 : bv 32 := 0x004e8e93.
Lemma F_7f6d8 : fetch_word Ubsan.M.loaded_segments (0x7f6d8 : word) = Some W_7f6d8.
Proof. vm_refl. Qed.
Lemma D_7f6d8 : decode_any W_7f6d8 = Some (OpImm ALU_ADD 29 29 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6dc : bv 32 := 0xfe0f12e3.
Lemma F_7f6dc : fetch_word Ubsan.M.loaded_segments (0x7f6dc : word) = Some W_7f6dc.
Proof. vm_refl. Qed.
Lemma D_7f6dc : decode_any W_7f6dc = Some (Branch BC_NE 30 0 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6e0 : bv 32 := 0xf8078ce3.
Lemma F_7f6e0 : fetch_word Ubsan.M.loaded_segments (0x7f6e0 : word) = Some W_7f6e0.
Proof. vm_refl. Qed.
Lemma D_7f6e0 : decode_any W_7f6e0 = Some (Branch BC_EQ 15 0 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6e4 : bv 32 := 0x5a0e8a63.
Lemma F_7f6e4 : fetch_word Ubsan.M.loaded_segments (0x7f6e4 : word) = Some W_7f6e4.
Proof. vm_refl. Qed.
Lemma D_7f6e4 : decode_any W_7f6e4 = Some (Branch BC_EQ 29 0 1460, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6e8 : bv 32 := 0x003eff13.
Lemma F_7f6e8 : fetch_word Ubsan.M.loaded_segments (0x7f6e8 : word) = Some W_7f6e8.
Proof. vm_refl. Qed.
Lemma D_7f6e8 : decode_any W_7f6e8 = Some (OpImm ALU_AND 30 29 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6ec : bv 32 := 0xf80f00e3.
Lemma F_7f6ec : fetch_word Ubsan.M.loaded_segments (0x7f6ec : word) = Some W_7f6ec.
Proof. vm_refl. Qed.
Lemma D_7f6ec : decode_any W_7f6ec = Some (Branch BC_EQ 30 0 8064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6f0 : bv 32 := 0x5a80006f.
Lemma F_7f6f0 : fetch_word Ubsan.M.loaded_segments (0x7f6f0 : word) = Some W_7f6f0.
Proof. vm_refl. Qed.
Lemma D_7f6f0 : decode_any W_7f6f0 = Some (Jal 0 1448, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6f4 : bv 32 := 0x00000813.
Lemma F_7f6f4 : fetch_word Ubsan.M.loaded_segments (0x7f6f4 : word) = Some W_7f6f4.
Proof. vm_refl. Qed.
Lemma D_7f6f4 : decode_any W_7f6f4 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6f8 : bv 32 := 0x00100e13.
Lemma F_7f6f8 : fetch_word Ubsan.M.loaded_segments (0x7f6f8 : word) = Some W_7f6f8.
Proof. vm_refl. Qed.
Lemma D_7f6f8 : decode_any W_7f6f8 = Some (OpImm ALU_ADD 28 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f6fc : bv 32 := 0x00de8533.
Lemma F_7f6fc : fetch_word Ubsan.M.loaded_segments (0x7f6fc : word) = Some W_7f6fc.
Proof. vm_refl. Qed.
Lemma D_7f6fc : decode_any W_7f6fc = Some (Op ALU_ADD 10 29 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f700 : bv 32 := 0x00de88bb.
Lemma F_7f700 : fetch_word Ubsan.M.loaded_segments (0x7f700 : word) = Some W_7f700.
Proof. vm_refl. Qed.
Lemma D_7f700 : decode_any W_7f700 = Some (Op32 ALU_ADD 17 29 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f704 : bv 32 := 0x58a89a63.
Lemma F_7f704 : fetch_word Ubsan.M.loaded_segments (0x7f704 : word) = Some W_7f704.
Proof. vm_refl. Qed.
Lemma D_7f704 : decode_any W_7f704 = Some (Branch BC_NE 17 10 1428, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f708 : bv 32 := 0x01e6b6b3.
Lemma F_7f708 : fetch_word Ubsan.M.loaded_segments (0x7f708 : word) = Some W_7f708.
Proof. vm_refl. Qed.
Lemma D_7f708 : decode_any W_7f708 = Some (Op ALU_SLTU 13 13 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f70c : bv 32 := 0x01f57513.
Lemma F_7f70c : fetch_word Ubsan.M.loaded_segments (0x7f70c : word) = Some W_7f70c.
Proof. vm_refl. Qed.
Lemma D_7f70c : decode_any W_7f70c = Some (OpImm ALU_AND 10 10 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f710 : bv 32 := 0x00153893.
Lemma F_7f710 : fetch_word Ubsan.M.loaded_segments (0x7f710 : word) = Some W_7f710.
Proof. vm_refl. Qed.
Lemma D_7f710 : decode_any W_7f710 = Some (OpImm ALU_SLTU 17 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f714 : bv 32 := 0x0116e8b3.
Lemma F_7f714 : fetch_word Ubsan.M.loaded_segments (0x7f714 : word) = Some W_7f714.
Proof. vm_refl. Qed.
Lemma D_7f714 : decode_any W_7f714 = Some (Op ALU_OR 17 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f718 : bv 32 := 0x14088263.
Lemma F_7f718 : fetch_word Ubsan.M.loaded_segments (0x7f718 : word) = Some W_7f718.
Proof. vm_refl. Qed.
Lemma D_7f718 : decode_any W_7f718 = Some (Branch BC_EQ 17 0 324, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f71c : bv 32 := 0x00000513.
Lemma F_7f71c : fetch_word Ubsan.M.loaded_segments (0x7f71c : word) = Some W_7f71c.
Proof. vm_refl. Qed.
Lemma D_7f71c : decode_any W_7f71c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f720 : bv 32 := 0x00f00e93.
Lemma F_7f720 : fetch_word Ubsan.M.loaded_segments (0x7f720 : word) = Some W_7f720.
Proof. vm_refl. Qed.
Lemma D_7f720 : decode_any W_7f720 = Some (OpImm ALU_ADD 29 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f724 : bv 32 := 0x17d58e63.
Lemma F_7f724 : fetch_word Ubsan.M.loaded_segments (0x7f724 : word) = Some W_7f724.
Proof. vm_refl. Qed.
Lemma D_7f724 : decode_any W_7f724 = Some (Branch BC_EQ 11 29 380, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f728 : bv 32 := 0x00500e93.
Lemma F_7f728 : fetch_word Ubsan.M.loaded_segments (0x7f728 : word) = Some W_7f728.
Proof. vm_refl. Qed.
Lemma D_7f728 : decode_any W_7f728 = Some (OpImm ALU_ADD 29 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f72c : bv 32 := 0x2bd58c63.
Lemma F_7f72c : fetch_word Ubsan.M.loaded_segments (0x7f72c : word) = Some W_7f72c.
Proof. vm_refl. Qed.
Lemma D_7f72c : decode_any W_7f72c = Some (Branch BC_EQ 11 29 696, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f730 : bv 32 := 0x28059a63.
Lemma F_7f730 : fetch_word Ubsan.M.loaded_segments (0x7f730 : word) = Some W_7f730.
Proof. vm_refl. Qed.
Lemma D_7f730 : decode_any W_7f730 = Some (Branch BC_NE 11 0 660, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f734 : bv 32 := 0x0032f593.
Lemma F_7f734 : fetch_word Ubsan.M.loaded_segments (0x7f734 : word) = Some W_7f734.
Proof. vm_refl. Qed.
Lemma D_7f734 : decode_any W_7f734 = Some (OpImm ALU_AND 11 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f738 : bv 32 := 0x56059063.
Lemma F_7f738 : fetch_word Ubsan.M.loaded_segments (0x7f738 : word) = Some W_7f738.
Proof. vm_refl. Qed.
Lemma D_7f738 : decode_any W_7f738 = Some (Branch BC_NE 11 0 1376, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f73c : bv 32 := 0xfff3c393.
Lemma F_7f73c : fetch_word Ubsan.M.loaded_segments (0x7f73c : word) = Some W_7f73c.
Proof. vm_refl. Qed.
Lemma D_7f73c : decode_any W_7f73c = Some (OpImm ALU_XOR 7 7 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f740 : bv 32 := 0x00271593.
Lemma F_7f740 : fetch_word Ubsan.M.loaded_segments (0x7f740 : word) = Some W_7f740.
Proof. vm_refl. Qed.
Lemma D_7f740 : decode_any W_7f740 = Some (ShiftImm ALU_SLL 11 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f744 : bv 32 := 0x00072713.
Lemma F_7f744 : fetch_word Ubsan.M.loaded_segments (0x7f744 : word) = Some W_7f744.
Proof. vm_refl. Qed.
Lemma D_7f744 : decode_any W_7f744 = Some (OpImm ALU_SLT 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f748 : bv 32 := 0x00028f13.
Lemma F_7f748 : fetch_word Ubsan.M.loaded_segments (0x7f748 : word) = Some W_7f748.
Proof. vm_refl. Qed.
Lemma D_7f748 : decode_any W_7f748 = Some (OpImm ALU_ADD 30 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f74c : bv 32 := 0x00030e93.
Lemma F_7f74c : fetch_word Ubsan.M.loaded_segments (0x7f74c : word) = Some W_7f74c.
Proof. vm_refl. Qed.
Lemma D_7f74c : decode_any W_7f74c = Some (OpImm ALU_ADD 29 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f750 : bv 32 := 0x54028463.
Lemma F_7f750 : fetch_word Ubsan.M.loaded_segments (0x7f750 : word) = Some W_7f750.
Proof. vm_refl. Qed.
Lemma D_7f750 : decode_any W_7f750 = Some (Branch BC_EQ 5 0 1352, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f754 : bv 32 := 0x0002af83.
Lemma F_7f754 : fetch_word Ubsan.M.loaded_segments (0x7f754 : word) = Some W_7f754.
Proof. vm_refl. Qed.
Lemma D_7f754 : decode_any W_7f754 = Some (Load SZ4 true 31 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f758 : bv 32 := 0x007ff433.
Lemma F_7f758 : fetch_word Ubsan.M.loaded_segments (0x7f758 : word) = Some W_7f758.
Proof. vm_refl. Qed.
Lemma D_7f758 : decode_any W_7f758 = Some (Op ALU_AND 8 31 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f75c : bv 32 := 0x01e58fb3.
Lemma F_7f75c : fetch_word Ubsan.M.loaded_segments (0x7f75c : word) = Some W_7f75c.
Proof. vm_refl. Qed.
Lemma D_7f75c : decode_any W_7f75c = Some (Op ALU_ADD 31 11 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f760 : bv 32 := 0x0082a023.
Lemma F_7f760 : fetch_word Ubsan.M.loaded_segments (0x7f760 : word) = Some W_7f760.
Proof. vm_refl. Qed.
Lemma D_7f760 : decode_any W_7f760 = Some (Store SZ4 5 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f764 : bv 32 := 0x520f8a63.
Lemma F_7f764 : fetch_word Ubsan.M.loaded_segments (0x7f764 : word) = Some W_7f764.
Proof. vm_refl. Qed.
Lemma D_7f764 : decode_any W_7f764 = Some (Branch BC_EQ 31 0 1332, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f768 : bv 32 := 0x01efbf33.
Lemma F_7f768 : fetch_word Ubsan.M.loaded_segments (0x7f768 : word) = Some W_7f768.
Proof. vm_refl. Qed.
Lemma D_7f768 : decode_any W_7f768 = Some (Op ALU_SLTU 30 31 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f76c : bv 32 := 0x00ef4f33.
Lemma F_7f76c : fetch_word Ubsan.M.loaded_segments (0x7f76c : word) = Some W_7f76c.
Proof. vm_refl. Qed.
Lemma D_7f76c : decode_any W_7f76c = Some (Op ALU_XOR 30 30 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f770 : bv 32 := 0x001f4f13.
Lemma F_7f770 : fetch_word Ubsan.M.loaded_segments (0x7f770 : word) = Some W_7f770.
Proof. vm_refl. Qed.
Lemma D_7f770 : decode_any W_7f770 = Some (OpImm ALU_XOR 30 30 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f774 : bv 32 := 0x520f0263.
Lemma F_7f774 : fetch_word Ubsan.M.loaded_segments (0x7f774 : word) = Some W_7f774.
Proof. vm_refl. Qed.
Lemma D_7f774 : decode_any W_7f774 = Some (Branch BC_EQ 30 0 1316, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f778 : bv 32 := 0xfffe8e9b.
Lemma F_7f778 : fetch_word Ubsan.M.loaded_segments (0x7f778 : word) = Some W_7f778.
Proof. vm_refl. Qed.
Lemma D_7f778 : decode_any W_7f778 = Some (OpImm32 29 29 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f77c : bv 32 := 0x00b282b3.
Lemma F_7f77c : fetch_word Ubsan.M.loaded_segments (0x7f77c : word) = Some W_7f77c.
Proof. vm_refl. Qed.
Lemma D_7f77c : decode_any W_7f77c = Some (Op ALU_ADD 5 5 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f780 : bv 32 := 0x000f8f13.
Lemma F_7f780 : fetch_word Ubsan.M.loaded_segments (0x7f780 : word) = Some W_7f780.
Proof. vm_refl. Qed.
Lemma D_7f780 : decode_any W_7f780 = Some (OpImm ALU_ADD 30 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f784 : bv 32 := 0xfc0e96e3.
Lemma F_7f784 : fetch_word Ubsan.M.loaded_segments (0x7f784 : word) = Some W_7f784.
Proof. vm_refl. Qed.
Lemma D_7f784 : decode_any W_7f784 = Some (Branch BC_NE 29 0 8140, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f788 : bv 32 := 0x080e1263.
Lemma F_7f788 : fetch_word Ubsan.M.loaded_segments (0x7f788 : word) = Some W_7f788.
Proof. vm_refl. Qed.
Lemma D_7f788 : decode_any W_7f788 = Some (Branch BC_NE 28 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f78c : bv 32 := 0x00000293.
Lemma F_7f78c : fetch_word Ubsan.M.loaded_segments (0x7f78c : word) = Some W_7f78c.
Proof. vm_refl. Qed.
Lemma D_7f78c : decode_any W_7f78c = Some (OpImm ALU_ADD 5 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f790 : bv 32 := 0x00387393.
Lemma F_7f790 : fetch_word Ubsan.M.loaded_segments (0x7f790 : word) = Some W_7f790.
Proof. vm_refl. Qed.
Lemma D_7f790 : decode_any W_7f790 = Some (OpImm ALU_AND 7 16 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f794 : bv 32 := 0x0013b393.
Lemma F_7f794 : fetch_word Ubsan.M.loaded_segments (0x7f794 : word) = Some W_7f794.
Proof. vm_refl. Qed.
Lemma D_7f794 : decode_any W_7f794 = Some (OpImm ALU_SLTU 7 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f798 : bv 32 := 0x00080e13.
Lemma F_7f798 : fetch_word Ubsan.M.loaded_segments (0x7f798 : word) = Some W_7f798.
Proof. vm_refl. Qed.
Lemma D_7f798 : decode_any W_7f798 = Some (OpImm ALU_ADD 28 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f79c : bv 32 := 0x04078063.
Lemma F_7f79c : fetch_word Ubsan.M.loaded_segments (0x7f79c : word) = Some W_7f79c.
Proof. vm_refl. Qed.
Lemma D_7f79c : decode_any W_7f79c = Some (Branch BC_EQ 15 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7a0 : bv 32 := 0x01003eb3.
Lemma F_7f7a0 : fetch_word Ubsan.M.loaded_segments (0x7f7a0 : word) = Some W_7f7a0.
Proof. vm_refl. Qed.
Lemma D_7f7a0 : decode_any W_7f7a0 = Some (Op ALU_SLTU 29 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7a4 : bv 32 := 0x01d3ff33.
Lemma F_7f7a4 : fetch_word Ubsan.M.loaded_segments (0x7f7a4 : word) = Some W_7f7a4.
Proof. vm_refl. Qed.
Lemma D_7f7a4 : decode_any W_7f7a4 = Some (Op ALU_AND 30 7 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7a8 : bv 32 := 0x00080f93.
Lemma F_7f7a8 : fetch_word Ubsan.M.loaded_segments (0x7f7a8 : word) = Some W_7f7a8.
Proof. vm_refl. Qed.
Lemma D_7f7a8 : decode_any W_7f7a8 = Some (OpImm ALU_ADD 31 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7ac : bv 32 := 0x000e0413.
Lemma F_7f7ac : fetch_word Ubsan.M.loaded_segments (0x7f7ac : word) = Some W_7f7ac.
Proof. vm_refl. Qed.
Lemma D_7f7ac : decode_any W_7f7ac = Some (OpImm ALU_ADD 8 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7b0 : bv 32 := 0x00078493.
Lemma F_7f7b0 : fetch_word Ubsan.M.loaded_segments (0x7f7b0 : word) = Some W_7f7b0.
Proof. vm_refl. Qed.
Lemma D_7f7b0 : decode_any W_7f7b0 = Some (OpImm ALU_ADD 9 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7b4 : bv 32 := 0x4f046263.
Lemma F_7f7b4 : fetch_word Ubsan.M.loaded_segments (0x7f7b4 : word) = Some W_7f7b4.
Proof. vm_refl. Qed.
Lemma D_7f7b4 : decode_any W_7f7b4 = Some (Branch BC_LTU 8 16 1252, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7b8 : bv 32 := 0x00143913.
Lemma F_7f7b8 : fetch_word Ubsan.M.loaded_segments (0x7f7b8 : word) = Some W_7f7b8.
Proof. vm_refl. Qed.
Lemma D_7f7b8 : decode_any W_7f7b8 = Some (OpImm ALU_SLTU 18 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7bc : bv 32 := 0x012ec933.
Lemma F_7f7bc : fetch_word Ubsan.M.loaded_segments (0x7f7bc : word) = Some W_7f7bc.
Proof. vm_refl. Qed.
Lemma D_7f7bc : decode_any W_7f7bc = Some (Op ALU_XOR 18 29 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7c0 : bv 32 := 0x4c090c63.
Lemma F_7f7c0 : fetch_word Ubsan.M.loaded_segments (0x7f7c0 : word) = Some W_7f7c0.
Proof. vm_refl. Qed.
Lemma D_7f7c0 : decode_any W_7f7c0 = Some (Branch BC_EQ 18 0 1240, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7c4 : bv 32 := 0x4c0f0a63.
Lemma F_7f7c4 : fetch_word Ubsan.M.loaded_segments (0x7f7c4 : word) = Some W_7f7c4.
Proof. vm_refl. Qed.
Lemma D_7f7c4 : decode_any W_7f7c4 = Some (Branch BC_EQ 30 0 1236, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7c8 : bv 32 := 0x000fa023.
Lemma F_7f7c8 : fetch_word Ubsan.M.loaded_segments (0x7f7c8 : word) = Some W_7f7c8.
Proof. vm_refl. Qed.
Lemma D_7f7c8 : decode_any W_7f7c8 = Some (Store SZ4 31 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7cc : bv 32 := 0xfff48493.
Lemma F_7f7cc : fetch_word Ubsan.M.loaded_segments (0x7f7cc : word) = Some W_7f7cc.
Proof. vm_refl. Qed.
Lemma D_7f7cc : decode_any W_7f7cc = Some (OpImm ALU_ADD 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7d0 : bv 32 := 0x00440413.
Lemma F_7f7d0 : fetch_word Ubsan.M.loaded_segments (0x7f7d0 : word) = Some W_7f7d0.
Proof. vm_refl. Qed.
Lemma D_7f7d0 : decode_any W_7f7d0 = Some (OpImm ALU_ADD 8 8 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7d4 : bv 32 := 0x004f8f93.
Lemma F_7f7d4 : fetch_word Ubsan.M.loaded_segments (0x7f7d4 : word) = Some W_7f7d4.
Proof. vm_refl. Qed.
Lemma D_7f7d4 : decode_any W_7f7d4 = Some (OpImm ALU_ADD 31 31 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7d8 : bv 32 := 0xfc049ee3.
Lemma F_7f7d8 : fetch_word Ubsan.M.loaded_segments (0x7f7d8 : word) = Some W_7f7d8.
Proof. vm_refl. Qed.
Lemma D_7f7d8 : decode_any W_7f7d8 = Some (Branch BC_NE 9 0 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7dc : bv 32 := 0x01058eb3.
Lemma F_7f7dc : fetch_word Ubsan.M.loaded_segments (0x7f7dc : word) = Some W_7f7dc.
Proof. vm_refl. Qed.
Lemma D_7f7dc : decode_any W_7f7dc = Some (Op ALU_ADD 29 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7e0 : bv 32 := 0x01003f33.
Lemma F_7f7e0 : fetch_word Ubsan.M.loaded_segments (0x7f7e0 : word) = Some W_7f7e0.
Proof. vm_refl. Qed.
Lemma D_7f7e0 : decode_any W_7f7e0 = Some (Op ALU_SLTU 30 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7e4 : bv 32 := 0x001ebf93.
Lemma F_7f7e4 : fetch_word Ubsan.M.loaded_segments (0x7f7e4 : word) = Some W_7f7e4.
Proof. vm_refl. Qed.
Lemma D_7f7e4 : decode_any W_7f7e4 = Some (OpImm ALU_SLTU 31 29 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7e8 : bv 32 := 0x4bff0863.
Lemma F_7f7e8 : fetch_word Ubsan.M.loaded_segments (0x7f7e8 : word) = Some W_7f7e8.
Proof. vm_refl. Qed.
Lemma D_7f7e8 : decode_any W_7f7e8 = Some (Branch BC_EQ 30 31 1200, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7ec : bv 32 := 0x010eb833.
Lemma F_7f7ec : fetch_word Ubsan.M.loaded_segments (0x7f7ec : word) = Some W_7f7ec.
Proof. vm_refl. Qed.
Lemma D_7f7ec : decode_any W_7f7ec = Some (Op ALU_SLTU 16 29 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7f0 : bv 32 := 0x00e84833.
Lemma F_7f7f0 : fetch_word Ubsan.M.loaded_segments (0x7f7f0 : word) = Some W_7f7f0.
Proof. vm_refl. Qed.
Lemma D_7f7f0 : decode_any W_7f7f0 = Some (Op ALU_XOR 16 16 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7f4 : bv 32 := 0x00184813.
Lemma F_7f7f4 : fetch_word Ubsan.M.loaded_segments (0x7f7f4 : word) = Some W_7f7f4.
Proof. vm_refl. Qed.
Lemma D_7f7f4 : decode_any W_7f7f4 = Some (OpImm ALU_XOR 16 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7f8 : bv 32 := 0x4a080063.
Lemma F_7f7f8 : fetch_word Ubsan.M.loaded_segments (0x7f7f8 : word) = Some W_7f7f8.
Proof. vm_refl. Qed.
Lemma D_7f7f8 : decode_any W_7f7f8 = Some (Branch BC_EQ 16 0 1184, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7fc : bv 32 := 0x0012829b.
Lemma F_7f7fc : fetch_word Ubsan.M.loaded_segments (0x7f7fc : word) = Some W_7f7fc.
Proof. vm_refl. Qed.
Lemma D_7f7fc : decode_any W_7f7fc = Some (OpImm32 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f800 : bv 32 := 0x00be0e33.
Lemma F_7f800 : fetch_word Ubsan.M.loaded_segments (0x7f800 : word) = Some W_7f800.
Proof. vm_refl. Qed.
Lemma D_7f800 : decode_any W_7f800 = Some (Op ALU_ADD 28 28 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f804 : bv 32 := 0x000e8813.
Lemma F_7f804 : fetch_word Ubsan.M.loaded_segments (0x7f804 : word) = Some W_7f804.
Proof. vm_refl. Qed.
Lemma D_7f804 : decode_any W_7f804 = Some (OpImm ALU_ADD 16 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f808 : bv 32 := 0xf8c29ae3.
Lemma F_7f808 : fetch_word Ubsan.M.loaded_segments (0x7f808 : word) = Some W_7f808.
Proof. vm_refl. Qed.
Lemma D_7f808 : decode_any W_7f808 = Some (Branch BC_NE 5 12 8084, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f80c : bv 32 := 0x2e089e63.
Lemma F_7f80c : fetch_word Ubsan.M.loaded_segments (0x7f80c : word) = Some W_7f80c.
Proof. vm_refl. Qed.
Lemma D_7f80c : decode_any W_7f80c = Some (Branch BC_NE 17 0 764, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f810 : bv 32 := 0x00357613.
Lemma F_7f810 : fetch_word Ubsan.M.loaded_segments (0x7f810 : word) = Some W_7f810.
Proof. vm_refl. Qed.
Lemma D_7f810 : decode_any W_7f810 = Some (OpImm ALU_AND 12 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f814 : bv 32 := 0x48061263.
Lemma F_7f814 : fetch_word Ubsan.M.loaded_segments (0x7f814 : word) = Some W_7f814.
Proof. vm_refl. Qed.
Lemma D_7f814 : decode_any W_7f814 = Some (Branch BC_NE 12 0 1156, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f818 : bv 32 := 0xfff6c613.
Lemma F_7f818 : fetch_word Ubsan.M.loaded_segments (0x7f818 : word) = Some W_7f818.
Proof. vm_refl. Qed.
Lemma D_7f818 : decode_any W_7f818 = Some (OpImm ALU_XOR 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f81c : bv 32 := 0x00050693.
Lemma F_7f81c : fetch_word Ubsan.M.loaded_segments (0x7f81c : word) = Some W_7f81c.
Proof. vm_refl. Qed.
Lemma D_7f81c : decode_any W_7f81c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f820 : bv 32 := 0x46050c63.
Lemma F_7f820 : fetch_word Ubsan.M.loaded_segments (0x7f820 : word) = Some W_7f820.
Proof. vm_refl. Qed.
Lemma D_7f820 : decode_any W_7f820 = Some (Branch BC_EQ 10 0 1144, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f824 : bv 32 := 0x00052783.
Lemma F_7f824 : fetch_word Ubsan.M.loaded_segments (0x7f824 : word) = Some W_7f824.
Proof. vm_refl. Qed.
Lemma D_7f824 : decode_any W_7f824 = Some (Load SZ4 true 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f828 : bv 32 := 0x00c7f833.
Lemma F_7f828 : fetch_word Ubsan.M.loaded_segments (0x7f828 : word) = Some W_7f828.
Proof. vm_refl. Qed.
Lemma D_7f828 : decode_any W_7f828 = Some (Op ALU_AND 16 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f82c : bv 32 := 0x00d587b3.
Lemma F_7f82c : fetch_word Ubsan.M.loaded_segments (0x7f82c : word) = Some W_7f82c.
Proof. vm_refl. Qed.
Lemma D_7f82c : decode_any W_7f82c = Some (Op ALU_ADD 15 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f830 : bv 32 := 0x01052023.
Lemma F_7f830 : fetch_word Ubsan.M.loaded_segments (0x7f830 : word) = Some W_7f830.
Proof. vm_refl. Qed.
Lemma D_7f830 : decode_any W_7f830 = Some (Store SZ4 10 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f834 : bv 32 := 0x46078263.
Lemma F_7f834 : fetch_word Ubsan.M.loaded_segments (0x7f834 : word) = Some W_7f834.
Proof. vm_refl. Qed.
Lemma D_7f834 : decode_any W_7f834 = Some (Branch BC_EQ 15 0 1124, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f838 : bv 32 := 0x00d7b6b3.
Lemma F_7f838 : fetch_word Ubsan.M.loaded_segments (0x7f838 : word) = Some W_7f838.
Proof. vm_refl. Qed.
Lemma D_7f838 : decode_any W_7f838 = Some (Op ALU_SLTU 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f83c : bv 32 := 0x00e6c6b3.
Lemma F_7f83c : fetch_word Ubsan.M.loaded_segments (0x7f83c : word) = Some W_7f83c.
Proof. vm_refl. Qed.
Lemma D_7f83c : decode_any W_7f83c = Some (Op ALU_XOR 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f840 : bv 32 := 0x0016c693.
Lemma F_7f840 : fetch_word Ubsan.M.loaded_segments (0x7f840 : word) = Some W_7f840.
Proof. vm_refl. Qed.
Lemma D_7f840 : decode_any W_7f840 = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f844 : bv 32 := 0x44068a63.
Lemma F_7f844 : fetch_word Ubsan.M.loaded_segments (0x7f844 : word) = Some W_7f844.
Proof. vm_refl. Qed.
Lemma D_7f844 : decode_any W_7f844 = Some (Branch BC_EQ 13 0 1108, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f848 : bv 32 := 0xfff3031b.
Lemma F_7f848 : fetch_word Ubsan.M.loaded_segments (0x7f848 : word) = Some W_7f848.
Proof. vm_refl. Qed.
Lemma D_7f848 : decode_any W_7f848 = Some (OpImm32 6 6 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f84c : bv 32 := 0x00b50533.
Lemma F_7f84c : fetch_word Ubsan.M.loaded_segments (0x7f84c : word) = Some W_7f84c.
Proof. vm_refl. Qed.
Lemma D_7f84c : decode_any W_7f84c = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f850 : bv 32 := 0x00078693.
Lemma F_7f850 : fetch_word Ubsan.M.loaded_segments (0x7f850 : word) = Some W_7f850.
Proof. vm_refl. Qed.
Lemma D_7f850 : decode_any W_7f850 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f854 : bv 32 := 0xfc0316e3.
Lemma F_7f854 : fetch_word Ubsan.M.loaded_segments (0x7f854 : word) = Some W_7f854.
Proof. vm_refl. Qed.
Lemma D_7f854 : decode_any W_7f854 = Some (Branch BC_NE 6 0 8140, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f858 : bv 32 := 0x2b00006f.
Lemma F_7f858 : fetch_word Ubsan.M.loaded_segments (0x7f858 : word) = Some W_7f858.
Proof. vm_refl. Qed.
Lemma D_7f858 : decode_any W_7f858 = Some (Jal 0 688, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f85c : bv 32 := 0x00251513.
Lemma F_7f85c : fetch_word Ubsan.M.loaded_segments (0x7f85c : word) = Some W_7f85c.
Proof. vm_refl. Qed.
Lemma D_7f85c : decode_any W_7f85c = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f860 : bv 32 := 0xfffa0697.
Lemma F_7f860 : fetch_word Ubsan.M.loaded_segments (0x7f860 : word) = Some W_7f860.
Proof. vm_refl. Qed.
Lemma D_7f860 : decode_any W_7f860 = Some (Auipc 13 1048480, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f864 : bv 32 := 0xc6468693.
Lemma F_7f864 : fetch_word Ubsan.M.loaded_segments (0x7f864 : word) = Some W_7f864.
Proof. vm_refl. Qed.
Lemma D_7f864 : decode_any W_7f864 = Some (OpImm ALU_ADD 13 13 3172, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f868 : bv 32 := 0xfff6ce93.
Lemma F_7f868 : fetch_word Ubsan.M.loaded_segments (0x7f868 : word) = Some W_7f868.
Proof. vm_refl. Qed.
Lemma D_7f868 : decode_any W_7f868 = Some (OpImm ALU_XOR 29 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f86c : bv 32 := 0x42aee663.
Lemma F_7f86c : fetch_word Ubsan.M.loaded_segments (0x7f86c : word) = Some W_7f86c.
Proof. vm_refl. Qed.
Lemma D_7f86c : decode_any W_7f86c = Some (Branch BC_LTU 29 10 1068, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f870 : bv 32 := 0x00428e93.
Lemma F_7f870 : fetch_word Ubsan.M.loaded_segments (0x7f870 : word) = Some W_7f870.
Proof. vm_refl. Qed.
Lemma D_7f870 : decode_any W_7f870 = Some (OpImm ALU_ADD 29 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f874 : bv 32 := 0x00500f13.
Lemma F_7f874 : fetch_word Ubsan.M.loaded_segments (0x7f874 : word) = Some W_7f874.
Proof. vm_refl. Qed.
Lemma D_7f874 : decode_any W_7f874 = Some (OpImm ALU_ADD 30 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f878 : bv 32 := 0x43eee063.
Lemma F_7f878 : fetch_word Ubsan.M.loaded_segments (0x7f878 : word) = Some W_7f878.
Proof. vm_refl. Qed.
Lemma D_7f878 : decode_any W_7f878 = Some (Branch BC_LTU 29 30 1056, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f87c : bv 32 := 0x00279f13.
Lemma F_7f87c : fetch_word Ubsan.M.loaded_segments (0x7f87c : word) = Some W_7f87c.
Proof. vm_refl. Qed.
Lemma D_7f87c : decode_any W_7f87c = Some (ShiftImm ALU_SLL 30 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f880 : bv 32 := 0xfffecf93.
Lemma F_7f880 : fetch_word Ubsan.M.loaded_segments (0x7f880 : word) = Some W_7f880.
Proof. vm_refl. Qed.
Lemma D_7f880 : decode_any W_7f880 = Some (OpImm ALU_XOR 31 29 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f884 : bv 32 := 0x41efea63.
Lemma F_7f884 : fetch_word Ubsan.M.loaded_segments (0x7f884 : word) = Some W_7f884.
Proof. vm_refl. Qed.
Lemma D_7f884 : decode_any W_7f884 = Some (Branch BC_LTU 31 30 1044, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f888 : bv 32 := 0x00a68533.
Lemma F_7f888 : fetch_word Ubsan.M.loaded_segments (0x7f888 : word) = Some W_7f888.
Proof. vm_refl. Qed.
Lemma D_7f888 : decode_any W_7f888 = Some (Op ALU_ADD 10 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f88c : bv 32 := 0x00052683.
Lemma F_7f88c : fetch_word Ubsan.M.loaded_segments (0x7f88c : word) = Some W_7f88c.
Proof. vm_refl. Qed.
Lemma D_7f88c : decode_any W_7f88c = Some (Load SZ4 true 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f890 : bv 32 := 0x00279513.
Lemma F_7f890 : fetch_word Ubsan.M.loaded_segments (0x7f890 : word) = Some W_7f890.
Proof. vm_refl. Qed.
Lemma D_7f890 : decode_any W_7f890 = Some (ShiftImm ALU_SLL 10 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f894 : bv 32 := 0x00ae8533.
Lemma F_7f894 : fetch_word Ubsan.M.loaded_segments (0x7f894 : word) = Some W_7f894.
Proof. vm_refl. Qed.
Lemma D_7f894 : decode_any W_7f894 = Some (Op ALU_ADD 10 29 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f898 : bv 32 := 0x00f00e93.
Lemma F_7f898 : fetch_word Ubsan.M.loaded_segments (0x7f898 : word) = Some W_7f898.
Proof. vm_refl. Qed.
Lemma D_7f898 : decode_any W_7f898 = Some (OpImm ALU_ADD 29 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f89c : bv 32 := 0xe9d596e3.
Lemma F_7f89c : fetch_word Ubsan.M.loaded_segments (0x7f89c : word) = Some W_7f89c.
Proof. vm_refl. Qed.
Lemma D_7f89c : decode_any W_7f89c = Some (Branch BC_NE 11 29 7820, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8a0 : bv 32 := 0x0032f593.
Lemma F_7f8a0 : fetch_word Ubsan.M.loaded_segments (0x7f8a0 : word) = Some W_7f8a0.
Proof. vm_refl. Qed.
Lemma D_7f8a0 : decode_any W_7f8a0 = Some (OpImm ALU_AND 11 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8a4 : bv 32 := 0x3e059a63.
Lemma F_7f8a4 : fetch_word Ubsan.M.loaded_segments (0x7f8a4 : word) = Some W_7f8a4.
Proof. vm_refl. Qed.
Lemma D_7f8a4 : decode_any W_7f8a4 = Some (Branch BC_NE 11 0 1012, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8a8 : bv 32 := 0x00271593.
Lemma F_7f8a8 : fetch_word Ubsan.M.loaded_segments (0x7f8a8 : word) = Some W_7f8a8.
Proof. vm_refl. Qed.
Lemma D_7f8a8 : decode_any W_7f8a8 = Some (ShiftImm ALU_SLL 11 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8ac : bv 32 := 0x00072713.
Lemma F_7f8ac : fetch_word Ubsan.M.loaded_segments (0x7f8ac : word) = Some W_7f8ac.
Proof. vm_refl. Qed.
Lemma D_7f8ac : decode_any W_7f8ac = Some (OpImm ALU_SLT 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8b0 : bv 32 := 0x00028f13.
Lemma F_7f8b0 : fetch_word Ubsan.M.loaded_segments (0x7f8b0 : word) = Some W_7f8b0.
Proof. vm_refl. Qed.
Lemma D_7f8b0 : decode_any W_7f8b0 = Some (OpImm ALU_ADD 30 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8b4 : bv 32 := 0x00030e93.
Lemma F_7f8b4 : fetch_word Ubsan.M.loaded_segments (0x7f8b4 : word) = Some W_7f8b4.
Proof. vm_refl. Qed.
Lemma D_7f8b4 : decode_any W_7f8b4 = Some (OpImm ALU_ADD 29 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8b8 : bv 32 := 0x3e028063.
Lemma F_7f8b8 : fetch_word Ubsan.M.loaded_segments (0x7f8b8 : word) = Some W_7f8b8.
Proof. vm_refl. Qed.
Lemma D_7f8b8 : decode_any W_7f8b8 = Some (Branch BC_EQ 5 0 992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8bc : bv 32 := 0x0002af83.
Lemma F_7f8bc : fetch_word Ubsan.M.loaded_segments (0x7f8bc : word) = Some W_7f8bc.
Proof. vm_refl. Qed.
Lemma D_7f8bc : decode_any W_7f8bc = Some (Load SZ4 true 31 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8c0 : bv 32 := 0x007fe433.
Lemma F_7f8c0 : fetch_word Ubsan.M.loaded_segments (0x7f8c0 : word) = Some W_7f8c0.
Proof. vm_refl. Qed.
Lemma D_7f8c0 : decode_any W_7f8c0 = Some (Op ALU_OR 8 31 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8c4 : bv 32 := 0x01e58fb3.
Lemma F_7f8c4 : fetch_word Ubsan.M.loaded_segments (0x7f8c4 : word) = Some W_7f8c4.
Proof. vm_refl. Qed.
Lemma D_7f8c4 : decode_any W_7f8c4 = Some (Op ALU_ADD 31 11 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8c8 : bv 32 := 0x0082a023.
Lemma F_7f8c8 : fetch_word Ubsan.M.loaded_segments (0x7f8c8 : word) = Some W_7f8c8.
Proof. vm_refl. Qed.
Lemma D_7f8c8 : decode_any W_7f8c8 = Some (Store SZ4 5 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8cc : bv 32 := 0x3c0f8663.
Lemma F_7f8cc : fetch_word Ubsan.M.loaded_segments (0x7f8cc : word) = Some W_7f8cc.
Proof. vm_refl. Qed.
Lemma D_7f8cc : decode_any W_7f8cc = Some (Branch BC_EQ 31 0 972, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8d0 : bv 32 := 0x01efbf33.
Lemma F_7f8d0 : fetch_word Ubsan.M.loaded_segments (0x7f8d0 : word) = Some W_7f8d0.
Proof. vm_refl. Qed.
Lemma D_7f8d0 : decode_any W_7f8d0 = Some (Op ALU_SLTU 30 31 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8d4 : bv 32 := 0x00ef4f33.
Lemma F_7f8d4 : fetch_word Ubsan.M.loaded_segments (0x7f8d4 : word) = Some W_7f8d4.
Proof. vm_refl. Qed.
Lemma D_7f8d4 : decode_any W_7f8d4 = Some (Op ALU_XOR 30 30 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8d8 : bv 32 := 0x001f4f13.
Lemma F_7f8d8 : fetch_word Ubsan.M.loaded_segments (0x7f8d8 : word) = Some W_7f8d8.
Proof. vm_refl. Qed.
Lemma D_7f8d8 : decode_any W_7f8d8 = Some (OpImm ALU_XOR 30 30 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8dc : bv 32 := 0x3a0f0e63.
Lemma F_7f8dc : fetch_word Ubsan.M.loaded_segments (0x7f8dc : word) = Some W_7f8dc.
Proof. vm_refl. Qed.
Lemma D_7f8dc : decode_any W_7f8dc = Some (Branch BC_EQ 30 0 956, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8e0 : bv 32 := 0xfffe8e9b.
Lemma F_7f8e0 : fetch_word Ubsan.M.loaded_segments (0x7f8e0 : word) = Some W_7f8e0.
Proof. vm_refl. Qed.
Lemma D_7f8e0 : decode_any W_7f8e0 = Some (OpImm32 29 29 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8e4 : bv 32 := 0x00b282b3.
Lemma F_7f8e4 : fetch_word Ubsan.M.loaded_segments (0x7f8e4 : word) = Some W_7f8e4.
Proof. vm_refl. Qed.
Lemma D_7f8e4 : decode_any W_7f8e4 = Some (Op ALU_ADD 5 5 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8e8 : bv 32 := 0x000f8f13.
Lemma F_7f8e8 : fetch_word Ubsan.M.loaded_segments (0x7f8e8 : word) = Some W_7f8e8.
Proof. vm_refl. Qed.
Lemma D_7f8e8 : decode_any W_7f8e8 = Some (OpImm ALU_ADD 30 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8ec : bv 32 := 0xfc0e96e3.
Lemma F_7f8ec : fetch_word Ubsan.M.loaded_segments (0x7f8ec : word) = Some W_7f8ec.
Proof. vm_refl. Qed.
Lemma D_7f8ec : decode_any W_7f8ec = Some (Branch BC_NE 29 0 8140, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8f0 : bv 32 := 0x080e1463.
Lemma F_7f8f0 : fetch_word Ubsan.M.loaded_segments (0x7f8f0 : word) = Some W_7f8f0.
Proof. vm_refl. Qed.
Lemma D_7f8f0 : decode_any W_7f8f0 = Some (Branch BC_NE 28 0 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8f4 : bv 32 := 0x00000293.
Lemma F_7f8f4 : fetch_word Ubsan.M.loaded_segments (0x7f8f4 : word) = Some W_7f8f4.
Proof. vm_refl. Qed.
Lemma D_7f8f4 : decode_any W_7f8f4 = Some (OpImm ALU_ADD 5 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8f8 : bv 32 := 0x00387393.
Lemma F_7f8f8 : fetch_word Ubsan.M.loaded_segments (0x7f8f8 : word) = Some W_7f8f8.
Proof. vm_refl. Qed.
Lemma D_7f8f8 : decode_any W_7f8f8 = Some (OpImm ALU_AND 7 16 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8fc : bv 32 := 0x0013b393.
Lemma F_7f8fc : fetch_word Ubsan.M.loaded_segments (0x7f8fc : word) = Some W_7f8fc.
Proof. vm_refl. Qed.
Lemma D_7f8fc : decode_any W_7f8fc = Some (OpImm ALU_SLTU 7 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f900 : bv 32 := 0xfff00e13.
Lemma F_7f900 : fetch_word Ubsan.M.loaded_segments (0x7f900 : word) = Some W_7f900.
Proof. vm_refl. Qed.
Lemma D_7f900 : decode_any W_7f900 = Some (OpImm ALU_ADD 28 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f904 : bv 32 := 0x00080e93.
Lemma F_7f904 : fetch_word Ubsan.M.loaded_segments (0x7f904 : word) = Some W_7f904.
Proof. vm_refl. Qed.
Lemma D_7f904 : decode_any W_7f904 = Some (OpImm ALU_ADD 29 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f908 : bv 32 := 0x04078063.
Lemma F_7f908 : fetch_word Ubsan.M.loaded_segments (0x7f908 : word) = Some W_7f908.
Proof. vm_refl. Qed.
Lemma D_7f908 : decode_any W_7f908 = Some (Branch BC_EQ 15 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f90c : bv 32 := 0x01003f33.
Lemma F_7f90c : fetch_word Ubsan.M.loaded_segments (0x7f90c : word) = Some W_7f90c.
Proof. vm_refl. Qed.
Lemma D_7f90c : decode_any W_7f90c = Some (Op ALU_SLTU 30 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f910 : bv 32 := 0x01e3ffb3.
Lemma F_7f910 : fetch_word Ubsan.M.loaded_segments (0x7f910 : word) = Some W_7f910.
Proof. vm_refl. Qed.
Lemma D_7f910 : decode_any W_7f910 = Some (Op ALU_AND 31 7 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f914 : bv 32 := 0x00080413.
Lemma F_7f914 : fetch_word Ubsan.M.loaded_segments (0x7f914 : word) = Some W_7f914.
Proof. vm_refl. Qed.
Lemma D_7f914 : decode_any W_7f914 = Some (OpImm ALU_ADD 8 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f918 : bv 32 := 0x000e8493.
Lemma F_7f918 : fetch_word Ubsan.M.loaded_segments (0x7f918 : word) = Some W_7f918.
Proof. vm_refl. Qed.
Lemma D_7f918 : decode_any W_7f918 = Some (OpImm ALU_ADD 9 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f91c : bv 32 := 0x00078913.
Lemma F_7f91c : fetch_word Ubsan.M.loaded_segments (0x7f91c : word) = Some W_7f91c.
Proof. vm_refl. Qed.
Lemma D_7f91c : decode_any W_7f91c = Some (OpImm ALU_ADD 18 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f920 : bv 32 := 0x3704ec63.
Lemma F_7f920 : fetch_word Ubsan.M.loaded_segments (0x7f920 : word) = Some W_7f920.
Proof. vm_refl. Qed.
Lemma D_7f920 : decode_any W_7f920 = Some (Branch BC_LTU 9 16 888, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f924 : bv 32 := 0x0014b993.
Lemma F_7f924 : fetch_word Ubsan.M.loaded_segments (0x7f924 : word) = Some W_7f924.
Proof. vm_refl. Qed.
Lemma D_7f924 : decode_any W_7f924 = Some (OpImm ALU_SLTU 19 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f928 : bv 32 := 0x013f49b3.
Lemma F_7f928 : fetch_word Ubsan.M.loaded_segments (0x7f928 : word) = Some W_7f928.
Proof. vm_refl. Qed.
Lemma D_7f928 : decode_any W_7f928 = Some (Op ALU_XOR 19 30 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f92c : bv 32 := 0x36098663.
Lemma F_7f92c : fetch_word Ubsan.M.loaded_segments (0x7f92c : word) = Some W_7f92c.
Proof. vm_refl. Qed.
Lemma D_7f92c : decode_any W_7f92c = Some (Branch BC_EQ 19 0 876, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f930 : bv 32 := 0x360f8463.
Lemma F_7f930 : fetch_word Ubsan.M.loaded_segments (0x7f930 : word) = Some W_7f930.
Proof. vm_refl. Qed.
Lemma D_7f930 : decode_any W_7f930 = Some (Branch BC_EQ 31 0 872, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f934 : bv 32 := 0x01c42023.
Lemma F_7f934 : fetch_word Ubsan.M.loaded_segments (0x7f934 : word) = Some W_7f934.
Proof. vm_refl. Qed.
Lemma D_7f934 : decode_any W_7f934 = Some (Store SZ4 8 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f938 : bv 32 := 0xfff90913.
Lemma F_7f938 : fetch_word Ubsan.M.loaded_segments (0x7f938 : word) = Some W_7f938.
Proof. vm_refl. Qed.
Lemma D_7f938 : decode_any W_7f938 = Some (OpImm ALU_ADD 18 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f93c : bv 32 := 0x00448493.
Lemma F_7f93c : fetch_word Ubsan.M.loaded_segments (0x7f93c : word) = Some W_7f93c.
Proof. vm_refl. Qed.
Lemma D_7f93c : decode_any W_7f93c = Some (OpImm ALU_ADD 9 9 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f940 : bv 32 := 0x00440413.
Lemma F_7f940 : fetch_word Ubsan.M.loaded_segments (0x7f940 : word) = Some W_7f940.
Proof. vm_refl. Qed.
Lemma D_7f940 : decode_any W_7f940 = Some (OpImm ALU_ADD 8 8 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f944 : bv 32 := 0xfc091ee3.
Lemma F_7f944 : fetch_word Ubsan.M.loaded_segments (0x7f944 : word) = Some W_7f944.
Proof. vm_refl. Qed.
Lemma D_7f944 : decode_any W_7f944 = Some (Branch BC_NE 18 0 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f948 : bv 32 := 0x01058f33.
Lemma F_7f948 : fetch_word Ubsan.M.loaded_segments (0x7f948 : word) = Some W_7f948.
Proof. vm_refl. Qed.
Lemma D_7f948 : decode_any W_7f948 = Some (Op ALU_ADD 30 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f94c : bv 32 := 0x01003fb3.
Lemma F_7f94c : fetch_word Ubsan.M.loaded_segments (0x7f94c : word) = Some W_7f94c.
Proof. vm_refl. Qed.
Lemma D_7f94c : decode_any W_7f94c = Some (Op ALU_SLTU 31 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f950 : bv 32 := 0x001f3413.
Lemma F_7f950 : fetch_word Ubsan.M.loaded_segments (0x7f950 : word) = Some W_7f950.
Proof. vm_refl. Qed.
Lemma D_7f950 : decode_any W_7f950 = Some (OpImm ALU_SLTU 8 30 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f954 : bv 32 := 0x348f8263.
Lemma F_7f954 : fetch_word Ubsan.M.loaded_segments (0x7f954 : word) = Some W_7f954.
Proof. vm_refl. Qed.
Lemma D_7f954 : decode_any W_7f954 = Some (Branch BC_EQ 31 8 836, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f958 : bv 32 := 0x010f3833.
Lemma F_7f958 : fetch_word Ubsan.M.loaded_segments (0x7f958 : word) = Some W_7f958.
Proof. vm_refl. Qed.
Lemma D_7f958 : decode_any W_7f958 = Some (Op ALU_SLTU 16 30 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f95c : bv 32 := 0x00e84833.
Lemma F_7f95c : fetch_word Ubsan.M.loaded_segments (0x7f95c : word) = Some W_7f95c.
Proof. vm_refl. Qed.
Lemma D_7f95c : decode_any W_7f95c = Some (Op ALU_XOR 16 16 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f960 : bv 32 := 0x00184813.
Lemma F_7f960 : fetch_word Ubsan.M.loaded_segments (0x7f960 : word) = Some W_7f960.
Proof. vm_refl. Qed.
Lemma D_7f960 : decode_any W_7f960 = Some (OpImm ALU_XOR 16 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f964 : bv 32 := 0x32080a63.
Lemma F_7f964 : fetch_word Ubsan.M.loaded_segments (0x7f964 : word) = Some W_7f964.
Proof. vm_refl. Qed.
Lemma D_7f964 : decode_any W_7f964 = Some (Branch BC_EQ 16 0 820, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f968 : bv 32 := 0x0012829b.
Lemma F_7f968 : fetch_word Ubsan.M.loaded_segments (0x7f968 : word) = Some W_7f968.
Proof. vm_refl. Qed.
Lemma D_7f968 : decode_any W_7f968 = Some (OpImm32 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f96c : bv 32 := 0x00be8eb3.
Lemma F_7f96c : fetch_word Ubsan.M.loaded_segments (0x7f96c : word) = Some W_7f96c.
Proof. vm_refl. Qed.
Lemma D_7f96c : decode_any W_7f96c = Some (Op ALU_ADD 29 29 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f970 : bv 32 := 0x000f0813.
Lemma F_7f970 : fetch_word Ubsan.M.loaded_segments (0x7f970 : word) = Some W_7f970.
Proof. vm_refl. Qed.
Lemma D_7f970 : decode_any W_7f970 = Some (OpImm ALU_ADD 16 30 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f974 : bv 32 := 0xf8c29ae3.
Lemma F_7f974 : fetch_word Ubsan.M.loaded_segments (0x7f974 : word) = Some W_7f974.
Proof. vm_refl. Qed.
Lemma D_7f974 : decode_any W_7f974 = Some (Branch BC_NE 5 12 8084, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f978 : bv 32 := 0x18089863.
Lemma F_7f978 : fetch_word Ubsan.M.loaded_segments (0x7f978 : word) = Some W_7f978.
Proof. vm_refl. Qed.
Lemma D_7f978 : decode_any W_7f978 = Some (Branch BC_NE 17 0 400, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f97c : bv 32 := 0x00357613.
Lemma F_7f97c : fetch_word Ubsan.M.loaded_segments (0x7f97c : word) = Some W_7f97c.
Proof. vm_refl. Qed.
Lemma D_7f97c : decode_any W_7f97c = Some (OpImm ALU_AND 12 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f980 : bv 32 := 0x30061c63.
Lemma F_7f980 : fetch_word Ubsan.M.loaded_segments (0x7f980 : word) = Some W_7f980.
Proof. vm_refl. Qed.
Lemma D_7f980 : decode_any W_7f980 = Some (Branch BC_NE 12 0 792, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f984 : bv 32 := 0x00050613.
Lemma F_7f984 : fetch_word Ubsan.M.loaded_segments (0x7f984 : word) = Some W_7f984.
Proof. vm_refl. Qed.
Lemma D_7f984 : decode_any W_7f984 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f988 : bv 32 := 0x30050863.
Lemma F_7f988 : fetch_word Ubsan.M.loaded_segments (0x7f988 : word) = Some W_7f988.
Proof. vm_refl. Qed.
Lemma D_7f988 : decode_any W_7f988 = Some (Branch BC_EQ 10 0 784, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f98c : bv 32 := 0x00052783.
Lemma F_7f98c : fetch_word Ubsan.M.loaded_segments (0x7f98c : word) = Some W_7f98c.
Proof. vm_refl. Qed.
Lemma D_7f98c : decode_any W_7f98c = Some (Load SZ4 true 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f990 : bv 32 := 0x00d7e833.
Lemma F_7f990 : fetch_word Ubsan.M.loaded_segments (0x7f990 : word) = Some W_7f990.
Proof. vm_refl. Qed.
Lemma D_7f990 : decode_any W_7f990 = Some (Op ALU_OR 16 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f994 : bv 32 := 0x00c587b3.
Lemma F_7f994 : fetch_word Ubsan.M.loaded_segments (0x7f994 : word) = Some W_7f994.
Proof. vm_refl. Qed.
Lemma D_7f994 : decode_any W_7f994 = Some (Op ALU_ADD 15 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f998 : bv 32 := 0x01052023.
Lemma F_7f998 : fetch_word Ubsan.M.loaded_segments (0x7f998 : word) = Some W_7f998.
Proof. vm_refl. Qed.
Lemma D_7f998 : decode_any W_7f998 = Some (Store SZ4 10 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f99c : bv 32 := 0x2e078e63.
Lemma F_7f99c : fetch_word Ubsan.M.loaded_segments (0x7f99c : word) = Some W_7f99c.
Proof. vm_refl. Qed.
Lemma D_7f99c : decode_any W_7f99c = Some (Branch BC_EQ 15 0 764, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9a0 : bv 32 := 0x00c7b633.
Lemma F_7f9a0 : fetch_word Ubsan.M.loaded_segments (0x7f9a0 : word) = Some W_7f9a0.
Proof. vm_refl. Qed.
Lemma D_7f9a0 : decode_any W_7f9a0 = Some (Op ALU_SLTU 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9a4 : bv 32 := 0x00e64633.
Lemma F_7f9a4 : fetch_word Ubsan.M.loaded_segments (0x7f9a4 : word) = Some W_7f9a4.
Proof. vm_refl. Qed.
Lemma D_7f9a4 : decode_any W_7f9a4 = Some (Op ALU_XOR 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9a8 : bv 32 := 0x00164613.
Lemma F_7f9a8 : fetch_word Ubsan.M.loaded_segments (0x7f9a8 : word) = Some W_7f9a8.
Proof. vm_refl. Qed.
Lemma D_7f9a8 : decode_any W_7f9a8 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9ac : bv 32 := 0x2e060663.
Lemma F_7f9ac : fetch_word Ubsan.M.loaded_segments (0x7f9ac : word) = Some W_7f9ac.
Proof. vm_refl. Qed.
Lemma D_7f9ac : decode_any W_7f9ac = Some (Branch BC_EQ 12 0 748, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9b0 : bv 32 := 0xfff3031b.
Lemma F_7f9b0 : fetch_word Ubsan.M.loaded_segments (0x7f9b0 : word) = Some W_7f9b0.
Proof. vm_refl. Qed.
Lemma D_7f9b0 : decode_any W_7f9b0 = Some (OpImm32 6 6 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9b4 : bv 32 := 0x00b50533.
Lemma F_7f9b4 : fetch_word Ubsan.M.loaded_segments (0x7f9b4 : word) = Some W_7f9b4.
Proof. vm_refl. Qed.
Lemma D_7f9b4 : decode_any W_7f9b4 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9b8 : bv 32 := 0x00078613.
Lemma F_7f9b8 : fetch_word Ubsan.M.loaded_segments (0x7f9b8 : word) = Some W_7f9b8.
Proof. vm_refl. Qed.
Lemma D_7f9b8 : decode_any W_7f9b8 = Some (OpImm ALU_ADD 12 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9bc : bv 32 := 0xfc0316e3.
Lemma F_7f9bc : fetch_word Ubsan.M.loaded_segments (0x7f9bc : word) = Some W_7f9bc.
Proof. vm_refl. Qed.
Lemma D_7f9bc : decode_any W_7f9bc = Some (Branch BC_NE 6 0 8140, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9c0 : bv 32 := 0x1480006f.
Lemma F_7f9c0 : fetch_word Ubsan.M.loaded_segments (0x7f9c0 : word) = Some W_7f9c0.
Proof. vm_refl. Qed.
Lemma D_7f9c0 : decode_any W_7f9c0 = Some (Jal 0 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9c4 : bv 32 := 0xfff97517.
Lemma F_7f9c4 : fetch_word Ubsan.M.loaded_segments (0x7f9c4 : word) = Some W_7f9c4.
Proof. vm_refl. Qed.
Lemma D_7f9c4 : decode_any W_7f9c4 = Some (Auipc 10 1048471, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9c8 : bv 32 := 0x03250513.
Lemma F_7f9c8 : fetch_word Ubsan.M.loaded_segments (0x7f9c8 : word) = Some W_7f9c8.
Proof. vm_refl. Qed.
Lemma D_7f9c8 : decode_any W_7f9c8 = Some (OpImm ALU_ADD 10 10 50, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9cc : bv 32 := 0x01813403.
Lemma F_7f9cc : fetch_word Ubsan.M.loaded_segments (0x7f9cc : word) = Some W_7f9cc.
Proof. vm_refl. Qed.
Lemma D_7f9cc : decode_any W_7f9cc = Some (Load SZ8 true 8 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9d0 : bv 32 := 0x01013483.
Lemma F_7f9d0 : fetch_word Ubsan.M.loaded_segments (0x7f9d0 : word) = Some W_7f9d0.
Proof. vm_refl. Qed.
Lemma D_7f9d0 : decode_any W_7f9d0 = Some (Load SZ8 true 9 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9d4 : bv 32 := 0x00813903.
Lemma F_7f9d4 : fetch_word Ubsan.M.loaded_segments (0x7f9d4 : word) = Some W_7f9d4.
Proof. vm_refl. Qed.
Lemma D_7f9d4 : decode_any W_7f9d4 = Some (Load SZ8 true 18 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9d8 : bv 32 := 0x00013983.
Lemma F_7f9d8 : fetch_word Ubsan.M.loaded_segments (0x7f9d8 : word) = Some W_7f9d8.
Proof. vm_refl. Qed.
Lemma D_7f9d8 : decode_any W_7f9d8 = Some (Load SZ8 true 19 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9dc : bv 32 := 0x02010113.
Lemma F_7f9dc : fetch_word Ubsan.M.loaded_segments (0x7f9dc : word) = Some W_7f9dc.
Proof. vm_refl. Qed.
Lemma D_7f9dc : decode_any W_7f9dc = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9e0 : bv 32 := 0xcc5e306f.
Lemma F_7f9e0 : fetch_word Ubsan.M.loaded_segments (0x7f9e0 : word) = Some W_7f9e0.
Proof. vm_refl. Qed.
Lemma D_7f9e0 : decode_any W_7f9e0 = Some (Jal 0 1981636, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9e4 : bv 32 := 0x0032f593.
Lemma F_7f9e4 : fetch_word Ubsan.M.loaded_segments (0x7f9e4 : word) = Some W_7f9e4.
Proof. vm_refl. Qed.
Lemma D_7f9e4 : decode_any W_7f9e4 = Some (OpImm ALU_AND 11 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9e8 : bv 32 := 0x2a059863.
Lemma F_7f9e8 : fetch_word Ubsan.M.loaded_segments (0x7f9e8 : word) = Some W_7f9e8.
Proof. vm_refl. Qed.
Lemma D_7f9e8 : decode_any W_7f9e8 = Some (Branch BC_NE 11 0 688, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9ec : bv 32 := 0x00271593.
Lemma F_7f9ec : fetch_word Ubsan.M.loaded_segments (0x7f9ec : word) = Some W_7f9ec.
Proof. vm_refl. Qed.
Lemma D_7f9ec : decode_any W_7f9ec = Some (ShiftImm ALU_SLL 11 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9f0 : bv 32 := 0x00072713.
Lemma F_7f9f0 : fetch_word Ubsan.M.loaded_segments (0x7f9f0 : word) = Some W_7f9f0.
Proof. vm_refl. Qed.
Lemma D_7f9f0 : decode_any W_7f9f0 = Some (OpImm ALU_SLT 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9f4 : bv 32 := 0x00028f13.
Lemma F_7f9f4 : fetch_word Ubsan.M.loaded_segments (0x7f9f4 : word) = Some W_7f9f4.
Proof. vm_refl. Qed.
Lemma D_7f9f4 : decode_any W_7f9f4 = Some (OpImm ALU_ADD 30 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9f8 : bv 32 := 0x00030e93.
Lemma F_7f9f8 : fetch_word Ubsan.M.loaded_segments (0x7f9f8 : word) = Some W_7f9f8.
Proof. vm_refl. Qed.
Lemma D_7f9f8 : decode_any W_7f9f8 = Some (OpImm ALU_ADD 29 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9fc : bv 32 := 0x28028e63.
Lemma F_7f9fc : fetch_word Ubsan.M.loaded_segments (0x7f9fc : word) = Some W_7f9fc.
Proof. vm_refl. Qed.
Lemma D_7f9fc : decode_any W_7f9fc = Some (Branch BC_EQ 5 0 668, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa00 : bv 32 := 0x0002af83.
Lemma F_7fa00 : fetch_word Ubsan.M.loaded_segments (0x7fa00 : word) = Some W_7fa00.
Proof. vm_refl. Qed.
Lemma D_7fa00 : decode_any W_7fa00 = Some (Load SZ4 true 31 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa04 : bv 32 := 0x007fc433.
Lemma F_7fa04 : fetch_word Ubsan.M.loaded_segments (0x7fa04 : word) = Some W_7fa04.
Proof. vm_refl. Qed.
Lemma D_7fa04 : decode_any W_7fa04 = Some (Op ALU_XOR 8 31 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa08 : bv 32 := 0x01e58fb3.
Lemma F_7fa08 : fetch_word Ubsan.M.loaded_segments (0x7fa08 : word) = Some W_7fa08.
Proof. vm_refl. Qed.
Lemma D_7fa08 : decode_any W_7fa08 = Some (Op ALU_ADD 31 11 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa0c : bv 32 := 0x0082a023.
Lemma F_7fa0c : fetch_word Ubsan.M.loaded_segments (0x7fa0c : word) = Some W_7fa0c.
Proof. vm_refl. Qed.
Lemma D_7fa0c : decode_any W_7fa0c = Some (Store SZ4 5 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa10 : bv 32 := 0x280f8463.
Lemma F_7fa10 : fetch_word Ubsan.M.loaded_segments (0x7fa10 : word) = Some W_7fa10.
Proof. vm_refl. Qed.
Lemma D_7fa10 : decode_any W_7fa10 = Some (Branch BC_EQ 31 0 648, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa14 : bv 32 := 0x01efbf33.
Lemma F_7fa14 : fetch_word Ubsan.M.loaded_segments (0x7fa14 : word) = Some W_7fa14.
Proof. vm_refl. Qed.
Lemma D_7fa14 : decode_any W_7fa14 = Some (Op ALU_SLTU 30 31 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa18 : bv 32 := 0x00ef4f33.
Lemma F_7fa18 : fetch_word Ubsan.M.loaded_segments (0x7fa18 : word) = Some W_7fa18.
Proof. vm_refl. Qed.
Lemma D_7fa18 : decode_any W_7fa18 = Some (Op ALU_XOR 30 30 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa1c : bv 32 := 0x001f4f13.
Lemma F_7fa1c : fetch_word Ubsan.M.loaded_segments (0x7fa1c : word) = Some W_7fa1c.
Proof. vm_refl. Qed.
Lemma D_7fa1c : decode_any W_7fa1c = Some (OpImm ALU_XOR 30 30 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa20 : bv 32 := 0x260f0c63.
Lemma F_7fa20 : fetch_word Ubsan.M.loaded_segments (0x7fa20 : word) = Some W_7fa20.
Proof. vm_refl. Qed.
Lemma D_7fa20 : decode_any W_7fa20 = Some (Branch BC_EQ 30 0 632, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa24 : bv 32 := 0xfffe8e9b.
Lemma F_7fa24 : fetch_word Ubsan.M.loaded_segments (0x7fa24 : word) = Some W_7fa24.
Proof. vm_refl. Qed.
Lemma D_7fa24 : decode_any W_7fa24 = Some (OpImm32 29 29 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa28 : bv 32 := 0x00b282b3.
Lemma F_7fa28 : fetch_word Ubsan.M.loaded_segments (0x7fa28 : word) = Some W_7fa28.
Proof. vm_refl. Qed.
Lemma D_7fa28 : decode_any W_7fa28 = Some (Op ALU_ADD 5 5 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa2c : bv 32 := 0x000f8f13.
Lemma F_7fa2c : fetch_word Ubsan.M.loaded_segments (0x7fa2c : word) = Some W_7fa2c.
Proof. vm_refl. Qed.
Lemma D_7fa2c : decode_any W_7fa2c = Some (OpImm ALU_ADD 30 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa30 : bv 32 := 0xfc0e96e3.
Lemma F_7fa30 : fetch_word Ubsan.M.loaded_segments (0x7fa30 : word) = Some W_7fa30.
Proof. vm_refl. Qed.
Lemma D_7fa30 : decode_any W_7fa30 = Some (Branch BC_NE 29 0 8140, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa34 : bv 32 := 0x080e1663.
Lemma F_7fa34 : fetch_word Ubsan.M.loaded_segments (0x7fa34 : word) = Some W_7fa34.
Proof. vm_refl. Qed.
Lemma D_7fa34 : decode_any W_7fa34 = Some (Branch BC_NE 28 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa38 : bv 32 := 0x00000293.
Lemma F_7fa38 : fetch_word Ubsan.M.loaded_segments (0x7fa38 : word) = Some W_7fa38.
Proof. vm_refl. Qed.
Lemma D_7fa38 : decode_any W_7fa38 = Some (OpImm ALU_ADD 5 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa3c : bv 32 := 0x00387393.
Lemma F_7fa3c : fetch_word Ubsan.M.loaded_segments (0x7fa3c : word) = Some W_7fa3c.
Proof. vm_refl. Qed.
Lemma D_7fa3c : decode_any W_7fa3c = Some (OpImm ALU_AND 7 16 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa40 : bv 32 := 0x0013b393.
Lemma F_7fa40 : fetch_word Ubsan.M.loaded_segments (0x7fa40 : word) = Some W_7fa40.
Proof. vm_refl. Qed.
Lemma D_7fa40 : decode_any W_7fa40 = Some (OpImm ALU_SLTU 7 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa44 : bv 32 := 0x00080e13.
Lemma F_7fa44 : fetch_word Ubsan.M.loaded_segments (0x7fa44 : word) = Some W_7fa44.
Proof. vm_refl. Qed.
Lemma D_7fa44 : decode_any W_7fa44 = Some (OpImm ALU_ADD 28 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa48 : bv 32 := 0x04078463.
Lemma F_7fa48 : fetch_word Ubsan.M.loaded_segments (0x7fa48 : word) = Some W_7fa48.
Proof. vm_refl. Qed.
Lemma D_7fa48 : decode_any W_7fa48 = Some (Branch BC_EQ 15 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa4c : bv 32 := 0x01003eb3.
Lemma F_7fa4c : fetch_word Ubsan.M.loaded_segments (0x7fa4c : word) = Some W_7fa4c.
Proof. vm_refl. Qed.
Lemma D_7fa4c : decode_any W_7fa4c = Some (Op ALU_SLTU 29 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa50 : bv 32 := 0x01d3ff33.
Lemma F_7fa50 : fetch_word Ubsan.M.loaded_segments (0x7fa50 : word) = Some W_7fa50.
Proof. vm_refl. Qed.
Lemma D_7fa50 : decode_any W_7fa50 = Some (Op ALU_AND 30 7 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa54 : bv 32 := 0x00080f93.
Lemma F_7fa54 : fetch_word Ubsan.M.loaded_segments (0x7fa54 : word) = Some W_7fa54.
Proof. vm_refl. Qed.
Lemma D_7fa54 : decode_any W_7fa54 = Some (OpImm ALU_ADD 31 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa58 : bv 32 := 0x000e0413.
Lemma F_7fa58 : fetch_word Ubsan.M.loaded_segments (0x7fa58 : word) = Some W_7fa58.
Proof. vm_refl. Qed.
Lemma D_7fa58 : decode_any W_7fa58 = Some (OpImm ALU_ADD 8 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa5c : bv 32 := 0x00078493.
Lemma F_7fa5c : fetch_word Ubsan.M.loaded_segments (0x7fa5c : word) = Some W_7fa5c.
Proof. vm_refl. Qed.
Lemma D_7fa5c : decode_any W_7fa5c = Some (OpImm ALU_ADD 9 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa60 : bv 32 := 0x23046c63.
Lemma F_7fa60 : fetch_word Ubsan.M.loaded_segments (0x7fa60 : word) = Some W_7fa60.
Proof. vm_refl. Qed.
Lemma D_7fa60 : decode_any W_7fa60 = Some (Branch BC_LTU 8 16 568, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa64 : bv 32 := 0x00143913.
Lemma F_7fa64 : fetch_word Ubsan.M.loaded_segments (0x7fa64 : word) = Some W_7fa64.
Proof. vm_refl. Qed.
Lemma D_7fa64 : decode_any W_7fa64 = Some (OpImm ALU_SLTU 18 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa68 : bv 32 := 0x012ec933.
Lemma F_7fa68 : fetch_word Ubsan.M.loaded_segments (0x7fa68 : word) = Some W_7fa68.
Proof. vm_refl. Qed.
Lemma D_7fa68 : decode_any W_7fa68 = Some (Op ALU_XOR 18 29 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa6c : bv 32 := 0x22090663.
Lemma F_7fa6c : fetch_word Ubsan.M.loaded_segments (0x7fa6c : word) = Some W_7fa6c.
Proof. vm_refl. Qed.
Lemma D_7fa6c : decode_any W_7fa6c = Some (Branch BC_EQ 18 0 556, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa70 : bv 32 := 0x220f0463.
Lemma F_7fa70 : fetch_word Ubsan.M.loaded_segments (0x7fa70 : word) = Some W_7fa70.
Proof. vm_refl. Qed.
Lemma D_7fa70 : decode_any W_7fa70 = Some (Branch BC_EQ 30 0 552, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa74 : bv 32 := 0x000fa903.
Lemma F_7fa74 : fetch_word Ubsan.M.loaded_segments (0x7fa74 : word) = Some W_7fa74.
Proof. vm_refl. Qed.
Lemma D_7fa74 : decode_any W_7fa74 = Some (Load SZ4 true 18 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa78 : bv 32 := 0xfff48493.
Lemma F_7fa78 : fetch_word Ubsan.M.loaded_segments (0x7fa78 : word) = Some W_7fa78.
Proof. vm_refl. Qed.
Lemma D_7fa78 : decode_any W_7fa78 = Some (OpImm ALU_ADD 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa7c : bv 32 := 0x00440413.
Lemma F_7fa7c : fetch_word Ubsan.M.loaded_segments (0x7fa7c : word) = Some W_7fa7c.
Proof. vm_refl. Qed.
Lemma D_7fa7c : decode_any W_7fa7c = Some (OpImm ALU_ADD 8 8 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa80 : bv 32 := 0xfff94913.
Lemma F_7fa80 : fetch_word Ubsan.M.loaded_segments (0x7fa80 : word) = Some W_7fa80.
Proof. vm_refl. Qed.
Lemma D_7fa80 : decode_any W_7fa80 = Some (OpImm ALU_XOR 18 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa84 : bv 32 := 0x012fa023.
Lemma F_7fa84 : fetch_word Ubsan.M.loaded_segments (0x7fa84 : word) = Some W_7fa84.
Proof. vm_refl. Qed.
Lemma D_7fa84 : decode_any W_7fa84 = Some (Store SZ4 31 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa88 : bv 32 := 0x004f8f93.
Lemma F_7fa88 : fetch_word Ubsan.M.loaded_segments (0x7fa88 : word) = Some W_7fa88.
Proof. vm_refl. Qed.
Lemma D_7fa88 : decode_any W_7fa88 = Some (OpImm ALU_ADD 31 31 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa8c : bv 32 := 0xfc049ae3.
Lemma F_7fa8c : fetch_word Ubsan.M.loaded_segments (0x7fa8c : word) = Some W_7fa8c.
Proof. vm_refl. Qed.
Lemma D_7fa8c : decode_any W_7fa8c = Some (Branch BC_NE 9 0 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa90 : bv 32 := 0x01058eb3.
Lemma F_7fa90 : fetch_word Ubsan.M.loaded_segments (0x7fa90 : word) = Some W_7fa90.
Proof. vm_refl. Qed.
Lemma D_7fa90 : decode_any W_7fa90 = Some (Op ALU_ADD 29 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa94 : bv 32 := 0x01003f33.
Lemma F_7fa94 : fetch_word Ubsan.M.loaded_segments (0x7fa94 : word) = Some W_7fa94.
Proof. vm_refl. Qed.
Lemma D_7fa94 : decode_any W_7fa94 = Some (Op ALU_SLTU 30 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa98 : bv 32 := 0x001ebf93.
Lemma F_7fa98 : fetch_word Ubsan.M.loaded_segments (0x7fa98 : word) = Some W_7fa98.
Proof. vm_refl. Qed.
Lemma D_7fa98 : decode_any W_7fa98 = Some (OpImm ALU_SLTU 31 29 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa9c : bv 32 := 0x1fff0e63.
Lemma F_7fa9c : fetch_word Ubsan.M.loaded_segments (0x7fa9c : word) = Some W_7fa9c.
Proof. vm_refl. Qed.
Lemma D_7fa9c : decode_any W_7fa9c = Some (Branch BC_EQ 30 31 508, 4%Z).
Proof. vm_refl. Qed.

Definition W_7faa0 : bv 32 := 0x010eb833.
Lemma F_7faa0 : fetch_word Ubsan.M.loaded_segments (0x7faa0 : word) = Some W_7faa0.
Proof. vm_refl. Qed.
Lemma D_7faa0 : decode_any W_7faa0 = Some (Op ALU_SLTU 16 29 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7faa4 : bv 32 := 0x00e84833.
Lemma F_7faa4 : fetch_word Ubsan.M.loaded_segments (0x7faa4 : word) = Some W_7faa4.
Proof. vm_refl. Qed.
Lemma D_7faa4 : decode_any W_7faa4 = Some (Op ALU_XOR 16 16 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_7faa8 : bv 32 := 0x00184813.
Lemma F_7faa8 : fetch_word Ubsan.M.loaded_segments (0x7faa8 : word) = Some W_7faa8.
Proof. vm_refl. Qed.
Lemma D_7faa8 : decode_any W_7faa8 = Some (OpImm ALU_XOR 16 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7faac : bv 32 := 0x1e080663.
Lemma F_7faac : fetch_word Ubsan.M.loaded_segments (0x7faac : word) = Some W_7faac.
Proof. vm_refl. Qed.
Lemma D_7faac : decode_any W_7faac = Some (Branch BC_EQ 16 0 492, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fab0 : bv 32 := 0x0012829b.
Lemma F_7fab0 : fetch_word Ubsan.M.loaded_segments (0x7fab0 : word) = Some W_7fab0.
Proof. vm_refl. Qed.
Lemma D_7fab0 : decode_any W_7fab0 = Some (OpImm32 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fab4 : bv 32 := 0x00be0e33.
Lemma F_7fab4 : fetch_word Ubsan.M.loaded_segments (0x7fab4 : word) = Some W_7fab4.
Proof. vm_refl. Qed.
Lemma D_7fab4 : decode_any W_7fab4 = Some (Op ALU_ADD 28 28 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fab8 : bv 32 := 0x000e8813.
Lemma F_7fab8 : fetch_word Ubsan.M.loaded_segments (0x7fab8 : word) = Some W_7fab8.
Proof. vm_refl. Qed.
Lemma D_7fab8 : decode_any W_7fab8 = Some (OpImm ALU_ADD 16 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fabc : bv 32 := 0xf8c296e3.
Lemma F_7fabc : fetch_word Ubsan.M.loaded_segments (0x7fabc : word) = Some W_7fabc.
Proof. vm_refl. Qed.
Lemma D_7fabc : decode_any W_7fabc = Some (Branch BC_NE 5 12 8076, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fac0 : bv 32 := 0x04089463.
Lemma F_7fac0 : fetch_word Ubsan.M.loaded_segments (0x7fac0 : word) = Some W_7fac0.
Proof. vm_refl. Qed.
Lemma D_7fac0 : decode_any W_7fac0 = Some (Branch BC_NE 17 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fac4 : bv 32 := 0x00357613.
Lemma F_7fac4 : fetch_word Ubsan.M.loaded_segments (0x7fac4 : word) = Some W_7fac4.
Proof. vm_refl. Qed.
Lemma D_7fac4 : decode_any W_7fac4 = Some (OpImm ALU_AND 12 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fac8 : bv 32 := 0x1c061863.
Lemma F_7fac8 : fetch_word Ubsan.M.loaded_segments (0x7fac8 : word) = Some W_7fac8.
Proof. vm_refl. Qed.
Lemma D_7fac8 : decode_any W_7fac8 = Some (Branch BC_NE 12 0 464, 4%Z).
Proof. vm_refl. Qed.

Definition W_7facc : bv 32 := 0x00050613.
Lemma F_7facc : fetch_word Ubsan.M.loaded_segments (0x7facc : word) = Some W_7facc.
Proof. vm_refl. Qed.
Lemma D_7facc : decode_any W_7facc = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fad0 : bv 32 := 0x1c050463.
Lemma F_7fad0 : fetch_word Ubsan.M.loaded_segments (0x7fad0 : word) = Some W_7fad0.
Proof. vm_refl. Qed.
Lemma D_7fad0 : decode_any W_7fad0 = Some (Branch BC_EQ 10 0 456, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fad4 : bv 32 := 0x00052783.
Lemma F_7fad4 : fetch_word Ubsan.M.loaded_segments (0x7fad4 : word) = Some W_7fad4.
Proof. vm_refl. Qed.
Lemma D_7fad4 : decode_any W_7fad4 = Some (Load SZ4 true 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fad8 : bv 32 := 0x00d7c833.
Lemma F_7fad8 : fetch_word Ubsan.M.loaded_segments (0x7fad8 : word) = Some W_7fad8.
Proof. vm_refl. Qed.
Lemma D_7fad8 : decode_any W_7fad8 = Some (Op ALU_XOR 16 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fadc : bv 32 := 0x00c587b3.
Lemma F_7fadc : fetch_word Ubsan.M.loaded_segments (0x7fadc : word) = Some W_7fadc.
Proof. vm_refl. Qed.
Lemma D_7fadc : decode_any W_7fadc = Some (Op ALU_ADD 15 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fae0 : bv 32 := 0x01052023.
Lemma F_7fae0 : fetch_word Ubsan.M.loaded_segments (0x7fae0 : word) = Some W_7fae0.
Proof. vm_refl. Qed.
Lemma D_7fae0 : decode_any W_7fae0 = Some (Store SZ4 10 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fae4 : bv 32 := 0x1a078a63.
Lemma F_7fae4 : fetch_word Ubsan.M.loaded_segments (0x7fae4 : word) = Some W_7fae4.
Proof. vm_refl. Qed.
Lemma D_7fae4 : decode_any W_7fae4 = Some (Branch BC_EQ 15 0 436, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fae8 : bv 32 := 0x00c7b633.
Lemma F_7fae8 : fetch_word Ubsan.M.loaded_segments (0x7fae8 : word) = Some W_7fae8.
Proof. vm_refl. Qed.
Lemma D_7fae8 : decode_any W_7fae8 = Some (Op ALU_SLTU 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7faec : bv 32 := 0x00e64633.
Lemma F_7faec : fetch_word Ubsan.M.loaded_segments (0x7faec : word) = Some W_7faec.
Proof. vm_refl. Qed.
Lemma D_7faec : decode_any W_7faec = Some (Op ALU_XOR 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_7faf0 : bv 32 := 0x00164613.
Lemma F_7faf0 : fetch_word Ubsan.M.loaded_segments (0x7faf0 : word) = Some W_7faf0.
Proof. vm_refl. Qed.
Lemma D_7faf0 : decode_any W_7faf0 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7faf4 : bv 32 := 0x1a060263.
Lemma F_7faf4 : fetch_word Ubsan.M.loaded_segments (0x7faf4 : word) = Some W_7faf4.
Proof. vm_refl. Qed.
Lemma D_7faf4 : decode_any W_7faf4 = Some (Branch BC_EQ 12 0 420, 4%Z).
Proof. vm_refl. Qed.

Definition W_7faf8 : bv 32 := 0xfff3031b.
Lemma F_7faf8 : fetch_word Ubsan.M.loaded_segments (0x7faf8 : word) = Some W_7faf8.
Proof. vm_refl. Qed.
Lemma D_7faf8 : decode_any W_7faf8 = Some (OpImm32 6 6 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fafc : bv 32 := 0x00b50533.
Lemma F_7fafc : fetch_word Ubsan.M.loaded_segments (0x7fafc : word) = Some W_7fafc.
Proof. vm_refl. Qed.
Lemma D_7fafc : decode_any W_7fafc = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb00 : bv 32 := 0x00078613.
Lemma F_7fb00 : fetch_word Ubsan.M.loaded_segments (0x7fb00 : word) = Some W_7fb00.
Proof. vm_refl. Qed.
Lemma D_7fb00 : decode_any W_7fb00 = Some (OpImm ALU_ADD 12 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb04 : bv 32 := 0xfc0316e3.
Lemma F_7fb04 : fetch_word Ubsan.M.loaded_segments (0x7fb04 : word) = Some W_7fb04.
Proof. vm_refl. Qed.
Lemma D_7fb04 : decode_any W_7fb04 = Some (Branch BC_NE 6 0 8140, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb08 : bv 32 := 0x01813403.
Lemma F_7fb08 : fetch_word Ubsan.M.loaded_segments (0x7fb08 : word) = Some W_7fb08.
Proof. vm_refl. Qed.
Lemma D_7fb08 : decode_any W_7fb08 = Some (Load SZ8 true 8 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb0c : bv 32 := 0x01013483.
Lemma F_7fb0c : fetch_word Ubsan.M.loaded_segments (0x7fb0c : word) = Some W_7fb0c.
Proof. vm_refl. Qed.
Lemma D_7fb0c : decode_any W_7fb0c = Some (Load SZ8 true 9 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb10 : bv 32 := 0x00813903.
Lemma F_7fb10 : fetch_word Ubsan.M.loaded_segments (0x7fb10 : word) = Some W_7fb10.
Proof. vm_refl. Qed.
Lemma D_7fb10 : decode_any W_7fb10 = Some (Load SZ8 true 18 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb14 : bv 32 := 0x00013983.
Lemma F_7fb14 : fetch_word Ubsan.M.loaded_segments (0x7fb14 : word) = Some W_7fb14.
Proof. vm_refl. Qed.
Lemma D_7fb14 : decode_any W_7fb14 = Some (Load SZ8 true 19 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb18 : bv 32 := 0x02010113.
Lemma F_7fb18 : fetch_word Ubsan.M.loaded_segments (0x7fb18 : word) = Some W_7fb18.
Proof. vm_refl. Qed.
Lemma D_7fb18 : decode_any W_7fb18 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb1c : bv 32 := 0x00008067.
Lemma F_7fb1c : fetch_word Ubsan.M.loaded_segments (0x7fb1c : word) = Some W_7fb1c.
Proof. vm_refl. Qed.
Lemma D_7fb1c : decode_any W_7fb1c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb20 : bv 32 := 0x00000593.
Lemma F_7fb20 : fetch_word Ubsan.M.loaded_segments (0x7fb20 : word) = Some W_7fb20.
Proof. vm_refl. Qed.
Lemma D_7fb20 : decode_any W_7fb20 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb24 : bv 32 := 0x00000393.
Lemma F_7fb24 : fetch_word Ubsan.M.loaded_segments (0x7fb24 : word) = Some W_7fb24.
Proof. vm_refl. Qed.
Lemma D_7fb24 : decode_any W_7fb24 = Some (OpImm ALU_ADD 7 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb28 : bv 32 := 0x00357e13.
Lemma F_7fb28 : fetch_word Ubsan.M.loaded_segments (0x7fb28 : word) = Some W_7fb28.
Proof. vm_refl. Qed.
Lemma D_7fb28 : decode_any W_7fb28 = Some (OpImm ALU_AND 28 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb2c : bv 32 := 0x01d50fb3.
Lemma F_7fb2c : fetch_word Ubsan.M.loaded_segments (0x7fb2c : word) = Some W_7fb2c.
Proof. vm_refl. Qed.
Lemma D_7fb2c : decode_any W_7fb2c = Some (Op ALU_ADD 31 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb30 : bv 32 := 0x02000513.
Lemma F_7fb30 : fetch_word Ubsan.M.loaded_segments (0x7fb30 : word) = Some W_7fb30.
Proof. vm_refl. Qed.
Lemma D_7fb30 : decode_any W_7fb30 = Some (OpImm ALU_ADD 10 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb34 : bv 32 := 0x00500e93.
Lemma F_7fb34 : fetch_word Ubsan.M.loaded_segments (0x7fb34 : word) = Some W_7fb34.
Proof. vm_refl. Qed.
Lemma D_7fb34 : decode_any W_7fb34 = Some (OpImm ALU_ADD 29 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb38 : bv 32 := 0x01ef8f33.
Lemma F_7fb38 : fetch_word Ubsan.M.loaded_segments (0x7fb38 : word) = Some W_7fb38.
Proof. vm_refl. Qed.
Lemma D_7fb38 : decode_any W_7fb38 = Some (Op ALU_ADD 30 31 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb3c : bv 32 := 0xfff00f93.
Lemma F_7fb3c : fetch_word Ubsan.M.loaded_segments (0x7fb3c : word) = Some W_7fb3c.
Proof. vm_refl. Qed.
Lemma D_7fb3c : decode_any W_7fb3c = Some (OpImm ALU_ADD 31 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb40 : bv 32 := 0x0100006f.
Lemma F_7fb40 : fetch_word Ubsan.M.loaded_segments (0x7fb40 : word) = Some W_7fb40.
Proof. vm_refl. Qed.
Lemma D_7fb40 : decode_any W_7fb40 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb44 : bv 32 := 0x0013839b.
Lemma F_7fb44 : fetch_word Ubsan.M.loaded_segments (0x7fb44 : word) = Some W_7fb44.
Proof. vm_refl. Qed.
Lemma D_7fb44 : decode_any W_7fb44 = Some (OpImm32 7 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb48 : bv 32 := 0x00e585bb.
Lemma F_7fb48 : fetch_word Ubsan.M.loaded_segments (0x7fb48 : word) = Some W_7fb48.
Proof. vm_refl. Qed.
Lemma D_7fb48 : decode_any W_7fb48 = Some (Op32 ALU_ADD 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb4c : bv 32 := 0xfac38ee3.
Lemma F_7fb4c : fetch_word Ubsan.M.loaded_segments (0x7fb4c : word) = Some W_7fb4c.
Proof. vm_refl. Qed.
Lemma D_7fb4c : decode_any W_7fb4c = Some (Branch BC_EQ 7 12 8124, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb50 : bv 32 := 0x02e384b3.
Lemma F_7fb50 : fetch_word Ubsan.M.loaded_segments (0x7fb50 : word) = Some W_7fb50.
Proof. vm_refl. Qed.
Lemma D_7fb50 : decode_any W_7fb50 = Some (Mul M_MUL 9 7 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb54 : bv 32 := 0x02e3843b.
Lemma F_7fb54 : fetch_word Ubsan.M.loaded_segments (0x7fb54 : word) = Some W_7fb54.
Proof. vm_refl. Qed.
Lemma D_7fb54 : decode_any W_7fb54 = Some (Mul32 M_MUL 8 7 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb58 : bv 32 := 0x14941063.
Lemma F_7fb58 : fetch_word Ubsan.M.loaded_segments (0x7fb58 : word) = Some W_7fb58.
Proof. vm_refl. Qed.
Lemma D_7fb58 : decode_any W_7fb58 = Some (Branch BC_NE 8 9 320, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb5c : bv 32 := 0x0004849b.
Lemma F_7fb5c : fetch_word Ubsan.M.loaded_segments (0x7fb5c : word) = Some W_7fb5c.
Proof. vm_refl. Qed.
Lemma D_7fb5c : decode_any W_7fb5c = Some (OpImm32 9 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb60 : bv 32 := 0x00249413.
Lemma F_7fb60 : fetch_word Ubsan.M.loaded_segments (0x7fb60 : word) = Some W_7fb60.
Proof. vm_refl. Qed.
Lemma D_7fb60 : decode_any W_7fb60 = Some (ShiftImm ALU_SLL 8 9 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb64 : bv 32 := 0x00540433.
Lemma F_7fb64 : fetch_word Ubsan.M.loaded_segments (0x7fb64 : word) = Some W_7fb64.
Proof. vm_refl. Qed.
Lemma D_7fb64 : decode_any W_7fb64 = Some (Op ALU_ADD 8 8 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb68 : bv 32 := 0x00143913.
Lemma F_7fb68 : fetch_word Ubsan.M.loaded_segments (0x7fb68 : word) = Some W_7fb68.
Proof. vm_refl. Qed.
Lemma D_7fb68 : decode_any W_7fb68 = Some (OpImm ALU_SLTU 18 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb6c : bv 32 := 0x13280663.
Lemma F_7fb6c : fetch_word Ubsan.M.loaded_segments (0x7fb6c : word) = Some W_7fb6c.
Proof. vm_refl. Qed.
Lemma D_7fb6c : decode_any W_7fb6c = Some (Branch BC_EQ 16 18 300, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb70 : bv 32 := 0x00543933.
Lemma F_7fb70 : fetch_word Ubsan.M.loaded_segments (0x7fb70 : word) = Some W_7fb70.
Proof. vm_refl. Qed.
Lemma D_7fb70 : decode_any W_7fb70 = Some (Op ALU_SLTU 18 8 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb74 : bv 32 := 0x0004a493.
Lemma F_7fb74 : fetch_word Ubsan.M.loaded_segments (0x7fb74 : word) = Some W_7fb74.
Proof. vm_refl. Qed.
Lemma D_7fb74 : decode_any W_7fb74 = Some (OpImm ALU_SLT 9 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb78 : bv 32 := 0x009944b3.
Lemma F_7fb78 : fetch_word Ubsan.M.loaded_segments (0x7fb78 : word) = Some W_7fb78.
Proof. vm_refl. Qed.
Lemma D_7fb78 : decode_any W_7fb78 = Some (Op ALU_XOR 9 18 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb7c : bv 32 := 0x0014c493.
Lemma F_7fb7c : fetch_word Ubsan.M.loaded_segments (0x7fb7c : word) = Some W_7fb7c.
Proof. vm_refl. Qed.
Lemma D_7fb7c : decode_any W_7fb7c = Some (OpImm ALU_XOR 9 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb80 : bv 32 := 0x10048c63.
Lemma F_7fb80 : fetch_word Ubsan.M.loaded_segments (0x7fb80 : word) = Some W_7fb80.
Proof. vm_refl. Qed.
Lemma D_7fb80 : decode_any W_7fb80 = Some (Branch BC_EQ 9 0 280, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb84 : bv 32 := 0x00a6f663.
Lemma F_7fb84 : fetch_word Ubsan.M.loaded_segments (0x7fb84 : word) = Some W_7fb84.
Proof. vm_refl. Qed.
Lemma D_7fb84 : decode_any W_7fb84 = Some (Branch BC_GEU 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb88 : bv 32 := 0x00040993.
Lemma F_7fb88 : fetch_word Ubsan.M.loaded_segments (0x7fb88 : word) = Some W_7fb88.
Proof. vm_refl. Qed.
Lemma D_7fb88 : decode_any W_7fb88 = Some (OpImm ALU_ADD 19 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb8c : bv 32 := 0x0340006f.
Lemma F_7fb8c : fetch_word Ubsan.M.loaded_segments (0x7fb8c : word) = Some W_7fb8c.
Proof. vm_refl. Qed.
Lemma D_7fb8c : decode_any W_7fb8c = Some (Jal 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb90 : bv 32 := 0x00259493.
Lemma F_7fb90 : fetch_word Ubsan.M.loaded_segments (0x7fb90 : word) = Some W_7fb90.
Proof. vm_refl. Qed.
Lemma D_7fb90 : decode_any W_7fb90 = Some (ShiftImm ALU_SLL 9 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb94 : bv 32 := 0x009f04b3.
Lemma F_7fb94 : fetch_word Ubsan.M.loaded_segments (0x7fb94 : word) = Some W_7fb94.
Proof. vm_refl. Qed.
Lemma D_7fb94 : decode_any W_7fb94 = Some (Op ALU_ADD 9 30 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb98 : bv 32 := 0x00088913.
Lemma F_7fb98 : fetch_word Ubsan.M.loaded_segments (0x7fb98 : word) = Some W_7fb98.
Proof. vm_refl. Qed.
Lemma D_7fb98 : decode_any W_7fb98 = Some (OpImm ALU_ADD 18 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb9c : bv 32 := 0x00448493.
Lemma F_7fb9c : fetch_word Ubsan.M.loaded_segments (0x7fb9c : word) = Some W_7fb9c.
Proof. vm_refl. Qed.
Lemma D_7fb9c : decode_any W_7fb9c = Some (OpImm ALU_ADD 9 9 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fba0 : bv 32 := 0x0fd4ec63.
Lemma F_7fba0 : fetch_word Ubsan.M.loaded_segments (0x7fba0 : word) = Some W_7fba0.
Proof. vm_refl. Qed.
Lemma D_7fba0 : decode_any W_7fba0 = Some (Branch BC_LTU 9 29 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fba4 : bv 32 := 0x0e040a63.
Lemma F_7fba4 : fetch_word Ubsan.M.loaded_segments (0x7fba4 : word) = Some W_7fba4.
Proof. vm_refl. Qed.
Lemma D_7fba4 : decode_any W_7fba4 = Some (Branch BC_EQ 8 0 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fba8 : bv 32 := 0x0e0e1863.
Lemma F_7fba8 : fetch_word Ubsan.M.loaded_segments (0x7fba8 : word) = Some W_7fba8.
Proof. vm_refl. Qed.
Lemma D_7fba8 : decode_any W_7fba8 = Some (Branch BC_NE 28 0 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbac : bv 32 := 0x00440993.
Lemma F_7fbac : fetch_word Ubsan.M.loaded_segments (0x7fbac : word) = Some W_7fbac.
Proof. vm_refl. Qed.
Lemma D_7fbac : decode_any W_7fbac = Some (OpImm ALU_ADD 19 8 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbb0 : bv 32 := 0xfff9091b.
Lemma F_7fbb0 : fetch_word Ubsan.M.loaded_segments (0x7fbb0 : word) = Some W_7fbb0.
Proof. vm_refl. Qed.
Lemma D_7fbb0 : decode_any W_7fbb0 = Some (OpImm32 18 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbb4 : bv 32 := 0x01f42023.
Lemma F_7fbb4 : fetch_word Ubsan.M.loaded_segments (0x7fbb4 : word) = Some W_7fbb4.
Proof. vm_refl. Qed.
Lemma D_7fbb4 : decode_any W_7fbb4 = Some (Store SZ4 8 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbb8 : bv 32 := 0x00098413.
Lemma F_7fbb8 : fetch_word Ubsan.M.loaded_segments (0x7fbb8 : word) = Some W_7fbb8.
Proof. vm_refl. Qed.
Lemma D_7fbb8 : decode_any W_7fbb8 = Some (OpImm ALU_ADD 8 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbbc : bv 32 := 0xfe0910e3.
Lemma F_7fbbc : fetch_word Ubsan.M.loaded_segments (0x7fbbc : word) = Some W_7fbbc.
Proof. vm_refl. Qed.
Lemma D_7fbbc : decode_any W_7fbbc = Some (Branch BC_NE 18 0 8160, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbc0 : bv 32 := 0xf80782e3.
Lemma F_7fbc0 : fetch_word Ubsan.M.loaded_segments (0x7fbc0 : word) = Some W_7fbc0.
Proof. vm_refl. Qed.
Lemma D_7fbc0 : decode_any W_7fbc0 = Some (Branch BC_EQ 15 0 8068, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbc4 : bv 32 := 0x0c098a63.
Lemma F_7fbc4 : fetch_word Ubsan.M.loaded_segments (0x7fbc4 : word) = Some W_7fbc4.
Proof. vm_refl. Qed.
Lemma D_7fbc4 : decode_any W_7fbc4 = Some (Branch BC_EQ 19 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbc8 : bv 32 := 0x0039f413.
Lemma F_7fbc8 : fetch_word Ubsan.M.loaded_segments (0x7fbc8 : word) = Some W_7fbc8.
Proof. vm_refl. Qed.
Lemma D_7fbc8 : decode_any W_7fbc8 = Some (OpImm ALU_AND 8 19 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbcc : bv 32 := 0x0c041663.
Lemma F_7fbcc : fetch_word Ubsan.M.loaded_segments (0x7fbcc : word) = Some W_7fbcc.
Proof. vm_refl. Qed.
Lemma D_7fbcc : decode_any W_7fbcc = Some (Branch BC_NE 8 0 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbd0 : bv 32 := 0x0009a403.
Lemma F_7fbd0 : fetch_word Ubsan.M.loaded_segments (0x7fbd0 : word) = Some W_7fbd0.
Proof. vm_refl. Qed.
Lemma D_7fbd0 : decode_any W_7fbd0 = Some (Load SZ4 true 8 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbd4 : bv 32 := 0x00646433.
Lemma F_7fbd4 : fetch_word Ubsan.M.loaded_segments (0x7fbd4 : word) = Some W_7fbd4.
Proof. vm_refl. Qed.
Lemma D_7fbd4 : decode_any W_7fbd4 = Some (Op ALU_OR 8 8 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbd8 : bv 32 := 0x0089a023.
Lemma F_7fbd8 : fetch_word Ubsan.M.loaded_segments (0x7fbd8 : word) = Some W_7fbd8.
Proof. vm_refl. Qed.
Lemma D_7fbd8 : decode_any W_7fbd8 = Some (Store SZ4 19 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbdc : bv 32 := 0xf69ff06f.
Lemma F_7fbdc : fetch_word Ubsan.M.loaded_segments (0x7fbdc : word) = Some W_7fbdc.
Proof. vm_refl. Qed.
Lemma D_7fbdc : decode_any W_7fbdc = Some (Jal 0 2097000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbe0 : bv 32 := 0x00000393.
Lemma F_7fbe0 : fetch_word Ubsan.M.loaded_segments (0x7fbe0 : word) = Some W_7fbe0.
Proof. vm_refl. Qed.
Lemma D_7fbe0 : decode_any W_7fbe0 = Some (OpImm ALU_ADD 7 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbe4 : bv 32 := 0xfff34313.
Lemma F_7fbe4 : fetch_word Ubsan.M.loaded_segments (0x7fbe4 : word) = Some W_7fbe4.
Proof. vm_refl. Qed.
Lemma D_7fbe4 : decode_any W_7fbe4 = Some (OpImm ALU_XOR 6 6 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbe8 : bv 32 := 0x00357e13.
Lemma F_7fbe8 : fetch_word Ubsan.M.loaded_segments (0x7fbe8 : word) = Some W_7fbe8.
Proof. vm_refl. Qed.
Lemma D_7fbe8 : decode_any W_7fbe8 = Some (OpImm ALU_AND 28 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbec : bv 32 := 0x01d50eb3.
Lemma F_7fbec : fetch_word Ubsan.M.loaded_segments (0x7fbec : word) = Some W_7fbec.
Proof. vm_refl. Qed.
Lemma D_7fbec : decode_any W_7fbec = Some (Op ALU_ADD 29 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbf0 : bv 32 := 0x02000513.
Lemma F_7fbf0 : fetch_word Ubsan.M.loaded_segments (0x7fbf0 : word) = Some W_7fbf0.
Proof. vm_refl. Qed.
Lemma D_7fbf0 : decode_any W_7fbf0 = Some (OpImm ALU_ADD 10 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbf4 : bv 32 := 0x01ee8eb3.
Lemma F_7fbf4 : fetch_word Ubsan.M.loaded_segments (0x7fbf4 : word) = Some W_7fbf4.
Proof. vm_refl. Qed.
Lemma D_7fbf4 : decode_any W_7fbf4 = Some (Op ALU_ADD 29 29 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbf8 : bv 32 := 0x00500f13.
Lemma F_7fbf8 : fetch_word Ubsan.M.loaded_segments (0x7fbf8 : word) = Some W_7fbf8.
Proof. vm_refl. Qed.
Lemma D_7fbf8 : decode_any W_7fbf8 = Some (OpImm ALU_ADD 30 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbfc : bv 32 := 0x01c0006f.
Lemma F_7fbfc : fetch_word Ubsan.M.loaded_segments (0x7fbfc : word) = Some W_7fbfc.
Proof. vm_refl. Qed.
Lemma D_7fbfc : decode_any W_7fbfc = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc00 : bv 32 := 0x00092f83.
Lemma F_7fc00 : fetch_word Ubsan.M.loaded_segments (0x7fc00 : word) = Some W_7fc00.
Proof. vm_refl. Qed.
Lemma D_7fc00 : decode_any W_7fc00 = Some (Load SZ4 true 31 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc04 : bv 32 := 0x006fffb3.
Lemma F_7fc04 : fetch_word Ubsan.M.loaded_segments (0x7fc04 : word) = Some W_7fc04.
Proof. vm_refl. Qed.
Lemma D_7fc04 : decode_any W_7fc04 = Some (Op ALU_AND 31 31 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc08 : bv 32 := 0x01f92023.
Lemma F_7fc08 : fetch_word Ubsan.M.loaded_segments (0x7fc08 : word) = Some W_7fc08.
Proof. vm_refl. Qed.
Lemma D_7fc08 : decode_any W_7fc08 = Some (Store SZ4 18 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc0c : bv 32 := 0x0013839b.
Lemma F_7fc0c : fetch_word Ubsan.M.loaded_segments (0x7fc0c : word) = Some W_7fc0c.
Proof. vm_refl. Qed.
Lemma D_7fc0c : decode_any W_7fc0c = Some (OpImm32 7 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc10 : bv 32 := 0x00e585bb.
Lemma F_7fc10 : fetch_word Ubsan.M.loaded_segments (0x7fc10 : word) = Some W_7fc10.
Proof. vm_refl. Qed.
Lemma D_7fc10 : decode_any W_7fc10 = Some (Op32 ALU_ADD 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc14 : bv 32 := 0xeec38ae3.
Lemma F_7fc14 : fetch_word Ubsan.M.loaded_segments (0x7fc14 : word) = Some W_7fc14.
Proof. vm_refl. Qed.
Lemma D_7fc14 : decode_any W_7fc14 = Some (Branch BC_EQ 7 12 7924, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc18 : bv 32 := 0x02e38433.
Lemma F_7fc18 : fetch_word Ubsan.M.loaded_segments (0x7fc18 : word) = Some W_7fc18.
Proof. vm_refl. Qed.
Lemma D_7fc18 : decode_any W_7fc18 = Some (Mul M_MUL 8 7 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc1c : bv 32 := 0x02e38fbb.
Lemma F_7fc1c : fetch_word Ubsan.M.loaded_segments (0x7fc1c : word) = Some W_7fc1c.
Proof. vm_refl. Qed.
Lemma D_7fc1c : decode_any W_7fc1c = Some (Mul32 M_MUL 31 7 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc20 : bv 32 := 0x068f9c63.
Lemma F_7fc20 : fetch_word Ubsan.M.loaded_segments (0x7fc20 : word) = Some W_7fc20.
Proof. vm_refl. Qed.
Lemma D_7fc20 : decode_any W_7fc20 = Some (Branch BC_NE 31 8 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc24 : bv 32 := 0x0004041b.
Lemma F_7fc24 : fetch_word Ubsan.M.loaded_segments (0x7fc24 : word) = Some W_7fc24.
Proof. vm_refl. Qed.
Lemma D_7fc24 : decode_any W_7fc24 = Some (OpImm32 8 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc28 : bv 32 := 0x00241f93.
Lemma F_7fc28 : fetch_word Ubsan.M.loaded_segments (0x7fc28 : word) = Some W_7fc28.
Proof. vm_refl. Qed.
Lemma D_7fc28 : decode_any W_7fc28 = Some (ShiftImm ALU_SLL 31 8 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc2c : bv 32 := 0x005f8fb3.
Lemma F_7fc2c : fetch_word Ubsan.M.loaded_segments (0x7fc2c : word) = Some W_7fc2c.
Proof. vm_refl. Qed.
Lemma D_7fc2c : decode_any W_7fc2c = Some (Op ALU_ADD 31 31 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc30 : bv 32 := 0x001fb493.
Lemma F_7fc30 : fetch_word Ubsan.M.loaded_segments (0x7fc30 : word) = Some W_7fc30.
Proof. vm_refl. Qed.
Lemma D_7fc30 : decode_any W_7fc30 = Some (OpImm ALU_SLTU 9 31 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc34 : bv 32 := 0x06980263.
Lemma F_7fc34 : fetch_word Ubsan.M.loaded_segments (0x7fc34 : word) = Some W_7fc34.
Proof. vm_refl. Qed.
Lemma D_7fc34 : decode_any W_7fc34 = Some (Branch BC_EQ 16 9 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc38 : bv 32 := 0x005fb4b3.
Lemma F_7fc38 : fetch_word Ubsan.M.loaded_segments (0x7fc38 : word) = Some W_7fc38.
Proof. vm_refl. Qed.
Lemma D_7fc38 : decode_any W_7fc38 = Some (Op ALU_SLTU 9 31 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc3c : bv 32 := 0x00042413.
Lemma F_7fc3c : fetch_word Ubsan.M.loaded_segments (0x7fc3c : word) = Some W_7fc3c.
Proof. vm_refl. Qed.
Lemma D_7fc3c : decode_any W_7fc3c = Some (OpImm ALU_SLT 8 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc40 : bv 32 := 0x0084c433.
Lemma F_7fc40 : fetch_word Ubsan.M.loaded_segments (0x7fc40 : word) = Some W_7fc40.
Proof. vm_refl. Qed.
Lemma D_7fc40 : decode_any W_7fc40 = Some (Op ALU_XOR 8 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc44 : bv 32 := 0x00144413.
Lemma F_7fc44 : fetch_word Ubsan.M.loaded_segments (0x7fc44 : word) = Some W_7fc44.
Proof. vm_refl. Qed.
Lemma D_7fc44 : decode_any W_7fc44 = Some (OpImm ALU_XOR 8 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc48 : bv 32 := 0x04040863.
Lemma F_7fc48 : fetch_word Ubsan.M.loaded_segments (0x7fc48 : word) = Some W_7fc48.
Proof. vm_refl. Qed.
Lemma D_7fc48 : decode_any W_7fc48 = Some (Branch BC_EQ 8 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc4c : bv 32 := 0x00a6f663.
Lemma F_7fc4c : fetch_word Ubsan.M.loaded_segments (0x7fc4c : word) = Some W_7fc4c.
Proof. vm_refl. Qed.
Lemma D_7fc4c : decode_any W_7fc4c = Some (Branch BC_GEU 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc50 : bv 32 := 0x000f8913.
Lemma F_7fc50 : fetch_word Ubsan.M.loaded_segments (0x7fc50 : word) = Some W_7fc50.
Proof. vm_refl. Qed.
Lemma D_7fc50 : decode_any W_7fc50 = Some (OpImm ALU_ADD 18 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc54 : bv 32 := 0x0340006f.
Lemma F_7fc54 : fetch_word Ubsan.M.loaded_segments (0x7fc54 : word) = Some W_7fc54.
Proof. vm_refl. Qed.
Lemma D_7fc54 : decode_any W_7fc54 = Some (Jal 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc58 : bv 32 := 0x00259413.
Lemma F_7fc58 : fetch_word Ubsan.M.loaded_segments (0x7fc58 : word) = Some W_7fc58.
Proof. vm_refl. Qed.
Lemma D_7fc58 : decode_any W_7fc58 = Some (ShiftImm ALU_SLL 8 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc5c : bv 32 := 0x008e8433.
Lemma F_7fc5c : fetch_word Ubsan.M.loaded_segments (0x7fc5c : word) = Some W_7fc5c.
Proof. vm_refl. Qed.
Lemma D_7fc5c : decode_any W_7fc5c = Some (Op ALU_ADD 8 29 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc60 : bv 32 := 0x00088493.
Lemma F_7fc60 : fetch_word Ubsan.M.loaded_segments (0x7fc60 : word) = Some W_7fc60.
Proof. vm_refl. Qed.
Lemma D_7fc60 : decode_any W_7fc60 = Some (OpImm ALU_ADD 9 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc64 : bv 32 := 0x00440413.
Lemma F_7fc64 : fetch_word Ubsan.M.loaded_segments (0x7fc64 : word) = Some W_7fc64.
Proof. vm_refl. Qed.
Lemma D_7fc64 : decode_any W_7fc64 = Some (OpImm ALU_ADD 8 8 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc68 : bv 32 := 0x03e46863.
Lemma F_7fc68 : fetch_word Ubsan.M.loaded_segments (0x7fc68 : word) = Some W_7fc68.
Proof. vm_refl. Qed.
Lemma D_7fc68 : decode_any W_7fc68 = Some (Branch BC_LTU 8 30 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc6c : bv 32 := 0x020f8663.
Lemma F_7fc6c : fetch_word Ubsan.M.loaded_segments (0x7fc6c : word) = Some W_7fc6c.
Proof. vm_refl. Qed.
Lemma D_7fc6c : decode_any W_7fc6c = Some (Branch BC_EQ 31 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc70 : bv 32 := 0x020e1463.
Lemma F_7fc70 : fetch_word Ubsan.M.loaded_segments (0x7fc70 : word) = Some W_7fc70.
Proof. vm_refl. Qed.
Lemma D_7fc70 : decode_any W_7fc70 = Some (Branch BC_NE 28 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc74 : bv 32 := 0x004f8913.
Lemma F_7fc74 : fetch_word Ubsan.M.loaded_segments (0x7fc74 : word) = Some W_7fc74.
Proof. vm_refl. Qed.
Lemma D_7fc74 : decode_any W_7fc74 = Some (OpImm ALU_ADD 18 31 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc78 : bv 32 := 0xfff4849b.
Lemma F_7fc78 : fetch_word Ubsan.M.loaded_segments (0x7fc78 : word) = Some W_7fc78.
Proof. vm_refl. Qed.
Lemma D_7fc78 : decode_any W_7fc78 = Some (OpImm32 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc7c : bv 32 := 0x000fa023.
Lemma F_7fc7c : fetch_word Ubsan.M.loaded_segments (0x7fc7c : word) = Some W_7fc7c.
Proof. vm_refl. Qed.
Lemma D_7fc7c : decode_any W_7fc7c = Some (Store SZ4 31 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc80 : bv 32 := 0x00090f93.
Lemma F_7fc80 : fetch_word Ubsan.M.loaded_segments (0x7fc80 : word) = Some W_7fc80.
Proof. vm_refl. Qed.
Lemma D_7fc80 : decode_any W_7fc80 = Some (OpImm ALU_ADD 31 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc84 : bv 32 := 0xfe0490e3.
Lemma F_7fc84 : fetch_word Ubsan.M.loaded_segments (0x7fc84 : word) = Some W_7fc84.
Proof. vm_refl. Qed.
Lemma D_7fc84 : decode_any W_7fc84 = Some (Branch BC_NE 9 0 8160, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc88 : bv 32 := 0xf80782e3.
Lemma F_7fc88 : fetch_word Ubsan.M.loaded_segments (0x7fc88 : word) = Some W_7fc88.
Proof. vm_refl. Qed.
Lemma D_7fc88 : decode_any W_7fc88 = Some (Branch BC_EQ 15 0 8068, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc8c : bv 32 := 0x00090663.
Lemma F_7fc8c : fetch_word Ubsan.M.loaded_segments (0x7fc8c : word) = Some W_7fc8c.
Proof. vm_refl. Qed.
Lemma D_7fc8c : decode_any W_7fc8c = Some (Branch BC_EQ 18 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc90 : bv 32 := 0x00397f93.
Lemma F_7fc90 : fetch_word Ubsan.M.loaded_segments (0x7fc90 : word) = Some W_7fc90.
Proof. vm_refl. Qed.
Lemma D_7fc90 : decode_any W_7fc90 = Some (OpImm ALU_AND 31 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc94 : bv 32 := 0xf60f86e3.
Lemma F_7fc94 : fetch_word Ubsan.M.loaded_segments (0x7fc94 : word) = Some W_7fc94.
Proof. vm_refl. Qed.
Lemma D_7fc94 : decode_any W_7fc94 = Some (Branch BC_EQ 31 0 8044, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc98 : bv 32 := 0xc0001073.
Lemma F_7fc98 : fetch_word Ubsan.M.loaded_segments (0x7fc98 : word) = Some W_7fc98.
Proof. vm_refl. Qed.
Lemma D_7fc98 : decode_any W_7fc98 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.

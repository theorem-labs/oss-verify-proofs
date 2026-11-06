(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_6d928 : bv 32 := 0x00050663.
Lemma F_6d928 : fetch_word Plain.M.loaded_segments (0x6d980 : word) = Some W_6d928.
Proof. vm_refl. Qed.
Lemma D_6d928 : decode_any W_6d928 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d92c : bv 32 := 0x00852503.
Lemma F_6d92c : fetch_word Plain.M.loaded_segments (0x6d984 : word) = Some W_6d92c.
Proof. vm_refl. Qed.
Lemma D_6d92c : decode_any W_6d92c = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d930 : bv 32 := 0x00008067.
Lemma F_6d930 : fetch_word Plain.M.loaded_segments (0x6d988 : word) = Some W_6d930.
Proof. vm_refl. Qed.
Lemma D_6d930 : decode_any W_6d930 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3e4 : bv 32 := 0xf1010113.
Lemma F_9b3e4 : fetch_word Plain.M.loaded_segments (0x9b43c : word) = Some W_9b3e4.
Proof. vm_refl. Qed.
Lemma D_9b3e4 : decode_any W_9b3e4 = Some (OpImm ALU_ADD 2 2 3856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3e8 : bv 32 := 0x0e113423.
Lemma F_9b3e8 : fetch_word Plain.M.loaded_segments (0x9b440 : word) = Some W_9b3e8.
Proof. vm_refl. Qed.
Lemma D_9b3e8 : decode_any W_9b3e8 = Some (Store SZ8 2 1 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3ec : bv 32 := 0x0e813023.
Lemma F_9b3ec : fetch_word Plain.M.loaded_segments (0x9b444 : word) = Some W_9b3ec.
Proof. vm_refl. Qed.
Lemma D_9b3ec : decode_any W_9b3ec = Some (Store SZ8 2 8 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3f0 : bv 32 := 0x0c913c23.
Lemma F_9b3f0 : fetch_word Plain.M.loaded_segments (0x9b448 : word) = Some W_9b3f0.
Proof. vm_refl. Qed.
Lemma D_9b3f0 : decode_any W_9b3f0 = Some (Store SZ8 2 9 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3f4 : bv 32 := 0x0d213823.
Lemma F_9b3f4 : fetch_word Plain.M.loaded_segments (0x9b44c : word) = Some W_9b3f4.
Proof. vm_refl. Qed.
Lemma D_9b3f4 : decode_any W_9b3f4 = Some (Store SZ8 2 18 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3f8 : bv 32 := 0x0d313423.
Lemma F_9b3f8 : fetch_word Plain.M.loaded_segments (0x9b450 : word) = Some W_9b3f8.
Proof. vm_refl. Qed.
Lemma D_9b3f8 : decode_any W_9b3f8 = Some (Store SZ8 2 19 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3fc : bv 32 := 0x0d413023.
Lemma F_9b3fc : fetch_word Plain.M.loaded_segments (0x9b454 : word) = Some W_9b3fc.
Proof. vm_refl. Qed.
Lemma D_9b3fc : decode_any W_9b3fc = Some (Store SZ8 2 20 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b400 : bv 32 := 0x0b513c23.
Lemma F_9b400 : fetch_word Plain.M.loaded_segments (0x9b458 : word) = Some W_9b400.
Proof. vm_refl. Qed.
Lemma D_9b400 : decode_any W_9b400 = Some (Store SZ8 2 21 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b404 : bv 32 := 0x0b613823.
Lemma F_9b404 : fetch_word Plain.M.loaded_segments (0x9b45c : word) = Some W_9b404.
Proof. vm_refl. Qed.
Lemma D_9b404 : decode_any W_9b404 = Some (Store SZ8 2 22 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b408 : bv 32 := 0x0b713423.
Lemma F_9b408 : fetch_word Plain.M.loaded_segments (0x9b460 : word) = Some W_9b408.
Proof. vm_refl. Qed.
Lemma D_9b408 : decode_any W_9b408 = Some (Store SZ8 2 23 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b40c : bv 32 := 0x0b813023.
Lemma F_9b40c : fetch_word Plain.M.loaded_segments (0x9b464 : word) = Some W_9b40c.
Proof. vm_refl. Qed.
Lemma D_9b40c : decode_any W_9b40c = Some (Store SZ8 2 24 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b410 : bv 32 := 0x09913c23.
Lemma F_9b410 : fetch_word Plain.M.loaded_segments (0x9b468 : word) = Some W_9b410.
Proof. vm_refl. Qed.
Lemma D_9b410 : decode_any W_9b410 = Some (Store SZ8 2 25 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b414 : bv 32 := 0x09a13823.
Lemma F_9b414 : fetch_word Plain.M.loaded_segments (0x9b46c : word) = Some W_9b414.
Proof. vm_refl. Qed.
Lemma D_9b414 : decode_any W_9b414 = Some (Store SZ8 2 26 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b418 : bv 32 := 0x09b13423.
Lemma F_9b418 : fetch_word Plain.M.loaded_segments (0x9b470 : word) = Some W_9b418.
Proof. vm_refl. Qed.
Lemma D_9b418 : decode_any W_9b418 = Some (Store SZ8 2 27 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b41c : bv 32 := 0x08813027.
Lemma F_9b41c : fetch_word Plain.M.loaded_segments (0x9b474 : word) = Some W_9b41c.
Proof. vm_refl. Qed.
Lemma D_9b41c : decode_any W_9b41c = Some (FStore FMT_D 2 8 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b420 : bv 32 := 0x06913c27.
Lemma F_9b420 : fetch_word Plain.M.loaded_segments (0x9b478 : word) = Some W_9b420.
Proof. vm_refl. Qed.
Lemma D_9b420 : decode_any W_9b420 = Some (FStore FMT_D 2 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b424 : bv 32 := 0x20058463.
Lemma F_9b424 : fetch_word Plain.M.loaded_segments (0x9b47c : word) = Some W_9b424.
Proof. vm_refl. Qed.
Lemma D_9b424 : decode_any W_9b424 = Some (Branch BC_EQ 11 0 520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b428 : bv 32 := 0x00058413.
Lemma F_9b428 : fetch_word Plain.M.loaded_segments (0x9b480 : word) = Some W_9b428.
Proof. vm_refl. Qed.
Lemma D_9b428 : decode_any W_9b428 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b42c : bv 32 := 0x00050993.
Lemma F_9b42c : fetch_word Plain.M.loaded_segments (0x9b484 : word) = Some W_9b42c.
Proof. vm_refl. Qed.
Lemma D_9b42c : decode_any W_9b42c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b430 : bv 32 := 0x0005a023.
Lemma F_9b430 : fetch_word Plain.M.loaded_segments (0x9b488 : word) = Some W_9b430.
Proof. vm_refl. Qed.
Lemma D_9b430 : decode_any W_9b430 = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b434 : bv 32 := 0x1c050863.
Lemma F_9b434 : fetch_word Plain.M.loaded_segments (0x9b48c : word) = Some W_9b434.
Proof. vm_refl. Qed.
Lemma D_9b434 : decode_any W_9b434 = Some (Branch BC_EQ 10 0 464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b438 : bv 32 := 0x00070493.
Lemma F_9b438 : fetch_word Plain.M.loaded_segments (0x9b490 : word) = Some W_9b438.
Proof. vm_refl. Qed.
Lemma D_9b438 : decode_any W_9b438 = Some (OpImm ALU_ADD 9 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b43c : bv 32 := 0x00068d13.
Lemma F_9b43c : fetch_word Plain.M.loaded_segments (0x9b494 : word) = Some W_9b43c.
Proof. vm_refl. Qed.
Lemma D_9b43c : decode_any W_9b43c = Some (OpImm ALU_ADD 26 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b440 : bv 32 := 0x00060913.
Lemma F_9b440 : fetch_word Plain.M.loaded_segments (0x9b498 : word) = Some W_9b440.
Proof. vm_refl. Qed.
Lemma D_9b440 : decode_any W_9b440 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b444 : bv 32 := 0x00098513.
Lemma F_9b444 : fetch_word Plain.M.loaded_segments (0x9b49c : word) = Some W_9b444.
Proof. vm_refl. Qed.
Lemma D_9b444 : decode_any W_9b444 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b448 : bv 32 := 0xce0d20ef.
Lemma F_9b448 : fetch_word Plain.M.loaded_segments (0x9b4a0 : word) = Some W_9b448.
Proof. vm_refl. Qed.
Lemma D_9b448 : decode_any W_9b448 = Some (Jal 1 1909984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b44c : bv 32 := 0x00100593.
Lemma F_9b44c : fetch_word Plain.M.loaded_segments (0x9b4a4 : word) = Some W_9b44c.
Proof. vm_refl. Qed.
Lemma D_9b44c : decode_any W_9b44c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b450 : bv 32 := 0x1ab51a63.
Lemma F_9b450 : fetch_word Plain.M.loaded_segments (0x9b4a8 : word) = Some W_9b450.
Proof. vm_refl. Qed.
Lemma D_9b450 : decode_any W_9b450 = Some (Branch BC_NE 10 11 436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b454 : bv 32 := 0x00091463.
Lemma F_9b454 : fetch_word Plain.M.loaded_segments (0x9b4ac : word) = Some W_9b454.
Proof. vm_refl. Qed.
Lemma D_9b454 : decode_any W_9b454 = Some (Branch BC_NE 18 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b458 : bv 32 := 0x04600913.
Lemma F_9b458 : fetch_word Plain.M.loaded_segments (0x9b4b0 : word) = Some W_9b458.
Proof. vm_refl. Qed.
Lemma D_9b458 : decode_any W_9b458 = Some (OpImm ALU_ADD 18 0 70, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b45c : bv 32 := 0x00048863.
Lemma F_9b45c : fetch_word Plain.M.loaded_segments (0x9b4b4 : word) = Some W_9b45c.
Proof. vm_refl. Qed.
Lemma D_9b45c : decode_any W_9b45c = Some (Branch BC_EQ 9 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b46c : bv 32 := 0xfff83517.
Lemma F_9b46c : fetch_word Plain.M.loaded_segments (0x9b4c4 : word) = Some W_9b46c.
Proof. vm_refl. Qed.
Lemma D_9b46c : decode_any W_9b46c = Some (Auipc 10 1048451, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b470 : bv 32 := 0x00500593.
Lemma F_9b470 : fetch_word Plain.M.loaded_segments (0x9b4c8 : word) = Some W_9b470.
Proof. vm_refl. Qed.
Lemma D_9b470 : decode_any W_9b470 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b474 : bv 32 := 0x1e850513.
Lemma F_9b474 : fetch_word Plain.M.loaded_segments (0x9b4cc : word) = Some W_9b474.
Proof. vm_refl. Qed.
Lemma D_9b474 : decode_any W_9b474 = Some (OpImm ALU_ADD 10 10 488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b478 : bv 32 := 0x00600613.
Lemma F_9b478 : fetch_word Plain.M.loaded_segments (0x9b4d0 : word) = Some W_9b478.
Proof. vm_refl. Qed.
Lemma D_9b478 : decode_any W_9b478 = Some (OpImm ALU_ADD 12 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b47c : bv 32 := 0x00000693.
Lemma F_9b47c : fetch_word Plain.M.loaded_segments (0x9b4d4 : word) = Some W_9b47c.
Proof. vm_refl. Qed.
Lemma D_9b47c : decode_any W_9b47c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b480 : bv 32 := 0x891f70ef.
Lemma F_9b480 : fetch_word Plain.M.loaded_segments (0x9b4d8 : word) = Some W_9b480.
Proof. vm_refl. Qed.
Lemma D_9b480 : decode_any W_9b480 = Some (Jal 1 2062480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b484 : bv 32 := 0x00050c13.
Lemma F_9b484 : fetch_word Plain.M.loaded_segments (0x9b4dc : word) = Some W_9b484.
Proof. vm_refl. Qed.
Lemma D_9b484 : decode_any W_9b484 = Some (OpImm ALU_ADD 24 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b488 : bv 32 := 0x04a13023.
Lemma F_9b488 : fetch_word Plain.M.loaded_segments (0x9b4e0 : word) = Some W_9b488.
Proof. vm_refl. Qed.
Lemma D_9b488 : decode_any W_9b488 = Some (Store SZ8 2 10 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b48c : bv 32 := 0xfff75517.
Lemma F_9b48c : fetch_word Plain.M.loaded_segments (0x9b4e4 : word) = Some W_9b48c.
Proof. vm_refl. Qed.
Lemma D_9b48c : decode_any W_9b48c = Some (Auipc 10 1048437, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b490 : bv 32 := 0x00500593.
Lemma F_9b490 : fetch_word Plain.M.loaded_segments (0x9b4e8 : word) = Some W_9b490.
Proof. vm_refl. Qed.
Lemma D_9b490 : decode_any W_9b490 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b494 : bv 32 := 0x73450513.
Lemma F_9b494 : fetch_word Plain.M.loaded_segments (0x9b4ec : word) = Some W_9b494.
Proof. vm_refl. Qed.
Lemma D_9b494 : decode_any W_9b494 = Some (OpImm ALU_ADD 10 10 1844, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b498 : bv 32 := 0x00600613.
Lemma F_9b498 : fetch_word Plain.M.loaded_segments (0x9b4f0 : word) = Some W_9b498.
Proof. vm_refl. Qed.
Lemma D_9b498 : decode_any W_9b498 = Some (OpImm ALU_ADD 12 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b49c : bv 32 := 0x00000693.
Lemma F_9b49c : fetch_word Plain.M.loaded_segments (0x9b4f4 : word) = Some W_9b49c.
Proof. vm_refl. Qed.
Lemma D_9b49c : decode_any W_9b49c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4a0 : bv 32 := 0x871f70ef.
Lemma F_9b4a0 : fetch_word Plain.M.loaded_segments (0x9b4f8 : word) = Some W_9b4a0.
Proof. vm_refl. Qed.
Lemma D_9b4a0 : decode_any W_9b4a0 = Some (Jal 1 2062448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4a4 : bv 32 := 0x00050c93.
Lemma F_9b4a4 : fetch_word Plain.M.loaded_segments (0x9b4fc : word) = Some W_9b4a4.
Proof. vm_refl. Qed.
Lemma D_9b4a4 : decode_any W_9b4a4 = Some (OpImm ALU_ADD 25 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4a8 : bv 32 := 0x02a13c23.
Lemma F_9b4a8 : fetch_word Plain.M.loaded_segments (0x9b500 : word) = Some W_9b4a8.
Proof. vm_refl. Qed.
Lemma D_9b4a8 : decode_any W_9b4a8 = Some (Store SZ8 2 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4ac : bv 32 := 0xfff78517.
Lemma F_9b4ac : fetch_word Plain.M.loaded_segments (0x9b504 : word) = Some W_9b4ac.
Proof. vm_refl. Qed.
Lemma D_9b4ac : decode_any W_9b4ac = Some (Auipc 10 1048440, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4b0 : bv 32 := 0x00500593.
Lemma F_9b4b0 : fetch_word Plain.M.loaded_segments (0x9b508 : word) = Some W_9b4b0.
Proof. vm_refl. Qed.
Lemma D_9b4b0 : decode_any W_9b4b0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4b4 : bv 32 := 0xb2c50513.
Lemma F_9b4b4 : fetch_word Plain.M.loaded_segments (0x9b50c : word) = Some W_9b4b4.
Proof. vm_refl. Qed.
Lemma D_9b4b4 : decode_any W_9b4b4 = Some (OpImm ALU_ADD 10 10 2860, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4b8 : bv 32 := 0x00600613.
Lemma F_9b4b8 : fetch_word Plain.M.loaded_segments (0x9b510 : word) = Some W_9b4b8.
Proof. vm_refl. Qed.
Lemma D_9b4b8 : decode_any W_9b4b8 = Some (OpImm ALU_ADD 12 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4bc : bv 32 := 0x00000693.
Lemma F_9b4bc : fetch_word Plain.M.loaded_segments (0x9b514 : word) = Some W_9b4bc.
Proof. vm_refl. Qed.
Lemma D_9b4bc : decode_any W_9b4bc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4c0 : bv 32 := 0x851f70ef.
Lemma F_9b4c0 : fetch_word Plain.M.loaded_segments (0x9b518 : word) = Some W_9b4c0.
Proof. vm_refl. Qed.
Lemma D_9b4c0 : decode_any W_9b4c0 = Some (Jal 1 2062416, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4c4 : bv 32 := 0x00050a93.
Lemma F_9b4c4 : fetch_word Plain.M.loaded_segments (0x9b51c : word) = Some W_9b4c4.
Proof. vm_refl. Qed.
Lemma D_9b4c4 : decode_any W_9b4c4 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4c8 : bv 32 := 0x02a13823.
Lemma F_9b4c8 : fetch_word Plain.M.loaded_segments (0x9b520 : word) = Some W_9b4c8.
Proof. vm_refl. Qed.
Lemma D_9b4c8 : decode_any W_9b4c8 = Some (Store SZ8 2 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4cc : bv 32 := 0xfff7c517.
Lemma F_9b4cc : fetch_word Plain.M.loaded_segments (0x9b524 : word) = Some W_9b4cc.
Proof. vm_refl. Qed.
Lemma D_9b4cc : decode_any W_9b4cc = Some (Auipc 10 1048444, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4d0 : bv 32 := 0x00500593.
Lemma F_9b4d0 : fetch_word Plain.M.loaded_segments (0x9b528 : word) = Some W_9b4d0.
Proof. vm_refl. Qed.
Lemma D_9b4d0 : decode_any W_9b4d0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4d4 : bv 32 := 0xd4150513.
Lemma F_9b4d4 : fetch_word Plain.M.loaded_segments (0x9b52c : word) = Some W_9b4d4.
Proof. vm_refl. Qed.
Lemma D_9b4d4 : decode_any W_9b4d4 = Some (OpImm ALU_ADD 10 10 3393, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4d8 : bv 32 := 0x00600613.
Lemma F_9b4d8 : fetch_word Plain.M.loaded_segments (0x9b530 : word) = Some W_9b4d8.
Proof. vm_refl. Qed.
Lemma D_9b4d8 : decode_any W_9b4d8 = Some (OpImm ALU_ADD 12 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4dc : bv 32 := 0x00000693.
Lemma F_9b4dc : fetch_word Plain.M.loaded_segments (0x9b534 : word) = Some W_9b4dc.
Proof. vm_refl. Qed.
Lemma D_9b4dc : decode_any W_9b4dc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4e0 : bv 32 := 0x831f70ef.
Lemma F_9b4e0 : fetch_word Plain.M.loaded_segments (0x9b538 : word) = Some W_9b4e0.
Proof. vm_refl. Qed.
Lemma D_9b4e0 : decode_any W_9b4e0 = Some (Jal 1 2062384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4e4 : bv 32 := 0x00050b13.
Lemma F_9b4e4 : fetch_word Plain.M.loaded_segments (0x9b53c : word) = Some W_9b4e4.
Proof. vm_refl. Qed.
Lemma D_9b4e4 : decode_any W_9b4e4 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4e8 : bv 32 := 0x02a13423.
Lemma F_9b4e8 : fetch_word Plain.M.loaded_segments (0x9b540 : word) = Some W_9b4e8.
Proof. vm_refl. Qed.
Lemma D_9b4e8 : decode_any W_9b4e8 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4ec : bv 32 := 0xfff7d517.
Lemma F_9b4ec : fetch_word Plain.M.loaded_segments (0x9b544 : word) = Some W_9b4ec.
Proof. vm_refl. Qed.
Lemma D_9b4ec : decode_any W_9b4ec = Some (Auipc 10 1048445, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4f0 : bv 32 := 0xa0350593.
Lemma F_9b4f0 : fetch_word Plain.M.loaded_segments (0x9b548 : word) = Some W_9b4f0.
Proof. vm_refl. Qed.
Lemma D_9b4f0 : decode_any W_9b4f0 = Some (OpImm ALU_ADD 11 10 2563, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4f4 : bv 32 := 0x00098513.
Lemma F_9b4f4 : fetch_word Plain.M.loaded_segments (0x9b54c : word) = Some W_9b4f4.
Proof. vm_refl. Qed.
Lemma D_9b4f4 : decode_any W_9b4f4 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4f8 : bv 32 := 0x00000613.
Lemma F_9b4f8 : fetch_word Plain.M.loaded_segments (0x9b550 : word) = Some W_9b4f8.
Proof. vm_refl. Qed.
Lemma D_9b4f8 : decode_any W_9b4f8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b4fc : bv 32 := 0xbe0f80ef.
Lemma F_9b4fc : fetch_word Plain.M.loaded_segments (0x9b554 : word) = Some W_9b4fc.
Proof. vm_refl. Qed.
Lemma D_9b4fc : decode_any W_9b4fc = Some (Jal 1 2065376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b500 : bv 32 := 0x00050b93.
Lemma F_9b500 : fetch_word Plain.M.loaded_segments (0x9b558 : word) = Some W_9b500.
Proof. vm_refl. Qed.
Lemma D_9b500 : decode_any W_9b500 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b504 : bv 32 := 0x06a13423.
Lemma F_9b504 : fetch_word Plain.M.loaded_segments (0x9b55c : word) = Some W_9b504.
Proof. vm_refl. Qed.
Lemma D_9b504 : decode_any W_9b504 = Some (Store SZ8 2 10 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b508 : bv 32 := 0x04013423.
Lemma F_9b508 : fetch_word Plain.M.loaded_segments (0x9b560 : word) = Some W_9b508.
Proof. vm_refl. Qed.
Lemma D_9b508 : decode_any W_9b508 = Some (Store SZ8 2 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b50c : bv 32 := 0x1ba05663.
Lemma F_9b50c : fetch_word Plain.M.loaded_segments (0x9b564 : word) = Some W_9b50c.
Proof. vm_refl. Qed.
Lemma D_9b50c : decode_any W_9b50c = Some (Branch BC_GE 0 26 428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b604 : bv 32 := 0x00077517.
Lemma F_9b604 : fetch_word Plain.M.loaded_segments (0x9b65c : word) = Some W_9b604.
Proof. vm_refl. Qed.
Lemma D_9b604 : decode_any W_9b604 = Some (Auipc 10 119, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b608 : bv 32 := 0xf6c53503.
Lemma F_9b608 : fetch_word Plain.M.loaded_segments (0x9b660 : word) = Some W_9b608.
Proof. vm_refl. Qed.
Lemma D_9b608 : decode_any W_9b608 = Some (Load SZ8 true 10 10 3948, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b60c : bv 32 := 0x00052503.
Lemma F_9b60c : fetch_word Plain.M.loaded_segments (0x9b664 : word) = Some W_9b60c.
Proof. vm_refl. Qed.
Lemma D_9b60c : decode_any W_9b60c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b610 : bv 32 := 0x00500593.
Lemma F_9b610 : fetch_word Plain.M.loaded_segments (0x9b668 : word) = Some W_9b610.
Proof. vm_refl. Qed.
Lemma D_9b610 : decode_any W_9b610 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b614 : bv 32 := 0x08a5c263.
Lemma F_9b614 : fetch_word Plain.M.loaded_segments (0x9b66c : word) = Some W_9b614.
Proof. vm_refl. Qed.
Lemma D_9b614 : decode_any W_9b614 = Some (Branch BC_LT 11 10 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b618 : bv 32 := 0xfff76517.
Lemma F_9b618 : fetch_word Plain.M.loaded_segments (0x9b670 : word) = Some W_9b618.
Proof. vm_refl. Qed.
Lemma D_9b618 : decode_any W_9b618 = Some (Auipc 10 1048438, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b61c : bv 32 := 0xfff81597.
Lemma F_9b61c : fetch_word Plain.M.loaded_segments (0x9b674 : word) = Some W_9b61c.
Proof. vm_refl. Qed.
Lemma D_9b61c : decode_any W_9b61c = Some (Auipc 11 1048449, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b620 : bv 32 := 0x22d50513.
Lemma F_9b620 : fetch_word Plain.M.loaded_segments (0x9b678 : word) = Some W_9b620.
Proof. vm_refl. Qed.
Lemma D_9b620 : decode_any W_9b620 = Some (OpImm ALU_ADD 10 10 557, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b624 : bv 32 := 0x40c58593.
Lemma F_9b624 : fetch_word Plain.M.loaded_segments (0x9b67c : word) = Some W_9b624.
Proof. vm_refl. Qed.
Lemma D_9b624 : decode_any W_9b624 = Some (OpImm ALU_ADD 11 11 1036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b628 : bv 32 := 0x0280006f.
Lemma F_9b628 : fetch_word Plain.M.loaded_segments (0x9b680 : word) = Some W_9b628.
Proof. vm_refl. Qed.
Lemma D_9b628 : decode_any W_9b628 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b650 : bv 32 := 0x00100613.
Lemma F_9b650 : fetch_word Plain.M.loaded_segments (0x9b6a8 : word) = Some W_9b650.
Proof. vm_refl. Qed.
Lemma D_9b650 : decode_any W_9b650 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b654 : bv 32 := 0x0e813083.
Lemma F_9b654 : fetch_word Plain.M.loaded_segments (0x9b6ac : word) = Some W_9b654.
Proof. vm_refl. Qed.
Lemma D_9b654 : decode_any W_9b654 = Some (Load SZ8 true 1 2 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b658 : bv 32 := 0x0e013403.
Lemma F_9b658 : fetch_word Plain.M.loaded_segments (0x9b6b0 : word) = Some W_9b658.
Proof. vm_refl. Qed.
Lemma D_9b658 : decode_any W_9b658 = Some (Load SZ8 true 8 2 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b65c : bv 32 := 0x0d813483.
Lemma F_9b65c : fetch_word Plain.M.loaded_segments (0x9b6b4 : word) = Some W_9b65c.
Proof. vm_refl. Qed.
Lemma D_9b65c : decode_any W_9b65c = Some (Load SZ8 true 9 2 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b660 : bv 32 := 0x0d013903.
Lemma F_9b660 : fetch_word Plain.M.loaded_segments (0x9b6b8 : word) = Some W_9b660.
Proof. vm_refl. Qed.
Lemma D_9b660 : decode_any W_9b660 = Some (Load SZ8 true 18 2 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b664 : bv 32 := 0x0c813983.
Lemma F_9b664 : fetch_word Plain.M.loaded_segments (0x9b6bc : word) = Some W_9b664.
Proof. vm_refl. Qed.
Lemma D_9b664 : decode_any W_9b664 = Some (Load SZ8 true 19 2 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b668 : bv 32 := 0x0c013a03.
Lemma F_9b668 : fetch_word Plain.M.loaded_segments (0x9b6c0 : word) = Some W_9b668.
Proof. vm_refl. Qed.
Lemma D_9b668 : decode_any W_9b668 = Some (Load SZ8 true 20 2 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b66c : bv 32 := 0x0b813a83.
Lemma F_9b66c : fetch_word Plain.M.loaded_segments (0x9b6c4 : word) = Some W_9b66c.
Proof. vm_refl. Qed.
Lemma D_9b66c : decode_any W_9b66c = Some (Load SZ8 true 21 2 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b670 : bv 32 := 0x0b013b03.
Lemma F_9b670 : fetch_word Plain.M.loaded_segments (0x9b6c8 : word) = Some W_9b670.
Proof. vm_refl. Qed.
Lemma D_9b670 : decode_any W_9b670 = Some (Load SZ8 true 22 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b674 : bv 32 := 0x0a813b83.
Lemma F_9b674 : fetch_word Plain.M.loaded_segments (0x9b6cc : word) = Some W_9b674.
Proof. vm_refl. Qed.
Lemma D_9b674 : decode_any W_9b674 = Some (Load SZ8 true 23 2 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b678 : bv 32 := 0x0a013c03.
Lemma F_9b678 : fetch_word Plain.M.loaded_segments (0x9b6d0 : word) = Some W_9b678.
Proof. vm_refl. Qed.
Lemma D_9b678 : decode_any W_9b678 = Some (Load SZ8 true 24 2 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b67c : bv 32 := 0x09813c83.
Lemma F_9b67c : fetch_word Plain.M.loaded_segments (0x9b6d4 : word) = Some W_9b67c.
Proof. vm_refl. Qed.
Lemma D_9b67c : decode_any W_9b67c = Some (Load SZ8 true 25 2 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b680 : bv 32 := 0x09013d03.
Lemma F_9b680 : fetch_word Plain.M.loaded_segments (0x9b6d8 : word) = Some W_9b680.
Proof. vm_refl. Qed.
Lemma D_9b680 : decode_any W_9b680 = Some (Load SZ8 true 26 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b684 : bv 32 := 0x08813d83.
Lemma F_9b684 : fetch_word Plain.M.loaded_segments (0x9b6dc : word) = Some W_9b684.
Proof. vm_refl. Qed.
Lemma D_9b684 : decode_any W_9b684 = Some (Load SZ8 true 27 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b688 : bv 32 := 0x08013407.
Lemma F_9b688 : fetch_word Plain.M.loaded_segments (0x9b6e0 : word) = Some W_9b688.
Proof. vm_refl. Qed.
Lemma D_9b688 : decode_any W_9b688 = Some (FLoad FMT_D 8 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b68c : bv 32 := 0x07813487.
Lemma F_9b68c : fetch_word Plain.M.loaded_segments (0x9b6e4 : word) = Some W_9b68c.
Proof. vm_refl. Qed.
Lemma D_9b68c : decode_any W_9b68c = Some (FLoad FMT_D 9 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b690 : bv 32 := 0x0f010113.
Lemma F_9b690 : fetch_word Plain.M.loaded_segments (0x9b6e8 : word) = Some W_9b690.
Proof. vm_refl. Qed.
Lemma D_9b690 : decode_any W_9b690 = Some (OpImm ALU_ADD 2 2 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b694 : bv 32 := 0x961c706f.
Lemma F_9b694 : fetch_word Plain.M.loaded_segments (0x9b6ec : word) = Some W_9b694.
Proof. vm_refl. Qed.
Lemma D_9b694 : decode_any W_9b694 = Some (Jal 0 1866080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b6b8 : bv 32 := 0x00000a13.
Lemma F_9b6b8 : fetch_word Plain.M.loaded_segments (0x9b710 : word) = Some W_9b6b8.
Proof. vm_refl. Qed.
Lemma D_9b6b8 : decode_any W_9b6b8 = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b6bc : bv 32 := 0x00000513.
Lemma F_9b6bc : fetch_word Plain.M.loaded_segments (0x9b714 : word) = Some W_9b6bc.
Proof. vm_refl. Qed.
Lemma D_9b6bc : decode_any W_9b6bc = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b6c0 : bv 32 := 0x000b8593.
Lemma F_9b6c0 : fetch_word Plain.M.loaded_segments (0x9b718 : word) = Some W_9b6c0.
Proof. vm_refl. Qed.
Lemma D_9b6c0 : decode_any W_9b6c0 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b6c4 : bv 32 := 0x000c0613.
Lemma F_9b6c4 : fetch_word Plain.M.loaded_segments (0x9b71c : word) = Some W_9b6c4.
Proof. vm_refl. Qed.
Lemma D_9b6c4 : decode_any W_9b6c4 = Some (OpImm ALU_ADD 12 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b6c8 : bv 32 := 0xc2cf40ef.
Lemma F_9b6c8 : fetch_word Plain.M.loaded_segments (0x9b720 : word) = Some W_9b6c8.
Proof. vm_refl. Qed.
Lemma D_9b6c8 : decode_any W_9b6c8 = Some (Jal 1 2049068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b6cc : bv 32 := 0x06a13023.
Lemma F_9b6cc : fetch_word Plain.M.loaded_segments (0x9b724 : word) = Some W_9b6cc.
Proof. vm_refl. Qed.
Lemma D_9b6cc : decode_any W_9b6cc = Some (Store SZ8 2 10 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b6d0 : bv 32 := 0x00000513.
Lemma F_9b6d0 : fetch_word Plain.M.loaded_segments (0x9b728 : word) = Some W_9b6d0.
Proof. vm_refl. Qed.
Lemma D_9b6d0 : decode_any W_9b6d0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b6d4 : bv 32 := 0x000b8593.
Lemma F_9b6d4 : fetch_word Plain.M.loaded_segments (0x9b72c : word) = Some W_9b6d4.
Proof. vm_refl. Qed.
Lemma D_9b6d4 : decode_any W_9b6d4 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b6d8 : bv 32 := 0x000c8613.
Lemma F_9b6d8 : fetch_word Plain.M.loaded_segments (0x9b730 : word) = Some W_9b6d8.
Proof. vm_refl. Qed.
Lemma D_9b6d8 : decode_any W_9b6d8 = Some (OpImm ALU_ADD 12 25 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b6dc : bv 32 := 0xc18f40ef.
Lemma F_9b6dc : fetch_word Plain.M.loaded_segments (0x9b734 : word) = Some W_9b6dc.
Proof. vm_refl. Qed.
Lemma D_9b6dc : decode_any W_9b6dc = Some (Jal 1 2049048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b6e0 : bv 32 := 0x06013583.
Lemma F_9b6e0 : fetch_word Plain.M.loaded_segments (0x9b738 : word) = Some W_9b6e0.
Proof. vm_refl. Qed.
Lemma D_9b6e0 : decode_any W_9b6e0 = Some (Load SZ8 true 11 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b6e4 : bv 32 := 0x00050613.
Lemma F_9b6e4 : fetch_word Plain.M.loaded_segments (0x9b73c : word) = Some W_9b6e4.
Proof. vm_refl. Qed.
Lemma D_9b6e4 : decode_any W_9b6e4 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b6e8 : bv 32 := 0x04a13c23.
Lemma F_9b6e8 : fetch_word Plain.M.loaded_segments (0x9b740 : word) = Some W_9b6e8.
Proof. vm_refl. Qed.
Lemma D_9b6e8 : decode_any W_9b6e8 = Some (Store SZ8 2 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b6ec : bv 32 := 0x00058513.
Lemma F_9b6ec : fetch_word Plain.M.loaded_segments (0x9b744 : word) = Some W_9b6ec.
Proof. vm_refl. Qed.
Lemma D_9b6ec : decode_any W_9b6ec = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b6f0 : bv 32 := 0xeccdd0ef.
Lemma F_9b6f0 : fetch_word Plain.M.loaded_segments (0x9b748 : word) = Some W_9b6f0.
Proof. vm_refl. Qed.
Lemma D_9b6f0 : decode_any W_9b6f0 = Some (Jal 1 1955532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b6f4 : bv 32 := 0x000a0a63.
Lemma F_9b6f4 : fetch_word Plain.M.loaded_segments (0x9b74c : word) = Some W_9b6f4.
Proof. vm_refl. Qed.
Lemma D_9b6f4 : decode_any W_9b6f4 = Some (Branch BC_EQ 20 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b708 : bv 32 := 0x06013503.
Lemma F_9b708 : fetch_word Plain.M.loaded_segments (0x9b760 : word) = Some W_9b708.
Proof. vm_refl. Qed.
Lemma D_9b708 : decode_any W_9b708 = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b70c : bv 32 := 0x00100593.
Lemma F_9b70c : fetch_word Plain.M.loaded_segments (0x9b764 : word) = Some W_9b70c.
Proof. vm_refl. Qed.
Lemma D_9b70c : decode_any W_9b70c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b710 : bv 32 := 0x00100613.
Lemma F_9b710 : fetch_word Plain.M.loaded_segments (0x9b768 : word) = Some W_9b710.
Proof. vm_refl. Qed.
Lemma D_9b710 : decode_any W_9b710 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b714 : bv 32 := 0x00000693.
Lemma F_9b714 : fetch_word Plain.M.loaded_segments (0x9b76c : word) = Some W_9b714.
Proof. vm_refl. Qed.
Lemma D_9b714 : decode_any W_9b714 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b718 : bv 32 := 0x00000713.
Lemma F_9b718 : fetch_word Plain.M.loaded_segments (0x9b770 : word) = Some W_9b718.
Proof. vm_refl. Qed.
Lemma D_9b718 : decode_any W_9b718 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b71c : bv 32 := 0xed8f80ef.
Lemma F_9b71c : fetch_word Plain.M.loaded_segments (0x9b774 : word) = Some W_9b71c.
Proof. vm_refl. Qed.
Lemma D_9b71c : decode_any W_9b71c = Some (Jal 1 2066136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b720 : bv 32 := 0x04a13823.
Lemma F_9b720 : fetch_word Plain.M.loaded_segments (0x9b778 : word) = Some W_9b720.
Proof. vm_refl. Qed.
Lemma D_9b720 : decode_any W_9b720 = Some (Store SZ8 2 10 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b724 : bv 32 := 0x07410593.
Lemma F_9b724 : fetch_word Plain.M.loaded_segments (0x9b77c : word) = Some W_9b724.
Proof. vm_refl. Qed.
Lemma D_9b724 : decode_any W_9b724 = Some (OpImm ALU_ADD 11 2 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b728 : bv 32 := 0x00000613.
Lemma F_9b728 : fetch_word Plain.M.loaded_segments (0x9b780 : word) = Some W_9b728.
Proof. vm_refl. Qed.
Lemma D_9b728 : decode_any W_9b728 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b72c : bv 32 := 0x835dd0ef.
Lemma F_9b72c : fetch_word Plain.M.loaded_segments (0x9b784 : word) = Some W_9b72c.
Proof. vm_refl. Qed.
Lemma D_9b72c : decode_any W_9b72c = Some (Jal 1 1955892, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b730 : bv 32 := 0x06013603.
Lemma F_9b730 : fetch_word Plain.M.loaded_segments (0x9b788 : word) = Some W_9b730.
Proof. vm_refl. Qed.
Lemma D_9b730 : decode_any W_9b730 = Some (Load SZ8 true 12 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b734 : bv 32 := 0xfff7e517.
Lemma F_9b734 : fetch_word Plain.M.loaded_segments (0x9b78c : word) = Some W_9b734.
Proof. vm_refl. Qed.
Lemma D_9b734 : decode_any W_9b734 = Some (Auipc 10 1048446, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b738 : bv 32 := 0x53950513.
Lemma F_9b738 : fetch_word Plain.M.loaded_segments (0x9b790 : word) = Some W_9b738.
Proof. vm_refl. Qed.
Lemma D_9b738 : decode_any W_9b738 = Some (OpImm ALU_ADD 10 10 1337, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b73c : bv 32 := 0x00098593.
Lemma F_9b73c : fetch_word Plain.M.loaded_segments (0x9b794 : word) = Some W_9b73c.
Proof. vm_refl. Qed.
Lemma D_9b73c : decode_any W_9b73c = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b740 : bv 32 := 0x00048693.
Lemma F_9b740 : fetch_word Plain.M.loaded_segments (0x9b798 : word) = Some W_9b740.
Proof. vm_refl. Qed.
Lemma D_9b740 : decode_any W_9b740 = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b744 : bv 32 := 0x3fc000ef.
Lemma F_9b744 : fetch_word Plain.M.loaded_segments (0x9b79c : word) = Some W_9b744.
Proof. vm_refl. Qed.
Lemma D_9b744 : decode_any W_9b744 = Some (Jal 1 1020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b748 : bv 32 := 0x06010513.
Lemma F_9b748 : fetch_word Plain.M.loaded_segments (0x9b7a0 : word) = Some W_9b748.
Proof. vm_refl. Qed.
Lemma D_9b748 : decode_any W_9b748 = Some (OpImm ALU_ADD 10 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b74c : bv 32 := 0xb98d10ef.
Lemma F_9b74c : fetch_word Plain.M.loaded_segments (0x9b7a4 : word) = Some W_9b74c.
Proof. vm_refl. Qed.
Lemma D_9b74c : decode_any W_9b74c = Some (Jal 1 1905560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b750 : bv 32 := 0x05810513.
Lemma F_9b750 : fetch_word Plain.M.loaded_segments (0x9b7a8 : word) = Some W_9b750.
Proof. vm_refl. Qed.
Lemma D_9b750 : decode_any W_9b750 = Some (OpImm ALU_ADD 10 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b754 : bv 32 := 0xb90d10ef.
Lemma F_9b754 : fetch_word Plain.M.loaded_segments (0x9b7ac : word) = Some W_9b754.
Proof. vm_refl. Qed.
Lemma D_9b754 : decode_any W_9b754 = Some (Jal 1 1905552, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b758 : bv 32 := 0x05010513.
Lemma F_9b758 : fetch_word Plain.M.loaded_segments (0x9b7b0 : word) = Some W_9b758.
Proof. vm_refl. Qed.
Lemma D_9b758 : decode_any W_9b758 = Some (OpImm ALU_ADD 10 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b75c : bv 32 := 0xb88d10ef.
Lemma F_9b75c : fetch_word Plain.M.loaded_segments (0x9b7b4 : word) = Some W_9b75c.
Proof. vm_refl. Qed.
Lemma D_9b75c : decode_any W_9b75c = Some (Jal 1 1905544, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b760 : bv 32 := 0x00000513.
Lemma F_9b760 : fetch_word Plain.M.loaded_segments (0x9b7b8 : word) = Some W_9b760.
Proof. vm_refl. Qed.
Lemma D_9b760 : decode_any W_9b760 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b764 : bv 32 := 0x000b8593.
Lemma F_9b764 : fetch_word Plain.M.loaded_segments (0x9b7bc : word) = Some W_9b764.
Proof. vm_refl. Qed.
Lemma D_9b764 : decode_any W_9b764 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b768 : bv 32 := 0x000a8613.
Lemma F_9b768 : fetch_word Plain.M.loaded_segments (0x9b7c0 : word) = Some W_9b768.
Proof. vm_refl. Qed.
Lemma D_9b768 : decode_any W_9b768 = Some (OpImm ALU_ADD 12 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b76c : bv 32 := 0xb88f40ef.
Lemma F_9b76c : fetch_word Plain.M.loaded_segments (0x9b7c4 : word) = Some W_9b76c.
Proof. vm_refl. Qed.
Lemma D_9b76c : decode_any W_9b76c = Some (Jal 1 2048904, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b770 : bv 32 := 0x06a13023.
Lemma F_9b770 : fetch_word Plain.M.loaded_segments (0x9b7c8 : word) = Some W_9b770.
Proof. vm_refl. Qed.
Lemma D_9b770 : decode_any W_9b770 = Some (Store SZ8 2 10 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b774 : bv 32 := 0x00000513.
Lemma F_9b774 : fetch_word Plain.M.loaded_segments (0x9b7cc : word) = Some W_9b774.
Proof. vm_refl. Qed.
Lemma D_9b774 : decode_any W_9b774 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b778 : bv 32 := 0x000b8593.
Lemma F_9b778 : fetch_word Plain.M.loaded_segments (0x9b7d0 : word) = Some W_9b778.
Proof. vm_refl. Qed.
Lemma D_9b778 : decode_any W_9b778 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b77c : bv 32 := 0x000b0613.
Lemma F_9b77c : fetch_word Plain.M.loaded_segments (0x9b7d4 : word) = Some W_9b77c.
Proof. vm_refl. Qed.
Lemma D_9b77c : decode_any W_9b77c = Some (OpImm ALU_ADD 12 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b780 : bv 32 := 0xb74f40ef.
Lemma F_9b780 : fetch_word Plain.M.loaded_segments (0x9b7d8 : word) = Some W_9b780.
Proof. vm_refl. Qed.
Lemma D_9b780 : decode_any W_9b780 = Some (Jal 1 2048884, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b784 : bv 32 := 0x06013583.
Lemma F_9b784 : fetch_word Plain.M.loaded_segments (0x9b7dc : word) = Some W_9b784.
Proof. vm_refl. Qed.
Lemma D_9b784 : decode_any W_9b784 = Some (Load SZ8 true 11 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b788 : bv 32 := 0x00050613.
Lemma F_9b788 : fetch_word Plain.M.loaded_segments (0x9b7e0 : word) = Some W_9b788.
Proof. vm_refl. Qed.
Lemma D_9b788 : decode_any W_9b788 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b78c : bv 32 := 0x04a13c23.
Lemma F_9b78c : fetch_word Plain.M.loaded_segments (0x9b7e4 : word) = Some W_9b78c.
Proof. vm_refl. Qed.
Lemma D_9b78c : decode_any W_9b78c = Some (Store SZ8 2 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b790 : bv 32 := 0x00058513.
Lemma F_9b790 : fetch_word Plain.M.loaded_segments (0x9b7e8 : word) = Some W_9b790.
Proof. vm_refl. Qed.
Lemma D_9b790 : decode_any W_9b790 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b794 : bv 32 := 0xe28dd0ef.
Lemma F_9b794 : fetch_word Plain.M.loaded_segments (0x9b7ec : word) = Some W_9b794.
Proof. vm_refl. Qed.
Lemma D_9b794 : decode_any W_9b794 = Some (Jal 1 1955368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b798 : bv 32 := 0x000a0a63.
Lemma F_9b798 : fetch_word Plain.M.loaded_segments (0x9b7f0 : word) = Some W_9b798.
Proof. vm_refl. Qed.
Lemma D_9b798 : decode_any W_9b798 = Some (Branch BC_EQ 20 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b7ac : bv 32 := 0x06013503.
Lemma F_9b7ac : fetch_word Plain.M.loaded_segments (0x9b804 : word) = Some W_9b7ac.
Proof. vm_refl. Qed.
Lemma D_9b7ac : decode_any W_9b7ac = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b7b0 : bv 32 := 0x00100593.
Lemma F_9b7b0 : fetch_word Plain.M.loaded_segments (0x9b808 : word) = Some W_9b7b0.
Proof. vm_refl. Qed.
Lemma D_9b7b0 : decode_any W_9b7b0 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b7b4 : bv 32 := 0x00100613.
Lemma F_9b7b4 : fetch_word Plain.M.loaded_segments (0x9b80c : word) = Some W_9b7b4.
Proof. vm_refl. Qed.
Lemma D_9b7b4 : decode_any W_9b7b4 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b7b8 : bv 32 := 0x00000693.
Lemma F_9b7b8 : fetch_word Plain.M.loaded_segments (0x9b810 : word) = Some W_9b7b8.
Proof. vm_refl. Qed.
Lemma D_9b7b8 : decode_any W_9b7b8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b7bc : bv 32 := 0x00000713.
Lemma F_9b7bc : fetch_word Plain.M.loaded_segments (0x9b814 : word) = Some W_9b7bc.
Proof. vm_refl. Qed.
Lemma D_9b7bc : decode_any W_9b7bc = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b7c0 : bv 32 := 0xe34f80ef.
Lemma F_9b7c0 : fetch_word Plain.M.loaded_segments (0x9b818 : word) = Some W_9b7c0.
Proof. vm_refl. Qed.
Lemma D_9b7c0 : decode_any W_9b7c0 = Some (Jal 1 2065972, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b7c4 : bv 32 := 0x04a13823.
Lemma F_9b7c4 : fetch_word Plain.M.loaded_segments (0x9b81c : word) = Some W_9b7c4.
Proof. vm_refl. Qed.
Lemma D_9b7c4 : decode_any W_9b7c4 = Some (Store SZ8 2 10 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b7c8 : bv 32 := 0x07010593.
Lemma F_9b7c8 : fetch_word Plain.M.loaded_segments (0x9b820 : word) = Some W_9b7c8.
Proof. vm_refl. Qed.
Lemma D_9b7c8 : decode_any W_9b7c8 = Some (OpImm ALU_ADD 11 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b7cc : bv 32 := 0x00000613.
Lemma F_9b7cc : fetch_word Plain.M.loaded_segments (0x9b824 : word) = Some W_9b7cc.
Proof. vm_refl. Qed.
Lemma D_9b7cc : decode_any W_9b7cc = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b7d0 : bv 32 := 0xf90dd0ef.
Lemma F_9b7d0 : fetch_word Plain.M.loaded_segments (0x9b828 : word) = Some W_9b7d0.
Proof. vm_refl. Qed.
Lemma D_9b7d0 : decode_any W_9b7d0 = Some (Jal 1 1955728, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b7d4 : bv 32 := 0x06013603.
Lemma F_9b7d4 : fetch_word Plain.M.loaded_segments (0x9b82c : word) = Some W_9b7d4.
Proof. vm_refl. Qed.
Lemma D_9b7d4 : decode_any W_9b7d4 = Some (Load SZ8 true 12 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b7d8 : bv 32 := 0xfff7f517.
Lemma F_9b7d8 : fetch_word Plain.M.loaded_segments (0x9b830 : word) = Some W_9b7d8.
Proof. vm_refl. Qed.
Lemma D_9b7d8 : decode_any W_9b7d8 = Some (Auipc 10 1048447, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b7dc : bv 32 := 0xd1b50513.
Lemma F_9b7dc : fetch_word Plain.M.loaded_segments (0x9b834 : word) = Some W_9b7dc.
Proof. vm_refl. Qed.
Lemma D_9b7dc : decode_any W_9b7dc = Some (OpImm ALU_ADD 10 10 3355, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b7e0 : bv 32 := 0x00098593.
Lemma F_9b7e0 : fetch_word Plain.M.loaded_segments (0x9b838 : word) = Some W_9b7e0.
Proof. vm_refl. Qed.
Lemma D_9b7e0 : decode_any W_9b7e0 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b7e4 : bv 32 := 0x00048693.
Lemma F_9b7e4 : fetch_word Plain.M.loaded_segments (0x9b83c : word) = Some W_9b7e4.
Proof. vm_refl. Qed.
Lemma D_9b7e4 : decode_any W_9b7e4 = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b7e8 : bv 32 := 0x358000ef.
Lemma F_9b7e8 : fetch_word Plain.M.loaded_segments (0x9b840 : word) = Some W_9b7e8.
Proof. vm_refl. Qed.
Lemma D_9b7e8 : decode_any W_9b7e8 = Some (Jal 1 856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b7ec : bv 32 := 0x06010513.
Lemma F_9b7ec : fetch_word Plain.M.loaded_segments (0x9b844 : word) = Some W_9b7ec.
Proof. vm_refl. Qed.
Lemma D_9b7ec : decode_any W_9b7ec = Some (OpImm ALU_ADD 10 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b7f0 : bv 32 := 0xaf4d10ef.
Lemma F_9b7f0 : fetch_word Plain.M.loaded_segments (0x9b848 : word) = Some W_9b7f0.
Proof. vm_refl. Qed.
Lemma D_9b7f0 : decode_any W_9b7f0 = Some (Jal 1 1905396, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b7f4 : bv 32 := 0x05810513.
Lemma F_9b7f4 : fetch_word Plain.M.loaded_segments (0x9b84c : word) = Some W_9b7f4.
Proof. vm_refl. Qed.
Lemma D_9b7f4 : decode_any W_9b7f4 = Some (OpImm ALU_ADD 10 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b7f8 : bv 32 := 0xaecd10ef.
Lemma F_9b7f8 : fetch_word Plain.M.loaded_segments (0x9b850 : word) = Some W_9b7f8.
Proof. vm_refl. Qed.
Lemma D_9b7f8 : decode_any W_9b7f8 = Some (Jal 1 1905388, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b7fc : bv 32 := 0x05010513.
Lemma F_9b7fc : fetch_word Plain.M.loaded_segments (0x9b854 : word) = Some W_9b7fc.
Proof. vm_refl. Qed.
Lemma D_9b7fc : decode_any W_9b7fc = Some (OpImm ALU_ADD 10 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b800 : bv 32 := 0xae4d10ef.
Lemma F_9b800 : fetch_word Plain.M.loaded_segments (0x9b858 : word) = Some W_9b800.
Proof. vm_refl. Qed.
Lemma D_9b800 : decode_any W_9b800 = Some (Jal 1 1905380, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b804 : bv 32 := 0x07412503.
Lemma F_9b804 : fetch_word Plain.M.loaded_segments (0x9b85c : word) = Some W_9b804.
Proof. vm_refl. Qed.
Lemma D_9b804 : decode_any W_9b804 = Some (Load SZ4 true 10 2 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b808 : bv 32 := 0x07012583.
Lemma F_9b808 : fetch_word Plain.M.loaded_segments (0x9b860 : word) = Some W_9b808.
Proof. vm_refl. Qed.
Lemma D_9b808 : decode_any W_9b808 = Some (Load SZ4 true 11 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b80c : bv 32 := 0x00050613.
Lemma F_9b80c : fetch_word Plain.M.loaded_segments (0x9b864 : word) = Some W_9b80c.
Proof. vm_refl. Qed.
Lemma D_9b80c : decode_any W_9b80c = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b810 : bv 32 := 0x00a5c463.
Lemma F_9b810 : fetch_word Plain.M.loaded_segments (0x9b868 : word) = Some W_9b810.
Proof. vm_refl. Qed.
Lemma D_9b810 : decode_any W_9b810 = Some (Branch BC_LT 11 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b814 : bv 32 := 0x00058613.
Lemma F_9b814 : fetch_word Plain.M.loaded_segments (0x9b86c : word) = Some W_9b814.
Proof. vm_refl. Qed.
Lemma D_9b814 : decode_any W_9b814 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b818 : bv 32 := 0xd0057453.
Lemma F_9b818 : fetch_word Plain.M.loaded_segments (0x9b870 : word) = Some W_9b818.
Proof. vm_refl. Qed.
Lemma D_9b818 : decode_any W_9b818 = Some (Fcvt FC_S FC_W 8 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b81c : bv 32 := 0xd005f4d3.
Lemma F_9b81c : fetch_word Plain.M.loaded_segments (0x9b874 : word) = Some W_9b81c.
Proof. vm_refl. Qed.
Lemma D_9b81c : decode_any W_9b81c = Some (Fcvt FC_S FC_W 9 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b820 : bv 32 := 0x02c95463.
Lemma F_9b820 : fetch_word Plain.M.loaded_segments (0x9b878 : word) = Some W_9b820.
Proof. vm_refl. Qed.
Lemma D_9b820 : decode_any W_9b820 = Some (Branch BC_GE 18 12 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b824 : bv 32 := 0x089477d3.
Lemma F_9b824 : fetch_word Plain.M.loaded_segments (0x9b87c : word) = Some W_9b824.
Proof. vm_refl. Qed.
Lemma D_9b824 : decode_any W_9b824 = Some (Fari F_SUB FMT_S 15 8 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b828 : bv 32 := 0x00947753.
Lemma F_9b828 : fetch_word Plain.M.loaded_segments (0x9b880 : word) = Some W_9b828.
Proof. vm_refl. Qed.
Lemma D_9b828 : decode_any W_9b828 = Some (Fari F_ADD FMT_S 14 8 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b82c : bv 32 := 0x420787d3.
Lemma F_9b82c : fetch_word Plain.M.loaded_segments (0x9b884 : word) = Some W_9b82c.
Proof. vm_refl. Qed.
Lemma D_9b82c : decode_any W_9b82c = Some (Fcvt FC_D FC_S 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b830 : bv 32 := 0x42070753.
Lemma F_9b830 : fetch_word Plain.M.loaded_segments (0x9b888 : word) = Some W_9b830.
Proof. vm_refl. Qed.
Lemma D_9b830 : decode_any W_9b830 = Some (Fcvt FC_D FC_S 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b834 : bv 32 := 0x5a077753.
Lemma F_9b834 : fetch_word Plain.M.loaded_segments (0x9b88c : word) = Some W_9b834.
Proof. vm_refl. Qed.
Lemma D_9b834 : decode_any W_9b834 = Some (Fsqrt FMT_D 14 14 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b838 : bv 32 := 0x1ae7f7d3.
Lemma F_9b838 : fetch_word Plain.M.loaded_segments (0x9b890 : word) = Some W_9b838.
Proof. vm_refl. Qed.
Lemma D_9b838 : decode_any W_9b838 = Some (Fari F_DIV FMT_D 15 15 14 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b83c : bv 32 := 0x02f7f7d3.
Lemma F_9b83c : fetch_word Plain.M.loaded_segments (0x9b894 : word) = Some W_9b83c.
Proof. vm_refl. Qed.
Lemma D_9b83c : decode_any W_9b83c = Some (Fari F_ADD FMT_D 15 15 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b840 : bv 32 := 0x4017f7d3.
Lemma F_9b840 : fetch_word Plain.M.loaded_segments (0x9b898 : word) = Some W_9b840.
Proof. vm_refl. Qed.
Lemma D_9b840 : decode_any W_9b840 = Some (Fcvt FC_S FC_D 15 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b844 : bv 32 := 0x00f42027.
Lemma F_9b844 : fetch_word Plain.M.loaded_segments (0x9b89c : word) = Some W_9b844.
Proof. vm_refl. Qed.
Lemma D_9b844 : decode_any W_9b844 = Some (FStore FMT_S 8 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b848 : bv 32 := 0x08048263.
Lemma F_9b848 : fetch_word Plain.M.loaded_segments (0x9b8a0 : word) = Some W_9b848.
Proof. vm_refl. Qed.
Lemma D_9b848 : decode_any W_9b848 = Some (Branch BC_EQ 9 0 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b8cc : bv 32 := 0x06810513.
Lemma F_9b8cc : fetch_word Plain.M.loaded_segments (0x9b924 : word) = Some W_9b8cc.
Proof. vm_refl. Qed.
Lemma D_9b8cc : decode_any W_9b8cc = Some (OpImm ALU_ADD 10 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b8d0 : bv 32 := 0xa14d10ef.
Lemma F_9b8d0 : fetch_word Plain.M.loaded_segments (0x9b928 : word) = Some W_9b8d0.
Proof. vm_refl. Qed.
Lemma D_9b8d0 : decode_any W_9b8d0 = Some (Jal 1 1905172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b8d4 : bv 32 := 0x04810513.
Lemma F_9b8d4 : fetch_word Plain.M.loaded_segments (0x9b92c : word) = Some W_9b8d4.
Proof. vm_refl. Qed.
Lemma D_9b8d4 : decode_any W_9b8d4 = Some (OpImm ALU_ADD 10 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b8d8 : bv 32 := 0xa0cd10ef.
Lemma F_9b8d8 : fetch_word Plain.M.loaded_segments (0x9b930 : word) = Some W_9b8d8.
Proof. vm_refl. Qed.
Lemma D_9b8d8 : decode_any W_9b8d8 = Some (Jal 1 1905164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b8dc : bv 32 := 0x04010513.
Lemma F_9b8dc : fetch_word Plain.M.loaded_segments (0x9b934 : word) = Some W_9b8dc.
Proof. vm_refl. Qed.
Lemma D_9b8dc : decode_any W_9b8dc = Some (OpImm ALU_ADD 10 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b8e0 : bv 32 := 0xab9f60ef.
Lemma F_9b8e0 : fetch_word Plain.M.loaded_segments (0x9b938 : word) = Some W_9b8e0.
Proof. vm_refl. Qed.
Lemma D_9b8e0 : decode_any W_9b8e0 = Some (Jal 1 2058936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b8e4 : bv 32 := 0x03810513.
Lemma F_9b8e4 : fetch_word Plain.M.loaded_segments (0x9b93c : word) = Some W_9b8e4.
Proof. vm_refl. Qed.
Lemma D_9b8e4 : decode_any W_9b8e4 = Some (OpImm ALU_ADD 10 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b8e8 : bv 32 := 0xab1f60ef.
Lemma F_9b8e8 : fetch_word Plain.M.loaded_segments (0x9b940 : word) = Some W_9b8e8.
Proof. vm_refl. Qed.
Lemma D_9b8e8 : decode_any W_9b8e8 = Some (Jal 1 2058928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b8ec : bv 32 := 0x03010513.
Lemma F_9b8ec : fetch_word Plain.M.loaded_segments (0x9b944 : word) = Some W_9b8ec.
Proof. vm_refl. Qed.
Lemma D_9b8ec : decode_any W_9b8ec = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b8f0 : bv 32 := 0xaa9f60ef.
Lemma F_9b8f0 : fetch_word Plain.M.loaded_segments (0x9b948 : word) = Some W_9b8f0.
Proof. vm_refl. Qed.
Lemma D_9b8f0 : decode_any W_9b8f0 = Some (Jal 1 2058920, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b8f4 : bv 32 := 0x02810513.
Lemma F_9b8f4 : fetch_word Plain.M.loaded_segments (0x9b94c : word) = Some W_9b8f4.
Proof. vm_refl. Qed.
Lemma D_9b8f4 : decode_any W_9b8f4 = Some (OpImm ALU_ADD 10 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b8f8 : bv 32 := 0xaa1f60ef.
Lemma F_9b8f8 : fetch_word Plain.M.loaded_segments (0x9b950 : word) = Some W_9b8f8.
Proof. vm_refl. Qed.
Lemma D_9b8f8 : decode_any W_9b8f8 = Some (Jal 1 2058912, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b8fc : bv 32 := 0x00000513.
Lemma F_9b8fc : fetch_word Plain.M.loaded_segments (0x9b954 : word) = Some W_9b8fc.
Proof. vm_refl. Qed.
Lemma D_9b8fc : decode_any W_9b8fc = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b900 : bv 32 := 0x0e813083.
Lemma F_9b900 : fetch_word Plain.M.loaded_segments (0x9b958 : word) = Some W_9b900.
Proof. vm_refl. Qed.
Lemma D_9b900 : decode_any W_9b900 = Some (Load SZ8 true 1 2 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b904 : bv 32 := 0x0e013403.
Lemma F_9b904 : fetch_word Plain.M.loaded_segments (0x9b95c : word) = Some W_9b904.
Proof. vm_refl. Qed.
Lemma D_9b904 : decode_any W_9b904 = Some (Load SZ8 true 8 2 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b908 : bv 32 := 0x0d813483.
Lemma F_9b908 : fetch_word Plain.M.loaded_segments (0x9b960 : word) = Some W_9b908.
Proof. vm_refl. Qed.
Lemma D_9b908 : decode_any W_9b908 = Some (Load SZ8 true 9 2 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b90c : bv 32 := 0x0d013903.
Lemma F_9b90c : fetch_word Plain.M.loaded_segments (0x9b964 : word) = Some W_9b90c.
Proof. vm_refl. Qed.
Lemma D_9b90c : decode_any W_9b90c = Some (Load SZ8 true 18 2 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b910 : bv 32 := 0x0c813983.
Lemma F_9b910 : fetch_word Plain.M.loaded_segments (0x9b968 : word) = Some W_9b910.
Proof. vm_refl. Qed.
Lemma D_9b910 : decode_any W_9b910 = Some (Load SZ8 true 19 2 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b914 : bv 32 := 0x0c013a03.
Lemma F_9b914 : fetch_word Plain.M.loaded_segments (0x9b96c : word) = Some W_9b914.
Proof. vm_refl. Qed.
Lemma D_9b914 : decode_any W_9b914 = Some (Load SZ8 true 20 2 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b918 : bv 32 := 0x0b813a83.
Lemma F_9b918 : fetch_word Plain.M.loaded_segments (0x9b970 : word) = Some W_9b918.
Proof. vm_refl. Qed.
Lemma D_9b918 : decode_any W_9b918 = Some (Load SZ8 true 21 2 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b91c : bv 32 := 0x0b013b03.
Lemma F_9b91c : fetch_word Plain.M.loaded_segments (0x9b974 : word) = Some W_9b91c.
Proof. vm_refl. Qed.
Lemma D_9b91c : decode_any W_9b91c = Some (Load SZ8 true 22 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b920 : bv 32 := 0x0a813b83.
Lemma F_9b920 : fetch_word Plain.M.loaded_segments (0x9b978 : word) = Some W_9b920.
Proof. vm_refl. Qed.
Lemma D_9b920 : decode_any W_9b920 = Some (Load SZ8 true 23 2 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b924 : bv 32 := 0x0a013c03.
Lemma F_9b924 : fetch_word Plain.M.loaded_segments (0x9b97c : word) = Some W_9b924.
Proof. vm_refl. Qed.
Lemma D_9b924 : decode_any W_9b924 = Some (Load SZ8 true 24 2 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b928 : bv 32 := 0x09813c83.
Lemma F_9b928 : fetch_word Plain.M.loaded_segments (0x9b980 : word) = Some W_9b928.
Proof. vm_refl. Qed.
Lemma D_9b928 : decode_any W_9b928 = Some (Load SZ8 true 25 2 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b92c : bv 32 := 0x09013d03.
Lemma F_9b92c : fetch_word Plain.M.loaded_segments (0x9b984 : word) = Some W_9b92c.
Proof. vm_refl. Qed.
Lemma D_9b92c : decode_any W_9b92c = Some (Load SZ8 true 26 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b930 : bv 32 := 0x08813d83.
Lemma F_9b930 : fetch_word Plain.M.loaded_segments (0x9b988 : word) = Some W_9b930.
Proof. vm_refl. Qed.
Lemma D_9b930 : decode_any W_9b930 = Some (Load SZ8 true 27 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b934 : bv 32 := 0x08013407.
Lemma F_9b934 : fetch_word Plain.M.loaded_segments (0x9b98c : word) = Some W_9b934.
Proof. vm_refl. Qed.
Lemma D_9b934 : decode_any W_9b934 = Some (FLoad FMT_D 8 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b938 : bv 32 := 0x07813487.
Lemma F_9b938 : fetch_word Plain.M.loaded_segments (0x9b990 : word) = Some W_9b938.
Proof. vm_refl. Qed.
Lemma D_9b938 : decode_any W_9b938 = Some (FLoad FMT_D 9 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b93c : bv 32 := 0x0f010113.
Lemma F_9b93c : fetch_word Plain.M.loaded_segments (0x9b994 : word) = Some W_9b93c.
Proof. vm_refl. Qed.
Lemma D_9b93c : decode_any W_9b93c = Some (OpImm ALU_ADD 2 2 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b940 : bv 32 := 0x00008067.
Lemma F_9b940 : fetch_word Plain.M.loaded_segments (0x9b998 : word) = Some W_9b940.
Proof. vm_refl. Qed.
Lemma D_9b940 : decode_any W_9b940 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_9bb40 : bv 32 := 0x08068e63.
Lemma F_9bb40 : fetch_word Plain.M.loaded_segments (0x9bb98 : word) = Some W_9bb40.
Proof. vm_refl. Qed.
Lemma D_9bb40 : decode_any W_9bb40 = Some (Branch BC_EQ 13 0 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bbdc : bv 32 := 0x00008067.
Lemma F_9bbdc : fetch_word Plain.M.loaded_segments (0x9bc34 : word) = Some W_9bbdc.
Proof. vm_refl. Qed.
Lemma D_9bbdc : decode_any W_9bbdc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

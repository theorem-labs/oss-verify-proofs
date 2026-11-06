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
Definition W_6caa4 : bv 32 := 0x00050663.
Lemma F_6caa4 : fetch_word Plain.M.loaded_segments (0x6cafc : word) = Some W_6caa4.
Proof. vm_refl. Qed.
Lemma D_6caa4 : decode_any W_6caa4 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6caa8 : bv 32 := 0x01052503.
Lemma F_6caa8 : fetch_word Plain.M.loaded_segments (0x6cb00 : word) = Some W_6caa8.
Proof. vm_refl. Qed.
Lemma D_6caa8 : decode_any W_6caa8 = Some (Load SZ4 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6caac : bv 32 := 0x00008067.
Lemma F_6caac : fetch_word Plain.M.loaded_segments (0x6cb04 : word) = Some W_6caac.
Proof. vm_refl. Qed.
Lemma D_6caac : decode_any W_6caac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cda0 : bv 32 := 0x00058463.
Lemma F_6cda0 : fetch_word Plain.M.loaded_segments (0x6cdf8 : word) = Some W_6cda0.
Proof. vm_refl. Qed.
Lemma D_6cda0 : decode_any W_6cda0 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cda4 : bv 32 := 0x0005a023.
Lemma F_6cda4 : fetch_word Plain.M.loaded_segments (0x6cdfc : word) = Some W_6cda4.
Proof. vm_refl. Qed.
Lemma D_6cda4 : decode_any W_6cda4 = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cda8 : bv 32 := 0x00060463.
Lemma F_6cda8 : fetch_word Plain.M.loaded_segments (0x6ce00 : word) = Some W_6cda8.
Proof. vm_refl. Qed.
Lemma D_6cda8 : decode_any W_6cda8 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdac : bv 32 := 0x00062023.
Lemma F_6cdac : fetch_word Plain.M.loaded_segments (0x6ce04 : word) = Some W_6cdac.
Proof. vm_refl. Qed.
Lemma D_6cdac : decode_any W_6cdac = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdb0 : bv 32 := 0x00068463.
Lemma F_6cdb0 : fetch_word Plain.M.loaded_segments (0x6ce08 : word) = Some W_6cdb0.
Proof. vm_refl. Qed.
Lemma D_6cdb0 : decode_any W_6cdb0 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdb4 : bv 32 := 0x0006a023.
Lemma F_6cdb4 : fetch_word Plain.M.loaded_segments (0x6ce0c : word) = Some W_6cdb4.
Proof. vm_refl. Qed.
Lemma D_6cdb4 : decode_any W_6cdb4 = Some (Store SZ4 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdb8 : bv 32 := 0x02050a63.
Lemma F_6cdb8 : fetch_word Plain.M.loaded_segments (0x6ce10 : word) = Some W_6cdb8.
Proof. vm_refl. Qed.
Lemma D_6cdb8 : decode_any W_6cdb8 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdbc : bv 32 := 0x00058663.
Lemma F_6cdbc : fetch_word Plain.M.loaded_segments (0x6ce14 : word) = Some W_6cdbc.
Proof. vm_refl. Qed.
Lemma D_6cdbc : decode_any W_6cdbc = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdc0 : bv 32 := 0x00052703.
Lemma F_6cdc0 : fetch_word Plain.M.loaded_segments (0x6ce18 : word) = Some W_6cdc0.
Proof. vm_refl. Qed.
Lemma D_6cdc0 : decode_any W_6cdc0 = Some (Load SZ4 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdc4 : bv 32 := 0x00e5a023.
Lemma F_6cdc4 : fetch_word Plain.M.loaded_segments (0x6ce1c : word) = Some W_6cdc4.
Proof. vm_refl. Qed.
Lemma D_6cdc4 : decode_any W_6cdc4 = Some (Store SZ4 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdc8 : bv 32 := 0x00060663.
Lemma F_6cdc8 : fetch_word Plain.M.loaded_segments (0x6ce20 : word) = Some W_6cdc8.
Proof. vm_refl. Qed.
Lemma D_6cdc8 : decode_any W_6cdc8 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdcc : bv 32 := 0x00452583.
Lemma F_6cdcc : fetch_word Plain.M.loaded_segments (0x6ce24 : word) = Some W_6cdcc.
Proof. vm_refl. Qed.
Lemma D_6cdcc : decode_any W_6cdcc = Some (Load SZ4 true 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdd0 : bv 32 := 0x00b62023.
Lemma F_6cdd0 : fetch_word Plain.M.loaded_segments (0x6ce28 : word) = Some W_6cdd0.
Proof. vm_refl. Qed.
Lemma D_6cdd0 : decode_any W_6cdd0 = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdd4 : bv 32 := 0x00000593.
Lemma F_6cdd4 : fetch_word Plain.M.loaded_segments (0x6ce2c : word) = Some W_6cdd4.
Proof. vm_refl. Qed.
Lemma D_6cdd4 : decode_any W_6cdd4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdd8 : bv 32 := 0x00068663.
Lemma F_6cdd8 : fetch_word Plain.M.loaded_segments (0x6ce30 : word) = Some W_6cdd8.
Proof. vm_refl. Qed.
Lemma D_6cdd8 : decode_any W_6cdd8 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cddc : bv 32 := 0x00852503.
Lemma F_6cddc : fetch_word Plain.M.loaded_segments (0x6ce34 : word) = Some W_6cddc.
Proof. vm_refl. Qed.
Lemma D_6cddc : decode_any W_6cddc = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cde0 : bv 32 := 0x00a6a023.
Lemma F_6cde0 : fetch_word Plain.M.loaded_segments (0x6ce38 : word) = Some W_6cde0.
Proof. vm_refl. Qed.
Lemma D_6cde0 : decode_any W_6cde0 = Some (Store SZ4 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cde4 : bv 32 := 0x00058513.
Lemma F_6cde4 : fetch_word Plain.M.loaded_segments (0x6ce3c : word) = Some W_6cde4.
Proof. vm_refl. Qed.
Lemma D_6cde4 : decode_any W_6cde4 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cde8 : bv 32 := 0x00008067.
Lemma F_6cde8 : fetch_word Plain.M.loaded_segments (0x6ce40 : word) = Some W_6cde8.
Proof. vm_refl. Qed.
Lemma D_6cde8 : decode_any W_6cde8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d428 : bv 32 := 0xfd010113.
Lemma F_6d428 : fetch_word Plain.M.loaded_segments (0x6d480 : word) = Some W_6d428.
Proof. vm_refl. Qed.
Lemma D_6d428 : decode_any W_6d428 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d42c : bv 32 := 0x02113423.
Lemma F_6d42c : fetch_word Plain.M.loaded_segments (0x6d484 : word) = Some W_6d42c.
Proof. vm_refl. Qed.
Lemma D_6d42c : decode_any W_6d42c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d430 : bv 32 := 0x02813023.
Lemma F_6d430 : fetch_word Plain.M.loaded_segments (0x6d488 : word) = Some W_6d430.
Proof. vm_refl. Qed.
Lemma D_6d430 : decode_any W_6d430 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d434 : bv 32 := 0x00913c23.
Lemma F_6d434 : fetch_word Plain.M.loaded_segments (0x6d48c : word) = Some W_6d434.
Proof. vm_refl. Qed.
Lemma D_6d434 : decode_any W_6d434 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d438 : bv 32 := 0x01213823.
Lemma F_6d438 : fetch_word Plain.M.loaded_segments (0x6d490 : word) = Some W_6d438.
Proof. vm_refl. Qed.
Lemma D_6d438 : decode_any W_6d438 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d43c : bv 32 := 0x01313423.
Lemma F_6d43c : fetch_word Plain.M.loaded_segments (0x6d494 : word) = Some W_6d43c.
Proof. vm_refl. Qed.
Lemma D_6d43c : decode_any W_6d43c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d440 : bv 32 := 0x00050413.
Lemma F_6d440 : fetch_word Plain.M.loaded_segments (0x6d498 : word) = Some W_6d440.
Proof. vm_refl. Qed.
Lemma D_6d440 : decode_any W_6d440 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d444 : bv 32 := 0x06058063.
Lemma F_6d444 : fetch_word Plain.M.loaded_segments (0x6d49c : word) = Some W_6d444.
Proof. vm_refl. Qed.
Lemma D_6d444 : decode_any W_6d444 = Some (Branch BC_EQ 11 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d448 : bv 32 := 0x00058493.
Lemma F_6d448 : fetch_word Plain.M.loaded_segments (0x6d4a0 : word) = Some W_6d448.
Proof. vm_refl. Qed.
Lemma D_6d448 : decode_any W_6d448 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d44c : bv 32 := 0x18858e63.
Lemma F_6d44c : fetch_word Plain.M.loaded_segments (0x6d4a4 : word) = Some W_6d44c.
Proof. vm_refl. Qed.
Lemma D_6d44c : decode_any W_6d44c = Some (Branch BC_EQ 11 8 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5e8 : bv 32 := 0x00040513.
Lemma F_6d5e8 : fetch_word Plain.M.loaded_segments (0x6d640 : word) = Some W_6d5e8.
Proof. vm_refl. Qed.
Lemma D_6d5e8 : decode_any W_6d5e8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5ec : bv 32 := 0x02813083.
Lemma F_6d5ec : fetch_word Plain.M.loaded_segments (0x6d644 : word) = Some W_6d5ec.
Proof. vm_refl. Qed.
Lemma D_6d5ec : decode_any W_6d5ec = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5f0 : bv 32 := 0x02013403.
Lemma F_6d5f0 : fetch_word Plain.M.loaded_segments (0x6d648 : word) = Some W_6d5f0.
Proof. vm_refl. Qed.
Lemma D_6d5f0 : decode_any W_6d5f0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5f4 : bv 32 := 0x01813483.
Lemma F_6d5f4 : fetch_word Plain.M.loaded_segments (0x6d64c : word) = Some W_6d5f4.
Proof. vm_refl. Qed.
Lemma D_6d5f4 : decode_any W_6d5f4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5f8 : bv 32 := 0x01013903.
Lemma F_6d5f8 : fetch_word Plain.M.loaded_segments (0x6d650 : word) = Some W_6d5f8.
Proof. vm_refl. Qed.
Lemma D_6d5f8 : decode_any W_6d5f8 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5fc : bv 32 := 0x00813983.
Lemma F_6d5fc : fetch_word Plain.M.loaded_segments (0x6d654 : word) = Some W_6d5fc.
Proof. vm_refl. Qed.
Lemma D_6d5fc : decode_any W_6d5fc = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d600 : bv 32 := 0x03010113.
Lemma F_6d600 : fetch_word Plain.M.loaded_segments (0x6d658 : word) = Some W_6d600.
Proof. vm_refl. Qed.
Lemma D_6d600 : decode_any W_6d600 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d604 : bv 32 := 0x00008067.
Lemma F_6d604 : fetch_word Plain.M.loaded_segments (0x6d65c : word) = Some W_6d604.
Proof. vm_refl. Qed.
Lemma D_6d604 : decode_any W_6d604 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_6d9e8 : bv 32 := 0x00050663.
Lemma F_6d9e8 : fetch_word Plain.M.loaded_segments (0x6da40 : word) = Some W_6d9e8.
Proof. vm_refl. Qed.
Lemma D_6d9e8 : decode_any W_6d9e8 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d9ec : bv 32 := 0x03853503.
Lemma F_6d9ec : fetch_word Plain.M.loaded_segments (0x6da44 : word) = Some W_6d9ec.
Proof. vm_refl. Qed.
Lemma D_6d9ec : decode_any W_6d9ec = Some (Load SZ8 true 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d9f0 : bv 32 := 0x00008067.
Lemma F_6d9f0 : fetch_word Plain.M.loaded_segments (0x6da48 : word) = Some W_6d9f0.
Proof. vm_refl. Qed.
Lemma D_6d9f0 : decode_any W_6d9f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_883e8 : bv 32 := 0xf8010113.
Lemma F_883e8 : fetch_word Plain.M.loaded_segments (0x88440 : word) = Some W_883e8.
Proof. vm_refl. Qed.
Lemma D_883e8 : decode_any W_883e8 = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_883ec : bv 32 := 0x06113c23.
Lemma F_883ec : fetch_word Plain.M.loaded_segments (0x88444 : word) = Some W_883ec.
Proof. vm_refl. Qed.
Lemma D_883ec : decode_any W_883ec = Some (Store SZ8 2 1 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_883f0 : bv 32 := 0x06813823.
Lemma F_883f0 : fetch_word Plain.M.loaded_segments (0x88448 : word) = Some W_883f0.
Proof. vm_refl. Qed.
Lemma D_883f0 : decode_any W_883f0 = Some (Store SZ8 2 8 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_883f4 : bv 32 := 0x06913423.
Lemma F_883f4 : fetch_word Plain.M.loaded_segments (0x8844c : word) = Some W_883f4.
Proof. vm_refl. Qed.
Lemma D_883f4 : decode_any W_883f4 = Some (Store SZ8 2 9 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_883f8 : bv 32 := 0x07213023.
Lemma F_883f8 : fetch_word Plain.M.loaded_segments (0x88450 : word) = Some W_883f8.
Proof. vm_refl. Qed.
Lemma D_883f8 : decode_any W_883f8 = Some (Store SZ8 2 18 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_883fc : bv 32 := 0x05313c23.
Lemma F_883fc : fetch_word Plain.M.loaded_segments (0x88454 : word) = Some W_883fc.
Proof. vm_refl. Qed.
Lemma D_883fc : decode_any W_883fc = Some (Store SZ8 2 19 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88400 : bv 32 := 0x05413823.
Lemma F_88400 : fetch_word Plain.M.loaded_segments (0x88458 : word) = Some W_88400.
Proof. vm_refl. Qed.
Lemma D_88400 : decode_any W_88400 = Some (Store SZ8 2 20 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88404 : bv 32 := 0x05513423.
Lemma F_88404 : fetch_word Plain.M.loaded_segments (0x8845c : word) = Some W_88404.
Proof. vm_refl. Qed.
Lemma D_88404 : decode_any W_88404 = Some (Store SZ8 2 21 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88408 : bv 32 := 0x05613023.
Lemma F_88408 : fetch_word Plain.M.loaded_segments (0x88460 : word) = Some W_88408.
Proof. vm_refl. Qed.
Lemma D_88408 : decode_any W_88408 = Some (Store SZ8 2 22 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8840c : bv 32 := 0x03713c23.
Lemma F_8840c : fetch_word Plain.M.loaded_segments (0x88464 : word) = Some W_8840c.
Proof. vm_refl. Qed.
Lemma D_8840c : decode_any W_8840c = Some (Store SZ8 2 23 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88410 : bv 32 := 0x03813823.
Lemma F_88410 : fetch_word Plain.M.loaded_segments (0x88468 : word) = Some W_88410.
Proof. vm_refl. Qed.
Lemma D_88410 : decode_any W_88410 = Some (Store SZ8 2 24 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88414 : bv 32 := 0x03913423.
Lemma F_88414 : fetch_word Plain.M.loaded_segments (0x8846c : word) = Some W_88414.
Proof. vm_refl. Qed.
Lemma D_88414 : decode_any W_88414 = Some (Store SZ8 2 25 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88418 : bv 32 := 0x03a13023.
Lemma F_88418 : fetch_word Plain.M.loaded_segments (0x88470 : word) = Some W_88418.
Proof. vm_refl. Qed.
Lemma D_88418 : decode_any W_88418 = Some (Store SZ8 2 26 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8841c : bv 32 := 0x12058263.
Lemma F_8841c : fetch_word Plain.M.loaded_segments (0x88474 : word) = Some W_8841c.
Proof. vm_refl. Qed.
Lemma D_8841c : decode_any W_8841c = Some (Branch BC_EQ 11 0 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88420 : bv 32 := 0x00058413.
Lemma F_88420 : fetch_word Plain.M.loaded_segments (0x88478 : word) = Some W_88420.
Proof. vm_refl. Qed.
Lemma D_88420 : decode_any W_88420 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88424 : bv 32 := 0x00050493.
Lemma F_88424 : fetch_word Plain.M.loaded_segments (0x8847c : word) = Some W_88424.
Proof. vm_refl. Qed.
Lemma D_88424 : decode_any W_88424 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88428 : bv 32 := 0x01410593.
Lemma F_88428 : fetch_word Plain.M.loaded_segments (0x88480 : word) = Some W_88428.
Proof. vm_refl. Qed.
Lemma D_88428 : decode_any W_88428 = Some (OpImm ALU_ADD 11 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8842c : bv 32 := 0x01010613.
Lemma F_8842c : fetch_word Plain.M.loaded_segments (0x88484 : word) = Some W_8842c.
Proof. vm_refl. Qed.
Lemma D_8842c : decode_any W_8842c = Some (OpImm ALU_ADD 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88430 : bv 32 := 0x00c10693.
Lemma F_88430 : fetch_word Plain.M.loaded_segments (0x88488 : word) = Some W_88430.
Proof. vm_refl. Qed.
Lemma D_88430 : decode_any W_88430 = Some (OpImm ALU_ADD 13 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88434 : bv 32 := 0x00040513.
Lemma F_88434 : fetch_word Plain.M.loaded_segments (0x8848c : word) = Some W_88434.
Proof. vm_refl. Qed.
Lemma D_88434 : decode_any W_88434 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88438 : bv 32 := 0x969e40ef.
Lemma F_88438 : fetch_word Plain.M.loaded_segments (0x88490 : word) = Some W_88438.
Proof. vm_refl. Qed.
Lemma D_88438 : decode_any W_88438 = Some (Jal 1 1984872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8843c : bv 32 := 0x00c12503.
Lemma F_8843c : fetch_word Plain.M.loaded_segments (0x88494 : word) = Some W_8843c.
Proof. vm_refl. Qed.
Lemma D_8843c : decode_any W_8843c = Some (Load SZ4 true 10 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88440 : bv 32 := 0x02000593.
Lemma F_88440 : fetch_word Plain.M.loaded_segments (0x88498 : word) = Some W_88440.
Proof. vm_refl. Qed.
Lemma D_88440 : decode_any W_88440 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88444 : bv 32 := 0x18a5e263.
Lemma F_88444 : fetch_word Plain.M.loaded_segments (0x8849c : word) = Some W_88444.
Proof. vm_refl. Qed.
Lemma D_88444 : decode_any W_88444 = Some (Branch BC_LTU 11 10 388, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88448 : bv 32 := 0x100015b7.
Lemma F_88448 : fetch_word Plain.M.loaded_segments (0x884a0 : word) = Some W_88448.
Proof. vm_refl. Qed.
Lemma D_88448 : decode_any W_88448 = Some (Lui 11 65537, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8844c : bv 32 := 0x00459593.
Lemma F_8844c : fetch_word Plain.M.loaded_segments (0x884a4 : word) = Some W_8844c.
Proof. vm_refl. Qed.
Lemma D_8844c : decode_any W_8844c = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88450 : bv 32 := 0x11658593.
Lemma F_88450 : fetch_word Plain.M.loaded_segments (0x884a8 : word) = Some W_88450.
Proof. vm_refl. Qed.
Lemma D_88450 : decode_any W_88450 = Some (OpImm ALU_ADD 11 11 278, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88454 : bv 32 := 0x00a5d533.
Lemma F_88454 : fetch_word Plain.M.loaded_segments (0x884ac : word) = Some W_88454.
Proof. vm_refl. Qed.
Lemma D_88454 : decode_any W_88454 = Some (Op ALU_SRL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88458 : bv 32 := 0x00157513.
Lemma F_88458 : fetch_word Plain.M.loaded_segments (0x884b0 : word) = Some W_88458.
Proof. vm_refl. Qed.
Lemma D_88458 : decode_any W_88458 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8845c : bv 32 := 0x16050663.
Lemma F_8845c : fetch_word Plain.M.loaded_segments (0x884b4 : word) = Some W_8845c.
Proof. vm_refl. Qed.
Lemma D_8845c : decode_any W_8845c = Some (Branch BC_EQ 10 0 364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88460 : bv 32 := 0x00048513.
Lemma F_88460 : fetch_word Plain.M.loaded_segments (0x884b8 : word) = Some W_88460.
Proof. vm_refl. Qed.
Lemma D_88460 : decode_any W_88460 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88464 : bv 32 := 0x00040593.
Lemma F_88464 : fetch_word Plain.M.loaded_segments (0x884bc : word) = Some W_88464.
Proof. vm_refl. Qed.
Lemma D_88464 : decode_any W_88464 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88468 : bv 32 := 0xfc1e40ef.
Lemma F_88468 : fetch_word Plain.M.loaded_segments (0x884c0 : word) = Some W_88468.
Proof. vm_refl. Qed.
Lemma D_88468 : decode_any W_88468 = Some (Jal 1 1986496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8846c : bv 32 := 0x00a13c23.
Lemma F_8846c : fetch_word Plain.M.loaded_segments (0x884c4 : word) = Some W_8846c.
Proof. vm_refl. Qed.
Lemma D_8846c : decode_any W_8846c = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88470 : bv 32 := 0x12050863.
Lemma F_88470 : fetch_word Plain.M.loaded_segments (0x884c8 : word) = Some W_88470.
Proof. vm_refl. Qed.
Lemma D_88470 : decode_any W_88470 = Some (Branch BC_EQ 10 0 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88474 : bv 32 := 0x00050493.
Lemma F_88474 : fetch_word Plain.M.loaded_segments (0x884cc : word) = Some W_88474.
Proof. vm_refl. Qed.
Lemma D_88474 : decode_any W_88474 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88478 : bv 32 := 0xd70e50ef.
Lemma F_88478 : fetch_word Plain.M.loaded_segments (0x884d0 : word) = Some W_88478.
Proof. vm_refl. Qed.
Lemma D_88478 : decode_any W_88478 = Some (Jal 1 1987952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8847c : bv 32 := 0x00050413.
Lemma F_8847c : fetch_word Plain.M.loaded_segments (0x884d4 : word) = Some W_8847c.
Proof. vm_refl. Qed.
Lemma D_8847c : decode_any W_8847c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88480 : bv 32 := 0x00048a13.
Lemma F_88480 : fetch_word Plain.M.loaded_segments (0x884d8 : word) = Some W_88480.
Proof. vm_refl. Qed.
Lemma D_88480 : decode_any W_88480 = Some (OpImm ALU_ADD 20 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88484 : bv 32 := 0x00048513.
Lemma F_88484 : fetch_word Plain.M.loaded_segments (0x884dc : word) = Some W_88484.
Proof. vm_refl. Qed.
Lemma D_88484 : decode_any W_88484 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88488 : bv 32 := 0xe1ce40ef.
Lemma F_88488 : fetch_word Plain.M.loaded_segments (0x884e0 : word) = Some W_88488.
Proof. vm_refl. Qed.
Lemma D_88488 : decode_any W_88488 = Some (Jal 1 1984028, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8848c : bv 32 := 0x00c12583.
Lemma F_8848c : fetch_word Plain.M.loaded_segments (0x884e4 : word) = Some W_8848c.
Proof. vm_refl. Qed.
Lemma D_8848c : decode_any W_8848c = Some (Load SZ4 true 11 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88490 : bv 32 := 0x00400613.
Lemma F_88490 : fetch_word Plain.M.loaded_segments (0x884e8 : word) = Some W_88490.
Proof. vm_refl. Qed.
Lemma D_88490 : decode_any W_88490 = Some (OpImm ALU_ADD 12 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88494 : bv 32 := 0x00050913.
Lemma F_88494 : fetch_word Plain.M.loaded_segments (0x884ec : word) = Some W_88494.
Proof. vm_refl. Qed.
Lemma D_88494 : decode_any W_88494 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88498 : bv 32 := 0x1cc58263.
Lemma F_88498 : fetch_word Plain.M.loaded_segments (0x884f0 : word) = Some W_88498.
Proof. vm_refl. Qed.
Lemma D_88498 : decode_any W_88498 = Some (Branch BC_EQ 11 12 452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8849c : bv 32 := 0x00200513.
Lemma F_8849c : fetch_word Plain.M.loaded_segments (0x884f4 : word) = Some W_8849c.
Proof. vm_refl. Qed.
Lemma D_8849c : decode_any W_8849c = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_884a0 : bv 32 := 0x16a58063.
Lemma F_884a0 : fetch_word Plain.M.loaded_segments (0x884f8 : word) = Some W_884a0.
Proof. vm_refl. Qed.
Lemma D_884a0 : decode_any W_884a0 = Some (Branch BC_EQ 11 10 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_884a4 : bv 32 := 0x00100513.
Lemma F_884a4 : fetch_word Plain.M.loaded_segments (0x884fc : word) = Some W_884a4.
Proof. vm_refl. Qed.
Lemma D_884a4 : decode_any W_884a4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_884a8 : bv 32 := 0x1ea59a63.
Lemma F_884a8 : fetch_word Plain.M.loaded_segments (0x88500 : word) = Some W_884a8.
Proof. vm_refl. Qed.
Lemma D_884a8 : decode_any W_884a8 = Some (Branch BC_NE 11 10 500, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_884ac : bv 32 := 0x10000513.
Lemma F_884ac : fetch_word Plain.M.loaded_segments (0x88504 : word) = Some W_884ac.
Proof. vm_refl. Qed.
Lemma D_884ac : decode_any W_884ac = Some (OpImm ALU_ADD 10 0 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_884b0 : bv 32 := 0x00100593.
Lemma F_884b0 : fetch_word Plain.M.loaded_segments (0x88508 : word) = Some W_884b0.
Proof. vm_refl. Qed.
Lemma D_884b0 : decode_any W_884b0 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_884b4 : bv 32 := 0x531710ef.
Lemma F_884b4 : fetch_word Plain.M.loaded_segments (0x8850c : word) = Some W_884b4.
Proof. vm_refl. Qed.
Lemma D_884b4 : decode_any W_884b4 = Some (Jal 1 466224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_884b8 : bv 32 := 0x00050493.
Lemma F_884b8 : fetch_word Plain.M.loaded_segments (0x88510 : word) = Some W_884b8.
Proof. vm_refl. Qed.
Lemma D_884b8 : decode_any W_884b8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_884bc : bv 32 := 0x00000513.
Lemma F_884bc : fetch_word Plain.M.loaded_segments (0x88514 : word) = Some W_884bc.
Proof. vm_refl. Qed.
Lemma D_884bc : decode_any W_884bc = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_884c0 : bv 32 := 0x00000593.
Lemma F_884c0 : fetch_word Plain.M.loaded_segments (0x88518 : word) = Some W_884c0.
Proof. vm_refl. Qed.
Lemma D_884c0 : decode_any W_884c0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_884c4 : bv 32 := 0x00000613.
Lemma F_884c4 : fetch_word Plain.M.loaded_segments (0x8851c : word) = Some W_884c4.
Proof. vm_refl. Qed.
Lemma D_884c4 : decode_any W_884c4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_884c8 : bv 32 := 0x00000693.
Lemma F_884c8 : fetch_word Plain.M.loaded_segments (0x88520 : word) = Some W_884c8.
Proof. vm_refl. Qed.
Lemma D_884c8 : decode_any W_884c8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_884cc : bv 32 := 0x00000713.
Lemma F_884cc : fetch_word Plain.M.loaded_segments (0x88524 : word) = Some W_884cc.
Proof. vm_refl. Qed.
Lemma D_884cc : decode_any W_884cc = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_884d0 : bv 32 := 0x10048793.
Lemma F_884d0 : fetch_word Plain.M.loaded_segments (0x88528 : word) = Some W_884d0.
Proof. vm_refl. Qed.
Lemma D_884d0 : decode_any W_884d0 = Some (OpImm ALU_ADD 15 9 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_884d4 : bv 32 := 0x00048813.
Lemma F_884d4 : fetch_word Plain.M.loaded_segments (0x8852c : word) = Some W_884d4.
Proof. vm_refl. Qed.
Lemma D_884d4 : decode_any W_884d4 = Some (OpImm ALU_ADD 16 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_884d8 : bv 32 := 0x0075589b.
Lemma F_884d8 : fetch_word Plain.M.loaded_segments (0x88530 : word) = Some W_884d8.
Proof. vm_refl. Qed.
Lemma D_884d8 : decode_any W_884d8 = Some (ShiftImm32 ALU_SRL 17 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_884dc : bv 32 := 0x00555293.
Lemma F_884dc : fetch_word Plain.M.loaded_segments (0x88534 : word) = Some W_884dc.
Proof. vm_refl. Qed.
Lemma D_884dc : decode_any W_884dc = Some (ShiftImm ALU_SRL 5 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_884e0 : bv 32 := 0x00355313.
Lemma F_884e0 : fetch_word Plain.M.loaded_segments (0x88538 : word) = Some W_884e0.
Proof. vm_refl. Qed.
Lemma D_884e0 : decode_any W_884e0 = Some (ShiftImm ALU_SRL 6 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_884e4 : bv 32 := 0x00155393.
Lemma F_884e4 : fetch_word Plain.M.loaded_segments (0x8853c : word) = Some W_884e4.
Proof. vm_refl. Qed.
Lemma D_884e4 : decode_any W_884e4 = Some (ShiftImm ALU_SRL 7 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_884e8 : bv 32 := 0x0105fe13.
Lemma F_884e8 : fetch_word Plain.M.loaded_segments (0x88540 : word) = Some W_884e8.
Proof. vm_refl. Qed.
Lemma D_884e8 : decode_any W_884e8 = Some (OpImm ALU_AND 28 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_884ec : bv 32 := 0x02067e93.
Lemma F_884ec : fetch_word Plain.M.loaded_segments (0x88544 : word) = Some W_884ec.
Proof. vm_refl. Qed.
Lemma D_884ec : decode_any W_884ec = Some (OpImm ALU_AND 29 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_884f0 : bv 32 := 0x0406ff13.
Lemma F_884f0 : fetch_word Plain.M.loaded_segments (0x88548 : word) = Some W_884f0.
Proof. vm_refl. Qed.
Lemma D_884f0 : decode_any W_884f0 = Some (OpImm ALU_AND 30 13 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_884f4 : bv 32 := 0x02068693.
Lemma F_884f4 : fetch_word Plain.M.loaded_segments (0x8854c : word) = Some W_884f4.
Proof. vm_refl. Qed.
Lemma D_884f4 : decode_any W_884f4 = Some (OpImm ALU_ADD 13 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_884f8 : bv 32 := 0x00860613.
Lemma F_884f8 : fetch_word Plain.M.loaded_segments (0x88550 : word) = Some W_884f8.
Proof. vm_refl. Qed.
Lemma D_884f8 : decode_any W_884f8 = Some (OpImm ALU_ADD 12 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_884fc : bv 32 := 0x0022f293.
Lemma F_884fc : fetch_word Plain.M.loaded_segments (0x88554 : word) = Some W_884fc.
Proof. vm_refl. Qed.
Lemma D_884fc : decode_any W_884fc = Some (OpImm ALU_AND 5 5 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88500 : bv 32 := 0x00437313.
Lemma F_88500 : fetch_word Plain.M.loaded_segments (0x88558 : word) = Some W_88500.
Proof. vm_refl. Qed.
Lemma D_88500 : decode_any W_88500 = Some (OpImm ALU_AND 6 6 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88504 : bv 32 := 0x0083f393.
Lemma F_88504 : fetch_word Plain.M.loaded_segments (0x8855c : word) = Some W_88504.
Proof. vm_refl. Qed.
Lemma D_88504 : decode_any W_88504 = Some (OpImm ALU_AND 7 7 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88508 : bv 32 := 0x011768b3.
Lemma F_88508 : fetch_word Plain.M.loaded_segments (0x88560 : word) = Some W_88508.
Proof. vm_refl. Qed.
Lemma D_88508 : decode_any W_88508 = Some (Op ALU_OR 17 14 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8850c : bv 32 := 0x01de6e33.
Lemma F_8850c : fetch_word Plain.M.loaded_segments (0x88564 : word) = Some W_8850c.
Proof. vm_refl. Qed.
Lemma D_8850c : decode_any W_8850c = Some (Op ALU_OR 28 28 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88510 : bv 32 := 0x08070713.
Lemma F_88510 : fetch_word Plain.M.loaded_segments (0x88568 : word) = Some W_88510.
Proof. vm_refl. Qed.
Lemma D_88510 : decode_any W_88510 = Some (OpImm ALU_ADD 14 14 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88514 : bv 32 := 0x0058e8b3.
Lemma F_88514 : fetch_word Plain.M.loaded_segments (0x8856c : word) = Some W_88514.
Proof. vm_refl. Qed.
Lemma D_88514 : decode_any W_88514 = Some (Op ALU_OR 17 17 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88518 : bv 32 := 0x007362b3.
Lemma F_88518 : fetch_word Plain.M.loaded_segments (0x88570 : word) = Some W_88518.
Proof. vm_refl. Qed.
Lemma D_88518 : decode_any W_88518 = Some (Op ALU_OR 5 6 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8851c : bv 32 := 0x01ee6333.
Lemma F_8851c : fetch_word Plain.M.loaded_segments (0x88574 : word) = Some W_8851c.
Proof. vm_refl. Qed.
Lemma D_8851c : decode_any W_8851c = Some (Op ALU_OR 6 28 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88520 : bv 32 := 0x0058e8b3.
Lemma F_88520 : fetch_word Plain.M.loaded_segments (0x88578 : word) = Some W_88520.
Proof. vm_refl. Qed.
Lemma D_88520 : decode_any W_88520 = Some (Op ALU_OR 17 17 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88524 : bv 32 := 0x0068e8b3.
Lemma F_88524 : fetch_word Plain.M.loaded_segments (0x8857c : word) = Some W_88524.
Proof. vm_refl. Qed.
Lemma D_88524 : decode_any W_88524 = Some (Op ALU_OR 17 17 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88528 : bv 32 := 0x01180023.
Lemma F_88528 : fetch_word Plain.M.loaded_segments (0x88580 : word) = Some W_88528.
Proof. vm_refl. Qed.
Lemma D_88528 : decode_any W_88528 = Some (Store SZ1 16 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8852c : bv 32 := 0x00180813.
Lemma F_8852c : fetch_word Plain.M.loaded_segments (0x88584 : word) = Some W_8852c.
Proof. vm_refl. Qed.
Lemma D_8852c : decode_any W_8852c = Some (OpImm ALU_ADD 16 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88530 : bv 32 := 0x00258593.
Lemma F_88530 : fetch_word Plain.M.loaded_segments (0x88588 : word) = Some W_88530.
Proof. vm_refl. Qed.
Lemma D_88530 : decode_any W_88530 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88534 : bv 32 := 0x00150513.
Lemma F_88534 : fetch_word Plain.M.loaded_segments (0x8858c : word) = Some W_88534.
Proof. vm_refl. Qed.
Lemma D_88534 : decode_any W_88534 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88538 : bv 32 := 0xfaf810e3.
Lemma F_88538 : fetch_word Plain.M.loaded_segments (0x88590 : word) = Some W_88538.
Proof. vm_refl. Qed.
Lemma D_88538 : decode_any W_88538 = Some (Branch BC_NE 16 15 8096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8853c : bv 32 := 0x1640006f.
Lemma F_8853c : fetch_word Plain.M.loaded_segments (0x88594 : word) = Some W_8853c.
Proof. vm_refl. Qed.
Lemma D_8853c : decode_any W_8853c = Some (Jal 0 356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_886a0 : bv 32 := 0x00400593.
Lemma F_886a0 : fetch_word Plain.M.loaded_segments (0x886f8 : word) = Some W_886a0.
Proof. vm_refl. Qed.
Lemma D_886a0 : decode_any W_886a0 = Some (OpImm ALU_ADD 11 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_886a4 : bv 32 := 0x00090513.
Lemma F_886a4 : fetch_word Plain.M.loaded_segments (0x886fc : word) = Some W_886a4.
Proof. vm_refl. Qed.
Lemma D_886a4 : decode_any W_886a4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_886a8 : bv 32 := 0x33d710ef.
Lemma F_886a8 : fetch_word Plain.M.loaded_segments (0x88700 : word) = Some W_886a8.
Proof. vm_refl. Qed.
Lemma D_886a8 : decode_any W_886a8 = Some (Jal 1 465724, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_886ac : bv 32 := 0x10050463.
Lemma F_886ac : fetch_word Plain.M.loaded_segments (0x88704 : word) = Some W_886ac.
Proof. vm_refl. Qed.
Lemma D_886ac : decode_any W_886ac = Some (Branch BC_EQ 10 0 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_886b0 : bv 32 := 0x00050993.
Lemma F_886b0 : fetch_word Plain.M.loaded_segments (0x88708 : word) = Some W_886b0.
Proof. vm_refl. Qed.
Lemma D_886b0 : decode_any W_886b0 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_886b4 : bv 32 := 0x00c12503.
Lemma F_886b4 : fetch_word Plain.M.loaded_segments (0x8870c : word) = Some W_886b4.
Proof. vm_refl. Qed.
Lemma D_886b4 : decode_any W_886b4 = Some (Load SZ4 true 10 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_886b8 : bv 32 := 0xfff50513.
Lemma F_886b8 : fetch_word Plain.M.loaded_segments (0x88710 : word) = Some W_886b8.
Proof. vm_refl. Qed.
Lemma D_886b8 : decode_any W_886b8 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_886bc : bv 32 := 0x01f00593.
Lemma F_886bc : fetch_word Plain.M.loaded_segments (0x88714 : word) = Some W_886bc.
Proof. vm_refl. Qed.
Lemma D_886bc : decode_any W_886bc = Some (OpImm ALU_ADD 11 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_886c0 : bv 32 := 0x28a5e663.
Lemma F_886c0 : fetch_word Plain.M.loaded_segments (0x88718 : word) = Some W_886c0.
Proof. vm_refl. Qed.
Lemma D_886c0 : decode_any W_886c0 = Some (Branch BC_LTU 11 10 652, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_886c4 : bv 32 := 0x00251513.
Lemma F_886c4 : fetch_word Plain.M.loaded_segments (0x8871c : word) = Some W_886c4.
Proof. vm_refl. Qed.
Lemma D_886c4 : decode_any W_886c4 = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_886c8 : bv 32 := 0xfff97597.
Lemma F_886c8 : fetch_word Plain.M.loaded_segments (0x88720 : word) = Some W_886c8.
Proof. vm_refl. Qed.
Lemma D_886c8 : decode_any W_886c8 = Some (Auipc 11 1048471, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_886cc : bv 32 := 0x02858593.
Lemma F_886cc : fetch_word Plain.M.loaded_segments (0x88724 : word) = Some W_886cc.
Proof. vm_refl. Qed.
Lemma D_886cc : decode_any W_886cc = Some (OpImm ALU_ADD 11 11 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_886d0 : bv 32 := 0x00b50533.
Lemma F_886d0 : fetch_word Plain.M.loaded_segments (0x88728 : word) = Some W_886d0.
Proof. vm_refl. Qed.
Lemma D_886d0 : decode_any W_886d0 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_886d4 : bv 32 := 0x00052503.
Lemma F_886d4 : fetch_word Plain.M.loaded_segments (0x8872c : word) = Some W_886d4.
Proof. vm_refl. Qed.
Lemma D_886d4 : decode_any W_886d4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_886d8 : bv 32 := 0x00b50533.
Lemma F_886d8 : fetch_word Plain.M.loaded_segments (0x88730 : word) = Some W_886d8.
Proof. vm_refl. Qed.
Lemma D_886d8 : decode_any W_886d8 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_886dc : bv 32 := 0x00291a1b.
Lemma F_886dc : fetch_word Plain.M.loaded_segments (0x88734 : word) = Some W_886dc.
Proof. vm_refl. Qed.
Lemma D_886dc : decode_any W_886dc = Some (ShiftImm32 ALU_SLL 20 18 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_886e0 : bv 32 := 0x00050067.
Lemma F_886e0 : fetch_word Plain.M.loaded_segments (0x88738 : word) = Some W_886e0.
Proof. vm_refl. Qed.
Lemma D_886e0 : decode_any W_886e0 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_886e4 : bv 32 := 0x01412a83.
Lemma F_886e4 : fetch_word Plain.M.loaded_segments (0x8873c : word) = Some W_886e4.
Proof. vm_refl. Qed.
Lemma D_886e4 : decode_any W_886e4 = Some (Load SZ4 true 21 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_886e8 : bv 32 := 0x01faf513.
Lemma F_886e8 : fetch_word Plain.M.loaded_segments (0x88740 : word) = Some W_886e8.
Proof. vm_refl. Qed.
Lemma D_886e8 : decode_any W_886e8 = Some (OpImm ALU_AND 10 21 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_886ec : bv 32 := 0x02050663.
Lemma F_886ec : fetch_word Plain.M.loaded_segments (0x88744 : word) = Some W_886ec.
Proof. vm_refl. Qed.
Lemma D_886ec : decode_any W_886ec = Some (Branch BC_EQ 10 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_886f0 : bv 32 := 0x01012583.
Lemma F_886f0 : fetch_word Plain.M.loaded_segments (0x88748 : word) = Some W_886f0.
Proof. vm_refl. Qed.
Lemma D_886f0 : decode_any W_886f0 = Some (Load SZ4 true 11 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_886f4 : bv 32 := 0x02000613.
Lemma F_886f4 : fetch_word Plain.M.loaded_segments (0x8874c : word) = Some W_886f4.
Proof. vm_refl. Qed.
Lemma D_886f4 : decode_any W_886f4 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_886f8 : bv 32 := 0x40a60833.
Lemma F_886f8 : fetch_word Plain.M.loaded_segments (0x88750 : word) = Some W_886f8.
Proof. vm_refl. Qed.
Lemma D_886f8 : decode_any W_886f8 = Some (Op ALU_SUB 16 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_886fc : bv 32 := 0x00100613.
Lemma F_886fc : fetch_word Plain.M.loaded_segments (0x88754 : word) = Some W_886fc.
Proof. vm_refl. Qed.
Lemma D_886fc : decode_any W_886fc = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88700 : bv 32 := 0x00040513.
Lemma F_88700 : fetch_word Plain.M.loaded_segments (0x88758 : word) = Some W_88700.
Proof. vm_refl. Qed.
Lemma D_88700 : decode_any W_88700 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88704 : bv 32 := 0x00090693.
Lemma F_88704 : fetch_word Plain.M.loaded_segments (0x8875c : word) = Some W_88704.
Proof. vm_refl. Qed.
Lemma D_88704 : decode_any W_88704 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88708 : bv 32 := 0x00000713.
Lemma F_88708 : fetch_word Plain.M.loaded_segments (0x88760 : word) = Some W_88708.
Proof. vm_refl. Qed.
Lemma D_88708 : decode_any W_88708 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8870c : bv 32 := 0x00058793.
Lemma F_8870c : fetch_word Plain.M.loaded_segments (0x88764 : word) = Some W_8870c.
Proof. vm_refl. Qed.
Lemma D_8870c : decode_any W_8870c = Some (OpImm ALU_ADD 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88710 : bv 32 := 0xbe0f40ef.
Lemma F_88710 : fetch_word Plain.M.loaded_segments (0x88768 : word) = Some W_88710.
Proof. vm_refl. Qed.
Lemma D_88710 : decode_any W_88710 = Some (Jal 1 2048992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88714 : bv 32 := 0x01412a83.
Lemma F_88714 : fetch_word Plain.M.loaded_segments (0x8876c : word) = Some W_88714.
Proof. vm_refl. Qed.
Lemma D_88714 : decode_any W_88714 = Some (Load SZ4 true 21 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88718 : bv 32 := 0x01012503.
Lemma F_88718 : fetch_word Plain.M.loaded_segments (0x88770 : word) = Some W_88718.
Proof. vm_refl. Qed.
Lemma D_88718 : decode_any W_88718 = Some (Load SZ4 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8871c : bv 32 := 0x42a05c63.
Lemma F_8871c : fetch_word Plain.M.loaded_segments (0x88774 : word) = Some W_8871c.
Proof. vm_refl. Qed.
Lemma D_8871c : decode_any W_8871c = Some (Branch BC_GE 0 10 1080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88720 : bv 32 := 0x007a8513.
Lemma F_88720 : fetch_word Plain.M.loaded_segments (0x88778 : word) = Some W_88720.
Proof. vm_refl. Qed.
Lemma D_88720 : decode_any W_88720 = Some (OpImm ALU_ADD 10 21 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88724 : bv 32 := 0x41f5559b.
Lemma F_88724 : fetch_word Plain.M.loaded_segments (0x8877c : word) = Some W_88724.
Proof. vm_refl. Qed.
Lemma D_88724 : decode_any W_88724 = Some (ShiftImm32 ALU_SRA 11 10 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88728 : bv 32 := 0x01d5d59b.
Lemma F_88728 : fetch_word Plain.M.loaded_segments (0x88780 : word) = Some W_88728.
Proof. vm_refl. Qed.
Lemma D_88728 : decode_any W_88728 = Some (ShiftImm32 ALU_SRL 11 11 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8872c : bv 32 := 0x00b50533.
Lemma F_8872c : fetch_word Plain.M.loaded_segments (0x88784 : word) = Some W_8872c.
Proof. vm_refl. Qed.
Lemma D_8872c : decode_any W_8872c = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88730 : bv 32 := 0x4035551b.
Lemma F_88730 : fetch_word Plain.M.loaded_segments (0x88788 : word) = Some W_88730.
Proof. vm_refl. Qed.
Lemma D_88730 : decode_any W_88730 = Some (ShiftImm32 ALU_SRA 10 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88734 : bv 32 := 0x00a04463.
Lemma F_88734 : fetch_word Plain.M.loaded_segments (0x8878c : word) = Some W_88734.
Proof. vm_refl. Qed.
Lemma D_88734 : decode_any W_88734 = Some (Branch BC_LT 0 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8873c : bv 32 := 0x00000b13.
Lemma F_8873c : fetch_word Plain.M.loaded_segments (0x88794 : word) = Some W_8873c.
Proof. vm_refl. Qed.
Lemma D_8873c : decode_any W_8873c = Some (OpImm ALU_ADD 22 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88740 : bv 32 := 0xfffa0b9b.
Lemma F_88740 : fetch_word Plain.M.loaded_segments (0x88798 : word) = Some W_88740.
Proof. vm_refl. Qed.
Lemma D_88740 : decode_any W_88740 = Some (OpImm32 23 20 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88744 : bv 32 := 0x00291c13.
Lemma F_88744 : fetch_word Plain.M.loaded_segments (0x8879c : word) = Some W_88744.
Proof. vm_refl. Qed.
Lemma D_88744 : decode_any W_88744 = Some (ShiftImm ALU_SLL 24 18 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88748 : bv 32 := 0x40ab8cbb.
Lemma F_88748 : fetch_word Plain.M.loaded_segments (0x887a0 : word) = Some W_88748.
Proof. vm_refl. Qed.
Lemma D_88748 : decode_any W_88748 = Some (Op32 ALU_SUB 25 23 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8874c : bv 32 := 0x00040d13.
Lemma F_8874c : fetch_word Plain.M.loaded_segments (0x887a4 : word) = Some W_8874c.
Proof. vm_refl. Qed.
Lemma D_8874c : decode_any W_8874c = Some (OpImm ALU_ADD 26 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88750 : bv 32 := 0x0140006f.
Lemma F_88750 : fetch_word Plain.M.loaded_segments (0x887a8 : word) = Some W_88750.
Proof. vm_refl. Qed.
Lemma D_88750 : decode_any W_88750 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88754 : bv 32 := 0x01012503.
Lemma F_88754 : fetch_word Plain.M.loaded_segments (0x887ac : word) = Some W_88754.
Proof. vm_refl. Qed.
Lemma D_88754 : decode_any W_88754 = Some (Load SZ4 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88758 : bv 32 := 0x001b0b13.
Lemma F_88758 : fetch_word Plain.M.loaded_segments (0x887b0 : word) = Some W_88758.
Proof. vm_refl. Qed.
Lemma D_88758 : decode_any W_88758 = Some (OpImm ALU_ADD 22 22 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8875c : bv 32 := 0x018d0d33.
Lemma F_8875c : fetch_word Plain.M.loaded_segments (0x887b4 : word) = Some W_8875c.
Proof. vm_refl. Qed.
Lemma D_8875c : decode_any W_8875c = Some (Op ALU_ADD 26 26 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88760 : bv 32 := 0x3eab5a63.
Lemma F_88760 : fetch_word Plain.M.loaded_segments (0x887b8 : word) = Some W_88760.
Proof. vm_refl. Qed.
Lemma D_88760 : decode_any W_88760 = Some (Branch BC_GE 22 10 1012, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88764 : bv 32 := 0x032b0533.
Lemma F_88764 : fetch_word Plain.M.loaded_segments (0x887bc : word) = Some W_88764.
Proof. vm_refl. Qed.
Lemma D_88764 : decode_any W_88764 = Some (Mul M_MUL 10 22 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88768 : bv 32 := 0x00251513.
Lemma F_88768 : fetch_word Plain.M.loaded_segments (0x887c0 : word) = Some W_88768.
Proof. vm_refl. Qed.
Lemma D_88768 : decode_any W_88768 = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8876c : bv 32 := 0x00a405b3.
Lemma F_8876c : fetch_word Plain.M.loaded_segments (0x887c4 : word) = Some W_8876c.
Proof. vm_refl. Qed.
Lemma D_8876c : decode_any W_8876c = Some (Op ALU_ADD 11 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88770 : bv 32 := 0x00098513.
Lemma F_88770 : fetch_word Plain.M.loaded_segments (0x887c8 : word) = Some W_88770.
Proof. vm_refl. Qed.
Lemma D_88770 : decode_any W_88770 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88774 : bv 32 := 0x000a0613.
Lemma F_88774 : fetch_word Plain.M.loaded_segments (0x887cc : word) = Some W_88774.
Proof. vm_refl. Qed.
Lemma D_88774 : decode_any W_88774 = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88778 : bv 32 := 0x4e0810ef.
Lemma F_88778 : fetch_word Plain.M.loaded_segments (0x887d0 : word) = Some W_88778.
Proof. vm_refl. Qed.
Lemma D_88778 : decode_any W_88778 = Some (Jal 1 529632, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8877c : bv 32 := 0xfd505ce3.
Lemma F_8877c : fetch_word Plain.M.loaded_segments (0x887d4 : word) = Some W_8877c.
Proof. vm_refl. Qed.
Lemma D_8877c : decode_any W_8877c = Some (Branch BC_GE 0 21 8152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88780 : bv 32 := 0x000d0513.
Lemma F_88780 : fetch_word Plain.M.loaded_segments (0x887d8 : word) = Some W_88780.
Proof. vm_refl. Qed.
Lemma D_88780 : decode_any W_88780 = Some (OpImm ALU_ADD 10 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88784 : bv 32 := 0x000b8593.
Lemma F_88784 : fetch_word Plain.M.loaded_segments (0x887dc : word) = Some W_88784.
Proof. vm_refl. Qed.
Lemma D_88784 : decode_any W_88784 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88788 : bv 32 := 0x00b98633.
Lemma F_88788 : fetch_word Plain.M.loaded_segments (0x887e0 : word) = Some W_88788.
Proof. vm_refl. Qed.
Lemma D_88788 : decode_any W_88788 = Some (Op ALU_ADD 12 19 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8878c : bv 32 := 0x00364613.
Lemma F_8878c : fetch_word Plain.M.loaded_segments (0x887e4 : word) = Some W_8878c.
Proof. vm_refl. Qed.
Lemma D_8878c : decode_any W_8878c = Some (OpImm ALU_XOR 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88790 : bv 32 := 0x00064603.
Lemma F_88790 : fetch_word Plain.M.loaded_segments (0x887e8 : word) = Some W_88790.
Proof. vm_refl. Qed.
Lemma D_88790 : decode_any W_88790 = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88794 : bv 32 := 0x00c48633.
Lemma F_88794 : fetch_word Plain.M.loaded_segments (0x887ec : word) = Some W_88794.
Proof. vm_refl. Qed.
Lemma D_88794 : decode_any W_88794 = Some (Op ALU_ADD 12 9 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88798 : bv 32 := 0x00064603.
Lemma F_88798 : fetch_word Plain.M.loaded_segments (0x887f0 : word) = Some W_88798.
Proof. vm_refl. Qed.
Lemma D_88798 : decode_any W_88798 = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8879c : bv 32 := 0x00354693.
Lemma F_8879c : fetch_word Plain.M.loaded_segments (0x887f4 : word) = Some W_8879c.
Proof. vm_refl. Qed.
Lemma D_8879c : decode_any W_8879c = Some (OpImm ALU_XOR 13 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_887a0 : bv 32 := 0xfff5859b.
Lemma F_887a0 : fetch_word Plain.M.loaded_segments (0x887f8 : word) = Some W_887a0.
Proof. vm_refl. Qed.
Lemma D_887a0 : decode_any W_887a0 = Some (OpImm32 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_887a4 : bv 32 := 0x00c68023.
Lemma F_887a4 : fetch_word Plain.M.loaded_segments (0x887fc : word) = Some W_887a4.
Proof. vm_refl. Qed.
Lemma D_887a4 : decode_any W_887a4 = Some (Store SZ1 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_887a8 : bv 32 := 0x00150513.
Lemma F_887a8 : fetch_word Plain.M.loaded_segments (0x88800 : word) = Some W_887a8.
Proof. vm_refl. Qed.
Lemma D_887a8 : decode_any W_887a8 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_887ac : bv 32 := 0xfd959ee3.
Lemma F_887ac : fetch_word Plain.M.loaded_segments (0x88804 : word) = Some W_887ac.
Proof. vm_refl. Qed.
Lemma D_887ac : decode_any W_887ac = Some (Branch BC_NE 11 25 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_887b0 : bv 32 := 0xfa5ff06f.
Lemma F_887b0 : fetch_word Plain.M.loaded_segments (0x88808 : word) = Some W_887b0.
Proof. vm_refl. Qed.
Lemma D_887b0 : decode_any W_887b0 = Some (Jal 0 2097060, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88b54 : bv 32 := 0x00098513.
Lemma F_88b54 : fetch_word Plain.M.loaded_segments (0x88bac : word) = Some W_88b54.
Proof. vm_refl. Qed.
Lemma D_88b54 : decode_any W_88b54 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88b58 : bv 32 := 0x7c4710ef.
Lemma F_88b58 : fetch_word Plain.M.loaded_segments (0x88bb0 : word) = Some W_88b58.
Proof. vm_refl. Qed.
Lemma D_88b58 : decode_any W_88b58 = Some (Jal 1 464836, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88b5c : bv 32 := 0x00048663.
Lemma F_88b5c : fetch_word Plain.M.loaded_segments (0x88bb4 : word) = Some W_88b5c.
Proof. vm_refl. Qed.
Lemma D_88b5c : decode_any W_88b5c = Some (Branch BC_EQ 9 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88b60 : bv 32 := 0x00048513.
Lemma F_88b60 : fetch_word Plain.M.loaded_segments (0x88bb8 : word) = Some W_88b60.
Proof. vm_refl. Qed.
Lemma D_88b60 : decode_any W_88b60 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88b64 : bv 32 := 0x7b8710ef.
Lemma F_88b64 : fetch_word Plain.M.loaded_segments (0x88bbc : word) = Some W_88b64.
Proof. vm_refl. Qed.
Lemma D_88b64 : decode_any W_88b64 = Some (Jal 1 464824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88b68 : bv 32 := 0x01813503.
Lemma F_88b68 : fetch_word Plain.M.loaded_segments (0x88bc0 : word) = Some W_88b68.
Proof. vm_refl. Qed.
Lemma D_88b68 : decode_any W_88b68 = Some (Load SZ8 true 10 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88b6c : bv 32 := 0x07813083.
Lemma F_88b6c : fetch_word Plain.M.loaded_segments (0x88bc4 : word) = Some W_88b6c.
Proof. vm_refl. Qed.
Lemma D_88b6c : decode_any W_88b6c = Some (Load SZ8 true 1 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88b70 : bv 32 := 0x07013403.
Lemma F_88b70 : fetch_word Plain.M.loaded_segments (0x88bc8 : word) = Some W_88b70.
Proof. vm_refl. Qed.
Lemma D_88b70 : decode_any W_88b70 = Some (Load SZ8 true 8 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88b74 : bv 32 := 0x06813483.
Lemma F_88b74 : fetch_word Plain.M.loaded_segments (0x88bcc : word) = Some W_88b74.
Proof. vm_refl. Qed.
Lemma D_88b74 : decode_any W_88b74 = Some (Load SZ8 true 9 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88b78 : bv 32 := 0x06013903.
Lemma F_88b78 : fetch_word Plain.M.loaded_segments (0x88bd0 : word) = Some W_88b78.
Proof. vm_refl. Qed.
Lemma D_88b78 : decode_any W_88b78 = Some (Load SZ8 true 18 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88b7c : bv 32 := 0x05813983.
Lemma F_88b7c : fetch_word Plain.M.loaded_segments (0x88bd4 : word) = Some W_88b7c.
Proof. vm_refl. Qed.
Lemma D_88b7c : decode_any W_88b7c = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88b80 : bv 32 := 0x05013a03.
Lemma F_88b80 : fetch_word Plain.M.loaded_segments (0x88bd8 : word) = Some W_88b80.
Proof. vm_refl. Qed.
Lemma D_88b80 : decode_any W_88b80 = Some (Load SZ8 true 20 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88b84 : bv 32 := 0x04813a83.
Lemma F_88b84 : fetch_word Plain.M.loaded_segments (0x88bdc : word) = Some W_88b84.
Proof. vm_refl. Qed.
Lemma D_88b84 : decode_any W_88b84 = Some (Load SZ8 true 21 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88b88 : bv 32 := 0x04013b03.
Lemma F_88b88 : fetch_word Plain.M.loaded_segments (0x88be0 : word) = Some W_88b88.
Proof. vm_refl. Qed.
Lemma D_88b88 : decode_any W_88b88 = Some (Load SZ8 true 22 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88b8c : bv 32 := 0x03813b83.
Lemma F_88b8c : fetch_word Plain.M.loaded_segments (0x88be4 : word) = Some W_88b8c.
Proof. vm_refl. Qed.
Lemma D_88b8c : decode_any W_88b8c = Some (Load SZ8 true 23 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88b90 : bv 32 := 0x03013c03.
Lemma F_88b90 : fetch_word Plain.M.loaded_segments (0x88be8 : word) = Some W_88b90.
Proof. vm_refl. Qed.
Lemma D_88b90 : decode_any W_88b90 = Some (Load SZ8 true 24 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88b94 : bv 32 := 0x02813c83.
Lemma F_88b94 : fetch_word Plain.M.loaded_segments (0x88bec : word) = Some W_88b94.
Proof. vm_refl. Qed.
Lemma D_88b94 : decode_any W_88b94 = Some (Load SZ8 true 25 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88b98 : bv 32 := 0x02013d03.
Lemma F_88b98 : fetch_word Plain.M.loaded_segments (0x88bf0 : word) = Some W_88b98.
Proof. vm_refl. Qed.
Lemma D_88b98 : decode_any W_88b98 = Some (Load SZ8 true 26 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88b9c : bv 32 := 0x08010113.
Lemma F_88b9c : fetch_word Plain.M.loaded_segments (0x88bf4 : word) = Some W_88b9c.
Proof. vm_refl. Qed.
Lemma D_88b9c : decode_any W_88b9c = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88ba0 : bv 32 := 0x00008067.
Lemma F_88ba0 : fetch_word Plain.M.loaded_segments (0x88bf8 : word) = Some W_88ba0.
Proof. vm_refl. Qed.
Lemma D_88ba0 : decode_any W_88ba0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

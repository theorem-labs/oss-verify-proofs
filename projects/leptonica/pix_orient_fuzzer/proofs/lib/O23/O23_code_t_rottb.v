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
Definition W_88ba4 : bv 32 := 0xfb010113.
Lemma F_88ba4 : fetch_word Plain.M.loaded_segments (0x88bfc : word) = Some W_88ba4.
Proof. vm_refl. Qed.
Lemma D_88ba4 : decode_any W_88ba4 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88ba8 : bv 32 := 0x04113423.
Lemma F_88ba8 : fetch_word Plain.M.loaded_segments (0x88c00 : word) = Some W_88ba8.
Proof. vm_refl. Qed.
Lemma D_88ba8 : decode_any W_88ba8 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88bac : bv 32 := 0x04813023.
Lemma F_88bac : fetch_word Plain.M.loaded_segments (0x88c04 : word) = Some W_88bac.
Proof. vm_refl. Qed.
Lemma D_88bac : decode_any W_88bac = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88bb0 : bv 32 := 0x02913c23.
Lemma F_88bb0 : fetch_word Plain.M.loaded_segments (0x88c08 : word) = Some W_88bb0.
Proof. vm_refl. Qed.
Lemma D_88bb0 : decode_any W_88bb0 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88bb4 : bv 32 := 0x03213823.
Lemma F_88bb4 : fetch_word Plain.M.loaded_segments (0x88c0c : word) = Some W_88bb4.
Proof. vm_refl. Qed.
Lemma D_88bb4 : decode_any W_88bb4 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88bb8 : bv 32 := 0x03313423.
Lemma F_88bb8 : fetch_word Plain.M.loaded_segments (0x88c10 : word) = Some W_88bb8.
Proof. vm_refl. Qed.
Lemma D_88bb8 : decode_any W_88bb8 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88bbc : bv 32 := 0x03413023.
Lemma F_88bbc : fetch_word Plain.M.loaded_segments (0x88c14 : word) = Some W_88bbc.
Proof. vm_refl. Qed.
Lemma D_88bbc : decode_any W_88bbc = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88bc0 : bv 32 := 0x01513c23.
Lemma F_88bc0 : fetch_word Plain.M.loaded_segments (0x88c18 : word) = Some W_88bc0.
Proof. vm_refl. Qed.
Lemma D_88bc0 : decode_any W_88bc0 = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88bc4 : bv 32 := 0x01613823.
Lemma F_88bc4 : fetch_word Plain.M.loaded_segments (0x88c1c : word) = Some W_88bc4.
Proof. vm_refl. Qed.
Lemma D_88bc4 : decode_any W_88bc4 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88bc8 : bv 32 := 0x01713423.
Lemma F_88bc8 : fetch_word Plain.M.loaded_segments (0x88c20 : word) = Some W_88bc8.
Proof. vm_refl. Qed.
Lemma D_88bc8 : decode_any W_88bc8 = Some (Store SZ8 2 23 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88bcc : bv 32 := 0x10058063.
Lemma F_88bcc : fetch_word Plain.M.loaded_segments (0x88c24 : word) = Some W_88bcc.
Proof. vm_refl. Qed.
Lemma D_88bcc : decode_any W_88bcc = Some (Branch BC_EQ 11 0 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88bd0 : bv 32 := 0x00058413.
Lemma F_88bd0 : fetch_word Plain.M.loaded_segments (0x88c28 : word) = Some W_88bd0.
Proof. vm_refl. Qed.
Lemma D_88bd0 : decode_any W_88bd0 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88bd4 : bv 32 := 0x00050493.
Lemma F_88bd4 : fetch_word Plain.M.loaded_segments (0x88c2c : word) = Some W_88bd4.
Proof. vm_refl. Qed.
Lemma D_88bd4 : decode_any W_88bd4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88bd8 : bv 32 := 0x00410613.
Lemma F_88bd8 : fetch_word Plain.M.loaded_segments (0x88c30 : word) = Some W_88bd8.
Proof. vm_refl. Qed.
Lemma D_88bd8 : decode_any W_88bd8 = Some (OpImm ALU_ADD 12 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88bdc : bv 32 := 0x00010693.
Lemma F_88bdc : fetch_word Plain.M.loaded_segments (0x88c34 : word) = Some W_88bdc.
Proof. vm_refl. Qed.
Lemma D_88bdc : decode_any W_88bdc = Some (OpImm ALU_ADD 13 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88be0 : bv 32 := 0x00058513.
Lemma F_88be0 : fetch_word Plain.M.loaded_segments (0x88c38 : word) = Some W_88be0.
Proof. vm_refl. Qed.
Lemma D_88be0 : decode_any W_88be0 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88be4 : bv 32 := 0x00000593.
Lemma F_88be4 : fetch_word Plain.M.loaded_segments (0x88c3c : word) = Some W_88be4.
Proof. vm_refl. Qed.
Lemma D_88be4 : decode_any W_88be4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88be8 : bv 32 := 0x9b8e40ef.
Lemma F_88be8 : fetch_word Plain.M.loaded_segments (0x88c40 : word) = Some W_88be8.
Proof. vm_refl. Qed.
Lemma D_88be8 : decode_any W_88be8 = Some (Jal 1 1982904, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88bec : bv 32 := 0x00012503.
Lemma F_88bec : fetch_word Plain.M.loaded_segments (0x88c44 : word) = Some W_88bec.
Proof. vm_refl. Qed.
Lemma D_88bec : decode_any W_88bec = Some (Load SZ4 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88bf0 : bv 32 := 0x02000593.
Lemma F_88bf0 : fetch_word Plain.M.loaded_segments (0x88c48 : word) = Some W_88bf0.
Proof. vm_refl. Qed.
Lemma D_88bf0 : decode_any W_88bf0 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88bf4 : bv 32 := 0x18a5e663.
Lemma F_88bf4 : fetch_word Plain.M.loaded_segments (0x88c4c : word) = Some W_88bf4.
Proof. vm_refl. Qed.
Lemma D_88bf4 : decode_any W_88bf4 = Some (Branch BC_LTU 11 10 396, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88bf8 : bv 32 := 0x100015b7.
Lemma F_88bf8 : fetch_word Plain.M.loaded_segments (0x88c50 : word) = Some W_88bf8.
Proof. vm_refl. Qed.
Lemma D_88bf8 : decode_any W_88bf8 = Some (Lui 11 65537, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88bfc : bv 32 := 0x00459593.
Lemma F_88bfc : fetch_word Plain.M.loaded_segments (0x88c54 : word) = Some W_88bfc.
Proof. vm_refl. Qed.
Lemma D_88bfc : decode_any W_88bfc = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c00 : bv 32 := 0x11658593.
Lemma F_88c00 : fetch_word Plain.M.loaded_segments (0x88c58 : word) = Some W_88c00.
Proof. vm_refl. Qed.
Lemma D_88c00 : decode_any W_88c00 = Some (OpImm ALU_ADD 11 11 278, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c04 : bv 32 := 0x00a5d533.
Lemma F_88c04 : fetch_word Plain.M.loaded_segments (0x88c5c : word) = Some W_88c04.
Proof. vm_refl. Qed.
Lemma D_88c04 : decode_any W_88c04 = Some (Op ALU_SRL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c08 : bv 32 := 0x00157513.
Lemma F_88c08 : fetch_word Plain.M.loaded_segments (0x88c60 : word) = Some W_88c08.
Proof. vm_refl. Qed.
Lemma D_88c08 : decode_any W_88c08 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c0c : bv 32 := 0x16050a63.
Lemma F_88c0c : fetch_word Plain.M.loaded_segments (0x88c64 : word) = Some W_88c0c.
Proof. vm_refl. Qed.
Lemma D_88c0c : decode_any W_88c0c = Some (Branch BC_EQ 10 0 372, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c10 : bv 32 := 0x00048513.
Lemma F_88c10 : fetch_word Plain.M.loaded_segments (0x88c68 : word) = Some W_88c10.
Proof. vm_refl. Qed.
Lemma D_88c10 : decode_any W_88c10 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c14 : bv 32 := 0x00040593.
Lemma F_88c14 : fetch_word Plain.M.loaded_segments (0x88c6c : word) = Some W_88c14.
Proof. vm_refl. Qed.
Lemma D_88c14 : decode_any W_88c14 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c18 : bv 32 := 0x811e40ef.
Lemma F_88c18 : fetch_word Plain.M.loaded_segments (0x88c70 : word) = Some W_88c18.
Proof. vm_refl. Qed.
Lemma D_88c18 : decode_any W_88c18 = Some (Jal 1 1984528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c1c : bv 32 := 0x10050263.
Lemma F_88c1c : fetch_word Plain.M.loaded_segments (0x88c74 : word) = Some W_88c1c.
Proof. vm_refl. Qed.
Lemma D_88c1c : decode_any W_88c1c = Some (Branch BC_EQ 10 0 260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c20 : bv 32 := 0x00050913.
Lemma F_88c20 : fetch_word Plain.M.loaded_segments (0x88c78 : word) = Some W_88c20.
Proof. vm_refl. Qed.
Lemma D_88c20 : decode_any W_88c20 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c24 : bv 32 := 0xdc5e40ef.
Lemma F_88c24 : fetch_word Plain.M.loaded_segments (0x88c7c : word) = Some W_88c24.
Proof. vm_refl. Qed.
Lemma D_88c24 : decode_any W_88c24 = Some (Jal 1 1985988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c28 : bv 32 := 0x00050493.
Lemma F_88c28 : fetch_word Plain.M.loaded_segments (0x88c80 : word) = Some W_88c28.
Proof. vm_refl. Qed.
Lemma D_88c28 : decode_any W_88c28 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c2c : bv 32 := 0x00090413.
Lemma F_88c2c : fetch_word Plain.M.loaded_segments (0x88c84 : word) = Some W_88c2c.
Proof. vm_refl. Qed.
Lemma D_88c2c : decode_any W_88c2c = Some (OpImm ALU_ADD 8 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c30 : bv 32 := 0x00090513.
Lemma F_88c30 : fetch_word Plain.M.loaded_segments (0x88c88 : word) = Some W_88c30.
Proof. vm_refl. Qed.
Lemma D_88c30 : decode_any W_88c30 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c34 : bv 32 := 0xe71e30ef.
Lemma F_88c34 : fetch_word Plain.M.loaded_segments (0x88c8c : word) = Some W_88c34.
Proof. vm_refl. Qed.
Lemma D_88c34 : decode_any W_88c34 = Some (Jal 1 1982064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c38 : bv 32 := 0x00050a13.
Lemma F_88c38 : fetch_word Plain.M.loaded_segments (0x88c90 : word) = Some W_88c38.
Proof. vm_refl. Qed.
Lemma D_88c38 : decode_any W_88c38 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c3c : bv 32 := 0x00400593.
Lemma F_88c3c : fetch_word Plain.M.loaded_segments (0x88c94 : word) = Some W_88c3c.
Proof. vm_refl. Qed.
Lemma D_88c3c : decode_any W_88c3c = Some (OpImm ALU_ADD 11 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c40 : bv 32 := 0x5a4710ef.
Lemma F_88c40 : fetch_word Plain.M.loaded_segments (0x88c98 : word) = Some W_88c40.
Proof. vm_refl. Qed.
Lemma D_88c40 : decode_any W_88c40 = Some (Jal 1 464292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c44 : bv 32 := 0x10050263.
Lemma F_88c44 : fetch_word Plain.M.loaded_segments (0x88c9c : word) = Some W_88c44.
Proof. vm_refl. Qed.
Lemma D_88c44 : decode_any W_88c44 = Some (Branch BC_EQ 10 0 260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c48 : bv 32 := 0x00050913.
Lemma F_88c48 : fetch_word Plain.M.loaded_segments (0x88ca0 : word) = Some W_88c48.
Proof. vm_refl. Qed.
Lemma D_88c48 : decode_any W_88c48 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c4c : bv 32 := 0x00412503.
Lemma F_88c4c : fetch_word Plain.M.loaded_segments (0x88ca4 : word) = Some W_88c4c.
Proof. vm_refl. Qed.
Lemma D_88c4c : decode_any W_88c4c = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c50 : bv 32 := 0x00200593.
Lemma F_88c50 : fetch_word Plain.M.loaded_segments (0x88ca8 : word) = Some W_88c50.
Proof. vm_refl. Qed.
Lemma D_88c50 : decode_any W_88c50 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c54 : bv 32 := 0x06b54663.
Lemma F_88c54 : fetch_word Plain.M.loaded_segments (0x88cac : word) = Some W_88c54.
Proof. vm_refl. Qed.
Lemma D_88c54 : decode_any W_88c54 = Some (Branch BC_LT 10 11 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c58 : bv 32 := 0x02051593.
Lemma F_88c58 : fetch_word Plain.M.loaded_segments (0x88cb0 : word) = Some W_88c58.
Proof. vm_refl. Qed.
Lemma D_88c58 : decode_any W_88c58 = Some (ShiftImm ALU_SLL 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c5c : bv 32 := 0x002a199b.
Lemma F_88c5c : fetch_word Plain.M.loaded_segments (0x88cb4 : word) = Some W_88c5c.
Proof. vm_refl. Qed.
Lemma D_88c5c : decode_any W_88c5c = Some (ShiftImm32 ALU_SLL 19 20 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c60 : bv 32 := 0xfff50513.
Lemma F_88c60 : fetch_word Plain.M.loaded_segments (0x88cb8 : word) = Some W_88c60.
Proof. vm_refl. Qed.
Lemma D_88c60 : decode_any W_88c60 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c64 : bv 32 := 0x002a1a93.
Lemma F_88c64 : fetch_word Plain.M.loaded_segments (0x88cbc : word) = Some W_88c64.
Proof. vm_refl. Qed.
Lemma D_88c64 : decode_any W_88c64 = Some (ShiftImm ALU_SLL 21 20 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c68 : bv 32 := 0x0205d593.
Lemma F_88c68 : fetch_word Plain.M.loaded_segments (0x88cc0 : word) = Some W_88c68.
Proof. vm_refl. Qed.
Lemma D_88c68 : decode_any W_88c68 = Some (ShiftImm ALU_SRL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c6c : bv 32 := 0x03450533.
Lemma F_88c6c : fetch_word Plain.M.loaded_segments (0x88cc4 : word) = Some W_88c6c.
Proof. vm_refl. Qed.
Lemma D_88c6c : decode_any W_88c6c = Some (Mul M_MUL 10 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c70 : bv 32 := 0x0015db13.
Lemma F_88c70 : fetch_word Plain.M.loaded_segments (0x88cc8 : word) = Some W_88c70.
Proof. vm_refl. Qed.
Lemma D_88c70 : decode_any W_88c70 = Some (ShiftImm ALU_SRL 22 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c74 : bv 32 := 0x00251513.
Lemma F_88c74 : fetch_word Plain.M.loaded_segments (0x88ccc : word) = Some W_88c74.
Proof. vm_refl. Qed.
Lemma D_88c74 : decode_any W_88c74 = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c78 : bv 32 := 0x00a48a33.
Lemma F_88c78 : fetch_word Plain.M.loaded_segments (0x88cd0 : word) = Some W_88c78.
Proof. vm_refl. Qed.
Lemma D_88c78 : decode_any W_88c78 = Some (Op ALU_ADD 20 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c7c : bv 32 := 0x41500bb3.
Lemma F_88c7c : fetch_word Plain.M.loaded_segments (0x88cd4 : word) = Some W_88c7c.
Proof. vm_refl. Qed.
Lemma D_88c7c : decode_any W_88c7c = Some (Op ALU_SUB 23 0 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c80 : bv 32 := 0x00090513.
Lemma F_88c80 : fetch_word Plain.M.loaded_segments (0x88cd8 : word) = Some W_88c80.
Proof. vm_refl. Qed.
Lemma D_88c80 : decode_any W_88c80 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c84 : bv 32 := 0x00048593.
Lemma F_88c84 : fetch_word Plain.M.loaded_segments (0x88cdc : word) = Some W_88c84.
Proof. vm_refl. Qed.
Lemma D_88c84 : decode_any W_88c84 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c88 : bv 32 := 0x00098613.
Lemma F_88c88 : fetch_word Plain.M.loaded_segments (0x88ce0 : word) = Some W_88c88.
Proof. vm_refl. Qed.
Lemma D_88c88 : decode_any W_88c88 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c8c : bv 32 := 0x7cd800ef.
Lemma F_88c8c : fetch_word Plain.M.loaded_segments (0x88ce4 : word) = Some W_88c8c.
Proof. vm_refl. Qed.
Lemma D_88c8c : decode_any W_88c8c = Some (Jal 1 528332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c90 : bv 32 := 0x00048513.
Lemma F_88c90 : fetch_word Plain.M.loaded_segments (0x88ce8 : word) = Some W_88c90.
Proof. vm_refl. Qed.
Lemma D_88c90 : decode_any W_88c90 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c94 : bv 32 := 0x000a0593.
Lemma F_88c94 : fetch_word Plain.M.loaded_segments (0x88cec : word) = Some W_88c94.
Proof. vm_refl. Qed.
Lemma D_88c94 : decode_any W_88c94 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c98 : bv 32 := 0x00098613.
Lemma F_88c98 : fetch_word Plain.M.loaded_segments (0x88cf0 : word) = Some W_88c98.
Proof. vm_refl. Qed.
Lemma D_88c98 : decode_any W_88c98 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88c9c : bv 32 := 0x7bd800ef.
Lemma F_88c9c : fetch_word Plain.M.loaded_segments (0x88cf4 : word) = Some W_88c9c.
Proof. vm_refl. Qed.
Lemma D_88c9c : decode_any W_88c9c = Some (Jal 1 528316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88ca0 : bv 32 := 0x000a0513.
Lemma F_88ca0 : fetch_word Plain.M.loaded_segments (0x88cf8 : word) = Some W_88ca0.
Proof. vm_refl. Qed.
Lemma D_88ca0 : decode_any W_88ca0 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88ca4 : bv 32 := 0x00090593.
Lemma F_88ca4 : fetch_word Plain.M.loaded_segments (0x88cfc : word) = Some W_88ca4.
Proof. vm_refl. Qed.
Lemma D_88ca4 : decode_any W_88ca4 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88ca8 : bv 32 := 0x00098613.
Lemma F_88ca8 : fetch_word Plain.M.loaded_segments (0x88d00 : word) = Some W_88ca8.
Proof. vm_refl. Qed.
Lemma D_88ca8 : decode_any W_88ca8 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88cac : bv 32 := 0x7ad800ef.
Lemma F_88cac : fetch_word Plain.M.loaded_segments (0x88d04 : word) = Some W_88cac.
Proof. vm_refl. Qed.
Lemma D_88cac : decode_any W_88cac = Some (Jal 1 528300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88cb0 : bv 32 := 0x017a0a33.
Lemma F_88cb0 : fetch_word Plain.M.loaded_segments (0x88d08 : word) = Some W_88cb0.
Proof. vm_refl. Qed.
Lemma D_88cb0 : decode_any W_88cb0 = Some (Op ALU_ADD 20 20 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88cb4 : bv 32 := 0xfffb0b13.
Lemma F_88cb4 : fetch_word Plain.M.loaded_segments (0x88d0c : word) = Some W_88cb4.
Proof. vm_refl. Qed.
Lemma D_88cb4 : decode_any W_88cb4 = Some (OpImm ALU_ADD 22 22 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88cb8 : bv 32 := 0x015484b3.
Lemma F_88cb8 : fetch_word Plain.M.loaded_segments (0x88d10 : word) = Some W_88cb8.
Proof. vm_refl. Qed.
Lemma D_88cb8 : decode_any W_88cb8 = Some (Op ALU_ADD 9 9 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88cbc : bv 32 := 0xfc0b12e3.
Lemma F_88cbc : fetch_word Plain.M.loaded_segments (0x88d14 : word) = Some W_88cbc.
Proof. vm_refl. Qed.
Lemma D_88cbc : decode_any W_88cbc = Some (Branch BC_NE 22 0 8132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88cc0 : bv 32 := 0x00090513.
Lemma F_88cc0 : fetch_word Plain.M.loaded_segments (0x88d18 : word) = Some W_88cc0.
Proof. vm_refl. Qed.
Lemma D_88cc0 : decode_any W_88cc0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88cc4 : bv 32 := 0x658710ef.
Lemma F_88cc4 : fetch_word Plain.M.loaded_segments (0x88d1c : word) = Some W_88cc4.
Proof. vm_refl. Qed.
Lemma D_88cc4 : decode_any W_88cc4 = Some (Jal 1 464472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88cc8 : bv 32 := 0x0b00006f.
Lemma F_88cc8 : fetch_word Plain.M.loaded_segments (0x88d20 : word) = Some W_88cc8.
Proof. vm_refl. Qed.
Lemma D_88cc8 : decode_any W_88cc8 = Some (Jal 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88d78 : bv 32 := 0x00040513.
Lemma F_88d78 : fetch_word Plain.M.loaded_segments (0x88dd0 : word) = Some W_88d78.
Proof. vm_refl. Qed.
Lemma D_88d78 : decode_any W_88d78 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88d7c : bv 32 := 0x0380006f.
Lemma F_88d7c : fetch_word Plain.M.loaded_segments (0x88dd4 : word) = Some W_88d7c.
Proof. vm_refl. Qed.
Lemma D_88d7c : decode_any W_88d7c = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88db4 : bv 32 := 0x04813083.
Lemma F_88db4 : fetch_word Plain.M.loaded_segments (0x88e0c : word) = Some W_88db4.
Proof. vm_refl. Qed.
Lemma D_88db4 : decode_any W_88db4 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88db8 : bv 32 := 0x04013403.
Lemma F_88db8 : fetch_word Plain.M.loaded_segments (0x88e10 : word) = Some W_88db8.
Proof. vm_refl. Qed.
Lemma D_88db8 : decode_any W_88db8 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88dbc : bv 32 := 0x03813483.
Lemma F_88dbc : fetch_word Plain.M.loaded_segments (0x88e14 : word) = Some W_88dbc.
Proof. vm_refl. Qed.
Lemma D_88dbc : decode_any W_88dbc = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88dc0 : bv 32 := 0x03013903.
Lemma F_88dc0 : fetch_word Plain.M.loaded_segments (0x88e18 : word) = Some W_88dc0.
Proof. vm_refl. Qed.
Lemma D_88dc0 : decode_any W_88dc0 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88dc4 : bv 32 := 0x02813983.
Lemma F_88dc4 : fetch_word Plain.M.loaded_segments (0x88e1c : word) = Some W_88dc4.
Proof. vm_refl. Qed.
Lemma D_88dc4 : decode_any W_88dc4 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88dc8 : bv 32 := 0x02013a03.
Lemma F_88dc8 : fetch_word Plain.M.loaded_segments (0x88e20 : word) = Some W_88dc8.
Proof. vm_refl. Qed.
Lemma D_88dc8 : decode_any W_88dc8 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88dcc : bv 32 := 0x01813a83.
Lemma F_88dcc : fetch_word Plain.M.loaded_segments (0x88e24 : word) = Some W_88dcc.
Proof. vm_refl. Qed.
Lemma D_88dcc : decode_any W_88dcc = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88dd0 : bv 32 := 0x01013b03.
Lemma F_88dd0 : fetch_word Plain.M.loaded_segments (0x88e28 : word) = Some W_88dd0.
Proof. vm_refl. Qed.
Lemma D_88dd0 : decode_any W_88dd0 = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88dd4 : bv 32 := 0x00813b83.
Lemma F_88dd4 : fetch_word Plain.M.loaded_segments (0x88e2c : word) = Some W_88dd4.
Proof. vm_refl. Qed.
Lemma D_88dd4 : decode_any W_88dd4 = Some (Load SZ8 true 23 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88dd8 : bv 32 := 0x05010113.
Lemma F_88dd8 : fetch_word Plain.M.loaded_segments (0x88e30 : word) = Some W_88dd8.
Proof. vm_refl. Qed.
Lemma D_88dd8 : decode_any W_88dd8 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_88ddc : bv 32 := 0x00008067.
Lemma F_88ddc : fetch_word Plain.M.loaded_segments (0x88e34 : word) = Some W_88ddc.
Proof. vm_refl. Qed.
Lemma D_88ddc : decode_any W_88ddc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

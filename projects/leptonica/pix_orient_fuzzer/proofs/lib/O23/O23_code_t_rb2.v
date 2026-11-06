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
Definition W_6cef0 : bv 32 := 0x02058063.
Lemma F_6cef0 : fetch_word Plain.M.loaded_segments (0x6cf48 : word) = Some W_6cef0.
Proof. vm_refl. Qed.
Lemma D_6cef0 : decode_any W_6cef0 = Some (Branch BC_EQ 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cef4 : bv 32 := 0x04050463.
Lemma F_6cef4 : fetch_word Plain.M.loaded_segments (0x6cf4c : word) = Some W_6cef4.
Proof. vm_refl. Qed.
Lemma D_6cef4 : decode_any W_6cef4 = Some (Branch BC_EQ 10 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cef8 : bv 32 := 0x06a58c63.
Lemma F_6cef8 : fetch_word Plain.M.loaded_segments (0x6cf50 : word) = Some W_6cef8.
Proof. vm_refl. Qed.
Lemma D_6cef8 : decode_any W_6cef8 = Some (Branch BC_EQ 11 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cefc : bv 32 := 0x00050613.
Lemma F_6cefc : fetch_word Plain.M.loaded_segments (0x6cf54 : word) = Some W_6cefc.
Proof. vm_refl. Qed.
Lemma D_6cefc : decode_any W_6cefc = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf00 : bv 32 := 0x00000513.
Lemma F_6cf00 : fetch_word Plain.M.loaded_segments (0x6cf58 : word) = Some W_6cf00.
Proof. vm_refl. Qed.
Lemma D_6cf00 : decode_any W_6cf00 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf04 : bv 32 := 0x0185b583.
Lemma F_6cf04 : fetch_word Plain.M.loaded_segments (0x6cf5c : word) = Some W_6cf04.
Proof. vm_refl. Qed.
Lemma D_6cf04 : decode_any W_6cf04 = Some (Load SZ8 true 11 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf08 : bv 32 := 0x00b63c23.
Lemma F_6cf08 : fetch_word Plain.M.loaded_segments (0x6cf60 : word) = Some W_6cf08.
Proof. vm_refl. Qed.
Lemma D_6cf08 : decode_any W_6cf08 = Some (Store SZ8 12 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf0c : bv 32 := 0x00008067.
Lemma F_6cf0c : fetch_word Plain.M.loaded_segments (0x6cf64 : word) = Some W_6cf0c.
Proof. vm_refl. Qed.
Lemma D_6cf0c : decode_any W_6cf0c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

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
Definition W_940a4 : bv 32 := 0xfa010113.
Lemma F_940a4 : fetch_word Plain.M.loaded_segments (0x940fc : word) = Some W_940a4.
Proof. vm_refl. Qed.
Lemma D_940a4 : decode_any W_940a4 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_940a8 : bv 32 := 0x04113c23.
Lemma F_940a8 : fetch_word Plain.M.loaded_segments (0x94100 : word) = Some W_940a8.
Proof. vm_refl. Qed.
Lemma D_940a8 : decode_any W_940a8 = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_940ac : bv 32 := 0x04813823.
Lemma F_940ac : fetch_word Plain.M.loaded_segments (0x94104 : word) = Some W_940ac.
Proof. vm_refl. Qed.
Lemma D_940ac : decode_any W_940ac = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_940b0 : bv 32 := 0x04913423.
Lemma F_940b0 : fetch_word Plain.M.loaded_segments (0x94108 : word) = Some W_940b0.
Proof. vm_refl. Qed.
Lemma D_940b0 : decode_any W_940b0 = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_940b4 : bv 32 := 0x05213023.
Lemma F_940b4 : fetch_word Plain.M.loaded_segments (0x9410c : word) = Some W_940b4.
Proof. vm_refl. Qed.
Lemma D_940b4 : decode_any W_940b4 = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_940b8 : bv 32 := 0x03313c23.
Lemma F_940b8 : fetch_word Plain.M.loaded_segments (0x94110 : word) = Some W_940b8.
Proof. vm_refl. Qed.
Lemma D_940b8 : decode_any W_940b8 = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_940bc : bv 32 := 0x03413823.
Lemma F_940bc : fetch_word Plain.M.loaded_segments (0x94114 : word) = Some W_940bc.
Proof. vm_refl. Qed.
Lemma D_940bc : decode_any W_940bc = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_940c0 : bv 32 := 0x03513423.
Lemma F_940c0 : fetch_word Plain.M.loaded_segments (0x94118 : word) = Some W_940c0.
Proof. vm_refl. Qed.
Lemma D_940c0 : decode_any W_940c0 = Some (Store SZ8 2 21 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_940c4 : bv 32 := 0x03613023.
Lemma F_940c4 : fetch_word Plain.M.loaded_segments (0x9411c : word) = Some W_940c4.
Proof. vm_refl. Qed.
Lemma D_940c4 : decode_any W_940c4 = Some (Store SZ8 2 22 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_940c8 : bv 32 := 0x01713c23.
Lemma F_940c8 : fetch_word Plain.M.loaded_segments (0x94120 : word) = Some W_940c8.
Proof. vm_refl. Qed.
Lemma D_940c8 : decode_any W_940c8 = Some (Store SZ8 2 23 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_940cc : bv 32 := 0x04050863.
Lemma F_940cc : fetch_word Plain.M.loaded_segments (0x94124 : word) = Some W_940cc.
Proof. vm_refl. Qed.
Lemma D_940cc : decode_any W_940cc = Some (Branch BC_EQ 10 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_940d0 : bv 32 := 0x00058993.
Lemma F_940d0 : fetch_word Plain.M.loaded_segments (0x94128 : word) = Some W_940d0.
Proof. vm_refl. Qed.
Lemma D_940d0 : decode_any W_940d0 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_940d4 : bv 32 := 0x00050493.
Lemma F_940d4 : fetch_word Plain.M.loaded_segments (0x9412c : word) = Some W_940d4.
Proof. vm_refl. Qed.
Lemma D_940d4 : decode_any W_940d4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_940d8 : bv 32 := 0x00060b93.
Lemma F_940d8 : fetch_word Plain.M.loaded_segments (0x94130 : word) = Some W_940d8.
Proof. vm_refl. Qed.
Lemma D_940d8 : decode_any W_940d8 = Some (OpImm ALU_ADD 23 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_940dc : bv 32 := 0x84dd90ef.
Lemma F_940dc : fetch_word Plain.M.loaded_segments (0x94134 : word) = Some W_940dc.
Proof. vm_refl. Qed.
Lemma D_940dc : decode_any W_940dc = Some (Jal 1 1939532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_940e0 : bv 32 := 0x00100593.
Lemma F_940e0 : fetch_word Plain.M.loaded_segments (0x94138 : word) = Some W_940e0.
Proof. vm_refl. Qed.
Lemma D_940e0 : decode_any W_940e0 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_940e4 : bv 32 := 0x06b51063.
Lemma F_940e4 : fetch_word Plain.M.loaded_segments (0x9413c : word) = Some W_940e4.
Proof. vm_refl. Qed.
Lemma D_940e4 : decode_any W_940e4 = Some (Branch BC_NE 10 11 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_940e8 : bv 32 := 0xffb9851b.
Lemma F_940e8 : fetch_word Plain.M.loaded_segments (0x94140 : word) = Some W_940e8.
Proof. vm_refl. Qed.
Lemma D_940e8 : decode_any W_940e8 = Some (OpImm32 10 19 4091, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_940ec : bv 32 := 0xffb00593.
Lemma F_940ec : fetch_word Plain.M.loaded_segments (0x94144 : word) = Some W_940ec.
Proof. vm_refl. Qed.
Lemma D_940ec : decode_any W_940ec = Some (OpImm ALU_ADD 11 0 4091, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_940f0 : bv 32 := 0x0aa5e463.
Lemma F_940f0 : fetch_word Plain.M.loaded_segments (0x94148 : word) = Some W_940f0.
Proof. vm_refl. Qed.
Lemma D_940f0 : decode_any W_940f0 = Some (Branch BC_LTU 11 10 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94198 : bv 32 := 0x01410593.
Lemma F_94198 : fetch_word Plain.M.loaded_segments (0x941f0 : word) = Some W_94198.
Proof. vm_refl. Qed.
Lemma D_94198 : decode_any W_94198 = Some (OpImm ALU_ADD 11 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9419c : bv 32 := 0x01010613.
Lemma F_9419c : fetch_word Plain.M.loaded_segments (0x941f4 : word) = Some W_9419c.
Proof. vm_refl. Qed.
Lemma D_9419c : decode_any W_9419c = Some (OpImm ALU_ADD 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941a0 : bv 32 := 0x00048513.
Lemma F_941a0 : fetch_word Plain.M.loaded_segments (0x941f8 : word) = Some W_941a0.
Proof. vm_refl. Qed.
Lemma D_941a0 : decode_any W_941a0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941a4 : bv 32 := 0x00000693.
Lemma F_941a4 : fetch_word Plain.M.loaded_segments (0x941fc : word) = Some W_941a4.
Proof. vm_refl. Qed.
Lemma D_941a4 : decode_any W_941a4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941a8 : bv 32 := 0xbf9d80ef.
Lemma F_941a8 : fetch_word Plain.M.loaded_segments (0x94200 : word) = Some W_941a8.
Proof. vm_refl. Qed.
Lemma D_941a8 : decode_any W_941a8 = Some (Jal 1 1936376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941ac : bv 32 := 0x01012503.
Lemma F_941ac : fetch_word Plain.M.loaded_segments (0x94204 : word) = Some W_941ac.
Proof. vm_refl. Qed.
Lemma D_941ac : decode_any W_941ac = Some (Load SZ4 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941b0 : bv 32 := 0x00100593.
Lemma F_941b0 : fetch_word Plain.M.loaded_segments (0x94208 : word) = Some W_941b0.
Proof. vm_refl. Qed.
Lemma D_941b0 : decode_any W_941b0 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941b4 : bv 32 := 0x02a5c663.
Lemma F_941b4 : fetch_word Plain.M.loaded_segments (0x9420c : word) = Some W_941b4.
Proof. vm_refl. Qed.
Lemma D_941b4 : decode_any W_941b4 = Some (Branch BC_LT 11 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941b8 : bv 32 := 0x0007e517.
Lemma F_941b8 : fetch_word Plain.M.loaded_segments (0x94210 : word) = Some W_941b8.
Proof. vm_refl. Qed.
Lemma D_941b8 : decode_any W_941b8 = Some (Auipc 10 126, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941bc : bv 32 := 0x3b853503.
Lemma F_941bc : fetch_word Plain.M.loaded_segments (0x94214 : word) = Some W_941bc.
Proof. vm_refl. Qed.
Lemma D_941bc : decode_any W_941bc = Some (Load SZ8 true 10 10 952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941c0 : bv 32 := 0x00052503.
Lemma F_941c0 : fetch_word Plain.M.loaded_segments (0x94218 : word) = Some W_941c0.
Proof. vm_refl. Qed.
Lemma D_941c0 : decode_any W_941c0 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941c4 : bv 32 := 0x00500593.
Lemma F_941c4 : fetch_word Plain.M.loaded_segments (0x9421c : word) = Some W_941c4.
Proof. vm_refl. Qed.
Lemma D_941c4 : decode_any W_941c4 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941c8 : bv 32 := 0x4aa5cc63.
Lemma F_941c8 : fetch_word Plain.M.loaded_segments (0x94220 : word) = Some W_941c8.
Proof. vm_refl. Qed.
Lemma D_941c8 : decode_any W_941c8 = Some (Branch BC_LT 11 10 1208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941cc : bv 32 := 0xfff82517.
Lemma F_941cc : fetch_word Plain.M.loaded_segments (0x94224 : word) = Some W_941cc.
Proof. vm_refl. Qed.
Lemma D_941cc : decode_any W_941cc = Some (Auipc 10 1048450, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941d0 : bv 32 := 0xfff82597.
Lemma F_941d0 : fetch_word Plain.M.loaded_segments (0x94228 : word) = Some W_941d0.
Proof. vm_refl. Qed.
Lemma D_941d0 : decode_any W_941d0 = Some (Auipc 11 1048450, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941d4 : bv 32 := 0x13050513.
Lemma F_941d4 : fetch_word Plain.M.loaded_segments (0x9422c : word) = Some W_941d4.
Proof. vm_refl. Qed.
Lemma D_941d4 : decode_any W_941d4 = Some (OpImm ALU_ADD 10 10 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941d8 : bv 32 := 0x14258593.
Lemma F_941d8 : fetch_word Plain.M.loaded_segments (0x94230 : word) = Some W_941d8.
Proof. vm_refl. Qed.
Lemma D_941d8 : decode_any W_941d8 = Some (OpImm ALU_ADD 11 11 322, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941dc : bv 32 := 0x1c80006f.
Lemma F_941dc : fetch_word Plain.M.loaded_segments (0x94234 : word) = Some W_941dc.
Proof. vm_refl. Qed.
Lemma D_941dc : decode_any W_941dc = Some (Jal 0 456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941e0 : bv 32 := 0x00048513.
Lemma F_941e0 : fetch_word Plain.M.loaded_segments (0x94238 : word) = Some W_941e0.
Proof. vm_refl. Qed.
Lemma D_941e0 : decode_any W_941e0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941e4 : bv 32 := 0x8c1d80ef.
Lemma F_941e4 : fetch_word Plain.M.loaded_segments (0x9423c : word) = Some W_941e4.
Proof. vm_refl. Qed.
Lemma D_941e4 : decode_any W_941e4 = Some (Jal 1 1935552, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941e8 : bv 32 := 0x00050913.
Lemma F_941e8 : fetch_word Plain.M.loaded_segments (0x94240 : word) = Some W_941e8.
Proof. vm_refl. Qed.
Lemma D_941e8 : decode_any W_941e8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941ec : bv 32 := 0x00048513.
Lemma F_941ec : fetch_word Plain.M.loaded_segments (0x94244 : word) = Some W_941ec.
Proof. vm_refl. Qed.
Lemma D_941ec : decode_any W_941ec = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941f0 : bv 32 := 0xff8d90ef.
Lemma F_941f0 : fetch_word Plain.M.loaded_segments (0x94248 : word) = Some W_941f0.
Proof. vm_refl. Qed.
Lemma D_941f0 : decode_any W_941f0 = Some (Jal 1 1939448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941f4 : bv 32 := 0x00050413.
Lemma F_941f4 : fetch_word Plain.M.loaded_segments (0x9424c : word) = Some W_941f4.
Proof. vm_refl. Qed.
Lemma D_941f4 : decode_any W_941f4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941f8 : bv 32 := 0x00048513.
Lemma F_941f8 : fetch_word Plain.M.loaded_segments (0x94250 : word) = Some W_941f8.
Proof. vm_refl. Qed.
Lemma D_941f8 : decode_any W_941f8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_941fc : bv 32 := 0x00000593.
Lemma F_941fc : fetch_word Plain.M.loaded_segments (0x94254 : word) = Some W_941fc.
Proof. vm_refl. Qed.
Lemma D_941fc : decode_any W_941fc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94200 : bv 32 := 0xac5da0ef.
Lemma F_94200 : fetch_word Plain.M.loaded_segments (0x94258 : word) = Some W_94200.
Proof. vm_refl. Qed.
Lemma D_94200 : decode_any W_94200 = Some (Jal 1 1944260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94204 : bv 32 := 0x01412503.
Lemma F_94204 : fetch_word Plain.M.loaded_segments (0x9425c : word) = Some W_94204.
Proof. vm_refl. Qed.
Lemma D_94204 : decode_any W_94204 = Some (Load SZ4 true 10 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94208 : bv 32 := 0x01012583.
Lemma F_94208 : fetch_word Plain.M.loaded_segments (0x94260 : word) = Some W_94208.
Proof. vm_refl. Qed.
Lemma D_94208 : decode_any W_94208 = Some (Load SZ4 true 11 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9420c : bv 32 := 0x01f5561b.
Lemma F_9420c : fetch_word Plain.M.loaded_segments (0x94264 : word) = Some W_9420c.
Proof. vm_refl. Qed.
Lemma D_9420c : decode_any W_9420c = Some (ShiftImm32 ALU_SRL 12 10 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94210 : bv 32 := 0x00c50533.
Lemma F_94210 : fetch_word Plain.M.loaded_segments (0x94268 : word) = Some W_94210.
Proof. vm_refl. Qed.
Lemma D_94210 : decode_any W_94210 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94214 : bv 32 := 0x01f5d61b.
Lemma F_94214 : fetch_word Plain.M.loaded_segments (0x9426c : word) = Some W_94214.
Proof. vm_refl. Qed.
Lemma D_94214 : decode_any W_94214 = Some (ShiftImm32 ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94218 : bv 32 := 0x00c585b3.
Lemma F_94218 : fetch_word Plain.M.loaded_segments (0x94270 : word) = Some W_94218.
Proof. vm_refl. Qed.
Lemma D_94218 : decode_any W_94218 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9421c : bv 32 := 0x4015551b.
Lemma F_9421c : fetch_word Plain.M.loaded_segments (0x94274 : word) = Some W_9421c.
Proof. vm_refl. Qed.
Lemma D_9421c : decode_any W_9421c = Some (ShiftImm32 ALU_SRA 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94220 : bv 32 := 0x4015d59b.
Lemma F_94220 : fetch_word Plain.M.loaded_segments (0x94278 : word) = Some W_94220.
Proof. vm_refl. Qed.
Lemma D_94220 : decode_any W_94220 = Some (ShiftImm32 ALU_SRA 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94224 : bv 32 := 0x00100613.
Lemma F_94224 : fetch_word Plain.M.loaded_segments (0x9427c : word) = Some W_94224.
Proof. vm_refl. Qed.
Lemma D_94224 : decode_any W_94224 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94228 : bv 32 := 0xbb8d80ef.
Lemma F_94228 : fetch_word Plain.M.loaded_segments (0x94280 : word) = Some W_94228.
Proof. vm_refl. Qed.
Lemma D_94228 : decode_any W_94228 = Some (Jal 1 1934264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9422c : bv 32 := 0x00a13423.
Lemma F_9422c : fetch_word Plain.M.loaded_segments (0x94284 : word) = Some W_9422c.
Proof. vm_refl. Qed.
Lemma D_9422c : decode_any W_9422c = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94230 : bv 32 := 0x14050863.
Lemma F_94230 : fetch_word Plain.M.loaded_segments (0x94288 : word) = Some W_94230.
Proof. vm_refl. Qed.
Lemma D_94230 : decode_any W_94230 = Some (Branch BC_EQ 10 0 336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94234 : bv 32 := 0x00050a93.
Lemma F_94234 : fetch_word Plain.M.loaded_segments (0x9428c : word) = Some W_94234.
Proof. vm_refl. Qed.
Lemma D_94234 : decode_any W_94234 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94238 : bv 32 := 0x00048593.
Lemma F_94238 : fetch_word Plain.M.loaded_segments (0x94290 : word) = Some W_94238.
Proof. vm_refl. Qed.
Lemma D_94238 : decode_any W_94238 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9423c : bv 32 := 0xcb5d80ef.
Lemma F_9423c : fetch_word Plain.M.loaded_segments (0x94294 : word) = Some W_9423c.
Proof. vm_refl. Qed.
Lemma D_9423c : decode_any W_9423c = Some (Jal 1 1936564, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94240 : bv 32 := 0x3f000537.
Lemma F_94240 : fetch_word Plain.M.loaded_segments (0x94298 : word) = Some W_94240.
Proof. vm_refl. Qed.
Lemma D_94240 : decode_any W_94240 = Some (Lui 10 258048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94244 : bv 32 := 0xf0050553.
Lemma F_94244 : fetch_word Plain.M.loaded_segments (0x9429c : word) = Some W_94244.
Proof. vm_refl. Qed.
Lemma D_94244 : decode_any W_94244 = Some (Fmv FMV_F_X FMT_S 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94248 : bv 32 := 0x000a8513.
Lemma F_94248 : fetch_word Plain.M.loaded_segments (0x942a0 : word) = Some W_94248.
Proof. vm_refl. Qed.
Lemma D_94248 : decode_any W_94248 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9424c : bv 32 := 0x20a505d3.
Lemma F_9424c : fetch_word Plain.M.loaded_segments (0x942a4 : word) = Some W_9424c.
Proof. vm_refl. Qed.
Lemma D_9424c : decode_any W_9424c = Some (Fsgnj F_SGNJ FMT_S 11 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94250 : bv 32 := 0xc55d90ef.
Lemma F_94250 : fetch_word Plain.M.loaded_segments (0x942a8 : word) = Some W_94250.
Proof. vm_refl. Qed.
Lemma D_94250 : decode_any W_94250 = Some (Jal 1 1940564, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94254 : bv 32 := 0x000a8513.
Lemma F_94254 : fetch_word Plain.M.loaded_segments (0x942ac : word) = Some W_94254.
Proof. vm_refl. Qed.
Lemma D_94254 : decode_any W_94254 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94258 : bv 32 := 0x84dd80ef.
Lemma F_94258 : fetch_word Plain.M.loaded_segments (0x942b0 : word) = Some W_94258.
Proof. vm_refl. Qed.
Lemma D_94258 : decode_any W_94258 = Some (Jal 1 1935436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9425c : bv 32 := 0x00050a13.
Lemma F_9425c : fetch_word Plain.M.loaded_segments (0x942b4 : word) = Some W_9425c.
Proof. vm_refl. Qed.
Lemma D_9425c : decode_any W_9425c = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94260 : bv 32 := 0x000a8b13.
Lemma F_94260 : fetch_word Plain.M.loaded_segments (0x942b8 : word) = Some W_94260.
Proof. vm_refl. Qed.
Lemma D_94260 : decode_any W_94260 = Some (OpImm ALU_ADD 22 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94264 : bv 32 := 0x000a8513.
Lemma F_94264 : fetch_word Plain.M.loaded_segments (0x942bc : word) = Some W_94264.
Proof. vm_refl. Qed.
Lemma D_94264 : decode_any W_94264 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94268 : bv 32 := 0xf80d90ef.
Lemma F_94268 : fetch_word Plain.M.loaded_segments (0x942c0 : word) = Some W_94268.
Proof. vm_refl. Qed.
Lemma D_94268 : decode_any W_94268 = Some (Jal 1 1939328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9426c : bv 32 := 0x00050493.
Lemma F_9426c : fetch_word Plain.M.loaded_segments (0x942c4 : word) = Some W_9426c.
Proof. vm_refl. Qed.
Lemma D_9426c : decode_any W_9426c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94270 : bv 32 := 0x000b8613.
Lemma F_94270 : fetch_word Plain.M.loaded_segments (0x942c8 : word) = Some W_94270.
Proof. vm_refl. Qed.
Lemma D_94270 : decode_any W_94270 = Some (OpImm ALU_ADD 12 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94274 : bv 32 := 0x000b8593.
Lemma F_94274 : fetch_word Plain.M.loaded_segments (0x942cc : word) = Some W_94274.
Proof. vm_refl. Qed.
Lemma D_94274 : decode_any W_94274 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94278 : bv 32 := 0x000b9a63.
Lemma F_94278 : fetch_word Plain.M.loaded_segments (0x942d0 : word) = Some W_94278.
Proof. vm_refl. Qed.
Lemma D_94278 : decode_any W_94278 = Some (Branch BC_NE 23 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9428c : bv 32 := 0x001a151b.
Lemma F_9428c : fetch_word Plain.M.loaded_segments (0x942e4 : word) = Some W_9428c.
Proof. vm_refl. Qed.
Lemma D_9428c : decode_any W_9428c = Some (ShiftImm32 ALU_SLL 10 20 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94290 : bv 32 := 0x00090693.
Lemma F_94290 : fetch_word Plain.M.loaded_segments (0x942e8 : word) = Some W_94290.
Proof. vm_refl. Qed.
Lemma D_94290 : decode_any W_94290 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94294 : bv 32 := 0x00a94463.
Lemma F_94294 : fetch_word Plain.M.loaded_segments (0x942ec : word) = Some W_94294.
Proof. vm_refl. Qed.
Lemma D_94294 : decode_any W_94294 = Some (Branch BC_LT 18 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94298 : bv 32 := 0x00050693.
Lemma F_94298 : fetch_word Plain.M.loaded_segments (0x942f0 : word) = Some W_94298.
Proof. vm_refl. Qed.
Lemma D_94298 : decode_any W_94298 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9429c : bv 32 := 0x01012783.
Lemma F_9429c : fetch_word Plain.M.loaded_segments (0x942f4 : word) = Some W_9429c.
Proof. vm_refl. Qed.
Lemma D_9429c : decode_any W_9429c = Some (Load SZ4 true 15 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942a0 : bv 32 := 0x00200713.
Lemma F_942a0 : fetch_word Plain.M.loaded_segments (0x942f8 : word) = Some W_942a0.
Proof. vm_refl. Qed.
Lemma D_942a0 : decode_any W_942a0 = Some (OpImm ALU_ADD 14 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942a4 : bv 32 := 0x000b0513.
Lemma F_942a4 : fetch_word Plain.M.loaded_segments (0x942fc : word) = Some W_942a4.
Proof. vm_refl. Qed.
Lemma D_942a4 : decode_any W_942a4 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942a8 : bv 32 := 0x11374463.
Lemma F_942a8 : fetch_word Plain.M.loaded_segments (0x94300 : word) = Some W_942a8.
Proof. vm_refl. Qed.
Lemma D_942a8 : decode_any W_942a8 = Some (Branch BC_LT 14 19 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942ac : bv 32 := 0x00100713.
Lemma F_942ac : fetch_word Plain.M.loaded_segments (0x94304 : word) = Some W_942ac.
Proof. vm_refl. Qed.
Lemma D_942ac : decode_any W_942ac = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942b0 : bv 32 := 0x1ee99263.
Lemma F_942b0 : fetch_word Plain.M.loaded_segments (0x94308 : word) = Some W_942b0.
Proof. vm_refl. Qed.
Lemma D_942b0 : decode_any W_942b0 = Some (Branch BC_NE 19 14 484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942b4 : bv 32 := 0x00200713.
Lemma F_942b4 : fetch_word Plain.M.loaded_segments (0x9430c : word) = Some W_942b4.
Proof. vm_refl. Qed.
Lemma D_942b4 : decode_any W_942b4 = Some (OpImm ALU_ADD 14 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942b8 : bv 32 := 0x38e7c263.
Lemma F_942b8 : fetch_word Plain.M.loaded_segments (0x94310 : word) = Some W_942b8.
Proof. vm_refl. Qed.
Lemma D_942b8 : decode_any W_942b8 = Some (Branch BC_LT 15 14 900, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942bc : bv 32 := 0x00000713.
Lemma F_942bc : fetch_word Plain.M.loaded_segments (0x94314 : word) = Some W_942bc.
Proof. vm_refl. Qed.
Lemma D_942bc : decode_any W_942bc = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942c0 : bv 32 := 0xaaaab837.
Lemma F_942c0 : fetch_word Plain.M.loaded_segments (0x94318 : word) = Some W_942c0.
Proof. vm_refl. Qed.
Lemma D_942c0 : decode_any W_942c0 = Some (Lui 16 699051, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942c4 : bv 32 := 0xffe78893.
Lemma F_942c4 : fetch_word Plain.M.loaded_segments (0x9431c : word) = Some W_942c4.
Proof. vm_refl. Qed.
Lemma D_942c4 : decode_any W_942c4 = Some (OpImm ALU_ADD 17 15 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942c8 : bv 32 := 0x002a1a13.
Lemma F_942c8 : fetch_word Plain.M.loaded_segments (0x94320 : word) = Some W_942c8.
Proof. vm_refl. Qed.
Lemma D_942c8 : decode_any W_942c8 = Some (ShiftImm ALU_SLL 20 20 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942cc : bv 32 := 0x00291293.
Lemma F_942cc : fetch_word Plain.M.loaded_segments (0x94324 : word) = Some W_942cc.
Proof. vm_refl. Qed.
Lemma D_942cc : decode_any W_942cc = Some (ShiftImm ALU_SLL 5 18 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942d0 : bv 32 := 0x00391913.
Lemma F_942d0 : fetch_word Plain.M.loaded_segments (0x94328 : word) = Some W_942d0.
Proof. vm_refl. Qed.
Lemma D_942d0 : decode_any W_942d0 = Some (ShiftImm ALU_SLL 18 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942d4 : bv 32 := 0x02069313.
Lemma F_942d4 : fetch_word Plain.M.loaded_segments (0x9432c : word) = Some W_942d4.
Proof. vm_refl. Qed.
Lemma D_942d4 : decode_any W_942d4 = Some (ShiftImm ALU_SLL 6 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942d8 : bv 32 := 0xaaa80793.
Lemma F_942d8 : fetch_word Plain.M.loaded_segments (0x94330 : word) = Some W_942d8.
Proof. vm_refl. Qed.
Lemma D_942d8 : decode_any W_942d8 = Some (OpImm ALU_ADD 15 16 2730, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942dc : bv 32 := 0x0018d89b.
Lemma F_942dc : fetch_word Plain.M.loaded_segments (0x94334 : word) = Some W_942dc.
Proof. vm_refl. Qed.
Lemma D_942dc : decode_any W_942dc = Some (ShiftImm32 ALU_SRL 17 17 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942e0 : bv 32 := 0x00540833.
Lemma F_942e0 : fetch_word Plain.M.loaded_segments (0x94338 : word) = Some W_942e0.
Proof. vm_refl. Qed.
Lemma D_942e0 : decode_any W_942e0 = Some (Op ALU_ADD 16 8 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942e4 : bv 32 := 0x01f35293.
Lemma F_942e4 : fetch_word Plain.M.loaded_segments (0x9433c : word) = Some W_942e4.
Proof. vm_refl. Qed.
Lemma D_942e4 : decode_any W_942e4 = Some (ShiftImm ALU_SRL 5 6 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942e8 : bv 32 := 0x0018889b.
Lemma F_942e8 : fetch_word Plain.M.loaded_segments (0x94340 : word) = Some W_942e8.
Proof. vm_refl. Qed.
Lemma D_942e8 : decode_any W_942e8 = Some (OpImm32 17 17 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942ec : bv 32 := 0x005482b3.
Lemma F_942ec : fetch_word Plain.M.loaded_segments (0x94344 : word) = Some W_942ec.
Proof. vm_refl. Qed.
Lemma D_942ec : decode_any W_942ec = Some (Op ALU_ADD 5 9 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942f0 : bv 32 := 0x0180006f.
Lemma F_942f0 : fetch_word Plain.M.loaded_segments (0x94348 : word) = Some W_942f0.
Proof. vm_refl. Qed.
Lemma D_942f0 : decode_any W_942f0 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942f4 : bv 32 := 0x00170713.
Lemma F_942f4 : fetch_word Plain.M.loaded_segments (0x9434c : word) = Some W_942f4.
Proof. vm_refl. Qed.
Lemma D_942f4 : decode_any W_942f4 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942f8 : bv 32 := 0x014484b3.
Lemma F_942f8 : fetch_word Plain.M.loaded_segments (0x94350 : word) = Some W_942f8.
Proof. vm_refl. Qed.
Lemma D_942f8 : decode_any W_942f8 = Some (Op ALU_ADD 9 9 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942fc : bv 32 := 0x01280833.
Lemma F_942fc : fetch_word Plain.M.loaded_segments (0x94354 : word) = Some W_942fc.
Proof. vm_refl. Qed.
Lemma D_942fc : decode_any W_942fc = Some (Op ALU_ADD 16 16 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94300 : bv 32 := 0x01240433.
Lemma F_94300 : fetch_word Plain.M.loaded_segments (0x94358 : word) = Some W_94300.
Proof. vm_refl. Qed.
Lemma D_94300 : decode_any W_94300 = Some (Op ALU_ADD 8 8 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94304 : bv 32 := 0x33170c63.
Lemma F_94304 : fetch_word Plain.M.loaded_segments (0x9435c : word) = Some W_94304.
Proof. vm_refl. Qed.
Lemma D_94304 : decode_any W_94304 = Some (Branch BC_EQ 14 17 824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94308 : bv 32 := 0xfed056e3.
Lemma F_94308 : fetch_word Plain.M.loaded_segments (0x94360 : word) = Some W_94308.
Proof. vm_refl. Qed.
Lemma D_94308 : decode_any W_94308 = Some (Branch BC_GE 0 13 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9430c : bv 32 := 0x02ea0333.
Lemma F_9430c : fetch_word Plain.M.loaded_segments (0x94364 : word) = Some W_9430c.
Proof. vm_refl. Qed.
Lemma D_9430c : decode_any W_9430c = Some (Mul M_MUL 6 20 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94310 : bv 32 := 0x00628333.
Lemma F_94310 : fetch_word Plain.M.loaded_segments (0x94368 : word) = Some W_94310.
Proof. vm_refl. Qed.
Lemma D_94310 : decode_any W_94310 = Some (Op ALU_ADD 6 5 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94314 : bv 32 := 0x00040393.
Lemma F_94314 : fetch_word Plain.M.loaded_segments (0x9436c : word) = Some W_94314.
Proof. vm_refl. Qed.
Lemma D_94314 : decode_any W_94314 = Some (OpImm ALU_ADD 7 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94318 : bv 32 := 0x00080e13.
Lemma F_94318 : fetch_word Plain.M.loaded_segments (0x94370 : word) = Some W_94318.
Proof. vm_refl. Qed.
Lemma D_94318 : decode_any W_94318 = Some (OpImm ALU_ADD 28 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9431c : bv 32 := 0x00048e93.
Lemma F_9431c : fetch_word Plain.M.loaded_segments (0x94374 : word) = Some W_9431c.
Proof. vm_refl. Qed.
Lemma D_9431c : decode_any W_9431c = Some (OpImm ALU_ADD 29 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94320 : bv 32 := 0x0003af03.
Lemma F_94320 : fetch_word Plain.M.loaded_segments (0x94378 : word) = Some W_94320.
Proof. vm_refl. Qed.
Lemma D_94320 : decode_any W_94320 = Some (Load SZ4 true 30 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94324 : bv 32 := 0x000e2f83.
Lemma F_94324 : fetch_word Plain.M.loaded_segments (0x9437c : word) = Some W_94324.
Proof. vm_refl. Qed.
Lemma D_94324 : decode_any W_94324 = Some (Load SZ4 true 31 28 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94328 : bv 32 := 0x01efef33.
Lemma F_94328 : fetch_word Plain.M.loaded_segments (0x94380 : word) = Some W_94328.
Proof. vm_refl. Qed.
Lemma D_94328 : decode_any W_94328 = Some (Op ALU_OR 30 31 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9432c : bv 32 := 0x001f1f93.
Lemma F_9432c : fetch_word Plain.M.loaded_segments (0x94384 : word) = Some W_9432c.
Proof. vm_refl. Qed.
Lemma D_9432c : decode_any W_9432c = Some (ShiftImm ALU_SLL 31 30 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94330 : bv 32 := 0x01efef33.
Lemma F_94330 : fetch_word Plain.M.loaded_segments (0x94388 : word) = Some W_94330.
Proof. vm_refl. Qed.
Lemma D_94330 : decode_any W_94330 = Some (Op ALU_OR 30 31 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94334 : bv 32 := 0x00ff7f33.
Lemma F_94334 : fetch_word Plain.M.loaded_segments (0x9438c : word) = Some W_94334.
Proof. vm_refl. Qed.
Lemma D_94334 : decode_any W_94334 = Some (Op ALU_AND 30 30 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94338 : bv 32 := 0x007f1f93.
Lemma F_94338 : fetch_word Plain.M.loaded_segments (0x94390 : word) = Some W_94338.
Proof. vm_refl. Qed.
Lemma D_94338 : decode_any W_94338 = Some (ShiftImm ALU_SLL 31 30 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9433c : bv 32 := 0x01ef8f33.
Lemma F_9433c : fetch_word Plain.M.loaded_segments (0x94394 : word) = Some W_9433c.
Proof. vm_refl. Qed.
Lemma D_9433c : decode_any W_9433c = Some (Op ALU_ADD 30 31 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94340 : bv 32 := 0x018f5f9b.
Lemma F_94340 : fetch_word Plain.M.loaded_segments (0x94398 : word) = Some W_94340.
Proof. vm_refl. Qed.
Lemma D_94340 : decode_any W_94340 = Some (ShiftImm32 ALU_SRL 31 30 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94344 : bv 32 := 0x030f1f13.
Lemma F_94344 : fetch_word Plain.M.loaded_segments (0x9439c : word) = Some W_94344.
Proof. vm_refl. Qed.
Lemma D_94344 : decode_any W_94344 = Some (ShiftImm ALU_SLL 30 30 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94348 : bv 32 := 0x01f58fb3.
Lemma F_94348 : fetch_word Plain.M.loaded_segments (0x943a0 : word) = Some W_94348.
Proof. vm_refl. Qed.
Lemma D_94348 : decode_any W_94348 = Some (Op ALU_ADD 31 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9434c : bv 32 := 0x038f5f13.
Lemma F_9434c : fetch_word Plain.M.loaded_segments (0x943a4 : word) = Some W_9434c.
Proof. vm_refl. Qed.
Lemma D_9434c : decode_any W_9434c = Some (ShiftImm ALU_SRL 30 30 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94350 : bv 32 := 0x01e58f33.
Lemma F_94350 : fetch_word Plain.M.loaded_segments (0x943a8 : word) = Some W_94350.
Proof. vm_refl. Qed.
Lemma D_94350 : decode_any W_94350 = Some (Op ALU_ADD 30 11 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94354 : bv 32 := 0x000fcf83.
Lemma F_94354 : fetch_word Plain.M.loaded_segments (0x943ac : word) = Some W_94354.
Proof. vm_refl. Qed.
Lemma D_94354 : decode_any W_94354 = Some (Load SZ1 false 31 31 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94358 : bv 32 := 0x000f4f03.
Lemma F_94358 : fetch_word Plain.M.loaded_segments (0x943b0 : word) = Some W_94358.
Proof. vm_refl. Qed.
Lemma D_94358 : decode_any W_94358 = Some (Load SZ1 false 30 30 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9435c : bv 32 := 0x008f9f93.
Lemma F_9435c : fetch_word Plain.M.loaded_segments (0x943b4 : word) = Some W_9435c.
Proof. vm_refl. Qed.
Lemma D_9435c : decode_any W_9435c = Some (ShiftImm ALU_SLL 31 31 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94360 : bv 32 := 0x01efef33.
Lemma F_94360 : fetch_word Plain.M.loaded_segments (0x943b8 : word) = Some W_94360.
Proof. vm_refl. Qed.
Lemma D_94360 : decode_any W_94360 = Some (Op ALU_OR 30 31 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94364 : bv 32 := 0x002ecf93.
Lemma F_94364 : fetch_word Plain.M.loaded_segments (0x943bc : word) = Some W_94364.
Proof. vm_refl. Qed.
Lemma D_94364 : decode_any W_94364 = Some (OpImm ALU_XOR 31 29 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94368 : bv 32 := 0x002e8e93.
Lemma F_94368 : fetch_word Plain.M.loaded_segments (0x943c0 : word) = Some W_94368.
Proof. vm_refl. Qed.
Lemma D_94368 : decode_any W_94368 = Some (OpImm ALU_ADD 29 29 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9436c : bv 32 := 0x004e0e13.
Lemma F_9436c : fetch_word Plain.M.loaded_segments (0x943c4 : word) = Some W_9436c.
Proof. vm_refl. Qed.
Lemma D_9436c : decode_any W_9436c = Some (OpImm ALU_ADD 28 28 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94370 : bv 32 := 0x01ef9023.
Lemma F_94370 : fetch_word Plain.M.loaded_segments (0x943c8 : word) = Some W_94370.
Proof. vm_refl. Qed.
Lemma D_94370 : decode_any W_94370 = Some (Store SZ2 31 30 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94374 : bv 32 := 0x00438393.
Lemma F_94374 : fetch_word Plain.M.loaded_segments (0x943cc : word) = Some W_94374.
Proof. vm_refl. Qed.
Lemma D_94374 : decode_any W_94374 = Some (OpImm ALU_ADD 7 7 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94378 : bv 32 := 0xfa6e94e3.
Lemma F_94378 : fetch_word Plain.M.loaded_segments (0x943d0 : word) = Some W_94378.
Proof. vm_refl. Qed.
Lemma D_94378 : decode_any W_94378 = Some (Branch BC_NE 29 6 8104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9437c : bv 32 := 0xf79ff06f.
Lemma F_9437c : fetch_word Plain.M.loaded_segments (0x943d4 : word) = Some W_9437c.
Proof. vm_refl. Qed.
Lemma D_9437c : decode_any W_9437c = Some (Jal 0 2097016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94380 : bv 32 := 0x0007e517.
Lemma F_94380 : fetch_word Plain.M.loaded_segments (0x943d8 : word) = Some W_94380.
Proof. vm_refl. Qed.
Lemma D_94380 : decode_any W_94380 = Some (Auipc 10 126, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94384 : bv 32 := 0x1f053503.
Lemma F_94384 : fetch_word Plain.M.loaded_segments (0x943dc : word) = Some W_94384.
Proof. vm_refl. Qed.
Lemma D_94384 : decode_any W_94384 = Some (Load SZ8 true 10 10 496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94388 : bv 32 := 0x00052503.
Lemma F_94388 : fetch_word Plain.M.loaded_segments (0x943e0 : word) = Some W_94388.
Proof. vm_refl. Qed.
Lemma D_94388 : decode_any W_94388 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9438c : bv 32 := 0x00500593.
Lemma F_9438c : fetch_word Plain.M.loaded_segments (0x943e4 : word) = Some W_9438c.
Proof. vm_refl. Qed.
Lemma D_9438c : decode_any W_9438c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94390 : bv 32 := 0x2ea5c863.
Lemma F_94390 : fetch_word Plain.M.loaded_segments (0x943e8 : word) = Some W_94390.
Proof. vm_refl. Qed.
Lemma D_94390 : decode_any W_94390 = Some (Branch BC_LT 11 10 752, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94394 : bv 32 := 0xfff7e517.
Lemma F_94394 : fetch_word Plain.M.loaded_segments (0x943ec : word) = Some W_94394.
Proof. vm_refl. Qed.
Lemma D_94394 : decode_any W_94394 = Some (Auipc 10 1048446, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94398 : bv 32 := 0xfff82597.
Lemma F_94398 : fetch_word Plain.M.loaded_segments (0x943f0 : word) = Some W_94398.
Proof. vm_refl. Qed.
Lemma D_94398 : decode_any W_94398 = Some (Auipc 11 1048450, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9439c : bv 32 := 0x2ee50513.
Lemma F_9439c : fetch_word Plain.M.loaded_segments (0x943f4 : word) = Some W_9439c.
Proof. vm_refl. Qed.
Lemma D_9439c : decode_any W_9439c = Some (OpImm ALU_ADD 10 10 750, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_943a0 : bv 32 := 0xf7a58593.
Lemma F_943a0 : fetch_word Plain.M.loaded_segments (0x943f8 : word) = Some W_943a0.
Proof. vm_refl. Qed.
Lemma D_943a0 : decode_any W_943a0 = Some (OpImm ALU_ADD 11 11 3962, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_943a4 : bv 32 := 0x00000613.
Lemma F_943a4 : fetch_word Plain.M.loaded_segments (0x943fc : word) = Some W_943a4.
Proof. vm_refl. Qed.
Lemma D_943a4 : decode_any W_943a4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_943a8 : bv 32 := 0xd1dce0ef.
Lemma F_943a8 : fetch_word Plain.M.loaded_segments (0x94400 : word) = Some W_943a8.
Proof. vm_refl. Qed.
Lemma D_943a8 : decode_any W_943a8 = Some (Jal 1 1895708, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_943ac : bv 32 := 0x2d80006f.
Lemma F_943ac : fetch_word Plain.M.loaded_segments (0x94404 : word) = Some W_943ac.
Proof. vm_refl. Qed.
Lemma D_943ac : decode_any W_943ac = Some (Jal 0 728, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9463c : bv 32 := 0x04061463.
Lemma F_9463c : fetch_word Plain.M.loaded_segments (0x94694 : word) = Some W_9463c.
Proof. vm_refl. Qed.
Lemma D_9463c : decode_any W_9463c = Some (Branch BC_NE 12 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94684 : bv 32 := 0x05813083.
Lemma F_94684 : fetch_word Plain.M.loaded_segments (0x946dc : word) = Some W_94684.
Proof. vm_refl. Qed.
Lemma D_94684 : decode_any W_94684 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94688 : bv 32 := 0x05013403.
Lemma F_94688 : fetch_word Plain.M.loaded_segments (0x946e0 : word) = Some W_94688.
Proof. vm_refl. Qed.
Lemma D_94688 : decode_any W_94688 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9468c : bv 32 := 0x04813483.
Lemma F_9468c : fetch_word Plain.M.loaded_segments (0x946e4 : word) = Some W_9468c.
Proof. vm_refl. Qed.
Lemma D_9468c : decode_any W_9468c = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94690 : bv 32 := 0x04013903.
Lemma F_94690 : fetch_word Plain.M.loaded_segments (0x946e8 : word) = Some W_94690.
Proof. vm_refl. Qed.
Lemma D_94690 : decode_any W_94690 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94694 : bv 32 := 0x03813983.
Lemma F_94694 : fetch_word Plain.M.loaded_segments (0x946ec : word) = Some W_94694.
Proof. vm_refl. Qed.
Lemma D_94694 : decode_any W_94694 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94698 : bv 32 := 0x03013a03.
Lemma F_94698 : fetch_word Plain.M.loaded_segments (0x946f0 : word) = Some W_94698.
Proof. vm_refl. Qed.
Lemma D_94698 : decode_any W_94698 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9469c : bv 32 := 0x02813a83.
Lemma F_9469c : fetch_word Plain.M.loaded_segments (0x946f4 : word) = Some W_9469c.
Proof. vm_refl. Qed.
Lemma D_9469c : decode_any W_9469c = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_946a0 : bv 32 := 0x02013b03.
Lemma F_946a0 : fetch_word Plain.M.loaded_segments (0x946f8 : word) = Some W_946a0.
Proof. vm_refl. Qed.
Lemma D_946a0 : decode_any W_946a0 = Some (Load SZ8 true 22 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_946a4 : bv 32 := 0x01813b83.
Lemma F_946a4 : fetch_word Plain.M.loaded_segments (0x946fc : word) = Some W_946a4.
Proof. vm_refl. Qed.
Lemma D_946a4 : decode_any W_946a4 = Some (Load SZ8 true 23 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_946a8 : bv 32 := 0x06010113.
Lemma F_946a8 : fetch_word Plain.M.loaded_segments (0x94700 : word) = Some W_946a8.
Proof. vm_refl. Qed.
Lemma D_946a8 : decode_any W_946a8 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_946ac : bv 32 := 0x00008067.
Lemma F_946ac : fetch_word Plain.M.loaded_segments (0x94704 : word) = Some W_946ac.
Proof. vm_refl. Qed.
Lemma D_946ac : decode_any W_946ac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

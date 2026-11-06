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
Definition W_6ce20 : bv 32 := 0x02050263.
Lemma F_6ce20 : fetch_word Plain.M.loaded_segments (0x6ce78 : word) = Some W_6ce20.
Proof. vm_refl. Qed.
Lemma D_6ce20 : decode_any W_6ce20 = Some (Branch BC_EQ 10 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ce24 : bv 32 := 0x04058663.
Lemma F_6ce24 : fetch_word Plain.M.loaded_segments (0x6ce7c : word) = Some W_6ce24.
Proof. vm_refl. Qed.
Lemma D_6ce24 : decode_any W_6ce24 = Some (Branch BC_EQ 11 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ce28 : bv 32 := 0x0ca58063.
Lemma F_6ce28 : fetch_word Plain.M.loaded_segments (0x6ce80 : word) = Some W_6ce28.
Proof. vm_refl. Qed.
Lemma D_6ce28 : decode_any W_6ce28 = Some (Branch BC_EQ 11 10 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ce2c : bv 32 := 0x00c5a583.
Lemma F_6ce2c : fetch_word Plain.M.loaded_segments (0x6ce84 : word) = Some W_6ce2c.
Proof. vm_refl. Qed.
Lemma D_6ce2c : decode_any W_6ce2c = Some (Load SZ4 true 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ce30 : bv 32 := 0x06b05a63.
Lemma F_6ce30 : fetch_word Plain.M.loaded_segments (0x6ce88 : word) = Some W_6ce30.
Proof. vm_refl. Qed.
Lemma D_6ce30 : decode_any W_6ce30 = Some (Branch BC_GE 0 11 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ce34 : bv 32 := 0x00050613.
Lemma F_6ce34 : fetch_word Plain.M.loaded_segments (0x6ce8c : word) = Some W_6ce34.
Proof. vm_refl. Qed.
Lemma D_6ce34 : decode_any W_6ce34 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ce38 : bv 32 := 0x00000513.
Lemma F_6ce38 : fetch_word Plain.M.loaded_segments (0x6ce90 : word) = Some W_6ce38.
Proof. vm_refl. Qed.
Lemma D_6ce38 : decode_any W_6ce38 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ce3c : bv 32 := 0x00b62623.
Lemma F_6ce3c : fetch_word Plain.M.loaded_segments (0x6ce94 : word) = Some W_6ce3c.
Proof. vm_refl. Qed.
Lemma D_6ce3c : decode_any W_6ce3c = Some (Store SZ4 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ce40 : bv 32 := 0x00008067.
Lemma F_6ce40 : fetch_word Plain.M.loaded_segments (0x6ce98 : word) = Some W_6ce40.
Proof. vm_refl. Qed.
Lemma D_6ce40 : decode_any W_6ce40 = Some (Jalr 0 1 0, 4%Z).
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
Definition W_6f374 : bv 32 := 0x00050c63.
Lemma F_6f374 : fetch_word Plain.M.loaded_segments (0x6f3cc : word) = Some W_6f374.
Proof. vm_refl. Qed.
Lemma D_6f374 : decode_any W_6f374 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f378 : bv 32 := 0x04058063.
Lemma F_6f378 : fetch_word Plain.M.loaded_segments (0x6f3d0 : word) = Some W_6f378.
Proof. vm_refl. Qed.
Lemma D_6f378 : decode_any W_6f378 = Some (Branch BC_EQ 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f37c : bv 32 := 0x00058613.
Lemma F_6f37c : fetch_word Plain.M.loaded_segments (0x6f3d4 : word) = Some W_6f37c.
Proof. vm_refl. Qed.
Lemma D_6f37c : decode_any W_6f37c = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f380 : bv 32 := 0x00058693.
Lemma F_6f380 : fetch_word Plain.M.loaded_segments (0x6f3d8 : word) = Some W_6f380.
Proof. vm_refl. Qed.
Lemma D_6f380 : decode_any W_6f380 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f384 : bv 32 := 0x00058713.
Lemma F_6f384 : fetch_word Plain.M.loaded_segments (0x6f3dc : word) = Some W_6f384.
Proof. vm_refl. Qed.
Lemma D_6f384 : decode_any W_6f384 = Some (OpImm ALU_ADD 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f388 : bv 32 := 0x03c0006f.
Lemma F_6f388 : fetch_word Plain.M.loaded_segments (0x6f3e0 : word) = Some W_6f388.
Proof. vm_refl. Qed.
Lemma D_6f388 : decode_any W_6f388 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3c4 : bv 32 := 0xfa010113.
Lemma F_6f3c4 : fetch_word Plain.M.loaded_segments (0x6f41c : word) = Some W_6f3c4.
Proof. vm_refl. Qed.
Lemma D_6f3c4 : decode_any W_6f3c4 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3c8 : bv 32 := 0x04113c23.
Lemma F_6f3c8 : fetch_word Plain.M.loaded_segments (0x6f420 : word) = Some W_6f3c8.
Proof. vm_refl. Qed.
Lemma D_6f3c8 : decode_any W_6f3c8 = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3cc : bv 32 := 0x04813823.
Lemma F_6f3cc : fetch_word Plain.M.loaded_segments (0x6f424 : word) = Some W_6f3cc.
Proof. vm_refl. Qed.
Lemma D_6f3cc : decode_any W_6f3cc = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3d0 : bv 32 := 0x04913423.
Lemma F_6f3d0 : fetch_word Plain.M.loaded_segments (0x6f428 : word) = Some W_6f3d0.
Proof. vm_refl. Qed.
Lemma D_6f3d0 : decode_any W_6f3d0 = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3d4 : bv 32 := 0x05213023.
Lemma F_6f3d4 : fetch_word Plain.M.loaded_segments (0x6f42c : word) = Some W_6f3d4.
Proof. vm_refl. Qed.
Lemma D_6f3d4 : decode_any W_6f3d4 = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3d8 : bv 32 := 0x03313c23.
Lemma F_6f3d8 : fetch_word Plain.M.loaded_segments (0x6f430 : word) = Some W_6f3d8.
Proof. vm_refl. Qed.
Lemma D_6f3d8 : decode_any W_6f3d8 = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3dc : bv 32 := 0x03413823.
Lemma F_6f3dc : fetch_word Plain.M.loaded_segments (0x6f434 : word) = Some W_6f3dc.
Proof. vm_refl. Qed.
Lemma D_6f3dc : decode_any W_6f3dc = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3e0 : bv 32 := 0x03513423.
Lemma F_6f3e0 : fetch_word Plain.M.loaded_segments (0x6f438 : word) = Some W_6f3e0.
Proof. vm_refl. Qed.
Lemma D_6f3e0 : decode_any W_6f3e0 = Some (Store SZ8 2 21 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3e4 : bv 32 := 0x03713023.
Lemma F_6f3e4 : fetch_word Plain.M.loaded_segments (0x6f43c : word) = Some W_6f3e4.
Proof. vm_refl. Qed.
Lemma D_6f3e4 : decode_any W_6f3e4 = Some (Store SZ8 2 23 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3e8 : bv 32 := 0x10050063.
Lemma F_6f3e8 : fetch_word Plain.M.loaded_segments (0x6f440 : word) = Some W_6f3e8.
Proof. vm_refl. Qed.
Lemma D_6f3e8 : decode_any W_6f3e8 = Some (Branch BC_EQ 10 0 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3ec : bv 32 := 0x00068413.
Lemma F_6f3ec : fetch_word Plain.M.loaded_segments (0x6f444 : word) = Some W_6f3ec.
Proof. vm_refl. Qed.
Lemma D_6f3ec : decode_any W_6f3ec = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3f0 : bv 32 := 0x00060993.
Lemma F_6f3f0 : fetch_word Plain.M.loaded_segments (0x6f448 : word) = Some W_6f3f0.
Proof. vm_refl. Qed.
Lemma D_6f3f0 : decode_any W_6f3f0 = Some (OpImm ALU_ADD 19 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3f4 : bv 32 := 0x00058493.
Lemma F_6f3f4 : fetch_word Plain.M.loaded_segments (0x6f44c : word) = Some W_6f3f4.
Proof. vm_refl. Qed.
Lemma D_6f3f4 : decode_any W_6f3f4 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3f8 : bv 32 := 0x00b665b3.
Lemma F_6f3f8 : fetch_word Plain.M.loaded_segments (0x6f450 : word) = Some W_6f3f8.
Proof. vm_refl. Qed.
Lemma D_6f3f8 : decode_any W_6f3f8 = Some (Op ALU_OR 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3fc : bv 32 := 0x00e6e633.
Lemma F_6f3fc : fetch_word Plain.M.loaded_segments (0x6f454 : word) = Some W_6f3fc.
Proof. vm_refl. Qed.
Lemma D_6f3fc : decode_any W_6f3fc = Some (Op ALU_OR 12 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f400 : bv 32 := 0x00c5e5b3.
Lemma F_6f400 : fetch_word Plain.M.loaded_segments (0x6f458 : word) = Some W_6f400.
Proof. vm_refl. Qed.
Lemma D_6f400 : decode_any W_6f400 = Some (Op ALU_OR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f404 : bv 32 := 0x1005c663.
Lemma F_6f404 : fetch_word Plain.M.loaded_segments (0x6f45c : word) = Some W_6f404.
Proof. vm_refl. Qed.
Lemma D_6f404 : decode_any W_6f404 = Some (Branch BC_LT 11 0 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f408 : bv 32 := 0x00070a13.
Lemma F_6f408 : fetch_word Plain.M.loaded_segments (0x6f460 : word) = Some W_6f408.
Proof. vm_refl. Qed.
Lemma D_6f408 : decode_any W_6f408 = Some (OpImm ALU_ADD 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f40c : bv 32 := 0x01c10593.
Lemma F_6f40c : fetch_word Plain.M.loaded_segments (0x6f464 : word) = Some W_6f40c.
Proof. vm_refl. Qed.
Lemma D_6f40c : decode_any W_6f40c = Some (OpImm ALU_ADD 11 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f410 : bv 32 := 0x01810613.
Lemma F_6f410 : fetch_word Plain.M.loaded_segments (0x6f468 : word) = Some W_6f410.
Proof. vm_refl. Qed.
Lemma D_6f410 : decode_any W_6f410 = Some (OpImm ALU_ADD 12 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f414 : bv 32 := 0x01410693.
Lemma F_6f414 : fetch_word Plain.M.loaded_segments (0x6f46c : word) = Some W_6f414.
Proof. vm_refl. Qed.
Lemma D_6f414 : decode_any W_6f414 = Some (OpImm ALU_ADD 13 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f418 : bv 32 := 0x00050913.
Lemma F_6f418 : fetch_word Plain.M.loaded_segments (0x6f470 : word) = Some W_6f418.
Proof. vm_refl. Qed.
Lemma D_6f418 : decode_any W_6f418 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f41c : bv 32 := 0x985fd0ef.
Lemma F_6f41c : fetch_word Plain.M.loaded_segments (0x6f474 : word) = Some W_6f41c.
Proof. vm_refl. Qed.
Lemma D_6f41c : decode_any W_6f41c = Some (Jal 1 2087300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f420 : bv 32 := 0x01c12503.
Lemma F_6f420 : fetch_word Plain.M.loaded_segments (0x6f478 : word) = Some W_6f420.
Proof. vm_refl. Qed.
Lemma D_6f420 : decode_any W_6f420 = Some (Load SZ4 true 10 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f424 : bv 32 := 0x009989b3.
Lemma F_6f424 : fetch_word Plain.M.loaded_segments (0x6f47c : word) = Some W_6f424.
Proof. vm_refl. Qed.
Lemma D_6f424 : decode_any W_6f424 = Some (Op ALU_ADD 19 19 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f428 : bv 32 := 0x413509bb.
Lemma F_6f428 : fetch_word Plain.M.loaded_segments (0x6f480 : word) = Some W_6f428.
Proof. vm_refl. Qed.
Lemma D_6f428 : decode_any W_6f428 = Some (Op32 ALU_SUB 19 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f42c : bv 32 := 0x13305a63.
Lemma F_6f42c : fetch_word Plain.M.loaded_segments (0x6f484 : word) = Some W_6f42c.
Proof. vm_refl. Qed.
Lemma D_6f42c : decode_any W_6f42c = Some (Branch BC_GE 0 19 308, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f430 : bv 32 := 0x01812503.
Lemma F_6f430 : fetch_word Plain.M.loaded_segments (0x6f488 : word) = Some W_6f430.
Proof. vm_refl. Qed.
Lemma D_6f430 : decode_any W_6f430 = Some (Load SZ4 true 10 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f434 : bv 32 := 0x008a0a33.
Lemma F_6f434 : fetch_word Plain.M.loaded_segments (0x6f48c : word) = Some W_6f434.
Proof. vm_refl. Qed.
Lemma D_6f434 : decode_any W_6f434 = Some (Op ALU_ADD 20 20 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f438 : bv 32 := 0x41450a3b.
Lemma F_6f438 : fetch_word Plain.M.loaded_segments (0x6f490 : word) = Some W_6f438.
Proof. vm_refl. Qed.
Lemma D_6f438 : decode_any W_6f438 = Some (Op32 ALU_SUB 20 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f43c : bv 32 := 0x15405663.
Lemma F_6f43c : fetch_word Plain.M.loaded_segments (0x6f494 : word) = Some W_6f43c.
Proof. vm_refl. Qed.
Lemma D_6f43c : decode_any W_6f43c = Some (Branch BC_GE 0 20 332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f440 : bv 32 := 0x01412603.
Lemma F_6f440 : fetch_word Plain.M.loaded_segments (0x6f498 : word) = Some W_6f440.
Proof. vm_refl. Qed.
Lemma D_6f440 : decode_any W_6f440 = Some (Load SZ4 true 12 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f444 : bv 32 := 0x00098513.
Lemma F_6f444 : fetch_word Plain.M.loaded_segments (0x6f49c : word) = Some W_6f444.
Proof. vm_refl. Qed.
Lemma D_6f444 : decode_any W_6f444 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f448 : bv 32 := 0x000a0593.
Lemma F_6f448 : fetch_word Plain.M.loaded_segments (0x6f4a0 : word) = Some W_6f448.
Proof. vm_refl. Qed.
Lemma D_6f448 : decode_any W_6f448 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f44c : bv 32 := 0x994fd0ef.
Lemma F_6f44c : fetch_word Plain.M.loaded_segments (0x6f4a4 : word) = Some W_6f44c.
Proof. vm_refl. Qed.
Lemma D_6f44c : decode_any W_6f44c = Some (Jal 1 2085268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f450 : bv 32 := 0x16050063.
Lemma F_6f450 : fetch_word Plain.M.loaded_segments (0x6f4a8 : word) = Some W_6f450.
Proof. vm_refl. Qed.
Lemma D_6f450 : decode_any W_6f450 = Some (Branch BC_EQ 10 0 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f454 : bv 32 := 0x00050a93.
Lemma F_6f454 : fetch_word Plain.M.loaded_segments (0x6f4ac : word) = Some W_6f454.
Proof. vm_refl. Qed.
Lemma D_6f454 : decode_any W_6f454 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f458 : bv 32 := 0x00090593.
Lemma F_6f458 : fetch_word Plain.M.loaded_segments (0x6f4b0 : word) = Some W_6f458.
Proof. vm_refl. Qed.
Lemma D_6f458 : decode_any W_6f458 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f45c : bv 32 := 0xa95fd0ef.
Lemma F_6f45c : fetch_word Plain.M.loaded_segments (0x6f4b4 : word) = Some W_6f45c.
Proof. vm_refl. Qed.
Lemma D_6f45c : decode_any W_6f45c = Some (Jal 1 2087572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f460 : bv 32 := 0x000a8513.
Lemma F_6f460 : fetch_word Plain.M.loaded_segments (0x6f4b8 : word) = Some W_6f460.
Proof. vm_refl. Qed.
Lemma D_6f460 : decode_any W_6f460 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f464 : bv 32 := 0x00090593.
Lemma F_6f464 : fetch_word Plain.M.loaded_segments (0x6f4bc : word) = Some W_6f464.
Proof. vm_refl. Qed.
Lemma D_6f464 : decode_any W_6f464 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f468 : bv 32 := 0x9b9fd0ef.
Lemma F_6f468 : fetch_word Plain.M.loaded_segments (0x6f4c0 : word) = Some W_6f468.
Proof. vm_refl. Qed.
Lemma D_6f468 : decode_any W_6f468 = Some (Jal 1 2087352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f46c : bv 32 := 0x000a8513.
Lemma F_6f46c : fetch_word Plain.M.loaded_segments (0x6f4c4 : word) = Some W_6f46c.
Proof. vm_refl. Qed.
Lemma D_6f46c : decode_any W_6f46c = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f470 : bv 32 := 0x00090593.
Lemma F_6f470 : fetch_word Plain.M.loaded_segments (0x6f4c8 : word) = Some W_6f470.
Proof. vm_refl. Qed.
Lemma D_6f470 : decode_any W_6f470 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f474 : bv 32 := 0xb05fd0ef.
Lemma F_6f474 : fetch_word Plain.M.loaded_segments (0x6f4cc : word) = Some W_6f474.
Proof. vm_refl. Qed.
Lemma D_6f474 : decode_any W_6f474 = Some (Jal 1 2087684, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f478 : bv 32 := 0x00c00793.
Lemma F_6f478 : fetch_word Plain.M.loaded_segments (0x6f4d0 : word) = Some W_6f478.
Proof. vm_refl. Qed.
Lemma D_6f478 : decode_any W_6f478 = Some (OpImm ALU_ADD 15 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f47c : bv 32 := 0x00813023.
Lemma F_6f47c : fetch_word Plain.M.loaded_segments (0x6f4d4 : word) = Some W_6f47c.
Proof. vm_refl. Qed.
Lemma D_6f47c : decode_any W_6f47c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f480 : bv 32 := 0x000a8b93.
Lemma F_6f480 : fetch_word Plain.M.loaded_segments (0x6f4d8 : word) = Some W_6f480.
Proof. vm_refl. Qed.
Lemma D_6f480 : decode_any W_6f480 = Some (OpImm ALU_ADD 23 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f484 : bv 32 := 0x000a8513.
Lemma F_6f484 : fetch_word Plain.M.loaded_segments (0x6f4dc : word) = Some W_6f484.
Proof. vm_refl. Qed.
Lemma D_6f484 : decode_any W_6f484 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f488 : bv 32 := 0x00000593.
Lemma F_6f488 : fetch_word Plain.M.loaded_segments (0x6f4e0 : word) = Some W_6f488.
Proof. vm_refl. Qed.
Lemma D_6f488 : decode_any W_6f488 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f48c : bv 32 := 0x00000613.
Lemma F_6f48c : fetch_word Plain.M.loaded_segments (0x6f4e4 : word) = Some W_6f48c.
Proof. vm_refl. Qed.
Lemma D_6f48c : decode_any W_6f48c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f490 : bv 32 := 0x00098693.
Lemma F_6f490 : fetch_word Plain.M.loaded_segments (0x6f4e8 : word) = Some W_6f490.
Proof. vm_refl. Qed.
Lemma D_6f490 : decode_any W_6f490 = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f494 : bv 32 := 0x000a0713.
Lemma F_6f494 : fetch_word Plain.M.loaded_segments (0x6f4ec : word) = Some W_6f494.
Proof. vm_refl. Qed.
Lemma D_6f494 : decode_any W_6f494 = Some (OpImm ALU_ADD 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f498 : bv 32 := 0x00090813.
Lemma F_6f498 : fetch_word Plain.M.loaded_segments (0x6f4f0 : word) = Some W_6f498.
Proof. vm_refl. Qed.
Lemma D_6f498 : decode_any W_6f498 = Some (OpImm ALU_ADD 16 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f49c : bv 32 := 0x00048893.
Lemma F_6f49c : fetch_word Plain.M.loaded_segments (0x6f4f4 : word) = Some W_6f49c.
Proof. vm_refl. Qed.
Lemma D_6f49c : decode_any W_6f49c = Some (OpImm ALU_ADD 17 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4a0 : bv 32 := 0x2b40a0ef.
Lemma F_6f4a0 : fetch_word Plain.M.loaded_segments (0x6f4f8 : word) = Some W_6f4a0.
Proof. vm_refl. Qed.
Lemma D_6f4a0 : decode_any W_6f4a0 = Some (Jal 1 41652, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4a4 : bv 32 := 0x00090513.
Lemma F_6f4a4 : fetch_word Plain.M.loaded_segments (0x6f4fc : word) = Some W_6f4a4.
Proof. vm_refl. Qed.
Lemma D_6f4a4 : decode_any W_6f4a4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4a8 : bv 32 := 0xc80fe0ef.
Lemma F_6f4a8 : fetch_word Plain.M.loaded_segments (0x6f500 : word) = Some W_6f4a8.
Proof. vm_refl. Qed.
Lemma D_6f4a8 : decode_any W_6f4a8 = Some (Jal 1 2090112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4ac : bv 32 := 0x02000593.
Lemma F_6f4ac : fetch_word Plain.M.loaded_segments (0x6f504 : word) = Some W_6f4ac.
Proof. vm_refl. Qed.
Lemma D_6f4ac : decode_any W_6f4ac = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4b0 : bv 32 := 0x02b51863.
Lemma F_6f4b0 : fetch_word Plain.M.loaded_segments (0x6f508 : word) = Some W_6f4b0.
Proof. vm_refl. Qed.
Lemma D_6f4b0 : decode_any W_6f4b0 = Some (Branch BC_NE 10 11 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4e0 : bv 32 := 0x000b8513.
Lemma F_6f4e0 : fetch_word Plain.M.loaded_segments (0x6f538 : word) = Some W_6f4e0.
Proof. vm_refl. Qed.
Lemma D_6f4e0 : decode_any W_6f4e0 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4e4 : bv 32 := 0x1000006f.
Lemma F_6f4e4 : fetch_word Plain.M.loaded_segments (0x6f53c : word) = Some W_6f4e4.
Proof. vm_refl. Qed.
Lemma D_6f4e4 : decode_any W_6f4e4 = Some (Jal 0 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4e8 : bv 32 := 0x000a3517.
Lemma F_6f4e8 : fetch_word Plain.M.loaded_segments (0x6f540 : word) = Some W_6f4e8.
Proof. vm_refl. Qed.
Lemma D_6f4e8 : decode_any W_6f4e8 = Some (Auipc 10 163, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4ec : bv 32 := 0x08853503.
Lemma F_6f4ec : fetch_word Plain.M.loaded_segments (0x6f544 : word) = Some W_6f4ec.
Proof. vm_refl. Qed.
Lemma D_6f4ec : decode_any W_6f4ec = Some (Load SZ8 true 10 10 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4f0 : bv 32 := 0x00052503.
Lemma F_6f4f0 : fetch_word Plain.M.loaded_segments (0x6f548 : word) = Some W_6f4f0.
Proof. vm_refl. Qed.
Lemma D_6f4f0 : decode_any W_6f4f0 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4f4 : bv 32 := 0x00500593.
Lemma F_6f4f4 : fetch_word Plain.M.loaded_segments (0x6f54c : word) = Some W_6f4f4.
Proof. vm_refl. Qed.
Lemma D_6f4f4 : decode_any W_6f4f4 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4f8 : bv 32 := 0x0ea5c463.
Lemma F_6f4f8 : fetch_word Plain.M.loaded_segments (0x6f550 : word) = Some W_6f4f8.
Proof. vm_refl. Qed.
Lemma D_6f4f8 : decode_any W_6f4f8 = Some (Branch BC_LT 11 10 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4fc : bv 32 := 0xfffa1517.
Lemma F_6f4fc : fetch_word Plain.M.loaded_segments (0x6f554 : word) = Some W_6f4fc.
Proof. vm_refl. Qed.
Lemma D_6f4fc : decode_any W_6f4fc = Some (Auipc 10 1048481, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f500 : bv 32 := 0xfffa9597.
Lemma F_6f500 : fetch_word Plain.M.loaded_segments (0x6f558 : word) = Some W_6f500.
Proof. vm_refl. Qed.
Lemma D_6f500 : decode_any W_6f500 = Some (Auipc 11 1048489, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f504 : bv 32 := 0xe0150513.
Lemma F_6f504 : fetch_word Plain.M.loaded_segments (0x6f55c : word) = Some W_6f504.
Proof. vm_refl. Qed.
Lemma D_6f504 : decode_any W_6f504 = Some (OpImm ALU_ADD 10 10 3585, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f508 : bv 32 := 0xe7358593.
Lemma F_6f508 : fetch_word Plain.M.loaded_segments (0x6f560 : word) = Some W_6f508.
Proof. vm_refl. Qed.
Lemma D_6f508 : decode_any W_6f508 = Some (OpImm ALU_ADD 11 11 3699, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f50c : bv 32 := 0x0280006f.
Lemma F_6f50c : fetch_word Plain.M.loaded_segments (0x6f564 : word) = Some W_6f50c.
Proof. vm_refl. Qed.
Lemma D_6f50c : decode_any W_6f50c = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f534 : bv 32 := 0x00000613.
Lemma F_6f534 : fetch_word Plain.M.loaded_segments (0x6f58c : word) = Some W_6f534.
Proof. vm_refl. Qed.
Lemma D_6f534 : decode_any W_6f534 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f538 : bv 32 := 0x05813083.
Lemma F_6f538 : fetch_word Plain.M.loaded_segments (0x6f590 : word) = Some W_6f538.
Proof. vm_refl. Qed.
Lemma D_6f538 : decode_any W_6f538 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f53c : bv 32 := 0x05013403.
Lemma F_6f53c : fetch_word Plain.M.loaded_segments (0x6f594 : word) = Some W_6f53c.
Proof. vm_refl. Qed.
Lemma D_6f53c : decode_any W_6f53c = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f540 : bv 32 := 0x04813483.
Lemma F_6f540 : fetch_word Plain.M.loaded_segments (0x6f598 : word) = Some W_6f540.
Proof. vm_refl. Qed.
Lemma D_6f540 : decode_any W_6f540 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f544 : bv 32 := 0x04013903.
Lemma F_6f544 : fetch_word Plain.M.loaded_segments (0x6f59c : word) = Some W_6f544.
Proof. vm_refl. Qed.
Lemma D_6f544 : decode_any W_6f544 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f548 : bv 32 := 0x03813983.
Lemma F_6f548 : fetch_word Plain.M.loaded_segments (0x6f5a0 : word) = Some W_6f548.
Proof. vm_refl. Qed.
Lemma D_6f548 : decode_any W_6f548 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f54c : bv 32 := 0x03013a03.
Lemma F_6f54c : fetch_word Plain.M.loaded_segments (0x6f5a4 : word) = Some W_6f54c.
Proof. vm_refl. Qed.
Lemma D_6f54c : decode_any W_6f54c = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f550 : bv 32 := 0x02813a83.
Lemma F_6f550 : fetch_word Plain.M.loaded_segments (0x6f5a8 : word) = Some W_6f550.
Proof. vm_refl. Qed.
Lemma D_6f550 : decode_any W_6f550 = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f554 : bv 32 := 0x02013b83.
Lemma F_6f554 : fetch_word Plain.M.loaded_segments (0x6f5ac : word) = Some W_6f554.
Proof. vm_refl. Qed.
Lemma D_6f554 : decode_any W_6f554 = Some (Load SZ8 true 23 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f558 : bv 32 := 0x06010113.
Lemma F_6f558 : fetch_word Plain.M.loaded_segments (0x6f5b0 : word) = Some W_6f558.
Proof. vm_refl. Qed.
Lemma D_6f558 : decode_any W_6f558 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f55c : bv 32 := 0xb69f306f.
Lemma F_6f55c : fetch_word Plain.M.loaded_segments (0x6f5b4 : word) = Some W_6f55c.
Proof. vm_refl. Qed.
Lemma D_6f55c : decode_any W_6f55c = Some (Jal 0 2046824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f5b0 : bv 32 := 0x000a3517.
Lemma F_6f5b0 : fetch_word Plain.M.loaded_segments (0x6f608 : word) = Some W_6f5b0.
Proof. vm_refl. Qed.
Lemma D_6f5b0 : decode_any W_6f5b0 = Some (Auipc 10 163, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f5b4 : bv 32 := 0xfc053503.
Lemma F_6f5b4 : fetch_word Plain.M.loaded_segments (0x6f60c : word) = Some W_6f5b4.
Proof. vm_refl. Qed.
Lemma D_6f5b4 : decode_any W_6f5b4 = Some (Load SZ8 true 10 10 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f5b8 : bv 32 := 0x00052503.
Lemma F_6f5b8 : fetch_word Plain.M.loaded_segments (0x6f610 : word) = Some W_6f5b8.
Proof. vm_refl. Qed.
Lemma D_6f5b8 : decode_any W_6f5b8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f5bc : bv 32 := 0x00500593.
Lemma F_6f5bc : fetch_word Plain.M.loaded_segments (0x6f614 : word) = Some W_6f5bc.
Proof. vm_refl. Qed.
Lemma D_6f5bc : decode_any W_6f5bc = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f5c0 : bv 32 := 0x02a5c063.
Lemma F_6f5c0 : fetch_word Plain.M.loaded_segments (0x6f618 : word) = Some W_6f5c0.
Proof. vm_refl. Qed.
Lemma D_6f5c0 : decode_any W_6f5c0 = Some (Branch BC_LT 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f5c4 : bv 32 := 0xfffa3517.
Lemma F_6f5c4 : fetch_word Plain.M.loaded_segments (0x6f61c : word) = Some W_6f5c4.
Proof. vm_refl. Qed.
Lemma D_6f5c4 : decode_any W_6f5c4 = Some (Auipc 10 1048483, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f5c8 : bv 32 := 0xfffa9597.
Lemma F_6f5c8 : fetch_word Plain.M.loaded_segments (0x6f620 : word) = Some W_6f5c8.
Proof. vm_refl. Qed.
Lemma D_6f5c8 : decode_any W_6f5c8 = Some (Auipc 11 1048489, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f5cc : bv 32 := 0x0be50513.
Lemma F_6f5cc : fetch_word Plain.M.loaded_segments (0x6f624 : word) = Some W_6f5cc.
Proof. vm_refl. Qed.
Lemma D_6f5cc : decode_any W_6f5cc = Some (OpImm ALU_ADD 10 10 190, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f5d0 : bv 32 := 0xdab58593.
Lemma F_6f5d0 : fetch_word Plain.M.loaded_segments (0x6f628 : word) = Some W_6f5d0.
Proof. vm_refl. Qed.
Lemma D_6f5d0 : decode_any W_6f5d0 = Some (OpImm ALU_ADD 11 11 3499, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f5d4 : bv 32 := 0x00000613.
Lemma F_6f5d4 : fetch_word Plain.M.loaded_segments (0x6f62c : word) = Some W_6f5d4.
Proof. vm_refl. Qed.
Lemma D_6f5d4 : decode_any W_6f5d4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f5d8 : bv 32 := 0xaedf30ef.
Lemma F_6f5d8 : fetch_word Plain.M.loaded_segments (0x6f630 : word) = Some W_6f5d8.
Proof. vm_refl. Qed.
Lemma D_6f5d8 : decode_any W_6f5d8 = Some (Jal 1 2046700, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f5dc : bv 32 := 0x0080006f.
Lemma F_6f5dc : fetch_word Plain.M.loaded_segments (0x6f634 : word) = Some W_6f5dc.
Proof. vm_refl. Qed.
Lemma D_6f5dc : decode_any W_6f5dc = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f5e4 : bv 32 := 0x05813083.
Lemma F_6f5e4 : fetch_word Plain.M.loaded_segments (0x6f63c : word) = Some W_6f5e4.
Proof. vm_refl. Qed.
Lemma D_6f5e4 : decode_any W_6f5e4 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f5e8 : bv 32 := 0x05013403.
Lemma F_6f5e8 : fetch_word Plain.M.loaded_segments (0x6f640 : word) = Some W_6f5e8.
Proof. vm_refl. Qed.
Lemma D_6f5e8 : decode_any W_6f5e8 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f5ec : bv 32 := 0x04813483.
Lemma F_6f5ec : fetch_word Plain.M.loaded_segments (0x6f644 : word) = Some W_6f5ec.
Proof. vm_refl. Qed.
Lemma D_6f5ec : decode_any W_6f5ec = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f5f0 : bv 32 := 0x04013903.
Lemma F_6f5f0 : fetch_word Plain.M.loaded_segments (0x6f648 : word) = Some W_6f5f0.
Proof. vm_refl. Qed.
Lemma D_6f5f0 : decode_any W_6f5f0 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f5f4 : bv 32 := 0x03813983.
Lemma F_6f5f4 : fetch_word Plain.M.loaded_segments (0x6f64c : word) = Some W_6f5f4.
Proof. vm_refl. Qed.
Lemma D_6f5f4 : decode_any W_6f5f4 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f5f8 : bv 32 := 0x03013a03.
Lemma F_6f5f8 : fetch_word Plain.M.loaded_segments (0x6f650 : word) = Some W_6f5f8.
Proof. vm_refl. Qed.
Lemma D_6f5f8 : decode_any W_6f5f8 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f5fc : bv 32 := 0x02813a83.
Lemma F_6f5fc : fetch_word Plain.M.loaded_segments (0x6f654 : word) = Some W_6f5fc.
Proof. vm_refl. Qed.
Lemma D_6f5fc : decode_any W_6f5fc = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f600 : bv 32 := 0x02013b83.
Lemma F_6f600 : fetch_word Plain.M.loaded_segments (0x6f658 : word) = Some W_6f600.
Proof. vm_refl. Qed.
Lemma D_6f600 : decode_any W_6f600 = Some (Load SZ8 true 23 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f604 : bv 32 := 0x06010113.
Lemma F_6f604 : fetch_word Plain.M.loaded_segments (0x6f65c : word) = Some W_6f604.
Proof. vm_refl. Qed.
Lemma D_6f604 : decode_any W_6f604 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f608 : bv 32 := 0x00008067.
Lemma F_6f608 : fetch_word Plain.M.loaded_segments (0x6f660 : word) = Some W_6f608.
Proof. vm_refl. Qed.
Lemma D_6f608 : decode_any W_6f608 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

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

Definition W_382d0 : bv 32 := 0xfe010113.
Lemma F_382d0 : fetch_word Ubsan.M.loaded_segments (0x382d0 : word) = Some W_382d0.
Proof. vm_refl. Qed.
Lemma D_382d0 : decode_any W_382d0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_382d4 : bv 32 := 0x00113c23.
Lemma F_382d4 : fetch_word Ubsan.M.loaded_segments (0x382d4 : word) = Some W_382d4.
Proof. vm_refl. Qed.
Lemma D_382d4 : decode_any W_382d4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_382d8 : bv 32 := 0x00813823.
Lemma F_382d8 : fetch_word Ubsan.M.loaded_segments (0x382d8 : word) = Some W_382d8.
Proof. vm_refl. Qed.
Lemma D_382d8 : decode_any W_382d8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_382dc : bv 32 := 0x00913423.
Lemma F_382dc : fetch_word Ubsan.M.loaded_segments (0x382dc : word) = Some W_382dc.
Proof. vm_refl. Qed.
Lemma D_382dc : decode_any W_382dc = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_382e0 : bv 32 := 0x06b05263.
Lemma F_382e0 : fetch_word Ubsan.M.loaded_segments (0x382e0 : word) = Some W_382e0.
Proof. vm_refl. Qed.
Lemma D_382e0 : decode_any W_382e0 = Some (Branch BC_GE 0 11 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_382e4 : bv 32 := 0x08a05063.
Lemma F_382e4 : fetch_word Ubsan.M.loaded_segments (0x382e4 : word) = Some W_382e4.
Proof. vm_refl. Qed.
Lemma D_382e4 : decode_any W_382e4 = Some (Branch BC_GE 0 10 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_382e8 : bv 32 := 0x02a58633.
Lemma F_382e8 : fetch_word Ubsan.M.loaded_segments (0x382e8 : word) = Some W_382e8.
Proof. vm_refl. Qed.
Lemma D_382e8 : decode_any W_382e8 = Some (Mul M_MUL 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_382ec : bv 32 := 0x01d65613.
Lemma F_382ec : fetch_word Ubsan.M.loaded_segments (0x382ec : word) = Some W_382ec.
Proof. vm_refl. Qed.
Lemma D_382ec : decode_any W_382ec = Some (ShiftImm ALU_SRL 12 12 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_382f0 : bv 32 := 0x08060a63.
Lemma F_382f0 : fetch_word Ubsan.M.loaded_segments (0x382f0 : word) = Some W_382f0.
Proof. vm_refl. Qed.
Lemma D_382f0 : decode_any W_382f0 = Some (Branch BC_EQ 12 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_382f4 : bv 32 := 0x0000d617.
Lemma F_382f4 : fetch_word Ubsan.M.loaded_segments (0x382f4 : word) = Some W_382f4.
Proof. vm_refl. Qed.
Lemma D_382f4 : decode_any W_382f4 = Some (Auipc 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_382f8 : bv 32 := 0xba463403.
Lemma F_382f8 : fetch_word Ubsan.M.loaded_segments (0x382f8 : word) = Some W_382f8.
Proof. vm_refl. Qed.
Lemma D_382f8 : decode_any W_382f8 = Some (Load SZ8 true 8 12 2980, 4%Z).
Proof. vm_refl. Qed.

Definition W_382fc : bv 32 := 0x00042603.
Lemma F_382fc : fetch_word Ubsan.M.loaded_segments (0x382fc : word) = Some W_382fc.
Proof. vm_refl. Qed.
Lemma D_382fc : decode_any W_382fc = Some (Load SZ4 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38300 : bv 32 := 0x00500693.
Lemma F_38300 : fetch_word Ubsan.M.loaded_segments (0x38300 : word) = Some W_38300.
Proof. vm_refl. Qed.
Lemma D_38300 : decode_any W_38300 = Some (OpImm ALU_ADD 13 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_38304 : bv 32 := 0x10c6c463.
Lemma F_38304 : fetch_word Ubsan.M.loaded_segments (0x38304 : word) = Some W_38304.
Proof. vm_refl. Qed.
Lemma D_38304 : decode_any W_38304 = Some (Branch BC_LT 13 12 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_38308 : bv 32 := 0xfffda617.
Lemma F_38308 : fetch_word Ubsan.M.loaded_segments (0x38308 : word) = Some W_38308.
Proof. vm_refl. Qed.
Lemma D_38308 : decode_any W_38308 = Some (Auipc 12 1048538, 4%Z).
Proof. vm_refl. Qed.

Definition W_3830c : bv 32 := 0xfffda697.
Lemma F_3830c : fetch_word Ubsan.M.loaded_segments (0x3830c : word) = Some W_3830c.
Proof. vm_refl. Qed.
Lemma D_3830c : decode_any W_3830c = Some (Auipc 13 1048538, 4%Z).
Proof. vm_refl. Qed.

Definition W_38310 : bv 32 := 0x0d660613.
Lemma F_38310 : fetch_word Ubsan.M.loaded_segments (0x38310 : word) = Some W_38310.
Proof. vm_refl. Qed.
Lemma D_38310 : decode_any W_38310 = Some (OpImm ALU_ADD 12 12 214, 4%Z).
Proof. vm_refl. Qed.

Definition W_38314 : bv 32 := 0x20168713.
Lemma F_38314 : fetch_word Ubsan.M.loaded_segments (0x38314 : word) = Some W_38314.
Proof. vm_refl. Qed.
Lemma D_38314 : decode_any W_38314 = Some (OpImm ALU_ADD 14 13 513, 4%Z).
Proof. vm_refl. Qed.

Definition W_38318 : bv 32 := 0x00050693.
Lemma F_38318 : fetch_word Ubsan.M.loaded_segments (0x38318 : word) = Some W_38318.
Proof. vm_refl. Qed.
Lemma D_38318 : decode_any W_38318 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3831c : bv 32 := 0x00060513.
Lemma F_3831c : fetch_word Ubsan.M.loaded_segments (0x3831c : word) = Some W_3831c.
Proof. vm_refl. Qed.
Lemma D_3831c : decode_any W_3831c = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38320 : bv 32 := 0x00058613.
Lemma F_38320 : fetch_word Ubsan.M.loaded_segments (0x38320 : word) = Some W_38320.
Proof. vm_refl. Qed.
Lemma D_38320 : decode_any W_38320 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38324 : bv 32 := 0x00070593.
Lemma F_38324 : fetch_word Ubsan.M.loaded_segments (0x38324 : word) = Some W_38324.
Proof. vm_refl. Qed.
Lemma D_38324 : decode_any W_38324 = Some (OpImm ALU_ADD 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38328 : bv 32 := 0xb01df0ef.
Lemma F_38328 : fetch_word Ubsan.M.loaded_segments (0x38328 : word) = Some W_38328.
Proof. vm_refl. Qed.
Lemma D_38328 : decode_any W_38328 = Some (Jal 1 1964800, 4%Z).
Proof. vm_refl. Qed.

Definition W_3832c : bv 32 := 0x00042503.
Lemma F_3832c : fetch_word Ubsan.M.loaded_segments (0x3832c : word) = Some W_3832c.
Proof. vm_refl. Qed.
Lemma D_3832c : decode_any W_3832c = Some (Load SZ4 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38330 : bv 32 := 0x00600593.
Lemma F_38330 : fetch_word Ubsan.M.loaded_segments (0x38330 : word) = Some W_38330.
Proof. vm_refl. Qed.
Lemma D_38330 : decode_any W_38330 = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_38334 : bv 32 := 0x0cb55c63.
Lemma F_38334 : fetch_word Ubsan.M.loaded_segments (0x38334 : word) = Some W_38334.
Proof. vm_refl. Qed.
Lemma D_38334 : decode_any W_38334 = Some (Branch BC_GE 10 11 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_38338 : bv 32 := 0xfffd8517.
Lemma F_38338 : fetch_word Ubsan.M.loaded_segments (0x38338 : word) = Some W_38338.
Proof. vm_refl. Qed.
Lemma D_38338 : decode_any W_38338 = Some (Auipc 10 1048536, 4%Z).
Proof. vm_refl. Qed.

Definition W_3833c : bv 32 := 0x1bd50513.
Lemma F_3833c : fetch_word Ubsan.M.loaded_segments (0x3833c : word) = Some W_3833c.
Proof. vm_refl. Qed.
Lemma D_3833c : decode_any W_3833c = Some (OpImm ALU_ADD 10 10 445, 4%Z).
Proof. vm_refl. Qed.

Definition W_38340 : bv 32 := 0x0ac0006f.
Lemma F_38340 : fetch_word Ubsan.M.loaded_segments (0x38340 : word) = Some W_38340.
Proof. vm_refl. Qed.
Lemma D_38340 : decode_any W_38340 = Some (Jal 0 172, 4%Z).
Proof. vm_refl. Qed.

Definition W_38344 : bv 32 := 0x0000d517.
Lemma F_38344 : fetch_word Ubsan.M.loaded_segments (0x38344 : word) = Some W_38344.
Proof. vm_refl. Qed.
Lemma D_38344 : decode_any W_38344 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_38348 : bv 32 := 0xb5453503.
Lemma F_38348 : fetch_word Ubsan.M.loaded_segments (0x38348 : word) = Some W_38348.
Proof. vm_refl. Qed.
Lemma D_38348 : decode_any W_38348 = Some (Load SZ8 true 10 10 2900, 4%Z).
Proof. vm_refl. Qed.

Definition W_3834c : bv 32 := 0x00052503.
Lemma F_3834c : fetch_word Ubsan.M.loaded_segments (0x3834c : word) = Some W_3834c.
Proof. vm_refl. Qed.
Lemma D_3834c : decode_any W_3834c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38350 : bv 32 := 0x00600593.
Lemma F_38350 : fetch_word Ubsan.M.loaded_segments (0x38350 : word) = Some W_38350.
Proof. vm_refl. Qed.
Lemma D_38350 : decode_any W_38350 = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_38354 : bv 32 := 0x0ab55c63.
Lemma F_38354 : fetch_word Ubsan.M.loaded_segments (0x38354 : word) = Some W_38354.
Proof. vm_refl. Qed.
Lemma D_38354 : decode_any W_38354 = Some (Branch BC_GE 10 11 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_38358 : bv 32 := 0xfffd8517.
Lemma F_38358 : fetch_word Ubsan.M.loaded_segments (0x38358 : word) = Some W_38358.
Proof. vm_refl. Qed.
Lemma D_38358 : decode_any W_38358 = Some (Auipc 10 1048536, 4%Z).
Proof. vm_refl. Qed.

Definition W_3835c : bv 32 := 0xf6d50513.
Lemma F_3835c : fetch_word Ubsan.M.loaded_segments (0x3835c : word) = Some W_3835c.
Proof. vm_refl. Qed.
Lemma D_3835c : decode_any W_3835c = Some (OpImm ALU_ADD 10 10 3949, 4%Z).
Proof. vm_refl. Qed.

Definition W_38360 : bv 32 := 0x08c0006f.
Lemma F_38360 : fetch_word Ubsan.M.loaded_segments (0x38360 : word) = Some W_38360.
Proof. vm_refl. Qed.
Lemma D_38360 : decode_any W_38360 = Some (Jal 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_38364 : bv 32 := 0x0000d517.
Lemma F_38364 : fetch_word Ubsan.M.loaded_segments (0x38364 : word) = Some W_38364.
Proof. vm_refl. Qed.
Lemma D_38364 : decode_any W_38364 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_38368 : bv 32 := 0xb3453503.
Lemma F_38368 : fetch_word Ubsan.M.loaded_segments (0x38368 : word) = Some W_38368.
Proof. vm_refl. Qed.
Lemma D_38368 : decode_any W_38368 = Some (Load SZ8 true 10 10 2868, 4%Z).
Proof. vm_refl. Qed.

Definition W_3836c : bv 32 := 0x00052503.
Lemma F_3836c : fetch_word Ubsan.M.loaded_segments (0x3836c : word) = Some W_3836c.
Proof. vm_refl. Qed.
Lemma D_3836c : decode_any W_3836c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38370 : bv 32 := 0x00600593.
Lemma F_38370 : fetch_word Ubsan.M.loaded_segments (0x38370 : word) = Some W_38370.
Proof. vm_refl. Qed.
Lemma D_38370 : decode_any W_38370 = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_38374 : bv 32 := 0x08b55c63.
Lemma F_38374 : fetch_word Ubsan.M.loaded_segments (0x38374 : word) = Some W_38374.
Proof. vm_refl. Qed.
Lemma D_38374 : decode_any W_38374 = Some (Branch BC_GE 10 11 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_38378 : bv 32 := 0xfffd9517.
Lemma F_38378 : fetch_word Ubsan.M.loaded_segments (0x38378 : word) = Some W_38378.
Proof. vm_refl. Qed.
Lemma D_38378 : decode_any W_38378 = Some (Auipc 10 1048537, 4%Z).
Proof. vm_refl. Qed.

Definition W_3837c : bv 32 := 0x16e50513.
Lemma F_3837c : fetch_word Ubsan.M.loaded_segments (0x3837c : word) = Some W_3837c.
Proof. vm_refl. Qed.
Lemma D_3837c : decode_any W_3837c = Some (OpImm ALU_ADD 10 10 366, 4%Z).
Proof. vm_refl. Qed.

Definition W_38380 : bv 32 := 0x06c0006f.
Lemma F_38380 : fetch_word Ubsan.M.loaded_segments (0x38380 : word) = Some W_38380.
Proof. vm_refl. Qed.
Lemma D_38380 : decode_any W_38380 = Some (Jal 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_38384 : bv 32 := 0x00050493.
Lemma F_38384 : fetch_word Ubsan.M.loaded_segments (0x38384 : word) = Some W_38384.
Proof. vm_refl. Qed.
Lemma D_38384 : decode_any W_38384 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38388 : bv 32 := 0x00058413.
Lemma F_38388 : fetch_word Ubsan.M.loaded_segments (0x38388 : word) = Some W_38388.
Proof. vm_refl. Qed.
Lemma D_38388 : decode_any W_38388 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3838c : bv 32 := 0x00100513.
Lemma F_3838c : fetch_word Ubsan.M.loaded_segments (0x3838c : word) = Some W_3838c.
Proof. vm_refl. Qed.
Lemma D_3838c : decode_any W_3838c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_38390 : bv 32 := 0x01800593.
Lemma F_38390 : fetch_word Ubsan.M.loaded_segments (0x38390 : word) = Some W_38390.
Proof. vm_refl. Qed.
Lemma D_38390 : decode_any W_38390 = Some (OpImm ALU_ADD 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_38394 : bv 32 := 0x565030ef.
Lemma F_38394 : fetch_word Ubsan.M.loaded_segments (0x38394 : word) = Some W_38394.
Proof. vm_refl. Qed.
Lemma D_38394 : decode_any W_38394 = Some (Jal 1 15716, 4%Z).
Proof. vm_refl. Qed.

Definition W_38398 : bv 32 := 0x08050663.
Lemma F_38398 : fetch_word Ubsan.M.loaded_segments (0x38398 : word) = Some W_38398.
Proof. vm_refl. Qed.
Lemma D_38398 : decode_any W_38398 = Some (Branch BC_EQ 10 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_3839c : bv 32 := 0x00757593.
Lemma F_3839c : fetch_word Ubsan.M.loaded_segments (0x3839c : word) = Some W_3839c.
Proof. vm_refl. Qed.
Lemma D_3839c : decode_any W_3839c = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_383a0 : bv 32 := 0x08059263.
Lemma F_383a0 : fetch_word Ubsan.M.loaded_segments (0x383a0 : word) = Some W_383a0.
Proof. vm_refl. Qed.
Lemma D_383a0 : decode_any W_383a0 = Some (Branch BC_NE 11 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_383a4 : bv 32 := 0x00952023.
Lemma F_383a4 : fetch_word Ubsan.M.loaded_segments (0x383a4 : word) = Some W_383a4.
Proof. vm_refl. Qed.
Lemma D_383a4 : decode_any W_383a4 = Some (Store SZ4 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_383a8 : bv 32 := 0x00040593.
Lemma F_383a8 : fetch_word Ubsan.M.loaded_segments (0x383a8 : word) = Some W_383a8.
Proof. vm_refl. Qed.
Lemma D_383a8 : decode_any W_383a8 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_383ac : bv 32 := 0x00852223.
Lemma F_383ac : fetch_word Ubsan.M.loaded_segments (0x383ac : word) = Some W_383ac.
Proof. vm_refl. Qed.
Lemma D_383ac : decode_any W_383ac = Some (Store SZ4 10 8 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_383b0 : bv 32 := 0x00050413.
Lemma F_383b0 : fetch_word Ubsan.M.loaded_segments (0x383b0 : word) = Some W_383b0.
Proof. vm_refl. Qed.
Lemma D_383b0 : decode_any W_383b0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_383b4 : bv 32 := 0x00048513.
Lemma F_383b4 : fetch_word Ubsan.M.loaded_segments (0x383b4 : word) = Some W_383b4.
Proof. vm_refl. Qed.
Lemma D_383b4 : decode_any W_383b4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_383b8 : bv 32 := 0x070000ef.
Lemma F_383b8 : fetch_word Ubsan.M.loaded_segments (0x383b8 : word) = Some W_383b8.
Proof. vm_refl. Qed.
Lemma D_383b8 : decode_any W_383b8 = Some (Jal 1 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_383bc : bv 32 := 0x00050593.
Lemma F_383bc : fetch_word Ubsan.M.loaded_segments (0x383bc : word) = Some W_383bc.
Proof. vm_refl. Qed.
Lemma D_383bc : decode_any W_383bc = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_383c0 : bv 32 := 0x00040513.
Lemma F_383c0 : fetch_word Ubsan.M.loaded_segments (0x383c0 : word) = Some W_383c0.
Proof. vm_refl. Qed.
Lemma D_383c0 : decode_any W_383c0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_383c4 : bv 32 := 0x00b43823.
Lemma F_383c4 : fetch_word Ubsan.M.loaded_segments (0x383c4 : word) = Some W_383c4.
Proof. vm_refl. Qed.
Lemma D_383c4 : decode_any W_383c4 = Some (Store SZ8 8 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_383c8 : bv 32 := 0x04059463.
Lemma F_383c8 : fetch_word Ubsan.M.loaded_segments (0x383c8 : word) = Some W_383c8.
Proof. vm_refl. Qed.
Lemma D_383c8 : decode_any W_383c8 = Some (Branch BC_NE 11 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_383cc : bv 32 := 0x665030ef.
Lemma F_383cc : fetch_word Ubsan.M.loaded_segments (0x383cc : word) = Some W_383cc.
Proof. vm_refl. Qed.
Lemma D_383cc : decode_any W_383cc = Some (Jal 1 15972, 4%Z).
Proof. vm_refl. Qed.

Definition W_383d0 : bv 32 := 0x0000d517.
Lemma F_383d0 : fetch_word Ubsan.M.loaded_segments (0x383d0 : word) = Some W_383d0.
Proof. vm_refl. Qed.
Lemma D_383d0 : decode_any W_383d0 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_383d4 : bv 32 := 0xac853503.
Lemma F_383d4 : fetch_word Ubsan.M.loaded_segments (0x383d4 : word) = Some W_383d4.
Proof. vm_refl. Qed.
Lemma D_383d4 : decode_any W_383d4 = Some (Load SZ8 true 10 10 2760, 4%Z).
Proof. vm_refl. Qed.

Definition W_383d8 : bv 32 := 0x00052503.
Lemma F_383d8 : fetch_word Ubsan.M.loaded_segments (0x383d8 : word) = Some W_383d8.
Proof. vm_refl. Qed.
Lemma D_383d8 : decode_any W_383d8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_383dc : bv 32 := 0x00500593.
Lemma F_383dc : fetch_word Ubsan.M.loaded_segments (0x383dc : word) = Some W_383dc.
Proof. vm_refl. Qed.
Lemma D_383dc : decode_any W_383dc = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_383e0 : bv 32 := 0x02a5c663.
Lemma F_383e0 : fetch_word Ubsan.M.loaded_segments (0x383e0 : word) = Some W_383e0.
Proof. vm_refl. Qed.
Lemma D_383e0 : decode_any W_383e0 = Some (Branch BC_LT 11 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_383e4 : bv 32 := 0xfffd8517.
Lemma F_383e4 : fetch_word Ubsan.M.loaded_segments (0x383e4 : word) = Some W_383e4.
Proof. vm_refl. Qed.
Lemma D_383e4 : decode_any W_383e4 = Some (Auipc 10 1048536, 4%Z).
Proof. vm_refl. Qed.

Definition W_383e8 : bv 32 := 0x11e50513.
Lemma F_383e8 : fetch_word Ubsan.M.loaded_segments (0x383e8 : word) = Some W_383e8.
Proof. vm_refl. Qed.
Lemma D_383e8 : decode_any W_383e8 = Some (OpImm ALU_ADD 10 10 286, 4%Z).
Proof. vm_refl. Qed.

Definition W_383ec : bv 32 := 0xfffda597.
Lemma F_383ec : fetch_word Ubsan.M.loaded_segments (0x383ec : word) = Some W_383ec.
Proof. vm_refl. Qed.
Lemma D_383ec : decode_any W_383ec = Some (Auipc 11 1048538, 4%Z).
Proof. vm_refl. Qed.

Definition W_383f0 : bv 32 := 0x12158593.
Lemma F_383f0 : fetch_word Ubsan.M.loaded_segments (0x383f0 : word) = Some W_383f0.
Proof. vm_refl. Qed.
Lemma D_383f0 : decode_any W_383f0 = Some (OpImm ALU_ADD 11 11 289, 4%Z).
Proof. vm_refl. Qed.

Definition W_383f4 : bv 32 := 0x00000613.
Lemma F_383f4 : fetch_word Ubsan.M.loaded_segments (0x383f4 : word) = Some W_383f4.
Proof. vm_refl. Qed.
Lemma D_383f4 : decode_any W_383f4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_383f8 : bv 32 := 0x01813083.
Lemma F_383f8 : fetch_word Ubsan.M.loaded_segments (0x383f8 : word) = Some W_383f8.
Proof. vm_refl. Qed.
Lemma D_383f8 : decode_any W_383f8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_383fc : bv 32 := 0x01013403.
Lemma F_383fc : fetch_word Ubsan.M.loaded_segments (0x383fc : word) = Some W_383fc.
Proof. vm_refl. Qed.
Lemma D_383fc : decode_any W_383fc = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_38400 : bv 32 := 0x00813483.
Lemma F_38400 : fetch_word Ubsan.M.loaded_segments (0x38400 : word) = Some W_38400.
Proof. vm_refl. Qed.
Lemma D_38400 : decode_any W_38400 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_38404 : bv 32 := 0x02010113.
Lemma F_38404 : fetch_word Ubsan.M.loaded_segments (0x38404 : word) = Some W_38404.
Proof. vm_refl. Qed.
Lemma D_38404 : decode_any W_38404 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_38408 : bv 32 := 0xabddf06f.
Lemma F_38408 : fetch_word Ubsan.M.loaded_segments (0x38408 : word) = Some W_38408.
Proof. vm_refl. Qed.
Lemma D_38408 : decode_any W_38408 = Some (Jal 0 1964732, 4%Z).
Proof. vm_refl. Qed.

Definition W_3840c : bv 32 := 0x00000513.
Lemma F_3840c : fetch_word Ubsan.M.loaded_segments (0x3840c : word) = Some W_3840c.
Proof. vm_refl. Qed.
Lemma D_3840c : decode_any W_3840c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38410 : bv 32 := 0x01813083.
Lemma F_38410 : fetch_word Ubsan.M.loaded_segments (0x38410 : word) = Some W_38410.
Proof. vm_refl. Qed.
Lemma D_38410 : decode_any W_38410 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_38414 : bv 32 := 0x01013403.
Lemma F_38414 : fetch_word Ubsan.M.loaded_segments (0x38414 : word) = Some W_38414.
Proof. vm_refl. Qed.
Lemma D_38414 : decode_any W_38414 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_38418 : bv 32 := 0x00813483.
Lemma F_38418 : fetch_word Ubsan.M.loaded_segments (0x38418 : word) = Some W_38418.
Proof. vm_refl. Qed.
Lemma D_38418 : decode_any W_38418 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3841c : bv 32 := 0x02010113.
Lemma F_3841c : fetch_word Ubsan.M.loaded_segments (0x3841c : word) = Some W_3841c.
Proof. vm_refl. Qed.
Lemma D_3841c : decode_any W_3841c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_38420 : bv 32 := 0x00008067.
Lemma F_38420 : fetch_word Ubsan.M.loaded_segments (0x38420 : word) = Some W_38420.
Proof. vm_refl. Qed.
Lemma D_38420 : decode_any W_38420 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38424 : bv 32 := 0xc0001073.
Lemma F_38424 : fetch_word Ubsan.M.loaded_segments (0x38424 : word) = Some W_38424.
Proof. vm_refl. Qed.
Lemma D_38424 : decode_any W_38424 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.

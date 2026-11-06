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
Definition W_8f4d8 : bv 32 := 0xf9010113.
Lemma F_8f4d8 : fetch_word Plain.M.loaded_segments (0x8f530 : word) = Some W_8f4d8.
Proof. vm_refl. Qed.
Lemma D_8f4d8 : decode_any W_8f4d8 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f4dc : bv 32 := 0x06113423.
Lemma F_8f4dc : fetch_word Plain.M.loaded_segments (0x8f534 : word) = Some W_8f4dc.
Proof. vm_refl. Qed.
Lemma D_8f4dc : decode_any W_8f4dc = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f4e0 : bv 32 := 0x06813023.
Lemma F_8f4e0 : fetch_word Plain.M.loaded_segments (0x8f538 : word) = Some W_8f4e0.
Proof. vm_refl. Qed.
Lemma D_8f4e0 : decode_any W_8f4e0 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f4e4 : bv 32 := 0x04913c23.
Lemma F_8f4e4 : fetch_word Plain.M.loaded_segments (0x8f53c : word) = Some W_8f4e4.
Proof. vm_refl. Qed.
Lemma D_8f4e4 : decode_any W_8f4e4 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f4e8 : bv 32 := 0x05213823.
Lemma F_8f4e8 : fetch_word Plain.M.loaded_segments (0x8f540 : word) = Some W_8f4e8.
Proof. vm_refl. Qed.
Lemma D_8f4e8 : decode_any W_8f4e8 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f4ec : bv 32 := 0x05313423.
Lemma F_8f4ec : fetch_word Plain.M.loaded_segments (0x8f544 : word) = Some W_8f4ec.
Proof. vm_refl. Qed.
Lemma D_8f4ec : decode_any W_8f4ec = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f4f0 : bv 32 := 0x05413023.
Lemma F_8f4f0 : fetch_word Plain.M.loaded_segments (0x8f548 : word) = Some W_8f4f0.
Proof. vm_refl. Qed.
Lemma D_8f4f0 : decode_any W_8f4f0 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f4f4 : bv 32 := 0x03513c23.
Lemma F_8f4f4 : fetch_word Plain.M.loaded_segments (0x8f54c : word) = Some W_8f4f4.
Proof. vm_refl. Qed.
Lemma D_8f4f4 : decode_any W_8f4f4 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f4f8 : bv 32 := 0x03613823.
Lemma F_8f4f8 : fetch_word Plain.M.loaded_segments (0x8f550 : word) = Some W_8f4f8.
Proof. vm_refl. Qed.
Lemma D_8f4f8 : decode_any W_8f4f8 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f4fc : bv 32 := 0x03713423.
Lemma F_8f4fc : fetch_word Plain.M.loaded_segments (0x8f554 : word) = Some W_8f4fc.
Proof. vm_refl. Qed.
Lemma D_8f4fc : decode_any W_8f4fc = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f500 : bv 32 := 0x00060413.
Lemma F_8f500 : fetch_word Plain.M.loaded_segments (0x8f558 : word) = Some W_8f500.
Proof. vm_refl. Qed.
Lemma D_8f500 : decode_any W_8f500 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f504 : bv 32 := 0x00058913.
Lemma F_8f504 : fetch_word Plain.M.loaded_segments (0x8f55c : word) = Some W_8f504.
Proof. vm_refl. Qed.
Lemma D_8f504 : decode_any W_8f504 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f508 : bv 32 := 0x00810693.
Lemma F_8f508 : fetch_word Plain.M.loaded_segments (0x8f560 : word) = Some W_8f508.
Proof. vm_refl. Qed.
Lemma D_8f508 : decode_any W_8f508 = Some (OpImm ALU_ADD 13 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f50c : bv 32 := 0x170000ef.
Lemma F_8f50c : fetch_word Plain.M.loaded_segments (0x8f564 : word) = Some W_8f50c.
Proof. vm_refl. Qed.
Lemma D_8f50c : decode_any W_8f50c = Some (Jal 1 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f510 : bv 32 := 0x0e050263.
Lemma F_8f510 : fetch_word Plain.M.loaded_segments (0x8f568 : word) = Some W_8f510.
Proof. vm_refl. Qed.
Lemma D_8f510 : decode_any W_8f510 = Some (Branch BC_EQ 10 0 228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f514 : bv 32 := 0x00050493.
Lemma F_8f514 : fetch_word Plain.M.loaded_segments (0x8f56c : word) = Some W_8f514.
Proof. vm_refl. Qed.
Lemma D_8f514 : decode_any W_8f514 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f518 : bv 32 := 0x02410593.
Lemma F_8f518 : fetch_word Plain.M.loaded_segments (0x8f570 : word) = Some W_8f518.
Proof. vm_refl. Qed.
Lemma D_8f518 : decode_any W_8f518 = Some (OpImm ALU_ADD 11 2 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f51c : bv 32 := 0x02010613.
Lemma F_8f51c : fetch_word Plain.M.loaded_segments (0x8f574 : word) = Some W_8f51c.
Proof. vm_refl. Qed.
Lemma D_8f51c : decode_any W_8f51c = Some (OpImm ALU_ADD 12 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f520 : bv 32 := 0x00090513.
Lemma F_8f520 : fetch_word Plain.M.loaded_segments (0x8f578 : word) = Some W_8f520.
Proof. vm_refl. Qed.
Lemma D_8f520 : decode_any W_8f520 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f524 : bv 32 := 0x00000693.
Lemma F_8f524 : fetch_word Plain.M.loaded_segments (0x8f57c : word) = Some W_8f524.
Proof. vm_refl. Qed.
Lemma D_8f524 : decode_any W_8f524 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f528 : bv 32 := 0x879dd0ef.
Lemma F_8f528 : fetch_word Plain.M.loaded_segments (0x8f580 : word) = Some W_8f528.
Proof. vm_refl. Qed.
Lemma D_8f528 : decode_any W_8f528 = Some (Jal 1 1955960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f52c : bv 32 := 0x01810593.
Lemma F_8f52c : fetch_word Plain.M.loaded_segments (0x8f584 : word) = Some W_8f52c.
Proof. vm_refl. Qed.
Lemma D_8f52c : decode_any W_8f52c = Some (OpImm ALU_ADD 11 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f530 : bv 32 := 0x01c10613.
Lemma F_8f530 : fetch_word Plain.M.loaded_segments (0x8f588 : word) = Some W_8f530.
Proof. vm_refl. Qed.
Lemma D_8f530 : decode_any W_8f530 = Some (OpImm ALU_ADD 12 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f534 : bv 32 := 0x01010693.
Lemma F_8f534 : fetch_word Plain.M.loaded_segments (0x8f58c : word) = Some W_8f534.
Proof. vm_refl. Qed.
Lemma D_8f534 : decode_any W_8f534 = Some (OpImm ALU_ADD 13 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f538 : bv 32 := 0x01410713.
Lemma F_8f538 : fetch_word Plain.M.loaded_segments (0x8f590 : word) = Some W_8f538.
Proof. vm_refl. Qed.
Lemma D_8f538 : decode_any W_8f538 = Some (OpImm ALU_ADD 14 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f53c : bv 32 := 0x00040513.
Lemma F_8f53c : fetch_word Plain.M.loaded_segments (0x8f594 : word) = Some W_8f53c.
Proof. vm_refl. Qed.
Lemma D_8f53c : decode_any W_8f53c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f540 : bv 32 := 0x0b0030ef.
Lemma F_8f540 : fetch_word Plain.M.loaded_segments (0x8f598 : word) = Some W_8f540.
Proof. vm_refl. Qed.
Lemma D_8f540 : decode_any W_8f540 = Some (Jal 1 12464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f544 : bv 32 := 0x00048513.
Lemma F_8f544 : fetch_word Plain.M.loaded_segments (0x8f59c : word) = Some W_8f544.
Proof. vm_refl. Qed.
Lemma D_8f544 : decode_any W_8f544 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f548 : bv 32 := 0xf15de0ef.
Lemma F_8f548 : fetch_word Plain.M.loaded_segments (0x8f5a0 : word) = Some W_8f548.
Proof. vm_refl. Qed.
Lemma D_8f548 : decode_any W_8f548 = Some (Jal 1 1961748, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f54c : bv 32 := 0x01812583.
Lemma F_8f54c : fetch_word Plain.M.loaded_segments (0x8f5a4 : word) = Some W_8f54c.
Proof. vm_refl. Qed.
Lemma D_8f54c : decode_any W_8f54c = Some (Load SZ4 true 11 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f550 : bv 32 := 0x08b05c63.
Lemma F_8f550 : fetch_word Plain.M.loaded_segments (0x8f5a8 : word) = Some W_8f550.
Proof. vm_refl. Qed.
Lemma D_8f550 : decode_any W_8f550 = Some (Branch BC_GE 0 11 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f554 : bv 32 := 0x00000913.
Lemma F_8f554 : fetch_word Plain.M.loaded_segments (0x8f5ac : word) = Some W_8f554.
Proof. vm_refl. Qed.
Lemma D_8f554 : decode_any W_8f554 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f558 : bv 32 := 0x01c12503.
Lemma F_8f558 : fetch_word Plain.M.loaded_segments (0x8f5b0 : word) = Some W_8f558.
Proof. vm_refl. Qed.
Lemma D_8f558 : decode_any W_8f558 = Some (Load SZ4 true 10 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f55c : bv 32 := 0x00100993.
Lemma F_8f55c : fetch_word Plain.M.loaded_segments (0x8f5b4 : word) = Some W_8f55c.
Proof. vm_refl. Qed.
Lemma D_8f55c : decode_any W_8f55c = Some (OpImm ALU_ADD 19 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f560 : bv 32 := 0x0100006f.
Lemma F_8f560 : fetch_word Plain.M.loaded_segments (0x8f5b8 : word) = Some W_8f560.
Proof. vm_refl. Qed.
Lemma D_8f560 : decode_any W_8f560 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f564 : bv 32 := 0x01812583.
Lemma F_8f564 : fetch_word Plain.M.loaded_segments (0x8f5bc : word) = Some W_8f564.
Proof. vm_refl. Qed.
Lemma D_8f564 : decode_any W_8f564 = Some (Load SZ4 true 11 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f568 : bv 32 := 0x00190913.
Lemma F_8f568 : fetch_word Plain.M.loaded_segments (0x8f5c0 : word) = Some W_8f568.
Proof. vm_refl. Qed.
Lemma D_8f568 : decode_any W_8f568 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f56c : bv 32 := 0x06b95e63.
Lemma F_8f56c : fetch_word Plain.M.loaded_segments (0x8f5c4 : word) = Some W_8f56c.
Proof. vm_refl. Qed.
Lemma D_8f56c : decode_any W_8f56c = Some (Branch BC_GE 18 11 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f570 : bv 32 := 0xfea05ce3.
Lemma F_8f570 : fetch_word Plain.M.loaded_segments (0x8f5c8 : word) = Some W_8f570.
Proof. vm_refl. Qed.
Lemma D_8f570 : decode_any W_8f570 = Some (Branch BC_GE 0 10 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f574 : bv 32 := 0x00000a13.
Lemma F_8f574 : fetch_word Plain.M.loaded_segments (0x8f5cc : word) = Some W_8f574.
Proof. vm_refl. Qed.
Lemma D_8f574 : decode_any W_8f574 = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f578 : bv 32 := 0x00000a93.
Lemma F_8f578 : fetch_word Plain.M.loaded_segments (0x8f5d0 : word) = Some W_8f578.
Proof. vm_refl. Qed.
Lemma D_8f578 : decode_any W_8f578 = Some (OpImm ALU_ADD 21 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f57c : bv 32 := 0x00000b13.
Lemma F_8f57c : fetch_word Plain.M.loaded_segments (0x8f5d4 : word) = Some W_8f57c.
Proof. vm_refl. Qed.
Lemma D_8f57c : decode_any W_8f57c = Some (OpImm ALU_ADD 22 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f580 : bv 32 := 0x00391b93.
Lemma F_8f580 : fetch_word Plain.M.loaded_segments (0x8f5d8 : word) = Some W_8f580.
Proof. vm_refl. Qed.
Lemma D_8f580 : decode_any W_8f580 = Some (ShiftImm ALU_SLL 23 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f584 : bv 32 := 0x0140006f.
Lemma F_8f584 : fetch_word Plain.M.loaded_segments (0x8f5dc : word) = Some W_8f584.
Proof. vm_refl. Qed.
Lemma D_8f584 : decode_any W_8f584 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f588 : bv 32 := 0x001b0b13.
Lemma F_8f588 : fetch_word Plain.M.loaded_segments (0x8f5e0 : word) = Some W_8f588.
Proof. vm_refl. Qed.
Lemma D_8f588 : decode_any W_8f588 = Some (OpImm ALU_ADD 22 22 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f58c : bv 32 := 0x001a8a93.
Lemma F_8f58c : fetch_word Plain.M.loaded_segments (0x8f5e4 : word) = Some W_8f58c.
Proof. vm_refl. Qed.
Lemma D_8f58c : decode_any W_8f58c = Some (OpImm ALU_ADD 21 21 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f590 : bv 32 := 0x004a0a13.
Lemma F_8f590 : fetch_word Plain.M.loaded_segments (0x8f5e8 : word) = Some W_8f590.
Proof. vm_refl. Qed.
Lemma D_8f590 : decode_any W_8f590 = Some (OpImm ALU_ADD 20 20 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f594 : bv 32 := 0xfcab58e3.
Lemma F_8f594 : fetch_word Plain.M.loaded_segments (0x8f5ec : word) = Some W_8f594.
Proof. vm_refl. Qed.
Lemma D_8f594 : decode_any W_8f594 = Some (Branch BC_GE 22 10 8144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f598 : bv 32 := 0x01043583.
Lemma F_8f598 : fetch_word Plain.M.loaded_segments (0x8f5f0 : word) = Some W_8f598.
Proof. vm_refl. Qed.
Lemma D_8f598 : decode_any W_8f598 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f59c : bv 32 := 0x017585b3.
Lemma F_8f59c : fetch_word Plain.M.loaded_segments (0x8f5f4 : word) = Some W_8f59c.
Proof. vm_refl. Qed.
Lemma D_8f59c : decode_any W_8f59c = Some (Op ALU_ADD 11 11 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5a0 : bv 32 := 0x0005b583.
Lemma F_8f5a0 : fetch_word Plain.M.loaded_segments (0x8f5f8 : word) = Some W_8f5a0.
Proof. vm_refl. Qed.
Lemma D_8f5a0 : decode_any W_8f5a0 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5a4 : bv 32 := 0x014585b3.
Lemma F_8f5a4 : fetch_word Plain.M.loaded_segments (0x8f5fc : word) = Some W_8f5a4.
Proof. vm_refl. Qed.
Lemma D_8f5a4 : decode_any W_8f5a4 = Some (Op ALU_ADD 11 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5a8 : bv 32 := 0x0005a583.
Lemma F_8f5a8 : fetch_word Plain.M.loaded_segments (0x8f600 : word) = Some W_8f5a8.
Proof. vm_refl. Qed.
Lemma D_8f5a8 : decode_any W_8f5a8 = Some (Load SZ4 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5ac : bv 32 := 0xfd359ee3.
Lemma F_8f5ac : fetch_word Plain.M.loaded_segments (0x8f604 : word) = Some W_8f5ac.
Proof. vm_refl. Qed.
Lemma D_8f5ac : decode_any W_8f5ac = Some (Branch BC_NE 11 19 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5b0 : bv 32 := 0x01412503.
Lemma F_8f5b0 : fetch_word Plain.M.loaded_segments (0x8f608 : word) = Some W_8f5b0.
Proof. vm_refl. Qed.
Lemma D_8f5b0 : decode_any W_8f5b0 = Some (Load SZ4 true 10 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5b4 : bv 32 := 0x01012603.
Lemma F_8f5b4 : fetch_word Plain.M.loaded_segments (0x8f60c : word) = Some W_8f5b4.
Proof. vm_refl. Qed.
Lemma D_8f5b4 : decode_any W_8f5b4 = Some (Load SZ4 true 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5b8 : bv 32 := 0x02412683.
Lemma F_8f5b8 : fetch_word Plain.M.loaded_segments (0x8f610 : word) = Some W_8f5b8.
Proof. vm_refl. Qed.
Lemma D_8f5b8 : decode_any W_8f5b8 = Some (Load SZ4 true 13 2 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5bc : bv 32 := 0x02012703.
Lemma F_8f5bc : fetch_word Plain.M.loaded_segments (0x8f614 : word) = Some W_8f5bc.
Proof. vm_refl. Qed.
Lemma D_8f5bc : decode_any W_8f5bc = Some (Load SZ4 true 14 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5c0 : bv 32 := 0x00813803.
Lemma F_8f5c0 : fetch_word Plain.M.loaded_segments (0x8f618 : word) = Some W_8f5c0.
Proof. vm_refl. Qed.
Lemma D_8f5c0 : decode_any W_8f5c0 = Some (Load SZ8 true 16 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5c4 : bv 32 := 0x40aa85bb.
Lemma F_8f5c4 : fetch_word Plain.M.loaded_segments (0x8f61c : word) = Some W_8f5c4.
Proof. vm_refl. Qed.
Lemma D_8f5c4 : decode_any W_8f5c4 = Some (Op32 ALU_SUB 11 21 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5c8 : bv 32 := 0x40c9063b.
Lemma F_8f5c8 : fetch_word Plain.M.loaded_segments (0x8f620 : word) = Some W_8f5c8.
Proof. vm_refl. Qed.
Lemma D_8f5c8 : decode_any W_8f5c8 = Some (Op32 ALU_SUB 12 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5cc : bv 32 := 0x00e00793.
Lemma F_8f5cc : fetch_word Plain.M.loaded_segments (0x8f624 : word) = Some W_8f5cc.
Proof. vm_refl. Qed.
Lemma D_8f5cc : decode_any W_8f5cc = Some (OpImm ALU_ADD 15 0 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5d0 : bv 32 := 0x00013023.
Lemma F_8f5d0 : fetch_word Plain.M.loaded_segments (0x8f628 : word) = Some W_8f5d0.
Proof. vm_refl. Qed.
Lemma D_8f5d0 : decode_any W_8f5d0 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5d4 : bv 32 := 0x00048513.
Lemma F_8f5d4 : fetch_word Plain.M.loaded_segments (0x8f62c : word) = Some W_8f5d4.
Proof. vm_refl. Qed.
Lemma D_8f5d4 : decode_any W_8f5d4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5d8 : bv 32 := 0x00000893.
Lemma F_8f5d8 : fetch_word Plain.M.loaded_segments (0x8f630 : word) = Some W_8f5d8.
Proof. vm_refl. Qed.
Lemma D_8f5d8 : decode_any W_8f5d8 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5dc : bv 32 := 0x978ea0ef.
Lemma F_8f5dc : fetch_word Plain.M.loaded_segments (0x8f634 : word) = Some W_8f5dc.
Proof. vm_refl. Qed.
Lemma D_8f5dc : decode_any W_8f5dc = Some (Jal 1 2007416, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5e0 : bv 32 := 0x01c12503.
Lemma F_8f5e0 : fetch_word Plain.M.loaded_segments (0x8f638 : word) = Some W_8f5e0.
Proof. vm_refl. Qed.
Lemma D_8f5e0 : decode_any W_8f5e0 = Some (Load SZ4 true 10 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5e4 : bv 32 := 0xfa5ff06f.
Lemma F_8f5e4 : fetch_word Plain.M.loaded_segments (0x8f63c : word) = Some W_8f5e4.
Proof. vm_refl. Qed.
Lemma D_8f5e4 : decode_any W_8f5e4 = Some (Jal 0 2097060, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5e8 : bv 32 := 0x00810513.
Lemma F_8f5e8 : fetch_word Plain.M.loaded_segments (0x8f640 : word) = Some W_8f5e8.
Proof. vm_refl. Qed.
Lemma D_8f5e8 : decode_any W_8f5e8 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5ec : bv 32 := 0xcf8dd0ef.
Lemma F_8f5ec : fetch_word Plain.M.loaded_segments (0x8f644 : word) = Some W_8f5ec.
Proof. vm_refl. Qed.
Lemma D_8f5ec : decode_any W_8f5ec = Some (Jal 1 1955064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5f0 : bv 32 := 0x05c0006f.
Lemma F_8f5f0 : fetch_word Plain.M.loaded_segments (0x8f648 : word) = Some W_8f5f0.
Proof. vm_refl. Qed.
Lemma D_8f5f0 : decode_any W_8f5f0 = Some (Jal 0 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5f4 : bv 32 := 0x00083517.
Lemma F_8f5f4 : fetch_word Plain.M.loaded_segments (0x8f64c : word) = Some W_8f5f4.
Proof. vm_refl. Qed.
Lemma D_8f5f4 : decode_any W_8f5f4 = Some (Auipc 10 131, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5f8 : bv 32 := 0xf7c53503.
Lemma F_8f5f8 : fetch_word Plain.M.loaded_segments (0x8f650 : word) = Some W_8f5f8.
Proof. vm_refl. Qed.
Lemma D_8f5f8 : decode_any W_8f5f8 = Some (Load SZ8 true 10 10 3964, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f5fc : bv 32 := 0x00052503.
Lemma F_8f5fc : fetch_word Plain.M.loaded_segments (0x8f654 : word) = Some W_8f5fc.
Proof. vm_refl. Qed.
Lemma D_8f5fc : decode_any W_8f5fc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f600 : bv 32 := 0x00500593.
Lemma F_8f600 : fetch_word Plain.M.loaded_segments (0x8f658 : word) = Some W_8f600.
Proof. vm_refl. Qed.
Lemma D_8f600 : decode_any W_8f600 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f604 : bv 32 := 0x04a5c263.
Lemma F_8f604 : fetch_word Plain.M.loaded_segments (0x8f65c : word) = Some W_8f604.
Proof. vm_refl. Qed.
Lemma D_8f604 : decode_any W_8f604 = Some (Branch BC_LT 11 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f608 : bv 32 := 0xfff87517.
Lemma F_8f608 : fetch_word Plain.M.loaded_segments (0x8f660 : word) = Some W_8f608.
Proof. vm_refl. Qed.
Lemma D_8f608 : decode_any W_8f608 = Some (Auipc 10 1048455, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f60c : bv 32 := 0xfff89597.
Lemma F_8f60c : fetch_word Plain.M.loaded_segments (0x8f664 : word) = Some W_8f60c.
Proof. vm_refl. Qed.
Lemma D_8f60c : decode_any W_8f60c = Some (Auipc 11 1048457, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f610 : bv 32 := 0x46d50513.
Lemma F_8f610 : fetch_word Plain.M.loaded_segments (0x8f668 : word) = Some W_8f610.
Proof. vm_refl. Qed.
Lemma D_8f610 : decode_any W_8f610 = Some (OpImm ALU_ADD 10 10 1133, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f614 : bv 32 := 0x86358593.
Lemma F_8f614 : fetch_word Plain.M.loaded_segments (0x8f66c : word) = Some W_8f614.
Proof. vm_refl. Qed.
Lemma D_8f614 : decode_any W_8f614 = Some (OpImm ALU_ADD 11 11 2147, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f618 : bv 32 := 0x00000613.
Lemma F_8f618 : fetch_word Plain.M.loaded_segments (0x8f670 : word) = Some W_8f618.
Proof. vm_refl. Qed.
Lemma D_8f618 : decode_any W_8f618 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f61c : bv 32 := 0x06813083.
Lemma F_8f61c : fetch_word Plain.M.loaded_segments (0x8f674 : word) = Some W_8f61c.
Proof. vm_refl. Qed.
Lemma D_8f61c : decode_any W_8f61c = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f620 : bv 32 := 0x06013403.
Lemma F_8f620 : fetch_word Plain.M.loaded_segments (0x8f678 : word) = Some W_8f620.
Proof. vm_refl. Qed.
Lemma D_8f620 : decode_any W_8f620 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f624 : bv 32 := 0x05813483.
Lemma F_8f624 : fetch_word Plain.M.loaded_segments (0x8f67c : word) = Some W_8f624.
Proof. vm_refl. Qed.
Lemma D_8f624 : decode_any W_8f624 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f628 : bv 32 := 0x05013903.
Lemma F_8f628 : fetch_word Plain.M.loaded_segments (0x8f680 : word) = Some W_8f628.
Proof. vm_refl. Qed.
Lemma D_8f628 : decode_any W_8f628 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f62c : bv 32 := 0x04813983.
Lemma F_8f62c : fetch_word Plain.M.loaded_segments (0x8f684 : word) = Some W_8f62c.
Proof. vm_refl. Qed.
Lemma D_8f62c : decode_any W_8f62c = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f630 : bv 32 := 0x04013a03.
Lemma F_8f630 : fetch_word Plain.M.loaded_segments (0x8f688 : word) = Some W_8f630.
Proof. vm_refl. Qed.
Lemma D_8f630 : decode_any W_8f630 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f634 : bv 32 := 0x03813a83.
Lemma F_8f634 : fetch_word Plain.M.loaded_segments (0x8f68c : word) = Some W_8f634.
Proof. vm_refl. Qed.
Lemma D_8f634 : decode_any W_8f634 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f638 : bv 32 := 0x03013b03.
Lemma F_8f638 : fetch_word Plain.M.loaded_segments (0x8f690 : word) = Some W_8f638.
Proof. vm_refl. Qed.
Lemma D_8f638 : decode_any W_8f638 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f63c : bv 32 := 0x02813b83.
Lemma F_8f63c : fetch_word Plain.M.loaded_segments (0x8f694 : word) = Some W_8f63c.
Proof. vm_refl. Qed.
Lemma D_8f63c : decode_any W_8f63c = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f640 : bv 32 := 0x07010113.
Lemma F_8f640 : fetch_word Plain.M.loaded_segments (0x8f698 : word) = Some W_8f640.
Proof. vm_refl. Qed.
Lemma D_8f640 : decode_any W_8f640 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f644 : bv 32 := 0xa81d306f.
Lemma F_8f644 : fetch_word Plain.M.loaded_segments (0x8f69c : word) = Some W_8f644.
Proof. vm_refl. Qed.
Lemma D_8f644 : decode_any W_8f644 = Some (Jal 0 1915520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f64c : bv 32 := 0x00048513.
Lemma F_8f64c : fetch_word Plain.M.loaded_segments (0x8f6a4 : word) = Some W_8f64c.
Proof. vm_refl. Qed.
Lemma D_8f64c : decode_any W_8f64c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f650 : bv 32 := 0x06813083.
Lemma F_8f650 : fetch_word Plain.M.loaded_segments (0x8f6a8 : word) = Some W_8f650.
Proof. vm_refl. Qed.
Lemma D_8f650 : decode_any W_8f650 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f654 : bv 32 := 0x06013403.
Lemma F_8f654 : fetch_word Plain.M.loaded_segments (0x8f6ac : word) = Some W_8f654.
Proof. vm_refl. Qed.
Lemma D_8f654 : decode_any W_8f654 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f658 : bv 32 := 0x05813483.
Lemma F_8f658 : fetch_word Plain.M.loaded_segments (0x8f6b0 : word) = Some W_8f658.
Proof. vm_refl. Qed.
Lemma D_8f658 : decode_any W_8f658 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f65c : bv 32 := 0x05013903.
Lemma F_8f65c : fetch_word Plain.M.loaded_segments (0x8f6b4 : word) = Some W_8f65c.
Proof. vm_refl. Qed.
Lemma D_8f65c : decode_any W_8f65c = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f660 : bv 32 := 0x04813983.
Lemma F_8f660 : fetch_word Plain.M.loaded_segments (0x8f6b8 : word) = Some W_8f660.
Proof. vm_refl. Qed.
Lemma D_8f660 : decode_any W_8f660 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f664 : bv 32 := 0x04013a03.
Lemma F_8f664 : fetch_word Plain.M.loaded_segments (0x8f6bc : word) = Some W_8f664.
Proof. vm_refl. Qed.
Lemma D_8f664 : decode_any W_8f664 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f668 : bv 32 := 0x03813a83.
Lemma F_8f668 : fetch_word Plain.M.loaded_segments (0x8f6c0 : word) = Some W_8f668.
Proof. vm_refl. Qed.
Lemma D_8f668 : decode_any W_8f668 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f66c : bv 32 := 0x03013b03.
Lemma F_8f66c : fetch_word Plain.M.loaded_segments (0x8f6c4 : word) = Some W_8f66c.
Proof. vm_refl. Qed.
Lemma D_8f66c : decode_any W_8f66c = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f670 : bv 32 := 0x02813b83.
Lemma F_8f670 : fetch_word Plain.M.loaded_segments (0x8f6c8 : word) = Some W_8f670.
Proof. vm_refl. Qed.
Lemma D_8f670 : decode_any W_8f670 = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f674 : bv 32 := 0x07010113.
Lemma F_8f674 : fetch_word Plain.M.loaded_segments (0x8f6cc : word) = Some W_8f674.
Proof. vm_refl. Qed.
Lemma D_8f674 : decode_any W_8f674 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f678 : bv 32 := 0x00008067.
Lemma F_8f678 : fetch_word Plain.M.loaded_segments (0x8f6d0 : word) = Some W_8f678.
Proof. vm_refl. Qed.
Lemma D_8f678 : decode_any W_8f678 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

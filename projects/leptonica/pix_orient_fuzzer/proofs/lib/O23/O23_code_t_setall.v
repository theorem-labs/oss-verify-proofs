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
Definition W_6da28 : bv 32 := 0x00050663.
Lemma F_6da28 : fetch_word Plain.M.loaded_segments (0x6da80 : word) = Some W_6da28.
Proof. vm_refl. Qed.
Lemma D_6da28 : decode_any W_6da28 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6da2c : bv 32 := 0x03053503.
Lemma F_6da2c : fetch_word Plain.M.loaded_segments (0x6da84 : word) = Some W_6da2c.
Proof. vm_refl. Qed.
Lemma D_6da2c : decode_any W_6da2c = Some (Load SZ8 true 10 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6da30 : bv 32 := 0x00008067.
Lemma F_6da30 : fetch_word Plain.M.loaded_segments (0x6da88 : word) = Some W_6da30.
Proof. vm_refl. Qed.
Lemma D_6da30 : decode_any W_6da30 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e4c8 : bv 32 := 0xfe010113.
Lemma F_6e4c8 : fetch_word Plain.M.loaded_segments (0x6e520 : word) = Some W_6e4c8.
Proof. vm_refl. Qed.
Lemma D_6e4c8 : decode_any W_6e4c8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e4cc : bv 32 := 0x00113c23.
Lemma F_6e4cc : fetch_word Plain.M.loaded_segments (0x6e524 : word) = Some W_6e4cc.
Proof. vm_refl. Qed.
Lemma D_6e4cc : decode_any W_6e4cc = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e4d0 : bv 32 := 0x00813823.
Lemma F_6e4d0 : fetch_word Plain.M.loaded_segments (0x6e528 : word) = Some W_6e4d0.
Proof. vm_refl. Qed.
Lemma D_6e4d0 : decode_any W_6e4d0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e4d4 : bv 32 := 0x00913423.
Lemma F_6e4d4 : fetch_word Plain.M.loaded_segments (0x6e52c : word) = Some W_6e4d4.
Proof. vm_refl. Qed.
Lemma D_6e4d4 : decode_any W_6e4d4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e4d8 : bv 32 := 0x06050663.
Lemma F_6e4d8 : fetch_word Plain.M.loaded_segments (0x6e530 : word) = Some W_6e4d8.
Proof. vm_refl. Qed.
Lemma D_6e4d8 : decode_any W_6e4d8 = Some (Branch BC_EQ 10 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e4dc : bv 32 := 0x00050413.
Lemma F_6e4dc : fetch_word Plain.M.loaded_segments (0x6e534 : word) = Some W_6e4dc.
Proof. vm_refl. Qed.
Lemma D_6e4dc : decode_any W_6e4dc = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e4e0 : bv 32 := 0xd48ff0ef.
Lemma F_6e4e0 : fetch_word Plain.M.loaded_segments (0x6e538 : word) = Some W_6e4e0.
Proof. vm_refl. Qed.
Lemma D_6e4e0 : decode_any W_6e4e0 = Some (Jal 1 2094408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e4e4 : bv 32 := 0x02050e63.
Lemma F_6e4e4 : fetch_word Plain.M.loaded_segments (0x6e53c : word) = Some W_6e4e4.
Proof. vm_refl. Qed.
Lemma D_6e4e4 : decode_any W_6e4e4 = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e4e8 : bv 32 := 0x00050493.
Lemma F_6e4e8 : fetch_word Plain.M.loaded_segments (0x6e540 : word) = Some W_6e4e8.
Proof. vm_refl. Qed.
Lemma D_6e4e8 : decode_any W_6e4e8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e4ec : bv 32 := 0x5e1020ef.
Lemma F_6e4ec : fetch_word Plain.M.loaded_segments (0x6e544 : word) = Some W_6e4ec.
Proof. vm_refl. Qed.
Lemma D_6e4ec : decode_any W_6e4ec = Some (Jal 1 11744, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e4f0 : bv 32 := 0x00c4a583.
Lemma F_6e4f0 : fetch_word Plain.M.loaded_segments (0x6e548 : word) = Some W_6e4f0.
Proof. vm_refl. Qed.
Lemma D_6e4f0 : decode_any W_6e4f0 = Some (Load SZ4 true 11 9 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e4f4 : bv 32 := 0x02b55663.
Lemma F_6e4f4 : fetch_word Plain.M.loaded_segments (0x6e54c : word) = Some W_6e4f4.
Proof. vm_refl. Qed.
Lemma D_6e4f4 : decode_any W_6e4f4 = Some (Branch BC_GE 10 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e4f8 : bv 32 := 0x000a4517.
Lemma F_6e4f8 : fetch_word Plain.M.loaded_segments (0x6e550 : word) = Some W_6e4f8.
Proof. vm_refl. Qed.
Lemma D_6e4f8 : decode_any W_6e4f8 = Some (Auipc 10 164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e4fc : bv 32 := 0x07853503.
Lemma F_6e4fc : fetch_word Plain.M.loaded_segments (0x6e554 : word) = Some W_6e4fc.
Proof. vm_refl. Qed.
Lemma D_6e4fc : decode_any W_6e4fc = Some (Load SZ8 true 10 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e500 : bv 32 := 0x00052503.
Lemma F_6e500 : fetch_word Plain.M.loaded_segments (0x6e558 : word) = Some W_6e500.
Proof. vm_refl. Qed.
Lemma D_6e500 : decode_any W_6e500 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e504 : bv 32 := 0x00500593.
Lemma F_6e504 : fetch_word Plain.M.loaded_segments (0x6e55c : word) = Some W_6e504.
Proof. vm_refl. Qed.
Lemma D_6e504 : decode_any W_6e504 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e508 : bv 32 := 0x06a5cc63.
Lemma F_6e508 : fetch_word Plain.M.loaded_segments (0x6e560 : word) = Some W_6e508.
Proof. vm_refl. Qed.
Lemma D_6e508 : decode_any W_6e508 = Some (Branch BC_LT 11 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e50c : bv 32 := 0xfffaf517.
Lemma F_6e50c : fetch_word Plain.M.loaded_segments (0x6e564 : word) = Some W_6e50c.
Proof. vm_refl. Qed.
Lemma D_6e50c : decode_any W_6e50c = Some (Auipc 10 1048495, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e510 : bv 32 := 0xfffa6597.
Lemma F_6e510 : fetch_word Plain.M.loaded_segments (0x6e568 : word) = Some W_6e510.
Proof. vm_refl. Qed.
Lemma D_6e510 : decode_any W_6e510 = Some (Auipc 11 1048486, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e514 : bv 32 := 0x00150513.
Lemma F_6e514 : fetch_word Plain.M.loaded_segments (0x6e56c : word) = Some W_6e514.
Proof. vm_refl. Qed.
Lemma D_6e514 : decode_any W_6e514 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e518 : bv 32 := 0x56b58593.
Lemma F_6e518 : fetch_word Plain.M.loaded_segments (0x6e570 : word) = Some W_6e518.
Proof. vm_refl. Qed.
Lemma D_6e518 : decode_any W_6e518 = Some (OpImm ALU_ADD 11 11 1387, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e51c : bv 32 := 0x04c0006f.
Lemma F_6e51c : fetch_word Plain.M.loaded_segments (0x6e574 : word) = Some W_6e51c.
Proof. vm_refl. Qed.
Lemma D_6e51c : decode_any W_6e51c = Some (Jal 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e520 : bv 32 := 0x00446583.
Lemma F_6e520 : fetch_word Plain.M.loaded_segments (0x6e578 : word) = Some W_6e520.
Proof. vm_refl. Qed.
Lemma D_6e520 : decode_any W_6e520 = Some (Load SZ4 false 11 8 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e524 : bv 32 := 0x01046603.
Lemma F_6e524 : fetch_word Plain.M.loaded_segments (0x6e57c : word) = Some W_6e524.
Proof. vm_refl. Qed.
Lemma D_6e524 : decode_any W_6e524 = Some (Load SZ4 false 12 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e528 : bv 32 := 0x03843503.
Lemma F_6e528 : fetch_word Plain.M.loaded_segments (0x6e580 : word) = Some W_6e528.
Proof. vm_refl. Qed.
Lemma D_6e528 : decode_any W_6e528 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e52c : bv 32 := 0x02b60633.
Lemma F_6e52c : fetch_word Plain.M.loaded_segments (0x6e584 : word) = Some W_6e52c.
Proof. vm_refl. Qed.
Lemma D_6e52c : decode_any W_6e52c = Some (Mul M_MUL 12 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e530 : bv 32 := 0x00261613.
Lemma F_6e530 : fetch_word Plain.M.loaded_segments (0x6e588 : word) = Some W_6e530.
Proof. vm_refl. Qed.
Lemma D_6e530 : decode_any W_6e530 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e534 : bv 32 := 0x0ff00593.
Lemma F_6e534 : fetch_word Plain.M.loaded_segments (0x6e58c : word) = Some W_6e534.
Proof. vm_refl. Qed.
Lemma D_6e534 : decode_any W_6e534 = Some (OpImm ALU_ADD 11 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e538 : bv 32 := 0x4a19b0ef.
Lemma F_6e538 : fetch_word Plain.M.loaded_segments (0x6e590 : word) = Some W_6e538.
Proof. vm_refl. Qed.
Lemma D_6e538 : decode_any W_6e538 = Some (Jal 1 638112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e568 : bv 32 := 0x00100613.
Lemma F_6e568 : fetch_word Plain.M.loaded_segments (0x6e5c0 : word) = Some W_6e568.
Proof. vm_refl. Qed.
Lemma D_6e568 : decode_any W_6e568 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e56c : bv 32 := 0x01813083.
Lemma F_6e56c : fetch_word Plain.M.loaded_segments (0x6e5c4 : word) = Some W_6e56c.
Proof. vm_refl. Qed.
Lemma D_6e56c : decode_any W_6e56c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e570 : bv 32 := 0x01013403.
Lemma F_6e570 : fetch_word Plain.M.loaded_segments (0x6e5c8 : word) = Some W_6e570.
Proof. vm_refl. Qed.
Lemma D_6e570 : decode_any W_6e570 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e574 : bv 32 := 0x00813483.
Lemma F_6e574 : fetch_word Plain.M.loaded_segments (0x6e5cc : word) = Some W_6e574.
Proof. vm_refl. Qed.
Lemma D_6e574 : decode_any W_6e574 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e578 : bv 32 := 0x02010113.
Lemma F_6e578 : fetch_word Plain.M.loaded_segments (0x6e5d0 : word) = Some W_6e578.
Proof. vm_refl. Qed.
Lemma D_6e578 : decode_any W_6e578 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e57c : bv 32 := 0xa79f406f.
Lemma F_6e57c : fetch_word Plain.M.loaded_segments (0x6e5d4 : word) = Some W_6e57c.
Proof. vm_refl. Qed.
Lemma D_6e57c : decode_any W_6e57c = Some (Jal 0 2050680, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_712cc : bv 32 := 0x00050663.
Lemma F_712cc : fetch_word Plain.M.loaded_segments (0x71324 : word) = Some W_712cc.
Proof. vm_refl. Qed.
Lemma D_712cc : decode_any W_712cc = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_712d0 : bv 32 := 0x01052503.
Lemma F_712d0 : fetch_word Plain.M.loaded_segments (0x71328 : word) = Some W_712d0.
Proof. vm_refl. Qed.
Lemma D_712d0 : decode_any W_712d0 = Some (Load SZ4 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_712d4 : bv 32 := 0x00008067.
Lemma F_712d4 : fetch_word Plain.M.loaded_segments (0x7132c : word) = Some W_712d4.
Proof. vm_refl. Qed.
Lemma D_712d4 : decode_any W_712d4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.


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
Definition W_1949c : bv 32 := 0xff010113.
Lemma F_1949c : fetch_word Plain.M.loaded_segments (0x194f4 : word) = Some W_1949c.
Proof. vm_refl. Qed.
Lemma D_1949c : decode_any W_1949c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_194a0 : bv 32 := 0x00113423.
Lemma F_194a0 : fetch_word Plain.M.loaded_segments (0x194f8 : word) = Some W_194a0.
Proof. vm_refl. Qed.
Lemma D_194a0 : decode_any W_194a0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_194a4 : bv 32 := 0x00813023.
Lemma F_194a4 : fetch_word Plain.M.loaded_segments (0x194fc : word) = Some W_194a4.
Proof. vm_refl. Qed.
Lemma D_194a4 : decode_any W_194a4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_194a8 : bv 32 := 0x02050c63.
Lemma F_194a8 : fetch_word Plain.M.loaded_segments (0x19500 : word) = Some W_194a8.
Proof. vm_refl. Qed.
Lemma D_194a8 : decode_any W_194a8 = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_194ac : bv 32 := 0x0a8000ef.
Lemma F_194ac : fetch_word Plain.M.loaded_segments (0x19504 : word) = Some W_194ac.
Proof. vm_refl. Qed.
Lemma D_194ac : decode_any W_194ac = Some (Jal 1 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_194b0 : bv 32 := 0x04050c63.
Lemma F_194b0 : fetch_word Plain.M.loaded_segments (0x19508 : word) = Some W_194b0.
Proof. vm_refl. Qed.
Lemma D_194b0 : decode_any W_194b0 = Some (Branch BC_EQ 10 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_194b4 : bv 32 := 0x00456603.
Lemma F_194b4 : fetch_word Plain.M.loaded_segments (0x1950c : word) = Some W_194b4.
Proof. vm_refl. Qed.
Lemma D_194b4 : decode_any W_194b4 = Some (Load SZ4 false 12 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_194b8 : bv 32 := 0x01056683.
Lemma F_194b8 : fetch_word Plain.M.loaded_segments (0x19510 : word) = Some W_194b8.
Proof. vm_refl. Qed.
Lemma D_194b8 : decode_any W_194b8 = Some (Load SZ4 false 13 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_194bc : bv 32 := 0x03853583.
Lemma F_194bc : fetch_word Plain.M.loaded_segments (0x19514 : word) = Some W_194bc.
Proof. vm_refl. Qed.
Lemma D_194bc : decode_any W_194bc = Some (Load SZ8 true 11 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_194c0 : bv 32 := 0x02c68633.
Lemma F_194c0 : fetch_word Plain.M.loaded_segments (0x19518 : word) = Some W_194c0.
Proof. vm_refl. Qed.
Lemma D_194c0 : decode_any W_194c0 = Some (Mul M_MUL 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_194c4 : bv 32 := 0x00261613.
Lemma F_194c4 : fetch_word Plain.M.loaded_segments (0x1951c : word) = Some W_194c4.
Proof. vm_refl. Qed.
Lemma D_194c4 : decode_any W_194c4 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_194c8 : bv 32 := 0x00050413.
Lemma F_194c8 : fetch_word Plain.M.loaded_segments (0x19520 : word) = Some W_194c8.
Proof. vm_refl. Qed.
Lemma D_194c8 : decode_any W_194c8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_194cc : bv 32 := 0x00058513.
Lemma F_194cc : fetch_word Plain.M.loaded_segments (0x19524 : word) = Some W_194cc.
Proof. vm_refl. Qed.
Lemma D_194cc : decode_any W_194cc = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_194d0 : bv 32 := 0x00000593.
Lemma F_194d0 : fetch_word Plain.M.loaded_segments (0x19528 : word) = Some W_194d0.
Proof. vm_refl. Qed.
Lemma D_194d0 : decode_any W_194d0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_194d4 : bv 32 := 0x1311d0ef.
Lemma F_194d4 : fetch_word Plain.M.loaded_segments (0x1952c : word) = Some W_194d4.
Proof. vm_refl. Qed.
Lemma D_194d4 : decode_any W_194d4 = Some (Jal 1 121136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_194d8 : bv 32 := 0x00040513.
Lemma F_194d8 : fetch_word Plain.M.loaded_segments (0x19530 : word) = Some W_194d8.
Proof. vm_refl. Qed.
Lemma D_194d8 : decode_any W_194d8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_194dc : bv 32 := 0x0680006f.
Lemma F_194dc : fetch_word Plain.M.loaded_segments (0x19534 : word) = Some W_194dc.
Proof. vm_refl. Qed.
Lemma D_194dc : decode_any W_194dc = Some (Jal 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19508 : bv 32 := 0x0001f517.
Lemma F_19508 : fetch_word Plain.M.loaded_segments (0x19560 : word) = Some W_19508.
Proof. vm_refl. Qed.
Lemma D_19508 : decode_any W_19508 = Some (Auipc 10 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1950c : bv 32 := 0xf1053503.
Lemma F_1950c : fetch_word Plain.M.loaded_segments (0x19564 : word) = Some W_1950c.
Proof. vm_refl. Qed.
Lemma D_1950c : decode_any W_1950c = Some (Load SZ8 true 10 10 3856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19510 : bv 32 := 0x00052503.
Lemma F_19510 : fetch_word Plain.M.loaded_segments (0x19568 : word) = Some W_19510.
Proof. vm_refl. Qed.
Lemma D_19510 : decode_any W_19510 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19514 : bv 32 := 0x00500593.
Lemma F_19514 : fetch_word Plain.M.loaded_segments (0x1956c : word) = Some W_19514.
Proof. vm_refl. Qed.
Lemma D_19514 : decode_any W_19514 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19518 : bv 32 := 0x02a5c463.
Lemma F_19518 : fetch_word Plain.M.loaded_segments (0x19570 : word) = Some W_19518.
Proof. vm_refl. Qed.
Lemma D_19518 : decode_any W_19518 = Some (Branch BC_LT 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1951c : bv 32 := 0xffff7517.
Lemma F_1951c : fetch_word Plain.M.loaded_segments (0x19574 : word) = Some W_1951c.
Proof. vm_refl. Qed.
Lemma D_1951c : decode_any W_1951c = Some (Auipc 10 1048567, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19520 : bv 32 := 0xffff8597.
Lemma F_19520 : fetch_word Plain.M.loaded_segments (0x19578 : word) = Some W_19520.
Proof. vm_refl. Qed.
Lemma D_19520 : decode_any W_19520 = Some (Auipc 11 1048568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19524 : bv 32 := 0x1e450513.
Lemma F_19524 : fetch_word Plain.M.loaded_segments (0x1957c : word) = Some W_19524.
Proof. vm_refl. Qed.
Lemma D_19524 : decode_any W_19524 = Some (OpImm ALU_ADD 10 10 484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19528 : bv 32 := 0x25258593.
Lemma F_19528 : fetch_word Plain.M.loaded_segments (0x19580 : word) = Some W_19528.
Proof. vm_refl. Qed.
Lemma D_19528 : decode_any W_19528 = Some (OpImm ALU_ADD 11 11 594, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1952c : bv 32 := 0x00000613.
Lemma F_1952c : fetch_word Plain.M.loaded_segments (0x19584 : word) = Some W_1952c.
Proof. vm_refl. Qed.
Lemma D_1952c : decode_any W_1952c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19530 : bv 32 := 0x00813083.
Lemma F_19530 : fetch_word Plain.M.loaded_segments (0x19588 : word) = Some W_19530.
Proof. vm_refl. Qed.
Lemma D_19530 : decode_any W_19530 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19534 : bv 32 := 0x00013403.
Lemma F_19534 : fetch_word Plain.M.loaded_segments (0x1958c : word) = Some W_19534.
Proof. vm_refl. Qed.
Lemma D_19534 : decode_any W_19534 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19538 : bv 32 := 0x01010113.
Lemma F_19538 : fetch_word Plain.M.loaded_segments (0x19590 : word) = Some W_19538.
Proof. vm_refl. Qed.
Lemma D_19538 : decode_any W_19538 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1953c : bv 32 := 0xee0fe06f.
Lemma F_1953c : fetch_word Plain.M.loaded_segments (0x19594 : word) = Some W_1953c.
Proof. vm_refl. Qed.
Lemma D_1953c : decode_any W_1953c = Some (Jal 0 2090720, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19544 : bv 32 := 0x00813083.
Lemma F_19544 : fetch_word Plain.M.loaded_segments (0x1959c : word) = Some W_19544.
Proof. vm_refl. Qed.
Lemma D_19544 : decode_any W_19544 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19548 : bv 32 := 0x00013403.
Lemma F_19548 : fetch_word Plain.M.loaded_segments (0x195a0 : word) = Some W_19548.
Proof. vm_refl. Qed.
Lemma D_19548 : decode_any W_19548 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1954c : bv 32 := 0x01010113.
Lemma F_1954c : fetch_word Plain.M.loaded_segments (0x195a4 : word) = Some W_1954c.
Proof. vm_refl. Qed.
Lemma D_1954c : decode_any W_1954c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19550 : bv 32 := 0x00008067.
Lemma F_19550 : fetch_word Plain.M.loaded_segments (0x195a8 : word) = Some W_19550.
Proof. vm_refl. Qed.
Lemma D_19550 : decode_any W_19550 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_1970c : bv 32 := 0x02058063.
Lemma F_1970c : fetch_word Plain.M.loaded_segments (0x19764 : word) = Some W_1970c.
Proof. vm_refl. Qed.
Lemma D_1970c : decode_any W_1970c = Some (Branch BC_EQ 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19710 : bv 32 := 0x04050463.
Lemma F_19710 : fetch_word Plain.M.loaded_segments (0x19768 : word) = Some W_19710.
Proof. vm_refl. Qed.
Lemma D_19710 : decode_any W_19710 = Some (Branch BC_EQ 10 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19714 : bv 32 := 0x06a58c63.
Lemma F_19714 : fetch_word Plain.M.loaded_segments (0x1976c : word) = Some W_19714.
Proof. vm_refl. Qed.
Lemma D_19714 : decode_any W_19714 = Some (Branch BC_EQ 11 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19718 : bv 32 := 0x00050613.
Lemma F_19718 : fetch_word Plain.M.loaded_segments (0x19770 : word) = Some W_19718.
Proof. vm_refl. Qed.
Lemma D_19718 : decode_any W_19718 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1971c : bv 32 := 0x00000513.
Lemma F_1971c : fetch_word Plain.M.loaded_segments (0x19774 : word) = Some W_1971c.
Proof. vm_refl. Qed.
Lemma D_1971c : decode_any W_1971c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19720 : bv 32 := 0x0185b583.
Lemma F_19720 : fetch_word Plain.M.loaded_segments (0x19778 : word) = Some W_19720.
Proof. vm_refl. Qed.
Lemma D_19720 : decode_any W_19720 = Some (Load SZ8 true 11 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19724 : bv 32 := 0x00b63c23.
Lemma F_19724 : fetch_word Plain.M.loaded_segments (0x1977c : word) = Some W_19724.
Proof. vm_refl. Qed.
Lemma D_19724 : decode_any W_19724 = Some (Store SZ8 12 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19728 : bv 32 := 0x00008067.
Lemma F_19728 : fetch_word Plain.M.loaded_segments (0x19780 : word) = Some W_19728.
Proof. vm_refl. Qed.
Lemma D_19728 : decode_any W_19728 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.


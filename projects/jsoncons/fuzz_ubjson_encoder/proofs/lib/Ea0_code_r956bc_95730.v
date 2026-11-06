(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_96500 : bv 32 := 0xfe010113.
Lemma F_96500 : fetch_word Asan.M.loaded_segments (0x96550 : word) = Some W_96500.
Proof. vm_refl. Qed.
Lemma D_96500 : decode_any W_96500 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_96504 : bv 32 := 0x00113c23.
Lemma F_96504 : fetch_word Asan.M.loaded_segments (0x96554 : word) = Some W_96504.
Proof. vm_refl. Qed.
Lemma D_96504 : decode_any W_96504 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_96508 : bv 32 := 0x00813823.
Lemma F_96508 : fetch_word Asan.M.loaded_segments (0x96558 : word) = Some W_96508.
Proof. vm_refl. Qed.
Lemma D_96508 : decode_any W_96508 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9650c : bv 32 := 0x00913423.
Lemma F_9650c : fetch_word Asan.M.loaded_segments (0x9655c : word) = Some W_9650c.
Proof. vm_refl. Qed.
Lemma D_9650c : decode_any W_9650c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_96510 : bv 32 := 0x01213023.
Lemma F_96510 : fetch_word Asan.M.loaded_segments (0x96560 : word) = Some W_96510.
Proof. vm_refl. Qed.
Lemma D_96510 : decode_any W_96510 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_96514 : bv 32 := 0x00060413.
Lemma F_96514 : fetch_word Asan.M.loaded_segments (0x96564 : word) = Some W_96514.
Proof. vm_refl. Qed.
Lemma D_96514 : decode_any W_96514 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_96518 : bv 32 := 0x00058493.
Lemma F_96518 : fetch_word Asan.M.loaded_segments (0x96568 : word) = Some W_96518.
Proof. vm_refl. Qed.
Lemma D_96518 : decode_any W_96518 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9651c : bv 32 := 0x00058513.
Lemma F_9651c : fetch_word Asan.M.loaded_segments (0x9656c : word) = Some W_9651c.
Proof. vm_refl. Qed.
Lemma D_9651c : decode_any W_9651c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_96520 : bv 32 := 0x00060593.
Lemma F_96520 : fetch_word Asan.M.loaded_segments (0x96570 : word) = Some W_96520.
Proof. vm_refl. Qed.
Lemma D_96520 : decode_any W_96520 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_96524 : bv 32 := 0x00068613.
Lemma F_96524 : fetch_word Asan.M.loaded_segments (0x96574 : word) = Some W_96524.
Proof. vm_refl. Qed.
Lemma D_96524 : decode_any W_96524 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_96528 : bv 32 := 0xf19f70ef.
Lemma F_96528 : fetch_word Asan.M.loaded_segments (0x96578 : word) = Some W_96528.
Proof. vm_refl. Qed.
Lemma D_96528 : decode_any W_96528 = Some (Jal 1 2064152, 4%Z).
Proof. vm_refl. Qed.

Definition W_9652c : bv 32 := 0x00050e63.
Lemma F_9652c : fetch_word Asan.M.loaded_segments (0x9657c : word) = Some W_9652c.
Proof. vm_refl. Qed.
Lemma D_9652c : decode_any W_9652c = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_96530 : bv 32 := 0x01813083.
Lemma F_96530 : fetch_word Asan.M.loaded_segments (0x96580 : word) = Some W_96530.
Proof. vm_refl. Qed.
Lemma D_96530 : decode_any W_96530 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_96534 : bv 32 := 0x01013403.
Lemma F_96534 : fetch_word Asan.M.loaded_segments (0x96584 : word) = Some W_96534.
Proof. vm_refl. Qed.
Lemma D_96534 : decode_any W_96534 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_96538 : bv 32 := 0x00813483.
Lemma F_96538 : fetch_word Asan.M.loaded_segments (0x96588 : word) = Some W_96538.
Proof. vm_refl. Qed.
Lemma D_96538 : decode_any W_96538 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9653c : bv 32 := 0x00013903.
Lemma F_9653c : fetch_word Asan.M.loaded_segments (0x9658c : word) = Some W_9653c.
Proof. vm_refl. Qed.
Lemma D_9653c : decode_any W_9653c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_96540 : bv 32 := 0x02010113.
Lemma F_96540 : fetch_word Asan.M.loaded_segments (0x96590 : word) = Some W_96540.
Proof. vm_refl. Qed.
Lemma D_96540 : decode_any W_96540 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_96544 : bv 32 := 0x00008067.
Lemma F_96544 : fetch_word Asan.M.loaded_segments (0x96594 : word) = Some W_96544.
Proof. vm_refl. Qed.
Lemma D_96544 : decode_any W_96544 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_96548 : bv 32 := 0x00050913.
Lemma F_96548 : fetch_word Asan.M.loaded_segments (0x96598 : word) = Some W_96548.
Proof. vm_refl. Qed.
Lemma D_96548 : decode_any W_96548 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9654c : bv 32 := 0x00048513.
Lemma F_9654c : fetch_word Asan.M.loaded_segments (0x9659c : word) = Some W_9654c.
Proof. vm_refl. Qed.
Lemma D_9654c : decode_any W_9654c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_96550 : bv 32 := 0x00040593.
Lemma F_96550 : fetch_word Asan.M.loaded_segments (0x965a0 : word) = Some W_96550.
Proof. vm_refl. Qed.
Lemma D_96550 : decode_any W_96550 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_96554 : bv 32 := 0x020000ef.
Lemma F_96554 : fetch_word Asan.M.loaded_segments (0x965a4 : word) = Some W_96554.
Proof. vm_refl. Qed.
Lemma D_96554 : decode_any W_96554 = Some (Jal 1 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_96558 : bv 32 := 0x00090513.
Lemma F_96558 : fetch_word Asan.M.loaded_segments (0x965a8 : word) = Some W_96558.
Proof. vm_refl. Qed.
Lemma D_96558 : decode_any W_96558 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9655c : bv 32 := 0x01813083.
Lemma F_9655c : fetch_word Asan.M.loaded_segments (0x965ac : word) = Some W_9655c.
Proof. vm_refl. Qed.
Lemma D_9655c : decode_any W_9655c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_96560 : bv 32 := 0x01013403.
Lemma F_96560 : fetch_word Asan.M.loaded_segments (0x965b0 : word) = Some W_96560.
Proof. vm_refl. Qed.
Lemma D_96560 : decode_any W_96560 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_96564 : bv 32 := 0x00813483.
Lemma F_96564 : fetch_word Asan.M.loaded_segments (0x965b4 : word) = Some W_96564.
Proof. vm_refl. Qed.
Lemma D_96564 : decode_any W_96564 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_96568 : bv 32 := 0x00013903.
Lemma F_96568 : fetch_word Asan.M.loaded_segments (0x965b8 : word) = Some W_96568.
Proof. vm_refl. Qed.
Lemma D_96568 : decode_any W_96568 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9656c : bv 32 := 0x02010113.
Lemma F_9656c : fetch_word Asan.M.loaded_segments (0x965bc : word) = Some W_9656c.
Proof. vm_refl. Qed.
Lemma D_9656c : decode_any W_9656c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_96570 : bv 32 := 0x00008067.
Lemma F_96570 : fetch_word Asan.M.loaded_segments (0x965c0 : word) = Some W_96570.
Proof. vm_refl. Qed.
Lemma D_96570 : decode_any W_96570 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

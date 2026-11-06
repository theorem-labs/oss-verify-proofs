(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_3447c : bv 32 := 0x00050663.
Lemma F_3447c : fetch_word Plain.M.loaded_segments (0x344d4 : word) = Some W_3447c.
Proof. vm_refl. Qed.
Lemma D_3447c : decode_any W_3447c = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_34488 : bv 32 := 0x00085517.
Lemma F_34488 : fetch_word Plain.M.loaded_segments (0x344e0 : word) = Some W_34488.
Proof. vm_refl. Qed.
Lemma D_34488 : decode_any W_34488 = Some (Auipc 10 133, 4%Z).
Proof. vm_refl. Qed.

Definition W_3448c : bv 32 := 0x12850593.
Lemma F_3448c : fetch_word Plain.M.loaded_segments (0x344e4 : word) = Some W_3448c.
Proof. vm_refl. Qed.
Lemma D_3448c : decode_any W_3448c = Some (OpImm ALU_ADD 11 10 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_34490 : bv 32 := 0x00100513.
Lemma F_34490 : fetch_word Plain.M.loaded_segments (0x344e8 : word) = Some W_34490.
Proof. vm_refl. Qed.
Lemma D_34490 : decode_any W_34490 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_34494 : bv 32 := 0x00a58023.
Lemma F_34494 : fetch_word Plain.M.loaded_segments (0x344ec : word) = Some W_34494.
Proof. vm_refl. Qed.
Lemma D_34494 : decode_any W_34494 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_34498 : bv 32 := 0x00084517.
Lemma F_34498 : fetch_word Plain.M.loaded_segments (0x344f0 : word) = Some W_34498.
Proof. vm_refl. Qed.
Lemma D_34498 : decode_any W_34498 = Some (Auipc 10 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_3449c : bv 32 := 0xc4853503.
Lemma F_3449c : fetch_word Plain.M.loaded_segments (0x344f4 : word) = Some W_3449c.
Proof. vm_refl. Qed.
Lemma D_3449c : decode_any W_3449c = Some (Load SZ8 true 10 10 3144, 4%Z).
Proof. vm_refl. Qed.

Definition W_344a0 : bv 32 := 0x00050e63.
Lemma F_344a0 : fetch_word Plain.M.loaded_segments (0x344f8 : word) = Some W_344a0.
Proof. vm_refl. Qed.
Lemma D_344a0 : decode_any W_344a0 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_344bc : bv 32 := 0x00084517.
Lemma F_344bc : fetch_word Plain.M.loaded_segments (0x34514 : word) = Some W_344bc.
Proof. vm_refl. Qed.
Lemma D_344bc : decode_any W_344bc = Some (Auipc 10 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_344c0 : bv 32 := 0xc2c53503.
Lemma F_344c0 : fetch_word Plain.M.loaded_segments (0x34518 : word) = Some W_344c0.
Proof. vm_refl. Qed.
Lemma D_344c0 : decode_any W_344c0 = Some (Load SZ8 true 10 10 3116, 4%Z).
Proof. vm_refl. Qed.

Definition W_344c4 : bv 32 := 0x00050c63.
Lemma F_344c4 : fetch_word Plain.M.loaded_segments (0x3451c : word) = Some W_344c4.
Proof. vm_refl. Qed.
Lemma D_344c4 : decode_any W_344c4 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_344dc : bv 32 := 0x00813083.
Lemma F_344dc : fetch_word Plain.M.loaded_segments (0x34534 : word) = Some W_344dc.
Proof. vm_refl. Qed.
Lemma D_344dc : decode_any W_344dc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_344e0 : bv 32 := 0x00013403.
Lemma F_344e0 : fetch_word Plain.M.loaded_segments (0x34538 : word) = Some W_344e0.
Proof. vm_refl. Qed.
Lemma D_344e0 : decode_any W_344e0 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_344e4 : bv 32 := 0x01010113.
Lemma F_344e4 : fetch_word Plain.M.loaded_segments (0x3453c : word) = Some W_344e4.
Proof. vm_refl. Qed.
Lemma D_344e4 : decode_any W_344e4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_344e8 : bv 32 := 0x00008067.
Lemma F_344e8 : fetch_word Plain.M.loaded_segments (0x34540 : word) = Some W_344e8.
Proof. vm_refl. Qed.
Lemma D_344e8 : decode_any W_344e8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_34540 : bv 32 := 0x24050a63.
Lemma F_34540 : fetch_word Plain.M.loaded_segments (0x34598 : word) = Some W_34540.
Proof. vm_refl. Qed.
Lemma D_34540 : decode_any W_34540 = Some (Branch BC_EQ 10 0 596, 4%Z).
Proof. vm_refl. Qed.

Definition W_34580 : bv 32 := 0x01a9d513.
Lemma F_34580 : fetch_word Plain.M.loaded_segments (0x345d8 : word) = Some W_34580.
Proof. vm_refl. Qed.
Lemma D_34580 : decode_any W_34580 = Some (ShiftImm ALU_SRL 10 19 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_34584 : bv 32 := 0x1a051863.
Lemma F_34584 : fetch_word Plain.M.loaded_segments (0x345dc : word) = Some W_34584.
Proof. vm_refl. Qed.
Lemma D_34584 : decode_any W_34584 = Some (Branch BC_NE 10 0 432, 4%Z).
Proof. vm_refl. Qed.

Definition W_34588 : bv 32 := 0x00199a93.
Lemma F_34588 : fetch_word Plain.M.loaded_segments (0x345e0 : word) = Some W_34588.
Proof. vm_refl. Qed.
Lemma D_34588 : decode_any W_34588 = Some (ShiftImm ALU_SLL 21 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3458c : bv 32 := 0x000a8513.
Lemma F_3458c : fetch_word Plain.M.loaded_segments (0x345e4 : word) = Some W_3458c.
Proof. vm_refl. Qed.
Lemma D_3458c : decode_any W_3458c = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_34590 : bv 32 := 0x7f4690ef.
Lemma F_34590 : fetch_word Plain.M.loaded_segments (0x345e8 : word) = Some W_34590.
Proof. vm_refl. Qed.
Lemma D_34590 : decode_any W_34590 = Some (Jal 1 432116, 4%Z).
Proof. vm_refl. Qed.

Definition W_34594 : bv 32 := 0x1c050063.
Lemma F_34594 : fetch_word Plain.M.loaded_segments (0x345ec : word) = Some W_34594.
Proof. vm_refl. Qed.
Lemma D_34594 : decode_any W_34594 = Some (Branch BC_EQ 10 0 448, 4%Z).
Proof. vm_refl. Qed.

Definition W_34598 : bv 32 := 0x00050493.
Lemma F_34598 : fetch_word Plain.M.loaded_segments (0x345f0 : word) = Some W_34598.
Proof. vm_refl. Qed.
Lemma D_34598 : decode_any W_34598 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3459c : bv 32 := 0x00098a63.
Lemma F_3459c : fetch_word Plain.M.loaded_segments (0x345f4 : word) = Some W_3459c.
Proof. vm_refl. Qed.
Lemma D_3459c : decode_any W_3459c = Some (Branch BC_EQ 19 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_345a0 : bv 32 := 0x00048513.
Lemma F_345a0 : fetch_word Plain.M.loaded_segments (0x345f8 : word) = Some W_345a0.
Proof. vm_refl. Qed.
Lemma D_345a0 : decode_any W_345a0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_345a4 : bv 32 := 0x000b8593.
Lemma F_345a4 : fetch_word Plain.M.loaded_segments (0x345fc : word) = Some W_345a4.
Proof. vm_refl. Qed.
Lemma D_345a4 : decode_any W_345a4 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_345a8 : bv 32 := 0x00098613.
Lemma F_345a8 : fetch_word Plain.M.loaded_segments (0x34600 : word) = Some W_345a8.
Proof. vm_refl. Qed.
Lemma D_345a8 : decode_any W_345a8 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_345ac : bv 32 := 0x689770ef.
Lemma F_345ac : fetch_word Plain.M.loaded_segments (0x34604 : word) = Some W_345ac.
Proof. vm_refl. Qed.
Lemma D_345ac : decode_any W_345ac = Some (Jal 1 491144, 4%Z).
Proof. vm_refl. Qed.

Definition W_345e0 : bv 32 := 0x000a0513.
Lemma F_345e0 : fetch_word Plain.M.loaded_segments (0x34638 : word) = Some W_345e0.
Proof. vm_refl. Qed.
Lemma D_345e0 : decode_any W_345e0 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_345e4 : bv 32 := 0x4f57c0ef.
Lemma F_345e4 : fetch_word Plain.M.loaded_segments (0x3463c : word) = Some W_345e4.
Proof. vm_refl. Qed.
Lemma D_345e4 : decode_any W_345e4 = Some (Jal 1 511220, 4%Z).
Proof. vm_refl. Qed.

Definition W_34660 : bv 32 := 0x000ac663.
Lemma F_34660 : fetch_word Plain.M.loaded_segments (0x346b8 : word) = Some W_34660.
Proof. vm_refl. Qed.
Lemma D_34660 : decode_any W_34660 = Some (Branch BC_LT 21 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_34664 : bv 32 := 0x00050413.
Lemma F_34664 : fetch_word Plain.M.loaded_segments (0x346bc : word) = Some W_34664.
Proof. vm_refl. Qed.
Lemma D_34664 : decode_any W_34664 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_34668 : bv 32 := 0x0780006f.
Lemma F_34668 : fetch_word Plain.M.loaded_segments (0x346c0 : word) = Some W_34668.
Proof. vm_refl. Qed.
Lemma D_34668 : decode_any W_34668 = Some (Jal 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_3466c : bv 32 := 0x148000ef.
Lemma F_3466c : fetch_word Plain.M.loaded_segments (0x346c4 : word) = Some W_3466c.
Proof. vm_refl. Qed.
Lemma D_3466c : decode_any W_3466c = Some (Jal 1 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_34670 : bv 32 := 0x0fb00593.
Lemma F_34670 : fetch_word Plain.M.loaded_segments (0x346c8 : word) = Some W_34670.
Proof. vm_refl. Qed.
Lemma D_34670 : decode_any W_34670 = Some (OpImm ALU_ADD 11 0 251, 4%Z).
Proof. vm_refl. Qed.

Definition W_34674 : bv 32 := 0x00050413.
Lemma F_34674 : fetch_word Plain.M.loaded_segments (0x346cc : word) = Some W_34674.
Proof. vm_refl. Qed.
Lemma D_34674 : decode_any W_34674 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_34678 : bv 32 := 0x06b56463.
Lemma F_34678 : fetch_word Plain.M.loaded_segments (0x346d0 : word) = Some W_34678.
Proof. vm_refl. Qed.
Lemma D_34678 : decode_any W_34678 = Some (Branch BC_LTU 10 11 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_347b4 : bv 32 := 0x00000513.
Lemma F_347b4 : fetch_word Plain.M.loaded_segments (0x3480c : word) = Some W_347b4.
Proof. vm_refl. Qed.
Lemma D_347b4 : decode_any W_347b4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_347b8 : bv 32 := 0x00008067.
Lemma F_347b8 : fetch_word Plain.M.loaded_segments (0x34810 : word) = Some W_347b8.
Proof. vm_refl. Qed.
Lemma D_347b8 : decode_any W_347b8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

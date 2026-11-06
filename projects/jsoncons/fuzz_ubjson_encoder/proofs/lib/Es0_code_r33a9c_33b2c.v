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

Definition W_3445c : bv 32 := 0xff010113.
Lemma F_3445c : fetch_word Plain.M.loaded_segments (0x344b4 : word) = Some W_3445c.
Proof. vm_refl. Qed.
Lemma D_3445c : decode_any W_3445c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_34460 : bv 32 := 0x00113423.
Lemma F_34460 : fetch_word Plain.M.loaded_segments (0x344b8 : word) = Some W_34460.
Proof. vm_refl. Qed.
Lemma D_34460 : decode_any W_34460 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_34464 : bv 32 := 0x00813023.
Lemma F_34464 : fetch_word Plain.M.loaded_segments (0x344bc : word) = Some W_34464.
Proof. vm_refl. Qed.
Lemma D_34464 : decode_any W_34464 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_34468 : bv 32 := 0x01010413.
Lemma F_34468 : fetch_word Plain.M.loaded_segments (0x344c0 : word) = Some W_34468.
Proof. vm_refl. Qed.
Lemma D_34468 : decode_any W_34468 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3446c : bv 32 := 0x00085517.
Lemma F_3446c : fetch_word Plain.M.loaded_segments (0x344c4 : word) = Some W_3446c.
Proof. vm_refl. Qed.
Lemma D_3446c : decode_any W_3446c = Some (Auipc 10 133, 4%Z).
Proof. vm_refl. Qed.

Definition W_34470 : bv 32 := 0x14450513.
Lemma F_34470 : fetch_word Plain.M.loaded_segments (0x344c8 : word) = Some W_34470.
Proof. vm_refl. Qed.
Lemma D_34470 : decode_any W_34470 = Some (OpImm ALU_ADD 10 10 324, 4%Z).
Proof. vm_refl. Qed.

Definition W_34474 : bv 32 := 0x00054503.
Lemma F_34474 : fetch_word Plain.M.loaded_segments (0x344cc : word) = Some W_34474.
Proof. vm_refl. Qed.
Lemma D_34474 : decode_any W_34474 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_34478 : bv 32 := 0x00157513.
Lemma F_34478 : fetch_word Plain.M.loaded_segments (0x344d0 : word) = Some W_34478.
Proof. vm_refl. Qed.
Lemma D_34478 : decode_any W_34478 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3447c : bv 32 := 0x00050663.
Lemma F_3447c : fetch_word Plain.M.loaded_segments (0x344d4 : word) = Some W_3447c.
Proof. vm_refl. Qed.
Lemma D_3447c : decode_any W_3447c = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_34480 : bv 32 := 0x0040006f.
Lemma F_34480 : fetch_word Plain.M.loaded_segments (0x344d8 : word) = Some W_34480.
Proof. vm_refl. Qed.
Lemma D_34480 : decode_any W_34480 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_34484 : bv 32 := 0x0580006f.
Lemma F_34484 : fetch_word Plain.M.loaded_segments (0x344dc : word) = Some W_34484.
Proof. vm_refl. Qed.
Lemma D_34484 : decode_any W_34484 = Some (Jal 0 88, 4%Z).
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

Definition W_344a4 : bv 32 := 0x0040006f.
Lemma F_344a4 : fetch_word Plain.M.loaded_segments (0x344fc : word) = Some W_344a4.
Proof. vm_refl. Qed.
Lemma D_344a4 : decode_any W_344a4 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_344a8 : bv 32 := 0x00085517.
Lemma F_344a8 : fetch_word Plain.M.loaded_segments (0x34500 : word) = Some W_344a8.
Proof. vm_refl. Qed.
Lemma D_344a8 : decode_any W_344a8 = Some (Auipc 10 133, 4%Z).
Proof. vm_refl. Qed.

Definition W_344ac : bv 32 := 0xdd050513.
Lemma F_344ac : fetch_word Plain.M.loaded_segments (0x34504 : word) = Some W_344ac.
Proof. vm_refl. Qed.
Lemma D_344ac : decode_any W_344ac = Some (OpImm ALU_ADD 10 10 3536, 4%Z).
Proof. vm_refl. Qed.

Definition W_344b0 : bv 32 := 0x00053503.
Lemma F_344b0 : fetch_word Plain.M.loaded_segments (0x34508 : word) = Some W_344b0.
Proof. vm_refl. Qed.
Lemma D_344b0 : decode_any W_344b0 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_344b4 : bv 32 := 0x708670ef.
Lemma F_344b4 : fetch_word Plain.M.loaded_segments (0x3450c : word) = Some W_344b4.
Proof. vm_refl. Qed.
Lemma D_344b4 : decode_any W_344b4 = Some (Jal 1 423688, 4%Z).
Proof. vm_refl. Qed.

Definition W_344b8 : bv 32 := 0x0040006f.
Lemma F_344b8 : fetch_word Plain.M.loaded_segments (0x34510 : word) = Some W_344b8.
Proof. vm_refl. Qed.
Lemma D_344b8 : decode_any W_344b8 = Some (Jal 0 4, 4%Z).
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

Definition W_344c8 : bv 32 := 0x0040006f.
Lemma F_344c8 : fetch_word Plain.M.loaded_segments (0x34520 : word) = Some W_344c8.
Proof. vm_refl. Qed.
Lemma D_344c8 : decode_any W_344c8 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_344cc : bv 32 := 0xffff1517.
Lemma F_344cc : fetch_word Plain.M.loaded_segments (0x34524 : word) = Some W_344cc.
Proof. vm_refl. Qed.
Lemma D_344cc : decode_any W_344cc = Some (Auipc 10 1048561, 4%Z).
Proof. vm_refl. Qed.

Definition W_344d0 : bv 32 := 0x21c50513.
Lemma F_344d0 : fetch_word Plain.M.loaded_segments (0x34528 : word) = Some W_344d0.
Proof. vm_refl. Qed.
Lemma D_344d0 : decode_any W_344d0 = Some (OpImm ALU_ADD 10 10 540, 4%Z).
Proof. vm_refl. Qed.

Definition W_344d4 : bv 32 := 0x000000ef.
Lemma F_344d4 : fetch_word Plain.M.loaded_segments (0x3452c : word) = Some W_344d4.
Proof. vm_refl. Qed.
Lemma D_344d4 : decode_any W_344d4 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_344d8 : bv 32 := 0x0040006f.
Lemma F_344d8 : fetch_word Plain.M.loaded_segments (0x34530 : word) = Some W_344d8.
Proof. vm_refl. Qed.
Lemma D_344d8 : decode_any W_344d8 = Some (Jal 0 4, 4%Z).
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

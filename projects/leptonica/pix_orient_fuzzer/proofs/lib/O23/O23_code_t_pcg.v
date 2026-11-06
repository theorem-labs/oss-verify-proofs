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
Definition W_635fc : bv 32 := 0x02050e63.
Lemma F_635fc : fetch_word Plain.M.loaded_segments (0x63654 : word) = Some W_635fc.
Proof. vm_refl. Qed.
Lemma D_635fc : decode_any W_635fc = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63600 : bv 32 := 0xfe010113.
Lemma F_63600 : fetch_word Plain.M.loaded_segments (0x63658 : word) = Some W_63600.
Proof. vm_refl. Qed.
Lemma D_63600 : decode_any W_63600 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63604 : bv 32 := 0x00113c23.
Lemma F_63604 : fetch_word Plain.M.loaded_segments (0x6365c : word) = Some W_63604.
Proof. vm_refl. Qed.
Lemma D_63604 : decode_any W_63604 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63608 : bv 32 := 0x00813823.
Lemma F_63608 : fetch_word Plain.M.loaded_segments (0x63660 : word) = Some W_63608.
Proof. vm_refl. Qed.
Lemma D_63608 : decode_any W_63608 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6360c : bv 32 := 0x00913423.
Lemma F_6360c : fetch_word Plain.M.loaded_segments (0x63664 : word) = Some W_6360c.
Proof. vm_refl. Qed.
Lemma D_6360c : decode_any W_6360c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63610 : bv 32 := 0x00058493.
Lemma F_63610 : fetch_word Plain.M.loaded_segments (0x63668 : word) = Some W_63610.
Proof. vm_refl. Qed.
Lemma D_63610 : decode_any W_63610 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63614 : bv 32 := 0x00050413.
Lemma F_63614 : fetch_word Plain.M.loaded_segments (0x6366c : word) = Some W_63614.
Proof. vm_refl. Qed.
Lemma D_63614 : decode_any W_63614 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63618 : bv 32 := 0x00053503.
Lemma F_63618 : fetch_word Plain.M.loaded_segments (0x63670 : word) = Some W_63618.
Proof. vm_refl. Qed.
Lemma D_63618 : decode_any W_63618 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6361c : bv 32 := 0x00050463.
Lemma F_6361c : fetch_word Plain.M.loaded_segments (0x63674 : word) = Some W_6361c.
Proof. vm_refl. Qed.
Lemma D_6361c : decode_any W_6361c = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63624 : bv 32 := 0x04048063.
Lemma F_63624 : fetch_word Plain.M.loaded_segments (0x6367c : word) = Some W_63624.
Proof. vm_refl. Qed.
Lemma D_63624 : decode_any W_63624 = Some (Branch BC_EQ 9 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63664 : bv 32 := 0x00000593.
Lemma F_63664 : fetch_word Plain.M.loaded_segments (0x636bc : word) = Some W_63664.
Proof. vm_refl. Qed.
Lemma D_63664 : decode_any W_63664 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63668 : bv 32 := 0x00000513.
Lemma F_63668 : fetch_word Plain.M.loaded_segments (0x636c0 : word) = Some W_63668.
Proof. vm_refl. Qed.
Lemma D_63668 : decode_any W_63668 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6366c : bv 32 := 0x00b43023.
Lemma F_6366c : fetch_word Plain.M.loaded_segments (0x636c4 : word) = Some W_6366c.
Proof. vm_refl. Qed.
Lemma D_6366c : decode_any W_6366c = Some (Store SZ8 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63670 : bv 32 := 0x01813083.
Lemma F_63670 : fetch_word Plain.M.loaded_segments (0x636c8 : word) = Some W_63670.
Proof. vm_refl. Qed.
Lemma D_63670 : decode_any W_63670 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63674 : bv 32 := 0x01013403.
Lemma F_63674 : fetch_word Plain.M.loaded_segments (0x636cc : word) = Some W_63674.
Proof. vm_refl. Qed.
Lemma D_63674 : decode_any W_63674 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63678 : bv 32 := 0x00813483.
Lemma F_63678 : fetch_word Plain.M.loaded_segments (0x636d0 : word) = Some W_63678.
Proof. vm_refl. Qed.
Lemma D_63678 : decode_any W_63678 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6367c : bv 32 := 0x02010113.
Lemma F_6367c : fetch_word Plain.M.loaded_segments (0x636d4 : word) = Some W_6367c.
Proof. vm_refl. Qed.
Lemma D_6367c : decode_any W_6367c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63680 : bv 32 := 0x00008067.
Lemma F_63680 : fetch_word Plain.M.loaded_segments (0x636d8 : word) = Some W_63680.
Proof. vm_refl. Qed.
Lemma D_63680 : decode_any W_63680 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf78 : bv 32 := 0xfd010113.
Lemma F_6cf78 : fetch_word Plain.M.loaded_segments (0x6cfd0 : word) = Some W_6cf78.
Proof. vm_refl. Qed.
Lemma D_6cf78 : decode_any W_6cf78 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf7c : bv 32 := 0x02113423.
Lemma F_6cf7c : fetch_word Plain.M.loaded_segments (0x6cfd4 : word) = Some W_6cf7c.
Proof. vm_refl. Qed.
Lemma D_6cf7c : decode_any W_6cf7c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf80 : bv 32 := 0x02813023.
Lemma F_6cf80 : fetch_word Plain.M.loaded_segments (0x6cfd8 : word) = Some W_6cf80.
Proof. vm_refl. Qed.
Lemma D_6cf80 : decode_any W_6cf80 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf84 : bv 32 := 0x00913c23.
Lemma F_6cf84 : fetch_word Plain.M.loaded_segments (0x6cfdc : word) = Some W_6cf84.
Proof. vm_refl. Qed.
Lemma D_6cf84 : decode_any W_6cf84 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf88 : bv 32 := 0x0e058063.
Lemma F_6cf88 : fetch_word Plain.M.loaded_segments (0x6cfe0 : word) = Some W_6cf88.
Proof. vm_refl. Qed.
Lemma D_6cf88 : decode_any W_6cf88 = Some (Branch BC_EQ 11 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf8c : bv 32 := 0x10050263.
Lemma F_6cf8c : fetch_word Plain.M.loaded_segments (0x6cfe4 : word) = Some W_6cf8c.
Proof. vm_refl. Qed.
Lemma D_6cf8c : decode_any W_6cf8c = Some (Branch BC_EQ 10 0 260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf90 : bv 32 := 0x0ca58863.
Lemma F_6cf90 : fetch_word Plain.M.loaded_segments (0x6cfe8 : word) = Some W_6cf90.
Proof. vm_refl. Qed.
Lemma D_6cf90 : decode_any W_6cf90 = Some (Branch BC_EQ 11 10 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf94 : bv 32 := 0x0085a603.
Lemma F_6cf94 : fetch_word Plain.M.loaded_segments (0x6cfec : word) = Some W_6cf94.
Proof. vm_refl. Qed.
Lemma D_6cf94 : decode_any W_6cf94 = Some (Load SZ4 true 12 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf98 : bv 32 := 0x00852683.
Lemma F_6cf98 : fetch_word Plain.M.loaded_segments (0x6cff0 : word) = Some W_6cf98.
Proof. vm_refl. Qed.
Lemma D_6cf98 : decode_any W_6cf98 = Some (Load SZ4 true 13 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf9c : bv 32 := 0x10d61e63.
Lemma F_6cf9c : fetch_word Plain.M.loaded_segments (0x6cff4 : word) = Some W_6cf9c.
Proof. vm_refl. Qed.
Lemma D_6cf9c : decode_any W_6cf9c = Some (Branch BC_NE 12 13 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cfa0 : bv 32 := 0x03053603.
Lemma F_6cfa0 : fetch_word Plain.M.loaded_segments (0x6cff8 : word) = Some W_6cfa0.
Proof. vm_refl. Qed.
Lemma D_6cfa0 : decode_any W_6cfa0 = Some (Load SZ8 true 12 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cfa4 : bv 32 := 0x00c13823.
Lemma F_6cfa4 : fetch_word Plain.M.loaded_segments (0x6cffc : word) = Some W_6cfa4.
Proof. vm_refl. Qed.
Lemma D_6cfa4 : decode_any W_6cfa4 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cfa8 : bv 32 := 0x02060063.
Lemma F_6cfa8 : fetch_word Plain.M.loaded_segments (0x6d000 : word) = Some W_6cfa8.
Proof. vm_refl. Qed.
Lemma D_6cfa8 : decode_any W_6cfa8 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cfac : bv 32 := 0x00050413.
Lemma F_6cfac : fetch_word Plain.M.loaded_segments (0x6d004 : word) = Some W_6cfac.
Proof. vm_refl. Qed.
Lemma D_6cfac : decode_any W_6cfac = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cfb0 : bv 32 := 0x01010513.
Lemma F_6cfb0 : fetch_word Plain.M.loaded_segments (0x6d008 : word) = Some W_6cfb0.
Proof. vm_refl. Qed.
Lemma D_6cfb0 : decode_any W_6cfb0 = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cfb4 : bv 32 := 0x00058493.
Lemma F_6cfb4 : fetch_word Plain.M.loaded_segments (0x6d00c : word) = Some W_6cfb4.
Proof. vm_refl. Qed.
Lemma D_6cfb4 : decode_any W_6cfb4 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cfb8 : bv 32 := 0x1cc040ef.
Lemma F_6cfb8 : fetch_word Plain.M.loaded_segments (0x6d010 : word) = Some W_6cfb8.
Proof. vm_refl. Qed.
Lemma D_6cfb8 : decode_any W_6cfb8 = Some (Jal 1 16844, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cfbc : bv 32 := 0x00048593.
Lemma F_6cfbc : fetch_word Plain.M.loaded_segments (0x6d014 : word) = Some W_6cfbc.
Proof. vm_refl. Qed.
Lemma D_6cfbc : decode_any W_6cfbc = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cfc0 : bv 32 := 0x00040513.
Lemma F_6cfc0 : fetch_word Plain.M.loaded_segments (0x6d018 : word) = Some W_6cfc0.
Proof. vm_refl. Qed.
Lemma D_6cfc0 : decode_any W_6cfc0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cfc4 : bv 32 := 0x02043823.
Lemma F_6cfc4 : fetch_word Plain.M.loaded_segments (0x6d01c : word) = Some W_6cfc4.
Proof. vm_refl. Qed.
Lemma D_6cfc4 : decode_any W_6cfc4 = Some (Store SZ8 8 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cfc8 : bv 32 := 0x0305b403.
Lemma F_6cfc8 : fetch_word Plain.M.loaded_segments (0x6d020 : word) = Some W_6cfc8.
Proof. vm_refl. Qed.
Lemma D_6cfc8 : decode_any W_6cfc8 = Some (Load SZ8 true 8 11 48, 4%Z).
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
Definition W_6d450 : bv 32 := 0x0044a503.
Lemma F_6d450 : fetch_word Plain.M.loaded_segments (0x6d4a8 : word) = Some W_6d450.
Proof. vm_refl. Qed.
Lemma D_6d450 : decode_any W_6d450 = Some (Load SZ4 true 10 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d454 : bv 32 := 0x0104a583.
Lemma F_6d454 : fetch_word Plain.M.loaded_segments (0x6d4ac : word) = Some W_6d454.
Proof. vm_refl. Qed.
Lemma D_6d454 : decode_any W_6d454 = Some (Load SZ4 true 11 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d458 : bv 32 := 0x02a58533.
Lemma F_6d458 : fetch_word Plain.M.loaded_segments (0x6d4b0 : word) = Some W_6d458.
Proof. vm_refl. Qed.
Lemma D_6d458 : decode_any W_6d458 = Some (Mul M_MUL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d45c : bv 32 := 0x0025191b.
Lemma F_6d45c : fetch_word Plain.M.loaded_segments (0x6d4b4 : word) = Some W_6d45c.
Proof. vm_refl. Qed.
Lemma D_6d45c : decode_any W_6d45c = Some (ShiftImm32 ALU_SLL 18 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d460 : bv 32 := 0x08040463.
Lemma F_6d460 : fetch_word Plain.M.loaded_segments (0x6d4b8 : word) = Some W_6d460.
Proof. vm_refl. Qed.
Lemma D_6d460 : decode_any W_6d460 = Some (Branch BC_EQ 8 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d464 : bv 32 := 0x00040513.
Lemma F_6d464 : fetch_word Plain.M.loaded_segments (0x6d4bc : word) = Some W_6d464.
Proof. vm_refl. Qed.
Lemma D_6d464 : decode_any W_6d464 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d468 : bv 32 := 0x00048593.
Lemma F_6d468 : fetch_word Plain.M.loaded_segments (0x6d4c0 : word) = Some W_6d468.
Proof. vm_refl. Qed.
Lemma D_6d468 : decode_any W_6d468 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d46c : bv 32 := 0x1dc000ef.
Lemma F_6d46c : fetch_word Plain.M.loaded_segments (0x6d4c4 : word) = Some W_6d46c.
Proof. vm_refl. Qed.
Lemma D_6d46c : decode_any W_6d46c = Some (Jal 1 476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d470 : bv 32 := 0x00100593.
Lemma F_6d470 : fetch_word Plain.M.loaded_segments (0x6d4c8 : word) = Some W_6d470.
Proof. vm_refl. Qed.
Lemma D_6d470 : decode_any W_6d470 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d474 : bv 32 := 0x0ab51263.
Lemma F_6d474 : fetch_word Plain.M.loaded_segments (0x6d4cc : word) = Some W_6d474.
Proof. vm_refl. Qed.
Lemma D_6d474 : decode_any W_6d474 = Some (Branch BC_NE 10 11 164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d518 : bv 32 := 0x00040513.
Lemma F_6d518 : fetch_word Plain.M.loaded_segments (0x6d570 : word) = Some W_6d518.
Proof. vm_refl. Qed.
Lemma D_6d518 : decode_any W_6d518 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d51c : bv 32 := 0x00048593.
Lemma F_6d51c : fetch_word Plain.M.loaded_segments (0x6d574 : word) = Some W_6d51c.
Proof. vm_refl. Qed.
Lemma D_6d51c : decode_any W_6d51c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d520 : bv 32 := 0xa59ff0ef.
Lemma F_6d520 : fetch_word Plain.M.loaded_segments (0x6d578 : word) = Some W_6d520.
Proof. vm_refl. Qed.
Lemma D_6d520 : decode_any W_6d520 = Some (Jal 1 2095704, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d524 : bv 32 := 0x00c4a503.
Lemma F_6d524 : fetch_word Plain.M.loaded_segments (0x6d57c : word) = Some W_6d524.
Proof. vm_refl. Qed.
Lemma D_6d524 : decode_any W_6d524 = Some (Load SZ4 true 10 9 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d528 : bv 32 := 0x06a05463.
Lemma F_6d528 : fetch_word Plain.M.loaded_segments (0x6d580 : word) = Some W_6d528.
Proof. vm_refl. Qed.
Lemma D_6d528 : decode_any W_6d528 = Some (Branch BC_GE 0 10 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d52c : bv 32 := 0x00a42623.
Lemma F_6d52c : fetch_word Plain.M.loaded_segments (0x6d584 : word) = Some W_6d52c.
Proof. vm_refl. Qed.
Lemma D_6d52c : decode_any W_6d52c = Some (Store SZ4 8 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d530 : bv 32 := 0x08c0006f.
Lemma F_6d530 : fetch_word Plain.M.loaded_segments (0x6d588 : word) = Some W_6d530.
Proof. vm_refl. Qed.
Lemma D_6d530 : decode_any W_6d530 = Some (Jal 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5bc : bv 32 := 0x0184b503.
Lemma F_6d5bc : fetch_word Plain.M.loaded_segments (0x6d614 : word) = Some W_6d5bc.
Proof. vm_refl. Qed.
Lemma D_6d5bc : decode_any W_6d5bc = Some (Load SZ8 true 10 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5c0 : bv 32 := 0x00a43c23.
Lemma F_6d5c0 : fetch_word Plain.M.loaded_segments (0x6d618 : word) = Some W_6d5c0.
Proof. vm_refl. Qed.
Lemma D_6d5c0 : decode_any W_6d5c0 = Some (Store SZ8 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5c4 : bv 32 := 0x0204a503.
Lemma F_6d5c4 : fetch_word Plain.M.loaded_segments (0x6d61c : word) = Some W_6d5c4.
Proof. vm_refl. Qed.
Lemma D_6d5c4 : decode_any W_6d5c4 = Some (Load SZ4 true 10 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5c8 : bv 32 := 0x0284b583.
Lemma F_6d5c8 : fetch_word Plain.M.loaded_segments (0x6d620 : word) = Some W_6d5c8.
Proof. vm_refl. Qed.
Lemma D_6d5c8 : decode_any W_6d5c8 = Some (Load SZ8 true 11 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5cc : bv 32 := 0x02a42023.
Lemma F_6d5cc : fetch_word Plain.M.loaded_segments (0x6d624 : word) = Some W_6d5cc.
Proof. vm_refl. Qed.
Lemma D_6d5cc : decode_any W_6d5cc = Some (Store SZ4 8 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5d0 : bv 32 := 0x02840513.
Lemma F_6d5d0 : fetch_word Plain.M.loaded_segments (0x6d628 : word) = Some W_6d5d0.
Proof. vm_refl. Qed.
Lemma D_6d5d0 : decode_any W_6d5d0 = Some (OpImm ALU_ADD 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5d4 : bv 32 := 0x828f60ef.
Lemma F_6d5d4 : fetch_word Plain.M.loaded_segments (0x6d62c : word) = Some W_6d5d4.
Proof. vm_refl. Qed.
Lemma D_6d5d4 : decode_any W_6d5d4 = Some (Jal 1 2056232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5d8 : bv 32 := 0x03843503.
Lemma F_6d5d8 : fetch_word Plain.M.loaded_segments (0x6d630 : word) = Some W_6d5d8.
Proof. vm_refl. Qed.
Lemma D_6d5d8 : decode_any W_6d5d8 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5dc : bv 32 := 0x0384b583.
Lemma F_6d5dc : fetch_word Plain.M.loaded_segments (0x6d634 : word) = Some W_6d5dc.
Proof. vm_refl. Qed.
Lemma D_6d5dc : decode_any W_6d5dc = Some (Load SZ8 true 11 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5e0 : bv 32 := 0x00090613.
Lemma F_6d5e0 : fetch_word Plain.M.loaded_segments (0x6d638 : word) = Some W_6d5e0.
Proof. vm_refl. Qed.
Lemma D_6d5e0 : decode_any W_6d5e0 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5e4 : bv 32 := 0x6749c0ef.
Lemma F_6d5e4 : fetch_word Plain.M.loaded_segments (0x6d63c : word) = Some W_6d5e4.
Proof. vm_refl. Qed.
Lemma D_6d5e4 : decode_any W_6d5e4 = Some (Jal 1 640628, 4%Z).
Proof. vm_refl. Qed.


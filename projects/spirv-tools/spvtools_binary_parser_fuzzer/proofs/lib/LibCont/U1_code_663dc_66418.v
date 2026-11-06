(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_663dc : bv 32 := 0xff010113.
Lemma F_663dc : fetch_word Ubsan.M.loaded_segments (0x6641c : word) = Some W_663dc.
Proof. vm_refl. Qed.
Lemma D_663dc : decode_any W_663dc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_663e0 : bv 32 := 0x00113423.
Lemma F_663e0 : fetch_word Ubsan.M.loaded_segments (0x66420 : word) = Some W_663e0.
Proof. vm_refl. Qed.
Lemma D_663e0 : decode_any W_663e0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_663e4 : bv 32 := 0x00813023.
Lemma F_663e4 : fetch_word Ubsan.M.loaded_segments (0x66424 : word) = Some W_663e4.
Proof. vm_refl. Qed.
Lemma D_663e4 : decode_any W_663e4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_663e8 : bv 32 := 0x03e5d513.
Lemma F_663e8 : fetch_word Ubsan.M.loaded_segments (0x66428 : word) = Some W_663e8.
Proof. vm_refl. Qed.
Lemma D_663e8 : decode_any W_663e8 = Some (ShiftImm ALU_SRL 10 11 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_663ec : bv 32 := 0x02051263.
Lemma F_663ec : fetch_word Ubsan.M.loaded_segments (0x6642c : word) = Some W_663ec.
Proof. vm_refl. Qed.
Lemma D_663ec : decode_any W_663ec = Some (Branch BC_NE 10 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_663f0 : bv 32 := 0x00058413.
Lemma F_663f0 : fetch_word Ubsan.M.loaded_segments (0x66430 : word) = Some W_663f0.
Proof. vm_refl. Qed.
Lemma D_663f0 : decode_any W_663f0 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_663f4 : bv 32 := 0x00259513.
Lemma F_663f4 : fetch_word Ubsan.M.loaded_segments (0x66434 : word) = Some W_663f4.
Proof. vm_refl. Qed.
Lemma D_663f4 : decode_any W_663f4 = Some (ShiftImm ALU_SLL 10 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_663f8 : bv 32 := 0x6fc810ef.
Lemma F_663f8 : fetch_word Ubsan.M.loaded_segments (0x66438 : word) = Some W_663f8.
Proof. vm_refl. Qed.
Lemma D_663f8 : decode_any W_663f8 = Some (Jal 1 530172, 4%Z).
Proof. vm_refl. Qed.

Definition W_663fc : bv 32 := 0x00040593.
Lemma F_663fc : fetch_word Ubsan.M.loaded_segments (0x6643c : word) = Some W_663fc.
Proof. vm_refl. Qed.
Lemma D_663fc : decode_any W_663fc = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66400 : bv 32 := 0x00813083.
Lemma F_66400 : fetch_word Ubsan.M.loaded_segments (0x66440 : word) = Some W_66400.
Proof. vm_refl. Qed.
Lemma D_66400 : decode_any W_66400 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_66404 : bv 32 := 0x00013403.
Lemma F_66404 : fetch_word Ubsan.M.loaded_segments (0x66444 : word) = Some W_66404.
Proof. vm_refl. Qed.
Lemma D_66404 : decode_any W_66404 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66408 : bv 32 := 0x01010113.
Lemma F_66408 : fetch_word Ubsan.M.loaded_segments (0x66448 : word) = Some W_66408.
Proof. vm_refl. Qed.
Lemma D_66408 : decode_any W_66408 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6640c : bv 32 := 0x00008067.
Lemma F_6640c : fetch_word Ubsan.M.loaded_segments (0x6644c : word) = Some W_6640c.
Proof. vm_refl. Qed.
Lemma D_6640c : decode_any W_6640c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

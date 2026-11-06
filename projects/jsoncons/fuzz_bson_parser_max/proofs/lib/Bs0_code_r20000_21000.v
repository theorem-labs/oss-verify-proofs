(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_33e8c : bv 32 := 0x00050663.
Lemma F_33e8c : fetch_word Plain.M.loaded_segments (0x33ee4 : word) = Some W_33e8c.
Proof. vm_refl. Qed.
Lemma D_33e8c : decode_any W_33e8c = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e98 : bv 32 := 0x00083517.
Lemma F_33e98 : fetch_word Plain.M.loaded_segments (0x33ef0 : word) = Some W_33e98.
Proof. vm_refl. Qed.
Lemma D_33e98 : decode_any W_33e98 = Some (Auipc 10 131, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33e9c : bv 32 := 0x07850593.
Lemma F_33e9c : fetch_word Plain.M.loaded_segments (0x33ef4 : word) = Some W_33e9c.
Proof. vm_refl. Qed.
Lemma D_33e9c : decode_any W_33e9c = Some (OpImm ALU_ADD 11 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ea0 : bv 32 := 0x00100513.
Lemma F_33ea0 : fetch_word Plain.M.loaded_segments (0x33ef8 : word) = Some W_33ea0.
Proof. vm_refl. Qed.
Lemma D_33ea0 : decode_any W_33ea0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ea4 : bv 32 := 0x00a58023.
Lemma F_33ea4 : fetch_word Plain.M.loaded_segments (0x33efc : word) = Some W_33ea4.
Proof. vm_refl. Qed.
Lemma D_33ea4 : decode_any W_33ea4 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ea8 : bv 32 := 0x00082517.
Lemma F_33ea8 : fetch_word Plain.M.loaded_segments (0x33f00 : word) = Some W_33ea8.
Proof. vm_refl. Qed.
Lemma D_33ea8 : decode_any W_33ea8 = Some (Auipc 10 130, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33eac : bv 32 := 0xb9853503.
Lemma F_33eac : fetch_word Plain.M.loaded_segments (0x33f04 : word) = Some W_33eac.
Proof. vm_refl. Qed.
Lemma D_33eac : decode_any W_33eac = Some (Load SZ8 true 10 10 2968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33eb0 : bv 32 := 0x00050e63.
Lemma F_33eb0 : fetch_word Plain.M.loaded_segments (0x33f08 : word) = Some W_33eb0.
Proof. vm_refl. Qed.
Lemma D_33eb0 : decode_any W_33eb0 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ecc : bv 32 := 0x00082517.
Lemma F_33ecc : fetch_word Plain.M.loaded_segments (0x33f24 : word) = Some W_33ecc.
Proof. vm_refl. Qed.
Lemma D_33ecc : decode_any W_33ecc = Some (Auipc 10 130, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ed0 : bv 32 := 0xb7c53503.
Lemma F_33ed0 : fetch_word Plain.M.loaded_segments (0x33f28 : word) = Some W_33ed0.
Proof. vm_refl. Qed.
Lemma D_33ed0 : decode_any W_33ed0 = Some (Load SZ8 true 10 10 2940, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ed4 : bv 32 := 0x00050c63.
Lemma F_33ed4 : fetch_word Plain.M.loaded_segments (0x33f2c : word) = Some W_33ed4.
Proof. vm_refl. Qed.
Lemma D_33ed4 : decode_any W_33ed4 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33eec : bv 32 := 0x00813083.
Lemma F_33eec : fetch_word Plain.M.loaded_segments (0x33f44 : word) = Some W_33eec.
Proof. vm_refl. Qed.
Lemma D_33eec : decode_any W_33eec = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ef0 : bv 32 := 0x00013403.
Lemma F_33ef0 : fetch_word Plain.M.loaded_segments (0x33f48 : word) = Some W_33ef0.
Proof. vm_refl. Qed.
Lemma D_33ef0 : decode_any W_33ef0 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ef4 : bv 32 := 0x01010113.
Lemma F_33ef4 : fetch_word Plain.M.loaded_segments (0x33f4c : word) = Some W_33ef4.
Proof. vm_refl. Qed.
Lemma D_33ef4 : decode_any W_33ef4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ef8 : bv 32 := 0x00008067.
Lemma F_33ef8 : fetch_word Plain.M.loaded_segments (0x33f50 : word) = Some W_33ef8.
Proof. vm_refl. Qed.
Lemma D_33ef8 : decode_any W_33ef8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33f50 : bv 32 := 0x24050a63.
Lemma F_33f50 : fetch_word Plain.M.loaded_segments (0x33fa8 : word) = Some W_33f50.
Proof. vm_refl. Qed.
Lemma D_33f50 : decode_any W_33f50 = Some (Branch BC_EQ 10 0 596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33f90 : bv 32 := 0x01a9d513.
Lemma F_33f90 : fetch_word Plain.M.loaded_segments (0x33fe8 : word) = Some W_33f90.
Proof. vm_refl. Qed.
Lemma D_33f90 : decode_any W_33f90 = Some (ShiftImm ALU_SRL 10 19 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33f94 : bv 32 := 0x1a051863.
Lemma F_33f94 : fetch_word Plain.M.loaded_segments (0x33fec : word) = Some W_33f94.
Proof. vm_refl. Qed.
Lemma D_33f94 : decode_any W_33f94 = Some (Branch BC_NE 10 0 432, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33f98 : bv 32 := 0x00199a93.
Lemma F_33f98 : fetch_word Plain.M.loaded_segments (0x33ff0 : word) = Some W_33f98.
Proof. vm_refl. Qed.
Lemma D_33f98 : decode_any W_33f98 = Some (ShiftImm ALU_SLL 21 19 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33f9c : bv 32 := 0x000a8513.
Lemma F_33f9c : fetch_word Plain.M.loaded_segments (0x33ff4 : word) = Some W_33f9c.
Proof. vm_refl. Qed.
Lemma D_33f9c : decode_any W_33f9c = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33fa0 : bv 32 := 0x7f4670ef.
Lemma F_33fa0 : fetch_word Plain.M.loaded_segments (0x33ff8 : word) = Some W_33fa0.
Proof. vm_refl. Qed.
Lemma D_33fa0 : decode_any W_33fa0 = Some (Jal 1 423924, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33fa4 : bv 32 := 0x1c050063.
Lemma F_33fa4 : fetch_word Plain.M.loaded_segments (0x33ffc : word) = Some W_33fa4.
Proof. vm_refl. Qed.
Lemma D_33fa4 : decode_any W_33fa4 = Some (Branch BC_EQ 10 0 448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33fa8 : bv 32 := 0x00050493.
Lemma F_33fa8 : fetch_word Plain.M.loaded_segments (0x34000 : word) = Some W_33fa8.
Proof. vm_refl. Qed.
Lemma D_33fa8 : decode_any W_33fa8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33fac : bv 32 := 0x00098a63.
Lemma F_33fac : fetch_word Plain.M.loaded_segments (0x34004 : word) = Some W_33fac.
Proof. vm_refl. Qed.
Lemma D_33fac : decode_any W_33fac = Some (Branch BC_EQ 19 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33fb0 : bv 32 := 0x00048513.
Lemma F_33fb0 : fetch_word Plain.M.loaded_segments (0x34008 : word) = Some W_33fb0.
Proof. vm_refl. Qed.
Lemma D_33fb0 : decode_any W_33fb0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33fb4 : bv 32 := 0x000b8593.
Lemma F_33fb4 : fetch_word Plain.M.loaded_segments (0x3400c : word) = Some W_33fb4.
Proof. vm_refl. Qed.
Lemma D_33fb4 : decode_any W_33fb4 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33fb8 : bv 32 := 0x00098613.
Lemma F_33fb8 : fetch_word Plain.M.loaded_segments (0x34010 : word) = Some W_33fb8.
Proof. vm_refl. Qed.
Lemma D_33fb8 : decode_any W_33fb8 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33fbc : bv 32 := 0x685750ef.
Lemma F_33fbc : fetch_word Plain.M.loaded_segments (0x34014 : word) = Some W_33fbc.
Proof. vm_refl. Qed.
Lemma D_33fbc : decode_any W_33fbc = Some (Jal 1 482948, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ff0 : bv 32 := 0x000a0513.
Lemma F_33ff0 : fetch_word Plain.M.loaded_segments (0x34048 : word) = Some W_33ff0.
Proof. vm_refl. Qed.
Lemma D_33ff0 : decode_any W_33ff0 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_33ff4 : bv 32 := 0x4f17a0ef.
Lemma F_33ff4 : fetch_word Plain.M.loaded_segments (0x3404c : word) = Some W_33ff4.
Proof. vm_refl. Qed.
Lemma D_33ff4 : decode_any W_33ff4 = Some (Jal 1 503024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_34070 : bv 32 := 0x000ac663.
Lemma F_34070 : fetch_word Plain.M.loaded_segments (0x340c8 : word) = Some W_34070.
Proof. vm_refl. Qed.
Lemma D_34070 : decode_any W_34070 = Some (Branch BC_LT 21 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_34074 : bv 32 := 0x00050413.
Lemma F_34074 : fetch_word Plain.M.loaded_segments (0x340cc : word) = Some W_34074.
Proof. vm_refl. Qed.
Lemma D_34074 : decode_any W_34074 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_34078 : bv 32 := 0x0780006f.
Lemma F_34078 : fetch_word Plain.M.loaded_segments (0x340d0 : word) = Some W_34078.
Proof. vm_refl. Qed.
Lemma D_34078 : decode_any W_34078 = Some (Jal 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3407c : bv 32 := 0x148000ef.
Lemma F_3407c : fetch_word Plain.M.loaded_segments (0x340d4 : word) = Some W_3407c.
Proof. vm_refl. Qed.
Lemma D_3407c : decode_any W_3407c = Some (Jal 1 328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_34080 : bv 32 := 0x0fb00593.
Lemma F_34080 : fetch_word Plain.M.loaded_segments (0x340d8 : word) = Some W_34080.
Proof. vm_refl. Qed.
Lemma D_34080 : decode_any W_34080 = Some (OpImm ALU_ADD 11 0 251, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_34084 : bv 32 := 0x00050413.
Lemma F_34084 : fetch_word Plain.M.loaded_segments (0x340dc : word) = Some W_34084.
Proof. vm_refl. Qed.
Lemma D_34084 : decode_any W_34084 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_34088 : bv 32 := 0x06b56463.
Lemma F_34088 : fetch_word Plain.M.loaded_segments (0x340e0 : word) = Some W_34088.
Proof. vm_refl. Qed.
Lemma D_34088 : decode_any W_34088 = Some (Branch BC_LTU 10 11 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_341c4 : bv 32 := 0x00000513.
Lemma F_341c4 : fetch_word Plain.M.loaded_segments (0x3421c : word) = Some W_341c4.
Proof. vm_refl. Qed.
Lemma D_341c4 : decode_any W_341c4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_341c8 : bv 32 := 0x00008067.
Lemma F_341c8 : fetch_word Plain.M.loaded_segments (0x34220 : word) = Some W_341c8.
Proof. vm_refl. Qed.
Lemma D_341c8 : decode_any W_341c8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

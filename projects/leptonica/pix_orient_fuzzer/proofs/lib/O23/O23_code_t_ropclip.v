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
Definition W_79f58 : bv 32 := 0xf9010113.
Lemma F_79f58 : fetch_word Plain.M.loaded_segments (0x79fb0 : word) = Some W_79f58.
Proof. vm_refl. Qed.
Lemma D_79f58 : decode_any W_79f58 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f5c : bv 32 := 0x06113423.
Lemma F_79f5c : fetch_word Plain.M.loaded_segments (0x79fb4 : word) = Some W_79f5c.
Proof. vm_refl. Qed.
Lemma D_79f5c : decode_any W_79f5c = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f60 : bv 32 := 0x06813023.
Lemma F_79f60 : fetch_word Plain.M.loaded_segments (0x79fb8 : word) = Some W_79f60.
Proof. vm_refl. Qed.
Lemma D_79f60 : decode_any W_79f60 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f64 : bv 32 := 0x04913c23.
Lemma F_79f64 : fetch_word Plain.M.loaded_segments (0x79fbc : word) = Some W_79f64.
Proof. vm_refl. Qed.
Lemma D_79f64 : decode_any W_79f64 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f68 : bv 32 := 0x05213823.
Lemma F_79f68 : fetch_word Plain.M.loaded_segments (0x79fc0 : word) = Some W_79f68.
Proof. vm_refl. Qed.
Lemma D_79f68 : decode_any W_79f68 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f6c : bv 32 := 0x05313423.
Lemma F_79f6c : fetch_word Plain.M.loaded_segments (0x79fc4 : word) = Some W_79f6c.
Proof. vm_refl. Qed.
Lemma D_79f6c : decode_any W_79f6c = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f70 : bv 32 := 0x05413023.
Lemma F_79f70 : fetch_word Plain.M.loaded_segments (0x79fc8 : word) = Some W_79f70.
Proof. vm_refl. Qed.
Lemma D_79f70 : decode_any W_79f70 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f74 : bv 32 := 0x03513c23.
Lemma F_79f74 : fetch_word Plain.M.loaded_segments (0x79fcc : word) = Some W_79f74.
Proof. vm_refl. Qed.
Lemma D_79f74 : decode_any W_79f74 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f78 : bv 32 := 0x03613823.
Lemma F_79f78 : fetch_word Plain.M.loaded_segments (0x79fd0 : word) = Some W_79f78.
Proof. vm_refl. Qed.
Lemma D_79f78 : decode_any W_79f78 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f7c : bv 32 := 0x03713423.
Lemma F_79f7c : fetch_word Plain.M.loaded_segments (0x79fd4 : word) = Some W_79f7c.
Proof. vm_refl. Qed.
Lemma D_79f7c : decode_any W_79f7c = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f80 : bv 32 := 0x03813023.
Lemma F_79f80 : fetch_word Plain.M.loaded_segments (0x79fd8 : word) = Some W_79f80.
Proof. vm_refl. Qed.
Lemma D_79f80 : decode_any W_79f80 = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f84 : bv 32 := 0x01913c23.
Lemma F_79f84 : fetch_word Plain.M.loaded_segments (0x79fdc : word) = Some W_79f84.
Proof. vm_refl. Qed.
Lemma D_79f84 : decode_any W_79f84 = Some (Store SZ8 2 25 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f88 : bv 32 := 0x01a13823.
Lemma F_79f88 : fetch_word Plain.M.loaded_segments (0x79fe0 : word) = Some W_79f88.
Proof. vm_refl. Qed.
Lemma D_79f88 : decode_any W_79f88 = Some (Store SZ8 2 26 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f8c : bv 32 := 0x01b13423.
Lemma F_79f8c : fetch_word Plain.M.loaded_segments (0x79fe4 : word) = Some W_79f8c.
Proof. vm_refl. Qed.
Lemma D_79f8c : decode_any W_79f8c = Some (Store SZ8 2 27 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f90 : bv 32 := 0x0a013383.
Lemma F_79f90 : fetch_word Plain.M.loaded_segments (0x79fe8 : word) = Some W_79f90.
Proof. vm_refl. Qed.
Lemma D_79f90 : decode_any W_79f90 = Some (Load SZ8 true 7 2 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f94 : bv 32 := 0x08813303.
Lemma F_79f94 : fetch_word Plain.M.loaded_segments (0x79fec : word) = Some W_79f94.
Proof. vm_refl. Qed.
Lemma D_79f94 : decode_any W_79f94 = Some (Load SZ8 true 6 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f98 : bv 32 := 0x00100e13.
Lemma F_79f98 : fetch_word Plain.M.loaded_segments (0x79ff0 : word) = Some W_79f98.
Proof. vm_refl. Qed.
Lemma D_79f98 : decode_any W_79f98 = Some (OpImm ALU_ADD 28 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79f9c : bv 32 := 0x00050293.
Lemma F_79f9c : fetch_word Plain.M.loaded_segments (0x79ff4 : word) = Some W_79f9c.
Proof. vm_refl. Qed.
Lemma D_79f9c : decode_any W_79f9c = Some (OpImm ALU_ADD 5 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fa0 : bv 32 := 0x01c68c63.
Lemma F_79fa0 : fetch_word Plain.M.loaded_segments (0x79ff8 : word) = Some W_79fa0.
Proof. vm_refl. Qed.
Lemma D_79fa0 : decode_any W_79fa0 = Some (Branch BC_EQ 13 28 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fb8 : bv 32 := 0x43f7d513.
Lemma F_79fb8 : fetch_word Plain.M.loaded_segments (0x7a010 : word) = Some W_79fb8.
Proof. vm_refl. Qed.
Lemma D_79fb8 : decode_any W_79fb8 = Some (ShiftImm ALU_SRA 10 15 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fbc : bv 32 := 0x00f026b3.
Lemma F_79fbc : fetch_word Plain.M.loaded_segments (0x7a014 : word) = Some W_79fbc.
Proof. vm_refl. Qed.
Lemma D_79fbc : decode_any W_79fbc = Some (Op ALU_SLT 13 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fc0 : bv 32 := 0x00f57533.
Lemma F_79fc0 : fetch_word Plain.M.loaded_segments (0x7a018 : word) = Some W_79fc0.
Proof. vm_refl. Qed.
Lemma D_79fc0 : decode_any W_79fc0 = Some (Op ALU_AND 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fc4 : bv 32 := 0x40d006bb.
Lemma F_79fc4 : fetch_word Plain.M.loaded_segments (0x7a01c : word) = Some W_79fc4.
Proof. vm_refl. Qed.
Lemma D_79fc4 : decode_any W_79fc4 = Some (Op32 ALU_SUB 13 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fc8 : bv 32 := 0x40a383bb.
Lemma F_79fc8 : fetch_word Plain.M.loaded_segments (0x7a020 : word) = Some W_79fc8.
Proof. vm_refl. Qed.
Lemma D_79fc8 : decode_any W_79fc8 = Some (Op32 ALU_SUB 7 7 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fcc : bv 32 := 0x01150533.
Lemma F_79fcc : fetch_word Plain.M.loaded_segments (0x7a024 : word) = Some W_79fcc.
Proof. vm_refl. Qed.
Lemma D_79fcc : decode_any W_79fcc = Some (Op ALU_ADD 10 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fd0 : bv 32 := 0x00f6f6b3.
Lemma F_79fd0 : fetch_word Plain.M.loaded_segments (0x7a028 : word) = Some W_79fd0.
Proof. vm_refl. Qed.
Lemma D_79fd0 : decode_any W_79fd0 = Some (Op ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fd4 : bv 32 := 0x007027b3.
Lemma F_79fd4 : fetch_word Plain.M.loaded_segments (0x7a02c : word) = Some W_79fd4.
Proof. vm_refl. Qed.
Lemma D_79fd4 : decode_any W_79fd4 = Some (Op ALU_SLT 15 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fd8 : bv 32 := 0x43f3d893.
Lemma F_79fd8 : fetch_word Plain.M.loaded_segments (0x7a030 : word) = Some W_79fd8.
Proof. vm_refl. Qed.
Lemma D_79fd8 : decode_any W_79fd8 = Some (ShiftImm ALU_SRA 17 7 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fdc : bv 32 := 0x40f007b3.
Lemma F_79fdc : fetch_word Plain.M.loaded_segments (0x7a034 : word) = Some W_79fdc.
Proof. vm_refl. Qed.
Lemma D_79fdc : decode_any W_79fdc = Some (Op ALU_SUB 15 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fe0 : bv 32 := 0x0078f8b3.
Lemma F_79fe0 : fetch_word Plain.M.loaded_segments (0x7a038 : word) = Some W_79fe0.
Proof. vm_refl. Qed.
Lemma D_79fe0 : decode_any W_79fe0 = Some (Op ALU_AND 17 17 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fe4 : bv 32 := 0x0077fd33.
Lemma F_79fe4 : fetch_word Plain.M.loaded_segments (0x7a03c : word) = Some W_79fe4.
Proof. vm_refl. Qed.
Lemma D_79fe4 : decode_any W_79fe4 = Some (Op ALU_AND 26 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fe8 : bv 32 := 0x01150533.
Lemma F_79fe8 : fetch_word Plain.M.loaded_segments (0x7a040 : word) = Some W_79fe8.
Proof. vm_refl. Qed.
Lemma D_79fe8 : decode_any W_79fe8 = Some (Op ALU_ADD 10 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79fec : bv 32 := 0x411689bb.
Lemma F_79fec : fetch_word Plain.M.loaded_segments (0x7a044 : word) = Some W_79fec.
Proof. vm_refl. Qed.
Lemma D_79fec : decode_any W_79fec = Some (Op32 ALU_SUB 19 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ff0 : bv 32 := 0x40b505bb.
Lemma F_79ff0 : fetch_word Plain.M.loaded_segments (0x7a048 : word) = Some W_79ff0.
Proof. vm_refl. Qed.
Lemma D_79ff0 : decode_any W_79ff0 = Some (Op32 ALU_SUB 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ff4 : bv 32 := 0x013585bb.
Lemma F_79ff4 : fetch_word Plain.M.loaded_segments (0x7a04c : word) = Some W_79ff4.
Proof. vm_refl. Qed.
Lemma D_79ff4 : decode_any W_79ff4 = Some (Op32 ALU_ADD 11 11 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ff8 : bv 32 := 0x00b026b3.
Lemma F_79ff8 : fetch_word Plain.M.loaded_segments (0x7a050 : word) = Some W_79ff8.
Proof. vm_refl. Qed.
Lemma D_79ff8 : decode_any W_79ff8 = Some (Op ALU_SLT 13 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79ffc : bv 32 := 0x40d006bb.
Lemma F_79ffc : fetch_word Plain.M.loaded_segments (0x7a054 : word) = Some W_79ffc.
Proof. vm_refl. Qed.
Lemma D_79ffc : decode_any W_79ffc = Some (Op32 ALU_SUB 13 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a000 : bv 32 := 0x00b6f5b3.
Lemma F_7a000 : fetch_word Plain.M.loaded_segments (0x7a058 : word) = Some W_7a000.
Proof. vm_refl. Qed.
Lemma D_7a000 : decode_any W_7a000 = Some (Op ALU_AND 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a004 : bv 32 := 0x40b5053b.
Lemma F_7a004 : fetch_word Plain.M.loaded_segments (0x7a05c : word) = Some W_7a004.
Proof. vm_refl. Qed.
Lemma D_7a004 : decode_any W_7a004 = Some (Op32 ALU_SUB 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a008 : bv 32 := 0x406d05bb.
Lemma F_7a008 : fetch_word Plain.M.loaded_segments (0x7a060 : word) = Some W_7a008.
Proof. vm_refl. Qed.
Lemma D_7a008 : decode_any W_7a008 = Some (Op32 ALU_SUB 11 26 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a00c : bv 32 := 0x00a585bb.
Lemma F_7a00c : fetch_word Plain.M.loaded_segments (0x7a064 : word) = Some W_7a00c.
Proof. vm_refl. Qed.
Lemma D_7a00c : decode_any W_7a00c = Some (Op32 ALU_ADD 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a010 : bv 32 := 0x00b026b3.
Lemma F_7a010 : fetch_word Plain.M.loaded_segments (0x7a068 : word) = Some W_7a010.
Proof. vm_refl. Qed.
Lemma D_7a010 : decode_any W_7a010 = Some (Op ALU_SLT 13 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a014 : bv 32 := 0x40d006bb.
Lemma F_7a014 : fetch_word Plain.M.loaded_segments (0x7a06c : word) = Some W_7a014.
Proof. vm_refl. Qed.
Lemma D_7a014 : decode_any W_7a014 = Some (Op32 ALU_SUB 13 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a018 : bv 32 := 0x00b6f5b3.
Lemma F_7a018 : fetch_word Plain.M.loaded_segments (0x7a070 : word) = Some W_7a018.
Proof. vm_refl. Qed.
Lemma D_7a018 : decode_any W_7a018 = Some (Op ALU_AND 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a01c : bv 32 := 0x40b5033b.
Lemma F_7a01c : fetch_word Plain.M.loaded_segments (0x7a074 : word) = Some W_7a01c.
Proof. vm_refl. Qed.
Lemma D_7a01c : decode_any W_7a01c = Some (Op32 ALU_SUB 6 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a020 : bv 32 := 0x00604463.
Lemma F_7a020 : fetch_word Plain.M.loaded_segments (0x7a078 : word) = Some W_7a020.
Proof. vm_refl. Qed.
Lemma D_7a020 : decode_any W_7a020 = Some (Branch BC_LT 0 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a024 : bv 32 := 0x6cd0106f.
Lemma F_7a024 : fetch_word Plain.M.loaded_segments (0x7a07c : word) = Some W_7a024.
Proof. vm_refl. Qed.
Lemma D_7a024 : decode_any W_7a024 = Some (Jal 0 7884, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a028 : bv 32 := 0x0a813503.
Lemma F_7a028 : fetch_word Plain.M.loaded_segments (0x7a080 : word) = Some W_7a028.
Proof. vm_refl. Qed.
Lemma D_7a028 : decode_any W_7a028 = Some (Load SZ8 true 10 2 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a02c : bv 32 := 0x09013583.
Lemma F_7a02c : fetch_word Plain.M.loaded_segments (0x7a084 : word) = Some W_7a02c.
Proof. vm_refl. Qed.
Lemma D_7a02c : decode_any W_7a02c = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a030 : bv 32 := 0x07013683.
Lemma F_7a030 : fetch_word Plain.M.loaded_segments (0x7a088 : word) = Some W_7a030.
Proof. vm_refl. Qed.
Lemma D_7a030 : decode_any W_7a030 = Some (Load SZ8 true 13 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a034 : bv 32 := 0x43f85793.
Lemma F_7a034 : fetch_word Plain.M.loaded_segments (0x7a08c : word) = Some W_7a034.
Proof. vm_refl. Qed.
Lemma D_7a034 : decode_any W_7a034 = Some (ShiftImm ALU_SRA 15 16 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a038 : bv 32 := 0x010028b3.
Lemma F_7a038 : fetch_word Plain.M.loaded_segments (0x7a090 : word) = Some W_7a038.
Proof. vm_refl. Qed.
Lemma D_7a038 : decode_any W_7a038 = Some (Op ALU_SLT 17 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a03c : bv 32 := 0x0107f7b3.
Lemma F_7a03c : fetch_word Plain.M.loaded_segments (0x7a094 : word) = Some W_7a03c.
Proof. vm_refl. Qed.
Lemma D_7a03c : decode_any W_7a03c = Some (Op ALU_AND 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a040 : bv 32 := 0x411008bb.
Lemma F_7a040 : fetch_word Plain.M.loaded_segments (0x7a098 : word) = Some W_7a040.
Proof. vm_refl. Qed.
Lemma D_7a040 : decode_any W_7a040 = Some (Op32 ALU_SUB 17 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a044 : bv 32 := 0x0108f833.
Lemma F_7a044 : fetch_word Plain.M.loaded_segments (0x7a09c : word) = Some W_7a044.
Proof. vm_refl. Qed.
Lemma D_7a044 : decode_any W_7a044 = Some (Op ALU_AND 16 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a048 : bv 32 := 0x00f686b3.
Lemma F_7a048 : fetch_word Plain.M.loaded_segments (0x7a0a0 : word) = Some W_7a048.
Proof. vm_refl. Qed.
Lemma D_7a048 : decode_any W_7a048 = Some (Op ALU_ADD 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a04c : bv 32 := 0x40f5053b.
Lemma F_7a04c : fetch_word Plain.M.loaded_segments (0x7a0a4 : word) = Some W_7a04c.
Proof. vm_refl. Qed.
Lemma D_7a04c : decode_any W_7a04c = Some (Op32 ALU_SUB 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a050 : bv 32 := 0x43f55793.
Lemma F_7a050 : fetch_word Plain.M.loaded_segments (0x7a0a8 : word) = Some W_7a050.
Proof. vm_refl. Qed.
Lemma D_7a050 : decode_any W_7a050 = Some (ShiftImm ALU_SRA 15 10 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a054 : bv 32 := 0x00a028b3.
Lemma F_7a054 : fetch_word Plain.M.loaded_segments (0x7a0ac : word) = Some W_7a054.
Proof. vm_refl. Qed.
Lemma D_7a054 : decode_any W_7a054 = Some (Op ALU_SLT 17 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a058 : bv 32 := 0x00a7f7b3.
Lemma F_7a058 : fetch_word Plain.M.loaded_segments (0x7a0b0 : word) = Some W_7a058.
Proof. vm_refl. Qed.
Lemma D_7a058 : decode_any W_7a058 = Some (Op ALU_AND 15 15 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a05c : bv 32 := 0x411008bb.
Lemma F_7a05c : fetch_word Plain.M.loaded_segments (0x7a0b4 : word) = Some W_7a05c.
Proof. vm_refl. Qed.
Lemma D_7a05c : decode_any W_7a05c = Some (Op32 ALU_SUB 17 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a060 : bv 32 := 0x00f68933.
Lemma F_7a060 : fetch_word Plain.M.loaded_segments (0x7a0b8 : word) = Some W_7a060.
Proof. vm_refl. Qed.
Lemma D_7a060 : decode_any W_7a060 = Some (Op ALU_ADD 18 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a064 : bv 32 := 0x00a8fbb3.
Lemma F_7a064 : fetch_word Plain.M.loaded_segments (0x7a0bc : word) = Some W_7a064.
Proof. vm_refl. Qed.
Lemma D_7a064 : decode_any W_7a064 = Some (Op ALU_AND 23 17 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a068 : bv 32 := 0x40f80dbb.
Lemma F_7a068 : fetch_word Plain.M.loaded_segments (0x7a0c0 : word) = Some W_7a068.
Proof. vm_refl. Qed.
Lemma D_7a068 : decode_any W_7a068 = Some (Op32 ALU_SUB 27 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a06c : bv 32 := 0x40c9053b.
Lemma F_7a06c : fetch_word Plain.M.loaded_segments (0x7a0c4 : word) = Some W_7a06c.
Proof. vm_refl. Qed.
Lemma D_7a06c : decode_any W_7a06c = Some (Op32 ALU_SUB 10 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a070 : bv 32 := 0x01b5053b.
Lemma F_7a070 : fetch_word Plain.M.loaded_segments (0x7a0c8 : word) = Some W_7a070.
Proof. vm_refl. Qed.
Lemma D_7a070 : decode_any W_7a070 = Some (Op32 ALU_ADD 10 10 27, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a074 : bv 32 := 0x00a02633.
Lemma F_7a074 : fetch_word Plain.M.loaded_segments (0x7a0cc : word) = Some W_7a074.
Proof. vm_refl. Qed.
Lemma D_7a074 : decode_any W_7a074 = Some (Op ALU_SLT 12 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a078 : bv 32 := 0x40c00633.
Lemma F_7a078 : fetch_word Plain.M.loaded_segments (0x7a0d0 : word) = Some W_7a078.
Proof. vm_refl. Qed.
Lemma D_7a078 : decode_any W_7a078 = Some (Op ALU_SUB 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a07c : bv 32 := 0x00a67c33.
Lemma F_7a07c : fetch_word Plain.M.loaded_segments (0x7a0d4 : word) = Some W_7a07c.
Proof. vm_refl. Qed.
Lemma D_7a07c : decode_any W_7a07c = Some (Op ALU_AND 24 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a080 : bv 32 := 0x4189053b.
Lemma F_7a080 : fetch_word Plain.M.loaded_segments (0x7a0d8 : word) = Some W_7a080.
Proof. vm_refl. Qed.
Lemma D_7a080 : decode_any W_7a080 = Some (Op32 ALU_SUB 10 18 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a084 : bv 32 := 0x40bb85bb.
Lemma F_7a084 : fetch_word Plain.M.loaded_segments (0x7a0dc : word) = Some W_7a084.
Proof. vm_refl. Qed.
Lemma D_7a084 : decode_any W_7a084 = Some (Op32 ALU_SUB 11 23 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a088 : bv 32 := 0x00a585bb.
Lemma F_7a088 : fetch_word Plain.M.loaded_segments (0x7a0e0 : word) = Some W_7a088.
Proof. vm_refl. Qed.
Lemma D_7a088 : decode_any W_7a088 = Some (Op32 ALU_ADD 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a08c : bv 32 := 0x00b02633.
Lemma F_7a08c : fetch_word Plain.M.loaded_segments (0x7a0e4 : word) = Some W_7a08c.
Proof. vm_refl. Qed.
Lemma D_7a08c : decode_any W_7a08c = Some (Op ALU_SLT 12 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a090 : bv 32 := 0x40c00633.
Lemma F_7a090 : fetch_word Plain.M.loaded_segments (0x7a0e8 : word) = Some W_7a090.
Proof. vm_refl. Qed.
Lemma D_7a090 : decode_any W_7a090 = Some (Op ALU_SUB 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a094 : bv 32 := 0x00b67cb3.
Lemma F_7a094 : fetch_word Plain.M.loaded_segments (0x7a0ec : word) = Some W_7a094.
Proof. vm_refl. Qed.
Lemma D_7a094 : decode_any W_7a094 = Some (Op ALU_AND 25 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a098 : bv 32 := 0x4195063b.
Lemma F_7a098 : fetch_word Plain.M.loaded_segments (0x7a0f0 : word) = Some W_7a098.
Proof. vm_refl. Qed.
Lemma D_7a098 : decode_any W_7a098 = Some (Op32 ALU_SUB 12 10 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a09c : bv 32 := 0x00c04463.
Lemma F_7a09c : fetch_word Plain.M.loaded_segments (0x7a0f4 : word) = Some W_7a09c.
Proof. vm_refl. Qed.
Lemma D_7a09c : decode_any W_7a09c = Some (Branch BC_LT 0 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0a0 : bv 32 := 0x6510106f.
Lemma F_7a0a0 : fetch_word Plain.M.loaded_segments (0x7a0f8 : word) = Some W_7a0a0.
Proof. vm_refl. Qed.
Lemma D_7a0a0 : decode_any W_7a0a0 = Some (Jal 0 7760, 4%Z).
Proof. vm_refl. Qed.


(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)




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
Definition W_7a0a4 : bv 32 := 0x09813683.
Lemma F_7a0a4 : fetch_word Plain.M.loaded_segments (0x7a0fc : word) = Some W_7a0a4.
Proof. vm_refl. Qed.
Lemma D_7a0a4 : decode_any W_7a0a4 = Some (Load SZ8 true 13 2 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0a8 : bv 32 := 0x07813583.
Lemma F_7a0a8 : fetch_word Plain.M.loaded_segments (0x7a100 : word) = Some W_7a0a8.
Proof. vm_refl. Qed.
Lemma D_7a0a8 : decode_any W_7a0a8 = Some (Load SZ8 true 11 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0ac : bv 32 := 0x08013b03.
Lemma F_7a0ac : fetch_word Plain.M.loaded_segments (0x7a104 : word) = Some W_7a0ac.
Proof. vm_refl. Qed.
Lemma D_7a0ac : decode_any W_7a0ac = Some (Load SZ8 true 22 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0b0 : bv 32 := 0x01a9e7b3.
Lemma F_7a0b0 : fetch_word Plain.M.loaded_segments (0x7a108 : word) = Some W_7a0b0.
Proof. vm_refl. Qed.
Lemma D_7a0b0 : decode_any W_7a0b0 = Some (Op ALU_OR 15 19 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0b4 : bv 32 := 0x01f7f793.
Lemma F_7a0b4 : fetch_word Plain.M.loaded_segments (0x7a10c : word) = Some W_7a0b4.
Proof. vm_refl. Qed.
Lemma D_7a0b4 : decode_any W_7a0b4 = Some (OpImm ALU_AND 15 15 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0b8 : bv 32 := 0xfff58a93.
Lemma F_7a0b8 : fetch_word Plain.M.loaded_segments (0x7a110 : word) = Some W_7a0b8.
Proof. vm_refl. Qed.
Lemma D_7a0b8 : decode_any W_7a0b8 = Some (OpImm ALU_ADD 21 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0bc : bv 32 := 0x0a078463.
Lemma F_7a0bc : fetch_word Plain.M.loaded_segments (0x7a114 : word) = Some W_7a0bc.
Proof. vm_refl. Qed.
Lemma D_7a0bc : decode_any W_7a0bc = Some (Branch BC_EQ 15 0 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0c0 : bv 32 := 0x01f9fa13.
Lemma F_7a0c0 : fetch_word Plain.M.loaded_segments (0x7a118 : word) = Some W_7a0c0.
Proof. vm_refl. Qed.
Lemma D_7a0c0 : decode_any W_7a0c0 = Some (OpImm ALU_AND 20 19 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0c4 : bv 32 := 0x01fd7f13.
Lemma F_7a0c4 : fetch_word Plain.M.loaded_segments (0x7a11c : word) = Some W_7a0c4.
Proof. vm_refl. Qed.
Lemma D_7a0c4 : decode_any W_7a0c4 = Some (OpImm ALU_AND 30 26 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0c8 : bv 32 := 0xfff98517.
Lemma F_7a0c8 : fetch_word Plain.M.loaded_segments (0x7a120 : word) = Some W_7a0c8.
Proof. vm_refl. Qed.
Lemma D_7a0c8 : decode_any W_7a0c8 = Some (Auipc 10 1048472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0cc : bv 32 := 0x68b50513.
Lemma F_7a0cc : fetch_word Plain.M.loaded_segments (0x7a124 : word) = Some W_7a0cc.
Proof. vm_refl. Qed.
Lemma D_7a0cc : decode_any W_7a0cc = Some (OpImm ALU_ADD 10 10 1675, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0d0 : bv 32 := 0x0bea1a63.
Lemma F_7a0d0 : fetch_word Plain.M.loaded_segments (0x7a128 : word) = Some W_7a0d0.
Proof. vm_refl. Qed.
Lemma D_7a0d0 : decode_any W_7a0d0 = Some (Branch BC_NE 20 30 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a164 : bv 32 := 0x01f37793.
Lemma F_7a164 : fetch_word Plain.M.loaded_segments (0x7a1bc : word) = Some W_7a164.
Proof. vm_refl. Qed.
Lemma D_7a164 : decode_any W_7a164 = Some (OpImm ALU_AND 15 6 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a168 : bv 32 := 0x10078263.
Lemma F_7a168 : fetch_word Plain.M.loaded_segments (0x7a1c0 : word) = Some W_7a168.
Proof. vm_refl. Qed.
Lemma D_7a168 : decode_any W_7a168 = Some (Branch BC_EQ 15 0 260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a16c : bv 32 := 0x00279513.
Lemma F_7a16c : fetch_word Plain.M.loaded_segments (0x7a1c4 : word) = Some W_7a16c.
Proof. vm_refl. Qed.
Lemma D_7a16c : decode_any W_7a16c = Some (ShiftImm ALU_SLL 10 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a170 : bv 32 := 0xfffa5817.
Lemma F_7a170 : fetch_word Plain.M.loaded_segments (0x7a1c8 : word) = Some W_7a170.
Proof. vm_refl. Qed.
Lemma D_7a170 : decode_any W_7a170 = Some (Auipc 16 1048485, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a174 : bv 32 := 0x25c80813.
Lemma F_7a174 : fetch_word Plain.M.loaded_segments (0x7a1cc : word) = Some W_7a174.
Proof. vm_refl. Qed.
Lemma D_7a174 : decode_any W_7a174 = Some (OpImm ALU_ADD 16 16 604, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a178 : bv 32 := 0x00a80533.
Lemma F_7a178 : fetch_word Plain.M.loaded_segments (0x7a1d0 : word) = Some W_7a178.
Proof. vm_refl. Qed.
Lemma D_7a178 : decode_any W_7a178 = Some (Op ALU_ADD 10 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a17c : bv 32 := 0x00052383.
Lemma F_7a17c : fetch_word Plain.M.loaded_segments (0x7a1d4 : word) = Some W_7a17c.
Proof. vm_refl. Qed.
Lemma D_7a17c : decode_any W_7a17c = Some (Load SZ4 true 7 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a180 : bv 32 := 0x0ec0006f.
Lemma F_7a180 : fetch_word Plain.M.loaded_segments (0x7a1d8 : word) = Some W_7a180.
Proof. vm_refl. Qed.
Lemma D_7a180 : decode_any W_7a180 = Some (Jal 0 236, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a184 : bv 32 := 0x001a3813.
Lemma F_7a184 : fetch_word Plain.M.loaded_segments (0x7a1dc : word) = Some W_7a184.
Proof. vm_refl. Qed.
Lemma D_7a184 : decode_any W_7a184 = Some (OpImm ALU_SLTU 16 20 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a188 : bv 32 := 0x02000393.
Lemma F_7a188 : fetch_word Plain.M.loaded_segments (0x7a1e0 : word) = Some W_7a188.
Proof. vm_refl. Qed.
Lemma D_7a188 : decode_any W_7a188 = Some (OpImm ALU_ADD 7 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a18c : bv 32 := 0x41438eb3.
Lemma F_7a18c : fetch_word Plain.M.loaded_segments (0x7a1e4 : word) = Some W_7a18c.
Proof. vm_refl. Qed.
Lemma D_7a18c : decode_any W_7a18c = Some (Op ALU_SUB 29 7 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a190 : bv 32 := 0xfff80813.
Lemma F_7a190 : fetch_word Plain.M.loaded_segments (0x7a1e8 : word) = Some W_7a190.
Proof. vm_refl. Qed.
Lemma D_7a190 : decode_any W_7a190 = Some (OpImm ALU_ADD 16 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a194 : bv 32 := 0x01d87e33.
Lemma F_7a194 : fetch_word Plain.M.loaded_segments (0x7a1ec : word) = Some W_7a194.
Proof. vm_refl. Qed.
Lemma D_7a194 : decode_any W_7a194 = Some (Op ALU_AND 28 16 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a198 : bv 32 := 0x22078e63.
Lemma F_7a198 : fetch_word Plain.M.loaded_segments (0x7a1f0 : word) = Some W_7a198.
Proof. vm_refl. Qed.
Lemma D_7a198 : decode_any W_7a198 = Some (Branch BC_EQ 15 0 572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a19c : bv 32 := 0x41e38fb3.
Lemma F_7a19c : fetch_word Plain.M.loaded_segments (0x7a1f4 : word) = Some W_7a19c.
Proof. vm_refl. Qed.
Lemma D_7a19c : decode_any W_7a19c = Some (Op ALU_SUB 31 7 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1a0 : bv 32 := 0x001f3793.
Lemma F_7a1a0 : fetch_word Plain.M.loaded_segments (0x7a1f8 : word) = Some W_7a1a0.
Proof. vm_refl. Qed.
Lemma D_7a1a0 : decode_any W_7a1a0 = Some (OpImm ALU_SLTU 15 30 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1a4 : bv 32 := 0x000e081b.
Lemma F_7a1a4 : fetch_word Plain.M.loaded_segments (0x7a1fc : word) = Some W_7a1a4.
Proof. vm_refl. Qed.
Lemma D_7a1a4 : decode_any W_7a1a4 = Some (OpImm32 16 28 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1a8 : bv 32 := 0xfffa5897.
Lemma F_7a1a8 : fetch_word Plain.M.loaded_segments (0x7a200 : word) = Some W_7a1a8.
Proof. vm_refl. Qed.
Lemma D_7a1a8 : decode_any W_7a1a8 = Some (Auipc 17 1048485, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1ac : bv 32 := 0xfff78793.
Lemma F_7a1ac : fetch_word Plain.M.loaded_segments (0x7a204 : word) = Some W_7a1ac.
Proof. vm_refl. Qed.
Lemma D_7a1ac : decode_any W_7a1ac = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1b0 : bv 32 := 0x01f7f7b3.
Lemma F_7a1b0 : fetch_word Plain.M.loaded_segments (0x7a208 : word) = Some W_7a1b0.
Proof. vm_refl. Qed.
Lemma D_7a1b0 : decode_any W_7a1b0 = Some (Op ALU_AND 15 15 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1b4 : bv 32 := 0x0107b833.
Lemma F_7a1b4 : fetch_word Plain.M.loaded_segments (0x7a20c : word) = Some W_7a1b4.
Proof. vm_refl. Qed.
Lemma D_7a1b4 : decode_any W_7a1b4 = Some (Op ALU_SLTU 16 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1b8 : bv 32 := 0x40fe07bb.
Lemma F_7a1b8 : fetch_word Plain.M.loaded_segments (0x7a210 : word) = Some W_7a1b8.
Proof. vm_refl. Qed.
Lemma D_7a1b8 : decode_any W_7a1b8 = Some (Op32 ALU_SUB 15 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1bc : bv 32 := 0x00184813.
Lemma F_7a1bc : fetch_word Plain.M.loaded_segments (0x7a214 : word) = Some W_7a1bc.
Proof. vm_refl. Qed.
Lemma D_7a1bc : decode_any W_7a1bc = Some (OpImm ALU_XOR 16 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1c0 : bv 32 := 0x00581813.
Lemma F_7a1c0 : fetch_word Plain.M.loaded_segments (0x7a218 : word) = Some W_7a1c0.
Proof. vm_refl. Qed.
Lemma D_7a1c0 : decode_any W_7a1c0 = Some (ShiftImm ALU_SLL 16 16 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1c4 : bv 32 := 0x010787bb.
Lemma F_7a1c4 : fetch_word Plain.M.loaded_segments (0x7a21c : word) = Some W_7a1c4.
Proof. vm_refl. Qed.
Lemma D_7a1c4 : decode_any W_7a1c4 = Some (Op32 ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1c8 : bv 32 := 0x00279813.
Lemma F_7a1c8 : fetch_word Plain.M.loaded_segments (0x7a220 : word) = Some W_7a1c8.
Proof. vm_refl. Qed.
Lemma D_7a1c8 : decode_any W_7a1c8 = Some (ShiftImm ALU_SLL 16 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1cc : bv 32 := 0x1a088413.
Lemma F_7a1cc : fetch_word Plain.M.loaded_segments (0x7a224 : word) = Some W_7a1cc.
Proof. vm_refl. Qed.
Lemma D_7a1cc : decode_any W_7a1cc = Some (OpImm ALU_ADD 8 17 416, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1d0 : bv 32 := 0x01040833.
Lemma F_7a1d0 : fetch_word Plain.M.loaded_segments (0x7a228 : word) = Some W_7a1d0.
Proof. vm_refl. Qed.
Lemma D_7a1d0 : decode_any W_7a1d0 = Some (Op ALU_ADD 16 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1d4 : bv 32 := 0x00082883.
Lemma F_7a1d4 : fetch_word Plain.M.loaded_segments (0x7a22c : word) = Some W_7a1d4.
Proof. vm_refl. Qed.
Lemma D_7a1d4 : decode_any W_7a1d4 = Some (Load SZ4 true 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1d8 : bv 32 := 0x40f3883b.
Lemma F_7a1d8 : fetch_word Plain.M.loaded_segments (0x7a230 : word) = Some W_7a1d8.
Proof. vm_refl. Qed.
Lemma D_7a1d8 : decode_any W_7a1d8 = Some (Op32 ALU_SUB 16 7 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1dc : bv 32 := 0x280a0263.
Lemma F_7a1dc : fetch_word Plain.M.loaded_segments (0x7a234 : word) = Some W_7a1dc.
Proof. vm_refl. Qed.
Lemma D_7a1dc : decode_any W_7a1dc = Some (Branch BC_EQ 20 0 644, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1e0 : bv 32 := 0x002e9493.
Lemma F_7a1e0 : fetch_word Plain.M.loaded_segments (0x7a238 : word) = Some W_7a1e0.
Proof. vm_refl. Qed.
Lemma D_7a1e0 : decode_any W_7a1e0 = Some (ShiftImm ALU_SLL 9 29 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1e4 : bv 32 := 0x02ed8933.
Lemma F_7a1e4 : fetch_word Plain.M.loaded_segments (0x7a23c : word) = Some W_7a1e4.
Proof. vm_refl. Qed.
Lemma D_7a1e4 : decode_any W_7a1e4 = Some (Mul M_MUL 18 27 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1e8 : bv 32 := 0x0059dc1b.
Lemma F_7a1e8 : fetch_word Plain.M.loaded_segments (0x7a240 : word) = Some W_7a1e8.
Proof. vm_refl. Qed.
Lemma D_7a1e8 : decode_any W_7a1e8 = Some (ShiftImm32 ALU_SRL 24 19 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1ec : bv 32 := 0x009404b3.
Lemma F_7a1ec : fetch_word Plain.M.loaded_segments (0x7a244 : word) = Some W_7a1ec.
Proof. vm_refl. Qed.
Lemma D_7a1ec : decode_any W_7a1ec = Some (Op ALU_ADD 9 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1f0 : bv 32 := 0x02db8cb3.
Lemma F_7a1f0 : fetch_word Plain.M.loaded_segments (0x7a248 : word) = Some W_7a1f0.
Proof. vm_refl. Qed.
Lemma D_7a1f0 : decode_any W_7a1f0 = Some (Mul M_MUL 25 23 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1f4 : bv 32 := 0x00291913.
Lemma F_7a1f4 : fetch_word Plain.M.loaded_segments (0x7a24c : word) = Some W_7a1f4.
Proof. vm_refl. Qed.
Lemma D_7a1f4 : decode_any W_7a1f4 = Some (ShiftImm ALU_SLL 18 18 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1f8 : bv 32 := 0x002c1413.
Lemma F_7a1f8 : fetch_word Plain.M.loaded_segments (0x7a250 : word) = Some W_7a1f8.
Proof. vm_refl. Qed.
Lemma D_7a1f8 : decode_any W_7a1f8 = Some (ShiftImm ALU_SLL 8 24 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a1fc : bv 32 := 0x01228933.
Lemma F_7a1fc : fetch_word Plain.M.loaded_segments (0x7a254 : word) = Some W_7a1fc.
Proof. vm_refl. Qed.
Lemma D_7a1fc : decode_any W_7a1fc = Some (Op ALU_ADD 18 5 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a200 : bv 32 := 0x00890433.
Lemma F_7a200 : fetch_word Plain.M.loaded_segments (0x7a258 : word) = Some W_7a200.
Proof. vm_refl. Qed.
Lemma D_7a200 : decode_any W_7a200 = Some (Op ALU_ADD 8 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a204 : bv 32 := 0x005d591b.
Lemma F_7a204 : fetch_word Plain.M.loaded_segments (0x7a25c : word) = Some W_7a204.
Proof. vm_refl. Qed.
Lemma D_7a204 : decode_any W_7a204 = Some (ShiftImm32 ALU_SRL 18 26 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a208 : bv 32 := 0x002c9c93.
Lemma F_7a208 : fetch_word Plain.M.loaded_segments (0x7a260 : word) = Some W_7a208.
Proof. vm_refl. Qed.
Lemma D_7a208 : decode_any W_7a208 = Some (ShiftImm ALU_SLL 25 25 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a20c : bv 32 := 0x00291093.
Lemma F_7a20c : fetch_word Plain.M.loaded_segments (0x7a264 : word) = Some W_7a20c.
Proof. vm_refl. Qed.
Lemma D_7a20c : decode_any W_7a20c = Some (ShiftImm ALU_SLL 1 18 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a210 : bv 32 := 0x0004a903.
Lemma F_7a210 : fetch_word Plain.M.loaded_segments (0x7a268 : word) = Some W_7a210.
Proof. vm_refl. Qed.
Lemma D_7a210 : decode_any W_7a210 = Some (Load SZ4 true 18 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a214 : bv 32 := 0x019b0cb3.
Lemma F_7a214 : fetch_word Plain.M.loaded_segments (0x7a26c : word) = Some W_7a214.
Proof. vm_refl. Qed.
Lemma D_7a214 : decode_any W_7a214 = Some (Op ALU_ADD 25 22 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a218 : bv 32 := 0x001c80b3.
Lemma F_7a218 : fetch_word Plain.M.loaded_segments (0x7a270 : word) = Some W_7a218.
Proof. vm_refl. Qed.
Lemma D_7a218 : decode_any W_7a218 = Some (Op ALU_ADD 1 25 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a21c : bv 32 := 0x01ea3cb3.
Lemma F_7a21c : fetch_word Plain.M.loaded_segments (0x7a274 : word) = Some W_7a21c.
Proof. vm_refl. Qed.
Lemma D_7a21c : decode_any W_7a21c = Some (Op ALU_SLTU 25 20 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a220 : bv 32 := 0x006fbf33.
Lemma F_7a220 : fetch_word Plain.M.loaded_segments (0x7a278 : word) = Some W_7a220.
Proof. vm_refl. Qed.
Lemma D_7a220 : decode_any W_7a220 = Some (Op ALU_SLTU 30 31 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a224 : bv 32 := 0x001f4c13.
Lemma F_7a224 : fetch_word Plain.M.loaded_segments (0x7a27c : word) = Some W_7a224.
Proof. vm_refl. Qed.
Lemma D_7a224 : decode_any W_7a224 = Some (OpImm ALU_XOR 24 30 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a228 : bv 32 := 0x25d37463.
Lemma F_7a228 : fetch_word Plain.M.loaded_segments (0x7a280 : word) = Some W_7a228.
Proof. vm_refl. Qed.
Lemma D_7a228 : decode_any W_7a228 = Some (Branch BC_GEU 6 29 584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a22c : bv 32 := 0x00000493.
Lemma F_7a22c : fetch_word Plain.M.loaded_segments (0x7a284 : word) = Some W_7a22c.
Proof. vm_refl. Qed.
Lemma D_7a22c : decode_any W_7a22c = Some (OpImm ALU_ADD 9 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a230 : bv 32 := 0x00000e93.
Lemma F_7a230 : fetch_word Plain.M.loaded_segments (0x7a288 : word) = Some W_7a230.
Proof. vm_refl. Qed.
Lemma D_7a230 : decode_any W_7a230 = Some (OpImm ALU_ADD 29 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a234 : bv 32 := 0x00000e13.
Lemma F_7a234 : fetch_word Plain.M.loaded_segments (0x7a28c : word) = Some W_7a234.
Proof. vm_refl. Qed.
Lemma D_7a234 : decode_any W_7a234 = Some (OpImm ALU_ADD 28 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a238 : bv 32 := 0x00000293.
Lemma F_7a238 : fetch_word Plain.M.loaded_segments (0x7a290 : word) = Some W_7a238.
Proof. vm_refl. Qed.
Lemma D_7a238 : decode_any W_7a238 = Some (OpImm ALU_ADD 5 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a23c : bv 32 := 0x00000d13.
Lemma F_7a23c : fetch_word Plain.M.loaded_segments (0x7a294 : word) = Some W_7a23c.
Proof. vm_refl. Qed.
Lemma D_7a23c : decode_any W_7a23c = Some (OpImm ALU_ADD 26 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a240 : bv 32 := 0x0143033b.
Lemma F_7a240 : fetch_word Plain.M.loaded_segments (0x7a298 : word) = Some W_7a240.
Proof. vm_refl. Qed.
Lemma D_7a240 : decode_any W_7a240 = Some (Op32 ALU_ADD 6 6 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a244 : bv 32 := 0xfffa5397.
Lemma F_7a244 : fetch_word Plain.M.loaded_segments (0x7a29c : word) = Some W_7a244.
Proof. vm_refl. Qed.
Lemma D_7a244 : decode_any W_7a244 = Some (Auipc 7 1048485, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a248 : bv 32 := 0x00231313.
Lemma F_7a248 : fetch_word Plain.M.loaded_segments (0x7a2a0 : word) = Some W_7a248.
Proof. vm_refl. Qed.
Lemma D_7a248 : decode_any W_7a248 = Some (ShiftImm ALU_SLL 6 6 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a24c : bv 32 := 0x18838393.
Lemma F_7a24c : fetch_word Plain.M.loaded_segments (0x7a2a4 : word) = Some W_7a24c.
Proof. vm_refl. Qed.
Lemma D_7a24c : decode_any W_7a24c = Some (OpImm ALU_ADD 7 7 392, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a250 : bv 32 := 0x00638333.
Lemma F_7a250 : fetch_word Plain.M.loaded_segments (0x7a2a8 : word) = Some W_7a250.
Proof. vm_refl. Qed.
Lemma D_7a250 : decode_any W_7a250 = Some (Op ALU_ADD 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a254 : bv 32 := 0x00032303.
Lemma F_7a254 : fetch_word Plain.M.loaded_segments (0x7a2ac : word) = Some W_7a254.
Proof. vm_refl. Qed.
Lemma D_7a254 : decode_any W_7a254 = Some (Load SZ4 true 6 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a258 : bv 32 := 0x00100393.
Lemma F_7a258 : fetch_word Plain.M.loaded_segments (0x7a2b0 : word) = Some W_7a258.
Proof. vm_refl. Qed.
Lemma D_7a258 : decode_any W_7a258 = Some (OpImm ALU_ADD 7 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a25c : bv 32 := 0x00713023.
Lemma F_7a25c : fetch_word Plain.M.loaded_segments (0x7a2b4 : word) = Some W_7a25c.
Proof. vm_refl. Qed.
Lemma D_7a25c : decode_any W_7a25c = Some (Store SZ8 2 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a260 : bv 32 := 0x01237933.
Lemma F_7a260 : fetch_word Plain.M.loaded_segments (0x7a2b8 : word) = Some W_7a260.
Proof. vm_refl. Qed.
Lemma D_7a260 : decode_any W_7a260 = Some (Op ALU_AND 18 6 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a264 : bv 32 := 0x00100993.
Lemma F_7a264 : fetch_word Plain.M.loaded_segments (0x7a2bc : word) = Some W_7a264.
Proof. vm_refl. Qed.
Lemma D_7a264 : decode_any W_7a264 = Some (OpImm ALU_ADD 19 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a268 : bv 32 := 0x2e40006f.
Lemma F_7a268 : fetch_word Plain.M.loaded_segments (0x7a2c0 : word) = Some W_7a268.
Proof. vm_refl. Qed.
Lemma D_7a268 : decode_any W_7a268 = Some (Jal 0 740, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a26c : bv 32 := 0xfffa4517.
Lemma F_7a26c : fetch_word Plain.M.loaded_segments (0x7a2c4 : word) = Some W_7a26c.
Proof. vm_refl. Qed.
Lemma D_7a26c : decode_any W_7a26c = Some (Auipc 10 1048484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a270 : bv 32 := 0x00d00813.
Lemma F_7a270 : fetch_word Plain.M.loaded_segments (0x7a2c8 : word) = Some W_7a270.
Proof. vm_refl. Qed.
Lemma D_7a270 : decode_any W_7a270 = Some (OpImm ALU_ADD 16 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a274 : bv 32 := 0x1be50513.
Lemma F_7a274 : fetch_word Plain.M.loaded_segments (0x7a2cc : word) = Some W_7a274.
Proof. vm_refl. Qed.
Lemma D_7a274 : decode_any W_7a274 = Some (OpImm ALU_ADD 10 10 446, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a278 : bv 32 := 0x47586663.
Lemma F_7a278 : fetch_word Plain.M.loaded_segments (0x7a2d0 : word) = Some W_7a278.
Proof. vm_refl. Qed.
Lemma D_7a278 : decode_any W_7a278 = Some (Branch BC_LTU 16 21 1132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a27c : bv 32 := 0x00535e1b.
Lemma F_7a27c : fetch_word Plain.M.loaded_segments (0x7a2d4 : word) = Some W_7a27c.
Proof. vm_refl. Qed.
Lemma D_7a27c : decode_any W_7a27c = Some (ShiftImm32 ALU_SRL 28 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a280 : bv 32 := 0x02db883b.
Lemma F_7a280 : fetch_word Plain.M.loaded_segments (0x7a2d8 : word) = Some W_7a280.
Proof. vm_refl. Qed.
Lemma D_7a280 : decode_any W_7a280 = Some (Mul32 M_MUL 16 23 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a284 : bv 32 := 0x005d589b.
Lemma F_7a284 : fetch_word Plain.M.loaded_segments (0x7a2dc : word) = Some W_7a284.
Proof. vm_refl. Qed.
Lemma D_7a284 : decode_any W_7a284 = Some (ShiftImm32 ALU_SRL 17 26 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a288 : bv 32 := 0x02ed8ebb.
Lemma F_7a288 : fetch_word Plain.M.loaded_segments (0x7a2e0 : word) = Some W_7a288.
Proof. vm_refl. Qed.
Lemma D_7a288 : decode_any W_7a288 = Some (Mul32 M_MUL 29 27 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a28c : bv 32 := 0x002a9a93.
Lemma F_7a28c : fetch_word Plain.M.loaded_segments (0x7a2e4 : word) = Some W_7a28c.
Proof. vm_refl. Qed.
Lemma D_7a28c : decode_any W_7a28c = Some (ShiftImm ALU_SLL 21 21 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a290 : bv 32 := 0x00281813.
Lemma F_7a290 : fetch_word Plain.M.loaded_segments (0x7a2e8 : word) = Some W_7a290.
Proof. vm_refl. Qed.
Lemma D_7a290 : decode_any W_7a290 = Some (ShiftImm ALU_SLL 16 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a294 : bv 32 := 0x010b0833.
Lemma F_7a294 : fetch_word Plain.M.loaded_segments (0x7a2ec : word) = Some W_7a294.
Proof. vm_refl. Qed.
Lemma D_7a294 : decode_any W_7a294 = Some (Op ALU_ADD 16 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a298 : bv 32 := 0xfffa5f17.
Lemma F_7a298 : fetch_word Plain.M.loaded_segments (0x7a2f0 : word) = Some W_7a298.
Proof. vm_refl. Qed.
Lemma D_7a298 : decode_any W_7a298 = Some (Auipc 30 1048485, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a29c : bv 32 := 0x00289893.
Lemma F_7a29c : fetch_word Plain.M.loaded_segments (0x7a2f4 : word) = Some W_7a29c.
Proof. vm_refl. Qed.
Lemma D_7a29c : decode_any W_7a29c = Some (ShiftImm ALU_SLL 17 17 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2a0 : bv 32 := 0x002e9e93.
Lemma F_7a2a0 : fetch_word Plain.M.loaded_segments (0x7a2f8 : word) = Some W_7a2a0.
Proof. vm_refl. Qed.
Lemma D_7a2a0 : decode_any W_7a2a0 = Some (ShiftImm ALU_SLL 29 29 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2a4 : bv 32 := 0x078f0f93.
Lemma F_7a2a4 : fetch_word Plain.M.loaded_segments (0x7a2fc : word) = Some W_7a2a4.
Proof. vm_refl. Qed.
Lemma D_7a2a4 : decode_any W_7a2a4 = Some (OpImm ALU_ADD 31 30 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2a8 : bv 32 := 0x01fa8ab3.
Lemma F_7a2a8 : fetch_word Plain.M.loaded_segments (0x7a300 : word) = Some W_7a2a8.
Proof. vm_refl. Qed.
Lemma D_7a2a8 : decode_any W_7a2a8 = Some (Op ALU_ADD 21 21 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2ac : bv 32 := 0x01180833.
Lemma F_7a2ac : fetch_word Plain.M.loaded_segments (0x7a304 : word) = Some W_7a2ac.
Proof. vm_refl. Qed.
Lemma D_7a2ac : decode_any W_7a2ac = Some (Op ALU_ADD 16 16 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2b0 : bv 32 := 0x000aa883.
Lemma F_7a2b0 : fetch_word Plain.M.loaded_segments (0x7a308 : word) = Some W_7a2b0.
Proof. vm_refl. Qed.
Lemma D_7a2b0 : decode_any W_7a2b0 = Some (Load SZ4 true 17 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2b4 : bv 32 := 0x01d28433.
Lemma F_7a2b4 : fetch_word Plain.M.loaded_segments (0x7a30c : word) = Some W_7a2b4.
Proof. vm_refl. Qed.
Lemma D_7a2b4 : decode_any W_7a2b4 = Some (Op ALU_ADD 8 5 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2b8 : bv 32 := 0x0059df1b.
Lemma F_7a2b8 : fetch_word Plain.M.loaded_segments (0x7a310 : word) = Some W_7a2b8.
Proof. vm_refl. Qed.
Lemma D_7a2b8 : decode_any W_7a2b8 = Some (ShiftImm32 ALU_SRL 30 19 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2bc : bv 32 := 0x002f1f13.
Lemma F_7a2bc : fetch_word Plain.M.loaded_segments (0x7a314 : word) = Some W_7a2bc.
Proof. vm_refl. Qed.
Lemma D_7a2bc : decode_any W_7a2bc = Some (ShiftImm ALU_SLL 30 30 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2c0 : bv 32 := 0x01f88fb3.
Lemma F_7a2c0 : fetch_word Plain.M.loaded_segments (0x7a318 : word) = Some W_7a2c0.
Proof. vm_refl. Qed.
Lemma D_7a2c0 : decode_any W_7a2c0 = Some (Op ALU_ADD 31 17 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2c4 : bv 32 := 0x01e408b3.
Lemma F_7a2c4 : fetch_word Plain.M.loaded_segments (0x7a31c : word) = Some W_7a2c4.
Proof. vm_refl. Qed.
Lemma D_7a2c4 : decode_any W_7a2c4 = Some (Op ALU_ADD 17 8 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2c8 : bv 32 := 0x000f8067.
Lemma F_7a2c8 : fetch_word Plain.M.loaded_segments (0x7a320 : word) = Some W_7a2c8.
Proof. vm_refl. Qed.
Lemma D_7a2c8 : decode_any W_7a2c8 = Some (Jalr 0 31 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a460 : bv 32 := 0x00000093.
Lemma F_7a460 : fetch_word Plain.M.loaded_segments (0x7a4b8 : word) = Some W_7a460.
Proof. vm_refl. Qed.
Lemma D_7a460 : decode_any W_7a460 = Some (OpImm ALU_ADD 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a464 : bv 32 := 0x00000413.
Lemma F_7a464 : fetch_word Plain.M.loaded_segments (0x7a4bc : word) = Some W_7a464.
Proof. vm_refl. Qed.
Lemma D_7a464 : decode_any W_7a464 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a468 : bv 32 := 0x00000e93.
Lemma F_7a468 : fetch_word Plain.M.loaded_segments (0x7a4c0 : word) = Some W_7a468.
Proof. vm_refl. Qed.
Lemma D_7a468 : decode_any W_7a468 = Some (OpImm ALU_ADD 29 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a46c : bv 32 := 0x00000913.
Lemma F_7a46c : fetch_word Plain.M.loaded_segments (0x7a4c4 : word) = Some W_7a46c.
Proof. vm_refl. Qed.
Lemma D_7a46c : decode_any W_7a46c = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a470 : bv 32 := 0x41d30fbb.
Lemma F_7a470 : fetch_word Plain.M.loaded_segments (0x7a4c8 : word) = Some W_7a470.
Proof. vm_refl. Qed.
Lemma D_7a470 : decode_any W_7a470 = Some (Op32 ALU_SUB 31 6 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a474 : bv 32 := 0x013e0f33.
Lemma F_7a474 : fetch_word Plain.M.loaded_segments (0x7a4cc : word) = Some W_7a474.
Proof. vm_refl. Qed.
Lemma D_7a474 : decode_any W_7a474 = Some (Op ALU_ADD 30 28 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a478 : bv 32 := 0x01ae0d33.
Lemma F_7a478 : fetch_word Plain.M.loaded_segments (0x7a4d0 : word) = Some W_7a478.
Proof. vm_refl. Qed.
Lemma D_7a478 : decode_any W_7a478 = Some (Op ALU_ADD 26 28 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a47c : bv 32 := 0x007ffa63.
Lemma F_7a47c : fetch_word Plain.M.loaded_segments (0x7a4d4 : word) = Some W_7a47c.
Proof. vm_refl. Qed.
Lemma D_7a47c : decode_any W_7a47c = Some (Branch BC_GEU 31 7 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a480 : bv 32 := 0x00000e13.
Lemma F_7a480 : fetch_word Plain.M.loaded_segments (0x7a4d8 : word) = Some W_7a480.
Proof. vm_refl. Qed.
Lemma D_7a480 : decode_any W_7a480 = Some (OpImm ALU_ADD 28 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a484 : bv 32 := 0x00000e93.
Lemma F_7a484 : fetch_word Plain.M.loaded_segments (0x7a4dc : word) = Some W_7a484.
Proof. vm_refl. Qed.
Lemma D_7a484 : decode_any W_7a484 = Some (OpImm ALU_ADD 29 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a488 : bv 32 := 0x00000493.
Lemma F_7a488 : fetch_word Plain.M.loaded_segments (0x7a4e0 : word) = Some W_7a488.
Proof. vm_refl. Qed.
Lemma D_7a488 : decode_any W_7a488 = Some (OpImm ALU_ADD 9 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a48c : bv 32 := 0x0380006f.
Lemma F_7a48c : fetch_word Plain.M.loaded_segments (0x7a4e4 : word) = Some W_7a48c.
Proof. vm_refl. Qed.
Lemma D_7a48c : decode_any W_7a48c = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a490 : bv 32 := 0x005fde1b.
Lemma F_7a490 : fetch_word Plain.M.loaded_segments (0x7a4e8 : word) = Some W_7a490.
Proof. vm_refl. Qed.
Lemma D_7a490 : decode_any W_7a490 = Some (ShiftImm32 ALU_SRL 28 31 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a494 : bv 32 := 0x02ed83b3.
Lemma F_7a494 : fetch_word Plain.M.loaded_segments (0x7a4ec : word) = Some W_7a494.
Proof. vm_refl. Qed.
Lemma D_7a494 : decode_any W_7a494 = Some (Mul M_MUL 7 27 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a498 : bv 32 := 0x005f5e9b.
Lemma F_7a498 : fetch_word Plain.M.loaded_segments (0x7a4f0 : word) = Some W_7a498.
Proof. vm_refl. Qed.
Lemma D_7a498 : decode_any W_7a498 = Some (ShiftImm32 ALU_SRL 29 30 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a49c : bv 32 := 0x02db84b3.
Lemma F_7a49c : fetch_word Plain.M.loaded_segments (0x7a4f4 : word) = Some W_7a49c.
Proof. vm_refl. Qed.
Lemma D_7a49c : decode_any W_7a49c = Some (Mul M_MUL 9 23 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4a0 : bv 32 := 0x00239393.
Lemma F_7a4a0 : fetch_word Plain.M.loaded_segments (0x7a4f8 : word) = Some W_7a4a0.
Proof. vm_refl. Qed.
Lemma D_7a4a0 : decode_any W_7a4a0 = Some (ShiftImm ALU_SLL 7 7 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4a4 : bv 32 := 0x002e9e93.
Lemma F_7a4a4 : fetch_word Plain.M.loaded_segments (0x7a4fc : word) = Some W_7a4a4.
Proof. vm_refl. Qed.
Lemma D_7a4a4 : decode_any W_7a4a4 = Some (ShiftImm ALU_SLL 29 29 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4a8 : bv 32 := 0x007283b3.
Lemma F_7a4a8 : fetch_word Plain.M.loaded_segments (0x7a500 : word) = Some W_7a4a8.
Proof. vm_refl. Qed.
Lemma D_7a4a8 : decode_any W_7a4a8 = Some (Op ALU_ADD 7 5 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4ac : bv 32 := 0x01d38eb3.
Lemma F_7a4ac : fetch_word Plain.M.loaded_segments (0x7a504 : word) = Some W_7a4ac.
Proof. vm_refl. Qed.
Lemma D_7a4ac : decode_any W_7a4ac = Some (Op ALU_ADD 29 7 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4b0 : bv 32 := 0x005d539b.
Lemma F_7a4b0 : fetch_word Plain.M.loaded_segments (0x7a508 : word) = Some W_7a4b0.
Proof. vm_refl. Qed.
Lemma D_7a4b0 : decode_any W_7a4b0 = Some (ShiftImm32 ALU_SRL 7 26 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4b4 : bv 32 := 0x00249493.
Lemma F_7a4b4 : fetch_word Plain.M.loaded_segments (0x7a50c : word) = Some W_7a4b4.
Proof. vm_refl. Qed.
Lemma D_7a4b4 : decode_any W_7a4b4 = Some (ShiftImm ALU_SLL 9 9 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4b8 : bv 32 := 0x00239393.
Lemma F_7a4b8 : fetch_word Plain.M.loaded_segments (0x7a510 : word) = Some W_7a4b8.
Proof. vm_refl. Qed.
Lemma D_7a4b8 : decode_any W_7a4b8 = Some (ShiftImm ALU_SLL 7 7 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4bc : bv 32 := 0x009b04b3.
Lemma F_7a4bc : fetch_word Plain.M.loaded_segments (0x7a514 : word) = Some W_7a4bc.
Proof. vm_refl. Qed.
Lemma D_7a4bc : decode_any W_7a4bc = Some (Op ALU_ADD 9 22 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4c0 : bv 32 := 0x007484b3.
Lemma F_7a4c0 : fetch_word Plain.M.loaded_segments (0x7a518 : word) = Some W_7a4c0.
Proof. vm_refl. Qed.
Lemma D_7a4c0 : decode_any W_7a4c0 = Some (Op ALU_ADD 9 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4c4 : bv 32 := 0x01330333.
Lemma F_7a4c4 : fetch_word Plain.M.loaded_segments (0x7a51c : word) = Some W_7a4c4.
Proof. vm_refl. Qed.
Lemma D_7a4c4 : decode_any W_7a4c4 = Some (Op ALU_ADD 6 6 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4c8 : bv 32 := 0x01f37393.
Lemma F_7a4c8 : fetch_word Plain.M.loaded_segments (0x7a520 : word) = Some W_7a4c8.
Proof. vm_refl. Qed.
Lemma D_7a4c8 : decode_any W_7a4c8 = Some (OpImm ALU_AND 7 6 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4cc : bv 32 := 0x020fb993.
Lemma F_7a4cc : fetch_word Plain.M.loaded_segments (0x7a524 : word) = Some W_7a4cc.
Proof. vm_refl. Qed.
Lemma D_7a4cc : decode_any W_7a4cc = Some (OpImm ALU_SLTU 19 31 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4d0 : bv 32 := 0x06038663.
Lemma F_7a4d0 : fetch_word Plain.M.loaded_segments (0x7a528 : word) = Some W_7a4d0.
Proof. vm_refl. Qed.
Lemma D_7a4d0 : decode_any W_7a4d0 = Some (Branch BC_EQ 7 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4d4 : bv 32 := 0x00013023.
Lemma F_7a4d4 : fetch_word Plain.M.loaded_segments (0x7a52c : word) = Some W_7a4d4.
Proof. vm_refl. Qed.
Lemma D_7a4d4 : decode_any W_7a4d4 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4d8 : bv 32 := 0x00239313.
Lemma F_7a4d8 : fetch_word Plain.M.loaded_segments (0x7a530 : word) = Some W_7a4d8.
Proof. vm_refl. Qed.
Lemma D_7a4d8 : decode_any W_7a4d8 = Some (ShiftImm ALU_SLL 6 7 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4dc : bv 32 := 0xfffa5f97.
Lemma F_7a4dc : fetch_word Plain.M.loaded_segments (0x7a534 : word) = Some W_7a4dc.
Proof. vm_refl. Qed.
Lemma D_7a4dc : decode_any W_7a4dc = Some (Auipc 31 1048485, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4e0 : bv 32 := 0xef0f8f93.
Lemma F_7a4e0 : fetch_word Plain.M.loaded_segments (0x7a538 : word) = Some W_7a4e0.
Proof. vm_refl. Qed.
Lemma D_7a4e0 : decode_any W_7a4e0 = Some (OpImm ALU_ADD 31 31 3824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4e4 : bv 32 := 0x006f8333.
Lemma F_7a4e4 : fetch_word Plain.M.loaded_segments (0x7a53c : word) = Some W_7a4e4.
Proof. vm_refl. Qed.
Lemma D_7a4e4 : decode_any W_7a4e4 = Some (Op ALU_ADD 6 31 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4e8 : bv 32 := 0x02ed8fb3.
Lemma F_7a4e8 : fetch_word Plain.M.loaded_segments (0x7a540 : word) = Some W_7a4e8.
Proof. vm_refl. Qed.
Lemma D_7a4e8 : decode_any W_7a4e8 = Some (Mul M_MUL 31 27 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4ec : bv 32 := 0x005f5f1b.
Lemma F_7a4ec : fetch_word Plain.M.loaded_segments (0x7a544 : word) = Some W_7a4ec.
Proof. vm_refl. Qed.
Lemma D_7a4ec : decode_any W_7a4ec = Some (ShiftImm32 ALU_SRL 30 30 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4f0 : bv 32 := 0x002f9f93.
Lemma F_7a4f0 : fetch_word Plain.M.loaded_segments (0x7a548 : word) = Some W_7a4f0.
Proof. vm_refl. Qed.
Lemma D_7a4f0 : decode_any W_7a4f0 = Some (ShiftImm ALU_SLL 31 31 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4f4 : bv 32 := 0x01f282b3.
Lemma F_7a4f4 : fetch_word Plain.M.loaded_segments (0x7a54c : word) = Some W_7a4f4.
Proof. vm_refl. Qed.
Lemma D_7a4f4 : decode_any W_7a4f4 = Some (Op ALU_ADD 5 5 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4f8 : bv 32 := 0x002e1f93.
Lemma F_7a4f8 : fetch_word Plain.M.loaded_segments (0x7a550 : word) = Some W_7a4f8.
Proof. vm_refl. Qed.
Lemma D_7a4f8 : decode_any W_7a4f8 = Some (ShiftImm ALU_SLL 31 28 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a4fc : bv 32 := 0x02db8bb3.
Lemma F_7a4fc : fetch_word Plain.M.loaded_segments (0x7a554 : word) = Some W_7a4fc.
Proof. vm_refl. Qed.
Lemma D_7a4fc : decode_any W_7a4fc = Some (Mul M_MUL 23 23 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a500 : bv 32 := 0x005d5d1b.
Lemma F_7a500 : fetch_word Plain.M.loaded_segments (0x7a558 : word) = Some W_7a500.
Proof. vm_refl. Qed.
Lemma D_7a500 : decode_any W_7a500 = Some (ShiftImm32 ALU_SRL 26 26 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a504 : bv 32 := 0x002f1f13.
Lemma F_7a504 : fetch_word Plain.M.loaded_segments (0x7a55c : word) = Some W_7a504.
Proof. vm_refl. Qed.
Lemma D_7a504 : decode_any W_7a504 = Some (ShiftImm ALU_SLL 30 30 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a508 : bv 32 := 0x002b9b93.
Lemma F_7a508 : fetch_word Plain.M.loaded_segments (0x7a560 : word) = Some W_7a508.
Proof. vm_refl. Qed.
Lemma D_7a508 : decode_any W_7a508 = Some (ShiftImm ALU_SLL 23 23 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a50c : bv 32 := 0x002d1d13.
Lemma F_7a50c : fetch_word Plain.M.loaded_segments (0x7a564 : word) = Some W_7a50c.
Proof. vm_refl. Qed.
Lemma D_7a50c : decode_any W_7a50c = Some (ShiftImm ALU_SLL 26 26 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a510 : bv 32 := 0x017b0b33.
Lemma F_7a510 : fetch_word Plain.M.loaded_segments (0x7a568 : word) = Some W_7a510.
Proof. vm_refl. Qed.
Lemma D_7a510 : decode_any W_7a510 = Some (Op ALU_ADD 22 22 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a514 : bv 32 := 0x00032303.
Lemma F_7a514 : fetch_word Plain.M.loaded_segments (0x7a56c : word) = Some W_7a514.
Proof. vm_refl. Qed.
Lemma D_7a514 : decode_any W_7a514 = Some (Load SZ4 true 6 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a518 : bv 32 := 0x01e282b3.
Lemma F_7a518 : fetch_word Plain.M.loaded_segments (0x7a570 : word) = Some W_7a518.
Proof. vm_refl. Qed.
Lemma D_7a518 : decode_any W_7a518 = Some (Op ALU_ADD 5 5 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a51c : bv 32 := 0x01ab0b33.
Lemma F_7a51c : fetch_word Plain.M.loaded_segments (0x7a574 : word) = Some W_7a51c.
Proof. vm_refl. Qed.
Lemma D_7a51c : decode_any W_7a51c = Some (Op ALU_ADD 22 22 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a520 : bv 32 := 0x01f282b3.
Lemma F_7a520 : fetch_word Plain.M.loaded_segments (0x7a578 : word) = Some W_7a520.
Proof. vm_refl. Qed.
Lemma D_7a520 : decode_any W_7a520 = Some (Op ALU_ADD 5 5 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a524 : bv 32 := 0x01fb0d33.
Lemma F_7a524 : fetch_word Plain.M.loaded_segments (0x7a57c : word) = Some W_7a524.
Proof. vm_refl. Qed.
Lemma D_7a524 : decode_any W_7a524 = Some (Op ALU_ADD 26 22 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a528 : bv 32 := 0x007823b3.
Lemma F_7a528 : fetch_word Plain.M.loaded_segments (0x7a580 : word) = Some W_7a528.
Proof. vm_refl. Qed.
Lemma D_7a528 : decode_any W_7a528 = Some (Op ALU_SLT 7 16 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a52c : bv 32 := 0x0013cf13.
Lemma F_7a52c : fetch_word Plain.M.loaded_segments (0x7a584 : word) = Some W_7a52c.
Proof. vm_refl. Qed.
Lemma D_7a52c : decode_any W_7a52c = Some (OpImm ALU_XOR 30 7 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a530 : bv 32 := 0x00d00393.
Lemma F_7a530 : fetch_word Plain.M.loaded_segments (0x7a588 : word) = Some W_7a530.
Proof. vm_refl. Qed.
Lemma D_7a530 : decode_any W_7a530 = Some (OpImm ALU_ADD 7 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a534 : bv 32 := 0x0353f063.
Lemma F_7a534 : fetch_word Plain.M.loaded_segments (0x7a58c : word) = Some W_7a534.
Proof. vm_refl. Qed.
Lemma D_7a534 : decode_any W_7a534 = Some (Branch BC_GEU 7 21 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a53c : bv 32 := 0x00000293.
Lemma F_7a53c : fetch_word Plain.M.loaded_segments (0x7a594 : word) = Some W_7a53c.
Proof. vm_refl. Qed.
Lemma D_7a53c : decode_any W_7a53c = Some (OpImm ALU_ADD 5 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a540 : bv 32 := 0x00000d13.
Lemma F_7a540 : fetch_word Plain.M.loaded_segments (0x7a598 : word) = Some W_7a540.
Proof. vm_refl. Qed.
Lemma D_7a540 : decode_any W_7a540 = Some (OpImm ALU_ADD 26 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a544 : bv 32 := 0x00100313.
Lemma F_7a544 : fetch_word Plain.M.loaded_segments (0x7a59c : word) = Some W_7a544.
Proof. vm_refl. Qed.
Lemma D_7a544 : decode_any W_7a544 = Some (OpImm ALU_ADD 6 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a548 : bv 32 := 0x00613023.
Lemma F_7a548 : fetch_word Plain.M.loaded_segments (0x7a5a0 : word) = Some W_7a548.
Proof. vm_refl. Qed.
Lemma D_7a548 : decode_any W_7a548 = Some (Store SZ8 2 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a54c : bv 32 := 0x00d00393.
Lemma F_7a54c : fetch_word Plain.M.loaded_segments (0x7a5a4 : word) = Some W_7a54c.
Proof. vm_refl. Qed.
Lemma D_7a54c : decode_any W_7a54c = Some (OpImm ALU_ADD 7 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a550 : bv 32 := 0x1953ea63.
Lemma F_7a550 : fetch_word Plain.M.loaded_segments (0x7a5a8 : word) = Some W_7a550.
Proof. vm_refl. Qed.
Lemma D_7a550 : decode_any W_7a550 = Some (Branch BC_LTU 7 21 404, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a554 : bv 32 := 0x002a9a93.
Lemma F_7a554 : fetch_word Plain.M.loaded_segments (0x7a5ac : word) = Some W_7a554.
Proof. vm_refl. Qed.
Lemma D_7a554 : decode_any W_7a554 = Some (ShiftImm ALU_SLL 21 21 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a558 : bv 32 := 0xfffa5397.
Lemma F_7a558 : fetch_word Plain.M.loaded_segments (0x7a5b0 : word) = Some W_7a558.
Proof. vm_refl. Qed.
Lemma D_7a558 : decode_any W_7a558 = Some (Auipc 7 1048485, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a55c : bv 32 := 0xd4838393.
Lemma F_7a55c : fetch_word Plain.M.loaded_segments (0x7a5b4 : word) = Some W_7a55c.
Proof. vm_refl. Qed.
Lemma D_7a55c : decode_any W_7a55c = Some (OpImm ALU_ADD 7 7 3400, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a560 : bv 32 := 0x007a8ab3.
Lemma F_7a560 : fetch_word Plain.M.loaded_segments (0x7a5b8 : word) = Some W_7a560.
Proof. vm_refl. Qed.
Lemma D_7a560 : decode_any W_7a560 = Some (Op ALU_ADD 21 21 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a564 : bv 32 := 0x000aaf83.
Lemma F_7a564 : fetch_word Plain.M.loaded_segments (0x7a5bc : word) = Some W_7a564.
Proof. vm_refl. Qed.
Lemma D_7a564 : decode_any W_7a564 = Some (Load SZ4 true 31 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a568 : bv 32 := 0x007f83b3.
Lemma F_7a568 : fetch_word Plain.M.loaded_segments (0x7a5c0 : word) = Some W_7a568.
Proof. vm_refl. Qed.
Lemma D_7a568 : decode_any W_7a568 = Some (Op ALU_ADD 7 31 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a56c : bv 32 := 0x00038067.
Lemma F_7a56c : fetch_word Plain.M.loaded_segments (0x7a5c4 : word) = Some W_7a56c.
Proof. vm_refl. Qed.
Lemma D_7a56c : decode_any W_7a56c = Some (Jalr 0 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ad84 : bv 32 := 0x00000513.
Lemma F_7ad84 : fetch_word Plain.M.loaded_segments (0x7addc : word) = Some W_7ad84.
Proof. vm_refl. Qed.
Lemma D_7ad84 : decode_any W_7ad84 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ad88 : bv 32 := 0xfff3c593.
Lemma F_7ad88 : fetch_word Plain.M.loaded_segments (0x7ade0 : word) = Some W_7ad88.
Proof. vm_refl. Qed.
Lemma D_7ad88 : decode_any W_7ad88 = Some (OpImm ALU_XOR 11 7 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ad8c : bv 32 := 0x01df0fb3.
Lemma F_7ad8c : fetch_word Plain.M.loaded_segments (0x7ade4 : word) = Some W_7ad8c.
Proof. vm_refl. Qed.
Lemma D_7ad8c : decode_any W_7ad8c = Some (Op ALU_ADD 31 30 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ad90 : bv 32 := 0x00271e93.
Lemma F_7ad90 : fetch_word Plain.M.loaded_segments (0x7ade8 : word) = Some W_7ad90.
Proof. vm_refl. Qed.
Lemma D_7ad90 : decode_any W_7ad90 = Some (ShiftImm ALU_SLL 29 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ad94 : bv 32 := 0x00269f13.
Lemma F_7ad94 : fetch_word Plain.M.loaded_segments (0x7adec : word) = Some W_7ad94.
Proof. vm_refl. Qed.
Lemma D_7ad94 : decode_any W_7ad94 = Some (ShiftImm ALU_SLL 30 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ad98 : bv 32 := 0xfffe0e13.
Lemma F_7ad98 : fetch_word Plain.M.loaded_segments (0x7adf0 : word) = Some W_7ad98.
Proof. vm_refl. Qed.
Lemma D_7ad98 : decode_any W_7ad98 = Some (OpImm ALU_ADD 28 28 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ad9c : bv 32 := 0x01f282b3.
Lemma F_7ad9c : fetch_word Plain.M.loaded_segments (0x7adf4 : word) = Some W_7ad9c.
Proof. vm_refl. Qed.
Lemma D_7ad9c : decode_any W_7ad9c = Some (Op ALU_ADD 5 5 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ada0 : bv 32 := 0x020e1e13.
Lemma F_7ada0 : fetch_word Plain.M.loaded_segments (0x7adf8 : word) = Some W_7ada0.
Proof. vm_refl. Qed.
Lemma D_7ada0 : decode_any W_7ada0 = Some (ShiftImm ALU_SLL 28 28 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ada4 : bv 32 := 0x01ee5e13.
Lemma F_7ada4 : fetch_word Plain.M.loaded_segments (0x7adfc : word) = Some W_7ada4.
Proof. vm_refl. Qed.
Lemma D_7ada4 : decode_any W_7ada4 = Some (ShiftImm ALU_SRL 28 28 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ada8 : bv 32 := 0x004e0e13.
Lemma F_7ada8 : fetch_word Plain.M.loaded_segments (0x7ae00 : word) = Some W_7ada8.
Proof. vm_refl. Qed.
Lemma D_7ada8 : decode_any W_7ada8 = Some (OpImm ALU_ADD 28 28 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7adac : bv 32 := 0x02000f93.
Lemma F_7adac : fetch_word Plain.M.loaded_segments (0x7ae04 : word) = Some W_7adac.
Proof. vm_refl. Qed.
Lemma D_7adac : decode_any W_7adac = Some (OpImm ALU_ADD 31 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7adb0 : bv 32 := 0x00080413.
Lemma F_7adb0 : fetch_word Plain.M.loaded_segments (0x7ae08 : word) = Some W_7adb0.
Proof. vm_refl. Qed.
Lemma D_7adb0 : decode_any W_7adb0 = Some (OpImm ALU_ADD 8 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7adb4 : bv 32 := 0x04c0006f.
Lemma F_7adb4 : fetch_word Plain.M.loaded_segments (0x7ae0c : word) = Some W_7adb4.
Proof. vm_refl. Qed.
Lemma D_7adb4 : decode_any W_7adb4 = Some (Jal 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7adb8 : bv 32 := 0x02d504b3.
Lemma F_7adb8 : fetch_word Plain.M.loaded_segments (0x7ae10 : word) = Some W_7adb8.
Proof. vm_refl. Qed.
Lemma D_7adb8 : decode_any W_7adb8 = Some (Mul M_MUL 9 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7adbc : bv 32 := 0x02e50933.
Lemma F_7adbc : fetch_word Plain.M.loaded_segments (0x7ae14 : word) = Some W_7adbc.
Proof. vm_refl. Qed.
Lemma D_7adbc : decode_any W_7adbc = Some (Mul M_MUL 18 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7adc0 : bv 32 := 0x00249493.
Lemma F_7adc0 : fetch_word Plain.M.loaded_segments (0x7ae18 : word) = Some W_7adc0.
Proof. vm_refl. Qed.
Lemma D_7adc0 : decode_any W_7adc0 = Some (ShiftImm ALU_SLL 9 9 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7adc4 : bv 32 := 0x00291993.
Lemma F_7adc4 : fetch_word Plain.M.loaded_segments (0x7ae1c : word) = Some W_7adc4.
Proof. vm_refl. Qed.
Lemma D_7adc4 : decode_any W_7adc4 = Some (ShiftImm ALU_SLL 19 18 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7adc8 : bv 32 := 0x00980933.
Lemma F_7adc8 : fetch_word Plain.M.loaded_segments (0x7ae20 : word) = Some W_7adc8.
Proof. vm_refl. Qed.
Lemma D_7adc8 : decode_any W_7adc8 = Some (Op ALU_ADD 18 16 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7adcc : bv 32 := 0x013884b3.
Lemma F_7adcc : fetch_word Plain.M.loaded_segments (0x7ae24 : word) = Some W_7adcc.
Proof. vm_refl. Qed.
Lemma D_7adcc : decode_any W_7adcc = Some (Op ALU_ADD 9 17 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7add0 : bv 32 := 0x00078e63.
Lemma F_7add0 : fetch_word Plain.M.loaded_segments (0x7ae28 : word) = Some W_7add0.
Proof. vm_refl. Qed.
Lemma D_7add0 : decode_any W_7add0 = Some (Branch BC_EQ 15 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7add4 : bv 32 := 0x0004a983.
Lemma F_7add4 : fetch_word Plain.M.loaded_segments (0x7ae2c : word) = Some W_7add4.
Proof. vm_refl. Qed.
Lemma D_7add4 : decode_any W_7add4 = Some (Load SZ4 true 19 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7add8 : bv 32 := 0x00092903.
Lemma F_7add8 : fetch_word Plain.M.loaded_segments (0x7ae30 : word) = Some W_7add8.
Proof. vm_refl. Qed.
Lemma D_7add8 : decode_any W_7add8 = Some (Load SZ4 true 18 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7addc : bv 32 := 0x00b9f9b3.
Lemma F_7addc : fetch_word Plain.M.loaded_segments (0x7ae34 : word) = Some W_7addc.
Proof. vm_refl. Qed.
Lemma D_7addc : decode_any W_7addc = Some (Op ALU_AND 19 19 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ade0 : bv 32 := 0x00797933.
Lemma F_7ade0 : fetch_word Plain.M.loaded_segments (0x7ae38 : word) = Some W_7ade0.
Proof. vm_refl. Qed.
Lemma D_7ade0 : decode_any W_7ade0 = Some (Op ALU_AND 18 18 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ade4 : bv 32 := 0x01396933.
Lemma F_7ade4 : fetch_word Plain.M.loaded_segments (0x7ae3c : word) = Some W_7ade4.
Proof. vm_refl. Qed.
Lemma D_7ade4 : decode_any W_7ade4 = Some (Op ALU_OR 18 18 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ade8 : bv 32 := 0x0124a023.
Lemma F_7ade8 : fetch_word Plain.M.loaded_segments (0x7ae40 : word) = Some W_7ade8.
Proof. vm_refl. Qed.
Lemma D_7ade8 : decode_any W_7ade8 = Some (Store SZ4 9 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7adec : bv 32 := 0x00150513.
Lemma F_7adec : fetch_word Plain.M.loaded_segments (0x7ae44 : word) = Some W_7adec.
Proof. vm_refl. Qed.
Lemma D_7adec : decode_any W_7adec = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7adf0 : bv 32 := 0x01d282b3.
Lemma F_7adf0 : fetch_word Plain.M.loaded_segments (0x7ae48 : word) = Some W_7adf0.
Proof. vm_refl. Qed.
Lemma D_7adf0 : decode_any W_7adf0 = Some (Op ALU_ADD 5 5 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7adf4 : bv 32 := 0x01e40433.
Lemma F_7adf4 : fetch_word Plain.M.loaded_segments (0x7ae4c : word) = Some W_7adf4.
Proof. vm_refl. Qed.
Lemma D_7adf4 : decode_any W_7adf4 = Some (Op ALU_ADD 8 8 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7adf8 : bv 32 := 0x00c51463.
Lemma F_7adf8 : fetch_word Plain.M.loaded_segments (0x7ae50 : word) = Some W_7adf8.
Proof. vm_refl. Qed.
Lemma D_7adf8 : decode_any W_7adf8 = Some (Branch BC_NE 10 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7adfc : bv 32 := 0x0f40106f.
Lemma F_7adfc : fetch_word Plain.M.loaded_segments (0x7ae54 : word) = Some W_7adfc.
Proof. vm_refl. Qed.
Lemma D_7adfc : decode_any W_7adfc = Some (Jal 0 4340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ae00 : bv 32 := 0xfbf36ce3.
Lemma F_7ae00 : fetch_word Plain.M.loaded_segments (0x7ae58 : word) = Some W_7ae00.
Proof. vm_refl. Qed.
Lemma D_7ae00 : decode_any W_7ae00 = Some (Branch BC_LTU 6 31 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ae04 : bv 32 := 0x00000913.
Lemma F_7ae04 : fetch_word Plain.M.loaded_segments (0x7ae5c : word) = Some W_7ae04.
Proof. vm_refl. Qed.
Lemma D_7ae04 : decode_any W_7ae04 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ae08 : bv 32 := 0x012404b3.
Lemma F_7ae08 : fetch_word Plain.M.loaded_segments (0x7ae60 : word) = Some W_7ae08.
Proof. vm_refl. Qed.
Lemma D_7ae08 : decode_any W_7ae08 = Some (Op ALU_ADD 9 8 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ae0c : bv 32 := 0x0004a483.
Lemma F_7ae0c : fetch_word Plain.M.loaded_segments (0x7ae64 : word) = Some W_7ae0c.
Proof. vm_refl. Qed.
Lemma D_7ae0c : decode_any W_7ae0c = Some (Load SZ4 true 9 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ae10 : bv 32 := 0x012289b3.
Lemma F_7ae10 : fetch_word Plain.M.loaded_segments (0x7ae68 : word) = Some W_7ae10.
Proof. vm_refl. Qed.
Lemma D_7ae10 : decode_any W_7ae10 = Some (Op ALU_ADD 19 5 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ae14 : bv 32 := 0x00490913.
Lemma F_7ae14 : fetch_word Plain.M.loaded_segments (0x7ae6c : word) = Some W_7ae14.
Proof. vm_refl. Qed.
Lemma D_7ae14 : decode_any W_7ae14 = Some (OpImm ALU_ADD 18 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ae18 : bv 32 := 0x0099a023.
Lemma F_7ae18 : fetch_word Plain.M.loaded_segments (0x7ae70 : word) = Some W_7ae18.
Proof. vm_refl. Qed.
Lemma D_7ae18 : decode_any W_7ae18 = Some (Store SZ4 19 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ae1c : bv 32 := 0xffc916e3.
Lemma F_7ae1c : fetch_word Plain.M.loaded_segments (0x7ae74 : word) = Some W_7ae1c.
Proof. vm_refl. Qed.
Lemma D_7ae1c : decode_any W_7ae1c = Some (Branch BC_NE 18 28 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ae20 : bv 32 := 0x012284b3.
Lemma F_7ae20 : fetch_word Plain.M.loaded_segments (0x7ae78 : word) = Some W_7ae20.
Proof. vm_refl. Qed.
Lemma D_7ae20 : decode_any W_7ae20 = Some (Op ALU_ADD 9 5 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ae24 : bv 32 := 0x01240933.
Lemma F_7ae24 : fetch_word Plain.M.loaded_segments (0x7ae7c : word) = Some W_7ae24.
Proof. vm_refl. Qed.
Lemma D_7ae24 : decode_any W_7ae24 = Some (Op ALU_ADD 18 8 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ae28 : bv 32 := 0xfa0796e3.
Lemma F_7ae28 : fetch_word Plain.M.loaded_segments (0x7ae80 : word) = Some W_7ae28.
Proof. vm_refl. Qed.
Lemma D_7ae28 : decode_any W_7ae28 = Some (Branch BC_NE 15 0 8108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7ae2c : bv 32 := 0xfc1ff06f.
Lemma F_7ae2c : fetch_word Plain.M.loaded_segments (0x7ae84 : word) = Some W_7ae2c.
Proof. vm_refl. Qed.
Lemma D_7ae2c : decode_any W_7ae2c = Some (Jal 0 2097088, 4%Z).
Proof. vm_refl. Qed.

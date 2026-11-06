(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.H Require GcFlushS15.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.grayquant_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_17234 : bv 32 := 0x06c5a02f.
Lemma F_17234 : fetch_word Plain.M.loaded_segments (0x1728c : word) = Some W_17234.
Proof. vm_refl. Qed.
Lemma D_17234 : decode_any W_17234 = Some (Amo AMO_ADD AW true true 0 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17238 : bv 32 := 0x00008067.
Lemma F_17238 : fetch_word Plain.M.loaded_segments (0x17290 : word) = Some W_17238.
Proof. vm_refl. Qed.
Lemma D_17238 : decode_any W_17238 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_198b8 : bv 32 := 0x09405263.
Lemma F_198b8 : fetch_word Plain.M.loaded_segments (0x19910 : word) = Some W_198b8.
Proof. vm_refl. Qed.
Lemma D_198b8 : decode_any W_198b8 = Some (Branch BC_GE 0 20 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_198bc : bv 32 := 0x06813583.
Lemma F_198bc : fetch_word Plain.M.loaded_segments (0x19914 : word) = Some W_198bc.
Proof. vm_refl. Qed.
Lemma D_198bc : decode_any W_198bc = Some (Load SZ8 true 11 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_198c0 : bv 32 := 0x06013603.
Lemma F_198c0 : fetch_word Plain.M.loaded_segments (0x19918 : word) = Some W_198c0.
Proof. vm_refl. Qed.
Lemma D_198c0 : decode_any W_198c0 = Some (Load SZ8 true 12 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_198c4 : bv 32 := 0x05813683.
Lemma F_198c4 : fetch_word Plain.M.loaded_segments (0x1991c : word) = Some W_198c4.
Proof. vm_refl. Qed.
Lemma D_198c4 : decode_any W_198c4 = Some (Load SZ8 true 13 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_198c8 : bv 32 := 0x002a1713.
Lemma F_198c8 : fetch_word Plain.M.loaded_segments (0x19920 : word) = Some W_198c8.
Proof. vm_refl. Qed.
Lemma D_198c8 : decode_any W_198c8 = Some (ShiftImm ALU_SLL 14 20 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_198cc : bv 32 := 0xffff8797.
Lemma F_198cc : fetch_word Plain.M.loaded_segments (0x19924 : word) = Some W_198cc.
Proof. vm_refl. Qed.
Lemma D_198cc : decode_any W_198cc = Some (Auipc 15 1048568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_198d0 : bv 32 := 0xdd87a787.
Lemma F_198d0 : fetch_word Plain.M.loaded_segments (0x19928 : word) = Some W_198d0.
Proof. vm_refl. Qed.
Lemma D_198d0 : decode_any W_198d0 = Some (FLoad FMT_S 15 15 3544, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_198d4 : bv 32 := 0xffff8797.
Lemma F_198d4 : fetch_word Plain.M.loaded_segments (0x1992c : word) = Some W_198d4.
Proof. vm_refl. Qed.
Lemma D_198d4 : decode_any W_198d4 = Some (Auipc 15 1048568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_198d8 : bv 32 := 0xdc87a707.
Lemma F_198d8 : fetch_word Plain.M.loaded_segments (0x19930 : word) = Some W_198d8.
Proof. vm_refl. Qed.
Lemma D_198d8 : decode_any W_198d8 = Some (FLoad FMT_S 14 15 3528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_198dc : bv 32 := 0xffff8797.
Lemma F_198dc : fetch_word Plain.M.loaded_segments (0x19934 : word) = Some W_198dc.
Proof. vm_refl. Qed.
Lemma D_198dc : decode_any W_198dc = Some (Auipc 15 1048568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_198e0 : bv 32 := 0xcec7b687.
Lemma F_198e0 : fetch_word Plain.M.loaded_segments (0x19938 : word) = Some W_198e0.
Proof. vm_refl. Qed.
Lemma D_198e0 : decode_any W_198e0 = Some (FLoad FMT_D 13 15 3308, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_198e4 : bv 32 := 0x00e50733.
Lemma F_198e4 : fetch_word Plain.M.loaded_segments (0x1993c : word) = Some W_198e4.
Proof. vm_refl. Qed.
Lemma D_198e4 : decode_any W_198e4 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_198e8 : bv 32 := 0x3f0007b7.
Lemma F_198e8 : fetch_word Plain.M.loaded_segments (0x19940 : word) = Some W_198e8.
Proof. vm_refl. Qed.
Lemma D_198e8 : decode_any W_198e8 = Some (Lui 15 258048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_198ec : bv 32 := 0xf0078653.
Lemma F_198ec : fetch_word Plain.M.loaded_segments (0x19944 : word) = Some W_198ec.
Proof. vm_refl. Qed.
Lemma D_198ec : decode_any W_198ec = Some (Fmv FMV_F_X FMT_S 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_198f0 : bv 32 := 0x00050793.
Lemma F_198f0 : fetch_word Plain.M.loaded_segments (0x19948 : word) = Some W_198f0.
Proof. vm_refl. Qed.
Lemma D_198f0 : decode_any W_198f0 = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_198f4 : bv 32 := 0x0005a803.
Lemma F_198f4 : fetch_word Plain.M.loaded_segments (0x1994c : word) = Some W_198f4.
Proof. vm_refl. Qed.
Lemma D_198f4 : decode_any W_198f4 = Some (Load SZ4 true 16 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_198f8 : bv 32 := 0x00062883.
Lemma F_198f8 : fetch_word Plain.M.loaded_segments (0x19950 : word) = Some W_198f8.
Proof. vm_refl. Qed.
Lemma D_198f8 : decode_any W_198f8 = Some (Load SZ4 true 17 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_198fc : bv 32 := 0xd00875d3.
Lemma F_198fc : fetch_word Plain.M.loaded_segments (0x19954 : word) = Some W_198fc.
Proof. vm_refl. Qed.
Lemma D_198fc : decode_any W_198fc = Some (Fcvt FC_S FC_W 11 16 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19900 : bv 32 := 0xd008f553.
Lemma F_19900 : fetch_word Plain.M.loaded_segments (0x19958 : word) = Some W_19900.
Proof. vm_refl. Qed.
Lemma D_19900 : decode_any W_19900 = Some (Fcvt FC_S FC_W 10 17 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19904 : bv 32 := 0x0006a803.
Lemma F_19904 : fetch_word Plain.M.loaded_segments (0x1995c : word) = Some W_19904.
Proof. vm_refl. Qed.
Lemma D_19904 : decode_any W_19904 = Some (Load SZ4 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19908 : bv 32 := 0x00468693.
Lemma F_19908 : fetch_word Plain.M.loaded_segments (0x19960 : word) = Some W_19908.
Proof. vm_refl. Qed.
Lemma D_19908 : decode_any W_19908 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1990c : bv 32 := 0x10c57553.
Lemma F_1990c : fetch_word Plain.M.loaded_segments (0x19964 : word) = Some W_1990c.
Proof. vm_refl. Qed.
Lemma D_1990c : decode_any W_1990c = Some (Fari F_MUL FMT_S 10 10 12 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19910 : bv 32 := 0x50f5f5c3.
Lemma F_19910 : fetch_word Plain.M.loaded_segments (0x19968 : word) = Some W_19910.
Proof. vm_refl. Qed.
Lemma D_19910 : decode_any W_19910 = Some (Fma F_MADD FMT_S 11 11 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19914 : bv 32 := 0xd0087553.
Lemma F_19914 : fetch_word Plain.M.loaded_segments (0x1996c : word) = Some W_19914.
Proof. vm_refl. Qed.
Lemma D_19914 : decode_any W_19914 = Some (Fcvt FC_S FC_W 10 16 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19918 : bv 32 := 0x58e575c3.
Lemma F_19918 : fetch_word Plain.M.loaded_segments (0x19970 : word) = Some W_19918.
Proof. vm_refl. Qed.
Lemma D_19918 : decode_any W_19918 = Some (Fma F_MADD FMT_S 11 10 14 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1991c : bv 32 := 0x420585d3.
Lemma F_1991c : fetch_word Plain.M.loaded_segments (0x19974 : word) = Some W_1991c.
Proof. vm_refl. Qed.
Lemma D_1991c : decode_any W_1991c = Some (Fcvt FC_D FC_S 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19920 : bv 32 := 0x02d5f5d3.
Lemma F_19920 : fetch_word Plain.M.loaded_segments (0x19978 : word) = Some W_19920.
Proof. vm_refl. Qed.
Lemma D_19920 : decode_any W_19920 = Some (Fari F_ADD FMT_D 11 11 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19924 : bv 32 := 0xc2159853.
Lemma F_19924 : fetch_word Plain.M.loaded_segments (0x1997c : word) = Some W_19924.
Proof. vm_refl. Qed.
Lemma D_19924 : decode_any W_19924 = Some (Fcvt FC_WU FC_D 16 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19928 : bv 32 := 0x0107a023.
Lemma F_19928 : fetch_word Plain.M.loaded_segments (0x19980 : word) = Some W_19928.
Proof. vm_refl. Qed.
Lemma D_19928 : decode_any W_19928 = Some (Store SZ4 15 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1992c : bv 32 := 0x00478793.
Lemma F_1992c : fetch_word Plain.M.loaded_segments (0x19984 : word) = Some W_1992c.
Proof. vm_refl. Qed.
Lemma D_1992c : decode_any W_1992c = Some (OpImm ALU_ADD 15 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19930 : bv 32 := 0x00460613.
Lemma F_19930 : fetch_word Plain.M.loaded_segments (0x19988 : word) = Some W_19930.
Proof. vm_refl. Qed.
Lemma D_19930 : decode_any W_19930 = Some (OpImm ALU_ADD 12 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19934 : bv 32 := 0x00458593.
Lemma F_19934 : fetch_word Plain.M.loaded_segments (0x1998c : word) = Some W_19934.
Proof. vm_refl. Qed.
Lemma D_19934 : decode_any W_19934 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19938 : bv 32 := 0xfae79ee3.
Lemma F_19938 : fetch_word Plain.M.loaded_segments (0x19990 : word) = Some W_19938.
Proof. vm_refl. Qed.
Lemma D_19938 : decode_any W_19938 = Some (Branch BC_NE 15 14 8124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19fdc : bv 32 := 0x00008067.
Lemma F_19fdc : fetch_word Plain.M.loaded_segments (0x1a034 : word) = Some W_19fdc.
Proof. vm_refl. Qed.
Lemma D_19fdc : decode_any W_19fdc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.


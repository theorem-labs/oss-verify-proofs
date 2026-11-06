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
Definition W_9b944 : bv 32 := 0xff010113.
Lemma F_9b944 : fetch_word Plain.M.loaded_segments (0x9b99c : word) = Some W_9b944.
Proof. vm_refl. Qed.
Lemma D_9b944 : decode_any W_9b944 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b948 : bv 32 := 0x00113423.
Lemma F_9b948 : fetch_word Plain.M.loaded_segments (0x9b9a0 : word) = Some W_9b948.
Proof. vm_refl. Qed.
Lemma D_9b948 : decode_any W_9b948 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b94c : bv 32 := 0x00813023.
Lemma F_9b94c : fetch_word Plain.M.loaded_segments (0x9b9a4 : word) = Some W_9b94c.
Proof. vm_refl. Qed.
Lemma D_9b94c : decode_any W_9b94c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b950 : bv 32 := 0x04050663.
Lemma F_9b950 : fetch_word Plain.M.loaded_segments (0x9b9a8 : word) = Some W_9b950.
Proof. vm_refl. Qed.
Lemma D_9b950 : decode_any W_9b950 = Some (Branch BC_EQ 10 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b954 : bv 32 := 0xf00007d3.
Lemma F_9b954 : fetch_word Plain.M.loaded_segments (0x9b9ac : word) = Some W_9b954.
Proof. vm_refl. Qed.
Lemma D_9b954 : decode_any W_9b954 = Some (Fmv FMV_F_X FMT_S 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b958 : bv 32 := 0xa0f52653.
Lemma F_9b958 : fetch_word Plain.M.loaded_segments (0x9b9b0 : word) = Some W_9b958.
Proof. vm_refl. Qed.
Lemma D_9b958 : decode_any W_9b958 = Some (Fcmp F_EQ FMT_S 12 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b95c : bv 32 := 0x00052023.
Lemma F_9b95c : fetch_word Plain.M.loaded_segments (0x9b9b4 : word) = Some W_9b95c.
Proof. vm_refl. Qed.
Lemma D_9b95c : decode_any W_9b95c = Some (Store SZ4 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b960 : bv 32 := 0x00061663.
Lemma F_9b960 : fetch_word Plain.M.loaded_segments (0x9b9b8 : word) = Some W_9b960.
Proof. vm_refl. Qed.
Lemma D_9b960 : decode_any W_9b960 = Some (Branch BC_NE 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b964 : bv 32 := 0xa0f5a653.
Lemma F_9b964 : fetch_word Plain.M.loaded_segments (0x9b9bc : word) = Some W_9b964.
Proof. vm_refl. Qed.
Lemma D_9b964 : decode_any W_9b964 = Some (Fcmp F_EQ FMT_S 12 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b968 : bv 32 := 0x08060063.
Lemma F_9b968 : fetch_word Plain.M.loaded_segments (0x9b9c0 : word) = Some W_9b968.
Proof. vm_refl. Qed.
Lemma D_9b968 : decode_any W_9b968 = Some (Branch BC_EQ 12 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b96c : bv 32 := 0x00077517.
Lemma F_9b96c : fetch_word Plain.M.loaded_segments (0x9b9c4 : word) = Some W_9b96c.
Proof. vm_refl. Qed.
Lemma D_9b96c : decode_any W_9b96c = Some (Auipc 10 119, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b970 : bv 32 := 0xc0453503.
Lemma F_9b970 : fetch_word Plain.M.loaded_segments (0x9b9c8 : word) = Some W_9b970.
Proof. vm_refl. Qed.
Lemma D_9b970 : decode_any W_9b970 = Some (Load SZ8 true 10 10 3076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b974 : bv 32 := 0x00052503.
Lemma F_9b974 : fetch_word Plain.M.loaded_segments (0x9b9cc : word) = Some W_9b974.
Proof. vm_refl. Qed.
Lemma D_9b974 : decode_any W_9b974 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b978 : bv 32 := 0x00300593.
Lemma F_9b978 : fetch_word Plain.M.loaded_segments (0x9b9d0 : word) = Some W_9b978.
Proof. vm_refl. Qed.
Lemma D_9b978 : decode_any W_9b978 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b97c : bv 32 := 0x00a5cc63.
Lemma F_9b97c : fetch_word Plain.M.loaded_segments (0x9b9d4 : word) = Some W_9b97c.
Proof. vm_refl. Qed.
Lemma D_9b97c : decode_any W_9b97c = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b980 : bv 32 := 0xfff80517.
Lemma F_9b980 : fetch_word Plain.M.loaded_segments (0x9b9d8 : word) = Some W_9b980.
Proof. vm_refl. Qed.
Lemma D_9b980 : decode_any W_9b980 = Some (Auipc 10 1048448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b984 : bv 32 := 0xfff7e597.
Lemma F_9b984 : fetch_word Plain.M.loaded_segments (0x9b9dc : word) = Some W_9b984.
Proof. vm_refl. Qed.
Lemma D_9b984 : decode_any W_9b984 = Some (Auipc 11 1048446, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b988 : bv 32 := 0xbc950513.
Lemma F_9b988 : fetch_word Plain.M.loaded_segments (0x9b9e0 : word) = Some W_9b988.
Proof. vm_refl. Qed.
Lemma D_9b988 : decode_any W_9b988 = Some (OpImm ALU_ADD 10 10 3017, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b98c : bv 32 := 0x2d658593.
Lemma F_9b98c : fetch_word Plain.M.loaded_segments (0x9b9e4 : word) = Some W_9b98c.
Proof. vm_refl. Qed.
Lemma D_9b98c : decode_any W_9b98c = Some (OpImm ALU_ADD 11 11 726, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b990 : bv 32 := 0xe98c70ef.
Lemma F_9b990 : fetch_word Plain.M.loaded_segments (0x9b9e8 : word) = Some W_9b990.
Proof. vm_refl. Qed.
Lemma D_9b990 : decode_any W_9b990 = Some (Jal 1 1865368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b994 : bv 32 := 0x00000513.
Lemma F_9b994 : fetch_word Plain.M.loaded_segments (0x9b9ec : word) = Some W_9b994.
Proof. vm_refl. Qed.
Lemma D_9b994 : decode_any W_9b994 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b998 : bv 32 := 0x0400006f.
Lemma F_9b998 : fetch_word Plain.M.loaded_segments (0x9b9f0 : word) = Some W_9b998.
Proof. vm_refl. Qed.
Lemma D_9b998 : decode_any W_9b998 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b9d8 : bv 32 := 0x00813083.
Lemma F_9b9d8 : fetch_word Plain.M.loaded_segments (0x9ba30 : word) = Some W_9b9d8.
Proof. vm_refl. Qed.
Lemma D_9b9d8 : decode_any W_9b9d8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b9dc : bv 32 := 0x00013403.
Lemma F_9b9dc : fetch_word Plain.M.loaded_segments (0x9ba34 : word) = Some W_9b9dc.
Proof. vm_refl. Qed.
Lemma D_9b9dc : decode_any W_9b9dc = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b9e0 : bv 32 := 0x01010113.
Lemma F_9b9e0 : fetch_word Plain.M.loaded_segments (0x9ba38 : word) = Some W_9b9e0.
Proof. vm_refl. Qed.
Lemma D_9b9e0 : decode_any W_9b9e0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b9e4 : bv 32 := 0x00008067.
Lemma F_9b9e4 : fetch_word Plain.M.loaded_segments (0x9ba3c : word) = Some W_9b9e4.
Proof. vm_refl. Qed.
Lemma D_9b9e4 : decode_any W_9b9e4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b9e8 : bv 32 := 0xa0f62653.
Lemma F_9b9e8 : fetch_word Plain.M.loaded_segments (0x9ba40 : word) = Some W_9b9e8.
Proof. vm_refl. Qed.
Lemma D_9b9e8 : decode_any W_9b9e8 = Some (Fcmp F_EQ FMT_S 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b9ec : bv 32 := 0x02061463.
Lemma F_9b9ec : fetch_word Plain.M.loaded_segments (0x9ba44 : word) = Some W_9b9ec.
Proof. vm_refl. Qed.
Lemma D_9b9ec : decode_any W_9b9ec = Some (Branch BC_NE 12 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b9f0 : bv 32 := 0xa0f6a653.
Lemma F_9b9f0 : fetch_word Plain.M.loaded_segments (0x9ba48 : word) = Some W_9b9f0.
Proof. vm_refl. Qed.
Lemma D_9b9f0 : decode_any W_9b9f0 = Some (Fcmp F_EQ FMT_S 12 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b9f4 : bv 32 := 0x02061863.
Lemma F_9b9f4 : fetch_word Plain.M.loaded_segments (0x9ba4c : word) = Some W_9b9f4.
Proof. vm_refl. Qed.
Lemma D_9b9f4 : decode_any W_9b9f4 = Some (Branch BC_NE 12 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b9f8 : bv 32 := 0xa0f51653.
Lemma F_9b9f8 : fetch_word Plain.M.loaded_segments (0x9ba50 : word) = Some W_9b9f8.
Proof. vm_refl. Qed.
Lemma D_9b9f8 : decode_any W_9b9f8 = Some (Fcmp F_LT FMT_S 12 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b9fc : bv 32 := 0x02061c63.
Lemma F_9b9fc : fetch_word Plain.M.loaded_segments (0x9ba54 : word) = Some W_9b9fc.
Proof. vm_refl. Qed.
Lemma D_9b9fc : decode_any W_9b9fc = Some (Branch BC_NE 12 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba00 : bv 32 := 0x20a50753.
Lemma F_9ba00 : fetch_word Plain.M.loaded_segments (0x9ba58 : word) = Some W_9ba00.
Proof. vm_refl. Qed.
Lemma D_9ba00 : decode_any W_9ba00 = Some (Fsgnj F_SGNJ FMT_S 14 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba04 : bv 32 := 0xa0f59653.
Lemma F_9ba04 : fetch_word Plain.M.loaded_segments (0x9ba5c : word) = Some W_9ba04.
Proof. vm_refl. Qed.
Lemma D_9ba04 : decode_any W_9ba04 = Some (Fcmp F_LT FMT_S 12 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba08 : bv 32 := 0x02060c63.
Lemma F_9ba08 : fetch_word Plain.M.loaded_segments (0x9ba60 : word) = Some W_9ba08.
Proof. vm_refl. Qed.
Lemma D_9ba08 : decode_any W_9ba08 = Some (Branch BC_EQ 12 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba0c : bv 32 := 0x20b597d3.
Lemma F_9ba0c : fetch_word Plain.M.loaded_segments (0x9ba64 : word) = Some W_9ba0c.
Proof. vm_refl. Qed.
Lemma D_9ba0c : decode_any W_9ba0c = Some (Fsgnj F_SGNJN FMT_S 15 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba10 : bv 32 := 0x0340006f.
Lemma F_9ba10 : fetch_word Plain.M.loaded_segments (0x9ba68 : word) = Some W_9ba10.
Proof. vm_refl. Qed.
Lemma D_9ba10 : decode_any W_9ba10 = Some (Jal 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba14 : bv 32 := 0x41000637.
Lemma F_9ba14 : fetch_word Plain.M.loaded_segments (0x9ba6c : word) = Some W_9ba14.
Proof. vm_refl. Qed.
Lemma D_9ba14 : decode_any W_9ba14 = Some (Lui 12 266240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba18 : bv 32 := 0xf0060653.
Lemma F_9ba18 : fetch_word Plain.M.loaded_segments (0x9ba70 : word) = Some W_9ba18.
Proof. vm_refl. Qed.
Lemma D_9ba18 : decode_any W_9ba18 = Some (Fmv FMV_F_X FMT_S 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba1c : bv 32 := 0xa0f6a653.
Lemma F_9ba1c : fetch_word Plain.M.loaded_segments (0x9ba74 : word) = Some W_9ba1c.
Proof. vm_refl. Qed.
Lemma D_9ba1c : decode_any W_9ba1c = Some (Fcmp F_EQ FMT_S 12 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba20 : bv 32 := 0xfc060ce3.
Lemma F_9ba20 : fetch_word Plain.M.loaded_segments (0x9ba78 : word) = Some W_9ba20.
Proof. vm_refl. Qed.
Lemma D_9ba20 : decode_any W_9ba20 = Some (Branch BC_EQ 12 0 8152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba24 : bv 32 := 0x40200637.
Lemma F_9ba24 : fetch_word Plain.M.loaded_segments (0x9ba7c : word) = Some W_9ba24.
Proof. vm_refl. Qed.
Lemma D_9ba24 : decode_any W_9ba24 = Some (Lui 12 262656, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba28 : bv 32 := 0xf00606d3.
Lemma F_9ba28 : fetch_word Plain.M.loaded_segments (0x9ba80 : word) = Some W_9ba28.
Proof. vm_refl. Qed.
Lemma D_9ba28 : decode_any W_9ba28 = Some (Fmv FMV_F_X FMT_S 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba2c : bv 32 := 0xa0f51653.
Lemma F_9ba2c : fetch_word Plain.M.loaded_segments (0x9ba84 : word) = Some W_9ba2c.
Proof. vm_refl. Qed.
Lemma D_9ba2c : decode_any W_9ba2c = Some (Fcmp F_LT FMT_S 12 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba30 : bv 32 := 0xfc0608e3.
Lemma F_9ba30 : fetch_word Plain.M.loaded_segments (0x9ba88 : word) = Some W_9ba30.
Proof. vm_refl. Qed.
Lemma D_9ba30 : decode_any W_9ba30 = Some (Branch BC_EQ 12 0 8144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba34 : bv 32 := 0x20a51753.
Lemma F_9ba34 : fetch_word Plain.M.loaded_segments (0x9ba8c : word) = Some W_9ba34.
Proof. vm_refl. Qed.
Lemma D_9ba34 : decode_any W_9ba34 = Some (Fsgnj F_SGNJN FMT_S 14 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba38 : bv 32 := 0xa0f59653.
Lemma F_9ba38 : fetch_word Plain.M.loaded_segments (0x9ba90 : word) = Some W_9ba38.
Proof. vm_refl. Qed.
Lemma D_9ba38 : decode_any W_9ba38 = Some (Fcmp F_LT FMT_S 12 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba3c : bv 32 := 0xfc0618e3.
Lemma F_9ba3c : fetch_word Plain.M.loaded_segments (0x9ba94 : word) = Some W_9ba3c.
Proof. vm_refl. Qed.
Lemma D_9ba3c : decode_any W_9ba3c = Some (Branch BC_NE 12 0 8144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba40 : bv 32 := 0x20b587d3.
Lemma F_9ba40 : fetch_word Plain.M.loaded_segments (0x9ba98 : word) = Some W_9ba40.
Proof. vm_refl. Qed.
Lemma D_9ba40 : decode_any W_9ba40 = Some (Fsgnj F_SGNJ FMT_S 15 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba44 : bv 32 := 0xa0a61653.
Lemma F_9ba44 : fetch_word Plain.M.loaded_segments (0x9ba9c : word) = Some W_9ba44.
Proof. vm_refl. Qed.
Lemma D_9ba44 : decode_any W_9ba44 = Some (Fcmp F_LT FMT_S 12 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba48 : bv 32 := 0x10d7f053.
Lemma F_9ba48 : fetch_word Plain.M.loaded_segments (0x9baa0 : word) = Some W_9ba48.
Proof. vm_refl. Qed.
Lemma D_9ba48 : decode_any W_9ba48 = Some (Fari F_MUL FMT_S 0 15 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba4c : bv 32 := 0x00060a63.
Lemma F_9ba4c : fetch_word Plain.M.loaded_segments (0x9baa4 : word) = Some W_9ba4c.
Proof. vm_refl. Qed.
Lemma D_9ba4c : decode_any W_9ba4c = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba50 : bv 32 := 0xa0e01653.
Lemma F_9ba50 : fetch_word Plain.M.loaded_segments (0x9baa8 : word) = Some W_9ba50.
Proof. vm_refl. Qed.
Lemma D_9ba50 : decode_any W_9ba50 = Some (Fcmp F_LT FMT_S 12 0 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba54 : bv 32 := 0x00060663.
Lemma F_9ba54 : fetch_word Plain.M.loaded_segments (0x9baac : word) = Some W_9ba54.
Proof. vm_refl. Qed.
Lemma D_9ba54 : decode_any W_9ba54 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba58 : bv 32 := 0x00100613.
Lemma F_9ba58 : fetch_word Plain.M.loaded_segments (0x9bab0 : word) = Some W_9ba58.
Proof. vm_refl. Qed.
Lemma D_9ba58 : decode_any W_9ba58 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba5c : bv 32 := 0x0500006f.
Lemma F_9ba5c : fetch_word Plain.M.loaded_segments (0x9bab4 : word) = Some W_9ba5c.
Proof. vm_refl. Qed.
Lemma D_9ba5c : decode_any W_9ba5c = Some (Jal 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba60 : bv 32 := 0xa0b61653.
Lemma F_9ba60 : fetch_word Plain.M.loaded_segments (0x9bab8 : word) = Some W_9ba60.
Proof. vm_refl. Qed.
Lemma D_9ba60 : decode_any W_9ba60 = Some (Fcmp F_LT FMT_S 12 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba64 : bv 32 := 0x10d776d3.
Lemma F_9ba64 : fetch_word Plain.M.loaded_segments (0x9babc : word) = Some W_9ba64.
Proof. vm_refl. Qed.
Lemma D_9ba64 : decode_any W_9ba64 = Some (Fari F_MUL FMT_S 13 14 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba68 : bv 32 := 0x00060a63.
Lemma F_9ba68 : fetch_word Plain.M.loaded_segments (0x9bac0 : word) = Some W_9ba68.
Proof. vm_refl. Qed.
Lemma D_9ba68 : decode_any W_9ba68 = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba6c : bv 32 := 0xa0f69653.
Lemma F_9ba6c : fetch_word Plain.M.loaded_segments (0x9bac4 : word) = Some W_9ba6c.
Proof. vm_refl. Qed.
Lemma D_9ba6c : decode_any W_9ba6c = Some (Fcmp F_LT FMT_S 12 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba70 : bv 32 := 0x00060663.
Lemma F_9ba70 : fetch_word Plain.M.loaded_segments (0x9bac8 : word) = Some W_9ba70.
Proof. vm_refl. Qed.
Lemma D_9ba70 : decode_any W_9ba70 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba74 : bv 32 := 0x00200613.
Lemma F_9ba74 : fetch_word Plain.M.loaded_segments (0x9bacc : word) = Some W_9ba74.
Proof. vm_refl. Qed.
Lemma D_9ba74 : decode_any W_9ba74 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba78 : bv 32 := 0x0340006f.
Lemma F_9ba78 : fetch_word Plain.M.loaded_segments (0x9bad0 : word) = Some W_9ba78.
Proof. vm_refl. Qed.
Lemma D_9ba78 : decode_any W_9ba78 = Some (Jal 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba7c : bv 32 := 0x20c61653.
Lemma F_9ba7c : fetch_word Plain.M.loaded_segments (0x9bad4 : word) = Some W_9ba7c.
Proof. vm_refl. Qed.
Lemma D_9ba7c : decode_any W_9ba7c = Some (Fsgnj F_SGNJN FMT_S 12 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba80 : bv 32 := 0xa0c51653.
Lemma F_9ba80 : fetch_word Plain.M.loaded_segments (0x9bad8 : word) = Some W_9ba80.
Proof. vm_refl. Qed.
Lemma D_9ba80 : decode_any W_9ba80 = Some (Fcmp F_LT FMT_S 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba84 : bv 32 := 0x00060a63.
Lemma F_9ba84 : fetch_word Plain.M.loaded_segments (0x9badc : word) = Some W_9ba84.
Proof. vm_refl. Qed.
Lemma D_9ba84 : decode_any W_9ba84 = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba88 : bv 32 := 0xa0e01653.
Lemma F_9ba88 : fetch_word Plain.M.loaded_segments (0x9bae0 : word) = Some W_9ba88.
Proof. vm_refl. Qed.
Lemma D_9ba88 : decode_any W_9ba88 = Some (Fcmp F_LT FMT_S 12 0 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba8c : bv 32 := 0x00060663.
Lemma F_9ba8c : fetch_word Plain.M.loaded_segments (0x9bae4 : word) = Some W_9ba8c.
Proof. vm_refl. Qed.
Lemma D_9ba8c : decode_any W_9ba8c = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba90 : bv 32 := 0x00300613.
Lemma F_9ba90 : fetch_word Plain.M.loaded_segments (0x9bae8 : word) = Some W_9ba90.
Proof. vm_refl. Qed.
Lemma D_9ba90 : decode_any W_9ba90 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba94 : bv 32 := 0x0180006f.
Lemma F_9ba94 : fetch_word Plain.M.loaded_segments (0x9baec : word) = Some W_9ba94.
Proof. vm_refl. Qed.
Lemma D_9ba94 : decode_any W_9ba94 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba98 : bv 32 := 0xa0c59653.
Lemma F_9ba98 : fetch_word Plain.M.loaded_segments (0x9baf0 : word) = Some W_9ba98.
Proof. vm_refl. Qed.
Lemma D_9ba98 : decode_any W_9ba98 = Some (Fcmp F_LT FMT_S 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba9c : bv 32 := 0x00060a63.
Lemma F_9ba9c : fetch_word Plain.M.loaded_segments (0x9baf4 : word) = Some W_9ba9c.
Proof. vm_refl. Qed.
Lemma D_9ba9c : decode_any W_9ba9c = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9baa0 : bv 32 := 0xa0f69653.
Lemma F_9baa0 : fetch_word Plain.M.loaded_segments (0x9baf8 : word) = Some W_9baa0.
Proof. vm_refl. Qed.
Lemma D_9baa0 : decode_any W_9baa0 = Some (Fcmp F_LT FMT_S 12 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9baa4 : bv 32 := 0x00060663.
Lemma F_9baa4 : fetch_word Plain.M.loaded_segments (0x9bafc : word) = Some W_9baa4.
Proof. vm_refl. Qed.
Lemma D_9baa4 : decode_any W_9baa4 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9baa8 : bv 32 := 0x00400613.
Lemma F_9baa8 : fetch_word Plain.M.loaded_segments (0x9bb00 : word) = Some W_9baa8.
Proof. vm_refl. Qed.
Lemma D_9baa8 : decode_any W_9baa8 = Some (OpImm ALU_ADD 12 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9baac : bv 32 := 0x00c52023.
Lemma F_9baac : fetch_word Plain.M.loaded_segments (0x9bb04 : word) = Some W_9baac.
Proof. vm_refl. Qed.
Lemma D_9baac : decode_any W_9baac = Some (Store SZ4 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bab0 : bv 32 := 0xee0582e3.
Lemma F_9bab0 : fetch_word Plain.M.loaded_segments (0x9bb08 : word) = Some W_9bab0.
Proof. vm_refl. Qed.
Lemma D_9bab0 : decode_any W_9bab0 = Some (Branch BC_EQ 11 0 7908, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb40 : bv 32 := 0x08068e63.
Lemma F_9bb40 : fetch_word Plain.M.loaded_segments (0x9bb98 : word) = Some W_9bb40.
Proof. vm_refl. Qed.
Lemma D_9bb40 : decode_any W_9bb40 = Some (Branch BC_EQ 13 0 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bbdc : bv 32 := 0x00008067.
Lemma F_9bbdc : fetch_word Plain.M.loaded_segments (0x9bc34 : word) = Some W_9bbdc.
Proof. vm_refl. Qed.
Lemma D_9bbdc : decode_any W_9bbdc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

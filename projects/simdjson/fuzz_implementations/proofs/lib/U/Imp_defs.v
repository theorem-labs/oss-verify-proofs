(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image ZBridge.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.MallocU Require Import RMallocRep.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Export Layout Sj_iface.

From OSSVerify.simdjson.fuzz_implementations.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition IMP_LFTOI : Z := 0x3ee58.
Definition IMP_FRAME : Z := 1056.
Definition IMP_BODY : Z := 0x3eeac.
Definition IMP_CTORS : Z := 0x3eedc.
Definition IMP_LOOP : Z := 0x3eff8.
Definition IMP_GETACT_RET : Z := 0x3f01c.
Definition IMP_PARSE_RET : Z := 0x3f044.
Definition IMP_OKARM : Z := 0x3f05c.
Definition IMP_OKARM_END : Z := 0x3f16c.
Definition IMP_AFTER : Z := 0x3f178.
Definition IMP_DTORS : Z := 0x3f260.
Definition IMP_EPILOGUE : Z := 0x3f298.
Definition IMP_FIRST : Z := 0x3f2dc.

Definition IMP_GRSI : Z := 0x3ec2c.
Definition IMP_VEC_DTOR : Z := 0x3ee38.
Definition IMP_GET_AVAIL : Z := 0x445c4.
Definition IMP_AVP_BEGIN : Z := 0x44308.
Definition IMP_AVP_END : Z := 0x44394.
Definition IMP_SUPPORTED : Z := 0x442e4.
Definition IMP_GFS : Z := 0x5e668.
Definition IMP_VEC_ALLOCN : Z := 0x42e98.
Definition IMP_SPLIT_DTOR : Z := 0x42e50.
Definition IMP_MEMCPY : Z := 0xd5a30.
Definition IMP_MEMSET : Z := 0xd5fb0.
Definition IMP_CXA_ATEXIT : Z := 0xc4b08.
Definition IMP_GUARD_ACQ : Z := 0x621bc.
Definition IMP_GUARD_REL : Z := 0x6220c.
Definition IMP_DOC_DTOR : Z := 0x4002c.
Definition IMP_OSS_CTOR : Z := 0x3f390.
Definition IMP_APPEND : Z := 0x4048c.
Definition IMP_PUT : Z := 0x429cc.
Definition IMP_STR : Z := 0x85fa0.
Definition IMP_DSO : Z := 0xe2b88.

Definition IMP_UNIMP : Z := 0x3f2d8.
Definition IMP_ABORT_ARM : Z := 0x3f324.
Definition IMP_GRSI_GROW : Z := 0x3ed10.
Definition IMP_VEC_RELOC : Z := 0x42f40.
Definition IMP_VEC_CHK : Z := 0x43020.
Definition IMP_OPNEW : Z := 0xda968.
Definition IMP_STR_MOVE : Z := 0x3f480.
Definition IMP_SIZE_SPILL : Z := 48.

Definition IMP_IMPLS : Z := 320.
Definition IMP_IMPL_SIZE : Z := 136.
Definition IMP_NIMPL : Z := 4.
Definition IMP_PARSER : Z := 328.
Definition IMP_DOC : Z := 352.
Definition IMP_OUTPUT : Z := 432.
Definition IMP_SRET : Z := 56.
Definition IMP_OSS : Z := 56.
Definition IMP_SB : Z := 864.
Definition IMP_SAVES : Z := 952.
Definition IMP_OKARM_STACK : Z := 65536.

Definition IMP_OS_VPTR : Z := 0xdf470.
Definition IMP_IOS_VPTR : Z := 0xdf498.
Definition IMP_SB_VPTR : Z := 0xdf2e0.
Definition IMP_SBB_VPTR : Z := 0xdf0a0.

Definition imp_saves (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Lemma imp_saves_size : forall ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11, cells_size (imp_saves ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) = 104%nat.
Proof. intros. reflexivity. Qed.

Definition impl0_cells (imp : Z) (j1 j17 j57 j100 : list byte) : list cell :=
  [C8 (wz imp);
   C1 (Z_to_bv 8 0); CB 7 j1; C8 (wz 0); C1 (Z_to_bv 8 0); CB 3 j17; C4 (wz 12);
   C8 (wz 0); C8 (wz 0); C8 (wz 0);
   C8 (wz 4294967295); C1 (Z_to_bv 8 0); CB 7 j57; C8 (wz 0); C8 (wz 0);
   C8 (wz 0); C8 (wz 0); C4 (wz 0); CB 4 j100;
   C8 (wz 0); C8 (wz 0); C8 (wz 0)].
Lemma impl0_cells_size : forall imp j1 j17 j57 j100, cells_size (impl0_cells imp j1 j17 j57 j100) = 136%nat.
Proof. intros. reflexivity. Qed.

Definition out_short (b0 : byte) (j23 : list byte) : list cell := [C1 b0; CB 23 j23].
Definition out_long (S L DATA : Z) : list cell := [C8 (wz (S + 1)); C8 (wz L); C8 (wz DATA)].

Definition gcell (b : bool) : list cell :=
  if b then [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); CB 6 (zeros 6)] else [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 6 (zeros 6)].
Definition sj_cellsX (g0 : bool) (act : Z) (g1 g3 : bool) (arr : Z) (g2 : bool) (spb spn : Z) (sg : bool) : list cell :=
  gcell g0 ++ [C8 (wz act)] ++ gcell g1 ++ [CB 16 (zeros 16)] ++ gcell g3 ++ [C8 (wz arr)] ++ gcell g2 ++ [C8 (wz spb); C8 (wz spn); CB 48 (zeros 48)]
  ++ (if sg then [C8 (wz SJ_FALLBACK_VPTR); C8 (wz SJ_STR_NAME); C8 (wz 8); C8 (wz SJ_STR_DESC); C8 (wz 31); C4 (wz 0)]
      else [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 0)])
  ++ [CB 4 (zeros 4)].
Definition sj_cells_zero : list cell := sj_cellsX false 0 false false 0 false 0 0 false.
Definition sj_cells_g0 : list cell := sj_cellsX true 0 false false 0 false 0 0 false.
Definition sj_cells_mid : list cell := sj_cellsX true 0 false true SJ_FALLBACK true SJ_AVP_ARR 1 true.
Lemma sj_cells_true_X : sj_cells true = sj_cellsX true SJ_FALLBACK true true SJ_FALLBACK true SJ_AVP_ARR 1 true.
Proof. reflexivity. Qed.
Lemma sj_cellsX_size : forall g0 act g1 g3 arr g2 spb spn sg, cells_size (sj_cellsX g0 act g1 g3 arr g2 spb spn sg) = 176%nat.
Proof. intros [|] act [|] [|] arr [|] spb spn [|]; reflexivity. Qed.
Lemma sj_cells_size : forall i, cells_size (sj_cells i) = 176%nat. Proof. intros [|]; reflexivity. Qed.


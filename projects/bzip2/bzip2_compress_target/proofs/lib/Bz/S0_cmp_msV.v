(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCState BzCSortM BzArrD CmpMem CmpCut CmpCut0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs CmpCutMS CmpMsKit.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Record sca := mkSCA { k48 : word; k56 : word; k64 : word; k88 : word; k96 : word; k104 : word }.
(* [comment removed for export] *)
Record scb := mkSCB { k144 : word; k152 : word; k168 : word; k176 : word; k184 : word; k192 : word; k200 : word; k208 : word;
                    k216 : word; k224 : word; k232 : word; k240 : word; k248 : word; k256 : word; k264 : word; k272 : word; k288 : word }.

Section V.
  Variable X : msenv.
  Notation p := (bv_unsigned (me_sp X) - 4928).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X). Notation E := (me_E X).

  (* [comment removed for export] *)
  Definition sca_cells (s : sca) : list cell :=
    [C8 (Z_to_bv 64 (n - 1)); C8 (me_sv X); C8 (Z_to_bv 64 (A1 - 4)); C8 (Z_to_bv 64 65534);
     C8 (k48 s); C8 (k56 s); C8 (k64 s);
     C8 (Z_to_bv 64 (FT + 262144)); C8 (Z_to_bv 64 (FT + 4));
     C8 (k88 s); C8 (k96 s); C8 (k104 s);
     C8 (Z_to_bv 64 E); C8 (Z_to_bv 64 (n * budget_q)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 18446744073707454463)].   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition scb_cells (s : scb) : list cell :=
    [C8 (k144 s); C8 (k152 s); C8 (Z_to_bv 64 (A1 + 4)); C8 (k168 s); C8 (k176 s); C8 (k184 s); C8 (k192 s);
     C8 (k200 s); C8 (k208 s); C8 (k216 s); C8 (k224 s); C8 (k232 s); C8 (k240 s); C8 (k248 s); C8 (k256 s); C8 (k264 s);
     C8 (k272 s); C8 (Z_to_bv 64 (A2 + qo)); C4 (k288 s)].
End V.
End ACeilS1.


(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac open_sc_in H := unfold sca_cells, scb_cells in H; cbn [k48 k56 k64 k88 k96 k104 k144 k152 k168 k176 k184 k192 k200 k208 k216 k224 k232 k240 k248 k256 k264 k272 k288] in H.

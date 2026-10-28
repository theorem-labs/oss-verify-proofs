(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCut0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCLemmasMs CmpCutMS CmpMsKit.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Record sca := mkSCA { k40 : word; k48 : word; k64 : word; k72 : word; k96 : word; k104 : word; k112 : word }.
(* [comment removed for export] *)
Record scb := mkSCB { k128 : word; k136 : word; k144 : word; k152 : word; k168 : word; k176 : word; k184 : word; k208 : word;
                    k232 : word; k240 : word; k248 : word; k256 : word; k288 : word }.

Section V.
  Variable X : msenv.
  Notation p := (bv_unsigned (me_sp X) - 5008).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X). Notation E := (me_E X).

  (* [comment removed for export] *)
  Definition sca_cells (s : sca) : list cell :=
    [C8 (Z_to_bv 64 (n * budget_q)); C8 (Z_to_bv 64 E); C8 (me_sv X); C8 (Z_to_bv 64 (n - 1));
     C8 (k40 s); C8 (k48 s); C8 (Z_to_bv 64 0);
     C8 (k64 s); C8 (k72 s);
     C8 (Z_to_bv 64 (18446744073709551615 - (p + 340))); C8 (Z_to_bv 64 (18446744073709551615 - (p + 1364)));
     C8 (k96 s); C8 (k104 s); C8 (k112 s)].   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition scb_cells (s : scb) : list cell :=
    [C8 (Z_to_bv 64 0); C8 (k128 s); C8 (k136 s); C8 (k144 s); C8 (k152 s);
     C8 (Z_to_bv 64 (18446744073709551615 - (p + 2388))); C8 (k168 s); C8 (k176 s); C8 (k184 s);
     C8 (Z_to_bv 64 65535); C8 (Z_to_bv 64 0); C8 (k208 s); C8 (Z_to_bv 64 18446744073707454463);
     C8 (Z_to_bv 64 (18446744073709551615 - A2)); C8 (k232 s); C8 (k240 s); C8 (k248 s); C8 (k256 s);
     C8 (Z_to_bv 64 (18446744073709551615 - (p + 3704))); C8 (Z_to_bv 64 (18446744073709551615 - (p + 4104)));
     C8 (Z_to_bv 64 (18446744073709551615 - (p + 4504))); C8 (k288 s); C8 (Z_to_bv 64 2147483647);
     C8 (Z_to_bv 64 FT); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (A2 + qo)); C8 (Z_to_bv 64 (18446744073709551615 - FT))].
End V.
End ACeilS1.


(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac open_sc_in H := unfold sca_cells, scb_cells in H; cbn [k40 k48 k64 k72 k96 k104 k112 k128 k136 k144 k152 k168 k176 k184 k208 k232 k240 k248 k256 k288] in H.

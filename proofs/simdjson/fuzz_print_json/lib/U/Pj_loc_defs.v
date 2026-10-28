(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Export Layout.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation PJ_LOC_LO := 0xed228%Z (only parsing).
Notation PJ_LOC_HI := 0xee0d8%Z (only parsing).

Definition loc0_cells : list cell := [CB 3760 (repeat (Z_to_bv 8 0) 3760)].

Definition locb_cells (j1 j2 j3 j4 j5 j6 : list byte) : list cell :=
  [CB 488 j1;
   C8 (Z_to_bv 64 0xed828);
   C1 (Z_to_bv 8 1);
   CB 199 j2;
   C8 (Z_to_bv 64 18446744073709551615);
   C4 (Z_to_bv 64 3);
   CB 604 j3;
   C8 (Z_to_bv 64 0xd9608);
   CB 232 j4;
   C8 (Z_to_bv 64 0xed850);
   C8 (Z_to_bv 64 0xed940);
   CB 24 j5;
   C8 (Z_to_bv 64 0xed748);
   CB 2160 j6].

Definition LOC0 (m : word -> option byte) : Prop := rw_cells usegs m PJ_LOC_LO loc0_cells.
Definition LOCB (m : word -> option byte) : Prop :=
  exists j1 j2 j3 j4 j5 j6, rw_cells usegs m PJ_LOC_LO (locb_cells j1 j2 j3 j4 j5 j6).
Definition pj_locale (m : word -> option byte) : Prop := LOC0 m \/ LOCB m.

Lemma loc0_cells_size : cells_size loc0_cells = 3760%nat.
Proof. reflexivity. Qed.
Lemma locb_cells_size : forall j1 j2 j3 j4 j5 j6, cells_size (locb_cells j1 j2 j3 j4 j5 j6) = 3760%nat.
Proof. intros. reflexivity. Qed.

Lemma LOC0_hull : forall m, LOC0 m -> exists bs, rw_cells usegs m PJ_LOC_LO [CB 3760 bs].
Proof. intros m H. exists (repeat (Z_to_bv 8 0) 3760). exact H. Qed.
Lemma LOCB_hull : forall m, LOCB m -> exists bs, rw_cells usegs m PJ_LOC_LO [CB 3760 bs].
Proof.
  intros m (j1 & j2 & j3 & j4 & j5 & j6 & H).
  apply rw_cells_forget in H. rewrite locb_cells_size in H. exact H.
Qed.
Lemma pj_locale_hull : forall m, pj_locale m -> exists bs, rw_cells usegs m PJ_LOC_LO [CB 3760 bs].
Proof. intros m [H|H]; [apply LOC0_hull | apply LOCB_hull]; exact H. Qed.

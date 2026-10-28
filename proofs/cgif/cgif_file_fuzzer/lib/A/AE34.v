(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP02.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Fixpoint build_ranges (rs : list (Z * nat)) (t : ctable) : ctable :=
match rs with [] => t | (lo, n) :: rest => build_ranges rest (build_table tfibsegs lo n t) end.
Lemma build_ranges_ok : forall rs t,
Forall (fun r => 0 <= fst r) rs -> table_ok tfibsegs t -> table_ok tfibsegs (build_ranges rs t).
Proof.
induction rs as [|[lo n] rest IH]; intros t Hrs Ht; cbn; [exact Ht|].
inversion Hrs; subst. apply IH; [assumption|]. apply build_table_ok; [cbn in *; assumption | exact Ht].
Qed.
Definition musl_sel_ranges : list (Z * nat) :=
[ (0x8d878, 71%nat); (0x92e7c, 25%nat); (0x92fb0, 87%nat); (0x92cec, 435%nat); (0x93ad0, 1146%nat); (0x96be0, 47%nat);
(0x97e60, 10%nat); (0x9c8b8, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x418f0, 38%nat);  (0x41c1c, 165%nat); (0x426c8, 549%nat); (0x42f5c, 94%nat); (0x430d4, 180%nat);
(0x4361c, 156%nat); (0x4388c, 157%nat); (0x441e4, 729%nat); (0x44d48, 45%nat); (0x45114, 54%nat);
(0x47a5c, 102%nat); (0x515d4, 1009%nat); (0x53ccc, 79%nat); (0x54158, 209%nat); (0x586dc, 6%nat);
(0x595ec, 40%nat);  (0x63a1c, 13%nat);  (0x63abc, 7%nat);   (0x63d20, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt 0x51fa8 = Some 0x81010113 /\ clookup tbl_icpt 0x97294 = None /\ clookup tbl_icpt 0x63e98 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

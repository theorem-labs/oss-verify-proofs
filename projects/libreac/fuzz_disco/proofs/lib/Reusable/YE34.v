(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP02 YB1v.
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
[ (0x9056c, 71%nat); (0x95998, 25%nat); (0x959fc, 87%nat); (0x95808, 383%nat); (0x9634c, 1146%nat); (0x9945c, 47%nat);
(0x9a6dc, 10%nat); (0x9f134, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x42a3c, 36%nat);  (0x42d60, 165%nat); (0x4380c, 549%nat); (0x440a0, 94%nat); (0x44218, 180%nat);
(0x44760, 156%nat); (0x449d0, 157%nat); (0x45328, 729%nat); (0x45e8c, 45%nat); (0x46258, 54%nat);
(0x48588, 102%nat); (0x52100, 1009%nat); (0x547f8, 79%nat); (0x54c84, 209%nat); (0x59208, 6%nat);
(0x5a118, 40%nat);  (0x64548, 13%nat);  (0x645e8, 7%nat);   (0x6484c, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt 0x52ad4 = Some 0x81010113 /\ clookup tbl_icpt 0x99b10 = None /\ clookup tbl_icpt 0x649c4 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

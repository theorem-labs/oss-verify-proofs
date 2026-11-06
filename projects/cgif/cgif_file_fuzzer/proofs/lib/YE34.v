(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP02 YB1v.
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
[ (0x8daec, 71%nat); (0x930f0, 25%nat); (0x93224, 87%nat); (0x92f60, 435%nat); (0x93d44, 1146%nat); (0x96e54, 47%nat);
(0x980d4, 10%nat); (0x9cb2c, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x41920, 38%nat);  (0x41c4c, 165%nat); (0x426f8, 549%nat); (0x42f8c, 94%nat); (0x43104, 180%nat);
(0x4364c, 156%nat); (0x438bc, 157%nat); (0x44214, 729%nat); (0x44d78, 45%nat); (0x45144, 54%nat);
(0x47a8c, 102%nat); (0x51604, 1009%nat); (0x53cfc, 79%nat); (0x54188, 209%nat); (0x5870c, 6%nat);
(0x5961c, 40%nat);  (0x63a4c, 13%nat);  (0x63aec, 7%nat);   (0x63d50, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt 0x51fd8 = Some 0x81010113 /\ clookup tbl_icpt 0x97508 = None /\ clookup tbl_icpt 0x63ec8 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

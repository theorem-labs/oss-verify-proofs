(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ03 YB1u.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Fixpoint build_ranges (rs : list (Z * nat)) (t : ctable) : ctable :=
match rs with [] => t | (lo, n) :: rest => build_ranges rest (build_table trbsegs lo n t) end.
Lemma build_ranges_ok : forall rs t,
Forall (fun r => 0 <= fst r) rs -> table_ok trbsegs t -> table_ok trbsegs (build_ranges rs t).
Proof.
induction rs as [|[lo n] rest IH]; intros t Hrs Ht; cbn; [exact Ht|].
inversion Hrs; subst. apply IH; [assumption|]. apply build_table_ok; [cbn in *; assumption | exact Ht].
Qed.
Definition musl_sel_ranges : list (Z * nat) :=
[ (0x92ac0, 71%nat); (0x98164, 25%nat); (0x98298, 87%nat); (0x97fd4, 435%nat); (0x98db8, 1146%nat); (0x9bec8, 47%nat);
(0x9d148, 10%nat); (0xa1ba0, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x42388, 38%nat);  (0x426b4, 165%nat); (0x43160, 549%nat); (0x439f4, 94%nat); (0x43b6c, 180%nat);
(0x440b4, 156%nat); (0x44324, 157%nat); (0x44c7c, 729%nat); (0x457e0, 45%nat); (0x45bac, 54%nat);
(0x484f4, 102%nat); (0x5206c, 1009%nat); (0x54aac, 79%nat); (0x54f38, 209%nat); (0x594bc, 6%nat);
(0x5a3cc, 40%nat);  (0x647fc, 13%nat);  (0x6489c, 7%nat);   (0x64b00, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok trbsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.


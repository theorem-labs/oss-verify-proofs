(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE34.v, with its module paths changed, and its fuzz_reply.asan addresses relocated from cgif_file_fuzzer.asan (33 numerals; per-numeral report). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
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
[ (0x8cf28, 71%nat); (0x92354, 25%nat); (0x923b8, 87%nat); (0x921c4, 383%nat); (0x92d08, 1146%nat); (0x95e18, 47%nat);
(0x971c4, 10%nat); (0x9c2f0, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x4218c, 40%nat);  (0x424c4, 165%nat); (0x43b3c, 549%nat); (0x443d0, 94%nat); (0x44548, 180%nat);
(0x44a90, 156%nat); (0x44f70, 157%nat); (0x458c8, 729%nat); (0x4642c, 45%nat); (0x467f8, 54%nat);
(0x48ba8, 102%nat); (0x52720, 1229%nat); (0x554d0, 79%nat); (0x5595c, 209%nat); (0x59ee0, 6%nat);
(0x5adf0, 40%nat);  (0x652b8, 13%nat);  (0x65358, 7%nat);   (0x655bc, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt 0x53464 = Some 0x81010113 /\ clookup tbl_icpt 0x964cc = None /\ clookup tbl_icpt 0x65734 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

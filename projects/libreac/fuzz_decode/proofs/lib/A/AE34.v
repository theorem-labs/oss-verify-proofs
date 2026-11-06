(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE34.v, with its module paths changed and its addresses moved to libreac/fuzz_grant's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/A/AE34.v (donor image sha256 c2c7559b29bd), with its module paths changed and its addresses moved to libreac/fuzz_decode's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import AB1v.
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
[ (0x88acc, 71%nat); (0x8def8, 25%nat); (0x8df5c, 87%nat); (0x8dd68, 435%nat); (0x8e8ac, 1146%nat); (0x919bc, 47%nat);
(0x92c3c, 10%nat); (0x97694, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x41544, 38%nat);  (0x41868, 165%nat); (0x42314, 549%nat); (0x42ba8, 94%nat); (0x42d20, 180%nat);
(0x43268, 156%nat); (0x434d8, 157%nat); (0x43e30, 729%nat); (0x44994, 45%nat); (0x44d60, 54%nat);
(0x47090, 102%nat); (0x50c08, 1009%nat); (0x5353c, 79%nat); (0x539c8, 209%nat); (0x5819c, 6%nat);
(0x590ac, 40%nat);  (0x635f0, 13%nat);  (0x63690, 7%nat);   (0x638f4, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt 0x515dc = Some 0x81010113 /\ clookup tbl_icpt 0x92070 = None /\ clookup tbl_icpt 0x63a6c = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

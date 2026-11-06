(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE34.v, with its module paths changed and its addresses moved to libreac/fuzz_boxreg's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require Import AB1v.
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
[ (0x88be0, 71%nat); (0x8e00c, 25%nat); (0x8e070, 87%nat); (0x8de7c, 383%nat); (0x8e9c0, 1146%nat); (0x91ad0, 47%nat);
(0x92db0, 10%nat); (0x97808, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x413ec, 3%nat); (0x413fc, 33%nat);  (0x41714, 165%nat); (0x4279c, 549%nat); (0x43030, 94%nat); (0x431a8, 180%nat);
(0x436f0, 156%nat); (0x43960, 157%nat); (0x442b8, 729%nat); (0x44e1c, 45%nat); (0x451e8, 54%nat);
(0x47518, 102%nat); (0x51090, 1009%nat); (0x53788, 79%nat); (0x53c14, 209%nat); (0x58198, 6%nat);
(0x590a8, 40%nat);  (0x634d8, 13%nat);  (0x63578, 7%nat);   (0x637dc, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt 0x51a64 = Some 0x81010113 /\ clookup tbl_icpt 0x92184 = None /\ clookup tbl_icpt 0x63954 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

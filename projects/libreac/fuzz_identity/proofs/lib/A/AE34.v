(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AE34.v, with its module paths and addresses changed; 2 of its 36 lines of code are new or changed and 2 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1v.
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
[ (0x8b070, 71%nat); (0x9049c, 25%nat); (0x90500, 87%nat); (0x9030c, 125%nat); (0x90500, 258%nat); (0x90e50, 1146%nat); (0x93f60, 47%nat);
(0x951e0, 10%nat); (0x99c38, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x4218c, 24%nat); (0x421ec, 1%nat); (0x421f0, 11%nat);  (0x424b0, 165%nat); (0x42f5c, 549%nat); (0x437f0, 94%nat); (0x43968, 180%nat);
(0x43eb0, 156%nat); (0x44120, 157%nat); (0x44a78, 729%nat); (0x455dc, 45%nat); (0x459a8, 54%nat);
(0x47cd8, 102%nat); (0x51850, 1009%nat); (0x53f48, 79%nat); (0x543d4, 209%nat); (0x58958, 6%nat);
(0x59868, 40%nat);  (0x63c98, 13%nat);  (0x63d38, 7%nat);   (0x63f9c, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt 0x52224 = Some 0x81010113 /\ clookup tbl_icpt 0x94614 = None /\ clookup tbl_icpt 0x64114 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

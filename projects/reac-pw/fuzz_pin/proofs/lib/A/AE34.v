(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE34.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AE34.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_pin's ASan build. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import AB1v.
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
[ (0x87c70, 71%nat); (0x8d09c, 25%nat); (0x8d100, 87%nat); (0x8cf0c, 125%nat); (0x8d100, 258%nat); (0x8da50, 1146%nat); (0x90b60, 47%nat);
(0x91f58, 10%nat); (0x969b0, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x41908, 3%nat); (0x41918, 1%nat); (0x41920, 20%nat); (0x41970, 1%nat); (0x41974, 11%nat);  (0x41c34, 165%nat); (0x43144, 549%nat); (0x439d8, 94%nat); (0x43b50, 180%nat);
(0x44098, 156%nat); (0x44308, 157%nat); (0x44c60, 729%nat); (0x457c4, 45%nat); (0x45b90, 54%nat);
(0x47ec0, 102%nat); (0x51a38, 865%nat); (0x53ef0, 79%nat); (0x5437c, 209%nat); (0x58900, 6%nat);
(0x59810, 40%nat);  (0x63c40, 13%nat);  (0x63ce0, 7%nat);   (0x63f44, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt 0x521cc = Some 0x81010113 /\ clookup tbl_icpt 0x91214 = None /\ clookup tbl_icpt 0x640bc = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

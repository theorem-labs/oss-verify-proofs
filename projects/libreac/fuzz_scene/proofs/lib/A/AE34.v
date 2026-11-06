(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE34.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import AB1v.
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
[ (0x8b498, 71%nat); (0x908c4, 25%nat); (0x90928, 87%nat); (0x90734, 125%nat); (0x90928, 258%nat); (0x91278, 1146%nat); (0x94388, 47%nat);
(0x95608, 10%nat); (0x9a060, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x442f8, 24%nat); (0x44358, 1%nat); (0x4435c, 11%nat);  (0x4461c, 165%nat); (0x450c8, 549%nat); (0x4595c, 94%nat); (0x45ad4, 180%nat);
(0x4601c, 156%nat); (0x4628c, 157%nat); (0x46be4, 729%nat); (0x47748, 45%nat); (0x47b14, 54%nat);
(0x49e44, 102%nat); (0x539bc, 1009%nat); (0x560b4, 79%nat); (0x56540, 209%nat); (0x5aac4, 6%nat);
(0x5b9d4, 40%nat);  (0x65e04, 13%nat);  (0x65ea4, 7%nat);   (0x66108, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt 0x54390 = Some 0x81010113 /\ clookup tbl_icpt 0x94a3c = None /\ clookup tbl_icpt 0x66280 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

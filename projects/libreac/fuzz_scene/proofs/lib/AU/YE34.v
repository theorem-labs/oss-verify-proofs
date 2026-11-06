(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YE34.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP02. From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YB1v.
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
[ (0x8b7cc, 71%nat); (0x90bf8, 25%nat); (0x90c5c, 87%nat); (0x90a68, 125%nat); (0x90c5c, 258%nat); (0x915ac, 1146%nat); (0x946bc, 47%nat);
(0x9593c, 10%nat); (0x9a394, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x44324, 24%nat); (0x44384, 1%nat); (0x44388, 11%nat);  (0x44648, 165%nat); (0x450f4, 549%nat); (0x45988, 94%nat); (0x45b00, 180%nat);
(0x46048, 156%nat); (0x462b8, 157%nat); (0x46c10, 729%nat); (0x47774, 45%nat); (0x47b40, 54%nat);
(0x49e70, 102%nat); (0x539e8, 1009%nat); (0x560e0, 79%nat); (0x5656c, 209%nat); (0x5aaf0, 6%nat);
(0x5ba00, 40%nat);  (0x65e30, 13%nat);  (0x65ed0, 7%nat);   (0x66134, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt 0x543bc = Some 0x81010113 /\ clookup tbl_icpt 0x94d70 = None /\ clookup tbl_icpt 0x662ac = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

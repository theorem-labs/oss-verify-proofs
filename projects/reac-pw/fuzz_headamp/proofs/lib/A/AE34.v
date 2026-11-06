(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE34.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AE34.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_role's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/reac-pw/fuzz_role/lib/A/AE34.v at 9f8c843f0e03 (image sha256 614cffc0864c), with its module paths changed and its addresses moved to reac-pw/fuzz_headamp's ASan build (image sha256 f3e0669d2819) by alreloc a5c53bb2bed4; comments kept as the source has them. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import AB1v.
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
[ (0x8c7ec, 71%nat); (0x91338, 25%nat); (0x9139c, 87%nat); (0x911a8, 125%nat); (0x9139c, 258%nat); (0x91cec, 1146%nat); (0x94dfc, 47%nat);
(0x960d8, 10%nat); (0x9ab30, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x41b98, 3%nat); (0x41ba8, 20%nat); (0x41bf8, 1%nat); (0x41bfc, 11%nat);  (0x41ec0, 165%nat); (0x42f48, 549%nat); (0x437dc, 47%nat); (0x43898, 180%nat);
(0x43de0, 156%nat); (0x44050, 157%nat); (0x449a8, 729%nat); (0x4550c, 45%nat); (0x458d8, 54%nat);
(0x47ccc, 102%nat); (0x51d04, 1009%nat); (0x543fc, 79%nat); (0x54888, 209%nat); (0x58e0c, 6%nat);
(0x59d1c, 40%nat);  (0x6414c, 13%nat);  (0x641ec, 7%nat);   (0x64450, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt 0x526d8 = Some 0x81010113 /\ clookup tbl_icpt 0x954ac = None /\ clookup tbl_icpt 0x645c8 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

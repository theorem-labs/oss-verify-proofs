(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YE34.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to omx-clap-core/fuzz_manifest's ASan build. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v.
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
[ (0x892e8, 71%nat); (0x8e714, 25%nat); (0x8e778, 87%nat); (0x8e584, 125%nat); (0x8e778, 258%nat); (0x8f0c8, 1146%nat); (0x921d8, 47%nat);
(0x93b90, 10%nat); (0x985e8, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x41328, 3%nat); (0x41340, 21%nat); (0x41394, 1%nat); (0x41398, 11%nat);  (0x41658, 165%nat); (0x431cc, 549%nat); (0x43a60, 94%nat); (0x43bd8, 180%nat);
(0x44120, 156%nat); (0x44390, 157%nat); (0x44ce8, 729%nat); (0x4584c, 45%nat); (0x45c18, 54%nat);
(0x47f48, 102%nat); (0x51ac0, 1009%nat); (0x541b8, 79%nat); (0x54644, 209%nat); (0x58bc8, 6%nat);
(0x59ad8, 40%nat);  (0x63f08, 13%nat);  (0x63fa8, 7%nat);   (0x6420c, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt 0x52494 = Some 0x81010113 /\ clookup tbl_icpt 0x9288c = None /\ clookup tbl_icpt 0x64384 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AE34.v, with its module paths and module names changed; 32 of its 50 lines of code are new or changed and 18 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YB1v.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Fixpoint build_ranges (rs : list (Z * nat)) (t : ctable) : ctable :=
match rs with [] => t | (lo, n) :: rest => build_ranges rest (build_table tfibsegs lo n t) end.
Lemma build_ranges_ok : forall rs t,
Forall (fun r => 0 <= fst r) rs -> table_ok tfibsegs t -> table_ok tfibsegs (build_ranges rs t).
Proof.
induction rs as [|[lo n] rest IH]; intros t Hrs Ht; cbn; [exact Ht|].
inversion Hrs; subst. apply IH; [assumption|]. apply build_table_ok; [cbn in *; assumption | exact Ht].
Qed.
Definition pf_icpt_ranges : list (Z * nat) :=
[(0x42a40, 1%nat); (0x42a54, 1%nat); (0x42a70, 1%nat);
(0x42a74, 1%nat); (0x42a7c, 1%nat); (0x42d60, 165%nat);
(0x44218, 180%nat); (0x453c4, 690%nat); (0x45e8c, 45%nat);
(0x45f40, 198%nat); (0x46330, 41%nat); (0x48588, 102%nat);
(0x52100, 1%nat); (0x52104, 1%nat); (0x527e4, 188%nat);
(0x52ad4, 380%nat); (0x547f8, 79%nat); (0x54c84, 209%nat);
(0x59208, 6%nat); (0x5a118, 40%nat); (0x64178, 59%nat);
(0x643c0, 8%nat); (0x64418, 9%nat); (0x64494, 24%nat);
(0x64548, 13%nat); (0x645e8, 7%nat); (0x6484c, 12%nat);
(0x649c4, 45%nat)].
Definition tbl_pf_icpt : ctable := Eval vm_compute in build_ranges pf_icpt_ranges TEmpty.
Lemma tbl_pf_icpt_eq : tbl_pf_icpt = build_ranges pf_icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_pf_icpt). Qed.
Lemma tbl_pf_icpt_ok : table_ok tfibsegs tbl_pf_icpt.
Proof.
rewrite tbl_pf_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold pf_icpt_ranges. repeat constructor; cbn; discriminate.
Qed.
Definition pf_musl_ranges : list (Z * nat) :=
[(0x8ffec, 3%nat); (0x95f8c, 78%nat); (0x9617c, 21%nat);
(0x9634c, 108%nat); (0x964fc, 908%nat); (0x9732c, 77%nat);
(0x97460, 53%nat); (0x99478, 51%nat); (0x99544, 55%nat);
(0x99a14, 51%nat); (0x99b10, 257%nat); (0x99f14, 62%nat);
(0x9a39c, 17%nat)].
Definition tbl_pf : ctable := Eval vm_compute in build_ranges pf_musl_ranges tbl_pf_icpt.
Lemma tbl_pf_eq : tbl_pf = build_ranges pf_musl_ranges tbl_pf_icpt.
Proof. vm_cast_no_check (eq_refl tbl_pf). Qed.
Lemma tbl_pf_ok : table_ok tfibsegs tbl_pf.
Proof.
rewrite tbl_pf_eq. apply build_ranges_ok; [| exact tbl_pf_icpt_ok].
unfold pf_musl_ranges. repeat constructor; cbn; discriminate.
Qed.

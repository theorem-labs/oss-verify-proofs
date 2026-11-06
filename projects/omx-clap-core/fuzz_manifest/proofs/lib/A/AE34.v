(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: relocated from cgif_file_fuzzer.asan to omx-clap-core fuzz_manifest.asan: 32 address literal(s) rewritten, module paths changed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v.
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
[ (0x89000, 71%nat); (0x8e42c, 25%nat); (0x8e490, 87%nat); (0x8e29c, 383%nat); (0x8ede0, 1146%nat); (0x91ef0, 47%nat);
(0x938a8, 10%nat); (0x98300, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x412c8, 39%nat);  (0x415f8, 165%nat); (0x4316c, 549%nat); (0x43a00, 94%nat); (0x43b78, 180%nat);
(0x440c0, 156%nat); (0x44330, 157%nat); (0x44c88, 729%nat); (0x457ec, 45%nat); (0x45bb8, 54%nat);
(0x47ee8, 102%nat); (0x51a60, 1009%nat); (0x54158, 79%nat); (0x545e4, 209%nat); (0x58b68, 6%nat);
(0x59a78, 40%nat);  (0x63ea8, 13%nat);  (0x63f48, 7%nat);   (0x641ac, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt 0x52434 = Some 0x81010113 /\ clookup tbl_icpt 0x925a4 = None /\ clookup tbl_icpt 0x64324 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made from projects/cgif/cgif_file_fuzzer/proofs/lib/YE34.v, with its module paths and addresses changed; 2 of its 35 lines of code are new or changed and 2 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YP02. From OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB Require Import YB1v.
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
[ (0x8b35c, 71%nat); (0x90788, 25%nat); (0x907ec, 87%nat); (0x905f8, 125%nat); (0x907ec, 258%nat); (0x9113c, 1146%nat); (0x9424c, 47%nat);
(0x954cc, 10%nat); (0x99f24, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x421f4, 24%nat); (0x42254, 1%nat); (0x42258, 11%nat);  (0x42518, 165%nat); (0x42fc4, 549%nat); (0x43858, 94%nat); (0x439d0, 180%nat);
(0x43f18, 156%nat); (0x44188, 157%nat); (0x44ae0, 729%nat); (0x45644, 45%nat); (0x45a10, 54%nat);
(0x47d40, 102%nat); (0x518b8, 1009%nat); (0x53fb0, 79%nat); (0x5443c, 209%nat); (0x589c0, 6%nat);
(0x598d0, 40%nat);  (0x63d00, 13%nat);  (0x63da0, 7%nat);   (0x64004, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt 0x5228c = Some 0x81010113 /\ clookup tbl_icpt 0x94900 = None /\ clookup tbl_icpt 0x6417c = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE34.v, with its module paths changed and its addresses moved to libreac/fuzz_grant's ASan build. *)
(* Relocated from proofs/libreac/fuzz_grant/lib/A/AE34.v at 25e3d17bdb50 by port_core 83f5203d2a2f onto libdiginet/fuzz_transport (asan). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
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
[ (0x93c6c, 71%nat); (0x99098, 25%nat); (0x990fc, 87%nat); (0x98f08, 435%nat); (0x99a4c, 1146%nat); (0x9cb5c, 47%nat);
(0x9dddc, 10%nat); (0xa2834, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x42ce4, 38%nat);  (0x43008, 165%nat); (0x43ab4, 549%nat); (0x44348, 94%nat); (0x444c0, 180%nat);
(0x44a08, 156%nat); (0x44c78, 157%nat); (0x455d0, 729%nat); (0x46134, 45%nat); (0x46500, 54%nat);
(0x48830, 102%nat); (0x523a8, 1009%nat); (0x54aa0, 79%nat); (0x54f2c, 209%nat); (0x594b0, 6%nat);
(0x5a3c0, 40%nat);  (0x647f0, 13%nat);  (0x64890, 7%nat);   (0x64af4, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt 0x52d7c = Some 0x81010113 /\ clookup tbl_icpt 0x9d210 = None /\ clookup tbl_icpt 0x64c6c = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

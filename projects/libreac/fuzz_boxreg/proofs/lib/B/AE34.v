(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE34.v, with its module paths changed and its addresses moved to libreac/fuzz_boxreg's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B Require Import AB1v.
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
[ (0x89004, 71%nat); (0x8e430, 25%nat); (0x8e494, 87%nat); (0x8e2a0, 383%nat); (0x8ede4, 1146%nat); (0x91ef4, 47%nat);
(0x931d4, 10%nat); (0x97c2c, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x4144c, 3%nat); (0x4145c, 33%nat);  (0x41774, 165%nat); (0x427fc, 549%nat); (0x43090, 94%nat); (0x43208, 180%nat);
(0x43750, 156%nat); (0x439c0, 157%nat); (0x44318, 729%nat); (0x44e7c, 45%nat); (0x45248, 54%nat);
(0x47578, 102%nat); (0x510f0, 1009%nat); (0x537e8, 79%nat); (0x53c74, 209%nat); (0x581f8, 6%nat);
(0x59108, 40%nat);  (0x63538, 13%nat);  (0x635d8, 7%nat);   (0x6383c, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt 0x51ac4 = Some 0x81010113 /\ clookup tbl_icpt 0x925a8 = None /\ clookup tbl_icpt 0x639b4 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

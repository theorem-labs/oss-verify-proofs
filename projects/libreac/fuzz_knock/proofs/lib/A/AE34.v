(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE34.v, with its module paths changed and its addresses moved to libreac/fuzz_knock's ASan build; AB1v's tfibsegs is A/AWalkFw0.v's. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import AWalkFw0.
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
[ (0x86368, 71%nat); (0x8b794, 25%nat); (0x8b7f8, 87%nat); (0x8b604, 383%nat); (0x8c148, 1146%nat); (0x8f258, 47%nat);
(0x904d4, 10%nat); (0x94f2c, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x40eac, 35%nat);  (0x411cc, 165%nat); (0x41c78, 549%nat); (0x4250c, 47%nat); (0x425c8, 180%nat);
(0x42b10, 156%nat); (0x42d80, 157%nat); (0x436d8, 729%nat); (0x4423c, 45%nat); (0x44608, 54%nat);
(0x46938, 102%nat); (0x504b0, 714%nat); (0x5270c, 79%nat); (0x52b98, 209%nat); (0x5711c, 6%nat);
(0x5802c, 40%nat);  (0x6245c, 13%nat);  (0x624fc, 7%nat);   (0x62760, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt 0x509e8 = Some 0x81010113 /\ clookup tbl_icpt 0x8f908 = None /\ clookup tbl_icpt 0x628d8 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

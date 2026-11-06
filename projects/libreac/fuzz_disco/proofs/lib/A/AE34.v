(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE34.v, with its module paths changed and its addresses moved to libreac/fuzz_disco's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AB1v.
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
[ (0x901cc, 71%nat); (0x955f8, 25%nat); (0x9565c, 87%nat); (0x95468, 383%nat); (0x95fac, 1146%nat); (0x990bc, 47%nat);
(0x9a33c, 10%nat); (0x9ed94, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x429c4, 36%nat);  (0x42ce8, 165%nat); (0x43794, 549%nat); (0x44028, 94%nat); (0x441a0, 180%nat);
(0x446e8, 156%nat); (0x44958, 157%nat); (0x452b0, 729%nat); (0x45e14, 45%nat); (0x461e0, 54%nat);
(0x48510, 102%nat); (0x52088, 1009%nat); (0x54780, 79%nat); (0x54c0c, 209%nat); (0x59190, 6%nat);
(0x5a0a0, 40%nat);  (0x644d0, 13%nat);  (0x64570, 7%nat);   (0x647d4, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt 0x52a5c = Some 0x81010113 /\ clookup tbl_icpt 0x99770 = None /\ clookup tbl_icpt 0x6494c = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

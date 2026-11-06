(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ03 YB0z.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Fixpoint build_ranges (rs : list (Z * nat)) (t : ctable) : ctable :=
match rs with [] => t | (lo, n) :: rest => build_ranges rest (build_table trasegs lo n t) end.
Lemma build_ranges_ok : forall rs t,
Forall (fun r => 0 <= fst r) rs -> table_ok trasegs t -> table_ok trasegs (build_ranges rs t).
Proof.
induction rs as [|[lo n] rest IH]; intros t Hrs Ht; cbn; [exact Ht|].
inversion Hrs; subst. apply IH; [assumption|]. apply build_table_ok; [cbn in *; assumption | exact Ht].
Qed.
Definition musl_sel_ranges : list (Z * nat) :=
[ (0x91a74, 71%nat); (0x97078, 25%nat); (0x971ac, 87%nat); (0x96ee8, 435%nat); (0x97ccc, 1146%nat); (0x9addc, 47%nat);
(0x9c05c, 10%nat); (0xa0ab4, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x420c4, 38%nat);  (0x423f0, 165%nat); (0x42e9c, 549%nat); (0x43730, 94%nat); (0x438a8, 180%nat);
(0x43df0, 156%nat); (0x44060, 157%nat); (0x449b8, 729%nat); (0x4551c, 45%nat); (0x458e8, 54%nat);
(0x48230, 102%nat); (0x51da8, 1009%nat); (0x547e8, 79%nat); (0x54c74, 209%nat); (0x591f8, 6%nat);
(0x5a108, 40%nat);  (0x64538, 13%nat);  (0x645d8, 7%nat);   (0x6483c, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok trasegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.


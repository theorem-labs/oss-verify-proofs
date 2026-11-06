(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YE34.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to libreac/fuzz_grant's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP02. From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YB1v.
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
[ (0x8d2ec, 71%nat); (0x92718, 25%nat); (0x9277c, 87%nat); (0x92588, 125%nat); (0x9277c, 258%nat); (0x930cc, 1146%nat); (0x961dc, 47%nat);
(0x9745c, 10%nat); (0x9beb4, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x424bc, 24%nat); (0x4251c, 1%nat); (0x42520, 11%nat);  (0x427e0, 165%nat); (0x4328c, 549%nat); (0x43b20, 94%nat); (0x43c98, 180%nat);
(0x441e0, 156%nat); (0x44450, 157%nat); (0x44da8, 729%nat); (0x4590c, 45%nat); (0x45cd8, 54%nat);
(0x48008, 102%nat); (0x51b80, 1009%nat); (0x54278, 79%nat); (0x54704, 209%nat); (0x58c88, 6%nat);
(0x59b98, 40%nat);  (0x63fc8, 13%nat);  (0x64068, 7%nat);   (0x642cc, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt 0x52554 = Some 0x81010113 /\ clookup tbl_icpt 0x96890 = None /\ clookup tbl_icpt 0x64444 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

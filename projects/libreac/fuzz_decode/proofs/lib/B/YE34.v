(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *) (* Modified by Theorem Labs, 2026-10: two donor ranges are split, never widened (the release's range-content rule): musl_sel_ranges' (0x92f60, 435) covers the donor's fopen 0x93158 and fclose 0x93154, which fuzz_decode.asan-ubsan does not link, so it becomes (0x8e310, 125) = __stdio_write + dprintf and (0x8e504, 258) = __lockfile .. __stdio_exit; and icpt_ranges' trampoline table has the donor's two dead slots 0x41980 (fopen) and 0x41988 (fclose) cut out, so it becomes (0x41590, 24), (0x415f0, 1) and (0x415f4, 11) = the 36 live trampolines, not 38 slots *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YE34.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to libreac/fuzz_decode's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YP02. From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YB1v.
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
[ (0x89074, 71%nat); (0x8e4a0, 25%nat); (0x8e504, 87%nat); (0x8e310, 125%nat); (0x8e504, 258%nat); (0x8ee54, 1146%nat); (0x91f64, 47%nat);
(0x931e4, 10%nat); (0x97c3c, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x41590, 24%nat); (0x415f0, 1%nat); (0x415f4, 11%nat);  (0x418b4, 165%nat); (0x42360, 549%nat); (0x42bf4, 94%nat); (0x42d6c, 180%nat);
(0x432b4, 156%nat); (0x43524, 157%nat); (0x43e7c, 729%nat); (0x449e0, 45%nat); (0x44dac, 54%nat);
(0x470dc, 102%nat); (0x50c54, 1009%nat); (0x53588, 79%nat); (0x53a14, 209%nat); (0x581e8, 6%nat);
(0x590f8, 40%nat);  (0x6363c, 13%nat);  (0x636dc, 7%nat);   (0x63940, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt 0x51628 = Some 0x81010113 /\ clookup tbl_icpt 0x92618 = None /\ clookup tbl_icpt 0x63ab8 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

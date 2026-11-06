(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE34.v, with its module paths changed, its addresses moved to plugin-hostd/fuzz_command's ASan build, the musl range from __stdio_write measured without cgif's fclose (fuzz_command has none: 435 -> 383 instructions, 0x9a820..0x9ae1c) and the wrapper block at its full fuzz_command length (46 entries, 0x45130..0x451e8). *)
(* Modified by Theorem Labs, 2026-10: copied from this harness's lib/A/AE34.v (the twin of cgif_file_fuzzer's lib/YE34.v), with its module paths changed (lib/A to lib/B, image Asan to AsanUbsan) and its addresses moved to plugin-hostd/fuzz_command's ASan+UBSan build. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v.
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
[ (0x950e0, 71%nat); (0x9a50c, 25%nat); (0x9a570, 87%nat); (0x9a37c, 383%nat); (0x9aec0, 1146%nat); (0x9dfd0, 47%nat);
(0x9f6ec, 10%nat); (0xa4144, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x4517c, 46%nat);  (0x454c8, 165%nat); (0x47170, 549%nat); (0x47a04, 94%nat); (0x47b7c, 180%nat);
(0x480c4, 156%nat); (0x48334, 157%nat); (0x48c8c, 729%nat); (0x497f0, 45%nat); (0x49e9c, 54%nat);
(0x4d63c, 102%nat); (0x57674, 1009%nat); (0x59d6c, 79%nat); (0x5a1f8, 209%nat); (0x5e77c, 6%nat);
(0x5f68c, 40%nat);  (0x69abc, 13%nat);  (0x69b5c, 7%nat);   (0x69dc0, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt 0x58048 = Some 0x81010113 /\ clookup tbl_icpt 0x9e698 = None /\ clookup tbl_icpt 0x69f38 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

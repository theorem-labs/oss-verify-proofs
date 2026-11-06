(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE34.v, with its module paths changed, its addresses moved to plugin-hostd/fuzz_command's ASan build, the musl range from __stdio_write measured without cgif's fclose (fuzz_command has none: 435 -> 383 instructions, 0x9a820..0x9ae1c) and the wrapper block at its full fuzz_command length (46 entries, 0x45130..0x451e8). *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/AE34.v (donor image sha256 c0661b96b5bd), with its module paths changed and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1v.
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
[ (0x90e50, 71%nat); (0x9627c, 25%nat); (0x962e0, 87%nat); (0x960ec, 383%nat); (0x96c30, 1146%nat); (0x99d40, 47%nat);
(0x9b8fc, 10%nat); (0xa0354, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x43a0c, 4%nat); (0x43a28, 1%nat); (0x43a30, 33%nat); (0x43ab8, 1%nat);  (0x43d50, 165%nat); (0x46530, 549%nat); (0x46dc4, 94%nat); (0x46f3c, 180%nat);
(0x47484, 156%nat); (0x476f4, 157%nat); (0x4804c, 729%nat); (0x48bb0, 45%nat); (0x48f7c, 54%nat);
(0x4b8a0, 102%nat); (0x558d8, 1009%nat); (0x5820c, 79%nat); (0x58698, 209%nat); (0x5ce6c, 6%nat);
(0x5dd7c, 40%nat);  (0x682c0, 13%nat);  (0x68360, 7%nat);   (0x685c4, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt 0x562ac = Some 0x81010113 /\ clookup tbl_icpt 0x9a3f4 = None /\ clookup tbl_icpt 0x6873c = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

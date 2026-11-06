(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE34.v, with its module paths changed, its addresses moved to plugin-hostd/fuzz_command's ASan build, the musl range from __stdio_write measured without cgif's fclose (fuzz_command has none: 435 -> 383 instructions, 0x9a820..0x9ae1c) and the wrapper block at its full fuzz_command length (46 entries, 0x45130..0x451e8). *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/AE34.v (donor image sha256 c0661b96b5bd), with its module paths changed and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/AE34.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v.
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
[ (0x915fc, 71%nat); (0x96a28, 25%nat); (0x96a8c, 87%nat); (0x96898, 383%nat); (0x973dc, 1146%nat); (0x9a4ec, 47%nat);
(0x9c0a8, 10%nat); (0xa0b00, 69%nat) ].
Definition icpt_ranges : list (Z * nat) :=
musl_sel_ranges ++
[ (0x43a98, 4%nat); (0x43ab4, 1%nat); (0x43abc, 33%nat); (0x43b44, 1%nat);  (0x43ddc, 165%nat); (0x465bc, 549%nat); (0x46e50, 94%nat); (0x46fc8, 180%nat);
(0x47510, 156%nat); (0x47780, 157%nat); (0x480d8, 729%nat); (0x48c3c, 45%nat); (0x49008, 54%nat);
(0x4b92c, 102%nat); (0x55964, 1009%nat); (0x58298, 79%nat); (0x58724, 209%nat); (0x5cef8, 6%nat);
(0x5de08, 40%nat);  (0x6834c, 13%nat);  (0x683ec, 7%nat);   (0x68650, 12%nat) ].
Definition tbl_icpt : ctable := Eval vm_compute in build_ranges icpt_ranges TEmpty.
Lemma tbl_icpt_eq : tbl_icpt = build_ranges icpt_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_icpt). Qed.
Lemma tbl_icpt_ok : table_ok tfibsegs tbl_icpt.
Proof.
rewrite tbl_icpt_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold icpt_ranges, musl_sel_ranges. cbn [app]. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_icpt_probe :
clookup tbl_icpt 0x56338 = Some 0x81010113 /\ clookup tbl_icpt 0x9aba0 = None /\ clookup tbl_icpt 0x687c8 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

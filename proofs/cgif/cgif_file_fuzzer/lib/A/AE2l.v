(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP02.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition ff_ranges : list (Z * nat) :=
[ (0x423e4, 184%nat); (0x462f0, 457%nat); (0x47bf4, 747%nat); (0x929c4, 130%nat); (0x93540, 100%nat); (0x936d0, 176%nat);
(0x97790, 71%nat); (0x97b64, 3%nat); (0x97d5c, 1%nat); (0x97dec, 3%nat) ].
Definition tbl_ff : ctable := Eval vm_compute in build_ranges ff_ranges tbl_icpt.
Lemma tbl_ff_eq : tbl_ff = build_ranges ff_ranges tbl_icpt.
Proof. vm_cast_no_check (eq_refl tbl_ff). Qed.
Lemma tbl_ff_ok : table_ok tfibsegs tbl_ff.
Proof.
rewrite tbl_ff_eq. apply build_ranges_ok; [| apply tbl_icpt_ok].
unfold ff_ranges. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_ff_probe :
clookup tbl_ff 0x47bf4 = Some 0xf5010113 /\ clookup tbl_ff 0x462f0 = Some 0x81010113 /\ clookup tbl_ff 0x423e4 = Some 0x81010113 /\
clookup tbl_ff 0x52930 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

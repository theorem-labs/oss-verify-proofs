(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP02 YB1v YE34.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition ff_ranges : list (Z * nat) :=
[ (0x42414, 184%nat); (0x46320, 457%nat); (0x47c24, 747%nat); (0x92c38, 130%nat); (0x937b4, 100%nat); (0x93944, 176%nat);
(0x97a04, 71%nat); (0x97dd8, 3%nat); (0x97fd0, 1%nat); (0x98060, 3%nat) ].
Definition tbl_ff : ctable := Eval vm_compute in build_ranges ff_ranges tbl_icpt.
Lemma tbl_ff_eq : tbl_ff = build_ranges ff_ranges tbl_icpt.
Proof. vm_cast_no_check (eq_refl tbl_ff). Qed.
Lemma tbl_ff_ok : table_ok tfibsegs tbl_ff.
Proof.
rewrite tbl_ff_eq. apply build_ranges_ok; [| apply tbl_icpt_ok].
unfold ff_ranges. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_ff_probe :
clookup tbl_ff 0x47c24 = Some 0xf5010113 /\ clookup tbl_ff 0x46320 = Some 0x81010113 /\ clookup tbl_ff 0x42414 = Some 0x81010113 /\
clookup tbl_ff 0x52960 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

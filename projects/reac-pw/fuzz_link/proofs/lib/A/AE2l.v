(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE2l.v, with its module paths changed and its addresses moved to libreac/fuzz_pcap's ASan build. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AE34.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition ff_ranges : list (Z * nat) :=
[ (0x44118, 184%nat); (0x48074, 174%nat); (0x49390, 747%nat); (0x96f50, 176%nat);
(0x9b0a0, 71%nat); (0x9b4d4, 3%nat); (0x9b6cc, 1%nat); (0x9b75c, 3%nat) ].
Definition tbl_ff : ctable := Eval vm_compute in build_ranges ff_ranges tbl_icpt.
Lemma tbl_ff_eq : tbl_ff = build_ranges ff_ranges tbl_icpt.
Proof. vm_cast_no_check (eq_refl tbl_ff). Qed.
Lemma tbl_ff_ok : table_ok tfibsegs tbl_ff.
Proof.
rewrite tbl_ff_eq. apply build_ranges_ok; [| apply tbl_icpt_ok].
unfold ff_ranges. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_ff_probe :
clookup tbl_ff 0x49390 = Some 0xf5010113 /\ clookup tbl_ff 0x44118 = Some 0x81010113 /\
clookup tbl_ff 0x540cc = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

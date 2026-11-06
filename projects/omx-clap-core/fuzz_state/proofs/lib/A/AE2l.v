(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE2l.v, with its module paths changed and its addresses moved to omx-clap-core/fuzz_state's ASan build. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AE34.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition ff_ranges : list (Z * nat) :=
[ (0x43140, 184%nat); (0x4704c, 67%nat); (0x48338, 747%nat); (0x920b4, 12%nat); (0x92988, 160%nat);
(0x98f1c, 71%nat); (0x992f0, 3%nat); (0x994e8, 1%nat); (0x99578, 3%nat) ].
Definition tbl_ff : ctable := Eval vm_compute in build_ranges ff_ranges tbl_icpt.
Lemma tbl_ff_eq : tbl_ff = build_ranges ff_ranges tbl_icpt.
Proof. vm_cast_no_check (eq_refl tbl_ff). Qed.
Lemma tbl_ff_ok : table_ok tfibsegs tbl_ff.
Proof.
rewrite tbl_ff_eq. apply build_ranges_ok; [| apply tbl_icpt_ok].
unfold ff_ranges. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_ff_probe :
clookup tbl_ff 0x48338 = Some 0xf5010113 /\ clookup tbl_ff 0x43140 = Some 0x81010113 /\
clookup tbl_ff 0x53074 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

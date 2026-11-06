(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AD1g.v's tfib_holes_if (forallb if_chk HS_tfib_list = true, by computation) for plugin-hostd/fuzz_command: the check of hand-off states 30..39 of A/AB01.v, one lemma per state, so that the 50 states' checks (each over every TFIB_CONST cell of A/AF0m.v) compile in parallel files; A/CmdStartInst.v joins them into the instance of class TfibHolesIf. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AD1g.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AB01.
Lemma if_chk_30 : if_chk AB01.HS_tfib_30 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_31 : if_chk AB01.HS_tfib_31 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_32 : if_chk AB01.HS_tfib_32 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_33 : if_chk AB01.HS_tfib_33 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_34 : if_chk AB01.HS_tfib_34 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_35 : if_chk AB01.HS_tfib_35 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_36 : if_chk AB01.HS_tfib_36 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_37 : if_chk AB01.HS_tfib_37 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_38 : if_chk AB01.HS_tfib_38 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_39 : if_chk AB01.HS_tfib_39 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

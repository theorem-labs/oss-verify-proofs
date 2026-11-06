(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AD1g.v's tfib_holes_if (forallb if_chk HS_tfib_list = true, by computation) for plugin-hostd/fuzz_command: the check of hand-off states 10..19 of A/AB01.v, one lemma per state, so that the 50 states' checks (each over every TFIB_CONST cell of A/AF0m.v) compile in parallel files; A/CmdStartInst.v joins them into the instance of class TfibHolesIf. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AD1g.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AB01.
Lemma if_chk_10 : if_chk AB01.HS_tfib_10 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_11 : if_chk AB01.HS_tfib_11 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_12 : if_chk AB01.HS_tfib_12 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_13 : if_chk AB01.HS_tfib_13 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_14 : if_chk AB01.HS_tfib_14 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_15 : if_chk AB01.HS_tfib_15 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_16 : if_chk AB01.HS_tfib_16 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_17 : if_chk AB01.HS_tfib_17 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_18 : if_chk AB01.HS_tfib_18 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_19 : if_chk AB01.HS_tfib_19 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

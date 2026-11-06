(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AD1g.v's tfib_holes_if (forallb if_chk HS_tfib_list = true, by computation) for plugin-hostd/fuzz_command: the check of hand-off states 40..49 of A/AB01.v, one lemma per state, so that the 50 states' checks (each over every TFIB_CONST cell of A/AF0m.v) compile in parallel files; A/CmdStartInst.v joins them into the instance of class TfibHolesIf. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AD1g.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AB01.
Lemma if_chk_40 : if_chk AB01.HS_tfib_40 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_41 : if_chk AB01.HS_tfib_41 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_42 : if_chk AB01.HS_tfib_42 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_43 : if_chk AB01.HS_tfib_43 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_44 : if_chk AB01.HS_tfib_44 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_45 : if_chk AB01.HS_tfib_45 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_46 : if_chk AB01.HS_tfib_46 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_47 : if_chk AB01.HS_tfib_47 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_48 : if_chk AB01.HS_tfib_48 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_49 : if_chk AB01.HS_tfib_49 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

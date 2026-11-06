(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AD1g.v's tfib_holes_if (forallb if_chk HS_tfib_list = true, by computation) for plugin-hostd/fuzz_command: the check of hand-off states 20..29 of A/AB01.v, one lemma per state, so that the 50 states' checks (each over every TFIB_CONST cell of A/AF0m.v) compile in parallel files; A/CmdStartInst.v joins them into the instance of class TfibHolesIf. *)
(* Modified by Theorem Labs, 2026-10: copied from this harness's lib/A/CmdStartIf2.v, with its module paths changed (lib/A to lib/B, image Asan to AsanUbsan) and its addresses moved to plugin-hostd/fuzz_command's ASan+UBSan build. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YD1g.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YB01.
Lemma if_chk_20 : if_chk YB01.HS_tfib_20 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_21 : if_chk YB01.HS_tfib_21 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_22 : if_chk YB01.HS_tfib_22 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_23 : if_chk YB01.HS_tfib_23 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_24 : if_chk YB01.HS_tfib_24 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_25 : if_chk YB01.HS_tfib_25 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_26 : if_chk YB01.HS_tfib_26 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_27 : if_chk YB01.HS_tfib_27 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_28 : if_chk YB01.HS_tfib_28 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_29 : if_chk YB01.HS_tfib_29 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

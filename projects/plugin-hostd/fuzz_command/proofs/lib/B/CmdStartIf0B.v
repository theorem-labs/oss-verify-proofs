(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AD1g.v's tfib_holes_if (forallb if_chk HS_tfib_list = true, by computation) for plugin-hostd/fuzz_command: the check of hand-off states 0..9 of A/AB01.v, one lemma per state, so that the 50 states' checks (each over every TFIB_CONST cell of A/AF0m.v) compile in parallel files; A/CmdStartInst.v joins them into the instance of class TfibHolesIf. *)
(* Modified by Theorem Labs, 2026-10: copied from this harness's lib/A/CmdStartIf0.v, with its module paths changed (lib/A to lib/B, image Asan to AsanUbsan) and its addresses moved to plugin-hostd/fuzz_command's ASan+UBSan build. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YD1g.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YB01.
Lemma if_chk_0 : if_chk YB01.HS_tfib_0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_1 : if_chk YB01.HS_tfib_1 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_2 : if_chk YB01.HS_tfib_2 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_3 : if_chk YB01.HS_tfib_3 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_4 : if_chk YB01.HS_tfib_4 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_5 : if_chk YB01.HS_tfib_5 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_6 : if_chk YB01.HS_tfib_6 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_7 : if_chk YB01.HS_tfib_7 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_8 : if_chk YB01.HS_tfib_8 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma if_chk_9 : if_chk YB01.HS_tfib_9 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

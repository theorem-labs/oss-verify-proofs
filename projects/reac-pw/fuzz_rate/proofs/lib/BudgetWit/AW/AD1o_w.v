(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1o.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AD1o.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_rate's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AD1o.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0i YK15.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0n YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YI04 YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.BudgetWit.AW Require Import YA0n_w YA0e_w.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG01 YG0f YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.BudgetWit.AW Require Import YG0n_w YG0s_w YG0d_w YCe5_w.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YL02.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import AB1v AF0m AD2j.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.BudgetWit.AW Require Import AD2i_w AD1t_w AD20_w AD1v_w AD2h_w AD2f_w AD1w_w AD1x_w AE22_w ACeg_w.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.BudgetWit.AW Require Import AE3f_w AE2p_w.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import AE3i.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.BudgetWit.AW Require Import AE39_w AE3h_w AE3m_w AF0x_w AE2y_w AE31_w AE36_w AE2v_w AD1k_w.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.BudgetWit.AW Require Import AE2k_w AD1u_w.
Section e.
Lemma stdout_img_chk : img_cells_chk F_STDOUT stdout_fields0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma stdout_pristine_img : forall H m, stdout_img H m -> stdout_pristine (mrestrict H m).
Proof.
intros H m Hi. apply (ofile_is_img _ STDOUT_LO STDOUT_HI); [apply img_rd_of_aview; exact Hi | exact stdout_img_chk |].
unfold stdout_fields0, F_STDOUT, STDOUT_LO, STDOUT_HI. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
Qed.
End e.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD26.v, with its module paths changed, names TfibSyms -> BoxregSyms and its addresses moved to libreac/fuzz_boxreg's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AD26.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.libreac.fuzz_boxreg.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YO0d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK00 YK14 YK15.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK0p YP0n YK0s YM02 YP0m YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YN3q YN3v YI04 YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0p_w YA0m_w.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.BudgetWit.AW Require Import YA0e_w.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG01 YG0k YG0f.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.BudgetWit.AW Require Import YG0n_w YG0d_w YCe5_w.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require Import AB1v AB12 AF0l.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.BudgetWit.AW Require Import AB1h_w.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require Import AB13 AF0m AD2j.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.BudgetWit.AW Require Import AD2i_w AD1t_w AD20_w.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YD2n.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.BudgetWit.AW Require Import AD1v_w AD1y_w.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Lemma img_regions_wf : regions_wf IMG_REGIONS = true. Proof. reflexivity. Qed.
Lemma submem_refl : forall rs, submem rs rs.
Proof. induction rs as [|r rs IH]; [constructor|]. apply submem_keep; [|exact IH]. repeat split; try lia. auto. Qed.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.BudgetWit.AW Require Import AE2k_w AD1u_w.

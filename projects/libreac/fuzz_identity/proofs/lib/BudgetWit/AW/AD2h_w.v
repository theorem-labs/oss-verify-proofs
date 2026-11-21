(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AD2h.v, with its module paths and addresses changed; 4 of its 73 lines of code are new or changed and 2 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from A/AD2h.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut for the usage path at 16 GiB: the pruning removed declarations that this path does not use; some unused declarations can remain. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.libreac.fuzz_identity.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l YP06 YP03 YP0g YP08 YN3q YN3v YI04 YL09 YL02 YL04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1v AF0m AD2j.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AD2i_w AD1t_w AD20_w AD1y_w.
Import ListNotations.

From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AD2i_w AD1t_w AD20_w AD1y_w AD24_w.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Definition cond_SH : acond := mkAC BC_GEU (SLit 5) (SOff A_LEN 0).
Definition cond_H6 : acond := mkAC BC_LTU (SLit 5) (SOff A_LEN 0).

Definition S_SHORT : sstate := Eval vm_compute in run_lp (add_cond S_HDR cond_SH).
Definition blkreg6 : YP09.region := YP09.mkRegion (Some A_BUF) 0 6 0 0 [mkChunk 0 (CData 2 0 6)].
Definition S_H0c : sstate := Eval vm_compute in (add_cond S_HDR cond_H6).
Definition S_H6 : sstate := mkSS (ss_pc S_H0c) (ss_regs S_H0c) (ss_mem S_H0c ++ [blkreg6]) None (ss_facts S_H0c).
Definition S_H1 : sstate := Eval vm_compute in run_lp S_H6.

Definition cond_OV : acond := mkAC BC_LTU (SOff A_LEN 0) sv_cl6.
Definition cond_OK : acond := mkAC BC_GEU (SOff A_LEN 0) sv_cl6.

Definition S_OVR : sstate := Eval vm_compute in run_lp (add_cond S_H1 cond_OV).
Definition S_P : sstate := Eval vm_compute in run_lp (add_cond S_H1 cond_OK).

Lemma S_HDR_win_ok : forallb drv_win_ok (ss_mem S_HDR) = true. Proof. reflexivity. Qed.

Lemma wbs_SHORT : wr_below_sp (ss_facts S_SHORT) (ss_mem S_HDR) = true. Proof. vm_compute. reflexivity. Qed.

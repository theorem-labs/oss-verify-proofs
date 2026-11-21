(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from the start-up certificate lemmas of proofs/cgif/cgif_file_fuzzer/lib/A (AD1g.v tfib_holes_chk and tfib_holes_if, AD2i.v entry_check_all, AD1d.v tfib_holes_chkB, AD1f.v tfib_holes_imgsh, AD2k.v finv_check_all, each by computation, and AB01.v / AB1n.v's hand-off states and tfib_startup_T1) for plugin-hostd/fuzz_command: the instances of the start-up classes of lib/A/CmdStartCert.v, AD1g.v, AD2i.v, AD1d.v, AD1f.v and AD2k.v from fuzz_command's ASan start-up certificate (lib/A/AB01.v HS_tfib_list, lib/A/AB1n.v tfib_startup_T1); TfibHolesIf joins the per-state checks of lib/A/CmdStartIf0.v .. CmdStartIf4.v, and TfibHolesStkAux is lib/A/StartStkAux.v's tfib_holes_stkaux; TfibAvis8 (lib/A/CmdWorldH8.v, the page alignment of the a_vis entries, omx-clap-core/fuzz_manifest's FMworldH8.v avis8_all) is cmd_avis8_c, by computation. *)
(* Modified by Theorem Labs, 2026-11: made from A/CmdStartInst.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 by the port of its source A/CmdStartInst.v (taken three-way onto this twin), with the declarations the twin cut left cut and its modules kept on their twins. *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.plugin_hostd.fuzz_command.images Require Import Asan.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK15.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK0c YK0e YK09 YA01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.BudgetWit.AW Require Import YA0c_w YA0e_w YA02_w.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB12.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.BudgetWit.AW Require Import AB1h_w CmdStartCert_w.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.BudgetWit.AW Require AB1n_w.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.BudgetWit.AW Require Import AD1g_w AD2i_w AD1d_w AD1f_w CmdWorldH8_w.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.BudgetWit.AW Require AB01r_w.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.BudgetWit.AW Require Import PlanRegen_w.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
(* A hand-off state of flag r is one of flag r's states (A/AB01r.v HS_tfib_r, HS_tfib_list_r). *)
Lemma cmd_HS_tfib_r_In_r : forall r h ch, AB01r_w.HS_tfib_r r h = Some ch -> In ch (AB01r_w.HS_tfib_list_r r).
Proof.
intros r h ch H. unfold AB01r_w.HS_tfib_r, hlookup in H.
destruct (find (fun q => Nat.eqb (fst q) h) (AB01r_w.HSL_r r)) as [q|] eqn:F; [|discriminate H].
injection H as <-. apply find_some in F as [F _]. unfold AB01r_w.HS_tfib_list_r. exact (in_map snd _ _ F).
Qed.
(* The hand-off states of fuzz_command's ASan start-up run, per CONFIG_RSEQ flag, computed in the build from the
   recorded plan (lib/A/AB01r.v). *)
#[export] Instance cmd_start_data : StartData := {|
HS_tfib_r := AB01r_w.HS_tfib_r; HS_tfib_list_r := AB01r_w.HS_tfib_list_r; HS_tfib_list_all := AB01r_w.HS_tfib_list_all;
HS_tfib_r_In_r := cmd_HS_tfib_r_In_r; HS_tfib_r_In := AB01r_w.HS_tfib_r_In |}.
(* The start-up theorem over those states (lib/A/AB1n.v, its certificate lib/A/AB1m.v). *)
#[export] Instance cmd_start_thm : StartThm := {| tfib_startup_T1 := AB1n_w.tfib_startup_T1 |}.
(* The checks of the hand-off states, each by computation over both flags' states (the kernel evaluates each check
   once, at Qed). *)
#[export] Instance cmd_holes_chk : TfibHolesChk.
Proof. constructor. vm_cast_no_check (@eq_refl bool true). Qed.
#[export] Instance cmd_holes_if : TfibHolesIf.
Proof. constructor. vm_cast_no_check (@eq_refl bool true). Qed.
#[export] Instance cmd_entry_check_all : EntryCheckAll.
Proof. constructor. intros [|]; vm_cast_no_check (@eq_refl bool true). Qed.
#[export] Instance cmd_holes_chkB : TfibHolesChkB.
Proof. constructor. vm_cast_no_check (@eq_refl bool true). Qed.
#[export] Instance cmd_holes_imgsh : TfibHolesImgsh.
Proof. constructor. vm_cast_no_check (@eq_refl bool true). Qed.
(* Every a_vis entry of every hand-off state but STK_P has a page-aligned base and length (lib/A/CmdWorldH8.v
   avis8_chk), by computation on lib/A/AB01r.v's states; the instance by tactics, as cmd_holes_stkaux. *)
Lemma cmd_avis8_c : forallb avis8_chk AB01r_w.HS_tfib_list_all = true.
Proof. vm_compute. reflexivity. Qed.
#[export] Instance cmd_avis8 : @TfibAvis8 cmd_start_data.
Proof. constructor. exact cmd_avis8_c. Qed.

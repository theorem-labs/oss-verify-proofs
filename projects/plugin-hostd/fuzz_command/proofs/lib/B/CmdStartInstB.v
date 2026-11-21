(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from the start-up certificate lemmas of proofs/cgif/cgif_file_fuzzer/lib/A (AD1g.v tfib_holes_chk and tfib_holes_if, AD2i.v entry_check_all, AD1d.v tfib_holes_chkB, AD1f.v tfib_holes_imgsh, AD2k.v finv_check_all, each by computation, and AB01.v / AB1n.v's hand-off states and tfib_startup_T1) for plugin-hostd/fuzz_command: the instances of the start-up classes of lib/A/CmdStartCert.v, AD1g.v, AD2i.v, AD1d.v, AD1f.v and AD2k.v from fuzz_command's ASan start-up certificate (lib/A/AB01.v HS_tfib_list, lib/A/AB1n.v tfib_startup_T1); TfibHolesIf joins the per-state checks of lib/A/CmdStartIf0.v .. CmdStartIf4.v, and TfibHolesStkAux is lib/A/StartStkAux.v's tfib_holes_stkaux; TfibAvis8 (lib/A/CmdWorldH8.v, the page alignment of the a_vis entries, a Theorem Labs lane's FMworldH8.v avis8_all) is cmd_avis8_c, by computation. *)
(* Modified by Theorem Labs, 2026-10: copied from this harness's lib/A/CmdStartInst.v, with its module paths changed (lib/A to lib/B, image Asan to AsanUbsan) and its addresses moved to plugin-hostd/fuzz_command's ASan+UBSan build. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the instances are over the hand-off states B/YB01r.v computes in the build and B/YB1n.v's tfib_startup_T1 at that revision, each check by computation over both flags' states. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.plugin_hostd.fuzz_command.images Require Import AsanUbsan.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK15 YK18 YK0c YK0e YK09 YA01 YA0c YA0e YA02 PlanRegen.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB12 YB1h CmdStartCertB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YB01r YB1n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YD1g YD2i YD1d YD1f YD2k YCmdWorldH8.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require StartStkAux.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
(* A hand-off state of flag r is one of flag r's states (B/YB01r.v HS_tfib_r, HS_tfib_list_r). *)
Lemma cmd_HS_tfib_r_In_r : forall r h ch, YB01r.HS_tfib_r r h = Some ch -> In ch (YB01r.HS_tfib_list_r r).
Proof.
intros r h ch H. unfold YB01r.HS_tfib_r, hlookup in H.
destruct (find (fun q => Nat.eqb (fst q) h) (YB01r.HSL_r r)) as [q|] eqn:F; [|discriminate H].
injection H as <-. apply find_some in F as [F _]. unfold YB01r.HS_tfib_list_r. exact (in_map snd _ _ F).
Qed.
(* The hand-off states of fuzz_command's ASan+UBSan start-up run, per CONFIG_RSEQ flag, computed in the build from the
   recorded plan (lib/B/YB01r.v). *)
#[export] Instance cmd_start_data : StartData := {|
HS_tfib_r := YB01r.HS_tfib_r; HS_tfib_list_r := YB01r.HS_tfib_list_r; HS_tfib_list_all := YB01r.HS_tfib_list_all;
HS_tfib_r_In_r := cmd_HS_tfib_r_In_r; HS_tfib_r_In := YB01r.HS_tfib_r_In |}.
(* The start-up theorem over those states (lib/B/YB1n.v, its certificate lib/B/YB1m.v). *)
#[export] Instance cmd_start_thm : StartThm := {| tfib_startup_T1 := YB1n.tfib_startup_T1 |}.
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
#[export] Instance cmd_finv_check_all : FinvCheckAll.
Proof. constructor. vm_cast_no_check (@eq_refl bool true). Qed.
(* The auxv vector and the AT_RANDOM bytes of every hand-off state are covered (lib/B/StartStkAux.v, by
   computation).  By tactics: written as a record, elaborating it ran over 120 s, while constructor + exact takes no
   measurable time. *)
#[export] Instance cmd_holes_stkaux : @TfibHolesStkAux cmd_start_data.
Proof. constructor. exact StartStkAux.tfib_holes_stkaux. Qed.
(* Every a_vis entry of every hand-off state but STK_P has a page-aligned base and length (lib/B/YCmdWorldH8.v
   avis8_chk), by computation on lib/B/YB01r.v's states; the instance by tactics, as cmd_holes_stkaux. *)
Lemma cmd_avis8_c : forallb avis8_chk YB01r.HS_tfib_list_all = true.
Proof. vm_compute. reflexivity. Qed.
#[export] Instance cmd_avis8 : @TfibAvis8 cmd_start_data.
Proof. constructor. exact cmd_avis8_c. Qed.

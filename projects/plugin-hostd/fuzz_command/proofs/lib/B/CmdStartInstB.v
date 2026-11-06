(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from the start-up certificate lemmas of proofs/cgif/cgif_file_fuzzer/lib/A (AD1g.v tfib_holes_chk and tfib_holes_if, AD2i.v entry_check_all, AD1d.v tfib_holes_chkB, AD1f.v tfib_holes_imgsh, AD2k.v finv_check_all, each by computation, and AB01.v / AB1n.v's hand-off states and tfib_startup_T1) for plugin-hostd/fuzz_command: the instances of the start-up classes of lib/A/CmdStartCert.v, AD1g.v, AD2i.v, AD1d.v, AD1f.v and AD2k.v from fuzz_command's ASan start-up certificate (lib/A/AB01.v HS_tfib_list, lib/A/AB1n.v tfib_startup_T1); TfibHolesIf joins the per-state checks of lib/A/CmdStartIf0.v .. CmdStartIf4.v, and TfibHolesStkAux is lib/A/StartStkAux.v's tfib_holes_stkaux; TfibAvis8 (lib/A/CmdWorldH8.v, the page alignment of the a_vis entries, a Theorem Labs lane's FMworldH8.v avis8_all) is cmd_avis8_c, by computation. *)
(* Modified by Theorem Labs, 2026-10: copied from this harness's lib/A/CmdStartInst.v, with its module paths changed (lib/A to lib/B, image Asan to AsanUbsan) and its addresses moved to plugin-hostd/fuzz_command's ASan+UBSan build. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.plugin_hostd.fuzz_command.images Require Import AsanUbsan.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK15 YK18 YK0c YK0e YK09 YA01 YA0c YA0e YA02.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB12 YB1h CmdStartCertB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YB01 YB1n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YD1g YD2i YD1d YD1f YD2k YCmdWorldH8.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require CmdStartIf0B CmdStartIf1B CmdStartIf2B CmdStartIf3B CmdStartIf4B StartStkAux.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
(* The hand-off states of fuzz_command's ASan start-up certificate (lib/B/YB01.v, 50 states). *)
#[export] Instance cmd_start_data : StartData := {| HS_tfib_list := YB01.HS_tfib_list |}.
(* The start-up theorem over those states (lib/B/YB1n.v); HS_tfib of this instance is YB01.HS_tfib. *)
#[export] Instance cmd_start_thm : StartThm := {| tfib_startup_T1 := YB1n.tfib_startup_T1 |}.
(* The checks of the hand-off states, each by computation, as cgif's lemmas prove them (the kernel evaluates each
   check once, at Qed). *)
#[export] Instance cmd_holes_chk : TfibHolesChk.
Proof. constructor. vm_cast_no_check (@eq_refl bool true). Qed.
(* if_chk reads every TFIB_CONST cell of each state: one lemma per state in lib/B/CmdStartIf0B.v .. CmdStartIf4B.v. *)
#[export] Instance cmd_holes_if : TfibHolesIf.
Proof.
constructor. change (@HS_tfib_list cmd_start_data) with YB01.HS_tfib_list.
apply forallb_forall. intros ch Hin. unfold YB01.HS_tfib_list in Hin. cbn [In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
[ exact CmdStartIf0B.if_chk_0 | exact CmdStartIf0B.if_chk_1 | exact CmdStartIf0B.if_chk_2 | exact CmdStartIf0B.if_chk_3 | exact CmdStartIf0B.if_chk_4 | exact CmdStartIf0B.if_chk_5 | exact CmdStartIf0B.if_chk_6 | exact CmdStartIf0B.if_chk_7 | exact CmdStartIf0B.if_chk_8 | exact CmdStartIf0B.if_chk_9 | exact CmdStartIf1B.if_chk_10 | exact CmdStartIf1B.if_chk_11 | exact CmdStartIf1B.if_chk_12 | exact CmdStartIf1B.if_chk_13 | exact CmdStartIf1B.if_chk_14 | exact CmdStartIf1B.if_chk_15 | exact CmdStartIf1B.if_chk_16 | exact CmdStartIf1B.if_chk_17 | exact CmdStartIf1B.if_chk_18 | exact CmdStartIf1B.if_chk_19 | exact CmdStartIf2B.if_chk_20 | exact CmdStartIf2B.if_chk_21 | exact CmdStartIf2B.if_chk_22 | exact CmdStartIf2B.if_chk_23 | exact CmdStartIf2B.if_chk_24 | exact CmdStartIf2B.if_chk_25 | exact CmdStartIf2B.if_chk_26 | exact CmdStartIf2B.if_chk_27 | exact CmdStartIf2B.if_chk_28 | exact CmdStartIf2B.if_chk_29 | exact CmdStartIf3B.if_chk_30 | exact CmdStartIf3B.if_chk_31 | exact CmdStartIf3B.if_chk_32 | exact CmdStartIf3B.if_chk_33 | exact CmdStartIf3B.if_chk_34 | exact CmdStartIf3B.if_chk_35 | exact CmdStartIf3B.if_chk_36 | exact CmdStartIf3B.if_chk_37 | exact CmdStartIf3B.if_chk_38 | exact CmdStartIf3B.if_chk_39 | exact CmdStartIf4B.if_chk_40 | exact CmdStartIf4B.if_chk_41 | exact CmdStartIf4B.if_chk_42 | exact CmdStartIf4B.if_chk_43 | exact CmdStartIf4B.if_chk_44 | exact CmdStartIf4B.if_chk_45 | exact CmdStartIf4B.if_chk_46 | exact CmdStartIf4B.if_chk_47 | exact CmdStartIf4B.if_chk_48 | exact CmdStartIf4B.if_chk_49 ].
Qed.
#[export] Instance cmd_entry_check_all : EntryCheckAll.
Proof. constructor. vm_cast_no_check (@eq_refl bool true). Qed.
#[export] Instance cmd_holes_chkB : TfibHolesChkB.
Proof. constructor. vm_cast_no_check (@eq_refl bool true). Qed.
#[export] Instance cmd_holes_imgsh : TfibHolesImgsh.
Proof. constructor. vm_cast_no_check (@eq_refl bool true). Qed.
#[export] Instance cmd_finv_check_all : FinvCheckAll.
Proof. constructor. vm_cast_no_check (@eq_refl bool true). Qed.
(* The auxv words and the AT_RANDOM blob of every hand-off state are known (lib/B/StartStkAux.v, by computation). *)
(* By tactics: written as a record `{| tfib_holes_stkaux_c := ... |}`, elaborating it ran over 120 s (over 1,200 s with
   StartData implicit), while constructor + exact takes no measurable time. *)
#[export] Instance cmd_holes_stkaux : @TfibHolesStkAux cmd_start_data.
Proof. constructor. exact StartStkAux.tfib_holes_stkaux. Qed.
(* Every a_vis entry of every hand-off state but STK_P has a page-aligned base and length (lib/B/YCmdWorldH8.v avis8_chk),
   by computation on lib/B/YB01.v's states; the instance by tactics, as cmd_holes_stkaux. *)
Lemma cmd_avis8_c : forallb avis8_chk YB01.HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.
#[export] Instance cmd_avis8 : @TfibAvis8 cmd_start_data.
Proof. constructor. exact cmd_avis8_c. Qed.

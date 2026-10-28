(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code"; "segs"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "ok_frame"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open"; "Kx"; "JM"; "md_open"; "@Corelib.Init.Datatypes"; "nat"; "list"; "nil"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "False"; "and"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "triple"; "w_tr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState"; "Jinit"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init"; "pcU"; "phU"; "imgU"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates"; "S_main"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit"; "K_tcons"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states"; "S_M"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec"; "Spec"; "open_may_succeed"; "die"; "msg_cannot_open"; "@Corelib.Init.Nat"; "add"; "@Corelib.Init.Peano"; "le"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "mkEntry"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "ok_pframe"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout"; "valid_entry48"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_copen__G1.Drv_copen_states"; "check_nr"; "check_range"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymCall SymExit Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import InitLayout InitState.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import DriverSpec.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_copen__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_copen__G2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.StartStates OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_open__G1.Drv_open OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_copen__G1.Drv_copen_states OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_copen__G1.Drv_copen_chk1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_copen__G1.Drv_copen_chk2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_copen__G1.Drv_copen_chk3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_copen__G2.Drv_copen_chk4 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_copen__G2.Drv_copen.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma check_range_sound : ltac2:(tb__ "0|0|
S9S9S9S9SeScS27R4R3R2A3SdA3S10S21R4R2A2S22R2S20R4R3A2A2A2SeScS26R6R3A2SdA3F_;F_;Fk;Flen;Fa;Fq;").
Proof.
  intros q a len k H Hk. unfold check_range in H.
  exact (proj1 (forallb_forall _ _) H k ltac:(apply in_seq; lia)).
Qed.

Lemma checks_all : checks_S.
Proof.
  intros q k Hq Hk.
  destruct q as [|[|[|[|q]]]]; [ | | | | lia].
  - exact (check_range_sound 0 0 64 k check_range_0 ltac:(lia)).
  - exact (check_range_sound 1 0 64 k check_range_1 ltac:(lia)).
  - exact (check_range_sound 2 0 64 k check_range_2 ltac:(lia)).
  - exact (check_range_sound 3 0 64 k check_range_3 ltac:(lia)).
Qed.

Section All.
Variable sp brk mb : word.
Variable draw : EntryDraw.
Variable inp : ProcInput.
Hypothesis Hent : ltac2:(tb__ "0|0|
S25S18S23Vsp;Vbrk;Vmb;Vdraw;A4Vinp;A3").
Hypothesis Hinp : valid_input_either inp.
Let argv := in_argv inp.
Let argv1 : list byte := nth 1 argv [].
Let fs := in_fs inp.
Hypothesis Hargc : length argv = 2%nat.
Variable md0 : Model.
Hypothesis Hfds0 : m_fds md0 = std_fds.
Hypothesis Hfs : m_fs md0 = fs.
Variable ok : world -> Prop.
Hypothesis HokK : ltac2:(tb__ "0|0|
SaS1A1S2OF_;F_;S1aS1cVinp;A1R1A2S4S0Vok;R2A3F_;FK;").
Hypothesis HokP : ltac2:(tb__ "0|0|
SaS1A1S2OF_;F_;S1aS1cVinp;A1R1A2S24S0Vok;R2A3F_;FK;").
Hypothesis Hokh : ok_halted ok (Spec inp).

Theorem open_safe : ltac2:(tb__ "0|2|
S1dVargv1;Vfs;A2S5S7Vsp;Vdraw;Vinp;R1A4S13S0Vok;S3S0S6SbS1A1M0S8Vmd0;Vargv1;A2A2S1bR2A4S12SfL_;M1A4F_;Frho;F_;S5S15S0S16S17Vsp;Vdraw;Vinp;R1A7S13S0Vok;S3S0S6G0Vmd0;A2S19R2A4G1A4F_;Frho;F_;").
Proof using Hargc Hent Hfds0 Hfs Hinp HokK HokP Hokh.
  intros Hok rho HJ.
  exact (open_reach_safe sp brk mb draw inp Hent Hinp Hargc md0 Hfds0 Hfs ok HokK HokP
           (copen_safe sp brk mb draw inp Hent Hinp Hargc md0 Hfds0 Hfs ok HokK HokP Hokh checks_all) Hok rho HJ).
Qed.

Theorem cannot_open_exists : ltac2:(tb__ "0|0|
S5S15S0S16S17Vsp;Vdraw;Vinp;R1A7S11S0S3S0S6SbS1A1Vmd0;A2S19R2A4S12SeSaS1A1S14R1A1S1eVfs;S1fVargv1;A1A2A3Lw;A3F_;Frho;").
Proof using Hargc Hent Hfds0 Hfs Hinp.
  intros rho HJ.
  exact (copen_reach_exists sp brk mb draw inp Hent Hinp Hargc md0 _
           (copen_exists sp brk mb draw inp Hent Hinp Hargc md0 Hfds0 Hfs checks_all) rho HJ).
Qed.

Theorem open_exists : ltac2:(tb__ "0|1|
S1dVargv1;Vfs;A2S12OF_;S5S7Vsp;Vdraw;Vinp;R1A4S11S0S3S0S6SbS1A1M0S8Vmd0;Vargv1;A2A2S1bR2A4R3A3F_;Frho;S5S15S0S16S17Vsp;Vdraw;Vinp;R1A7S11S0S3S0S6G0Vmd0;A2S19R2A4R4A3F_;Frho;F_;FQ;F_;").
Proof using Hargc Hent Hfds0 Hfs Hinp. exact (open_reach_exists sp brk mb draw inp Hent Hinp Hargc md0 Hfds0 Hfs). Qed.

End All.

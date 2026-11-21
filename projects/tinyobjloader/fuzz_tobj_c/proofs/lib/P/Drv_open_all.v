(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch model's channel reader as a section hypothesis, LPS 08b1429, passed to copen_safe and copen_exists; the initial valuation's invariant taking the mmap base in the three statements; the main state and malloc's entry state per CONFIG_RSEQ, taken at the run's flag, and JM over the new entry-stack layout, written as plain text; the cannot-open path's loop checks for both values of the flag). *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "ok_frame"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_open__G1.Drv_open"; "Kx"; "JM"; "md_open"; "@Corelib.Init.Datatypes"; "nat"; "list"; "nil"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "False"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "triple"; "w_tr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState"; "Jinit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Init"; "pcP"; "phP"; "imgP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.StartStates"; "S_main"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymExit"; "K_tcons"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_open__G1.Drv_open_states"; "S_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec"; "Spec"; "open_may_succeed"; "die"; "msg_cannot_open"; "@Corelib.Init.Nat"; "add"; "@Corelib.Init.Peano"; "le"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "mkEntry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "ok_pframe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout"; "valid_entry48"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_copen__G1.Drv_copen_states"; "check_nr"; "check_range"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymCall SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import InitLayout InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import DriverSpec.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.StartStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_open__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_copen__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_copen__G2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.StartStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_open__G1.Drv_open_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_open__G1.Drv_open OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_copen__G1.Drv_copen_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_copen__G1.Drv_copen_chk1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_copen__G1.Drv_copen_chk2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_copen__G1.Drv_copen_chk3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_copen__G2.Drv_copen_chk4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_copen__G2.Drv_copen.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

(* The cannot-open path's loop checks hold for both values of the CONFIG_RSEQ flag [b]. *)
Lemma check_range_sound : forall (b : bool) (q a len k : nat),
  check_range b q a len = true -> (a <= k < a + len)%nat -> check_nr b q k = true.
Proof.
  intros b q a len k H Hk. unfold check_range in H.
  exact (proj1 (forallb_forall _ _) H k ltac:(apply in_seq; lia)).
Qed.

Lemma checks_all : checks_S.
Proof.
  intros b q k Hq Hk.
  destruct q as [|[|[|[|q]]]]; [ | | | | lia].
  - exact (check_range_sound b 0 0 64 k (check_range_0 b) ltac:(lia)).
  - exact (check_range_sound b 1 0 64 k (check_range_1 b) ltac:(lia)).
  - exact (check_range_sound b 2 0 64 k (check_range_2 b) ltac:(lia)).
  - exact (check_range_sound b 3 0 64 k (check_range_3 b) ltac:(lia)).
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
Hypothesis Hrdr0 : m_channel_reader md0 = true.
Variable ok : world -> Prop.
Hypothesis HokK : ltac2:(tb__ "0|0|
SaS1A1S2OF_;F_;S1aS1cVinp;A1R1A2S4S0Vok;R2A3F_;FK;").
Hypothesis HokP : ltac2:(tb__ "0|0|
SaS1A1S2OF_;F_;S1aS1cVinp;A1R1A2S24S0Vok;R2A3F_;FK;").
Hypothesis Hokh : ok_halted ok (Spec inp).

Theorem open_safe :
  (open_may_succeed argv1 fs -> forall rho : valuation, JM sp mb draw inp rho ->
     triple segs ok (SP segs (Kx [] (md_open md0 argv1)) (S_M (kb_rseq (in_kernel inp))) rho) (fun _ => False)) ->
  forall rho : valuation, Jinit segs pcP phP sp mb draw inp rho ->
    triple segs ok (SP segs (Kx [] md0) (S_main (kb_rseq (in_kernel inp))) rho) (fun _ => False).
Proof using Hargc Hent Hfds0 Hfs Hrdr0 Hinp HokK HokP Hokh.
  intros Hok rho HJ.
  exact (open_reach_safe sp brk mb draw inp Hent Hinp Hargc md0 Hfds0 Hfs ok HokK HokP
           (copen_safe sp brk mb draw inp Hent Hinp Hargc md0 Hfds0 Hfs Hrdr0 ok HokK HokP Hokh checks_all) Hok rho HJ).
Qed.

Theorem cannot_open_exists : forall rho : valuation, Jinit segs pcP phP sp mb draw inp rho ->
  etriple segs (SP segs (Kx [] md0) (S_main (kb_rseq (in_kernel inp))) rho)
    (fun w => w_tr w = die fs (msg_cannot_open argv1)).
Proof using Hargc Hent Hfds0 Hfs Hrdr0 Hinp.
  intros rho HJ.
  exact (copen_reach_exists sp brk mb draw inp Hent Hinp Hargc md0 _
           (copen_exists sp brk mb draw inp Hent Hinp Hargc md0 Hfds0 Hfs Hrdr0 checks_all) rho HJ).
Qed.

Theorem open_exists : open_may_succeed argv1 fs -> forall Q : world -> Prop,
  (forall rho : valuation, JM sp mb draw inp rho ->
     etriple segs (SP segs (Kx [] (md_open md0 argv1)) (S_M (kb_rseq (in_kernel inp))) rho) Q) ->
  forall rho : valuation, Jinit segs pcP phP sp mb draw inp rho ->
    etriple segs (SP segs (Kx [] md0) (S_main (kb_rseq (in_kernel inp))) rho) Q.
Proof using Hargc Hent Hfds0 Hfs Hinp. exact (open_reach_exists sp brk mb draw inp Hent Hinp Hargc md0 Hfds0 Hfs). Qed.

End All.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.

Import ListNotations.

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac norm_fd32 :=
  repeat match goal with
         | |- context [fd32 AT_FDCWD] =>
             change (fd32 AT_FDCWD) with AT_FDCWD32
         | H : context [fd32 AT_FDCWD] |- _ =>
             change (fd32 AT_FDCWD) with AT_FDCWD32 in H
         | |- context [fd32 ?x] => change (fd32 x) with x
         | H : context [fd32 ?x] |- _ => change (fd32 x) with x in H
         end.

(* [comment removed for export] *)
Ltac fd32_ok :=
  solve [ reflexivity
        | assumption
        | apply fd32_lt31; assumption
        | apply fd32_id; assumption
        | apply fd32_lt31; lia
        | apply fd32_id; lia ].
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_SimInv () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Numbers.BinNums.N"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.PhdrInfo"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.EntryDraw"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.LinuxProcessSem.State.ProcInput"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.LinuxProcessSem.Run.reaches_error"; "LinuxProcessSemantics.LinuxProcessSem.Run.init_config"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.omni_corun"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkEntry"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.never_errors"; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence.modeled"; "LinuxProcessSemantics.LinuxProcessSem.Run.run"].


(* [comment removed for export] *)
Lemma star_inv (segs : list Segment) (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep segs c evs (SNext c') -> Inv c') :
  forall c tr c', Inv c -> star segs c tr c' -> Inv c'.
Proof.
  intros c tr c' HInv Hstar. induction Hstar; [exact HInv|].
  apply IHHstar. eapply Hstep; eauto.
Qed.

(* [comment removed for export] *)
Lemma inv_no_reaches_error (segs : list Segment) (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep segs c evs (SNext c') -> Inv c')
  (Hnoerr : forall c evs, Inv c -> ~ sstep segs c evs SError) :
  forall c, Inv c -> ~ reaches_error segs c.
Proof.
  intros c HInv (tr & c' & evs & Hstar & Hss).
  eapply Hnoerr; [| exact Hss].
  eapply star_inv; eauto.
Qed.

(* [comment removed for export] *)
Lemma inv_coexec (segs : list Segment) (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep segs c evs (SNext c') -> Inv c')
  (Hnoerr : forall c evs, Inv c -> ~ sstep segs c evs SError) :
  forall c, Inv c -> OmniRun.coexec segs c never_errors.
Proof.
  cofix CH. intros c HInv.
  destruct (m_halted (cfg_model c)) as [code |] eqn:Hh.
  - apply coexec_halt; [rewrite Hh; discriminate | exact (fun h => h)].
  - apply coexec_step; [exact Hh | |].
    + intros evs Hss. exfalso. exact (Hnoerr c evs HInv Hss).
    + intros evs c' Hss. exact (CH c' (Hstep c evs c' HInv Hss)).
Qed.

(* [comment removed for export] *)
Lemma no_error_run_corun : ltac2:(CDefT.buildp (gd_tbl_SimInv ()) "Psegs,(0.$1.)Ppc,$2.Pph,$3.Psp,(4.&40.)Pbrk0,(4.&40.)Pmb,(4.&40.)Prnd,$5.Plim,$6.Pinp,$7.P,(8.(9.R9.(:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)))(;.(<.R:.R9.R8.)R3.(=.R7.R6.R5.R4.)R2.$>.)")
(* [comment removed for export] *).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp H. cbn [omni_corun].
  apply no_error_coexec, H.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma no_error_run_modeled : ltac2:(CDefT.buildp (gd_tbl_SimInv ()) "Psegs,(0.$1.)Ppc,$2.Pph,$3.Psp,(4.&40.)Pbrk0,(4.&40.)Pmb,(4.&40.)Prnd,$5.Plim,$6.Pinp,$7.P,(8.(9.R9.(:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)))(?.(10.(<.R:.R9.R8.)R3.(=.R7.R6.R5.R4.)R2.))")
(* [comment removed for export] *).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp H.
  apply modeled_iff. cbn [img_segments].
  eapply coexec_conseq; [apply no_error_run_corun, H | apply never_errors_covered].
Qed.

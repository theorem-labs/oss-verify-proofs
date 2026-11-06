(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common Require Import SimInv ExitSim.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape RegsExt.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import ShapeX.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import LibWritev.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import DivergeSim SpinAlg.

Import ListNotations.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_SRz () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.ABoot.DivergeSim.is_self_jump"; "Corelib.Init.Datatypes.true"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.Run.mi_account_step"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk"; "Corelib.Init.Datatypes.pair"; "WithSegs.to_spinJ"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "LinuxProcessSemantics.LinuxProcessSem.Run.step_to"; "LinuxProcessSemantics.LinuxProcessSem.Run.sstep"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "Corelib.Init.Logic.and"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.Run.SNext"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "WithSegs.spinningJ"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "OSSVerify.KrLib.Lib.Shape.TSet"; "OSSVerify.KrLib.Lib.Shape.node_ok"; "WithSegs.srealizesJ"; "OSSVerify.KrLib.Lib.Shape.t_alt"; "OSSVerify.KrLib.Lib.Shape.t_emit"; "Corelib.Init.Datatypes.unit"; "LinuxProcessSemantics.LinuxProcessSem.Run.cfg_model"; "Corelib.Init.Datatypes.sum"; "Corelib.Init.Datatypes.inl"; "Corelib.Init.Datatypes.inr"; "OSSVerify.KrLib.Lib.Shape.t_alt2"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.Common.ExitSim.is_exit_no"; "OSSVerify.KrLib.Lib.Shape.t_exit"; "stdpp.bitvector.definitions.bv_and"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_gpr"; "stdpp.bitvector.definitions.Z_to_bv"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "Corelib.Init.Peano.le"; "Corelib.Init.Datatypes.length"; "OSSVerify.KrLib.BB.ShapeX.wr_index"; "Corelib.Lists.ListDef.map"; "LinuxProcessSemantics.LinuxProcessSem.State.WriteEv"; "Corelib.Lists.ListDef.firstn"; "Corelib.Init.Specif.proj1_sig"; "Corelib.Init.Datatypes.nat"; "Corelib.Lists.ListDef.skipn"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step"].


Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive to_spinJ : machine_state -> Model -> Prop :=
| tsj_here : forall ms mo,
    ms_svc_pending ms = None -> is_self_jump segs ms = true -> to_spinJ ms mo
| tsj_step : forall ms mo ms' mo',
    ms_svc_pending ms = None ->
    mi_account_step segs ms mo = MachineOk (ms', mo') ->
    to_spinJ ms' mo' -> to_spinJ ms mo
(* [comment removed for export] *)
| tsj_node : forall ms mo,
    (exists e st, sstep segs (mkCfg ms mo) e st) ->
    (forall e st, sstep segs (mkCfg ms mo) e st ->
        e = [] /\ exists ms' mo', st = SNext (mkCfg ms' mo') /\ m_halted mo' = None /\ to_spinJ ms' mo') ->
    to_spinJ ms mo.

(* [comment removed for export] *)
#[using="Type"] Lemma to_spinJ_ind2 : ltac2:(CDefT.buildp (gd_tbl_SRz ()) "PP,P,$0.P,$1.SpP,Pms,$0.Pmo,$1.P,(2.(3.(4.&40.))(5.R2.)(6.(4.&40.)))P,(2.$7.(8.Vsegs,R3.)$9.)A2.R5.R4.R3.P,Pms,$0.Pmo,$1.Pms',$0.Pmo',$1.P,(2.(3.(4.&40.))(5.R4.)(6.(4.&40.)))P,(2.(:.(;.$0.$1.))(<.Vsegs,R5.R4.)(=.(;.$0.$1.)(>.$0.$1.R3.R2.)))P,(?.R4.R3.)P,A2.R9.R5.R4.A2.R:.R8.R7.P,Pms,$0.Pmo,$1.P,(10.(11.$12.)Le,(11.$12.)(10.$13.Lst,$13.(14.Vsegs,(15.R4.R3.)R2.R1.)))P,Pe,(11.$12.)Pst,$13.P,(14.Vsegs,(15.R5.R4.)R2.R1.)(16.(2.(11.$12.)R3.(17.$12.))(10.$0.Lms',$0.(10.$1.Lmo',$1.(16.(2.$13.R4.(18.(15.R2.R1.)))(16.(2.(3.(4.&40.))(19.R1.)(6.(4.&40.)))(16.(?.R2.R1.)A2.R;.R2.R1.))))))A2.R7.R4.R3.Pms,$0.Pmo,$1.P,(?.R2.R1.)A2.R7.R3.R2.")
(* [comment removed for export] *).
Proof.
  intros P Hhere Hstep Hnode. fix IH 3. intros ms mo H.
  destruct H as [ms mo Hs Hj | ms mo ms' mo' Hs Ha H | ms mo Hp Hall].
  - apply Hhere; assumption.
  - eapply Hstep; [exact Hs | exact Ha | exact H | exact (IH ms' mo' H)].
  - apply Hnode; [exact Hp|]. intros e st Hss.
    destruct (Hall e st Hss) as (He & ms' & mo' & Hst & Hh & Hsub).
    split; [exact He|]. exists ms', mo'. split; [exact Hst|]. split; [exact Hh|]. split; [exact Hsub | exact (IH ms' mo' Hsub)].
Qed.

Definition spinningJ (c : config) : Prop :=
  to_spinJ (cfg_ms c) (cfg_model c) /\ m_halted (cfg_model c) = None.

#[using="Type"] Lemma spinningJ_here : ltac2:(CDefT.buildp (gd_tbl_SRz ()) "Pms,$0.Pmo,$1.P,(2.(3.(4.&40.))(5.R2.)(6.(4.&40.)))P,(2.$7.(8.Vsegs,R3.)$9.)P,(2.(3.(4.&40.))(19.R3.)(6.(4.&40.)))(1:.(15.R5.R4.))")
(* [comment removed for export] *).
Proof. intros ms mo Hs Hj Hh. split; [apply tsj_here; assumption | exact Hh]. Qed.

#[using="Type"] Lemma spinningJ_step : ltac2:(CDefT.buildp (gd_tbl_SRz ()) "Pms,$0.Pmo,$1.Pms',$0.Pmo',$1.P,(2.(3.(4.&40.))(5.R4.)(6.(4.&40.)))P,(2.(:.(;.$0.$1.))(<.Vsegs,R5.R4.)(=.(;.$0.$1.)(>.$0.$1.R3.R2.)))P,(1:.(15.R4.R3.))(1:.(15.R7.R6.))")
(* [comment removed for export] *).
Proof.
  intros ms mo ms' mo' Hs Ha [H1 H2]. cbn in H1, H2. split; cbn.
  - eapply tsj_step; eauto.
  - pose proof (mi_account_step_halted segs ms mo ms' mo' Ha) as E. congruence.
Qed.

#[using="Type"] Lemma is_self_jump_eqv : forall ms ms', ms_eqv ms ms' -> is_self_jump segs ms = is_self_jump segs ms'.
Proof.
  intros ms ms' (_ & _ & Hpc & Hsvc & _). unfold is_self_jump, ms_pc. rewrite Hsvc, Hpc. reflexivity.
Qed.

#[using="Type"] Lemma to_spinJ_eqv : forall ms mo, to_spinJ ms mo -> forall ms', ms_eqv ms ms' -> to_spinJ ms' mo.
Proof.
  intros ms mo H. revert ms mo H. apply (to_spinJ_ind2 (fun ms mo => forall ms', ms_eqv ms ms' -> to_spinJ ms' mo)).
  - intros ms mo Hs Hj ms' Heqv. apply tsj_here.
    + destruct Heqv as (_ & _ & _ & Hsvc & _). congruence.
    + rewrite <- (is_self_jump_eqv ms ms' Heqv). exact Hj.
  - intros ms mo ms1 mo1 Hs Ha H IH ms' Heqv.
    pose proof (account_step_eqv segs ms ms' mo Heqv) as K. rewrite Ha in K.
    destruct (mi_account_step segs ms' mo) as [[b mo1']| |] eqn:E; try contradiction.
    destruct K as [Kb <-].
    eapply tsj_step; [| exact E | apply IH; exact Kb].
    destruct Heqv as (_ & _ & _ & Hsvc & _). congruence.
  - intros ms mo (e0 & st0 & Hs0) Hall ms1 Heqv.
    assert (CE : cfg_eqv (mkCfg ms mo) (mkCfg ms1 mo)) by (split; [exact Heqv | reflexivity]).
    apply tsj_node.
    + destruct (sstep_cfg_eqv segs _ _ e0 st0 CE Hs0) as (X' & HsX & _). exists e0, X'. exact HsX.
    + intros e st1 Hs1.
      destruct (sstep_cfg_eqv segs _ _ e st1 (cfg_eqv_sym _ _ CE) Hs1) as (X & HsX & HX).
      destruct (Hall e X HsX) as (He & ms' & mo' & -> & Hh & _ & IH).
      split; [exact He|].
      destruct st1 as [[ms1' mo1']|]; cbn in HX; [|contradiction].
      destruct HX as [HXms HXmo]. cbn in HXms, HXmo. subst mo'.
      exists ms1', mo1'. split; [reflexivity|]. split; [exact Hh|]. apply IH. apply ms_eqv_sym. exact HXms.
Qed.

#[using="Type"] Lemma cfg_eqv_trans : forall a b c, cfg_eqv a b -> cfg_eqv b c -> cfg_eqv a c.
Proof. intros a b c [H1 H2] [G1 G2]. split; [eapply ms_eqv_trans; eauto | congruence]. Qed.

#[using="Type"] Lemma spinningJ_eqv : forall c c', spinningJ c -> cfg_eqv c c' -> spinningJ c'.
Proof.
  intros [ms mo] [ms' mo'] [H1 H2] [E1 E2]. cbn in *. subst mo'. split; cbn; [| exact H2].
  eapply to_spinJ_eqv; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive srealizesJ (c : config) (T : TSet) : Prop :=
| SRZJ : (forall c', cfg_eqv c c' -> srealizes segs c' T) -> srealizesJ c T.

#[using="Type"] Lemma srzJ_srz : forall c T, srealizesJ c T -> srealizes segs c T.
Proof. intros c T [H]. apply H. apply cfg_eqv_refl. Qed.

#[using="Type"] Lemma srzJ_eqv : forall c T, srealizesJ c T -> forall c', cfg_eqv c c' -> srealizesJ c' T.
Proof. intros c T [H] c' E. constructor. intros c'' E'. apply H. eapply cfg_eqv_trans; eauto. Qed.

#[using="Type"] Lemma srzJ_node : ltac2:(CDefT.buildp (gd_tbl_SRz ()) "Pc,$1;.PI,StPevs,P,R1.(11.$12.)Pnx,P,R2.$1;.PT,P,R3.$1<.Pi0,R4.P,(1=.Vsegs,R6.R5.R4.R3.)P,Pi,R6.(1>.A1.R5.R1.A1.R4.R1.)(1>.R8.(1?.R7.Li,R7.(20.A1.R7.R1.A1.R5.R1.)))")
(* [comment removed for export] *).
Proof.
  intros c I evs nx T i0 [Hcomp Hsound] Hcont. constructor. intros c' Heqv.
  set (I' := { p : I * config | sstep segs c' (evs (fst p)) (SNext (snd p)) /\ cfg_eqv (nx (fst p)) (snd p) }).
  assert (Hfib : forall i, exists X', sstep segs c' (evs i) (SNext X') /\ cfg_eqv (nx i) X').
  { intros i. destruct (sstep_cfg_eqv segs c c' (evs i) (SNext (nx i)) Heqv (Hcomp i)) as (X' & Hs & HX).
    destruct X' as [c''|]; cbn in HX; [|contradiction]. exists c''. split; assumption. }
  destruct (Hfib i0) as (X0 & HX0s & HX0e).
  apply (srz_conseq segs c' (ShapeAlg.t_alt (fun p : I' => ShapeAlg.t_emit (evs (fst (proj1_sig p))) (T (fst (proj1_sig p)))))).
  + apply (srz_node segs c' I' (fun p => evs (fst (proj1_sig p))) (fun p => snd (proj1_sig p))
             (fun p => T (fst (proj1_sig p))) (exist _ (i0, X0) (conj HX0s HX0e))).
    * split.
      -- intros [[i X] [Hs HX]]. cbn. exact Hs.
      -- intros e st Hs.
         destruct (sstep_cfg_eqv segs c' c e st (cfg_eqv_sym _ _ Heqv) Hs) as (X & HsX & HX).
         destruct (Hsound e X HsX) as (i & -> & ->).
         destruct st as [c''|]; cbn in HX; [|contradiction].
         exists (exist _ (i, c'') (conj Hs (cfg_eqv_sym _ _ HX))). cbn. split; reflexivity.
    * intros [[i X] [Hs HX]]. cbn. destruct (Hcont i) as [Hi]. apply Hi. exact HX.
  + intros tr. split.
    * intros [[[i X] [Hs HX]] Htr]. cbn in Htr. exists i. exact Htr.
    * intros [i Htr]. destruct (Hfib i) as (X & Hs & HX).
      exists (exist _ (i, X) (conj Hs HX)). cbn. exact Htr.
Qed.

#[using="Type"] Lemma srzJ_halt : forall c, m_halted (cfg_model c) <> None -> srealizesJ c t_nil.
Proof. intros c Hh. constructor. intros c' [_ E]. apply srz_halt. rewrite <- E. exact Hh. Qed.

#[using="Type"] Lemma srzJ_conseq : forall c T T', srealizesJ c T -> t_eq T T' -> srealizesJ c T'.
Proof. intros c T T' [H] Heq. constructor. intros c' E. eapply srz_conseq; [apply H; exact E | exact Heq]. Qed.

#[using="Type"] Lemma srzJ_nonempty : forall c T, srealizesJ c T -> T [].
Proof. intros c T H. eapply srealizes_nonempty. apply srzJ_srz. exact H. Qed.

#[using="Type"] Lemma srzJ_pclosed : forall c T, srealizesJ c T -> forall tr tr', T tr -> is_prefix tr' tr -> T tr'.
Proof. intros c T H. eapply srealizes_pclosed. apply srzJ_srz. exact H. Qed.

#[using="Type"] Lemma srzJ_obs_iff : forall c T, srealizesJ c T -> forall tr, obs_trace segs c tr <-> T tr.
Proof. intros c T H. apply srealizes_obs_iff. apply srzJ_srz. exact H. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srz_of_realizes : forall c T, realizes segs c T -> srealizes segs c T.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
  - exact (srz_node segs c I evs nx T i0 Hnode IH).
  - exact (srz_halt segs c (halted_ok_not_none c Hh)).
  - exact (srz_conseq segs c T T' IH Heq).
Qed.

#[using="Type"] Lemma srzJ_of_realizes : forall c T, realizes segs c T -> srealizesJ c T.
Proof.
  intros c T H. constructor. intros c' E. apply srz_of_realizes. eapply realizes_eqv; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma srzJ_silent1 : ltac2:(CDefT.buildp (gd_tbl_SRz ()) "Pc,$1;.Pc',$1;.PT,$1<.P,(1=.Vsegs,R3.$21.L,$21.(17.$12.)L,$21.R3.)P,(1>.R3.R2.)(1>.R5.R3.)")
(* [comment removed for export] *).
Proof.
  intros c c' T Hnode Hc.
  apply (srzJ_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (srzJ_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode). intros []; exact Hc.
  - eapply t_eq_trans; [ apply (t_alt_unit (fun _ : unit => t_emit [] T)) | apply t_emit_nil_eq; eapply srzJ_nonempty; exact Hc ].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma node_acc_step : ltac2:(CDefT.buildp (gd_tbl_SRz ()) "Pms,$0.Pmo,$1.Pms',$0.Pmo',$1.P,(2.(3.(4.&40.))(19.R3.)(6.(4.&40.)))P,(2.(3.(4.&40.))(5.R5.)(6.(4.&40.)))P,(2.(:.(;.$0.$1.))(<.Vsegs,R6.R5.)(=.(;.$0.$1.)(>.$0.$1.R4.R3.)))(1=.Vsegs,(15.R7.R6.)$21.L,$21.(17.$12.)L,$21.(15.R6.R5.))")
(* [comment removed for export] *).
Proof.
  intros ms mo ms' mo' Hh Hsvc Hacc. split.
  - intros _. apply sstep_instr; assumption.
  - intros e st Hss. exists tt.
    inversion Hss; subst; try congruence.
    match goal with H : mi_account_step segs ms mo = MachineOk _ |- _ => rewrite Hacc in H; inversion H; subst end.
    split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive srealizesJ0 (c : config) (T : TSet) : Prop :=
| SRZJ0 : (forall c', cfg_eqv c c' -> srealizes0 segs c' T) -> srealizesJ0 c T.

#[using="Type"] Lemma srzJ0_srz0 : forall c T, srealizesJ0 c T -> srealizes0 segs c T.
Proof. intros c T [H]. apply H. apply cfg_eqv_refl. Qed.

#[using="Type"] Lemma srzJ0_eqv : forall c T, srealizesJ0 c T -> forall c', cfg_eqv c c' -> srealizesJ0 c' T.
Proof. intros c T [H] c' E. constructor. intros c'' E'. apply H. eapply cfg_eqv_trans; eauto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srzJ0_of_srzJ : forall c T, srealizesJ c T -> srealizesJ0 c T.
Proof. intros c T [H]. constructor. intros c' E. apply srealizes_srealizes0. apply H. exact E. Qed.

#[using="Type"] Lemma srzJ0_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config) (T : I -> TSet) (i0 : I),
  node_ok segs c I evs nx -> (forall i, srealizesJ0 (nx i) (T i)) ->
  srealizesJ0 c (t_alt (fun i => t_emit (evs i) (T i))).
Proof.
  intros c I evs nx T i0 [Hcomp Hsound] Hcont. constructor. intros c' Heqv.
  set (I' := { p : I * config | sstep segs c' (evs (fst p)) (SNext (snd p)) /\ cfg_eqv (nx (fst p)) (snd p) }).
  assert (Hfib : forall i, exists X', sstep segs c' (evs i) (SNext X') /\ cfg_eqv (nx i) X').
  { intros i. destruct (sstep_cfg_eqv segs c c' (evs i) (SNext (nx i)) Heqv (Hcomp i)) as (X' & Hs & HX).
    destruct X' as [c''|]; cbn in HX; [|contradiction]. exists c''. split; assumption. }
  destruct (Hfib i0) as (X0 & HX0s & HX0e).
  apply (srz0_conseq segs c' (ShapeAlg.t_alt (fun p : I' => ShapeAlg.t_emit (evs (fst (proj1_sig p))) (T (fst (proj1_sig p)))))).
  + apply (srz0_node segs c' I' (fun p => evs (fst (proj1_sig p))) (fun p => snd (proj1_sig p))
             (fun p => T (fst (proj1_sig p))) (exist _ (i0, X0) (conj HX0s HX0e))).
    * split.
      -- intros [[i X] [Hs HX]]. cbn. exact Hs.
      -- intros e st Hs.
         destruct (sstep_cfg_eqv segs c' c e st (cfg_eqv_sym _ _ Heqv) Hs) as (X & HsX & HX).
         destruct (Hsound e X HsX) as (i & -> & ->).
         destruct st as [c''|]; cbn in HX; [|contradiction].
         exists (exist _ (i, c'') (conj Hs (cfg_eqv_sym _ _ HX))). cbn. split; reflexivity.
    * intros [[i X] [Hs HX]]. cbn. destruct (Hcont i) as [Hi]. apply Hi. exact HX.
  + intros tr. split.
    * intros [[[i X] [Hs HX]] Htr]. cbn in Htr. exists i. exact Htr.
    * intros [i Htr]. destruct (Hfib i) as (X & Hs & HX).
      exists (exist _ (i, X) (conj Hs HX)). cbn. exact Htr.
Qed.

#[using="Type"] Lemma srzJ0_halt : forall c, m_halted (cfg_model c) <> None -> srealizesJ0 c t_nil.
Proof. intros c Hh. constructor. intros c' [_ E]. apply srz0_halt. rewrite <- E. exact Hh. Qed.

#[using="Type"] Lemma srzJ0_conseq : forall c T T', srealizesJ0 c T -> t_eq T T' -> srealizesJ0 c T'.
Proof. intros c T T' [H] Heq. constructor. intros c' E. eapply srz0_conseq; [apply H; exact E | exact Heq]. Qed.

#[using="Type"] Lemma srzJ0_nonempty : forall c T, srealizesJ0 c T -> T [].
Proof. intros c T H. eapply srealizes0_nonempty. apply srzJ0_srz0. exact H. Qed.

#[using="Type"] Lemma srzJ0_pclosed : forall c T, srealizesJ0 c T -> forall tr tr', T tr -> is_prefix tr' tr -> T tr'.
Proof. intros c T H. eapply srealizes0_pclosed. apply srzJ0_srz0. exact H. Qed.

#[using="Type"] Lemma srzJ0_obs_iff : forall c T, srealizesJ0 c T -> forall tr, obs_trace segs c tr <-> T tr.
Proof. intros c T H. apply srealizes0_obs_iff. apply srzJ0_srz0. exact H. Qed.

#[using="Type"] Lemma srzJ0_of_realizes : forall c T, realizes segs c T -> srealizesJ0 c T.
Proof. intros c T H. apply srzJ0_of_srzJ. apply srzJ_of_realizes. exact H. Qed.

#[using="Type"] Lemma srzJ0_silent1 : forall c c' T,
  node_ok segs c unit (fun _ => []) (fun _ => c') -> srealizesJ0 c' T -> srealizesJ0 c T.
Proof.
  intros c c' T Hnode Hc.
  apply (srzJ0_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (srzJ0_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode). intros []; exact Hc.
  - eapply t_eq_trans; [ apply (t_alt_unit (fun _ : unit => t_emit [] T)) | apply t_emit_nil_eq; eapply srzJ0_nonempty; exact Hc ].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srzJ0_to_spinJ : forall ms mo, to_spinJ ms mo -> m_halted mo = None -> srealizesJ0 (mkCfg ms mo) t_nil.
Proof.
  intros ms mo H. revert ms mo H.
  apply (to_spinJ_ind2 (fun ms mo => m_halted mo = None -> srealizesJ0 (mkCfg ms mo) t_nil)).
  - intros ms mo Hs Hj Hh. constructor. intros [ms' mo'] [E1 E2]. cbn in E1, E2. subst mo'.
    apply srz0_spin; cbn; [| exact Hh]. apply is_self_jump_to_spin. rewrite <- (is_self_jump_eqv ms ms' E1). exact Hj.
  - intros ms mo ms' mo' Hs Ha _ IH Hh.
    eapply srzJ0_silent1; [apply (node_acc_step ms mo ms' mo' Hh Hs Ha)|].
    apply IH. pose proof (mi_account_step_halted segs ms mo ms' mo' Ha) as E. congruence.
  - intros ms mo (e0 & st0 & Hs0) Hall Hh.
    set (I := { c' : config | sstep segs (mkCfg ms mo) [] (SNext c') }).
    destruct (Hall e0 st0 Hs0) as (E0 & ms0 & mo0 & Est0 & _). subst e0 st0.
    pose (i0 := exist (fun c' => sstep segs (mkCfg ms mo) [] (SNext c')) (mkCfg ms0 mo0) Hs0 : I).
    apply (srzJ0_conseq (mkCfg ms mo) (t_alt (fun _ : I => t_emit [] t_nil))).
    + apply (srzJ0_node (mkCfg ms mo) I (fun _ => []) (fun i => proj1_sig i) (fun _ => t_nil) i0).
      * split.
        -- intros [c' Hc']. exact Hc'.
        -- intros e st Hss. destruct (Hall e st Hss) as (-> & ms' & mo' & -> & _).
           exists (exist _ (mkCfg ms' mo') Hss). split; reflexivity.
      * intros [c' Hc']. cbn [proj1_sig]. destruct (Hall [] (SNext c') Hc') as (_ & ms' & mo' & E & Hh' & _ & IH).
        inversion E; subst. apply IH. exact Hh'.
    + intros tr. split.
      * intros [_ Htr]. apply (proj1 (t_emit_nil_eq t_nil eq_refl tr)). exact Htr.
      * intros Htr. exists i0. apply (proj2 (t_emit_nil_eq t_nil eq_refl tr)). exact Htr.
Qed.

#[using="Type"] Lemma srzJ0_spin : forall c, spinningJ c -> srealizesJ0 c t_nil.
Proof. intros [ms mo] [H1 H2]. cbn in H1, H2. apply srzJ0_to_spinJ; assumption. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma spinningJ_node : ltac2:(CDefT.buildp (gd_tbl_SRz ()) "Pc,$1;.P,(2.(3.(4.&40.))(19.(22.R1.))(6.(4.&40.)))P,(10.(11.$12.)Le,(11.$12.)(10.$13.Lst,$13.(14.Vsegs,R4.R2.R1.)))P,Pe,(11.$12.)Pst,$13.P,(14.Vsegs,R5.R2.R1.)(16.(2.(11.$12.)R3.(17.$12.))(10.$1;.Lc',$1;.(16.(2.$13.R3.(18.R1.))(1:.R1.))))(1:.R4.)")
(* [comment removed for export] *).
Proof.
  intros [ms mo] Hh Hp Hall. cbn in Hh. split; [| exact Hh]. cbn. apply tsj_node; [exact Hp|].
  intros e st Hs. destruct (Hall e st Hs) as (He & [ms' mo'] & -> & [H1 H2]). cbn in H1, H2.
  split; [exact He|]. exists ms', mo'. split; [reflexivity|]. split; assumption.
Qed.


#[using="Type"] Lemma srzJ_emit1 : ltac2:(CDefT.buildp (gd_tbl_SRz ()) "Pc,$1;.Pc',$1;.Pe,(11.$12.)PT,$1<.P,(1=.Vsegs,R4.$21.L,$21.R3.L,$21.R4.)P,(1>.R4.R2.)(1>.R6.(20.R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros c c' e T Hnode Hc.
  apply (srzJ_conseq c (t_alt (fun _ : unit => t_emit e T))).
  - apply (srzJ_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode). intros []; exact Hc.
  - apply t_alt_unit.
Qed.

#[using="Type"] Lemma srzJ_alt2 : ltac2:(CDefT.buildp (gd_tbl_SRz ()) "Pc,$1;.PIA,StPIB,StPnx,P,(23.R2.R1.)$1;.PA,$1<.PB,$1<.Pa0,R5.Pb0,R5.P,(1=.Vsegs,R8.(23.R7.R6.)L,(23.R7.R6.)(17.$12.)R5.)P,Pi,R8.(1>.A1.R7.(24.R9.R8.R1.)R6.)P,Pi,R8.(1>.A1.R8.(25.R:.R9.R1.)R6.)(1>.R;.(26.R7.R6.))")
(* [comment removed for export] *).
Proof.
  intros c IA IB nx A B a0 b0 Hnode HA HB.
  assert (HA0 : A []) by (eapply srzJ_nonempty; apply (HA a0)).
  assert (HB0 : B []) by (eapply srzJ_nonempty; apply (HB b0)).
  apply (srzJ_conseq c (t_alt (fun i : IA + IB => t_emit [] (match i with inl _ => A | inr _ => B end)))).
  - apply (srzJ_node c (IA + IB) (fun _ => []) nx (fun i => match i with inl _ => A | inr _ => B end) (inl a0) Hnode).
    intros [i|i]; [apply HA | apply HB].
  - intro tr. unfold t_alt2. split.
    + intros [[i|i] Hi]; [ left; exact (proj1 (t_emit_nil_eq A HA0 tr) Hi) | right; exact (proj1 (t_emit_nil_eq B HB0 tr) Hi) ].
    + intros [H | H]; [ exists (inl a0); exact (proj2 (t_emit_nil_eq A HA0 tr) H) | exists (inr b0); exact (proj2 (t_emit_nil_eq B HB0 tr) H) ].
Qed.

#[using="Type"] Lemma srzJ_exit : ltac2:(CDefT.buildp (gd_tbl_SRz ()) "Pms,$0.Pmodel,$1.Px8,(4.&40.)P,(2.(3.(4.&40.))(19.R2.)(6.(4.&40.)))P,(2.(3.(4.&40.))(5.R4.)(27.(4.&40.)R2.))P,(28.R3.)(1>.(15.R6.R5.)(29.(2:.&40.(2;.R6.#0.)(2<.&40.+??.))(2=.R5.)))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 Hh Hsvc Hx8. apply srzJ_of_realizes. apply rz_exit with (x8 := x8); assumption.
Qed.

#[using="Type"] Lemma srzJ_wall : ltac2:(CDefT.buildp (gd_tbl_SRz ()) "Pc,$1;.Pch,(4.&40.)Pbs,(11.(4.&8.))PK,$1<.P,(2>.#1.(2?.(4.&8.)R2.))P,A1.R2.(17.$12.)P,(1>.R6.(1?.(30.R4.)Li,(30.R4.)(20.(31.(4.&8.)$12.(32.R6.)(33.(4.&8.)(34.$35.Ln,$35.(16.(2>.#1.R1.)(2>.R1.(2?.(4.&8.)R6.)))R1.)R5.))(20.(31.(4.&8.)$12.(32.R6.)(36.(4.&8.)(34.$35.Ln,$35.(16.(2>.#1.R1.)(2>.R1.(2?.(4.&8.)R6.)))R1.)R5.))R4.))))(1>.R7.(20.(31.(4.&8.)$12.(32.R6.)R5.)R4.))")
(* [comment removed for export] *).
Proof. intros c ch bs K Hnb HK H. eapply srzJ_conseq; [exact H | apply t_alt_wall; assumption]. Qed.

#[using="Type"] Lemma srzJ_regs_ext0 : forall {fx : FPState} (R R' : bvmap 5 word) pc mem rom mo T,
  (forall r : reg, bv_unsigned r <> 0%Z -> reg_get R r = reg_get R' r) ->
  srealizesJ (mkCfg (mkst R pc mem rom) mo) T ->
  srealizesJ (mkCfg (mkst R' pc mem rom) mo) T.
Proof.
  intros fx R R' pc mem rom mo T HR H. eapply srzJ_eqv; [exact H|]. split; [|reflexivity]. cbn. repeat split; auto; intros r; reflexivity.
Qed.

#[using="Type"] Lemma srzJ_getr_ext : forall {fx : FPState} (R R' : bvmap 5 word) pc mem rom mo T,
  (forall r : reg, getr R r = getr R' r) ->
  srealizesJ (mkCfg (mkst R pc mem rom) mo) T ->
  srealizesJ (mkCfg (mkst R' pc mem rom) mo) T.
Proof.
  intros fx R R' pc mem rom mo T HR H. eapply srzJ_regs_ext0; [|exact H].
  intros r Hr. specialize (HR r). unfold getr in HR.
  destruct (bv_eqb r 0) eqn:E; [|exact HR].
  exfalso. apply Hr. unfold bv_eqb in E. apply Z.eqb_eq in E. exact E.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srzJ_step : ltac2:(CDefT.buildp (gd_tbl_SRz ()) "Pms,$0.Pmodel,$1.Pms',$0.PT,$1<.P,(2.(3.(4.&40.))(19.R3.)(6.(4.&40.)))P,(2.(11.(;.(4.&40.)(4.&40.)))(37.R4.)(17.(;.(4.&40.)(4.&40.))))P,(2.(3.(4.&40.))(5.R6.)(6.(4.&40.)))P,(2.(:.$0.)(38.Vsegs,R7.)(=.$0.R5.))P,(1>.(15.R6.R7.)R5.)(1>.(15.R9.R8.)R6.)")
(* [comment removed for export] *).
Proof. intros ms model ms' T Hh Hl Hs Hst Hc. eapply srzJ_silent1; [apply node_instr; eassumption | exact Hc]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fo_excusedJ (c : config) (e : list event) (c' : config) : Prop :=
  forall c1 c1', cfg_eqv c c1 -> cfg_eqv c' c1' -> ~ fo_step segs c1 e c1'.

#[using="Type"] Lemma fo_excusedJ_not_fo_step : forall c e c', fo_excusedJ c e c' -> ~ fo_step segs c e c'.
Proof. intros c e c' H. apply H; apply cfg_eqv_refl. Qed.

#[using="Type"] Lemma fo_excusedJ_eqv : forall c e c' d d',
  fo_excusedJ c e c' -> cfg_eqv c d -> cfg_eqv c' d' -> fo_excusedJ d e d'.
Proof.
  intros c e c' d d' H E E' c1 c1' E1 E1'. apply H; eapply cfg_eqv_trans; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srzJ_node_sp : forall c (I : Type) (evs : I -> list event) (nx : I -> config) (T : I -> TSet) (i0 : I),
  node_ok segs c I evs nx ->
  (forall i, srealizesJ (nx i) (T i) \/ (srealizesJ0 (nx i) (T i) /\ fo_excusedJ c (evs i) (nx i))) ->
  srealizesJ c (t_alt (fun i => t_emit (evs i) (T i))).
Proof.
  intros c I evs nx T i0 [Hcomp Hsound] Hcont. constructor. intros c' Heqv.
  set (I' := { p : I * config | sstep segs c' (evs (fst p)) (SNext (snd p)) /\ cfg_eqv (nx (fst p)) (snd p) }).
  assert (Hfib : forall i, exists X', sstep segs c' (evs i) (SNext X') /\ cfg_eqv (nx i) X').
  { intros i. destruct (sstep_cfg_eqv segs c c' (evs i) (SNext (nx i)) Heqv (Hcomp i)) as (X' & Hs & HX).
    destruct X' as [c''|]; cbn in HX; [|contradiction]. exists c''. split; assumption. }
  destruct (Hfib i0) as (X0 & HX0s & HX0e).
  apply (srz_conseq segs c' (ShapeAlg.t_alt (fun p : I' => ShapeAlg.t_emit (evs (fst (proj1_sig p))) (T (fst (proj1_sig p)))))).
  + apply (srz_node_sp segs c' I' (fun p => evs (fst (proj1_sig p))) (fun p => snd (proj1_sig p))
             (fun p => T (fst (proj1_sig p))) (exist _ (i0, X0) (conj HX0s HX0e))).
    * split.
      -- intros [[i X] [Hs HX]]. cbn. exact Hs.
      -- intros e st Hs.
         destruct (sstep_cfg_eqv segs c' c e st (cfg_eqv_sym _ _ Heqv) Hs) as (X & HsX & HX).
         destruct (Hsound e X HsX) as (i & -> & ->).
         destruct st as [c''|]; cbn in HX; [|contradiction].
         exists (exist _ (i, c'') (conj Hs (cfg_eqv_sym _ _ HX))). cbn. split; reflexivity.
    * intros [[i X] [Hs HX]]. cbn. destruct (Hcont i) as [[Hi] | [[Hi] Hex]].
      -- left. apply Hi. exact HX.
      -- right. split; [apply Hi; exact HX |]. apply Hex; [exact Heqv | exact HX].
  + intros tr. split.
    * intros [[[i X] [Hs HX]] Htr]. cbn in Htr. exists i. exact Htr.
    * intros [i Htr]. destruct (Hfib i) as (X & Hs & HX).
      exists (exist _ (i, X) (conj Hs HX)). cbn. exact Htr.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srzJ_alt2_sp : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet) (a0 : IA) (b0 : IB),
  node_ok segs c (IA + IB) (fun _ => []) nx ->
  (forall i, srealizesJ (nx (inl i)) A \/ (srealizesJ0 (nx (inl i)) A /\ fo_excusedJ c [] (nx (inl i)))) ->
  (forall i, srealizesJ (nx (inr i)) B) ->
  srealizesJ c (t_alt2 A B).
Proof.
  intros c IA IB nx A B a0 b0 Hnode HA HB.
  assert (HA0 : A []).
  { destruct (HA a0) as [H | [H _]]; [eapply srzJ_nonempty; exact H | eapply srzJ0_nonempty; exact H]. }
  assert (HB0 : B []) by (eapply srzJ_nonempty; apply (HB b0)).
  apply (srzJ_conseq c (t_alt (fun i : IA + IB => t_emit [] (match i with inl _ => A | inr _ => B end)))).
  - apply (srzJ_node_sp c (IA + IB) (fun _ => []) nx (fun i => match i with inl _ => A | inr _ => B end) (inl a0) Hnode).
    intros [i|i]; [apply HA | left; apply HB].
  - intro tr. unfold t_alt2. split.
    + intros [[i|i] Hi]; [ left; exact (proj1 (t_emit_nil_eq A HA0 tr) Hi) | right; exact (proj1 (t_emit_nil_eq B HB0 tr) Hi) ].
    + intros [H | H]; [ exists (inl a0); exact (proj2 (t_emit_nil_eq A HA0 tr) H) | exists (inr b0); exact (proj2 (t_emit_nil_eq B HB0 tr) H) ].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma refusal_fo_excusedJ : forall ms model x8 eff' model' evs' c',
  ms_svc_pending ms = Some x8 ->
  injected_family_off forced_only_cfg (sys_input segs ms x8) = true ->
  syscall_spec (sys_input segs ms x8) model (Ok eff' model' evs') ->
  refusal_b (sys_input segs ms x8) model (eff_ret eff') = false ->
  refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms c') 0) = true ->
  fo_excusedJ (mkCfg ms model) [] c'.
Proof.
  intros ms model x8 eff' model' evs' c' Hsvc Hoff Hspec Hnr Hr [ms1 mo1] c1' [E1 E2] E'. cbn in E1, E2. subst mo1.
  assert (Hsvc1 : ms_svc_pending ms1 = Some x8) by (destruct E1 as (_ & _ & _ & Hs & _); congruence).
  rewrite (sys_input_eqv segs ms ms1 x8 E1) in Hoff, Hspec, Hnr, Hr.
  rewrite (ms_gpr_eqv (cfg_ms c') (cfg_ms c1') 0 (proj1 E') ltac:(lia)) in Hr.
  exact (refusal_not_fo_step segs ms1 model x8 eff' model' evs' c1' Hsvc1 Hoff Hspec Hnr Hr).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma spurious_fo_excusedJ : forall ms model x8 eff mo',
  ms_svc_pending ms = Some x8 ->
  spurious_refusal_cfg forced_only_cfg (sys_input segs ms x8) model eff ->
  fo_excusedJ (mkCfg ms model) [] (mkCfg (advance_past_svc (apply_effect ms eff)) mo').
Proof.
  intros ms model x8 eff mo' Hsvc (Hoff & Hr & eff' & m' & evs' & Hspec & Hnr).
  eapply refusal_fo_excusedJ; [exact Hsvc | exact Hoff | exact Hspec | exact Hnr |].
  cbn [cfg_ms]. rewrite ms_gpr0_advance_apply_effect. exact Hr.
Qed.

End WithSegs.

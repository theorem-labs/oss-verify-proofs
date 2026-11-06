(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes AEvt.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Monad MSafe.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_ImplAevt () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.Nodes.minv"; "OSSVerify.KrLib.Lib.Exec.evt"; "OSSVerify.KrLib.Lib.AEvt.aevt"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"].


Definition is_mm (n : node) : Prop :=
  match n with NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ => True | _ => False end.

Fixpoint tmm {R} (t : itree node R) : Prop :=
  match t with
  | Ret _ => True
  | Vis n k => is_mm n /\ forall r, tmm (k r)
  end.

Lemma tmm_bind {A B} : forall (t : itree node A) (f : A -> itree node B),
  tmm t -> (forall a, tmm (f a)) -> tmm (ITree.bind node t f).
Proof.
  induction t as [r|n k IH]; intros f Ht Hf; cbn in *; [apply Hf|].
  destruct Ht as [Hn Hk]. split; [exact Hn|]. intros r. apply IH; auto.
Qed.

Lemma tmm_ebind {A B} : forall (t : itree node (exc A)) (f : A -> itree node (exc B)),
  tmm t -> (forall a, tmm (f a)) -> tmm (ebind t f).
Proof.
  intros t f Ht Hf. unfold ebind. apply tmm_bind; [exact Ht|]. intros [|a]; [exact I| apply Hf].
Qed.

Lemma tmm_enode {A} : forall n (pl : resp -> option A), is_mm n -> tmm (enode n pl).
Proof. intros n pl Hn. cbn. split; [exact Hn|]. intros r. destruct (pl r); exact I. Qed.

Section Bridge.
Variable segs : list Segment.

#[using="Type"] Lemma evt_aevt : ltac2:(CDefT.buildp (gd_tbl_ImplAevt ()) "PQ,P,$0.SpPK,P,$1.SpPms,$0.Pmo,$2.P,(3.(4.(5.&40.))(6.R1.)(7.(5.&40.)))P,(8.R2.)P,(9.Vsegs,R6.R4.)P,Pms',$0.P,A1.R8.R1.(:.Vsegs,R8.(;.R2.R6.))(:.Vsegs,R7.(;.R6.R5.))")
(* [comment removed for export] *).
Proof.
  (intros Q K ms mo Hh Hm dd_H; ddestruct dd_H as (ms' & Hs & HQ); intros HK). eapply aevt_msteps; [exact Hh| exact Hm| exact Hs|]. apply HK, HQ.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma impl_twf_aevt {R} : forall (t : itree node R) (Q : R -> machine_state -> Prop) (P : R -> Model -> Prop) ms mo,
  tmm t ->
  impl segs (at_node segs) t Q ms ->
  twf t mo P ->
  minv mo -> m_halted mo = None ->
  aevt segs (fun c => exists r, Q r (cfg_ms c) /\ P r (cfg_model c)
                      /\ minv (cfg_model c) /\ m_halted (cfg_model c) = None /\ vm_only mo (cfg_model c))
       (mkCfg ms mo).
Proof.
  induction t as [r|n k IH]; intros Q P ms mo Ht Hi Hw Hm Hh; cbn in Ht, Hi, Hw.
  - eapply evt_aevt; [exact Hh| exact Hm| exact Hi|]. intros ms' HQ. apply aevt_now. cbn.
    exists r. split; [exact HQ|]. split; [exact Hw|]. split; [exact Hm|]. split; [exact Hh|]. apply vm_only_refl.
  - destruct Ht as [Hn Hk]. destruct Hw as [Hs Hwk].
    eapply evt_aevt; [exact Hh| exact Hm| exact Hi|]. intros ms1 [Hat Hik].
    ddestruct (mm_node_facts segs n ms1 mo ltac:(destruct n; first [exact I|destruct Hn]) Hat Hm Hh Hs) as (Hc & Hsnd & Hp).
    apply aevt_step.
    + ddestruct Hp as (eff & mo' & evs & Hst). pose proof (Hsnd _ _ _ Hst) as (_ & _ & Hss).
      rewrite (nstep_nil _ _ _ _ _ Hst) in Hss. eexists. exact Hss.
    + intros e st Hss. destruct (Hc _ _ Hss) as (eff & mo' & E & Hst). subst st. split; [exact (nstep_nil _ _ _ _ _ Hst)| discriminate].
    + intros e c' Hss. destruct (Hc _ _ Hss) as (eff & mo' & E & Hst). injection E as E'. subst c'.
      pose proof (Hsnd _ _ _ Hst) as (Hh' & Hm' & _).
      pose proof (nstep_mm_vm_only n mo eff mo' e Hm Hs Hst) as [Hvo _].
      eapply aevt_mono; [apply (IH eff Q P (nret ms1 eff) mo' (Hk eff) (Hik eff) (Hwk _ _ _ Hst) Hm' Hh')|].
      cbn. (intros c dd_H; ddestruct dd_H as (r & HQ & HP & M1 & M2 & M3)). exists r. split; [exact HQ|]. split; [exact HP|]. split; [exact M1|]. split; [exact M2|].
      eapply vm_only_trans; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma implM_mspec_aevt {St A} : forall (c : Monad.M St A) (s : St) (Q : A -> St -> machine_state -> Prop)
    (Pm : St -> Model -> Prop) (Qm : A -> St -> Model -> Prop) ms mo,
  tmm (c s) ->
  implM segs c s Q ms ->
  mspec Pm c Qm -> Pm s mo ->
  minv mo -> m_halted mo = None ->
  aevt segs (fun cf => exists a s', Q a s' (cfg_ms cf) /\ Qm a s' (cfg_model cf)
                      /\ minv (cfg_model cf) /\ m_halted (cfg_model cf) = None /\ vm_only mo (cfg_model cf))
       (mkCfg ms mo).
Proof.
  intros c s Q Pm Qm ms mo Ht Hi Hsp HP Hm Hh.
  pose proof (Hsp s mo HP) as Hw. unfold implM in Hi. unfold etwf in Hw.
  eapply aevt_mono; [apply (impl_twf_aevt _ _ _ ms mo Ht Hi Hw Hm Hh)|].
  cbn. (intros cf dd_H; ddestruct dd_H as ([|[a s']] & HQ & HPm & M)). { destruct HPm. }
  exists a, s'. cbn in HQ, HPm. tauto.
Qed.

End Bridge.

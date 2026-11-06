(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Exec ITree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require ShapeAlg ShapeAcc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Scfg Require Import Fcfg.
Import ListNotations.
Import Exc.
Import ShapeAlg(TSet, t_eq, t_alt, t_emit, t_nil, realizes, node_ok).
Open Scope Z_scope.
Unset Lia Cache.

Section Adeq.
Variable node : Type.
Variable segs : list Segment.
Variable at_node : node -> footprint -> machine_state -> Prop.
Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit : node -> Model -> word -> Model -> Prop.
Variable minv : Model -> Prop.
Variable nsafe : node -> Model -> Prop.
Variable fstep : node -> resp -> footprint -> footprint -> Prop.
Variable NMAX : nat.

Notation implF := (ITreeA.implF segs at_node fstep).
Notation node_soundA := (node_soundA node segs at_node nstep nexit minv nsafe NMAX).

Fixpoint twfA {R} (RNG : footprint) (A : alw) (t : itree node (exc R)) (mo : Model)
    (P : R -> footprint -> alw -> Model -> Prop) : Prop :=
  acct_ok NMAX RNG A mo /\
  match t with
  | Ret Unr => False
  | Ret (Ok r) => P r RNG A mo
  | Vis n k => nsafe n mo /\ (forall code mo', ~ nexit n mo code mo') /\
      forall rsp mo' evs, nstep n mo rsp mo' evs ->
        evs = [] /\ exists RNG' A', fstep n rsp RNG RNG' /\ alw_le A A' /\ twfA RNG' A' (k rsp) mo' P
  end.

Lemma twfA_acct : forall {R} RNG A (t : itree node (exc R)) mo P, twfA RNG A t mo P -> acct_ok NMAX RNG A mo.
Proof. intros R RNG A [[|r]|n k] mo P H; exact (proj1 H). Qed.

Lemma rz_csteps : forall c c' (K : TSet),
  csteps segs c c' -> realizes segs (mkCfg (fst c') (snd c')) K -> realizes segs (mkCfg (fst c) (snd c)) K.
Proof.
  intros c c' K H. induction H as [c|c c1 c2 (Hh & Hs & Ha) _ IH]; intros HK; [exact HK|].
  destruct c as [ms mo], c1 as [ms1 mo1]. cbn [fst snd] in *.
  eapply ShapeAcc.rz_astep; [exact Hh | exact Hs | exact Ha | apply IH; exact HK].
Qed.

Lemma phase_lift : forall RNG A (Qm : machine_state -> Prop) ms mo mo_,
  acct_ok NMAX RNG A mo -> mrel A mo mo_ -> m_halted mo = None ->
  evtF segs RNG Qm ms ->
  exists ms1 mo1_, csteps segs (ms, mo_) (ms1, mo1_) /\ Qm ms1 /\ mrel A mo mo1_ /\ ainv (m_vm_lazy mo) A NMAX mo1_.
Proof.
  intros RNG A Qm ms mo mo_ ACC MR Hh EV.
  pose proof (mrel_ainv NMAX RNG A mo mo_ ACC MR) as INV.
  destruct (evtF_lift segs (m_vm_lazy mo) A NMAX RNG Qm ms mo_ (proj1 ACC) INV
              ltac:(rewrite (mrel_halted _ _ _ MR); exact Hh) EV) as (ms1 & mo1_ & CS & HQ & INV1 & SB1).
  exists ms1, mo1_. split; [exact CS|]. split; [exact HQ|]. split; [eapply (mrel_after NMAX); eauto| exact INV1].
Qed.

Definition nidxA (n : node) (A : alw) (ms1 : machine_state) (mo mo1_ : Model) : Type :=
  { x : resp * Model * Model |
      nstep n mo (fst (fst x)) (snd (fst x)) [] /\ mrel A (snd (fst x)) (snd x) /\
      sstep_cfg segs fcfg (mkCfg ms1 mo1_) [] (SNext (mkCfg (nret ms1 (fst (fst x))) (snd x))) }.

Theorem implF_twfA_realizes_silent : node_soundA ->
  forall {R} (t : itree node (exc R)) RNG A (Q : R -> footprint -> machine_state -> Prop)
         (P : R -> footprint -> alw -> Model -> Prop) ms mo mo_ (K : TSet),
  implF RNG t (epostF Q) ms ->
  twfA RNG A t mo P ->
  m_halted mo = None -> minv mo -> mrel A mo mo_ ->
  (forall r RNG' A' ms' mo' mo_', Q r RNG' ms' -> P r RNG' A' mo' -> acct_ok NMAX RNG' A' mo' ->
       m_halted mo' = None -> minv mo' -> mrel A' mo' mo_' -> realizes segs (mkCfg ms' mo_') K) ->
  realizes segs (mkCfg ms mo_) K.
Proof.
  intros NS R t. induction t as [[|r]|n k IH]; intros RNG A Q P ms mo mo_ K Himpl Htwf Hh Hinv MR HK.
  - destruct Htwf as [_ []].
  - destruct Htwf as [ACC HP]. cbn [ITreeA.implF] in Himpl.
    destruct (phase_lift RNG A _ ms mo mo_ ACC MR Hh Himpl) as (ms1 & mo1_ & CS & HQ & MR1 & _).
    apply (rz_csteps (ms, mo_) (ms1, mo1_) K CS). cbn [fst snd].
    cbn in HQ. eapply HK; eauto.
  - destruct Htwf as (ACC & Hs & Hnx & Hk). cbn [ITreeA.implF] in Himpl.
    destruct (phase_lift RNG A _ ms mo mo_ ACC MR Hh Himpl) as (ms1 & mo1_ & CS & [Hat Hkids] & MR1 & INV1).
    apply (rz_csteps (ms, mo_) (ms1, mo1_) K CS). cbn [fst snd].

    assert (Hsub : forall x : nidxA n A ms1 mo mo1_,
              realizes segs (mkCfg (nret ms1 (fst (fst (proj1_sig x)))) (snd (proj1_sig x))) K).
    { intros [[[rsp mo'] mo_'] (Hst & MR' & Hss)]; cbn [fst snd proj1_sig] in *.
      destruct (Hk rsp mo' [] Hst) as (_ & RNG' & A' & HF & HLE & Htw').
      destruct (nsA_sound _ _ _ _ _ _ _ _ NS n RNG A ms1 mo mo1_ rsp mo' [] Hat Hh Hinv Hs (proj1 ACC) MR1 INV1 Hst) as (Hh' & Hinv' & _).
      eapply (IH rsp RNG' A' Q P); [apply Hkids; exact HF | exact Htw' | exact Hh' | exact Hinv' | eapply mrel_le; eassumption | exact HK]. }

    assert (I0' : inhabited (nidxA n A ms1 mo mo1_)).
    { destruct (nsA_progress _ _ _ _ _ _ _ _ NS n RNG A ms1 mo mo1_ Hat Hh Hinv Hs (proj1 ACC) MR1 INV1) as [(rsp & mo' & evs & Hst)|(code & mo' & Hex)];
        [| exfalso; exact (Hnx code mo' Hex)].
      destruct (Hk rsp mo' evs Hst) as (-> & _).
      destruct (nsA_sound _ _ _ _ _ _ _ _ NS n RNG A ms1 mo mo1_ rsp mo' [] Hat Hh Hinv Hs (proj1 ACC) MR1 INV1 Hst) as (_ & _ & mo_' & Hss & MP).
      constructor. exists (rsp, mo', mo_'). cbn [fst snd]. split; [exact Hst|]. split; [exact MP| exact Hss]. }
    destruct I0' as [I0].
    assert (K0 : K []) by (eapply ShapeAlg.realizes_nonempty; apply (Hsub I0)).
    eapply ShapeAlg.rz_conseq.
    + apply (ShapeAlg.rz_node segs (mkCfg ms1 mo1_) (nidxA n A ms1 mo mo1_) (fun _ => [])
               (fun x => mkCfg (nret ms1 (fst (fst (proj1_sig x)))) (snd (proj1_sig x))) (fun _ => K) I0).
      * split.
        -- intros [[[rsp mo'] mo_'] (Hst & MR' & Hss)]; cbn [fst snd proj1_sig]. exact Hss.
        -- intros e st Hss.
           destruct (nsA_complete _ _ _ _ _ _ _ _ NS n RNG A ms1 mo mo1_ e st Hat Hh Hinv Hs (proj1 ACC) MR1 INV1 Hss)
             as [(rsp & mo' & mo_' & -> & Hst & MP)|(code & mo' & mo_' & _ & Hex & _)];
             [| exfalso; exact (Hnx code mo' Hex)].
           destruct (Hk rsp mo' e Hst) as (-> & _).
           exists (exist _ (rsp, mo', mo_') (conj Hst (conj MP Hss))). cbn [fst snd proj1_sig]. split; reflexivity.
      * exact Hsub.
    + intros tr. unfold t_alt. split.
      * intros [i Hi]. exact (proj1 (ShapeAlg.t_emit_nil_eq K K0 tr) Hi).
      * intros H. exists I0. exact (proj2 (ShapeAlg.t_emit_nil_eq K K0 tr) H).
Qed.

End Adeq.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import Nodes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import NodesA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AProto.
Unset Nia Cache. Unset Nra Cache.

Section AsanAdeq.
Variable segs : list Segment.
Variable NMAX : nat.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAX) fstepS NMAX).

Theorem implS_twfS_realizes_silent :
  forall {R} (t : itree node (exc R)) RNG A (Q : R -> footprint -> machine_state -> Prop)
         (P : R -> footprint -> alw -> Model -> Prop) ms mo mo_ (K : TSet),
  implS segs RNG t (epostF Q) ms ->
  twfS RNG A t mo P ->
  m_halted mo = None -> minvA mo -> mrel A mo mo_ ->
  (forall r RNG' A' ms' mo' mo_', Q r RNG' ms' -> P r RNG' A' mo' -> acct_ok NMAX RNG' A' mo' ->
       m_halted mo' = None -> minvA mo' -> mrel A' mo' mo_' -> realizes segs (mkCfg ms' mo_') K) ->
  realizes segs (mkCfg ms mo_) K.
Proof.
  intros R t RNG A Q P ms mo mo_ K. eapply implF_twfA_realizes_silent. apply nodesA_sound.
Qed.
End AsanAdeq.

Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA.

Import ListNotations.
Import Exc.
Import ShapeAlg(TSet, t_eq, t_alt, t_emit, t_nil, realizes, node_ok).
Open Scope Z_scope.
Unset Lia Cache.

Section Adeq.
Variable node : Type.
Variable segs : list Segment.
Variable at_node : node -> footprint -> machine_state -> Prop.
Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit : node -> Model -> word -> Model -> Prop.
Variable minv : Model -> Prop.
Variable nsafe : node -> Model -> Prop.
Variable fstep : node -> resp -> footprint -> footprint -> Prop.
Variable NMAX : nat.

Notation implF := (ITreeA.implF segs at_node fstep).
Notation node_soundA := (node_soundA node segs at_node nstep nexit minv nsafe NMAX).

Fixpoint twfA {R} (RNG : footprint) (A : alw) (t : itree node (exc R)) (mo : Model)
    (P : R -> footprint -> alw -> Model -> Prop) : Prop :=
  acct_ok NMAX RNG A mo /\
  match t with
  | Ret Unr => False
  | Ret (Ok r) => P r RNG A mo
  | Vis n k => nsafe n mo /\ (forall code mo', ~ nexit n mo code mo') /\
      forall rsp mo' evs, nstep n mo rsp mo' evs ->
        evs = [] /\ exists RNG' A', fstep n rsp RNG RNG' /\ alw_le A A' /\ twfA RNG' A' (k rsp) mo' P
  end.

Lemma twfA_acct : forall {R} RNG A (t : itree node (exc R)) mo P, twfA RNG A t mo P -> acct_ok NMAX RNG A mo.
Proof. intros R RNG A [[|r]|n k] mo P H; exact (proj1 H). Qed.

Lemma rz_csteps : forall c c' (K : TSet),
  csteps segs c c' -> realizes segs (mkCfg (fst c') (snd c')) K -> realizes segs (mkCfg (fst c) (snd c)) K.
Proof.
  intros c c' K H. induction H as [c|c c1 c2 (Hh & Hs & Ha) _ IH]; intros HK; [exact HK|].
  destruct c as [ms mo], c1 as [ms1 mo1]. cbn [fst snd] in *.
  eapply ShapeAcc.rz_astep; [exact Hh | exact Hs | exact Ha | apply IH; exact HK].
Qed.

Lemma phase_lift : forall RNG A (Qm : machine_state -> Prop) ms mo mo_,
  acct_ok NMAX RNG A mo -> mrel A mo mo_ -> m_halted mo = None ->
  evtF segs RNG Qm ms ->
  exists ms1 mo1_, csteps segs (ms, mo_) (ms1, mo1_) /\ Qm ms1 /\ mrel A mo mo1_ /\ ainv (m_vm_lazy mo) A NMAX mo1_.
Proof.
  intros RNG A Qm ms mo mo_ ACC MR Hh EV.
  pose proof (mrel_ainv NMAX RNG A mo mo_ ACC MR) as INV.
  destruct (evtF_lift segs (m_vm_lazy mo) A NMAX RNG Qm ms mo_ (proj1 ACC) INV
              ltac:(rewrite (mrel_halted _ _ _ MR); exact Hh) EV) as (ms1 & mo1_ & CS & HQ & INV1 & SB1).
  exists ms1, mo1_. split; [exact CS|]. split; [exact HQ|]. split; [eapply (mrel_after NMAX); eauto| exact INV1].
Qed.

Definition nidxA (n : node) (A : alw) (ms1 : machine_state) (mo mo1_ : Model) : Type :=
  { x : resp * Model * Model |
      nstep n mo (fst (fst x)) (snd (fst x)) [] /\ mrel A (snd (fst x)) (snd x) /\
      sstep_cfg segs fcfg (mkCfg ms1 mo1_) [] (SNext (mkCfg (nret ms1 (fst (fst x))) (snd x))) }.

Theorem implF_twfA_realizes_silent : node_soundA ->
  forall {R} (t : itree node (exc R)) RNG A (Q : R -> footprint -> machine_state -> Prop)
         (P : R -> footprint -> alw -> Model -> Prop) ms mo mo_ (K : TSet),
  implF RNG t (epostF Q) ms ->
  twfA RNG A t mo P ->
  m_halted mo = None -> minv mo -> mrel A mo mo_ ->
  (forall r RNG' A' ms' mo' mo_', Q r RNG' ms' -> P r RNG' A' mo' -> acct_ok NMAX RNG' A' mo' ->
       m_halted mo' = None -> minv mo' -> mrel A' mo' mo_' -> realizes segs (mkCfg ms' mo_') K) ->
  realizes segs (mkCfg ms mo_) K.
Proof.
  intros NS R t. induction t as [[|r]|n k IH]; intros RNG A Q P ms mo mo_ K Himpl Htwf Hh Hinv MR HK.
  - destruct Htwf as [_ []].
  - destruct Htwf as [ACC HP]. cbn [ITreeA.implF] in Himpl.
    destruct (phase_lift RNG A _ ms mo mo_ ACC MR Hh Himpl) as (ms1 & mo1_ & CS & HQ & MR1 & _).
    apply (rz_csteps (ms, mo_) (ms1, mo1_) K CS). cbn [fst snd].
    cbn in HQ. eapply HK; eauto.
  - destruct Htwf as (ACC & Hs & Hnx & Hk). cbn [ITreeA.implF] in Himpl.
    destruct (phase_lift RNG A _ ms mo mo_ ACC MR Hh Himpl) as (ms1 & mo1_ & CS & [Hat Hkids] & MR1 & INV1).
    apply (rz_csteps (ms, mo_) (ms1, mo1_) K CS). cbn [fst snd].

    assert (Hsub : forall x : nidxA n A ms1 mo mo1_,
              realizes segs (mkCfg (nret ms1 (fst (fst (proj1_sig x)))) (snd (proj1_sig x))) K).
    { intros [[[rsp mo'] mo_'] (Hst & MR' & Hss)]; cbn [fst snd proj1_sig] in *.
      destruct (Hk rsp mo' [] Hst) as (_ & RNG' & A' & HF & HLE & Htw').
      destruct (nsA_sound _ _ _ _ _ _ _ _ NS n RNG A ms1 mo mo1_ rsp mo' [] Hat Hh Hinv Hs (proj1 ACC) MR1 INV1 Hst) as (Hh' & Hinv' & _).
      eapply (IH rsp RNG' A' Q P); [apply Hkids; exact HF | exact Htw' | exact Hh' | exact Hinv' | eapply mrel_le; eassumption | exact HK]. }

    assert (I0' : inhabited (nidxA n A ms1 mo mo1_)).
    { destruct (nsA_progress _ _ _ _ _ _ _ _ NS n RNG A ms1 mo mo1_ Hat Hh Hinv Hs (proj1 ACC) MR1 INV1) as [(rsp & mo' & evs & Hst)|(code & mo' & Hex)];
        [| exfalso; exact (Hnx code mo' Hex)].
      destruct (Hk rsp mo' evs Hst) as (-> & _).
      destruct (nsA_sound _ _ _ _ _ _ _ _ NS n RNG A ms1 mo mo1_ rsp mo' [] Hat Hh Hinv Hs (proj1 ACC) MR1 INV1 Hst) as (_ & _ & mo_' & Hss & MP).
      constructor. exists (rsp, mo', mo_'). cbn [fst snd]. split; [exact Hst|]. split; [exact MP| exact Hss]. }
    destruct I0' as [I0].
    assert (K0 : K []) by (eapply ShapeAlg.realizes_nonempty; apply (Hsub I0)).
    eapply ShapeAlg.rz_conseq.
    + apply (ShapeAlg.rz_node segs (mkCfg ms1 mo1_) (nidxA n A ms1 mo mo1_) (fun _ => [])
               (fun x => mkCfg (nret ms1 (fst (fst (proj1_sig x)))) (snd (proj1_sig x))) (fun _ => K) I0).
      * split.
        -- intros [[[rsp mo'] mo_'] (Hst & MR' & Hss)]; cbn [fst snd proj1_sig]. exact Hss.
        -- intros e st Hss.
           destruct (nsA_complete _ _ _ _ _ _ _ _ NS n RNG A ms1 mo mo1_ e st Hat Hh Hinv Hs (proj1 ACC) MR1 INV1 Hss)
             as [(rsp & mo' & mo_' & -> & Hst & MP)|(code & mo' & mo_' & _ & Hex & _)];
             [| exfalso; exact (Hnx code mo' Hex)].
           destruct (Hk rsp mo' e Hst) as (-> & _).
           exists (exist _ (rsp, mo', mo_') (conj Hst (conj MP Hss))). cbn [fst snd proj1_sig]. split; reflexivity.
      * exact Hsub.
    + intros tr. unfold t_alt. split.
      * intros [i Hi]. exact (proj1 (ShapeAlg.t_emit_nil_eq K K0 tr) Hi).
      * intros H. exists I0. exact (proj2 (ShapeAlg.t_emit_nil_eq K K0 tr) H).
Qed.

End Adeq.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.NodesA.
Import AProto.TwinB.
Unset Nia Cache. Unset Nra Cache.

Section AsanAdeq.
Variable segs : list Segment.
Variable NMAX : nat.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAX) fstepS NMAX).

Theorem implS_twfS_realizes_silent :
  forall {R} (t : itree node (exc R)) RNG A (Q : R -> footprint -> machine_state -> Prop)
         (P : R -> footprint -> alw -> Model -> Prop) ms mo mo_ (K : TSet),
  implS segs RNG t (epostF Q) ms ->
  twfS RNG A t mo P ->
  m_halted mo = None -> minvA mo -> mrel A mo mo_ ->
  (forall r RNG' A' ms' mo' mo_', Q r RNG' ms' -> P r RNG' A' mo' -> acct_ok NMAX RNG' A' mo' ->
       m_halted mo' = None -> minvA mo' -> mrel A' mo' mo_' -> realizes segs (mkCfg ms' mo_') K) ->
  realizes segs (mkCfg ms mo_) K.
Proof.
  intros R t RNG A Q P ms mo mo_ K. eapply implF_twfA_realizes_silent. apply nodesA_sound.
Qed.
End AsanAdeq.
End TwinB.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize Bridge TSim.
Import ListNotations.
Open Scope Z_scope.

Definition t_incl0 (T T' : TSet) : Prop := forall tr, T tr -> tr = [] \/ T' tr.

Lemma t_incl0_refl : forall T, t_incl0 T T. Proof. intros T tr H. right. exact H. Qed.
Lemma t_incl0_of_incl : forall T T', t_incl T T' -> t_incl0 T T'. Proof. intros T T' H tr Ht. right. apply H. exact Ht. Qed.
Lemma t_incl0_trans : forall T1 T2 T3, t_incl0 T1 T2 -> t_incl0 T2 T3 -> t_incl0 T1 T3.
Proof. intros T1 T2 T3 H1 H2 tr Ht. destruct (H1 tr Ht) as [-> | H]; [left; reflexivity| exact (H2 tr H)]. Qed.
Lemma t_incl_of_incl0 : forall T T', T' [] -> t_incl0 T T' -> t_incl T T'.
Proof. intros T T' N H tr Ht. destruct (H tr Ht) as [-> | H']; [exact N| exact H']. Qed.
Lemma t_eq_of_incl0 : forall T T', T [] -> T' [] -> t_incl0 T T' -> t_incl0 T' T -> t_eq T T'.
Proof. intros T T' N N' H H'. apply t_eq_of_incl; apply t_incl_of_incl0; assumption. Qed.

Lemma t_incl_emit0 : forall e T T', t_incl0 T T' -> t_incl (t_emit e T) (t_emit e T').
Proof.
  intros e T T' H tr. unfold t_emit. intros [Hp | (tr' & -> & HT)]; [left; exact Hp|].
  destruct (H tr' HT) as [-> | HT'].
  - left. rewrite app_nil_r. apply is_prefix_refl.
  - right. exists tr'. split; [reflexivity| exact HT'].
Qed.

Section WithSegs.
  Variable segs : list Segment.
  #[using="Type"] Lemma realizes_has_nil : forall c T, realizes segs c T -> T [].
  Proof. intros c T H. apply (realizes_obs_iff segs c T H). exists [], c. split; [apply star_cfg_refl| apply is_prefix_nil]. Qed.
End WithSegs.

Section TSimS.

  Context {NA NB : Type}.
  Variable nstepA : NA -> Model -> resp -> Model -> list event -> Prop.
  Variable nexitA : NA -> Model -> word -> Model -> Prop.
  Variable nstepB : NB -> Model -> resp -> Model -> list event -> Prop.
  Variable nexitB : NB -> Model -> word -> Model -> Prop.

  Local Notation tshA := (tshape NA nstepA nexitA).
  Local Notation tshB := (tshape NB nstepB nexitB).

  Definition silentA (n : NA) (mo : Model) : Prop :=
    (forall rsp mo' evs, nstepA n mo rsp mo' evs -> evs = []) /\ (forall code mo', ~ nexitA n mo code mo').
  Definition silentB (n : NB) (mo : Model) : Prop :=
    (forall rsp mo' evs, nstepB n mo rsp mo' evs -> evs = []) /\ (forall code mo', ~ nexitB n mo code mo').

  Context {RA RB : Type}.

  Inductive rafter (P : itree NB RB -> Model -> Prop) : itree NB RB -> Model -> Prop :=
  | ra_here : forall tB moB, P tB moB -> rafter P tB moB
  | ra_step : forall nB kB moB rspB moB',
      silentB nB moB -> nstepB nB moB rspB moB' [] -> rafter P (kB rspB) moB' -> rafter P (Vis nB kB) moB.

  Fixpoint stsim (L : RA -> Model -> RB -> Model -> Prop) (tA : itree NA RA) (moA : Model) (tB : itree NB RB) (moB : Model) {struct tA} : Prop :=
    rafter (fun tB moB =>
      match tA with
      | Ret rA => match tB with Ret rB => L rA moA rB moB | Vis _ _ => False end
      | Vis nA kA =>

          (silentA nA moA /\ forall rspA moA' evs, nstepA nA moA rspA moA' evs -> stsim L (kA rspA) moA' tB moB)
          \/
          match tB with
          | Ret _ => False
          | Vis nB kB =>
              (forall rspA moA' evs, nstepA nA moA rspA moA' evs ->
                 exists rspB moB', nstepB nB moB rspB moB' evs /\ stsim L (kA rspA) moA' (kB rspB) moB')
              /\ (forall code moA', nexitA nA moA code moA' -> exists moB', nexitB nB moB code moB' /\ m_fs moB' = m_fs moA')
          end
      end) tB moB.

  #[using="Type"] Lemma ss_ret : forall L rA moA rB moB, L rA moA rB moB -> stsim L (Ret rA) moA (Ret rB) moB.
  Proof. intros. cbn. apply ra_here. assumption. Qed.

  #[using="Type"] Lemma ss_match : forall L nA kA moA nB kB moB,
    (forall rspA moA' evs, nstepA nA moA rspA moA' evs ->
       exists rspB moB', nstepB nB moB rspB moB' evs /\ stsim L (kA rspA) moA' (kB rspB) moB') ->
    (forall code moA', nexitA nA moA code moA' -> exists moB', nexitB nB moB code moB' /\ m_fs moB' = m_fs moA') ->
    stsim L (Vis nA kA) moA (Vis nB kB) moB.
  Proof. intros. cbn. apply ra_here. right. auto. Qed.

  #[using="Type"] Lemma ss_left : forall L nA kA moA tB moB,
    silentA nA moA ->
    (forall rspA moA' evs, nstepA nA moA rspA moA' evs -> stsim L (kA rspA) moA' tB moB) ->
    stsim L (Vis nA kA) moA tB moB.
  Proof. intros. cbn. apply ra_here. left. auto. Qed.

  #[using="Type"] Lemma ss_right : forall L tA moA nB kB moB rspB moB',
    silentB nB moB -> nstepB nB moB rspB moB' [] -> stsim L tA moA (kB rspB) moB' -> stsim L tA moA (Vis nB kB) moB.
  Proof. intros L tA moA nB kB moB rspB moB' SIL ST H. destruct tA; cbn in *; eapply ra_step; eauto. Qed.

  #[using="Type"] Theorem stsim_tshape : forall (L : RA -> Model -> RB -> Model -> Prop) (KA : RA -> Model -> TSet) (KB : RB -> Model -> TSet) tA moA tB moB,
    stsim L tA moA tB moB ->
    (forall rA moA' rB moB', L rA moA' rB moB' -> t_incl0 (KA rA moA') (KB rB moB')) ->
    t_incl0 (tshA tA moA KA) (tshB tB moB KB).
  Proof.
    intros L KA KB tA. induction tA as [rA | nA kA IH]; intros moA tB moB H HK; cbn in H;
      induction H as [tB moB P | nB kB moB rspB moB' [SIL NX] STB H IHr].
    - destruct tB as [rB | nB kB]; [| destruct P]. cbn [tshape]. apply HK. exact P.
    -
      intros tr Htr. destruct (IHr tr Htr) as [-> | H']; [left; reflexivity| right].
      cbn [tshape]. exists (inl (exist _ (rspB, moB', []) STB)). cbn. right. exists tr. split; [reflexivity| exact H'].
    - destruct P as [([SIL NX] & F) | M].
      +
        cbn [tshape]. intros tr [[[[[rspA moA'] evs] ST] | [[code moA'] EX]] Htr]; cbn in Htr.
        * pose proof (SIL _ _ _ ST) as E. cbn in E. subst evs.
          destruct Htr as [Hp | (tr' & -> & Htr')].
          -- left. apply is_prefix_nil_r in Hp. exact Hp.
          -- cbn [app]. apply (IH rspA moA' tB moB (F _ _ _ ST) HK). exact Htr'.
        * exfalso. exact (NX _ _ EX).
      + destruct tB as [rB | nB kB]; [destruct M|]. destruct M as [F XF]. cbn [tshape].
        apply t_incl0_of_incl. apply t_alt_incl_match.
        intros [[[[rspA moA'] evs] ST] | [[code moA'] EX]]; cbn.
        * destruct (F _ _ _ ST) as (rspB & moB'' & STB & H').
          exists (inl (exist _ (rspB, moB'', evs) STB)). cbn. apply t_incl_emit0. apply (IH rspA moA' _ _ H' HK).
        * destruct (XF _ _ EX) as (moB' & EXB & EFS).
          exists (inr (exist _ (code, moB') EXB)). cbn. rewrite EFS. apply t_incl_refl.
    - intros tr Htr. destruct (IHr tr Htr) as [-> | H']; [left; reflexivity| right].
      cbn [tshape]. exists (inl (exist _ (rspB, moB', []) STB)). cbn. right. exists tr. split; [reflexivity| exact H'].
  Qed.

  #[using="Type"] Lemma stsim_mono : forall (L L' : RA -> Model -> RB -> Model -> Prop) tA moA tB moB,
    stsim L tA moA tB moB -> (forall rA moA' rB moB', L rA moA' rB moB' -> L' rA moA' rB moB') -> stsim L' tA moA tB moB.
  Proof.
    intros L L' tA. induction tA as [rA | nA kA IH]; intros moA tB moB H HL; cbn in H |- *;
      induction H as [tB moB P | nB kB moB rspB moB' SIL STB H IHr].
    - apply ra_here. destruct tB; [apply HL; exact P| destruct P].
    - eapply ra_step; eauto.
    - apply ra_here. destruct P as [(SIL & F) | M].
      + left. split; [exact SIL|]. intros rspA moA' evs ST. exact (IH _ _ _ _ (F _ _ _ ST) HL).
      + right. destruct tB as [rB | nB kB]; [destruct M|]. destruct M as [F XF]. split; [| exact XF].
        intros rspA moA' evs ST. destruct (F _ _ _ ST) as (rspB & moB'' & STB & H'). exists rspB, moB''. split; [exact STB| exact (IH _ _ _ _ H' HL)].
    - eapply ra_step; eauto.
  Qed.
End TSimS.

Arguments stsim {NA NB} nstepA nexitA nstepB nexitB {RA RB} L tA moA tB moB.
Arguments rafter {NB} nstepB nexitB {RB} P tB moB.
Arguments silentA {NA} nstepA nexitA n mo.
Arguments silentB {NB} nstepB nexitB n mo.
Arguments ss_ret {NA NB} nstepA nexitA nstepB nexitB {RA RB} L.
Arguments ss_match {NA NB} nstepA nexitA nstepB nexitB {RA RB} L.
Arguments ss_left {NA NB} nstepA nexitA nstepB nexitB {RA RB} L.
Arguments ss_right {NA NB} nstepA nexitA nstepB nexitB {RA RB} L.

Section Bind.
  Context {NA NB : Type}.
  Variable nstepA : NA -> Model -> resp -> Model -> list event -> Prop.
  Variable nexitA : NA -> Model -> word -> Model -> Prop.
  Variable nstepB : NB -> Model -> resp -> Model -> list event -> Prop.
  Variable nexitB : NB -> Model -> word -> Model -> Prop.
  Local Notation SIM := (stsim nstepA nexitA nstepB nexitB).

  #[using="Type"] Lemma stsim_bind : forall {RA RB SA SB : Type} (L1 : RA -> Model -> RB -> Model -> Prop) (L : SA -> Model -> SB -> Model -> Prop)
      (tA : itree NA RA) (fA : RA -> itree NA SA) (tB : itree NB RB) (fB : RB -> itree NB SB) moA moB,
    SIM L1 tA moA tB moB ->
    (forall rA moA' rB moB', L1 rA moA' rB moB' -> SIM L (fA rA) moA' (fB rB) moB') ->
    SIM L (ITree.bind NA tA fA) moA (ITree.bind NB tB fB) moB.
  Proof.
    intros RA RB SA SB L1 L tA. induction tA as [rA | nA kA IH]; intros fA tB fB moA moB H HF; cbn in H;
      induction H as [tB moB P | nB kB moB rspB moB' SIL STB H IHr].
    - destruct tB as [rB | nB kB]; [| destruct P]. cbn [ITree.bind]. apply HF. exact P.
    - cbn [ITree.bind]. eapply ss_right; eauto.
    - cbn [ITree.bind]. destruct P as [(SIL & F) | M].
      + apply ss_left; [exact SIL|]. intros rspA moA' evs ST. exact (IH rspA fA tB fB moA' moB (F _ _ _ ST) HF).
      + destruct tB as [rB | nB kB]; [destruct M|]. destruct M as [F XF]. cbn [ITree.bind]. apply ss_match; [| exact XF].
        intros rspA moA' evs ST. destruct (F _ _ _ ST) as (rspB & moB'' & STB & H').
        exists rspB, moB''. split; [exact STB| exact (IH rspA fA _ fB moA' moB'' H' HF)].
    - cbn [ITree.bind]. eapply ss_right; eauto.
  Qed.

End Bind.

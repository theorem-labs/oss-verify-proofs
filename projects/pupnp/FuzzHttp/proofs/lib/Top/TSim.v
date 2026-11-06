(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize Bridge.
Import ListNotations.
Open Scope Z_scope.
Notation tsh := (tshape node nstep nexit).

Lemma t_alt_match : forall {I J : Type} (f : I -> TSet) (g : J -> TSet),
  (forall i, exists j, t_eq (f i) (g j)) -> (forall j, exists i, t_eq (f i) (g j)) ->
  t_eq (t_alt f) (t_alt g).
Proof.
  intros I J f g HIJ HJI tr. unfold t_alt. split.
  - intros [i Hi]. destruct (HIJ i) as [j Hj]. exists j. apply (Hj tr). exact Hi.
  - intros [j Hj]. destruct (HJI j) as [i Hi]. exists i. apply (Hi tr). exact Hj.
Qed.

Definition t_incl (T T' : TSet) : Prop := forall tr, T tr -> T' tr.
Lemma t_incl_refl : forall T, t_incl T T. Proof. firstorder. Qed.
Lemma t_incl_trans : forall T1 T2 T3, t_incl T1 T2 -> t_incl T2 T3 -> t_incl T1 T3. Proof. firstorder. Qed.
Lemma t_incl_of_eq : forall T T', t_eq T T' -> t_incl T T'. Proof. intros T T' H tr. apply (H tr). Qed.
Lemma t_eq_of_incl : forall T T', t_incl T T' -> t_incl T' T -> t_eq T T'. Proof. intros T T' H1 H2 tr. split; auto. Qed.
Lemma t_incl_emit : forall e T T', t_incl T T' -> t_incl (t_emit e T) (t_emit e T').
Proof. intros e T T' H tr. unfold t_emit. intros [Hp|(tr' & -> & HT)]; [left; exact Hp| right; exists tr'; split; [reflexivity| apply H; exact HT]]. Qed.
Lemma t_alt_incl_match : forall {I J : Type} (f : I -> TSet) (g : J -> TSet),
  (forall i, exists j, t_incl (f i) (g j)) -> t_incl (t_alt f) (t_alt g).
Proof. intros I J f g HIJ tr. unfold t_alt. intros [i Hi]. destruct (HIJ i) as [j Hj]. exists j. apply Hj. exact Hi. Qed.

Section TSim.
  Context {RA RB : Type}.

  Fixpoint tsim (L : RA -> Model -> RB -> Model -> Prop) (tA : itree node RA) (moA : Model) (tB : itree node RB) (moB : Model) {struct tA} : Prop :=
    match tA, tB with
    | Ret rA, Ret rB => L rA moA rB moB
    | Vis nA kA, Vis nB kB =>
        (forall rspA moA' evs, nstep nA moA rspA moA' evs ->
           exists rspB moB', nstep nB moB rspB moB' evs /\ tsim L (kA rspA) moA' (kB rspB) moB')
        /\ (forall code moA', nexit nA moA code moA' -> exists moB', nexit nB moB code moB' /\ m_fs moB' = m_fs moA')
    | _, _ => False
    end.

  #[using="Type"] Lemma tsim_mono : forall (L L' : RA -> Model -> RB -> Model -> Prop) tA moA tB moB,
    tsim L tA moA tB moB -> (forall rA moA' rB moB', L rA moA' rB moB' -> L' rA moA' rB moB') -> tsim L' tA moA tB moB.
  Proof.
    intros L L'. induction tA as [rA|nA kA IH]; intros moA [rB|nB kB] moB H HL; cbn in *; try contradiction.
    - apply HL. exact H.
    - destruct H as (F & XF). split; [| exact XF].
      intros rspA moA' evs ST. destruct (F _ _ _ ST) as (rspB & moB' & STB & H). exists rspB, moB'. split; [exact STB|]. eapply IH; eauto.
  Qed.

  #[using="Type"] Theorem tsim_tshape : forall (L : RA -> Model -> RB -> Model -> Prop) (KA : RA -> Model -> TSet) (KB : RB -> Model -> TSet) tA moA tB moB,
    tsim L tA moA tB moB ->
    (forall rA moA' rB moB', L rA moA' rB moB' -> t_incl (KA rA moA') (KB rB moB')) ->
    t_incl (tsh tA moA KA) (tsh tB moB KB).
  Proof.
    intros L KA KB. induction tA as [rA|nA kA IH]; intros moA [rB|nB kB] moB H HK; cbn in H; try contradiction; cbn [tshape].
    - apply HK. exact H.
    - destruct H as (F & XF). apply t_alt_incl_match.
      intros [[[[rspA moA'] evs] ST] | [[code moA'] EX]]; cbn.
      * destruct (F _ _ _ ST) as (rspB & moB' & STB & H).
        exists (inl (exist _ (rspB, moB', evs) STB)). cbn. apply t_incl_emit. eapply IH; [exact H| exact HK].
      * destruct (XF _ _ EX) as (moB' & EXB & EFS).
        exists (inr (exist _ (code, moB') EXB)). cbn. rewrite EFS. apply t_incl_refl.
  Qed.

  #[using="Type"] Lemma tsim_ret : forall (L : RA -> Model -> RB -> Model -> Prop) rA moA rB moB,
    L rA moA rB moB -> tsim L (Ret rA) moA (Ret rB) moB.
  Proof. intros. cbn. assumption. Qed.
End TSim.

Lemma tsim_bind : forall {RA RB SA SB : Type} (L1 : RA -> Model -> RB -> Model -> Prop) (L : SA -> Model -> SB -> Model -> Prop)
    (tA : itree node RA) (fA : RA -> itree node SA) (tB : itree node RB) (fB : RB -> itree node SB) moA moB,
  tsim L1 tA moA tB moB ->
  (forall rA moA' rB moB', L1 rA moA' rB moB' -> tsim L (fA rA) moA' (fB rB) moB') ->
  tsim L (ITree.bind node tA fA) moA (ITree.bind node tB fB) moB.
Proof.
  intros RA RB SA SB L1 L tA. induction tA as [rA|nA kA IH]; intros fA [rB|nB kB] fB moA moB H HF; cbn in H; try contradiction.
  - cbn. apply HF. exact H.
  - cbn. destruct H as (F & XF). split; [| exact XF].
    intros rspA moA' evs ST. destruct (F _ _ _ ST) as (rspB & moB' & STB & H). exists rspB, moB'. split; [exact STB|]. eapply IH; eauto.
Qed.

Lemma tsim_vis : forall {RA RB : Type} (L : RA -> Model -> RB -> Model -> Prop) nA kA nB kB moA moB,
  (forall rspA moA' evs, nstep nA moA rspA moA' evs -> exists rspB moB', nstep nB moB rspB moB' evs /\ tsim L (kA rspA) moA' (kB rspB) moB') ->
  (forall code moA', nexit nA moA code moA' -> exists moB', nexit nB moB code moB' /\ m_fs moB' = m_fs moA') ->
  tsim L (Vis nA kA) moA (Vis nB kB) moB.
Proof. intros. cbn. auto. Qed.

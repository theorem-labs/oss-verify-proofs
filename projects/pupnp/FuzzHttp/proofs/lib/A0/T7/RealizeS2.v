(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Monad MSafe.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach Bridge TSim DriverSim.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7 Require Import RealizeS.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Notation tsh := (tshape node nstep nexit) (only parsing).

Lemma fdn_nsafe : forall n mo, fdn n -> nsafe n mo.
Proof. intros n mo Hn. destruct n; cbn in Hn |- *; try exact I; destruct Hn as [Hn|Hn]; contradiction. Qed.

Lemma twf_fdtree_cong {R} : forall (t : itree node R) (P : R -> Model -> Prop) m1 m2,
  fdtree t -> meq m1 m2 -> (forall r a b, meq a b -> P r a -> P r b) -> twf t m1 P -> twf t m2 P.
Proof.
  induction t as [r | n k IH]; intros P m1 m2 Ht HM HP H; cbn in *.
  - eapply HP; [exact HM| exact H].
  - destruct Ht as [Hn Hk]. destruct H as [_ H]. split; [apply fdn_nsafe; exact Hn|].
    intros rsp m2' evs ST. destruct Hn as [Hfd | Hex].
    + destruct (fd_transfer n m2 m1 rsp m2' evs Hfd (eq_sym (proj1 HM)) (eq_sym (proj2 HM)) ST) as (m1' & ST1 & U).
      eapply (IH rsp P m1' m2'); [apply Hk| apply meq_sym; exact (fdupd2_meq _ _ _ _ (meq_sym _ _ HM) U)| exact HP| exact (H rsp m1' evs ST1)].
    + destruct n; try contradiction. all: exfalso; exact (nstep_exit_none _ _ _ _ _ ST).
Qed.

Section RealizeS2.
  Variable segs : list Segment.
  Variable AS : Type.
  Variable V : AS -> Model -> Model.
  Variable INV : config -> AS -> Prop.
  Variable ATN : node -> machine_state -> AS -> Prop.
  Variable GOOD : node -> resp -> Prop.
  Local Notation SEAM := (RealizeS.SEAM segs AS V INV).
  Local Notation implS := (RealizeS.implS segs AS V INV ATN GOOD).

  Hypothesis V_fs : forall a mo, m_fs (V a mo) = m_fs mo.
  Hypothesis NODE : forall n ms mo a,
    fdn n -> ATN n ms a -> INV (mkCfg ms mo) a ->
    (forall e st, sstep_cfg segs ACFG (mkCfg ms mo) e st ->
        (exists rsp mo', st = SNext (mkCfg (nret ms rsp) mo') /\ nstep n (V a mo) rsp (V a mo') e /\ INV (mkCfg (nret ms rsp) mo') a /\ GOOD n rsp)
     \/ (exists code mo', st = SNext (mkCfg ms mo') /\ nexit n (V a mo) code (V a mo')
           /\ e = [ExitEv code (m_fs mo')] /\ m_halted mo' = Some code))
    /\ (forall rsp moE' evs, nstep n (V a mo) rsp moE' evs ->
        exists mo', V a mo' = moE' /\ sstep_cfg segs ACFG (mkCfg ms mo) evs (SNext (mkCfg (nret ms rsp) mo')) /\ INV (mkCfg (nret ms rsp) mo') a /\ GOOD n rsp)
    /\ (forall code moE', nexit n (V a mo) code moE' ->
        exists mo', V a mo' = moE' /\ m_halted mo' = Some code
          /\ sstep_cfg segs ACFG (mkCfg ms mo) [ExitEv code (m_fs moE')] (SNext (mkCfg ms mo')))
    /\ ((exists rsp moE' evs, nstep n (V a mo) rsp moE' evs) \/ (exists code moE', nexit n (V a mo) code moE')).

  #[using="V_fs NODE"] Theorem implS_realizes_twf {R} : forall (t : itree node R) (Q : R -> machine_state -> AS -> Prop) (P : R -> Model -> Prop) (K : R -> Model -> TSet) ms a mo,
    fdtree t ->
    implS t Q ms a -> INV (mkCfg ms mo) a ->
    twf t (V a mo) P -> (forall r m1 m2, meq m1 m2 -> P r m1 -> P r m2) ->
    (forall r ms' a' mo', Q r ms' a' -> INV (mkCfg ms' mo') a' -> P r (V a' mo') -> realizes segs (mkCfg ms' mo') (K r (V a' mo'))) ->
    (forall r m1 m2, meq m1 m2 -> t_eq (K r m1) (K r m2)) ->
    realizes segs (mkCfg ms mo) (tsh t (V a mo) K).
  Proof.
    induction t as [r | n k IH]; intros Q P K ms a mo Ht HI HINV HT HP HK KC; cbn [RealizeS.implS] in HI; cbn [tshape].
    - apply (sr_realizes segs _ _ _ (HI mo HINV)). intros [ms' mo'] (a' & HINV' & HM & HQ). cbn [cfg_ms cfg_model] in *.
      eapply rz_conseq; [exact (HK r ms' a' mo' HQ HINV' (HP r _ _ HM HT))|]. apply KC. apply meq_sym. exact HM.
    - destruct Ht as [Hn Hk].
      apply (sr_realizes segs _ _ _ (HI mo HINV)). intros [ms1 mo1] (a1 & HINV1 & HM & HAT & HC). cbn [cfg_ms cfg_model] in *.
      pose proof (twf_fdtree_cong (Vis n k) P (V a mo) (V a1 mo1) (conj Hn Hk) HM HP HT) as HT1. cbn in HT1. destruct HT1 as [_ HTk].
      apply (rz_conseq segs _ (tsh (Vis n k) (V a1 mo1) K)).
      2:{ apply (tsh_fdtree_cong (Vis n k) K (V a1 mo1) (V a mo)); [split; assumption| apply meq_sym; exact HM| exact KC]. }
      cbn [tshape].
      destruct (NODE n ms1 mo1 a1 Hn HAT HINV1) as (NC & NS & NE & NP).
      set (moE := V a1 mo1) in *.
      set (I1 := { p : resp * Model * list event |
                   sstep_cfg segs ACFG (mkCfg ms1 mo1) (snd p) (SNext (mkCfg (nret ms1 (fst (fst p))) (snd (fst p))))
                   /\ nstep n moE (fst (fst p)) (V a1 (snd (fst p))) (snd p)
                   /\ INV (mkCfg (nret ms1 (fst (fst p))) (snd (fst p))) a1 /\ GOOD n (fst (fst p)) }).
      set (I2 := { p : word * Model |
                   sstep_cfg segs ACFG (mkCfg ms1 mo1) [ExitEv (fst p) (m_fs (snd p))] (SNext (mkCfg ms1 (snd p)))
                   /\ nexit n moE (fst p) (V a1 (snd p)) /\ m_halted (snd p) = Some (fst p) }).
      set (nx := fun i : I1 + I2 =>
                   match i with
                   | inl (exist _ p _) => mkCfg (nret ms1 (fst (fst p))) (snd (fst p))
                   | inr (exist _ p _) => mkCfg ms1 (snd p)
                   end).
      set (evs := fun i : I1 + I2 =>
                   match i with
                   | inl (exist _ p _) => snd p
                   | inr (exist _ p _) => [ExitEv (fst p) (m_fs (snd p))]
                   end).
      set (TT := fun i : I1 + I2 =>
                   match i with
                   | inl (exist _ p _) => tsh (k (fst (fst p))) (V a1 (snd (fst p))) K
                   | inr _ => t_nil
                   end).
      assert (Hnode : node_ok segs (mkCfg ms1 mo1) (I1 + I2) evs nx).
      { split.
        * intros [[[[rsp mo'] es] PF] | [[code mo'] PF]]; cbn; destruct PF as (Hss & _); exact Hss.
        * intros e st Hss.
          destruct (NC e st Hss) as [(rsp & mo' & -> & Hst & HINV' & HG) | (code & mo' & -> & Hex & -> & Hh')].
          -- unshelve eexists (inl (exist _ (rsp, mo', e) _)); [cbn; auto | cbn; auto].
          -- unshelve eexists (inr (exist _ (code, mo') _)); [cbn; auto| cbn; auto]. }
      assert (Hcont : forall i, realizes segs (nx i) (TT i)).
      { intros [[[[rsp mo'] es] PF] | [[code mo'] PF]]; cbn.
        * destruct PF as (Hss & Hst & HINV' & HG). exact (IH rsp Q P K (nret ms1 rsp) a1 mo' (Hk rsp) (HC rsp HG) HINV' (HTk rsp _ es Hst) HP HK KC).
        * destruct PF as (Hss & Hex & Hh'). apply rz_halt. cbn. rewrite Hh'. discriminate. }
      assert (Hi0 : inhabited (I1 + I2)).
      { destruct NP as [(rsp0 & moE0 & evs0 & Hst0) | (code & moE' & Hex)].
        - destruct (NS rsp0 moE0 evs0 Hst0) as (mo' & EQ & Hss & HINV' & HG). constructor. left. exists (rsp0, mo', evs0). cbn. rewrite EQ. auto.
        - destruct (NE code moE' Hex) as (mo' & EQ & Hh' & Hss). constructor. right. exists (code, mo'). cbn.
          rewrite <- EQ, V_fs in Hss. split; [exact Hss|]. split; [rewrite EQ; exact Hex| exact Hh']. }
      destruct Hi0 as [i0].
      apply (rz_conseq segs _ (t_alt (fun i : I1 + I2 => t_emit (evs i) (TT i)))).
      + exact (rz_node segs _ (I1 + I2) evs nx TT i0 Hnode Hcont).
      + apply t_eq_alt_bi'.
        * intros [[[[rsp mo'] es] PF] | [[code mo'] PF]]; cbn.
          -- destruct PF as (Hss & Hst & HINV' & HG). exists (inl (exist _ (rsp, V a1 mo', es) Hst)). cbn. apply t_eq_refl.
          -- destruct PF as (Hss & Hex & Hh').
             exists (inr (exist _ (code, V a1 mo') Hex)). cbn. rewrite V_fs. apply t_eq_refl.
        * intros [[[[rsp moE'] es] Hst] | [[code moE'] Hex]]; cbn.
          -- destruct (NS rsp moE' es Hst) as (mo' & EQ & Hss & HINV' & HG).
             unshelve eexists (inl (exist _ (rsp, mo', es) _)); [cbn; rewrite EQ; auto 6| cbn]. rewrite EQ. apply t_eq_refl.
          -- destruct (NE code moE' Hex) as (mo' & EQ & Hh' & Hss).
             unshelve eexists (inr (exist _ (code, mo') _)); [cbn| cbn].
             { rewrite <- EQ, V_fs in Hss. split; [exact Hss|]. split; [rewrite EQ; exact Hex| exact Hh']. }
             rewrite <- EQ, V_fs. apply t_eq_refl.
  Qed.
End RealizeS2.

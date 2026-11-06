(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Monad.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach Bridge TSim DriverSim.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Notation tsh := (tshape node nstep nexit) (only parsing).

Definition meq (m1 m2 : Model) : Prop := m_fds m1 = m_fds m2 /\ m_fs m1 = m_fs m2.

Lemma meq_refl : forall m, meq m m. Proof. intros; split; reflexivity. Qed.
Lemma meq_sym : forall m1 m2, meq m1 m2 -> meq m2 m1. Proof. intros m1 m2 [A B]; split; congruence. Qed.
Lemma meq_trans : forall m1 m2 m3, meq m1 m2 -> meq m2 m3 -> meq m1 m3. Proof. intros m1 m2 m3 [A B] [C D]; split; congruence. Qed.

Definition fdn (n : node) : Prop := fdnode n \/ match n with NExit _ => True | _ => False end.

Fixpoint fdtree {R} (t : itree node R) : Prop :=
  match t with Ret _ => True | Vis n k => fdn n /\ forall r, fdtree (k r) end.

Lemma fdtree_bind {A B} : forall (t : itree node A) (f : A -> itree node B),
  fdtree t -> (forall a, fdtree (f a)) -> fdtree (ITree.bind node t f).
Proof. induction t as [r|n k IH]; intros f Ht Hf; cbn in *; [apply Hf|]. destruct Ht as [Hn Hk]. split; [exact Hn|]. intros r. apply IH; auto. Qed.

Lemma fdupd2_meq : forall m1 m1' m2 m2', meq m1 m2 -> fdupd2 m1 m1' m2 m2' -> meq m1' m2'.
Proof.
  intros m1 m1' m2 m2' [EF ES] [[-> ->] | (f & -> & ->)]; [split; assumption|].
  split; [rewrite !m_fds_with_fds; reflexivity| rewrite !m_fs_with_fds; exact ES].
Qed.

Lemma fdtree_tsim {R} : forall (t : itree node R) m1 m2,
  fdtree t -> meq m1 m2 -> tsim (fun r m1' r' m2' => r = r' /\ meq m1' m2') t m1 t m2.
Proof.
  induction t as [r | n k IH]; intros m1 m2 Ht HM; cbn [tsim].
  - split; [reflexivity| exact HM].
  - destruct Ht as [Hn Hk]. split.
    + intros rsp m1' evs ST. destruct Hn as [Hfd | Hex].
      * destruct (fd_transfer n m1 m2 rsp m1' evs Hfd (proj1 HM) (proj2 HM) ST) as (m2' & ST2 & U).
        exists rsp, m2'. split; [exact ST2|]. apply IH; [apply Hk| exact (fdupd2_meq _ _ _ _ HM U)].
      * destruct n; contradiction.
    + intros code m1' EX. destruct n; try (exfalso; exact EX). cbn [nexit] in EX |- *. destruct EX as [-> ->].
      eexists. split; [split; reflexivity|]. rewrite !m_fs_with_halted. symmetry. exact (proj2 HM).
Qed.

Theorem tsh_fdtree_cong {R} : forall (t : itree node R) (K : R -> Model -> TSet) m1 m2,
  fdtree t -> meq m1 m2 -> (forall r m1' m2', meq m1' m2' -> t_eq (K r m1') (K r m2')) ->
  t_eq (tsh t m1 K) (tsh t m2 K).
Proof.
  intros t K m1 m2 Ht HM HK. apply t_eq_of_incl.
  - apply (tsim_tshape _ K K t m1 t m2 (fdtree_tsim t m1 m2 Ht HM)). intros r m1' r' m2' [<- H]. apply t_incl_of_eq. apply HK. exact H.
  - apply (tsim_tshape _ K K t m2 t m1 (fdtree_tsim t m2 m1 Ht (meq_sym _ _ HM))). intros r m2' r' m1' [<- H]. apply t_incl_of_eq. apply HK. exact H.
Qed.

Section RealizeS.
  Variable segs : list Segment.
  Variable AS : Type.
  Variable V : AS -> Model -> Model.
  Variable INV : config -> AS -> Prop.
  Variable ATN : node -> machine_state -> AS -> Prop.
  Variable GOOD : node -> resp -> Prop.

  Definition SEAM (P : machine_state -> AS -> Prop) (ms : machine_state) (a : AS) : Prop :=
    forall mo, INV (mkCfg ms mo) a ->
      safe_reach segs (fun c' => exists a', INV c' a' /\ meq (V a mo) (V a' (cfg_model c')) /\ P (cfg_ms c') a') (mkCfg ms mo).

  Fixpoint implS {R} (t : itree node R) (Q : R -> machine_state -> AS -> Prop) (ms : machine_state) (a : AS) {struct t} : Prop :=
    match t with
    | Ret r => SEAM (fun ms' a' => Q r ms' a') ms a
    | Vis n k => SEAM (fun ms1 a1 => ATN n ms1 a1 /\ forall rsp, GOOD n rsp -> implS (k rsp) Q (nret ms1 rsp) a1) ms a
    end.

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

  #[using="Type"] Lemma t_eq_alt_bi' {I J} (f : I -> TSet) (g : J -> TSet) :
    (forall i, exists j, t_eq (f i) (g j)) -> (forall j, exists i, t_eq (f i) (g j)) -> t_eq (t_alt f) (t_alt g).
  Proof.
    intros FG GF tr. unfold t_alt. split.
    - intros [i Hi]. destruct (FG i) as [j E]. exists j. apply E. exact Hi.
    - intros [j Hj]. destruct (GF j) as [i E]. exists i. apply E. exact Hj.
  Qed.

  #[using="V_fs NODE"] Theorem implS_realizes {R} : forall (t : itree node R) (Q : R -> machine_state -> AS -> Prop) (K : R -> Model -> TSet) ms a mo,
    fdtree t ->
    implS t Q ms a -> INV (mkCfg ms mo) a ->
    (forall r ms' a' mo', Q r ms' a' -> INV (mkCfg ms' mo') a' -> realizes segs (mkCfg ms' mo') (K r (V a' mo'))) ->
    (forall r m1 m2, meq m1 m2 -> t_eq (K r m1) (K r m2)) ->
    realizes segs (mkCfg ms mo) (tsh t (V a mo) K).
  Proof.
    induction t as [r | n k IH]; intros Q K ms a mo Ht HI HINV HK KC; cbn [implS] in HI; cbn [tshape].
    - apply (sr_realizes segs _ _ _ (HI mo HINV)). intros [ms' mo'] (a' & HINV' & HM & HQ). cbn [cfg_ms cfg_model] in *.
      eapply rz_conseq; [exact (HK r ms' a' mo' HQ HINV')|]. apply KC. apply meq_sym. exact HM.
    - destruct Ht as [Hn Hk].
      apply (sr_realizes segs _ _ _ (HI mo HINV)). intros [ms1 mo1] (a1 & HINV1 & HM & HAT & HC). cbn [cfg_ms cfg_model] in *.

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
        * destruct PF as (Hss & Hst & HINV' & HG). exact (IH rsp Q K (nret ms1 rsp) a1 mo' (Hk rsp) (HC rsp HG) HINV' HK KC).
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

  #[using="Type"] Lemma SEAM_ret : forall (P : machine_state -> AS -> Prop) ms a, P ms a -> SEAM P ms a.
  Proof. intros P ms a HP mo HINV. apply sr_done. exists a. split; [exact HINV|]. split; [apply meq_refl| exact HP]. Qed.

  #[using="Type"] Lemma SEAM_mono : forall (P P' : machine_state -> AS -> Prop) ms a,
    SEAM P ms a -> (forall ms' a', P ms' a' -> P' ms' a') -> SEAM P' ms a.
  Proof.
    intros P P' ms a H HP mo HINV. eapply sr_mono; [exact (H mo HINV)|]. intros c' (a' & A & B & C). exists a'. auto.
  Qed.

  #[using="Type"] Lemma SEAM_bind : forall (P P' : machine_state -> AS -> Prop) ms a,
    SEAM P ms a -> (forall ms' a', P ms' a' -> SEAM P' ms' a') -> SEAM P' ms a.
  Proof.
    intros P P' ms a H HP mo HINV. eapply sr_bind; [exact (H mo HINV)|].
    intros [ms' mo'] (a' & HINV' & HM & HPa). cbn [cfg_ms cfg_model] in *.
    eapply sr_mono; [exact (HP ms' a' HPa mo' HINV')|]. intros c'' (a'' & A & B & C). exists a''. split; [exact A|]. split; [| exact C].
    eapply meq_trans; [exact HM| exact B].
  Qed.

  #[using="Type"] Lemma implS_ret {R} : forall (Q : R -> machine_state -> AS -> Prop) r ms a, Q r ms a -> implS (Ret r) Q ms a.
  Proof. intros. cbn. apply SEAM_ret. assumption. Qed.

  #[using="Type"] Lemma implS_seam {R} : forall (t : itree node R) Q (P : machine_state -> AS -> Prop) ms a,
    SEAM P ms a -> (forall ms' a', P ms' a' -> implS t Q ms' a') -> implS t Q ms a.
  Proof.
    intros t Q P ms a HS HK. destruct t as [r | n k]; cbn [implS] in *; (eapply SEAM_bind; [exact HS| exact HK]).
  Qed.

  #[using="Type"] Lemma implS_mono {R} : forall (t : itree node R) (Q Q' : R -> machine_state -> AS -> Prop) ms a,
    implS t Q ms a -> (forall r ms' a', Q r ms' a' -> Q' r ms' a') -> implS t Q' ms a.
  Proof.
    induction t as [r | n k IH]; intros Q Q' ms a H HQ; cbn [implS] in *.
    - eapply SEAM_mono; [exact H| intros ms' a'; apply HQ].
    - eapply SEAM_mono; [exact H|]. intros ms' a' [HAT HC]. split; [exact HAT|]. intros rsp HG. eapply IH; [apply HC; exact HG| exact HQ].
  Qed.

  #[using="Type"] Lemma implS_node {R} : forall n (k : resp -> itree node R) Q ms a,
    SEAM (fun ms1 a1 => ATN n ms1 a1 /\ forall rsp, GOOD n rsp -> implS (k rsp) Q (nret ms1 rsp) a1) ms a -> implS (Vis n k) Q ms a.
  Proof. intros. cbn. assumption. Qed.

  #[using="Type"] Lemma implS_bind {A B} : forall (t : itree node A) (f : A -> itree node B) Q1 Q ms a,
    implS t Q1 ms a -> (forall r ms' a', Q1 r ms' a' -> implS (f r) Q ms' a') -> implS (ITree.bind node t f) Q ms a.
  Proof.
    induction t as [r | n k IH]; intros f Q1 Q ms a H HF; cbn [ITree.bind implS] in *.
    - eapply implS_seam; [exact H| intros ms' a'; apply HF].
    - eapply SEAM_mono; [exact H|]. intros ms1 a1 [HAT HC]. split; [exact HAT|]. intros rsp HG. eapply IH; [apply HC; exact HG| exact HF].
  Qed.

  Definition implSM {St A} (c : Monad.M St A) (s : St) (Q : A -> St -> machine_state -> AS -> Prop) (ms : machine_state) (a : AS) : Prop :=
    implS (c s) (fun r ms' a' => match r with Ok p => Q (fst p) (snd p) ms' a' | Unr => True end) ms a.

  #[using="Type"] Lemma implSM_ret {St A} : forall (x : A) (s : St) Q ms a, Q x s ms a -> implSM (mret x) s Q ms a.
  Proof. intros. unfold implSM, mret. apply implS_ret. assumption. Qed.

  #[using="Type"] Lemma implSM_bind {St A B} : forall (m : Monad.M St A) (f : A -> Monad.M St B) s Q1 Q ms a,
    implSM m s Q1 ms a -> (forall x s' ms' a', Q1 x s' ms' a' -> implSM (f x) s' Q ms' a') -> implSM (mbind m f) s Q ms a.
  Proof.
    intros m f s Q1 Q ms a H HF. unfold implSM, mbind, ebind in *. eapply implS_bind; [exact H|].
    intros [|[x s']] ms' a' HQ; [apply implS_ret; exact I| exact (HF x s' ms' a' HQ)].
  Qed.
End RealizeS.

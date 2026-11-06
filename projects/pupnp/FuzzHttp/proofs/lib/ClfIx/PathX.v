(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Monad MSafe.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize TSim MSim.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Fixpoint tpaths {R} (t : itree node R) (mo : Model) (tr : list event) (r : R) (mo' : Model) : Prop :=
  match t with
  | Ret r0 => r0 = r /\ mo' = mo /\ tr = []
  | Vis n k => match n with NExit _ => False | _ => True end /\ nsafe n mo /\
               exists rsp mo1 evs tr', nstep n mo rsp mo1 evs /\ tpaths (k rsp) mo1 tr' r mo' /\ tr = evs ++ tr'
  end.

Lemma tpaths_bind {A B} : forall (t : itree node A) (f : A -> itree node B) mo tr1 a mo1 tr2 b mo2,
  tpaths t mo tr1 a mo1 -> tpaths (f a) mo1 tr2 b mo2 -> tpaths (ITree.bind node t f) mo (tr1 ++ tr2) b mo2.
Proof.
  induction t as [r | n k IH]; intros f mo tr1 a mo1 tr2 b mo2 H1 H2; cbn in *.
  - destruct H1 as (-> & -> & ->). exact H2.
  - destruct H1 as (Hne & Hs & rsp & mo' & evs & tr' & Hn & Hp & ->). split; [exact Hne|]. split; [exact Hs|].
    exists rsp, mo', evs, (tr' ++ tr2). split; [exact Hn|]. split; [eapply IH; eauto|]. symmetry. apply app_assoc.
Qed.

Lemma tpaths_ebind {A B} : forall (t : itree node (exc A)) (f : A -> itree node (exc B)) mo tr1 a mo1 tr2 b mo2,
  tpaths t mo tr1 (Ok a) mo1 -> tpaths (f a) mo1 tr2 b mo2 -> tpaths (ebind t f) mo (tr1 ++ tr2) b mo2.
Proof. intros. unfold ebind. eapply tpaths_bind; [eassumption|]. cbn beta iota. assumption. Qed.

Lemma tpaths_ret {R} : forall (r : R) mo, tpaths (Ret r) mo [] r mo.
Proof. intros. cbn. auto. Qed.

Section Star.
  Variable segs : list Segment.

  #[using="Type"] Theorem impl_tpaths_star {R} : forall (t : itree node R) Q ms mo tr r mo',
    impl segs (at_node segs) t Q ms -> tpaths t mo tr r mo' -> m_halted mo = None -> minv mo ->
    exists ms', star_cfg segs ACFG (mkCfg ms mo) tr (mkCfg ms' mo') /\ Q r ms' /\ m_halted mo' = None /\ minv mo'.
  Proof.
    induction t as [r0 | n k IH]; intros Q ms mo tr r mo' Himpl Hp Hh Hm; cbn in Himpl, Hp.
    - destruct Hp as (-> & -> & ->). destruct Himpl as (ms' & Hs & HQ).
      exists ms'. split; [exact (msteps_star segs ACFG ms ms' mo (minv_nolazy _ Hm) Hh Hs)|]. auto.
    - destruct Himpl as (ms1 & Hs & Hat & Hk).
      destruct Hp as (Hne & Hsafe & rsp & mo1 & evs & tr' & Hn & Hp' & ->).
      destruct (nonexit_node_facts segs n ms1 mo Hne Hat Hm Hh Hsafe) as (_ & Ks & _).
      destruct (Ks _ _ _ Hn) as (Hh1 & Hm1 & Hss).
      destruct (IH rsp Q (nret ms1 rsp) mo1 tr' r mo' (Hk rsp) Hp' Hh1 Hm1) as (ms' & Hstar & HQ & Hh' & Hm').
      exists ms'. split; [| auto].
      change (evs ++ tr') with ([] ++ (evs ++ tr')).
      eapply star_cfg_trans; [exact (msteps_star segs ACFG ms ms1 mo (minv_nolazy _ Hm) Hh Hs)|].
      eapply star_cfg_step; [exact Hss | exact Hstar].
  Qed.

  #[using="Type"] Corollary implM_tpaths_star {St A} : forall (c : M St A) (s : St) (Q : A -> St -> machine_state -> Prop) ms mo tr a s' mo',
    implM segs c s Q ms -> tpaths (c s) mo tr (Ok (a, s')) mo' -> m_halted mo = None -> minv mo ->
    exists ms', star_cfg segs ACFG (mkCfg ms mo) tr (mkCfg ms' mo') /\ Q a s' ms' /\ m_halted mo' = None /\ minv mo'.
  Proof.
    intros c s Q ms mo tr a s' mo' Hi Hp Hh Hm.
    destruct (impl_tpaths_star (c s) _ ms mo tr (Ok (a, s')) mo' Hi Hp Hh Hm) as (ms' & Hst & HQ & H'). cbn in HQ.
    exists ms'. auto.
  Qed.
End Star.

Lemma tsim_twf_conj {RA RB} : forall (L : RA -> Model -> RB -> Model -> Prop) (PA : RA -> Model -> Prop)
    (tA : itree node RA) moA (tB : itree node RB) moB,
  tsim L tA moA tB moB -> twf tA moA PA ->
  tsim (fun rA moA' rB moB' => L rA moA' rB moB' /\ PA rA moA') tA moA tB moB.
Proof.
  intros L PA tA. induction tA as [rA | nA kA IH]; intros moA [rB | nB kB] moB HS HW; cbn in HS, HW |- *; try contradiction.
  - split; assumption.
  - destruct HS as [F XF]. destruct HW as [_ HK]. split; [| exact XF].
    intros rspA moA' evs ST. destruct (F _ _ _ ST) as (rspB & moB' & STB & H).
    exists rspB, moB'. split; [exact STB|]. apply IH; [exact H | exact (HK _ _ _ ST)].
Qed.

Lemma msim_mspec_conj {StA StB A B} : forall (R : rel StA StB) (P : assn StA) (cA : M StA A) (cB : M StB B)
    (Q : A -> B -> rel StA StB) (Q1 : A -> assn StA),
  msim R cA cB Q -> mspec P cA Q1 ->
  msim (fun sA moA sB moB => R sA moA sB moB /\ P sA moA) cA cB
       (fun a b sA moA sB moB => Q a b sA moA sB moB /\ Q1 a sA moA).
Proof.
  intros R P cA cB Q Q1 HS HM sA moA sB moB [HR HP].
  eapply tsim_mono; [exact (tsim_twf_conj _ _ _ _ _ _ (HS _ _ _ _ HR) (HM _ _ HP))|].
  intros [|[a sA']] moA' [|[b sB']] moB'; cbn; intros [H1 H2]; auto.
Qed.

Lemma tpaths_mbind {St A B} : forall (m : M St A) (f : A -> M St B) s mo a s1 mo1 r mo2,
  tpaths (m s) mo [] (Ok (a, s1)) mo1 -> tpaths (f a s1) mo1 [] r mo2 -> tpaths (mbind m f s) mo [] r mo2.
Proof.
  intros m f s mo a s1 mo1 r mo2 H1 H2. unfold mbind. change ([] : list event) with ([] ++ [] : list event).
  eapply tpaths_ebind; [exact H1| exact H2].
Qed.

Lemma tpaths_mret {St A} : forall (a : A) (s : St) mo, tpaths (mret a s) mo [] (Ok (a, s)) mo.
Proof. intros. apply tpaths_ret. Qed.

Lemma tpaths_msys {St A} : forall n (dec : resp -> option A) (s : St) mo rsp mo1 a,
  match n with NExit _ => False | _ => True end -> nsafe n mo -> nstep n mo rsp mo1 [] -> dec rsp = Some a ->
  tpaths (msys n dec s) mo [] (Ok (a, s)) mo1.
Proof.
  intros n dec s mo rsp mo1 a Hne Hs Hn Hd. unfold msys, enode. cbn [tpaths]. split; [exact Hne|]. split; [exact Hs|].
  exists rsp, mo1, [], []. split; [exact Hn|]. rewrite Hd. cbn. repeat split; reflexivity.
Qed.

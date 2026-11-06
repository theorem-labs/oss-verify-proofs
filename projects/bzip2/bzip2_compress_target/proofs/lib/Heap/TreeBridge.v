(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Progress.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec CatSim ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require MState Exec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes EvtBridge.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.MState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Exec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.EvtBridge.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import Monad MSafe.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From Stdlib Require Import Classical_Prop.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Common Require CfgStep.
Import ListNotations.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Notation sspec := Specs.syscall_spec (only parsing).
Notation SOk := LinuxProcessSem.Monad.Ok (only parsing).
Notation SUnmodeled := LinuxProcessSem.Monad.Unmodeled (only parsing).
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mm_args_agree (i i' : SyscallInput) : Prop :=
  in_sysno i = in_sysno i' /\
  ( (bv_unsigned (in_sysno i) = 214 /\ in_arg i 0 = in_arg i' 0)
  \/ (bv_unsigned (in_sysno i) = 215 /\ in_arg i 0 = in_arg i' 0 /\ in_arg i 1 = in_arg i' 1)
  \/ (bv_unsigned (in_sysno i) = 222 /\ in_arg i 0 = in_arg i' 0 /\ in_arg i 1 = in_arg i' 1 /\ in_arg i 2 = in_arg i' 2
       /\ in_arg i 3 = in_arg i' 3 /\ in_arg i 4 = in_arg i' 4 /\ in_arg i 5 = in_arg i' 5)
  \/ (bv_unsigned (in_sysno i) = 226 /\ in_arg i 0 = in_arg i' 0 /\ in_arg i 1 = in_arg i' 1 /\ in_arg i 2 = in_arg i' 2)).

Lemma check_syscall_mm_ext : forall i i' eff m,
  mm_args_agree i i' -> check_syscall i eff m = check_syscall i' eff m.
Proof.
  intros i i' eff m [Hno H]. unfold check_syscall. rewrite <- Hno.
  destruct H as [(E & A0)|[(E & A0 & A1)|[(E & A0 & A1 & A2 & A3 & A4 & A5)|(E & A0 & A1 & A2)]]]; rewrite E;
    cbn -[check_brk check_munmap check_mmap check_mprotect in_arg]; congruence.
Qed.

Lemma syscall_spec_mm_ext : forall i i' m o,
  mm_args_agree i i' -> (sspec i m o <-> sspec i' m o).
Proof.
  intros i i' m o H. destruct o as [eff m' evs|].
  - rewrite <- !check_syscall_ok_iff. rewrite (check_syscall_mm_ext i i' eff m H). tauto.
  - rewrite <- !(check_syscall_err_iff _ (mkEffect (Z_to_bv 64 0) [] [])).
    rewrite (check_syscall_mm_ext i i' _ m H). tauto.
Qed.

Lemma mm_args_agree_sym : forall i i', mm_args_agree i i' -> mm_args_agree i' i.
Proof.
  intros i i' [Hno H]. split; [symmetry; exact Hno|]. rewrite <- Hno.
  destruct H as [(E & A0)|[(E & A0 & A1)|[(E & A0 & A1 & A2 & A3 & A4 & A5)|(E & A0 & A1 & A2)]]];
    [left | right; left | right; right; left | right; right; right]; repeat split; auto.
Qed.

Lemma mm_args_agree_a0 : forall i i', mm_args_agree i i' -> in_arg i 0 = in_arg i' 0.
Proof.
  intros i i' [_ H].
  destruct H as [(E & A0)|[(E & A0 & A1)|[(E & A0 & A1 & A2 & A3 & A4 & A5)|(E & A0 & A1 & A2)]]]; exact A0.
Qed.

Lemma spurious_mm_agree : forall cfg i i' m eff,
  mm_args_agree i i' -> spurious_refusal_cfg cfg i m eff -> spurious_refusal_cfg cfg i' m eff.
Proof.
  intros cfg i i' m eff H (Hoff & Hr & (eff' & m' & evs' & Hs' & Hnr')).
  pose proof (proj1 H) as Hno. pose proof (mm_args_agree_a0 i i' H) as Ha0.
  assert (Er : forall r, refusal_b i m r = refusal_b i' m r).
  { intros r. unfold refusal_b. rewrite Hno, Ha0. reflexivity. }
  split; [unfold injected_family_off in *; rewrite <- Hno; exact Hoff|].
  split; [rewrite <- Er; exact Hr|].
  exists eff', m', evs'. split; [apply (syscall_spec_mm_ext i i' m _ H); exact Hs'| rewrite <- Er; exact Hnr'].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Bridge.
Variable segs : list Segment.

Lemma at_node_agree : forall n ms i,
  at_node segs n ms -> node_input n = Some i ->
  exists x8, ms_svc_pending ms = Some x8 /\ mm_args_agree (sys_input segs ms x8) i.
Proof.
  intros n ms i Hat Hi.
  destruct n; cbn in Hi; try discriminate; injection Hi as <-; cbn in Hat.
  - destruct Hat as (Hsvc & A0). exists (Z_to_bv 64 214). split; [exact Hsvc|].
    split; [reflexivity|]. left.
    rewrite in_sysno_si. split; [reflexivity|]. rewrite in_a0_si. exact A0.
  - cps_destruct Hat as (Hsvc & A0 & A1 & A2 & A3 & A4 & A5). exists (Z_to_bv 64 222). split; [exact Hsvc|].
    split; [reflexivity|]. right; right; left.
    rewrite in_sysno_si, in_a0_si, in_a1_si, in_a2_si, in_a3_si, in_a4_si, in_a5_si. cbn. repeat split; assumption.
  - cps_destruct Hat as (Hsvc & A0 & A1). exists (Z_to_bv 64 215). split; [exact Hsvc|].
    split; [reflexivity|]. right; left.
    rewrite in_sysno_si, in_a0_si, in_a1_si. cbn. repeat split; assumption.
  - cps_destruct Hat as (Hsvc & A0 & A1 & A2). exists (Z_to_bv 64 226). split; [exact Hsvc|].
    split; [reflexivity|]. right; right; right.
    rewrite in_sysno_si, in_a0_si, in_a1_si, in_a2_si. cbn. repeat split; assumption.
Qed.

Lemma at_node_input : forall n ms i,
  at_node segs n ms -> node_input n = Some i ->
  exists x8, ms_svc_pending ms = Some x8 /\ forall m o, sspec (sys_input segs ms x8) m o <-> sspec i m o.
Proof.
  intros n ms i Hat Hi. destruct (at_node_agree n ms i Hat Hi) as (x8 & Hsvc & Ha).
  exists x8. split; [exact Hsvc|]. intros m o. apply syscall_spec_mm_ext. exact Ha.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ibenign (i : SyscallInput) (MD : Model) : Prop :=
  forall eff MD' evs, sspec i MD (SOk eff MD' evs) -> evs = [] /\ m_halted MD' = None /\ m_vm_lazy MD' = [].

Definition mm_idx (i : SyscallInput) (MD : Model) : Type :=
  { p : SyscallEffect * Model | sspec i MD (SOk (fst p) (snd p) [])
                                /\ ~ spurious_refusal_cfg CfgStep.kit_cfg i MD (fst p) }.

Lemma node_ok_mm : forall ms MD x8 i,
  ms_svc_pending ms = Some x8 -> m_halted MD = None ->
  mm_args_agree (sys_input segs ms x8) i ->
  ~ sspec i MD SUnmodeled -> ibenign i MD ->
  node_ok segs (mkCfg ms MD) (mm_idx i MD) (fun _ => [])
          (fun p => mkCfg (nret ms (fst (proj1_sig p))) (snd (proj1_sig p))).
Proof.
  intros ms MD x8 i Hsvc Hh Hag Hsafe Hb.
  pose proof (fun m o => syscall_spec_mm_ext _ _ m o Hag) as Hiff. split.
  - intros [[eff MD'] [Hs Hns]]. cbn.
    cps_destruct (Hb _ _ _ Hs) as (_ & Hh' & Hl').
    unfold nret. eapply sstep_cfg_syscall; [exact Hh| exact Hsvc| apply Hiff; exact Hs
      | intros Hsp; apply Hns; exact (spurious_mm_agree _ _ _ _ _ Hag Hsp) | exact Hh'|].
    apply materialize_model_accesses_no_lazy. exact Hl'.
  - intros e st Hss. inversion Hss; subst.
    + (* [comment removed for export] *) congruence.
    + congruence.
    + congruence.
    + (* [comment removed for export] *)
      match goal with H : ms_svc_pending ms = Some ?x |- _ => rewrite Hsvc in H; injection H as <- end.
      match goal with H : sspec (sys_input segs ms x8) MD _ |- _ => apply Hiff in H; rename H into Hs end.
      cps_destruct (Hb _ _ _ Hs) as (-> & Hh' & Hl').
      match goal with H : materialize_model_accesses ?m ?a = Some ?m2 |- _ =>
        rewrite (materialize_model_accesses_no_lazy _ _ Hl') in H; injection H as <- end.
      match goal with H : ~ spurious_refusal_cfg _ (sys_input segs ms x8) MD _ |- _ => rename H into Hns end.
      assert (Hns' : ~ spurious_refusal_cfg CfgStep.kit_cfg i MD eff)
        by (intros Hsp; apply Hns; exact (spurious_mm_agree _ _ _ _ _ (mm_args_agree_sym _ _ Hag) Hsp)).
      exists (exist _ (eff, model') (conj Hs Hns')). split; reflexivity.
    + (* [comment removed for export] *)
      match goal with H : ms_svc_pending ms = Some ?x |- _ => rewrite Hsvc in H; injection H as <- end.
      match goal with H : sspec (sys_input segs ms x8) MD _ |- _ => apply Hiff in H; rename H into Hs end.
      cps_destruct (Hb _ _ _ Hs) as (_ & _ & Hl').
      match goal with H : materialize_model_accesses ?m ?a = None |- _ =>
        rewrite (materialize_model_accesses_no_lazy _ _ Hl') in H; discriminate H end.
    + (* [comment removed for export] *)
      match goal with H : ms_svc_pending ms = Some ?x |- _ => rewrite Hsvc in H; injection H as <- end.
      match goal with H : sspec (sys_input segs ms x8) MD _ |- _ => apply Hiff in H; rename H into Hs end.
      cps_destruct (Hb _ _ _ Hs) as (_ & Hh' & _). congruence.
    + (* [comment removed for export] *)
      match goal with H : ms_svc_pending ms = Some ?x |- _ => rewrite Hsvc in H; injection H as <- end.
      match goal with H : sspec (sys_input segs ms x8) MD _ |- _ => apply Hiff in H; rename H into Hs end.
      cps_destruct (Hb _ _ _ Hs) as (_ & Hh' & _).
      match goal with H : m_killed ?m = Some ?sg |- _ => rewrite (m_killed_of_m_halted_none _ Hh') in H; discriminate H end.
    + (* [comment removed for export] *)
      match goal with H : ms_svc_pending ms = Some ?x |- _ => rewrite Hsvc in H; injection H as <- end.
      match goal with H : sspec (sys_input segs ms x8) MD _ |- _ => apply Hiff in H; rename H into Hs end.
      exact (False_ind _ (Hsafe Hs)).
Qed.

(* [comment removed for export] *)
Lemma mm_progress : forall i MD,
  ~ sspec i MD SUnmodeled -> ibenign i MD -> exists eff MD', sspec i MD (SOk eff MD' []).
Proof.
  intros i MD Hsafe Hb. pose proof (receptive i MD) as R.
  destruct (syscall_spec_witness i MD) as [eff MD' evs|] eqn:E.
  - cps_destruct (Hb _ _ _ R) as (-> & _ & _). exists eff, MD'. exact R.
  - exact (False_ind _ (Hsafe R)).
Qed.

Lemma mm_progress_c : forall i MD,
  ~ sspec i MD SUnmodeled -> ibenign i MD ->
  exists eff MD', sspec i MD (SOk eff MD' []) /\ ~ spurious_refusal_cfg CfgStep.kit_cfg i MD eff.
Proof.
  intros i MD Hsafe Hb.
  destruct (mm_progress i MD Hsafe Hb) as (eff0 & MD0 & H0).
  destruct (classic (exists eff' m' evs', sspec i MD (SOk eff' m' evs')
                       /\ refusal_b i MD (eff_ret eff') = false)) as [(eff' & m' & evs' & Hs' & Hnr) | Hnone].
  - cps_destruct (Hb _ _ _ Hs') as (-> & _ & _). exists eff', m'.
    split; [exact Hs'| apply spurious_refusal_not_refusal; exact Hnr].
  - exists eff0, MD0. split; [exact H0|]. intros (_ & _ & Hex). exact (Hnone Hex).
Qed.

Lemma rz_mm_node : forall ms MD x8 i (K : SyscallEffect -> Model -> TSet),
  ms_svc_pending ms = Some x8 -> m_halted MD = None ->
  mm_args_agree (sys_input segs ms x8) i ->
  ~ sspec i MD SUnmodeled -> ibenign i MD ->
  (forall eff MD', sspec i MD (SOk eff MD' []) -> ~ spurious_refusal_cfg CfgStep.kit_cfg i MD eff ->
     realizes segs (mkCfg (nret ms eff) MD') (K eff MD')) ->
  realizes segs (mkCfg ms MD) (fun tr => exists eff MD', sspec i MD (SOk eff MD' [])
                                 /\ ~ spurious_refusal_cfg CfgStep.kit_cfg i MD eff /\ K eff MD' tr).
Proof.
  intros ms MD x8 i K Hsvc Hh Hag Hsafe Hb HK.
  cps_destruct (mm_progress_c i MD Hsafe Hb) as (eff0 & MD0 & H0 & Hn0).
  eapply rz_conseq.
  - apply (rz_node segs (mkCfg ms MD) (mm_idx i MD) (fun _ => [])
             (fun p => mkCfg (nret ms (fst (proj1_sig p))) (snd (proj1_sig p)))
             (fun p => K (fst (proj1_sig p)) (snd (proj1_sig p)))
             (exist _ (eff0, MD0) (conj H0 Hn0))).
    + apply (node_ok_mm ms MD x8 i); assumption.
    + intros [[eff MD'] [Hs Hns]]. cbn. apply HK; assumption.
  - intros tr. unfold t_alt, t_emit. split.
    + intros [[[eff MD'] [Hs Hns]] H]. cbn in H. destruct H as [Hp|(tr' & -> & HT)].
      * apply is_prefix_nil_r in Hp. subst tr.
        exists eff, MD'. split; [exact Hs|]. split; [exact Hns|]. eapply realizes_nonempty. apply HK; assumption.
      * exists eff, MD'. split; [exact Hs|]. split; [exact Hns| exact HT].
    + cps_intros (eff & MD' & Hs & Hns & HT). exists (exist _ (eff, MD') (conj Hs Hns)). cbn. right. exists tr. split; [reflexivity| exact HT].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition t_leaves {A} (t : itree node (exc A)) (MD : Model) (TT : A -> Model -> TSet) : TSet :=
  fun tr => exists a MD', tpath nstep t MD [] (Ok a) MD' /\ TT a MD' tr.

Theorem impl_twf_realizes {A} : forall (t : itree node (exc A)) (Q : A -> machine_state -> Prop)
    (TT : A -> Model -> TSet) ms MD,
  m_halted MD = None -> m_vm_lazy MD = [] ->
  impl segs (at_node segs) t (epost Q) ms ->
  twf t MD (fun r MD' => match r with
                         | Unr => False
                         | Ok a => forall ms', Q a ms' -> realizes segs (mkCfg ms' MD') (TT a MD')
                         end) ->
  realizes segs (mkCfg ms MD) (t_leaves t MD TT).
Proof.
  intros t. induction t as [r|n k IH]; intros Q TT ms MD Hh Hl Himpl Htwf.
  - cbn in Himpl, Htwf. destruct r as [|a]; [contradiction|].
    eapply rz_conseq.
    + eapply evt_realizes; [exact Hh| exact Hl| exact Himpl|]. intros ms' HQ. exact (Htwf ms' HQ).
    + intros tr. unfold t_leaves. cbn. split.
      * intros HT. exists a, MD. repeat split; auto.
      * cps_intros (a' & MD' & (E & -> & _) & HT). injection E as ->. exact HT.
  - cbn in Himpl, Htwf. destruct Htwf as [[Hsafe Hben] Hk].
    unfold nbenign in Hben. unfold nsafe in Hsafe.
    destruct (node_input n) as [i|] eqn:Hi; [|contradiction].
    eapply evt_realizes; [exact Hh| exact Hl| exact Himpl|]. intros ms1 [Hat Hkm].
    cps_destruct (at_node_agree n ms1 i Hat Hi) as (x8 & Hsvc & Hag).
    eapply rz_conseq.
    + apply (rz_mm_node ms1 MD x8 i (fun eff MD' => t_leaves (k eff) MD' TT) Hsvc Hh Hag Hsafe Hben).
      intros eff MD' Hs Hns. cps_destruct (Hben _ _ _ Hs) as (_ & Hh' & Hl').
      apply (IH eff Q TT (nret ms1 eff) MD' Hh' Hl' (Hkm eff)).
      eapply Hk. eapply nbenign_nstep; [exact Hi| unfold nbenign; rewrite Hi; exact Hben| exact Hs| exact Hns].
    + intros tr. unfold t_leaves. cbn. split.
      * cps_intros (eff & MD' & Hs & Hns & a & MD'' & Hp & HT). exists a, MD''. split; [|exact HT].
        exists eff, MD', [], []. split; [|split; [exact Hp| reflexivity]].
        eapply nbenign_nstep; [exact Hi| unfold nbenign; rewrite Hi; exact Hben| exact Hs| exact Hns].
      * cps_intros (a & MD'' & (rsp & mo1 & evs & tr' & Hst & Hp & E) & HT).
        symmetry in E. apply app_eq_nil in E. destruct E as [-> ->].
        destruct (nstep_mm_spec n MD i rsp mo1 [] Hi Hst) as [_ [Hs Hns]].
        exists rsp, mo1. split; [exact Hs|]. split; [exact Hns|]. exists a, MD''. split; [exact Hp| exact HT].
Qed.

(* [comment removed for export] *)
Lemma twf_reaches {A} : forall (t : itree node (exc A)) MD (P : exc A -> Model -> Prop),
  twf t MD P -> exists r MD', tpath nstep t MD [] r MD' /\ P r MD'.
Proof.
  intros t. induction t as [r|n k IH]; intros MD P H; cbn in H.
  - exists r, MD. cbn. repeat split; auto.
  - destruct H as [[Hsafe Hben] Hk]. unfold nbenign in Hben. unfold nsafe in Hsafe.
    destruct (node_input n) as [i|] eqn:Hi; [|contradiction].
    cps_destruct (mm_progress_c i MD Hsafe Hben) as (eff & MD' & Hs & Hns).
    assert (Hst : nstep n MD eff MD' []).
    { eapply nbenign_nstep; [exact Hi| unfold nbenign; rewrite Hi; exact Hben| exact Hs| exact Hns]. }
    cps_destruct (IH eff MD' P (Hk _ _ _ Hst)) as (r & MD'' & Hp & HP).
    exists r, MD''. split; [|exact HP]. cbn. exists eff, MD', [], []. repeat split; auto.
Qed.

(* [comment removed for export] *)
Lemma t_leaves_const {A} : forall (t : itree node (exc A)) MD (T : TSet) (P : exc A -> Model -> Prop),
  twf t MD P -> (forall MD', ~ P Unr MD') ->
  t_eq (t_leaves t MD (fun _ _ => T)) T.
Proof.
  intros t MD T P Htwf HP tr. unfold t_leaves. split.
  - cps_intros (a & MD' & _ & HT). exact HT.
  - intros HT. cps_destruct (twf_reaches t MD P Htwf) as (r & MD' & Hp & HPr).
    destruct r as [|a]; [exfalso; exact (HP _ HPr)|]. exists a, MD'. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma t_leaves_same {A} : forall (t : itree node (exc A)) MD (f : A -> bool) (T : TSet) (P : exc A -> Model -> Prop),
  twf t MD P -> (forall MD', ~ P Unr MD') ->
  t_eq (t_leaves t MD (fun a _ => if f a then T else T)) T.
Proof.
  intros t MD f T P Htwf HP tr. unfold t_leaves. split.
  - cps_intros (a & MD' & _ & HT). destruct (f a); exact HT.
  - intros HT. cps_destruct (twf_reaches t MD P Htwf) as (r & MD' & Hp & HPr).
    destruct r as [|a]; [exfalso; exact (HP _ HPr)|]. exists a, MD'. split; [exact Hp| destruct (f a); exact HT].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Corollary implM_mspec_realizes {St A} : forall (c : @Monad.M St A) (s : St)
    (Qm : A -> St -> machine_state -> Prop) (P : @assn St) (Qk : A -> @assn St)
    (TT : A * St -> Model -> TSet) ms MD,
  implM segs c s Qm ms -> mspec P c Qk -> P s MD ->
  m_halted MD = None -> m_vm_lazy MD = [] ->
  (forall a s' ms' MD', Qm a s' ms' -> Qk a s' MD' -> realizes segs (mkCfg ms' MD') (TT (a, s') MD')) ->
  realizes segs (mkCfg ms MD) (t_leaves (c s) MD TT).
Proof.
  intros c s Qm P Qk TT ms MD Hi Hm HP Hh Hl HK.
  apply (impl_twf_realizes (c s) (fun p => Qm (fst p) (snd p)) TT ms MD Hh Hl).
  - exact Hi.
  - eapply twf_mono; [exact (Hm s MD HP)|]. cbn. intros [|[a s']] mo1 H; [exact H|].
    cbn in H. intros ms' HQ. apply HK; assumption.
Qed.

End Bridge.

End ACeilS1.

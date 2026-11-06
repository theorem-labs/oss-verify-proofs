(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import PropExec MState Mem ITree Nodes Decode NodesCfg DecodeCfg ITreeCfg.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Ceiling Image Stage.
From OSSVerify.Proofs.openssl.pem.lib Require Import TopLevel Obligations.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import Prelim Monad Stdio Driver Prog Canon ModelInv ProgDetIface ProgDetLogic ProgDetNodes ProgDetDriver ProgDet.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require NodesCfgA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation nstep := NodesCfg.nstep_c (only parsing).
Import ListNotations.
Import ITree.Exc.

Local Notation lpin := (ITreeCfg.lpin node nstep nexit).

Lemma lpin_of_pinned : forall {R} (t : itree node R) mo tr0 c,
  (forall s, ttrace nstep nexit t mo s -> tr0 ++ s = c) -> lpin t mo tr0.
Proof.
  intros R t. induction t as [r|n k IH|v k IH]; intros mo tr0 c H; cbn [ITreeCfg.lpin].
  - exact I.
  - intros rsp mo' evs Hst. apply (IH rsp mo' (tr0 ++ evs) c). intros s Hs. rewrite <- app_assoc. apply H.
    cbn. right. exists rsp, mo', evs, s. split; [exact Hst|]. split; [exact Hs| reflexivity].
  - exists c. intros a Hv s Hs. apply H. cbn. exists a. split; assumption.
Qed.

Lemma pinned_of_twfE : forall {R} (X : list event -> Prop) (t : itree node (exc R)) mo tr0 c,
  forall P, twfE None X t mo tr0 P ->
  tsafe nstep Pn t mo -> leaves_unreachable_m nstep t mo ->
  (forall tr, X tr -> tr = c) ->
  forall s, ttrace nstep nexit t mo s -> tr0 ++ s = c.
Proof.
  intros R X t mo tr0 c P Hw Hs Hl HX s Ht.
  apply ttrace_split in Ht. destruct Ht as [Hx|(r & mo' & Hp)]; [| exfalso; exact (Hl _ _ _ Hp)].
  apply HX. exact (twfE_texit None X t mo tr0 _ s Hw (texit_nstep_stepR t mo s Hs Hx)).
Qed.

Open Scope Z_scope.

Lemma Xcanon_pin : forall b argv fs tr, Xcanon (Some b) argv fs tr -> tr = ct_events fs (ctrace_of argv fs b).
Proof. intros b argv fs tr (b' & Hb & ->). rewrite (Hb b eq_refl). reflexivity. Qed.

Theorem prog_lpin_gen : forall segs rstage pc ph lim,
  segs_low segs ->
  prog_no_enomem_stmt segs rstage pc ph lim ->
  forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input_w inp ->
  lpin (the_prog segs rstage inp en) (mo0 segs lim en inp) [].
Proof.
  intros segs rstage pc ph lim Hsegs Hne en inp Hve Hvi.
  pose proof (prog_model_ok (CE__ := run_ceiling en) segs rstage pc ph lim en inp Hsegs Hve Hvi
                (run_ceiling_eq segs pc ph en inp (valid_input_w_va_size _ Hvi) Hve)) as [Hl0 Hs0].
  pose proof (Hne en inp Hve Hvi) as Hne'. unfold the_prog in *.
  set (t := @prog (run_ceiling en) segs rstage (in_argv inp)) in *.
  set (mo := mo0 segs lim en inp) in *.
  assert (Hl : leaves_unreachable_m nstep t mo) by exact (NodesCfgA.leaves_unreachable_a_c t mo Hne' Hl0).
  assert (Hs : tsafe nstep nsafe t mo) by exact (NodesCfgA.tsafe_a_c nsafe t mo Hne' Hs0).
  assert (HPn : tsafe nstep Pn t mo) by (apply tsafe_Pn; [exact Hs| exact Hne'| apply mo0_minv| apply mo0_not_halted]).
  assert (Hargv : Forall (fun a => zlength a < 2^32) (argv_Z (in_argv inp))) by (apply argv_Z_short; exact (proj1 Hvi)).
  assert (Hfd : m_fds mo = fds_std) by (unfold mo, TopLevel.mo0; rewrite m_fds_init_model; reflexivity).
  assert (Hfs : m_fs mo = in_fs inp) by (unfold mo, TopLevel.mo0; rewrite m_fs_init_model; reflexivity).
  set (argv := argv_Z (in_argv inp)) in *.
  destruct (Z.eq_dec (Z.of_nat (length argv)) 2) as [E2|NE2].
  2:{ (* [comment removed for export] *)
      apply (lpin_of_pinned t mo [] (ct_events (m_fs mo) (ctrace_of argv (m_fs mo) false))).
      apply (pinned_of_twfE (Xcanon None argv (m_fs mo)) t mo [] _ _
               (prog_twfE (CE__ := run_ceiling en) None segs rstage (in_argv inp) mo Hargv Hfd) HPn Hl).
      intros tr (b & _ & ->). rewrite !(ctrace_of_usage argv _ _ NE2). reflexivity. }
  (* [comment removed for export] *)
  unfold t, prog, prog_with, startup.
  unfold t, prog, prog_with, startup in HPn, Hl.
  cbn [Monad.mbind Monad.msys Monad.mret ITree.ebind ITree.enode ITree.bind ITree.tsafe fst snd] in HPn, Hl.
  cbn [Monad.mbind Monad.msys Monad.mret ITree.ebind ITree.enode ITree.bind ITreeCfg.lpin fst snd].
  destruct HPn as [HPn0 HPnk].
  intros rsp mo1 evs Hst.
  pose proof (HPnk rsp mo1 evs Hst) as HPn1.
  pose proof (leaves_unreachable_m_step _ _ _ _ mo rsp mo1 evs Hl Hst) as Hl1. cbv beta in Hl1.
  destruct (stepR_set_tid None mo rsp mo1 evs (conj HPn0 (conj Hst I))) as (-> & Hfd1 & Hfs1).
  clear HPnk Hl. cbn [app].
  destruct (dec_set_tid rsp) as [u|]; cbn [ITree.bind ITreeCfg.lpin ITree.tsafe fst snd] in HPn1, Hl1 |- *; [| exact I].
  unfold main_model in HPn1, Hl1 |- *.
  assert (Eif : negb (Z.of_nat (length (argv_Z (in_argv inp))) =? 2) = false) by (fold argv; rewrite E2; reflexivity).
  rewrite Eif in HPn1, Hl1 |- *.
  set (path := nth 1 (argv_Z (in_argv inp)) []) in *.
  change (read_all io raw_malloc raw_free rstage path) with (mbind (msys (NOpen (map (Z_to_bv 8) path)) dec_open) (ra_tail (CE__ := run_ceiling en) rstage path)) in HPn1, Hl1 |- *.
  cbn [Monad.mbind Monad.msys Monad.mret ITree.ebind ITree.enode ITree.bind ITree.tsafe fst snd] in HPn1, Hl1.
  cbn [Monad.mbind Monad.msys Monad.mret ITree.ebind ITree.enode ITree.bind ITreeCfg.lpin fst snd].
  destruct HPn1 as [HPn10 HPn1k].
  intros rsp2 mo2 evs2 Hst2.
  pose proof (HPn1k rsp2 mo2 evs2 Hst2) as HPn2.
  pose proof (leaves_unreachable_m_step _ _ _ _ mo1 rsp2 mo2 evs2 Hl1 Hst2) as Hl2. cbv beta in Hl2.
  clear HPn1k Hl1. cbn [app].
  assert (Hpath : zlength path < 2^32).
  { unfold path. destruct (nth_in_or_default 1 (argv_Z (in_argv inp)) []) as [Hin|E]; [exact (proj1 (Forall_forall _ _) Hargv _ Hin)| rewrite E; unfold zlength; cbn; lia]. }
  set (fs := m_fs mo) in *.
  destruct (dec_open rsp2) as [a|] eqn:Ed; cbn [ITree.bind ITreeCfg.lpin ITree.tsafe fst snd] in HPn2, Hl2 |- *; [| exact I].
  destruct (stepR_open None (map (Z_to_bv 8) path) mo1 rsp2 mo2 evs2 a (conj HPn10 (conj Hst2 I)) Ed) as (-> & Ha).
  cbn [app].
  (* [comment removed for export] *)
  set (b := match a with SVal _ => true | SErr _ => false end).
  set (X := Xcanon (Some b) argv fs).
  assert (Hpre : (fun (s : PState) (mo' : Model) (tr : list event) => s = ps_init (reservedZ segs) /\ tr = [] /\ m_fs mo' = fs /\ ps_so s = stdout_init
                                   /\ ra_pre (Some b) fs path a mo') (ps_init (reservedZ segs)) mo2 []).
  { split; [reflexivity|]. split; [reflexivity|]. destruct a as [e|v]; cbn [ra_pre] in *; cbv zeta.
    - destruct Ha as (-> & _). split; [exact Hfs1|]. split; [reflexivity|]. exists false. split; [intros b' E'; inversion E'; reflexivity| reflexivity].
    - destruct Ha as (Hv & Hr & Hop & _ & ->). rewrite Hfd1, Hfd, alloc_fd_std in Hv. apply Z_to_bv_3 in Hv; [|exact Hr]. subst v.
      rewrite m_fs_with_fds, m_fds_with_fds, Hfd1, Hfd. split; [exact Hfs1|]. split; [reflexivity|]. split; [reflexivity|].
      split; [rewrite Hfs1 in Hop; exact Hop|]. split; [intros b' E'; inversion E'; reflexivity| reflexivity]. }
  pose proof (mspecE_bind None X _ _ _ _ _
                (mspecE_bind None X _ _ _ _ _
                   (read_all_tail_E (CE__ := run_ceiling en) None (Some b) X rstage fs path [] Hpath a (ps_init (reservedZ segs)))
                   (fun ra => main_tail_E (CE__ := run_ceiling en) None (Some b) X fs [] argv ra E2))
                (fun code => exit_model_E None (Some b) fs argv code)
                (ps_init (reservedZ segs)) mo2 [] Hpre) as HW.
  apply (lpin_of_pinned _ mo2 [] (ct_events fs (ctrace_of argv fs b))).
  refine (pinned_of_twfE X _ mo2 [] _ (fun _ _ _ => True) _ HPn2 Hl2 (Xcanon_pin b argv fs)).
  apply twfE_ebind. eapply twfE_mono; [exact HW|]. intros p0 mo' tr' [].
Qed.

(* [comment removed for export] *)

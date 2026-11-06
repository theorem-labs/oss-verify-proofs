(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem ITree Nodes Decode Ceiling Image.
From OSSVerify.Proofs.openssl.ct.lib Require Import TopLevel Obligations.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad Stdio HexModel Target Driver Prog Canon ModelInv Unforced LB_Logic.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import ProgDetIface ProgDetLogic ProgDetNodes ProgDetMalloc ProgDetStdio ProgDetTarget ProgDetDriver ProgDet.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import LibProg LibSafe LibOps ProgG ProgGSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section TargetGE.
Context {CE__ : Ceiling}.
Context {LM : LibModel}.
Variable sel : option bool.
Variable X : list event -> Prop.
Hypothesis H_rc : forall ls d, lleaves (lib_one ls d) (fun r => snd r = 0).

Lemma run_callsG_E : forall Km d n ls j tr0, Km_ok Km -> (j + n <= 500)%nat ->
  mspecE sel X (SoA ps_so Km (so_after j) (tr0 ++ evw 1 (out_after j))) (run_callsG d n ls 0)
    (fun rc s mo tr => SoA ps_so Km (so_after (j + n)) (tr0 ++ evw 1 (out_after (j + n))) s mo tr /\ rc = 0).
Proof.
  intros Km d n. induction n as [|n IH]; intros ls j tr0 HKm Hj; cbn [run_callsG].
  - apply mspecE_ret. intros s mo tr H. rewrite Nat.add_0_r. auto.
  - eapply mspecE_bind with
      (Q1 := fun p s mo tr => SoA ps_so Km (so_after j) (tr0 ++ evw 1 (out_after j)) s mo tr /\ snd p = 0).
    { unfold lib_one_prog. apply (interp_E sel X _ (SoA_fstable Km _ _ HKm) (lib_one ls d) _ (H_rc ls d)). }
    intros p. apply mspecE_pure. intros Hp. rewrite Hp. change (pieces_emit_of (Zdecimal 0 ++ [10])) with pieces_emit_0.
    eapply mspecE_seq with (R := SoA ps_so Km (so_after (S j)) (tr0 ++ evw 1 (out_after (S j)))).
    + destruct j as [|j].
      * eapply mspecE_conseq; [apply (stdout_emit_first ps_so set_so_ps sel X (fun _ _ => eq_refl) Km tr0)| |].
        { intros s mo tr H. cbn [so_after out_after evw map] in H. rewrite app_nil_r in H. exact H. }
        intros a s mo tr H. exact H.
      * eapply mspecE_conseq; [apply (stdout_emit_next ps_so set_so_ps sel X (fun _ _ => eq_refl) Km (zeros_out j) (tr0 ++ evw 1 [48; 10]))| |].
        { rewrite zlength_zeros_out. unfold STDOUT_BUFSIZ. lia. }
        { intros s mo tr H. exact H. }
        intros a s mo tr H. cbv beta in H. rewrite zeros_out_app in H. exact H.
    + intros _. replace (j + S n)%nat with (S j + n)%nat by lia. apply IH; auto; lia.
Qed.

Theorem target_runG_E : forall Km cfg payload tr0, Km_ok Km -> zlength payload < 2^60 ->
  mspecE sel X (SoA ps_so Km stdout_init tr0) (runG cfg payload)
    (fun rc s mo tr => SoA ps_so Km (so_after (Z.to_nat (Z.land cfg 3 + 1))) (tr0 ++ evw 1 [48; 10]) s mo tr /\ rc = 0).
Proof.
  intros Km cfg payload tr0 HKm Hd. unfold runG, target_runG, lib_init_prog.
  pose proof (SoA_fstable Km stdout_init tr0 HKm) as HK0.
  eapply mspecE_bind with (Q1 := fun _ => SoA ps_so Km stdout_init tr0).
  { eapply mspecE_post; [apply (interp_E sel X _ HK0 lib_init (fun _ => True) (lleaves_true _))|].
    intros a s mo tr [H _]. exact H. }
  intros ls0. cbv zeta.
  eapply mspecE_bind with (Q1 := fun a s mo tr => SoA ps_so Km stdout_init tr0 s mo tr /\ a <> None).
  - destruct (zlength payload =? 0).
    + apply mspecE_ret. intros s mo tr H. split; [exact H| discriminate].
    + eapply mspecE_bind; [apply raw_malloc_E; [exact HK0| apply size_ok62; lia]|].
      intros r. apply mspecE_pure. intros Hr. destruct r as [p|]; [|contradiction Hr; reflexivity].
      apply mspecE_ret. intros s mo tr H. split; [exact H| discriminate].
  - intros [owned|]; [|apply mspecE_pure; intros []; reflexivity].
    apply mspecE_pure. intros _.
    destruct (calls_pos cfg) as [Hc1 Hc2]. destruct (Z.to_nat (Z.land cfg 3 + 1)) as [|n] eqn:En; [lia|].
    eapply mspecE_bind with (Q1 := fun rc s mo tr => SoA ps_so Km (so_after (S n)) (tr0 ++ evw 1 [48; 10]) s mo tr /\ rc = 0).
    + eapply mspecE_conseq; [apply (run_callsG_E Km payload (S n) ls0 0 tr0 HKm); lia| |].
      * intros s mo tr H. cbn [so_after out_after evw map]. rewrite app_nil_r. exact H.
      * intros rc s mo tr [H ->]. split; [exact H| reflexivity].
    + intros rc. apply mspecE_pure. intros ->.
      eapply mspecE_bind with (Q1 := fun _ => SoA ps_so Km (so_after (S n)) (tr0 ++ evw 1 [48; 10])).
      * destruct owned as [q|]; cbn [lib_free_optG]; [apply raw_free_E; apply SoA_fstable; exact HKm| apply mspecE_ret; auto].
      * intros u. apply mspecE_ret. intros s mo tr H. auto.
Qed.

End TargetGE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WholeG.
Context {CE__ : Ceiling}.
Context {LM : LibModel}.
Hypothesis H_rc : forall ls d, lleaves (lib_one ls d) (fun r => snd r = 0).
Variable sel : option bool.
Variable rstage : Z.
Variable fs : Fs.
Variable argv : list (list Z).
Hypothesis Hargv : Forall (fun a => zlength a < 2^32) argv.

Lemma prog_withG_E : forall (P0 : assnE PState),
  (forall s mo tr, P0 s mo tr -> m_fds mo = fds_std /\ m_fs mo = fs /\ ps_so s = stdout_init /\ tr = []) ->
  mspecE sel (Xcanon sel argv fs) P0 (prog_withG rstage argv) (fun _ _ _ _ => False).
Proof.
  intros P0 HP0. unfold prog_withG.
  eapply mspecE_seq with (R := fun s mo tr => m_fds mo = fds_std /\ m_fs mo = fs /\ ps_so s = stdout_init /\ tr = []).
  { eapply mspecE_pre; [apply startup_E|exact HP0]. intros s mo tr mo' (H1 & H2 & H3 & H4) E1 E2. repeat split; congruence. }
  intros _. eapply mspecE_bind.
  { apply (main_model_E_gen sel (Xcanon sel argv fs) rstage fs [] runG); [|exact Hargv].
    intros Km cfg payload tr1 HKm Hpl. apply target_runG_E; assumption. }
  intros code. apply exit_model_E.
Qed.

End WholeG.

Lemma progG_twfE : forall {CE__ : Ceiling} {LM : LibModel},
  (forall ls d, lleaves (lib_one ls d) (fun r => snd r = 0)) ->
  forall sel segs rstage argv mo,
  Forall (fun a => zlength a < 2^32) (argv_Z argv) -> m_fds mo = fds_std ->
  twfE sel (Xcanon sel (argv_Z argv) (m_fs mo)) (progG segs rstage argv) mo [] (fun _ _ _ => True).
Proof.
  intros CE LM H_rc sel segs rstage argv mo Hargv Hfd. unfold progG. apply twfE_ebind.
  eapply twfE_mono.
  - apply (prog_withG_E H_rc sel rstage (m_fs mo) (argv_Z argv) Hargv (fun s mo' tr => s = ps_init (reservedZ segs) /\ mo' = mo /\ tr = [])).
    + intros s mo' tr (-> & -> & ->). repeat split; auto.
    + auto.
  - intros p mo' tr' [].
Qed.

Lemma tsafe_noerr_no_enomem' : forall {R} (t : itree node R) mo,
  tsafe nstep node_noerr t mo -> tsafe nstep no_enomem t mo.
Proof.
  intros R t. induction t as [r|n k IH]; intros mo H; cbn in *; [exact I|].
  destruct H as [Hn Hk]. split; [destruct n; exact Hn|]. intros rsp mo' evs Hst. apply IH. exact (Hk rsp mo' evs Hst).
Qed.

(* [comment removed for export] *)
Definition the_progG {LM : LibModel} (segs : list Segment) (rstage : Z) : prog_tree (Exc.exc unit) :=
  fun inp en => @progG (run_ceiling en) LM segs rstage (in_argv inp).

Section DetG.
Context {LM : LibModel}.
Variable P : Z -> Z.
Variable T : list Z.
Variable ok : list (bptr * Z) -> Z -> Prop.          (* [comment removed for export] *)
Variable linv : LS -> list (bptr * Z) -> Prop.
Hypothesis HP0 : forall c, 0 <= P c.
Hypothesis HcT : capsT_ok P T.                         (* [comment removed for export] *)
Hypothesis HOK : ok_bridge P T ok.                    (* [comment removed for export] *)
Hypothesis H_init : lwf (okT T) lib_init [] (fun ls Li => linv ls [] /\ subms (map snd Li) T).
Hypothesis H_one : forall ls d X, linv ls X -> zlength d <= MAX_INPUT ->
  lwf ok (lib_one ls d) X (fun r X' => linv (fst r) X').
Hypothesis H_rc : forall ls d, lleaves (lib_one ls d) (fun r => snd r = 0).

(* [comment removed for export] *)
Theorem progG_model_ok_run : forall segs rstage pc ph lim,
  image_low segs -> KLIM + SMALLREQ <= lim ->
  forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
  leaves_unreachable_m nstep (the_progG segs rstage inp en) (mo0 segs lim en inp)
  /\ tsafe nstep nsafe (the_progG segs rstage inp en) (mo0 segs lim en inp).
Proof.
  intros segs rstage pc ph lim Hsegs Hlim en inp Hve Hvi. unfold the_progG.
  apply (progG_model_ok (CE__ := run_ceiling en) P T ok linv HP0 HcT HOK H_init H_one H_rc segs rstage pc ph lim en inp Hsegs Hlim Hve Hvi).
  exact (run_ceiling_eq segs pc ph en inp (vie_va_size _ Hvi) Hve).
Qed.

Theorem progG_det_gen : forall segs rstage pc ph lim,
  image_low segs -> KLIM + SMALLREQ <= lim ->
  forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
  forall tr, tree_traces (the_progG segs rstage inp en) (mo0 segs lim en inp) tr
             <-> canonT (argv_Z (in_argv inp)) (in_fs inp) tr.
Proof.
  intros segs rstage pc ph lim Hsegs Hlim en inp Hve Hvi tr.
  pose proof (run_ceiling_eq segs pc ph en inp (vie_va_size _ Hvi) Hve) as Hceil.
  pose proof (progG_model_ok (CE__ := run_ceiling en) P T ok linv HP0 HcT HOK H_init H_one H_rc
                segs rstage pc ph lim en inp Hsegs Hlim Hve Hvi Hceil) as [Hl Hs].
  pose proof (tsafe_noerr_no_enomem' _ _
                (progG_noerr_gen (CE__ := run_ceiling en) P T ok linv HP0 HcT HOK H_init H_one
                   segs rstage pc ph lim en inp Hsegs Hlim Hve Hvi Hceil)) as Hne'.
  unfold the_progG in *.
  set (t := @progG (run_ceiling en) LM segs rstage (in_argv inp)) in *.
  change (init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp) with (mo0 segs lim en inp) in Hne'.
  set (mo := mo0 segs lim en inp) in *.
  assert (HPn : tsafe nstep Pn t mo) by (apply tsafe_Pn; [exact Hs| exact Hne'| apply mo0_minv; exact Hvi| apply mo0_not_halted]).
  assert (Hargv : Forall (fun a => zlength a < 2^32) (argv_Z (in_argv inp))) by (apply argv_Z_short; exact (proj1 Hvi)).
  assert (Hfd : m_fds mo = fds_std) by (unfold mo, TopLevel.mo0; rewrite m_fds_init_model; reflexivity).
  assert (Hfs : m_fs mo = in_fs inp) by (unfold mo, TopLevel.mo0; rewrite m_fs_init_model; reflexivity).
  split.
  - intros (full & Hfull & Hp).
    apply ttrace_split in Hfull. destruct Hfull as [Hx|(r & mo' & Hpath)]; [|exfalso; exact (Hl _ _ _ Hpath)].
    pose proof (texit_nstep_stepR t mo full HPn Hx) as HxR.
    pose proof (twfE_texit None _ t mo [] _ full (progG_twfE (CE__ := run_ceiling en) H_rc None segs rstage (in_argv inp) mo Hargv Hfd) HxR) as (b & _ & E).
    cbn [app] in E. rewrite Hfs in E. apply canonT_iff. exists b. rewrite <- E. exact Hp.
  - intros Hc. apply canonT_iff in Hc. destruct Hc as (okb & Hp).
    pose proof (progG_twfE (CE__ := run_ceiling en) H_rc (Some okb) segs rstage (in_argv inp) mo Hargv Hfd) as Htw.
    destruct (twfE_exists (Some okb) _ t mo [] _ Htw HPn Hl) as (full & Hx).
    pose proof (twfE_texit (Some okb) _ t mo [] _ full Htw Hx) as (b & Hb & E).
    rewrite (Hb okb eq_refl) in E. cbn [app] in E. rewrite Hfs in E.
    exists full. split; [apply ttrace_split; left; exact (texit_stepR_nstep (Some okb) t mo full Hx)|]. rewrite E. exact Hp.
Qed.

(* [comment removed for export] *)
Corollary progG_trees_equiv : forall segsP rstageP pcP phP limP segsU rstageU pcU phU limU,
  image_low segsP -> KLIM + SMALLREQ <= limP -> image_low segsU -> KLIM + SMALLREQ <= limU ->
  forall (enP enU : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage segsP pcP phP) enP inp ->
    valid_entry (mkImage segsU pcU phU) enU inp ->
    valid_input_either inp ->
    trace_equiv (tree_traces (the_progG segsP rstageP inp enP) (mo0 segsP limP enP inp))
                (tree_traces (the_progG segsU rstageU inp enU) (mo0 segsU limU enU inp)).
Proof.
  intros segsP rstageP pcP phP limP segsU rstageU pcU phU limU HsP HlP HsU HlU enP enU inp HvP HvU Hvi tr.
  rewrite (progG_det_gen segsP rstageP pcP phP limP HsP HlP enP inp HvP Hvi tr).
  rewrite (progG_det_gen segsU rstageU pcU phU limU HsU HlU enU inp HvU Hvi tr). reflexivity.
Qed.

End DetG.

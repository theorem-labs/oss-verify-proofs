(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxGlue CxBatch.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HBPlanImage HBAtable HBArg HBCheckG HBChain HBHop HBBatch.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import DietTac.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Definition sub : Type := list (nat * expr).
Record a0d : Type := A0D { a0_F : list kentry; a0_plan : plan; a0_sig : sub; a0_Fx : list kentry }.
Record leafd : Type := LDX { ld_F : list kentry; ld_pA1 : plan; ld_sig : sub; ld_Fp : list kentry; ld_pC1 : plan; ld_rhos : list sub; ld_pC1x : list (nat * plan) }.
Definition LD (f : list kentry) (p : plan) (s : sub) (fp : list kentry) (c : plan) (r : list sub) : leafd := LDX f p s fp c r [].
Definition pC1_of (l : leafd) (c : nat) : plan :=
  match List.find (fun x => Nat.eqb (fst x) c) (ld_pC1x l) with Some x => snd x | None => ld_pC1 l end.
(* [comment removed for export] *)
Record fed : Type := FD { fd_phi : sub; fd_Fphi : list kentry; fd_pX : plan }.
Record holed : Type := HD { hd_c : nat; hd_tau : sub; hd_Fq : list kentry; hd_pC2 : plan; hd_fes : list (nat * fed) }.
Record opd : Type := OD { od_F : list kentry; od_pB : plan; od_holes : list (nat * holed) }.

Section Fam.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variables argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  #[local] Notation argH := (argH0 HAPH sp rdraw argv envp uid hw).
  #[local] Notation ISP := (bv_unsigned sp).
  #[local] Notation LIM := AsanInit.LIMIT.
  Variable SV : env -> (word -> option byte) -> Prop.
  Hypothesis SV_to1 : forall E M, SV E M -> HBArg.SINV1 sp brk0 argv envp rdraw hw uid E M.
  Hypothesis SV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SV E M -> SV E M'.
  Hypothesis SV_agree : forall E E' M, env_agree NX0 E E' -> SV E M -> SV E' M.
  Variable GC : bool.
  Variables BF FUEL : nat.
  Variable IT : itab.
  Hypothesis IT_ok : itab_sound HASEGS IT.

  #[local] Notation CSOK PHI := (cs_ok HASEGS HAT LIM (SVG PHI SV) argH ISP fs).
  #[local] Notation CHECK NX HS := (CAP.check HASEGS IT HAT NX LIM (hag_XN NX) (hag_XE NX) hag_XB HS 0 true false GC BF FUEL None).
  #[local] Notation HOP := (hop_sound sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit SV SV_to1 SV_frame SV_agree GC BF FUEL).
  #[local] Notation LEAF := (leaf_sound sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit SV SV_to1 SV_frame SV_agree GC BF FUEL).
  #[local] Notation SPECB := (spec_back sp rdraw argv envp uid hw fs SV).
  #[local] Notation ADDF := (add_facts sp rdraw argv envp uid hw fs SV).
  #[local] Notation CSPHI := (csok_phi sp rdraw argv envp uid hw fs SV).

  (* [comment removed for export] *)
  Variables N0 NA NB NC ND NE VSA VSB VSC VSD VSE : nat.
  Variables S0 TA1 TB : acs.
  Variables TCs TDs : list acs.
  Variables TFE TFEE : acs.
  Variable a0s : list a0d.
  Variable leaves : list leafd.
  Variable ops : list opd.
  Variable opdom : list kentry.
  Variable shapeB : shape.
  Variable sC2s : list shape.
  Variable sXs : list (list shape).
  Definition sC2 (j : nat) : shape := nth j sC2s SNil.
  Definition sX (j k : nat) : shape := nth k (nth j sXs []) SNil.
  Definition TCn (c : nat) : acs := nth c TCs S0.
  Definition TDn (c : nat) : acs := nth c TDs S0.

  (* [comment removed for export] *)
  Definition tgA0 (v : a0d) : list (nat * htgt) := [(0%nat, (TA1, a0_sig v, a0_Fx v))].
  Definition tgA1 (l : leafd) : list (nat * htgt) := [(0%nat, (TB, ld_sig l, ld_Fp l))].
  Definition tgB (o : opd) : list (nat * htgt) := map (fun p => (fst p, (TCn (hd_c (snd p)), hd_tau (snd p), hd_Fq (snd p)))) (od_holes o).
  Definition tgC1 (l : leafd) (c : nat) : list (nat * htgt) := [(0%nat, (TDn c, nth c (ld_rhos l) [], []))].
  Definition tgC2 (h : holed) : list (nat * htgt) := map (fun p => (fst p, (TFE, fd_phi (snd p), fd_Fphi (snd p)))) (hd_fes h).
  (* [comment removed for export] *)
  Definition stA0 (v : a0d) : acs := add_kn S0 (a0_F v).
  Definition stA1 (l : leafd) : acs := add_kn TA1 (ld_F l).
  Definition stB (o : opd) : acs := add_kn TB (od_F o).
  Definition stC1 (l : leafd) (c : nat) : acs := add_kn (inst_list (TCn c) (ld_sig l)) (ld_Fp l).
  Definition stC2 (h : holed) : acs := add_kn (inst_list (TDn (hd_c h)) (hd_tau h)) (hd_Fq h).
  Definition stX (f : fed) : acs := add_kn (inst_list TFEE (fd_phi f)) (fd_Fphi f).

  (* [comment removed for export] *)
  Definition mkA0 (v : a0d) : hjob := HJ N0 (tgA0 v) (stA0 v) (a0_plan v) (SHole 0).
  Definition mkA1 (l : leafd) : hjob := HJ NA (tgA1 l) (stA1 l) (ld_pA1 l) (SHole 0).
  Definition mkB (o : opd) : hjob := HJ NB (tgB o) (stB o) (od_pB o) shapeB.
  Definition mkC1 (lc : leafd * nat) : hjob := HJ NC (tgC1 (fst lc) (snd lc)) (stC1 (fst lc) (snd lc)) (pC1_of (fst lc) (snd lc)) (SHole 0).
  Definition mkC2 (jh : nat * holed) : hjob := HJ ND (tgC2 (snd jh)) (stC2 (snd jh)) (hd_pC2 (snd jh)) (sC2 (CAP.hole_cls (fst jh))).
  Definition mkX (x : nat * nat * fed) : hjob := HJ NE [] (stX (snd x)) (fd_pX (snd x)) (sX (CAP.hole_cls (fst (fst x))) (CAP.hole_cls (snd (fst x)))).
  Definition classes : list nat := seq 0 (length TCs).
  Definition xjobs_of (jh : nat * holed) : list (nat * nat * fed) := map (fun kf => (fst jh, fst kf, snd kf)) (hd_fes (snd jh)).
  Definition xjobs : list (nat * nat * fed) := flat_map xjobs_of (flat_map od_holes ops).
  Hypothesis JA0 : allok GC BF FUEL IT _ mkA0 a0s.
  Hypothesis JA1 : allok GC BF FUEL IT _ mkA1 leaves.
  Hypothesis JB : allok GC BF FUEL IT _ mkB ops.
  Hypothesis JC1 : allok GC BF FUEL IT _ mkC1 (list_prod leaves classes).
  Hypothesis JC2 : allok GC BF FUEL IT _ mkC2 (flat_map od_holes ops).
  Hypothesis JX : allok GC BF FUEL IT _ mkX xjobs.

  Lemma HA0 : forall v, In v a0s -> CHECK N0 (HS_tg (tgA0 v)) (stA0 v) (a0_plan v) = COk (SHole 0).
  Proof. intros v Hv. exact (JA0 v Hv). Qed.
  Lemma HA1 : forall l, In l leaves -> CHECK NA (HS_tg (tgA1 l)) (stA1 l) (ld_pA1 l) = COk (SHole 0).
  Proof. intros l Hl. exact (JA1 l Hl). Qed.
  Lemma HB : forall o, In o ops -> CHECK NB (HS_tg (tgB o)) (stB o) (od_pB o) = COk shapeB.
  Proof. intros o Ho. exact (JB o Ho). Qed.
  Lemma HC1 : forall l c, In l leaves -> (c < length TCs)%nat ->
    CHECK NC (HS_tg (tgC1 l c)) (stC1 l c) (pC1_of l c) = COk (SHole 0).
  Proof.
    intros l c Hl Hc. refine (JC1 (l, c) _). apply in_prod_iff. split; [exact Hl|]. unfold classes. apply in_seq. lia.
  Qed.
  Lemma HC2 : forall o j h, In o ops -> In (j, h) (od_holes o) -> CHECK ND (HS_tg (tgC2 h)) (stC2 h) (hd_pC2 h) = COk (sC2 (CAP.hole_cls j)).
  Proof. intros o j h Ho Hh. refine (JC2 (j, h) _). apply in_flat_map. exists o. split; assumption. Qed.
  Lemma HX : forall o j h k f, In o ops -> In (j, h) (od_holes o) -> In (k, f) (hd_fes h) ->
    CHECK NE (HS_tg []) (stX f) (fd_pX f) = COk (sX (CAP.hole_cls j) (CAP.hole_cls k)).
  Proof.
    intros o j h k f Ho Hh Hf. refine (JX (j, k, f) _). unfold xjobs. apply in_flat_map. exists (j, h). split.
    - apply in_flat_map. exists o. split; assumption.
    - unfold xjobs_of. cbn [fst snd]. apply in_map_iff. exists (k, f). split; [reflexivity | exact Hf].
  Qed.

  (* [comment removed for export] *)
  Definition nx_ok (n : nat) : bool := (Nat.leb NX0 n && CAP.expr_vars_lt n e_spw)%bool.
  Definition lvl_ok (s : sub) (F : list kentry) (n : nat) : bool := (sig_vars_lt n s && F_ok n F)%bool.
  Definition nolog (t : acs) : bool := match s_log (a_ss t) with [] => true | _ => false end.
  Definition side_lv : bool :=
    (nx_ok N0 && nx_ok NA && nx_ok NB && nx_ok NC && nx_ok ND && nx_ok NE
     && Nat.leb N0 VSA && Nat.leb NA VSB && Nat.leb NB VSC && Nat.leb NC VSD && Nat.leb ND VSE
     && Nat.leb N0 NA && Nat.leb NA NB && Nat.leb NB NC && Nat.leb NC ND && Nat.leb ND NE && Nat.leb NE (nxt TFE))%bool.
  Definition side_tm : bool := (nolog TA1 && nolog TB && forallb nolog TCs && forallb nolog TDs && nolog TFE && nolog TFEE)%bool.
  Definition side_sh : bool := (shape_vars_lt N0 shapeB && forallb (shape_vars_lt N0) sC2s && forallb (forallb (shape_vars_lt N0)) sXs)%bool.
  Definition side_a0 : bool :=
    forallb (fun v => ht_ok VSA (TA1, a0_sig v, a0_Fx v) && lvl_ok (a0_sig v) (a0_Fx v) NA && lvl_ok (a0_sig v) (a0_Fx v) NB
                      && lvl_ok (a0_sig v) (a0_Fx v) NC && lvl_ok (a0_sig v) (a0_Fx v) ND && lvl_ok (a0_sig v) (a0_Fx v) NE)%bool a0s.
  Definition side_lf : bool :=
    forallb (fun l => ht_ok VSB (TB, ld_sig l, ld_Fp l) && lvl_ok (ld_sig l) (ld_Fp l) NB && lvl_ok (ld_sig l) (ld_Fp l) NC && lvl_ok (ld_sig l) (ld_Fp l) ND
                      && lvl_ok (ld_sig l) (ld_Fp l) NE && forallb (fun r => sig_ok VSD r && sig_vars_lt ND r && sig_vars_lt NE r) (ld_rhos l))%bool leaves.
  Definition side_fe (p : nat * fed) : bool := (ht_ok VSE (TFE, fd_phi (snd p), fd_Fphi (snd p)) && lvl_ok (fd_phi (snd p)) (fd_Fphi (snd p)) NE)%bool.
  Definition side_hd (p : nat * holed) : bool :=
    (ht_ok VSC (TCn (hd_c (snd p)), hd_tau (snd p), hd_Fq (snd p))
     && lvl_ok (hd_tau (snd p)) (hd_Fq (snd p)) NC && lvl_ok (hd_tau (snd p)) (hd_Fq (snd p)) ND && lvl_ok (hd_tau (snd p)) (hd_Fq (snd p)) NE
     && Nat.ltb (hd_c (snd p)) (length TCs) && Nat.ltb (hd_c (snd p)) (length TDs) && forallb side_fe (hd_fes (snd p)))%bool.
  Definition side_op : bool :=
    forallb (fun o => F_ok NB (od_F o) && F_ok NC (od_F o) && F_ok ND (od_F o) && F_ok NE (od_F o) && forallb side_hd (od_holes o))%bool ops.
  Definition side_dom : bool := forallb (fun F => pure_fact F && existsb (kentry_eqb F) (kn TB))%bool opdom.
  Definition side_ok : bool := (side_lv && side_tm && side_sh && side_a0 && side_lf && side_op && side_dom)%bool.
  Hypothesis SIDE : side_ok = true.

  (* [comment removed for export] *)
  Hypothesis OPSEL : forall E, Forall (pure_holds E) opdom -> exists o, In o ops /\ Forall (pure_holds E) (od_F o).
  (* [comment removed for export] *)
  Hypothesis H_FE : fx_hole SV argH ISP fs TFE TFEE.

  Lemma S_lv : side_lv = true. Proof. pose proof SIDE as X. unfold side_ok in X. do 6 (apply andb_prop in X; destruct X as [X ?]). assumption. Qed.
  Lemma S_tm : side_tm = true. Proof. pose proof SIDE as X. unfold side_ok in X. do 6 (apply andb_prop in X; destruct X as [X ?]). assumption. Qed.
  Lemma S_sh : side_sh = true. Proof. pose proof SIDE as X. unfold side_ok in X. do 6 (apply andb_prop in X; destruct X as [X ?]). assumption. Qed.
  Lemma S_a0 : side_a0 = true. Proof. pose proof SIDE as X. unfold side_ok in X. do 6 (apply andb_prop in X; destruct X as [X ?]). assumption. Qed.
  Lemma S_lf : side_lf = true. Proof. pose proof SIDE as X. unfold side_ok in X. do 6 (apply andb_prop in X; destruct X as [X ?]). assumption. Qed.
  Lemma S_op : side_op = true. Proof. pose proof SIDE as X. unfold side_ok in X. do 6 (apply andb_prop in X; destruct X as [X ?]). assumption. Qed.
  Lemma S_dom : side_dom = true. Proof. pose proof SIDE as X. unfold side_ok in X. do 6 (apply andb_prop in X; destruct X as [X ?]). assumption. Qed.

  Lemma nx_of : forall n, nx_ok n = true -> (NX0 <= n)%nat /\ CAP.expr_vars_lt n e_spw = true.
  Proof. intros n H. unfold nx_ok in H. apply andb_prop in H as [A1 A2]. split; [apply Nat.leb_le; exact A1 | exact A2]. Qed.
  Lemma lvs : nx_ok N0 = true /\ nx_ok NA = true /\ nx_ok NB = true /\ nx_ok NC = true /\ nx_ok ND = true /\ nx_ok NE = true
              /\ (N0 <= VSA /\ NA <= VSB /\ NB <= VSC /\ NC <= VSD /\ ND <= VSE)%nat
              /\ (N0 <= NA /\ NA <= NB /\ NB <= NC /\ NC <= ND /\ ND <= NE /\ NE <= nxt TFE)%nat.
  Proof.
    pose proof S_lv as X. unfold side_lv in X. do 16 (apply andb_prop in X; destruct X as [X ?]).
    repeat match goal with H : Nat.leb _ _ = true |- _ => apply Nat.leb_le in H end. repeat split; assumption.
  Qed.
  Lemma nolog_nil : forall t, nolog t = true -> s_log (a_ss t) = [].
  Proof. intros t H. unfold nolog in H. destruct (s_log (a_ss t)); [reflexivity | discriminate]. Qed.
  Lemma tms : s_log (a_ss TA1) = [] /\ s_log (a_ss TB) = [] /\ forallb nolog TCs = true /\ forallb nolog TDs = true /\ s_log (a_ss TFE) = [] /\ s_log (a_ss TFEE) = [].
  Proof.
    pose proof S_tm as X. unfold side_tm in X. do 5 (apply andb_prop in X; destruct X as [X ?]).
    repeat split; try apply nolog_nil; assumption.
  Qed.

  (* [comment removed for export] *)
  Definition HOLES_X (j : nat) : nat -> env -> Fs.Fs -> TSet := fun k E fs0 => sd noHOLES t_nil E fs0 (sX (CAP.hole_cls j) (CAP.hole_cls k)).
  Definition HOLES_C : nat -> env -> Fs.Fs -> TSet := fun j E fs0 => sd (HOLES_X j) t_nil E fs0 (sC2 (CAP.hole_cls j)).
  Definition DEN : env -> Fs.Fs -> TSet := fun E fs0 => sd HOLES_C t_nil E fs0 shapeB.

  Lemma sX_vars : forall j k, shape_vars_lt N0 (sX j k) = true.
  Proof.
    pose proof S_sh as X. unfold side_sh in X. apply andb_prop in X as [_ X].
    intros j k. unfold sX. destruct (nth_in_or_default j sXs []) as [Hin | ->]; [|destruct k; reflexivity].
    pose proof (proj1 (forallb_forall _ _) X _ Hin) as Y.
    destruct (nth_in_or_default k (nth j sXs []) SNil) as [Hin2 | ->]; [|reflexivity].
    exact (proj1 (forallb_forall _ _) Y _ Hin2).
  Qed.
  Lemma sC2_vars : forall j, shape_vars_lt N0 (sC2 j) = true.
  Proof.
    pose proof S_sh as X. unfold side_sh in X. apply andb_prop in X as [X _]. apply andb_prop in X as [_ X].
    intros j. unfold sC2. destruct (nth_in_or_default j sC2s SNil) as [Hin | ->]; [|reflexivity].
    exact (proj1 (forallb_forall _ _) X _ Hin).
  Qed.
  Lemma HOLES_X_agree : forall j b, (N0 <= b)%nat -> forall k E E' fs0, env_agree b E E' -> HOLES_X j k E fs0 = HOLES_X j k E' fs0.
  Proof.
    intros j b Hb k E E' fs0 Hag. unfold HOLES_X.
    apply (sd_agree N0 noHOLES (noHOLES_agree2 N0) t_nil E E' fs0); [eapply env_agree_le; [exact Hag | exact Hb] | apply sX_vars].
  Qed.
  Lemma HOLES_X_mod : forall j k E fs0, HOLES_X j k E fs0 = HOLES_X j (CAP.hole_cls k) E fs0.
  Proof. intros j k E fs0. unfold HOLES_X. rewrite hole_cls_idem. reflexivity. Qed.
  Lemma HOLES_X_nil : forall j k E fs0, HOLES_X j k E fs0 [].
  Proof. intros j k E fs0. unfold HOLES_X. apply (sd_has_nil noHOLES noHOLES_nil2). reflexivity. Qed.
  Lemma HOLES_X_cls : forall j k E fs0, HOLES_X (CAP.hole_cls j) k E fs0 = HOLES_X j k E fs0.
  Proof. intros j k E fs0. unfold HOLES_X. rewrite hole_cls_idem. reflexivity. Qed.
  Lemma HOLES_C_agree : forall b, (N0 <= b)%nat -> forall h E E' fs0, env_agree b E E' -> HOLES_C h E fs0 = HOLES_C h E' fs0.
  Proof.
    intros b Hb h E E' fs0 Hag. unfold HOLES_C.
    apply (sd_agree N0 (HOLES_X h) (HOLES_X_agree h N0 (le_n _)) t_nil E E' fs0 (sC2 (CAP.hole_cls h))); [eapply env_agree_le; [exact Hag | exact Hb] | apply sC2_vars].
  Qed.
  Lemma HOLES_C_mod : forall h E fs0, HOLES_C h E fs0 = HOLES_C (CAP.hole_cls h) E fs0.
  Proof.
    intros h E fs0. unfold HOLES_C. rewrite hole_cls_idem.
    assert (EQ : HOLES_X (CAP.hole_cls h) = HOLES_X h).
    { apply FunctionalExtensionality.functional_extensionality. intros k. apply FunctionalExtensionality.functional_extensionality. intros E0.
      apply FunctionalExtensionality.functional_extensionality. intros f0. apply HOLES_X_cls. }
    rewrite EQ. reflexivity.
  Qed.
  Lemma HOLES_C_nil : forall h E fs0, HOLES_C h E fs0 [].
  Proof. intros h E fs0. unfold HOLES_C. apply (sd_has_nil (HOLES_X h) (HOLES_X_nil h)). reflexivity. Qed.
  Lemma DEN_agree : forall b, (N0 <= b)%nat -> forall E E' fs0, env_agree b E E' -> DEN E fs0 = DEN E' fs0.
  Proof.
    intros b Hb E E' fs0 Hag. unfold DEN.
    pose proof S_sh as X. unfold side_sh in X. apply andb_prop in X as [X _]. apply andb_prop in X as [X _].
    apply (sd_agree N0 HOLES_C (HOLES_C_agree N0 (le_n _)) t_nil E E' fs0 shapeB); [eapply env_agree_le; [exact Hag | exact Hb] | exact X].
  Qed.
  Lemma DEN_nil : forall E fs0, DEN E fs0 [].
  Proof. intros E fs0. unfold DEN. apply (sd_has_nil HOLES_C HOLES_C_nil). reflexivity. Qed.

  Lemma lvl_agree : forall PHI s F n b, (n <= b)%nat -> (forall E E', env_agree n E E' -> PHI E -> PHI E') -> lvl_ok s F b = true ->
    forall E E', env_agree b E E' -> PHI_ext PHI s F E -> PHI_ext PHI s F E'.
  Proof.
    intros PHI s F n b Hnb HP Hl0 E E' Hag. unfold lvl_ok in Hl0. apply andb_prop in Hl0 as [H1 H2].
    apply (PHI_ext_agree b PHI s F); [|exact H1|exact H2|exact Hag].
    intros E1 E2 Hag12. apply HP. eapply env_agree_le; [exact Hag12 | exact Hnb].
  Qed.
  (* [comment removed for export] *)
  Lemma know_pure_in : forall PHI E cs R FULL model F, CSOK PHI E cs R FULL model -> pure_fact F = true -> In F (kn cs) -> pure_holds E F.
  Proof.
    intros PHI E cs R FULL model F HC Hp Hin.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK. unfold know_ok in HK.
    pose proof (proj1 (Forall_forall _ _) HK F Hin) as H.
    destruct F; cbn [pure_fact] in Hp; try discriminate; cbn [kentry_ok] in H; cbn [pure_holds]; exact H.
  Qed.

  Section Chain.
    Variable v : a0d. Variable l : leafd.
    Hypothesis Hv : In v a0s. Hypothesis Hl : In l leaves.
    Variable PHI0 : env -> Prop.
    Hypothesis PHI0_agree : forall E E', env_agree N0 E E' -> PHI0 E -> PHI0 E'.
    Hypothesis PHI0_facts : forall E, PHI0 E -> Forall (pure_holds E) (a0_F v) /\ Forall (pure_holds E) (ld_F l).

    Definition PHI1 := PHI_ext PHI0 (a0_sig v) (a0_Fx v).
    Definition PHI2 := PHI_ext PHI1 (ld_sig l) (ld_Fp l).

    Lemma side_v : ht_ok VSA (TA1, a0_sig v, a0_Fx v) = true /\ lvl_ok (a0_sig v) (a0_Fx v) NA = true /\ lvl_ok (a0_sig v) (a0_Fx v) NB = true
                   /\ lvl_ok (a0_sig v) (a0_Fx v) NC = true /\ lvl_ok (a0_sig v) (a0_Fx v) ND = true /\ lvl_ok (a0_sig v) (a0_Fx v) NE = true.
    Proof.
      pose proof (proj1 (forallb_forall _ _) S_a0 v Hv) as Y. cbv beta in Y.
      do 5 (apply andb_prop in Y; destruct Y as [Y ?]). repeat split; assumption.
    Qed.
    Lemma side_l : ht_ok VSB (TB, ld_sig l, ld_Fp l) = true /\ lvl_ok (ld_sig l) (ld_Fp l) NB = true /\ lvl_ok (ld_sig l) (ld_Fp l) NC = true
                   /\ lvl_ok (ld_sig l) (ld_Fp l) ND = true /\ lvl_ok (ld_sig l) (ld_Fp l) NE = true
                   /\ forallb (fun r => sig_ok VSD r && sig_vars_lt ND r && sig_vars_lt NE r)%bool (ld_rhos l) = true.
    Proof.
      pose proof (proj1 (forallb_forall _ _) S_lf l Hl) as Y. cbv beta in Y.
      do 5 (apply andb_prop in Y; destruct Y as [Y ?]). repeat split; assumption.
    Qed.
    Lemma side_o : forall o, In o ops -> F_ok NB (od_F o) = true /\ F_ok NC (od_F o) = true /\ F_ok ND (od_F o) = true /\ F_ok NE (od_F o) = true
                                         /\ forallb side_hd (od_holes o) = true.
    Proof.
      intros o Ho. pose proof (proj1 (forallb_forall _ _) S_op o Ho) as Y. cbv beta in Y.
      do 4 (apply andb_prop in Y; destruct Y as [Y ?]). repeat split; assumption.
    Qed.
    Lemma side_h : forall o j h, In o ops -> In (j, h) (od_holes o) ->
      ht_ok VSC (TCn (hd_c h), hd_tau h, hd_Fq h) = true /\ lvl_ok (hd_tau h) (hd_Fq h) NC = true /\ lvl_ok (hd_tau h) (hd_Fq h) ND = true
      /\ lvl_ok (hd_tau h) (hd_Fq h) NE = true /\ (hd_c h < length TCs)%nat /\ (hd_c h < length TDs)%nat /\ forallb side_fe (hd_fes h) = true.
    Proof.
      intros o j h Ho Hh. destruct (side_o o Ho) as (_ & _ & _ & _ & Y).
      pose proof (proj1 (forallb_forall _ _) Y (j, h) Hh) as Z. unfold side_hd in Z. cbn [snd] in Z.
      do 6 (apply andb_prop in Z; destruct Z as [Z ?]). repeat split; try assumption; apply Nat.ltb_lt; assumption.
    Qed.

    (* [comment removed for export] *)
    Lemma X_thm : forall o j h k f, In o ops -> In (j, h) (od_holes o) -> In (k, f) (hd_fes h) ->
      forall (PHI : env -> Prop), (forall E E', env_agree NE E E' -> PHI E -> PHI E') ->
      forall E R FULL model, CSOK PHI E (stX f) R FULL model -> crz HASEGS (cfg_of HASEGS R (pc (stX f)) FULL model) (HOLES_X j k E (m_fs model)).
    Proof.
      intros o j h k f Ho Hh Hf PHI PA E R FULL model HC.
      destruct lvs as (_ & _ & _ & _ & _ & HNE & _). destruct (nx_of NE HNE) as [NE1 NE2].
      exact (LEAF NE NE1 NE2 PHI PA IT IT_ok (stX f) (fd_pX f) (sX (CAP.hole_cls j) (CAP.hole_cls k)) (HX o j h k f Ho Hh Hf) E R FULL model HC).
    Qed.

    (* [comment removed for export] *)
    Lemma C2_thm : forall o j h, In o ops -> In (j, h) (od_holes o) -> forall (PHI : env -> Prop),
      (forall E E', env_agree ND E E' -> PHI E -> PHI E') -> (forall E E', env_agree NE E E' -> PHI E -> PHI E') ->
      forall E R FULL model, CSOK PHI E (stC2 h) R FULL model -> crz HASEGS (cfg_of HASEGS R (pc (stC2 h)) FULL model) (HOLES_C j E (m_fs model)).
    Proof.
      intros o j h Ho Hh PHI PAD PAE E R FULL model HC.
      destruct lvs as (_ & _ & _ & _ & HND & HNE & (_ & _ & _ & _ & HDE) & (L0A & LAB & LBC & LCD & LDE & LET)).
      destruct (nx_of ND HND) as [ND1 ND2]. destruct tms as (_ & _ & _ & _ & TFElog & TFEElog).
      destruct (side_h o j h Ho Hh) as (_ & _ & _ & _ & _ & _ & Hfes).
      assert (HOK : forallb (fun p => ht_ok VSE (snd p)) (tgC2 h) = true).
      { unfold tgC2. apply forallb_forall. intros [k t] Hin. apply in_map_iff in Hin as [[k' f'] [Heq Hin]]. cbn [fst snd] in Heq. injection Heq as <- <-.
        cbn [snd]. pose proof (proj1 (forallb_forall _ _) Hfes (k', f') Hin) as Y. unfold side_fe in Y. cbn [snd] in Y. apply andb_prop in Y as [Y _]. exact Y. }
      refine (HOP ND VSE ND1 ND2 HDE PHI PAD (tgC2 h) HOK
                (HOLES_X j) (HOLES_X_agree j ND ltac:(lia)) (HOLES_X_nil j) (HOLES_X_mod j) _
                IT IT_ok (stC2 h) (hd_pC2 h) (sC2 (CAP.hole_cls j)) (HC2 o j h Ho Hh) E R FULL model HC).
      intros k t Ht E1 R1 FULL1 model1 HC1'.
      assert (Hex : exists f, In (k, f) (hd_fes h) /\ t = (TFE, fd_phi f, fd_Fphi f)).
      { unfold tgC2 in Ht. clear - Ht. induction (hd_fes h) as [|[k' f'] r IH]; cbn [map assoc fst snd] in Ht; [discriminate|].
        destruct (Nat.eqb_spec k' k) as [->|Hne]; [diet_injection Ht; exists f'; split; [left; reflexivity | reflexivity]|].
        destruct (IH Ht) as [f [Hin Heq]]. exists f. split; [right; exact Hin | exact Heq]. }
      destruct Hex as [f [Hf ->]]. unfold ht_T, ht_s, ht_F in *. cbn [fst snd] in *.
      pose proof (proj1 (forallb_forall _ _) Hfes (k, f) Hf) as Y. unfold side_fe in Y. cbn [snd] in Y. apply andb_prop in Y as [_ HlvE].
      set (PHIX := PHI_ext PHI (fd_phi f) (fd_Fphi f)) in *.
      assert (PAX : forall Ea Eb, env_agree NE Ea Eb -> PHIX Ea -> PHIX Eb) by (apply (lvl_agree PHI _ _ NE NE (le_n _)); [exact PAE | exact HlvE]).
      pose proof (fx_hole_phi sp rdraw argv envp uid hw fs SV NE PHIX PAX TFE TFEE LET H_FE) as HFX.
      apply (HFX E1 R1 FULL1 model1 (HOLES_X j k E1 (m_fs model1)) HC1').
      intros E2 R2 FULL2 model2 Hag HC2' Hfs.
      pose proof (SPECB PHIX (fd_phi f) (fd_Fphi f) TFEE E2 R2 FULL2 model2
                    ltac:(intros E0 (_ & Hs0 & Hf0); split; assumption) TFEElog HC2') as HC3.
      pose proof (X_thm o j h k f Ho Hh Hf PHIX PAX E2 R2 FULL2 model2 HC3) as HR.
      unfold stX in HR. change (pc (add_kn (inst_list TFEE (fd_phi f)) (fd_Fphi f))) with (pc (inst_list TFEE (fd_phi f))) in HR.
      rewrite pc_inst_list in HR. rewrite Hfs in HR.
      rewrite (HOLES_X_agree j (nxt TFE) ltac:(lia) k E1 E2 (m_fs model1) Hag). exact HR.
    Qed.

    (* [comment removed for export] *)
    Lemma C1_thm : forall o j h, In o ops -> In (j, h) (od_holes o) -> forall (PHI : env -> Prop),
      (forall b, In b [NC; ND; NE] -> forall E E', env_agree b E E' -> PHI E -> PHI E') ->
      (forall E, PHI E -> sig_holds E (hd_tau h) /\ Forall (pure_holds E) (hd_Fq h)) ->
      forall E R FULL model, CSOK PHI E (stC1 l (hd_c h)) R FULL model ->
        crz HASEGS (cfg_of HASEGS R (pc (stC1 l (hd_c h))) FULL model) (HOLES_C j E (m_fs model)).
    Proof.
      intros o j h Ho Hh PHI PA Ptau E R FULL model HC.
      destruct lvs as (_ & _ & _ & HNC & _ & _ & (_ & _ & _ & HCD & _) & (L0A & LAB & LBC & LCD & LDE & LET)).
      destruct (nx_of NC HNC) as [NC1 NC2]. destruct tms as (_ & _ & _ & TDsl & _ & _).
      destruct side_l as (_ & _ & _ & _ & _ & Hrho). destruct (side_h o j h Ho Hh) as (_ & _ & HlvD & HlvE & HcC & HcD & _).
      assert (TDlog : s_log (a_ss (TDn (hd_c h))) = []) by (apply nolog_nil; exact (proj1 (forallb_forall _ _) TDsl (TDn (hd_c h)) (nth_In TDs S0 HcD))).
      set (rho := nth (hd_c h) (ld_rhos l) []).
      assert (Hrho1 : sig_ok VSD rho = true /\ sig_vars_lt ND rho = true /\ sig_vars_lt NE rho = true).
      { unfold rho. destruct (nth_in_or_default (hd_c h) (ld_rhos l) []) as [Hin | ->]; [|repeat split; reflexivity].
        pose proof (proj1 (forallb_forall _ _) Hrho _ Hin) as Y. cbv beta in Y. apply andb_prop in Y as [Y Y3]. apply andb_prop in Y as [Y1 Y2]. repeat split; assumption. }
      assert (HOK : forallb (fun p => ht_ok VSD (snd p)) (tgC1 l (hd_c h)) = true).
      { unfold tgC1. cbn [forallb snd]. unfold ht_ok, ht_T, ht_s, ht_F. cbn [fst snd]. rewrite TDlog. change (nth (hd_c h) (ld_rhos l) []) with rho. rewrite (proj1 Hrho1). reflexivity. }
      refine (HOP NC VSD NC1 NC2 HCD PHI (PA NC ltac:(left; reflexivity)) (tgC1 l (hd_c h)) HOK
                (fun _ => HOLES_C j) (fun _ => HOLES_C_agree NC ltac:(lia) j) (fun _ => HOLES_C_nil j) (fun _ _ _ => eq_refl) _
                IT IT_ok (stC1 l (hd_c h)) (pC1_of l (hd_c h)) (SHole 0) (HC1 l (hd_c h) Hl HcC) E R FULL model HC).
      intros h0 t Ht E1 R1 FULL1 model1 HC1'. unfold tgC1 in Ht. cbn [assoc] in Ht.
      destruct (Nat.eqb 0 h0); [|discriminate]. diet_injection Ht. unfold ht_T, ht_s, ht_F in *. cbn [fst snd] in *.
      change (nth (hd_c h) (ld_rhos l) []) with rho in HC1'.
      assert (PA4 : forall Ea Eb, env_agree ND Ea Eb -> PHI_ext PHI rho [] Ea -> PHI_ext PHI rho [] Eb).
      { apply (lvl_agree PHI rho [] ND ND (le_n _)); [exact (PA ND ltac:(right; left; reflexivity))|]. unfold lvl_ok. rewrite (proj1 (proj2 Hrho1)). reflexivity. }
      assert (PA5 : forall Ea Eb, env_agree NE Ea Eb -> PHI_ext PHI rho [] Ea -> PHI_ext PHI rho [] Eb).
      { apply (lvl_agree PHI rho [] NE NE (le_n _)); [exact (PA NE ltac:(right; right; left; reflexivity))|]. unfold lvl_ok. rewrite (proj2 (proj2 Hrho1)). reflexivity. }
      pose proof (SPECB (PHI_ext PHI rho []) (hd_tau h) (hd_Fq h) (TDn (hd_c h)) E1 R1 FULL1 model1
                    ltac:(intros E0 [HP0 _]; exact (Ptau E0 HP0)) TDlog HC1') as HC2'.
      pose proof (C2_thm o j h Ho Hh (PHI_ext PHI rho []) PA4 PA5 E1 R1 FULL1 model1 HC2') as HR.
      unfold stC2 in HR. change (pc (add_kn (inst_list (TDn (hd_c h)) (hd_tau h)) (hd_Fq h))) with (pc (inst_list (TDn (hd_c h)) (hd_tau h))) in HR.
      rewrite pc_inst_list in HR. exact HR.
    Qed.

    (* [comment removed for export] *)
    Lemma B_thm : forall o, In o ops -> forall (PHI : env -> Prop),
      (forall b, In b [NB; NC; ND; NE] -> forall E E', env_agree b E E' -> PHI E -> PHI E') ->
      (forall E, PHI E -> sig_holds E (ld_sig l) /\ Forall (pure_holds E) (ld_Fp l)) ->
      forall E R FULL model, CSOK PHI E (stB o) R FULL model -> crz HASEGS (cfg_of HASEGS R (pc (stB o)) FULL model) (DEN E (m_fs model)).
    Proof.
      intros o Ho PHI PA Psig E R FULL model HC.
      destruct lvs as (_ & _ & HNB & _ & _ & _ & (_ & _ & HBC & _ & _) & (L0A & LAB & LBC & LCD & LDE & LET)).
      destruct (nx_of NB HNB) as [NB1 NB2]. destruct tms as (_ & _ & TCsl & _ & _ & _).
      assert (HOK : forallb (fun p => ht_ok VSC (snd p)) (tgB o) = true).
      { unfold tgB. apply forallb_forall. intros [j t] Hin. apply in_map_iff in Hin as [[j' h] [Heq Hin]]. cbn [fst snd] in Heq. injection Heq as <- <-.
        cbn [snd]. exact (proj1 (side_h o j' h Ho Hin)). }
      refine (HOP NB VSC NB1 NB2 HBC PHI (PA NB ltac:(left; reflexivity)) (tgB o) HOK
                HOLES_C (HOLES_C_agree NB ltac:(lia)) HOLES_C_nil HOLES_C_mod _
                IT IT_ok (stB o) (od_pB o) shapeB (HB o Ho) E R FULL model HC).
      intros j t Ht E1 R1 FULL1 model1 HC1'.
      assert (Hex : exists h, In (j, h) (od_holes o) /\ t = (TCn (hd_c h), hd_tau h, hd_Fq h)).
      { unfold tgB in Ht. clear - Ht. induction (od_holes o) as [|[j' h'] r IH]; cbn [map assoc fst snd] in Ht; [discriminate|].
        destruct (Nat.eqb_spec j' j) as [->|Hne]; [diet_injection Ht; exists h'; split; [left; reflexivity | reflexivity]|].
        destruct (IH Ht) as [h [Hin Heq]]. exists h. split; [right; exact Hin | exact Heq]. }
      destruct Hex as [h [Hh ->]]. unfold ht_T, ht_s, ht_F in *. cbn [fst snd] in *.
      destruct (side_h o j h Ho Hh) as (_ & HhC & HhD & HhE & HcC & _ & _).
      assert (TClog : s_log (a_ss (TCn (hd_c h))) = []) by (apply nolog_nil; exact (proj1 (forallb_forall _ _) TCsl (TCn (hd_c h)) (nth_In TCs S0 HcC))).
      set (PHI3 := PHI_ext PHI (hd_tau h) (hd_Fq h)) in *.
      assert (PA3 : forall b, In b [NC; ND; NE] -> forall Ea Eb, env_agree b Ea Eb -> PHI3 Ea -> PHI3 Eb).
      { intros b Hb. apply (lvl_agree PHI _ _ b b (le_n _)).
        - apply PA. cbn [In] in *. tauto.
        - cbn [In] in Hb. destruct Hb as [<-|[<-|[<-|[]]]]; assumption. }
      pose proof (SPECB PHI3 (ld_sig l) (ld_Fp l) (TCn (hd_c h)) E1 R1 FULL1 model1
                    ltac:(intros E0 [HP0 _]; exact (Psig E0 HP0)) TClog HC1') as HC1''.
      pose proof (C1_thm o j h Ho Hh PHI3 PA3 ltac:(intros E0 (_ & Ht0 & Hf0); split; assumption) E1 R1 FULL1 model1 HC1'') as HR.
      unfold stC1 in HR. change (pc (add_kn (inst_list (TCn (hd_c h)) (ld_sig l)) (ld_Fp l))) with (pc (inst_list (TCn (hd_c h)) (ld_sig l))) in HR.
      rewrite pc_inst_list in HR. exact HR.
    Qed.

    (* [comment removed for export] *)
    Lemma A1_thm : forall E R FULL model, CSOK PHI1 E (stA1 l) R FULL model -> crz HASEGS (cfg_of HASEGS R (pc (stA1 l)) FULL model) (DEN E (m_fs model)).
    Proof.
      intros E R FULL model HC.
      destruct lvs as (_ & HNA & _ & _ & _ & _ & (_ & HAB & _ & _ & _) & (L0A & LAB & LBC & LCD & LDE & LET)).
      destruct (nx_of NA HNA) as [NA1 NA2].
      destruct side_v as (_ & HvA & HvB & HvC & HvD & HvE). destruct side_l as (HlOK & HlB & HlC & HlD & HlE & _).
      assert (PA1 : forall b, In b [NA; NB; NC; ND; NE] -> forall Ea Eb, env_agree b Ea Eb -> PHI1 Ea -> PHI1 Eb).
      { intros b Hb. apply (lvl_agree PHI0 _ _ N0 b); [cbn [In] in Hb; lia | exact PHI0_agree |].
        cbn [In] in Hb. destruct Hb as [<-|[<-|[<-|[<-|[<-|[]]]]]]; assumption. }
      assert (HOK : forallb (fun p => ht_ok VSB (snd p)) (tgA1 l) = true) by (unfold tgA1; cbn [forallb snd]; rewrite HlOK; reflexivity).
      refine (HOP NA VSB NA1 NA2 HAB PHI1 (PA1 NA ltac:(left; reflexivity)) (tgA1 l) HOK
                (fun _ => DEN) (fun _ => DEN_agree NA ltac:(lia)) (fun _ => DEN_nil) (fun _ _ _ => eq_refl) _
                IT IT_ok (stA1 l) (ld_pA1 l) (SHole 0) (HA1 l Hl) E R FULL model HC).
      intros h0 t Ht E1 R1 FULL1 model1 HC1'. unfold tgA1 in Ht. cbn [assoc] in Ht.
      destruct (Nat.eqb 0 h0); [|discriminate]. diet_injection Ht. unfold ht_T, ht_s, ht_F in *. cbn [fst snd] in *.
      change (PHI_ext PHI1 (ld_sig l) (ld_Fp l)) with PHI2 in HC1'.
      (* [comment removed for export] *)
      assert (Hdom : Forall (pure_holds E1) opdom).
      { apply Forall_forall. intros F HF. pose proof (proj1 (forallb_forall _ _) S_dom F HF) as Y. cbv beta in Y. apply andb_prop in Y as [Y1 Y2].
        apply existsb_exists in Y2 as [F' [Hin Heq]]. apply c_kentry_eqb_eq in Heq. subst F'.
        exact (know_pure_in PHI2 E1 TB R1 FULL1 model1 F HC1' Y1 Hin). }
      destruct (OPSEL E1 Hdom) as [o [Ho HFo]].
      destruct (side_o o Ho) as (FoB & FoC & FoD & FoE & _).
      set (PHI2o := fun E0 : env => PHI2 E0 /\ Forall (pure_holds E0) (od_F o)).
      assert (PA2 : forall b, In b [NB; NC; ND; NE] -> forall Ea Eb, env_agree b Ea Eb -> PHI2o Ea -> PHI2o Eb).
      { intros b Hb Ea Eb Hag [H1 H2]. split.
        - revert H1. apply (lvl_agree PHI1 _ _ b b (le_n _)); [apply PA1; cbn [In] in *; tauto | | exact Hag].
          cbn [In] in Hb. destruct Hb as [<-|[<-|[<-|[<-|[]]]]]; assumption.
        - apply (pure_agree b (od_F o) Ea Eb Hag); [|exact H2]. cbn [In] in Hb. destruct Hb as [<-|[<-|[<-|[<-|[]]]]]; assumption. }
      pose proof (CSPHI PHI2 PHI2o E1 TB R1 FULL1 model1 ltac:(intros HP; split; [exact HP | exact HFo]) HC1') as HC1o.
      pose proof (ADDF PHI2o (od_F o) TB E1 R1 FULL1 model1 ltac:(intros E0 [_ HF0]; exact HF0) HC1o) as HC2'.
      pose proof (B_thm o Ho PHI2o PA2 ltac:(intros E0 [(_ & Hs0 & Hf0) _]; split; assumption) E1 R1 FULL1 model1 HC2') as HR.
      unfold stB in HR. change (pc (add_kn TB (od_F o))) with (pc TB) in HR. exact HR.
    Qed.

    (* [comment removed for export] *)
    Theorem fam_sound : forall E R FULL model, CSOK PHI0 E (stA0 v) R FULL model -> crz HASEGS (cfg_of HASEGS R (pc S0) FULL model) (DEN E (m_fs model)).
    Proof.
      intros E R FULL model HC.
      destruct lvs as (HN0 & _ & _ & _ & _ & _ & (H0A & _ & _ & _ & _) & _).
      destruct (nx_of N0 HN0) as [N01 N02]. destruct side_v as (HvOK & HvA & _).
      assert (HOK : forallb (fun p => ht_ok VSA (snd p)) (tgA0 v) = true) by (unfold tgA0; cbn [forallb snd]; rewrite HvOK; reflexivity).
      change (pc S0) with (pc (stA0 v)).
      refine (HOP N0 VSA N01 N02 H0A PHI0 PHI0_agree (tgA0 v) HOK
                (fun _ => DEN) (fun _ => DEN_agree N0 (le_n _)) (fun _ => DEN_nil) (fun _ _ _ => eq_refl) _
                IT IT_ok (stA0 v) (a0_plan v) (SHole 0) (HA0 v Hv) E R FULL model HC).
      intros h0 t Ht E1 R1 FULL1 model1 HC1'. unfold tgA0 in Ht. cbn [assoc] in Ht.
      destruct (Nat.eqb 0 h0); [|discriminate]. diet_injection Ht. unfold ht_T, ht_s, ht_F in *. cbn [fst snd] in *.
      change (PHI_ext PHI0 (a0_sig v) (a0_Fx v)) with PHI1 in HC1'.
      pose proof (ADDF PHI1 (ld_F l) TA1 E1 R1 FULL1 model1
                    ltac:(intros E0 (HP0 & _); exact (proj2 (PHI0_facts E0 HP0))) HC1') as HC2'.
      pose proof (A1_thm E1 R1 FULL1 model1 HC2') as HR.
      unfold stA1 in HR. change (pc (add_kn TA1 (ld_F l))) with (pc TA1) in HR. exact HR.
    Qed.
  End Chain.
End Fam.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxGlue.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxBatch HUPlanImage HUAtable H0Sinv HUCheckG HUChain HUChain2 HUHop HUBatch.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Definition sub : Type := list (nat * expr).
Record a0d : Type := A0D { a0_F : list kentry; a0_plan : plan; a0_sig : sub; a0_Fx : list kentry }.
(* [comment removed for export] *)
Record leafd : Type := LDX { ld_F : list kentry; ld_pA1 : plan; ld_sig : sub; ld_Fp : list kentry; ld_pC1 : plan; ld_rhos : list sub; ld_pC1x : list (nat * plan) }.
Definition LD (f : list kentry) (p : plan) (s : sub) (fp : list kentry) (c : plan) (r : list sub) : leafd := LDX f p s fp c r [].
Definition pC1_of (l : leafd) (c : nat) : plan :=
  match List.find (fun x => Nat.eqb (fst x) c) (ld_pC1x l) with Some x => snd x | None => ld_pC1 l end.
Record holed : Type := HD { hd_c : nat; hd_tau : sub; hd_Fq : list kentry; hd_pC2 : plan }.
Record opd : Type := OD { od_F : list kentry; od_pB : plan; od_holes : list (nat * holed) }.

Section Fam.
  Variable sp : word.
  Variable STR0 : Z.
  Variable LIM : Z.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hstr : bv_unsigned sp + 192 <= STR0 < 2 ^ 47 - 32.
  Hypothesis Hstr8 : STR0 mod 8 = 0.
  Variables BF FUEL : nat.
  Variable rs : list (Z * nat).

  #[local] Notation CSOK PHI := (cs_ok HSEGS H0T LIM (SINVg PHI sp STR0) (argHt STR0) (bv_unsigned sp) fs).
  #[local] Notation CHECK NX HS := (CAP.check HSEGS (APC.mk_itab_ranges HSEGS rs) H0T NX LIM (g0_XN NX LIM) (g0_XE NX) g0_XB HS 0 true false false BF FUEL None).

  (* [comment removed for export] *)
  Variables N0 NA NB NC ND VSA VSB VSC VSD : nat.
  Variables S0 TA1 TB : acs.
  Variables TCs TDs : list acs.
  Variable a0s : list a0d.
  Variable leaves : list leafd.
  Variable ops : list opd.
  Variable shapeB : shape.
  Variable sC2s : list shape.
  Definition sC2 (j : nat) : shape := nth j sC2s SNil.
  Definition TCn (c : nat) : acs := nth c TCs S0.
  Definition TDn (c : nat) : acs := nth c TDs S0.

  (* [comment removed for export] *)
  Definition tgA0 (v : a0d) : list (nat * htgt) := [(0%nat, (TA1, a0_sig v, a0_Fx v))].
  Definition tgA1 (l : leafd) : list (nat * htgt) := [(0%nat, (TB, ld_sig l, ld_Fp l))].
  Definition tgB (o : opd) : list (nat * htgt) := map (fun p => (fst p, (TCn (hd_c (snd p)), hd_tau (snd p), hd_Fq (snd p)))) (od_holes o).
  Definition tgC1 (l : leafd) (c : nat) : list (nat * htgt) := [(0%nat, (TDn c, nth c (ld_rhos l) [], []))].
  (* [comment removed for export] *)
  Definition stA0 (v : a0d) : acs := add_kn S0 (a0_F v).
  Definition stA1 (l : leafd) : acs := add_kn TA1 (ld_F l).
  Definition stB (o : opd) : acs := add_kn TB (od_F o).
  Definition stC1 (l : leafd) (c : nat) : acs := add_kn (inst_list (TCn c) (ld_sig l)) (ld_Fp l).
  Definition stC2 (h : holed) : acs := add_kn (inst_list (TDn (hd_c h)) (hd_tau h)) (hd_Fq h).

  (* [comment removed for export] *)
  Definition mkA0 (v : a0d) : hjob := HJ N0 (tgA0 v) (stA0 v) (a0_plan v) (SHole 0).
  Definition mkA1 (l : leafd) : hjob := HJ NA (tgA1 l) (stA1 l) (ld_pA1 l) (SHole 0).
  Definition mkB (o : opd) : hjob := HJ NB (tgB o) (stB o) (od_pB o) shapeB.
  Definition mkC1 (lc : leafd * nat) : hjob := HJ NC (tgC1 (fst lc) (snd lc)) (stC1 (fst lc) (snd lc)) (pC1_of (fst lc) (snd lc)) (SHole 0).
  Definition mkC2 (jh : nat * holed) : hjob := HJ ND [] (stC2 (snd jh)) (hd_pC2 (snd jh)) (sC2 (CAP.hole_cls (fst jh))).   (* [comment removed for export] *)
  Definition classes : list nat := seq 0 (length TCs).
  Hypothesis JA0 : allok LIM BF FUEL rs _ mkA0 a0s.
  Hypothesis JA1 : allok LIM BF FUEL rs _ mkA1 leaves.
  Hypothesis JB : allok LIM BF FUEL rs _ mkB ops.
  Hypothesis JC1 : allok LIM BF FUEL rs _ mkC1 (list_prod leaves classes).
  Hypothesis JC2 : allok LIM BF FUEL rs _ mkC2 (flat_map od_holes ops).

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
  Lemma HC2 : forall o j h, In o ops -> In (j, h) (od_holes o) -> CHECK ND noHS (stC2 h) (hd_pC2 h) = COk (sC2 (CAP.hole_cls j)).
  Proof. intros o j h Ho Hh. refine (JC2 (j, h) _). apply in_flat_map. exists o. split; assumption. Qed.

  (* [comment removed for export] *)
  Definition nx_ok (n : nat) : bool := (Nat.leb NX0t n && CAP.expr_vars_lt n e_spw)%bool.
  Definition lvl_ok (s : sub) (F : list kentry) (n : nat) : bool := (sig_vars_lt n s && F_ok n F)%bool.
  Definition nolog (t : acs) : bool := match s_log (a_ss t) with [] => true | _ => false end.
  Definition nodup_keys (o : opd) : bool := true.
  Definition side_ok : bool :=
    (nx_ok N0 && nx_ok NA && nx_ok NB && nx_ok NC && nx_ok ND
     && Nat.leb N0 VSA && Nat.leb NA VSB && Nat.leb NB VSC && Nat.leb NC VSD
     && Nat.leb N0 NA && Nat.leb NA NB && Nat.leb NB NC && Nat.leb NC ND
     && nolog TA1 && nolog TB && forallb nolog TCs && forallb nolog TDs
     && shape_vars_lt N0 shapeB && forallb (shape_vars_lt N0) sC2s
     && forallb (fun v => ht_ok VSA (TA1, a0_sig v, a0_Fx v) && lvl_ok (a0_sig v) (a0_Fx v) NA && lvl_ok (a0_sig v) (a0_Fx v) NB
                          && lvl_ok (a0_sig v) (a0_Fx v) NC && lvl_ok (a0_sig v) (a0_Fx v) ND) a0s
     && forallb (fun l => ht_ok VSB (TB, ld_sig l, ld_Fp l) && lvl_ok (ld_sig l) (ld_Fp l) NB && lvl_ok (ld_sig l) (ld_Fp l) NC && lvl_ok (ld_sig l) (ld_Fp l) ND
                          && forallb (fun r => sig_ok VSD r && sig_vars_lt ND r) (ld_rhos l)) leaves
     && forallb (fun o => forallb (fun p => ht_ok VSC (TCn (hd_c (snd p)), hd_tau (snd p), hd_Fq (snd p))
                                            && lvl_ok (hd_tau (snd p)) (hd_Fq (snd p)) NC && lvl_ok (hd_tau (snd p)) (hd_Fq (snd p)) ND
                                            && Nat.ltb (hd_c (snd p)) (length TCs) && Nat.ltb (hd_c (snd p)) (length TDs)) (od_holes o)) ops)%bool.
  Hypothesis SIDE : side_ok = true.

  (* [comment removed for export] *)
  Definition HOLES_C : nat -> env -> Fs.Fs -> TSet := fun j E fs0 => sd noHOLES t_nil E fs0 (sC2 (CAP.hole_cls j)).   (* [comment removed for export] *)
  Definition DEN : env -> Fs.Fs -> TSet := fun E fs0 => sd HOLES_C t_nil E fs0 shapeB.

  Ltac side H := let X := fresh in pose proof SIDE as X; unfold side_ok in X; repeat (apply andb_prop in X; destruct X as [X ?]); try exact H.

  Lemma sC2_vars : forall j, shape_vars_lt N0 (sC2 j) = true.
  Proof.
    pose proof SIDE as X. unfold side_ok in X. do 21 (apply andb_prop in X; destruct X as [X ?]).
    intros j. unfold sC2. destruct (nth_in_or_default j sC2s SNil) as [Hin | ->]; [|reflexivity].
    match goal with H : forallb (shape_vars_lt N0) sC2s = true |- _ => exact (proj1 (forallb_forall _ _) H _ Hin) end.
  Qed.
  Lemma HOLES_C_agree : forall b, (N0 <= b)%nat -> forall h E E' fs0, env_agree b E E' -> HOLES_C h E fs0 = HOLES_C h E' fs0.
  Proof.
    intros b Hb h E E' fs0 Hag. unfold HOLES_C.
    apply (sd_agree N0 noHOLES (noHOLES_agree2 N0) t_nil E E' fs0 (sC2 (CAP.hole_cls h))); [eapply env_agree_le; [exact Hag | exact Hb] | apply sC2_vars].
  Qed.
  Lemma HOLES_C_mod : forall h E fs0, HOLES_C h E fs0 = HOLES_C (CAP.hole_cls h) E fs0.
  Proof. intros h E fs0. unfold HOLES_C. rewrite hole_cls_idem. reflexivity. Qed.
  Lemma HOLES_C_nil : forall h E fs0, HOLES_C h E fs0 [].
  Proof. intros h E fs0. unfold HOLES_C. apply (sd_has_nil noHOLES noHOLES_nil2). reflexivity. Qed.
  Lemma DEN_agree : forall b, (N0 <= b)%nat -> forall E E' fs0, env_agree b E E' -> DEN E fs0 = DEN E' fs0.
  Proof.
    intros b Hb E E' fs0 Hag. unfold DEN.
    pose proof SIDE as X. unfold side_ok in X. do 21 (apply andb_prop in X; destruct X as [X ?]).
    apply (sd_agree N0 HOLES_C (HOLES_C_agree N0 (le_n _)) t_nil E E' fs0 shapeB); [eapply env_agree_le; [exact Hag | exact Hb] | assumption].
  Qed.
  Lemma DEN_nil : forall E fs0, DEN E fs0 [].
  Proof. intros E fs0. unfold DEN. apply (sd_has_nil HOLES_C HOLES_C_nil). reflexivity. Qed.

  Section Chain.
    Variable v : a0d. Variable l : leafd. Variable o : opd.
    Hypothesis Hv : In v a0s. Hypothesis Hl : In l leaves. Hypothesis Ho : In o ops.
    Variable PHI0 : env -> Prop.
    Hypothesis PHI0_agree : forall E E', env_agree N0 E E' -> PHI0 E -> PHI0 E'.
    Hypothesis PHI0_facts : forall E, PHI0 E -> Forall (pure_holds E) (a0_F v) /\ Forall (pure_holds E) (ld_F l) /\ Forall (pure_holds E) (od_F o).

    Definition PHI1 := PHI_ext PHI0 (a0_sig v) (a0_Fx v).
    Definition PHI2 := PHI_ext PHI1 (ld_sig l) (ld_Fp l).

    Lemma side_v : ht_ok VSA (TA1, a0_sig v, a0_Fx v) = true /\ lvl_ok (a0_sig v) (a0_Fx v) NA = true /\ lvl_ok (a0_sig v) (a0_Fx v) NB = true
                   /\ lvl_ok (a0_sig v) (a0_Fx v) NC = true /\ lvl_ok (a0_sig v) (a0_Fx v) ND = true.
    Proof.
      pose proof SIDE as X. unfold side_ok in X. do 21 (apply andb_prop in X; destruct X as [X ?]).
      match goal with H : forallb _ a0s = true |- _ => pose proof (proj1 (forallb_forall _ _) H v Hv) as Y end.
      do 4 (apply andb_prop in Y; destruct Y as [Y ?]). repeat split; assumption.
    Qed.
    Lemma side_l : ht_ok VSB (TB, ld_sig l, ld_Fp l) = true /\ lvl_ok (ld_sig l) (ld_Fp l) NB = true /\ lvl_ok (ld_sig l) (ld_Fp l) NC = true
                   /\ lvl_ok (ld_sig l) (ld_Fp l) ND = true /\ forallb (fun r => sig_ok VSD r && sig_vars_lt ND r)%bool (ld_rhos l) = true.
    Proof.
      pose proof SIDE as X. unfold side_ok in X. do 21 (apply andb_prop in X; destruct X as [X ?]).
      match goal with H : forallb _ leaves = true |- _ => pose proof (proj1 (forallb_forall _ _) H l Hl) as Y end.
      do 4 (apply andb_prop in Y; destruct Y as [Y ?]). repeat split; assumption.
    Qed.
    Lemma side_h : forall j h, In (j, h) (od_holes o) ->
      ht_ok VSC (TCn (hd_c h), hd_tau h, hd_Fq h) = true /\ lvl_ok (hd_tau h) (hd_Fq h) NC = true /\ lvl_ok (hd_tau h) (hd_Fq h) ND = true
      /\ (hd_c h < length TCs)%nat /\ (hd_c h < length TDs)%nat.
    Proof.
      intros j h Hh. pose proof SIDE as X. unfold side_ok in X. do 21 (apply andb_prop in X; destruct X as [X ?]).
      match goal with H : forallb _ ops = true |- _ => pose proof (proj1 (forallb_forall _ _) H o Ho) as Y end.
      pose proof (proj1 (forallb_forall _ _) Y (j, h) Hh) as Z. cbn [snd] in Z.
      do 4 (apply andb_prop in Z; destruct Z as [Z ?]). repeat split; try assumption; apply Nat.ltb_lt; assumption.
    Qed.
    Lemma lvl_agree : forall PHI s F n b, (n <= b)%nat -> (forall E E', env_agree n E E' -> PHI E -> PHI E') -> lvl_ok s F b = true ->
      forall E E', env_agree b E E' -> PHI_ext PHI s F E -> PHI_ext PHI s F E'.
    Proof.
      intros PHI s F n b Hnb HP Hl0 E E' Hag. unfold lvl_ok in Hl0. apply andb_prop in Hl0 as [H1 H2].
      apply (PHI_ext_agree b PHI s F); [|exact H1|exact H2|exact Hag].
      intros E1 E2 Hag12. apply HP. eapply env_agree_le; [exact Hag12 | exact Hnb].
    Qed.
    Lemma nxs : (N0 <= NA /\ NA <= NB /\ NB <= NC /\ NC <= ND)%nat.
    Proof.
      pose proof SIDE as X. unfold side_ok in X. do 21 (apply andb_prop in X; destruct X as [X ?]).
      repeat split; apply Nat.leb_le; assumption.
    Qed.
    Lemma PHI1_agree : forall b, (NA <= b)%nat -> lvl_ok (a0_sig v) (a0_Fx v) b = true -> forall E E', env_agree b E E' -> PHI1 E -> PHI1 E'.
    Proof. intros b Hb Hlv. apply (lvl_agree PHI0 _ _ N0 b); [pose proof nxs; lia | exact PHI0_agree | exact Hlv]. Qed.
    Lemma PHI2_agree : forall b, (NB <= b)%nat -> lvl_ok (a0_sig v) (a0_Fx v) b = true -> lvl_ok (ld_sig l) (ld_Fp l) b = true ->
      forall E E', env_agree b E E' -> PHI2 E -> PHI2 E'.
    Proof.
      intros b Hb Hv1 Hl1. apply (lvl_agree PHI1 _ _ b b (le_n _)); [|exact Hl1].
      apply PHI1_agree; [pose proof nxs; lia | exact Hv1].
    Qed.

    (* [comment removed for export] *)
    Lemma C2_thm : forall j h, In (j, h) (od_holes o) -> forall (PHI : env -> Prop), (forall E E', env_agree ND E E' -> PHI E -> PHI E') ->
      forall E R FULL model, CSOK PHI E (stC2 h) R FULL model -> crz HSEGS (cfg_of HSEGS R (pc (stC2 h)) FULL model) (HOLES_C j E (m_fs model)).
    Proof.
      intros j h Hh PHI PA E R FULL model HC.
      pose proof SIDE as X. unfold side_ok in X. do 21 (apply andb_prop in X; destruct X as [X ?]).
      assert (ND_ok : (NX0t <= ND)%nat /\ CAP.expr_vars_lt ND e_spw = true).
      { match goal with H : nx_ok ND = true |- _ => unfold nx_ok in H; apply andb_prop in H as [A1 A2]; split; [apply Nat.leb_le; exact A1 | exact A2] end. }
      exact (leaf_sound sp STR0 LIM fs Hsp Hstr Hstr8 BF FUEL ND (proj1 ND_ok) (proj2 ND_ok) PHI PA rs (stC2 h) (hd_pC2 h) (sC2 (CAP.hole_cls j)) (HC2 o j h Ho Hh) E R FULL model HC).
    Qed.

    (* [comment removed for export] *)
    Lemma C1_thm : forall j h, In (j, h) (od_holes o) -> forall (PHI : env -> Prop), (forall E E', env_agree NC E E' -> PHI E -> PHI E') ->
      (forall E, PHI E -> sig_holds E (hd_tau h) /\ Forall (pure_holds E) (hd_Fq h)) ->
      forall E R FULL model, CSOK PHI E (stC1 l (hd_c h)) R FULL model ->
        crz HSEGS (cfg_of HSEGS R (pc (stC1 l (hd_c h))) FULL model) (HOLES_C j E (m_fs model)).
    Proof.
      intros j h Hh PHI PA Ptau E R FULL model HC.
      pose proof SIDE as X. unfold side_ok in X. do 21 (apply andb_prop in X; destruct X as [X ?]).
      destruct side_l as (_ & _ & _ & _ & Hrho). destruct (side_h j h Hh) as (_ & _ & HlvD & HcC & HcD).
      assert (NC_ok : (NX0t <= NC)%nat /\ CAP.expr_vars_lt NC e_spw = true).
      { match goal with H : nx_ok NC = true |- _ => unfold nx_ok in H; apply andb_prop in H as [A1 A2]; split; [apply Nat.leb_le; exact A1 | exact A2] end. }
      assert (NCD : (NC <= VSD)%nat) by (apply Nat.leb_le; assumption).
      assert (TDlog : s_log (a_ss (TDn (hd_c h))) = []).
      { match goal with H : forallb nolog TDs = true |- _ => pose proof (proj1 (forallb_forall _ _) H (TDn (hd_c h)) (nth_In TDs S0 HcD)) as L end.
        unfold nolog in L. destruct (s_log (a_ss (TDn (hd_c h)))); [reflexivity | discriminate]. }
      set (rho := nth (hd_c h) (ld_rhos l) []).
      assert (Hrho1 : sig_ok VSD rho = true /\ sig_vars_lt ND rho = true).
      { unfold rho. destruct (nth_in_or_default (hd_c h) (ld_rhos l) []) as [Hin | ->]; [|split; reflexivity].
        pose proof (proj1 (forallb_forall _ _) Hrho _ Hin) as Y. apply andb_prop in Y. exact Y. }
      assert (HOK : forallb (fun p => ht_ok VSD (snd p)) (tgC1 l (hd_c h)) = true).
      { unfold tgC1. cbn [forallb snd]. unfold ht_ok, ht_T, ht_s, ht_F. cbn [fst snd]. rewrite TDlog. change (nth (hd_c h) (ld_rhos l) []) with rho. rewrite (proj1 Hrho1). reflexivity. }
      refine (hop_sound sp STR0 LIM fs Hsp Hstr Hstr8 BF FUEL NC VSD (proj1 NC_ok) (proj2 NC_ok) NCD PHI PA (tgC1 l (hd_c h)) HOK
                (fun _ => HOLES_C j) (fun _ => HOLES_C_agree NC ltac:(pose proof nxs; lia) j) (fun _ => HOLES_C_nil j) (fun _ _ _ => eq_refl) _
                rs (stC1 l (hd_c h)) (pC1_of l (hd_c h)) (SHole 0) (HC1 l (hd_c h) Hl HcC) E R FULL model HC).
      intros h0 t Ht E1 R1 FULL1 model1 HC1'. unfold tgC1 in Ht. cbn [assoc] in Ht.
      destruct (Nat.eqb 0 h0); [|discriminate]. injection Ht as <-. unfold ht_T, ht_s, ht_F in *. cbn [fst snd] in *.
      (* [comment removed for export] *)
      assert (PA4 : forall Ea Eb, env_agree ND Ea Eb -> PHI_ext PHI rho [] Ea -> PHI_ext PHI rho [] Eb).
      { apply (lvl_agree PHI rho [] NC ND); [pose proof nxs; lia | exact PA |]. unfold lvl_ok. rewrite (proj2 Hrho1). reflexivity. }
      pose proof (spec_back sp STR0 LIM fs (PHI_ext PHI rho []) (hd_tau h) (hd_Fq h) (TDn (hd_c h)) E1 R1 FULL1 model1
                    ltac:(intros E0 [HP0 _]; exact (Ptau E0 HP0)) TDlog HC1') as HC2'.
      pose proof (C2_thm j h Hh (PHI_ext PHI rho []) PA4 E1 R1 FULL1 model1 HC2') as HR.
      unfold stC2 in HR. change (pc (add_kn (inst_list (TDn (hd_c h)) (hd_tau h)) (hd_Fq h))) with (pc (inst_list (TDn (hd_c h)) (hd_tau h))) in HR.
      rewrite pc_inst_list in HR. exact HR.
    Qed.

    (* [comment removed for export] *)
    Lemma B_thm : forall (PHI : env -> Prop), (forall b, (NB <= b)%nat -> lvl_ok (a0_sig v) (a0_Fx v) b = true -> lvl_ok (ld_sig l) (ld_Fp l) b = true ->
                                                 forall E E', env_agree b E E' -> PHI E -> PHI E') ->
      (forall E, PHI E -> sig_holds E (ld_sig l) /\ Forall (pure_holds E) (ld_Fp l)) ->
      forall E R FULL model, CSOK PHI E (stB o) R FULL model -> crz HSEGS (cfg_of HSEGS R (pc (stB o)) FULL model) (DEN E (m_fs model)).
    Proof.
      intros PHI PA Psig E R FULL model HC.
      pose proof SIDE as X. unfold side_ok in X. do 21 (apply andb_prop in X; destruct X as [X ?]).
      destruct side_v as (_ & _ & HvB & HvC & HvD). destruct side_l as (_ & HlB & HlC & HlD & _).
      assert (NB_ok : (NX0t <= NB)%nat /\ CAP.expr_vars_lt NB e_spw = true).
      { match goal with H : nx_ok NB = true |- _ => unfold nx_ok in H; apply andb_prop in H as [A1 A2]; split; [apply Nat.leb_le; exact A1 | exact A2] end. }
      assert (NBC : (NB <= VSC)%nat) by (apply Nat.leb_le; assumption).
      assert (HOK : forallb (fun p => ht_ok VSC (snd p)) (tgB o) = true).
      { unfold tgB. apply forallb_forall. intros [j t] Hin. apply in_map_iff in Hin as [[j' h] [Heq Hin]]. cbn [fst snd] in Heq. injection Heq as <- <-.
        cbn [snd]. exact (proj1 (side_h j' h Hin)). }
      refine (hop_sound sp STR0 LIM fs Hsp Hstr Hstr8 BF FUEL NB VSC (proj1 NB_ok) (proj2 NB_ok) NBC PHI (PA NB (le_n _) HvB HlB) (tgB o) HOK
                HOLES_C (HOLES_C_agree NB ltac:(pose proof nxs; lia)) HOLES_C_nil HOLES_C_mod _
                rs (stB o) (od_pB o) shapeB (HB o Ho) E R FULL model HC).
      intros j t Ht E1 R1 FULL1 model1 HC1'.
      assert (Hex : exists h, In (j, h) (od_holes o) /\ t = (TCn (hd_c h), hd_tau h, hd_Fq h)).
      { unfold tgB in Ht. clear - Ht. induction (od_holes o) as [|[j' h'] r IH]; cbn [map assoc fst snd] in Ht; [discriminate|].
        destruct (Nat.eqb_spec j' j) as [->|Hne]; [injection Ht as <-; exists h'; split; [left; reflexivity | reflexivity]|].
        destruct (IH Ht) as [h [Hin Heq]]. exists h. split; [right; exact Hin | exact Heq]. }
      destruct Hex as [h [Hh ->]]. unfold ht_T, ht_s, ht_F in *. cbn [fst snd] in *.
      destruct (side_h j h Hh) as (_ & HhC & HhD & HcC & _).
      assert (TClog : s_log (a_ss (TCn (hd_c h))) = []).
      { match goal with H : forallb nolog TCs = true |- _ => pose proof (proj1 (forallb_forall _ _) H (TCn (hd_c h)) (nth_In TCs S0 HcC)) as L end.
        unfold nolog in L. destruct (s_log (a_ss (TCn (hd_c h)))); [reflexivity | discriminate]. }
      set (PHI3 := PHI_ext PHI (hd_tau h) (hd_Fq h)) in *.
      assert (PA3 : forall Ea Eb, env_agree NC Ea Eb -> PHI3 Ea -> PHI3 Eb).
      { apply (lvl_agree PHI _ _ NC NC (le_n _)); [|exact HhC]. apply PA; [pose proof nxs; lia | exact HvC | exact HlC]. }
      pose proof (spec_back sp STR0 LIM fs PHI3 (ld_sig l) (ld_Fp l) (TCn (hd_c h)) E1 R1 FULL1 model1
                    ltac:(intros E0 [HP0 _]; exact (Psig E0 HP0)) TClog HC1') as HC1''.
      pose proof (C1_thm j h Hh PHI3 PA3 ltac:(intros E0 (_ & Ht0 & Hf0); split; assumption) E1 R1 FULL1 model1 HC1'') as HR.
      unfold stC1 in HR. change (pc (add_kn (inst_list (TCn (hd_c h)) (ld_sig l)) (ld_Fp l))) with (pc (inst_list (TCn (hd_c h)) (ld_sig l))) in HR.
      rewrite pc_inst_list in HR. exact HR.
    Qed.

    (* [comment removed for export] *)
    Lemma A1_thm : forall E R FULL model, CSOK PHI1 E (stA1 l) R FULL model -> crz HSEGS (cfg_of HSEGS R (pc (stA1 l)) FULL model) (DEN E (m_fs model)).
    Proof.
      intros E R FULL model HC.
      pose proof SIDE as X. unfold side_ok in X. do 21 (apply andb_prop in X; destruct X as [X ?]).
      destruct side_v as (_ & HvA & HvB & HvC & HvD). destruct side_l as (HlOK & HlB & HlC & HlD & _).
      assert (NA_ok : (NX0t <= NA)%nat /\ CAP.expr_vars_lt NA e_spw = true).
      { match goal with H : nx_ok NA = true |- _ => unfold nx_ok in H; apply andb_prop in H as [A1 A2]; split; [apply Nat.leb_le; exact A1 | exact A2] end. }
      assert (NAB : (NA <= VSB)%nat) by (apply Nat.leb_le; assumption).
      assert (HOK : forallb (fun p => ht_ok VSB (snd p)) (tgA1 l) = true) by (unfold tgA1; cbn [forallb snd]; rewrite HlOK; reflexivity).
      refine (hop_sound sp STR0 LIM fs Hsp Hstr Hstr8 BF FUEL NA VSB (proj1 NA_ok) (proj2 NA_ok) NAB PHI1 (PHI1_agree NA (le_n _) HvA) (tgA1 l) HOK
                (fun _ => DEN) (fun _ => DEN_agree NA ltac:(pose proof nxs; lia)) (fun _ => DEN_nil) (fun _ _ _ => eq_refl) _
                rs (stA1 l) (ld_pA1 l) (SHole 0) (HA1 l Hl) E R FULL model HC).
      intros h0 t Ht E1 R1 FULL1 model1 HC1'. unfold tgA1 in Ht. cbn [assoc] in Ht.
      destruct (Nat.eqb 0 h0); [|discriminate]. injection Ht as <-. unfold ht_T, ht_s, ht_F in *. cbn [fst snd] in *.
      change (PHI_ext PHI1 (ld_sig l) (ld_Fp l)) with PHI2 in HC1'.
      pose proof (add_facts sp STR0 LIM fs PHI2 (od_F o) TB E1 R1 FULL1 model1
                    ltac:(intros E0 ((HP0 & _) & _); exact (proj2 (proj2 (PHI0_facts E0 HP0)))) HC1') as HC2'.
      pose proof (B_thm PHI2 PHI2_agree ltac:(intros E0 (_ & Hs0 & Hf0); split; assumption) E1 R1 FULL1 model1 HC2') as HR.
      unfold stB in HR. change (pc (add_kn TB (od_F o))) with (pc TB) in HR. exact HR.
    Qed.

    (* [comment removed for export] *)
    Theorem fam_sound : forall E R FULL model, CSOK PHI0 E (stA0 v) R FULL model -> crz HSEGS (cfg_of HSEGS R (pc S0) FULL model) (DEN E (m_fs model)).
    Proof.
      intros E R FULL model HC.
      pose proof SIDE as X. unfold side_ok in X. do 21 (apply andb_prop in X; destruct X as [X ?]).
      destruct side_v as (HvOK & HvA & _).
      assert (N0_ok : (NX0t <= N0)%nat /\ CAP.expr_vars_lt N0 e_spw = true).
      { match goal with H : nx_ok N0 = true |- _ => unfold nx_ok in H; apply andb_prop in H as [A1 A2]; split; [apply Nat.leb_le; exact A1 | exact A2] end. }
      assert (N0A : (N0 <= VSA)%nat) by (apply Nat.leb_le; assumption).
      assert (HOK : forallb (fun p => ht_ok VSA (snd p)) (tgA0 v) = true) by (unfold tgA0; cbn [forallb snd]; rewrite HvOK; reflexivity).
      change (pc S0) with (pc (stA0 v)).
      refine (hop_sound sp STR0 LIM fs Hsp Hstr Hstr8 BF FUEL N0 VSA (proj1 N0_ok) (proj2 N0_ok) N0A PHI0 PHI0_agree (tgA0 v) HOK
                (fun _ => DEN) (fun _ => DEN_agree N0 (le_n _)) (fun _ => DEN_nil) (fun _ _ _ => eq_refl) _
                rs (stA0 v) (a0_plan v) (SHole 0) (HA0 v Hv) E R FULL model HC).
      intros h0 t Ht E1 R1 FULL1 model1 HC1'. unfold tgA0 in Ht. cbn [assoc] in Ht.
      destruct (Nat.eqb 0 h0); [|discriminate]. injection Ht as <-. unfold ht_T, ht_s, ht_F in *. cbn [fst snd] in *.
      change (PHI_ext PHI0 (a0_sig v) (a0_Fx v)) with PHI1 in HC1'.
      pose proof (add_facts sp STR0 LIM fs PHI1 (ld_F l) TA1 E1 R1 FULL1 model1
                    ltac:(intros E0 (HP0 & _); exact (proj1 (proj2 (PHI0_facts E0 HP0)))) HC1') as HC2'.
      pose proof (A1_thm E1 R1 FULL1 model1 HC2') as HR.
      unfold stA1 in HR. change (pc (add_kn TA1 (ld_F l))) with (pc TA1) in HR. exact HR.
    Qed.
  End Chain.
End Fam.

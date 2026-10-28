(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxGlue.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HUPlanImage HUAtable H0Sinv HUCheckG HUChain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Section Chain2.
  Variable sp : word.
  Variable STR0 : Z.
  Variable LIM : Z.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hstr : bv_unsigned sp + 192 <= STR0 < 2 ^ 47 - 32.
  Hypothesis Hstr8 : STR0 mod 8 = 0.
  Variables BF FUEL : nat.

  #[local] Notation CSOK PHI := (cs_ok HSEGS H0T LIM (SINVg PHI sp STR0) (argHt STR0) (bv_unsigned sp) fs).
  #[local] Notation CHECK NX HS rs := (CAP.check HSEGS (APC.mk_itab_ranges HSEGS rs) H0T NX LIM (g0_XN NX LIM) (g0_XE NX) g0_XB HS 0 true false false BF FUEL None).

  (* [comment removed for export] *)
  Definition HOLES_B2 (Cs : list (nat * ccert)) : nat -> env -> Fs.Fs -> TSet :=
    fun h E fs0 => match assoc (CAP.hole_cls h) Cs with Some c => sd noHOLES t_nil E fs0 (cc_shape c) | None => t_nil end.
  Lemma HOLES_B2_mod : forall Cs h E fs0, HOLES_B2 Cs h E fs0 = HOLES_B2 Cs (CAP.hole_cls h) E fs0.
  Proof. intros Cs h E fs0. unfold HOLES_B2. rewrite hole_cls_idem. reflexivity. Qed.

  Lemma noHOLES_agree2 : forall b h E E' fs0, env_agree b E E' -> noHOLES h E fs0 = noHOLES h E' fs0.
  Proof. reflexivity. Qed.
  Lemma noHOLES_nil2 : forall h E fs0, noHOLES h E fs0 [].
  Proof. reflexivity. Qed.

  Definition Cs_vars_lt2 (b : nat) (Cs : list (nat * ccert)) : bool := forallb (fun p => shape_vars_lt b (cc_shape (snd p))) Cs.
  Lemma assoc_in2 : forall X h (l : list (nat * X)) x, assoc h l = Some x -> In (h, x) l.
  Proof.
    intros X h l x. induction l as [|[k y] r IH]; cbn [assoc]; [discriminate|].
    destruct (Nat.eqb_spec k h); [intros [= ->]; subst; left; reflexivity | intros H; right; exact (IH H)].
  Qed.
  Lemma HOLES_B2_agree : forall b Cs, Cs_vars_lt2 b Cs = true -> forall h E E' fs0, env_agree b E E' -> HOLES_B2 Cs h E fs0 = HOLES_B2 Cs h E' fs0.
  Proof.
    intros b Cs Hv h E E' fs0 Hag. unfold HOLES_B2. destruct (assoc (CAP.hole_cls h) Cs) as [c|] eqn:Hc; [|reflexivity].
    apply (sd_agree b noHOLES (noHOLES_agree2 b) t_nil E E' fs0 (cc_shape c) Hag).
    exact (proj1 (forallb_forall _ _) Hv (CAP.hole_cls h, c) (assoc_in2 _ _ _ _ Hc)).
  Qed.
  Lemma HOLES_B2_nil : forall Cs h E fs0, HOLES_B2 Cs h E fs0 [].
  Proof. intros Cs h E fs0. unfold HOLES_B2. destruct (assoc (CAP.hole_cls h) Cs); [apply (sd_has_nil noHOLES noHOLES_nil2); reflexivity | reflexivity]. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable NB : nat.
  Hypothesis NB_ge : (NX0t <= NB)%nat.
  Hypothesis NB_spw : CAP.expr_vars_lt NB e_spw = true.
  Variable TB : acs.                       (* [comment removed for export] *)
  Hypothesis TB_log : s_log (a_ss TB) = [].
  Variable holesB : list (nat * acs).      (* [comment removed for export] *)
  Hypothesis holesB_log : forall h ch, assoc h holesB = Some ch -> s_log (a_ss ch) = [].
  Hypothesis holesB_small : keys_small holesB = true.     (* [comment removed for export] *)
  Variable rsB : list (Z * nat).
  Variable planB : plan.
  Variable shapeB : shape.
  Hypothesis checkB : CHECK NB (fun h => assoc h holesB) rsB TB planB = COk shapeB.

  (* [comment removed for export] *)
  Definition C_ok2 (sigma : list (nat * expr)) (F : list kentry) (Cs : list (nat * ccert)) : Prop :=
    forall h ch, assoc h holesB = Some ch ->
      exists c, assoc h Cs = Some c /\ CHECK NB noHS (fst (fst c)) (add_kn (inst_list ch sigma) F) (snd (fst c)) = COk (cc_shape c).

  Definition PHIs2 (sigma : list (nat * expr)) (F : list kentry) : env -> Prop := fun E => sig_holds E sigma /\ Forall (pure_holds E) F.

  (* [comment removed for export] *)
  Definition F_ok (b : nat) (F : list kentry) : bool := (forallb pure_fact F && CAP.kn_vars_lt b F)%bool.
  Lemma pure_agree : forall b F E1 E2, env_agree b E1 E2 -> F_ok b F = true -> Forall (pure_holds E1) F -> Forall (pure_holds E2) F.
  Proof.
    intros b F E1 E2 Hag HF H. apply andb_prop in HF as [Hp Hv].
    eapply (pure_holds_of_know HSEGS E2 (fun _ => None) F Hp).
    eapply (know_ok_agree' HSEGS b E1 E2 _ F Hag Hv). apply know_of_pure_holds. exact H.
  Qed.

  Theorem B_leaf2 : forall sigma F Cs, sig_vars_lt NB sigma = true -> F_ok NB F = true -> Cs_vars_lt2 NB Cs = true -> C_ok2 sigma F Cs ->
    forall E R FULL model, CSOK (PHIs2 sigma F) E TB R FULL model ->
      crz HSEGS (cfg_of HSEGS R (pc TB) FULL model) (sd (HOLES_B2 Cs) t_nil E (m_fs model) shapeB).
  Proof.
    intros sigma F Cs Hsv HF HCv HCs E R FULL model HC.
    assert (PA : forall E1 E2, env_agree NB E1 E2 -> PHIs2 sigma F E1 -> PHIs2 sigma F E2).
    { intros E1 E2 Hag [H1 H2]. split; [exact (sig_holds_agree NB sigma E1 E2 Hag Hsv H1) | exact (pure_agree NB F E1 E2 Hag HF H2)]. }
    refine (g0_check_sound NB NB_ge NB_spw (PHIs2 sigma F) PA sp STR0 LIM fs Hsp Hstr Hstr8 (fun h => assoc h holesB) (HOLES_B2 Cs)
              (HOLES_B2_agree NB Cs HCv) (HOLES_B2_nil Cs) (HOLES_B2_mod Cs) _
              (APC.mk_itab_ranges HSEGS rsB) (mk_itab_ranges_sound HSEGS rsB) 0%nat false FUEL BF planB TB shapeB checkB E R FULL model HC).
    intros h ch Hh E1 R1 FULL1 model1 HC1. cbv beta in Hh.
    destruct (HCs h ch Hh) as [c [Hc Hchk]]. unfold HOLES_B2.
    rewrite (hole_cls_small h ltac:(apply Nat.ltb_lt; exact (proj1 (forallb_forall _ _) holesB_small (h, ch) (assoc_in2 _ _ _ _ Hh)))). rewrite Hc.
    pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC1) as [_ [HP HPF]].
    pose proof (cs_ok_inst_list_same HSEGS H0T LIM (argHt STR0) (bv_unsigned sp) fs (SINVg (PHIs2 sigma F) sp STR0) sigma ch E1 R1 FULL1 model1 HP (holesB_log h ch Hh) HC1) as HC2.
    pose proof (cs_ok_add_pure HSEGS H0T LIM (argHt STR0) (bv_unsigned sp) fs (SINVg (PHIs2 sigma F) sp STR0) E1 (inst_list ch sigma) R1 FULL1 model1 F HC2 HPF) as HC3.
    pose proof (g0_check_sound NB NB_ge NB_spw (PHIs2 sigma F) PA sp STR0 LIM fs Hsp Hstr Hstr8 noHS noHOLES (noHOLES_agree2 NB) noHOLES_nil2 noHOLES_mod
                  ltac:(intros h0 ch0 H0; discriminate H0)
                  (APC.mk_itab_ranges HSEGS (fst (fst c))) (mk_itab_ranges_sound HSEGS (fst (fst c))) 0%nat false FUEL BF (snd (fst c)) (add_kn (inst_list ch sigma) F) (cc_shape c) Hchk
                  E1 R1 FULL1 model1 HC3) as HR.
    change (pc (add_kn (inst_list ch sigma) F)) with (pc (inst_list ch sigma)) in HR. rewrite pc_inst_list in HR. exact HR.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable NA VS : nat.
  Hypothesis NA_ge : (NX0t <= NA)%nat.
  Hypothesis NA_spw : CAP.expr_vars_lt NA e_spw = true.
  Hypothesis NA_VS : (NA <= VS)%nat.
  Variable PHIA : env -> Prop.
  Hypothesis PHIA_agree : forall E E', env_agree NA E E' -> PHIA E -> PHIA E'.
  Hypothesis shapeB_vars : shape_vars_lt NA shapeB = true.

  (* [comment removed for export] *)
  Definition leaf : Type := (list (nat * expr) * list kentry * list (nat * ccert))%type.
  Definition lf_sig (l : leaf) := fst (fst l). Definition lf_F (l : leaf) := snd (fst l). Definition lf_Cs (l : leaf) := snd l.
  Variable Aholes : list (nat * leaf).
  Definition HS_A2 : nat -> option acs := fun h => match assoc h Aholes with Some l => Some (add_kn (inst_list TB (lf_sig l)) (lf_F l)) | None => None end.
  Definition HOLES_A2 : nat -> env -> Fs.Fs -> TSet :=
    fun h E fs0 => match assoc (CAP.hole_cls h) Aholes with Some l => sd (HOLES_B2 (lf_Cs l)) t_nil E fs0 shapeB | None => t_nil end.
  Hypothesis Aholes_small : keys_small Aholes = true.     (* [comment removed for export] *)
  Definition leaf_ok2 (l : leaf) : Prop :=
    sig_ok VS (lf_sig l) = true /\ sig_vars_lt NB (lf_sig l) = true /\ F_ok VS (lf_F l) = true /\ F_ok NB (lf_F l) = true
    /\ Cs_vars_lt2 NA (lf_Cs l) = true /\ Cs_vars_lt2 NB (lf_Cs l) = true /\ C_ok2 (lf_sig l) (lf_F l) (lf_Cs l).
  Hypothesis leaves_ok : forall h l, assoc h Aholes = Some l -> leaf_ok2 l.

  Variable rsA : list (Z * nat).
  Variable SA : acs.
  Variable planA : plan.
  Variable shapeA : shape.
  Hypothesis checkA : CHECK NA HS_A2 rsA SA planA = COk shapeA.

  Theorem chain_sound2 : forall E R FULL model, CSOK PHIA E SA R FULL model ->
    crz HSEGS (cfg_of HSEGS R (pc SA) FULL model) (sd HOLES_A2 t_nil E (m_fs model) shapeA).
  Proof.
    intros E R FULL model HC.
    refine (g0_check_sound NA NA_ge NA_spw PHIA PHIA_agree sp STR0 LIM fs Hsp Hstr Hstr8 HS_A2 HOLES_A2 _ _ _ _
              (APC.mk_itab_ranges HSEGS rsA) (mk_itab_ranges_sound HSEGS rsA) 0%nat false FUEL BF planA SA shapeA checkA E R FULL model HC).
    - intros h E1 E2 fs0 Hag. unfold HOLES_A2. destruct (assoc (CAP.hole_cls h) Aholes) as [l|] eqn:Hl; [|reflexivity].
      destruct (leaves_ok _ l Hl) as (_ & _ & _ & _ & Hcv & _ & _).
      exact (sd_agree NA (HOLES_B2 (lf_Cs l)) (HOLES_B2_agree NA (lf_Cs l) Hcv) t_nil E1 E2 fs0 shapeB Hag shapeB_vars).
    - intros h E1 fs0. unfold HOLES_A2. destruct (assoc (CAP.hole_cls h) Aholes); [apply (sd_has_nil _ (HOLES_B2_nil _)); reflexivity | reflexivity].
    - intros h E1 fs0. unfold HOLES_A2. rewrite hole_cls_idem. reflexivity.
    - intros h ch Hh E1 R1 FULL1 model1 HC1. unfold HS_A2 in Hh. unfold HOLES_A2.
      destruct (assoc h Aholes) as [l|] eqn:Hl; [|discriminate]. injection Hh as <-.
      rewrite (hole_cls_small h ltac:(apply Nat.ltb_lt; exact (proj1 (forallb_forall _ _) Aholes_small (h, l) (assoc_in2 _ _ _ _ Hl)))). rewrite Hl.
      destruct (leaves_ok h l Hl) as (Hso & Hsv & HFv & HFb & Hcva & Hcvb & HCs).
      assert (HFp : forallb pure_fact (lf_F l) = true) by (apply andb_prop in HFv as [X _]; exact X).
      pose proof (add_kn_facts_hold HSEGS H0T LIM (argHt STR0) (bv_unsigned sp) fs (SINVg PHIA sp STR0) E1 (inst_list TB (lf_sig l)) R1 FULL1 model1 (lf_F l) HFp HC1) as HF1.
      pose proof (cs_ok_unadd HSEGS H0T LIM (argHt STR0) (bv_unsigned sp) fs (SINVg PHIA sp STR0) E1 (inst_list TB (lf_sig l)) R1 FULL1 model1 (lf_F l)
                    (inst_list_log TB (lf_sig l) TB_log) HC1) as HC1'.
      assert (Hdom : forall p, In p (lf_sig l) -> (NA <= fst p)%nat)
        by (intros p Hp; pose proof (sig_ok_dom VS (lf_sig l) Hso p Hp); lia).
      pose proof (cs_ok_apply_sig HSEGS H0T LIM (argHt STR0) (bv_unsigned sp) fs NA NA_spw (SINVg PHIA sp STR0)
                    (AA_g NA STR0) (SA_g NA NA_ge PHIA PHIA_agree sp STR0) (lf_sig l) TB E1 R1 FULL1 model1 Hdom TB_log HC1') as HC2.
      set (E2 := apply_sig E1 (lf_sig l)) in *.
      assert (HagV : env_agree VS E1 E2) by (apply (apply_sig_agree VS (lf_sig l) E1); exact (sig_ok_dom VS (lf_sig l) Hso)).
      assert (Hag : env_agree NA E1 E2) by (eapply env_agree_le; [exact HagV | exact NA_VS]).
      assert (HC3 : CSOK (PHIs2 (lf_sig l) (lf_F l)) E2 TB R1 FULL1 model1).
      { apply (cs_ok_sinv HSEGS H0T LIM (argHt STR0) (bv_unsigned sp) fs (SINVg PHIA sp STR0) (SINVg (PHIs2 (lf_sig l) (lf_F l)) sp STR0) E2 TB R1 FULL1 model1); [|exact HC2].
        intros [H1 _]. split; [exact H1|]. split; [exact (apply_sig_holds VS (lf_sig l) E1 Hso) | exact (pure_agree VS (lf_F l) E1 E2 HagV HFv HF1)]. }
      pose proof (B_leaf2 (lf_sig l) (lf_F l) (lf_Cs l) Hsv HFb Hcvb HCs E2 R1 FULL1 model1 HC3) as HR.
      change (pc (add_kn (inst_list TB (lf_sig l)) (lf_F l))) with (pc (inst_list TB (lf_sig l))). rewrite pc_inst_list.
      rewrite (sd_agree NA (HOLES_B2 (lf_Cs l)) (HOLES_B2_agree NA (lf_Cs l) Hcva) t_nil E1 E2 (m_fs model1) shapeB Hag shapeB_vars).
      exact HR.
  Qed.
End Chain2.

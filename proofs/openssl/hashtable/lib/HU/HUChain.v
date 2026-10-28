(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxGlue.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HUPlanImage HUAtable H0Sinv HUCheckG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Fixpoint assoc {X : Type} (h : nat) (l : list (nat * X)) : option X :=
  match l with [] => None | (k, x) :: r => if Nat.eqb k h then Some x else assoc h r end.

Definition noHS : nat -> option acs := fun _ => None.
Definition noHOLES : nat -> env -> Fs.Fs -> TSet := fun _ _ _ => t_nil.

(* [comment removed for export] *)
Lemma hole_cls_small : forall h, (h < 1000)%nat -> CAP.hole_cls h = h.
Proof. intros h Hh. unfold CAP.hole_cls. apply Nat.mod_small. exact Hh. Qed.
Lemma hole_cls_idem : forall h, CAP.hole_cls (CAP.hole_cls h) = CAP.hole_cls h.
Proof. intros h. unfold CAP.hole_cls. apply Nat.Div0.mod_mod. Qed.
Lemma noHOLES_mod : forall h E fs0, noHOLES h E fs0 = noHOLES (CAP.hole_cls h) E fs0.
Proof. reflexivity. Qed.
Definition keys_small {X : Type} (l : list (nat * X)) : bool := forallb (fun p => Nat.ltb (fst p) 1000) l.

(* [comment removed for export] *)
Definition sig_vars_lt (b : nat) (s : list (nat * expr)) : bool :=
  forallb (fun p => Nat.ltb (fst p) b && CAP.expr_vars_lt b (snd p))%bool s.

Lemma sig_holds_agree : forall b s E E', env_agree b E E' -> sig_vars_lt b s = true -> sig_holds E s -> sig_holds E' s.
Proof.
  intros b s E E' Hag Hv H. unfold sig_holds in *. apply Forall_forall. intros p Hp.
  pose proof (proj1 (Forall_forall _ _) H p Hp) as Hq. pose proof (proj1 (forallb_forall _ _) Hv p Hp) as Hb.
  apply andb_prop in Hb as [Hb1 Hb2]. apply Nat.ltb_lt in Hb1.
  rewrite <- (proj1 Hag (fst p) Hb1). rewrite <- (edenot_agree' b E E' (snd p) Hag Hb2). exact Hq.
Qed.

(* [comment removed for export] *)
Definition ccert : Type := (list (Z * nat) * plan * shape)%type.
Definition cc_shape (c : ccert) : shape := snd c.

Section Chain.
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
  Definition HOLES_B (Cs : list (nat * ccert)) : nat -> env -> Fs.Fs -> TSet :=
    fun h E fs0 => match assoc (CAP.hole_cls h) Cs with Some c => sd noHOLES t_nil E fs0 (cc_shape c) | None => t_nil end.
  Lemma HOLES_B_mod : forall Cs h E fs0, HOLES_B Cs h E fs0 = HOLES_B Cs (CAP.hole_cls h) E fs0.
  Proof. intros Cs h E fs0. unfold HOLES_B. rewrite hole_cls_idem. reflexivity. Qed.

  Lemma noHOLES_agree : forall b h E E' fs0, env_agree b E E' -> noHOLES h E fs0 = noHOLES h E' fs0.
  Proof. reflexivity. Qed.
  Lemma noHOLES_nil : forall h E fs0, noHOLES h E fs0 [].
  Proof. reflexivity. Qed.

  Definition Cs_vars_lt (b : nat) (Cs : list (nat * ccert)) : bool := forallb (fun p => shape_vars_lt b (cc_shape (snd p))) Cs.
  Lemma assoc_in : forall X h (l : list (nat * X)) x, assoc h l = Some x -> In (h, x) l.
  Proof.
    intros X h l x. induction l as [|[k y] r IH]; cbn [assoc]; [discriminate|].
    destruct (Nat.eqb_spec k h); [intros [= ->]; subst; left; reflexivity | intros H; right; exact (IH H)].
  Qed.
  Lemma HOLES_B_agree : forall b Cs, Cs_vars_lt b Cs = true -> forall h E E' fs0, env_agree b E E' -> HOLES_B Cs h E fs0 = HOLES_B Cs h E' fs0.
  Proof.
    intros b Cs Hv h E E' fs0 Hag. unfold HOLES_B. destruct (assoc (CAP.hole_cls h) Cs) as [c|] eqn:Hc; [|reflexivity].
    apply (sd_agree b noHOLES (noHOLES_agree b) t_nil E E' fs0 (cc_shape c) Hag).
    exact (proj1 (forallb_forall _ _) Hv (CAP.hole_cls h, c) (assoc_in _ _ _ _ Hc)).
  Qed.
  Lemma HOLES_B_nil : forall Cs h E fs0, HOLES_B Cs h E fs0 [].
  Proof. intros Cs h E fs0. unfold HOLES_B. destruct (assoc (CAP.hole_cls h) Cs); [apply (sd_has_nil noHOLES noHOLES_nil); reflexivity | reflexivity]. Qed.

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
  Definition C_ok (sigma : list (nat * expr)) (Cs : list (nat * ccert)) : Prop :=
    forall h ch, assoc h holesB = Some ch ->
      exists c, assoc h Cs = Some c /\ CHECK NB noHS (fst (fst c)) (inst_list ch sigma) (snd (fst c)) = COk (cc_shape c).

  Definition PHIs (sigma : list (nat * expr)) : env -> Prop := fun E => sig_holds E sigma.

  (* [comment removed for export] *)
  Theorem B_leaf : forall sigma Cs, sig_vars_lt NB sigma = true -> Cs_vars_lt NB Cs = true -> C_ok sigma Cs ->
    forall E R FULL model, CSOK (PHIs sigma) E TB R FULL model ->
      crz HSEGS (cfg_of HSEGS R (pc TB) FULL model) (sd (HOLES_B Cs) t_nil E (m_fs model) shapeB).
  Proof.
    intros sigma Cs Hsv HCv HCs E R FULL model HC.
    assert (PA : forall E1 E2, env_agree NB E1 E2 -> PHIs sigma E1 -> PHIs sigma E2)
      by (intros E1 E2 Hag H; exact (sig_holds_agree NB sigma E1 E2 Hag Hsv H)).
    refine (g0_check_sound NB NB_ge NB_spw (PHIs sigma) PA sp STR0 LIM fs Hsp Hstr Hstr8 (fun h => assoc h holesB) (HOLES_B Cs)
              (HOLES_B_agree NB Cs HCv) (HOLES_B_nil Cs) (HOLES_B_mod Cs) _
              (APC.mk_itab_ranges HSEGS rsB) (mk_itab_ranges_sound HSEGS rsB) 0%nat false FUEL BF planB TB shapeB checkB E R FULL model HC).
    (* [comment removed for export] *)
    intros h ch Hh E1 R1 FULL1 model1 HC1. cbv beta in Hh.
    destruct (HCs h ch Hh) as [c [Hc Hchk]]. unfold HOLES_B.
    rewrite (hole_cls_small h ltac:(apply Nat.ltb_lt; exact (proj1 (forallb_forall _ _) holesB_small (h, ch) (assoc_in _ _ _ _ Hh)))). rewrite Hc.
    pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC1) as [_ HP].
    pose proof (cs_ok_inst_list_same HSEGS H0T LIM (argHt STR0) (bv_unsigned sp) fs (SINVg (PHIs sigma) sp STR0) sigma ch E1 R1 FULL1 model1 HP (holesB_log h ch Hh) HC1) as HC2.
    pose proof (g0_check_sound NB NB_ge NB_spw (PHIs sigma) PA sp STR0 LIM fs Hsp Hstr Hstr8 noHS noHOLES (noHOLES_agree NB) noHOLES_nil noHOLES_mod
                  ltac:(intros h0 ch0 H0; discriminate H0)
                  (APC.mk_itab_ranges HSEGS (fst (fst c))) (mk_itab_ranges_sound HSEGS (fst (fst c))) 0%nat false FUEL BF (snd (fst c)) (inst_list ch sigma) (cc_shape c) Hchk
                  E1 R1 FULL1 model1 HC2) as HR.
    rewrite pc_inst_list in HR. exact HR.
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
  Variable Aholes : list (nat * (list (nat * expr) * list (nat * ccert))).
  Definition HS_A : nat -> option acs := fun h => match assoc h Aholes with Some l => Some (inst_list TB (fst l)) | None => None end.
  Definition HOLES_A : nat -> env -> Fs.Fs -> TSet :=
    fun h E fs0 => match assoc (CAP.hole_cls h) Aholes with Some l => sd (HOLES_B (snd l)) t_nil E fs0 shapeB | None => t_nil end.
  Hypothesis Aholes_small : keys_small Aholes = true.     (* [comment removed for export] *)
  Definition leaf_ok (l : list (nat * expr) * list (nat * ccert)) : Prop :=
    sig_ok VS (fst l) = true /\ sig_vars_lt NB (fst l) = true /\ Cs_vars_lt NA (snd l) = true /\ Cs_vars_lt NB (snd l) = true /\ C_ok (fst l) (snd l).
  Hypothesis leaves_ok : forall h l, assoc h Aholes = Some l -> leaf_ok l.

  Variable rsA : list (Z * nat).
  Variable SA : acs.
  Variable planA : plan.
  Variable shapeA : shape.
  Hypothesis checkA : CHECK NA HS_A rsA SA planA = COk shapeA.

  Theorem chain_sound : forall E R FULL model, CSOK PHIA E SA R FULL model ->
    crz HSEGS (cfg_of HSEGS R (pc SA) FULL model) (sd HOLES_A t_nil E (m_fs model) shapeA).
  Proof.
    intros E R FULL model HC.
    refine (g0_check_sound NA NA_ge NA_spw PHIA PHIA_agree sp STR0 LIM fs Hsp Hstr Hstr8 HS_A HOLES_A _ _ _ _
              (APC.mk_itab_ranges HSEGS rsA) (mk_itab_ranges_sound HSEGS rsA) 0%nat false FUEL BF planA SA shapeA checkA E R FULL model HC).
    - intros h E1 E2 fs0 Hag. unfold HOLES_A. destruct (assoc (CAP.hole_cls h) Aholes) as [l|] eqn:Hl; [|reflexivity].
      destruct (leaves_ok _ l Hl) as (_ & _ & Hcv & _ & _).
      exact (sd_agree NA (HOLES_B (snd l)) (HOLES_B_agree NA (snd l) Hcv) t_nil E1 E2 fs0 shapeB Hag shapeB_vars).
    - intros h E1 fs0. unfold HOLES_A. destruct (assoc (CAP.hole_cls h) Aholes); [apply (sd_has_nil _ (HOLES_B_nil _)); reflexivity | reflexivity].
    - intros h E1 fs0. unfold HOLES_A. rewrite hole_cls_idem. reflexivity.
    - intros h ch Hh E1 R1 FULL1 model1 HC1. unfold HS_A in Hh. unfold HOLES_A.
      destruct (assoc h Aholes) as [l|] eqn:Hl; [|discriminate]. injection Hh as <-.
      rewrite (hole_cls_small h ltac:(apply Nat.ltb_lt; exact (proj1 (forallb_forall _ _) Aholes_small (h, l) (assoc_in _ _ _ _ Hl)))). rewrite Hl.
      destruct (leaves_ok h l Hl) as (Hso & Hsv & Hcva & Hcvb & HCs).
      assert (Hdom : forall p, In p (fst l) -> (NA <= fst p)%nat)
        by (intros p Hp; pose proof (sig_ok_dom VS (fst l) Hso p Hp); lia).
      pose proof (cs_ok_apply_sig HSEGS H0T LIM (argHt STR0) (bv_unsigned sp) fs NA NA_spw (SINVg PHIA sp STR0)
                    (AA_g NA STR0) (SA_g NA NA_ge PHIA PHIA_agree sp STR0) (fst l) TB E1 R1 FULL1 model1 Hdom TB_log HC1) as HC2.
      set (E2 := apply_sig E1 (fst l)) in *.
      assert (Hag : env_agree NA E1 E2).
      { eapply env_agree_le; [apply (apply_sig_agree VS (fst l) E1); exact (sig_ok_dom VS (fst l) Hso) | exact NA_VS]. }
      assert (HC3 : CSOK (PHIs (fst l)) E2 TB R1 FULL1 model1).
      { apply (cs_ok_sinv HSEGS H0T LIM (argHt STR0) (bv_unsigned sp) fs (SINVg PHIA sp STR0) (SINVg (PHIs (fst l)) sp STR0) E2 TB R1 FULL1 model1); [|exact HC2].
        intros [H1 _]. split; [exact H1 | exact (apply_sig_holds VS (fst l) E1 Hso)]. }
      pose proof (B_leaf (fst l) (snd l) Hsv Hcvb HCs E2 R1 FULL1 model1 HC3) as HR.
      rewrite pc_inst_list.
      rewrite (sd_agree NA (HOLES_B (snd l)) (HOLES_B_agree NA (snd l) Hcva) t_nil E1 E2 (m_fs model1) shapeB Hag shapeB_vars).
      exact HR.
  Qed.
End Chain.

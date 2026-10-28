(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxGlue.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HBPlanImage HBAtable HBArg HBCheckG HBChain.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import DietTac.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Fixpoint assoc {X : Type} (h : nat) (l : list (nat * X)) : option X :=
  match l with [] => None | (k, x) :: r => if Nat.eqb k h then Some x else assoc h r end.
Lemma assoc_in2 : forall X h (l : list (nat * X)) x, assoc h l = Some x -> In (h, x) l.
Proof.
  intros X h l x. induction l as [|[k y] r IH]; cbn [assoc]; [discriminate|].
  destruct (Nat.eqb_spec k h); [intros [= ->]; subst; left; reflexivity | intros H; right; exact (IH H)].
Qed.

Definition noHS : nat -> option acs := fun _ => None.
Definition noHOLES : nat -> env -> Fs.Fs -> TSet := fun _ _ _ => t_nil.
Lemma hole_cls_small : forall h, (h < 1000)%nat -> CAP.hole_cls h = h.
Proof. intros h Hh. unfold CAP.hole_cls. apply Nat.mod_small. exact Hh. Qed.
Lemma hole_cls_idem : forall h, CAP.hole_cls (CAP.hole_cls h) = CAP.hole_cls h.
Proof. intros h. unfold CAP.hole_cls. apply Nat.Div0.mod_mod. Qed.
Lemma noHOLES_mod : forall h E fs0, noHOLES h E fs0 = noHOLES (CAP.hole_cls h) E fs0.
Proof. reflexivity. Qed.
Lemma noHOLES_agree2 : forall b h E E' fs0, env_agree b E E' -> noHOLES h E fs0 = noHOLES h E' fs0.
Proof. reflexivity. Qed.
Lemma noHOLES_nil2 : forall h E fs0, noHOLES h E fs0 [].
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
Definition F_ok (b : nat) (F : list kentry) : bool := (forallb pure_fact F && CAP.kn_vars_lt b F)%bool.
Lemma pure_agree : forall b F E1 E2, env_agree b E1 E2 -> F_ok b F = true -> Forall (pure_holds E1) F -> Forall (pure_holds E2) F.
Proof.
  intros b F E1 E2 Hag HF H. apply andb_prop in HF as [Hp Hv].
  eapply (pure_holds_of_know HASEGS E2 (fun _ => None) F Hp).
  eapply (know_ok_agree' HASEGS b E1 E2 _ F Hag Hv). apply know_of_pure_holds. exact H.
Qed.

(* [comment removed for export] *)
Definition htgt : Type := (acs * list (nat * expr) * list kentry)%type.
Definition ht_T (t : htgt) : acs := fst (fst t).
Definition ht_s (t : htgt) : list (nat * expr) := snd (fst t).
Definition ht_F (t : htgt) : list kentry := snd t.
Definition ht_state (t : htgt) : acs := add_kn (inst_list (ht_T t) (ht_s t)) (ht_F t).
Definition HS_tg (holes : list (nat * htgt)) : nat -> option acs :=
  fun h => match assoc h holes with Some t => Some (ht_state t) | None => None end.
(* [comment removed for export] *)
Definition ht_ok (VS : nat) (t : htgt) : bool :=
  (match s_log (a_ss (ht_T t)) with [] => true | _ => false end && sig_ok VS (ht_s t) && F_ok VS (ht_F t))%bool.

Definition PHI_ext (PHI : env -> Prop) (s : list (nat * expr)) (F : list kentry) : env -> Prop :=
  fun E => PHI E /\ sig_holds E s /\ Forall (pure_holds E) F.

Lemma PHI_ext_agree : forall b PHI s F, (forall E E', env_agree b E E' -> PHI E -> PHI E') ->
  sig_vars_lt b s = true -> F_ok b F = true -> forall E E', env_agree b E E' -> PHI_ext PHI s F E -> PHI_ext PHI s F E'.
Proof.
  intros b PHI s F HP Hs HF E E' Hag (H1 & H2 & H3). split; [exact (HP E E' Hag H1)|]. split.
  - exact (sig_holds_agree b s E E' Hag Hs H2).
  - exact (pure_agree b F E E' Hag HF H3).
Qed.

Section Hop.
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
  (* [comment removed for export] *)
  Variable SV : env -> (word -> option byte) -> Prop.
  Hypothesis SV_to1 : forall E M, SV E M -> HBArg.SINV1 sp brk0 argv envp rdraw hw uid E M.
  Hypothesis SV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SV E M -> SV E M'.
  Hypothesis SV_agree : forall E E' M, env_agree NX0 E E' -> SV E M -> SV E' M.
  Variable GC : bool.
  Variables BF FUEL : nat.

  #[local] Notation CSOK PHI := (cs_ok HASEGS HAT LIM (SVG PHI SV) argH ISP fs).
  #[local] Notation CHECK NX HS IT := (CAP.check HASEGS IT HAT NX LIM (hag_XN NX) (hag_XE NX) hag_XB HS 0 true false GC BF FUEL None).
  #[local] Notation GCS NX NX_ge NX_spw PHI PHI_agree := (hag_check_sound NX NX_ge NX_spw PHI PHI_agree sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit SV SV_to1 SV_frame SV_agree).

  (* [comment removed for export] *)
  Lemma csok_phi : forall (PHI PHI' : env -> Prop) E cs R FULL model, (PHI E -> PHI' E) -> CSOK PHI E cs R FULL model -> CSOK PHI' E cs R FULL model.
  Proof.
    intros PHI PHI' E cs R FULL model H HC.
    apply (cs_ok_sinv HASEGS HAT LIM argH ISP fs (SVG PHI SV) (SVG PHI' SV) E cs R FULL model); [|exact HC].
    intros [H1 H2]. split; [exact H1 | exact (H H2)].
  Qed.
  Lemma csok_phi_holds : forall (PHI : env -> Prop) E cs R FULL model, CSOK PHI E cs R FULL model -> PHI E.
  Proof. intros PHI E cs R FULL model HC. exact (proj2 (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC)). Qed.

  (* [comment removed for export] *)
  Lemma spec_back : forall (PHI : env -> Prop) s F ch E R FULL model,
    (forall E, PHI E -> sig_holds E s /\ Forall (pure_holds E) F) -> s_log (a_ss ch) = [] ->
    CSOK PHI E ch R FULL model -> CSOK PHI E (add_kn (inst_list ch s) F) R FULL model.
  Proof.
    intros PHI s F ch E R FULL model HP Hlog HC.
    destruct (HP E (csok_phi_holds PHI E ch R FULL model HC)) as [Hs HF].
    apply (cs_ok_add_pure HASEGS HAT LIM argH ISP fs (SVG PHI SV) E (inst_list ch s) R FULL model F); [|exact HF].
    exact (cs_ok_inst_list_same HASEGS HAT LIM argH ISP fs (SVG PHI SV) s ch E R FULL model Hs Hlog HC).
  Qed.
  Lemma add_facts : forall (PHI : env -> Prop) F cs E R FULL model,
    (forall E, PHI E -> Forall (pure_holds E) F) -> CSOK PHI E cs R FULL model -> CSOK PHI E (add_kn cs F) R FULL model.
  Proof.
    intros PHI F cs E R FULL model HP HC.
    exact (cs_ok_add_pure HASEGS HAT LIM argH ISP fs (SVG PHI SV) E cs R FULL model F HC (HP E (csok_phi_holds PHI E cs R FULL model HC))).
  Qed.

  (* [comment removed for export] *)
  Theorem leaf_sound : forall NX, (NX0 <= NX)%nat -> CAP.expr_vars_lt NX e_spw = true ->
    forall (PHI : env -> Prop), (forall E E', env_agree NX E E' -> PHI E -> PHI E') ->
    forall IT, itab_sound HASEGS IT -> forall S plan shape, CHECK NX noHS IT S plan = COk shape ->
    forall E R FULL model, CSOK PHI E S R FULL model ->
      crz HASEGS (cfg_of HASEGS R (pc S) FULL model) (sd noHOLES t_nil E (m_fs model) shape).
  Proof.
    intros NX NX_ge NX_spw PHI PHI_agree IT IT_ok S plan shape Hchk E R FULL model HC.
    exact (GCS NX NX_ge NX_spw PHI PHI_agree noHS noHOLES (noHOLES_agree2 NX) noHOLES_nil2 noHOLES_mod
             ltac:(intros h0 ch0 H0; discriminate H0)
             IT IT_ok 0%nat GC FUEL BF plan S shape Hchk E R FULL model HC).
  Qed.

  Section OneHop.
    Variable NX VS : nat.
    Hypothesis NX_ge : (NX0 <= NX)%nat.
    Hypothesis NX_spw : CAP.expr_vars_lt NX e_spw = true.
    Hypothesis NX_VS : (NX <= VS)%nat.
    Variable PHI : env -> Prop.
    Hypothesis PHI_agree : forall E E', env_agree NX E E' -> PHI E -> PHI E'.
    Variable holes : list (nat * htgt).
    Hypothesis holes_ok : forallb (fun p => ht_ok VS (snd p)) holes = true.
    Variable HOLES : nat -> env -> Fs.Fs -> TSet.
    Hypothesis HOLES_agree : forall h E E' fs0, env_agree NX E E' -> HOLES h E fs0 = HOLES h E' fs0.
    Hypothesis HOLES_nil : forall h E fs0, HOLES h E fs0 [].
    Hypothesis HOLES_mod : forall h E fs0, HOLES h E fs0 = HOLES (CAP.hole_cls h) E fs0.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    Hypothesis conts : forall h t, assoc h holes = Some t ->
      forall E R FULL model, CSOK (PHI_ext PHI (ht_s t) (ht_F t)) E (ht_T t) R FULL model ->
        crz HASEGS (cfg_of HASEGS R (pc (ht_T t)) FULL model) (HOLES h E (m_fs model)).
    Variable IT : itab.
    Hypothesis IT_ok : itab_sound HASEGS IT.
    Variable S : acs.
    Variable plan : CAP.plan.
    Variable shape : CAP.shape.
    Hypothesis chk : CHECK NX (HS_tg holes) IT S plan = COk shape.

    Theorem hop_sound : forall E R FULL model, CSOK PHI E S R FULL model ->
      crz HASEGS (cfg_of HASEGS R (pc S) FULL model) (sd HOLES t_nil E (m_fs model) shape).
    Proof.
      intros E R FULL model HC.
      refine (GCS NX NX_ge NX_spw PHI PHI_agree (HS_tg holes) HOLES HOLES_agree HOLES_nil HOLES_mod _
                IT IT_ok 0%nat GC FUEL BF plan S shape chk E R FULL model HC).
      intros h ch Hh E1 R1 FULL1 model1 HC1. unfold HS_tg in Hh.
      destruct (assoc h holes) as [t|] eqn:Ht; [|discriminate]. diet_injection Hh.
      pose proof (proj1 (forallb_forall _ _) holes_ok (h, t) (assoc_in2 _ _ _ _ Ht)) as Hok. cbn [snd] in Hok.
      unfold ht_ok in Hok. apply andb_prop in Hok as [Hok HFv]. apply andb_prop in Hok as [Hlog Hso].
      assert (TL : s_log (a_ss (ht_T t)) = []) by (destruct (s_log (a_ss (ht_T t))); [reflexivity | discriminate]).
      unfold ht_state in HC1.
      assert (HFp : forallb pure_fact (ht_F t) = true) by (apply andb_prop in HFv as [X _]; exact X).
      pose proof (add_kn_facts_hold HASEGS HAT LIM argH ISP fs (SVG PHI SV) E1 (inst_list (ht_T t) (ht_s t)) R1 FULL1 model1 (ht_F t) HFp HC1) as HF1.
      pose proof (cs_ok_unadd HASEGS HAT LIM argH ISP fs (SVG PHI SV) E1 (inst_list (ht_T t) (ht_s t)) R1 FULL1 model1 (ht_F t)
                    (inst_list_log (ht_T t) (ht_s t) TL) HC1) as HC1'.
      assert (Hdom : forall p, In p (ht_s t) -> (NX <= fst p)%nat)
        by (intros p Hp; pose proof (sig_ok_dom VS (ht_s t) Hso p Hp); lia).
      pose proof (cs_ok_apply_sig HASEGS HAT LIM argH ISP fs NX NX_spw (SVG PHI SV)
                    (AA_g NX NX_ge sp rdraw argv envp uid hw) (SA_g NX NX_ge PHI PHI_agree SV SV_agree) (ht_s t) (ht_T t) E1 R1 FULL1 model1 Hdom TL HC1') as HC2.
      set (E2 := apply_sig E1 (ht_s t)) in *.
      assert (HagV : env_agree VS E1 E2) by (apply (apply_sig_agree VS (ht_s t) E1); exact (sig_ok_dom VS (ht_s t) Hso)).
      assert (Hag : env_agree NX E1 E2) by (eapply env_agree_le; [exact HagV | exact NX_VS]).
      assert (HC3 : CSOK (PHI_ext PHI (ht_s t) (ht_F t)) E2 (ht_T t) R1 FULL1 model1).
      { apply (csok_phi PHI (PHI_ext PHI (ht_s t) (ht_F t)) E2 (ht_T t) R1 FULL1 model1); [|exact HC2].
        intros HP. split; [exact HP|]. split; [exact (apply_sig_holds VS (ht_s t) E1 Hso) | exact (pure_agree VS (ht_F t) E1 E2 HagV HFv HF1)]. }
      pose proof (conts h t Ht E2 R1 FULL1 model1 HC3) as HR.
      unfold ht_state. change (pc (add_kn (inst_list (ht_T t) (ht_s t)) (ht_F t))) with (pc (inst_list (ht_T t) (ht_s t))). rewrite pc_inst_list.
      rewrite (HOLES_agree h E1 E2 (m_fs model1) Hag). exact HR.
    Qed.
  End OneHop.
  (* [comment removed for export] *)
  Lemma fx_hole_phi : forall NX (PHI : env -> Prop), (forall E E', env_agree NX E E' -> PHI E -> PHI E') ->
    forall START END, (NX <= nxt START)%nat -> fx_hole SV argH ISP fs START END -> fx_hole (SVG PHI SV) argH ISP fs START END.
  Proof.
    intros NX PHI PHI_agree START END Hnx HF E R FULL m T HC Hk.
    pose proof (csok_phi_holds PHI E START R FULL m HC) as HP.
    apply (HF E R FULL m T).
    - apply (cs_ok_sinv HASEGS HAT LIM argH ISP fs (SVG PHI SV) SV E START R FULL m); [|exact HC]. intros [H1 _]. exact H1.
    - intros E1 R1 FULL1 m1 Hag HC1 Hfs. apply (Hk E1 R1 FULL1 m1 Hag); [|exact Hfs].
      apply (cs_ok_sinv HASEGS HAT LIM argH ISP fs SV (SVG PHI SV) E1 END R1 FULL1 m1); [|exact HC1].
      intros H1. split; [exact H1|]. apply (PHI_agree E E1); [|exact HP]. eapply env_agree_le; [exact Hag | exact Hnx].
  Qed.
End Hop.

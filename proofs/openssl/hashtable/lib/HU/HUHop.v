(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxGlue.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HUPlanImage HUAtable H0Sinv HUCheckG HUChain HUChain2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

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
  Lemma csok_phi : forall (PHI PHI' : env -> Prop) E cs R FULL model, (PHI E -> PHI' E) -> CSOK PHI E cs R FULL model -> CSOK PHI' E cs R FULL model.
  Proof.
    intros PHI PHI' E cs R FULL model H HC.
    apply (cs_ok_sinv HSEGS H0T LIM (argHt STR0) (bv_unsigned sp) fs (SINVg PHI sp STR0) (SINVg PHI' sp STR0) E cs R FULL model); [|exact HC].
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
    apply (cs_ok_add_pure HSEGS H0T LIM (argHt STR0) (bv_unsigned sp) fs (SINVg PHI sp STR0) E (inst_list ch s) R FULL model F); [|exact HF].
    exact (cs_ok_inst_list_same HSEGS H0T LIM (argHt STR0) (bv_unsigned sp) fs (SINVg PHI sp STR0) s ch E R FULL model Hs Hlog HC).
  Qed.
  Lemma add_facts : forall (PHI : env -> Prop) F cs E R FULL model,
    (forall E, PHI E -> Forall (pure_holds E) F) -> CSOK PHI E cs R FULL model -> CSOK PHI E (add_kn cs F) R FULL model.
  Proof.
    intros PHI F cs E R FULL model HP HC.
    exact (cs_ok_add_pure HSEGS H0T LIM (argHt STR0) (bv_unsigned sp) fs (SINVg PHI sp STR0) E cs R FULL model F HC (HP E (csok_phi_holds PHI E cs R FULL model HC))).
  Qed.

  (* [comment removed for export] *)
  Theorem leaf_sound : forall NX, (NX0t <= NX)%nat -> CAP.expr_vars_lt NX e_spw = true ->
    forall (PHI : env -> Prop), (forall E E', env_agree NX E E' -> PHI E -> PHI E') ->
    forall rs S plan shape, CHECK NX noHS rs S plan = COk shape ->
    forall E R FULL model, CSOK PHI E S R FULL model ->
      crz HSEGS (cfg_of HSEGS R (pc S) FULL model) (sd noHOLES t_nil E (m_fs model) shape).
  Proof.
    intros NX NX_ge NX_spw PHI PHI_agree rs S plan shape Hchk E R FULL model HC.
    exact (g0_check_sound NX NX_ge NX_spw PHI PHI_agree sp STR0 LIM fs Hsp Hstr Hstr8 noHS noHOLES (noHOLES_agree2 NX) noHOLES_nil2 noHOLES_mod
             ltac:(intros h0 ch0 H0; discriminate H0)
             (APC.mk_itab_ranges HSEGS rs) (mk_itab_ranges_sound HSEGS rs) 0%nat false FUEL BF plan S shape Hchk E R FULL model HC).
  Qed.

  Section OneHop.
    Variable NX VS : nat.
    Hypothesis NX_ge : (NX0t <= NX)%nat.
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
        crz HSEGS (cfg_of HSEGS R (pc (ht_T t)) FULL model) (HOLES h E (m_fs model)).
    Variable rs : list (Z * nat).
    Variable S : acs.
    Variable plan : CAP.plan.
    Variable shape : CAP.shape.
    Hypothesis chk : CHECK NX (HS_tg holes) rs S plan = COk shape.

    Theorem hop_sound : forall E R FULL model, CSOK PHI E S R FULL model ->
      crz HSEGS (cfg_of HSEGS R (pc S) FULL model) (sd HOLES t_nil E (m_fs model) shape).
    Proof.
      intros E R FULL model HC.
      refine (g0_check_sound NX NX_ge NX_spw PHI PHI_agree sp STR0 LIM fs Hsp Hstr Hstr8 (HS_tg holes) HOLES HOLES_agree HOLES_nil HOLES_mod _
                (APC.mk_itab_ranges HSEGS rs) (mk_itab_ranges_sound HSEGS rs) 0%nat false FUEL BF plan S shape chk E R FULL model HC).
      intros h ch Hh E1 R1 FULL1 model1 HC1. unfold HS_tg in Hh.
      destruct (assoc h holes) as [t|] eqn:Ht; [|discriminate]. injection Hh as <-.
      pose proof (proj1 (forallb_forall _ _) holes_ok (h, t) (assoc_in2 _ _ _ _ Ht)) as Hok. cbn [snd] in Hok.
      unfold ht_ok in Hok. apply andb_prop in Hok as [Hok HFv]. apply andb_prop in Hok as [Hlog Hso].
      assert (TL : s_log (a_ss (ht_T t)) = []) by (destruct (s_log (a_ss (ht_T t))); [reflexivity | discriminate]).
      unfold ht_state in HC1.
      assert (HFp : forallb pure_fact (ht_F t) = true) by (apply andb_prop in HFv as [X _]; exact X).
      pose proof (add_kn_facts_hold HSEGS H0T LIM (argHt STR0) (bv_unsigned sp) fs (SINVg PHI sp STR0) E1 (inst_list (ht_T t) (ht_s t)) R1 FULL1 model1 (ht_F t) HFp HC1) as HF1.
      pose proof (cs_ok_unadd HSEGS H0T LIM (argHt STR0) (bv_unsigned sp) fs (SINVg PHI sp STR0) E1 (inst_list (ht_T t) (ht_s t)) R1 FULL1 model1 (ht_F t)
                    (inst_list_log (ht_T t) (ht_s t) TL) HC1) as HC1'.
      assert (Hdom : forall p, In p (ht_s t) -> (NX <= fst p)%nat)
        by (intros p Hp; pose proof (sig_ok_dom VS (ht_s t) Hso p Hp); lia).
      pose proof (cs_ok_apply_sig HSEGS H0T LIM (argHt STR0) (bv_unsigned sp) fs NX NX_spw (SINVg PHI sp STR0)
                    (AA_g NX STR0) (SA_g NX NX_ge PHI PHI_agree sp STR0) (ht_s t) (ht_T t) E1 R1 FULL1 model1 Hdom TL HC1') as HC2.
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
End Hop.

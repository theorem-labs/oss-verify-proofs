(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeTile SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_stage2_defs Sj_stage2_tapek Sj_tables2 Sj_stage2_exit Sj_stage2_arrc Sj_stage2_scend Sj_stage2_arrv Sj_stage2_arrb
  Sj_stage2_docend Sj_stage2_objc Sj_stage2_objb Sj_stage2_objf Sj_stage2_stra2 Sj_stage2_strb2 Sj_stage2_strc2 Sj_stage2_strd2
  Sj_stage2_atoma Sj_stage2_atomo Sj_stage2_entry Sj_stage2_rootc Sj_stage2_roott Sj_stage2_rootn Sj_stage2_rootf Sj_stage2_strr2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Lemma st_ext : forall s s' : st, k s = k s' -> depth s = depth s' -> W s = W s' -> sb s = sb s' -> scopes s = scopes s' -> s = s'.
Proof. intros [a b c d e] [a' b' c' d' e']; cbn; intros; subst; reflexivity. Qed.

Lemma string_ok_lt : forall bs idxs t d, S1OUT bs idxs -> (0 <= t <= n idxs)%Z -> string_ok bs idxs t d -> (0 <= d < blen bs)%Z.
Proof.
  intros bs idxs t d HS Ht (j & HC & HD). pose proof (closes_bounds _ _ _ HC). pose proof (off_range _ _ HS t Ht). lia.
Qed.

Definition occ (b : bool) : Z := if b then 91 else 123.

Section Main.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Variable Q : machine_state -> Prop.
  Notation G tws sbs := (s2_ghost E tws sbs).
  Notation INV := (Inv (e_bs E) (e_idxs E)).
  Notation STEP := (step (e_bs E) (e_idxs E)).
  Notation MU := (mu (e_idxs E)).
  Notation TINV := (TInvS ck_any).
  Notation TSTEP := (tstep (e_bs E) (e_idxs E) ck_any).

  Hypothesis KX : forall tws sbs, exit_k (G tws sbs) Q.

  Definition vexp (s : st) : Prop :=
    (0 <= k s <= e_n E)%Z /\ (1 <= W s <= k s + 1)%Z /\ (0 <= sb s)%Z /\ (3 * sb s <= 5 * e_off E (k s))%Z /\
    (depth s = Z.of_nat (length (scopes s)) /\ (depth s < MAXDEPTH)%Z) /\ Forall (fun sc => (1 <= snd sc < W s)%Z) (scopes s).

  Hypothesis NUMA : forall tws sbs s, vexp s -> Z.of_nat (length tws) = W s ->
    (forall v r, num_word v -> is_numstart (e_tok E (k s)) = true ->
       arrcont_k (G (tws ++ [v; r]) (sbs ++ [])) Q (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s))) ->
    arrnum_k (G tws sbs) Q s.
  Hypothesis NUMO : forall tws sbs s, vexp s -> Z.of_nat (length tws) = W s ->
    (forall v r, num_word v -> is_numstart (e_tok E (k s)) = true ->
       objcont_k (G (tws ++ [v; r]) (sbs ++ [])) Q (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s))) ->
    objnum_k (G tws sbs) Q s.

  Definition LABK (E' : s2env) (l : label) (s : st) : Prop :=
    match l with
    | ObjBegin => objbegin_k E' Q s
    | ObjField => objfield_k E' Q s
    | ObjCont => objcont_k E' Q s
    | ScopeEnd => scopeend_k E' Q s
    | ArrBegin => arrbegin_k E' Q s
    | ArrValue => arrvalue_k E' Q s
    | ArrCont => arrcont_k E' Q s
    | DocEnd => docend_k E' Q s
    | DocStart => True
    end.

  Definition GI (l : label) (s : st) (tws sbs cs : list Z) : Prop :=
    Z.of_nat (length tws) = W s /\ Z.of_nat (length sbs) = sb s /\ TINV l s (mkG (Tf tws) (Tf sbs) cs).

  Ltac by_state L :=
    repeat match goal with x := _ : st |- _ => subst x end;
    cbn [LABK] in L;
    lazymatch goal with |- ?f ?sG =>
      lazymatch type of L with ?g ?sL =>
        replace sG with sL by (apply st_ext; cbn [k depth W sb scopes]; first [reflexivity | lia]); exact L end end.

  Ltac env_of_goal := lazymatch goal with |- ?f ?Eg Q ?sx => Eg end.

  Ltac to_LABK l' sL :=
    unfold endc_env, empty_env, docend_env;
    let Eg := env_of_goal in
    let t := eval cbn [e_tws e_sbs gapp gpatch s2_ghost] in (e_tws Eg) in
    let u := eval cbn [e_tws e_sbs gapp gpatch s2_ghost] in (e_sbs Eg) in
    let LL := fresh "LL" in
    enough (LL : LABK (G t u) l' sL); [by_state LL|].

  Ltac lens := repeat match goal with x := _ : st |- _ => subst x end; unfold srec, le4z; repeat rewrite length_app; rewrite ?zupd_length; repeat rewrite length_app; cbn [length k depth W sb scopes s0]; lia.

  Ltac gn := cbn [e_bs e_idxs e_tcap e_scap e_lo e_sp e_tws e_sbs s2_ghost gapp gpatch] in *.
  Ltac gng := cbn [k depth W sb scopes e_bs e_idxs e_tcap e_scap e_lo e_sp e_tws e_sbs s2_ghost gapp gpatch].

  Theorem s2_labels : forall (N : nat) l s tws sbs cs, (MU l s < Z.of_nat N)%Z -> INV l s -> GI l s tws sbs cs -> LABK (G tws sbs) l s.
  Proof using OK KX NUMA NUMO.
    induction N as [|N IH]; intros l s tws sbs cs HMU HI HG.
    { pose proof (mu_nonneg _ _ _ _ HI). lia. }
    pose proof (ok_s1 _ OK) as HS1.
    pose proof (inv_k _ _ _ _ HI) as HK. pose proof (inv_W _ _ _ _ HI) as HW. pose proof (inv_sb _ _ _ _ HI) as [HSB0 HSB].
    pose proof (n_le_len _ _ HS1) as HNL. pose proof (ok_tcap _ OK) as [HTC _]. pose proof (ok_scap _ OK) as [HSC _].
    pose proof (ok_len _ OK) as HLEN. unfold S2_LEN_MAX in HLEN.
    assert (HL32 : (blen (e_bs E) + 3 < 2^32)%Z) by lia.
    assert (OK' : env_ok (G tws sbs)) by (apply env_ok_ghost; exact OK).
    destruct HG as (LT & LS & HT).

    assert (USg : forall l' s' tws' sbs' cs',
              TSTEP l s (mkG (Tf tws) (Tf sbs) cs) l' s' (mkG (Tf tws') (Tf sbs') cs') ->
              Z.of_nat (length tws') = W s' -> Z.of_nat (length sbs') = sb s' ->
              LABK (G tws' sbs') l' s').
    { intros l' s' tws' sbs' cs' ST L1 L2.
      pose proof (tstep_step _ _ _ _ _ _ _ _ _ ST) as ST0.
      apply (IH l' s' tws' sbs' cs').
      - pose proof (step_mu _ _ _ _ _ _ ST0). lia.
      - eapply step_inv; [exact HS1 | exact ST0 | exact HI].
      - split; [exact L1|]. split; [exact L2|]. exact (tstep_invS _ _ _ _ _ _ _ _ _ HI HT ST). }
    destruct l; cbn [LABK slackW slackS] in *.
    -   exact I.
    -
      unfold objbegin_k. intros. eapply (seg_obj_begin (G tws sbs) OK' Q s); [exact HI | eassumption | exact (KX _ _) | intros HD HQ]. gn.
      unfold keya_k. intros. eapply (seg_key_a (G tws sbs) OK' Q s);
        [exact HI | unfold MAXDEPTH; lia | exact HQ | eassumption | exact LT | exact LS | intros hv; exact (KX _ _) | intros d hv cb HSO HCB]. gn.
      pose proof (string_ok_lt _ _ (k s) d HS1 ltac:(gng; lia) HSO) as HD0.
      to_LABK ObjField (mkst (k s + 1) (depth s + 1) (W s + 2) (sb s + d + 5) ((false, W s) :: scopes s)).
      eapply USg; [ | lens | pose proof (srec_length d cb HCB); lens].
      apply (tst_obj_begin _ _ ck_any s (mkG (Tf tws) (Tf sbs) cs) _ _ d ltac:(unfold MAXDEPTH; lia) HQ HSO); cbn [gT gS gC]; rewrite ?app_nil_r.
      + apply frameT_app. exact LT.
      + apply frameS_app. exact LS.
      + rewrite (Tf_app_r _ _ (W s) 1%Z LT) by lia. reflexivity.
      + apply wrote_str_app; [exact LS | exact HCB | lia].
    -
      pose proof (inv_depth _ _ _ _ HI) as HDP. pose proof (inv_scopes _ _ _ _ HI) as HSCO.
      assert (COL : e_tok E (k s) = c_colon -> (k s + 1 <= e_n E)%Z /\ (3 * sb s <= 5 * e_off E (k s + 1))%Z).
      { intros HC. assert (k s < e_n E)%Z by (apply (tok_nonzero_lt (e_bs E)); [lia | rewrite HC; unfold c_colon; lia]).
        pose proof (off_add _ _ HS1 (k s) 1 ltac:(lia) ltac:(lia) ltac:(lia)) as HOA. lia. }
      set (sV := mkst (k s + 1) (depth s) (W s) (sb s) (scopes s)).
      assert (VE : e_tok E (k s) = c_colon -> vexp sV).
      { intros HC. destruct (COL HC) as [C1 C2]. unfold vexp, sV. cbn [k depth W sb scopes].
        split; [lia|]. split; [lia|]. split; [lia|]. split; [exact C2|]. split; [exact HDP | exact HSCO]. }
      unfold objfield_k. intros. eapply (seg_obj_field (G tws sbs) OK' Q s); [exact HI | eassumption | exact LT | exact (KX _ _) | ..].
      +
        intros HC HQ. gn. destruct (COL HC) as [C1 C2].
        assert (HKn : (k s + 1 < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E)); [lia | rewrite HQ; unfold c_quote; lia]).
        pose proof (inv_depth_range _ _ _ _ HI) as HDR.
        unfold objstr_k. intros. eapply (seg_str_c (G tws sbs) OK' Q sV); unfold sV; gng;
          [lia | split; lia | split; lia | exact HDR | exact HQ | eassumption | exact LT | exact LS | exact (KX _ _) | intros d' cb HSO HCB]. gn.
        to_LABK ObjCont (mkst (k sV + 1) (depth sV) (W sV + 1) (sb sV + d' + 5) (scopes sV)).
        eapply USg; [ | lens | pose proof (srec_length d' cb HCB); lens].
        apply (tst_obj_field _ _ _ s _ _ _ _ HC). apply tv_string; unfold sV; cbn [k depth W sb scopes gT gS gC]; rewrite ?app_nil_r;
          [exact HQ | exact HSO | apply frameT_app; exact LT | rewrite ?app_nil_r; apply frameS_app; exact LS
          | rewrite (Tf_app_r0 _ _ (W s) LT); reflexivity
          | rewrite ?app_nil_r; pose proof (string_ok_lt _ _ (k s + 1) d' HS1 ltac:(gng; lia) HSO); apply wrote_str_app; [exact LS | exact HCB | lia] ].
      +
        intros HC H1 H2. gn. replace (k s + 2)%Z with (k s + 1 + 1)%Z in H2 by lia.
        to_LABK ObjCont (mkst (k sV + 2) (depth sV) (W sV + 2) (sb sV) (scopes sV)).
        eapply USg; [ | lens | lens].
        apply (tst_obj_field _ _ _ s _ _ _ _ HC). apply (tv_arr_empty _ _ _ _ sV _ _ _ 0%Z); unfold sV; cbn [k depth W sb scopes gT gS gC]; rewrite ?app_nil_r;
          [exact H1 | exact H2 | apply frameT_app; exact LT | rewrite ?app_nil_r; apply frameS_refl
          | rewrite (Tf_app_r0 _ _ (W s) LT); reflexivity | unfold ck_any, CNT_MAX; lia
          | rewrite (Tf_app_r _ _ (W s) 1%Z LT) by lia; reflexivity ].
      +
        intros HC H1 H2. gn. replace (k s + 2)%Z with (k s + 1 + 1)%Z in H2 by lia.
        to_LABK ObjCont (mkst (k sV + 2) (depth sV) (W sV + 2) (sb sV) (scopes sV)).
        eapply USg; [ | lens | lens].
        apply (tst_obj_field _ _ _ s _ _ _ _ HC). apply (tv_obj_empty _ _ _ _ sV _ _ _ 0%Z); unfold sV; cbn [k depth W sb scopes gT gS gC]; rewrite ?app_nil_r;
          [exact H1 | exact H2 | apply frameT_app; exact LT | rewrite ?app_nil_r; apply frameS_refl
          | rewrite (Tf_app_r0 _ _ (W s) LT); reflexivity | unfold ck_any, CNT_MAX; lia
          | rewrite (Tf_app_r _ _ (W s) 1%Z LT) by lia; reflexivity ].
      +
        intros HC H1 H2. gn. replace (k s + 2)%Z with (k s + 1 + 1)%Z in H2 by lia.
        to_LABK ArrBegin (mkst (k sV + 1) (depth sV) (W sV) (sb sV) (scopes sV)).
        eapply USg; [ | lens | lens].
        apply (tst_obj_field _ _ _ s _ _ _ _ HC). apply tv_arr; unfold sV; cbn [k depth W sb scopes gT gS gC]; rewrite ?app_nil_r;
          [exact H1 | exact H2 | apply frameT_refl | apply frameS_refl].
      +
        intros HC H1 H2. gn. replace (k s + 2)%Z with (k s + 1 + 1)%Z in H2 by lia.
        to_LABK ObjBegin (mkst (k sV + 1) (depth sV) (W sV) (sb sV) (scopes sV)).
        eapply USg; [ | lens | lens].
        apply (tst_obj_field _ _ _ s _ _ _ _ HC). apply tv_obj; unfold sV; cbn [k depth W sb scopes gT gS gC]; rewrite ?app_nil_r;
          [exact H1 | exact H2 | apply frameT_refl | apply frameS_refl].
      +
        intros HC _ _ _ _. gn. apply (NUMO tws sbs _ (VE HC) ltac:(cbn [W]; exact LT)). unfold sV. cbn [k depth W sb scopes]. intros v r Hv HN. gn.
        to_LABK ObjCont (mkst (k sV + 1) (depth sV) (W sV + 2) (sb sV) (scopes sV)).
        eapply USg; [ | lens | lens].
        apply (tst_obj_field _ _ _ s _ _ _ _ HC). apply tv_number; unfold sV; cbn [k depth W sb scopes gT gS gC]; rewrite ?app_nil_r;
          [exact HN | apply frameT_app; exact LT | rewrite ?app_nil_r; apply frameS_refl | rewrite (Tf_app_r0 _ _ (W s) LT); exact Hv].
      +
        intros HC _ _ _ _. gn. destruct (COL HC) as [C1 C2].
        unfold objatom_k. intros. eapply (seg_atoms_o (G tws sbs) OK' Q sV); unfold sV; gng; [lia | split; lia | eassumption | exact LT | exact (KX _ _) | intros v Hv HA]. gn.
        to_LABK ObjCont (mkst (k sV + 1) (depth sV) (W sV + 1) (sb sV) (scopes sV)).
        eapply USg; [ | lens | lens].
        apply (tst_obj_field _ _ _ s _ _ _ _ HC). apply tv_atom; unfold sV; cbn [k depth W sb scopes gT gS gC]; rewrite ?app_nil_r;
          [exact HA | apply frameT_app; exact LT | rewrite ?app_nil_r; apply frameS_refl | rewrite (Tf_app_r0 _ _ (W s) LT); exact Hv].
    -
      destruct (tinv_counts_cons _ _ _ _ _ _ HI (TInvS_TInv _ _ _ _ HT) ltac:(left; reflexivity)) as (c & cs0 & HCS). cbn [gC] in HCS. subst cs.
      unfold objcont_k. intros. eapply (seg_obj_cont (G tws sbs) OK' Q s); [exact HI | eassumption | exact LT | exact (KX _ _) | intros HT1 HT2 | intros cv ti rest ESC Hcv HT1]; gn.
      +
        unfold keyb_k. intros. eapply (seg_key_b (G tws sbs) OK' Q _ s);
          [exact HI | exact HT1 | exact HT2 | reflexivity | eassumption | exact LT | exact LS | exact (KX _ _) | intros d cb HSO HCB]. gn.
        assert (HKn0 : (k s < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E)); [lia | rewrite HT1; unfold c_comma; lia]).
        pose proof (string_ok_lt _ _ (k s + 1) d HS1 ltac:(gng; lia) HSO) as HD0.
        to_LABK ObjField (mkst (k s + 2) (depth s) (W s + 1) (sb s + d + 5) (scopes s)).
        eapply USg; [ | lens | pose proof (srec_length d cb HCB); lens].
        apply (tst_obj_cont_comma _ _ ck_any s (mkG (Tf tws) (Tf sbs) (c :: cs0)) _ _ d c cs0 HT1 HT2 HSO); cbn [gT gS gC]; rewrite ?app_nil_r.
        * apply frameT_app. exact LT.
        * apply frameS_app. exact LS.
        * rewrite (Tf_app_r0 _ _ (W s) LT). reflexivity.
        * apply wrote_str_app; [exact LS | exact HCB | lia].
        * reflexivity.
      +
        pose proof (inv_scopes _ _ _ _ HI) as HSCS. rewrite ESC in HSCS. pose proof (Forall_inv HSCS) as HTI. cbn [snd] in HTI.
        to_LABK ScopeEnd (mkst (k s + 1) (depth s) (W s + 1) (sb s) (scopes s)).
        eapply USg; [ | lens | lens].
        apply (tst_obj_cont_end _ _ ck_any s (mkG (Tf tws) (Tf sbs) (c :: cs0)) _ _ ti rest c cs0 cv HT1 ESC eq_refl); cbn [gT gS gC]; rewrite ?app_nil_r.
        * apply frameTx_zupd_app; [exact LT | lia].
        * rewrite ?app_nil_r. apply frameS_refl.
        * rewrite (Tf_zupd_app_r0 _ _ (W s)) by exact LT. reflexivity.
        * rewrite Tf_zupd_app_same by lia. reflexivity.
        * exact Hcv.
    -
      unfold scopeend_k. intros. eapply (seg_scope_end (G tws sbs) OK' Q s); [exact HI | eassumption | intros sc0 HS0 | intros sc0 ti rest HS0 | intros sc0 ti rest HS0]; gn.
      + to_LABK DocEnd (mkst (k s) (depth s - 1) (W s) (sb s) []).
        eapply USg; [ | lens | lens].
        apply (tst_scope_end_doc _ _ _ s _ _ _ sc0 HS0); cbn [gT gS gC]; rewrite ?app_nil_r; [apply frameT_refl | apply frameS_refl].
      + to_LABK ArrCont (mkst (k s) (depth s - 1) (W s) (sb s) ((true, ti) :: rest)).
        eapply USg; [ | lens | lens].
        apply (tst_scope_end_arr _ _ _ s _ _ _ sc0 ti rest HS0); cbn [gT gS gC]; rewrite ?app_nil_r; [apply frameT_refl | apply frameS_refl].
      + to_LABK ObjCont (mkst (k s) (depth s - 1) (W s) (sb s) ((false, ti) :: rest)).
        eapply USg; [ | lens | lens].
        apply (tst_scope_end_obj _ _ _ s _ _ _ sc0 ti rest HS0); cbn [gT gS gC]; rewrite ?app_nil_r; [apply frameT_refl | apply frameS_refl].
    -
      unfold arrbegin_k. intros. eapply (seg_arr_begin (G tws sbs) OK' Q s); [exact HI | eassumption | exact (KX _ _) | intros HD]. gn.
      apply (arrvalue_k_hole (G tws sbs) Q); [exact OK' | cbn [e_tws e_tcap s2_ghost]; lia | intros h].
      to_LABK ArrValue (mkst (k s) (depth s + 1) (W s + 1) (sb s) ((true, W s) :: scopes s)).
      eapply USg; [ | lens | lens].
      apply tst_arr_begin; cbn [gT gS gC]; rewrite ?app_nil_r; [unfold MAXDEPTH; lia | apply frameT_app; exact LT | rewrite ?app_nil_r; apply frameS_refl].
    -
      assert (HV : vexp s).
      { unfold vexp. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact (inv_depth _ _ _ _ HI) | exact (inv_scopes _ _ _ _ HI)]. }
      unfold arrvalue_k. intros. eapply (seg_arr_value (G tws sbs) OK' Q s); [exact HI | eassumption | exact LT | exact (KX _ _) | ..].
      +
        intros HQ. gn.
        assert (HKn : (k s < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E)); [lia | rewrite HQ; unfold c_quote; lia]).
        unfold arrstr_k. intros. eapply (seg_str_d (G tws sbs) OK' Q s); [exact HI | exact HQ | eassumption | exact LT | exact LS | exact (KX _ _) | intros d cb HSO HCB]. gn.
        to_LABK ArrCont (mkst (k s + 1) (depth s) (W s + 1) (sb s + d + 5) (scopes s)).
        eapply USg; [ | lens | pose proof (srec_length d cb HCB); lens].
        apply tst_arr_value. apply tv_string; cbn [gT gS gC]; rewrite ?app_nil_r;
          [exact HQ | exact HSO | apply frameT_app; exact LT | rewrite ?app_nil_r; apply frameS_app; exact LS
          | rewrite (Tf_app_r0 _ _ (W s) LT); reflexivity
          | rewrite ?app_nil_r; pose proof (string_ok_lt _ _ (k s) d HS1 ltac:(gng; lia) HSO); apply wrote_str_app; [exact LS | exact HCB | lia] ].
      + intros H1 H2. gn.
        to_LABK ArrCont (mkst (k s + 2) (depth s) (W s + 2) (sb s) (scopes s)).
        eapply USg; [ | lens | lens].
        apply tst_arr_value. apply (tv_arr_empty _ _ _ _ s _ _ _ 0%Z); cbn [gT gS gC]; rewrite ?app_nil_r;
          [exact H1 | exact H2 | apply frameT_app; exact LT | rewrite ?app_nil_r; apply frameS_refl
          | rewrite (Tf_app_r0 _ _ (W s) LT); reflexivity | unfold ck_any, CNT_MAX; lia
          | rewrite (Tf_app_r _ _ (W s) 1%Z LT) by lia; reflexivity ].
      + intros H1 H2. gn.
        to_LABK ArrCont (mkst (k s + 2) (depth s) (W s + 2) (sb s) (scopes s)).
        eapply USg; [ | lens | lens].
        apply tst_arr_value. apply (tv_obj_empty _ _ _ _ s _ _ _ 0%Z); cbn [gT gS gC]; rewrite ?app_nil_r;
          [exact H1 | exact H2 | apply frameT_app; exact LT | rewrite ?app_nil_r; apply frameS_refl
          | rewrite (Tf_app_r0 _ _ (W s) LT); reflexivity | unfold ck_any, CNT_MAX; lia
          | rewrite (Tf_app_r _ _ (W s) 1%Z LT) by lia; reflexivity ].
      + intros H1 H2. gn.
        to_LABK ArrBegin (mkst (k s + 1) (depth s) (W s) (sb s) (scopes s)).
        eapply USg; [ | lens | lens].
        apply tst_arr_value. apply tv_arr; cbn [gT gS gC]; rewrite ?app_nil_r; [exact H1 | exact H2 | apply frameT_refl | apply frameS_refl].
      + intros H1 H2. gn.
        to_LABK ObjBegin (mkst (k s + 1) (depth s) (W s) (sb s) (scopes s)).
        eapply USg; [ | lens | lens].
        apply tst_arr_value. apply tv_obj; cbn [gT gS gC]; rewrite ?app_nil_r; [exact H1 | exact H2 | apply frameT_refl | apply frameS_refl].
      + intros _ _ _ _. apply (NUMA tws sbs s HV LT). intros v r Hv HN. gn.
        to_LABK ArrCont (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s)).
        eapply USg; [ | lens | lens].
        apply tst_arr_value. apply tv_number; cbn [gT gS gC]; rewrite ?app_nil_r;
          [exact HN | apply frameT_app; exact LT | rewrite ?app_nil_r; apply frameS_refl | rewrite (Tf_app_r0 _ _ (W s) LT); exact Hv].
      + intros _ _ _ _. unfold arratom_k. intros. eapply (seg_atoms_a (G tws sbs) OK' Q s); gng; [lia | split; lia | eassumption | exact LT | exact (KX _ _) | intros v Hv HA]. gn.
        to_LABK ArrCont (mkst (k s + 1) (depth s) (W s + 1) (sb s) (scopes s)).
        eapply USg; [ | lens | lens].
        apply tst_arr_value. apply tv_atom; cbn [gT gS gC]; rewrite ?app_nil_r;
          [exact HA | apply frameT_app; exact LT | rewrite ?app_nil_r; apply frameS_refl | rewrite (Tf_app_r0 _ _ (W s) LT); exact Hv].
    -
      destruct (tinv_counts_cons _ _ _ _ _ _ HI (TInvS_TInv _ _ _ _ HT) ltac:(right; reflexivity)) as (c & cs0 & HCS). cbn [gC] in HCS. subst cs.
      unfold arrcont_k. intros. eapply (seg_arr_cont (G tws sbs) OK' Q s); [exact HI | eassumption | exact LT | exact (KX _ _) | intros HT1 | intros cv ti rest ESC Hcv HT1]; gn.
      + to_LABK ArrValue (mkst (k s + 1) (depth s) (W s) (sb s) (scopes s)).
        eapply USg; [ | lens | lens].
        apply (tst_arr_cont_comma _ _ _ s _ _ _ c cs0 HT1); cbn [gT gS gC]; rewrite ?app_nil_r; [apply frameT_refl | apply frameS_refl | reflexivity].
      +
        pose proof (inv_scopes _ _ _ _ HI) as HSCS. rewrite ESC in HSCS. pose proof (Forall_inv HSCS) as HTI. cbn [snd] in HTI.
        to_LABK ScopeEnd (mkst (k s + 1) (depth s) (W s + 1) (sb s) (scopes s)).
        eapply USg; [ | lens | lens].
        apply (tst_arr_cont_end _ _ ck_any s (mkG (Tf tws) (Tf sbs) (c :: cs0)) _ _ ti rest c cs0 cv HT1 ESC eq_refl); cbn [gT gS gC]; rewrite ?app_nil_r.
        * apply frameTx_zupd_app; [exact LT | lia].
        * rewrite ?app_nil_r. apply frameS_refl.
        * rewrite (Tf_zupd_app_r0 _ _ (W s)) by exact LT. reflexivity.
        * rewrite Tf_zupd_app_same by lia. reflexivity.
        * exact Hcv.
    -
      unfold docend_k. intros. eapply (seg_doc_end (G tws sbs) OK' Q s); [exact HI | eassumption | exact LT | exact (KX _ _) |].
      unfold docend_env, tape_ok. gng. rewrite ?app_nil_r.
      replace (Z.of_nat (length (zupd (tws ++ [tword t_root 0]) (Z.to_nat 0) (tword t_root (W s + 1))))) with (W s + 1)%Z by lens.
      rewrite LS.
      apply (docend_tape_wfS _ _ HS1 HL32 ck_any s (mkG (Tf tws) (Tf sbs) cs)); cbn [gT gS gC]; rewrite ?app_nil_r.
      + exact HI. + exact HT.
      + intros x Hx. rewrite Tf_zupd_other by lia. apply Tf_app_l. lia.
      + rewrite Tf_zupd_other by lia. rewrite (Tf_app_r0 _ _ (W s) LT). reflexivity.
      + apply Tf_zupd_same. lens.
  Qed.

  Variable h0 : Z.
  Notation E0 := (G [h0] []).
  Hypothesis ROOTNUM : is_numstart (e_tok E 0) = true -> rootprim_k E0 Q 0x43874.

  Lemma first_step : forall l' s' tws' sbs' cs',
    TSTEP DocStart s0 (mkG (Tf [h0]) (Tf []) []) l' s' (mkG (Tf tws') (Tf sbs') cs') ->
    Z.of_nat (length tws') = W s' -> Z.of_nat (length sbs') = sb s' ->
    LABK (G tws' sbs') l' s'.
  Proof using OK KX NUMA NUMO.
    intros l' s' tws' sbs' cs' ST L1 L2.
    pose proof (ok_s1 _ OK) as HS1.
    pose proof (tstep_step _ _ _ _ _ _ _ _ _ ST) as ST0.
    assert (HI : INV l' s') by (eapply step_inv; [exact HS1 | exact ST0 | apply Inv_s0; exact HS1]).
    apply (s2_labels (S (Z.to_nat (MU l' s'))) l' s' tws' sbs' cs'); [lia | exact HI |].
    split; [exact L1|]. split; [exact L2|].
    exact (tstep_invS _ _ _ _ _ _ _ _ _ (Inv_s0 _ _ HS1) (TInvS_s0 ck_any (Tf [h0]) (Tf [])) ST).
  Qed.

  Ltac to_LABK0 l' sL :=
    unfold endc_env, empty_env, docend_env;
    let Eg := env_of_goal in
    let t := eval cbn [e_tws e_sbs gapp gpatch s2_ghost] in (e_tws Eg) in
    let u := eval cbn [e_tws e_sbs gapp gpatch s2_ghost] in (e_sbs Eg) in
    let LL := fresh "LL" in
    enough (LL : LABK (G t u) l' sL);
    [ cbn [LABK] in LL;
      lazymatch goal with |- ?f ?sG =>
        lazymatch type of LL with ?g ?sL' =>
          replace sG with sL' by (apply st_ext; cbn [k depth W sb scopes]; first [reflexivity | lia]); exact LL end end
    | ].

  Theorem s2_main : forall docv x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEM0 E0 docv fc m1 ->
    evt usegs Q
      (MS (mkR (e_ra E) (e_sp E) (e_gp E) (e_tp E) x5 x6 x7 (e_s0 E) (e_s1 E) (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (e_DOC E)) x12 x13 x14 x15 x16 x17
               (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E) x28 x29 x30 x31)
          F (Z_to_bv 64 0x43550) fc None m1 (seg_rom usegs)).
  Proof using OK KX NUMA NUMO ROOTNUM.
    intros docv x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m1 HM.
    pose proof (ok_s1 _ OK) as HS1. pose proof (n_le_len _ _ HS1) as HNL. pose proof (ok_len _ OK) as HLEN. unfold S2_LEN_MAX in HLEN.
    pose proof (ok_tcap _ OK) as [HTC _].
    assert (OK0 : env_ok E0) by (apply env_ok_ghost; exact OK).
    assert (L1 : Z.of_nat (length (e_tws E0)) = 1%Z) by reflexivity.
    assert (ATOM : forall c v, e_tok E 0 = c -> is_atomstart c = true -> atom_word v -> docend_k (G ([h0] ++ [v]) ([] ++ [])) Q (mkst 1 0 2 0 [])).
    { intros c v HT HA Hv. gn. rewrite <- HT in HA.
      to_LABK0 DocEnd (mkst (k s0 + 1) (depth s0) (W s0 + 1) (sb s0) (scopes s0)).
      eapply first_step; [ | reflexivity | reflexivity].
      apply tst_doc. apply tv_atom; cbn [gT gS gC]; rewrite ?app_nil_r; [exact HA | apply (frameT_app [h0]); reflexivity | apply frameS_refl | ].
      cbn [k W sb depth scopes s0]. rewrite (Tf_app_r0 [h0] [v] 1%Z) by reflexivity. exact Hv. }
    apply (seg_entry E0 OK0 Q docv x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m1 HM (KX _ _)).
    intros pc HPC HNX. unfold root_target in HPC. gn.
    destruct (e_tok E 0 =? 34)%Z eqn:T34.
    { apply Z.eqb_eq in T34. subst pc. unfold rootprim_k. intros.
      eapply (seg_root_str E0 OK0 Q); [exact T34 | eassumption | exact L1 | reflexivity | exact (KX _ _) | intros d cb HSO HCB]. gn.
      to_LABK0 DocEnd (mkst (k s0 + 1) (depth s0) (W s0 + 1) (sb s0 + d + 5) (scopes s0)).
      eapply first_step; [ | reflexivity | lens].
      apply tst_doc. apply tv_string; cbn [gT gS gC]; rewrite ?app_nil_r;
        [exact T34 | exact HSO | rewrite ?app_nil_r; apply (frameT_app [h0]); reflexivity | cbn [app]; apply (frameS_app [] (srec d cb) 0%Z); reflexivity
        | rewrite ?app_nil_r; cbn [k W sb depth scopes s0]; rewrite (Tf_app_r0 [h0] _ 1%Z) by reflexivity; reflexivity
        | cbn [k W sb depth scopes s0 app]; pose proof (string_ok_lt _ _ 0%Z d HS1 ltac:(pose proof (n_pos _ _ HS1); lia) HSO); apply (wrote_str_app []); [reflexivity | exact HCB | lia] ]. }
    destruct ((e_tok E 0 =? 45) || (48 <=? e_tok E 0) && (e_tok E 0 <=? 57))%Z eqn:TNUM.
    { subst pc. exact (ROOTNUM TNUM). }
    destruct (e_tok E 0 =? 91)%Z eqn:T91.
    { apply Z.eqb_eq in T91. subst pc. unfold rootprim_k. intros.
      eapply (seg_root_arr E0 OK0 Q); [exact T91 | eassumption | exact L1 | exact (KX _ _) | intros H2 | intros H2]; gn.
      - to_LABK0 ArrBegin (mkst (k s0 + 1) (depth s0) (W s0) (sb s0) (scopes s0)).
        eapply first_step; [ | reflexivity | reflexivity].
        apply tst_doc. apply tv_arr; cbn [gT gS gC]; rewrite ?app_nil_r; [exact T91 | exact H2 | apply frameT_refl | apply frameS_refl].
      - to_LABK0 DocEnd (mkst (k s0 + 2) (depth s0) (W s0 + 2) (sb s0) (scopes s0)).
        eapply first_step; [ | reflexivity | reflexivity].
        apply tst_doc. apply (tv_arr_empty _ _ _ _ s0 _ _ _ 0%Z); cbn [gT gS gC]; rewrite ?app_nil_r; cbn [k W sb depth scopes s0];
          [exact T91 | exact H2 | apply (frameT_app [h0]); reflexivity | apply frameS_refl
          | rewrite (Tf_app_r0 [h0] _ 1%Z) by reflexivity; reflexivity | unfold ck_any, CNT_MAX; lia
          | rewrite (Tf_app_r [h0] _ 1%Z 1%Z) by (cbn; lia); reflexivity ]. }
    destruct (e_tok E 0 =? 102)%Z eqn:T102.
    { apply Z.eqb_eq in T102. subst pc. unfold rootprim_k. intros.
      eapply (seg_root_f E0 OK0 Q); [eassumption | exact L1 | exact (KX _ _) | apply (ATOM _ _ T102); [reflexivity | right; left; reflexivity]]. }
    destruct (e_tok E 0 =? 110)%Z eqn:T110.
    { apply Z.eqb_eq in T110. subst pc. unfold rootprim_k. intros.
      eapply (seg_root_n E0 OK0 Q); [eassumption | exact L1 | exact (KX _ _) | apply (ATOM _ _ T110); [reflexivity | right; right; reflexivity]]. }
    destruct (e_tok E 0 =? 116)%Z eqn:T116.
    { apply Z.eqb_eq in T116. subst pc. unfold rootprim_k. intros.
      eapply (seg_root_t E0 OK0 Q); [eassumption | exact L1 | exact (KX _ _) | apply (ATOM _ _ T116); [reflexivity | left; reflexivity]]. }
    destruct (e_tok E 0 =? 123)%Z eqn:T123.
    { apply Z.eqb_eq in T123. subst pc. unfold rootprim_k. intros.
      eapply (seg_root_obj E0 OK0 Q); [exact T123 | eassumption | exact L1 | exact (KX _ _) | intros H2 | intros H2]; gn.
      - to_LABK0 ObjBegin (mkst (k s0 + 1) (depth s0) (W s0) (sb s0) (scopes s0)).
        eapply first_step; [ | reflexivity | reflexivity].
        apply tst_doc. apply tv_obj; cbn [gT gS gC]; rewrite ?app_nil_r; [exact T123 | exact H2 | apply frameT_refl | apply frameS_refl].
      - to_LABK0 DocEnd (mkst (k s0 + 2) (depth s0) (W s0 + 2) (sb s0) (scopes s0)).
        eapply first_step; [ | reflexivity | reflexivity].
        apply tst_doc. apply (tv_obj_empty _ _ _ _ s0 _ _ _ 0%Z); cbn [gT gS gC]; rewrite ?app_nil_r; cbn [k W sb depth scopes s0];
          [exact T123 | exact H2 | apply (frameT_app [h0]); reflexivity | apply frameS_refl
          | rewrite (Tf_app_r0 [h0] _ 1%Z) by reflexivity; reflexivity | unfold ck_any, CNT_MAX; lia
          | rewrite (Tf_app_r [h0] _ 1%Z 1%Z) by (cbn; lia); reflexivity ]. }
    congruence.
  Qed.
End Main.


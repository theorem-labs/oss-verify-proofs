(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeTile SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_arrc Sj_stage2_scend Sj_stage2_objc Sj_stage2_arrb Sj_stage2_docend
  Sj_stage2_arrv Sj_stage2_objb Sj_stage2_objf Sj_stage2_atoma Sj_stage2_atomo.
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
  Variable E0 : s2env.
  Hypothesis OK0 : env_ok E0.
  Variable WD : Type.
  Variable wm : WD -> mem.
  Variable wQ : WD -> machine_state -> Prop.
  Variable good : WD -> Z -> Prop.
  Definition wE (w : WD) : s2env := env_at E0 (wm w).
  Notation G w tws sbs := (s2_ghost (wE w) tws sbs).
  Hypothesis good_shz : forall w kk, good w kk -> a_shz (wE w).
  Hypothesis good_mono : forall w kk kk', good w kk -> (kk <= kk')%Z -> good w kk'.

  Hypothesis KX : forall w kk tws sbs, good w kk -> exit_k (G w tws sbs) (wQ w).
  Notation INV := (Inv (e_bs E0) (e_idxs E0)).
  Notation STEP := (step (e_bs E0) (e_idxs E0)).
  Notation MU := (mu (e_idxs E0)).
  Notation tk := (e_tok E0).
  Notation TINV := (TInvS ck_any).
  Notation TSTEP := (tstep (e_bs E0) (e_idxs E0) ck_any).

  Definition vexp (s : st) : Prop :=
    (0 <= k s <= e_n E0)%Z /\ (1 <= W s <= k s + 1)%Z /\ (0 <= sb s)%Z /\ (3 * sb s <= 5 * e_off E0 (k s))%Z /\
    (depth s = Z.of_nat (length (scopes s)) /\ (depth s < MAXDEPTH)%Z) /\ Forall (fun sc => (1 <= snd sc < W s)%Z) (scopes s).

  Hypothesis NUMA : forall w s (tws sbs : list Z), good w (k s) -> vexp s -> Z.of_nat (length tws) = W s ->
    (is_numstart (tk (k s)) = true -> forall w' v r, good w' (k s + 1) -> num_word v ->
       arrcont_k (G w' (tws ++ [v; r]) (sbs ++ [])) (wQ w') (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s))) ->
    arrnum_k (G w tws sbs) (wQ w) s.
  Hypothesis NUMO : forall w s (tws sbs : list Z), good w (k s) -> vexp s -> Z.of_nat (length tws) = W s ->
    (is_numstart (tk (k s)) = true -> forall w' v r, good w' (k s + 1) -> num_word v ->
       objcont_k (G w' (tws ++ [v; r]) (sbs ++ [])) (wQ w') (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s))) ->
    objnum_k (G w tws sbs) (wQ w) s.

  Hypothesis STR_KEYA : forall E Q s, env_ok E -> a_shz E -> Inv (e_bs E) (e_idxs E) ObjBegin s -> (depth s + 1 < MAXDEPTH)%Z ->
    e_tok E (k s) = c_quote -> Z.of_nat (length (e_tws E)) = W s -> Z.of_nat (length (e_sbs E)) = sb s ->
    (forall hv, exit_k (gapp E [hv; tword t_str (sb s)] []) Q) ->
    (forall d hv cb, string_ok (e_bs E) (e_idxs E) (k s) d -> Z.of_nat (length cb) = d ->
       keyend_k (gapp (gapp E [hv; tword t_str (sb s)] []) [] (srec d cb)) Q (k s) (depth s + 1) (W s + 2) (sb s) d ((false, W s) :: scopes s)) ->
    keya_k E Q s.
  Hypothesis STR_KEYB : forall E Q s0, env_ok E -> a_shz E -> Inv (e_bs E) (e_idxs E) ObjCont s0 ->
    e_tok E (k s0) = c_comma -> e_tok E (k s0 + 1) = c_quote -> Z.of_nat (length (e_tws E)) = W s0 -> Z.of_nat (length (e_sbs E)) = sb s0 ->
    exit_k (gapp E [tword t_str (sb s0)] []) Q ->
    (forall d cb, string_ok (e_bs E) (e_idxs E) (k s0 + 1) d -> Z.of_nat (length cb) = d ->
       keyend_k (gapp (gapp E [tword t_str (sb s0)] []) [] (srec d cb)) Q (k s0 + 1) (depth s0) (W s0 + 1) (sb s0) d (scopes s0)) ->
    keyb_k E Q (mkst (k s0 + 1) (depth s0) (W s0) (sb s0) (scopes s0)).
  Hypothesis STR_O : forall E Q s, env_ok E -> a_shz E ->
    (0 <= k s < e_n E)%Z -> (1 <= W s /\ W s + 1 <= e_tcap E)%Z -> (0 <= sb s /\ 3 * sb s <= 5 * e_off E (k s))%Z -> (0 <= depth s <= 1023)%Z ->
    e_tok E (k s) = c_quote -> Z.of_nat (length (e_tws E)) = W s -> Z.of_nat (length (e_sbs E)) = sb s ->
    exit_k (gapp E [tword t_str (sb s)] []) Q ->
    (forall d cb, string_ok (e_bs E) (e_idxs E) (k s) d -> Z.of_nat (length cb) = d ->
       objcont_k (gapp (gapp E [tword t_str (sb s)] []) [] (srec d cb)) Q (mkst (k s + 1) (depth s) (W s + 1) (sb s + d + 5) (scopes s))) ->
    objstr_k E Q s.
  Hypothesis STR_A : forall E Q s, env_ok E -> a_shz E -> Inv (e_bs E) (e_idxs E) ArrValue s ->
    e_tok E (k s) = c_quote -> Z.of_nat (length (e_tws E)) = W s -> Z.of_nat (length (e_sbs E)) = sb s ->
    exit_k (gapp E [tword t_str (sb s)] []) Q ->
    (forall d cb, string_ok (e_bs E) (e_idxs E) (k s) d -> Z.of_nat (length cb) = d ->
       arrcont_k (gapp (gapp E [tword t_str (sb s)] []) [] (srec d cb)) Q (mkst (k s + 1) (depth s) (W s + 1) (sb s + d + 5) (scopes s))) ->
    arrstr_k E Q s.

  Definition LABK (w : WD) (tws sbs : list Z) (l : label) (s : st) : Prop :=
    match l with
    | ObjBegin => objbegin_k (G w tws sbs) (wQ w) s
    | ObjCont => objcont_k (G w tws sbs) (wQ w) s
    | ScopeEnd => scopeend_k (G w tws sbs) (wQ w) s
    | ArrBegin => arrbegin_k (G w tws sbs) (wQ w) s
    | ArrValue => arrvalue_k (G w tws sbs) (wQ w) s
    | ArrCont => arrcont_k (G w tws sbs) (wQ w) s
    | DocEnd => docend_k (G w tws sbs) (wQ w) s
    | ObjField => forall kk dpt Wv sbv d sc, s = mkst (kk + 1) dpt Wv (sbv + d + 5) sc -> (0 <= sbv)%Z -> (0 <= d)%Z ->
                    keyend_k (G w tws sbs) (wQ w) kk dpt Wv sbv d sc
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

  Ltac env_of_goal :=
    lazymatch goal with
    | |- keyend_k ?Eg _ _ _ _ _ _ _ => Eg
    | |- _ ?Eg _ _ => Eg
    end.

  Ltac to_LABK w' l' sL :=
    unfold endc_env, empty_env, docend_env;
    let Eg := env_of_goal in
    let t := eval cbn [e_tws e_sbs gapp gpatch s2_ghost] in (e_tws Eg) in
    let u := eval cbn [e_tws e_sbs gapp gpatch s2_ghost] in (e_sbs Eg) in
    let LL := fresh "LL" in
    enough (LL : LABK w' t u l' sL); [by_state LL|].

  Ltac to_LABKF w' sL :=
    unfold endc_env, empty_env, docend_env;
    let Eg := env_of_goal in
    let t := eval cbn [e_tws e_sbs gapp gpatch s2_ghost] in (e_tws Eg) in
    let u := eval cbn [e_tws e_sbs gapp gpatch s2_ghost] in (e_sbs Eg) in
    let LL := fresh "LL" in
    enough (LL : LABK w' t u ObjField sL);
    [ cbn [LABK] in LL; repeat match goal with x := _ : st |- _ => subst x end;
      apply LL; [apply st_ext; cbn [k depth W sb scopes]; first [reflexivity | lia] | lia | lia] | ].

  Ltac lens := repeat match goal with x := _ : st |- _ => subst x end; unfold srec, le4z; repeat rewrite length_app; rewrite ?zupd_length; repeat rewrite length_app; cbn [length k depth W sb scopes s0]; lia.

  Ltac gn := unfold wE in *; cbn [e_bs e_idxs e_tcap e_scap e_lo e_sp e_tws e_sbs s2_ghost gapp gpatch env_at] in *.
  Ltac gng := unfold wE; cbn [k depth W sb scopes e_bs e_idxs e_tcap e_scap e_lo e_sp e_tws e_sbs s2_ghost gapp gpatch env_at].

  Theorem s2_labels : forall (N : nat) l s w tws sbs cs, good w (k s) -> (MU l s < Z.of_nat N)%Z -> INV l s -> GI l s tws sbs cs -> LABK w tws sbs l s.
  Proof using OK0 good_shz good_mono KX NUMA NUMO STR_KEYA STR_KEYB STR_O STR_A.
    induction N as [|N IH]; intros l s w tws sbs cs HG HMU HI HGI.
    { pose proof (mu_nonneg _ _ _ _ HI). lia. }
    pose proof (ok_s1 _ OK0) as HS1.
    pose proof (env_at_ok E0 (wm w) OK0) as OK. fold (wE w) in OK. pose proof (good_shz w _ HG) as SHZ.
    assert (OK' : env_ok (G w tws sbs)) by (apply env_ok_ghost; exact OK).
    assert (KXw : forall tws' sbs', exit_k (G w tws' sbs') (wQ w)) by (intros; exact (KX w _ _ _ HG)).
    pose proof (inv_k _ _ _ _ HI) as HK. pose proof (inv_W _ _ _ _ HI) as HW. pose proof (inv_sb _ _ _ _ HI) as [HSB0 HSB].
    pose proof (n_le_len _ _ HS1) as HNL. pose proof (ok_tcap _ OK0) as [HTC _]. pose proof (ok_scap _ OK0) as [HSC _].
    pose proof (ok_len _ OK0) as HLEN. unfold S2_LEN_MAX in HLEN.
    assert (HL32 : (blen (e_bs E0) + 3 < 2^32)%Z) by lia.
    assert (GM : forall kk', (k s <= kk')%Z -> good w kk') by (intros kk' Hk; exact (good_mono w _ _ HG Hk)).
    destruct HGI as (LT & LS & HT).

    assert (USg : forall w' l' s' tws' sbs' cs',
              TSTEP l s (mkG (Tf tws) (Tf sbs) cs) l' s' (mkG (Tf tws') (Tf sbs') cs') ->
              Z.of_nat (length tws') = W s' -> Z.of_nat (length sbs') = sb s' -> good w' (k s') ->
              LABK w' tws' sbs' l' s').
    { intros w' l' s' tws' sbs' cs' ST L1 L2 HG'.
      pose proof (tstep_step _ _ _ _ _ _ _ _ _ ST) as ST0.
      apply (IH l' s' w' tws' sbs' cs' HG').
      - pose proof (step_mu _ _ _ _ _ _ ST0). lia.
      - eapply step_inv; [exact HS1 | exact ST0 | exact HI].
      - split; [exact L1|]. split; [exact L2|]. exact (tstep_invS _ _ _ _ _ _ _ _ _ HI HT ST). }
    destruct l; cbn [LABK slackW slackS] in *.
    -   exact I.
    -
      unfold objbegin_k. intros. eapply (seg_obj_begin (G w tws sbs) OK' SHZ (wQ w) s); [eassumption | exact HI | exact (KXw _ _) | intros HD HQ]. gn.
      apply (STR_KEYA (G w tws sbs) (wQ w) s OK' SHZ HI ltac:(unfold MAXDEPTH; lia) HQ LT LS); [intros hv; exact (KXw _ _)|].
      intros d hv cb HSO HCB. gn.
      pose proof (string_ok_lt _ _ (k s) d HS1 ltac:(gng; lia) HSO) as HD0.
      to_LABKF w (mkst (k s + 1) (depth s + 1) (W s + 2) (sb s + d + 5) ((false, W s) :: scopes s)).
      eapply USg; [ | lens | pose proof (srec_length d cb HCB); lens | apply GM; lens].
      apply (tst_obj_begin _ _ ck_any s (mkG (Tf tws) (Tf sbs) cs) _ _ d ltac:(unfold MAXDEPTH; lia) HQ HSO); cbn [gT gS gC]; rewrite ?app_nil_r.
      + apply frameT_app. exact LT.
      + apply frameS_app. exact LS.
      + rewrite (Tf_app_r _ _ (W s) 1%Z LT) by lia. reflexivity.
      + apply wrote_str_app; [exact LS | exact HCB | lia].
    -
      intros kk dpt Wv sbv d sc -> HSBV HD0. cbn [k depth W sb scopes] in *.
      pose proof (inv_depth _ _ _ _ HI) as HDP. pose proof (inv_scopes _ _ _ _ HI) as HSCO. cbn [k depth W sb scopes] in HDP, HSCO.
      pose proof (off_range _ _ HS1 (kk + 1) HK) as HOR.
      assert (HSCAP : (sbv + d + 5 <= e_scap E0)%Z) by lia.
      assert (E2 : (kk + 1 + 1 = kk + 2)%Z) by lia. assert (E3 : (kk + 1 + 1 + 1 = kk + 3)%Z) by lia.
      assert (COL : tk (kk + 1) = c_colon -> (kk + 2 <= e_n E0)%Z /\ (3 * (sbv + d + 5) <= 5 * e_off E0 (kk + 2))%Z).
      { intros HC. assert (kk + 1 < e_n E0)%Z by (apply (tok_nonzero_lt (e_bs E0)); [lia | rewrite HC; unfold c_colon; lia]).
        pose proof (off_add _ _ HS1 (kk + 1) 1 ltac:(gng; lia) ltac:(gng; lia) ltac:(gng; lia)) as HOA. rewrite E2 in HOA. lia. }
      assert (VE : tk (kk + 1) = c_colon -> vexp (mkst (kk + 2) dpt Wv (sbv + d + 5) sc)).
      { intros HC. destruct (COL HC) as [C1 C2]. unfold vexp. cbn [k depth W sb scopes].
        split; [lia|]. split; [lia|]. split; [lia|]. split; [exact C2|]. split; [exact HDP | exact HSCO]. }
      set (sF := mkst (kk + 1) dpt Wv (sbv + d + 5) sc) in *.
      set (sV0 := mkst (kk + 1 + 1) dpt Wv (sbv + d + 5) sc).
      apply (seg_key_end (G w tws sbs) OK' SHZ (wQ w) kk dpt Wv sbv d sc HI ltac:(gng; lia) HD0 HSCAP LT (KXw _ _)).
      +
        intros HC HQ. gn. destruct (COL HC) as [C1 C2].
        assert (HKn : (kk + 2 < e_n E0)%Z) by (apply (tok_nonzero_lt (e_bs E0)); [lia | rewrite HQ; unfold c_quote; lia]).
        pose proof (inv_depth_range _ _ _ _ HI) as HDR. cbn [depth] in HDR.
        apply (STR_O (G w tws sbs) (wQ w) (mkst (kk + 2) dpt Wv (sbv + d + 5) sc) OK' SHZ); gng;
          [lia | split; lia | split; lia | exact HDR | exact HQ | exact LT | exact LS | exact (KXw _ _) | intros d' cb' HSO HCB']. gn.
        rewrite <- E2 in HQ, HSO.
        to_LABK w ObjCont (mkst (k sV0 + 1) (depth sV0) (W sV0 + 1) (sb sV0 + d' + 5) (scopes sV0)).
        eapply USg; [ | lens | pose proof (srec_length d' cb' HCB'); lens | apply GM; lens].
        apply (tst_obj_field _ _ _ sF _ _ _ _ HC). apply tv_string; cbn [k depth W sb scopes gT gS gC]; rewrite ?app_nil_r;
          [exact HQ | exact HSO | apply frameT_app; exact LT | rewrite ?app_nil_r; apply frameS_app; exact LS
          | rewrite (Tf_app_r0 _ _ Wv LT); reflexivity
          | rewrite ?app_nil_r; pose proof (string_ok_lt _ _ (kk + 1 + 1) d' HS1 ltac:(gng; lia) HSO); apply wrote_str_app; [exact LS | exact HCB' | lia] ].
      +
        intros HC H1 H2. gn. rewrite <- E2 in H1. rewrite <- E3 in H2.
        to_LABK w ObjCont (mkst (k sV0 + 2) (depth sV0) (W sV0 + 2) (sb sV0) (scopes sV0)).
        eapply USg; [ | lens | lens | apply GM; lens].
        apply (tst_obj_field _ _ _ sF _ _ _ _ HC). apply (tv_arr_empty _ _ _ _ sV0 _ _ _ 0%Z); cbn [k depth W sb scopes gT gS gC]; rewrite ?app_nil_r;
          [exact H1 | exact H2 | apply frameT_app; exact LT | rewrite ?app_nil_r; apply frameS_refl
          | rewrite (Tf_app_r0 _ _ Wv LT); reflexivity | unfold ck_any, CNT_MAX; lia
          | rewrite (Tf_app_r _ _ Wv 1%Z LT) by lia; reflexivity ].
      +
        intros HC H1 H2. gn. rewrite <- E2 in H1. rewrite <- E3 in H2.
        to_LABK w ObjCont (mkst (k sV0 + 2) (depth sV0) (W sV0 + 2) (sb sV0) (scopes sV0)).
        eapply USg; [ | lens | lens | apply GM; lens].
        apply (tst_obj_field _ _ _ sF _ _ _ _ HC). apply (tv_obj_empty _ _ _ _ sV0 _ _ _ 0%Z); cbn [k depth W sb scopes gT gS gC]; rewrite ?app_nil_r;
          [exact H1 | exact H2 | apply frameT_app; exact LT | rewrite ?app_nil_r; apply frameS_refl
          | rewrite (Tf_app_r0 _ _ Wv LT); reflexivity | unfold ck_any, CNT_MAX; lia
          | rewrite (Tf_app_r _ _ Wv 1%Z LT) by lia; reflexivity ].
      +
        intros HC H1 H2. gn. rewrite <- E2 in H1. rewrite <- E3 in H2.
        to_LABK w ArrBegin (mkst (k sV0 + 1) (depth sV0) (W sV0) (sb sV0) (scopes sV0)).
        eapply USg; [ | lens | lens | apply GM; lens].
        apply (tst_obj_field _ _ _ sF _ _ _ _ HC). apply tv_arr; cbn [k depth W sb scopes gT gS gC]; rewrite ?app_nil_r;
          [exact H1 | exact H2 | apply frameT_refl | apply frameS_refl].
      +
        intros HC H1 H2. gn. rewrite <- E2 in H1. rewrite <- E3 in H2.
        to_LABK w ObjBegin (mkst (k sV0 + 1) (depth sV0) (W sV0) (sb sV0) (scopes sV0)).
        eapply USg; [ | lens | lens | apply GM; lens].
        apply (tst_obj_field _ _ _ sF _ _ _ _ HC). apply tv_obj; cbn [k depth W sb scopes gT gS gC]; rewrite ?app_nil_r;
          [exact H1 | exact H2 | apply frameT_refl | apply frameS_refl].
      +
        intros HC _ _ _ _. gn.
        apply (NUMO w (mkst (kk + 2) dpt Wv (sbv + d + 5) sc) tws sbs (GM (kk + 2)%Z ltac:(lia)) (VE HC) ltac:(cbn [W]; exact LT)).
        cbn [k depth W sb scopes]. intros HN w' v r HG' Hv. gn. rewrite <- E2 in HN.
        to_LABK w' ObjCont (mkst (k sV0 + 1) (depth sV0) (W sV0 + 2) (sb sV0) (scopes sV0)).
        eapply USg; [ | lens | lens | unfold sV0; cbn [k]; replace (kk + 1 + 1 + 1)%Z with (kk + 2 + 1)%Z by lia; exact HG'].
        apply (tst_obj_field _ _ _ sF _ _ _ _ HC). apply tv_number; cbn [k depth W sb scopes gT gS gC]; rewrite ?app_nil_r;
          [exact HN | apply frameT_app; exact LT | rewrite ?app_nil_r; apply frameS_refl | rewrite (Tf_app_r0 _ _ Wv LT); exact Hv].
      +
        intros HC _ _ _ _. gn. destruct (COL HC) as [C1 C2].
        unfold objatom_k. intros. eapply (seg_atoms_o (G w tws sbs) OK' SHZ (wQ w) (mkst (kk + 2) dpt Wv (sbv + d + 5) sc)); gng;
          [eassumption | lia | split; lia | lia | exact LT | exact (KXw _ _) | intros v Hv HA]. gn.
        rewrite <- E2 in HA.
        to_LABK w ObjCont (mkst (k sV0 + 1) (depth sV0) (W sV0 + 1) (sb sV0) (scopes sV0)).
        eapply USg; [ | lens | lens | apply GM; lens].
        apply (tst_obj_field _ _ _ sF _ _ _ _ HC). apply tv_atom; cbn [k depth W sb scopes gT gS gC]; rewrite ?app_nil_r;
          [exact HA | apply frameT_app; exact LT | rewrite ?app_nil_r; apply frameS_refl | rewrite (Tf_app_r0 _ _ Wv LT); exact Hv].
    -
      destruct (tinv_counts_cons _ _ _ _ _ _ HI (TInvS_TInv _ _ _ _ HT) ltac:(left; reflexivity)) as (c & cs0 & HCS). cbn [gC] in HCS. subst cs.
      unfold objcont_k. intros. eapply (seg_obj_cont (G w tws sbs) OK' SHZ (wQ w) s); [eassumption | exact HI | exact LT | exact (KXw _ _) | intros HT1 HT2 | intros cv ti rest ESC Hcv HT1]; gn.
      +
        apply (STR_KEYB (G w tws sbs) (wQ w) s OK' SHZ HI HT1 HT2 LT LS (KXw _ _)). intros d cb HSO HCB. gn.
        assert (HKn0 : (k s < e_n E0)%Z) by (apply (tok_nonzero_lt (e_bs E0)); [lia | rewrite HT1; unfold c_comma; lia]).
        pose proof (string_ok_lt _ _ (k s + 1) d HS1 ltac:(gng; lia) HSO) as HD0.
        to_LABKF w (mkst (k s + 2) (depth s) (W s + 1) (sb s + d + 5) (scopes s)).
        eapply USg; [ | lens | pose proof (srec_length d cb HCB); lens | apply GM; lens].
        apply (tst_obj_cont_comma _ _ ck_any s (mkG (Tf tws) (Tf sbs) (c :: cs0)) _ _ d c cs0 HT1 HT2 HSO); cbn [gT gS gC]; rewrite ?app_nil_r.
        * apply frameT_app. exact LT.
        * apply frameS_app. exact LS.
        * rewrite (Tf_app_r0 _ _ (W s) LT). reflexivity.
        * apply wrote_str_app; [exact LS | exact HCB | lia].
        * reflexivity.
      +
        pose proof (inv_scopes _ _ _ _ HI) as HSCS. rewrite ESC in HSCS. pose proof (Forall_inv HSCS) as HTI. cbn [snd] in HTI.
        to_LABK w ScopeEnd (mkst (k s + 1) (depth s) (W s + 1) (sb s) (scopes s)).
        eapply USg; [ | lens | lens | apply GM; lens].
        apply (tst_obj_cont_end _ _ ck_any s (mkG (Tf tws) (Tf sbs) (c :: cs0)) _ _ ti rest c cs0 cv HT1 ESC eq_refl); cbn [gT gS gC]; rewrite ?app_nil_r.
        * apply frameTx_zupd_app; [exact LT | lia].
        * rewrite ?app_nil_r. apply frameS_refl.
        * rewrite (Tf_zupd_app_r0 _ _ (W s)) by exact LT. reflexivity.
        * rewrite Tf_zupd_app_same by lia. reflexivity.
        * exact Hcv.
    -
      unfold scopeend_k. intros. eapply (seg_scope_end (G w tws sbs) OK' SHZ (wQ w) s); [eassumption | exact HI | intros sc0 HS0 | intros sc0 ti rest HS0 | intros sc0 ti rest HS0]; gn.
      + to_LABK w DocEnd (mkst (k s) (depth s - 1) (W s) (sb s) []).
        eapply USg; [ | lens | lens | apply GM; lens].
        apply (tst_scope_end_doc _ _ _ s _ _ _ sc0 HS0); cbn [gT gS gC]; rewrite ?app_nil_r; [apply frameT_refl | apply frameS_refl].
      + to_LABK w ArrCont (mkst (k s) (depth s - 1) (W s) (sb s) ((true, ti) :: rest)).
        eapply USg; [ | lens | lens | apply GM; lens].
        apply (tst_scope_end_arr _ _ _ s _ _ _ sc0 ti rest HS0); cbn [gT gS gC]; rewrite ?app_nil_r; [apply frameT_refl | apply frameS_refl].
      + to_LABK w ObjCont (mkst (k s) (depth s - 1) (W s) (sb s) ((false, ti) :: rest)).
        eapply USg; [ | lens | lens | apply GM; lens].
        apply (tst_scope_end_obj _ _ _ s _ _ _ sc0 ti rest HS0); cbn [gT gS gC]; rewrite ?app_nil_r; [apply frameT_refl | apply frameS_refl].
    -
      unfold arrbegin_k. intros. eapply (seg_arr_begin (G w tws sbs) OK' SHZ (wQ w) s); [eassumption | exact HI | exact (KXw _ _) | intros HD]. gn.
      apply (arrvalue_k_hole (G w tws sbs) (wQ w)); [exact OK' | cbn [e_tws e_tcap s2_ghost wE env_at]; lia | intros h].
      to_LABK w ArrValue (mkst (k s) (depth s + 1) (W s + 1) (sb s) ((true, W s) :: scopes s)).
      eapply USg; [ | lens | lens | apply GM; lens].
      apply tst_arr_begin; cbn [gT gS gC]; rewrite ?app_nil_r; [unfold MAXDEPTH; lia | apply frameT_app; exact LT | rewrite ?app_nil_r; apply frameS_refl].
    -
      assert (HV : vexp s).
      { unfold vexp. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact (inv_depth _ _ _ _ HI) | exact (inv_scopes _ _ _ _ HI)]. }
      unfold arrvalue_k. intros. eapply (seg_arr_value (G w tws sbs) OK' SHZ (wQ w) s); [eassumption | exact HI | exact LT | exact (KXw _ _) | ..].
      +
        intros HQ. gn.
        assert (HKn : (k s < e_n E0)%Z) by (apply (tok_nonzero_lt (e_bs E0)); [lia | rewrite HQ; unfold c_quote; lia]).
        apply (STR_A (G w tws sbs) (wQ w) s OK' SHZ HI HQ LT LS (KXw _ _)). intros d cb HSO HCB. gn.
        to_LABK w ArrCont (mkst (k s + 1) (depth s) (W s + 1) (sb s + d + 5) (scopes s)).
        eapply USg; [ | lens | pose proof (srec_length d cb HCB); lens | apply GM; lens].
        apply tst_arr_value. apply tv_string; cbn [gT gS gC]; rewrite ?app_nil_r;
          [exact HQ | exact HSO | apply frameT_app; exact LT | rewrite ?app_nil_r; apply frameS_app; exact LS
          | rewrite (Tf_app_r0 _ _ (W s) LT); reflexivity
          | rewrite ?app_nil_r; pose proof (string_ok_lt _ _ (k s) d HS1 ltac:(gng; lia) HSO); apply wrote_str_app; [exact LS | exact HCB | lia] ].
      + intros H1 H2. gn.
        to_LABK w ArrCont (mkst (k s + 2) (depth s) (W s + 2) (sb s) (scopes s)).
        eapply USg; [ | lens | lens | apply GM; lens].
        apply tst_arr_value. apply (tv_arr_empty _ _ _ _ s _ _ _ 0%Z); cbn [gT gS gC]; rewrite ?app_nil_r;
          [exact H1 | exact H2 | apply frameT_app; exact LT | rewrite ?app_nil_r; apply frameS_refl
          | rewrite (Tf_app_r0 _ _ (W s) LT); reflexivity | unfold ck_any, CNT_MAX; lia
          | rewrite (Tf_app_r _ _ (W s) 1%Z LT) by lia; reflexivity ].
      + intros H1 H2. gn.
        to_LABK w ArrCont (mkst (k s + 2) (depth s) (W s + 2) (sb s) (scopes s)).
        eapply USg; [ | lens | lens | apply GM; lens].
        apply tst_arr_value. apply (tv_obj_empty _ _ _ _ s _ _ _ 0%Z); cbn [gT gS gC]; rewrite ?app_nil_r;
          [exact H1 | exact H2 | apply frameT_app; exact LT | rewrite ?app_nil_r; apply frameS_refl
          | rewrite (Tf_app_r0 _ _ (W s) LT); reflexivity | unfold ck_any, CNT_MAX; lia
          | rewrite (Tf_app_r _ _ (W s) 1%Z LT) by lia; reflexivity ].
      + intros H1 H2. gn.
        to_LABK w ArrBegin (mkst (k s + 1) (depth s) (W s) (sb s) (scopes s)).
        eapply USg; [ | lens | lens | apply GM; lens].
        apply tst_arr_value. apply tv_arr; cbn [gT gS gC]; rewrite ?app_nil_r; [exact H1 | exact H2 | apply frameT_refl | apply frameS_refl].
      + intros H1 H2. gn.
        to_LABK w ObjBegin (mkst (k s + 1) (depth s) (W s) (sb s) (scopes s)).
        eapply USg; [ | lens | lens | apply GM; lens].
        apply tst_arr_value. apply tv_obj; cbn [gT gS gC]; rewrite ?app_nil_r; [exact H1 | exact H2 | apply frameT_refl | apply frameS_refl].
      + intros _ _ _ _. apply (NUMA w s tws sbs HG HV LT). intros HN w' v r HG' Hv. gn.
        to_LABK w' ArrCont (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s)).
        eapply USg; [ | lens | lens | exact HG'].
        apply tst_arr_value. apply tv_number; cbn [gT gS gC]; rewrite ?app_nil_r;
          [exact HN | apply frameT_app; exact LT | rewrite ?app_nil_r; apply frameS_refl | rewrite (Tf_app_r0 _ _ (W s) LT); exact Hv].
      + intros _ _ _ _. unfold arratom_k. intros. eapply (seg_atoms_a (G w tws sbs) OK' SHZ (wQ w) s); gng;
          [eassumption | lia | split; lia | exact LT | exact (KXw _ _) | intros v Hv HA]. gn.
        to_LABK w ArrCont (mkst (k s + 1) (depth s) (W s + 1) (sb s) (scopes s)).
        eapply USg; [ | lens | lens | apply GM; lens].
        apply tst_arr_value. apply tv_atom; cbn [gT gS gC]; rewrite ?app_nil_r;
          [exact HA | apply frameT_app; exact LT | rewrite ?app_nil_r; apply frameS_refl | rewrite (Tf_app_r0 _ _ (W s) LT); exact Hv].
    -
      destruct (tinv_counts_cons _ _ _ _ _ _ HI (TInvS_TInv _ _ _ _ HT) ltac:(right; reflexivity)) as (c & cs0 & HCS). cbn [gC] in HCS. subst cs.
      unfold arrcont_k. intros. eapply (seg_arr_cont (G w tws sbs) OK' SHZ (wQ w) s); [eassumption | exact HI | exact LT | exact (KXw _ _) | intros HT1 | intros cv ti rest ESC Hcv HT1]; gn.
      + to_LABK w ArrValue (mkst (k s + 1) (depth s) (W s) (sb s) (scopes s)).
        eapply USg; [ | lens | lens | apply GM; lens].
        apply (tst_arr_cont_comma _ _ _ s _ _ _ c cs0 HT1); cbn [gT gS gC]; rewrite ?app_nil_r; [apply frameT_refl | apply frameS_refl | reflexivity].
      +
        pose proof (inv_scopes _ _ _ _ HI) as HSCS. rewrite ESC in HSCS. pose proof (Forall_inv HSCS) as HTI. cbn [snd] in HTI.
        to_LABK w ScopeEnd (mkst (k s + 1) (depth s) (W s + 1) (sb s) (scopes s)).
        eapply USg; [ | lens | lens | apply GM; lens].
        apply (tst_arr_cont_end _ _ ck_any s (mkG (Tf tws) (Tf sbs) (c :: cs0)) _ _ ti rest c cs0 cv HT1 ESC eq_refl); cbn [gT gS gC]; rewrite ?app_nil_r.
        * apply frameTx_zupd_app; [exact LT | lia].
        * rewrite ?app_nil_r. apply frameS_refl.
        * rewrite (Tf_zupd_app_r0 _ _ (W s)) by exact LT. reflexivity.
        * rewrite Tf_zupd_app_same by lia. reflexivity.
        * exact Hcv.
    -
      unfold docend_k. intros. eapply (seg_doc_end (G w tws sbs) OK' SHZ (wQ w) s); [eassumption | exact HI | exact LT | exact (KXw _ _) |].
      unfold docend_env, tape_ok. gng. rewrite ?app_nil_r.
      replace (Z.of_nat (length (zupd (tws ++ [tword t_root 0]) (Z.to_nat 0) (tword t_root (W s + 1))))) with (W s + 1)%Z by lens.
      rewrite LS.
      apply (docend_tape_wfS _ _ HS1 HL32 ck_any s (mkG (Tf tws) (Tf sbs) cs)); cbn [gT gS gC]; rewrite ?app_nil_r.
      + exact HI. + exact HT.
      + intros x Hx. rewrite Tf_zupd_other by lia. apply Tf_app_l. lia.
      + rewrite Tf_zupd_other by lia. rewrite (Tf_app_r0 _ _ (W s) LT). reflexivity.
      + apply Tf_zupd_same. lens.
  Qed.

  Lemma first_step : forall h0 l' s' w tws' sbs' cs',
    TSTEP DocStart s0 (mkG (Tf [h0]) (Tf []) []) l' s' (mkG (Tf tws') (Tf sbs') cs') ->
    Z.of_nat (length tws') = W s' -> Z.of_nat (length sbs') = sb s' -> good w (k s') ->
    LABK w tws' sbs' l' s'.
  Proof using OK0 good_shz good_mono KX NUMA NUMO STR_KEYA STR_KEYB STR_O STR_A.
    intros h0 l' s' w tws' sbs' cs' ST L1 L2 HG.
    pose proof (ok_s1 _ OK0) as HS1.
    pose proof (tstep_step _ _ _ _ _ _ _ _ _ ST) as ST0.
    assert (HI : INV l' s') by (eapply step_inv; [exact HS1 | exact ST0 | apply Inv_s0; exact HS1]).
    apply (s2_labels (S (Z.to_nat (MU l' s'))) l' s' w tws' sbs' cs'); [exact HG | lia | exact HI |].
    split; [exact L1|]. split; [exact L2|].
    exact (tstep_invS _ _ _ _ _ _ _ _ _ (Inv_s0 _ _ HS1) (TInvS_s0 ck_any (Tf [h0]) (Tf [])) ST).
  Qed.
End Main.


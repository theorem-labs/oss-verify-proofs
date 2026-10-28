(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_tables2 Sj_stage2_exitw Sj_stage2_entry Sj_stage2_rootc Sj_stage2_rootca Sj_stage2_roott
  Sj_stage2_rootn Sj_stage2_rootf Sj_stage2_objf Sj_stage2_hex4 Sj_stage2_docend Sj_stage2_main.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section Main2.
  Variable E0 : s2env.
  Hypothesis OK0 : env_ok E0.
  Variable WD : Type.
  Variable wm : WD -> mem.
  Variable wQ : WD -> machine_state -> Prop.
  Variable good : WD -> Z -> Prop.
  Notation wE := (Sj_stage2_main.wE E0 WD wm).
  Notation G w tws sbs := (s2_ghost (Sj_stage2_main.wE E0 WD wm w) tws sbs).
  Hypothesis good_shz : forall w kk, good w kk -> a_shz (wE w).
  Hypothesis good_mono : forall w kk kk', good w kk -> (kk <= kk')%Z -> good w kk'.
  Hypothesis KXW : forall w kk tws sbs, good w kk -> exit_kw (G w tws sbs) (wQ w).
  Hypothesis good_cc : forall w kk, good w kk -> a_cc (wE w).
  Hypothesis HROOM16 : (e_lo E0 + 16 <= e_spa E0)%Z.
  Notation tk := (e_tok E0).
  Notation vexp := (Sj_stage2_main.vexp E0).
  Notation TSTEP := (tstep (e_bs E0) (e_idxs E0) ck_any).

  Hypothesis NUMA : forall w s (tws sbs : list Z), good w (k s) -> vexp s -> Z.of_nat (length tws) = W s ->
    (is_numstart (tk (k s)) = true -> forall w' v r, good w' (k s + 1) -> num_word v ->
       arrcont_k (G w' (tws ++ [v; r]) (sbs ++ [])) (wQ w') (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s))) ->
    arrnum_k (G w tws sbs) (wQ w) s.
  Hypothesis NUMO : forall w s (tws sbs : list Z), good w (k s) -> vexp s -> Z.of_nat (length tws) = W s ->
    (is_numstart (tk (k s)) = true -> forall w' v r, good w' (k s + 1) -> num_word v ->
       objcont_k (G w' (tws ++ [v; r]) (sbs ++ [])) (wQ w') (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s))) ->
    objnum_k (G w tws sbs) (wQ w) s.

  Hypothesis ROOTNUM : forall w (h0 : Z), good w 0 -> is_numstart (tk 0) = true ->
    (forall w' v r, good w' 1 -> num_word v -> docend_k (G w' [h0; v; r] []) (wQ w') (mkst 1 0 3 0 [])) ->
    rootprim_k (G w [h0] []) (wQ w) 0xc5d88.

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

  Hypothesis STR_ROOT : forall E Q, env_ok E -> a_shz E -> a_cc E -> (e_lo E + 16 <= e_spa E)%Z -> e_tok E 0 = c_quote ->
    Z.of_nat (length (e_tws E)) = 1%Z -> Z.of_nat (length (e_sbs E)) = 0%Z ->
    exit_k (gapp E [tword t_str 0%Z] []) Q ->
    (forall d cb, string_ok (e_bs E) (e_idxs E) 0 d -> Z.of_nat (length cb) = d ->
       docend_k (gapp (gapp E [tword t_str 0%Z] []) [] (srec d cb)) Q (mkst 1 0 2 (0 + d + 5) [])) ->
    rootprim_k E Q 0xc75c8.

  Lemma KX : forall w kk tws sbs, good w kk -> exit_k (G w tws sbs) (wQ w).
  Proof using KXW. intros w kk tws sbs HG. apply exit_k_of_w. exact (KXW w kk tws sbs HG). Qed.

  Notation LABK := (Sj_stage2_main.LABK E0 WD wm wQ).
  Notation first_step := (Sj_stage2_main.first_step E0 OK0 WD wm wQ good good_shz good_mono KX NUMA NUMO STR_KEYA STR_KEYB STR_O STR_A).

  Lemma st_ext' : forall s s' : st, k s = k s' -> depth s = depth s' -> W s = W s' -> sb s = sb s' -> scopes s = scopes s' -> s = s'.
  Proof. intros [a b c d e] [a' b' c' d' e']; cbn; intros; subst; reflexivity. Qed.

  Ltac env_of_goal := lazymatch goal with |- _ ?Eg _ _ => Eg end.
  Ltac to_LABK0 w' l' sL :=
    unfold endc_env, empty_env, docend_env;
    let Eg := env_of_goal in
    let t := eval cbn [e_tws e_sbs gapp gpatch s2_ghost] in (e_tws Eg) in
    let u := eval cbn [e_tws e_sbs gapp gpatch s2_ghost] in (e_sbs Eg) in
    let LL := fresh "LL" in
    enough (LL : LABK w' t u l' sL);
    [ cbn [Sj_stage2_main.LABK] in LL;
      lazymatch goal with |- ?f ?sG =>
        lazymatch type of LL with ?g ?sL' =>
          replace sG with sL' by (apply st_ext'; cbn [k depth W sb scopes]; first [reflexivity | lia]); exact LL end end
    | ].
  Ltac lens := unfold srec, le4z; repeat rewrite length_app; rewrite ?zupd_length; repeat rewrite length_app; cbn [length k depth W sb scopes s0]; lia.
  Ltac gn := unfold Sj_stage2_main.wE in *; cbn [e_bs e_idxs e_tcap e_scap e_lo e_sp e_spa e_tws e_sbs s2_ghost gapp gpatch env_at] in *.

  Theorem s2_main : forall w (h0 : Z) docv x1 x5 x6 x7 x11 x12 x13 x16 x17 x18 x22 x23 x25 x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    good w 0 ->
    MEM1 (G w [h0] []) docv fc m1 ->
    evt bsegs (wQ w)
      (S2R (wE w) 0xc5778 x1 x5 x6 x7 (e_sp (wE w)) (Z_to_bv 64 (e_spa (wE w))) (Z_to_bv 64 (Z.shiftr (e_THIS (wE w) + 88) 3)) x11 x12 x13
           (Z_to_bv 64 (e_THIS (wE w) + 88)) (Z_to_bv 64 (e_FF (wE w))) x16 x17 x18 (Z_to_bv 64 (SHA (e_FF (wE w)))) (Z_to_bv 64 2147450880)
           (Z_to_bv 64 (e_DOC (wE w))) x22 x23 (Z_to_bv 64 (e_THIS (wE w))) x25 (Z_to_bv 64 (e_FF (wE w))) x27 x28 x29 x30 x31 F fc m1).
  Proof using OK0 good_shz good_mono KXW good_cc HROOM16 NUMA NUMO ROOTNUM STR_KEYA STR_KEYB STR_O STR_A STR_ROOT.
    intros w h0 docv x1 x5 x6 x7 x11 x12 x13 x16 x17 x18 x22 x23 x25 x27 x28 x29 x30 x31 F fc m1 HG HM.
    pose proof (ok_s1 _ OK0) as HS1. pose proof (n_le_len _ _ HS1) as HNL. pose proof (ok_len _ OK0) as HLEN. unfold S2_LEN_MAX in HLEN.
    pose proof (ok_tcap _ OK0) as [HTC _].
    pose proof (env_at_ok E0 (wm w) OK0) as OK. fold (wE w) in OK. pose proof (good_shz w _ HG) as SHZ.
    assert (OKg : env_ok (G w [h0] [])) by (apply env_ok_ghost; exact OK).
    assert (KXw : forall tws sbs, exit_k (G w tws sbs) (wQ w)) by (intros; exact (KX w _ _ _ HG)).
    assert (G1 : good w 1) by (apply (good_mono w 0); [exact HG | lia]).
    assert (G2 : good w 2) by (apply (good_mono w 0); [exact HG | lia]).
    assert (ATOM : forall c v, tk 0 = c -> is_atomstart c = true -> atom_word v -> docend_k (G w ([h0] ++ [v]) ([] ++ [])) (wQ w) (mkst 1 0 2 0 [])).
    { intros c v HT HA Hv. rewrite <- HT in HA.
      to_LABK0 w DocEnd (mkst (k s0 + 1) (depth s0) (W s0 + 1) (sb s0) (scopes s0)).
      eapply (first_step h0); [ | reflexivity | reflexivity | exact G1].
      apply tst_doc. apply tv_atom; cbn [gT gS gC]; rewrite ?app_nil_r; [exact HA | apply (frameT_app [h0]); reflexivity | apply frameS_refl | ].
      cbn [k W sb depth scopes s0]. rewrite (Tf_app_r0 [h0] [v] 1%Z) by reflexivity. exact Hv. }
    change (evt bsegs (wQ w) (S2R (G w [h0] []) 0xc5778 x1 x5 x6 x7 (e_sp (wE w)) (Z_to_bv 64 (e_spa (wE w))) (Z_to_bv 64 (Z.shiftr (e_THIS (wE w) + 88) 3)) x11 x12 x13
           (Z_to_bv 64 (e_THIS (wE w) + 88)) (Z_to_bv 64 (e_FF (wE w))) x16 x17 x18 (Z_to_bv 64 (SHA (e_FF (wE w)))) (Z_to_bv 64 2147450880)
           (Z_to_bv 64 (e_DOC (wE w))) x22 x23 (Z_to_bv 64 (e_THIS (wE w))) x25 (Z_to_bv 64 (e_FF (wE w))) x27 x28 x29 x30 x31 F fc m1)).
    apply (seg_entry (G w [h0] []) OKg SHZ (wQ w) docv x1 x5 x6 x7 x11 x12 x13 x16 x17 x18 x22 x23 x25 x27 x28 x29 x30 x31 F fc m1 HM (KXW w _ _ _ HG)).
    intros pc HPC HNX. unfold root_target in HPC.
    change (e_tok (G w [h0] []) 0) with (tk 0) in HPC.
    destruct (tk 0 =? 34)%Z eqn:T34.
    { apply Z.eqb_eq in T34. subst pc.
      apply (STR_ROOT (G w [h0] []) (wQ w) OKg SHZ (good_cc w _ HG) HROOM16 T34 eq_refl eq_refl (KXw _ _)). intros d cb HSO HCB. gn.
      to_LABK0 w DocEnd (mkst (k s0 + 1) (depth s0) (W s0 + 1) (sb s0 + d + 5) (scopes s0)).
      eapply (first_step h0); [ | reflexivity | cbn [k W sb depth scopes s0 app]; pose proof (srec_length d cb HCB); lens | exact G1].
      apply tst_doc. apply tv_string; cbn [gT gS gC]; rewrite ?app_nil_r;
        [exact T34 | exact HSO | rewrite ?app_nil_r; apply (frameT_app [h0]); reflexivity | cbn [app]; apply (frameS_app [] (srec d cb) 0%Z); reflexivity
        | rewrite ?app_nil_r; cbn [k W sb depth scopes s0]; rewrite (Tf_app_r0 [h0] _ 1%Z) by reflexivity; reflexivity
        | cbn [k W sb depth scopes s0 app]; pose proof (string_ok_lt _ _ 0%Z d HS1 ltac:(pose proof (n_pos _ _ HS1); lia) HSO); apply (wrote_str_app []); [reflexivity | exact HCB | lia] ]. }
    destruct ((tk 0 =? 45) || (48 <=? tk 0) && (tk 0 <=? 57))%Z eqn:TNUM.
    { subst pc. apply (ROOTNUM w h0 HG TNUM). intros w' v r HG' Hv.
      to_LABK0 w' DocEnd (mkst (k s0 + 1) (depth s0) (W s0 + 2) (sb s0) (scopes s0)).
      eapply (first_step h0); [ | reflexivity | reflexivity | exact HG'].
      apply tst_doc. apply tv_number; cbn [gT gS gC]; rewrite ?app_nil_r; cbn [k W sb depth scopes s0];
        [exact TNUM | apply (frameT_app [h0]); reflexivity | apply frameS_refl | replace (Tf [h0; v; r] 1%Z) with v by reflexivity; exact Hv]. }
    destruct (tk 0 =? 91)%Z eqn:T91.
    { apply Z.eqb_eq in T91. subst pc. unfold rootprim_k. intros.
      eapply (seg_root_arr (G w [h0] []) OKg SHZ (wQ w)); [eassumption | exact T91 | reflexivity | exact (KXw _ _) | intros H2 | intros H2]; gn.
      - to_LABK0 w ArrBegin (mkst (k s0 + 1) (depth s0) (W s0) (sb s0) (scopes s0)).
        eapply (first_step h0); [ | reflexivity | reflexivity | exact G1].
        apply tst_doc. apply tv_arr; cbn [gT gS gC]; rewrite ?app_nil_r; [exact T91 | exact H2 | apply frameT_refl | apply frameS_refl].
      - to_LABK0 w DocEnd (mkst (k s0 + 2) (depth s0) (W s0 + 2) (sb s0) (scopes s0)).
        eapply (first_step h0); [ | reflexivity | reflexivity | exact G2].
        apply tst_doc. apply (tv_arr_empty _ _ _ _ s0 _ _ _ 0%Z); cbn [gT gS gC]; rewrite ?app_nil_r; cbn [k W sb depth scopes s0];
          [exact T91 | exact H2 | apply (frameT_app [h0]); reflexivity | apply frameS_refl
          | rewrite (Tf_app_r0 [h0] _ 1%Z) by reflexivity; reflexivity | unfold ck_any, CNT_MAX; lia
          | rewrite (Tf_app_r [h0] _ 1%Z 1%Z) by (cbn; lia); reflexivity ]. }
    destruct (tk 0 =? 102)%Z eqn:T102.
    { apply Z.eqb_eq in T102. subst pc. unfold rootprim_k. intros.
      eapply (seg_root_f (G w [h0] []) OKg SHZ (wQ w)); [eassumption | reflexivity | exact (KXw _ _) | apply (ATOM _ _ T102); [reflexivity | right; left; reflexivity]]. }
    destruct (tk 0 =? 110)%Z eqn:T110.
    { apply Z.eqb_eq in T110. subst pc. unfold rootprim_k. intros.
      eapply (seg_root_n (G w [h0] []) OKg SHZ (wQ w)); [eassumption | reflexivity | exact (KXw _ _) | apply (ATOM _ _ T110); [reflexivity | right; right; reflexivity]]. }
    destruct (tk 0 =? 116)%Z eqn:T116.
    { apply Z.eqb_eq in T116. subst pc. unfold rootprim_k. intros.
      eapply (seg_root_t (G w [h0] []) OKg SHZ (wQ w)); [eassumption | reflexivity | exact (KXw _ _) | apply (ATOM _ _ T116); [reflexivity | left; reflexivity]]. }
    destruct (tk 0 =? 123)%Z eqn:T123.
    { apply Z.eqb_eq in T123. subst pc. unfold rootprim_k. intros.
      eapply (seg_root_obj (G w [h0] []) OKg SHZ (wQ w)); [eassumption | exact T123 | reflexivity | exact (KXw _ _) | intros H2 | intros H2]; gn.
      - to_LABK0 w ObjBegin (mkst (k s0 + 1) (depth s0) (W s0) (sb s0) (scopes s0)).
        eapply (first_step h0); [ | reflexivity | reflexivity | exact G1].
        apply tst_doc. apply tv_obj; cbn [gT gS gC]; rewrite ?app_nil_r; [exact T123 | exact H2 | apply frameT_refl | apply frameS_refl].
      - to_LABK0 w DocEnd (mkst (k s0 + 2) (depth s0) (W s0 + 2) (sb s0) (scopes s0)).
        eapply (first_step h0); [ | reflexivity | reflexivity | exact G2].
        apply tst_doc. apply (tv_obj_empty _ _ _ _ s0 _ _ _ 0%Z); cbn [gT gS gC]; rewrite ?app_nil_r; cbn [k W sb depth scopes s0];
          [exact T123 | exact H2 | apply (frameT_app [h0]); reflexivity | apply frameS_refl
          | rewrite (Tf_app_r0 [h0] _ 1%Z) by reflexivity; reflexivity | unfold ck_any, CNT_MAX; lia
          | rewrite (Tf_app_r [h0] _ 1%Z 1%Z) by (cbn; lia); reflexivity ]. }
    congruence.
  Qed.
End Main2.

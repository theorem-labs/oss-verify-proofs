(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes Z10q.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf Zpi Zpa SjTape Zpj Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Zwd Zwh Zw5 Zwf Zw6 Zw4
  Zwe Zys Zyr Zyt Zwp Zwr Zzj Zzm
  Zw8 Zw9 Zwg Zyw Zz5.
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

Definition normal (l : label) : Prop := match l with ObjField | ScopeEnd => False | _ => True end.

Section Main.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Variable Q : machine_state -> Prop.
  Notation G tws sbs := (s2_ghost E tws sbs).
  Notation INV := (Inv (e_bs E) (e_idxs E)).
  Notation STEP := (step (e_bs E) (e_idxs E)).
  Notation MU := (mu (e_idxs E)).
  Notation TINV := (TInv ck_any).
  Notation TSTEP := (tstep (e_bs E) (e_idxs E) ck_any).

  Hypothesis KX : forall tws sbs, exit_k (G tws sbs) Q.
  Hypothesis KS : forall tws sbs, tape_ok tws sbs -> succ_k (G tws sbs) Q.

  Definition vexp (s : st) : Prop :=
    (0 <= k s <= e_n E)%Z /\ (1 <= W s <= k s + 1)%Z /\ (0 <= sb s)%Z /\ (3 * sb s <= 5 * e_off E (k s))%Z /\
    (depth s = Z.of_nat (length (scopes s)) /\ (depth s < MAXDEPTH)%Z) /\ Forall (fun sc => (1 <= snd sc < W s)%Z) (scopes s).

  Hypothesis NUMA : forall tws sbs s, vexp s -> Z.of_nat (length tws) = W s ->
    (forall v r, num_word v -> is_numstart (e_tok E (k s)) = true ->
       lab_k (G (tws ++ [v; r]) (sbs ++ [])) Q 0x30fb0 (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s))) ->
    arrprim_k (G tws sbs) Q 0x31350 s.
  Hypothesis NUMO : forall tws sbs s, vexp s -> Z.of_nat (length tws) = W s ->
    (forall v r, num_word v -> is_numstart (e_tok E (k s)) = true ->
       lab_k (G (tws ++ [v; r]) (sbs ++ [])) Q 0x30c48 (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s))) ->
    objval_k (G tws sbs) Q 0x3018c s.

  Definition LABK (E' : s2env) (l : label) (s : st) : Prop :=
    match l with
    | ObjBegin => lab_k E' Q 0x2c090 s
    | ObjCont => lab_k E' Q 0x30c48 s
    | ArrValue => lab_k E' Q 0x30fec s
    | ArrCont => lab_k E' Q 0x30fb0 s
    | ArrBegin => arrbegin_k E' Q s
    | DocEnd => docend_k E' Q s
    | ScopeEnd => forall b ti rest, scopes s = (b, ti) :: rest ->
                    endc_k E' Q (occ b) (mkst (k s) (depth s) (W s - 1) (sb s) (scopes s))
    | ObjField => forall kk dpt Wv sbv d sc, s = mkst (kk + 1) dpt Wv (sbv + d + 5) sc -> (0 <= d)%Z ->
                    Z.of_nat (length (e_sbs E')) = sbv -> keyend_k E' Q kk dpt Wv sbv d sc
    | DocStart => True
    end.

  Definition GI (l : label) (s : st) (tws sbs cs : list Z) : Prop :=
    match l with
    | ObjField => Z.of_nat (length tws) = W s /\
                  exists d, (0 <= d)%Z /\ (Z.of_nat (length sbs) + d + 5 = sb s)%Z /\
                    forall cb, Z.of_nat (length cb) = d -> TINV ObjField s (mkG (Tf tws) (Tf (sbs ++ srec d cb)) cs)
    | ScopeEnd => (Z.of_nat (length tws) + 1 = W s)%Z /\ Z.of_nat (length sbs) = sb s /\
                  exists b ti rest, scopes s = (b, ti) :: rest /\ (0 <= ti < Z.of_nat (length tws))%Z /\
                    forall cv, (0 <= cv <= CNT_MAX)%Z ->
                      TINV ScopeEnd s (mkG (Tf (zupd tws (Z.to_nat ti) (cword (occ b) (W s) cv) ++ [tword (occ b + 2) ti])) (Tf sbs) cs)
    | _ => Z.of_nat (length tws) = W s /\ Z.of_nat (length sbs) = sb s /\ TINV l s (mkG (Tf tws) (Tf sbs) cs)
    end.

  Ltac by_state L :=
    repeat match goal with x := _ : st |- _ => subst x end;
    cbn [LABK] in L;
    lazymatch goal with |- ?f ?sG =>
      lazymatch type of L with ?g ?sL =>
        replace sG with sL by (apply st_ext; cbn [k depth W sb scopes]; first [reflexivity | lia]); exact L end end.

  Ltac env_of_goal :=
    lazymatch goal with
    | |- lab_k ?Eg _ _ _ => Eg
    | |- endc_k ?Eg _ _ _ => Eg
    | |- arrbegin_k ?Eg _ _ => Eg
    | |- docend_k ?Eg _ _ => Eg
    end.

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
  Proof using OK KX KS NUMA NUMO.
    induction N as [|N IH]; intros l s tws sbs cs HMU HI HG.
    { pose proof (mu_nonneg _ _ _ _ HI). lia. }
    pose proof (ok_s1 _ OK) as HS1.
    pose proof (inv_k _ _ _ _ HI) as HK. pose proof (inv_W _ _ _ _ HI) as HW. pose proof (inv_sb _ _ _ _ HI) as [HSB0 HSB].
    pose proof (n_le_len _ _ HS1) as HNL. pose proof (ok_tcap _ OK) as [HTC _]. pose proof (ok_scap _ OK) as [HSC _].
    pose proof (ok_len _ OK) as HLEN. unfold S2_LEN_MAX in HLEN.
    assert (HL32 : (blen (e_bs E) + 3 < 2^32)%Z) by lia.
    assert (OK' : env_ok (G tws sbs)) by (apply env_ok_ghost; exact OK).

    assert (USg : forall tws0 sbs0 cs0 l' s' tws' sbs' cs',
              TINV l s (mkG (Tf tws0) (Tf sbs0) cs0) ->
              TSTEP l s (mkG (Tf tws0) (Tf sbs0) cs0) l' s' (mkG (Tf tws') (Tf sbs') cs') ->
              Z.of_nat (length tws') = W s' -> Z.of_nat (length sbs') = sb s' -> normal l' ->
              LABK (G tws' sbs') l' s').
    { intros tws0 sbs0 cs0 l' s' tws' sbs' cs' HT ST L1 L2 HN.
      pose proof (tstep_step _ _ _ _ _ _ _ _ _ ST) as ST0.
      apply (IH l' s' tws' sbs' cs').
      - pose proof (step_mu _ _ _ _ _ _ ST0). lia.
      - eapply step_inv; [exact HS1 | exact ST0 | exact HI].
      - pose proof (tstep_inv _ _ _ _ _ _ _ _ _ HI HT ST) as HT'.
        destruct l'; cbn [normal] in HN; try contradiction; cbn [GI]; (split; [exact L1|]; split; [exact L2| exact HT']). }
    destruct l; cbn [LABK GI slackW slackS] in *.
    -   exact I.
    -
      destruct HG as (LT & LS & HT).
      apply (seg_obj_begin (G tws sbs) OK' Q s HI (KX tws sbs)). intros HD HQ. gn.
      apply (seg_key_a (G tws sbs) OK' Q s HI HD HQ LT LS); [intros h; exact (KX _ _)|].
      intros d h HSO. gn.
      pose proof (string_ok_lt _ _ (k s) d HS1 ltac:(gng; lia) HSO) as HD0.
      pose proof (st_obj_begin _ _ s d HD HQ HSO) as ST0.
      assert (HMU1 : (MU ObjField (mkst (k s + 1) (depth s + 1) (W s + 2) (sb s + d + 5) ((false, W s) :: scopes s)) < Z.of_nat N)%Z) by (pose proof (step_mu _ _ _ _ _ _ ST0); lia).
      assert (HI1 : INV ObjField (mkst (k s + 1) (depth s + 1) (W s + 2) (sb s + d + 5) ((false, W s) :: scopes s))) by (eapply step_inv; [exact HS1 | exact ST0 | exact HI]).
      assert (HG1 : GI ObjField (mkst (k s + 1) (depth s + 1) (W s + 2) (sb s + d + 5) ((false, W s) :: scopes s)) (tws ++ [h; tword t_str (sb s)]) (sbs ++ []) (1%Z :: cs)).
      { cbn [GI k depth W sb scopes]. split; [lens|]. exists d. split; [lia|]. split; [lens|].
        intros cb HCB.
        eapply (tstep_inv _ _ _ _ _ _ _ _ _ HI HT).
        apply (tst_obj_begin _ _ ck_any s (mkG (Tf tws) (Tf sbs) cs) (Tf (tws ++ [h; tword t_str (sb s)])) (Tf ((sbs ++ []) ++ srec d cb)) d HD HQ HSO); cbn [gT gS gC].
        - apply frameT_app. exact LT.
        - rewrite app_nil_r. apply frameS_app. exact LS.
        - rewrite (Tf_app_r _ _ (W s) 1%Z LT) by lia. reflexivity.
        - rewrite app_nil_r. apply wrote_str_app; [exact LS | exact HCB | lia]. }
      pose proof (IH _ _ _ _ _ HMU1 HI1 HG1) as L. cbn [LABK] in L.
      apply L; [apply st_ext; cbn [k depth W sb scopes]; first [reflexivity | lia] | lia | cbn [e_sbs s2_ghost]; lens].
    -
      intros kk dpt Wv sbv d sc -> HD0 LS. cbn [k depth W sb scopes e_sbs s2_ghost] in *.
      destruct HG as (LT & d0 & HD00 & LSD & HTf). assert (d0 = d) by lia. subst d0. clear HD00 LSD.
      pose proof (inv_depth _ _ _ _ HI) as HDP. pose proof (inv_scopes _ _ _ _ HI) as HSCO. cbn [k depth W sb scopes] in HDP, HSCO.
      pose proof (off_range _ _ HS1 (kk + 1) HK) as HOR.
      assert (HSCAP : (sbv + d + 5 <= e_scap E)%Z) by lia.
      assert (E2 : (kk + 1 + 1 = kk + 2)%Z) by lia. assert (E3 : (kk + 1 + 1 + 1 = kk + 3)%Z) by lia.
      assert (COL : e_tok E (kk + 1) = c_colon -> (kk + 2 <= e_n E)%Z /\ (3 * (sbv + d + 5) <= 5 * e_off E (kk + 2))%Z).
      { intros HC. assert (kk + 1 < e_n E)%Z by (apply (tok_nonzero_lt (e_bs E)); [lia | rewrite HC; unfold c_colon; lia]).
        pose proof (off_add _ _ HS1 (kk + 1) 1 ltac:(gng; lia) ltac:(gng; lia) ltac:(gng; lia)) as HOA. rewrite E2 in HOA. lia. }
      assert (VE : e_tok E (kk + 1) = c_colon -> vexp (mkst (kk + 2) dpt Wv (sbv + d + 5) sc)).
      { intros HC. destruct (COL HC) as [C1 C2]. unfold vexp. cbn [k depth W sb scopes].
        split; [lia|]. split; [lia|]. split; [lia|]. split; [exact C2|]. split; [exact HDP | exact HSCO]. }
      set (sF := mkst (kk + 1) dpt Wv (sbv + d + 5) sc) in *.
      set (sV0 := mkst (kk + 1 + 1) dpt Wv (sbv + d + 5) sc).
      apply (seg_key_end (G tws sbs) OK' Q kk dpt Wv sbv d sc ltac:(gng; lia) ltac:(gng; lia) HSCAP LS).
      intros cb HCB. pose proof (HTf cb HCB) as HT.
      assert (OK'' : env_ok (G (tws ++ []) (sbs ++ srec d cb))) by (apply env_ok_ghost; exact OK).
      assert (LT'' : Z.of_nat (length (e_tws (G (tws ++ []) (sbs ++ srec d cb)))) = Wv) by (cbn [e_tws gapp s2_ghost]; lens).
      assert (LS'' : Z.of_nat (length (e_sbs (G (tws ++ []) (sbs ++ srec d cb)))) = (sbv + d + 5)%Z).
      { cbn [e_sbs gapp s2_ghost]. rewrite length_app. pose proof (srec_length d cb HCB). lia. }
      apply (seg_key_disp (G (tws ++ []) (sbs ++ srec d cb)) OK'' Q kk dpt Wv sbv d sc HI ltac:(gng; lia) HD0 HSCAP LT'' (KX _ _)).
      +
        intros HC HQ. gn. destruct (COL HC) as [C1 C2].
        assert (HKn : (kk + 2 < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E)); [lia | rewrite HQ; unfold c_quote; lia]).
        apply (seg_str_o (G (tws ++ []) (sbs ++ srec d cb)) OK'' Q (mkst (kk + 2) dpt Wv (sbv + d + 5) sc)); gng;
          [lia | split; lia | split; lia | exact HQ | exact LT'' | exact LS'' | exact (KX _ _) | intros d' cb' HSO HCB']. gn.
        rewrite <- E2 in HQ, HSO.
        to_LABK ObjCont (mkst (k sV0 + 1) (depth sV0) (W sV0 + 1) (sb sV0 + d' + 5) (scopes sV0)).
        eapply USg; [exact HT | | lens | pose proof (srec_length d cb HCB); pose proof (srec_length d' cb' HCB'); lens | exact I].
        apply (tst_obj_field _ _ _ sF _ _ _ _ HC). apply tv_string; cbn [k depth W sb scopes gT gS gC].
        * exact HQ. * exact HSO.
        * rewrite !app_nil_r. apply frameT_app. exact LT.
        * rewrite app_nil_r. apply frameS_app. pose proof (srec_length d cb HCB). lens.
        * rewrite !app_nil_r. rewrite (Tf_app_r0 _ _ Wv LT). reflexivity.
        * rewrite app_nil_r. pose proof (string_ok_lt _ _ (kk + 1 + 1) d' HS1 ltac:(gng; lia) HSO). apply wrote_str_app; [pose proof (srec_length d cb HCB); lens | exact HCB' | lens].
      +
        intros HC H1 H2. gn. rewrite <- E2 in H1. rewrite <- E3 in H2.
        to_LABK ObjCont (mkst (k sV0 + 2) (depth sV0) (W sV0 + 2) (sb sV0) (scopes sV0)).
        eapply USg; [exact HT | | lens | lens | exact I].
        apply (tst_obj_field _ _ _ sF _ _ _ _ HC). apply (tv_arr_empty _ _ _ _ sV0 _ _ _ 0%Z); cbn [k depth W sb scopes gT gS gC];
          [exact H1 | exact H2 | rewrite !app_nil_r; apply frameT_app; exact LT | rewrite app_nil_r; apply frameS_refl
          | rewrite !app_nil_r; rewrite (Tf_app_r0 _ _ Wv LT); reflexivity | unfold ck_any, CNT_MAX; lia
          | rewrite !app_nil_r; rewrite (Tf_app_r _ _ Wv 1%Z LT) by lia; reflexivity ].
      +
        intros HC H1 H2. gn. rewrite <- E2 in H1. rewrite <- E3 in H2.
        to_LABK ObjCont (mkst (k sV0 + 2) (depth sV0) (W sV0 + 2) (sb sV0) (scopes sV0)).
        eapply USg; [exact HT | | lens | lens | exact I].
        apply (tst_obj_field _ _ _ sF _ _ _ _ HC). apply (tv_obj_empty _ _ _ _ sV0 _ _ _ 0%Z); cbn [k depth W sb scopes gT gS gC];
          [exact H1 | exact H2 | rewrite !app_nil_r; apply frameT_app; exact LT | rewrite app_nil_r; apply frameS_refl
          | rewrite !app_nil_r; rewrite (Tf_app_r0 _ _ Wv LT); reflexivity | unfold ck_any, CNT_MAX; lia
          | rewrite !app_nil_r; rewrite (Tf_app_r _ _ Wv 1%Z LT) by lia; reflexivity ].
      +
        intros HC H1 H2. gn. rewrite <- E2 in H1. rewrite <- E3 in H2.
        to_LABK ArrBegin (mkst (k sV0 + 1) (depth sV0) (W sV0) (sb sV0) (scopes sV0)).
        eapply USg; [exact HT | | lens | lens | exact I].
        apply (tst_obj_field _ _ _ sF _ _ _ _ HC). apply tv_arr; cbn [k depth W sb scopes gT gS gC];
          [exact H1 | exact H2 | rewrite !app_nil_r; apply frameT_refl | apply frameS_refl].
      +
        intros HC H1 H2. gn. rewrite <- E2 in H1. rewrite <- E3 in H2.
        to_LABK ObjBegin (mkst (k sV0 + 1) (depth sV0) (W sV0) (sb sV0) (scopes sV0)).
        eapply USg; [exact HT | | lens | lens | exact I].
        apply (tst_obj_field _ _ _ sF _ _ _ _ HC). apply tv_obj; cbn [k depth W sb scopes gT gS gC];
          [exact H1 | exact H2 | rewrite !app_nil_r; apply frameT_refl | apply frameS_refl].
      +
        intros HC _ _ _ _. gn. apply (NUMO (tws ++ []) (sbs ++ srec d cb) _ (VE HC) ltac:(cbn [W]; lens)). cbn [k depth W sb scopes]. intros v r Hv HN. gn. rewrite <- E2 in HN.
        to_LABK ObjCont (mkst (k sV0 + 1) (depth sV0) (W sV0 + 2) (sb sV0) (scopes sV0)).
        eapply USg; [exact HT | | lens | lens | exact I].
        apply (tst_obj_field _ _ _ sF _ _ _ _ HC). apply tv_number; cbn [k depth W sb scopes gT gS gC];
          [exact HN | rewrite !app_nil_r; apply frameT_app; exact LT | rewrite app_nil_r; apply frameS_refl
          | rewrite !app_nil_r; rewrite (Tf_app_r0 _ _ Wv LT); exact Hv].
      +
        intros HC _ _ _ _. gn. destruct (COL HC) as [C1 C2].
        apply (seg_atoms_o (G (tws ++ []) (sbs ++ srec d cb)) OK'' Q (mkst (kk + 2) dpt Wv (sbv + d + 5) sc)); gng; [lia | split; lia | exact LT'' | exact (KX _ _) | intros v Hv HA]. gn.
        rewrite <- E2 in HA.
        to_LABK ObjCont (mkst (k sV0 + 1) (depth sV0) (W sV0 + 1) (sb sV0) (scopes sV0)).
        eapply USg; [exact HT | | lens | lens | exact I].
        apply (tst_obj_field _ _ _ sF _ _ _ _ HC). apply tv_atom; cbn [k depth W sb scopes gT gS gC];
          [exact HA | rewrite !app_nil_r; apply frameT_app; exact LT | rewrite app_nil_r; apply frameS_refl
          | rewrite !app_nil_r; rewrite (Tf_app_r0 _ _ Wv LT); exact Hv].
    -
      destruct HG as (LT & LS & HT).
      destruct (tinv_counts_cons _ _ _ _ _ _ HI HT ltac:(left; reflexivity)) as (c & cs0 & HCS). cbn [gC] in HCS. subst cs.
      unfold lab_k. intros xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa7 xs2 xs3 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6 F fc m1 HM.
      apply (seg_obj_cont (G tws sbs) OK' Q s); [exact HI | exact HM | exact (KX _ _) | intros HT1 | intros HT1 HT2]; gn.
      +
        pose proof (inv_kind _ _ _ _ HI) as HKD. cbn [kind_ok] in HKD. destruct HKD as (ti & rest & ESC).
        pose proof (inv_scopes _ _ _ _ HI) as HSCS. rewrite ESC in HSCS. pose proof (Forall_inv HSCS) as HTI. cbn [snd] in HTI.
        pose proof (st_obj_cont_end _ _ s HT1) as ST0.
        assert (HMU1 : (MU ScopeEnd (mkst (k s + 1) (depth s) (W s + 1) (sb s) (scopes s)) < Z.of_nat N)%Z) by (pose proof (step_mu _ _ _ _ _ _ ST0); lia).
        assert (HI1 : INV ScopeEnd (mkst (k s + 1) (depth s) (W s + 1) (sb s) (scopes s))) by (eapply step_inv; [exact HS1 | exact ST0 | exact HI]).
        assert (HG1 : GI ScopeEnd (mkst (k s + 1) (depth s) (W s + 1) (sb s) (scopes s)) tws sbs (c :: cs0)).
        { cbn [GI k depth W sb scopes]. split; [lia|]. split; [exact LS|]. exists false, ti, rest. split; [exact ESC|]. split; [lia|].
          intros cv Hcv.
          eapply (tstep_inv _ _ _ _ _ _ _ _ _ HI HT).
          apply (tst_obj_cont_end _ _ ck_any s (mkG (Tf tws) (Tf sbs) (c :: cs0)) _ _ ti rest c cs0 cv HT1 ESC eq_refl); cbn [gT gS gC occ].
          - apply frameTx_zupd_app; [exact LT | lia].
          - apply frameS_refl.
          - rewrite (Tf_zupd_app_r0 _ _ (W s)) by exact LT. reflexivity.
          - rewrite Tf_zupd_app_same by lia. reflexivity.
          - exact Hcv. }
        pose proof (IH _ _ _ _ _ HMU1 HI1 HG1) as L. cbn [LABK] in L.
        specialize (L false ti rest ESC). cbn [occ k depth W sb scopes] in L. by_state L.
      +
        apply (seg_key_b (G tws sbs) OK' Q s HI HT1 HT2 LT LS (KX _ _)). intros d HSO. gn.
        assert (HKn0 : (k s < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E)); [lia | rewrite HT1; unfold c_comma; lia]).
        assert (HKn : (k s + 1 < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E)); [lia | rewrite HT2; unfold c_quote; lia]).
        pose proof (string_ok_lt _ _ (k s + 1) d HS1 ltac:(gng; lia) HSO) as HD0.
        pose proof (st_obj_cont_comma _ _ s d HT1 HT2 HSO) as ST0.
        assert (HMU1 : (MU ObjField (mkst (k s + 2) (depth s) (W s + 1) (sb s + d + 5) (scopes s)) < Z.of_nat N)%Z) by (pose proof (step_mu _ _ _ _ _ _ ST0); lia).
        assert (HI1 : INV ObjField (mkst (k s + 2) (depth s) (W s + 1) (sb s + d + 5) (scopes s))) by (eapply step_inv; [exact HS1 | exact ST0 | exact HI]).
        assert (HG1 : GI ObjField (mkst (k s + 2) (depth s) (W s + 1) (sb s + d + 5) (scopes s)) (tws ++ [tword t_str (sb s)]) (sbs ++ []) ((c + 1)%Z :: cs0)).
        { cbn [GI k depth W sb scopes]. split; [lens|]. exists d. split; [lia|]. split; [lens|].
          intros cb HCB.
          eapply (tstep_inv _ _ _ _ _ _ _ _ _ HI HT).
          apply (tst_obj_cont_comma _ _ ck_any s (mkG (Tf tws) (Tf sbs) (c :: cs0)) (Tf (tws ++ [tword t_str (sb s)])) (Tf ((sbs ++ []) ++ srec d cb)) d c cs0 HT1 HT2 HSO); cbn [gT gS gC].
          - apply frameT_app. exact LT.
          - rewrite app_nil_r. apply frameS_app. exact LS.
          - rewrite (Tf_app_r0 _ _ (W s) LT). reflexivity.
          - rewrite app_nil_r. apply wrote_str_app; [exact LS | exact HCB | lia].
          - reflexivity. }
        pose proof (IH _ _ _ _ _ HMU1 HI1 HG1) as L. cbn [LABK] in L.
        apply L; [apply st_ext; cbn [k depth W sb scopes]; first [reflexivity | lia] | lia | cbn [e_sbs s2_ghost]; lens].
    -
      intros b ti rest ESC.
      destruct HG as (LT & LS & b0 & ti0 & rest0 & ESC0 & HTI & HTf).
      rewrite ESC in ESC0. injection ESC0 as Er Et Eb. subst b0 ti0 rest0.
      pose proof (inv_depth _ _ _ _ HI) as [HD1 _]. rewrite ESC in HD1. cbn [length] in HD1.
      unfold endc_k. intros xra xt0 xt1 xt2 xs1 xa2 xa3 xa4 xa7 xs2 xs3 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6 F fc m1 HM. cbn [k depth W sb scopes] in HM |- *.
      assert (ES : mkst (k s) (depth s) (W s - 1 + 1) (sb s) (scopes s) = s) by (apply st_ext; cbn [k depth W sb scopes]; first [reflexivity | lia]).
      assert (HOC : (occ b = 91 \/ occ b = 123)%Z) by (destruct b; cbn [occ]; lia).
      apply (seg_endc (G tws sbs) OK' Q (mkst (k s) (depth s) (W s - 1) (sb s) (scopes s)) (occ b) b ti rest); cbn [k depth W sb scopes];
        [exact HOC | exact ESC | cbn [e_tws s2_ghost]; lia | lia | rewrite ES; exact HI | exact HM | intros cv sc Hcv HS0 | intros cv sc ti' rest' Hcv HS0 | intros cv sc ti' rest' Hcv HS0];
        unfold endc_env; cbn [e_tws e_sbs gapp gpatch s2_ghost]; replace (W s - 1 + 1)%Z with (W s) by lia.
      + rewrite HS0 in ESC. injection ESC as E2 E1. subst sc rest. cbn [length] in HD1.
        to_LABK DocEnd (mkst (k s) (depth s - 1) (W s) (sb s) []).
        eapply USg; [exact (HTf cv Hcv) | | lens | lens | exact I].
        apply (tst_scope_end_doc _ _ _ s _ _ _ (b, ti) HS0); cbn [gT gS gC]; [apply frameT_refl | rewrite app_nil_r; apply frameS_refl].
      + rewrite HS0 in ESC. injection ESC as E2 E1. subst sc rest.
        to_LABK ArrCont (mkst (k s) (depth s - 1) (W s) (sb s) ((true, ti') :: rest')).
        eapply USg; [exact (HTf cv Hcv) | | lens | lens | exact I].
        apply (tst_scope_end_arr _ _ _ s _ _ _ (b, ti) ti' rest' HS0); cbn [gT gS gC]; [apply frameT_refl | rewrite app_nil_r; apply frameS_refl].
      + rewrite HS0 in ESC. injection ESC as E2 E1. subst sc rest.
        to_LABK ObjCont (mkst (k s) (depth s - 1) (W s) (sb s) ((false, ti') :: rest')).
        eapply USg; [exact (HTf cv Hcv) | | lens | lens | exact I].
        apply (tst_scope_end_obj _ _ _ s _ _ _ (b, ti) ti' rest' HS0); cbn [gT gS gC]; [apply frameT_refl | rewrite app_nil_r; apply frameS_refl].
    -
      destruct HG as (LT & LS & HT).
      unfold arrbegin_k. intros xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6
        j0 j1 j2 j3 j4 j5 j6 j8 j9 F fc m1 HM.
      eapply (seg_arr_begin (G tws sbs) OK' Q s); [exact HI | exact HM | exact (KX _ _) | intros HD]. gn.
      apply (lab_k_hole (G tws sbs) Q); [exact OK' | cbn [e_tws e_tcap s2_ghost]; lia | intros h].
      to_LABK ArrValue (mkst (k s) (depth s + 1) (W s + 1) (sb s) ((true, W s) :: scopes s)).
      eapply USg; [exact HT | | lens | lens | exact I].
      apply tst_arr_begin; cbn [gT gS gC]; [exact HD | apply frameT_app; exact LT | rewrite app_nil_r; apply frameS_refl].
    -
      destruct HG as (LT & LS & HT).
      unfold lab_k. intros xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa7 xs2 xs3 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6 F fc m1 HM.
      assert (HV : vexp s).
      { unfold vexp. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact (inv_depth _ _ _ _ HI) | exact (inv_scopes _ _ _ _ HI)]. }
      apply (seg_arr_value (G tws sbs) OK' Q s); [exact HI | exact HM | exact LT | exact (KX _ _) | ..].
      +
        intros HQ. gn.
        assert (HKn : (k s < e_n E)%Z) by (apply (tok_nonzero_lt (e_bs E)); [lia | rewrite HQ; unfold c_quote; lia]).
        apply (seg_str_a (G tws sbs) OK' Q s); gng; [lia | split; lia | split; lia | exact HQ | exact LT | exact LS | exact (KX _ _) | intros d cb HSO HCB]. gn.
        to_LABK ArrCont (mkst (k s + 1) (depth s) (W s + 1) (sb s + d + 5) (scopes s)).
        eapply USg; [exact HT | | lens | pose proof (srec_length d cb HCB); lens | exact I].
        apply tst_arr_value. apply tv_string; cbn [gT gS gC];
          [exact HQ | exact HSO | rewrite !app_nil_r; apply frameT_app; exact LT | rewrite app_nil_r; apply frameS_app; exact LS
          | rewrite !app_nil_r; rewrite (Tf_app_r0 _ _ (W s) LT); reflexivity
          | rewrite app_nil_r; pose proof (string_ok_lt _ _ (k s) d HS1 ltac:(gng; lia) HSO); apply wrote_str_app; [exact LS | exact HCB | lia] ].
      + intros H1 H2. gn.
        to_LABK ArrCont (mkst (k s + 2) (depth s) (W s + 2) (sb s) (scopes s)).
        eapply USg; [exact HT | | lens | lens | exact I].
        apply tst_arr_value. apply (tv_arr_empty _ _ _ _ s _ _ _ 0%Z); cbn [gT gS gC];
          [exact H1 | exact H2 | apply frameT_app; exact LT | rewrite app_nil_r; apply frameS_refl
          | rewrite (Tf_app_r0 _ _ (W s) LT); reflexivity | unfold ck_any, CNT_MAX; lia
          | rewrite (Tf_app_r _ _ (W s) 1%Z LT) by lia; reflexivity ].
      + intros H1 H2. gn.
        to_LABK ArrCont (mkst (k s + 2) (depth s) (W s + 2) (sb s) (scopes s)).
        eapply USg; [exact HT | | lens | lens | exact I].
        apply tst_arr_value. apply (tv_obj_empty _ _ _ _ s _ _ _ 0%Z); cbn [gT gS gC];
          [exact H1 | exact H2 | apply frameT_app; exact LT | rewrite app_nil_r; apply frameS_refl
          | rewrite (Tf_app_r0 _ _ (W s) LT); reflexivity | unfold ck_any, CNT_MAX; lia
          | rewrite (Tf_app_r _ _ (W s) 1%Z LT) by lia; reflexivity ].
      + intros H1 H2. gn.
        to_LABK ArrBegin (mkst (k s + 1) (depth s) (W s) (sb s) (scopes s)).
        eapply USg; [exact HT | | lens | lens | exact I].
        apply tst_arr_value. apply tv_arr; cbn [gT gS gC]; [exact H1 | exact H2 | apply frameT_refl | apply frameS_refl].
      + intros H1 H2. gn.
        to_LABK ObjBegin (mkst (k s + 1) (depth s) (W s) (sb s) (scopes s)).
        eapply USg; [exact HT | | lens | lens | exact I].
        apply tst_arr_value. apply tv_obj; cbn [gT gS gC]; [exact H1 | exact H2 | apply frameT_refl | apply frameS_refl].
      + intros _ _ _ _. apply (NUMA tws sbs s HV LT). intros v r Hv HN. gn.
        to_LABK ArrCont (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s)).
        eapply USg; [exact HT | | lens | lens | exact I].
        apply tst_arr_value. apply tv_number; cbn [gT gS gC];
          [exact HN | apply frameT_app; exact LT | rewrite app_nil_r; apply frameS_refl | rewrite (Tf_app_r0 _ _ (W s) LT); exact Hv].
      + intros _ _ _ _. apply (seg_atoms_a (G tws sbs) OK' Q s); gng; [lia | split; lia | exact LT | exact (KX _ _) | intros v Hv HA]. gn.
        to_LABK ArrCont (mkst (k s + 1) (depth s) (W s + 1) (sb s) (scopes s)).
        eapply USg; [exact HT | | lens | lens | exact I].
        apply tst_arr_value. apply tv_atom; cbn [gT gS gC];
          [exact HA | apply frameT_app; exact LT | rewrite app_nil_r; apply frameS_refl | rewrite (Tf_app_r0 _ _ (W s) LT); exact Hv].
    -
      destruct HG as (LT & LS & HT).
      destruct (tinv_counts_cons _ _ _ _ _ _ HI HT ltac:(right; reflexivity)) as (c & cs0 & HCS). cbn [gC] in HCS. subst cs.
      unfold lab_k. intros xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa7 xs2 xs3 xs5 xs6 xs7 xs9 xs10 xt3 xt4 xt5 xt6 F fc m1 HM.
      apply (seg_arr_cont (G tws sbs) OK' Q s); [exact HI | exact HM | exact (KX _ _) | intros HT1 | intros HT1]; gn.
      + to_LABK ArrValue (mkst (k s + 1) (depth s) (W s) (sb s) (scopes s)).
        eapply USg; [exact HT | | lens | lens | exact I].
        apply (tst_arr_cont_comma _ _ _ s _ _ _ c cs0 HT1); cbn [gT gS gC]; [apply frameT_refl | apply frameS_refl | reflexivity].
      +
        pose proof (inv_kind _ _ _ _ HI) as HKD. cbn [kind_ok] in HKD. destruct HKD as (ti & rest & ESC).
        pose proof (inv_scopes _ _ _ _ HI) as HSCS. rewrite ESC in HSCS. pose proof (Forall_inv HSCS) as HTI. cbn [snd] in HTI.
        pose proof (st_arr_cont_end _ _ s HT1) as ST0.
        assert (HMU1 : (MU ScopeEnd (mkst (k s + 1) (depth s) (W s + 1) (sb s) (scopes s)) < Z.of_nat N)%Z) by (pose proof (step_mu _ _ _ _ _ _ ST0); lia).
        assert (HI1 : INV ScopeEnd (mkst (k s + 1) (depth s) (W s + 1) (sb s) (scopes s))) by (eapply step_inv; [exact HS1 | exact ST0 | exact HI]).
        assert (HG1 : GI ScopeEnd (mkst (k s + 1) (depth s) (W s + 1) (sb s) (scopes s)) tws sbs (c :: cs0)).
        { cbn [GI k depth W sb scopes]. split; [lia|]. split; [exact LS|]. exists true, ti, rest. split; [exact ESC|]. split; [lia|].
          intros cv Hcv.
          eapply (tstep_inv _ _ _ _ _ _ _ _ _ HI HT).
          apply (tst_arr_cont_end _ _ ck_any s (mkG (Tf tws) (Tf sbs) (c :: cs0)) _ _ ti rest c cs0 cv HT1 ESC eq_refl); cbn [gT gS gC occ].
          - apply frameTx_zupd_app; [exact LT | lia].
          - apply frameS_refl.
          - rewrite (Tf_zupd_app_r0 _ _ (W s)) by exact LT. reflexivity.
          - rewrite Tf_zupd_app_same by lia. reflexivity.
          - exact Hcv. }
        pose proof (IH _ _ _ _ _ HMU1 HI1 HG1) as L. cbn [LABK] in L.
        specialize (L true ti rest ESC). cbn [occ k depth W sb scopes] in L. by_state L.
    -
      destruct HG as (LT & LS & HT).
      apply (seg_doc_end (G tws sbs) OK' Q s HI LT); [exact (KX _ _)|].
      unfold docend_env. apply KS.
      unfold tape_ok. gng. rewrite ?app_nil_r.
      replace (Z.of_nat (length (zupd (tws ++ [tword t_root 0]) (Z.to_nat 0) (tword t_root (W s + 1))))) with (W s + 1)%Z by lens.
      rewrite LS.
      apply (docend_tape_wf _ _ HS1 HL32 ck_any s (mkG (Tf tws) (Tf sbs) cs)); cbn [gT gS gC].
      + exact HI. + exact HT.
      + intros x Hx. rewrite Tf_zupd_other by lia. apply Tf_app_l. lia.
      + rewrite Tf_zupd_other by lia. rewrite (Tf_app_r0 _ _ (W s) LT). reflexivity.
      + apply Tf_zupd_same. lens.
  Qed.

  Variable h0 : Z.
  Notation E0 := (G [h0] []).
  Hypothesis ROOTNUM : is_numstart (e_tok E 0) = true -> rootprim_k E0 Q 0x2aa00.

  Lemma first_step : forall l' s' tws' sbs' cs',
    TSTEP DocStart s0 (mkG (Tf [h0]) (Tf []) []) l' s' (mkG (Tf tws') (Tf sbs') cs') ->
    Z.of_nat (length tws') = W s' -> Z.of_nat (length sbs') = sb s' -> normal l' ->
    LABK (G tws' sbs') l' s'.
  Proof using OK KX KS NUMA NUMO.
    intros l' s' tws' sbs' cs' ST L1 L2 HN.
    pose proof (ok_s1 _ OK) as HS1. pose proof (ok_len _ OK) as HLEN. unfold S2_LEN_MAX in HLEN.
    pose proof (n_le_len _ _ HS1) as HNL.
    assert (HL32 : (blen (e_bs E) + 3 < 2^32)%Z) by lia.
    pose proof (tstep_step _ _ _ _ _ _ _ _ _ ST) as ST0.
    assert (HI : INV l' s') by (eapply step_inv; [exact HS1 | exact ST0 | apply Inv_s0; exact HS1]).
    apply (s2_labels (S (Z.to_nat (MU l' s'))) l' s' tws' sbs' cs'); [lia | exact HI |].
    pose proof (tstep_inv _ _ _ _ _ _ _ _ _ (Inv_s0 _ _ HS1) (TInv_s0 ck_any (Tf [h0]) (Tf [])) ST) as HT'.
    destruct l'; cbn [normal] in HN; try contradiction; cbn [GI]; (split; [exact L1|]; split; [exact L2| exact HT']).
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
    evt psegs Q
      (MS (mkR (e_ra E) (e_sp E) (e_gp E) (e_tp E) x5 x6 x7 (e_s0 E) (e_s1 E) (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (e_DOC E)) x12 x13 x14 x15 x16 x17
               (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E) x28 x29 x30 x31)
          F (Z_to_bv 64 0x2a918) fc None m1 (seg_rom psegs)).
  Proof using OK KX KS NUMA NUMO ROOTNUM.
    intros docv x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m1 HM.
    pose proof (ok_s1 _ OK) as HS1. pose proof (n_le_len _ _ HS1) as HNL. pose proof (ok_len _ OK) as HLEN. unfold S2_LEN_MAX in HLEN.
    assert (OK0 : env_ok E0) by (apply env_ok_ghost; exact OK).
    assert (L1 : Z.of_nat (length [h0]) = 1%Z) by reflexivity.
    assert (ATOM : forall c v, e_tok E 0 = c -> is_atomstart c = true -> atom_word v -> docend_k (G ([h0] ++ [v]) ([] ++ [])) Q (mkst 1 0 2 0 [])).
    { intros c v HT HA Hv. gn. rewrite <- HT in HA.
      to_LABK0 DocEnd (mkst (k s0 + 1) (depth s0) (W s0 + 1) (sb s0) (scopes s0)).
      eapply first_step; [ | reflexivity | reflexivity | exact I].
      apply tst_doc. apply tv_atom; cbn [gT gS gC]; [exact HA | apply (frameT_app [h0]); reflexivity | apply frameS_refl | ].
      cbn [k W sb depth scopes s0]. rewrite (Tf_app_r0 [h0] [v] 1%Z) by reflexivity. exact Hv. }
    apply (seg_entry E0 OK0 Q docv x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m1 HM L1 (KX _ _)).
    -
      intros HQ. apply (seg_root_str E0 OK0 Q HQ L1 eq_refl (KX _ _)). intros d cb HSO HCB. gn.
      to_LABK0 DocEnd (mkst (k s0 + 1) (depth s0) (W s0 + 1) (sb s0 + d + 5) (scopes s0)).
      eapply first_step; [ | reflexivity | lens | exact I].
      apply tst_doc. apply tv_string; cbn [gT gS gC];
        [exact HQ | exact HSO | rewrite !app_nil_r; apply (frameT_app [h0]); reflexivity | cbn [app]; apply (frameS_app [] (srec d cb) 0%Z); reflexivity
        | rewrite !app_nil_r; cbn [k W sb depth scopes s0]; rewrite (Tf_app_r0 [h0] _ 1%Z) by reflexivity; reflexivity
        | cbn [k W sb depth scopes s0 app]; pose proof (string_ok_lt _ _ 0%Z d HS1 ltac:(pose proof (n_pos _ _ HS1); lia) HSO); apply (wrote_str_app []); [reflexivity | exact HCB | lia] ].
    - exact ROOTNUM.
    - intros HT. gn. exact (seg_root_false E0 OK0 Q L1 (KX _ _) (ATOM _ _ HT eq_refl ltac:(right; left; reflexivity))).
    - intros HT. gn. exact (seg_root_null E0 OK0 Q L1 (KX _ _) (ATOM _ _ HT eq_refl ltac:(right; right; reflexivity))).
    - intros HT. gn. exact (seg_root_true E0 OK0 Q L1 (KX _ _) (ATOM _ _ HT eq_refl ltac:(left; reflexivity))).
    - intros H1 H2. gn.
      to_LABK0 ObjBegin (mkst (k s0 + 1) (depth s0) (W s0) (sb s0) (scopes s0)).
      eapply first_step; [ | reflexivity | reflexivity | exact I].
      apply tst_doc. apply tv_obj; cbn [gT gS gC]; [exact H1 | exact H2 | apply frameT_refl | apply frameS_refl].
    - intros H1 H2. gn.
      to_LABK0 DocEnd (mkst (k s0 + 2) (depth s0) (W s0 + 2) (sb s0) (scopes s0)).
      eapply first_step; [ | reflexivity | reflexivity | exact I].
      apply tst_doc. apply (tv_obj_empty _ _ _ _ s0 _ _ _ 0%Z); cbn [gT gS gC]; cbn [k W sb depth scopes s0];
        [exact H1 | exact H2 | apply (frameT_app [h0]); reflexivity | apply frameS_refl
        | rewrite (Tf_app_r0 [h0] _ 1%Z) by reflexivity; reflexivity | unfold ck_any, CNT_MAX; lia
        | rewrite (Tf_app_r [h0] _ 1%Z 1%Z) by (cbn; lia); reflexivity ].
    - intros H1 H2. gn.
      to_LABK0 ArrBegin (mkst (k s0 + 1) (depth s0) (W s0) (sb s0) (scopes s0)).
      eapply first_step; [ | reflexivity | reflexivity | exact I].
      apply tst_doc. apply tv_arr; cbn [gT gS gC]; [exact H1 | exact H2 | apply frameT_refl | apply frameS_refl].
    - intros H1 H2. gn.
      to_LABK0 DocEnd (mkst (k s0 + 2) (depth s0) (W s0 + 2) (sb s0) (scopes s0)).
      eapply first_step; [ | reflexivity | reflexivity | exact I].
      apply tst_doc. apply (tv_arr_empty _ _ _ _ s0 _ _ _ 0%Z); cbn [gT gS gC]; cbn [k W sb depth scopes s0];
        [exact H1 | exact H2 | apply (frameT_app [h0]); reflexivity | apply frameS_refl
        | rewrite (Tf_app_r0 [h0] _ 1%Z) by reflexivity; reflexivity | unfold ck_any, CNT_MAX; lia
        | rewrite (Tf_app_r [h0] _ 1%Z 1%Z) by (cbn; lia); reflexivity ].
  Qed.
End Main.

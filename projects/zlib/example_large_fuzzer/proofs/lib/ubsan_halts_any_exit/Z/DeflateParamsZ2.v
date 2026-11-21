(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateSafe DeflateOverlay.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSlow2 RefDeflSlow3 RefDeflSlow5 FillWinModel FlushBlockModel RefDeflateRel RefDeflSafeL1 RefDeflSafeZ RefDeflSafeG RefDeflFastM RefDeflFast1 RefDeflFast6 RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeS RefDeflSafeW RefDeflSafeT RefDeflSafeF RefDeflSafeFB RefDeflSafeFBT RefDeflSafeLM.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeI1 RefDeflSafeI2 RefDeflSafeI3 RefDeflSafeI4 RefDeflSafeLW RefDeflSafeLF RefDeflSafeL2 RefDeflSafeL3 RefDeflSafeL5 RefDeflSafeI6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateParamsDD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section SlowPQ.
  Variable c0 : cstrm.
  Variable s0 : deflate_state.
  Variable flush : Z.
  Hypothesis HC0 : C0OK' c0.
  Let HC0w : C0OK c0 := c0'_ok _ HC0.
  Let HFB : FB_CALL := FB_CALL_ok.

  Lemma TS_lv : forall a b, TS b = TS a -> lv b = lv a.
  Proof.
    intros a b E. pose proof (TS_fields _ _ E) as ((_ & _ & _ & _ & Elv & Esy) & _ & _ & _ & (_ & _ & _ & _ & _ & Elf & _) & _).
    unfold lv. rewrite Elv, Esy, Elf. reflexivity.
  Qed.
  Lemma PF_lv : forall a b, PF b = PF a -> lv b = lv a.
  Proof.
    intros a b E. pose proof (PF_fields _ _ E) as ((_ & _ & _ & _ & Elv & Esy) & _ & _ & (_ & _ & _ & _ & _ & Elf & _)).
    unfold lv. rewrite Elv, Esy, Elf. reflexivity.
  Qed.

  Lemma sfill_PQ : forall s, STI c0 s0 s -> PQ s -> PQ (fst (st_fill s flush)) /\ lv (fst (st_fill s flush)) = lv s.
  Proof.
    intros s HF HP. pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    unfold st_fill.
    destruct (Z.ltb_spec (ds_lookahead s) MIN_LOOKAHEAD) as [Hlt|Hge]; [| cbn [fst]; split; [exact HP | reflexivity]].
    assert (HP' : PQ (fill_window s) /\ lv (fill_window s) = lv s).
    { destruct (DC_fill_window c0 s HC0w HDC ltac:(rewrite Hm; discriminate) Hst Hlt) as (_ & _ & _ & R' & Eext & _).
      pose proof (fw_rest_fields _ _ R') as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & Elf & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ema & _) & (_ & _ & Elv & Est & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Esy & _) & _).
      split; [exact (PQ_of_fields s _ Ema Esy Eext HP) | unfold lv; rewrite Elv, Est, Elf; reflexivity]. }
    destruct (_ && _); [cbn [fst]; exact HP'|]. destruct (_ =? 0); cbn [fst]; exact HP'.
  Qed.

  Local Ltac absterm t x E := let H := fresh in assert (H : exists x0, x0 = t) by (eexists; reflexivity); destruct H as [x E]; rewrite <- E in *.

  Lemma sdecide_PQ : forall s1 s2 s4, STI c0 s0 s1 -> 1 <= ds_lookahead s1 -> ds_strstart s1 + MIN_LOOKAHEAD <= 2 * ds_w_size s1 ->
    SHREL s1 s2 -> SMREL s1 s2 s4 -> PQ (fst (st_decide s4)) /\ lv (fst (st_decide s4)) = lv s1.
  Proof.
    intros s1 s2 s4 HF1 Hl1 Hss1 HR MR.
    pose proof HF1 as (HDC1 & HK1 & Hp1 & Hm1 & Hst1 & Ho1).
    pose proof (STI_facts c0 s0 s1 HF1) as (D1 & X1 & V1 & Sw1 & Sh1 & Sl1 & Hma1 & Hml1 & Hpl1 & Hn1 & Hsn1 & Hse1 & Hstr1 & Hlook1 & Hsl1 & Hext1 & _).
    pose proof MR as (T4 & Estr4 & Elook4 & Esn4 & Epb4 & Elfc4 & Edfc4 & Ehd4 & Epv4 & Eih4 & Epl4 & Epm4 & Ema4 & Hml4 & Hms4 & Hlz4).
    pose proof (TS_fields _ _ T4) as (_ & _ & (Ebs4 & _) & _).
    unfold st_decide.
    destruct (dist_cond s4) eqn:Hdc.
    -
      pose proof (sdist_stage c0 s0 s1 s2 s4 HF1 Hl1 HR MR Hdc) as SD. cbv zeta in SD. destruct SD as (R & Ebf & Hml3 & Hmll & Hstr3 & HsD).
      pose proof (sdist_send c0 s0 s1 _ HF1 R Hml3 Hmll) as SE.
      absterm (fst (st_sdist s4)) s7 Es7. absterm (snd (st_sdist s4)) bf Ebf'.
      pose proof R as (T7 & Estr7 & _ & _ & Ema7 & _).
      pose proof (TS_fields _ _ T7) as (_ & _ & (Ebs7 & _) & _).
      unfold st_bflush. destruct bf.
      + rewrite flush_block_eq'.
        pose proof (send_facts c0 s0 HC0 s1 s7 (ds_match_length s1 - 1) 1 HF1 SE) as SF. cbv zeta in SF.
        destruct SF as (D7 & V7 & HK7 & Hp7 & Hm7 & Hst7 & Ho7 & Estrm7 & Hmeas7 & Hl7 & N7 & Ese7 & Elbs7 & X7 & FE7 & XX7 & B7).
        pose proof (flush_block_only_facts c0 s7 0 HFB HC0w D7 V7 XX7 FE7 Hst7 ltac:(rewrite Hm7; discriminate) B7) as FB. cbv zeta in FB.
        destruct FB as (_ & _ & _ & _ & EPF & _ & _ & _ & _ & _ & Esn' & _).
        pose proof (PF_fields _ _ EPF) as (_ & (_ & _ & _ & Ema' & _) & _).
        pose proof (PF_lv _ _ EPF) as Elv8. rewrite (TS_lv _ _ T7) in Elv8.
        absterm (flush_block_only s7 0) s8 Es8.
        destruct (cs_avail_out (ds_strm s8) =? 0); cbn [fst snd]; (split; [left; rewrite Ema', Ema7, Esn'; split; reflexivity | exact Elv8]).
      + cbn [fst snd]. split; [| exact (TS_lv _ _ T7)]. right. rewrite Estr7, Ebs7. clear - Hext1 Hml3. lia.
    - destruct (Z.eqb_spec (ds_match_available s4) 0) as [Hma0|Hma0]; cbn [negb].
      +
        unfold st_avail. cbn [fst snd]. split; [| etransitivity; [| exact (TS_lv _ _ T4)]; reflexivity]. right. dsred. rewrite Estr4, Ebs4. clear - Hext1. lia.
      +
        assert (Hma4 : ds_match_available s4 = 1) by (rewrite Ema4 in Hma0 |- *; clear - Hma1 Hma0; lia).
        pose proof (smid_facts c0 s0 HC0 s1 s2 s4 HF1 Hl1 HR MR Hdc Hma4) as SM. cbv zeta in SM.
        unfold st_slit.
        pose proof (tally_lit_facts s4 (arr_get (ds_window s4) (ds_strstart s4 - 1))) as (TK & _). cbv zeta in TK.
        destruct (tr_tally_lit s4 (arr_get (ds_window s4) (ds_strstart s4 - 1))) as [s5 b]. cbn [fst snd] in SM, TK |- *.
        destruct SM as (Ebf & D5 & V5 & XX5 & FE5 & HK5 & Ho5 & Hst5 & Hm5 & Estrm5 & Estr5 & Elook5 & Hstr11 & SE & Hma5 & Hml5 & H35 & Hext5 & N5 & Elbs5).
        pose proof (TS_lv _ _ (proj1 SE)) as Elv5. change (lv s5 = lv s1) in Elv5.
        absterm (if b then flush_block_only s5 0 else s5) s6 Es6. cbv zeta.
        split.
        * right. dsred. destruct b; subst s6.
          -- pose proof (flush_block_only_factsW c0 s5 0 HFB HC0w D5 V5 XX5 FE5 Hst5 ltac:(rewrite Hm5; discriminate)) as FB. cbv zeta in FB.
             destruct FB as (_ & _ & _ & _ & _ & Estr' & _ & Ebs' & _). rewrite Estr', Ebs'. clear. lia.
          -- destruct TK as (_ & _ & _ & _ & _ & Es5 & Eb5 & _). rewrite Es5, Eb5, Estr4, Ebs4. clear - Hext1. lia.
        * change (lv s6 = lv s1). destruct b; subst s6; [| exact Elv5].
          pose proof (flush_block_only_factsW c0 s5 0 HFB HC0w D5 V5 XX5 FE5 Hst5 ltac:(rewrite Hm5; discriminate)) as FB. cbv zeta in FB.
          destruct FB as (_ & _ & _ & _ & EPF & _). rewrite (PF_lv _ _ EPF). exact Elv5.
  Qed.

  Lemma strip_PQ : forall s, STI c0 s0 s -> PQ s -> PQ (fst (st_sbody s flush)) /\ lv (fst (st_sbody s flush)) = lv s.
  Proof.
    intros s HF HP. unfold st_sbody.
    pose proof (sfill_PQ s HF HP) as [HP1 Elv1].
    pose proof (sfill_stage c0 s0 flush HC0 s HF) as FS. cbv zeta in FS.
    destruct FS as (HF1 & Emeas & Hl0 & Hfw & Hl1r & Ews1 & Hnone & Hbrk & Hret & Hss1 & Hnc & _).
    absterm (fst (st_fill s flush)) s1 Es1.
    destruct (snd (st_fill s flush)) as [o|] eqn:Eo; [cbn [fst]; split; [exact HP1 | exact Elv1]|].
    pose proof (Hnone eq_refl) as Hl1.
    pose proof (shash_stage c0 s0 s1 HF1 Hl1) as HS. cbv zeta in HS. destruct HS as [HR Hlm].
    rewrite <- Ews1 in Hss1.
    pose proof (slm_stage c0 s0 s1 (fst (st_hash s1)) (snd (st_hash s1)) HF1 Hl1 Hss1 HR Hlm) as LM. cbv zeta in LM. destruct LM as [MR _].
    unfold st_srest. rewrite <- Elv1.
    exact (sdecide_PQ s1 (fst (st_hash s1)) (st_lm (prev_st (fst (st_hash s1))) (snd (st_hash s1))) HF1 Hl1 Hss1 HR MR).
  Qed.

  Lemma sloop_PQ : forall fuel s, STI c0 s0 s -> lz_meas s < Z.of_nat fuel -> PQ s ->
    PQ (fst (deflate_slow_loop fuel s flush)) /\ lv (fst (deflate_slow_loop fuel s flush)) = lv s.
  Proof.
    induction fuel as [|f IH]; intros s HF Hm HP; [cbn [deflate_slow_loop fst]; split; [exact HP | reflexivity]|].
    rewrite sloop_step'. pose proof (strip_PQ s HF HP) as [P1 Elv1]. destruct (sstep c0 s0 flush HC0 HFB s HF) as [_ OUT].
    absterm (fst (st_sbody s flush)) s2 Es2.
    destruct (snd (st_sbody s flush)) as [| |bs]; cbn [fst]; [| exact (conj P1 Elv1) | exact (conj P1 Elv1)].
    destruct OUT as [HF2 Hm2]. rewrite <- Elv1. apply IH; [exact HF2 | clear - Hm Hm2; lia | exact P1].
  Qed.

  Lemma stail_PQ : forall u, TAILOK c0 s0 u ->
    ds_match_available (fst (deflate_tail (tail_st u) flush)) = 0 /\ ds_sym_next (fst (deflate_tail (tail_st u) flush)) = 0
    /\ lv (fst (deflate_tail (tail_st u) flush)) = lv u.
  Proof.
    intros u (D & V & XX & B & HK & Ho & Hst & Hm & Hp & Hl0 & Hma0 & Hsn & Hstr & FE & XD & TI).
    pose proof (KV_fields _ _ HK) as (Ews & _). pose proof (dwf_sizes u D) as (Sw & _). pose proof (df_sl _ D) as Hsl.
    assert (Hv : 0 <= (if ds_strstart u <? MIN_MATCH - 1 then ds_strstart u else MIN_MATCH - 1) <= ds_strstart u
                 /\ (if ds_strstart u <? MIN_MATCH - 1 then ds_strstart u else MIN_MATCH - 1) <= ds_w_size u).
    { destruct (Z.ltb_spec (ds_strstart u) (MIN_MATCH - 1)); unfold MIN_MATCH in *; clear - Hstr Sw H; lia. }
    destruct (tail_insert_facts u _ (proj1 Hv) (proj2 Hv) D XX B FE XD) as (Dst & XXst & Bst & FEst & XDst).
    change (set_insert u (if ds_strstart u <? MIN_MATCH - 1 then ds_strstart u else MIN_MATCH - 1)) with (tail_st u) in Dst, XXst, Bst, FEst, XDst.
    assert (Efs : forall A (g : deflate_state -> A), (forall x v, g (set_insert x v) = g x) -> g (tail_st u) = g u) by (intros A g Hg; unfold tail_st; apply Hg).
    assert (Estrm : ds_strm (tail_st u) = ds_strm u) by (apply Efs; reflexivity).
    assert (Vst : SV c0 (tail_st u)) by (apply (SV_strm c0 u (tail_st u) Estrm V)).
    assert (Hmst : dmode (tail_st u) = 4) by (rewrite (Efs _ dmode) by reflexivity; exact Hm).
    assert (Hstst : ds_status (tail_st u) <> FINISH_STATE) by (rewrite (Efs _ ds_status) by reflexivity; exact Hst).
    assert (Hmast : ds_match_available (tail_st u) = 0) by (rewrite (Efs _ ds_match_available) by reflexivity; exact Hma0).
    assert (Elvt : lv (tail_st u) = lv u) by (apply Efs; reflexivity).
    absterm (tail_st u) u2 Eu2.
    assert (FB : forall last, 0 <= last <= 1 ->
      ds_match_available (flush_block_only u2 last) = 0 /\ ds_sym_next (flush_block_only u2 last) = 0 /\ lv (flush_block_only u2 last) = lv u).
    { intros last Hlast.
      pose proof (flush_block_only_facts c0 u2 last HFB HC0w Dst Vst XXst (FEst last Hlast) Hstst ltac:(rewrite Hmst; discriminate) Bst) as FBF. cbv zeta in FBF.
      destruct FBF as (_ & _ & _ & _ & EPF & _ & _ & _ & _ & _ & Esn' & _).
      pose proof (PF_fields _ _ EPF) as (_ & (_ & _ & _ & Ema' & _) & _).
      split; [rewrite Ema'; exact Hmast |]. split; [exact Esn' | rewrite (PF_lv _ _ EPF); exact Elvt]. }
    unfold deflate_tail. destruct (Z.eqb_spec flush Z_FINISH) as [F4|F4].
    - rewrite flush_block_eq'. destruct (FB 1 ltac:(clear; lia)) as (Hma' & Hsn' & Hlv').
      absterm (flush_block_only u2 1) s' Es'.
      destruct (cs_avail_out (ds_strm s') =? 0); cbn [negb Z.eqb fst snd]; repeat split; assumption.
    - destruct (Z.eqb_spec (ds_sym_next u2) 0) as [N0|N0]; cbn [negb fst snd].
      + split; [exact Hmast |]. split; [exact N0 | exact Elvt].
      + rewrite flush_block_eq'. destruct (FB 0 ltac:(clear; lia)) as (Hma' & Hsn' & Hlv').
        absterm (flush_block_only u2 0) s' Es'.
        destruct (cs_avail_out (ds_strm s') =? 0); cbn [negb Z.eqb fst snd]; repeat split; assumption.
  Qed.
End SlowPQ.

Theorem slow_PQ : forall c0 s flush, BFPRE c0 s flush -> dmode s = 4 -> PQ s ->
  PQ (fst (deflate_slow s flush)) /\ lv (fst (deflate_slow s flush)) = lv s.
Proof.
  intros c0 s flush (HC0 & HDC & Hp & Hst & Hfl) Hm HP.
  assert (HF : STI c0 s s).
  { split; [exact HDC|]. split; [reflexivity|]. split; [exact Hp|]. split; [exact Hm|]. split; [exact Hst | apply OUTLE_refl]. }
  pose proof HDC as [[D X] V].
  assert (Hmz : 0 <= lz_meas s) by (unfold lz_meas; pose proof (df_look _ D); pose proof (sv_ain _ _ V); lia).
  destruct (sloop c0 s flush HC0 FB_CALL_ok (lz_fuel s) s HF (lz_fuel_meas s Hmz)) as [_ HR].
  pose proof (sloop_PQ c0 s flush HC0 (lz_fuel s) s HF (lz_fuel_meas s Hmz) HP) as [LP Elv1].
  rewrite deflate_slow_eq.
  assert (EX : exists x, x = fst (deflate_slow_loop (lz_fuel s) s flush)) by (eexists; reflexivity). destruct EX as [s1 Es1]. rewrite <- Es1 in *.
  destruct (snd (deflate_slow_loop (lz_fuel s) s flush)) as [bs|]; [cbn [fst]; exact (conj LP Elv1)|].
  destruct HR as [HF1 Hl1]. cbv zeta.
  pose proof (STI_facts c0 s s1 HF1) as (D1 & X1 & V1 & _ & _ & _ & Hma1 & _).
  assert (EX : exists x, x = (if negb (ds_match_available s1 =? 0) then break1_st s1 else s1)) by (eexists; reflexivity). destruct EX as [u Eu].
  assert (TU : TAILOK c0 s u).
  { subst u. destruct (Z.eqb_spec (ds_match_available s1) 0) as [M0|M0]; cbn [negb].
    - exact (TAILOK_STI c0 s HC0 s1 HF1 Hl1 M0).
    - unfold break1_st. destruct (slit_tally_eq s1) as [E1 _]. rewrite <- E1.
      apply (TAILOK_lit c0 s HC0 s1 HF1 Hl1). clear - Hma1 M0. lia. }
  assert (Elvu : lv u = lv s1).
  { subst u. destruct (negb (ds_match_available s1 =? 0)); [| reflexivity]. reflexivity. }
  rewrite <- Eu. destruct (stail_PQ c0 s flush HC0 u TU) as (Hma' & Hsn' & Hlv'). split; [left; split; [exact Hma' | exact Hsn'] | rewrite Hlv', Elvu; exact Elv1].
Qed.

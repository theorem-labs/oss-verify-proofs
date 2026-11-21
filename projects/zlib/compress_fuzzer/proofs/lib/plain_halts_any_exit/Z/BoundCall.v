(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateSafe DeflateOverlay.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateRel RefDeflSafeZ RefDeflSafeG RefDeflSafeFB.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI1 RefDeflSafeI2 RefDeflSafeI3 RefDeflSafeI4 RefDeflSafeI6.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflProgress.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BoundArith BoundDefs BoundFw BoundTfb BoundMc BoundSlow BoundCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac fit3_l2_prune :=
  repeat match goal with
         | H : _ \/ _ |- _ => clear H
         | H : ?fit3A -> ?fit3B |- _ => clear H
         | H : _ <-> _ |- _ => clear H
         | H : exists _, _ |- _ => clear H
         end.
Local Ltac lia ::= first [ solve [ fit3_l2_prune; Zify.zify; xlia zchecker ] | Zify.zify; xlia zchecker ].

Definition AposI (IN : Z) (s : deflate_state) : Z := IN - ds_lookahead s - (ds_strstart s - ds_block_start s).

Record HI (ds : deflate_state) (z : zstrm) : Prop := {
  hi_dd : DD ds;
  hi_lvl : ds_level ds = 6;
  hi_strat : ds_strategy ds = 0;
  hi_lbs : ds_lit_bufsize ds = 16384;
  hi_ws : ds_w_size ds = 32768;
  hi_shape : SHAPE ds;
  hi_cov : ds_status ds <> FINISH_STATE -> COV ds;
  hi_apos : 0 <= AposI (zs_total_in z) ds;
  hi_budget : zs_total_out z + Mloc ds <= phi0 (AposI (zs_total_in z) ds) + paid ds;
  hi_gz : ds_gzhead ds = 0;
  hi_ins : ds_insert ds = 0 \/ ds_status ds = FINISH_STATE }.

Lemma wrap64_sub_inj : forall a b c, wrap64 (a - b) = wrap64 c -> 0 <= a < 2 ^ 64 -> 0 <= c + b < 2 ^ 64 -> a = c + b.
Proof.
  intros a b c E Ha Hc. rewrite !wrap64_mod in E.
  assert (E2 : a mod 2 ^ 64 = (c + b) mod 2 ^ 64).
  { replace a with ((a - b) + b) at 1 by lia. rewrite Z.add_mod by lia. rewrite E. rewrite <- Z.add_mod by lia. reflexivity. }
  rewrite !Z.mod_small in E2 by lia. exact E2.
Qed.

Lemma entry_fields : forall ds c,
  let s0 := set_strm ds c in
  ds_level s0 = ds_level ds /\ ds_strategy s0 = ds_strategy ds /\ ds_lit_bufsize s0 = ds_lit_bufsize ds /\ ds_w_size s0 = ds_w_size ds
  /\ ds_status s0 = ds_status ds /\ ds_wrap s0 = ds_wrap ds /\ ds_strstart s0 = ds_strstart ds
  /\ ds_lookahead s0 = ds_lookahead ds /\ ds_block_start s0 = ds_block_start ds
  /\ ds_pending s0 = ds_pending ds /\ ds_bi_valid s0 = ds_bi_valid ds /\ ds_strm s0 = c
  /\ ds_pending_buf s0 = ds_pending_buf ds /\ ds_sym_next s0 = ds_sym_next ds /\ ds_match_available s0 = ds_match_available ds
  /\ ds_match_length s0 = ds_match_length ds /\ ds_match_start s0 = ds_match_start ds.
Proof. intros ds c s0. subst s0. repeat split; reflexivity. Qed.

Lemma zlength_cs_output : forall c, zlength (cs_output c) = Z.of_nat (length (cs_out_rev c)).
Proof. intros c. unfold cs_output, zlength. rewrite rev_append_rev, app_nil_r, length_rev. reflexivity. Qed.

Theorem bcall : forall ds zc flush, HI ds (zc_strm zc) -> dcall_wf zc -> flush = Z_NO_FLUSH \/ flush = Z_FINISH ->
  (flush = Z_NO_FLUSH -> 0 < zlength (zc_input zc) /\ ds_status ds <> FINISH_STATE) ->
  (ds_status ds = FINISH_STATE -> zlength (zc_input zc) = 0) ->
  0 < zc_avail_out zc ->
  zs_total_in (zc_strm zc) + zlength (zc_input zc) < 2 ^ 64 -> zs_total_out (zc_strm zc) + zc_avail_out zc < 2 ^ 64 ->
  let r := deflate_m ds zc flush in
  HI (fst r) (zr_strm (snd r))
  /\ (zr_rc (snd r) = Z_OK \/ (flush = Z_FINISH /\ zr_rc (snd r) = Z_STREAM_END /\ ds_status (fst r) = FINISH_STATE))
  /\ (flush = Z_NO_FLUSH -> ds_status (fst r) <> FINISH_STATE)
  /\ (ds_status (fst r) = FINISH_STATE -> zr_consumed (snd r) = zlength (zc_input zc))
  /\ zs_total_in (zr_strm (snd r)) = zs_total_in (zc_strm zc) + zr_consumed (snd r)
  /\ zs_total_out (zr_strm (snd r)) = zs_total_out (zc_strm zc) + zlength (zr_output (snd r))
  /\ 0 <= zr_consumed (snd r) <= zlength (zc_input zc) /\ 0 <= zlength (zr_output (snd r)) <= zc_avail_out zc
  /\ zstrm_okP (zr_strm (snd r)) /\ bytes_okP (zr_output (snd r))
  /\ (zr_rc (snd r) = Z_OK -> 0 < zr_consumed (snd r) + zlength (zr_output (snd r))).
Proof.
  intros ds zc flush HI0 Hzc HFL HNF HFIN Hao Hti Hto. cbv zeta.
  set (c0 := cstrm_of_call zc). set (IN0 := zs_total_in (zc_strm zc)).
  pose proof (C0OK'_of_call zc Hzc) as HC0. fold c0 in HC0.
  destruct (entry_fields ds c0) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17).
  assert (H0 : DC c0 (set_strm ds c0)) by (split; [apply DD_set_strm; exact (hi_dd _ _ HI0) | subst c0; apply SV_entry; exact Hzc]).
  unfold deflate_m. fold c0.
  set (s0 := set_strm ds c0) in *.
  pose proof H0 as [[D0 X0] V0].
  assert (Ec0 : cs_next_in c0 = 0 /\ cs_avail_in c0 = zlength (zc_input zc) /\ cs_out_rev c0 = [] /\ cs_avail_out c0 = zc_avail_out zc
                /\ cs_total_in c0 = IN0 /\ cs_total_out c0 = zs_total_out (zc_strm zc) /\ arr_len (cs_input c0) = zlength (zc_input zc)).
  { subst c0 IN0. unfold cstrm_of_call. cbn [cs_next_in cs_avail_in cs_out_rev cs_avail_out cs_total_in cs_total_out cs_input].
    rewrite arr_len_of_list. repeat split; reflexivity. }
  destruct Ec0 as (N0 & A0 & O0 & AO0 & TI0 & TO0 & IL0).
  assert (EA0 : Apos IN0 s0 = AposI IN0 ds) by (unfold Apos, AposI; rewrite F12, N0, F8, F7, F9; lia).
  assert (EM0 : Mc s0 = Mloc ds) by (unfold Mc, olen, Mloc; rewrite F12, O0, F10, F11; reflexivity).
  assert (EP0 : paid s0 = paid ds) by (unfold paid; rewrite F5, F6; reflexivity).
  assert (C0 : CI c0 s0 IN0 s0).
  { constructor.
    - split; [exact H0 | reflexivity].
    - rewrite F1. exact (hi_lvl _ _ HI0).
    - rewrite F2. exact (hi_strat _ _ HI0).
    - reflexivity.
    - unfold SHAPE. rewrite F5, F6, F7. exact (hi_shape _ _ HI0).
    - rewrite F5. intros N. apply (COV_same ds s0); try assumption.
      + rewrite F7, F9. reflexivity.
      + unfold nbP. rewrite F9, F4, F7. exact (cv_nb _ (hi_cov _ _ HI0 N)).
      + rewrite F7, F17. reflexivity.
      + exact (hi_cov _ _ HI0 N).
    - rewrite EA0. exact (hi_apos _ _ HI0).
    - rewrite F5. intros E. rewrite AIN_def, F12, A0. exact (HFIN E).
    - apply Z.le_refl.
    - exact (hi_gz _ _ HI0).
    - rewrite F5. exact (hi_ins _ _ HI0). }
  assert (HNF' : flush = Z_NO_FLUSH -> 0 < cs_avail_in c0 /\ ds_status s0 <> FINISH_STATE)
    by (intros F; rewrite A0, F5; exact (HNF F)).
  assert (PRGR : RES c0 s0 (deflate_core s0 flush)).
  { apply (core_prog c0 s0 HC0 F12 D0 flush (conj H0 eq_refl)); [rewrite F2; exact (hi_strat _ _ HI0) | |].
    - destruct HFL as [-> | ->]; unfold Z_NO_FLUSH, Z_FINISH; lia.
    - destruct HFL as [F|F]; [right; split; [exact F | exact (proj1 (HNF' F))] | left; exact F]. }
  pose proof (bcore c0 s0 IN0 HC0 F12 D0 FB_CALL_ok ltac:(rewrite F3; exact (hi_lbs _ _ HI0)) ltac:(rewrite F4; exact (hi_ws _ _ HI0))
                flush C0 HFL HNF' ltac:(rewrite AO0; exact Hao)) as (C1 & RC & NF1).
  destruct PRGR as [_ PRGR].
  destruct (deflate_core s0 flush) as [s1 rc]. cbn [fst snd] in C1, RC, NF1, PRGR |- *.
  unfold zret_of_cs. cbn [zr_strm zr_rc zr_consumed zr_output zstrm_of_cs zs_total_in zs_total_out].
  pose proof (ci_st _ _ _ _ C1) as [[[D1 X1] V1] K1].
  pose proof (sv_nin _ _ V1) as Ni. pose proof (sv_inlen _ _ V1) as Il. pose proof (sv_ain _ _ V1) as Ai.
  pose proof (sv_out _ _ V1) as Ou. pose proof (sv_aout _ _ V1) as Ao. pose proof (sv_tin _ _ V1) as Ti. pose proof (sv_tout _ _ V1) as To.
  rewrite O0 in Ou, To. unfold zlen in Ou, To. cbn [length Z.of_nat] in Ou, To. rewrite IL0 in Il. rewrite AO0 in Ou. rewrite TO0 in To.
  destruct Hzc as ((Hz1 & Hz2 & _) & _).

  assert (ETI : cs_total_in (ds_strm s1) = IN0 + cs_next_in (ds_strm s1)).
  { apply wrap64_sub_inj; [| exact Ti | subst IN0; lia].
    pose proof (ci_fwT _ _ _ _ C1) as E. unfold fwT in E. rewrite F12, TI0, N0, Z.sub_0_r in E. exact E. }

  assert (ETO : cs_total_out (ds_strm s1) = zs_total_out (zc_strm zc) + Z.of_nat (length (cs_out_rev (ds_strm s1)))).
  { rewrite To. rewrite Z.sub_0_r. apply wrap64_id. lia. }
  rewrite zlength_cs_output.
  split.
  { pose proof (KV_fields _ _ K1) as (Kw & _ & Kl & _).
    assert (EA1 : AposI (cs_total_in (ds_strm s1)) s1 = Apos IN0 s1) by (unfold AposI, Apos; rewrite ETI; reflexivity).
    constructor; unfold zstrm_of_cs; cbn [zs_total_in zs_total_out].
    - exact (conj D1 X1).
    - exact (ci_lvl _ _ _ _ C1).
    - exact (ci_strat _ _ _ _ C1).
    - rewrite Kl, F3. exact (hi_lbs _ _ HI0).
    - rewrite Kw, F4. exact (hi_ws _ _ HI0).
    - exact (ci_shape _ _ _ _ C1).
    - exact (ci_cov _ _ _ _ C1).
    - rewrite EA1. exact (ci_apos _ _ _ _ C1).
    - rewrite EA1, ETO. pose proof (ci_G _ _ _ _ C1) as G. unfold Gs in G. rewrite EA0, EM0, EP0 in G.
      pose proof (hi_budget _ _ HI0) as B. fold IN0 in B. unfold Mc, olen in G. lia.
    - exact (ci_gz _ _ _ _ C1).
    - exact (ci_ins _ _ _ _ C1). }
  split; [exact RC|]. split; [exact NF1|].
  split; [intros E; pose proof (ci_fin _ _ _ _ C1 E) as A; rewrite AIN_def in A; lia|].
  split; [exact ETI|]. split; [exact ETO|]. split; [lia|]. split; [lia|].
  split.
  { unfold zstrm_okP, zstrm_of_cs. cbn [zs_total_in zs_total_out zs_adler zs_data_type].
    split; [exact Ti|]. split; [rewrite ETO; lia|]. split; [exact (sv_adler _ _ V1) | exact (sv_dt _ _ V1)]. }
  split.
  { unfold bytes_okP, cs_output. rewrite rev_append_rev, app_nil_r. apply Forall_rev. exact (sv_outb _ _ V1). }
  intros Erc. destruct (PRGR Erc) as [_ PR]. rewrite A0, AO0 in PR. clear - PR Il Ou Ni Ai Ao Hao. lia.
Qed.

Lemma HI_total_out : forall ds z, HI ds z -> zs_total_out z <= phi0 (zs_total_in z) + 11.
Proof.
  intros ds z H. pose proof (hi_budget _ _ H) as B. pose proof (hi_apos _ _ H) as A. destruct (hi_dd _ _ H) as [D X].
  pose proof (df_pend _ D) as (_ & P & _). pose proof (df_bi _ D) as ((Bv & _) & _).
  pose proof (df_look _ D) as L.
  assert (SB : 0 <= ds_strstart ds - ds_block_start ds).
  { pose proof (dx_ext _ X) as E. rewrite (dmode4 ds (hi_lvl _ _ H) (hi_strat _ _ H)) in E. specialize (E ltac:(lia)). lia. }
  assert (Hm : 0 <= Mloc ds) by (unfold Mloc; pose proof (cdiv8_nonneg (ds_bi_valid ds) Bv); lia).
  assert (Hp : paid ds <= 11) by (unfold paid; destruct (_ =? INIT_STATE), (_ =? FINISH_STATE), (_ <=? 0); lia).
  pose proof (phi0_mono (AposI (zs_total_in z) ds) (zs_total_in z) ltac:(unfold AposI in *; lia)). lia.
Qed.

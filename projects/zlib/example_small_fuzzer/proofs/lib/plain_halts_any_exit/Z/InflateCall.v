(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZProg ZIface InflateState Inftrees InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inftrees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InflateFast OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefZApi RefInflateRel RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeS3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefZApi OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefUpdWin1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflate_runA.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeD RefInflateSafeH RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeS3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeS3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeS3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeD OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeK OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeS1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeS2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateEqS RefInflateEqB InflateFrameIn HarnessSmall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section CallI.
  Variable flush : Z.

  Lemma FI_W0 : forall s zc, FI (zs_total_in (zc_strm zc)) (zlength (zc_input zc)) (zlength (zc_input zc)) (W0 s zc).
  Proof.
    intros s zc. unfold FI, W0, icall_of_zcall. cbn [w_c w_r ic_total_in ir_in ic_input ir_ret]. rewrite arr_len_of_list.
    repeat split; try reflexivity; unfold Z_OK; lia.
  Qed.

  Definition IPOST2 (zc : ZCall) (p : inflate_state * ZRet) : Prop :=
    let zr := snd p in
    (zr_rc zr = Z_OK ->
       0 <= zr_consumed zr <= zlength (zc_input zc)
       /\ zs_total_in (zr_strm zr) = wrap64 (zs_total_in (zc_strm zc) + zr_consumed zr)
       /\ 0 < zr_consumed zr + zlength (zr_output zr))
    /\ - 2 ^ 31 <= zr_rc zr < 2 ^ 31.

  Lemma ret_model_ok : forall in_ out r, ret_model flush in_ out r = Z_OK -> in_ <> 0 \/ out <> 0.
  Proof.
    intros in_ out r. unfold ret_model.
    destruct (Z.eqb_spec in_ 0) as [E1|E1]; [| intros _; left; exact E1].
    destruct (Z.eqb_spec out 0) as [E2|E2]; [| intros _; right; exact E2].
    cbn [andb orb]. destruct (Z.eqb_spec (ir_ret r) Z_OK) as [E3|E3]; [intros H; discriminate H | intros H; contradiction].
  Qed.

  Lemma ret_model_range : forall in_ out r, - 2 ^ 31 <= ir_ret r < 2 ^ 31 -> - 2 ^ 31 <= ret_model flush in_ out r < 2 ^ 31.
  Proof. intros in_ out r H. unfold ret_model. destruct (_ && _); [unfold Z_BUF_ERROR; lia | exact H]. Qed.

  Theorem inflate_m_post2 : forall s zc ch p,
    INV s -> ZC zc -> ipure (inflate_m ivar_ref hooks_pure s zc flush) ch = Some p -> IPOST2 zc p.
  Proof.
    intros s zc ch p HI Hz E. pose proof Hz as (Hao & Hlen & Hby). pose proof (zlength_nonneg (zc_input zc)) as LN.
    unfold ipure in E. rewrite (inflate_m_W0 hooks_pure) in E by (apply INV_check; exact HI).
    destruct (Z.eq_dec (is_mode s) MEM) as [EM|NM].
    - rewrite (inf_loop_MEM flush (W0 s zc)) in E; cycle 1.
      { unfold W0, s_entry. cbn [w_s]. rewrite EM. change (MEM =? TYPE) with false. cbv iota. exact EM. }
      { cbn [W0 w_c icall_of_zcall ic_avail_in]. lia. }
      { cbn [W0 w_c icall_of_zcall ic_avail_out]. lia. }
      unfold sret in E. cbn [fst] in E. injection E; intros <-. unfold IPOST2. cbn [snd zret_of_icall zr_rc].
      split; [intros X; discriminate X | unfold Z_MEM_ERROR; lia].
    - destruct (WINV_entry' s zc HI Hz) as [HW HP].
      assert (HB : BK (zc_avail_out zc) (zs_total_out (zc_strm zc)) (W0 s zc)).
      { unfold BK, caseA. cbn [W0 w_s w_c w_r icall_of_zcall ic_outbuf ic_total_out ir_out]. unfold arr_make. rewrite arr_len_init.
        split; [reflexivity|]. unfold s_entry.
        assert (NS : is_mode s <> SYNC) by (intros ES; destruct HI as (_ & _ & HM); rewrite ES in HM; exact HM).
        destruct (Z.eqb_spec (is_mode s) TYPE) as [ET|ET]; sacc; [split; [discriminate|]; split; [discriminate|] | split; [exact NM|]; split; [exact NS|]]; left; split; reflexivity. }
      pose proof (inf_loop_bk flush (zc_avail_out zc) (zs_total_out (zc_strm zc)) (W0 s zc) HW HB HP) as L.
      pose proof (inf_loop_fi _ _ _ flush (W0 s zc) (FI_W0 s zc)) as LF.
      destruct (inf_loop ivar_ref flush (W0 s zc)) as [stop [s' c' r']]. destruct L as (HW' & HB' & HR'). cbn [fst snd] in LF.
      unfold WINV in HW'. cbn [w_s w_c w_r] in HW'. destruct HW' as (_ & HREG & _).
      pose proof HREG as (RN & RH & RNH & RP & RL & RPL & _ & _ & RNI & RNO).
      destruct HB' as (B1 & B2 & B3 & HAB). unfold caseA, caseB in HAB. cbn [w_s w_c w_r] in B1, B2, B3, HAB.
      destruct stop as [|rc].
      +
        destruct LF as (LF1 & LF2 & LF3 & LF4). cbn [w_c w_r] in LF1, LF2, LF3, LF4.
        rewrite (inf_leave_eq hooks_pure) in E. unfold sbind in E.
        assert (TAIL : forall s2 ch',
                  match @sret CH _ (lv_fin flush s2 (c_rest c' r') r') ch' with MRet q => Some (fst q) | _ => None end = Some p -> IPOST2 zc p).
        { intros s2 ch' X. unfold sret in X. cbn [fst] in X. injection X; intros <-. unfold IPOST2, lv_fin. cbv zeta.
          match goal with |- context [if ?cnd then _ else _] => destruct cnd end;
            cbn [fst snd zret_of_icall zr_output zr_rc zr_strm zr_consumed zstrm_of_icall zs_total_in];
            unfold c_rest; sacc; rewrite arr_slice_length.
          all: (split; [| apply ret_model_range; exact LF4]).
          all: intros Hrc; apply ret_model_ok in Hrc.
          all: rewrite LF2, LF1 in *.
          all: replace (zlength (zc_input zc) - ir_have r') with (ir_next r') in * by (clear - RNH LF3; lia).
          all: rewrite (wrap32_id (ir_next r')) in * by (clear - RN RH RNH RNI LF3; lia).
          all: split; [clear - RN RH RNH LF3; lia|]; split; [reflexivity|].
          all: rewrite Z.max_r by exact RP.
          all: destruct Hrc as [Hin|Hout]; [clear - Hin RN RP; lia|].
          all: destruct HAB as [[A1 A2]|(C1 & C2 & C3)]; rewrite ?A2, ?C2 in Hout.
          1,3: replace (zc_avail_out zc - ir_left r') with (ir_put r') in Hout by (clear - B1 RPL; lia);
               rewrite wrap32_id in Hout by (clear - B1 RPL RP RL RNO; lia); clear - Hout RN RP; lia.
          all: exfalso; apply Hout; replace (ir_left r' - ir_left r') with 0 by lia; reflexivity. }
        destruct (lv_cond flush (s_rest s' r') (c_rest c' r') r').
        * rewrite updatewindow_pure in E. cbn [mbind fst snd] in E.
          destruct (uw_pure (s_rest s' r') _ _ _ ch) as [s2|].
          -- exact (TAIL s2 ch E).
          -- unfold sret in E. injection E; intros <-. unfold IPOST2, lv_mem. cbn [fst snd zret_of_icall zr_rc].
             split; [intros X; discriminate X | unfold Z_MEM_ERROR; lia].
        * unfold sret at 1 in E. cbn [mbind fst snd] in E. exact (TAIL (s_rest s' r') ch E).
      +
        unfold sret in E. cbn [fst] in E. injection E; intros <-. destruct HR' as [-> Hno].
        unfold IPOST2. cbn [fst snd zret_of_icall zr_rc]. split; [intros X; discriminate X | unfold Z_NEED_DICT; lia].
  Qed.
End CallI.

Theorem inflate_INV' : forall s zc flush ch s' zr,
  INV s -> ZC zc -> ipure (inflate_m ivar_ref hooks_pure s zc flush) ch = Some (s', zr) -> INV s'.
Proof.
  intros s zc flush ch s' zr HI Hz E.
  unfold ipure in E. rewrite (inflate_m_W0 hooks_pure) in E by (apply INV_check; exact HI).
  destruct (WINV_entry' s zc HI Hz) as [HW HP].
  pose proof (inf_loop_post flush (W0 s zc) HW HP) as L.
  destruct (inf_loop ivar_ref flush (W0 s zc)) as [stop w'].
  destruct stop as [|rc].
  - destruct L as [HW' _]. destruct w' as [s1 c1 r1].
    destruct (inf_leave hooks_pure flush (mkW s1 c1 r1) ch) as [p| | |] eqn:EL; try discriminate E.
    destruct p as [[s2 zr2] ch']. cbn [fst] in E.
    assert (E2 : s2 = s') by (injection E; intros _ X; exact X). subst s2.
    exact (inf_leave_INV flush s1 c1 r1 ch s' zr2 ch' HW' EL).
  - destruct L as [_ HI']. unfold sret in E. cbn [fst] in E.
    assert (E2 : w_s w' = s') by (injection E; intros _ X; exact X). rewrite <- E2. exact HI'.
Qed.


Lemma updatewindow_dh : forall s src end_ copy ans,
  updatewindow dhooks s src end_ copy [ans]
  = MRet (uw_pure s src end_ copy ans, match is_window_blk s with Some _ => [ans] | None => [] end).
Proof.
  intros s src end_ copy ans. rewrite updatewindow_unfold. unfold uw_pure.
  destruct (is_window_blk s) as [b|].
  - unfold sbind at 1. unfold sret at 1. cbn [mbind fst snd]. rewrite updw_body_eq. reflexivity.
  - unfold sbind. cbn [zalloc dhooks mbind fst snd sret].
    destruct ans as [[b g]|]; cbn [mbind fst snd]; [rewrite updw_body_eq|]; reflexivity.
Qed.

Lemma inflate_p_pure : forall ans s zc flush, inflateStateCheck s = false ->
  ipure (inflate_m ivar_ref hooks_pure s zc flush) ans = Some (fst (inflate_p ans s zc flush)).
Proof.
  intros ans s zc flush Hc. unfold inflate_p, ipure.
  rewrite (inflate_m_W0 dhooks), (inflate_m_W0 hooks_pure) by exact Hc.
  destruct (inf_loop ivar_ref flush (W0 s zc)) as [stop [s' c' r']]. destruct stop as [|rc].
  - rewrite !inf_leave_eq. unfold sbind. destruct (lv_cond flush (s_rest s' r') (c_rest c' r') r').
    + rewrite updatewindow_dh, updatewindow_pure. cbn [mbind fst snd].
      destruct (uw_pure (s_rest s' r') _ _ _ ans) as [s2|]; unfold sret; cbn [fst snd]; reflexivity.
    + unfold sret. cbn [mbind fst snd]. reflexivity.
  - unfold sret. cbn [fst snd]. reflexivity.
Qed.

Lemma inflate_p_check : forall ans s zc flush, inflateStateCheck s = true ->
  inflate_p ans s zc flush = ((s, zret_of_icall (icall_of_zcall zc) Z_STREAM_ERROR), false).
Proof. intros ans s zc flush Hc. unfold inflate_p, inflate_m. rewrite Hc. reflexivity. Qed.

Lemma inflate_p_refused : forall b g s zc flush,
  snd (inflate_p (Some (b, g)) s zc flush) = true ->
  zr_rc (snd (fst (inflate_p None s zc flush))) = Z_MEM_ERROR.
Proof.
  intros b g s zc flush. destruct (inflateStateCheck s) eqn:Hc.
  - rewrite (inflate_p_check _ s zc flush Hc). cbn [snd]. intros H; discriminate H.
  - unfold inflate_p. rewrite (inflate_m_W0 dhooks) by exact Hc.
    destruct (inf_loop ivar_ref flush (W0 s zc)) as [stop [s' c' r']]. destruct stop as [|rc].
    2:{ unfold sret. cbn [fst snd]. intros H; discriminate H. }
    rewrite !inf_leave_eq. unfold sbind. destruct (lv_cond flush (s_rest s' r') (c_rest c' r') r').
    2:{ unfold sret. cbn [mbind fst snd]. intros H; discriminate H. }
    rewrite !updatewindow_dh. cbn [mbind fst snd]. unfold uw_pure.
    destruct (is_window_blk (s_rest s' r')) as [b0|].
    + unfold sret. cbn [fst snd]. intros H; discriminate H.
    + intros _. unfold sret, lv_mem. cbn [fst snd zret_of_icall zr_rc]. reflexivity.
Qed.

Lemma inflate_p_refused_zr : forall b g s zc flush,
  snd (inflate_p (Some (b, g)) s zc flush) = true ->
  let zn := snd (fst (inflate_p None s zc flush)) in
  let zg := snd (fst (inflate_p (Some (b, g)) s zc flush)) in
  zr_consumed zn = zr_consumed zg /\ zr_output zn = zr_output zg /\ zr_strm zn = zr_strm zg /\ zr_rc zn = Z_MEM_ERROR.
Proof.
  intros b g s zc flush. cbv zeta. destruct (inflateStateCheck s) eqn:Hc.
  - rewrite !(inflate_p_check _ s zc flush Hc). cbn [snd]. intros H; discriminate H.
  - unfold inflate_p. rewrite (inflate_m_W0 dhooks) by exact Hc.
    destruct (inf_loop ivar_ref flush (W0 s zc)) as [stop [s' c' r']]. destruct stop as [|rc].
    2:{ unfold sret. cbn [fst snd]. intros H; discriminate H. }
    rewrite !inf_leave_eq. unfold sbind. destruct (lv_cond flush (s_rest s' r') (c_rest c' r') r').
    2:{ unfold sret. cbn [mbind fst snd]. intros H; discriminate H. }
    rewrite !updatewindow_dh. cbn [mbind fst snd]. unfold uw_pure.
    destruct (is_window_blk (s_rest s' r')) as [b0|].
    + unfold sret. cbn [fst snd]. intros H; discriminate H.
    + intros _. unfold sret. cbn [fst snd]. rewrite lv_fin_pre, lv_pre_updw, lv_pre_fresh. unfold lv_mem.
      cbn [fst snd zret_of_icall zr_consumed zr_output zr_strm zr_rc]. repeat split; reflexivity.
Qed.

Theorem inflate_p_rc_range : forall ans s zc flush, - 2 ^ 31 <= zr_rc (snd (fst (inflate_p ans s zc flush))) < 2 ^ 31.
Proof.
  intros ans s zc flush. destruct (inflateStateCheck s) eqn:Hc.
  - rewrite (inflate_p_check ans s zc flush Hc). cbn [fst snd zret_of_icall zr_rc]. unfold Z_STREAM_ERROR. lia.
  - unfold inflate_p. rewrite (inflate_m_W0 dhooks) by exact Hc.
    pose proof (inf_loop_fi _ _ _ flush (W0 s zc) (FI_W0 s zc)) as LF.
    destruct (inf_loop ivar_ref flush (W0 s zc)) as [stop [s' c' r']]. cbn [fst snd] in LF.
    destruct stop as [|rc].
    + destruct LF as (_ & _ & _ & LF4). cbn [w_r] in LF4.
      rewrite inf_leave_eq. unfold sbind. destruct (lv_cond flush (s_rest s' r') (c_rest c' r') r').
      * rewrite updatewindow_dh. cbn [mbind fst snd].
        destruct (uw_pure (s_rest s' r') _ _ _ ans) as [s2|]; unfold sret; cbn [fst snd].
        -- unfold lv_fin. cbv zeta. match goal with |- context [if ?cnd then _ else _] => destruct cnd end;
             cbn [fst snd zret_of_icall zr_rc]; apply ret_model_range; exact LF4.
        -- unfold lv_mem. cbn [fst snd zret_of_icall zr_rc]. unfold Z_MEM_ERROR. lia.
      * unfold sret. cbn [mbind fst snd]. unfold lv_fin. cbv zeta. match goal with |- context [if ?cnd then _ else _] => destruct cnd end;
          cbn [fst snd zret_of_icall zr_rc]; apply ret_model_range; exact LF4.
    + destruct LF as [_ LR]. unfold sret. cbn [fst snd zret_of_icall zr_rc]. exact LR.
Qed.

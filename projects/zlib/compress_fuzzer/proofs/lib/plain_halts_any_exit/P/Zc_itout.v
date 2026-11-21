(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface InflateState Inftrees InflateFast InflateArms Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefZApi RefInflateRel RefUpdWin1 RefInflate_runA.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeD RefInflateSafeH RefInflateSafeK RefInflateSafeS1 RefInflateSafeS2 RefInflateSafeS3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateEqS RefInflateEqB InflateFrameIn HarnessSmall InflateCall ZApiInst ZApiInstC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma inflate_m_tout_range : forall flush s zc ch p,
  INV s -> ZC zc -> 0 <= zs_total_out (zc_strm zc) < 2 ^ 64 ->
  ipure (inflate_m ivar_ref hooks_pure s zc flush) ch = Some p ->
  0 <= zs_total_out (zr_strm (snd p)) < 2 ^ 64.
Proof.
  intros flush s zc ch p HI Hz HT E. pose proof Hz as (Hao & Hlen & Hby). pose proof (zlength_nonneg (zc_input zc)) as LN.
  unfold ipure in E. rewrite (inflate_m_W0 hooks_pure) in E by (apply INV_check; exact HI).
  destruct (Z.eq_dec (is_mode s) MEM) as [EM|NM].
  - rewrite (inf_loop_MEM flush (W0 s zc)) in E; cycle 1.
    { unfold W0, s_entry. cbn [w_s]. rewrite EM. change (MEM =? TYPE) with false. cbv iota. exact EM. }
    { cbn [W0 w_c icall_of_zcall ic_avail_in]. lia. }
    { cbn [W0 w_c icall_of_zcall ic_avail_out]. lia. }
    unfold sret in E. cbn [fst] in E. injection E; intros <-.
    cbn [snd W0 w_c zret_of_icall zr_strm zstrm_of_icall icall_of_zcall ic_total_out zs_total_out]. exact HT.
  - destruct (WINV_entry' s zc HI Hz) as [HW HP].
    assert (HB : BK (zc_avail_out zc) (zs_total_out (zc_strm zc)) (W0 s zc)).
    { unfold BK, caseA. cbn [W0 w_s w_c w_r icall_of_zcall ic_outbuf ic_total_out ir_out]. unfold arr_make. rewrite arr_len_init.
      split; [reflexivity|]. unfold s_entry.
      assert (NS : is_mode s <> SYNC) by (intros ES; destruct HI as (_ & _ & HM); rewrite ES in HM; exact HM).
      destruct (Z.eqb_spec (is_mode s) TYPE) as [ET|ET]; sacc; [split; [discriminate|]; split; [discriminate|] | split; [exact NM|]; split; [exact NS|]]; left; split; reflexivity. }
    pose proof (inf_loop_bk flush (zc_avail_out zc) (zs_total_out (zc_strm zc)) (W0 s zc) HW HB HP) as L.
    destruct (inf_loop ivar_ref flush (W0 s zc)) as [stop [s' c' r']]. destruct L as (HW' & HB' & HR').
    destruct HB' as (B1 & B2 & B3 & HAB). unfold caseA, caseB in HAB. cbn [w_s w_c w_r] in B1, B2, B3, HAB.
    assert (TC : 0 <= ic_total_out c' < 2 ^ 64).
    { destruct HAB as [[A1 _]|(C1 & _)]; rewrite ?A1, ?C1; [exact HT| apply wrap64_range]. }
    destruct stop as [|rc].
    +
      rewrite (inf_leave_eq hooks_pure) in E. unfold sbind in E.
      assert (TPRE : 0 <= ic_total_out (snd (lv_pre (s_rest s' r') (c_rest c' r') r')) < 2 ^ 64).
      { unfold lv_pre. cbv zeta. match goal with |- context [if ?cnd then _ else _] => destruct cnd end; cbn [snd]; sacc; apply wrap64_range. }
      assert (TAIL : forall s2 ch',
                match @sret CH _ (lv_fin flush s2 (c_rest c' r') r') ch' with MRet q => Some (fst q) | _ => None end = Some p ->
                0 <= zs_total_out (zr_strm (snd p)) < 2 ^ 64).
      { intros s2 ch' X. unfold sret in X. cbn [fst] in X. injection X; intros <-. rewrite lv_fin_pre. cbn [snd zret_of_icall zr_strm zstrm_of_icall zs_total_out].
        unfold lv_pre. cbv zeta. match goal with |- context [if ?cnd then _ else _] => destruct cnd end; cbn [snd]; sacc; apply wrap64_range. }
      destruct (lv_cond flush (s_rest s' r') (c_rest c' r') r').
      * rewrite updatewindow_pure in E. cbn [mbind fst snd] in E.
        destruct (uw_pure (s_rest s' r') _ _ _ ch) as [s2|].
        -- exact (TAIL s2 ch E).
        -- unfold sret in E. injection E; intros <-. unfold lv_mem. cbn [fst snd zret_of_icall zr_strm zstrm_of_icall zs_total_out]. exact TPRE.
      * unfold sret at 1 in E. cbn [mbind fst snd] in E. exact (TAIL (s_rest s' r') ch E).
    +
      unfold sret in E. cbn [fst] in E. injection E; intros <-.
      cbn [snd zret_of_icall zr_strm zstrm_of_icall zs_total_out]. exact TC.
Qed.

Lemma zic_total_out_range : forall inp x aout ok,
  INV (iz_s x) -> bytes_ok inp -> zlength inp < 2 ^ 32 -> 0 <= aout < 2 ^ 32 ->
  0 <= zs_total_out (iz_z x) < 2 ^ 64 ->
  let '(x', _, _, _) := zic_inflate inp x aout ok in 0 <= zs_total_out (iz_z x') < 2 ^ 64.
Proof.
  intros inp x aout ok HI Hb Hl Ha HT. unfold zic_inflate.
  set (zc := mkZCall inp aout (iz_z x)).
  assert (Hz : ZC zc) by (unfold ZC, zc; cbn [zc_avail_out zc_input]; repeat split; try lia; exact Hb).
  pose proof (inflate_p_pure (wans ok) (iz_s x) zc Z_NO_FLUSH (INV_check _ HI)) as EP.
  destruct (inflate_p (wans ok) (iz_s x) zc Z_NO_FLUSH) as [[s' zr] asked] eqn:EIP. cbn [fst] in EP.
  pose proof (inflate_m_tout_range Z_NO_FLUSH (iz_s x) zc (wans ok) (s', zr) HI Hz HT EP) as R. cbn [snd iz_z] in R |- *. exact R.
Qed.

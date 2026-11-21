(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Spec Require ZApiL ZHarnessL.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateParams.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState Inftrees InflateFast InflateArms Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefZApi RefInflateRel RefInflate_runA RefInflateSafeD RefInflateSafeS2 RefInflateEqS RefInflateEqB.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateCall HarnessSmall HarnessLarge ZApiInst ZApiOk ZApiInstL InflatePsi InflatePsiS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition drc4 (rc : Z) : Prop := rc = Z_OK \/ rc = Z_STREAM_END \/ rc = Z_STREAM_ERROR \/ rc = Z_BUF_ERROR.

Lemma drc4_cint : forall rc, drc4 rc -> ZHarnessL.cint rc.
Proof. intros rc [-> |[-> |[-> | ->]]]; unfold ZHarnessL.cint, Z_OK, Z_STREAM_END, Z_STREAM_ERROR, Z_BUF_ERROR; lia. Qed.

Lemma zlib_header_rc : forall s, snd (deflate_zlib_header s) = None \/ snd (deflate_zlib_header s) = Some Z_OK.
Proof. intros s. unfold deflate_zlib_header. cbv zeta. destruct (negb (ds_pending _ =? 0)); cbn [snd]; auto. Qed.

Lemma gzip_header_rc : forall s, snd (deflate_gzip_header s) = None \/ snd (deflate_gzip_header s) = Some Z_OK.
Proof. intros s. unfold deflate_gzip_header. cbv zeta. destruct (negb (ds_pending _ =? 0)); cbn [snd]; auto. Qed.

Lemma trailer_rc : forall s, drc4 (snd (deflate_trailer s)).
Proof. intros s. unfold deflate_trailer. cbv zeta. cbn [snd]. destruct (negb (ds_pending _ =? 0)); unfold drc4; auto. Qed.

Lemma blocks_rc : forall s flush, snd (deflate_blocks s flush) = None \/ snd (deflate_blocks s flush) = Some Z_OK.
Proof.
  intros s flush. unfold deflate_blocks.
  match goal with |- context [if ?c then _ else (s, None)] => destruct c end; [|left; reflexivity].
  destruct (run_compress_func s flush) as [s1 b]. cbv zeta.
  destruct (block_state_eqb b need_more || block_state_eqb b finish_started); [right; reflexivity|].
  destruct (block_state_eqb b block_done); [|left; reflexivity].
  destruct (cs_avail_out _ =? 0); [right; reflexivity | left; reflexivity].
Qed.

Lemma deflate_core_rc : forall s flush, drc4 (snd (deflate_core s flush)).
Proof.
  intros s flush. unfold deflate_core.
  destruct (deflateStateCheck s || (Z_BLOCK <? flush) || (flush <? 0)); [cbn [snd]; unfold drc4; auto|].
  destruct ((ds_status s =? FINISH_STATE) && negb (flush =? Z_FINISH)); [cbn [err_return snd]; unfold drc4; auto|].
  destruct (cs_avail_out (ds_strm s) =? 0); [cbn [err_return snd]; unfold drc4; auto|].
  cbv zeta.
  match goal with |- drc4 (snd (let '(s0, r) := ?t in _)) => destruct t as [s1 [rc1|]] eqn:E1 end.
  { cbn [snd]. revert E1.
    destruct (negb (ds_pending _ =? 0)); [destruct (cs_avail_out _ =? 0); intros E1; [injection E1; intros <- _; unfold drc4; auto | discriminate E1]|].
    destruct (_ && _ && _); intros E1; [| discriminate E1]. unfold err_return in E1. injection E1; intros <- _. unfold drc4; auto. }
  clear E1.
  destruct ((ds_status s1 =? FINISH_STATE) && negb (cs_avail_in (ds_strm s1) =? 0)); [cbn [err_return snd]; unfold drc4; auto|].
  set (s2 := if (ds_status s1 =? INIT_STATE) && (ds_wrap s1 =? 0) then set_status s1 BUSY_STATE else s1). clearbody s2.
  match goal with |- drc4 (snd (let '(s0, r) := ?t in _)) => destruct t as [s3 [rc3|]] eqn:E3 end.
  { cbn [snd]. revert E3. destruct (ds_status s2 =? INIT_STATE); intros E3; [| discriminate E3].
    destruct (zlib_header_rc s2) as [X|X]; rewrite E3 in X; cbn [snd] in X; [discriminate X | injection X; intros ->; unfold drc4; auto]. }
  clear E3.
  match goal with |- drc4 (snd (let '(s0, r) := ?t in _)) => destruct t as [s4 [rc4|]] eqn:E4 end.
  { cbn [snd]. revert E4. destruct (ds_status s3 =? GZIP_STATE); intros E4; [| discriminate E4].
    destruct (gzip_header_rc s3) as [X|X]; rewrite E4 in X; cbn [snd] in X; [discriminate X | injection X; intros ->; unfold drc4; auto]. }
  clear E4.
  destruct (deflate_blocks s4 flush) as [s5 [rc5|]] eqn:E5.
  { cbn [snd]. destruct (blocks_rc s4 flush) as [X|X]; rewrite E5 in X; cbn [snd] in X; [discriminate X | injection X; intros ->; unfold drc4; auto]. }
  destruct (negb (flush =? Z_FINISH)); [cbn [snd]; unfold drc4; auto|].
  destruct (ds_wrap s5 <=? 0); [cbn [snd]; unfold drc4; auto|].
  apply trailer_rc.
Qed.

Lemma deflate_m_rc : forall s zc flush, drc4 (zr_rc (snd (deflate_m s zc flush))).
Proof.
  intros s zc flush. unfold deflate_m. cbv zeta.
  pose proof (deflate_core_rc (set_strm s (cstrm_of_call zc)) flush) as H.
  destruct (deflate_core _ flush) as [s' rc]. cbn [snd zret_of_cs zr_rc] in *. exact H.
Qed.


Section Loop.

  Lemma il_step_done : forall N comprc x is',
    0 <= N < 2 ^ 32 -> zlength comprc = N -> Forall (fun b => 0 <= b < 256) comprc -> ILI N x ->
    ZHarnessL.il_stepP zinstL N comprc x = inr (ZHarnessL.IRLdone is') ->
    0 <= zs_total_out (iz_z is') < 2 ^ 64.
  Proof.
    intros N comprc x is' HN Hlen Hby [HI HT].
    unfold ZHarnessL.il_stepP, ZHarnessL.i_callL. cbn [ZApiL.il_inflate ZApiL.il_total_in zinstL]. unfold zil_inflate.
    set (inp := Prelim.zdrop (zs_total_in (iz_z x)) comprc).
    assert (Hinp : zlength inp = N - zs_total_in (iz_z x)).
    { subst inp. unfold Prelim.zdrop. unfold zlength. rewrite length_skipn. unfold zlength in Hlen. lia. }
    set (zc := mkZCall inp N (iz_z x)).
    assert (Hz : ZC zc).
    { unfold ZC. subst zc. cbn [zc_avail_out zc_input]. split; [lia|]. split; [lia|].
      subst inp. unfold bytes_ok, Prelim.zdrop. apply Forall_skipn'. exact Hby. }
    pose proof (inflate_p_pure (wans true) (iz_s x) zc Z_NO_FLUSH (INV_check _ HI)) as EP.
    pose proof (inflate_m_post Z_NO_FLUSH (iz_s x) zc (wans true) _ HI Hz EP) as [_ P2].
    destruct (inflate_p (wans true) (iz_s x) zc Z_NO_FLUSH) as [[s' zr] asked]. cbn [fst snd] in P2, EP.
    destruct (Z.eqb_spec (zr_rc zr) ZApi.Z_STREAM_END) as [E1|N1].
    - intros X. injection X; intros <-. cbn [iz_z]. rewrite (P2 ltac:(right; exact E1)). apply wrap64_range.
    - destruct (zr_rc zr =? ZApi.Z_OK); intros X; discriminate X.
  Qed.

  Lemma il_loop_nat2 : forall N comprc n x,
    0 <= N < 2 ^ 32 -> zlength comprc = N -> Forall (fun b => 0 <= b < 256) comprc -> ILI N x -> IM N x < Z.of_nat n ->
    match ZHarnessL.iterNL n (ZHarnessL.il_stepP zinstL N comprc) x with
    | inl _ => False
    | inr ZHarnessL.IRLstuck => False
    | inr (ZHarnessL.IRLdone is') => 0 <= zs_total_out (iz_z is') < 2 ^ 64
    | inr (ZHarnessL.IRLerr _) => True
    end.
  Proof.
    intros N comprc n. induction n as [|n IH]; intros x HN Hlen Hby HX HM.
    { exfalso. pose proof (IM_nonneg N x HX). cbn in HM. lia. }
    cbn [ZHarnessL.iterNL]. pose proof (il_step N comprc x HN Hlen Hby HX) as ST.
    pose proof (il_step_done N comprc x) as SD.
    destruct (ZHarnessL.il_stepP zinstL N comprc x) as [x'|r].
    - destruct ST as [HX' HM']. apply IH; try assumption. lia.
    - destruct r as [is'|rc|]; [exact (SD is' HN Hlen Hby HX eq_refl) | exact I | exact (ST eq_refl)].
  Qed.

  Theorem iloopL_total2 : forall size comprc,
    1 <= size <= ZApiL.ZL_MAX -> zlength comprc = ZApiL.NofL size -> Forall (fun b => 0 <= b < 256) comprc ->
    match ZHarnessL.iloopL_pure zinstL (ZApiL.NofL size) comprc (ZApiL.il_init zinstL) with
    | ZHarnessL.IRLstuck => False
    | ZHarnessL.IRLdone is' => 0 <= zs_total_out (iz_z is') < 2 ^ 64
    | ZHarnessL.IRLerr _ => True
    end.
  Proof.
    intros size comprc Hsz Hlen Hby.
    unfold ZApiL.ZL_MAX in Hsz. unfold ZApiL.NofL in *.
    set (N := 100 + 3 * size) in *.
    unfold ZHarnessL.iloopL_pure. rewrite ZHarnessL.iterZL_nat.
    assert (HX0 : ILI N (ZApiL.il_init zinstL)).
    { cbn [ZApiL.il_init zinstL]. unfold zi_init, ILI. cbn [iz_s iz_z]. split; [exact INV_is0|].
      destruct iz0_totals as [-> _]. lia. }
    assert (HM0 : IM N (ZApiL.il_init zinstL) < Z.of_nat (Z.to_nat (ZHarnessL.ZIL_FUEL N))).
    { cbn [ZApiL.il_init zinstL]. unfold zi_init, IM. cbn [iz_s iz_z]. destruct iz0_totals as [-> _]. destruct is0_bits_pend as [B0 P0].
      unfold PSIq. rewrite B0, P0. pose proof (ZIL_FUEL_enough N ltac:(lia)). rewrite Z2Nat.id by (unfold ZHarnessL.ZIL_FUEL; lia). lia. }
    pose proof (il_loop_nat2 N comprc (Z.to_nat (ZHarnessL.ZIL_FUEL N)) (ZApiL.il_init zinstL) ltac:(lia) Hlen Hby HX0 HM0) as L.
    destruct (ZHarnessL.iterNL _ _ _) as [x'|r]; [destruct L|exact L].
  Qed.

End Loop.


Lemma zil_shape : forall P : inflate_state * ZRet * bool,
  (let '(r, _) := P in let '(s', zr) := r in (mkIZ s' (zr_strm zr), zr_consumed zr, zr_output zr, zr_rc zr))
  = (mkIZ (fst (fst P)) (zr_strm (snd (fst P))), zr_consumed (snd (fst P)), zr_output (snd (fst P)), zr_rc (snd (fst P))).
Proof. intros [[s' zr] w]. reflexivity. Qed.

Theorem zinstL_ok : ZHarnessL.zapiL_ok zinstL.
Proof.
  constructor.
  - cbn [ZApiL.il_total_in ZApiL.il_total_out ZApiL.il_init zinstL]. unfold zi_init. cbn [iz_z]. exact iz0_totals.
  - cbn [ZApiL.zl_dstate ZApiL.zl_dwin ZApiL.zl_dprev ZApiL.zl_dhead ZApiL.zl_dpend ZApiL.zl_isize ZApiL.zl_wsize zinstL].
    repeat constructor; lia.
  - intros inp x aout flush. cbn [ZApiL.dl_deflate zinstL]. unfold zdl_deflate.
    pose proof (deflate_m_rc (dz_s x) (mkZCall inp aout (dz_z x)) flush) as H.
    destruct (deflate_m _ _ flush) as [s' zr]. cbn [snd] in *. apply drc4_cint. exact H.
  - intros x. cbn [ZApiL.dl_end zinstL]. unfold dend_rc, ZHarnessL.cint, Z_STREAM_ERROR, Z_DATA_ERROR, Z_OK.
    destruct (deflateStateCheck _); [lia|]. destruct (_ =? _); lia.
  - intros inp x aout ok. cbn [ZApiL.il_inflate zinstL]. unfold zil_inflate.
    pose proof (inflate_p_rc_range (wans ok) (iz_s x) (mkZCall inp aout (iz_z x)) Z_NO_FLUSH) as H.
    destruct (inflate_p _ _ _ _) as [[s' zr] w]. cbn [fst snd] in *. exact H.
  - intros x. cbn [ZApiL.il_end zinstL]. unfold iend_rc, ZHarnessL.cint, Z_STREAM_ERROR, Z_OK.
    destruct (inflateStateCheck _); lia.
  - intros inp x aout Hw. cbn [ZApiL.il_inflate ZApiL.il_wants_window zinstL] in *. unfold zil_inflate, zil_wants_window in *.
    rewrite !zil_shape. cbn [fst snd].
    split; [exact (inflate_p_refused _ _ _ _ _ Hw) | exact (inflate_p_out_same (6%N, g0) (iz_s x) (mkZCall inp aout (iz_z x)) Z_NO_FLUSH)].
  - intros size comprc Hsz Hlen Hby.
    pose proof (iloopL_total2 size comprc Hsz Hlen Hby) as L.
    cbn [ZApiL.il_total_out zinstL].
    destruct (ZHarnessL.iloopL_pure _ _ _ _) as [is'|rc|]; [exact L | exact I | exact L].
Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z119 FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf SjTape Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim Stdio Zpb Z3o.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Zvw Z4d.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks Zkt Zi4 D_defs D_kit D_clx Z87 Z82 I_lkit Sj_rtf Zpm Zpl Zq2 Zq3
  Sj_new Zpt Zps Zpo Zwn Zsl Z4a Z73 Z5g Z6m Z71 Z5h Z5i Z5j
  Z6q Z6y Z6p Z45 Z5k Z4e Z4l Z4m Z4n Z4o Z52 Z57 Z5b Z4q.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Top3.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis AF : art_facts RT.
Hypothesis PDT : pdtor_cps RT (pdone RT).
Hypothesis VDES : vdestroy_cpsA RT.

Local Ltac nomod := repeat match goal with H : _ mod _ = _ |- _ => clear H end.
Local Ltac ul := unfold FUZZ_STACK, ATPA_SPLITINTO_STACK, ATPA_SPLIT_STACK, ATPA_PUSH_STACK, ATPA_DESTROY_STACK, PID_STACK, GSTR_STACK_A in *;
                 unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma lftoi_tail : forall (Σ Σx : rts RT) PMc (m mx : mem) (usp sp' f A lo d : Z) (bs : list byte)
    (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 s2x s6x s7x s8x u3 u4 u5 u6 : word) (Fx : bvmap 5 word) (fcx : bv 32) (h3 t : list byte),
  fdfs_only PMc -> mat_stable PMc ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d < SEGTOP_A)) ->
  rt_frames RT Σ = [] -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= usp -> usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
  lp_inv RT LIB Σ Σx m mx usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A ->
  pdone RT Σx mx (f + 96) (vblockA A (vcap_iter (atp_P (chars bs)) 0 0) (Z.of_nat (atp_P (chars bs))) ++ rt_live RT Σ) ->
  rt_credit RT Σ - FUZZ_COST <= rt_credit RT Σx ->
  usp - 304 <= sp' <= usp - 288 -> sp' mod 32 = 0 -> 0 < f -> f mod 64 = 0 -> f + 256 <= rt_sp0 RT Σ - STACK_WIN ->
  (f + 256 <= 0x10000 \/ SEGTOP_A <= f) -> (f + 256 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 32 <= f) ->
  SHB <= f / 8 + 2147450880 -> f / 8 + 2147450880 + 32 + 1 <= rt_sp0 RT Σ - STACK_WIN -> frm0 fcx ->
  cps_f (ASTA RT Σx PMc (eq (sa_regs e_pdtor (Z_to_bv 64 0x96e80) sp' gp (Z_to_bv 64 0x653c30) u0 u1 u2 usp (Z_to_bv 64 (f + 96)) v1 v2 v3 v4 v5 v6 v7 f s2x s6x s7x s8x
                                       u3 u4 u5 u6 Fx fcx mx)))
    (fin_postA RT LIB Σ PMc usp lo ra gp (Z_to_bv 64 0x653c30) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m).
Proof using LIB_loc AF PDT VDES.
  intros Σ Σx PMc m mx usp sp' f A lo d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 s2x s6x s7x s8x u3 u4 u5 u6 Fx fcx h3 t
    FDO MST INLV FRS0 LVPOS LOW LOR SPT SPA INVx PD CRx SPR SPA' FPOS F64 FR1' FSEG2 FSELF SHB0 SHT FRM.
  intros T c (Hc & FC0) Hk. unfold sa_regs in Hc.
  pose proof INVx as (ARTx & MIx & STx & (j0 & j1 & j2 & j4 & jq & je & jo & jn & jr & j13 & FRlx) & STpx & FRsx & FHx & FSx & VRx & BSx & LIBx & PRESx & FRSx & SPx).
  pose proof (af_sp0_range RT AF Σx mx ARTx) as SP0R. rewrite SPx in SP0R.
  set (P := atp_P (chars bs)) in *. set (S := f / 8 + 2147450880) in *. set (capv := vcap_iter P 0 0) in *. set (L0 := vblockA A capv (Z.of_nat P) ++ rt_live RT Σ) in *.
  assert (SHF : shad (f + 256) = S + 32) by (subst S; unfold shad, SHB; Z.div_mod_to_equations; lia).
  assert (SHS : shad f = S) by reflexivity.
  assert (EU1 : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; ul).
  assert (EUSP : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; ul).
  assert (P2 : (2 <= P)%nat) by (subst P; unfold atp_P; lia).
  pose proof (vcap_iter_inv P 0 0 ltac:(lia) ltac:(lia)) as CAPI. rewrite Z.add_0_l in CAPI. fold capv in CAPI.
  assert (INCL0 : forall e, In e (rt_live RT Σ) -> In e L0) by (intros e He; subst L0; apply in_or_app; right; exact He).
  assert (INA0 : In (A, 16 * Z.of_nat P) L0).
  { subst L0. apply in_or_app. left. unfold vblockA. destruct (Z.eqb_spec capv 0); [lia|]. apply ann_block_vis. }

  apply (PDT Σx PMc (Z_to_bv 64 0x96e80) (Z_to_bv 64 sp') gp (Z_to_bv 64 0x653c30) u0 u1 u2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') (Z_to_bv 64 (f + 96)) v1 v2 v3 v4 v5 v6 v7
           s2x (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120)) s6x s7x s8x (Z_to_bv 64 S) (Z_to_bv 64 f) (Z_to_bv 64 2147450880)
           u3 u4 u5 u6 Fx fcx mx (f + 96) L0 lo FDO MST eq_refl eq_refl PD ARTx MIx);
    [.. | split; [subst S; exact Hc| apply (cfrm0_of_asta RT Σx PMc (eq _) c Hc); intros ms0 <-; exact FRM] |].
  - rewrite EU1. exact STx.
  - rewrite SPx. exact LOW.
  - rewrite EU1. ul.
  - rewrite EU1. ul.
  - rewrite EU1. clear - SPA'. Z.div_mod_to_equations. lia.
  - unfold unwind_ok. rewrite EU1, EUSP. right; right. lia.
  - exact FRM.
  - intros cq ((Σq & Hcq & LVq & FRSq & SPq & CRq) & FCq).
    destruct (ASTA_unpack_f RT Σq _ _ cq Hcq FCq) as (msq & (vq & mq & RSq & (ARTq & MIq & STq) & PRESq) & FRMq & Hcq'). clear Hcq.
    destruct RSq as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & Fq & fcq & ->).
    cbn [ms_fcsr] in FRMq. rewrite EU1 in STq, PRESq. rewrite (ret_pc_even 0x96e80) in Hcq' by lia.
    assert (FRSq' : rt_frames RT Σq = [(f, 2%nat)]) by (rewrite FRSq; exact FRSx).
    assert (INFq : In (f, 2%nat) (rt_frames RT Σq)) by (rewrite FRSq'; left; reflexivity).
    assert (INCLq : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σq)) by (rewrite LVq; exact INCL0).
    assert (INAq : In (A, 16 * Z.of_nat P) (rt_live RT Σq)) by (rewrite LVq; exact INA0).
    assert (EQq : forall a : word, lp_dom RT Σ usp sp' f A d bs (bv_unsigned a) -> mq a = mx a).
    { intros a Ha. apply PRESq.
      - rewrite <- LVq, <- FRSq. exact (lp_client RT AF Σ Σq mq usp sp' f lo d A bs ARTq FRSq' FRS0 INCLq INAq INLV FPOS F64 ltac:(lia) SPT _ Ha).
      - cbn [outside]. split; [| exact I].
        exact (lp_apart_frame RT AF Σ Σq mq usp sp' f lo d A (f + 96) (f + 96 + 80) bs ARTq FRSq' FRS0 ltac:(rewrite SPq; exact SPx) INCLq INAq INLV LOW LOR ltac:(lia) FSELF ltac:(lia) ltac:(lia) _ Ha). }
    pose proof (lp_inv_xfer' RT LIB LIB_loc Σ Σx Σq m mx mq usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A INVx ltac:(lia) FRSq SPq ARTq MIq STq EQq) as INVq.
    clear EQq PRESq Hc INVx PD.
    pose proof INVq as (_ & _ & _ & (k0 & k1 & k2 & k4 & kq & ke & ko & kn & kr & k13 & FRlq) & STpq & FRsq & FHq & FSq & VRq & BSq & LIBq & PRESq & _ & SPq').
    pose proof (fframe_ranges RT AF Σq mq f 2 ARTq INFq) as (_ & _ & _ & _ & SHTq). change (fs_size 2) with 256 in SHTq. rewrite SHF, SPq' in SHTq.
    pose proof (af_frames_range RT AF Σq mq f 2%nat ARTq INFq) as (_ & _ & _ & FLVq). change (fs_size 2) with 256 in FLVq.
    pose proof (af_fshadow_apart RT AF Σq mq f 2 ARTq INFq) as (FSLq & _). change (fs_size 2) with 256 in FSLq. rewrite SHF, SHS in FSLq.
    pose proof (af_live_range RT AF Σq mq A _ ARTq INAq) as (AR0 & AR1 & AR2). rewrite SPq' in AR1.
    pose proof (FLVq A _ INAq) as AFL. pose proof (FSLq A _ INAq) as ASL.

    unfold fa_locals2 in FRlq.
    lazymatch type of FRlq with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?rest) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: rest) with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9] ++ [c10] ++ rest) in FRlq end.
    apply Zvw.rw_cells_app in FRlq. destruct FRlq as [X1q FRlq]. apply Zvw.rw_cells_app in FRlq. destruct FRlq as [RESq X3q].
    cbn [cells_size csize Nat.add] in X1q, RESq, X3q. replace (sp' + Z.of_nat 136) with (sp' + 136) in RESq, X3q by lia. replace (sp' + 136 + Z.of_nat 24) with (sp' + 160) in X3q by lia.

    pose proof (fa_walk12 usp sp' f (Z_to_bv 64 0x96e80) gp (Z_to_bv 64 0x653c30) w0 w1 w2 vq g1 g2 g3 g4 g5 g6 g7 s2x s6x s7x s8x w3 w4 w5 w6 t kr Fq fcq mq
                  FPOS ltac:(ul) ltac:(apply Z.div_pos; lia) ltac:(subst S; ul) ltac:(ul) ltac:(ul) ltac:(subst S; exact FSELF) ltac:(subst S; clear - SHTq LOW LOR SPR; ul) FSq RESq MIq) as W12.
    fold S in W12. unfold sa_regs in W12.
    lazymatch type of W12 with evt bsegs _ ?X =>
      assert (W12' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W12) end.
    clear W12.
    apply (cps_realizes bsegs _ _ _ cq (asta_evt_c RT AF Σq PMc _ _ MST W12') ltac:(subst S; exact Hcq')). clear W12'. intros c13 Hc13.
    destruct (ASTA_unpack RT Σq _ _ c13 Hc13) as (ms13 & (m13 & jr' & -> & MU13 & WM13 & MI13 & FS13 & RC13) & Hc13'). clear Hc13.
    assert (ART13 : ART RT Σq m13).
    { apply (art_client_write RT AF Σq mq m13 sp' ARTq ltac:(rewrite SPq'; ul)); [| exact WM13].
      intros a Ha. apply MU13. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Ha.
      - right; right; right; right. exists f, 2%nat. change (fs_size 2) with 256. rewrite SHF, SHS. split; [exact INFq| lia].
      - left. ul. }
    assert (AG13 : agree_on (fun x => ~ (S + 12 <= x < S + 22) /\ ~ (sp' + 136 <= x < sp' + 144)) mq m13).
    { apply (agree_of_munch _ _ _ _ MU13). intros x (H1 & H2). cbn [outside]. repeat split; assumption. }
    assert (X1_13 : rw_cells bsegs m13 sp' [CB 8 k0; CB 8 k1; CB 8 k2; C8 (Z_to_bv 64 f); CB 16 k4; C8 (Z_to_bv 64 f); CB 24 kq; CB 16 ke; CB 24 ko; CB 16 kn]).
    { apply (rw_cells_agree bsegs mq m13 _ _ X1q); [| exact WM13]. eapply agree_sub; [exact AG13|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta.
      clear - Hx SHTq LOW LOR SPR. subst S. split; ul. }
    assert (X3_13 : rw_cells bsegs m13 (sp' + 160) [C8 (Z_to_bv 64 (d + Z.of_nat (length bs))); C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 7 k13]).
    { apply (rw_cells_agree bsegs mq m13 _ _ X3q); [| exact WM13]. eapply agree_sub; [exact AG13|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta.
      clear - Hx SHTq LOW LOR SPR. subst S. split; ul. }
    assert (STp13 : stk bsegs m13 (sp' + 184) (usp - 104)).
    { apply (stk_agree bsegs mq m13 _ _ STpq); [| exact WM13]. eapply agree_sub; [exact AG13|]. intros x Hx. cbv beta in *. clear - Hx SHTq LOW LOR SPR. subst S. split; ul. }
    assert (ST13 : stk bsegs m13 lo sp').
    { apply (stk_agree bsegs mq m13 _ _ STq); [| exact WM13]. eapply agree_sub; [exact AG13|]. intros x Hx. cbv beta in *. clear - Hx SHTq LOW LOR SPR. subst S. split; ul. }
    assert (FRs13 : rw_cells bsegs m13 (usp - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
    { apply (rw_cells_agree bsegs mq m13 _ _ FRsq); [| exact WM13]. eapply agree_sub; [exact AG13|]. intros x Hx. unfold fa_saved in Hx. cbn [cells_size csize Nat.add] in Hx.
      cbv beta. clear - Hx SHTq LOW LOR SPR. subst S. split; ul. }
    assert (FH13 : rw_cells bsegs m13 f (fz_hdr (C8 (Z_to_bv 64 0x41b58ab3)) (C8 (Z_to_bv 64 0x1e816)) (C8 (Z_to_bv 64 0x96ab0)) h3)).
    { apply (rw_cells_agree bsegs mq m13 _ _ FHq); [| exact WM13]. eapply agree_sub; [exact AG13|]. intros x Hx. unfold fz_hdr in Hx. cbn [cells_size csize Nat.add] in Hx.
      cbv beta. clear - Hx FSELF FR1' LOW LOR SPR. subst S. split; ul. }
    assert (LIB13 : LIB m13).
    { apply (LIB_agree2 LIB LIB_loc mq m13 LIBq). eapply agree_sub; [exact AG13|]. intros x Hx. pose proof (proj2 (lib_fp_static x Hx)) as R. cbv beta.
      clear - R SHB0 SP0R LOW LOR SPR. subst S. unfold SHB in *. split; ul. }
    assert (VR13 : vrepA m13 (f + 32) A capv (Z.of_nat P) (atp_elsA d (chars bs))).
    { destruct VRq as (E & R & C & A0 & AH & SV & BLK). unfold vrepA. split; [exact E|]. split; [exact R|]. split; [exact C|]. split; [exact A0|]. split; [exact AH|].
      split. { apply (rw_cells_agree bsegs mq m13 _ _ SV); [| exact WM13]. eapply agree_sub; [exact AG13|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta.
               clear - Hx FSELF FR1' LOW LOR SPR. subst S. split; ul. }
      destruct BLK as [B|(CQ1 & A16 & ASG & EL)]; [left; exact B| right]. split; [exact CQ1|]. split; [exact A16|]. split; [exact ASG|].
      apply (rw_cells_agree bsegs mq m13 _ _ EL); [| exact WM13]. eapply agree_sub; [exact AG13|]. intros x Hx. rewrite velts_size, atp_elsA_length in Hx. fold P in Hx.
      cbv beta. clear - Hx ASL AR1 LOW LOR SPR. split; ul. }
    pose proof (fobjV_of_shadow1 RT Σq m13 f t FPOS F64 FRSq' FS13) as FOBJV13.
    assert (CAP1 : 1 <= capv) by lia.
    pose proof RC13 as RC13'. change ([C8 (Z_to_bv 64 (f + 32)); CB 16 jr']) with ([C8 (Z_to_bv 64 (f + 32))] ++ [CB 16 jr']) in RC13'.
    apply Zvw.rw_cells_app in RC13'. destruct RC13' as [RCa13 _].

    apply (VDES Σq PMc (Z_to_bv 64 0x96eb8) (Z_to_bv 64 sp') gp (Z_to_bv 64 0x653c30) w0 w1 w2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') (Z_to_bv 64 (sp' + 136)) g1 g2 g3 g4 g5 g6 g7
             (Z_to_bv 64 (-8)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120)) s6x s7x s8x (Z_to_bv 64 S) (Z_to_bv 64 f) (Z_to_bv 64 2147450880)
             w3 w4 w5 w6 Fq fcq m13 (sp' + 136) (f + 32) A capv (Z.of_nat P) (atp_elsA d (chars bs)) (rt_live RT Σ) lo FDO MST eq_refl eq_refl);
      [.. | split; [subst S; exact Hc13'| apply (cfrm0_of_asta RT Σq PMc (eq _) c13 Hc13'); intros ms0 <-; exact FRMq] |].
    + rewrite EU1. lia.
    + ul.
    + clear - SPA'. Z.div_mod_to_equations. lia.
    + exact RCa13.
    + exact VR13.
    + unfold vliveA. rewrite LVq. subst L0 capv P. reflexivity.
    + exact LVPOS.
    + exact CAP1.
    + exact FOBJV13.
    + exact ART13.
    + exact MI13.
    + rewrite EU1. exact ST13.
    + rewrite SPq'. exact LOW.
    + rewrite EU1. ul.
    + rewrite EU1. ul.
    + rewrite EU1. clear - SPA'. Z.div_mod_to_equations. lia.
    + unfold unwind_ok. rewrite EU1, EUSP. right; right. lia.
    + exact FRMq.
    + intros c14 ((Σv & Hc14 & LVv & FRSv & SPv & CRv) & FC14).
      destruct (ASTA_unpack_f RT Σv _ _ c14 Hc14 FC14) as (ms14 & (vv & m14 & RS14 & (ART14 & MI14 & ST14) & PRES14) & FRM14 & Hc14'). clear Hc14.
      destruct RS14 as (y0 & y1 & y2 & k1' & k2' & k3 & k4' & k5 & k6 & k7 & y3 & y4 & y5 & y6 & F14 & fc14 & ->).
      cbn [ms_fcsr] in FRM14. rewrite EU1 in ST14, PRES14. rewrite (ret_pc_even 0x96eb8) in Hc14' by lia.
      assert (FRSv' : rt_frames RT Σv = [(f, 2%nat)]) by (rewrite FRSv; exact FRSq').
      assert (INFv : In (f, 2%nat) (rt_frames RT Σv)) by (rewrite FRSv'; left; reflexivity).

      assert (ACL : forall x, (sp' <= x < usp) \/ (f <= x < f + 32) \/ (S <= x < S + 32) \/ in_ranges LIB_FP x ->
                      aclient (rt_live RT Σ) (rt_frames RT Σq) sp' x /\ outside [(f + 32, f + 32 + 24)] x).
      { intros x Hx. split.
        - destruct Hx as [H|[H|[H|H]]].
          + left. ul.
          + right; right; right; left. exists f, 2%nat. change (fs_size 2) with 256. split; [exact INFq| lia].
          + right; right; right; right. exists f, 2%nat. change (fs_size 2) with 256. rewrite SHF, SHS. split; [exact INFq| lia].
          + right; left. exact (proj1 (lib_fp_static x H)).
        - cbn [outside]. split; [| exact I]. destruct Hx as [H|[H|[H|H]]]; [clear - H FR1' LOW LOR SPR; ul| lia| clear - H FSELF; lia|].
          pose proof (proj2 (lib_fp_static x H)). clear - H0 FSEG2. unfold SEGTOP_A in *. lia. }
      assert (AG14 : agree_on (fun x => (sp' <= x < usp) \/ (f <= x < f + 32) \/ (S <= x < S + 32) \/ in_ranges LIB_FP x) m13 m14).
      { intros a Ha. destruct (ACL _ Ha) as [H1 H2]. exact (PRES14 a H1 H2). }
      assert (FH14 : rw_cells bsegs m14 f (fz_hdr (C8 (Z_to_bv 64 0x41b58ab3)) (C8 (Z_to_bv 64 0x1e816)) (C8 (Z_to_bv 64 0x96ab0)) h3)).
      { apply (rw_cells_agree_nw bsegs m13 m14 _ _ FH13). eapply agree_sub; [exact AG14|]. intros x Hx. unfold fz_hdr in Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. lia. }
      assert (FS14 : rw_cells bsegs m14 S (fa_shadow1 t)).
      { apply (rw_cells_agree_nw bsegs m13 m14 _ _ FS13). eapply agree_sub; [exact AG14|]. intros x Hx. unfold fa_shadow1 in Hx. cbn [map app repeat cells_size csize Nat.add] in Hx.
        cbv beta. lia. }
      assert (X1_14 : rw_cells bsegs m14 sp' [CB 8 k0; CB 8 k1; CB 8 k2; C8 (Z_to_bv 64 f); CB 16 k4; C8 (Z_to_bv 64 f); CB 24 kq; CB 16 ke; CB 24 ko; CB 16 kn]).
      { apply (rw_cells_agree_nw bsegs m13 m14 _ _ X1_13). eapply agree_sub; [exact AG14|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. lia. }

      pose proof X1_14 as FL14.
      lazymatch type of FL14 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?rest) =>
        change (c0 :: c1 :: c2 :: c3 :: rest) with ([c0; c1; c2] ++ [c3] ++ rest) in FL14 end.
      apply Zvw.rw_cells_app in FL14. destruct FL14 as [_ FL14]. apply Zvw.rw_cells_app in FL14. destruct FL14 as [FL14 _].
      cbn [cells_size csize Nat.add] in FL14. replace (sp' + Z.of_nat 24) with (sp' + 24) in FL14 by lia.

      pose proof (fa_walk13a usp sp' f lo (Z_to_bv 64 0x96eb8) gp (Z_to_bv 64 0x653c30) y0 y1 y2 vv k1' k2' k3 k4' k5 k6 k7 s6x s7x s8x y3 y4 y5 y6 h3 t F14 fc14 m14
                    FPOS ltac:(clear - FR1' LOW; ul) ltac:(subst S; clear - SHT LOW; ul) ltac:(apply Z.div_pos; lia) ltac:(subst S; exact FSELF) ltac:(clear - LOR SPR; ul) ltac:(clear - LOR SPT SPR; ul)
                    FH14 ltac:(subst S; exact FS14) FL14 MI14) as W13.
      fold S in W13. unfold sx_regs in W13.
      lazymatch type of W13 with evt bsegs _ ?X =>
        assert (W13' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W13) end.
      clear W13.
      apply (cps_realizes bsegs _ _ _ c14 (asta_evt_c RT AF Σv PMc _ _ MST W13') ltac:(subst S; exact Hc14')). clear W13'. intros c15 Hc15.
      destruct (ASTA_unpack RT Σv _ _ c15 Hc15) as (ms15 & (m15 & a0' & -> & MU15 & WM15 & MI15) & Hc15'). clear Hc15.
      assert (ART15 : ART RT Σv m15).
      { apply (art_client_write RT AF Σv m14 m15 sp' ART14 ltac:(rewrite SPv, SPq'; ul)); [| exact WM15].
        intros a Ha. apply MU15. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Ha.
        - right; right; right; left. exists f, 2%nat. change (fs_size 2) with 256. split; [exact INFv| lia].
        - right; right; right; right. exists f, 2%nat. change (fs_size 2) with 256. rewrite SHF, SHS. split; [exact INFv| lia]. }
      assert (AG15 : agree_on (fun x => ~ (f <= x < f + 8) /\ ~ (S <= x < S + 32)) m14 m15).
      { apply (agree_of_munch _ _ _ _ MU15). intros x (H1 & H2). cbn [outside]. repeat split; assumption. }

      set (LCl := [CB 8 k0; CB 8 k1; CB 8 k2; C8 (Z_to_bv 64 f); CB 16 k4; C8 (Z_to_bv 64 f); CB 24 kq; CB 16 ke; CB 24 ko; CB 16 kn] ++ [C8 (Z_to_bv 64 (f + 32)); CB 16 jr']
                  ++ [C8 (Z_to_bv 64 (d + Z.of_nat (length bs))); C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 7 k13]).
      assert (LC15 : rw_cells bsegs m15 sp' LCl).
      { subst LCl. apply Zvw.rw_cells_app. split.
        { apply (rw_cells_agree bsegs m14 m15 _ _); [exact X1_14| | exact WM15].
          eapply agree_sub; [exact AG15|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. clear - Hx FR1' SHT LOW LOR SPR. subst S. split; ul. }
        apply Zvw.rw_cells_app. cbn [cells_size csize Nat.add]. replace (sp' + Z.of_nat 136) with (sp' + 136) by lia. replace (sp' + 136 + Z.of_nat 24) with (sp' + 160) by lia. split.
        { apply (rw_cells_agree bsegs m14 m15 _ _); [| | exact WM15].
          - apply (rw_cells_agree_nw bsegs m13 m14 _ _ RC13). eapply agree_sub; [exact AG14|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. lia.
          - eapply agree_sub; [exact AG15|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. clear - Hx FR1' SHT LOW LOR SPR. subst S. split; ul. }
        apply (rw_cells_agree bsegs m14 m15 _ _); [| | exact WM15].
        - apply (rw_cells_agree_nw bsegs m13 m14 _ _ X3_13). eapply agree_sub; [exact AG14|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. lia.
        - eapply agree_sub; [exact AG15|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. clear - Hx FR1' SHT LOW LOR SPR. subst S. split; ul. }
      assert (ST15 : stk bsegs m15 lo sp').
      { apply (stk_agree bsegs m14 m15 _ _ ST14); [| exact WM15]. eapply agree_sub; [exact AG15|]. intros x Hx. cbv beta in *. clear - Hx FR1' SHT LOW LOR SPR. subst S. split; ul. }
      assert (STp15 : stk bsegs m15 (sp' + 184) (usp - 104)).
      { apply (stk_agree bsegs m14 m15 _ _); [| | exact WM15].
        - apply (stk_agree_nw bsegs m13 m14 _ _ STp13). eapply agree_sub; [exact AG14|]. intros x Hx. cbv beta in *. lia.
        - eapply agree_sub; [exact AG15|]. intros x Hx. cbv beta in *. clear - Hx FR1' SHT LOW LOR SPR. subst S. split; ul. }
      assert (FRs15 : rw_cells bsegs m15 (usp - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
      { apply (rw_cells_agree bsegs m14 m15 _ _); [| | exact WM15].
        - apply (rw_cells_agree_nw bsegs m13 m14 _ _ FRs13). eapply agree_sub; [exact AG14|]. intros x Hx. unfold fa_saved in Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. lia.
        - eapply agree_sub; [exact AG15|]. intros x Hx. unfold fa_saved in Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. clear - Hx FR1' SHT LOW LOR SPR. subst S. split; ul. }
      assert (LIB15 : LIB m15).
      { apply (LIB_agree2 LIB LIB_loc m14 m15).
        - apply (LIB_agree2 LIB LIB_loc m13 m14 LIB13). eapply agree_sub; [exact AG14|]. intros x Hx. cbv beta. do 3 right. exact Hx.
        - eapply agree_sub; [exact AG15|]. intros x Hx. pose proof (proj2 (lib_fp_static x Hx)) as R. cbv beta. clear - R FSEG2 SHB0. subst S. unfold SEGTOP_A, SHB in *. split; lia. }

      destruct (af_frame_release RT AF Σv m15 f 2 [] ART15 FRSv') as (Σ4 & fl & FLC & NAC & FL0 & FLW & FW & REL).
      change (fs_size 2) with 256 in FW. replace (f + 256 - 8) with (f + 248) in FW by lia. rewrite SPv, SPq' in FLW.
      pose proof (fa_walk13b usp sp' f fl lo (Z_to_bv 64 0x96eb8) gp (Z_to_bv 64 0x653c30) y0 y1 y2 a0' k2' k3 k4' k5 k6 k7 s6x s7x s8x y3 y4 y5 y6
                    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 LCl F14 fc14 m15 FPOS ltac:(clear - FR1' LOW; ul) FL0 ltac:(clear - FLW LOW; lia) ltac:(clear - SP0R LOW; ul) ltac:(clear - LOR SPR; ul)
                    ltac:(subst LCl; reflexivity) ltac:(lia) ltac:(clear - SPT; ul) ST15 LC15 STp15 FRs15 FW FLC MI15) as W14.
      unfold sx_regs in W14. fold S in W14.
      lazymatch type of W14 with evt bsegs _ ?X =>
        assert (W14' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W14) end.
      clear W14.
      apply (cps_realizes bsegs _ _ _ c15 (asta_evt_c RT AF Σv PMc _ _ MST W14') ltac:(subst S; exact Hc15')). clear W14'. intros c16 Hc16.
      destruct (ASTA_unpack RT Σv _ _ c16 Hc16) as (ms16 & (m16 & RS16 & E16 & MU16 & WM16 & MI16 & ST16 & FL16) & Hc16'). clear Hc16.
      destruct (REL m16 MU16 WM16 FL16) as (ART16 & FRS4 & LV4 & SP4 & CR4 & AL4 & AM4).

      assert (NFL : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> x <> fl).
      { intros x Hx E. subst x. destruct Hx as [H|[H|[H|[H|H]]]].
        - clear - H FLW LOW LOR. ul.
        - apply NAC. right; left. exact H.
        - apply NAC. right; right; left. rewrite LVv. exact H.
        - destruct H as (f9 & k9 & Hin & _). rewrite FRS0 in Hin. destruct Hin.
        - destruct H as (f9 & k9 & Hin & _). rewrite FRS0 in Hin. destruct Hin. }
      assert (CALLER : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> outside LIB_FP (bv_unsigned a) -> m16 a = m a).
      { intros a Ha Hout. rewrite <- (PRESq a Ha Hout).
        assert (NF : ~ (f <= bv_unsigned a < f + 256) /\ ~ (S <= bv_unsigned a < S + 32) /\ (usp <= bv_unsigned a \/ bv_unsigned a < lo)).
        { destruct Ha as [H|[H|[H|[H|H]]]].
          - clear - H FR1' SHT LOW LOR SPR. split; [ul|]. split; [ul| left; lia].
          - pose proof (client_static_range _ H) as R. clear - R FSEG2 SHB0 SP0R LOW. subst S. unfold SEGTOP_A, SHB in *. split; [lia|]. split; [lia| right; ul].
          - destruct H as (p & k & Hin & Hr). pose proof (FLVq p k (INCLq _ Hin)) as Y1. pose proof (FSLq p k (INCLq _ Hin)) as Y2.
            pose proof (af_live_range RT AF Σq mq p k ARTq (INCLq _ Hin)) as (_ & Y3 & _). rewrite SPq' in Y3. clear - Hr Y1 Y2 Y3 LOW. split; [lia|]. split; [lia| right; lia].
          - destruct H as (f9 & k9 & Hin & _). rewrite FRS0 in Hin. destruct Hin.
          - destruct H as (f9 & k9 & Hin & _). rewrite FRS0 in Hin. destruct Hin. }
        destruct NF as (NF1 & NF2 & NF3).
        rewrite (MU16 a), (MU15 a), (PRES14 a), (MU13 a); [reflexivity| | | | |].
        - cbn [outside]. clear - NF2 NF3 LOR SPR. subst S. split; [lia|]. split; [ul| exact I].
        - apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| rewrite FRS0; intros e []| lia].
        - cbn [outside]. split; [clear - NF1; lia| exact I].
        - cbn [outside]. split; [clear - NF1; lia|]. split; [clear - NF2; lia| exact I].
        - cbn [outside]. split; [| exact I]. intros E. exact (NFL _ Ha ltac:(clear - E; lia)). }
      apply Hk. split; [| apply (cfrm0_of_asta RT Σv PMc (eq _) c16 Hc16'); intros ms0 <-; rewrite E16; exact FRM14].
      exists Σ4. split; [| split; [rewrite LV4; exact LVv| split; [exact FRS4| split; [rewrite SP4, SPv; exact SPq'| rewrite CR4, CRv, CRq; exact CRx]]]].
      eapply ASTA_conseq; [exact (ASTA_switch RT Σv Σ4 PMc _ c16 Hc16' AL4 AM4)|]. intros ms <-. exists m16.
      split; [exact RS16|]. split; [split; [exact ART16| split; [exact MI16| exact ST16]]|].
      split; [exact CALLER|].
      apply (LIB_agree2 LIB LIB_loc m15 m16 LIB15). apply (agree_of_munch _ _ _ _ MU16). intros x Hx. cbn [outside]. split; [| exact I].
      intros E. exact (NFL x (or_intror (or_introl (proj1 (lib_fp_static x Hx)))) ltac:(clear - E; lia)).
Qed.
End Top3.

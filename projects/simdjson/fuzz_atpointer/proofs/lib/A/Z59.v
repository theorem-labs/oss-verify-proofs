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
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Layout Shadow Zks Zkt Zi4 D_defs D_kit D_clx Z87 Z82 I_lkit Sj_rtf Zpm Zpl Zq2 Zq3
  Sj_new Zpt Zps Zpo Zwn Zsl Z4a Z73 Z5g Z6m Z71 Z5h Z5i Z5j
  Z6q Z6y Z6p Z45 Z4e Z4l Z4m Z4n Z4o Z52 Z57 Z5b.
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
Hypothesis HOBJ : forall E, aenvA_ok E -> atp_obj_cpsA RT E (Nat.pred TAPE_MAX_DEPTH).
Hypothesis HARR : forall E, aenvA_ok E -> atp_arr_cpsA RT E (Nat.pred TAPE_MAX_DEPTH).

Local Ltac nomod := repeat match goal with H : _ mod _ = _ |- _ => clear H end.
Local Ltac ul := unfold FUZZ_STACK, ATPA_SPLITINTO_STACK, ATPA_SPLIT_STACK, ATPA_PUSH_STACK, ATPA_DESTROY_STACK, PID_STACK in *;
                 unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma lftoi_tail : forall (Σ Σx : rts RT) PMc (m mx : mem) (usp sp' f A lo d : Z) (bs : list byte)
    (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 s6x s7x s8x u3 u4 u5 u6 : word) (Fx : bvmap 5 word) (fcx : bv 32) (h3 t : list byte),
  fdfs_only PMc -> mat_stable PMc ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d < SEGTOP_A)) ->
  rt_frames RT Σ = [] -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= usp -> usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
  lp_inv RT LIB Σ Σx m mx usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A ->
  pdone RT Σx mx (f + 96) (vblockA A (vcap_iter (atp_P (chars bs)) 0 0) (Z.of_nat (atp_P (chars bs))) ++ rt_live RT Σ) ->
  rt_credit RT Σ - FUZZ_COST <= rt_credit RT Σx ->
  usp - 240 <= sp' <= usp - 224 -> sp' mod 32 = 0 -> 0 < f -> f mod 64 = 0 -> f + 256 <= rt_sp0 RT Σ - STACK_WIN ->
  (f + 256 <= 0x10000 \/ SEGTOP_A <= f) -> (f + 256 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 32 <= f) ->
  SHB <= f / 8 + 2147450880 -> f / 8 + 2147450880 + 32 + 1 <= rt_sp0 RT Σ - STACK_WIN -> frm0 fcx ->
  cps_f (ASTA RT Σx PMc (eq (sa_regs e_pdtor (Z_to_bv 64 0x96c88) sp' gp (Z_to_bv 64 0x646eb0) u0 u1 u2 usp (Z_to_bv 64 (f + 96)) v1 v2 v3 v4 v5 v6 v7 f s6x s7x s8x
                                       u3 u4 u5 u6 Fx fcx mx)))
    (fin_postA RT LIB Σ PMc usp lo ra gp (Z_to_bv 64 0x646eb0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m).
Proof using LIB_loc AF PDT VDES.
  intros Σ Σx PMc m mx usp sp' f A lo d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 s6x s7x s8x u3 u4 u5 u6 Fx fcx h3 t
    FDO MST INLV FRS0 LVPOS LOW LOR SPT SPA INVx PD CRx SPR SPA' FPOS F64 FR1' FSEG2 FSELF SHB0 SHT FRM.
  intros T c (Hc & FC0) Hk. unfold sa_regs in Hc.
  pose proof INVx as (ARTx & MIx & STx & (j0 & j1 & j2 & jo & jr & j13 & jn & FRlx) & STpx & FRsx & FHx & FSx & VRx & BSx & LIBx & PRESx & FRSx & SPx).
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

  apply (PDT Σx PMc (Z_to_bv 64 0x96c88) (Z_to_bv 64 sp') gp (Z_to_bv 64 0x646eb0) u0 u1 u2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') (Z_to_bv 64 (f + 96)) v1 v2 v3 v4 v5 v6 v7
           (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120)) s6x s7x s8x (Z_to_bv 64 S) (Z_to_bv 64 f) (Z_to_bv 64 2147450880)
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
    cbn [ms_fcsr] in FRMq. rewrite EU1 in STq, PRESq. rewrite (ret_pc_even 0x96c88) in Hcq' by lia.
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
    pose proof INVq as (_ & _ & _ & (k0 & k1 & k2 & ko & kr & k13 & kn & FRlq) & STpq & FRsq & FHq & FSq & VRq & BSq & LIBq & PRESq & _ & SPq').
    pose proof (fframe_ranges RT AF Σq mq f 2 ARTq INFq) as (_ & _ & _ & _ & SHTq). change (fs_size 2) with 256 in SHTq. rewrite SHF, SPq' in SHTq.
    pose proof (af_frames_range RT AF Σq mq f 2%nat ARTq INFq) as (_ & _ & _ & FLVq). change (fs_size 2) with 256 in FLVq.
    pose proof (af_fshadow_apart RT AF Σq mq f 2 ARTq INFq) as (FSLq & _). change (fs_size 2) with 256 in FSLq. rewrite SHF, SHS in FSLq.
    pose proof (af_live_range RT AF Σq mq A _ ARTq INAq) as (AR0 & AR1 & AR2). rewrite SPq' in AR1.
    pose proof (FLVq A _ INAq) as AFL. pose proof (FSLq A _ INAq) as ASL.

    unfold fa_locals2 in FRlq.
    lazymatch type of FRlq with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?rest) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: rest) with ([c0; c1; c2; c3; c4] ++ [c5] ++ rest) in FRlq end.
    apply Zvw.rw_cells_app in FRlq. destruct FRlq as [X1q FRlq]. apply Zvw.rw_cells_app in FRlq. destruct FRlq as [RESq X3q].
    cbn [cells_size csize Nat.add] in X1q, RESq, X3q. replace (sp' + Z.of_nat 56) with (sp' + 56) in RESq, X3q by lia. replace (sp' + 56 + Z.of_nat 24) with (sp' + 80) in X3q by lia.

    pose proof (fa_walk12 usp sp' f (Z_to_bv 64 0x96c88) gp (Z_to_bv 64 0x646eb0) w0 w1 w2 vq g1 g2 g3 g4 g5 g6 g7 s6x s7x s8x w3 w4 w5 w6 t kr Fq fcq mq
                  FPOS ltac:(ul) ltac:(apply Z.div_pos; lia) ltac:(subst S; ul) ltac:(ul) ltac:(ul) ltac:(subst S; exact FSELF) ltac:(subst S; clear - SHTq LOW LOR SPR; ul) FSq RESq MIq) as W12.
    fold S in W12. unfold sa_regs in W12.
    lazymatch type of W12 with evt asegs _ ?X =>
      assert (W12' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W12) end.
    clear W12.
    apply (cps_realizes asegs _ _ _ cq (asta_evt_c RT AF Σq PMc _ _ MST W12') ltac:(subst S; exact Hcq')). clear W12'. intros c13 Hc13.
    destruct (ASTA_unpack RT Σq _ _ c13 Hc13) as (ms13 & (m13 & jr' & -> & MU13 & WM13 & MI13 & FS13 & RC13) & Hc13'). clear Hc13.
    assert (ART13 : ART RT Σq m13).
    { apply (art_client_write RT AF Σq mq m13 sp' ARTq ltac:(rewrite SPq'; ul)); [| exact WM13].
      intros a Ha. apply MU13. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Ha.
      - right; right; right; right. exists f, 2%nat. change (fs_size 2) with 256. rewrite SHF, SHS. split; [exact INFq| lia].
      - left. ul. }
    assert (AG13 : agree_on (fun x => ~ (S + 12 <= x < S + 22) /\ ~ (sp' + 56 <= x < sp' + 64)) mq m13).
    { apply (agree_of_munch _ _ _ _ MU13). intros x (H1 & H2). cbn [outside]. repeat split; assumption. }
    assert (X1_13 : rw_cells asegs m13 sp' [CB 8 k0; CB 8 k1; CB 8 k2; C8 (Z_to_bv 64 f); CB 24 ko]).
    { apply (rw_cells_agree asegs mq m13 _ _ X1q); [| exact WM13]. eapply agree_sub; [exact AG13|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta.
      clear - Hx SHTq LOW LOR SPR. subst S. split; ul. }
    assert (X3_13 : rw_cells asegs m13 (sp' + 80) [C8 (Z_to_bv 64 (d + Z.of_nat (length bs))); C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 7 k13; CB 16 kn]).
    { apply (rw_cells_agree asegs mq m13 _ _ X3q); [| exact WM13]. eapply agree_sub; [exact AG13|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta.
      clear - Hx SHTq LOW LOR SPR. subst S. split; ul. }
    assert (STp13 : stk asegs m13 (sp' + 120) (usp - 104)).
    { apply (stk_agree asegs mq m13 _ _ STpq); [| exact WM13]. eapply agree_sub; [exact AG13|]. intros x Hx. cbv beta in *. clear - Hx SHTq LOW LOR SPR. subst S. split; ul. }
    assert (ST13 : stk asegs m13 lo sp').
    { apply (stk_agree asegs mq m13 _ _ STq); [| exact WM13]. eapply agree_sub; [exact AG13|]. intros x Hx. cbv beta in *. clear - Hx SHTq LOW LOR SPR. subst S. split; ul. }
    assert (FRs13 : rw_cells asegs m13 (usp - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
    { apply (rw_cells_agree asegs mq m13 _ _ FRsq); [| exact WM13]. eapply agree_sub; [exact AG13|]. intros x Hx. unfold fa_saved in Hx. cbn [cells_size csize Nat.add] in Hx.
      cbv beta. clear - Hx SHTq LOW LOR SPR. subst S. split; ul. }
    assert (FH13 : rw_cells asegs m13 f (fz_hdr (C8 (Z_to_bv 64 0x41b58ab3)) (C8 (Z_to_bv 64 0x1e899)) (C8 (Z_to_bv 64 0x969b0)) h3)).
    { apply (rw_cells_agree asegs mq m13 _ _ FHq); [| exact WM13]. eapply agree_sub; [exact AG13|]. intros x Hx. unfold fz_hdr in Hx. cbn [cells_size csize Nat.add] in Hx.
      cbv beta. clear - Hx FSELF FR1' LOW LOR SPR. subst S. split; ul. }
    assert (LIB13 : LIB m13).
    { apply (LIB_agree2 LIB LIB_loc mq m13 LIBq). eapply agree_sub; [exact AG13|]. intros x Hx. pose proof (proj2 (lib_fp_static x Hx)) as R. cbv beta.
      clear - R SHB0 SP0R LOW LOR SPR. subst S. unfold SHB in *. split; ul. }
    assert (VR13 : vrepA m13 (f + 32) A capv (Z.of_nat P) (atp_elsA d (chars bs))).
    { destruct VRq as (E & R & C & A0 & AH & SV & BLK). unfold vrepA. split; [exact E|]. split; [exact R|]. split; [exact C|]. split; [exact A0|]. split; [exact AH|].
      split. { apply (rw_cells_agree asegs mq m13 _ _ SV); [| exact WM13]. eapply agree_sub; [exact AG13|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta.
               clear - Hx FSELF FR1' LOW LOR SPR. subst S. split; ul. }
      destruct BLK as [B|(CQ1 & A16 & ASG & EL)]; [left; exact B| right]. split; [exact CQ1|]. split; [exact A16|]. split; [exact ASG|].
      apply (rw_cells_agree asegs mq m13 _ _ EL); [| exact WM13]. eapply agree_sub; [exact AG13|]. intros x Hx. rewrite velts_size, atp_elsA_length in Hx. fold P in Hx.
      cbv beta. clear - Hx ASL AR1 LOW LOR SPR. split; ul. }
    pose proof (fobjV_of_shadow1 RT Σq m13 f t FPOS F64 FRSq' FS13) as FOBJV13.
    assert (CAP1 : 1 <= capv) by lia.
    pose proof RC13 as RC13'. change ([C8 (Z_to_bv 64 (f + 32)); CB 16 jr']) with ([C8 (Z_to_bv 64 (f + 32))] ++ [CB 16 jr']) in RC13'.
    apply Zvw.rw_cells_app in RC13'. destruct RC13' as [RCa13 _].

    apply (VDES Σq PMc (Z_to_bv 64 0x96cc0) (Z_to_bv 64 sp') gp (Z_to_bv 64 0x646eb0) w0 w1 w2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') (Z_to_bv 64 (sp' + 56)) g1 g2 g3 g4 g5 g6 g7
             (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (-8)) (Z_to_bv 64 (f + 120)) s6x s7x s8x (Z_to_bv 64 S) (Z_to_bv 64 f) (Z_to_bv 64 2147450880)
             w3 w4 w5 w6 Fq fcq m13 (sp' + 56) (f + 32) A capv (Z.of_nat P) (atp_elsA d (chars bs)) (rt_live RT Σ) lo FDO MST eq_refl eq_refl);
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
      destruct RS14 as (y0 & y1 & y2 & k1' & k2' & k3 & k4 & k5 & k6 & k7 & y3 & y4 & y5 & y6 & F14 & fc14 & ->).
      cbn [ms_fcsr] in FRM14. rewrite EU1 in ST14, PRES14. rewrite (ret_pc_even 0x96cc0) in Hc14' by lia.
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
      assert (FH14 : rw_cells asegs m14 f (fz_hdr (C8 (Z_to_bv 64 0x41b58ab3)) (C8 (Z_to_bv 64 0x1e899)) (C8 (Z_to_bv 64 0x969b0)) h3)).
      { apply (rw_cells_agree_nw asegs m13 m14 _ _ FH13). eapply agree_sub; [exact AG14|]. intros x Hx. unfold fz_hdr in Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. lia. }
      assert (FS14 : rw_cells asegs m14 S (fa_shadow1 t)).
      { apply (rw_cells_agree_nw asegs m13 m14 _ _ FS13). eapply agree_sub; [exact AG14|]. intros x Hx. unfold fa_shadow1 in Hx. cbn [map app repeat cells_size csize Nat.add] in Hx.
        cbv beta. lia. }

      pose proof (fa_walk13a usp sp' f lo (Z_to_bv 64 0x96cc0) gp (Z_to_bv 64 0x646eb0) y0 y1 y2 vv k1' k2' k3 k4 k5 k6 k7 s6x s7x s8x y3 y4 y5 y6 h3 t F14 fc14 m14
                    FPOS ltac:(clear - FR1' LOW; ul) ltac:(subst S; clear - SHT LOW; ul) ltac:(apply Z.div_pos; lia) ltac:(subst S; exact FSELF) ltac:(clear - LOR SPT; ul) FH14 ltac:(subst S; exact FS14) MI14) as W13.
      fold S in W13. unfold sx_regs in W13.
      lazymatch type of W13 with evt asegs _ ?X =>
        assert (W13' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W13) end.
      clear W13.
      apply (cps_realizes asegs _ _ _ c14 (asta_evt_c RT AF Σv PMc _ _ MST W13') ltac:(subst S; exact Hc14')). clear W13'. intros c15 Hc15.
      destruct (ASTA_unpack RT Σv _ _ c15 Hc15) as (ms15 & (m15 & a0' & -> & MU15 & WM15 & MI15) & Hc15'). clear Hc15.
      assert (ART15 : ART RT Σv m15).
      { apply (art_client_write RT AF Σv m14 m15 sp' ART14 ltac:(rewrite SPv, SPq'; ul)); [| exact WM15].
        intros a Ha. apply MU15. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Ha.
        - right; right; right; left. exists f, 2%nat. change (fs_size 2) with 256. split; [exact INFv| lia].
        - right; right; right; right. exists f, 2%nat. change (fs_size 2) with 256. rewrite SHF, SHS. split; [exact INFv| lia]. }
      assert (AG15 : agree_on (fun x => ~ (f <= x < f + 8) /\ ~ (S <= x < S + 32)) m14 m15).
      { apply (agree_of_munch _ _ _ _ MU15). intros x (H1 & H2). cbn [outside]. repeat split; assumption. }

      set (LCl := [CB 8 k0; CB 8 k1; CB 8 k2; C8 (Z_to_bv 64 f); CB 24 ko] ++ [C8 (Z_to_bv 64 (f + 32)); CB 16 jr']
                  ++ [C8 (Z_to_bv 64 (d + Z.of_nat (length bs))); C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 7 k13; CB 16 kn]).
      assert (LC15 : rw_cells asegs m15 sp' LCl).
      { subst LCl. apply Zvw.rw_cells_app. split.
        { apply (rw_cells_agree asegs m14 m15 _ _); [| | exact WM15].
          - apply (rw_cells_agree_nw asegs m13 m14 _ _ X1_13). eapply agree_sub; [exact AG14|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. lia.
          - eapply agree_sub; [exact AG15|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. clear - Hx FR1' SHT LOW LOR SPR. subst S. split; ul. }
        apply Zvw.rw_cells_app. cbn [cells_size csize Nat.add]. replace (sp' + Z.of_nat 56) with (sp' + 56) by lia. replace (sp' + 56 + Z.of_nat 24) with (sp' + 80) by lia. split.
        { apply (rw_cells_agree asegs m14 m15 _ _); [| | exact WM15].
          - apply (rw_cells_agree_nw asegs m13 m14 _ _ RC13). eapply agree_sub; [exact AG14|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. lia.
          - eapply agree_sub; [exact AG15|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. clear - Hx FR1' SHT LOW LOR SPR. subst S. split; ul. }
        apply (rw_cells_agree asegs m14 m15 _ _); [| | exact WM15].
        - apply (rw_cells_agree_nw asegs m13 m14 _ _ X3_13). eapply agree_sub; [exact AG14|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. lia.
        - eapply agree_sub; [exact AG15|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. clear - Hx FR1' SHT LOW LOR SPR. subst S. split; ul. }
      assert (ST15 : stk asegs m15 lo sp').
      { apply (stk_agree asegs m14 m15 _ _ ST14); [| exact WM15]. eapply agree_sub; [exact AG15|]. intros x Hx. cbv beta in *. clear - Hx FR1' SHT LOW LOR SPR. subst S. split; ul. }
      assert (STp15 : stk asegs m15 (sp' + 120) (usp - 104)).
      { apply (stk_agree asegs m14 m15 _ _); [| | exact WM15].
        - apply (stk_agree_nw asegs m13 m14 _ _ STp13). eapply agree_sub; [exact AG14|]. intros x Hx. cbv beta in *. lia.
        - eapply agree_sub; [exact AG15|]. intros x Hx. cbv beta in *. clear - Hx FR1' SHT LOW LOR SPR. subst S. split; ul. }
      assert (FRs15 : rw_cells asegs m15 (usp - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
      { apply (rw_cells_agree asegs m14 m15 _ _); [| | exact WM15].
        - apply (rw_cells_agree_nw asegs m13 m14 _ _ FRs13). eapply agree_sub; [exact AG14|]. intros x Hx. unfold fa_saved in Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. lia.
        - eapply agree_sub; [exact AG15|]. intros x Hx. unfold fa_saved in Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. clear - Hx FR1' SHT LOW LOR SPR. subst S. split; ul. }
      assert (LIB15 : LIB m15).
      { apply (LIB_agree2 LIB LIB_loc m14 m15).
        - apply (LIB_agree2 LIB LIB_loc m13 m14 LIB13). eapply agree_sub; [exact AG14|]. intros x Hx. cbv beta. do 3 right. exact Hx.
        - eapply agree_sub; [exact AG15|]. intros x Hx. pose proof (proj2 (lib_fp_static x Hx)) as R. cbv beta. clear - R FSEG2 SHB0. subst S. unfold SEGTOP_A, SHB in *. split; lia. }

      destruct (af_frame_release RT AF Σv m15 f 2 [] ART15 FRSv') as (Σ4 & fl & FLC & NAC & FL0 & FLW & FW & REL).
      change (fs_size 2) with 256 in FW. replace (f + 256 - 8) with (f + 248) in FW by lia. rewrite SPv, SPq' in FLW.
      pose proof (fa_walk13b usp sp' f fl lo (Z_to_bv 64 0x96cc0) gp (Z_to_bv 64 0x646eb0) y0 y1 y2 a0' k1' k2' k3 k4 k5 k6 k7 s6x s7x s8x y3 y4 y5 y6
                    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 LCl F14 fc14 m15 FPOS ltac:(clear - FR1' LOW; ul) FL0 ltac:(clear - FLW LOW; lia) ltac:(clear - SP0R LOW; ul) ltac:(clear - LOR SPR; ul)
                    ltac:(subst LCl; reflexivity) ltac:(lia) ltac:(clear - SPT; ul) ST15 LC15 STp15 FRs15 FW FLC MI15) as W14.
      unfold sx_regs in W14. fold S in W14.
      lazymatch type of W14 with evt asegs _ ?X =>
        assert (W14' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W14) end.
      clear W14.
      apply (cps_realizes asegs _ _ _ c15 (asta_evt_c RT AF Σv PMc _ _ MST W14') ltac:(subst S; exact Hc15')). clear W14'. intros c16 Hc16.
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

Theorem lftoi_par3 : forall (Σ Σg : rts RT) PMc (m mg : mem) (usp sp' f A lo d : Z) (bs : list byte)
    (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6x s7x s8x t3 t4 t5 t6 : word) F fc (h3 t j20 : list byte)
    (impl idx oc ia tape sbuf : Z) (r : word),
  fdfs_only PMc -> mat_stable PMc ->
  0 < d -> Z.of_nat (length bs) < 2^26 ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d < SEGTOP_A)) ->
  rt_frames RT Σ = [] -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  Z.of_nat (length (rt_live RT Σ)) + FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ -> 8 + vcost_pushes (atp_P (chars bs)) 0 0 <= 2^31 + 2^26 ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= usp -> usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
  lp_inv RT LIB Σ Σg m mg usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A ->
  rw_cells asegs mg (sp' + 56) (res_cellsA (f + 120) r j20) -> bv_unsigned r < 64 ->
  s2a_okres tape sbuf (roundup64 (doc_cap bs + 3)) (al_sbuf (doc_cap bs)) r mg ->
  pdone RT Σg mg (f + 96) (vblockA A (vcap_iter (atp_P (chars bs)) 0 0) (Z.of_nat (atp_P (chars bs))) ++ rt_live RT Σ) ->
  pidA_st RT Σg mg (f + 96) impl idx oc ia tape sbuf (doc_cap bs) ->
  usp - 240 <= sp' <= usp - 224 -> sp' mod 32 = 0 -> 0 < f -> f mod 64 = 0 -> f + 256 <= rt_sp0 RT Σ - STACK_WIN ->
  (f + 256 <= 0x10000 \/ SEGTOP_A <= f) -> (f + 256 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 32 <= f) ->
  SHB <= f / 8 + 2147450880 -> f / 8 + 2147450880 + 32 + 1 <= rt_sp0 RT Σ - STACK_WIN ->
  rt_live RT Σg = (ia, 1024) :: (oc, 8192) :: (idx, sc_idx (doc_cap bs)) :: (impl, 96) :: (tape, al_tape (doc_cap bs)) :: (sbuf, al_sbuf (doc_cap bs))
                    :: vblockA A (vcap_iter (atp_P (chars bs)) 0 0) (Z.of_nat (atp_P (chars bs))) ++ rt_live RT Σ ->
  (impl mod 16 = 0 /\ idx mod 16 = 0 /\ oc mod 16 = 0 /\ ia mod 16 = 0 /\ tape mod 16 = 0 /\ sbuf mod 16 = 0) ->
  rt_credit RT Σ - 2 - vcost_pushes (atp_P (chars bs)) 0 0 - mcost (doc_len bs + 64) - pid_costA (doc_len bs) <= rt_credit RT Σg ->
  frm0 fc ->
  cps_f (ASTA RT Σg PMc (eq (sa_regs 0x96c78 x1 sp' gp (Z_to_bv 64 0x646eb0) t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s6x s7x s8x t3 t4 t5 t6 F fc mg)))
    (fin_postA RT LIB Σ PMc usp lo ra gp (Z_to_bv 64 0x646eb0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m).
Proof using LIB_loc AF PDT VDES HOBJ HARR.
  intros Σ Σg PMc m mg usp sp' f A lo d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6x s7x s8x t3 t4 t5 t6 F fc h3 t j20
    impl idx oc ia tape sbuf r FDO MST D0 BSL INLV FRS0 LVPOS LVB CR0 VCB LOW LOR SPT SPA INV RC R64 OKR PD PST SPR SPA' FPOS F64 FR1' FSEG2 FSELF SHB0 SHT LVg MODS CRg FRM.
  intros T c (Hc & FC0) Hk.
  pose proof INV as (ARTg & MIg & STg & (j0 & j1 & j2 & jo & jr & j13 & jn & FRlg) & STpg & FRsg & FHg & FSg & VRg & BSg & LIBg & PRESg & FRSg & SPg).
  pose proof (af_sp0_range RT AF Σg mg ARTg) as SP0R. rewrite SPg in SP0R. pose proof (af_sp0_win RT AF Σg mg ARTg) as SP0W. rewrite SPg in SP0W.
  set (n := Z.of_nat (length bs)) in *. set (P := atp_P (chars bs)) in *. set (S := f / 8 + 2147450880) in *. set (capv := vcap_iter P 0 0) in *.
  set (cap := doc_cap bs) in *.
  assert (CAPR : 32 <= cap <= 1048512) by (subst cap; unfold doc_cap, doc_len; pose proof (atp_doc_len (chars bs)) as [_ DL]; unfold SJ_PADMAX in DL; pose proof (zlength_nonneg (atp_doc (chars bs))); lia).
  assert (EU1 : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; ul).
  assert (P2 : (2 <= P)%nat) by (subst P; unfold atp_P; lia).
  pose proof (vcap_iter_inv P 0 0 ltac:(lia) ltac:(lia)) as CAPI. rewrite Z.add_0_l in CAPI. fold capv in CAPI.
  assert (DLR : 0 <= doc_len bs <= 1048512) by (unfold doc_len; pose proof (atp_doc_len (chars bs)) as [_ DL]; unfold SJ_PADMAX in DL; pose proof (zlength_nonneg (atp_doc (chars bs))); lia).
  pose proof (pid_costA_nonneg (doc_len bs) ltac:(lia)) as PC0. pose proof (pid_costA_bound (doc_len bs) DLR) as PCB.
  pose proof (mcost_nonneg (doc_len bs + 64) ltac:(lia)) as MC0. pose proof (mcost_le (doc_len bs + 64) ltac:(lia)) as MCB.
  assert (VC0 : 0 <= vcost_pushes P 0 0) by (apply vcost_pushes_nonneg; lia).
  assert (CRT : rt_credit RT Σ - FUZZ_COST <= rt_credit RT Σg) by (clear - CRg CR0 VCB PC0 MC0 VC0 PCB MCB DLR; subst P; unfold FUZZ_COST, DCOST in *; lia).
  destruct (Z.eq_dec (bv_unsigned r) 0) as [R0|RNZ].
  2: {
    pose proof (fa_walk11 usp sp' f x1 gp (Z_to_bv 64 0x646eb0) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6x s7x s8x t3 t4 t5 t6 r j20 F fc mg
                  FPOS ltac:(ul) ltac:(ul) ltac:(ul) ltac:(pose proof (bv_unsigned_in_range 64 r) as XR; clear - XR RNZ R64; lia) RC MIg) as W11.
    unfold sa_regs in W11. fold S in W11.
    lazymatch type of W11 with evt asegs _ ?X =>
      assert (W11' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W11) end.
    clear W11.
    apply (cps_realizes asegs _ _ _ c (asta_evt_c RT AF Σg PMc _ _ MST W11') ltac:(unfold sa_regs in Hc; subst S; exact Hc)). clear W11'. intros c6 Hc6.
    destruct (ASTA_unpack RT Σg _ _ c6 Hc6) as (ms6 & <- & Hc6'). clear Hc6.
    exact (lftoi_tail Σ Σg PMc m mg usp sp' f A lo d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6x s7x s8x t3 t4 t5 t6 F fc h3 t
             FDO MST INLV FRS0 LVPOS LOW LOR SPT SPA INV PD CRT SPR SPA' FPOS F64 FR1' FSEG2 FSELF SHB0 SHT FRM T c6
             (conj ltac:(unfold sa_regs; subst S; exact Hc6') (cfrm0_of_asta RT Σg PMc (eq _) c6 Hc6' ltac:(intros ms0 <-; exact FRM))) Hk). }

  assert (ER : r = Z_to_bv 64 0) by (apply bv_eq; rewrite R0; reflexivity). subst r.
  unfold res_cellsA in RC. rewrite bv_eqb_refl in RC.
  destruct OKR as [K|(_ & tws & sbs & TAPEB & SBUFB & WF & SBSR & LT & LS)]; [rewrite unsigned_lit in K by lia; lia|].
  pose proof (tape_wf_root _ _ _ _ _ WF) as [EL NR]. pose proof WF as (_ & SNR & TW0 & TWN & _).
  set (tn := Z.of_nat (length tws)) in *. set (sn := Z.of_nat (length sbs)) in *.
  pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) ltac:(lia)) as TW1R.

  pose proof VRg as (EELS0 & SZR & CAPB & A0 & AH & SVg & BLKg).
  destruct BLKg as [(C0 & _)|(CP1 & A16 & APOS & ELg)]; [exfalso; lia|].
  destruct (atp_elsA_shape d (chars bs)) as (P0 & [P1 L1] & rest & EELS & P0Z & ES0).
  destruct (atp_ptr_bytes d bs _ P1 L1 rest mg EELS BSg) as (bsp & EPTR & EL1 & PTRC).
  rewrite EELS in ELg. cbn [velts fst snd] in ELg.
  assert (INCLg : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σg)) by (intros e He; rewrite LVg; do 6 right; apply in_or_app; right; exact He).
  assert (INAg : In (A, 16 * Z.of_nat P) (rt_live RT Σg)).
  { rewrite LVg. do 6 right. apply in_or_app. left. unfold vblockA. destruct (Z.eqb_spec capv 0); [lia|]. apply ann_block_vis. }
  assert (INTg : In (tape, al_tape cap) (rt_live RT Σg)) by (rewrite LVg; do 4 right; left; reflexivity).
  assert (INSg : In (sbuf, al_sbuf cap) (rt_live RT Σg)) by (rewrite LVg; do 5 right; left; reflexivity).
  pose proof (af_live_range RT AF Σg mg A _ ARTg INAg) as (AR0 & AR1 & AR2). rewrite SPg in AR1.
  pose proof (af_live_range RT AF Σg mg tape _ ARTg INTg) as (TR0 & TR1 & TR2). rewrite SPg in TR1.
  pose proof (af_live_range RT AF Σg mg sbuf _ ARTg INSg) as (SR0 & SR1 & SR2). rewrite SPg in SR1.
  pose proof (al_tape_bounds cap ltac:(lia)) as TPB. pose proof (al_sbuf_bounds cap ltac:(lia)) as SBB.
  assert (SHZA : shz mg A 32).
  { pose proof (shz_live RT AF Σg mg A _ ARTg INAg ltac:(clear - A16; Z.div_mod_to_equations; lia)) as X.
    eapply shz_sub; [exact X| lia|]. clear - P2. Z.div_mod_to_equations. nia. }
  pose proof PST as (FOBJP & (q1 & q17 & q57 & PCg) & _).
  assert (SHZD : shz mg (f + 120) 8) by (eapply shz_sub; [exact (fobj_shz RT AF Σg mg (f + 96) 80 ARTg FOBJP)| lia| lia]).
  assert (SHZT : shz mg (tape + 8) 8).
  { pose proof (shz_live RT AF Σg mg tape _ ARTg INTg ltac:(clear - MODS; Z.div_mod_to_equations; lia)) as X.
    eapply shz_sub; [exact X| lia|]. clear - TPB. Z.div_mod_to_equations. lia. }
  assert (DOCC : rw_cells asegs mg (f + 120) [C8 (Z_to_bv 64 tape); C8 (Z_to_bv 64 sbuf); C8 (Z_to_bv 64 cap); C8 (Z_to_bv 64 4294967295); C1 z8; CB 7 q57; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
  { unfold pid_cells in PCg.
    lazymatch type of PCg with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?rest) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: rest) with ([c0; c1; c2; c3; c4; c5] ++ rest) in PCg end.
    apply Zvw.rw_cells_app in PCg. destruct PCg as [_ X]. cbn [cells_size csize Nat.add] in X. replace (f + 96 + Z.of_nat 24) with (f + 120) in X by lia. exact X. }
  pose proof FRlg as JN. unfold fa_locals2 in JN.
  lazymatch type of JN with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: nil) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: nil) with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9] ++ [c10]) in JN end.
  apply Zvw.rw_cells_app in JN. destruct JN as [_ JN]. cbn [cells_size csize Nat.add] in JN. replace (sp' + Z.of_nat 104) with (sp' + 104) in JN by lia.
  assert (P0R : 0 <= P0 < 2^64).
  { destruct P0Z as [(-> & _)| ->]; [lia|]. destruct INLV as [(p & k & Hin & Q1 & Q2)|(_ & DL)]; [| clear - D0 DL; ul].
    pose proof (af_live_range RT AF Σg mg p k ARTg (INCLg _ Hin)) as (_ & R1 & _). rewrite SPg in R1. clear - D0 Q1 Q2 R1 SP0R. ul. }
  assert (L0R : 0 <= zlength (atp_s0 (chars bs)) < 2^64).
  { pose proof (zlength_nonneg (atp_s0 (chars bs))). pose proof (atp_s0_len (chars bs)) as X. rewrite chars_length in X. subst n. lia. }
  assert (P1R : 0 <= P1 /\ P1 + Z.of_nat (length bsp) < 2^47).
  { destruct PTRC as [(-> & ->)|(Q1 & Q2 & _)]; [cbn; lia|]. destruct INLV as [(p & k & Hin & Q3 & Q4)|(E0 & DL)].
    - pose proof (af_live_range RT AF Σg mg p k ARTg (INCLg _ Hin)) as (_ & R1 & _). rewrite SPg in R1. clear - D0 Q1 Q2 Q3 Q4 R1 SP0R. subst n. ul.
    - subst bs n. cbn [length] in Q2. clear - D0 DL Q1 Q2. ul. }
  assert (L1R : 0 <= L1 < 2^64) by (rewrite EL1; clear - P1R; ul).
  pose proof (fa_walkR usp sp' f A tape P0 (zlength (atp_s0 (chars bs))) P1 L1 (velts rest) (C8 (Z_to_bv 64 (A + 16 * Z.of_nat P))) (C8 (Z_to_bv 64 (A + 16 * capv))) _ tws
                x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6x s7x s8x t3 t4 t5 t6 j20 jn F fc mg
                FPOS ltac:(ul) ltac:(apply Z.div_pos; lia) ltac:(clear - SP0R LOW LOR SPR; ul) ltac:(clear - SPT SPR; ul) APOS ltac:(lia) TR0 ltac:(clear - TR1 SP0R TPB; ul)
                ltac:(clear - P1R; ul) L1R P0R L0R ltac:(lia) TW1R RC JN SVg ELg DOCC TAPEB SHZA SHZD SHZT MIg) as WR.
  unfold sa_regs, TPV in WR. fold S in WR.
  lazymatch type of WR with evt asegs _ ?X =>
    assert (WR' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact WR) end.
  clear WR.
  apply (cps_realizes asegs _ _ _ c (asta_evt_c RT AF Σg PMc _ _ MST WR') ltac:(unfold sa_regs in Hc; subst S; exact Hc)). clear WR'. intros c6 Hc6.
  destruct (ASTA_unpack RT Σg _ _ c6 Hc6) as (ms6 & X6 & Hc6'). clear Hc6.
  destruct X6 as [(pc & ra' & m1 & a4' & a5' & a6' & a7' & PC & -> & MU1 & WM1 & MI1 & NODE1)|(_ & _ & a1' & a2' & a3' & a4' & a5' & a6' & a7' & ->)].
  2: {
    exact (lftoi_tail Σ Σg PMc m mg usp sp' f A lo d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a1' a2' a3' a4' a5' a6' a7' s6x s7x s8x t3 t4 t5 t6 F fc h3 t
             FDO MST INLV FRS0 LVPOS LOW LOR SPT SPA INV PD CRT SPR SPA' FPOS F64 FR1' FSEG2 FSELF SHB0 SHT FRM T c6
             (conj ltac:(unfold sa_regs, TPV in Hc6' |- *; subst S; exact Hc6') (cfrm0_of_asta RT Σg PMc (eq _) c6 Hc6' ltac:(intros ms0 <-; exact FRM))) Hk). }

  assert (ART1 : ART RT Σg m1).
  { apply (art_client_write RT AF Σg mg m1 sp' ARTg ltac:(rewrite SPg; ul)); [| exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ul. }
  assert (AG1 : agree_on (fun x => ~ (sp' + 104 <= x < sp' + 120)) mg m1).
  { apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [outside]. split; [exact Hx| exact I]. }
  assert (INFg : In (f, 2%nat) (rt_frames RT Σg)) by (rewrite FRSg; left; reflexivity).
  pose proof (af_frames_align RT AF Σg mg f 2%nat ARTg INFg) as [_ FSEGg].

  assert (PBX : exists PB NPB, bsp = [] \/ (In (PB, NPB) (rt_live RT Σ) /\ PB <= P1 /\ P1 + Z.of_nat (length bsp) <= PB + NPB)).
  { destruct PTRC as [(_ & ->)|(Q1 & Q2 & _)]; [exists 0, 0; left; reflexivity|].
    destruct INLV as [(p & k & Hin & Q3 & Q4)|(E0 & _)].
    - exists p, k. right. split; [exact Hin| subst n; lia].
    - exists 0, 0. left. subst bs n. cbn [length] in Q2. destruct bsp; [reflexivity| cbn [length] in Q2; lia]. }
  destruct PBX as (PB & NPB & PBF).
  assert (LBSP : Z.of_nat (length bsp) <= n) by (destruct PTRC as [(_ & ->)|(Q1 & Q2 & _)]; [cbn; lia| lia]).
  assert (ECL : zlength (chars bsp) = Z.of_nat (length bsp)) by apply chars_length.
  set (E := mkAEA lo usp (f + 120) f 2%nat tape (al_tape cap) sbuf (al_sbuf cap) tws sbs P1 (chars bsp) PB NPB).
  assert (OKE : aenvA_ok E).
  { apply mkAEAok; subst E; cbn [ae_lo ae_hi ae_DOC ae_fD ae_kD ae_TAPE ae_NT ae_SBUF ae_NS ae_tws ae_sbs ae_PTR ae_p1 ae_PB ae_NPB].
    - exact WF.
    - exact SBSR.
    - apply chars_range.
    - rewrite ECL. lia.
    - split; [clear - MODS; lia|]. split; [unfold al_tape; rewrite Z.mul_comm, Z.mod_mul by lia; reflexivity|].
      split; [unfold al_tape; subst tn cap; clear - LT; lia|]. split; [exact TR0| clear - TR1 LOW; lia].
    - split; [clear - MODS; lia|]. split; [unfold al_sbuf, roundup64; clear; Z.div_mod_to_equations; lia|].
      split; [subst sn cap; clear - LS; lia|]. split; [exact SR0| clear - SR1 LOW; lia].
    - intros NE. destruct PBF as [E0|(INPB & Q1 & Q2)]; [exfalso; apply NE; rewrite E0; reflexivity|].
      pose proof (af_live_range RT AF Σg mg PB NPB ARTg (INCLg _ INPB)) as (RB0 & RB1 & _). rewrite SPg in RB1.
      split; [exact RB0|]. rewrite ECL. clear - Q1 Q2 RB1 LOW. lia.
    - lia.
    - change (fs_size 2) with 256. split; [clear - F64; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|]. split; [exact FSEGg| clear - FR1' LOW; lia].
    - clear - SP0W LOW. unfold STACK_WIN in *. lia.
    - clear - LOR SPT. ul. }
  assert (LVE : a_live RT Σg E).
  { unfold a_live; subst E; cbn [ae_lo ae_fD ae_kD ae_TAPE ae_NT ae_SBUF ae_NS ae_p1 ae_PB ae_NPB].
    split; [exact INTg|]. split; [exact INSg|]. split; [destruct PBF as [->|(INPB & _)]; [left; reflexivity| right; exact (INCLg _ INPB)]|].
    split; [exact INFg| rewrite SPg; exact LOW]. }
  assert (AI1 : AINV_A E m1).
  { unfold AINV_A; subst E; cbn [ae_DOC ae_TAPE ae_SBUF ae_tws ae_sbs ae_PTR ae_p1].
    split. { apply (bytes_at_agree asegs mg m1 _ _ TAPEB). eapply agree_sub; [exact AG1|]. intros x Hx. cbv beta in *. rewrite u64s_length, length_map in Hx.
             clear - Hx TR1 TPB LT LOW LOR SPR. subst tn cap. unfold al_tape in *. ul. }
    split. { apply (bytes_at_agree asegs mg m1 _ _ SBUFB). eapply agree_sub; [exact AG1|]. intros x Hx. cbv beta in *. rewrite length_map in Hx.
             clear - Hx SR1 LS LOW LOR SPR. subst sn cap. ul. }
    split. { change (map (Z_to_bv 8) (chars bsp)) with (to_bytes (chars bsp)). rewrite to_bytes_chars.
             destruct PTRC as [(-> & ->)|(Q1 & Q2 & BSP)]; [apply bytes_at_nil; lia|].
             apply (bytes_at_agree asegs mg m1 _ _ BSP). eapply agree_sub; [exact AG1|]. intros x Hx. cbv beta in *.
             destruct INLV as [(p & k & Hin & Q3 & Q4)|(E0 & _)]; [| subst bs n; cbn [length] in Q2; lia].
             pose proof (af_live_range RT AF Σg mg p k ARTg (INCLg _ Hin)) as (_ & R1 & _). rewrite SPg in R1. clear - Hx Q1 Q2 Q3 Q4 R1 LOW LOR SPR. subst n. ul. }
    split. { lazymatch type of DOCC with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) => change (c0 :: c1 :: rest) with ([c0; c1] ++ rest) in DOCC end.
             apply Zvw.rw_cells_app in DOCC. destruct DOCC as [DC _].
             apply (rw_cells_agree asegs mg m1 _ _ DC); [| exact WM1]. eapply agree_sub; [exact AG1|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta.
             clear - Hx FR1' LOW LOR SPR. ul. }
    replace (shad (f + 120)) with (S + Z.of_nat 15) by (subst S; unfold shad, SHB; Z.div_mod_to_equations; lia).
    pose proof FSg as X. unfold fa_shadow2 in X. cbn [map app repeat] in X.
    lazymatch type of X with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?d0 :: ?d1 :: ?rest) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: d0 :: d1 :: rest)
        with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14] ++ [d0; d1] ++ rest) in X end.
    apply Zvw.rw_cells_app in X. destruct X as [_ X]. apply Zvw.rw_cells_app in X. destruct X as [X _].
    cbn [cells_size csize Nat.add] in X. destruct X as [[_ HB] _]. cbn [cells_bytes cbytes app] in HB.
    apply (bytes_at_agree asegs mg m1 _ _ HB). eapply agree_sub; [exact AG1|]. intros x Hx. cbv beta in *. cbn [length] in Hx. clear - Hx SHT LOW LOR SPR. subst S. ul. }
  assert (PAT : ptr_atA E P1 (chars bsp)) by (exists []; subst E; cbn [ae_p1 ae_PTR app]; split; [reflexivity| unfold zlength; cbn [length]; lia]).

  pose proof FRlg as OUTg. unfold fa_locals2 in OUTg.
  lazymatch type of OUTg with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: rest) with ([c0; c1; c2; c3] ++ [c4] ++ rest) in OUTg end.
  apply Zvw.rw_cells_app in OUTg. destruct OUTg as [_ OUTg]. apply Zvw.rw_cells_app in OUTg. destruct OUTg as [OUTg _].
  cbn [cells_size csize Nat.add] in OUTg. replace (sp' + Z.of_nat 32) with (sp' + 32) in OUTg by lia.
  assert (OUT1 : rw_cells asegs m1 (sp' + 32) [CB 24 jo]).
  { apply (rw_cells_agree asegs mg m1 _ _ OUTg); [| exact WM1]. eapply agree_sub; [exact AG1|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. lia. }
  pose proof AI1 as AI1'. pose proof INV as (_ & _ & STg' & _).
  assert (ST1 : stk asegs m1 lo sp').
  { apply (stk_agree asegs mg m1 _ _ STg'); [| exact WM1]. eapply agree_sub; [exact AG1|]. intros x Hx. cbv beta in *. lia. }
  assert (CRL : obj_costA (Nat.pred TAPE_MAX_DEPTH) (zlength (chars bsp)) <= rt_credit RT Σg).
  { rewrite ECL. change (Nat.pred TAPE_MAX_DEPTH) with 1023%nat. unfold obj_costA, LVL_C1, DCOST. clear - CRg CR0 VCB PC0 MC0 VC0 PCB MCB DLR LBSP BSL. subst P n. unfold FUZZ_COST, DCOST in *. lia. }
  assert (PREO : forall need cost frames, need <= obj_needA (Nat.pred TAPE_MAX_DEPTH) -> cost <= obj_costA (Nat.pred TAPE_MAX_DEPTH) (zlength (chars bsp)) -> (frames <= 1024)%nat ->
                  lvl_pre RT E Σg m1 sp' (sp' + 32) (sp' + 104) 1 jo need cost frames).
  { intros need cost frames HN HC HF. unfold lvl_pre. subst E. cbn [ae_DOC ae_hi ae_lo].
    split; [exact NODE1|]. split; [lia|]. split; [lia|]. split; [clear - SPA'; Z.div_mod_to_equations; lia|].
    split; [exact OUT1|]. split; [lia|]. split; [lia|]. split; [clear - SPA'; Z.div_mod_to_equations; lia|]. split; [right; lia|].
    split; [exact ART1|]. split; [exact MI1|]. split; [exact ST1|].
    split; [change (Nat.pred TAPE_MAX_DEPTH) with 1023%nat in HN; unfold obj_needA, elem_needA in HN; clear - HN LOR SPR; ul|].
    split; [clear - SPA'; Z.div_mod_to_equations; lia|].
    split; [rewrite FRSg; cbn [length]; unfold FRAMES_MAX2; lia|]. split; [lia|].
    split; [rewrite LVg; cbn [length]; rewrite length_app; pose proof (vblockA_length A capv (Z.of_nat P)); clear - H LVB; unfold FUZZ_LIVE, LIVE_MAX in *; lia|].

    change (lposx (rt_live RT Σg)). rewrite LVg.
    pose proof (roundup64_ge cap) as RG1. pose proof (roundup64_ge (cap + 3)) as RG2. pose proof (roundup64_ge (5 * (cap / 3) + 64)) as RG3.
    do 6 (apply lposx_cons; [first [lia| unfold sc_idx, al_tape, al_sbuf; clear - CAPR RG1 RG2 RG3; Z.div_mod_to_equations; lia]|]).
    apply lposx_app; [| exact (lposx_of_pos _ LVPOS)].
    unfold vblockA. destruct (capv =? 0); [intros p' k' []| apply lposx_ann_block; lia]. }

  assert (LVLK : forall (cost : Z) (cr : config), 0 <= cost <= obj_costA (Nat.pred TAPE_MAX_DEPTH) (zlength (chars bsp)) ->
            lvl_postA RT E Σg PMc (Z_to_bv 64 ra') sp' gp (Z_to_bv 64 usp) (Z_to_bv 64 sp') (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120))
                      s6x s7x s8x (Z_to_bv 64 S) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) (sp' + 32) m1 cost cr /\ cfrm0 cr ->
            realizes asegs cr T).
  { intros cost cr HCOST ((Σr & Hcr & LVr & FRSr & SPr & CRr) & FCr).
    destruct (ASTA_unpack_f RT Σr _ _ cr Hcr FCr) as (msr & (vr & m8 & RS8 & (ART8 & MI8 & ST8) & PRES8 & (jo' & OUT8) & AI8) & FRM8 & Hcr'). clear Hcr.
    destruct RS8 as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & F8 & fc8 & ->).
    cbn [ms_fcsr] in FRM8. subst E. cbn [ae_lo] in ST8. unfold TPV in Hcr'.
    assert (RA : ret_pc (Z_to_bv 64 ra') = Z_to_bv 64 ra') by (destruct PC as [(_ & -> & _)|(_ & -> & _)]; apply ret_pc_even; lia). rewrite RA in Hcr'.
    assert (FRSr' : rt_frames RT Σr = [(f, 2%nat)]) by (rewrite FRSr; exact FRSg).
    assert (EQ8 : forall a : word, lp_dom RT Σ usp sp' f A d bs (bv_unsigned a) -> ~ (sp' + 32 <= bv_unsigned a < sp' + 56) -> ~ (sp' + 104 <= bv_unsigned a < sp' + 120) -> m8 a = mg a).
    { intros a Ha H1 H2. rewrite <- (AG1 a H2). apply PRES8; [| cbn [outside]; split; [clear - H1; lia| exact I]].
      exact (lp_client RT AF Σ Σg mg usp sp' f lo d A bs ARTg FRSg FRS0 INCLg INAg INLV FPOS F64 ltac:(lia) SPT _ Ha). }
    assert (NODE8 : rw_cells asegs m8 (sp' + 104) [C8 (Z_to_bv 64 (f + 120)); C8 (Z_to_bv 64 1)]).
    { apply (rw_cells_agree_nw asegs m1 m8 _ _ NODE1). apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES8). intros x Hx. cbn [cells_size csize Nat.add] in Hx.
      split; [left; ul| cbn [outside]; split; [lia| exact I]]. }
    destruct (rw_cells_forget asegs m8 (sp' + 104) _ NODE8) as (jn' & NODE8'). cbn [cells_size csize Nat.add] in NODE8'.
    pose proof (lp_inv_xfer_junk RT LIB LIB_loc AF Σ Σg Σr m mg m8 usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A jo' jn'
                  INV FRS0 INCLg INAg INLV LOW LOR SPR FRSr SPr ART8 MI8 ST8 EQ8 OUT8 NODE8') as INV8.
    assert (PD8 : pdone RT Σr m8 (f + 96) (vblockA A capv (Z.of_nat P) ++ rt_live RT Σ)).
    { apply (pdone_xfer RT AF Σg Σr mg m8 (f + 96) _ PD ARTg FRSr LVr). intros a Ha.
      pose proof (af_frames_range RT AF Σg mg f 2%nat ARTg INFg) as (_ & FR1g & _ & FLVg). change (fs_size 2) with 256 in FR1g, FLVg. rewrite SPg in FR1g.
      pose proof (fframe_ranges RT AF Σg mg f 2 ARTg INFg) as (_ & _ & _ & _ & SHTg). change (fs_size 2) with 256 in SHTg. rewrite SPg in SHTg.
      assert (LOWa : bv_unsigned a < lo).
      { destruct Ha as [(f9 & k9 & Hin & Hr)|[(f9 & k9 & Hin & Hr)|(p & k & Hin & Hr)]].
        - rewrite FRSg in Hin. destruct Hin as [Hin|[]]. injection Hin as <- <-. change (fs_size 2) with 256 in Hr. clear - Hr FR1g LOW. lia.
        - rewrite FRSg in Hin. destruct Hin as [Hin|[]]. injection Hin as <- <-. change (fs_size 2) with 256 in Hr. unfold shad in *. clear - Hr SHTg LOW. lia.
        - pose proof (af_live_range RT AF Σg mg p k ARTg Hin) as (_ & R1 & _). rewrite SPg in R1. clear - Hr R1 LOW. lia. }
      rewrite <- (AG1 a ltac:(cbv beta; clear - LOWa LOR SPR; ul)). apply PRES8; [| cbn [outside]; split; [clear - LOWa LOR SPR; ul| exact I]].
      destruct Ha as [H|[H|H]]; [right; right; right; left; exact H| right; right; right; right; exact H| right; right; left; exact H]. }
    assert (CR8 : rt_credit RT Σ - FUZZ_COST <= rt_credit RT Σr).
    { rewrite ECL in HCOST. change (Nat.pred TAPE_MAX_DEPTH) with 1023%nat in HCOST. unfold obj_costA, LVL_C1, DCOST in HCOST.
      clear - CRr HCOST CRg CR0 VCB PC0 MC0 VC0 PCB MCB DLR LBSP BSL. subst P n. unfold FUZZ_COST, DCOST in *. lia. }

    pose proof (fa_walk11b ra' usp sp' f (Z_to_bv 64 ra') gp (Z_to_bv 64 0x646eb0) w0 w1 w2 vr g1 g2 g3 g4 g5 g6 g7 s6x s7x s8x w3 w4 w5 w6 F8 fc8 m8
                  ltac:(destruct PC as [(_ & -> & _)|(_ & -> & _)]; [left| right]; reflexivity) FPOS ltac:(ul)) as W11.
    unfold sa_regs in W11. fold S in W11.
    lazymatch type of W11 with evt asegs _ ?X =>
      assert (W11' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W11) end.
    clear W11.
    apply (cps_realizes asegs _ _ _ cr (asta_evt_c RT AF Σr PMc _ _ MST W11') ltac:(subst S; exact Hcr')). clear W11'. intros c9 Hc9.
    destruct (ASTA_unpack RT Σr _ _ c9 Hc9) as (ms9 & <- & Hc9'). clear Hc9.
    exact (lftoi_tail Σ Σr PMc m m8 usp sp' f A lo d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 s6x s7x s8x w3 w4 w5 w6 F8 fc8 h3 t
             FDO MST INLV FRS0 LVPOS LOW LOR SPT SPA INV8 PD8 CR8 SPR SPA' FPOS F64 FR1' FSEG2 FSELF SHB0 SHT FRM8 T c9
             (conj ltac:(unfold sa_regs; subst S; exact Hc9') (cfrm0_of_asta RT Σr PMc (eq _) c9 Hc9' ltac:(intros ms0 <-; exact FRM8))) Hk). }

  rewrite EL1, <- ECL in Hc6'. unfold TPV in Hc6'. fold S in Hc6'.
  pose proof (cfrm0_of_asta RT Σg PMc (eq _) c6 Hc6' ltac:(intros ms0 <-; exact FRM)) as FC6.
  assert (CSTA : 0 <= arr_costA (Nat.pred TAPE_MAX_DEPTH) (zlength (chars bsp)) <= obj_costA (Nat.pred TAPE_MAX_DEPTH) (zlength (chars bsp)))
    by (rewrite ECL; unfold arr_costA, obj_costA, LVL_C1, DCOST; lia).
  destruct (elem_view_of (Tf tws) (Tf sbs) sn ck_any (fun c0 cv H => H) ltac:(lia) TAPE_MAX_DEPTH 1 (tn - 1) EL ltac:(lia) ltac:(lia))
    as [TY Ej|TY Ej|TY Ej STR|d' e cc Ed TY Ej NXT CLOSE TILES|d' e cc Ed TY Ej NXT CLOSE TILES]; unfold ty in TY.
  - exfalso. destruct PC as [(_ & _ & K)|(_ & _ & K)]; destruct TY as [TY|[TY|TY]]; rewrite TY in K; discriminate K.
  - exfalso. destruct PC as [(_ & _ & K)|(_ & _ & K)]; destruct TY as [TY|[TY|TY]]; rewrite TY in K; discriminate K.
  - exfalso. destruct PC as [(_ & _ & K)|(_ & _ & K)]; rewrite TY in K; discriminate K.
  -
    destruct PC as [(_ & _ & K)|(-> & -> & _)]; [exfalso; rewrite TY in K; discriminate K|].
    change TAPE_MAX_DEPTH with (Datatypes.S (Nat.pred TAPE_MAX_DEPTH)) in Ed. injection Ed as <-.
    apply (HARR E OKE Σg PMc (chars bsp) 1 e cc sp' (sp' + 32) (sp' + 104) P1 (Z_to_bv 64 0x96ecc) gp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a4' a5' a6' a7'
             (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120)) s6x s7x s8x (Z_to_bv 64 S) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) t3 t4 t5 t6
             F fc m1 jo FDO MST LVE AI1 PAT TY NXT CLOSE TILES ltac:(lia) ltac:(subst E tn; cbn [ae_tws]; lia)
             (PREO (arr_needA (Nat.pred TAPE_MAX_DEPTH)) (arr_costA (Nat.pred TAPE_MAX_DEPTH) (zlength (chars bsp))) (Nat.pred TAPE_MAX_DEPTH)
                   (arr_le_obj_needA _) (proj2 CSTA) ltac:(change (Nat.pred TAPE_MAX_DEPTH) with 1023%nat; lia)) FRM T c6 (conj Hc6' FC6)).
    intros cr Hcr. exact (LVLK _ cr CSTA Hcr).
  -
    destruct PC as [(-> & -> & _)|(_ & _ & K)]; [| exfalso; rewrite TY in K; discriminate K].
    change TAPE_MAX_DEPTH with (Datatypes.S (Nat.pred TAPE_MAX_DEPTH)) in Ed. injection Ed as <-.
    assert (CSTO : 0 <= obj_costA (Nat.pred TAPE_MAX_DEPTH) (zlength (chars bsp)) <= obj_costA (Nat.pred TAPE_MAX_DEPTH) (zlength (chars bsp))) by lia.
    apply (HOBJ E OKE Σg PMc (chars bsp) 1 e cc sp' (sp' + 32) (sp' + 104) P1 (Z_to_bv 64 0x96e00) gp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a4' a5' a6' a7'
             (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120)) s6x s7x s8x (Z_to_bv 64 S) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) t3 t4 t5 t6
             F fc m1 jo FDO MST LVE AI1 PAT TY NXT CLOSE TILES ltac:(lia) ltac:(subst E tn; cbn [ae_tws]; lia)
             (PREO (obj_needA (Nat.pred TAPE_MAX_DEPTH)) (obj_costA (Nat.pred TAPE_MAX_DEPTH) (zlength (chars bsp))) (Datatypes.S (Nat.pred TAPE_MAX_DEPTH))
                   (Z.le_refl _) (Z.le_refl _) ltac:(change (Nat.pred TAPE_MAX_DEPTH) with 1023%nat; lia)) FRM T c6 (conj Hc6' FC6)).
    intros cr Hcr. exact (LVLK _ cr CSTO Hcr).
Qed.

End Top3.

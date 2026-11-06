(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z119 FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim Stdio Zpb Z3o.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Zvw Z4d.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Layout Shadow Zks Zkt Zi4 D_defs D_kit D_clx Z87 Z82 I_lkit Sj_rtf Zpm Zpl Zq2 Zq3
  Sj_new Zpo Zwn Z4a Z73 Z5g Z6m Z71 Z5h Z5i Z5j Z6q Z6y Z6p
  Z4e Z4l Z4m Z4n Z52 Z57.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Top2c.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis AF : art_facts RT.
Hypothesis DELA : del_cps RT e_delarr.
Hypothesis PID : pid_cps RT LIB.

Local Ltac nomod := repeat match goal with H : _ mod _ = _ |- _ => clear H end.
Local Ltac ul := unfold FUZZ_STACK, ATPA_SPLITINTO_STACK, ATPA_SPLIT_STACK, ATPA_PUSH_STACK, PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma lftoi_ptail : forall (Σ Σ1 Σn : rts RT) PMc (m mx : mem) (usp sp' f A lo d buf P0 : Z) (bs bs0 : list byte)
    (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (u0 u1 u2 v6 v7 u3 u4 u5 u6 : word) (Fx : bvmap 5 word) (fcx : bv 32) (h3 t p1 p17 p57 : list byte),
  fdfs_only PMc -> mat_stable PMc ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d < SEGTOP_A)) ->
  rt_frames RT Σ = [] ->
  Z.of_nat (length (rt_live RT Σ)) + FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ -> 8 + vcost_pushes (atp_P (chars bs)) 0 0 <= 2^32 ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= usp -> usp + 16 <= USTACK_TOP ->
  vliveA (rt_live RT Σ1) A (vcap_iter (atp_P (chars bs)) 0 0) (Z.of_nat (atp_P (chars bs))) (rt_live RT Σ) ->
  rt_credit RT Σ - 2 - vcost_pushes (atp_P (chars bs)) 0 0 <= rt_credit RT Σ1 ->
  Z.of_nat (length (rt_live RT Σ1)) <= 3 + Z.of_nat (length (rt_live RT Σ)) -> lposx (rt_live RT Σ1) ->
  rt_live RT Σn = (buf, Z.of_nat (length bs0) + 64) :: rt_live RT Σ1 -> rt_frames RT Σn = [(f, 2%nat)] -> rt_sp0 RT Σn = rt_sp0 RT Σ ->
  rt_credit RT Σn = rt_credit RT Σ1 - mcost (Z.of_nat (length bs0) + 64) -> buf mod 16 = 0 ->
  Z.of_nat (length bs0) <= 1048512 -> 0 <= Z.of_nat (length bs0) <= Z.of_nat (length bs) ->
  doc_len bs = Z.of_nat (length bs0) -> doc_cap bs = Z.max (Z.of_nat (length bs0)) 32 ->
  usp - 240 <= sp' <= usp - 224 -> sp' mod 32 = 0 -> 0 < f -> f mod 64 = 0 -> f + 256 <= rt_sp0 RT Σ - STACK_WIN ->
  (f + 256 <= 0x10000 \/ SEGTOP_A <= f) -> (f + 256 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 32 <= f) ->
  SHB <= f / 8 + 2147450880 -> f / 8 + 2147450880 + 32 + 1 <= rt_sp0 RT Σ - STACK_WIN ->

  lp_inv RT LIB Σ Σn m mx usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A ->
  rw_cells asegs mx (f + 96) (parser_init p1 p17 p57) ->
  bytes_at asegs mx buf (bs0 ++ repeat z8 64) -> frm0 fcx ->
  cps_f (ASTA RT Σn PMc (eq (sa_regs e_pid (Z_to_bv 64 0x96c50) sp' gp (Z_to_bv 64 0x646eb0) u0 u1 u2 usp (Z_to_bv 64 (sp' + 56)) (Z_to_bv 64 (f + 96))
                                (Z_to_bv 64 (f + 120)) (Z_to_bv 64 buf) (Z_to_bv 64 (Z.of_nat (length bs0))) (Z_to_bv 64 0) v6 v7 f (Z_to_bv 64 buf)
                                (Z_to_bv 64 (Z.of_nat (length bs0))) (Z_to_bv 64 P0) u3 u4 u5 u6 Fx fcx mx)))
    (gate_postA RT LIB Σ PMc usp lo d bs ra gp (Z_to_bv 64 0x646eb0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m).
Proof using LIB_loc AF DELA PID.
  intros Σ Σ1 Σn PMc m mx usp sp' f A lo d buf P0 bs bs0 ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u0 u1 u2 v6 v7 u3 u4 u5 u6 Fx fcx h3 t p1 p17 p57
    FDO MST INLV FRS0 LVB CR0 VCB LOW LOR SPT VL1 CR1 LVL1 LPX1 LVn FRSn' SPn' CRn B16 SMALL L0R EDL EDC SPR SPA' FPOS F64 FR1' FSEG2 FSELF SHB0 SHT INVx FPx BUFx FRMx.
  intros T cx (Hcx & FCx) Hk. unfold sa_regs in Hcx.
  set (l0 := Z.of_nat (length bs0)) in *. set (P := atp_P (chars bs)) in *. set (S := f / 8 + 2147450880) in *. set (capv := vcap_iter P 0 0) in *.
  set (cap := Z.max l0 32) in *.
  pose proof INVx as (ARTx0 & _). pose proof (af_sp0_range RT AF Σn mx ARTx0) as SP0R. rewrite SPn' in SP0R. clear ARTx0.
  assert (EU1 : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; ul).
  assert (EUSP : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; ul).
  assert (P2 : (2 <= P)%nat) by (subst P; unfold atp_P; lia).
  pose proof (vcap_iter_inv P 0 0 ltac:(lia) ltac:(lia)) as CAPI. rewrite Z.add_0_l in CAPI. fold capv in CAPI.
  pose proof (sc_idx_bounds cap ltac:(lia)) as IXB. pose proof (al_tape_bounds cap ltac:(lia)) as TPB. pose proof (al_sbuf_bounds cap ltac:(lia)) as SBB.
  pose proof (pid_costA_bound l0 ltac:(lia)) as PCB. pose proof (mcost_le (l0 + 64) ltac:(lia)) as MCB. pose proof (mcost_nonneg (l0 + 64) ltac:(lia)) as MC0.
  assert (VC0 : 0 <= vcost_pushes P 0 0) by (apply vcost_pushes_nonneg; lia).
  assert (INCL1 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ1)).
  { intros e He. unfold vliveA in VL1. rewrite VL1. apply in_or_app. right. exact He. }
  assert (INA : In (A, 16 * Z.of_nat P) (rt_live RT Σ1)).
  { unfold vliveA, vblockA in VL1. rewrite VL1. apply in_or_app. left. destruct (Z.eqb_spec capv 0); [lia|]. apply ann_block_vis. }
  assert (INCLn : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σn)) by (intros e He; rewrite LVn; right; exact (INCL1 e He)).
  assert (INAn : In (A, 16 * Z.of_nat P) (rt_live RT Σn)) by (rewrite LVn; right; exact INA).
  assert (INBn : In (buf, l0 + 64) (rt_live RT Σn)) by (rewrite LVn; left; reflexivity).
  assert (CLIn : forall my, ART RT Σn my -> forall x, lp_dom RT Σ usp sp' f A d bs x -> aclient (rt_live RT Σn) (rt_frames RT Σn) sp' x).
  { intros my ARTy. exact (lp_client RT AF Σ Σn my usp sp' f lo d A bs ARTy FRSn' FRS0 INCLn INAn INLV FPOS F64 ltac:(lia) SPT). }
  assert (LPXn : lposx (rt_live RT Σn)) by (rewrite LVn; apply lposx_cons; [lia| exact LPX1]).
  pose proof INVx as (ARTx & MIx & STx & (k0 & k1 & k2 & ko & kr & k13 & kn & FRlx) & _ & _ & _ & _ & _ & _ & LIBx & _ & FRSx & SPx).
  pose proof FRlx as RESx. unfold fa_locals2 in RESx.
  lazymatch type of RESx with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: rest) with ([c0; c1; c2; c3; c4] ++ [c5] ++ rest) in RESx end.
  apply Zvw.rw_cells_app in RESx. destruct RESx as [_ RESx]. apply Zvw.rw_cells_app in RESx. destruct RESx as [RESx _].
  cbn [cells_size csize Nat.add] in RESx. replace (sp' + Z.of_nat 56) with (sp' + 56) in RESx by lia.
  pose proof (lp_fobjP RT LIB Σ Σn m mx usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A INVx FPOS F64) as FOBJx.
  apply (PID Σn PMc (Z_to_bv 64 0x96c50) (Z_to_bv 64 sp') gp (Z_to_bv 64 0x646eb0) u0 u1 u2 (Z_to_bv 64 usp) (Z_to_bv 64 sp')
           (Z_to_bv 64 (sp' + 56)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120)) (Z_to_bv 64 buf) (Z_to_bv 64 l0) (Z_to_bv 64 0) v6 v7
           (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120)) (Z_to_bv 64 buf) (Z_to_bv 64 l0) (Z_to_bv 64 P0)
           (Z_to_bv 64 S) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) u3 u4 u5 u6 Fx fcx mx (f + 96) (sp' + 56) buf bs0 p1 p17 p57 kr lo FDO MST);
    try reflexivity; try assumption; [.. | split; [subst S; exact Hcx| apply (cfrm0_of_asta RT Σn PMc (eq _) cx Hcx); intros ms0 <-; exact FRMx] |].
  * f_equal. lia.
  * rewrite padded_bytes_chars. exact BUFx.
  * rewrite EU1. lia.
  * ul.
  * rewrite LVn. cbn [length]. clear - LVL1 LVB. unfold FUZZ_LIVE, LIVE_MAX in *. lia.
  * rewrite FRSn'. cbn [length]. unfold PID_FRAMES, FRAMES_MAX. lia.
  * rewrite CRn. clear - CR1 CR0 VCB MCB VC0 L0R SMALL PCB. unfold FUZZ_COST in *. subst l0. lia.
  * rewrite EU1. exact STx.
  * rewrite SPn'. exact LOW.
  * rewrite EU1. ul.
  * rewrite EU1. ul.
  * rewrite EU1. clear - SPA'. Z.div_mod_to_equations. lia.
  * intros c11 ((Σp & impl & idx & oc & ia & tape & sbuf & Hc11 & LVp & MODS & FRSp & SPp & CRp) & FC11).
    destruct (ASTA_unpack_f RT Σp _ _ c11 Hc11 FC11) as (ms11 & (v11 & m11 & RS11 & (ART11 & MI11 & ST11) & PRES11 & (r & j20 & RC11 & R64 & OKR11) & LIB11 & PD11 & PST11) & FRM11 & Hc11').
    clear Hc11. destruct RS11 as (z0 & z1 & z2 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & z3 & z4 & z5 & z6 & F11 & fc11 & ->).
    cbn [ms_fcsr] in FRM11. rewrite EU1 in ST11, PRES11. rewrite (ret_pc_even 0x96c50) in Hc11' by lia.
    destruct (rw_cells_forget asegs m11 (sp' + 56) _ RC11) as (jr' & RES11).
    assert (RSZ : cells_size (res_cellsA (f + 96 + 24) r j20) = 24%nat) by (unfold res_cellsA; destruct (bv_eqb _ _); reflexivity). rewrite RSZ in RES11.
    assert (EQ11 : forall a : word, lp_dom RT Σ usp sp' f A d bs (bv_unsigned a) -> ~ (sp' + 56 <= bv_unsigned a < sp' + 80) ->
                    ~ in_ranges LIB_FP (bv_unsigned a) -> m11 a = mx a).
    { intros a Ha H1 H2. apply PRES11; [exact (CLIn mx ARTx _ Ha)|]. cbn [outside]. split; [| split; [clear - H1; lia| exact (outside_of_nin _ _ H2)]].
      exact (lp_apart_frame RT AF Σ Σn mx usp sp' f lo d A (f + 96) (f + 96 + 80) bs ARTx FRSn' FRS0 SPn' INCLn INAn INLV LOW LOR ltac:(lia) FSELF ltac:(lia) ltac:(lia) _ Ha). }
    pose proof (lp_inv_xfer_pid RT LIB LIB_loc AF Σ Σn Σp m mx m11 usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A jr'
                  INVx FRS0 INCLn INAn INLV LOW LOR SPR FSEG2 SHB0 FRSp SPp ART11 MI11 ST11 EQ11 LIB11 RES11) as INV11.
    assert (RCC : res_cellsA (f + 96 + 24) r j20 = res_cellsA (f + 120) r j20) by (f_equal; lia). rewrite RCC in RC11, RSZ.
    clear EQ11 PRES11 Hcx RESx FRlx.

    pose proof (fa_walk9 usp sp' f buf l0 P0 (Z_to_bv 64 0x96c50) gp (Z_to_bv 64 0x646eb0) z0 z1 z2 v11 q1 q2 q3 q4 q5 q6 q7 z3 z4 z5 z6 F11 fc11 m11 FPOS ltac:(ul)) as W9.
    unfold sa_regs in W9. fold S in W9.
    lazymatch type of W9 with evt asegs _ ?X =>
      assert (W9' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W9) end.
    clear W9.
    apply (cps_realizes asegs _ _ _ c11 (asta_evt_c RT AF Σp PMc _ _ MST W9') Hc11'). clear W9'. intros c12 Hc12.
    destruct (ASTA_unpack RT Σp _ _ c12 Hc12) as (ms12 & <- & Hc12'). clear Hc12.
    assert (INBp : In (buf, l0 + 64) (rt_live RT Σp)) by (rewrite LVp; do 6 right; exact INBn).
    apply (DELA Σp PMc (Z_to_bv 64 0x96c58) (Z_to_bv 64 sp') gp (Z_to_bv 64 0x646eb0) z0 z1 z2 (Z_to_bv 64 usp) (Z_to_bv 64 sp')
             (Z_to_bv 64 buf) q1 q2 q3 q4 q5 q6 q7
             (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120)) (Z_to_bv 64 buf) (Z_to_bv 64 l0) (Z_to_bv 64 P0)
             (Z_to_bv 64 S) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) z3 z4 z5 z6 F11 fc11 m11 buf (l0 + 64) lo FDO MST INBp eq_refl eq_refl ART11 MI11);
      [| | exact FRM11| split; [subst S; exact Hc12'| apply (cfrm0_of_asta RT Σp PMc (eq _) c12 Hc12'); intros ms0 <-; exact FRM11] |].
    -- unfold call_ok. rewrite EU1, SPp, SPn'. split; [exact ST11|]. split; [exact LOW|]. split; [ul|]. split; [ul| clear - SPA'; Z.div_mod_to_equations; lia].
    -- unfold unwind_ok. rewrite EU1, EUSP. right; right. lia.
    -- intros c13 ((Σd & vd & Hc13 & LVd & FRSd & SPd & CRd) & FC13).
       destruct (ASTA_unpack_f RT Σd _ _ c13 Hc13 FC13) as (ms13 & (m13 & RS13 & (ART13 & MI13 & ST13) & PRES13) & FRM13 & Hc13'). clear Hc13.
       destruct RS13 as (i0 & i1 & i2 & o1 & o2 & o3 & o4 & o5 & o6 & o7 & i3 & i4 & i5 & i6 & F13 & fc13 & ->).
       cbn [ms_fcsr] in FRM13. rewrite EU1 in ST13, PRES13. rewrite (ret_pc_even 0x96c58) in Hc13' by lia.

       unfold vliveA in VL1.
       assert (LVp' : rt_live RT Σp = (ia, 1024) :: (oc, 8192) :: (idx, sc_idx cap) :: (impl, 96) :: (tape, al_tape cap) :: (sbuf, al_sbuf cap)
                                       :: (buf, l0 + 64) :: vblockA A capv (Z.of_nat P) ++ rt_live RT Σ).
       { rewrite LVp, LVn, VL1. subst l0 cap. reflexivity. }
       assert (PD11' : pdone RT Σp m11 (f + 96) ((buf, l0 + 64) :: vblockA A capv (Z.of_nat P) ++ rt_live RT Σ)) by (rewrite <- VL1, <- LVn; exact PD11).
       assert (LPXv : lposx (vblockA A capv (Z.of_nat P) ++ rt_live RT Σ)) by (rewrite <- VL1; exact LPX1).
       destruct (pdone_free RT AF Σp Σd m11 m13 (f + 96) buf (l0 + 64) sp' ia oc idx impl tape sbuf 1024 8192 (sc_idx cap) 96 (al_tape cap) (al_sbuf cap)
                   (vblockA A capv (Z.of_nat P) ++ rt_live RT Σ) PD11' ART11 LVp'
                   ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) LPXv LVd FRSd PRES13) as [PD13 LVd'].
       assert (FRSd' : rt_frames RT Σd = [(f, 2%nat)]) by (rewrite FRSd, FRSp; exact FRSn').
       assert (INCLd : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σd)) by (intros e He; rewrite LVd'; do 6 right; apply in_or_app; right; exact He).
       assert (INAd : In (A, 16 * Z.of_nat P) (rt_live RT Σd)).
       { rewrite LVd'. do 6 right. apply in_or_app. left. unfold vblockA. destruct (Z.eqb_spec capv 0); [lia|]. apply ann_block_vis. }
       assert (EQ13 : forall a : word, lp_dom RT Σ usp sp' f A d bs (bv_unsigned a) -> m13 a = m11 a).
       { intros a Ha. apply PRES13. rewrite <- FRSd. exact (lp_client RT AF Σ Σd m13 usp sp' f lo d A bs ART13 FRSd' FRS0 INCLd INAd INLV FPOS F64 ltac:(lia) SPT _ Ha). }
       pose proof (lp_inv_xfer' RT LIB LIB_loc Σ Σp Σd m m11 m13 usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A INV11 ltac:(lia) FRSd SPd ART13 MI13 ST13 EQ13) as INV13.
       assert (RC13 : rw_cells asegs m13 (sp' + 56) (res_cellsA (f + 120) r j20)).
       { apply (rw_cells_agree_nw asegs m11 m13 _ _ RC11). apply (agree_of_pres _ _ _ _ _ _ PRES13). intros x Hx. cbv beta in Hx. rewrite RSZ in Hx. left. ul. }
       assert (INTd : In (tape, al_tape cap) (rt_live RT Σd)) by (rewrite LVd'; do 4 right; left; reflexivity).
       assert (INSd : In (sbuf, al_sbuf cap) (rt_live RT Σd)) by (rewrite LVd'; do 5 right; left; reflexivity).
       assert (INMd : In (impl, 96) (rt_live RT Σd)) by (rewrite LVd'; do 3 right; left; reflexivity).
       assert (OKR13 : s2a_okres tape sbuf (roundup64 (cap + 3)) (al_sbuf cap) r m13).
       { apply (s2a_okres_agree (fun x => aclient (rt_live RT Σd) (rt_frames RT Σp) sp' x) m11 m13); [intros a Ha; exact (PRES13 a Ha)| | | subst cap l0; exact OKR11].
         - intros a Ha. right; right; left. exists tape, (al_tape cap). split; [exact INTd| unfold al_tape; lia].
         - intros a Ha. right; right; left. exists sbuf, (al_sbuf cap). split; [exact INSd| lia]. }
       pose proof (pidA_st_xfer RT AF Σp Σd (rt_live RT Σd) m11 m13 (f + 96) sp' impl idx oc ia tape sbuf cap ltac:(subst cap l0; exact PST11) ART11 FRSd INMd (or_intror PRES13)) as PST13.

       pose proof (fa_walk10 usp sp' f (Z_to_bv 64 0x96c58) gp (Z_to_bv 64 0x646eb0) i0 i1 i2 vd o1 o2 o3 o4 o5 o6 o7 (Z_to_bv 64 buf) (Z_to_bv 64 l0) (Z_to_bv 64 P0) i3 i4 i5 i6 F13 fc13 m13) as W10.
       unfold sa_regs in W10. fold S in W10.
       lazymatch type of W10 with evt asegs _ ?X =>
         assert (W10' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W10) end.
       clear W10.
       apply (cps_realizes asegs _ _ _ c13 (asta_evt_c RT AF Σd PMc _ _ MST W10') Hc13'). clear W10'. intros c14 Hc14.
       destruct (ASTA_unpack RT Σd _ _ c14 Hc14) as (ms14 & <- & Hc14'). clear Hc14.
       apply Hk. split; [| apply (cfrm0_of_asta RT Σd PMc (eq _) c14 Hc14'); intros ms0 <-; exact FRM13].
       apply (gate_intro RT LIB Σ Σd PMc c14 m m13 usp sp' f A lo d bs ra gp (Z_to_bv 64 0x646eb0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                (Z_to_bv 64 0x96c58) i0 i1 i2 vd o1 o2 o3 o4 o5 o6 o7 (Z_to_bv 64 buf) (Z_to_bv 64 l0) (Z_to_bv 64 P0) i3 i4 i5 i6 F13 fc13 h3 t j20 impl idx oc ia tape sbuf r);
         [ unfold sa_regs; subst S; exact Hc14' | exact FRM13 | exact INV13 | exact RC13 | exact R64 | rewrite EDC; exact OKR13
         | exact PD13 | rewrite EDC; exact PST13
         | exact SPR | exact SPA' | exact FPOS | exact F64 | exact FR1' | exact FSEG2 | exact FSELF | exact SHB0 | exact SHT
         | rewrite EDC; exact LVd' | exact MODS | idtac ].
       rewrite EDL, CRd. subst P l0. clear - CRp CRn CR1 VC0 MC0. lia.
Qed.
End Top2c.

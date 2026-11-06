(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_defs D_kit I_read. Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_read.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require Import L2Kit L2Act L2Stmt B0_fs_L2f B0_sm_mkl B0_sm_L2a.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzArr BzCMem BzCStream BzCState BzCMtf BzCHuff BzArrD CmpMem CmpCut CmpCutSM CmpCutSmA BzCFactsSmA CmpCutSmB BzCFactsGm BzCSmF1 BzCFactsSmB BzCFactsSd CmpHmKit CmpSmKit CmpSmKit2 AsanKit AsanKit2 AsanCut AsanCutB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmas1 BzCHuffF1.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_smV B0_cmp_sdV B0_cmp_smV B0_cmp_smK B0_cmp_smBz B0_cmp_smZ.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).

Section SMG.
Context {BZP : BzParams} {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis HBM : hbMakeCodeLengths_contract RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
(* [comment removed for export] *)
Variables (cx : cctx) (g : eg) (e : est) (lo : Z) (sp gp tp : word).
Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis IMG : cctx_img (aci_c B0C) cx.
Hypothesis GM : g_mtf g = true. Hypothesis GB : g_bs g = true. Hypothesis GZ : g_zbits g = Z_to_bv 64 (c_A2 cx + e_nblock e).
Hypothesis SFA : smA_facts e. Hypothesis SFB : smB_facts e znew znew znew znew znew.
Hypothesis TP : tp = Z_to_bv 64 0x6094d8.
Notation usp := (bv_unsigned sp).
Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation FT := (c_FT cx). Notation J := (c_J cx).
Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e). Notation nInUse := (e_nInUse e).
Notation Wsm := [(E, E + 55768); (A2, A2 + ARR2_SIZE)].
Notation cSB := (Z_to_bv 64 2147450880).
(* [comment removed for export] *)
Variables (PMc : Model -> Prop) (P FB SHF SHE : Z) (fr : list (Z * nat)) (live0 : list (Z * Z)) (sp0 : Z).
Hypothesis FDO : fdfs_only PMc. Hypothesis MST : mat_stable PMc.
Hypothesis G : act_geom RT lo P usp sp0 true 2 FB SHF 256 32 fr live0 Wsm.
Hypothesis ACE : alloc_ceiling = sp0 - STACK_WIN.
Hypothesis FRLO : P + 1696 <= usp. Hypothesis FRHI : usp <= P + 1712.
Hypothesis ROOM : lo + RT_STACK + 304 <= P.
Hypothesis FRB : (length fr + 1 < FRAMES_MAX)%nat.
Hypothesis LIVE : In (E, 55768) live0. Hypothesis LIV1 : In (A1, ARR1_SIZE) live0. Hypothesis LIV2 : In (A2, ARR2_SIZE) live0. Hypothesis LIVF : In (FT, 262148) live0.
Hypothesis AE : sanchor E SHE. Hypothesis EIMG : 0x62b000 <= E.
(* [comment removed for export] *)
Hypothesis GFE : E + 55768 <= FB \/ FB + 256 <= E. Hypothesis GFA1 : A1 + ARR1_SIZE <= FB \/ FB + 256 <= A1.
Hypothesis GFA2 : A2 + ARR2_SIZE <= FB \/ FB + 256 <= A2. Hypothesis GFFT : FT + 262148 <= FB \/ FB + 256 <= FT.
Hypothesis GLSE : E + 55768 <= SHF \/ SHF + 32 <= E. Hypothesis GLSA1 : A1 + ARR1_SIZE <= SHF \/ SHF + 32 <= A1.
Hypothesis GLSA2 : A2 + ARR2_SIZE <= SHF \/ SHF + 32 <= A2. Hypothesis GLSFT : FT + 262148 <= SHF \/ SHF + 32 <= FT.
Hypothesis GSELF : FB + 256 <= SHF \/ SHF + 32 <= FB.
Hypothesis FSEG : 0x62b000 <= FB. Hypothesis FHI : FB + 256 <= 0x7fff7000 \/ 0x10007fff8000 <= FB.
Hypothesis OFFE : E + 55768 <= 0x7fff7000 \/ 0x10007fff8000 <= E. Hypothesis OFF1 : A1 + ARR1_SIZE <= 0x7fff7000 \/ 0x10007fff8000 <= A1.
Hypothesis OFF2 : A2 + ARR2_SIZE <= 0x7fff7000 \/ 0x10007fff8000 <= A2.
Hypothesis SHR0 : 2147450880 <= SHF. Hypothesis SHR1 : SHF + 32 <= 17594333495296.
Variable mi : mem.   (* [comment removed for export] *)
Notation PRESI := (PRESI usp fr live0 Wsm mi).
Notation SOK Σ := (sig_ok RT sp0 true 2 FB fr live0 Σ).

Lemma sm_shsep_ok_here : sm_shsep cx lo P FB SHF.
Proof. eapply sm_shsep_ok; eassumption. Qed.
Ltac shsep_open :=
  let H := fresh "SHS" in pose proof (sm_shsep_ok_here) as H; unfold sm_shsep in H;
  destruct H as (?DEA1 & ?DEA2 & ?DEFT & ?DA1A2 & ?DA1FT & ?DA2FT & ?DEFB & ?DA1FB & ?DA2FB & ?DFTFB & ?DESH & ?DA1SH & ?DA2SH & ?DFTSH & ?DFBSH & ?XL1 & ?XL2 & ?XL3 & ?XL4 & ?XL5 & ?XL6 & ?XL7 & ?XL8 & ?XL9 & ?XL10 & ?XL11 & ?XL12);
  box_ors.

(* [comment removed for export] *)
Ltac sm_keys :=
  pose proof (ck_intro P CStack) as KP; pose proof (ck_intro usp CStack) as KU; pose proof (ck_intro FB CFrame) as KFB; pose proof (ck_intro SHF CShadow) as KSH;
  pose proof (ck_intro E (CLive E 55768)) as KE; pose proof (ck_intro A1 (CLive A1 ARR1_SIZE)) as KA1; pose proof (ck_intro A2 (CLive A2 ARR2_SIZE)) as KA2;
  pose proof (ck_intro FT (CLive FT 262148)) as KFT.
Ltac fp_ours := per_interval; cbn [outside]; lia.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Notation cP := (Z_to_bv 64 P).
Notation CO := (FB + 32). Notation FV := (FB + 64).
Notation arr1 := (e_arr1 e).
Notation ITK k := (ITk e znew znew znew znew znew k).
Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
Notation ITR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s10 t3 t4 :=
  (mkR ra cP gp tp t0 t1 t2 sp cP a0 a1 a2 a3 a4 a5 a6 a7 cSB (Z_to_bv 64 (258 * nG)) s4 (Z_to_bv 64 1032) (Z_to_bv 64 1548) (Z_to_bv 64 (4 * A)) (Z_to_bv 64 257)
       (Z_to_bv 64 CO) s10 (Z_to_bv 64 (CO + 12)) t3 t4 (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 (-9))).
Notation HIT v32 v48 v56 v88 v20 v28 :=
  (sd_hi cx nG (SDW (Z_to_bv 64 FV) (Z_to_bv 64 (1032 * nG)) (Z_to_bv 64 A) (Z_to_bv 64 (E + 37708)) v32 v48 v56 (Z_to_bv 64 (E + 37708)) v88 (NOT (E + 45448)) (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 A) v20 v28)).
Notation LOWk w104 := (sd_loA cx FB SHF SHE (Z_to_bv 64 (FB + 88)) (Z_to_bv 64 (flag6 nG)) w104).
Ltac dj H := let D := fresh "D" in pose proof H as D; unfold id in D |- *; clear - D; lia.
Ltac openST :=
  let H := fresh "ST0" in pose proof (proj1 SFB) as H; unfold smB_static in H;
  destruct H as (?HA & ?HNG & ?HM & ?HNI & ?ZB & ?MV & ?HK & ?HK2 & ?HN6).
Ltac act_open :=
  shsep_open; sm_keys;
  pose proof G as [_ _ _ _ GLOW GLOR GPUS GSPT GSPA GFR GSH GSP0 _ _]; unfold USTACK_TOP, RT_STACK, STACK_WIN, SEGTOP_A in GLOW, GLOR, GSPT, GFR, GSH, GSP0;
  pose proof (ag_ax G) as AX; pose proof alloc_ceiling_range as ACR;
  assert (CEP : CEIL <= P) by (unfold CEIL; rewrite ACE; unfold STACK_WIN; clear - GLOW GLOR; lia);
  assert (FBH : FB + 160 <= CEIL) by (unfold CEIL; rewrite ACE; unfold STACK_WIN; clear - GFR; lia).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation Wits := [(E + 1704, E + 19706); (E + 37708, E + 39256); (E + 45448, E + 51640); (E + 51640, E + 55768); (P + 32, P + 136); (P + 136, P + 1264); (P + 1384, P + 1568);
                  (FV, FV + 24); (CO, CO + 12)].

Lemma sm_l2_iters : forall (n k : nat) (Σ0 Σ1 : rts RT) (m0 m : mem) (Jsp jc : list byte) (v32 v88 : word)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 : word) F fc T c,
  (k + n = 4)%nat -> (1 <= n)%nat -> SOK Σ1 -> rt_live RT Σ1 = rt_live RT Σ0 -> rt_frames RT Σ1 = rt_frames RT Σ0 -> Z.of_nat n * nG <= rt_credit RT Σ1 ->
  length Jsp = 1128%nat -> length jc = 12%nat ->
  u8arr b0segs m A1 (zb8 arr1 ARR1_SIZE) ->
  u8arr b0segs m (E + 37708) (ovb (it_len (ITK k)) (jseg J 37708 1548) 1548) ->
  u32arr b0segs m (E + 51640) (ovw (it_lpk e (ITK k)) (jseg J 51640 4128) 1032) ->
  u32arr b0segs m (E + 45448) (ovw (g_rfreq (Gend e (ITK k))) (jseg J 45448 6192) 1548) ->
  u8arr b0segs m (E + 1704) (ovb (g_sel (Gend e (ITK k))) (jseg J 1704 18002) 18002) ->
  rw_cells b0segs m (E + 640) (EHEAD2 cx g e) ->
  rw_cells b0segs m (P + 32) (LOWk (Z_to_bv 64 (Z.of_nat k + 1))) ->
  u8arr b0segs m (P + 136) Jsp ->
  rw_cells b0segs m (P + 1264) (sm_set cx FV) ->
  rw_cells b0segs m (P + 1384) (HIT v32 (Z_to_bv 64 (g_totc (Gend e (ITK k)))) (Z_to_bv 64 nMTF) v88 (Z_to_bv 64 (g_nSel (Gend e (ITK k)))) (Z_to_bv 64 (E + 37708))) ->
  u32arr b0segs m FV (zw32 (g_fave (Gend e (ITK k))) 6) -> u8arr b0segs m CO jc ->
  rw_cells b0segs m SHF sm_shadow ->
  ART RT Σ1 m -> KMem.mem_inv bsegs m -> stk bsegs m lo P -> PRESI m ->
  rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) P Wits m0 m ->
  ASTA RT Σ1 PMc (eq (MS (ITR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1548)) (Z_to_bv 64 0) t3 t4)
                         F (Z_to_bv 64 0x9399c) fc None m (seg_rom b0segs))) c ->
  (forall c' (Σ' : rts RT) (m' : mem) (Jsp' jc' : list byte) (fv : zarr) (v32' v48' v56' v88' : word)
          (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s10' t3' t4' : word) F' fc',
     ASTA RT Σ' PMc (eq (MS (ITR (Z_to_bv 64 A) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s10' t3' t4')
                            F' (Z_to_bv 64 0x939fc) fc' None m' (seg_rom b0segs))) c' ->
     SOK Σ' -> rt_live RT Σ' = rt_live RT Σ0 -> rt_frames RT Σ' = rt_frames RT Σ0 -> rt_credit RT Σ' = rt_credit RT Σ1 - Z.of_nat n * nG ->
     length Jsp' = 1128%nat -> length jc' = 12%nat ->
     u8arr b0segs m' A1 (zb8 arr1 ARR1_SIZE) ->
     u8arr b0segs m' (E + 37708) (ovb (it_len (ITK 4)) (jseg J 37708 1548) 1548) ->
     u32arr b0segs m' (E + 51640) (ovw (it_lp (ITK 4)) (jseg J 51640 4128) 1032) ->
     u32arr b0segs m' (E + 45448) (ovw (it_rfreq (ITK 4)) (jseg J 45448 6192) 1548) ->
     u8arr b0segs m' (E + 1704) (ovb (it_sel (ITK 4)) (jseg J 1704 18002) 18002) ->
     rw_cells b0segs m' (E + 640) (EHEAD2 cx g e) ->
     rw_cells b0segs m' (P + 32) (LOWk (Z_to_bv 64 4)) ->
     u8arr b0segs m' (P + 136) Jsp' ->
     rw_cells b0segs m' (P + 1264) (sm_set cx FV) ->
     rw_cells b0segs m' (P + 1384) (HIT v32' v48' v56' v88' (Z_to_bv 64 (it_nSel (ITK 4))) (Z_to_bv 64 (E + 37708))) ->
     u32arr b0segs m' FV (zw32 fv 6) -> u8arr b0segs m' CO jc' ->
     rw_cells b0segs m' SHF sm_shadow ->
     ART RT Σ' m' -> KMem.mem_inv bsegs m' -> stk bsegs m' lo P -> PRESI m' ->
     rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) P Wits m0 m' ->
     realizes bsegs c' T) ->
  realizes bsegs c T.
Proof.
  induction n as [|n IH]. { intros; lia. }
  intros k Σ0 Σ1 m0 m Jsp jc v32 v88 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 F fc T c Hkn Hn SK LVE0 FRE0 CRED LJsp Ljc
    AR1 LEN LPK RFQ SEL EH2 LOW SPL SETc HI FAVE COST SHD ART0 MI0 ST0 PR0 ACC Hc Hk.
  act_open. openST. pose proof SK as (FRM & SP0E & LIVS). pose proof (LIVS _ LIVE) as LVE.
  assert (Hk4 : (k < 4)%nat) by (clear - Hkn Hn; lia).
  destruct (proj2 SFB k Hk4) as (BL & BP & BG & BM).
  remember (ITK k) as s eqn:Es.
  rewrite <- LVE0, <- FRE0 in ACC.
  (* [comment removed for export] *)
  pose proof (proj1 BG (Z.to_nat (KSEL e)) ltac:(clear - HK; lia)) as GFE'. cbv zeta in GFE'. change (Gj e s (Z.to_nat (KSEL e))) with (Gend e s) in GFE'.
  destruct GFE' as (Egs & EnS & Htc & RFF & FVB & SLF).
  assert (EgsN : g_gs (Gend e s) = nMTF) by (rewrite Egs; apply Z.min_r; clear - HK HK2; lia).
  (* [comment removed for export] *)
  pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'. destruct CX' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ME16 & _).
  set (qE := E / 4). assert (E4 : E = 4 * qE) by (subst qE; clear - ME16; Z.div_mod_to_equations; lia). clearbody qE.
  pose proof (sm_mkl_cps RT AF HBM PMc FDO MST lo P usp sp0 FB SHF fr live0 Wsm mi G ACE FRLO ROOM FRB cx qE (jseg J 37708 1548) (jseg J 45448 6192) A nG (g_rfreq (Gend e s)) (ml_len e s) gp tp
                CX LIVE E4 TP ltac:(clear - HA; lia) ltac:(clear - HNG; lia)) as ML.
  specialize (ML ltac:(intros x Hx; cbn [outside]; clear - Hx; lia)).
  specialize (ML ltac:(intros tt v Htt Hv; destruct (RFF tt v Htt Hv) as [D R]; rewrite EgsN in R; split; [exact D| bz_params; clear - R HM BZbsH__; lia])).
  specialize (ML ltac:(intros t' Ht'; destruct (proj1 BM t' Ht') as (X1 & X2 & _); split; [exact X1|];
                        rewrite (hbMakeCodeLengths_pt _ _ _ _ _ znew znew eq_refl eq_refl) in X2; exact X2)).
  specialize (ML (Z.to_nat nG) 0%nat Σ1 Σ1 m m).
  change (258 * Z.of_nat 0 - 1548) with (-1548) in ML. change (1032 * Z.of_nat 0) with 0 in ML.
  refine (cps_realizes bsegs _ _ T c (ML _ _ _ _ _ _ _ _ _ _ _ _ sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc ltac:(clear - HNG; lia) ltac:(clear - HNG; lia) SK eq_refl eq_refl
            ltac:(rewrite Z2Nat.id by (clear - HNG; lia); clear - CRED HNG; nia) ART0 MI0 ST0 PR0 LEN RFQ HI (pfp_refl _ _ _ _ m)) Hc _).
  clear ML Hc LEN RFQ HI.
  intros c6 (Σ6 & m6 & x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & F6 & fc6 & Hc6 & SK6 & LV6 & FR6 & CR6 & ART6 & MI6 & ST6 & PR6 & LEN & RFQ & HI & ACCm).
  xfer_rtf G SK ACCm m m6.
  pose proof (pfp_trans _ _ _ _ m0 m m6 ACC (pfp_weaken _ _ _ _ Wits m m6 ACCm ltac:(per_interval; cbn [KFrame.outside]; lia))) as ACC6. clear ACC ACCm.
  rewrite Z2Nat.id in CR6 by (clear - HNG; lia).
  (* [comment removed for export] *)
  destruct (MLt e s (Z.to_nat nG)) as [[[l' h'] w'] p'] eqn:EML.
  assert (EIT : ITK (S k) = SITS l' (g_rfreq (Gend e s)) (it_lpk e s) (g_sel (Gend e s)) (g_cost (Gend e s)) (g_fave (Gend e s)) (g_nSel (Gend e s)) h' w' p').
  { rewrite ITk_S, <- Es, (proj2 BM), EML. reflexivity. }
  unfold ml_len in LEN. replace (0 + Z.to_nat nG)%nat with (Z.to_nat nG) in LEN by (clear; lia). rewrite EML in LEN. cbn [fst] in LEN.
  assert (EL : it_len (ITK (S k)) = l') by (rewrite EIT; reflexivity).
  assert (ELP : it_lp (ITK (S k)) = it_lpk e s) by (rewrite EIT; reflexivity).
  assert (ERF : it_rfreq (ITK (S k)) = g_rfreq (Gend e s)) by (rewrite EIT; reflexivity).
  assert (ESL : it_sel (ITK (S k)) = g_sel (Gend e s)) by (rewrite EIT; reflexivity).
  assert (ENS : it_nSel (ITK (S k)) = g_nSel (Gend e s)) by (rewrite EIT; reflexivity).
  rewrite <- EL in LEN. rewrite <- ELP in LPK. rewrite <- ERF in RFQ. rewrite <- ESL in SEL. clear EIT EML EL ELP ERF ESL.
  rewrite LVE0 in LV6, ACC6. rewrite FRE0 in FR6, ACC6.
  destruct (Nat.eqb_spec (k + 1) 4) as [E4'|N4].
  - (* [comment removed for export] *)
    assert (n = 0)%nat by (clear - Hkn E4'; lia). subst n. assert (k = 3)%nat by (clear - E4'; lia). subst k.
    rewrite <- ENS in HI.
    eapply (Hk c6 Σ6 m6 Jsp jc (g_fave (Gend e s))); [exact Hc6| exact SK6| exact LV6| exact FR6| rewrite CR6; clear; lia| exact LJsp| exact Ljc
      | exact AR1| exact LEN| exact LPK| exact RFQ| exact SEL| exact EH2| exact LOW| exact SPL| exact SETc| exact HI| exact FAVE| exact COST| exact SHD
      | exact ART6| exact MI6| exact ST6| exact PR6| exact ACC6].
  - (* [comment removed for export] *)
    assert (OP : forall a b, P <= a -> b <= SH_LO \/ SH_HI <= a) by (intros a b Ha; right; unfold SH_HI; clear - Ha XL7; lia).
    assert (OE : forall a b, E <= a -> b <= E + 55768 -> b <= SH_LO \/ SH_HI <= a) by (intros a b Ha Hb; pose proof OFFE as D; unfold id in D; unfold SH_LO, SH_HI; clear - D Ha Hb; lia).
    assert (OF : forall a b, FB <= a -> b <= FB + 256 -> b <= SH_LO \/ SH_HI <= a) by (intros a b Ha Hb; pose proof FHI as D; unfold id in D; unfold SH_LO, SH_HI; clear - D Ha Hb; lia).
    assert (SHe : shzW b0segs (Wit cx P FB) m6 E (E + ESTATE_SIZE)).
    { apply (sm_shE RT AF cx lo sp CX P FB SHF fr live0 sp0 G LIVE Σ6 m6 _ SK6 ART6). intros x Hx X47. unfold Wit. cbn [disjoint_from].
      repeat (split; [apply shd_app; [exact X47| first [apply OE; clear; lia| apply OP; clear; lia| apply OF; clear; lia]]|]). exact I. }
    assert (SHa : shzW b0segs (Wit cx P FB) m6 A1 (A1 + ARR1_SIZE)).
    { apply (sm_shA1 RT AF cx lo sp CX P FB SHF fr live0 sp0 G LIV1 Σ6 m6 _ SK6 ART6). intros x Hx X47. unfold Wit. cbn [disjoint_from].
      repeat (split; [apply shd_app; [exact X47| first [apply OE; clear; lia| apply OP; clear; lia| apply OF; clear; lia]]|]). exact I. }
    replace (Z.of_nat k + 1) with (Z.of_nat (S k)) in LOW by (clear; lia).
    eapply (l1_realizes RT AF Σ6 PMc _ T c6 MST Hc6).
    eapply (B0_sm_segC cx e g _ gp tp sp F6 fc6 znew znew znew znew znew P SHE FB SHF CX SEP GM CEP XL11 ltac:(clear - GFR; lia) FBH
              ltac:(unfold SH_LO; exact SHR0) ltac:(unfold SH_HI; clear - SHR1; lia) AE AX
              ltac:(dj DEFB) ltac:(dj DA1FB) ltac:(dj DESH) ltac:(dj DFBSH) ltac:(unfold id; left; clear - XL6; lia)
              ltac:(pose proof OFFE as D; unfold id in D |- *; unfold SH_LO, SH_HI; clear - D; lia) ltac:(pose proof FHI as D; unfold id in D |- *; unfold SH_LO, SH_HI; clear - D; lia)
              ltac:(unfold SH_HI; clear - XL7; lia) SFB (S k) Jsp jc (g_fave (Gend e s)) _ _ _ _ _ m6 m6);
      [clear - Hkn N4; lia| exact LJsp| exact Ljc| exact AR1| exact LEN| exact LPK| exact RFQ| exact SEL| exact EH2| exact LOW| exact SPL| exact SETc| exact HI| exact FAVE| exact COST| exact SHD
      | exact (kmem_inv_N _ _ MI6)| apply munch_refl| apply wmono_refl| exact SHa| exact SHe|].
    clear AR1 LEN LPK RFQ SEL EH2 LOW SPL SETc HI FAVE COST SHD SHa SHe Hc6.
    intros m7 Jsp' jc' v32' v88' ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4'. cbv zeta.
    intros LJsp' Ljc' AR1 LEN LPK RFQ SEL EH2 LOW SPL SETc HI FAVE COST SHD NMI7 MU7 WM7. apply evt_done. intros c7 Hc7.
    unfold Wit in MU7.
    lazymatch type of MU7 with munch ?W _ _ => destruct (after_l1 AF G Σ6 W m6 m7 SK6 ART6 MI6 ST6 PR6 NMI7 MU7 WM7 ltac:(fp_ours)) as (ART7 & MI7 & ST7 & PR7 & STEP7) end.
    rewrite LV6, FR6 in STEP7.
    pose proof (pfp_trans _ _ _ _ m0 m6 m7 ACC6 (pfp_weaken _ _ _ _ Wits m6 m7 STEP7 ltac:(per_interval; cbn [KFrame.outside]; lia))) as ACC7. clear ACC6 STEP7.
    eapply (IH (S k) Σ0 Σ6 m0 m7 Jsp' jc' v32' v88' _ _ _ _ _ _ _ _ _ _ _ _ _ _ F6 fc6 T c7 ltac:(clear - Hkn; lia) ltac:(clear - Hkn N4; lia) SK6 LV6 FR6
              ltac:(rewrite CR6; clear - CRED HNG; nia) LJsp' Ljc' AR1 LEN LPK RFQ SEL EH2 LOW SPL SETc HI FAVE COST SHD ART7 MI7 ST7 PR7 ACC7 Hc7).
    intros c8 Σ8 m8 Jsp8 jc8 fv8 p32 p48 p56 p88 q0 q1 q2 g0 g1 g2 g3 g4 g5 g6 g7 qs4 qs10 q3 q4 F8 fc8 Hc8 SK8 LV8 FR8 CR8.
    eapply (Hk c8 Σ8 m8 Jsp8 jc8 fv8 p32 p48 p56 p88); [exact Hc8| exact SK8| exact LV8| exact FR8| rewrite CR8, CR6; clear; nia].
Qed.

End SMG.

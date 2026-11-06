(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout RT_iface D_defs D_kit I_read.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require Import L2Kit L2Act L2Stmt A0_fs_L2f A0_sm_mkl A0_sm_L2a.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzArr BzCMem BzCStream BzCState BzCMtf BzCHuff BzArrD CmpMem CmpCut CmpCutSM CmpCutSmA BzCFactsSmA CmpCutSmB BzCFactsGm BzCSmF1 BzCFactsSmB BzCFactsSd CmpHmKit CmpSmKit CmpSmKit2 AsanKit AsanKit2 AsanCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmas1 BzCHuffF1.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_smV A0_cmp_fsP A0_cmp_smA A0_cmp_smBz A0_cmp_smBb A0_cmp_smK A0_cmp_sdV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).

Section SMG.
Context {BZP : BzParams} {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MSET : memset_icontract RT e_asan_memset.
Hypothesis HBM : hbMakeCodeLengths_contract RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
(* [comment removed for export] *)
Variables (cx : cctx) (g : eg) (e : est) (lo : Z) (sp gp tp : word).
Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis IMG : cctx_img (aci_c A0C) cx.
Hypothesis GM : g_mtf g = true. Hypothesis GB : g_bs g = true. Hypothesis GZ : g_zbits g = Z_to_bv 64 (c_A2 cx + e_nblock e).
Hypothesis SFA : smA_facts e. Hypothesis SFB : smB_facts e znew znew znew znew znew.
Hypothesis TP : tp = Z_to_bv 64 0x5fc0d8.
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
Hypothesis FRLO : P + 1600 <= usp. Hypothesis FRHI : usp <= P + 1616.
Hypothesis ROOM : lo + RT_STACK + 240 <= P.
Hypothesis FRB : (length fr + 1 < FRAMES_MAX)%nat.
Hypothesis LIVE : In (E, 55768) live0. Hypothesis LIV1 : In (A1, ARR1_SIZE) live0. Hypothesis LIV2 : In (A2, ARR2_SIZE) live0. Hypothesis LIVF : In (FT, 262148) live0.
Hypothesis AE : sanchor E SHE. Hypothesis EIMG : 0x61e000 <= E.
(* [comment removed for export] *)
Hypothesis GFE : E + 55768 <= FB \/ FB + 256 <= E. Hypothesis GFA1 : A1 + ARR1_SIZE <= FB \/ FB + 256 <= A1.
Hypothesis GFA2 : A2 + ARR2_SIZE <= FB \/ FB + 256 <= A2. Hypothesis GFFT : FT + 262148 <= FB \/ FB + 256 <= FT.
Hypothesis GLSE : E + 55768 <= SHF \/ SHF + 32 <= E. Hypothesis GLSA1 : A1 + ARR1_SIZE <= SHF \/ SHF + 32 <= A1.
Hypothesis GLSA2 : A2 + ARR2_SIZE <= SHF \/ SHF + 32 <= A2. Hypothesis GLSFT : FT + 262148 <= SHF \/ SHF + 32 <= FT.
Hypothesis GSELF : FB + 256 <= SHF \/ SHF + 32 <= FB.
Hypothesis FSEG : 0x61e000 <= FB. Hypothesis FHI : FB + 256 <= 0x7fff7000 \/ 0x10007fff8000 <= FB.
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
(* [comment removed for export] *)

Notation cP := (Z_to_bv 64 P).
Notation CO := (FB + 32). Notation FV := (FB + 64).
Notation arr1 := (e_arr1 e).
Notation ITK k := (ITk e znew znew znew znew znew k).
(* [comment removed for export] *)
Notation IZ ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s11 t3 t4 t5 t6 :=
  (mkR ra cP gp tp t0 t1 t2 sp cP a0 a1 a2 a3 a4 a5 a6 a7
       s2 s3 cSB s5 s6 (Z_to_bv 64 A) (Z_to_bv 64 A1) (Z_to_bv 64 (SHE + 83)) (Z_to_bv 64 nG) s11 t3 t4 t5 t6).
(* [comment removed for export] *)
Notation GA ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 t3 t4 t5 t6 :=
  (mkR ra cP gp tp t0 t1 t2 sp cP a0 a1 a2 a3 a4 a5 a6 a7
       s2 (Z_to_bv 64 (E + 37708)) cSB s5 s6 (Z_to_bv 64 A) (Z_to_bv 64 A1) (Z_to_bv 64 (SHE + 83)) (Z_to_bv 64 nG) (Z_to_bv 64 (E + 668)) t3 t4 t5 t6).

Ltac dj H := let D := fresh "D" in pose proof H as D; unfold id in D |- *; clear - D; lia.
(* [comment removed for export] *)
Ltac vwW H := apply frdW_intro; [exact H| x_disj].
Ltac openST :=
  let H := fresh "ST0" in pose proof (proj1 SFB) as H; unfold smB_static in H;
  destruct H as (?HA & ?HNG & ?HM & ?HNI & ?ZB & ?MV & ?HK & ?HK2 & ?HN6).
Ltac act_open :=
  shsep_open; sm_keys;
  pose proof G as [_ _ _ _ GLOW GLOR GPUS GSPT GSPA GFR GSH GSP0 _ _]; unfold USTACK_TOP, RT_STACK, STACK_WIN, SEGTOP_A in GLOW, GLOR, GSPT, GFR, GSH, GSP0;
  pose proof (ag_ax G) as AX; pose proof alloc_ceiling_range as ACR;
  assert (CEP : CEIL <= P) by (unfold CEIL; rewrite ACE; unfold STACK_WIN; clear - GLOW GLOR; lia).

Lemma sm_rfreq_zero_S : forall n rf alphaSize t, sm_rfreq_zero (S n) rf alphaSize t = sm_rfreq_zero n (zfill0 (Z.to_nat alphaSize) rf (258 * t)) alphaSize (t + 1).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sm_shE' : forall Σ (m : mem) W, SOK Σ -> ART RT Σ m ->
  (forall x, E <= x < E + 55768 -> 0 <= x < 2^47 -> disjoint_from W (x / 8 + 2147450880) 1) -> shzW a0segs W m E (E + 55768).
Proof. intros. eapply sm_shE; eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation Wrf := [(E + 45448, E + 51640); (E + 51640, E + 55768); (P + 1424, P + 1440)].
Notation HIX w1360 w1424 w1432 :=
  [C8 (Z_to_bv 64 (E + 37708)); C8 (Z_to_bv 64 999999999); C8 w1360; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 CO); C8 (Z_to_bv 64 FV);
   C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (E + 45448)); C8 (Z_to_bv 64 (E + 45448 + 1032 * nG)); C8 (Z_to_bv 64 A); C8 w1424; C8 w1432].

Lemma sm_rfrows : forall (n : nat) (t : Z) (rf lp len : zarr) (Σ1 : rts RT) (m0 m : mem) (v16 v24 w1360 w1424 w1432 : word)
    (t0 t1 t2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word) F fc T c,
  t + Z.of_nat n = nG -> 0 <= t -> (1 <= n)%nat -> SOK Σ1 ->
  (forall t v, 0 <= t < 6 -> 0 <= v < A -> zdef len (258 * t + v) = true /\ 0 <= zget len (258 * t + v) <= 17) ->
  u32arr a0segs m (E + 45448) (ovw rf (jseg J 45448 6192) 1548) ->
  u8arr a0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
  u32arr a0segs m (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
  rw_cells a0segs m (P + 1344) (HIX w1360 w1424 w1432) ->
  rw_cells a0segs m (P + 16) (sm_loA cx e FB SHF SHE v16 v24) -> rw_cells a0segs m (P + 160) (sm_loB cx e SHE) ->
  rw_cells a0segs m (E + 640) (EHEAD2 cx g e) ->
  ART RT Σ1 m -> KMem.mem_inv asegs m -> stk asegs m lo P -> PRESI m ->
  rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) P Wrf m0 m -> wmono asegs m0 m ->
  ASTA RT Σ1 PMc (eq (MS (IZ (Z_to_bv 64 0x8a9fc) t0 t1 t2 (Z_to_bv 64 (E + 45448 + 1032 * t)) (Z_to_bv 64 0) (Z_to_bv 64 (4 * A)) a3 a4 a5 a6 a7
                              (Z_to_bv 64 (E + 45448 + 1032 * t)) (Z_to_bv 64 (nG - t)) (Z_to_bv 64 (4 * A)) (Z_to_bv 64 (E + 668)) s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x52ea0) fc None m (seg_rom a0segs))) c ->
  (forall c' (m' : mem) (u0 u1 e3 e4 e5 e6 e7 u3 u4 u5 u6 : word) F' fc',
     ASTA RT Σ1 PMc (eq (MS (IZ (Z_to_bv 64 0x8ac34) u0 u1 (Z_to_bv 64 CO) (Z_to_bv 64 CO) (Z_to_bv 64 0) (Z_to_bv 64 12) e3 e4 e5 e6 e7
                                 (Z_to_bv 64 nMTF) (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 0) (Z_to_bv 64 49) (Z_to_bv 64 (E + 668)) u3 u4 u5 u6)
                            F' (Z_to_bv 64 0x52ea0) fc' None m' (seg_rom a0segs))) c' ->
     u32arr a0segs m' (E + 45448) (ovw (sm_rfreq_zero n rf A t) (jseg J 45448 6192) 1548) ->
     u8arr a0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
     u32arr a0segs m' (E + 51640) (ovw (if nG =? 6 then sm_lenpack (Z.to_nat A) lp len 0 else lp) (jseg J 51640 4128) 1032) ->
     rw_cells a0segs m' (P + 1344) (sm_hi cx e CO FV w1360 0 0) ->
     rw_cells a0segs m' (P + 16) (sm_loA cx e FB SHF SHE v16 v24) -> rw_cells a0segs m' (P + 160) (sm_loB cx e SHE) ->
     rw_cells a0segs m' (E + 640) (EHEAD2 cx g e) ->
     ART RT Σ1 m' -> KMem.mem_inv asegs m' -> stk asegs m' lo P -> PRESI m' ->
     rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) P Wrf m0 m' -> wmono asegs m0 m' ->
     realizes asegs c' T) ->
  realizes asegs c T.
Proof.
  induction n as [|n IH]. { intros; lia. }
  intros t rf lp len Σ1 m0 m v16 v24 w1360 w1424 w1432 t0 t1 t2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 F fc T c Ht Ht0 Hn SK LF RFQ LEN LPK HI LOA LOB EH2 ART0 MI0 ST0 PR0 ACC WMA Hc Hk.
  act_open. openST. pose proof SK as (FRM & SP0E & LIVS). pose proof (LIVS _ LIVE) as LVE.
  pose proof (af_live_range RT AF Σ1 m E 55768 ART0 LVE) as (EL0 & EL1 & _). rewrite SP0E in EL1. unfold STACK_WIN in EL1.
  (* [comment removed for export] *)
  destruct (rfrow_before_memset a0segs m (E + 45448) rf (jseg J 45448 6192) 1548 t A RFQ Ht0 ltac:(clear - HA; lia) ltac:(clear - Ht Hn HA HNG; lia)) as (R0 & R1 & R2). clear RFQ R1.
  eapply (memset_call G PMc FDO MST Σ1 (E + 45448 + 1032 * t) (4 * A) z8 m); [exact MSET| exact SK| clear - EL0 EL1 Ht Ht0 HNG GSP0; lia| clear - HA; lia| | exact ART0| exact MI0| exact ST0| exact Hc|].
  { apply (cdst_live AF G Σ1 m E 55768 (E + 45448 + 1032 * t) (4 * A) ART0 LVE); [clear - Ht0; lia| clear - Ht Ht0 Hn HA HNG; lia| clear - HA; lia]. }
  clear Hc. intros c1 m1 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F1 fc1 Hc1 ART1 MI1 ST1 WM1 BY1 STEP1.
  pose proof (pres_step G Σ1 _ m m1 SK PR0 STEP1 ltac:(per_interval; right; cbn [outside]; lia)) as PR1.
  xfer_rt G SK STEP1 WM1 m m1.
  rewrite (KMState.ret_pc_even 0x8a9fc ltac:(lia) eq_refl) in Hc1.
  assert (RFQ1 : u32arr a0segs m1 (E + 45448) (ovw (zfill0 (Z.to_nat A) rf (258 * t)) (jseg J 45448 6192) 1548)).
  { destruct (af_acc_live RT AF Σ1 m1 E 55768 ART1 LVE) as [WRE _].
    pose proof (n_rw_CB_of_bytes m1 (E + 45448 + 1032 * t) (repeat z8 (Z.to_nat (4 * A))) BY1
                  ltac:(rewrite repeat_length; apply (wr_at_sub asegs m1 E 55768 _ _ WRE); clear - Ht Ht0 Hn HA HNG; lia)) as ROW.
    rewrite repeat_length in ROW.
    apply (rfrow_after_memset a0segs m1 (E + 45448) rf (jseg J 45448 6192) 1548 t A R0 ROW R2); [exact Ht0| clear - HA; lia| clear - Ht Hn HA HNG; lia]. }
  clear R0 R2 BY1.
  assert (ACC1 : rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) P Wrf m0 m1).
  { apply (pfp_trans _ _ _ _ m0 m m1 ACC). apply (pfp_weaken _ _ _ _ Wrf m m1 STEP1). per_interval; cbn [KFrame.outside]; lia. }
  assert (WMA1 : wmono asegs m0 m1) by (eapply wmono_trans; [exact WMA| exact WM1]).
  clear STEP1 WM1 ACC WMA.
  (* [comment removed for export] *)
  assert (SHe : shzW a0segs [(E + 51640, E + 55768); (P + 1424, P + 1440)] m1 E (E + 55768)).
  { apply (sm_shE' Σ1 m1 _ SK ART1). intros x Hx X47. cbn [disjoint_from].
    split; [apply shd_app; [exact X47| pose proof OFFE as D; unfold id in D; unfold SH_LO, SH_HI; clear - D; lia]|].
    split; [apply shd_app; [exact X47| right; unfold SH_HI; clear - XL7; lia]| exact I]. }
  eapply (l1_realizes RT AF Σ1 PMc _ T c1 MST Hc1).
  eapply (A0_sm_it2 cx e g _ gp tp sp F1 fc1 P SHE CO FV FB SHF v16 v24 CX GM CEP XL11 AE HA HNG HM t lp len w1360 w1424 w1432 m1 m1);
    [clear - Ht Ht0 Hn; lia| exact LF| exact LEN| exact LPK| exact HI| exact (kmem_inv_N _ _ MI1)| apply munch_refl| apply wmono_refl| vwW LOA| vwW LOB| vwW EH2| exact SHe| |].
  - (* [comment removed for export] *)
    intros NX. apply evt_done. clear Hc1. intros c2 Hc2.
    destruct n as [|n']; [exfalso; clear - Ht NX; lia|].
    rewrite sm_rfreq_zero_S in Hk.
    eapply (IH (t + 1) _ lp len Σ1 m0 m1 v16 v24 w1360 w1424 w1432 _ _ _ _ _ _ _ _ s11 _ _ _ _ F1 fc1 T c2 ltac:(clear - Ht; lia) ltac:(clear - Ht0; lia) ltac:(clear; lia) SK LF
              RFQ1 LEN LPK HI LOA LOB EH2 ART1 MI1 ST1 PR1 ACC1 WMA1 Hc2 Hk).
  - (* [comment removed for export] *)
    intros LAST m2 q0 q1 q3 q4 q5 q6 q7 x3 x4 x5 x6 LEN2 LPK2 HI2 NMI2 MU2 WM2. apply evt_done. clear Hc1. intros c2 Hc2.
    assert (n = 0)%nat by (clear - Ht LAST; lia). subst n. cbn [sm_rfreq_zero] in Hk.
    lazymatch type of MU2 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m1 m2 SK ART1 MI1 ST1 PR1 NMI2 MU2 WM2 ltac:(fp_ours)) as (ART2 & MI2 & ST2 & PR2 & STEP2) end.
    clear LEN LPK HI. xfer_l1 m1 m2 MU2 WM2.
    eapply (Hk c2 m2); [exact Hc2| exact RFQ1| exact LEN2| exact LPK2| exact HI2| exact LOA| exact LOB| exact EH2| exact ART2| exact MI2| exact ST2| exact PR2| |].
    + apply (pfp_trans _ _ _ _ m0 m1 m2 ACC1). apply (pfp_weaken _ _ _ _ Wrf m1 m2 STEP2). per_interval; cbn [KFrame.outside]; lia.
    + eapply wmono_trans; [exact WMA1| exact WM2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sm_acc_cost : forall (m : mem), 0 <= FB -> rw_cells a0segs m (SHF + 4) [C1 z8; C1 (Z_to_bv 8 4)] -> acc asegs m CO 12.
Proof.
  intros m HF SHC. pose proof (ag_ax G) as [AX1 AX2]. destruct (n_rw_cells_bytes a0segs m _ _ SHC) as [BY _]. cbn [cells_bytes cbytes app] in BY.
  apply (acc_ushadow asegs m CO 12); [clear - AX1; Z.div_mod_to_equations; lia| clear - HF; lia| clear; lia|].
  replace (shad CO) with (SHF + 4) by (unfold shad, SHB; rewrite AX2; clear - AX1; Z.div_mod_to_equations; lia). exact BY.
Qed.
Lemma sm_acc_fave : forall (m : mem), 0 <= FB -> rw_cells a0segs m (SHF + 8) [C1 z8; C1 z8; C1 z8] -> acc asegs m FV 24.
Proof.
  intros m HF SHV. pose proof (ag_ax G) as [AX1 AX2]. destruct (n_rw_cells_bytes a0segs m _ _ SHV) as [BY _]. cbn [cells_bytes cbytes app] in BY.
  exact (acc_of_zero_shadow asegs m FB SHF 8 3 AX1 AX2 HF ltac:(clear; lia) BY).
Qed.
Lemma fave_zero_bytes : forall (m : mem) Ab f, rw_cells a0segs m Ab [CB 24 (repeat z8 24)] -> u32arr a0segs m Ab (zw32 (zero6 f) 6).
Proof.
  intros m Ab f H.
  replace (zw32 (zero6 f) 6) with (repeat (Z_to_bv 64 0) (Z.to_nat 6)).
  - apply (u32arr_zero_init a0segs m Ab 6); [exact H| clear; lia].
  - apply nth_error_ext. intros k. destruct (Nat.lt_ge_cases k 6) as [Hk|Hk].
    + rewrite nth_error_repeat by lia. replace k with (Z.to_nat (Z.of_nat k)) by lia. rewrite zw32_nth by lia.
      unfold zero6. rewrite zfill0_get. replace ((0 <=? Z.of_nat k) && (Z.of_nat k <? 0 + Z.of_nat 6))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia). reflexivity.
    + rewrite (proj2 (nth_error_None _ _)) by (rewrite repeat_length; lia). rewrite (proj2 (nth_error_None _ _)) by (rewrite zw32_length_nat; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation Wgl := [(E + 1704, E + 19706); (E + 45448, E + 51640); (P + 232, P + 1344); (P + 1360, P + 1368); (P + 1424, P + 1440); (FV, FV + 24); (CO, CO + 12)].

Lemma sm_grploop : forall (n j : nat) (s : sits) (lp len : zarr) (Σ1 : rts RT) (m0 m : mem) (Jsp : list byte) (w1360 : word)
    (t0 t1 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc T c,
  smB_grp e s -> it_len s = len -> it_lpk e s = lp ->
  (forall t v, 0 <= t < 6 -> 0 <= v < A -> zdef len (258 * t + v) = true /\ 0 <= zget len (258 * t + v) <= 17) ->
  (nG = 6 -> forall v j, 0 <= v < A -> 0 <= j < 3 -> zdef lp (4 * v + j) = true /\ 0 <= zget lp (4 * v + j) < 2097152) ->
  Z.of_nat j + Z.of_nat n = KSEL e -> (1 <= n)%nat -> SOK Σ1 -> length Jsp = 1112%nat ->
  u8arr a0segs m A1 (zb8 arr1 ARR1_SIZE) ->
  u8arr a0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
  u32arr a0segs m (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
  u32arr a0segs m (E + 45448) (ovw (g_rfreq (Gj e s j)) (jseg J 45448 6192) 1548) ->
  u8arr a0segs m (E + 1704) (ovb (g_sel (Gj e s j)) (jseg J 1704 18002) 18002) ->
  u8arr a0segs m (P + 232) Jsp ->
  rw_cells a0segs m (P + 1344) (sm_hi cx e CO FV w1360 (g_totc (Gj e s j)) (g_gs (Gj e s j))) ->
  u32arr a0segs m FV (zw32 (g_fave (Gj e s j)) 6) ->
  rw_cells a0segs m (P + 160) (sm_loB cx e SHE) -> rw_cells a0segs m (E + 640) (EHEAD2 cx g e) ->
  rw_cells a0segs m (SHF + 4) [C1 z8; C1 (Z_to_bv 8 4)] -> rw_cells a0segs m (SHF + 8) [C1 z8; C1 z8; C1 z8] -> wr_at asegs m CO 12 ->
  ART RT Σ1 m -> KMem.mem_inv asegs m -> stk asegs m lo P -> PRESI m ->
  rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) P Wgl m0 m -> wmono asegs m0 m ->
  ASTA RT Σ1 PMc (eq (MS (GA (Z_to_bv 64 0x8ac34) t0 t1 (Z_to_bv 64 CO) (Z_to_bv 64 CO) (Z_to_bv 64 0) (Z_to_bv 64 12) a3 a4 a5 a6 a7
                              (Z_to_bv 64 nMTF) (Z_to_bv 64 (g_nSel (Gj e s j))) (Z_to_bv 64 (g_gs (Gj e s j) + 49)) t3 t4 t5 t6)
                         F (Z_to_bv 64 0x52ea0) fc None m (seg_rom a0segs))) c ->
  (forall c' (m' : mem) (Jsp' : list byte) (w1360' : word) (totc' gs' : Z) (ra' u0 u1 u2 e0 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 : word) F' fc',
     ASTA RT Σ1 PMc (eq (MS (GA ra' u0 u1 u2 e0 e1 e2 e3 e4 e5 e6 e7 (Z_to_bv 64 nMTF) (Z_to_bv 64 (g_nSel (Gend e s))) (Z_to_bv 64 (E + 668)) u3 u4 u5 u6)
                            F' (Z_to_bv 64 0x8f16c) fc' None m' (seg_rom a0segs))) c' ->
     length Jsp' = 1112%nat ->
     u8arr a0segs m' A1 (zb8 arr1 ARR1_SIZE) ->
     u8arr a0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
     u32arr a0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
     u32arr a0segs m' (E + 45448) (ovw (g_rfreq (Gend e s)) (jseg J 45448 6192) 1548) ->
     u8arr a0segs m' (E + 1704) (ovb (g_sel (Gend e s)) (jseg J 1704 18002) 18002) ->
     u8arr a0segs m' (P + 232) Jsp' ->
     rw_cells a0segs m' (P + 1344) (sm_hi cx e CO FV w1360' totc' gs') ->
     rw_cells a0segs m' (P + 160) (sm_loB cx e SHE) -> rw_cells a0segs m' (E + 640) (EHEAD2 cx g e) ->
     rw_cells a0segs m' (SHF + 4) [C1 z8; C1 (Z_to_bv 8 4)] -> rw_cells a0segs m' (SHF + 8) [C1 z8; C1 z8; C1 z8] ->
     ART RT Σ1 m' -> KMem.mem_inv asegs m' -> stk asegs m' lo P -> PRESI m' ->
     rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) P Wgl m0 m' -> wmono asegs m0 m' ->
     realizes asegs c' T) ->
  realizes asegs c T.
Proof.
  induction n as [|n IH]. { intros; lia. }
  intros j s lp len Σ1 m0 m Jsp w1360 t0 t1 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc T c HGF Elen Elp LF LPF Hj Hn SK LJsp AR1 LEN LPK RFQ SEL SPL HI FAVE LOB EH2 SHC SHV WRC ART0 MI0 ST0 PR0 ACC WMA Hc Hk.
  act_open. openST. pose proof SK as (FRM & SP0E & LIVS). pose proof (LIVS _ LIVE) as LVE. pose proof (LIVS _ LIV1) as LV1.
  destruct HGF as [GF GEND].
  pose proof (GF j ltac:(clear - Hj; lia)) as Fj. cbv zeta in Fj. destruct Fj as (Egs & EnS & Htc & RFF & FVB & SLF).
  remember (Gj e s j) as gj eqn:EGJ.
  destruct gj as [rf sel cost fave nSel totc gs]. cbn [g_rfreq g_sel g_cost g_fave g_nSel g_totc g_gs] in *.
  subst nSel. assert (Egs' : gs = 50 * Z.of_nat j) by (rewrite Egs; apply Z.min_l; clear - Hj Hn HK HK2; lia).
  (* [comment removed for export] *)
  eapply (memset_call G PMc FDO MST Σ1 CO 12 z8 m); [exact MSET| exact SK| clear - GFR GSP0; lia| clear; lia| | exact ART0| exact MI0| exact ST0| exact Hc|].
  { apply (cdst_frame G Σ1 m CO 12 SK (sm_acc_cost m ltac:(clear - GFR; lia) SHC) WRC); clear; lia. }
  clear Hc. intros c1 m1 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F1 fc1 Hc1 ART1 MI1 ST1 WM1 BY1 STEP1.
  pose proof (pres_step_ours G Σ1 _ _ m m1 SK PR0 STEP1 ltac:(right; left; clear; lia)) as PR1.
  xfer_rt G SK STEP1 WM1 m m1.
  rewrite (KMState.ret_pc_even 0x8ac34 ltac:(lia) eq_refl) in Hc1.
  assert (COST : u8arr a0segs m1 CO (zb8 znew 12)).
  { pose proof (n_rw_CB_of_bytes m1 CO (repeat z8 (Z.to_nat 12)) BY1 ltac:(rewrite repeat_length; exact WRC)) as CZ. rewrite repeat_length in CZ.
    apply (zb8_init a0segs m1 CO 12 _ CZ ltac:(clear; lia)). apply repeat_zero_nth. }
  clear BY1.
  assert (ACC1 : rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) P Wgl m0 m1).
  { apply (pfp_trans _ _ _ _ m0 m m1 ACC). apply (pfp_weaken _ _ _ _ Wgl m m1 STEP1). per_interval; cbn [KFrame.outside]; lia. }
  assert (WMA1 : wmono asegs m0 m1) by (eapply wmono_trans; [exact WMA| exact WM1]).
  clear STEP1 WM1 ACC WMA.
  (* [comment removed for export] *)
  assert (AFW : app_fp Wgl).
  { cbn [app_fp]. unfold SH_LO, SH_HI. pose proof OFFE as D1. pose proof FHI as D2. unfold id in D1, D2. clear - D1 D2 XL7. repeat split; lia. }
  destruct (af_acc_live RT AF Σ1 m1 A1 ARR1_SIZE ART1 LV1) as [_ ACC1'].
  pose proof (af_live_range RT AF Σ1 m1 A1 ARR1_SIZE ART1 LV1) as (A1L0 & A1L1 & _). rewrite SP0E in A1L1. unfold STACK_WIN in A1L1.
  pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'. destruct CX' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MA16 & _).
  assert (SHa : shzW a0segs Wgl m1 A1 (A1 + ARR1_SIZE)).
  { apply (shzW_of_acc a0segs Wgl m1 A1 ARR1_SIZE A1 (A1 + ARR1_SIZE) ACC1' AFW); [clear - A1L0; lia| clear - A1L1 GSP0; lia| clear; lia|].
    bz_params. clear - MA16. Z.div_mod_to_equations. lia. }
  assert (SHe : shzW a0segs Wgl m1 E (E + 55768)).
  { apply (sm_shE' Σ1 m1 _ SK ART1). intros x Hx X47. cbn [disjoint_from].
    assert (OP : forall a b, P <= a -> b <= SH_LO \/ SH_HI <= a) by (intros a b Ha; right; unfold SH_HI; clear - Ha XL7; lia).
    assert (OE : forall a b, E <= a -> b <= E + 55768 -> b <= SH_LO \/ SH_HI <= a) by (intros a b Ha Hb; pose proof OFFE as D; unfold id in D; unfold SH_LO, SH_HI; clear - D Ha Hb; lia).
    assert (OF : forall a b, FB <= a -> b <= FB + 256 -> b <= SH_LO \/ SH_HI <= a) by (intros a b Ha Hb; pose proof FHI as D; unfold id in D; unfold SH_LO, SH_HI; clear - D Ha Hb; lia).
    split; [apply shd_app; [exact X47| apply OE; clear; lia]|]. split; [apply shd_app; [exact X47| apply OE; clear; lia]|].
    split; [apply shd_app; [exact X47| apply OP; clear; lia]|]. split; [apply shd_app; [exact X47| apply OP; clear; lia]|]. split; [apply shd_app; [exact X47| apply OP; clear; lia]|].
    split; [apply shd_app; [exact X47| apply OF; clear; lia]|]. split; [apply shd_app; [exact X47| apply OF; clear; lia]| exact I]. }
  destruct AX as [AX1 AX2].
  assert (SHf : shzW a0segs Wgl m1 FV (FV + 24)).
  { apply (shzW_of_acc a0segs Wgl m1 FV 24 FV (FV + 24) (sm_acc_fave m1 ltac:(clear - GFR; lia) SHV) AFW); [clear - GFR; lia| clear - GFR GSP0; lia| clear; lia|].
    clear - AX1. Z.div_mod_to_equations. lia. }
  assert (SHc : shpW a0segs Wgl m1 CO (CO + 12)).
  { apply (shpW_of_acc a0segs Wgl m1 CO 12 (sm_acc_cost m1 ltac:(clear - GFR; lia) SHC) AFW); [clear - GFR; lia| clear - GFR GSP0; lia]. }
  eapply (l1_realizes RT AF Σ1 PMc _ T c1 MST Hc1).
  eapply (A0_sm_grp cx e g _ gp tp sp F1 fc1 lp len P SHE CO FV CX GM CEP XL11 ltac:(clear - GFR; lia) ltac:(unfold CEIL; rewrite ACE; unfold STACK_WIN; clear - GFR; lia)
            ltac:(clear - GFR; lia) ltac:(unfold CEIL; rewrite ACE; unfold STACK_WIN; clear - GFR; lia) AE ltac:(dj DEFB) ltac:(dj DEFB) ltac:(unfold id; left; clear; lia)
            HA HNG HM ZB MV LF LPF rf sel cost fave gs (Z.of_nat j) totc Jsp w1360 m1 m1);
    [clear - Egs' Hj Hn HK HK2; lia| bz_params; clear - Hj Hn HK HK2 HM BZbsL__ BZbsH__; lia| exact Htc| intros tt Htt v Hv; apply RFF; [clear - Htt HNG; lia| exact Hv]| intros tt Htt; apply FVB; exact Htt| exact LJsp
    | exact RFQ| exact SEL| exact SPL| exact HI| exact FAVE| exact COST| exact (kmem_inv_N _ _ MI1)| apply munch_refl| apply wmono_refl
    | intros m_ MU_; apply (u8arr_munch a0segs _ m1 m_ _ _ AR1 MU_); unfold Wg; x_disj
    | intros m_ MU_; apply (u8arr_munch a0segs _ m1 m_ _ _ LEN MU_); unfold Wg; x_disj
    | intros m_ MU_; apply (u32arr_munch a0segs _ m1 m_ _ _ LPK MU_); unfold Wg; x_disj
    | unfold Wg; vwW LOB| unfold Wg; vwW EH2| exact SHa| exact SHe| exact SHf| exact SHc| |].
  - (* [comment removed for export] *)
    intros m2 Jsp' w1360' cb' q0 q1 q3 q4 q5 q6 q7 x3 x5 x6. cbv zeta. intros LT LJsp' Hbt Hbc RFQ2 SEL2 SPL2 HI2 FAVE2 COST2 NMI2 MU2 WM2. apply evt_done. clear Hc1. intros c2 Hc2.
    unfold Wg in MU2.
    lazymatch type of MU2 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m1 m2 SK ART1 MI1 ST1 PR1 NMI2 MU2 WM2 ltac:(fp_ours)) as (ART2 & MI2 & ST2 & PR2 & STEP2) end.
    clear RFQ SEL SPL HI FAVE COST SHa SHe SHf SHc. xfer_l1 m1 m2 MU2 WM2. clear COST2.
    destruct (GE_facts nMTF gs ltac:(clear - Egs' Hj Hn HK HK2; lia)) as (G1 & G2 & G3).
    assert (EG' : Gj e s (S j) = sm_group_iter arr1 len lp nG nMTF (SGS rf sel cost fave (Z.of_nat j) totc gs)) by (rewrite Gj_S, Elen, Elp, <- EGJ; reflexivity).
    rewrite sm_group_iter_eq in EG'. cbv zeta in EG'. cbn [g_rfreq g_sel g_cost g_fave g_nSel g_totc g_gs] in EG'.
    assert (Hj1 : Z.of_nat (S j) < KSEL e) by (destruct (Z.lt_ge_cases (Z.of_nat (S j)) (KSEL e)); [assumption| exfalso; clear - H LT G3 Egs' Hj HK HK2; nia]).
    destruct n as [|n']; [exfalso; clear - Hj Hj1; lia|].
    pose proof (IH (S j) s lp len Σ1 m0 m2 Jsp' w1360' q0 q1 q3 q4 q5 q6 q7 x3 (Z_to_bv 64 (GE nMTF gs + 1)) x5 x6 F1 fc1 T c2) as IH'.
    rewrite EG' in IH'. cbn [g_rfreq g_sel g_cost g_fave g_nSel g_totc g_gs] in IH'.
    eapply IH'; [split; [exact GF| exact GEND]| exact Elen| exact Elp| exact LF| exact LPF| clear - Hj; lia| clear; lia| exact SK| exact LJsp'
                | exact AR1| exact LEN| exact LPK| exact RFQ2| exact SEL2| exact SPL2| exact HI2| exact FAVE2| exact LOB| exact EH2| exact SHC| exact SHV| exact WRC
                | exact ART2| exact MI2| exact ST2| exact PR2| | | exact Hc2| exact Hk].
    + apply (pfp_trans _ _ _ _ m0 m1 m2 ACC1). apply (pfp_weaken _ _ _ _ Wgl m1 m2 STEP2). per_interval; cbn [KFrame.outside]; lia.
    + eapply wmono_trans; [exact WMA1| exact WM2].
  - (* [comment removed for export] *)
    intros m2 Jsp' w1360' cb' ra' q0 q1 q3 q4 q5 q6 q7 x3 x5 x6. cbv zeta. intros LAST LJsp' Hbt Hbc RFQ2 SEL2 SPL2 HI2 FAVE2 COST2 NMI2 MU2 WM2. apply evt_done. clear Hc1. intros c2 Hc2.
    unfold Wg in MU2.
    lazymatch type of MU2 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m1 m2 SK ART1 MI1 ST1 PR1 NMI2 MU2 WM2 ltac:(fp_ours)) as (ART2 & MI2 & ST2 & PR2 & STEP2) end.
    clear RFQ SEL SPL HI FAVE COST SHa SHe SHf SHc. xfer_l1 m1 m2 MU2 WM2. clear COST2.
    destruct (GE_facts nMTF gs ltac:(clear - Egs' Hj Hn HK HK2; lia)) as (G1 & G2 & G3).
    assert (EG' : Gj e s (S j) = sm_group_iter arr1 len lp nG nMTF (SGS rf sel cost fave (Z.of_nat j) totc gs)) by (rewrite Gj_S, Elen, Elp, <- EGJ; reflexivity).
    rewrite sm_group_iter_eq in EG'. cbv zeta in EG'. cbn [g_rfreq g_sel g_cost g_fave g_nSel g_totc g_gs] in EG'.
    assert (Hj1 : Z.of_nat (S j) = KSEL e) by (destruct (Z.eq_dec (Z.of_nat (S j)) (KSEL e)); [assumption| exfalso; clear - n0 LAST G3 Egs' Hj HK HK2; nia]).
    assert (EEND : Gend e s = Gj e s (S j)) by (unfold Gend; f_equal; clear - Hj1; lia).
    pose proof (Hk c2 m2 Jsp' w1360' totc gs ra' q0 q1 (Z_to_bv 64 CO) (Z_to_bv 64 (totc + fst (sm_best (Z.to_nat nG) (COSTC arr1 len lp nG gs (GE nMTF gs) cost) 0 999999999 (-1))))
                  (Z_to_bv 64 (GE nMTF gs + 1)) (Z_to_bv 64 (fst (sm_best (Z.to_nat nG) (COSTC arr1 len lp nG gs (GE nMTF gs) cost) 0 999999999 (-1)))) q3 q4 q5 q6 q7
                  x3 (Z_to_bv 64 (GE nMTF gs + 1)) x5 x6 F1 fc1) as K'.
    rewrite EEND, EG' in K'. cbn [g_rfreq g_sel g_cost g_fave g_nSel g_totc g_gs] in K'.
    eapply K'; [exact Hc2| exact LJsp'| exact AR1| exact LEN| exact LPK| exact RFQ2| exact SEL2| exact SPL2| exact HI2| exact LOB| exact EH2| exact SHC| exact SHV
               | exact ART2| exact MI2| exact ST2| exact PR2| | ].
    + apply (pfp_trans _ _ _ _ m0 m1 m2 ACC1). apply (pfp_weaken _ _ _ _ Wgl m1 m2 STEP2). per_interval; cbn [KFrame.outside]; lia.
    + eapply wmono_trans; [exact WMA1| exact WM2].
Qed.
(* [comment removed for export] *)
Ltac cutL R k H nb :=
  let T := fresh "T" in
  lazymatch type of R with rw_cells ?segs ?m ?A ?cs =>
    destruct (rw_cells_cutZ segs m A cs k R) as [H T]; clear R; rename T into R;
    cbn [firstn skipn cells_size csize Nat.add] in H, R;
    lazymatch type of R with rw_cells _ _ ?A' _ => replace A' with nb in R by (cbn; lia) end
  end.
Ltac glueL H1 H2 H :=
  lazymatch type of H1 with rw_cells ?segs ?m ?A ?cs1 => lazymatch type of H2 with rw_cells _ _ ?B ?cs2 =>
    assert (H : rw_cells segs m A (cs1 ++ cs2))
      by (apply (proj2 (rw_cells_app_iff_c segs m A cs1 cs2)); split; [exact H1| cbn [cells_size csize Nat.add];
          lazymatch goal with |- rw_cells _ _ ?A' _ => replace A' with B by (cbn; lia) end; exact H2]);
    cbn [app] in H; clear H1 H2 end end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation Wit := [(E + 1704, E + 19706); (E + 37708, E + 39256); (E + 45448, E + 51640); (E + 51640, E + 55768); (P + 152, P + 160); (P + 232, P + 1344); (P + 1344, P + 1440);
                 (FV, FV + 24); (CO, CO + 12)].

Lemma sm_l2_iter : forall (k : nat) (Σ0 Σ1 : rts RT) (m0 m : mem) (Jsp : list byte) (v16 v24 w1360 : word) (totc gs : Z)
    (t0 t1 t2 a3 a4 a5 a6 a7 s3 s5 s11 t3 t4 t5 t6 : word) F fc T c,
  (k < 4)%nat -> SOK Σ1 -> rt_live RT Σ1 = rt_live RT Σ0 -> rt_frames RT Σ1 = rt_frames RT Σ0 -> nG <= rt_credit RT Σ1 -> length Jsp = 1112%nat ->
  u8arr a0segs m A1 (zb8 arr1 ARR1_SIZE) ->
  u8arr a0segs m (E + 37708) (ovb (it_len (ITK k)) (jseg J 37708 1548) 1548) ->
  u32arr a0segs m (E + 51640) (ovw (it_lp (ITK k)) (jseg J 51640 4128) 1032) ->
  u32arr a0segs m (E + 45448) (ovw (it_rfreq (ITK k)) (jseg J 45448 6192) 1548) ->
  u8arr a0segs m (E + 1704) (ovb (it_sel (ITK k)) (jseg J 1704 18002) 18002) ->
  rw_cells a0segs m (P + 16) (sm_loA cx e FB SHF SHE v16 v24) -> rw_cells a0segs m (P + 152) [C8 (Z_to_bv 64 (Z.of_nat k))] -> rw_cells a0segs m (P + 160) (sm_loB cx e SHE) ->
  u8arr a0segs m (P + 232) Jsp ->
  rw_cells a0segs m (P + 1344) (sm_hi cx e CO FV w1360 totc gs) ->
  rw_cells a0segs m (E + 640) (EHEAD2 cx g e) ->
  rw_cells a0segs m (SHF + 4) [C1 z8; C1 (Z_to_bv 8 4)] -> rw_cells a0segs m (SHF + 8) [C1 z8; C1 z8; C1 z8] -> wr_at asegs m CO 12 -> wr_at asegs m FV 24 ->
  ART RT Σ1 m -> KMem.mem_inv asegs m -> stk asegs m lo P -> PRESI m ->
  rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) P Wit m0 m ->
  ASTA RT Σ1 PMc (eq (MS (IZ (Z_to_bv 64 0x8a9d8) t0 t1 t2 (Z_to_bv 64 FV) (Z_to_bv 64 0) (Z_to_bv 64 24) a3 a4 a5 a6 a7
                              (Z_to_bv 64 (E + 45448)) s3 s5 (Z_to_bv 64 (E + 668)) s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x52ea0) fc None m (seg_rom a0segs))) c ->
  (forall (last : bool) c' (Σ' : rts RT) (m' : mem) (Jsp' : list byte) (w1360' : word) (totc' gs' : Z) (ra' u0 u1 u2 e0 e1 e2 e3 e4 e5 e6 e7 x3 x11 u3 u4 u5 u6 : word) F' fc',
     last = (k + 1 =? 4)%nat ->
     (if last
      then ASTA RT Σ' PMc (eq (MS (IZ ra' u0 u1 u2 e0 e1 e2 e3 e4 e5 e6 e7 (Z_to_bv 64 (E + 45448)) x3 (Z_to_bv 64 (it_nSel (ITK (S k)))) (Z_to_bv 64 (E + 668)) x11 u3 u4 u5 u6)
                                  F' (Z_to_bv 64 0x8f29c) fc' None m' (seg_rom a0segs))) c'
      else ASTA RT Σ' PMc (eq (MS (IZ (Z_to_bv 64 0x8a9d8) u0 u1 u2 (Z_to_bv 64 FV) (Z_to_bv 64 0) (Z_to_bv 64 24) e3 e4 e5 e6 e7
                                      (Z_to_bv 64 (E + 45448)) x3 (Z_to_bv 64 (it_nSel (ITK (S k)))) (Z_to_bv 64 (E + 668)) x11 u3 u4 u5 u6)
                                  F' (Z_to_bv 64 0x52ea0) fc' None m' (seg_rom a0segs))) c') ->
     SOK Σ' -> rt_live RT Σ' = rt_live RT Σ0 -> rt_frames RT Σ' = rt_frames RT Σ0 -> rt_credit RT Σ' = rt_credit RT Σ1 - nG -> length Jsp' = 1112%nat ->
     u8arr a0segs m' A1 (zb8 arr1 ARR1_SIZE) ->
     u8arr a0segs m' (E + 37708) (ovb (it_len (ITK (S k))) (jseg J 37708 1548) 1548) ->
     u32arr a0segs m' (E + 51640) (ovw (it_lp (ITK (S k))) (jseg J 51640 4128) 1032) ->
     u32arr a0segs m' (E + 45448) (ovw (it_rfreq (ITK (S k))) (jseg J 45448 6192) 1548) ->
     u8arr a0segs m' (E + 1704) (ovb (it_sel (ITK (S k))) (jseg J 1704 18002) 18002) ->
     rw_cells a0segs m' (P + 16) (sm_loA cx e FB SHF SHE v16 v24) -> rw_cells a0segs m' (P + 152) [C8 (Z_to_bv 64 (Z.of_nat (S k)))] -> rw_cells a0segs m' (P + 160) (sm_loB cx e SHE) ->
     u8arr a0segs m' (P + 232) Jsp' ->
     rw_cells a0segs m' (P + 1344) (sm_hi cx e CO FV w1360' totc' gs') ->
     rw_cells a0segs m' (E + 640) (EHEAD2 cx g e) ->
     rw_cells a0segs m' (SHF + 4) [C1 z8; C1 (Z_to_bv 8 4)] -> rw_cells a0segs m' (SHF + 8) [C1 z8; C1 z8; C1 z8] -> wr_at asegs m' CO 12 -> wr_at asegs m' FV 24 ->
     ART RT Σ' m' -> KMem.mem_inv asegs m' -> stk asegs m' lo P -> PRESI m' ->
     rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) P Wit m0 m' ->
     realizes asegs c' T) ->
  realizes asegs c T.
Proof.
  intros k Σ0 Σ1 m0 m Jsp v16 v24 w1360 totc gs t0 t1 t2 a3 a4 a5 a6 a7 s3 s5 s11 t3 t4 t5 t6 F fc T c Hk4 SK LVE0 FRE0 CRED LJsp
    AR1 LEN LPK RFQ SEL LOA ITER LOB SPL HI EH2 SHC SHV WRC WRV ART0 MI0 ST0 PR0 ACC Hc Hk.
  act_open. openST. pose proof SK as (FRM & SP0E & LIVS). pose proof (LIVS _ LIVE) as LVE.
  destruct (proj2 SFB k Hk4) as (BL & BP & BG & BM).
  remember (ITK k) as s eqn:Es.
  rewrite <- LVE0, <- FRE0 in ACC.
  (* [comment removed for export] *)
  eapply (memset_call G PMc FDO MST Σ1 FV 24 z8 m); [exact MSET| exact SK| clear - GFR GSP0; lia| clear; lia| | exact ART0| exact MI0| exact ST0| exact Hc|].
  { apply (cdst_frame G Σ1 m FV 24 SK (sm_acc_fave m ltac:(clear - GFR; lia) SHV) WRV); clear; lia. }
  clear Hc. intros c1 m1 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F1 fc1 Hc1 ART1 MI1 ST1 WM1 BY1 STEP1.
  pose proof (pres_step_ours G Σ1 _ _ m m1 SK PR0 STEP1 ltac:(right; left; clear; lia)) as PR1.
  xfer_rt G SK STEP1 WM1 m m1.
  rewrite (KMState.ret_pc_even 0x8a9d8 ltac:(lia) eq_refl) in Hc1.
  assert (FAVE : u32arr a0segs m1 FV (zw32 (zero6 (it_fave s)) 6)).
  { pose proof (n_rw_CB_of_bytes m1 FV (repeat z8 (Z.to_nat 24)) BY1 ltac:(rewrite repeat_length; exact WRV)) as CZ. rewrite repeat_length in CZ.
    change (Z.to_nat 24) with 24%nat in CZ. exact (fave_zero_bytes m1 FV (it_fave s) CZ). }
  clear BY1.
  pose proof (pfp_trans _ _ _ _ m0 m m1 ACC (pfp_weaken _ _ _ _ Wit m m1 STEP1 ltac:(per_interval; cbn [KFrame.outside]; lia))) as ACC1. clear ACC STEP1 WM1.
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ1 PMc _ T c1 MST Hc1).
  eapply (A0_sm_it1 cx e _ gp tp sp F1 fc1 P SHE FB SHF v16 v24 CX HA m1); [apply frdW_intro; [exact LOA| exact I]| apply frdW_intro; [exact LOB| exact I]|].
  apply evt_done. clear Hc1. intros c2 Hc2.
  (* [comment removed for export] *)
  pose proof (sm_rfrows (Z.to_nat nG) 0 (it_rfreq s) (it_lp s) (it_len s) Σ1 m1 m1 v16 v24 w1360 (Z_to_bv 64 totc) (Z_to_bv 64 gs)) as RL.
  replace (E + 45448 + 1032 * 0) with (E + 45448) in RL by (clear; lia). replace (nG - 0) with nG in RL by (clear; lia).
  eapply (RL _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 T c2 ltac:(clear - HNG; lia) ltac:(clear; lia) ltac:(clear - HNG; lia) SK BL RFQ LEN LPK HI LOA LOB EH2 ART1 MI1 ST1 PR1 (pfp_refl _ _ _ _ m1) (wmono_refl _ m1) Hc2).
  clear RL Hc2 RFQ LEN LPK HI LOA LOB EH2.
  intros c3 m3 y0 y1 y3 y4 y5 y6 y7 z3 z4 z5 z6 F3 fc3 Hc3 RFQ LEN LPK HI LOA LOB EH2 ART3 MI3 ST3 PR3 ACCr WMr.
  xfer_rt G SK ACCr WMr m1 m3.
  change (sm_rfreq_zero (Z.to_nat nG) (it_rfreq s) A 0) with (it_rf0 e s) in RFQ.
  change (if nG =? 6 then sm_lenpack (Z.to_nat A) (it_lp s) (it_len s) 0 else it_lp s) with (it_lpk e s) in LPK.
  pose proof (pfp_trans _ _ _ _ m0 m1 m3 ACC1 (pfp_weaken _ _ _ _ Wit m1 m3 ACCr ltac:(per_interval; cbn [KFrame.outside]; lia))) as ACC3. clear ACC1 ACCr WMr.
  (* [comment removed for export] *)
  assert (LPF : nG = 6 -> forall v j, 0 <= v < A -> 0 <= j < 3 -> zdef (it_lpk e s) (4 * v + j) = true /\ 0 <= zget (it_lpk e s) (4 * v + j) < 2097152).
  { intros H6 v j Hv Hj. destruct (BP H6 v j Hv Hj) as (D & _ & R). exact (conj D R). }
  eapply (sm_grploop (Z.to_nat (KSEL e)) 0 s (it_lpk e s) (it_len s) Σ1 m3 m3 Jsp w1360 _ _ _ _ _ _ _ _ _ _ _ F3 fc3 T c3 BG eq_refl eq_refl BL LPF ltac:(clear - HK; lia) ltac:(clear - HK; lia) SK LJsp
            AR1 LEN LPK RFQ SEL SPL HI FAVE LOB EH2 SHC SHV WRC ART3 MI3 ST3 PR3 (pfp_refl _ _ _ _ m3) (wmono_refl _ m3) Hc3).
  clear Hc3 AR1 LEN LPK RFQ SEL SPL HI FAVE LOB EH2 SHC SHV.
  intros c4 m4 Jsp' w1360' totc' gs' ra4 y0' y1' y2' g0 g1 g2 g3 g4 g5 g6 g7 z3' z4' z5' z6' F4 fc4 Hc4 LJsp' AR1 LEN LPK RFQ SEL SPL HI LOB EH2 SHC SHV ART4 MI4 ST4 PR4 ACCg WMg.
  xfer_rt G SK ACCg WMg m3 m4.
  pose proof (pfp_trans _ _ _ _ m0 m3 m4 ACC3 (pfp_weaken _ _ _ _ Wit m3 m4 ACCg ltac:(per_interval; cbn [KFrame.outside]; lia))) as ACC4. clear ACC3 ACCg WMg.
  (* [comment removed for export] *)
  pose proof (proj1 BG (Z.to_nat (KSEL e)) ltac:(clear - HK; lia)) as GFE'. cbv zeta in GFE'. change (Gj e s (Z.to_nat (KSEL e))) with (Gend e s) in GFE'.
  destruct GFE' as (Egs & EnS & Htc & RFF & FVB & SLF).
  assert (EgsN : g_gs (Gend e s) = nMTF) by (rewrite Egs; apply Z.min_r; clear - HK HK2; lia).
  (* [comment removed for export] *)
  assert (SHe : shzW a0segs [(P + 152, P + 160)] m4 E (E + 55768)).
  { apply (sm_shE' Σ1 m4 _ SK ART4). intros x Hx X47. cbn [disjoint_from].
    split; [apply shd_app; [exact X47| right; unfold SH_HI; clear - XL7; lia]| exact I]. }
  eapply (l1_realizes RT AF Σ1 PMc _ T c4 MST Hc4).
  eapply (A0_sm_it4b cx e g _ gp tp sp F4 fc4 P SHE CO FV FB SHF v16 v24 CX AE (Z.of_nat k) w1360' totc' gs' m4 m4);
    [clear - Hk4; lia| exact ITER| exact (kmem_inv_N _ _ MI4)| apply munch_refl| apply wmono_refl| vwW LOA| vwW LOB| vwW HI| vwW EH2| exact SHe|].
  clear ITER SHe Hc4. intros m5 qa0 qa1 qa3 ITER NMI5 MU5 WM5. apply evt_done. intros c5 Hc5.
  lazymatch type of MU5 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m4 m5 SK ART4 MI4 ST4 PR4 NMI5 MU5 WM5 ltac:(fp_ours)) as (ART5 & MI5 & ST5 & PR5 & STEP5) end.
  xfer_l1 m4 m5 MU5 WM5. clear NMI5 MU5 WM5.
  pose proof (pfp_trans _ _ _ _ m0 m4 m5 ACC4 (pfp_weaken _ _ _ _ Wit m4 m5 STEP5 ltac:(per_interval; cbn [KFrame.outside]; lia))) as ACC5. clear ACC4 STEP5.
  (* [comment removed for export] *)
  unfold sm_hi in HI. cbv zeta in HI. cutL HI 8%nat HIa (P + 1408). cutL HI 1%nat SL (P + 1416).
  pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'. destruct CX' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ME16 & _).
  set (qE := E / 4). assert (E4 : E = 4 * qE) by (subst qE; clear - ME16; Z.div_mod_to_equations; lia). clearbody qE.
  pose proof (sm_mkl_cps RT AF HBM PMc FDO MST lo P usp sp0 FB SHF fr live0 Wsm mi G ACE FRLO ROOM FRB E qE (jseg J 37708 1548) (jseg J 45448 6192) A nG (g_rfreq (Gend e s)) (ml_len e s) gp tp
                LIVE E4 TP ltac:(clear - HA; lia) ltac:(clear - HNG; lia)) as ML.
  specialize (ML ltac:(intros x Hx; cbn [outside]; clear - Hx; lia)).
  specialize (ML ltac:(intros tt v Htt Hv; destruct (RFF tt v Htt Hv) as [D R]; rewrite EgsN in R; split; [exact D| bz_params; clear - R HM BZbsH__; lia])).
  specialize (ML ltac:(intros t' Ht'; destruct (proj1 BM t' Ht') as (X1 & X2 & _); split; [exact X1|];
                        rewrite (hbMakeCodeLengths_pt _ _ _ _ _ znew znew eq_refl eq_refl) in X2; exact X2)).
  specialize (ML (Z.to_nat nG) 0%nat Σ1 Σ1 m5 m5).
  replace (E + 37708 + 258 * Z.of_nat 0) with (E + 37708) in ML by (clear; lia). replace (E + 45448 + 1032 * Z.of_nat 0) with (E + 45448) in ML by (clear; lia).
  refine (cps_realizes asegs _ _ T c5 (ML _ _ _ _ sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F4 fc4 ltac:(clear - HNG; lia) ltac:(clear - HNG; lia) SK eq_refl eq_refl ltac:(clear - CRED HNG; lia)
            ART5 MI5 ST5 PR5 LEN RFQ SL (pfp_refl _ _ _ _ m5)) Hc5 _).
  clear ML Hc5 LEN RFQ SL.
  intros c6 (Σ6 & m6 & ra6 & x0 & x1 & x2 & y0'' & y1'' & y3'' & y4'' & y5'' & y6'' & y7'' & x3' & x4' & x5' & x6' & F6 & fc6 & Hc6 & SK6 & LV6 & FR6 & CR6 & ART6 & MI6 & ST6 & PR6 & LEN & RFQ & SL & ACCm).
  xfer_rtf G SK ACCm m5 m6.
  pose proof (pfp_trans _ _ _ _ m0 m5 m6 ACC5 (pfp_weaken _ _ _ _ Wit m5 m6 ACCm ltac:(per_interval; cbn [KFrame.outside]; lia))) as ACC6. clear ACC5 ACCm.
  glueL SL HI HIb. glueL HIa HIb HI.
  (* [comment removed for export] *)
  destruct (MLt e s (Z.to_nat nG)) as [[[l' h'] w'] p'] eqn:EML.
  assert (EIT : ITK (S k) = SITS l' (g_rfreq (Gend e s)) (it_lpk e s) (g_sel (Gend e s)) (g_cost (Gend e s)) (g_fave (Gend e s)) (g_nSel (Gend e s)) h' w' p').
  { rewrite ITk_S, <- Es, (proj2 BM), EML. reflexivity. }
  rewrite EIT in Hk. cbn [it_len it_lp it_rfreq it_sel it_nSel] in Hk.
  unfold ml_len in LEN. replace (0 + Z.to_nat nG)%nat with (Z.to_nat nG) in LEN by (clear; lia). rewrite EML in LEN. cbn [fst] in LEN.
  replace (Z.of_nat k + 1) with (Z.of_nat (S k)) in ITER by (clear; lia).
  rewrite LVE0 in LV6, ACC6. rewrite FRE0 in FR6, ACC6.
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ6 PMc _ T c6 MST Hc6).
  eapply (A0_sm_it6 cx e _ gp tp sp F6 fc6 P SHE CO FV CX (Z.of_nat (S k)) w1360' totc' gs' m6);
    [clear - Hk4; lia| apply frdW_intro; [exact ITER| exact I]| apply frdW_intro; [exact HI| exact I]| |].
  - intros NX. apply evt_done. clear Hc6. intros c7 Hc7.
    eapply (Hk false c7 Σ6 m6 Jsp' w1360' totc' gs' (Z_to_bv 64 0) _ _ _ (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0));
      [symmetry; apply Nat.eqb_neq; clear - NX; lia| exact Hc7| exact SK6| exact LV6| exact FR6| rewrite CR6; clear - HNG; lia| exact LJsp'
      | exact AR1| exact LEN| exact LPK| exact RFQ| exact SEL| exact LOA| exact ITER| exact LOB| exact SPL| exact HI| exact EH2| exact SHC| exact SHV| exact WRC| exact WRV
      | exact ART6| exact MI6| exact ST6| exact PR6| exact ACC6].
  - intros LAST. apply evt_done. clear Hc6. intros c7 Hc7.
    eapply (Hk true c7 Σ6 m6 Jsp' w1360' totc' gs');
      [symmetry; apply Nat.eqb_eq; clear - LAST; lia| exact Hc7| exact SK6| exact LV6| exact FR6| rewrite CR6; clear - HNG; lia| exact LJsp'
      | exact AR1| exact LEN| exact LPK| exact RFQ| exact SEL| exact LOA| exact ITER| exact LOB| exact SPL| exact HI| exact EH2| exact SHC| exact SHV| exact WRC| exact WRV
      | exact ART6| exact MI6| exact ST6| exact PR6| exact ACC6].
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sm_l2_iters : forall (n k : nat) (Σ0 Σ1 : rts RT) (m0 m : mem) (Jsp : list byte) (v16 v24 w1360 : word) (totc gs : Z)
    (t0 t1 t2 a3 a4 a5 a6 a7 s3 s5 s11 t3 t4 t5 t6 : word) F fc T c,
  (k + n = 4)%nat -> (1 <= n)%nat -> SOK Σ1 -> rt_live RT Σ1 = rt_live RT Σ0 -> rt_frames RT Σ1 = rt_frames RT Σ0 -> Z.of_nat n * nG <= rt_credit RT Σ1 -> length Jsp = 1112%nat ->
  u8arr a0segs m A1 (zb8 arr1 ARR1_SIZE) ->
  u8arr a0segs m (E + 37708) (ovb (it_len (ITK k)) (jseg J 37708 1548) 1548) ->
  u32arr a0segs m (E + 51640) (ovw (it_lp (ITK k)) (jseg J 51640 4128) 1032) ->
  u32arr a0segs m (E + 45448) (ovw (it_rfreq (ITK k)) (jseg J 45448 6192) 1548) ->
  u8arr a0segs m (E + 1704) (ovb (it_sel (ITK k)) (jseg J 1704 18002) 18002) ->
  rw_cells a0segs m (P + 16) (sm_loA cx e FB SHF SHE v16 v24) -> rw_cells a0segs m (P + 152) [C8 (Z_to_bv 64 (Z.of_nat k))] -> rw_cells a0segs m (P + 160) (sm_loB cx e SHE) ->
  u8arr a0segs m (P + 232) Jsp ->
  rw_cells a0segs m (P + 1344) (sm_hi cx e CO FV w1360 totc gs) ->
  rw_cells a0segs m (E + 640) (EHEAD2 cx g e) ->
  rw_cells a0segs m (SHF + 4) [C1 z8; C1 (Z_to_bv 8 4)] -> rw_cells a0segs m (SHF + 8) [C1 z8; C1 z8; C1 z8] -> wr_at asegs m CO 12 -> wr_at asegs m FV 24 ->
  ART RT Σ1 m -> KMem.mem_inv asegs m -> stk asegs m lo P -> PRESI m ->
  rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) P Wit m0 m ->
  ASTA RT Σ1 PMc (eq (MS (IZ (Z_to_bv 64 0x8a9d8) t0 t1 t2 (Z_to_bv 64 FV) (Z_to_bv 64 0) (Z_to_bv 64 24) a3 a4 a5 a6 a7
                              (Z_to_bv 64 (E + 45448)) s3 s5 (Z_to_bv 64 (E + 668)) s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x52ea0) fc None m (seg_rom a0segs))) c ->
  (forall c' (Σ' : rts RT) (m' : mem) (Jsp' : list byte) (w1360' : word) (totc' gs' : Z) (ra' u0 u1 u2 e0 e1 e2 e3 e4 e5 e6 e7 x3 x11 u3 u4 u5 u6 : word) F' fc',
     ASTA RT Σ' PMc (eq (MS (IZ ra' u0 u1 u2 e0 e1 e2 e3 e4 e5 e6 e7 (Z_to_bv 64 (E + 45448)) x3 (Z_to_bv 64 (it_nSel (ITK 4))) (Z_to_bv 64 (E + 668)) x11 u3 u4 u5 u6)
                            F' (Z_to_bv 64 0x8f29c) fc' None m' (seg_rom a0segs))) c' ->
     SOK Σ' -> rt_live RT Σ' = rt_live RT Σ0 -> rt_frames RT Σ' = rt_frames RT Σ0 -> rt_credit RT Σ' = rt_credit RT Σ1 - Z.of_nat n * nG -> length Jsp' = 1112%nat ->
     u8arr a0segs m' A1 (zb8 arr1 ARR1_SIZE) ->
     u8arr a0segs m' (E + 37708) (ovb (it_len (ITK 4)) (jseg J 37708 1548) 1548) ->
     u32arr a0segs m' (E + 51640) (ovw (it_lp (ITK 4)) (jseg J 51640 4128) 1032) ->
     u32arr a0segs m' (E + 45448) (ovw (it_rfreq (ITK 4)) (jseg J 45448 6192) 1548) ->
     u8arr a0segs m' (E + 1704) (ovb (it_sel (ITK 4)) (jseg J 1704 18002) 18002) ->
     rw_cells a0segs m' (P + 16) (sm_loA cx e FB SHF SHE v16 v24) -> rw_cells a0segs m' (P + 152) [C8 (Z_to_bv 64 4)] -> rw_cells a0segs m' (P + 160) (sm_loB cx e SHE) ->
     u8arr a0segs m' (P + 232) Jsp' ->
     rw_cells a0segs m' (P + 1344) (sm_hi cx e CO FV w1360' totc' gs') ->
     rw_cells a0segs m' (E + 640) (EHEAD2 cx g e) ->
     rw_cells a0segs m' (SHF + 4) [C1 z8; C1 (Z_to_bv 8 4)] -> rw_cells a0segs m' (SHF + 8) [C1 z8; C1 z8; C1 z8] -> wr_at asegs m' CO 12 -> wr_at asegs m' FV 24 ->
     ART RT Σ' m' -> KMem.mem_inv asegs m' -> stk asegs m' lo P -> PRESI m' ->
     rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) P Wit m0 m' ->
     realizes asegs c' T) ->
  realizes asegs c T.
Proof.
  induction n as [|n IH]. { intros; lia. }
  intros k Σ0 Σ1 m0 m Jsp v16 v24 w1360 totc gs t0 t1 t2 a3 a4 a5 a6 a7 s3 s5 s11 t3 t4 t5 t6 F fc T c Hkn Hn SK LVE0 FRE0 CRED LJsp
    AR1 LEN LPK RFQ SEL LOA ITER LOB SPL HI EH2 SHC SHV WRC WRV ART0 MI0 ST0 PR0 ACC Hc Hk.
  pose proof (proj1 SFB) as ST0'. unfold smB_static in ST0'. destruct ST0' as (_ & HNG & _).
  eapply (sm_l2_iter k Σ0 Σ1 m0 m Jsp v16 v24 w1360 totc gs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc T c ltac:(clear - Hkn; lia) SK LVE0 FRE0 ltac:(clear - CRED HNG; nia) LJsp
            AR1 LEN LPK RFQ SEL LOA ITER LOB SPL HI EH2 SHC SHV WRC WRV ART0 MI0 ST0 PR0 ACC Hc).
  clear Hc AR1 LEN LPK RFQ SEL LOA ITER LOB SPL HI EH2 SHC SHV WRC WRV ART0 MI0 ST0 PR0 ACC.
  intros last c1 Σ' m' Jsp' w1360' totc' gs' ra' u0 u1 u2 e0 e1 e2 e3 e4 e5 e6 e7 x3 x11 u3 u4 u5 u6 F' fc' Elast Hc' SK' LV' FR' CR' LJsp'
    AR1 LEN LPK RFQ SEL LOA ITER LOB SPL HI EH2 SHC SHV WRC WRV ART' MI' ST' PR' ACC'.
  destruct (Nat.eqb_spec (k + 1) 4) as [E4|N4]; subst last.
  - (* [comment removed for export] *)
    assert (n = 0)%nat by (clear - Hkn E4; lia). subst n. replace (S k) with 4%nat in * by (clear - E4; lia).
    eapply (Hk c1 Σ' m' Jsp' w1360' totc' gs'); [exact Hc'| exact SK'| exact LV'| exact FR'| rewrite CR'; clear; lia| exact LJsp'
      | exact AR1| exact LEN| exact LPK| exact RFQ| exact SEL| exact LOA| exact ITER| exact LOB| exact SPL| exact HI| exact EH2| exact SHC| exact SHV| exact WRC| exact WRV
      | exact ART'| exact MI'| exact ST'| exact PR'| exact ACC'].
  - eapply (IH (S k) Σ0 Σ' m0 m' Jsp' v16 v24 w1360' totc' gs' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' T c1 ltac:(clear - Hkn; lia) ltac:(clear - Hkn N4; lia) SK' LV' FR'
              ltac:(rewrite CR'; clear - CRED HNG; nia) LJsp' AR1 LEN LPK RFQ SEL LOA ITER LOB SPL HI EH2 SHC SHV WRC WRV ART' MI' ST' PR' ACC' Hc').
    intros c2 Σ2 m2 Jsp2 w1360'' totc'' gs'' ra2 p0 p1 p2 q0 q1 q2 q3 q4 q5 q6 q7 y3 y11 p3 p4 p5 p6 F2 fc2 Hc2 SK2 LV2 FR2 CR2 LJsp2.
    eapply (Hk c2 Σ2 m2 Jsp2 w1360'' totc'' gs''); [exact Hc2| exact SK2| exact LV2| exact FR2| rewrite CR2, CR'; clear; nia| exact LJsp2].
Qed.

End SMG.

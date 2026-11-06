(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_defs D_kit I_read. Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_read.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require RT_liveprim. Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_liveprim.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require Import L2Kit L2Act L2Stmt B0_fs_L2f B0_sm_L2a B0_sm_L2b B0_sm_L2c.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzArr BzCMem BzCStream BzCState BzCMtf BzCHuff BzArrD CmpMem CmpCut CmpCutSM CmpCutSmA BzCFactsSmA CmpCutSmB BzCFactsGm BzCSmF1 BzCFactsSmB BzCFactsSd CmpHmKit CmpSmKit CmpSmKit2 AsanKit AsanKit2 AsanCut AsanCutB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmas1 BzCHuffF1.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_smV B0_cmp_sdV B0_cmp_smV B0_cmp_fsP B0_cmp_smP.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).


Lemma mod16_linqT : forall x, x mod 16 = 0 -> exists q, x = 16 * q.
Proof. intros x H. exists (x / 16). Z.div_mod_to_equations. lia. Qed.

Ltac cutL R k H nb :=
  let T := fresh "T" in
  lazymatch type of R with rw_cells ?segs ?m ?A ?cs =>
    destruct (rw_cells_cutZ segs m A cs k R) as [H T]; clear R; rename T into R;
    cbn [firstn skipn cells_size csize Nat.add] in H, R;
    lazymatch type of R with rw_cells _ _ ?A' _ => replace A' with nb in R by (cbn; lia) end
  end.

Section SMT.
Context {BZP : BzParams} {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis SMAL : stack_malloc_contract RT 2.
Hypothesis HBM : hbMakeCodeLengths_contract RT.
Hypothesis AF_PRIM : af_live_primary RT.   (* [comment removed for export] *)

Theorem sendMTFValues_cps : sendMTFValues_contract RT smA_facts smB_facts sd_facts.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cx g e lo usp eD W
    FDO MST Ha0 TP CEQ GM GB GZ EM AM LIVE LIV1 LIV2 LIVF FRMAX CRED ART0 MI0 ST0 LOW LOR SPT AL CX SEP IMG ZI BWOK NB0 ROOMZ SFA SFB SDF.
  subst a0. intros T c Hc Hk.
  pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'.
  destruct CX' as (RE & RE' & RA1 & RA1' & RA2 & RA2' & RFT & RFT' & _ & _ & _ & _ & ME16 & MA1 & MA2 & MFT & _).
  pose proof IMG as IMG'. unfold cctx_img, img_apart, IMG_LO3 in IMG'. cbn [ci_hi aci_c B0C] in IMG'. destruct IMG' as (_ & IA1 & IA2 & IFT & _).
  pose proof alloc_ceiling_range as ACR. bz_params. unfold FTAB_WORDS, ESTATE_SIZE, CEIL in *.
  change (4 * 65537) with 262148 in *.
  pose proof (AF_PRIM Σ m _ _ ART0 LIVE ltac:(clear; lia)) as IE. unfold SEGTOP_A in IE.
  destruct (mod16_linqT _ AL) as [qsp ALQ].
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. fold usp in SPR.
  unfold RT_STACK in LOR.
  destruct AM as (AR1 & AR2 & FTB). unfold FTAB_WORDS in FTB.
  pose proof (proj1 SFB) as STB. unfold smB_static in STB. destruct STB as (_ & HNG & _).
  set (P := 32 * ((usp - 1696) / 32)).
  assert (PF : lo + 65536 + 304 <= P /\ (P = usp - 1696 \/ P = usp - 1712) /\ P mod 16 = 0 /\ exists q, P = 32 * q).
  { subst P. split; [clear - ALQ LOR; Z.div_mod_to_equations; lia|]. split; [clear - ALQ; Z.div_mod_to_equations; lia|]. split; [clear; Z.div_mod_to_equations; lia|].
    exists ((usp - 1696) / 32). reflexivity. }
  destruct PF as (YPl4 & PCASE & SPA & PQ).
  assert (YPl : lo <= P) by (clear - YPl4; lia). assert (YPh : P + 1696 <= usp) by (clear - PCASE; lia). assert (YPa : usp <= P + 1712) by (clear - PCASE; lia).
  clearbody P.
  destruct (fs_aconsts_of_art RT AF Σ m ART0) as [AC AU].
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ PMc _ T c MST Hc).
  eapply (B0_smA_in1 cx _ sp gp tp F fc P lo ltac:(unfold CEIL; rewrite CEQ; exact LOW) YPl (ex_intro _ qsp ALQ) PQ PCASE m);
    [exact ST0| exact (kmem_inv_N _ _ MI0)| exact AC| exact AU|].
  intros m1 jsp jg ng w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128
    w1264 w1272 w1280 w1288 w1296 w1304 w1312 w1320 w1328 w1336 w1344 w1352 w1360 w1368 w1376
    w1384 w1392 w1400 w1408 w1416 w1424 w1432 w1440 w1448 w1456 w1464 w1472 w1480 w1488 w1496 w1504 w1512 w1520 w1528 w1536 w1544 w1552 w1560 w1568
    x1 x2 NGE FR ST1 NMI1 MU1 WM1. apply evt_done. clear Hc. intros c1 Hc1.
  fold usp in NGE, MU1.
  assert (MU1k : KFrame.munch [(P, usp)] m m1) by exact MU1.
  assert (ART1 : ART RT Σ m1).
  { apply (art_of_munch RT AF Σ m m1 [(P, usp)] P ART0 ltac:(clear - LOW YPl; lia) MU1k WM1). per_interval. left. unfold USTACK_TOP in *. match goal with HX : _ <= _ < _ |- _ => clear - SPT HX YPl; lia end. }
  assert (MI1 : KMem.mem_inv bsegs m1).
  { apply (kmem_inv_munch' bsegs [(P, usp)] m m1 MI0 MU1k NMI1). intros x Hx. revert Hx. refine (not_outside_cons _ _ _ _ _ _ _); [intro| refine (not_outside_nil _ _)].
    unfold KMem.UTOP, USTACK_TOP in *. match goal with HX : _ <= _ < _ |- _ => clear - SPT HX; lia end. }
  (* [comment removed for export] *)
  cutL FR 3%nat C0 (P + 24). cutL FR 1%nat SL24 (P + 32). cutL FR 13%nat LOWc (P + 136). cutL FR 1%nat SPC (P + 1264). cutL FR 15%nat SETc (P + 1384). cutL FR 24%nat HIc (P + 1576).
  destruct (rw_cells_cutZ b0segs m1 (P + 1576) _ 1%nat FR) as [GAPC SAV]. clear FR. cbn [firstn skipn cells_size csize Nat.add] in GAPC, SAV.
  replace (P + 1576 + Z.of_nat (ng + 0)) with (usp + -104) in SAV by (clear - NGE; lia).
  destruct (rw_cells_CB_C1s b0segs _ _ _ _ SPC) as [_ Ljsp]. pose proof (u8arr_of_rw_cells b0segs m1 _ _ _ SPC) as SPL. clear SPC.
  destruct (rw_cells_CB_C1s b0segs _ _ _ _ GAPC) as [_ Ljg]. pose proof (u8arr_of_rw_cells b0segs m1 _ _ _ GAPC) as GAPU. clear GAPC.
  assert (NG16 : (16 <= ng)%nat) by (clear - NGE PCASE; lia).
  rewrite <- (firstn_skipn 16 jg) in GAPU. apply (proj1 (u8arr_app b0segs m1 (P + 1576) _ _)) in GAPU. destruct GAPU as [I16 GAPR].
  assert (Li16 : length (firstn 16 jg) = 16%nat) by (rewrite length_firstn, Ljg; clear - NG16; lia).
  rewrite Li16 in GAPR. replace (P + 1576 + Z.of_nat 16) with (P + 1592) in GAPR by (clear; lia).
  pose proof (stk_of_u8arr b0segs _ _ _ GAPR) as GAP. rewrite length_skipn, Ljg in GAP.
  replace (P + 1592 + Z.of_nat (ng - 16)) with (usp + -104) in GAP by (clear - NGE NG16; lia). clear GAPR.
  pose proof (ck_intro P CStack) as KP. pose proof (ck_intro usp CStack) as KU.
  pose proof (ck_intro (c_E cx) (CLive (c_E cx) 55768)) as KE.
  pose proof (ck_intro (c_A1 cx) (CLive (c_A1 cx) ARR1_SIZE)) as KA1. pose proof (ck_intro (c_A2 cx) (CLive (c_A2 cx) ARR2_SIZE)) as KA2.
  pose proof (ck_intro (c_FT cx) (CLive (c_FT cx) 262148)) as KFT.
  assert (BLW : c_E cx + 55768 <= P /\ c_A1 cx + ARR1_SIZE <= P /\ c_A2 cx + ARR2_SIZE <= P /\ c_FT cx + 262148 <= P) by (clear - RE' RA1' RA2' RFT' CEQ LOW YPl; lia).
  destruct BLW as (BLE & BL1 & BL2 & BLF).
  destruct EM as (EH1 & INU & UNS & EH2 & MTF & SEL & SELM & LEN & CODE & RFQ & LPK).
  xfer_l1 m m1 MU1 WM1.
  (* [comment removed for export] *)
  refine (cps_realizes bsegs _ _ T c1 _ Hc1 _).
  { eapply (SMAL Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 160 lo FDO MST
              ltac:(right; left; reflexivity) TP).
    - reflexivity.
    - change (fs_size 2) with 256. clear; lia.
    - reflexivity.
    - clear - FRMAX. lia.
    - clear - CRED. lia.
    - exact ART1.
    - exact MI1.
    - unfold call_ok. rewrite unsigned_lit by (clear - YPl YPh SPR LOW ACR CEQ; lia). unfold STACK_WIN, USTACK_TOP, RT_STACK in *.
      split; [exact ST1|]. split; [exact LOW|]. split; [clear - YPl4; lia|]. split; [clear - SPT YPh; lia| exact SPA]. }
  intros c2 (Σ1 & f & Hq2 & FRS1 & LV1 & SP1 & CR1 & FPOS & F64 & FTOP). change (fs_size 2) with 256 in *.
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hq2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRF & WRS & ZSH) & Hc2). clear Hq2.
  destruct RS2 as (u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite unsigned_lit in ST2, PRES2 by (clear - YPl YPh SPR LOW ACR CEQ; lia). change (256 - 8) with 248 in WRF. change (256 / 8) with 32 in WRS.
  rewrite (KMState.ret_pc_even 0x8bcb0 ltac:(lia) eq_refl) in Hc2.
  (* [comment removed for export] *)
  set (Wsm := [(c_E cx, c_E cx + 55768); (c_A2 cx, c_A2 cx + ARR2_SIZE)]).
  assert (WCL : forall x, ~ outside Wsm x -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x).
  { intros x Hx. unfold Wsm in Hx. cbn [outside] in Hx.
    assert (C : (c_E cx <= x < c_E cx + 55768) \/ (c_A2 cx <= x < c_A2 cx + ARR2_SIZE)) by (clear - Hx; lia).
    destruct C as [C|C]; right; right; left.
    - exists (c_E cx), 55768. split; [exact LIVE| exact C].
    - exists (c_A2 cx), ARR2_SIZE. split; [exact LIV2| exact C]. }
  set (SHF := f / 8 + 2147450880). change (shad f) with SHF in WRS, ZSH.
  destruct (act_setup RT AF Σ Σ1 m m2 2 f SHF 256 32 lo P usp Wsm eq_refl eq_refl eq_refl eq_refl ART0 ART2 FRS1 LV1 SP1 LOW
              ltac:(unfold RT_STACK; clear - YPl4; lia) ltac:(clear - YPh; lia) SPT SPA WCL) as (G & SOK & _ & FSEG & FHI & SHR0 & SHR1 & GSELF & GLV).
  destruct (GLV _ _ LIVE) as (GFE & GSE & _ & _ & OFE & _). destruct (GLV _ _ LIV1) as (GF1 & GS1 & _ & _ & OF1 & _).
  destruct (GLV _ _ LIV2) as (GF2 & GS2 & _ & _ & OF2 & _). destruct (GLV _ _ LIVF) as (GFF & GSF & _).
  clearbody SHF. unfold SEGTOP_A in FSEG.
  (* [comment removed for export] *)
  assert (STEP2 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) P [] m1 m2) by exact (pfp_of_pres _ _ _ [] m1 m2 PRES2).
  assert (WRFn : wr_at b0segs m2 f 248) by exact WRF. assert (WRSn : wr_at b0segs m2 SHF 32) by exact WRS. clear WRF WRS.
  clear ST1.
  xfer_rt G I STEP2 WM2 m1 m2.
  assert (GFE' : c_E cx + 55768 <= f \/ f + 256 <= c_E cx) by (clear - GFE; lia).
  assert (GF1' : c_A1 cx + ARR1_SIZE <= f \/ f + 256 <= c_A1 cx) by (clear - GF1; lia).
  assert (GF2' : c_A2 cx + ARR2_SIZE <= f \/ f + 256 <= c_A2 cx) by (clear - GF2; lia).
  assert (GFF' : c_FT cx + 262148 <= f \/ f + 256 <= c_FT cx) by (clear - GFF; lia).
  (* [comment removed for export] *)
  set (SHE := c_E cx / 8 + 2147450880).
  assert (AE : sanchor (c_E cx) SHE) by (split; [clear - ME16; Z.div_mod_to_equations; lia| reflexivity]).
  clearbody SHE.
  eapply (sm_act RT AF HBM cx g e lo sp gp tp CX SEP GM GB GZ SFA SFB TP PMc P f SHF SHE (rt_frames RT Σ) (rt_live RT Σ) (rt_sp0 RT Σ) FDO MST G CEQ YPh
            ltac:(unfold RT_STACK; clear - YPl4; lia) ltac:(clear - FRMAX; lia) LIVE LIV1 LIV2 LIVF AE IE GFE' GF1' GF2' GFF' GSE GS1 GS2 GSF GSELF FSEG FHI OFE OF2 SHR0 SHR1 m2
            SDF ZI BWOK NB0 ROOMZ Σ1 jsp (firstn 16 jg) w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128
            w1264 w1272 w1280 w1288 w1296 w1304 w1312 w1320 w1328 w1336 w1344 w1352 w1360 w1368 w1376
            w1384 w1392 w1400 w1408 w1416 w1424 w1432 w1440 w1448 w1456 w1464 w1472 w1480 w1488 w1496 w1504 w1512 w1520 w1528 w1536 w1544 w1552 w1560 w1568
            s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 T c2 SOK ltac:(rewrite CR1; clear - CRED HNG; lia) Ljsp Li16);
    try eassumption.
  - unfold emem. split; [exact EH1|]. split; [exact INU|]. split; [exact UNS|]. split; [exact EH2|]. split; [exact MTF|]. split; [exact SEL|]. split; [exact SELM|].
    split; [exact LEN|]. split; [exact CODE|]. split; [exact RFQ| exact LPK].
  - intros c' Σ2 m' z0 z1 z2 g0 g1 g2 g3 g4 g5 g6 g7 z3 z4 z5 z6 F' fc' Hc' FRS2 LV2 SP2 CR2 ART' MI' ST' EM' AR1' AR2' FTB' BWD PR'.
    apply Hk. exists Σ2.
    split; [| split; [rewrite LV2, LV1; reflexivity| split; [exact FRS2| split; [exact SP2| rewrite CR2, CR1; clear; lia]]]].
    eapply ASTA_conseq; [exact Hc'|]. intros ms <-. exists m', z0, z1, z2, g0, g1, g2, g3, g4, g5, g6, g7, z3, z4, z5, z6, F', fc'.
    split; [reflexivity|]. split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact EM'|]. split; [exact AR1'|]. split; [exact AR2'|]. split; [exact FTB'|].
    split; [exact BWD|].
    exact (pres_final RT AF Σ lo P usp Wsm m m1 m2 m' ART0 LOW ltac:(clear - YPl; lia) ltac:(clear - YPh; lia) MU1 PRES2 PR').
Qed.
End SMT.

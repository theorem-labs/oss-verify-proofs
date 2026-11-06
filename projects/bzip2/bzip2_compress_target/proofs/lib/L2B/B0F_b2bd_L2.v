(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_defs D_kit I_read RT_liveprim L_libA. Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_read.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_liveprim.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require L_hkit L_harn_defs RT_globals.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require R_unwind_chain. Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_unwind_chain.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require Import L2Kit L2Act L2Stmt L2StmtS L2StmtD B0_sessK.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require Import B0_b2bc_K B0F_b2bd_K.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzInv BzContracts CmpMem CmpCut CmpCarve CmpFsKit0 AsanKit AsanCut AsanCutB0 B0_b2c_cbV B0_b2c_hcV B0_b2c_wrV B0F_b2d_wrV B0F_b2d_wrW.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require GlueCarve BzDOut BzDState BzWalkArith3.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).

Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut.
Module HD := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harn_defs.TwinB__.
Module HK := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_hkit.TwinB__.

Section B2BD.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis SMAL : stack_malloc_contract RT 2.
Hypothesis MSET : memset_icontract RT e_asan_memset.
Hypothesis INITC : forall (AC : ACeil), @bzDecompressInit_contract AC RT.
Hypothesis BZDC : forall (AC : ACeil), @bzDecompress_contract AC RT.
Hypothesis ENDC : forall (AC : ACeil), @bzDecompressEnd_contract AC RT.
Hypothesis ACL : forall Σ (m : mem), ART RT Σ m -> @alloc_ceiling (aceil_of_sp (rt_sp0 RT Σ)) = rt_sp0 RT Σ - STACK_WIN.

Ltac fp_ours PHI := per_interval; match goal with HX : _ <= _ < _ |- _ => clear - HX PHI; lia end.
Ltac in_list := cbn [app In]; repeat (first [left; reflexivity | right]).

Theorem b2bd_glue : HD.b2bd_cps RT OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A dec_okL.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ob dl zb cap ocap zcap z junk sm lo zlen
         FDO MST A0E A1E A2E A3E A4E A5E TP RAE CAPR ZLE ZCR BYS ZLIV OLIV CAPO OBNZ OBJ DLF DLC DL8 DLSH POSN LIVB FRB CRED HREC LIB ART0 MI0 ST0 LOW LOR SPT SPA SPS.
  intros T c Hc Hk. subst a0 a1 a2 a3 a4 a5 ra. unfold entry_st in Hc.
  set (usp := bv_unsigned sp) in *. set (small := if sm then 1 else 0) in *.
  pose (ACI := aceil_of_sp (rt_sp0 RT Σ)).
  pose proof (ACL Σ m ART0) as CEQ. change (@alloc_ceiling ACI = rt_sp0 RT Σ - STACK_WIN) in CEQ.
  (* [comment removed for export] *)
  assert (ZL0 : 0 <= zlen) by (unfold zlen; lia).
  assert (SMR : small = 0 \/ small = 1) by (unfold small; destruct sm; [right| left]; reflexivity).
  pose proof (@alloc_ceiling_range ACI) as ACR.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. fold usp in SPR.
  unfold HD.B2B_STACK, OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_libiface.TwinB__.FUZZ_STACK in LOR. unfold HD.B2B_LIVE in LIVB. unfold HD.B2B_FRAMES in FRB. unfold HD.B2BD_COST in CRED.
  set (P := 32 * ((usp - 160) / 32)).
  assert (PCASE : P = usp - 160 \/ P = usp - 176) by (subst P; clear - SPA; Z.div_mod_to_equations; lia).
  assert (PF : lo + 200000 <= P /\ P + 160 <= usp /\ usp <= P + 176 /\ P mod 16 = 0) by (subst P; clear - SPA LOR; Z.div_mod_to_equations; lia).
  destruct PF as (PLO & PHI & PHI' & SPA').
  assert (USPQ : exists q, usp = 16 * q) by (exists (usp / 16); clear - SPA; Z.div_mod_to_equations; lia).
  assert (PQ : exists q, P = 32 * q) by (exists ((usp - 160) / 32); reflexivity).
  assert (LLO : @CEILv ACI <= lo) by (unfold CEILv; rewrite CEQ; exact LOW).
  pose proof (af_live_range RT AF Σ m _ _ ART0 ZLIV) as (ZB0 & ZBH & ZBI). pose proof (af_live_range RT AF Σ m _ _ ART0 OLIV) as (OB0 & OBH & OBI). unfold SEGTOP_A in ZBI, OBI.
  destruct DLF as (fD & kD & FDIN & FDLO & FDHI).
  pose proof (af_frames_range RT AF Σ m fD kD ART0 FDIN) as (FD0 & FD1 & _ & FDL).
  pose proof (af_frames_align RT AF Σ m fD kD ART0 FDIN) as (_ & FDSEG). unfold SEGTOP_A in FDSEG.
  pose proof (af_frames_hi RT AF Σ m fD kD ART0 FDIN) as FDHI'.
  assert (DLR : 0 < dl) by (clear - FD0 FDLO; lia).
  assert (DLH : dl + 4 <= @CEILv ACI) by (unfold CEILv; rewrite CEQ; clear - FD1 FDHI; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  assert (AC : aconsts B0C m) by (split; [exact (ro_C8_KN m _ _ G1)| exact (ro_C8_KN m _ _ G2)]).
  assert (AU : aconsts_uar B0C m) by (split; [exact (ro_C8_KN m _ _ G3)| exact (ro_C4_KN m _ _ G4)]). clear G1 G2 G3 G4.
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ PMc _ T c MST Hc).
  eapply (@B0_b2d_D1 ACI _ P lo ob dl zb zlen small 0 sp gp tp F fc LLO ltac:(clear - PLO; lia) PCASE USPQ PQ DLR DLH m);
    [exact ST0| exact (kmem_inv_N _ _ MI0)| exact AC| exact AU|].
  clear Hc AC AU. intros m1 v0 v8 v16 v32 v40 v48 a1' a2' SL GAP SAV ST1 NMI1 MU1 WM1. apply evt_done. intros c1 Hc1.
  fold usp in GAP, SAV, MU1.
  assert (MU1k : KFrame.munch [(P, usp)] m m1) by exact MU1.
  assert (ART1 : ART RT Σ m1).
  { apply (art_of_munch RT AF Σ m m1 [(P, usp)] P ART0 ltac:(clear - LOW PLO; lia) MU1k WM1). per_interval. left. unfold USTACK_TOP in *. match goal with HX : _ <= _ < _ |- _ => clear - SPT HX; lia end. }
  assert (MI1 : KMem.mem_inv bsegs m1).
  { apply (kmem_inv_munch' bsegs [(P, usp)] m m1 MI0 MU1k NMI1). intros x Hx. revert Hx. refine (not_outside_cons _ _ _ _ _ _ _); [intro| refine (not_outside_nil _ _)].
    unfold KMem.UTOP, USTACK_TOP in *. match goal with HX : _ <= _ < _ |- _ => clear - SPT HX; lia end. }
  pose proof (ck_intro P CStack) as KP. pose proof (ck_intro usp CStack) as KU.
  clear ST0. xfer_l1 m m1 MU1 WM1.
  (* [comment removed for export] *)
  assert (PU : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; clear - PLO PHI SPR LOW ACR CEQ; lia).
  refine (cps_realizes bsegs _ _ T c1 _ Hc1 _).
  { eapply (SMAL Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 160 lo FDO MST ltac:(right; left; reflexivity) TP).
    - reflexivity.
    - change (fs_size 2) with 256. clear; lia.
    - reflexivity.
    - clear - FRB. unfold FRAMES_MAX in *. lia.
    - clear - CRED. lia.
    - exact ART1.
    - exact MI1.
    - unfold call_ok. rewrite PU. unfold STACK_WIN, USTACK_TOP, RT_STACK in *.
      split; [exact ST1|]. split; [exact LOW|]. split; [clear - PLO; lia|]. split; [clear - SPT PHI; lia| exact SPA']. }
  clear Hc1. intros c2 (Σ1 & FB & Hq2 & FRS1 & LV1 & SP1 & CR1 & FPOS & F64 & FTOP). change (fs_size 2) with 256 in *.
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hq2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRF & WRS & ZSH) & Hc2). clear Hq2.
  destruct RS2 as (u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite PU in ST2, PRES2. change (256 - 8) with 248 in WRF. change (256 / 8) with 32 in WRS. change (Z.to_nat (160 / 8)) with 20%nat in ZSH.
  rewrite (KMState.ret_pc_even 0x88c74 ltac:(lia) eq_refl) in Hc2.
  (* [comment removed for export] *)
  set (Wc := [(ob, ob + cap); (dl, dl + 4)]).
  assert (DCL : forall x, dl <= x < dl + 4 -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x).
  { intros x Hx. right; right; right; left. exists fD, kD. split; [exact FDIN| clear - Hx FDLO FDHI; lia]. }
  assert (WCL : forall x, ~ outside Wc x -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x).
  { intros x Hx. unfold Wc in Hx. cbn [outside] in Hx.
    assert (C : (ob <= x < ob + cap) \/ (dl <= x < dl + 4)) by (clear - Hx; lia).
    destruct C as [C|C]; [right; right; left; exists ob, ocap; split; [exact OLIV| clear - C CAPO; lia]| exact (DCL x C)]. }
  set (SHF := FB / 8 + 2147450880). change (shad FB) with SHF in WRS, ZSH.
  destruct (act_setup RT AF Σ Σ1 m m2 2 FB SHF 256 32 lo P usp Wc eq_refl eq_refl eq_refl eq_refl ART0 ART2 FRS1 LV1 SP1 LOW
              ltac:(unfold RT_STACK; clear - PLO; lia) ltac:(clear - PHI; lia) SPT SPA' WCL) as (G & SOK & _ & FSEG & FHI & SHR0 & SHR1 & GSELF & GLV).
  pose proof (ag_ax G) as AX. pose proof (ag_gfr G) as (_ & FR1). unfold SEGTOP_A in FSEG.
  clearbody SHF.
  assert (STEP2 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) P [] m1 m2) by exact (pfp_of_pres _ _ _ [] m1 m2 PRES2).
  clear ST1. xfer_rt G I STEP2 WM2 m1 m2.
  assert (AG02 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> m2 a = m a).
  { intros a Ha. rewrite (PRES2 a (aclient_mono _ _ usp _ _ P _ Ha (fun e H => H) (fun e H => H) ltac:(clear - PHI; lia))). apply MU1k. cbn [KFrame.outside]. split; [| exact I].
    destruct (aclient_split RT AF Σ m usp (bv_unsigned a) ART0 Ha) as [EE|EE]; clear - EE LOW PLO PHI; lia. }
  assert (DLC2 : rw_cells b0segs m2 dl [C4 (Z_to_bv 64 cap)]).
  { apply k2n_C4. apply (rw_cells_agree_nw bsegs m m2 dl _ DLC). intros a Ha. cbn [KCells.cells_size KCells.csize Nat.add] in Ha. apply AG02. apply DCL. clear - Ha. lia. }
  pose proof (ck_intro dl CCaller) as KDL.
  assert (FBIN1 : rt_frames RT Σ1 = [] ++ (FB, 2%nat) :: rt_frames RT Σ) by (rewrite FRS1; reflexivity).
  pose proof (af_frames_disj RT AF Σ1 m2 FB 2%nat fD kD [] _ ART2 FBIN1 FDIN) as DLFB. change (fs_size 2) with 256 in DLFB.
  assert (DLFB' : id (FB + 256 <= dl \/ dl + 4 <= FB)) by (unfold id; clear - DLFB FDLO FDHI; lia).
  pose proof (af_fshadow_apart RT AF Σ1 m2 FB 2%nat ART2 ltac:(rewrite FRS1; left; reflexivity)) as (_ & FSHX). change (fs_size 2) with 256 in FSHX.
  pose proof (FSHX fD kD ltac:(rewrite FRS1; right; exact FDIN)) as DLSHF.
  assert (SHFE : shad FB = SHF /\ shad (FB + 256) = SHF + 32) by (destruct AX as [A8 AE]; rewrite AE; unfold shad, SHB; clear - A8; Z.div_mod_to_equations; lia).
  rewrite (proj1 SHFE), (proj2 SHFE) in DLSHF.
  assert (DLSHF' : id (SHF + 32 <= dl \/ dl + 4 <= SHF)) by (unfold id; clear - DLSHF FDLO FDHI; lia).
  assert (DLP : dl + 4 <= P) by (clear - DLH LLO PLO; unfold CEILv in *; lia).
  clear DLFB DLSHF FSHX.
  (* [comment removed for export] *)
  pose proof (ck_intro FB CFrame) as KFB. pose proof (ck_intro SHF CShadow) as KSH.
  destruct (n_wr_at_rw_CB m2 FB 24 (wr_at_sub bsegs m2 FB 248 FB 24 WRF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (jh & HDJ).
  assert (HD0 : rw_cells b0segs m2 FB [C8 (jw8 jh 0); C8 (jw8 jh 8); C8 (jw8 jh 16)]).
  { assert (LJ : Z.of_nat (length jh) = 24) by (destruct HDJ as [[Hwf _] _]; cbn in Hwf; destruct Hwf as [HL _]; rewrite HL; reflexivity).
    change [C8 (jw8 jh 0); C8 (jw8 jh 8); C8 (jw8 jh 16)] with (jcells jh 0 [8; 8; 8]%nat).
    eapply (carve_cb b0segs); [exact HDJ| apply jcells_wf; cbn [sum_nat Nat.add]; lia| rewrite jcells_bytes by (cbn [sum_nat Nat.add]; lia); exact (jseg_all jh 24 LJ)| rewrite jcells_size; reflexivity]. }
  clear HDJ.
  destruct (n_wr_at_rw_CB m2 (FB + 32) 80 (wr_at_sub bsegs m2 FB 248 (FB + 32) 80 WRF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (jb & SMJ).
  destruct (strm_carveD b0segs m2 (FB + 32) jb SMJ) as (SM & LQ1 & LQ2). clear SMJ.
  pose proof (n_rw_CB_of_bytes' m2 SHF (repeat (Z_to_bv 8 0) 20) ZSH ltac:(rewrite repeat_length; apply (wr_at_sub bsegs m2 SHF 32); [exact WRS| clear; lia| clear; lia| clear; lia])) as SH20.
  rewrite repeat_length in SH20.
  destruct (n_wr_at_rw_CB m2 (SHF + 20) 12 (wr_at_sub bsegs m2 SHF 32 (SHF + 20) 12 WRS ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (j12 & SH12).
  clear WRF WRS ZSH.
  (* [comment removed for export] *)
  assert (FBH : FB + 256 <= @CEILv ACI) by (unfold CEILv; rewrite CEQ; exact FR1).
  assert (DST : 0 < ob < 18446744073709551616) by (clear - OB0 OBH ACR CEQ CAPO CAPR; lia).
  assert (SRC : 0 < zb < 18446744073709551616) by (clear - ZB0 ZBH ACR CEQ ZLE ZL0; lia).
  assert (NMI2 : mem_inv b0segs m2) by exact (kmem_inv_N _ _ MI2).
  eapply (l1_realizes RT AF Σ1 PMc _ T c2 MST Hc2).
  eapply (@B0_b2d_D2 ACI _ P FB SHF (FB + 32) lo ob dl zb zlen small 0 sp gp tp F2 fc2 LLO ltac:(clear - PLO; lia) DST DLR DLH SRC ltac:(clear - SMR; lia) ltac:(clear; lia) AX eq_refl FSEG FBH
            ltac:(unfold SH_HI; exact SHR1) GSELF m2 v0 v8 v16 v32 v40 v48 _ _ _ _);
    [exact SL| exact HD0| exact SH20| exact NMI2|].
  clear Hc2 SL HD0 SH20. intros m3 a3' SL HD0 SH20 NMI3 MU3 WM3. apply evt_done. intros c3 Hc3.
  unfold b2d_W2 in MU3.
  destruct (after_l1 AF G Σ1 _ m2 m3 SOK ART2 MI2 ST2 (presi_refl _ _ _ _ m2) NMI3 MU3 WM3 ltac:(fp_ours PHI)) as (ART3 & MI3 & ST3 & PR3 & _).
  assert (GSELF' : id (FB + 256 <= SHF \/ SHF + 32 <= FB)) by exact GSELF.
  assert (PFB : FB + 256 <= P) by (clear - FR1 LOW PLO; lia).
  assert (PSH : SHF + 32 <= P) by (clear - SHR1 LLO ACR PLO; unfold CEILv in LLO; lia).
  clear ST2. xfer_l1 m2 m3 MU3 WM3. clear NMI3 MU3 WM3 NMI2.
  unfold b2c_shadow in SH20.
  destruct (rw_cells_cutZ b0segs m3 SHF _ 4%nat SH20) as [SHa SHr]. cbn [firstn skipn cells_size csize Nat.add] in SHa, SHr. change (Z.of_nat 4) with 4 in SHr.
  destruct (rw_cells_cutZ b0segs m3 (SHF + 4) _ 10%nat SHr) as [SHz SHb]. cbn [firstn skipn cells_size csize Nat.add] in SHz, SHb.
  replace (SHF + 4 + Z.of_nat 10) with (SHF + 14) in SHb by (clear; lia). clear SH20 SHr.
  unfold STRMD in SM.
  destruct (rw_cells_cutZ b0segs m3 (FB + 32) _ 11%nat SM) as [SMa SMt]. cbn [firstn skipn cells_size csize Nat.add] in SMa, SMt.
  replace (FB + 32 + Z.of_nat 56) with (FB + 88) in SMt by (clear; lia). clear SM.
  assert (ZSH3 : KMem.bytes_at bsegs m3 (SHF + 4) (repeat z8 10)) by exact (proj1 (n_rw_cells_bytes b0segs m3 _ _ SHz)).
  assert (ACC3 : acc bsegs m3 (FB + 88) 24).
  { pose proof (acc_of_zero_shadow bsegs m3 FB SHF 4 10 (proj1 AX) (proj2 AX) ltac:(clear - FSEG; lia) ltac:(clear; lia) ZSH3) as A.
    apply (acc_sub bsegs m3 _ _ (FB + 88) 24 A); clear; lia. }
  assert (WRT : wr_at bsegs m3 (FB + 88) 24) by exact (proj2 (n_rw_cells_bytes b0segs m3 _ _ SMt)).
  (* [comment removed for export] *)
  eapply (memset_call G PMc FDO MST Σ1 (FB + 88) 24 z8 m3); [exact MSET| exact SOK| clear - FSEG FBH ACR; unfold CEILv in FBH; lia| clear; lia
                                                            | exact (cdst_frame G Σ1 m3 (FB + 88) 24 SOK ACC3 WRT ltac:(clear; lia) ltac:(clear; lia))
                                                            | exact ART3| exact MI3| exact ST3| exact Hc3|].
  clear Hc3 SMt ACC3 ZSH3. intros c4 m4 x0 x1 x2 f1 f2 f3 f4 f5 f6 f7 x3 x4 x5 x6 F4 fc4 Hc4 ART4 MI4 ST4 WM4 BY4 STEP4.
  rewrite (KMState.ret_pc_even 0x88d64 ltac:(lia) eq_refl) in Hc4.
  pose proof (pres_step_ours G Σ1 _ _ m3 m4 SOK PR3 STEP4 ltac:(right; left; clear; lia)) as PR4.
  clear ST3. xfer_rt G SOK STEP4 WM4 m3 m4.
  pose proof (n_rw_CB_of_bytes' m4 (FB + 88) (repeat z8 (Z.to_nat 24)) BY4 ltac:(rewrite repeat_length; exact WRT)) as Z24. rewrite repeat_length in Z24.
  assert (SMt : rw_cells b0segs m4 (FB + 88) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
  { eapply (carve_cb b0segs); [exact Z24| cbn [cells_wf cell_wf]; repeat split| reflexivity| reflexivity]. }
  pose proof (rw_cells_glue b0segs m4 (FB + 32) _ _ (FB + 88) SMa SMt ltac:(cbn [cells_size csize Nat.add]; clear; lia)) as SM. cbn [app] in SM.
  clear SMa SMt Z24 BY4 WRT STEP4 WM4.
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ1 PMc _ T c4 MST Hc4). eapply B0_b2d_D3. apply evt_done. clear Hc4. intros c5 Hc5.
  assert (CEQ1 : @alloc_ceiling ACI = rt_sp0 RT Σ1 - STACK_WIN) by (rewrite SP1; exact CEQ).
  assert (SOKA4 : strm_okA RT Σ1 m4 (FB + 32)).
  { split; [exists FB, 2%nat; split; [rewrite FRS1; left; reflexivity| change (fs_size 2) with 256; clear; lia]|].
    split; [clear - F64; Z.div_mod_to_equations; lia|].
    replace (shad (FB + 32)) with (SHF + 4) by (destruct AX as [A8 ->]; unfold shad, SHB; clear - A8; Z.div_mod_to_equations; lia).
    exact (proj1 (n_rw_cells_bytes b0segs m4 _ _ SHz)). }
  pose proof (INITC ACI Σ1 PMc (Z_to_bv 64 0x88d74) (Z_to_bv 64 P) gp tp x0 x1 x2 sp (Z_to_bv 64 P) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 0) (Z_to_bv 64 small) f3 f4 f5 f6 f7
                (Z_to_bv 64 FB) (Z_to_bv 64 2147450880) (Z_to_bv 64 (-2)) (Z_to_bv 64 FB) (Z_to_bv 64 zb) (Z_to_bv 64 ob) (Z_to_bv 64 small) (Z_to_bv 64 0) (Z_to_bv 64 (FB + 32))
                (Z_to_bv 64 SHF) x3 x4 x5 x6 F4 fc4 m4 (FB + 32) small
                (jw8 jb 0) (jw4 jb 8) (jw4 jb 12) (jw4 jb 16) (jseg jb 20 4) (jw8 jb 24) (jw4 jb 32) (jw4 jb 36) (jw4 jb 40) (jseg jb 44 4) (jw8 jb 48) lo) as IC.
  cbv zeta in IC. rewrite PU in IC.
  refine (cps_realizes bsegs _ _ T c5 (IC FDO MST eq_refl eq_refl eq_refl SMR TP CEQ1 SM LQ1 LQ2 SOKA4 ltac:(rewrite LV1; clear - LIVB; unfold LIVE_MAX in *; lia)
            ART4 MI4 ST4 ltac:(rewrite SP1; exact LOW) ltac:(unfold RT_STACK; clear - PLO; lia) ltac:(clear - SPT PHI; lia) SPA') Hc5 _).
  clear Hc5 IC. intros c6 (Σ2 & S & Hq & LV2 & FRS2 & SP2 & CR2).
  destruct (ASTA_unpack RT Σ2 _ _ c6 Hq) as (ms6 & (m5 & y0 & y1 & y2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & y3 & y4 & y5 & y6 & F5 & fc5 & h0 & nbu0 & cf0 & d0 & r0 & js & POST) & Hc6). clear Hq.
  destruct POST as (-> & ART5 & MI5 & ST5 & DS5 & SM5 & S16 & SAP & STEP5).
  rewrite (ret_pc_even 0x88d74 ltac:(lia) eq_refl) in Hc6.
  (* [comment removed for export] *)
  assert (LVall : rt_live RT Σ2 = (S, 64144) :: rt_live RT Σ) by (rewrite LV2, LV1; reflexivity).
  assert (SOK2 : sig_ok RT (rt_sp0 RT Σ) true 2 FB (rt_frames RT Σ) (rt_live RT Σ) Σ2).
  { split; [rewrite FRS2; exact FRS1|]. split; [rewrite SP2; exact SP1|]. intros e1' He. rewrite LVall. right. exact He. }
  pose proof (pres_step_ours G Σ1 _ _ m4 m5 SOK PR4 STEP5 ltac:(right; left; clear; lia)) as PR5.
  clear ST4 SM. xfer_rtf G SOK STEP5 m4 m5.
  (* [comment removed for export] *)
  set (SHD := dl / 8 + 2147450880).
  assert (AD : sanchor dl SHD) by (apply sanchor_intro; exact DL8).
  pose proof (af_fshadow_apart RT AF Σ m fD kD ART0 FDIN) as (FDSL & FDSF).
  assert (SHDR : shad fD <= shad dl /\ shad dl + 1 <= shad (fD + fs_size kD)) by (unfold shad, SHB; clear - FDLO FDHI; Z.div_mod_to_equations; lia).
  assert (DSHCL : forall x, shad dl <= x < shad dl + 1 -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x /\ outside Wc x).
  { intros x Hx. split; [right; right; right; right; exists fD, kD; split; [exact FDIN| clear - Hx SHDR; lia]|].
    unfold Wc. cbn [outside]. split; [destruct (FDSL _ _ OLIV) as [D|D]; clear - D Hx SHDR CAPO; lia|]. split; [destruct (FDSF _ _ FDIN) as [D|D]; clear - D Hx SHDR FDLO FDHI; lia| exact I]. }
  assert (DLSHb : KMem.bytes_at bsegs m (shad dl) [Z_to_bv 8 4]) by exact (proj2 DLSH).
  assert (DLACC : forall mk, rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp Wc m mk -> acc bsegs mk dl 4).
  { intros mk FPk. apply (acc_dl mk dl DL8 ltac:(clear - DLR; lia)). apply (bytes_at_agree bsegs m mk _ _ DLSHb). intros a Ha. cbn [length] in Ha.
    destruct (DSHCL (bv_unsigned a) ltac:(clear - Ha; lia)) as [C O]. exact (FPk a C O). }
  pose proof (pres_final RT AF Σ lo P usp Wc m m1 m2 m5 ART0 LOW ltac:(clear - PLO; lia) ltac:(clear - PHI; lia) MU1k PRES2 PR5) as FP5.
  assert (AFW4 : app_fp [(FB + 32, FB + 32 + 36)]) by (cbn [app_fp]; unfold SH_LO, SH_HI; split; [clear - FHI; lia| exact I]).
  assert (DL47 : 0 <= dl /\ dl + 4 <= 2^47) by (clear - DLR DLH ACR; unfold CEILv in DLH; lia).
  assert (DLFv : apartv dl 4 FB 256) by (unfold apartv; pose proof DLFB' as D; unfold id in D; clear - D; lia).
  eapply (l1_realizes RT AF Σ2 PMc _ T c6 MST Hc6).
  eapply (@B0_b2d_D4 ACI _ P FB SHF (FB + 32) lo ob dl zb zlen small 0 sp gp tp F5 fc5 LLO ltac:(clear - PLO; lia) DLR DLH eq_refl FSEG FBH SHD AD ltac:(clear - FDSEG FDLO; lia) DLFv m5 cap);
    [clear - CAPR; lia| exact SM5| exact SL| exact DLC2| exact (kmem_inv_N _ _ MI5)| exact (shpW_of_acc b0segs _ m5 dl 4 (DLACC m5 FP5) AFW4 (proj1 DL47) (proj2 DL47))|].
  clear Hc6 SM5 SL DLC2. intros m6 a1'' a2'' SM SL DLC2 NMI6 MU6 WM6. apply evt_done. intros c7 Hc7.
  unfold b2d_W4 in MU6.
  destruct (after_l1 AF G Σ2 _ m5 m6 SOK2 ART5 MI5 ST5 PR5 NMI6 MU6 WM6 ltac:(fp_ours PHI)) as (ART6 & MI6 & ST6 & PR6 & _).
  (* [comment removed for export] *)
  assert (SLIV : In (S, 64144) (rt_live RT Σ2)) by (rewrite LVall; left; reflexivity).
  assert (ZLIV2 : In (zb, zcap) (rt_live RT Σ2)) by (rewrite LVall; right; exact ZLIV).
  assert (OLIV2 : In (ob, ocap) (rt_live RT Σ2)) by (rewrite LVall; right; exact OLIV).
  assert (FBIN2 : In (FB, 2%nat) (rt_frames RT Σ2)) by (rewrite FRS2, FRS1; left; reflexivity).
  assert (FDIN2 : In (fD, kD) (rt_frames RT Σ2)) by (rewrite FRS2, FRS1; right; exact FDIN).
  pose proof (af_frames_range RT AF Σ2 m5 FB 2%nat ART5 FBIN2) as (_ & _ & _ & FBL2). change (fs_size 2) with 256 in FBL2.
  pose proof (af_fshadow_apart RT AF Σ2 m5 FB 2%nat ART5 FBIN2) as (FBS2 & _). change (fs_size 2) with 256 in FBS2. rewrite (proj1 SHFE), (proj2 SHFE) in FBS2.
  pose proof (af_frames_range RT AF Σ2 m5 fD kD ART5 FDIN2) as (_ & _ & _ & FDL2).
  pose proof (af_live_range RT AF Σ2 m5 _ _ ART5 SLIV) as (S0 & SH & SI). unfold SEGTOP_A in SI. rewrite SP2, SP1 in SH.
  assert (GFS : id (FB + 256 <= S \/ S + 64144 <= FB)) by exact (FBL2 _ _ SLIV).
  assert (GFZ : id (FB + 256 <= zb \/ zb + zcap <= FB)) by exact (FBL2 _ _ ZLIV2).
  assert (GFO : id (FB + 256 <= ob \/ ob + ocap <= FB)) by exact (FBL2 _ _ OLIV2).
  assert (GSS : id (S + 64144 <= SHF \/ SHF + 32 <= S)) by exact (FBS2 _ _ SLIV).
  assert (GSZ : id (zb + zcap <= SHF \/ SHF + 32 <= zb)) by exact (FBS2 _ _ ZLIV2).
  assert (GSO : id (ob + ocap <= SHF \/ SHF + 32 <= ob)) by exact (FBS2 _ _ OLIV2).
  assert (GDS : id (dl + 4 <= S \/ S + 64144 <= dl)) by (unfold id; destruct (FDL2 _ _ SLIV) as [D|D]; clear - D FDLO FDHI; lia).
  assert (GDZ : id (dl + 4 <= zb \/ zb + zcap <= dl)) by (unfold id; destruct (FDL2 _ _ ZLIV2) as [D|D]; clear - D FDLO FDHI; lia).
  assert (GDO : id (dl + 4 <= ob \/ ob + ocap <= dl)) by (unfold id; destruct (FDL2 _ _ OLIV2) as [D|D]; clear - D FDLO FDHI; lia).
  pose proof (af_live_disj RT AF Σ2 m5 S 64144 zb zcap [] _ ART5 LVall ZLIV) as DZS.
  pose proof (af_live_disj RT AF Σ2 m5 S 64144 ob ocap [] _ ART5 LVall OLIV) as DOS.
  pose proof (live_disj_in RT AF Σ m ob ocap zb zcap ART0 OLIV ZLIV ltac:(intros E; apply OBNZ; congruence)) as DOZ.
  assert (GZS : id (S + 64144 <= zb \/ zb + zcap <= S)) by exact DZS.
  assert (GOS : id (S + 64144 <= ob \/ ob + ocap <= S)) by exact DOS.
  assert (GOZ : id (ob + ocap <= zb \/ zb + zcap <= ob)) by exact DOZ.
  assert (PSS : S + 64144 <= P) by (clear - SH LOW PLO; lia).
  assert (PSZ : zb + zcap <= P) by (clear - ZBH LOW PLO; lia).
  assert (PSO : ob + ocap <= P) by (clear - OBH LOW PLO; lia).
  clear FBL2 FBS2 FDL2.
  pose proof (ck_intro S (CLive S 64144)) as KS. pose proof (ck_intro zb (CLive zb zcap)) as KZB. pose proof (ck_intro ob (CLive ob ocap)) as KOB.
  unfold dstate10A in DS5. destruct DS5 as (HEAD5 & HWF & NBU5 & NBUR & CF5 & CFL & MID5 & TT0 & L160 & L40 & NIU & CCRC & DR5 & SAVE5).
  assert (DR6 : drest_at b0segs m6 S r0).
  { apply (drest_transport b0segs _ m5 m6 S r0 DR5 MU6 WM6); cbn [disjoint_from]; (split; [| exact I]); pose proof GFS as D; unfold id in D; clear - D; lia. }
  clear DR5 ST5. xfer_l1 m5 m6 MU6 WM6. clear NMI6 MU6 WM6.
  (* [comment removed for export] *)
  set (cx := BCX S (FB + 32) zb zlen ob cap 0 0 small 0 0 0 0).
  set (b0 := BZS zb zlen zlen (Z_to_bv 64 0) (Z_to_bv 64 0) (jseg jb 20 4) ob cap cap (Z_to_bv 64 0) (Z_to_bv 64 0) (jseg jb 44 4) S (Z_to_bv 64 DBZA) (Z_to_bv 64 DBZF) (Z_to_bv 64 0)).
  pose proof (pres_final RT AF Σ lo P usp Wc m m1 m2 m6 ART0 LOW ltac:(clear - PLO; lia) ltac:(clear - PHI; lia) MU1k PRES2 PR6) as FP6.
  (* [comment removed for export] *)
  assert (PAYCL : forall x, zb <= x < zb + zlen -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x /\ outside Wc x).
  { intros x Hx. split; [right; right; left; exists zb, zcap; split; [exact ZLIV| clear - Hx ZLE; lia]|].
    unfold Wc. cbn [outside]. pose proof (FDL zb zcap ZLIV) as D2.
    split; [clear - DOZ Hx ZLE CAPO; lia|]. split; [clear - D2 Hx ZLE FDLO FDHI; lia| exact I]. }
  assert (PLM6 : bytes_at b0segs m6 zb z).
  { apply (bytes_at_agree bsegs m m6 _ _ BYS). intros a Ha. destruct (PAYCL (bv_unsigned a) Ha) as [C O]. exact (FP6 a C O). }
  assert (LIB6 : OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m6).
  { apply (lib_of_pfp _ _ _ _ m m6 LIB FP6). intros x Hx. unfold Wc. cbn [outside]. split; [clear - Hx OBI CAPO CAPR; lia|]. split; [clear - Hx FDSEG FDLO; lia| exact I]. }
  (* [comment removed for export] *)
  destruct (af_acc_live RT AF Σ2 m6 ob ocap ART6 OLIV2) as [WRO _].
  destruct (n_wr_at_rw_CB m6 ob cap (wr_at_sub bsegs m6 ob ocap ob cap WRO ltac:(clear; lia) ltac:(clear - CAPR CAPO; lia) ltac:(clear - CAPR CAPO; lia)) ltac:(clear - CAPR; lia)) as (OB & OBJ6).
  assert (LOB : Z.of_nat (length OB) = cap) by (destruct OBJ6 as [[Hwf _] _]; cbn in Hwf; destruct Hwf as [HL _]; rewrite HL; clear - CAPR; lia).
  pose proof (u8arr_of_rw_cells b0segs m6 ob _ OB OBJ6) as OBM. clear OBJ6 WRO.
  assert (SMB : rw_cells b0segs m6 (FB + 32) (STRM_CELLS b0)).
  { rewrite strm_cells_eq. unfold b0. cbn [bs_src bs_len bs_ai bs_til bs_tih bs_q1 bs_dst bs_dlen bs_av bs_tol bs_toh bs_q2 bs_S bs_bzalloc bs_bzfree bs_opaque].
    replace (zb + (zlen - zlen)) with zb by (clear; lia). replace (ob + (cap - cap)) with ob by (clear; lia). exact SM. }
  assert (S10 : strm10A b0 cx).
  { unfold strm10A, bzs_wf, b0, cx. cbn [bs_src bs_len bs_ai bs_til bs_tih bs_q1 bs_dst bs_dlen bs_av bs_tol bs_toh bs_q2 bs_S bs_bzalloc bs_bzfree bs_opaque b_s b_src b_len b_dst b_dlen].
    split; [split; [exact LQ1| split; [exact LQ2| clear - ZL0 ZLE ZCR CAPR; lia]]|]. repeat (split; [reflexivity|]). reflexivity. }
  assert (SOKA6 : strm_okA RT Σ2 m6 (FB + 32)).
  { split; [exists FB, 2%nat; split; [exact FBIN2| change (fs_size 2) with 256; clear; lia]|].
    split; [clear - F64; Z.div_mod_to_equations; lia|].
    replace (shad (FB + 32)) with (SHF + 4) by (destruct AX as [A8 ->]; unfold shad, SHB; clear - A8; Z.div_mod_to_equations; lia).
    exact (proj1 (n_rw_cells_bytes b0segs m6 _ _ SHz)). }
  assert (DLIVE : dliveA RT Σ2 m6 cx zb zcap ob ocap).
  { unfold dliveA, cx. cbn [b_s b_strm b_src b_len b_dst b_dlen b_tt b_ll16 b_ll4 b_n].
    split; [exact SLIV|]. split; [exact ZLIV2|]. split; [clear; lia|]. split; [clear - ZLE; lia|]. split; [exact OLIV2|]. split; [clear; lia|]. split; [clear - CAPO; lia|].
    split; [intros H; exfalso; apply H; reflexivity|]. split; [intros H; exfalso; apply H; reflexivity|]. split; [intros H; exfalso; apply H; reflexivity| exact SOKA6]. }
  assert (DPURE : dpureA cx).
  { unfold dpureA, dsepA, disj, cx. cbn [b_s b_strm b_src b_len b_dst b_dlen b_tt b_ll16 b_ll4 b_n b_small].
    split; [clear - ZL0 ZLE ZCR; lia|]. split; [exact CAPR|]. split; [exact SMR|]. split; [clear; lia|]. split; [exact S16|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [pose proof GFS as D; unfold id in D; clear - D; lia|]. split; [clear - DZS ZLE; lia|]. split; [clear - DOS CAPO; lia|].
    split; [pose proof GFZ as D; unfold id in D; clear - D ZLE; lia|]. split; [pose proof GFO as D; unfold id in D; clear - D CAPO; lia|]. split; [clear - DOZ ZLE CAPO; lia|].
    split; [intros H; exfalso; apply H; reflexivity|]. split; [intros H; exfalso; apply H; reflexivity|]. split; [intros H; exfalso; apply H; reflexivity|]. intros H; exfalso; apply H; reflexivity. }
  assert (DS6 : dstate10A m6 S (FB + 32) small h0 nbu0 cf0 d0 r0 js).
  { unfold dstate10A. exact (conj HEAD5 (conj HWF (conj NBU5 (conj NBUR (conj CF5 (conj CFL (conj MID5 (conj TT0 (conj L160 (conj L40 (conj NIU (conj CCRC (conj DR6 SAVE5))))))))))))). }
  assert (CEQ2 : @alloc_ceiling ACI = rt_sp0 RT Σ2 - STACK_WIN) by (rewrite SP2; exact CEQ1).
  pose proof (BZDC ACI Σ2 PMc (Z_to_bv 64 0x88f18) (Z_to_bv 64 P) gp tp y0 y1 y2 sp (Z_to_bv 64 P) (Z_to_bv 64 (FB + 32)) a1'' a2'' g3 g4 g5 g6 g7
                (Z_to_bv 64 FB) (Z_to_bv 64 SHD) (Z_to_bv 64 0) (Z_to_bv 64 FB) (Z_to_bv 64 zb) (Z_to_bv 64 ob) (Z_to_bv 64 small) (Z_to_bv 64 0) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 SHF)
                y3 y4 y5 y6 F5 fc5 m6 cx z OB h0 nbu0 cf0 d0 r0 js b0 zb zcap ob ocap lo) as BC.
  cbv zeta in BC. rewrite PU in BC.
  refine (cps_realizes bsegs _ _ T c7 (BC FDO MST eq_refl TP CEQ2 DS6 SMB S10 PLM6 eq_refl OBM LOB LIB6 DLIVE DPURE eq_refl eq_refl eq_refl eq_refl
            ltac:(rewrite FRS2, FRS1; cbn [length]; clear - FRB; unfold FRAMES_MAX in *; lia) ltac:(rewrite LVall; cbn [length]; clear - LIVB; unfold LIVE_MAX in *; lia)
            ltac:(rewrite CR2, CR1; unfold BZD_COST, DEC10_COST, mcost; cbn [cx b_len]; change (3600000 <=? 64512) with false; cbv iota; clear - CRED ZLE ZCR; lia)
            ART6 MI6 ST6 ltac:(rewrite SP2, SP1; exact LOW) ltac:(unfold RT_STACK, BZD_STACK, DEC_STACK; clear - PLO; lia) ltac:(clear - SPT PHI; lia) SPA') Hc7 _).
  clear Hc7 BC. intros c8 (Σ3 & bn & tt & l16 & l4 & Hq & LV3 & FRS3 & SP3 & CR3).
  destruct (ASTA_unpack RT Σ3 _ _ c8 Hq) as (ms8 & (m7 & q0 & q1 & q2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & q3 & q4 & q5 & q6 & F7 & fc7 & junkD & hF & dmF & b' & db & rest & POST) & Hc8). clear Hq.
  destruct (bzDecompress (dst_init junkD 0 (b_small cx)) (dstrm_init (map bv_unsigned z) (b_dlen cx))) as [[ret dF] sF] eqn:BZE.
  destruct POST as (-> & ART7 & MI7 & ST7 & LIB7 & DLIVE7 & DPURE7 & DBOK & HEAD7 & HSTRM & MID7 & TTE & L16E & L4E & SM7 & BWF & BS7 & BDST & BDLEN & BFREE & BOPQ & BAV & OBM7 & LDB & DBE & OUTL & RVR & STEP7).
  rewrite (ret_pc_even 0x88f18 ltac:(lia) eq_refl) in Hc8.
  unfold cx in BZE, DBOK, HEAD7, HSTRM, MID7, SM7, BS7, BDST, BDLEN, OBM7, LDB, OUTL, STEP7.
  cbn [b_s b_strm b_src b_len b_dst b_dlen b_small] in BZE, DBOK, HEAD7, HSTRM, MID7, SM7, BS7, BDST, BDLEN, OBM7, LDB, OUTL, STEP7.
  (* [comment removed for export] *)
  assert (LVsplit : rt_live RT Σ2 = [(S, 64144)] ++ rt_live RT Σ) by (rewrite LVall; reflexivity).
  assert (FRsub : forall e1', In e1' (rt_frames RT Σ) -> In e1' (rt_frames RT Σ2)) by (intros e1' H; rewrite FRS2, FRS1; right; exact H).
  assert (SPU2 : rt_sp0 RT Σ2 - STACK_WIN <= usp) by (rewrite SP2, SP1; clear - LOW PLO PHI; lia).
  pose proof (newlive_not_caller RT AF Σ2 m6 _ _ usp _ S 64144 ART6 LVsplit ltac:(in_list) FRsub SPU2) as NEWS.
  assert (LV3all : rt_live RT Σ3 = dblocks bn tt l16 l4 ++ (S, 64144) :: rt_live RT Σ) by (rewrite LV3, LVall; reflexivity).
  assert (SOK3 : sig_ok RT (rt_sp0 RT Σ) true 2 FB (rt_frames RT Σ) (rt_live RT Σ) Σ3).
  { split; [rewrite FRS3, FRS2; exact FRS1|]. split; [rewrite SP3, SP2; exact SP1|]. intros e1' He. rewrite LV3all. apply in_or_app. right. right. exact He. }
  assert (PR7 : PRESI usp (rt_frames RT Σ) (rt_live RT Σ) Wc m2 m7).
  { apply (pres_step_new G Σ2 _ m6 m7 SOK2 PR6 STEP7). per_interval.
    - right; right. apply NEWS. assumption.
    - left. right; left. match goal with HX : _ <= _ < _ |- _ => clear - HX; lia end.
    - right; left. unfold Wc. cbn [outside]. match goal with HX : _ <= _ < _ |- _ => clear - HX; lia end. }
  clear HEAD5 NBU5 CF5 MID5 SAVE5 DR6 DS6 SM SMB OBM PLM6 LIB6 SOKA6 ST6 DLIVE DPURE.
  xfer_rtf G SOK2 STEP7 m6 m7.
  (* [comment removed for export] *)
  pose proof (pres_final RT AF Σ lo P usp Wc m m1 m2 m7 ART0 LOW ltac:(clear - PLO; lia) ltac:(clear - PHI; lia) MU1k PRES2 PR7) as FP7.
  assert (AFW5 : app_fp [(dl, dl + 4)]) by (cbn [app_fp]; unfold SH_LO, SH_HI; split; [clear - FDHI' FDLO FDHI; lia| exact I]).
  destruct BWF as (LQ1' & LQ2' & _ & AVR & _ & _). rewrite BDLEN in AVR.
  set (avo := bs_av b') in *.
  pose proof SM7 as SM7c. rewrite strm_cells_eq in SM7c. fold avo in SM7c.
  eapply (l1_realizes RT AF Σ3 PMc _ T c8 MST Hc8).
  eapply (@B0_b2d_D5 ACI _ P FB SHF (FB + 32) lo ob dl zb zlen small 0 sp gp tp F7 fc7 LLO ltac:(clear - PLO; lia) DLR DLH eq_refl FSEG FBH SHD AD ltac:(clear - FDSEG FDLO; lia) DLFv m7 ret cap avo);
    [exact RVR| exact AVR| clear - CAPR; lia| exact SM7c| exact SL| exact DLC2| exact (kmem_inv_N _ _ MI7)| exact (shpW_of_acc b0segs _ m7 dl 4 (DLACC m7 FP7) AFW5 (proj1 DL47) (proj2 DL47))|].
  clear Hc8 SL DLC2 SM7c. intros m8 a1x a2x _ SL DLC2 NMI8 MU8 WM8. apply evt_done. intros c9 Hc9.
  unfold b2d_W5 in MU8.
  destruct (after_l1 AF G Σ3 _ m7 m8 SOK3 ART7 MI7 ST7 PR7 NMI8 MU8 WM8 ltac:(per_interval; right; right; right; unfold Wc; cbn [outside]; match goal with HX : _ <= _ < _ |- _ => clear - HX; lia end))
    as (ART8 & MI8 & ST8 & PR8 & _).
  clear ST7 LIB7. xfer_l1 m7 m8 MU8 WM8. clear NMI8 MU8 WM8.
  (* [comment removed for export] *)
  assert (SOKA8 : strm_okA RT Σ3 m8 (FB + 32)).
  { split; [exists FB, 2%nat; split; [rewrite FRS3; exact FBIN2| change (fs_size 2) with 256; clear; lia]|].
    split; [clear - F64; Z.div_mod_to_equations; lia|].
    replace (shad (FB + 32)) with (SHF + 4) by (destruct AX as [A8 ->]; unfold shad, SHB; clear - A8; Z.div_mod_to_equations; lia).
    exact (proj1 (n_rw_cells_bytes b0segs m8 _ _ SHz)). }
  assert (CEQ3 : @alloc_ceiling ACI = rt_sp0 RT Σ3 - STACK_WIN) by (rewrite SP3; exact CEQ2).
  destruct (dblocks_pos RT AF Σ3 m8 small bn tt l16 l4 _ ART8 LV3all DBOK) as (BN09 & BLKN & TTP & L16P & L4P).
  assert (SLIV3 : In (S, 64144) (rt_live RT Σ3)) by (rewrite LV3all; apply in_or_app; right; left; reflexivity).
  assert (DBIN : forall e, In e (dblocks bn tt l16 l4) -> In e (rt_live RT Σ3)) by (intros e He; rewrite LV3all; apply in_or_app; left; exact He).
  pose proof (ENDC ACI Σ3 PMc (Z_to_bv 64 (b2d_ra ret)) (Z_to_bv 64 P) gp tp q0 q1 q2 sp (Z_to_bv 64 P) (Z_to_bv 64 (FB + 32)) a1x a2x h3 h4 h5 h6 h7
                (Z_to_bv 64 FB) (Z_to_bv 64 (b2d_s3 SHD ret avo)) (Z_to_bv 64 ret) (Z_to_bv 64 FB) (Z_to_bv 64 zb) (Z_to_bv 64 ob) (Z_to_bv 64 small) (Z_to_bv 64 0) (Z_to_bv 64 (FB + 32))
                (Z_to_bv 64 SHF) q3 q4 q5 q6 F7 fc7 m8 (FB + 32) S bn tt l16 l4 hF dmF b' lo) as EC.
  cbv zeta in EC. rewrite PU in EC.
  refine (cps_realizes bsegs _ _ T c9 (EC FDO MST eq_refl TP CEQ3 HEAD7 HSTRM MID7 TTE L16E L4E SM7 BS7 BFREE BOPQ LQ1' LQ2' SOKA8 SLIV3 DBIN BN09 BLKN S16 TTP L16P L4P
            ART8 MI8 ST8 ltac:(rewrite SP3, SP2, SP1; exact LOW) ltac:(unfold RT_STACK; clear - PLO; lia) ltac:(clear - SPT PHI; lia) SPA') Hc9 _).
  clear Hc9 EC. intros c10 (Σ4 & Hq & LV4 & FRS4 & SP4 & CR4).
  destruct (ASTA_unpack RT Σ4 _ _ c10 Hq) as (ms10 & (m9 & k0 & k1 & k2 & j1 & j2 & j3 & j4 & j5 & j6 & j7 & k3 & k4 & k5 & k6 & F9 & fc9 & -> & ART9 & MI9 & ST9 & SM9 & STEP9) & Hc10). clear Hq.
  (* [comment removed for export] *)
  assert (LV4' : rt_live RT Σ4 = rt_live RT Σ).
  { rewrite LV4, LV3all. exact (live_removeD RT AF Σ3 m8 small bn tt l16 l4 S (rt_live RT Σ) ART8 LV3all DBOK POSN). }
  assert (SOK4 : sig_ok RT (rt_sp0 RT Σ) true 2 FB (rt_frames RT Σ) (rt_live RT Σ) Σ4).
  { split; [rewrite FRS4, FRS3, FRS2; exact FRS1|]. split; [rewrite SP4, SP3, SP2; exact SP1|]. intros e1' He. rewrite LV4'. exact He. }
  (* [comment removed for export] *)
  destruct (dblocks_virtual small bn tt l16 l4 S (FB + 32 + 48) (FB + 32 + 56) DBOK) as (p1 & n1 & p2 & n2 & IN1 & IN2 & WSUB).
  pose proof (pfp_weaken _ _ _ _ _ m8 m9 STEP9 WSUB) as STEP9'. clear STEP9 WSUB.
  assert (LV3split : rt_live RT Σ3 = (dblocks bn tt l16 l4 ++ [(S, 64144)]) ++ rt_live RT Σ) by (rewrite LV3all, <- app_assoc; reflexivity).
  assert (FRsub3 : forall e1', In e1' (rt_frames RT Σ) -> In e1' (rt_frames RT Σ3)) by (intros e1' H; rewrite FRS3; exact (FRsub _ H)).
  assert (SPU3 : rt_sp0 RT Σ3 - STACK_WIN <= usp) by (rewrite SP3; exact SPU2).
  pose proof (newlive_not_caller RT AF Σ3 m8 _ _ usp _ S 64144 ART8 LV3split ltac:(apply in_or_app; right; left; reflexivity) FRsub3 SPU3) as NEWS3.
  pose proof (newlive_not_caller RT AF Σ3 m8 _ _ usp _ p1 n1 ART8 LV3split IN1 FRsub3 SPU3) as NEWP1.
  pose proof (newlive_not_caller RT AF Σ3 m8 _ _ usp _ p2 n2 ART8 LV3split IN2 FRsub3 SPU3) as NEWP2.
  assert (FBIN3 : In (FB, 2%nat) (rt_frames RT Σ3)) by (rewrite FRS3; exact FBIN2).
  assert (FDIN3 : In (fD, kD) (rt_frames RT Σ3)) by (rewrite FRS3; exact FDIN2).
  destruct (newblk_facts RT AF Σ3 m8 _ _ p1 n1 FB 2%nat ART8 LV3split IN1 FBIN3) as (B1F & B1S & B1P & B1H & B1L). change (fs_size 2) with 256 in B1F, B1S. rewrite (proj1 SHFE), (proj2 SHFE) in B1S.
  destruct (newblk_facts RT AF Σ3 m8 _ _ p2 n2 FB 2%nat ART8 LV3split IN2 FBIN3) as (B2F & B2S & B2P & B2H & B2L). change (fs_size 2) with 256 in B2F, B2S. rewrite (proj1 SHFE), (proj2 SHFE) in B2S.
  destruct (newblk_facts RT AF Σ3 m8 _ _ p1 n1 fD kD ART8 LV3split IN1 FDIN3) as (B1D & _).
  destruct (newblk_facts RT AF Σ3 m8 _ _ p2 n2 fD kD ART8 LV3split IN2 FDIN3) as (B2D & _).
  assert (G1F : id (FB + 256 <= p1 \/ p1 + n1 <= FB)) by exact B1F.
  assert (G2F : id (FB + 256 <= p2 \/ p2 + n2 <= FB)) by exact B2F.
  assert (G1S : id (p1 + n1 <= SHF \/ SHF + 32 <= p1)) by exact B1S.
  assert (G2S : id (p2 + n2 <= SHF \/ SHF + 32 <= p2)) by exact B2S.
  assert (G1D : id (dl + 4 <= p1 \/ p1 + n1 <= dl)) by (unfold id; clear - B1D FDLO FDHI; lia).
  assert (G2D : id (dl + 4 <= p2 \/ p2 + n2 <= dl)) by (unfold id; clear - B2D FDLO FDHI; lia).
  assert (G1O : id (p1 + n1 <= ob \/ ob + ocap <= p1)) by exact (B1L _ _ OLIV).
  assert (G2O : id (p2 + n2 <= ob \/ ob + ocap <= p2)) by exact (B2L _ _ OLIV).
  assert (PP1 : p1 + n1 <= P) by (rewrite SP3, SP2, SP1 in B1H; clear - B1H LOW PLO; lia).
  assert (PP2 : p2 + n2 <= P) by (rewrite SP3, SP2, SP1 in B2H; clear - B2H LOW PLO; lia).
  clear B1F B2F B1S B2S B1D B2D B1L B2L B1H B2H.
  assert (PR9 : PRESI usp (rt_frames RT Σ) (rt_live RT Σ) Wc m2 m9).
  { apply (pres_step_new G Σ3 _ m8 m9 SOK3 PR8 STEP9'). per_interval.
    - right; right. apply NEWS3. assumption.
    - left. right; left. match goal with HX : _ <= _ < _ |- _ => clear - HX; lia end.
    - right; right. apply NEWP1. assumption.
    - right; right. apply NEWP2. assumption. }
  clear HEAD7 MID7 SM7 ST8 SOKA8.
  xfer_rtf G SOK3 STEP9' m8 m9.
  (* [comment removed for export] *)
  assert (L12 : length j12 = 12%nat) by (destruct SH12 as [[Hwf _] _]; cbn in Hwf; destruct Hwf as [HL _]; exact HL).
  pose proof (rw_cells_glue b0segs m9 SHF _ _ (SHF + 4) SHa SHz ltac:(cbn [cells_size csize Nat.add]; clear; lia)) as SH1.
  pose proof (rw_cells_glue b0segs m9 SHF _ _ (SHF + 14) SH1 SHb ltac:(cbn [app cells_size csize Nat.add]; clear; lia)) as SH2.
  pose proof (rw_cells_glue b0segs m9 SHF _ _ (SHF + 20) SH2 SH12 ltac:(cbn [app cells_size csize Nat.add]; clear; lia)) as SH3.
  cbn [app] in SH3. clear SHa SHz SHb SH12 SH1 SH2.
  match type of SH3 with rw_cells _ _ _ ?cs =>
    assert (SHU : rw_cells b0segs m9 SHF [CB 32 (cells_bytes cs)])
      by (apply (BzWalkArith3.rw_cells_recell b0segs m9 SHF cs); [exact SH3| cbn [cells_wf cell_wf cells_bytes cbytes app]; rewrite app_nil_r; cbn [length]; rewrite L12; split; [reflexivity| exact I]
                                                                  | cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity| cbn [cells_size csize Nat.add]; reflexivity]) end.
  clear SH3. apply u8arr_of_rw_cells in SHU.
  destruct (rw_cells_cutZ b0segs m9 FB _ 1%nat HD0) as [HDa _]. cbn [firstn cells_size csize Nat.add] in HDa. clear HD0.
  eapply (l1_realizes RT AF Σ4 PMc _ T c10 MST Hc10).
  eapply (B0_b2d_D6 _ gp tp F9 fc9 SHD m9 ret avo).
  eapply (@B0_b2d_E1 ACI _ P FB SHF sp gp tp F9 fc9 FSEG FBH GSELF m9 _ _);
    [| exact SHU| exact HDa| exact (kmem_inv_N _ _ MI9)|]; [cbn [cells_bytes cbytes app]; rewrite app_nil_r; cbn [length]; rewrite L12; reflexivity|].
  clear Hc10 SHU HDa. intros m10 a0x SHF5 HDm NMI10 MU10 WM10. apply evt_done. intros c11 Hc11.
  unfold b2d_WE1 in MU10.
  destruct (after_l1 AF G Σ4 _ m9 m10 SOK4 ART9 MI9 ST9 PR9 NMI10 MU10 WM10 ltac:(fp_ours PHI)) as (ART10 & MI10 & ST10 & PR10 & _).
  clear ST9. xfer_l1 m9 m10 MU10 WM10. clear NMI10 MU10 WM10 SHF5 HDm SM9.
  (* [comment removed for export] *)
  destruct (release_inline2 AF G (mi := m2) Σ4 m10 eq_refl SOK4 ART10) as (Σ5 & fl & FLC & FLP & FL0 & FLW & FLD & REL).
  replace (FB + 256 - 8) with (FB + 248) in FLP by (clear; lia).
  eapply (l1_realizes RT AF Σ4 PMc _ T c11 MST Hc11).
  eapply (@B0_b2d_E1b ACI _ FB gp tp F9 fc9 fl m10); [exact (ro_C8_KN m10 _ _ FLP)|].
  eapply (B0_b2d_E2 _ gp tp F9 fc9 fl m10 (Z_to_bv 8 1)); [exact FLC| exact (kmem_inv_N _ _ MI10)|].
  clear Hc11. intros m11 FLC2 NMI11 MU11 WM11. apply evt_done. intros c12 Hc12.
  destruct (REL m11 MU11 WM11 FLC2 MI10 NMI11 ST10 PR10) as (ART11 & FRS5 & LV5 & SP5 & CR5 & AL5 & AM5 & MI11 & ST11 & PR11).
  clear ST10. xfer_fl G SOK4 FLD m10 m11 MU11 WM11.
  pose proof (ASTA_switch RT Σ4 Σ5 PMc _ c12 Hc12 AL5 AM5) as Hc12'. clear Hc12.
  eapply (l1_realizes RT AF Σ5 PMc _ T c12 MST Hc12').
  eapply (@B0_b2d_E3 ACI _ P lo sp gp tp F9 fc9 ltac:(clear - PLO; lia) PCASE m11); [exact SL| exact GAP| exact SAV| exact ST11|].
  clear Hc12'. intros STu. apply evt_done. intros c13 Hc13.
  (* [comment removed for export] *)
  pose proof (pres_final RT AF Σ lo P usp Wc m m1 m2 m11 ART0 LOW ltac:(clear - PLO; lia) ltac:(clear - PHI; lia) MU1k PRES2 PR11) as FPE.
  apply Hk. exists Σ5, (b2d_rc ret avo), (b2d_dlv ret cap avo).
  split; [| split; [rewrite LV5; exact LV4'| split; [exact FRS5| split; [exact SP5|]]]].
  2:{ rewrite CR5, CR4. unfold HD.B2BD_COST. unfold BZD_COST, DEC10_COST, mcost in CR3. cbn [cx b_len] in CR3. change (3600000 <=? 64512) with false in CR3. cbv iota in CR3.
      clear - CR3 CR2 CR1 ZLE ZCR. lia. }
  eapply ASTA_conseq; [exact Hc13|]. intros ms <-. exists m11.
  split. { unfold ret_st. exists k0, k1, k2, j1, j2, j3, j4, j5, j6, j7, k3, k4, k5, k6, F9, fc9. reflexivity. }
  split. { split; [exact ART11| split; [exact MI11| exact STu]]. }
  split. { exact FPE. }
  split. { exact (n2k_C4 m11 dl _ DLC2). }
  split. { apply (lib_of_pfp _ _ _ _ m m11 LIB FPE). intros x Hx. unfold Wc. cbn [outside]. split; [clear - Hx OBI CAPO CAPR; lia|]. split; [clear - Hx FDSEG FDLO; lia| exact I]. }
  unfold b2d_rc, b2d_dlv. destruct (Z.eqb_spec ret 4) as [R4|N4].
  2:{ right. destruct (Z.eqb_spec ret 0) as [R0|N0]; [destruct (avo =? 0); clear; lia| clear - RVR N4 N0; lia]. }
  left. split; [reflexivity|]. subst ret.
  exists (map (Z_to_bv 8) (s_output sF)).
  split. { exists junkD. unfold buffToBuffDecompress. cbv zeta. fold small. rewrite BZE. cbv beta iota zeta. change (4 =? BZ_OK) with false. change (4 =? BZ_STREAM_END) with true. cbv iota.
           split; reflexivity. }
  split. { rewrite length_map, OUTL, BAV. reflexivity. }
  split. { clear - AVR. lia. }
  rewrite DBE in OBM7.
  exact (proj1 (proj1 (KMem.bytes_at_app bsegs m11 ob _ _) (proj1 (n_u8arr_bytes b0segs m11 ob _ OBM7)))).
Qed.
End B2BD.

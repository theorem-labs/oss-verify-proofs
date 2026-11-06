(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_defs D_kit I_read RT_liveprim L_libA. Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_read.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_liveprim.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require L_hkit L_harn_defs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require R_unwind_chain. Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_unwind_chain.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require Import L2Kit L2Act L2Stmt L2StmtS B0_sessK B0_b2bc_K.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCBlock BzCDriver BzArrD CmpMem CmpCut CmpSess CmpSess2 CmpSessB CmpFsKit0 AsanKit AsanCut AsanCutB0 B0_b2c_cbV B0_b2c_hcV B0_b2c_wrV B0_b2c_wrE B0_b2c_wrW CmpLaws CmpLawsB BzRT1 BzRT.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCarve BzCLemmasFs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCEmit BzWalkArith3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).



Section B2BC.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis SMAL : stack_malloc_contract RT 2.
Hypothesis MSET : memset_icontract RT e_asan_memset.
Hypothesis INITC : forall (BZP : BzParams) (AC : ACeil), @bzCompressInit_contract BZP AC RT.
Hypothesis BZCC : forall (BZP : BzParams) (AC : ACeil), @bzCompress_contract BZP AC RT (@HCXB BZP) cb_facts.
Hypothesis ENDC : forall (BZP : BzParams) (AC : ACeil), @bzCompressEnd_contract BZP AC RT.
(* [comment removed for export] *)
Hypothesis ACL : forall Σ (m : mem), ART RT Σ m -> @alloc_ceiling (aceil_of_sp (rt_sp0 RT Σ)) = rt_sp0 RT Σ - STACK_WIN.

(* [comment removed for export] *)
Ltac fp_ours PHI := per_interval; match goal with HX : _ <= _ < _ |- _ => clear - HX PHI; lia end.

Ltac in_list := cbn [app In]; repeat (first [left; reflexivity | right]).

Theorem b2bc_glue : b2bc_cps_pos RT OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A enc_okL.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m zb dl d bs junk lo len
         FDO MST A0E A1E A2E A3E A4E A5E A6E TP RAE LEN D0 BYS PIN ZLIV ZBJ DLF DLC DL8 DLSH POSN LIVB FRB CRED HREC LIB ART0 MI0 ST0 LOW LOR SPT SPA SPS.
  intros T c Hc Hk. subst a0 a1 a2 a3 a4 a5 a6 ra. unfold entry_st in Hc.
  set (usp := bv_unsigned sp) in *.
  set (nZ := HK.nZ_of len) in *.
  pose (BZP := b2bP len). pose (ACI := aceil_of_sp (rt_sp0 RT Σ)).
  pose proof (ACL Σ m ART0) as CEQ. change (@alloc_ceiling ACI = rt_sp0 RT Σ - STACK_WIN) in CEQ.
  (* [comment removed for export] *)
  assert (LEN0 : 0 <= len) by (unfold len; lia).
  assert (NZR : len + 600 <= nZ < 2^27) by (unfold nZ, HK.nZ_of; clear - LEN LEN0; Z.div_mod_to_equations; lia).
  pose proof (@alloc_ceiling_range ACI) as ACR. pose proof (@p_bs_rng BZP) as BZbs. pose proof (@p_wf_rng BZP) as BZwf.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. fold usp in SPR.
  unfold HD.B2B_STACK, OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_libiface.TwinB__.FUZZ_STACK in LOR. unfold HD.B2B_LIVE in LIVB. unfold HD.B2B_FRAMES in FRB. unfold HD.B2BC_COST in CRED.
  set (P := 32 * ((usp - 160) / 32)).
  assert (PCASE : P = usp - 160 \/ P = usp - 176) by (subst P; clear - SPA; Z.div_mod_to_equations; lia).
  assert (PF : lo + 200000 <= P /\ P + 160 <= usp /\ usp <= P + 176 /\ P mod 16 = 0) by (subst P; clear - SPA LOR; Z.div_mod_to_equations; lia).
  destruct PF as (PLO & PHI & PHI' & SPA').
  assert (USPQ : exists q, usp = 16 * q) by (exists (usp / 16); clear - SPA; Z.div_mod_to_equations; lia).
  assert (PQ : exists q, P = 32 * q) by (exists ((usp - 160) / 32); reflexivity).
  assert (LLO : @CEILv ACI <= lo) by (unfold CEILv; rewrite CEQ; exact LOW).
  (* [comment removed for export] *)
  pose proof (af_live_range RT AF Σ m _ _ ART0 ZLIV) as (ZB0 & ZBH & ZBI). unfold SEGTOP_A in ZBI.
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
  eapply (@B0_b2c_W1 BZP ACI _ P lo zb dl d len (HK.wf_of len) sp gp tp F fc LLO ltac:(clear - PLO; lia) PCASE USPQ PQ DLR DLH m);
    [exact ST0| exact (kmem_inv_N _ _ MI0)| exact AC| exact AU|].
  clear Hc AC AU. intros m1 v0 v8 v32 v40 v48 a1' a2' SL GAP SAV ST1 NMI1 MU1 WM1. apply evt_done. intros c1 Hc1.
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
  rewrite (KMState.ret_pc_even 0x888b8 ltac:(lia) eq_refl) in Hc2.
  (* [comment removed for export] *)
  set (Wc := [(zb, zb + nZ); (dl, dl + 4)]).
  assert (DCL : forall x, dl <= x < dl + 4 -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x).
  { intros x Hx. right; right; right; left. exists fD, kD. split; [exact FDIN| clear - Hx FDLO FDHI; lia]. }
  assert (WCL : forall x, ~ outside Wc x -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x).
  { intros x Hx. unfold Wc in Hx. cbn [outside] in Hx.
    assert (C : (zb <= x < zb + nZ) \/ (dl <= x < dl + 4)) by (clear - Hx; lia).
    destruct C as [C|C]; [right; right; left; exists zb, nZ; split; [exact ZLIV| exact C]| exact (DCL x C)]. }
  set (SHF := FB / 8 + 2147450880). change (shad FB) with SHF in WRS, ZSH.
  destruct (act_setup RT AF Σ Σ1 m m2 2 FB SHF 256 32 lo P usp Wc eq_refl eq_refl eq_refl eq_refl ART0 ART2 FRS1 LV1 SP1 LOW
              ltac:(unfold RT_STACK; clear - PLO; lia) ltac:(clear - PHI; lia) SPT SPA' WCL) as (G & SOK & _ & FSEG & FHI & SHR0 & SHR1 & GSELF & GLV).
  pose proof (ag_ax G) as AX. pose proof (ag_gfr G) as (_ & FR1). unfold SEGTOP_A in FSEG.
  clearbody SHF.
  assert (STEP2 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) P [] m1 m2) by exact (pfp_of_pres _ _ _ [] m1 m2 PRES2).
  clear ST1. xfer_rt G I STEP2 WM2 m1 m2.
  (* [comment removed for export] *)
  assert (AG02 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> m2 a = m a).
  { intros a Ha. rewrite (PRES2 a (aclient_mono _ _ usp _ _ P _ Ha (fun e H => H) (fun e H => H) ltac:(clear - PHI; lia))). apply MU1k. cbn [KFrame.outside]. split; [| exact I].
    destruct (aclient_split RT AF Σ m usp (bv_unsigned a) ART0 Ha) as [EE|EE]; clear - EE LOW PLO PHI; lia. }
  assert (DLC2 : rw_cells b0segs m2 dl [C4 (Z_to_bv 64 nZ)]).
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
  pose proof (strm_carve b0segs m2 (FB + 32) jb SMJ) as SM. clear SMJ.
  pose proof (n_rw_CB_of_bytes' m2 SHF (repeat (Z_to_bv 8 0) 20) ZSH ltac:(rewrite repeat_length; apply (wr_at_sub bsegs m2 SHF 32); [exact WRS| clear; lia| clear; lia| clear; lia])) as SH20.
  rewrite repeat_length in SH20.
  destruct (n_wr_at_rw_CB m2 (SHF + 20) 12 (wr_at_sub bsegs m2 SHF 32 (SHF + 20) 12 WRS ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (j12 & SH12).
  clear WRF WRS ZSH.
  (* [comment removed for export] *)
  assert (FBH : FB + 256 <= @CEILv ACI) by (unfold CEILv; rewrite CEQ; exact FR1).
  assert (DST : 0 < zb < 18446744073709551616) by (clear - ZB0 ZBH NZR ACR CEQ; lia).
  assert (SRC : 0 < d < 18446744073709551616) by (clear - D0; lia).
  assert (WF0 : 0 <= HK.wf_of len <= 250) by (unfold HK.wf_of; clear; pose proof (Z.mod_pos_bound len 251 ltac:(lia)); lia).
  assert (NMI2 : mem_inv b0segs m2) by exact (kmem_inv_N _ _ MI2).
  eapply (l1_realizes RT AF Σ1 PMc _ T c2 MST Hc2).
  eapply (@B0_b2c_W2 BZP ACI _ P FB SHF (FB + 32) lo zb dl d len (HK.wf_of len) sp gp tp F2 fc2 LLO ltac:(clear - PLO; lia) WF0 eq_refl DST DLR DLH SRC AX eq_refl FSEG FBH
            ltac:(unfold SH_HI; exact SHR1) GSELF m2 v0 v8 v32 v40 v48 _ _ _ _);
    [exact SL| exact HD0| exact SH20| exact NMI2|].
  clear Hc2 SL HD0 SH20. intros m3 a3' SL HD0 SH20 NMI3 MU3 WM3. apply evt_done. intros c3 Hc3.
  unfold b2c_W2 in MU3.
  destruct (after_l1 AF G Σ1 _ m2 m3 SOK ART2 MI2 ST2 (presi_refl _ _ _ _ m2) NMI3 MU3 WM3 ltac:(fp_ours PHI)) as (ART3 & MI3 & ST3 & PR3 & _).
  assert (GSELF' : id (FB + 256 <= SHF \/ SHF + 32 <= FB)) by exact GSELF.
  assert (PFB : FB + 256 <= P) by (clear - FR1 LOW PLO; lia).
  assert (PSH : SHF + 32 <= P) by (clear - SHR1 LLO ACR PLO; unfold CEILv in LLO; lia).
  clear ST2. xfer_l1 m2 m3 MU3 WM3. clear NMI3 MU3 WM3 NMI2.
  (* [comment removed for export] *)
  unfold b2c_shadow in SH20.
  destruct (rw_cells_cutZ b0segs m3 SHF _ 4%nat SH20) as [SHa SHr]. cbn [firstn skipn cells_size csize Nat.add] in SHa, SHr. change (Z.of_nat 4) with 4 in SHr.
  destruct (rw_cells_cutZ b0segs m3 (SHF + 4) _ 10%nat SHr) as [SHz SHb]. cbn [firstn skipn cells_size csize Nat.add] in SHz, SHb.
  replace (SHF + 4 + Z.of_nat 10) with (SHF + 14) in SHb by (clear; lia). clear SH20 SHr.
  unfold STRMC in SM.
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
  rewrite (KMState.ret_pc_even 0x889c0 ltac:(lia) eq_refl) in Hc4.
  pose proof (pres_step_ours G Σ1 _ _ m3 m4 SOK PR3 STEP4 ltac:(right; left; clear; lia)) as PR4.
  clear ST3. xfer_rt G SOK STEP4 WM4 m3 m4.
  pose proof (n_rw_CB_of_bytes' m4 (FB + 88) (repeat z8 (Z.to_nat 24)) BY4 ltac:(rewrite repeat_length; exact WRT)) as Z24. rewrite repeat_length in Z24.
  assert (SMt : rw_cells b0segs m4 (FB + 88) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
  { eapply (carve_cb b0segs); [exact Z24| cbn [cells_wf cell_wf]; repeat split| reflexivity| reflexivity]. }
  pose proof (rw_cells_glue b0segs m4 (FB + 32) _ _ (FB + 88) SMa SMt ltac:(cbn [cells_size csize Nat.add]; clear; lia)) as SM. cbn [app] in SM.
  clear SMa SMt Z24 BY4 WRT STEP4 WM4.
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ1 PMc _ T c4 MST Hc4). eapply B0_b2c_W3. apply evt_done. clear Hc4. intros c5 Hc5.
  assert (CEQ1 : @alloc_ceiling ACI = rt_sp0 RT Σ1 - STACK_WIN) by (rewrite SP1; exact CEQ).
  assert (OWC : forall x, usp <= x -> outside Wc x).
  { intros x Hx. unfold Wc. cbn [outside]. split; [clear - Hx ZBH LOW PLO PHI; lia|]. split; [clear - Hx DLH LLO PLO PHI; unfold CEILv in *; lia| exact I]. }
  (* [comment removed for export] *)
  pose proof (pres_final RT AF Σ lo P usp Wc m m1 m2 m4 ART0 LOW ltac:(clear - PLO; lia) ltac:(clear - PHI; lia) MU1k PRES2 PR4) as FP4.
  assert (UW4 : uw_chain USTACK_TOP m4 P usp [0x814a4; 0x81200]).
  { cbn [uw_chain]. split; [clear - PHI; lia|]. split; [clear - SPA; Z.div_mod_to_equations; lia|]. split; [clear - SPT; lia|].
    exists (bv_unsigned s0). split; [pose proof (bv_unsigned_in_range 64 s0) as R; unfold bv_modulus in R; cbn in R; exact R|]. split.
    - unfold HSAVED in SAV. destruct (rw_cells_cutZ b0segs m4 _ _ 11%nat SAV) as [_ REC]. cbn [firstn skipn cells_size csize Nat.add] in REC.
      replace (usp + -104 + Z.of_nat 88) with (usp + -16) in REC by (clear; lia). rewrite Z_to_bv_bv_unsigned. exact (n2k_C8C8 m4 _ _ _ REC).
    - apply (uw_chain_agree _ m m4 _ _ _ HREC). intros a Ha. apply FP4; [left; exact Ha| apply OWC; clear - Ha; lia]. }
  assert (SOKA4 : strm_okA RT Σ1 m4 (FB + 32)).
  { split; [exists FB, 2%nat; split; [rewrite FRS1; left; reflexivity| change (fs_size 2) with 256; clear; lia]|].
    split; [clear - F64; Z.div_mod_to_equations; lia|].
    replace (shad (FB + 32)) with (SHF + 4) by (destruct AX as [A8 ->]; unfold shad, SHB; clear - A8; Z.div_mod_to_equations; lia).
    exact (proj1 (n_rw_cells_bytes b0segs m4 _ _ SHz)). }
  pose proof (INITC BZP ACI Σ1 PMc (Z_to_bv 64 0x889d4) (Z_to_bv 64 P) gp tp x0 x1 x2 sp (Z_to_bv 64 P) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 0) (Z_to_bv 64 WORKFACTOR) f4 f5 f6 f7 (Z_to_bv 64 FB) (Z_to_bv 64 2147450880) (Z_to_bv 64 (-2)) (Z_to_bv 64 SHF) (Z_to_bv 64 FB) (Z_to_bv 64 zb) (Z_to_bv 64 WORKFACTOR) (Z_to_bv 64 0) (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 (FB + 32)) x3 x4 x5 x6 F4 fc4 m4 (FB + 32) (jw8 jb 0) (jw4 jb 8) (jw4 jb 12) (jw4 jb 16) (jw4 jb 20) (jw8 jb 24) (jw4 jb 32) (jw4 jb 36) (jw4 jb 40) (jw4 jb 44) (jw8 jb 48) lo) as IC.
  cbv zeta in IC. rewrite PU in IC.
  assert (ICOST : @INIT_COST BZP <= 14973720).
  { unfold INIT_COST, ESTATE_SIZE, FTAB_WORDS, mcost. change (4 * 65537) with 262148.
    destruct (Z.leb_spec 55768 64512); [| exfalso; lia]. destruct (Z.leb_spec ARR1_SIZE 64512); [exfalso; clear - H0 BZbs; lia|].
    destruct (Z.leb_spec ARR2_SIZE 64512); [exfalso; clear - H1 BZbs; lia|]. destruct (Z.leb_spec 262148 64512); [exfalso; lia|]. clear - BZbs. lia. }
  refine (cps_realizes bsegs _ _ T c5 (IC FDO MST eq_refl eq_refl eq_refl eq_refl TP CEQ1 SM SOKA4 UW4 ltac:(rewrite LV1; clear - LIVB; unfold LIVE_MAX in *; lia)
            ltac:(rewrite CR1; clear - ICOST CRED; lia) ART4 MI4 ST4 ltac:(rewrite SP1; exact LOW) ltac:(unfold RT_STACK; clear - PLO; lia)
            ltac:(clear - SPT PHI; lia) SPA') Hc5 _).
  clear Hc5 IC. intros c6 (Σ2 & E & r1 & r2 & r3 & Hq & LV2 & FRS2 & SP2 & CR2).
  destruct (ASTA_unpack RT Σ2 _ _ c6 Hq) as (ms6 & (m5 & y0 & y1 & y2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & y3 & y4 & y5 & y6 & F5 & fc5 & J & ar1 & ar2 & ft & inU & uns & mtf & sel & selM
                                                  & len' & code & rfreq & lenp & bsB & bsL & nIn & oP & nM & POST) & Hc6). clear Hq.
  cbv zeta in POST. destruct POST as (-> & ART5 & MI5 & ST5 & CX & SEP & IMG & EM & AM & ZB1 & ZB2 & FTW & SM5 & STEP5).
  rewrite (ret_pc_even 0x889d4 ltac:(lia) eq_refl) in Hc6.
  (* [comment removed for export] *)
  set (cx := CC E r1 r2 r3 (FB + 32 - BZF_STRM) 0 J []) in *.
  set (e0 := est_init ar1 ar2 ft inU uns mtf sel selM len' code rfreq lenp bsB bsL nIn oP nM) in *.
  assert (LVall : rt_live RT Σ2 = (r3, 262148) :: (r2, ARR2_SIZE) :: (r1, ARR1_SIZE) :: (E, 55768) :: rt_live RT Σ) by (rewrite LV2, LV1; reflexivity).
  assert (SOK2 : sig_ok RT (rt_sp0 RT Σ) true 2 FB (rt_frames RT Σ) (rt_live RT Σ) Σ2).
  { split; [rewrite FRS2; exact FRS1|]. split; [rewrite SP2; exact SP1|]. intros e1' He. rewrite LVall. right; right; right; right. exact He. }
  pose proof (pres_step_ours G Σ1 _ _ m4 m5 SOK PR4 STEP5 ltac:(right; left; clear; lia)) as PR5.
  clear ST4 SM. xfer_rtf G SOK STEP5 m4 m5.
  (* [comment removed for export] *)
  set (SHD := dl / 8 + 2147450880).
  assert (AD : sanchor dl SHD) by (apply sanchor_intro; exact DL8).
  pose proof (af_fshadow_apart RT AF Σ m fD kD ART0 FDIN) as (FDSL & FDSF).
  assert (SHDR : shad fD <= shad dl /\ shad dl + 1 <= shad (fD + fs_size kD)) by (unfold shad, SHB; clear - FDLO FDHI; Z.div_mod_to_equations; lia).
  assert (DSHCL : forall x, shad dl <= x < shad dl + 1 -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x /\ outside Wc x).
  { intros x Hx. split; [right; right; right; right; exists fD, kD; split; [exact FDIN| clear - Hx SHDR; lia]|].
    unfold Wc. cbn [outside]. split; [destruct (FDSL _ _ ZLIV) as [D|D]; clear - D Hx SHDR; lia|]. split; [destruct (FDSF _ _ FDIN) as [D|D]; clear - D Hx SHDR FDLO FDHI; lia| exact I]. }
  assert (DLSHb : KMem.bytes_at bsegs m (shad dl) [Z_to_bv 8 4]) by exact (proj2 DLSH).
  assert (DLACC : forall mk, rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp Wc m mk -> acc bsegs mk dl 4).
  { intros mk FPk. apply (acc_dl mk dl DL8 ltac:(clear - DLR; lia)). apply (bytes_at_agree bsegs m mk _ _ DLSHb). intros a Ha. cbn [length] in Ha.
    destruct (DSHCL (bv_unsigned a) ltac:(clear - Ha; lia)) as [C O]. exact (FPk a C O). }
  pose proof (pres_final RT AF Σ lo P usp Wc m m1 m2 m5 ART0 LOW ltac:(clear - PLO; lia) ltac:(clear - PHI; lia) MU1k PRES2 PR5) as FP5.
  assert (AFW4 : app_fp [(FB + 32, FB + 32 + 36)]) by (cbn [app_fp]; unfold SH_LO, SH_HI; split; [clear - FHI; lia| exact I]).
  assert (DL47 : 0 <= dl /\ dl + 4 <= 2^47) by (clear - DLR DLH ACR; unfold CEILv in DLH; lia).
  assert (DLFv : apartv dl 4 FB 256) by (unfold apartv; pose proof DLFB' as D; unfold id in D; clear - D; lia).
  eapply (l1_realizes RT AF Σ2 PMc _ T c6 MST Hc6).
  eapply (@B0_b2c_W4 BZP ACI _ P FB SHF (FB + 32) lo zb dl d len sp gp tp F5 fc5 LLO ltac:(clear - PLO; lia) DLR DLH eq_refl FSEG FBH SHD AD ltac:(clear - FDSEG FDLO; lia) DLFv m5 nZ);
    [clear - NZR; lia| exact SM5| exact SL| exact DLC2| exact (kmem_inv_N _ _ MI5)| exact (shpW_of_acc b0segs _ m5 dl 4 (DLACC m5 FP5) AFW4 (proj1 DL47) (proj2 DL47))|].
  clear Hc6 SM5 SL DLC2. intros m6 a2'' a3'' SM SL DLC2 NMI6 MU6 WM6. apply evt_done. intros c7 Hc7.
  unfold b2c_W4 in MU6.
  destruct (after_l1 AF G Σ2 _ m5 m6 SOK2 ART5 MI5 ST5 PR5 NMI6 MU6 WM6 ltac:(fp_ours PHI)) as (ART6 & MI6 & ST6 & PR6 & _).
  (* [comment removed for export] *)
  pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'. cbn [cx c_E c_A1 c_A2 c_FT c_J] in CX'.
  destruct CX' as (RE & RE' & RA1 & RA1' & RA2 & RA2' & RFT & RFT' & _ & _ & _ & _ & ME16 & MA1 & MA2 & MFT & _ & _ & LJ & _).
  unfold ESTATE_SIZE, FTAB_WORDS, CEIL in RE', RA1', RA2', RFT', LJ. change (4 * 65537) with 262148 in RFT'.
  assert (ELIV : In (E, 55768) (rt_live RT Σ2)) by (rewrite LVall; in_list).
  assert (R1LIV : In (r1, ARR1_SIZE) (rt_live RT Σ2)) by (rewrite LVall; in_list).
  assert (R2LIV : In (r2, ARR2_SIZE) (rt_live RT Σ2)) by (rewrite LVall; in_list).
  assert (R3LIV : In (r3, 262148) (rt_live RT Σ2)) by (rewrite LVall; in_list).
  assert (ZLIV2 : In (zb, nZ) (rt_live RT Σ2)) by (rewrite LVall; right; right; right; right; exact ZLIV).
  assert (FBIN2 : In (FB, 2%nat) (rt_frames RT Σ2)) by (rewrite FRS2, FRS1; left; reflexivity).
  assert (FDIN2 : In (fD, kD) (rt_frames RT Σ2)) by (rewrite FRS2, FRS1; right; exact FDIN).
  pose proof (af_frames_range RT AF Σ2 m5 FB 2%nat ART5 FBIN2) as (_ & _ & _ & FBL2). change (fs_size 2) with 256 in FBL2.
  pose proof (af_fshadow_apart RT AF Σ2 m5 FB 2%nat ART5 FBIN2) as (FBS2 & _). change (fs_size 2) with 256 in FBS2. rewrite (proj1 SHFE), (proj2 SHFE) in FBS2.
  pose proof (af_frames_range RT AF Σ2 m5 fD kD ART5 FDIN2) as (_ & _ & _ & FDL2).
  assert (GFE : id (FB + 256 <= E \/ E + 55768 <= FB)) by exact (FBL2 _ _ ELIV).
  assert (GF1 : id (FB + 256 <= r1 \/ r1 + ARR1_SIZE <= FB)) by exact (FBL2 _ _ R1LIV).
  assert (GF2 : id (FB + 256 <= r2 \/ r2 + ARR2_SIZE <= FB)) by exact (FBL2 _ _ R2LIV).
  assert (GF3 : id (FB + 256 <= r3 \/ r3 + 262148 <= FB)) by exact (FBL2 _ _ R3LIV).
  assert (GFZ : id (FB + 256 <= zb \/ zb + nZ <= FB)) by exact (FBL2 _ _ ZLIV2).
  assert (GSE : id (E + 55768 <= SHF \/ SHF + 32 <= E)) by exact (FBS2 _ _ ELIV).
  assert (GS1 : id (r1 + ARR1_SIZE <= SHF \/ SHF + 32 <= r1)) by exact (FBS2 _ _ R1LIV).
  assert (GS2 : id (r2 + ARR2_SIZE <= SHF \/ SHF + 32 <= r2)) by exact (FBS2 _ _ R2LIV).
  assert (GS3 : id (r3 + 262148 <= SHF \/ SHF + 32 <= r3)) by exact (FBS2 _ _ R3LIV).
  assert (GSZ : id (zb + nZ <= SHF \/ SHF + 32 <= zb)) by exact (FBS2 _ _ ZLIV2).
  assert (GDE : id (dl + 4 <= E \/ E + 55768 <= dl)) by (unfold id; destruct (FDL2 _ _ ELIV) as [D|D]; clear - D FDLO FDHI; lia).
  assert (GD1 : id (dl + 4 <= r1 \/ r1 + ARR1_SIZE <= dl)) by (unfold id; destruct (FDL2 _ _ R1LIV) as [D|D]; clear - D FDLO FDHI; lia).
  assert (GD2 : id (dl + 4 <= r2 \/ r2 + ARR2_SIZE <= dl)) by (unfold id; destruct (FDL2 _ _ R2LIV) as [D|D]; clear - D FDLO FDHI; lia).
  assert (GD3 : id (dl + 4 <= r3 \/ r3 + 262148 <= dl)) by (unfold id; destruct (FDL2 _ _ R3LIV) as [D|D]; clear - D FDLO FDHI; lia).
  assert (GDZ : id (dl + 4 <= zb \/ zb + nZ <= dl)) by (unfold id; destruct (FDL2 _ _ ZLIV2) as [D|D]; clear - D FDLO FDHI; lia).
  clear FBL2 FBS2 FDL2.
  pose proof (ck_intro E (CLive E 55768)) as KE. pose proof (ck_intro r1 (CLive r1 ARR1_SIZE)) as KR1. pose proof (ck_intro r2 (CLive r2 ARR2_SIZE)) as KR2.
  pose proof (ck_intro r3 (CLive r3 262148)) as KR3. pose proof (ck_intro zb (CLive zb nZ)) as KZB.
  destruct EM as (EH1 & INU & UNS & EH2 & MTF & SEL & SLM & LEN' & COD & RFQ & LNP). cbn [cx c_E c_J] in EH1, INU, UNS, EH2, MTF, SEL, SLM, LEN', COD, RFQ, LNP.
  destruct AM as (AR1 & AR2 & FTB). unfold FTAB_WORDS in FTB. cbn [cx c_A1 c_A2 c_FT] in AR1, AR2, FTB.
  clear ST5. xfer_l1 m5 m6 MU6 WM6. clear NMI6 MU6 WM6.
  (* [comment removed for export] *)
  set (pay := map bv_unsigned bs). set (z0 := z_b2b pay nZ).
  assert (LPAY : Z.of_nat (length pay) = len) by (unfold pay; rewrite length_map; reflexivity).
  assert (BYP : Forall (fun c0 => 0 <= c0 < 256) pay).
  { unfold pay. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (b & <- & _). pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. }
  pose proof (@HCXB_init BZP cx nZ (Z_to_bv 64 0) pay ar1 ar2 ft inU uns mtf sel selM len' code rfreq lenp bsB bsL nIn oP nM ZB1 ZB2 FTW
                ltac:(clear - NZR LEN0; lia) ltac:(rewrite LPAY; exact LEN) BYP) as HX. cbv zeta in HX. fold e0 z0 in HX.
  pose proof (@hc_lawsB_intro BZP BzCEmit.cbm_ok cb_facts (fun g e _ F => F)) as LAWS.
  pose proof (pres_final RT AF Σ lo P usp Wc m m1 m2 m6 ART0 LOW ltac:(clear - PLO; lia) ltac:(clear - PHI; lia) MU1k PRES2 PR6) as FP6.
  (* [comment removed for export] *)
  assert (PAYCL : forall x, d <= x < d + len -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x /\ outside Wc x).
  { intros x Hx. destruct PIN as [(p & n & PI & PL & PH & PNE)|PE]; [| exfalso; subst bs; unfold len in Hx; cbn [length Z.of_nat] in Hx; clear - Hx; lia].
    split; [right; right; left; exists p, n; split; [exact PI| clear - Hx PL PH; lia]|].
    unfold Wc. cbn [outside]. pose proof (live_disj_in RT AF Σ m p n zb nZ ART0 PI ZLIV PNE) as D1. pose proof (FDL p n PI) as D2.
    split; [clear - D1 Hx PL PH; lia|]. split; [clear - D2 Hx PL PH FDLO FDHI; lia| exact I]. }
  assert (PLM6 : u8ro b0segs m6 d bs).
  { apply (bytes_at_agree bsegs m m6 _ _ BYS). intros a Ha. destruct (PAYCL (bv_unsigned a) Ha) as [C O]. exact (FP6 a C O). }
  assert (LIB6 : OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.LIB_A m6).
  { apply (lib_of_pfp _ _ _ _ m m6 LIB FP6). intros x Hx. unfold Wc. cbn [outside]. split; [clear - Hx ZBI NZR; lia|]. split; [clear - Hx FDSEG FDLO; lia| exact I]. }
  (* [comment removed for export] *)
  destruct (af_acc_live RT AF Σ2 m6 zb nZ ART6 ZLIV2) as [WRZ _].
  destruct (n_wr_at_rw_CB m6 zb nZ WRZ ltac:(clear - NZR LEN0; lia)) as (OB & OBJ).
  assert (LOB : Z.of_nat (length OB) = nZ) by (destruct OBJ as [[Hwf _] _]; cbn in Hwf; destruct Hwf as [HL _]; rewrite HL; clear - NZR LEN0; lia).
  pose proof (u8arr_of_rw_cells b0segs m6 zb _ OB OBJ) as OBM. clear OBJ WRZ.
  pose proof (af_live_disj RT AF Σ2 m6 r3 262148 zb nZ [] _ ART6 LVall ltac:(cbn [app In]; right; right; right; exact ZLIV)) as DZ3.
  pose proof (af_live_disj RT AF Σ2 m6 r2 ARR2_SIZE zb nZ [(r3, 262148)] _ ART6 LVall ltac:(cbn [app In]; right; right; right; exact ZLIV)) as DZ2.
  pose proof (af_live_disj RT AF Σ2 m6 r1 ARR1_SIZE zb nZ [(r3, 262148); (r2, ARR2_SIZE)] _ ART6 LVall ltac:(cbn [app In]; right; right; right; exact ZLIV)) as DZ1.
  pose proof (af_live_disj RT AF Σ2 m6 E 55768 zb nZ [(r3, 262148); (r2, ARR2_SIZE); (r1, ARR1_SIZE)] _ ART6 LVall ltac:(cbn [app In]; right; right; right; exact ZLIV)) as DZE.
  assert (OOK : out_okB (aci_c B0C) cx zb nZ).
  { unfold out_okB, apart, img_apart, IMG_LO3, CEIL. cbn [ci_hi aci_c B0C cx c_E c_A1 c_A2 c_FT]. unfold ESTATE_SIZE, FTAB_WORDS. change (4 * 65537) with 262148.
    split; [exact ZB0|]. split; [clear - NZR LEN0; lia|]. split; [rewrite CEQ; exact ZBH|]. split; [clear - NZR; lia|].
    split; [clear - DZE; lia|]. split; [clear - DZ1; lia|]. split; [clear - DZ2; lia|]. split; [clear - DZ3; lia| clear - ZBI; lia]. }
  assert (PAYC : pay_condB cx zb nZ d bs).
  { intros NE. destruct PIN as [(p & n & PI & PL & PH & PNE)|PE]; [| exfalso; exact (NE PE)].
    assert (PI2 : In (p, n) (rt_live RT Σ2)) by (rewrite LVall; right; right; right; right; exact PI).
    pose proof (af_live_range RT AF Σ m p n ART0 PI) as (_ & PHI2 & _).
    pose proof (af_live_disj RT AF Σ2 m6 r3 262148 p n [] _ ART6 LVall ltac:(cbn [app In]; right; right; right; exact PI)) as DP3.
    pose proof (af_live_disj RT AF Σ2 m6 r2 ARR2_SIZE p n [(r3, 262148)] _ ART6 LVall ltac:(cbn [app In]; right; right; right; exact PI)) as DP2.
    pose proof (af_live_disj RT AF Σ2 m6 r1 ARR1_SIZE p n [(r3, 262148); (r2, ARR2_SIZE)] _ ART6 LVall ltac:(cbn [app In]; right; right; right; exact PI)) as DP1.
    pose proof (af_live_disj RT AF Σ2 m6 E 55768 p n [(r3, 262148); (r2, ARR2_SIZE); (r1, ARR1_SIZE)] _ ART6 LVall ltac:(cbn [app In]; right; right; right; exact PI)) as DPE.
    pose proof (live_disj_in RT AF Σ m p n zb nZ ART0 PI ZLIV PNE) as DPZ.
    unfold pay_okB, apart, CEIL. cbn [cx c_E c_A1 c_A2 c_FT]. unfold ESTATE_SIZE, FTAB_WORDS. change (4 * 65537) with 262148. fold len.
    split; [clear - D0; lia|]. split; [exact LEN0|]. split; [rewrite CEQ; clear - PH PHI2; lia|].
    split; [clear - DPE PL PH; lia|]. split; [clear - DP1 PL PH; lia|]. split; [clear - DP2 PL PH; lia|]. split; [clear - DP3 PL PH; lia| clear - DPZ PL PH; lia]. }
  assert (PAYL : pay_liveA RT Σ2 zb nZ d bs).
  { intros NE. destruct PIN as [(p & n & PI & PL & PH & PNE)|PE]; [| exfalso; exact (NE PE)].
    exists p, n. split; [rewrite LVall; right; right; right; right; exact PI|]. split; [exact PL|]. split; [exact PH| exact PNE]. }
  assert (SMB : rw_cells b0segs m6 (FB + 32) (STRMB cx zb nZ DBZA DBZF z0 d (jw4 jb 20) (jw4 jb 44))).
  { unfold STRMB. cbn [z0 z_b2b z_avail_in z_avail_out z_tin_lo z_tin_hi z_tout_lo z_tout_hi cx c_E]. rewrite LPAY. replace (zb + (nZ - nZ)) with zb by (clear; lia). exact SM. }
  assert (SOKA6 : strm_okA RT Σ2 m6 (FB + 32)).
  { split; [exists FB, 2%nat; split; [exact FBIN2| change (fs_size 2) with 256; clear; lia]|].
    split; [clear - F64; Z.div_mod_to_equations; lia|].
    replace (shad (FB + 32)) with (SHF + 4) by (destruct AX as [A8 ->]; unfold shad, SHB; clear - A8; Z.div_mod_to_equations; lia).
    exact (proj1 (n_rw_cells_bytes b0segs m6 _ _ SHz)). }
  assert (EM6 : emem cx b0segs (eg_init (Z_to_bv 64 0)) e0 m6).
  { unfold emem. cbn [cx c_E c_J]. exact (conj EH1 (conj INU (conj UNS (conj EH2 (conj MTF (conj SEL (conj SLM (conj LEN' (conj COD (conj RFQ LNP)))))))))). }
  assert (AM6 : CmpCut.amem cx b0segs e0 m6) by (unfold CmpCut.amem, FTAB_WORDS; cbn [cx c_A1 c_A2 c_FT]; exact (conj AR1 (conj AR2 FTB))).
  assert (CEQ2 : @alloc_ceiling ACI = rt_sp0 RT Σ2 - STACK_WIN) by (rewrite SP2; exact CEQ1).
  pose proof (@hc_credit_bound BZP z0 ltac:(cbn [z0 z_b2b z_avail_in]; rewrite LPAY; clear - LEN LEN0; lia)) as HCB.
  pose proof (BZCC BZP ACI Σ2 PMc (Z_to_bv 64 0x88a20) (Z_to_bv 64 P) gp tp y0 y1 y2 sp (Z_to_bv 64 P) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 2) a2'' a3'' g4 g5 g6 g7 (Z_to_bv 64 FB) (Z_to_bv 64 SHD) (Z_to_bv 64 0) (Z_to_bv 64 SHF) (Z_to_bv 64 FB) (Z_to_bv 64 zb) (Z_to_bv 64 WORKFACTOR) (Z_to_bv 64 0) (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 (FB + 32)) y3 y4 y5 y6 F5 fc5 m6 cx zb nZ DBZA DBZF (eg_init (Z_to_bv 64 0)) e0 z0 d bs OB (jw4 jb 20) (jw4 jb 44) lo) as BC.
  cbv zeta in BC. rewrite PU in BC. change (c_bz cx + BZF_STRM) with (FB + 32 - BZF_STRM + BZF_STRM) in BC.
  replace (FB + 32 - BZF_STRM + BZF_STRM) with (FB + 32) in BC by (clear; lia).
  refine (cps_realizes bsegs _ _ T c7 (BC FDO MST eq_refl eq_refl TP CEQ2 eq_refl eq_refl ltac:(cbn [z0 z_b2b z_avail_in]; exact LPAY) eq_refl eq_refl EM6 AM6 LIB6 SMB SOKA6
            OBM LOB OOK ZLIV2 PLM6 eq_refl PAYC PAYL ELIV R1LIV R2LIV R3LIV
            ltac:(rewrite FRS2, FRS1; cbn [length]; clear - FRB; unfold FRAMES_MAX in *; lia) ltac:(rewrite CR2, CR1; clear - HCB ICOST CRED; lia)
            ART6 MI6 ST6 ltac:(rewrite SP2, SP1; exact LOW) ltac:(unfold RT_STACK; clear - PLO; lia) ltac:(clear - SPT PHI; lia) SPA' CX SEP IMG LAWS HX) Hc7 _).
  clear Hc7 BC. intros c8 (Σ3 & Hq & LV3 & FRS3 & SP3 & CR3).
  destruct (ASTA_unpack RT Σ3 _ _ c8 Hq) as (ms8 & (m7 & q0 & q1 & q2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & q3 & q4 & q5 & q6 & F7 & fc7 & g' & POST) & Hc8). clear Hq.
  (* [comment removed for export] *)
  pose proof (@b2b_round_trip BZP ar1 ar2 ft inU uns mtf sel selM len' code rfreq lenp bsB bsL nIn oP nM BzDOut.dst_zero pay nZ len 0 ZB1 ZB2 FTW BYP
                ltac:(clear - NZR LEN0; lia) ltac:(rewrite LPAY; clear; lia) (or_introl eq_refl)) as [RT1 _].
  cbv zeta in RT1. fold e0 z0 in RT1. set (str := enc_stream e0 pay) in RT1.
  destruct (bzCompress znew e0 z0 BZ_FINISH) as [[ret eF] zF] eqn:BZE.
  destruct POST as (-> & ART7 & MI7 & ST7 & EM7 & AM7 & LIB7 & SM7 & OBM7 & (AVO7 & OUTL7) & EOK7 & STEP7).
  rewrite (ret_pc_even 0x88a20 ltac:(lia) eq_refl) in Hc8.
  assert (RETD : ret = -1 \/ ret = 3 \/ ret = 4).
  { destruct (Z_le_gt_dec (Z.of_nat (length str)) nZ) as [FIT|OVF]; [right; right; exact (proj1 (proj1 RT1 FIT))| right; left; exact (proj1 (proj2 RT1 ltac:(clear - OVF; lia)))]. }
  (* [comment removed for export] *)
  assert (LVsplit : rt_live RT Σ2 = [(r3, 262148); (r2, ARR2_SIZE); (r1, ARR1_SIZE); (E, 55768)] ++ rt_live RT Σ) by (rewrite LVall; reflexivity).
  assert (FRsub : forall e1', In e1' (rt_frames RT Σ) -> In e1' (rt_frames RT Σ2)) by (intros e1' H; rewrite FRS2, FRS1; right; exact H).
  assert (SPU2 : rt_sp0 RT Σ2 - STACK_WIN <= usp) by (rewrite SP2, SP1; clear - LOW PLO PHI; lia).
  pose proof (newlive_not_caller RT AF Σ2 m6 _ _ usp _ E 55768 ART6 LVsplit ltac:(in_list) FRsub SPU2) as NEWE.
  pose proof (newlive_not_caller RT AF Σ2 m6 _ _ usp _ r1 ARR1_SIZE ART6 LVsplit ltac:(in_list) FRsub SPU2) as NEW1.
  pose proof (newlive_not_caller RT AF Σ2 m6 _ _ usp _ r2 ARR2_SIZE ART6 LVsplit ltac:(in_list) FRsub SPU2) as NEW2.
  pose proof (newlive_not_caller RT AF Σ2 m6 _ _ usp _ r3 262148 ART6 LVsplit ltac:(in_list) FRsub SPU2) as NEW3.
  pose proof (sig_ok_eq RT _ _ _ _ _ _ Σ2 Σ3 SOK2 LV3 FRS3 SP3) as SOK3.
  unfold ESTATE_SIZE, FTAB_WORDS in STEP7. change (4 * 65537) with 262148 in STEP7. cbn [cx c_E c_A1 c_A2 c_FT] in STEP7.
  assert (PR7 : PRESI usp (rt_frames RT Σ) (rt_live RT Σ) Wc m2 m7).
  { apply (pres_step_new G Σ2 _ m6 m7 SOK2 PR6 STEP7). per_interval.
    - right; right. apply NEWE. assumption.
    - right; right. apply NEW1. assumption.
    - right; right. apply NEW2. assumption.
    - right; right. apply NEW3. assumption.
    - right; left. unfold Wc. cbn [outside]. match goal with HX : _ <= _ < _ |- _ => clear - HX; lia end.
    - left. right; left. match goal with HX : _ <= _ < _ |- _ => clear - HX; lia end. }
  clear EH1 INU UNS EH2 MTF SEL SLM LEN' COD RFQ LNP AR1 AR2 FTB SM OBM PLM6 LIB6 EM6 AM6 SMB SOKA6 ST6.
  xfer_rtf G SOK2 STEP7 m6 m7.
  (* [comment removed for export] *)
  pose proof (pres_final RT AF Σ lo P usp Wc m m1 m2 m7 ART0 LOW ltac:(clear - PLO; lia) ltac:(clear - PHI; lia) MU1k PRES2 PR7) as FP7.
  assert (AFW5 : app_fp [(dl, dl + 4)]) by (cbn [app_fp]; unfold SH_LO, SH_HI; split; [clear - FDHI' FDLO FDHI; lia| exact I]).
  pose proof SM7 as SM7c. unfold STRMB in SM7c.
  eapply (l1_realizes RT AF Σ3 PMc _ T c8 MST Hc8).
  eapply (@B0_b2c_W5 BZP ACI _ P FB SHF (FB + 32) lo zb dl d len sp gp tp F7 fc7 LLO ltac:(clear - PLO; lia) DLR DLH eq_refl FSEG FBH SHD AD ltac:(clear - FDSEG FDLO; lia) DLFv m7 ret nZ
            (z_avail_out zF));
    [exact RETD| exact AVO7| clear - NZR; lia| exact SM7c| exact SL| exact DLC2| exact (kmem_inv_N _ _ MI7)| exact (shpW_of_acc b0segs _ m7 dl 4 (DLACC m7 FP7) AFW5 (proj1 DL47) (proj2 DL47))|].
  clear Hc8 SL DLC2 SM7c. intros m8 a1x a2x SM8 SL DLC2 NMI8 MU8 WM8. apply evt_done. intros c9 Hc9.
  unfold b2c_W5 in MU8.
  destruct (after_l1 AF G Σ3 _ m7 m8 SOK3 ART7 MI7 ST7 PR7 NMI8 MU8 WM8 ltac:(per_interval; right; right; right; unfold Wc; cbn [outside]; match goal with HX : _ <= _ < _ |- _ => clear - HX; lia end))
    as (ART8 & MI8 & ST8 & PR8 & _).
  destruct EM7 as (EH1 & _). cbn [cx c_E] in EH1. clear AM7 LIB7 SM7.
  assert (GZE : id (E + 55768 <= zb \/ zb + nZ <= E)) by exact DZE.
  pose proof (outb_length (z_outr zF) OB nZ LOB ltac:(clear - OUTL7 AVO7; lia)) as LOBz.
  clear ST7. xfer_l1 m7 m8 MU8 WM8. clear NMI8 MU8 WM8.
  (* [comment removed for export] *)
  assert (SOKA8 : strm_okA RT Σ3 m8 (FB + 32)).
  { split; [exists FB, 2%nat; split; [rewrite FRS3; exact FBIN2| change (fs_size 2) with 256; clear; lia]|].
    split; [clear - F64; Z.div_mod_to_equations; lia|].
    replace (shad (FB + 32)) with (SHF + 4) by (destruct AX as [A8 ->]; unfold shad, SHB; clear - A8; Z.div_mod_to_equations; lia).
    exact (proj1 (n_rw_cells_bytes b0segs m8 _ _ SHz)). }
  assert (CEQ3 : @alloc_ceiling ACI = rt_sp0 RT Σ3 - STACK_WIN) by (rewrite SP3; exact CEQ2).
  pose proof (ENDC BZP ACI Σ3 PMc (Z_to_bv 64 0x88a64) (Z_to_bv 64 P) gp tp q0 q1 q2 sp (Z_to_bv 64 P) (Z_to_bv 64 (FB + 32)) a1x a2x h3 h4 h5 h6 h7 (Z_to_bv 64 FB) (Z_to_bv 64 SHD) (Z_to_bv 64 (b2c_rc ret)) (Z_to_bv 64 SHF) (Z_to_bv 64 FB) (Z_to_bv 64 zb) (Z_to_bv 64 WORKFACTOR) (Z_to_bv 64 0) (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 (FB + 32)) q3 q4 q5 q6 F7 fc7 m8 cx zb nZ DBZA g' eF zF (d + (z_avail_in z0 - z_avail_in zF)) (jw4 jb 20) (jw4 jb 44) lo) as EC.
  cbv zeta in EC. rewrite PU in EC. change (c_bz cx + BZF_STRM) with (FB + 32 - BZF_STRM + BZF_STRM) in EC.
  replace (FB + 32 - BZF_STRM + BZF_STRM) with (FB + 32) in EC by (clear; lia).
  refine (cps_realizes bsegs _ _ T c9 (EC FDO MST eq_refl TP CEQ3 EH1 SM8 SOKA8 ltac:(rewrite LV3; exact ELIV) ltac:(rewrite LV3; exact R1LIV) ltac:(rewrite LV3; exact R2LIV)
            ltac:(rewrite LV3; exact R3LIV) ART8 MI8 ST8 ltac:(rewrite SP3, SP2, SP1; exact LOW) ltac:(unfold RT_STACK; clear - PLO; lia) ltac:(clear - SPT PHI; lia) SPA' CX SEP) Hc9 _).
  clear Hc9 EC. intros c10 (Σ4 & Hq & LV4 & FRS4 & SP4 & CR4).
  destruct (ASTA_unpack RT Σ4 _ _ c10 Hq) as (ms10 & (m9 & k0 & k1 & k2 & j1 & j2 & j3 & j4 & j5 & j6 & j7 & k3 & k4 & k5 & k6 & F9 & fc9 & -> & ART9 & MI9 & ST9 & SM9 & STEP9) & Hc10). clear Hq.
  rewrite (ret_pc_even 0x88a64 ltac:(lia) eq_refl) in Hc10.
  (* [comment removed for export] *)
  assert (LV4' : rt_live RT Σ4 = rt_live RT Σ).
  { rewrite LV4, LV3, LVall. cbn [cx c_E c_A1 c_A2 c_FT].
    apply (live_remove4 RT AF Σ2 m6 E 55768 r1 ARR1_SIZE r2 ARR2_SIZE r3 262148 (rt_live RT Σ) ART6 LVall); [clear; lia| clear - BZbs; lia| clear - BZbs; lia| clear; lia| exact POSN]. }
  assert (SOK4 : sig_ok RT (rt_sp0 RT Σ) true 2 FB (rt_frames RT Σ) (rt_live RT Σ) Σ4).
  { split; [rewrite FRS4, FRS3, FRS2; exact FRS1|]. split; [rewrite SP4, SP3, SP2; exact SP1|]. intros e1' He. rewrite LV4'. exact He. }
  unfold ESTATE_SIZE, FTAB_WORDS in STEP9. change (4 * 65537) with 262148 in STEP9. cbn [cx c_E c_A1 c_A2 c_FT] in STEP9.
  assert (PR9 : PRESI usp (rt_frames RT Σ) (rt_live RT Σ) Wc m2 m9).
  { apply (pres_step_new G Σ3 _ m8 m9 SOK3 PR8 STEP9). per_interval.
    - right; right. apply NEWE. assumption.
    - right; right. apply NEW1. assumption.
    - right; right. apply NEW2. assumption.
    - right; right. apply NEW3. assumption.
    - left. right; left. match goal with HX : _ <= _ < _ |- _ => clear - HX; lia end. }
  assert (ZLIV3 : In (zb, nZ) (rt_live RT Σ3)) by (rewrite LV3; exact ZLIV2).
  clear EH1 SM8 ST8 SOKA8.
  xfer_rtf G SOK3 STEP9 m8 m9.
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
  eapply (@B0_b2c_E1 ACI _ P FB SHF sp gp tp F9 fc9 FSEG FBH GSELF m9 _ _);
    [| exact SHU| exact HDa| exact (kmem_inv_N _ _ MI9)|]; [cbn [cells_bytes cbytes app]; rewrite app_nil_r; cbn [length]; rewrite L12; reflexivity|].
  clear Hc10 SHU HDa. intros m10 a0x SHF5 HDm NMI10 MU10 WM10. apply evt_done. intros c11 Hc11.
  unfold b2c_WE1 in MU10.
  destruct (after_l1 AF G Σ4 _ m9 m10 SOK4 ART9 MI9 ST9 PR9 NMI10 MU10 WM10 ltac:(fp_ours PHI)) as (ART10 & MI10 & ST10 & PR10 & _).
  clear ST9. xfer_l1 m9 m10 MU10 WM10. clear NMI10 MU10 WM10 SHF5 HDm SM9.
  (* [comment removed for export] *)
  destruct (release_inline2 AF G (mi := m2) Σ4 m10 eq_refl SOK4 ART10) as (Σ5 & fl & FLC & FLP & FL0 & FLW & FLD & REL).
  replace (FB + 256 - 8) with (FB + 248) in FLP by (clear; lia).
  eapply (l1_realizes RT AF Σ4 PMc _ T c11 MST Hc11).
  eapply (@B0_b2c_E1b ACI _ FB gp tp F9 fc9 fl m10); [exact (ro_C8_KN m10 _ _ FLP)|].
  eapply (B0_b2c_E2 _ gp tp F9 fc9 fl m10 (Z_to_bv 8 1)); [exact FLC| exact (kmem_inv_N _ _ MI10)|].
  clear Hc11. intros m11 FLC2 NMI11 MU11 WM11. apply evt_done. intros c12 Hc12.
  destruct (REL m11 MU11 WM11 FLC2 MI10 NMI11 ST10 PR10) as (ART11 & FRS5 & LV5 & SP5 & CR5 & AL5 & AM5 & MI11 & ST11 & PR11).
  clear ST10. xfer_fl G SOK4 FLD m10 m11 MU11 WM11.
  pose proof (ASTA_switch RT Σ4 Σ5 PMc _ c12 Hc12 AL5 AM5) as Hc12'. clear Hc12.
  eapply (l1_realizes RT AF Σ5 PMc _ T c12 MST Hc12').
  eapply (@B0_b2c_E3 ACI _ P lo sp gp tp F9 fc9 ltac:(clear - PLO; lia) PCASE m11); [exact SL| exact GAP| exact SAV| exact ST11|].
  clear Hc12'. intros STu. apply evt_done. intros c13 Hc13.
  (* [comment removed for export] *)
  pose proof (pres_final RT AF Σ lo P usp Wc m m1 m2 m11 ART0 LOW ltac:(clear - PLO; lia) ltac:(clear - PHI; lia) MU1k PRES2 PR11) as FPE.
  apply Hk. exists Σ5, (b2c_rc ret), (b2c_dlv ret nZ (z_avail_out zF)).
  split; [| split; [rewrite LV5; exact LV4'| split; [exact FRS5| split; [exact SP5|]]]].
  2:{ rewrite CR5, CR4. unfold HD.B2BC_COST. clear - CR3 CR2 CR1 HCB ICOST. lia. }
  eapply ASTA_conseq; [exact Hc13|]. intros ms <-. exists m11.
  split. { unfold ret_st. exists k0, k1, k2, j1, j2, j3, j4, j5, j6, j7, k3, k4, k5, k6, F9, fc9. reflexivity. }
  split. { split; [exact ART11| split; [exact MI11| exact STu]]. }
  split. { exact FPE. }
  split. { exact (n2k_C4 m11 dl _ DLC2). }
  split. { apply (lib_of_pfp _ _ _ _ m m11 LIB FPE). intros x Hx. unfold Wc. cbn [outside]. split; [clear - Hx ZBI NZR; lia|]. split; [clear - Hx FDSEG FDLO; lia| exact I]. }
  destruct RETD as [-> | [-> | ->]]; [right; unfold b2c_rc; cbn; clear; lia| right; unfold b2c_rc; cbn; clear; lia|].
  left. split; [reflexivity|].
  destruct (Z_le_gt_dec (Z.of_nat (length str)) nZ) as [FIT|OVF].
  2:{ exfalso. pose proof (proj1 (proj2 RT1 ltac:(clear - OVF; lia))) as R3. unfold BZ_FINISH_OK in R3. clear - R3. lia. }
  destruct (proj1 RT1 FIT) as (_ & OUTR & AVO & _).
  exists (map (Z_to_bv 8) str).
  split. { exists BZP, ar1, ar2, ft, inU, uns, mtf, sel, selM, len', code, rfreq, lenp, bsB, bsL, nIn, oP, nM.
           split; [reflexivity|]. split; [reflexivity|]. split; [exact ZB1|]. split; [exact ZB2|]. split; [exact FTW| reflexivity]. }
  split. { unfold b2c_dlv. cbn [Z.eqb Pos.eqb]. rewrite AVO, length_map. clear. lia. }
  split. { unfold b2c_dlv. cbn [Z.eqb Pos.eqb]. rewrite AVO. clear - FIT. lia. }
  rewrite OUTR, outb_eq, rev_involutive in OBM7.
  exact (proj1 (proj1 (KMem.bytes_at_app bsegs m11 zb _ _) (proj1 (n_u8arr_bytes b0segs m11 zb _ OBM7)))).
Qed.
End B2BC.

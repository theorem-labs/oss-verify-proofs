(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BY_ubkit B_iface BYajlRep BYajl_iface BY_rz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.LiaFastA.zify_fast_euclid3.   (* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section W.
Variable Y : ay_params.
Hypothesis KIPY : AHK_y_kip_stmt Y.
Hypothesis FRAMEY : AHK_y_frame_stmt Y.
Hypothesis BLKY : AHK_y_blocks_stmt Y.
Hypothesis MIY : AHK_y_mem_inv_stmt Y.
Hypothesis BSHY : AHK_y_block_shadow_stmt Y.
Hypothesis BSMALL : AHK_y_small_high_stmt Y.   (* [comment removed for export] *)
Hypothesis LAYY : AHK_y_layout_stmt Y.
Hypothesis RRT : ayR_trans_stmt Y.
Hypothesis NONNEG : yacct_nonneg_stmt Y.
Hypothesis YFREE : yacct_free_stmt Y.
Hypothesis YFB : forall b, y_free_cost Y + y_free_cost Y <= y_phi_buf Y b.     (* [comment removed for export] *)
Hypothesis WFREE : aywrap_free_stmt Y.
(* [comment removed for export] *)
Variable URA : list Z.
Hypothesis UTRIV : forall m SP ra s0, bv_unsigned s0 < alloc_ceiling -> In (bv_unsigned ra) URA -> y_uanchor Y m SP ra s0.   (* [comment removed for export] *)
Hypothesis URA_site1 : In 0x8710c URA.                                          (* [comment removed for export] *)
Hypothesis UFRAME : forall m m' SP ra s0, (forall a, SP <= a < 2^47 -> m' (wa a) = m (wa a)) -> y_uanchor Y m SP ra s0 -> y_uanchor Y m' SP ra s0.

Ltac ay_statics_open STA :=
  let G1 := fresh "G1" in let G2 := fresh "G2" in let G3 := fresh "G3" in let G4 := fresh "G4" in
  destruct STA as (G1 & G2 & G3 & G4);
  unfold AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz in G1, G2, G3, G4.

(* [comment removed for export] *)
Ltac buf_free_tail BS HBS B AF FR ST sp :=
  shadow_fast BS (B + 24) 8;
  zstepA;                                            (* [comment removed for export] *)
  ugd; zstepA; ugd;                                  (* [comment removed for export] *)
  zstepA; shadow_fast HBS (AF + 16) 8;               (* [comment removed for export] *)
  zstepA; shadow_fast HBS (AF + 24) 8;               (* [comment removed for export] *)
  zstepA; zstepA; stepA; stepA;                      (* [comment removed for export] *)
  do 5 stepA;                                        (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp);
  stepA.                                             (* [comment removed for export] *)

Theorem aybuf_free_proof : aybuf_free_stmt Y.
Proof. aceil.
  unfold aybuf_free_stmt. intros LF REST mb b AF lo RR K. intros until s. intros (MBP & MBA8 & AFP & AFA8) K0 AY BR YAF AFOK BSH FP EA CRED RR0 NBIG UA CONT. subst a0.
  destruct FP as (ST & CEIL & LO & SPH & SP16 & MI & TP & FRM).
  apply AYST_split in AY. destruct AY as [AHK0 YS]. pose proof YS as (_ & _ & _ & STA).
  destruct AFOK as (hb & HBIN & HB1 & HB2 & AF8 & HBS & HBHI).
  destruct (BLKY _ _ _ _ _ AHK0) as (RNG & SEP & ND).
  assert (HBIN' : In hb (abl (buf_blocks mb b) ++ REST)) by (apply in_or_app; right; exact HBIN).
  pose proof (RNG hb HBIN') as HBR. unfold ablock_range, ACONSTS in HBR. cbn [c_img_hi] in HBR.
  pose proof HBHI as HBSH. unfold oshw_hi, A_SB in HBSH.   (* [comment removed for export] *)
  assert (HBSH2 : 17594333495296 <= ab_addr hb) by (revert HBSH CEILB; clear; intros H CEILB; cbn in H; lia). clear HBSH.
  pose proof (RNG _ (or_introl eq_refl)) as BRNG. unfold ablock_range, ACONSTS in BRNG. cbn [c_img_hi ab_addr ab_size abl buf_blocks map blk_addr blk_size fst snd] in BRNG.
  pose proof (BSMALL _ _ _ _ _ _ AHK0 (or_introl eq_refl) ltac:(cbn; unfold SIZEOF_BUF; lia)) as BSHI. cbn [ab_addr abl buf_blocks map blk_addr blk_size fst snd] in BSHI. unfold oshw_hi, A_SB, amem in BSHI.
  assert (BSH2 : 17594333495296 <= mb_addr mb) by (revert BSHI CEILB; clear; intros H CEILB; cbn in H; lia). clear BSHI.
  pose proof (rw_cells_bound _ _ _ _ YAF) as YAFB. cbn [cells_size csize Nat.add alloc_cells length] in YAFB.
  destruct BR as ((BC & DZ & RL & RU) & BD & FB). unfold buf_cells in BC.
  pose proof (rw_cells_bound _ _ _ _ BC) as BCB. cbn [cells_size csize Nat.add] in BCB.
  unfold AY_BUF_FREE, AY_BUF_FREE_STACK, AMALLOC_STACK, SIZEOF_BUF, wz in *.
  aceil.
  ay_statics_open STA.
  unfold alloc_cells in YAF. cbn [yc_malloc_w yc_realloc_w yc_free_w ayc] in YAF. unfold AY_MALLOC_W, AY_REALLOC_W, AY_FREE_W, wz in YAF.
  pose proof (block_shadow_bound bsegs m _ _ _ HBS) as HBSB. unfold A_SB in HBSB. unfold oshadow, A_SB in HBS. open_shadow HBS.
  pose proof (block_shadow_bound bsegs m _ _ _ BSH) as BSB. unfold A_SB in BSB. unfold oshadow, A_SB in BSH. open_shadow BSH.
  pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  destruct (yb_data b) as [dp|] eqn:HD.
  - (* [comment removed for export] *)
    assert (D0 : mb_data mb <> 0) by (intros E; apply DZ in E; congruence).
    unfold buf_blocks, abl in AHK0, RNG, SEP, ND, HBIN'. rewrite HD in AHK0, RNG, SEP, ND, HBIN'. cbn [map app blk_addr blk_size fst snd] in AHK0, RNG, SEP, ND, HBIN'.
    pose proof (RNG _ (or_intror (or_introl eq_refl))) as DRNG. unfold ablock_range, ACONSTS in DRNG. cbn [c_img_hi ab_addr ab_size] in DRNG.
    aceil. unfold SIZEOF_BUF in *.
    assert (NE_BD : mb_addr mb <> mb_data mb).
    { cbn [map ab_addr] in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI _]. intros E. apply NI. left. symmetry. exact E. }
    pose proof (SEP (mkABlock (mb_addr mb) 32) (mkABlock (mb_data mb) (yb_len b)) (or_introl eq_refl) (or_intror (or_introl eq_refl)) NE_BD) as SBD; cbn [ab_addr ab_size] in SBD.
    all: clear BD.
    all: arz_seg KIPY AHK0.
    all: pose proof (aypol_stack Y _ LF _ _ LINK lo (bv_unsigned sp) ltac:(aceil; lia) ltac:(lia)) as PSTK.
    all: pose proof (aypol_img Y _ LF _ _ LINK) as PIMG.
    all: assert (Q1 : 0 <= ab_addr (mkABlock (mb_addr mb) 32)) by (cbn [ab_addr]; lia).
    all: assert (Q2 : 0 <= oshw_lo (ab_addr (mkABlock (mb_addr mb) 32))) by (cbn [ab_addr]; unfold oshw_lo, A_SB; lia).
    all: assert (Q3 : oshw_hi (ab_addr (mkABlock (mb_addr mb) 32)) (ab_size (mkABlock (mb_addr mb) 32)) < 2^64) by (cbn [ab_addr ab_size]; unfold oshw_hi, A_SB, amem; lia).
    all: assert (Q4 : ab_addr (mkABlock (mb_addr mb) 32) + ab_size (mkABlock (mb_addr mb) 32) < 2^64) by (cbn [ab_addr ab_size]; lia).
    all: pose proof (aypol_opol_block Y _ LF _ _ LINK _ (or_introl eq_refl) Q1 Q2 Q3 Q4) as [PB PBS]; clear Q1 Q2 Q3 Q4.
    all: assert (Q1 : 0 <= ab_addr hb) by lia.
    all: assert (Q2 : 0 <= oshw_lo (ab_addr hb)) by (unfold oshw_lo, A_SB; lia).
    all: assert (Q3 : oshw_hi (ab_addr hb) (ab_size hb) < 2^64) by (unfold oshw_hi, A_SB, amem; lia).
    all: assert (Q4 : ab_addr hb + ab_size hb < 2^64) by lia.
    all: pose proof (aypol_opol_block Y _ LF _ _ LINK hb HBIN' Q1 Q2 Q3 Q4) as [PHB PHBS]; clear Q1 Q2 Q3 Q4.
    all: cbn [ab_addr ab_size] in PB, PBS; unfold pol, oshw_lo, oshw_hi, A_SB, amem, AY_IMG_LO, AY_IMG_HI in PSTK, PIMG, PB, PBS, PHB, PHBS.
    all: clear Hh HLI Hmi.
    all: carve_frame 32%nat ST.
    all: do 5 stepA.                                  (* [comment removed for export] *)
    all: zstepA; if_cases K1; zify_cond K1; [kill K1|].   (* [comment removed for export] *)
    all: stepA; zstepA; ugd.                          (* [comment removed for export] *)
    all: do 2 stepA.                                  (* [comment removed for export] *)
    all: zstepA.                                      (* [comment removed for export] *)
    all: zstepA.                                      (* [comment removed for export] *)
    all: shadow_fast BSH (mb_addr mb + 16) 8.         (* [comment removed for export] *)
    all: zstepA.                                      (* [comment removed for export] *)
    all: zstepA.                                      (* [comment removed for export] *)
    all: zstepA; if_cases K2; zify_cond K2; [kill K2|].   (* [comment removed for export] *)
    all: shadow_fast BSH (mb_addr mb + 24) 8.         (* [comment removed for export] *)
    all: zstepA.                                      (* [comment removed for export] *)
    all: ugd; zstepA; ugd.                            (* [comment removed for export] *)
    all: zstepA; shadow_fast HBS (AF + 16) 8.         (* [comment removed for export] *)
    all: zstepA; shadow_fast HBS (AF + 24) 8.         (* [comment removed for export] *)
    all: zstepA; zstepA.                              (* [comment removed for export] *)
    all: stepA.                                       (* [comment removed for export] *)
    all: apply evtA_done; intros mo1 Hag1 HLI1 Hh1.
    all: lazymatch type of MU with munch _ _ ?mx => rename mx into m1 end.
    all: assert (AHK1 : y_AHK Y s ({| ab_addr := mb_addr mb; ab_size := 32 |} :: {| ab_addr := mb_data mb; ab_size := yb_len b |} :: REST) LF m1 mo1)
      by (destruct (BACK mo1 Hag1 HLI1) as [AHKb _]; eapply FRAMEY; [exact AHKb| exact MU| exact WM|];
          constructor; [| constructor]; left; cbn; aceil; lia).
    all: pose proof (proj2 (BACK mo1 Hag1 HLI1)) as R1.
    all: pose proof (aystatics_munch _ _ _ YS MU WM ltac:(constructor; [cbn; lia| constructor])) as YS1.
    all: rename MU into MU0; rename WM into WM0; clear LINK BACK PSTK PIMG PB PBS PHB PHBS.
    (* [comment removed for export] *)
    all: name_sp sp (-32)%Z; rewrite <- Hsp in ST.
    all: eapply (WFREE (mb_data mb) (yb_len b) _ LF lo (y_free_cost Y + RR));
      [ exact K0
      | apply AYST_split; split; [exact AHK1| exact YS1]
      | right; left; reflexivity
      | reflexivity
      | pose proof (YFB b); lia
      | pose proof YFREE as YF0; unfold yacct_free_stmt in YF0; lia
      | pose proof (nbig_cons_le {| ab_addr := mb_addr mb; ab_size := 32 |} ({| ab_addr := mb_data mb; ab_size := yb_len b |} :: REST));
        pose proof (nbig_cons_le {| ab_addr := mb_data mb; ab_size := yb_len b |} REST); unfold AY_NBIG_REST in NBIG; lia
      | unfold ayframe_pre, AY_WRAP_STACK, AMALLOC_STACK; aceil;
        split; [exact ST|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [Z.div_mod_to_equations; lia|];
        split; [assumption|]; split; [exact TP| exact FRM]
      | apply UTRIV; [rewrite unsigned_lit by lia; aceil; lia| rewrite unsigned_lit by lia; exact URA_site1]
      | ].
    all: cbv beta; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 m2 mo2 sa2 (MI2 & ST2 & FRM2 & WM2 & PRES2) SO2 R2 CRED2 AY2.
    all: unname_sp.
    all: rewrite (ab_remove_skip _ _ _ _ NE_BD), ab_remove_head in PRES2, AY2.
    all: apply AYST_split in AY2; destruct AY2 as [AHK2 YS2]; pose proof YS2 as (_ & _ & _ & STA2); ay_statics_open STA2.
    all: pose proof (aypres_frame _ _ _ _ _ _ _ PRES2 FR ltac:(lia)) as FR2; clear FR.
    all: pose proof (aypres_block _ _ _ _ _ _ _ PRES2 YAF ltac:(exists hb; split; [right; exact HBIN| cbn; lia])) as YAF2; clear YAF.
    all: pose proof (aypres_block _ _ _ _ _ _ _ PRES2 BC ltac:(eexists; split; [left; reflexivity| cbn; lia])) as BC2; clear BC.
    all: clear G1 G2 G3 G4 BSH HBS.
    all: pose proof (BSHY _ _ _ _ _ _ AHK2 (or_introl eq_refl) ltac:(cbn; lia)) as [BSH _]; cbn [ab_addr ab_size] in BSH; unfold oshadow, A_SB in BSH; open_shadow BSH.
    all: pose proof (BSHY _ _ _ _ _ hb AHK2 (or_intror HBIN) ltac:(lia)) as [HBS _]; unfold oshadow, A_SB in HBS; open_shadow HBS.
    all: assert (PRES2w : ay_pres REST LF (bv_unsigned sp) [] m m2)
      by (eapply ay_pres_trans;
          [ eapply ay_pres_of_munch; [exact MU0| exact WM0|];
            intros a Ha Hc _; eapply (ay_client_outside REST LF); [ | | | | exact Hc];
            [ intros b0 Hb0; pose proof (RNG b0 (or_intror (or_intror Hb0))) as Rb; unfold ablock_range in Rb; lia
            | intros f Hf; destruct (proj1 (LAYY _ _ _ _ _ AHK0) f Hf) as (L1 & L2 & L3 & L4 & L5); unfold oshw_hi, A_SB, amem in L1; lia
            | aceil; lia | lia ]
          | eapply (ay_pres_weaken Y); [exact PRES2| lia| intros b0 Hb0; right; exact Hb0| auto| auto] ]).
    (* [comment removed for export] *)
    all: pose proof (munch_refl ([] : list (Z * Z)) m2) as MU; pose proof (wmono_refl bsegs m2) as WM.
    all: arz_seg KIPY AHK2.
    all: pose proof (aypol_stack Y _ LF _ _ LINK lo (bv_unsigned sp) ltac:(aceil; lia) ltac:(lia)) as PSTK.
    all: pose proof (aypol_img Y _ LF _ _ LINK) as PIMG.
    all: assert (Q1 : 0 <= ab_addr (mkABlock (mb_addr mb) 32)) by (cbn [ab_addr]; lia).
    all: assert (Q2 : 0 <= oshw_lo (ab_addr (mkABlock (mb_addr mb) 32))) by (cbn [ab_addr]; unfold oshw_lo, A_SB; lia).
    all: assert (Q3 : oshw_hi (ab_addr (mkABlock (mb_addr mb) 32)) (ab_size (mkABlock (mb_addr mb) 32)) < 2^64) by (cbn [ab_addr ab_size]; unfold oshw_hi, A_SB, amem; lia).
    all: assert (Q4 : ab_addr (mkABlock (mb_addr mb) 32) + ab_size (mkABlock (mb_addr mb) 32) < 2^64) by (cbn [ab_addr ab_size]; lia).
    all: pose proof (aypol_opol_block Y _ LF _ _ LINK _ (or_introl eq_refl) Q1 Q2 Q3 Q4) as [PB PBS]; clear Q1 Q2 Q3 Q4.
    all: assert (Q1 : 0 <= ab_addr hb) by lia.
    all: assert (Q2 : 0 <= oshw_lo (ab_addr hb)) by (unfold oshw_lo, A_SB; lia).
    all: assert (Q3 : oshw_hi (ab_addr hb) (ab_size hb) < 2^64) by (unfold oshw_hi, A_SB, amem; lia).
    all: assert (Q4 : ab_addr hb + ab_size hb < 2^64) by lia.
    all: pose proof (aypol_opol_block Y _ LF _ _ LINK hb (or_intror HBIN) Q1 Q2 Q3 Q4) as [PHB PHBS]; clear Q1 Q2 Q3 Q4.
    all: cbn [ab_addr ab_size] in PB, PBS; unfold pol, oshw_lo, oshw_hi, A_SB, amem, AY_IMG_LO, AY_IMG_HI in PSTK, PIMG, PB, PBS, PHB, PHBS.
    all: clear Hh HLI Hmi; ret_pc_lit; unfold wz.
    all: buf_free_tail BSH HBS (mb_addr mb) AF FR2 ST2 sp.
    all: apply evtA_done; intros mo2b Hag2b HLI2b Hh2b.
    all: lazymatch type of MU with munch _ _ ?mx => rename mx into m2' end.
    all: destruct (BACK mo2b Hag2b HLI2b) as [AHK2b R2b].
    all: assert (AHK2c : y_AHK Y sa2 ({| ab_addr := mb_addr mb; ab_size := 32 |} :: REST) LF m2' mo2b)
      by (eapply FRAMEY; [exact AHK2b| exact MU| exact WM| constructor]).
    all: pose proof (aystatics_munch _ _ _ YS2 MU WM ltac:(constructor)) as YS2c.
    all: assert (AGREE : forall a, bv_unsigned sp <= a < 2^47 -> m2' (wa a) = m (wa a))
      by (intros a Ha; try rewrite (MU (wa a) I); destruct (PRES2w a ltac:(lia) ltac:(left; lia) ltac:(intros F0; exact F0)) as [E _]; exact E).
    all: clear LINK BACK PSTK PIMG PB PBS PHB PHBS.
    all: eapply (WFREE (mb_addr mb) 32 _ LF lo RR);
      [ exact K0
      | apply AYST_split; split; [exact AHK2c| exact YS2c]
      | left; reflexivity
      | reflexivity
      | exact CRED2
      | exact RR0
      | pose proof (nbig_cons_le {| ab_addr := mb_addr mb; ab_size := 32 |} REST); unfold AY_NBIG_REST in NBIG; lia
      | unfold ayframe_pre, AY_WRAP_STACK, AMALLOC_STACK; aceil;
        split; [assumption|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [assumption|]; split; [exact TP| exact FRM2]
      | eapply UFRAME; [exact AGREE| exact UA]
      | ].
    all: cbv beta; intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F3 fc3 m3 mo3 sa3 (MI3 & ST3 & FRM3 & WM3 & PRES3) SO3 R3 CRED3 AY3.
    all: rewrite ab_remove_head in PRES3, AY3.
    all: eapply CONT; unfold aybuf_free_rpost.
    all: split; [rewrite SO3; exact SO2|].
    all: split; [eapply RRT; [exact R1| eapply RRT; [exact R2| eapply RRT; [exact R2b| exact R3]]]|].
    all: split; [lia|].
    all: split; [split; [exact MI3|]; split; [exact ST3|]; split; [exact FRM3|]; split;
                [ exact I
                | eapply ay_pres_trans; [exact PRES2w|]; eapply ay_pres_trans; [| exact PRES3];
                  eapply ay_pres_of_munch; [exact MU| exact WM| intros; exact I] ]|].
    all: split; [eapply aypres_block; [exact PRES3| eassumption| exists hb; split; [exact HBIN| cbn; lia]]|].
    all: exact AY3.
  - (* [comment removed for export] *)
    assert (D0 : mb_data mb = 0) by (apply DZ; reflexivity).
    unfold buf_blocks, abl in AHK0, RNG, SEP, ND, HBIN'. rewrite HD in AHK0, RNG, SEP, ND, HBIN'. cbn [map app blk_addr blk_size fst snd] in AHK0, RNG, SEP, ND, HBIN'.
    unfold SIZEOF_BUF in *. clear BD.
    arz_seg KIPY AHK0.
    pose proof (aypol_stack Y _ LF _ _ LINK lo (bv_unsigned sp) ltac:(aceil; lia) ltac:(lia)) as PSTK.
    pose proof (aypol_img Y _ LF _ _ LINK) as PIMG.
    assert (Q1 : 0 <= ab_addr (mkABlock (mb_addr mb) 32)) by (cbn [ab_addr]; lia).
    assert (Q2 : 0 <= oshw_lo (ab_addr (mkABlock (mb_addr mb) 32))) by (cbn [ab_addr]; unfold oshw_lo, A_SB; lia).
    assert (Q3 : oshw_hi (ab_addr (mkABlock (mb_addr mb) 32)) (ab_size (mkABlock (mb_addr mb) 32)) < 2^64) by (cbn [ab_addr ab_size]; unfold oshw_hi, A_SB, amem; lia).
    assert (Q4 : ab_addr (mkABlock (mb_addr mb) 32) + ab_size (mkABlock (mb_addr mb) 32) < 2^64) by (cbn [ab_addr ab_size]; lia).
    pose proof (aypol_opol_block Y _ LF _ _ LINK _ (or_introl eq_refl) Q1 Q2 Q3 Q4) as [PB PBS]; clear Q1 Q2 Q3 Q4.
    assert (Q1 : 0 <= ab_addr hb) by lia.
    assert (Q2 : 0 <= oshw_lo (ab_addr hb)) by (unfold oshw_lo, A_SB; lia).
    assert (Q3 : oshw_hi (ab_addr hb) (ab_size hb) < 2^64) by (unfold oshw_hi, A_SB, amem; lia).
    assert (Q4 : ab_addr hb + ab_size hb < 2^64) by lia.
    pose proof (aypol_opol_block Y _ LF _ _ LINK hb HBIN' Q1 Q2 Q3 Q4) as [PHB PHBS]; clear Q1 Q2 Q3 Q4.
    cbn [ab_addr ab_size] in PB, PBS; unfold pol, oshw_lo, oshw_hi, A_SB, amem, AY_IMG_LO, AY_IMG_HI in PSTK, PIMG, PB, PBS, PHB, PHBS.
    clear Hh HLI Hmi.
    carve_frame 32%nat ST.
    do 5 stepA.
    zstepA; if_cases K1; zify_cond K1; [kill K1|].
    stepA; zstepA; ugd.                               (* [comment removed for export] *)
    do 2 stepA. zstepA. zstepA.
    shadow_fast BSH (mb_addr mb + 16) 8.
    zstepA. zstepA.
    zstepA; if_cases K2; zify_cond K2; [| kill K2].     (* [comment removed for export] *)
    buf_free_tail BSH HBS (mb_addr mb) AF FR ST sp.
    apply evtA_done; intros mo1 Hag1 HLI1 Hh1.
    lazymatch type of MU with munch _ _ ?mx => rename mx into m1 end.
    destruct (BACK mo1 Hag1 HLI1) as [AHKb R1].
    assert (AHK1 : y_AHK Y s ({| ab_addr := mb_addr mb; ab_size := 32 |} :: REST) LF m1 mo1)
      by (eapply FRAMEY; [exact AHKb| exact MU| exact WM|]; constructor; [| constructor]; left; cbn; aceil; lia).
    pose proof (aystatics_munch _ _ _ YS MU WM ltac:(constructor; [cbn; lia| constructor])) as YS1.
    assert (AGREE : forall a, bv_unsigned sp <= a < 2^47 -> m1 (wa a) = m (wa a))
      by (intros a Ha; apply MU; rewrite wa_unsigned by lia; cbn; lia).
    clear LINK BACK PSTK PIMG PB PBS PHB PHBS.
    eapply (WFREE (mb_addr mb) 32 _ LF lo (y_free_cost Y + RR));
      [ exact K0
      | apply AYST_split; split; [exact AHK1| exact YS1]
      | left; reflexivity
      | reflexivity
      | pose proof (YFB b); lia
      | pose proof YFREE as YF0; unfold yacct_free_stmt in YF0; lia
      | pose proof (nbig_cons_le {| ab_addr := mb_addr mb; ab_size := 32 |} REST); unfold AY_NBIG_REST in NBIG; lia
      | unfold ayframe_pre, AY_WRAP_STACK, AMALLOC_STACK; aceil;
        split; [assumption|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [assumption|]; split; [exact TP| exact FRM]
      | eapply UFRAME; [exact AGREE| exact UA]
      | ].
    cbv beta; intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F3 fc3 m3 mo3 sa3 (MI3 & ST3 & FRM3 & WM3 & PRES3) SO3 R3 CRED3 AY3.
    rewrite ab_remove_head in PRES3, AY3.
    eapply CONT; unfold aybuf_free_rpost.
    split; [exact SO3|].
    split; [eapply RRT; [exact R1| exact R3]|].
    split; [pose proof YFREE; unfold yacct_free_stmt in *; lia|].
    split; [split; [exact MI3|]; split; [exact ST3|]; split; [exact FRM3|]; split;
            [ exact I
            | eapply ay_pres_trans; [| exact PRES3];
              eapply ay_pres_of_munch; [exact MU| exact WM|];
              intros a Ha Hc _; eapply (ay_client_outside REST LF); [ | | | | exact Hc];
              [ intros b0 Hb0; pose proof (RNG b0 (or_intror Hb0)) as Rb; unfold ablock_range in Rb; lia
              | intros f Hf; destruct (proj1 (LAYY _ _ _ _ _ AHK0) f Hf) as (L1 & L2 & L3 & L4 & L5); unfold oshw_hi, A_SB, amem in L1; lia
              | aceil; lia | lia ] ]|].
    split; [eapply aypres_block; [exact PRES3| eassumption| exists hb; split; [exact HBIN| cbn; lia]]|].
    exact AY3.
Qed.
End W.
End RC__1.

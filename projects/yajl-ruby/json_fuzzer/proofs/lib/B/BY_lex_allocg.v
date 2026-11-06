(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep SFW1_lemmas.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BI_shadow BI_asan_memset BYajlRep BYajl_iface BY_rz BY_lex_alloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma yleaf_ymalloc' : forall n r, yleaf (ymalloc n) r.
Proof. aceil. intros. unfold ymalloc. apply (yl_malloc _ _ r). apply yl_ret. Qed.
Lemma yleaf_yfree' : forall p, yleaf (yfree p) tt.
Proof. aceil. intros. unfold yfree. apply yl_free. apply yl_ret. Qed.

Section W.
Variable Y : ay_params.
Hypothesis KIPY : AHK_y_kip_stmt Y.
Hypothesis FRAMEY : AHK_y_frame_stmt Y.
Hypothesis BLKY : AHK_y_blocks_stmt Y.
Hypothesis BSHY : AHK_y_block_shadow_stmt Y.
Hypothesis BSMALL : AHK_y_small_high_stmt Y.   (* [comment removed for export] *)
Hypothesis LAYY : AHK_y_layout_stmt Y.
Hypothesis PERMY : AHK_y_perm_stmt Y.
Hypothesis GLOBY : AHK_y_globals_shadow_stmt Y.
Hypothesis RRT : ayR_trans_stmt Y.
Hypothesis NONNEG : yacct_nonneg_stmt Y.
Hypothesis YFREE : yacct_free_stmt Y.   (* [comment removed for export] *)
Hypothesis WMAL : aywrap_malloc_stmt Y.
Hypothesis BALLOC : aybuf_alloc_stmt Y.
Variable URA : list Z.
Hypothesis UTRIV : forall m SP ra s0, bv_unsigned s0 < alloc_ceiling -> In (bv_unsigned ra) URA -> y_uanchor Y m SP ra s0.
Hypothesis URA_mal : In 0x82cb8 URA.
Hypothesis URA_ba : In 0x82cd8 URA.     (* [comment removed for export] *)
Hypothesis ICPG : forall s LB LF m mo, y_AHK Y s LB LF m mo -> icp_globals bsegs m A_SB.
Hypothesis ICPB : forall s LB LF m mo b A n, y_AHK Y s LB LF m mo -> In b LB ->
    ab_addr b <= A -> 1 <= n -> A + n <= ab_addr b + ab_size b ->
    exists ws, shadow_window bsegs m A_SB A n ws /\ range_clean A_SB A n ws
               /\ shw_hi A_SB A n <= 0x10007fff8000 /\ amem (ab_addr b) (ab_size b).   (* [comment removed for export] *)
Hypothesis ICPR : forall s LB LF m mo b A n, y_AHK Y s LB LF m mo -> In b LB -> ab_addr b <= A -> 1 <= n -> A + n <= ab_addr b + ab_size b ->
    pages_budgeted (y_aS Y s) (shw_lo A_SB A) (shw_hi A_SB A n).

Ltac ay_statics_open STA :=
  let G1 := fresh "G1" in let G2 := fresh "G2" in let G3 := fresh "G3" in let G4 := fresh "G4" in
  destruct STA as (G1 & G2 & G3 & G4);
  unfold AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz in G1, G2, G3, G4.

Theorem aylex_alloc_proof : aylex_alloc_stmt Y.
Proof. aceil.
  unfold aylex_alloc_stmt. intros LF REST AF aC v8 lo RR K. intros until s. intros [AFP AFA8] K0 AY YAF AFOK HAC HV8 FP EA0 EA1 EA2 CRED RR0 NBIG UA CONT. subst a0 a1 a2.
  destruct FP as (ST & CEIL & LO & SPH & SP16 & MI & TP & FRM).
  apply AYST_split in AY. destruct AY as [AHK0 YS]. pose proof YS as (_ & _ & _ & STA). ay_statics_open STA.
  destruct AFOK as (hb & HBI & HB1 & HB2 & AF8 & HBS & HBHI).
  destruct (BLKY _ _ _ _ _ AHK0) as (RNG & SEP & ND).
  pose proof (RNG _ HBI) as HBR. unfold ablock_range, ACONSTS in HBR. cbn [c_img_hi] in HBR.
  pose proof HBHI as HBSI. unfold oshw_hi, A_SB in HBSI.
  assert (HBS2 : 17594333495296 <= ab_addr hb) by (revert HBSI CEILB; clear; intros H CEILB; cbn in H; lia). clear HBSI.
  unfold AY_LEX_ALLOC_STACK, AY_BUF_ALLOC_STACK, AMALLOC_STACK, SIZEOF_LEXER, SIZEOF_BUF, wz in *.
  aceil.
  unfold alloc_cells in YAF. cbn [yc_malloc_w yc_realloc_w yc_free_w ayc] in YAF. unfold wz in YAF.
  pose proof HBS as HBS0. destruct HBS as (HB8 & HBn & HBSu). unfold A_SB in HBSu.
  destruct NONNEG as (NA0 & NB0 & _). pose proof (NB0 ybuf_zero) as NBZ. pose proof (NA0 32) as NA32. pose proof YFREE as YF0. unfold yacct_free_stmt in YF0.
  (* [comment removed for export] *)
  arz_seg KIPY AHK0.
  pose proof (aypol_stack Y _ LF _ _ LINK lo (bv_unsigned sp) ltac:(aceil; lia) ltac:(lia)) as PSTK.
  pose proof (aypol_img Y _ LF _ _ LINK) as PIMG. unfold AY_IMG_LO, AY_IMG_HI in PIMG.
  pose proof (aypol_opol_sub Y _ LF _ _ LINK hb AF 32 HBI HB1 ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold oshw_lo, A_SB; lia) ltac:(unfold oshw_hi, A_SB, amem; lia) ltac:(lia)) as [PHB _].
  pose proof (aypol_opol_block Y _ LF _ _ LINK hb HBI ltac:(lia) ltac:(unfold oshw_lo, A_SB; lia) ltac:(unfold oshw_hi, A_SB, amem; lia) ltac:(lia)) as [_ PHBS].
  unfold oshw_lo, oshw_hi, A_SB, amem in PHB, PHBS.
  eapply evtA_cut.
  { eapply (alexa1_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AF aC v8 lo (ab_addr hb) (ab_size hb));
      [ exact ST | exact MI | lia | lia | lia | exact G1 | exact G2 | exact YAF | exact HBSu | reflexivity | lia | lia | exact AF8 | lia | lia | lia | lia | lia | lia
      | exact PSTK | exact PIMG | exact PHB | exact PHBS ]. }
  cbv beta. intros ms1 (m1 & -> & MU & WM & MI1 & ST1 & FR1).
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1.
  destruct (BACK mo1 Hag1 HLI1) as [AHKb R1].
  assert (AHK1 : y_AHK Y s REST LF m1 mo1).
  { eapply FRAMEY; [exact AHKb| exact MU| exact WM|]. constructor; [left; cbn [fst snd]; aceil; lia| constructor]. }
  clear AHKb.
  pose proof (aystatics_munch _ _ _ YS MU WM ltac:(constructor; [cbn [fst snd]; lia| constructor])) as YS1.
  eapply (rw_cells_transport bsegs) in YAF; [| exact MU| exact WM| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  assert (PRES1 : ay_pres REST LF (bv_unsigned sp) [] m m1).
  { eapply ay_pres_of_munch; [exact MU| exact WM|]. intros a Ha Hc _.
    eapply (ay_client_outside_stack Y BLKY LAYY _ _ _ _ _ REST (bv_unsigned sp)); [exact AHK0| intros b0 Hb0; exact Hb0| aceil; lia| lia| exact Hc]. }
  clear LINK BACK PSTK PIMG PHB PHBS HBSu G1 G2 G3 G4. unfold ALEXA_MAL_RET.
  (* [comment removed for export] *)
  name_sp sp (-48)%Z. rewrite <- Hsp in ST1.
  eapply (WMAL 48 REST LF lo (y_acharge Y 32 + y_phi_buf Y ybuf_zero + y_free_cost Y + RR));
    [ exact K0
    | apply AYST_split; split; [exact AHK1| exact YS1]
    | reflexivity
    | lia
    | lia
    | lia
    | unfold AY_NBIG_REST in NBIG; lia
    | unfold ayframe_pre, AY_WRAP_STACK, AMALLOC_STACK; aceil;
      split; [exact ST1|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [Z.div_mod_to_equations; lia|];
      split; [exact MI1|]; split; [exact TP| exact FRM]
    | apply UTRIV; [rewrite unsigned_lit by lia; aceil; lia| rewrite unsigned_lit by lia; exact URA_mal]
    | ].
  cbv beta. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 m2 mo2 sa2 Lx (MI2 & ST2 & FRM2 & WM2 & PRES2) SO2 R2 CRED2 RES.
  unname_sp.
  pose proof (aypres_frame _ _ _ _ _ _ _ PRES2 FR1 ltac:(lia)) as FR2. clear FR1.
  pose proof (aypres_block _ _ _ _ _ _ _ PRES2 YAF ltac:(exists hb; split; [exact HBI| cbn; lia])) as YAF2. clear YAF.
  assert (PRES2w : ay_pres REST LF (bv_unsigned sp) [] m m2).
  { eapply ay_pres_trans; [exact PRES1|]. eapply (ay_pres_weaken Y); [exact PRES2| lia| intros b0 Hb0; exact Hb0| auto| auto]. }
  destruct RES as (EA0 & LXR & LXAM & LXHI & LXS & (junk0 & NEW) & AY2). subst a0'. unfold wz.
  unfold ablock_range, ACONSTS in LXR. cbn [c_img_hi] in LXR. aceil.
  pose proof (LXHI ltac:(clear; lia)) as LXSH. unfold oshw_hi, A_SB in LXSH.   (* [comment removed for export] *)
  assert (LXSH2 : 17594333495296 <= Lx) by (revert LXSH CEILB; clear; intros H CEILB; cbn in H; lia). clear LXSH LXHI.
  apply AYST_split in AY2. destruct AY2 as [AHK2 YS2].
  destruct (ICPB _ _ _ _ _ (mkABlock Lx 48) Lx 48 AHK2 (or_introl eq_refl) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia)) as (ws & SW & RC & _ & _).
  pose proof (ICPR _ _ _ _ _ (mkABlock Lx 48) Lx 48 AHK2 (or_introl eq_refl) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia)) as PGW.
  pose proof (ICPG _ _ _ _ _ AHK2) as IG2. unfold A_SB in SW, RC, PGW, IG2.
  pose proof (shw_geom 2147450880 Lx 48 ltac:(lia) ltac:(lia) ltac:(lia)) as GEO. cbv zeta in GEO.
  (* [comment removed for export] *)
  arz_seg KIPY AHK2. ret_pc_lit.
  pose proof (aypol_stack Y _ LF _ _ LINK lo (bv_unsigned sp) ltac:(aceil; lia) ltac:(lia)) as PSTK.
  pose proof (aypol_img Y _ LF _ _ LINK) as PIMG. unfold AY_IMG_LO, AY_IMG_HI in PIMG.
  pose proof (aypol_opol_block Y _ LF _ _ LINK (mkABlock Lx 48) (or_introl eq_refl) ltac:(cbn; lia) ltac:(cbn; unfold oshw_lo, A_SB; lia) ltac:(cbn; unfold oshw_hi, A_SB, amem; lia) ltac:(cbn; lia)) as [PL _].
  pose proof (aypol_pages (m_vm_lazy mo2) _ _ _ PGW ltac:(unfold shw_lo, al8 in *; Z.div_mod_to_equations; lia) ltac:(lia)) as PWL.
  cbn [ab_addr ab_size] in PL.
  eapply evtA_cut.
  { eapply (alexa2_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AF aC v8 lo (bv_unsigned sp + -48) Lx junk0 ws);
      [ exact ST2 | exact MI2 | lia | lia | lia | exact NEW | exact IG2 | exact SW | exact RC | lia | lia | lia | lia
      | intros a k Ha Hk; apply PSTK; lia | intros a k Ha Hk; apply PIMG; lia | exact PL | exact PWL ]. }
  cbv beta. intros ms3 (t0x & t1x & t2x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m3 & -> & MU3 & WM3 & MI3 & ST3 & LXC3).
  apply evtA_done. intros mo3 Hag3 HLI3 Hh3.
  eapply (rw_cells_transport bsegs) in FR2; [| exact MU3| exact WM3| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  destruct (BLKY _ _ _ _ _ AHK2) as (_ & SEP2 & ND2).
  pose proof (SEP2 _ _ (or_introl eq_refl) (or_intror HBI) (nd_head_ne _ _ _ ND2 HBI)) as SLH. cbn [ab_addr ab_size] in SLH.
  eapply (rw_cells_transport bsegs) in YAF2; [| exact MU3| exact WM3| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; clear -CEILB SLH HB1 HB2 HBR CEIL LO; lia].
  destruct (BACK mo3 Hag3 HLI3) as [AHKb R3].
  assert (AHK3 : y_AHK Y sa2 (mkABlock Lx 48 :: REST) LF m3 mo3).
  { eapply FRAMEY; [exact AHKb| exact MU3| exact WM3|].
    constructor; [left; cbn [fst snd]; aceil; lia|].
    constructor; [right; left; eexists; split; [left; reflexivity| cbn; lia]| constructor]. }
  clear AHKb.
  pose proof (aystatics_munch _ _ _ YS2 MU3 WM3 ltac:(constructor; [cbn [fst snd]; lia| constructor; [cbn [fst snd]; lia| constructor]])) as YS3.
  assert (PRES3w : ay_pres REST LF (bv_unsigned sp) [] m m3).
  { eapply ay_pres_trans; [exact PRES2w|]. eapply ay_pres_of_munch; [exact MU3| exact WM3|]. intros a Ha Hc _. apply outside_cons; [| apply outside_cons; [| exact I]].
    - eapply (ay_client_outside_stack Y BLKY LAYY _ _ _ _ _ REST (bv_unsigned sp)); [exact AHK2| intros b0 Hb0; right; exact Hb0| aceil; lia| lia| exact Hc].
    - eapply (ay_client_outside_block Y BLKY BSHY LAYY _ _ _ _ _ REST (bv_unsigned sp) (mkABlock Lx 48));
        [exact AHK2| left; reflexivity| | cbn; lia| cbn; lia| lia| aceil; lia| exact Hc].
      intros b0 Hb0. split; [right; exact Hb0|]. cbn. intros E. exact (nd_head_ne _ _ _ ND2 Hb0 (eq_sym E)). }
  clear LINK BACK PSTK PIMG PL PWL SW RC PGW IG2. unfold ALEXA_BA_RET.
  (* [comment removed for export] *)
  name_sp sp (-48)%Z. rewrite <- Hsp in ST3.
  eapply (BALLOC LF (mkABlock Lx 48 :: REST) AF lo (y_free_cost Y + RR));
    [ split; [exact AFP| exact AFA8]                              (* [comment removed for export] *)
    | exact K0
    | apply AYST_split; split; [exact AHK3| exact YS3]
    | exact YAF2
    | exists hb; split; [right; exact HBI|]; split; [exact HB1|]; split; [exact HB2|]; split; [exact AF8|]; split; [| exact HBHI];
      exact (proj1 (BSHY _ _ _ _ _ hb AHK3 (or_intror HBI) ltac:(lia)))
    | unfold ayframe_pre, AY_BUF_ALLOC_STACK, AMALLOC_STACK; aceil;
      split; [exact ST3|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [Z.div_mod_to_equations; lia|];
      split; [exact MI3|]; split; [exact TP| exact FRM2]
    | reflexivity
    | unfold SIZEOF_BUF; lia
    | lia
    | change (nbig (mkABlock Lx 48 :: REST)) with (nbig REST); exact NBIG
    | apply UTRIV; [rewrite unsigned_lit by lia; aceil; lia| rewrite unsigned_lit by lia; exact URA_ba]
    | ].
  cbv beta. intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F4 fc4 m4 mo4 sa4 B0 (SO4 & R4 & CRED4 & (MI4 & ST4 & FRM4 & WM4 & PRES4) & YAF4 & RES4).
  unname_sp.
  pose proof (aypres_frame _ _ _ _ _ _ _ PRES4 FR2 ltac:(lia)) as FR4. clear FR2.
  pose proof (aypres_block _ _ _ _ _ _ _ PRES4 LXC3 ltac:(eexists; split; [left; reflexivity| cbn; lia])) as LXC4. clear LXC3.
  assert (PRES4w : ay_pres REST LF (bv_unsigned sp) [] m m4).
  { eapply ay_pres_trans; [exact PRES3w|]. eapply (ay_pres_weaken Y); [exact PRES4| lia| intros b0 Hb0; right; exact Hb0| auto| auto]. }
  destruct RES4 as (EA & B0P & B0SH & BST & B0S & AY4). unfold SIZEOF_BUF in BST, B0S, AY4. subst a0''.
  destruct BST as (BC & _ & _ & _). unfold buf_cells, ybuf_zero in BC. cbn [yb_state yb_len yb_used buf_state_code] in BC. unfold wz in BC.
  unfold oshw_hi, A_SB in B0SH. assert (B0SH2 : 17594333495296 <= B0) by (revert B0SH CEILB; clear; intros H CEILB; cbn in H; lia).
  apply AYST_split in AY4. destruct AY4 as [AHK4 YS4]. pose proof YS4 as (_ & _ & _ & STA4). ay_statics_open STA4.
  destruct (BLKY _ _ _ _ _ AHK4) as (RNG4 & SEP4 & ND4).
  pose proof (RNG4 _ (or_introl eq_refl)) as B0R. unfold ablock_range in B0R; aceil. cbn [ab_addr ab_size] in B0R.
  pose proof (SEP4 _ _ (or_introl eq_refl) (or_intror (or_introl eq_refl)) (nd_head_ne _ _ _ ND4 (or_introl eq_refl))) as SB0L. cbn [ab_addr ab_size] in SB0L.
  assert (HL4 : In (mkABlock Lx 48) (mkABlock B0 32 :: mkABlock Lx 48 :: REST)) by (right; left; reflexivity).
  assert (HR4 : forall b, In b REST -> In b (mkABlock B0 32 :: mkABlock Lx 48 :: REST)) by (intros b0 Hb0; right; right; exact Hb0).
  pose proof (BSHY _ _ _ _ _ (mkABlock Lx 48) AHK4 HL4 ltac:(cbn; lia)) as [LS4 _]. cbn [ab_addr ab_size] in LS4. destruct LS4 as (_ & _ & LSu4). unfold A_SB in LSu4.
  destruct B0S as (_ & _ & RSu4). unfold A_SB in RSu4.
  (* [comment removed for export] *)
  arz_seg KIPY AHK4. ret_pc_lit.
  pose proof (aypol_stack Y _ LF _ _ LINK lo (bv_unsigned sp) ltac:(aceil; lia) ltac:(lia)) as PSTK.
  pose proof (aypol_opol_block Y _ LF _ _ LINK (mkABlock Lx 48) HL4 ltac:(cbn; lia) ltac:(cbn; unfold oshw_lo, A_SB; lia) ltac:(cbn; unfold oshw_hi, A_SB, amem; lia) ltac:(cbn; lia)) as [PL PLS].
  cbn [ab_addr ab_size] in PL, PLS. unfold oshw_lo, oshw_hi, A_SB, amem in PL, PLS.
  eapply evtA_cut.
  { eapply (alexa3_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F4 fc4 m4 AF aC v8 lo (bv_unsigned sp + -48) Lx B0 _);
      [ exact ST4 | exact MI4 | lia | lia | lia | exact FR4 | exact LXC4 | exact LSu4 | reflexivity
      | lia | lia | lia | lia | lia | lia | lia | lia
      | intros a k Ha Hk; apply PSTK; lia | exact PL | intros a k Ha Hk; apply PLS; lia ]. }
  cbv beta. intros ms5 (t0y & t1y & t2y & a1y & a2y & a3y & a4y & a5y & a6y & a7y & t3y & t4y & t5y & t6y & m5 & -> & MU5 & WM5 & MI5 & ST5 & LXC5).
  eapply (u8arr_transport bsegs) in LSu4; [| exact MU5| exact WM5| cbv [disjoint_from fst snd]; rewrite (blk_shadow_length 48) by lia; lia].
  eapply (u8arr_transport bsegs) in RSu4; [| exact MU5| exact WM5| cbv [disjoint_from fst snd]; rewrite (blk_shadow_length 32) by lia; lia].
  pose proof (aypres_block _ _ _ _ _ _ _ PRES4 YAF2 ltac:(exists hb; split; [right; exact HBI| cbn; lia])) as YAF4'.
  pose proof (SEP4 _ _ (or_intror (or_introl eq_refl)) (or_intror (or_intror HBI)) (nd_head_ne _ _ _ (nd_tail _ _ ND4) HBI)) as SLH4. cbn [ab_addr ab_size] in SLH4.
  eapply (rw_cells_transport bsegs) in YAF4'; [| exact MU5| exact WM5| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; clear -CEILB SLH4 HB1 HB2 HBR CEIL LO; lia].
  eapply (rw_cells_transport bsegs) in BC; [| exact MU5| exact WM5| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; clear -CEILB SB0L; lia].
  apply evtA_done. intros mo5 Hag5 HLI5 Hh5. destruct (BACK mo5 Hag5 HLI5) as [AHKb R5].
  assert (AHK5 : y_AHK Y sa4 (mkABlock B0 32 :: mkABlock Lx 48 :: REST) LF m5 mo5).
  { eapply FRAMEY; [exact AHKb| exact MU5| exact WM5|].
    constructor; [right; left; exists (mkABlock Lx 48); split; [exact HL4| cbn; lia]| constructor]. }
  pose proof (aystatics_munch _ _ _ YS4 MU5 WM5 ltac:(constructor; [cbn [fst snd]; lia| constructor])) as YS5.
  assert (PRES5 : ay_pres REST LF (bv_unsigned sp) [] m m5).
  { eapply ay_pres_trans; [exact PRES4w|]. eapply ay_pres_of_munch; [exact MU5| exact WM5|]. intros a Ha Hc _. apply outside_cons; [| exact I].
    eapply (ay_client_outside_block Y BLKY BSHY LAYY _ _ _ _ _ REST (bv_unsigned sp) (mkABlock Lx 48));
      [exact AHK4| exact HL4| | cbn; lia| cbn; lia| lia| aceil; lia| exact Hc].
    intros b0 Hb0. split; [exact (HR4 _ Hb0)|]. cbn. intros E.
    destruct (BLKY _ _ _ _ _ AHK3) as (_ & _ & ND3). exact (nd_head_ne _ _ _ ND3 Hb0 (eq_sym E)). }
  clear LINK BACK PSTK PL PLS.
  (* [comment removed for export] *)
  replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) in * by lia. rewrite Z_to_bv_bv_unsigned.
  eapply (CONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F4 fc4 m5 mo5 sa4 Lx (mkMB (0%N, 0, 0) B0 (0%N, 0, 0) 0) (mkLexer 0 0 LE_ok ybuf_zero 0%nat 0 0 aC v8)).
  unfold aylex_alloc_rpost.
  split; [rewrite SO4; exact SO2|].
  split; [eapply RRT; [exact R1|]; eapply RRT; [exact R2|]; eapply RRT; [exact R3|]; eapply RRT; [exact R4| exact R5]|].
  split; [cbn [lx_buf] in CRED4 |- *; lia|].
  split.
  { split; [exact MI5|]. split; [exact ST5|]. split; [exact FRM4|]. split.
    - exact I.
    - exact PRES5. }
  split; [exact YAF4'|].
  cbv beta iota. split; [reflexivity|]. split; [lia|]. split; [unfold oshw_hi, A_SB; cbn; lia|]. split; [unfold oshw_hi, A_SB; cbn; clear -B0SH2; lia|].
  split; [exists 0%nat; unfold ylex_alloc; apply (yleaf_bind _ _ (Some 0%nat)); [apply yleaf_ymalloc'|]; cbn beta iota;
          apply (yleaf_bind _ _ (Some 0%nat)); [unfold ybuf_alloc; apply yleaf_ymalloc'| apply yl_ret]|].
  split.
  { split.
    - split; [| cbn; lia]. unfold lexer_cells. cbn [lx_lineOff lx_charOff lx_error lex_error_code lx_bufOff lx_bufInUse lx_allowComments lx_validateUTF8 mb_addr]. unfold wz. exact LXC5.
    - split; [| split; [cbn; exact I| cbn; constructor]].
      split; [unfold buf_cells, ybuf_zero; cbn [buf_state_code yb_state yb_len yb_used mb_addr mb_data lx_buf]; unfold wz; exact BC| split; [cbn; tauto| cbn; lia]]. }
  split; [reflexivity|].
  split; [unfold oshadow, block_shadow, A_SB, SIZEOF_LEXER; split; [lia|]; split; [lia|]; exact LSu4|].
  split; [unfold oshadow, block_shadow, A_SB, SIZEOF_BUF; cbn [mb_addr]; split; [lia|]; split; [lia|]; exact RSu4|].
  apply AYST_split. split; [| exact YS5].
  cbn [buf_blocks yb_data ybuf_zero mb_id mb_addr mb_did mb_data abl map blk_addr blk_size fst snd app lx_buf].
  eapply PERMY; [exact AHK5| apply Permutation.perm_swap| apply Permutation.Permutation_refl].
Qed.
End W.
End RC__1.

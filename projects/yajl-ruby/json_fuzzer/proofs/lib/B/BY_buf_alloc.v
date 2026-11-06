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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BY_ubkit B_iface BI_shadow BI_asan_memset BYajlRep BYajl_iface BY_rz.
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
Hypothesis LAYY : AHK_y_layout_stmt Y.
Hypothesis RRT : ayR_trans_stmt Y.
Hypothesis NONNEG : yacct_nonneg_stmt Y.
Hypothesis WMAL : aywrap_malloc_stmt Y.
(* [comment removed for export] *)
Variable URA : list Z.
Hypothesis UTRIV : forall m SP ra s0, bv_unsigned s0 < alloc_ceiling -> In (bv_unsigned ra) URA -> y_uanchor Y m SP ra s0.
Hypothesis URA_site1 : In 0x86ff8 URA.                                          (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis ICPG : forall s LB LF m mo, y_AHK Y s LB LF m mo -> icp_globals bsegs m A_SB.
Hypothesis ICPB : forall s LB LF m mo b A n, y_AHK Y s LB LF m mo -> In b LB ->
    ab_addr b <= A -> 1 <= n -> A + n <= ab_addr b + ab_size b ->
    exists ws, shadow_window bsegs m A_SB A n ws /\ range_clean A_SB A n ws
               /\ shw_hi A_SB A n <= 0x10007fff8000 /\ amem (ab_addr b) (ab_size b).   (* [comment removed for export] *)   (* [comment removed for export] *)
Hypothesis ICPR : forall s LB LF m mo b A n, y_AHK Y s LB LF m mo -> In b LB -> ab_addr b <= A -> 1 <= n -> A + n <= ab_addr b + ab_size b ->
    pages_budgeted (y_aS Y s) (shw_lo A_SB A) (shw_hi A_SB A n).

Ltac ay_statics_open STA :=
  let G1 := fresh "G1" in let G2 := fresh "G2" in let G3 := fresh "G3" in let G4 := fresh "G4" in
  destruct STA as (G1 & G2 & G3 & G4);
  unfold AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz in G1, G2, G3, G4.

Theorem aybuf_alloc_proof : aybuf_alloc_stmt Y.
Proof. aceil.
  unfold aybuf_alloc_stmt. intros LF REST AF lo RR K. intros until s. intros [AFP AFA8] K0 AY YAF AFOK FP EA CRED RR0 NBIG UA CONT. subst a0.
  destruct FP as (ST & CEIL & LO & SPH & SP16 & MI & TP & FRM).
  apply AYST_split in AY. destruct AY as [AHK0 YS]. pose proof YS as (_ & _ & _ & STA).
  destruct AFOK as (hb & HBIN & HB1 & HB2 & AF8 & HBS & HBHI).
  destruct (BLKY _ _ _ _ _ AHK0) as (RNG & SEP & ND).
  pose proof (RNG hb HBIN) as HBR. unfold ablock_range, ACONSTS in HBR. cbn [c_img_hi] in HBR.
  pose proof HBHI as HBSH.   (* [comment removed for export] *)
  pose proof (rw_cells_bound _ _ _ _ YAF) as YAFB. cbn [cells_size csize Nat.add alloc_cells length] in YAFB.
  unfold AY_BUF_ALLOC, AY_BUF_ALLOC_STACK, AMALLOC_STACK, wz in *.
  aceil.
  unfold oshw_hi, A_SB, amem in HBSH. assert (HBSH2 : 17594333495296 <= ab_addr hb) by (revert HBSH CEILB; clear; intros HBSH CEILB; cbn in HBSH; lia). clear HBSH.
  ay_statics_open STA.
  unfold alloc_cells in YAF. cbn [yc_malloc_w yc_realloc_w yc_free_w ayc] in YAF. unfold AY_MALLOC_W, AY_REALLOC_W, AY_FREE_W, wz in YAF.
  pose proof (block_shadow_bound bsegs m _ _ _ HBS) as HBSB. unfold A_SB in HBSB.
  unfold oshadow, A_SB in HBS. open_shadow HBS.
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  arz_seg KIPY AHK0.
  pose proof (aypol_stack Y REST LF _ _ LINK) as PSTK. pose proof (aypol_img Y REST LF _ _ LINK) as PIMG.
  pose proof (aypol_opol_block Y REST LF _ _ LINK hb HBIN ltac:(lia) ltac:(unfold oshw_lo, A_SB; lia) ltac:(unfold oshw_hi, A_SB, amem; lia) ltac:(lia)) as [PHB PHBS].
  unfold pol, oshw_lo, oshw_hi, A_SB, amem, AY_IMG_LO, AY_IMG_HI in PSTK, PIMG, PHB, PHBS; aceil.
  specialize (PSTK (bv_unsigned sp + -32) (bv_unsigned sp) ltac:(lia) ltac:(lia)).
  carve_frame 32%nat ST.
  do 5 stepA.                                         (* [comment removed for export] *)
  ugd.                                                (* [comment removed for export] *)
  stepA.                                              (* [comment removed for export] *)
  zstepA. ugd.                                        (* [comment removed for export] *)
  do 3 stepA.                                         (* [comment removed for export] *)
  shadow_fast HBS AF 8.                               (* [comment removed for export] *)
  zstepA.                                             (* [comment removed for export] *)
  shadow_fast HBS (AF + 24) 8.                        (* [comment removed for export] *)
  zstepA. zstepA. stepA.                              (* [comment removed for export] *)
  stepA.                                              (* [comment removed for export] *)
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1.
  (* [comment removed for export] *)
  lazymatch type of MU with munch _ _ ?mx => rename mx into m1 end.
  assert (AHK1 : y_AHK Y s REST LF m1 mo1).
  { destruct (BACK mo1 Hag1 HLI1) as [AHKb _].
    eapply FRAMEY; [exact AHKb| exact MU| exact WM|].
    constructor; [| constructor]. left. cbn. aceil. lia. }
  pose proof (proj2 (BACK mo1 Hag1 HLI1)) as R1.
  pose proof (aystatics_munch _ _ _ YS MU WM ltac:(constructor; [cbn; lia| constructor])) as YS1.
  rename MU into MU0. rename WM into WM0.
  clear LINK BACK Hh HLI Hmi.
  (* [comment removed for export] *)
  name_sp sp (-32)%Z. rewrite <- Hsp in ST.
  eapply (WMAL 32 REST LF lo (y_phi_buf Y ybuf_zero + RR)).
  - exact K0.
  - apply AYST_split. split; [exact AHK1| exact YS1].
  - reflexivity.
  - lia.
  - unfold SIZEOF_BUF in CRED. lia.
  - destruct NONNEG as (_ & NB0 & _). pose proof (NB0 ybuf_zero). lia.
  - unfold AY_NBIG_REST in NBIG. lia.
  - unfold ayframe_pre, AY_WRAP_STACK, AMALLOC_STACK; aceil.
    split; [exact ST|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [Z.div_mod_to_equations; lia|].
    split; [assumption|]. split; [exact TP| exact FRM].
  - apply UTRIV; [rewrite unsigned_lit by lia; aceil; lia| rewrite unsigned_lit by lia; exact URA_site1].
  - cbv beta. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 m2 mo2 sa2 B0 (MI2 & ST2 & FRM2 & WM2 & PRES2) SO2 R2 CRED2 RES.
    unname_sp.
    (* [comment removed for export] *)
    pose proof (aypres_frame _ _ _ _ _ _ _ PRES2 FR ltac:(lia)) as FR2. clear FR.
    pose proof (aypres_block _ _ _ _ _ _ _ PRES2 YAF ltac:(exists hb; split; [exact HBIN| cbn; lia])) as YAF2. clear YAF.
    clear G1 G2 G3 G4 HBS YS YS1 PSTK PIMG PHB PHBS.
    assert (PRES2w : ay_pres REST LF (bv_unsigned sp) [] m m2).
    { eapply ay_pres_trans.
      - eapply ay_pres_of_munch; [exact MU0| exact WM0|].
        intros a Ha Hc _. eapply (ay_client_outside REST LF); [ | | | | exact Hc].
        + intros b Hb. pose proof (RNG b Hb) as Rb. unfold ablock_range in Rb. lia.
        + intros f Hf. destruct (proj1 (LAYY _ _ _ _ _ AHK0) f Hf) as (L1 & L2 & L3 & L4 & L5). unfold oshw_hi, A_SB, amem in L1. lia.
        + aceil; lia.
        + lia.
      - eapply (ay_pres_weaken Y); [exact PRES2| lia| auto| auto| auto]. }
    clear PRES2.
    (* [comment removed for export] *)
    + (* [comment removed for export] *)
      destruct RES as (EA0 & BR & B0AM & B0HI & B0S & (junk2 & NEW) & AY2). pose proof (B0HI ltac:(clear; lia)) as B0SH. clear B0HI. subst a0'.
      unfold ablock_range, ACONSTS in BR. cbn [c_img_hi] in BR. aceil. unfold oshw_hi, A_SB, amem in B0SH.
      assert (B0SH2 : 17594333495296 <= B0) by (revert B0SH CEILB; clear; intros H CEILB; cbn in H; lia). clear B0SH.
      apply AYST_split in AY2. destruct AY2 as [AHK2 YS2]. pose proof YS2 as (_ & _ & _ & STA2). ay_statics_open STA2.
      destruct (BLKY _ _ _ _ _ AHK2) as (RNG2 & SEP2 & ND2).
      assert (NE : B0 <> ab_addr hb).
      { cbn [map ab_addr] in ND2. apply List.NoDup_cons_iff in ND2. destruct ND2 as [NI _]. intros E. apply NI. rewrite E. apply in_map. exact HBIN. }
      assert (SEPhb : ab_addr hb + ab_size hb <= B0 \/ B0 + 32 <= ab_addr hb).
      { destruct (SEP2 (mkABlock B0 SIZEOF_BUF) hb (or_introl eq_refl) (or_intror HBIN) NE) as [X|X]; cbn [ab_addr ab_size] in X; unfold SIZEOF_BUF in X; lia. }
      (* [comment removed for export] *)
      pose proof (block_shadow_bound bsegs m2 _ _ _ B0S) as B0SB. unfold A_SB in B0SB.
      pose proof B0S as B0S'. unfold oshadow, A_SB in B0S. open_shadow B0S.
      (* [comment removed for export] *)
      pose proof (ICPG _ _ _ _ _ AHK2) as IG2.
      destruct (ICPB _ _ _ _ _ (mkABlock B0 SIZEOF_BUF) B0 32 AHK2 (or_introl eq_refl) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; unfold SIZEOF_BUF; lia)) as (ws & SW & RC & SWHI & _).
      pose proof (ICPR _ _ _ _ _ (mkABlock B0 SIZEOF_BUF) B0 32 AHK2 (or_introl eq_refl) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; unfold SIZEOF_BUF; lia)) as PGW.
      pose proof (shw_geom A_SB B0 32 ltac:(unfold A_SB; lia) ltac:(lia) ltac:(lia)) as GEO. cbv zeta in GEO. unfold A_SB in GEO, SW, RC, SWHI, PGW, IG2.
      (* [comment removed for export] *)
      pose proof (munch_refl [(lo, bv_unsigned sp); (B0, B0 + 32)] m2) as MU. pose proof (wmono_refl bsegs m2) as WM.
      arz_seg KIPY AHK2.
      pose proof (aypol_stack Y _ LF _ _ LINK lo (bv_unsigned sp) ltac:(aceil; lia) ltac:(lia)) as PSTK.
      pose proof (aypol_img Y _ LF _ _ LINK) as PIMG.
      pose proof (aypol_opol_block Y _ LF _ _ LINK (mkABlock B0 SIZEOF_BUF) (or_introl eq_refl) ltac:(cbn; lia) ltac:(cbn; unfold oshw_lo, A_SB; lia) ltac:(cbn; unfold oshw_hi, A_SB, amem, SIZEOF_BUF; lia) ltac:(cbn; unfold SIZEOF_BUF; lia)) as [PB0 PB0S].
      pose proof (aypol_pages (m_vm_lazy mo2) _ _ _ PGW ltac:(unfold shw_lo, al8 in *; Z.div_mod_to_equations; lia) ltac:(lia)) as PWIN.
      cbn [ab_addr ab_size] in PB0, PB0S. unfold pol, oshw_lo, oshw_hi, A_SB, amem, AY_IMG_LO, AY_IMG_HI, SIZEOF_BUF in PSTK, PIMG, PB0, PB0S, PWIN.
      clear Hh HLI Hmi. ret_pc_lit. unfold wz.
      zstepA. if_cases K1; zify_cond K1. { exfalso. revert K1. rewrite ?unsigned_lit by lia. lia. }   (* [comment removed for export] *)
      stepA. stepA. stepA.                            (* [comment removed for export] *)
      stepA.                                          (* [comment removed for export] *)
      call_spA (asan_memset_small_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ B0 0 32 2147450880 ws junk2 lo).
      * exact ST2.
      * aceil; lia.
      * lia.
      * exact MI2.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * lia.
      * lia.
      * lia.
      * left. aceil. lia.
      * right. lia.
      * exact NEW.
      * exact IG2.
      * exact SW.
      * exact RC.
      * left. unfold shw_hi, al8 in *. lia.
      * intros a k Ha Hk. apply PSTK; lia.
      * intros a k Ha Hk. apply PIMG; lia.
      * intros a k Ha Hk. apply PB0; lia.
      * exact PWIN.
      * lazymatch goal with H : stk bsegs ?mx lo _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into ST3 end.
        (* [comment removed for export] *)
        lazymatch goal with H : rw_cells bsegs ?mx B0 [CB _ (repeat _ _)] |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
          pose proof (rw_cells_split_CB bsegs mx B0 [] 32 (repeat (Z_to_bv 8 0) 32) [] [24%nat; 8%nat] H eq_refl) as NEW'; clear H;
          cbn [app mk_CB_cells firstn skipn repeat] in NEW';
          destruct (proj1 (ycells_app bsegs mx B0 [CB 24 (repeat (Z_to_bv 8 0) 24)] [CB 8 (repeat (Z_to_bv 8 0) 8)]) NEW') as [Z24 D8]; clear NEW';
          cbn [cells_size csize Nat.add] in D8; change (Z.of_nat 24) with 24 in D8 end.
        zstepA. ugd.                                  (* [comment removed for export] *)
        zstepA.                                       (* [comment removed for export] *)
        shadow_fast B0S (B0 + 24) 8.                  (* [comment removed for export] *)
        zstepA.                                       (* [comment removed for export] *)
        stepA. stepA.                                 (* [comment removed for export] *)
        do 5 stepA.                                   (* [comment removed for export] *)
        stepA.                                        (* [comment removed for export] *)
        lazymatch goal with H : rw_cells bsegs ?mx (bv_unsigned sp + -32) _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => release_frame H ST3 (bv_unsigned sp) end.
        apply evtA_done. intros mo3 Hag3 HLI3 Hh3.
        lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into mf end.
        lazymatch goal with H : rw_cells bsegs mf B0 [CB _ (repeat _ _)] |- _ => rename H into Z24 end.
        lazymatch goal with H : rw_cells bsegs mf (B0 + 24) _ |- _ => rename H into D8f end.
        lazymatch goal with H : rw_cells bsegs mf AF _ |- _ => rename H into YAFf end.
        lazymatch goal with H : mem_inv bsegs mf |- _ => rename H into MIf end.
        lazymatch goal with H : stk bsegs mf lo _ |- _ => rename H into STf end.
        (* [comment removed for export] *)
        destruct (BACK mo3 Hag3 HLI3) as [AHK2b R3].
        assert (AHKf : y_AHK Y sa2 (mkABlock B0 SIZEOF_BUF :: REST) LF mf mo3).
        { eapply FRAMEY; [exact AHK2b| exact MU| exact WM|].
          constructor; [left; cbn; aceil; lia|].
          constructor; [| constructor]. right; left. exists (mkABlock B0 SIZEOF_BUF). split; [left; reflexivity| cbn; unfold SIZEOF_BUF; lia]. }
        pose proof (aystatics_munch _ _ _ YS2 MU WM ltac:(constructor; [cbn; aceil; lia| constructor; [cbn; lia| constructor]])) as YSf.
        (* [comment removed for export] *)
        pose proof (proj2 (ycells_app bsegs mf B0 [CB 24 (repeat (Z_to_bv 8 0) 24)] [C8 (Z_to_bv 64 AF)]) (conj Z24 D8f)) as BC. cbn [app] in BC.
        eapply (CONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 mf mo3 sa2 B0). unfold aybuf_alloc_rpost.
        split; [exact SO2|]. split; [eapply RRT; [exact R1| eapply RRT; [exact R2| exact R3]]|]. split; [exact CRED2|].
        split.
        { split; [exact MIf|]. split; [exact STf|]. split; [exact FRM2|]. split.
          - exact I.
          - eapply ay_pres_trans; [exact PRES2w|]. eapply ay_pres_of_munch; [exact MU| exact WM|].
            intros a Ha Hc _. cbn. split; [| split; [| exact I]].
            + eapply (ay_client_outside REST LF (bv_unsigned sp) lo (bv_unsigned sp) a) in Hc.
              * cbn in Hc. tauto.
              * intros b Hb. pose proof (RNG b Hb) as Rb. unfold ablock_range in Rb. lia.
              * intros f Hf. destruct (proj1 (LAYY _ _ _ _ _ AHK0) f Hf) as (L1 & L2 & L3 & L4 & L5). unfold oshw_hi, A_SB, amem in L1. lia.
              * aceil; lia.
              * lia.
            + destruct Hc as [Hc|[(b & Hb & Hr)|[(f & Hf & Hr)|Hc]]].
              * lia.
              * assert (NEb : B0 <> ab_addr b).
                { cbn [map ab_addr] in ND2. apply List.NoDup_cons_iff in ND2. destruct ND2 as [NI _]. intros E. apply NI. rewrite E. apply in_map. exact Hb. }
                destruct (SEP2 (mkABlock B0 SIZEOF_BUF) b (or_introl eq_refl) (or_intror Hb) NEb) as [X|X]; cbn [ab_addr ab_size] in X; unfold SIZEOF_BUF in X; lia.
              * destruct (proj1 (proj2 (LAYY _ _ _ _ _ AHK2)) f (mkABlock B0 SIZEOF_BUF) Hf (or_introl eq_refl)) as [X1 X2]. cbn [ab_addr ab_size] in X1. unfold SIZEOF_BUF in X1.
                destruct (proj1 (LAYY _ _ _ _ _ AHK2) f Hf) as (L1 & L2 & L3 & L4 & L5). unfold oshw_hi, A_SB, amem in L1.
                pose proof (ff_shadow_top2 f L4 ltac:(lia) L2) as T. unfold oshw_lo, oshw_hi, A_SB, amem in T. cbn in T.
                unfold A_SB in Hr. destruct Hr; lia.
              * unfold ay_static in Hc. lia. }
        split; [exact YAFf|].
        split; [reflexivity|]. split; [lia|]. split; [unfold oshw_hi, A_SB, amem; cbn; lia|].
        split.
        { split; [| split; [cbn; tauto| cbn; lia]].
          eapply rw_cells_recast; [exact BC| cbn; repeat split; exact I| reflexivity| reflexivity]. }
        split; [unfold oshadow, block_shadow, A_SB, SIZEOF_BUF; split; [assumption|]; split; [lia|]; rewrite <- B0Seq; assumption|].
        apply AYST_split. split; [exact AHKf| exact YSf].
Qed.
End W.
End RC__1.

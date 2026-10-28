(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx HeapIfaceANull As0StepLib As0Tables
     ArtMem ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInitCache_b BatPopulate1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatClsRep_b BatCellEx_b BatByteCell_b BatCARSpec_b BatAlloc3Pure_b BatDepot_b BatUnwind_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInv_b BatInvMallocPure_b BatInvMalloc_b BatLift_b BatWrapPure_b BatWrapKit_b BatWrapMallocH_b BatWrapMallocX_b BatWrapMallocC_b BatWrapMalloc_b BatIfaceLaws_b
     BatFxImg_b BatImgCell_b BatFreeNull3_b BatInvFree_b BatInvFrameX_b BatWrapC_b BatWrapFreeC_b BatWrapFree_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Lemma art_zone_lt_HI : forall FSG rn (G : art_gs FSG) LB (Mr : word -> option byte) x,
  art_alloc_rep FSG rn G LB Mr ->
  (forall p, In p (art_live (g_log FSG G)) -> 0 < fst p /\ 0 < snd p /\ fst p + snd p <= rn_HI rn) ->
  art_alloc_zone FSG rn G x -> x < rn_HI rn.
Proof.
  intros FSG rn G LB Mr x REP LIVE HZ. pose proof REP as (ROK & _). rok_open ROK. geo_open GEO.
  assert (SHB : forall y, 0 <= y <= 2 ^ 47 -> HeapIfaceA.S y + 1 < rn_HI rn).
  { intros y Hy. unfold HeapIfaceA.S, HeapIfaceA.SB. assert (y / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8) with 17592186044416 in *. lia. }
  destruct HZ as [HZ | [HZ | [HZ | [HZ | [HZ | [HZ | [HZ | [HZ | [HZ | [HZ | [HZ | HZ]]]]]]]]]]].
  - unfold art_zone_statics in HZ. clear - HZ G1. lia.
  - unfold art_zone_thread in HZ. clear - HZ G8. lia.
  - clear - HZ G14. lia.
  - unfold art_zone_kspace in HZ. clear - HZ Kend. lia.
  - destruct HZ as [HZ | (p & Hp & HZ)]; [clear - HZ Phi; lia|]. destruct (LIVE p Hp) as (L1 & L2 & L3). clear - HZ L3. lia.
  - unfold art_zone_depot, dprivD in HZ. clear - HZ Dl2 Dblk G1. lia.
  - destruct HZ as [HZ | (p & Hp & HZ)].
    + pose proof (SHB (rn_kbase rn + 0x2000011000) ltac:(clear - Kend G2 Kspb G4; lia)). clear - HZ H. lia.
    + destruct (LIVE p Hp) as (L1 & L2 & L3). pose proof (SHB (fst p + snd p) ltac:(clear - L1 L2 L3 G2; lia)). clear - HZ H. lia.
  - clear - HZ G1. lia.
  - clear - HZ G1 G20. lia.
  - clear - HZ G1 G22 Hkey. lia.
  - clear - HZ G1. lia.
  - clear - HZ G1. lia.
Qed.

Section Wrap.
Variable FSG : Type.
Variable FSINV : art_run -> FSG -> list fframe -> list fframe -> (word -> option byte) -> Prop.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Variable L : asan_layout.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis HLsegs : hl_segs L = ASEGS.
Hypothesis HLfree : hl_free L = 0x79814.
Hypothesis HLscr : hl_scr_free L = 4096.
Hypothesis HLtp : hl_tp L = rn_tp rn.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x696000.
Hypothesis HLst : forall a, art_zone_statics a -> hl_rt_static L a.
Hypothesis FSLAW : art_fsinv_frame_law FSG FSINV.
Hypothesis FS_IN : forall gfs FF LK M, FSINV rn gfs FF LK M ->
  forall f, In f (FF ++ LK) -> ar_fs (rn_ar rn) <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= ar_fs (rn_ar rn) + FS_BYTES /\ 0 < ff_bytes (ff_class f).

#[using="Hwx HLsegs HLfree HLscr HLtp HLlo HLhi HLst FSLAW FS_IN"] Theorem art_wrap_free_null : afree_null_spec L (rn_ar rn) scfg (art_iface FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV rn).
Proof.
  intros fx R M model LB FF LK cr A K RI Hhalt HMI H10 H4 Hret AST K0 POST.
  rewrite HLsegs, HLfree. replace (Z_to_bv 64 497684) with (0x79814%bv : word) by (apply bv_eq; reflexivity).
  destruct RI as (G & REPr & FS & BV & CRED & CLI & KN & LZ & EG). cbn [vml_of fst snd] in REPr, BV, LZ, EG.
  pose proof (BINV_elim _ _ _ _ _ _ _ _ _ _ _ BV Hhalt HMI) as B0.
  pose proof REPr as (ROK & ST & TH & _ & _ & _ & _ & _ & (IA1 & IA2 & _) & _). pose proof ROK as ROK'. rok_open14 ROK'. pose proof GEO as GEO'. geo_open GEO'.
  set (Sp := U (getr R 2)) in *. assert (H2 : getr R 2 = Z_to_bv 64 Sp) by (unfold Sp; symmetry; apply Z_to_bv_bv_unsigned).
  rewrite HLscr in AST. destruct AST as (S16 & SHI & SLE & STOP & SWR & SDEF).
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity. rewrite HIeq in SHI.
  pose proof CLI as (CB & CND & _ & _ & CS1 & CS2 & CS3 & CS4 & CS5 & CS6 & _ & CSP & _). rewrite HIeq in CS1, CS2.
  set (Mr0 := mrestrict (mkH (m_vm_lazy model) A) M) in *.
  pose proof (art_live_of_binv MAPS0 RESV0 NOACC0 BASE BUDGET rn _ _ _ _ B0 KN) as LIVE.
  assert (W0 : wrA Mr0 (Sp - 4096) 4096). { apply (art_stack_wr FSG rn G A (m_vm_lazy model) M Sp 4096 ROK LZ ltac:(lia) ltac:(lia) ltac:(lia)). rewrite <- HLsegs. exact SWR. }
  assert (RD0 : readable8 Mr0 Sp (ar_stack_top (rn_ar rn))). { apply (art_stack_readable FSG rn G A (m_vm_lazy model) M Sp (ar_stack_top (rn_ar rn)) ROK LZ ltac:(lia) ltac:(lia) SDEF). }
  set (raw0 := getr R 1) in *.
  assert (H4' : getr R 4 = Z_to_bv 64 (rn_tp rn)) by (rewrite <- HLtp; exact H4).
  assert (HS47 : Sp < 2 ^ 47) by (clear - SLE CSP; lia).
  assert (HHI : rn_HI rn + 4096 <= Sp - 4096) by (clear - SHI; lia).
  (* [comment removed for export] *)
  destruct ST as (PC & LY & T & _ & _ & DR & _ & C1 & _ & _ & _ & _ & _ & C7 & _ & C9 & _ & _ & _ & C13 & C14 & C15 & C16 & _).
  destruct TH as (Wt & T1 & T2 & T3 & T4 & T5 & T6 & LSAN0).
  destruct (art_free3_null R Mr0 (seg_rom ASEGS) raw0 Sp (rn_HI rn) 0 (rn_tp rn) (rn_key rn) (rn_tsd rn) (rn_ctx rn) (rn_t rn) (rn_spb rn) (rn_ris rn) (rn_qs rn)
              (ar_stack_top (rn_ar rn)) (ar_stack_bottom (rn_ar rn)) (g_ia FSG G)
              eq_refl Hret H2 H4' H10 eq_refl GEO HHI HS47 S16 ltac:(clear - CS1 G1; lia) ltac:(clear - CS5; lia) ltac:(clear - CS1 CS5 G1; lia) ltac:(clear - CS4; lia) Htpd Htsdd
              W0 RD0 Wt (art_img_wr_iaflag Mr0 0x1cf6c8 4 ltac:(lia) ltac:(lia) ltac:(lia)) (art_img_wr_iatab Mr0 0x140e40 0x81030 ltac:(lia) ltac:(lia) ltac:(lia))
              LY T PC C1 C13 C14 T6 T5 T3 T4 IA1
              ltac:(intros E j Hj; replace (0x140e48 + 8 * j) with (0x140e40 + 8 + 8 * j) by lia; exact (IA2 E j Hj)))
    as (R' & Mr' & RUN & P2 & P1 & PK & GRr & FRr & _ & Cia' & Ctab').
  apply (bridge_msteps ASEGS scfg Hwx MAPS0 RESV0 NOACC0 (rn_HI rn) BASE BUDGET (g_log FSG G) A (mkst R (0x79814 : word) M (seg_rom ASEGS)) model
           (mkst R' raw0 Mr' (seg_rom ASEGS)) K B0).
  { rewrite restrict_mkst. eapply msteps_trans; [apply art_free_thunk|exact RUN]. }
  intros ms' model' Est B1 RT BS. destruct (restrict_eq_mkst _ _ _ _ _ _ Est) as (Ems & EMr0). set (M1 := ms_mem ms') in *. rewrite Ems.
  assert (EMr : mrestrict (bhid A model') M1 = Mr') by (symmetry; exact EMr0).
  change (ms_mem (mkst R (0x79814 : word) M (seg_rom ASEGS))) with M in BS.
  pose proof (art_bstep_pure_frame A M M1 model model' Mr' BS EMr) as FRAME.
  pose proof (art_bstep_pure_grows A M M1 model model' Mr' BS EMr GRr) as GROW.
  pose proof (art_bstep_pure_lazy A M M1 model model' BS) as LAZY.
  assert (FR1 : forall x : word, ~ art_free_null_fp Sp (U x) -> M1 x = M x) by (intros x Hx; apply FRAME; apply FRr; exact Hx).
  assert (EQ : forall a, 0 <= a < 2 ^ 64 -> ~ art_free_null_fp Sp a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha N. apply FR1. rewrite art_u_lit by lia. exact N. }
  assert (LIVE' : forall p, In p (art_live (g_log FSG G)) -> 0 < fst p /\ 0 < snd p /\ fst p + snd p <= rn_HI rn).
  { intros p Hp. destruct (LIVE p Hp) as (L1 & L2 & L3 & _). repeat split; assumption. }
  (* [comment removed for export] *)
  assert (NFP_lo : forall a, a < rn_HI rn -> ~ art_ia_zone a -> ~ art_free_null_fp Sp a).
  { intros a Ha NI [F|[F|F]]; [clear - F Ha HHI; lia| |]; apply NI; unfold art_ia_zone; clear - F; lia. }
  assert (NFP_off : forall a, a < rn_HI rn -> (a < 0x10000 \/ 0x696000 <= a) -> ~ art_free_null_fp Sp a).
  { intros a Ha OFF. apply NFP_lo; [exact Ha|]. unfold art_ia_zone. clear - OFF. lia. }
  assert (NFP_sh : forall a, 0x7fff7000 <= a < 0x10007fff8000 -> ~ art_free_null_fp Sp a).
  { intros a Ha. apply NFP_off; [clear - Ha G1; lia|right; clear - Ha; lia]. }
  assert (RI' : art_ri_inv FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV rn LB FF LK cr A M1 (vml_of model')).
  { exists (art_gs_ia G). cbn [vml_of fst snd].
    split.
    { change (mkH (m_vm_lazy model') A) with (bhid A model'). rewrite EMr.
      apply (art_alloc_rep_frame_ia FSG MAPS0 RESV0 rn G LB Mr0 Mr' REPr GRr).
      - intros x Z NB NI. apply FRr. apply NFP_lo; [exact (art_zone_lt_HI FSG rn G LB Mr0 (U x) REPr LIVE' Z)|exact NI].
      - apply (art_cell_agree ASEGS Mr0 Mr'); [|clear - Hloff' Hloff''; lia|cbn; clear - Hloff''; lia|exact LSAN0].
        intros x Hx. cbn in Hx. apply FRr. apply NFP_lo; [clear - Hx Hloff'' G1; lia|]. unfold art_ia_zone. clear - Hx Htpd Hloff. lia.
      - exact (bi_live _ _ _ _ _ _ _ _ _ _ _ B0).
      - exact KN.
      - exact Cia'.
      - intros j Hj. replace (0x140e40 + 8 + 8 * j) with (0x140e48 + 8 * j) by lia. exact (Ctab' j Hj). }
    split.
    { change (g_fs FSG (art_gs_ia G)) with (g_fs FSG G). apply (FSLAW rn (g_fs FSG G) FF LK M M1 FS GROW). intros x Hz. apply FR1. unfold art_fs_zone in Hz. unfold FS_BYTES in *.
      destruct Hz as [HZ|[HZ|[HZ|[(HZ & NS)|[HZ|HZ]]]]].
      - apply NFP_off; [clear - HZ Fhi; lia|clear - HZ Fimg; lia].
      - apply NFP_off; [clear - HZ G8; lia|clear - HZ G9; lia].
      - apply NFP_sh. pose proof (art_S_ge (ar_fs (rn_ar rn)) 0 ltac:(clear - Flo; lia)). pose proof (art_S_lt (ar_fs (rn_ar rn) + 0xb09000) (2 ^ 44) ltac:(clear - Fhi G2; lia)). clear - HZ H H0. lia.
      - apply NFP_lo; [clear - HZ G1; lia|]. intros I. apply NS. unfold art_zone_statics. unfold art_ia_zone in I. clear - I. lia.
      - apply NFP_sh. unfold HeapIfaceA.S, HeapIfaceA.SB in HZ. change (0x10000 / 8) with 8192 in HZ. change (0x696000 / 8) with 863232 in HZ. clear - HZ. lia.
      - apply NFP_off; [clear - HZ D1; lia|clear - HZ D2; lia]. }
    split. { exact (BINV_intro _ _ _ _ _ _ _ _ _ _ _ B1). }
    split; [exact CRED|].
    split. { apply (art_client_ok_frame rn LB FF LK A M M1 CLI GROW). intros b a Hb Ha.
             destruct (CB b Hb) as (K1 & _ & _ & K4 & K5 & _). rewrite HIeq in K5.
             assert (Ra : 0x7fff7000 <= a < 0x10007fff8000).
             { unfold in_shadow_of in Ha. pose proof (art_S_ge (fst b) 0 ltac:(clear - K1; lia)). pose proof (art_S_lt (fst b + snd b - 1) (2 ^ 44) ltac:(clear - K5 G2; lia)). clear - Ha H H0. lia. }
             apply EQ; [clear - Ra; lia|exact (NFP_sh a Ra)]. }
    split; [exact KN|].
    split. { exact (art_lazy_ok_shrink FSG rn G A (m_vm_lazy model) (m_vm_lazy model') LZ LAZY). }
    destruct EG as (AW & EB). split; [exact AW|]. intros b x Hb Hx. destruct (page_in_ranges (page_base x) (m_vm_lazy model')) eqn:E; [|reflexivity].
    pose proof (LAZY x E) as E0. rewrite (EB b x Hb Hx) in E0. discriminate E0. }
  rewrite <- HLsegs.
  apply (POST R' M1 model' A).
  - apply art_kept_preserved; [rewrite P2, H2; reflexivity|exact PK].
  - rewrite HLscr. split.
    + intros a Ha CLa. apply EQ; [exact Ha|]. unfold aclient, aclient_g in CLa.
      destruct CLa as [(b & Hb & Hr)|[((C1' & C2') & C3')|[((C1' & C2') & C3')|[(f & Hf & R1 & R2)|[SH|[(f & Hf & SH)|(b & Hb & SH)]]]]]].
      * destruct (CB b Hb) as (K1 & K2 & _ & K4 & K5 & _). rewrite HIeq in K5. apply NFP_off; [clear - Hr K5; lia|clear - Hr K2; lia].
      * intros [F|[F|F]]; [exact (C3' F)|rewrite HIeq in C1'; clear - F C1' G1; lia|rewrite HIeq in C1'; clear - F C1' G1; lia].
      * rewrite HLlo in C1'. rewrite HLhi in C2'. apply NFP_lo; [clear - C2' G1; lia|]. intros I. apply C3'. apply HLst. unfold art_zone_statics. unfold art_ia_zone in I. clear - I. lia.
      * destruct (FS_IN _ _ _ _ FS f (in_or_app _ _ _ (or_introl Hf))) as (F1 & F2 & _). unfold FS_BYTES in *. apply NFP_off; [clear - R1 F1 F2 Fhi; lia|clear - R1 F1 F2 Fimg; lia].
      * apply NFP_sh. unfold in_shadow_of in SH. rewrite HIeq in SH. pose proof (art_S_ge (rn_HI rn) 0 ltac:(clear - G1; lia)).
        pose proof (art_S_lt (rn_HI rn + (2 ^ 47 - rn_HI rn) - 1) (2 ^ 44) ltac:(clear; lia)). clear - SH H H0. lia.
      * destruct (FS_IN _ _ _ _ FS f (in_or_app _ _ _ (or_introl Hf))) as (F1 & F2 & F3). unfold FS_BYTES in *. apply NFP_sh. unfold in_shadow_of in SH.
        pose proof (art_S_ge (ff_addr f) 0 ltac:(clear - F1 Flo; lia)). pose proof (art_S_lt (ff_addr f + ff_bytes (ff_class f) - 1) (2 ^ 44) ltac:(clear - F2 Fhi G2; lia)). clear - SH H H0. lia.
      * destruct (CB b Hb) as (K1 & _ & _ & K4 & K5 & _). rewrite HIeq in K5. apply NFP_sh. unfold in_shadow_of in SH.
        pose proof (art_S_ge (fst b) 0 ltac:(clear - K1; lia)). pose proof (art_S_lt (fst b + snd b - 1) (2 ^ 44) ltac:(clear - K5 G2; lia)). clear - SH H H0. lia.
    + intros a Ha. apply GROW.
      assert (WM : wrA M (Sp - 4096) 4096) by (intros dd kk Hd Hk; rewrite <- HLsegs; apply SWR; assumption).
      pose proof (art_wr_wview ASEGS M (Sp - 4096) 4096 ltac:(clear - HHI G1; lia) ltac:(clear - HS47; lia) WM (Z_to_bv 64 a)) as V. rewrite art_u_lit in V by (clear - Ha HHI G1 HS47; lia). specialize (V ltac:(clear - Ha; lia)).
      rewrite art_wview_off in V by (rewrite art_u_lit by (clear - Ha HHI G1 HS47; lia); right; clear - Ha HHI G1; lia). exact V.
  - exact RT.
  - apply incl_refl.
  - exact (bi_minv _ _ _ _ _ _ _ _ _ _ _ B1).
  - exact RI'.
Qed.
End Wrap.

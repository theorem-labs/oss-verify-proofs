(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTop0i. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvXTrk3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTop0i.AsAllocFXTrk.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRunI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4R OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTop0i OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRun3N OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRunI.AsAllocF0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRunI.AsAllocF0i OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRunI.AsAllocF2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4R.AsAllocFRun OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTop0i.AsAllocFRunJ OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRun3N.AsAllocFRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4R.AsAllocFMem OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTop0i.AsAllocFHypI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTop0i.AsAllocFTopA.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wf_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wf_clear_disj_or A | wf_clear_disj_or B] | ?A <-> ?B => first [wf_clear_disj_or A | wf_clear_disj_or B] | ?A -> ?B => first [wf_clear_disj_or A | wf_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wf_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wf_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac am_inner ::= first [ solve [wf_clear_disj; wf_lia0] | wf_lia0 ].
#[local] Ltac lia ::= ha_first_lia.   (* [comment removed for export] *)
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
(* [comment removed for export] *)
#[local] Abbreviation up8 := AsAinvOpsPf3d.AsAinvFreeS.up8.

Section TOPA0.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND CPM KD : Z).
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Hypothesis CELLS : free_cells bt TP TSDP PGP FL MIDEND CPM.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis G_KD : 0 <= KD <= 1408.
  Hypothesis HYP_DEPOT : HYP_DEPOT_stmt bt FXOK KD.
  Hypothesis HTP : TP = ia_tp asan_addrs.
  Hypothesis OPS_IA4 : OPS_REP_ialloc_init4_stmt bt.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).

  #[local] Abbreviation runA_post := (AsAllocFTop0i.AsAllocFTopA.runA_post bt FXOK KD).
  (* [comment removed for export] *)
  Definition free_runA0_stmt : Prop :=
    forall fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret sp m : Z) (p : word) (st : ast),
      FXOK fx -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
      WF bt st Lc FF -> Rep bt st Lc FF M mdl -> bounds st Lc B C K ->
      call_pre ASEGS asan_addrs R M ret sp MSTK_A -> getr R 10 = p -> fpc M (U (getr R 8)) sp DMAX ->
      In (U p, m) Lc -> K + kcost_free <= KCAP -> (exists h : option Z, holes_le h st) ->     (* [comment removed for export] *)
      a_ialloc st = false ->
      katD ASEGS (cfg ASEGS fx R (ia_free asan_addrs) M mdl) (runA_post (set_ialloc st) Lc FF R M mdl p).

  Theorem free_runA0 : free_runA0_stmt.
  Proof using OPS_IA4 HTP HYP_DEPOT G_KD GEOM CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP.
    (lazymatch goal with |- ?G => let G' := eval unfold free_runA0_stmt in G in change_no_check G' end).
    intros fx R M mdl Lc FF B C K ret sp m p st HFX HH MW W RP BD CP HR10 FPC HinP HK HLEX IA.
    pose proof ceil_rng as CR.
    set (S := getr R 2) in *. set (ra0 := getr R 1). set (tp := getr R 4).
    destruct CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk). fold S ra0 tp in CP1, CP2, CP4.
    assert (Utp : U tp = 0x63a740) by (rewrite CP4; vm_compute; reflexivity).
    assert (ETP : TP = 0x63a740) by (rewrite HTP; reflexivity).
    destruct CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CELL_kif & CELL_key & CELL_tsdp & CELL_tctx & CELL_hook
                      & CELL_mcsz & CELL_msz & CELL_gfl & CELL_mff & CELL_gsh & CELL_gmb & CELL_mb & CELL_gme & CELL_me & CELL_ghe & CELL_he
                      & CELL_grm & CELL_rm & CELL_cpm & G_consts).
    destruct G_consts as (Gc1 & Gc2 & Gc3 & Gc4 & Gc5 & Gc6 & Gc7 & Gc8 & Gc9 & Gc10).
    destruct GEOM as (GCT & Gtop & Gbot).
    pose proof (free_obls_pf bt) as (OBL_nolazy_rt & OBL_freed_private & OBL_rt_private & OBL_stats_not_rep & OBL_blk_geom & OBL_batch_geom & OBL_hdr_writable & OBL_X_vs_node & OBL_store_private).
    unfold OBL_nolazy_rt_stmt in OBL_nolazy_rt. unfold OBL_freed_private_stmt in OBL_freed_private. unfold OBL_rt_private_stmt in OBL_rt_private.
    unfold OBL_stats_not_rep_stmt in OBL_stats_not_rep. unfold OBL_blk_geom_stmt in OBL_blk_geom. unfold OBL_batch_geom_stmt in OBL_batch_geom.
    unfold OBL_hdr_writable_stmt in OBL_hdr_writable. unfold OBL_X_vs_node_stmt in OBL_X_vs_node. unfold OBL_store_private_stmt in OBL_store_private.
    destruct (live_range bt st Lc FF W (U p) m HinP) as (Lp1 & Lp2 & Lp3 & Lp4).
    destruct (OBL_blk_geom st Lc FF (U p) m W HinP) as (GpT & GCp & (AB1 & AB2 & AB3 & AB4)).
    pose proof (blk_above_img bt st Lc FF W ltac:((lazymatch goal with |- ?G => let G' := eval unfold img_lo_small in G in change_no_check G' end); rewrite BT_ia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) (U p) m HinP) as PIMG.
    destruct (up8_facts m ltac:(lia)) as (U8a & U8b & U8c & U8d).
    pose proof (thread_dyn bt st Lc FF W) as (GT0 & GTC & GTI & GTB & TPG & GC0 & GCC & GCI & GCB & CPG' & GCT' & SB0 & SB1 & SBH & SB16).
    clear AB3 GCT'. hidehyp GpT. hidehyp GCp. hidehyp GCT. hidehyp GTB. hidehyp GCB. hidehyp AB4.
    assert (GT4 : 4096 <= T) by (unfold PG in TPG; clear - GT0 TPG; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18).
    destruct R3 as (Tctx & Ttop & Tbot & Tsw & Tfs & Tunw & TQ & TPC & TW & Tback & Ttid & Ttls1 & Ttls2).
    destruct R8 as [RH _]. destruct (RH (U p) m HinP) as (Hst & (b1 & Hb1 & H11) & Hnhi & Hnlo & Hw8 & Hz4 & _).
    assert (Hb1r : 0 <= b1 < 256) by (destruct Hb1; subst; lia). unfold byteZ, cellN in H11. rewrite w2b1 in H11 by lia.
    destruct R11 as (IAf & IAl & IAz & _). rewrite IA in IAf.
    destruct (R15 (U p) m HinP) as [WBLK WSH].
    pose proof (OBL_hdr_writable st Lc FF M mdl (U p) m W RP HinP) as WHDR.
    rewrite BT_segs in *. rewrite BT_ia in *. cbn [ia_img_lo ia_img_hi asan_addrs] in GTI, GCI, PIMG.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr.
    unfold PTRHI in CPlo, CPhi. unfold AS_HEAPLO, AS_LO, MSTK_A, PG, KSPACE, NMAX, PTRLO in *.
    (* [comment removed for export] *)
    set (Hd := HID st mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi asan_addrs] in G in change_no_check G' end). lia. }
    assert (NHrt : forall z, (T <= z < T + 4096) \/ (CTX <= z < CTX + 0x10000) \/ (U p - 16 <= z < U p + up8 m) ->
                   Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (OBL_nolazy_rt st Lc FF M mdl z W RP).
      (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). first [clear - Hz HinP | idtac]; (destruct Hz as [Hz|[Hz|Hz]]; [am_tauto | am_tauto | right; right; left; exists (U p), m; split; [exact HinP | lia]]). }
    destruct R14 as (B1 & B2 & B3 & B4 & B5).
    set (Mr := mrestrict Hd M).
    Ltac hoff NH := apply hid_off_of; intros z Hz; unfold T_UNW, T_QC, T_PC, PC_SZ in *; split; [lia | apply NH; lia].
    (* [comment removed for export] *)
    Ltac konst Hd M R1 NHs C := apply (cellZ_restrict Hd M _ _ _ (const_cell bt M _ _ _ R1 C)); [lia | lia | hoff NHs].
    assert (K_mcs : rdn ASEGS Mr (Z_to_bv 64 0x10827c) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 30))) by konst Hd M R1 NHs CELL_mcs.
    assert (K_gcf : rdn ASEGS Mr (Z_to_bv 64 0xff260) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1990a8))) by konst Hd M R1 NHs CELL_gcf.
    assert (K_fum : rdn ASEGS Mr (Z_to_bv 64 0x1990ca) 1 = Some [Z_to_bv 8 1]) by konst Hd M R1 NHs CELL_fum.
    assert (K_inited : rdn ASEGS Mr (Z_to_bv 64 0x108258) 1 = Some [Z_to_bv 8 1]) by konst Hd M R1 NHs CELL_inited.
    assert (K_pg : rdn ASEGS Mr (Z_to_bv 64 0xff250) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 PGP))) by konst Hd M R1 NHs CELL_pg.
    assert (K_P : rdn ASEGS Mr (Z_to_bv 64 PGP) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 4096))) by konst Hd M R1 NHs CELL_P.
    assert (K_kif : rdn ASEGS Mr (Z_to_bv 64 0x106de0) 1 = Some [Z_to_bv 8 1]) by konst Hd M R1 NHs CELL_kif.
    assert (K_key : rdn ASEGS Mr (at_ (Z_to_bv 64 0x106de0) 4) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))).
    { replace (at_ (Z_to_bv 64 0x106de0) 4) with (Z_to_bv 64 0x106de4) by (apply bv_eq; reflexivity). konst Hd M R1 NHs CELL_key. }
    assert (K_tsdp : rdn ASEGS Mr (at_ tp (-88)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 TSDP))).
    { replace (at_ tp (-88)) with (Z_to_bv 64 (TP - 88)) by (apply bv_eq; rewrite at_u by (rewrite Utp; lia); rewrite Utp, ETP; reflexivity). rewrite ETP. rewrite ETP in CELL_tsdp. konst Hd M R1 NHs CELL_tsdp. }
    assert (K_tctx : rdn ASEGS Mr (Z_to_bv 64 TSDP) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 CTX))) by konst Hd M R1 NHs CELL_tctx.
    assert (K_hook : rdn ASEGS Mr (Z_to_bv 64 0x199048) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) by konst Hd M R1 NHs CELL_hook.
    (* [comment removed for export] *)
    Ltac thr_cell Hd M NHrt C := apply (cellZ_restrict Hd M _ _ _ C); [(lazymatch goal with |- ?G => let G' := eval unfold T_UNW, T_QC in G in change_no_check G' end); lia | unfold T_UNW, T_QC in *; lia | hoff NHrt].
    assert (K_thr : rdn ASEGS Mr (at_ (Z_to_bv 64 CTX) 152) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 T))).
    { replace (at_ (Z_to_bv 64 CTX) 152) with (Z_to_bv 64 (CTX + 152)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tback. }
    assert (K_T0 : rdn ASEGS Mr (Z_to_bv 64 T) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 CTX))) by thr_cell Hd M NHrt Tctx.
    assert (K_tid : rdn ASEGS Mr (Z_to_bv 64 (CTX + 8)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))) by thr_cell Hd M NHrt Ttid.
    assert (K_unw : rdn ASEGS Mr (at_ (Z_to_bv 64 T) 3168) 1 = Some [Z_to_bv 8 0]).
    { replace (at_ (Z_to_bv 64 T) 3168) with (Z_to_bv 64 (T + T_UNW)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_, T_UNW in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tunw. }
    assert (K_sw : rdn ASEGS Mr (at_ (Z_to_bv 64 T) 40) 1 = Some [Z_to_bv 8 0]).
    { replace (at_ (Z_to_bv 64 T) 40) with (Z_to_bv 64 (T + 40)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tsw. }
    assert (K_top : rdn ASEGS Mr (at_ (Z_to_bv 64 T) 8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bt_stack_top bt)))).
    { replace (at_ (Z_to_bv 64 T) 8) with (Z_to_bv 64 (T + 8)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Ttop. }
    assert (K_bot : rdn ASEGS Mr (at_ (Z_to_bv 64 T) 16) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bt_stack_bottom bt)))).
    { replace (at_ (Z_to_bv 64 T) 16) with (Z_to_bv 64 (T + 16)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tbot. }
    (* [comment removed for export] *)
    unfold IA_FLAG, IA_INST in IAf, IAl, IAz. rewrite BT_ia in IAf, IAl, IAz. cbn [ia_ialloc_flag ia_ialloc_inst asan_addrs] in IAf, IAl, IAz.
    assert (K_iaflag : rdn ASEGS Mr (Z_to_bv 64 0x197008) 1 = Some [Z_to_bv 8 0]).
    { apply (cellZ_restrict Hd M _ _ _ IAf); [lia | lia | hoff NHs]. }
    assert (K_lock : rdn ASEGS Mr (Z_to_bv 64 0x197009) 1 = Some [Z_to_bv 8 0]).
    { apply (cellZ_restrict Hd M _ _ _ IAl); [lia | lia | hoff NHs]. }
    destruct (rdn2_junk_ex Mr) as (b2 & b3 & K_junk).
    assert (K_flagw : rdn ASEGS Mr (Z_to_bv 64 0x197008) 4 = Some [Z_to_bv 8 0; Z_to_bv 8 0; b2; b3]).
    { change 4%nat with (1 + (1 + 2))%nat. apply (rdn_cat ASEGS Mr _ 1 3 [Z_to_bv 8 0]); [exact K_iaflag | | wd_ulia].
      replace (at_ (Z_to_bv 64 0x197008) (Z.of_nat 1)) with (Z_to_bv 64 0x197009 : word) by (apply bv_eq; reflexivity).
      apply (rdn_cat ASEGS Mr _ 1 2 [Z_to_bv 8 0]); [exact K_lock | | wd_ulia].
      replace (at_ (Z_to_bv 64 0x197009) (Z.of_nat 1)) with (Z_to_bv 64 0x19700a : word) by (apply bv_eq; reflexivity). exact K_junk. }
    destruct (p_div_facts (U p) ltac:(lia)) as [Q47 Q32].
    set (q32 := U p / 2 ^ 32) in Q32.
    (* [comment removed for export] *)
    assert (exists n1 : Z, n1 = 40) as [n1 En1] by (exists 40; reflexivity).
    assert (exists n2 : Z, n2 = 262144) as [n2 En2] by (exists 262144; reflexivity).
    assert (exists n3 : Z, n3 = 3456) as [n3 En3] by (exists 3456; reflexivity).
    assert (exists n4 : Z, n4 = 262728) as [n4 En4] by (exists 262728; reflexivity).
    (* [comment removed for export] *)
    pose proof (bt_ok_W bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DC & _ & _ & _).
    rewrite Forall_forall in DC.
    assert (DYN_P : forall a, PGP <= a < PGP + 8 -> ~ img_dyn (bt_ia bt) a) by (intros a Ha; exact (DC _ CELL_P a Ha)).
    assert (DYN_TS : forall a, TSDP <= a < TSDP + 8 -> ~ img_dyn (bt_ia bt) a) by (intros a Ha; exact (DC _ CELL_tctx a Ha)).
    rewrite BT_ia in DYN_P, DYN_TS.
    assert (GPIz : (PGP + 8 <= 0x108780 \/ 0x108780 + 0x81038 <= PGP) /\ (PGP + 8 <= 0x197008 \/ 0x19700c <= PGP)).
    { split.
      - destruct (ivl_disj PGP 8 0x108780 (0x108780 + 0x81038) ltac:(intros a Ha X; apply (DYN_P a Ha); (lazymatch goal with |- ?G => let G' := eval unfold img_dyn, IASZ in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance ia_depot_tab ia_stackstore ia_ialloc_flag ia_ialloc_inst asan_addrs] in G in change_no_check G' end); lia) ltac:(lia) ltac:(lia)); lia.
      - destruct (ivl_disj PGP 8 0x197008 (0x197008 + 8) ltac:(intros a Ha X; apply (DYN_P a Ha); (lazymatch goal with |- ?G => let G' := eval unfold img_dyn, IASZ in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance ia_depot_tab ia_stackstore ia_ialloc_flag ia_ialloc_inst asan_addrs] in G in change_no_check G' end); lia) ltac:(lia) ltac:(lia)); lia. }
    assert (GPI : (U (Z_to_bv 64 PGP) + 8 <= 0x108780 \/ 0x108780 + 0x81038 <= U (Z_to_bv 64 PGP)) /\ (U (Z_to_bv 64 PGP) + 8 <= 0x197008 \/ 0x19700c <= U (Z_to_bv 64 PGP))) by (unorm; exact GPIz).
    assert (GTSI : (TSDP + 8 <= 0x108780 \/ 0x108780 + 0x81038 <= TSDP) /\ (TSDP + 8 <= 0x197008 \/ 0x197010 <= TSDP)).
    { split.
      - destruct (ivl_disj TSDP 8 0x108780 (0x108780 + 0x81038) ltac:(intros a Ha X; apply (DYN_TS a Ha); (lazymatch goal with |- ?G => let G' := eval unfold img_dyn, IASZ in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance ia_depot_tab ia_stackstore ia_ialloc_flag ia_ialloc_inst asan_addrs] in G in change_no_check G' end); lia) ltac:(lia) ltac:(lia)); lia.
      - destruct (ivl_disj TSDP 8 0x197008 (0x197008 + 8) ltac:(intros a Ha X; apply (DYN_TS a Ha); (lazymatch goal with |- ?G => let G' := eval unfold img_dyn, IASZ in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance ia_depot_tab ia_stackstore ia_ialloc_flag ia_ialloc_inst asan_addrs] in G in change_no_check G' end); lia) ltac:(lia) ltac:(lia)); lia. }
    (* [comment removed for export] *)
    assert (K_hdr : rdn ASEGS Mr (at_ p (-16)) 4 = Some [Z_to_bv 8 2; Z_to_bv 8 b1; Z_to_bv 8 (U (Z_to_bv 64 (m / 2 ^ 32))); Z_to_bv 8 (Z.shiftr (U (Z_to_bv 64 (m / 2 ^ 32))) 8)]).
    { replace (at_ p (-16)) with (Z_to_bv 64 (U p - 16)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite rdn_mrestrict; [| wd_ulia | unorm; hoff NHrt].
      change 4%nat with (1 + (1 + 2))%nat.
      apply (rdn_cat ASEGS M _ 1 3 [Z_to_bv 8 2]); [exact Hst | | wd_ulia].
      replace (at_ (Z_to_bv 64 (U p - 16)) (Z.of_nat 1)) with (Z_to_bv 64 (U p - 15)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      apply (rdn_cat ASEGS M _ 1 2 [Z_to_bv 8 b1]); [exact H11 | | wd_ulia].
      replace (at_ (Z_to_bv 64 (U p - 15)) (Z.of_nat 1)) with (Z_to_bv 64 (U p - 14)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      exact Hnhi. }
    assert (K_nhi : rdn ASEGS Mr (at_ p (-14)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (m / 2 ^ 32)))).
    { replace (at_ p (-14)) with (Z_to_bv 64 (U p - 14)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Hnhi. }
    assert (K_nlo : rdn ASEGS Mr (at_ p (-12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (m mod 2 ^ 32)))).
    { replace (at_ p (-12)) with (Z_to_bv 64 (U p - 12)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Hnlo. }
    (* [comment removed for export] *)
    assert (SOKstk : store_ok ASEGS Mr (at_ S (-2304)) 2304 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; hoff NHs].
      apply store_ok_bytes; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. intros x Hx. rewrite at_u in Hx by lia. apply CPstk. cbn in Hx. lia. }
    assert (SOKunw : store_ok ASEGS Mr (at_ (Z_to_bv 64 T) 3168) 1 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (first [clear - GTC CPhi CPlo | idtac]; lia) | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; hoff NHrt].
      apply (writableZ_store_ok M _ _ _ _ TW); (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia_c. }
    assert (SOKhdr : store_ok ASEGS Mr (at_ p (-16)) 4 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; hoff NHrt].
      apply (writableZ_store_ok M _ _ _ _ WHDR); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]. }
    assert (SOKp : store_ok ASEGS Mr p 8 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoff NHrt].
      apply (writableZ_store_ok M _ _ _ _ WHDR); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia. }
    assert (SOKstat : store_ok ASEGS Mr (Z_to_bv 64 (T + 2824)) 16 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| wd_ulia_c | unorm; hoff NHrt].
      apply (writableZ_store_ok M _ _ _ _ TW); wd_ulia_c. }
    (* [comment removed for export] *)
    destruct (rdn_defined_ex ASEGS Mr (Z_to_bv 64 (T + 2824)) 8) as (bf0 & Cf0 & Lf0).
    { intros i Hi. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite mrestrict_off; [| apply NHrt; revert Hi; unorm; intros Hi; lia].
      apply (writableZ_def M _ _ _ TW). revert Hi; unorm; intros Hi. lia. }
    { unorm. lia. }
    destruct (rdn_defined_ex ASEGS Mr (Z_to_bv 64 (T + 2832)) 8) as (bf1 & Cf1 & Lf1).
    { intros i Hi. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite mrestrict_off; [| apply NHrt; revert Hi; unorm; intros Hi; lia].
      apply (writableZ_def M _ _ _ TW). revert Hi; unorm; intros Hi. lia. }
    { unorm. lia. }
    (* [comment removed for export] *)
    assert (FPCr : fpc Mr (U (getr R 8)) (U S) DMAX).
    { rewrite CP2. apply (fpc_kept_gen M _ _ _ FPC Mr). destruct (fpc_shape _ _ _ _ FPC) as [ST|FR]; [left; exact ST | right].
      intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). apply mrestrict_off. apply NHs; unfold PTRHI in *; lia. }
    set (h2 := Z_to_bv 8 (U (Z_to_bv 64 (m / 2 ^ 32)))) in *. set (h3 := Z_to_bv 8 (Z.shiftr (U (Z_to_bv 64 (m / 2 ^ 32))) 8)) in *.
    (* [comment removed for export] *)
    set (MIr := fr_init Mr b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4).
    Ltac xinit En1 En2 En3 En4 K := apply (init_keeps_rdn _ _ _ _ _ _ _ En1 En2 En3 En4); [(lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact K].
    assert (KI_mcs : rdn ASEGS MIr (Z_to_bv 64 0x10827c) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 30))) by xinit En1 En2 En3 En4 K_mcs.
    assert (KI_gcf : rdn ASEGS MIr (Z_to_bv 64 0xff260) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1990a8))) by xinit En1 En2 En3 En4 K_gcf.
    assert (KI_fum : rdn ASEGS MIr (Z_to_bv 64 0x1990ca) 1 = Some [Z_to_bv 8 1]) by xinit En1 En2 En3 En4 K_fum.
    assert (KI_inited : rdn ASEGS MIr (Z_to_bv 64 0x108258) 1 = Some [Z_to_bv 8 1]) by xinit En1 En2 En3 En4 K_inited.
    assert (KI_pg : rdn ASEGS MIr (Z_to_bv 64 0xff250) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 PGP))) by xinit En1 En2 En3 En4 K_pg.
    assert (KI_P : rdn ASEGS MIr (Z_to_bv 64 PGP) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 4096))) by xinit En1 En2 En3 En4 K_P.
    assert (KI_kif : rdn ASEGS MIr (Z_to_bv 64 0x106de0) 1 = Some [Z_to_bv 8 1]) by xinit En1 En2 En3 En4 K_kif.
    assert (KI_key : rdn ASEGS MIr (at_ (Z_to_bv 64 0x106de0) 4) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))) by xinit En1 En2 En3 En4 K_key.
    assert (KI_tsdp : rdn ASEGS MIr (at_ tp (-88)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 TSDP))) by xinit En1 En2 En3 En4 K_tsdp.
    assert (KI_tctx : rdn ASEGS MIr (Z_to_bv 64 TSDP) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 CTX))) by (first [clear - GTSI En4 En3 En2 En1 K_tctx Gc2 Gc1 | idtac]; xinit En1 En2 En3 En4 K_tctx).
    assert (KI_hook : rdn ASEGS MIr (Z_to_bv 64 0x199048) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))) by xinit En1 En2 En3 En4 K_hook.
    assert (KI_thr : rdn ASEGS MIr (at_ (Z_to_bv 64 CTX) 152) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 T))) by (first [clear - En4 En3 En2 En1 K_thr GCI GCC GC0 CPhi CPlo | idtac]; xinit En1 En2 En3 En4 K_thr).
    assert (KI_T0 : rdn ASEGS MIr (Z_to_bv 64 T) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 CTX))) by xinit En1 En2 En3 En4 K_T0.
    assert (KI_tid : rdn ASEGS MIr (Z_to_bv 64 (CTX + 8)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))) by xinit En1 En2 En3 En4 K_tid.
    assert (KI_unw : rdn ASEGS MIr (at_ (Z_to_bv 64 T) 3168) 1 = Some [Z_to_bv 8 0]) by (first [clear - En4 En3 En2 En1 K_unw GTI GTC GT0 CPhi CPlo | idtac]; xinit En1 En2 En3 En4 K_unw).
    assert (KI_sw : rdn ASEGS MIr (at_ (Z_to_bv 64 T) 40) 1 = Some [Z_to_bv 8 0]) by (first [clear - En4 En3 En2 En1 K_sw GTI GTC GT0 CPhi CPlo | idtac]; xinit En1 En2 En3 En4 K_sw).
    assert (KI_top : rdn ASEGS MIr (at_ (Z_to_bv 64 T) 8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bt_stack_top bt)))) by (first [clear - En4 En3 En2 En1 K_top GTI GTC GT0 CPhi CPlo | idtac]; xinit En1 En2 En3 En4 K_top).
    assert (KI_bot : rdn ASEGS MIr (at_ (Z_to_bv 64 T) 16) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (bt_stack_bottom bt)))) by (first [clear - En4 En3 En2 En1 K_bot GTI GTC GT0 CPhi CPlo | idtac]; xinit En1 En2 En3 En4 K_bot).
    assert (KI_hdr : rdn ASEGS MIr (at_ p (-16)) 4 = Some [Z_to_bv 8 2; Z_to_bv 8 b1; h2; h3]) by xinit En1 En2 En3 En4 K_hdr.
    assert (KI_nhi : rdn ASEGS MIr (at_ p (-14)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (m / 2 ^ 32)))) by xinit En1 En2 En3 En4 K_nhi.
    assert (KI_nlo : rdn ASEGS MIr (at_ p (-12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (m mod 2 ^ 32)))) by xinit En1 En2 En3 En4 K_nlo.
    assert (KI_f0 : rdn ASEGS MIr (Z_to_bv 64 (T + 2824)) 8 = Some bf0) by xinit En1 En2 En3 En4 Cf0.
    assert (KI_f1 : rdn ASEGS MIr (Z_to_bv 64 (T + 2832)) 8 = Some bf1) by xinit En1 En2 En3 En4 Cf1.
    clear K_mcs K_gcf K_fum K_inited K_kif K_key K_tsdp K_tctx K_hook K_thr K_T0 K_tid K_unw K_sw K_top K_bot K_nhi K_nlo.
    (* [comment removed for export] *)
    clear GPIz GTSI DYN_P DYN_TS DC. hidehyp GPI.
    set (hdr := [Z_to_bv 8 2; Z_to_bv 8 b1; h2; h3]) in K_hdr, KI_hdr.
    pose proof (bytes_le_to_Z_bound hdr) as Bhv. cbn [length hdr] in Bhv.
    pose proof (bytes_le_to_Z_nonneg hdr) as Bhv0.
    assert (Vhv : bytes_le_to_Z hdr = U (Z_to_bv 64 (bytes_le_to_Z hdr))) by (unorm; reflexivity).
    (* [comment removed for export] *)
    assert (GS12 : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0) by (rewrite CP2; lia).
    assert (Gp12 : AIMGHI + 16 <= U p /\ U p + 8 <= U S - 3584 /\ U p mod 16 = 0) by (rewrite CP2; lia).
    assert (GT12 : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584)).
    { split; [exact GT4|]. split; [(lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); unfold hide in GTB; split; lia | rewrite CP2; lia]. }
    assert (GpT12 : U p + 8 <= T \/ T + 4096 <= U p - 16) by (unfold hide in GpT; lia).
    assert (Gctx12 : 1 <= CTX /\ CTX + 4096 <= U S - 3584 /\ (CTX + 4096 <= T \/ T + 4096 <= CTX) /\ (CTX + 4096 <= U p - 16 \/ U p + 8 <= CTX)).
    { unfold hide in GCT, GCp. rewrite CP2. lia. }
    assert (Gtp12 : AIMGLO + 88 <= U tp /\ U tp + 8 <= AIMGHI) by (rewrite Utp; lia).
    assert (Gtsdp12 : AIMGLO <= U (Z_to_bv 64 TSDP) /\ U (Z_to_bv 64 TSDP) + 8 <= AIMGHI) by (wd_ulia).
    assert (GP12 : AIMGLO <= U (Z_to_bv 64 PGP) /\ U (Z_to_bv 64 PGP) + 8 <= AIMGHI) by (wd_ulia).
    assert (Gtop12 : 4096 <= U (Z_to_bv 64 (bt_stack_top bt)) <= 2 ^ 47) by (wd_ulia).
    assert (Gbot12 : U (Z_to_bv 64 (bt_stack_bottom bt)) < U (Z_to_bv 64 (bt_stack_top bt))) by (wd_ulia).
    assert (Gn12 : 1 <= m <= 2 ^ 40) by lia.
    assert (Gq12 : U p / 2 ^ 32 = q32 /\ 0 <= q32 < 2 ^ 15 /\ U p / 2 ^ 47 = 0) by (repeat split; try reflexivity; lia).
    assert (Ch1 : Z_to_bv 8 b1 = Z_to_bv 8 0x11 \/ Z_to_bv 8 b1 = Z_to_bv 8 0x91) by (destruct Hb1 as [E|E]; rewrite E; [left|right]; reflexivity).
    assert (Chv : bytes_le_to_Z [Z_to_bv 8 2; Z_to_bv 8 b1; h2; h3] = U (Z_to_bv 64 (bytes_le_to_Z hdr))) by (subst hdr; exact Vhv).
    (* [comment removed for export] *)
    unfold hide in GPI.
    destruct (run_p12_0 Mr (seg_rom ASEGS) R S p ra0 tp (Z_to_bv 64 TSDP) (Z_to_bv 64 PGP) (Z_to_bv 64 (bt_stack_top bt)) (Z_to_bv 64 (bt_stack_bottom bt))
                T CTX m q32 DMAX (Z_to_bv 8 b1) h2 h3 (Z_to_bv 64 (bytes_le_to_Z hdr)) bf0 bf1 b2 b3 n1 n2 n3 n4)
      as (r12 & MU & sz & bsz & RUN12 & X1 & X2 & X8 & X9 & X10 & X11 & X18 & X19 & X20 & X21 & X22 & X3 & X4 & X23 & X24 & X25 & X26 & X27
          & SZ1 & SZ2 & FOOTU & GRU & USZ & UPC & UUNW & RSZ & LSZ & TAG0).
    all: try assumption.
    all: try reflexivity.
    all: let k := numgoals in guard k = 1.
    change (fr_init Mr b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4) with MIr in FOOTU, GRU.
    (* [comment removed for export] *)
    clear GPI.
    (* [comment removed for export] *)
    (lazymatch goal with |- ?G => let G' := eval unfold cfg in G in change_no_check G' end). replace (Z_to_bv 64 (ia_free asan_addrs)) with (Z_to_bv 64 0x6e2fc : word) by (apply bv_eq; reflexivity).
    replace (0x6e2fc%bv : word) with (Z_to_bv 64 0x6e2fc : word) in RUN12 by (apply bv_eq; reflexivity).
    replace (0x8ea80%bv : word) with (Z_to_bv 64 0x8ea80 : word) in RUN12 by (apply bv_eq; reflexivity).
    apply (katD_msteps_acct ASEGS Hd (HID_off_segments bt st Lc FF M mdl BT_ia RP) asanF_segs_wx (a_aa st)
             (@mkst fx R (Z_to_bv 64 0x6e2fc) M (seg_rom ASEGS))
             (@mkst fx r12 (Z_to_bv 64 0x8ea80) (fr_P2 MU S p (getr R 22) T m (Z_to_bv 8 b1) h2 h3 bf0 bf1) (seg_rom ASEGS)) mdl).
    { apply lazy_cover_HID. }
    { exact B1. }
    { exact B2. }
    { exact HH. }
    { rewrite restrict_mkstF. exact RUN12. }
    intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx R (Z_to_bv 64 0x6e2fc) M (seg_rom ASEGS))) with M by reflexivity.
    pose proof (same_but_materialized_frame mdl mdl1 SBM1) as SF1.
    remember (fr_P2 MU S p (getr R 22) T m (Z_to_bv 8 b1) h2 h3 bf0 bf1) as M11r eqn:EM11.
    remember (fr_P1 MIr S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)) as M3 eqn:EM3 in FOOTU, GRU.
    set (MDin := munrestrict Hd M M11r).
    (* [comment removed for export] *)
    set (MI := fr_init M b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4).
    assert (VISI : forall x : word, Hd x = true -> init_out x).
    { intros x Hx. pose proof (u64_range x) as Rx. (lazymatch goal with |- ?G => let G' := eval unfold init_out in G in change_no_check G' end).
      destruct (Z_lt_le_dec (U x) AIMGLO) as [L|L]; [lia|]. destruct (Z_lt_le_dec (U x) AIMGHI) as [H'|H']; [|lia].
      exfalso. rewrite <- (Z_to_bv_bv_unsigned 64 x) in Hx. rewrite (NHs (U x)) in Hx; [discriminate | lia | right; lia]. }
    assert (EMI : forall a : word, Hd a = false -> MIr a = MI a).
    { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold MIr, MI in G in change_no_check G' end). apply (fr_init_pw b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4). (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). apply mrestrict_off. exact Ha. }
    pose proof (fr_init_grows b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4 M) as GRMI. change (mem_grows M MI) in GRMI.
    (* [comment removed for export] *)
    set (st1 := op_meter st EVT [] 0).
    assert (W1 : WF bt st1 Lc FF) by (apply WF_meter; [exact W | (lazymatch goal with |- ?G => let G' := eval unfold EVT in G in change_no_check G' end); lia | reflexivity]   (* [comment removed for export] *)).
    destruct SF1 as (_ & Evm & Elz & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehl & _ & _ & _ & Eeg).
    assert (RP1 : Rep bt st1 Lc FF M mdl1).
    { pose proof (Rep_sbm bt st Lc FF M mdl mdl1 RP MI1 SBM1) as RPm.
      apply (OPS_REP_meter_pf bt st Lc FF M mdl1 mdl1 EVT [] 0 RPm eq_refl).
      - intros a; apply iff_refl.
      - pose proof RPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & FA & _) & _). exact FA.
      - rewrite app_nil_r. exact B1.
      - rewrite app_nil_r. exact MI1.
      - lia.
      - (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    (* [comment removed for export] *)
    set (st2 := op_ialloc_init st1).
    assert (W2I : WF bt st2 Lc FF) by (apply WF_ialloc_init; exact W1).
    assert (RPI : Rep bt st2 Lc FF MI mdl1).
    { apply (OPS_IA4 st1 Lc FF M MI mdl1 W1 RP1).
      - (lazymatch goal with |- ?G => let G' := eval cbn [st1 op_meter add_meter a_ialloc] in G in change_no_check G' end). exact IA.
      - intros a NE. pose proof (u64_range a) as Ra. split; [| exact (fr_init_some b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4 M a NE)].
        (lazymatch goal with |- ?G => let G' := eval unfold foot_ialloc4, IA_FLAG, IA_INST, IASZ in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_ialloc_flag ia_ialloc_inst asan_addrs] in G in change_no_check G' end).
        first [clear - NE En4 En3 En2 En1 | idtac]; (destruct (Z_lt_le_dec (U a) 0x108780) as [A1|A1]; [| destruct (Z_lt_le_dec (U a) 0x1897b0) as [A2|A2]; [right; left; lia|]];
          (destruct (Z_lt_le_dec (U a) 0x197008) as [A3|A3]; [| destruct (Z_lt_le_dec (U a) 0x19700c) as [A4|A4]; [left; lia|]]);
          exfalso; apply NE; apply (fr_init_out b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4 En1 En2 En3 En4); (lazymatch goal with |- ?G => let G' := eval unfold init_out in G in change_no_check G' end); lia).
      - rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN, IA_FLAG in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_ialloc_flag asan_addrs] in G in change_no_check G' end). apply (fr_init_flag b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4).
      - rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN, IA_FLAG in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_ialloc_flag asan_addrs Z.add Pos.add Pos.succ] in G in change_no_check G' end). apply (fr_init_lock b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4).
      - rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold fillZ, byteZ, cellN, IA_INST in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_ialloc_inst asan_addrs] in G in change_no_check G' end). intros i Hi.
        apply (fr_init_map1 b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4); first [assumption | lia].
      - rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN, IA_INST in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_ialloc_inst asan_addrs Z.add Pos.add Pos.succ] in G in change_no_check G' end).
        change (Z_to_bv 64 PG) with (Z_to_bv 64 4096 : word). apply (fr_init_pgcell b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4).
      - rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN, IA_INST in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_ialloc_inst asan_addrs Z.add Pos.add Pos.succ] in G in change_no_check G' end).
        apply (fr_init_chunks b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4). }
    (* [comment removed for export] *)
    assert (Mb15 : M (at_ p (-15)) = Some (Z_to_bv 8 b1)).
    { replace (at_ p (-15)) with (Z_to_bv 64 (U p - 15)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). apply rdn1_heap; [wd_ulia | exact H11]. }
    assert (Mb14 : M (at_ p (-14)) = Some h2 /\ M (at_ p (-13)) = Some h3).
    { pose proof (rdn_firstn ASEGS M 2 _ _ 1 Hnhi ltac:(lia)) as F1. cbn [firstn word_to_le_bytes Z_to_le_bytes] in F1.
      pose proof (rdn_skip ASEGS M _ 2 _ 1 Hnhi ltac:(lia) ltac:(wd_ulia)) as F2. cbn [skipn word_to_le_bytes Z_to_le_bytes Nat.sub] in F2.
      split.
      - replace (at_ p (-14)) with (Z_to_bv 64 (U p - 14)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). subst h2. apply rdn1_heap; [wd_ulia | exact F1].
      - replace (at_ p (-13)) with (at_ (Z_to_bv 64 (U p - 14)) (Z.of_nat 1)) by (first [clear - Lp3 Lp2 Lp1 CPhi CPlo | idtac]; (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia)). subst h3. apply rdn1_heap; [(lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia | exact F2]. }
    destruct Mb14 as [Mb14 Mb13].
    assert (Mb3210 : M (at_ (Z_to_bv 64 T) 3168) = Some (Z_to_bv 8 0)).
    { replace (at_ (Z_to_bv 64 T) 3168) with (Z_to_bv 64 (T + T_UNW)) by (first [clear - GTC GT0 CPhi CPlo | idtac]; (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_, T_UNW in G in change_no_check G' end); wd_ulia)).
      change (Z_to_bv 8 0) with (Z_to_bv 8 (U (Z_to_bv 64 0))). apply rdn1_offimg; [(lazymatch goal with |- ?G => let G' := eval unfold T_UNW in G in change_no_check G' end); wd_ulia | exact Tunw]. }
    assert (MUb3210 : MU (at_ (Z_to_bv 64 T) 3168) = Some (Z_to_bv 8 0)) by (apply rdn1_offimg; [(lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia | exact UUNW]).
    (* [comment removed for export] *)
    Ltac onMIr MIr Mr En1 En2 En3 En4 NH Mb := (lazymatch goal with |- ?G => let G' := eval unfold MIr in G in change_no_check G' end); rewrite (fr_init_out _ _ _ _ _ _ _ En1 En2 En3 En4) by ((lazymatch goal with |- ?G => let G' := eval unfold init_out in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia);
      (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); rewrite mrestrict_off; [exact Mb | rewrite <- (Z_to_bv_bv_unsigned 64 (at_ _ _)); (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; apply NH; lia].
    assert (Ib15 : MIr (at_ p (-15)) = Some (Z_to_bv 8 b1)) by onMIr MIr Mr En1 En2 En3 En4 NHrt Mb15.
    assert (Ib14 : MIr (at_ p (-14)) = Some h2) by onMIr MIr Mr En1 En2 En3 En4 NHrt Mb14.
    assert (Ib13 : MIr (at_ p (-13)) = Some h3) by onMIr MIr Mr En1 En2 En3 En4 NHrt Mb13.
    assert (Ib3210 : MIr (at_ (Z_to_bv 64 T) 3168) = Some (Z_to_bv 8 0)) by (first [clear - Mb3210 En4 En3 En2 En1 NHrt GTI GTC GT0 CPhi CPlo | idtac]; onMIr MIr Mr En1 En2 En3 En4 NHrt Mb3210).
    (* [comment removed for export] *)
    assert (GSm : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47) by (rewrite CP2; lia).
    assert (Gpm : AIMGHI + 16 <= U p /\ U p + 8 <= U S - 3584) by (rewrite CP2; lia).
    assert (GTm : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584)) by exact GT12.
    assert (GpTm : U p + 8 <= T \/ T + 4096 <= U p - 16) by exact GpT12.
    (* [comment removed for export] *)
    pose proof (fr_P1_grows' MIr S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)) as GRr3. feed GRr3. rewrite <- EM3 in GRr3.
    pose proof (fr_P2_grows MU S p (getr R 22) T m (Z_to_bv 8 b1) h2 h3 bf0 bf1) as GR2. feed GR2. rewrite <- EM11 in GR2.
    assert (GRIr11 : mem_grows MIr M11r).
    { eapply mem_grows_trans; [exact GRr3|]. eapply mem_grows_trans; [exact GRU|]. exact GR2. }
    assert (GRr11 : mem_grows Mr M11r).
    { eapply mem_grows_trans; [| exact GRIr11]. (lazymatch goal with |- ?G => let G' := eval unfold MIr in G in change_no_check G' end). apply (fr_init_grows b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4). }
    assert (GRinI : mem_grows MI MDin).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MDin, munrestrict in G in change_no_check G' end). destruct (Hd x) eqn:Ex.
      - unfold MI in Hx. rewrite (fr_init_out b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4 En1 En2 En3 En4) in Hx by (apply VISI; exact Ex). exact Hx.
      - apply GRIr11. rewrite (EMI x Ex). exact Hx. }
    assert (GRin : mem_grows M MDin) by (eapply mem_grows_trans; [exact GRMI | exact GRinI]).
    (* [comment removed for export] *)
    assert (MUeq : forall x : word, (U x < U S - 2272 \/ U S - 64 <= U x) -> U x <> T + 3168 -> MU x = M3 x).
    { intros x Hx1 Hx2. destruct (decide (MU x = M3 x)) as [E|NE]; [exact E|]. exfalso. destruct (FOOTU x NE) as [F|[F|[F|F]]]; lia. }
    (* [comment removed for export] *)
    pose proof (fr_P1_foot MIr S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)) as P1F. feed P1F. rewrite <- EM3 in P1F.
    pose proof (fr_P2_foot MU S p (getr R 22) T m (Z_to_bv 8 b1) h2 h3 bf0 bf1) as P2F. feed P2F. rewrite <- EM11 in P2F.
    pose proof (fr_P2_hdr MU S p (getr R 22) T m (Z_to_bv 8 b1) h2 h3 bf0 bf1) as P2H. feed P2H. rewrite <- EM11 in P2H.
    destruct P2H as (E16 & E15 & E14 & E13).
    assert (DIFF1 : forall a : word, MDin a <> MI a -> Xd (U S) (U p) T (U a) /\ MDin a <> None).
    { intros a NE. pose proof (u64_range a) as Ha.
      split; cycle 1.
      { destruct (MDin a) eqn:E1; [discriminate|]. exfalso. apply NE. destruct (MI a) eqn:E2; [|reflexivity].
        exfalso. assert (X : MI a <> None) by (rewrite E2; discriminate). apply GRinI in X. rewrite E1 in X. exact (X eq_refl). }
      unfold MDin, munrestrict in NE. destruct (Hd a) eqn:Eh.
      { exfalso. apply NE. symmetry. (lazymatch goal with |- ?G => let G' := eval unfold MI in G in change_no_check G' end). apply (fr_init_out b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4 En1 En2 En3 En4). apply VISI. exact Eh. }
      rewrite <- (EMI a Eh) in NE.
      (lazymatch goal with |- ?G => let G' := eval unfold Xd in G in change_no_check G' end).
      destruct (decide (M11r a = MU a)) as [E11|N11].
      - rewrite E11 in NE. destruct (decide (MU a = M3 a)) as [EU|NU].
        + rewrite EU in NE. pose proof (P1F a NE). lia.
        + destruct (FOOTU a NU) as [F|[F|[F|F]]]; try (first [clear - F | idtac]; lia).
          exfalso. apply NE. replace a with (at_ (Z_to_bv 64 T) 3168) by (first [clear - F GTC GT0 CPhi CPlo | idtac]; (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia)). rewrite MUb3210, Ib3210. reflexivity.
      - destruct (P2F a N11) as [F|[F|[F|F]]]; try (first [clear - F | idtac]; lia).
        (* [comment removed for export] *)
        destruct (decide (U a = U p - 16)) as [E16'|N16]; [lia|]. exfalso. apply NE.
        destruct (decide (U a = U p - 15)) as [E|N1].
        { replace a with (at_ p (-15)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). rewrite E15, Ib15. reflexivity. }
        destruct (decide (U a = U p - 14)) as [E|N2].
        { replace a with (at_ p (-14)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). rewrite E14, Ib14. reflexivity. }
        replace a with (at_ p (-13)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). rewrite E13, Ib13. reflexivity. }
    (* [comment removed for export] *)
    assert (DIFF0 : forall a : word, MDin a <> M a -> (Xd (U S) (U p) T (U a) \/ ~ init_out a) /\ MDin a <> None).
    { intros a NE. destruct (decide (MDin a = MI a)) as [E|N].
      - rewrite E in NE |- *. split; [right | exact (fr_init_some b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4 M a NE)].
        intros IO. apply NE. (lazymatch goal with |- ?G => let G' := eval unfold MI in G in change_no_check G' end). apply (fr_init_out b2 b3 (Z_to_bv 64 4096) n1 n2 n3 n4 En1 En2 En3 En4). exact IO.
      - destruct (DIFF1 a N) as [X D]. split; [left; exact X | exact D]. }
    (* [comment removed for export] *)
    assert (VIS : forall a : word, Hd a = false -> MDin a = M11r a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold MDin in G in change_no_check G' end); apply munrestrict_off; exact Ha).
    assert (VISstk : forall a : word, U S - 3584 <= U a < U S -> MDin a = M11r a).
    { intros a Ha. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 a). apply NHs; [lia|]. left. rewrite CP2 in Ha. lia. }
    (* [comment removed for export] *)
    assert (SZW : U (Z_to_bv 64 (bytes_le_to_Z bsz)) mod 2 ^ 32 = sz).
    { pose proof (bytes_le_to_Z_bound bsz) as Bb. rewrite LSZ in Bb. pose proof (bytes_le_to_Z_nonneg bsz). unorm. apply (lez_low32 ASEGS MU (at_ S (-2120)) bsz sz RSZ USZ). lia. }
    apply (katD_bind ASEGS _ (depot_post bt FXOK KD (Xd (U S) (U p) T) st2 Lc FF MDin mdl1 r12 (at_ S (-2176)) (Z_to_bv 64 0x4fdc8))).
    { apply (HYP_DEPOT fx (Xd (U S) (U p) T) st2 Lc FF MDin mdl1 r12 (at_ S (-2176)) (at_ S (-2112)) (Z_to_bv 64 (bytes_le_to_Z bsz)) (Z_to_bv 64 0x4fdc8) sz HFX).
      { rewrite Ehl. exact HH. }
      { exact (model_ivs_wf_sbm mdl mdl1 SBM1 MW). }
      { exact W2I. }
      { exists MI. split; [exact RPI | exact DIFF1]. }
      { intros a Ha. split.
        - unfold Xd in Ha. rewrite CP2 in Ha. rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi asan_addrs] in G in change_no_check G' end).
          destruct Ha as [Ha|[Ha|[Ha|Ha]]]; [lia | lia | destruct GTI as [GTI'|GTI']; lia | lia].
        - intros id Hid. cbn [st2 op_ialloc_init set_ialloc st1 op_meter add_meter a_dep] in Hid |- *.
          apply (OBL_X_vs_node st Lc FF (U p) m id a W HinP Hid). unfold Xd in Ha. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). rewrite CP2 in Ha. clear - Ha U8a U8b U8c U8d Lp3 CPlo CR. lia. }
      { (* [comment removed for export] *)
        intros a Ha. apply (xd_xtracked bt _ Lc FF (U S) (U p) m a W2I HinP); [rewrite CP2; clear - CPlo; lia | exact Ha]. }
      { (* [comment removed for export] *)
        destruct HLEX as [h0 HLE0]. exists h0. exact HLE0. }
      { (lazymatch goal with |- ?G => let G' := eval cbn [st2 op_ialloc_init set_ialloc st1 op_meter add_meter a_dep a_kact] in G in change_no_check G' end). destruct W as (_ & _ & _ & _ & _ & _ & (D1 & D2 & Drest) & (WM1 & _) & _).
        rewrite meter_div by exact WM1. lia. }
      { (lazymatch goal with |- ?G => let G' := eval cbn [st2 op_ialloc_init set_ialloc st1 op_meter add_meter a_dep a_kact] in G in change_no_check G' end). destruct W as (_ & _ & _ & _ & _ & _ & (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & Drest) & (WM1 & _) & _).
        rewrite meter_div by exact WM1. unfold FRW in *. lia. }
      { exact X1. } { exact X2. } { exact X10. } { exact X11. }
      { rewrite at_u by lia. rewrite CP2. destruct (sp_facts16 sp CP16) as [E _]. exact E. }
      { rewrite at_u by lia. rewrite CP2. lia. }
      { rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval unfold PTRHI in G in change_no_check G' end). lia. }
      { apply ret_ok_lit; [lia | reflexivity]. }
      { intros a Ha. rewrite at_u in Ha by lia. split.
        - apply GRin. apply store_ok1_heap; [lia|]. apply CPstk. rewrite <- CP2. lia.
        - eapply store_ok_mono; [exact GRin|]. apply CPstk. rewrite <- CP2. lia. }
      { split; [exact (proj1 SZ1) | unfold DMAX in SZ2; cbn in SZ2; exact SZ2]. }            (* [comment removed for export] *)
      { exact SZW. }
      { (* [comment removed for export] *)
        assert (TG : rdn ASEGS MU (at_ (at_ S (-2120)) 4) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))) by (rewrite at_at; exact TAG0).
        pose proof (lez_high32_0 ASEGS MU (at_ S (-2120)) bsz RSZ TG) as HI.
        pose proof (bytes_le_to_Z_bound bsz) as Bb. rewrite LSZ in Bb. pose proof (bytes_le_to_Z_nonneg bsz) as Bn.
        rewrite u_Z2bv by (clear - Bb Bn; cbn in Bb; lia). rewrite HI. clear; lia. }
      { (* [comment removed for export] *)
        (lazymatch goal with |- ?G => let G' := eval cbn [st2 op_ialloc_init set_ialloc st1 op_meter add_meter a_kact] in G in change_no_check G' end). destruct BD as (_ & _ & BK). unfold kcost_free in HK. clear - BK HK. lia. }
      { intros i Hi. rewrite at_u in Hi by lia. apply GRin. apply store_ok1_heap; [wd_ulia|].
        replace (Z_to_bv 64 i) with (Z_to_bv 64 (U (Z_to_bv 64 i))) by (apply bv_eq; unorm; reflexivity).
        rewrite Z_to_bv_bv_unsigned. apply CPstk. unorm. rewrite <- CP2. lia. }
      { rewrite at_u by lia. rewrite CP2. lia. }
      { rewrite !at_u by lia. clear. lia. }                                                  (* [comment removed for export] *)
      { rewrite at_u by lia. clear - SZ1 SZ2 HSr. unfold DMAX in SZ2. cbn in SZ2. lia. } }    (* [comment removed for export] *)
    (* [comment removed for export] *)
    intros c' POST.
    destruct POST as (fx' & st' & M' & mdl' & R' & id & Ec' & HFX' & (d' & naa & Est') & W2 & RX2 & KEPTX & DIFF2 & CHG2 & RK & A0 & Hid & SEV & LZ & HH2 & MW2).
    subst c'. apply katD_refl.
    unfold depot_st in Est'. cbn [st2 op_ialloc_init set_ialloc st1 op_meter add_meter a_reg a_cinit a_cache a_tq a_gq a_sec a_nres a_dep a_hint a_ialloc a_aa a_kact a_shsec] in Est'.
    rewrite app_nil_r, Z.add_0_r in Est'. subst st'.
    destruct RX2 as (M0' & RP2 & DX2).
    (* [comment removed for export] *)
    pose proof (fr_P2_q0 MU S p (getr R 22) T m (Z_to_bv 8 b1) h2 h3 bf0 bf1) as Cq0. feed Cq0. rewrite <- EM11 in Cq0.
    pose proof (fr_P2_q1 MU S p (getr R 22) T m (Z_to_bv 8 b1) h2 h3 bf0 bf1) as Cq1. feed Cq1. rewrite <- EM11 in Cq1.
    pose proof (fr_P2_q2 MU S p (getr R 22) T m (Z_to_bv 8 b1) h2 h3 bf0 bf1) as Cq2. feed Cq2. rewrite <- EM11 in Cq2.
    pose proof (fr_P2_q3 MU S p (getr R 22) T m (Z_to_bv 8 b1) h2 h3 bf0 bf1) as Cq3. feed Cq3. rewrite <- EM11 in Cq3.
    pose proof (fr_P2_q4 MU S p (getr R 22) T m (Z_to_bv 8 b1) h2 h3 bf0 bf1) as Cq4. feed Cq4. rewrite <- EM11 in Cq4.
    pose proof (fr_P2_q5 MU S p (getr R 22) T m (Z_to_bv 8 b1) h2 h3 bf0 bf1) as Cq5. feed Cq5. rewrite <- EM11 in Cq5.
    (* [comment removed for export] *)
    pose proof (fr_P2_rdn_out MU S p (getr R 22) T m (Z_to_bv 8 b1) h2 h3 bf0 bf1) as P2O. feed P2O. rewrite <- EM11 in P2O.
    assert (ICPT : forall k (v : word), -56 <= k <= -8 ->
              rdn ASEGS M3 (at_ S k) 8 = Some (LE8 v) -> rdn ASEGS M11r (at_ S k) 8 = Some (LE8 v)).
    { intros k v Hk Hr. rewrite P2O; cycle 1.
      { rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. } { rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. } { rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. } { rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
      apply (rd_same ASEGS MU M3); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hr].
      intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply MUeq; lia. }
    pose proof (fr_P1_i0 MIr S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)) as I0. feed I0. rewrite <- EM3 in I0.
    pose proof (fr_P1_i1 MIr S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)) as I1. feed I1. rewrite <- EM3 in I1.
    pose proof (fr_P1_i2 MIr S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)) as I2. feed I2. rewrite <- EM3 in I2.
    pose proof (fr_P1_i3 MIr S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)) as I3. feed I3. rewrite <- EM3 in I3.
    pose proof (fr_P1_i4 MIr S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)) as I4. feed I4. rewrite <- EM3 in I4.
    pose proof (fr_P1_i5 MIr S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)) as I5. feed I5. rewrite <- EM3 in I5.
    pose proof (fr_P1_i6 MIr S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)) as I6. feed I6. rewrite <- EM3 in I6.
    pose proof (ICPT (-8) ra0 ltac:(lia) I0) as Ci0.
    pose proof (ICPT (-16) (getr R 8) ltac:(lia) I1) as Ci1.
    pose proof (ICPT (-24) (getr R 9) ltac:(lia) I2) as Ci2.
    pose proof (ICPT (-32) (getr R 18) ltac:(lia) I3) as Ci3.
    pose proof (ICPT (-40) (getr R 19) ltac:(lia) I4) as Ci4.
    pose proof (ICPT (-48) (getr R 20) ltac:(lia) I5) as Ci5.
    pose proof (ICPT (-56) (getr R 21) ltac:(lia) I6) as Ci6.
    (* [comment removed for export] *)
    assert (XF : forall k bs0, -2176 <= k -> k + 8 <= 0 -> rdn ASEGS M11r (at_ S k) 8 = Some bs0 -> rdn ASEGS M' (at_ S k) 8 = Some bs0).
    { intros k bs0 Hk1 Hk2 Hr. apply (rd_same ASEGS M' M11r); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hr].
      intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. rewrite (KEPTX x); [| (lazymatch goal with |- ?G => let G' := eval unfold Xd in G in change_no_check G' end); (first [clear - Hx Hk2 Hk1 | idtac]; lia) | rewrite at_u by (first [clear - CR CPlo CP2 CPhi | idtac]; lia); (first [clear - Hx Hk1 | idtac]; lia)]. apply VISstk. lia. }
    Ltac incs := apply in_cs; reflexivity.
    Ltac viaRK RK k X := etransitivity; [| exact X];
      match goal with |- getr _ ?x = getr _ _ => replace x with (Z_to_bv 5 k) by (apply bv_eq; reflexivity) end; apply RK; incs.
    (lazymatch goal with |- ?G => let G' := eval unfold AsAllocFTop0i.AsAllocFTopA.runA_post in G in change_no_check G' end). exists fx', R', M', M0', mdl', d', naa, id.
    (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold runA_st, set_ialloc in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_reg a_cinit a_cache a_tq a_gq a_sec a_nres a_dep a_hint a_ialloc a_aa a_kact a_shsec] in G in change_no_check G' end).
    fold S. (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance ia_img_lo ia_img_hi asan_addrs] in G in change_no_check G' end).
    split; [reflexivity|]. split; [exact HFX'|]. split; [exact HH2|]. split; [exact W2|]. split; [exact RP2|]. split; [exact DX2|].
    split.
    { (* [comment removed for export] *) intros a NE. destruct (decide (M' a = MDin a)) as [E|N].
      + rewrite E in NE |- *. destruct (DIFF0 a NE) as [[X|X] D]; (split; [| exact D]); [left; exact X|].
        right. right. right. exists 0x10825a, 0x1990a8. split; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); do 4 right; left; reflexivity|]. pose proof (u64_range a). unfold init_out in X. lia.
      + destruct (DIFF2 a N) as [_ D]. split; [| exact D]. right. pose proof (CHG2 a N) as CX. rewrite at_u in CX by lia. rewrite ?BT_ia in CX.
        destruct CX as [X|[X|X]]; [left; lia | right; left; exact X | right; right; exact X]. }
    split.
    { (* [comment removed for export] *) rewrite (KEPTX (at_ p (-16))); [| (lazymatch goal with |- ?G => let G' := eval unfold Xd in G in change_no_check G' end); rewrite at_u by (first [clear - Lp1 Lp3 Lp2 CPhi CPlo | idtac]; lia); (repeat match goal with H : _ |- _ => clear H end; lia) | rewrite !at_u by (first [clear - CR CPlo CP2 CPhi Lp1 Lp3 Lp2 | idtac]; lia); (first [clear - Lp3 Lp2 CPlo CP2 G_KD | idtac]; lia)].
      rewrite VIS by (rewrite <- (Z_to_bv_bv_unsigned 64 (at_ p (-16))); rewrite at_u by lia; apply NHrt; lia). exact E16. }
    split; [apply XF; [lia | lia | exact Cq0]|]. split; [apply XF; [lia | lia | exact Cq1]|]. split; [apply XF; [lia | lia | exact Cq2]|].
    split; [apply XF; [lia | lia | exact Cq3]|]. split; [apply XF; [lia | lia | exact Cq4]|]. split; [apply XF; [lia | lia | exact Cq5]|].
    split; [apply XF; [lia | lia | exact Ci0]|]. split; [apply XF; [lia | lia | exact Ci1]|]. split; [apply XF; [lia | lia | exact Ci2]|].
    split; [apply XF; [lia | lia | exact Ci3]|]. split; [apply XF; [lia | lia | exact Ci4]|]. split; [apply XF; [lia | lia | exact Ci5]|].
    split; [apply XF; [lia | lia | exact Ci6]|].
    split; [viaRK RK 2 X2|]. split; [viaRK RK 8 X8|]. split; [viaRK RK 9 X9|]. split; [exact A0|].
    split; [viaRK RK 18 X18|]. split; [viaRK RK 19 X19|]. split; [viaRK RK 20 X20|]. split; [viaRK RK 21 X21|].
    split; [viaRK RK 22 X22|]. split; [viaRK RK 3 X3|]. split; [viaRK RK 4 X4|].
    split; [viaRK RK 23 X23|]. split; [viaRK RK 24 X24|]. split; [viaRK RK 25 X25|]. split; [viaRK RK 26 X26|]. split; [viaRK RK 27 X27|].
    split; [exact Hid|].
    split; [eapply same_except_vm_trans; [apply same_but_materialized_except_vm; exact SBM1 | exact SEV]|].
    split.
    { intros a Ha. cbn [a_dep] in LZ.
      assert (RNGa : 0 <= a < 2 ^ 64).                                                       (* [comment removed for export] *)
      { destruct Ha as [V|[V|V]]; [| clear - V CR; lia | cbn [ia_img_lo ia_img_hi asan_addrs] in V; clear - V; lia].
        rewrite <- ?BT_ia in V. exact (proj1 (AsKSys7b.app_visible_cases bt _ Lc FF _ _ W2 a V)). }
      destruct (LZ a RNGa) as [E|(blk & Hin & Hnin & Hr)]; [rewrite E; (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz; reflexivity|].
      exfalso. destruct (OBL_store_private _ Lc FF blk a W2 Hin Hr) as (Z1 & Z2 & Z3). rewrite ?BT_ia in Z2, Z3. cbn [ia_img_lo ia_img_hi asan_addrs] in Z2.
      destruct Ha as [V|[V|V]]; [exact (Z3 V) | lia | cbn [ia_img_lo ia_img_hi asan_addrs] in V; lia]. }
    exact MW2.
  Qed.
End TOPA0.

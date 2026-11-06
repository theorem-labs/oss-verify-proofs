(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.AsAinvOpsQ3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRunI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4R OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRun3N OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRun3Nf OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFPutB OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFMemN OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFMemM OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTop0i. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRunI.AsAllocF0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRunI.AsAllocF2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4R.AsAllocFRun OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRun3N.AsAllocFRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRun3N OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRun3Nf OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFPutB.AsAllocFRunM OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4R.AsAllocFMem OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFMemN OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFMemM OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK1.AsAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTop0i.AsAllocFTopA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFPutB.AsAllocFTail.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AsAllocFFam.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= ha_first_lia.   (* [comment removed for export] *)
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation up8 := AsAinvOpsPf3d.AsAinvFreeS.up8.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma down8_up8Nf : forall n, AsRtRegion.down8 (n + 7) = up8 n.
Proof. intros n. (lazymatch goal with |- ?G => let G' := eval unfold AsRtRegion.down8, AsAinvOpsPf3d.AsAinvFreeS.up8 in G in change_no_check G' end). reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma nth_error_snoc_f : forall {A} (l : list A) (x : A), nth_error (l ++ [x]) (length l) = Some x.
Proof. intros A l x. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. Qed.

Section PUTNf.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND CPM KD : Z).
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Hypothesis CELLS : free_cells bt TP TSDP PGP FL MIDEND CPM.
  Hypothesis CELLNB : free_cells_nb bt.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis G_KD : 0 <= KD <= 1408.
  Hypothesis HTP : TP = ia_tp asan_addrs.
  Variable KDR : Z.
  Hypothesis G_KDR : 0 <= KDR <= 1376.
  Hypothesis HYP_DRAIN : HYP_DRAIN_stmt bt FXOK KDR.
  (* [comment removed for export] *)
  Hypothesis OPS_WFX_newbatch : forall st Lc FF L1 L2 p n k ks,
    WF bt st Lc FF -> a_kact st <= KCAP -> Lc = L1 ++ (p, n) :: L2 -> a_cache st BATCHCLASS = ks ++ [k] ->
    WFX bt (op_quar_newbatch (op_cache_pop st BATCHCLASS) (chunk_of_compact (bt_spacebeg bt) BATCHCLASS k) (p - 16) n) (L1 ++ L2) FF.
  (* [comment removed for export] *)
  Variables (HP HPc : option Z -> ast -> Prop).
  Hypothesis FAM : hp_fam bt HP HPc.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition free_putNf_stmt : Prop :=
    forall (h : option Z) fx' (R R' : bvmap 5 word) (M M' M0 : mem) (mdl mdl' : Model) (Lc FF L1 L2 : list (Z * Z)) (B C K1 ret sp m : Z) (p : word)
           (st' : ast) (id : Z) (ks : list Z) (k : Z) (tq' : list batch) (b : batch),
      let S := getr R 2 in
      (* [comment removed for export] *)
      call_pre ASEGS asan_addrs R M ret sp MSTK_A -> getr R 10 = p ->
      Lc = L1 ++ (U p, m) :: L2 ->
      (* [comment removed for export] *)
      WF bt st' Lc FF -> Rep bt st' Lc FF M0 mdl' -> bounds st' Lc B C K1 -> HPc h st' ->
      a_tq st' = tq' ++ [b] -> Z.of_nat (length (ba_items b)) = BATCHCAP -> a_cache st' BATCHCLASS = ks ++ [k] -> m <= 2 ^ 28 ->
      (* [comment removed for export] *)
      FXOK fx' -> m_halted mdl' = None -> BackingAlgebra.model_ivs_wf mdl' ->
      (forall a : word, M' a <> M0 a -> Xd (U S) (U p) T (U a) /\ M' a <> None) ->
      (forall a : word, M' a <> M a ->
          (Xd (U S) (U p) T (U a) \/ (U S - 2176 - KD <= U a < U S - 2176)
           \/ rt_priv (bt_ia bt) Lc FF (U a) \/ in_wins (ia_priv (bt_ia bt)) (U a))
          /\ M' a <> None) ->
      M' (at_ p (-16)) = Some (Z_to_bv 8 3) ->
      rdn ASEGS M' (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6e4a4)) -> rdn ASEGS M' (at_ S (-2144)) 8 = Some (LE8 S) ->
      rdn ASEGS M' (at_ S (-2152)) 8 = Some (LE8 p) -> rdn ASEGS M' (at_ S (-2160)) 8 = Some (LE8 (Z_to_bv 64 0x6e434)) ->
      rdn ASEGS M' (at_ S (-2168)) 8 = Some (LE8 (Z_to_bv 64 1)) -> rdn ASEGS M' (at_ S (-2176)) 8 = Some (LE8 (at_ S (-2128))) ->
      rdn ASEGS M' (at_ S (-8)) 8 = Some (LE8 (getr R 1)) -> rdn ASEGS M' (at_ S (-16)) 8 = Some (LE8 (getr R 8)) ->
      rdn ASEGS M' (at_ S (-24)) 8 = Some (LE8 (getr R 9)) -> rdn ASEGS M' (at_ S (-32)) 8 = Some (LE8 (getr R 18)) ->
      rdn ASEGS M' (at_ S (-40)) 8 = Some (LE8 (getr R 19)) -> rdn ASEGS M' (at_ S (-48)) 8 = Some (LE8 (getr R 20)) ->
      rdn ASEGS M' (at_ S (-56)) 8 = Some (LE8 (getr R 21)) ->
      getr R' 2 = at_ S (-2176) -> getr R' 8 = at_ p (-16) -> getr R' 9 = at_ S (-2128) -> getr R' 10 = Z_to_bv 64 id ->
      getr R' 18 = Z_to_bv 64 (IB bt) -> getr R' 19 = Z_to_bv 64 0 -> getr R' 20 = Z_to_bv 64 T -> getr R' 21 = at_ S (-81) ->
      getr R' 22 = getr R 22 -> getr R' 3 = getr R 3 -> getr R' 4 = getr R 4 ->
      getr R' 23 = getr R 23 -> getr R' 24 = getr R 24 -> getr R' 25 = getr R 25 -> getr R' 26 = getr R 26 -> getr R' 27 = getr R 27 ->
      0 <= id < 2 ^ 32 ->
      same_except_vm mdl mdl' -> lazy_kept (bt_ia bt) Lc FF mdl mdl' ->
      katD ASEGS (mkCfg (@mkst fx' R' (Z_to_bv 64 0x4fdc8) M' (seg_rom ASEGS)) mdl')
           (free_post ASEGS FXOK asan_addrs (AAINV_F bt HP) h MSTK_A R M mdl (L1 ++ L2) FF
                      (Z.max 0 (B - (m + MBLK))) (Z.max 0 (C - 1)) K1 ret sp).

  Theorem free_putNf : free_putNf_stmt.
  Proof using FAM OPS_WFX_newbatch HYP_DRAIN G_KDR KDR G_KD GEOM CELLNB CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP.
    (lazymatch goal with |- ?G => let G' := eval unfold free_putNf_stmt in G in change_no_check G' end).
    intros h fx' R R' M M' M0 mdl mdl' Lc FF L1 L2 B C K1 ret sp m p st' id ks k tq' b CP HR10 ELc W' RP' BD' HLE ETQ FULL ECA M28
           HFX' HH' MW' DX CHG Hb16 Cq0 Cq1 Cq2 Cq3 Cq4 Cq5 Ci0 Ci1 Ci2 Ci3 Ci4 Ci5 Ci6
           Y2 Y8 Y9 Y10 Y18 Y19 Y20 Y21 Y22 Y3 Y4 Y23 Y24 Y25 Y26 Y27 Hid SEV LZ.
    pose proof ceil_rng as CR.
    set (S := getr R 2) in *. set (ra0 := getr R 1). set (tp := getr R 4).
    destruct CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk). fold S ra0 tp in CP1, CP2, CP4. fold tp in Y4.
    assert (Utp : U tp = 0x63a740) by (rewrite CP4; vm_compute; reflexivity).
    unfold IB in Y18. rewrite BT_ia in Y18. cbn [ia_instance asan_addrs] in Y18.
    destruct CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CELL_kif & CELL_key & CELL_tsdp & CELL_tctx & CELL_hook
                      & CELL_mcsz & CELL_msz & CELL_gfl & CELL_mff & CELL_gsh & CELL_gmb & CELL_mb & CELL_gme & CELL_me & CELL_ghe & CELL_he
                      & CELL_grm & CELL_rm & CELL_cpm & G_consts).
    destruct G_consts as (Gc1 & Gc2 & Gc3 & Gc4 & Gc5 & Gc6 & Gc7 & Gc8 & Gc9 & Gc10).
    destruct GEOM as (GCT & Gtop & Gbot).
    pose proof (free_obls_pf bt) as
      (OBL_nolazy_rt & OBL_freed_private & OBL_rt_private & _ & OBL_blk_geom & OBL_batch_geom & OBL_hdr_writable & _ & _).
    unfold OBL_nolazy_rt_stmt in OBL_nolazy_rt. unfold OBL_freed_private_stmt in OBL_freed_private. unfold OBL_rt_private_stmt in OBL_rt_private.
    unfold OBL_blk_geom_stmt in OBL_blk_geom. unfold OBL_batch_geom_stmt in OBL_batch_geom. unfold OBL_hdr_writable_stmt in OBL_hdr_writable.
    pose proof (OBL_cache_chunk_pf bt) as OBL_cache. unfold OBL_cache_chunk_stmt in OBL_cache.
    assert (HinP : In (U p, m) Lc) by (rewrite ELc; apply in_app_iff; right; left; reflexivity).
    assert (HinK : In k (a_cache st' BATCHCLASS)) by (rewrite ECA; apply in_app_iff; right; left; reflexivity).
    assert (HinB : In b (a_tq st' ++ a_gq st')) by (apply in_app_iff; left; rewrite ETQ; apply in_app_iff; right; left; reflexivity).
    destruct (live_range bt st' Lc FF W' (U p) m HinP) as (Lp1 & Lp2 & Lp3 & Lp4).
    destruct (OBL_blk_geom st' Lc FF (U p) m W' HinP) as (GpT & GCp & (AB1 & AB2 & AB3 & AB4)).
    pose proof (blk_above_img bt st' Lc FF W' ltac:((lazymatch goal with |- ?G => let G' := eval unfold img_lo_small in G in change_no_check G' end); rewrite BT_ia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) (U p) m HinP) as PIMG.
    destruct (up8_facts m ltac:(lia)) as (U8a & U8b & U8c & U8d).
    destruct (OBL_batch_geom st' Lc FF b (U p) m W' HinB HinP) as (GBp & GBT & GBlo & GBhi).
    destruct (read_tq_last bt st' Lc FF M0 mdl' tq' b W' RP' ETQ) as (Qlen & Qlast & Qbytes & Bnext & Bsize & Bcnt & Bitems & BWb & Bcvb & Blen & Blob & Bhib).
    rewrite FULL in Bcnt. unfold BATCHCAP in Bcnt.
    pose proof (thread_dyn bt st' Lc FF W') as (GT0 & GTC & GTI & GTB & TPG & GC0 & GCC & GCI & GCB & CPG' & GCT' & SB0 & SB1 & SBH & SB16).
    assert (GT4 : 4096 <= T) by (unfold PG in TPG; clear - GT0 TPG; Z.div_mod_to_equations; lia).
    clear AB3 GCT' GCB.
    (* [comment removed for export] *)
    destruct (OBL_cache st' Lc FF M0 mdl' BATCHCLASS k W' RP' ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia) HinK)
      as (Bcv & Blo & Bhi & B16 & Kr & BT & BC & BP & BB & Bnl & BW & Bpriv).
    set (ba := chunk_of_compact (bt_spacebeg bt) BATCHCLASS k) in *.
    change (csize BATCHCLASS) with 8192 in Bhi, BT, BC, BP, BB, Bnl, BW, Bpriv.
    assert (Eba : bt_spacebeg bt + 3 * 2 ^ 35 + 16 * k = ba) by ((lazymatch goal with |- ?G => let G' := eval unfold ba, chunk_of_compact, region_beg, KREGION, BATCHCLASS in G in change_no_check G' end); lia).
    specialize (BP (U p) m HinP). specialize (BB b HinB).
    clear OBL_blk_geom OBL_cache OBL_batch_geom.
    assert (T16 : T mod 16 = 0) by (clear -TPG; unfold PG in TPG; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    assert (QA : 0 <= q_bytes tq' /\ BATCHSZ <= ba_bytes b /\ q_bytes (a_tq st') = q_bytes tq' + ba_bytes b
                 /\ 1 <= Z.of_nat (length (a_tq st')) <= 2 ^ 8 /\ q_bytes (a_tq st') <= 2 ^ 20).
    { pose proof W' as (_ & _ & (QT & _ & QTB & _) & _). rewrite Forall_forall in QT.
      assert (IT : forall b0, In b0 (a_tq st') -> forall m0 n0, In (m0, n0) (ba_items b0) -> 1 <= n0).
      { intros b0 Hb0 m0 n0 Hin. destruct (QT b0 Hb0) as (_ & _ & WI). destruct (WI m0 n0 Hin) as [X _]. lia. }
      pose proof (q_bytes_ge (a_tq st') IT) as G1.
      assert (G2 : BATCHSZ * Z.of_nat (length tq') <= q_bytes tq').
      { apply q_bytes_ge. intros b0 Hb0. apply IT. rewrite ETQ. apply in_app_iff. left. exact Hb0. }
      assert (G3 : BATCHSZ <= ba_bytes b) by (apply ba_bytes_ge; apply IT; rewrite ETQ; apply in_app_iff; right; left; reflexivity).
      rewrite ETQ, q_bytes_app in QTB, G1 |- *. cbn [q_bytes fold_right] in QTB, G1 |- *. rewrite length_app in G1 |- *. cbn [length] in G1 |- *.
      unfold BATCHSZ in G1, G2, G3, QTB |- *. clear - G1 G2 G3 QTB. repeat split; lia. }
    destruct QA as (QA1 & QA2 & QA3 & QA4 & QA5).
    pose proof W' as (_ & _ & (_ & _ & QTB0 & QGB & _) & _).
    (* [comment removed for export] *)
    pose proof RP' as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18).
    destruct R3 as (Tctx & Ttop & Tbot & Tsw & Tfs & Tunw & TQ & TPC & TW & Tback & Ttid & Ttls1 & Ttls2).
    destruct R8 as [RH _]. destruct (RH (U p) m HinP) as (Hst & H11 & Hnhi & Hnlo & Hw8 & Hz4 & _).
    destruct (R15 (U p) m HinP) as [WBLK WSH].
    destruct R14 as (B1 & B2 & B3 & B4 & B5).
    pose proof R17 as Csb.
    pose proof (OBL_hdr_writable st' Lc FF M0 mdl' (U p) m W' RP' HinP) as WHDR.
    (* [comment removed for export] *)
    destruct TQ as (_ & Qfirst & _ & _).
    destruct (TPC BATCHCLASS ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia)) as (PCcnt & _ & PCsz & PCk). rewrite ECA in PCcnt, PCk.
    rewrite length_app in PCcnt. cbn [length] in PCcnt. rewrite Nat2Z.inj_add in PCcnt. change (Z.of_nat 1) with 1 in PCcnt.
    specialize (PCk (length ks) k (nth_error_snoc_f ks k)).
    unfold T_PC, PC_SZ, BATCHCLASS in PCcnt, PCsz, PCk.
    clear R2 R4 R5 R6 R7 R9 R10 R12 R16 R18 RH TPC OBL_hdr_writable.
    rewrite BT_segs in *. rewrite BT_ia in *. cbn [ia_img_lo ia_img_hi asan_addrs] in GTI, GCI, PIMG.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr.
    unfold PTRHI in CPlo, CPhi. unfold AS_HEAPLO, AS_LO, MSTK_A, PG, NMAX, BATCHSZ, BATCHCAP, T_QC, SB, KSPACE, PTRLO in *.
    destruct (p16_facts (U p) Lp4 ltac:(lia)) as (_ & _ & _ & P8 & _ & _).
    destruct (sh_up8 (U p) m P8 ltac:(lia)) as [SHhi SHlo]. unfold SB in SHhi, SHlo.
    pose proof (cache_len bt st' Lc FF W' BATCHCLASS ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia)) as CL. rewrite ECA, length_app in CL. cbn [length] in CL.
    destruct (shad_facts2 (U p) (up8 m) ltac:(clear -AB4 Hpr U8a; lia) ltac:(clear - Hpr; lia) ltac:(clear - AB2 CR; lia) U8b P8 U8d) as (D81 & D82 & D83 & D84 & D85 & D86).
    (* [comment removed for export] *)
    assert (XdC : forall z, AIMGLO <= z < AIMGHI -> ~ Xd (U S) (U p) T z) by (intros z Hz; (lazymatch goal with |- ?G => let G' := eval unfold Xd in G in change_no_check G' end); rewrite CP2; clear -Hz GTI PIMG CPlo CR HSr; lia).
    assert (XdT : forall z, T <= z < T + 2800 -> ~ Xd (U S) (U p) T z) by (intros z Hz; (lazymatch goal with |- ?G => let G' := eval unfold Xd in G in change_no_check G' end); clear - Hz GpT U8b CP2 CPlo GTC; lia).
    assert (XdBo : forall z, ba_addr b <= z < ba_addr b + 8192 -> ~ Xd (U S) (U p) T z) by (intros z Hz; (lazymatch goal with |- ?G => let G' := eval unfold Xd in G in change_no_check G' end); clear - Hz GBp GBT GBhi U8b CP2 CPlo; lia).
    assert (XdH : forall z, U p - 15 <= z < U p -> ~ Xd (U S) (U p) T z) by (intros z Hz; (lazymatch goal with |- ?G => let G' := eval unfold Xd in G in change_no_check G' end); clear - Hz GpT U8b AB2 CP2 CPlo; lia).
    (* [comment removed for export] *)
    assert (GSm : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47) by (clear - CP2 CPlo CPhi CR; lia).
    assert (Gpm : AIMGHI + 16 <= U p /\ (PSIDE (U p) (up8 m) /\ U p + up8 m <= U S - 3584) /\ U p mod 16 = 0).
    { split; [clear - PIMG; lia|]. split; [split; [(lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear -AB4 U8a; lia | clear - AB2 U8a CP2 CPlo; lia] | exact Lp4]. }
    assert (GTm : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584)).
    { split; [exact GT4|]. split; [(lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - GTI GTB; split; lia | clear - GTC CP2 CPlo; lia]. }
    assert (Gn8m : 8 <= up8 m /\ up8 m mod 8 = 0 /\ up8 m <= 2 ^ 40) by (clear - U8a U8b U8c U8d M28 Lp3; lia).
    assert (Gbam : 0x10007fff8000 <= ba /\ ba + 8192 <= U S - 3584) by (clear - Blo Bhi CP2 CPlo; lia).
    assert (GbaTm : ba + 8192 <= T \/ T + 4096 <= ba) by (clear - BT; lia).
    assert (Gbapm : ba + 8192 <= U p - 16 \/ U p + up8 m <= ba) by (clear - BP; lia).
    assert (GpTm : U p + up8 m <= T \/ T + 4096 <= U p - 16) by (clear - GpT; lia).
    assert (Glm : 0x10007fff8000 <= ba_addr b /\ ba_addr b + 8192 <= U S - 3584) by (clear - GBlo GBhi CP2 CPlo; lia).
    assert (GlTm : ba_addr b + 8192 <= T \/ T + 4096 <= ba_addr b) by (clear - GBT; lia).
    assert (Glpm : ba_addr b + 8192 <= U p - 16 \/ U p + up8 m <= ba_addr b) by (clear - GBp; lia).
    assert (Gbalm : ba_addr b + 8192 <= ba \/ ba + 8192 <= ba_addr b) by (clear - BB; unfold BATCHSZ in BB; lia).
    hidehyp GpT. hidehyp GCp. hidehyp GCT. hidehyp BT. hidehyp BC. hidehyp BP. hidehyp BB. hidehyp GBp. hidehyp GBT. hidehyp GbaTm. hidehyp Gbapm. hidehyp GpTm.
    hidehyp GlTm. hidehyp Glpm. hidehyp Gbalm.
    hidehyp GTI. hidehyp GTB. hidehyp AB4. hidehyp D81. hidehyp GCI.
    (* [comment removed for export] *)
    assert (EQ0 : forall a : word, ~ Xd (U S) (U p) T (U a) -> M' a = M0 a).
    { intros a Ha. destruct (decide (M' a = M0 a)) as [E|N]; [exact E|]. exfalso. exact (Ha (proj1 (DX a N))). }
    assert (GR0 : mem_grows M0 M') by (intros a Ha; destruct (decide (M' a = M0 a)) as [E|N]; [rewrite E; exact Ha | exact (proj2 (DX a N))]).
    assert (GRM : mem_grows M M') by (intros a Ha; destruct (decide (M' a = M a)) as [E|N]; [rewrite E; exact Ha | exact (proj2 (CHG a N))]).
    (* [comment removed for export] *)
    set (Hd := HID st' mdl').
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st' mdl' z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi asan_addrs] in G in change_no_check G' end). lia. }
    assert (NHT : forall z, T <= z < T + 4096 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (OBL_nolazy_rt st' Lc FF M0 mdl' z W' RP'). left. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact Hz. }
    assert (NHp : forall z, U p - 16 <= z < U p + up8 m -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (OBL_nolazy_rt st' Lc FF M0 mdl' z W' RP'). right; right; left. exists (U p), m. split; [exact HinP | exact Hz]. }
    assert (NHb : forall z, ba <= z < ba + 8192 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply Bnl. exact Hz. }
    assert (NHbo : forall z, ba_addr b <= z < ba_addr b + 8192 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (OBL_nolazy_rt st' Lc FF M0 mdl' z W' RP'). right; right; right. exists b. split; [exact HinB | (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); exact Hz]. }
    assert (NHsh : forall z, sh_lo (U p) <= z < sh_hi (U p) m -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_allowed. exact (B4 (U p) m HinP z Hz). }
    assert (LZT : forall z, T <= z < T + 4096 -> lzb mdl' z = false).
    { intros z Hz. apply (OBL_nolazy_rt st' Lc FF M0 mdl' z W' RP'). left. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact Hz. }
    clear OBL_nolazy_rt Bnl.
    Ltac hoff NH := apply hid_off_of; intros z Hz; split; [lia | apply NH; lia].
    (* [comment removed for export] *)
    Ltac cell0 EQ0 NH XD C :=
      rewrite rdn_mrestrict; [ | wd_ulia_c | unorm; hoff NH ];
      eapply rd_same; [ intros x Hx; apply EQ0; apply XD; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                      | wd_ulia_c | exact C ].
    Ltac konst EQ0 R1 NHs XdC C := cell0 EQ0 NHs XdC (const_cell bt _ _ _ _ R1 C).
    assert (K_mcsz : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 (0x103f18 + 808)) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 20)))) by konst EQ0 R1 NHs XdC CELL_mcsz.
    assert (K_msz : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 (0x103f18 + 792)) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 28)))) by konst EQ0 R1 NHs XdC CELL_msz.
    assert (K_gfl : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 0xff268) 8 = Some (LE8 (Z_to_bv 64 FL))) by konst EQ0 R1 NHs XdC CELL_gfl.
    assert (K_mff : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 (FL + 48)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))) by konst EQ0 R1 NHs XdC CELL_mff.
    assert (K_gsh : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 0xff270) 8 = Some (LE8 (Z_to_bv 64 0x107578))) by konst EQ0 R1 NHs XdC CELL_gsh.
    assert (K_sh : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 0x107578) 8 = Some (LE8 (Z_to_bv 64 0x7fff8000))).
    { cbn [ia_rtc_sb asan_addrs] in Csb. cell0 EQ0 NHs XdC Csb. }
    assert (K_gmb : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 0xff278) 8 = Some (LE8 (Z_to_bv 64 0x108268))) by konst EQ0 R1 NHs XdC CELL_gmb.
    assert (K_mb : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 0x108268) 8 = Some (LE8 (Z_to_bv 64 0))) by konst EQ0 R1 NHs XdC CELL_mb.
    assert (K_gme : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 0xff280) 8 = Some (LE8 (Z_to_bv 64 0x108270))) by konst EQ0 R1 NHs XdC CELL_gme.
    assert (K_me : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 0x108270) 8 = Some (LE8 (Z_to_bv 64 MIDEND))) by konst EQ0 R1 NHs XdC CELL_me.
    assert (K_ghe : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 0xff288) 8 = Some (LE8 (Z_to_bv 64 0x108260))) by konst EQ0 R1 NHs XdC CELL_ghe.
    assert (K_he : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 0x108260) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff))) by konst EQ0 R1 NHs XdC CELL_he.
    assert (K_grm : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 0xff290) 8 = Some (LE8 (Z_to_bv 64 0x1011b0))) by konst EQ0 R1 NHs XdC CELL_grm.
    assert (K_rm : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 0x1011b0) 8 = Some (LE8 (Z_to_bv 64 0xf56e4))) by konst EQ0 R1 NHs XdC CELL_rm.
    assert (K_cpm : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 0x106ddc) 1 = Some [Z_to_bv 8 CPM]).
    { rewrite <- w2b1 by lia. konst EQ0 R1 NHs XdC CELL_cpm. }
    assert (K_spb : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 0x103f38) 8 = Some (LE8 (Z_to_bv 64 (bt_spacebeg bt)))).
    { unfold free_cells_nb, IB in CELLNB. rewrite BT_ia in CELLNB. cbn [ia_instance asan_addrs Z.add] in CELLNB. konst EQ0 R1 NHs XdC CELLNB. }
    (* [comment removed for export] *)
    assert (K_len : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 (T + 80)) 8 = Some (LE8 (Z_to_bv 64 (Z.of_nat (length (a_tq st')))))) by cell0 EQ0 NHT XdT Qlen.
    assert (K_last : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 (T + 96)) 8 = Some (LE8 (Z_to_bv 64 (ba_addr b)))).
    { replace (T + 96) with (T + 80 + 16) by lia. cell0 EQ0 NHT XdT Qlast. }
    assert (K_qb : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 (T + 104)) 8 = Some (LE8 (Z_to_bv 64 (q_bytes (a_tq st'))))).
    { replace (T + 104) with (T + 80 + 24) by lia. cell0 EQ0 NHT XdT Qbytes. }
    assert (K_lcnt : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 (ba_addr b + 16)) 8 = Some (LE8 (Z_to_bv 64 1021))) by cell0 EQ0 NHbo XdBo Bcnt.
    assert (K_cnt24 : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 (T + 2128)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (Z.of_nat (length ks) + 1)))).
    { replace (T + 2128) with (T + 208 + 80 * 24) by lia. cell0 EQ0 NHT XdT PCcnt. }
    assert (K_cs : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 (T + 2136)) 8 = Some (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))).
    { replace (T + 2136) with (T + 208 + 80 * 24 + 8) by lia. cell0 EQ0 NHT XdT PCsz. }
    assert (K_k : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 (T + 2144 + 4 * (Z.of_nat (length ks) + 1 - 1))) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 k))).
    { replace (T + 2144 + 4 * (Z.of_nat (length ks) + 1 - 1)) with (T + 208 + 80 * 24 + 16 + 4 * Z.of_nat (length ks)) by lia. cell0 EQ0 NHT XdT PCk. }
    destruct (rdn_defined_ex ASEGS (mrestrict Hd M') (Z_to_bv 64 (T + 2784)) 8) as (bst & K_st & Lst).
    { intros i Hi. rewrite mrestrict_off; [| apply NHT; revert Hi; unorm; intros Hi; lia]. apply GR0.
      apply (writableZ_def M0 _ _ _ TW). revert Hi; unorm; intros Hi. lia. }
    { unorm. lia. }
    assert (K_nhi : rdn ASEGS (mrestrict Hd M') (at_ p (-14)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (m / 2 ^ 32)))).
    { replace (at_ p (-14)) with (Z_to_bv 64 (U p - 14)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). cell0 EQ0 NHp XdH Hnhi. }
    assert (K_nlo : rdn ASEGS (mrestrict Hd M') (at_ p (-12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (m mod 2 ^ 32)))).
    { replace (at_ p (-12)) with (Z_to_bv 64 (U p - 12)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). cell0 EQ0 NHp XdH Hnlo. }
    clear Qlen Qlast Qbytes Bnext Bsize Bcnt Bitems PCcnt PCsz PCk Hnhi Hnlo Csb R1.
    (* [comment removed for export] *)
    Ltac stk NHs C := rewrite rdn_mrestrict; [ exact C | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; hoff NHs ].
    assert (S_q0 : rdn ASEGS (mrestrict Hd M') (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6e4a4))) by stk NHs Cq0.
    assert (S_q1 : rdn ASEGS (mrestrict Hd M') (at_ S (-2144)) 8 = Some (LE8 S)) by stk NHs Cq1.
    assert (S_q2 : rdn ASEGS (mrestrict Hd M') (at_ S (-2152)) 8 = Some (LE8 p)) by stk NHs Cq2.
    assert (S_q3 : rdn ASEGS (mrestrict Hd M') (at_ S (-2160)) 8 = Some (LE8 (Z_to_bv 64 0x6e434))) by stk NHs Cq3.
    assert (S_q4 : rdn ASEGS (mrestrict Hd M') (at_ S (-2168)) 8 = Some (LE8 (Z_to_bv 64 1))) by stk NHs Cq4.
    assert (S_q5 : rdn ASEGS (mrestrict Hd M') (at_ S (-2176)) 8 = Some (LE8 (at_ S (-2128)))) by stk NHs Cq5.
    assert (S_i0 : rdn ASEGS (mrestrict Hd M') (at_ S (-8)) 8 = Some (LE8 (Z_to_bv 64 ret))) by (rewrite <- CP1; stk NHs Ci0).
    assert (S_i1 : rdn ASEGS (mrestrict Hd M') (at_ S (-16)) 8 = Some (LE8 (getr R 8))) by stk NHs Ci1.
    assert (S_i2 : rdn ASEGS (mrestrict Hd M') (at_ S (-24)) 8 = Some (LE8 (getr R 9))) by stk NHs Ci2.
    assert (S_i3 : rdn ASEGS (mrestrict Hd M') (at_ S (-32)) 8 = Some (LE8 (getr R 18))) by stk NHs Ci3.
    assert (S_i4 : rdn ASEGS (mrestrict Hd M') (at_ S (-40)) 8 = Some (LE8 (getr R 19))) by stk NHs Ci4.
    assert (S_i5 : rdn ASEGS (mrestrict Hd M') (at_ S (-48)) 8 = Some (LE8 (getr R 20))) by stk NHs Ci5.
    assert (S_i6 : rdn ASEGS (mrestrict Hd M') (at_ S (-56)) 8 = Some (LE8 (getr R 21))) by stk NHs Ci6.
    clear Cq0 Cq1 Cq2 Cq3 Cq4 Cq5 Ci0 Ci1 Ci2 Ci3 Ci4 Ci5 Ci6.
    (* [comment removed for export] *)
    assert (SOKstk : store_ok ASEGS (mrestrict Hd M') (at_ S (-2304)) 2304 = true).
    { rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; hoff NHs].
      apply store_ok_bytes; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. intros x Hx. rewrite at_u in Hx by lia.
      eapply store_ok_mono; [exact GRM|]. apply CPstk. cbn in Hx. rewrite <- CP2. lia. }
    assert (SOKp : store_ok ASEGS (mrestrict Hd M') p 8 = true).
    { rewrite store_ok_mrestrict; [| (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoff NHp].
      eapply store_ok_mono; [exact GR0|]. apply (writableZ_store_ok M0 _ _ _ _ WHDR); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia. }
    assert (SOKsh : store_ok ASEGS (mrestrict Hd M') (Z_to_bv 64 (shad p)) (Z.to_nat (up8 m / 8)) = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold shad in G in change_no_check G' end). rewrite store_ok_mrestrict; [| unorm; rewrite Z2Nat.id by lia; lia | unorm; rewrite Z2Nat.id by lia; hoff NHsh].
      eapply store_ok_mono; [exact GR0|]. apply (writableZ_store_ok M0 _ _ _ _ WSH); unorm; rewrite ?Z2Nat.id by lia; lia. }
    assert (SOKT : store_ok ASEGS (mrestrict Hd M') (Z_to_bv 64 T) (Z.to_nat 4096) = true).
    { rewrite store_ok_mrestrict; [| wd_ulia_c | unorm; hoff NHT].
      eapply store_ok_mono; [exact GR0|]. apply (writableZ_store_ok M0 _ _ _ _ TW); wd_ulia_c. }
    assert (SOKba : store_ok ASEGS (mrestrict Hd M') (Z_to_bv 64 ba) 32 = true).
    { rewrite store_ok_mrestrict; [| wd_ulia_c | unorm; hoff NHb].
      eapply store_ok_mono; [exact GR0|]. apply (writableZ_store_ok M0 _ _ _ _ BW); wd_ulia_c. }
    assert (SOKlast : store_ok ASEGS (mrestrict Hd M') (Z_to_bv 64 (ba_addr b)) 8 = true).
    { rewrite store_ok_mrestrict; [| wd_ulia_c | unorm; hoff NHbo].
      eapply store_ok_mono; [exact GR0|]. apply (writableZ_store_ok M0 _ _ _ _ BWb); wd_ulia_c. }
    clear WHDR WSH WBLK TW BW BWb.
    (* [comment removed for export] *)
    assert (GS3 : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0) by (rewrite CP2; lia).
    assert (Gn3 : 1 <= m <= 2 ^ 28) by lia.
    assert (Gn83 : AsRtRegion.down8 (m + 7) = up8 m /\ m <= up8 m <= m + 7 /\ up8 m mod 8 = 0 /\ 8 <= up8 m) by (split; [apply down8_up8Nf | lia]).
    assert (Gfl3 : 0 <= FL /\ FL + 4096 <= AIMGHI) by lia.
    assert (Gqb3 : 0 <= q_bytes (a_tq st') <= 2 ^ 20) by (clear - QA1 QA2 QA3 QA5; lia).
    assert (Glen3 : 1 <= Z.of_nat (length (a_tq st')) < 2 ^ 40) by (clear - QA4; lia).
    assert (Gcnt24 : 1 <= Z.of_nat (length ks) + 1 <= 16) by (clear - CL; lia).
    assert (Gk3 : 0 <= k < 2 ^ 32) by exact Kr.
    assert (Gspb : 0 <= bt_spacebeg bt) by (clear - SB0; lia).
    assert (Lbcs : length (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0))) = 8%nat) by apply length_N_to_le_bytes.

    assert (Gmid3 : U (Z_to_bv 64 MIDEND) < 2 ^ 64) by (wd_ulia).
    assert (Hret3 : ret_ok (Z_to_bv 64 ret)) by (apply ret_ok_lit; [lia | exact CPe]).
    assert (Ccpm1 : U (Z_to_bv 8 CPM) <> 0) by (rewrite (Z_to_bv_small 8 CPM ltac:(change (bv_modulus 8) with 256; lia)); lia).
    assert (D20' : getr R' 20 = Z_to_bv 64 T) by exact Y20.
    (* [comment removed for export] *)
    destruct (run_m3f (mrestrict Hd M') (seg_rom ASEGS) R' S p tp (getr R 22)
                T m (up8 m) id FL (ba_addr b) (q_bytes (a_tq st')) (Z.of_nat (length (a_tq st'))) (Z.of_nat (length ks) + 1) k (bt_spacebeg bt) ba
                (Z_to_bv 8 CPM) (Z_to_bv 64 MIDEND) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0))))
      as (rf & RUN3 & Z2 & Z22 & Z3 & Z4 & Z23 & Z24 & Z25 & Z26 & Z27).
    all: try assumption.
    all: try reflexivity.
    all: try (unfold hide in *; assumption).
    all: let k := numgoals in guard k = 1.
    (* [comment removed for export] *)
    replace (0x4fdc8%bv : word) with (Z_to_bv 64 0x4fdc8 : word) in RUN3 by (apply bv_eq; reflexivity).
    apply (katD_msteps_acct ASEGS Hd (HID_off_segments bt st' Lc FF M0 mdl' BT_ia RP') asanF_segs_wx (a_aa st')
             (@mkst fx' R' (Z_to_bv 64 0x4fdc8) M' (seg_rom ASEGS))
             (@mkst fx' rf (0x50194%bv : word) (fr_P3f (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) (seg_rom ASEGS)) mdl').
    { apply lazy_cover_HID. }
    { exact B1. }
    { exact B2. }
    { exact HH'. }
    { rewrite restrict_mkstF. exact RUN3. }
    clear RUN3 K_mcsz K_msz K_gfl K_mff K_gsh K_sh K_gmb K_mb K_gme K_me K_ghe K_he K_grm K_rm K_cpm K_spb K_len K_last K_qb K_lcnt K_cnt24 K_cs K_k K_st K_nhi K_nlo
          S_q0 S_q1 S_q2 S_q3 S_q4 S_q5 SOKstk SOKp SOKsh SOKT SOKba SOKlast.
    intros mdl3 MI3 SBM3 HC3. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx' R' (Z_to_bv 64 0x4fdc8) M' (seg_rom ASEGS))) with M' by reflexivity.
    pose proof (same_but_materialized_frame mdl' mdl3 SBM3) as SF3.
    destruct SF3 as (_ & Evm3 & Elz3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh3 & _ & _ & _ & Eeg3).
    remember (fr_P3f (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as M13 eqn:EM13.
    set (Mfin := munrestrict Hd M' M13).
    pose proof (fr_P3f_grows (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as GR13.
    feed GR13. rewrite <- EM13 in GR13.
    assert (VIS : forall a : word, Hd a = false -> Mfin a = M13 a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold Mfin in G in change_no_check G' end); apply munrestrict_off; exact Ha).
    assert (HIDv : forall a : word, Hd a = true -> Mfin a = M' a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold Mfin in G in change_no_check G' end); apply munrestrict_on; exact Ha).
    assert (MrM' : forall a : word, Hd a = false -> mrestrict Hd M' a = M' a) by (intros a Ha; apply mrestrict_off; exact Ha).
    assert (GRfin' : mem_grows M' Mfin).
    { intros a Ha. destruct (Hd a) eqn:Eh; [rewrite (HIDv a Eh); exact Ha | rewrite (VIS a Eh)]. apply GR13. rewrite (MrM' a Eh). exact Ha. }
    assert (GRfin : mem_grows M Mfin) by (eapply mem_grows_trans; [exact GRM | exact GRfin']).
    (* [comment removed for export] *)
    pose proof (fr_P3f_foot (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as P3F.
    feed P3F. rewrite <- EM13 in P3F.
    assert (DIFF3 : forall a : word, Mfin a <> M' a ->
              (U S - 2272 <= U a < U S - 2128) \/ (U p <= U a < U p + 8) \/ (0x7fff8000 + U p / 8 <= U a < 0x7fff8000 + U p / 8 + up8 m / 8)
              \/ (ba <= U a < ba + 32) \/ (T + 80 <= U a < T + 112) \/ (T + 2128 <= U a < T + 2132) \/ (T + 2784 <= U a < T + 2792)
              \/ (ba_addr b <= U a < ba_addr b + 8)).
    { intros a NE. destruct (Hd a) eqn:Eh; [exfalso; apply NE; apply HIDv; exact Eh|].
      rewrite (VIS a Eh) in NE. rewrite <- (MrM' a Eh) in NE. exact (P3F a NE). }
    (* [comment removed for export] *)
    assert (PRIVp : forall z, (U p - 16 <= z < U p + up8 m \/ sh_lo (U p) <= z < sh_hi (U p) m) -> rt_priv asan_addrs (L1 ++ L2) FF z).
    { intros z Hz. exact (OBL_freed_private st' Lc FF L1 L2 (U p) m z W' ELc Hz). }
    assert (PRIVT : forall z, T <= z < T + 4096 -> rt_priv asan_addrs (L1 ++ L2) FF z).
    { intros z Hz. destruct (OBL_rt_private st' Lc FF z W' ltac:(left; (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); exact Hz)) as (Z1' & Z2' & Z3').
      split; [exact Z1'|]. split; [exact Z2'|]. intros V. apply Z3'. rewrite ELc. apply app_visible_mono. exact V. }
    assert (PRIVB : forall z, ba <= z < ba + 8192 -> rt_priv asan_addrs (L1 ++ L2) FF z).
    { intros z Hz. destruct (Bpriv z Hz) as (Z1' & Z2' & Z3'). split; [exact Z1'|]. split; [exact Z2'|]. intros V. apply Z3'. rewrite ELc. apply app_visible_mono. exact V. }
    assert (PRIVBo : forall z, ba_addr b <= z < ba_addr b + 8192 -> rt_priv asan_addrs (L1 ++ L2) FF z).
    { intros z Hz. destruct (OBL_rt_private st' Lc FF z W' ltac:(right; exists b; split; [exact HinB | (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); exact Hz])) as (Z1' & Z2' & Z3').
      split; [exact Z1'|]. split; [exact Z2'|]. intros V. apply Z3'. rewrite ELc. apply app_visible_mono. exact V. }
    clear OBL_freed_private OBL_rt_private Bpriv.
    (* [comment removed for export] *)
    assert (XS : forall kk bs0, -2304 <= kk -> kk + 8 <= 0 -> rdn ASEGS M13 (at_ S kk) 8 = Some bs0 -> rdn ASEGS Mfin (at_ S kk) 8 = Some bs0).
    { intros kk bs0 Hk1 Hk2 Hr. apply (rd_same ASEGS Mfin M13); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hr].
      intros x Hx. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [apply u64_range|]. rewrite at_u in Hx by lia. cbn in Hx. lia. }
    pose proof (fr_P3f_stk (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as P3K.
    feed P3K. rewrite <- EM13 in P3K.
    assert (XH : forall kk bs0, -2128 <= kk -> kk + 8 <= 0 -> rdn ASEGS (mrestrict Hd M') (at_ S kk) 8 = Some bs0 -> rdn ASEGS M13 (at_ S kk) 8 = Some bs0).
    { intros kk bs0 Hk1 Hk2 Hr. apply (rd_same ASEGS M13 (mrestrict Hd M')); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hr].
      intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply P3K. lia. }
    replace (0x50194%bv : word) with (Z_to_bv 64 0x50194 : word) by (apply bv_eq; reflexivity).
    apply (free_put_tail bt FXOK KDR BT_segs BT_ia GEOM G_KDR HYP_DRAIN HP HPc FAM
             h fx' R rf M Mfin mdl mdl3 (L1 ++ L2) FF (Z.max 0 (B - (m + MBLK))) (Z.max 0 (C - 1)) K1 ret sp
             (op_quar_newbatch (op_cache_pop st' BATCHCLASS) ba (U p - 16) m) p (Z_to_bv 64 0x6e434) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81))
             (Z_to_bv 64 m) (at_ S (-2128)) (at_ (Z_to_bv 64 T) 208) (at_ p (-16))).
    all: rewrite ?BT_ia.
    - exact CP1.
    - exact CPr.
    - exact CPe.
    - exact CP2.
    - exact CP16.
    - exact CPlo.
    - exact CPhi.
    - exact CP4.
    - exact HFX'.
    - rewrite Eh3. exact HH'.
    - exact (model_ivs_wf_sbm mdl' mdl3 SBM3 MW').
    - (lazymatch goal with |- ?G => let G' := eval unfold ba in G in change_no_check G' end). exact (OPS_WFX_newbatch st' Lc FF L1 L2 (U p) m k ks W' (hp_kcap bt HP HPc FAM h st' HLE) ELc ECA).
    - (* [comment removed for export] *)
      assert (XF : forall c bs0, 0 <= c -> c + 8 <= 2 ^ 64 -> (forall z, c <= z < c + 8 -> Hd (Z_to_bv 64 z) = false) ->
                rdn ASEGS M13 (Z_to_bv 64 c) 8 = Some bs0 -> rdn ASEGS Mfin (Z_to_bv 64 c) 8 = Some bs0).
      { intros c bs0 Hc1 Hc2 NH Hr. apply (rd_same ASEGS Mfin M13); [| wd_ulia_c | exact Hr].
        intros x Hx. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NH. revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia. }
      pose proof (fr_P3f_hdr16 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as P3H. feed P3H.
      pose proof (fr_P3f_shadow (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as P3S. feed P3S.
      pose proof (fr_P3f_b0 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as Pb0. feed Pb0.
      pose proof (fr_P3f_b8 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as Pb8. feed Pb8.
      pose proof (fr_P3f_b16 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as Pb16. feed Pb16.
      pose proof (fr_P3f_b24 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as Pb24. feed Pb24.
      pose proof (fr_P3f_q80 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as Pq80. feed Pq80.
      pose proof (fr_P3f_first (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as Pfirst. feed Pfirst.
      pose proof (fr_P3f_last (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as Plast. feed Plast.
      pose proof (fr_P3f_q96 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as Pq96. feed Pq96.
      pose proof (fr_P3f_q104 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as Pq104. feed Pq104.
      pose proof (fr_P3f_cnt (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as Pcnt. feed Pcnt.
      rewrite <- EM13 in P3H, P3S, Pb0, Pb8, Pb16, Pb24, Pq80, Pfirst, Plast, Pq96, Pq104, Pcnt.
      assert (XF4 : forall c bs0, 0 <= c -> c + 4 <= 2 ^ 64 -> (forall z, c <= z < c + 4 -> Hd (Z_to_bv 64 z) = false) ->
                rdn ASEGS M13 (Z_to_bv 64 c) 4 = Some bs0 -> rdn ASEGS Mfin (Z_to_bv 64 c) 4 = Some bs0).
      { intros c bs0 Hc1 Hc2 NH Hr. apply (rd_same ASEGS Mfin M13); [| wd_ulia_c | exact Hr].
        intros x Hx. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NH. revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia. }
      apply (OPS_REP_quar_newbatch2x_pf bt st' Lc FF L1 L2 M0 Mfin mdl' mdl3 (U p) m k ks W' RP' ELc ECA).
      * (* [comment removed for export] *)
        intros a NE. pose proof (u64_range a) as Ha. split; cycle 1.
        { destruct (Mfin a) eqn:EF; [discriminate|]. exfalso. apply NE. destruct (M0 a) eqn:E0; [|reflexivity]. exfalso.
          assert (D : M0 a <> None) by (rewrite E0; discriminate). apply GR0, GRfin' in D. rewrite EF in D. exact (D eq_refl). }
        (lazymatch goal with |- ?G => let G' := eval unfold foot_quar_newbatch in G in change_no_check G' end). rewrite ETQ, rev_app_distr. (lazymatch goal with |- ?G => let G' := eval cbn [rev app] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold T_QC, T_PC, PC_SZ, BATCHCLASS in G in change_no_check G' end).
        destruct (decide (Mfin a = M' a)) as [E|N].
        { rewrite E in NE. destruct (DX a NE) as [X _]. unfold Xd in X. rewrite CP2 in X.
          destruct X as [X|[X|[X|X]]]; [left; exact X | right; left; exact X | do 7 right; left; lia | do 8 right; lia]. }
        destruct (DIFF3 a N) as [X|[X|[X|[X|[X|[X|[X|X]]]]]]].
        { do 8 right. rewrite CP2 in X. lia. }
        { right; left. exact X. }
        { right; right; left. unfold sh_lo, sh_hi, SB in *. lia. }
        { do 3 right; left. exact X. }
        { do 4 right; left. lia. }
        { do 6 right; left. lia. }
        { do 7 right; left. lia. }
        { do 5 right; left. exact X. }
      * (* [comment removed for export] *)
        (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN in G in change_no_check G' end). rewrite BT_segs. rewrite w2b1 by lia. apply heap_rdn1; [wd_ulia|].
        replace (Z_to_bv 64 (U p - 16)) with (at_ p (-16)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
        assert (Eh : Hd (at_ p (-16)) = false) by (rewrite <- (Z_to_bv_bv_unsigned 64 (at_ p (-16))); rewrite at_u by lia; apply NHp; lia).
        rewrite (VIS _ Eh). rewrite P3H. rewrite (MrM' _ Eh). exact Hb16.
      * (* [comment removed for export] *)
        intros g Hg. pose proof (granule_idx (U p) m g P8 Hg) as GI.
        (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN in G in change_no_check G' end). rewrite BT_segs. rewrite w2b1 by lia. unfold user_granule in Hg. apply heap_rdn1; [(lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end); wd_ulia|].
        assert (Eh : Hd (Z_to_bv 64 (SB + g)) = false) by (apply NHsh; (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, sh_hi, SB in G in change_no_check G' end); lia).
        rewrite (VIS _ Eh). replace (SB + g) with (SB + U p / 8 + (g - U p / 8)) by lia. (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end). apply P3S. exact GI.
      * (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. apply XF; [lia | lia | intros z Hz; apply NHb; lia |]. exact Pb0.
      * (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end). replace (8192 + m) with (m + 8192) by lia.
        apply XF; [lia | lia | intros z Hz; apply NHb; lia |]. exact Pb8.
      * (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. apply XF; [lia | lia | intros z Hz; apply NHb; lia |]. exact Pb16.
      * (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. apply XF; [lia | lia | intros z Hz; apply NHb; lia |].
        replace (Z_to_bv 64 (U p - 16)) with (at_ p (-16)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). exact Pb24.
      * (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold T_QC in G in change_no_check G' end).
        apply XF; [lia | lia | intros z Hz; apply NHT; lia |]. exact Pq80.
      * intros Enil. exfalso. rewrite ETQ in Enil. destruct tq'; discriminate Enil.
      * intros b0 q0 Eb. (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold T_QC in G in change_no_check G' end). replace (T + 80 + 8) with (T + 88) by lia.
        rewrite Eb in Qfirst. unfold T_QC in Qfirst. replace (T + 80 + 8) with (T + 88) in Qfirst by lia.
        apply (rd_same ASEGS Mfin M0); [| wd_ulia_c | exact Qfirst].
        intros x Hx.
        assert (Ehx : Hd x = false) by (rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHT; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia).
        rewrite (VIS x Ehx). rewrite Pfirst by (revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia).
        rewrite (MrM' x Ehx). apply EQ0. apply XdT. revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia.
      * (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold T_QC in G in change_no_check G' end). replace (T + 80 + 16) with (T + 96) by lia.
        apply XF; [lia | lia | intros z Hz; apply NHT; lia |]. exact Pq96.
      * (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold T_QC, BATCHSZ in G in change_no_check G' end). replace (T + 80 + 24) with (T + 104) by lia.
        apply XF; [lia | lia | intros z Hz; apply NHT; lia |]. exact Pq104.
      * intros tq'' b'' Etq. rewrite ETQ in Etq. apply app_inj_tail in Etq. destruct Etq as [_ Eb]. subst b''.
        (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. apply XF; [lia | lia | intros z Hz; apply NHbo; lia |]. exact Plast.
      * (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ, BATCHCLASS in G in change_no_check G' end). replace (T + 208 + 80 * 24) with (T + 2128) by lia.
        replace (Z.of_nat (length ks)) with (Z.of_nat (length ks) + 1 - 1) by lia.
        apply XF4; [lia | lia | intros z Hz; apply NHT; lia |]. exact Pcnt.
      * exact SBM3.
      * exact MI3.
    - (* [comment removed for export] *)
      assert (PH0 : 0 <= PHI (L1 ++ L2)).
      { apply PHI_nonneg. intros q n0 Hin.
        assert (Hin' : In (q, n0) Lc).
        { rewrite ELc. apply in_app_iff in Hin. apply in_app_iff. destruct Hin as [Hin|Hin]; [left; exact Hin | right; right; exact Hin]. }
        destruct (live_range bt _ _ _ W' q n0 Hin') as (_ & _ & X & _). lia. }
      unfold bounds in BD' |- *. (lazymatch goal with |- ?G => let G' := eval cbn [a_kact op_quar_newbatch op_cache_pop set_tq set_cache] in G in change_no_check G' end).
      rewrite ELc in BD'. rewrite PHI_app in BD' |- *. cbn [PHI snd fst] in BD'. rewrite length_app in BD' |- *. cbn [length] in BD'.
      rewrite PHI_app in PH0. unfold kcost_free, MBLK in *.
      destruct BD' as (BDa & BDb & BDc). split; [lia|]. split; [lia|]. lia.
    - (* [comment removed for export] *)
      apply (hp_neut bt HP HPc FAM h st' _ HLE); [| exact (fk_trans _ _ _ (fk_cache_pop bt st' BATCHCLASS (or_introl eq_refl)) (fk_quar_newbatch _ _ _ _)) | reflexivity].
      intros h' H'. unfold holes_le in H' |- *. (lazymatch goal with |- ?G => let G' := eval cbn [a_reg op_quar_newbatch op_cache_pop set_tq set_cache] in G in change_no_check G' end). exact H'.
    - (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval cbn [a_gq op_quar_newbatch op_cache_pop set_tq set_cache] in G in change_no_check G' end). exact QGB.
    - (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval cbn [a_tq op_quar_newbatch op_cache_pop set_tq set_cache] in G in change_no_check G' end). intros E. apply app_eq_nil in E. destruct E as [_ E]. discriminate E.
    - (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval cbn [a_tq op_quar_newbatch op_cache_pop set_tq set_cache] in G in change_no_check G' end). rewrite q_bytes_app.
      replace (q_bytes [BATCH ba [(U p - 16, m)]]) with (BATCHSZ + (m + 0) + 0) by reflexivity.
      clear - QA1 QA2 QA3 QA5 M28 Lp3. unfold BATCHSZ in *. lia.
    - (* [comment removed for export] *)
      intros z Hz. transitivity (lzb mdl' z); [(lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz3; reflexivity|]. apply LZT. exact Hz.
    - exact Z2. - exact Z22. - rewrite Z3; exact Y3. - rewrite Z4; reflexivity. - rewrite Z23; exact Y23. - rewrite Z24; exact Y24.
    - rewrite Z25; exact Y25. - rewrite Z26; exact Y26. - rewrite Z27; exact Y27.
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3f_e0 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance asan_addrs] in G in change_no_check G' end). apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3f_e1 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3f_e2 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3f_e3 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3f_e4 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3f_e5 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3f_e6 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3f_cb0 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3f_cb1 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3f_q0 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3f_q1 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3f_q2 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3f_q3 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3f_q4 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3f_q5 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3f_q6 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3f_q7 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (Z.of_nat (length ks) + 1) k ba (q_bytes (a_tq st')) (ba_addr b) (Z.of_nat (length (a_tq st'))) bst (LE8 (Z_to_bv 64 (if a_cinit st' then csize 24 else 0)))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | apply XH; [lia | lia | fold ra0; rewrite CP1; exact S_i0]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_i1]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_i2]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_i3]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_i4]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_i5]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_i6]].
    - (* [comment removed for export] *)
      intros a Ha. rewrite <- CP2 in Ha. unfold MSTK_A in Ha. split.
      + apply GRfin. apply store_ok1_heap; [clear - Ha CPlo CP2 CR; lia|]. apply CPstk. rewrite <- CP2. lia.
      + eapply store_ok_mono; [exact GRfin|]. apply CPstk. rewrite <- CP2. lia.
    - (* [comment removed for export] *)
      intros a NE. pose proof (u64_range a) as Ha. (lazymatch goal with |- ?G => let G' := eval unfold as_changed in G in change_no_check G' end). rewrite <- CP2. (lazymatch goal with |- ?G => let G' := eval unfold MSTK_A in G in change_no_check G' end).
      destruct (decide (Mfin a = M' a)) as [E|N].
      { rewrite E in NE. destruct (CHG a NE) as [[X|[X|[X|X]]] _].
        - unfold Xd in X. destruct X as [X|[X|[X|X]]].
          + right; left. apply PRIVp. left. lia.
          + right; left. apply PRIVp. left. lia.
          + right; left. apply PRIVT. lia.
          + left. lia.
        - left. lia.
        - right; left. destruct X as (X1 & X2 & X3). split; [exact X1|]. split; [exact X2|]. intros V. apply X3. rewrite ELc. apply app_visible_mono. exact V.
        - right; right; left. exact X. }
      destruct (DIFF3 a N) as [X|[X|[X|[X|[X|[X|[X|X]]]]]]].
      + left. lia.
      + right; left. apply PRIVp. left. lia.
      + right; left. apply PRIVp. right. unfold sh_lo, sh_hi, SB in *. lia.
      + right; left. apply PRIVB. lia.
      + right; left. apply PRIVT. lia.
      + right; left. apply PRIVT. lia.
      + right; left. apply PRIVT. lia.
      + right; left. apply PRIVBo. lia.
    - exact GRfin.
    - eapply same_except_vm_trans; [exact SEV | apply same_but_materialized_except_vm; exact SBM3].
    - (* [comment removed for export] *) intros a Ha. transitivity (lzb mdl' a); [(lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz3; reflexivity|]. apply LZ.
      destruct Ha as [V|[V|V]]; [left; rewrite ELc; apply app_visible_mono; exact V | right; left; exact V | right; right; exact V].
  Qed.
End PUTNf.



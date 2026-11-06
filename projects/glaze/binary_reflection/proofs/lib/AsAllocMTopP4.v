(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.glaze.binary_reflection.images.Asan OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocMTopP2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.AsAinvOpsQ3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop.AsAllocMMemAm OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1.AsAllocM3q OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1.AsAllocMRunS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop.AsAllocMTopA.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop.AsDepotHyp8 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop.AsAllocMXTrk.

Import OSSVerify.glaze.binary_reflection.images.Asan.

Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsLia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac am_inner ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | hs_am_lia ].   (* [comment removed for export] *)
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma mod4096_mod8s : forall t, t mod 4096 = 0 -> t mod 8 = 0.
Proof. intros t Ht. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma restrict_mkst_s : forall {fx : FPState} (Hd : word -> bool) (r : bvmap 5 word) pc m rom,
  restrict Hd (@mkst fx r pc m rom) = @mkst fx r pc (mrestrict Hd m) rom.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Definition uncharge (st : ast) : ast :=
  AST (a_reg st) (a_cinit st) (a_cache st) (a_tq st) (a_gq st) (a_sec st) (a_nres st) (a_dep st) (a_hint st) (a_ialloc st)
      (a_aa st) (a_kact st - EVT) (a_shsec st).

Section WithCeil.
Context {RC : run_ceil}.

Section TOPP2.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND KD : Z).
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis G_KD : 0 <= KD <= 1312.
  Hypothesis HYP_DEPOT : AsAllocFHyp.HYP_DEPOT_stmt bt FXOK KD.   (* [comment removed for export] *)

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).

  Ltac rne := let E := fresh "E" in intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate E.

  (* [comment removed for export] *)
  Theorem malloc_suffix :
    forall fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (ret sp n : Z) (st : ast) (ks : list Z) (kk : Z)
           (rq : bvmap 5 word) (Mq : mem) (mdlq : Model) (x18 x19 : word) (sz : Z) (bsz : list byte),
      FXOK fx -> m_halted mdlq = None -> BackingAlgebra.model_ivs_wf mdlq ->
      WF bt st Lc FF -> Rep bt st Lc FF Mq mdlq ->
      call_pre ASEGS asan_addrs R M ret sp MSTK_A -> 1 <= n <= 64512 ->
      a_cache st (class_of (needed n)) = ks ++ [kk] ->
      let S := getr R 2 in
      let c := class_of (needed n) in
      let p := chunk_of_compact SBEG c kk + rz n in
      (* [comment removed for export] *)
      getr rq 10 = Z_to_bv 64 1 -> getr rq 2 = at_ S (-2320) -> getr rq 8 = Z_to_bv 64 c -> getr rq 9 = at_ (Z_to_bv 64 T) (208 + 80 * c) ->
      getr rq 18 = Z_to_bv 64 8 -> getr rq 19 = at_ (Z_to_bv 64 T) 208 -> getr rq 20 = Z_to_bv 64 0x103f18 -> getr rq 21 = Z_to_bv 64 n ->
      getr rq 22 = Z_to_bv 64 0x103f18 -> getr rq 23 = at_ S (-2128) -> getr rq 25 = Z_to_bv 64 7 -> getr rq 26 = Z_to_bv 64 T -> getr rq 27 = Z_to_bv 64 1 ->
      getr rq 4 = getr R 4 -> getr rq 3 = getr R 3 ->
      (* [comment removed for export] *)
      (forall (k0 : Z) (v : word), In (k0, v) (ma_slotsA S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)) ->
          rdn ASEGS Mq (at_ S k0) 8 = Some (LE8 v)) ->
      (forall (k0 : Z) (v : word),
          In (k0, v) [(-8, getr R 1); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
          rdn ASEGS Mq (at_ S k0) 8 = Some (LE8 v)) ->
      rdn ASEGS Mq (at_ S (-2120)) 4 = Some (LE4 sz) -> rdn ASEGS Mq (at_ S (-2120)) 8 = Some bsz -> length bsz = 8%nat -> (1 <= sz <= 8 /\ bytes_le_to_Z bsz = sz) ->
      rdn ASEGS Mq (at_ S (-2128)) 8 = Some (LE8 (at_ S (-2112))) ->
      (forall (o : Z) (v : word),
          In (o, v) [(-8, at_ ARB 0x4bdc4); (-16, Z_to_bv 64 1); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 (needed n)); (-48, Z_to_bv 64 (rz n))]%Z ->
          rdn ASEGS Mq (at_ (at_ S (-2272)) o) 8 = Some (LE8 v)) ->
      (forall a : word, sp - MSTK_A <= U a < sp -> Mq a <> None /\ store_ok ASEGS Mq a 1%nat = true) ->
      (* [comment removed for export] *)
      (forall a : word, Mq a <> M a ->
          (Xm (U S) T c p (U a) \/ (U S - 3584 <= U a < U S - 2272) \/ rt_priv (bt_ia bt) Lc FF (U a) \/ in_wins (ia_priv (bt_ia bt)) (U a))
          /\ Mq a <> None) ->
      same_except_vm mdl mdlq -> lazy_kept (bt_ia bt) Lc FF mdl mdlq ->
      a_kact st <= KCAP ->                                                            (* [comment removed for export] *)
      depot_room bt st ->                                                               (* [comment removed for export] *)
      (exists h : option Z, holes_le h st) ->                                           (* [comment removed for export] *)
      katD ASEGS (mkCfg (@mkst fx rq (Z_to_bv 64 0x5052c) Mq (seg_rom ASEGS)) mdlq) (runA_post bt FXOK (uncharge st) ks kk Lc FF R M mdl n).
  Proof using HYP_DEPOT G_KD GEOM CELLS BT_ia BT_segs KD MIDEND FL PGP TSDP TP.
    intros fx R M mdl Lc FF ret sp n st ks kk rq Mq mdlq x18 x19 sz bsz HFX HH MW W RP CP Hn HC S c p
           Q10 Q2 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q25 Q26 Q27 Q4 Q3 FA FI FS4 FS8 Lsz SZ1 FTR FC STKq ACC SEVq LKq KCq DR HOLES.
    pose proof ceil_rng as CR. pose proof ceil_pg as CPG.
    set (ab := chunk_of_compact SBEG c kk) in *.
    destruct CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk). fold S in CP2.
    destruct CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CELL_kif & CELL_key & CELL_tsdp & CELL_tctx
                      & CELL_rss & CELL_lmag & CELL_tbl2 & CELL_t16 & CELL_t2048 & CELL_minrz & CELL_maxrz & CELL_maxsz & CELL_sbeg & _).
    destruct GEOM as (GCT & Gtop & Gbot).
    pose proof (free_obls_pf bt) as (OBL_nolazy_rt & _ & OBL_rt_private & OBL_stats_not_rep & _ & _ & _ & OBL_X_vs_node & OBL_store_private).
    unfold OBL_nolazy_rt_stmt in OBL_nolazy_rt. unfold OBL_rt_private_stmt in OBL_rt_private. unfold OBL_stats_not_rep_stmt in OBL_stats_not_rep.
    unfold OBL_X_vs_node_stmt in OBL_X_vs_node. unfold OBL_store_private_stmt in OBL_store_private.
    (* [comment removed for export] *)
    pose proof (mc_needed n Hn) as (NF1 & NF2 & NF3 & NF4 & NF5 & NF6 & NF7 & NF8). fold c in NF3, NF4.
    pose proof (mc_chunk bt st Lc FF Mq mdlq n ks kk W RP Hn HC) as (CV & A1 & A2 & A16 & Hkk & AT & ACT & ALIV & ABAT & ANL & AW & APRIV).
    fold c in CV, A1, A2, A16, AT, ACT, ALIV, ABAT, ANL, AW, APRIV. fold ab in CV, A1, A2, A16, AT, ACT, ALIV, ABAT, ANL, AW, APRIV.
    pose proof (mc_pclass bt st Lc FF Mq mdlq n ks kk W RP Hn HC) as (Pcnt & Pk & (cszv & Pcsz) & Plen). fold c in Pcnt, Pk, Pcsz.
    pose proof (mc_vs_node bt st Lc FF Mq mdlq n ks kk W RP Hn HC) as ANODE. fold c ab in ANODE.
    hidehyp GCT.
    (* [comment removed for export] *)
    pose proof (thread_dyn bt st Lc FF W) as (GT0 & GTC & GTI & GTB & TPG & GC0 & GCC & GCI & GCB & SB0 & SB1). hidehyp GCB.
    hidehyp GTB.
    assert (GT4 : 4096 <= T) by (unfold PG in TPG; clear - GT0 TPG; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18).
    destruct R3 as (Tctx & Ttop & Tbot & Tsw & Tfs & Tunw & TQ & TPC & TW & Tback & Ttid & Ttls1 & Ttls2).
    rewrite BT_segs in *. rewrite BT_ia in *. cbn [ia_img_lo ia_img_hi asan_addrs] in GTI, GCI.
    pose proof (u64_range S) as HSr.
    unfold PTRHI in CPlo, CPhi. unfold AS_HEAPLO, AS_LO, MSTK_A, PG, KSPACE, NMAX in *.
    (* [comment removed for export] *)
    set (Hd := HID st mdlq).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdlq z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi asan_addrs] in G in change_no_check G' end). lia. }
    assert (NHrt : forall z, (T <= z < T + 4096) \/ (CTX <= z < CTX + 0x10000) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (OBL_nolazy_rt st Lc FF Mq mdlq z W RP). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). clear - Hz. tauto. }
    assert (NHab : forall z, ab <= z < ab + csize c -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. exact (ANL z Hz). }
    destruct R14 as (Bw1 & Bw2 & Bw3 & Bw4 & Bw5).
    set (Mr := mrestrict Hd Mq).
    Ltac hoff NH := apply hid_off_of; intros z Hz; unfold T_UNW, T_QC, T_PC, PC_SZ in *; split; [lia | apply NH; lia].
    Ltac konst Hd M R1 NHs C := apply (cellZ_restrict Hd M _ _ _ (const_cell bt M _ _ _ R1 C)); [lia | lia | hoff NHs].
    Ltac thr_cell Hd M NHrt C := apply (cellZ_restrict Hd M _ _ _ C); [(lazymatch goal with |- ?G => let G' := eval unfold T_UNW, T_QC, T_PC, PC_SZ in G in change_no_check G' end); lia | unfold T_UNW, T_QC, T_PC, PC_SZ in *; lia | hoff NHrt].
    set (thr := Z_to_bv 64 T : word). set (ctxw := Z_to_bv 64 CTX : word). set (sbeg := Z_to_bv 64 SBEG : word).
    assert (Uthr : U thr = T) by ((lazymatch goal with |- ?G => let G' := eval unfold thr in G in change_no_check G' end); unorm; reflexivity).
    assert (Uctx : U ctxw = CTX) by ((lazymatch goal with |- ?G => let G' := eval unfold ctxw in G in change_no_check G' end); unorm; reflexivity).
    assert (Usb : U sbeg = SBEG) by ((lazymatch goal with |- ?G => let G' := eval unfold sbeg in G in change_no_check G' end); unorm; reflexivity).
    assert (Eab : ms_ab sbeg n kk = ab) by ((lazymatch goal with |- ?G => let G' := eval unfold ms_ab in G in change_no_check G' end); rewrite Usb; reflexivity).
    (* [comment removed for export] *)
    assert (K_sbeg : rdn ASEGS Mr (at_ (Z_to_bv 64 0x103f18) 32) 8 = Some (LE8 sbeg)).
    { replace (at_ (Z_to_bv 64 0x103f18) 32) with (Z_to_bv 64 0x103f38 : word) by (apply bv_eq; reflexivity). (lazymatch goal with |- ?G => let G' := eval unfold sbeg in G in change_no_check G' end). konst Hd Mq R1 NHs CELL_sbeg. }
    assert (K_T0 : rdn ASEGS Mr thr 8 = Some (LE8 ctxw)) by ((lazymatch goal with |- ?G => let G' := eval unfold thr, ctxw in G in change_no_check G' end); thr_cell Hd Mq NHrt Tctx).
    assert (K_tid : rdn ASEGS Mr (at_ ctxw 8) 4 = Some (LE4 0)).
    { (lazymatch goal with |- ?G => let G' := eval unfold ctxw in G in change_no_check G' end). replace (at_ (Z_to_bv 64 CTX) 8) with (Z_to_bv 64 (CTX + 8)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd Mq NHrt Ttid. }
    assert (K_cnt : rdn ASEGS Mr (at_ (at_ thr 208) (80 * c)) 4 = Some (LE4 (Z.of_nat (length ks) + 1))).
    { (lazymatch goal with |- ?G => let G' := eval unfold thr in G in change_no_check G' end). replace (at_ (at_ (Z_to_bv 64 T) 208) (80 * c)) with (Z_to_bv 64 (T + T_PC + PC_SZ * c)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_, T_PC, PC_SZ in G in change_no_check G' end); wd_ulia). thr_cell Hd Mq NHrt Pcnt. }
    assert (K_k : rdn ASEGS Mr (at_ (at_ thr 208) (80 * c + 16 + 4 * (Z.of_nat (length ks) + 1 - 1))) 4 = Some (LE4 kk)).
    { (lazymatch goal with |- ?G => let G' := eval unfold thr in G in change_no_check G' end). replace (at_ (at_ (Z_to_bv 64 T) 208) (80 * c + 16 + 4 * (Z.of_nat (length ks) + 1 - 1))) with (Z_to_bv 64 (T + T_PC + PC_SZ * c + 16 + 4 * Z.of_nat (length ks)))
        by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_, T_PC, PC_SZ in G in change_no_check G' end); wd_ulia). thr_cell Hd Mq NHrt Pk. }
    assert (K_csz : rdn ASEGS Mr (at_ (at_ thr 208) (80 * c + 8)) 8 = Some (LE8 (Z_to_bv 64 cszv))).
    { (lazymatch goal with |- ?G => let G' := eval unfold thr in G in change_no_check G' end). replace (at_ (at_ (Z_to_bv 64 T) 208) (80 * c + 8)) with (Z_to_bv 64 (T + T_PC + PC_SZ * c + 8)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_, T_PC, PC_SZ in G in change_no_check G' end); wd_ulia). thr_cell Hd Mq NHrt Pcsz. }
    (* [comment removed for export] *)
    assert (STKr : forall x : word, U S - 3584 <= U x < U S -> Mr x = Mq x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). apply mrestrict_off. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [pose proof (u64_range x); lia|]. left. rewrite CP2 in Hx. lia. }
    assert (RDr : forall (k : Z) (w : nat) (bs : list byte), -3584 <= k -> k + Z.of_nat w <= 0 -> rdn ASEGS Mq (at_ S k) w = Some bs -> rdn ASEGS Mr (at_ S k) w = Some bs).
    { intros k w bs K1 K2 Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]|]. intros x Hx. rewrite at_u in Hx by lia. apply STKr. lia. }
    assert (SOKT : store_ok ASEGS Mr thr 4096 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr, thr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| wd_ulia_c | unorm; hoff NHrt].
      apply (writableZ_store_ok Mq _ _ _ _ TW); wd_ulia_c. }
    assert (SOKh : store_ok ASEGS Mr (at_ (Z_to_bv 64 ab) (rz n - 16)) 16 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| rewrite at_u by (wd_ulia); wd_ulia_c | rewrite at_u by (wd_ulia); unorm; hoff NHab].
      apply (writableZ_store_ok Mq _ _ _ _ AW); rewrite ?at_u by (wd_ulia); wd_ulia_c. }
    destruct (rdn_defined_ex ASEGS Mr (Z_to_bv 64 (T + 2784)) 8) as (bst & Cst & Lst).
    { intros i Hi. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite mrestrict_off; [| apply NHrt; revert Hi; unorm; intros Hi; lia].
      apply (writableZ_def Mq _ _ _ TW). revert Hi; unorm; intros Hi. lia. }
    { unorm. lia. }
    set (stw := Z_to_bv 64 (bytes_le_to_Z bst) : word).
    assert (K_st : rdn ASEGS Mr (at_ (at_ thr 208) 2576) 8 = Some (LE8 stw)).
    { (lazymatch goal with |- ?G => let G' := eval unfold stw in G in change_no_check G' end). rewrite (word_to_le_bytes_of_bytes8 bst Lst).
      (lazymatch goal with |- ?G => let G' := eval unfold thr in G in change_no_check G' end). replace (at_ (at_ (Z_to_bv 64 T) 208) 2576) with (Z_to_bv 64 (T + 2784)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). exact Cst. }
    destruct (rdn_defined_ex ASEGS Mr (at_ (Z_to_bv 64 ab) (rz n - 15)) 1) as (bb1 & Cb1 & Lb1).
    { intros i Hi. rewrite at_u in Hi by (wd_ulia). (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite mrestrict_off; [| apply NHab; revert Hi; unorm; intros Hi; lia].
      apply (writableZ_def Mq _ _ _ AW). revert Hi; unorm; intros Hi. lia. }
    { rewrite at_u by (wd_ulia). unorm. lia. }
    destruct bb1 as [|b1 [|]]; try discriminate Lb1.
    (* [comment removed for export] *)
    set (rC := regupd (regupd (regupd (regupd (regupd (regupd (regupd rq 1 (at_ ARB 0x4bdc4)) 2 (at_ S (-2272))) 8 (Z_to_bv 64 1)) 9 (Z_to_bv 64 n)) 18 (Z_to_bv 64 8))
                      19 (Z_to_bv 64 (needed n))) 20 (Z_to_bv 64 (rz n))).
    assert (C1 : getr rC 1 = at_ ARB 0x4bdc4) by ((lazymatch goal with |- ?G => let G' := eval unfold rC in G in change_no_check G' end); rewrite !getr_other by rne; apply getr_same; rne).
    assert (C2 : getr rC 2 = at_ S (-2272)) by ((lazymatch goal with |- ?G => let G' := eval unfold rC in G in change_no_check G' end); rewrite !getr_other by rne; apply getr_same; rne).
    assert (C8 : getr rC 8 = Z_to_bv 64 1) by ((lazymatch goal with |- ?G => let G' := eval unfold rC in G in change_no_check G' end); rewrite !getr_other by rne; apply getr_same; rne).
    assert (C9 : getr rC 9 = Z_to_bv 64 n) by ((lazymatch goal with |- ?G => let G' := eval unfold rC in G in change_no_check G' end); rewrite !getr_other by rne; apply getr_same; rne).
    assert (C18 : getr rC 18 = Z_to_bv 64 8) by ((lazymatch goal with |- ?G => let G' := eval unfold rC in G in change_no_check G' end); rewrite !getr_other by rne; apply getr_same; rne).
    assert (C19 : getr rC 19 = Z_to_bv 64 (needed n)) by ((lazymatch goal with |- ?G => let G' := eval unfold rC in G in change_no_check G' end); rewrite !getr_other by rne; apply getr_same; rne).
    assert (C20 : getr rC 20 = Z_to_bv 64 (rz n)) by ((lazymatch goal with |- ?G => let G' := eval unfold rC in G in change_no_check G' end); apply getr_same; rne).
    assert (FRr : forall (o : Z) (v : word), In (o, v) (cb_slots2 rC (at_ ARB 0x4bdc4)) -> rdn ASEGS Mr (at_ (at_ S (-2272)) o) 8 = Some (LE8 v)).
    { intros o v Hin. unfold cb_slots2 in Hin. rewrite C8, C9, C18, C19, C20 in Hin.
      assert (Ho : -48 <= o <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      rewrite at_at. apply RDr; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at. exact (FC o v Hin). }
    assert (R16r : rdn ASEGS Mr (at_ (at_ S (-2272)) 16) 8 = Some (LE8 (Z_to_bv 64 16))).
    { rewrite at_at. apply RDr; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. apply (FA (-2256) (Z_to_bv 64 16)). (lazymatch goal with |- ?G => let G' := eval unfold ma_slotsA in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end). repeat (first [left; reflexivity | right]). }
    assert (Rtrr : rdn ASEGS Mr (at_ S (-2128)) 8 = Some (LE8 (at_ S (-2112)))) by (apply RDr; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact FTR]).
    assert (Rszr : rdn ASEGS Mr (at_ (at_ S (-2128)) 8) 8 = Some bsz) by (rewrite at_at; apply RDr; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact FS8]).
    assert (Q2' : getr rq 2 = at_ (at_ S (-2272)) (-48)) by (rewrite at_at; exact Q2).
    assert (Q9' : getr rq 9 = at_ (at_ thr 208) (80 * c)) by (rewrite at_at; exact Q9).
    assert (Hszw : bytes_le_to_Z bsz = U (Z_to_bv 64 (bytes_le_to_Z bsz)) /\ length bsz = 8%nat).
    { split; [| exact Lsz]. pose proof (bytes_le_to_Z_bound bsz) as Bb. rewrite Lsz in Bb. pose proof (bytes_le_to_Z_nonneg bsz). unorm. lia. }
    (* [comment removed for export] *)
    destruct (run_mA_suf Mr (seg_rom ASEGS) rq rC S thr ctxw sbeg (Z_to_bv 64 cszv) stw (at_ S (-2112)) (Z_to_bv 64 (bytes_le_to_Z bsz)) n
                (Z.of_nat (length ks) + 1) kk 0 b1 bsz)
      as (r4 & RUN & X1 & X2 & X10 & X11 & X8 & X9 & X18 & X19 & X20 & X21 & X24 & X25 & XK).
    all: try (first [ hs_assum | lazymatch goal with |- store_ok _ _ _ _ = _ => fail | _ => assumption end ]).
    all: rewrite ?Eab, ?Uthr, ?Uctx, ?Usb.
    all: try (first [ hs_assum | lazymatch goal with |- store_ok _ _ _ _ = _ => fail | _ => assumption end ]).
    all: try (hs_arith_goal; wd_ulia_c).
    all: try (hs_arith_goal; rewrite ?CP2; unfold hide, hideW in *; unfold PG in *; lia).
    all: try (rewrite CP2; split; [(lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); lia|]; split; [lia | apply mod4096_mod8s; exact TPG]).
    all: let k := numgoals in guard k = 1.
    rewrite Eab in *.
    (* [comment removed for export] *)
    match type of RUN with msteps _ _ (mkst _ _ ?mc _) => set (MC := mc) in * end.
    set (cnt := Z.of_nat (length ks) + 1) in *.
    assert (EMC : MC = ma_P2m Mr T n cnt stw (Z_to_bv 64 cszv) (Z_to_bv 64 ab) b1) by reflexivity.
    apply (katD_msteps_acct ASEGS Hd (HID_off_segments bt st Lc FF Mq mdlq BT_ia RP) asanF_segs_wx (a_aa st)
             (@mkst fx rq (Z_to_bv 64 0x5052c) Mq (seg_rom ASEGS)) (@mkst fx r4 (Z_to_bv 64 0x8ea80) MC (seg_rom ASEGS)) mdlq).
    { apply lazy_cover_HID. }
    { exact Bw1. }
    { exact Bw2. }
    { exact HH. }
    { rewrite restrict_mkst_s. exact RUN. }
    intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx rq (Z_to_bv 64 0x5052c) Mq (seg_rom ASEGS))) with Mq by reflexivity.
    pose proof (same_but_materialized_frame mdlq mdl1 SBM1) as SF1.
    set (MDin := munrestrict Hd Mq MC).
    (* [comment removed for export] *)
    set (st1 := st) in *.
    pose proof W as W1.
    destruct SF1 as (_ & Evm & Elz & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehl & _ & _ & _ & Eeg).
    pose proof (Rep_sbm bt st1 Lc FF Mq mdlq mdl1 RP MI1 SBM1) as RP1.
    (* [comment removed for export] *)
    assert (Uab : U (Z_to_bv 64 ab) = ab) by (unorm; reflexivity).
    assert (GSm : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47) by (rewrite CP2; lia).
    assert (GTm : 4096 <= T /\ T + 4096 <= U S - 3584) by (rewrite CP2; lia).
    assert (Gmm : AIMGHI <= U (Z_to_bv 64 ab) /\ U (Z_to_bv 64 ab) + needed n <= U S - 3584) by (rewrite Uab, CP2; lia).
    assert (MCB : forall x : word, (U x < ab + rz n - 15 \/ ab + rz n - 8 <= U x) -> MC x = ma_Bm Mr T n cnt stw (Z_to_bv 64 cszv) x).
    { intros x Hx. rewrite EMC. apply (mam_P2_outside Mr S T n cnt stw (Z_to_bv 64 cszv) (Z_to_bv 64 ab) b1 GSm Hn Gmm). rewrite Uab. exact Hx. }
    assert (MBr : forall x : word, (U x < T + 208 + 80 * c \/ T + 208 + 80 * c + 4 <= U x) -> (U x < T + 2784 \/ T + 2792 <= U x) ->
               ma_Bm Mr T n cnt stw (Z_to_bv 64 cszv) x = Mr x).
    { intros x H1 H2. apply (mam_B_outside Mr S T n cnt stw (Z_to_bv 64 cszv) GSm GTm Hn); assumption. }
    assert (GRall : mem_grows Mr MC).
    { rewrite EMC. eapply mem_grows_trans; [apply mam_B_grows | apply mam_P2_grows]. }
    assert (GRin : mem_grows Mq MDin).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MDin, munrestrict in G in change_no_check G' end). destruct (Hd x) eqn:Ex; [exact Hx|]. apply GRall. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite mrestrict_off by exact Ex. exact Hx. }
    (* [comment removed for export] *)
    assert (DIFF1 : forall a : word, MDin a <> Mq a -> Xm (U S) T c p (U a) /\ MDin a <> None).
    { intros a NE. pose proof (u64_range a) as Ha.
      split; cycle 1.
      { destruct (MDin a) eqn:E1; [discriminate|]. exfalso. apply NE. destruct (Mq a) eqn:E2; [|reflexivity].
        exfalso. assert (X : Mq a <> None) by (rewrite E2; discriminate). apply GRin in X. rewrite E1 in X. exact (X eq_refl). }
      unfold MDin, munrestrict in NE. destruct (Hd a) eqn:Eh; [exfalso; exact (NE eq_refl)|].
      assert (EMr : Mr a = Mq a) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); apply mrestrict_off; exact Eh).
      (lazymatch goal with |- ?G => let G' := eval unfold Xm, T_PC, PC_SZ in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold p in G in change_no_check G' end).
      destruct (Z.lt_ge_cases (U a) (ab + rz n - 15)) as [L1|L1]; [| destruct (Z.lt_ge_cases (U a) (ab + rz n - 8)) as [L2|L2]; [right; right; right; lia|]].
      all: rewrite MCB in NE by lia.
      all: destruct (Z.lt_ge_cases (U a) (T + 208 + 80 * c)) as [L3|L3];
           [ exfalso; apply NE; rewrite MBr by lia; exact EMr
           | destruct (Z.lt_ge_cases (U a) (T + 208 + 80 * c + 4)) as [L4|L4];
             [ right; left; lia
             | destruct (Z.lt_ge_cases (U a) (T + 2784)) as [L5|L5];
               [ exfalso; apply NE; rewrite MBr by lia; exact EMr
               | destruct (Z.lt_ge_cases (U a) (T + 2792)) as [L6|L6];
                 [ right; right; left; lia
                 | exfalso; apply NE; rewrite MBr by lia; exact EMr ] ] ] ]. }
    (* [comment removed for export] *)
    assert (VIS : forall a : word, Hd a = false -> MDin a = MC a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold MDin in G in change_no_check G' end); apply munrestrict_off; exact Ha).
    assert (VISstk : forall a : word, U S - 3584 <= U a < U S -> MDin a = Mq a).
    { intros a Ha. rewrite VIS by (rewrite <- (Z_to_bv_bv_unsigned 64 a); apply NHs; [pose proof (u64_range a); lia | left; rewrite CP2 in Ha; lia]).
      rewrite MCB by lia. rewrite MBr by lia. apply STKr. exact Ha. }
    (* [comment removed for export] *)
    assert (SZW : U (Z_to_bv 64 (bytes_le_to_Z bsz)) mod 2 ^ 32 = sz).
    { pose proof (bytes_le_to_Z_bound bsz) as Bb. rewrite Lsz in Bb. pose proof (bytes_le_to_Z_nonneg bsz). unorm. apply (lez_low32 ASEGS Mq (at_ S (-2120)) bsz sz FS8 FS4). lia. }
    assert (TAGW : U (Z_to_bv 64 (bytes_le_to_Z bsz)) / 2 ^ 32 < 256).
    { rewrite (proj2 SZ1). rewrite u_Z2bv by (clear - SZ1; lia). rewrite Z.div_small by (clear - SZ1; lia). lia. }
    assert (KCW : a_kact st1 <= KCAP) by ((lazymatch goal with |- ?G => let G' := eval unfold st1, op_meter, add_meter in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_kact] in G in change_no_check G' end); exact KCq).
    apply (katD_bind ASEGS _ (depot_post bt FXOK KD (Xm (U S) T c p) st1 Lc FF MDin mdl1 r4 (at_ S (-2272)) (Z_to_bv 64 0x4bed0))).
    { apply (HYP_DEPOT fx (Xm (U S) T c p) st1 Lc FF MDin mdl1 r4 (at_ S (-2272)) (at_ S (-2112)) (Z_to_bv 64 (bytes_le_to_Z bsz)) (Z_to_bv 64 0x4bed0) sz HFX).
      { rewrite Ehl. exact HH. }
      { exact (model_ivs_wf_sbm mdlq mdl1 SBM1 MW). }
      { exact W1. }
      { exists Mq. split; [exact RP1 | exact DIFF1]. }
      { intros a Ha. split.
        - unfold Xm, T_PC, PC_SZ in Ha. unfold p in Ha. rewrite CP2 in Ha. rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi asan_addrs] in G in change_no_check G' end).
          destruct Ha as [Ha|[Ha|[Ha|Ha]]]; [lia | | | lia]; (destruct GTI as [GTI'|GTI']; lia).
        - intros id Hid. cbn [st1 op_meter add_meter a_dep] in Hid |- *.
          unfold Xm, T_PC, PC_SZ in Ha. destruct Ha as [Ha|[Ha|[Ha|Ha]]].
          + apply (mc_T_stack_vs_node bt st Lc FF W id a Hid). right. rewrite CP2 in Ha. lia.
          + apply (mc_T_stack_vs_node bt st Lc FF W id a Hid). left. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). lia.
          + apply (mc_T_stack_vs_node bt st Lc FF W id a Hid). left. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). lia.
          + apply (ANODE id a Hid). unfold p in Ha. pose proof (csize_pos c NF3) as ((Cz1 & Cz2) & Cz3). lia. }
      { intros a Ha. refine (Xm_xtracked bt st Lc FF Mq mdlq n ks kk (U S) T p W RP Hn HC eq_refl _ _ a Ha).
        - rewrite CP2. lia.
        - (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). fold c ab. (lazymatch goal with |- ?G => let G' := eval unfold p in G in change_no_check G' end). pose proof (csize_pos c NF3) as ((Cz1 & Cz2) & Cz3). lia. }
      { destruct HOLES as [h0 HOLE]. exists h0. exact (AsAinvEntry3.AsAinvHole3.holes_le_same_reg h0 st st1 eq_refl HOLE). }
      { exact (proj1 DR). }
      { exact (proj2 DR). }
      { exact X1. } { exact X2. } { exact X10. } { exact X11. }
      { rewrite at_u by lia. rewrite CP2. clear - CP16 CPlo HSr CR. Z.div_mod_to_equations. lia. }
      { rewrite at_u by lia. rewrite CP2. lia. }
      { rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval unfold PTRHI in G in change_no_check G' end). lia. }
      { apply ret_ok_lit; [lia | reflexivity]. }
      { intros a Ha. rewrite at_u in Ha by lia. split.
        - apply GRin. apply (proj1 (STKq a ltac:(rewrite <- CP2; lia))).
        - eapply store_ok_mono; [exact GRin|]. apply (proj2 (STKq a ltac:(rewrite <- CP2; lia))). }
      { exact (proj1 SZ1). }
      { exact SZW. }
      { exact TAGW. }
      { exact KCW. }
      { intros i Hi. rewrite at_u in Hi by lia. apply GRin. apply (proj1 (STKq (Z_to_bv 64 i) ltac:(unorm; rewrite <- CP2; lia))). }
      { rewrite at_u by lia. rewrite CP2. lia. }
      { rewrite !at_u by lia. lia. }
      { rewrite at_u by lia. lia. } }
    (* [comment removed for export] *)
    intros c' POST.
    destruct POST as (fx' & st' & M' & mdl' & R' & id & Ec' & HFX' & (d' & naa & Est') & W2 & RX2 & KEPTX & DIFF2 & CHG2 & RK & A0 & Hid & SEV & LZ & HH2 & MW2).
    subst c'. apply katD_refl.
    unfold depot_st in Est'. cbn [st1 op_meter add_meter a_reg a_cinit a_cache a_tq a_gq a_sec a_nres a_dep a_hint a_ialloc a_aa a_kact a_shsec] in Est'.
    subst st'.
    destruct RX2 as (M0' & RP2 & DX2).
    (* [comment removed for export] *)
    assert (XF : forall k bs0 (w : nat), -2272 <= k -> k + Z.of_nat w <= 0 -> rdn ASEGS Mq (at_ S k) w = Some bs0 -> rdn ASEGS M' (at_ S k) w = Some bs0).
    { intros k bs0 w Hk1 Hk2 Hr. apply (rd_same ASEGS M' Mq); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | exact Hr].
      intros x Hx. rewrite at_u in Hx by lia. rewrite (KEPTX x); [| (lazymatch goal with |- ?G => let G' := eval unfold Xm in G in change_no_check G' end); lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]]. apply VISstk. lia. }
    (* [comment removed for export] *)
    assert (XLO : forall x : word, Xm (U S) T c p (U x) -> U x < U S - 3584 -> Hd x = false -> M' x = MC x).
    { intros x Hx Hlo Hh. rewrite (KEPTX x); [| exact Hx | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]]. apply VIS. exact Hh. }
    destruct (mam_P2_hdr Mr S T n cnt stw (Z_to_bv 64 cszv) (Z_to_bv 64 ab) b1 GSm Hn Gmm) as (H15 & H14 & H12).
    rewrite <- EMC in H15, H14, H12.
    Ltac incs := apply in_cs; reflexivity.
    Ltac viaRK RK k X := etransitivity; [| exact X];
      match goal with |- getr _ ?x = getr _ _ => replace x with (Z_to_bv 5 k) by (apply bv_eq; reflexivity) end; apply RK; incs.
    Ltac viaXK RK XK k Q := etransitivity; [| exact Q]; etransitivity; [| apply XK; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])];
      match goal with |- getr _ ?x = getr _ _ => replace x with (Z_to_bv 5 k) by (apply bv_eq; reflexivity) end; apply RK; incs.
    (lazymatch goal with |- ?G => let G' := eval unfold runA_post in G in change_no_check G' end).
    exists fx', R', M', M0', mdl', d', naa, id, b1, x18, x19.
    (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). fold S c ab p. rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi asan_addrs] in G in change_no_check G' end).
    replace (runA_st (uncharge st1) d' naa) with (depot_st st1 d' naa)
      by ((lazymatch goal with |- ?G => let G' := eval unfold runA_st, uncharge, depot_st in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_reg a_cinit a_cache a_tq a_gq a_sec a_nres a_dep a_hint a_ialloc a_aa a_kact a_shsec] in G in change_no_check G' end); f_equal; clear; lia).
    split; [reflexivity|]. split; [exact HFX'|]. split; [exact HH2|]. split; [exact MW2|]. split; [exact W2|]. split; [exact RP2|]. split; [exact DX2|].
    split.
    { (* [comment removed for export] *) intros a NE. destruct (decide (M' a = MDin a)) as [E|N].
      + rewrite E in NE |- *. destruct (decide (MDin a = Mq a)) as [E0|N0].
        * rewrite E0 in NE |- *. pose proof (ACC a NE) as AC. rewrite ?BT_ia in AC. exact AC.
        * destruct (DIFF1 a N0) as [X D]. split; [left; exact X | exact D].
      + destruct (DIFF2 a N) as [_ D]. split; [| exact D]. right. pose proof (CHG2 a N) as CX. rewrite at_u in CX by lia. rewrite ?BT_ia in CX.
        destruct CX as [X|[X|X]]; [left; lia | right; left; exact X | right; right; exact X]. }
    split.
    { (* [comment removed for export] *) intros k0 v Hin.
      pose proof (ma_slotsA_range S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) k0 v Hin) as [Hk1 Hk2].
      apply (XF k0 (LE8 v) 8%nat); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (FA k0 v Hin)]. }
    split.
    { (* [comment removed for export] *) intros k0 v Hin.
      assert (Hk : -56 <= k0 /\ k0 + 8 <= 0).
      { cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
      apply (XF k0 (LE8 v) 8%nat); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (FI k0 v Hin)]. }
    split.
    { (* [comment removed for export] *)
      replace (Z_to_bv 64 (p - 15)) with (at_ (Z_to_bv 64 ab) (rz n - 15)) by (apply bv_eq; rewrite at_u by (rewrite Uab; lia); rewrite Uab; (lazymatch goal with |- ?G => let G' := eval unfold p in G in change_no_check G' end); wd_ulia).
      rewrite XLO; [exact H15 | rewrite at_u, Uab by (rewrite Uab; lia); (lazymatch goal with |- ?G => let G' := eval unfold Xm, p in G in change_no_check G' end); lia | rewrite at_u, Uab by (rewrite Uab; lia); lia |].
      rewrite <- (Z_to_bv_bv_unsigned 64 (at_ _ _)). rewrite at_u, Uab by (rewrite Uab; lia). apply NHab. lia. }
    split.
    { (* [comment removed for export] *)
      apply (rd_same ASEGS M' MC); [| wd_ulia_c |].
      + intros x Hx. revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx. apply XLO; [(lazymatch goal with |- ?G => let G' := eval unfold Xm in G in change_no_check G' end); lia | lia | rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHab; lia].
      + replace (Z_to_bv 64 (p - 14)) with (at_ (Z_to_bv 64 ab) (rz n - 14)) by (apply bv_eq; rewrite at_u by (rewrite Uab; lia); rewrite Uab; (lazymatch goal with |- ?G => let G' := eval unfold p in G in change_no_check G' end); wd_ulia).
        exact H14. }
    split.
    { (* [comment removed for export] *)
      apply (rd_same ASEGS M' MC); [| wd_ulia_c |].
      + intros x Hx. revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx. apply XLO; [(lazymatch goal with |- ?G => let G' := eval unfold Xm in G in change_no_check G' end); lia | lia | rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHab; lia].
      + replace (Z_to_bv 64 (p - 12)) with (at_ (Z_to_bv 64 ab) (rz n - 12)) by (apply bv_eq; rewrite at_u by (rewrite Uab; lia); rewrite Uab; (lazymatch goal with |- ?G => let G' := eval unfold p in G in change_no_check G' end); wd_ulia).
        exact H12. }
    split.
    { (* [comment removed for export] *)
      apply (rd_same ASEGS M' MC); [| (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); wd_ulia_c |].
      + intros x Hx. revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx.
        apply XLO; [(lazymatch goal with |- ?G => let G' := eval unfold Xm, T_PC, PC_SZ in G in change_no_check G' end); lia | lia | rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHrt; lia].
      + replace (Z_to_bv 64 (T + T_PC + PC_SZ * c)) with (at_ (Z_to_bv 64 T) (208 + 80 * class_of (needed n))) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_, T_PC, PC_SZ in G in change_no_check G' end); fold c; wd_ulia).
        replace (Z.of_nat (length ks)) with (cnt - 1) by ((lazymatch goal with |- ?G => let G' := eval unfold cnt in G in change_no_check G' end); lia).
        rewrite EMC. apply (mam_P2_cnt Mr S T n cnt stw (Z_to_bv 64 cszv) (Z_to_bv 64 ab) b1 GSm GTm Hn Gmm). rewrite Uab. lia. }
    split; [viaRK RK 2 X2|]. split; [viaXK RK XK 4 Q4|]. split; [viaXK RK XK 3 Q3|].
    split; [etransitivity; [| exact C8]; viaRK RK 8 X8|]. split; [viaRK RK 9 X9|].
    split; [exact A0|]. split; [viaRK RK 18 X18|]. split; [viaRK RK 19 X19|]. split; [viaRK RK 20 X20|]. split; [viaRK RK 21 X21|].
    split; [viaXK RK XK 22 Q22|]. split; [viaXK RK XK 23 Q23|]. split; [viaRK RK 24 X24|]. split; [viaRK RK 25 X25|]. split; [viaXK RK XK 26 Q26|].
    split; [viaXK RK XK 27 Q27|]. split; [exact Hid|].
    split; [eapply same_except_vm_trans; [exact SEVq|]; eapply same_except_vm_trans; [apply same_but_materialized_except_vm; exact SBM1 | exact SEV]|].
    (lazymatch goal with |- ?G => let G' := eval unfold lazy_kept in G in change_no_check G' end). rewrite ?BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi asan_addrs] in G in change_no_check G' end).
    intros a Ha. pose proof (LKq a) as LQ. rewrite ?BT_ia in LQ. cbn [ia_img_lo ia_img_hi asan_addrs] in LQ. rewrite <- (LQ Ha).
    cbn [a_dep] in LZ. assert (RNGa : 0 <= a < 2 ^ 64).
    { destruct Ha as [V|[V|V]]; [refine (proj1 (AsKSys7b.app_visible_cases bt _ Lc FF (2 ^ 20) (2 ^ 28) W2 a _)); rewrite ?BT_ia; exact V | pose proof ceil_rng; lia | lia]. }
    (* [comment removed for export] *)
    first [destruct (LZ a RNGa) as [E|(blk & Hin & Hnin & Hr)] | destruct (LZ a) as [E|(blk & Hin & Hnin & Hr)]]; [rewrite E; (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz; reflexivity|].
    exfalso. destruct (OBL_store_private _ Lc FF blk a W2 Hin Hr) as (Z1 & Z2 & Z3). rewrite ?BT_ia in Z2, Z3. cbn [ia_img_lo ia_img_hi asan_addrs] in Z2.
    destruct Ha as [V|[V|V]]; [exact (Z3 V) | lia | lia].
  Qed.
End TOPP2.
End WithCeil.
End AsAllocMTopP2.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopP1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocMTopP3.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.AsAinvOpsQ3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop.AsAllocMTopA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopP1.AsAllocM8Lq OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopP1.AsAllocM8Lr OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopP1.AsAllocMHoleN OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopP1 AsAllocMTopP2.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop.AsDepotHyp8.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section WithCeil.
Context {RC : run_ceil}.

Section TOPP3.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND KD : Z).
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis PCELLS : pop_cells bt.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis BOOTG : boot_geom bt.
  Hypothesis G_KD : 0 <= KD <= 1312.
  Hypothesis HYP_DEPOT : AsAllocFHyp.HYP_DEPOT_stmt bt FXOK KD.
  Hypothesis HTP : TP = ia_tp asan_addrs.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation AAINVH := (AAINV_HS bt).
  #[local] Abbreviation MOK := (malloc_ok ASEGS FXOK asan_addrs AAINVH MSTK_A).
  #[local] Abbreviation MNULL := (malloc_null ASEGS FXOK asan_addrs AAINVH MSTK_A).


  (* [comment removed for export] *)
  Definition miss_null_stmt : Prop :=
    forall (h : option Z) fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret n sp : Z) (st st' : ast) (c' : config),
      m_halted mdl = None -> FXOK fx ->
      WF bt st Lc FF -> Rep bt st Lc FF M mdl -> bounds st Lc B C K -> holes_lsopt h st -> BackingAlgebra.model_ivs_wf mdl -> hole_ok h n ->
      call_pre ASEGS asan_addrs R M ret sp MSTK_A ->
      U (getr R 10) = n -> 1 <= n <= 64512 -> fpc M (U (getr R 8)) sp DMAX ->
      B + (n + MBLK) <= GBUDGET -> C + 1 <= LMAX -> K + kcost_malloc n <= KCAP ->
      a_cache st (class_of (needed n)) = [] ->
      refill_fail_st bt st (class_of (needed n)) st' -> at_refill_ret bt fx R M mdl Lc FF n st' 0 c' ->
      katD ASEGS c' (MNULL R M mdl Lc FF B C K ret n sp).

  (* [comment removed for export] *)
  Lemma miss_conts : partB_stmt bt FXOK ->
    forall (h : option Z) fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret n sp : Z) (st : ast),
      m_halted mdl = None -> FXOK fx ->
      WF bt st Lc FF -> bounds st Lc B C K -> holes_lsopt h st -> hole_ok h n ->
      call_pre ASEGS asan_addrs R M ret sp MSTK_A ->
      U (getr R 10) = n -> 1 <= n <= 64512 -> fpc M (U (getr R 8)) sp DMAX ->
      B + (n + MBLK) <= GBUDGET -> C + 1 <= LMAX -> K + kcost_malloc n <= KCAP ->
      a_cache st (class_of (needed n)) = [] ->
      (forall st' c', refill_ok_st bt (op_meter st EVT [] 0) (class_of (needed n)) st' -> a_cache st' (class_of (needed n)) <> [] ->
                      at_refill_ret bt fx R M mdl Lc FF n st' 1 c' -> katwD ASEGS c' (MOK R M mdl Lc FF B C K ret n sp) (fun _ => True))
      /\ (forall st' c', refill_fail_st bt (op_meter st EVT [] 0) (class_of (needed n)) st' -> at_refill_ret bt fx R M mdl Lc FF n st' 0 c' ->
                         katD ASEGS c' (fun _ => True)).
  Proof using HYP_DEPOT G_KD GEOM CELLS BT_ia BT_segs KD MIDEND FL PGP TSDP TP.
    intros PB h fx R M mdl Lc FF B C K ret n sp st HLT HFX W BD HL HO CP HR10 Hn' FPC HB HC HK HC0.
    pose proof (holes_ls_of_opt h n st HL HO) as HS.
    set (st1 := op_meter st EVT [] 0).
    assert (W1 : WF bt st1 Lc FF) by (apply (WF_meter bt st Lc FF EVT [] 0 W); (lazymatch goal with |- ?G => let G' := eval unfold EVT in G in change_no_check G' end); lia).
    assert (HS1 : holes_ls n st1) by (exact (holes_ls_same_regcache n st st1 eq_refl eq_refl HS)).
    assert (HC01 : a_cache st1 (class_of (needed n)) = []) by exact HC0.
    pose proof (depot_room_meter bt st Lc FF EVT [] 0 W (Z.le_refl _)) as DR1. fold st1 in DR1.
    split; [| intros st' c' _ _; apply katD_refl; exact I].
    intros st' c' EST CNE AR. apply katwD_of_katD.
    destruct AR as (rq & Mq & mdlq & x18 & x19 & sz & bsz & AR). cbv zeta in AR.
    destruct AR as (Ec & HLq & MWq & Wq & RPq & Q10 & Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27 & Q4 & Q3
                    & FA & FI & FS4 & FS8 & Lsz & SZ1 & FTR & FC & STKq & ACC & SEVq & LKq).
    subst c'.
    pose proof (app_removelast_last 0 CNE) as E.
    set (ks := removelast (a_cache st' (class_of (needed n)))) in E. set (kk := last (a_cache st' (class_of (needed n))) 0) in E.
    pose proof CP as (_ & _ & _ & CP2 & _).
    pose proof (refill_ok_st_frame bt st1 (class_of (needed n)) st' EST) as (_ & _ & _ & ED' & _ & EK' & _).
    cbn [st1 op_meter add_meter a_dep a_kact] in ED', EK'.
    apply (katD_bind ASEGS _ (runA_post bt FXOK (uncharge st') ks kk Lc FF R M mdl n)).
    + apply (malloc_suffix bt FXOK TP TSDP PGP FL MIDEND KD BT_segs BT_ia CELLS GEOM G_KD HYP_DEPOT fx R M mdl Lc FF ret sp n st' ks kk rq Mq mdlq x18 x19 sz bsz
               HFX HLq MWq Wq RPq CP Hn' E); try assumption.
      * intros a Ha. apply STKq. rewrite CP2. exact Ha.
      * intros a NE. destruct (ACC a NE) as [F D]. split; [| exact (D eq_refl)].
        destruct F as [F | F]; [| right; right; left; exact F].
        destruct (Z_lt_le_dec (U a) (U (getr R 2) - 2480)) as [L | L]; [right; left; lia | left; (lazymatch goal with |- ?G => let G' := eval unfold Xm in G in change_no_check G' end); left; lia].
      * rewrite EK'. destruct BD as (_ & _ & BK). unfold kcost_malloc, EVT in HK |- *. clear - BK HK Hn'. lia.
      * unfold depot_room in DR1 |- *. cbn [st1 op_meter add_meter a_dep a_kact] in DR1. rewrite ED', EK'. exact DR1.
      * exists h. exact (refill_ok_st_holes bt st1 (class_of (needed n)) st' EST h (AsAinvEntry3.AsAinvHole3.holes_le_same_reg h st st1 eq_refl (holes_lsopt_le _ _ HL))).
    + intros c' PC.
      eapply (PB h fx R M mdl Lc FF B C K ret n sp (uncharge st') ks kk c'); try eassumption.
      * unfold bounds in BD |- *. (lazymatch goal with |- ?G => let G' := eval unfold uncharge in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_kact] in G in change_no_check G' end). rewrite EK'. clear - BD. unfold EVT in *. lia.
      * apply (AsAinvEntry3.AsAinvHole3.holes_le_same_reg h st' (uncharge st') eq_refl).
        exact (refill_ok_st_holes bt st1 (class_of (needed n)) st' EST h (AsAinvEntry3.AsAinvHole3.holes_le_same_reg h st st1 eq_refl (holes_lsopt_le _ _ HL))).
      * (lazymatch goal with |- ?G => let G' := eval unfold hole_flags, uncharge in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_reg] in G in change_no_check G' end). destruct (holes_closed_ok bt n st1 Lc FF st' Hn' W1 HS1 HC01 EST (class_of (needed n))) as [F1 F2].
        rewrite F1, F2. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma miss_charge : forall (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K n : Z) (st : ast),
      WF bt st Lc FF -> Rep bt st Lc FF M mdl -> bounds st Lc B C K -> 1 <= n -> K + kcost_malloc n <= KCAP ->
      WF bt (op_meter st EVT [] 0) Lc FF /\ Rep bt (op_meter st EVT [] 0) Lc FF M mdl /\ a_kact (op_meter st EVT [] 0) <= KCAP
      /\ mu_room (op_meter st EVT [] 0).
  Proof using.
    intros M mdl Lc FF B C K n st W RP BD Hn HK. clear HYP_DEPOT G_KD GEOM BOOTG PCELLS CELLS HTP.
    split; [apply (WF_meter bt st Lc FF EVT [] 0 W); (lazymatch goal with |- ?G => let G' := eval unfold EVT in G in change_no_check G' end); lia|].
    split.
    - pose proof RP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & FA' & _) & (Bw1 & Bw2 & _) & _).
      apply (OPS_REP_meter_pf bt st Lc FF M mdl mdl EVT [] 0 RP eq_refl); [intros a; tauto | exact FA' | | | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      + rewrite app_nil_r. exact Bw1.
      + rewrite app_nil_r. exact Bw2.
    - split; [| apply (AsAinvRoom3.mu_room_charged bt st Lc FF); [exact W | reflexivity | reflexivity]].
      (lazymatch goal with |- ?G => let G' := eval cbn [a_kact op_meter add_meter] in G in change_no_check G' end). destruct BD as (_ & _ & BK). unfold kcost_malloc, EVT in HK |- *. clear - BK HK Hn. lia.
  Qed.

  Theorem case_miss : partB_stmt bt FXOK -> miss_null_stmt -> MCASE bt FXOK (ia_malloc asan_addrs) P_miss.
  Proof using HTP HYP_DEPOT G_KD BOOTG GEOM PCELLS CELLS BT_ia BT_segs KD MIDEND FL PGP TSDP TP.
    intros PB _ h fx R M mdl Lc FF B C K ret n sp st HLT HFX W RP BD HL MW HO CP HR10 Hn FPC HB HC HK (Hp & HC0).
    assert (Hn' : 1 <= n <= 64512) by lia.
    destruct (miss_charge M mdl Lc FF B C K n st W RP BD (proj1 Hn') HK) as (W1 & RP1 & KC1 & MUR1).
    destruct (miss_conts PB h fx R M mdl Lc FF B C K ret n sp st HLT HFX W BD HL HO CP HR10 Hn' FPC HB HC HK HC0) as [C1 C0].
    apply katwD_of_katD. apply (katwD_ok_only ASEGS _ _ (fun _ => True)).
    exact (malloc_to_refill_ret bt TP TSDP PGP FL MIDEND BT_segs BT_ia CELLS PCELLS GEOM BOOTG HTP fx R M mdl Lc FF ret sp n (op_meter st EVT [] 0)
             (MOK R M mdl Lc FF B C K ret n sp) (fun _ => True) HLT MW W1 RP1 KC1 MUR1 CP HR10 Hn' FPC HC0 C1 C0).
  Qed.

  (* [comment removed for export] *)
  Definition MCASE_S (entry : Z) (P : Z -> ast -> Prop) : Prop :=
    forall (h : option Z) fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret n sp : Z) (st : ast),
      m_halted mdl = None -> FXOK fx ->
      WF bt st Lc FF -> Rep bt st Lc FF M mdl -> bounds st Lc B C K -> holes_lsopt h st -> BackingAlgebra.model_ivs_wf mdl -> hole_ok h n ->
      call_pre ASEGS asan_addrs R M ret sp MSTK_A ->
      U (getr R 10) = n -> 1 <= n <= NMAX -> fpc M (U (getr R 8)) sp DMAX ->
      B + (n + MBLK) <= GBUDGET -> C + 1 <= LMAX -> K + kcost_malloc n <= KCAP ->
      P n st ->
      katsD ASEGS (cfg ASEGS fx R entry M mdl) (MOK R M mdl Lc FF B C K ret n sp) (MNULL R M mdl Lc FF B C K ret n sp).
  Definition P_fresh_prim (n : Z) (st : ast) : Prop :=
    n <= 64512 /\ a_cache st (class_of (needed n)) = []
    /\ Z.of_nat (length (r_free (a_reg st (class_of (needed n))))) < cache_hint (class_of (needed n))
    /\ utest_x st (class_of (needed n)).

  Theorem case_miss_alt : partB_stmt bt FXOK -> miss_null_stmt -> MCASE_S (ia_malloc asan_addrs) P_fresh_prim.
  Proof using HTP HYP_DEPOT G_KD BOOTG GEOM PCELLS CELLS BT_ia BT_segs KD MIDEND FL PGP TSDP TP.
    intros PB _ h fx R M mdl Lc FF B C K ret n sp st HLT HFX W RP BD HL MW HO CP HR10 Hn FPC HB HC HK (Hp & HC0 & ENF & EUX).
    assert (Hn' : 1 <= n <= 64512) by lia.
    destruct (miss_charge M mdl Lc FF B C K n st W RP BD (proj1 Hn') HK) as (W1 & RP1 & KC1 & MUR1).
    destruct (miss_conts PB h fx R M mdl Lc FF B C K ret n sp st HLT HFX W BD HL HO CP HR10 Hn' FPC HB HC HK HC0) as [C1 C0].
    apply katsD_of_katwD. apply katwD_of_katD. apply (katsD_ok_only ASEGS _ _ (fun _ => True)).
    exact (malloc_to_refill_ret_s bt TP TSDP PGP FL MIDEND BT_segs BT_ia CELLS PCELLS GEOM BOOTG HTP fx R M mdl Lc FF ret sp n (op_meter st EVT [] 0)
             (MOK R M mdl Lc FF B C K ret n sp) (fun _ => True) HLT MW W1 RP1 KC1 MUR1 CP HR10 Hn' FPC HC0 ENF EUX C1 C0).
  Qed.
End TOPP3.
End WithCeil.
End AsAllocMTopP3.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.AsAinvOpsQ3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop.AsAllocMTopA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTop.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopP1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopP1.AsAllocM8Lq OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopP1.AsAllocM8Lr OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg.AsAllocM8n OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg.AsAllocMRunN OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopP1.AsAllocMHoleN OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopP1 AsAllocMTopP3.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma restrict_mkst_n : forall {fx : FPState} (Hd : word -> bool) (r : bvmap 5 word) pc m rom,
  restrict Hd (@mkst fx r pc m rom) = @mkst fx r pc (mrestrict Hd m) rom.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma store_ok1_defQ : forall (m : mem) (a : word), m a <> None -> store_ok ASEGS m a 1%nat = true.
Proof.
  intros m a D. apply store_ok_of_all; [pose proof (u64_range a); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
  intros x Hx. assert (x = a) by (apply bv_eq; cbn in Hx; lia). subst x. (lazymatch goal with |- ?G => let G' := eval unfold wview in G in change_no_check G' end). destruct (m a); [discriminate | exact (False_ind _ (D eq_refl))].
Qed.

Section WithCeil.
Context {RC : run_ceil}.

Section TOPP4.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND : Z).
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis NCELL : In (0x1897e1, 1%nat, 1) (bt_consts bt).                       (* [comment removed for export] *)
  Hypothesis HTP : TP = ia_tp asan_addrs.
  (* [comment removed for export] *)
  Hypothesis OOM_NOT_REP : forall st Lc FF, WF bt st Lc FF -> ~ rep_cells bt st Lc FF 0x1897e0.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation AAINVH := (AAINV_HS bt).
  #[local] Abbreviation MNULL := (malloc_null ASEGS FXOK asan_addrs AAINVH MSTK_A).

  (* [comment removed for export] *)
  Lemma errno_wins_ok : as_wins_ok asan_addrs [(ia_errno asan_addrs, ia_errno asan_addrs + 4)].
  Proof using.
    intros a (lo & hi & Hin & Ha). cbn [In] in Hin. destruct Hin as [E | []]. injection E as <- <-.
    unfold ia_errno in Ha. cbn [ia_tp asan_addrs] in Ha.
    split; [(lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi asan_addrs] in G in change_no_check G' end); lia|].
    split; [| split].
    - intros (lo' & hi' & Hin & Hr). cbn [ia_priv asan_addrs In] in Hin.
      repeat (destruct Hin as [E | Hin]; [injection E as <- <-; lia|]). destruct Hin.
    - (lazymatch goal with |- ?G => let G' := eval unfold in_rtc in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [ia_rtc_sb ia_rtc_uar asan_addrs] in G in change_no_check G' end). lia.
    - intros (lo' & hi' & Hin & Hr). cbn [ia_const asan_addrs In] in Hin.
      repeat (destruct Hin as [E | Hin]; [injection E as <- <-; lia|]). destruct Hin.
  Qed.

  Theorem miss_null : miss_null_stmt bt FXOK.
  Proof using OOM_NOT_REP NCELL CELLS BT_ia BT_segs MIDEND FL PGP TSDP TP.
    intros h fx R M mdl Lc FF B C K ret n sp st st' c' HLT HFX W RP BD HL MW HO CP HR10 Hn FPC HB HC HK HC0 EST AR.
    destruct AR as (rq & Mq & mdlq & x18 & x19 & sz & bsz & AR). cbv zeta in AR.
    destruct AR as (Ec & HLq & MWq & Wq & RPq & Q10 & Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27 & Q4 & Q3
                    & FA & FI & FS4 & FS8 & Lsz & SZ1 & FTR & FC & STKq & ACC & SEVq & LKq).
    subst c'.
    pose proof ceil_rng as CR.
    set (S := getr R 2) in *. set (tp := getr R 4) in *.
    destruct CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk). fold S in CP2. fold tp in CP4.
    pose proof CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & _).
    pose proof (free_obls_pf bt) as (OBL_nolazy_rt & _). unfold OBL_nolazy_rt_stmt in OBL_nolazy_rt.
    pose proof (thread_dyn bt st' Lc FF Wq) as (GT0 & GTC & GTI & GTB & TPG & _).
    assert (GT4 : 4096 <= T) by (unfold PG in TPG; clear - GT0 TPG; Z.div_mod_to_equations; lia).
    pose proof RPq as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18).
    rewrite BT_segs in *. rewrite BT_ia in *. cbn [ia_img_lo ia_img_hi asan_addrs] in GTI.
    pose proof (u64_range S) as HSr.
    unfold PTRHI in CPlo, CPhi. unfold AS_HEAPLO, AS_LO, MSTK_A, PG in *.
    assert (GTS : TSIDE T) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); exact (conj GTI GTB)). hidehyp GTB.
    assert (Etp : tp = Z_to_bv 64 (ia_tp asan_addrs)) by exact CP4.
    assert (Utp : U tp = ia_tp asan_addrs) by (rewrite Etp; reflexivity).
    (* [comment removed for export] *)
    set (Hd := HID st' mdlq).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st' mdlq z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi asan_addrs] in G in change_no_check G' end). lia. }
    destruct R14 as (Bw1 & Bw2 & _).
    set (Mr := mrestrict Hd Mq).
    Ltac hoff NH := apply hid_off_of; intros z Hz; split; [lia | apply NH; lia].
    Ltac konst Hd M R1 NHs C := apply (cellZ_restrict Hd M _ _ _ (const_cell bt M _ _ _ R1 C)); [lia | lia | hoff NHs].
    assert (K_mcs : rdn ASEGS Mr (Z_to_bv 64 0x10827c) 4 = Some (LE4 30)) by konst Hd Mq R1 NHs CELL_mcs.
    assert (K_gcf : rdn ASEGS Mr (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 0x1990a8))) by konst Hd Mq R1 NHs CELL_gcf.
    assert (K_fum : rdn ASEGS Mr (Z_to_bv 64 0x1990ca) 1 = Some [Z_to_bv 8 1]) by konst Hd Mq R1 NHs CELL_fum.
    assert (K_inited : rdn ASEGS Mr (Z_to_bv 64 0x108258) 1 = Some [Z_to_bv 8 1]) by konst Hd Mq R1 NHs CELL_inited.
    assert (K_mrn : rdn ASEGS Mr (Z_to_bv 64 0x1897e1) 1 = Some [Z_to_bv 8 1]) by konst Hd Mq R1 NHs NCELL.
    assert (STKr : forall x : word, U S - 3584 <= U x < U S -> Mr x = Mq x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). apply mrestrict_off. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [pose proof (u64_range x); lia|]. left. rewrite CP2 in Hx. lia. }
    assert (RDr : forall (k : Z) (w : nat) (bs : list byte), -3584 <= k -> k + Z.of_nat w <= 0 -> rdn ASEGS Mq (at_ S k) w = Some bs -> rdn ASEGS Mr (at_ S k) w = Some bs).
    { intros k w bs K1 K2 Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]|]. intros x Hx. rewrite at_u in Hx by lia. apply STKr. lia. }
    assert (SOKstk : store_ok ASEGS Mr (at_ S (-3584)) 3584 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; hoff NHs].
      apply store_ok_bytes; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply (proj2 (STKq x ltac:(lia))). }
    assert (SOKoom : store_ok ASEGS Mr (Z_to_bv 64 0x1897e0) 1 = true) by (apply store_ok_wseg; vm_cast_no_check (eq_refl true)).
    assert (SOKerr : store_ok ASEGS Mr (at_ tp (-164)) 4 = true).
    { rewrite Etp. replace (at_ (Z_to_bv 64 (ia_tp asan_addrs)) (-164)) with (Z_to_bv 64 (ia_errno asan_addrs) : word) by (apply bv_eq; reflexivity).
      apply store_ok_wseg. vm_cast_no_check (eq_refl true). }
    assert (FCr : forall (o : Z) (v : word),
              In (o, v) [(-8, at_ ARB 0x4bdc4); (-16, Z_to_bv 64 1); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 (needed n)); (-48, Z_to_bv 64 (rz n))]%Z ->
              rdn ASEGS Mr (at_ (at_ S (-2272)) o) 8 = Some (LE8 v)).
    { intros o v Hin.
      assert (Ho : -48 <= o <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      rewrite at_at. apply RDr; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at. exact (FC o v Hin). }
    assert (FAr : forall (k : Z) (v : word), In (k, v) (ma_slotsA S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)) ->
              rdn ASEGS Mr (at_ S k) 8 = Some (LE8 v)).
    { intros k v Hin. pose proof (ma_slotsA_range S n x18 x19 _ _ _ _ _ _ k v Hin) as [Hk1 Hk2]. apply RDr; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (FA k v Hin)]. }
    assert (FIr : forall (k : Z) (v : word),
              In (k, v) [(-8, getr R 1); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
              rdn ASEGS Mr (at_ S k) 8 = Some (LE8 v)).
    { intros k v Hin.
      assert (Hk : -56 <= k /\ k + 8 <= 0) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      apply RDr; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (FI k v Hin)]. }
    assert (Q2' : getr rq 2 = at_ (at_ S (-2272)) (-48)) by (rewrite at_at; exact Q2).
    assert (RETR : ret_ok (getr R 1)) by (rewrite CP1; apply ret_ok_lit; [lia | exact CPe]).
    (* [comment removed for export] *)
    destruct (run_mA_null Mr (seg_rom ASEGS) rq R S tp T n x18 x19 Q2' Q4 Q3 Q10 Q18 RETR)
      as (r3 & RUN & X10 & X1 & X2 & X3 & X4 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & X26 & X27).
    all: try assumption.
    all: try (rewrite ?CP2; split; [split; [exact GT4 | exact GTS] | lia]).
    all: try (rewrite ?CP2, ?Utp; (lazymatch goal with |- ?G => let G' := eval cbn [ia_tp asan_addrs] in G in change_no_check G' end); lia).
    all: try (rewrite ?CP2, ?Utp; (lazymatch goal with |- ?G => let G' := eval cbn [ia_tp asan_addrs] in G in change_no_check G' end); repeat split; lia).
    all: let k := numgoals in guard k = 1.
    (* [comment removed for export] *)
    set (MC := mn_mem Mr S tp) in RUN.
    apply (katD_msteps_acct ASEGS Hd (HID_off_segments bt st' Lc FF Mq mdlq BT_ia RPq) asanF_segs_wx (a_aa st')
             (@mkst fx rq (Z_to_bv 64 0x5052c) Mq (seg_rom ASEGS)) (@mkst fx r3 (getr R 1) MC (seg_rom ASEGS)) mdlq).
    { apply lazy_cover_HID. }
    { exact Bw1. }
    { exact Bw2. }
    { exact HLq. }
    { rewrite restrict_mkst_n. exact RUN. }
    intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx rq (Z_to_bv 64 0x5052c) Mq (seg_rom ASEGS))) with Mq by reflexivity.
    set (MDin := munrestrict Hd Mq MC).
    apply katD_refl.
    (* [comment removed for export] *)
    assert (GSm : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0) by (rewrite CP2; lia).
    assert (Gtpm : AIMGLO + 164 <= U tp /\ U tp <= AIMGHI) by (rewrite Utp; (lazymatch goal with |- ?G => let G' := eval cbn [ia_tp asan_addrs] in G in change_no_check G' end); lia).
    assert (GRin : mem_grows Mq MDin).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MDin, munrestrict in G in change_no_check G' end). destruct (Hd x) eqn:Ex; [exact Hx|]. apply (mn_mem_grows Mr S tp). (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite mrestrict_off by exact Ex. exact Hx. }
    assert (DIFF : forall a : word, MDin a <> Mq a ->
              U a = 0x1897e0 \/ (U S - 2152 <= U a < U S - 2144) \/ (ia_errno asan_addrs <= U a < ia_errno asan_addrs + 4)).
    { intros a NE. unfold MDin, munrestrict in NE. destruct (Hd a) eqn:Eh; [exfalso; exact (NE eq_refl)|].
      assert (EMr : Mr a = Mq a) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); apply mrestrict_off; exact Eh).
      destruct (Z.eq_dec (U a) 0x1897e0) as [E|N1]; [left; exact E|].
      destruct (Z_lt_le_dec (U a) (U S - 2152)) as [L1|L1]; [| destruct (Z_lt_le_dec (U a) (U S - 2144)) as [L2|L2]; [right; left; lia|]].
      all: destruct (Z_lt_le_dec (U a) (U tp - 164)) as [L3|L3]; [| destruct (Z_lt_le_dec (U a) (U tp - 160)) as [L4|L4]; [right; right; (lazymatch goal with |- ?G => let G' := eval unfold ia_errno in G in change_no_check G' end); rewrite <- Utp; lia|]].
      all: exfalso; apply NE; rewrite <- EMr; apply (mn_mem_outside Mr S tp GSm Gtpm); lia. }
    assert (DEF : forall a : word, MDin a <> Mq a -> MDin a <> None).
    { intros a NE. destruct (MDin a) eqn:E1; [discriminate|]. exfalso. apply NE. destruct (Mq a) eqn:E2; [|reflexivity].
      exfalso. assert (X : Mq a <> None) by (rewrite E2; discriminate). apply GRin in X. rewrite E1 in X. exact (X eq_refl). }
    (* [comment removed for export] *)
    assert (RPf : Rep bt st' Lc FF MDin mdl1).
    { apply (Rep_frame bt st' Lc FF Mq MDin mdl1 Wq (Rep_sbm bt st' Lc FF Mq mdlq mdl1 RPq MI1 SBM1)).
      intros a NE. split; [| exact (DEF a NE)]. intros RCa.
      destruct (DIFF a NE) as [E | [E | E]].
      - rewrite E in RCa. exact (OOM_NOT_REP st' Lc FF Wq RCa).
      - pose proof (rep_cells_lt_ceil bt BT_ia st' Lc FF (U a) Wq RCa). rewrite CP2 in E. lia.
      - refine (win_vs_rep bt st' Lc FF Wq [(ia_errno asan_addrs, ia_errno asan_addrs + 4)] (U a) _ _ RCa).
        + rewrite BT_ia. exact errno_wins_ok.
        + exists (ia_errno asan_addrs), (ia_errno asan_addrs + 4). split; [left; reflexivity | exact E]. }
    (* [comment removed for export] *)
    pose proof (holes_ls_fail bt n st st' Hn (holes_ls_of_opt h n st HL HO) HC0 EST) as HLS.
    pose proof (refill_fail_st_frame bt st (class_of (needed n)) st' EST) as (_ & _ & _ & _ & _ & EK & _).
    (* [comment removed for export] *)
    (lazymatch goal with |- ?G => let G' := eval unfold malloc_null in G in change_no_check G' end). exists fx, r3, MDin, mdl1.
    split; [(lazymatch goal with |- ?G => let G' := eval unfold cfg in G in change_no_check G' end); rewrite CP1; reflexivity|]. split; [exact HFX|].
    split.
    { (* [comment removed for export] *)
      intros r Hr. unfold as_callee_saved in Hr. cbn [In] in Hr.
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 2) with (2%bv : reg) by (apply bv_eq; reflexivity); rewrite X2; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 3) with (3%bv : reg) by (apply bv_eq; reflexivity); rewrite X3; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 4) with (4%bv : reg) by (apply bv_eq; reflexivity); rewrite X4; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 8) with (8%bv : reg) by (apply bv_eq; reflexivity); rewrite X8; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 9) with (9%bv : reg) by (apply bv_eq; reflexivity); rewrite X9; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 18) with (18%bv : reg) by (apply bv_eq; reflexivity); rewrite X18; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 19) with (19%bv : reg) by (apply bv_eq; reflexivity); rewrite X19; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 20) with (20%bv : reg) by (apply bv_eq; reflexivity); rewrite X20; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 21) with (21%bv : reg) by (apply bv_eq; reflexivity); rewrite X21; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 22) with (22%bv : reg) by (apply bv_eq; reflexivity); rewrite X22; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 23) with (23%bv : reg) by (apply bv_eq; reflexivity); rewrite X23; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 24) with (24%bv : reg) by (apply bv_eq; reflexivity); rewrite X24; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 25) with (25%bv : reg) by (apply bv_eq; reflexivity); rewrite X25; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 26) with (26%bv : reg) by (apply bv_eq; reflexivity); rewrite X26; reflexivity|].
      destruct Hr as [<- | Hr]; [replace (Z_to_bv 5 27) with (27%bv : reg) by (apply bv_eq; reflexivity); rewrite X27; reflexivity|].
      destruct Hr. }
    split; [exact X10|].
    split.
    { (* [comment removed for export] *) intros a NE. (lazymatch goal with |- ?G => let G' := eval unfold as_changed in G in change_no_check G' end). rewrite ?BT_ia.
      destruct (decide (MDin a = Mq a)) as [E | N].
      - rewrite E in NE. destruct (ACC a NE) as [[F | F] _]; [left; rewrite <- CP2; fold S; (lazymatch goal with |- ?G => let G' := eval unfold MSTK_A in G in change_no_check G' end); lia | right; left; rewrite ?BT_ia in F; exact F].
      - destruct (DIFF a N) as [E | [E | E]].
        + right; right; left. exists 0x10825a, 0x1990a8. split; [(lazymatch goal with |- ?G => let G' := eval cbn [ia_priv asan_addrs In] in G in change_no_check G' end); tauto | lia].
        + left. rewrite <- CP2. fold S. (lazymatch goal with |- ?G => let G' := eval unfold MSTK_A in G in change_no_check G' end). lia.
        + right; right; right. exact E. }
    split.
    { (* [comment removed for export] *) intros a Ha Dm. unfold in_errno, ia_errno in Ha. cbn [ia_tp asan_addrs] in Ha.
      (lazymatch goal with |- ?G => let G' := eval unfold MDin in G in change_no_check G' end). rewrite munrestrict_off by (rewrite <- (Z_to_bv_bv_unsigned 64 a); apply NHs; [pose proof (u64_range a); lia | right; lia]).
      apply (mn_mem_errno Mr S tp Gtpm). rewrite Utp. (lazymatch goal with |- ?G => let G' := eval cbn [ia_tp asan_addrs] in G in change_no_check G' end). lia. }
    split.
    { (* [comment removed for export] *) intros a Ha. assert (D : MDin a <> None) by (apply GRin; apply (proj1 (STKq a ltac:((lazymatch goal with |- ?G => let G' := eval unfold MSTK_A in G in change_no_check G' end); rewrite CP2; exact Ha)))).
      split; [exact D | exact (store_ok1_defQ MDin a D)]. }
    split.
    { (* [comment removed for export] *)
      exists st'. split; [exact Wq|]. split; [exact RPf|]. split; [| exact (model_ivs_wf_sbm mdlq mdl1 SBM1 MWq)].
      split; [unfold bounds in BD |- *; rewrite EK; exact BD | exact HLS]. }
    split; [eapply same_except_vm_trans; [exact SEVq | apply same_but_materialized_except_vm; exact SBM1]|].
    split; [| exact (halted_sbm mdlq mdl1 SBM1 HLq)].
    intros a Ha. pose proof (lazy_kept_sbm bt Lc FF mdlq mdl1 SBM1 a) as L1. rewrite ?BT_ia in L1. rewrite (L1 Ha). pose proof (LKq a) as L2. rewrite ?BT_ia in L2. exact (L2 Ha).
  Qed.
End TOPP4.
End WithCeil.
